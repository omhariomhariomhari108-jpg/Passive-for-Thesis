"""Active <-> Passive Card Game: MULTIPLAYER v3 (Streamlit)

* Student accounts: create an account (Student ID + password), then log in.
* Each student sees their own record (logins, games started / completed / won).
* Teacher dashboard (password): all students, activity log, accounts, password reset, CSV download.
* Accounts and activity are saved to a Google Sheet (free Apps Script, no card needed),
  or to a local file if no sheet is connected (lost when the app restarts).
Run locally with:  streamlit run app.py
"""
import contextlib
import hashlib
import hmac
import datetime
import os
import queue
import random
import re
import sqlite3
import threading
import time
import uuid
from collections import Counter

import pandas as pd
import streamlit as st

# ------------------------------------------------------------------
# DATA
# ------------------------------------------------------------------
SETS = [
    {"a": ["The international office verifies the students’ documents.",
           "The international office verified the students’ documents."],
     "p": ["The students’ documents are verified by the international office.",
           "The students’ documents were verified by the international office."],
     "g": ["am/is/are + V3", "was/were + V3"]},
    {"a": ["The technicians are repairing the university computers.",
           "The technicians were repairing the university computers."],
     "p": ["The university computers are being repaired by the technicians.",
           "The university computers were being repaired by the technicians."],
     "g": ["am/is/are + being + V3", "was/were + being + V3"]},
    {"a": ["The international office will announce the scholarship results.",
           "The international office must announce the scholarship results."],
     "p": ["The scholarship results will be announced by the international office.",
           "The scholarship results must be announced by the international office."],
     "g": ["will + be + V3", "modal + be + V3"]},
    {"a": ["The research team has collected the survey data.",
           "The research team had collected the survey data."],
     "p": ["The survey data has been collected by the research team.",
           "The survey data had been collected by the research team."],
     "g": ["has/have + been + V3", "had + been + V3"]},
]

BOT_NAMES = ["Bot Ana", "Bot Budi", "Bot Citra", "Bot Dewi"]
TYPE_NAMES = {"A": "Active", "P": "Passive", "G": "Grammar"}
SPECIAL = {"STOP", "CHG", "P2"}
SPECIAL_TEXT = {"STOP": "⛔ STOP MOVE", "CHG": "❓ CHANGE MOVE", "P2": "➕ +2"}
IDLE_SECONDS = 45            # others may let a bot play for an idle student
ROOM_LIFETIME = 6 * 3600     # rooms are deleted after 6 hours
MATCH_WINDOW = 30 * 60       # auto-match only joins tables opened in the last 30 min


def build_deck():
    """52 cards: 16 Active, 16 Passive, 8 Grammar, 4 Stop, 4 Change, 4 +2."""
    deck, cid = [], 0
    for s, st_ in enumerate(SETS):
        for v in (0, 1):
            for _ in range(2):
                deck.append({"id": cid, "t": "A", "s": s, "v": v, "x": st_["a"][v]}); cid += 1
                deck.append({"id": cid, "t": "P", "s": s, "v": v, "x": st_["p"][v]}); cid += 1
            deck.append({"id": cid, "t": "G", "s": s, "v": v, "x": st_["g"][v]}); cid += 1
    for t, x in (("STOP", "STOP MOVE"), ("CHG", "CHANGE MOVE"), ("P2", "+2")):
        for _ in range(4):
            deck.append({"id": cid, "t": t, "x": x}); cid += 1
    random.shuffle(deck)
    return deck


# ------------------------------------------------------------------
# GAME LOGIC (4 seats; each seat is a student or a bot)
# ------------------------------------------------------------------
class Game:
    def __init__(self, names, bots):
        self.names, self.bots = list(names), list(bots)
        self.deck = build_deck()
        self.hands = [[self.deck.pop() for _ in range(8)] for _ in range(4)]
        first = self.deck.pop()
        while first["t"] in SPECIAL:
            self.deck.insert(0, first)
            first = self.deck.pop()
        self.disc = [first]
        self.ref = first            # last normal card (used for matching)
        self.need = None            # type forced by Change Move
        self.pending = 0            # accumulated +2
        self.cur = 0
        self.only = None            # after drawing: only this card may be played
        self.drew = False
        self.pick = None            # Change Move card waiting for a type
        self.owe = [False] * 4      # forgot to say PASSIVE!
        self.over = None
        self.counted = False
        self.turn_since = time.time()
        self.log = ["Game started. Top card: " + first["x"]]

    def top(self):
        return self.disc[-1]

    def add_log(self, msg):
        self.log = (self.log + [msg])[-7:]

    def can_play(self, c):
        if self.pending:
            return c["t"] == "P2"
        if c["t"] in SPECIAL:
            return True
        if self.need:
            return c["t"] == self.need
        r = self.ref
        if c["t"] == "G" or r["t"] == "G":     # Grammar <-> related sentence only
            return c["t"] != r["t"] and c["s"] == r["s"] and c["v"] == r["v"]
        return c["t"] == r["t"] or (c["s"] == r["s"] and c["v"] == r["v"])

    def playable(self, p):
        return [c for c in self.hands[p]
                if self.can_play(c) and (self.only is None or c["id"] == self.only)]

    def give(self, p):
        if not self.deck:
            top = self.disc.pop()
            self.deck = self.disc
            random.shuffle(self.deck)
            self.disc = [top]
        if not self.deck:
            return None
        c = self.deck.pop()
        self.hands[p].append(c)
        return c

    def check_owe(self, actor):
        """Reached one card without saying PASSIVE! -> draw 2 when somebody else acts."""
        for q in range(4):
            if q != actor and self.owe[q]:
                self.give(q); self.give(q)
                self.owe[q] = False
                self.add_log(f"{self.names[q]} forgot to say PASSIVE! (+2 cards)")

    def act(self, p, c, typ=None):
        self.check_owe(p)
        self.owe[p] = False
        self.hands[p] = [x for x in self.hands[p] if x["id"] != c["id"]]
        self.disc.append(c)
        self.pick = None
        skip = False
        msg = f"{self.names[p]} played: {c['x']}"
        if c["t"] == "STOP":
            skip = True
        elif c["t"] == "CHG":
            if not typ:
                n = Counter(x["t"] for x in self.hands[p] if x["t"] in TYPE_NAMES)
                typ = max("APG", key=lambda k: n[k])
            self.need = typ
            msg += f" → {TYPE_NAMES[typ]}"
        elif c["t"] == "P2":
            self.pending += 2
        else:
            self.ref, self.need = c, None
        self.add_log(msg)
        if not self.hands[p]:
            self.over = p
            return
        if len(self.hands[p]) == 1:
            if self.bots[p]:
                self.add_log(f"{self.names[p]}: PASSIVE!")
            else:
                self.owe[p] = True
        self.advance(p, skip)

    def advance(self, p, skip):
        n = (p + 1) % 4
        if skip:
            self.add_log(f"{self.names[n]} is skipped")
            n = (n + 1) % 4
        self.cur, self.only, self.drew = n, None, False
        self.turn_since = time.time()

    def draw_act(self, p):
        self.check_owe(p)
        if self.pending:
            n, self.pending = self.pending, 0
            for _ in range(n):
                self.give(p)
            self.add_log(f"{self.names[p]} draws {n} cards")
            return self.advance(p, False)
        c = self.give(p)
        self.add_log(f"{self.names[p]} draws a card")
        if c and self.can_play(c):
            if not self.bots[p]:
                self.only, self.drew = c["id"], True
                return
            return self.act(p, c)
        self.advance(p, False)

    def bot_turn(self):
        p = self.cur
        ok = self.playable(p)
        if not ok:
            return self.draw_act(p)
        norm = [c for c in ok if c["t"] not in SPECIAL]
        spec = [c for c in ok if c["t"] in SPECIAL]
        if self.pending:
            pick = spec[0]
        elif spec and (not norm or random.random() < 0.25):
            pick = random.choice(spec)
        else:
            pick = random.choice(norm)
        self.act(p, pick)

    def run_bots(self):
        while self.over is None and self.bots[self.cur]:
            self.bot_turn()

    # ---- student actions (p = seat number) ----------------------
    def _mine(self, p):
        return self.over is None and self.cur == p

    def human_play(self, p, cid):
        if not self._mine(p) or self.pick:
            return
        c = next((x for x in self.hands[p] if x["id"] == cid), None)
        if not c:
            return
        if not self.can_play(c) or (self.only is not None and cid != self.only):
            return self.add_log("✗ That card cannot be played now. Check the rule.")
        if c["t"] == "CHG":
            self.pick = c
            return
        self.act(p, c)
        self.run_bots()

    def human_type(self, p, typ):
        if self._mine(p) and self.pick and typ in TYPE_NAMES:
            self.act(p, self.pick, typ)
            self.run_bots()

    def human_draw(self, p):
        if not self._mine(p) or self.pick or self.drew:
            return
        if not self.pending and any(self.can_play(c) for c in self.hands[p]):
            return self.add_log("✗ You still have a playable card.")
        self.draw_act(p)
        self.run_bots()

    def human_pass(self, p):
        if self._mine(p) and self.drew:
            self.advance(p, False)
            self.run_bots()

    def human_announce(self, p):
        if self.owe[p]:
            self.owe[p] = False
            self.add_log(f"{self.names[p]}: PASSIVE!")

    def nudge(self, by):
        """Let a bot play for an idle student."""
        p = self.cur
        if (self.over is None and not self.bots[p] and p != by
                and time.time() - self.turn_since >= IDLE_SECONDS):
            self.add_log(f"A bot plays for {self.names[p]} (idle)")
            self.pick = None
            self.bot_turn()
            self.run_bots()

    def status(self):
        if self.pending:
            return f"+{self.pending} penalty: play a +2 card or draw {self.pending}"
        if self.need:
            return f"Next card must be: {TYPE_NAMES[self.need]}"
        if self.ref["t"] == "G":
            return "Play a sentence that uses this grammar rule"
        return "Play the same kind of sentence, or a related card"


# ------------------------------------------------------------------
# ROOMS (shared by every browser connected to this server)
# ------------------------------------------------------------------
class Room:
    def __init__(self, code, public):
        self.code, self.public = code, public
        self.players = []            # dicts: sid, name, email, token
        self.game = None
        self.round = 0
        self.wins = {}
        self.lock = threading.RLock()
        self.created = time.time()

    def seat(self, token):
        for i, p in enumerate(self.players):
            if p["token"] == token:
                return i
        return None

    def seat_sid(self, sid):
        for i, p in enumerate(self.players):
            if p["sid"] == sid:
                return i
        return None

    def active_for(self, sid):
        """Is this student currently seated (and not finished / not left)?"""
        i = self.seat_sid(sid)
        if i is None:
            return False
        if self.game is None:
            return True
        return self.game.over is None and not self.game.bots[i]

    def start(self):
        n = len(self.players)
        names = [p["name"] for p in self.players] + BOT_NAMES[:4 - n]
        self.game = Game(names, [False] * n + [True] * (4 - n))
        self.round += 1
        for p in self.players:
            store().log("game_start", p["sid"], p["name"], p["email"], self.code,
                        f"round {self.round}")
        self.game.run_bots()

    def leave(self, token):
        with self.lock:
            i = self.seat(token)
            if i is None:
                return
            p = self.players[i]
            store().log("leave", p["sid"], p["name"], p["email"], self.code,
                        "lobby" if self.game is None else "in game")
            if self.game is None:
                self.players.pop(i)
            elif not self.game.bots[i]:
                g = self.game
                g.bots[i], g.owe[i] = True, False
                g.names[i] = p["name"] + " (left)"
                if g.over is None and g.cur == i:
                    g.run_bots()


@st.cache_resource
def registry():
    return {"rooms": {}, "lock": threading.Lock()}


def clean_text(raw, pattern, n):
    return re.sub(r"\s+", " ", re.sub(pattern, "", raw or "")).strip()[:n]


def clean_name(raw):
    return clean_text(raw, r"[^\w .'-]", 20)


def clean_sid(raw):
    return clean_text(raw, r"[^A-Za-z0-9._-]", 20).upper()


def _new_code(reg):
    while True:
        code = "".join(random.choices("ABCDEFGHJKMNPQRSTUVWXYZ23456789", k=4))
        if code not in reg["rooms"]:
            return code


def _seat_player(room, player):
    """Seat the player in the room (call with the room lock held). Returns (ok, msg)."""
    i = room.seat_sid(player["sid"])
    if i is not None:                       # already seated: reuse the old seat
        player["token"] = room.players[i]["token"]
        return True, "Welcome back!"
    if room.game is not None:
        return False, "This game has already started."
    if len(room.players) >= 4:
        return False, "This table is full (4 players)."
    room.players.append(player)
    store().log("join", player["sid"], player["name"], player["email"], room.code)
    if len(room.players) == 4:
        room.start()
    return True, "Joined."


def create_private_room(player):
    reg = registry()
    with reg["lock"]:
        now = time.time()
        for c in [c for c, r in reg["rooms"].items() if now - r.created > ROOM_LIFETIME]:
            del reg["rooms"][c]
        room = Room(_new_code(reg), public=False)
        reg["rooms"][room.code] = room
    with room.lock:
        _seat_player(room, player)
    return room, ""


def join_by_code(code, player):
    room = registry()["rooms"].get((code or "").strip().upper())
    if room is None:
        return None, "Room not found. Check the code."
    with room.lock:
        ok, msg = _seat_player(room, player)
    return (room, "") if ok else (None, msg)


def matchmake(player):
    """Put the student at an open table (or open a new one)."""
    reg = registry()
    with reg["lock"]:
        now = time.time()
        for c in [c for c, r in reg["rooms"].items() if now - r.created > ROOM_LIFETIME]:
            del reg["rooms"][c]
        for room in reg["rooms"].values():               # 1) a table I already sit at
            if room.active_for(player["sid"]):
                with room.lock:
                    _seat_player(room, player)
                return room
        open_rooms = sorted((r for r in reg["rooms"].values()
                             if r.public and r.game is None and len(r.players) < 4
                             and now - r.created < MATCH_WINDOW), key=lambda r: r.created)
        for room in open_rooms:                          # 2) the oldest open table
            with room.lock:
                ok, _ = _seat_player(room, player)
            if ok:
                return room
        room = Room(_new_code(reg), public=True)         # 3) a new table
        reg["rooms"][room.code] = room
        with room.lock:
            _seat_player(room, player)
        return room


def start_game(code):
    """Start (or restart after a finished game). Safe if several students click at once."""
    room = registry()["rooms"].get(code)
    if room:
        with room.lock:
            if room.game is None or room.game.over is not None:
                room.start()


def do(code, method, *args):
    room = registry()["rooms"].get(code)
    if room and room.game:
        with room.lock:
            getattr(room.game, method)(*args)


def get_secret(key):
    try:
        return st.secrets.get(key)
    except Exception:
        return None


# ------------------------------------------------------------------
# STORAGE: activity log + student accounts
# Google Sheet through a free Apps Script web app if configured,
# otherwise a local SQLite file (lost when the app restarts).
# Everything is also kept in memory, so the screens are always instant and up to date.
# ------------------------------------------------------------------
COLS = ["time", "event", "student_id", "name", "email", "room", "detail"]
ACC_COLS = ["student_id", "name", "salt", "pw_hash", "created", "updated"]
EVENT_LABELS = {"register": "Created account", "login": "Logged in", "join": "Joined a table",
                "game_start": "Game started", "game_complete": "Game completed",
                "leave": "Left a table", "password_reset": "Password reset"}
MAX_FAILS, LOCK_SECONDS = 5, 300


def now_str():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def hash_pw(pw, salt):
    return hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), bytes.fromhex(salt), 120_000).hex()


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.q = queue.Queue()
        self.retry, self.acc_retry = [], []
        self.fails = {}
        self.error = ""
        self.url = str(get_secret("SHEET_WEBHOOK_URL") or "").strip()
        self.token = str(get_secret("SHEET_WEBHOOK_TOKEN") or "")
        self.remote = bool(self.url)
        self.path = os.environ.get("GAME_LOG_DB", "game_log.db")
        self.rows, self.accounts = [], {}
        with self._db() as c:
            c.execute("CREATE TABLE IF NOT EXISTS log(time TEXT,event TEXT,student_id TEXT,"
                      "name TEXT,email TEXT,room TEXT,detail TEXT)")
            c.execute("CREATE TABLE IF NOT EXISTS accounts(student_id TEXT PRIMARY KEY,name TEXT,"
                      "salt TEXT,pw_hash TEXT,created TEXT,updated TEXT)")
        self._load()
        threading.Thread(target=self._worker, daemon=True).start()

    # ---- low level ------------------------------------------------
    @contextlib.contextmanager
    def _db(self):
        conn = sqlite3.connect(self.path)
        try:
            yield conn
            conn.commit()
        finally:
            conn.close()

    def _call(self, method, **kw):
        import requests
        if method == "post":
            r = requests.post(self.url, json={"token": self.token, **kw}, timeout=30)
        else:
            r = requests.get(self.url, params={"token": self.token, **kw}, timeout=30)
        res = r.json()
        if not res.get("ok"):
            raise RuntimeError(res.get("error", "unknown error"))
        return res

    @staticmethod
    def _fit(row, n):
        return ([str(x) for x in row] + [""] * n)[:n]

    def _load(self):
        loaded = False
        if self.remote:
            try:
                log_rows = self._call("get", sheet="log")["rows"]
                acc_rows = self._call("get", sheet="accounts")["rows"]
                self.rows = [self._fit(r, 7) for r in log_rows if str(r[0]).strip()]
                self.accounts = {str(r[0]): dict(zip(ACC_COLS, self._fit(r, 6)))
                                 for r in acc_rows if str(r[0]).strip()}
                loaded = True
            except Exception as e:
                self.error = f"Could not read the Google Sheet ({type(e).__name__}: {e})"
        if not loaded:
            with self._db() as c:
                self.rows = [list(r) for r in c.execute("SELECT * FROM log")]
                self.accounts = {r[0]: dict(zip(ACC_COLS, r))
                                 for r in c.execute("SELECT * FROM accounts")}

    def _worker(self):
        while True:
            rows = [self.q.get()]
            while len(rows) < 20:
                try:
                    rows.append(self.q.get_nowait())
                except queue.Empty:
                    break
            try:
                with self._db() as c:
                    c.executemany("INSERT INTO log VALUES (?,?,?,?,?,?,?)", rows)
            except Exception as e:
                self.error = f"{type(e).__name__}: {e}"
            if self.remote:
                batch = self.retry + rows
                try:
                    self._call("post", action="append", sheet="log", rows=batch)
                    self.retry, self.error = [], ""
                except Exception as e:
                    self.retry = batch[-500:]
                    self.error = f"Google Sheet not reachable ({type(e).__name__}: {e})"

    def _persist(self, acc):
        row = [acc[k] for k in ACC_COLS]
        with self._db() as c:
            c.execute("INSERT OR REPLACE INTO accounts VALUES (?,?,?,?,?,?)", row)
        if self.remote:
            with self.lock:
                self.acc_retry = [r for r in self.acc_retry if r[0] != row[0]] + [row]
                try:
                    for r in list(self.acc_retry):
                        self._call("post", action="upsert", sheet="accounts", row=r)
                        self.acc_retry.remove(r)
                    self.error = ""
                except Exception as e:
                    self.error = f"Account saved locally, Google Sheet not reachable ({type(e).__name__}: {e})"

    # ---- activity log ---------------------------------------------
    def log(self, event, sid="", name="", email="", room="", detail=""):
        row = [now_str(), event, str(sid), name, email, room, detail]
        with self.lock:
            self.rows.append(row)
        self.q.put(row)

    def read(self):
        with self.lock:
            return pd.DataFrame(list(self.rows), columns=COLS)

    # ---- accounts -------------------------------------------------
    def _locked(self, key):
        n, last = self.fails.get(key, (0, 0.0))
        if time.time() - last >= LOCK_SECONDS:
            n = 0
        return n

    def _fail(self, key):
        self.fails[key] = (self._locked(key) + 1, time.time())

    def register(self, sid, name, pw):
        with self.lock:
            if sid in self.accounts:
                return None, "This Student ID already has an account. Please log in."
            salt, t = os.urandom(16).hex(), now_str()
            acc = {"student_id": sid, "name": name, "salt": salt,
                   "pw_hash": hash_pw(pw, salt), "created": t, "updated": t}
            self.accounts[sid] = acc
        self._persist(acc)
        return acc, ""

    def check(self, sid, pw):
        with self.lock:
            if self._locked(sid) >= MAX_FAILS:
                return None, "Too many wrong attempts. Please wait 5 minutes."
            acc = self.accounts.get(sid)
            if acc and hmac.compare_digest(acc["pw_hash"], hash_pw(pw, acc["salt"])):
                self.fails.pop(sid, None)
                return acc, ""
            self._fail(sid)
            return None, "Wrong Student ID or password."

    def check_teacher(self, pw):
        secret = str(get_secret("TEACHER_PASSWORD") or "")
        with self.lock:
            if self._locked("__teacher__") >= MAX_FAILS:
                return False, "Too many wrong attempts. Please wait 5 minutes."
            if secret and hmac.compare_digest(pw.encode(), secret.encode()):
                self.fails.pop("__teacher__", None)
                return True, ""
            self._fail("__teacher__")
            return False, "Wrong teacher password."

    def set_password(self, sid, pw):
        with self.lock:
            acc = self.accounts.get(sid)
            if not acc:
                return False
            salt = os.urandom(16).hex()
            acc.update(salt=salt, pw_hash=hash_pw(pw, salt), updated=now_str())
        self._persist(acc)
        return True


@st.cache_resource
def store():
    return Store()


def summarize(df, accounts):
    """One row per student: registered, last login, logins, games started/completed, wins."""
    d = df[df["student_id"] != ""]
    ids = sorted(set(accounts) | set(d["student_id"]))
    out = pd.DataFrame(index=pd.Index(ids, name="student_id"))
    last_name = d.groupby("student_id")["name"].last()
    out["name"] = [accounts[i]["name"] if i in accounts else last_name.get(i, "") for i in ids]
    out["registered"] = [accounts[i]["created"] if i in accounts else "" for i in ids]
    out["last_login"] = (d[d.event == "login"].groupby("student_id")["time"].max()
                         .reindex(out.index).fillna(""))
    for col, mask in (("logins", d.event == "login"),
                      ("games_started", d.event == "game_start"),
                      ("games_completed", d.event == "game_complete"),
                      ("wins", (d.event == "game_complete") & (d.detail == "win"))):
        out[col] = d[mask].groupby("student_id").size().reindex(out.index).fillna(0).astype(int)
    return out.sort_values(["last_login", "registered"], ascending=False)


# ------------------------------------------------------------------
# SCREENS
# ------------------------------------------------------------------
@st.fragment(run_every=2)
def lobby(code, token):
    room = registry()["rooms"].get(code)
    if room is None or room.seat(token) is None or room.game is not None:
        st.rerun()                  # switch screens (or leave) on the next full run
        return
    st.markdown(f"### Waiting for players  ·  table `{code}`")
    st.write(f"**Players ({len(room.players)}/4):**")
    for i, p in enumerate(room.players):
        you = "  (you)" if p["token"] == token else ""
        st.write(f"{i + 1}. {p['name']} · ID {p['sid']}{you}")
    for _ in range(4 - len(room.players)):
        st.write("⬜ waiting…")
    st.caption("The game starts automatically when 4 students have joined. "
               "You can also start now: empty seats are played by bots.")
    st.button("▶ Start now", type="primary", on_click=start_game, args=(code,))


@st.fragment(run_every=2)
def board(code, token):
    room = registry()["rooms"].get(code)
    me = room.seat(token) if room else None
    if room is None or room.game is None or me is None or room.game.bots[me]:
        st.rerun()
        return
    g = room.game

    with room.lock:                          # record a finished game once
        if g.over is not None and not g.counted:
            g.counted = True
            for i, p in enumerate(room.players):
                if not g.bots[i]:
                    store().log("game_complete", p["sid"], p["name"], p["email"], code,
                                "win" if i == g.over else "lose")
            if g.over < len(room.players) and not g.bots[g.over]:
                sid = room.players[g.over]["sid"]
                room.wins[sid] = room.wins.get(sid, 0) + 1

    for col, k in zip(st.columns(3), (1, 2, 3)):
        p = (me + k) % 4
        mark = "▶ " if g.cur == p and g.over is None else ""
        icon = "🤖 " if g.bots[p] else ""
        col.metric(f"{mark}{icon}{g.names[p]}", f"{len(g.hands[p])} cards")

    with st.container(border=True):
        t1, t2 = st.columns([1, 3])
        t1.markdown(f"**Draw pile**\n\n{len(g.deck)} cards")
        c = g.top()
        t2.markdown("**Top card**")
        t2.markdown(f"### {SPECIAL_TEXT[c['t']] if c['t'] in SPECIAL else c['x']}")

    if g.over is not None:
        if g.over == me:
            st.success("🎉 You win!")
            if st.session_state.get("celebrated") != id(g):
                st.session_state.celebrated = id(g)
                st.balloons()
        else:
            st.error(f"{g.names[g.over]} wins!")
        st.button("Play again with the same players", type="primary",
                  on_click=start_game, args=(code,))
        st.caption("Scores: " + ", ".join(
            f"{p['name']} {room.wins.get(p['sid'], 0)}" for p in room.players))
        return

    my_turn = g.cur == me
    if my_turn:
        st.info("✅ Your turn. " + g.status())
    else:
        st.warning(f"Waiting for {g.names[g.cur]}… " + g.status())
        if not g.bots[g.cur] and time.time() - g.turn_since >= IDLE_SECONDS:
            st.button(f"⏭ {g.names[g.cur]} is idle: let a bot play this turn",
                      on_click=do, args=(code, "nudge", me))

    hint = st.toggle("Show hints", value=False, key="hint")
    st.subheader(f"Your hand ({len(g.hands[me])})")

    if my_turn and g.pick:
        st.write("**Choose the next card type:**")
        for col, t in zip(st.columns(3), "APG"):
            col.button(TYPE_NAMES[t], key="type" + t, on_click=do,
                       args=(code, "human_type", me, t), use_container_width=True)
    else:
        ctl = st.columns(3)
        ctl[0].button("Draw pending" if g.pending else "Draw a card", on_click=do,
                      args=(code, "human_draw", me), disabled=not my_turn or g.drew,
                      use_container_width=True)
        if my_turn and g.drew:
            ctl[1].button("Keep & pass", on_click=do, args=(code, "human_pass", me),
                          use_container_width=True)
        if g.owe[me]:
            ctl[2].button("PASSIVE!", type="primary", on_click=do,
                          args=(code, "human_announce", me), use_container_width=True)

    ok_ids = {x["id"] for x in g.playable(me)} if my_turn else set()
    cols = st.columns(2)
    for i, c in enumerate(g.hands[me]):
        label = SPECIAL_TEXT[c["t"]] if c["t"] in SPECIAL else c["x"]
        if hint and c["id"] in ok_ids:
            label = "✅ " + label
        cols[i % 2].button(label, key=f"card{c['id']}", on_click=do,
                           args=(code, "human_play", me, c["id"]),
                           use_container_width=True,
                           disabled=(not my_turn) or bool(g.pick))

    for line in g.log:
        st.caption(line)


def logout():
    for k in ("user", "room", "token"):
        st.session_state.pop(k, None)


def enter(room, token):
    st.session_state.room, st.session_state.token = room.code, token
    st.rerun()


def leave_and_clear(room=None, token=None):
    if room is not None:
        room.leave(token)
    st.session_state.pop("room", None)
    st.session_state.pop("token", None)


def find_active_room(sid):
    for room in registry()["rooms"].values():
        if room.active_for(sid):
            return room
    return None


def start_session(acc):
    ss = st.session_state
    store().log("login", acc["student_id"], acc["name"])
    ss.user = {"role": "student", "sid": acc["student_id"], "name": acc["name"]}
    room = find_active_room(acc["student_id"])        # resume a game in progress
    if room is not None:
        i = room.seat_sid(acc["student_id"])
        ss.room, ss.token = room.code, room.players[i]["token"]
    st.rerun()


def auth_screen():
    st.title("🃏 Active ↔ Passive Card Game")
    s = store()
    class_code = get_secret("CLASS_CODE")
    t_login, t_new, t_teacher = st.tabs(["Log in", "Create account", "Teacher"])

    with t_login:
        with st.form("login_form"):
            sid = st.text_input("Student ID", key="li_sid", max_chars=20)
            pw = st.text_input("Password", type="password", key="li_pw")
            go = st.form_submit_button("Log in", type="primary", use_container_width=True)
        if go:
            acc, err = s.check(clean_sid(sid), pw)
            if acc is None:
                st.error(err)
            else:
                start_session(acc)

    with t_new:
        st.caption("First time? Create your account once, then log in with your Student ID.")
        with st.form("register_form"):
            name = st.text_input("Your name", key="rg_name", max_chars=20)
            sid = st.text_input("Student ID", key="rg_sid", max_chars=20)
            pw = st.text_input("Password (at least 6 characters)", type="password", key="rg_pw")
            pw2 = st.text_input("Repeat password", type="password", key="rg_pw2")
            access = st.text_input("Class access code", type="password", key="rg_code") if class_code else ""
            go = st.form_submit_button("Create account", type="primary", use_container_width=True)
        if go:
            name, sid = clean_name(name), clean_sid(sid)
            if len(name) < 2:
                st.error("Please write your name (at least 2 letters).")
            elif len(sid) < 3:
                st.error("Please write your Student ID (at least 3 characters).")
            elif len(pw) < 6:
                st.error("The password must have at least 6 characters.")
            elif pw != pw2:
                st.error("The two passwords are not the same.")
            elif class_code and access != str(class_code):
                st.error("Wrong class access code.")
            else:
                acc, err = s.register(sid, name, pw)
                if acc is None:
                    st.error(err)
                else:
                    s.log("register", sid, name)
                    start_session(acc)

    with t_teacher:
        if not get_secret("TEACHER_PASSWORD"):
            st.info("Add TEACHER_PASSWORD to the app's Secrets to enable the teacher dashboard.")
        else:
            with st.form("teacher_form"):
                pw = st.text_input("Teacher password", type="password", key="tc_pw")
                go = st.form_submit_button("Open dashboard", use_container_width=True)
            if go:
                ok, err = s.check_teacher(pw)
                if ok:
                    st.session_state.user = {"role": "teacher", "sid": "", "name": "Teacher"}
                    st.rerun()
                else:
                    st.error(err)


def rules_expander():
    with st.expander("Rules in short"):
        st.write(
            "Decide whether each sentence is Active or Passive. Play the same kind of sentence, "
            "or a related card (the matching Active/Passive sentence, or its grammar rule). "
            "A Grammar card can only be played on a sentence that uses that rule, and it must be "
            "followed by a sentence using the same rule, never by another Grammar card. "
            "Stop skips the next player, Change Move chooses the next type, +2 cards stack. "
            "No valid move? Draw one card. One card left? Press PASSIVE! First to empty their hand wins.")


def play_menu(user):
    player = {"sid": user["sid"], "name": user["name"], "email": "", "token": uuid.uuid4().hex[:10]}
    st.write("Press **Start game** and you are matched with other students. "
             "The game begins when 4 students are seated (or press *Start now* in the waiting room).")
    if st.button("▶ Start game", type="primary", use_container_width=True):
        enter(matchmake(player), player["token"])
    with st.expander("Play with friends in a private room"):
        if st.button("Create private room", use_container_width=True):
            room, _ = create_private_room(player)
            enter(room, player["token"])
        code = st.text_input("Room code", max_chars=4, key="join_code")
        if st.button("Join room", use_container_width=True):
            room, err = join_by_code(code, player)
            if room is None:
                st.error(err)
            else:
                enter(room, player["token"])
    rules_expander()


def my_record(user):
    s = store()
    df = s.read()
    mine = df[df["student_id"] == user["sid"]]
    wins = int(((mine.event == "game_complete") & (mine.detail == "win")).sum())
    cols = st.columns(4)
    cols[0].metric("Logins", int((mine.event == "login").sum()))
    cols[1].metric("Games started", int((mine.event == "game_start").sum()))
    cols[2].metric("Games completed", int((mine.event == "game_complete").sum()))
    cols[3].metric("Wins", wins)
    logins = mine[mine.event == "login"]
    if len(logins) > 1:
        st.caption(f"Your previous login: {logins.time.iloc[-2]} (UTC)")
    st.subheader("My activity")
    view = mine.tail(50).iloc[::-1][["time", "event", "room", "detail"]].copy()
    view["event"] = view["event"].map(lambda e: EVENT_LABELS.get(e, e))
    st.dataframe(view, use_container_width=True, hide_index=True)
    with st.expander("Change password"):
        with st.form("chpw_form", clear_on_submit=True):
            old = st.text_input("Current password", type="password")
            new = st.text_input("New password (at least 6 characters)", type="password")
            go = st.form_submit_button("Change password")
        if go:
            if len(new) < 6:
                st.error("The new password must have at least 6 characters.")
            elif s.check(user["sid"], old)[0] is None:
                st.error("Current password is wrong.")
            else:
                s.set_password(user["sid"], new)
                st.success("Password changed.")


def student_home(user):
    top = st.columns([3, 1])
    top[0].markdown(f"**👤 {user['name']}** · ID {user['sid']}")
    top[1].button("Log out", on_click=logout, use_container_width=True)
    t_play, t_rec = st.tabs(["🎮 Play", "📊 My record"])
    with t_play:
        play_menu(user)
    with t_rec:
        my_record(user)


def teacher_panel():
    s = store()
    st.title("👩‍🏫 Teacher dashboard")
    st.button("Log out", on_click=logout)
    if s.remote and not s.error:
        st.success("Records are saved to your Google Sheet ✅")
    elif s.remote:
        st.error("Google Sheet problem: " + s.error)
    else:
        st.warning("No Google Sheet connected: accounts and records are kept in a temporary "
                   "file and are LOST when the app restarts.")
    st.button("Refresh")
    df, accounts = s.read(), dict(s.accounts)
    summ = summarize(df, accounts)
    t_stu, t_log, t_acc = st.tabs(["Students", "Activity log", "Accounts"])

    with t_stu:
        playing = sum(1 for r in registry()["rooms"].values() if r.game and r.game.over is None)
        m = st.columns(4)
        m[0].metric("Students registered", len(accounts))
        m[1].metric("Total logins", int((df.event == "login").sum()))
        m[2].metric("Games completed", int((df.event == "game_complete").sum()))
        m[3].metric("Tables playing now", playing)
        q = st.text_input("Search by name or Student ID", key="t_search").strip().lower()
        view = summ
        if q:
            view = summ[summ.index.str.lower().str.contains(q, regex=False)
                        | summ["name"].str.lower().str.contains(q, regex=False)]
        st.dataframe(view, use_container_width=True)
        st.download_button("Download students (CSV)", summ.to_csv().encode("utf-8"),
                           "students_summary.csv", "text/csv")
        logins = df[df.event == "login"]
        if not logins.empty:
            st.caption("Logins per day (UTC)")
            st.bar_chart(logins.groupby(logins["time"].str[:10]).size())
        st.caption("Times are shown in UTC. “Games completed” counts games that ended while "
                   "the student was still seated.")

    with t_log:
        c1, c2 = st.columns(2)
        events = c1.multiselect("Event", sorted(df["event"].unique()), key="t_events")
        sid_q = c2.text_input("Student ID contains", key="t_sid").strip().upper()
        view = df
        if events:
            view = view[view["event"].isin(events)]
        if sid_q:
            view = view[view["student_id"].str.upper().str.contains(sid_q, regex=False)]
        st.dataframe(view.tail(500).iloc[::-1], use_container_width=True, hide_index=True)
        st.download_button("Download full log (CSV)", df.to_csv(index=False).encode("utf-8"),
                           "game_log.csv", "text/csv")

    with t_acc:
        if not accounts:
            st.write("No accounts yet.")
        else:
            acc_view = pd.DataFrame(accounts.values())[["student_id", "name", "created", "updated"]]
            st.dataframe(acc_view, use_container_width=True, hide_index=True)
            st.subheader("Reset a student’s password")
            st.caption("Use this when a student forgets their password. "
                       "Give them the temporary password; they can change it after logging in.")
            with st.form("reset_form", clear_on_submit=True):
                sid = st.selectbox("Student ID", sorted(accounts))
                tmp = st.text_input("Temporary password (at least 6 characters)", type="password")
                go = st.form_submit_button("Reset password")
            if go:
                if len(tmp) < 6:
                    st.error("The temporary password must have at least 6 characters.")
                elif s.set_password(sid, tmp):
                    s.log("password_reset", sid, accounts[sid]["name"], detail="by teacher")
                    st.success(f"Password for {sid} was reset.")


def main():
    st.set_page_config(page_title="Active ↔ Passive Card Game", page_icon="🃏", layout="centered")
    ss = st.session_state
    user = ss.get("user")
    if not user:
        return auth_screen()
    if user["role"] == "teacher":
        return teacher_panel()
    if "room" not in ss:
        return student_home(user)

    code, token = ss.room, ss.token
    room = registry()["rooms"].get(code)
    i = room.seat(token) if room else None
    if room is None or i is None or (room.game is not None and room.game.bots[i]):
        leave_and_clear()
        st.rerun()
        return
    top = st.columns([3, 1])
    top[0].markdown(f"**🃏 Table `{code}`** · you are **{room.players[i]['name']}**")
    if top[1].button("Leave", use_container_width=True):
        leave_and_clear(room, token)
        st.rerun()
    if room.game is None:
        lobby(code, token)
    else:
        board(code, token)
    rules_expander()


if __name__ == "__main__":
    main()
