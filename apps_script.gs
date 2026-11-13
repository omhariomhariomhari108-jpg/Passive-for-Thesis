// Paste this in your Google Sheet: Extensions > Apps Script (replace everything), then
// Deploy > New deployment > Web app (Execute as: Me, Who has access: Anyone).
// After any later edit: Deploy > Manage deployments > pencil > Version: New version > Deploy.
const TOKEN = "CHANGE-THIS-TO-A-LONG-RANDOM-TEXT";   // must match SHEET_WEBHOOK_TOKEN in Streamlit Secrets

const SHEETS = {
  log:      ["time", "event", "student_id", "name", "email", "room", "detail"],
  accounts: ["student_id", "name", "salt", "pw_hash", "created", "updated"]
};

function sheet_(name) {
  if (!SHEETS[name]) throw new Error("unknown sheet: " + name);
  const ss = SpreadsheetApp.getActiveSpreadsheet();
  let sh = ss.getSheetByName(name);
  if (!sh) sh = ss.insertSheet(name);
  if (sh.getLastRow() === 0) sh.appendRow(SHEETS[name]);
  return sh;
}

function out_(obj) {
  return ContentService.createTextOutput(JSON.stringify(obj))
    .setMimeType(ContentService.MimeType.JSON);
}

function doPost(e) {
  const lock = LockService.getScriptLock();
  try {
    const data = JSON.parse(e.postData.contents);
    if (data.token !== TOKEN) return out_({ok: false, error: "bad token"});
    lock.waitLock(20000);
    const sh = sheet_(data.sheet);
    const width = SHEETS[data.sheet].length;
    if (data.action === "append") {
      const rows = data.rows;
      const range = sh.getRange(sh.getLastRow() + 1, 1, rows.length, width);
      range.setNumberFormat("@");                 // keep text as text (IDs like 00123)
      range.setValues(rows);
    } else if (data.action === "upsert") {        // update the row with the same first column, or add it
      const row = data.row;
      const last = sh.getLastRow();
      let target = last + 1;
      if (last > 1) {
        const ids = sh.getRange(2, 1, last - 1, 1).getValues();
        for (let i = 0; i < ids.length; i++) {
          if (String(ids[i][0]) === String(row[0])) { target = i + 2; break; }
        }
      }
      const range = sh.getRange(target, 1, 1, width);
      range.setNumberFormat("@");
      range.setValues([row]);
    } else {
      return out_({ok: false, error: "unknown action"});
    }
    return out_({ok: true});
  } catch (err) {
    return out_({ok: false, error: String(err)});
  } finally {
    try { lock.releaseLock(); } catch (x) {}
  }
}

function doGet(e) {
  try {
    if (!e.parameter || e.parameter.token !== TOKEN) return out_({ok: false, error: "bad token"});
    const values = sheet_(e.parameter.sheet || "log").getDataRange().getValues();
    return out_({ok: true, rows: values.slice(1)});
  } catch (err) {
    return out_({ok: false, error: String(err)});
  }
}
