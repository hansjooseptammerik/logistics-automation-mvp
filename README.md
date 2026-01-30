# Logistics Automation MVP

A demo project showing how PDF-based orders can be converted into a structured logistics workflow without manual copying or printing.

This is an MVP demo focused on workflow automation and usability (not production-grade PDF parsing).

---

## What this demo shows

- Import PDF orders
- Automatically extract:
  - Client name
  - Phone number
  - Address
  - Items
- Dispatcher workflow:
  - Review extracted data
  - Add notes
  - Set delivery date and time window
  - Update status
- Route planning and worker assignment
- Worker view:
  - Assigned jobs only
  - Client details and item list
  - Call and navigation actions

---

## Tech stack

- Python
- Streamlit
- SQLite
- PyPDF

---

## Run locally (Windows-friendly)

### 1) Install dependencies
```bash
python -m pip install -r requirements.txt
