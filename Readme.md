# 🗓️ Smart College Timetable Generator

A Streamlit web app that builds clash-free college timetables by treating the problem as a
**Constraint Satisfaction Problem (CSP)** and solving it with classic AI search techniques:

- **Backtracking Search**
- **Minimum Remaining Values (MRV)** – variable ordering heuristic
- **Forward Checking** – domain pruning after every assignment

You enter your classes, teachers, subjects, rooms and break timings in the browser, press one
button, and get a colour-coded timetable that you can download as **CSV** or **PDF**.

---

## ✨ Features

- Editable tables for **classes/divisions, rooms, subjects, teachers and course assignments**
- Configurable **working days, periods per day, start time and period length**
- Configurable **breaks**: choose *after which period* each break happens, how long it is, and its label
- Teacher rules: **max lectures per day** and **unavailable days / periods**
- Room rules: **Classroom vs Lab** matching and **capacity check**
- Optional **free-period fillers** (Library, Self Study, Sports…) so no cell is blank
- Views by **division, teacher, room, or whole college**
- Live solver statistics: lectures placed, nodes explored, backtracks, time taken
- Toggle **MRV** and **Forward Checking** on/off to compare algorithm performance
- Independent **validation** of the finished timetable (re-checks every rule from scratch)
- Friendly error messages when the input is impossible (for example, a teacher overloaded)
- **Export**: CSV (flat list), CSV (current grid view), PDF (one landscape page per division / teacher / room)

---

## 🚀 Quick start

**Requirements:** Python 3.9+

```bash
pip install -r requirements.txt
streamlit run app.py
```

The app opens at `http://localhost:8501` with sample data already loaded, so you can press
**Generate timetable** right away.

`requirements.txt`:

```
streamlit>=1.40
pandas
reportlab
```

---

## 🧭 How to use

1. **⏰ Schedule & Breaks** – pick working days, periods per day, first period start time and
   period length. Add breaks in the table (e.g. *after period 2, 15 min, Tea Break*;
   *after period 4, 45 min, Lunch Break*). A live preview of the day appears below.
2. **🏫 Master Data** – add or edit:
   - **Classes / Divisions** – name and number of students
   - **Rooms** – name, type (Classroom / Lab) and capacity
   - **Subjects** – name and the room type it needs
   - **Teachers** – max lectures per day and unavailable slots
3. **📚 Courses** – each row means *this division studies this subject with this teacher N times
   a week*. Use the **Quick add** form to pick values from dropdowns and add a subject to several
   divisions at once.
4. **🚀 Generate & View** – press **Generate timetable**, browse the views, then download CSV / PDF.

### Teacher "Unavailable" syntax

| Entry | Meaning |
|---|---|
| `Fri` | not available the whole of Friday |
| `Mon-1` | not available Monday, period 1 |
| `Fri-5, Fri-6, Tue` | comma-separated combination |

### Getting a completely full timetable (no free periods)

Make each division's **total lectures per week equal to its total slots**:

```
slots per division = working days × periods per day      (e.g. 5 × 6 = 30)
```

If the total is lower, the leftover slots are filled with free-period activities (or shown as
"Free period" if fillers are turned off).

---

## 🧠 How the solver works

**Variables** – one variable per lecture, e.g. `(SE-A, DSA, Prof. Mehta, #3)`.

**Domain** – every `(day, period, room)` combination that is initially legal for that lecture
(correct room type, enough capacity, teacher available).

**Hard constraints**

1. A teacher teaches at most one lecture per slot
2. A division attends at most one lecture per slot
3. A room hosts at most one lecture per slot
4. Room type must match the subject (Classroom / Lab)
5. Room capacity ≥ division strength
6. Teachers are never scheduled in their unavailable slots
7. A teacher has at most *max lectures/day* lectures per day
8. A subject appears at most *N* times per day for a division
   (default `N = ceil(lectures per week / working days)`, can be overridden)

**Search loop**

```
search():
    if no unassigned lectures: return success
    pick a lecture with MRV          # smallest remaining domain (ties: highest degree)
    for each value in its domain:    # ordered to spread lectures across the week
        assign it
        forward-check: remove conflicting values from other lectures' domains
        if no domain became empty and search(): return success
        undo assignment and pruning  # backtrack
    return failure
```

A time limit and node limit stop the search on very hard inputs, and the app then explains
which lecture was hardest to place and what to relax.

---

## 📁 Project structure

```
timetable_app/
├── app.py             # solver + Streamlit UI + CSV/PDF export (single file)
├── requirements.txt
└── README.md
```

Inside `app.py`:

| Section | What it contains |
|---|---|
| 1. CSP solver | `TimetableCSP` (backtracking, MRV, forward checking) and `validate_schedule` |
| 2. Input handling | table cleaning, unavailable-slot parser, break/slot builder, feasibility pre-checks |
| 3. Rendering / export | HTML grid, CSV builders, PDF builder (ReportLab) |
| 4. Sample data / state | default data and session-state setup |
| 5. UI | sidebar, four tabs, generation and download logic |

---

## 📤 Export formats

| File | Content |
|---|---|
| **CSV – all lectures** | one row per lecture: Division, Day, Period, Start, End, Subject, Teacher, Room (includes free-period activities) |
| **CSV – current view** | the grid you are looking at (rows = periods and breaks, columns = days) |
| **PDF** | landscape A4, colour-coded, one page per division / teacher / room (choose which in the app) |

CSV files are written with a UTF-8 BOM so they open correctly in Excel.

---

## 🛠️ Troubleshooting

| Problem | What to do |
|---|---|
| **"No timetable found"** | Add more periods/days or rooms, raise teachers' max lectures/day, remove some unavailability, increase the time limit in the sidebar, or try another seed |
| **Teacher / room overloaded message** | The total lectures assigned exceed available slots; reduce lectures/week or add teachers/rooms |
| **"No Lab with capacity ≥ …"** | Add a suitable room or reduce the division strength |
| **Course row has unknown division/subject/teacher** | The name doesn't match the Master Data tables exactly; use the Quick add form |
| **PDF button shows a warning** | Install ReportLab: `pip install reportlab` |
| **Edits disappear on refresh** | Data lives in the browser session only; use **Reset to sample data** to start over |

---

## ⚠️ Current limitations

- Every lecture occupies exactly **one period** (no double-period lab blocks yet)
- Data is **not saved** between browser sessions
- PDF export uses standard Latin-1 fonts, so non-Latin characters may not render in the PDF

## 🔭 Ideas for future work

- Double-period lab sessions
- Save / load projects (SQLite or JSON)
- Soft constraints (e.g. avoid first/last period for certain teachers, minimise gaps)
- Per-day period counts and half-day schedules
- Multi-section electives and shared lectures

---

## 📜 License

Free to use and modify for learning and academic projects.