"""
Smart College Timetable Generator
---------------------------------
Solves the timetable as a Constraint Satisfaction Problem (CSP) using:
  * Backtracking Search
  * Minimum Remaining Values (MRV) variable ordering
  * Forward Checking (domain pruning after every assignment)

Run:   streamlit run app.py
"""

import html
import io
import math
import random
import sys
import time as _time
from collections import defaultdict
from datetime import date, datetime, time, timedelta

import pandas as pd
import streamlit as st

ALL_DAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

PALETTE = [
    ("#dbeafe", "#1d4ed8"), ("#fce7f3", "#be185d"), ("#dcfce7", "#15803d"),
    ("#fef9c3", "#a16207"), ("#ede9fe", "#6d28d9"), ("#ffedd5", "#c2410c"),
    ("#cffafe", "#0e7490"), ("#fee2e2", "#b91c1c"), ("#e0e7ff", "#4338ca"),
    ("#d9f99d", "#4d7c0f"), ("#fae8ff", "#a21caf"), ("#ccfbf1", "#0f766e"),
]


# =============================================================================
#  1.  CSP SOLVER
# =============================================================================
class _Stop(Exception):
    """Raised when the time / node limit is reached."""


class Lecture:
    __slots__ = ("vid", "division", "subject", "teacher", "room_type", "number")

    def __init__(self, vid, division, subject, teacher, room_type, number):
        self.vid = vid
        self.division = division
        self.subject = subject
        self.teacher = teacher
        self.room_type = room_type
        self.number = number


class TimetableCSP:
    """
    Variable : one lecture (division, subject, teacher, #k)
    Domain   : {(day, period, room)}
    Hard constraints
        - a teacher teaches at most one lecture per slot
        - a division attends at most one lecture per slot
        - a room hosts at most one lecture per slot
        - room type (Classroom / Lab) must match the subject
        - room capacity >= division strength
        - teacher unavailable slots are never used
        - a teacher has at most `max_day` lectures per day
        - a subject appears at most `max_subject_per_day` times per day per division
    """

    def __init__(self, days, n_periods, divisions, teachers, rooms, subjects,
                 courses, max_subject_per_day=0, use_mrv=True, use_fc=True,
                 seed=1, time_limit=30, node_limit=2_000_000):
        self.days = days
        self.n_days = len(days)
        self.n_periods = n_periods
        self.divisions = divisions      # {name: strength}
        self.teachers = teachers        # {name: {"max_day": int, "blocked": set((d,p))}}
        self.rooms = rooms              # {name: (type, capacity)}
        self.subjects = subjects        # {name: room_type}
        self.courses = courses          # [(division, subject, teacher, count)]
        self.use_mrv = use_mrv
        self.use_fc = use_fc
        self.rng = random.Random(seed)
        self.time_limit = time_limit
        self.node_limit = node_limit

        # statistics
        self.nodes = 0
        self.backtracks = 0
        self.deepest = 0
        self.stuck = None
        self.stopped = False
        self.elapsed = 0.0

        self._build()

    # ---------------------------------------------------------------- build
    def _build(self):
        total = defaultdict(int)
        for div, sub, _t, cnt in self.courses:
            total[(div, sub)] += cnt
        self.max_subj_day = {}
        for key, tot in total.items():
            auto = max(1, math.ceil(tot / max(1, self.n_days)))
            self.max_subj_day[key] = auto

        self.lect = {}
        self.domains = {}
        self.room_candidates = {}
        vid = 0
        for div, sub, teacher, cnt in self.courses:
            rtype = self.subjects[sub]
            rooms = [r for r, (rt, cap) in self.rooms.items()
                     if rt == rtype and cap >= self.divisions[div]]
            blocked = self.teachers[teacher]["blocked"]
            for k in range(cnt):
                lec = Lecture(vid, div, sub, teacher, rtype, k + 1)
                self.lect[vid] = lec
                self.room_candidates[vid] = rooms
                self.domains[vid] = {
                    (d, p, r)
                    for d in range(self.n_days)
                    for p in range(self.n_periods)
                    if (d, p) not in blocked
                    for r in rooms
                }
                vid += 1

        # static "degree" = number of other lectures sharing a teacher or division
        by_t, by_d = defaultdict(int), defaultdict(int)
        for lec in self.lect.values():
            by_t[lec.teacher] += 1
            by_d[lec.division] += 1
        self.degree = {v: by_t[l.teacher] + by_d[l.division] for v, l in self.lect.items()}

        # dynamic state
        self.assignment = {}
        self.unassigned = set(self.lect)
        self.teacher_busy, self.div_busy, self.room_busy = set(), set(), set()
        self.subj_day = defaultdict(int)
        self.teach_day = defaultdict(int)
        self.div_day = defaultdict(int)

    # --------------------------------------------------------------- search
    def solve(self):
        start = _time.time()
        self._t0 = start
        sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000))
        ok = False
        try:
            ok = self._search()
        except _Stop:
            self.stopped = True
        self.elapsed = _time.time() - start
        return ok

    def _tick(self):
        self.nodes += 1
        if self.nodes > self.node_limit or (_time.time() - self._t0) > self.time_limit:
            raise _Stop()

    def _search(self):
        if not self.unassigned:
            return True
        var = self._select_variable()
        v = self.lect[var]
        values = self._ordered_values(v)
        depth = len(self.assignment)
        for val in values:
            if not self.use_fc and not self._consistent(v, val):
                continue
            self._tick()
            removed, ok = self._assign(v, val)
            if ok and self._search():
                return True
            self._unassign(v, val, removed)
            self.backtracks += 1
        if depth >= self.deepest:
            self.deepest = depth
            self.stuck = v
        return False

    # ------------------------------------------------- variable / value order
    def _select_variable(self):
        if not self.use_mrv:
            return min(self.unassigned)
        if self.use_fc:
            return min(self.unassigned,
                       key=lambda u: (len(self.domains[u]), -self.degree[u], u))
        # without FC the MRV count has to be computed on demand
        def remaining(u):
            lec = self.lect[u]
            return sum(1 for x in self.domains[u] if self._consistent(lec, x))
        return min(self.unassigned, key=lambda u: (remaining(u), -self.degree[u], u))

    def _ordered_values(self, v):
        vals = sorted(self.domains[v.vid])
        self.rng.shuffle(vals)
        # prefer days on which the division / teacher is lightly loaded (spreads the week)
        vals.sort(key=lambda x: self.div_day[(v.division, x[0])]
                  + 0.5 * self.teach_day[(v.teacher, x[0])])
        return vals

    # -------------------------------------------------------------- constraints
    def _consistent(self, v, val):
        d, p, r = val
        if (v.teacher, d, p) in self.teacher_busy:
            return False
        if (v.division, d, p) in self.div_busy:
            return False
        if (r, d, p) in self.room_busy:
            return False
        if self.subj_day[(v.division, v.subject, d)] >= self.max_subj_day[(v.division, v.subject)]:
            return False
        if self.teach_day[(v.teacher, d)] >= self.teachers[v.teacher]["max_day"]:
            return False
        return True

    def _assign(self, v, val):
        d, p, r = val
        self.assignment[v.vid] = val
        self.unassigned.discard(v.vid)
        self.teacher_busy.add((v.teacher, d, p))
        self.div_busy.add((v.division, d, p))
        self.room_busy.add((r, d, p))
        self.subj_day[(v.division, v.subject, d)] += 1
        self.teach_day[(v.teacher, d)] += 1
        self.div_day[(v.division, d)] += 1

        removed = []
        if not self.use_fc:
            return removed, True

        subj_full = (self.subj_day[(v.division, v.subject, d)]
                     >= self.max_subj_day[(v.division, v.subject)])
        teach_full = (self.teach_day[(v.teacher, d)]
                      >= self.teachers[v.teacher]["max_day"])

        for uid in self.unassigned:
            u = self.lect[uid]
            dom = self.domains[uid]
            rm = set()
            if val in dom:                                   # same room, same slot
                rm.add(val)
            if u.teacher == v.teacher or u.division == v.division:   # same slot
                for room in self.room_candidates[uid]:
                    x = (d, p, room)
                    if x in dom:
                        rm.add(x)
            if (subj_full and u.division == v.division and u.subject == v.subject) or \
               (teach_full and u.teacher == v.teacher):      # daily limits
                rm.update(x for x in dom if x[0] == d)
            if rm:
                for x in rm:
                    dom.discard(x)
                    removed.append((uid, x))
                if not dom:                                  # domain wipe-out
                    return removed, False
        return removed, True

    def _unassign(self, v, val, removed):
        d, p, r = val
        for uid, x in removed:
            self.domains[uid].add(x)
        self.assignment.pop(v.vid, None)
        self.unassigned.add(v.vid)
        self.teacher_busy.discard((v.teacher, d, p))
        self.div_busy.discard((v.division, d, p))
        self.room_busy.discard((r, d, p))
        self.subj_day[(v.division, v.subject, d)] -= 1
        self.teach_day[(v.teacher, d)] -= 1
        self.div_day[(v.division, d)] -= 1

    # ----------------------------------------------------------------- output
    def entries(self):
        out = []
        for vid, (d, p, r) in self.assignment.items():
            l = self.lect[vid]
            out.append({"division": l.division, "subject": l.subject,
                        "teacher": l.teacher, "room": r, "day": d, "period": p})
        out.sort(key=lambda e: (e["division"], e["day"], e["period"]))
        return out


def validate_schedule(entries, problem):
    """Independent re-check of every hard constraint on the finished timetable."""
    issues = []
    seen_t, seen_d, seen_r = {}, {}, {}
    subj_day, teach_day = defaultdict(int), defaultdict(int)
    counts = defaultdict(int)
    for e in entries:
        d, p = e["day"], e["period"]
        for seen, key, label in ((seen_t, (e["teacher"], d, p), "Teacher"),
                                 (seen_d, (e["division"], d, p), "Division"),
                                 (seen_r, (e["room"], d, p), "Room")):
            if key in seen:
                issues.append(f"{label} clash: {key[0]} on {problem['days'][d]} P{p + 1}")
            seen[key] = 1
        rtype, cap = problem["rooms"][e["room"]]
        if rtype != problem["subjects"][e["subject"]]:
            issues.append(f"Room type mismatch: {e['subject']} in {e['room']}")
        if cap < problem["divisions"][e["division"]]:
            issues.append(f"Room too small: {e['room']} for {e['division']}")
        if (d, p) in problem["teachers"][e["teacher"]]["blocked"]:
            issues.append(f"{e['teacher']} is unavailable on {problem['days'][d]} P{p + 1}")
        subj_day[(e["division"], e["subject"], d)] += 1
        teach_day[(e["teacher"], d)] += 1
        counts[(e["division"], e["subject"], e["teacher"])] += 1
    for (t, d), n in teach_day.items():
        if n > problem["teachers"][t]["max_day"]:
            issues.append(f"{t} has {n} lectures on {problem['days'][d]} (limit {problem['teachers'][t]['max_day']})")
    need = defaultdict(int)
    for div, sub, t, cnt in problem["courses"]:
        need[(div, sub, t)] += cnt
    for key, n in need.items():
        if counts[key] != n:
            issues.append(f"{key[0]} / {key[1]}: expected {n} lectures, found {counts[key]}")
    return issues


# =============================================================================
#  2.  INPUT HANDLING
# =============================================================================
def _s(x):
    if x is None or (isinstance(x, float) and math.isnan(x)):
        return ""
    return str(x).strip()


def _n(x, default):
    try:
        v = float(x)
        if math.isnan(v):
            return default
        return int(v)
    except (TypeError, ValueError):
        return default


def parse_unavailable(text, days, n_periods):
    """'Mon, Fri-5, Tue-1' -> blocked {(day_idx, period_idx)}  (period numbers start at 1)"""
    blocked, bad = set(), []
    text = _s(text)
    if not text:
        return blocked, bad
    day_idx = {d.lower(): i for i, d in enumerate(days)}
    known = [d.lower() for d in ALL_DAYS]
    for tok in text.replace(";", ",").split(","):
        tok = tok.strip()
        if not tok:
            continue
        parts = tok.replace(" ", "").split("-")
        dname = parts[0][:3].lower()
        if dname not in known:
            bad.append(tok)
            continue
        if dname not in day_idx:        # a valid day that isn't a working day: nothing to block
            continue
        d = day_idx[dname]
        if len(parts) == 1:
            blocked |= {(d, p) for p in range(n_periods)}
        else:
            try:
                p = int(parts[1]) - 1
            except ValueError:
                bad.append(tok)
                continue
            if 0 <= p < n_periods:
                blocked.add((d, p))
            else:
                bad.append(tok)
    return blocked, bad


def build_slots(n_periods, start, minutes, breaks):
    """breaks: {after_period_no: [(label, minutes), ...]}"""
    fmt = lambda t: t.strftime("%H:%M")
    cur = datetime.combine(date.today(), start)
    slots = []
    for p in range(n_periods):
        end = cur + timedelta(minutes=minutes)
        slots.append({"type": "period", "p": p, "no": p + 1,
                      "start": fmt(cur), "end": fmt(end), "time": f"{fmt(cur)}–{fmt(end)}"})
        cur = end
        if p + 1 < n_periods:
            for label, mins in breaks.get(p + 1, []):
                end = cur + timedelta(minutes=mins)
                slots.append({"type": "break", "label": label, "minutes": mins,
                              "time": f"{fmt(cur)}–{fmt(end)}"})
                cur = end
    return slots


def collect_problem():
    """Read the UI tables and build a validated problem description."""
    ss = st.session_state
    errors, warnings = [], []

    days = [d for d in ALL_DAYS if d in ss.days_sel]
    n_periods = int(ss.n_periods)
    if not days:
        errors.append("Select at least one working day.")

    def clean(df, first):
        df = df.copy()
        df[first] = df[first].map(_s)
        return df[df[first] != ""]

    div_df = clean(ss.cfg["divisions"], "Division")
    tea_df = clean(ss.cfg["teachers"], "Teacher")
    room_df = clean(ss.cfg["rooms"], "Room")
    sub_df = clean(ss.cfg["subjects"], "Subject")
    crs_df = ss.cfg["courses"].copy()

    divisions, teachers, rooms, subjects = {}, {}, {}, {}
    for _, r in div_df.iterrows():
        if r["Division"] in divisions:
            errors.append(f"Duplicate division '{r['Division']}'.")
        divisions[r["Division"]] = _n(r["Strength"], 60)
    for _, r in tea_df.iterrows():
        if r["Teacher"] in teachers:
            errors.append(f"Duplicate teacher '{r['Teacher']}'.")
        blocked, bad = parse_unavailable(r.get("Unavailable"), days, n_periods)
        for b in bad:
            warnings.append(f"Teacher '{r['Teacher']}': could not understand unavailable entry '{b}'.")
        teachers[r["Teacher"]] = {"max_day": max(1, _n(r.get("Max lectures/day"), n_periods)),
                                  "blocked": blocked}
    for _, r in room_df.iterrows():
        if r["Room"] in rooms:
            errors.append(f"Duplicate room '{r['Room']}'.")
        rooms[r["Room"]] = (_s(r["Type"]) or "Classroom", _n(r["Capacity"], 60))
    for _, r in sub_df.iterrows():
        if r["Subject"] in subjects:
            errors.append(f"Duplicate subject '{r['Subject']}'.")
        subjects[r["Subject"]] = _s(r["Room type"]) or "Classroom"

    courses = []
    for _, r in crs_df.iterrows():
        div, sub, tea = _s(r["Division"]), _s(r["Subject"]), _s(r["Teacher"])
        if not (div or sub or tea):
            continue
        cnt = _n(r["Lectures/week"], 0)
        if div not in divisions:
            errors.append(f"Course row ({div or '?'}, {sub or '?'}): unknown division.")
        elif sub not in subjects:
            errors.append(f"Course row ({div}, {sub or '?'}): unknown subject.")
        elif tea not in teachers:
            errors.append(f"Course row ({div}, {sub}): unknown teacher '{tea or '?'}'.")
        elif cnt <= 0:
            errors.append(f"Course row ({div}, {sub}): lectures per week must be at least 1.")
        else:
            courses.append((div, sub, tea, cnt))

    if not divisions:
        errors.append("Add at least one division.")
    if not rooms:
        errors.append("Add at least one room.")
    if not courses and not errors:
        errors.append("Add at least one course (division + subject + teacher + lectures/week).")

    # ---- breaks
    breaks = defaultdict(list)
    for _, r in ss.cfg["breaks"].iterrows():
        after = _n(r["After period"], 0)
        if after <= 0 and not _s(r["Label"]):
            continue
        if not (1 <= after < n_periods):
            warnings.append(f"Break '{_s(r['Label']) or 'Break'}' after period {after} ignored "
                            f"(must be between 1 and {n_periods - 1}).")
            continue
        breaks[after].append((_s(r["Label"]) or "Break", max(1, _n(r["Duration (min)"], 10))))
    slots = build_slots(n_periods, ss.start_time, int(ss.p_minutes), breaks)

    problem = {"days": days, "n_periods": n_periods, "divisions": divisions,
               "teachers": teachers, "rooms": rooms, "subjects": subjects,
               "courses": courses, "slots": slots,
               "max_subject_per_day": int(ss.max_subj_day)}
    if errors:
        return problem, errors, warnings

    # ---- feasibility pre-checks (readable diagnostics)
    total_slots = len(days) * n_periods
    per_div, per_teacher, per_type = defaultdict(int), defaultdict(int), defaultdict(int)
    for div, sub, tea, cnt in courses:
        per_div[div] += cnt
        per_teacher[tea] += cnt
        per_type[subjects[sub]] += cnt
        ok_rooms = [r for r, (rt, cap) in rooms.items()
                    if rt == subjects[sub] and cap >= divisions[div]]
        if not ok_rooms:
            errors.append(f"No {subjects[sub]} with capacity ≥ {divisions[div]} exists for "
                          f"{div} / {sub}. Add a suitable room or lower the strength.")
    for div, n in per_div.items():
        if n > total_slots:
            errors.append(f"Division {div} needs {n} lectures but only {total_slots} slots exist per week.")
    for tea, n in per_teacher.items():
        avail = total_slots - len(teachers[tea]["blocked"])
        cap = min(avail, teachers[tea]["max_day"] * len(days))
        if n > cap:
            errors.append(f"Teacher {tea} is assigned {n} lectures/week but can teach at most {cap} "
                          f"(availability / max-per-day limits).")
    for rtype, n in per_type.items():
        n_rooms = sum(1 for rt, _ in rooms.values() if rt == rtype)
        if n > n_rooms * total_slots:
            errors.append(f"{n} {rtype} lectures need slots but {n_rooms} {rtype}(s) only offer "
                          f"{n_rooms * total_slots}.")
    seen = set()
    for div, sub, _t, _c in courses:
        if (div, sub) in seen:
            warnings.append(f"{div} / {sub} appears in more than one course row (counts are merged).")
        seen.add((div, sub))
    return problem, errors, warnings


# =============================================================================
#  3.  RENDERING / EXPORT HELPERS
# =============================================================================
def esc(x):
    return html.escape(str(x))


def cell_parts(kind, e):
    if kind == "division":
        return e["subject"], e["teacher"], e["room"]
    if kind == "teacher":
        return e["subject"], e["division"], e["room"]
    return e["subject"], e["division"], e["teacher"]       # room view


def make_index(entries):
    idx = defaultdict(list)
    for e in entries:
        for kind in ("division", "teacher", "room"):
            idx[(kind, e[kind], e["day"], e["period"])].append(e)
    return idx


def subject_colors(subjects):
    return {s: PALETTE[i % len(PALETTE)] for i, s in enumerate(sorted(subjects))}


def assign_fillers(entries, divisions, n_days, n_periods, activities):
    """Give every empty slot of every division an activity (Library, Self Study ...), spread evenly."""
    fill = {}
    if not activities:
        return fill
    for div in divisions:
        busy = {(e["day"], e["period"]) for e in entries if e["division"] == div}
        used, day_used = defaultdict(int), defaultdict(set)
        for d in range(n_days):
            for p in range(n_periods):
                if (d, p) in busy:
                    continue
                a = min(activities, key=lambda x: (x in day_used[d], used[x], activities.index(x)))
                fill[(div, d, p)] = a
                used[a] += 1
                day_used[d].add(a)
    return fill


def free_label(kind, name, di, p, res):
    """Text for a slot that has no lecture."""
    if kind == "division":
        return res["fill"].get((name, di, p), "Free period")
    return "Free period" if kind == "teacher" else "Vacant"


def grid_html(kind, name, res):
    days, slots, idx, colors = res["days"], res["slots"], res["idx"], res["colors"]
    h = ['<div class="tt-wrap"><table class="tt"><thead><tr><th class="tt-th-time">Time</th>']
    h += [f"<th>{esc(d)}</th>" for d in days]
    h.append("</tr></thead><tbody>")
    for s in slots:
        if s["type"] == "break":
            h.append(f'<tr><td class="tt-time">{esc(s["time"])}</td>'
                     f'<td colspan="{len(days)}" class="tt-break">☕ {esc(s["label"])} · {s["minutes"]} min</td></tr>')
            continue
        h.append(f'<tr><td class="tt-time"><b>P{s["no"]}</b><br><span>{esc(s["time"])}</span></td>')
        for di in range(len(days)):
            es = idx.get((kind, name, di, s["p"]), [])
            if not es:
                lab = free_label(kind, name, di, s["p"], res)
                if kind == "division" and (name, di, s["p"]) in res["fill"]:
                    h.append(f'<td class="tt-fill">📖 {esc(lab)}</td>')
                else:
                    h.append(f'<td class="tt-free">{esc(lab)}</td>')
                continue
            parts = []
            for e in es:
                sub, l2, l3 = cell_parts(kind, e)
                bg, fg = colors[e["subject"]]
                parts.append((bg, fg, f'<div class="tt-sub" style="color:{fg}">{esc(sub)}</div>'
                                      f'<div>👤 {esc(l2)}</div><div>🚪 {esc(l3)}</div>'))
            bg = parts[0][0]
            h.append(f'<td class="tt-cell" style="background:{bg};border-left-color:{parts[0][1]}">'
                     + "<hr>".join(p[2] for p in parts) + "</td>")
        h.append("</tr>")
    h.append("</tbody></table></div>")
    return "".join(h)


def grid_df(kind, name, res):
    rows = []
    for s in res["slots"]:
        if s["type"] == "break":
            rows.append([f"{s['label']} ({s['time']})"] + [""] * len(res["days"]))
            continue
        row = [f"P{s['no']} ({s['time']})"]
        for di in range(len(res["days"])):
            es = res["idx"].get((kind, name, di, s["p"]), [])
            row.append(" / ".join(" | ".join(cell_parts(kind, e)) for e in es)
                       if es else free_label(kind, name, di, s["p"], res))
        rows.append(row)
    return pd.DataFrame(rows, columns=["Time"] + res["days"])


def flat_df(res):
    time_of = {s["p"]: s for s in res["slots"] if s["type"] == "period"}
    rows = [{
        "Division": e["division"], "Day": res["days"][e["day"]], "Period": e["period"] + 1,
        "Start": time_of[e["period"]]["start"], "End": time_of[e["period"]]["end"],
        "Subject": e["subject"], "Teacher": e["teacher"], "Room": e["room"],
    } for e in res["entries"]]
    for (div, d, p), act in sorted(res["fill"].items()):
        rows.append({"Division": div, "Day": res["days"][d], "Period": p + 1,
                     "Start": time_of[p]["start"], "End": time_of[p]["end"],
                     "Subject": act, "Teacher": "-", "Room": "-"})
    df = pd.DataFrame(rows)
    order = {d: i for i, d in enumerate(res["days"])}
    return df.sort_values(["Division", "Day", "Period"], key=lambda c: c.map(order) if c.name == "Day" else c,
                          ignore_index=True)


def csv_bytes(df):
    return df.to_csv(index=False).encode("utf-8-sig")        # utf-8-sig opens cleanly in Excel


def build_pdf(res, kinds):
    from reportlab.lib import colors as rl
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
    from reportlab.platypus import PageBreak, Paragraph, SimpleDocTemplate, Spacer, Table, TableStyle

    def clean(t):                                   # base-14 fonts only know Latin-1
        return esc(str(t).encode("latin-1", "replace").decode("latin-1"))

    buf = io.BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=landscape(A4), leftMargin=24, rightMargin=24,
                            topMargin=24, bottomMargin=24, title="Timetable")
    base = getSampleStyleSheet()
    title = ParagraphStyle("t", parent=base["Title"], textColor=rl.HexColor("#4338ca"), fontSize=18)
    small = ParagraphStyle("s", parent=base["Normal"], fontSize=8, leading=10)
    head = ParagraphStyle("h", parent=base["Normal"], fontSize=10, leading=12,
                          textColor=rl.white, alignment=1, fontName="Helvetica-Bold")
    names = {"division": res["divisions"], "teacher": res["teachers"], "room": res["rooms"]}
    labels = {"division": "Division", "teacher": "Teacher", "room": "Room"}
    ndays = len(res["days"])
    avail = landscape(A4)[0] - 48
    widths = [90] + [(avail - 90) / ndays] * ndays

    story, first = [], True
    for kind in kinds:
        for name in names[kind]:
            if not first:
                story.append(PageBreak())
            first = False
            story.append(Paragraph(f"{labels[kind]} timetable – {clean(name)}", title))
            story.append(Spacer(1, 6))
            data = [[Paragraph("Time", head)] + [Paragraph(clean(d), head) for d in res["days"]]]
            style = [("BACKGROUND", (0, 0), (-1, 0), rl.HexColor("#4f46e5")),
                     ("GRID", (0, 0), (-1, -1), 0.6, rl.white),
                     ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                     ("BACKGROUND", (0, 1), (0, -1), rl.HexColor("#eef2ff"))]
            for s in res["slots"]:
                r = len(data)
                if s["type"] == "break":
                    data.append([Paragraph(f"<b>{clean(s['label'])}</b> ({s['time']}) - {s['minutes']} min", small)]
                                + [""] * ndays)
                    style += [("SPAN", (0, r), (-1, r)),
                              ("BACKGROUND", (0, r), (-1, r), rl.HexColor("#fef3c7")),
                              ("ALIGN", (0, r), (-1, r), "CENTER")]
                    continue
                row = [Paragraph(f"<b>P{s['no']}</b><br/>{s['time']}", small)]
                for di in range(ndays):
                    es = res["idx"].get((kind, name, di, s["p"]), [])
                    if not es:
                        lab = free_label(kind, name, di, s["p"], res)
                        row.append(Paragraph(f"<i>{clean(lab)}</i>", small))
                        if kind == "division" and (name, di, s["p"]) in res["fill"]:
                            style.append(("BACKGROUND", (di + 1, r), (di + 1, r), rl.HexColor("#e6faf5")))
                        continue
                    sub, l2, l3 = cell_parts(kind, es[0])
                    row.append(Paragraph(f"<b>{clean(sub)}</b><br/>{clean(l2)}<br/>{clean(l3)}", small))
                    style.append(("BACKGROUND", (di + 1, r), (di + 1, r),
                                  rl.HexColor(res["colors"][es[0]["subject"]][0])))
                data.append(row)
            tbl = Table(data, colWidths=widths, repeatRows=1)
            tbl.setStyle(TableStyle(style))
            story.append(tbl)
    if not story:
        story.append(Paragraph("Nothing selected.", base["Normal"]))
    doc.build(story)
    return buf.getvalue()


# =============================================================================
#  4.  SAMPLE DATA + SESSION STATE
# =============================================================================
def sample_data():
    return {
        "divisions": pd.DataFrame({"Division": ["SE-A", "SE-B"], "Strength": [60, 55]}),
        "teachers": pd.DataFrame({
            "Teacher": ["Prof. Mehta", "Prof. Kulkarni", "Prof. Iyer", "Prof. Patil",
                        "Prof. Joshi", "Prof. Nair"],
            "Max lectures/day": [4, 4, 4, 4, 4, 4],
            "Unavailable": ["", "Mon-1", "", "Fri-5, Fri-6", "", ""]}),
        "rooms": pd.DataFrame({
            "Room": ["R101", "R102", "Lab-1", "Lab-2"],
            "Type": ["Classroom", "Classroom", "Lab", "Lab"],
            "Capacity": [70, 70, 60, 60]}),
        "subjects": pd.DataFrame({
            "Subject": ["DSA", "DBMS", "OS", "Maths", "DSA Lab", "DBMS Lab"],
            "Room type": ["Classroom", "Classroom", "Classroom", "Classroom", "Lab", "Lab"]}),
        "breaks": pd.DataFrame({"After period": [2, 4], "Duration (min)": [15, 45],
                                "Label": ["Tea Break", "Lunch Break"]}),
        "courses": pd.DataFrame(
            [[d, s, t, n] for d in ("SE-A", "SE-B") for s, t, n in
             (("DSA", "Prof. Mehta", 4), ("DBMS", "Prof. Kulkarni", 4), ("OS", "Prof. Iyer", 3),
              ("Maths", "Prof. Patil", 4), ("DSA Lab", "Prof. Joshi", 2),
              ("DBMS Lab", "Prof. Nair", 2))],
            columns=["Division", "Subject", "Teacher", "Lectures/week"]),
    }


def init_state():
    ss = st.session_state
    if "initialized" in ss:
        return
    ver = ss.get("ver", 0) + 1
    ss.clear()
    ss.ver = ver
    ss.course_ver = 0
    ss.base = sample_data()
    ss.cfg = {k: v.copy() for k, v in ss.base.items()}
    ss.days_sel = ["Mon", "Tue", "Wed", "Thu", "Fri"]
    ss.n_periods = 6
    ss.start_time = time(9, 0)
    ss.p_minutes = 55
    ss.max_subj_day = 0
    ss.fill_on = True
    ss.fill_text = "Library, Self Study, Sports, Mentoring, Project Work"
    ss.result = None
    ss.failure = None
    ss.initialized = True


# =============================================================================
#  5.  STREAMLIT UI
# =============================================================================
CSS = """
<style>
.hero{background:linear-gradient(120deg,#4f46e5,#7c3aed 55%,#ec4899);padding:1.4rem 1.8rem;
border-radius:18px;color:#fff;margin-bottom:1rem;box-shadow:0 8px 24px rgba(79,70,229,.25)}
.hero h1{margin:0;font-size:2rem;color:#fff;padding:0}
.hero p{margin:.35rem 0 0;opacity:.92;font-size:1rem}
.chip{display:inline-block;background:rgba(255,255,255,.2);padding:.15rem .7rem;border-radius:999px;
margin:.5rem .35rem 0 0;font-size:.78rem}
.stButton>button,.stDownloadButton>button{border-radius:12px;font-weight:600;padding:.55rem 1.2rem}
.stButton>button[kind="primary"]{background:linear-gradient(120deg,#4f46e5,#ec4899);border:none;color:#fff}
.tt-wrap{overflow-x:auto;margin:.5rem 0 1.2rem}
table.tt{border-collapse:separate;border-spacing:6px;width:100%;table-layout:fixed;min-width:640px}
table.tt th{background:linear-gradient(120deg,#4f46e5,#7c3aed);color:#fff;padding:.55rem;border-radius:10px;
text-align:center;font-weight:600}
table.tt th.tt-th-time{width:110px}
table.tt td{padding:.45rem .55rem;font-size:.82rem;line-height:1.3;vertical-align:top}
td.tt-time{background:#eef2ff;color:#312e81;border-radius:10px;text-align:center}
td.tt-time span{font-size:.72rem;color:#6366f1}
td.tt-cell{border-radius:12px;color:#1f2937;border-left:5px solid #888}
td.tt-cell hr{margin:.3rem 0;border:0;border-top:1px dashed rgba(0,0,0,.25)}
.tt-sub{font-weight:700;font-size:.9rem;margin-bottom:.1rem}
td.tt-free{background:rgba(148,163,184,.12);color:#94a3b8;border-radius:12px;text-align:center}
td.tt-fill{background:repeating-linear-gradient(135deg,#f0fdfa,#f0fdfa 8px,#e6faf5 8px,#e6faf5 16px);color:#0f766e;border-radius:12px;text-align:center;font-weight:600;border:1px dashed #5eead4;vertical-align:middle!important}
td.tt-break{background:#fef3c7;color:#92400e;border-radius:10px;text-align:center;font-weight:600}
</style>
"""


def sidebar():
    ss = st.session_state
    with st.sidebar:
        st.header("🧠 Solver settings")
        ss.use_mrv = st.checkbox("Minimum Remaining Values (MRV)", value=True,
                                 help="Always pick the lecture with the fewest legal slots left.")
        ss.use_fc = st.checkbox("Forward Checking", value=True,
                                help="After each placement, remove conflicting slots from other lectures' domains.")
        ss.seed = st.number_input("Random seed", min_value=0, value=1, step=1,
                                  help="Change the seed to get a different valid timetable.")
        ss.time_limit = st.slider("Time limit (seconds)", 5, 120, 30)
        st.caption("Backtracking search is always on. Turn MRV / Forward Checking off to see how many "
                   "more nodes and backtracks the plain algorithm needs.")
        st.divider()
        if st.button("↺ Reset to sample data"):
            ss.pop("initialized", None)
            st.rerun()


def tab_schedule():
    ss = st.session_state
    st.subheader("Working days, periods & breaks")
    c1, c2 = st.columns(2)
    with c1:
        st.multiselect("Working days", ALL_DAYS, key="days_sel")
        st.number_input("Periods per day", 1, 12, key="n_periods")
    with c2:
        st.time_input("First period starts at", key="start_time")
        st.number_input("Period length (minutes)", 20, 180, step=5, key="p_minutes")

    st.markdown("**Breaks** – choose *after which period* each break happens and how long it is.")
    ss.cfg["breaks"] = st.data_editor(
        ss.base["breaks"], num_rows="dynamic", key=f"ed_breaks_{ss.ver}",
        column_config={
            "After period": st.column_config.NumberColumn("After period", min_value=1, max_value=11, step=1),
            "Duration (min)": st.column_config.NumberColumn("Duration (min)", min_value=1, max_value=180, step=5),
            "Label": st.column_config.TextColumn("Label"),
        })

    st.markdown("**Rule:** maximum lectures of one subject per day for a division")
    st.number_input("0 = automatic (lectures per week ÷ working days, rounded up)",
                    0, 6, key="max_subj_day")

    st.markdown("**Free periods**")
    st.checkbox("Fill empty periods with activities (no blank cells)", key="fill_on")
    st.text_input("Activities (comma separated, shared out evenly across the week)", key="fill_text",
                  disabled=not ss.fill_on)

    # live preview of the day structure
    br = defaultdict(list)
    for _, r in ss.cfg["breaks"].iterrows():
        a = _n(r["After period"], 0)
        if a >= 1:
            br[a].append((_s(r["Label"]) or "Break", max(1, _n(r["Duration (min)"], 10))))
    slots = build_slots(int(ss.n_periods), ss.start_time, int(ss.p_minutes), br)
    prev = pd.DataFrame([{"Slot": f"Period {s['no']}" if s["type"] == "period" else f"☕ {s['label']}",
                          "Time": s["time"]} for s in slots])
    st.markdown("**Day structure preview**")
    st.dataframe(prev, hide_index=True)


def tab_master():
    ss = st.session_state
    st.subheader("Classes, rooms, teachers & subjects")
    st.caption("Add rows with the ➕ at the bottom of each table, delete by selecting a row and pressing Delete.")
    k = ss.ver
    c1, c2 = st.columns(2)
    with c1:
        st.markdown("##### 🎓 Classes / Divisions")
        ss.cfg["divisions"] = st.data_editor(
            ss.base["divisions"], num_rows="dynamic", key=f"ed_div_{k}",
            column_config={"Strength": st.column_config.NumberColumn("Students", min_value=1, step=1)})
    with c2:
        st.markdown("##### 🚪 Rooms")
        ss.cfg["rooms"] = st.data_editor(
            ss.base["rooms"], num_rows="dynamic", key=f"ed_room_{k}",
            column_config={
                "Type": st.column_config.SelectboxColumn("Type", options=["Classroom", "Lab"], required=True),
                "Capacity": st.column_config.NumberColumn("Capacity", min_value=1, step=1)})
    c3, c4 = st.columns(2)
    with c3:
        st.markdown("##### 📘 Subjects")
        ss.cfg["subjects"] = st.data_editor(
            ss.base["subjects"], num_rows="dynamic", key=f"ed_sub_{k}",
            column_config={"Room type": st.column_config.SelectboxColumn(
                "Room type", options=["Classroom", "Lab"], required=True)})
    with c4:
        st.markdown("##### 👩‍🏫 Teachers")
        ss.cfg["teachers"] = st.data_editor(
            ss.base["teachers"], num_rows="dynamic", key=f"ed_tea_{k}",
            column_config={
                "Max lectures/day": st.column_config.NumberColumn("Max lectures/day", min_value=1, max_value=12, step=1),
                "Unavailable": st.column_config.TextColumn(
                    "Unavailable", help="Examples: 'Fri'  (whole day),  'Mon-1' (Monday period 1),  "
                                        "'Fri-5, Fri-6, Tue'")})


def _opts(df, col):
    return [x for x in df[col].map(_s).tolist() if x]


def tab_courses():
    ss = st.session_state
    st.subheader("Course assignments")
    st.caption("Each row = *this division studies this subject with this teacher N times a week*.")
    ss.cfg["courses"] = st.data_editor(
        ss.base["courses"], num_rows="dynamic", key=f"ed_courses_{ss.ver}_{ss.course_ver}",
        column_config={
            "Division": st.column_config.TextColumn("Division"),
            "Subject": st.column_config.TextColumn("Subject"),
            "Teacher": st.column_config.TextColumn("Teacher"),
            "Lectures/week": st.column_config.NumberColumn("Lectures/week", min_value=1, max_value=20, step=1)})

    st.markdown("##### ➕ Quick add (no typing mistakes)")
    divs, subs, teas = (_opts(ss.cfg["divisions"], "Division"), _opts(ss.cfg["subjects"], "Subject"),
                        _opts(ss.cfg["teachers"], "Teacher"))
    if not (divs and subs and teas):
        st.info("Add divisions, subjects and teachers in the *Master Data* tab first.")
        return
    with st.form("add_course"):
        c1, c2, c3, c4 = st.columns(4)
        f_divs = c1.multiselect("Division(s)", divs)
        f_sub = c2.selectbox("Subject", subs)
        f_tea = c3.selectbox("Teacher", teas)
        f_cnt = c4.number_input("Lectures / week", 1, 20, 3)
        if st.form_submit_button("Add course"):
            if not f_divs:
                st.warning("Pick at least one division.")
            else:
                cur = ss.cfg["courses"].copy()
                new = pd.DataFrame([[d, f_sub, f_tea, int(f_cnt)] for d in f_divs], columns=cur.columns)
                ss.base["courses"] = pd.concat([cur, new], ignore_index=True)
                ss.course_ver += 1
                st.rerun()


def run_generation():
    ss = st.session_state
    problem, errors, warnings = collect_problem()
    ss.result, ss.failure = None, None
    for w in warnings:
        st.warning(w)
    if errors:
        ss.failure = ["**Please fix these problems first:**"] + [f"• {e}" for e in errors]
        return

    solver = TimetableCSP(
        problem["days"], problem["n_periods"], problem["divisions"], problem["teachers"],
        problem["rooms"], problem["subjects"], problem["courses"],
        max_subject_per_day=problem["max_subject_per_day"],
        use_mrv=ss.use_mrv, use_fc=ss.use_fc, seed=int(ss.seed), time_limit=ss.time_limit)
    if problem["max_subject_per_day"] > 0:
        for key in solver.max_subj_day:
            solver.max_subj_day[key] = problem["max_subject_per_day"]
    empty = [solver.lect[v] for v, d in solver.domains.items() if not d]
    if empty:
        l = empty[0]
        ss.failure = [f"**{l.division} / {l.subject}** ({l.teacher}) has no legal slot at all – "
                      "check the teacher's unavailability, room types and room capacities."]
        return

    with st.spinner("Searching for a conflict-free timetable…"):
        ok = solver.solve()

    stats = {"lectures": len(solver.lect), "nodes": solver.nodes,
             "backtracks": solver.backtracks, "seconds": solver.elapsed}
    if not ok:
        l = solver.stuck
        why = "time / node limit reached" if solver.stopped else "search space exhausted – no solution exists"
        msg = [f"**No timetable found** ({why}). Explored {solver.nodes:,} nodes, {solver.backtracks:,} backtracks."]
        if l is not None:
            msg.append(f"• Hardest lecture to place: **{l.division} / {l.subject}** taught by **{l.teacher}**.")
        msg.append("• Try: more periods/days, more rooms, a higher max-lectures/day for teachers, "
                   "fewer teacher unavailability slots, or a bigger time limit / different seed.")
        ss.failure = msg
        return

    entries = solver.entries()
    activities = [a.strip() for a in ss.fill_text.replace("\n", ",").split(",") if a.strip()] if ss.fill_on else []
    issues = validate_schedule(entries, problem)
    ss.result = {
        "entries": entries, "stats": stats, "issues": issues, "days": problem["days"],
        "slots": problem["slots"], "idx": make_index(entries),
        "colors": subject_colors(problem["subjects"]),
        "divisions": list(problem["divisions"]), "rooms": list(problem["rooms"]),
        "teachers": sorted({e["teacher"] for e in entries}),
        "fill": assign_fillers(entries, list(problem["divisions"]), len(problem["days"]),
                               problem["n_periods"], activities),
    }


def tab_generate():
    ss = st.session_state
    st.subheader("Generate & view")
    st.write(f"Algorithm: **Backtracking** + **{'MRV' if ss.use_mrv else 'static order'}** + "
             f"**{'Forward Checking' if ss.use_fc else 'no pruning'}**")
    if st.button("🚀 Generate timetable", type="primary"):
        run_generation()

    if ss.failure:
        st.error("\n\n".join(ss.failure))
    res = ss.result
    if not res:
        return

    s = res["stats"]
    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Lectures placed", s["lectures"])
    m2.metric("Nodes explored", f"{s['nodes']:,}")
    m3.metric("Backtracks", f"{s['backtracks']:,}")
    m4.metric("Time", f"{s['seconds']:.2f}s")
    if res["issues"]:
        st.error("Independent validation found problems:\n\n" + "\n".join(f"• {i}" for i in res["issues"]))
    else:
        st.success("✅ Independent validation passed – no teacher, class or room clashes.")

    st.divider()
    view = st.radio("View by", ["Division", "Teacher", "Room", "Whole college"], horizontal=True)
    kind = {"Division": "division", "Teacher": "teacher", "Room": "room"}.get(view)
    if kind:
        names = {"division": res["divisions"], "teacher": res["teachers"], "room": res["rooms"]}[kind]
        name = st.selectbox(f"Select {view.lower()}", names)
        st.markdown(grid_html(kind, name, res), unsafe_allow_html=True)
        grid = grid_df(kind, name, res)
        grid_name = f"timetable_{kind}_{name}".replace(" ", "_")
    else:
        parts = []
        for d in res["divisions"]:
            st.markdown(f"#### 🎓 {esc(d)}")
            st.markdown(grid_html("division", d, res), unsafe_allow_html=True)
            g = grid_df("division", d, res)
            g.insert(0, "Division", d)
            parts.append(g)
        grid = pd.concat(parts, ignore_index=True)
        grid_name = "timetable_whole_college"

    # legend
    legend = "".join(f'<span class="chip" style="background:{bg};color:{fg}">{esc(sub)}</span>'
                     for sub, (bg, fg) in res["colors"].items())
    st.markdown(legend, unsafe_allow_html=True)

    st.divider()
    st.subheader("⬇️ Download")
    d1, d2, d3 = st.columns(3)
    d1.download_button("CSV – all lectures (flat list)", csv_bytes(flat_df(res)),
                       "timetable_all.csv", "text/csv")
    d2.download_button("CSV – current view (grid)", csv_bytes(grid), f"{grid_name}.csv", "text/csv")
    with d3:
        inc = st.multiselect("PDF pages for", ["Divisions", "Teachers", "Rooms"], default=["Divisions"])
        kinds = [{"Divisions": "division", "Teachers": "teacher", "Rooms": "room"}[x] for x in inc]
        try:
            st.download_button("PDF – printable timetable", build_pdf(res, kinds),
                               "timetable.pdf", "application/pdf")
        except ImportError:
            st.warning("PDF export needs reportlab:  pip install reportlab")


def main():
    st.set_page_config(page_title="Smart Timetable Generator", page_icon="🗓️", layout="wide")
    st.markdown(CSS, unsafe_allow_html=True)
    init_state()
    st.markdown(
        '<div class="hero"><h1>🗓️ Smart College Timetable Generator</h1>'
        '<p>Constraint-satisfaction timetabling – no clashes for teachers, classes or rooms.</p>'
        '<span class="chip">Backtracking Search</span><span class="chip">MRV</span>'
        '<span class="chip">Forward Checking</span><span class="chip">CSV + PDF export</span></div>',
        unsafe_allow_html=True)
    sidebar()
    t1, t2, t3, t4 = st.tabs(["⏰ Schedule & Breaks", "🏫 Master Data", "📚 Courses", "🚀 Generate & View"])
    with t1:
        tab_schedule()
    with t2:
        tab_master()
    with t3:
        tab_courses()
    with t4:
        tab_generate()


main()