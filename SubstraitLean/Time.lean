/-!
# Timestamps: `date_part` and `date_trunc`

Timestamps are microseconds since 1970-01-01 00:00 (UTC, proleptic Gregorian
calendar). This file computes DataFusion's `date_part` and `date_trunc`
exactly, checked against DataFusion 51 by `python/tests/test_time.py`:

* `date_part` is `NULL` outside the dates `chrono` represents, the years
  -262143 to 262142.
* `date_trunc` to a day or less rounds down; below `-2⁶³` it wraps around.
  To a week (from Monday), month, quarter or year, DataFusion computes in
  nanoseconds, so it fails (or gives garbage) unless the timestamp and its
  truncation are within ±2⁶³ ns, i.e. ±9223372036854775 µs.

The calendar is computed through `monthIndex d = 12 · year + (month - 1)` of
day `d` and `monthStart i`, the first day of month `i`. The one fact about
them proved here is `monthIndex_spec`: day `d` lies in month `monthIndex d`.
Monotonicity of years and truncations follows, which is what the contract
checker uses.
-/

namespace Substrait.Time

def usPerDay : Int := 86_400_000_000

/-! ## The calendar

Years here start on 1 March (so leap days end them), counted from 0000-03-01,
which is day `-719468`. Every 400 years have 146097 days. -/

/-- The day year `y` starts on, counted from 0000-03-01. -/
def yearStart (y : Int) : Int := 365 * y + y / 4 - y / 100 + y / 400

/-- The year of day `x ∈ [0, 146097)` of a 400-year era: 100-year centuries
(the last one a day longer), 4-year cycles in them, then years. -/
def eraYear (x : Int) : Int :=
  let c := min (x / 36524) 3
  let r := x - 36524 * c
  let q := r / 1461
  100 * c + 4 * q + min ((r - 1461 * q) / 365) 3

/-- Days from 1 March to the first of month `m` (`0` = March, …, `11` = February). -/
def monthOff (m : Int) : Int := (153 * m + 2) / 5

/-- The (March-based) year of day `d`, counted from 1970-01-01. -/
def shiftedYear (d : Int) : Int :=
  400 * ((d + 719468) / 146097) + eraYear ((d + 719468) % 146097)

def dayInYear (d : Int) : Int := d + 719468 - yearStart (shiftedYear d)

/-- `12 · year + (month - 1)` of day `d`. -/
def monthIndex (d : Int) : Int := 12 * shiftedYear d + (5 * dayInYear d + 2) / 153 + 2

/-- The first day of month `i` (as in `monthIndex`). -/
def monthStart (i : Int) : Int := yearStart ((i - 2) / 12) + monthOff ((i - 2) % 12) - 719468

theorem yearStart_cqk {c q k : Int} (hc : 0 ≤ c ∧ c ≤ 3) (hq : 0 ≤ q ∧ q ≤ 24) (hk : 0 ≤ k ∧ k ≤ 3) :
    yearStart (100 * c + 4 * q + k) = 36524 * c + 1461 * q + 365 * k := by
  simp only [yearStart]; omega

theorem yearStart_century (c : Int) :
    yearStart (100 * (c + 1)) = 36524 * (c + 1) + (c + 1) / 4 := by
  simp only [yearStart]; omega

theorem eraYear_spec {x : Int} (h0 : 0 ≤ x) (h1 : x < 146097) :
    0 ≤ eraYear x ∧ eraYear x ≤ 399 ∧ yearStart (eraYear x) ≤ x ∧ x < yearStart (eraYear x + 1) := by
  simp only [eraYear]
  generalize hc : min (x / 36524) 3 = c
  have hc' : 0 ≤ c ∧ c ≤ 3 ∧ 36524 * c ≤ x ∧ (c < 3 → x < 36524 * (c + 1)) := by omega
  generalize hq : (x - 36524 * c) / 1461 = q
  have hq' : 0 ≤ q ∧ q ≤ 24 ∧ 1461 * q ≤ x - 36524 * c ∧ x - 36524 * c < 1461 * (q + 1) := by omega
  have hq24 : q = 24 → c < 3 → x - 36524 * c - 1461 * q < 1460 := by omega
  generalize hk : min ((x - 36524 * c - 1461 * q) / 365) 3 = k
  have hk' : 0 ≤ k ∧ k ≤ 3 ∧ 365 * k ≤ x - 36524 * c - 1461 * q ∧
      (k < 3 → x - 36524 * c - 1461 * q < 365 * (k + 1)) := by omega
  have h := yearStart_cqk ⟨hc'.1, hc'.2.1⟩ ⟨hq'.1, hq'.2.1⟩ ⟨hk'.1, hk'.2.1⟩
  refine ⟨by omega, by omega, by omega, ?_⟩
  rcases Int.lt_or_le k 3 with hk3 | hk3
  · have := yearStart_cqk ⟨hc'.1, hc'.2.1⟩ ⟨hq'.1, hq'.2.1⟩ (k := k + 1) ⟨by omega, by omega⟩
    rw [show 100 * c + 4 * q + k + 1 = 100 * c + 4 * q + (k + 1) by omega, this]; omega
  rcases Int.lt_or_le q 24 with hq24' | hq24'
  · have := yearStart_cqk ⟨hc'.1, hc'.2.1⟩ (q := q + 1) ⟨by omega, by omega⟩ (k := 0) ⟨by omega, by omega⟩
    rw [show 100 * c + 4 * q + k + 1 = 100 * c + 4 * (q + 1) + 0 by omega, this]; omega
  · have := yearStart_century c
    rw [show 100 * c + 4 * q + k + 1 = 100 * (c + 1) by omega, this]
    rcases Int.lt_or_le c 3 with hc3 | hc3
    · have := hc'.2.2.2 hc3; omega
    · omega

theorem yearStart_era (e y : Int) :
    yearStart (400 * e + y) = 146097 * e + yearStart y := by
  simp only [yearStart]; omega

theorem yearLen (y : Int) :
    365 ≤ yearStart (y + 1) - yearStart y ∧ yearStart (y + 1) - yearStart y ≤ 366 := by
  simp only [yearStart]; omega

theorem month_spec {t : Int} (h0 : 0 ≤ t) (h1 : t ≤ 365) :
    0 ≤ (5 * t + 2) / 153 ∧ (5 * t + 2) / 153 ≤ 11 ∧ monthOff ((5 * t + 2) / 153) ≤ t ∧
    ((5 * t + 2) / 153 < 11 → t < monthOff ((5 * t + 2) / 153 + 1)) := by
  simp only [monthOff]; omega

theorem shiftedYear_spec (d : Int) :
    yearStart (shiftedYear d) ≤ d + 719468 ∧ d + 719468 < yearStart (shiftedYear d + 1) := by
  have hx := eraYear_spec (x := (d + 719468) % 146097) (by omega) (by omega)
  have h1 := yearStart_era ((d + 719468) / 146097) (eraYear ((d + 719468) % 146097))
  have h2 := yearStart_era ((d + 719468) / 146097) (eraYear ((d + 719468) % 146097) + 1)
  simp only [shiftedYear]
  rw [h1, show 400 * ((d + 719468) / 146097) + eraYear ((d + 719468) % 146097) + 1 =
    400 * ((d + 719468) / 146097) + (eraYear ((d + 719468) % 146097) + 1) by omega, h2]
  omega

theorem dayInYear_range (d : Int) : 0 ≤ dayInYear d ∧ dayInYear d ≤ 365 := by
  have := shiftedYear_spec d
  have := yearLen (shiftedYear d)
  simp only [dayInYear]; omega

/-- Day `d` lies in month `monthIndex d`. -/
theorem monthIndex_spec (d : Int) :
    monthStart (monthIndex d) ≤ d ∧ d < monthStart (monthIndex d + 1) := by
  have hy := shiftedYear_spec d
  have hm := month_spec (dayInYear_range d).1 (dayInYear_range d).2
  simp only [monthIndex, monthStart, dayInYear] at *
  generalize shiftedYear d = y at *
  generalize hmd : (5 * (d + 719468 - yearStart y) + 2) / 153 = m at *
  rw [show 12 * y + m + 2 - 2 = 12 * y + m by omega, show (12 * y + m) / 12 = y by omega,
    show (12 * y + m) % 12 = m by omega]
  refine ⟨by omega, ?_⟩
  rcases Int.lt_or_le m 11 with h11 | h11
  · rw [show 12 * y + m + 2 + 1 - 2 = 12 * y + (m + 1) by omega,
      show (12 * y + (m + 1)) / 12 = y by omega, show (12 * y + (m + 1)) % 12 = m + 1 by omega]
    have := hm.2.2.2 h11; omega
  · rw [show 12 * y + m + 2 + 1 - 2 = 12 * (y + 1) + 0 by omega,
      show (12 * (y + 1) + 0) / 12 = y + 1 by omega, show (12 * (y + 1) + 0) % 12 = 0 by omega]
    simp only [monthOff]; omega

/-- Months are 28 to 31 days long. -/
theorem monthStart_step (i : Int) :
    monthStart i + 28 ≤ monthStart (i + 1) ∧ monthStart (i + 1) ≤ monthStart i + 31 := by
  simp only [monthStart]
  rw [show i + 1 - 2 = i - 2 + 1 by omega]
  generalize i - 2 = j
  have hl := yearLen (j / 12)
  rcases Int.lt_or_le (j % 12) 11 with h | h
  · rw [show (j + 1) / 12 = j / 12 by omega, show (j + 1) % 12 = j % 12 + 1 by omega]
    simp only [monthOff]; omega
  · rw [show (j + 1) / 12 = j / 12 + 1 by omega, show (j + 1) % 12 = 0 by omega,
      show j % 12 = 11 by omega]
    simp only [monthOff]; omega

theorem mono_of_step {f : Int → Int} (h : ∀ x, f x ≤ f (x + 1)) {x y : Int} (hxy : x ≤ y) :
    f x ≤ f y := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, y = x + n := ⟨(y - x).toNat, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    have := h (x + n)
    rw [show x + ((n + 1 : Nat) : Int) = x + n + 1 by omega]
    exact Int.le_trans (ih (by omega)) this

theorem monthStart_mono {i j : Int} (h : i ≤ j) : monthStart i ≤ monthStart j :=
  mono_of_step (fun i => by have := monthStart_step i; omega) h

theorem monthIndex_mono {d e : Int} (h : d ≤ e) : monthIndex d ≤ monthIndex e := by
  have hd := monthIndex_spec d
  have he := monthIndex_spec e
  apply Int.not_lt.mp
  intro hlt
  have := monthStart_mono (show monthIndex e + 1 ≤ monthIndex d by omega)
  omega

/-- A year is 365 or 366 days. -/
theorem yearSpan (k : Int) :
    monthStart (12 * k) + 365 ≤ monthStart (12 * (k + 1)) ∧
      monthStart (12 * (k + 1)) ≤ monthStart (12 * k) + 366 := by
  simp only [monthStart]
  rw [show 12 * k - 2 = 12 * (k - 1) + 10 by omega, show 12 * (k + 1) - 2 = 12 * (k - 1 + 1) + 10 by omega,
    show (12 * (k - 1) + 10) / 12 = k - 1 by omega, show (12 * (k - 1) + 10) % 12 = 10 by omega,
    show (12 * (k - 1 + 1) + 10) / 12 = k - 1 + 1 by omega, show (12 * (k - 1 + 1) + 10) % 12 = 10 by omega]
  have := yearLen (k - 1); omega

/-! ## Parts of a date -/

inductive DatePart where
  | year | quarter | month | week | day | hour | minute | second | millisecond | microsecond
  | dow | doy
  deriving Repr, DecidableEq

def DatePart.all : List DatePart :=
  [.year, .quarter, .month, .week, .day, .hour, .minute, .second, .millisecond, .microsecond,
   .dow, .doy]

def DatePart.name : DatePart → String
  | .year => "year" | .quarter => "quarter" | .month => "month" | .week => "week"
  | .day => "day" | .hour => "hour" | .minute => "minute" | .second => "second"
  | .millisecond => "millisecond" | .microsecond => "microsecond" | .dow => "dow" | .doy => "doy"

def DatePart.ofName? (s : String) : Option DatePart := DatePart.all.find? (·.name == s.toLower)

def days (ts : Int) : Int := ts / usPerDay

def dayOfYear (d : Int) : Int := d - monthStart (monthIndex d / 12 * 12) + 1

/-- ISO week: the week (from Monday) of the year its Thursday is in. -/
def isoWeek (d : Int) : Int := (dayOfYear (d - (d + 3) % 7 + 3) - 1) / 7 + 1

def partOf : DatePart → Int → Int
  | .year, ts => monthIndex (days ts) / 12
  | .quarter, ts => monthIndex (days ts) % 12 / 3 + 1
  | .month, ts => monthIndex (days ts) % 12 + 1
  | .week, ts => isoWeek (days ts)
  | .day, ts => days ts - monthStart (monthIndex (days ts)) + 1
  | .hour, ts => ts % usPerDay / 3_600_000_000
  | .minute, ts => ts % 3_600_000_000 / 60_000_000
  | .second, ts => ts % 60_000_000 / 1_000_000
  | .millisecond, ts => ts % 60_000_000 / 1000
  | .microsecond, ts => ts % 60_000_000
  -- 1970-01-01 is a Thursday; Sunday is 0.
  | .dow, ts => (days ts + 4) % 7
  | .doy, ts => dayOfYear (days ts)

/-- The timestamps `chrono` represents: -262143-01-01 to 262142-12-31. -/
def partMin : Int := -8334601228800000000
def partMax : Int := 8210266876799999999

def datePart (p : DatePart) (ts : Int) : Option Int :=
  if partMin ≤ ts ∧ ts ≤ partMax then some (partOf p ts) else none

/-- The range of each part but the year. -/
def DatePart.range : DatePart → Option (Int × Int)
  | .year => none
  | .quarter => some (1, 4)
  | .month => some (1, 12)
  | .week => some (1, 53)
  | .day => some (1, 31)
  | .hour => some (0, 23)
  | .minute | .second => some (0, 59)
  | .millisecond => some (0, 59999)
  | .microsecond => some (0, 59999999)
  | .dow => some (0, 6)
  | .doy => some (1, 366)

theorem dayOfYear_range (d : Int) : 1 ≤ dayOfYear d ∧ dayOfYear d ≤ 366 := by
  have hs := monthIndex_spec d
  have h1 := monthStart_mono (show monthIndex d / 12 * 12 ≤ monthIndex d by omega)
  have h2 := monthStart_mono (show monthIndex d + 1 ≤ 12 * (monthIndex d / 12 + 1) by omega)
  have hy := yearSpan (monthIndex d / 12)
  simp only [dayOfYear]
  rw [show monthIndex d / 12 * 12 = 12 * (monthIndex d / 12) by omega]
  rw [show monthIndex d / 12 * 12 = 12 * (monthIndex d / 12) by omega] at h1
  omega

theorem partOf_range {p : DatePart} {lo hi : Int} (hp : p.range = some (lo, hi)) (ts : Int) :
    lo ≤ partOf p ts ∧ partOf p ts ≤ hi := by
  cases p <;> simp only [DatePart.range, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp <;>
    obtain ⟨rfl, rfl⟩ := hp <;> simp only [partOf, usPerDay]
  case week => have := dayOfYear_range (days ts - (days ts + 3) % 7 + 3); simp only [isoWeek]; omega
  case day =>
    have := monthIndex_spec (days ts)
    have := monthStart_step (monthIndex (days ts))
    omega
  case doy => exact dayOfYear_range _
  all_goals omega

theorem days_mono {s t : Int} (h : s ≤ t) : days s ≤ days t := Int.ediv_le_ediv (by decide) h

theorem year_mono {s t : Int} (h : s ≤ t) : partOf .year s ≤ partOf .year t :=
  Int.ediv_le_ediv (by decide) (monthIndex_mono (days_mono h))

/-! ## Truncation -/

inductive TimeUnit where
  | microsecond | millisecond | second | minute | hour | day | week | month | quarter | year
  deriving Repr, DecidableEq

def TimeUnit.all : List TimeUnit :=
  [.microsecond, .millisecond, .second, .minute, .hour, .day, .week, .month, .quarter, .year]

def TimeUnit.name : TimeUnit → String
  | .microsecond => "microsecond" | .millisecond => "millisecond" | .second => "second"
  | .minute => "minute" | .hour => "hour" | .day => "day" | .week => "week" | .month => "month"
  | .quarter => "quarter" | .year => "year"

def TimeUnit.ofName? (s : String) : Option TimeUnit := TimeUnit.all.find? (·.name == s.toLower)

/-- Units DataFusion truncates to in nanoseconds. -/
def TimeUnit.calendar : TimeUnit → Bool
  | .week | .month | .quarter | .year => true
  | _ => false

def floorTo (k ts : Int) : Int := ts / k * k

def trunc : TimeUnit → Int → Int
  | .microsecond, ts => ts
  | .millisecond, ts => floorTo 1000 ts
  | .second, ts => floorTo 1_000_000 ts
  | .minute, ts => floorTo 60_000_000 ts
  | .hour, ts => floorTo 3_600_000_000 ts
  | .day, ts => floorTo usPerDay ts
  -- Monday is 3 days before 1970-01-01.
  | .week, ts => (days ts - (days ts + 3) % 7) * usPerDay
  | .month, ts => monthStart (monthIndex (days ts)) * usPerDay
  | .quarter, ts => monthStart (monthIndex (days ts) / 3 * 3) * usPerDay
  | .year, ts => monthStart (monthIndex (days ts) / 12 * 12) * usPerDay

/-- Calendar truncation is exact for timestamps from here … -/
def nsMin : Int := -9223372036854775
/-- … to here. -/
def nsMax : Int := 9223372036854775

theorem floorTo_mono {k s t : Int} (hk : 0 < k) (h : s ≤ t) : floorTo k s ≤ floorTo k t :=
  Int.mul_le_mul_of_nonneg_right (Int.ediv_le_ediv hk h) (Int.le_of_lt hk)

theorem trunc_mono (u : TimeUnit) {s t : Int} (h : s ≤ t) : trunc u s ≤ trunc u t := by
  have hd := days_mono h
  have hm := monthIndex_mono hd
  have hu : (0 : Int) ≤ usPerDay := by decide
  cases u <;> simp only [trunc]
  case microsecond => exact h
  case millisecond | second | minute | hour | day => exact floorTo_mono (by decide) h
  case week =>
    apply Int.mul_le_mul_of_nonneg_right _ hu
    exact mono_of_step (f := fun d => d - (d + 3) % 7) (fun x => by omega) hd
  case month => exact Int.mul_le_mul_of_nonneg_right (monthStart_mono hm) hu
  case quarter => exact Int.mul_le_mul_of_nonneg_right (monthStart_mono (by omega)) hu
  case year => exact Int.mul_le_mul_of_nonneg_right (monthStart_mono (by omega)) hu

/-! ## Dates

A DATE is the number of days since 1970-01-01. DataFusion computes date
arithmetic with `chrono`, which fails (panics) outside the years it
represents; `date_trunc` of a DATE goes through nanoseconds, like the
calendar truncations above. -/

/-- The days `chrono` represents: -262143-01-01 (`partMin`) to 262142-12-31
(`partMax`). -/
def dayMin : Int := -96465292
def dayMax : Int := 95026236

/-- The days whose midnight is within DataFusion's nanosecond range. -/
def nsDayMin : Int := -106751
def nsDayMax : Int := 106751

/-- `date_part(p, d)` of a date: the part of its midnight (`NULL` outside
the dates `chrono` represents, as for timestamps). -/
def datePartDay (p : DatePart) (d : Int) : Option Int := datePart p (d * usPerDay)

/-- `date_trunc(u, d)` of a date, as a date. -/
def truncDay (u : TimeUnit) (d : Int) : Int := days (trunc u (d * usPerDay))

/-- Adding `m` months to day `d`: the same day of month `monthIndex d + m`,
or that month's last day if it is shorter (2024-01-31 + 1 month is
2024-02-29), as DataFusion, DuckDB and Polars do. -/
def addMonths (m d : Int) : Int :=
  min (monthStart (monthIndex d + m) + (d - monthStart (monthIndex d)))
    (monthStart (monthIndex d + m + 1) - 1)

/-- Adding `m` months to a timestamp: to its day, keeping the time of day. -/
def addMonthsUs (m ts : Int) : Int := addMonths m (days ts) * usPerDay + ts % usPerDay

/-- Day `x` of month `j` (between its first day and the next month's) is in
month `j`. -/
theorem monthIndex_eq {j x : Int} (h₁ : monthStart j ≤ x) (h₂ : x < monthStart (j + 1)) :
    monthIndex x = j := by
  have hs := monthIndex_spec x
  rcases Int.lt_trichotomy (monthIndex x) j with hlt | heq | hgt
  · have := monthStart_mono (show monthIndex x + 1 ≤ j by omega); omega
  · exact heq
  · have := monthStart_mono (show j + 1 ≤ monthIndex x by omega); omega

/-- Adding `m` months lands in the month `m` months later … -/
theorem addMonths_month (m d : Int) : monthIndex (addMonths m d) = monthIndex d + m := by
  have hs := monthIndex_spec d
  have hstep := monthStart_step (monthIndex d + m)
  apply monthIndex_eq <;> simp only [addMonths] <;> omega

/-- … on the same day of the month, unless that month is shorter: then on its
last day. -/
theorem addMonths_day (m d : Int) :
    addMonths m d - monthStart (monthIndex d + m) =
      min (d - monthStart (monthIndex d)) (monthStart (monthIndex d + m + 1) - 1 - monthStart (monthIndex d + m)) := by
  simp only [addMonths]; omega

theorem addMonths_mono (m : Int) {d e : Int} (h : d ≤ e) : addMonths m d ≤ addMonths m e := by
  have hd := monthIndex_spec d
  have he := monthIndex_spec e
  have hi := monthIndex_mono h
  have hstep := monthStart_step (monthIndex e + m)
  simp only [addMonths]
  rcases Int.lt_or_eq_of_le hi with hlt | heq
  · have := monthStart_mono (show monthIndex d + m + 1 ≤ monthIndex e + m by omega)
    omega
  · rw [heq]; omega

theorem truncDay_mono (u : TimeUnit) {d e : Int} (h : d ≤ e) : truncDay u d ≤ truncDay u e :=
  days_mono (trunc_mono u (Int.mul_le_mul_of_nonneg_right h (by decide)))

#guard addMonths 1 19753 == 19782 && addMonths 1 19782 == 19811 && addMonths (-1) 19813 == 19782
#guard addMonths 12 19782 == 20147 && addMonths (-13) 19813 == 19416
#guard addMonthsUs 1 (19753 * usPerDay + 36000000000) == 19782 * usPerDay + 36000000000
#guard addMonthsUs 1 (-1) == 2678400000000 - 1
#guard [DatePart.year, .month, .day, .dow].map (datePartDay · 19782) == [some 2024, some 2, some 29, some 4]
#guard datePartDay .year dayMax == some 262142 && datePartDay .year (dayMax + 1) == none
#guard datePartDay .year dayMin == some (-262143) && datePartDay .year (dayMin - 1) == none
#guard [TimeUnit.day, .week, .month, .quarter, .year].map (truncDay · 19782) == [19782, 19779, 19754, 19723, 19723]

/-! ## Formatting (`strftime`, chrono's)

The directives chrono formats the same way as DuckDB, Polars and the other
engines: `%Y` (the year, padded to four digits, with a sign outside 0 to
9999), `%m`, `%d`, `%H`, `%M`, `%S`, `%j` (day of the year), `%F`
(`%Y-%m-%d`), `%T` (`%H:%M:%S`) and `%%`. -/

/-- `x ≥ 0` in decimal, padded with zeros to `n` digits. -/
def pad (n : Nat) (x : Int) : String :=
  let s := toString x.toNat
  String.ofList (List.replicate (n - s.length) '0') ++ s

def yearText (y : Int) : String :=
  if 0 ≤ y ∧ y ≤ 9999 then pad 4 y else if 9999 < y then "+" ++ toString y else "-" ++ pad 4 (-y)

/-- A piece of a format: text, or a directive (its letter). -/
inductive FmtPiece where
  | text (c : Char)
  | dir (c : Char)
  deriving Repr, DecidableEq

def fmtDirectives : List Char := ['Y', 'm', 'd', 'H', 'M', 'S', 'j', 'F', 'T', '%']

/-- The pieces of a format string, or `none` if it has a directive outside
`fmtDirectives` (or ends in `%`). -/
def parseFormat : List Char → Option (List FmtPiece)
  | [] => some []
  | '%' :: c :: rest =>
    if fmtDirectives.contains c then (parseFormat rest).map (.dir c :: ·) else none
  | ['%'] => none
  | c :: rest => (parseFormat rest).map (.text c :: ·)

def FmtPiece.render (ts : Int) : FmtPiece → String
  | .text c => c.toString
  | .dir 'Y' => yearText (partOf .year ts)
  | .dir 'm' => pad 2 (partOf .month ts)
  | .dir 'd' => pad 2 (partOf .day ts)
  | .dir 'H' => pad 2 (partOf .hour ts)
  | .dir 'M' => pad 2 (partOf .minute ts)
  | .dir 'S' => pad 2 (partOf .second ts)
  | .dir 'j' => pad 3 (partOf .doy ts)
  | .dir 'F' => yearText (partOf .year ts) ++ "-" ++ pad 2 (partOf .month ts) ++ "-" ++ pad 2 (partOf .day ts)
  | .dir 'T' => pad 2 (partOf .hour ts) ++ ":" ++ pad 2 (partOf .minute ts) ++ ":" ++ pad 2 (partOf .second ts)
  | .dir _ => "%"

/-- `strftime(ts, fmt)` for a format `parseFormat` accepts. -/
def strftime (fmt : String) (ts : Int) : String :=
  String.join (((parseFormat fmt.toList).getD []).map (·.render ts))

/-- The time of day of a timestamp (`CAST(ts AS TIME)`), in microseconds. -/
def timeOfDay (ts : Int) : Int := ts % usPerDay

theorem timeOfDay_range (ts : Int) : 0 ≤ timeOfDay ts ∧ timeOfDay ts < usPerDay := by
  simp only [timeOfDay, usPerDay]; omega

#guard strftime "%Y-%m-%d %H:%M:%S" 1700000000123456 == "2023-11-14 22:13:20"
#guard strftime "%Y-%m-%d %H:%M:%S" (-62135596800000001) == "0000-12-31 23:59:59"
#guard strftime "%F %T" 253402300800000000 == "+10000-01-01 00:00:00"
#guard strftime "%Y" partMin == "-262143" && strftime "%j %%" (-1) == "365 %"
#guard (parseFormat "%Y %q".toList).isNone && (parseFormat "50%".toList).isNone
#guard timeOfDay (-1) == usPerDay - 1

/-! ## Buckets

`date_bin(k, ts, origin)` (Ibis's `bucket`, Polars' `group_by_dynamic` without
overlap): the start of the `k`-microsecond bucket, counted from `origin`,
that `ts` falls in. -/

def bucket (k : Nat) (origin ts : Int) : Int := floorTo k (ts - origin) + origin

theorem bucket_mono (k : Nat) (origin : Int) {s t : Int} (h : s ≤ t) :
    bucket k origin s ≤ bucket k origin t := by
  simp only [bucket]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [floorTo]
  · have := floorTo_mono (k := (k : Int)) (by omega) (show s - origin ≤ t - origin by omega)
    omega

#guard bucket 900000000 0 (-1) == -900000000 && bucket 900000000 300000000 0 == -600000000
#guard bucket 900000000 0 899999999 == 0 && bucket 900000000 0 900000000 == 900000000

/-! Values DataFusion gives (`python/tests/test_time.py` checks many more). -/

#guard DatePart.all.map (partOf · 1700000000123456) == [2023, 4, 11, 46, 14, 22, 13, 20, 20123, 20123456, 2, 318]
#guard DatePart.all.map (partOf · (-1)) == [1969, 4, 12, 1, 31, 23, 59, 59, 59999, 59999999, 3, 365]
#guard DatePart.all.map (partOf · (-62135596800000000)) == [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1]
#guard DatePart.all.map (partOf · 951782400000005) == [2000, 1, 2, 9, 29, 0, 0, 0, 0, 5, 2, 60]
#guard datePart .year (partMin - 1) == none && datePart .year partMin == some (-262143)
#guard datePart .year partMax == some 262142 && datePart .year (partMax + 1) == none
#guard TimeUnit.all.map (trunc · 1700000000123456) == [1700000000123456, 1700000000123000,
  1700000000000000, 1699999980000000, 1699999200000000, 1699920000000000, 1699833600000000,
  1698796800000000, 1696118400000000, 1672531200000000]
#guard trunc .week 0 == -259200000000 && trunc .year (-1) == -31536000000000

end Substrait.Time
