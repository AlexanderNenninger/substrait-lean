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
