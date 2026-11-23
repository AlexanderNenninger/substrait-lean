import Sverify.Core.CaseTable
import Sverify.Core.Regex
import Sverify.Core.Digest

/-!
# String functions

String functions on Unicode scalar values (Lean's `Char`), checked by
`python/tests/test_text.py`: `substring`, `strpos` and the trims against
a SQL engine, and `LIKE` with a backslash escape, `repeat`, `reverse`, `replace`,
`ascii` and `levenshtein`, whose meaning follows Rust's strings:

* `substring(s FROM a FOR n)` keeps the characters at 1-based positions
  `a … a+n-1` that exist; without `FOR`, all from `a` on. (A negative `n`
  fails; the parser only accepts constant `n ≥ 0`.)
* `strpos(s, t)` is the 1-based position of the first `t` in `s`, `0` if none
  (and `1` for the empty `t`).
* `LIKE` matches `%` (any characters) and `_` (one character); a backslash
  makes the next character literal, and a trailing backslash is itself.
* `btrim`/`ltrim`/`rtrim` remove characters of a set from the ends.
* `repeat(s, n)` is `s` `n` times (`''` for `n ≤ 0`); a result of more than
  `2³¹ - 1` bytes fails (`Text.repeatFits`), as Arrow's `Utf8` offsets are
  32-bit (`Utf8View` input too).
* `reverse(s)` reverses the characters (combining marks move with them).
* `replace(s, p, r)` replaces every non-overlapping `p`, from the left, by `r`
  (Rust's `str::replace`); an empty `p` matches nowhere, so the result is `s`
  (D44).
* `ascii(s)` is the code point of the first character, `0` for `''`.
* `levenshtein(s, t)` counts single-character insertions, deletions and
  substitutions.

`translate` is not modelled: engines differ on whether it works on grapheme
clusters or on characters.

`UPPER`, `LOWER`, `ILIKE`, regular expressions and the digests `md5` and
`sha256` are black boxes: `opaque` functions, so no proof depends on what
they compute, only on their types (and that they are functions, so equal
inputs give equal outputs). Their meaning is Rust's (`str::to_uppercase`, the
`regex` crate); the SQL translations refuse
at run time what their engines compute differently (#70). `ILIKE` folds case
with Unicode's simple case folding (the `regex` crate's `(?i)`, so
`'É' ILIKE 'é'` but not `'ß' ILIKE 'SS'`). Lean's evaluator maps ASCII case
only, and evaluates regular expressions with RE2's meaning
(`core/Sverify/Core/Regex.lean`) where it agrees with Rust's: elsewhere it
panics, and `substrait-check` then refuses to print rows rather than print
wrong ones. The table of black boxes, `core/Sverify/Core/BlackBox.lean` (#325),
generalises these: a function declared by one row.
-/

namespace Substrait.Text

/-- The characters at 1-based positions `a … a+n-1` that exist (Substrait's
`negative_start` = `LEFT_OF_BEGINNING`: a start below 1 is left of the first
character). -/
def substr (s : String) (a : Int) (n : Option Nat) : String :=
  let cs := s.toList
  let lo := (a - 1).toNat
  let hi := match n with
    | some n => (a - 1 + n).toNat
    | none => cs.length
  String.ofList ((cs.drop lo).take (hi - lo))

/-- `substring` with `negative_start` = `WRAP_FROM_END`, the reference's
choice when the plan omits it (#209): a negative start counts from the end,
`-1` being the last character, so `substring('hello', -2, 2) = 'lo'`. A start
that wraps to before the first character, and a start of 0, are left of the
beginning. -/
def substrWrap (s : String) (a : Int) (n : Option Nat) : String :=
  substr s (if a < 0 then a + s.length + 1 else a) n

#guard substrWrap "hello" (-2) (some 2) == "lo" && substrWrap "hello" (-2) none == "lo"
#guard substrWrap "hello" (-10) (some 7) == "he" && substrWrap "hello" 0 (some 2) == "h"
#guard substrWrap "hello" (-6) (some 2) == "h" && substrWrap "hello" (-5) (some 1) == "h"
#guard substrWrap "hello" 2 (some 3) == substr "hello" 2 (some 3)

def findFrom (t : List Char) : List Char → Nat → Option Nat
  | cs, i =>
    if t.isPrefixOf cs then some i
    else match cs with
      | [] => none
      | _ :: r => findFrom t r (i + 1)

/-! ### A linear search (#2497)

`findFrom` tests `isPrefixOf` at every position: up to `n · m` comparisons
for a needle of `m` characters in `n`, which took DuckDB's long
almost-matching needle test past the replay's watchdog. `findFromFast` keeps a
hash of the `m` characters at the current position, rolled forward one
character at a time, and tests `isPrefixOf` only where it equals the needle's
hash. A window equal to the needle has the needle's hash, so this skips only
positions that cannot match: the result is `findFrom`'s
(`findFrom_eq_fast`), and the compiled checker runs it (`findFrom_csimp`).
The search is linear in `n + m` plus the cost of the positions whose hashes
collide. -/

namespace Find

/-- The hash's modulus and base. A hash stays below `2³¹` and a product below
`2⁶²`, a scalar at run time. -/
def P : Int := 2147483647
def B : Int := 1000003

/-- A character's digit. -/
def dig (c : Char) : Int := c.toNat

/-- The exact polynomial of a list, `Σ dig cₖ · B^(m-1-k)`, for proofs. -/
def poly (l : List Char) : Int := l.foldl (fun h c => h * B + dig c) 0

/-- The polynomial modulo `P`, as the checker computes it. -/
def hashOf (l : List Char) : Int := l.foldl (fun h c => (h * B + dig c) % P) 0

/-- `B ^ n` modulo `P`. -/
def bPow : Nat → Int
  | 0 => 1 % P
  | n + 1 => bPow n * B % P

theorem mul_add_emod (a c : Int) : (a % P * B + c) % P = (a * B + c) % P := by
  rw [Int.add_emod, Int.mul_emod, Int.emod_emod]
  conv => rhs; rw [Int.add_emod, Int.mul_emod]

theorem foldl_emod (l : List Char) (a : Int) :
    l.foldl (fun h c => (h * B + dig c) % P) (a % P) = l.foldl (fun h c => h * B + dig c) a % P := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih => simp only [List.foldl_cons]; rw [mul_add_emod, ← ih]

theorem hashOf_eq (l : List Char) : hashOf l = poly l % P := by
  have := foldl_emod l 0
  simpa [hashOf, poly] using this

theorem bPow_eq : ∀ n, bPow n = B ^ n % P
  | 0 => rfl
  | n + 1 => by
    have := mul_add_emod (B ^ n) 0
    simp only [Int.add_zero] at this
    rw [bPow, bPow_eq n, this, Int.pow_succ]

theorem foldl_poly (l : List Char) (a : Int) :
    l.foldl (fun h c => h * B + dig c) a = a * B ^ l.length + poly l := by
  induction l generalizing a with
  | nil => simp [poly]
  | cons c l ih =>
    simp only [List.foldl_cons, poly, List.length_cons]
    rw [ih, ih (0 * B + dig c), Int.pow_succ]
    simp only [Int.zero_mul, Int.zero_add, Int.add_mul, Int.mul_assoc, Int.mul_comm B]
    omega

theorem poly_cons (c : Char) (l : List Char) : poly (c :: l) = dig c * B ^ l.length + poly l := by
  have := foldl_poly l (0 * B + dig c)
  simp only [Int.zero_mul, Int.zero_add] at this
  simpa [poly] using this

theorem poly_snoc (l : List Char) (c : Char) : poly (l ++ [c]) = poly l * B + dig c := by
  simp [poly, List.foldl_append]

/-- The rolled hash: the window `x :: u` moves on to `u ++ [y]`. -/
theorem roll {x y : Char} {u : List Char} {r : Int} (hr : r = poly (x :: u) % P) :
    ((r - dig x * bPow u.length) * B + dig y) % P = poly (u ++ [y]) % P := by
  rw [poly_snoc, bPow_eq, hr]
  have e : poly u = poly (x :: u) - dig x * B ^ u.length := by rw [poly_cons]; omega
  rw [e, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.mul_emod (dig x), Int.emod_emod, Int.emod_emod]
  conv => rhs; rw [Int.add_emod, Int.mul_emod, Int.sub_emod, Int.mul_emod (dig x)]

/-- The search from position `i` of `front`, whose first `m` characters hash
to `r`; `back` is `front` without them, `ht` the needle's hash and `bm`
`B ^ (m - 1)` modulo `P`. -/
def scan (t : List Char) (ht bm : Int) : List Char → List Char → Nat → Int → Option Nat
  | front, back, i, r =>
    if r == ht && t.isPrefixOf front then some i
    else match back, front with
      | y :: back', x :: front' => scan t ht bm front' back' (i + 1) (((r - dig x * bm) * B + dig y) % P)
      | _, _ => none
termination_by _ back => back.length

theorem findFrom_short (t : List Char) : ∀ (cs : List Char) (i : Nat), cs.length < t.length →
    findFrom t cs i = none
  | cs, i, h => by
    have hp : t.isPrefixOf cs = false := by
      rw [Bool.eq_false_iff]; intro hp
      have := (List.isPrefixOf_iff_prefix.mp hp).length_le; omega
    unfold findFrom
    rw [hp]
    cases cs with
    | nil => rfl
    | cons c cs => exact findFrom_short t cs (i + 1) (by simp at h; omega)

theorem prefix_eq {t w back : List Char} (hw : w.length = t.length)
    (hp : t.isPrefixOf (w ++ back) = true) : t = w :=
  (List.prefix_of_prefix_length_le (List.isPrefixOf_iff_prefix.mp hp) (List.prefix_append w back)
    (by omega)).eq_of_length (by omega)

theorem scan_eq {t : List Char} (ht0 : t ≠ []) :
    ∀ (front back w : List Char) (i : Nat) (r : Int), front = w ++ back → w.length = t.length →
      r = poly w % P →
      scan t (poly t % P) (bPow (t.length - 1)) front back i r = findFrom t front i
  | front, back, w, i, r, hf, hw, hr => by
    unfold scan findFrom
    by_cases hp : t.isPrefixOf front = true
    · have e := prefix_eq hw (hf ▸ hp)
      subst e
      simp [hr, hp]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.and_false, Bool.false_eq_true, ite_false]
      obtain ⟨x, u, rfl⟩ : ∃ x u, w = x :: u := by
        cases w with
        | nil => exact absurd (List.length_eq_zero_iff.mp hw.symm) ht0
        | cons x u => exact ⟨x, u, rfl⟩
      subst hf
      simp only [List.cons_append]
      have hu1 : u.length + 1 = t.length := by simpa using hw
      have hu : u.length = t.length - 1 := by omega
      cases back with
      | nil =>
        simp only [List.append_nil]
        exact (findFrom_short t u (i + 1) (by omega)).symm
      | cons y back' =>
        simp only
        have hroll := roll (y := y) hr
        rw [hu] at hroll
        exact scan_eq ht0 (u ++ y :: back') back' (u ++ [y]) (i + 1) _ (by simp)
          (by simp; omega) hroll
termination_by _ back => back.length

/-- `findFrom`, by a rolling hash. -/
def findFromFast (t cs : List Char) (i : Nat) : Option Nat :=
  if t.isEmpty then some i
  else scan t (hashOf t) (bPow (t.length - 1)) cs (cs.drop t.length) i (hashOf (cs.take t.length))

theorem findFrom_eq_fast (t cs : List Char) (i : Nat) : findFrom t cs i = findFromFast t cs i := by
  unfold findFromFast
  by_cases ht : t.isEmpty = true
  · rw [List.isEmpty_iff.mp ht]; unfold findFrom; simp
  · have ht0 : t ≠ [] := fun e => ht (List.isEmpty_iff.mpr e)
    simp only [ht, Bool.false_eq_true, ite_false, hashOf_eq]
    by_cases hl : t.length ≤ cs.length
    · exact (scan_eq ht0 cs _ _ i _ (List.take_append_drop _ _).symm (by simp; omega) rfl).symm
    · have hd : cs.drop t.length = [] := List.drop_eq_nil_of_le (by omega)
      rw [hd, findFrom_short t cs i (by omega)]
      unfold scan
      have hp : t.isPrefixOf cs = false := by
        rw [Bool.eq_false_iff]; intro hp
        have := (List.isPrefixOf_iff_prefix.mp hp).length_le; omega
      simp [hp]

end Find

@[csimp] theorem findFrom_csimp : @findFrom = @Find.findFromFast := by
  funext t cs i; exact Find.findFrom_eq_fast t cs i

#guard Find.findFromFast "lo".toList "hello".toList 1 == some 4
#guard Find.findFromFast "".toList "ab".toList 1 == some 1
#guard Find.findFromFast "abc".toList "ab".toList 1 == none
#guard Find.findFromFast "ab".toList "aab".toList 1 == some 2

/-- **The size hypothesis for strings** (trusted, #202, #336): every string
has fewer than `2³²` characters, a bound of the reference's that the engines'
strings stay within (duckdb-exec-size-limits). So a length or
position never reaches `sizeCap`, and capping it there changes nothing; it
gives the range analysis an upper bound, so that `strpos(s, t) - 1` is proved
not to overflow. (Relations keep their own bound, `rowCap`.) -/
def sizeCap : Int := 2 ^ 32

/-- **The size hypothesis for relations** (trusted, #202): a relation a window
reads has fewer than `2⁶²` rows (`Rel.Small`), so `ROW_NUMBER` and the ranks
stay below `rowCap`. -/
def rowCap : Int := 2 ^ 62

/-- `substring`'s offsets and lengths stay below `substrMax` in magnitude
(#336): the reference's choice for the option `substring_range` is `ERROR`
for an offset outside `[-2³², 2³²)` or a length of `2³²` or more
(`Issue.domain`), the strings' own bound (`sizeCap`), which duckdb-substring-range
shares; a profile that computes there (`COMPUTE`,
`Profile.substrait`) refines it. -/
def substrMax : Int := 2 ^ 32

/-- Is `substring(s, a, n)` within the range of offsets and lengths? -/
def substrInRange (a : Int) (n : Option Nat) : Bool :=
  decide (-substrMax ≤ a) && decide (a < substrMax) && n.all fun n => decide ((n : Int) < substrMax)

#guard substrInRange (2 ^ 32 - 1) (some (2 ^ 32 - 1)) && substrInRange (-(2 ^ 32)) none
#guard !substrInRange (2 ^ 32) none && !substrInRange (-(2 ^ 32) - 1) none
#guard !substrInRange 1 (some (2 ^ 32))

/-- A length or position, which the size hypothesis keeps below `sizeCap`. -/
def capped (n : Int) : Int := min n sizeCap

theorem capped_le (n : Int) : capped n ≤ sizeCap := Int.min_le_right _ _

theorem capped_nonneg {n : Int} (h : 0 ≤ n) : 0 ≤ capped n := by
  unfold capped sizeCap; omega

def strpos (s t : String) : Int :=
  capped (match findFrom t.toList s.toList 1 with
  | some i => i
  | none => 0)

def startsWith (s t : String) : Bool := t.toList.isPrefixOf s.toList

def endsWith (s t : String) : Bool := t.toList.reverse.isPrefixOf s.toList.reverse

/-! ## `LIKE` -/

inductive Tok where
  | any | one | lit (c : Char)

def tokens : List Char → List Tok
  | [] => []
  | '\\' :: c :: r => .lit c :: tokens r
  | '%' :: r => .any :: tokens r
  | '_' :: r => .one :: tokens r
  | c :: r => .lit c :: tokens r

def matchTokens : List Tok → List Char → Bool
  | [], s => s.isEmpty
  | .any :: p, s => (List.range (s.length + 1)).any fun k => matchTokens p (s.drop k)
  | .one :: p, s => match s with
    | _ :: s => matchTokens p s
    | [] => false
  | .lit c :: p, s => match s with
    | d :: s => c == d && matchTokens p s
    | [] => false

def like (s p : String) : Bool := matchTokens (tokens p.toList) s.toList

/-! ## Trimming -/

def trimLeft (cs : List Char) (set : List Char) : List Char := cs.dropWhile set.contains

/-- Trim characters of `set` from the start (`left`) and/or the end (`right`). -/
def trim (left right : Bool) (s set : String) : String :=
  let cs := s.toList
  let cs := if left then trimLeft cs set.toList else cs
  let cs := if right then (trimLeft cs.reverse set.toList).reverse else cs
  String.ofList cs

/-! ## Repeating, reversing, replacing -/

/-- The longest string `repeat` writes, in bytes; past it, `repeat` raises.
It lies at or below every engine's own limit on a string's length
(`duckdb-exec-size-limits`, `polars-exec-size-limits`,
`spark-exec-size-limits`), so every route raises at the writers' guard before
an engine fails on its own, and the bound also caps what the checker's
evaluator writes (#1074; ruling 267). -/
def repeatMax : Nat := 2 ^ 31 - 1

/-- Does `repeat(s, n)` fit in `repeatMax` bytes? (`n ≤ 0` gives `''`.) -/
def repeatFits (s : String) (n : Int) : Bool := decide (s.utf8ByteSize * n.toNat ≤ repeatMax)

/-- `s` appended to `acc` `k` times, in place: a loop, with no list of `k`
pieces in between. -/
def repeatOnto (s : String) : Nat → String → String
  | 0, acc => acc
  | k + 1, acc => repeatOnto s k (acc ++ s)

/-- `repeat(s, n)`: `s` `n` times. It writes the result into one string
(`repeatStr_eq` gives the plain form): the plain form's list of `n` pieces
took about 32 bytes a piece, so `repeat(' ', 10⁹)`, a 1 GB result within
`repeatFits`, took over 30 GB of the checker's memory (#1074). The empty string is `""`
whatever `n` is, so it never loops: `repeatFits` holds for it at every `n`, and
`n = 2⁶³ - 1` would spin forever (#2278). -/
def repeatStr (s : String) (n : Int) : String :=
  if s.isEmpty then "" else repeatOnto s n.toNat ""

theorem repeatOnto_eq (s : String) :
    ∀ k acc, repeatOnto s k acc = acc ++ String.join (List.replicate k s)
  | 0, acc => by simp [repeatOnto]
  | k + 1, acc => by
    rw [repeatOnto, repeatOnto_eq s k, List.replicate_succ, String.join_cons, String.append_assoc]

theorem repeatStr_eq (s : String) (n : Int) :
    repeatStr s n = String.join (List.replicate n.toNat s) := by
  by_cases h : s.isEmpty
  · have : s = "" := String.isEmpty_iff.mp h
    subst this
    have hj : ∀ k, String.join (List.replicate k "") = "" := by
      intro k; induction k with
      | zero => simp
      | succ k ih => simp [List.replicate_succ, ih]
    simp [repeatStr, hj]
  · simp [repeatStr, h, repeatOnto_eq]

def reverse (s : String) : String := String.ofList s.toList.reverse

/-- Replace every `p` (not empty) in `cs`, from the left; `fuel` is at least
`cs.length`. -/
def replaceGo (p r : List Char) : Nat → List Char → List Char
  | 0, cs => cs
  | _ + 1, [] => []
  | n + 1, c :: cs =>
    if p.isPrefixOf (c :: cs) then r ++ replaceGo p r n ((c :: cs).drop p.length)
    else c :: replaceGo p r n cs

def replace (s p r : String) : String :=
  let cs := s.toList
  if p.isEmpty then s else String.ofList (replaceGo p.toList r.toList cs.length cs)

def ascii (s : String) : Int :=
  match s.toList with
  | c :: _ => c.toNat
  | [] => 0

/-! ## Edit distance -/

/-- The next row of the edit distance table: `prev` is the row of the
characters before `c`, `left` the entry to the left of the one computed. -/
def levRow (c : Char) : List Char → List Nat → Nat → List Nat
  | b :: bs, p0 :: p1 :: ps, left =>
    let v := min (min (p1 + 1) (left + 1)) (p0 + if c == b then 0 else 1)
    v :: levRow c bs (p1 :: ps) v
  | _, _, _ => []

def levenshtein (s t : String) : Nat :=
  let ts := t.toList
  let step (prev : List Nat) (c : Char) : List Nat :=
    let first := prev.headD 0 + 1
    first :: levRow c ts prev first
  ((s.toList.foldl step (List.range (ts.length + 1))).getLast?).getD 0

/-! ## Black boxes -/

/-- Is every character ASCII? The one definition behind `Issue.nonAscii`
(`UnFn.issue`, `BinFn.issue`) and the evaluator's refusal below. -/
def isAscii (s : String) : Bool := s.toList.all fun c => c.toNat < 128

/-- ASCII without the vertical tab: the text on which RE2's classes and
Rust's agree (`classesDiffer`). -/
def isPlain (s : String) : Bool := isAscii s && !s.toList.contains '\x0b'

/-- The scalar `c` under the mapping `t` of `CaseTable`: its entry, or itself. -/
def mapScalar (t : Array (Nat × Nat)) (c : Char) : Char :=
  match t.binSearch (c.toNat, 0) fun a b => a.1 < b.1 with
  | some (_, v) => Char.ofNat v
  | none => c

/-- The scalars of `UPPER`'s raise set (`CaseTable.upperRaise`): the engines map them
differently (D51). -/
def upperRaises (s : String) : Bool := s.toList.any fun c => CaseTable.upperRaise.contains c.toNat

/-- The scalars of `LOWER`'s raise set (`CaseTable.lowerRaise`). -/
def lowerRaises (s : String) : Bool := s.toList.any fun c => CaseTable.lowerRaise.contains c.toNat

/-- `UPPER`: each scalar's upper case where the tier-1 engines agree on it, one
scalar each (`CaseTable.upperMap`). On a string with a scalar of the raise set
(`upperRaises`) the reference raises, and this value is not used. -/
def upper (s : String) : String := s.map (mapScalar CaseTable.upperMap)

/-- `LOWER`, as `upper` (`CaseTable.lowerMap`, `lowerRaises`). -/
def lower (s : String) : String := s.map (mapScalar CaseTable.lowerMap)

-- The sizes of the raise sets (D51): 157 for `UPPER`, 56 for `LOWER` and U+03A3.
#guard CaseTable.upperRaise.length == 157
#guard CaseTable.lowerRaise.length == 57

set_option maxRecDepth 4096 in
/-- No scalar of either raise set is ASCII, so ASCII text has the engines' value. -/
theorem upperRaises_of_isAscii {s : String} (h : isAscii s = true) : upperRaises s = false := by
  have hs : ∀ x ∈ CaseTable.upperRaise, 128 ≤ x := by decide
  simp only [isAscii, List.all_eq_true, decide_eq_true_eq] at h
  simp only [upperRaises, Bool.eq_false_iff, ne_eq, List.any_eq_true, List.contains_iff_mem, not_exists,
    not_and]
  intro c hc hm
  have := h c hc
  have := hs _ hm
  omega

set_option maxRecDepth 4096 in
theorem lowerRaises_of_isAscii {s : String} (h : isAscii s = true) : lowerRaises s = false := by
  have hs : ∀ x ∈ CaseTable.lowerRaise, 128 ≤ x := by decide
  simp only [isAscii, List.all_eq_true, decide_eq_true_eq] at h
  simp only [lowerRaises, Bool.eq_false_iff, ne_eq, List.any_eq_true, List.contains_iff_mem, not_exists,
    not_and]
  intro c hc hm
  have := h c hc
  have := hs _ hm
  omega

def ilikeAscii (s p : String) : Bool :=
  if isAscii s && isAscii p then like s.toLower p.toLower
  else panic! s!"ILIKE of non-ASCII text is not evaluated in Lean"

/-- `s ILIKE p`: `LIKE` with Unicode's simple case folding. -/
@[implemented_by ilikeAscii] opaque ilike : String → String → Bool

/-- Does the pattern use `\\d`, `\\w`, `\\s`, `\\b` or a complement? -/
def regexClasses : List Char → Bool
  | '\\' :: c :: r => "dDwWsSbB".contains c || regexClasses r
  | _ :: r => regexClasses r
  | [] => false

/-- Would RE2 and Rust's `regex` crate read the classes of `p` differently on
`s`? Rust's are Unicode classes, and its `\\s` includes `\\v`. -/
def classesDiffer (s p : String) : Bool :=
  regexClasses p.toList && s.toList.any fun c => 128 ≤ c.toNat || c == '\x0b'

theorem classesDiffer_of_isPlain {s : String} (p : String) (h : isPlain s = true) :
    classesDiffer s p = false := by
  simp only [isPlain, isAscii, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  have : s.toList.any (fun c => 128 ≤ c.toNat || c == '\x0b') = false := by
    simp only [Bool.eq_false_iff, ne_eq, List.any_eq_true, not_exists, not_and, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    intro c hc hor
    rcases hor with hor | hor
    · have := h1 c hc; omega
    · subst hor; simp_all
  simp [classesDiffer, this]

/-- `f ()`, or a panic where the meaning of `p` on `s` is engine-specific.
The message depends on the pattern, so it is not a constant the compiler
evaluates once. -/
def regexEvaluated {α : Type} [Inhabited α] (s p : String) (f : Unit → α) : α :=
  if classesDiffer s p then
    panic! s!"regular expression {p} of non-ASCII text is not evaluated in Lean"
  else f ()

def regexMatchImpl (s p : String) : Option Nat := regexEvaluated s p fun _ =>
  let (r, g) := Regex.parse p
  (Regex.search r g s.toList.toArray 0).map fun _ => max g 1 - 1

def regexExtractImpl (s p : String) (g : Nat) : String := regexEvaluated s p fun _ =>
  let (r, n) := Regex.parse p
  let t := s.toList.toArray
  match Regex.search r n t 0 with
  | some caps => Regex.slice t (caps[g]?.getD none)
  | none => ""

def regexReplaceImpl (s p rw : String) (global : Bool) : String := regexEvaluated s p fun _ =>
  let (r, n) := Regex.parse p
  let t := s.toList.toArray
  if global then (Regex.replaceAll r n t rw.toList 0 none "" 0).1
  else match Regex.search r n t 0 with
    | none => s
    | some caps =>
      let (i, j) := (caps[0]!).getD (0, 0)
      Regex.slice t (some (0, i)) ++ Regex.rewrite t caps rw.toList ++ Regex.slice t (some (j, t.size))

/-- `regexp_match(s, p)`: `none` if `p` does not match `s`, otherwise `some k`
where the match has `k + 1` entries (its groups, or the whole match). -/
@[implemented_by regexMatchImpl] opaque regexMatch : String → String → Option Nat

/-- `regexp_extract(s, p, g)`: group `g` of the first match of `p` in `s`
(`0`: the whole match), or `''` where nothing matches, the group took no
part or `p` has fewer groups. -/
@[implemented_by regexExtractImpl] opaque regexExtract : String → String → Nat → String

/-- `regexp_replace(s, p, r)`: the first match of `p` in `s` (every match, if
`global`) replaced by `r`, where `\\0` … `\\9` are the match's groups and
`\\\\` a backslash. -/
@[implemented_by regexReplaceImpl] opaque regexReplace : String → String → String → Bool → String

/-- `md5(s)`: the MD5 digest of the UTF-8 bytes, as 32 lowercase hex digits. -/
@[implemented_by Digest.md5] opaque md5 : String → String

/-- `sha256(s)`: the SHA-256 digest of the UTF-8 bytes, as 64 lowercase hex digits. -/
@[implemented_by Digest.sha256] opaque sha256 : String → String

/-! ## Patterns that certainly compile

One engine compiles a pattern with Rust's `regex` crate when it first
evaluates it, and fails if it is invalid; another compiles a constant
pattern with RE2 when it plans the query. `simpleRegex` accepts a conservative
subset of both syntaxes: literal characters, `.`, `^`, `$`, escapes, groups
(also non-capturing, `(?:…)`), alternatives, simple classes and the
quantifiers `*`, `+`, `?` and `{n}`, `{n,}`, `{n,m}` with `n ≤ m ≤ 1000`, in
patterns of at most 200 characters (Rust allows 250 nested groups). That
these compile in both, and that RE2 matches them as `core/Sverify/Core/Regex.lean`
does, is part of the trusted model, tested by `python/tests/test_text.py`. -/

def plain (c : Char) : Bool := !"\\.+*?()|[]{}^$".contains c
def escapable (c : Char) : Bool := "\\.+*?()|[]{}^$-dDwWsSnt".contains c
def plainInClass (c : Char) : Bool := !"[]\\-&~^".contains c

/-- A repetition count: up to 4 digits, at most 1000. -/
def count (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  let n := (String.ofList ds).toNat?.getD 0
  if ds.isEmpty || 4 < ds.length || 1000 < n then none else some (n, cs.drop ds.length)

/-- Skip a quantifier, if there is one. -/
def quantifier : List Char → Option (List Char)
  | '*' :: r | '+' :: r | '?' :: r => some r
  | '{' :: r => do
    let (n, r) ← count r
    match r with
    | '}' :: r => some r
    | ',' :: '}' :: r => some r
    | ',' :: r =>
      let (m, r) ← count r
      match r with
      | '}' :: r => if n ≤ m then some r else none
      | _ => none
    | _ => none
  | r => some r

/-- The items of a class up to its closing `]`. -/
def classItems : Nat → List Char → Option (List Char)
  | 0, _ => none
  | _ + 1, ']' :: r => some r
  | n + 1, '\\' :: c :: r => if "dDwWsS\\[]-^".contains c then classItems n r else none
  | n + 1, a :: '-' :: b :: r =>
    if plainInClass a && plainInClass b && a ≤ b then classItems n r else none
  | n + 1, a :: r => if plainInClass a then classItems n r else none
  | _ + 1, [] => none

/-- A class after its `[`: an optional `^`, then at least one item. -/
def classBody (cs : List Char) : Option (List Char) :=
  let cs := match cs with
    | '^' :: r => r
    | r => r
  match cs with
  | ']' :: _ => none
  | _ => classItems (cs.length + 1) cs

mutual
/-- Alternatives, up to a `)` or the end. -/
def alternatives : Nat → List Char → Option (List Char)
  | 0, _ => none
  | n + 1, cs => do
    match ← sequence n cs with
    | '|' :: r => alternatives n r
    | r => some r

/-- A sequence of (quantified) atoms, up to a `|`, a `)` or the end. -/
def sequence : Nat → List Char → Option (List Char)
  | 0, _ => none
  | n + 1, cs => match cs with
    | [] => some []
    | ')' :: _ | '|' :: _ => some cs
    | '^' :: r | '$' :: r => sequence n r
    | '\\' :: c :: r =>
      if "bB".contains c then sequence n r
      else if escapable c then quantifier r >>= sequence n
      else none
    | '.' :: r => quantifier r >>= sequence n
    | '(' :: '?' :: ':' :: r | '(' :: r => do
      match ← alternatives n r with
      | ')' :: r => quantifier r >>= sequence n
      | _ => none
    | '[' :: r => classBody r >>= quantifier >>= sequence n
    | c :: r => if plain c then quantifier r >>= sequence n else none
end

def simpleRegex (p : String) : Bool :=
  p.length ≤ 200 && alternatives (3 * p.length + 3) p.toList == some []

/-- The number of capture groups of a pattern `simpleRegex` accepts. -/
def regexGroups (p : String) : Nat := (Regex.parse p).2

/-- A replacement RE2 accepts for a pattern with `g` groups: `\\0` … `\\g`
and `\\\\`, and no other backslash. -/
def rewriteOk (g : Nat) : List Char → Bool
  | '\\' :: c :: r => (c == '\\' || (c.isDigit && c.toNat - 48 ≤ g)) && rewriteOk g r
  | ['\\'] => false
  | _ :: r => rewriteOk g r
  | [] => true

#guard substr "hello" 0 (some 2) == "h"
#guard substr "hello" (-1) (some 3) == "h"
#guard substr "hello" 10 (some 2) == ""
#guard substr "hello" 2 (some 0) == ""
#guard substr "hello" 2 none == "ello"
#guard substr "héllo" 2 (some 2) == "él"
#guard strpos "héllo" "l" == 3 && strpos "abc" "" == 1 && strpos "" "" == 1 && strpos "abc" "d" == 0
#guard like "abc" "a%" && like "abc" "a_c" && like "a%c" "a\\%c" && !like "abc" "a\\%c"
#guard !like "ABC" "a%" && like "a\\" "a\\" && like "abc" "a\\bc" && !like "a\\bc" "a\\bc"
#guard like "" "%" && !like "" "_"
#guard trim true true "  ab  " " " == "ab" && trim true true "xyabyx" "xy" == "ab"
#guard repeatStr "ab" 3 == "ababab" && repeatStr "ab" (-1) == "" && repeatStr "ab" 0 == ""
#guard repeatFits "ab" (2 ^ 30 - 1) && !repeatFits "ab" (2 ^ 30) && !repeatFits "é" (2 ^ 30)
#guard repeatStr "" (2 ^ 63 - 1) == "" && repeatStr "ab" (2 ^ 63 - 1 - 2 ^ 63) == ""
#guard repeatFits "" (2 ^ 62) && repeatFits "ab" (-(2 ^ 62))
#guard reverse "héllo" == "olléh" && reverse "" == ""
#guard replace "ab" "" "x" == "ab" && replace "aaa" "aa" "b" == "ba" && replace "ab" "a" "" == "b"
#guard replace "" "" "x" == "" && replace "abcabc" "bc" "Z" == "aZaZ"
#guard ascii "" == 0 && ascii "é" == 233 && ascii "ab" == 97
#guard levenshtein "kitten" "sitting" == 3 && levenshtein "" "" == 0 && levenshtein "abc" "" == 3
#guard levenshtein "" "ab" == 2 && levenshtein "é" "e" == 1 && levenshtein "flaw" "lawn" == 2
#guard ilikeAscii "ABC" "a%" && ilikeAscii "abc" "A_C" && !ilikeAscii "abd" "a_c"
#guard simpleRegex "^a" && simpleRegex "(a)(b)" && simpleRegex "\\d{4}-\\d{2}" && simpleRegex "[a-z]+$"
#guard !simpleRegex "(" && !simpleRegex "a**" && !simpleRegex "[]" && !simpleRegex "(?i)a"
#guard !simpleRegex "a{3,2}" && !simpleRegex "*a"
-- A quantifier with no digits (`0{`) reached `Regex.digits` and `count` through `toNat!`.
#guard !simpleRegex "0{"
#guard simpleRegex "(?:a)(b)" && !simpleRegex "(?i)a" && !simpleRegex "(?=a)"
#guard regexGroups "(a)(?:b)(c(d))" == 3 && regexGroups "[(]\\(" == 0
#guard rewriteOk 1 "[\\1\\0\\\\]".toList && !rewriteOk 1 "\\2".toList && !rewriteOk 1 "a\\".toList
#guard !rewriteOk 1 "\\n".toList
#guard regexExtractImpl "abc" "x" 0 == "" && regexExtractImpl "abc" "(b)(c)" 2 == "c"
#guard regexExtractImpl "abc" "(x)?b" 1 == "" && regexExtractImpl "abc" "(b)" 2 == ""
#guard regexExtractImpl "aaa" "(a*)*" 1 == "aaa" && regexExtractImpl "ab" "(a|ab)(c|bcd)?" 0 == "a"
#guard regexExtractImpl "xay" "(?:x)(a)" 1 == "a" && regexExtractImpl "a\nb" "a.b" 0 == ""
#guard regexReplaceImpl "aaa" "a" "b" false == "baa" && regexReplaceImpl "aaa" "a" "b" true == "bbb"
#guard regexReplaceImpl "abc" "(b)" "[\\1\\0]" false == "a[bb]c"
#guard regexReplaceImpl "abc" "" "-" true == "-a-b-c-" && regexReplaceImpl "abc" "b*" "-" true == "-a-c-"
#guard regexReplaceImpl "abc" "\\b" "|" true == "|abc|"
#guard regexReplaceImpl "abab" "(a)|(b)" "[\\1\\2]" true == "[a][b][a][b]"
#guard regexMatchImpl "abc" "(b)(c)" == some 1 && regexMatchImpl "abc" "b" == some 0
#guard regexMatchImpl "abc" "^b" == none

end Substrait.Text
