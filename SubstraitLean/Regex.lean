/-!
# Evaluating regular expressions (#50)

The evaluator behind the black boxes `Text.regexMatch`, `Text.regexExtract`
and `Text.regexReplace` (`implemented_by`): no proof sees it. It covers the
patterns `Text.simpleRegex` accepts, with RE2's meaning, which DuckDB uses:

* leftmost-first matching: the leftmost match, and among those the one a
  backtracking matcher finds first (alternatives in order, greedy
  quantifiers), with its capture groups;
* `.` matches any character but `\n`; `^` and `$` match only at the start
  and end of the text;
* `\d`, `\w`, `\s` and `\b` are ASCII (`\s` is `[\t\n\f\r ]`);
* an iteration of `*`, `+` or `{n,}` beyond the minimum must not be empty,
  so `(a*)*` captures `'aaa'` in `'aaa'`, as RE2 does.

Rust's `regex` crate, which DataFusion and Polars use, reads `\d`, `\w`, `\s`
and `\b` as Unicode classes, and its `\s` includes `\v`. Where a text would
tell them apart, the evaluator panics instead of picking one, and
`substrait-check` then refuses to print rows (`Text.classesDiffer`).

Positions are character indices into the text, so `(i, j)` is the match of
characters `i … j-1`. The parser and the matcher are `partial`: they only
run, they are not reasoned about.
-/

namespace Substrait.Regex

/-- A member of a class `[…]`: a range of characters, or `\d`, `\w`, … -/
inductive ClassItem where
  | range (lo hi : Char)
  | perl (c : Char)
  deriving Inhabited

inductive Re where
  | lit (c : Char)
  /-- `.` -/
  | any
  | cls (neg : Bool) (items : List ClassItem)
  /-- `^`, `$`: the start and the end of the text. -/
  | bol | eol
  /-- `\b` (`neg = false`) and `\B`. -/
  | word (neg : Bool)
  /-- A group: capturing (its number), or `(?:…)` (`none`). -/
  | group (idx : Option Nat) (r : Re)
  | seq (rs : List Re)
  | alt (rs : List Re)
  /-- `r{lo,hi}`, greedy; `*` is `{0,}`, `+` `{1,}` and `?` `{0,1}`. -/
  | rep (r : Re) (lo : Nat) (hi : Option Nat)
  deriving Inhabited

/-- RE2's ASCII classes `\d`, `\w`, `\s` and their complements. -/
def perl (k c : Char) : Bool :=
  let n := c.toNat
  let d := 48 ≤ n && n ≤ 57
  let w := d || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || c == '_'
  let s := c == '\t' || c == '\n' || c == '\x0c' || c == '\r' || c == ' '
  match k with
  | 'd' => d | 'D' => !d | 'w' => w | 'W' => !w | 's' => s | 'S' => !s
  | _ => false

def ClassItem.has (c : Char) : ClassItem → Bool
  | .range lo hi => lo ≤ c && c ≤ hi
  | .perl k => Regex.perl k c

/-! ## Parsing

The grammar of `Text.simpleRegex`; the parser assumes the pattern is in it. -/

def digits (cs : List Char) : Nat × List Char :=
  let ds := cs.takeWhile Char.isDigit
  ((String.ofList ds).toNat!, cs.drop ds.length)

/-- A quantifier, if there is one: its bounds and the rest. -/
def quantifier : List Char → Option ((Nat × Option Nat) × List Char)
  | '*' :: r => some ((0, none), r)
  | '+' :: r => some ((1, none), r)
  | '?' :: r => some ((0, some 1), r)
  | '{' :: r =>
    let (n, r) := digits r
    match r with
    | '}' :: r => some ((n, some n), r)
    | ',' :: '}' :: r => some ((n, none), r)
    | ',' :: r =>
      let (m, r) := digits r
      some ((n, some m), r.drop 1)
    | _ => none
  | _ => none

def quantify (a : Re) (cs : List Char) : Re × List Char :=
  match quantifier cs with
  | some ((lo, hi), r) => (.rep a lo hi, r)
  | none => (a, cs)

/-- The items of a class after its `[` and optional `^`, up to `]`. -/
partial def classItems (acc : List ClassItem) : List Char → List ClassItem × List Char
  | ']' :: r => (acc.reverse, r)
  | '\\' :: c :: r =>
    classItems ((if "dDwWsS".contains c then .perl c else .range c c) :: acc) r
  | a :: '-' :: b :: r => if b == ']' then classItems (.range a a :: acc) ('-' :: b :: r)
    else classItems (.range a b :: acc) r
  | a :: r => classItems (.range a a :: acc) r
  | [] => (acc.reverse, [])

/-- An escaped character outside a class. -/
def escape (c : Char) : Re :=
  if "dDwWsS".contains c then .cls false [.perl c]
  else if c == 'n' then .lit '\n'
  else if c == 't' then .lit '\t'
  else .lit c

mutual
/-- Alternatives up to a `)` or the end; `g` is the number of groups opened
before, and is returned updated. -/
partial def parseAlt (cs : List Char) (g : Nat) : Re × List Char × Nat :=
  let (a, r, g) := parseSeq cs g []
  match r with
  | '|' :: r =>
    let (b, r, g) := parseAlt r g
    match b with
    | .alt bs => (.alt (a :: bs), r, g)
    | b => (.alt [a, b], r, g)
  | r => (a, r, g)

partial def parseSeq (cs : List Char) (g : Nat) (acc : List Re) : Re × List Char × Nat :=
  let next (a : Re) (r : List Char) (g : Nat) :=
    let (a, r) := quantify a r
    parseSeq r g (a :: acc)
  match cs with
  | [] | ')' :: _ | '|' :: _ => (.seq acc.reverse, cs, g)
  | '^' :: r => parseSeq r g (.bol :: acc)
  | '$' :: r => parseSeq r g (.eol :: acc)
  | '\\' :: 'b' :: r => parseSeq r g (.word false :: acc)
  | '\\' :: 'B' :: r => parseSeq r g (.word true :: acc)
  | '\\' :: c :: r => next (escape c) r g
  | '.' :: r => next .any r g
  | '(' :: '?' :: ':' :: r =>
    let (x, r, g) := parseAlt r g
    next (.group none x) (r.drop 1) g
  | '(' :: r =>
    let (x, r, g') := parseAlt r (g + 1)
    next (.group (some (g + 1)) x) (r.drop 1) g'
  | '[' :: '^' :: r =>
    let (items, r) := classItems [] r
    next (.cls true items) r g
  | '[' :: r =>
    let (items, r) := classItems [] r
    next (.cls false items) r g
  | c :: r => next (.lit c) r g
end

/-- A pattern and its number of capture groups. -/
def parse (p : String) : Re × Nat :=
  let (r, _, g) := parseAlt p.toList 0
  (r, g)

/-! ## Matching -/

/-- Each group's match, `none` where it took no part; group 0 is the whole match. -/
abbrev Caps := Array (Option (Nat × Nat))

def isWord (t : Array Char) (i : Nat) : Bool := (t[i]?.map (Regex.perl 'w')).getD false

mutual
/-- Match `r` at `i`, then the continuation `k`: the first success in
priority order. -/
partial def run (t : Array Char) (r : Re) (i : Nat) (caps : Caps)
    (k : Nat → Caps → Option Caps) : Option Caps :=
  match r with
  | .lit c => if t[i]? == some c then k (i + 1) caps else none
  | .any => match t[i]? with
    | some c => if c != '\n' then k (i + 1) caps else none
    | none => none
  | .cls neg items => match t[i]? with
    | some c => if items.any (·.has c) != neg then k (i + 1) caps else none
    | none => none
  | .bol => if i == 0 then k i caps else none
  | .eol => if i == t.size then k i caps else none
  | .word neg =>
    let b := (i > 0 && isWord t (i - 1)) != isWord t i
    if b != neg then k i caps else none
  | .group none r => run t r i caps k
  | .group (some g) r => run t r i caps fun j c => k j (c.set! g (some (i, j)))
  | .seq [] => k i caps
  | .seq (r :: rs) => run t r i caps fun j c => run t (.seq rs) j c k
  | .alt rs => rs.findSome? fun r => run t r i caps k
  | .rep r lo hi => runRep t r lo hi 0 i caps k

/-- Iteration `n` of `r{lo,hi}` at `i`: greedily one more, else stop. -/
partial def runRep (t : Array Char) (r : Re) (lo : Nat) (hi : Option Nat) (n i : Nat)
    (caps : Caps) (k : Nat → Caps → Option Caps) : Option Caps :=
  let more :=
    if hi.all (n < ·) then
      run t r i caps fun j c =>
        -- Beyond the minimum, an iteration must make progress.
        if j == i && lo ≤ n then none else runRep t r lo hi (n + 1) j c k
    else none
  match more with
  | some c => some c
  | none => if lo ≤ n then k i caps else none
end

/-- The leftmost-first match of `r` (with `g` groups) in `t` at or after
`start`. -/
partial def search (r : Re) (g : Nat) (t : Array Char) (start : Nat) : Option Caps :=
  if t.size < start then none
  else match run t r start (Array.replicate (g + 1) none) (fun j c => some (c.set! 0 (some (start, j)))) with
    | some c => some c
    | none => search r g t (start + 1)

def slice (t : Array Char) : Option (Nat × Nat) → String
  | some (i, j) => String.ofList (t.extract i j).toList
  | none => ""

/-- RE2's `Rewrite`: `\0` … `\9` are the groups (`''` where a group took no
part), `\\` is a backslash. -/
def rewrite (t : Array Char) (caps : Caps) : List Char → String
  | '\\' :: c :: r =>
    if c.isDigit then slice t (caps[c.toNat - 48]?.getD none) ++ rewrite t caps r
    else c.toString ++ rewrite t caps r
  | c :: r => c.toString ++ rewrite t caps r
  | [] => ""

/-- RE2's `GlobalReplace`: every match from the left; an empty match right
where the previous match ended is skipped by one character. -/
partial def replaceAll (r : Re) (g : Nat) (t : Array Char) (rw : List Char) (p : Nat)
    (lastEnd : Option Nat) (out : String) (count : Nat) : String × Nat :=
  if t.size < p then (out, count)
  else match search r g t p with
    | none => (out ++ slice t (some (p, t.size)), count)
    | some caps =>
      let (i, j) := (caps[0]!).getD (p, p)
      let out := out ++ slice t (some (p, i))
      if i == j && lastEnd == some i then
        replaceAll r g t rw (p + 1) lastEnd (out ++ slice t (some (p, min (p + 1) t.size))) count
      else replaceAll r g t rw j (some j) (out ++ rewrite t caps rw) (count + 1)

end Substrait.Regex
