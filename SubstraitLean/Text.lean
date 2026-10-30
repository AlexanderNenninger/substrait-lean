/-!
# String functions

DataFusion's string functions on Unicode scalar values (Lean's `Char`), checked
against DataFusion 51 by `python/tests/test_text.py`:

* `substring(s FROM a FOR n)` keeps the characters at 1-based positions
  `a … a+n-1` that exist; without `FOR`, all from `a` on. (A negative `n`
  fails; the parser only accepts constant `n ≥ 0`.)
* `strpos(s, t)` is the 1-based position of the first `t` in `s`, `0` if none
  (and `1` for the empty `t`).
* `LIKE` matches `%` (any characters) and `_` (one character); a backslash
  makes the next character literal, and a trailing backslash is itself.
* `btrim`/`ltrim`/`rtrim` remove characters of a set from the ends.

`UPPER`, `LOWER` and regular expressions are **black boxes**: `opaque`
functions, so no proof depends on what they compute. Lean's evaluator maps
ASCII case only, and evaluates no regular expressions.
-/

namespace Substrait.Text

def substr (s : String) (a : Int) (n : Option Nat) : String :=
  let cs := s.toList
  let lo := (a - 1).toNat
  let hi := match n with
    | some n => (a - 1 + n).toNat
    | none => cs.length
  String.ofList ((cs.drop lo).take (hi - lo))

def findFrom (t : List Char) : List Char → Nat → Option Nat
  | cs, i =>
    if t.isPrefixOf cs then some i
    else match cs with
      | [] => none
      | _ :: r => findFrom t r (i + 1)

def strpos (s t : String) : Int :=
  match findFrom t.toList s.toList 1 with
  | some i => i
  | none => 0

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

/-! ## Black boxes -/

def asciiOnly (f : String → String) (what : String) (s : String) : String :=
  if s.toList.all fun c => c.toNat < 128 then f s
  else panic! s!"{what} of non-ASCII text is not evaluated in Lean"

def upperAscii (s : String) : String := asciiOnly String.toUpper "UPPER" s
def lowerAscii (s : String) : String := asciiOnly String.toLower "LOWER" s

/-- `UPPER`: Unicode case mapping (`'ß'` becomes `"SS"`). -/
@[implemented_by upperAscii] opaque upper : String → String
/-- `LOWER`: Unicode case mapping. -/
@[implemented_by lowerAscii] opaque lower : String → String

def regexUnevaluated (_ _ : String) : Option Nat :=
  panic! "regular expressions are not evaluated in Lean"

/-- `regexp_match(s, p)`: `none` if `p` does not match `s`, otherwise `some k`
where the match has `k + 1` entries (its groups, or the whole match). -/
@[implemented_by regexUnevaluated] opaque regexMatch : String → String → Option Nat

/-! ## Patterns that certainly compile

DataFusion compiles a pattern with Rust's `regex` crate when it first
evaluates it, and fails if it is invalid. `simpleRegex` accepts a
conservative subset of its syntax: literal characters, `.`, `^`, `$`,
escapes, groups, alternatives, simple classes and the quantifiers `*`, `+`,
`?` and `{n}`, `{n,}`, `{n,m}` with `n ≤ m ≤ 1000`, in patterns of at most 200
characters (Rust allows 250 nested groups). That these compile is part of the
trusted model, tested by `python/tests/test_text.py`. -/

def plain (c : Char) : Bool := !"\\.+*?()|[]{}^$".contains c
def escapable (c : Char) : Bool := "\\.+*?()|[]{}^$-dDwWsSnt".contains c
def plainInClass (c : Char) : Bool := !"[]\\-&~^".contains c

/-- A repetition count: up to 4 digits, at most 1000. -/
def count (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  let n := (String.ofList ds).toNat!
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
    | '(' :: r => do
      match ← alternatives n r with
      | ')' :: r => quantifier r >>= sequence n
      | _ => none
    | '[' :: r => classBody r >>= quantifier >>= sequence n
    | c :: r => if plain c then quantifier r >>= sequence n else none
end

def simpleRegex (p : String) : Bool :=
  p.length ≤ 200 && alternatives (3 * p.length + 3) p.toList == some []

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
#guard simpleRegex "^a" && simpleRegex "(a)(b)" && simpleRegex "\\d{4}-\\d{2}" && simpleRegex "[a-z]+$"
#guard !simpleRegex "(" && !simpleRegex "a**" && !simpleRegex "[]" && !simpleRegex "(?i)a"
#guard !simpleRegex "a{3,2}" && !simpleRegex "*a"

end Substrait.Text
