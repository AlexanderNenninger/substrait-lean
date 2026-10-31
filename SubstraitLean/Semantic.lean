import SubstraitLean.Keys
import SubstraitLean.Check

/-!
# Semantic rewrites from contracts

Rewrites that hold only on data meeting a contract's preconditions: the
facts and keys that `Rel.aeval` and `Rel.keys` derive from them justify each
one. Engines apply such rewrites only for constraints they enforce, or that
the user asserts unchecked (`RELY`); ours are checked at ingestion or proved
through composition (`docs/optimizations.md` §3).

`Rel.optimize` rewrites bottom-up. At each node it decides from the analyses
of the already rewritten inputs, so one rewrite can enable the next.

* **`DISTINCT` on a key** (#76). If the input has a key, its rows are
  pairwise distinct and `dedup` keeps them all (`dedup_of_nodup`).
* **`GROUP BY` a key, without measures** (#76). Every group has one row, so
  the aggregate is the projection of its grouping expressions.
* **`fn(DISTINCT x)` with `x` a key** (#76). The values are distinct within
  every group, so `DISTINCT` changes nothing: `COUNT(DISTINCT id)` is
  `COUNT(id)`.

* **Filters the contract implies** (#78). If the abstract evaluation shows
  the condition certainly TRUE on the input (`Expr.absD`, as for a
  postcondition), the filter keeps every row and goes. If it shows the
  condition never TRUE, no row passes, and the plan is an empty `VALUES`.
  This removes CHECK constraints the engine does not enforce, and re-checks
  of an upstream guarantee in a composed pipeline.

* **Left joins that are inner joins** (#77). A left join pads a left row
  only when nothing matches it. If the condition is `l.k = r.pk`, `l.k` is
  NOT NULL and comes from a table column with a foreign key to a column that
  `r` keeps every value of (`Rel.origin`, `Rel.cover`), every left row has
  a match: the fact-table-to-dimension case, which engines cannot see from
  unenforced constraints. Under a filter that is never TRUE on a padded row
  (one testing a right column), the padded rows go anyway, and that case
  needs no foreign key.

* **Joins that only check a key** (#75). If the condition determines a key
  of the right side, each left row has at most one partner; a left join then
  gives one row per left row, and so does an inner join on a NOT NULL foreign
  key. When nothing above reads the right side's columns (an emit, a
  projection, an aggregate), the join goes (`Rel.joinElim`).

* **Eager aggregation below a join on a key** (#80). A `GROUP BY` of left
  columns over `R ⋈ S`, where the condition determines a key of `S` and only
  reads left columns that are grouped, aggregates `R` first and joins the
  groups with `S`. Every left row has at most one partner, and the rows of a
  group all have one or none, so the join only keeps or drops whole groups.

`Rel.step` applies rules until none fires (at most four times), so a join
that goes can leave a `DISTINCT` that goes next.

`Rel.optimize_sound`: on every catalog meeting the preconditions, the
rewritten plan is well-formed, has the same arity, and gives the same list of
rows. As elsewhere (`Rel.guardFree_sound`, `Rel.shardSplit_sound`), the
checker runs the analyses on the schema-only catalog: they read only arities.
-/

namespace Substrait

theorem dedupN_of_nodup {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.Nodup → dedupN n l = l
  | _, [], _, _ => by cases ‹Nat› <;> simp [dedupN]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, x :: xs, h, hnd => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    have hf : xs.filter (· != x) = xs :=
      List.filter_eq_self.2 fun y hy => by simpa using fun h : y = x => hx (h ▸ hy)
    simp only [dedupN, hf]
    rw [dedupN_of_nodup n xs (by simp at h; omega) hxs]

theorem dedup_of_nodup {α : Type} [DecidableEq α] {l : List α} (h : l.Nodup) : dedup l = l :=
  dedupN_of_nodup _ l (Nat.le_refl _) h

/-- Values that a key's columns determine are distinct across the rows. -/
theorem KeyOn.map_pairwise {β : Type} {k : List Nat} {rows : Relation} (h : KeyOn k rows)
    {f : Row → β} (hf : ∀ x y, f x = f y → keyOf k x = keyOf k y) :
    (rows.map f).Pairwise (· ≠ ·) :=
  List.pairwise_map.mpr (h.imp fun hne heq => hne (hf _ _ heq))

/-! ## The rewrites -/

/-- Is `e` a column `c` that is a key by itself (`[c]`, `[c, c]` or `[]`)? -/
def keyCol (ks : List (List Nat)) : Expr → Bool
  | .field c => ks.any (·.all (· == c))
  | _ => false

def Measure.dropDistinct (ks : List (List Nat)) (m : Measure) : Measure :=
  if m.distinct && keyCol ks m.arg then { m with distinct := false } else m

/-- Do the grouping expressions include the columns of a key? -/
def groupsKey (ks : List (List Nat)) (gs : List Expr) : Bool :=
  ks.any (·.all fun c => gs.contains (.field c))

/-! ## Foreign keys and where columns come from -/

/-- Foreign keys of each table: `(c, s, p)` says every non-NULL value of
column `c` occurs in column `p` of table `s`. -/
abbrev ForeignKeys := String → List (Nat × String × Nat)

def ForeignKeys.Hold (R : ForeignKeys) (cat : Catalog) : Prop :=
  ∀ t, ∀ fk ∈ R t, ∀ x ∈ (cat t).rows, x.getD fk.1 .null ≠ .null →
    ∃ y ∈ (cat fk.2.1).rows, y.getD fk.2.2 .null = x.getD fk.1 .null

/-- The table column that the non-NULL values of column `i` come from. -/
def Rel.origin (cat : Catalog) : Rel → Nat → Option (String × Nat)
  | .read t, i => some (t, i)
  | .values _ _, _ => none
  | .filter r _, i | .fetch r _ _, i | .orderBy r _, i | .distinct r, i | .semi r _ _ _, i =>
      r.origin cat i
  | .project r es, i =>
      if i < r.arity cat then r.origin cat i
      else match es[i - r.arity cat]? with
        | some (.field j) => r.origin cat j
        | _ => none
  | .window r _ _ _, i => if i < r.arity cat then r.origin cat i else none
  | .emit r m, i => m[i]?.bind (r.origin cat)
  | .cross a b, i | .join a b _ _, i =>
      if i < a.arity cat then a.origin cat i else b.origin cat (i - a.arity cat)
  | .unionAll a b, i => if a.origin cat i = b.origin cat i then a.origin cat i else none
  | .aggregate r gs _, i => match gs[i]? with
    | some (.field j) => r.origin cat j
    | _ => none

/-- A table column whose non-NULL values all occur in column `j`. -/
def Rel.cover (cat : Catalog) : Rel → Nat → Option (String × Nat)
  | .read t, j => some (t, j)
  | .project r _, j => if j < r.arity cat then r.cover cat j else none
  | .emit r m, j => m[j]?.bind (r.cover cat)
  | .orderBy r _, j | .distinct r, j => r.cover cat j
  | _, _ => none

/-- The columns `on` equates, the left one first and the right one relative
to the right side. -/
def eqPair (n : Nat) : Expr → Option (Nat × Nat)
  | .bin .eq (.field i) (.field j) =>
    if i < n ∧ n ≤ j then some (i, j - n) else if j < n ∧ n ≤ i then some (j, i - n) else none
  | _ => none

/-- Does every left row of `a ⟕ b ON on` have a match, by a foreign key? -/
def Rel.fkMatch (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : ForeignKeys) (a b : Rel) (on : Expr) : Bool :=
  match eqPair (a.arity cat) on with
  | some (i, j) => match a.origin cat i, b.cover cat j with
    | some (t, c), some (s, p) =>
      (R t).contains (c, s, p) &&
        !((a.aeval cat A F (Rel.keyedWindows cat A F K)).getD i AVal.top).null
    | _, _ => false
  | none => false

/-- A join whose rows are its left rows, extended: the condition determines a
key of the right side (at most one partner per left row), and for an inner
join a foreign key gives every left row one. Returns the rewrite's name, the
left side and the right side's arity. -/
def Rel.joinElim (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : ForeignKeys) : Rel → Option (String × Rel × Nat)
  | .join a b ty on =>
    if (b.keys cat A F K).any (determines on (a.arity cat)) then
      match ty with
      | .left => some ("left join on a key, no column used", a, b.arity cat)
      | .inner =>
        if Rel.fkMatch cat A F K R a b on then
          some ("join on a foreign key, no column used", a, b.arity cat)
        else none
    else none
  | _ => none

/-- An abstract row of NULLs. -/
def nullRow (n : Nat) : List AVal := List.replicate n (AVal.ofValue .null)

/-- What the abstract evaluation knows about `c` on the rows of `r`. -/
def Rel.condVal (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) (c : Expr) : AVal :=
  let T := Rel.keyedWindows cat A F K
  c.absD (r.aeval cat A F T) (r.facts cat F T)

/-! ## Functional dependencies -/

/-- On `rows`, the columns `k` determine column `c`. -/
def FD (k : List Nat) (c : Nat) (rows : Relation) : Prop :=
  ∀ x ∈ rows, ∀ y ∈ rows, keyOf k x = keyOf k y → x.getD c .null = y.getD c .null

/-- A key determines every column. -/
def keyFds (ks : List (List Nat)) (n : Nat) : List (List Nat × Nat) :=
  ks.flatMap fun k => (List.range n).map (k, ·)

/-- Columns a condition equates determine each other. -/
def eqFds (ps : List (Nat × Nat)) : List (List Nat × Nat) :=
  ps.flatMap fun p => [([p.1], p.2), ([p.2], p.1)]

def inRange (n : Nat) (fd : List Nat × Nat) : Bool := fd.1.all (· < n) && decide (fd.2 < n)

def shiftFd (n : Nat) (fd : List Nat × Nat) : List Nat × Nat := (fd.1.map (n + ·), n + fd.2)

/-- A position of column `x` in an emit. -/
def emitPos? (m : List Nat) (x : Nat) : Option Nat := (List.range m.length).find? (m[·]? == some x)

/-- A dependency through an emit, for every position of its column. -/
def emitFd (m : List Nat) (fd : List Nat × Nat) : List (List Nat × Nat) :=
  if fd.1.all fun x => (emitPos? m x).isSome then
    ((List.range m.length).filter (m[·]? == some fd.2)).map
      fun p => (fd.1.map fun x => (emitPos? m x).getD 0, p)
  else []

/-- A projected column `$j` and its copy determine each other. -/
def copyFds (n : Nat) (es : List Expr) : List (List Nat × Nat) :=
  es.zipIdx.flatMap fun (e, q) => match e with
    | .field j => if j < n then [([j], n + q), ([n + q], j)] else []
    | _ => []

/-- Functional dependencies of a plan's output: from the input keys, the
grouping columns of an aggregate, equalities in filters and inner joins, and
copied columns. -/
def Rel.fds (cat : Catalog) (K : String → List (List Nat)) : Rel → List (List Nat × Nat)
  | .read t => keyFds (K t) (cat t).arity
  | .aggregate _ gs ms => keyFds [List.range gs.length] (gs.length + ms.length)
  | .filter r c => r.fds cat K ++ eqFds c.eqCols
  | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ => r.fds cat K
  | .project r es => (r.fds cat K).filter (inRange (r.arity cat)) ++ copyFds (r.arity cat) es
  | .window r _ _ _ => (r.fds cat K).filter (inRange (r.arity cat))
  | .emit r m => (r.fds cat K).flatMap (emitFd m)
  | .cross a b => (a.fds cat K).filter (inRange (a.arity cat)) ++
      (b.fds cat K).map (shiftFd (a.arity cat))
  | .join a b .inner on => (a.fds cat K).filter (inRange (a.arity cat)) ++
      (b.fds cat K).map (shiftFd (a.arity cat)) ++ eqFds on.eqCols
  | .join a _ .left _ => (a.fds cat K).filter (inRange (a.arity cat))
  | .values _ _ | .unionAll _ _ => []

/-- The columns that `X` determines, `fuel` rounds deep. -/
def fdClosure (fds : List (List Nat × Nat)) : Nat → List Nat → List Nat
  | 0, X => X
  | fuel + 1, X => fdClosure fds fuel (X ++ (fds.filter fun fd => fd.1.all (X.contains ·)).map (·.2))

def fieldsOf (es : List Expr) : List Nat := es.filterMap fun | .field j => some j | _ => none

/-- Grouping positions to keep: drop a column the others determine (greedy;
`Rel.fdAgg` checks the result). -/
def keepCols (fds : List (List Nat × Nat)) (gs : List Expr) : List Nat :=
  (List.range gs.length).foldl (fun keep q =>
    let others := keep.filter (· != q)
    match gs.getD q (.lit .null) with
    | .field c =>
      if (fdClosure fds (fds.length + 1) (fieldsOf (others.map (gs.getD · (.lit .null))))).contains c
      then others else keep
    | _ => keep) (List.range gs.length)

/-- The `q`-th grouping expression. -/
def gAt (gs : List Expr) (q : Nat) : Expr := gs.getD q (.lit .null)

def determinedBy (cl : List Nat) (gs : List Expr) (q : Nat) : Bool :=
  match gAt gs q with
  | .field c => cl.contains c
  | _ => false

def minOf (gs : List Expr) (q : Nat) : Measure := { fn := .min, arg := gAt gs q }

/-- Where the original columns are in the rewritten aggregate. -/
def fdEmit (qs drops : List Nat) (n m : Nat) : List Nat :=
  (List.range n).map (fun q => if qs.contains q then qs.idxOf q else qs.length + m + drops.idxOf q) ++
    (List.range m).map (qs.length + ·)

/-- `GROUP BY gs` as `GROUP BY` the kept columns, carrying the ones they
determine through `MIN` (all values of a group agree on them). -/
def Rel.fdAgg (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) (gs : List Expr) (ms : List Measure) :
    Option (String × Rel) :=
  let fds := r.fds cat K ++ keyFds (r.keys cat A F K) (r.arity cat)
  let qs := keepCols fds gs
  let drops := (List.range gs.length).filter (!qs.contains ·)
  let cl := fdClosure fds (fds.length + 1) (fieldsOf (qs.map (gAt gs)))
  if !qs.isEmpty && !drops.isEmpty && drops.all (determinedBy cl gs) then
    some ("GROUP BY columns that others determine",
      .emit (.aggregate r (qs.map (gAt gs)) (ms ++ drops.map (minOf gs)))
        (fdEmit qs drops gs.length ms.length))
  else none

/-- Do all of `e`'s column references satisfy `p`? -/
def Expr.refsAll (p : Nat → Bool) : Expr → Bool
  | .lit _ => true
  | .field i => p i
  | .un _ a => a.refsAll p
  | .bin _ a b => a.refsAll p && b.refsAll p
  | .ifThen c t e => c.refsAll p && t.refsAll p && e.refsAll p

/-- The position of the grouping column `$c`. -/
def gpos (gs : List Expr) (c : Nat) : Option Nat :=
  (List.range gs.length).find? fun q => gs[q]? == some (.field c)

/-- A join condition's columns after the left side is aggregated: grouped
left columns move to their group position, right columns after the
aggregate's `out` columns. -/
def eagerCols (n : Nat) (gs : List Expr) (out k : Nat) : List Expr :=
  (List.range n).map (fun c => match gpos gs c with
    | some q => .field q
    | none => .lit .null) ++ (List.range k).map fun j => .field (out + j)

/-- `GROUP BY` of left columns over a join on a key of the right side, as the
join of the left side's groups with the right side. -/
def Rel.eagerAgg (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) (gs : List Expr) (ms : List Measure) :
    Option (String × Rel) :=
  match r with
  | .join a b .inner on =>
    if !gs.isEmpty && gs.all (·.refsLtb (a.arity cat)) &&
        ms.all (·.exprs.all (·.refsLtb (a.arity cat))) &&
        (b.keys cat A F K).any (determines on (a.arity cat)) &&
        on.refsAll (fun i => decide (a.arity cat ≤ i) || (gpos gs i).isSome) then
      some ("aggregate below a join on a key",
        .emit (.join (.aggregate a gs ms) b .inner
            (on.subst (eagerCols (a.arity cat) gs (gs.length + ms.length) (b.arity cat))))
          (List.range (gs.length + ms.length)))
    else none
  | _ => none

/-- One rewrite at the root, and its name for the report. -/
def Rel.rule (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : ForeignKeys) : Rel → Option (String × Rel)
  | .filter r c =>
    let a := r.condVal cat A F K c
    if a.certainlyTrue then some ("filter implied by the contract", r)
    else if !a.tt then some ("filter the contract rules out", .values (r.arity cat) [])
    else match r with
      | .join x y .left on =>
        let pad := x.aeval cat A F (Rel.keyedWindows cat A F K) ++ nullRow (y.arity cat)
        if !(c.absD pad []).tt then
          some ("left join under a filter rejecting NULLs", .filter (.join x y .inner on) c)
        else none
      | _ => none
  | .join a b .left on =>
    if Rel.fkMatch cat A F K R a b on then some ("left join on a foreign key", .join a b .inner on)
    else none
  | .distinct r => if (r.keys cat A F K).isEmpty then none else some ("DISTINCT on a key", r)
  | .aggregate r gs ms =>
    let ks := r.keys cat A F K
    if ms.isEmpty && !gs.isEmpty && groupsKey ks gs then
      some ("GROUP BY a key", .emit (.project r gs) ((List.range gs.length).map (r.arity cat + ·)))
    else if ms.any fun m => m.distinct && keyCol ks m.arg then
      some ("DISTINCT aggregate of a key", .aggregate r gs (ms.map (Measure.dropDistinct ks)))
    else match r.joinElim cat A F K R with
      | some (name, a, _) =>
        if gs.all (·.refsLtb (a.arity cat)) && ms.all (·.exprs.all (·.refsLtb (a.arity cat))) then
          some (name, .aggregate a gs ms)
        else none
      | none => match Rel.fdAgg cat A F K r gs ms with
        | some x => some x
        | none => Rel.eagerAgg cat A F K r gs ms
  | .emit r m =>
    match r.joinElim cat A F K R with
    | some (name, a, _) => if m.all (· < a.arity cat) then some (name, .emit a m) else none
    | none => match r with
      | .project j es => match j.joinElim cat A F K R with
        | some (name, a, k) =>
          if es.all (·.refsLtb (a.arity cat)) && m.all (fun i => i < a.arity cat || a.arity cat + k ≤ i)
          then some (name, .emit (.project a es) (m.map fun i => if i < a.arity cat then i else i - k))
          else none
        | none => none
      | _ => none
  | _ => none

/-- Apply `rule` at the root while it fires (`fuel` times at most), logging
the names. -/
def Rel.stepN (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : ForeignKeys) : Nat → Rel → List String → Rel × List String
  | 0, r, log => (r, log)
  | fuel + 1, r, log =>
    match r.rule cat A F K R with
    | some (name, s) => s.stepN cat A F K R fuel (log ++ [name])
    | none => (r, log)

def Rel.step (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : ForeignKeys) (r : Rel) (log : List String) :
    Rel × List String :=
  r.stepN cat A F K R 4 log

/-- Rewrite bottom-up; also return the names of the rewrites applied. -/
def Rel.optimize (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : ForeignKeys) : Rel → Rel × List String
  | .read t => (.read t, [])
  | .values n rows => (.values n rows, [])
  | .filter r c => step cat A F K R (.filter (r.optimize cat A F K R).1 c) (r.optimize cat A F K R).2
  | .project r es => step cat A F K R (.project (r.optimize cat A F K R).1 es) (r.optimize cat A F K R).2
  | .emit r m => step cat A F K R (.emit (r.optimize cat A F K R).1 m) (r.optimize cat A F K R).2
  | .cross a b => step cat A F K R (.cross (a.optimize cat A F K R).1 (b.optimize cat A F K R).1)
      ((a.optimize cat A F K R).2 ++ (b.optimize cat A F K R).2)
  | .join a b ty on => step cat A F K R (.join (a.optimize cat A F K R).1 (b.optimize cat A F K R).1 ty on)
      ((a.optimize cat A F K R).2 ++ (b.optimize cat A F K R).2)
  | .fetch r off cnt => step cat A F K R (.fetch (r.optimize cat A F K R).1 off cnt) (r.optimize cat A F K R).2
  | .unionAll a b => step cat A F K R (.unionAll (a.optimize cat A F K R).1 (b.optimize cat A F K R).1)
      ((a.optimize cat A F K R).2 ++ (b.optimize cat A F K R).2)
  | .window r part sort fns =>
      step cat A F K R (.window (r.optimize cat A F K R).1 part sort fns) (r.optimize cat A F K R).2
  | .semi a b anti on => step cat A F K R (.semi (a.optimize cat A F K R).1 (b.optimize cat A F K R).1 anti on)
      ((a.optimize cat A F K R).2 ++ (b.optimize cat A F K R).2)
  | .orderBy r keys => step cat A F K R (.orderBy (r.optimize cat A F K R).1 keys) (r.optimize cat A F K R).2
  | .distinct r => step cat A F K R (.distinct (r.optimize cat A F K R).1) (r.optimize cat A F K R).2
  | .aggregate r gs ms =>
      step cat A F K R (.aggregate (r.optimize cat A F K R).1 gs ms) (r.optimize cat A F K R).2

/-! ## Soundness -/

/-- `s` can replace `r`: well-formed, the same arity, the same rows. -/
structure Same (cat : Catalog) (r s : Rel) : Prop where
  wf : s.WF cat
  arity : s.arity cat = r.arity cat
  eval : s.eval cat = r.eval cat

theorem Same.trans {cat : Catalog} {r s t : Rel} (h : Same cat r s) (h' : Same cat s t) :
    Same cat r t := ⟨h'.wf, h'.arity.trans h.arity, h'.eval.trans h.eval⟩

theorem Measure.kept_sublist (m : Measure) (rows : Relation) : (m.kept rows).Sublist rows := by
  unfold kept; split
  · exact List.Sublist.refl _
  · exact List.filter_sublist

theorem Measure.eval_dropDistinct {ks : List (List Nat)} {rows : Relation}
    (hk : ∀ k ∈ ks, KeyOn k rows) (m : Measure) : (m.dropDistinct ks).eval rows = m.eval rows := by
  unfold dropDistinct
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hd, hc⟩ := h
    unfold keyCol at hc
    split at hc
    · rename_i c heq
      obtain ⟨k, hkm, hkc⟩ := List.any_eq_true.mp hc
      have hp := (hk k hkm).map_pairwise (f := m.arg.eval) fun x y he => by
        simp only [keyOf, List.map_inj_left]
        intro c' hc'
        have := List.all_eq_true.mp hkc c' hc'
        simp only [beq_iff_eq] at this
        subst this
        simpa [heq, Expr.eval] using he
      have hnd : (((m.kept rows).map m.arg.eval).filter (· != .null)).Nodup :=
        ((hp.sublist ((m.kept_sublist rows).map _)).filter _)
      simp only [Measure.eval, inputs, hd, ↓reduceIte, dedup_of_nodup hnd]
      rfl
    · simp at hc
  · rfl

theorem Measure.refsLt_dropDistinct {ks : List (List Nat)} {n : Nat} {m : Measure}
    (h : m.refsLt n) : (m.dropDistinct ks).refsLt n := by
  unfold dropDistinct; split <;> exact h

theorem aggregateEval_congr_ms {gs : List Expr} {ms ms' : List Measure} {rows : Relation}
    (h : ∀ grp, grp.Sublist rows → ms'.map (·.eval grp) = ms.map (·.eval grp)) :
    aggregateEval gs ms' rows = aggregateEval gs ms rows := by
  unfold aggregateEval
  split
  · rw [h rows (List.Sublist.refl _)]
  · exact List.map_congr_left fun k _ => by rw [h (groupRows gs rows k) List.filter_sublist]

/-! ### Foreign keys -/

/-- `Rel.origin` is right: a non-NULL value of column `i` is a value of the
table column. -/
def OriginOk (cat : Catalog) (r : Rel) : Prop :=
  ∀ {i t c}, r.origin cat i = some (t, c) → ∀ x ∈ r.eval cat, x.getD i .null ≠ .null →
    ∃ y ∈ (cat t).rows, y.getD c .null = x.getD i .null

/-- `Rel.cover` is right: every non-NULL value of the table column is in
column `j`. -/
def CoverOk (cat : Catalog) (r : Rel) : Prop :=
  ∀ {j t p}, r.cover cat j = some (t, p) → ∀ y ∈ (cat t).rows, y.getD p .null ≠ .null →
    ∃ z ∈ r.eval cat, z.getD j .null = y.getD p .null

theorem getD_replicate_null (k j : Nat) : (List.replicate k Value.null).getD j .null = .null := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem originOk_pair {cat : Catalog} {a b : Rel} {y z : Row} (hl : y.length = a.arity cat)
    (iha : OriginOk cat a) (ihb : OriginOk cat b) {i : Nat} {t : String} {c : Nat}
    (h : (if i < a.arity cat then a.origin cat i else b.origin cat (i - a.arity cat)) = some (t, c))
    (hy : y ∈ a.eval cat) (hz : z ∈ b.eval cat ∨ ∃ k, z = List.replicate k .null)
    (hn : (y ++ z).getD i .null ≠ .null) :
    ∃ w ∈ (cat t).rows, w.getD c .null = (y ++ z).getD i .null := by
  split at h
  · rename_i hi
    rw [getD_append_left' (by omega)] at hn ⊢
    exact iha h y hy hn
  · rename_i hi
    obtain ⟨d, rfl⟩ : ∃ d, i = y.length + d := ⟨i - y.length, by omega⟩
    rw [getD_append_right'] at hn ⊢
    rw [hl, Nat.add_sub_cancel_left] at h
    rcases hz with hz | ⟨k, rfl⟩
    · exact ihb h z hz hn
    · exact absurd (getD_replicate_null k d) hn

theorem Rel.origin_sound {cat : Catalog} (hcat : cat.WF) : ∀ {r : Rel}, r.WF cat → OriginOk cat r
  | .read _, _ => fun h x hx _ => by
      simp only [origin, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨x, hx, rfl⟩
  | .values _ _, _ => fun h => by simp [origin] at h
  | .filter r _, hwf => fun h x hx hn => by
      simp only [eval, List.mem_filter] at hx
      exact origin_sound hcat hwf.1 h x hx.1 hn
  | .fetch r _ _, hwf => fun h x hx hn => by
      simp only [eval] at hx
      have hx' : x ∈ r.eval cat := by
        split at hx
        · exact List.mem_of_mem_drop hx
        · exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
      exact origin_sound hcat (r := r) hwf h x hx' hn
  | .orderBy r _, hwf => fun h x hx hn => by
      simp only [eval, List.mem_mergeSort] at hx
      exact origin_sound hcat hwf.1 h x hx hn
  | .distinct r, hwf => fun h x hx hn => by
      simp only [eval, mem_dedup] at hx
      exact origin_sound hcat (r := r) hwf h x hx hn
  | .semi r _ _ _, hwf => fun h x hx hn => by
      simp only [eval, List.mem_filter] at hx
      exact origin_sound hcat hwf.1 h x hx.1 hn
  | .project r es, hwf => fun h x hx hn => by
      rename_i i _ _
      simp only [eval, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hl := eval_arity hcat hwf.1 y hy
      simp only [origin] at h
      split at h
      · rename_i hi
        rw [getD_append_left' (by omega)] at hn ⊢
        exact origin_sound hcat hwf.1 h y hy hn
      · rename_i hi
        obtain ⟨d, rfl⟩ : ∃ d, i = y.length + d := ⟨i - y.length, by omega⟩
        rw [← hl, Nat.add_sub_cancel_left] at h
        rw [getD_append_right'] at hn ⊢
        cases hg : es[d]? with
        | none => simp [hg] at h
        | some e =>
          cases e with
          | field j =>
            simp only [hg] at h
            have he : (es.map (·.eval y)).getD d .null = y.getD j .null := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_map, hg, Expr.eval]
            rw [he] at hn ⊢
            exact origin_sound hcat hwf.1 h y hy hn
          | _ => simp [hg] at h
  | .window r _ _ _, hwf => fun h x hx hn => by
      obtain ⟨_, y, _, _, hy, rfl⟩ := mem_windowEval hx
      have hl := eval_arity hcat hwf.1 y hy
      simp only [origin] at h
      split at h
      · rw [getD_append_left' (by omega)] at hn ⊢
        exact origin_sound hcat hwf.1 h y hy hn
      · simp at h
  | .emit r m, hwf => fun h x hx hn => by
      rename_i i _ _
      simp only [eval, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [origin] at h
      cases hm : m[i]? with
      | none => simp [hm] at h
      | some j =>
        simp only [hm, Option.bind_some] at h
        have he : (m.map (y.getD · .null)).getD i .null = y.getD j .null := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, hm]
        rw [he] at hn ⊢
        exact origin_sound hcat hwf.1 h y hy hn
  | .cross a b, hwf => fun h x hx hn => by
      simp only [eval, mem_crossRows] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      exact originOk_pair (eval_arity hcat hwf.1 y hy) (origin_sound hcat hwf.1)
        (origin_sound hcat hwf.2) h hy (.inl hz) hn
  | .join a b .inner _, hwf => fun h x hx hn => by
      simp only [eval, List.mem_filter, mem_crossRows] at hx
      obtain ⟨⟨y, hy, z, hz, rfl⟩, _⟩ := hx
      exact originOk_pair (eval_arity hcat hwf.1 y hy) (origin_sound hcat hwf.1)
        (origin_sound hcat hwf.2.1) h hy (.inl hz) hn
  | .join a b .left on, hwf => fun h x hx hn => by
      simp only [eval, List.mem_flatMap] at hx
      obtain ⟨y, hy, hx⟩ := hx
      unfold leftJoinRow at hx
      simp only [] at hx
      split at hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact originOk_pair (eval_arity hcat hwf.1 y hy) (origin_sound hcat hwf.1)
          (origin_sound hcat hwf.2.1) h hy (.inr ⟨_, rfl⟩) hn
      · simp only [List.mem_filter, List.mem_map] at hx
        obtain ⟨⟨z, hz, rfl⟩, _⟩ := hx
        exact originOk_pair (eval_arity hcat hwf.1 y hy) (origin_sound hcat hwf.1)
          (origin_sound hcat hwf.2.1) h hy (.inl hz) hn
  | .unionAll a b, hwf => fun h x hx hn => by
      simp only [origin] at h
      split at h
      · rename_i hab
        simp only [eval, List.mem_append] at hx
        rcases hx with hx | hx
        · exact origin_sound hcat hwf.1 h x hx hn
        · exact origin_sound hcat hwf.2.1 (hab ▸ h) x hx hn
      · simp at h
  | .aggregate r gs ms, hwf => fun h x hx hn => by
      rename_i i _ _
      obtain ⟨k, grp, rfl, -, hk⟩ := mem_aggregateEval hx
      simp only [origin] at h
      cases hg : gs[i]? with
      | none => simp [hg] at h
      | some e =>
        cases e with
        | field j =>
          simp only [hg] at h
          rcases hk with ⟨rfl, rfl⟩ | ⟨y, hy, rfl⟩
          · simp at hg
          · have hi : i < (groupKey gs y).length := by
              simp only [groupKey, List.length_map]
              exact (List.getElem?_eq_some_iff.mp hg).1
            have he : (groupKey gs y ++ ms.map (·.eval grp)).getD i .null = y.getD j .null := by
              rw [getD_append_left' hi]
              simp [groupKey, List.getD_eq_getElem?_getD, List.getElem?_map, hg, Expr.eval]
            rw [he] at hn ⊢
            exact origin_sound hcat hwf.1 h y hy hn
        | _ => simp [hg] at h

theorem Rel.cover_sound {cat : Catalog} (hcat : cat.WF) : ∀ {r : Rel}, r.WF cat → CoverOk cat r
  | .read _, _ => fun h y hy _ => by
      simp only [cover, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨y, hy, rfl⟩
  | .project r es, hwf => fun h y hy hn => by
      simp only [cover] at h
      split at h
      · rename_i hj
        obtain ⟨z, hz, he⟩ := cover_sound hcat hwf.1 h y hy hn
        refine ⟨_, List.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
        rw [getD_append_left' (by rw [eval_arity hcat hwf.1 z hz]; exact hj), he]
      · simp at h
  | .emit r m, hwf => fun h y hy hn => by
      rename_i j _ _
      simp only [cover] at h
      cases hm : m[j]? with
      | none => simp [hm] at h
      | some j' =>
        simp only [hm, Option.bind_some] at h
        obtain ⟨z, hz, he⟩ := cover_sound hcat hwf.1 h y hy hn
        refine ⟨_, List.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, hm] at he ⊢
        exact he
  | .orderBy r _, hwf => fun h y hy hn => by
      obtain ⟨z, hz, he⟩ := cover_sound hcat hwf.1 h y hy hn
      exact ⟨z, by simpa [eval, List.mem_mergeSort] using hz, he⟩
  | .distinct r, hwf => fun h y hy hn => by
      obtain ⟨z, hz, he⟩ := cover_sound hcat (r := r) hwf h y hy hn
      exact ⟨z, by simpa [eval, mem_dedup] using hz, he⟩
  | .values _ _, _ | .filter _ _, _ | .cross _ _, _ | .join _ _ _ _, _ | .fetch _ _ _, _
  | .unionAll _ _, _ | .window _ _ _ _, _ | .semi _ _ _ _, _ | .aggregate _ _ _, _ =>
      fun h => by simp [cover] at h

theorem eq_self_isTrue {v : Value} (h : v ≠ .null) : (BinFn.apply .eq v v).isTrue = true := by
  cases v <;> simp_all [BinFn.apply, Value.isTrue]

theorem eqPair_sound {n i j : Nat} {on : Expr} {x z : Row} (h : eqPair n on = some (i, j))
    (hl : x.length = n) (hv : z.getD j .null = x.getD i .null) (hn : x.getD i .null ≠ .null) :
    (on.eval (x ++ z)).isTrue = true := by
  unfold eqPair at h
  split at h
  · rename_i i' j'
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨d, rfl⟩ : ∃ d, j' = x.length + d := ⟨j' - x.length, by omega⟩
      simp only [Expr.eval, getD_append_left' (hl ▸ hc.1), getD_append_right']
      rw [← hl, Nat.add_sub_cancel_left] at hv
      rw [hv]; exact eq_self_isTrue hn
    · split at h
      · rename_i _ hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d, rfl⟩ : ∃ d, i' = x.length + d := ⟨i' - x.length, by omega⟩
        simp only [Expr.eval, getD_append_left' (hl ▸ hc.1), getD_append_right']
        rw [← hl, Nat.add_sub_cancel_left] at hv
        rw [hv]; exact eq_self_isTrue hn
      · simp at h
  · simp at h

/-- A left join where every left row has a match is an inner join. -/
theorem leftJoin_eq_inner {A B : Relation} {on : Expr} {k : Nat}
    (h : ∀ x ∈ A, ∃ z ∈ B, (on.eval (x ++ z)).isTrue = true) :
    A.flatMap (leftJoinRow on k B) = (crossRows A B).filter fun row => (on.eval row).isTrue := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    simp only [crossRows, List.flatMap_cons, List.filter_append] at ih ⊢
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    congr 1
    obtain ⟨z, hz, ht⟩ := h x (by simp)
    have hne : ((B.map (x ++ ·)).filter fun row => (on.eval row).isTrue) ≠ [] :=
      List.ne_nil_of_mem (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨z, hz, rfl⟩, ht⟩)
    simp [leftJoinRow, hne]

/-- Under a filter that no padded row passes, a left join is an inner join. -/
theorem filter_leftJoin {A B : Relation} {on c : Expr} {k : Nat}
    (h : ∀ x ∈ A, (c.eval (x ++ List.replicate k .null)).isTrue = false) :
    (A.flatMap (leftJoinRow on k B)).filter (fun row => (c.eval row).isTrue) =
      ((crossRows A B).filter fun row => (on.eval row).isTrue).filter
        fun row => (c.eval row).isTrue := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    simp only [crossRows, List.flatMap_cons, List.filter_append] at ih ⊢
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    congr 1
    simp only [leftJoinRow]
    split
    · rename_i he
      rw [List.isEmpty_iff.mp he]
      simp [h x (by simp)]
    · rfl

theorem EnvMem.nullRow (n : Nat) : EnvMem (nullRow n) (List.replicate n .null) := by
  intro j
  rw [getD_replicate_null]
  simp only [Substrait.nullRow, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp [AVal.ofValue, AVal.top, AVal.Mem]

/-! ### Join elimination -/

/-- A list whose elements are pairwise "different" under the empty relation has
at most one element. -/
theorem eq_nil_or_singleton {α : Type} : ∀ {l : List α}, l.Pairwise (fun _ _ => False) →
    l = [] ∨ ∃ a, l = [a]
  | [], _ => .inl rfl
  | [a], _ => .inr ⟨a, rfl⟩
  | _ :: b :: _, h => by simp at h; exact absurd rfl (h.1 b).1

/-- Each left row with exactly one output row extending it. -/
theorem flatMap_single {A : Relation} {G : Row → Relation}
    (h : ∀ x ∈ A, ∃ w, G x = [x ++ w]) :
    A.flatMap G = A.map (fun x => (G x).headD x) ∧
      ∀ x ∈ A, ∃ w, (G x).headD x = x ++ w := by
  refine ⟨?_, fun x hx => ?_⟩
  · induction A with
    | nil => rfl
    | cons x A ih =>
      obtain ⟨w, hw⟩ := h x (by simp)
      simp only [List.flatMap_cons, List.map_cons, hw, List.headD_cons, List.singleton_append]
      rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
  · obtain ⟨w, hw⟩ := h x hx
    exact ⟨w, by simp [hw]⟩

theorem Measure.eval_map {m : Measure} {grp : Relation} {g : Row → Row}
    (h : ∀ x ∈ grp, ∀ e ∈ m.exprs, e.eval (g x) = e.eval x) : m.eval (grp.map g) = m.eval grp := by
  have hk : m.kept (grp.map g) = (m.kept grp).map g := by
    unfold Measure.kept
    split
    · rfl
    · rename_i c hc
      rw [List.filter_map]
      congr 1
      exact List.filter_congr fun x hx => by
        simp [h x hx c (by simp [Measure.exprs, hc])]
  have ha : (m.kept grp).map (fun x => m.arg.eval (g x)) = (m.kept grp).map m.arg.eval :=
    List.map_congr_left fun x hx =>
      h x ((m.kept_sublist grp).subset hx) m.arg (by simp [Measure.exprs])
  simp only [Measure.eval, Measure.inputs, hk, List.map_map, Function.comp_def, ha]

theorem aggregateEval_map {gs : List Expr} {ms : List Measure} {A : Relation} {g : Row → Row}
    (hg : ∀ x ∈ A, ∀ e ∈ gs, e.eval (g x) = e.eval x)
    (hm : ∀ x ∈ A, ∀ m ∈ ms, ∀ e ∈ m.exprs, e.eval (g x) = e.eval x) :
    aggregateEval gs ms (A.map g) = aggregateEval gs ms A := by
  have hkey : ∀ x ∈ A, groupKey gs (g x) = groupKey gs x := fun x hx =>
    List.map_congr_left fun e he => hg x hx e he
  have hrows : ∀ k, groupRows gs (A.map g) k = (groupRows gs A k).map g := fun k => by
    unfold groupRows
    rw [List.filter_map]
    congr 1
    exact List.filter_congr fun x hx => by simp [hkey x hx]
  have hmeas : ∀ grp, (∀ x ∈ grp, x ∈ A) → ms.map (·.eval (grp.map g)) = ms.map (·.eval grp) :=
    fun grp hsub => List.map_congr_left fun m hm' =>
      Measure.eval_map fun x hx => hm x (hsub x hx) m hm'
  unfold aggregateEval
  split
  · rw [hmeas A fun _ h => h]
  · have hk : (A.map g).map (groupKey gs) = A.map (groupKey gs) := by
      rw [List.map_map]; exact List.map_congr_left fun x hx => hkey x hx
    rw [hk]
    exact List.map_congr_left fun k _ => by
      rw [hrows, hmeas (groupRows gs A k) fun x hx => (List.mem_filter.mp hx).1]

/-! ### Functional dependencies -/

theorem dedupN_parallel {α β : Type} [DecidableEq β] {f g : α → β} :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ x ∈ l, ∀ y ∈ l, f x = f y ↔ g x = g y) →
    ∃ L : List α, (∀ x ∈ L, x ∈ l) ∧ dedupN n (l.map f) = L.map f ∧ dedupN n (l.map g) = L.map g
  | _, [], _, _ => ⟨[], by simp, by cases ‹Nat› <;> simp [dedupN], by cases ‹Nat› <;> simp [dedupN]⟩
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, x :: xs, hl, he => by
    have hfg : xs.filter ((· != f x) ∘ f) = xs.filter ((· != g x) ∘ g) :=
      List.filter_congr fun y hy => by
        rw [Bool.eq_iff_iff]
        simp only [Function.comp_apply, bne_iff_ne, ne_eq]
        exact not_congr (he y (by simp [hy]) x (by simp))
    have hlen : (xs.filter ((· != f x) ∘ f)).length ≤ n := by
      have := List.length_filter_le ((· != f x) ∘ f) xs; simp at hl; omega
    obtain ⟨L, hL, hf, hg⟩ := dedupN_parallel n _ hlen fun y hy z hz =>
      he y (by simp [(List.mem_filter.mp hy).1]) z (by simp [(List.mem_filter.mp hz).1])
    refine ⟨x :: L, fun y hy => ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_filter.mp (hL y hy)).1
    · simp only [List.map_cons, dedupN, List.filter_map, hf]
    · simp only [List.map_cons, dedupN, List.filter_map, ← hfg, hg]

theorem dedup_parallel {α β : Type} [DecidableEq β] {f g : α → β} {l : List α}
    (he : ∀ x ∈ l, ∀ y ∈ l, f x = f y ↔ g x = g y) :
    ∃ L : List α, (∀ x ∈ L, x ∈ l) ∧ dedup (l.map f) = L.map f ∧ dedup (l.map g) = L.map g := by
  have := dedupN_parallel (f := f) (g := g) l.length l (Nat.le_refl _) he
  simpa [dedup] using this

/-- `MIN` of an expression constant on the group is its value. -/
theorem Measure.eval_min_const {e : Expr} {grp : Relation} {x : Row} (hx : x ∈ grp)
    (h : ∀ y ∈ grp, e.eval y = e.eval x) : ({ fn := .min, arg := e } : Measure).eval grp = e.eval x := by
  simp only [Measure.eval, Measure.inputs, Measure.kept, Bool.false_eq_true, ↓reduceIte]
  have hall : ∀ v ∈ (grp.map e.eval).filter (· != .null), v = e.eval x := fun v hv => by
    obtain ⟨⟨y, hy, rfl⟩, _⟩ := by simpa only [List.mem_filter, List.mem_map] using hv
    exact h y hy
  by_cases hv : e.eval x = .null
  · have : (grp.map e.eval).filter (· != .null) = [] :=
      List.filter_eq_nil_iff.2 fun v hv' => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv'
        simp [h y hy, hv]
    rw [this, hv]; rfl
  · have hm : e.eval x ∈ (grp.map e.eval).filter (· != .null) :=
      List.mem_filter.mpr ⟨List.mem_map_of_mem hx, by simpa using hv⟩
    obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hm)
    rw [has] at hall ⊢
    exact hall _ (pickFold_mem _ a as)

theorem FD.of_key {k : List Nat} {rows : Relation} (h : KeyOn k rows) (c : Nat) : FD k c rows :=
  fun _ hx _ hy he => by rw [KeyOn.eq_of_keyOf h hx hy he]

theorem FD.mono {k : List Nat} {c : Nat} {rows rows' : Relation} (hsub : ∀ x ∈ rows', x ∈ rows)
    (h : FD k c rows) : FD k c rows' := fun x hx y hy => h x (hsub x hx) y (hsub y hy)

theorem keyFds_sound {ks : List (List Nat)} {n : Nat} {rows : Relation} (h : ∀ k ∈ ks, KeyOn k rows) :
    ∀ fd ∈ keyFds ks n, FD fd.1 fd.2 rows := by
  intro fd hfd
  simp only [keyFds, List.mem_flatMap, List.mem_map] at hfd
  obtain ⟨k, hk, c, _, rfl⟩ := hfd
  exact FD.of_key (h k hk) c

/-- Columns that agree on every row determine each other. -/
theorem FD.of_eq {i j : Nat} {rows : Relation}
    (h : ∀ x ∈ rows, ∀ y ∈ rows, x.getD i .null = y.getD i .null → x.getD j .null = y.getD j .null) :
    FD [i] j rows := fun x hx y hy he => h x hx y hy (by simpa [keyOf] using he)

theorem eqFds_sound {c : Expr} {rows : Relation} (ht : ∀ x ∈ rows, (c.eval x).isTrue = true) :
    ∀ fd ∈ eqFds c.eqCols, FD fd.1 fd.2 rows := by
  intro fd hfd
  simp only [eqFds, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hfd
  obtain ⟨p, hp, rfl | rfl⟩ := hfd
  · exact FD.of_eq fun x hx y hy => (Expr.eqCols_det (ht x hx) (ht y hy) p hp).1
  · exact FD.of_eq fun x hx y hy => (Expr.eqCols_det (ht x hx) (ht y hy) p hp).2

/-- A dependency of the left rows holds on rows extending them. -/
theorem FD.left {rows A : Relation} {n : Nat} (hA : ∀ x ∈ A, x.length = n)
    (hrows : ∀ r ∈ rows, ∃ x ∈ A, ∃ w, r = x ++ w) {fd : List Nat × Nat}
    (hr : inRange n fd = true) (h : FD fd.1 fd.2 A) : FD fd.1 fd.2 rows := by
  simp only [inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
  intro r hr' s hs he
  obtain ⟨x, hx, w, rfl⟩ := hrows r hr'
  obtain ⟨y, hy, v, rfl⟩ := hrows s hs
  rw [keyOf_append_left (by rw [hA x hx]; exact hr.1), keyOf_append_left (by rw [hA y hy]; exact hr.1)] at he
  rw [getD_append_left' (by rw [hA x hx]; exact hr.2), getD_append_left' (by rw [hA y hy]; exact hr.2)]
  exact h x hx y hy he

/-- A dependency of the right rows holds, shifted, on rows extending them. -/
theorem FD.right {rows B : Relation} {n : Nat}
    (hrows : ∀ r ∈ rows, ∃ x w, x.length = n ∧ w ∈ B ∧ r = x ++ w) {fd : List Nat × Nat}
    (h : FD fd.1 fd.2 B) : FD (shiftFd n fd).1 (shiftFd n fd).2 rows := by
  intro r hr s hs he
  obtain ⟨x, w, hx, hw, rfl⟩ := hrows r hr
  obtain ⟨y, v, hy, hv, rfl⟩ := hrows s hs
  simp only [shiftFd] at he ⊢
  have e1 := keyOf_shift fd.1 x w
  have e2 := keyOf_shift fd.1 y v
  rw [hx] at e1; rw [hy] at e2
  rw [e1, e2] at he
  have g1 := getD_append_right' (x := x) (y := w) fd.2
  have g2 := getD_append_right' (x := y) (y := v) fd.2
  rw [hx] at g1; rw [hy] at g2
  rw [g1, g2]
  exact h w hw v hv he

theorem fdClosure_sound {fds : List (List Nat × Nat)} {rows : Relation}
    (h : ∀ fd ∈ fds, FD fd.1 fd.2 rows) {x y : Row} (hx : x ∈ rows) (hy : y ∈ rows) :
    ∀ (fuel : Nat) (X : List Nat), (∀ i ∈ X, x.getD i .null = y.getD i .null) →
      ∀ i ∈ fdClosure fds fuel X, x.getD i .null = y.getD i .null
  | 0, _, hX => hX
  | fuel + 1, X, hX => fdClosure_sound h hx hy fuel _ fun i hi => by
    rcases List.mem_append.mp hi with hi | hi
    · exact hX i hi
    · simp only [List.mem_map, List.mem_filter, List.all_eq_true, List.contains_iff_mem] at hi
      obtain ⟨fd, ⟨hfd, hsub⟩, rfl⟩ := hi
      exact h fd hfd x hx y hy (List.map_inj_left.mpr fun c hc => hX c (hsub c hc))

theorem emitPos?_spec {m : List Nat} {x p : Nat} (h : emitPos? m x = some p) : m[p]? = some x := by
  have := List.find?_some h
  simpa using this

theorem getD_emit {m : List Nat} {y : Row} {p x : Nat} (h : m[p]? = some x) :
    (m.map (y.getD · .null)).getD p .null = y.getD x .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

/-! ### Eager aggregation -/

theorem Expr.eval_congr_refsAll {p : Nat → Bool} {r r' : Row}
    (h : ∀ i, p i = true → r.getD i .null = r'.getD i .null) :
    ∀ {e : Expr}, e.refsAll p = true → e.eval r = e.eval r'
  | .lit _, _ => rfl
  | .field i, he => h i he
  | .un _ a, he => by simp only [eval, Expr.eval_congr_refsAll h (e := a) he]
  | .bin _ a b, he => by
    simp only [refsAll, Bool.and_eq_true] at he
    simp only [eval, Expr.eval_congr_refsAll h he.1, Expr.eval_congr_refsAll h he.2]
  | .ifThen c t e, he => by
    simp only [refsAll, Bool.and_eq_true] at he
    simp only [eval, Expr.eval_congr_refsAll h he.1.1, Expr.eval_congr_refsAll h he.1.2,
      Expr.eval_congr_refsAll h he.2]

theorem Expr.refsLt_subst {cols : List Expr} {m : Nat} (hc : ∀ c ∈ cols, c.refsLt m) :
    ∀ e : Expr, (e.subst cols).refsLt m
  | .lit _ => trivial
  | .field i => by
    simp only [subst, List.getD_eq_getElem?_getD]
    cases h : cols[i]? with
    | none => trivial
    | some c => exact hc c (List.mem_of_getElem? h)
  | .un _ a => Expr.refsLt_subst hc a
  | .bin _ a b => ⟨Expr.refsLt_subst hc a, Expr.refsLt_subst hc b⟩
  | .ifThen c t e => ⟨Expr.refsLt_subst hc c, Expr.refsLt_subst hc t, Expr.refsLt_subst hc e⟩

theorem gpos_spec {gs : List Expr} {c q : Nat} (h : gpos gs c = some q) : gs[q]? = some (.field c) := by
  simpa using List.find?_some h

theorem dedupN_fuel {α : Type} [DecidableEq α] : ∀ (n m : Nat) (l : List α), l.length ≤ n →
    l.length ≤ m → dedupN n l = dedupN m l
  | 0, m, [], _, _ => by cases m <;> rfl
  | 0, _, _ :: _, h, _ => by simp at h
  | _ + 1, 0, [], _, _ => rfl
  | _ + 1, 0, _ :: _, _, h => by simp at h
  | _ + 1, _ + 1, [], _, _ => rfl
  | n + 1, m + 1, x :: xs, h₁, h₂ => by
    have := List.length_filter_le (· != x) xs
    simp only [List.length_cons] at h₁ h₂
    simp only [dedupN]
    rw [dedupN_fuel n m _ (by omega) (by omega)]

theorem dedup_cons {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    dedup (x :: xs) = x :: dedup (xs.filter (· != x)) := by
  simp only [dedup, List.length_cons, dedupN]
  rw [dedupN_fuel _ _ _ (List.length_filter_le _ _) (Nat.le_refl _)]

theorem dedup_nil {α : Type} [DecidableEq α] : dedup ([] : List α) = [] := by simp [dedup, dedupN]

/-- Filtering by a predicate of the images commutes with `dedup`. -/
theorem dedup_filter_map {α β : Type} [DecidableEq β] {f : α → β} {p : α → Bool} {q : β → Bool} :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ x ∈ l, p x = q (f x)) →
      dedup ((l.filter p).map f) = (dedup (l.map f)).filter q
  | _, [], _, _ => by simp [dedup_nil]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, x :: xs, hl, hpq => by
    have hlen : (xs.filter ((· != f x) ∘ f)).length ≤ n := by
      have := List.length_filter_le ((· != f x) ∘ f) xs; simp at hl; omega
    have ih := dedup_filter_map n _ hlen fun y hy => hpq y (List.mem_cons_of_mem _ (List.mem_filter.mp hy).1)
    rw [List.map_cons, dedup_cons, List.filter_map]
    by_cases hp : p x
    · have hq : q (f x) = true := by rw [← hpq x (by simp)]; exact hp
      rw [List.filter_cons_of_pos hp, List.map_cons, dedup_cons, List.filter_cons_of_pos hq,
        List.filter_map, ← ih, List.filter_filter, List.filter_filter]
      congr 3
      exact List.filter_congr fun y _ => by simp [Bool.and_comm]
    · have hq : q (f x) = false := by rw [← hpq x (by simp)]; simpa using hp
      rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg (by simp [hq]), ← ih, List.filter_filter]
      congr 2
      refine List.filter_congr fun y hy => ?_
      by_cases hpy : p y
      · have hne : f y ≠ f x := fun he => by
          have h1 := hpq y (by simp [hy]); have h2 := hpq x (by simp)
          rw [he] at h1; simp_all
        simp [hpy, hne]
      · simp [hpy]

/-- An aggregate over the rows of its groups that pass `p`, when `p` is the
same on a group, is the aggregate's rows that pass `P`. -/
theorem aggregateEval_filter {gs : List Expr} {ms : List Measure} {A : Relation}
    {p P : Row → Bool} (hgs : gs ≠ [])
    (hp : ∀ x ∈ A, ∀ y ∈ A, groupKey gs x = groupKey gs y → p x = p y)
    (hP : ∀ x ∈ A,
      P (groupKey gs x ++ ms.map (·.eval (groupRows gs A (groupKey gs x)))) = p x) :
    aggregateEval gs ms (A.filter p) = (aggregateEval gs ms A).filter P := by
  let q : Row → Bool := fun k => A.any fun x => groupKey gs x == k && p x
  have hq : ∀ x ∈ A, p x = q (groupKey gs x) := fun x hx => by
    cases hpx : p x
    · symm
      simp only [q, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and, Bool.not_eq_true]
      intro y hy he; rw [hp y hy x hx he]; exact hpx
    · symm
      exact List.any_eq_true.mpr ⟨x, hx, by simp [hpx]⟩
  have hgsE : gs.isEmpty = false := by simpa using hgs
  unfold aggregateEval
  simp only [hgsE, Bool.false_eq_true, ↓reduceIte]
  rw [dedup_filter_map _ _ (Nat.le_refl _) hq, List.filter_map]
  have hk : ∀ k ∈ dedup (A.map (groupKey gs)), ∃ x ∈ A, k = groupKey gs x := fun k hk => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk); exact ⟨x, hx, rfl⟩
  rw [List.filter_congr (p := q) (q := P ∘ fun k => k ++ ms.map (·.eval (groupRows gs A k)))
    fun k hk' => by
      obtain ⟨x, hx, rfl⟩ := hk k hk'
      simp only [Function.comp_apply, hP x hx, hq x hx]]
  refine List.map_congr_left fun k hk' => ?_
  obtain ⟨hk₁, hk₂⟩ := List.mem_filter.mp hk'
  obtain ⟨x, hx, rfl⟩ := hk k hk₁
  have hgr : groupRows gs (A.filter p) (groupKey gs x) = groupRows gs A (groupKey gs x) := by
    unfold groupRows
    rw [List.filter_filter]
    refine List.filter_congr fun y hy => ?_
    by_cases he : groupKey gs y = groupKey gs x
    · have hpx : p x = true := by simpa [Function.comp_apply, hP x hx] using hk₂
      simp [he, hp y hy x hx he, hpx]
    · simp [he]
  rw [hgr]

/-- Each left row with at most one partner. -/
theorem flatMap_opt {A : Relation} {M : Row → Relation}
    (h : ∀ x ∈ A, M x = [] ∨ ∃ w, M x = [x ++ w]) :
    A.flatMap M = (A.filter fun x => !(M x).isEmpty).map (fun x => (M x).headD x) ∧
      ∀ x ∈ A, ∃ w, (M x).headD x = x ++ w := by
  refine ⟨?_, fun x hx => ?_⟩
  · induction A with
    | nil => rfl
    | cons x A ih =>
      rw [List.flatMap_cons, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
      rcases h x (by simp) with hm | ⟨w, hm⟩ <;> simp [hm]
  · rcases h x hx with hm | ⟨w, hm⟩
    · exact ⟨[], by simp [hm]⟩
    · exact ⟨w, by simp [hm]⟩

section
variable {cat : Catalog} (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
  (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
  (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
  (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {R : ForeignKeys} (hR : R.Hold cat)
include hcat hA hF hK hR

omit hA hF hR in
theorem Rel.fds_sound : ∀ {r : Rel}, r.WF cat → ∀ fd ∈ r.fds cat K, FD fd.1 fd.2 (r.eval cat)
  | .read t, _ => keyFds_sound (hK t)
  | .aggregate _ gs ms, _ => keyFds_sound fun k hk => by
      simp only [List.mem_singleton] at hk; subst hk; exact aggregateEval_key gs ms _
  | .values _ _, _ | .unionAll _ _, _ => fun _ h => by simp [fds] at h
  | .filter r c, hwf => fun fd hfd => by
      simp only [fds, List.mem_append] at hfd
      rcases hfd with h | h
      · exact (fds_sound hwf.1 fd h).mono fun x hx => (List.mem_filter.mp hx).1
      · exact eqFds_sound (fun x hx => (List.mem_filter.mp hx).2) fd h
  | .fetch r _ _, hwf => fun fd hfd => by
      simp only [fds] at hfd
      refine (fds_sound (r := r) hwf fd hfd).mono fun x hx => ?_
      simp only [eval] at hx
      split at hx
      · exact List.mem_of_mem_drop hx
      · exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  | .orderBy r _, hwf => fun fd hfd => by
      simp only [fds] at hfd
      exact (fds_sound hwf.1 fd hfd).mono fun x hx => by simpa [eval, List.mem_mergeSort] using hx
  | .distinct r, hwf => fun fd hfd => by
      simp only [fds] at hfd
      exact (fds_sound (r := r) hwf fd hfd).mono fun x hx => by simpa [eval, mem_dedup] using hx
  | .semi r _ _ _, hwf => fun fd hfd => by
      simp only [fds] at hfd
      exact (fds_sound hwf.1 fd hfd).mono fun x hx => (List.mem_filter.mp hx).1
  | .window r _ _ _, hwf => fun fd hfd => by
      simp only [fds, List.mem_filter] at hfd
      refine FD.left (eval_arity hcat hwf.1) (fun row hrow => ?_) hfd.2 (fds_sound hwf.1 fd hfd.1)
      obtain ⟨_, y, _, _, hy, rfl⟩ := mem_windowEval hrow
      exact ⟨y, hy, _, rfl⟩
  | .project r es, hwf => fun fd hfd => by
      simp only [fds, List.mem_append, List.mem_filter] at hfd
      rcases hfd with h | h
      · refine FD.left (eval_arity hcat hwf.1) (fun row hrow => ?_) h.2 (fds_sound hwf.1 fd h.1)
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hrow
        exact ⟨y, hy, _, rfl⟩
      · simp only [copyFds, List.mem_flatMap] at h
        obtain ⟨⟨e, q⟩, hq, h⟩ := h
        have heq := List.mem_zipIdx_iff_getElem?.mp hq
        cases e with
        | field j =>
          simp only at h
          split at h
          · rename_i hj
            -- The copy and its column agree on every row.
            have hc : ∀ row ∈ (Rel.project r es).eval cat,
                row.getD (r.arity cat + q) .null = row.getD j .null := fun row hrow => by
              obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hrow
              have hl := eval_arity hcat hwf.1 y hy
              rw [← hl, getD_append_right', getD_append_left' (by omega)]
              simp [List.getD_eq_getElem?_getD, List.getElem?_map, heq, Expr.eval]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact FD.of_eq fun x hx y hy he => by rw [hc x hx, hc y hy]; exact he
            · exact FD.of_eq fun x hx y hy he => by rw [← hc x hx, ← hc y hy]; exact he
          · simp at h
        | _ => simp at h
  | .emit r m, hwf => fun fd hfd => by
      simp only [fds, List.mem_flatMap] at hfd
      obtain ⟨fd₀, h₀, hfd⟩ := hfd
      have ih := fds_sound hwf.1 fd₀ h₀
      unfold emitFd at hfd
      split at hfd
      · rename_i hall
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hfd
        have hp' : m[p]? = some fd₀.2 := by simpa using (List.mem_filter.mp hp).2
        have hk : ∀ y : Row, keyOf (fd₀.1.map fun x => (emitPos? m x).getD 0)
            (m.map (y.getD · .null)) = keyOf fd₀.1 y := fun y => by
          simp only [keyOf, List.map_map]
          refine List.map_congr_left fun x hx => ?_
          have := List.all_eq_true.mp hall x hx
          obtain ⟨p', hp''⟩ := Option.isSome_iff_exists.mp this
          simp only [Function.comp_apply, hp'', Option.getD_some]
          exact getD_emit (emitPos?_spec hp'')
        intro o ho o' ho' he
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho
        obtain ⟨y', hy', rfl⟩ := List.mem_map.mp ho'
        rw [hk, hk] at he
        rw [getD_emit hp', getD_emit hp']
        exact ih y hy y' hy' he
      · simp at hfd
  | .cross a b, hwf => fun fd hfd => by
      simp only [fds, List.mem_append, List.mem_filter, List.mem_map] at hfd
      rcases hfd with h | ⟨fd₀, h₀, rfl⟩
      · refine FD.left (eval_arity hcat hwf.1) (fun row hrow => ?_) h.2 (fds_sound hwf.1 fd h.1)
        obtain ⟨x, hx, y, _, rfl⟩ := mem_crossRows.mp hrow
        exact ⟨x, hx, y, rfl⟩
      · refine FD.right (fun row hrow => ?_) (fds_sound hwf.2 fd₀ h₀)
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp hrow
        exact ⟨x, y, eval_arity hcat hwf.1 x hx, hy, rfl⟩
  | .join a b .inner on, hwf => fun fd hfd => by
      simp only [fds, List.mem_append, List.mem_filter, List.mem_map] at hfd
      rcases hfd with (h | ⟨fd₀, h₀, rfl⟩) | h
      · refine FD.left (eval_arity hcat hwf.1) (fun row hrow => ?_) h.2 (fds_sound hwf.1 fd h.1)
        obtain ⟨x, hx, y, _, rfl⟩ := mem_crossRows.mp (List.mem_filter.mp hrow).1
        exact ⟨x, hx, y, rfl⟩
      · refine FD.right (fun row hrow => ?_) (fds_sound hwf.2.1 fd₀ h₀)
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp (List.mem_filter.mp hrow).1
        exact ⟨x, y, eval_arity hcat hwf.1 x hx, hy, rfl⟩
      · exact eqFds_sound (fun x hx => (List.mem_filter.mp hx).2) fd h
  | .join a b .left on, hwf => fun fd hfd => by
      simp only [fds, List.mem_filter] at hfd
      refine FD.left (eval_arity hcat hwf.1) (fun row hrow => ?_) hfd.2 (fds_sound hwf.1 fd hfd.1)
      simp only [eval, List.mem_flatMap] at hrow
      obtain ⟨x, hx, hrow⟩ := hrow
      unfold leftJoinRow at hrow
      simp only [] at hrow
      split at hrow
      · exact ⟨x, hx, _, List.mem_singleton.mp hrow⟩
      · obtain ⟨⟨y, _, rfl⟩, _⟩ := by simpa only [List.mem_filter, List.mem_map] using hrow
        exact ⟨x, hx, y, rfl⟩

omit hR in
theorem Rel.fdAgg_sound {r s : Rel} {gs : List Expr} {ms : List Measure} {name : String}
    (hwf : (Rel.aggregate r gs ms).WF cat) (h : r.fdAgg cat A F K gs ms = some (name, s)) :
    Same cat (.aggregate r gs ms) s := by
  have hfds : ∀ fd ∈ r.fds cat K ++ keyFds (r.keys cat A F K) (r.arity cat),
      FD fd.1 fd.2 (r.eval cat) := fun fd hfd => by
    rcases List.mem_append.mp hfd with h | h
    · exact fds_sound hcat hK hwf.1 fd h
    · exact keyFds_sound (fun k hk => keys_sound hcat hA hF hK hwf.1 k hk) fd h
  unfold Rel.fdAgg at h
  simp only at h
  generalize r.fds cat K ++ keyFds (r.keys cat A F K) (r.arity cat) = fds at h hfds
  generalize keepCols fds gs = qs at h
  generalize hD : (List.range gs.length).filter (!qs.contains ·) = drops at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
      at hc
    obtain ⟨⟨hqs, hdr⟩, hdet⟩ := hc
    have hmemD : ∀ q, q ∈ drops ↔ q < gs.length ∧ q ∉ qs := fun q => by
      rw [← hD]; simp
    have gd_mem : ∀ q, q < gs.length → gAt gs q ∈ gs := fun q hq => by
      simp only [gAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
      exact List.getElem_mem hq
    have gd_ge : ∀ q, ¬ q < gs.length → gAt gs q = .lit .null := fun q hq => by
      simp [gAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : gs.length ≤ q)]
    have gd_refs : ∀ q, (gAt gs q).refsLt (r.arity cat) := fun q => by
      by_cases hq : q < gs.length
      · exact hwf.2.1 _ (gd_mem q hq)
      · rw [gd_ge q hq]; trivial
    have hgs_q : ∀ x y : Row, groupKey gs x = groupKey gs y → ∀ q, (gAt gs q).eval x = (gAt gs q).eval y :=
      fun x y he q => by
        by_cases hq : q < gs.length
        · exact List.map_inj_left.mp he _ (gd_mem q hq)
        · rw [gd_ge q hq]; rfl
    have hcore : ∀ x : Row, groupKey (qs.map (gAt gs)) x = qs.map fun q => (gAt gs q).eval x := fun x => by
      simp [groupKey, List.map_map, Function.comp_def]
    -- The kept columns determine the dropped ones.
    have hiff : ∀ x ∈ r.eval cat, ∀ y ∈ r.eval cat,
        groupKey gs x = groupKey gs y ↔ groupKey (qs.map (gAt gs)) x = groupKey (qs.map (gAt gs)) y := fun x hx y hy => by
      constructor
      · intro he
        rw [hcore, hcore]
        exact List.map_congr_left fun q _ => hgs_q x y he q
      · intro he
        rw [hcore, hcore] at he
        have hq := List.map_inj_left.mp he
        have hf : ∀ j ∈ fieldsOf (qs.map (gAt gs)), x.getD j .null = y.getD j .null := fun j hj => by
          simp only [fieldsOf, List.mem_filterMap] at hj
          obtain ⟨e, he', hej⟩ := hj
          obtain ⟨q, hq', rfl⟩ := List.mem_map.mp he'
          have := hq q hq'
          cases hg : gAt gs q <;> simp_all [Expr.eval]
        have hcl := fdClosure_sound hfds hx hy (fds.length + 1) _ hf
        refine List.map_inj_left.mpr fun g hg => ?_
        obtain ⟨q, hq', rfl⟩ := List.mem_iff_getElem.mp hg
        have hgd : gAt gs q = gs[q] := by
          simp [gAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']
        rw [← hgd]
        by_cases hk : q ∈ qs
        · exact hq q hk
        · have hd := hdet q ((hmemD q).mpr ⟨hq', hk⟩)
          unfold determinedBy at hd
          cases hg : gAt gs q with
          | field c =>
            rw [hg] at hd
            simpa [Expr.eval] using hcl c (List.contains_iff_mem.mp hd)
          | _ => rw [hg] at hd; simp at hd
    obtain ⟨L, hL, hLg, hLc⟩ := dedup_parallel hiff
    have hgsne : gs ≠ [] := by
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hdr
      intro h0; have := ((hmemD q).mp hq).1; simp [h0] at this
    have hcorene : (qs.map (gAt gs)) ≠ [] := by simpa using hqs
    refine ⟨⟨⟨hwf.1, ?_, ?_⟩, ?_⟩, by simp [fdEmit, arity], ?_⟩
    · intro e he
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
      exact gd_refs q
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hwf.2.2 m hm
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
        exact ⟨gd_refs q, fun c hc => by simp [minOf] at hc⟩
    · intro i hi
      simp only [fdEmit, List.mem_append, List.mem_map, List.mem_range] at hi
      simp only [arity, List.length_append, List.length_map]
      rcases hi with ⟨q, hq, rfl⟩ | ⟨j, hj, rfl⟩
      · by_cases hk : q ∈ qs
        · simp only [List.contains_iff_mem, hk, ↓reduceIte]
          have := List.idxOf_lt_length_of_mem hk; omega
        · have hd : q ∈ drops := (hmemD q).mpr ⟨hq, hk⟩
          simp only [List.contains_iff_mem, hk, ↓reduceIte]
          have := List.idxOf_lt_length_of_mem hd; omega
      · omega
    · simp only [eval, aggregateEval, List.isEmpty_iff, hgsne, hcorene, ↓reduceIte, hLg, hLc,
        List.map_map]
      refine List.map_congr_left fun x hx => ?_
      have hxr := hL x hx
      have hG : groupRows (qs.map (gAt gs)) (r.eval cat) (groupKey (qs.map (gAt gs)) x) =
          groupRows gs (r.eval cat) (groupKey gs x) :=
        List.filter_congr fun y hy => by
          rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact (hiff y hy x hxr).symm
      simp only [Function.comp_apply, hG]
      generalize hGdef : groupRows gs (r.eval cat) (groupKey gs x) = G
      have hxG : x ∈ G := by rw [← hGdef]; exact List.mem_filter.mpr ⟨hxr, by simp⟩
      have hGc : ∀ y ∈ G, ∀ q, (gAt gs q).eval y = (gAt gs q).eval x := fun y hy q => by
        rw [← hGdef] at hy
        exact hgs_q y x (by simpa using (List.mem_filter.mp hy).2) q
      have hlc : (groupKey (qs.map (gAt gs)) x).length = qs.length := by simp [groupKey]
      have hlg : (groupKey gs x).length = gs.length := by simp [groupKey]
      simp only [fdEmit, List.map_append]
      congr 1
      · conv => rhs; rw [← keyOf_range hlg]
        simp only [keyOf, List.map_map]
        refine List.map_congr_left fun q hq => ?_
        have hq' := List.mem_range.mp hq
        have hgq : (groupKey gs x).getD q .null = (gAt gs q).eval x := by
          simp [groupKey, gAt, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hq']
        simp only [Function.comp_apply, hgq]
        by_cases hk : q ∈ qs
        · simp only [List.contains_iff_mem, hk, ↓reduceIte]
          have hi := List.idxOf_lt_length_of_mem hk
          rw [getD_append_left' (by omega), hcore]
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
            List.getElem_idxOf hi]
        · have hd : q ∈ drops := (hmemD q).mpr ⟨hq', hk⟩
          have hi := List.idxOf_lt_length_of_mem hd
          simp only [List.contains_iff_mem, hk, ↓reduceIte]
          rw [show qs.length + ms.length + drops.idxOf q =
              (groupKey (qs.map (gAt gs)) x).length + ((ms.map (·.eval G)).length + drops.idxOf q) by
                simp [hlc]; omega,
            getD_append_right', getD_append_right']
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
            List.getElem_idxOf hi, Option.map_some, Option.getD_some]
          exact Measure.eval_min_const hxG fun y hy => hGc y hy q
      · conv => rhs; rw [← keyOf_range (x := ms.map (·.eval G)) (n := ms.length) (by simp)]
        simp only [keyOf, List.map_map]
        refine List.map_congr_left fun j hj => ?_
        have hj' := List.mem_range.mp hj
        simp only [Function.comp_apply]
        rw [← hlc, getD_append_right', getD_append_left' (by simpa using hj')]
  · simp at h

omit hR in
/-- With the condition on a key of the right side, each left row has at most
one partner. -/
theorem Rel.partners_le_one {a b : Rel} {on : Expr} (ha : a.WF cat) (hb : b.WF cat)
    (hk : (b.keys cat A F K).any (determines on (a.arity cat)) = true) :
    ∀ x ∈ a.eval cat, ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) = [] ∨
      ∃ z, ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) = [x ++ z] := by
  intro x hx
  obtain ⟨kb, hkb, hd⟩ := List.any_eq_true.mp hk
  have hkB := keys_sound hcat hA hF hK hb kb hkb
  have hm := match_block (on := on) (eval_arity hcat ha x hx) hkB
  have hnil : kb.filter (fun c => !determinedCol on (a.arity cat) c) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by
      unfold determines at hd
      simp [List.all_eq_true.mp hd c hc]
  rw [hnil] at hm
  rcases eq_nil_or_singleton (hm.imp fun h => h rfl) with he | ⟨y, hy⟩
  · exact .inl he
  · have hm' : y ∈ ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) := by
      rw [hy]; simp
    obtain ⟨⟨z, _, rfl⟩, _⟩ := by simpa only [List.mem_filter, List.mem_map] using hm'
    exact .inr ⟨z, hy⟩

omit hR in
theorem Rel.eagerAgg_sound {r s : Rel} {gs : List Expr} {ms : List Measure} {name : String}
    (hwf : (Rel.aggregate r gs ms).WF cat) (h : r.eagerAgg cat A F K gs ms = some (name, s)) :
    Same cat (.aggregate r gs ms) s := by
  cases r with
  | join a b ty on =>
    cases ty with
    | left => simp [eagerAgg] at h
    | inner =>
    simp only [eagerAgg] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
        Expr.refsLtb_iff] at hc
      obtain ⟨⟨⟨⟨hgs, hgl⟩, hml⟩, hkey⟩, hrefs⟩ := hc
      have hjw : (Rel.join a b .inner on).WF cat := hwf.1
      have ha := hjw.1
      have hb := hjw.2.1
      generalize hn : a.arity cat = n at *
      generalize hkk : b.arity cat = k at *
      generalize hout : gs.length + ms.length = out
      have hAl : ∀ x ∈ a.eval cat, x.length = n := fun x hx => hn ▸ eval_arity hcat ha x hx
      have hBl : ∀ z ∈ b.eval cat, z.length = k := fun z hz => hkk ▸ eval_arity hcat hb z hz
      let M : Row → Relation := fun x =>
        ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue)
      let on' := on.subst (eagerCols n gs out k)
      -- Rows that agree on the grouping columns match the same right rows.
      have hon : ∀ x ∈ a.eval cat, ∀ y ∈ a.eval cat, groupKey gs x = groupKey gs y →
          ∀ z, on.eval (x ++ z) = on.eval (y ++ z) := fun x hx y hy he z => by
        refine Expr.eval_congr_refsAll (fun i hi => ?_) hrefs
        by_cases hni : n ≤ i
        · obtain ⟨d, rfl⟩ : ∃ d, i = n + d := ⟨i - n, by omega⟩
          have e1 := getD_append_right' (x := x) (y := z) d
          have e2 := getD_append_right' (x := y) (y := z) d
          rw [hAl x hx] at e1; rw [hAl y hy] at e2
          rw [e1, e2]
        · simp only [hni, decide_false, Bool.false_or, Option.isSome_iff_exists] at hi
          obtain ⟨q, hq⟩ := hi
          have hg := gpos_spec hq
          have hq' : q < gs.length := (List.getElem?_eq_some_iff.mp hg).1
          have := List.map_inj_left.mp he gs[q] (List.getElem_mem hq')
          have hgq : gs[q] = .field i := (List.getElem?_eq_some_iff.mp hg).2
          rw [hgq] at this
          rw [getD_append_left' (by rw [hAl x hx]; omega), getD_append_left' (by rw [hAl y hy]; omega)]
          simpa [Expr.eval] using this
      -- The rewritten condition on a group row is the condition on its rows.
      have hsub : ∀ x ∈ a.eval cat, ∀ v : Row, v.length = ms.length → ∀ z ∈ b.eval cat,
          on'.eval (groupKey gs x ++ v ++ z) = on.eval (x ++ z) := fun x hx v hv z hz => by
        simp only [on', Expr.eval_subst]
        refine Expr.eval_congr_refsAll (fun i hi => ?_) hrefs
        rw [getD_map_eval]
        have hgl' : (groupKey gs x).length = gs.length := by simp [groupKey]
        have hrow : (groupKey gs x ++ v).length = out := by simp [hgl', hv, ← hout]
        by_cases hni : n ≤ i
        · obtain ⟨d, rfl⟩ : ∃ d, i = n + d := ⟨i - n, by omega⟩
          have e1 := getD_append_right' (x := x) (y := z) d
          rw [hAl x hx] at e1
          rw [e1]
          by_cases hd : d < k
          · have : (eagerCols n gs out k).getD (n + d) (.lit .null) = .field (out + d) := by
              simp [eagerCols, List.getD_eq_getElem?_getD, hd]
            rw [this]
            have e2 := getD_append_right' (x := groupKey gs x ++ v) (y := z) d
            rw [hrow] at e2
            simpa [Expr.eval] using e2
          · have : (eagerCols n gs out k).getD (n + d) (.lit .null) = .lit .null := by
              simp [eagerCols, List.getD_eq_getElem?_getD, List.getElem?_append_right,
                List.getElem?_eq_none (by simp; omega : ((List.range k).map fun j => Expr.field (out + j)).length ≤ d)]
            rw [this]
            simp [Expr.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hBl z hz]; omega : z.length ≤ d)]
        · simp only [hni, decide_false, Bool.false_or, Option.isSome_iff_exists] at hi
          obtain ⟨q, hq⟩ := hi
          have hg := gpos_spec hq
          have hq' : q < gs.length := (List.getElem?_eq_some_iff.mp hg).1
          have hgq : gs[q] = .field i := (List.getElem?_eq_some_iff.mp hg).2
          have : (eagerCols n gs out k).getD i (.lit .null) = .field q := by
            simp [eagerCols, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega : i < ((List.range n).map _).length), hq, show i < n by omega]
          rw [this, getD_append_left' (by rw [hAl x hx]; omega)]
          simp only [Expr.eval]
          rw [List.append_assoc, getD_append_left' (by rw [hgl']; exact hq')]
          simp [groupKey, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq', hgq,
            Expr.eval]
      -- A group row has a partner when its rows do.
      have hfilt : ∀ x ∈ a.eval cat, ∀ v : Row, v.length = ms.length →
          ((b.eval cat).map (groupKey gs x ++ v ++ ·)).filter (fun row => (on'.eval row).isTrue) =
            ((b.eval cat).filter fun z => (on.eval (x ++ z)).isTrue).map (groupKey gs x ++ v ++ ·) :=
          fun x hx v hv => by
        rw [List.filter_map]
        congr 1
        exact List.filter_congr fun z hz => by simp only [Function.comp_apply]; rw [hsub x hx v hv z hz]
      have hM : ∀ x, M x = ((b.eval cat).filter fun z => (on.eval (x ++ z)).isTrue).map (x ++ ·) :=
        fun x => by simp only [M, List.filter_map, Function.comp_def]
      have hle := partners_le_one hcat hA hF hK ha hb (hn ▸ hkey)
      obtain ⟨hJ, hg⟩ := flatMap_opt (A := a.eval cat) (M := M) hle
      let p : Row → Bool := fun x => !(M x).isEmpty
      let P : Row → Bool := fun row =>
        !(((b.eval cat).map (row ++ ·)).filter fun r => (on'.eval r).isTrue).isEmpty
      have hP : ∀ x ∈ a.eval cat, ∀ v : Row, v.length = ms.length → P (groupKey gs x ++ v) = p x :=
        fun x hx v hv => by simp only [P, p, hfilt x hx v hv, hM x, List.isEmpty_map]
      have hlen : ∀ row ∈ aggregateEval gs ms (a.eval cat), ∃ x ∈ a.eval cat, ∃ v : Row,
          v.length = ms.length ∧ row = groupKey gs x ++ v := fun row hr => by
        obtain ⟨kk, grp, rfl, -, hk'⟩ := mem_aggregateEval hr
        rcases hk' with ⟨rfl, -⟩ | ⟨x, hx, rfl⟩
        · exact absurd rfl hgs
        · exact ⟨x, hx, _, by simp, rfl⟩
      refine ⟨⟨⟨⟨ha, fun g hg' => hn ▸ hgl g hg', fun m hm => ?_⟩, hb, ?_⟩, ?_⟩, ?_, ?_⟩
      · exact ⟨hn ▸ hml m hm m.arg (by simp [Measure.exprs]),
          fun c hc => hn ▸ hml m hm c (by simp [Measure.exprs]; exact .inr hc)⟩
      · simp only [arity, hkk, hout]
        refine Expr.refsLt_subst (fun c hc => ?_) on
        simp only [eagerCols, List.mem_append, List.mem_map, List.mem_range] at hc
        rcases hc with ⟨i, _, rfl⟩ | ⟨j, hj, rfl⟩
        · cases hq : gpos gs i with
          | none => trivial
          | some q =>
            have := (List.getElem?_eq_some_iff.mp (gpos_spec hq)).1
            show q < out + k; omega
        · show out + j < out + k; omega
      · intro i hi
        simp only [arity, hkk, hout, List.mem_range] at hi ⊢; omega
      · simp [arity, hout]
      · -- Both sides are the groups with a partner.
        have hJe : (Rel.join a b .inner on).eval cat = (a.eval cat).flatMap M := by
          simp only [eval, crossRows, List.filter_flatMap]; rfl
        have orig : aggregateEval gs ms ((Rel.join a b .inner on).eval cat) =
            (aggregateEval gs ms (a.eval cat)).filter P := by
          rw [hJe, hJ, aggregateEval_map (g := fun x => (M x).headD x)
            (fun x hx e he => by
              obtain ⟨w, hw⟩ := hg x (List.mem_filter.mp hx).1
              rw [hw]; exact Expr.eval_append w (hn ▸ hgl e he) (hAl x (List.mem_filter.mp hx).1))
            (fun x hx m hm e he => by
              obtain ⟨w, hw⟩ := hg x (List.mem_filter.mp hx).1
              rw [hw]; exact Expr.eval_append w (hn ▸ hml m hm e he) (hAl x (List.mem_filter.mp hx).1))]
          exact aggregateEval_filter (P := P) hgs
            (fun x hx y hy he => by
              simp only [hM x, hM y, List.isEmpty_map]
              congr 2
              exact List.filter_congr fun z _ => by rw [hon x hx y hy he z])
            (fun x hx => hP x hx _ (by simp))
        have hR : ∀ row ∈ aggregateEval gs ms (a.eval cat),
            ((b.eval cat).map (row ++ ·)).filter (fun r => (on'.eval r).isTrue) = [] ∨
              ∃ w, ((b.eval cat).map (row ++ ·)).filter (fun r => (on'.eval r).isTrue) = [row ++ w] :=
            fun row hr => by
          obtain ⟨x, hx, v, hv, rfl⟩ := hlen row hr
          rw [hfilt x hx v hv]
          rcases hle x hx with he | ⟨z, hz⟩
          · left
            have he' : M x = [] := he
            rw [hM x] at he'; simpa using he'
          · right
            have hz₀ : M x = [x ++ z] := hz
            rw [hM x] at hz₀
            obtain ⟨z', hz'⟩ : ∃ z', (b.eval cat).filter (fun z => (on.eval (x ++ z)).isTrue) = [z'] := by
              cases hf : (b.eval cat).filter (fun z => (on.eval (x ++ z)).isTrue) with
              | nil => rw [hf] at hz₀; simp at hz₀
              | cons z₁ zs =>
                rw [hf] at hz₀
                cases zs with
                | nil => exact ⟨z₁, rfl⟩
                | cons => simp at hz₀
            exact ⟨z', by rw [hz']; simp⟩
        obtain ⟨hJ', hg'⟩ := flatMap_opt hR
        have new : (Rel.emit (.join (.aggregate a gs ms) b .inner on') (List.range out)).eval cat =
            (aggregateEval gs ms (a.eval cat)).filter P := by
          simp only [eval, crossRows, List.filter_flatMap]
          rw [hJ', List.map_map]
          conv => rhs; rw [← List.map_id ((aggregateEval gs ms (a.eval cat)).filter P)]
          refine List.map_congr_left fun row hrow => ?_
          have hmem := (List.mem_filter.mp hrow).1
          obtain ⟨w, hw⟩ := hg' row hmem
          have hrl : row.length = out := by rw [← hout]; exact aggregateEval_length hmem
          simp only [Function.comp_apply, hw, id]
          change keyOf (List.range out) (row ++ w) = row
          rw [keyOf_append_left (by simp [hrl]), keyOf_range hrl]
        exact new.trans orig.symm
    · simp at h
  | _ => simp [eagerAgg] at h

theorem Rel.fkMatch_sound {a b : Rel} {on : Expr} (hm : Rel.fkMatch cat A F K R a b on = true)
    (ha : a.WF cat) (hb : b.WF cat) :
    ∀ x ∈ a.eval cat, ∃ z ∈ b.eval cat, (on.eval (x ++ z)).isTrue = true := by
  intro x hx
  unfold Rel.fkMatch at hm
  split at hm
  · rename_i i j hij
    split at hm
    · rename_i t c s p ho hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hm
      obtain ⟨hfk, hnn⟩ := hm
      have hT := keyedWindows_sound hcat hA hF hK
      have hmem := aeval_sound hcat hA hF hT ha x hx i
      have hxn : x.getD i .null ≠ .null := fun h0 => by
        rw [h0] at hmem
        simp only [AVal.Mem, List.getD_eq_getElem?_getD] at hmem hnn
        simp [hmem] at hnn
      obtain ⟨y, hy, hyx⟩ := origin_sound hcat ha ho x hx hxn
      obtain ⟨w, hw, hwy⟩ := hR t _ hfk y hy (by rw [hyx]; exact hxn)
      obtain ⟨z, hz, hzw⟩ := cover_sound hcat hb hc w hw (by rw [hwy, hyx]; exact hxn)
      exact ⟨z, hz, eqPair_sound hij (eval_arity hcat ha x hx) (by rw [hzw, hwy, hyx]) hxn⟩
    · simp at hm
  · simp at hm

theorem Rel.joinElim_sound {r a : Rel} {name : String} {k : Nat} (hwf : r.WF cat)
    (h : r.joinElim cat A F K R = some (name, a, k)) :
    a.WF cat ∧ r.arity cat = a.arity cat + k ∧
      ∃ g : Row → Row, r.eval cat = (a.eval cat).map g ∧ ∀ x ∈ a.eval cat, ∃ w, g x = x ++ w := by
  cases r with
  | join a' b ty on =>
    simp only [joinElim] at h
    split at h
    · rename_i hk
      obtain ⟨kb, hkb, hd⟩ := List.any_eq_true.mp hk
      have hkB := keys_sound hcat hA hF hK hwf.2.1 kb hkb
      have hle : ∀ x ∈ a'.eval cat,
          ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) = [] ∨
            ∃ z, ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) = [x ++ z] :=
          fun x hx => by
        have hb := match_block (on := on) (eval_arity hcat hwf.1 x hx) hkB
        have hnil : kb.filter (fun c => !determinedCol on (a'.arity cat) c) = [] :=
          List.filter_eq_nil_iff.2 fun c hc => by
            unfold determines at hd
            simp [List.all_eq_true.mp hd c hc]
        rw [hnil] at hb
        rcases eq_nil_or_singleton (hb.imp fun h => h rfl) with he | ⟨y, hy⟩
        · exact .inl he
        · have hm : y ∈ ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) := by
            rw [hy]; simp
          obtain ⟨⟨z, _, rfl⟩, _⟩ := by simpa only [List.mem_filter, List.mem_map] using hm
          exact .inr ⟨z, hy⟩
      cases ty with
      | inner =>
        simp only at h
        split at h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl, rfl⟩ := h
          refine ⟨hwf.1, rfl, ?_⟩
          have hall := fkMatch_sound hcat hA hF hK hR hm hwf.1 hwf.2.1
          have hG : ∀ x ∈ a'.eval cat, ∃ w,
              ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) = [x ++ w] :=
              fun x hx => by
            rcases hle x hx with he | hy
            · obtain ⟨z, hz, ht⟩ := hall x hx
              have hm : x ++ z ∈ ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue) :=
                List.mem_filter.mpr ⟨List.mem_map.mpr ⟨z, hz, rfl⟩, ht⟩
              rw [he] at hm; simp at hm
            · exact hy
          obtain ⟨he, hg⟩ := flatMap_single hG
          refine ⟨_, ?_, hg⟩
          simp only [eval, crossRows, List.filter_flatMap]
          exact he
        · simp at h
      | left =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        refine ⟨hwf.1, rfl, ?_⟩
        have hG : ∀ x ∈ a'.eval cat, ∃ w, leftJoinRow on (b.arity cat) (b.eval cat) x = [x ++ w] :=
          fun x hx => by
            rcases hle x hx with he | ⟨z, hz⟩
            · exact ⟨List.replicate (b.arity cat) .null, by simp [leftJoinRow, he]⟩
            · exact ⟨z, by simp [leftJoinRow, hz]⟩
        obtain ⟨he, hg⟩ := flatMap_single hG
        exact ⟨_, he, hg⟩
    · simp at h
  | _ => simp [joinElim] at h

theorem Rel.rule_sound {r s : Rel} {name : String} (hwf : r.WF cat)
    (h : r.rule cat A F K R = some (name, s)) : Same cat r s := by
  have keys := fun {r : Rel} (hr : r.WF cat) => keys_sound hcat hA hF hK hr
  have cond : ∀ {r : Rel}, r.WF cat → ∀ c : Expr, ∀ row ∈ r.eval cat,
      (r.condVal cat A F K c).Mem (c.eval row) := fun hr c row hrow =>
    have hT := keyedWindows_sound hcat hA hF hK
    Expr.absD_sound (aeval_sound hcat hA hF hT hr row hrow) (facts_sound hcat hF hT hr row hrow)
      (fun _ h => by simp at h) c
  match r, hwf, h with
  | .filter r c, hwf, h =>
    simp only [rule] at h
    split at h
    · rename_i ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨hwf.1, rfl, ?_⟩
      simp only [eval]
      refine (List.filter_eq_self.2 fun row hrow => ?_).symm
      simp [AVal.certainlyTrue_mem ht (cond hwf.1 c row hrow), Value.isTrue]
    · split at h
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨by simp [WF], rfl, ?_⟩
        simp only [eval]
        refine (List.filter_eq_nil_iff.2 fun row hrow => ?_).symm
        have hm := cond hwf.1 c row hrow
        cases hv : c.eval row with
        | bool b => cases b <;> simp_all [AVal.Mem, Value.isTrue]
        | _ => simp [Value.isTrue]
      · split at h
        · rename_i x y on _ _
          split at h
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            refine ⟨⟨hwf.1, hwf.2⟩, rfl, ?_⟩
            simp only [eval]
            refine (filter_leftJoin fun z hz => ?_).symm
            have hT := keyedWindows_sound hcat hA hF hK
            have hpad := (aeval_sound hcat hA hF hT hwf.1.1 z hz).append (EnvMem.nullRow (y.arity cat))
              (by rw [aeval_length hwf.1.1, eval_arity hcat hwf.1.1 z hz])
            have hm := Expr.absD_sound hpad (fs := []) (ks := []) (fun _ h => by simp at h)
              (fun _ h => by simp at h) c
            cases hv : c.eval (z ++ List.replicate (y.arity cat) .null) with
            | bool b => cases b <;> simp_all [AVal.Mem, Value.isTrue]
            | _ => simp [Value.isTrue]
          · simp at h
        · simp at h
  | .join a b .left on, hwf, h =>
    simp only [rule] at h
    split at h
    · rename_i hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨hwf, rfl, ?_⟩
      simp only [eval]
      exact (leftJoin_eq_inner (fkMatch_sound hcat hA hF hK hR hm hwf.1 hwf.2.1)).symm
    · simp at h
  | .distinct r, hwf, h =>
    simp only [rule] at h
    split at h
    · simp at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (by simpa using hne)
      exact ⟨hwf, rfl, by simp only [eval, dedup_of_nodup (keys (r := r) hwf k hk).nodup]⟩
  | .aggregate r gs ms, hwf, h =>
    simp only [rule] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        groupsKey, List.any_eq_true, List.all_eq_true, List.contains_iff_mem] at hc
      obtain ⟨⟨rfl, hgs⟩, k, hk, hkg⟩ := hc
      have hlen := eval_arity hcat hwf.1
      refine ⟨⟨⟨hwf.1, hwf.2.1⟩, by simp [arity]⟩, by simp [arity], ?_⟩
      -- The groups are distinct, so each has one row.
      have hp := (keys hwf.1 k hk).map_pairwise (f := groupKey gs) fun x y he => by
        simp only [keyOf, List.map_inj_left]
        intro c hc
        simpa [Expr.eval] using List.map_inj_left.mp he _ (hkg c hc)
      simp only [eval, aggregateEval, List.isEmpty_iff, hgs, ↓reduceIte, dedup_of_nodup hp,
        List.map_map]
      refine List.map_congr_left fun row hrow => ?_
      have h1 : keyOf ((List.range gs.length).map (r.arity cat + ·)) (row ++ groupKey gs row) =
          groupKey gs row := by
        rw [← hlen row hrow, keyOf_shift, keyOf_range (by simp [groupKey])]
      simpa [keyOf, List.map_map, groupKey] using h1
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨⟨hwf.1, hwf.2.1, ?_⟩, by simp [arity], ?_⟩
        · simp only [List.mem_map]
          rintro _ ⟨m, hm, rfl⟩
          exact Measure.refsLt_dropDistinct (hwf.2.2 m hm)
        · simp only [eval]
          refine aggregateEval_congr_ms fun grp hg => ?_
          rw [List.map_map]
          exact List.map_congr_left fun m _ =>
            Measure.eval_dropDistinct (fun k hk => (keys hwf.1 k hk).sublist hg) m
      · split at h
        · rename_i name' a k hj
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            simp only [Bool.and_eq_true, List.all_eq_true, Expr.refsLtb_iff] at hc
            obtain ⟨hgs, hms⟩ := hc
            obtain ⟨ha, -, g, he, hg⟩ := joinElim_sound hcat hA hF hK hR hwf.1 hj
            refine ⟨⟨ha, hgs, fun m hm => ⟨hms m hm m.arg (by simp [Measure.exprs]),
              fun c hc => hms m hm c (by simp [Measure.exprs]; exact .inr hc)⟩⟩, rfl, ?_⟩
            have hext : ∀ x ∈ a.eval cat, ∀ e : Expr, e.refsLt (a.arity cat) →
                e.eval (g x) = e.eval x := fun x hx e hr => by
              obtain ⟨w, hw⟩ := hg x hx
              rw [hw]; exact Expr.eval_append w hr (eval_arity hcat ha x hx)
            simp only [eval, he]
            exact (aggregateEval_map (fun x hx e he' => hext x hx e (hgs e he'))
              (fun x hx m hm e he' => hext x hx e (hms m hm e he'))).symm
          · simp at h
        · split at h
          · rename_i hf
            simp only [Option.some.injEq] at h
            subst h
            exact fdAgg_sound hcat hA hF hK hwf hf
          · exact eagerAgg_sound hcat hA hF hK hwf h
  | .emit r m, hwf, h =>
    simp only [rule] at h
    split at h
    · rename_i name' a k hj
      split at h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨ha, -, g, he, hg⟩ := joinElim_sound hcat hA hF hK hR hwf.1 hj
        have hm' : ∀ i ∈ m, i < a.arity cat := by simpa using hm
        refine ⟨⟨ha, hm'⟩, rfl, ?_⟩
        simp only [eval, he, List.map_map]
        refine List.map_congr_left fun x hx => ?_
        obtain ⟨w, hw⟩ := hg x hx
        have hl := eval_arity hcat ha x hx
        simp only [Function.comp_apply, hw]
        exact List.map_congr_left fun i hi => (getD_append_left' (by rw [hl]; exact hm' i hi)).symm
      · simp at h
    · split at h
      · rename_i j es _
        split at h
        · rename_i name' a k hj
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            simp only [Bool.and_eq_true, List.all_eq_true, Expr.refsLtb_iff, Bool.or_eq_true,
              decide_eq_true_eq] at hc
            obtain ⟨hes, hmi⟩ := hc
            obtain ⟨ha, hn, g, he, hg⟩ := joinElim_sound hcat hA hF hK hR hwf.1.1 hj
            refine ⟨⟨⟨ha, hes⟩, ?_⟩, by simp [arity], ?_⟩
            · simp only [List.mem_map]
              rintro _ ⟨i, hi, rfl⟩
              have := hwf.2 i hi
              simp only [arity, hn] at this
              simp only [arity]
              have := hmi i hi
              split <;> omega
            · simp only [eval, he, List.map_map]
              refine List.map_congr_left fun x hx => ?_
              obtain ⟨w, hw⟩ := hg x hx
              have hl := eval_arity hcat ha x hx
              have hwl : w.length = k := by
                have := eval_arity hcat hwf.1.1 (g x) (by rw [he]; exact List.mem_map_of_mem hx)
                rw [hw, hn] at this
                simp [hl] at this
                omega
              have hesx : es.map (·.eval (x ++ w)) = es.map (·.eval x) :=
                List.map_congr_left fun e he' => Expr.eval_append w (hes e he') hl
              simp only [Function.comp_apply, hw, hesx]
              refine List.map_congr_left fun i hi => ?_
              rcases hmi i hi with hi' | hi'
              · simp only [Function.comp_apply, hi', ↓reduceIte, List.append_assoc]
                rw [getD_append_left' (by omega), getD_append_left' (by omega)]
              · have hni : ¬ i < a.arity cat := by omega
                simp only [Function.comp_apply, hni, ↓reduceIte, List.append_assoc]
                obtain ⟨d, rfl⟩ : ∃ d, i = x.length + (w.length + d) := ⟨i - x.length - w.length, by omega⟩
                rw [show x.length + (w.length + d) - k = x.length + d by omega, getD_append_right',
                  getD_append_right', getD_append_right']
          · simp at h
        · simp at h
      · simp at h

theorem Rel.stepN_sound : ∀ (fuel : Nat) {r : Rel} {log : List String}, r.WF cat →
    Same cat r (r.stepN cat A F K R fuel log).1
  | 0, _, _, hwf => ⟨hwf, rfl, rfl⟩
  | fuel + 1, r, log, hwf => by
    unfold stepN
    split
    · rename_i hs
      have h1 := rule_sound hcat hA hF hK hR hwf hs
      exact h1.trans (stepN_sound fuel h1.wf)
    · exact ⟨hwf, rfl, rfl⟩

theorem Rel.step_sound {r : Rel} {log : List String} (hwf : r.WF cat) :
    Same cat r (r.step cat A F K R log).1 :=
  stepN_sound hcat hA hF hK hR 4 hwf

/-- **Soundness of the rewrites**: on data meeting the preconditions, the
rewritten plan gives the same rows. -/
theorem Rel.optimize_sound : ∀ {r : Rel}, r.WF cat → Same cat r (r.optimize cat A F K R).1
  | .read _, hwf | .values _ _, hwf => ⟨hwf, rfl, rfl⟩
  | .filter r c, hwf => by
    have ih := optimize_sound hwf.1
    refine Same.trans ?_ (step_sound hcat hA hF hK hR ?_)
    · exact ⟨⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩, ih.arity, by simp [eval, ih.eval]⟩
    · exact ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
  | .project r es, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.project (r.optimize cat A F K R).1 es).WF cat := ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hR hw)
  | .emit r m, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.emit (r.optimize cat A F K R).1 m).WF cat := ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, rfl, by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hR hw)
  | .cross a b, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2
    have hw : (Rel.cross (a.optimize cat A F K R).1 (b.optimize cat A F K R).1).WF cat := ⟨iha.wf, ihb.wf⟩
    exact Same.trans ⟨hw, by simp [arity, iha.arity, ihb.arity], by simp [eval, iha.eval, ihb.eval]⟩
      (step_sound hcat hA hF hK hR hw)
  | .join a b ty on, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2.1
    have hw : (Rel.join (a.optimize cat A F K R).1 (b.optimize cat A F K R).1 ty on).WF cat :=
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
    refine Same.trans ⟨hw, by simp [arity, iha.arity, ihb.arity], ?_⟩ (step_sound hcat hA hF hK hR hw)
    cases ty <;> simp [eval, iha.eval, ihb.eval, ihb.arity]
  | .fetch r off cnt, hwf => by
    have ih := optimize_sound (r := r) hwf
    have hw : (Rel.fetch (r.optimize cat A F K R).1 off cnt).WF cat := ih.wf
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hR hw)
  | .unionAll a b, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2.1
    have hw : (Rel.unionAll (a.optimize cat A F K R).1 (b.optimize cat A F K R).1).WF cat :=
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
    exact Same.trans ⟨hw, by simp [arity, iha.arity], by simp [eval, iha.eval, ihb.eval]⟩
      (step_sound hcat hA hF hK hR hw)
  | .window r part sort fns, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.window (r.optimize cat A F K R).1 part sort fns).WF cat :=
      ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hR hw)
  | .semi a b anti on, hwf => by
    have iha := optimize_sound hwf.1
    have ihb := optimize_sound hwf.2.1
    have hw : (Rel.semi (a.optimize cat A F K R).1 (b.optimize cat A F K R).1 anti on).WF cat :=
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
    exact Same.trans ⟨hw, by simp [arity, iha.arity], by simp [eval, iha.eval, ihb.eval]⟩
      (step_sound hcat hA hF hK hR hw)
  | .orderBy r keys, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.orderBy (r.optimize cat A F K R).1 keys).WF cat := ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hR hw)
  | .distinct r, hwf => by
    have ih := optimize_sound (r := r) hwf
    have hw : (Rel.distinct (r.optimize cat A F K R).1).WF cat := ih.wf
    exact Same.trans ⟨hw, by simp [arity, ih.arity], by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hR hw)
  | .aggregate r gs ms, hwf => by
    have ih := optimize_sound hwf.1
    have hw : (Rel.aggregate (r.optimize cat A F K R).1 gs ms).WF cat :=
      ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
    exact Same.trans ⟨hw, rfl, by simp [eval, ih.eval]⟩ (step_sound hcat hA hF hK hR hw)

end

end Substrait
