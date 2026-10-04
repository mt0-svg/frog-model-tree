module

public import FrogModel.Defs
public import FrogModel.Engine.Defs

@[expose] public section

/-!
# The lower model M1_L as a machine driven by the values it reads

The rule M1_L of Section 13 of the paper. The vertex `w` of the planted model (the vertex `r` of the
paper) is the empty word; a vertex of `T(w)` is a word `v : Vertex 3` (`c :: v` its child `c`,
height `m - |v|`); the parent of `w` is the leaf `y`. A frog is an entrant `Sum.inl i` (it starts
at `w`) or the frog `Sum.inr v` of the vertex `v`.

A value read is a step of `Step 3` (its second component, `0` to the parent and `c + 1` to the
child `c`, as in `FrogModel.step` away from the root) and a kill coin in `ℕ`. The rule is a machine:
`req s` names the frog whose next step is read (`none`: a kill coin, or padding after the run), and
`upd p s x` is the state after the value `x`. The state is the stack of open closures (innermost
first) and the marks. A closure `C(v, Q, t)` is a `Frame`: its vertex, its type (`isR`), the
unmarked children of `v` when it started (`f0`, read by the keep function of an `H` closure), its
pool, its ups, the frog on a ghost walk with its vertex, and whether it waits for its kill coin.

As in the rule of Section 13, the pool is a list read from its head; a frog back from a ghost walk
goes to the head; the frogs returned by an `R` or `H` entry are appended and the pool is cut to its
first `P` frogs. The keep functions are given as sets of coin values (`keep isR h f a f' n`), so
that the keep probability is the mass of a set of coins, as in the proof of Proposition 13.3.
-/

namespace FrogModel.D3

/-- Frogs of the planted model: entrant `i`, or the frog of a vertex of `T(w)`. -/
abbrev Frog := ℕ ⊕ Vertex 3

/-- A value read: a step and a kill coin. -/
abbrev Val := Step 3 × ℕ

/-- The parameters of M1_L at height `m`: the caps `V` and `P`, the ghost depth `L` and the keep
sets (`keep isR h f a f' n`: a closure of type `isR` at height `h`, `f` unmarked children at its
start, outcome `(a, f')`, is kept when its coin is `n`). -/
structure Params where
  m : ℕ
  V : ℕ
  P : ℕ
  L : ℕ
  keep : Bool → ℕ → ℕ → ℕ → ℕ → ℕ → Bool

/-- An open closure. -/
structure Frame where
  v : Vertex 3
  isR : Bool
  f0 : ℕ
  pool : List Frog
  ups : List Frog
  ghost : Option (Frog × Vertex 3)
  killing : Bool

/-- The state of the machine: the open closures, innermost first, the marked vertices, and the
ups of the top closure once the run has ended (`stack = []`). -/
structure St where
  stack : List Frame
  marks : Finset (Vertex 3)
  out : List Frog

/-- The number of unmarked children of `v`. -/
def unmarked (marks : Finset (Vertex 3)) (v : Vertex 3) : ℕ :=
  (Finset.univ.filter fun c : Fin 3 => c :: v ∉ marks).card

/-- The three children of `v`. -/
def kids (v : Vertex 3) : Finset (Vertex 3) := Finset.univ.image fun c : Fin 3 => c :: v

/-- One step of a ghost walk below `v`: to the parent, or to a child. -/
def ghostStep (u : Vertex 3) (ξ : Step 3) : Vertex 3 :=
  if h : ξ.2 = 0 then u.tail else ξ.2.pred h :: u

/-- After a round: a closure with an empty pool and no ghost ends; the top one ends the run, any
other waits for its kill coin. -/
def settle (marks : Finset (Vertex 3)) : List Frame → St
  | [] => ⟨[], marks, []⟩
  | [f] => if f.pool = [] ∧ f.ghost = none then ⟨[], marks, f.ups⟩ else ⟨[f], marks, []⟩
  | f :: g :: s =>
    if f.pool = [] ∧ f.ghost = none then ⟨{f with killing := true} :: g :: s, marks, []⟩
    else ⟨f :: g :: s, marks, []⟩

/-- The frog read next: the ghost frog, the head of the pool, or `none` for a kill coin and for
padding after the run. -/
def req (s : St) : Option Frog :=
  match s.stack with
  | [] => none
  | f :: _ =>
    if f.killing then none
    else match f.ghost with
      | some (φ, _) => some φ
      | none => f.pool.head?

/-- The state after the value `x`. -/
def upd (p : Params) (s : St) (x : Val) : St :=
  match s.stack with
  | [] => s
  | f :: rest =>
    if f.killing then
      let kept := p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked s.marks f.v) x.2
      let rets := if kept then f.ups else []
      let marks' := if kept then s.marks else s.marks ∪ kids f.v
      match rest with
      | [] => ⟨[], marks', rets⟩
      | g :: rest' => settle marks' ({g with pool := (g.pool ++ rets).take p.P} :: rest')
    else match f.ghost with
      | some (φ, u) =>
        let u' := ghostStep u x.1
        if u' = f.v then ⟨{f with pool := φ :: f.pool, ghost := none} :: rest, s.marks, []⟩
        else if u'.length = f.v.length + p.L then settle s.marks ({f with ghost := none} :: rest)
        else ⟨{f with ghost := some (φ, u')} :: rest, s.marks, []⟩
      | none =>
        match f.pool with
        | [] => s
        | φ :: ps =>
          if h : x.1.2 = 0 then
            let ups' := if f.ups.length < p.V then f.ups ++ [φ] else f.ups
            settle s.marks ({f with pool := ps, ups := ups'} :: rest)
          else
            let z := x.1.2.pred h :: f.v
            if f.v.length = p.m ∨ (f.isR = false ∧ z ∈ s.marks) then
              ⟨{f with pool := ps, ghost := some (φ, z)} :: rest, s.marks, []⟩
            else if z ∉ s.marks then
              ⟨⟨z, true, 3, [φ, Sum.inr z], [], none, false⟩ :: {f with pool := ps} :: rest,
                insert z s.marks, []⟩
            else
              ⟨⟨z, false, unmarked s.marks z, [φ], [], none, false⟩ :: {f with pool := ps} :: rest,
                s.marks, []⟩

/-- The initial state with `k` entrants: the top closure `C(w, {entrants} ∪ {ψ_w}, R)`. -/
def init (k : ℕ) : St :=
  ⟨[⟨[], true, 3, (List.range k).map Sum.inl ++ [Sum.inr []], [], none, false⟩], ∅, []⟩

/-- The count so far: the ups of the top closure. -/
def count (s : St) : ℕ :=
  match s.stack.getLast? with
  | none => s.out.length
  | some f => f.ups.length

/-- The run on a sequence of values. -/
def run (p : Params) (k : ℕ) (y : ℕ → Val) : ℕ → St := FrogModel.Engine.traj (upd p) (init k) y

/-- The state after a finite sequence of values. -/
def runFin (p : Params) (k : ℕ) {n : ℕ} (y : Fin n → Val) : St :=
  (List.ofFn y).foldl (upd p) (init k)

/-- The rule as a reading: the pool of the `n`-th value read, `some φ` for frog `φ` and `none` for
the kill coins and the padding. -/
def sel (p : Params) (k : ℕ) (n : ℕ) (y : Fin n → Val) : Option Frog := req (runFin p k y)

end FrogModel.D3
