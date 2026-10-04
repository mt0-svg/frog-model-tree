module

public import FrogModel.D3.M1L.GenDefs

@[expose] public section

/-!
# M1_L at every height: the laws by height and the candidate on the machine stack

`laws p h` is `(ρ_h, K_h)` of Lemma 13.2 of the paper on the recursion `Gen`: the law of an R
closure at height `h` with two frogs and of an H closure with one frog and `t` unmarked children,
after the kill. `costs p c h` is the expected number of reads of the same closures, kill coin
included, with cost `c` per read (`c = 1`; `c = 0` gives `0`); a ghost walk from depth `d` costs at
most `2 (L - d)` reads.

The candidate on a machine state is a fold over its stack of open closures: the summary `Sm` of a
closure (type, `f0`, pool size, ups, child types read from the marks, ghost depth, its child index
in its parent) and its value `fv` from `Gen`, whose end value is the kill coin, then the candidate
of the stack below with the parent updated by the outcome (`applyO`). In each closure with a
running child the child's own type is masked: the outcome of the child overwrites it.
-/

namespace FrogModel.D3

/-- The kill: an outcome `(a, g)`, kept with probability `κ`, becomes `(0, 0)` otherwise. The
probability of ending at `(b, f)`. -/
noncomputable def killP (κ : ℝ) (a g b f : ℕ) : ℝ :=
  (if a = b ∧ g = f then κ else 0) + (if b = 0 ∧ f = 0 then 1 - κ else 0)

/-- The keep probability of the machine's keep set. -/
noncomputable def κm (p : Params) (r : Bool) (h f0 a g : ℕ) : ℝ :=
  (coinLaw {j | p.keep r h f0 a g j = true}).toReal

/-- An R closure at height `0` makes ghost entries only: it is an H closure for the recursion. -/
def isRe (h : ℕ) (r : Bool) : Bool := r && decide (h ≠ 0)

/-- The child types of a fresh R closure at height `h` (every child marked at height `0`). -/
def initK (h : ℕ) : Kid := fun _ => if h = 0 then some 0 else none

/-- Child types with `t` unmarked children, for the H closures (every child marked at height `0`). -/
def kidOf (h t : ℕ) : Kid := fun c => if h = 0 then some 0 else if c.val < t then none else some 0

/-- The inputs of the recursion at a height: `ρ` and `K` of the height below. -/
abbrev LawIn := (ℕ → ℕ → ℝ) × (ℕ → ℕ → ℕ → ℝ)

/-- `Gen` at height `h` for a closure of type `r`, on the inputs `q`. -/
noncomputable def GenH (p : Params) (h : ℕ) (r : Bool) (q : LawIn) (add : Kid → ℝ)
    (term : Kid → ℕ → ℝ) : Kid → ℕ → ℕ → ℝ :=
  Gen p.V p.P (isRe h r) (pL p.L) q.1 q.2 add term

/-- `ρ_h` and `K_h` from the inputs of height `h`. -/
noncomputable def lawsAt (p : Params) (h : ℕ) (q : LawIn) : LawIn :=
  (fun b f => GenH p h true q (fun _ => 0)
      (fun k a => killP (κm p true h 3 a (nN k)) a (nN k) b f) (initK h) 2 0,
    fun t b f => GenH p h false q (fun _ => 0)
      (fun k a => killP (κm p false h t a (nN k)) a (nN k) b f) (kidOf h t) 1 0)

/-- The point mass at `(0, 0)`, the inputs at height `0`. -/
noncomputable def dummyIn : LawIn :=
  (fun b f => if b = 0 ∧ f = 0 then 1 else 0, fun _ b f => if b = 0 ∧ f = 0 then 1 else 0)

/-- `(ρ_h, K_h)`. -/
noncomputable def laws (p : Params) : ℕ → LawIn
  | 0 => lawsAt p 0 dummyIn
  | h + 1 => lawsAt p (h + 1) (laws p h)

/-- The inputs at height `h`: `(ρ_{h-1}, K_{h-1})`; at height `0`, where no closure reads them, the
point mass at `(0, 0)`. -/
noncomputable def inp (p : Params) : ℕ → LawIn
  | 0 => dummyIn
  | h + 1 => laws p h

/-- The cost of a ghost walk from depth `d`. -/
noncomputable def gcost (L d : ℕ) : ℝ := 2 * ((L - d : ℕ) : ℝ)

/-- The additive term of the cost recursion: the read of the direction, then the expected cost of
the entry into each child (`τ`: the costs of the height below). -/
noncomputable def addC (p : Params) (c : ℝ) (h : ℕ) (r : Bool) (τ : ℝ × (ℕ → ℝ)) (k : Kid) : ℝ :=
  c + ∑ c', 1 / 4 * (match k c' with
    | none => τ.1
    | some t => if isRe h r then τ.2 t else c * gcost p.L 1)

/-- The costs at height `h` from those of the height below. -/
noncomputable def costsAt (p : Params) (c : ℝ) (h : ℕ) (τ : ℝ × (ℕ → ℝ)) : ℝ × (ℕ → ℝ) :=
  (GenH p h true (inp p h) (addC p c h true τ) (fun _ _ => c) (initK h) 2 0,
    fun t => GenH p h false (inp p h) (addC p c h false τ) (fun _ _ => c) (kidOf h t) 1 0)

/-- The expected cost of an R closure (two frogs) and of an H closure (one frog, `t` unmarked
children) at height `h`, kill coin included. -/
noncomputable def costs (p : Params) (c : ℝ) : ℕ → ℝ × (ℕ → ℝ)
  | 0 => costsAt p c 0 (0, fun _ => 0)
  | h + 1 => costsAt p c (h + 1) (costs p c h)

/-- The costs of the height below `h`. -/
noncomputable def cinp (p : Params) (c : ℝ) : ℕ → ℝ × (ℕ → ℝ)
  | 0 => (0, fun _ => 0)
  | h + 1 => costs p c h

/-- The summary of an open closure. -/
structure Sm where
  isR : Bool
  f0 : ℕ
  n : ℕ
  a : ℕ
  kid : Kid
  d : ℕ
  slot : Fin 3

/-- The value of a closure at height `h`, with cost `c` per read and end value `term`. -/
noncomputable def fv (p : Params) (c : ℝ) (h : ℕ) (term : Kid → ℕ → ℝ) (s : Sm) : ℝ :=
  if s.d = 0 then GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) term s.kid s.n s.a
  else c * gcost p.L s.d +
    rL p.L s.d * GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) term s.kid (s.n + 1) s.a +
    (1 - rL p.L s.d) * GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) term s.kid s.n s.a

/-- The round of a closure at height `h` into child `c'`, loop and entry cost included: an R entry
(cost `τR`), an H entry (cost `τH t`, loop `K t 1 t`) or a ghost entry (cost `2 (L - 1)`, loop `p_L`). -/
noncomputable def childV (p : Params) (c : ℝ) (h : ℕ) (r : Bool) (T : Kid → ℕ → ℝ) (k : Kid)
    (n a : ℕ) (c' : Fin 3) : ℝ :=
  match k c' with
  | none => (cinp p c h).1 + bodyG p.V p.P (isRe h r) (pL p.L) (inp p h).1 (inp p h).2
      (GenH p h r (inp p h) (addC p c h r (cinp p c h)) T) k n a c'
  | some t => (if isRe h r then (cinp p c h).2 t +
        (inp p h).2 t 1 t * GenH p h r (inp p h) (addC p c h r (cinp p c h)) T k n a
      else c * gcost p.L 1 + pL p.L * GenH p h r (inp p h) (addC p c h r (cinp p c h)) T k n a) +
    bodyG p.V p.P (isRe h r) (pL p.L) (inp p h).1 (inp p h).2
      (GenH p h r (inp p h) (addC p c h r (cinp p c h)) T) k n a c'

/-- The parent after its child at `slot` returns `b` frogs and leaves `f` unmarked children. -/
def applyO (P b : ℕ) (f : Fin 4) (slot : Fin 3) (g : Sm) : Sm :=
  { g with n := min (g.n + b) P, kid := Function.update g.kid slot (some f) }

/-- The candidate on a stack of summaries, the head at height `h`; `top` is the value at the end
of the run. -/
noncomputable def fold (p : Params) (c : ℝ) (top : ℕ → ℝ) : ℕ → List Sm → ℝ
  | _, [] => 0
  | h, [f] => fv p c h (fun _ a => top a) f
  | h, f :: g :: rest => fv p c h (fun k a => c + ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
      killP (κm p f.isR h f.f0 a (nN k)) a (nN k) b f' *
        fold p c top (h + 1) (applyO p.P b f' f.slot g :: rest)) f
termination_by _ l => l.length

theorem unmarked_lt (marks : Finset (Vertex 3)) (v : Vertex 3) : unmarked marks v < 4 := by
  unfold unmarked
  have := Finset.card_filter_le (Finset.univ : Finset (Fin 3)) fun c => c :: v ∉ marks
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The child types of a closure at `v` read from the marks, the child `msk` masked. -/
def kidM (p : Params) (marks : Finset (Vertex 3)) (v : Vertex 3) (msk : Option (Fin 3)) : Kid :=
  fun c =>
    if p.m - v.length = 0 then some 0
    else if msk = some c then none
    else if c :: v ∉ marks then none
    else if p.m - v.length = 1 then some 0
    else some ⟨unmarked marks (c :: v), unmarked_lt marks (c :: v)⟩

/-- The depth of the ghost walk of a closure below its vertex (`0`: none). -/
def gdepth (f : Frame) : ℕ :=
  match f.ghost with
  | none => 0
  | some (_, u) => u.length - f.v.length

/-- The summary of a closure. -/
def sm (p : Params) (marks : Finset (Vertex 3)) (msk : Option (Fin 3)) (f : Frame) : Sm :=
  ⟨f.isR, f.f0, f.pool.length, f.ups.length, kidM p marks f.v msk, gdepth f, f.v.headD 0⟩

/-- The summaries of a stack, each closure masking the child running above it. -/
def projS (p : Params) (marks : Finset (Vertex 3)) : Option (Fin 3) → List Frame → List Sm
  | _, [] => []
  | msk, f :: rest => sm p marks msk f :: projS p marks f.v.head? rest

/-- The candidate on a machine state: cost `c` per read, value `top` at the end of the run. -/
noncomputable def Ucand (p : Params) (c : ℝ) (top : ℕ → ℝ) (s : St) : ℝ :=
  match s.stack with
  | [] => top s.out.length
  | f :: rest => fold p c top (p.m - f.v.length) (projS p s.marks none (f :: rest))

/-- A closure within the caps, its ghost walk strictly between its vertex and depth `L`. -/
def FrameOK (p : Params) (f : Frame) : Prop :=
  f.pool.length ≤ p.P ∧ f.ups.length ≤ p.V ∧ f.v.length ≤ p.m ∧
    ∀ φ u, f.ghost = some (φ, u) →
      f.v <:+ u ∧ f.v.length + 1 ≤ u.length ∧ u.length < f.v.length + p.L ∧
        f.pool.length + 1 ≤ p.P

/-- The shape of the stack: each closure at a child of the next one, at a marked vertex except
the top one (the root, an R closure); the head waits for its kill coin exactly when its pool is
empty and it has no ghost; the closures below the head have no ghost and do not wait. -/
def StackOK (p : Params) (marks : Finset (Vertex 3)) : Bool → List Frame → Prop
  | _, [] => True
  | hd, [f] => f.v = [] ∧ f.isR = true ∧ f.killing = false ∧
      (hd = true → f.pool ≠ [] ∨ f.ghost ≠ none) ∧ (hd = false → f.ghost = none) ∧ FrameOK p f
  | hd, f :: g :: rest => f.v = f.v.headD 0 :: g.v ∧ f.v ∈ marks ∧
      (hd = true → (f.killing = true ↔ (f.pool = [] ∧ f.ghost = none))) ∧
      (hd = false → f.killing = false ∧ f.ghost = none) ∧ FrameOK p f ∧
      StackOK p marks false (g :: rest)

/-- The marks: never the root, and every mark below depth one has its parent marked. -/
def MarksAnc (marks : Finset (Vertex 3)) : Prop :=
  ∀ u ∈ marks, u ≠ [] ∧ (u.tail ≠ [] → u.tail ∈ marks)

/-- The good states of the run. -/
def Good (p : Params) : Set St :=
  {s | MarksAnc s.marks ∧ StackOK p s.marks true s.stack ∧ (s.stack = [] → s.out.length ≤ p.V)}

end FrogModel.D3
