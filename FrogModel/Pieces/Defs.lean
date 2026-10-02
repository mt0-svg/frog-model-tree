module

public import FrogModel.Defs
public import FrogModel.Lemmas.Defs

@[expose] public section

/-!
# The piece space of Theorem A and the planted tree

Section 3.2 of the paper. A piece is a full step sequence; segment `(u, k)` of frog `u` is the
walk driven by its piece from its start vertex, cut at its first time `≥ 1` at the root. The
steps of frog `u` are its pieces glued at the cuts. The planted tree `T*` has the vertices
`some v` (`v` below the root `r = some []`) and the leaf `y = none`; `frozenCount` is the number
`X` of frogs frozen at `y`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel

variable {d : ℕ}

/-- The cut time of the walk from `v` driven by `x`: its first time `n ≥ 1` at the root, `⊤` if
there is none. -/
noncomputable def cut (v : Vertex d) (x : ℕ → Step d) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | 1 ≤ n ∧ walk v x n = root})

/-- The index of a piece: segment `k` of frog `u`. -/
abbrev Seg (d : ℕ) := Vertex d × ℕ

/-- The start of a segment: segment `0` of frog `u` starts at `u`, the others at the root. -/
def Seg.start : Seg d → Vertex d
  | (u, 0) => u
  | (_, _ + 1) => root

/-- The piece space: one step sequence for every segment. -/
abbrev Pieces (d : ℕ) := Seg d → ℕ → Step d

/-- The law of the pieces: all steps independent with law `stepLaw d`. -/
noncomputable def piecesMeasure (d : ℕ) [NeZero d] : Measure (Pieces d) :=
  Measure.infinitePi fun _ : Seg d => Measure.infinitePi fun _ : ℕ => stepLaw d

/-- The cut of segment `σ`. -/
noncomputable def segCut (ζ : Pieces d) (σ : Seg d) : ℕ∞ := cut σ.start (ζ σ)

/-- The cumulative cut times of frog `u`: `T_u(0) = 0`, `T_u(k + 1) = T_u(k) + cut of (u, k)`. -/
noncomputable def cutSum (ζ : Pieces d) (u : Vertex d) : ℕ → ℕ∞
  | 0 => 0
  | k + 1 => cutSum ζ u k + segCut ζ (u, k)

open Classical in
/-- The segment of frog `u` in use at time `t`: the number of `k` with `T_u(k + 1) ≤ t`. -/
noncomputable def segAt (ζ : Pieces d) (u : Vertex d) (t : ℕ) : ℕ :=
  ((Finset.range (t + 1)).filter fun k => cutSum ζ u (k + 1) ≤ t).card

/-- The glued steps of frog `u`: at time `t`, the step of its current segment at the time
elapsed since that segment started. -/
noncomputable def glue (ζ : Pieces d) (u : Vertex d) (t : ℕ) : Step d :=
  ζ (u, segAt ζ u t) (t - (cutSum ζ u (segAt ζ u t)).toNat)

/-- The arcs of the stages: segment `σ` reaches `(w, 0)`, `w ≠ root`, when its path visits `w`
at a time at most its cut. -/
def segArc (σ : Seg d) (x : ℕ → Step d) (τ : Seg d) : Prop :=
  τ.2 = 0 ∧ τ.1 ≠ root ∧ ∃ n : ℕ, (n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1

/-- A segment is closed when its path returns to the root. -/
def segClosed (σ : Seg d) (x : ℕ → Step d) : Prop := cut σ.start x ≠ ⊤

/-- The next segment of the same frog. -/
def segSucc (σ : Seg d) : Seg d := (σ.1, σ.2 + 1)

/-- The stages `Σ_m` of Section 3.2 of the paper, from the segment `(root, 0)`. -/
noncomputable def stage (ζ : Pieces d) (m : ℕ) : Set (Seg d) :=
  Stage.stages segArc segClosed segSucc (root, 0) ζ m

/-- One step on the planted tree `T*`: the leaf `y = none` is absorbing (a frozen frog stays
there); from `some v` the step uses `ξ.2` as at a non-root vertex of the `d`-ary tree: `0` to the
parent (`y` from the root `some []`), `c + 1` to the child `c`. -/
def stepStar : Option (Vertex d) → Step d → Option (Vertex d)
  | none, _ => none
  | some v, ξ =>
    if h : ξ.2 = 0 then
      match v with
      | [] => none
      | _ :: w => some w
    else some (ξ.2.pred h :: v)

/-- The vertices of `T*`: a countable type, with every set measurable. -/
instance (d : ℕ) : MeasurableSpace (Option (Vertex d)) := ⊤

instance (d : ℕ) : DiscreteMeasurableSpace (Option (Vertex d)) := ⟨fun _ => trivial⟩

/-- The walk on `T*` from `v` driven by `x`. -/
def walkStar (v : Option (Vertex d)) (x : ℕ → Step d) : ℕ → Option (Vertex d)
  | 0 => v
  | n + 1 => stepStar (walkStar v x n) (x n)

/-- `T(c) ∪ {o}` inside the `d`-ary tree: the vertex `v` of `T*` is `v ++ [c]`, the leaf `y`
is the root `o`. -/
def embedStar (c : Fin d) : Option (Vertex d) → Vertex d
  | none => root
  | some v => v ++ [c]

/-- The arcs of the reachability digraph of `T*` (frog `v` at `some v`, steps `ζ v`): frog `a`
reaches the frog of `b ≠ r` when its path visits `some b`. -/
def starArc (ζ : Sample d) (a b : Vertex d) : Prop :=
  b ≠ [] ∧ ∃ n, walkStar (some a) (ζ a) n = some b

open Classical in
/-- `X`: the number of frogs of `T*` reached from the frog at `r` whose path reaches `y`. -/
noncomputable def frozenCount (ζ : Sample d) : ℝ≥0∞ :=
  ∑' v : Vertex d,
    if Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none then 1
    else 0

/-- `x = E X`. -/
noncomputable def meanX (d : ℕ) [NeZero d] : ℝ≥0∞ := ∫⁻ ζ, frozenCount ζ ∂frogMeasure d

/-- The returns to the root of the walk from `u` driven by `x` at the times `1 ≤ s ≤ t`. -/
def returns (u : Vertex d) (x : ℕ → Step d) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter fun s => walk u x s = root

/-- The position at time `t` of the walk from `u` driven by `x`, cut at its returns to the root:
the index of the current segment (the number of returns in `[1, t]`) and the time elapsed since
the segment started (since the last return, or since `0`). -/
def posOf (u : Vertex d) (x : ℕ → Step d) (t : ℕ) : ℕ × ℕ :=
  ((returns u x t).card, t - (returns u x t).sup id)

/-! ### Stages, entering segments and the planted trees of Lemma 3.5 of the paper -/

/-- The base of stage `i + 1`: the segment `(root, 0)`, the segments of `Σ_i` and the successors of
its closed ones, so that `stage ζ (i + 1)` is the closure of `stageBase ζ i`. -/
def stageBase (ζ : Pieces d) (i : ℕ) : Set (Seg d) :=
  insert (root, 0) (stage ζ i ∪ {τ | ∃ σ ∈ stage ζ i, segClosed σ (ζ σ) ∧ τ = segSucc σ})

/-- `Z_i`: the segments of the base of stage `i + 1` outside `Σ_i`; `Z_0 = {(root, 0)}`, and for
`i ≥ 1` the successors of the closed segments of stage `i`. Each starts at the root. -/
def enterSeg (ζ : Pieces d) (i : ℕ) : Set (Seg d) := stageBase ζ i \ stage ζ i

/-- `R_i = |Z_i|`. -/
noncomputable def stageR (ζ : Pieces d) (i : ℕ) : ℝ≥0∞ := (enterSeg ζ i).encard

/-- The segments of `Z_i` whose first step goes to the child `[j]` of the root. -/
def enterAt (ζ : Pieces d) (i : ℕ) (j : Fin d) : Set (Seg d) :=
  {σ | σ ∈ enterSeg ζ i ∧ (ζ σ 0).1 = j}

/-- `A_j` of Lemma 3.5: if a segment of `Z_i` enters `[j]`, the segments of `Z_i` entering `[j]`
and `([j], 0)` when `[j]` is not in `U_i`; empty otherwise. -/
def enterSet (ζ : Pieces d) (i : ℕ) (j : Fin d) : Set (Seg d) :=
  {σ | (enterAt ζ i j).Nonempty ∧ (σ ∈ enterAt ζ i j ∨ (σ = ([j], 0) ∧ ([j], 0) ∉ stage ζ i))}

/-- `W_(i+1)`: the children `[j]` of the root entered from `Z_i` and not in `U_i`. -/
noncomputable def stageW (ζ : Pieces d) (i : ℕ) : ℝ≥0∞ :=
  {j : Fin d | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i}.encard

/-- A segment lies in the subtree of `[j]`: it starts at the root with a first step to `[j]`, or it
is the segment `0` of a frog of `T([j])`. -/
def inSub (ζ : Pieces d) (j : Fin d) (τ : Seg d) : Prop :=
  (τ.start = root ∧ (ζ τ 0).1 = j) ∨ ∃ v : Vertex d, τ = (v ++ [j], 0)

/-- The vertex of `T*` of a segment of a subtree: the root `r = []` for a segment starting at the
root, `v` for the segment `(v ++ [j], 0)`. -/
def starVertex (τ : Seg d) : Vertex d := if τ.start = root then [] else τ.1.dropLast

/-- The steps of a segment seen in `T*`: after its first step if it starts at the root. -/
def starSeq (τ : Seg d) (x : ℕ → Step d) : ℕ → Step d :=
  if τ.start = root then fun n => x (n + 1) else x

/-- The sample of `T*` attached to `σ ∈ A_j` (Lemma 3.5), from a family of pieces `ρ`: the frog at
`r` follows the piece of `σ` (after its first step if `σ` starts at the root), the frog at `v ≠ r`
the piece of `(v ++ [j], 0)`. -/
def starSample (j : Fin d) (σ : Seg d) (ρ : Pieces d) : Sample d :=
  fun v => if v = [] ∧ σ.start = root then starSeq σ (ρ σ) else ρ (v ++ [j], 0)

end FrogModel
