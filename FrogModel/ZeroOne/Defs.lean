module

public import FrogModel.Defs
public import FrogModel.Pieces.Defs

@[expose] public section

/-!
# Definitions of the proof of Theorem 9.3 of the paper

The filtration of the frogs at depth `≤ n` (`nearSigma`, `nearFiltration`) and the frogs below
(`farSigma`); the sample of the planted tree at a vertex `w` (`shift`, `embedAt`); the first
vertex at a given depth on the walk of the root frog (`firstDeep`); the frozen frogs of `T*`
(`frozen`), their exit times (`exitTime`) and the steps after the exit (`glueAt`, `glueExit`);
a run of parent steps (`upRun`).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.ZeroOne

variable {d : ℕ}

set_option warn.classDefReducibility false in
/-- The σ-algebra of the step variables of the frogs at depth at most `n`. -/
def nearSigma (d n : ℕ) : MeasurableSpace (Sample d) :=
  ⨆ (v : Vertex d) (_ : v.length ≤ n),
    MeasurableSpace.comap (fun ω : Sample d => ω v) inferInstance

set_option warn.classDefReducibility false in
/-- The σ-algebra of the step variables of the frogs at depth more than `n`. -/
def farSigma (d n : ℕ) : MeasurableSpace (Sample d) :=
  ⨆ (v : Vertex d) (_ : n < v.length),
    MeasurableSpace.comap (fun ω : Sample d => ω v) inferInstance

/-- The filtration of the frogs at depth at most `n`. -/
def nearFiltration (d : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Sample d)) where
  seq := nearSigma d
  mono' := fun _ _ hnm =>
    iSup_mono fun _ => iSup_mono' fun h => ⟨le_trans h hnm, le_rfl⟩
  le' := fun _ => iSup₂_le fun v _ => (measurable_pi_apply v).comap_le

/-- The sample of the planted tree `T*` at `w`: frog `v` of `T*` is the frog `v ++ w`. -/
def shift (w : Vertex d) (ω : Sample d) : Sample d := fun v => ω (v ++ w)

/-- The vertex `v ++ w` of the subtree at `w` for the vertex `some v` of `T*`; the leaf `none`
is the parent of `w`. -/
def embedAt (w : Vertex d) : Option (Vertex d) → Vertex d
  | none => w.tail
  | some v => v ++ w

open Classical in
/-- The first vertex at depth `m` on the walk from the root driven by `x`, `none` if the walk
never reaches depth `m`. -/
noncomputable def firstDeep (m : ℕ) (x : ℕ → Step d) : Option (Vertex d) :=
  if h : ∃ t, (walk root x t).length = m then some (walk root x (Nat.find h)) else none

/-- Frog `v` of `T*` is frozen: it is reached from the frog at the root of `T*` and its path
reaches the leaf. `frozenCount ζ` counts these frogs. -/
def frozen (ζ : Sample d) (v : Vertex d) : Prop :=
  Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none

/-- The exit time of the walk on `T*` from `some v` driven by `x`: its first time at the leaf,
`⊤` if there is none. -/
noncomputable def exitTime (v : Vertex d) (x : ℕ → Step d) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | walkStar (some v) x n = none})

/-- The steps of `x` at the times `k, ..., k + n - 1` all go to the parent. -/
def upRun (n : ℕ) (x : ℕ → Step d) (k : ℕ) : Prop := ∀ j < n, (x (k + j)).2 = 0

/-- The sequence `a` before time `e`, then the sequence `b`. -/
noncomputable def glueAt {α : Type*} (e : ℕ∞) (a b : ℕ → α) : ℕ → α :=
  fun t => if (t : ℕ∞) < e then a t else b (t - e.toNat)

/-- Two samples of `T*` glued at the exit times of the first: frog `v` follows `p.1 v` up to its
exit time, then `p.2 v`. -/
noncomputable def glueExit (p : Sample d × Sample d) : Sample d :=
  fun v => glueAt (exitTime v (p.1 v)) (p.1 v) (p.2 v)

end FrogModel.ZeroOne
