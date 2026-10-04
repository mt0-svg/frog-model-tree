module

public import FrogModel.LemmaR.Statement
public import FrogModel.Pieces.Glue

@[expose] public section

/-!
# Definitions of the recurrence criterion on `T_d`

- `seqLaw d`: the law of one step sequence, i.i.d. steps of law `stepLaw d`.
- `returnCount u x`: `N_u`, the number of times `t ≥ 1` at which the walk from `u` driven by `x` is
  at the root.
- `words d n`: the vertices at depth `≤ n`, as a finset.
- `ReachN S n`: the woken set `W_n` with sleeping frogs at depth at most `n`: the least set
  containing the root such that `u ∈ W_n`, `|u| ≤ n` and `S u t = v` give `v ∈ W_n`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.LemmaR

variable {d : ℕ}

/-- The law of one step sequence: i.i.d. steps of law `stepLaw d`. -/
noncomputable abbrev seqLaw (d : ℕ) [NeZero d] : Measure (ℕ → Step d) :=
  Measure.infinitePi fun _ : ℕ => stepLaw d

/-- `N_u`: the number of times `t ≥ 1` at which the walk from `u` driven by `x` is at the root. -/
noncomputable def returnCount (u : Vertex d) (x : ℕ → Step d) : ℕ∞ :=
  {t : ℕ | 1 ≤ t ∧ walk u x t = root}.encard

/-- The vertices at depth `≤ n`. -/
def words (d n : ℕ) : Finset (Vertex d) :=
  (Finset.range (n + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → Fin d)).image List.ofFn

/-- `W_n`: the least set containing the root such that `u ∈ W_n`, `|u| ≤ n` and `S u t = v` give
`v ∈ W_n`. -/
inductive ReachN (S : Vertex d → ℕ → Vertex d) (n : ℕ) : Vertex d → Prop
  | root : ReachN S n root
  | path {u : Vertex d} (t : ℕ) : ReachN S n u → u.length ≤ n → ReachN S n (S u t)

end FrogModel.LemmaR
