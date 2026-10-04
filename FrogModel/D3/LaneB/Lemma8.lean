module

public import FrogModel.D3.LaneB.ClosureFacts
public import FrogModel.D3.LaneB.Counts

@[expose] public section

/-!
# Lemma 10.6 of the paper, second bound

`P(e_1 < J) ≤ P(N(j) < k) + P(Bin(k, 1/4) < J)`: if `e_1 < J` and `N ≥ k`, fewer than `J` of the
first `k` directions enter the child `1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- The directions of the closure have law `dirMeasure`. -/
theorem closMeasure_dir (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (A : Set (ℕ → Fin 4)) :
    closMeasure Q {x | x.2 ∈ A} = dirMeasure A := by
  unfold closMeasure
  rw [show {x : ClosSample | x.2 ∈ A} = Set.univ ×ˢ A by ext x; simp, Measure.prod_prod,
    measure_univ, one_mul]

/-- **Lemma 10.6 of the paper**, second bound. -/
theorem lemma8b_of : lemma8b := by
  intro m j J k hj hk
  unfold closProb
  have hsub : {x : ClosSample | closE (j + 1) x.1 x.2 0 < J} ⊆
      {x | closN (j + 1) x.1 x.2 < k} ∪ {x | x.2 ∈ {D : ℕ → Fin 4 | dirCount D 1 k < J}} := by
    intro x hx
    exact lemma8b_incl (j + 1) k J x.1 x.2 0 hx
  rw [← dirMeasure_dirCount_lt k J 1, ← closMeasure_dir (curveLaw m),
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono (by finiteness)
    ((measure_mono hsub).trans (measure_union_le _ _))

end FrogModel.D3.Iface
