module

public import FrogModel.D3.LaneB.Coins
public import FrogModel.D3.LaneB.Measurability

@[expose] public section

/-!
# The parent curve of the closure

From the law of the closure (`curveLaw_succ`, Lemma 10.1 of the paper): the planted curve at height
`m + 1` has the law of the closure's parent curve, so `E G_(m+1)(j) = E X` and
`P(G_(m+1)(j) ≤ v) = P(X ≤ v)` in the `j`-closure for `j ≥ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

theorem measurable_closCurvePair :
    Measurable fun x : ClosSample => (closCurve x.1 x.2, closNCurve x.1 x.2) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun j => ?_) (measurable_pi_iff.mpr fun j => ?_)
  · unfold closCurve
    split_ifs
    · exact measurable_const
    · exact measurable_closX (j + 1)
  · unfold closNCurve
    split_ifs
    · exact measurable_const
    · exact measurable_closN (j + 1)

/-- `curveLaw (m + 1)` is the law of the closure's parent curve. -/
theorem curveLaw_succ_fst (hmeas : measurable_plantedPair)
    (hsucc : curveLaw_succ) (m : ℕ) :
    curveLaw (m + 1) = (closMeasure (curveLaw m)).map fun x => closCurve x.1 x.2 := by
  have h1 : curveLaw (m + 1) =
      (pathMeasure.map fun π => (plantedCurve (m + 1) π, presCurve (m + 1) π)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hmeas (m + 1))]
    rfl
  rw [h1, hsucc m, Measure.map_map measurable_fst measurable_closCurvePair]
  rfl

/-- `E G_(m+1)(j) = E X` in the `j`-closure. -/
theorem meanG_succ_eq (hmeas : measurable_plantedPair)
    (hsucc : curveLaw_succ) (m j : ℕ) (hj : 1 ≤ j) :
    meanG (m + 1) j =
      (∫⁻ x, (closX (j + 1) x.1 x.2 : ℝ≥0∞) ∂closMeasure (curveLaw m)).toReal := by
  unfold meanG
  have hf : Measurable fun G : ℕ → ℕ∞ => ((G j : ℕ∞) : ℝ≥0∞) :=
    (Measurable.of_discrete (f := fun y : ℕ∞ => (y : ℝ≥0∞))).comp (measurable_pi_apply j)
  have hcc : Measurable fun x : ClosSample => closCurve x.1 x.2 :=
    measurable_fst.comp measurable_closCurvePair
  rw [lintegral_plantedG_eq hmeas, curveLaw_succ_fst hmeas hsucc m, lintegral_map hf hcc]
  congr 1
  refine lintegral_congr fun x => ?_
  have hj0 : j ≠ 0 := by omega
  simp [closCurve, hj0]

/-- `P(G_(m+1)(j) ≤ v) = P(X ≤ v)` in the `j`-closure. -/
theorem cdfG_succ_eq (hmeas : measurable_plantedPair)
    (hsucc : curveLaw_succ) (m j v : ℕ) (hj : 1 ≤ j) :
    cdfG (m + 1) j v = closProb m {x | closX (j + 1) x.1 x.2 ≤ v} := by
  have hk : Measurable fun G : ℕ → ℕ∞ => G j := measurable_pi_apply j
  have hs : MeasurableSet {G : ℕ → ℕ∞ | G j ≤ (v : ℕ∞)} :=
    hk (MeasurableSet.of_discrete (s := {y : ℕ∞ | y ≤ (v : ℕ∞)}))
  have hcc : Measurable fun x : ClosSample => closCurve x.1 x.2 :=
    measurable_fst.comp measurable_closCurvePair
  rw [cdfG_eq hmeas, curveLaw_succ_fst hmeas hsucc m, Measure.map_apply hcc hs]
  unfold closProb
  congr 3
  ext x
  have hj0 : j ≠ 0 := by omega
  simp [closCurve, hj0]

end FrogModel.D3.Iface
