module

public import FrogModel.Recursion.Law

@[expose] public section

/-!
# Lemma 4.3 of the paper, the exact recursion

`CurveLawZero d` and `CurveLawSucc d` (Recursion/Statement.lean) from Law.lean: the glued
sample has the law of the frog model (`map_glue`), its curve at kill depth `K + 1` is pathwise
`psiG` of the child curves and the directions whenever infinitely many root steps go to the
parent (`curveK_succ_eq_psiG`, almost sure by `ae_dirS_infinite`), and these have law
`(curveLaw d K)^d ⊗ dirMeasure d` (`map_childS_dirS`).
-/

open MeasureTheory ProbabilityTheory FrogModel.LemmaX

namespace FrogModel.Recursion

/-- **Lemma 4.3 at kill depth 0.** -/
theorem curveLawZero_holds (d : ℕ) [NeZero d] : CurveLawZero d := by
  unfold CurveLawZero curveLaw
  rw [psiLaw_dirac_zero, ← map_dirZero]
  have h1 : (fun p : Sample d × (ℕ → ℕ → Step d) => curveK 0 p.1 p.2) =
      (fun D (j : ℕ) => dirCount D 0 j) ∘ (fun ξ : ℕ → ℕ → Step d => fun a => (ξ a 0).2) ∘
        Prod.snd := by
    funext p j
    exact curveK_zero_eq p.1 p.2 j
  have hdir : Measurable fun ξ : ℕ → ℕ → Step d => fun a => (ξ a 0).2 := by fun_prop
  rw [h1, ← Measure.map_map measurable_dirCount_zero (hdir.comp measurable_snd),
    ← Measure.map_map hdir measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

/-- **Lemma 4.3, the exact recursion.** -/
theorem curveLawSucc_holds (d : ℕ) [NeZero d] : CurveLawSucc d := by
  intro K
  have hmc : Measurable fun p : Sample d × (ℕ → ℕ → Step d) => curveK (K + 1) p.1 p.2 :=
    measurable_curveK (K + 1)
  conv_lhs => rw [curveLaw, ← map_glue, Measure.map_map hmc measurable_glue]
  rw [psiLaw, ← map_childS_dirS K, Measure.map_map measurable_psiG (measurable_childS_dirS K)]
  apply Measure.map_congr
  filter_upwards [ae_dirS_infinite K] with π hπ
  exact curveK_succ_eq_psiG K π hπ

end FrogModel.Recursion
