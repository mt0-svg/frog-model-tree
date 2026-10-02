module

public import FrogModel.Engine.G3Cert
public import FrogModel.LemmaX.CertMain
public import FrogModel.LemmaX.PlanCand
public import FrogModel.Recursion.Main

@[expose] public section

/-!
# The frozen target from the data

`transient_four_of_data`: a tree of entries that passes the checker G3K (`G3K.Spec.checkAll`)
and the start checks for the atoms `Latoms` gives `Transient 4`, the first target of
FrogModel/Challenge.lean (its definitions are those of FrogModel/Defs.lean). It composes
`transient_four_of` (Lemma X at `d = 4`, Theorem 2.3 of the paper, and Theorem A, Theorem 2.2), the
recursion of Lemma 4.3 (`curveLawZero_holds`, `curveLawSucc_holds`), the soundness of the checker (`phiSuper_of_check`)
and the plan of `Latoms` checked by the kernel (`planCheck_cand`). The tree itself is the
certificate data, generated outside the repository; the theorem `checkAll t = true` on it is a
kernel run (Section 8.2 of the paper). From the same data, `meanVisits_four_le_of_data` gives
the second target, `E V ≤ 5.756`, through Theorem A.
FrogModel/Solution.lean applies both to the data tree.
-/

namespace FrogModel

open FrogModel.Engine.G3 FrogModel.LemmaX MeasureTheory
open scoped ENNReal

/-- **`Transient 4` from a tree that passes the checker and the start checks.** -/
theorem transient_four_of_data
    (h : ∃ t : G3K.Tree, G3K.Spec.checkAll t = true ∧ startOK Latoms t = true) : Transient 4 := by
  obtain ⟨t, hc, hs⟩ := h
  exact transient_four_of (FrogModel.Recursion.curveLawZero_holds 4)
    (FrogModel.Recursion.curveLawSucc_holds 4) (phiSuper_of_check t Latoms planData hc hs planCheck_cand)

/-- **Lemma X at `d = 4`** (Theorem 2.3: `E X ≤ c`) from a tree that passes the checker and the
start checks. -/
theorem lemmaXFour_of_data
    (h : ∃ t : G3K.Tree, G3K.Spec.checkAll t = true ∧ startOK Latoms t = true) : LemmaXFour := by
  obtain ⟨t, hc, hs⟩ := h
  exact lemmaXFour_of (FrogModel.Recursion.curveLawZero_holds 4)
    (FrogModel.Recursion.curveLawSucc_holds 4) (phiSuper_of_check t Latoms planData hc hs planCheck_cand)

/-- **`E V ≤ 5c / (1 - c)`** at `d = 4`, with `c = 9337230319347 / 17448304640000` the bound of
Lemma X, from a tree that passes the checker and the start checks (Theorem A). -/
theorem meanVisits_four_le_exact_of_data
    (h : ∃ t : G3K.Tree, G3K.Spec.checkAll t = true ∧ startOK Latoms t = true) :
    ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure 4 ≤
      ENNReal.ofReal (5 * (9337230319347 / 17448304640000) /
        (1 - 9337230319347 / 17448304640000)) := by
  have hX : meanX 4 ≤ ENNReal.ofReal (9337230319347 / 17448304640000) := lemmaXFour_of_data h
  set c : ℝ := 9337230319347 / 17448304640000 with hc
  have hc0 : 0 ≤ c := by rw [hc]; norm_num
  have hc1 : c < 1 := by rw [hc]; norm_num
  have hcE : ENNReal.ofReal c < 1 := by rw [ENNReal.ofReal_lt_one]; exact hc1
  have hx1 : meanX 4 < 1 := lt_of_le_of_lt hX hcE
  refine (theoremA (by norm_num) hx1).trans ?_
  have hnum : ((4 : ℕ) + 1 : ℝ≥0∞) * meanX 4 ≤ 5 * ENNReal.ofReal c := by
    rw [show ((4 : ℕ) + 1 : ℝ≥0∞) = 5 by norm_num]
    gcongr
  have hden : 1 - ENNReal.ofReal c ≤ 1 - meanX 4 := tsub_le_tsub_left hX 1
  refine (ENNReal.div_le_div hnum hden).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hc0, show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos (by linarith)]

/-- **`E V ≤ 5.756`** at `d = 4` from a tree that passes the checker and the start checks. -/
theorem meanVisits_four_le_of_data
    (h : ∃ t : G3K.Tree, G3K.Spec.checkAll t = true ∧ startOK Latoms t = true) :
    ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure 4 ≤ ENNReal.ofReal (5756 / 1000) := by
  refine (meanVisits_four_le_exact_of_data h).trans (ENNReal.ofReal_le_ofReal ?_)
  norm_num

end FrogModel
