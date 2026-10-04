module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# Lemma 10.7 (2) of the paper from Lemmas 10.5 and 10.6

Lemmas 10.5 and 10.6 give `E G_(m+1)(j) ≥ E G_m(J) (1 - P) + (1 + j - J)/3`, and
`mu_(m+1)(j) - (1 + j - J)/3 = mu_m(J)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

theorem meanG_nonneg (m k : ℕ) : 0 ≤ meanG m k := ENNReal.toReal_nonneg

/-- **Lemma 10.7 (2) of the paper** from Lemma 10.5 and the first bound of Lemma 10.6. -/
theorem lemma17b_of (hd1 : d1) (h8a : lemma8a) : lemma17b := by
  intro m j J hj P hP
  have h1 := hd1 m j J hj
  have h2 := h8a m j J hj
  have h3 : meanG m J * closProb m {x | closE (j + 1) x.1 x.2 0 < J} ≤ meanG m J * P :=
    mul_le_mul_of_nonneg_left hP (meanG_nonneg m J)
  unfold deficit mu
  push_cast
  nlinarith

end FrogModel.D3.Iface
