module

public import FrogModel.D3.Interfaces.Checks
public import FrogModel.D3.Bridge

@[expose] public section

/-!
# Helpers of the assembly of the d = 3 route

Section 15 of the paper. FrogModel/D3/Assembly.lean proves Theorem 8.4 and the frozen target
`FrogModel.Recurrent 3` (FrogModel/D3/Defs.lean, the text of the definition in
FrogModel/ChallengeRecurrent.lean) from the proofs of FrogModel/D3; it uses the glue of the
parameters at `10^30` (`glue`, `m1_lt`) and the ratio bound of the last step (`ratio_bound`,
`mu_pos`) proved here.

The statements it uses: `lemma19` (Lemma 8.3), `lintegral_plantedG_le` (Lemma 10.2), `seed_valid`
(Lemma 13.4), `lemma18_1`, `lemma18_3`, `ext_valid` (Lemma 12.5), `m1run_certS` (Proposition 15.1),
`dcheck1` (Proposition 15.2), `thmDprime1` (Theorem 14.1), `dprime_tail` (Lemma 14.3), `f3L`
(Proposition 13.3). The statements of Closure.lean (Sections 10 and 11) enter through the proofs of
Sections 12 to 14.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- The parameters of the intervals up to `10^30`, then those of Lemma 14.3 of the paper. -/
def glue (f g : ℕ → ℕ) (m : ℕ) : ℕ := if m < 10 ^ 30 then f m else g m

theorem m1_lt : m1 < 10 ^ 30 := by unfold m1; norm_num

theorem mu_pos (m k : ℕ) : 0 < mu m k := by unfold mu; positivity

/-- `(n + 1)/20 ≤ E Z_(n+1)` from Lemma 8.3 of the paper and `E G_n(1) ≥ (n + 2)/5`, as a ratio. -/
theorem ratio_bound (n : ℕ) (x : ℝ) (hx : ((n : ℝ) + 2) / 5 ≤ x) (a : ℝ≥0∞)
    (ha : (1 + ENNReal.ofReal x) / 4 ≤ a) : (1 / 20 : ℝ≥0∞) ≤ a / ((n + 1 : ℕ) : ℝ≥0∞) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have h1 : (1 + ENNReal.ofReal x) / 4 = ENNReal.ofReal ((1 + x) / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_add zero_le_one hx0,
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have h2 : (1 / 20 : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (((n : ℝ) + 1) / 20) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast,
      div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), h2]
  refine le_trans ?_ ha
  rw [h1]
  apply ENNReal.ofReal_le_ofReal
  linarith

end FrogModel.D3.Iface
