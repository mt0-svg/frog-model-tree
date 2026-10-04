module

public import FrogModel.D3.Interfaces.Seed
public import FrogModel.D3.LaneC.Lemma18

@[expose] public section

/-!
# The seed lemma (Lemma 13.4 of the paper)

`seed_valid_of` is the seed lemma from the statements it uses, taken as hypotheses (the `Prop`
statements of the interfaces), as in `ext_valid_of`.

The deficits: `Delta_m0(k) ≤ mu_m0(k)`, and for `1 ≤ k' ≤ k`, `Delta_m0(k) ≤ Delta_m0(k')`
(Lemma 10.7 (1)) `= mu_m0(k') - E G_m0(k') ≤ mu_m0(k') - e_k'`; so `Delta_m0(k) ≤ D0(k)
= delta0(k) mu_m0(k)`. The cdf rows: each term of `preSeed` bounds `P(G_m0(k) ≤ g)`: `R` by the
hypothesis on `c_k`, `C` by the coins, `L` and `t<i>` by the bounds of Lemma 11.1 (3) at `D0(k)`,
`J` by the monotonicity in `k`; the minimum over `g' ≥ g` by that in `g`.
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC

/-- The `L` term of a cdf row (the bounds of Lemma 11.1 (3) of the paper), at any `D ≥ Delta_m(k)`. -/
theorem cdfG_le_L12 (h12 : lemma12_G) (h12' : lemma12'_G) (m k g : ℕ) (D : ℝ)
    (hD : deficit m k ≤ D) : cdfG m k g ≤ L12 D (mu m k) g := by
  unfold L12
  refine le_min (h12 m k g _ hD) ?_
  rw [Finset.le_fold_min]
  refine ⟨cdfG_le_one' _ _ _, fun i hi => ?_⟩
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hi2' : (i : ℝ) ≤ 199 := by exact_mod_cast hi2
  exact h12' m k g _ _ hD (by positivity) (by rw [div_lt_one (by norm_num)]; linarith)

section Seed

variable (h17a : lemma17a) (h12 : lemma12_G) (h12' : lemma12'_G)
  (hC : cdfG_le_binCdf) (V m0 : ℕ) (P : StParams) (W : ℕ → ℕ → ℝ)
  (hc : ∀ k, 1 ≤ k → k ≤ P.E → ∀ g < V, cdfG m0 k g ≤ cS W V k g)
  (he : ∀ k, 1 ≤ k → k ≤ P.E → eS W V k ≤ meanG m0 k)

include h17a he in
/-- `Delta_m0(k) ≤ D0(k)` for `k ≤ E`. -/
theorem deficit_le_D0 (k : ℕ) (hk : k ≤ P.E) : deficit m0 k ≤ D0 W V m0 k := by
  unfold D0
  rw [Finset.le_fold_min]
  refine ⟨deficit_le_mu _ _, fun k' hk' => ?_⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk'
  calc deficit m0 k ≤ deficit m0 k' := deficit_anti h17a m0 h2
    _ = mu m0 k' - meanG m0 k' := rfl
    _ ≤ mu m0 k' - eS W V k' := by linarith [he k' h1 (h2.trans hk)]

include h17a h12 h12' hC hc he in
theorem cdfG_le_preSeed (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ P.E) (g : ℕ) (prev : ℝ)
    (hprev : cdfG m0 k g ≤ prev) : cdfG m0 k g ≤ preSeed W V m0 k g prev := by
  unfold preSeed
  refine le_min (le_min ?_ (hC m0 k g)) (le_min ?_ hprev)
  · split_ifs with hg
    · exact hc k hk1 hk g hg
    · exact cdfG_le_one' _ _ _
  · exact cdfG_le_L12 h12 h12' m0 k g _ (deficit_le_D0 h17a V m0 P W he k hk)

include h17a h12 h12' hC hc he in
theorem cdfG_le_F0 : ∀ k ≤ P.E, ∀ g ≤ P.GM, cdfG m0 k g ≤ F0 W V m0 P.GM k g
  | 0, _, g, _ => by
      simp only [F0]
      exact cdfG_le_one' _ _ _
  | k + 1, hk, g, hg => by
      simp only [F0]
      rw [Finset.le_fold_min]
      have hk' : k ≤ P.E := by omega
      refine ⟨cdfG_le_preSeed h17a h12 h12' hC V m0 P W hc he (k + 1) (by omega) hk g _
        ((cdfG_succ_le _ _ _).trans (cdfG_le_F0 k hk' g hg)), fun g' hg' => ?_⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hg'
      exact (cdfG_mono_g _ _ h1).trans (cdfG_le_preSeed h17a h12 h12' hC V m0 P W hc he (k + 1)
        (by omega) hk g' _ ((cdfG_succ_le _ _ _).trans (cdfG_le_F0 k hk' g' h2)))

end Seed

/-- **The seed lemma** (Lemma 13.4 of the paper), from the statements of Lemmas 10.7 (1) and 11.1. -/
theorem seed_valid_of (h17a : lemma17a) (h12 : lemma12_G)
    (h12' : lemma12'_G) (hC : cdfG_le_binCdf) : seed_valid := by
  intro V m0 P W hc he
  refine ⟨fun k hk g hg => cdfG_le_F0 h17a h12 h12' hC V m0 P W hc he k hk g hg, fun k hk => ?_⟩
  change deficit m0 k ≤ D0 W V m0 k / mu m0 k * mu m0 k
  rw [div_mul_cancel₀ _ (mu_pos m0 k).ne']
  exact deficit_le_D0 h17a V m0 P W he k hk

end FrogModel.D3.LaneC
