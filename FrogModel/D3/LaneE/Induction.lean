module

public import FrogModel.D3.LaneE.Basic

@[expose] public section

/-!
# Theorem 14.1 of the paper from the statements it reads

`thmDprime1_of` proves the interface statement `thmDprime1` from the statements it reads
(`measurable_plantedPair` and `lintegral_plantedG_le` of Lemmas 10.1 and 10.2, `lemma12_G` of
Lemma 11.1, `lemma10` of Lemma 11.5, `lemma9_two` of Lemma 11.4, `lemma8a` and `lemma8b` of
Lemma 10.6, `d1` of Lemma 10.5), taken as hypotheses (the `Prop` statements of the interfaces).
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneE

theorem mu_nonneg (m k : ℕ) : 0 ≤ mu m k := by unfold mu; positivity

theorem meanG_nonneg (m k : ℕ) : 0 ≤ meanG m k := ENNReal.toReal_nonneg

theorem meanG_le_mu (hfin : lintegral_plantedG_le) (m k : ℕ) : meanG m k ≤ mu m k := by
  unfold meanG
  exact ENNReal.toReal_le_of_le_ofReal (mu_nonneg m k) (hfin m k)

theorem meanG_mono (hfin : lintegral_plantedG_le) (m : ℕ) {k k' : ℕ} (hkk : k ≤ k') :
    meanG m k ≤ meanG m k' := by
  unfold meanG
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfin m k')) ?_
  refine lintegral_mono fun π => ?_
  have h : plantedG m k π ≤ plantedG m k' π :=
    monotone_nat_of_le_succ (f := fun j => plantedG m j π) (fun j => plantedG_mono m j π) hkk
  exact ENat.toENNReal_le.mpr h

theorem closProb_nonneg (m : ℕ) (A : Set ClosSample) : 0 ≤ closProb m A := ENNReal.toReal_nonneg

theorem closProb_le_one (m : ℕ) (A : Set ClosSample) : closProb m A ≤ 1 := by
  unfold closProb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem tailG_le_one (h k x : ℕ) : tailG h k x ≤ 1 := by
  unfold tailG
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

/-- `P(G_h(1) ≥ x) + P(G_h(1) ≤ x - 1) = 1` for `x ≥ 1`. -/
theorem tail_add_cdf (hmeas : measurable_plantedPair) (h x : ℕ) (hx : 1 ≤ x) :
    tailG h 1 x + cdfG h 1 (x - 1) = 1 := by
  have hm : Measurable fun π : PFrog → ℕ → Step 3 => plantedG h 1 π :=
    (measurable_pi_apply 1).comp (hmeas h).fst
  set S : Set (PFrog → ℕ → Step 3) := {π | plantedG h 1 π ≤ ((x - 1 : ℕ) : ℕ∞)} with hSdef
  have hS : MeasurableSet S := hm (MeasurableSet.of_discrete (s := {g : ℕ∞ | g ≤ ((x - 1 : ℕ) : ℕ∞)}))
  have hc : {π : PFrog → ℕ → Step 3 | (x : ℕ∞) ≤ plantedG h 1 π} = Sᶜ := by
    ext π
    simp only [hSdef, Set.mem_ofPred_eq, Set.mem_compl_iff]
    induction plantedG h 1 π using ENat.recTopCoe with
    | top => simp
    | coe n => simp only [Nat.cast_le]; omega
  unfold tailG cdfG
  rw [hc, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), add_comm,
    prob_add_prob_compl hS]
  simp

/-- The lower bound `jackLower` on the tail (`pi` of Section 14 of the paper), given by Lemma 11.1
when `E G_h(1) ≥ c0 mu_h(1)`. -/
theorem jackLower_le_tailG (hmeas : measurable_plantedPair) (h12 : lemma12_G)
    (h x : ℕ) (hx : 1 ≤ x) (hmean : c0 * mu h 1 ≤ meanG h 1) : jackLower h x ≤ tailG h 1 x := by
  have hD : deficit h 1 ≤ (1 - c0) * mu h 1 := by unfold deficit; linarith
  have hc := h12 h 1 (x - 1) _ hD
  unfold lemma12B at hc
  have hsum := tail_add_cdf hmeas h x hx
  have hx' : ((x - 1 : ℕ) : ℝ) + 1 = x := by rw [Nat.cast_sub hx]; push_cast; ring
  rw [hx'] at hc
  have htail0 : 0 ≤ tailG h 1 x := ENNReal.toReal_nonneg
  unfold jackLower
  split_ifs with h1
  · rw [ite_eq_left h1] at hc
    refine max_le htail0 ?_
    have hpos : 0 < mu h 1 - x := by linarith
    have hle : (deficit h 1 + Real.sqrt (mu h 1) / 2) / (mu h 1 - x) ≤
        ((1 - c0) * mu h 1 + Real.sqrt (mu h 1) / 2) / (mu h 1 - x) :=
      div_le_div_of_nonneg_right (by linarith) hpos.le
    linarith
  · exact htail0

/-- **Theorem 14.1 of the paper** from the statements it reads. -/
theorem thmDprime1_of (hmeas : measurable_plantedPair)
    (hfin : lintegral_plantedG_le) (h12 : lemma12_G) (h10 : lemma10)
    (h9 : lemma9_two) (h8a : lemma8a) (h8b : lemma8b)
    (hd1 : d1) : thmDprime1 := by
  intro J D k y k1 hJ62 hJmono hcond hB1 hB62
  have hm1 : m1 = 1778279 := rfl
  -- P(m): the bound at every height of (m1 - 30, m], and the mean at the comparison index
  have key : ∀ m, m1 ≤ m → (∀ h, m1 - 30 < h → h ≤ m → c0 * mu h 1 ≤ meanG h 1) ∧
      b1 + (1 / 3 - eps) * ((m : ℝ) - m1) ≤ meanG m (J m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact ⟨hB1, by rw [hJ62, sub_self, mul_zero, add_zero]; exact hB62⟩
    | succ m hm ih =>
      obtain ⟨ihA, ihB⟩ := ih
      obtain ⟨hJ1, hD1, hDm, hDlow, hk, hy, hk1, hK1, hK2⟩ := hcond m hm
      -- the two jackpots, at the heights m + 1 - D and m
      have hpD : jackLower (m + 1 - D m) (y m) ≤ tailG (m + 1 - D m) 1 (y m) :=
        jackLower_le_tailG hmeas h12 _ _ hy (ihA _ hDlow (by omega))
      have hp1 : jackLower m (k1 m) ≤ tailG m 1 (k1 m) :=
        jackLower_le_tailG hmeas h12 _ _ hk1 (ihA _ (by omega) le_rfl)
      -- the J-closure: P(e_1 < J) ≤ LJ(m)
      have hPJ : closProb m {x | closE (J m + 1) x.1 x.2 0 < J m} ≤ LJ m (J m) (D m) (k m) (y m) := by
        have hb2 := binLt_nonneg (y m) (k m) ((3 : ℝ)⁻¹ ^ (D m - 1)) (by positivity)
          (pow_le_one₀ (by norm_num) (by norm_num))
        have hb3 := binLt_nonneg (k m) (J m) (1 / 4) (by norm_num) (by norm_num)
        by_cases hc : 0 ≤ 2 / 3 - (J m : ℝ) * (3 : ℝ)⁻¹ ^ D m
        · have h10' := h10 m (J m + 1) (D m) (k m) (y m) (by omega) hD1 hDm hk hy
          have h8' := h8b m (J m) (J m) (k m) hJ1 hk
          have hq : ((J m + 1 : ℕ) : ℝ) - 1 = (J m : ℝ) := by push_cast; ring
          rw [hq] at h10'
          have ht1 := tailG_le_one (m + 1 - D m) 1 (y m)
          have hj := jackLower_mem (m + 1 - D m) (y m)
          have hc1 : 2 / 3 - (J m : ℝ) * (3 : ℝ)⁻¹ ^ D m ≤ 2 / 3 := by
            have : (0 : ℝ) ≤ (J m : ℝ) * (3 : ℝ)⁻¹ ^ D m := by positivity
            linarith
          have hpow : (1 - (2 / 3 - (J m : ℝ) * (3 : ℝ)⁻¹ ^ D m) * tailG (m + 1 - D m) 1 (y m)) ^ (J m + 1) ≤
              (1 - max 0 (2 / 3 - (J m : ℝ) * (3 : ℝ)⁻¹ ^ D m) * jackLower (m + 1 - D m) (y m)) ^ (J m + 1) := by
            rw [max_eq_right hc]
            apply pow_le_pow_left₀
            · nlinarith
            · nlinarith
          unfold LJ
          linarith
        · have h0 : max 0 (2 / 3 - (J m : ℝ) * (3 : ℝ)⁻¹ ^ D m) = 0 := max_eq_left (le_of_lt (not_le.mp hc))
          have h1 : 1 ≤ LJ m (J m) (D m) (k m) (y m) := by
            unfold LJ; rw [h0, zero_mul, sub_zero, one_pow]; linarith
          exact (closProb_le_one _ _).trans h1
      -- (K1): the loss of the J-closure is at most eps
      have hloss : lossL m (J m) (J m) ≤ eps := by
        calc lossL m (J m) (J m) ≤ meanG m (J m) * closProb m {x | closE (J m + 1) x.1 x.2 0 < J m} :=
              h8a m (J m) (J m) hJ1
          _ ≤ mu m (J m) * LJ m (J m) (D m) (k m) (y m) :=
              mul_le_mul (meanG_le_mu hfin _ _) hPJ (closProb_nonneg _ _) (mu_nonneg _ _)
          _ = ((m : ℝ) + J m + 1) / 3 * LJ m (J m) (D m) (k m) (y m) := by unfold mu; ring
          _ ≤ eps := hK1
      have hd := hd1 m (J m) (J m) hJ1
      have hJmon : J m ≤ J (m + 1) :=
        hJmono (Set.mem_Ici.mpr hm) (Set.mem_Ici.mpr (by omega)) (by omega)
      have hB' : b1 + (1 / 3 - eps) * (((m + 1 : ℕ) : ℝ) - m1) ≤ meanG (m + 1) (J (m + 1)) := by
        have := meanG_mono hfin (m + 1) hJmon
        push_cast
        linarith
      -- the 1-closure: P(e_1 < J) ≤ L1(m)
      have hP1 : closProb m {x | closE (1 + 1) x.1 x.2 0 < J m} ≤ L1 m (J m) (k1 m) := by
        have h8' := h8b m 1 (J m) (k1 m) le_rfl hk1
        have h9' := h9 m (k1 m) hk1
        have hS := oneSubSPoly_anti _ _ hp1 (tailG_le_one m 1 (k1 m))
        unfold L1
        linarith
      have hloss1 : lossL m 1 (J m) ≤ meanG m (J m) * L1 m (J m) (k1 m) :=
        (h8a m 1 (J m) le_rfl).trans (mul_le_mul_of_nonneg_left hP1 (meanG_nonneg _ _))
      have hd' := hd1 m 1 (J m) le_rfl
      push_cast at hd'
      have hmr : (m1 : ℝ) ≤ m := by exact_mod_cast hm
      have hA0 : 0 < b1 + (1 / 3 - eps) * ((m : ℝ) - m1) := by
        unfold b1 eps; nlinarith
      have hJ1r : (1 : ℝ) ≤ J m := by exact_mod_cast hJ1
      have hL1 : 0 ≤ 1 - L1 m (J m) (k1 m) := by
        by_contra hneg
        have := mul_neg_of_pos_of_neg hA0 (not_le.mp hneg)
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        unfold c0 at hK2
        linarith
      have hA' : c0 * mu (m + 1) 1 ≤ meanG (m + 1) 1 := by
        have hmu : mu (m + 1) 1 = ((m : ℝ) + 3) / 3 := by unfold mu; push_cast; ring
        rw [hmu]
        have h1 := mul_le_mul_of_nonneg_right ihB hL1
        have : c0 * ((m : ℝ) + 3) / 3 = c0 * (((m : ℝ) + 3) / 3) := by ring
        linarith
      refine ⟨fun h hh1 hh2 => ?_, hB'⟩
      rcases Nat.lt_or_ge h (m + 1) with hlt | hge
      · exact ihA h hh1 (by omega)
      · rw [show h = m + 1 by omega]; exact hA'
  intro m hm
  by_cases hle : m ≤ m1
  · exact hB1 m hm hle
  · exact (key m (by omega)).1 m hm le_rfl

end FrogModel.D3.LaneE
