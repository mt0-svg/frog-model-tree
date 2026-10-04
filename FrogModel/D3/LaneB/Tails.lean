module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# Real-valued tools (Abel summation, envelopes)

Self-contained lemmas for Lemma 11.3 of the paper.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- Abel summation: a nonincreasing weight `w ≥ 0` against masses whose partial sums are
dominated. -/
theorem abel_mono (w p q : ℕ → ℝ) (S : ℕ) (hw : ∀ s, w (s + 1) ≤ w s)
    (hw0 : ∀ s, 0 ≤ w s)
    (hcum : ∀ t < S, ∑ s ∈ Finset.range (t + 1), p s ≤ ∑ s ∈ Finset.range (t + 1), q s) :
    ∑ s ∈ Finset.range S, w s * p s ≤ ∑ s ∈ Finset.range S, w s * q s := by
  have hparts_p := Finset.sum_range_by_parts w p S
  have hparts_q := Finset.sum_range_by_parts w q S
  simp at hparts_p hparts_q
  rw [hparts_p, hparts_q]
  have hA : w (S - 1) * (∑ i ∈ Finset.range S, p i) ≤ w (S - 1) * (∑ i ∈ Finset.range S, q i) := by
    have hwS : 0 ≤ w (S - 1) := hw0 (S - 1)
    have hsum : (∑ i ∈ Finset.range S, p i) ≤ (∑ i ∈ Finset.range S, q i) := by
      by_cases hS : S = 0
      · subst hS; simp
      · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
        have hSm1_lt_S : S - 1 < S := Nat.sub_lt hSpos (by omega)
        have h_eq : (S - 1 : ℕ) + 1 = S := Nat.sub_add_cancel (by omega)
        have htemp := hcum (S - 1) hSm1_lt_S
        rw [h_eq] at htemp
        exact htemp
    exact mul_le_mul_of_nonneg_left hsum hwS
  have hB : (∑ x ∈ Finset.range (S - 1), (w (x + 1) - w x) * (∑ i ∈ Finset.range (x + 1), q i)) ≤
            (∑ x ∈ Finset.range (S - 1), (w (x + 1) - w x) * (∑ i ∈ Finset.range (x + 1), p i)) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    have hw_diff : w (x + 1) - w x ≤ 0 := by
      have h := hw x
      linarith
    have hsum_pq : (∑ i ∈ Finset.range (x + 1), p i) ≤ (∑ i ∈ Finset.range (x + 1), q i) := by
      have hx_lt_S : x < S := by
        have hx_range : x < S - 1 := Finset.mem_range.1 hx
        by_cases hS0 : S = 0
        · have : x < 0 := by simp [hS0] at hx
          omega
        · have hSpos : 0 < S := Nat.pos_of_ne_zero hS0
          omega
      exact hcum x hx_lt_S
    nlinarith
  linarith

/-- The envelope dominates `W` on `[s, S]`, is nonincreasing in `s` and nonnegative. -/
theorem envelope_props (W : ℕ → ℝ) (S s : ℕ) :
    (∀ s', s ≤ s' → s' ≤ S → W s' ≤ envelope W S s) ∧
      envelope W S (s + 1) ≤ envelope W S s ∧ 0 ≤ envelope W S s := by
  have h0 : 0 ≤ envelope W S s := by
    dsimp [envelope]
    rw [Finset.le_fold_max]
    left
    exact le_rfl
  have h_forall : ∀ s', s ≤ s' → s' ≤ S → W s' ≤ envelope W S s := by
    intro s' hs_le hs_le'
    dsimp [envelope]
    rw [Finset.le_fold_max]
    right
    refine ⟨s', Finset.mem_Icc.mpr ⟨hs_le, hs_le'⟩, ?_⟩
    rfl
  have h_mono : envelope W S (s + 1) ≤ envelope W S s := by
    dsimp [envelope]
    rw [Finset.fold_max_le]
    refine ⟨h0, ?_⟩
    intro x hx
    rcases Finset.mem_Icc.mp hx with ⟨hx1, hx2⟩
    rw [Finset.le_fold_max]
    right
    refine ⟨x, Finset.mem_Icc.mpr ⟨Nat.le_of_succ_le hx1, hx2⟩, ?_⟩
    rfl
  refine And.intro ?_ ?_
  · exact h_forall
  · exact And.intro h_mono h0

/-- The envelope of a weight vanishing beyond `GM` vanishes beyond `GM`. -/
theorem envelope_zero (W : ℕ → ℝ) (GM S s : ℕ) (hW : ∀ s, GM < s → W s = 0)
    (hs : GM < s) : envelope W S s = 0 := by
  unfold envelope
  have hle : (Finset.Icc s S).fold max 0 W ≤ 0 := by
    rw [Finset.fold_max_le]
    constructor
    · rfl
    · intro x hx
      rcases Finset.mem_Icc.mp hx with ⟨hx1, hx2⟩
      have hxGM : GM < x := lt_of_lt_of_le hs hx1
      rw [hW x hxGM]
  have hge : 0 ≤ (Finset.Icc s S).fold max 0 W := by
    rw [Finset.le_fold_max]
    left
    rfl
  exact le_antisymm hle hge

/-- Convolution with a nondecreasing nonnegative `H` keeps a domination of partial sums. -/
theorem conv_cdf_mono (p r H : ℕ → ℝ) (t : ℕ) (hH : Monotone H)
    (hH0 : ∀ u, 0 ≤ H u)
    (hcum : ∀ u ≤ t, ∑ g ∈ Finset.range (u + 1), p g ≤ ∑ g ∈ Finset.range (u + 1), r g) :
    ∑ g ∈ Finset.range (t + 1), p g * H (t - g) ≤ ∑ g ∈ Finset.range (t + 1), r g * H (t - g) := by
  set w := fun (i : ℕ) => H (t - i) with hw_def
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w]
    apply hH0
  have hw_anti : ∀ i, w (i + 1) ≤ w i := by
    intro i
    dsimp [w]
    apply hH
    omega
  -- rewrite the goal using w
  have hgoal : (∑ g ∈ Finset.range (t + 1), p g * H (t - g)) = (∑ g ∈ Finset.range (t + 1), w g * p g) := by
    simp [w, mul_comm]
  have hgoal_r : (∑ g ∈ Finset.range (t + 1), r g * H (t - g)) = (∑ g ∈ Finset.range (t + 1), w g * r g) := by
    simp [w, mul_comm]
  rw [hgoal, hgoal_r]
  -- summation by parts
  have hparts_p := Finset.sum_range_by_parts w p (t + 1)
  have hparts_r := Finset.sum_range_by_parts w r (t + 1)
  simp_rw [smul_eq_mul] at hparts_p hparts_r
  -- simplify the index arithmetic
  have ht1 : (t + 1 : ℕ) - 1 = t := by omega
  simp [ht1] at hparts_p hparts_r
  -- Now hparts_p: ∑ w_i * p_i = w_t * P_t - ∑_{i<t} (w_{i+1} - w_i) * P_i
  -- hparts_r: similarly
  rw [hparts_p, hparts_r]
  -- Goal: w t * P_t - S_p ≤ w t * R_t - S_r
  have hPt_le_Rt : (∑ i ∈ Finset.range (t + 1), p i) ≤ (∑ i ∈ Finset.range (t + 1), r i) := by
    apply hcum t
    omega
  have h_wt_nonneg : 0 ≤ w t := hw_nonneg t
  have h_mul : w t * (∑ i ∈ Finset.range (t + 1), p i) ≤ w t * (∑ i ∈ Finset.range (t + 1), r i) := by
    nlinarith
  -- We need: S_r ≤ S_p, i.e., ∑ (w(i+1)-w i) * R_i ≤ ∑ (w(i+1)-w i) * P_i
  have h_sum : (∑ i ∈ Finset.range t, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), r j)) ≤
              (∑ i ∈ Finset.range t, (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), p j)) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi_lt_t : i < t := by simpa [Finset.mem_range] using hi
    have hi_le_t : i ≤ t := Nat.le_of_lt hi_lt_t
    have hPi_le_Ri : (∑ j ∈ Finset.range (i + 1), p j) ≤ (∑ j ∈ Finset.range (i + 1), r j) := hcum i hi_le_t
    have h_diff_nonpos : w (i + 1) - w i ≤ 0 := by linarith [hw_anti i]
    nlinarith
  apply sub_le_sub h_mul h_sum

/-- The real part of Lemma 11.3 (1) of the paper: a weight `W ≥ 0` against masses `p` is at most its
envelope against masses `r` whose partial sums dominate those of `p` below `S`. -/
theorem lemma16C_real (W p r : ℕ → ℝ) (S : ℕ) (_hW0 : ∀ s, 0 ≤ W s)
    (hp0 : ∀ s, 0 ≤ p s)
    (hcum : ∀ t < S, ∑ s ∈ Finset.range (t + 1), p s ≤ ∑ s ∈ Finset.range (t + 1), r s) :
    ∑ s ∈ Finset.range S, W s * p s ≤ ∑ s ∈ Finset.range S, envelope W S s * r s := by
  -- Define w s = envelope W S s if s ≤ S, else 0
  let w : ℕ → ℝ := fun s => if s ≤ S then envelope W S s else 0
  have hw_props (s : ℕ) := envelope_props W S s
  have hw_noninc : ∀ s, w (s + 1) ≤ w s := by
    intro s
    dsimp [w]
    by_cases h : s + 1 ≤ S
    · rw [ite_eq_left h]
      by_cases hs : s ≤ S
      · rw [ite_eq_left hs]
        exact (hw_props s).2.1
      · exfalso
        have hs_lt_S : s < S := Nat.lt_of_lt_of_le (Nat.lt_succ_self s) h
        exact hs hs_lt_S.le
    · rw [ite_eq_right h]
      by_cases hs : s ≤ S
      · rw [ite_eq_left hs]
        exact (hw_props s).2.2
      · rw [ite_eq_right hs]
  have hw_nonneg : ∀ s, 0 ≤ w s := by
    intro s
    dsimp [w]
    by_cases hs : s ≤ S
    · rw [ite_eq_left hs]
      exact (hw_props s).2.2
    · rw [ite_eq_right hs]
  have hW_le_w : ∀ s, s < S → W s ≤ w s := by
    intro s hs
    dsimp [w]
    have hs_le_S : s ≤ S := hs.le
    rw [ite_eq_left hs_le_S]
    exact (hw_props s).1 s (le_refl s) hs_le_S
  have h_sum1 : ∑ s ∈ Finset.range S, W s * p s ≤ ∑ s ∈ Finset.range S, w s * p s := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hiS : i < S := Finset.mem_range.1 hi
    have hWi : W i ≤ w i := hW_le_w i hiS
    exact mul_le_mul_of_nonneg_right hWi (hp0 i)
  have h_sum2 : ∑ s ∈ Finset.range S, w s * p s ≤ ∑ s ∈ Finset.range S, w s * r s :=
    abel_mono w p r S hw_noninc hw_nonneg hcum
  have h_sum3 : ∑ s ∈ Finset.range S, w s * r s = ∑ s ∈ Finset.range S, envelope W S s * r s := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiS : i < S := Finset.mem_range.1 hi
    dsimp [w]
    rw [ite_eq_left hiS.le]
  calc
    ∑ s ∈ Finset.range S, W s * p s ≤ ∑ s ∈ Finset.range S, w s * p s := h_sum1
    _ ≤ ∑ s ∈ Finset.range S, w s * r s := h_sum2
    _ = ∑ s ∈ Finset.range S, envelope W S s * r s := h_sum3

/-- Binomial masses are nonnegative and sum to one; the cdf and the lower tail are at most one. -/
theorem binCdf_facts (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ i, 0 ≤ binPmf n p i) ∧ ∑ i ∈ Finset.range (n + 1), binPmf n p i = 1 ∧
      (∀ v, binCdf n p v ≤ 1) ∧ (∀ J, binLt n p J ≤ 1) ∧ (∀ E, 0 ≤ binGe n p E) := by
  have h_pmf_nonneg : ∀ i, 0 ≤ binPmf n p i := by
    intro i
    unfold binPmf
    positivity
  have h_sum_eq_one : ∑ i ∈ Finset.range (n + 1), binPmf n p i = 1 := by
    calc
      ∑ i ∈ Finset.range (n + 1), binPmf n p i
          = ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) := by
        simp [binPmf]
      _ = ∑ i ∈ Finset.range (n + 1), (p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        ring
      _ = (p + (1 - p)) ^ n := by
        rw [add_pow]
      _ = 1 ^ n := by ring
      _ = 1 := by simp
  have h_pmf_eq_zero : ∀ i, n < i → binPmf n p i = 0 := by
    intro i hi
    unfold binPmf
    have h_choose : (n.choose i : ℝ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero]
    simp [h_choose]
  have h_cdf_le_one : ∀ v, binCdf n p v ≤ 1 := by
    intro v
    unfold binCdf
    have h_sum_eq_inter : ∑ i ∈ Finset.range (v + 1), binPmf n p i =
        ∑ i ∈ (Finset.range (v + 1)) ∩ (Finset.range (n + 1)), binPmf n p i := by
      apply (Finset.sum_subset (Finset.inter_subset_left) ?_).symm
      intro i hi hmem
      have : i ∉ Finset.range (n + 1) := by
        intro hi2
        apply hmem
        exact Finset.mem_inter.mpr ⟨hi, hi2⟩
      have : n < i := by
        rw [Finset.mem_range] at this
        omega
      exact h_pmf_eq_zero i this
    have h_sum_inter_le : ∑ i ∈ (Finset.range (v + 1)) ∩ (Finset.range (n + 1)), binPmf n p i ≤
        ∑ i ∈ Finset.range (n + 1), binPmf n p i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by
        intro i hi hi_not
        exact h_pmf_nonneg i)
    rw [h_sum_eq_inter]
    rw [h_sum_eq_one] at h_sum_inter_le
    exact h_sum_inter_le
  have h_lt_le_one : ∀ J, binLt n p J ≤ 1 := by
    intro J
    unfold binLt
    have h_sum_eq_inter : ∑ i ∈ Finset.range J, binPmf n p i =
        ∑ i ∈ (Finset.range J) ∩ (Finset.range (n + 1)), binPmf n p i := by
      apply (Finset.sum_subset (Finset.inter_subset_left) ?_).symm
      intro i hi hmem
      have : i ∉ Finset.range (n + 1) := by
        intro hi2
        apply hmem
        exact Finset.mem_inter.mpr ⟨hi, hi2⟩
      have : n < i := by
        rw [Finset.mem_range] at this
        omega
      exact h_pmf_eq_zero i this
    have h_sum_inter_le : ∑ i ∈ (Finset.range J) ∩ (Finset.range (n + 1)), binPmf n p i ≤
        ∑ i ∈ Finset.range (n + 1), binPmf n p i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by
        intro i hi hi_not
        exact h_pmf_nonneg i)
    rw [h_sum_eq_inter]
    rw [h_sum_eq_one] at h_sum_inter_le
    exact h_sum_inter_le
  have h_ge_nonneg : ∀ E, 0 ≤ binGe n p E := by
    intro E
    unfold binGe
    apply Finset.sum_nonneg
    intro i hi
    exact h_pmf_nonneg i
  exact ⟨h_pmf_nonneg, h_sum_eq_one, h_cdf_le_one, h_lt_le_one, h_ge_nonneg⟩

end FrogModel.D3.Iface
