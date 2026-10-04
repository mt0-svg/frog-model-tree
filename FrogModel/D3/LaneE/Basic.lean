module

public import FrogModel.D3.Interfaces.DPrime

@[expose] public section

/-!
# The one-height facts behind (K1) and (K2)

Pieces of the proof of Lemma 14.2 of the paper. The tilt bound for the binomial tails (pure
algebra), `jackLower` monotone in the height and its rational lower bound, the antitone first terms,
and the reduction of (K1), (K2) on an interval to closed inequalities at its ends.
-/

open FrogModel.D3.Iface

namespace FrogModel.D3.LaneE

/-- The tilt: `P(Bin(n, p) < J) ≤ (1 - p + p z)^n / z^(J - 1)` for `0 < z ≤ 1`. -/
theorem tilt_binLt (n J : ℕ) (p z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    binLt n p J ≤ (1 - p + p * z) ^ n / z ^ (J - 1) := by
  have hz' : 0 < z ^ (J - 1) := pow_pos hz0 _
  have hq : 0 ≤ 1 - p := by linarith
  rw [le_div_iff₀ hz']
  unfold binLt binPmf
  rw [Finset.sum_mul]
  set g : ℕ → ℝ := fun i => (p * z) ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ) with hg
  have hg0 : ∀ i, 0 ≤ g i := fun i => by rw [hg]; positivity
  have hstep : ∀ i ∈ Finset.range J,
      (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) * z ^ (J - 1) ≤ g i := by
    intro i hi
    have hiJ : i ≤ J - 1 := by rw [Finset.mem_range] at hi; omega
    have hzz : z ^ (J - 1) ≤ z ^ i := pow_le_pow_of_le_one hz0.le hz1 hiJ
    have h0 : 0 ≤ (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) := by positivity
    calc (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) * z ^ (J - 1)
        ≤ (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) * z ^ i := mul_le_mul_of_nonneg_left hzz h0
      _ = g i := by rw [hg]; ring
  calc ∑ i ∈ Finset.range J, (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) * z ^ (J - 1)
      ≤ ∑ i ∈ Finset.range J, g i := Finset.sum_le_sum hstep
    _ ≤ ∑ i ∈ Finset.range (max J (n + 1)), g i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (le_max_left _ _))
        (fun i _ _ => hg0 i)
    _ = ∑ i ∈ Finset.range (n + 1), g i := by
      refine (Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) ?_).symm
      intro i _ hni
      rw [Finset.mem_range, not_lt] at hni
      rw [hg]; simp [Nat.choose_eq_zero_of_lt (show n < i by omega)]
    _ = (p * z + (1 - p)) ^ n := (add_pow _ _ _).symm
    _ = (1 - p + p * z) ^ n := by ring

theorem one_sub_pow_le_exp (x : ℝ) (n : ℕ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) ^ n ≤ Real.exp (-((n : ℝ) * x)) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  calc (1 - x) ^ n ≤ Real.exp (-x) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp (-((n : ℝ) * x)) := by rw [← Real.exp_nat_mul]; ring_nf

theorem exp_neg_one_le : Real.exp (-1) ≤ 3 / 8 := by
  have h := Real.exp_one_gt_d9
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  norm_num at h ⊢
  linarith

theorem jackLower_mono (h h' x : ℕ) (hh : h ≤ h') : jackLower h x ≤ jackLower h' x := by
  have hmu : mu h 1 ≤ mu h' 1 := by unfold mu; gcongr
  unfold jackLower
  by_cases hx : (x : ℝ) < mu h 1
  · have hx' : (x : ℝ) < mu h' 1 := lt_of_lt_of_le hx hmu
    rw [ite_eq_left hx, ite_eq_left hx']
    refine max_le_max le_rfl ?_
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
    have hμ0 : 0 ≤ mu h 1 := by linarith
    set s := √(mu h 1) with hs
    set s' := √(mu h' 1) with hs'
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hss : s ≤ s' := Real.sqrt_le_sqrt hmu
    have h2 : s ^ 2 = mu h 1 := Real.sq_sqrt hμ0
    have h2' : s' ^ 2 = mu h' 1 := Real.sq_sqrt (by linarith)
    have hB : 0 < mu h 1 - x := by linarith
    have hB' : 0 < mu h' 1 - x := by linarith
    rw [sub_le_sub_iff_left, div_le_div_iff₀ hB' hB]
    unfold c0
    rw [← h2, ← h2']
    have e1 : 0 ≤ (s' - s) * x := mul_nonneg (by linarith) hx0
    have e2 : 0 ≤ (s' ^ 2 - s ^ 2) * x := mul_nonneg (by nlinarith) hx0
    have e3 : 0 ≤ s * s' * (s' - s) := mul_nonneg (mul_nonneg hs0 (by linarith)) (by linarith)
    nlinarith
  · rw [ite_eq_right hx]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl

theorem jackLower_mem (h x : ℕ) : 0 ≤ jackLower h x ∧ jackLower h x ≤ 1 := by
  unfold jackLower
  split_ifs with hx
  · refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    have hμ : 0 ≤ mu h 1 := le_trans (Nat.cast_nonneg x) hx.le
    have hB : 0 < mu h 1 - x := by linarith
    have : 0 ≤ ((1 - c0) * mu h 1 + Real.sqrt (mu h 1) / 2) / (mu h 1 - x) := by
      unfold c0; positivity
    linarith
  · exact ⟨le_rfl, zero_le_one⟩

theorem jackLower_ge (h x : ℕ) (s p : ℝ) (hs : 0 ≤ s) (hs2 : mu h 1 ≤ s ^ 2) (hx : (x : ℝ) < mu h 1)
    (hp : p ≤ 1 - ((1 - c0) * mu h 1 + s / 2) / (mu h 1 - x)) : p ≤ jackLower h x := by
  unfold jackLower
  rw [ite_eq_left hx]
  refine le_trans ?_ (le_max_right _ _)
  refine hp.trans ?_
  have hB : 0 < mu h 1 - x := by linarith [Nat.cast_nonneg (α := ℝ) x]
  have hsq : Real.sqrt (mu h 1) ≤ s := by
    rw [show s = Real.sqrt (s ^ 2) from (Real.sqrt_sq hs).symm]; exact Real.sqrt_le_sqrt hs2
  rw [sub_le_sub_iff_left]
  exact div_le_div_of_nonneg_right (by linarith) hB.le

theorem oneSubSPoly_anti (p p' : ℝ) (hpp : p ≤ p') (hp' : p' ≤ 1) : 1 - SPoly p' ≤ 1 - SPoly p := by
  unfold SPoly
  nlinarith

theorem K2_of_base (m ml J : ℕ) (L L' : ℝ) (hml : m1 ≤ ml) (hm : ml ≤ m) (hLL : L' ≤ L)
    (hslope : c0 / 3 ≤ (1 / 3 - eps) * (1 - L))
    (hbase : (c0 * ((ml : ℝ) + 3) + J - 2) / 3 ≤ (b1 + (1 / 3 - eps) * ((ml : ℝ) - m1)) * (1 - L)) :
    c0 * ((m : ℝ) + 3) / 3 ≤ (b1 + (1 / 3 - eps) * ((m : ℝ) - m1)) * (1 - L') - ((J : ℝ) - 2) / 3 := by
  have hmlR : (m1 : ℝ) ≤ ml := by exact_mod_cast hml
  have hmR : (ml : ℝ) ≤ m := by exact_mod_cast hm
  have hX : 0 ≤ b1 + (1 / 3 - eps) * ((m : ℝ) - m1) := by unfold b1 eps; nlinarith
  have h1 := mul_le_mul_of_nonneg_left (show 1 - L ≤ 1 - L' by linarith) hX
  have h2 := mul_le_mul_of_nonneg_left hslope (show (0 : ℝ) ≤ m - ml by linarith)
  unfold c0 eps b1 at *
  nlinarith

theorem LJ_le (m ml J D k y : ℕ) (p t2 t3 : ℝ) (hm : ml ≤ m) (hD : D ≤ ml + 1)
    (hco : 0 ≤ 2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) (_hp0 : 0 ≤ p) (hp : p ≤ jackLower (ml + 1 - D) y)
    (ht2 : binLt y ((3 : ℝ)⁻¹ ^ (D - 1)) k ≤ t2) (ht3 : binLt k (1 / 4) J ≤ t3) :
    LJ m J D k y ≤ (1 - (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * p) ^ (J + 1) + t2 + t3 := by
  unfold LJ
  rw [max_eq_right hco]
  have hmono := jackLower_mono (ml + 1 - D) (m + 1 - D) y (by omega)
  have hmem := jackLower_mem (m + 1 - D) y
  have hc : 2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D ≤ 2 / 3 := by
    have : (0 : ℝ) ≤ (J : ℝ) * (3 : ℝ)⁻¹ ^ D := by positivity
    linarith
  have hlo : 0 ≤ 1 - (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * jackLower (m + 1 - D) y := by
    have := mul_le_mul hc hmem.2 hmem.1 (by norm_num)
    linarith
  have hle : (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * p ≤
      (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * jackLower (m + 1 - D) y :=
    mul_le_mul_of_nonneg_left (hp.trans hmono) hco
  have := pow_le_pow_left₀ hlo (show 1 - (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * jackLower (m + 1 - D) y ≤
    1 - (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * p by linarith) (J + 1)
  linarith

theorem L1_le (m ml J k1 : ℕ) (p t9 : ℝ) (hm : ml ≤ m) (hp : p ≤ jackLower ml k1)
    (ht9 : binLt k1 (1 / 4) J ≤ t9) : L1 m J k1 ≤ 1 - SPoly p + t9 := by
  unfold L1
  have hmono := jackLower_mono ml m k1 hm
  have := oneSubSPoly_anti p (jackLower m k1) (hp.trans hmono) (jackLower_mem m k1).2
  linarith

/-- `binLt` is a sum of nonnegative terms for `0 ≤ p ≤ 1`. -/
theorem binLt_nonneg (n J : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binLt n p J := by
  unfold binLt binPmf
  refine Finset.sum_nonneg fun i _ => ?_
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem LJ_nonneg (m J D k y : ℕ) : 0 ≤ LJ m J D k y := by
  unfold LJ
  have hj := jackLower_mem (m + 1 - D) y
  have h3 : (0 : ℝ) ≤ (3 : ℝ)⁻¹ ^ (D - 1) := by positivity
  have h3' : (3 : ℝ)⁻¹ ^ (D - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hc : max 0 (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) ≤ 2 / 3 := by
    refine max_le (by norm_num) ?_
    have : (0 : ℝ) ≤ (J : ℝ) * (3 : ℝ)⁻¹ ^ D := by positivity
    linarith
  have hc0 : 0 ≤ max 0 (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) := le_max_left _ _
  have h1 : 0 ≤ 1 - max 0 (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * jackLower (m + 1 - D) y := by
    nlinarith [hj.1, hj.2]
  have := binLt_nonneg y k _ h3 h3'
  have := binLt_nonneg k J (1 / 4) (by norm_num) (by norm_num)
  positivity

end FrogModel.D3.LaneE
