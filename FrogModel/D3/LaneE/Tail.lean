module

public import FrogModel.D3.LaneE.Interval
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# (K1) and (K2) past 10^30

The proof of Lemma 14.3 of the paper. For `m ≥ 10^30` and `r = m^(1/4)`:
`J = max(140, ⌈(11/5) ln m⌉)` has `m ≤ e^(5J/11) ≤ (197/125)^J` and `J ≤ 9 r` (from `ln m ≤ 4 r`);
`3^(D-1) < 100 J ≤ 3^D`, so `2/3 - J 3^-D ≥ 197/300`, `D ≤ 100 J ≤ m/2` and `y < 1800 J^2`; both
jackpots are at least `59/100` (`jackLower_ge_big`: a mean above `10^20`, a threshold below `10^6`
times its square root); the two binomial tails are the tilt bounds of Interval.lean at `h = 6`,
`c = 12`. (K1) reduces to a closed inequality in `J ≥ 140` whose bases are below `1`
(`tail_K1_num`), (K2) to a linear inequality in `m` with slope margin `0.0017`.
-/

open FrogModel.D3.Iface

namespace FrogModel.D3.LaneE

theorem exp_five_eleventh_le : Real.exp (5 / 11) ≤ 197 / 125 := by
  have h1 : Real.exp (5 / 11) ^ 11 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
  have h3 : (2.7182818286 : ℝ) ^ 5 ≤ (197 / 125) ^ 11 := by norm_num
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (11 : ℕ) ≠ 0)).mp
    (h1 ▸ h2.trans h3)

theorem tail_regroup (R q A B : ℝ) (J : ℕ) :
    R ^ J * (q ^ (J + 1) + A ^ J + B ^ J) = q * (R * q) ^ J + (R * A) ^ J + (R * B) ^ J := by
  rw [pow_succ, mul_pow, mul_pow, mul_pow]; ring

/-- (K1) past `10^30` as a closed inequality in `J ≥ 140`. -/
theorem tail_K1_num (J : ℕ) (hJ : 140 ≤ J) :
    (2 / 3 : ℝ) * ((197 / 125) ^ J * ((18377 / 30000) ^ (J + 1) + ((3 / 8) ^ 6 * (3 / 2) ^ 12) ^ J +
      ((9 / 11) ^ 12 * (11 / 3)) ^ J)) ≤ 1 / 50 := by
  have hQ : (2 / 3 : ℚ) * ((18377 / 30000) * ((197 / 125) * (18377 / 30000)) ^ 140 +
      ((197 / 125) * ((3 / 8) ^ 6 * (3 / 2) ^ 12)) ^ 140 +
      ((197 / 125) * ((9 / 11) ^ 12 * (11 / 3))) ^ 140) ≤ 1 / 50 := by
    decide +kernel
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  push_cast at hR
  rw [tail_regroup]
  have a1 : ((197 / 125 : ℝ) * (18377 / 30000)) ^ J ≤ ((197 / 125 : ℝ) * (18377 / 30000)) ^ 140 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
  have a2 : ((197 / 125 : ℝ) * ((3 / 8) ^ 6 * (3 / 2) ^ 12)) ^ J ≤
      ((197 / 125 : ℝ) * ((3 / 8) ^ 6 * (3 / 2) ^ 12)) ^ 140 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
  have a3 : ((197 / 125 : ℝ) * ((9 / 11) ^ 12 * (11 / 3))) ^ J ≤
      ((197 / 125 : ℝ) * ((9 / 11) ^ 12 * (11 / 3))) ^ 140 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
  linarith

/-- The tilt for `Bin(12 J, 1/4)` below `J`. -/
theorem tail_t3 (J : ℕ) : binLt (12 * J) (1 / 4) J ≤ ((9 / 11 : ℝ) ^ 12 * (11 / 3)) ^ J := by
  refine (Entry.binLt_quarter_le (12 * J) J 12 (by norm_num)).trans ?_
  have hq : ((1 - 1 / 4 + 1 / 4 * (3 / (((12 : ℕ) : ℚ) - 1))) ^ (12 * J) /
      (3 / (((12 : ℕ) : ℚ) - 1)) ^ (J - 1) : ℚ) ≤ ((9 / 11 : ℚ) ^ 12 * (11 / 3)) ^ J := by
    rw [show (1 - 1 / 4 + 1 / 4 * (3 / (((12 : ℕ) : ℚ) - 1))) = 9 / 11 by norm_num,
      show (3 / (((12 : ℕ) : ℚ) - 1)) = 3 / 11 by norm_num, div_eq_mul_inv, ← inv_pow,
      show (3 / 11 : ℚ)⁻¹ = 11 / 3 by norm_num, mul_pow, ← pow_mul, mul_comm 12 J]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)) (by positivity)
  have := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at this ⊢
  exact this

/-- The tilt for `Bin(18 J 3^(D-1), 3^(1-D))` below `12 J`. -/
theorem tail_t2 (J D : ℕ) (hD : 1 ≤ D) :
    binLt (18 * J * 3 ^ (D - 1)) ((3 : ℝ)⁻¹ ^ (D - 1)) (12 * J) ≤ ((3 / 8 : ℝ) ^ 6 * (3 / 2) ^ 12) ^ J := by
  have h := Entry.binLt_y_le ⟨0, 0, J, D, 6, 12, 0, 0⟩ hD
  have hy : Entry.y ⟨0, 0, J, D, 6, 12, 0, 0⟩ = 18 * J * 3 ^ (D - 1) := by
    show 3 * 6 * J * 3 ^ (D - 1) = _; ring
  have hk : Entry.k ⟨0, 0, J, D, 6, 12, 0, 0⟩ = 12 * J := by
    show 2 * 6 * J = _; ring
  rw [hy, hk] at h
  refine h.trans ?_
  have hq : Entry.t2 ⟨0, 0, J, D, 6, 12, 0, 0⟩ ≤ ((3 / 8 : ℚ) ^ 6 * (3 / 2) ^ 12) ^ J := by
    show (3 / 8 : ℚ) ^ (6 * J) * (3 / 2) ^ (2 * 6 * J - 1) ≤ _
    rw [mul_pow, ← pow_mul, ← pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  have := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at this
  exact this

/-- `ln x ≤ 4 x^(1/4)`. -/
theorem log_le_four_rt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 4 * √√x := by
  have h1 : Real.log x = 4 * Real.log √√x := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx.le]; ring
  rw [h1]
  have := Real.log_le_sub_one_of_pos (show 0 < √√x by positivity)
  linarith

/-- Both jackpots past `10^30`: `59/100 ≤ jackLower h x` when `mu_h(1) ≥ 10^20` and
`x^2 ≤ 10^12 mu_h(1)`. -/
theorem jackLower_ge_big (h x : ℕ) (hmu : 10 ^ 20 ≤ mu h 1) (hx : (x : ℝ) ^ 2 ≤ 10 ^ 12 * mu h 1) :
    59 / 100 ≤ jackLower h x := by
  have hμ0 : 0 ≤ mu h 1 := le_trans (by positivity) hmu
  set s := √(mu h 1) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = mu h 1 := Real.sq_sqrt hμ0
  have hs : (10 : ℝ) ^ 10 ≤ s := by
    by_contra hlt
    rw [not_le] at hlt
    have := pow_lt_pow_left₀ hlt hs0 (two_ne_zero)
    rw [hs2] at this
    linarith
  have hxs : (x : ℝ) ≤ 10 ^ 6 * s := by
    by_contra hlt
    rw [not_le] at hlt
    have := pow_lt_pow_left₀ hlt (by positivity) (two_ne_zero)
    rw [mul_pow, hs2] at this
    linarith
  have hss := mul_le_mul_of_nonneg_left hs hs0
  have hxμ : (x : ℝ) < mu h 1 := by nlinarith
  refine jackLower_ge h x s (59 / 100) hs0 hs2.ge hxμ ?_
  have hpos : 0 < mu h 1 - x := by linarith
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hpos]
  unfold c0
  linarith

/-- **(K1) and (K2) past `10^30`** (Lemma 14.3 of the paper). -/
theorem dprime_tail_holds : dprime_tail := by
  intro m hm
  have hm1 : m1 = 1778279 := rfl
  have hmR : (10 : ℝ) ^ 30 ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmR
  -- `r = m^(1/4)`
  obtain ⟨r, hrdef⟩ : ∃ r, √√(m : ℝ) = r := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hrdef ▸ Real.sqrt_nonneg _
  have hr4 : r ^ 4 = m := by
    rw [← hrdef, show (√√(m : ℝ)) ^ 4 = ((√√(m : ℝ)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hm0.le]
  have hr7 : (10 : ℝ) ^ 7 ≤ r := by
    by_contra hlt
    rw [not_le] at hlt
    have := pow_lt_pow_left₀ hlt hr0 (by norm_num : (4 : ℕ) ≠ 0)
    rw [hr4] at this
    linarith
  have hr3 : (10 : ℝ) ^ 21 ≤ r ^ 3 := by
    calc (10 : ℝ) ^ 21 = ((10 : ℝ) ^ 7) ^ 3 := by norm_num
      _ ≤ r ^ 3 := pow_le_pow_left₀ (by positivity) hr7 3
  have hrm : (10 : ℝ) ^ 21 * r ≤ m := by
    rw [← hr4]; nlinarith [mul_le_mul_of_nonneg_left hr3 hr0]
  have hr2m : r ^ 2 ≤ m := by
    have h1 : (1 : ℝ) ≤ r ^ 2 := by nlinarith
    rw [← hr4]; nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg r)]
  have hlog : Real.log m ≤ 4 * r := hrdef ▸ log_le_four_rt _ hm0
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  -- `J`
  have hJ140 : 140 ≤ Jtail m := le_max_left _ _
  have hJlog : (11 / 5 : ℝ) * Real.log m ≤ Jtail m :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hJup : (Jtail m : ℝ) ≤ 9 * r := by
    unfold Jtail
    rcases le_total 140 ⌈(11 / 5 : ℝ) * Real.log m⌉₊ with h | h
    · rw [max_eq_right h]
      have := Nat.ceil_lt_add_one (show 0 ≤ (11 / 5 : ℝ) * Real.log m by positivity)
      linarith
    · rw [max_eq_left h]; push_cast; linarith
  -- `m ≤ (197/125)^J`
  have hmJ : (m : ℝ) ≤ (197 / 125 : ℝ) ^ Jtail m := by
    calc (m : ℝ) = Real.exp (Real.log m) := (Real.exp_log hm0).symm
      _ ≤ Real.exp ((Jtail m : ℝ) * (5 / 11)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (5 / 11) ^ Jtail m := Real.exp_nat_mul _ _
      _ ≤ (197 / 125 : ℝ) ^ Jtail m :=
        pow_le_pow_left₀ (Real.exp_pos _).le exp_five_eleventh_le _
  unfold DCond ktail ytail Dtail
  generalize Jtail m = J at *
  -- `D`
  have hD1 : 1 ≤ Nat.clog 3 (100 * J) := Nat.clog_pos (by norm_num) (by omega)
  have hDlt : 3 ^ (Nat.clog 3 (100 * J) - 1) < 100 * J := by
    have := Nat.pow_pred_clog_lt_self (b := 3) (by norm_num) (show 1 < 100 * J by omega)
    simpa [Nat.pred_eq_sub_one] using this
  have hDge : 100 * J ≤ 3 ^ Nat.clog 3 (100 * J) := Nat.le_pow_clog (by norm_num) _
  have hDle : Nat.clog 3 (100 * J) ≤ 100 * J := by
    have : Nat.clog 3 (100 * J) - 1 < 3 ^ (Nat.clog 3 (100 * J) - 1) := Nat.lt_pow_self (by norm_num)
    omega
  generalize Nat.clog 3 (100 * J) = D at *
  have hJR : (140 : ℝ) ≤ J := by exact_mod_cast hJ140
  have hDR : (D : ℝ) ≤ 100 * J := by exact_mod_cast hDle
  have hDm : (D : ℝ) + 1778249 < m := by linarith
  have hDm' : D + 1778249 < m := by exact_mod_cast hDm
  have hDm1 : D ≤ m + 1 := by omega
  -- `y < 1800 J^2`
  have hyJ : 18 * J * 3 ^ (D - 1) < 1800 * J ^ 2 := by
    have : 18 * J * 3 ^ (D - 1) < 18 * J * (100 * J) :=
      Nat.mul_lt_mul_of_pos_left hDlt (by omega)
    calc 18 * J * 3 ^ (D - 1) < 18 * J * (100 * J) := this
      _ = 1800 * J ^ 2 := by ring
  have hyR : ((18 * J * 3 ^ (D - 1) : ℕ) : ℝ) ≤ 145800 * r ^ 2 := by
    have h1 : ((18 * J * 3 ^ (D - 1) : ℕ) : ℝ) ≤ 1800 * (J : ℝ) ^ 2 := by exact_mod_cast hyJ.le
    have h2 : (J : ℝ) ^ 2 ≤ (9 * r) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJup 2
    linarith
  -- the coefficient `2/3 - J 3^-D ≥ 197/300`
  have hx0 : (0 : ℝ) < (3 : ℝ)⁻¹ ^ D := by positivity
  have hx3 : (3 : ℝ)⁻¹ ^ D * 3 ^ D = 1 := by rw [← mul_pow]; norm_num
  have hDgeR : (100 : ℝ) * J ≤ 3 ^ D := by exact_mod_cast hDge
  have hco : (J : ℝ) * (3 : ℝ)⁻¹ ^ D ≤ 1 / 100 := by
    linarith [mul_le_mul_of_nonneg_right hDgeR hx0.le]
  have hco0 : 0 ≤ (J : ℝ) * (3 : ℝ)⁻¹ ^ D := by positivity
  -- the two jackpots
  have hpD : 59 / 100 ≤ jackLower (m + 1 - D) (18 * J * 3 ^ (D - 1)) := by
    have hmu : (m : ℝ) / 6 ≤ mu (m + 1 - D) 1 := by
      unfold mu; rw [Nat.cast_sub hDm1]; push_cast; linarith
    refine jackLower_ge_big _ _ (by linarith) ?_
    have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) hyR 2
    have h2 : (145800 * r ^ 2) ^ 2 = 145800 ^ 2 * (m : ℝ) := by rw [← hr4]; ring
    linarith
  have hp1 : 59 / 100 ≤ jackLower m (12 * J) := by
    have hmu : (m : ℝ) / 3 ≤ mu m 1 := by unfold mu; push_cast; linarith
    refine jackLower_ge_big _ _ (by linarith) ?_
    have h1 : ((12 * J : ℕ) : ℝ) ≤ 108 * r := by push_cast; linarith
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
    linarith
  refine ⟨by omega, hD1, hDm1, by rw [hm1]; omega, by omega,
    Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by positivity), by omega, ?_, ?_⟩
  · -- (K1)
    have hLJ := LJ_le m m J D (12 * J) (18 * J * 3 ^ (D - 1)) (59 / 100) _ _ le_rfl hDm1
      (by linarith) (by norm_num) hpD (tail_t2 J D hD1) (tail_t3 J)
    have hfirst : (1 - (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * (59 / 100)) ^ (J + 1) ≤
        (18377 / 30000 : ℝ) ^ (J + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hT : LJ m J D (12 * J) (18 * J * 3 ^ (D - 1)) ≤ (18377 / 30000 : ℝ) ^ (J + 1) +
        ((3 / 8) ^ 6 * (3 / 2) ^ 12) ^ J + ((9 / 11) ^ 12 * (11 / 3)) ^ J := by linarith
    have hJm : ((m : ℝ) + J + 1) / 3 ≤ 2 / 3 * m := by linarith
    have hnum := tail_K1_num J hJ140
    unfold eps
    calc ((m : ℝ) + J + 1) / 3 * LJ m J D (12 * J) (18 * J * 3 ^ (D - 1))
        ≤ (2 / 3 * m) * ((18377 / 30000 : ℝ) ^ (J + 1) + ((3 / 8) ^ 6 * (3 / 2) ^ 12) ^ J +
          ((9 / 11) ^ 12 * (11 / 3)) ^ J) :=
          mul_le_mul hJm hT (LJ_nonneg _ _ _ _ _) (by positivity)
      _ ≤ (2 / 3 * (197 / 125 : ℝ) ^ J) * ((18377 / 30000 : ℝ) ^ (J + 1) +
          ((3 / 8) ^ 6 * (3 / 2) ^ 12) ^ J + ((9 / 11) ^ 12 * (11 / 3)) ^ J) := by gcongr
      _ ≤ 1 / 50 := by linarith
  · -- (K2)
    have hL1 := L1_le m m J (12 * J) (59 / 100) _ le_rfl hp1 (tail_t3 J)
    have hB : ((9 / 11 : ℝ) ^ 12 * (11 / 3)) ^ J ≤ 1 / 10 ^ 10 := by
      calc ((9 / 11 : ℝ) ^ 12 * (11 / 3)) ^ J ≤ ((9 / 11 : ℝ) ^ 12 * (11 / 3)) ^ 140 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ140
        _ ≤ 1 / 10 ^ 10 := by norm_num
    have hS : SPoly (59 / 100) = 51507 / 80000 := by unfold SPoly; norm_num
    have hX : 0 ≤ b1 + (1 / 3 - eps) * ((m : ℝ) - m1) := by
      unfold b1 eps; rw [hm1]; push_cast; linarith
    have hprod := mul_le_mul_of_nonneg_left
      (show 51507 / 80000 - 1 / 10 ^ 10 ≤ 1 - L1 m J (12 * J) by linarith) hX
    unfold c0 b1 eps
    unfold b1 eps at hprod hX
    rw [hm1] at hprod hX ⊢
    push_cast at hprod hX ⊢
    linarith

end FrogModel.D3.LaneE
