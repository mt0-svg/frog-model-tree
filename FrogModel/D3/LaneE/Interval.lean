module

public import FrogModel.D3.LaneE.Basic

@[expose] public section

/-!
# One interval of the table of Proposition 15.2 of the paper as a check over ℚ

An `Entry` is an interval `[ml, mh]` of code/dcheck/dcheck_m1_cert.gp with its parameters and two
rational square-root bounds; `Entry.check` evaluates, in exact rationals, the test of an entry
(Section 14) at its ends, and `Entry.sound` (Lemma 14.2) turns a passing check into `DCond` at every
height of the interval. `pickE` reads the entry of a height from a linked table.
-/

open FrogModel.D3.Iface

namespace FrogModel.D3.LaneE

/-- An interval `[ml, mh]` with the comparison index `J`, the depth `D`, `k = 2 h J`,
`y = 3 h J 3^(D-1)` (the entry `a = 2 h`, `b = 3/2` of dcheck_m1_cert.gp), `k1 = a9 J`, and rational
bounds `sD ≥ sqrt(mu_(ml+1-D)(1))`, `s1 ≥ sqrt(mu_ml(1))`. -/
structure Entry where
  ml : ℕ
  mh : ℕ
  J : ℕ
  D : ℕ
  h : ℕ
  a9 : ℕ
  sD : ℚ
  s1 : ℚ

namespace Entry

def k (e : Entry) : ℕ := 2 * e.h * e.J
def y (e : Entry) : ℕ := 3 * e.h * e.J * 3 ^ (e.D - 1)
def k1 (e : Entry) : ℕ := e.a9 * e.J
/-- `mu_n(1)` in ℚ. -/
def muQ (n : ℕ) : ℚ := ((n : ℚ) + 1 + ((1 : ℕ) : ℚ)) / 3
def muD (e : Entry) : ℚ := muQ (e.ml + 1 - e.D)
def mu1 (e : Entry) : ℚ := muQ e.ml
/-- `2/3 - J 3^-D`. -/
def co (e : Entry) : ℚ := 2 / 3 - (e.J : ℚ) * (3 : ℚ)⁻¹ ^ e.D
/-- The lower bound `p_w` of Section 14 of the paper on the tail, with `sD` for the square root, at
height `ml + 1 - D` and threshold `y`. -/
def pD (e : Entry) : ℚ := 1 - ((1 - 3 / 5) * e.muD + e.sD / 2) / (e.muD - (e.y : ℚ))
/-- The same at height `ml` and threshold `k1`. -/
def p1 (e : Entry) : ℚ := 1 - ((1 - 3 / 5) * e.mu1 + e.s1 / 2) / (e.mu1 - (e.k1 : ℚ))
/-- `≥ P(Bin(y, 3^(1-D)) < k)`: the tilt at `z = 2/3` and `exp(-1) ≤ 3/8`. -/
def t2 (e : Entry) : ℚ := (3 / 8) ^ (e.h * e.J) * (3 / 2) ^ (e.k - 1)
def z3 (e : Entry) : ℚ := 3 / (2 * (e.h : ℚ) - 1)
/-- `≥ P(Bin(k, 1/4) < J)`: the tilt at `z3 = 3/(2h - 1)`. -/
def t3 (e : Entry) : ℚ := (1 - 1 / 4 + 1 / 4 * e.z3) ^ e.k / e.z3 ^ (e.J - 1)
def z9 (e : Entry) : ℚ := 3 / ((e.a9 : ℚ) - 1)
/-- `≥ P(Bin(k1, 1/4) < J)`: the tilt at `z9 = 3/(a9 - 1)`. -/
def t9 (e : Entry) : ℚ := (1 - 1 / 4 + 1 / 4 * e.z9) ^ e.k1 / e.z9 ^ (e.J - 1)
/-- The bound on `L1` at the left end. -/
def L1q (e : Entry) : ℚ := 1 - (15 / 16 - 9 / 16 * (1 - e.p1) - 3 / 8 * (1 - e.p1) ^ 2) + e.t9
/-- (K1) at the right end with the bound on `LJ` at the left end. -/
def K1q (e : Entry) : ℚ := ((e.mh : ℚ) + e.J + 1) / 3 * ((1 - e.co * e.pD) ^ (e.J + 1) + e.t2 + e.t3)

/-- The test of an entry (Section 14 of the paper): the conditions on the interval, in exact
rationals. -/
def check (e : Entry) : Bool :=
  decide (1 ≤ e.J) && decide (1 ≤ e.D) && decide (e.D ≤ 30) && decide (m1 ≤ e.ml) &&
  decide (e.ml ≤ e.mh) && decide (2 ≤ e.h) && decide (4 ≤ e.a9) &&
  decide (0 ≤ e.sD) && decide (e.muD ≤ e.sD ^ 2) && decide (0 ≤ e.s1) && decide (e.mu1 ≤ e.s1 ^ 2) &&
  decide ((e.y : ℚ) < e.muD) && decide ((e.k1 : ℚ) < e.mu1) && decide (0 ≤ e.co) && decide (0 ≤ e.pD) &&
  decide (e.K1q ≤ 1 / 50) && decide (3 / 5 / 3 ≤ (1 / 3 - 1 / 50) * (1 - e.L1q)) &&
  decide ((3 / 5 * ((e.ml : ℚ) + 3) + e.J - 2) / 3 ≤
    (27290443 / 50 + (1 / 3 - 1 / 50) * ((e.ml : ℚ) - 1778279)) * (1 - e.L1q))

theorem muQ_cast (n : ℕ) : ((muQ n : ℚ) : ℝ) = mu n 1 := by
  unfold muQ mu; push_cast; ring

/-- The tilt at `z = 2/3` for `Bin(3 h J 3^(D-1), 3^(1-D))` below `k`. -/
theorem binLt_y_le (e : Entry) (hD : 1 ≤ e.D) :
    binLt e.y ((3 : ℝ)⁻¹ ^ (e.D - 1)) e.k ≤ (e.t2 : ℝ) := by
  obtain ⟨d, hd⟩ : ∃ d, e.D = d + 1 := ⟨e.D - 1, by omega⟩
  have hp0 : (0 : ℝ) ≤ (3 : ℝ)⁻¹ ^ (e.D - 1) := by positivity
  have hp1 : (3 : ℝ)⁻¹ ^ (e.D - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := tilt_binLt e.y e.k ((3 : ℝ)⁻¹ ^ (e.D - 1)) (2 / 3) hp0 hp1 (by norm_num) (by norm_num)
  refine ht.trans ?_
  have hx : 1 - (3 : ℝ)⁻¹ ^ (e.D - 1) + (3 : ℝ)⁻¹ ^ (e.D - 1) * (2 / 3) = 1 - (3 : ℝ)⁻¹ ^ (d + 1) := by
    rw [hd, Nat.add_sub_cancel, pow_succ]; ring
  have hx0 : (0 : ℝ) ≤ (3 : ℝ)⁻¹ ^ (d + 1) := by positivity
  have hx1 : (3 : ℝ)⁻¹ ^ (d + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hexp := one_sub_pow_le_exp ((3 : ℝ)⁻¹ ^ (d + 1)) e.y hx0 hx1
  have hyx : (e.y : ℝ) * (3 : ℝ)⁻¹ ^ (d + 1) = ((e.h * e.J : ℕ) : ℝ) := by
    unfold y; rw [hd, Nat.add_sub_cancel]; push_cast
    rw [pow_succ]; field_simp
    rw [mul_assoc, ← mul_pow]; norm_num
  rw [hyx] at hexp
  have he : Real.exp (-((e.h * e.J : ℕ) : ℝ)) ≤ (3 / 8 : ℝ) ^ (e.h * e.J) := by
    rw [show -((e.h * e.J : ℕ) : ℝ) = ((e.h * e.J : ℕ) : ℝ) * (-1) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le _
  rw [hx]
  unfold t2
  push_cast
  rw [div_eq_mul_inv, ← inv_pow, show ((2 : ℝ) / 3)⁻¹ = 3 / 2 by norm_num]
  exact mul_le_mul_of_nonneg_right (hexp.trans he) (by positivity)

/-- The tilt at `z = 3/(c - 1)` for `Bin(n, 1/4)` below `J`, `c ≥ 4`. -/
theorem binLt_quarter_le (n J c : ℕ) (hc : 4 ≤ c) :
    binLt n (1 / 4) J ≤
      (((1 - 1 / 4 + 1 / 4 * (3 / ((c : ℚ) - 1))) ^ n / (3 / ((c : ℚ) - 1)) ^ (J - 1) : ℚ) : ℝ) := by
  have hc' : (4 : ℝ) ≤ c := by exact_mod_cast hc
  have hz0 : (0 : ℝ) < 3 / ((c : ℝ) - 1) := by apply div_pos <;> linarith
  have hz1 : 3 / ((c : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have := tilt_binLt n J (1 / 4) (3 / ((c : ℝ) - 1)) (by norm_num) (by norm_num) hz0 hz1
  push_cast
  convert this using 2

/-- A passing check gives `DCond` at every height of the interval. -/
theorem sound (e : Entry) (hc : e.check = true) (m : ℕ) (hm1 : e.ml ≤ m) (hm2 : m ≤ e.mh)
    (fJ fD fk fy fk1 : ℕ → ℕ) (hJ : fJ m = e.J) (hD : fD m = e.D) (hk : fk m = e.k)
    (hy : fy m = e.y) (hk1 : fk1 m = e.k1) : DCond fJ fD fk fy fk1 m := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hJ1, hD1⟩, hD30⟩, hml⟩, hmlh⟩, hh⟩, ha9⟩, hsD0⟩, hsD⟩, hs10⟩, hs1⟩, hyD⟩,
    hk1mu⟩, hco⟩, hpD0⟩, hK1⟩, hsl⟩, hba⟩ := hc
  have hm1' : m1 = 1778279 := rfl
  have hml' : 1778279 ≤ e.ml := hml
  unfold DCond
  rw [hJ, hD, hk, hy, hk1]
  have hmuD : ((e.muD : ℚ) : ℝ) = mu (e.ml + 1 - e.D) 1 := muQ_cast _
  have hmu1 : ((e.mu1 : ℚ) : ℝ) = mu e.ml 1 := muQ_cast _
  -- the two jackpots
  have hpD : ((e.pD : ℚ) : ℝ) ≤ jackLower (e.ml + 1 - e.D) e.y := by
    refine jackLower_ge _ _ (e.sD : ℝ) _ (by exact_mod_cast hsD0) ?_ ?_ (le_of_eq ?_)
    · rw [← hmuD]; exact_mod_cast hsD
    · rw [← hmuD]; exact_mod_cast hyD
    · rw [← hmuD]; unfold pD c0; push_cast; ring
  have hp1 : ((e.p1 : ℚ) : ℝ) ≤ jackLower e.ml e.k1 := by
    refine jackLower_ge _ _ (e.s1 : ℝ) _ (by exact_mod_cast hs10) ?_ ?_ (le_of_eq ?_)
    · rw [← hmu1]; exact_mod_cast hs1
    · rw [← hmu1]; exact_mod_cast hk1mu
    · rw [← hmu1]; unfold p1 c0; push_cast; ring
  -- the binomial tails
  have ht2 := binLt_y_le e hD1
  have ht3 : binLt e.k (1 / 4) e.J ≤ ((e.t3 : ℚ) : ℝ) := by
    have := binLt_quarter_le e.k e.J (2 * e.h) (by omega)
    convert this using 2
    unfold t3 z3; push_cast; ring_nf
  have ht9 : binLt e.k1 (1 / 4) e.J ≤ ((e.t9 : ℚ) : ℝ) := by
    have := binLt_quarter_le e.k1 e.J e.a9 ha9
    convert this using 2
    unfold t9 z9; rfl
  have hco' : (0 : ℝ) ≤ 2 / 3 - (e.J : ℝ) * (3 : ℝ)⁻¹ ^ e.D := by
    have : ((e.co : ℚ) : ℝ) = 2 / 3 - (e.J : ℝ) * (3 : ℝ)⁻¹ ^ e.D := by unfold co; push_cast; ring
    rw [← this]; exact_mod_cast hco
  have hLJ := LJ_le m e.ml e.J e.D e.k e.y _ _ _ hm1 (by omega) hco' (by exact_mod_cast hpD0) hpD ht2 ht3
  have hL1 := L1_le m e.ml e.J e.k1 _ _ hm1 hp1 ht9
  refine ⟨hJ1, hD1, by omega, by rw [hm1']; omega, ?_, ?_, ?_, ?_, ?_⟩
  · unfold k; have : 1 ≤ e.h * e.J := Nat.one_le_iff_ne_zero.mpr (by positivity); nlinarith
  · unfold y; have : 1 ≤ 3 ^ (e.D - 1) := Nat.one_le_pow _ _ (by norm_num)
    have : 1 ≤ e.h * e.J := Nat.one_le_iff_ne_zero.mpr (by positivity); nlinarith
  · unfold k1; nlinarith
  · -- (K1)
    have hK1r : ((e.K1q : ℚ) : ℝ) ≤ 1 / 50 := by
      have := (Rat.cast_le (K := ℝ)).mpr hK1; push_cast at this; exact this
    have hK1e : ((e.K1q : ℚ) : ℝ) = ((e.mh : ℝ) + e.J + 1) / 3 *
        ((1 - (2 / 3 - (e.J : ℝ) * (3 : ℝ)⁻¹ ^ e.D) * ((e.pD : ℚ) : ℝ)) ^ (e.J + 1) +
          ((e.t2 : ℚ) : ℝ) + ((e.t3 : ℚ) : ℝ)) := by
      unfold K1q co; push_cast; ring
    have hmh : ((m : ℝ) + e.J + 1) / 3 ≤ ((e.mh : ℝ) + e.J + 1) / 3 := by
      have : (m : ℝ) ≤ e.mh := by exact_mod_cast hm2
      linarith
    have h0 := LJ_nonneg m e.J e.D e.k e.y
    calc ((m : ℝ) + e.J + 1) / 3 * LJ m e.J e.D e.k e.y
        ≤ ((e.mh : ℝ) + e.J + 1) / 3 * LJ m e.J e.D e.k e.y :=
          mul_le_mul_of_nonneg_right hmh h0
      _ ≤ ((e.K1q : ℚ) : ℝ) := by
          rw [hK1e]; exact mul_le_mul_of_nonneg_left hLJ (by positivity)
      _ ≤ eps := by unfold eps; exact hK1r
  · -- (K2)
    have hL1e : ((e.L1q : ℚ) : ℝ) = 1 - SPoly ((e.p1 : ℚ) : ℝ) + ((e.t9 : ℚ) : ℝ) := by
      unfold L1q SPoly; push_cast; ring
    have hsl' : c0 / 3 ≤ (1 / 3 - eps) * (1 - ((e.L1q : ℚ) : ℝ)) := by
      have := (Rat.cast_le (K := ℝ)).mpr hsl; push_cast at this; unfold c0 eps; linarith
    have hba' : (c0 * ((e.ml : ℝ) + 3) + e.J - 2) / 3 ≤
        (b1 + (1 / 3 - eps) * ((e.ml : ℝ) - m1)) * (1 - ((e.L1q : ℚ) : ℝ)) := by
      have := (Rat.cast_le (K := ℝ)).mpr hba; push_cast at this; unfold c0 eps b1; rw [hm1']; push_cast
      linarith
    exact K2_of_base m e.ml e.J _ _ hml hm1 (hL1e ▸ hL1) hsl' hba'

end Entry

end FrogModel.D3.LaneE
