module

public import FrogModel.Engine.G3StepV

@[expose] public section

/-!
# The W side of the checker, move by move

Along the moves of a covered state `X` of phase `q = X.i + 1`, the accumulator of the checker holds
W' of the targets (`ww`, the pack of `H`: nine lanes of 128 bits, the budgets `0` to `T`) and the
stops (`pp`, in units of `2^-48`). `InvW X a R` says that every lane of `H` is at most
`sh (2^77 - 1)`, and that while every target was found (`ok`), the part `R` of the right side of the
flagged system at `X` is at most `theta^e` times lane `T - e` of `H` plus the stops, in units of
`2^-88`. Each move keeps the invariant with `R` raised by its weight times `tauW` at the state
reached (`move_W`); so do the rows (`rowLoop_W`), the tail atoms (`tailLoop_W`) with the closed-form
tail (`tail_bound`), the moves of a child (`child_W`) and of all children (`moves_W`). The exit and the final
comparison of the checker close the inequality at `X` (`finish_W`), and `Ws_super_of_check`
follows state by state.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine.G3

open FrogModel.Cert FrogModel.LemmaX FrogModel.Lanes

/-! ### Casts and lanes -/

/-- The closed form of a geometric tail: `m/5 Σ_k eps (1 - rho) rho^(k+n) phi^(t1+k+n+E) A/B` is
`N/D` with the numerator and denominator of `hU`, so at most `U / 2^48`. -/
theorem wtail_closed (eN eD rN rD fN fD m n t1 E A B U : ℕ) (heD : 0 < eD)
    (hrD : 0 < rD) (hr : rN < rD) (hfD : 0 < fD) (hfr : fN * rN < fD * rD) (hB : 0 < B)
    (hU : 2 ^ 48 * ((m * (eN * (rD - rN) * rN ^ n) * (fN ^ (t1 + n) * (fD * rD)) * fN ^ E * A : ℕ) :
        ℝ≥0∞) / ((5 * eD * rD ^ (n + 1) * (fD ^ (t1 + n) * (fD * rD - fN * rN)) * fD ^ E * B : ℕ) :
        ℝ≥0∞) ≤ U) :
    (m : ℝ≥0∞) * (5⁻¹ * ∑' k, ENNReal.ofReal ((eN : ℝ) / eD * (1 - (rN : ℝ) / rD) *
        ((rN : ℝ) / rD) ^ (k + n)) *
      ENNReal.ofReal (((fN : ℝ) / fD) ^ (t1 + (k + n) + E) * ((A : ℝ) / B))) ≤
      (U : ℝ≥0∞) / 2 ^ 48 := by
  have hrD' : (0 : ℝ) < rD := by exact_mod_cast hrD
  have heD' : (0 : ℝ) < eD := by exact_mod_cast heD
  have hfD' : (0 : ℝ) < fD := by exact_mod_cast hfD
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hfr' : (fN : ℝ) * rN < fD * rD := by exact_mod_cast hfr
  have hr' : (rN : ℝ) < rD := by exact_mod_cast hr
  set ρ : ℝ := (rN : ℝ) / rD with hρ
  set φ : ℝ := (fN : ℝ) / fD with hφ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : 0 ≤ 1 - ρ := by
    have : ρ < 1 := by rw [hρ, div_lt_one hrD']; exact hr'
    linarith
  have hφ0 : 0 ≤ φ := by positivity
  have hρφ : ρ * φ < 1 := by
    rw [hρ, hφ, div_mul_div_comm, div_lt_one (by positivity)]
    linarith
  set C : ℝ := (eN : ℝ) / eD * (1 - ρ) * ρ ^ n * (φ ^ (t1 + n + E) * ((A : ℝ) / B)) with hC
  have hterm : ∀ k, ENNReal.ofReal ((eN : ℝ) / eD * (1 - ρ) * ρ ^ (k + n)) *
      ENNReal.ofReal (φ ^ (t1 + (k + n) + E) * ((A : ℝ) / B)) = ENNReal.ofReal (C * (ρ * φ) ^ k) := by
    intro k
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hC, mul_pow]
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    ((summable_geometric_of_lt_one (by positivity) hρφ).mul_left C),
    tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hρφ]
  set N := m * (eN * (rD - rN) * rN ^ n) * (fN ^ (t1 + n) * (fD * rD)) * fN ^ E * A with hN
  set D := 5 * eD * rD ^ (n + 1) * (fD ^ (t1 + n) * (fD * rD - fN * rN)) * fD ^ E * B with hD
  have hD0 : 0 < D := by
    rw [hD]
    have : 0 < fD * rD - fN * rN := Nat.sub_pos_of_lt hfr
    positivity
  have hY0 : 0 ≤ C * (1 - ρ * φ)⁻¹ := by
    have : 0 < 1 - ρ * φ := by linarith
    positivity
  have h1 : (m : ℝ≥0∞) * (5⁻¹ * ENNReal.ofReal (C * (1 - ρ * φ)⁻¹)) =
      ENNReal.ofReal ((m : ℝ) * (C * (1 - ρ * φ)⁻¹) / 5) := by
    generalize C * (1 - ρ * φ)⁻¹ = Y at hY0 ⊢
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, div_eq_mul_inv]
    ring
  have h2 : (m : ℝ) * (C * (1 - ρ * φ)⁻¹) / 5 = (N : ℝ) / D := by
    have hne : (fD : ℝ) * rD - fN * rN ≠ 0 := by linarith
    have h1ρφ : 1 - ρ * φ = ((fD : ℝ) * rD - fN * rN) / (fD * rD) := by
      rw [hρ, hφ]; field_simp
    rw [h1ρφ, hN, hD, hC, hρ, hφ]
    push_cast [Nat.cast_sub hr.le, Nat.cast_sub hfr.le]
    simp only [div_pow]
    field_simp
    ring
  rw [h1, h2, ENNReal.ofReal_div_of_pos (by exact_mod_cast hD0), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp)),
    mul_comm, ← mul_div_assoc]
  exact hU

/-- A weight `num/pd` times a nonnegative rational `x`, with `num/pd x = N/D` and
`2^48 N/D ≤ U`, is at most `U / 2^48`. -/
theorem wstop_cast (num pd N D U : ℕ) (x : ℚ) (hpd : 0 < pd) (hD : 0 < D)
    (hx0 : 0 ≤ x) (hx : (num : ℚ) / pd * x = N / D) (hU : 2 ^ 48 * (N : ℝ≥0∞) / D ≤ U) :
    (num : ℝ≥0∞) / pd * ENNReal.ofReal (x : ℝ) ≤ (U : ℝ≥0∞) / 2 ^ 48 := by
  have hpd' : 0 < (pd : ℝ) := by exact_mod_cast hpd
  have hx0' : 0 ≤ (x : ℝ) := by exact_mod_cast hx0
  have hnum_nonneg : 0 ≤ (num : ℝ) := by exact_mod_cast Nat.zero_le _
  have hdiv_nonneg : 0 ≤ (num : ℝ) / (pd : ℝ) := div_nonneg hnum_nonneg (by exact_mod_cast hpd.le)
  calc
    (num : ℝ≥0∞) / pd * ENNReal.ofReal (x : ℝ)
        = (ENNReal.ofReal (num : ℝ) / ENNReal.ofReal (pd : ℝ)) * ENNReal.ofReal (x : ℝ) := by
      simp [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((num : ℝ) / (pd : ℝ)) * ENNReal.ofReal (x : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos hpd']
    _ = ENNReal.ofReal (((num : ℝ) / (pd : ℝ)) * (x : ℝ)) := by
      rw [ENNReal.ofReal_mul hdiv_nonneg]
    _ = ENNReal.ofReal (((num : ℚ) / pd * x : ℚ) : ℝ) := by
      push_cast
      ring
    _ = ENNReal.ofReal ((N / D : ℚ) : ℝ) := by rw [hx]
    _ = ENNReal.ofReal ((N : ℝ) / (D : ℝ)) := by push_cast; ring
    _ = ENNReal.ofReal (N : ℝ) / ENNReal.ofReal (D : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hD)]
    _ = (N : ℝ≥0∞) / (D : ℝ≥0∞) := by simp [ENNReal.ofReal_natCast]
    _ ≤ (U : ℝ≥0∞) / (2 ^ 48 : ℝ≥0∞) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 ^ 48 : ℝ≥0∞) ≠ 0)) (Or.inl (by norm_num : (2 ^ 48 : ℝ≥0∞) ≠ ⊤))]
      calc
        ((N : ℝ≥0∞) / (D : ℝ≥0∞)) * (2 ^ 48 : ℝ≥0∞)
            = ((N : ℝ≥0∞) * (2 ^ 48 : ℝ≥0∞)) / (D : ℝ≥0∞) := by rw [ENNReal.mul_div_right_comm]
        _ = ((2 ^ 48 : ℝ≥0∞) * (N : ℝ≥0∞)) / (D : ℝ≥0∞) := by rw [mul_comm]
        _ ≤ (U : ℝ≥0∞) := hU

/-- A weight `num/pd` below `U / 2^48` times `theta L / 2^40` is at most `theta U L / 2^88`. -/
theorem whi_cast (num pd U L : ℕ) (θ : ℝ≥0∞)
    (hU : 2 ^ 48 * (num : ℝ≥0∞) / pd ≤ U) :
    (num : ℝ≥0∞) / pd * (θ * ((L : ℝ≥0∞) / 2 ^ 40)) ≤ θ * (((U * L : ℕ) : ℝ≥0∞) / 2 ^ 88) := by
  have h2_48_ne_zero : (2 ^ 48 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_48_ne_top : (2 ^ 48 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h2_40_ne_top : (2 ^ 40 : ℝ≥0∞) ≠ ⊤ := by norm_num
  -- From hU: 2^48 * num / pd ≤ U, derive 2^48 * num ≤ U * pd
  have hU_mul : (2 ^ 48 : ℝ≥0∞) * (num : ℝ≥0∞) ≤ (U : ℝ≥0∞) * (pd : ℝ≥0∞) := by
    refine ((ENNReal.div_le_iff_le_mul ?_ ?_).mp hU)
    · right; exact ENNReal.natCast_ne_top _
    · left; exact ENNReal.natCast_ne_top _
  -- From hU_mul, derive num/pd ≤ U/2^48
  have hU_div : (num : ℝ≥0∞) / (pd : ℝ≥0∞) ≤ (U : ℝ≥0∞) / (2 ^ 48 : ℝ≥0∞) := by
    -- Using ENNReal.div_le_of_le_mul: a ≤ b * c → a / c ≤ b
    -- We need: num ≤ (U/2^48) * pd
    -- From hU_mul: 2^48 * num ≤ U * pd
    -- So num = (2^48 * num) / 2^48 ≤ (U * pd) / 2^48 = (U/2^48) * pd
    have h_num_le : (num : ℝ≥0∞) ≤ ((U : ℝ≥0∞) / (2 ^ 48 : ℝ≥0∞)) * (pd : ℝ≥0∞) := by
      calc
        (num : ℝ≥0∞) = ((2 ^ 48 : ℝ≥0∞) * (num : ℝ≥0∞)) / (2 ^ 48 : ℝ≥0∞) := by
          rw [mul_comm, ENNReal.mul_div_cancel_right h2_48_ne_zero h2_48_ne_top]
        _ ≤ ((U : ℝ≥0∞) * (pd : ℝ≥0∞)) / (2 ^ 48 : ℝ≥0∞) := by
          -- Using hU_mul: 2^48 * num ≤ U * pd
          -- We want: (2^48 * num) / 2^48 ≤ (U * pd) / 2^48
          -- This follows from hU_mul by dividing both sides by 2^48
          -- In ENNReal, we can use `gcongr` to apply the division
          gcongr
        _ = ((U : ℝ≥0∞) / (2 ^ 48 : ℝ≥0∞)) * (pd : ℝ≥0∞) := by
          rw [mul_div_assoc, ENNReal.mul_comm_div]
    exact ENNReal.div_le_of_le_mul h_num_le
  -- Now multiply hU_div by L/2^40 and use the identity (U/2^48) * (L/2^40) = U*L/2^88
  have h_main : (num : ℝ≥0∞) / (pd : ℝ≥0∞) * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞)) ≤
      ((U : ℝ≥0∞) * (L : ℝ≥0∞)) / (2 ^ 88 : ℝ≥0∞) := by
    have h_mul : (num : ℝ≥0∞) / (pd : ℝ≥0∞) * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞)) ≤
        ((U : ℝ≥0∞) / (2 ^ 48 : ℝ≥0∞)) * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞)) := by
      gcongr
    calc
      (num : ℝ≥0∞) / (pd : ℝ≥0∞) * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞))
          ≤ ((U : ℝ≥0∞) / (2 ^ 48 : ℝ≥0∞)) * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞)) := h_mul
      _ = (U : ℝ≥0∞) * (L : ℝ≥0∞) / (2 ^ 88 : ℝ≥0∞) := by
        calc
          ((U : ℝ≥0∞) / (2 ^ 48 : ℝ≥0∞)) * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞))
              = ((2 ^ 48 : ℝ≥0∞)⁻¹ * (U : ℝ≥0∞)) * ((2 ^ 40 : ℝ≥0∞)⁻¹ * (L : ℝ≥0∞)) := by
                simp [ENNReal.div_eq_inv_mul]
          _ = ((U : ℝ≥0∞) * (L : ℝ≥0∞)) * ((2 ^ 48 : ℝ≥0∞)⁻¹ * (2 ^ 40 : ℝ≥0∞)⁻¹) := by
                ring
          _ = ((U : ℝ≥0∞) * (L : ℝ≥0∞)) * (((2 ^ 48 : ℝ≥0∞) * (2 ^ 40 : ℝ≥0∞))⁻¹) := by
                rw [← ENNReal.mul_inv (Or.inl h2_48_ne_zero) (Or.inl h2_48_ne_top)]
          _ = ((U : ℝ≥0∞) * (L : ℝ≥0∞)) * ((2 ^ 88 : ℝ≥0∞)⁻¹) := by norm_num
          _ = ((U : ℝ≥0∞) * (L : ℝ≥0∞)) / (2 ^ 88 : ℝ≥0∞) := by
            rw [ENNReal.div_eq_inv_mul, mul_comm]
  calc
    (num : ℝ≥0∞) / (pd : ℝ≥0∞) * (θ * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞)))
        = θ * ((num : ℝ≥0∞) / (pd : ℝ≥0∞) * ((L : ℝ≥0∞) / (2 ^ 40 : ℝ≥0∞))) := by
          ring
    _ ≤ θ * (((U : ℝ≥0∞) * (L : ℝ≥0∞)) / (2 ^ 88 : ℝ≥0∞)) := by
      gcongr
    _ = θ * (((U * L : ℕ) : ℝ≥0∞) / 2 ^ 88) := by
      simp

/-- With `theta / 5 ≤ K / 2^48`: `5⁻¹ theta^(e+1) L / 2^40 ≤ theta^e K L / 2^88`. -/
theorem wexit_cast (θ : ℝ≥0∞) (K L e : ℕ) (hK : θ / 5 ≤ (K : ℝ≥0∞) / 2 ^ 48) :
    5⁻¹ * (θ ^ (e + 1) * ((L : ℝ≥0∞) / 2 ^ 40)) ≤ θ ^ e * (((K * L : ℕ) : ℝ≥0∞) / 2 ^ 88) := by
  calc 5⁻¹ * (θ ^ (e + 1) * ((L : ℝ≥0∞) / 2 ^ 40)) = θ ^ e * (θ / 5 * ((L : ℝ≥0∞) / 2 ^ 40)) := by
        rw [pow_succ, div_eq_mul_inv θ]; ring
    _ ≤ θ ^ e * ((K : ℝ≥0∞) / 2 ^ 48 * ((L : ℝ≥0∞) / 2 ^ 40)) := by gcongr
    _ = θ ^ e * (((K * L : ℕ) : ℝ≥0∞) / 2 ^ 88) := by
        congr 1
        simp only [div_eq_mul_inv]
        rw [show (2 : ℝ≥0∞) ^ 88 = 2 ^ 48 * 2 ^ 40 by norm_num,
          ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), Nat.cast_mul]
        ring

/-- `a / b ≤ K / 2^48` from `a 2^48 ≤ K b`. -/
theorem wofReal_div_le (a b K : ℕ) (hb : 0 < b) (h : a * 2 ^ 48 ≤ K * b) :
    ENNReal.ofReal ((a : ℝ) / b) ≤ (K : ℝ≥0∞) / 2 ^ 48 := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have h2pos : 0 < (2 ^ 48 : ℝ) := by norm_num
  have h' : (a : ℝ) * (2 ^ 48 : ℝ) ≤ (K : ℝ) * (b : ℝ) := by exact_mod_cast h
  have hdiv : (a : ℝ) / (b : ℝ) ≤ (K : ℝ) / (2 ^ 48 : ℝ) := by
    rw [div_le_div_iff₀ hb' h2pos]
    -- goal: (a : ℝ) * (2 ^ 48 : ℝ) ≤ (K : ℝ) * (b : ℝ)
    exact h'
  have h_ofReal : ENNReal.ofReal ((a : ℝ) / (b : ℝ)) ≤ ENNReal.ofReal ((K : ℝ) / (2 ^ 48 : ℝ)) :=
    ENNReal.ofReal_le_ofReal hdiv
  have h_eq : ENNReal.ofReal ((K : ℝ) / (2 ^ 48 : ℝ)) = (K : ℝ≥0∞) / 2 ^ 48 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 ^ 48 : ℝ))]
    simp
  calc
    ENNReal.ofReal ((a : ℝ) / (b : ℝ)) ≤ ENNReal.ofReal ((K : ℝ) / (2 ^ 48 : ℝ)) := h_ofReal
    _ = (K : ℝ≥0∞) / 2 ^ 48 := h_eq

/-- The stops in units of `2^-40` against units of `2^-88`. -/
theorem wpp_split (H pp x : ℕ) :
    ((H + (pp + x) * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88 =
      ((H + pp * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88 + (x : ℝ≥0∞) / 2 ^ 48 := by
  push_cast
  have h2_40 : (2 ^ 40 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_40_top : (2 ^ 40 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_pow_eq : (2 ^ 88 : ℝ≥0∞) = (2 ^ 40 : ℝ≥0∞) * (2 ^ 48 : ℝ≥0∞) := by
    ring
  -- Rewrite denominator using power identity
  rw [h_pow_eq]
  -- Rewrite the computed 2^40 back to symbolic form
  have h_pow : (1099511627776 : ℝ≥0∞) = (2 ^ 40 : ℝ≥0∞) := by norm_num
  rw [h_pow]
  -- Expand (pp + x) * 2^40
  have h_expand : ((pp : ℝ≥0∞) + (x : ℝ≥0∞)) * (2 ^ 40 : ℝ≥0∞) = (pp : ℝ≥0∞) * (2 ^ 40 : ℝ≥0∞) + (x : ℝ≥0∞) * (2 ^ 40 : ℝ≥0∞) := by
    ring
  rw [h_expand]
  -- Rearrange numerator
  have h_rearr : (↑H + ((pp : ℝ≥0∞) * (2 ^ 40 : ℝ≥0∞) + (x : ℝ≥0∞) * (2 ^ 40 : ℝ≥0∞))) = ((↑H + (pp : ℝ≥0∞) * (2 ^ 40 : ℝ≥0∞)) + (x : ℝ≥0∞) * (2 ^ 40 : ℝ≥0∞)) := by
    abel
  rw [h_rearr]
  rw [ENNReal.add_div]
  -- Cancel common term
  congr 1
  rw [mul_comm (↑x) ((2 : ℝ≥0∞) ^ 40)]
  rw [ENNReal.mul_div_mul_left (↑x) ((2 : ℝ≥0∞) ^ 48) h2_40 h2_40_top]

/-- A lane of the W side of the final comparison stays below its guard bit. -/
theorem wlane_bound (H Ex sh K pp e0 : ℕ) (b : Bool)
    (hH : H ≤ sh * (2 ^ 77 - 1)) (hE : Ex ≤ K * (2 ^ 77 - 1)) (hsh : sh + K ≤ 2 ^ 49)
    (hpp : pp + e0 < 2 ^ 86) :
    H + Ex + (pp * 2 ^ 40 + (if b then e0 * 2 ^ 40 else 0)) < 2 ^ 127 := by
  have h_if_le : (if b then e0 * 2 ^ 40 else 0) ≤ e0 * 2 ^ 40 := by
    cases b <;> simp
  have h_total : H + Ex + (pp * 2 ^ 40 + (if b then e0 * 2 ^ 40 else 0)) ≤ H + Ex + (pp + e0) * 2 ^ 40 := by
    have h : pp * 2 ^ 40 + (if b then e0 * 2 ^ 40 else 0) ≤ pp * 2 ^ 40 + e0 * 2 ^ 40 :=
      Nat.add_le_add_left h_if_le (pp * 2 ^ 40)
    rw [Nat.add_mul]
    exact Nat.add_le_add_left h (H + Ex)
  have h_bound1 : H + Ex < 2 ^ 126 := by
    have hsum : H + Ex ≤ (sh + K) * (2 ^ 77 - 1) := by
      have h := Nat.add_le_add hH hE
      rw [Nat.add_mul]
      exact h
    have h_lt : (sh + K) * (2 ^ 77 - 1) < 2 ^ 49 * 2 ^ 77 := by
      have h_mul : (sh + K) * (2 ^ 77 - 1) ≤ 2 ^ 49 * (2 ^ 77 - 1) :=
        Nat.mul_le_mul hsh (le_refl _)
      have h_sub : 2 ^ 77 - 1 < 2 ^ 77 := by
        have hpos : 0 < 2 ^ 77 := by norm_num
        omega
      have h_mul_lt : 2 ^ 49 * (2 ^ 77 - 1) < 2 ^ 49 * 2 ^ 77 :=
        Nat.mul_lt_mul_of_pos_left h_sub (by norm_num : 0 < 2 ^ 49)
      exact Nat.lt_of_le_of_lt h_mul h_mul_lt
    have h_eq : 2 ^ 49 * 2 ^ 77 = 2 ^ 126 := by
      rw [← pow_add]
    rw [h_eq] at h_lt
    exact Nat.lt_of_le_of_lt hsum h_lt
  have h_bound2 : (pp + e0) * 2 ^ 40 < 2 ^ 126 := by
    calc
      (pp + e0) * 2 ^ 40 < 2 ^ 86 * 2 ^ 40 :=
        Nat.mul_lt_mul_of_pos_right hpp (by norm_num : 0 < 2 ^ 40)
      _ = 2 ^ 126 := by
        rw [← pow_add]
  have h_eq2 : 2 ^ 126 + 2 ^ 126 = 2 ^ 127 := by
    rw [← two_mul, mul_comm, ← pow_succ]
  have h_lt : H + Ex + (pp + e0) * 2 ^ 40 < 2 ^ 127 := by
    have h_add : (H + Ex) + (pp + e0) * 2 ^ 40 < 2 ^ 126 + 2 ^ 126 :=
      Nat.add_lt_add h_bound1 h_bound2
    rw [← h_eq2]
    exact h_add
  exact Nat.lt_of_le_of_lt h_total h_lt

/-- Lanes `0` to `7` of a pack of nine lanes of 128 bits, moved up one lane. -/
theorem wUp_pack (G : ℕ → ℕ) (hG : ∀ l, G l < 2 ^ 128) :
    (FrogModel.Lanes.pack 128 9 G &&& (2 ^ (128 * 8) - 2 ^ (128 * 0))) * 2 ^ 128 =
      FrogModel.Lanes.pack 128 9 (fun l => if l = 0 then 0 else G (l - 1)) := by
  have hsub : 2 ^ (128 * 8) - 2 ^ (128 * 0) = 2 ^ (128 * 8) - 1 := by norm_num
  rw [hsub, Nat.and_two_pow_sub_one_eq_mod]
  have hpack_succ : FrogModel.Lanes.pack 128 9 G =
      FrogModel.Lanes.pack 128 8 G + G 8 * 2 ^ (128 * 8) := by
    rw [FrogModel.Lanes.pack_succ]
  rw [hpack_succ, Nat.add_mul_mod_self_right]
  have hpack_lt : FrogModel.Lanes.pack 128 8 G < 2 ^ (128 * 8) := by
    apply FrogModel.Lanes.pack_lt
    intro l hl
    apply hG l
  rw [Nat.mod_eq_of_lt hpack_lt]
  calc
    FrogModel.Lanes.pack 128 8 G * 2 ^ 128
        = (∑ l ∈ Finset.range 8, G l * 2 ^ (128 * l)) * 2 ^ 128 := rfl
    _ = ∑ l ∈ Finset.range 8, G l * (2 ^ (128 * l) * 2 ^ 128) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    _ = ∑ l ∈ Finset.range 8, G l * 2 ^ (128 * l + 128) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [pow_add]
    _ = ∑ l ∈ Finset.range 8, G l * 2 ^ (128 * (l + 1)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    _ = ∑ l ∈ Finset.range 9, (fun l => if l = 0 then 0 else G (l - 1)) l * 2 ^ (128 * l) := by
      conv =>
        rhs
        rw [Finset.sum_range_succ']
      simp

/-- A product over four children, through the multiset of their codes. -/
theorem wprod_codes {α : Type*} (σ : Fin 4 → α) (f : α → ℚ) (code : α → ℕ)
    (dec : ℕ → α) (hdc : ∀ c, dec (code (σ c)) = σ c) (u1 u2 u3 w : ℕ)
    (h : Multiset.map (fun c => code (σ c)) Finset.univ.val = {u1, u2, u3, w}) :
    ∏ c, f (σ c) = f (dec u1) * f (dec u2) * f (dec u3) * f (dec w) := by
  rw [Finset.prod_eq_multiset_prod]
  have hmap : Multiset.map (fun c => f (σ c)) Finset.univ.val = Multiset.map (fun c => f (dec (code (σ c)))) Finset.univ.val := by
    refine Multiset.map_congr rfl ?_
    intro x hx
    rw [hdc x]
  rw [hmap]
  calc
    (Multiset.map (fun c => f (dec (code (σ c)))) Finset.univ.val).prod
        = (Multiset.map ((fun n => f (dec n)) ∘ (fun c => code (σ c))) Finset.univ.val).prod := rfl
    _ = (Multiset.map (fun n => f (dec n)) (Multiset.map (fun c => code (σ c)) Finset.univ.val)).prod := by
      rw [← Multiset.map_map]
    _ = (Multiset.map (fun n => f (dec n)) ({u1, u2, u3, w} : Multiset ℕ)).prod := by rw [h]
    _ = f (dec u1) * f (dec u2) * f (dec u3) * f (dec w) := by
      simp [mul_assoc]

/-- A multiset of four naturals sorts to a list of four. -/
theorem wsort_four (s : Multiset ℕ) (hs : Multiset.card s = 4) :
    ∃ c1 c2 c3 c4, s.sort (· ≤ ·) = [c1, c2, c3, c4] ∧ c1 ≤ c2 ∧ c2 ≤ c3 ∧ c3 ≤ c4 := by
  have hlen : (s.sort (· ≤ ·)).length = 4 := by
    rw [Multiset.length_sort, hs]
  rcases (List.length_eq_four.mp hlen) with ⟨c1, c2, c3, c4, hsorted⟩
  have hpairwise : List.Pairwise (· ≤ ·) (s.sort (· ≤ ·)) := Multiset.pairwise_sort s (· ≤ ·)
  rw [hsorted] at hpairwise
  have h12 : c1 ≤ c2 := by
    have := (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ · : ℕ → ℕ → Prop))).mp hpairwise
    exact this.1
  have hrest : List.Pairwise (· ≤ ·) [c2, c3, c4] := by
    have := (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ · : ℕ → ℕ → Prop))).mp hpairwise
    exact this.2
  have h23 : c2 ≤ c3 := by
    have := (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ · : ℕ → ℕ → Prop))).mp hrest
    exact this.1
  have hrest2 : List.Pairwise (· ≤ ·) [c3, c4] := by
    have := (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ · : ℕ → ℕ → Prop))).mp hrest
    exact this.2
  have h34 : c3 ≤ c4 := by
    have := (List.pairwise_cons_cons_iff_of_trans (R := (· ≤ · : ℕ → ℕ → Prop))).mp hrest2
    exact this.1
  exact ⟨c1, c2, c3, c4, hsorted, h12, h23, h34⟩

/-! ### Constants and codes -/

theorem two48_eq : G3K.Spec.two48 = 2 ^ 48 := by unfold G3K.Spec.two48; norm_num

theorem onesW_eq : G3K.Spec.onesW = pack 128 9 fun _ => 1 := by
  have h1 := gW_eq
  unfold G3K.Spec.gW at h1
  have h2 : (2 : ℕ) ^ 127 * pack 128 9 (fun _ => 1) = pack 128 9 fun _ => 2 ^ 127 := by
    rw [pack_const_mul]; simp
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (h1.trans h2.symm)

theorem codeMs_lt (σ : Fin 4 → CState) (hwf : ∀ c, cand.ChildWF (σ c)) (u : ℕ)
    (hu : u ∈ codeMs σ) : u < 38 := by
  unfold codeMs at hu
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hu
  exact code_lt _ (hwf c)

theorem codeMs_card (σ : Fin 4 → CState) : Multiset.card (codeMs σ) = 4 := by
  simp [codeMs]

/-- The product of the potentials of three codes, as the checker writes it. -/
theorem nd_spec (u1 u2 u3 : ℕ) (h1 : u1 < 38) (h2 : u2 < 38) (h3 : u3 < 38) :
    ((G3K.wN u1 * G3K.wN u2 * G3K.wN u3 : ℕ) : ℚ) / ((G3K.wD u1 * G3K.wD u2 * G3K.wD u3 : ℕ) : ℚ) =
        cand.wQ (decC u1) * cand.wQ (decC u2) * cand.wQ (decC u3) ∧
      0 < G3K.wD u1 * G3K.wD u2 * G3K.wD u3 := by
  obtain ⟨e1, p1⟩ := w_spec u1 h1
  obtain ⟨e2, p2⟩ := w_spec u2 h2
  obtain ⟨e3, p3⟩ := w_spec u3 h3
  refine ⟨?_, Nat.mul_pos (Nat.mul_pos p1 p2) p3⟩
  rw [← e1, ← e2, ← e3]
  push_cast
  rw [mul_div_mul_comm, mul_div_mul_comm]

theorem thetaC_div5 : thetaC / 5 = ENNReal.ofReal ((G3K.th5N : ℝ) / G3K.th5D) := by
  obtain ⟨-, -, -, -, -, -, hth, -⟩ := const_spec
  unfold thetaC
  rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by simp, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  have := congrArg (fun q : ℚ => (q : ℝ)) hth
  push_cast at this
  exact this

theorem thetaC_exitHi : thetaC / 5 ≤ (G3K.exitHi : ℝ≥0∞) / 2 ^ 48 := by
  rw [thetaC_div5]
  exact wofReal_div_le _ _ _ (by decide) (by decide)

/-- `Phi` at a state: `theta^e` times the rest. -/
theorem phiC_eq (Z : RState CState 4 4) :
    phiC Z = thetaC ^ Z.e *
      ENNReal.ofReal (((cand.phi ^ (Z.p + 4 - Z.i - 1) * ∏ c, cand.wQ (Z.σ c) : ℚ) : ℝ)) := by
  have hθ : (0 : ℝ) ≤ ((cand.theta : ℚ) : ℝ) := by
    have := cand_I2.2.2.2.1
    exact_mod_cast (show (0 : ℚ) ≤ cand.theta by linarith)
  unfold phiC thetaC Data.PhiQ
  rw [← ENNReal.ofReal_pow hθ, ← ENNReal.ofReal_mul (pow_nonneg hθ _)]
  congr 1
  push_cast
  ring

/-! ### The integrand at the states reached -/

/-- `tauW` at the state the chain reaches when child `c` of `X` moves by `r`. -/
noncomputable def tgtW (t : G3K.Tree) (X : RState CState 4 4) (c : Fin 4) (r : ℕ × CState) :
    ℝ≥0∞ :=
  tauW t (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) (rstepR X c r))

theorem tauW_flag (t : G3K.Tree) (X Z : RState CState 4 4) :
    tauW t (X, false) (Z, true) = phiC Z := by
  unfold tauW
  rw [if_pos ⟨rfl, rfl⟩]
  unfold Ws
  rw [if_pos (Or.inl rfl), add_zero]

theorem tauW_live (t : G3K.Tree) (X Z : RState CState 4 4) :
    tauW t (X, false) (Z, false) = Ws t (Z, false) := by
  unfold tauW
  rw [if_neg (fun h => Bool.false_ne_true h.2), zero_add]

/-- From a flagged, absorbed or `e > T` state, the integrand is `0`. -/
theorem tauW_dead (t : G3K.Tree) (y : RState CState 4 4 × Bool)
    (h0 : y.2 = true ∨ 4 ≤ y.1.i ∨ cand.T < y.1.e) (ξ : Fin 5 × ℝ) :
    tauW t y (gT t y ξ) = 0 := by
  have hc : y.2 = true ∨ cand.T < y.1.e ∨ 4 ≤ y.1.i := by
    rcases h0 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hg : gT t y ξ = (rstep cand.childStep y.1 ξ, y.2) := by
    show domStep cand.childStep cand.T 16 (keepOf t) (lumpState cand) y ξ = _
    unfold domStep
    rw [if_pos hc]
  rw [hg]
  unfold tauW
  rw [if_neg (fun h => by rw [h.1] at h; exact Bool.false_ne_true h.2), zero_add]
  unfold Ws
  rw [if_pos]
  rcases h0 with h | h | h
  · exact Or.inl h
  · right; left
    show 4 ≤ (rstep cand.childStep y.1 ξ).i
    rw [rstep_of_absorbed _ _ h]; exact h
  · by_cases hi : y.1.i < 4
    · right; right
      show cand.T < (rstep cand.childStep y.1 ξ).e
      rw [rstep_e]; split_ifs <;> omega
    · right; left
      show 4 ≤ (rstep cand.childStep y.1 ξ).i
      rw [rstep_of_absorbed _ _ (by omega)]; omega

/-- A move that sets the flag: `Phi` at the state reached. -/
theorem tauW_stop (t : G3K.Tree) (X : RState CState 4 4) (hi : X.i < 4) (he : X.e ≤ cand.T)
    (hwf : ∀ c, cand.ChildWF (X.σ c)) (c : Fin 4) (u1 u2 u3 : ℕ)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 δ w : ℕ) (hw : w < 38)
    (hnd : (n3 : ℚ) / d3 = cand.wQ (decC u1) * cand.wQ (decC u2) * cand.wQ (decC u3))
    (hstop : 16 < X.p - 1 + δ) :
    tgtW t X c (δ, decC w) =
      thetaC ^ X.e * ENNReal.ofReal ((((G3K.phiN : ℚ) / G3K.phiD) ^
        (δ + (X.p - 1 + G3K.cJ - (X.i + 1))) *
          (((n3 * G3K.wN w : ℕ) : ℚ) / ((d3 * G3K.wD w : ℕ) : ℚ)) : ℚ) : ℝ) := by
  have hp0 : X.p - 1 + δ ≠ 0 := by omega
  have hX' := rstepR_same X c δ (decC w) hi hp0
  have hdn := domNext_flag t X (rstepR X c (δ, decC w)) hi he
    (Or.inr (by rw [hX']; exact hstop))
  have hσ' : codeMs (Function.update X.σ c (decC w)) = {u1, u2, u3, w} := by
    rw [codeMs_update X.σ c (decC w) u1 u2 u3 hms, code_decC w hw]
  have hwf' : ∀ c', cand.ChildWF (Function.update X.σ c (decC w) c') := by
    intro c'
    by_cases hc : c' = c
    · subst hc; rw [Function.update_self]; exact childWF_decC w hw
    · rw [Function.update_of_ne hc]; exact hwf c'
  unfold tgtW
  rw [hdn, tauW_flag, hX', phiC_eq]
  dsimp only
  have hq : (cand.phi ^ (X.p - 1 + δ + 4 - X.i - 1) *
      ∏ c', cand.wQ (Function.update X.σ c (decC w) c') : ℚ) =
      ((G3K.phiN : ℚ) / G3K.phiD) ^ (δ + (X.p - 1 + G3K.cJ - (X.i + 1))) *
        (((n3 * G3K.wN w : ℕ) : ℚ) / ((d3 * G3K.wD w : ℕ) : ℚ)) := by
    rw [wprod_codes (Function.update X.σ c (decC w)) cand.wQ code decC
      (fun c' => decC_code _ (hwf' c')) u1 u2 u3 w hσ']
    obtain ⟨hwN, -⟩ := w_spec w hw
    obtain ⟨-, -, -, -, -, hphi, -⟩ := const_spec
    rw [← hwN, ← hnd, hphi]
    have hexp : X.p - 1 + δ + 4 - X.i - 1 = δ + (X.p - 1 + G3K.cJ - (X.i + 1)) := by
      have : G3K.cJ = 4 := rfl
      omega
    rw [hexp]
    push_cast
    ring
  rw [hq]

/-! ### The invariant -/

/-- **The invariant of the W side** along the moves of `X`. -/
def InvW (X : RState CState 4 4) (a : G3K.Spec.Acc) (R : ℝ≥0∞) : Prop :=
  ∃ H : ℕ → ℕ, a.ww = pack 128 9 H ∧ (∀ l, H l ≤ a.sh * (2 ^ 77 - 1)) ∧
    (a.ok = true →
      R ≤ thetaC ^ X.e * (((H (cand.T - X.e) + a.pp * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88))

theorem invW_zero (X : RState CState 4 4) : InvW X G3K.Spec.acc0 0 :=
  ⟨fun _ => 0, by simp [G3K.Spec.acc0, pack], fun _ => Nat.zero_le _, fun _ => zero_le⟩

theorem invW_mono (X : RState CState 4 4) (a : G3K.Spec.Acc) (R R' : ℝ≥0∞) (h : InvW X a R)
    (hR : R' ≤ R) : InvW X a R' := by
  obtain ⟨H, h1, h2, h3⟩ := h
  exact ⟨H, h1, h2, fun hok => hR.trans (h3 hok)⟩

theorem invW_addStop (X : RState CState 4 4) (x : ℕ) (a : G3K.Spec.Acc) (R : ℝ≥0∞)
    (h : InvW X a R) :
    InvW X (G3K.Spec.addStop x a) (R + thetaC ^ X.e * ((x : ℝ≥0∞) / 2 ^ 48)) := by
  obtain ⟨H, h1, h2, h3⟩ := h
  refine ⟨H, ?_, ?_, fun hok => ?_⟩
  · rw [addStop_ww]; exact h1
  · rw [addStop_sh]; exact h2
  · rw [addStop_ok] at hok
    rw [addStop_pp, wpp_split, mul_add]
    exact add_le_add (h3 hok) le_rfl

theorem invW_addAbs (X : RState CState 4 4) (lo : ℕ) (a : G3K.Spec.Acc) (R : ℝ≥0∞)
    (h : InvW X a R) : InvW X (G3K.Spec.addAbs lo a) R := by
  obtain ⟨H, h1, h2, h3⟩ := h
  refine ⟨H, ?_, ?_, fun hok => ?_⟩
  · rw [addAbs_ww]; exact h1
  · rw [addAbs_sh]; exact h2
  · rw [addAbs_ok] at hok
    rw [addAbs_pp]; exact h3 hok

/-- The common step of `invW_addNext` and `invW_addSame`, on the fields. -/
theorem invW_live (X : RState CState 4 4) (a : G3K.Spec.Acc) (hi : ℕ) (tt : G3K.E)
    (R τ : ℝ≥0∞) (hw : tt.w = pack 128 9 fun l => lane 128 l tt.w)
    (hG : ∀ l, lane 128 l tt.w ≤ 2 ^ 77 - 1)
    (hτ : tt.flag ≤ 1 →
      τ ≤ thetaC ^ X.e * (((hi * lane 128 (cand.T - X.e) tt.w : ℕ) : ℝ≥0∞) / 2 ^ 88))
    (h : InvW X a R) :
    ∃ H : ℕ → ℕ, a.ww + hi * tt.w = pack 128 9 H ∧ (∀ l, H l ≤ (a.sh + hi) * (2 ^ 77 - 1)) ∧
      ((a.ok && decide (tt.flag ≤ 1)) = true →
        R + τ ≤ thetaC ^ X.e * (((H (cand.T - X.e) + a.pp * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88)) := by
  obtain ⟨H, h1, h2, h3⟩ := h
  refine ⟨fun l => H l + hi * lane 128 l tt.w, ?_, fun l => ?_, fun hok => ?_⟩
  · rw [h1]
    conv_lhs => rw [hw]
    rw [pack_const_mul, pack_add]
  · calc H l + hi * lane 128 l tt.w ≤ a.sh * (2 ^ 77 - 1) + hi * (2 ^ 77 - 1) :=
          add_le_add (h2 l) (Nat.mul_le_mul_left _ (hG l))
      _ = (a.sh + hi) * (2 ^ 77 - 1) := by ring
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hok
    calc R + τ ≤ thetaC ^ X.e * (((H (cand.T - X.e) + a.pp * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88) +
          thetaC ^ X.e * (((hi * lane 128 (cand.T - X.e) tt.w : ℕ) : ℝ≥0∞) / 2 ^ 88) :=
          add_le_add (h3 hok.1) (hτ hok.2)
      _ = _ := by
        rw [← mul_add, ENNReal.div_add_div_same]
        congr 2
        push_cast
        ring

theorem invW_addNext (X : RState CState 4 4) (lo hi : ℕ) (tt : G3K.E) (a : G3K.Spec.Acc)
    (R τ : ℝ≥0∞) (hw : tt.w = pack 128 9 fun l => lane 128 l tt.w)
    (hG : ∀ l, lane 128 l tt.w ≤ 2 ^ 77 - 1)
    (hτ : tt.flag ≤ 1 →
      τ ≤ thetaC ^ X.e * (((hi * lane 128 (cand.T - X.e) tt.w : ℕ) : ℝ≥0∞) / 2 ^ 88))
    (h : InvW X a R) : InvW X (G3K.Spec.addNext lo hi tt a) (R + τ) := by
  unfold InvW
  rw [addNext_ww, addNext_sh, addNext_pp, addNext_ok]
  exact invW_live X a hi tt R τ hw hG hτ h

theorem invW_addSame (X : RState CState 4 4) (lo hi : ℕ) (tt : G3K.E) (a : G3K.Spec.Acc)
    (R τ : ℝ≥0∞) (hw : tt.w = pack 128 9 fun l => lane 128 l tt.w)
    (hG : ∀ l, lane 128 l tt.w ≤ 2 ^ 77 - 1)
    (hτ : tt.flag ≤ 1 →
      τ ≤ thetaC ^ X.e * (((hi * lane 128 (cand.T - X.e) tt.w : ℕ) : ℝ≥0∞) / 2 ^ 88))
    (h : InvW X a R) : InvW X (G3K.Spec.addSame lo hi tt a) (R + τ) := by
  unfold InvW
  rw [addSame_ww, addSame_sh, addSame_pp, addSame_ok]
  exact invW_live X a hi tt R τ hw hG hτ h

/-- **A target found by the checker**: W' is the pack of its lanes, below `2^77`, and when the flag
of the target is at most `1`, `Ws` at the state the chain takes is lane `T - e` of it. -/
theorem look_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X' : RState CState 4 4)
    (hi' : X'.i < 4) (he' : X'.e ≤ cand.T) (hp1 : 1 ≤ X'.p) (hp' : X'.p ≤ 16)
    (hwf : ∀ c, cand.ChildWF (X'.σ c)) :
    (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).w =
        pack 128 9 (fun l => lane 128 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).w) ∧
      (∀ l, lane 128 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).w ≤ 2 ^ 77 - 1) ∧
      ((G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).flag ≤ 1 →
        Ws t (keptOf t X', false) ≤ thetaC ^ X'.e *
          ((lane 128 (cand.T - X'.e) (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).w :
            ℝ≥0∞) / 2 ^ 40)) := by
  rcases look_cases t X' with hb | ⟨hl, hk⟩
  · rw [hb]
    refine ⟨?_, fun l => ?_, fun hf => ?_⟩
    · simp [G3K.Spec.bad, lane, pack]
    · simp [G3K.Spec.bad, lane]
    · exact absurd hf (by simp [G3K.Spec.bad])
  · rw [hl]
    obtain ⟨hi2, he2, hp2, hout2⟩ := keptOf_fields t X'
    have hwf2 := keptOf_wf t X' hwf
    have hb := boundsOK_sound _ _ (entry_bounds t h (keptOf t X') hwf2 (by omega) hk)
    refine ⟨hb.2.2.1.symm, fun l => by have := (hb.2.2.2 l).1; omega, fun _ => ?_⟩
    have hcov : Covered t (keptOf t X', false) :=
      ⟨rfl, show (keptOf t X').i < 4 by omega, show (keptOf t X').e ≤ cand.T by omega,
        show 1 ≤ (keptOf t X').p by omega, show (keptOf t X').p ≤ 16 by omega, hwf2, hk⟩
    have hn : ¬((keptOf t X', false).2 = true ∨ 4 ≤ (keptOf t X', false).1.i ∨
        cand.T < (keptOf t X', false).1.e) := by
      rintro (h1 | h1 | h1)
      · exact Bool.false_ne_true h1
      · change 4 ≤ (keptOf t X').i at h1; omega
      · change cand.T < (keptOf t X').e at h1; omega
    unfold Ws
    rw [if_neg hn, if_pos hcov]
    change thetaC ^ (keptOf t X').e * _ ≤ _
    rw [he2]

/-! ### One move -/

/-- **One move** keeps the invariant of the W side. -/
theorem move_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 δ w num pd : ℕ) (hw : w < 38)
    (hnd : (n3 : ℚ) / d3 = cand.wQ (decC u1) * cand.wQ (decC u2) * cand.wQ (decC u3))
    (hd3 : 0 < d3) (hpd : 0 < pd) (a : G3K.Spec.Acc) (R : ℝ≥0∞) (hI : InvW X a R) :
    InvW X (G3K.Spec.move t (X.i + 1) u1 u2 u3
        (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).1
        (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.1
        (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.2 n3 d3 w
        (X.p - 1 + δ) num pd a)
      (R + (num : ℝ≥0∞) / pd * tgtW t X c (δ, decC w)) := by
  obtain ⟨-, hi, he, hp1, hp16, hwf, -⟩ := hX
  change X.i < 4 at hi
  change X.e ≤ cand.T at he
  have hσ' : codeMs (Function.update X.σ c (decC w)) = {u1, u2, u3, w} := by
    rw [codeMs_update X.σ c (decC w) u1 u2 u3 hms, code_decC w hw]
  have hwf' : ∀ c', cand.ChildWF (Function.update X.σ c (decC w) c') := by
    intro c'
    by_cases hc : c' = c
    · subst hc; rw [Function.update_self]; exact childWF_decC w hw
    · rw [Function.update_of_ne hc]; exact hwf c'
  have hTP : G3K.cTP = 16 := rfl
  have hJ4 : G3K.cJ = 4 := rfl
  unfold G3K.Spec.move
  split_ifs with hstop hzero hJ
  · -- the move sets the flag: a stop of weight `stopW`
    have hs : 16 < X.p - 1 + δ := by omega
    rw [tauW_stop t X hi he hwf c u1 u2 u3 hms n3 d3 δ w hw hnd hs]
    refine invW_mono X _ _ _ (invW_addStop X _ a R hI) (add_le_add le_rfl ?_)
    rw [mul_left_comm]
    gcongr
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hphiD, -, -⟩ := const_spec
    obtain ⟨-, hwD⟩ := w_spec w hw
    have hexp : X.p - 1 + δ + G3K.cJ - (X.i + 1) = δ + (X.p - 1 + G3K.cJ - (X.i + 1)) := by
      omega
    unfold G3K.Spec.stopW
    rw [hexp]
    have hD : 0 < pd * G3K.phiD ^ (δ + (X.p - 1 + G3K.cJ - (X.i + 1))) * (d3 * G3K.wD w) :=
      Nat.mul_pos (Nat.mul_pos hpd (pow_pos hphiD _)) (Nat.mul_pos hd3 hwD)
    refine wstop_cast _ _ _ _ _ _ hpd hD (by positivity) ?_ (up48_ge _ _ hD)
    have h1 : (pd : ℚ) ≠ 0 := by exact_mod_cast hpd.ne'
    have h2 : (G3K.phiD : ℚ) ≠ 0 := by exact_mod_cast hphiD.ne'
    have h3 : (d3 : ℚ) ≠ 0 := by exact_mod_cast hd3.ne'
    have h4 : (G3K.wD w : ℚ) ≠ 0 := by exact_mod_cast hwD.ne'
    push_cast
    rw [div_pow]
    field_simp
  · -- the move absorbs the chain: `0`
    have hX' := rstepR_next X c δ (decC w) hi hzero
    have hdn := domNext_abs t X (rstepR X c (δ, decC w)) hi he (by rw [hX']; exact he)
      (by rw [hX']; show 1 ≤ 16; omega) (by rw [hX']; show 4 ≤ X.i + 1; omega)
    have h0 : tgtW t X c (δ, decC w) = 0 := by
      unfold tgtW
      rw [hdn, tauW_live]
      unfold Ws
      rw [if_pos (Or.inr (Or.inl (by rw [hX']; show 4 ≤ X.i + 1; omega)))]
    rw [h0, mul_zero, add_zero]
    exact invW_addAbs X _ a R hI
  · -- the move ends the phase
    have hi3 : X.i + 1 < 4 := by omega
    have hX' := rstepR_next X c δ (decC w) hi hzero
    set X' : RState CState 4 4 := ⟨X.i + 1, X.e, 1, Function.update X.σ c (decC w),
      Function.update X.out ⟨X.i, hi⟩ (X.e : ℕ∞)⟩ with hX'def
    have hk1 : keyOf X' = G3K.Spec.encIns (X.i + 1 + 1) u1 u2 u3 w 1 :=
      keyOf_encIns X' u1 u2 u3 w h12 h23 hσ'
    have hk2 := keyOf_lump_encIns X' u1 u2 u3 w hwf' hσ'
    rw [← hk1, ← hk2]
    obtain ⟨hpack, hlt, hle⟩ := look_W t h X' hi3 he le_rfl (show 1 ≤ 16 by norm_num) hwf'
    set tt := G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X')) with htt
    have hdn := domNext_live t X X' hi he hi3 he (show 1 ≤ 16 by norm_num)
    have hτ : tgtW t X c (δ, decC w) = Ws t (keptOf t X', false) := by
      unfold tgtW; rw [hX', hdn, tauW_live]
    rw [hτ]
    refine invW_addNext X _ _ tt a R _ hpack hlt (fun hf => ?_) hI
    exact (mul_le_mul' le_rfl (hle hf)).trans (whi_cast num pd _ _ _ (up48_ge num pd hpd))
  · -- the move stays in the phase
    have hp2 : X.p - 1 + δ ≤ 16 := by omega
    have hX' := rstepR_same X c δ (decC w) hi hzero
    set X' : RState CState 4 4 := ⟨X.i, X.e, X.p - 1 + δ, Function.update X.σ c (decC w),
      X.out⟩ with hX'def
    have hk1 : keyOf X' = G3K.Spec.encIns (X.i + 1) u1 u2 u3 w (X.p - 1 + δ) :=
      keyOf_encIns X' u1 u2 u3 w h12 h23 hσ'
    have hk2 := keyOf_lump_encIns X' u1 u2 u3 w hwf' hσ'
    rw [← hk1, ← hk2]
    obtain ⟨hpack, hlt, hle⟩ := look_W t h X' hi he (show 1 ≤ X.p - 1 + δ by omega) hp2 hwf'
    set tt := G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X')) with htt
    have hdn := domNext_live t X X' hi he hi he hp2
    have hτ : tgtW t X c (δ, decC w) = Ws t (keptOf t X', false) := by
      unfold tgtW; rw [hX', hdn, tauW_live]
    rw [hτ]
    refine invW_addSame X _ _ tt a R _ hpack hlt (fun hf => ?_) hI
    exact (mul_le_mul' le_rfl (hle hf)).trans (whi_cast num pd _ _ _ (up48_ge num pd hpd))

/-! ### Rows, tails, children -/

/-- **The moves of a row** keep the invariant of the W side. -/
theorem rowLoop_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 m : ℕ)
    (hnd : (n3 : ℚ) / d3 = cand.wQ (decC u1) * cand.wQ (decC u2) * cand.wQ (decC u3))
    (hd3 : 0 < d3) :
    ∀ (rs : List G3K.Tr) (a : G3K.Spec.Acc) (R : ℝ≥0∞),
      (∀ r ∈ rs, r.next < 38 ∧ 0 < r.pd) → InvW X a R →
      InvW X (G3K.Spec.rowLoop t (X.i + 1) u1 u2 u3
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.2 n3 d3 (X.p - 1) m rs a)
        (R + (rs.map fun r =>
          ((m * r.pn : ℕ) : ℝ≥0∞) / r.pd * tgtW t X c (r.delta, decC r.next)).sum)
  | [], a, R, _, hI => by
      rw [G3K.Spec.rowLoop]
      exact invW_mono X a R _ hI (by simp)
  | r :: rs, a, R, hr, hI => by
      rw [G3K.Spec.rowLoop]
      have h1 := move_W t h X hX c u1 u2 u3 h12 h23 hms n3 d3 r.delta r.next (m * r.pn) r.pd
        (hr r List.mem_cons_self).1 hnd hd3 (hr r List.mem_cons_self).2 a R hI
      have h2 := rowLoop_W t h X hX c u1 u2 u3 h12 h23 hms n3 d3 m hnd hd3 rs _ _
        (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')) h1
      refine invW_mono X _ _ _ h2 (le_of_eq ?_)
      simp only [List.map_cons, List.sum_cons]
      ring

theorem tailD_pos (j : ℕ) : 0 < G3K.Spec.tailD j := by
  unfold G3K.Spec.tailD
  have : 0 < G3K.epsD := by decide
  have : 0 < G3K.rhoD := by decide
  positivity

/-- **The tail atoms** keep the invariant of the W side. -/
theorem tailLoop_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 m ct : ℕ) (hct : ct < 38)
    (hnd : (n3 : ℚ) / d3 = cand.wQ (decC u1) * cand.wQ (decC u2) * cand.wQ (decC u3))
    (hd3 : 0 < d3) :
    ∀ (n k : ℕ) (a : G3K.Spec.Acc) (R : ℝ≥0∞), InvW X a R →
      InvW X (G3K.Spec.tailLoop t (X.i + 1) u1 u2 u3
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.2 n3 d3 ct (X.p - 1) m
          k n a)
        (R + ∑ j ∈ Finset.range n,
          ((m * G3K.Spec.tailN (k + j) : ℕ) : ℝ≥0∞) / G3K.Spec.tailD (k + j) *
            tgtW t X c (G3K.cT + 1 + (k + j), decC ct))
  | 0, k, a, R, hI => by
      rw [G3K.Spec.tailLoop]
      exact invW_mono X a R _ hI (by simp)
  | n + 1, k, a, R, hI => by
      rw [G3K.Spec.tailLoop]
      have h1 := move_W t h X hX c u1 u2 u3 h12 h23 hms n3 d3 (G3K.cT + 1 + k) ct
        (m * G3K.Spec.tailN k) (G3K.Spec.tailD k) hct hnd hd3 (tailD_pos k) a R hI
      have h2 := tailLoop_W t h X hX c u1 u2 u3 h12 h23 hms n3 d3 m ct hct hnd hd3 n (k + 1) _ _ h1
      refine invW_mono X _ _ _ h2 (le_of_eq ?_)
      rw [Finset.sum_range_succ' _ n]
      simp only [add_zero, Nat.add_assoc, Nat.add_comm 1]
      ring

theorem tailW_real (k : ℕ) :
    ((cand.tailW k : ℚ) : ℝ) = (G3K.epsN : ℝ) / G3K.epsD * (1 - (G3K.rhoN : ℝ) / G3K.rhoD) *
      ((G3K.rhoN : ℝ) / G3K.rhoD) ^ k := by
  obtain ⟨-, -, -, heps, hrho, -⟩ := const_spec
  unfold Data.tailW
  rw [heps, hrho]
  push_cast
  ring

/-- **The tail of a child state F or B** is at most the tail atoms of the checker and its closed
form, `cfW`. -/
theorem tail_bound (t : G3K.Tree) (X : RState CState 4 4) (hi : X.i < 4) (he : X.e ≤ cand.T)
    (hp1 : 1 ≤ X.p) (hwf : ∀ c, cand.ChildWF (X.σ c)) (c : Fin 4) (u1 u2 u3 : ℕ)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 m ct : ℕ) (hct : ct < 38)
    (hnd : (n3 : ℚ) / d3 = cand.wQ (decC u1) * cand.wQ (decC u2) * cand.wQ (decC u3))
    (hd3 : 0 < d3) :
    m * (5⁻¹ * ∑' k, ENNReal.ofReal (cand.tailW k : ℝ) * tgtW t X c (cand.T + 1 + k, decC ct)) ≤
      ∑ j ∈ Finset.range (G3K.cTP + 1 - (X.p + G3K.cT)),
          ((m * G3K.Spec.tailN (0 + j) : ℕ) : ℝ≥0∞) / G3K.Spec.tailD (0 + j) *
            tgtW t X c (G3K.cT + 1 + (0 + j), decC ct) +
        thetaC ^ X.e * ((G3K.Spec.cfW n3 d3 ct m (max (G3K.cT + 1) (G3K.cTP + 2 - X.p))
          (X.p - 1 + G3K.cJ - (X.i + 1)) : ℝ≥0∞) / 2 ^ 48) := by
  obtain ⟨-, -, -, -, -, -, -, hepsD, hrhoD, hlt, hphiD, -, hfr⟩ := const_spec
  have hT : cand.T = G3K.cT := rfl
  have hT8 : G3K.cT = 8 := rfl
  have hTP : G3K.cTP = 16 := rfl
  obtain ⟨-, hwD⟩ := w_spec ct hct
  set n := G3K.cTP + 1 - (X.p + G3K.cT) with hn
  set E := X.p - 1 + G3K.cJ - (X.i + 1) with hE
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := n), mul_add, mul_add]
  gcongr ?_ + ?_
  · -- the tail atoms of the checker
    apply le_of_eq
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zero_add, natMul_div, ← ofReal_ratDiv _ _ (tailD_pos j), tail_weight, ofReal_div5, hT]
    ring
  · -- the rest of the tail sets the flag: the closed form
    have hterm : ∀ k, tgtW t X c (cand.T + 1 + (k + n), decC ct) =
        thetaC ^ X.e * ENNReal.ofReal ((((G3K.phiN : ℚ) / G3K.phiD) ^ (cand.T + 1 + (k + n) + E) *
          (((n3 * G3K.wN ct : ℕ) : ℚ) / ((d3 * G3K.wD ct : ℕ) : ℚ)) : ℚ) : ℝ) := fun k =>
      tauW_stop t X hi he hwf c u1 u2 u3 hms n3 d3 _ ct hct hnd (by omega)
    have hx : ∀ k, ((((G3K.phiN : ℚ) / G3K.phiD) ^ (cand.T + 1 + (k + n) + E) *
        (((n3 * G3K.wN ct : ℕ) : ℚ) / ((d3 * G3K.wD ct : ℕ) : ℚ)) : ℚ) : ℝ) =
        ((G3K.phiN : ℝ) / G3K.phiD) ^ (G3K.cT + 1 + (k + n) + E) *
          (((n3 * G3K.wN ct : ℕ) : ℝ) / ((d3 * G3K.wD ct : ℕ) : ℝ)) := by
      intro k
      rw [hT]
      push_cast
      ring
    simp_rw [hterm, mul_left_comm _ (thetaC ^ X.e), ENNReal.tsum_mul_left, hx, tailW_real]
    have hcomm : ∀ a b c d : ℝ≥0∞, a * (b * (c * d)) = c * (a * (b * d)) := fun a b c d => by ring
    rw [hcomm]
    gcongr
    have hmax : max (G3K.cT + 1) (G3K.cTP + 2 - X.p) = G3K.cT + 1 + n := by
      rw [hn, hT8, hTP]; omega
    have hcf : G3K.Spec.cfW n3 d3 ct m (max (G3K.cT + 1) (G3K.cTP + 2 - X.p)) E =
        G3K.Spec.up48 (m * (G3K.epsN * (G3K.rhoD - G3K.rhoN) * G3K.rhoN ^ n) *
            (G3K.phiN ^ (G3K.cT + 1 + n) * (G3K.phiD * G3K.rhoD)) * G3K.phiN ^ E *
            (n3 * G3K.wN ct))
          (5 * G3K.epsD * G3K.rhoD ^ (n + 1) *
            (G3K.phiD ^ (G3K.cT + 1 + n) * (G3K.phiD * G3K.rhoD - G3K.phiN * G3K.rhoN)) *
            G3K.phiD ^ E * (d3 * G3K.wD ct)) := by
      rw [hmax]
      unfold G3K.Spec.cfW G3K.Spec.tailN G3K.Spec.tailD
      rw [Nat.add_sub_cancel_left]
    have hD : 0 < 5 * G3K.epsD * G3K.rhoD ^ (n + 1) *
        (G3K.phiD ^ (G3K.cT + 1 + n) * (G3K.phiD * G3K.rhoD - G3K.phiN * G3K.rhoN)) *
        G3K.phiD ^ E * (d3 * G3K.wD ct) :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hepsD)
        (pow_pos hrhoD _)) (Nat.mul_pos (pow_pos hphiD _) (Nat.sub_pos_of_lt hfr)))
        (pow_pos hphiD _)) (Nat.mul_pos hd3 hwD)
    rw [hcf]
    exact wtail_closed _ _ _ _ _ _ m n (G3K.cT + 1) E _ _ _ hepsD hrhoD hlt hphiD hfr
      (Nat.mul_pos hd3 hwD) (up48_ge _ _ hD)

/-- **The moves of one child state** of multiplicity `m`. -/
theorem child_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 m : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (acc : G3K.Spec.Acc) (R : ℝ≥0∞)
    (hI : InvW X acc R) :
    InvW X (G3K.Spec.child t (X.i + 1) (code (X.σ c)) u1 u2 u3 X.p m acc)
      (R + m * (5⁻¹ * moveSum cand (X.σ c) (fun r => tgtW t X c r))) := by
  obtain ⟨-, hi, he, hp1, hp16, hwf, -⟩ := id hX
  have hcc : code (X.σ c) < 38 := code_lt _ (hwf c)
  have hdec : decC (code (X.σ c)) = X.σ c := decC_code _ (hwf c)
  have hu1 : u1 < 38 := codeMs_lt X.σ hwf u1 (by rw [hms]; simp)
  have hu2 : u2 < 38 := codeMs_lt X.σ hwf u2 (by rw [hms]; simp)
  have hu3 : u3 < 38 := codeMs_lt X.σ hwf u3 (by rw [hms]; simp)
  obtain ⟨hnd, hd3⟩ := nd_spec u1 u2 u3 hu1 hu2 hu3
  obtain ⟨-, hr38⟩ := row_spec _ hcc
  have hrow := rowLoop_W t h X hX c u1 u2 u3 h12 h23 hms (G3K.wN u1 * G3K.wN u2 * G3K.wN u3)
    (G3K.wD u1 * G3K.wD u2 * G3K.wD u3) m hnd hd3 (G3K.row (code (X.σ c))) acc R hr38 hI
  have hsum : ((G3K.row (code (X.σ c))).map fun r =>
      ((m * r.pn : ℕ) : ℝ≥0∞) / r.pd * tgtW t X c (r.delta, decC r.next)).sum =
      m * (5⁻¹ * ((cand.finRow (X.σ c)).map fun e =>
        ENNReal.ofReal (e.p : ℝ) * tgtW t X c (e.δ, e.next)).sum) := by
    rw [rowSum_eq _ hcc m (fun r => tgtW t X c r), hdec]
  obtain ⟨ht0, ht1, htn, ht0l, ht1l⟩ := tail_spec
  unfold G3K.Spec.child
  dsimp only
  split_ifs with hc1
  · -- `F` or `B`: the row, the tail atoms, the closed form of the tail
    have hct : G3K.tailOf (code (X.σ c)) < 38 := by
      interval_cases hcode : code (X.σ c)
      · exact ht0l
      · exact ht1l
    have hnext : cand.tailNext (X.σ c) = some (decC (G3K.tailOf (code (X.σ c)))) := by
      rw [← hdec]
      interval_cases hcode : code (X.σ c)
      · exact ht0
      · exact ht1
    unfold G3K.Spec.withTails
    have htail := tailLoop_W t h X hX c u1 u2 u3 h12 h23 hms (G3K.wN u1 * G3K.wN u2 * G3K.wN u3)
      (G3K.wD u1 * G3K.wD u2 * G3K.wD u3) m _ hct hnd hd3 (G3K.cTP + 1 - (X.p + G3K.cT)) 0 _ _
      hrow
    refine invW_mono X _ _ _ (invW_addStop X _ _ _ htail) ?_
    rw [hsum, add_assoc, add_assoc]
    gcongr R + ?_
    unfold moveSum
    rw [hnext, mul_add, mul_add]
    gcongr _ + ?_
    exact tail_bound t X hi he hp1 hwf c u1 u2 u3 hms _ _ m _ hct hnd hd3
  · -- a label, a tail or a max label: the row alone, no tail
    have hnext : cand.tailNext (X.σ c) = none := by
      rw [← hdec]; exact htn _ hcc (by omega)
    refine invW_mono X _ _ _ hrow (le_of_eq ?_)
    rw [hsum]
    unfold moveSum
    rw [hnext, add_zero]

/-- **The moves of all children**. -/
theorem moves_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) :
    InvW X (G3K.Spec.moves t (X.i + 1) c1 c2 c3 c4 X.p)
      (∑ c, 5⁻¹ * moveSum cand (X.σ c) (fun r => tgtW t X c r)) := by
  have hwf : ∀ c, cand.ChildWF (X.σ c) := hX.2.2.2.2.2.1
  have hinj := code_inj_of_wf X hwf
  have hsort := Multiset.pairwise_sort (codeMs X.σ) (· ≤ ·)
  rw [hL] at hsort
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at hsort
  have h12 : c1 ≤ c2 := by omega
  have h23 : c2 ≤ c3 := by omega
  have h34 : c3 ≤ c4 := by omega
  have hms : ({c1, c2, c3, c4} : Multiset ℕ) = codeMs X.σ := by
    rw [← Multiset.sort_eq (codeMs X.σ) (· ≤ ·), hL]; rfl
  set F : Fin 4 → ℝ≥0∞ := fun c => 5⁻¹ * moveSum cand (X.σ c) (fun r => tgtW t X c r)
    with hFdef
  have hF : ∀ c c', X.σ c = X.σ c' → F c = F c' := by
    intro c c' hcc
    simp only [hFdef, tgtW]
    rw [moveSum_congr t X (tauW t (X, false)) (fun π Z b => tauW_perm t _ π Z b) c c' hcc]
  have key := moves_inv (ι := Unit) (fun a R => InvW X a (R ())) t (X.i + 1) X.p c1 c2 c3 c4
    (fun a _ => perCode X F a) h12 h23 h34 (invW_zero X)
    (by
      intro a u1 u2 u3 m acc R hu12 hu23 hu hP
      obtain ⟨c, hca, hms2⟩ := exists_child_of_code X a u1 u2 u3 (hu.trans hms)
      subst hca
      have hc := child_W t h X hX c u1 u2 u3 m hu12 hu23 hms2 acc (R ()) hP
      show InvW X _ (R () + (m : ℝ≥0∞) * perCode X F (code (X.σ c)))
      rw [perCode_eq X hinj F hF c]
      exact hc)
  refine invW_mono X _ _ _ key (le_of_eq ?_)
  exact sum_perCode X hinj F hF c1 c2 c3 c4 hL

/-! ### The exit and the final comparison -/

/-- **The final comparison of the W side**, lane by lane. -/
theorem final_read (s : G3K.E) (q : ℕ) (a : G3K.Spec.Acc) (ev ew e0 : ℕ) (eok : Bool)
    (H Ex : ℕ → ℕ) (hs : ∀ j, lane 128 j s.w < 2 ^ 77)
    (hsw : pack 128 9 (fun j => lane 128 j s.w) = s.w) (hww : a.ww = pack 128 9 H)
    (hH : ∀ l, H l ≤ a.sh * (2 ^ 77 - 1)) (hew : ew = pack 128 9 Ex)
    (hEx : ∀ l, Ex l ≤ G3K.exitHi * (2 ^ 77 - 1))
    (hf : G3K.Spec.final s q a ev ew e0 eok = true) :
    a.ok = true ∧ eok = true ∧ ∀ l < 9,
      H l + Ex l + (a.pp * 2 ^ 40 + (if l = 0 then e0 * 2 ^ 40 else 0)) ≤ lane 128 l s.w * 2 ^ 48 := by
  unfold G3K.Spec.final at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨hok, heok⟩, -⟩, hsh⟩, hpp⟩, -⟩, hW⟩ := hf
  refine ⟨hok, heok, ?_⟩
  have hgW : G3K.Spec.gW = pack 128 9 fun _ => 2 ^ (128 - 1) := gW_eq
  have hlhs : a.ww + ew + (a.pp * G3K.Spec.two40 * G3K.Spec.onesW + e0 * G3K.Spec.two40) =
      pack 128 9 fun l => H l + Ex l + (a.pp * 2 ^ 40 + (if l = 0 then e0 * 2 ^ 40 else 0)) := by
    have hs0 : e0 * 2 ^ 40 = pack 128 9 (fun l => if l = 0 then e0 * 2 ^ 40 else 0) :=
      eq_pack_lane0 128 9 _ (by norm_num)
    rw [hww, hew, two40_eq, onesW_eq, pack_const_mul]
    conv_lhs => rw [hs0]
    rw [pack_add, pack_add, pack_add]
    simp only [mul_one]
  have hrhs : s.w * G3K.Spec.two48 = pack 128 9 fun l => lane 128 l s.w * 2 ^ 48 := by
    rw [two48_eq, mul_comm]
    conv_lhs => rw [← hsw]
    rw [pack_const_mul]
    simp only [mul_comm]
  rw [hlhs, hrhs, hgW] at hW
  intro l hl
  refine (leLanes_pack 128 9 (by norm_num) _ _ (fun l _ => ?_) (fun l _ => ?_)).1 hW l hl
  · have h1 := wlane_bound (H l) (Ex l) a.sh G3K.exitHi a.pp e0 (decide (l = 0)) (hH l) (hEx l)
      hsh hpp
    by_cases h0 : l = 0 <;> simp_all
  · have := hs l
    calc lane 128 l s.w * 2 ^ 48 < 2 ^ 77 * 2 ^ 48 := Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ ≤ 2 ^ (128 - 1) := by norm_num

/-- The exit when it sets the flag (`e = T`): at most the exit stop. -/
theorem exit_stop_W (t : G3K.Tree) (X : RState CState 4 4) (hi : X.i < 4) (hp1 : 1 ≤ X.p)
    (hwf : ∀ c, cand.ChildWF (X.σ c)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) (he : X.e = cand.T) :
    5⁻¹ * tauW t (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        (rstep cand.childStep X (0, 0))) ≤
      thetaC ^ X.e * ((G3K.Spec.exitStop (X.i + 1) c1 c2 c3 c4 X.p : ℝ≥0∞) / 2 ^ 48) := by
  obtain ⟨-, -, -, -, -, hphi, -, -, -, -, hphiD, hth5D, -⟩ := const_spec
  have hJ4 : G3K.cJ = 4 := rfl
  have hms : codeMs X.σ = {c1, c2, c3, c4} := by
    rw [← Multiset.sort_eq (codeMs X.σ) (· ≤ ·), hL]; rfl
  have hlt : ∀ x ∈ [c1, c2, c3, c4], x < 38 := fun x hx =>
    codeMs_lt X.σ hwf x (by rw [← hL] at hx; exact (Multiset.mem_sort _).1 hx)
  obtain ⟨Z, hZ, hZe, hZσ, hZE⟩ : ∃ Z : RState CState 4 4, rstep cand.childStep X (0, 0) = Z ∧
      Z.e = X.e + 1 ∧ Z.σ = X.σ ∧ Z.p + 4 - Z.i - 1 = X.p - 1 + G3K.cJ - (X.i + 1) := by
    rw [rstep_exit X hi]
    split_ifs with hp
    · exact ⟨_, rfl, rfl, rfl, by show 1 + 4 - (X.i + 1) - 1 = X.p - 1 + G3K.cJ - (X.i + 1); omega⟩
    · exact ⟨_, rfl, rfl, rfl, by show X.p - 1 + 4 - X.i - 1 = X.p - 1 + G3K.cJ - (X.i + 1); omega⟩
  rw [hZ, domNext_flag t X Z hi (by omega) (Or.inl (by omega)), tauW_flag, phiC_eq, hZe, hZσ,
    hZE, pow_succ]
  calc 5⁻¹ * (thetaC ^ X.e * thetaC * ENNReal.ofReal (((cand.phi ^ (X.p - 1 + G3K.cJ - (X.i + 1)) *
          ∏ c, cand.wQ (X.σ c) : ℚ) : ℝ)))
      = thetaC ^ X.e * (thetaC / 5 * ENNReal.ofReal (((cand.phi ^ (X.p - 1 + G3K.cJ - (X.i + 1)) *
          ∏ c, cand.wQ (X.σ c) : ℚ) : ℝ))) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ _ := by
        gcongr
        have h5 : thetaC / 5 = (G3K.th5N : ℝ≥0∞) / G3K.th5D := by
          rw [thetaC_div5, ENNReal.ofReal_div_of_pos (by exact_mod_cast hth5D),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        rw [h5, wprod_codes X.σ cand.wQ code decC (fun c => decC_code _ (hwf c)) c1 c2 c3 c4 hms]
        obtain ⟨e1, p1⟩ := w_spec c1 (hlt c1 (by simp))
        obtain ⟨e2, p2⟩ := w_spec c2 (hlt c2 (by simp))
        obtain ⟨e3, p3⟩ := w_spec c3 (hlt c3 (by simp))
        obtain ⟨e4, p4⟩ := w_spec c4 (hlt c4 (by simp))
        rw [← e1, ← e2, ← e3, ← e4, hphi]
        unfold G3K.Spec.exitStop
        have hD : 0 < G3K.th5D * G3K.phiD ^ (X.p - 1 + G3K.cJ - (X.i + 1)) *
            (G3K.wD c1 * G3K.wD c2 * G3K.wD c3 * G3K.wD c4) :=
          Nat.mul_pos (Nat.mul_pos hth5D (pow_pos hphiD _))
            (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4)
        refine wstop_cast _ _ _ _ _ _ hth5D hD (by positivity) ?_ (up48_ge _ _ hD)
        have q0 : (G3K.th5D : ℚ) ≠ 0 := by exact_mod_cast hth5D.ne'
        have q1 : (G3K.phiD : ℚ) ≠ 0 := by exact_mod_cast hphiD.ne'
        have q2 : (G3K.wD c1 : ℚ) ≠ 0 := by exact_mod_cast p1.ne'
        have q3 : (G3K.wD c2 : ℚ) ≠ 0 := by exact_mod_cast p2.ne'
        have q4 : (G3K.wD c3 : ℚ) ≠ 0 := by exact_mod_cast p3.ne'
        have q5 : (G3K.wD c4 : ℚ) ≠ 0 := by exact_mod_cast p4.ne'
        push_cast
        rw [div_pow]
        field_simp

/-- The pack of a target found by the checker, below `2^77` in every lane. -/
theorem look_W_pack (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X' : RState CState 4 4)
    (hp' : X'.p ≤ 16) (hwf : ∀ c, cand.ChildWF (X'.σ c)) :
    (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).w =
        pack 128 9 (fun l => lane 128 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).w) ∧
      ∀ l, lane 128 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).w ≤ 2 ^ 77 - 1 := by
  rcases look_cases t X' with hb | ⟨hl, hk⟩
  · rw [hb]
    exact ⟨by simp [G3K.Spec.bad, lane, pack], fun l => by simp [G3K.Spec.bad, lane]⟩
  · rw [hl]
    obtain ⟨-, -, hp2, -⟩ := keptOf_fields t X'
    have hb := boundsOK_sound _ _ (entry_bounds t h (keptOf t X') (keptOf_wf t X' hwf)
      (by omega) hk)
    exact ⟨hb.2.2.1.symm, fun l => by have := (hb.2.2.2 l).1; omega⟩

/-- The exit's lanes `exitHi wUp` of a target: the pack of its lanes moved up one budget. -/
theorem exitHi_wUp (tt : G3K.E) (hw : tt.w = pack 128 9 fun l => lane 128 l tt.w) :
    G3K.exitHi * G3K.Spec.wUp tt =
      pack 128 9 fun l => G3K.exitHi * (if l = 0 then 0 else lane 128 (l - 1) tt.w) := by
  unfold G3K.Spec.wUp
  rw [lowW_eq]
  conv_lhs => rw [hw]
  rw [wUp_pack _ (fun l => lane_lt 128 l _), pack_const_mul]

/-- The lane `T - e` of the comparison closes the inequality at `X`. -/
theorem combine_W (θe : ℝ≥0∞) (Hb Exb pp e0b Lb : ℕ) (R E : ℝ≥0∞)
    (hlane : Hb + Exb + (pp * 2 ^ 40 + e0b) ≤ Lb * 2 ^ 48)
    (hR : R ≤ θe * (((Hb + pp * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88))
    (hE : E ≤ θe * (((Exb + e0b : ℕ) : ℝ≥0∞) / 2 ^ 88)) :
    E + R ≤ θe * ((Lb : ℝ≥0∞) / 2 ^ 40) := by
  calc E + R ≤ θe * (((Exb + e0b : ℕ) : ℝ≥0∞) / 2 ^ 88) +
        θe * (((Hb + pp * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88) := add_le_add hE hR
    _ = θe * (((Exb + e0b + (Hb + pp * 2 ^ 40) : ℕ) : ℝ≥0∞) / 2 ^ 88) := by
        rw [← mul_add, ENNReal.div_add_div_same]
        congr 2
        push_cast
        ring
    _ ≤ θe * (((Lb * 2 ^ 48 : ℕ) : ℝ≥0∞) / 2 ^ 88) := by
        gcongr
        omega
    _ = θe * ((Lb : ℝ≥0∞) / 2 ^ 40) := by
        congr 1
        rw [show (2 : ℝ≥0∞) ^ 88 = 2 ^ 40 * 2 ^ 48 by norm_num, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, ENNReal.mul_div_mul_right _ _ (by positivity) (by simp)]

/-- `Ws` at a covered state. -/
theorem Ws_cov (t : G3K.Tree) (X : RState CState 4 4) (hX : Covered t (X, false)) :
    Ws t (X, false) = thetaC ^ X.e * ((lane 128 (cand.T - X.e) (entry t X).w : ℝ≥0∞) / 2 ^ 40) := by
  have hn : ¬((X, false).2 = true ∨ 4 ≤ (X, false).1.i ∨ cand.T < (X, false).1.e) := by
    rintro (h1 | h1 | h1)
    · exact Bool.false_ne_true h1
    · have := hX.2.1; change X.i < 4 at this; change 4 ≤ X.i at h1; omega
    · have := hX.2.2.1; change X.e ≤ cand.T at this; change cand.T < X.e at h1; omega
  unfold Ws
  rw [if_neg hn, if_pos hX]

/-- **The exit of the last frog** (`p = 1`, phase `J`): it sets the flag or absorbs. -/
theorem finish_abs_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) (hp : X.p = 1) (hq : X.i + 1 = G3K.cJ)
    (a : G3K.Spec.Acc) (R : ℝ≥0∞) (hI : InvW X a R) (ev : ℕ)
    (hf : G3K.Spec.final (entry t X) (X.i + 1) a ev 0
      (G3K.Spec.exitStop (X.i + 1) c1 c2 c3 c4 X.p) true = true) :
    5⁻¹ * tauW t (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        (rstep cand.childStep X (0, 0))) + R ≤ Ws t (X, false) := by
  obtain ⟨-, hi, he, hp1, hp16, hwf, hk⟩ := id hX
  change X.i < 4 at hi
  change X.e ≤ cand.T at he
  obtain ⟨H, hww, hH, hR⟩ := hI
  have hb := boundsOK_sound _ _ (entry_bounds t h X hwf (by change X.p ≤ 16 at hp16; omega) hk)
  obtain ⟨hok, -, hlanes⟩ := final_read (entry t X) (X.i + 1) a ev 0 _ true H (fun _ => 0)
    (fun j => (hb.2.2.2 j).1) hb.2.2.1 hww hH (by simp [pack]) (fun _ => Nat.zero_le _) hf
  have hT8 : cand.T = 8 := rfl
  rw [Ws_cov t X hX]
  refine combine_W _ (H (cand.T - X.e)) 0 a.pp
    (if cand.T - X.e = 0 then G3K.Spec.exitStop (X.i + 1) c1 c2 c3 c4 X.p * 2 ^ 40 else 0) _ R _
    (hlanes _ (by omega)) (hR hok) ?_
  by_cases heT : X.e = cand.T
  · rw [if_pos (by omega), zero_add]
    refine (exit_stop_W t X hi (by omega) hwf c1 c2 c3 c4 hL heT).trans (le_of_eq ?_)
    congr 1
    rw [show (2 : ℝ≥0∞) ^ 88 = 2 ^ 48 * 2 ^ 40 by norm_num, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, ENNReal.mul_div_mul_right _ _ (by positivity) (by simp)]
  · have hJ4 : G3K.cJ = 4 := rfl
    have hX' : rstep cand.childStep X (0, 0) = ⟨X.i + 1, X.e + 1, 1, X.σ,
        Function.update X.out ⟨X.i, hi⟩ ((X.e + 1 : ℕ) : ℕ∞)⟩ := by
      rw [rstep_exit X hi, if_pos (by omega)]
    have hdn := domNext_abs t X (rstep cand.childStep X (0, 0)) hi he
      (by rw [hX']; show X.e + 1 ≤ cand.T; omega) (by rw [hX']; show 1 ≤ 16; omega)
      (by rw [hX']; show 4 ≤ X.i + 1; omega)
    rw [hdn, tauW_live]
    unfold Ws
    rw [if_pos (Or.inr (Or.inl (by rw [hX']; show 4 ≤ X.i + 1; omega))), mul_zero]
    exact zero_le

/-- **The exit to a live state** (`p > 1`, or `p = 1` before phase `J`). -/
theorem finish_live_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X X'' : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4])
    (hrs : rstep cand.childStep X (0, 0) = X'') (hi'' : X''.i < 4) (he'' : X''.e = X.e + 1)
    (hp1'' : 1 ≤ X''.p) (hp'' : X''.p ≤ 16) (hσ'' : X''.σ = X.σ)
    (a : G3K.Spec.Acc) (R : ℝ≥0∞) (hI : InvW X a R) (ev : ℕ)
    (hf : G3K.Spec.final (entry t X) (X.i + 1) a ev
      (G3K.exitHi * G3K.Spec.wUp (G3K.Spec.look t (keyOf X'') (keyOf (lumpState cand X''))))
      (G3K.Spec.exitStop (X.i + 1) c1 c2 c3 c4 X.p)
      (decide ((G3K.Spec.look t (keyOf X'') (keyOf (lumpState cand X''))).flag ≤ 1)) = true) :
    5⁻¹ * tauW t (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        (rstep cand.childStep X (0, 0))) + R ≤ Ws t (X, false) := by
  obtain ⟨-, hi, he, hp1, hp16, hwf, hk⟩ := id hX
  change X.i < 4 at hi
  change X.e ≤ cand.T at he
  obtain ⟨H, hww, hH, hR⟩ := hI
  have hwf'' : ∀ c, cand.ChildWF (X''.σ c) := by rw [hσ'']; exact hwf
  have hb := boundsOK_sound _ _ (entry_bounds t h X hwf (by change X.p ≤ 16 at hp16; omega) hk)
  obtain ⟨hpack, hle⟩ := look_W_pack t h X'' hp'' hwf''
  set tt := G3K.Spec.look t (keyOf X'') (keyOf (lumpState cand X'')) with htt
  have hEx : ∀ l, G3K.exitHi * (if l = 0 then 0 else lane 128 (l - 1) tt.w) ≤
      G3K.exitHi * (2 ^ 77 - 1) := by
    intro l
    refine Nat.mul_le_mul_left _ ?_
    split_ifs
    · exact Nat.zero_le _
    · exact hle _
  obtain ⟨hok, heok, hlanes⟩ := final_read (entry t X) (X.i + 1) a ev _ _ _ H _
    (fun j => (hb.2.2.2 j).1) hb.2.2.1 hww hH (exitHi_wUp tt hpack) hEx hf
  have hT8 : cand.T = 8 := rfl
  rw [Ws_cov t X hX]
  refine combine_W _ (H (cand.T - X.e))
    (G3K.exitHi * (if cand.T - X.e = 0 then 0 else lane 128 (cand.T - X.e - 1) tt.w)) a.pp
    (if cand.T - X.e = 0 then G3K.Spec.exitStop (X.i + 1) c1 c2 c3 c4 X.p * 2 ^ 40 else 0) _ R _
    (hlanes _ (by omega)) (hR hok) ?_
  by_cases heT : X.e = cand.T
  · rw [if_pos (by omega), if_pos (by omega), mul_zero, zero_add]
    refine (exit_stop_W t X hi (by omega) hwf c1 c2 c3 c4 hL heT).trans (le_of_eq ?_)
    congr 1
    rw [show (2 : ℝ≥0∞) ^ 88 = 2 ^ 48 * 2 ^ 40 by norm_num, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, ENNReal.mul_div_mul_right _ _ (by positivity) (by simp)]
  · rw [if_neg (by omega), if_neg (by omega), add_zero]
    have he1 : X''.e ≤ cand.T := by omega
    have hflag : tt.flag ≤ 1 := of_decide_eq_true heok
    rw [hrs, domNext_live t X X'' hi he hi'' he1 hp'', tauW_live]
    have hW'' := (look_W t h X'' hi'' he1 hp1'' hp'' hwf'').2.2 hflag
    rw [he''] at hW''
    have hidx : cand.T - X.e - 1 = cand.T - (X.e + 1) := by omega
    rw [hidx]
    calc 5⁻¹ * Ws t (keptOf t X'', false) ≤
          5⁻¹ * (thetaC ^ (X.e + 1) * ((lane 128 (cand.T - (X.e + 1)) tt.w : ℝ≥0∞) / 2 ^ 40)) := by
          gcongr
      _ ≤ _ := wexit_cast _ _ _ _ thetaC_exitHi

/-- **The exit and the comparisons** close the inequality at a covered state. -/
theorem finish_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) (a : G3K.Spec.Acc) (R : ℝ≥0∞)
    (hI : InvW X a R)
    (hf : G3K.Spec.finish t (entry t X) (X.i + 1) c1 c2 c3 c4 X.p a
      (G3K.Spec.exitStop (X.i + 1) c1 c2 c3 c4 X.p) = true) :
    5⁻¹ * tauW t (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        (rstep cand.childStep X (0, 0))) + R ≤ Ws t (X, false) := by
  obtain ⟨-, hi, he, hp1, hp16, hwf, -⟩ := id hX
  change X.i < 4 at hi
  change 1 ≤ X.p at hp1
  change X.p ≤ 16 at hp16
  have hJ4 : G3K.cJ = 4 := rfl
  unfold G3K.Spec.finish at hf
  split_ifs at hf with hp hq
  · exact finish_abs_W t h X hX c1 c2 c3 c4 hL hp hq a R hI _ hf
  · -- the last frog of a phase before `J` exits: the next phase
    unfold G3K.Spec.exitNext at hf
    have hi3 : X.i + 1 < 4 := by omega
    obtain ⟨X'', hX''⟩ : ∃ X'' : RState CState 4 4, X'' = ⟨X.i + 1, X.e + 1, 1, X.σ,
        Function.update X.out ⟨X.i, hi⟩ ((X.e + 1 : ℕ) : ℕ∞)⟩ := ⟨_, rfl⟩
    have hrs : rstep cand.childStep X (0, 0) = X'' := by
      rw [hX'', rstep_exit X hi, if_pos (by omega)]
    have hk1 : keyOf X'' = G3K.Spec.enc (X.i + 1 + 1) c1 c2 c3 c4 1 := by
      rw [hX'']; exact keyOf_enc _ c1 c2 c3 c4 hL
    have hk2 : keyOf (lumpState cand X'') = G3K.Spec.lumpKey4 (X.i + 1 + 1) c1 c2 c3 c4 1 := by
      rw [hX'']; exact keyOf_lump_enc _ c1 c2 c3 c4 hwf hL
    rw [← hk1, ← hk2] at hf
    exact finish_live_W t h X X'' hX c1 c2 c3 c4 hL hrs (by rw [hX'']; exact hi3)
      (by rw [hX'']) (by rw [hX'']) (by rw [hX'']; show 1 ≤ 16; omega) (by rw [hX'']) a R hI _ hf
  · -- a frog exits and others remain: the same phase
    unfold G3K.Spec.exitSame at hf
    obtain ⟨X'', hX''⟩ : ∃ X'' : RState CState 4 4,
        X'' = ⟨X.i, X.e + 1, X.p - 1, X.σ, X.out⟩ := ⟨_, rfl⟩
    have hrs : rstep cand.childStep X (0, 0) = X'' := by
      rw [hX'', rstep_exit X hi, if_neg (by omega)]
    have hk1 : keyOf X'' = G3K.Spec.enc (X.i + 1) c1 c2 c3 c4 (X.p - 1) := by
      rw [hX'']; exact keyOf_enc _ c1 c2 c3 c4 hL
    have hk2 : keyOf (lumpState cand X'') = G3K.Spec.lumpKey4 (X.i + 1) c1 c2 c3 c4 (X.p - 1) := by
      rw [hX'']; exact keyOf_lump_enc _ c1 c2 c3 c4 hwf hL
    rw [← hk1, ← hk2] at hf
    exact finish_live_W t h X X'' hX c1 c2 c3 c4 hL hrs (by rw [hX'']; exact hi)
      (by rw [hX'']) (by rw [hX'']; show 1 ≤ X.p - 1; omega)
      (by rw [hX'']; show X.p - 1 ≤ 16; omega) (by rw [hX'']) a R hI _ hf

/-- The check of a covered state, at its decoded key. -/
theorem checkS_of_covered (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) :
    G3K.Spec.checkS t (entry t X) (X.i + 1) c1 c2 c3 c4 X.p = true := by
  obtain ⟨-, hi, he, hp1, hp16, hwf, hk⟩ := hX
  have hs : G3K.Spec.stateCheck t (entry t X) (keyOf X) = true :=
    (G3K.Spec.checkAll_sound h (keyOf X) hk).2
  have hlt : ∀ x ∈ [c1, c2, c3, c4], x < 38 := fun x hx =>
    codeMs_lt X.σ hwf x (by rw [← hL] at hx; exact (Multiset.mem_sort _).1 hx)
  have hp : X.p < 128 := by change X.p ≤ 16 at hp16; omega
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := dec_enc (X.i + 1) c1 c2 c3 c4 X.p
    (by have := hlt c1 (by simp); omega) (by have := hlt c2 (by simp); omega)
    (by have := hlt c3 (by simp); omega) (by have := hlt c4 (by simp); omega) hp
  unfold G3K.Spec.stateCheck at hs
  rw [keyOf_enc X c1 c2 c3 c4 hL, d1, d2, d3, d4, d5, d6] at hs
  exact hs

/-- **The inequality at a covered state**. -/
theorem covered_W (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) :
    ∫⁻ ξ, tauW t (X, false) (gT t (X, false) ξ) ∂nuC ≤ Ws t (X, false) := by
  have hwf : ∀ c, cand.ChildWF (X.σ c) := hX.2.2.2.2.2.1
  rw [lintegral_candDom 16 (keepOf t) (tauW t (X, false)) (X, false) hwf]
  obtain ⟨c1, c2, c3, c4, hL, -, -, -⟩ := wsort_four (codeMs X.σ) (codeMs_card X.σ)
  have hm := moves_W t h X hX c1 c2 c3 c4 hL
  have hck := checkS_of_covered t h X hX c1 c2 c3 c4 hL
  unfold G3K.Spec.checkS at hck
  generalize G3K.Spec.moves t (X.i + 1) c1 c2 c3 c4 X.p = M at hm hck
  exact finish_W t h X hX c1 c2 c3 c4 hL M _ hm hck

/-- **Item 5 (W)**: `Ws t` is a super-solution, for every tree that passes the checker. -/
theorem Ws_super_of_check (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) :
    fkRhs (flagReward (gT t) phiC) nuC +
      FrogModel.LinSys.app (fkKernel (gT t) (fun _ _ => 1) nuC) (Ws t) ≤ Ws t := by
  intro y
  show fkRhs (flagReward (gT t) phiC) nuC y +
    FrogModel.LinSys.app (fkKernel (gT t) (fun _ _ => 1) nuC) (Ws t) y ≤ Ws t y
  rw [rhsW_eq]
  by_cases h0 : y.2 = true ∨ 4 ≤ y.1.i ∨ cand.T < y.1.e
  · rw [lintegral_congr (fun ξ => tauW_dead t y h0 ξ), lintegral_zero]
    exact zero_le
  · by_cases hc : Covered t y
    · obtain ⟨X, b⟩ := y
      obtain rfl : b = false := hc.1
      exact covered_W t h X hc
    · unfold Ws
      rw [if_neg h0, if_neg hc]
      exact le_top

end FrogModel.Engine.G3
