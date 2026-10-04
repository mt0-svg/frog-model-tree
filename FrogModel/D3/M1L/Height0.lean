module

public import FrogModel.D3.M1L.Laws
public import FrogModel.D3.M1L.F1Zero
public import FrogModel.Engine.Markov
public import FrogModel.D3.ChainLaw

@[expose] public section

/-!
# M1_L at height 0: the law of the top closure at `p.m = 0`

The law of a closure at height 0 (Section 13 of the paper), for the top closure at `m = 0`: on the
frog paths, the run of M1_L with `k` entrants ends with `b` ups with probability
`capBin V q_L (k + 1) 0 b`, the law of `min (Bin(k + 1, q_L), V)`.

Route, as in the proof of Lemma 13.2: the values read are i.i.d. (`map_fp_read`); the run projects
to the chain `hstep` on the directions (`proj_upd`); the probability to end with `b` ups is the
least solution of the first-step system (`Engine.measure_exists_traj_eq_least`); `U0` is a solution
(`U0_round`, `U0_ghost`), so the least solution is at most `U0`; the expected number of reads is at
most `T0` (`T0_drift`, `Engine.lintegral_tsum_traj_eq_least`), so the chain ends almost surely and
the probabilities sum to one, as `U0` does: they are equal.
-/

open MeasureTheory ProbabilityTheory FrogModel
open scoped ENNReal

/-- A rewriting of the cap used by `capBin_succ`. -/
theorem FrogModel.D3.min_add_succ_eq_min_min_add (a V j : ℕ) (ha : a ≤ V) :
    min (a + (j + 1)) V = min (min (a + 1) V + j) V := by
  by_cases h : a + 1 ≤ V
  · have hmin1 : min (a + 1) V = a + 1 := Nat.min_eq_left h
    rw [hmin1]
    rw [show a + 1 + j = a + (j + 1) by omega]
  · have hmin1 : min (a + 1) V = V := Nat.min_eq_right (by omega)
    rw [hmin1]
    have hbig : V ≤ a + (j + 1) := by omega
    rw [Nat.min_eq_right hbig, Nat.min_eq_right (show V ≤ V + j from by omega)]

/-- First step of the capped binomial: the first of `p + 1` trials succeeds with probability `x`. -/
theorem FrogModel.D3.capBin_succ (V : ℕ) (x : ℝ) (p a b : ℕ) (ha : a ≤ V) :
    FrogModel.D3.capBin V x (p + 1) a b =
      x * FrogModel.D3.capBin V x p (min (a + 1) V) b + (1 - x) * FrogModel.D3.capBin V x p a b := by
  unfold FrogModel.D3.capBin
  rw [Finset.sum_range_succ']
  simp [Nat.choose_zero_right, pow_zero, add_zero]
  have hchoose : ∀ j, ((p+1 : ℕ).choose (j+1) : ℝ) = (p.choose j : ℝ) + (p.choose (j+1) : ℝ) := by
    intro j; simp [Nat.choose_succ_succ]
  simp_rw [hchoose]
  simp_rw [add_mul]
  simp_rw [ite_add_zero]
  rw [Finset.sum_add_distrib]
  -- Goal: (if min a V = b then (1-x)^(p+1) else 0) + S1 + S2 = x * T + (1-x) * U
  -- Factor x from S1: rewrite x^(j+1) = x * x^j
  have hxpow : ∀ j, x ^ (j+1 : ℕ) = x * x ^ j := by
    intro j; simp [pow_succ, mul_comm]
  simp_rw [hxpow]
  -- Now S1 = Σ_j [min(a+j+1,V)=b] * C(p,j) * (x * x^j) * (1-x)^(p-j)
  -- Regroup: (x * x^j) * (1-x)^(p-j) = x * (x^j * (1-x)^(p-j))
  -- Then factor x out of the sum
  -- Let A(j) = if min (a+(j+1)) V = b then (p.choose j : ℝ) * x^j * (1-x)^(p-j) else 0
  -- Then S1 = Σ_j C(p,j) * x * A(j) = x * Σ_j A(j)
  -- We'll work with the goal as-is and use ring/field_simp later
  -- Instead, let's use the g(k) auxiliary function approach from the start
  -- Define g(k) = [min(a+k,V)=b] * C(p,k) * x^k * (1-x)^(p+1-k)
  set g := fun (k : ℕ) => if min (a + k) V = b then (p.choose k : ℝ) * x ^ k * (1 - x) ^ (p + 1 - k) else 0 with hg
  have hg0 : g 0 = if min a V = b then (1 - x) ^ (p + 1) else 0 := by
    simp [g]
  have hg_last : g (p + 1) = 0 := by
    simp [g]
  have hsum_g : (∑ k ∈ Finset.range (p + 1 + 1), g k) = (∑ k ∈ Finset.range (p + 1), g k) := by
    rw [Finset.sum_range_succ, hg_last, add_zero]
  have hsum_g_split : (∑ k ∈ Finset.range (p + 1 + 1), g k) = g 0 + (∑ j ∈ Finset.range (p + 1), g (j + 1)) := by
    rw [Finset.sum_range_succ', add_comm]
  have hU : (∑ k ∈ Finset.range (p + 1), g k) = (1 - x) * (∑ j ∈ Finset.range (p + 1), if min (a + j) V = b then (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) else 0) := by
    simp_rw [g]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases h : min (a + j) V = b
    · have h_exp : p + 1 - j = (p - j) + 1 := by
        have hjle : j ≤ p := by
          have := Finset.mem_range.1 hj
          omega
        omega
      simp [h, mul_assoc, h_exp, pow_succ, mul_comm, mul_left_comm]
    · simp [h]
  -- Now express the goal in terms of g
  -- The LHS after sum_range_succ' and simp is:
  -- (if min a V = b then (1-x)^(p+1) else 0) + Σ_j [min(a+j+1,V)=b] * C(p+1,j+1) * x^(j+1) * (1-x)^(p-j)
  -- We already rewrote C(p+1,j+1) = C(p,j) + C(p,j+1) and split into S1 + S2
  -- Let's compute S1 + S2 + (if min a V = b then (1-x)^(p+1) else 0) in terms of g
  -- S1 = Σ_j [min(a+j+1,V)=b] * C(p,j) * x^(j+1) * (1-x)^(p-j)
  -- S2 = Σ_j [min(a+j+1,V)=b] * C(p,j+1) * x^(j+1) * (1-x)^(p-j)
  -- Note: g(j+1) = [min(a+j+1,V)=b] * C(p,j+1) * x^(j+1) * (1-x)^(p-j)
  -- So S2 = Σ_j g(j+1)
  -- And S1 = Σ_j [min(a+j+1,V)=b] * C(p,j) * x * x^j * (1-x)^(p-j)
  --       = x * Σ_j [min(a+j+1,V)=b] * C(p,j) * x^j * (1-x)^(p-j)
  --       = x * Σ_j [min(min(a+1,V)+j,V)=b] * C(p,j) * x^j * (1-x)^(p-j)  (by min lemma)
  --       = x * T
  -- So the LHS = (if min a V = b then (1-x)^(p+1) else 0) + x*T + Σ_j g(j+1)
  -- The RHS = x*T + (1-x)*U
  -- Using hU: (1-x)*U = Σ_k g(k)
  -- And hsum_g: Σ_{k=0}^{p+1} g(k) = Σ_{k=0}^{p} g(k)
  -- So Σ_{k=0}^{p+1} g(k) = g(0) + Σ_{j=0}^{p} g(j+1) = g(0) + S2
  -- Therefore S2 + g(0) = (1-x)*U
  -- And g(0) = (if min a V = b then (1-x)^(p+1) else 0)
  -- So LHS = g(0) + x*T + S2 = x*T + (S2 + g(0)) = x*T + (1-x)*U = RHS

  -- Let's formalize this.
  -- First, express S2 as Σ_j g(j+1)
  have hS2 : (∑ j ∈ Finset.range (p + 1), if min (a + (j + 1)) V = b then (p.choose (j + 1) : ℝ) * x ^ (j + 1) * (1 - x) ^ (p - j) else 0) =
      (∑ j ∈ Finset.range (p + 1), g (j + 1)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    dsimp [g]
    have : p - j = p + 1 - (j + 1) := by omega
    rw [this]
  -- The goal has (x * x^j) but hS2 has x^(j+1); rewrite back
  simp_rw [← hxpow]
  rw [hS2]
  -- Now goal: (if min a V = b then (1-x)^(p+1) else 0) + S1 + (∑ j, g(j+1)) = x*T + (1-x)*U
  -- Express S1 as x * T' where T' = Σ_j [min(a+j+1,V)=b] * C(p,j) * x^j * (1-x)^(p-j)
  -- Then use min lemma to relate T' to T
  have hmin : ∀ j, min (a + (j + 1)) V = min (min (a + 1) V + j) V := by
    intro j
    by_cases h : a + 1 ≤ V
    · have hmin1 : min (a + 1) V = a + 1 := Nat.min_eq_left h
      rw [hmin1]
      rw [show a + 1 + j = a + (j + 1) by omega]
    · have hmin1 : min (a + 1) V = V := Nat.min_eq_right (by omega)
      rw [hmin1]
      have hbig : V ≤ a + (j + 1) := by omega
      rw [Nat.min_eq_right hbig, Nat.min_eq_right (show V ≤ V + j from by omega)]
  have hS1 : (∑ j ∈ Finset.range (p + 1), if min (a + (j + 1)) V = b then (p.choose j : ℝ) * x ^ (j + 1) * (1 - x) ^ (p - j) else 0) =
      x * (∑ j ∈ Finset.range (p + 1), if min (min (a + 1) V + j) V = b then (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) else 0) := by
    calc
      (∑ j ∈ Finset.range (p + 1), if min (a + (j + 1)) V = b then (p.choose j : ℝ) * x ^ (j + 1) * (1 - x) ^ (p - j) else 0) =
          (∑ j ∈ Finset.range (p + 1), if min (a + (j + 1)) V = b then x * ((p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j)) else 0) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [pow_succ, mul_assoc, mul_comm]
      _ = x * (∑ j ∈ Finset.range (p + 1), if min (a + (j + 1)) V = b then (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j hj => ?_
        simp [mul_assoc, mul_comm]
      _ = x * (∑ j ∈ Finset.range (p + 1), if min (min (a + 1) V + j) V = b then (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) else 0) := by
        refine congrArg (fun s => x * s) (Finset.sum_congr rfl fun j hj => ?_)
        rw [hmin j]
  rw [hS1]
  -- Now goal: (if min a V = b then (1-x)^(p+1) else 0) + x*T + (∑ j, g(j+1)) = x*T + (1-x)*U
  -- Cancel x*T from both sides
  -- We need: (if min a V = b then (1-x)^(p+1) else 0) + (∑ j, g(j+1)) = (1-x)*U
  -- From hU: (1-x)*U = Σ_k g(k)
  rw [← hU]
  -- Goal: (if min a V = b then (1-x)^(p+1) else 0) + (∑ j, g(j+1)) = Σ_k g(k)
  -- From hsum_g_split: Σ_{k=0}^{p+1} g(k) = g(0) + Σ_{j=0}^{p} g(j+1)
  -- From hsum_g: Σ_{k=0}^{p+1} g(k) = Σ_{k=0}^{p} g(k)
  -- So: g(0) + Σ_j g(j+1) = Σ_k g(k)
  -- And hg0: g(0) = (if min a V = b then (1-x)^(p+1) else 0)
  -- Therefore: (if min a V = b then (1-x)^(p+1) else 0) + Σ_j g(j+1) = Σ_k g(k)
  -- Which is exactly our goal!
  rw [← hg0]
  -- Goal: ((x * T) + (∑ j, g(j+1)) + g 0) = (x * T) + (∑ k, g k)
  -- Cancel x*T from both sides, then use hsum_g_split and hsum_g
  have hkey : g 0 + (∑ j ∈ Finset.range (p + 1), g (j + 1)) = (∑ k ∈ Finset.range (p + 1), g k) := by
    rw [← hsum_g_split, hsum_g]
  linarith

/-- The arithmetic of `pL` and `qL`. -/
theorem FrogModel.D3.pL_qL_facts (L : ℕ) (hL : 2 ≤ L) :
    0 ≤ FrogModel.D3.pL L ∧ FrogModel.D3.pL L < 1 / 3 ∧
      1 / 3 - FrogModel.D3.pL L = 2 / (3 * ((3 : ℝ) ^ L - 1)) ∧
      FrogModel.D3.qL L = (1 / 4) / (1 - 3 * FrogModel.D3.pL L / 4) ∧
      0 < FrogModel.D3.qL L ∧ FrogModel.D3.qL L < 1 / 3 ∧
      (3 / 4) * (1 - FrogModel.D3.pL L) / (1 - 3 * FrogModel.D3.pL L / 4) = 1 - FrogModel.D3.qL L := by
  set p := FrogModel.D3.pL L with hp
  set q := FrogModel.D3.qL L with hq
  have hL0 : 0 < L := by omega
  have hL1 : 1 ≤ L := by omega
  have h3pos : 0 < (3 : ℝ) := by norm_num
  have h3gt1 : (1 : ℝ) < (3 : ℝ) := by norm_num
  have htp : 0 < (3 : ℝ) ^ L := pow_pos h3pos L
  have htp_gt1 : (1 : ℝ) < (3 : ℝ) ^ L := by
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℕ) := by norm_num
      _ < (3 : ℝ) ^ L := pow_lt_pow_right₀ h3gt1 hL0
  have h_denom_pos : 0 < (3 : ℝ) ^ L - 1 := by linarith
  have h_pow_eq : (3 : ℝ) ^ L = (3 : ℝ) ^ (L - 1) * (3 : ℝ) := by
    calc
      (3 : ℝ) ^ L = (3 : ℝ) ^ ((L - 1) + 1) := by rw [Nat.sub_add_cancel hL1]
      _ = (3 : ℝ) ^ (L - 1) * (3 : ℝ) ^ 1 := by rw [pow_add]
      _ = (3 : ℝ) ^ (L - 1) * (3 : ℝ) := by norm_num
  have h_upos : 0 < (3 : ℝ) ^ (L - 1) := pow_pos h3pos (L - 1)
  have h_upos_ge_one : (1 : ℝ) ≤ (3 : ℝ) ^ (L - 1) := by
    have hLm1 : 1 ≤ L - 1 := by omega
    have ha : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
    have h := pow_le_pow_right₀ (a := (3 : ℝ)) ha hLm1
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (1 : ℕ) := by norm_num
    exact h1.trans h
  have h_num_nonneg : 0 ≤ (3 : ℝ) ^ (L - 1) - 1 := by linarith
  have hp_nonneg : 0 ≤ p := by
    dsimp [p, FrogModel.D3.pL]
    exact div_nonneg h_num_nonneg (by linarith)
  have hp_lt_third : p < 1 / 3 := by
    dsimp [p, FrogModel.D3.pL]
    field_simp [h_denom_pos.ne.symm]
    nlinarith
  have h_eq1 : 1 / 3 - p = 2 / (3 * ((3 : ℝ) ^ L - 1)) := by
    dsimp [p, FrogModel.D3.pL]
    field_simp [h_denom_pos.ne.symm]
    ring_nf
    nlinarith
  have h_eq2 : q = (1 / 4) / (1 - 3 * p / 4) := by
    dsimp [q, FrogModel.D3.qL, p]
    field_simp
  have h_pos : 0 < q := by
    dsimp [q, FrogModel.D3.qL]
    refine div_pos (by norm_num) ?_
    have : 3 * p < 1 := by linarith
    linarith
  have h_lt_third : q < 1 / 3 := by
    dsimp [q, FrogModel.D3.qL]
    refine (one_div_lt_one_div ?_ ?_).mpr ?_
    · have : 3 * p < 1 := by linarith
      linarith
    · norm_num
    · have : 3 * p < 1 := by linarith
      linarith
  have h_denom2_pos : 0 < 4 - 3 * p := by linarith
  have h_eq3 : (3 / 4) * (1 - p) / (1 - 3 * p / 4) = 1 - q := by
    dsimp [q, FrogModel.D3.qL]
    rw [← hp]
    field_simp [h_denom2_pos.ne.symm]
    ring_nf
  exact ⟨hp_nonneg, hp_lt_third, h_eq1, h_eq2, h_pos, h_lt_third, h_eq3⟩

/-- The return probabilities of a ghost walk: boundary values, `r_1 = p_L`, the first-step equation
inside, and the bounds. -/
theorem FrogModel.D3.rL_facts (L : ℕ) (hL : 1 ≤ L) :
    FrogModel.D3.rL L 0 = 1 ∧ FrogModel.D3.rL L L = 0 ∧ FrogModel.D3.rL L 1 = FrogModel.D3.pL L ∧
      (∀ d : ℕ, 1 ≤ d → d < L →
        FrogModel.D3.rL L d = 1 / 4 * FrogModel.D3.rL L (d - 1) + 3 / 4 * FrogModel.D3.rL L (d + 1)) ∧
      ∀ d : ℕ, 0 ≤ FrogModel.D3.rL L d ∧ FrogModel.D3.rL L d ≤ 1 := by
  have h3pos : (1 : ℝ) ≤ 3 := by norm_num
  have h3Lpos : 0 < (3 : ℝ) ^ L - 1 := by
    have h : 1 < (3 : ℝ) ^ L := by
      calc
        1 < (3 : ℝ) ^ 1 := by norm_num
        _ ≤ (3 : ℝ) ^ L := pow_le_pow_right₀ h3pos hL
    linarith
  have h3Lne_zero : (3 : ℝ) ^ L - 1 ≠ 0 := by linarith
  have hone_le_pow (n : ℕ) : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ h3pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- rL L 0 = 1
    unfold FrogModel.D3.rL
    have hsub : L - 0 = L := by omega
    simp [hsub, h3Lne_zero]
  · -- rL L L = 0
    unfold FrogModel.D3.rL
    simp
  · -- rL L 1 = pL L
    unfold FrogModel.D3.rL FrogModel.D3.pL
    rfl
  · -- recurrence
    intro d hd1 hdLt
    unfold FrogModel.D3.rL
    field_simp [h3Lne_zero]
    ring_nf
    have h_exp1 : L - (d - 1) = (L - d) + 1 := by omega
    have h_exp2 : L - (1 + d) = (L - d) - 1 := by omega
    have hk : 1 ≤ L - d := by omega
    rw [h_exp1, h_exp2]
    have h_pow_eq : (3 : ℝ) ^ (L - d) = (3 : ℝ) * (3 : ℝ) ^ ((L - d) - 1) := by
      calc
        (3 : ℝ) ^ (L - d) = (3 : ℝ) ^ (((L - d) - 1) + 1) := by rw [Nat.sub_add_cancel hk]
        _ = (3 : ℝ) ^ ((L - d) - 1) * (3 : ℝ) := by rw [pow_succ]
        _ = (3 : ℝ) * (3 : ℝ) ^ ((L - d) - 1) := by ring
    rw [pow_succ, h_pow_eq]
    ring
  · -- bounds
    intro d
    unfold FrogModel.D3.rL
    constructor
    · -- 0 ≤ rL L d
      refine div_nonneg ?_ (by linarith)
      have h : 1 ≤ (3 : ℝ) ^ (L - d) := one_le_pow₀ h3pos
      linarith
    · -- rL L d ≤ 1
      refine (div_le_one ?_).mpr ?_
      · linarith
      · have h : (3 : ℝ) ^ (L - d) ≤ (3 : ℝ) ^ L :=
          pow_le_pow_right₀ h3pos (Nat.sub_le L d)
        linarith

/-- The capped binomial: nonnegative, zero above the cap, and a point mass for zero trials. -/
theorem FrogModel.D3.capBin_basic (V : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∀ p a b : ℕ, 0 ≤ FrogModel.D3.capBin V x p a b) ∧
      (∀ p a b : ℕ, V < b → FrogModel.D3.capBin V x p a b = 0) ∧
      ∀ a b : ℕ, a ≤ V → FrogModel.D3.capBin V x 0 a b = if a = b then 1 else 0 := by
  have hx0' : 0 ≤ 1 - x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro p a b
    dsimp [FrogModel.D3.capBin]
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs with h
    · positivity
    · rfl
  · intro p a b hVb
    dsimp [FrogModel.D3.capBin]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hmin : min (a + j) V ≤ V := Nat.min_le_right _ _
    have : min (a + j) V ≠ b := by
      intro h_eq
      have hle : b ≤ V := h_eq ▸ hmin
      linarith
    simp [this]
  · intro a b ha
    dsimp [FrogModel.D3.capBin]
    simp [Nat.min_eq_left ha]

/-- The capped binomial is a probability law on `{0, ..., V}`. -/
theorem FrogModel.D3.sum_capBin (V : ℕ) (x : ℝ) (p a : ℕ) :
    ∑ b ∈ Finset.range (V + 1), FrogModel.D3.capBin V x p a b = 1 := by
  calc
    ∑ b ∈ Finset.range (V + 1), FrogModel.D3.capBin V x p a b
        = ∑ b ∈ Finset.range (V + 1), ∑ j ∈ Finset.range (p + 1),
            if min (a + j) V = b then (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) else 0 := rfl
    _ = ∑ j ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (V + 1),
            if min (a + j) V = b then (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hmem : min (a + j) V ∈ Finset.range (V + 1) := by
        apply Finset.mem_range.mpr
        have hmin := Nat.min_le_right (a + j) V
        omega
      rw [Finset.sum_ite_eq]
      simp [hmem]
    _ = (x + (1 - x)) ^ p := by
      rw [add_pow]
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = 1 ^ p := by ring
    _ = 1 := by simp

/-- **First step of a round at height 0.** -/
theorem FrogModel.D3.U0_round (V L b n u : ℕ) (hL : 2 ≤ L) (hu : u ≤ V) (hn : 1 ≤ n) :
    FrogModel.D3.U0 V L b (n, u, 0) =
      1 / 4 * FrogModel.D3.U0 V L b (FrogModel.D3.hstep V L (n, u, 0) 0) +
        3 / 4 * FrogModel.D3.U0 V L b (FrogModel.D3.hstep V L (n, u, 0) 1) := by
  rcases Nat.exists_eq_add_of_le' hn with ⟨m, rfl⟩
  simp [FrogModel.D3.hstep, FrogModel.D3.U0]
  have hrL : FrogModel.D3.rL L 1 = FrogModel.D3.pL L :=
    (FrogModel.D3.rL_facts L (by omega : 1 ≤ L)).2.2.1
  rw [hrL]
  rw [FrogModel.D3.capBin_succ V (FrogModel.D3.qL L) m u b hu]
  have hfacts := FrogModel.D3.pL_qL_facts L hL
  rcases hfacts with ⟨hp_nonneg, hp_lt, h_eq1, h_qdef, hq_pos, hq_lt, h_eq2⟩
  have h_denom_ne_zero : 1 - 3 * FrogModel.D3.pL L / 4 ≠ 0 := by
    intro hzero
    have : FrogModel.D3.pL L = 4/3 := by linarith
    linarith [hp_lt, this]
  have hq_mul : FrogModel.D3.qL L * (1 - 3 * FrogModel.D3.pL L / 4) = 1/4 := by
    rw [h_qdef]
    have h_denom2_ne_zero : 4 - 3 * FrogModel.D3.pL L ≠ 0 := by
      intro hzero2
      have : FrogModel.D3.pL L = 4/3 := by linarith
      linarith [hp_lt, this]
    field_simp [h_denom_ne_zero, h_denom2_ne_zero]
  have h_one_minus_q_mul : (1 - FrogModel.D3.qL L) * (1 - 3 * FrogModel.D3.pL L / 4) = (3/4) * (1 - FrogModel.D3.pL L) := by
    field_simp [h_denom_ne_zero] at h_eq2 ⊢
    linarith
  by_cases huV : u < V
  · simp [huV]
    set C1 := FrogModel.D3.capBin V (FrogModel.D3.qL L) m (u + 1) b with hC1
    set C2 := FrogModel.D3.capBin V (FrogModel.D3.qL L) m u b with hC2
    have hdiff : FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2
        - (1/4 * C1 + 3/4 * (FrogModel.D3.pL L * (FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2) + (1 - FrogModel.D3.pL L) * C2)) = 0 := by
      calc
        FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2
            - (1/4 * C1 + 3/4 * (FrogModel.D3.pL L * (FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2) + (1 - FrogModel.D3.pL L) * C2))
                = (FrogModel.D3.qL L - 1/4 - 3/4 * FrogModel.D3.pL L * FrogModel.D3.qL L) * C1
                  + (1 - FrogModel.D3.qL L - 3/4 + 3/4 * FrogModel.D3.pL L * FrogModel.D3.qL L) * C2 := by ring
        _ = (FrogModel.D3.qL L * (1 - 3 * FrogModel.D3.pL L / 4) - 1/4) * C1
            + ((1 - FrogModel.D3.qL L) * (1 - 3 * FrogModel.D3.pL L / 4) - 3/4 * (1 - FrogModel.D3.pL L)) * C2 := by ring
        _ = (1/4 - 1/4) * C1 + (3/4 * (1 - FrogModel.D3.pL L) - 3/4 * (1 - FrogModel.D3.pL L)) * C2 := by rw [hq_mul, h_one_minus_q_mul]
        _ = 0 := by ring
    linarith
  · have hu_eq_V : u = V := by omega
    simp [hu_eq_V]
    set C1 := FrogModel.D3.capBin V (FrogModel.D3.qL L) m V b with hC1
    set C2 := FrogModel.D3.capBin V (FrogModel.D3.qL L) m u b with hC2
    have hdiff : FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2
        - (1/4 * C1 + 3/4 * (FrogModel.D3.pL L * (FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2) + (1 - FrogModel.D3.pL L) * C2)) = 0 := by
      calc
        FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2
            - (1/4 * C1 + 3/4 * (FrogModel.D3.pL L * (FrogModel.D3.qL L * C1 + (1 - FrogModel.D3.qL L) * C2) + (1 - FrogModel.D3.pL L) * C2))
                = (FrogModel.D3.qL L - 1/4 - 3/4 * FrogModel.D3.pL L * FrogModel.D3.qL L) * C1
                  + (1 - FrogModel.D3.qL L - 3/4 + 3/4 * FrogModel.D3.pL L * FrogModel.D3.qL L) * C2 := by ring
        _ = (FrogModel.D3.qL L * (1 - 3 * FrogModel.D3.pL L / 4) - 1/4) * C1
            + ((1 - FrogModel.D3.qL L) * (1 - 3 * FrogModel.D3.pL L / 4) - 3/4 * (1 - FrogModel.D3.pL L)) * C2 := by ring
        _ = (1/4 - 1/4) * C1 + (3/4 * (1 - FrogModel.D3.pL L) - 3/4 * (1 - FrogModel.D3.pL L)) * C2 := by rw [hq_mul, h_one_minus_q_mul]
        _ = 0 := by ring
    linarith

/-- **First step of a ghost step at height 0.** -/
theorem FrogModel.D3.U0_ghost (V L b n u d : ℕ) (hL : 2 ≤ L) (hd : d + 1 < L) :
    FrogModel.D3.U0 V L b (n, u, d + 1) =
      1 / 4 * FrogModel.D3.U0 V L b (FrogModel.D3.hstep V L (n, u, d + 1) 0) +
        3 / 4 * FrogModel.D3.U0 V L b (FrogModel.D3.hstep V L (n, u, d + 1) 1) := by
  have hL1 : 1 ≤ L := by omega
  rcases FrogModel.D3.rL_facts L hL1 with ⟨h_rL0, h_rLL, h_rL1, h_recurrence, h_bounds⟩
  have hd_lt_L : d < L := by omega
  -- Write d as either 0 or d'+1
  rcases Nat.eq_zero_or_pos d with (hd0 | hdpos)
  · -- d = 0
    subst hd0
    simp [FrogModel.D3.U0, FrogModel.D3.hstep]
    by_cases h2L : 2 = L
    · simp [h2L]
      have h_rec : rL L 1 = 1/4 := by
        have := h_recurrence 1 (by omega) (by omega)
        simpa [h2L, h_rL0, h_rLL] using this
      rw [h_rec]
      ring
    · simp [h2L]
      have h_rec := h_recurrence 1 (by omega) (by omega)
      rw [h_rL0] at h_rec
      rw [h_rec]
      ring
  · -- d ≥ 1, write d = d' + 1
    rcases Nat.exists_eq_succ_of_ne_zero hdpos.ne.symm with ⟨d', hd_eq⟩
    subst hd_eq
    simp [FrogModel.D3.U0, FrogModel.D3.hstep]
    -- Goal: rL L (d'+2) * A + (1 - rL L (d'+2)) * B = 1/4 * (match if d'+1 = L then (n,u,0) else (n,u,d'+1) with ...) + 3/4 * (match if d'+3 = L then (n,u,0) else (n,u,d'+3) with ...)
    by_cases hd1L : d' + 1 = L
    · -- d'+1 = L, so d' = L-1, d'+2 = L+1, d'+3 = L+2
      -- Note: d'+3 = L+2 ≠ L
      simp [hd1L]
      -- Goal: rL L (L+1) * A + (1 - rL L (L+1)) * B = 1/4 * B + 3/4 * (rL L (L+2) * A + (1 - rL L (L+2)) * B)
      -- But L+1 = d'+2, L+2 = d'+3
      -- From recurrence: rL L (d'+2) = 1/4 * rL L (d'+1) + 3/4 * rL L (d'+3) = 1/4 * rL L L + 3/4 * rL L (d'+3) = 3/4 * rL L (d'+3)
      have h_rec := h_recurrence (d' + 2) (by omega) (by omega)
      -- h_rec : rL L (d'+2) = 1/4 * rL L ((d'+2)-1) + 3/4 * rL L ((d'+2)+1)
      -- Simplify: (d'+2)-1 = d'+1, (d'+2)+1 = d'+3
      have h_rec_simp : rL L (d' + 2) = 1/4 * rL L (d' + 1) + 3/4 * rL L (d' + 3) := by
        simpa [add_comm, add_left_comm, add_assoc] using h_rec
      rw [hd1L, h_rLL] at h_rec_simp
      -- h_rec_simp : rL L (d'+2) = 1/4 * 0 + 3/4 * rL L (d'+3)
      -- Now rewrite d'+2 as L+1 and d'+3 as L+2
      have hL2 : d' + 3 = L + 2 := by omega
      have hL1' : d' + 2 = L + 1 := by omega
      rw [hL1', hL2] at h_rec_simp
      -- h_rec_simp : rL L (L+1) = 1/4 * 0 + 3/4 * rL L (L+2)
      -- The goal already has L+1 and L+2
      rw [h_rec_simp]
      ring_nf
    · -- d'+1 ≠ L
      by_cases hd3L : d' + 3 = L
      · -- d'+3 = L, so d'+1 = L-2, d'+2 = L-1
        -- Note: d'+1 ≠ L (already have)
        simp [hd1L, hd3L]
        -- Goal: rL L (d'+2) * A + (1 - rL L (d'+2)) * B = 1/4 * (rL L (d'+1) * A + (1 - rL L (d'+1)) * B) + 3/4 * B
        -- From recurrence: rL L (d'+2) = 1/4 * rL L (d'+1) + 3/4 * rL L (d'+3) = 1/4 * rL L (d'+1) + 3/4 * rL L L = 1/4 * rL L (d'+1)
        have h_rec := h_recurrence (d' + 2) (by omega) (by omega)
        -- h_rec : rL L (d'+2) = 1/4 * rL L ((d'+2)-1) + 3/4 * rL L ((d'+2)+1)
        have h_rec_simp : rL L (d' + 2) = 1/4 * rL L (d' + 1) + 3/4 * rL L (d' + 3) := by
          simpa [add_comm, add_left_comm, add_assoc] using h_rec
        rw [hd3L, h_rLL] at h_rec_simp
        -- h_rec_simp : rL L (d'+2) = 1/4 * rL L (d'+1) + 3/4 * 0
        rw [h_rec_simp]
        ring_nf
      · -- d'+1 ≠ L, d'+3 ≠ L
        simp [hd1L, hd3L]
        -- Goal: rL L (d'+2) * A + (1 - rL L (d'+2)) * B = 1/4 * (rL L (d'+1) * A + (1 - rL L (d'+1)) * B) + 3/4 * (rL L (d'+3) * A + (1 - rL L (d'+3)) * B)
        -- From recurrence: rL L (d'+2) = 1/4 * rL L (d'+1) + 3/4 * rL L (d'+3)
        have h_rec := h_recurrence (d' + 2) (by omega) (by omega)
        -- h_rec : rL L (d'+2) = 1/4 * rL L ((d'+2)-1) + 3/4 * rL L ((d'+2)+1)
        have h_rec_simp : rL L (d' + 2) = 1/4 * rL L (d' + 1) + 3/4 * rL L (d' + 3) := by
          simpa [add_comm, add_left_comm, add_assoc] using h_rec
        rw [h_rec_simp]
        ring_nf

/-- The outcome law of the height-0 chain from any state: nonnegative, zero above the cap, total mass one. -/
theorem FrogModel.D3.U0_nonneg_sum (V L : ℕ) (hL : 2 ≤ L) (s : ℕ × ℕ × ℕ) :
    (∀ b, 0 ≤ FrogModel.D3.U0 V L b s) ∧ (∀ b, V < b → FrogModel.D3.U0 V L b s = 0) ∧
      ∑ b ∈ Finset.range (V + 1), FrogModel.D3.U0 V L b s = 1 := by
  have hL1 : 1 ≤ L := by omega
  rcases FrogModel.D3.rL_facts L hL1 with ⟨hr0, hrL, hr1, hr_rec, hr_bounds⟩
  rcases s with ⟨n, u, d⟩
  cases' d with d
  · -- d = 0
    have hqL : 0 ≤ FrogModel.D3.qL L ∧ FrogModel.D3.qL L ≤ 1 := by
      rcases FrogModel.D3.pL_qL_facts L hL with ⟨_, _, _, _, hq0, hq_lt, _⟩
      have hq0' : 0 ≤ FrogModel.D3.qL L := le_of_lt hq0
      have hq1' : FrogModel.D3.qL L ≤ 1 := le_trans (le_of_lt hq_lt) (by norm_num : (1/3 : ℝ) ≤ 1)
      exact ⟨hq0', hq1'⟩
    rcases hqL with ⟨hq0, hq1⟩
    rcases FrogModel.D3.capBin_basic V (FrogModel.D3.qL L) hq0 hq1 with ⟨hcap_nonneg, hcap_zero, hcap_sum⟩
    dsimp [FrogModel.D3.U0]
    refine ⟨?_, ?_, ?_⟩
    · intro b; exact hcap_nonneg n u b
    · intro b hb; exact hcap_zero n u b hb
    · exact FrogModel.D3.sum_capBin V (FrogModel.D3.qL L) n u
  · -- d = d + 1
    have hr_bounds_d := hr_bounds (d + 1)
    rcases hr_bounds_d with ⟨hr0_d, hr1_d⟩
    have hqL : 0 ≤ FrogModel.D3.qL L ∧ FrogModel.D3.qL L ≤ 1 := by
      rcases FrogModel.D3.pL_qL_facts L hL with ⟨_, _, _, _, hq0, hq_lt, _⟩
      have hq0' : 0 ≤ FrogModel.D3.qL L := le_of_lt hq0
      have hq1' : FrogModel.D3.qL L ≤ 1 := le_trans (le_of_lt hq_lt) (by norm_num : (1/3 : ℝ) ≤ 1)
      exact ⟨hq0', hq1'⟩
    rcases hqL with ⟨hq0, hq1⟩
    rcases FrogModel.D3.capBin_basic V (FrogModel.D3.qL L) hq0 hq1 with ⟨hcap_nonneg, hcap_zero, hcap_sum⟩
    dsimp [FrogModel.D3.U0]
    have hA_nonneg : ∀ b, 0 ≤ FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b := hcap_nonneg (n + 1) u
    have hA_zero : ∀ b, V < b → FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b = 0 := hcap_zero (n + 1) u
    have hA_sum : ∑ b ∈ Finset.range (V + 1), FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b = 1 :=
      FrogModel.D3.sum_capBin V (FrogModel.D3.qL L) (n + 1) u
    have hB_nonneg : ∀ b, 0 ≤ FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b := hcap_nonneg n u
    have hB_zero : ∀ b, V < b → FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b = 0 := hcap_zero n u
    have hB_sum : ∑ b ∈ Finset.range (V + 1), FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b = 1 :=
      FrogModel.D3.sum_capBin V (FrogModel.D3.qL L) n u
    refine ⟨?_, ?_, ?_⟩
    · intro b
      have h1 : 0 ≤ FrogModel.D3.rL L (d + 1) * FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b :=
        mul_nonneg hr0_d (hA_nonneg b)
      have h_nonneg_one_minus_r : 0 ≤ 1 - FrogModel.D3.rL L (d + 1) := by linarith
      have h2 : 0 ≤ (1 - FrogModel.D3.rL L (d + 1)) * FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b :=
        mul_nonneg h_nonneg_one_minus_r (hB_nonneg b)
      exact add_nonneg h1 h2
    · intro b hb
      have hAzero : FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b = 0 := hA_zero b hb
      have hBzero : FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b = 0 := hB_zero b hb
      simp [hAzero, hBzero]
    · calc
        ∑ b ∈ Finset.range (V + 1),
            (FrogModel.D3.rL L (d + 1) * FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b +
             (1 - FrogModel.D3.rL L (d + 1)) * FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b) =
            (∑ b ∈ Finset.range (V + 1), FrogModel.D3.rL L (d + 1) * FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b) +
            (∑ b ∈ Finset.range (V + 1), (1 - FrogModel.D3.rL L (d + 1)) * FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b) := by
          rw [Finset.sum_add_distrib]
        _ = FrogModel.D3.rL L (d + 1) * (∑ b ∈ Finset.range (V + 1), FrogModel.D3.capBin V (FrogModel.D3.qL L) (n + 1) u b) +
            (1 - FrogModel.D3.rL L (d + 1)) * (∑ b ∈ Finset.range (V + 1), FrogModel.D3.capBin V (FrogModel.D3.qL L) n u b) := by
          simp [Finset.mul_sum]
        _ = FrogModel.D3.rL L (d + 1) * 1 + (1 - FrogModel.D3.rL L (d + 1)) * 1 := by rw [hA_sum, hB_sum]
        _ = 1 := by ring

theorem FrogModel.D3.hstep_ghost_up (V L n u d : ℕ) :
    FrogModel.D3.hstep V L (n, u, d + 1) 0 =
      if d = 0 then (n + 1, u, 0) else if d = L then (n, u, 0) else (n, u, d) := by
  simp [hstep]

theorem FrogModel.D3.hstep_ghost_down (V L n u d : ℕ) (a : Fin 4) (ha : a ≠ 0) :
    FrogModel.D3.hstep V L (n, u, d + 1) a = if d + 2 = L then (n, u, 0) else (n, u, d + 2) := by
  simp [hstep, ha]

theorem FrogModel.D3.hstep_round_up (V L n u : ℕ) :
    FrogModel.D3.hstep V L (n + 1, u, 0) 0 = (n, if u < V then u + 1 else u, 0) := by
  simp [hstep]

theorem FrogModel.D3.hstep_round_down (V L n u : ℕ) (a : Fin 4) (ha : a ≠ 0) :
    FrogModel.D3.hstep V L (n + 1, u, 0) a = (n, u, 1) := by
  simp [hstep, ha]

/-- **Drift of the time bound.** From a state with ghost depth below `L`, one read lowers `T0` by at least
one on average (four times: by four over the four directions), unless the state is an end; and the depth
stays below `L`. -/
theorem FrogModel.D3.T0_drift (V L : ℕ) (hL : 2 ≤ L) (s : ℕ × ℕ × ℕ) (hs : s.2.2 < L) :
    4 * (if s.1 = 0 ∧ s.2.2 = 0 then 0 else 1) + ∑ a : Fin 4, FrogModel.D3.T0 L (FrogModel.D3.hstep V L s a) ≤
        4 * FrogModel.D3.T0 L s ∧
      ∀ a : Fin 4, (FrogModel.D3.hstep V L s a).2.2 < L := by
  obtain ⟨n, u, d⟩ := s
  simp only at hs
  have h1 : (1 : Fin 4) ≠ 0 := by decide
  have h2 : (2 : Fin 4) ≠ 0 := by decide
  have h3 : (3 : Fin 4) ≠ 0 := by decide
  cases d with
  | zero =>
    rcases n with _ | m
    · simp [hstep, T0]
      omega
    · refine ⟨?_, fun a => ?_⟩
      · rw [Fin.sum_univ_four, hstep_round_up, hstep_round_down V L m u 1 h1,
          hstep_round_down V L m u 2 h2, hstep_round_down V L m u 3 h3]
        simp only [T0, add_eq_zero, one_ne_zero, and_false, and_true, ↓reduceIte]
        have : 2 * L * (m + 1) = 2 * L * m + 2 * L := by ring
        omega
      · by_cases ha : a = 0
        · subst ha; rw [hstep_round_up]; simp; omega
        · rw [hstep_round_down V L m u a ha]; simp; omega
  | succ d =>
    refine ⟨?_, fun a => ?_⟩
    · rw [Fin.sum_univ_four, hstep_ghost_up, hstep_ghost_down V L n u d 1 h1,
        hstep_ghost_down V L n u d 2 h2, hstep_ghost_down V L n u d 3 h3]
      simp only [add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
      have hdL : d ≠ L := by omega
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · have : 2 * L * (n + 1) = 2 * L * n + 2 * L := by ring
        split_ifs with hL2 <;> simp only [T0] <;> omega
      · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hd
        simp only [zero_add, add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
        split_ifs with hL2 <;> simp only [T0] <;> omega
    · by_cases ha : a = 0
      · subst ha; rw [hstep_ghost_up]; split_ifs <;> simp <;> omega
      · rw [hstep_ghost_down V L n u d a ha]; split_ifs <;> simp <;> omega

/-- The uniform law on the four directions: a probability, and an integral is the mean of the four values. -/
theorem FrogModel.D3.lintegral_dirLaw :
    FrogModel.D3.dirLaw Set.univ = 1 ∧
      ∀ h : Fin 4 → ℝ≥0∞, ∫⁻ a, h a ∂FrogModel.D3.dirLaw = (∑ a : Fin 4, h a) / 4 := by
  constructor
  · -- dirLaw Set.univ = 1
    unfold FrogModel.D3.dirLaw
    rw [ProbabilityTheory.uniformOn_univ]
    have hcard : Measure.count (Set.univ : Set (Fin 4)) = (Fintype.card (Fin 4) : ENNReal) := by
      calc
        Measure.count (Set.univ : Set (Fin 4)) = ((Set.univ : Set (Fin 4)).encard : ENNReal) := by
          rw [Measure.count_apply MeasurableSet.univ]
        _ = (ENat.card (Fin 4) : ENNReal) := by simp
        _ = (Fintype.card (Fin 4) : ENNReal) := by simp
    rw [hcard]
    apply ENNReal.div_self
    · norm_num
    · norm_num
  · -- ∀ h, integral = mean
    intro h
    unfold FrogModel.D3.dirLaw
    rw [MeasureTheory.lintegral_fintype]
    have h_singleton (a : Fin 4) : (uniformOn Set.univ : Measure (Fin 4)) {a} = (1 : ℝ≥0∞) / 4 := by
      rw [ProbabilityTheory.uniformOn_univ]
      rw [Measure.count_singleton]
      have hcard : (Fintype.card (Fin 4) : ℝ≥0∞) = (4 : ℝ≥0∞) := by norm_num
      rw [hcard]
    have hsum : (∑ a : Fin 4, h a * ((uniformOn Set.univ : Measure (Fin 4)) {a})) =
               (∑ a : Fin 4, h a * ((1 : ℝ≥0∞) / 4)) := by
      refine Finset.sum_congr rfl (λ a ha => ?_)
      rw [h_singleton a]
    rw [hsum]
    rw [← Finset.sum_mul]
    rw [ENNReal.div_eq_inv_mul]
    simp
    rw [ENNReal.div_eq_inv_mul]
    rw [mul_comm]

/-- The directions of an i.i.d. stream of values are i.i.d. uniform. -/
theorem FrogModel.D3.map_dir_iid :
    (FrogModel.Engine.iidMeasure FrogModel.D3.valLaw).map (fun y (n : ℕ) => (y n).1.2) =
      FrogModel.Engine.iidMeasure FrogModel.D3.dirLaw := by
  unfold FrogModel.Engine.iidMeasure
  -- iidMeasure ν = Measure.infinitePi fun _ : ℕ => ν
  -- Use infinitePi_map_pi with f i = fun (x : Val) => x.1.2
  have h_meas : ∀ (i : ℕ), Measurable (fun (x : FrogModel.D3.Val) => x.1.2) := by
    intro i
    exact measurable_of_countable _
  -- Apply the lemma
  have h_pi := Measure.infinitePi_map_pi (μ := fun (_ : ℕ) => FrogModel.D3.valLaw)
    (f := fun (_ : ℕ) => (fun (x : FrogModel.D3.Val) => x.1.2))
    (hf := h_meas)
  -- h_pi : (infinitePi ...).map (fun x i => (fun x => x.1.2) i (x i)) = infinitePi (fun i => (valLaw).map (fun x => x.1.2))
  -- Simplify the left side
  simp at h_pi
  -- Now h_pi gives the equality we need, but with map_dir_valLaw applied
  rw [h_pi]
  -- RHS: infinitePi fun i => valLaw.map (fun x => x.1.2)
  have h_factor : FrogModel.D3.valLaw.map (fun (x : FrogModel.D3.Val) => x.1.2) = FrogModel.D3.dirLaw := by
    rw [FrogModel.D3.map_dir_valLaw, FrogModel.D3.dirLaw]
  simp [h_factor]

/-- **The run at height 0 projects to the chain on the directions.** At `p.m = 0`, one step of M1_L keeps
the shape and moves the projection `(pool size, ups, ghost depth)` by `hstep` on the direction read. -/
theorem FrogModel.D3.proj_upd (p : FrogModel.D3.Params) (hm : p.m = 0) (s : FrogModel.D3.St)
    (x : FrogModel.D3.Val) (hs : FrogModel.D3.Shape0 s) :
    FrogModel.D3.Shape0 (FrogModel.D3.upd p s x) ∧
      FrogModel.D3.proj0 (FrogModel.D3.upd p s x) = FrogModel.D3.hstep p.V p.L (FrogModel.D3.proj0 s) x.1.2 := by
  rcases hs with hs | ⟨f, hs, hv, hk, hg⟩
  · obtain ⟨st, marks, out⟩ := s
    simp only at hs
    subst hs
    exact ⟨Or.inl rfl, by simp [upd, proj0, hstep]⟩
  · obtain ⟨st, marks, out⟩ := s
    simp only at hs
    subst hs
    obtain ⟨v, isR, f0, pool, ups, ghost, killing⟩ := f
    simp only at hv hk hg
    subst hv hk
    rcases ghost with _ | ⟨φ, u⟩
    · rcases pool with _ | ⟨φ, ps⟩
      · refine ⟨Or.inr ⟨_, rfl, rfl, rfl, hg⟩, ?_⟩
        simp [upd, proj0, hstep]
      · by_cases hd : x.1.2 = 0
        · simp only [upd, hd, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
          by_cases hps : ps = []
          · subst hps
            refine ⟨by simp [settle, Shape0], ?_⟩
            simp [settle, proj0, hstep]
            split_ifs <;> simp
          · simp only [settle, hps, false_and, ↓reduceIte]
            refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simp⟩, ?_⟩
            simp only [proj0, List.length_cons, hstep]
            simp
            split_ifs <;> simp
        · simp only [upd, hd, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, List.length_nil, hm,
            true_or]
          refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simp⟩, ?_⟩
          simp [proj0, hstep, hd]
    · obtain ⟨c, u0, rfl⟩ := List.exists_cons_of_ne_nil (hg φ u rfl)
      have hlen : (proj0 ⟨[⟨[], isR, f0, pool, ups, some (φ, c :: u0), false⟩], marks, out⟩) =
          (pool.length, ups.length, u0.length + 1) := by simp [proj0]
      rw [hlen]
      simp only [upd, Bool.false_eq_true, ↓reduceIte, List.length_nil, zero_add]
      by_cases hd : x.1.2 = 0
      · have hgs : ghostStep (c :: u0) x.1 = u0 := by simp [ghostStep, hd]
        rw [hgs]
        by_cases h0 : u0 = []
        · subst h0
          refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simp⟩, ?_⟩
          simp [proj0, hstep, hd]
        · have h0' : u0.length ≠ 0 := by simpa using h0
          by_cases hL : u0.length = p.L
          · have hL0 : p.L ≠ 0 := by omega
            simp only [h0, ↓reduceIte, hL]
            by_cases hp : pool = []
            · subst hp
              refine ⟨by simp [settle, Shape0], ?_⟩
              simp [settle, proj0, hstep, hd, hL0]
            · simp only [settle, hp, ↓reduceIte, and_true]
              refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simp⟩, ?_⟩
              simp [proj0, hstep, hd, hL0]
          · simp only [h0, hL, ↓reduceIte]
            refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simpa using h0⟩, ?_⟩
            simp [proj0, hstep, hd, h0', hL]
      · have hgs : ghostStep (c :: u0) x.1 = x.1.2.pred hd :: c :: u0 := by
          simp [ghostStep, hd]
        rw [hgs]
        by_cases hL : u0.length + 2 = p.L
        · have hL' : (x.1.2.pred hd :: c :: u0).length = p.L := by simpa using hL
          have hL0 : p.L ≠ 0 := by omega
          simp only [List.cons_ne_nil, ↓reduceIte, hL']
          by_cases hp : pool = []
          · subst hp
            refine ⟨by simp [settle, Shape0], ?_⟩
            simp [settle, proj0, hstep, hd, hL, hL0]
          · simp only [settle, hp, ↓reduceIte, and_true]
            refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simp⟩, ?_⟩
            simp [proj0, hstep, hd, hL, hL0]
        · have hL' : (x.1.2.pred hd :: c :: u0).length ≠ p.L := by simpa using hL
          simp only [List.cons_ne_nil, ↓reduceIte, hL']
          refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simp⟩, ?_⟩
          simp [proj0, hstep, hd, hL]

namespace FrogModel.D3

instance : IsProbabilityMeasure dirLaw := ⟨lintegral_dirLaw.1⟩

instance : IsProbabilityMeasure (Engine.iidMeasure dirLaw) := by
  unfold Engine.iidMeasure; infer_instance

theorem measurableSet_fin4 (S : Set (Fin 4)) : MeasurableSet S := S.to_countable.measurableSet

theorem hstep_ended (V L u : ℕ) (a : Fin 4) : hstep V L (0, u, 0) a = (0, u, 0) := by
  simp [hstep]

theorem hstep_dir (V L : ℕ) (y : ℕ × ℕ × ℕ) (a : Fin 4) (ha : a ≠ 0) :
    hstep V L y a = hstep V L y 1 := by
  obtain ⟨n, u, d⟩ := y
  cases d <;> simp [hstep, ha]

theorem hstep_ups_le (V L : ℕ) (y : ℕ × ℕ × ℕ) (hy : y.2.1 ≤ V) (a : Fin 4) :
    (hstep V L y a).2.1 ≤ V := by
  obtain ⟨n, u, d⟩ := y
  simp only at hy
  cases d with
  | zero => simp only [hstep]; split_ifs <;> simp <;> omega
  | succ d => simp only [hstep]; split_ifs <;> simp [hy]

theorem traj_ended (V L u : ℕ) (w : ℕ → Fin 4) (t : ℕ) :
    Engine.traj (hstep V L) (0, u, 0) w t = (0, u, 0) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Engine.traj, ih, hstep_ended]

/-- Once at an end, the chain stays there. -/
theorem traj_stay (V L u : ℕ) (y : ℕ × ℕ × ℕ) (w : ℕ → Fin 4) (j t : ℕ)
    (hj : Engine.traj (hstep V L) y w j = (0, u, 0)) (ht : j ≤ t) :
    Engine.traj (hstep V L) y w t = (0, u, 0) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Engine.traj_add, hj, traj_ended]

theorem traj_ups_le (V L : ℕ) (y : ℕ × ℕ × ℕ) (hy : y.2.1 ≤ V) (w : ℕ → Fin 4) (t : ℕ) :
    (Engine.traj (hstep V L) y w t).2.1 ≤ V := by
  induction t with
  | zero => exact hy
  | succ t ih => exact hstep_ups_le V L _ ih _

theorem traj_depth_lt (V L : ℕ) (hL : 2 ≤ L) (y : ℕ × ℕ × ℕ) (hy : y.2.2 < L) (w : ℕ → Fin 4)
    (t : ℕ) : (Engine.traj (hstep V L) y w t).2.2 < L := by
  induction t with
  | zero => exact hy
  | succ t ih => exact (T0_drift V L hL _ ih).2 _

theorem measurableSet_hstep (V L : ℕ) (x y : ℕ × ℕ × ℕ) :
    MeasurableSet {a : Fin 4 | hstep V L x a = y} := measurableSet_fin4 _

theorem measurableSet_reach (V L : ℕ) (y z : ℕ × ℕ × ℕ) :
    MeasurableSet {w : ℕ → Fin 4 | ∃ t, Engine.traj (hstep V L) y w t = z} := by
  have : {w : ℕ → Fin 4 | ∃ t, Engine.traj (hstep V L) y w t = z} =
      ⋃ t, {w | Engine.traj (hstep V L) y w t = z} := by ext; simp
  rw [this]
  exact MeasurableSet.iUnion fun t => measurableSet_traj_eq _ (measurableSet_hstep V L) y t z


/-- The first-step equation of `U0` at every state that is not an end. -/
theorem U0_step (V L b : ℕ) (hL : 2 ≤ L) (z : ℕ × ℕ × ℕ) (hd : z.2.2 < L) (hu : z.2.1 ≤ V)
    (hne : ¬(z.1 = 0 ∧ z.2.2 = 0)) :
    U0 V L b z = 1 / 4 * U0 V L b (hstep V L z 0) + 3 / 4 * U0 V L b (hstep V L z 1) := by
  obtain ⟨n, u, d⟩ := z
  simp only at hd hu hne
  cases d with
  | zero => exact U0_round V L b n u hL hu (by omega)
  | succ d => exact U0_ghost V L b n u d hL hd
theorem qL_mem (L : ℕ) (hL : 2 ≤ L) : 0 ≤ qL L ∧ qL L ≤ 1 := by
  obtain ⟨-, -, -, -, h0, h1, -⟩ := pL_qL_facts L hL
  exact ⟨h0.le, by linarith⟩

theorem lintegral_ofReal_U0 (V L b : ℕ) (hL : 2 ≤ L) (z : ℕ × ℕ × ℕ) (hd : z.2.2 < L)
    (hu : z.2.1 ≤ V) (hne : ¬(z.1 = 0 ∧ z.2.2 = 0)) :
    ∫⁻ a, ENNReal.ofReal (U0 V L b (hstep V L z a)) ∂dirLaw = ENNReal.ofReal (U0 V L b z) := by
  have hnn : ∀ y, 0 ≤ U0 V L b y := fun y => (U0_nonneg_sum V L hL y).1 b
  rw [lintegral_dirLaw.2, Fin.sum_univ_four, hstep_dir V L z 2 (by decide),
    hstep_dir V L z 3 (by decide), U0_step V L b hL z hd hu hne,
    ← ENNReal.ofReal_add (hnn _) (hnn _), ← ENNReal.ofReal_add (add_nonneg (hnn _) (hnn _)) (hnn _),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hnn _) (hnn _)) (hnn _)) (hnn _)]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  ring

/-- The time bound in the form of `chain_law`. -/
theorem T0_super (V L : ℕ) (hL : 2 ≤ L) (z : ℕ × ℕ × ℕ) (hd : z.2.2 < L) :
    {y : ℕ × ℕ × ℕ | y.1 = 0 ∧ y.2.2 = 0}.indicator 0 z +
        {y : ℕ × ℕ × ℕ | y.1 = 0 ∧ y.2.2 = 0}ᶜ.indicator 1 z +
        ∫⁻ a, (T0 L (hstep V L z a) : ℝ≥0∞) ∂dirLaw ≤ (T0 L z : ℝ≥0∞) := by
  obtain ⟨hdr, -⟩ := T0_drift V L hL z hd
  rw [lintegral_dirLaw.2]
  set i : ℕ := if z.1 = 0 ∧ z.2.2 = 0 then 0 else 1 with hi
  have hind : {y : ℕ × ℕ × ℕ | y.1 = 0 ∧ y.2.2 = 0}.indicator 0 z +
      {y : ℕ × ℕ × ℕ | y.1 = 0 ∧ y.2.2 = 0}ᶜ.indicator 1 z = (i : ℝ≥0∞) := by
    by_cases he : z.1 = 0 ∧ z.2.2 = 0 <;> simp [Set.indicator, he, hi]
  rw [hind]
  have hcast : ((4 * i + ∑ a : Fin 4, T0 L (hstep V L z a) : ℕ) : ℝ≥0∞) ≤
      ((4 * T0 L z : ℕ) : ℝ≥0∞) := by exact_mod_cast hdr
  push_cast at hcast
  rw [ENNReal.div_eq_inv_mul]
  calc (i : ℝ≥0∞) + 4⁻¹ * ∑ a, (T0 L (hstep V L z a) : ℝ≥0∞)
      = 4⁻¹ * (4 * i + ∑ a, (T0 L (hstep V L z a) : ℝ≥0∞)) := by
        rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 4⁻¹ * (4 * (T0 L z : ℝ≥0∞)) := by gcongr
    _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- **The law at height 0, on the stream of directions**, an instance of `chain_law`. From a reachable
state that is not an end, the chain ends with `b` ups with probability `U0 V L b`. -/
theorem law_height0 (V L : ℕ) (hL : 2 ≤ L) (y : ℕ × ℕ × ℕ) (hd : y.2.2 < L) (hu : y.2.1 ≤ V)
    (hne : ¬(y.1 = 0 ∧ y.2.2 = 0)) (b : ℕ) :
    Engine.iidMeasure dirLaw {w | ∃ t, Engine.traj (hstep V L) y w t = (0, b, 0)} =
      ENNReal.ofReal (U0 V L b y) := by
  set E := {y : ℕ × ℕ × ℕ | y.1 = 0 ∧ y.2.2 = 0}
  set G := {y : ℕ × ℕ × ℕ | y.2.2 < L ∧ y.2.1 ≤ V}
  have hnn : ∀ b z, 0 ≤ U0 V L b z := fun b z => (U0_nonneg_sum V L hL z).1 b
  have hset : {w | ∃ t, Engine.traj (hstep V L) y w t = (0, b, 0)} =
      {w | ∃ t, Engine.traj (hstep V L) y w t ∈ E ∧ (Engine.traj (hstep V L) y w t).2.1 = b} := by
    ext w
    refine exists_congr fun t => ?_
    constructor
    · intro h
      simp [E, h]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      ext <;> simp [h1, h2, h3]
  by_cases hbV : V < b
  · have hempty : {w | ∃ t, Engine.traj (hstep V L) y w t = (0, b, 0)} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro t ht
      have := traj_ups_le V L y hu w t
      rw [ht] at this
      simp at this
      omega
    rw [hempty, (U0_nonneg_sum V L hL y).2.1 b hbV]
    simp
  rw [hset]
  refine chain_law (hstep V L) dirLaw (measurableSet_hstep V L) E ?_ (fun z => z.2.1)
    (Finset.range (V + 1)) G ?_ ?_ (fun b z => ENNReal.ofReal (U0 V L b z)) ?_ ?_ ?_
    (fun z => (T0 L z : ℝ≥0∞)) ?_ (fun _ _ => by simp) y ⟨hd, hu⟩ hne b
    (Finset.mem_range.2 (by omega))
  · rintro ⟨n, u, d⟩ ⟨h1, h2⟩ ξ
    simp only at h1 h2
    subst h1 h2
    exact hstep_ended V L u ξ
  · rintro z ⟨hz1, hz2⟩ ξ
    exact ⟨(T0_drift V L hL z hz1).2 ξ, hstep_ups_le V L z hz2 ξ⟩
  · rintro z ⟨-, hz⟩ -
    simp only [Finset.mem_range]
    omega
  · rintro c ⟨n, u, d⟩ ⟨-, hu'⟩ ⟨h1, h2⟩
    simp only at h1 h2 hu'
    subst h1 h2
    have hc := (capBin_basic V (qL L) (qL_mem L hL).1 (qL_mem L hL).2).2.2 u c hu'
    simp only [U0, hc]
    split_ifs <;> simp
  · rintro c z ⟨hz1, hz2⟩ hzE
    exact (lintegral_ofReal_U0 V L c hL z hz1 hz2 hzE).le
  · rintro z -
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hnn c z), (U0_nonneg_sum V L hL z).2.2]
    simp
  · rintro z ⟨hz1, -⟩
    exact T0_super V L hL z hz1

/-- The run at `p.m = 0` never stalls: a frame left has a frog in its pool or on a ghost walk. -/
def Live0 (s : St) : Prop := ∀ f, s.stack = [f] → f.pool ≠ [] ∨ f.ghost ≠ none

theorem live_upd (p : Params) (hm : p.m = 0) (s : St) (x : Val) (hs : Shape0 s) (hl : Live0 s) :
    Live0 (upd p s x) := by
  rcases hs with hs | ⟨f, hs, hv, hk, hg⟩
  · obtain ⟨st, marks, out⟩ := s
    simp only at hs
    subst hs
    intro f' hf'
    simp [upd] at hf'
  · obtain ⟨st, marks, out⟩ := s
    simp only at hs
    subst hs
    obtain ⟨v, isR, f0, pool, ups, ghost, killing⟩ := f
    simp only at hv hk hg
    subst hv hk
    have hl' := hl _ rfl
    intro f' hf'
    rcases ghost with _ | ⟨φ, u⟩
    · rcases pool with _ | ⟨φ, ps⟩
      · simp at hl'
      · by_cases hd : x.1.2 = 0
        · simp only [upd, hd, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte] at hf'
          by_cases hps : ps = []
          · subst hps
            simp [settle] at hf'
          · simp only [settle, hps, ↓reduceIte, List.cons.injEq, and_true] at hf'
            subst hf'
            exact Or.inl hps
        · simp only [upd, hd, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, List.length_nil, hm,
            true_or, List.cons.injEq, and_true] at hf'
          subst hf'
          simp
    · obtain ⟨c, u0, rfl⟩ := List.exists_cons_of_ne_nil (hg φ u rfl)
      simp only [upd, Bool.false_eq_true, ↓reduceIte, List.length_nil, zero_add] at hf'
      split_ifs at hf' with h0 hL
      · simp only [List.cons.injEq, and_true] at hf'
        subst hf'
        simp
      · by_cases hps : pool = []
        · subst hps
          simp [settle] at hf'
        · simp only [settle, hps, ↓reduceIte, List.cons.injEq, and_true] at hf'
          subst hf'
          exact Or.inl hps
      · simp only [List.cons.injEq, and_true] at hf'
        subst hf'
        simp

theorem shape_live_init (k : ℕ) : Shape0 (init k) ∧ Live0 (init k) := by
  refine ⟨Or.inr ⟨_, rfl, rfl, rfl, by simp⟩, ?_⟩
  intro f hf
  simp only [init, List.cons.injEq, and_true] at hf
  subst hf
  simp

/-- **The run at height 0 is the chain `hstep` on the directions read.** -/
theorem proj_run (p : Params) (hm : p.m = 0) (k : ℕ) (y : ℕ → Val) (n : ℕ) :
    Shape0 (run p k y n) ∧ Live0 (run p k y n) ∧
      proj0 (run p k y n) = Engine.traj (hstep p.V p.L) (k + 1, 0, 0) (fun t => (y t).1.2) n := by
  induction n with
  | zero =>
    obtain ⟨h1, h2⟩ := shape_live_init k
    exact ⟨h1, h2, by simp [run, Engine.traj, proj0, init]⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have h := proj_upd p hm _ (y n) h1
    refine ⟨h.1, live_upd p hm _ _ h1 h2, ?_⟩
    change proj0 (upd p (run p k y n) (y n)) =
      hstep p.V p.L (Engine.traj (hstep p.V p.L) (k + 1, 0, 0) (fun t => (y t).1.2) n) (y n).1.2
    rw [h.2, h3]

/-- On the reachable states, the end with `b` ups is the projected end `(0, b, 0)`. -/
theorem end_iff_proj (s : St) (hs : Shape0 s) (hl : Live0 s) (b : ℕ) :
    (s.stack = [] ∧ count s = b) ↔ proj0 s = (0, b, 0) := by
  obtain ⟨st, marks, out⟩ := s
  rcases hs with hs | ⟨f, hs, -, -, hg⟩
  · simp only at hs
    subst hs
    simp [proj0, count]
  · simp only at hs
    subst hs
    have hl' := hl f rfl
    simp only [List.cons_ne_nil, false_and, false_iff, proj0]
    intro h
    simp only [Prod.mk.injEq, List.length_eq_zero_iff] at h
    obtain ⟨hp, -, hd⟩ := h
    rcases hgh : f.ghost with _ | ⟨φ, u⟩
    · exact hl'.elim (fun h => h hp) (fun h => h hgh)
    · rw [hgh] at hd
      exact hg φ u hgh (List.length_eq_zero_iff.1 hd)

/-- **The law of the run at `m = 0`, on the frog paths.** With `k` entrants, the run of M1_L on
the frog paths ends with `b` ups with probability `capBin V q_L (k + 1) 0 b`, the law of
`min (Bin(k + 1, q_L), V)`. -/
theorem top_law_zero (p : Params) (hm : p.m = 0) (hL : 2 ≤ p.L) (k b : ℕ) :
    fpMeasure {ω | ∃ n, (run p k (Pool.poolSeq (sel p k) ω) n).stack = [] ∧
        count (run p k (Pool.poolSeq (sel p k) ω) n) = b} =
      ENNReal.ofReal (capBin p.V (qL p.L) (k + 1) 0 b) := by
  set dirs : (ℕ → Val) → (ℕ → Fin 4) := fun y t => (y t).1.2 with hdirs
  set T := {w : ℕ → Fin 4 | ∃ t, Engine.traj (hstep p.V p.L) (k + 1, 0, 0) w t = (0, b, 0)}
    with hT
  have hS : {y : ℕ → Val | ∃ n, (run p k y n).stack = [] ∧ count (run p k y n) = b} =
      dirs ⁻¹' T := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hT, hdirs]
    refine exists_congr fun n => ?_
    obtain ⟨h1, h2, h3⟩ := proj_run p hm k y n
    rw [end_iff_proj _ h1 h2, h3]
  have hTm : MeasurableSet T := measurableSet_reach p.V p.L _ _
  have hdm : Measurable dirs :=
    measurable_pi_iff.2 fun t => (measurable_of_countable (fun x : Val => x.1.2)).comp
      (measurable_pi_apply t)
  have hpm := (Pool.measurable_poolSeq (sel p k) (measurableSet_sel p k)).1
  have hev : {ω | ∃ n, (run p k (Pool.poolSeq (sel p k) ω) n).stack = [] ∧
      count (run p k (Pool.poolSeq (sel p k) ω) n) = b} =
      Pool.poolSeq (sel p k) ⁻¹' (dirs ⁻¹' T) := by
    rw [← hS]
    rfl
  rw [hev, ← Measure.map_apply hpm (hdm hTm), map_fp_read, ← Measure.map_apply hdm hTm, hdirs,
    map_dir_iid, hT, law_height0 p.V p.L hL (k + 1, 0, 0) (by simp; omega) (by simp)
      (by simp) b]
  rfl

end FrogModel.D3
