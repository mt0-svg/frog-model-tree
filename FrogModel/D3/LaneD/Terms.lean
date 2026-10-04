module

public import FrogModel.D3.Interfaces.Step
public import FrogModel.D3.LaneD.Pack

@[expose] public section

/-!
# The terms of a step in integers

Each term of `Phi^S` (and of the extension and the seed) that a checker evaluates in integers, against
its real value: the ratios `r'(k', j)` and the term `T` (`ratio_eq`, `T_bound`), the binomial sums
(`binSum_eq`, `binLt4_eq`, `binCdfN_eq`, and `binGe`, `binLt`, `binCdf` at `1/2`, `1/4`, `1/3`), the
deficit terms `L` (`L_arith`, `B_val`) and `S2` (`S2_arith`, `Dt_eq`, `runmin_fold`), and the cdf
terms `L` (`lemma12B_check`, the square root witness) and `A` (`A_arith`). `cdiv a b` is the ceiling
of `a / b` (`cdiv_spec`).
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K

theorem ratio_eq (a b k j : ℕ) : ratio a b k j = (ratioN a b k j : ℝ) / ratioD a b j := by
  unfold ratio mu
  simp only [Nat.cast_add, Nat.cast_one]
  have hleft1 : ((a : ℝ) + 1 + (k : ℝ)) / 3 / (((a : ℝ) + 1 + 1 + (j : ℝ)) / 3) =
      ((a : ℝ) + 1 + (k : ℝ)) / ((a : ℝ) + 2 + (j : ℝ)) := by
    field_simp [show (3 : ℝ) ≠ 0 from by norm_num, show (a : ℝ) + 2 + (j : ℝ) ≠ 0 from by positivity]
    ring
  have hleft2 : ((b : ℝ) + 1 + (k : ℝ)) / 3 / (((b : ℝ) + 1 + 1 + (j : ℝ)) / 3) =
      ((b : ℝ) + 1 + (k : ℝ)) / ((b : ℝ) + 2 + (j : ℝ)) := by
    field_simp [show (3 : ℝ) ≠ 0 from by norm_num, show (b : ℝ) + 2 + (j : ℝ) ≠ 0 from by positivity]
    ring
  rw [hleft1, hleft2]
  unfold ratioN ratioD
  have hmaxN : ∀ (p q : ℕ), (maxN p q : ℝ) = max (p : ℝ) (q : ℝ) := by
    intro p q
    by_cases h : p ≤ q
    · have hmaxN_eq : maxN p q = q := by
        dsimp [maxN]
        rw [Nat.sub_eq_zero_of_le h, add_zero]
      rw [hmaxN_eq]
      simp [h]
    · have hq_le_p : q ≤ p := by omega
      have hmaxN_eq : maxN p q = p := by
        dsimp [maxN]
        rw [Nat.add_comm, Nat.sub_add_cancel hq_le_p]
      rw [hmaxN_eq]
      simp [hq_le_p]
  rw [hmaxN]
  simp [Nat.cast_add, Nat.cast_mul]
  set x := (a : ℝ) + 1 + (k : ℝ) with hx
  set y := (b : ℝ) + 1 + (k : ℝ) with hy
  set A := (a : ℝ) + 2 + (j : ℝ) with hAdef
  set B := (b : ℝ) + 2 + (j : ℝ) with hBdef
  have hApos : A > 0 := by
    dsimp [A]
    positivity
  have hBpos : B > 0 := by
    dsimp [B]
    positivity
  have hgoal : max (x / A) (y / B) = max (x * B) (y * A) / (A * B) := by
    by_cases h : x / A ≥ y / B
    · have h' : x * B ≥ y * A := by
        calc
          x * B = (x / A) * (A * B) := by field_simp [hApos.ne']
          _ ≥ (y / B) * (A * B) := mul_le_mul_of_nonneg_right h (by positivity)
          _ = y * A := by field_simp [hBpos.ne']
      have hmax1 : max (x / A) (y / B) = x / A := max_eq_left h
      have hmax2 : max (x * B) (y * A) = x * B := max_eq_left h'
      calc
        max (x / A) (y / B) = x / A := hmax1
        _ = (x * B) / (A * B) := by field_simp [hApos.ne', hBpos.ne']
        _ = max (x * B) (y * A) / (A * B) := by rw [hmax2]
    · have hlt : y / B > x / A := by linarith
      have h' : y * A ≥ x * B := by
        calc
          y * A = (y / B) * (A * B) := by field_simp [hBpos.ne']
          _ ≥ (x / A) * (A * B) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = x * B := by field_simp [hApos.ne']
      have hmax1 : max (x / A) (y / B) = y / B := max_eq_right (by linarith)
      have hmax2 : max (x * B) (y * A) = y * A := max_eq_right h'
      calc
        max (x / A) (y / B) = y / B := hmax1
        _ = (y * A) / (A * B) := by field_simp [hApos.ne', hBpos.ne']
        _ = max (x * B) (y * A) / (A * B) := by rw [hmax2]
  simpa [x, y, A, B] using hgoal

theorem cdiv_spec (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  set q := cdiv a b with hq
  have hdiv := Nat.div_add_mod (a + b - 1) b
  have hmod_lt : (a + b - 1) % b < b := Nat.mod_lt (a + b - 1) hb
  have hpos : 1 ≤ a + b := by
    have hb1 : 1 ≤ b := Nat.one_le_of_lt hb
    exact Nat.le_trans hb1 (Nat.le_add_left b a)
  have hq_eq : ((a + b - 1) / b) = q := rfl
  have h_eq : a + b = q * b + ((a + b - 1) % b) + 1 := by
    calc
      a + b = ((a + b) - 1) + 1 := by rw [Nat.sub_add_cancel hpos]
      _ = (b * ((a + b - 1) / b) + (a + b - 1) % b) + 1 := by rw [hdiv]
      _ = (b * q + (a + b - 1) % b) + 1 := by rw [hq_eq]
      _ = (q * b + (a + b - 1) % b) + 1 := by rw [mul_comm]
      _ = q * b + ((a + b - 1) % b) + 1 := rfl
  have hmod' : (a + b - 1) % b + 1 ≤ b := Nat.succ_le_of_lt hmod_lt
  have h_ineq' : a + b ≤ q * b + b := by
    rw [h_eq]
    have : q * b + ((a + b - 1) % b) + 1 = q * b + (((a + b - 1) % b) + 1) := by
      ring
    rw [this]
    exact Nat.add_le_add_left hmod' (q * b)
  have hineq : a ≤ q * b := Nat.le_of_add_le_add_right h_ineq'
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hineq' : (a : ℝ) ≤ (q : ℝ) * (b : ℝ) := by exact_mod_cast hineq
  rw [div_le_iff₀ hbpos]
  simpa [hq] using hineq'

theorem T_bound (a b j : ℕ) : ratio a b 0 j ≤ (cdiv (Nat.shiftLeft (ratioN a b 0 j) 128) (ratioD a b j) : ℝ) / 2 ^ 128 := by
  have hratio_eq : ratio a b 0 j = (ratioN a b 0 j : ℝ) / ratioD a b j := ratio_eq a b 0 j
  rw [hratio_eq]
  have hpos : 0 < ratioD a b j := by
    unfold ratioD
    have ha : 0 < a + 2 + j := by omega
    have hb : 0 < b + 2 + j := by omega
    exact mul_pos ha hb
  have hdiv_eq : (ratioN a b 0 j : ℝ) / (ratioD a b j : ℝ) = ((ratioN a b 0 j : ℝ) * (2 ^ 128 : ℝ)) / (ratioD a b j : ℝ) / (2 ^ 128 : ℝ) := by
    calc
      (ratioN a b 0 j : ℝ) / (ratioD a b j : ℝ)
          = ((ratioN a b 0 j : ℝ) / (ratioD a b j : ℝ)) * 1 := by ring
      _ = ((ratioN a b 0 j : ℝ) / (ratioD a b j : ℝ)) * ((2 ^ 128 : ℝ) / (2 ^ 128 : ℝ)) := by
        rw [div_self (show (2 ^ 128 : ℝ) ≠ 0 from by norm_num)]
      _ = ((ratioN a b 0 j : ℝ) * (2 ^ 128 : ℝ)) / ((ratioD a b j : ℝ) * (2 ^ 128 : ℝ)) := by ring
      _ = ((ratioN a b 0 j : ℝ) * (2 ^ 128 : ℝ)) / (ratioD a b j : ℝ) / (2 ^ 128 : ℝ) := by ring
  have hcdiv : ((ratioN a b 0 j : ℝ) * (2 ^ 128 : ℝ)) / (ratioD a b j : ℝ) ≤ (cdiv (Nat.shiftLeft (ratioN a b 0 j) 128) (ratioD a b j) : ℝ) := by
    have h := cdiv_spec (Nat.shiftLeft (ratioN a b 0 j) 128) (ratioD a b j) hpos
    have hshift' : (Nat.shiftLeft (ratioN a b 0 j) 128 : ℝ) = (ratioN a b 0 j : ℝ) * (2 ^ 128 : ℝ) := by
      exact_mod_cast Nat.shiftLeft_eq (ratioN a b 0 j) 128
    rw [hshift'] at h
    exact h
  calc
    (ratioN a b 0 j : ℝ) / (ratioD a b j : ℝ) = ((ratioN a b 0 j : ℝ) * (2 ^ 128 : ℝ)) / (ratioD a b j : ℝ) / (2 ^ 128 : ℝ) := hdiv_eq
    _ ≤ (cdiv (Nat.shiftLeft (ratioN a b 0 j) 128) (ratioD a b j) : ℝ) / (2 ^ 128 : ℝ) := by
      exact div_le_div_of_nonneg_right hcdiv (by norm_num : 0 ≤ (2 ^ 128 : ℝ))

theorem binSum_eq (n v : ℕ) : binSum n v = ∑ u ∈ Finset.range (v + 1), n.choose u := by
  have hpos : ∀ m : ℕ, 0 < m + 1 := fun m => Nat.succ_pos m
  have inv : ∀ m : ℕ, natFold m (0, 1) (fun u (st : ℕ × ℕ) =>
      (st.1 + st.2, st.2 * (n - u) / (u + 1))) =
      (∑ u ∈ Finset.range m, n.choose u, n.choose m) := by
    intro m
    induction' m with m ih
    · simp [natFold]
    · have : natFold (m + 1) (0, 1) (fun u (st : ℕ × ℕ) =>
        (st.1 + st.2, st.2 * (n - u) / (u + 1))) =
        (fun u (st : ℕ × ℕ) => (st.1 + st.2, st.2 * (n - u) / (u + 1))) m
        (natFold m (0, 1) (fun u (st : ℕ × ℕ) => (st.1 + st.2, st.2 * (n - u) / (u + 1)))) := by
        rfl
      rw [this, ih]
      simp
      have h := Nat.choose_succ_right_eq n m
      have hdiv : n.choose m * (n - m) / (m + 1) = n.choose (m + 1) := by
        calc
          n.choose m * (n - m) / (m + 1) = (n.choose (m + 1) * (m + 1)) / (m + 1) := by
            rw [← h]
          _ = n.choose (m + 1) := by
            rw [Nat.mul_div_cancel _ (hpos m)]
      rw [hdiv]
      simp [Finset.sum_range_succ]
  have h := inv (v + 1)
  calc
    binSum n v = (natFold (v + 1) (0, 1) (fun u (st : ℕ × ℕ) =>
      (st.1 + st.2, st.2 * (n - u) / (u + 1)))).1 := rfl
    _ = (∑ u ∈ Finset.range (v + 1), n.choose u, n.choose (v + 1)).1 := by rw [h]
    _ = ∑ u ∈ Finset.range (v + 1), n.choose u := by simp

theorem binLt4_eq (K J : ℕ) : binLt4 K J = ∑ i ∈ Finset.range J, K.choose i * 3 ^ (K - i) := by
  set f : ℕ → ℕ × ℕ → ℕ × ℕ := fun i (st : ℕ × ℕ) =>
    (Nat.add st.1 (Nat.mul st.2 (Nat.pow 3 (Nat.sub K i))),
     Nat.div (Nat.mul st.2 (Nat.sub K i)) (Nat.add i 1))
  have hzero : natFold 0 (0, 1) f = (0, 1) := rfl
  have hsucc (n : ℕ) : natFold (n + 1) (0, 1) f = f n (natFold n (0, 1) f) := rfl
  have h : ∀ m : ℕ, natFold m (0, 1) f = (∑ i ∈ Finset.range m, K.choose i * 3 ^ (K - i), K.choose m) := by
    intro m
    induction' m with m ih
    · rw [hzero]
      simp
    · rw [hsucc m, ih]
      simp [f, Finset.sum_range_succ]
      have hpos : 0 < m + 1 := Nat.zero_lt_succ m
      have heq := Nat.choose_succ_right_eq K m
      have hdiv : Nat.div (Nat.mul (K.choose m) (K - m)) (m + 1) = K.choose (m + 1) := by
        apply Nat.div_eq_of_eq_mul_right hpos
        -- goal: K.choose m * (K - m) = (m + 1) * K.choose (m + 1)
        -- heq: K.choose (m+1) * (m+1) = K.choose m * (K-m)
        -- heq.symm: K.choose m * (K-m) = K.choose (m+1) * (m+1)
        simpa [mul_comm] using heq.symm
      simpa using hdiv
  rw [binLt4, h J]

theorem binCdfN_aux (n v b : ℕ) :
    (natFold (v+1) (0, 1) (fun i (st : ℕ × ℕ) =>
      (st.1 + st.2 * b ^ (n - i), Nat.div (st.2 * (n - i)) (i + 1)))) =
    (∑ i ∈ Finset.range (v+1), n.choose i * b ^ (n - i), n.choose (v+1)) := by
  induction' v with v ih
  · simp [natFold]
  · have h_choose : n.choose (v+1) * (n - (v+1)) / (v+2) = n.choose (v+2) := by
      have h := Nat.choose_succ_right_eq n (v+1)
      have hpos : 0 < v+2 := by omega
      rw [← h, Nat.mul_div_cancel _ hpos]
    have h_step : natFold ((v+1)+1) (0, 1) (fun i (st : ℕ × ℕ) =>
      (st.1 + st.2 * b ^ (n - i), Nat.div (st.2 * (n - i)) (i + 1))) =
      (fun i (st : ℕ × ℕ) => (st.1 + st.2 * b ^ (n - i), Nat.div (st.2 * (n - i)) (i + 1)))
        (v+1) (natFold (v+1) (0, 1) (fun i (st : ℕ × ℕ) =>
          (st.1 + st.2 * b ^ (n - i), Nat.div (st.2 * (n - i)) (i + 1)))) := by
      simp [natFold]
    rw [h_step, ih]
    simp
    constructor
    · simp [Finset.sum_range_succ]
    · have h_add : (v:ℕ)+1+1 = v+2 := by omega
      rw [h_add]
      exact h_choose

theorem binCdfN_eq (n v b : ℕ) : binCdfN n v b = ∑ i ∈ Finset.range (v + 1), n.choose i * b ^ (n - i) := by
  unfold binCdfN
  have h := binCdfN_aux n v b
  exact congrArg (fun p : ℕ × ℕ => p.1) h

theorem binGe_pow_aux (i n : ℕ) (hi : i ≤ n) : ((2 : ℝ) ^ i)⁻¹ * (((2 : ℝ)⁻¹) ^ (n - i)) = ((2 : ℝ) ^ n)⁻¹ := by
  calc
    ((2 : ℝ) ^ i)⁻¹ * (((2 : ℝ)⁻¹) ^ (n - i)) = ((2 : ℝ) ^ i)⁻¹ * (((2 : ℝ) ^ (n - i))⁻¹) := by
      simp [inv_pow]
    _ = ((2 : ℝ) ^ i * (2 : ℝ) ^ (n - i))⁻¹ := by rw [mul_inv]
    _ = ((2 : ℝ) ^ (i + (n - i)))⁻¹ := by rw [pow_add]
    _ = ((2 : ℝ) ^ n)⁻¹ := by
      rw [add_comm, Nat.sub_add_cancel hi]

theorem binGe_half (n E : ℕ) (h : E ≤ n) : binGe n (1 / 2) E = (binSum n (n - E) : ℝ) / 2 ^ n := by
  simp [binGe, binPmf]
  have h_sub : (1 : ℝ) - (2⁻¹ : ℝ) = (2⁻¹ : ℝ) := by norm_num
  rw [h_sub]
  have h_sum_eq : (∑ i ∈ Finset.Icc E n, (↑(n.choose i) : ℝ) * ((2 : ℝ) ^ i)⁻¹ * (((2 : ℝ)⁻¹) ^ (n - i))) =
                  (∑ i ∈ Finset.Icc E n, (↑(n.choose i) : ℝ) * ((2 : ℝ) ^ n)⁻¹) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_le_n : i ≤ n := (Finset.mem_Icc.mp hi).2
    have h_simp : ((2 : ℝ) ^ i)⁻¹ * (((2 : ℝ)⁻¹) ^ (n - i)) = ((2 : ℝ) ^ n)⁻¹ :=
      binGe_pow_aux i n hi_le_n
    calc
      (↑(n.choose i) : ℝ) * ((2 : ℝ) ^ i)⁻¹ * (((2 : ℝ)⁻¹) ^ (n - i)) =
          (↑(n.choose i) : ℝ) * (((2 : ℝ) ^ i)⁻¹ * (((2 : ℝ)⁻¹) ^ (n - i))) := by ring
      _ = (↑(n.choose i) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rw [h_simp]
  rw [h_sum_eq]
  rw [← Finset.sum_mul]
  rw [div_eq_mul_inv]
  field_simp [show (2 : ℝ) ^ n ≠ 0 from by positivity]
  have h_reindex : (∑ i ∈ Finset.Icc E n, (n.choose i : ℝ)) =
                   (∑ u ∈ Finset.range ((n - E) + 1), (n.choose u : ℝ)) := by
    refine Finset.sum_nbij' (fun a => n - a) (fun b => n - b) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha_le_n : a ≤ n := (Finset.mem_Icc.mp ha).2
      have ha_ge_E : E ≤ a := (Finset.mem_Icc.mp ha).1
      apply Finset.mem_range.mpr
      have : n - a ≤ n - E := Nat.sub_le_sub_left ha_ge_E n
      omega
    · intro b hb
      rw [Finset.mem_range] at hb
      have hb_le : b ≤ n - E := by omega
      have h_le_n : n - b ≤ n := Nat.sub_le _ _
      have h_ge_E : E ≤ n - b := by
        omega
      exact Finset.mem_Icc.mpr ⟨h_ge_E, h_le_n⟩
    · intro a ha
      have ha_le_n : a ≤ n := (Finset.mem_Icc.mp ha).2
      omega
    · intro b hb
      rw [Finset.mem_range] at hb
      have hb_le_n : b ≤ n := by omega
      omega
    · intro a ha
      have ha_le_n : a ≤ n := (Finset.mem_Icc.mp ha).2
      rw [Nat.choose_symm ha_le_n]
  rw [h_reindex]
  rw [← Nat.cast_sum, binSum_eq n (n - E)]

theorem binLt_quarter (K J : ℕ) : binLt K (1 / 4) J = (binLt4 K J : ℝ) / 4 ^ K := by
  rw [binLt, binLt4_eq K J]
  simp_rw [binPmf]
  have hsub : (1 : ℝ) - (1 : ℝ) / 4 = (3 : ℝ) / 4 := by ring
  rw [hsub]
  have hterm (i : ℕ) : ((K.choose i : ℝ) * ((1 : ℝ) / 4) ^ i * ((3 : ℝ) / 4) ^ (K - i)) =
      ((K.choose i : ℝ) * ((3 : ℝ) ^ (K - i))) / ((4 : ℝ) ^ K) := by
    by_cases h : i ≤ K
    · have h_exp : i + (K - i) = K := Nat.add_sub_cancel' h
      calc
        ((K.choose i : ℝ) * ((1 : ℝ) / 4) ^ i * ((3 : ℝ) / 4) ^ (K - i))
            = (K.choose i : ℝ) * (((1 : ℝ) / 4) ^ i * ((3 : ℝ) / 4) ^ (K - i)) := by ring
        _ = (K.choose i : ℝ) * (((1 : ℝ) ^ i / (4 : ℝ) ^ i) * ((3 : ℝ) ^ (K - i) / (4 : ℝ) ^ (K - i))) := by simp [div_pow]
        _ = (K.choose i : ℝ) * (((1 : ℝ) ^ i * (3 : ℝ) ^ (K - i)) / ((4 : ℝ) ^ i * (4 : ℝ) ^ (K - i))) := by ring
        _ = (K.choose i : ℝ) * (((3 : ℝ) ^ (K - i)) / ((4 : ℝ) ^ (i + (K - i)))) := by
          simp [pow_add]
        _ = (K.choose i : ℝ) * (((3 : ℝ) ^ (K - i)) / ((4 : ℝ) ^ K)) := by rw [h_exp]
        _ = ((K.choose i : ℝ) * ((3 : ℝ) ^ (K - i))) / ((4 : ℝ) ^ K) := by ring
    · have h_choose : (K.choose i : ℝ) = 0 := by
        rw [Nat.cast_eq_zero, Nat.choose_eq_zero_of_lt (not_le.mp h)]
      simp [h_choose]
  simp_rw [hterm]
  rw [← Finset.sum_div]
  simp [Nat.cast_sum, Nat.cast_mul]

theorem binCdf_third (n v : ℕ) : binCdf n (1 / 3) v = (binCdfN n v 2 : ℝ) / 3 ^ n := by
  have h_pow_eq (i : ℕ) (hle : i ≤ n) : ((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i) = ((2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n) := by
    have h_add : (i : ℕ) + (n - i) = n := Nat.add_sub_cancel' hle
    calc
      ((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i)
          = ((1 : ℝ) ^ i / (3 : ℝ) ^ i) * ((2 : ℝ) ^ (n - i) / (3 : ℝ) ^ (n - i)) := by
        simp [div_pow]
      _ = ((1 : ℝ) ^ i * (2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ i * (3 : ℝ) ^ (n - i)) := by ring
      _ = ((1 : ℝ) ^ i * (2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ ((i : ℕ) + (n - i) : ℕ)) := by
        simp [pow_add]
      _ = ((1 : ℝ) ^ i * (2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n) := by simp [h_add]
      _ = (1 * (2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n) := by simp
      _ = ((2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n) := by simp
  have h_term_eq (i : ℕ) : ((n.choose i : ℝ) * ((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i)) =
      ((n.choose i : ℝ) * (2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n) := by
    by_cases hle : i ≤ n
    · have h_pow := h_pow_eq i hle
      calc
        ((n.choose i : ℝ) * ((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i))
            = (n.choose i : ℝ) * (((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i)) := by ring
        _ = (n.choose i : ℝ) * (((2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n)) := by rw [h_pow]
        _ = ((n.choose i : ℝ) * (2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n) := by ring
    · have h_choose : (n.choose i : ℝ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hle)
      simp [h_choose]
  have h_sub : (1 : ℝ) - ((1 : ℝ) / 3) = ((2 : ℝ) / 3) := by norm_num
  calc
    binCdf n (1 / 3) v = ∑ i ∈ Finset.range (v + 1), binPmf n (1 / 3) i := rfl
    _ = ∑ i ∈ Finset.range (v + 1), ((n.choose i : ℝ) * ((1 : ℝ) / 3) ^ i * (1 - ((1 : ℝ) / 3)) ^ (n - i)) := rfl
    _ = ∑ i ∈ Finset.range (v + 1), ((n.choose i : ℝ) * ((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i)) := by
      rw [h_sub]
    _ = ∑ i ∈ Finset.range (v + 1), (((n.choose i : ℝ) * (2 : ℝ) ^ (n - i)) / ((3 : ℝ) ^ n)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h_term_eq i]
    _ = (∑ i ∈ Finset.range (v + 1), ((n.choose i : ℝ) * (2 : ℝ) ^ (n - i))) / ((3 : ℝ) ^ n) := by
      rw [Finset.sum_div]
    _ = (binCdfN n v 2 : ℝ) / ((3 : ℝ) ^ n) := by
      rw [binCdfN_eq n v 2]
      simp [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

theorem binCdf_quarter (n v : ℕ) : binCdf n (1 / 4) v = (binCdfN n v 3 : ℝ) / 4 ^ n := by
  unfold binCdf binPmf
  have hsub : (1 : ℝ) - (1 / 4 : ℝ) = (3 : ℝ) / 4 := by norm_num
  rw [hsub, binCdfN_eq]
  simp_rw [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hi_le_n : i ≤ n
  · -- case i ≤ n
    have h_add : (i : ℕ) + (n - i) = n := by
      rw [add_comm, Nat.sub_add_cancel hi_le_n]
    calc
      (n.choose i : ℝ) * (1 / 4) ^ i * (3 / 4) ^ (n - i) =
          (n.choose i : ℝ) * (((1 : ℝ) / 4) ^ i * ((3 : ℝ) / 4) ^ (n - i)) := by ring
      _ = (n.choose i : ℝ) * (((1 : ℝ) ^ i / (4 : ℝ) ^ i) * ((3 : ℝ) ^ (n - i) / (4 : ℝ) ^ (n - i))) := by
        simp [div_pow]
      _ = (n.choose i : ℝ) * (((1 : ℝ) * (3 : ℝ) ^ (n - i)) / ((4 : ℝ) ^ i * (4 : ℝ) ^ (n - i))) := by ring
      _ = (n.choose i : ℝ) * ((3 : ℝ) ^ (n - i) / ((4 : ℝ) ^ i * (4 : ℝ) ^ (n - i))) := by simp
      _ = ((n.choose i : ℝ) * (3 : ℝ) ^ (n - i)) / ((4 : ℝ) ^ i * (4 : ℝ) ^ (n - i)) := by ring
      _ = ((n.choose i : ℝ) * (3 : ℝ) ^ (n - i)) / ((4 : ℝ) ^ (i + (n - i))) := by rw [pow_add]
      _ = ((n.choose i : ℝ) * (3 : ℝ) ^ (n - i)) / (4 : ℝ) ^ n := by rw [h_add]
  · -- case n < i
    have h_choose_zero : (n.choose i : ℝ) = 0 := by
      rw [Nat.cast_eq_zero, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi_le_n)]
    simp [h_choose_zero]

theorem binCdf_le_one (n v : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : binCdf n p v ≤ 1 := by
  have h1p : 0 ≤ 1 - p := by linarith
  have h_nonneg : ∀ i, 0 ≤ binPmf n p i := by
    intro i
    dsimp [binPmf]
    have hc : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    have hp : 0 ≤ p ^ i := pow_nonneg h0 i
    have h1p' : 0 ≤ (1 - p) ^ (n - i) := pow_nonneg h1p (n - i)
    exact mul_nonneg (mul_nonneg hc hp) h1p'
  have hzero : ∀ i, n < i → binPmf n p i = 0 := by
    intro i hi
    dsimp [binPmf]
    have hchoose : n.choose i = 0 := Nat.choose_eq_zero_of_lt hi
    simp [hchoose]
  have h_full_eq_one : ∑ i ∈ Finset.range (n + 1), binPmf n p i = 1 := by
    calc
      ∑ i ∈ Finset.range (n + 1), binPmf n p i
          = ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) := rfl
      _ = ∑ i ∈ Finset.range (n + 1), (p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        ring
      _ = (p + (1 - p)) ^ n := by rw [add_pow]
      _ = 1 ^ n := by ring
      _ = 1 := by simp
  by_cases h : v ≤ n
  · -- v ≤ n: range (v+1) ⊆ range (n+1)
    have h_sub : Finset.range (v + 1) ⊆ Finset.range (n + 1) := by
      rw [Finset.range_subset_range]
      omega
    have h_sum_le : binCdf n p v ≤ ∑ i ∈ Finset.range (n + 1), binPmf n p i :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun i _hi _not => h_nonneg i)
    linarith
  · -- n < v: range (n+1) ⊆ range (v+1), extra terms are zero
    have h_sub : Finset.range (n + 1) ⊆ Finset.range (v + 1) := by
      rw [Finset.range_subset_range]
      omega
    have h_sum_split : ∑ i ∈ Finset.range (v + 1), binPmf n p i =
        (∑ i ∈ Finset.range (n + 1), binPmf n p i) + (∑ i ∈ (Finset.range (v + 1)) \ (Finset.range (n + 1)), binPmf n p i) := by
      calc
        ∑ i ∈ Finset.range (v + 1), binPmf n p i
            = (∑ i ∈ (Finset.range (v + 1)) \ (Finset.range (n + 1)), binPmf n p i) +
              (∑ i ∈ Finset.range (n + 1), binPmf n p i) := by rw [Finset.sum_sdiff h_sub]
        _ = (∑ i ∈ Finset.range (n + 1), binPmf n p i) + (∑ i ∈ (Finset.range (v + 1)) \ (Finset.range (n + 1)), binPmf n p i) := by rw [add_comm]
    have h_extra_zero : ∑ i ∈ (Finset.range (v + 1)) \ (Finset.range (n + 1)), binPmf n p i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_sdiff] at hi
      have hi_gt_n : n < i := by
        have : i ∉ Finset.range (n + 1) := hi.2
        rw [Finset.mem_range] at this
        omega
      exact hzero i hi_gt_n
    dsimp [binCdf]
    rw [h_sum_split, h_extra_zero, add_zero, h_full_eq_one]

theorem L_arith (nJ nb db rN dd : ℕ) (x PB : ℝ) (hnJ : nJ ≤ 2 ^ 52) (hdb : 0 < db) (hdd : 0 < dd)
    (hPB : PB ≤ x) (hx : x ≤ (nb : ℝ) / db) :
    ((nJ : ℝ) / 2 ^ 52 * (1 - PB) + PB) * ((rN : ℝ) / dd) ≤
      (cdiv (((nJ * db + nb * (2 ^ 52 - nJ)) * rN) * 2 ^ 76) (db * dd) : ℝ) / 2 ^ 128 := by
  -- Positivity of key constants
  have hpos_db : 0 < (db : ℝ) := by exact mod_cast hdb
  have hpos_dd : 0 < (dd : ℝ) := by exact mod_cast hdd
  have hpos_2pow52 : 0 < (2 ^ 52 : ℝ) := by norm_num
  have hpos_2pow128 : 0 ≤ (2 ^ 128 : ℝ) := by norm_num
  have hpos_rN_div_dd : 0 ≤ (rN : ℝ) / dd := div_nonneg (Nat.cast_nonneg _) (by exact mod_cast hdd.le)
  have hpos_1_minus_δ : 0 ≤ 1 - (nJ : ℝ) / (2 ^ 52 : ℝ) := by
    refine sub_nonneg.mpr ?_
    exact (div_le_one (by norm_num)).mpr (mod_cast hnJ)
  -- δ = nJ / 2^52
  set δ := (nJ : ℝ) / (2 ^ 52 : ℝ) with hδ
  -- Key inequality: δ*(1-PB) + PB ≤ δ + (nb/db)*(1-δ)
  have h_main : δ * (1 - PB) + PB ≤ δ + ((nb : ℝ) / db) * (1 - δ) := by
    have h_PB_le : PB ≤ (nb : ℝ) / db := by linarith
    have h_mul : PB * (1 - δ) ≤ ((nb : ℝ) / db) * (1 - δ) :=
      mul_le_mul_of_nonneg_right h_PB_le hpos_1_minus_δ
    calc
      δ * (1 - PB) + PB = δ + PB * (1 - δ) := by ring
      _ ≤ δ + ((nb : ℝ) / db) * (1 - δ) := by gcongr
  -- Multiply by rN/dd ≥ 0
  have h_mul : (δ * (1 - PB) + PB) * ((rN : ℝ) / dd) ≤ (δ + ((nb : ℝ) / db) * (1 - δ)) * ((rN : ℝ) / dd) :=
    mul_le_mul_of_nonneg_right h_main hpos_rN_div_dd
  -- Algebraic simplification of the RHS
  have h_expr : (δ + ((nb : ℝ) / db) * (1 - δ)) * ((rN : ℝ) / dd) =
      ((nJ : ℝ) * (db : ℝ) + (nb : ℝ) * ((2 ^ 52 : ℝ) - (nJ : ℝ))) * (rN : ℝ) / ((2 ^ 52 : ℝ) * (db : ℝ) * (dd : ℝ)) := by
    dsimp [δ]
    field_simp [show (2 ^ 52 : ℝ) ≠ 0 from by norm_num, show (db : ℝ) ≠ 0 from by exact mod_cast hdb.ne']
  -- Set N = ((nJ * db + nb * (2 ^ 52 - nJ)) * rN) * 2 ^ 76
  set N := ((nJ * db + nb * (2 ^ 52 - nJ)) * rN) * 2 ^ 76 with hN
  have h_cast : (N : ℝ) = ((nJ : ℝ) * (db : ℝ) + (nb : ℝ) * ((2 ^ 52 : ℝ) - (nJ : ℝ))) * (rN : ℝ) * (2 ^ 76 : ℝ) := by
    have hnJ_large : nJ ≤ 4503599627370496 := by
      have h : (2 ^ 52 : ℕ) = 4503599627370496 := by norm_num
      simpa [h] using hnJ
    dsimp [N]
    simp [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hnJ_large]
    norm_num
  have h_eq : ((nJ : ℝ) * (db : ℝ) + (nb : ℝ) * ((2 ^ 52 : ℝ) - (nJ : ℝ))) * (rN : ℝ) / ((2 ^ 52 : ℝ) * (db : ℝ) * (dd : ℝ)) =
      (N : ℝ) / ((2 ^ 128 : ℝ) * (db : ℝ) * (dd : ℝ)) := by
    rw [h_cast]
    have h_pow : (2 ^ 128 : ℝ) = (2 ^ 52 : ℝ) * (2 ^ 76 : ℝ) := by norm_num
    rw [h_pow]
    ring
  -- Apply cdiv_spec
  have h_cdiv : (N : ℝ) / (db * dd : ℝ) ≤ (cdiv N (db * dd) : ℝ) := by
    simpa [Nat.cast_mul] using cdiv_spec N (db * dd) (mul_pos hdb hdd)
  -- Final chain of inequalities
  calc
    ((nJ : ℝ) / 2 ^ 52 * (1 - PB) + PB) * ((rN : ℝ) / dd) ≤ (δ + ((nb : ℝ) / db) * (1 - δ)) * ((rN : ℝ) / dd) := h_mul
    _ = ((nJ : ℝ) * (db : ℝ) + (nb : ℝ) * ((2 ^ 52 : ℝ) - (nJ : ℝ))) * (rN : ℝ) / ((2 ^ 52 : ℝ) * (db : ℝ) * (dd : ℝ)) := h_expr
    _ = (N : ℝ) / ((2 ^ 128 : ℝ) * (db : ℝ) * (dd : ℝ)) := h_eq
    _ = ((N : ℝ) / (db * dd : ℝ)) / (2 ^ 128 : ℝ) := by ring
    _ ≤ (cdiv N (db * dd) : ℝ) / (2 ^ 128 : ℝ) := (div_le_div_of_nonneg_right h_cdiv hpos_2pow128)
    _ = (cdiv (((nJ * db + nb * (2 ^ 52 - nJ)) * rN) * 2 ^ 76) (db * dd) : ℝ) / 2 ^ 128 := rfl

theorem lemma12B_check (N v U rho nF : ℕ) (D : ℝ) (hD : D ≤ (U : ℝ) / 2 ^ 128 * ((N : ℝ) / 3))
    (hrho : N * 2 ^ 256 ≤ 3 * rho ^ 2) (hv : 3 * (v + 1) < N)
    (hc : 2 * U * N + 3 * rho ≤ nF * 2 ^ 77 * (N - 3 * (v + 1))) :
    lemma12B D ((N : ℝ) / 3) v ≤ (nF : ℝ) / 2 ^ 52 := by
  set mu := (N : ℝ) / 3 with hmu
  have hv_nat : 3 * (v + 1) < N := hv
  have hv_cast : (3 : ℝ) * ((v : ℝ) + 1) < (N : ℝ) := by exact_mod_cast hv_nat
  have h_den_pos : 0 < mu - ((v : ℝ) + 1) := by
    rw [hmu]
    linarith
  have h_den_nonneg : 0 ≤ mu - ((v : ℝ) + 1) := by linarith
  have hv_lt_mu : (v : ℝ) + 1 < mu := by
    rw [hmu]
    linarith
  have hlemma : lemma12B D mu v = (D + Real.sqrt mu / 2) / (mu - ((v : ℝ) + 1)) := by
    unfold lemma12B
    simp [hv_lt_mu]
  rw [hlemma]
  have h_sqrt : Real.sqrt mu ≤ (rho : ℝ) / ((2 : ℝ) ^ 128) := by
    have h_mu_nonneg : 0 ≤ mu := by
      rw [hmu]
      have hN : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
      positivity
    have h_pow_pos : 0 < (2 : ℝ) ^ 128 := by positivity
    have h_sq : mu * ((2 : ℝ) ^ 256) ≤ (rho : ℝ) ^ 2 := by
      have h_hrho' : (N : ℝ) * ((2 : ℝ) ^ 256) ≤ (3 : ℝ) * ((rho : ℝ) ^ 2) := by
        exact_mod_cast hrho
      calc
        mu * ((2 : ℝ) ^ 256) = ((N : ℝ) / 3) * ((2 : ℝ) ^ 256) := rfl
        _ = ((N : ℝ) * ((2 : ℝ) ^ 256)) / 3 := by ring
        _ ≤ ((3 : ℝ) * ((rho : ℝ) ^ 2)) / 3 :=
          div_le_div_of_nonneg_right h_hrho' (by norm_num : (0 : ℝ) ≤ 3)
        _ = (rho : ℝ) ^ 2 := by ring
    have h_sqrt_sq : Real.sqrt (mu * ((2 : ℝ) ^ 256)) ≤ Real.sqrt ((rho : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt h_sq
    have h_sqrt_mul : Real.sqrt (mu * ((2 : ℝ) ^ 256)) = Real.sqrt mu * Real.sqrt (((2 : ℝ) ^ 256)) :=
      Real.sqrt_mul h_mu_nonneg _
    have h_sqrt_pow : Real.sqrt (((2 : ℝ) ^ 256)) = (2 : ℝ) ^ 128 := by
      calc
        Real.sqrt (((2 : ℝ) ^ 256)) = Real.sqrt (((2 : ℝ) ^ 128) ^ 2) := by ring
        _ = |(2 : ℝ) ^ 128| := Real.sqrt_sq_eq_abs _
        _ = (2 : ℝ) ^ 128 := abs_of_pos (by positivity)
    have h_sqrt_rho : Real.sqrt ((rho : ℝ) ^ 2) = (rho : ℝ) :=
      Real.sqrt_sq (by exact_mod_cast Nat.zero_le rho)
    rw [h_sqrt_mul, h_sqrt_pow, h_sqrt_rho] at h_sqrt_sq
    calc
      Real.sqrt mu = (Real.sqrt mu * ((2 : ℝ) ^ 128)) / ((2 : ℝ) ^ 128) := by
        field_simp [ne_of_gt h_pow_pos]
      _ ≤ (rho : ℝ) / ((2 : ℝ) ^ 128) := div_le_div_of_nonneg_right h_sqrt_sq (by positivity)
  have h_num : D + Real.sqrt mu / 2 ≤ ((U : ℝ) * (N : ℝ) / 3 + (rho : ℝ) / 2) / ((2 : ℝ) ^ 128) := by
    have hD' : D ≤ ((U : ℝ) * mu) / ((2 : ℝ) ^ 128) := by
      simpa [hmu, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hD
    have h_sqrt' : Real.sqrt mu / 2 ≤ ((rho : ℝ) / 2) / ((2 : ℝ) ^ 128) := by
      calc
        Real.sqrt mu / 2 ≤ ((rho : ℝ) / ((2 : ℝ) ^ 128)) / 2 := by gcongr
        _ = (rho : ℝ) / (((2 : ℝ) ^ 128) * 2) := by ring
        _ = (rho : ℝ) / ((2 : ℝ) ^ 129) := by ring
        _ = ((rho : ℝ) / 2) / ((2 : ℝ) ^ 128) := by ring
    calc
      D + Real.sqrt mu / 2 ≤ ((U : ℝ) * mu) / ((2 : ℝ) ^ 128) + ((rho : ℝ) / 2) / ((2 : ℝ) ^ 128) := by
        gcongr
      _ = ((U : ℝ) * mu + (rho : ℝ) / 2) / ((2 : ℝ) ^ 128) := by ring
      _ = ((U : ℝ) * ((N : ℝ) / 3) + (rho : ℝ) / 2) / ((2 : ℝ) ^ 128) := by rw [hmu]
      _ = ((U : ℝ) * (N : ℝ) / 3 + (rho : ℝ) / 2) / ((2 : ℝ) ^ 128) := by ring
  have h_main : (D + Real.sqrt mu / 2) / (mu - ((v : ℝ) + 1)) ≤ (nF : ℝ) / ((2 : ℝ) ^ 52) := by
    have h_le_nat : 3 * (v + 1) ≤ N := by omega
    have h_den_ne_zero : (N : ℝ) - 3 * ((v : ℝ) + 1) ≠ 0 := by
      intro hzero
      have : (N : ℝ) = 3 * ((v : ℝ) + 1) := by linarith
      have h_lt : (3 : ℝ) * ((v : ℝ) + 1) < (N : ℝ) := by exact_mod_cast hv_nat
      linarith
    calc
      (D + Real.sqrt mu / 2) / (mu - ((v : ℝ) + 1))
          ≤ (((U : ℝ) * (N : ℝ) / 3 + (rho : ℝ) / 2) / ((2 : ℝ) ^ 128)) / (mu - ((v : ℝ) + 1)) :=
        div_le_div_of_nonneg_right h_num h_den_nonneg
      _ = ((2 : ℝ) * (U : ℝ) * (N : ℝ) + 3 * (rho : ℝ)) / (((2 : ℝ) ^ 129) * ((N : ℝ) - 3 * ((v : ℝ) + 1))) := by
        rw [hmu]
        field_simp
      _ ≤ ((nF : ℝ) * ((2 : ℝ) ^ 77) * ((N : ℝ) - 3 * ((v : ℝ) + 1))) / (((2 : ℝ) ^ 129) * ((N : ℝ) - 3 * ((v : ℝ) + 1))) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have hc_real : (2 * U * N + 3 * rho : ℝ) ≤ (nF : ℝ) * ((2 : ℝ) ^ 77) * ((N : ℝ) - 3 * ((v : ℝ) + 1)) := by
          have hc' : (2 * U * N + 3 * rho : ℝ) ≤ (nF * 2 ^ 77 * (N - 3 * (v + 1)) : ℝ) := by
            exact_mod_cast hc
          simpa [Nat.cast_sub h_le_nat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hc'
        simpa [mul_comm, mul_left_comm, mul_assoc] using hc_real
      _ = (nF : ℝ) / ((2 : ℝ) ^ 52) := by
        field_simp [h_den_ne_zero]
  exact h_main

theorem A_arith (main Den nF nF' E v n0 : ℕ) (hDen : 0 < Den)
    (h : main * 2 ^ (E + v + 52 + 2 * n0) + 3 * binSum (E + v) v * (nF * Den) * 2 ^ (2 * n0) +
        binCdfN n0 v 3 * Den * 2 ^ (E + v + 52) ≤ nF' * Den * 2 ^ (E + v + 2 * n0)) :
    (main : ℝ) / Den + 3 * binGe (E + v) (1 / 2) E * ((nF : ℝ) / 2 ^ 52) + binCdf n0 (1 / 4) v ≤
      (nF' : ℝ) / 2 ^ 52 := by
  have hℝ : (main : ℝ) * (2 : ℝ) ^ (E + v + 52 + 2 * n0) + 3 * (binSum (E + v) v : ℝ) * ((nF : ℝ) * (Den : ℝ)) * (2 : ℝ) ^ (2 * n0) +
      (binCdfN n0 v 3 : ℝ) * (Den : ℝ) * (2 : ℝ) ^ (E + v + 52) ≤ (nF' : ℝ) * (Den : ℝ) * (2 : ℝ) ^ (E + v + 2 * n0) := by
    exact_mod_cast h
  have hbinGe : binGe (E + v) (1 / 2) E = ((binSum (E + v) v : ℕ) : ℝ) / ((2 : ℝ) ^ (E + v)) := by
    have hle : E ≤ E + v := Nat.le_add_right E v
    have h := binGe_half (E + v) E hle
    simpa [Nat.add_sub_cancel_left] using h
  have hbinCdf : binCdf n0 (1 / 4) v = ((binCdfN n0 v 3 : ℕ) : ℝ) / ((2 : ℝ) ^ (2 * n0)) := by
    have h := binCdf_quarter n0 v
    rw [h]
    have h4pow : (4 : ℝ) ^ n0 = (2 : ℝ) ^ (2 * n0) := by
      calc
        (4 : ℝ) ^ n0 = ((2 : ℝ) ^ 2) ^ n0 := by norm_num
        _ = (2 : ℝ) ^ (2 * n0) := by simp [pow_mul]
    rw [h4pow]
  have hpos_denom : 0 < (Den : ℝ) * (2 : ℝ) ^ (E + v + 52 + 2 * n0) := by
    positivity
  -- Multiply the goal by the positive denominator and show it equals hℝ
  have h_mul : ((main : ℝ) / Den + 3 * binGe (E + v) (1 / 2) E * ((nF : ℝ) / 2 ^ 52) + binCdf n0 (1 / 4) v) * ((Den : ℝ) * (2 : ℝ) ^ (E + v + 52 + 2 * n0)) ≤
      ((nF' : ℝ) / 2 ^ 52) * ((Den : ℝ) * (2 : ℝ) ^ (E + v + 52 + 2 * n0)) := by
    calc
      ((main : ℝ) / Den + 3 * binGe (E + v) (1 / 2) E * ((nF : ℝ) / 2 ^ 52) + binCdf n0 (1 / 4) v) * ((Den : ℝ) * (2 : ℝ) ^ (E + v + 52 + 2 * n0))
          = ((main : ℝ) * (2 : ℝ) ^ (E + v + 52 + 2 * n0) + 3 * (binSum (E + v) v : ℝ) * ((nF : ℝ) * (Den : ℝ)) * (2 : ℝ) ^ (2 * n0) +
              (binCdfN n0 v 3 : ℝ) * (Den : ℝ) * (2 : ℝ) ^ (E + v + 52)) := by
        rw [hbinGe, hbinCdf]
        field_simp [hDen.ne.symm]
        ring
      _ ≤ (nF' : ℝ) * (Den : ℝ) * (2 : ℝ) ^ (E + v + 2 * n0) := hℝ
      _ = ((nF' : ℝ) / 2 ^ 52) * ((Den : ℝ) * (2 : ℝ) ^ (E + v + 52 + 2 * n0)) := by
        field_simp
        ring
  exact le_of_mul_le_mul_right h_mul hpos_denom

theorem B_val (main Den nF E J K : ℕ) (hJ : 1 ≤ J) (hDen : 0 < Den) :
    ((main * 2 ^ (E + J - 1 + 52 + 2 * K) + 2 * binSum (E + J - 1) (J - 1) * (nF * Den) * 2 ^ (2 * K) +
        binLt4 K J * Den * 2 ^ (E + J - 1 + 52) : ℕ) : ℝ) / ((Den * 2 ^ (E + J - 1 + 52 + 2 * K) : ℕ) : ℝ) =
      (main : ℝ) / Den + 2 * binGe (E + J - 1) (1 / 2) E * ((nF : ℝ) / 2 ^ 52) + binLt K (1 / 4) J := by
  have hE : E ≤ E + J - 1 := by omega
  have hGe := binGe_half (E + J - 1) E hE
  have hLt := binLt_quarter K J
  have h_sub : (E + J - 1) - E = J - 1 := by omega
  rw [h_sub] at hGe
  have hDen' : (Den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hDen.ne.symm
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h4pow : (4 : ℝ) ^ K = (2 : ℝ) ^ (2 * K) := by
    calc
      (4 : ℝ) ^ K = ((2 : ℝ) ^ 2) ^ K := by norm_num
      _ = (2 : ℝ) ^ (2 * K) := by rw [pow_mul]
  push_cast
  rw [hGe, hLt, h4pow]
  field_simp [hDen', h2]
  ring

theorem S2_arith (n dd : ℕ) (hdd : 0 < dd) (s2 dt : ℕ → ℕ) (law : ℕ → ℝ) (hlaw : ∀ k < n, law k ≤ (s2 k : ℝ) / 2 ^ 64) :
    ∑ k ∈ Finset.range n, law k * ((dt k : ℝ) / (2 ^ 52 * dd)) ≤
      (cdiv ((∑ k ∈ Finset.range n, s2 k * dt k) * 2 ^ 128) (dd * 2 ^ 116) : ℝ) / 2 ^ 128 := by
  -- First prove cdiv_spec inline, since it's not yet available
  have cdiv_spec (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
    have hle : a ≤ cdiv a b * b := by
      have h := Nat.lt_mul_div_succ (a + b - 1) hb
      have hcdiv_eq : cdiv a b = (a + b - 1) / b := rfl
      rw [← hcdiv_eq] at h
      have h' : a + b - 1 < cdiv a b * b + b := by
        simpa [mul_add, mul_comm] using h
      omega
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hle' : (a : ℝ) ≤ (cdiv a b * b : ℕ).cast := by exact_mod_cast hle
    calc
      (a : ℝ) / (b : ℝ) ≤ ((cdiv a b * b : ℕ) : ℝ) / (b : ℝ) :=
        div_le_div_of_nonneg_right hle' (by positivity)
      _ = ((cdiv a b : ℝ) * (b : ℝ)) / (b : ℝ) := by simp
      _ = (cdiv a b : ℝ) := by
        field_simp [hb'.ne']
  set S := ∑ k ∈ Finset.range n, s2 k * dt k with hS
  have hSpos : 0 < dd * 2 ^ 116 := by
    have h2 : 0 < (2 : ℕ) ^ 116 := by norm_num
    exact mul_pos hdd h2
  have hpos_term : ∀ k, 0 ≤ (dt k : ℝ) / ((2 : ℝ) ^ 52 * (dd : ℝ)) := by
    intro k
    refine div_nonneg (Nat.cast_nonneg _) ?_
    positivity
  have hpointwise : ∀ k, k < n → law k * ((dt k : ℝ) / ((2 : ℝ) ^ 52 * (dd : ℝ))) ≤
      ((s2 k : ℝ) / ((2 : ℝ) ^ 64)) * ((dt k : ℝ) / ((2 : ℝ) ^ 52 * (dd : ℝ))) := by
    intro k hk
    refine mul_le_mul_of_nonneg_right (hlaw k hk) (hpos_term k)
  have hsum : ∑ k ∈ Finset.range n, law k * ((dt k : ℝ) / ((2 : ℝ) ^ 52 * (dd : ℝ))) ≤
      ∑ k ∈ Finset.range n, ((s2 k : ℝ) / ((2 : ℝ) ^ 64)) * ((dt k : ℝ) / ((2 : ℝ) ^ 52 * (dd : ℝ))) :=
    Finset.sum_le_sum fun k hk => hpointwise k (Finset.mem_range.1 hk)
  have hsum_simplify : ∑ k ∈ Finset.range n, ((s2 k : ℝ) / ((2 : ℝ) ^ 64)) * ((dt k : ℝ) / ((2 : ℝ) ^ 52 * (dd : ℝ))) =
      ((S : ℝ) / (((2 : ℝ) ^ 116) * (dd : ℝ))) := by
    calc
      ∑ k ∈ Finset.range n, ((s2 k : ℝ) / ((2 : ℝ) ^ 64)) * ((dt k : ℝ) / ((2 : ℝ) ^ 52 * (dd : ℝ)))
          = ∑ k ∈ Finset.range n, ((s2 k : ℝ) * (dt k : ℝ)) / (((2 : ℝ) ^ 64) * (((2 : ℝ) ^ 52) * (dd : ℝ))) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            ring
      _ = ∑ k ∈ Finset.range n, ((s2 k * dt k : ℕ) : ℝ) / (((2 : ℝ) ^ 64) * ((2 : ℝ) ^ 52) * (dd : ℝ)) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            push_cast
            ring
      _ = (∑ k ∈ Finset.range n, ((s2 k * dt k : ℕ) : ℝ)) / (((2 : ℝ) ^ 64) * ((2 : ℝ) ^ 52) * (dd : ℝ)) := by
            rw [Finset.sum_div]
      _ = ((S : ℝ) / (((2 : ℝ) ^ 64) * ((2 : ℝ) ^ 52) * (dd : ℝ))) := by
            simp [hS, Nat.cast_sum]
      _ = ((S : ℝ) / (((2 : ℝ) ^ 116) * (dd : ℝ))) := by
            have h_denom : ((2 : ℝ) ^ 64) * ((2 : ℝ) ^ 52) * (dd : ℝ) = ((2 : ℝ) ^ 116) * (dd : ℝ) := by
              have h : ((2 : ℝ) ^ 64) * ((2 : ℝ) ^ 52) = (2 : ℝ) ^ 116 := by
                calc
                  ((2 : ℝ) ^ 64) * ((2 : ℝ) ^ 52) = (2 : ℝ) ^ (64 + 52) := by rw [← pow_add]
                  _ = (2 : ℝ) ^ 116 := by norm_num
              rw [h]
            rw [h_denom]
  have hidentity : ((S : ℝ) / (((2 : ℝ) ^ 116) * (dd : ℝ))) =
      (((S * 2 ^ 128 : ℕ) : ℝ) / ((dd * 2 ^ 116 : ℕ) : ℝ)) / ((2 : ℝ) ^ 128) := by
    push_cast
    ring
  have hcdiv := cdiv_spec (S * 2 ^ 128) (dd * 2 ^ 116) hSpos
  have hDpos : (0 : ℝ) ≤ ((2 : ℝ) ^ 128) := by norm_num
  have hfinal : (((S * 2 ^ 128 : ℕ) : ℝ) / ((dd * 2 ^ 116 : ℕ) : ℝ)) / ((2 : ℝ) ^ 128) ≤
      (cdiv (S * 2 ^ 128) (dd * 2 ^ 116) : ℝ) / ((2 : ℝ) ^ 128) :=
    div_le_div_of_nonneg_right hcdiv hDpos
  calc
    ∑ k ∈ Finset.range n, law k * ((dt k : ℝ) / (2 ^ 52 * dd))
        ≤ ∑ k ∈ Finset.range n, ((s2 k : ℝ) / 2 ^ 64) * ((dt k : ℝ) / (2 ^ 52 * dd)) := hsum
    _ = ((S : ℝ) / (((2 : ℝ) ^ 116) * (dd : ℝ))) := hsum_simplify
    _ = (((S * 2 ^ 128 : ℕ) : ℝ) / ((dd * 2 ^ 116 : ℕ) : ℝ)) / ((2 : ℝ) ^ 128) := hidentity
    _ ≤ (cdiv (S * 2 ^ 128) (dd * 2 ^ 116) : ℝ) / ((2 : ℝ) ^ 128) := hfinal
    _ = (cdiv ((∑ k ∈ Finset.range n, s2 k * dt k) * 2 ^ 128) (dd * 2 ^ 116) : ℝ) / 2 ^ 128 := by
      simp [hS]

theorem Dt_eq (S : State) (a b j k : ℕ) (x : ℕ → ℕ)
    (hx : ∀ k' ≤ k, S.delta k' = (x k' : ℝ) / 2 ^ 52) :
    Dt S a b j k = (((Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
      (fun k' => x k' * ratioN a b k' j) : ℕ) : ℝ) / (2 ^ 52 * ratioD a b j) := by
  set B := (2 ^ 52 : ℝ) * (ratioD a b j : ℝ) with hB
  have hB_nonneg : 0 ≤ B := by
    rw [hB]
    have h1 : 0 ≤ (2 ^ 52 : ℝ) := by norm_num
    have h2 : 0 ≤ (ratioD a b j : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg h1 h2
  have hg_inf : ∀ (x y : ℝ), (x ⊓ y) / B = (x / B) ⊓ (y / B) := by
    intro x y
    calc
      (x ⊓ y) / B = min x y / B := rfl
      _ = min (x / B) (y / B) := by rw [min_div_div_right hB_nonneg]
      _ = (x / B) ⊓ (y / B) := rfl
  have h_term_eq : ∀ k', k' ∈ Finset.range (k + 1) → S.delta k' * ratio a b k' j =
      (((x k' * ratioN a b k' j : ℕ) : ℝ) / B) := by
    intro k' hk'
    have hk'_le_k : k' ≤ k := by
      have := Finset.mem_range.1 hk'
      omega
    rw [hx k' hk'_le_k, ratio_eq a b k' j]
    push_cast
    ring
  calc
    Dt S a b j k = (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun k' => S.delta k' * ratio a b k' j) := rfl
    _ = (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun k' => (((x k' * ratioN a b k' j : ℕ) : ℝ) / B)) := by
      rw [Finset.inf'_congr Finset.nonempty_range_add_one rfl h_term_eq]
    _ = ((Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun k' => ((x k' * ratioN a b k' j : ℕ) : ℝ))) / B := by
      simpa using (Finset.apply_inf'_eq_inf'_comp Finset.nonempty_range_add_one
        (fun t : ℝ => t / B) hg_inf).symm
    _ = (((Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun k' => x k' * ratioN a b k' j) : ℕ) : ℝ) / B := by
      rw [Nat.cast_finsetInf' (fun k' => x k' * ratioN a b k' j) Finset.nonempty_range_add_one]
    _ = (((Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun k' => x k' * ratioN a b k' j) : ℕ) : ℝ) / (2 ^ 52 * ratioD a b j) := by rfl

theorem runmin_fold (n : ℕ) (X : ℕ → ℕ) (l : List ℕ) :
    (natFold n (0, 0, l) (fun k (st : ℕ × ℕ × List ℕ) =>
        let x := X k
        let dt := cond (Nat.beq k 0) x (minN st.2.1 x)
        (Nat.add st.1 (Nat.mul (hd st.2.2) dt), dt, tl st.2.2))).1 =
      ∑ k ∈ Finset.range n, l.getD k 0 *
        (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one X := by
  set f := fun (k : ℕ) (st : ℕ × ℕ × List ℕ) =>
    let x := X k
    let dt := cond (Nat.beq k 0) x (minN st.2.1 x)
    (Nat.add st.1 (Nat.mul (hd st.2.2) dt), dt, tl st.2.2) with hf
  set R := fun (k : ℕ) => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one X with hR
  have minN_eq_min : ∀ a b : ℕ, minN a b = min a b := by
    intro a b
    rcases Nat.le_total a b with (h | h)
    · have hsub : a - b = 0 := Nat.sub_eq_zero_of_le h
      simp [minN, hsub, h]
    · have hsub : a - (a - b) = b := by omega
      simp [minN, hsub, h]
  have hR_succ : ∀ k : ℕ, R (k + 1) = min (R k) (X (k + 1)) := by
    intro k
    dsimp [R]
    have hne : (Finset.range (k + 1)).Nonempty := Finset.nonempty_range_add_one (n := k)
    convert Finset.inf'_insert hne X (b := k+1) (s := Finset.range (k+1)) using 1
    · simp [Finset.range_add_one]
    · simp [min_comm]
  have hhd : ∀ (l : List ℕ) (m : ℕ), hd (l.drop m) = l.getD m 0 := by
    intro l m
    induction m generalizing l with
    | zero =>
        cases l <;> rfl
    | succ m ih =>
        cases l with
        | nil => rfl
        | cons x xs =>
            simp [hd, List.drop, List.getD]
  have invariant : ∀ (m : ℕ), natFold m (0, 0, l) f =
      ((∑ k ∈ Finset.range m, l.getD k 0 * R k),
       (if m = 0 then 0 else R (m - 1)),
       l.drop m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [show natFold (m + 1) (0, 0, l) f = f m (natFold m (0, 0, l) f) from rfl]
        rw [ih]
        dsimp [f]
        rw [hhd l m]
        have htl : tl (l.drop m) = l.drop (m + 1) := by
          simp [tl, List.tail_drop]
        rw [htl]
        by_cases hm : m = 0
        · subst hm; simp [hR]
        · have hm_eq : m = (m - 1) + 1 := by omega
          have hRm : R m = min (R (m - 1)) (X m) := by
            rw [hm_eq]
            exact hR_succ (m - 1)
          simp [hm, minN_eq_min (R (m - 1)) (X m), hRm, Finset.sum_range_succ]
  rw [invariant n]

end FrogModel.D3.LaneD
