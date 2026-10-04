module

public import FrogModel.D3.M1K.Closure

@[expose] public section

/-!
# Height `0` of the stored run against `Rhat_0` and `Khat_0` at `L = 60`

`check0` reads the stored laws of height `0`: off the bottom, `rho*_0` has mass only at `(1, 0)` and
`(2, 0)`, `K*_0(t -> .)` only at `(1, t)` and `(0, t)`, each at most a constant `c`. Each constant over
`2^62` is at most the exact entry, `2 q (1 - q)`, `q^2`, `q`, `1 - q` with `q = q_60`, so the stored
laws are below the exact ones off the bottom (`height0_sound`): condition (i) of Proposition 13.3 of
the paper.
-/

open FrogModel.Lanes FrogModel.D3.Iface

namespace FrogModel.D3.M1K

/-! ## Leaves: the exact laws at height `0` -/

/-- `q_60 = (3^60 - 1)/(3^61 - 1)`. -/
theorem qL60_eq : qL 60 = (3 ^ 60 - 1) / (3 ^ 61 - 1) := by
  unfold qL pL
  norm_num

theorem qL60_nonneg : 0 ≤ qL 60 := by
  rw [qL60_eq]; norm_num

theorem qL60_le_one : qL 60 ≤ 1 := by
  rw [qL60_eq]; norm_num

theorem c1_le : (2049638230412172401 : ℝ) / 2 ^ 62 ≤ 2 * qL 60 * (1 - qL 60) := by
  rw [qL60_eq]; norm_num

theorem c2_le : (512409557603043100 : ℝ) / 2 ^ 62 ≤ qL 60 ^ 2 := by
  rw [qL60_eq]; norm_num

theorem c3_le : (1537228672809129301 : ℝ) / 2 ^ 62 ≤ qL 60 := by
  rw [qL60_eq]; norm_num

theorem c4_le : (3074457345618258602 : ℝ) / 2 ^ 62 ≤ 1 - qL 60 := by
  rw [qL60_eq]; norm_num

theorem Rhat0_one : Rhat0 V 60 1 0 = 2 * qL 60 * (1 - qL 60) := by
  simp [Rhat0, Finset.sum_range_succ, V]

theorem Rhat0_two : Rhat0 V 60 2 0 = qL 60 ^ 2 := by
  simp [Rhat0, Finset.sum_range_succ, V]

theorem Rhat0_nonneg (b f : ℕ) : 0 ≤ Rhat0 V 60 b f := by
  unfold Rhat0
  have h0 := qL60_nonneg
  have h1 := qL60_le_one
  split_ifs
  · refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · have : 0 ≤ 1 - qL 60 := by linarith
      positivity
    · exact le_rfl
  · exact le_rfl

theorem Khat0_nonneg (t a f : ℕ) : 0 ≤ Khat0 60 t a f := by
  unfold Khat0
  have := qL60_nonneg
  have := qL60_le_one
  split_ifs <;> linarith

/-! ## The check of height `0` -/

theorem lane_div_le (n c : ℕ) (h : n ≤ c) (r : ℝ) (hr : (c : ℝ) / 2 ^ 62 ≤ r) :
    (n : ℝ) / 2 ^ 62 ≤ r :=
  le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)) hr

theorem height0_sound (s : St) (h : check0 s = true) :
    OffBottomLe V 3 (rhoR s) (Rhat0 V 60) ∧ ∀ t ≤ 3, OffBottomLe V t (KR s t) (Khat0 60 t) := by
  unfold check0 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hz, ⟨h4, h8⟩, hK⟩ := h
  rw [natFold_and] at hz hK
  refine ⟨fun a ha f hf hoff => ?_, fun t ht a ha f hf hoff => ?_⟩
  · have hl : 4 * a + f < NL := by simp only [V] at ha; simp only [NL]; omega
    unfold rhoR
    rw [ite_eq_left ⟨ha, hf⟩]
    have hzl := hz _ hl
    simp only [Bool.or_eq_true, Nat.beq_eq] at hzl
    rcases hzl with (h0 | h0 | h0) | h0
    · omega
    · obtain ⟨rfl, rfl⟩ : a = 1 ∧ f = 0 := by omega
      rw [Rhat0_one]
      exact lane_div_le _ _ (Nat.le_of_ble_eq_true h4) _ c1_le
    · obtain ⟨rfl, rfl⟩ : a = 2 ∧ f = 0 := by omega
      rw [Rhat0_two]
      exact lane_div_le _ _ (Nat.le_of_ble_eq_true h8) _ c2_le
    · rw [h0, Nat.cast_zero, zero_div]
      exact Rhat0_nonneg a f
  · have hl : 4 * a + f < NL := by simp only [V] at ha; simp only [NL]; omega
    have hKt := hK t (by omega)
    simp only [Bool.and_eq_true] at hKt
    obtain ⟨hzt, h3, hc4⟩ := hKt
    rw [natFold_and] at hzt
    unfold KR
    rw [ite_eq_left ⟨ha, by omega⟩]
    have hzl := hzt _ hl
    simp only [Bool.or_eq_true, Nat.beq_eq, Nat.add_eq] at hzl
    simp only [Nat.add_eq] at h3
    rcases hzl with (h0 | h0 | h0) | h0
    · omega
    · obtain ⟨ha0, hft⟩ : a = 0 ∧ f = t := by omega
      have ht0 : t ≠ 0 := by omega
      simp only [Bool.or_eq_true, Nat.beq_eq, ht0, false_or] at hc4
      rw [ha0, hft]
      unfold Khat0
      rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl]
      exact lane_div_le _ _ (by simpa using Nat.le_of_ble_eq_true hc4) _ c4_le
    · obtain ⟨ha0, hft⟩ : a = 1 ∧ f = t := by omega
      rw [ha0, hft]
      unfold Khat0
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact lane_div_le _ _ (by have := Nat.le_of_ble_eq_true h3; simpa [Nat.add_comm] using this) _ c3_le
    · rw [h0, Nat.cast_zero, zero_div]
      exact Khat0_nonneg t a f

end FrogModel.D3.M1K
