module

public import FrogModel.D3.Interfaces.Checks
public import FrogModel.D3.LaneD.SingleSound
public import FrogModel.D3.LaneD.K.Seed

@[expose] public section

/-!
# The seed check is sound

`seedCheck_sound`: if `K.seedCheck` accepts the masses `massPk` and the stored seed `(F, D)`, the
stored seed is at least the seed state `seedState 48 100 96 W` (the seed of Lemma 13.4 of the paper)
built from the masses `W k x = n_k(x)/2^62`, and it is well formed at `P0 = (32, 96, 16, 12)`.

The quantities of the seed in integers: `e_k = E_k/2^62` with `E_k = sum over x of x n_k(x)`
(`eS_eq`), `c_k(g) = 1 - (sum over x in (g, 48] of n_k(x))/2^62` (`cS_eq`); the deficit terms
`M<k'>` (`seed_M_le`) and the term `R` (`seed_R_le`) as exact integer comparisons.
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K

theorem mass_eq (massPk k x : ℕ) : mass massPk k x = (massPk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 := by
  simp only [mass, slot_eq, Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]

theorem massMean_eq (massPk k : ℕ) : massMean massPk k = ∑ x ∈ Finset.range 49, x * mass massPk k x := by
  exact natFold_add 49 (fun x => x * mass massPk k x)

theorem massAbove_eq (massPk k g : ℕ) : massAbove massPk k g = ∑ x ∈ Finset.Ioc g 48, mass massPk k x := by
  have hI : Finset.Ioc g 48 = Finset.Ico (g + 1) 49 := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  calc massAbove massPk k g = ∑ i ∈ Finset.range (48 - g), mass massPk k (g + 1 + i) :=
        natFold_add (48 - g) (fun i => mass massPk k (g + 1 + i))
    _ = ∑ x ∈ Finset.Ioc g 48, mass massPk k x := by
        rw [hI, Finset.sum_Ico_eq_sum_range, show 49 - (g + 1) = 48 - g by omega]

section Masses

variable (massPk : ℕ) (W : ℕ → ℕ → ℝ) (hW : ∀ k, 1 ≤ k → k ≤ 32 → ∀ x ≤ 48,
  W k x = (((massPk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 : ℕ) : ℝ) / 2 ^ 62)

include hW

theorem eS_eq (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 32) : eS W 48 k = (massMean massPk k : ℝ) / 2 ^ 62 := by
  unfold eS
  rw [massMean_eq, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hW k hk1 hk x (by simp only [Finset.mem_range] at hx; omega), ← mass_eq]
  push_cast
  ring

theorem cS_eq (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 32) (g : ℕ) :
    cS W 48 k g = 1 - (massAbove massPk k g : ℝ) / 2 ^ 62 := by
  unfold cS
  rw [massAbove_eq, Nat.cast_sum, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hW k hk1 hk x (Finset.mem_Ioc.1 hx).2, ← mass_eq]

end Masses

theorem seed_M_le (k k' o E : ℕ) (h : (101 + k') * 2 ^ 62 ≤ o * (101 + k) * 2 ^ 10 + 3 * E) :
    (mu 100 k' - (E : ℝ) / 2 ^ 62) / mu 100 k ≤ (o : ℝ) / 2 ^ 52 := by
  have hmu : 0 < mu 100 k := by unfold mu; positivity
  rw [div_le_iff₀ hmu]
  have h' : ((101 + k' : ℕ) : ℝ) * 2 ^ 62 ≤ (o : ℝ) * (101 + k : ℕ) * 2 ^ 10 + 3 * E := by
    exact_mod_cast h
  unfold mu
  push_cast at h' ⊢
  linarith

theorem seed_R_le (o S : ℕ) (h : 2 ^ 62 ≤ o * 2 ^ 10 + S) : 1 - (S : ℝ) / 2 ^ 62 ≤ (o : ℝ) / 2 ^ 52 := by
  have h' : (2 : ℝ) ^ 62 ≤ (o : ℝ) * 2 ^ 10 + S := by exact_mod_cast h
  linarith

theorem D0_le (massPk D : ℕ) (W : ℕ → ℕ → ℝ) (hW : ∀ k, 1 ≤ k → k ≤ 32 → ∀ x ≤ 48,
    W k x = (((massPk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 : ℕ) : ℝ) / 2 ^ 62)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 32) (h : seedDef massPk D k = true) :
    D0 W 48 100 k / mu 100 k ≤ (slot 64 D k : ℝ) / 2 ^ 52 := by
  have hmu : 0 < mu 100 k := by unfold mu; positivity
  unfold seedDef at h
  simp only [Bool.or_eq_true, Nat.ble_eq, anyN_eq_true] at h
  rcases h with h1 | ⟨i, hi, hM⟩
  · refine one_le_of _ h1 _ ?_
    rw [div_le_one hmu]
    unfold D0
    exact (Finset.fold_min_le _).2 (Or.inl le_rfl)
  · have hle : D0 W 48 100 k ≤ mu 100 (i + 1) - eS W 48 (i + 1) := by
      unfold D0
      exact (Finset.fold_min_le _).2 (Or.inr ⟨i + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, le_rfl⟩)
    rw [eS_eq massPk W hW (i + 1) (by omega) (by omega)] at hle
    refine (div_le_div_of_nonneg_right hle hmu.le).trans (seed_M_le k (i + 1) _ _ ?_)
    simp only [shl_eq, Nat.add_eq, Nat.mul_eq] at hM
    exact hM

theorem preSeed_le_R (W : ℕ → ℕ → ℝ) (V m0 k g : ℕ) (prev : ℝ) :
    preSeed W V m0 k g prev ≤ if g < V then cS W V k g else 1 :=
  min_le_of_left_le (min_le_left _ _)

theorem preSeed_le_C (W : ℕ → ℕ → ℝ) (V m0 k g : ℕ) (prev : ℝ) :
    preSeed W V m0 k g prev ≤ binCdf k (1 / 3) g :=
  min_le_of_left_le (min_le_right _ _)

theorem preSeed_le_L (W : ℕ → ℕ → ℝ) (V m0 k g : ℕ) (prev : ℝ) :
    preSeed W V m0 k g prev ≤ L12 (D0 W V m0 k) (mu m0 k) g :=
  min_le_of_right_le (min_le_left _ _)

theorem preSeed_le_prev (W : ℕ → ℕ → ℝ) (V m0 k g : ℕ) (prev : ℝ) : preSeed W V m0 k g prev ≤ prev :=
  min_le_of_right_le (min_le_right _ _)

/-- **The seed check is sound.** -/
theorem seedCheck_sound (massPk : ℕ) (F : List ℕ) (D : ℕ) (hint : ℕ) (hc : K.seedCheck massPk F D hint = true)
    (W : ℕ → ℕ → ℝ) (hW : ∀ k, 1 ≤ k → k ≤ 32 → ∀ x ≤ 48,
      W k x = (((massPk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 : ℕ) : ℝ) / 2 ^ 62) :
    (seedState 48 100 96 W).Le P0 (decState F D) ∧ (decState F D).WF P0 := by
  simp only [K.seedCheck, Bool.and_eq_true, allN_eq_true] at hc
  obtain ⟨⟨hshape, hdef⟩, hrow⟩ := hc
  have hWF : (decState F D).WF P0 := shapeOK_sound P0 F D hshape
  have hmu : ∀ k, 0 < mu 100 k := fun k => by unfold mu; positivity
  have h52 : (0 : ℝ) < 2 ^ 52 := by positivity
  -- the deficits
  have hdelta : ∀ k ≤ 32, D0 W 48 100 k / mu 100 k ≤ (slot 64 D k : ℝ) / 2 ^ 52 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have h1 : D0 W 48 100 0 = mu 100 0 := by
        unfold D0
        rw [Finset.Icc_eq_empty (by norm_num), Finset.fold_empty]
      rw [h1, div_self (hmu 0).ne']
      exact le_of_eq hWF.2.2.2.2.symm
    · have hd := hdef (k - 1) (by omega)
      rw [show Nat.add (k - 1) 1 = k by simp only [Nat.add_eq]; omega] at hd
      exact D0_le massPk D W hW k hk1 hk hd
  refine ⟨⟨fun k hk g hg => ?_, fun k hk => hdelta k hk⟩, hWF⟩
  -- the cdf rows, by `rows_le`
  have hout0 : ∀ g ≤ 96, 1 ≤ (slot 64 (getN F 0) g : ℝ) / 2 ^ 52 :=
    fun g hg => le_of_eq (hWF.2.2.2.1 g hg).symm
  refine rows_le 32 96 (preSeed W 48 100) (F0 W 48 100 96) (fun _ => rfl) (fun _ _ => rfl)
    (fun k g x => preSeed_le_prev W 48 100 k g x) (fun k g => (slot 64 (getN F k) g : ℝ) / 2 ^ 52)
    hout0 ?_ k hk g hg
  intro k hk1 hk g hg
  have hr := hrow (k - 1) (by omega)
  rw [show Nat.add (k - 1) 1 = k by simp only [Nat.add_eq]; omega] at hr
  simp only [K.seedRow, allN_eq_true] at hr
  have he := hr g (by omega)
  simp only [K.seedEntry, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq,
    Nat.sub_eq] at he
  rcases he with ((((⟨hg', hn⟩ | hJ) | hone) | ⟨hg48, hR⟩) | hL) | hC
  · exact Or.inl ⟨hg', div_le_div_of_nonneg_right (by exact_mod_cast hn) h52.le⟩
  · exact Or.inr (Or.inl (div_le_div_of_nonneg_right (by exact_mod_cast hJ) h52.le))
  · refine Or.inr (Or.inr fun x => ?_)
    rw [show one52 = 1 * 2 ^ 52 from shl_eq 1 52, one_mul] at hone
    exact one_le_of _ (by rw [show one52 = 1 * 2 ^ 52 from shl_eq 1 52, one_mul]; exact hone) _
      ((preSeed_le_C W 48 100 k g x).trans (binCdf_le_one _ _ _ (by norm_num) (by norm_num)))
  · refine Or.inr (Or.inr fun x => ?_)
    rw [shl_eq, shl_eq, one_mul] at hR
    refine (preSeed_le_R W 48 100 k g x).trans ?_
    rw [ite_eq_left hg48, cS_eq massPk W hW k hk1 hk g]
    exact seed_R_le _ _ hR
  · refine Or.inr (Or.inr fun x => (preSeed_le_L W 48 100 k g x).trans ?_)
    have hm : mu 100 k = ((101 + k : ℕ) : ℝ) / 3 := by rw [mu_eq]
    rw [hm]
    refine lterm_sound (101 + k) (slot 64 D k) _ g _ _ ?_ hL
    rw [← hm, ← div_le_iff₀ (hmu k)]
    exact hdelta k hk
  · exact Or.inr (Or.inr fun x => (preSeed_le_C W 48 100 k g x).trans (cOK_sound _ _ _ hC))

end FrogModel.D3.LaneD
