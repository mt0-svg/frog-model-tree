module

public import FrogModel.D3.LaneC.LowerDefs
public import FrogModel.D3.LaneB.Tails

@[expose] public section

/-!
# The stage laws of the lower closures are monotone in the first answers

For the proof of Lemma 12.1 of the paper. A stage law `stageLaw cap pc pg pn R Rmax next` against an
antitone weight `φ ≥ 0` (`Vs`): nonincreasing in the number of frogs (`stage_mono`), and larger when
the pseudo-law `R` of the frogs a new child returns is smaller in the order of partial sums
(`stage_cmp`). Hence `lawS2` and `cdfS3` computed from a cdf bound `F ≥ F'` dominate those computed
from `F'` (`lawS2_cmp`, `cdfS3_cmp`), which lets the proof of Lemma 12.1 use the true cdf of
`G_m(1)`.
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC.Lower

theorem capShift_Vs (cap : ℕ) (hcap : 1 ≤ cap) (A φ : ℕ → ℝ) :
    Vs cap (capShift cap A) φ = Vs cap A (fun k => φ (min (k + 1) cap)) := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hcap
  -- hc : cap = 1 + c
  rw [hc, add_comm 1 c]
  -- Now cap = c + 1
  unfold Vs capShift
  dsimp
  rw [show c+1+1 = c+2 by omega]
  -- Goal: ∑ k ∈ range (c+2), (if k = 0 then 0 else if k < c+1 then A (k-1) else if k = c+1 then A c + A (c+1) else 0) * φ k
  --   = ∑ k ∈ range (c+2), A k * φ (min (k+1) (c+1))
  have h_left : (∑ k ∈ Finset.range (c+2), (if k = 0 then 0 else if k < c+1 then A (k-1) else if k = c+1 then A c + A (c+1) else 0) * φ k) =
      (∑ k ∈ Finset.range (c+1), A k * φ (k+1)) + A (c+1) * φ (c+1) := by
    rw [Finset.sum_range_succ']
    -- Goal: (∑ k ∈ range (c+1), (if (k+1) = 0 then 0 else if (k+1) < c+1 then A ((k+1)-1) else ...) * φ (k+1))
    --       + ((if 0 = 0 then 0 else ...) * φ 0) = RHS
    have h_first : ((if 0 = 0 then 0 else if 0 < c+1 then A (0-1) else if 0 = c+1 then A c + A (c+1) else 0) * φ 0) = 0 := by
      simp
    rw [h_first, add_zero]
    -- Goal: ∑ k ∈ range (c+1), (if k+1 = 0 then 0 else if k+1 < c+1 then A ((k+1)-1) else if k+1 = c+1 then A c + A (c+1) else 0) * φ (k+1)
    --     = ∑ k ∈ range (c+1), A k * φ (k+1) + A (c+1) * φ (c+1)
    rw [Finset.sum_range_succ]
    -- Goal: (∑ k ∈ range c, ...) + ((if c+1 = 0 then 0 else if c+1 < c+1 then A (c+1-1) else ...) * φ (c+1)) = RHS
    have h_sub : (c+1 : ℕ) - 1 = c := by omega
    rw [h_sub]
    have h_last : ((if c+1 = 0 then 0 else if c+1 < c+1 then A c else if c+1 = c+1 then A c + A (c+1) else 0) * φ (c+1)) =
        (A c + A (c+1)) * φ (c+1) := by
      simp
    rw [h_last]
    -- Goal: ∑ k ∈ range c, (if k+1 = 0 then 0 else if k+1 < c+1 then A ((k+1)-1) else if k+1 = c+1 then A c + A (c+1) else 0) * φ (k+1)
    --     + (A c + A (c+1)) * φ (c+1) = (∑ k ∈ range (c+1), A k * φ (k+1)) + A (c+1) * φ (c+1)
    have h_sum : (∑ k ∈ Finset.range c, (if k+1 = 0 then 0 else if k+1 < c+1 then A ((k+1)-1) else if k+1 = c+1 then A c + A (c+1) else 0) * φ (k+1)) =
        (∑ k ∈ Finset.range c, A k * φ (k+1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hk_lt_c : k < c := hk
      have hk1_lt_c1 : k+1 < c+1 := by omega
      have hk1_sub : (k+1 : ℕ) - 1 = k := by omega
      simp [hk1_lt_c1, hk1_sub]
    rw [h_sum]
    rw [Finset.sum_range_succ]
    ring
  have h_right : (∑ k ∈ Finset.range (c+2), A k * φ (min (k+1) (c+1))) =
      (∑ k ∈ Finset.range (c+1), A k * φ (k+1)) + A (c+1) * φ (c+1) := by
    rw [Finset.sum_range_succ]
    have h_last : A (c+1) * φ (min ((c+1)+1) (c+1)) = A (c+1) * φ (c+1) := by
      simp
    rw [h_last]
    -- Goal: (∑ k ∈ range (c+1), A k * φ (min (k+1) (c+1))) + A (c+1) * φ (c+1) = (∑ k ∈ range (c+1), A k * φ (k+1)) + A (c+1) * φ (c+1)
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le_c : k ≤ c := by omega
    have h_min : min (k+1) (c+1) = k+1 := by omega
    rw [h_min]
  rw [h_left, h_right]

theorem Vs_stage_zero (cap : ℕ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ) (next : ℕ → ℕ → ℝ)
    (φ : ℕ → ℝ) : Vs cap (stageLaw cap pc pg pn R Rmax next 0) φ = φ 0 := by
  unfold Vs
  rw [Finset.sum_eq_single 0]
  · simp [stageLaw]
  · intro k _ hk
    simp [stageLaw, hk]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos cap)) h

/-- One stage step against a weight: linearity of `Vs` in the table. -/
theorem Vs_stage (cap : ℕ) (hcap : 1 ≤ cap) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ)
    (next : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (y : ℕ) :
    Vs cap (stageLaw cap pc pg pn R Rmax next (y + 1)) φ =
      pc * Vs cap (stageLaw cap pc pg pn R Rmax next y) (fun k => φ (min (k + 1) cap)) +
        pg * Vs cap (stageLaw cap pc pg pn R Rmax next y) φ +
        pn * ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (y + r)) φ := by
  rw [← capShift_Vs cap hcap]
  have e3 : ∑ k ∈ Finset.range (cap + 1),
      (pn * ∑ r ∈ Finset.range (Rmax + 1), R r * next (y + r) k) * φ k =
      pn * ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (y + r)) φ := by
    unfold Vs
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [← e3]
  unfold Vs
  simp only [stageLaw, add_mul, Finset.sum_add_distrib]
  congr 1
  congr 1
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

theorem stage_mono (cap : ℕ) (hcap : 1 ≤ cap) (pc pg pn : ℝ) (hpc : 0 ≤ pc) (hpg : 0 ≤ pg)
    (hpn : 0 ≤ pn) (hp : pc + pg + pn = 1) (R : ℕ → ℝ) (Rmax : ℕ) (hR : ∀ r, 0 ≤ R r)
    (hR1 : ∑ r ∈ Finset.range (Rmax + 1), R r ≤ 1) (next : ℕ → ℕ → ℝ)
    (hmono : ∀ φ : ℕ → ℝ, Antitone φ → (∀ k, 0 ≤ φ k) → ∀ y,
      Vs cap (next (y + 1)) φ ≤ Vs cap (next y) φ)
    (htop : ∀ φ : ℕ → ℝ, Antitone φ → (∀ k, 0 ≤ φ k) → ∀ y, Vs cap (next y) φ ≤ φ 0)
    (φ : ℕ → ℝ) (hφ : Antitone φ) (hφ0 : ∀ k, 0 ≤ φ k) (y : ℕ) :
    Vs cap (stageLaw cap pc pg pn R Rmax next (y + 1)) φ ≤
        Vs cap (stageLaw cap pc pg pn R Rmax next y) φ ∧
      Vs cap (stageLaw cap pc pg pn R Rmax next y) φ ≤ φ 0 := by
  induction y generalizing φ with
  | zero =>
    refine ⟨?_, (Vs_stage_zero cap pc pg pn R Rmax next φ).le⟩
    rw [Vs_stage cap hcap pc pg pn R Rmax next φ 0]
    simp only [Vs_stage_zero]
    have h1 : φ (min (0 + 1) cap) ≤ φ 0 := hφ (Nat.zero_le _)
    have h2 : ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (0 + r)) φ ≤ φ 0 := by
      calc ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (0 + r)) φ
          ≤ ∑ r ∈ Finset.range (Rmax + 1), R r * φ 0 :=
            Finset.sum_le_sum fun r _ =>
              mul_le_mul_of_nonneg_left (htop φ hφ hφ0 _) (hR r)
        _ = (∑ r ∈ Finset.range (Rmax + 1), R r) * φ 0 := by rw [Finset.sum_mul]
        _ ≤ 1 * φ 0 := mul_le_mul_of_nonneg_right hR1 (hφ0 0)
        _ = φ 0 := one_mul _
    have h3 := mul_le_mul_of_nonneg_left h1 hpc
    have h4 := mul_le_mul_of_nonneg_left h2 hpn
    have h5 : pc * φ 0 + pg * φ 0 + pn * φ 0 = φ 0 := by
      rw [← add_mul, ← add_mul, hp, one_mul]
    linarith
  | succ y ih =>
    have hplus : Antitone fun k => φ (min (k + 1) cap) :=
      fun a b hab => hφ (min_le_min_right _ (by omega))
    have hplus0 : ∀ k, 0 ≤ φ (min (k + 1) cap) := fun k => hφ0 _
    obtain ⟨ihφ1, ihφ2⟩ := ih φ hφ hφ0
    obtain ⟨ihp1, _⟩ := ih _ hplus hplus0
    refine ⟨?_, ihφ1.trans ihφ2⟩
    rw [Vs_stage cap hcap pc pg pn R Rmax next φ (y + 1)]
    conv_rhs => rw [Vs_stage cap hcap pc pg pn R Rmax next φ y]
    have h3 : ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (y + 1 + r)) φ ≤
        ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (y + r)) φ :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
        (by rw [show y + 1 + r = (y + r) + 1 by ring]; exact hmono φ hφ hφ0 _) (hR r)
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left ihp1 hpc)
      (mul_le_mul_of_nonneg_left ihφ1 hpg)) (mul_le_mul_of_nonneg_left h3 hpn)

theorem stage_cmp (cap : ℕ) (hcap : 1 ≤ cap) (pc pg pn : ℝ) (hpc : 0 ≤ pc) (hpg : 0 ≤ pg)
    (hpn : 0 ≤ pn) (R R' : ℕ → ℝ) (Rmax : ℕ) (hR : ∀ r, 0 ≤ R r) (_hR' : ∀ r, 0 ≤ R' r)
    (hcum : ∀ t < Rmax + 1, ∑ r ∈ Finset.range (t + 1), R' r ≤ ∑ r ∈ Finset.range (t + 1), R r)
    (next next' : ℕ → ℕ → ℝ) (hn' : ∀ y k, 0 ≤ next' y k)
    (hcmp : ∀ φ : ℕ → ℝ, Antitone φ → (∀ k, 0 ≤ φ k) → ∀ y,
      Vs cap (next' y) φ ≤ Vs cap (next y) φ)
    (hmono' : ∀ φ : ℕ → ℝ, Antitone φ → (∀ k, 0 ≤ φ k) → ∀ y,
      Vs cap (next' (y + 1)) φ ≤ Vs cap (next' y) φ)
    (φ : ℕ → ℝ) (hφ : Antitone φ) (hφ0 : ∀ k, 0 ≤ φ k) (y : ℕ) :
    Vs cap (stageLaw cap pc pg pn R' Rmax next' y) φ ≤ Vs cap (stageLaw cap pc pg pn R Rmax next y) φ := by
  induction y generalizing φ with
  | zero => rw [Vs_stage_zero, Vs_stage_zero]
  | succ y ih =>
    have hplus : Antitone fun k => φ (min (k + 1) cap) :=
      fun a b hab => hφ (min_le_min_right _ (by omega))
    have hplus0 : ∀ k, 0 ≤ φ (min (k + 1) cap) := fun k => hφ0 _
    rw [Vs_stage cap hcap pc pg pn R' Rmax next' φ y, Vs_stage cap hcap pc pg pn R Rmax next φ y]
    have a1 := ih _ hplus hplus0
    have a2 := ih φ hφ hφ0
    have hw : ∀ s, Vs cap (next' (y + (s + 1))) φ ≤ Vs cap (next' (y + s)) φ := fun s => by
      rw [show y + (s + 1) = (y + s) + 1 by ring]; exact hmono' φ hφ hφ0 _
    have hw0 : ∀ s, 0 ≤ Vs cap (next' (y + s)) φ := fun s =>
      Finset.sum_nonneg fun k _ => mul_nonneg (hn' _ k) (hφ0 k)
    have hab := abel_mono (fun r => Vs cap (next' (y + r)) φ) R' R (Rmax + 1) hw hw0 hcum
    have a3 : ∑ r ∈ Finset.range (Rmax + 1), R' r * Vs cap (next' (y + r)) φ ≤
        ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (y + r)) φ := by
      calc ∑ r ∈ Finset.range (Rmax + 1), R' r * Vs cap (next' (y + r)) φ
          = ∑ r ∈ Finset.range (Rmax + 1), Vs cap (next' (y + r)) φ * R' r :=
            Finset.sum_congr rfl fun r _ => mul_comm _ _
        _ ≤ ∑ r ∈ Finset.range (Rmax + 1), Vs cap (next' (y + r)) φ * R r := hab
        _ = ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next' (y + r)) φ :=
            Finset.sum_congr rfl fun r _ => mul_comm _ _
        _ ≤ ∑ r ∈ Finset.range (Rmax + 1), R r * Vs cap (next (y + r)) φ :=
            Finset.sum_le_sum fun r _ =>
              mul_le_mul_of_nonneg_left (hcmp φ hφ hφ0 _) (hR r)
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left a1 hpc)
      (mul_le_mul_of_nonneg_left a2 hpg)) (mul_le_mul_of_nonneg_left a3 hpn)

theorem plR_cum (F : ℕ → ℝ) (GM g : ℕ) : ∑ r ∈ Finset.range (g + 1), plR F GM r = Ftil F GM g := by
  induction' g with g ih
  · simp [plR, Ftil]
  · rw [Finset.sum_range_succ, ih]
    unfold plR Ftil
    by_cases hzero : g + 1 = 0
    · exact (Nat.succ_ne_zero _ hzero).elim
    · simp
      by_cases hg : g ≤ GM
      · by_cases hg_lt : g < GM
        · simp [hg, hg_lt]
        · have h_eq : g = GM := by omega
          subst h_eq
          simp
      · by_cases hg_lt : g < GM
        · omega
        · simp [hg, hg_lt]

theorem plR_nonneg2 (F1 : ℕ → ℝ) (GM : ℕ) (hmono : ∀ g < GM, F1 g ≤ F1 (g + 1))
    (h01 : ∀ g ≤ GM, 0 ≤ F1 g ∧ F1 g ≤ 1) (r : ℕ) : 0 ≤ plR F1 GM r := by
  dsimp [plR, Ftil]
  by_cases h0 : r = 0
  · subst h0
    simp
    rcases h01 0 (Nat.zero_le GM) with ⟨h, _⟩
    exact h
  · simp [h0]
    by_cases hle : r ≤ GM + 1
    · simp [hle]
      by_cases hrgm : r ≤ GM
      · simp [hrgm]
        have hrsub : r - 1 ≤ GM := by omega
        simp
        have hmono' := hmono (r - 1) (by omega)
        have h_eq : (r - 1 : ℕ) + 1 = r := by omega
        rw [h_eq] at hmono'
        linarith
      · simp [hrgm]
        have heq : r = GM + 1 := by omega
        subst heq
        rcases h01 GM (le_refl GM) with ⟨_, hle1⟩
        simp
        linarith
    · simp [hle]

theorem stageLaw_nonneg2 (cap : ℕ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ)
    (next : ℕ → ℕ → ℝ) (hpc : 0 ≤ pc) (hpg : 0 ≤ pg) (hpn : 0 ≤ pn) (hR : ∀ r, 0 ≤ R r)
    (hnext : ∀ y k, 0 ≤ next y k) (y k : ℕ) : 0 ≤ stageLaw cap pc pg pn R Rmax next y k := by
  induction' y with y IH generalizing k
  · -- y = 0
    unfold stageLaw
    split <;> norm_num
  · -- y + 1
    unfold stageLaw
    have hcapShift : 0 ≤ capShift cap (stageLaw cap pc pg pn R Rmax next y) k := by
      unfold capShift
      split
      · norm_num
      · rename_i hk0
        split
        · exact IH (k - 1)
        · split
          · rename_i hk_eq_cap
            have h1 : 0 ≤ stageLaw cap pc pg pn R Rmax next y (cap - 1) := IH (cap - 1)
            have h2 : 0 ≤ stageLaw cap pc pg pn R Rmax next y cap := IH cap
            nlinarith
          · norm_num
    have hsum : 0 ≤ ∑ r ∈ Finset.range (Rmax + 1), R r * next (y + r) k :=
      Finset.sum_nonneg fun r _ => mul_nonneg (hR r) (hnext (y + r) k)
    have h1 : 0 ≤ pc * capShift cap (stageLaw cap pc pg pn R Rmax next y) k :=
      mul_nonneg hpc hcapShift
    have h2 : 0 ≤ pg * stageLaw cap pc pg pn R Rmax next y k :=
      mul_nonneg hpg (IH k)
    have h3 : 0 ≤ pn * ∑ r ∈ Finset.range (Rmax + 1), R r * next (y + r) k :=
      mul_nonneg hpn hsum
    nlinarith

theorem lawS2_cmp (GM E q : ℕ) (hE : 1 ≤ E) (F F' : ℕ → ℝ) (hFF : ∀ g ≤ GM, F' g ≤ F g)
    (hmono : ∀ g < GM, F g ≤ F (g + 1)) (h01 : ∀ g ≤ GM, 0 ≤ F g ∧ F g ≤ 1)
    (hmono' : ∀ g < GM, F' g ≤ F' (g + 1)) (h01' : ∀ g ≤ GM, 0 ≤ F' g ∧ F' g ≤ 1)
    (φ : ℕ → ℝ) (hφ : Antitone φ) (hφ0 : ∀ k, 0 ≤ φ k) :
    Vs E (lawS2 GM E F' q) φ ≤ Vs E (lawS2 GM E F q) φ := by
  set R := plR F GM with hRdef
  set R' := plR F' GM with hR'def
  have hR0 : ∀ r, 0 ≤ R r := plR_nonneg2 F GM hmono h01
  have hR'0 : ∀ r, 0 ≤ R' r := plR_nonneg2 F' GM hmono' h01'
  have hR'1 : ∑ r ∈ Finset.range (GM + 1 + 1), R' r ≤ 1 := by
    rw [hR'def, plR_cum]
    unfold Ftil
    simp
  have hcum : ∀ t < GM + 1 + 1,
      ∑ r ∈ Finset.range (t + 1), R' r ≤ ∑ r ∈ Finset.range (t + 1), R r := by
    intro t ht
    rw [hRdef, hR'def, plR_cum, plR_cum]
    unfold Ftil
    by_cases hle : t ≤ GM
    · simp only [hle, ite_true]
      exact hFF t hle
    · simp only [hle, ite_false, le_refl]
  set f0 : ℕ → ℕ → ℝ := fun _ _ => 0 with hf0def
  have hf0y : ∀ (ψ : ℕ → ℝ) (y : ℕ), Vs E (f0 y) ψ = 0 := fun ψ y => by simp [Vs, f0]
  set s2 := stageLaw E (3 / 10 : ℝ) (7 / 10 : ℝ) 0 R (GM + 1) f0 with hs2def
  set s2' := stageLaw E (3 / 10 : ℝ) (7 / 10 : ℝ) 0 R' (GM + 1) f0 with hs2'def
  set s1 := stageLaw E (3 / 11 : ℝ) (5 / 11 : ℝ) (3 / 11 : ℝ) R (GM + 1) s2 with hs1def
  set s1' := stageLaw E (3 / 11 : ℝ) (5 / 11 : ℝ) (3 / 11 : ℝ) R' (GM + 1) s2' with hs1'def
  -- the last stage
  have c2 : ∀ ψ : ℕ → ℝ, Antitone ψ → (∀ k, 0 ≤ ψ k) → ∀ y, Vs E (s2' y) ψ ≤ Vs E (s2 y) ψ :=
    fun ψ hψ hψ0 y => stage_cmp E hE _ _ _ (by norm_num) (by norm_num) le_rfl R R' (GM + 1)
      hR0 hR'0 hcum f0 f0 (fun _ _ => le_rfl) (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
      ψ hψ hψ0 y
  have m2 : ∀ ψ : ℕ → ℝ, Antitone ψ → (∀ k, 0 ≤ ψ k) → ∀ y,
      Vs E (s2' (y + 1)) ψ ≤ Vs E (s2' y) ψ ∧ Vs E (s2' y) ψ ≤ ψ 0 :=
    fun ψ hψ hψ0 y => stage_mono E hE _ _ _ (by norm_num) (by norm_num) le_rfl (by norm_num) R'
      (GM + 1) hR'0 hR'1 f0 (fun ψ' _ _ y' => by simp only [hf0y, le_refl])
      (fun ψ' _ hψ'0 y' => by rw [hf0y ψ' y']; exact hψ'0 0) ψ hψ hψ0 y
  have n2' : ∀ y k, 0 ≤ s2' y k := fun y k =>
    stageLaw_nonneg2 E _ _ _ R' (GM + 1) f0 (by norm_num) (by norm_num) le_rfl hR'0
      (fun _ _ => le_rfl) y k
  -- the middle stage
  have c1 : ∀ ψ : ℕ → ℝ, Antitone ψ → (∀ k, 0 ≤ ψ k) → ∀ y, Vs E (s1' y) ψ ≤ Vs E (s1 y) ψ :=
    fun ψ hψ hψ0 y => stage_cmp E hE _ _ _ (by norm_num) (by norm_num) (by norm_num) R R'
      (GM + 1) hR0 hR'0 hcum s2 s2' n2' c2 (fun ψ' hψ' hψ'0 y' => (m2 ψ' hψ' hψ'0 y').1)
      ψ hψ hψ0 y
  have m1 : ∀ ψ : ℕ → ℝ, Antitone ψ → (∀ k, 0 ≤ ψ k) → ∀ y,
      Vs E (s1' (y + 1)) ψ ≤ Vs E (s1' y) ψ ∧ Vs E (s1' y) ψ ≤ ψ 0 :=
    fun ψ hψ hψ0 y => stage_mono E hE _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) R' (GM + 1) hR'0 hR'1 s2' (fun ψ' hψ' hψ'0 y' => (m2 ψ' hψ' hψ'0 y').1)
      (fun ψ' hψ' hψ'0 y' => (m2 ψ' hψ' hψ'0 y').2) ψ hψ hψ0 y
  have n1' : ∀ y k, 0 ≤ s1' y k := fun y k =>
    stageLaw_nonneg2 E _ _ _ R' (GM + 1) s2' (by norm_num) (by norm_num) (by norm_num) hR'0
      n2' y k
  -- the first stage
  simp only [lawS2]
  exact stage_cmp E hE _ _ _ (by norm_num) (by norm_num) (by norm_num) R R' (GM + 1) hR0 hR'0
    hcum s1 s1' n1' c1 (fun ψ' hψ' hψ'0 y' => (m1 ψ' hψ' hψ'0 y').1) φ hφ hφ0 q

theorem cdfS3_cmp (GM q v : ℕ) (hv : v ≤ GM) (F F' : ℕ → ℝ) (hFF : ∀ g ≤ GM, F' g ≤ F g)
    (hmono : ∀ g < GM, F g ≤ F (g + 1)) (h01 : ∀ g ≤ GM, 0 ≤ F g ∧ F g ≤ 1)
    (hmono' : ∀ g < GM, F' g ≤ F' (g + 1)) (h01' : ∀ g ≤ GM, 0 ≤ F' g ∧ F' g ≤ 1) :
    cdfS3 GM F' q v ≤ cdfS3 GM F q v := by
  -- Express cdfS3 as Vs with indicator
  have hcdf_eq (F1 : ℕ → ℝ) (GM' q' v' : ℕ) (hv' : v' ≤ GM') : cdfS3 GM' F1 q' v' = Vs (GM' + 1) (lawS3 GM' F1 q') (fun x => if x ≤ v' then 1 else 0) := by
    dsimp [cdfS3, Vs]
    have hfilter : (Finset.range (GM' + 2)).filter (· ≤ v') = Finset.range (v' + 1) := by
      ext x; simp; omega
    calc
      ∑ x ∈ Finset.range (v' + 1), lawS3 GM' F1 q' x
          = ∑ x ∈ (Finset.range (GM' + 2)).filter (· ≤ v'), lawS3 GM' F1 q' x := by rw [hfilter]
      _ = ∑ x ∈ Finset.range (GM' + 2), (if x ≤ v' then lawS3 GM' F1 q' x else 0) := by rw [Finset.sum_filter]
      _ = ∑ x ∈ Finset.range (GM' + 2), (lawS3 GM' F1 q' x * (if x ≤ v' then 1 else 0)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : x ≤ v'
        · simp [hx, mul_comm]
        · simp [hx]
      _ = ∑ x ∈ Finset.range (GM' + 1 + 1), lawS3 GM' F1 q' x * (if x ≤ v' then 1 else 0) := by
        simp [show GM' + 2 = GM' + 1 + 1 by omega]
  let φ : ℕ → ℝ := fun x => if x ≤ v then 1 else 0
  have hφ_anti : Antitone φ := by
    intro a b h
    dsimp [φ]
    by_cases hb : b ≤ v
    · have ha : a ≤ v := le_trans h hb
      simp [ha, hb]
    · by_cases ha : a ≤ v
      · simp [ha, hb]
      · simp [ha, hb]
  have hφ_nonneg : ∀ k, 0 ≤ φ k := by
    intro k; dsimp [φ]; split <;> norm_num
  rw [hcdf_eq F' GM q v hv, hcdf_eq F GM q v hv]
  -- Abbreviations for the pseudo-laws
  let R := plR F GM
  let R' := plR F' GM
  have hR : ∀ r, 0 ≤ R r := plR_nonneg2 F GM hmono h01
  have hR' : ∀ r, 0 ≤ R' r := plR_nonneg2 F' GM hmono' h01'
  -- Cumulative comparison for plR
  have hcum : ∀ t < GM + 2, ∑ r ∈ Finset.range (t + 1), R' r ≤ ∑ r ∈ Finset.range (t + 1), R r := by
    intro t ht
    rw [plR_cum F' GM t, plR_cum F GM t]
    dsimp [Ftil]
    by_cases h : t ≤ GM
    · have hF' := hFF t h
      simp [h, hF']
    · have hnot : ¬ t ≤ GM := h
      simp [hnot]
  have hR1 : ∑ r ∈ Finset.range (GM + 2), R r ≤ 1 := by
    rw [plR_cum F GM (GM + 1)]
    dsimp [Ftil]
    have hnot : ¬ GM + 1 ≤ GM := by omega
    simp [hnot]
  have hR1' : ∑ r ∈ Finset.range (GM + 2), R' r ≤ 1 := by
    rw [plR_cum F' GM (GM + 1)]
    dsimp [Ftil]
    have hnot : ¬ GM + 1 ≤ GM := by omega
    simp [hnot]
  have hcap : 1 ≤ GM + 1 := by omega
  -- Define the stage laws
  let t3 := stageLaw (GM + 1) (1 / 3) (2 / 3) 0 R (GM + 1) (fun _ _ => 0)
  let t3' := stageLaw (GM + 1) (1 / 3) (2 / 3) 0 R' (GM + 1) (fun _ _ => 0)
  let t2 := stageLaw (GM + 1) (3 / 10) (4 / 10) (3 / 10) R (GM + 1) t3
  let t2' := stageLaw (GM + 1) (3 / 10) (4 / 10) (3 / 10) R' (GM + 1) t3'
  let t1 := stageLaw (GM + 1) (3 / 11) (2 / 11) (6 / 11) R (GM + 1) t2
  let t1' := stageLaw (GM + 1) (3 / 11) (2 / 11) (6 / 11) R' (GM + 1) t2'
  let t0 := stageLaw (GM + 1) (1 / 4) 0 (3 / 4) R (GM + 1) t1
  let t0' := stageLaw (GM + 1) (1 / 4) 0 (3 / 4) R' (GM + 1) t1'
  -- Nonnegativity of stage laws (for F' side)
  have h_t3'_nonneg : ∀ y k, 0 ≤ t3' y k := by
    intro y k
    apply stageLaw_nonneg2 (GM + 1) (1/3) (2/3) 0 R' (GM + 1) (fun _ _ => 0)
      (by norm_num) (by norm_num) (by norm_num) hR' (fun y k => by norm_num) y k
  have h_t2'_nonneg : ∀ y k, 0 ≤ t2' y k := by
    intro y k
    apply stageLaw_nonneg2 (GM + 1) (3/10) (4/10) (3/10) R' (GM + 1) t3'
      (by norm_num) (by norm_num) (by norm_num) hR' h_t3'_nonneg y k
  have h_t1'_nonneg : ∀ y k, 0 ≤ t1' y k := by
    intro y k
    apply stageLaw_nonneg2 (GM + 1) (3/11) (2/11) (6/11) R' (GM + 1) t2'
      (by norm_num) (by norm_num) (by norm_num) hR' h_t2'_nonneg y k
  -- stage_mono gives both monotonicity and the top bound (Vs ... ≤ φ 0)
  have h_t3_stage (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t3' (y' + 1)) φ' ≤ Vs (GM + 1) (t3' y') φ' ∧ Vs (GM + 1) (t3' y') φ' ≤ φ' 0 := by
    refine stage_mono (GM + 1) hcap (1/3) (2/3) 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) R' (GM + 1) hR' hR1' (fun _ _ => 0)
      (by intro φ'' hφ''_anti hφ''_nonneg y''; simp [Vs])
      (by intro φ'' hφ''_anti hφ''_nonneg y''; simp [Vs]; exact hφ''_nonneg 0)
      φ' hφ'_anti hφ'_nonneg y'
  have h_t3_mono (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t3' (y' + 1)) φ' ≤ Vs (GM + 1) (t3' y') φ' :=
    (h_t3_stage φ' hφ'_anti hφ'_nonneg y').1
  have h_t3_top (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t3' y') φ' ≤ φ' 0 :=
    (h_t3_stage φ' hφ'_anti hφ'_nonneg y').2

  have h_t2_stage (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t2' (y' + 1)) φ' ≤ Vs (GM + 1) (t2' y') φ' ∧ Vs (GM + 1) (t2' y') φ' ≤ φ' 0 := by
    refine stage_mono (GM + 1) hcap (3/10) (4/10) (3/10) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) R' (GM + 1) hR' hR1' t3' h_t3_mono h_t3_top φ' hφ'_anti hφ'_nonneg y'
  have h_t2_mono (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t2' (y' + 1)) φ' ≤ Vs (GM + 1) (t2' y') φ' :=
    (h_t2_stage φ' hφ'_anti hφ'_nonneg y').1
  have h_t2_top (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t2' y') φ' ≤ φ' 0 :=
    (h_t2_stage φ' hφ'_anti hφ'_nonneg y').2

  have h_t1_stage (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t1' (y' + 1)) φ' ≤ Vs (GM + 1) (t1' y') φ' ∧ Vs (GM + 1) (t1' y') φ' ≤ φ' 0 := by
    refine stage_mono (GM + 1) hcap (3/11) (2/11) (6/11) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) R' (GM + 1) hR' hR1' t2' h_t2_mono h_t2_top φ' hφ'_anti hφ'_nonneg y'
  have h_t1_mono (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t1' (y' + 1)) φ' ≤ Vs (GM + 1) (t1' y') φ' :=
    (h_t1_stage φ' hφ'_anti hφ'_nonneg y').1
  have h_t1_top (φ' : ℕ → ℝ) (hφ'_anti : Antitone φ') (hφ'_nonneg : ∀ k, 0 ≤ φ' k) (y' : ℕ) :
      Vs (GM + 1) (t1' y') φ' ≤ φ' 0 :=
    (h_t1_stage φ' hφ'_anti hφ'_nonneg y').2
  -- Base comparison for t3 (next = next' = 0)
  have h_t3_cmp : ∀ (φ' : ℕ → ℝ), Antitone φ' → (∀ k, 0 ≤ φ' k) → ∀ y,
      Vs (GM + 1) (t3' y) φ' ≤ Vs (GM + 1) (t3 y) φ' := by
    intro φ' hφ'_anti hφ'_nonneg y'
    apply stage_cmp (GM + 1) hcap (1/3) (2/3) 0 (by norm_num) (by norm_num) (by norm_num)
      R R' (GM + 1) hR hR' hcum
      (fun _ _ => 0) (fun _ _ => 0) (fun y k => by norm_num)
      (by
        intro φ'' hφ''_anti hφ''_nonneg y''
        simp [Vs])
      (by
        intro φ'' hφ''_anti hφ''_nonneg y''
        simp [Vs])
      φ' hφ'_anti hφ'_nonneg y'
  -- t2 comparison (using t3 comparison as hcmp)
  have h_t2_cmp : ∀ (φ' : ℕ → ℝ), Antitone φ' → (∀ k, 0 ≤ φ' k) → ∀ y,
      Vs (GM + 1) (t2' y) φ' ≤ Vs (GM + 1) (t2 y) φ' := by
    intro φ' hφ'_anti hφ'_nonneg y'
    apply stage_cmp (GM + 1) hcap (3/10) (4/10) (3/10) (by norm_num) (by norm_num) (by norm_num)
      R R' (GM + 1) hR hR' hcum
      t3 t3' h_t3'_nonneg
      h_t3_cmp
      h_t3_mono
      φ' hφ'_anti hφ'_nonneg y'
  -- t1 comparison (using t2 comparison as hcmp)
  have h_t1_cmp : ∀ (φ' : ℕ → ℝ), Antitone φ' → (∀ k, 0 ≤ φ' k) → ∀ y,
      Vs (GM + 1) (t1' y) φ' ≤ Vs (GM + 1) (t1 y) φ' := by
    intro φ' hφ'_anti hφ'_nonneg y'
    apply stage_cmp (GM + 1) hcap (3/11) (2/11) (6/11) (by norm_num) (by norm_num) (by norm_num)
      R R' (GM + 1) hR hR' hcum
      t2 t2' h_t2'_nonneg
      h_t2_cmp
      h_t2_mono
      φ' hφ'_anti hφ'_nonneg y'
  -- t0 (outermost) comparison
  have h_t0_cmp : Vs (GM + 1) (t0' q) φ ≤ Vs (GM + 1) (t0 q) φ := by
    apply stage_cmp (GM + 1) hcap (1/4) 0 (3/4) (by norm_num) (by norm_num) (by norm_num)
      R R' (GM + 1) hR hR' hcum
      t1 t1' h_t1'_nonneg
      h_t1_cmp
      h_t1_mono
      φ hφ_anti hφ_nonneg q
  -- Relate lawS3 to the stage law definitions
  simpa [lawS3, t0, t1, t2, t3, t0', t1', t2', t3'] using h_t0_cmp

end FrogModel.D3.LaneC.Lower
