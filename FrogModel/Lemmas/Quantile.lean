module

public import FrogModel.Lemmas.Defs

@[expose] public section

/-!
# The quantile coupling (proof of Theorem 6.5 of the paper)

Two measures of equal finite mass on `ℕ∞`, the second dominating the first in the tails, are the
marginals of a measure on pairs `x ≤ y`: `Order.quantile_coupling`. The coupling is the overlap of
the intervals `[F x, F x + μ x)` of the cumulative masses (`cumBelow`) under Lebesgue measure.
-/

open MeasureTheory
open scoped ENNReal
open FrogModel

theorem FrogModel.Order.cumBelow_mono (μ : ℕ∞ → ℝ≥0∞) : Monotone (FrogModel.Order.cumBelow μ) := by
  intro x y hxy
  unfold FrogModel.Order.cumBelow
  refine ENNReal.tsum_le_tsum fun z => ?_
  split_ifs with hzx hzy
  · rfl
  · exfalso; exact hzy (lt_of_lt_of_le hzx hxy)
  · apply zero_le
  · rfl

theorem FrogModel.Order.cumBelow_add_le (μ : ℕ∞ → ℝ≥0∞) (x y : ℕ∞) (hxy : x < y) :
    FrogModel.Order.cumBelow μ x + μ x ≤ FrogModel.Order.cumBelow μ y := by
  dsimp [FrogModel.Order.cumBelow]
  have hμx : μ x = ∑' z, (if z = x then μ z else 0) := by
    rw [tsum_ite_eq]
  rw [hμx]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro z
  by_cases hzx : z < x
  · have hzy : z < y := lt_trans hzx hxy
    simp [hzx, hzy, ne_of_lt hzx]
  · simp [hzx]
    by_cases hzx_eq : z = x
    · subst hzx_eq
      simp [hxy]
    · simp [hzx_eq]

theorem FrogModel.Order.cumBelow_succ (μ : ℕ∞ → ℝ≥0∞) (n : ℕ) :
    FrogModel.Order.cumBelow μ ((n + 1 : ℕ) : ℕ∞) = FrogModel.Order.cumBelow μ n + μ n := by
  have h_cond (z : ℕ∞) : z < ((n + 1 : ℕ) : ℕ∞) ↔ z < (n : ℕ∞) ∨ z = (n : ℕ∞) := by
    have h_cast : ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by simp
    rw [h_cast]
    constructor
    · intro h
      have hle : z ≤ (n : ℕ∞) := (ENat.lt_natCast_add_one_iff (n := n)).mp h
      rcases le_iff_lt_or_eq.mp hle with (hlt' | heq')
      · exact Or.inl hlt'
      · exact Or.inr heq'
    · intro h
      rcases h with (hlt' | heq')
      · have hle : z ≤ (n : ℕ∞) := le_of_lt hlt'
        exact (ENat.lt_natCast_add_one_iff (n := n)).mpr hle
      · rw [heq']
        exact ENat.natCast_lt_succ (n := n)
  have h_summand (z : ℕ∞) : (if z < ((n + 1 : ℕ) : ℕ∞) then μ z else 0) =
      ((if z < (n : ℕ∞) then μ z else 0) + (if z = (n : ℕ∞) then μ z else 0)) := by
    by_cases hlt : z < (n : ℕ∞)
    · have heq : z ≠ (n : ℕ∞) := by
        intro heq; rw [heq] at hlt; exact lt_irrefl _ hlt
      have hlt_succ : z < ((n + 1 : ℕ) : ℕ∞) := (h_cond z).mpr (Or.inl hlt)
      rw [ite_eq_left hlt_succ, ite_eq_left hlt, ite_eq_right heq]
      simp
    · by_cases heq : z = (n : ℕ∞)
      · have hlt_succ : z < ((n + 1 : ℕ) : ℕ∞) := (h_cond z).mpr (Or.inr heq)
        rw [ite_eq_left hlt_succ, ite_eq_right hlt, ite_eq_left heq]
        simp
      · have hlt_succ : ¬ z < ((n + 1 : ℕ) : ℕ∞) := by
          intro h; rcases (h_cond z).mp h with (h' | h')
          · exact hlt h'
          · exact heq h'
        rw [ite_eq_right hlt_succ, ite_eq_right hlt, ite_eq_right heq]
        simp
  calc
    FrogModel.Order.cumBelow μ ((n + 1 : ℕ) : ℕ∞) = ∑' z, if z < ((n + 1 : ℕ) : ℕ∞) then μ z else 0 := rfl
    _ = ∑' z, ((if z < (n : ℕ∞) then μ z else 0) + (if z = (n : ℕ∞) then μ z else 0)) := by
      refine tsum_congr ?_
      intro z
      exact h_summand z
    _ = (∑' z, if z < (n : ℕ∞) then μ z else 0) + (∑' z, if z = (n : ℕ∞) then μ z else 0) := by
      rw [ENNReal.tsum_add]
    _ = FrogModel.Order.cumBelow μ n + (∑' z, if z = (n : ℕ∞) then μ z else 0) := rfl
    _ = FrogModel.Order.cumBelow μ n + μ n := by
      rw [tsum_ite_eq]

theorem FrogModel.Order.cumBelow_top (μ : ℕ∞ → ℝ≥0∞) :
    FrogModel.Order.cumBelow μ ⊤ = ⨆ n : ℕ, FrogModel.Order.cumBelow μ n := by
  unfold FrogModel.Order.cumBelow
  -- Goal: (∑' z, if z < ⊤ then μ z else 0) = ⨆ n : ℕ, ∑' z, if z < n then μ z else 0

  -- Helper: Nat.cast is injective
  have h_inj : Function.Injective (Nat.cast : ℕ → ℕ∞) := by
    intro a b h
    exact ENat.natCast_inj.mp h

  -- Helper: if z < x for any x, then z ≠ ⊤
  have h_ne_top_of_lt {z x : ℕ∞} (h : z < x) : z ≠ ⊤ := by
    intro h_eq
    rw [h_eq] at h
    -- Now h : ⊤ < x, which is impossible
    exact Mathlib.Tactic.ENatToNat.not_lt_top x h

  -- Helper: support of the indicator function is contained in range of Nat.cast
  have h_support {x : ℕ∞} : Function.support (fun (z : ℕ∞) => if z < x then μ z else 0) ⊆ Set.range (Nat.cast : ℕ → ℕ∞) := by
    intro z hz
    rw [Function.mem_support] at hz
    -- hz : (if z < x then μ z else 0) ≠ 0
    -- This means z < x must hold
    have h_lt : z < x := by
      by_contra! h_not
      have hzero : (if z < x then μ z else 0) = 0 := by simp [h_not]
      rw [hzero] at hz
      exact hz rfl
    have h_ne_top : z ≠ ⊤ := h_ne_top_of_lt h_lt
    rcases (ENat.ne_top_iff_exists.mp h_ne_top) with ⟨m, hm⟩
    exact ⟨m, hm⟩

  -- Step 1: Reindex the LHS tsum from ℕ∞ to ℕ
  have h_tsum_top : (∑' z : ℕ∞, if z < (⊤ : ℕ∞) then μ z else 0) = (∑' n : ℕ, μ n) := by
    calc
      (∑' z : ℕ∞, if z < (⊤ : ℕ∞) then μ z else 0)
          = (∑' n : ℕ, if (n : ℕ∞) < (⊤ : ℕ∞) then μ (n : ℕ∞) else 0) := by
        rw [Function.Injective.tsum_eq h_inj (h_support (x := ⊤))]
      _ = (∑' n : ℕ, μ (n : ℕ∞)) := by
        refine tsum_congr (fun n => ?_)
        have h_lt : (n : ℕ∞) < (⊤ : ℕ∞) := ENat.natCast_lt_top n
        simp [h_lt]
      _ = (∑' n : ℕ, μ n) := by simp

  -- Step 2: For each n, reindex and simplify the term
  have h_cumBelow_n (n : ℕ) : (∑' z : ℕ∞, if z < (n : ℕ∞) then μ z else 0) = (∑ k ∈ Finset.range n, μ k) := by
    calc
      (∑' z : ℕ∞, if z < (n : ℕ∞) then μ z else 0)
          = (∑' m : ℕ, if (m : ℕ∞) < (n : ℕ∞) then μ (m : ℕ∞) else 0) := by
        rw [Function.Injective.tsum_eq h_inj (h_support (x := (n : ℕ∞)))]
      _ = (∑ m ∈ Finset.range n, μ m) := by
        have h_support' : ∀ m : ℕ, m ∉ Finset.range n → (if (m : ℕ∞) < (n : ℕ∞) then μ m else 0) = 0 := by
          intro m hm
          rw [Finset.mem_range] at hm
          have h_not_lt : ¬ (m : ℕ∞) < (n : ℕ∞) := by
            rw [ENat.natCast_lt_natCast]
            exact hm
          simp [h_not_lt]

        have h_tsum := tsum_eq_sum (L := SummationFilter.unconditional ℕ) h_support'

        have h_sum_eq : (∑ m ∈ Finset.range n, (if (m : ℕ∞) < (n : ℕ∞) then μ m else 0)) = (∑ m ∈ Finset.range n, μ m) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          have h_lt : (k : ℕ∞) < (n : ℕ∞) := by
            rw [ENat.natCast_lt_natCast]
            exact hk
          simp [h_lt]

        calc
          (∑' m : ℕ, if (m : ℕ∞) < (n : ℕ∞) then μ m else 0)
              = (∑'[SummationFilter.unconditional ℕ] m : ℕ, if (m : ℕ∞) < (n : ℕ∞) then μ m else 0) := rfl
          _ = (∑ m ∈ Finset.range n, (if (m : ℕ∞) < (n : ℕ∞) then μ m else 0)) := by rw [h_tsum]
          _ = (∑ m ∈ Finset.range n, μ m) := by rw [h_sum_eq]

  -- Step 3: Rewrite the goal using the above
  rw [h_tsum_top]
  -- Goal: (∑' n : ℕ, μ n) = ⨆ n : ℕ, ∑' z : ℕ∞, if z < (n : ℕ∞) then μ z else 0

  -- Rewrite the RHS using h_cumBelow_n
  have h_rhs : (⨆ n : ℕ, ∑' z : ℕ∞, if z < (n : ℕ∞) then μ z else 0) = (⨆ n : ℕ, ∑ k ∈ Finset.range n, μ k) := by
    refine iSup_congr (fun n => ?_)
    rw [h_cumBelow_n n]

  rw [h_rhs]
  -- Goal: (∑' n : ℕ, μ n) = ⨆ n : ℕ, ∑ k ∈ Finset.range n, μ k

  -- This is exactly ENNReal.tsum_eq_iSup_nat
  rw [ENNReal.tsum_eq_iSup_nat]

theorem FrogModel.Order.cumBelow_add_tail (μ : ℕ∞ → ℝ≥0∞) (t : ℕ∞) :
    FrogModel.Order.cumBelow μ t + ∑' x, (if t ≤ x then μ x else 0) = ∑' x, μ x := by
  dsimp [FrogModel.Order.cumBelow]
  calc
    (∑' (z : ℕ∞), (if z < t then μ z else 0)) + (∑' (x : ℕ∞), (if t ≤ x then μ x else 0))
        = ∑' (z : ℕ∞), ((if z < t then μ z else 0) + (if t ≤ z then μ z else 0)) := by
      rw [ENNReal.tsum_add]
    _ = ∑' (z : ℕ∞), μ z := by
      refine tsum_congr (fun z => ?_)
      rcases lt_or_ge z t with (h | h)
      · simp [h, not_le.mpr h]
      · simp [h, not_lt.mpr h]
    _ = ∑' (x : ℕ∞), μ x := rfl

theorem FrogModel.Order.cumBelow_le_of_tail (μ ν : ℕ∞ → ℝ≥0∞) (hfin : ∑' x, ν x ≠ ⊤)
    (hmass : ∑' x, μ x = ∑' x, ν x)
    (htail : ∀ t : ℕ∞, ∑' x, (if t ≤ x then μ x else 0) ≤ ∑' x, (if t ≤ x then ν x else 0))
    (t : ℕ∞) : FrogModel.Order.cumBelow ν t ≤ FrogModel.Order.cumBelow μ t := by
  set tailμ := ∑' x, (if t ≤ x then μ x else 0) with htailμ
  set tailν := ∑' x, (if t ≤ x then ν x else 0) with htailν
  have h_add_ν : FrogModel.Order.cumBelow ν t + tailν = ∑' x, ν x := by
    simpa [htailν] using FrogModel.Order.cumBelow_add_tail ν t
  have h_add_μ : FrogModel.Order.cumBelow μ t + tailμ = ∑' x, μ x := by
    simpa [htailμ] using FrogModel.Order.cumBelow_add_tail μ t
  have h_total_ne_top : ∑' x, ν x ≠ ⊤ := hfin
  have h_total_eq : ∑' x, μ x = ∑' x, ν x := hmass
  have h_tail_le : tailμ ≤ tailν := htail t
  have h_sum_le : FrogModel.Order.cumBelow ν t + tailν ≤ FrogModel.Order.cumBelow μ t + tailν := by
    calc
      FrogModel.Order.cumBelow ν t + tailν = ∑' x, ν x := h_add_ν
      _ = ∑' x, μ x := by rw [h_total_eq]
      _ = FrogModel.Order.cumBelow μ t + tailμ := by rw [h_add_μ]
      _ ≤ FrogModel.Order.cumBelow μ t + tailν := add_le_add_right h_tail_le _
  have h_tailν_ne_top : tailν ≠ ⊤ := by
    intro htop
    apply h_total_ne_top
    rw [← h_add_ν, htop]
    simp
  exact ENNReal.le_of_add_le_add_right h_tailν_ne_top h_sum_le

theorem FrogModel.Order.iUnion_Ico_cumBelow (μ : ℕ∞ → ℝ≥0∞) (hfin : ∑' x, μ x ≠ ⊤) :
    ⋃ x, Set.Ico (FrogModel.Order.cumBelow μ x).toReal
        (FrogModel.Order.cumBelow μ x + μ x).toReal = Set.Ico 0 (∑' x, μ x).toReal := by
  have hm_fin : (∑' x, μ x) < ⊤ := lt_of_le_of_ne le_top hfin
  have hm_ne_top : (∑' x, μ x) ≠ ⊤ := hfin
  have hF_add_tail (t : ℕ∞) : (FrogModel.Order.cumBelow μ) t + ∑' x, (if t ≤ x then μ x else 0) = ∑' x, μ x :=
    FrogModel.Order.cumBelow_add_tail μ t
  have h_tail_ge (t : ℕ∞) : μ t ≤ ∑' x, (if t ≤ x then μ x else 0) := by
    have h := ENNReal.le_tsum (f := fun x : ℕ∞ => (if t ≤ x then μ x else 0)) t
    simpa using h
  have hF_add_μ_le_m (t : ℕ∞) : (FrogModel.Order.cumBelow μ) t + μ t ≤ ∑' x, μ x := by
    calc
      (FrogModel.Order.cumBelow μ) t + μ t ≤ (FrogModel.Order.cumBelow μ) t + ∑' x, (if t ≤ x then μ x else 0) := by
        exact add_le_add_right (h_tail_ge t) ((FrogModel.Order.cumBelow μ) t)
      _ = ∑' x, μ x := hF_add_tail t
  have hF_add_μ_ne_top (t : ℕ∞) : (FrogModel.Order.cumBelow μ) t + μ t ≠ ⊤ := by
    have hle : (FrogModel.Order.cumBelow μ) t + μ t ≤ ∑' x, μ x := hF_add_μ_le_m t
    intro htop
    rw [htop] at hle
    have hmtop' : (∑' x, μ x) = ⊤ := le_antisymm le_top hle
    exact hm_ne_top hmtop'
  have hF_nonneg (t : ℕ∞) : 0 ≤ ((FrogModel.Order.cumBelow μ) t).toReal := ENNReal.toReal_nonneg
  have hF_add_μ_fin (t : ℕ∞) : ((FrogModel.Order.cumBelow μ) t + μ t).toReal ≤ (∑' x, μ x).toReal := by
    rw [ENNReal.toReal_le_toReal (hF_add_μ_ne_top t) hm_ne_top]
    exact hF_add_μ_le_m t
  have hF0 : (FrogModel.Order.cumBelow μ) 0 = 0 := by
    dsimp [FrogModel.Order.cumBelow]
    apply ENNReal.tsum_eq_zero.mpr
    intro z
    have : ¬ (z < (0 : ℕ∞)) := by simp
    simp [this]
  have hF_top_add_μ_top : (FrogModel.Order.cumBelow μ) ⊤ + μ ⊤ = ∑' x, μ x := by
    have h := hF_add_tail ⊤
    have htail : ∑' x, (if ⊤ ≤ x then μ x else 0) = μ ⊤ := by
      apply tsum_eq_single (L := SummationFilter.unconditional ℕ∞) ⊤
      intro x hx
      have : ¬ (⊤ ≤ x) := by
        intro hle
        apply hx
        exact le_antisymm le_top hle
      simp [this]
    rw [htail] at h
    exact h
  have hF_fin (t : ℕ∞) : (FrogModel.Order.cumBelow μ) t ≠ ⊤ := by
    intro htopF
    have : (FrogModel.Order.cumBelow μ) t + μ t = ⊤ := by
      rw [htopF, top_add]
    exact hF_add_μ_ne_top t this
  have hF_top : ((FrogModel.Order.cumBelow μ) ⊤).toReal = ⨆ n : ℕ, ((FrogModel.Order.cumBelow μ) n).toReal := by
    have htop_eq : (FrogModel.Order.cumBelow μ) ⊤ = ⨆ n : ℕ, (FrogModel.Order.cumBelow μ) n :=
      FrogModel.Order.cumBelow_top μ
    rw [htop_eq]
    exact ENNReal.toReal_iSup (f := fun n : ℕ => (FrogModel.Order.cumBelow μ) n) (fun n => hF_fin n)
  refine Set.ext ?_
  intro p
  constructor
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨x, hp⟩
    rcases Set.mem_Ico.1 hp with ⟨hpx1, hpx2⟩
    have h0 : 0 ≤ p := le_trans (hF_nonneg x) hpx1
    have hm' : p < (∑' x, μ x).toReal := lt_of_lt_of_le hpx2 (hF_add_μ_fin x)
    exact Set.mem_Ico.mpr ⟨h0, hm'⟩
  · intro hp
    rcases Set.mem_Ico.1 hp with ⟨hp0, hpm⟩
    by_cases h : ∀ n : ℕ, ((FrogModel.Order.cumBelow μ) n).toReal ≤ p
    · -- Case 1: ∀ n, (F n).toReal ≤ p
      have hF_top_le : ((FrogModel.Order.cumBelow μ) ⊤).toReal ≤ p := by
        rw [hF_top]
        exact ciSup_le h
      have h_lt : p < ((FrogModel.Order.cumBelow μ) ⊤ + μ ⊤).toReal := by
        rw [hF_top_add_μ_top]
        exact hpm
      exact Set.mem_iUnion.mpr ⟨⊤, Set.mem_Ico.mpr ⟨hF_top_le, h_lt⟩⟩
    · -- Case 2: ∃ n, p < (F n).toReal
      push Not at h
      let n := Nat.find h
      have hn : p < ((FrogModel.Order.cumBelow μ) n).toReal := Nat.find_spec h
      have hn_min : ∀ k < n, ((FrogModel.Order.cumBelow μ) k).toReal ≤ p := by
        intro k hk
        by_contra! hk'
        have := Nat.find_min h hk
        exact this hk'
      -- n ≠ 0 because F 0 = 0 and p ≥ 0
      have hn0 : n ≠ 0 := by
        intro hzero
        have hzero' : (n : ℕ∞) = (0 : ℕ∞) := congrArg (fun x : ℕ => (x : ℕ∞)) hzero
        rw [hzero'] at hn
        have h0 : ((FrogModel.Order.cumBelow μ) (0 : ℕ∞)).toReal = 0 := by simp [hF0]
        rw [h0] at hn
        linarith
      -- n = k+1 for some k
      rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨k, hk⟩
      have hk_lt_n : k < n := by
        rw [hk]
        omega
      have hk_le : ((FrogModel.Order.cumBelow μ) k).toReal ≤ p := hn_min k hk_lt_n
      have h_succ_eq : (FrogModel.Order.cumBelow μ) (k + 1 : ℕ) = (FrogModel.Order.cumBelow μ) k + μ k :=
        FrogModel.Order.cumBelow_succ μ k
      rw [hk, h_succ_eq] at hn
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_Ico.mpr ⟨hk_le, hn⟩⟩

theorem FrogModel.Order.pairwise_disjoint_Ico_cumBelow (μ : ℕ∞ → ℝ≥0∞) (hfin : ∑' x, μ x ≠ ⊤) :
    Pairwise (Function.onFun Disjoint fun x => Set.Ico (FrogModel.Order.cumBelow μ x).toReal
      (FrogModel.Order.cumBelow μ x + μ x).toReal) := by
  intro x y hxy
  have hsum_lt_top : ∑' x, μ x < ⊤ := lt_top_iff_ne_top.mpr hfin
  have hlt_or : x < y ∨ y < x := lt_or_gt_of_ne hxy
  rcases hlt_or with (hlt | hlt)
  · -- case x < y
    have hle_ennreal : FrogModel.Order.cumBelow μ x + μ x ≤ FrogModel.Order.cumBelow μ y :=
      FrogModel.Order.cumBelow_add_le μ x y hlt
    -- F y ≤ sum, hence finite
    have hle_Fy_sum : FrogModel.Order.cumBelow μ y ≤ ∑' x, μ x := by
      have h := FrogModel.Order.cumBelow_add_tail μ y
      have hnonneg : 0 ≤ ∑' z, (if y ≤ z then μ z else 0) := zero_le (a := ∑' z, (if y ≤ z then μ z else 0))
      calc
        FrogModel.Order.cumBelow μ y ≤ FrogModel.Order.cumBelow μ y + ∑' z, (if y ≤ z then μ z else 0) :=
          le_add_of_nonneg_right hnonneg
        _ = ∑' x, μ x := h
    have hfin_Fy : FrogModel.Order.cumBelow μ y < ⊤ :=
      lt_of_le_of_lt hle_Fy_sum hsum_lt_top
    -- F x + μ x ≤ F y, hence finite
    have hfin_Fx_add : FrogModel.Order.cumBelow μ x + μ x < ⊤ :=
      lt_of_le_of_lt hle_ennreal hfin_Fy
    have hle_toReal : (FrogModel.Order.cumBelow μ x + μ x).toReal ≤ (FrogModel.Order.cumBelow μ y).toReal := by
      rw [ENNReal.toReal_le_toReal hfin_Fx_add.ne hfin_Fy.ne]
      exact hle_ennreal
    rw [Function.onFun, Set.Ico_disjoint_Ico]
    -- Goal: min ((F x + μ x).toReal) ((F y + μ y).toReal) ≤ max ((F x).toReal) ((F y).toReal)
    -- We have (F x + μ x).toReal ≤ (F y).toReal
    -- min a₂ b₂ ≤ a₂ ≤ b₁ ≤ max a₁ b₁
    calc
      min ((FrogModel.Order.cumBelow μ x + μ x).toReal) ((FrogModel.Order.cumBelow μ y + μ y).toReal)
          ≤ (FrogModel.Order.cumBelow μ x + μ x).toReal := min_le_left _ _
      _ ≤ (FrogModel.Order.cumBelow μ y).toReal := hle_toReal
      _ ≤ max ((FrogModel.Order.cumBelow μ x).toReal) ((FrogModel.Order.cumBelow μ y).toReal) := le_max_right _ _
  · -- case y < x, symmetric
    have hle_ennreal : FrogModel.Order.cumBelow μ y + μ y ≤ FrogModel.Order.cumBelow μ x :=
      FrogModel.Order.cumBelow_add_le μ y x hlt
    have hle_Fx_sum : FrogModel.Order.cumBelow μ x ≤ ∑' x, μ x := by
      have h := FrogModel.Order.cumBelow_add_tail μ x
      have hnonneg : 0 ≤ ∑' z, (if x ≤ z then μ z else 0) := zero_le (a := ∑' z, (if x ≤ z then μ z else 0))
      calc
        FrogModel.Order.cumBelow μ x ≤ FrogModel.Order.cumBelow μ x + ∑' z, (if x ≤ z then μ z else 0) :=
          le_add_of_nonneg_right hnonneg
        _ = ∑' x, μ x := h
    have hfin_Fx : FrogModel.Order.cumBelow μ x < ⊤ :=
      lt_of_le_of_lt hle_Fx_sum hsum_lt_top
    have hfin_Fy_add : FrogModel.Order.cumBelow μ y + μ y < ⊤ :=
      lt_of_le_of_lt hle_ennreal hfin_Fx
    have hle_toReal : (FrogModel.Order.cumBelow μ y + μ y).toReal ≤ (FrogModel.Order.cumBelow μ x).toReal := by
      rw [ENNReal.toReal_le_toReal hfin_Fy_add.ne hfin_Fx.ne]
      exact hle_ennreal
    rw [Function.onFun, Set.Ico_disjoint_Ico]
    calc
      min ((FrogModel.Order.cumBelow μ x + μ x).toReal) ((FrogModel.Order.cumBelow μ y + μ y).toReal)
          ≤ (FrogModel.Order.cumBelow μ y + μ y).toReal := min_le_right _ _
      _ ≤ (FrogModel.Order.cumBelow μ x).toReal := hle_toReal
      _ ≤ max ((FrogModel.Order.cumBelow μ x).toReal) ((FrogModel.Order.cumBelow μ y).toReal) := le_max_left _ _

theorem FrogModel.Order.tsum_volume_Ico_inter (μ ν : ℕ∞ → ℝ≥0∞) (hfin : ∑' x, ν x ≠ ⊤)
    (hmass : ∑' x, μ x = ∑' x, ν x) (x : ℕ∞) :
    ∑' y, volume (Set.Ico (FrogModel.Order.cumBelow μ x).toReal
        (FrogModel.Order.cumBelow μ x + μ x).toReal ∩
      Set.Ico (FrogModel.Order.cumBelow ν y).toReal
        (FrogModel.Order.cumBelow ν y + ν y).toReal) = μ x := by
  set I := Set.Ico (FrogModel.Order.cumBelow μ x).toReal (FrogModel.Order.cumBelow μ x + μ x).toReal with hI
  set J := fun y : ℕ∞ => Set.Ico (FrogModel.Order.cumBelow ν y).toReal
    (FrogModel.Order.cumBelow ν y + ν y).toReal with hJ
  have hsum_ne_top : ∑' x, μ x ≠ ⊤ := by
    rw [hmass]
    exact hfin
  have h_mu_x_ne_top : μ x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top hsum_ne_top x
  have h_cumBelow_ne_top : FrogModel.Order.cumBelow μ x ≠ ⊤ := by
    have hle : FrogModel.Order.cumBelow μ x ≤ ∑' x, μ x := by
      have h_eq := FrogModel.Order.cumBelow_add_tail μ x
      have hle' : FrogModel.Order.cumBelow μ x ≤
          FrogModel.Order.cumBelow μ x + ∑' z, (if x ≤ z then μ z else 0) :=
        le_add_of_nonneg_right (zero_le (a := ∑' z, (if x ≤ z then μ z else 0)))
      rw [h_eq] at hle'
      exact hle'
    exact ne_top_of_le_ne_top hsum_ne_top hle
  have h_cumBelow_add_mu_ne_top : FrogModel.Order.cumBelow μ x + μ x ≠ ⊤ :=
    (ENNReal.add_ne_top.mpr ⟨h_cumBelow_ne_top, h_mu_x_ne_top⟩)
  have h_disjoint_J : Pairwise (Function.onFun Disjoint J) :=
    FrogModel.Order.pairwise_disjoint_Ico_cumBelow ν hfin
  have h_disjoint_I_inter_J : Pairwise (Function.onFun Disjoint fun y => I ∩ J y) := by
    have h_sub : (fun y => I ∩ J y) ≤ J := by
      intro y
      exact Set.inter_subset_right (s := I) (t := J y)
    exact pairwise_disjoint_mono h_disjoint_J h_sub
  have h_measurable : ∀ y, MeasurableSet (I ∩ J y) := by
    intro y
    exact (measurableSet_Ico.inter measurableSet_Ico : MeasurableSet (I ∩ J y))
  have h_measure_union : ∑' y, volume (I ∩ J y) = volume (⋃ y, I ∩ J y) := by
    rw [← MeasureTheory.measure_iUnion h_disjoint_I_inter_J h_measurable]
  have h_inter_union : (⋃ y, I ∩ J y) = I ∩ (⋃ y, J y) := by
    rw [← Set.inter_iUnion]
  have h_union_J : (⋃ y, J y) = Set.Ico 0 (∑' x, ν x).toReal := by
    rw [FrogModel.Order.iUnion_Ico_cumBelow ν hfin]
  have h_union_J' : (⋃ y, J y) = Set.Ico 0 (∑' x, μ x).toReal := by
    rw [h_union_J, hmass]
  have h_cumBelow_add_mu_le : FrogModel.Order.cumBelow μ x + μ x ≤ ∑' x, μ x := by
    have h_eq := FrogModel.Order.cumBelow_add_tail μ x
    have h_tail_ge_mu : μ x ≤ ∑' z, (if x ≤ z then μ z else 0) := by
      simpa using ENNReal.le_tsum (f := fun z : ℕ∞ => (if x ≤ z then μ z else 0)) x
    have hle_sum : FrogModel.Order.cumBelow μ x + μ x ≤
        FrogModel.Order.cumBelow μ x + ∑' z, (if x ≤ z then μ z else 0) :=
      add_le_add (le_refl (FrogModel.Order.cumBelow μ x)) h_tail_ge_mu
    rw [h_eq] at hle_sum
    exact hle_sum
  have h_I_subset : I ⊆ Set.Ico 0 (∑' x, μ x).toReal := by
    intro z hz
    rw [Set.mem_Ico] at hz ⊢
    rcases hz with ⟨hz_left, hz_right⟩
    have hz_left' : 0 ≤ z := le_trans ENNReal.toReal_nonneg hz_left
    refine ⟨hz_left', ?_⟩
    have h_toReal_le : (FrogModel.Order.cumBelow μ x + μ x).toReal ≤ (∑' x, μ x).toReal :=
      ENNReal.toReal_mono hsum_ne_top h_cumBelow_add_mu_le
    exact lt_of_lt_of_le hz_right h_toReal_le
  have h_inter_eq_I : I ∩ (⋃ y, J y) = I := by
    rw [h_union_J', Set.inter_eq_left.mpr h_I_subset]
  have h_volume_I : volume I = μ x := by
    unfold I
    rw [Real.volume_Ico]
    have h_add_toReal : (FrogModel.Order.cumBelow μ x + μ x).toReal =
        (FrogModel.Order.cumBelow μ x).toReal + (μ x).toReal := by
      rw [ENNReal.toReal_add h_cumBelow_ne_top h_mu_x_ne_top]
    rw [h_add_toReal, add_sub_cancel_left, ENNReal.ofReal_toReal h_mu_x_ne_top]
  calc
    ∑' y, volume (I ∩ J y) = volume (⋃ y, I ∩ J y) := by rw [h_measure_union]
    _ = volume (I ∩ (⋃ y, J y)) := by rw [h_inter_union]
    _ = volume I := by rw [h_inter_eq_I]
    _ = μ x := h_volume_I

theorem FrogModel.Order.Ico_inter_eq_empty (μ ν : ℕ∞ → ℝ≥0∞) (hfin : ∑' x, μ x ≠ ⊤)
    (hcum : ∀ t, FrogModel.Order.cumBelow ν t ≤ FrogModel.Order.cumBelow μ t) (x y : ℕ∞)
    (hyx : y < x) :
    Set.Ico (FrogModel.Order.cumBelow μ x).toReal (FrogModel.Order.cumBelow μ x + μ x).toReal ∩
      Set.Ico (FrogModel.Order.cumBelow ν y).toReal
        (FrogModel.Order.cumBelow ν y + ν y).toReal = ∅ := by
  have hy_ne_top : y ≠ ⊤ := by
    intro hy_top
    have htop_lt_x : ⊤ < x := by simpa [hy_top] using hyx
    exact not_top_lt htop_lt_x
  rcases (ENat.ne_top_iff_exists.mp hy_ne_top) with ⟨n, hn⟩
  have hn_lt_x : (n : ℕ∞) < x := by simpa [hn] using hyx
  have h_succ_le_x : ((n + 1 : ℕ) : ℕ∞) ≤ x :=
    ((ENat.add_one_le_iff (ENat.natCast_ne_top n)).mpr hn_lt_x)
  have h_cumBelow_succ : FrogModel.Order.cumBelow ν ((n + 1 : ℕ) : ℕ∞) =
      FrogModel.Order.cumBelow ν y + ν y := by
    simpa [hn] using FrogModel.Order.cumBelow_succ ν n
  have h_cumBelow_le : FrogModel.Order.cumBelow ν y + ν y ≤ FrogModel.Order.cumBelow μ x := by
    calc
      FrogModel.Order.cumBelow ν y + ν y = FrogModel.Order.cumBelow ν ((n + 1 : ℕ) : ℕ∞) := by
        rw [h_cumBelow_succ]
      _ ≤ FrogModel.Order.cumBelow μ ((n + 1 : ℕ) : ℕ∞) := hcum _
      _ ≤ FrogModel.Order.cumBelow μ x := FrogModel.Order.cumBelow_mono _ h_succ_le_x
  have h_fin_cumBelow : FrogModel.Order.cumBelow μ x ≠ ⊤ := by
    have h_total := FrogModel.Order.cumBelow_add_tail μ x
    intro htop
    apply hfin
    rw [← h_total]
    simp [htop]
  have h_fin_cumBelow_nu : FrogModel.Order.cumBelow ν y + ν y ≠ ⊤ := by
    intro htop
    apply h_fin_cumBelow
    have htop_le : (⊤ : ℝ≥0∞) ≤ FrogModel.Order.cumBelow μ x := by
      simpa [htop] using h_cumBelow_le
    exact top_unique htop_le
  have h_toReal_le : (FrogModel.Order.cumBelow ν y + ν y).toReal ≤
      (FrogModel.Order.cumBelow μ x).toReal :=
    ENNReal.toReal_mono h_fin_cumBelow h_cumBelow_le
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  rcases hne with ⟨p, hp⟩
  rcases ((Set.mem_inter_iff p _ _).mp hp) with ⟨hp1, hp2⟩
  have hp_lower : (FrogModel.Order.cumBelow μ x).toReal ≤ p :=
    Set.mem_Ico.mp hp1 |>.left
  have hp_upper : p < (FrogModel.Order.cumBelow ν y + ν y).toReal :=
    Set.mem_Ico.mp hp2 |>.right
  linarith

theorem FrogModel.Order.quantile_coupling (μ ν : ℕ∞ → ℝ≥0∞) (hfin : ∑' x, ν x ≠ ⊤)
    (hmass : ∑' x, μ x = ∑' x, ν x)
    (htail : ∀ t : ℕ∞, ∑' x, (if t ≤ x then μ x else 0) ≤ ∑' x, (if t ≤ x then ν x else 0)) :
    ∃ π : ℕ∞ × ℕ∞ → ℝ≥0∞, (∀ x, ∑' y, π (x, y) = μ x) ∧ (∀ y, ∑' x, π (x, y) = ν y) ∧
      ∀ x y, π (x, y) ≠ 0 → x ≤ y := by
  set hfinμ : ∑' x, μ x ≠ ⊤ := hmass ▸ hfin
  set hcum : ∀ t : ℕ∞, FrogModel.Order.cumBelow ν t ≤ FrogModel.Order.cumBelow μ t :=
    FrogModel.Order.cumBelow_le_of_tail μ ν hfin hmass htail
  set π : ℕ∞ × ℕ∞ → ℝ≥0∞ := λ ⟨x, y⟩ =>
    volume (Set.Ico (FrogModel.Order.cumBelow μ x).toReal
      (FrogModel.Order.cumBelow μ x + μ x).toReal ∩
      Set.Ico (FrogModel.Order.cumBelow ν y).toReal
        (FrogModel.Order.cumBelow ν y + ν y).toReal) with hπ
  refine ⟨π, ?_, ?_, ?_⟩
  · intro x
    simpa [hπ] using FrogModel.Order.tsum_volume_Ico_inter μ ν hfin hmass x
  · intro y
    have h := FrogModel.Order.tsum_volume_Ico_inter ν μ hfinμ hmass.symm y
    simpa [hπ, Set.inter_comm] using h
  · intro x y hπxy
    by_contra! hlt
    have h_empty : Set.Ico (FrogModel.Order.cumBelow μ x).toReal
        (FrogModel.Order.cumBelow μ x + μ x).toReal ∩
        Set.Ico (FrogModel.Order.cumBelow ν y).toReal
          (FrogModel.Order.cumBelow ν y + ν y).toReal = ∅ :=
      FrogModel.Order.Ico_inter_eq_empty μ ν hfinμ hcum x y hlt
    have h_zero : π (x, y) = 0 := by
      rw [hπ]
      simp [h_empty]
    exact hπxy h_zero
