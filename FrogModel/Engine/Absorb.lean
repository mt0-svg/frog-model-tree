module

public import FrogModel.Engine.FK

@[expose] public section

/-!
# The root engine: the absorbed output as a least solution

The probability that the root chain from a live valid state `x` records the
outputs `o` is the least solution of the linear system with kernel the transition probabilities and
right side the probability of being absorbed with `o` at the next step (`law_absorb`); under i.i.d.
inputs whose directions exit with positive probability, the exits are unbounded almost surely
(`ae_exitCount_unbounded`).
-/

open MeasureTheory
open scoped ENNReal

open Classical in
theorem FrogModel.Engine.tsum_eq_ite_of_unique (a : ℕ → ℝ≥0∞) (h01 : ∀ k, a k = 0 ∨ a k = 1)
    (huniq : ∀ j k, a j ≠ 0 → a k ≠ 0 → j = k) :
    ∑' k, a k = if ∃ k, a k ≠ 0 then 1 else 0 := by
  split_ifs with h
  · obtain ⟨k₀, hk₀⟩ := h
    have hk₀_one : a k₀ = 1 := by
      rcases h01 k₀ with (h0 | h1)
      · exfalso; exact hk₀ h0
      · exact h1
    have h_others : ∀ k, k ≠ k₀ → a k = 0 := by
      intro k hk_ne
      rcases h01 k with (h0 | h1)
      · exact h0
      · exfalso
        apply hk_ne
        exact huniq k k₀ (by rw [h1]; norm_num) hk₀
    calc
      ∑' k, a k = a k₀ := tsum_eq_single k₀ h_others
      _ = 1 := hk₀_one
  · have h_all_zero : ∀ k, a k = 0 := by
      intro k
      rcases h01 k with (h0 | h1)
      · exact h0
      · exfalso
        apply h
        exact ⟨k, by rw [h1]; norm_num⟩
    have h_eq : a = 0 := by
      ext k; exact h_all_zero k
    simp [h_eq]

theorem FrogModel.Engine.fk_one_eq_sum {X Ξ : Type*} (f : X → Ξ → X) (a : X → Ξ → ℝ≥0∞)
    (n : ℕ) (x : X) (w : ℕ → Ξ) :
    FrogModel.Engine.fk f (fun _ _ => 1) a n x w =
      ∑ k ∈ Finset.range n, a (FrogModel.Engine.traj f x w k) (w k) := by
  induction' n with n ih generalizing x w
  · simp [FrogModel.Engine.fk]
  · rw [FrogModel.Engine.fk]
    simp
    rw [ih (f x (w 0)) (fun k => w (k + 1))]
    simp_rw [← FrogModel.Engine.traj_succ_shift f x w]
    rw [Finset.sum_range_succ']
    simp [FrogModel.Engine.traj, add_comm]

theorem FrogModel.Engine.absorbAt_unique {S U : Type*} {d J : ℕ} (cstep : S → U → ℕ × S)
    (o : Fin J → ℕ) (x : FrogModel.Engine.RState S d J) (w : ℕ → Fin (d + 1) × U) (j k : ℕ)
    (hj : FrogModel.Engine.absorbAt cstep o (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w j) (w j) ≠ 0)
    (hk : FrogModel.Engine.absorbAt cstep o (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w k) (w k) ≠ 0) :
    j = k := by
  simp only [FrogModel.Engine.absorbAt] at hj hk
  split_ifs at hj with hc_j
  · rcases hc_j with ⟨h_lt_j, h_le_j, h_out_j⟩
    split_ifs at hk with hc_k
    · rcases hc_k with ⟨h_lt_k, h_le_k, h_out_k⟩
      have h_mono := FrogModel.Engine.traj_i_mono cstep x w
      by_cases h_jk : j < k
      · have h_succ_le : j + 1 ≤ k := Nat.succ_le_of_lt h_jk
        have h_mono_le : (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w (j + 1)).i ≤
                         (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w k).i :=
          h_mono h_succ_le
        have h_le_trans : J ≤ (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w k).i :=
          le_trans h_le_j h_mono_le
        have : (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w k).i < J := h_lt_k
        linarith
      · by_cases h_kj : k < j
        · have h_succ_le : k + 1 ≤ j := Nat.succ_le_of_lt h_kj
          have h_mono_le : (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w (k + 1)).i ≤
                           (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w j).i :=
            h_mono h_succ_le
          have h_le_trans : J ≤ (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w j).i :=
            le_trans h_le_k h_mono_le
          have : (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w j).i < J := h_lt_j
          linarith
        · omega
    · exact (hk rfl).elim
  · exact (hj rfl).elim

theorem FrogModel.Engine.exists_absorbAt_iff {S U : Type*} {d J : ℕ} (cstep : S → U → ℕ × S)
    (o : Fin J → ℕ) (x : FrogModel.Engine.RState S d J) (hx : FrogModel.Engine.Valid x)
    (hlive : x.i < J) (w : ℕ → Fin (d + 1) × U) :
    (∃ k, FrogModel.Engine.absorbAt cstep o
        (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w k) (w k) ≠ 0) ↔
      FrogModel.Engine.recOut (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w) =
        fun k => (o k : ℕ∞) := by
  set t := FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w
  have ht0 : t 0 = x := rfl
  have ht_succ : ∀ n, t (n + 1) = FrogModel.Engine.rstep cstep (t n) (w n) := fun n => rfl
  -- claim: if J ≤ (t n).i then recOut t = (t n).out
  have h_claim : ∀ n, J ≤ (t n).i → FrogModel.Engine.recOut t = (t n).out := by
    intro n hn
    ext j
    apply le_antisymm
    · -- ⨅ s, (t s).out j ≤ (t n).out j
      exact iInf_le (fun s => (t s).out j) n
    · -- (t n).out j ≤ ⨅ s, (t s).out j
      refine le_iInf ?_
      intro s
      by_cases hsn : s ≤ n
      · -- s ≤ n, use antitone
        have h_anti : Antitone fun n => (t n).out :=
          FrogModel.Engine.traj_out_antitone cstep x hx w
        exact (h_anti hsn) j
      · -- n < s, i.e., n ≤ s
        have hns : n ≤ s := Nat.le_of_lt (Nat.lt_of_not_ge hsn)
        have h_j_lt_i : (j : ℕ) < (t n).i :=
          lt_of_lt_of_le j.2 hn
        exact (FrogModel.Engine.traj_out_stable cstep x w j n h_j_lt_i s hns).symm.le
  constructor
  · -- forward direction (→)
    rintro ⟨k, hk⟩
    have h_absorb_cond : (t k).i < J ∧ J ≤ (FrogModel.Engine.rstep cstep (t k) (w k)).i ∧
        (FrogModel.Engine.rstep cstep (t k) (w k)).out = fun k => (o k : ℕ∞) := by
      unfold FrogModel.Engine.absorbAt at hk
      by_cases hc : (t k).i < J ∧ J ≤ (FrogModel.Engine.rstep cstep (t k) (w k)).i ∧
          (FrogModel.Engine.rstep cstep (t k) (w k)).out = fun k => (o k : ℕ∞)
      · exact hc
      · simp [hc] at hk
    rcases h_absorb_cond with ⟨h_lt, h_le, h_out⟩
    have h_recOut : FrogModel.Engine.recOut t = (t (k + 1)).out :=
      h_claim (k + 1) (by
        rw [ht_succ k]
        exact h_le)
    rw [h_recOut, ht_succ k, h_out]
  · -- backward direction (←)
    intro h_recOut
    have hJpos : 0 < J := Nat.lt_of_le_of_lt (Nat.zero_le _) hlive
    have hJsub_lt : J - 1 < J := by
      have := Nat.pred_lt hJpos.ne'
      simpa using this
    let l : Fin J := ⟨J - 1, hJsub_lt⟩
    have h_recOut_l : FrogModel.Engine.recOut t l = (o l : ℕ∞) := by
      simp [h_recOut]
    have h_fin_ne_top : (o l : ℕ∞) ≠ ⊤ := by simp
    have h_not_all_top : ¬ (∀ n, (t n).out l = ⊤) := by
      rw [← iInf_eq_top]
      rw [← FrogModel.Engine.recOut]
      intro h_all_top
      apply h_fin_ne_top
      rw [← h_recOut_l]
      exact h_all_top
    rcases not_forall.mp h_not_all_top with ⟨s, hs⟩
    -- hs : ¬ (t s).out l = ⊤, i.e., (t s).out l ≠ ⊤
    have hs_ne_top : (t s).out l ≠ ⊤ := hs
    have h_valid := FrogModel.Engine.traj_valid cstep x hx w s
    -- h_valid : Valid (t s)
    -- Valid means: (i < J → 1 ≤ p) ∧ ∀ k, i ≤ k → out k = ⊤
    rcases h_valid with ⟨h_valid_imp, h_valid_out⟩
    have h_not_le : ¬ ((t s).i ≤ l) := by
      intro hle
      apply hs_ne_top
      exact h_valid_out l hle
    have h_l_lt_i : (l : ℕ) < (t s).i := Nat.lt_of_not_ge h_not_le
    -- (l : ℕ) = J - 1, so J - 1 < (t s).i, hence J ≤ (t s).i
    have h_J_le_i : J ≤ (t s).i := by
      have : J - 1 < (t s).i := h_l_lt_i
      omega
    have h_exists : ∃ n, J ≤ (t n).i := ⟨s, h_J_le_i⟩
    let n := Nat.find h_exists
    have hn : J ≤ (t n).i := Nat.find_spec h_exists
    have hn_min : ∀ m, m < n → ¬ (J ≤ (t m).i) := fun m hm => Nat.find_min h_exists hm
    have hn_pos : n ≠ 0 := by
      intro hzero
      rw [hzero] at hn
      rw [ht0] at hn
      exact Nat.not_lt_of_le hn hlive
    rcases Nat.exists_eq_succ_of_ne_zero hn_pos with ⟨k, hk_eq⟩
    -- hk_eq : n = k + 1
    have hk_not_le : ¬ (J ≤ (t k).i) := by
      rw [hk_eq] at hn_min
      exact hn_min k (Nat.lt_succ_self k)
    have hk_lt_J : (t k).i < J := Nat.lt_of_not_ge hk_not_le
    have h_recOut_n : FrogModel.Engine.recOut t = (t n).out := h_claim n hn
    rw [hk_eq] at h_recOut_n
    -- h_recOut_n : recOut t = (t (k + 1)).out
    -- But recOut t = fun k => (o k : ℕ∞) by h_recOut
    have h_out_n : (t (k + 1)).out = fun k => (o k : ℕ∞) := by
      rw [← h_recOut_n, h_recOut]
    refine ⟨k, ?_⟩
    unfold FrogModel.Engine.absorbAt
    have h_cond : (t k).i < J ∧ J ≤ (FrogModel.Engine.rstep cstep (t k) (w k)).i ∧
        (FrogModel.Engine.rstep cstep (t k) (w k)).out = fun k => (o k : ℕ∞) := by
      refine ⟨hk_lt_J, ?_, ?_⟩
      · -- J ≤ (rstep cstep (t k) (w k)).i = (t (k+1)).i
        rw [← ht_succ k]
        rw [hk_eq] at hn
        exact hn
      · -- (rstep cstep (t k) (w k)).out = fun k => (o k : ℕ∞)
        rw [← ht_succ k, h_out_n]
    simp [h_cond]

theorem FrogModel.Engine.iSup_fk_absorb {S U : Type*} {d J : ℕ} (cstep : S → U → ℕ × S)
    (o : Fin J → ℕ) (x : FrogModel.Engine.RState S d J) (hx : FrogModel.Engine.Valid x)
    (hlive : x.i < J) (w : ℕ → Fin (d + 1) × U) :
    ⨆ n, FrogModel.Engine.fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
        (FrogModel.Engine.absorbAt cstep o) n x w =
      if FrogModel.Engine.recOut (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w) =
          (fun k => (o k : ℕ∞)) then 1 else 0 := by
  have h_fk_eq : ∀ n, FrogModel.Engine.fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
      (FrogModel.Engine.absorbAt cstep o) n x w =
      ∑ k ∈ Finset.range n, FrogModel.Engine.absorbAt cstep o
        (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w k) (w k) := by
    intro n
    exact FrogModel.Engine.fk_one_eq_sum (FrogModel.Engine.rstep cstep)
      (FrogModel.Engine.absorbAt cstep o) n x w
  simp_rw [h_fk_eq]
  rw [← ENNReal.tsum_eq_iSup_nat]
  let a : ℕ → ℝ≥0∞ := fun k =>
    FrogModel.Engine.absorbAt cstep o (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w k) (w k)
  have h01 : ∀ k, a k = 0 ∨ a k = 1 := by
    intro k
    unfold a FrogModel.Engine.absorbAt
    split_ifs with hcond
    · right; rfl
    · left; rfl
  have huniq : ∀ j k, a j ≠ 0 → a k ≠ 0 → j = k :=
    FrogModel.Engine.absorbAt_unique cstep o x w
  rw [FrogModel.Engine.tsum_eq_ite_of_unique a h01 huniq]
  have h_iff : (∃ k, a k ≠ 0) ↔
      FrogModel.Engine.recOut (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w) =
      fun k => (o k : ℕ∞) := by
    simpa [a] using FrogModel.Engine.exists_absorbAt_iff cstep o x hx hlive w
  by_cases h : ∃ k, a k ≠ 0
  · have h_recOut : FrogModel.Engine.recOut (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w) =
        fun k => (o k : ℕ∞) := h_iff.mp h
    simp [h, h_recOut]
  · have h_recOut : FrogModel.Engine.recOut (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w) ≠
        fun k => (o k : ℕ∞) := by
      intro h_eq; apply h; exact h_iff.mpr h_eq
    simp [h, h_recOut]

/-- A set of the form `{u | g (cstep s u) = y}` is measurable. -/
theorem FrogModel.Engine.measurableSet_comp_cstep_eq {S U T : Type*} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (g : ℕ × S → T) (s : S) (y : T) : MeasurableSet {u | g (cstep s u) = y} := by
  have e : {u | g (cstep s u) = y} = ⋃ r ∈ {r | g r = y}, {u | cstep s u = r} := by
    ext u; simp
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun r _ => hc s r

/-- The set of inputs sending the root chain from `x` to `y` is measurable. -/
theorem FrogModel.Engine.measurableSet_rstep_eq {S U : Type*} {d J : ℕ} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (x y : FrogModel.Engine.RState S d J) :
    MeasurableSet {ξ : Fin (d + 1) × U | FrogModel.Engine.rstep cstep x ξ = y} := by
  have e : {ξ : Fin (d + 1) × U | FrogModel.Engine.rstep cstep x ξ = y} =
      ⋃ a : Fin (d + 1), Prod.fst ⁻¹' {a} ∩
        Prod.snd ⁻¹' {u | FrogModel.Engine.rstep cstep x (a, u) = y} := by
    ext ⟨a, u⟩; simp
  rw [e]
  refine MeasurableSet.iUnion fun a =>
    (measurable_fst (measurableSet_singleton a)).inter (measurable_snd ?_)
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨c, rfl⟩
  · have h : ∀ u u' : U, FrogModel.Engine.rstep cstep x (0, u) =
        FrogModel.Engine.rstep cstep x (0, u') := by
      intro u u'
      simp [FrogModel.Engine.rstep, FrogModel.Engine.move]
    have e0 : {u | FrogModel.Engine.rstep cstep x (0, u) = y} =
        {_u | ∃ u, FrogModel.Engine.rstep cstep x (0, u) = y} := by
      ext u
      exact ⟨fun hu => ⟨u, hu⟩, fun ⟨u', hu'⟩ => (h u u').trans hu'⟩
    rw [e0]
    exact MeasurableSet.const _
  · have h : ∀ u : U, FrogModel.Engine.rstep cstep x (c.succ, u) =
        FrogModel.Engine.rstep (fun _ (_ : Unit) => cstep (x.σ c) u) x (c.succ, ()) := by
      intro u
      simp [FrogModel.Engine.rstep, FrogModel.Engine.move]
    simp only [h]
    exact FrogModel.Engine.measurableSet_comp_cstep_eq cstep hc
      (fun r => FrogModel.Engine.rstep (fun _ (_ : Unit) => r) x (c.succ, ())) (x.σ c) y

theorem FrogModel.Engine.measurable_absorbAt {S U : Type*} {d J : ℕ} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (o : Fin J → ℕ) (x : FrogModel.Engine.RState S d J) :
    Measurable (FrogModel.Engine.absorbAt cstep o x) := by
  have h_meas : ∀ y : FrogModel.Engine.RState S d J,
      MeasurableSet {ξ : Fin (d + 1) × U | FrogModel.Engine.rstep cstep x ξ = y} := by
    intro y
    exact FrogModel.Engine.measurableSet_rstep_eq cstep hc x y
  have hA : MeasurableSet {ξ : Fin (d + 1) × U | x.i < J ∧ J ≤ (FrogModel.Engine.rstep cstep x ξ).i ∧
      (FrogModel.Engine.rstep cstep x ξ).out = fun k => (o k : ℕ∞)} := by
    have h_union : {ξ : Fin (d + 1) × U | x.i < J ∧ J ≤ (FrogModel.Engine.rstep cstep x ξ).i ∧
        (FrogModel.Engine.rstep cstep x ξ).out = fun k => (o k : ℕ∞)} =
        ⋃ (y : FrogModel.Engine.RState S d J), {ξ : Fin (d + 1) × U |
          FrogModel.Engine.rstep cstep x ξ = y ∧ x.i < J ∧ J ≤ y.i ∧ y.out = fun k => (o k : ℕ∞)} := by
      ext ξ
      constructor
      · rintro ⟨hi, hJ, hout⟩
        refine Set.mem_iUnion.mpr ⟨FrogModel.Engine.rstep cstep x ξ, ?_⟩
        simp [hi, hJ, hout]
      · intro h
        rcases Set.mem_iUnion.mp h with ⟨y, h_mem⟩
        simp only [Set.mem_ofPred_eq] at h_mem
        rcases h_mem with ⟨h_eq, hi, hJ, hout⟩
        have hi' : (FrogModel.Engine.rstep cstep x ξ).i = y.i := by rw [h_eq]
        have hout' : (FrogModel.Engine.rstep cstep x ξ).out = y.out := by rw [h_eq]
        simp [hi', hout', hi, hJ, hout]
    rw [h_union]
    refine MeasurableSet.iUnion fun y => ?_
    have h_meas_y : MeasurableSet {ξ : Fin (d + 1) × U |
        FrogModel.Engine.rstep cstep x ξ = y} := h_meas y
    have h_fixed : MeasurableSet {ξ : Fin (d + 1) × U |
        x.i < J ∧ J ≤ y.i ∧ y.out = fun k => (o k : ℕ∞)} := by
      -- This set does not depend on ξ, so it's either ∅ or the whole space
      by_cases h_cond : x.i < J ∧ J ≤ y.i ∧ y.out = fun k => (o k : ℕ∞)
      · have : {ξ : Fin (d + 1) × U | x.i < J ∧ J ≤ y.i ∧ y.out = fun k => (o k : ℕ∞)} = Set.univ := by
          ext ξ; simp [h_cond]
        rw [this]
        exact MeasurableSet.univ
      · have : {ξ : Fin (d + 1) × U | x.i < J ∧ J ≤ y.i ∧ y.out = fun k => (o k : ℕ∞)} = ∅ := by
          ext ξ; simp [h_cond]
        rw [this]
        exact MeasurableSet.empty
    -- Intersection of two measurable sets is measurable
    exact MeasurableSet.inter h_meas_y h_fixed
  have h_eq : FrogModel.Engine.absorbAt cstep o x = fun ξ => if ξ ∈ {ξ : Fin (d + 1) × U |
      x.i < J ∧ J ≤ (FrogModel.Engine.rstep cstep x ξ).i ∧
      (FrogModel.Engine.rstep cstep x ξ).out = fun k => (o k : ℕ∞)} then (1 : ℝ≥0∞) else 0 := by
    ext ξ
    simp [FrogModel.Engine.absorbAt]
  rw [h_eq]
  exact Measurable.ite hA measurable_const measurable_const

theorem FrogModel.Engine.law_absorb {S U : Type*} {d J : ℕ} [MeasurableSpace U] [Countable S]
    (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] (o : Fin J → ℕ)
    (x : FrogModel.Engine.RState S d J) (hx : FrogModel.Engine.Valid x) (hlive : x.i < J) :
    FrogModel.Engine.iidMeasure ν
        {w | FrogModel.Engine.recOut (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w) =
          fun k => (o k : ℕ∞)} =
      FrogModel.LinSys.least (FrogModel.Engine.fkKernel (FrogModel.Engine.rstep cstep) (fun _ _ => 1) ν)
        (FrogModel.Engine.fkRhs (FrogModel.Engine.absorbAt cstep o) ν) x := by
  let B : Set (ℕ → Fin (d + 1) × U) := {w | FrogModel.Engine.recOut
    (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) x w) = fun k => (o k : ℕ∞)}
  have hF_eq : (fun (w : ℕ → Fin (d + 1) × U) =>
      ⨆ n, FrogModel.Engine.fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
        (FrogModel.Engine.absorbAt cstep o) n x w) =
      B.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext w
    dsimp [B, Set.indicator]
    rw [FrogModel.Engine.iSup_fk_absorb cstep o x hx hlive w]
    split_ifs <;> rfl
  have hF_meas : Measurable (fun (w : ℕ → Fin (d + 1) × U) =>
      ⨆ n, FrogModel.Engine.fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
        (FrogModel.Engine.absorbAt cstep o) n x w) := by
    refine Measurable.iSup ?_
    intro n
    exact FrogModel.Engine.measurable_fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
      (FrogModel.Engine.absorbAt cstep o) (FrogModel.Engine.measurableSet_rstep_eq cstep hc) (by
        intro x; exact measurable_const)
      (FrogModel.Engine.measurable_absorbAt cstep hc o) n x
  have hB_meas : MeasurableSet B := by
    have : B = (fun (w : ℕ → Fin (d + 1) × U) =>
      ⨆ n, FrogModel.Engine.fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
        (FrogModel.Engine.absorbAt cstep o) n x w) ⁻¹' {(1 : ℝ≥0∞)} := by
      ext w
      dsimp [B]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [FrogModel.Engine.iSup_fk_absorb cstep o x hx hlive w]
      split_ifs <;> simp [*]
    rw [this]
    exact hF_meas (measurableSet_singleton _)
  calc
    FrogModel.Engine.iidMeasure ν B = ∫⁻ w, B.indicator (fun _ => (1 : ℝ≥0∞)) w ∂(FrogModel.Engine.iidMeasure ν) :=
      (MeasureTheory.lintegral_indicator_one hB_meas).symm
    _ = ∫⁻ w, ⨆ n, FrogModel.Engine.fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
        (FrogModel.Engine.absorbAt cstep o) n x w ∂(FrogModel.Engine.iidMeasure ν) := by
      rw [hF_eq]
    _ = FrogModel.LinSys.least (FrogModel.Engine.fkKernel (FrogModel.Engine.rstep cstep) (fun _ _ => 1) ν)
        (FrogModel.Engine.fkRhs (FrogModel.Engine.absorbAt cstep o) ν) x := by
      rw [FrogModel.Engine.lintegral_iSup_fk (FrogModel.Engine.rstep cstep) (fun _ _ => 1)
        (FrogModel.Engine.absorbAt cstep o) ν (FrogModel.Engine.measurableSet_rstep_eq cstep hc)
        (by intro x; exact measurable_const)
        (FrogModel.Engine.measurable_absorbAt cstep hc o) x]

open Classical in
theorem FrogModel.LinSys.least_lump {ι κ : Type*} (K : ι → ι → ℝ≥0∞) (K' : κ → κ → ℝ≥0∞)
    (π : ι → κ) (b' : κ → ℝ≥0∞)
    (hK : ∀ i k, ∑' j, (if π j = k then K i j else 0) = K' (π i) k) :
    FrogModel.LinSys.least K (b' ∘ π) = FrogModel.LinSys.least K' b' ∘ π := by
  have h_iter : ∀ n, FrogModel.LinSys.iter K (b' ∘ π) n = FrogModel.LinSys.iter K' b' n ∘ π := by
    intro n
    induction' n with n ih
    · ext i; simp [FrogModel.LinSys.iter]
    · ext i
      simp [FrogModel.LinSys.iter, ih, FrogModel.LinSys.app]
      apply congrArg (fun t => b' (π i) + t)
      calc
        ∑' j, K i j * FrogModel.LinSys.iter K' b' n (π j)
            = ∑' j, ∑' k, (if π j = k then K i j * FrogModel.LinSys.iter K' b' n k else 0) := by
              refine tsum_congr (fun j => ?_)
              simp [eq_comm, tsum_ite_eq (π j) (fun k => K i j * FrogModel.LinSys.iter K' b' n k)]
        _ = ∑' k, ∑' j, (if π j = k then K i j * FrogModel.LinSys.iter K' b' n k else 0) := by
              rw [ENNReal.tsum_comm]
        _ = ∑' k, (∑' j, (if π j = k then K i j else 0)) * FrogModel.LinSys.iter K' b' n k := by
              refine tsum_congr (fun k => ?_)
              have h_mul : (fun j => (if π j = k then K i j * FrogModel.LinSys.iter K' b' n k else 0)) =
                  (fun j => (if π j = k then K i j else 0) * FrogModel.LinSys.iter K' b' n k) := by
                ext j; split <;> simp
              rw [h_mul, ENNReal.tsum_mul_right]
        _ = ∑' k, K' (π i) k * FrogModel.LinSys.iter K' b' n k := by
              refine tsum_congr (fun k => ?_)
              rw [hK i k]
  ext i
  simp [FrogModel.LinSys.least, h_iter]

open Filter ProbabilityTheory in
theorem FrogModel.Engine.ae_exitCount_unbounded {U : Type*} {d : ℕ} [MeasurableSpace U]
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] (hν : ν {ξ | ξ.1 = 0} ≠ 0) :
    ∀ᵐ w ∂(FrogModel.Engine.iidMeasure ν), ∀ m, ∃ n, m ≤ FrogModel.Engine.exitCount w n := by
  let μ := FrogModel.Engine.iidMeasure ν
  let A : ℕ → Set (ℕ → Fin (d + 1) × U) := fun k => {w | (w k).1 = 0}
  have hA_meas : ∀ k, MeasurableSet (A k) := by
    intro k
    have h_eq : A k = (fun (w : ℕ → Fin (d + 1) × U) => w k) ⁻¹' {ξ | ξ.1 = 0} := by
      ext w; simp [A]
    rw [h_eq]
    have h_set : MeasurableSet ({ξ | ξ.1 = 0} : Set (Fin (d + 1) × U)) := by
      have : {ξ | ξ.1 = 0} = (fun (ξ : Fin (d + 1) × U) => ξ.1) ⁻¹' {0} := by
        ext ξ; simp
      rw [this]
      exact (measurable_fst) (MeasurableSet.of_discrete)
    exact (measurable_pi_apply k) h_set
  have h_indep_fun : iIndepFun (fun (i : ℕ) (ω : ℕ → Fin (d + 1) × U) => ω i) μ := by
    unfold μ FrogModel.Engine.iidMeasure
    apply iIndepFun_infinitePi (X := fun (i : ℕ) (x : Fin (d + 1) × U) => x)
    intro i
    exact measurable_id
  let c := ν {ξ | ξ.1 = 0}
  have hc_ne_zero : c ≠ 0 := hν
  have hA_meas_c : ∀ k, μ (A k) = c := by
    intro k
    have h_eq : A k = (fun (w : ℕ → Fin (d + 1) × U) => w k) ⁻¹' {ξ | ξ.1 = 0} := by
      ext w; simp [A]
    rw [h_eq]
    have h_mp : MeasurePreserving (fun (w : ℕ → Fin (d + 1) × U) => w k) μ ν := by
      simpa [μ, FrogModel.Engine.iidMeasure] using
        measurePreserving_eval_infinitePi (fun _ : ℕ => ν) k
    have h_set : MeasurableSet ({ξ | ξ.1 = 0} : Set (Fin (d + 1) × U)) := by
      have : {ξ | ξ.1 = 0} = (fun (ξ : Fin (d + 1) × U) => ξ.1) ⁻¹' {0} := by
        ext ξ; simp
      rw [this]
      exact (measurable_fst) (MeasurableSet.of_discrete)
    have h_null_meas : NullMeasurableSet ({ξ | ξ.1 = 0} : Set (Fin (d + 1) × U)) ν :=
      h_set.nullMeasurableSet
    rw [h_mp.measure_preimage h_null_meas]
  have h_sum : (∑' k, μ (A k)) = ∞ := by
    simp_rw [hA_meas_c]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hc_ne_zero
  have h_indep_set : iIndepSet A μ := by
    rw [iIndepSet_iff_meas_biInter hA_meas]
    intro s
    have h := (iIndepFun_iff_measure_inter_preimage_eq_mul
      (β := fun (_ : ℕ) => Fin (d + 1) × U)
      (m := fun (_ : ℕ) => by infer_instance)
      (f := fun (i : ℕ) (ω : ℕ → Fin (d + 1) × U) => ω i)).mp h_indep_fun
    have h_meas_set : MeasurableSet ({ξ | ξ.1 = 0} : Set (Fin (d + 1) × U)) := by
      have : {ξ | ξ.1 = 0} = (fun (ξ : Fin (d + 1) × U) => ξ.1) ⁻¹' {0} := by
        ext ξ; simp
      rw [this]
      exact (measurable_fst) (MeasurableSet.of_discrete)
    have h_inter := h s (sets := fun _ => {ξ | ξ.1 = 0}) (by
      intro i hi
      exact h_meas_set)
    simpa [A] using h_inter
  have : IsProbabilityMeasure μ := by
    unfold μ FrogModel.Engine.iidMeasure; infer_instance
  have h_limsup : μ (limsup A atTop) = 1 :=
    measure_limsup_eq_one hA_meas h_indep_set h_sum
  have h_ae : ∀ᵐ w ∂μ, w ∈ limsup A atTop := by
    rw [ae_iff]
    have h_meas_limsup : MeasurableSet (limsup A atTop) :=
      MeasurableSet.measurableSet_limsup hA_meas
    have h_fin : μ (limsup A atTop) ≠ ⊤ := by rw [h_limsup]; exact ENNReal.one_ne_top
    have h_compl_null : μ ((limsup A atTop)ᶜ) = 0 := by
      rw [measure_compl h_meas_limsup h_fin, h_limsup, measure_univ]
      simp
    have h_set : {w | ¬ w ∈ limsup A atTop} = (limsup A atTop)ᶜ := by
      ext ω; simp
    rw [h_set, h_compl_null]
  filter_upwards [h_ae] with w hw
  intro m
  rw [mem_limsup_iff_frequently_mem] at hw
  rw [Nat.frequently_atTop_iff_infinite] at hw
  obtain ⟨t, ht_sub, ht_card⟩ := Set.Infinite.exists_subset_card_eq hw m
  by_cases hm : m = 0
  · subst hm; refine ⟨0, ?_⟩; simp [FrogModel.Engine.exitCount]
  · have ht_nonempty : t.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty; rw [h_empty, Finset.card_empty] at ht_card; exact hm ht_card.symm
    let n := t.max' ht_nonempty + 1
    have hn : ∀ k ∈ t, k < n := by
      intro k hk
      have h_le := Finset.le_max' t k hk
      omega
    have h_sub : t ⊆ (Finset.range n).filter (fun k => (w k).1 = 0) := by
      intro k hk
      have hk_mem_set : k ∈ {n' | w ∈ A n'} := ht_sub (by simpa using hk)
      have hk_mem_A : w ∈ A k := by simpa [A] using hk_mem_set
      have hk_lt_n : k < n := hn k hk
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hk_lt_n, hk_mem_A⟩
    refine ⟨n, ?_⟩
    have h_card_le : t.card ≤ ((Finset.range n).filter (fun k => (w k).1 = 0)).card :=
      Finset.card_le_card h_sub
    rw [← ht_card]
    simpa [FrogModel.Engine.exitCount] using h_card_le
