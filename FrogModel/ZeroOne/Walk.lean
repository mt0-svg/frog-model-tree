module

public import FrogModel.ZeroOne.Defs
public import FrogModel.Pieces.Basic

@[expose] public section

/-!
# Walks: the root frog reaches every depth, exit times, the planted tree at any vertex

Facts on walks for the proof of Theorem 9.3 of the paper.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.ZeroOne

/-- Steps to a child: `m` steps whose second component is nonzero raise the depth by `m`. -/
theorem FrogModel.ZeroOne.length_walk_add {d : ℕ} (u : Vertex d) (x : ℕ → Step d) (k m : ℕ)
    (h : ∀ j < m, (x (k + j)).2 ≠ 0) :
    (walk u x (k + m)).length = (walk u x k).length + m := by
  induction' m with m ih
  · simp
  · have hx : (x (k + m)).2 ≠ 0 := h m (by omega)
    have h' : ∀ j < m, (x (k + j)).2 ≠ 0 := fun j hj => h j (by omega)
    rw [Nat.add_succ]
    rw [walk]
    cases hwalk : walk u x (k + m) with
    | nil =>
      simp [step]
      have ih_len := ih h'
      have hlen : (walk u x (k + m)).length = 0 := by simp [hwalk]
      rw [hlen] at ih_len
      omega
    | cons c w =>
      simp [step, hx]
      have ih_len := ih h'
      rw [hwalk] at ih_len
      simp at ih_len
      rw [ih_len]
      omega

/-- The depth of the walk from the root moves by one at each step: a walk at depth `≥ m` at
time `t` was at depth exactly `m` at some time `≤ t`. -/
theorem FrogModel.ZeroOne.exists_length_eq {d : ℕ} (x : ℕ → Step d) (t m : ℕ)
    (h : m ≤ (walk root x t).length) :
    ∃ s ≤ t, (walk root x s).length = m := by
  have h_step_len (v : Vertex d) (ξ : Step d) : (step v ξ).length = v.length + 1 ∨ (step v ξ).length + 1 = v.length := by
    cases v with
    | nil =>
      simp [step]
    | cons c w =>
      simp only [step]
      split_ifs with h_eq
      · right; simp
      · left; simp
  induction' t with t ih
  · -- t = 0
    have h0 : (walk root x 0).length = 0 := by
      simp [walk, root]
    have hm0 : m = 0 := by omega
    subst hm0
    exact ⟨0, le_rfl, h0⟩
  · -- t = t + 1
    by_cases hm : m ≤ (walk root x t).length
    · -- m ≤ length at t, use IH
      rcases ih hm with ⟨s, hs, hs_eq⟩
      exact ⟨s, Nat.le_trans hs (Nat.le_succ t), hs_eq⟩
    · -- (walk root x t).length < m ≤ (walk root x (t+1)).length
      have h_lt : (walk root x t).length < m := by omega
      have h_le : m ≤ (walk root x (t + 1)).length := h
      -- The step changes the length by exactly one
      have h_step_len' := h_step_len (walk root x t) (x t)
      rcases h_step_len' with (h_add | h_sub)
      · -- (step ...).length = (walk ...).length + 1
        have h_add' : (walk root x (t + 1)).length = (walk root x t).length + 1 := by
          simpa [walk] using h_add
        have hm_eq : m = (walk root x (t + 1)).length := by omega
        subst hm_eq
        exact ⟨t + 1, le_rfl, rfl⟩
      · -- (step ...).length + 1 = (walk ...).length
        have h_sub' : (walk root x (t + 1)).length + 1 = (walk root x t).length := by
          simpa [walk] using h_sub
        -- But we have (walk root x t).length < m ≤ (walk root x (t+1)).length
        -- This is impossible: (walk root x (t+1)).length + 1 = (walk root x t).length < m ≤ (walk root x (t+1)).length
        omega

/-- A step goes to a child, away from the root, with probability `d / (d + 1)`. -/
theorem FrogModel.ZeroOne.stepLaw_snd_ne_zero {d : ℕ} [NeZero d] :
    stepLaw d {ξ : Step d | ξ.2 ≠ 0} = (d : ℝ≥0∞) / (d + 1) := by
  rw [stepLaw, ProbabilityTheory.uniformOn_univ]
  have hs : {ξ : Step d | ξ.2 ≠ 0} =
      ((Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ.erase (0 : Fin (d + 1))) :
        Finset (Step d)) := by
    ext ξ
    simp
  rw [hs, Measure.count_apply_finset, Finset.card_product, Finset.card_univ,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.add_sub_cancel]
  push_cast
  exact ENNReal.mul_div_mul_left _ _ (by simp [NeZero.ne d]) (ENNReal.natCast_ne_top d)

/-- The first `K` blocks of `m` steps each contain a step whose second component is `0` with
probability `(1 - (d / (d + 1))^m)^K`. -/
theorem FrogModel.ZeroOne.measure_no_block {d : ℕ} [NeZero d] (m K : ℕ) :
    (Measure.infinitePi fun _ : ℕ => stepLaw d)
        {x | ∀ i < K, ∃ j < m, (x (i * m + j)).2 = 0} =
      (1 - ((d : ℝ≥0∞) / (d + 1)) ^ m) ^ K := by
  set μ := Measure.infinitePi fun _ : ℕ => stepLaw d with hμ
  set p := ((d : ℝ≥0∞) / (d + 1)) ^ m with hp
  have hp1 : p ≤ 1 := pow_le_one₀ (zero_le) (ENNReal.div_le_of_le_mul (by simp))
  induction K with
  | zero => simp
  | succ K ih =>
    set G := {x : ℕ → Step d | ∀ i < K, ∃ j < m, (x (i * m + j)).2 = 0} with hGdef
    set B := (Finset.range m).image (fun j => K * m + j) with hBdef
    set C := {x : ℕ → Step d | ∀ k ∈ B, x k ∈ {ξ : Step d | ξ.2 ≠ 0}} with hCdef
    have hGm : MeasurableSet G := by
      have : G = ⋂ i ∈ Finset.range K, ⋃ j ∈ Finset.range m,
          (fun x : ℕ → Step d => x (i * m + j)) ⁻¹' {ξ : Step d | ξ.2 = 0} := by
        ext x
        simp [G]
      rw [this]
      exact Finset.measurableSet_biInter _ fun i _ => Finset.measurableSet_biUnion _ fun j _ =>
        measurable_pi_apply _ (Set.toFinite _).measurableSet
    have hCm : MeasurableSet C := by
      have : C = ⋂ k ∈ B, (fun x : ℕ → Step d => x k) ⁻¹' {ξ : Step d | ξ.2 ≠ 0} := by
        ext x
        simp [C]
      rw [this]
      exact Finset.measurableSet_biInter _ fun k _ =>
        measurable_pi_apply _ (Set.toFinite _).measurableSet
    have hins : ∀ ω ω' : ℕ → Step d, (∀ i ∉ B, ω i = ω' i) → (ω ∈ G ↔ ω' ∈ G) := by
      have key : ∀ i < K, ∀ j < m, i * m + j ∉ B := by
        intro i hi j hj hB
        obtain ⟨j', hj', heq⟩ := Finset.mem_image.1 hB
        have h1 : (i + 1) * m ≤ K * m := Nat.mul_le_mul_right m hi
        have h2 : (i + 1) * m = i * m + m := Nat.succ_mul i m
        omega
      intro ω ω' h
      simp only [G, Set.mem_ofPred_eq]
      constructor
      · intro hω i hi
        obtain ⟨j, hj, h0⟩ := hω i hi
        exact ⟨j, hj, by rw [← h _ (key i hi j hj)]; exact h0⟩
      · intro hω i hi
        obtain ⟨j, hj, h0⟩ := hω i hi
        exact ⟨j, hj, by rw [h _ (key i hi j hj)]; exact h0⟩
    have hcyl : μ (G ∩ C) = μ G * p := by
      rw [hCdef, Stage.infinitePi_inter_cyl (fun _ => stepLaw d) B G hGm hins
        (fun _ => {ξ : Step d | ξ.2 ≠ 0}) (fun _ => (Set.toFinite _).measurableSet),
        Finset.prod_const, Finset.card_image_of_injective _ (add_right_injective (K * m)),
        Finset.card_range, stepLaw_snd_ne_zero]
    have hset : {x : ℕ → Step d | ∀ i < K + 1, ∃ j < m, (x (i * m + j)).2 = 0} =
        G \ (G ∩ C) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff, not_and]
      constructor
      · intro h
        refine ⟨fun i hi => h i (by omega), fun _ hC => ?_⟩
        obtain ⟨j, hj, hj0⟩ := h K (by omega)
        exact hC (K * m + j) (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩) hj0
      · rintro ⟨hG, hnot⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hG i hi
        · by_contra hcon
          push Not at hcon
          exact hnot hG fun k hk => by
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
            exact hcon j (Finset.mem_range.1 hj)
    rw [hset, measure_sdiff Set.inter_subset_left (hGm.inter hCm).nullMeasurableSet
      (measure_ne_top _ _), hcyl, ih, pow_succ]
    rw [ENNReal.mul_sub (fun _ _ => ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
      tsub_le_self)), mul_one]

/-- The walk from the root reaches every depth almost surely. -/
theorem FrogModel.ZeroOne.firstDeep_ne_none {d : ℕ} [NeZero d] (m : ℕ) :
    (Measure.infinitePi fun _ : ℕ => stepLaw d) {x | firstDeep m x = none} = 0 := by
  set μ := Measure.infinitePi fun _ : ℕ => stepLaw d
  set p := ((d : ℝ≥0∞) / (d + 1)) ^ m
  have hd_ne_zero : (d : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast NeZero.pos d |>.ne'
  have hd_add_one_ne_zero : (d : ℝ≥0∞) + 1 ≠ 0 := by
    positivity
  have hd_add_one_ne_top : (d : ℝ≥0∞) + 1 ≠ ⊤ := by
    simp
  have h_div_pos : 0 < (d : ℝ≥0∞) / (d + 1) :=
    ENNReal.div_pos hd_ne_zero hd_add_one_ne_top
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have h_div_le_one : (d : ℝ≥0∞) / (d + 1) ≤ 1 := by
    refine (ENNReal.div_le_iff (y := (d : ℝ≥0∞) + 1) hd_add_one_ne_zero hd_add_one_ne_top).mpr ?_
    calc
      (d : ℝ≥0∞) ≤ (d : ℝ≥0∞) + 1 := le_add_of_nonneg_right (by norm_num)
      _ = 1 * ((d : ℝ≥0∞) + 1) := by simp
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    have h := ENNReal.pow_le_pow_left h_div_le_one (n := m)
    simpa [one_pow] using h
  have h_sub : ∀ K, {x : ℕ → Step d | firstDeep m x = none} ⊆ {x : ℕ → Step d | ∀ i < K, ∃ j < m, (x (i * m + j)).2 = 0} := by
    intro K x hx
    have h_no_depth : ¬∃ t, (walk root x t).length = m := by
      dsimp [firstDeep] at hx
      rintro ⟨t, ht⟩
      have h_exists : ∃ t, (walk root x t).length = m := ⟨t, ht⟩
      rw [dite_eq_left h_exists] at hx
      exact Option.some_ne_none _ hx
    intro i hi
    by_contra! h_all
    -- h_all: ∀ j < m, (x (i * m + j)).2 ≠ 0
    have h_len : (walk root x (i * m + m)).length = (walk root x (i * m)).length + m := by
      apply length_walk_add root x (i * m) m
      intro j hj
      exact h_all j hj
    have h_len_ge : m ≤ (walk root x (i * m + m)).length := by
      rw [h_len]
      exact Nat.le_add_left m _
    rcases exists_length_eq x (i * m + m) m h_len_ge with ⟨s, _, hs⟩
    apply h_no_depth
    exact ⟨s, hs⟩
  have h_le : ∀ K, μ {x | firstDeep m x = none} ≤ (1 - p) ^ K := by
    intro K
    calc
      μ {x | firstDeep m x = none} ≤ μ {x | ∀ i < K, ∃ j < m, (x (i * m + j)).2 = 0} :=
        measure_mono (h_sub K)
      _ = (1 - p) ^ K := by
        rw [measure_no_block m K]
  have h_one_minus_p_lt_one : 1 - p < 1 :=
    ENNReal.sub_lt_self (by norm_num) (by norm_num) hp_pos.ne'
  have h_tendsto : Filter.Tendsto (fun (K : ℕ) => (1 - p) ^ K) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h_one_minus_p_lt_one
  have h_le_zero : μ {x | firstDeep m x = none} ≤ 0 := by
    -- Using ge_of_tendsto' : if f K → 0 and b ≤ f K for all K, then b ≤ 0
    have := ge_of_tendsto' h_tendsto h_le
    exact this
  exact le_antisymm h_le_zero (zero_le (a := μ {x | firstDeep m x = none}))

/-- The first vertex at depth `m` is at depth `m` and on the walk. -/
theorem FrogModel.ZeroOne.firstDeep_spec {d : ℕ} (m : ℕ) (x : ℕ → Step d) (w : Vertex d)
    (h : firstDeep m x = some w) :
    w.length = m ∧ ∃ t, walk root x t = w := by
  unfold firstDeep at h
  split_ifs at h with hex
  · -- h : some (walk root x (Nat.find hex)) = some w
    have h_eq : walk root x (Nat.find hex) = w := Option.some.inj h
    refine ⟨?_, ?_⟩
    · rw [← h_eq]
      exact Nat.find_spec hex
    · exact ⟨Nat.find hex, h_eq⟩

/-- The first vertex at depth `m` is a measurable function of the steps. -/
theorem FrogModel.ZeroOne.measurableSet_firstDeep {d : ℕ} (m : ℕ) (o : Option (Vertex d)) :
    MeasurableSet {x : ℕ → Step d | firstDeep m x = o} := by
  have hw : ∀ t, Measurable fun x : ℕ → Step d => walk root x t := fun t =>
    (measurable_pi_apply t).comp (measurable_walk root)
  have hL : ∀ t, MeasurableSet {x : ℕ → Step d | (walk root x t).length = m} := fun t =>
    hw t (MeasurableSet.of_discrete (s := {u : Vertex d | u.length = m}))
  have hE : ∀ t (w : Vertex d), MeasurableSet {x : ℕ → Step d | walk root x t = w} :=
    fun t w => hw t (measurableSet_singleton w)
  cases o with
  | none =>
    have : {x : ℕ → Step d | firstDeep m x = none} =
        ⋂ t, {x | (walk root x t).length = m}ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, firstDeep]
      split_ifs with h
      · simp only [false_iff, not_forall, not_not]
        exact h
      · simp only [true_iff]
        push Not at h
        exact h
    rw [this]
    exact MeasurableSet.iInter fun t => (hL t).compl
  | some w =>
    have : {x : ℕ → Step d | firstDeep m x = some w} =
        ⋃ t, ({x | walk root x t = w} ∩ {x | (walk root x t).length = m} ∩
          ⋂ s ∈ Finset.range t, {x | (walk root x s).length = m}ᶜ) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_range, firstDeep]
      split_ifs with h
      · rw [Option.some.injEq]
        constructor
        · intro hx
          exact ⟨Nat.find h, ⟨hx, Nat.find_spec h⟩, fun s hs => Nat.find_min h hs⟩
        · rintro ⟨t, ⟨hwt, hl⟩, hmin⟩
          have ht : Nat.find h = t := (Nat.find_eq_iff h).2 ⟨hl, fun s hs => hmin s hs⟩
          rw [ht, hwt]
      · simp only [false_iff, not_exists, not_and]
        push Not at h
        rintro t ⟨_, hl⟩ _
        exact h t hl
    rw [this]
    exact MeasurableSet.iUnion fun t => ((hE t w).inter (hL t)).inter
      (MeasurableSet.biInter (Finset.range t).countable_toSet fun s _ => (hL s).compl)

theorem FrogModel.ZeroOne.walkStar_prefix {d : ℕ} (v : Option (Vertex d)) (a a' : ℕ → Step d)
    (n : ℕ)
    (h : ∀ i < n, a i = a' i) : walkStar v a n = walkStar v a' n := by
  induction' n with n ih
  · rfl
  · simp [walkStar, ih (fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi))), h n (Nat.lt_succ_self n)]


/-- The exit time is a stopping time. -/
theorem FrogModel.ZeroOne.exitTime_eq_of_prefix {d : ℕ} (v : Vertex d) (a a' : ℕ → Step d)
    (k : ℕ) (h : exitTime v a = k) (ha : ∀ i < k, a i = a' i) :
    exitTime v a' = k := by
  let S : Set ℕ := {n | walkStar (some v) a n = none}
  have hS_nonempty : S.Nonempty := by
    by_contra h_empty
    have h_empty' : (fun (n : ℕ) => (n : ℕ∞)) '' S = (∅ : Set ℕ∞) := by
      rw [Set.image_eq_empty, Set.not_nonempty_iff_eq_empty.mp h_empty]
    have h_sInf_empty : sInf ((fun (n : ℕ) => (n : ℕ∞)) '' S) = (⊤ : ℕ∞) := by
      simp [h_empty']
    have h_exitTime_eq : exitTime v a = sInf ((fun (n : ℕ) => (n : ℕ∞)) '' S) := rfl
    rw [h_exitTime_eq, h_sInf_empty] at h
    have hk_ne_top : (k : ℕ∞) ≠ (⊤ : ℕ∞) := by
      simp
    exact hk_ne_top h.symm
  have h_bddBelow : BddBelow S := OrderBot.bddBelow S
  have h_coe_sInf : ((sInf S : ℕ) : ℕ∞) = (k : ℕ∞) := by
    calc
      ((sInf S : ℕ) : ℕ∞) = sInf ((fun (n : ℕ) => (n : ℕ∞)) '' S) :=
        WithTop.coe_sInf' hS_nonempty h_bddBelow
      _ = (k : ℕ∞) := by
        show exitTime v a = (k : ℕ∞)
        rw [h]
  have h_sInf_S_eq_k : sInf S = k :=
    ENat.natCast_inj.mp h_coe_sInf
  have h_isLeast : IsLeast S k := by
    have h_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
    have h_le : ∀ m ∈ S, sInf S ≤ m := fun m hm => Nat.sInf_le hm
    rw [h_sInf_S_eq_k] at h_mem h_le
    exact ⟨h_mem, h_le⟩
  have h_walkStar_k : walkStar (some v) a k = none := h_isLeast.1
  have h_walkStar_lt : ∀ i < k, walkStar (some v) a i ≠ none := by
    intro i hi h_eq
    have hi_mem : i ∈ S := h_eq
    have h_le : k ≤ i := h_isLeast.2 hi_mem
    linarith
  have h_walkStar_prefix : ∀ n, n ≤ k → walkStar (some v) a n = walkStar (some v) a' n := by
    intro n hn
    apply walkStar_prefix (some v) a a' n
    intro i hi
    apply ha i
    exact lt_of_lt_of_le hi hn
  have h_walkStar_k' : walkStar (some v) a' k = none := by
    rw [← h_walkStar_prefix k (le_refl k), h_walkStar_k]
  have h_walkStar_lt' : ∀ i < k, walkStar (some v) a' i ≠ none := by
    intro i hi
    rw [← h_walkStar_prefix i (Nat.le_of_lt hi)]
    exact h_walkStar_lt i hi
  let S' : Set ℕ := {n | walkStar (some v) a' n = none}
  have hk_mem_S' : k ∈ S' := h_walkStar_k'
  have hS'_nonempty : S'.Nonempty := ⟨k, hk_mem_S'⟩
  have h_isLeast_S' : IsLeast S' k := by
    refine ⟨hk_mem_S', ?_⟩
    intro m hm
    by_contra h_lt
    have hm_lt_k : m < k := by omega
    have h_ne_none : walkStar (some v) a' m ≠ none := h_walkStar_lt' m hm_lt_k
    exact h_ne_none hm
  have h_sInf_S'_eq_k : sInf S' = k := h_isLeast_S'.csInf_eq
  have h_bddBelow_S' : BddBelow S' := OrderBot.bddBelow S'
  calc
    exitTime v a' = sInf ((fun (n : ℕ) => (n : ℕ∞)) '' S') := rfl
    _ = ((sInf S' : ℕ) : ℕ∞) :=
      (WithTop.coe_sInf' hS'_nonempty h_bddBelow_S').symm
    _ = (k : ℕ∞) := by rw [h_sInf_S'_eq_k]

/-- At a finite exit time the walk on `T*` is at the leaf, and not before. -/
theorem FrogModel.ZeroOne.exitTime_spec {d : ℕ} (v : Vertex d) (x : ℕ → Step d) (k : ℕ)
    (h : exitTime v x = k) :
    walkStar (some v) x k = none ∧ ∀ i < k, walkStar (some v) x i ≠ none := by
  set S : Set ℕ := {n | walkStar (some v) x n = none} with hS
  have h_exit_def : exitTime v x = sInf ((fun n : ℕ => (n : ℕ∞)) '' S) := rfl
  rw [h_exit_def] at h
  -- h : sInf ((fun n : ℕ => (n : ℕ∞)) '' S) = (k : ℕ∞)
  have hS_nonempty : S.Nonempty := by
    by_contra! h_empty
    have h_empty' : ((fun n : ℕ => (n : ℕ∞)) '' S) = (∅ : Set ℕ∞) := by
      rw [Set.image_eq_empty]
      exact h_empty
    rw [h_empty', sInf_empty] at h
    have : (k : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top _
    exact this h.symm
  have h_sInf_eq : (sInf S : ℕ) = k := by
    have h_image : sInf ((fun n : ℕ => (n : ℕ∞)) '' S) = ⨅ a ∈ S, (a : ℕ∞) := by
      rw [sInf_image]
    rw [h_image] at h
    have h_coe : ((sInf S : ℕ) : ℕ∞) = ⨅ a ∈ S, (a : ℕ∞) := ENat.natCast_sInf hS_nonempty
    rw [← h_coe] at h
    exact (Nat.cast_inj (R := ℕ∞)).mp h
  have hk_mem : k ∈ S := by
    rw [hS]
    have : sInf S ∈ S := Nat.sInf_mem hS_nonempty
    rw [← h_sInf_eq]
    exact this
  have h_not_mem : ∀ i < k, i ∉ S := by
    intro i hi
    have : i < sInf S := by
      rw [h_sInf_eq]
      exact hi
    exact Nat.notMem_of_lt_sInf this
  constructor
  · rw [hS] at hk_mem
    exact hk_mem
  · intro i hi
    have : i ∉ S := h_not_mem i hi
    rw [hS] at this
    exact this

theorem FrogModel.ZeroOne.exitTime_ne_top_iff {d : ℕ} (v : Vertex d) (x : ℕ → Step d) :
    exitTime v x ≠ ⊤ ↔ ∃ n, walkStar (some v) x n = none := by
  let S : Set ℕ := {n | walkStar (some v) x n = none}
  have h_exitTime : exitTime v x = sInf ((fun n : ℕ => (n : ℕ∞)) '' S) := rfl
  constructor
  · intro h
    by_contra hS_empty
    apply h
    rw [h_exitTime]
    have hS_eq_empty : S = ∅ := by
      ext n
      constructor
      · intro hn
        exfalso
        exact hS_empty ⟨n, hn⟩
      · intro hn
        exact hn.elim
    rw [hS_eq_empty, Set.image_empty, sInf_empty]
  · intro h
    rcases h with ⟨n, hn⟩
    rw [h_exitTime]
    have hmem : (n : ℕ∞) ∈ ((fun n : ℕ => (n : ℕ∞)) '' S) := by
      apply Set.mem_image_of_mem
      exact hn
    have hle : sInf ((fun n : ℕ => (n : ℕ∞)) '' S) ≤ (n : ℕ∞) := sInf_le hmem
    have hlt : (n : ℕ∞) < ⊤ := by
      simp
    exact ne_of_lt (lt_of_le_of_lt hle hlt)

/-- The exit time is measurable. -/
theorem FrogModel.ZeroOne.measurable_exitTime {d : ℕ} (v : Vertex d) :
    Measurable (exitTime (d := d) v) := by
  have hW : ∀ n, MeasurableSet {x : ℕ → Step d | walkStar (some v) x n = none} := fun n =>
    FrogModel.measurable_walkStar_at d v n (measurableSet_singleton none)
  refine measurable_to_countable' fun e => ?_
  induction e using ENat.recTopCoe with
  | top =>
    have : exitTime (d := d) v ⁻¹' {⊤} = ⋂ n, {x | walkStar (some v) x n = none}ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_ofPred_eq]
      constructor
      · intro h n hn
        exact (FrogModel.ZeroOne.exitTime_ne_top_iff v x).2 ⟨n, hn⟩ h
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := (FrogModel.ZeroOne.exitTime_ne_top_iff v x).1 hne
        exact h n hn
    rw [this]
    exact MeasurableSet.iInter fun n => (hW n).compl
  | coe k =>
    have : exitTime (d := d) v ⁻¹' {(k : ℕ∞)} = {x | walkStar (some v) x k = none} ∩
        ⋂ i ∈ Finset.range k, {x | walkStar (some v) x i = none}ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.mem_range]
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := FrogModel.ZeroOne.exitTime_spec v x k h
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        unfold exitTime
        apply le_antisymm
        · exact sInf_le ⟨k, h1, rfl⟩
        · refine le_sInf ?_
          rintro _ ⟨n, hn, rfl⟩
          by_contra hlt
          exact h2 n (by have h3 := not_le.1 hlt; simpa using h3) hn
    rw [this]
    exact (hW k).inter
      (MeasurableSet.biInter (Finset.range k).countable_toSet fun i _ => (hW i).compl)

/-- The subtree at `w ≠ root` and its parent form a copy of `T*`: before its exit, the walk on
`T*` from `some v` is the walk from `v ++ w` with the same steps. -/
theorem FrogModel.ZeroOne.walk_append_embedAt {d : ℕ} (w : Vertex d) (hw : w ≠ [])
    (v : Vertex d) (x : ℕ → Step d) (n : ℕ) (h : ∀ i < n, walkStar (some v) x i ≠ none) :
    walk (v ++ w) x n = embedAt w (walkStar (some v) x n) := by
  have hstep : ∀ (v : Vertex d) (ξ : Step d), step (v ++ w) ξ = embedAt w (stepStar (some v) ξ) := by
    intro v ξ
    obtain ⟨c, w', rfl⟩ := List.exists_cons_of_ne_nil hw
    cases v with
    | nil =>
      simp [step, stepStar, embedAt]
      by_cases hξ : ξ.2 = 0
      · simp [hξ]
      · simp [hξ]
    | cons c' v' =>
      simp [step, stepStar, embedAt]
      by_cases hξ : ξ.2 = 0
      · simp [hξ]
      · simp [hξ]
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : walkStar (some v) x n ≠ none := h n (Nat.lt_succ_self n)
    match w' : walkStar (some v) x n with
    | none => exact (hn w').elim
    | some u =>
      have hn' : ∀ i < n, walkStar (some v) x i ≠ none := by
        intro i hi
        apply h i
        exact Nat.lt_of_lt_of_le hi (Nat.le_succ n)
      rw [walk, walkStar, ih hn', w']
      simp [embedAt, hstep]

/-- From depth `L`, a run of `L` parent steps ends at the root. -/
theorem FrogModel.ZeroOne.walk_upRun {d : ℕ} (u : Vertex d) (x : ℕ → Step d) (k : ℕ)
    (h : upRun (walk u x k).length x k) :
    walk u x (k + (walk u x k).length) = root := by
  induction' hlen : (walk u x k).length with L ih generalizing k
  · -- base case: (walk u x k).length = 0
    have hnil : walk u x k = [] := List.eq_nil_of_length_eq_zero hlen
    simp [hnil, root]
  · -- step case: (walk u x k).length = L.succ
    have hne : walk u x k ≠ [] := by
      intro heq
      rw [heq] at hlen
      simp at hlen
    rcases List.exists_cons_of_ne_nil hne with ⟨c, w, hw⟩
    have hwlen : w.length = L := by
      rw [hw] at hlen
      simpa using hlen
    have hx0 : (x k).2 = 0 := h 0 (by omega)
    have hwalk_succ : walk u x (k + 1) = w := by
      rw [walk, hw]
      simp [step, hx0]
    have h_add : k + L.succ = (k + 1) + L := by omega
    rw [h_add]
    apply ih (k + 1) ?_ ?_
    · -- upRun L x (k + 1)
      intro j hj
      have hj' : j < L := by
        rw [hwalk_succ] at hj
        rwa [hwlen] at hj
      have : (k + 1) + j = k + (j + 1) := by omega
      rw [this]
      apply h (j + 1)
      rw [hlen]
      exact Nat.add_lt_add_right hj' 1
    · -- (walk u x (k + 1)).length = L
      rw [hwalk_succ]
      exact hwlen

/-- The frogs of `T*` at `w` reached from its root are woken when `w` is. -/
theorem FrogModel.ZeroOne.reach_append {d : ℕ} (ω : Sample d) (w : Vertex d) (hw : w ≠ [])
    (hR : Reach (paths ω) w) (v : Vertex d)
    (hv : Relation.ReflTransGen (starArc (shift w ω)) [] v) :
    Reach (paths ω) (v ++ w) := by
  induction hv with
  | refl =>
      simp
      exact hR
  | @tail a b hab hba ih =>
      rcases hba with ⟨_hb_ne, n, hn⟩
      have h_none_lt : ∀ i < n, walkStar (some a) ((shift w ω) a) i ≠ none := by
        intro i hi h_eq_none
        have h_absorb : walkStar (some a) ((shift w ω) a) n = none :=
          FrogModel.walkStar_absorb (some a) ((shift w ω) a) i n h_eq_none (Nat.le_of_lt hi)
        rw [hn] at h_absorb
        simp at h_absorb
      have h_walk_eq : walk (a ++ w) (ω (a ++ w)) n = b ++ w := by
        have htemp := FrogModel.ZeroOne.walk_append_embedAt w hw a (ω (a ++ w)) n h_none_lt
        calc
          walk (a ++ w) (ω (a ++ w)) n = embedAt w (walkStar (some a) (ω (a ++ w)) n) := by
            simpa [shift] using htemp
          _ = embedAt w (some b) := by
            have hn' : walkStar (some a) (ω (a ++ w)) n = some b := by
              simpa [shift] using hn
            rw [hn']
          _ = b ++ w := rfl
      have h_paths_eq : paths ω (a ++ w) n = b ++ w := by
        calc
          paths ω (a ++ w) n = walk (a ++ w) (ω (a ++ w)) n := rfl
          _ = b ++ w := h_walk_eq
      rw [← h_paths_eq]
      exact Reach.path n ih

/-- If `w` is woken and infinitely many frozen frogs of `T*` at `w` run straight up to the root
after their exit, the root is visited infinitely often. -/
theorem FrogModel.ZeroOne.visits_infinite_of_upRun {d : ℕ} (ω : Sample d) (w : Vertex d)
    (hw : w ≠ []) (hR : Reach (paths ω) w)
    (hinf : {v | frozen (shift w ω) v ∧
      upRun (w.length - 1) (shift w ω v) (exitTime v (shift w ω v)).toNat}.Infinite) :
    (visits (paths ω)).Infinite := by
  set S := paths ω
  set L := w.length - 1
  set I := {v | frozen (shift w ω) v ∧
    upRun (w.length - 1) (shift w ω v) (exitTime v (shift w ω v)).toNat}
  have hI : I.Infinite := hinf
  have hV : {p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root}.Infinite := by
    -- Define f : Vertex d → Vertex d × ℕ
    set f : Vertex d → Vertex d × ℕ := fun v => (v ++ w, (exitTime v (ω (v ++ w))).toNat + L)
    have hf_inj : Function.Injective f := by
      intro x y h
      have h_eq : (x ++ w, (exitTime x (ω (x ++ w))).toNat + L) = (y ++ w, (exitTime y (ω (y ++ w))).toNat + L) := h
      have h_append : x ++ w = y ++ w := by
        have := congrArg Prod.fst h_eq
        simpa [f] using this
      exact List.append_left_injective w h_append
    have hf_injOn : Set.InjOn f I :=
      hf_inj.injOn
    have h_image_infinite : (f '' I).Infinite :=
      Set.Infinite.image hf_injOn hI
    have h_subset : f '' I ⊆ {p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root} := by
      intro p hp
      rcases hp with ⟨v, hv, rfl⟩
      have hv_frozen : frozen (shift w ω) v := hv.1
      have hv_upRun : upRun (w.length - 1) (shift w ω v) (exitTime v (shift w ω v)).toNat := hv.2
      -- From frozen: Relation.ReflTransGen (starArc (shift w ω)) [] v
      rcases hv_frozen with ⟨h_refl_trans, h_exit⟩
      -- h_exit : ∃ n, walkStar (some v) ((shift w ω) v) n = none
      rcases h_exit with ⟨n, hn⟩
      -- (shift w ω) v = ω (v ++ w)
      have h_shift : (shift w ω) v = ω (v ++ w) := rfl
      rw [h_shift] at hn
      -- exitTime v (ω (v ++ w)) ≠ ⊤
      have h_exitTime_ne_top : exitTime v (ω (v ++ w)) ≠ ⊤ := by
        rw [FrogModel.ZeroOne.exitTime_ne_top_iff]
        exact ⟨n, hn⟩
      -- So exitTime = (k : ℕ∞) for some k
      rcases (ENat.ne_top_iff_exists.mp h_exitTime_ne_top) with ⟨k, hk⟩
      -- hk : (k : ℕ∞) = exitTime v (ω (v ++ w))
      have hk_symm : exitTime v (ω (v ++ w)) = (k : ℕ∞) := hk.symm
      have hk_toNat : (exitTime v (ω (v ++ w))).toNat = k := by
        rw [hk_symm, ENat.toNat_natCast]
      -- From exitTime_spec
      rcases FrogModel.ZeroOne.exitTime_spec v (ω (v ++ w)) k hk_symm with ⟨h_exit_none, h_exit_before⟩
      -- h_exit_none : walkStar (some v) (ω (v ++ w)) k = none
      -- h_exit_before : ∀ i < k, walkStar (some v) (ω (v ++ w)) i ≠ none
      -- So k ≥ 1 since walkStar (some v) _ 0 = some v ≠ none
      have hk_pos : 1 ≤ k := by
        by_contra! h
        have hk0 : k = 0 := by omega
        subst hk0
        have h0 : walkStar (some v) (ω (v ++ w)) 0 = some v := rfl
        rw [h0] at h_exit_none
        exact Option.some_ne_none v h_exit_none
      -- From walk_append_embedAt
      have h_walk_append : walk (v ++ w) (ω (v ++ w)) k = embedAt w (walkStar (some v) (ω (v ++ w)) k) :=
        FrogModel.ZeroOne.walk_append_embedAt w hw v (ω (v ++ w)) k h_exit_before
      rw [h_exit_none] at h_walk_append
      have h_embed_none : embedAt w none = w.tail := rfl
      rw [h_embed_none] at h_walk_append
      -- Now h_walk_append : walk (v ++ w) (ω (v ++ w)) k = w.tail
      have h_tail_len : (w.tail : Vertex d).length = w.length - 1 := by
        rw [List.length_tail]
      -- From upRun hypothesis
      -- First rewrite shift in hv_upRun
      rw [h_shift] at hv_upRun
      -- hv_upRun : upRun (w.length - 1) (ω (v ++ w)) (exitTime v (ω (v ++ w))).toNat
      rw [hk_toNat] at hv_upRun
      -- hv_upRun : upRun (w.length - 1) (ω (v ++ w)) k
      -- But w.length - 1 = L
      have hv_upRun' : upRun L (ω (v ++ w)) k := by
        simpa [L] using hv_upRun
      -- Now we need upRun (walk (v ++ w) (ω (v ++ w)) k).length (ω (v ++ w)) k for walk_upRun
      -- We know (walk (v ++ w) (ω (v ++ w)) k).length = L
      have h_walk_len : (walk (v ++ w) (ω (v ++ w)) k).length = L := by
        rw [h_walk_append, h_tail_len]
      -- So we can rewrite hv_upRun' to get the needed hypothesis
      have h_upRun_walk : upRun (walk (v ++ w) (ω (v ++ w)) k).length (ω (v ++ w)) k := by
        rw [h_walk_len]
        exact hv_upRun'
      -- Now apply walk_upRun
      have h_walk_upRun : walk (v ++ w) (ω (v ++ w)) (k + (walk (v ++ w) (ω (v ++ w)) k).length) = root :=
        FrogModel.ZeroOne.walk_upRun (v ++ w) (ω (v ++ w)) k h_upRun_walk
      rw [h_walk_len] at h_walk_upRun
      -- h_walk_upRun : walk (v ++ w) (ω (v ++ w)) (k + L) = root
      -- Now we have: f v = (v ++ w, k + L)
      -- Need: Reach S (v ++ w) ∧ 1 ≤ k + L ∧ S (v ++ w) (k + L) = root
      have h_reach : Reach S (v ++ w) :=
        FrogModel.ZeroOne.reach_append ω w hw hR v h_refl_trans
      have h_time : 1 ≤ k + L := by
        omega
      have h_root : S (v ++ w) (k + L) = root := by
        calc
          S (v ++ w) (k + L) = walk (v ++ w) (ω (v ++ w)) (k + L) := rfl
          _ = root := h_walk_upRun
      -- Now we have f v ∈ V
      have h_mem : f v ∈ {p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root} := by
        dsimp [f]
        rw [hk_toNat]
        exact ⟨h_reach, h_time, h_root⟩
      exact h_mem
    -- Now combine
    have hV' : (f '' I).Infinite := h_image_infinite
    have hV_sub : f '' I ⊆ {p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root} := h_subset
    exact Set.Infinite.mono hV_sub hV'
  -- Now use encard_visits to relate visits to V
  have h_encard_eq : (visits S).encard = {p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root}.encard := by
    exact FrogModel.encard_visits S (fun u => paths_zero ω u)
  have h_encard_infinite : (visits S).encard = ⊤ := by
    rw [h_encard_eq, Set.encard_eq_top_iff.mpr hV]
  -- Convert encard = ⊤ to Infinite
  exact Set.encard_eq_top_iff.mp h_encard_infinite
