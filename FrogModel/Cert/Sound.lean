module

public import FrogModel.Cert.Defs

@[expose] public section

/-!
# From the cheap conditions to the hypotheses of Lemma 6.3 and Theorem 6.5 of the paper

For the rational data `D` of a certificate (FrogModel.Cert.Defs): the paths of the table from
`root` carry a probability law (`paths_prob_sum`, `paths_prob_pos`), `r_q(s)` is the mean of
`phi^(B(J) - B(q))` from label `s` of level `q` (`r_eq_paths`), at least `1` (`one_le_r`), and
satisfies the one-step identities of the proof of Lemma 6.3 (`r_step`, `r_two_step`,
`boundary_mean`, `step_factor_le`, `drift_eq_one`, `one_le_weight`). Under (I0), (I1), (I2):
`H* = (1 - eps) P_tab + eps sum_(t > T) (1 - rho) rho^(t - T - 1) delta_(Z_t)` has total mass
`1` and nonnegative atoms (`law_mass_one`, `atom_nonneg`, `tail_mass`), `M = E phi^(B*(J))`
(`M_eq_tsum`, `tail_mgf`) and `c = E B*(1)` (`c_eq_tsum`, `tail_mean`); the tail comparison of
the proof of Theorem 6.5 is `tail_compare` with `inv_theta_pow_le`.
-/

open MeasureTheory
open scoped ENNReal
open FrogModel.Cert

theorem FrogModel.Cert.Data.rLevel_length (D : FrogModel.Cert.Data) (h1 : D.I1) :
    ∀ n ≤ D.J, (D.rLevel n).length = D.nLabels (D.J - n) := by
  intro n hn
  induction' n with k ih
  · rcases h1 with ⟨hlen, h0, hJ, htrans, hsum⟩
    have h0 : D.rLevel 0 = [1] := rfl
    rw [h0]
    simp [hJ]
  · have hsucc : D.rLevel (k + 1) = (List.range (D.nLabels (D.J - (k + 1)))).map
      (fun s => ((D.row (D.J - (k + 1)) s).map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum) := rfl
    rw [hsucc]
    simp

theorem FrogModel.Cert.Data.r_end (D : FrogModel.Cert.Data) : D.r D.J 0 = 1 := by
  unfold FrogModel.Cert.Data.r FrogModel.Cert.Data.rLevel
  simp

theorem FrogModel.Cert.Data.r_step (D : FrogModel.Cert.Data) (h1 : D.I1) :
    ∀ q < D.J, ∀ s < D.nLabels q,
      ((D.row q s).map fun t => t.p * D.phi ^ t.δ * D.r (q + 1) t.s').sum = D.r q s := by
  intro q hq s hs
  have hqle : q + 1 ≤ D.J := Nat.succ_le_of_lt hq
  have hqle_sq : q ≤ q + 1 := Nat.le_succ q
  have hsub : D.J - q = (D.J - (q + 1)) + 1 := by
    rw [← Nat.sub_add_sub_cancel hqle hqle_sq, Nat.add_sub_cancel_left]
  have hsub2 : D.J - ((D.J - (q + 1)) + 1) = q := by
    nth_rw 1 [← Nat.sub_add_cancel hqle]
    rw [Nat.add_sub_add_left, Nat.add_sub_cancel_right]
  simp [r, rLevel, hsub, hsub2, hs]

theorem FrogModel.Cert.Data.paths_prob_sum (D : FrogModel.Cert.Data) (h1 : D.I1) :
    ∀ n q s, q + n = D.J → s < D.nLabels q → ((D.paths n q s).map FrogModel.Cert.pathProb).sum = 1 := by
  -- Helper lemma: sum of flatMap equals sum of mapped sums
  have h_sum_flatMap : ∀ {α : Type} {β : Type} [AddCommMonoid β] (l : List α) (f : α → List β),
      (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
    intro α β _ l f
    induction' l with a l ih
    · rfl
    · simp [List.flatMap, List.map_cons, List.sum_cons]; rfl
  intro n
  induction' n with n ih
  · intro q s hqn hs
    have hqJ : q = D.J := by omega
    subst hqJ
    simp [FrogModel.Cert.Data.paths, FrogModel.Cert.pathProb]
  · intro q s hqn hs
    rcases h1 with ⟨hlen, h0, hJ, hall, hrow⟩
    have hq_lt_J : q < D.J := by omega
    have hq1n : q + 1 + n = D.J := by omega
    simp [FrogModel.Cert.Data.paths]
    -- Goal: (((D.row q s).flatMap fun t => (D.paths n (q + 1) t.s').map (t :: ·)).map
    --   FrogModel.Cert.pathProb).sum = 1
    -- Step 1: (l.flatMap f).map g = l.flatMap (fun a => (f a).map g) by definition
    have h_map_flatMap : ∀ (l : List Tr) (f : Tr → List (List Tr)) (g : List Tr → ℚ),
        ((l.flatMap f).map g).sum = (l.flatMap fun a => (f a).map g).sum := by
      intro l f g
      simp [List.flatMap, List.map_map]; rfl
    rw [h_map_flatMap]
    -- Step 2: Simplify inner map: pathProb (t :: π) = t.p * pathProb π
    have h_inner_map : ∀ (t : Tr),
        ((D.paths n (q + 1) t.s').map (t :: ·)).map FrogModel.Cert.pathProb =
        (D.paths n (q + 1) t.s').map fun π => t.p * FrogModel.Cert.pathProb π := by
      intro t
      simp [FrogModel.Cert.pathProb, List.map_map]
    -- Use List.flatMap_congr to replace the inner function
    have h_flatMap_eq : (D.row q s).flatMap (fun t => ((D.paths n (q + 1) t.s').map (t :: ·)).map
        FrogModel.Cert.pathProb) =
        (D.row q s).flatMap (fun t => (D.paths n (q + 1) t.s').map fun π => t.p * FrogModel.Cert.pathProb π) := by
      refine List.flatMap_congr ?_
      intro t ht
      exact h_inner_map t
    rw [h_flatMap_eq]
    -- Step 3: Push sum inside flatMap
    rw [h_sum_flatMap]
    -- Goal: ((D.row q s).map fun t =>
    --   ((D.paths n (q + 1) t.s').map fun π => t.p * FrogModel.Cert.pathProb π).sum).sum = 1
    -- Step 4: Factor out t.p from each inner sum
    simp_rw [List.sum_map_mul_left]
    -- Goal: ((D.row q s).map fun t => t.p * ((D.paths n (q + 1) t.s').map FrogModel.Cert.pathProb).sum).sum = 1
    -- Step 5: For each t in row q s, the inner sum equals 1 by IH
    have h_inner_sum : ∀ t ∈ D.row q s, ((D.paths n (q + 1) t.s').map FrogModel.Cert.pathProb).sum = 1 := by
      intro t ht
      have ht_mem := List.mem_filter.mp ht
      rcases ht_mem with ⟨ht_table, h⟩
      have h_decide : t.q = q ∧ t.s = s := by
        simpa using h
      have hqt_eq := h_decide.1
      have hallt := hall t ht_table
      have hqt := hallt.1
      have hst := hallt.2.1
      have hst' := hallt.2.2.1
      -- hst' : t.s' < D.nLabels (t.q + 1)
      -- Since t ∈ D.row q s, we have t.q = q
      have hst'_labels : t.s' < D.nLabels (q + 1) := by
        rw [hqt_eq] at hst'
        exact hst'
      exact ih (q + 1) t.s' hq1n hst'_labels
    -- Now we need to use h_inner_sum to simplify the goal
    -- We prove a helper: (l.map f).sum = (l.map g).sum if f and g agree on l
    have h_sum_map_congr : ∀ {α β : Type} [AddCommMonoid β] (l : List α) (f g : α → β),
        (∀ x ∈ l, f x = g x) → (l.map f).sum = (l.map g).sum := by
      intro α β _ l f g h
      induction' l with a l ih
      · rfl
      · simp [List.map_cons, List.sum_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    -- Replace ((D.paths n (q+1) t.s').map pathProb).sum with 1
    have h_sum_eq1 := h_sum_map_congr (D.row q s)
      (fun t => t.p * ((D.paths n (q + 1) t.s').map FrogModel.Cert.pathProb).sum)
      (fun t => t.p * (1 : ℚ))
      (by
        intro t ht
        rw [h_inner_sum t ht])
    rw [h_sum_eq1]
    -- Goal: ((D.row q s).map fun t => t.p * (1 : ℚ)).sum = 1
    simp [mul_one]
    -- Goal: ((D.row q s).map Tr.p).sum = 1
    -- This is exactly hrow q hq_lt_J s hs
    exact hrow q hq_lt_J s hs

theorem FrogModel.Cert.Data.paths_prob_pos (D : FrogModel.Cert.Data) (h1 : D.I1) :
    ∀ n q s, ∀ π ∈ D.paths n q s, 0 < FrogModel.Cert.pathProb π := by
  intro n
  induction' n with n ih
  · intro q s π hπ
    have h_empty : D.paths 0 q s = [[]] := rfl
    rw [h_empty] at hπ
    have hπ_eq : π = [] := by
      simpa using hπ
    rw [hπ_eq]
    simp [FrogModel.Cert.pathProb]
  · intro q s π hπ
    have h_flatmap : D.paths (n + 1) q s =
      (D.row q s).flatMap fun t => (D.paths n (q + 1) t.s').map (t :: ·) := rfl
    rw [h_flatmap] at hπ
    rcases List.mem_flatMap.mp hπ with ⟨t, ht, hπ'⟩
    rcases List.mem_map.mp hπ' with ⟨π', hπ'', rfl⟩
    have hp_pos : 0 < t.p := by
      have h_all : ∀ t ∈ D.table, t.q < D.J ∧ t.s < D.nLabels t.q ∧ t.s' < D.nLabels (t.q + 1) ∧ 0 < t.p :=
        h1.2.2.2.1
      have ht_table : t ∈ D.table := by
        have := (List.mem_filter.mp ht).1
        exact this
      rcases h_all t ht_table with ⟨_, _, _, hp⟩
      exact hp
    have h_ih := ih (q + 1) t.s' π' hπ''
    unfold FrogModel.Cert.pathProb
    simp
    exact mul_pos hp_pos h_ih

theorem FrogModel.Cert.Data.r_eq_paths (D : FrogModel.Cert.Data) (h1 : D.I1) :
    ∀ q ≤ D.J, ∀ s < D.nLabels q,
      D.r q s = ((D.paths (D.J - q) q s).map fun π =>
        FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π).sum := by
  -- First, prove the recurrence for r (r_step)
  have hr_step (q : ℕ) (hq : q < D.J) (s : ℕ) (hs : s < D.nLabels q) :
      D.r q s = ((D.row q s).map fun t => t.p * D.phi ^ t.δ * D.r (q + 1) t.s').sum := by
    dsimp [Data.r]
    have hsub : D.J - q = (D.J - (q + 1)) + 1 := by omega
    rw [hsub]
    have hsub2 : D.J - ((D.J - (q + 1)) + 1) = q := by omega
    simp [Data.rLevel, List.getD, hsub2, hs]
  -- Key identity for path probabilities
  have h_path_prob (t : Tr) (π : List Tr) :
      FrogModel.Cert.pathProb (t :: π) * D.phi ^ FrogModel.Cert.pathInc (t :: π) =
      (t.p * D.phi ^ t.δ) * (FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π) := by
    simp [FrogModel.Cert.pathProb, FrogModel.Cert.pathInc, mul_assoc, mul_comm, mul_left_comm, pow_add]
  -- Lemma: for t ∈ row q s, we have t.s' < D.nLabels (q+1) (from I1)
  have h_row_bound (q s : ℕ) (t : Tr) (ht : t ∈ D.row q s) : t.s' < D.nLabels (q + 1) := by
    rcases h1 with ⟨hlen, hl0, hlJ, htrans, hsum⟩
    have ht_table : t ∈ D.table := by
      unfold Data.row at ht
      simp at ht
      exact ht.1
    have hq_eq : t.q = q := by
      unfold Data.row at ht
      simp at ht
      exact ht.2.1
    rcases htrans t ht_table with ⟨_, _, hs'_bound, _⟩
    rw [hq_eq] at hs'_bound
    exact hs'_bound
  -- Helper: sum of flatMap equals sum of map of sums
  have h_sum_flatMap (l : List Tr) (h : Tr → List ℚ) : (l.flatMap h).sum = (l.map fun a => (h a).sum).sum := by
    induction' l with a l ih
    · rfl
    · simp [List.flatMap, List.sum_append]
      rfl
  -- Helper: map_congr for lists
  have h_map_congr {α : Type} (l : List α) (f g : α → ℚ) (h : ∀ t ∈ l, f t = g t) : l.map f = l.map g := by
    induction' l with t ts ih
    · rfl
    · simp [List.map_cons, h t (by simp), ih (fun x hx => h x (by simp [hx]))]
  -- Main lemma by induction on n = D.J - q
  have h_main : ∀ (n : ℕ) (q s : ℕ), q + n = D.J → s < D.nLabels q →
      D.r q s = ((D.paths n q s).map fun π =>
        FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π).sum := by
    intro n
    induction' n with n ih
    · -- n = 0: q = D.J
      intro q s h_add hs
      have hq_eq : q = D.J := by omega
      subst hq_eq
      have hs0 : s = 0 := by
        have h_labels : D.nLabels D.J = 1 := h1.2.2.1
        omega
      subst hs0
      simp [Data.r, rLevel, FrogModel.Cert.pathProb, FrogModel.Cert.pathInc, FrogModel.Cert.Data.paths]
    · -- n = n'+1: q < D.J
      intro q s h_add hs
      have hq_lt : q < D.J := by omega
      rw [hr_step q hq_lt s hs]
      simp [FrogModel.Cert.Data.paths]
      have h_add_q1 : (q + 1) + n = D.J := by omega
      -- Rewrite D.r (q+1) t.s' using induction hypothesis
      have h_map_eq : (D.row q s).map (fun t => t.p * D.phi ^ t.δ * D.r (q + 1) t.s') =
          (D.row q s).map (fun t => (t.p * D.phi ^ t.δ) *
            ((D.paths n (q+1) t.s').map fun π =>
              FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π).sum) := by
        apply h_map_congr
        intro t ht
        have hts'_bound : t.s' < D.nLabels (q + 1) := h_row_bound q s t ht
        simp [ih (q+1) t.s' h_add_q1 hts'_bound, mul_assoc]
      rw [h_map_eq]
      -- RHS = (List.map (fun π => ...) ((D.row q s).flatMap fun t => (D.paths n (q+1) t.s').map (t :: ·))).sum
      -- Use List.map_flatMap: map g (flatMap f l) = flatMap (fun a => map g (f a)) l
      rw [List.map_flatMap]
      -- RHS = ((D.row q s).flatMap fun t => ((D.paths n (q+1) t.s').map (t :: ·)).map fun π => pathProb π * D.phi ^ pathInc π).sum
      simp [List.map_map]
      -- RHS = ((D.row q s).flatMap fun t => (D.paths n (q+1) t.s').map fun π => pathProb (t :: π) * D.phi ^ pathInc (t :: π)).sum
      -- Use h_sum_flatMap to rewrite flatMap as map
      rw [h_sum_flatMap]
      -- Now RHS = ((D.row q s).map fun t => ((D.paths n (q+1) t.s').map fun π => pathProb (t :: π) * D.phi ^ pathInc (t :: π)).sum).sum
      -- Both sides are (map ... (D.row q s)).sum, need pointwise equality
      have h_map_eq2 : (D.row q s).map (fun t => (t.p * D.phi ^ t.δ) *
          ((D.paths n (q+1) t.s').map fun π =>
            FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π).sum) =
          (D.row q s).map (fun t => ((D.paths n (q+1) t.s').map fun π =>
            FrogModel.Cert.pathProb (t :: π) * D.phi ^ FrogModel.Cert.pathInc (t :: π)).sum) := by
        apply h_map_congr
        intro t ht
        calc
          (t.p * D.phi ^ t.δ) * ((D.paths n (q+1) t.s').map fun π =>
            FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π).sum
              = ((D.paths n (q+1) t.s').map fun π =>
                  (t.p * D.phi ^ t.δ) * (FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π)).sum := by
            rw [List.sum_map_mul_left]
          _ = ((D.paths n (q+1) t.s').map fun π =>
              FrogModel.Cert.pathProb (t :: π) * D.phi ^ FrogModel.Cert.pathInc (t :: π)).sum := by
            simp [h_path_prob]
      rw [h_map_eq2]
      rfl
  -- Apply h_main to the original goal
  intro q hq s hs
  have h_add : q + (D.J - q) = D.J := Nat.add_sub_cancel' hq
  exact h_main (D.J - q) q s h_add hs

theorem FrogModel.Cert.Data.one_le_r (D : FrogModel.Cert.Data) (h1 : D.I1) (hφ : 1 ≤ D.phi) :
    ∀ q ≤ D.J, ∀ s < D.nLabels q, 1 ≤ D.r q s := by
  -- Extract components of I1
  have h_nLabels_J : D.nLabels D.J = 1 := h1.2.2.1
  have h_table : ∀ t ∈ D.table, t.q < D.J ∧ t.s < D.nLabels t.q ∧ t.s' < D.nLabels (t.q + 1) ∧ 0 < t.p := h1.2.2.2.1
  have h_row_sum : ∀ q < D.J, ∀ s < D.nLabels q, ((D.row q s).map Tr.p).sum = 1 := h1.2.2.2.2
  intro q hq s hs
  -- D.r q s = (D.rLevel (D.J - q)).getD s 0
  rw [FrogModel.Cert.Data.r]
  -- Goal: 1 ≤ (D.rLevel (D.J - q)).getD s 0
  set n := D.J - q with hn_def
  have hn : n ≤ D.J := Nat.sub_le _ _
  -- Helper lemma: for all m ≤ D.J, for all s' < D.nLabels (D.J - m), 1 ≤ (rLevel m).getD s' 0
  have h_lemma : ∀ (m : ℕ), m ≤ D.J → ∀ (s' : ℕ), s' < D.nLabels (D.J - m) → 1 ≤ (D.rLevel m).getD s' 0 := by
    intro m hm
    induction' m with k ih
    · -- m = 0
      intro s' hs'
      have h_sub : D.J - 0 = D.J := Nat.sub_zero _
      rw [h_sub] at hs'
      rw [h_nLabels_J] at hs'
      have hs'0 : s' = 0 := by omega
      subst hs'0
      simp [Data.rLevel]
    · -- m = k+1
      have hk_le : k ≤ D.J := by omega
      intro s' hs'
      -- Expand rLevel (k+1)
      have h_rLevel_succ : D.rLevel (k + 1) =
        (List.range (D.nLabels (D.J - (k + 1)))).map fun s =>
          ((D.row (D.J - (k + 1)) s).map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum := rfl
      rw [h_rLevel_succ]
      -- Need to show: (List.map ... (List.range ...)).getD s' 0 ≥ 1
      -- First, note that s' < length of this list
      have h_len : (List.map (fun s => ((D.row (D.J - (k + 1)) s).map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum)
        (List.range (D.nLabels (D.J - (k + 1))))).length = D.nLabels (D.J - (k + 1)) := by
        simp
      have hs'_lt_len : s' < (List.map (fun s => ((D.row (D.J - (k + 1)) s).map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum)
        (List.range (D.nLabels (D.J - (k + 1))))).length := by
        rw [h_len]
        exact hs'
      rw [List.getD_eq_getElem _ _ hs'_lt_len]
      -- Now: (List.map ... (List.range ...))[s']
      -- Using List.getElem_map
      have h_range_len' : s' < (List.map (fun s => ((D.row (D.J - (k + 1)) s).map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum)
        (List.range (D.nLabels (D.J - (k + 1))))).length := hs'_lt_len
      rw [List.getElem_map (f := fun s => ((D.row (D.J - (k + 1)) s).map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum)
        (l := List.range (D.nLabels (D.J - (k + 1)))) (i := s') (h := h_range_len')]
      -- Now: f ((List.range ...)[s']) where f = fun s => ...
      -- (List.range ...)[s'] = s'
      have h_range_get : (List.range (D.nLabels (D.J - (k + 1))))[s']'(by
        simpa [List.length_range] using hs') = s' := by
        simp
      rw [h_range_get]
      -- Now: ((D.row (D.J - (k + 1)) s').map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum
      -- Need to show this sum ≥ 1
      -- From I1, the row sum of p's = 1
      have h_q_lt : D.J - (k + 1) < D.J := by
        omega
      have h_row_sum' : ((D.row (D.J - (k + 1)) s').map Tr.p).sum = 1 :=
        h_row_sum (D.J - (k + 1)) h_q_lt s' hs'
      -- Each term in the sum is ≥ the corresponding t.p
      have h_terms_ge : ∀ t ∈ D.row (D.J - (k + 1)) s',
          t.p ≤ t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0 := by
        intro t ht
        -- Get that t is in the table
        have ht_mem_table : t ∈ D.table := by
          have : D.row (D.J - (k + 1)) s' = D.table.filter fun t => t.q = D.J - (k + 1) ∧ t.s = s' := rfl
          rw [this] at ht
          exact ((List.mem_filter.mp ht).1)
        have ht_q_eq : t.q = D.J - (k + 1) := by
          have : D.row (D.J - (k + 1)) s' = D.table.filter fun t => t.q = D.J - (k + 1) ∧ t.s = s' := rfl
          rw [this] at ht
          have h_filter := (List.mem_filter.mp ht).2
          have h_and : t.q = D.J - (k + 1) ∧ t.s = s' := by
            simpa [decide_eq_true_eq] using h_filter
          exact h_and.1
        have h_table_data := h_table t ht_mem_table
        rcases h_table_data with ⟨ht_q_lt, ht_s, ht_s', ht_p⟩
        have hp_nonneg : 0 ≤ t.p := by linarith
        have h_phi_pow_ge_one : 1 ≤ D.phi ^ t.δ := one_le_pow₀ hφ
        have h_rLevel_ge_one : 1 ≤ (D.rLevel k).getD t.s' 0 := by
          -- Need t.s' < D.nLabels (D.J - k)
          have h_s'_lt : t.s' < D.nLabels (D.J - k) := by
            -- From ht_s' : t.s' < D.nLabels (t.q + 1)
            -- t.q = D.J - (k+1), so t.q + 1 = D.J - k
            rw [ht_q_eq] at ht_s'
            have : (D.J - (k + 1)) + 1 = D.J - k := by omega
            rw [this] at ht_s'
            exact ht_s'
          exact ih hk_le t.s' h_s'_lt
        -- Now: t.p ≤ t.p * phi^δ * rLevel
        have h_nonneg_phi_pow : 0 ≤ D.phi ^ t.δ :=
          pow_nonneg (by linarith) t.δ
        have h_nonneg_mul : 0 ≤ t.p * D.phi ^ t.δ := mul_nonneg hp_nonneg h_nonneg_phi_pow
        calc
          t.p = t.p * 1 * 1 := by ring
          _ ≤ t.p * (D.phi ^ t.δ) * 1 := by
            have h : t.p * 1 ≤ t.p * (D.phi ^ t.δ) :=
              mul_le_mul_of_nonneg_left h_phi_pow_ge_one hp_nonneg
            simpa [mul_assoc] using mul_le_mul_of_nonneg_right h (by norm_num : (0 : ℚ) ≤ 1)
          _ ≤ t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0 := by
            have h : (t.p * D.phi ^ t.δ) * 1 ≤ (t.p * D.phi ^ t.δ) * (D.rLevel k).getD t.s' 0 :=
              mul_le_mul_of_nonneg_left h_rLevel_ge_one h_nonneg_mul
            simpa [mul_assoc] using h
      -- Now use List.sum_le_sum
      have h_sum_ge : ((D.row (D.J - (k + 1)) s').map Tr.p).sum ≤
          ((D.row (D.J - (k + 1)) s').map fun t => t.p * D.phi ^ t.δ * (D.rLevel k).getD t.s' 0).sum := by
        refine List.sum_le_sum ?_
        intro t ht
        simpa using h_terms_ge t ht
      rw [h_row_sum'] at h_sum_ge
      exact h_sum_ge
  have h_sub_eq : D.J - n = q := by
    rw [hn_def]
    omega
  have hs' : s < D.nLabels (D.J - n) := by
    rw [h_sub_eq]
    exact hs
  exact h_lemma n hn s hs'

theorem FrogModel.Cert.Data.EB1_eq_paths (D : FrogModel.Cert.Data) (h1 : D.I1) (hJ : 1 ≤ D.J) :
    D.EB1 = ((D.paths D.J 0 0).map fun π =>
      FrogModel.Cert.pathProb π * (FrogModel.Cert.firstInc π : ℚ)).sum := by
  obtain ⟨n, hn⟩ : ∃ n, D.J = n + 1 := ⟨D.J - 1, by omega⟩
  have hfm : ∀ (l : List FrogModel.Cert.Tr) (f : FrogModel.Cert.Tr → List ℚ),
      (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
    intro l f
    simp [List.flatMap, List.sum_flatten, Function.comp_def]
  rw [hn, FrogModel.Cert.Data.paths, List.map_flatMap, hfm, FrogModel.Cert.Data.EB1]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have hmem := List.mem_filter.mp ht
  have hq : t.q = 0 := by simpa using (of_decide_eq_true hmem.2).1
  have hs' : t.s' < D.nLabels 1 := by
    have := (h1.2.2.2.1 t hmem.1).2.2.1
    rwa [hq] at this
  have hsum := D.paths_prob_sum h1 n 1 t.s' (by omega) hs'
  rw [List.map_map]
  have hf : ∀ π ∈ D.paths n (0 + 1) t.s',
      ((fun π => FrogModel.Cert.pathProb π * (FrogModel.Cert.firstInc π : ℚ)) ∘ (t :: ·)) π =
        t.p * t.δ * FrogModel.Cert.pathProb π := by
    intro π _
    simp only [Function.comp, FrogModel.Cert.pathProb, FrogModel.Cert.firstInc, List.map_cons,
      List.prod_cons, List.head?_cons, Option.map_some, Option.getD_some]
    ring
  rw [List.map_congr_left hf, List.sum_map_mul_left, zero_add, hsum, mul_one]

theorem FrogModel.Cert.Data.r_two_step (D : FrogModel.Cert.Data) (h1 : D.I1) (hJ : 2 ≤ D.J) :
    ((D.row 0 0).map fun t₁ => ((D.row 1 t₁.s').map fun t₂ =>
      t₁.p * t₂.p * D.phi ^ (t₁.δ + t₂.δ) * D.r 2 t₂.s').sum).sum = D.r 0 0 := by
  have hJpos : 0 < D.J := by omega
  have hJpos' : 1 < D.J := by omega
  have hn0 : D.nLabels 0 = 1 := h1.2.1
  have h0_lt_n0 : 0 < D.nLabels 0 := by
    rw [hn0]
    omega
  have hstep0 := FrogModel.Cert.Data.r_step D h1 0 hJpos 0 h0_lt_n0
  -- hstep0: ((D.row 0 0).map fun t => t.p * D.phi ^ t.δ * D.r 1 t.s').sum = D.r 0 0

  have hstep1 : ∀ t₁, t₁ ∈ D.row 0 0 →
    D.r 1 t₁.s' = ((D.row 1 t₁.s').map fun t₂ => t₂.p * D.phi ^ t₂.δ * D.r 2 t₂.s').sum := by
    intro t₁ ht₁
    have ht₁_table : t₁ ∈ D.table := by
      have hfilter : D.row 0 0 = D.table.filter (fun t => t.q = 0 ∧ t.s = 0) := rfl
      rw [hfilter] at ht₁
      exact (List.mem_filter.mp ht₁).1
    have ht₁_prop := h1.2.2.2.1 t₁ ht₁_table
    have ht₁_qs : t₁.q = 0 ∧ t₁.s = 0 := by
      have hfilter : D.row 0 0 = D.table.filter (fun t => t.q = 0 ∧ t.s = 0) := rfl
      rw [hfilter] at ht₁
      simpa using (List.mem_filter.mp ht₁).2
    have h_lt : t₁.s' < D.nLabels 1 := by
      rcases ht₁_prop with ⟨_, _, hlt, _⟩
      rcases ht₁_qs with ⟨hq, _⟩
      rw [hq] at hlt
      exact hlt
    exact (FrogModel.Cert.Data.r_step D h1 1 hJpos' t₁.s' h_lt).symm

  have h_mul_sum : ∀ (a : ℚ) (l : List ℚ), a * l.sum = (l.map fun x => a * x).sum := by
    intro a l
    induction' l with x xs ih
    · simp
    · simp [mul_add, ih]

  have hinner : ∀ t₁, t₁ ∈ D.row 0 0 →
    ((D.row 1 t₁.s').map fun t₂ => t₁.p * t₂.p * D.phi ^ (t₁.δ + t₂.δ) * D.r 2 t₂.s').sum =
    t₁.p * D.phi ^ t₁.δ * D.r 1 t₁.s' := by
    intro t₁ ht₁
    have hstep1_t1 := hstep1 t₁ ht₁
    rw [hstep1_t1]
    have h_eq_map : (D.row 1 t₁.s').map (fun t₂ => t₁.p * t₂.p * D.phi ^ (t₁.δ + t₂.δ) * D.r 2 t₂.s') =
        ((D.row 1 t₁.s').map (fun t₂ => t₂.p * D.phi ^ t₂.δ * D.r 2 t₂.s')).map (fun x => t₁.p * D.phi ^ t₁.δ * x) := by
      simp [List.map_map, mul_assoc, mul_comm, mul_left_comm, pow_add]
    rw [h_eq_map, h_mul_sum]

  have sum_map_congr : ∀ {α β : Type _} [AddCommMonoid β] (l : List α) (f g : α → β),
      (∀ x ∈ l, f x = g x) → (l.map f).sum = (l.map g).sum := by
    intro α β _ l f g h
    induction' l with x xs ih
    · rfl
    · have hx : f x = g x := h x List.mem_cons_self
      have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      simp [List.map_cons, List.sum_cons, hx, ih hxs]

  have hsum : ((D.row 0 0).map fun t₁ => ((D.row 1 t₁.s').map fun t₂ =>
    t₁.p * t₂.p * D.phi ^ (t₁.δ + t₂.δ) * D.r 2 t₂.s').sum).sum =
    ((D.row 0 0).map fun t₁ => t₁.p * D.phi ^ t₁.δ * D.r 1 t₁.s').sum :=
    sum_map_congr (D.row 0 0) _ _ hinner

  rw [hsum, hstep0]

theorem FrogModel.Cert.tail_mass (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (k : ℕ) :
    HasSum (fun n : ℕ => (1 - ρ) * ρ ^ (k + n)) (ρ ^ k) := by
  have hgeom := hasSum_geometric_of_lt_one h0 h1
  have hsum : HasSum (fun n : ℕ => ((1 - ρ) * ρ ^ k) * ρ ^ n) (((1 - ρ) * ρ ^ k) * (1 - ρ)⁻¹) :=
    hgeom.mul_left ((1 - ρ) * ρ ^ k)
  have h_eq : ((1 - ρ) * ρ ^ k) * (1 - ρ)⁻¹ = ρ ^ k := by
    have h_ne : (1 - ρ : ℝ) ≠ 0 := by linarith
    calc
      ((1 - ρ) * ρ ^ k) * (1 - ρ)⁻¹ = ρ ^ k * ((1 - ρ) * (1 - ρ)⁻¹) := by ring
      _ = ρ ^ k * 1 := by field_simp [h_ne]
      _ = ρ ^ k := by ring
  have h_expr : (fun n : ℕ => (1 - ρ) * ρ ^ (k + n)) = (fun n : ℕ => ((1 - ρ) * ρ ^ k) * ρ ^ n) := by
    ext n
    simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
  rw [h_expr]
  simpa [h_eq] using hsum

theorem FrogModel.Cert.tail_mean (ρ : ℝ) (T : ℕ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    HasSum (fun n : ℕ => (1 - ρ) * ρ ^ n * ((T : ℝ) + 1 + n)) ((T : ℝ) + 1 + ρ / (1 - ρ)) := by
  have hρ_ne_one : 1 - ρ ≠ 0 := by linarith
  have h_norm : ‖ρ‖ < 1 := by
    simpa [abs_of_nonneg h0] using h1
  have h_geom := hasSum_geometric_of_lt_one h0 h1
  have h_mul_geom := hasSum_coe_mul_geometric_of_norm_lt_one h_norm
  have hA : HasSum (fun n : ℕ => ((T : ℝ) + 1) * (1 - ρ) * ρ ^ n) (((T : ℝ) + 1) * (1 - ρ) * ((1 - ρ)⁻¹)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (h_geom.mul_left ((T : ℝ) + 1)).mul_left (1 - ρ)
  have hB : HasSum (fun n : ℕ => (1 - ρ) * (n : ℝ) * ρ ^ n) ((1 - ρ) * (ρ / (1 - ρ) ^ 2)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul_geom.mul_left (1 - ρ)
  have hsum := hA.add hB
  have hsum' : HasSum (fun n : ℕ => (1 - ρ) * ρ ^ n * ((T : ℝ) + 1 + (n : ℝ))) ((T : ℝ) + 1 + ρ / (1 - ρ)) := by
    convert hsum using 1
    · ext n
      ring
    · field_simp [hρ_ne_one]
  simpa using hsum'

theorem FrogModel.Cert.tail_mgf (ρ φ : ℝ) (T : ℕ) (h0 : 0 ≤ ρ) (hφ : 0 ≤ φ) (h1 : φ * ρ < 1) :
    HasSum (fun n : ℕ => (1 - ρ) * ρ ^ n * φ ^ (T + 1 + n)) ((1 - ρ) * φ ^ (T + 1) / (1 - φ * ρ)) := by
  have h_mul_nonneg : 0 ≤ φ * ρ := mul_nonneg hφ h0
  have h_mul_lt_one : φ * ρ < 1 := h1
  have h_geom := hasSum_geometric_of_lt_one h_mul_nonneg h_mul_lt_one
  have h_mul := HasSum.mul_left ((1 - ρ) * φ ^ (T + 1)) h_geom
  -- rewrite the summand
  have h_eq : (fun n : ℕ => (1 - ρ) * ρ ^ n * φ ^ (T + 1 + n)) =
      (fun n : ℕ => ((1 - ρ) * φ ^ (T + 1)) * ((φ * ρ) ^ n)) := by
    ext n
    calc
      (1 - ρ) * ρ ^ n * φ ^ (T + 1 + n)
          = (1 - ρ) * ρ ^ n * (φ ^ (T + 1) * φ ^ n) := by rw [pow_add]
      _ = ((1 - ρ) * φ ^ (T + 1)) * (ρ ^ n * φ ^ n) := by ring
      _ = ((1 - ρ) * φ ^ (T + 1)) * ((ρ * φ) ^ n) := by rw [mul_pow]
      _ = ((1 - ρ) * φ ^ (T + 1)) * ((φ * ρ) ^ n) := by rw [mul_comm ρ φ]
  -- rewrite the goal to match h_mul
  rw [h_eq]
  simpa [div_eq_mul_inv] using h_mul

theorem FrogModel.Cert.inv_theta_pow_le (θ ρ : ℝ) (h1 : 1 < θ) (h2 : 1 ≤ θ * ρ) (n : ℕ) :
    θ⁻¹ ^ n ≤ ρ ^ n := by
  have hθpos : 0 < θ := by linarith
  have hθ_nonneg : 0 ≤ θ := by linarith
  have hinv_nonneg : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ_nonneg
  have hinv_le_ρ : θ⁻¹ ≤ ρ := by
    calc
      θ⁻¹ = θ⁻¹ * 1 := by ring
      _ ≤ θ⁻¹ * (θ * ρ) := mul_le_mul_of_nonneg_left h2 hinv_nonneg
      _ = (θ⁻¹ * θ) * ρ := by ring
      _ = 1 * ρ := by
        field_simp [hθpos.ne.symm]
      _ = ρ := by ring
  exact pow_le_pow_left₀ hinv_nonneg hinv_le_ρ n

theorem FrogModel.Cert.Data.drift_eq_one (D : FrogModel.Cert.Data) (h : D.phi ≠ 0) :
    (D.theta / D.phi + 4 * (D.kappa / D.phi)) / 5 = 1 := by
  unfold Data.theta
  field_simp [h]
  ring

theorem FrogModel.Cert.Data.law_mass_one (D : FrogModel.Cert.Data) (h0 : D.I0) (h1 : D.I1) :
    (1 - (D.eps : ℝ)) * ((((D.paths D.J 0 0).map FrogModel.Cert.pathProb).sum : ℚ) : ℝ) +
      (D.eps : ℝ) * ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n = 1 := by
  rcases h0 with ⟨hJ, hT, heps_pos, heps_lt_one, hrho_pos, hrho_lt_one, hphi_gt_one⟩
  have hnLabels0 : D.nLabels 0 = 1 := by
    have := h1
    rcases this with ⟨_, hnl0, _, _, _⟩
    exact hnl0
  have hpaths : ((D.paths D.J 0 0).map FrogModel.Cert.pathProb).sum = (1 : ℚ) := by
    apply FrogModel.Cert.Data.paths_prob_sum D h1 D.J 0 0 ?_ ?_
    · simp
    · rw [hnLabels0]
      exact Nat.one_pos
  have hpaths_real : (↑(((D.paths D.J 0 0).map FrogModel.Cert.pathProb).sum : ℚ) : ℝ) = (1 : ℝ) := by
    exact_mod_cast hpaths
  rw [hpaths_real]
  have hrho_nonneg : 0 ≤ (D.rho : ℝ) := by exact_mod_cast hrho_pos.le
  have hrho_lt_one_real : (D.rho : ℝ) < 1 := by exact_mod_cast hrho_lt_one
  have hgeom : ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n = 1 := by
    calc
      ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n = (1 - (D.rho : ℝ)) * ∑' n : ℕ, (D.rho : ℝ) ^ n := by
        rw [tsum_mul_left]
      _ = (1 - (D.rho : ℝ)) * ((1 - (D.rho : ℝ))⁻¹) := by
        rw [tsum_geometric_of_lt_one hrho_nonneg hrho_lt_one_real]
      _ = 1 := by
        have hne : (1 - (D.rho : ℝ)) ≠ 0 := by linarith
        field_simp [hne]
  rw [hgeom]
  ring

theorem FrogModel.Cert.Data.atom_nonneg (D : FrogModel.Cert.Data) (h0 : D.I0) (h1 : D.I1) :
    ∀ π ∈ D.paths D.J 0 0, 0 ≤ (1 - D.eps) * FrogModel.Cert.pathProb π := by
  intro π hπ
  rcases h0 with ⟨_, _, _, h_eps_lt_one, _, _, _⟩
  have h_eps_nonneg : 0 ≤ 1 - D.eps := by linarith
  have h_pos : ∀ t ∈ D.table, 0 < t.p := by
    rcases h1 with ⟨_, _, _, h_pos_all, _⟩
    intro t ht
    rcases h_pos_all t ht with ⟨_, _, _, hpos⟩
    exact hpos
  have h_paths_nonneg : ∀ n q s, ∀ π ∈ D.paths n q s, 0 ≤ FrogModel.Cert.pathProb π := by
    intro n
    induction' n with n ih
    · intro q s π hπ
      have : D.paths 0 q s = [[]] := rfl
      rw [this] at hπ
      simp at hπ
      subst hπ
      simp [FrogModel.Cert.pathProb]
    · intro q s π hπ
      simp [FrogModel.Cert.Data.paths] at hπ
      rcases hπ with ⟨t, ht, π', hπ', rfl⟩
      have ht_table : t ∈ D.table := (List.mem_filter.mp ht).1
      have ht_pos : 0 < t.p := h_pos t ht_table
      have hπ'_nonneg := ih (q + 1) t.s' π' hπ'
      simp [FrogModel.Cert.pathProb]
      apply mul_nonneg
      · exact le_of_lt ht_pos
      · exact hπ'_nonneg
  have h_prob_nonneg : 0 ≤ FrogModel.Cert.pathProb π := h_paths_nonneg D.J 0 0 π hπ
  nlinarith

theorem FrogModel.Cert.Data.M_eq_tsum (D : FrogModel.Cert.Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2) :
    (D.M : ℝ) = (1 - (D.eps : ℝ)) * ((((D.paths D.J 0 0).map fun π =>
        FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π).sum : ℚ) : ℝ) +
      (D.eps : ℝ) * ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n) := by
  rcases h0 with ⟨hJ, hT, heps_pos, heps_lt1, hrho_pos, hrho_lt1, hphi_gt1⟩
  have h1_saved := h1
  rcases h1 with ⟨hlen, hn0, hnJ, htrans, hsum⟩
  rcases h2 with ⟨hphi_rho_lt1, hkappa_ge1, hM_le_kappa, htheta_gt1, htheta_rho_ge1⟩
  have hnLabels0_pos : 0 < D.nLabels 0 := by
    rw [hn0]
    exact Nat.one_pos
  have hr00_eq : D.r 0 0 = ((D.paths (D.J - 0) 0 0).map fun π =>
        FrogModel.Cert.pathProb π * D.phi ^ FrogModel.Cert.pathInc π).sum :=
    r_eq_paths D h1_saved 0 (Nat.zero_le _) 0 hnLabels0_pos
  have hrho_nonneg : 0 ≤ (D.rho : ℝ) := by exact mod_cast hrho_pos.le
  have hphi_nonneg : 0 ≤ (D.phi : ℝ) := by
    have : 0 ≤ D.phi := by linarith
    exact mod_cast this
  have hphi_rho_lt1' : (D.phi : ℝ) * (D.rho : ℝ) < 1 := by
    exact mod_cast hphi_rho_lt1
  have h_tail_hasSum : HasSum (fun n : ℕ => (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n))
      ((1 - (D.rho : ℝ)) * (D.phi : ℝ) ^ (D.T + 1) / (1 - (D.phi : ℝ) * (D.rho : ℝ))) :=
    tail_mgf (D.rho : ℝ) (D.phi : ℝ) D.T hrho_nonneg hphi_nonneg hphi_rho_lt1'
  have h_tsum_eq : ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n) =
      (1 - (D.rho : ℝ)) * (D.phi : ℝ) ^ (D.T + 1) / (1 - (D.phi : ℝ) * (D.rho : ℝ)) :=
    h_tail_hasSum.tsum_eq
  have hM_unfold : (D.M : ℝ) = (1 - (D.eps : ℝ)) * (D.r 0 0 : ℝ) + (D.eps : ℝ) * (1 - (D.rho : ℝ)) * (D.phi : ℝ) ^ (D.T + 1) / (1 - (D.phi : ℝ) * (D.rho : ℝ)) := by
    simp [FrogModel.Cert.Data.M]
  rw [hM_unfold]
  rw [hr00_eq]
  simp
  rw [h_tsum_eq]
  ring

theorem FrogModel.Cert.Data.c_eq_tsum (D : FrogModel.Cert.Data) (h0 : D.I0) (h1 : D.I1) :
    (D.c : ℝ) = (1 - (D.eps : ℝ)) * ((((D.paths D.J 0 0).map fun π =>
        FrogModel.Cert.pathProb π * (FrogModel.Cert.firstInc π : ℚ)).sum : ℚ) : ℝ) +
      (D.eps : ℝ) * ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * ((D.T : ℝ) + 1 + n) := by
  have hJ : 1 ≤ D.J := Nat.le_trans (by norm_num) h0.1
  have h_rho_nonneg : 0 ≤ (D.rho : ℝ) := by
    have h := h0.2.2.2.2.1
    exact le_of_lt (by exact_mod_cast h)
  have h_rho_lt_one : (D.rho : ℝ) < 1 := by
    have h := h0.2.2.2.2.2.1
    exact_mod_cast h
  dsimp [FrogModel.Cert.Data.c]
  have hEB1 := FrogModel.Cert.Data.EB1_eq_paths D h1 hJ
  have h_tail := FrogModel.Cert.tail_mean (D.rho : ℝ) D.T h_rho_nonneg h_rho_lt_one
  have h_tsum : ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * ((D.T : ℝ) + 1 + n) =
      ((D.T : ℝ) + 1 + (D.rho : ℝ) / (1 - (D.rho : ℝ))) :=
    h_tail.tsum_eq
  push_cast
  have hEB1' : (D.EB1 : ℝ) = ((((D.paths D.J 0 0).map fun π =>
    FrogModel.Cert.pathProb π * (FrogModel.Cert.firstInc π : ℚ)).sum : ℚ) : ℝ) := by
    exact_mod_cast hEB1
  rw [hEB1', h_tsum]
  simp

theorem FrogModel.Cert.Data.boundary_mean (D : FrogModel.Cert.Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2) :
    (1 - (D.eps : ℝ)) * ((((D.row 0 0).map fun t => t.p * D.phi ^ t.δ * D.r 1 t.s').sum : ℚ) : ℝ) +
      (D.eps : ℝ) * ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n) =
      (D.M : ℝ) := by
  rcases h0 with ⟨hJ, hT, heps_pos, heps_lt1, hrho_pos, hrho_lt1, hphi_gt1⟩
  have h1_orig := h1
  rcases h1 with ⟨hlen, hnLabels0, hnLabelsJ, htrans, hrowsum⟩
  have hphi_pos : 0 < D.phi := lt_trans (by norm_num : (0 : ℚ) < 1) hphi_gt1
  have hJpos : 0 < D.J := Nat.lt_of_lt_of_le (by decide : 0 < 2) hJ
  have hnLabels0_pos : 0 < D.nLabels 0 := by
    rw [hnLabels0]
    omega
  have h_rstep := FrogModel.Cert.Data.r_step D h1_orig 0 (by omega) 0 hnLabels0_pos
  have hrho_pos' : 0 ≤ (D.rho : ℝ) := le_of_lt (by exact_mod_cast hrho_pos)
  have hphi_pos' : 0 ≤ (D.phi : ℝ) := le_of_lt (by exact_mod_cast hphi_pos)
  have hphi_rho_lt_one' : (D.phi : ℝ) * (D.rho : ℝ) < 1 := by exact_mod_cast h2.1
  have h_tail := FrogModel.Cert.tail_mgf (D.rho : ℝ) (D.phi : ℝ) D.T hrho_pos' hphi_pos' hphi_rho_lt_one'
  have h_tsum : ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n) = (1 - (D.rho : ℝ)) * (D.phi : ℝ) ^ (D.T + 1) / (1 - (D.phi : ℝ) * (D.rho : ℝ)) :=
    h_tail.tsum_eq
  calc
    (1 - (D.eps : ℝ)) * ((((D.row 0 0).map fun t => t.p * D.phi ^ t.δ * D.r 1 t.s').sum : ℚ) : ℝ) +
      (D.eps : ℝ) * ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n)
    = (1 - (D.eps : ℝ)) * ((D.r 0 0 : ℚ) : ℝ) + (D.eps : ℝ) * ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n) := by
      simp [h_rstep]
    _ = (1 - (D.eps : ℝ)) * (D.r 0 0 : ℝ) + (D.eps : ℝ) * ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * (D.phi : ℝ) ^ (D.T + 1 + n) := by simp
    _ = (1 - (D.eps : ℝ)) * (D.r 0 0 : ℝ) + (D.eps : ℝ) * ((1 - (D.rho : ℝ)) * (D.phi : ℝ) ^ (D.T + 1) / (1 - (D.phi : ℝ) * (D.rho : ℝ))) := by rw [h_tsum]
    _ = (D.M : ℝ) := by
      unfold FrogModel.Cert.Data.M
      push_cast
      ring

theorem FrogModel.Cert.step_factor_le (θ φ κ : ℝ) (a : Fin 4 → ℝ) (hφ : 0 < φ)
    (hθ : θ = 5 * φ - 4 * κ) (ha : ∀ c, a c ≤ κ) : (θ / φ + ∑ c, a c / φ) / 5 ≤ 1 := by
  have hφ' : φ ≠ 0 := by linarith
  have hθ_div : θ / φ = 5 - 4 * (κ / φ) := by
    rw [hθ]
    field_simp [hφ']
  have hsum : ∑ c : Fin 4, a c / φ ≤ 4 * (κ / φ) := by
    calc
      ∑ c : Fin 4, a c / φ ≤ ∑ c : Fin 4, κ / φ := by
        refine Finset.sum_le_sum ?_
        intro c _
        gcongr
        exact ha c
      _ = (Finset.card (Finset.univ : Finset (Fin 4))) • (κ / φ) := by simp [Finset.sum_const]
      _ = 4 * (κ / φ) := by norm_num
  calc
    (θ / φ + ∑ c : Fin 4, a c / φ) / 5 ≤ (θ / φ + 4 * (κ / φ)) / 5 := by
      gcongr
    _ = ((5 - 4 * (κ / φ)) + 4 * (κ / φ)) / 5 := by rw [hθ_div]
    _ = 5 / 5 := by ring
    _ = 1 := by norm_num

theorem FrogModel.Cert.tail_compare (θ ρ ε S : ℝ) (T t : ℕ) (hθ : 1 < θ) (hθρ : 1 ≤ θ * ρ)
    (hε : 0 ≤ ε) (hS : S ≤ ε * θ ^ (T + 1)) (ht : T + 1 ≤ t) :
    θ⁻¹ ^ t * S ≤ ε * ρ ^ (t - (T + 1)) := by
  have hθpos : 0 < θ := by linarith
  have h_inv_nonneg : 0 ≤ θ⁻¹ := inv_nonneg.mpr (by linarith)
  have h_inv_le : θ⁻¹ ≤ ρ := by
    calc
      θ⁻¹ = θ⁻¹ * 1 := by ring
      _ ≤ θ⁻¹ * (θ * ρ) := mul_le_mul_of_nonneg_left hθρ h_inv_nonneg
      _ = (θ⁻¹ * θ) * ρ := by ring
      _ = 1 * ρ := by field_simp [hθpos.ne.symm]
      _ = ρ := by ring
  have h_pow_eq : θ⁻¹ ^ t * θ ^ (T + 1) = θ⁻¹ ^ (t - (T + 1)) := by
    calc
      θ⁻¹ ^ t * θ ^ (T + 1) = (θ ^ t)⁻¹ * θ ^ (T + 1) := by simp [inv_pow]
      _ = θ ^ (T + 1) * (θ ^ t)⁻¹ := mul_comm _ _
      _ = (θ ^ t * (θ ^ (T + 1))⁻¹)⁻¹ := by simp [mul_inv_rev]
      _ = (θ ^ (t - (T + 1)))⁻¹ := by rw [pow_sub₀ θ hθpos.ne.symm ht]
      _ = θ⁻¹ ^ (t - (T + 1)) := by simp [inv_pow]
  calc
    θ⁻¹ ^ t * S ≤ θ⁻¹ ^ t * (ε * θ ^ (T + 1)) :=
      mul_le_mul_of_nonneg_left hS (pow_nonneg h_inv_nonneg t)
    _ = ε * (θ⁻¹ ^ t * θ ^ (T + 1)) := by ring
    _ = ε * θ⁻¹ ^ (t - (T + 1)) := by rw [h_pow_eq]
    _ ≤ ε * ρ ^ (t - (T + 1)) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h_inv_nonneg h_inv_le (t - (T + 1))) hε

theorem FrogModel.Cert.Data.one_le_weight (D : FrogModel.Cert.Data) (h0 : D.I0) (h1 : D.I1)
    (h2 : D.I2) : ∀ q, 1 ≤ q → q ≤ D.J → ∀ s < D.nLabels q, 1 ≤ D.kappa ^ (q - 1) * D.r q s := by
  intro q _ hq s hs
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h2.2.1)
    (D.one_le_r h1 h0.2.2.2.2.2.2.le q hq s hs)
