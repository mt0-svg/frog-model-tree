module

public import FrogModel.LemmaX.ChildDefs
public import FrogModel.Cert.Sound

@[expose] public section

/-!
# The child chain: the rows and the law of one move (Lemma 6.1 of the paper)

Section 6.2 of the paper. For a well-formed state of a table satisfying (I0) and (I1), the row
sequence has nonnegative weights summing to `1` (`rowSeq_nonneg`, `rowSeq_hasSum`), so the
inverse distribution function (`lintegral_quantile`) gives the law of one move:
`∫ g (childStep s u) dλ = ∑ p_n g(δ_n, next_n)` (`lintegral_childStep`), and the row law of
`ChildDefs` (`rowLaw_holds`). Every move keeps the states well formed (`childWF_step`), and the
moves are measurable (`measurableSet_childStep_eq`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaX FrogModel.Cert

/-- The uniforms giving one move of the child chain form a measurable set. -/
theorem FrogModel.Cert.Data.measurableSet_childStep_eq (D : Data) (s : CState) (r : ℕ × CState) :
    MeasurableSet {u : ℝ | D.childStep s u = r} := by
  set v : ℝ → ℝ := fun u => if 0 ≤ u ∧ u < 1 then u else 0 with hv_def
  have hv_meas : Measurable v := by
    have h_cond : MeasurableSet {u : ℝ | 0 ≤ u ∧ u < 1} := by
      have : {u : ℝ | 0 ≤ u ∧ u < 1} = Set.Ico (0 : ℝ) 1 := by
        ext u; simp [Set.mem_Ico]
      rw [this]
      exact measurableSet_Ico
    refine Measurable.ite h_cond measurable_id measurable_const
  have h_meas_lt (a : ℝ) : MeasurableSet {u : ℝ | v u < a} := by
    have : {u : ℝ | v u < a} = v ⁻¹' {x | x < a} := by rfl
    rw [this]
    exact hv_meas (measurableSet_lt measurable_id measurable_const)
  set c : ℕ → ℝ := fun n => (D.rowCum s (n + 1) : ℝ) with hc_def
  have hA (n : ℕ) : MeasurableSet {u : ℝ | v u < c n} := h_meas_lt (c n)
  set p : ℕ → ℝ → Prop := fun n u => v u < c n with hp_def
  -- S_n = {u | p n u ∧ ∀ m < n, ¬ p m u}
  have h_Sn (n : ℕ) : MeasurableSet {u : ℝ | p n u ∧ ∀ m < n, ¬ p m u} := by
    have h1 : MeasurableSet {u : ℝ | p n u} := hA n
    have h2 : MeasurableSet {u : ℝ | ∀ m < n, ¬ p m u} := by
      have : {u : ℝ | ∀ m < n, ¬ p m u} = ⋂ m ∈ Finset.range n, {u : ℝ | ¬ p m u} := by
        ext u; simp [Finset.mem_range]
      rw [this]
      refine MeasurableSet.biInter (Finset.countable_toSet _) fun m hm => ?_
      have : {u : ℝ | ¬ p m u} = {u : ℝ | v u < c m}ᶜ := by
        ext u; simp [p, not_lt]
      rw [this]
      exact (hA m).compl
    exact h1.inter h2
  -- Characterize childStep s u = r
  have h_char : ∀ u, D.childStep s u = r ↔
      ((¬ ∃ n, p n u) ∧ r = (0, s)) ∨ (∃ n, p n u ∧ (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2 ∧ ∀ m < n, ¬ p m u) := by
    intro u
    dsimp [childStep, p, v, c]
    constructor
    · intro h
      by_cases h_ex : ∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum s (n + 1) : ℝ)
      · simp [h_ex] at h
        set n := Nat.find h_ex with hn_def
        have h_spec := Nat.find_spec h_ex
        have h_min : ∀ m < n, ¬ p m u := fun m hm =>
          Nat.find_min h_ex (by simpa [hn_def] using hm)
        have h_pair : (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2 := by
          have h' := h
          simpa [hn_def] using (Prod.mk.inj h')
        right
        exact ⟨n, h_spec, h_pair.1, h_pair.2, h_min⟩
      · simp [h_ex] at h
        left
        exact ⟨h_ex, h.symm⟩
    · intro h
      rcases h with (⟨h_ex, hr_eq⟩ | ⟨n, hp_n, hδ, hnext, h_all_m⟩)
      · simp [h_ex, hr_eq]
      · have h_ex : ∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum s (n + 1) : ℝ) := ⟨n, hp_n⟩
        have h_find : Nat.find h_ex = n := by
          apply (Nat.find_eq_iff h_ex).mpr
          exact ⟨hp_n, h_all_m⟩
        simp [h_ex, h_find, hδ, hnext]
  -- Rewrite the goal using h_char
  have h_set_eq : {u : ℝ | D.childStep s u = r} =
      {u | ((¬ ∃ n, p n u) ∧ r = (0, s))} ∪ ⋃ n, {u | p n u ∧ (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2 ∧ ∀ m < n, ¬ p m u} := by
    ext u; simp [h_char u]
  rw [h_set_eq]
  by_cases hr : r = (0, s)
  · -- r = (0, s): the first set simplifies to {u | ¬ ∃ n, p n u}
    have h_first : {u : ℝ | ((¬ ∃ n, p n u) ∧ r = (0, s))} = {u : ℝ | ¬ ∃ n, p n u} := by
      ext u; simp [hr]
    rw [h_first]
    -- The second set: intersect each S_n with the constant condition
    have h_union_eq : ⋃ n, {u | p n u ∧ (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2 ∧ ∀ m < n, ¬ p m u} =
        ⋃ n, ({u | p n u ∧ ∀ m < n, ¬ p m u} ∩ {u | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2}) := by
      ext u; simp; tauto
    rw [h_union_eq]
    apply MeasurableSet.union
    · -- {u | ¬ ∃ n, p n u} = ⋂ n, {u | ¬ p n u}
      have : {u : ℝ | ¬ ∃ n, p n u} = ⋂ n, {u : ℝ | ¬ p n u} := by
        ext u; simp
      rw [this]
      refine MeasurableSet.iInter fun n => ?_
      have : {u : ℝ | ¬ p n u} = {u : ℝ | v u < c n}ᶜ := by
        ext u; simp [p]
      rw [this]
      exact (hA n).compl
    · refine MeasurableSet.iUnion fun n => ?_
      have h_fixed : MeasurableSet {u : ℝ | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2} := by
        by_cases h_match : (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2
        · have : {u : ℝ | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2} = Set.univ := by
            ext u; simp [h_match]
          rw [this]; exact MeasurableSet.univ
        · have : {u : ℝ | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2} = ∅ := by
            ext u; simp [h_match]
          rw [this]; exact MeasurableSet.empty
      exact (h_Sn n).inter h_fixed
  · -- r ≠ (0, s): the first set is empty
    have h_first_empty : {u : ℝ | ((¬ ∃ n, p n u) ∧ r = (0, s))} = ∅ := by
      ext u; simp [hr]
    rw [h_first_empty, Set.empty_union]
    -- The second set: same as above but without the r = (0,s) condition
    have h_union_eq : ⋃ n, {u | p n u ∧ (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2 ∧ ∀ m < n, ¬ p m u} =
        ⋃ n, ({u | p n u ∧ ∀ m < n, ¬ p m u} ∩ {u | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2}) := by
      ext u; simp; tauto
    rw [h_union_eq]
    refine MeasurableSet.iUnion fun n => ?_
    have h_fixed : MeasurableSet {u : ℝ | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2} := by
      by_cases h_match : (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2
      · have : {u : ℝ | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2} = Set.univ := by
          ext u; simp [h_match]
        rw [this]; exact MeasurableSet.univ
      · have : {u : ℝ | (D.rowSeq s n).δ = r.1 ∧ (D.rowSeq s n).next = r.2} = ∅ := by
          ext u; simp [h_match]
        rw [this]; exact MeasurableSet.empty
    exact (h_Sn n).inter h_fixed

/-- Every entry of the row of a well-formed state moves to a well-formed state. -/
theorem FrogModel.Cert.Data.rowSeq_next_wf (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState)
    (hs : D.ChildWF s) (n : ℕ) : D.ChildWF (D.rowSeq s n).next := by
  rcases h0 with ⟨hJ2, hT1, heps_pos, heps_lt1, hrho_pos, hrho_lt1, hphi_gt1⟩
  rcases h1 with ⟨hlen, hnLabels0, hnLabelsJ, htable, hsum⟩
  unfold rowSeq
  by_cases hlen' : n < (D.finRow s).length
  · simp [hlen']
    set e := (D.finRow s).get ⟨n, hlen'⟩ with he_def
    have he_mem : e ∈ D.finRow s := by
      rw [he_def]
      exact List.get_mem _ _
    cases s with
    | fresh =>
      have h_finRow_eq : D.finRow .fresh = D.freshRow := rfl
      rw [h_finRow_eq] at he_mem
      dsimp [Data.freshRow] at he_mem
      rcases List.mem_flatMap.mp he_mem with ⟨t₁, ht₁, he_mem'⟩
      rcases List.mem_map.mp he_mem' with ⟨t₂, ht₂, he_eq'⟩
      have he_next : e.next = D.nxt 2 t₂.s' := by
        have := congrArg Entry.next he_eq'.symm
        simpa using this
      dsimp [e] at he_next ⊢
      rw [he_next]
      have ht₂_mem : t₂ ∈ D.table := by
        have hmem := (List.mem_filter.mp ht₂).1
        simpa [Data.row] using hmem
      have ht₂_q : t₂.q = 1 := by
        have hmem := (List.mem_filter.mp ht₂).2
        have h := by simpa using hmem
        rcases h with ⟨hq, _⟩
        exact hq
      have ht₂_s'_lt : t₂.s' < D.nLabels 2 := by
        have := htable t₂ ht₂_mem
        rcases this with ⟨_, _, hlt, _⟩
        rw [ht₂_q] at hlt
        exact hlt
      by_cases h_eq : 2 = D.J
      · have h_nxt : D.nxt 2 t₂.s' = .bdry := by
          simp [nxt, h_eq]
        rw [h_nxt]
        unfold ChildWF; simp
      · have h_lt : 2 < D.J := by omega
        have h_nxt : D.nxt 2 t₂.s' = .lab 2 t₂.s' := by
          simp [nxt, h_eq]
        rw [h_nxt]
        unfold ChildWF; simp [h_lt, ht₂_s'_lt]
    | bdry =>
      have h_finRow_eq : D.finRow .bdry = D.bdryRow := rfl
      rw [h_finRow_eq] at he_mem
      dsimp [Data.bdryRow] at he_mem
      rcases List.mem_map.mp he_mem with ⟨t₁, ht₁, he_eq'⟩
      have ht₁_mem : t₁ ∈ D.table := by
        simpa [Data.row] using (List.mem_filter.mp ht₁).1
      have ht₁_q : t₁.q = 0 := by
        have hmem := (List.mem_filter.mp ht₁).2
        have h := by simpa using hmem
        rcases h with ⟨hq, _⟩
        exact hq
      have ht₁_s'_lt : t₁.s' < D.nLabels 1 := by
        have := htable t₁ ht₁_mem
        rcases this with ⟨_, _, hlt, _⟩
        rw [ht₁_q] at hlt
        exact hlt
      have h_ne : 1 ≠ D.J := by omega
      -- Need to extract he_next first
      have he_next : e.next = D.nxt 1 t₁.s' := by
        have := congrArg Entry.next he_eq'.symm
        simpa using this
      dsimp [e] at he_next ⊢
      rw [he_next]
      have h_nxt : D.nxt 1 t₁.s' = .lab 1 t₁.s' := by
        simp [nxt, h_ne]
      rw [h_nxt]
      have h_lt : 1 < D.J := by omega
      unfold ChildWF; simp [h_lt, ht₁_s'_lt]
    | lab q s =>
      have h_finRow_eq : D.finRow (.lab q s) = D.labRow q s := rfl
      rw [h_finRow_eq] at he_mem
      dsimp [Data.labRow] at he_mem
      rw [List.mem_mergeSort] at he_mem
      rcases List.mem_map.mp he_mem with ⟨t, ht, he_eq'⟩
      have ht_mem : t ∈ D.table := by
        simpa [Data.row] using (List.mem_filter.mp ht).1
      have ht_q : t.q = q := by
        have hmem := (List.mem_filter.mp ht).2
        have h := by simpa using hmem
        rcases h with ⟨hq, _⟩
        exact hq
      have ht_s'_lt : t.s' < D.nLabels (q + 1) := by
        have := htable t ht_mem
        rcases this with ⟨_, _, hlt, _⟩
        rw [ht_q] at hlt
        exact hlt
      have he_next : e.next = D.nxt (q + 1) t.s' := by
        have := congrArg Entry.next he_eq'.symm
        simpa using this
      dsimp [e] at he_next ⊢
      rw [he_next]
      by_cases h_eq : q + 1 = D.J
      · have h_nxt : D.nxt (q + 1) t.s' = .bdry := by
          simp [nxt, h_eq]
        rw [h_nxt]
        unfold ChildWF; simp
      · have h_lt : q + 1 < D.J := by
          unfold ChildWF at hs; rcases hs with ⟨_, hq2, _⟩; omega
        have h_nxt : D.nxt (q + 1) t.s' = .lab (q + 1) t.s' := by
          simp [nxt, h_eq]
        rw [h_nxt]
        unfold ChildWF; simp [h_lt, ht_s'_lt]
    | tail q =>
      have h_finRow_eq : D.finRow (.tail q) = D.tailRow q := rfl
      rw [h_finRow_eq] at he_mem
      dsimp [Data.tailRow] at he_mem
      simp at he_mem
      have he_next : e.next = D.nxtTail (q + 1) := by
        have := congrArg Entry.next he_mem
        simpa using this
      dsimp [e] at he_next ⊢
      rw [he_next]
      by_cases h_eq : q + 1 = D.J
      · have h_nxt : D.nxtTail (q + 1) = .bdry := by
          simp [nxtTail, h_eq]
        rw [h_nxt]
        unfold ChildWF; simp
      · have h_lt : q + 1 < D.J := by
          unfold ChildWF at hs; rcases hs with ⟨_, hq2⟩; omega
        have h_nxt : D.nxtTail (q + 1) = .tail (q + 1) := by
          simp [nxtTail, h_eq]
        rw [h_nxt]
        unfold ChildWF
        have hq1 : 1 ≤ q := by
          unfold ChildWF at hs; rcases hs with ⟨hq1, _⟩; exact hq1
        simp [h_lt]
    | maxLab q =>
      have h_finRow_eq : D.finRow (.maxLab q) = D.maxRow q := rfl
      rw [h_finRow_eq] at he_mem
      dsimp [Data.maxRow] at he_mem
      rcases List.mem_map.mp he_mem with ⟨k, hk, he_eq'⟩
      have he_next : e.next = D.nxtMax (q + 1) := by
        have := congrArg Entry.next he_eq'.symm
        simpa using this
      dsimp [e] at he_next ⊢
      rw [he_next]
      by_cases h_eq : q + 1 = D.J
      · have h_nxt : D.nxtMax (q + 1) = .bdry := by
          simp [nxtMax, h_eq]
        rw [h_nxt]
        unfold ChildWF; simp
      · have h_lt : q + 1 < D.J := by
          unfold ChildWF at hs; rcases hs with ⟨_, hq2⟩; omega
        have h_nxt : D.nxtMax (q + 1) = .maxLab (q + 1) := by
          simp [nxtMax, h_eq]
        rw [h_nxt]
        unfold ChildWF
        have hq1 : 1 ≤ q := by
          unfold ChildWF at hs; rcases hs with ⟨hq1, _⟩; exact hq1
        simp [h_lt]
  · simp [hlen']
    cases h_tn : D.tailNext s with
    | some ns =>
      cases s with
      | fresh =>
        have h_ns : ns = D.nxtTail 2 := by
          simp [tailNext] at h_tn
          -- h_tn : D.nxtTail 2 = ns
          exact h_tn.symm
        rw [h_ns]
        by_cases h_eq : 2 = D.J
        · have h_nxt : D.nxtTail 2 = .bdry := by
            simp [nxtTail, h_eq]
          rw [h_nxt]
          unfold ChildWF; simp
        · have h_lt : 2 < D.J := by omega
          have h_nxt : D.nxtTail 2 = .tail 2 := by
            simp [nxtTail, h_eq]
          rw [h_nxt]
          unfold ChildWF; simp [h_lt]
      | bdry =>
        have h_ns : ns = D.nxtTail 1 := by
          simp [tailNext] at h_tn
          exact h_tn.symm
        rw [h_ns]
        by_cases h_eq : 1 = D.J
        · have h_nxt : D.nxtTail 1 = .bdry := by
            simp [nxtTail, h_eq]
          rw [h_nxt]
          unfold ChildWF; simp
        · have h_lt : 1 < D.J := by omega
          have h_nxt : D.nxtTail 1 = .tail 1 := by
            simp [nxtTail, h_eq]
          rw [h_nxt]
          unfold ChildWF; simp [h_lt]
      | lab q s =>
        simp [tailNext] at h_tn
      | tail q =>
        simp [tailNext] at h_tn
      | maxLab q =>
        simp [tailNext] at h_tn
    | none =>
      exact hs

/-- The row of a label sums to `1`. -/
theorem FrogModel.Cert.Data.labRow_sum (D : Data) (h1 : D.I1) (q s : ℕ) (hq : q < D.J)
    (hs : s < D.nLabels q) : ((D.labRow q s).map Entry.p).sum = 1 := by
  rcases h1 with ⟨hlabels, h0, hJ, htrans, hsum⟩
  have hrow_sum := hsum q hq s hs
  unfold labRow
  have h_perm : (((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).mergeSort
    (fun a b => decide (a.δ ≤ b.δ))).Perm
    ((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)) :=
    List.mergeSort_perm _ _
  have h_map_perm : ((((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).mergeSort
    (fun a b => decide (a.δ ≤ b.δ))).map Entry.p).Perm
    (((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).map Entry.p) :=
    h_perm.map _
  have h_sum_eq : ((((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).mergeSort
    (fun a b => decide (a.δ ≤ b.δ))).map Entry.p).sum =
    (((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).map Entry.p).sum :=
    h_map_perm.sum_eq
  have h_map_eq : ((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).map Entry.p =
    (D.row q s).map Tr.p := by
    simp
  rw [h_sum_eq, h_map_eq, hrow_sum]

/-- The finite part of the row of `fresh` sums to `1 - eps`. -/
theorem FrogModel.Cert.Data.freshRow_sum (D : Data) (h1 : D.I1) (hJ : 2 ≤ D.J) :
    (D.freshRow.map Entry.p).sum = 1 - D.eps := by
  rcases h1 with ⟨hlen, hn0, hnJ, htrans, hsum⟩
  have hJ0 : 0 < D.J := by omega
  have hJ1 : 1 < D.J := by omega
  have hsum0 : ((D.row 0 0).map Tr.p).sum = 1 := by
    apply hsum 0 hJ0 0
    rw [hn0]
    exact Nat.one_pos
  have hsum1 (t₁ : Tr) (ht₁ : t₁ ∈ D.row 0 0) : ((D.row 1 t₁.s').map Tr.p).sum = 1 := by
    have ht_mem : t₁ ∈ D.table := List.mem_of_mem_filter ht₁
    have ht := htrans t₁ ht_mem
    rcases ht with ⟨hq, hs, hs', hp⟩
    rcases List.mem_filter.mp ht₁ with ⟨ht_mem', hcond⟩
    have hq0 : t₁.q = 0 := (of_decide_eq_true hcond).1
    have hs'_1 : t₁.s' < D.nLabels 1 := by
      rw [hq0] at hs'
      exact hs'
    apply hsum 1 hJ1 t₁.s' hs'_1
  unfold freshRow
  rw [List.map_flatMap]
  -- Goal: (flatMap (fun a => map Entry.p (map (fun t₂ => ...) (D.row 1 a.s'))) (D.row 0 0)).sum = ...
  -- Use List.flatMap_congr to replace the inner map
  -- Entry.p { p := x, ... } = x definitionally
  have h_inner_simp (a : Tr) : List.map Entry.p (List.map (fun t₂ => { p := (1 - D.eps) * a.p * t₂.p, δ := a.δ + t₂.δ, next := D.nxt 2 t₂.s' }) (D.row 1 a.s')) =
      List.map (fun t₂ => (1 - D.eps) * a.p * t₂.p) (D.row 1 a.s') := by
    rw [List.map_map]
    rfl
  -- Now use List.flatMap_congr
  have h_flatMap_eq : (List.flatMap
      (fun a => List.map Entry.p (List.map (fun t₂ => { p := (1 - D.eps) * a.p * t₂.p, δ := a.δ + t₂.δ, next := D.nxt 2 t₂.s' }) (D.row 1 a.s')))
      (D.row 0 0)) =
      (List.flatMap
      (fun a => List.map (fun t₂ => (1 - D.eps) * a.p * t₂.p) (D.row 1 a.s'))
      (D.row 0 0)) := by
    apply List.flatMap_congr
    intro a ha
    rw [h_inner_simp a]
  rw [h_flatMap_eq]
  -- Goal: (List.flatMap (fun a => List.map (fun t₂ => (1 - D.eps) * a.p * t₂.p) (D.row 1 a.s')) (D.row 0 0)).sum = 1 - D.eps
  -- Lemma: sum of flatMap = sum over elements of sum of each
  have h_sum_flatMap (l : List Tr) (f : Tr → List ℚ) : (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
    induction' l with x l ih
    · simp
    · simp [List.flatMap, List.sum_cons, List.map_cons]
      -- Goal: (map (List.sum ∘ f) l).sum = (map (fun x => (f x).sum) l).sum
      -- These are definitionally equal
      rfl
  -- Lemma: double sum identity
  have h_double_sum (l : List Tr) (r : ℚ) (hsum_l1 : ∀ t₁ ∈ l, ((D.row 1 t₁.s').map Tr.p).sum = 1) :
      (l.flatMap fun t₁ => (D.row 1 t₁.s').map fun t₂ => r * Tr.p t₁ * Tr.p t₂).sum = r * (l.map Tr.p).sum := by
    induction' l with t₁ l ih
    · simp
    · have hsum_t₁ : ((D.row 1 t₁.s').map Tr.p).sum = 1 := hsum_l1 t₁ (by simp)
      have hsum_l1' : ∀ t ∈ l, ((D.row 1 t.s').map Tr.p).sum = 1 := by
        intro t ht; apply hsum_l1 t; simp [ht]
      -- Use h_sum_flatMap to avoid expanding flatMap
      rw [h_sum_flatMap (t₁ :: l) _, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      -- Goal: ((D.row 1 t₁.s').map fun t₂ => r * Tr.p t₁ * Tr.p t₂).sum +
      --   (map (fun t₁' => ((D.row 1 t₁'.s').map fun t₂ => r * Tr.p t₁' * Tr.p t₂).sum) l).sum =
      --   r * (Tr.p t₁ + (map Tr.p l).sum)
      have h_inner_sum : ((D.row 1 t₁.s').map fun t₂ => r * Tr.p t₁ * Tr.p t₂).sum = r * Tr.p t₁ := by
        calc
          ((D.row 1 t₁.s').map fun t₂ => r * Tr.p t₁ * Tr.p t₂).sum
              = (r * Tr.p t₁) * ((D.row 1 t₁.s').map Tr.p).sum := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using List.sum_map_mul_left (D.row 1 t₁.s') Tr.p (r * Tr.p t₁)
          _ = (r * Tr.p t₁) * 1 := by rw [hsum_t₁]
          _ = r * Tr.p t₁ := by ring
      rw [h_inner_sum]
      -- Now goal: r * Tr.p t₁ + (map (fun t₁' => ((D.row 1 t₁'.s').map fun t₂ => r * Tr.p t₁' * Tr.p t₂).sum) l).sum = r * (Tr.p t₁ + (map Tr.p l).sum)
      -- Use h_sum_flatMap to relate the map to flatMap, then use ih
      rw [← h_sum_flatMap l (fun t₁' => (D.row 1 t₁'.s').map fun t₂ => r * Tr.p t₁' * Tr.p t₂)]
      rw [ih hsum_l1']
      ring
  -- Apply the lemma
  rw [h_double_sum (D.row 0 0) (1 - D.eps) hsum1]
  rw [hsum0]
  ring

/-- The finite part of the row of `bdry` sums to `1 - eps`. -/
theorem FrogModel.Cert.Data.bdryRow_sum (D : Data) (h1 : D.I1) (hJ : 1 ≤ D.J) :
    (D.bdryRow.map Entry.p).sum = 1 - D.eps := by
  rcases h1 with ⟨hlen, h0, hJ', htrans, hsum⟩
  have hJpos : 0 < D.J := by omega
  have hsum0 := hsum 0 hJpos 0 (by rw [h0]; exact Nat.one_pos)
  have h_bdry_eq : D.bdryRow.map Entry.p = (D.row 0 0).map fun t₁ => (1 - D.eps) * t₁.p := by
    simp [Data.bdryRow]
  calc
    (D.bdryRow.map Entry.p).sum
        = ((D.row 0 0).map fun t₁ => (1 - D.eps) * t₁.p).sum := by rw [h_bdry_eq]
    _ = (1 - D.eps) * ((D.row 0 0).map Tr.p).sum := by
      rw [List.sum_map_mul_left]
    _ = (1 - D.eps) * 1 := by rw [hsum0]
    _ = 1 - D.eps := by ring

/-- Every level up to `J` has a label. -/
theorem FrogModel.Cert.Data.nLabels_pos (D : Data) (h1 : D.I1) (q : ℕ) (hq : q ≤ D.J) :
    0 < D.nLabels q := by
  rcases h1 with ⟨hlen, h0, hJ, htrans, hsum⟩
  induction' q with k ih
  · -- q = 0
    rw [h0]
    exact Nat.one_pos
  · -- q = k+1
    have hk : k ≤ D.J := by omega
    have hpos := ih hk
    have hrow := hsum k (by omega) 0 hpos
    have hne : D.row k 0 ≠ [] := by
      intro hempty
      rw [hempty] at hrow
      simp at hrow
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
    have ht_filter : t ∈ D.table.filter (fun t' => t'.q = k ∧ t'.s = 0) := ht
    rw [List.mem_filter] at ht_filter
    obtain ⟨ht_table, ht_qs⟩ := ht_filter
    -- ht_qs : decide (t.q = k ∧ t.s = 0) = true
    have ht_qs' : t.q = k ∧ t.s = 0 := by
      simpa using ht_qs
    rcases ht_qs' with ⟨ht_q, ht_s⟩
    have ht_trans := htrans t ht_table
    rcases ht_trans with ⟨_, _, hlt, _⟩
    rw [ht_q] at hlt
    omega

/-- `max_s P_s(δ ≥ 0) = 1` at a level below `J`. -/
theorem FrogModel.Cert.Data.tailMax_zero (D : Data) (h1 : D.I1) (q : ℕ) (hq : q < D.J) :
    D.tailMax q 0 = 1 := by
  have hnpos : 0 < D.nLabels q := D.nLabels_pos h1 q (Nat.le_of_lt hq)
  unfold tailMax
  have h_tailMass : ∀ s, s < D.nLabels q → D.tailMass q s 0 = 1 := by
    intro s hs
    unfold tailMass
    rcases h1 with ⟨hlen, h0, hJ, htrans, hsum⟩
    simp [hsum q hq s hs]
  have h_map_eq : (List.range (D.nLabels q)).map (fun s => D.tailMass q s 0) =
      List.replicate (D.nLabels q) 1 := by
    apply List.ext_get
    · simp
    · intro i h₁ h₂
      have hi : i < D.nLabels q := by simpa using h₁
      simp [h_tailMass i hi]
  have h_foldr_replicate : ∀ (n : ℕ), 0 < n → ((List.replicate n (1 : ℚ)).foldr max (0 : ℚ)) = (1 : ℚ) := by
    intro n hn
    induction' n with m ih
    · exact (Nat.lt_irrefl 0 hn).elim
    · rw [List.replicate_succ, List.foldr_cons]
      by_cases hmz : m = 0
      · rw [hmz]; simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hmz
        rw [ih hmpos]
        simp
  rw [h_map_eq]
  exact h_foldr_replicate (D.nLabels q) hnpos

/-- No increment exceeds `maxDelta`. -/
theorem FrogModel.Cert.Data.tailMax_big (D : Data) (q : ℕ) : D.tailMax q (D.maxDelta + 1) = 0 := by
  have hmax : ∀ t ∈ D.table, t.δ ≤ D.maxDelta := by
    intro t ht
    unfold maxDelta
    have hmem : t.δ ∈ D.table.map Tr.δ :=
      List.mem_map_of_mem ht
    simpa using List.le_max_of_le hmem (le_refl _)
  have htailMass : ∀ s, D.tailMass q s (D.maxDelta + 1) = 0 := by
    intro s
    unfold tailMass
    have hfilter : ((D.row q s).filter fun t => D.maxDelta + 1 ≤ t.δ) = [] := by
      rw [List.filter_eq_nil_iff]
      intro t ht
      have ht_table : t ∈ D.table := by
        unfold Data.row at ht
        exact (List.mem_filter.mp ht).1
      have hle := hmax t ht_table
      have hnotle : ¬ (D.maxDelta + 1 ≤ t.δ) := by omega
      simp [hnotle]
    rw [hfilter]
    simp
  unfold tailMax
  have hfold : ∀ n : ℕ, List.foldr max (0 : ℚ) (List.replicate n (0 : ℚ)) = (0 : ℚ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ, ih]
  simp [htailMass]
  apply hfold

/-- `max_s P_s(δ ≥ k)` is non-increasing in `k`. -/
theorem FrogModel.Cert.Data.tailMax_antitone (D : Data) (h1 : D.I1) (q : ℕ) :
    Antitone (D.tailMax q) := by
  intro k₁ k₂ hk
  have key : ∀ l : List Tr, (∀ t ∈ l, 0 ≤ t.p) →
      ((l.filter fun t => k₂ ≤ t.δ).map Tr.p).sum ≤ ((l.filter fun t => k₁ ≤ t.δ).map Tr.p).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons t l ih =>
      have ih' := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
      have ht := hl t (List.mem_cons_self ..)
      by_cases h2 : k₂ ≤ t.δ
      · have h1' : k₁ ≤ t.δ := le_trans hk h2
        simp only [List.filter_cons, h2, h1', decide_true, ite_true, List.map_cons, List.sum_cons]
        linarith
      · by_cases h1' : k₁ ≤ t.δ
        · simp only [List.filter_cons, h2, h1', decide_true, decide_false, ite_true,
            List.map_cons, List.sum_cons, Bool.false_eq_true, ite_false]
          linarith
        · simp only [List.filter_cons, h2, h1', decide_false, Bool.false_eq_true, ite_false]
          exact ih'
  have hmass : ∀ s, D.tailMass q s k₂ ≤ D.tailMass q s k₁ := fun s =>
    key _ fun t ht => (h1.2.2.2.1 t (List.mem_filter.1 ht).1).2.2.2.le
  unfold Data.tailMax
  generalize List.range (D.nLabels q) = L
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (hmass s) ih

/-- The max row sums to `1` (it telescopes). -/
theorem FrogModel.Cert.Data.maxRow_sum (D : Data) (h1 : D.I1) (q : ℕ) (hq : q < D.J) :
    ((D.maxRow q).map Entry.p).sum = 1 := by
  unfold Data.maxRow
  rw [List.map_map]
  have htel : ∀ n, ((List.range n).map (Entry.p ∘ fun k =>
      (⟨D.tailMax q k - D.tailMax q (k + 1), k, D.nxtMax (q + 1)⟩ : Entry))).sum =
      D.tailMax q 0 - D.tailMax q n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply]
      ring
  rw [htel, D.tailMax_zero h1 q hq, D.tailMax_big]
  norm_num

/-- The weights of the row of a well-formed state are nonnegative. -/
theorem FrogModel.Cert.Data.rowSeq_nonneg (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState)
    (hs : D.ChildWF s) (n : ℕ) : 0 ≤ (D.rowSeq s n).p := by
  rcases h0 with ⟨_, _, he0, he1, hr0, hr1, _⟩
  have hrow : ∀ q s, ∀ t ∈ D.row q s, 0 ≤ t.p := fun q s t ht =>
    (h1.2.2.2.1 t (List.mem_filter.1 ht).1).2.2.2.le
  have heps : (0 : ℚ) ≤ 1 - D.eps := by linarith
  have hfin : ∀ e ∈ D.finRow s, 0 ≤ e.p := by
    intro e he
    cases s with
    | fresh =>
      simp only [Data.finRow, Data.freshRow, List.mem_flatMap, List.mem_map] at he
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := he
      exact mul_nonneg (mul_nonneg heps (hrow _ _ _ ht₁)) (hrow _ _ _ ht₂)
    | bdry =>
      simp only [Data.finRow, Data.bdryRow, List.mem_map] at he
      obtain ⟨t₁, ht₁, rfl⟩ := he
      exact mul_nonneg heps (hrow _ _ _ ht₁)
    | lab q t =>
      simp only [Data.finRow, Data.labRow, List.mem_mergeSort, List.mem_map] at he
      obtain ⟨t₁, ht₁, rfl⟩ := he
      exact hrow _ _ _ ht₁
    | tail q =>
      simp only [Data.finRow, Data.tailRow, List.mem_singleton] at he
      subst he
      norm_num
    | maxLab q =>
      simp only [Data.finRow, Data.maxRow, List.mem_map] at he
      obtain ⟨k, _, rfl⟩ := he
      exact sub_nonneg.2 (D.tailMax_antitone h1 q (Nat.le_succ k))
  unfold Data.rowSeq
  split_ifs with h
  · exact hfin _ (List.getElem_mem h)
  · split
    · exact mul_nonneg (mul_nonneg he0.le (by linarith)) (pow_nonneg hr0.le _)
    · exact le_rfl

/-- The weights of the row of a well-formed state sum to `1`. -/
theorem FrogModel.Cert.Data.rowSeq_hasSum (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState)
    (hs : D.ChildWF s) : HasSum (fun n => ((D.rowSeq s n).p : ℝ)) 1 := by
  have hfin : ∀ s : CState, ∑ i ∈ Finset.range (D.finRow s).length, ((D.rowSeq s i).p : ℝ) =
      (((D.finRow s).map Entry.p).sum : ℝ) := by
    intro s
    rw [Finset.sum_range]
    have h : ∀ i : Fin (D.finRow s).length, ((D.rowSeq s i).p : ℝ) = ((D.finRow s)[(i : ℕ)].p : ℝ) := by
      intro i
      rw [Data.rowSeq, dite_eq_left i.2]
    simp only [h]
    rw [Fin.sum_univ_fun_getElem (D.finRow s) (fun e : Entry => (e.p : ℝ)), Rat.cast_list_sum,
      List.map_map]
    rfl
  have hsplit : ∀ (s : CState) (a : ℝ), (((D.finRow s).map Entry.p).sum : ℝ) = 1 - a →
      HasSum (fun n => ((D.rowSeq s (n + (D.finRow s).length)).p : ℝ)) a →
      HasSum (fun n => ((D.rowSeq s n).p : ℝ)) 1 := by
    intro s a hsum htail
    refine (hasSum_nat_add_iff' (D.finRow s).length).mp ?_
    rw [hfin, hsum, sub_sub_cancel]
    exact htail
  have hidxS : ∀ (s s' : CState) (n : ℕ), D.tailNext s = some s' →
      D.rowSeq s (n + (D.finRow s).length) = ⟨D.tailW n, D.T + 1 + n, s'⟩ := by
    intro s s' n hn
    rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, hn]
  have hidxN : ∀ (s : CState) (n : ℕ), D.tailNext s = none →
      D.rowSeq s (n + (D.finRow s).length) = ⟨0, 0, s⟩ := by
    intro s n hn
    rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, hn]
  have hzero : ∀ s : CState, D.tailNext s = none →
      HasSum (fun n => ((D.rowSeq s (n + (D.finRow s).length)).p : ℝ)) 0 := by
    intro s hn
    simp only [hidxN _ _ hn, Rat.cast_zero]
    exact hasSum_zero
  rcases h0 with ⟨hJ2, _, he0, he1, hr0, hr1, _⟩
  have hgeom : ∀ s s' : CState, D.tailNext s = some s' →
      HasSum (fun n => ((D.rowSeq s (n + (D.finRow s).length)).p : ℝ)) (D.eps : ℝ) := by
    intro s s' hn
    simp only [hidxS _ _ _ hn, Data.tailW]
    push_cast
    have hr : (0 : ℝ) ≤ D.rho := by exact_mod_cast hr0.le
    have hr' : (D.rho : ℝ) < 1 := by exact_mod_cast hr1
    have h := (hasSum_geometric_of_lt_one hr hr').mul_left ((D.eps : ℝ) * (1 - D.rho))
    have hne : (1 : ℝ) - D.rho ≠ 0 := by linarith
    rwa [mul_assoc, mul_inv_cancel₀ hne, mul_one] at h
  cases s with
  | fresh =>
    refine hsplit _ D.eps ?_ (hgeom _ _ rfl)
    rw [show D.finRow .fresh = D.freshRow from rfl, D.freshRow_sum h1 hJ2]
    push_cast; ring
  | bdry =>
    refine hsplit _ D.eps ?_ (hgeom _ _ rfl)
    rw [show D.finRow .bdry = D.bdryRow from rfl, D.bdryRow_sum h1 (by omega)]
    push_cast; ring
  | lab q t =>
    refine hsplit _ 0 ?_ (hzero _ rfl)
    rw [show D.finRow (.lab q t) = D.labRow q t from rfl, D.labRow_sum h1 q t hs.2.1 hs.2.2]
    norm_num
  | tail q =>
    refine hsplit _ 0 ?_ (hzero _ rfl)
    simp [Data.finRow, Data.tailRow]
  | maxLab q =>
    refine hsplit _ 0 ?_ (hzero _ rfl)
    rw [show D.finRow (.maxLab q) = D.maxRow q from rfl, D.maxRow_sum h1 q hs.2]
    norm_num

open Classical in
/-- **The inverse distribution function.** Under Lebesgue measure on `[0, 1]`, the first index
`n` whose cumulative weight `c (n + 1)` exceeds the uniform (moved to `0` off `[0, 1)`) has law
`p`. -/
theorem FrogModel.LemmaX.lintegral_quantile {α : Type*} (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hsum : HasSum p 1) (c : ℕ → ℝ) (hc : ∀ n, c n = ∑ k ∈ Finset.range n, p k) (f : ℕ → α)
    (a₀ : α) (g : α → ℝ≥0∞) :
    ∫⁻ u, g (if h : ∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < c (n + 1) then f (Nat.find h)
        else a₀) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ∑' n, ENNReal.ofReal (p n) * g (f n) := by
  let v : ℝ → ℝ := fun u => if 0 ≤ u ∧ u < 1 then u else 0
  have hv_nonneg : ∀ u, 0 ≤ v u := by
    intro u; dsimp [v]; split
    · exact And.left ‹_›
    · exact le_refl 0
  have hv_lt_one : ∀ u, v u < 1 := by
    intro u; dsimp [v]; split
    · exact And.right ‹_›
    · norm_num
  have hc0 : c 0 = 0 := by
    rw [hc 0, Finset.sum_range_zero]
  have hc_mono : Monotone c := by
    intro a b h
    rw [hc a, hc b]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    intro i _ _
    exact hp i
  have hc_nonneg : ∀ n, 0 ≤ c n := by
    intro n; rw [hc n]
    apply Finset.sum_nonneg; intro i _; exact hp i
  have hsum' : Summable p := hsum.summable
  have htsum : ∑' n, p n = 1 := hsum.tsum_eq
  have hc_le_one : ∀ n, c n ≤ 1 := by
    intro n
    rw [hc n]
    have hle := hsum'.sum_le_tsum (Finset.range n) (fun i hi => hp i)
    rwa [htsum] at hle
  have hc_tendsto : Tendsto c atTop (nhds 1) := by
    have h := hsum.tendsto_sum_nat
    have hc_eq : c = fun n => ∑ k ∈ Finset.range n, p k := by
      ext n; exact hc n
    simpa [hc_eq] using h
  have h_exists : ∀ u, ∃ n, v u < c (n + 1) := by
    intro u
    have h_eventually : ∀ᶠ n in atTop, v u < c n :=
      hc_tendsto.eventually (eventually_gt_nhds (hv_lt_one u))
    rcases Filter.eventually_atTop.mp h_eventually with ⟨N, hN⟩
    have hN' : v u < c N := hN N (le_refl N)
    have hle : c N ≤ c (N + 1) := hc_mono (by omega)
    exact ⟨N, lt_of_lt_of_le hN' hle⟩
  let N : ℝ → ℕ := fun u => Nat.find (h_exists u)
  have hN_spec : ∀ u n, N u = n ↔ v u < c (n + 1) ∧ ∀ m < n, ¬ (v u < c (m + 1)) := by
    intro u n
    dsimp [N]
    rw [Nat.find_eq_iff (h_exists u)]
  have hN_Ico : ∀ u, u ∈ Set.Ico (0 : ℝ) 1 → ∀ n, N u = n ↔ c n ≤ u ∧ u < c (n + 1) := by
    intro u hu n
    rcases hu with ⟨hu0, hu1⟩
    have hv_eq : v u = u := by simp [v, hu0, hu1]
    rw [hN_spec u n, hv_eq]
    constructor
    · rintro ⟨hlt, h⟩
      have hle : c n ≤ u := by
        by_cases hn : n = 0
        · subst hn; rw [hc0]; exact hu0
        · have hm : n - 1 < n := by omega
          have h' := h (n - 1) hm
          have : (n - 1) + 1 = n := by omega
          rw [this] at h'
          linarith
      exact ⟨hle, hlt⟩
    · rintro ⟨hle, hlt⟩
      refine ⟨hlt, ?_⟩
      intro m hm
      have hm' : m + 1 ≤ n := by omega
      have hmono : c (m + 1) ≤ c n := hc_mono hm'
      linarith
  have h_vol_eq_restrict : volume.restrict (Set.Icc (0 : ℝ) 1) = volume.restrict (Set.Ico (0 : ℝ) 1) := by
    refine Measure.restrict_congr_set ?_
    have hvol_singleton : volume ({1} : Set ℝ) = 0 := by simp
    exact (MeasureTheory.Ico_ae_eq_Icc' hvol_singleton).symm
  rw [h_vol_eq_restrict]
  -- Now we work on Ico 0 1; rewrite integrand
  have h_meas_Ico : MeasurableSet (Set.Ico (0 : ℝ) 1) := measurableSet_Ico
  have h_integrand_eq : Set.EqOn (fun u => g (if h : ∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < c (n + 1) then f (Nat.find h) else a₀))
      (fun u => g (f (N u))) (Set.Ico (0 : ℝ) 1) := by
    intro u hu
    rcases hu with ⟨hu0, hu1⟩
    have hv_eq : v u = u := by simp [v, hu0, hu1]
    have h_exists' : ∃ n, u < c (n + 1) := by
      simpa [hv_eq] using h_exists u
    have h_pred_eq : ∀ n, (v u < c (n + 1)) ↔ (u < c (n + 1)) := by
      intro n; rw [hv_eq]
    have hN_eq : N u = Nat.find h_exists' := by
      dsimp [N]
      apply Nat.find_congr'
      intro n
      exact h_pred_eq n
    have h_cond_true : (∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < c (n + 1)) := by
      simpa [v, hv_eq] using h_exists'
    have h_find_eq : N u = Nat.find h_exists' := hN_eq
    dsimp [N] at h_find_eq
    -- h_find_eq : Nat.find (h_exists u) = Nat.find h_exists'
    -- But the goal uses Nat.find with the original h_exists u
    -- Since Nat.find is proof-irrelevant, we can just use hN_eq directly
    simp [h_cond_true, hN_eq, N]
  rw [setLIntegral_congr_fun h_meas_Ico h_integrand_eq]
  -- Now goal: ∫⁻ u in Ico 0 1, g (f (N u)) = ∑' n, ENNReal.ofReal (p n) * g (f n)
  -- Define A_n = Ico (c n) (c (n+1))
  let A : ℕ → Set ℝ := fun n => Set.Ico (c n) (c (n + 1))
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n => measurableSet_Ico
  have hA_disjoint : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    have h_disjoint : Disjoint (Set.Ico (c i) (c (i + 1))) (Set.Ico (c j) (c (j + 1))) := by
      rw [Set.Ico_disjoint_Ico]
      by_cases h : i ≤ j
      · have hci : c i ≤ c j := hc_mono h
        have hci1 : c (i + 1) ≤ c (j + 1) := hc_mono (by omega)
        have hmin : min (c (i + 1)) (c (j + 1)) = c (i + 1) := min_eq_left hci1
        have hmax : max (c i) (c j) = c j := max_eq_right hci
        rw [hmin, hmax]
        exact hc_mono (by omega)
      · have h' : j ≤ i := by omega
        have hcj : c j ≤ c i := hc_mono h'
        have hcj1 : c (j + 1) ≤ c (i + 1) := hc_mono (by omega)
        rw [min_eq_right hcj1, max_eq_left hcj]
        exact hc_mono (by omega)
    dsimp [A]
    exact h_disjoint
  have h_cover : Set.Ico (0 : ℝ) 1 = Set.iUnion A := by
    ext u; constructor
    · intro hu
      rcases hu with ⟨hu0, hu1⟩
      apply Set.mem_iUnion.mpr
      refine ⟨N u, ?_⟩
      show u ∈ Set.Ico (c (N u)) (c (N u + 1))
      exact ((hN_Ico u ⟨hu0, hu1⟩ (N u)).mp rfl)
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
      rcases hn with ⟨hcn, hcn1⟩
      exact ⟨by linarith [hc_nonneg n, hcn], by linarith [hc_le_one (n + 1), hcn1]⟩
  -- Use lintegral_tsum approach: write g(f(N u)) as sum of indicators
  have h_indicator : ∀ u, u ∈ Set.Ico (0 : ℝ) 1 → g (f (N u)) = ∑' n, (A n).indicator (fun _ => g (f n)) u := by
    intro u hu
    have h_mem : ∀ n, u ∈ A n ↔ N u = n := by
      intro n; dsimp [A]; exact ((hN_Ico u hu n).symm)
    calc
      g (f (N u)) = ∑' n, (if n = N u then g (f n) else 0) := by
        rw [tsum_ite_eq (N u) (fun n => g (f n))]
      _ = ∑' n, (if N u = n then g (f n) else 0) := by
        refine tsum_congr (fun n => ?_); simp [eq_comm]
      _ = ∑' n, (A n).indicator (fun _ => g (f n)) u := by
        refine tsum_congr (fun n => ?_)
        simp [Set.indicator, h_mem n]
  -- Now compute the integral
  calc
    ∫⁻ u in Set.Ico (0 : ℝ) 1, g (f (N u))
        = ∫⁻ u in Set.Ico (0 : ℝ) 1, (∑' n, (A n).indicator (fun _ => g (f n)) u) := by
      refine setLIntegral_congr_fun h_meas_Ico (fun u hu => ?_)
      rw [h_indicator u hu]
    _ = ∑' n, ∫⁻ u in Set.Ico (0 : ℝ) 1, (A n).indicator (fun _ => g (f n)) u := by
      rw [MeasureTheory.lintegral_tsum]
      intro n
      apply (Measurable.indicator ?_ (hA_meas n)).aemeasurable.restrict
      exact measurable_const
    _ = ∑' n, ∫⁻ u in A n ∩ Set.Ico (0 : ℝ) 1, g (f n) := by
      refine tsum_congr (fun n => ?_)
      rw [MeasureTheory.setLIntegral_indicator (hA_meas n)]
    _ = ∑' n, ∫⁻ u in A n, g (f n) := by
      refine tsum_congr (fun n => ?_)
      have h_sub : A n ⊆ Set.Ico (0 : ℝ) 1 := by
        dsimp [A]
        intro x hx; rcases hx with ⟨hx1, hx2⟩
        have hx1' : 0 ≤ x := by linarith [hc_nonneg n, hx1]
        have hx2' : x < 1 := by linarith [hc_le_one (n + 1), hx2]
        exact ⟨hx1', hx2'⟩
      rw [Set.inter_eq_left.mpr h_sub]
    _ = ∑' n, g (f n) * volume (A n) := by
      refine tsum_congr (fun n => ?_)
      rw [← MeasureTheory.lintegral_indicator (hA_meas n) (fun _ => g (f n))]
      rw [MeasureTheory.lintegral_indicator_const (hA_meas n) (g (f n))]
    _ = ∑' n, g (f n) * ENNReal.ofReal (c (n + 1) - c n) := by
      refine tsum_congr (fun n => ?_)
      dsimp [A]
      rw [Real.volume_Ico]
    _ = ∑' n, ENNReal.ofReal (p n) * g (f n) := by
      refine tsum_congr (fun n => ?_)
      have hp_eq : p n = c (n + 1) - c n := by
        rw [hc (n + 1), hc n, Finset.sum_range_succ]
        ring
      rw [hp_eq, mul_comm]

/-- **The law of one move**: the uniform selects entry `n` of the row with probability its
weight. -/
theorem FrogModel.Cert.Data.lintegral_childStep (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState)
    (hs : D.ChildWF s) (g : ℕ × CState → ℝ≥0∞) :
    ∫⁻ u, g (D.childStep s u) ∂lam =
      ∑' n, ENNReal.ofReal ((D.rowSeq s n).p : ℝ) * g ((D.rowSeq s n).δ, (D.rowSeq s n).next) := by
  unfold lam childStep
  refine FrogModel.LemmaX.lintegral_quantile
    (p := fun n => (D.rowSeq s n).p)
    (hp := fun n => by exact mod_cast D.rowSeq_nonneg h0 h1 s hs n)
    (hsum := D.rowSeq_hasSum h0 h1 s hs)
    (c := fun n => (D.rowCum s n : ℝ))
    (hc := ?_)
    (f := fun n => ((D.rowSeq s n).δ, (D.rowSeq s n).next))
    (a₀ := (0, s))
    (g := g)
  intro n
  simp [Data.rowCum, Rat.cast_sum]

/-- The weight of the row on a move `r` is `rowLawQ`. -/
theorem FrogModel.Cert.Data.tsum_rowSeq_eq (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState)
    (hs : D.ChildWF s) (r : ℕ × CState) :
    ∑' n, ENNReal.ofReal ((D.rowSeq s n).p : ℝ) *
        (if ((D.rowSeq s n).δ, (D.rowSeq s n).next) = r then 1 else 0) =
      ENNReal.ofReal (D.rowLawQ s r : ℝ) := by
  have hnn : ∀ e ∈ D.finRow s, 0 ≤ e.p := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have := D.rowSeq_nonneg h0 h1 s hs i
    rwa [Data.rowSeq, dite_eq_left hi] at this
  have hlist : ∀ l : List Entry, (∀ e ∈ l, 0 ≤ e.p) →
      (l.map fun e => ENNReal.ofReal (e.p : ℝ) * (if (e.δ, e.next) = r then 1 else 0)).sum =
        ENNReal.ofReal ((((l.filter fun e => e.δ = r.1 ∧ e.next = r.2).map Entry.p).sum : ℚ) : ℝ) := by
    intro l hl
    induction l with
    | nil => simp
    | cons e l ih =>
      have he : (0 : ℝ) ≤ (e.p : ℝ) := by exact_mod_cast hl e (by simp)
      have hl' : ∀ e ∈ l, 0 ≤ e.p := fun e' h => hl e' (by simp [h])
      have hsum : (0 : ℝ) ≤ ((((l.filter fun e => e.δ = r.1 ∧ e.next = r.2).map Entry.p).sum : ℚ) : ℝ) := by
        exact_mod_cast List.sum_nonneg fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact hl' y (List.mem_filter.1 hy).1
      rw [List.map_cons, List.sum_cons, ih hl']
      by_cases hc : e.δ = r.1 ∧ e.next = r.2
      · have hc' : (e.δ, e.next) = r := Prod.ext hc.1 hc.2
        rw [List.filter_cons_of_pos (by simpa using hc), List.map_cons, List.sum_cons, ite_eq_left hc',
          mul_one, Rat.cast_add, ENNReal.ofReal_add he hsum]
      · have hc' : (e.δ, e.next) ≠ r := fun h => hc ⟨by rw [← h], by rw [← h]⟩
        rw [List.filter_cons_of_neg (by simpa using hc), ite_eq_right hc', mul_zero, zero_add]
  have hfinite : ∑ i ∈ Finset.range (D.finRow s).length,
      ENNReal.ofReal ((D.rowSeq s i).p : ℝ) *
        (if ((D.rowSeq s i).δ, (D.rowSeq s i).next) = r then 1 else 0) =
      ENNReal.ofReal (((((D.finRow s).filter fun e => e.δ = r.1 ∧ e.next = r.2).map
        Entry.p).sum : ℚ) : ℝ) := by
    rw [Finset.sum_range]
    have h : ∀ i : Fin (D.finRow s).length, D.rowSeq s i = (D.finRow s)[(i : ℕ)] := by
      intro i
      rw [Data.rowSeq, dite_eq_left i.2]
    simp only [h]
    rw [Fin.sum_univ_fun_getElem (D.finRow s)
      (fun e => ENNReal.ofReal (e.p : ℝ) * (if (e.δ, e.next) = r then 1 else 0))]
    exact hlist _ hnn
  have hidxS : ∀ (s' : CState) (n : ℕ), D.tailNext s = some s' →
      D.rowSeq s (n + (D.finRow s).length) = ⟨D.tailW n, D.T + 1 + n, s'⟩ := by
    intro s' n hn
    rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, hn]
  have hidxN : ∀ n : ℕ, D.tailNext s = none →
      D.rowSeq s (n + (D.finRow s).length) = ⟨0, 0, s⟩ := by
    intro n hn
    rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, hn]
  rcases h0 with ⟨_, _, he0, he1, hr0, hr1, _⟩
  have htw : ∀ n, 0 ≤ D.tailW n := fun n =>
    mul_nonneg (mul_nonneg he0.le (by linarith)) (pow_nonneg hr0.le _)
  have htail : ∑' i, ENNReal.ofReal ((D.rowSeq s (i + (D.finRow s).length)).p : ℝ) *
        (if ((D.rowSeq s (i + (D.finRow s).length)).δ,
          (D.rowSeq s (i + (D.finRow s).length)).next) = r then 1 else 0) =
      ENNReal.ofReal (((if D.tailNext s = some r.2 ∧ D.T + 1 ≤ r.1 then
        D.tailW (r.1 - (D.T + 1)) else 0 : ℚ)) : ℝ) := by
    cases htn : D.tailNext s with
    | none =>
      simp only [hidxN _ htn, Rat.cast_zero, ENNReal.ofReal_zero, zero_mul, tsum_zero]
      simp
    | some s' =>
      simp only [hidxS _ _ htn]
      by_cases hc : s' = r.2 ∧ D.T + 1 ≤ r.1
      · rw [ite_eq_left (by simpa using hc)]
        rw [tsum_eq_single (r.1 - (D.T + 1))]
        · have hr : (D.T + 1 + (r.1 - (D.T + 1)), s') = r := Prod.ext (by simp; omega) hc.1
          rw [ite_eq_left hr, mul_one]
        · intro i hi
          have hr : (D.T + 1 + i, s') ≠ r := fun h => hi (by rw [← h]; simp)
          rw [ite_eq_right hr, mul_zero]
      · rw [ite_eq_right (by simpa using hc)]
        rw [Rat.cast_zero, ENNReal.ofReal_zero]
        refine ENNReal.tsum_eq_zero.2 fun i => ?_
        have hr : (D.T + 1 + i, s') ≠ r := fun h => hc ⟨by rw [← h], by rw [← h]; simp⟩
        rw [ite_eq_right hr, mul_zero]
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := (D.finRow s).length), hfinite, htail,
    Data.rowLawQ, Rat.cast_add, ENNReal.ofReal_add]
  · exact_mod_cast List.sum_nonneg fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hnn y (List.mem_filter.1 hy).1
  · split_ifs
    · exact_mod_cast htw _
    · simp

namespace FrogModel.Cert.Data

open FrogModel.LemmaX

/-- **Every move keeps the states well formed.** -/
theorem childWF_step (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState) (hs : D.ChildWF s)
    (u : ℝ) : D.ChildWF (D.childStep s u).2 := by
  unfold childStep
  by_cases h : ∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum s (n + 1) : ℝ)
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    exact D.rowSeq_next_wf h0 h1 s hs _
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    exact hs

/-- **The row law** (`RowLaw` of `ChildDefs`, for any table satisfying (I0) and (I1)). -/
theorem rowLaw (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState) (hs : D.ChildWF s)
    (r : ℕ × CState) : lam {u | D.childStep s u = r} = ENNReal.ofReal (D.rowLawQ s r : ℝ) := by
  have h := D.lintegral_childStep h0 h1 s hs fun r' => if r' = r then 1 else 0
  rw [D.tsum_rowSeq_eq h0 h1 s hs r] at h
  rw [← h, ← lintegral_indicator_one (D.measurableSet_childStep_eq s r)]
  refine lintegral_congr fun u => ?_
  by_cases hu : D.childStep s u = r <;> simp [Set.indicator, hu]

end FrogModel.Cert.Data

namespace FrogModel.LemmaX

open FrogModel.Cert

/-- **The row law of `cand`.** -/
theorem rowLaw_holds : RowLaw := fun s r hs => cand.rowLaw cand_I0 cand_I1 s hs r

end FrogModel.LemmaX
