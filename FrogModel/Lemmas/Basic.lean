module

public import FrogModel.Lemmas.Defs

@[expose] public section

/-!
# Self-contained lemmas of Sections 3 to 6 of the paper

- Lemma 3.4 (exploration): the stages are determined by the pieces of their own members
  (`closure_eq_of_agree`, `stages_eq_of_agree`); an event insensitive to the coordinates in a
  finite set is independent of them under the product law (`infinitePi_inter_cyl`); hence the
  identity of Lemma 3.4 for events determined by the stage and its pieces (`exploration`).
- Theorem A: the summed recursion (`sum_bound`), Lemma 3.6 as a count of new level-1 vertices
  (`sum_new_le`), the final bound and its monotonicity (`final_bound`), and its value for the
  certificate (`numeric_bound`).
- Lemma 4.2: least fixed points by iteration on `ℕ∞` (`iter_sup_mono`, `iter_sup_le_of_fixed`,
  `iter_sup_fixed`) and the frozen count as a function of the number of steps (`count_mono`).
- Theorem 6.5: the coupling drawn from a transport plan (`coupling_of_plan`) and `G ≤ Z_t` for a
  non-decreasing `G` (`le_const_iff_last`); the quantile coupling is in Lemmas/Quantile.lean.
- Section 4.4: the curve of a block sequence (`brCurve_mono`, `brCurve_mono_succ`,
  `brCurve_first_block`).
-/

open MeasureTheory
open scoped ENNReal

theorem FrogModel.Stage.closure_eq_of_agree {ι P : Type*} (arc : ι → P → ι → Prop) (ω ω' : ι → P)
    (base B : Set ι) (hagree : ∀ σ ∉ B, ω σ = ω' σ)
    (hdisj : Disjoint (FrogModel.Stage.closure arc ω base) B) :
    FrogModel.Stage.closure arc ω' base = FrogModel.Stage.closure arc ω base := by
  set C := FrogModel.Stage.closure arc ω base with hC
  set C' := FrogModel.Stage.closure arc ω' base with hC'
  have hdisj_left : ∀ σ ∈ C, σ ∉ B := Set.disjoint_left.mp hdisj
  have hC_base : base ⊆ C := by
    rw [hC]
    apply Set.subset_sInter
    intro S hS
    exact hS.1
  have hC_closed : ∀ σ ∈ C, ∀ τ, arc σ (ω σ) τ → τ ∈ C := by
    intro σ hσ τ hτ
    rw [hC]
    apply Set.mem_sInter.mpr
    intro S hS
    have hσS : σ ∈ S := Set.sInter_subset_of_mem hS hσ
    exact hS.2 σ hσS τ hτ
  have hC_closed' : ∀ σ ∈ C, ∀ τ, arc σ (ω' σ) τ → τ ∈ C := by
    intro σ hσ τ hτ
    have hσ_not_B : σ ∉ B := hdisj_left σ hσ
    have h_agree : ω σ = ω' σ := hagree σ hσ_not_B
    rw [← h_agree] at hτ
    exact hC_closed σ hσ τ hτ
  have hC'_base : base ⊆ C' := by
    rw [hC']
    apply Set.subset_sInter
    intro S hS
    exact hS.1
  have hC'_closed : ∀ σ ∈ C', ∀ τ, arc σ (ω' σ) τ → τ ∈ C' := by
    intro σ hσ τ hτ
    rw [hC']
    apply Set.mem_sInter.mpr
    intro S hS
    have hσS : σ ∈ S := Set.sInter_subset_of_mem hS hσ
    exact hS.2 σ hσS τ hτ
  -- Step 1: C' ⊆ C, because C contains base and is closed under ω'
  have hC'_subset_C : C' ⊆ C := by
    rw [hC, hC']
    apply Set.sInter_subset_of_mem
    exact ⟨hC_base, hC_closed'⟩
  -- Hence C' is also disjoint from B (since C is)
  have hdisj_left' : ∀ σ ∈ C', σ ∉ B := by
    intro σ hσ
    apply hdisj_left σ
    exact hC'_subset_C hσ
  -- Step 2: C' is closed under ω, because for σ ∈ C', σ ∉ B, so ω' σ = ω σ
  have hC'_closed_ω : ∀ σ ∈ C', ∀ τ, arc σ (ω σ) τ → τ ∈ C' := by
    intro σ hσ τ hτ
    have hσ_not_B : σ ∉ B := hdisj_left' σ hσ
    have h_agree : ω' σ = ω σ := (hagree σ hσ_not_B).symm
    rw [← h_agree] at hτ
    exact hC'_closed σ hσ τ hτ
  -- Step 3: C ⊆ C', because C' contains base and is closed under ω
  have hC_subset_C' : C ⊆ C' := by
    rw [hC, hC']
    apply Set.sInter_subset_of_mem
    exact ⟨hC'_base, hC'_closed_ω⟩
  exact Set.Subset.antisymm hC'_subset_C hC_subset_C'

theorem FrogModel.Stage.stages_eq_of_agree {ι P : Type*} (arc : ι → P → ι → Prop) (closed : ι → P → Prop)
    (succ : ι → ι) (σ₀ : ι) (ω ω' : ι → P) (B : Set ι) (hagree : ∀ σ ∉ B, ω σ = ω' σ) (m : ℕ)
    (hdisj : Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω m) B) :
    FrogModel.Stage.stages arc closed succ σ₀ ω' m = FrogModel.Stage.stages arc closed succ σ₀ ω m := by
  induction' m with m ih
  · rfl
  · -- m.succ case: hdisj is Disjoint (stages ω (m+1)) B
    -- First, prove stages ω m ⊆ stages ω (m+1) so we can get Disjoint (stages ω m) B
    have h_subset : FrogModel.Stage.stages arc closed succ σ₀ ω m ⊆
        FrogModel.Stage.stages arc closed succ σ₀ ω (Nat.succ m) := by
      intro x hx
      rw [FrogModel.Stage.stages]
      have h_base : x ∈ insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
          {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}) := by
        apply Set.subset_insert σ₀
        apply Set.subset_union_left
        exact hx
      have h_closure_base : insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
          {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}) ⊆
          FrogModel.Stage.closure arc ω (insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
          {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ})) := by
        intro y hy
        rw [FrogModel.Stage.closure]
        refine Set.mem_sInter.mpr ?_
        intro S hS
        exact hS.1 hy
      exact h_closure_base h_base
    have hdisj_m : Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω m) B :=
      hdisj.mono_left h_subset
    -- By IH, stages ω m = stages ω' m
    have hstages_eq : FrogModel.Stage.stages arc closed succ σ₀ ω m =
        FrogModel.Stage.stages arc closed succ σ₀ ω' m := (ih hdisj_m).symm
    -- Show the bases are equal
    have hbase_eq : insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
        {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}) =
        insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω' m ∪
        {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω' m, closed σ (ω' σ) ∧ τ = succ σ}) := by
      rw [hstages_eq]
      congr 1
      have hdisj_ω' : Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω' m) B := by
        rwa [← hstages_eq]
      ext τ
      constructor
      · intro h
        rcases h with (hτ | ⟨σ, hσ, hclosed, rfl⟩)
        · left; exact hτ
        · have hσ_notin_B : σ ∉ B := by
            intro hσB
            exact (hdisj_ω'.ne_of_mem hσ hσB) rfl
          have h_eq : ω σ = ω' σ := hagree σ hσ_notin_B
          right; refine ⟨σ, hσ, ?_, rfl⟩
          rw [← h_eq]; exact hclosed
      · intro h
        rcases h with (hτ | ⟨σ, hσ, hclosed, rfl⟩)
        · left; exact hτ
        · have hσ_notin_B : σ ∉ B := by
            intro hσB
            exact (hdisj_ω'.ne_of_mem hσ hσB) rfl
          have h_eq : ω σ = ω' σ := hagree σ hσ_notin_B
          right; refine ⟨σ, hσ, ?_, rfl⟩
          rw [h_eq]; exact hclosed
    -- Now use closure_eq_of_agree_proof
    have hdisj_base : Disjoint (FrogModel.Stage.closure arc ω
        (insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
          {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}))) B := by
      simpa [FrogModel.Stage.stages] using hdisj
    have htemp := FrogModel.Stage.closure_eq_of_agree arc ω ω'
      (insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
        {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}))
      B hagree hdisj_base
    simpa [FrogModel.Stage.stages, hbase_eq] using htemp

theorem FrogModel.Stage.infinitePi_inter_cyl {ι : Type*} {P : ι → Type*} [∀ i, MeasurableSpace (P i)]
    (μ : (i : ι) → Measure (P i)) [∀ i, IsProbabilityMeasure (μ i)] (B : Finset ι)
    (G : Set (∀ i, P i)) (hG : MeasurableSet G)
    (hins : ∀ ω ω' : ∀ i, P i, (∀ i ∉ B, ω i = ω' i) → (ω ∈ G ↔ ω' ∈ G))
    (C : (i : ι) → Set (P i)) (hC : ∀ i, MeasurableSet (C i)) :
    Measure.infinitePi μ (G ∩ {ω | ∀ i ∈ B, ω i ∈ C i}) =
      Measure.infinitePi μ G * ∏ i ∈ B, μ i (C i) := by
  -- The coordinate projections are independent under the infinite product measure
  have h_indep_fun : ProbabilityTheory.iIndepFun (fun (i : ι) (ω : ∀ i, P i) => ω i)
      (Measure.infinitePi μ) :=
    ProbabilityTheory.iIndepFun_infinitePi (fun i => measurable_id)
  -- Convert to independence of the generated sigma-algebras
  have h_indep : ProbabilityTheory.iIndep
      (fun (i : ι) => (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i))
      (Measure.infinitePi μ) :=
    h_indep_fun.iIndep
  -- The two sigma-algebras (coordinates in B and coordinates outside B) are independent
  have h_indep_sigma : ProbabilityTheory.Indep
      (⨆ i ∈ (B : Set ι), (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i))
      (⨆ i ∈ ((B : Set ι))ᶜ, (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i))
      (Measure.infinitePi μ) := by
    refine ProbabilityTheory.indep_iSup_of_disjoint ?_ h_indep ?_
    · intro i
      -- each coordinate sigma-algebra is ≤ the product sigma-algebra
      -- the product sigma-algebra is ⨆ i, comap (eval i)
      exact le_iSup (fun (i : ι) => (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i)) i
    · -- B and its complement are disjoint
      exact disjoint_compl_right
  -- The cylinder set {ω | ∀ i ∈ B, ω i ∈ C i} is measurable w.r.t. the sigma-algebra on B
  have h_cyl_meas : MeasurableSet[⨆ i ∈ (B : Set ι), (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i)]
      {ω | ∀ i ∈ B, ω i ∈ C i} := by
    -- This set is ⋂ i ∈ B, (eval i)⁻¹' (C i)
    have h_eq : {ω : ∀ i, P i | ∀ i ∈ B, ω i ∈ C i} = ⋂ i ∈ (B : Set ι), (fun x => x i) ⁻¹' (C i) := by
      ext x; simp
    rw [h_eq]
    refine Finset.measurableSet_biInter _ (fun i hi => ?_)
    -- Each (eval i)⁻¹' (C i) is in comap (eval i), and comap (eval i) ≤ the iSup
    have h_mem : MeasurableSet[(by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i)]
        ((fun ω => ω i) ⁻¹' (C i)) :=
      MeasurableSpace.measurableSet_comap.mpr ⟨C i, hC i, rfl⟩
    -- Show that the comap is ≤ the iSup
    have h_le : (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i) ≤
        ⨆ i ∈ (B : Set ι), (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i) :=
      le_iSup_of_le i (le_iSup (fun (_ : i ∈ (B : Set ι)) => _) hi)
    exact h_le _ h_mem
  -- G is measurable w.r.t. the sigma-algebra on the complement of B
  have h_G_meas : MeasurableSet[⨆ i ∈ ((B : Set ι))ᶜ, (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i)] G := by
    classical
      -- First, get a point in each P i (nonempty because μ i is a probability measure)
      have h_ne (i : ι) : Nonempty (P i) :=
        MeasureTheory.nonempty_of_isProbabilityMeasure (μ i)
      -- Choose a point x₀ i for each i ∈ B
      let x₀ : ∀ i, P i := fun i => Classical.choice (h_ne i)
      -- Define f : (∀ i, P i) → (∀ i, P i) that is constant on B and identity outside B
      let f : (∀ i, P i) → (∀ i, P i) := fun ω i => if i ∈ B then x₀ i else ω i
      -- The complement sigma-algebra
      let mBc : MeasurableSpace (∀ i, P i) := ⨆ i ∈ ((B : Set ι))ᶜ, (by infer_instance : MeasurableSpace (P i)).comap (fun (ω : ∀ i, P i) => ω i)
      -- f is measurable from mBc to the product sigma-algebra
      have hf_meas : @Measurable _ _ mBc MeasurableSpace.pi f := by
        rw [measurable_pi_iff]
        intro a
        by_cases ha : a ∈ B
        · -- a ∈ B: f x a = x₀ a, which is constant
          have h_eq : (fun (x : ∀ i, P i) => f x a) = fun _ => x₀ a := by
            ext x; simp [f, ha]
          rw [h_eq]
          -- Use measurable_iff_comap_le to reduce to a comap inequality
          rw [measurable_iff_comap_le]
          -- Goal: (mΩ a).comap (fun _ => x₀ a) ≤ mBc
          -- The comap of a constant function is ⊥, which is ≤ any sigma-algebra
          simp
        · -- a ∉ B: f x a = x a, which is the projection
          have h_eq : (fun (x : ∀ i, P i) => f x a) = fun x => x a := by
            ext x; simp [f, ha]
          rw [h_eq]
          -- Need to show eval a is measurable from mBc to mΩ a
          rw [measurable_iff_comap_le]
          -- Goal: (mΩ a).comap (eval a) ≤ mBc
          have h_le : (by infer_instance : MeasurableSpace (P a)).comap (fun (ω : ∀ i, P i) => ω a) ≤ mBc :=
            le_iSup_of_le a (le_iSup (fun (_ : a ∈ ((B : Set ι))ᶜ) => _) ha)
          exact h_le
      -- By hins, f⁻¹' G = G
      have h_preimage : f ⁻¹' G = G := by
        ext ω
        constructor
        · intro h
          have h_eq_off : ∀ i ∉ B, (f ω) i = ω i := by
            intro i hi
            simp [f, hi]
          exact ((hins (f ω) ω) h_eq_off).mp h
        · intro h
          have h_eq_off : ∀ i ∉ B, ω i = (f ω) i := by
            intro i hi
            simp [f, hi]
          exact ((hins ω (f ω)) h_eq_off).mp h
      -- Now we have: f⁻¹' G = G, and f is measurable from mBc
      -- So G is in mBc
      have h_preimage_meas : @MeasurableSet _ mBc (f ⁻¹' G) :=
        hf_meas hG
      rw [h_preimage] at h_preimage_meas
      exact h_preimage_meas
  -- From independence, we get the product formula
  -- h_indep_sigma : Indep mB mBc
  -- h_cyl_meas : MeasurableSet[mB] C, h_G_meas : MeasurableSet[mBc] G
  -- So we get IndepSet C G first, then swap
  have h_indep_set : ProbabilityTheory.IndepSet
      (G : Set (∀ i, P i))
      ({ω | ∀ i ∈ B, ω i ∈ C i} : Set (∀ i, P i))
      (Measure.infinitePi μ) :=
    (h_indep_sigma.indepSet_of_measurableSet h_cyl_meas h_G_meas).symm
  rw [h_indep_set.measure_inter_eq_mul]
  -- Now compute the measure of the cylinder
  have h_cyl_measure : Measure.infinitePi μ {ω | ∀ i ∈ B, ω i ∈ C i} = ∏ i ∈ B, μ i (C i) := by
    have h_eq : {ω | ∀ i ∈ B, ω i ∈ C i} = Set.pi (B : Set ι) C := by
      ext ω; simp
    rw [h_eq]
    exact MeasureTheory.Measure.infinitePi_pi μ (fun i hi => hC i)
  rw [h_cyl_measure]

theorem FrogModel.Stage.exploration {ι P : Type*} [MeasurableSpace P] (μ : ι → Measure P)
    [∀ i, IsProbabilityMeasure (μ i)] (arc : ι → P → ι → Prop) (closed : ι → P → Prop) (succ : ι → ι)
    (σ₀ : ι) (m : ℕ) (G : Set (ι → P))
    (hG : ∀ ω ω' : ι → P,
      FrogModel.Stage.stages arc closed succ σ₀ ω m = FrogModel.Stage.stages arc closed succ σ₀ ω' m →
      (∀ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, ω σ = ω' σ) → (ω ∈ G ↔ ω' ∈ G))
    (B : Finset ι)
    (hmeas : MeasurableSet
      (G ∩ {ω | Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω m) (B : Set ι)}))
    (C : ι → Set P) (hC : ∀ i, MeasurableSet (C i)) :
    Measure.infinitePi μ
        (G ∩ {ω | Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω m) (B : Set ι)} ∩
          {ω | ∀ i ∈ B, ω i ∈ C i}) =
      Measure.infinitePi μ
          (G ∩ {ω | Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω m) (B : Set ι)}) *
        ∏ i ∈ B, μ i (C i) := by
  set E := G ∩ {ω | Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω m) (B : Set ι)} with hE
  have hE_meas : MeasurableSet E := hmeas
  -- E is insensitive to coordinates outside B
  have hE_insens : ∀ ω ω' : ι → P, (∀ i ∉ B, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E) := by
    intro ω ω' hagree
    dsimp [E]
    -- Need: (ω ∈ G ∧ Disjoint (stages ... ω m) B) ↔ (ω' ∈ G ∧ Disjoint (stages ... ω' m) B)
    constructor
    · rintro ⟨hωG, hω_disj⟩
      -- From ω ∈ E, we have Disjoint (stages ... ω m) B
      -- So we can apply stages_eq_of_agree
      have h_stages_eq : FrogModel.Stage.stages arc closed succ σ₀ ω' m =
          FrogModel.Stage.stages arc closed succ σ₀ ω m :=
        FrogModel.Stage.stages_eq_of_agree arc closed succ σ₀ ω ω' (B : Set ι) hagree m hω_disj
      -- Now we need to show ω' ∈ G and Disjoint (stages ... ω' m) B
      -- For G: by hG, since stages are equal and ω, ω' agree on stages, ω' ∈ G ↔ ω ∈ G
      have h_agree_on_stages : ∀ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, ω σ = ω' σ := by
        intro σ hσ
        -- σ ∈ stages ... ω m, and stages ... ω m is disjoint from B
        -- So σ ∉ B, and hagree gives ω σ = ω' σ
        have hσ_not_B : σ ∉ (B : Set ι) := by
          intro hσB
          apply hω_disj.ne_of_mem hσ hσB
          rfl
        exact hagree σ hσ_not_B
      have hω'_G : ω' ∈ G := ((hG ω ω' h_stages_eq.symm h_agree_on_stages).mp hωG)
      -- For disjointness: stages ... ω' m = stages ... ω m, so it's also disjoint from B
      have hω'_disj : Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω' m) (B : Set ι) := by
        rw [h_stages_eq]
        exact hω_disj
      exact ⟨hω'_G, hω'_disj⟩
    · rintro ⟨hω'_G, hω'_disj⟩
      -- Symmetric argument
      have h_stages_eq : FrogModel.Stage.stages arc closed succ σ₀ ω m =
          FrogModel.Stage.stages arc closed succ σ₀ ω' m :=
        FrogModel.Stage.stages_eq_of_agree arc closed succ σ₀ ω' ω (B : Set ι) (by
          intro i hi
          apply (hagree i hi).symm) m hω'_disj
      have h_agree_on_stages : ∀ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω' m, ω' σ = ω σ := by
        intro σ hσ
        have hσ_not_B : σ ∉ (B : Set ι) := by
          intro hσB
          apply hω'_disj.ne_of_mem hσ hσB
          rfl
        exact (hagree σ hσ_not_B).symm
      have hω_G : ω ∈ G := ((hG ω' ω h_stages_eq.symm h_agree_on_stages).mp hω'_G)
      have hω_disj : Disjoint (FrogModel.Stage.stages arc closed succ σ₀ ω m) (B : Set ι) := by
        rw [h_stages_eq]
        exact hω'_disj
      exact ⟨hω_G, hω_disj⟩
  -- Now apply infinitePi_inter_cyl from Work.Deps
  exact FrogModel.Stage.infinitePi_inter_cyl (μ := μ) (B := B) (G := E)
    (hG := hE_meas) (hins := hE_insens) (C := C) (hC := hC)

theorem FrogModel.TheoremA.sum_bound (r w : ℕ → ℝ≥0∞) (x D : ℝ≥0∞) (hx : x < 1) (hD : D ≠ ⊤)
    (h0 : r 0 = 1) (hstep : ∀ i, r (i + 1) ≤ x * (r i + w (i + 1)))
    (hw : ∑' i, w (i + 1) ≤ D) :
    ∑' i, r (i + 1) ≤ x * (1 + D) / (1 - x) := by
  have hx_ne_top : x ≠ ⊤ := by
    have hx_lt_top : x < ⊤ := lt_of_lt_of_le hx le_top
    exact ne_of_lt hx_lt_top
  have hx_lt_top : x < ⊤ := lt_of_lt_of_le hx le_top
  have hD_lt_top : D < ⊤ := lt_top_iff_ne_top.mpr hD
  -- each w (i+1) is finite
  have hw_fin : ∀ i, w (i + 1) < ⊤ := by
    intro i
    have hle : w (i + 1) ≤ ∑' j, w (j + 1) := ENNReal.le_tsum (f := fun j => w (j + 1)) (a := i)
    have : w (i + 1) ≤ D := le_trans hle hw
    exact lt_of_le_of_lt this hD_lt_top
  -- each r i is finite
  have hr_fin : ∀ i, r i < ⊤ := by
    intro i
    induction' i with i ih
    · rw [h0]
      exact ENNReal.one_lt_top
    · have hle : r (i + 1) ≤ x * (r i + w (i + 1)) := hstep i
      have hsum_lt_top : r i + w (i + 1) < ⊤ := by
        rw [ENNReal.add_lt_top]
        exact ⟨ih, hw_fin i⟩
      have hx_mul_lt_top : x * (r i + w (i + 1)) < ⊤ :=
        ENNReal.mul_lt_top hx_lt_top hsum_lt_top
      exact lt_of_le_of_lt hle hx_mul_lt_top
  -- define partial sums S n = ∑ i ∈ range n, r (i+1)
  let S : ℕ → ℝ≥0∞ := fun n => ∑ i ∈ Finset.range n, r (i + 1)
  have hS_succ : ∀ n, S (n + 1) = S n + r (n + 1) := by
    intro n
    simp [S, Finset.sum_range_succ]
  have hS_zero : S 0 = 0 := by simp [S]
  -- each S n is finite
  have hS_fin : ∀ n, S n < ⊤ := by
    intro n
    induction' n with n ih
    · rw [hS_zero]
      exact ENNReal.zero_lt_top
    · rw [hS_succ n]
      rw [ENNReal.add_lt_top]
      exact ⟨ih, hr_fin (n + 1)⟩
  -- lemma: ∑ i ∈ range n, r i ≤ 1 + S n
  have hsum_r_bound : ∀ n, ∑ i ∈ Finset.range n, r i ≤ 1 + S n := by
    have hS_mono : ∀ m, S m ≤ S (m + 1) := by
      intro m; rw [hS_succ m]; exact le_add_of_nonneg_right (zero_le (a := r (m + 1)))
    have h_eq : ∀ m, ∑ i ∈ Finset.range (m + 1), r i = 1 + S m := by
      intro m
      induction' m with m ih
      · simp [S, h0]
      · simp [Finset.sum_range_succ, S, ih, add_assoc]
    intro n
    by_cases hn : n = 0
    · subst hn; simp [S]
    · rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, hm⟩
      subst hm
      rw [h_eq m]
      gcongr
      exact hS_mono m
  -- key inequality for each n: S n ≤ x * (1 + S n + D)
  have hS_le : ∀ n, S n ≤ x * (1 + S n + D) := by
    intro n
    calc
      S n = ∑ i ∈ Finset.range n, r (i + 1) := rfl
      _ ≤ ∑ i ∈ Finset.range n, (x * (r i + w (i + 1))) :=
        Finset.sum_le_sum (fun i _ => hstep i)
      _ = x * ∑ i ∈ Finset.range n, (r i + w (i + 1)) := by
        rw [Finset.mul_sum]
      _ = x * (∑ i ∈ Finset.range n, r i + ∑ i ∈ Finset.range n, w (i + 1)) := by
        rw [Finset.sum_add_distrib]
      _ ≤ x * (1 + S n + D) := by
        have hsum_w : ∑ i ∈ Finset.range n, w (i + 1) ≤ D := by
          calc
            ∑ i ∈ Finset.range n, w (i + 1) ≤ ∑' i, w (i + 1) :=
              ENNReal.sum_le_tsum (Finset.range n) (f := fun i => w (i + 1))
            _ ≤ D := hw
        have h_total : ∑ i ∈ Finset.range n, r i + ∑ i ∈ Finset.range n, w (i + 1) ≤ 1 + S n + D :=
          add_le_add (hsum_r_bound n) hsum_w
        gcongr
  -- Now from S n ≤ x * (1 + S n + D), deduce S n ≤ x * (1 + D) / (1 - x)
  have hS_bound : ∀ n, S n ≤ x * (1 + D) / (1 - x) := by
    intro n
    have h_le : S n ≤ x * (1 + S n + D) := hS_le n
    -- First show RHS < ⊤ so we can use toReal_mono
    have h_rhs_lt_top : x * (1 + S n + D) < ⊤ := by
      have h_one_add_Sn_lt_top : 1 + S n < ⊤ := by
        rw [ENNReal.add_lt_top]
        exact ⟨ENNReal.one_lt_top, hS_fin n⟩
      have h_sum_lt_top : 1 + S n + D < ⊤ := by
        -- (1 + S n) + D < ⊤
        rw [ENNReal.add_lt_top]
        exact ⟨h_one_add_Sn_lt_top, hD_lt_top⟩
      exact ENNReal.mul_lt_top hx_lt_top h_sum_lt_top
    have h_toReal_le : (S n).toReal ≤ (x * (1 + S n + D)).toReal :=
      ENNReal.toReal_mono h_rhs_lt_top.ne h_le
    -- Compute RHS in ℝ
    have h_rhs : (x * (1 + S n + D)).toReal = x.toReal * (1 + (S n).toReal + D.toReal) := by
      rw [ENNReal.toReal_mul]
      have h1 : (1 + S n + D).toReal = 1 + (S n).toReal + D.toReal := by
        calc
          (1 + S n + D).toReal = ((1 + S n) + D).toReal := rfl
          _ = (1 + S n).toReal + D.toReal := by
            rw [ENNReal.toReal_add (by
              rw [ENNReal.add_ne_top]
              exact ⟨ENNReal.one_ne_top, (hS_fin n).ne⟩) hD_lt_top.ne]
          _ = ((1 : ℝ≥0∞).toReal + (S n).toReal) + D.toReal := by
            rw [ENNReal.toReal_add ENNReal.one_ne_top (hS_fin n).ne]
          _ = 1 + (S n).toReal + D.toReal := by simp
      rw [h1]
    rw [h_rhs] at h_toReal_le
    -- Algebra in ℝ
    have h_real : (S n).toReal * (1 - x.toReal) ≤ x.toReal * (1 + D.toReal) := by
      linarith
    -- Convert back to ENNReal
    have h_prod_le : S n * (1 - x) ≤ x * (1 + D) := by
      have h_left' : (S n * (1 - x)).toReal = (S n).toReal * (1 - x.toReal) := by
        rw [ENNReal.toReal_mul]
        have hx_le_one : x ≤ 1 := le_of_lt hx
        rw [ENNReal.toReal_sub_of_le hx_le_one ENNReal.one_ne_top]
        simp
      have h_right : (x * (1 + D)).toReal = x.toReal * (1 + D.toReal) := by
        rw [ENNReal.toReal_mul]
        rw [ENNReal.toReal_add ENNReal.one_ne_top hD_lt_top.ne]
        simp
      have h_toReal_prod : (S n * (1 - x)).toReal ≤ (x * (1 + D)).toReal := by
        rw [h_left', h_right]
        exact h_real
      have h_left_fin : S n * (1 - x) ≠ ⊤ :=
        ENNReal.mul_ne_top (hS_fin n).ne (ENNReal.sub_ne_top ENNReal.one_ne_top)
      have h_right_fin : x * (1 + D) ≠ ⊤ := by
        have h_one_add_D_fin : 1 + D ≠ ⊤ := by
          rw [ENNReal.add_ne_top]
          exact ⟨ENNReal.one_ne_top, hD_lt_top.ne⟩
        exact ENNReal.mul_ne_top hx_ne_top h_one_add_D_fin
      exact ((ENNReal.toReal_le_toReal h_left_fin h_right_fin).mp h_toReal_prod)
    -- Apply ENNReal.le_div_iff_mul_le
    have h_cond1 : (1 - x) ≠ 0 ∨ x * (1 + D) ≠ 0 := by
      left
      intro hzero
      have hle : (1 : ℝ≥0∞) ≤ x := (tsub_eq_zero_iff_le.mp hzero)
      exact not_le.mpr hx hle
    have h_cond2 : (1 - x) ≠ ⊤ ∨ x * (1 + D) ≠ ⊤ := by
      left
      exact ENNReal.sub_ne_top ENNReal.one_ne_top
    rw [ENNReal.le_div_iff_mul_le h_cond1 h_cond2]
    exact h_prod_le
  -- take supremum
  have htsum : ∑' i, r (i + 1) = ⨆ n, S n := by
    rw [ENNReal.tsum_eq_iSup_nat]
  rw [htsum]
  exact iSup_le hS_bound

theorem FrogModel.TheoremA.sum_new_le (d : ℕ) (U : ℕ → Set (Fin d)) (hU : Monotone U)
    (h0 : U 0 = ∅) (W : ℕ → ℕ) (hW : ∀ i, W (i + 1) ≤ (U (i + 1) \ U i).ncard) :
    ∑' i, (W (i + 1) : ℝ≥0∞) ≤ d := by
  -- First, prove the key lemma about ncard
  have h_ncard_eq (n : ℕ) : (U n).ncard = ∑ a ∈ Finset.range n, (U (a+1) \ U a).ncard := by
    induction' n with n ih
    · simp [h0]
    · rw [Finset.sum_range_succ, ← ih]
      have hsub : U n ⊆ U (n+1) := hU (by omega)
      have hfin : (U (n+1)).Finite :=
        Set.Finite.subset (Set.finite_univ (α := Fin d)) (by intro x hx; exact Set.mem_univ x)
      have h_eq := Set.ncard_sdiff_add_ncard_of_subset hsub hfin
      omega
  -- Now use ENNReal.tsum_eq_iSup_nat
  rw [ENNReal.tsum_eq_iSup_nat]
  refine ciSup_le ?_
  intro n
  -- Goal: ∑ a ∈ Finset.range n, (W (a+1) : ℝ≥0∞) ≤ d
  calc
    ∑ a ∈ Finset.range n, (W (a+1) : ℝ≥0∞) ≤ ∑ a ∈ Finset.range n, ((U (a+1) \ U a).ncard : ℝ≥0∞) := by
      refine Finset.sum_le_sum ?_
      intro a ha
      have h := hW a
      exact mod_cast h
    _ = ((U n).ncard : ℝ≥0∞) := by
      simp [h_ncard_eq n]
    _ ≤ (d : ℝ≥0∞) := by
      have h_le : (U n).ncard ≤ d := by
        have h_sub : U n ⊆ Set.univ := Set.subset_univ _
        have h_fin : (Set.univ : Set (Fin d)).Finite := Set.finite_univ
        have h_card : (Set.univ : Set (Fin d)).ncard = d := by simp
        calc
          (U n).ncard ≤ (Set.univ : Set (Fin d)).ncard := Set.ncard_le_ncard h_sub h_fin
          _ = d := h_card
      exact mod_cast h_le

theorem FrogModel.TheoremA.final_bound (d : ℕ) (x c D : ℝ≥0∞) (hD : D ≤ d) (hxc : x ≤ c)
    (hc : c < 1) : x * (1 + D) / (1 - x) ≤ (d + 1) * c / (1 - c) := by
  have hx_lt_one : x < 1 := lt_of_le_of_lt hxc hc
  have h_num : x * (1 + D) ≤ ((d : ℝ≥0∞) + 1) * c := by
    have h1 : (1 : ℝ≥0∞) + D ≤ (1 : ℝ≥0∞) + (d : ℝ≥0∞) := by
      simpa [add_comm] using add_le_add_right hD (1 : ℝ≥0∞)
    have h2 : x * (1 + D) ≤ c * ((1 : ℝ≥0∞) + (d : ℝ≥0∞)) :=
      mul_le_mul hxc h1 (by positivity) (by positivity)
    simpa [add_comm, mul_comm] using h2
  have h_denom : (1 : ℝ≥0∞) - c ≤ (1 : ℝ≥0∞) - x := by
    have hpos : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
    exact ((ENNReal.sub_le_sub_iff_left hx_lt_one.le hpos).2 hxc)
  exact ENNReal.div_le_div h_num h_denom

theorem FrogModel.TheoremA.numeric_bound :
    (5 : ℝ) * (9337230319347 / 17448304640000) / (1 - 9337230319347 / 17448304640000) <
      5756 / 1000 := by
  norm_num

theorem FrogModel.Order.iter_sup_mono (T T' : ℕ∞ → ℕ∞) (hT' : Monotone T')
    (hle : ∀ n, T n ≤ T' n) (j j' : ℕ∞) (hj : j ≤ j') :
    ⨆ t : ℕ, T^[t] j ≤ ⨆ t : ℕ, T'^[t] j' := by
  have h_iter : ∀ t : ℕ, T^[t] j ≤ T'^[t] j' := by
    intro t
    induction' t with t ih
    · exact hj
    · rw [Function.iterate_succ', Function.iterate_succ']
      calc
        (T ∘ T^[t]) j = T (T^[t] j) := rfl
        _ ≤ T' (T^[t] j) := hle _
        _ ≤ T' (T'^[t] j') := hT' ih
        _ = (T' ∘ T'^[t]) j' := rfl
  exact iSup_mono h_iter

theorem FrogModel.Order.iter_sup_le_of_fixed (T : ℕ∞ → ℕ∞) (hT : Monotone T) (j N : ℕ∞)
    (hjN : j ≤ N) (hN : T N ≤ N) : ⨆ t : ℕ, T^[t] j ≤ N := by
  refine ciSup_le ?_
  intro t
  induction' t with t ih
  · exact hjN
  · rw [Function.iterate_succ_apply']
    calc
      T (T^[t] j) ≤ T N := hT ih
      _ ≤ N := hN

theorem FrogModel.Order.iter_sup_fixed (T : ℕ∞ → ℕ∞) (hT : Monotone T)
    (hcont : ∀ a : ℕ → ℕ∞, Monotone a → T (⨆ t, a t) = ⨆ t, T (a t)) (j : ℕ∞) (hj : j ≤ T j) :
    T (⨆ t : ℕ, T^[t] j) = ⨆ t : ℕ, T^[t] j := by
  let a : ℕ → ℕ∞ := fun t => T^[t] j
  have ha_mono : Monotone a := by
    refine monotone_nat_of_le_succ fun n => ?_
    show a n ≤ a (n+1)
    dsimp [a]
    induction' n with k ih
    · -- n = 0: j ≤ T j
      exact hj
    · -- n = k+1: T^[k+1] j ≤ T^[k+2] j
      -- goal: T^[k+1] j ≤ T^[k+2] j
      -- Note: T^[k+2] j simplifies to T^[k+1] (T j)
      -- and T^[k+1] j = T (T^[k] j)
      -- ih: T^[k] j ≤ T^[k] (T j) (which is T^[k] j ≤ T^[k+1] j)
      calc
        T^[k+1] j = T (T^[k] j) := by
          rw [Function.iterate_succ_apply']
        _ ≤ T (T^[k] (T j)) := hT ih
        _ = T^[k+1] (T j) := by
          rw [Function.iterate_succ_apply']
  have h_eq : T (⨆ t, a t) = ⨆ t, a t := by
    rw [hcont a ha_mono]
    -- T (a t) = T (T^[t] j) = T^[t+1] j = a (t+1)
    have hT_a : ∀ t, T (a t) = a (t+1) := by
      intro t
      dsimp [a]
      -- goal: T (T^[t] j) = T^[t+1] j
      -- T^[t+1] j may be simplified to T^[t] (T j)
      -- use iterate_succ_apply' which gives T^[t+1] j = T (T^[t] j)
      simpa using (Function.iterate_succ_apply' T t j).symm
    simp_rw [hT_a]
    -- Now: ⨆ t, a (t+1) = ⨆ t, a t
    -- ha_mono.iSup_nat_add 1 gives ⨆ n, a (n+1) = ⨆ n, a n
    exact ha_mono.iSup_nat_add 1
  simpa [a] using h_eq

theorem FrogModel.Order.count_mono (D : ℕ → ℕ) (N N' : ℕ∞) (h : N ≤ N') :
    {k : ℕ | (k : ℕ∞) < N ∧ D k = 0}.encard ≤ {k : ℕ | (k : ℕ∞) < N' ∧ D k = 0}.encard := by
  apply Set.encard_mono
  intro k hk
  rcases hk with ⟨hlt, hD⟩
  exact ⟨lt_of_lt_of_le hlt h, hD⟩

theorem FrogModel.Order.coupling_of_plan {α β : Type*} [Fintype α] [Fintype β] (R : α → β → Prop)
    (L : α → ℝ) (h : β → ℝ) (hh : ∀ y, 0 ≤ h y) (a : α → β → ℝ) (ha : ∀ x y, 0 ≤ a x y)
    (haR : ∀ x y, a x y ≠ 0 → R x y) (hfill : ∀ y, h y ≤ ∑ x, a x y)
    (hdraw : ∀ x, ∑ y, a x y ≤ L x) :
    ∃ π : α → β → ℝ, (∀ x y, 0 ≤ π x y) ∧ (∀ x y, π x y ≠ 0 → R x y) ∧
      (∀ y, ∑ x, π x y = h y) ∧ ∀ x, ∑ y, π x y ≤ L x := by
  set S := fun (y : β) => ∑ x : α, a x y with hS
  have hS_nonneg : ∀ y, 0 ≤ S y := by
    intro y
    apply Finset.sum_nonneg
    intro x _
    exact ha x y
  set π := fun (x : α) (y : β) => a x y * (h y / S y) with hπ
  have hdiv_nonneg : ∀ y, 0 ≤ h y / S y := by
    intro y
    by_cases hSy : S y = 0
    · rw [hSy, div_zero]
    · have hSy_pos : 0 < S y := by
        by_contra! H
        have heq : S y = 0 := le_antisymm H (hS_nonneg y)
        exact hSy heq
      apply div_nonneg (hh y) (by linarith)
  have hdiv_le_one : ∀ y, h y / S y ≤ 1 := by
    intro y
    by_cases hSy : S y = 0
    · rw [hSy, div_zero]
      exact zero_le_one
    · have hSy_pos : 0 < S y := by
        by_contra! H
        have heq : S y = 0 := le_antisymm H (hS_nonneg y)
        exact hSy heq
      exact ((div_le_one hSy_pos).mpr (hfill y))
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity of π
    intro x y
    dsimp [π]
    exact mul_nonneg (ha x y) (hdiv_nonneg y)
  · -- π x y ≠ 0 → R x y
    intro x y hπxy
    apply haR x y
    contrapose! hπxy
    dsimp [π]
    rw [hπxy, zero_mul]
  · -- column sums
    intro y
    by_cases hSy : S y = 0
    · have hy0 : h y = 0 := by
        have hy_le : h y ≤ S y := hfill y
        rw [hSy] at hy_le
        linarith [hh y, hy_le]
      simp [π, hSy, div_zero, hy0]
    · have hSy_pos : 0 < S y := by
        by_contra! H
        have heq : S y = 0 := le_antisymm H (hS_nonneg y)
        exact hSy heq
      calc
        ∑ x : α, π x y = ∑ x : α, a x y * (h y / S y) := rfl
        _ = (∑ x : α, a x y) * (h y / S y) := by rw [Finset.sum_mul]
        _ = S y * (h y / S y) := by rw [hS]
        _ = h y := by field_simp [hSy]
  · -- row sums
    intro x
    calc
      ∑ y : β, π x y = ∑ y : β, a x y * (h y / S y) := rfl
      _ ≤ ∑ y : β, a x y * 1 := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left (hdiv_le_one y) (ha x y)
      _ = ∑ y : β, a x y := by simp
      _ ≤ L x := hdraw x

theorem FrogModel.Order.le_const_iff_last (J : ℕ) (G : Fin (J + 1) → ℕ∞) (hG : Monotone G)
    (t : ℕ∞) : (∀ i, G i ≤ t) ↔ G (Fin.last J) ≤ t := by
  constructor
  · intro h
    exact h (Fin.last J)
  · intro h i
    exact le_trans (hG (Fin.le_last i)) h

theorem FrogModel.Order.brCurve_mono (J : ℕ) (B B' : ℕ → ℕ → ℕ∞) (h : ∀ b s, B b s ≤ B' b s)
    (n : ℕ) : FrogModel.Order.brCurve J B n ≤ FrogModel.Order.brCurve J B' n := by
  unfold FrogModel.Order.brCurve
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    apply h i J
  · apply h

theorem FrogModel.Order.brCurve_mono_succ (J : ℕ) (hJ : 1 ≤ J) (B : ℕ → ℕ → ℕ∞)
    (hB : ∀ b, Monotone (B b)) (hB0 : ∀ b, B b 0 = 0) (n : ℕ) :
    FrogModel.Order.brCurve J B n ≤ FrogModel.Order.brCurve J B (n + 1) := by
  have hJpos : 0 < J := by omega
  set q := n / J with hq
  set s := n % J with hs
  have hs_lt_J : s < J := Nat.mod_lt n hJpos
  have hdivmod : n = q * J + s := by
    have h := Nat.div_add_mod n J
    rw [← hq, ← hs] at h
    rw [← h, Nat.mul_comm J q]
  unfold FrogModel.Order.brCurve
  by_cases h : s + 1 < J
  · -- case s+1 < J: (n+1)/J = q, (n+1)%J = s+1
    have hle : s ≤ s + 1 := Nat.le_add_right s 1
    have hsum : (∑ b ∈ Finset.range q, B b J) + B q s ≤ (∑ b ∈ Finset.range q, B b J) + B q (s + 1) :=
      add_le_add_right (hB q hle) _
    have hdivmod1 : (n + 1) / J = q ∧ (n + 1) % J = s + 1 := by
      apply ((Nat.div_mod_unique hJpos).mpr ⟨?_, h⟩)
      have h_eq := Nat.div_add_mod n J
      rw [← hq, ← hs] at h_eq
      omega
    rcases hdivmod1 with ⟨hdiv1, hmod1⟩
    simp [hdiv1, hmod1]
    exact hsum
  · -- case s+1 ≥ J, so s+1 = J (since s < J)
    have hs_eq : s + 1 = J := by omega
    have hle : s ≤ J := Nat.le_of_lt hs_lt_J
    have hsum : (∑ b ∈ Finset.range q, B b J) + B q s ≤ (∑ b ∈ Finset.range q, B b J) + B q J :=
      add_le_add_right (hB q hle) _
    have hdivmod1 : (n + 1) / J = q + 1 ∧ (n + 1) % J = 0 := by
      apply ((Nat.div_mod_unique hJpos).mpr ⟨?_, by omega⟩)
      have h_eq := Nat.div_add_mod n J
      rw [← hq, ← hs] at h_eq
      calc
        0 + J * (q + 1) = J * (q + 1) := by simp
        _ = J * q + J := by ring
        _ = J * q + (s + 1) := by rw [hs_eq]
        _ = (J * q + s) + 1 := by omega
        _ = n + 1 := by rw [← h_eq]
    rcases hdivmod1 with ⟨hdiv1, hmod1⟩
    calc
      (∑ b ∈ Finset.range q, B b J) + B q s ≤ (∑ b ∈ Finset.range q, B b J) + B q J := hsum
      _ = (∑ b ∈ Finset.range q, B b J) + B q J + 0 := by simp
      _ = (∑ b ∈ Finset.range q, B b J) + B q J + B (q + 1) 0 := by rw [hB0 (q + 1)]
      _ = (∑ b ∈ Finset.range (q + 1), B b J) + B (q + 1) 0 := by rw [Finset.sum_range_succ]
      _ = (∑ b ∈ Finset.range ((n + 1) / J), B b J) + B ((n + 1) / J) ((n + 1) % J) := by rw [hdiv1, hmod1]

theorem FrogModel.Order.brCurve_first_block (J : ℕ) (hJ : 1 ≤ J) (B : ℕ → ℕ → ℕ∞)
    (hB0 : ∀ b, B b 0 = 0) : ∀ n ≤ J, FrogModel.Order.brCurve J B n = B 0 n := by
  intro n hn
  rcases Nat.lt_or_eq_of_le hn with (hlt | heq)
  · -- n < J
    have hdiv : n / J = 0 := Nat.div_eq_of_lt hlt
    have hmod : n % J = n := Nat.mod_eq_of_lt hlt
    unfold FrogModel.Order.brCurve
    simp [hdiv, hmod]
  · -- n = J
    have hpos : 0 < J := by omega
    have hdiv : J / J = 1 := Nat.div_self hpos
    have hmod : J % J = 0 := Nat.mod_self J
    subst heq
    unfold FrogModel.Order.brCurve
    simp [hdiv, hmod, hB0 1]
