module

public import FrogModel.Lemmas.Basic

@[expose] public section

/-!
# The refresh lemma (Lemma 3.4 of the paper)

For a stopping set `K` of a product of probability spaces (a random set of coordinates determined
by its own coordinates) and an event `G` determined by the coordinates in `K`, replacing the
coordinates in `K` by fresh independent ones gives, on `G`, a family with the product law,
independent of `G`: `map_refresh`, `lintegral_refresh`. The proof splits a box by the pattern of
`K` on it (`refresh_preimage_pi`, `pairwiseDisjoint_pattern`, `sum_pattern`) and applies
`Stage.infinitePi_inter_cyl` (`infinitePi_pattern_cyl`, `refresh_box`). The stages are stopping
sets (`isStoppingSet_stages`). Laws of reindexed coordinates: `infinitePi_map_comp_injective`,
`infinitePi_map_pair_injective`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open FrogModel

theorem FrogModel.Stage.measurable_refresh {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (K : (∀ i, X i) → Set ι)
    (hKm : ∀ i, MeasurableSet {ω : ∀ i, X i | i ∈ K ω}) :
    Measurable fun p : (∀ i, X i) × (∀ i, X i) => FrogModel.Stage.refresh K p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  have h_cond : MeasurableSet {p : (∀ i, X i) × (∀ i, X i) | i ∈ K p.1} :=
    measurable_fst (hKm i)
  have h_then : Measurable fun (p : (∀ i, X i) × (∀ i, X i)) => p.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  have h_else : Measurable fun (p : (∀ i, X i) × (∀ i, X i)) => p.1 i :=
    (measurable_pi_apply i).comp measurable_fst
  unfold FrogModel.Stage.refresh
  exact Measurable.ite h_cond h_then h_else

theorem FrogModel.Stage.refresh_preimage_pi {ι : Type*} {X : ι → Type*} [DecidableEq ι]
    (K : (∀ i, X i) → Set ι) (G : Set (∀ i, X i)) (s : Finset ι) (t : ∀ i, Set (X i)) :
    (G ×ˢ Set.univ) ∩
        (fun p : (∀ i, X i) × (∀ i, X i) => FrogModel.Stage.refresh K p.1 p.2) ⁻¹'
          Set.pi (↑s) t =
      ⋃ B ∈ s.powerset,
        (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t) ×ˢ Set.pi (↑B) t := by
  ext ⟨ω, ω'⟩
  simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, Set.mem_preimage, Set.mem_pi,
    Set.mem_iUnion, Finset.mem_powerset, Finset.mem_coe, Finset.mem_sdiff, Set.mem_setOf_eq]
  unfold FrogModel.Stage.refresh
  classical
  constructor
  · intro ⟨⟨hG, _⟩, hpi⟩
    let B := s.filter fun i => i ∈ K ω
    have hB_sub : B ⊆ s := Finset.filter_subset _ _
    have hK_iff : ∀ i ∈ s, i ∈ K ω ↔ i ∈ B := by
      intro i hi
      simp [B, Finset.mem_filter, hi]
    have hpi_sdiff : ∀ (i : ι), i ∈ s ∧ i ∉ B → ω i ∈ t i := by
      intro i ⟨hi, hnot⟩
      have hnotK : i ∉ K ω := by
        intro hKi
        apply hnot
        simp [B, Finset.mem_filter, hi, hKi]
      have hpi_i := hpi i hi
      simp [hnotK] at hpi_i
      exact hpi_i
    have hpi_B : ∀ i ∈ B, ω' i ∈ t i := by
      intro i hi
      have hiK : i ∈ K ω := (Finset.mem_filter.mp hi).2
      have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
      have hpi_i := hpi i hi_s
      simp [hiK] at hpi_i
      exact hpi_i
    exact ⟨B, hB_sub, ⟨⟨⟨hG, hK_iff⟩, hpi_sdiff⟩, hpi_B⟩⟩
  · intro ⟨B, hB_sub, ⟨⟨hG, hK_iff⟩, hpi_sdiff⟩, hpi_B⟩
    have hpi : ∀ i ∈ s, (if i ∈ K ω then ω' i else ω i) ∈ t i := by
      intro i hi
      by_cases hiK : i ∈ K ω
      · have hiB : i ∈ B := (hK_iff i hi).mp hiK
        have h := hpi_B i hiB
        simp [hiK, h]
      · have hiB : i ∉ B := mt ((hK_iff i hi).mpr) hiK
        have h := hpi_sdiff i ⟨hi, hiB⟩
        simp [hiK, h]
    exact ⟨⟨hG, trivial⟩, hpi⟩

theorem FrogModel.Stage.pairwiseDisjoint_pattern {ι : Type*} {X : ι → Type*} [DecidableEq ι]
    (K : (∀ i, X i) → Set ι) (G : Set (∀ i, X i)) (s : Finset ι) (t : ∀ i, Set (X i)) :
    (↑s.powerset : Set (Finset ι)).PairwiseDisjoint fun B =>
      (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t) ×ˢ Set.pi (↑B) t := by
  intro B hB B' hB' hne
  have hBmem : B ∈ s.powerset := by simpa using hB
  have hB'mem : B' ∈ s.powerset := by simpa using hB'
  have hBsub : (B : Set ι) ⊆ s := Finset.mem_powerset.mp hBmem
  have hB'sub : (B' : Set ι) ⊆ s := Finset.mem_powerset.mp hB'mem
  have hdiff : ∃ i ∈ s, (i ∈ B) ≠ (i ∈ B') := by
    by_contra! h
    -- h: ∀ i, i ∉ s ∨ (i ∈ B) = (i ∈ B')
    have h_all : ∀ i, i ∈ B ↔ i ∈ B' := by
      intro i
      by_cases hi : i ∈ s
      · exact ⟨fun hiB => (h i hi) ▸ hiB, fun hiB' => (h i hi).symm ▸ hiB'⟩
      · have hiB : i ∉ B := fun h' => hi (hBsub h')
        have hiB' : i ∉ B' := fun h' => hi (hB'sub h')
        simp [hiB, hiB']
    exact hne (Finset.ext h_all)
  rcases hdiff with ⟨i, hi, hdiff'⟩
  apply Set.disjoint_prod.mpr (Or.inl ?_)
  apply Set.disjoint_left.mpr
  intro ω hω1 hω2
  rcases hω1 with ⟨⟨hωG, hωK⟩, hωPi⟩
  rcases hω2 with ⟨⟨hωG', hωK'⟩, hωPi'⟩
  have hB_eq_B' : (i ∈ B) = (i ∈ B') := by
    apply propext
    constructor
    · intro hiB
      exact ((hωK' i hi).mp ((hωK i hi).mpr hiB))
    · intro hiB'
      exact ((hωK i hi).mp ((hωK' i hi).mpr hiB'))
  exact hdiff' hB_eq_B'

theorem FrogModel.Stage.sum_pattern {ι Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω)
    (K : Ω → Set ι) (hKm : ∀ i, MeasurableSet {ω | i ∈ K ω}) (G : Set Ω) (hG : MeasurableSet G)
    (s : Finset ι) :
    ∑ B ∈ s.powerset, m (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B}) = m G := by
  let A (B : Finset ι) : Set Ω := G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B}
  have h_disjoint : Set.PairwiseDisjoint ((s.powerset : Set (Finset ι))) A := by
    intro B hB C hC hne
    have h_disjoint' : Disjoint (A B) (A C) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      simp [A] at hx
      rcases hx with ⟨⟨hxG, hxB⟩, ⟨_, hxC⟩⟩
      have hB_sub : B ⊆ s := by
        rwa [Finset.mem_coe, Finset.mem_powerset] at hB
      have hC_sub : C ⊆ s := by
        rwa [Finset.mem_coe, Finset.mem_powerset] at hC
      have h_eq : B = C := by
        apply Finset.Subset.antisymm
        · intro i hi
          have hi_s : i ∈ s := hB_sub hi
          have h_iffB := hxB i hi_s
          have h_iffC := hxC i hi_s
          have hiK : i ∈ K x := h_iffB.mpr hi
          exact h_iffC.mp hiK
        · intro i hi
          have hi_s : i ∈ s := hC_sub hi
          have h_iffB := hxB i hi_s
          have h_iffC := hxC i hi_s
          have hiK : i ∈ K x := h_iffC.mpr hi
          exact h_iffB.mp hiK
      exact hne h_eq
    exact h_disjoint'
  have h_meas : ∀ B ∈ s.powerset, MeasurableSet (A B) := by
    intro B hB
    dsimp [A]
    apply hG.inter
    have : {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} = ⋂ i ∈ s, {ω | i ∈ K ω ↔ i ∈ B} := by
      ext ω; simp
    rw [this]
    apply Finset.measurableSet_biInter
    intro i hi
    by_cases hiB : i ∈ B
    · have : {ω | i ∈ K ω ↔ i ∈ B} = {ω | i ∈ K ω} := by
        ext ω; simp [hiB]
      rw [this]
      exact hKm i
    · have : {ω | i ∈ K ω ↔ i ∈ B} = {ω | i ∈ K ω}ᶜ := by
        ext ω; simp [hiB]
      rw [this]
      exact (hKm i).compl
  have h_union : ⋃ B ∈ s.powerset, A B = G := by
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset fun B hB => ?_
      dsimp [A]
      exact Set.inter_subset_left
    · intro x hxG
      classical
        let B := s.filter (λ i => i ∈ K x)
        have hB_sub : B ⊆ s := Finset.filter_subset (λ i => i ∈ K x) s
        have hB_mem : B ∈ s.powerset := by
          rw [Finset.mem_powerset]
          exact hB_sub
        have hx_mem : x ∈ A B := by
          dsimp [A]
          refine ⟨hxG, ?_⟩
          intro i hi
          simp [B, hi]
        exact Set.mem_biUnion hB_mem hx_mem
  calc
    ∑ B ∈ s.powerset, m (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B})
        = ∑ B ∈ s.powerset, m (A B) := rfl
    _ = m (⋃ B ∈ s.powerset, A B) := by
      rw [← measure_biUnion_finset h_disjoint h_meas]
    _ = m G := by rw [h_union]

theorem FrogModel.Stage.infinitePi_pattern_cyl {ι : Type*} {X : ι → Type*} [DecidableEq ι]
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (K : (∀ i, X i) → Set ι) (hK : FrogModel.Stage.IsStoppingSet K)
    (hKm : ∀ i, MeasurableSet {ω : ∀ i, X i | i ∈ K ω}) (G : Set (∀ i, X i))
    (hG : FrogModel.Stage.IsDetermined K G) (hGm : MeasurableSet G) (s B : Finset ι)
    (t : ∀ i, Set (X i)) (ht : ∀ i, MeasurableSet (t i)) :
    Measure.infinitePi μ (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t) =
      Measure.infinitePi μ (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B}) * ∏ i ∈ s \ B, μ i (t i) := by
  set E := G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} with hE_def
  have hE : MeasurableSet E := by
    have h_pattern : MeasurableSet {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} := by
      have h_eq : {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} = ⋂ i ∈ s, {ω | i ∈ K ω ↔ i ∈ B} := by
        ext ω; simp
      rw [h_eq]
      have h_countable : (s : Set ι).Countable := s.finite_toSet.countable
      refine MeasurableSet.biInter h_countable (fun i hi => ?_)
      by_cases hiB : i ∈ B
      · have h_eq_i : {ω | i ∈ K ω ↔ i ∈ B} = {ω | i ∈ K ω} := by
          ext ω; simp [hiB]
        rw [h_eq_i]
        exact hKm i
      · have h_eq_i : {ω | i ∈ K ω ↔ i ∈ B} = {ω | i ∉ K ω} := by
          ext ω; simp [hiB]
        rw [h_eq_i]
        exact (hKm i).compl
    exact hGm.inter h_pattern
  have hins : ∀ ω ω' : ∀ i, X i, (∀ i ∉ s \ B, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E) := by
    intro ω ω' h_agree
    have h_symm : ω ∈ E → ω' ∈ E := by
      intro hωE
      rcases hωE with ⟨hωG, hω_pattern⟩
      have hKω_eq : K ω' = K ω := by
        apply hK ω ω'
        intro i hiKω
        have hi_not_sdiffB : i ∉ s \ B := by
          intro hi_sdiffB
          have hi_s : i ∈ s := (Finset.mem_sdiff.1 hi_sdiffB).1
          have hi_not_B : i ∉ B := (Finset.mem_sdiff.1 hi_sdiffB).2
          have hi_B : i ∈ B := (hω_pattern i hi_s).mp hiKω
          exact hi_not_B hi_B
        exact h_agree i hi_not_sdiffB
      have hω'G : ω' ∈ G := ((hG ω ω') (by
        intro i hiKω
        have hi_not_sdiffB : i ∉ s \ B := by
          intro hi_sdiffB
          have hi_s : i ∈ s := (Finset.mem_sdiff.1 hi_sdiffB).1
          have hi_not_B : i ∉ B := (Finset.mem_sdiff.1 hi_sdiffB).2
          have hi_B : i ∈ B := (hω_pattern i hi_s).mp hiKω
          exact hi_not_B hi_B
        exact h_agree i hi_not_sdiffB
      )).mp hωG
      have hω'_pattern : ∀ i ∈ s, i ∈ K ω' ↔ i ∈ B := by
        intro i hi_s
        rw [hKω_eq]
        exact hω_pattern i hi_s
      exact ⟨hω'G, hω'_pattern⟩
    have h_symm' : ω' ∈ E → ω ∈ E := by
      intro hω'E
      rcases hω'E with ⟨hω'G, hω'_pattern⟩
      have hKω_eq : K ω = K ω' := by
        apply hK ω' ω
        intro i hiKω'
        have hi_not_sdiffB : i ∉ s \ B := by
          intro hi_sdiffB
          have hi_s : i ∈ s := (Finset.mem_sdiff.1 hi_sdiffB).1
          have hi_not_B : i ∉ B := (Finset.mem_sdiff.1 hi_sdiffB).2
          have hi_B : i ∈ B := (hω'_pattern i hi_s).mp hiKω'
          exact hi_not_B hi_B
        exact (h_agree i hi_not_sdiffB).symm
      have hωG : ω ∈ G := ((hG ω' ω) (by
        intro i hiKω'
        have hi_not_sdiffB : i ∉ s \ B := by
          intro hi_sdiffB
          have hi_s : i ∈ s := (Finset.mem_sdiff.1 hi_sdiffB).1
          have hi_not_B : i ∉ B := (Finset.mem_sdiff.1 hi_sdiffB).2
          have hi_B : i ∈ B := (hω'_pattern i hi_s).mp hiKω'
          exact hi_not_B hi_B
        exact (h_agree i hi_not_sdiffB).symm
      )).mp hω'G
      have hω_pattern : ∀ i ∈ s, i ∈ K ω ↔ i ∈ B := by
        intro i hi_s
        rw [hKω_eq]
        exact hω'_pattern i hi_s
      exact ⟨hωG, hω_pattern⟩
    exact ⟨h_symm, h_symm'⟩
  have h_pi_eq : Set.pi (↑(s \ B) : Set ι) t = {ω | ∀ i ∈ s \ B, ω i ∈ t i} := by
    ext ω; simp
  calc
    Measure.infinitePi μ (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t)
        = Measure.infinitePi μ (E ∩ Set.pi (↑(s \ B)) t) := by rw [hE_def]
    _ = Measure.infinitePi μ (E ∩ {ω | ∀ i ∈ s \ B, ω i ∈ t i}) := by rw [h_pi_eq]
    _ = Measure.infinitePi μ E * ∏ i ∈ s \ B, μ i (t i) := by
      rw [FrogModel.Stage.infinitePi_inter_cyl μ (s \ B) E hE hins t ht]
    _ = Measure.infinitePi μ (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B}) * ∏ i ∈ s \ B, μ i (t i) := by
      rw [hE_def]

theorem FrogModel.Stage.refresh_box {ι : Type*} {X : ι → Type*} [DecidableEq ι]
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (K : (∀ i, X i) → Set ι) (hK : FrogModel.Stage.IsStoppingSet K)
    (hKm : ∀ i, MeasurableSet {ω : ∀ i, X i | i ∈ K ω}) (G : Set (∀ i, X i))
    (hG : FrogModel.Stage.IsDetermined K G) (hGm : MeasurableSet G) (s : Finset ι)
    (t : ∀ i, Set (X i)) (ht : ∀ i, MeasurableSet (t i)) :
    ((Measure.infinitePi μ).prod (Measure.infinitePi μ))
        ((G ×ˢ Set.univ) ∩
          (fun p : (∀ i, X i) × (∀ i, X i) => FrogModel.Stage.refresh K p.1 p.2) ⁻¹'
            Set.pi (↑s) t) =
      Measure.infinitePi μ G * ∏ i ∈ s, μ i (t i) := by
  have h_eq_set : (G ×ˢ Set.univ) ∩
      (fun p : (∀ i, X i) × (∀ i, X i) => FrogModel.Stage.refresh K p.1 p.2) ⁻¹'
        Set.pi (↑s) t =
      ⋃ B ∈ s.powerset,
        (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t) ×ˢ Set.pi (↑B) t :=
    FrogModel.Stage.refresh_preimage_pi K G s t
  rw [h_eq_set]
  have h_disjoint : (↑(s.powerset : Finset (Finset ι)) : Set (Finset ι)).PairwiseDisjoint
      fun (B : Finset ι) =>
        (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t) ×ˢ Set.pi (↑B) t :=
    FrogModel.Stage.pairwiseDisjoint_pattern K G s t
  have h_meas : ∀ B ∈ s.powerset,
      MeasurableSet ((G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t) ×ˢ Set.pi (↑B) t) := by
    intro B hB
    refine MeasurableSet.prod ?_ ?_
    · refine (hGm.inter ?_).inter ?_
      · have h_meas_iff : MeasurableSet {ω : ∀ i, X i | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} := by
          have h_eq : {ω : ∀ i, X i | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} =
              ⋂ i ∈ s, {ω | i ∈ K ω ↔ i ∈ B} := by
            ext ω; simp
          rw [h_eq]
          refine Finset.measurableSet_biInter s fun i hi => ?_
          have h1 : MeasurableSet {ω | i ∈ K ω → i ∈ B} := by
            by_cases h : i ∈ B
            · have : {ω | i ∈ K ω → i ∈ B} = Set.univ := by ext ω; simp [h]
              rw [this]; exact MeasurableSet.univ
            · have : {ω | i ∈ K ω → i ∈ B} = {ω | i ∈ K ω}ᶜ := by ext ω; simp [h]
              rw [this]; exact (hKm i).compl
          have h2 : MeasurableSet {ω | i ∈ B → i ∈ K ω} := by
            by_cases h : i ∈ B
            · have : {ω | i ∈ B → i ∈ K ω} = {ω | i ∈ K ω} := by ext ω; simp [h]
              rw [this]; exact hKm i
            · have : {ω | i ∈ B → i ∈ K ω} = Set.univ := by ext ω; simp [h]
              rw [this]; exact MeasurableSet.univ
          have h_inter : MeasurableSet ({ω | i ∈ K ω → i ∈ B} ∩ {ω | i ∈ B → i ∈ K ω}) :=
            h1.inter h2
          have h_set_eq : {ω | i ∈ K ω ↔ i ∈ B} = {ω | i ∈ K ω → i ∈ B} ∩ {ω | i ∈ B → i ∈ K ω} := by
            ext ω; constructor
            · intro h; exact ⟨fun h' => (h.mp h'), fun h' => (h.mpr h')⟩
            · intro ⟨h1, h2⟩; exact ⟨fun h => h1 h, fun h => h2 h⟩
          rw [h_set_eq]
          exact h_inter
        exact h_meas_iff
      · have h_count : Countable (↑(s \ B) : Set ι) := Finset.countable_toSet _
        refine MeasurableSet.pi h_count fun i hi => ?_
        exact ht i
    · have h_count : Countable (↑B : Set ι) := Finset.countable_toSet _
      refine MeasurableSet.pi h_count fun i hi => ?_
      exact ht i
  rw [MeasureTheory.measure_biUnion_finset h_disjoint h_meas]
  simp_rw [Measure.prod_prod]
  have h_pi_B : ∀ B : Finset ι, Measure.infinitePi μ (Set.pi (↑B : Set ι) t) = ∏ i ∈ B, μ i (t i) := by
    intro B
    rw [Measure.infinitePi_pi (μ := μ) (s := B) (t := t) (mt := fun i hi => ht i)]
  simp_rw [h_pi_B]
  have h_pattern : ∀ B : Finset ι,
      Measure.infinitePi μ (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B} ∩ Set.pi (↑(s \ B)) t) =
      Measure.infinitePi μ (G ∩ {ω | ∀ i ∈ s, i ∈ K ω ↔ i ∈ B}) * ∏ i ∈ s \ B, μ i (t i) := by
    intro B
    exact FrogModel.Stage.infinitePi_pattern_cyl μ K hK hKm G hG hGm s B t ht
  simp_rw [h_pattern]
  simp_rw [mul_assoc]
  have h_prod_combine : ∀ B ∈ s.powerset,
      (∏ i ∈ s \ B, μ i (t i)) * ∏ i ∈ B, μ i (t i) = ∏ i ∈ s, μ i (t i) := by
    intro B hB
    have h_sub : B ⊆ s := Finset.mem_powerset.mp hB
    rw [← Finset.prod_sdiff h_sub]
  rw [Finset.sum_congr rfl fun B hB => by rw [h_prod_combine B hB]]
  rw [← Finset.sum_mul]
  congr 1
  exact FrogModel.Stage.sum_pattern (Measure.infinitePi μ) K hKm G hGm s

theorem FrogModel.Stage.map_refresh {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (K : (∀ i, X i) → Set ι) (hK : FrogModel.Stage.IsStoppingSet K)
    (hKm : ∀ i, MeasurableSet {ω : ∀ i, X i | i ∈ K ω}) (G : Set (∀ i, X i))
    (hG : FrogModel.Stage.IsDetermined K G) (hGm : MeasurableSet G) :
    (((Measure.infinitePi μ).prod (Measure.infinitePi μ)).restrict (G ×ˢ Set.univ)).map
        (fun p : (∀ i, X i) × (∀ i, X i) => FrogModel.Stage.refresh K p.1 p.2) =
      Measure.infinitePi μ G • Measure.infinitePi μ := by
  classical
  let P := Measure.infinitePi μ
  let ρ : (∀ i, X i) × (∀ i, X i) → ∀ i, X i :=
    fun p => FrogModel.Stage.refresh K p.1 p.2
  have hρ_meas : Measurable ρ := by
    simpa [ρ] using FrogModel.Stage.measurable_refresh K hKm
  have hP_univ : P Set.univ = 1 := by
    have : IsProbabilityMeasure P := inferInstance
    exact measure_univ
  have h_box : ∀ (s : Finset ι) (t : ∀ i, Set (X i)), (∀ i, MeasurableSet (t i)) →
      ((P.prod P).restrict (G ×ˢ Set.univ)).map ρ (Set.pi (s : Set ι) t) =
      P G * ∏ i ∈ s, μ i (t i) := by
    intro s t ht
    have h_meas_box : MeasurableSet (Set.pi (s : Set ι) t) :=
      MeasurableSet.pi (Finset.countable_toSet s) fun i hi => ht i
    have h_meas_preimage : MeasurableSet (ρ ⁻¹' (Set.pi (s : Set ι) t)) :=
      hρ_meas h_meas_box
    rw [Measure.map_apply hρ_meas h_meas_box]
    rw [Measure.restrict_apply h_meas_preimage]
    rw [Set.inter_comm]
    exact FrogModel.Stage.refresh_box μ K hK hKm G hG hGm s t ht
  by_cases hG0 : P G = 0
  · -- case P G = 0: both sides are zero
    have hL_univ_zero : ((P.prod P).restrict (G ×ˢ Set.univ)).map ρ Set.univ = 0 := by
      rw [Measure.map_apply hρ_meas MeasurableSet.univ]
      rw [Measure.restrict_apply (by
        -- ρ ⁻¹' Set.univ = Set.univ, which is measurable
        have : ρ ⁻¹' Set.univ = Set.univ := by simp
        rw [this]
        exact MeasurableSet.univ)]
      simp [hG0, hP_univ, Measure.prod_prod]
    have hL_zero : ((P.prod P).restrict (G ×ˢ Set.univ)).map ρ = 0 :=
      Measure.measure_univ_eq_zero.mp hL_univ_zero
    rw [hL_zero, hG0]
    simp
  · -- case P G ≠ 0
    have hG_ne_top : P G ≠ ⊤ := measure_ne_top P G
    set L := ((P.prod P).restrict (G ×ˢ Set.univ)).map ρ with hL_def
    have hL_eq : (P G)⁻¹ • L = P := by
      refine Measure.eq_infinitePi (μ := μ) (ν := (P G)⁻¹ • L) ?_
      intro s t ht
      have hL_box : L (Set.pi (s : Set ι) t) = P G * ∏ i ∈ s, μ i (t i) := h_box s t ht
      calc
        ((P G)⁻¹ • L) (Set.pi (s : Set ι) t) = (P G)⁻¹ * L (Set.pi (s : Set ι) t) := by
          rw [Measure.smul_apply, smul_eq_mul]
        _ = (P G)⁻¹ * (P G * ∏ i ∈ s, μ i (t i)) := by rw [hL_box]
        _ = ((P G)⁻¹ * P G) * ∏ i ∈ s, μ i (t i) := by ring
        _ = 1 * ∏ i ∈ s, μ i (t i) := by
          rw [ENNReal.inv_mul_cancel hG0 hG_ne_top]
        _ = ∏ i ∈ s, μ i (t i) := by simp
    calc
      L = (P G) • ((P G)⁻¹ • L) := by
        rw [smul_smul, ENNReal.mul_inv_cancel hG0 hG_ne_top, one_smul]
      _ = (P G) • P := by rw [hL_eq]

theorem FrogModel.Stage.lintegral_refresh {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (K : (∀ i, X i) → Set ι) (hK : FrogModel.Stage.IsStoppingSet K)
    (hKm : ∀ i, MeasurableSet {ω : ∀ i, X i | i ∈ K ω}) (G : Set (∀ i, X i))
    (hG : FrogModel.Stage.IsDetermined K G) (hGm : MeasurableSet G)
    (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, G.indicator (fun ω => ∫⁻ ω', f (FrogModel.Stage.refresh K ω ω')
        ∂Measure.infinitePi μ) ω ∂Measure.infinitePi μ =
      Measure.infinitePi μ G * ∫⁻ ω, f ω ∂Measure.infinitePi μ := by
  set P := Measure.infinitePi μ
  set ρ := fun p : (∀ i, X i) × (∀ i, X i) => FrogModel.Stage.refresh K p.1 p.2
  have hmeas : Measurable ρ := FrogModel.Stage.measurable_refresh K hKm
  have hmeas_fρ : AEMeasurable (fun (p : (∀ i, X i) × (∀ i, X i)) => f (ρ p)) ((P.restrict G).prod P) := by
    refine (hf.comp hmeas).aemeasurable
  calc
    ∫⁻ ω, G.indicator (fun ω => ∫⁻ ω', f (FrogModel.Stage.refresh K ω ω') ∂P) ω ∂P
        = ∫⁻ ω in G, (∫⁻ ω', f (FrogModel.Stage.refresh K ω ω') ∂P) ∂P := by
      rw [lintegral_indicator hGm]
    _ = ∫⁻ (p : (∀ i, X i) × (∀ i, X i)), f (ρ p) ∂((P.restrict G).prod P) := by
      rw [lintegral_prod _ hmeas_fρ]
    _ = ∫⁻ (p : (∀ i, X i) × (∀ i, X i)), f (ρ p) ∂((P.prod P).restrict (G ×ˢ Set.univ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = ∫⁻ ω, f ω ∂(((P.prod P).restrict (G ×ˢ Set.univ)).map ρ) := by
      rw [lintegral_map hf hmeas]
    _ = ∫⁻ ω, f ω ∂(P G • P) := by
      rw [FrogModel.Stage.map_refresh μ K hK hKm G hG hGm]
    _ = P G * ∫⁻ ω, f ω ∂P := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ = Measure.infinitePi μ G * ∫⁻ ω, f ω ∂Measure.infinitePi μ := rfl

theorem FrogModel.Stage.isStoppingSet_stages {ι P : Type*} (arc : ι → P → ι → Prop)
    (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι) (m : ℕ) :
    FrogModel.Stage.IsStoppingSet (X := fun _ : ι => P)
      (fun ω => FrogModel.Stage.stages arc closed succ σ₀ ω m) := by
  intro ω ω' h
  have h' : ∀ i ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, ω i = ω' i := by
    simpa using h
  apply FrogModel.Stage.stages_eq_of_agree arc closed succ σ₀ ω ω'
    ((FrogModel.Stage.stages arc closed succ σ₀ ω m)ᶜ) ?_ m ?_
  · intro σ hσ
    have hmem : σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m :=
      Set.notMem_compl_iff.mp hσ
    exact h' σ hmem
  · exact (Set.disjoint_compl_right_iff_subset.mpr (Set.Subset.refl _))

theorem FrogModel.infinitePi_map_comp_injective {ι α Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (e : α → ι) (he : Function.Injective e) :
    (Measure.infinitePi fun _ : ι => μ).map (fun ω a => ω (e a)) =
      Measure.infinitePi fun _ : α => μ := by
  exact MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj he

theorem FrogModel.infinitePi_map_pair_injective {ι α Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (e : α → ι) (he : Function.Injective e) (i₀ : ι)
    (hi₀ : ∀ a, e a ≠ i₀) :
    (Measure.infinitePi fun _ : ι => μ).map (fun ω => (ω i₀, fun a => ω (e a))) =
      μ.prod (Measure.infinitePi fun _ : α => μ) := by
  let PI := Measure.infinitePi fun _ : ι => μ
  let PA := Measure.infinitePi fun _ : α => μ
  have h_map_meas : Measurable (fun (ω : ι → Y) => (ω i₀, fun a => ω (e a))) := by
    fun_prop
  -- Use ext_prod to reduce to rectangle equality
  refine Measure.ext_prod (μ := PI.map (fun ω => (ω i₀, fun a => ω (e a))))
    (ν := μ.prod PA) ?_
  intro s t hs ht
  rw [Measure.map_apply h_map_meas (hs.prod ht)]
  -- Goal: PI ((fun ω => (ω i₀, fun a => ω (e a))) ⁻¹' (s ×ˢ t)) = μ s * PA t
  have h_preimage : (fun (ω : ι → Y) => (ω i₀, fun a => ω (e a))) ⁻¹' (s ×ˢ t) =
      {ω | ω i₀ ∈ s} ∩ {ω | (fun a => ω (e a)) ∈ t} := by
    ext ω; simp
  rw [h_preimage]
  -- Goal: PI ({ω | ω i₀ ∈ s} ∩ {ω | (fun a => ω (e a)) ∈ t}) = μ s * PA t
  -- Let A = {ω | ω i₀ ∈ s}, B = {ω | ω ∘ e ∈ t}
  -- We have PI A = μ s and PI B = PA t
  -- Need to show PI (A ∩ B) = PI A * PI B, i.e., A and B are independent
  have hA : PI {ω | ω i₀ ∈ s} = μ s := by
    have : {ω : ι → Y | ω i₀ ∈ s} = Set.pi ({i₀} : Finset ι) (fun _ => s) := by
      ext ω; simp
    rw [this]
    rw [MeasureTheory.Measure.infinitePi_pi (fun _ => μ) (fun i hi => hs)]
    simp
  have hB : PI {ω | (fun a => ω (e a)) ∈ t} = PA t := by
    have h_meas : Measurable (fun (ω : ι → Y) => fun a => ω (e a)) := by fun_prop
    calc
      PI {ω | (fun a => ω (e a)) ∈ t} = PI ((fun (ω : ι → Y) => fun a => ω (e a)) ⁻¹' t) := by rfl
      _ = (PI.map (fun (ω : ι → Y) => fun a => ω (e a))) t := by
        rw [← Measure.map_apply (μ := PI) h_meas ht]
      _ = PA t := by rw [FrogModel.infinitePi_map_comp_injective μ e he]
  -- Now we need PI (A ∩ B) = PI A * PI B
  -- Use independence of the coordinate i₀ from the coordinates in Set.range e
  have h_indep_eval : iIndepFun (fun (i : ι) (ω : ι → Y) => ω i) PI :=
    iIndepFun_infinitePi (X := fun x ω => ω) (fun i => by fun_prop)
  have h_indep : iIndep (fun (i : ι) => MeasurableSpace.comap (fun (ω : ι → Y) => ω i)
      (by infer_instance : MeasurableSpace Y)) PI :=
    (iIndepFun_iff_iIndep (fun _ => inferInstance) _ _).mp h_indep_eval
  have h_le : ∀ i, MeasurableSpace.comap (fun (ω : ι → Y) => ω i)
      (by infer_instance : MeasurableSpace Y) ≤
      inferInstanceAs (MeasurableSpace (ι → Y)) := by
    intro i
    exact Measurable.comap_le (measurable_pi_apply i)
  have h_disjoint : Disjoint ({i₀} : Set ι) (Set.range e) :=
    Set.disjoint_left.mpr (by
      intro x hx₁ hx₂
      have hx₁' : x = i₀ := Set.mem_singleton_iff.mp hx₁
      rcases hx₂ with ⟨a, ha⟩
      exact hi₀ a (ha.trans hx₁'))
  have h_indep_pair : Indep
      (⨆ i ∈ ({i₀} : Set ι), MeasurableSpace.comap (fun (ω : ι → Y) => ω i)
        (by infer_instance : MeasurableSpace Y))
      (⨆ i ∈ Set.range e, MeasurableSpace.comap (fun (ω : ι → Y) => ω i)
        (by infer_instance : MeasurableSpace Y)) PI :=
    indep_iSup_of_disjoint h_le h_indep h_disjoint
  have h_sup_singleton : (⨆ i ∈ ({i₀} : Set ι),
      MeasurableSpace.comap (fun (ω : ι → Y) => ω i) (inferInstance : MeasurableSpace Y)) =
      MeasurableSpace.comap (fun (ω : ι → Y) => ω i₀) (inferInstance : MeasurableSpace Y) := by
    simp
  have h_sup_range_le : MeasurableSpace.comap (fun (ω : ι → Y) => ω ∘ e)
      (inferInstance : MeasurableSpace (α → Y)) ≤
      ⨆ i ∈ Set.range e, MeasurableSpace.comap (fun (ω : ι → Y) => ω i)
        (inferInstance : MeasurableSpace Y) := by
    -- The product sigma-algebra is defined as ⨆ a, comap (eval a) _
    have h_prod_eq : (inferInstance : MeasurableSpace (α → Y)) =
        ⨆ a, MeasurableSpace.comap (fun (x : α → Y) => x a)
          (inferInstance : MeasurableSpace Y) := by
      rfl
    rw [h_prod_eq]
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le (fun a => ?_)
    rw [MeasurableSpace.comap_comp]
    -- Now we need to show comap (fun ω => ω (e a)) ≤ ⨆ i ∈ Set.range e, comap (ω i)
    -- This holds because e a ∈ Set.range e
    have h_mem : e a ∈ Set.range e := ⟨a, rfl⟩
    exact le_iSup₂_of_le (e a) h_mem (by rfl)
  rw [h_sup_singleton] at h_indep_pair
  have h_indep_pair' : Indep (MeasurableSpace.comap (fun (ω : ι → Y) => ω i₀)
      (inferInstance : MeasurableSpace Y))
      (MeasurableSpace.comap (fun (ω : ι → Y) => ω ∘ e)
      (inferInstance : MeasurableSpace (α → Y))) PI :=
    ProbabilityTheory.indep_of_indep_of_le_right h_indep_pair h_sup_range_le
  -- Now use Indep_iff to get the measure equality directly
  rw [Indep_iff] at h_indep_pair'
  have hA_comap : MeasurableSet[MeasurableSpace.comap (fun (ω : ι → Y) => ω i₀)
      (inferInstance : MeasurableSpace Y)] {ω : ι → Y | ω i₀ ∈ s} := by
    refine ⟨s, hs, ?_⟩
    rfl
  have hB_comap : MeasurableSet[MeasurableSpace.comap (fun (ω : ι → Y) => ω ∘ e)
      (inferInstance : MeasurableSpace (α → Y))] {ω : ι → Y | (fun a => ω (e a)) ∈ t} := by
    refine ⟨t, ht, ?_⟩
    rfl
  rw [h_indep_pair' _ _ hA_comap hB_comap, hA, hB]
  -- Goal: μ s * PA t = (μ.prod PA) (s ×ˢ t)
  rw [Measure.prod_prod]
