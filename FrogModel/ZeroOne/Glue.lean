module

public import FrogModel.ZeroOne.Walk
public import FrogModel.Pieces.Glue

@[expose] public section

/-!
# The strong Markov property at the exit times, Borel-Cantelli over infinitely many frogs

The step of the proof of Theorem 9.3 of the paper in which infinitely many frozen frogs of the copy
of `T*` run straight up to the root after their first visits to its leaf.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.ZeroOne

/-- Strong Markov property of an i.i.d. sequence at a stopping time `e`: the first sequence up
to `e`, then an independent i.i.d. sequence, is an i.i.d. sequence. -/
theorem FrogModel.ZeroOne.map_glueAt {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (ν : Measure α) [IsProbabilityMeasure ν] (e : (ℕ → α) → ℕ∞)
    (he : ∀ (a a' : ℕ → α) (k : ℕ), e a = k → (∀ i < k, a i = a' i) → e a' = k)
    (hm : Measurable e) :
    ((Measure.infinitePi fun _ : ℕ => ν).prod (Measure.infinitePi fun _ : ℕ => ν)).map
        (fun p => glueAt (e p.1) p.1 p.2) = Measure.infinitePi fun _ : ℕ => ν := by
  set P := Measure.infinitePi fun _ : ℕ => ν with hP
  have hG : Measurable fun p : (ℕ → α) × (ℕ → α) => glueAt (e p.1) p.1 p.2 := by
    refine measurable_pi_iff.mpr fun t => ?_
    have hF : Measurable fun q : ((ℕ → α) × (ℕ → α)) × ℕ∞ => glueAt q.2 q.1.1 q.1.2 t := by
      refine measurable_from_prod_countable_left fun k => ?_
      by_cases h : (t : ℕ∞) < k
      · simp only [glueAt, h, ite_true]
        exact (measurable_pi_apply t).comp measurable_fst
      · simp only [glueAt, h, ite_false]
        exact (measurable_pi_apply _).comp measurable_snd
    exact hF.comp (measurable_id.prodMk (hm.comp measurable_fst))
  refine FrogModel.ext_of_prefix _ _ fun N c => ?_
  rw [Measure.map_apply hG (FrogModel.measurableSet_prefix N c), FrogModel.infinitePi_prefix]
  by_cases hc : ∃ k < N, e c = k
  · obtain ⟨k, hkN, hk⟩ := hc
    obtain ⟨m, rfl⟩ : ∃ m, N = k + m := ⟨N - k, by omega⟩
    have hpre : (fun p : (ℕ → α) × (ℕ → α) => glueAt (e p.1) p.1 p.2) ⁻¹'
        {x | ∀ i < k + m, x i = c i} =
          {a : ℕ → α | ∀ i < k, a i = c i} ×ˢ {b : ℕ → α | ∀ j < m, b j = c (k + j)} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod]
      constructor
      · intro h
        have hek : e p.1 = k := by
          by_cases hlt : e p.1 < k
          · exfalso
            obtain ⟨m', hm'⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
            have hmk : m' < k := by
              rw [← hm'] at hlt
              exact_mod_cast hlt
            have hagree : ∀ i < m', p.1 i = c i := fun i hi => by
              have := h i (by omega)
              simp only [glueAt, ← hm'] at this
              rwa [ite_eq_left (by exact_mod_cast hi)] at this
            have h2 := he p.1 c m' hm'.symm hagree
            rw [hk] at h2
            have : k = m' := by exact_mod_cast h2
            omega
          · push Not at hlt
            refine he c p.1 k hk fun i hi => ?_
            have := h i (by omega)
            simp only [glueAt] at this
            rw [ite_eq_left (lt_of_lt_of_le (by exact_mod_cast hi) hlt)] at this
            exact this.symm
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · have := h i (by omega)
          simp only [glueAt, hek] at this
          rwa [ite_eq_left (by exact_mod_cast hi)] at this
        · have := h (k + j) (by omega)
          simp only [glueAt, hek, ENat.toNat_natCast] at this
          rw [ite_eq_right (by norm_cast; omega), Nat.add_sub_cancel_left] at this
          exact this
      · rintro ⟨h1, h2⟩ i hi
        have hek : e p.1 = k := he c p.1 k hk fun i hi => (h1 i hi).symm
        simp only [glueAt, hek, ENat.toNat_natCast]
        by_cases hik : i < k
        · rw [ite_eq_left (by exact_mod_cast hik)]
          exact h1 i hik
        · rw [ite_eq_right (by norm_cast)]
          rw [h2 (i - k) (by omega)]
          congr 1
          omega
    rw [hpre, Measure.prod_prod, FrogModel.infinitePi_prefix]
    have hshift : P {b : ℕ → α | ∀ j < m, b j = c (k + j)} = ∏ j ∈ Finset.range m, ν {c (k + j)} :=
      FrogModel.infinitePi_prefix ν m (fun j => c (k + j))
    rw [hshift, Finset.prod_range_add]
  · push Not at hc
    have hnot : ∀ (a : ℕ → α), (∀ i < N, a i = c i) → ∀ i < N, (i : ℕ∞) < e a := by
      intro a ha i hi
      by_contra hle
      push Not at hle
      obtain ⟨m, hm'⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top i) hle)
      have hmi : m ≤ i := by
        rw [← hm'] at hle
        exact_mod_cast hle
      exact hc m (by omega) (he a c m hm'.symm fun j hj => ha j (by omega))
    have hpre : (fun p : (ℕ → α) × (ℕ → α) => glueAt (e p.1) p.1 p.2) ⁻¹'
        {x | ∀ i < N, x i = c i} = {a : ℕ → α | ∀ i < N, a i = c i} ×ˢ Set.univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
      constructor
      · intro h
        have hge : ∀ m : ℕ, e p.1 = m → N ≤ m := by
          intro m hm'
          by_contra hlt
          push Not at hlt
          have hagree : ∀ i < m, p.1 i = c i := fun i hi => by
            have := h i (by omega)
            simp only [glueAt, hm'] at this
            rwa [ite_eq_left (by exact_mod_cast hi)] at this
          exact hc m hlt (he p.1 c m hm' hagree)
        intro i hi
        have hlt : (i : ℕ∞) < e p.1 := by
          by_contra hle
          push Not at hle
          obtain ⟨m, hm'⟩ :=
            ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top i) hle)
          have h3 := hge m hm'.symm
          rw [← hm'] at hle
          have : m ≤ i := by exact_mod_cast hle
          omega
        have := h i hi
        simp only [glueAt] at this
        rwa [ite_eq_left hlt] at this
      · intro h1 i hi
        have hlt := hnot p.1 h1 i hi
        simp only [glueAt, hlt, ite_true]
        exact h1 i hi
    rw [hpre, Measure.prod_prod, measure_univ, mul_one, FrogModel.infinitePi_prefix]

/-- The glued sequence is measurable when the gluing time is. -/
theorem FrogModel.ZeroOne.measurable_glueAt {α : Type*} [MeasurableSpace α]
    (e : (ℕ → α) → ℕ∞) (hm : Measurable e) :
    Measurable fun p : (ℕ → α) × (ℕ → α) => glueAt (e p.1) p.1 p.2 := by
  refine measurable_pi_iff.mpr fun t => ?_
  have hF : Measurable fun q : ((ℕ → α) × (ℕ → α)) × ℕ∞ => glueAt q.2 q.1.1 q.1.2 t := by
    refine measurable_from_prod_countable_left fun k => ?_
    by_cases h : (t : ℕ∞) < k
    · simp only [glueAt, h, ite_true]
      exact (measurable_pi_apply t).comp measurable_fst
    · simp only [glueAt, h, ite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  exact hF.comp (measurable_id.prodMk (hm.comp measurable_fst))

/-- Gluing after the exit time does not change the walk on `T*`. -/
theorem FrogModel.ZeroOne.walkStar_glueAt {d : ℕ} (v : Vertex d) (a b : ℕ → Step d) (n : ℕ) :
    walkStar (some v) (glueAt (exitTime v a) a b) n = walkStar (some v) a n := by
  have habs : ∀ (x : ℕ → Step d) (k j : ℕ), walkStar (some v) x k = none →
      walkStar (some v) x (k + j) = none := by
    intro x k j h
    induction j with
    | zero => simpa using h
    | succ j ih => rw [← Nat.add_assoc, walkStar, ih]; rfl
  by_cases hE : exitTime v a = ⊤
  · have : glueAt (exitTime v a) a b = a := by
      funext t
      simp [glueAt, hE]
    rw [this]
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hE
    have hpre : ∀ m ≤ k, walkStar (some v) (glueAt (exitTime v a) a b) m =
        walkStar (some v) a m := fun m hm =>
      FrogModel.ZeroOne.walkStar_prefix (some v) _ _ m fun i hi => by
        have hi' : (i : ℕ∞) < exitTime v a := by
          rw [← hk]; exact_mod_cast lt_of_lt_of_le hi hm
        simp [glueAt, hi']
    by_cases hn : n ≤ k
    · exact hpre n hn
    · have hka : walkStar (some v) a k = none :=
        (FrogModel.ZeroOne.exitTime_spec v a k hk.symm).1
      have hkg : walkStar (some v) (glueAt (exitTime v a) a b) k = none :=
        (hpre k le_rfl).trans hka
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.1 hn))
      rw [habs _ k j hkg, habs _ k j hka]

/-- The frozen frogs of the glued sample are those of the first sample. -/
theorem FrogModel.ZeroOne.frozen_glueExit {d : ℕ} (p : Sample d × Sample d) (v : Vertex d) :
    frozen (glueExit p) v ↔ frozen p.1 v := by
  unfold frozen
  have h_walk : ∀ (a : Vertex d) (n : ℕ), walkStar (some a) (glueAt (exitTime a (p.1 a)) (p.1 a) (p.2 a)) n = walkStar (some a) (p.1 a) n := by
    intro a n
    exact FrogModel.ZeroOne.walkStar_glueAt a (p.1 a) (p.2 a) n
  have h_starArc : starArc (glueExit p) = starArc p.1 := by
    ext a b
    unfold starArc glueExit
    simp [h_walk]
  have h_second : (∃ n, walkStar (some v) ((glueExit p) v) n = none) ↔ (∃ n, walkStar (some v) (p.1 v) n = none) := by
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [glueExit, h_walk v n] using hn
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [glueExit, h_walk v n] using hn
  rw [h_starArc, h_second]

theorem FrogModel.ZeroOne.exitTime_glueExit {d : ℕ} (p : Sample d × Sample d) (v : Vertex d) :
    exitTime v (glueExit p v) = exitTime v (p.1 v) := by
  unfold exitTime glueExit
  simp [FrogModel.ZeroOne.walkStar_glueAt]

/-- After the exit time, frog `v` of the glued sample follows `p.2 v`. -/
theorem FrogModel.ZeroOne.glueExit_after {d : ℕ} (p : Sample d × Sample d) (v : Vertex d)
    (k j : ℕ) (h : exitTime v (p.1 v) = k) :
    glueExit p v (k + j) = p.2 v j := by
  unfold glueExit glueAt
  rw [h]
  simp

/-- The glued sample has the law of the frog model. -/
theorem FrogModel.ZeroOne.map_glueExit {d : ℕ} [NeZero d] :
    ((frogMeasure d).prod (frogMeasure d)).map glueExit = frogMeasure d := by
  set P := Measure.infinitePi fun _ : ℕ => stepLaw d with hP
  have hF : frogMeasure d = Measure.infinitePi fun _ : Vertex d => P := rfl
  have hgm : ∀ v : Vertex d,
      Measurable fun p : (ℕ → Step d) × (ℕ → Step d) => glueAt (exitTime v p.1) p.1 p.2 :=
    fun v => measurable_glueAt _ (measurable_exitTime v)
  have hgmap : ∀ v : Vertex d,
      (P.prod P).map (fun p : (ℕ → Step d) × (ℕ → Step d) => glueAt (exitTime v p.1) p.1 p.2) =
        P := fun v =>
    map_glueAt (stepLaw d) (exitTime v) (fun a a' k h ha => exitTime_eq_of_prefix v a a' k h ha)
      (measurable_exitTime v)
  have hglue : Measurable (glueExit (d := d)) := by
    refine measurable_pi_iff.mpr fun v => ?_
    have h1 : Measurable fun q : Sample d × Sample d => q.1 v :=
      (measurable_pi_apply v).comp measurable_fst
    have h2 : Measurable fun q : Sample d × Sample d => q.2 v :=
      (measurable_pi_apply v).comp measurable_snd
    exact (hgm v).comp (h1.prodMk h2)
  rw [hF]
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hglue (MeasurableSet.pi s.countable_toSet fun v _ => ht v)]
  set ρ : Sample d × Sample d → (s → ℕ → Step d) × (s → ℕ → Step d) :=
    fun q => (s.restrict q.1, s.restrict q.2) with hρdef
  have hρm : Measurable ρ :=
    ((Finset.measurable_restrict s).comp measurable_fst).prodMk
      ((Finset.measurable_restrict s).comp measurable_snd)
  have hρ : ((Measure.infinitePi fun _ : Vertex d => P).prod
      (Measure.infinitePi fun _ : Vertex d => P)).map ρ =
        (Measure.pi fun _ : s => P).prod (Measure.pi fun _ : s => P) := by
    have h1 : (Measure.infinitePi fun _ : Vertex d => P).map s.restrict =
        Measure.pi fun _ : s => P := Measure.infinitePi_map_restrict (μ := fun _ => P)
    rw [← h1, Measure.map_prod_map _ _ (Finset.measurable_restrict s)
      (Finset.measurable_restrict s)]
    rfl
  set S : Set ((s → ℕ → Step d) × (s → ℕ → Step d)) :=
    {z | ∀ v : s, glueAt (exitTime v.1 (z.1 v)) (z.1 v) (z.2 v) ∈ t v} with hSdef
  have hSm : MeasurableSet S := by
    have : S = ⋂ v : s, (fun z : (s → ℕ → Step d) × (s → ℕ → Step d) =>
        glueAt (exitTime v.1 (z.1 v)) (z.1 v) (z.2 v)) ⁻¹' t v := by
      ext z
      simp [S]
    rw [this]
    refine MeasurableSet.iInter fun v => ?_
    have h1 : Measurable fun z : (s → ℕ → Step d) × (s → ℕ → Step d) => z.1 v :=
      (measurable_pi_apply v).comp measurable_fst
    have h2 : Measurable fun z : (s → ℕ → Step d) × (s → ℕ → Step d) => z.2 v :=
      (measurable_pi_apply v).comp measurable_snd
    have h3 : Measurable fun z : (s → ℕ → Step d) × (s → ℕ → Step d) =>
        glueAt (exitTime v.1 (z.1 v)) (z.1 v) (z.2 v) := (hgm v.1).comp (h1.prodMk h2)
    exact h3 (ht v)
  have hpre : glueExit ⁻¹' Set.pi ↑s t = ρ ⁻¹' S := by
    ext q
    simp [S, ρ, glueExit, Set.mem_pi]
  rw [hpre, ← Measure.map_apply hρm hSm, hρ]
  have hmp := measurePreserving_arrowProdEquivProdArrow (ℕ → Step d) (ℕ → Step d) s
    (fun _ => P) (fun _ => P)
  rw [← hmp.map_eq, Measure.map_apply (MeasurableEquiv.measurable _) hSm]
  have hS' : (MeasurableEquiv.arrowProdEquivProdArrow (ℕ → Step d) (ℕ → Step d) s) ⁻¹' S =
      Set.pi Set.univ (fun v : s =>
        (fun p : (ℕ → Step d) × (ℕ → Step d) => glueAt (exitTime v.1 p.1) p.1 p.2) ⁻¹' t v) := by
    ext z
    simp [S, Set.mem_pi, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  rw [hS', Measure.pi_pi, ← Finset.prod_coe_sort s]
  refine Fintype.prod_congr _ _ fun v => ?_
  rw [← Measure.map_apply (hgm v.1) (ht v), hgmap v.1]

/-- Independent coordinates over an infinite set `J`, each in `S` with positive probability:
almost surely infinitely many of them are in `S`. -/
theorem FrogModel.ZeroOne.measure_finite_hits {ι Y : Type*} [Countable ι] [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (S : Set Y) (hS : MeasurableSet S) (hp : 0 < μ S)
    (J : Set ι) (hJ : J.Infinite) :
    (Measure.infinitePi fun _ : ι => μ) {y | {i | i ∈ J ∧ y i ∈ S}.Finite} = 0 := by
  classical
  set P := Measure.infinitePi fun _ : ι => μ with hPdef
  have hsub : {y : ι → Y | {i | i ∈ J ∧ y i ∈ S}.Finite} ⊆
      ⋃ F : Finset ι, {y | ∀ i ∈ J \ ↑F, y i ∉ S} := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨(Set.Finite.toFinset hy), fun i hi hiS => hi.2 ?_⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hi.1, hiS⟩
  refine measure_mono_null hsub (measure_iUnion_null fun F => ?_)
  have hinf : (J \ ↑F).Infinite := hJ.sdiff F.finite_toSet
  have hbound : ∀ K : ℕ, P {y | ∀ i ∈ J \ ↑F, y i ∉ S} ≤ (1 - μ S) ^ K := by
    intro K
    obtain ⟨T, hT, hTcard⟩ := hinf.exists_subset_card_eq K
    calc P {y | ∀ i ∈ J \ ↑F, y i ∉ S} ≤ P (Set.pi ↑T fun _ => Sᶜ) :=
          measure_mono fun y hy i hi => hy i (hT hi)
      _ = ∏ i ∈ T, μ Sᶜ := Measure.infinitePi_pi (fun _ : ι => μ) (fun _ _ => hS.compl)
      _ = (1 - μ S) ^ K := by rw [Finset.prod_const, hTcard, prob_compl_eq_one_sub hS]
  have hlt : 1 - μ S < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne'
  have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  exact le_antisymm (ge_of_tendsto' htend hbound) zero_le

/-- A run of `n` parent steps has positive probability. -/
theorem FrogModel.ZeroOne.seqLaw_upRun_pos {d : ℕ} [NeZero d] (n : ℕ) :
    0 < (Measure.infinitePi fun _ : ℕ => stepLaw d) {x | upRun n x 0} := by
  have hS : MeasurableSet {ξ : Step d | ξ.2 = 0} := MeasurableSet.of_discrete
  have hsub : (Set.pi (↑(Finset.range n)) fun _ => {ξ : Step d | ξ.2 = 0}) ⊆
      {x | upRun n x 0} := by
    intro x hx j hj
    simpa using hx j (by simpa using hj)
  have hpos : 0 < stepLaw d {ξ : Step d | ξ.2 = 0} := by
    rw [stepLaw, ProbabilityTheory.uniformOn_univ]
    refine ENNReal.div_pos_iff.2 ⟨?_, ENNReal.natCast_ne_top _⟩
    exact Measure.count_ne_zero_iff.2 ⟨(⟨0, NeZero.pos d⟩, 0), rfl⟩
  calc 0 < ∏ _j ∈ Finset.range n, stepLaw d {ξ : Step d | ξ.2 = 0} :=
        pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => hpos.ne')
    _ = _ := (Measure.infinitePi_pi (fun _ : ℕ => stepLaw d) (fun _ _ => hS)).symm
    _ ≤ _ := measure_mono hsub

theorem FrogModel.ZeroOne.measurableSet_upRun {d : ℕ} (n k : ℕ) :
    MeasurableSet {x : ℕ → Step d | upRun n x k} := by
  have h_eq : {x : ℕ → Step d | upRun n x k} =
      ⋂ j ∈ Finset.range n, (fun x : ℕ → Step d => x (k + j)) ⁻¹' {ξ : Step d | ξ.2 = 0} := by
    ext x
    simp [upRun, Finset.mem_range]
  rw [h_eq]
  refine Finset.measurableSet_biInter (Finset.range n) ?_
  intro j hj
  have h_meas_fun : Measurable (fun (x : ℕ → Step d) => x (k + j)) :=
    measurable_pi_apply (k + j)
  have h_meas_set : MeasurableSet {ξ : Step d | ξ.2 = 0} :=
    MeasurableSet.of_discrete
  exact h_meas_fun h_meas_set

/-- Finitely many of countably many measurable events occur: a measurable event. -/
theorem FrogModel.ZeroOne.measurableSet_setOf_finite {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (S : ι → Set Ω) (hS : ∀ i, MeasurableSet (S i)) :
    MeasurableSet {ω | {i | ω ∈ S i}.Finite} := by
  have h_eq : {ω | {i | ω ∈ S i}.Finite} = ⋃ (F : Finset ι), ⋂ i ∈ (F : Set ι)ᶜ, (S i)ᶜ := by
    ext ω
    constructor
    · intro h
      have hfin : {i | ω ∈ S i}.Finite := h
      rcases Set.Finite.exists_finset_coe hfin with ⟨F, hF⟩
      refine Set.mem_iUnion.mpr ⟨F, ?_⟩
      simp
      intro i hi hω
      apply hi
      have hi_set : i ∈ (F : Set ι) := by
        rw [hF]
        exact hω
      exact hi_set
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨F, hF⟩
      simp at hF
      have h_sub : {i | ω ∈ S i} ⊆ (F : Set ι) := by
        intro i hi
        simp at hi
        by_contra! hiF
        have hω_not := hF i hiF
        exact hω_not hi
      exact Set.Finite.subset (Finset.finite_toSet F) h_sub
  rw [h_eq]
  refine MeasurableSet.iUnion ?_
  intro F
  refine MeasurableSet.biInter ?_ ?_
  · refine Set.Countable.mono (Set.subset_univ _) (Set.countable_univ (α := ι))
  · intro i hi
    exact (hS i).compl

theorem FrogModel.ZeroOne.frozenCount_eq_top_iff {d : ℕ} (ζ : Sample d) :
    frozenCount ζ = ⊤ ↔ {v | frozen ζ v}.Infinite := by
  classical
    set s := {v | frozen ζ v} with hs
    have h_tsum_eq : frozenCount ζ = ∑' (v : s), (1 : ℝ≥0∞) := by
      rw [frozenCount]
      calc
        ∑' v : Vertex d, (if (Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none) then (1 : ℝ≥0∞) else 0) =
            ∑' v : Vertex d, s.indicator (fun _ => (1 : ℝ≥0∞)) v := by
          refine tsum_congr (fun v => ?_)
          by_cases h : Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none
          · have hmem : v ∈ s := by dsimp [s]; exact h
            simp [h, hmem]
          · have hmem : v ∉ s := by dsimp [s]; exact h
            simp [h, hmem]
        _ = ∑' (v : s), (1 : ℝ≥0∞) := by rw [← tsum_subtype]
    rw [h_tsum_eq, ENNReal.tsum_one]
    -- Goal: ↑(ENat.card s) = ⊤ ↔ s.Infinite
    rw [ENat.toENNReal_eq_top]
    -- Goal: ENat.card s = ⊤ ↔ s.Infinite
    rw [ENat.card_eq_top]
    -- Goal: Infinite s ↔ s.Infinite
    rw [Set.infinite_coe_iff]
