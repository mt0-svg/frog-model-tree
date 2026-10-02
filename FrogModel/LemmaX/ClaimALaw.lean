module

public import FrogModel.LemmaX.ClaimA

@[expose] public section

/-!
# Claim A, laws (proof of Lemma 5.2 (2) and (3) of the paper)

(c) The original configuration has the law of the sample of `N_K` (`claimAOrig_holds`): its
coordinates are distinct coordinates of an i.i.d. family (`infinitePi_map_pair_comp`).

(b) The block outputs are i.i.d. with law `E_K` (`claimAIid_holds`). The woken set of a block is
a stopping set and the output is determined by it (`reachedK_block_congr`), so one refresh makes
the next configuration a fresh block configuration independent of the output
(`map_blockOut_refresh`, from `FrogModel.Stage.map_refresh`, Lemma 3.4 of the paper). By
induction on `n`, the first `n` outputs, the current configuration and the fresh configurations
still unused are independent, with laws `E_K^n`, `P_J` and `P_J^ℕ` (`map_blockOuts`).

Claim A (`claimA_holds`): on the probability space of the blocks, the curve of the original
configuration and the block renewal curve of the outputs are a coupling, by (a), (b) and (c).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.LemmaX

/-! ## Independent families of coordinates -/

/-- The coordinates `e a` of a family generate at most the coordinates in the range of `e`. -/
theorem comap_reindex_le_iSup {ι γ Y : Type*} [MeasurableSpace Y] (e : γ → ι) :
    MeasurableSpace.comap (fun η : ι → Y => fun a => η (e a))
        (inferInstance : MeasurableSpace (γ → Y)) ≤
      ⨆ i ∈ Set.range e, MeasurableSpace.comap (fun η : ι → Y => η i)
        (inferInstance : MeasurableSpace Y) := by
  have h_prod_eq : (inferInstance : MeasurableSpace (γ → Y)) =
      ⨆ a, MeasurableSpace.comap (fun x : γ → Y => x a) (inferInstance : MeasurableSpace Y) :=
    rfl
  rw [h_prod_eq, MeasurableSpace.comap_iSup]
  refine iSup_le fun a => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂_of_le (e a) ⟨a, rfl⟩ le_rfl

/-- Two injective reindexings with disjoint ranges of an i.i.d. family are independent i.i.d.
families. -/
theorem infinitePi_map_pair_comp {ι α β Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (e₁ : α → ι) (e₂ : β → ι)
    (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂) (h : ∀ a b, e₁ a ≠ e₂ b) :
    (Measure.infinitePi fun _ : ι => μ).map
        (fun η => (fun a => η (e₁ a), fun b => η (e₂ b))) =
      (Measure.infinitePi fun _ : α => μ).prod (Measure.infinitePi fun _ : β => μ) := by
  let PI := Measure.infinitePi fun _ : ι => μ
  have hm₁ : Measurable fun η : ι → Y => fun a => η (e₁ a) := by fun_prop
  have hm₂ : Measurable fun η : ι → Y => fun b => η (e₂ b) := by fun_prop
  have h_indep : iIndep (fun i : ι => MeasurableSpace.comap (fun η : ι → Y => η i)
      (inferInstance : MeasurableSpace Y)) PI :=
    (iIndepFun_infinitePi (P := fun _ : ι => μ) (X := fun _ y => y) fun _ => measurable_id).iIndep
  have h_le : ∀ i, MeasurableSpace.comap (fun η : ι → Y => η i) (inferInstance : MeasurableSpace Y)
      ≤ inferInstanceAs (MeasurableSpace (ι → Y)) := fun i =>
    Measurable.comap_le (measurable_pi_apply i)
  have hdisj : Disjoint (Set.range e₁) (Set.range e₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact h a b hb.symm
  have hind : IndepFun (fun η : ι → Y => fun a => η (e₁ a)) (fun η => fun b => η (e₂ b)) PI := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (indep_of_indep_of_le_right (indep_iSup_of_disjoint h_le h_indep hdisj)
        (comap_reindex_le_iSup e₂))
      (comap_reindex_le_iSup e₁)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hm₁.aemeasurable hm₂.aemeasurable).1 hind,
    Measure.map_infinitePi_infinitePi_of_inj h₁, Measure.map_infinitePi_infinitePi_of_inj h₂]

/-- An i.i.d. family over `α ⊕ β` splits into independent i.i.d. families over `α` and `β`. -/
theorem infinitePi_map_sum_split {α β Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    (Measure.infinitePi fun _ : α ⊕ β => μ).map
        (fun η => (fun a => η (.inl a), fun b => η (.inr b))) =
      (Measure.infinitePi fun _ : α => μ).prod (Measure.infinitePi fun _ : β => μ) :=
  infinitePi_map_pair_comp μ Sum.inl Sum.inr Sum.inl_injective Sum.inr_injective
    fun _ _ => Sum.inl_ne_inr

/-- Two independent i.i.d. families over `α` and `β` form an i.i.d. family over `α ⊕ β`. -/
theorem prod_map_sumElim {α β Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    ((Measure.infinitePi fun _ : α => μ).prod (Measure.infinitePi fun _ : β => μ)).map
        (fun p => Sum.elim p.1 p.2) =
      Measure.infinitePi fun _ : α ⊕ β => μ := by
  have hs : Measurable fun η : α ⊕ β → Y => (fun a => η (.inl a), fun b => η (.inr b)) := by
    fun_prop
  have he : Measurable fun p : (α → Y) × (β → Y) => Sum.elim p.1 p.2 := by
    refine measurable_pi_iff.2 fun l => ?_
    cases l with
    | inl a => exact (measurable_pi_apply a).comp measurable_fst
    | inr b => exact (measurable_pi_apply b).comp measurable_snd
  rw [← infinitePi_map_sum_split μ, Measure.map_map he hs]
  have hid : ((fun p : (α → Y) × (β → Y) => Sum.elim p.1 p.2) ∘
      fun η : α ⊕ β → Y => (fun a => η (.inl a), fun b => η (.inr b))) = id := by
    funext η l
    cases l <;> rfl
  rw [hid, Measure.map_id]

/-- An i.i.d. sequence splits into its first term and the independent i.i.d. sequence of the
others. -/
theorem infinitePi_map_head_tail {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun f => (f 0, fun k => f (k + 1))) =
      μ.prod (Measure.infinitePi fun _ : ℕ => μ) :=
  FrogModel.infinitePi_map_pair_injective μ (fun k => k + 1) (add_left_injective 1) 0
    fun k => Nat.succ_ne_zero k

/-! ## Probability measures -/

theorem isProbabilityMeasure_blockMeasure {d : ℕ} [NeZero d] (J : ℕ) :
    IsProbabilityMeasure (blockMeasure d J) := by
  unfold blockMeasure
  infer_instance

theorem isProbabilityMeasure_curveLaw {d : ℕ} [NeZero d] (K : ℕ) :
    IsProbabilityMeasure (FrogModel.Recursion.curveLaw d K) := by
  have : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  have : IsProbabilityMeasure (FrogModel.Recursion.initMeasure d) := by
    unfold FrogModel.Recursion.initMeasure; infer_instance
  unfold FrogModel.Recursion.curveLaw
  infer_instance

theorem isProbabilityMeasure_blockLaw {d : ℕ} [NeZero d] (K J : ℕ) :
    IsProbabilityMeasure (blockLaw d K J) := by
  have := isProbabilityMeasure_curveLaw (d := d) K
  unfold blockLaw
  infer_instance

/-! ## (c) The original configuration -/

/-- **Claim A (c)**: the original configuration has the law of the sample of `N_K`. -/
theorem claimAOrig_holds : ClaimAOrig := by
  intro d _ J hJ
  let P0 : Measure (ℕ → Step d) := Measure.infinitePi fun _ : ℕ => stepLaw d
  have hcurry := Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Vertex d ⊕ Fin J) => P0)
  have e₂inj : Function.Injective fun i : ℕ =>
      ((i / J, Sum.inr ⟨i % J, Nat.mod_lt i hJ⟩) : ℕ × (Vertex d ⊕ Fin J)) := by
    intro i i' hii
    simp only [Prod.mk.injEq, Sum.inr.injEq, Fin.mk.injEq] at hii
    rw [← Nat.div_add_mod' i J, ← Nat.div_add_mod' i' J, hii.1, hii.2]
  have hpair := infinitePi_map_pair_comp P0
    (fun v : Vertex d => ((0, Sum.inl v) : ℕ × (Vertex d ⊕ Fin J)))
    (fun i : ℕ => ((i / J, Sum.inr ⟨i % J, Nat.mod_lt i hJ⟩) : ℕ × (Vertex d ⊕ Fin J)))
    (fun v v' hvv => by simpa using hvv) e₂inj (fun v i => by simp)
  have hmc : Measurable (MeasurableEquiv.curry ℕ (Vertex d ⊕ Fin J) (ℕ → Step d)) :=
    (MeasurableEquiv.curry ℕ (Vertex d ⊕ Fin J) (ℕ → Step d)).measurable
  have hmo : Measurable fun ω : ℕ → BlockSample d J => (blockSleep (ω 0), origActive J hJ ω) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.2 fun v => (measurable_pi_apply (Sum.inl v)).comp
        (measurable_pi_apply 0)
    · exact measurable_pi_iff.2 fun i =>
        (measurable_pi_apply (Sum.inr (⟨i % J, Nat.mod_lt i hJ⟩ : Fin J) : Vertex d ⊕ Fin J)).comp
          (measurable_pi_apply (i / J))
  change (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Vertex d ⊕ Fin J => P0).map
    _ = _
  rw [← hcurry, Measure.map_map hmo hmc]
  exact hpair

/-! ## (b) The block outputs -/

section Iid

variable {d : ℕ}

/-- The sleeping frogs of a block configuration are a measurable function of it. -/
theorem measurable_blockSleep {J : ℕ} :
    Measurable (blockSleep : BlockSample d J → Sample d) := by
  unfold blockSleep
  exact measurable_pi_iff.2 fun v => measurable_pi_apply (Sum.inl v)

/-- The initial frogs of a block configuration are a measurable function of it. -/
theorem measurable_blockActive {J : ℕ} :
    Measurable (blockActive : BlockSample d J → ℕ → ℕ → Step d) := by
  refine measurable_pi_iff.2 fun a => ?_
  unfold blockActive
  by_cases h : a < J
  · simp only [h, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]
    exact measurable_pi_apply _

/-- The block output is a measurable function of the block configuration. -/
theorem measurable_blockOut (K J : ℕ) : Measurable (blockOut (d := d) K (J := J)) := by
  have h : Measurable fun ω : BlockSample d J => curveK K (blockSleep ω) (blockActive ω) :=
    Measurable.comp (g := fun p : Sample d × (ℕ → ℕ → Step d) => curveK K p.1 p.2)
      (f := fun ω : BlockSample d J => (blockSleep ω, blockActive ω)) (measurable_curveK K)
      (measurable_blockSleep.prodMk measurable_blockActive)
  unfold blockOut
  exact measurable_pi_iff.2 fun s => (measurable_pi_apply ((s : ℕ) + 1)).comp h

/-- Each label is in the woken set on a measurable event. -/
theorem measurableSet_mem_blockWoken (K J : ℕ) (i : Vertex d ⊕ Fin J) :
    MeasurableSet {ω : BlockSample d J | i ∈ blockWoken K ω} := by
  cases i with
  | inl v =>
    simp only [mem_blockWoken_inl]
    exact (measurable_blockSleep.prodMk measurable_blockActive) (measurableSet_reachedK K J v)
  | inr t =>
    simp only [mem_blockWoken_inr, Set.ofPred_true]
    exact MeasurableSet.univ

/-- The root-refreshed configuration of each block is a measurable function of the blocks. -/
theorem measurable_refreshSeq (K J b : ℕ) :
    Measurable fun ω : ℕ → BlockSample d J => refreshSeq K J ω b := by
  induction b with
  | zero => exact measurable_pi_apply 0
  | succ b ih =>
    have e : (fun ω : ℕ → BlockSample d J => refreshSeq K J ω (b + 1)) = fun ω =>
        FrogModel.Stage.refresh (blockWoken K) (refreshSeq K J ω b) (ω (b + 1)) := by
      funext ω
      simp only [refreshSeq]
    rw [e]
    exact Measurable.comp (g := fun p : BlockSample d J × BlockSample d J =>
        FrogModel.Stage.refresh (blockWoken K) p.1 p.2)
      (f := fun ω : ℕ → BlockSample d J => (refreshSeq K J ω b, ω (b + 1)))
      (FrogModel.Stage.measurable_refresh (blockWoken K) (measurableSet_mem_blockWoken K J))
      (ih.prodMk (measurable_pi_apply (b + 1)))

/-- **The woken set determines the block** (proof of Lemma 5.2 (2) of the paper): a block
configuration that agrees with `ω` on the woken set of `ω` reaches the same vertices with `n ≤ J`
initial frogs. -/
theorem reachedK_block_congr (K J : ℕ) (ω ω' : BlockSample d J)
    (hag : ∀ i ∈ blockWoken K ω, ω i = ω' i) (n : ℕ) (hn : n ≤ J) (v : Vertex d) :
    reachedK K (blockSleep ω') (blockActive ω') n v ↔
      reachedK K (blockSleep ω) (blockActive ω) n v := by
  have hA : ∀ a < J, blockActive ω' a = blockActive ω a := by
    intro a ha
    simp only [blockActive, ha, ↓reduceDIte]
    exact (hag _ (mem_blockWoken_inr K J ω ⟨a, ha⟩)).symm
  have hS : ∀ w, reachedK K (blockSleep ω) (blockActive ω) J w →
      blockSleep ω' w = blockSleep ω w := fun w hw =>
    (hag _ ((mem_blockWoken_inl K J ω w).2 hw)).symm
  constructor
  · rintro ⟨a, ha, u, hu, hau, huv⟩
    have haJ : a < J := lt_of_lt_of_le ha hn
    rw [hA a haJ] at hau
    refine ⟨a, ha, u, hu, hau, ?_⟩
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c e _ hce ih =>
      have hc : reachedK K (blockSleep ω) (blockActive ω) J c :=
        reachedK_mono K _ _ hn c ⟨a, ha, u, hu, hau, ih⟩
      exact ih.tail (starArcK_congr K _ _ c e (hS c hc) hce)
  · rintro ⟨a, ha, u, hu, hau, huv⟩
    have haJ : a < J := lt_of_lt_of_le ha hn
    refine ⟨a, ha, u, hu, by rw [hA a haJ]; exact hau, ?_⟩
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c e huc hce ih =>
      have hc : reachedK K (blockSleep ω) (blockActive ω) J c :=
        reachedK_mono K _ _ hn c ⟨a, ha, u, hu, hau, huc⟩
      exact ih.tail (starArcK_congr K _ _ c e (hS c hc).symm hce)

/-- The block woken set is a stopping set. -/
theorem isStoppingSet_blockWoken (K J : ℕ) :
    FrogModel.Stage.IsStoppingSet (blockWoken (d := d) K (J := J)) := by
  intro ω ω' hag
  ext i
  cases i with
  | inl v =>
    rw [mem_blockWoken_inl, mem_blockWoken_inl]
    exact reachedK_block_congr K J ω ω' hag J le_rfl v
  | inr t => exact iff_of_true (mem_blockWoken_inr K J ω' t) (mem_blockWoken_inr K J ω t)

/-- The block output is determined by the woken set. -/
theorem blockOut_congr (K J : ℕ) (ω ω' : BlockSample d J)
    (hag : ∀ i ∈ blockWoken K ω, ω i = ω' i) : blockOut K ω' = blockOut K ω := by
  have hA : ∀ a < J, blockActive ω' a = blockActive ω a := by
    intro a ha
    simp only [blockActive, ha, ↓reduceDIte]
    exact (hag _ (mem_blockWoken_inr K J ω ⟨a, ha⟩)).symm
  funext s
  unfold blockOut curveK
  have hs : (s : ℕ) + 1 ≤ J := s.isLt
  congr 1
  · congr 1
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ha, h⟩
      exact ⟨ha, by rw [← hA a (lt_of_lt_of_le ha hs)]; exact h⟩
    · rintro ⟨ha, h⟩
      exact ⟨ha, by rw [hA a (lt_of_lt_of_le ha hs)]; exact h⟩
  · congr 1
    ext b
    simp only [Set.mem_ofPred_eq]
    rw [reachedK_block_congr K J ω ω' hag _ hs b]
    constructor
    · rintro ⟨hb, h⟩
      have hS : blockSleep ω' b = blockSleep ω b :=
        (hag _ ((mem_blockWoken_inl K J ω b).2 (reachedK_mono K _ _ hs b hb))).symm
      exact ⟨hb, by rw [← hS]; exact h⟩
    · rintro ⟨hb, h⟩
      have hS : blockSleep ω' b = blockSleep ω b :=
        (hag _ ((mem_blockWoken_inl K J ω b).2 (reachedK_mono K _ _ hs b hb))).symm
      exact ⟨hb, by rw [hS]; exact h⟩

/-- Every event of the block output is determined by the woken set. -/
theorem isDetermined_blockOut (K J : ℕ) (S : Set (Fin J → ℕ∞)) :
    FrogModel.Stage.IsDetermined (blockWoken (d := d) K (J := J)) (blockOut K ⁻¹' S) := by
  intro ω ω' hag
  simp only [Set.mem_preimage]
  rw [blockOut_congr K J ω ω' hag]

variable [NeZero d]

/-- **One refresh** (Lemma 3.4 of the paper, in the proof of Lemma 5.2 (2)): under two
independent block configurations, the output of the first and the refreshed configuration are
independent, with laws the output law and the block law. -/
theorem map_blockOut_refresh (K J : ℕ) :
    ((blockMeasure d J).prod (blockMeasure d J)).map
        (fun p => (blockOut K p.1, FrogModel.Stage.refresh (blockWoken K) p.1 p.2)) =
      ((blockMeasure d J).map (blockOut K)).prod (blockMeasure d J) := by
  have := isProbabilityMeasure_blockMeasure (d := d) J
  have hKm := measurableSet_mem_blockWoken (d := d) K J
  have hR := FrogModel.Stage.measurable_refresh (blockWoken (d := d) K (J := J)) hKm
  have hO := measurable_blockOut (d := d) K J
  have hF : Measurable fun p : BlockSample d J × BlockSample d J =>
      (blockOut K p.1, FrogModel.Stage.refresh (blockWoken K) p.1 p.2) :=
    (hO.comp measurable_fst).prodMk hR
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply hF (hA.prod hB), Measure.map_apply hO hA]
  have hset : (fun p : BlockSample d J × BlockSample d J =>
      (blockOut K p.1, FrogModel.Stage.refresh (blockWoken K) p.1 p.2)) ⁻¹' (A ×ˢ B) =
      (fun p : BlockSample d J × BlockSample d J =>
        FrogModel.Stage.refresh (blockWoken K) p.1 p.2) ⁻¹' B ∩
        ((blockOut K ⁻¹' A) ×ˢ Set.univ) := by
    ext p
    simp [and_comm]
  have hmr := FrogModel.Stage.map_refresh
    (fun _ : Vertex d ⊕ Fin J => Measure.infinitePi fun _ : ℕ => stepLaw d) (blockWoken K)
    (isStoppingSet_blockWoken K J) hKm _ (isDetermined_blockOut K J A) (hO hA)
  rw [hset, ← Measure.restrict_apply (hR hB), ← Measure.map_apply hR hB]
  change ((((Measure.infinitePi fun _ : Vertex d ⊕ Fin J =>
      Measure.infinitePi fun _ : ℕ => stepLaw d).prod
        (Measure.infinitePi fun _ : Vertex d ⊕ Fin J =>
      Measure.infinitePi fun _ : ℕ => stepLaw d)).restrict ((blockOut K ⁻¹' A) ×ˢ Set.univ)).map
        fun p => FrogModel.Stage.refresh (blockWoken K) p.1 p.2) B = _
  rw [hmr, Measure.smul_apply, smul_eq_mul]
  rfl

omit [NeZero d] in
/-- The block configuration of a sample: its vertex frogs and its first `J` initial frogs. -/
theorem measurable_blockOfPair (J : ℕ) :
    Measurable fun p : Sample d × (ℕ → ℕ → Step d) => fun l : Vertex d ⊕ Fin J =>
      Sum.elim p.1 (fun t : Fin J => p.2 t) l := by
  refine measurable_pi_iff.2 fun l => ?_
  cases l with
  | inl v => exact (measurable_pi_apply v).comp measurable_fst
  | inr t => exact (measurable_pi_apply (t : ℕ)).comp measurable_snd

/-- The vertex frogs and the first `J` initial frogs of a sample of `N_K` form a block
configuration of law `P_J`. -/
theorem map_blockOfPair (J : ℕ) :
    ((frogMeasure d).prod (FrogModel.Recursion.initMeasure d)).map
        (fun p : Sample d × (ℕ → ℕ → Step d) => fun l : Vertex d ⊕ Fin J =>
          Sum.elim p.1 (fun t : Fin J => p.2 t) l) =
      blockMeasure d J := by
  let P0 : Measure (ℕ → Step d) := Measure.infinitePi fun _ : ℕ => stepLaw d
  have hres : (Measure.infinitePi fun _ : ℕ => P0).map (fun ξ (t : Fin J) => ξ t) =
      Measure.infinitePi fun _ : Fin J => P0 :=
    Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective
  have hmr : Measurable fun ξ : ℕ → ℕ → Step d => fun t : Fin J => ξ t := by fun_prop
  have hel : Measurable fun p : Sample d × (Fin J → ℕ → Step d) => Sum.elim p.1 p.2 := by
    refine measurable_pi_iff.2 fun l => ?_
    cases l with
    | inl a => exact (measurable_pi_apply a).comp measurable_fst
    | inr b => exact (measurable_pi_apply b).comp measurable_snd
  have hcomp : (fun p : Sample d × (ℕ → ℕ → Step d) => fun l : Vertex d ⊕ Fin J =>
      Sum.elim p.1 (fun t : Fin J => p.2 t) l) =
      (fun p : Sample d × (Fin J → ℕ → Step d) => Sum.elim p.1 p.2) ∘
        Prod.map id fun ξ (t : Fin J) => ξ t := by
    funext p l
    cases l <;> rfl
  change ((Measure.infinitePi fun _ : Vertex d => P0).prod (Measure.infinitePi fun _ : ℕ => P0)).map
    _ = Measure.infinitePi fun _ : Vertex d ⊕ Fin J => P0
  rw [hcomp, ← Measure.map_map hel (measurable_id.prodMap hmr), ← Measure.map_prod_map _ _
    measurable_id hmr, Measure.map_id, hres, prod_map_sumElim]

omit [NeZero d] in
/-- The block output of the block configuration of a sample is the first `J` values of its
curve. -/
theorem blockOut_blockOfPair (K J : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d) :
    blockOut K (fun l : Vertex d ⊕ Fin J => Sum.elim ζ (fun t : Fin J => ξ t) l) =
      firstValues J (curveK K ζ ξ) := by
  funext s
  unfold blockOut firstValues
  refine curveK_congr K _ _ _ _ _ (fun v _ => rfl) fun a ha => ?_
  have haJ : a < J := lt_of_lt_of_le ha s.isLt
  simp only [blockActive, haJ, ↓reduceDIte, Sum.elim_inr]

/-- **Claim A (b), first half**: the block output has law `E_K`. -/
theorem map_blockOut (K J : ℕ) : (blockMeasure d J).map (blockOut K) = blockLaw d K J := by
  rw [← map_blockOfPair J, Measure.map_map (measurable_blockOut K J) (measurable_blockOfPair J)]
  unfold blockLaw FrogModel.Recursion.curveLaw
  rw [Measure.map_map (measurable_firstValues J) (measurable_curveK K)]
  congr 1
  funext p
  exact blockOut_blockOfPair K J p.1 p.2

omit [NeZero d] in
/-- The output of a block and the refreshed configuration are a measurable function of the block
and of the fresh configuration. -/
theorem measurable_blockOut_refresh (K J : ℕ) :
    Measurable fun p : BlockSample d J × BlockSample d J =>
      (blockOut K p.1, FrogModel.Stage.refresh (blockWoken K) p.1 p.2) :=
  ((measurable_blockOut K J).comp measurable_fst).prodMk
    (FrogModel.Stage.measurable_refresh (blockWoken K) (measurableSet_mem_blockWoken K J))

/-- **One refresh** in the form of a measure preserving map: `(B, refresh)`
sends `P_J ⊗ P_J` to `E_K ⊗ P_J`. -/
theorem measurePreserving_blockOut_refresh (K J : ℕ) :
    MeasurePreserving (fun p : BlockSample d J × BlockSample d J =>
        (blockOut K p.1, FrogModel.Stage.refresh (blockWoken K) p.1 p.2))
      ((blockMeasure d J).prod (blockMeasure d J)) ((blockLaw d K J).prod (blockMeasure d J)) :=
  ⟨measurable_blockOut_refresh K J, by rw [map_blockOut_refresh, map_blockOut]⟩

omit [NeZero d] in
/-- Appending a value of law `E` to `n` i.i.d. values of law `E` gives `n + 1` i.i.d. values. -/
theorem measurePreserving_snoc {X : Type*} [MeasurableSpace X] (E : Measure X)
    [IsProbabilityMeasure E] (n : ℕ) :
    MeasurePreserving (fun p : (Fin n → X) × X => (Fin.snoc p.1 p.2 : Fin (n + 1) → X))
      ((Measure.pi fun _ : Fin n => E).prod E) (Measure.pi fun _ : Fin (n + 1) => E) := by
  have h := (MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X)
    (Fin.last n)) (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n))).comp
    (Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin n => E) (ν := E))
  convert h using 1
  funext p
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv_last]
  rfl

/-- One block of the induction: from the first `n` outputs, the configuration of block `n` and
the fresh configurations after it, to the first `n + 1` outputs, the configuration of block
`n + 1` and the fresh configurations after it. -/
theorem measurePreserving_blockStep (K J n : ℕ) :
    MeasurePreserving
      (fun p : (Fin n → Fin J → ℕ∞) × (BlockSample d J × (ℕ → BlockSample d J)) =>
        ((Fin.snoc p.1 (blockOut K p.2.1) : Fin (n + 1) → Fin J → ℕ∞),
          (FrogModel.Stage.refresh (blockWoken K) p.2.1 (p.2.2 0), fun k => p.2.2 (k + 1))))
      ((Measure.pi fun _ : Fin n => blockLaw d K J).prod
        ((blockMeasure d J).prod (Measure.infinitePi fun _ : ℕ => blockMeasure d J)))
      ((Measure.pi fun _ : Fin (n + 1) => blockLaw d K J).prod
        ((blockMeasure d J).prod (Measure.infinitePi fun _ : ℕ => blockMeasure d J))) := by
  have := isProbabilityMeasure_blockMeasure (d := d) J
  have := isProbabilityMeasure_blockLaw (d := d) K J
  let P := blockMeasure d J
  let E := blockLaw d K J
  let M := Measure.infinitePi fun _ : ℕ => P
  let Pn := Measure.pi fun _ : Fin n => E
  have ht : MeasurePreserving (fun f : ℕ → BlockSample d J => (f 0, fun k => f (k + 1)))
      M (P.prod M) :=
    ⟨by fun_prop, infinitePi_map_head_tail P⟩
  have h1 := (MeasurePreserving.id Pn).prod ((MeasurePreserving.id P).prod ht)
  have h2 := (MeasurePreserving.id Pn).prod
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc P P M))
  have h3 := (MeasurePreserving.id Pn).prod
    ((measurePreserving_blockOut_refresh (d := d) K J).prod (MeasurePreserving.id M))
  have h4 := (MeasurePreserving.id Pn).prod (measurePreserving_prodAssoc E P M)
  have h5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc Pn E (P.prod M))
  have h6 := (measurePreserving_snoc E n).prod (MeasurePreserving.id (P.prod M))
  have h := h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))
  convert h using 1
  funext p
  rfl

/-- The first `n` block outputs, the configuration of block `n` and the fresh configurations
after it are independent, with laws `E_K^n`, `P_J` and `P_J^ℕ`. -/
theorem map_blockOuts (K J n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => blockMeasure d J).map
        (fun ω => ((fun b : Fin n => blockOut K (refreshSeq K J ω b)),
          (refreshSeq K J ω n, fun k => ω (n + 1 + k)))) =
      (Measure.pi fun _ : Fin n => blockLaw d K J).prod
        ((blockMeasure d J).prod (Measure.infinitePi fun _ : ℕ => blockMeasure d J)) := by
  have := isProbabilityMeasure_blockMeasure (d := d) J
  have := isProbabilityMeasure_blockLaw (d := d) K J
  have hmeas : ∀ n, Measurable fun ω : ℕ → BlockSample d J =>
      ((fun b : Fin n => blockOut K (refreshSeq K J ω b)),
        (refreshSeq K J ω n, fun k => ω (n + 1 + k))) := by
    intro n
    refine Measurable.prodMk ?_ (Measurable.prodMk (measurable_refreshSeq K J n) ?_)
    · exact measurable_pi_iff.2 fun b =>
        (measurable_blockOut K J).comp (measurable_refreshSeq K J b)
    · exact measurable_pi_iff.2 fun k => measurable_pi_apply (n + 1 + k)
  induction n with
  | zero =>
    have hht : Measurable fun f : ℕ → BlockSample d J => (f 0, fun k => f (k + 1)) := by
      fun_prop
    rw [Measure.pi_of_empty, Measure.dirac_prod, ← infinitePi_map_head_tail (blockMeasure d J),
      Measure.map_map measurable_prodMk_left hht]
    congr 1
    funext ω
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · funext b
      exact b.elim0
    · funext k
      simp only [Function.comp_apply]
      congr 1
      omega
  | succ n ih =>
    have hstep := measurePreserving_blockStep (d := d) K J n
    rw [← hstep.map_eq, ← ih, Measure.map_map hstep.measurable (hmeas n)]
    congr 1
    funext ω
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · funext b
      refine Fin.lastCases ?_ (fun i => ?_) b
      · simp only [Function.comp_apply, Fin.snoc_last, Fin.val_last]
      · simp only [Function.comp_apply, Fin.snoc_castSucc, Fin.val_castSucc]
    · funext k
      simp only [Function.comp_apply]
      congr 1
      omega

end Iid

/-- **Claim A (b)**: the block output has law `E_K`, and the outputs of the root-refreshed blocks
are i.i.d. with law `E_K`. -/
theorem claimAIid_holds : ClaimAIid := by
  intro d _ K J _
  refine ⟨map_blockOut K J, ?_⟩
  have := isProbabilityMeasure_blockMeasure (d := d) J
  have := isProbabilityMeasure_blockLaw (d := d) K J
  have hYall : Measurable fun ω : ℕ → BlockSample d J => fun b => blockOut K (refreshSeq K J ω b) :=
    measurable_pi_iff.2 fun b => (measurable_blockOut K J).comp (measurable_refreshSeq K J b)
  have hfin : ∀ n, (Measure.infinitePi fun _ : ℕ => blockMeasure d J).map
      (fun ω => fun b : Fin n => blockOut K (refreshSeq K J ω b)) =
        Measure.pi fun _ : Fin n => blockLaw d K J := by
    intro n
    have hmeas : Measurable fun ω : ℕ → BlockSample d J =>
        ((fun b : Fin n => blockOut K (refreshSeq K J ω b)),
          (refreshSeq K J ω n, fun k => ω (n + 1 + k))) := by
      refine Measurable.prodMk ?_ (Measurable.prodMk (measurable_refreshSeq K J n) ?_)
      · exact measurable_pi_iff.2 fun b =>
          (measurable_blockOut K J).comp (measurable_refreshSeq K J b)
      · exact measurable_pi_iff.2 fun k => measurable_pi_apply (n + 1 + k)
    have h := congrArg (Measure.map Prod.fst) (map_blockOuts (d := d) K J n)
    rw [Measure.map_map measurable_fst hmeas, Measure.map_fst_prod, measure_univ, one_smul] at h
    exact h
  refine Measure.eq_infinitePi (fun _ : ℕ => blockLaw d K J) fun s t ht => ?_
  classical
  obtain ⟨n, hn⟩ : ∃ n, ∀ i ∈ s, i < n :=
    ⟨s.sup id + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
  let t' : Fin n → Set (Fin J → ℕ∞) := fun b => if (b : ℕ) ∈ s then t b else Set.univ
  have hres : Measurable fun B : ℕ → Fin J → ℕ∞ => fun b : Fin n => B b := by fun_prop
  have ht' : MeasurableSet (Set.pi Set.univ t') := by
    refine MeasurableSet.univ_pi fun b => ?_
    simp only [t']
    split_ifs
    · exact ht _
    · exact MeasurableSet.univ
  have hset : Set.pi (↑s) t =
      (fun B : ℕ → Fin J → ℕ∞ => fun b : Fin n => B b) ⁻¹' Set.pi Set.univ t' := by
    ext B
    simp only [Set.mem_pi, Finset.mem_coe, Set.mem_preimage, Set.mem_univ, true_implies, t']
    constructor
    · intro h b
      split_ifs with hb
      · exact h b hb
      · trivial
    · intro h i hi
      have := h ⟨i, hn i hi⟩
      simpa [hi] using this
  rw [hset, ← Measure.map_apply hres ht', Measure.map_map hres hYall]
  change ((Measure.infinitePi fun _ : ℕ => blockMeasure d J).map
    (fun ω => fun b : Fin n => blockOut K (refreshSeq K J ω b))) _ = _
  rw [hfin n, Measure.pi_pi]
  have hprod : ∀ b : Fin n, blockLaw d K J (t' b) =
      (fun i : ℕ => if i ∈ s then blockLaw d K J (t i) else 1) b := by
    intro b
    simp only [t']
    split_ifs
    · rfl
    · exact measure_univ
  rw [Finset.prod_congr rfl fun b _ => hprod b, Fin.prod_univ_eq_prod_range
    (fun i : ℕ => if i ∈ s then blockLaw d K J (t i) else 1) n, Finset.prod_ite_mem,
    Finset.inter_eq_right.2 fun i hi => Finset.mem_range.2 (hn i hi)]

/-- The original configuration is a measurable function of the blocks. -/
theorem measurable_origPair {d : ℕ} (J : ℕ) (hJ : 0 < J) :
    Measurable fun ω : ℕ → BlockSample d J => (blockSleep (ω 0), origActive J hJ ω) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.2 fun v => (measurable_pi_apply (Sum.inl v)).comp
      (measurable_pi_apply 0)
  · exact measurable_pi_iff.2 fun i =>
      (measurable_pi_apply (Sum.inr (⟨i % J, Nat.mod_lt i hJ⟩ : Fin J) : Vertex d ⊕ Fin J)).comp
        (measurable_pi_apply (i / J))

/-- **Claim A** (Proposition 5.1 of the paper): `N_K ≤ BR(E_K)` in the coupling order. -/
theorem claimA_holds : ClaimA := by
  intro d _ K J hJ
  have := isProbabilityMeasure_blockMeasure (d := d) J
  have hO := measurable_origPair (d := d) J hJ
  have hY : Measurable fun ω : ℕ → BlockSample d J => fun b => blockOut K (refreshSeq K J ω b) :=
    measurable_pi_iff.2 fun b => (measurable_blockOut K J).comp (measurable_refreshSeq K J b)
  have hf : Measurable fun ω : ℕ → BlockSample d J =>
      curveK K (blockSleep (ω 0)) (origActive J hJ ω) :=
    Measurable.comp (g := fun p : Sample d × (ℕ → ℕ → Step d) => curveK K p.1 p.2)
      (f := fun ω : ℕ → BlockSample d J => (blockSleep (ω 0), origActive J hJ ω))
      (measurable_curveK K) hO
  have hg : Measurable fun ω : ℕ → BlockSample d J =>
      FrogModel.Order.brCurve J fun b => blockCurve (blockOut K (refreshSeq K J ω b)) :=
    Measurable.comp (g := fun B : ℕ → Fin J → ℕ∞ => FrogModel.Order.brCurve J fun b =>
        blockCurve (B b))
      (f := fun ω : ℕ → BlockSample d J => fun b => blockOut K (refreshSeq K J ω b))
      (measurable_brCurve J) hY
  have h := couplingLE_of_map (Measure.infinitePi fun _ : ℕ => blockMeasure d J) _ _ hf hg
    measurableSet_le_curve (ae_of_all _ fun ω => Pi.le_def.2 fun m =>
      claimAPathwise_holds d K J hJ ω m)
  have h1 : (Measure.infinitePi fun _ : ℕ => blockMeasure d J).map
      (fun ω => curveK K (blockSleep (ω 0)) (origActive J hJ ω)) =
        FrogModel.Recursion.curveLaw d K := by
    have e := Measure.map_map (μ := Measure.infinitePi fun _ : ℕ => blockMeasure d J)
      (g := fun p : Sample d × (ℕ → ℕ → Step d) => curveK K p.1 p.2)
      (f := fun ω : ℕ → BlockSample d J => (blockSleep (ω 0), origActive J hJ ω))
      (measurable_curveK K) hO
    rw [claimAOrig_holds d J hJ] at e
    exact e.symm
  have h2 : (Measure.infinitePi fun _ : ℕ => blockMeasure d J).map
      (fun ω => FrogModel.Order.brCurve J fun b => blockCurve (blockOut K (refreshSeq K J ω b))) =
        brLaw J (blockLaw d K J) := by
    have e := Measure.map_map (μ := Measure.infinitePi fun _ : ℕ => blockMeasure d J)
      (g := fun B : ℕ → Fin J → ℕ∞ => FrogModel.Order.brCurve J fun b => blockCurve (B b))
      (f := fun ω : ℕ → BlockSample d J => fun b => blockOut K (refreshSeq K J ω b))
      (measurable_brCurve J) hY
    rw [(claimAIid_holds d K J hJ).2] at e
    exact e.symm
  rw [h1, h2] at h
  exact h

end FrogModel.LemmaX
