module

public import FrogModel.LemmaX.LawDefs
public import FrogModel.LemmaX.Kill
public import FrogModel.Lemmas.Basic

@[expose] public section

/-!
# Lemma X: the coupling order on laws, and the induction

Sections 4 and 5 of the paper. The coupling order `CouplingLE`
(LemmaX/LawDefs.lean): every coupling below is the joint law of two measurable maps on one
probability space (`couplingLE_of_map`), or the image of a product of couplings under a
measurable equivalence (`couplingLE_prod`, `couplingLE_pi`, `couplingLE_infinitePi`).
Transitivity glues along the middle marginal by a disintegration
(`couplingLE_trans_of_standardBorel`). Then Lemma 4.5 of the paper (`brLaw_mono`), Lemma 4.4
(`psiLaw_mono`), `Phi_J` monotone (`phiLaw_mono`), the restriction (`restrict_mono`), and the
induction of Theorem 5.3 (`blockInduction`).

`map_prodMap_compProd_comap` restates `TauCeti.Measure.map_prodMap_compProd_comap` of
TauCeti/Probability/Kernel/Composition/MeasureCompProd.lean in
https://github.com/TauCetiProject/TauCeti (commit e15ed4cf), Copyright (c) 2026 The Tau Ceti
contributors, Apache License 2.0.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaX FrogModel.Recursion

/-- The left marginal of a coupling is a probability measure. -/
theorem FrogModel.LemmaX.isProbabilityMeasure_left {α : Type*} [MeasurableSpace α] [LE α]
    {P Q : Measure α} (h : CouplingLE P Q) : IsProbabilityMeasure P := by
  obtain ⟨π, hπ, h1, -, -⟩ := h
  rw [← h1]
  infer_instance

/-- The right marginal of a coupling is a probability measure. -/
theorem FrogModel.LemmaX.isProbabilityMeasure_right {α : Type*} [MeasurableSpace α] [LE α]
    {P Q : Measure α} (h : CouplingLE P Q) : IsProbabilityMeasure Q := by
  obtain ⟨π, hπ, -, h2, -⟩ := h
  rw [← h2]
  infer_instance

/-- Two measurable maps on one probability space, ordered almost surely, have ordered laws,
where `≤` is a measurable relation. -/
theorem FrogModel.LemmaX.couplingLE_of_map {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [LE α] (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → α) (hf : Measurable f)
    (hg : Measurable g) (hle : MeasurableSet {p : α × α | p.1 ≤ p.2}) (h : ∀ᵐ ω ∂μ, f ω ≤ g ω) :
    CouplingLE (μ.map f) (μ.map g) := by
  refine ⟨μ.map fun ω => (f ω, g ω), inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (hf.prodMk hg)]
    rfl
  · rw [Measure.map_map measurable_snd (hf.prodMk hg)]
    rfl
  · exact (ae_map_iff (hf.prodMk hg).aemeasurable hle).2 h

/-- The coupling order is reflexive where `≤` is a measurable relation. -/
theorem FrogModel.LemmaX.couplingLE_refl {α : Type*} [MeasurableSpace α] [Preorder α]
    (P : Measure α) [IsProbabilityMeasure P] (hle : MeasurableSet {p : α × α | p.1 ≤ p.2}) :
    CouplingLE P P := by
  have := couplingLE_of_map P id id measurable_id measurable_id hle
    (Eventually.of_forall fun x => le_refl x)
  simpa only [Measure.map_id] using this

/-- A measurable monotone map preserves the coupling order, where `≤` is measurable on its
target. -/
theorem FrogModel.LemmaX.couplingLE_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Preorder α] [Preorder β] (f : α → β) (hf : Measurable f) (hmono : Monotone f)
    (hle : MeasurableSet {p : β × β | p.1 ≤ p.2}) (P Q : Measure α) (h : CouplingLE P Q) :
    CouplingLE (P.map f) (Q.map f) := by
  obtain ⟨π, hπ, h1, h2, h3⟩ := h
  have := couplingLE_of_map π (f ∘ Prod.fst) (f ∘ Prod.snd) (hf.comp measurable_fst)
    (hf.comp measurable_snd) hle (h3.mono fun p hp => hmono hp)
  rwa [← Measure.map_map hf measurable_fst, ← Measure.map_map hf measurable_snd, h1, h2] at this

/-- On a countable type with measurable points, `≤` is a measurable relation. -/
theorem FrogModel.LemmaX.measurableSet_le_of_countable {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [LE α] :
    MeasurableSet {p : α × α | p.1 ≤ p.2} :=
  (Set.to_countable _).measurableSet

/-- The pointwise order on a countable product is a measurable relation when the order of each
factor is. -/
theorem FrogModel.LemmaX.measurableSet_le_pi {ι : Type*} [Countable ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, LE (α i)]
    (h : ∀ i, MeasurableSet {p : α i × α i | p.1 ≤ p.2}) :
    MeasurableSet {p : (∀ i, α i) × (∀ i, α i) | p.1 ≤ p.2} := by
  have he : {p : (∀ i, α i) × (∀ i, α i) | p.1 ≤ p.2} =
      ⋂ i, (fun p : (∀ i, α i) × (∀ i, α i) => (p.1 i, p.2 i)) ⁻¹' {q | q.1 ≤ q.2} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Pi.le_def]
  rw [he]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable fun p : (∀ i, α i) × (∀ i, α i) => (p.1 i, p.2 i) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  exact hm (h i)

/-- `blockCurve` is monotone in the block. -/
theorem FrogModel.LemmaX.blockCurve_mono {J : ℕ} (B B' : Fin J → ℕ∞) (h : B ≤ B') (s : ℕ) :
    blockCurve B s ≤ blockCurve B' s := by
  unfold blockCurve
  split_ifs with hs
  · exact h _
  · exact le_rfl

/-- The first `J` values of a curve are a measurable function of the curve. -/
theorem FrogModel.LemmaX.measurable_firstValues (J : ℕ) : Measurable (firstValues J) :=
  measurable_pi_iff.2 fun s => measurable_pi_apply ((s : ℕ) + 1)

/-- The block renewal curve is a measurable function of the blocks. -/
theorem FrogModel.LemmaX.measurable_brCurve (J : ℕ) :
    Measurable fun B : ℕ → Fin J → ℕ∞ => FrogModel.Order.brCurve J fun b => blockCurve (B b) := by
  have hadd : Measurable fun q : ℕ∞ × ℕ∞ => q.1 + q.2 := measurable_of_countable _
  have hb : ∀ b s, Measurable fun B : ℕ → Fin J → ℕ∞ => blockCurve (B b) s := fun b s =>
    (measurable_of_countable fun C : Fin J → ℕ∞ => blockCurve C s).comp (measurable_pi_apply b)
  refine measurable_pi_iff.2 fun n => ?_
  unfold FrogModel.Order.brCurve
  have hsum : ∀ k : ℕ, Measurable fun B : ℕ → Fin J → ℕ∞ =>
      ∑ b ∈ Finset.range k, blockCurve (B b) J := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      exact hadd.comp (ih.prodMk (hb k J))
  exact hadd.comp ((hsum _).prodMk (hb _ _))

/-- The zero curve is below every curve law. -/
theorem FrogModel.LemmaX.couplingLE_dirac_zero (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] :
    CouplingLE (Measure.dirac 0) Q := by
  have hle : MeasurableSet {p : (ℕ → ℕ∞) × (ℕ → ℕ∞) | p.1 ≤ p.2} :=
    measurableSet_le_pi fun _ => measurableSet_le_of_countable
  have := couplingLE_of_map Q (fun _ => 0) id measurable_const measurable_id hle
    (Eventually.of_forall fun G => zero_le)
  simpa only [Measure.map_const, measure_univ, one_smul, Measure.map_id] using this

/-- The coupling order increases the integral of a measurable monotone function. -/
theorem FrogModel.LemmaX.lintegral_mono_of_couplingLE {α : Type*} [MeasurableSpace α] [Preorder α]
    {P Q : Measure α} (h : CouplingLE P Q) (f : α → ℝ≥0∞) (hf : Measurable f)
    (hmono : Monotone f) : ∫⁻ x, f x ∂P ≤ ∫⁻ x, f x ∂Q := by
  obtain ⟨π, hπ, h1, h2, h3⟩ := h
  rw [← h1, ← h2, lintegral_map hf measurable_fst, lintegral_map hf measurable_snd]
  exact lintegral_mono_ae (h3.mono fun p hp => hmono hp)

/-- An almost sure property transfers along a measurable equivalence, with no measurability of
the property. -/
theorem FrogModel.LemmaX.ae_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) {p : β → Prop} (h : ∀ᵐ x ∂μ, p (e x)) : ∀ᵐ y ∂μ.map e, p y := by
  rw [ae_iff, e.map_apply]
  exact ae_iff.1 h

/-- Pairs of families as families of pairs. -/
def FrogModel.LemmaX.piPairEquiv {ι : Type*} (α : ι → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i × α i) ≃ᵐ (∀ i, α i) × (∀ i, α i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun :=
    (measurable_pi_iff.2 fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
      (measurable_pi_iff.2 fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_iff.2 fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)

/-- Two pairs as a pair of pairs. -/
def FrogModel.LemmaX.prodPairEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    (α × α) × (β × β) ≃ᵐ (α × β) × (α × β) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  measurable_invFun :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))

/-- Two couplings give a coupling of the product laws. -/
theorem FrogModel.LemmaX.couplingLE_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Preorder α] [Preorder β] (P P' : Measure α) (Q Q' : Measure β) (hP : CouplingLE P P')
    (hQ : CouplingLE Q Q') : CouplingLE (P.prod Q) (P'.prod Q') := by
  obtain ⟨π, hπ, h1, h2, h3⟩ := hP
  obtain ⟨σ, hσ, k1, k2, k3⟩ := hQ
  let e := prodPairEquiv α β
  refine ⟨(π.prod σ).map e, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst e.measurable, ← h1, ← k1,
      Measure.map_prod_map π σ measurable_fst measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd e.measurable, ← h2, ← k2,
      Measure.map_prod_map π σ measurable_snd measurable_snd]
    rfl
  · refine ae_map_equiv _ e ?_
    have ha : ∀ᵐ x ∂π.prod σ, x.1.1 ≤ x.1.2 := by
      have h3' : ∀ᵐ p ∂(π.prod σ).map Prod.fst, p.1 ≤ p.2 := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]; exact h3
      exact ae_of_ae_map measurable_fst.aemeasurable h3'
    have hb : ∀ᵐ x ∂π.prod σ, x.2.1 ≤ x.2.2 := by
      have k3' : ∀ᵐ p ∂(π.prod σ).map Prod.snd, p.1 ≤ p.2 := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]; exact k3
      exact ae_of_ae_map measurable_snd.aemeasurable k3'
    filter_upwards [ha, hb] with x hx1 hx2
    exact Prod.mk_le_mk.2 ⟨hx1, hx2⟩

/-- Finitely many couplings give a coupling of the product laws. -/
theorem FrogModel.LemmaX.couplingLE_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, Preorder (α i)] (P Q : ∀ i, Measure (α i))
    (h : ∀ i, CouplingLE (P i) (Q i)) : CouplingLE (Measure.pi P) (Measure.pi Q) := by
  choose π hπ h1 h2 h3 using h
  let e := piPairEquiv α
  refine ⟨(Measure.pi π).map e, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst e.measurable]
    have := Measure.pi_map_pi (μ := π) (f := fun _ => Prod.fst)
      (fun i => measurable_fst.aemeasurable)
    simp only [h1] at this
    exact this
  · rw [Measure.map_map measurable_snd e.measurable]
    have := Measure.pi_map_pi (μ := π) (f := fun _ => Prod.snd)
      (fun i => measurable_snd.aemeasurable)
    simp only [h2] at this
    exact this
  · refine ae_map_equiv _ e ?_
    have hall : ∀ᵐ x ∂Measure.pi π, ∀ i, (x i).1 ≤ (x i).2 :=
      ae_all_iff.2 fun i => (Measure.quasiMeasurePreserving_eval π i).ae (h3 i)
    exact hall.mono fun x hx => fun i => hx i

/-- Countably many couplings give a coupling of the infinite product laws. -/
theorem FrogModel.LemmaX.couplingLE_infinitePi {ι : Type*} [Countable ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, Preorder (α i)] (P Q : ∀ i, Measure (α i))
    (h : ∀ i, CouplingLE (P i) (Q i)) :
    CouplingLE (Measure.infinitePi P) (Measure.infinitePi Q) := by
  choose π hπ h1 h2 h3 using h
  let e := piPairEquiv α
  refine ⟨(Measure.infinitePi π).map e, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst e.measurable]
    have := Measure.infinitePi_map_pi π (f := fun _ => Prod.fst) (fun i => measurable_fst)
    simp only [h1] at this
    exact this
  · rw [Measure.map_map measurable_snd e.measurable]
    have := Measure.infinitePi_map_pi π (f := fun _ => Prod.snd) (fun i => measurable_snd)
    simp only [h2] at this
    exact this
  · refine ae_map_equiv _ e ?_
    have hall : ∀ᵐ x ∂Measure.infinitePi π, ∀ i, (x i).1 ≤ (x i).2 :=
      ae_all_iff.2 fun i =>
        (measurePreserving_eval_infinitePi π i).quasiMeasurePreserving.ae (h3 i)
    exact hall.mono fun x hx => fun i => hx i

/-- The image of `μ ⊗ₘ κ.comap f` under `Prod.map f id` is `μ.map f ⊗ₘ κ` (TauCeti
`map_prodMap_compProd_comap`, restated; see the module header). -/
theorem FrogModel.LemmaX.map_prodMap_compProd_comap {W Y Z : Type*} [MeasurableSpace W]
    [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure W) [SFinite μ] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] {f : W → Y} (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
  have hmap : Measurable (Prod.map f (id : Z → Z)) := hf.prodMap measurable_id
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.compProd_apply (hs.preimage hmap),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr fun w => ?_
  rw [Kernel.comap_apply]
  rfl

/-- The coupling order is transitive on a standard Borel space where `≤` is a measurable
relation: glue the second coupling to the first along the middle marginal by the disintegration
`condKernel` of the second. -/
theorem FrogModel.LemmaX.couplingLE_trans_of_standardBorel {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α] [Preorder α]
    (hle : MeasurableSet {p : α × α | p.1 ≤ p.2}) {P Q R : Measure α}
    (h₁ : CouplingLE P Q) (h₂ : CouplingLE Q R) : CouplingLE P R := by
  obtain ⟨π, hπ, hπ1, hπ2, hπle⟩ := h₁
  obtain ⟨σ, hσ, hσ1, hσ2, hσle⟩ := h₂
  set κ : Kernel (α × α) α := σ.condKernel.comap Prod.snd measurable_snd
  set γ : Measure ((α × α) × α) := π ⊗ₘ κ
  have hγ1 : γ.map Prod.fst = π := Measure.fst_compProd π κ
  have hγ2 : γ.map (Prod.map Prod.snd id) = σ := by
    rw [map_prodMap_compProd_comap π σ.condKernel measurable_snd]
    change π.snd ⊗ₘ σ.condKernel = σ
    rw [Measure.snd, hπ2, ← hσ1]
    exact σ.disintegrate σ.condKernel
  refine ⟨γ.map (fun t => (t.1.1, t.2)), inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map (by fun_prop) (by fun_prop), ← hπ1, ← hγ1,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · rw [Measure.map_map (by fun_prop) (by fun_prop), ← hσ2, ← hγ2,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · have e1 : ∀ᵐ t ∂γ, t.1.1 ≤ t.1.2 := by
      rw [← hγ1] at hπle; exact ae_of_ae_map (by fun_prop) hπle
    have e2 : ∀ᵐ t ∂γ, t.1.2 ≤ t.2 := by
      rw [← hγ2] at hσle; exact ae_of_ae_map (by fun_prop) hσle
    rw [ae_map_iff (by fun_prop) hle]
    filter_upwards [e1, e2] with t h1 h2 using h1.trans h2

/-- The coupling order is transitive on a countable type with measurable points. -/
theorem FrogModel.LemmaX.couplingLE_trans {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [Preorder α] (P Q R : Measure α)
    (hPQ : CouplingLE P Q) (hQR : CouplingLE Q R) : CouplingLE P R := by
  have hP := isProbabilityMeasure_left hPQ
  have : Nonempty α := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 hne, measure_empty] at h1
    exact zero_ne_one h1
  exact couplingLE_trans_of_standardBorel measurableSet_le_of_countable hPQ hQR

/-- **The restriction to the first `J` values preserves the coupling order.** -/
theorem FrogModel.LemmaX.restrict_mono (J : ℕ) (P Q : Measure (ℕ → ℕ∞)) (h : CouplingLE P Q) :
    CouplingLE (P.map (firstValues J)) (Q.map (firstValues J)) :=
  couplingLE_map (firstValues J) (measurable_firstValues J) (by intro G G' hG s; exact hG _)
    measurableSet_le_of_countable P Q h

/-- The pointwise order on curves is a measurable relation. -/
theorem FrogModel.LemmaX.measurableSet_le_curve :
    MeasurableSet {p : (ℕ → ℕ∞) × (ℕ → ℕ∞) | p.1 ≤ p.2} :=
  measurableSet_le_pi fun _ => measurableSet_le_of_countable

/-- **Lemma 4.5 of the paper for laws**: `H ≤ H'` gives `BR(H) ≤ BR(H')` (i.i.d. coupled pairs
of blocks, `brCurve` monotone in each block). -/
theorem FrogModel.LemmaX.brLaw_mono (J : ℕ) (H H' : Measure (Fin J → ℕ∞)) (h : CouplingLE H H') :
    CouplingLE (brLaw J H) (brLaw J H') := by
  obtain ⟨π, hπ, h1, h2, h3⟩ := h
  have hbr := measurable_brCurve J
  have hu1 : Measurable fun x : ℕ → (Fin J → ℕ∞) × (Fin J → ℕ∞) => fun b => (x b).1 :=
    measurable_pi_iff.2 fun b => measurable_fst.comp (measurable_pi_apply b)
  have hu2 : Measurable fun x : ℕ → (Fin J → ℕ∞) × (Fin J → ℕ∞) => fun b => (x b).2 :=
    measurable_pi_iff.2 fun b => measurable_snd.comp (measurable_pi_apply b)
  have hae : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => π), ∀ b, (x b).1 ≤ (x b).2 :=
    ae_all_iff.2 fun b =>
      (measurePreserving_eval_infinitePi (fun _ : ℕ => π) b).quasiMeasurePreserving.ae h3
  have := couplingLE_of_map (Measure.infinitePi fun _ : ℕ => π) _ _ (hbr.comp hu1)
    (hbr.comp hu2) measurableSet_le_curve
    (hae.mono fun x hx n => FrogModel.Order.brCurve_mono J _ _
      (fun b s => blockCurve_mono _ _ (hx b) s) n)
  rw [← Measure.map_map hbr hu1, ← Measure.map_map hbr hu2,
    Measure.infinitePi_map_pi _ (fun _ => measurable_fst),
    Measure.infinitePi_map_pi _ (fun _ => measurable_snd)] at this
  simp only [h1, h2] at this
  exact this

/-- The law of the directions is a probability measure. -/
theorem FrogModel.LemmaX.isProbabilityMeasure_dirMeasure (d : ℕ) :
    IsProbabilityMeasure (dirMeasure d) := by
  unfold dirMeasure
  infer_instance

/-- **Lemma 4.4 of the paper**: `P ≤ Q` on curves gives `Psi(P) ≤ Psi(Q)` (`d` independent
coupled pairs of child curves, one direction sequence shared by both sides). -/
theorem FrogModel.LemmaX.psiLaw_mono (d : ℕ) (P Q : Measure (ℕ → ℕ∞)) (h : CouplingLE P Q) :
    CouplingLE (psiLaw d P) (psiLaw d Q) := by
  obtain ⟨σ, hσ, h1, h2, h3⟩ := couplingLE_pi (fun _ : Fin d => P) (fun _ => Q) (fun _ => h)
  have hdir := isProbabilityMeasure_dirMeasure d
  have hpsi : Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => psiG x.1 x.2 :=
    measurable_psiG
  have hf1 : Measurable fun y : ((Fin d → ℕ → ℕ∞) × (Fin d → ℕ → ℕ∞)) × (ℕ → Fin (d + 1)) =>
      (y.1.1, y.2) := (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hf2 : Measurable fun y : ((Fin d → ℕ → ℕ∞) × (Fin d → ℕ → ℕ∞)) × (ℕ → Fin (d + 1)) =>
      (y.1.2, y.2) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hae : ∀ᵐ y ∂σ.prod (dirMeasure d), y.1.1 ≤ y.1.2 := by
    have h3' : ∀ᵐ p ∂(σ.prod (dirMeasure d)).map Prod.fst, p.1 ≤ p.2 := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]; exact h3
    exact ae_of_ae_map measurable_fst.aemeasurable h3'
  have := couplingLE_of_map (σ.prod (dirMeasure d)) _ _ (hpsi.comp hf1) (hpsi.comp hf2)
    measurableSet_le_curve
    (hae.mono fun y hy j => psiG_le_of_le _ _ _ (fun c i => hy c i) j)
  rw [← Measure.map_map hpsi hf1, ← Measure.map_map hpsi hf2] at this
  have e1 := Measure.map_prod_map σ (dirMeasure d) measurable_fst measurable_id
  have e2 := Measure.map_prod_map σ (dirMeasure d) measurable_snd measurable_id
  rw [Measure.map_id] at e1 e2
  rw [h1] at e1
  rw [h2] at e2
  unfold psiLaw
  rw [e1, e2]
  exact this

/-- `Phi_J` is monotone for the coupling order. -/
theorem FrogModel.LemmaX.phiLaw_mono (d J : ℕ) (H H' : Measure (Fin J → ℕ∞))
    (h : CouplingLE H H') : CouplingLE (phiLaw d J H) (phiLaw d J H') :=
  restrict_mono J _ _ (psiLaw_mono d _ _ (brLaw_mono J H H' h))

/-- **The block laws are below a supersolution** (Theorem 5.3 of the paper): Lemma 4.3 in
domination form, Claim A at `d` and `J`, and `Phi_J(H) ≤ H` give `E_K ≤ H` for every `K`;
every transitivity step is on `Fin J → ℕ∞`. -/
theorem FrogModel.LemmaX.blockInduction (d : ℕ) [NeZero d] (J : ℕ) (H : Measure (Fin J → ℕ∞))
    (h0 : CouplingLE (curveLaw d 0) (psiLaw d (Measure.dirac 0)))
    (hs : ∀ K, CouplingLE (curveLaw d (K + 1)) (psiLaw d (curveLaw d K)))
    (hA : ∀ K, CouplingLE (curveLaw d K) (brLaw J (blockLaw d K J)))
    (hH : CouplingLE (phiLaw d J H) H) (K : ℕ) : CouplingLE (blockLaw d K J) H := by
  have hHp := isProbabilityMeasure_right hH
  have hBR : IsProbabilityMeasure (brLaw J H) := by unfold brLaw; infer_instance
  induction K with
  | zero =>
    have a1 : CouplingLE (blockLaw d 0 J) ((psiLaw d (Measure.dirac 0)).map (firstValues J)) :=
      restrict_mono J _ _ h0
    have a2 : CouplingLE ((psiLaw d (Measure.dirac 0)).map (firstValues J)) (phiLaw d J H) :=
      restrict_mono J _ _ (psiLaw_mono d _ _ (couplingLE_dirac_zero (brLaw J H)))
    exact couplingLE_trans _ _ _ (couplingLE_trans _ _ _ a1 a2) hH
  | succ K ih =>
    have a1 : CouplingLE (blockLaw d (K + 1) J) ((psiLaw d (curveLaw d K)).map (firstValues J)) :=
      restrict_mono J _ _ (hs K)
    have a2 : CouplingLE ((psiLaw d (curveLaw d K)).map (firstValues J))
        (phiLaw d J (blockLaw d K J)) :=
      restrict_mono J _ _ (psiLaw_mono d _ _ (hA K))
    have a3 : CouplingLE (phiLaw d J (blockLaw d K J)) (phiLaw d J H) :=
      phiLaw_mono d J _ _ ih
    exact couplingLE_trans _ _ _ (couplingLE_trans _ _ _
      (couplingLE_trans _ _ _ a1 a2) a3) hH
