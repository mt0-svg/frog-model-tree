module

public import FrogModel.Pool.Main

@[expose] public section

/-!
# Laws of reindexed, split and adaptively read i.i.d. families (Lemma 4.3 of the paper)

Generic facts on `Measure.infinitePi`, used for the law of the child curves:

- `map_infinitePi_pair`: two injective reindexings with disjoint ranges are independent i.i.d.
  families.
- `map_infinitePi_prodMk`: applying `z ↦ (f z, g z)` coordinatewise to an i.i.d. family, with
  `f z` and `g z` independent, gives two independent i.i.d. families.
- `map_prod_section`: if every section `F x` maps `ν` to `lam`, the map `(x, y) ↦ (x, F x y)`
  maps `μ ⊗ ν` to `μ ⊗ lam`.
- `map_prod_reindex`: an injective reindexing chosen by an independent variable (thinning).
- `map_adapted`: adaptive reading. If the coordinate read at step `k` depends only on the
  parameter coordinates and on the values read before, and is never a parameter coordinate nor
  read twice, the parameter and the values read are independent i.i.d. families.
- `ae_infinite_eq`: an i.i.d. uniform sequence on a finite type takes every value infinitely
  often.
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.Recursion

/-- A value followed by a sequence. -/
def seqCons {E : Type*} (e : E) (x : ℕ → E) : ℕ → E
  | 0 => e
  | i + 1 => x i

/-! ### Product splits and reindexings -/

/-- Two injective reindexings with disjoint ranges are independent i.i.d. families. -/
theorem map_infinitePi_pair {ι α β E : Type*} [MeasurableSpace E] (P : ι → Measure E)
    [∀ i, IsProbabilityMeasure (P i)] (f : α → ι) (g : β → ι) (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : ∀ a b, f a ≠ g b) :
    (Measure.infinitePi P).map (fun ω => (fun a => ω (f a), fun b => ω (g b))) =
      (Measure.infinitePi fun a => P (f a)).prod (Measure.infinitePi fun b => P (g b)) := by
  -- Define the combined injection h : α ⊕ β → ι
  let h : α ⊕ β → ι := Sum.elim f g
  have h_inj : Function.Injective h := by
    intro x y hxy
    rcases x with (xa | xb) <;> rcases y with (ya | yb)
    · simpa [h] using hf hxy
    · exfalso; exact hfg xa yb hxy
    · exfalso; exact hfg ya xb hxy.symm
    · simpa [h] using hg hxy
  -- By the reindexing lemma, pushforward by h gives infinitePi on the reindexed family
  have h_map : (Measure.infinitePi P).map (fun ω i => ω (h i)) =
      Measure.infinitePi (fun i : α ⊕ β => P (h i)) :=
    Measure.map_infinitePi_infinitePi_of_inj h_inj
  -- Relate the two maps via σ
  let σ : (α ⊕ β → E) → (α → E) × (β → E) := fun z => (fun a => z (Sum.inl a), fun b => z (Sum.inr b))
  have hσ_meas : Measurable σ := by
    refine Measurable.prodMk ?_ ?_
    · rw [measurable_pi_iff]; intro a; exact measurable_pi_apply (Sum.inl a)
    · rw [measurable_pi_iff]; intro b; exact measurable_pi_apply (Sum.inr b)
  have hΦ_meas : Measurable (fun (ω : ι → E) (i : α ⊕ β) => ω (h i)) := by
    rw [measurable_pi_iff]; intro i; exact measurable_pi_apply (h i)
  have h_map_ψ : (Measure.infinitePi P).map (fun ω => (fun a => ω (f a), fun b => ω (g b))) =
      ((Measure.infinitePi P).map (fun ω i => ω (h i))).map σ := by
    have h_comp : (fun (ω : ι → E) => (fun a => ω (f a), fun b => ω (g b))) =
        σ ∘ (fun (ω : ι → E) (i : α ⊕ β) => ω (h i)) := by
      ext ω
      · simp [σ, h]
      · simp [σ, h]
    rw [h_comp, Measure.map_map hσ_meas hΦ_meas]
  rw [h_map_ψ, h_map]
  -- Goal: (Measure.infinitePi (fun i : α ⊕ β => P (h i))).map σ =
  --   (Measure.infinitePi fun a => P (f a)).prod (Measure.infinitePi fun b => P (g b))
  let μ := Measure.infinitePi (fun i : α ⊕ β => P (h i))
  let ψ : (α → E) × (β → E) → (α ⊕ β → E) := fun p k =>
    match k with
    | Sum.inl a => p.1 a
    | Sum.inr b => p.2 b
  have hψ_meas : Measurable ψ := by
    rw [measurable_pi_iff]
    intro k
    rcases k with (a | b)
    · have : (fun p : (α → E) × (β → E) => ψ p (Sum.inl a)) = (fun p => p.1 a) := by
        ext p; rfl
      rw [this]
      exact (measurable_pi_apply a).comp measurable_fst
    · have : (fun p : (α → E) × (β → E) => ψ p (Sum.inr b)) = (fun p => p.2 b) := by
        ext p; rfl
      rw [this]
      exact (measurable_pi_apply b).comp measurable_snd
  let ν := (Measure.infinitePi fun a => P (f a)).prod (Measure.infinitePi fun b => P (g b))
  -- Prove ν.map ψ = μ using eq_infinitePi
  have h_eq : ν.map ψ = μ := by
    apply Measure.eq_infinitePi (μ := fun i : α ⊕ β => P (h i))
    intro s t ht
    -- Need: (ν.map ψ) (Set.pi s t) = ∏ i ∈ s, P (h i) (t i)
    rw [Measure.map_apply hψ_meas (MeasurableSet.pi s.countable_toSet (fun i hi => ht i))]
    -- Now: ν (ψ⁻¹' (Set.pi s t)) = ∏ i ∈ s, P (h i) (t i)
    -- Compute ψ⁻¹' (Set.pi s t) as a rectangle
    have h_inj_on_left : Set.InjOn (Sum.inl (β := β)) (Sum.inl (β := β) ⁻¹' (s : Set (α ⊕ β))) :=
      Sum.inl_injective.injOn (s := Sum.inl (β := β) ⁻¹' (s : Set (α ⊕ β)))
    have h_inj_on_right : Set.InjOn (Sum.inr (α := α)) (Sum.inr (α := α) ⁻¹' (s : Set (α ⊕ β))) :=
      Sum.inr_injective.injOn (s := Sum.inr (α := α) ⁻¹' (s : Set (α ⊕ β)))
    let sα := s.preimage (Sum.inl (β := β)) h_inj_on_left
    let sβ := s.preimage (Sum.inr (α := α)) h_inj_on_right
    have h_preimage : ψ ⁻¹' (Set.pi (s : Set (α ⊕ β)) t) =
        (Set.pi sα (fun a => t (Sum.inl a))) ×ˢ
        (Set.pi sβ (fun b => t (Sum.inr b))) := by
      ext p
      constructor
      · intro hp
        have h_mem : ∀ (k : α ⊕ β), k ∈ s → ψ p k ∈ t k := hp
        constructor
        · intro a ha
          have hmem : Sum.inl a ∈ s := by simpa [sα, Finset.mem_preimage] using ha
          simpa [ψ] using h_mem (Sum.inl a) hmem
        · intro b hb
          have hmem : Sum.inr b ∈ s := by simpa [sβ, Finset.mem_preimage] using hb
          simpa [ψ] using h_mem (Sum.inr b) hmem
      · intro hp
        rcases hp with ⟨hp₁, hp₂⟩
        intro k hk
        rcases k with (a | b)
        · have ha : a ∈ sα := by simpa [sα, Finset.mem_preimage] using hk
          exact hp₁ a ha
        · have hb : b ∈ sβ := by simpa [sβ, Finset.mem_preimage] using hk
          exact hp₂ b hb
    rw [h_preimage]
    -- Now ν (A ×ˢ B) where A = Set.pi sα ... and B = Set.pi sβ ...
    -- Use Measure.prod_prod
    dsimp [ν]
    rw [Measure.prod_prod]
    -- Now: (infinitePi fun a => P (f a)) A * (infinitePi fun b => P (g b)) B
    rw [Measure.infinitePi_pi (μ := fun a : α => P (f a)) (fun i hi => ht (Sum.inl i)),
      Measure.infinitePi_pi (μ := fun b : β => P (g b)) (fun i hi => ht (Sum.inr i))]
    -- Now: (∏ a ∈ sα, P (f a) (t (Sum.inl a))) * (∏ b ∈ sβ, P (g b) (t (Sum.inr b)))
    -- = ∏ i ∈ s, P (h i) (t i)
    -- This is the product splitting identity
    have h_prod_split : (∏ a ∈ sα, P (f a) (t (Sum.inl a))) * (∏ b ∈ sβ, P (g b) (t (Sum.inr b))) =
        (∏ i ∈ s, P (h i) (t i)) := by
      -- Split s into left and right parts
      classical
      let s_left := s.filter fun i => match i with | Sum.inl _ => True | Sum.inr _ => False
      let s_right := s.filter fun i => match i with | Sum.inl _ => False | Sum.inr _ => True
      have h_disjoint : Disjoint s_left s_right := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext i; simp [s_left, s_right]; rcases i with (a | b) <;> simp
      have h_union : s_left ∪ s_right = s := by
        ext i; simp [s_left, s_right]; rcases i with (a | b) <;> simp
      rw [← h_union, Finset.prod_union h_disjoint]
      -- Now reindex each part
      have h_left : (∏ i ∈ s_left, P (h i) (t i)) = (∏ a ∈ sα, P (f a) (t (Sum.inl a))) := by
        have h_image : sα.image (Sum.inl (β := β)) = s_left := by
          ext i
          constructor
          · intro hi
            rcases Finset.mem_image.mp hi with ⟨a, ha, rfl⟩
            apply Finset.mem_filter.mpr
            constructor
            · simpa [s_left] using Finset.mem_preimage.mp ha
            · simp
          · intro hi
            rcases Finset.mem_filter.mp hi with ⟨hi_mem, hi_val⟩
            rcases i with (a | b)
            · apply Finset.mem_image.mpr
              exact ⟨a, by simpa [sα, Finset.mem_preimage] using hi_mem, rfl⟩
            · exfalso; simpa [s_left] using hi_val
        rw [← h_image, Finset.prod_image (fun x hx y hy h => Sum.inl_injective h)]
        simp [h]
      have h_right : (∏ i ∈ s_right, P (h i) (t i)) = (∏ b ∈ sβ, P (g b) (t (Sum.inr b))) := by
        have h_image : sβ.image (Sum.inr (α := α)) = s_right := by
          ext i
          constructor
          · intro hi
            rcases Finset.mem_image.mp hi with ⟨b, hb, rfl⟩
            apply Finset.mem_filter.mpr
            constructor
            · simpa [s_right] using Finset.mem_preimage.mp hb
            · simp
          · intro hi
            rcases Finset.mem_filter.mp hi with ⟨hi_mem, hi_val⟩
            rcases i with (a | b)
            · exfalso; simpa [s_right] using hi_val
            · apply Finset.mem_image.mpr
              exact ⟨b, by simpa [sβ, Finset.mem_preimage] using hi_mem, rfl⟩
        rw [← h_image, Finset.prod_image (fun x hx y hy h => Sum.inr_injective h)]
        simp [h]
      rw [h_left, h_right]
    rw [h_prod_split]
  -- Now from h_eq : ν.map ψ = μ, we get μ.map σ = ν
  have h_comp : σ ∘ ψ = id := by
    ext ⟨x, y⟩
    · rfl
    · rfl
  calc
    μ.map σ = (ν.map ψ).map σ := by rw [h_eq]
    _ = ν.map (σ ∘ ψ) := by rw [Measure.map_map hσ_meas hψ_meas]
    _ = ν.map id := by rw [h_comp]
    _ = ν := by simp

/-- An i.i.d. family of pairs with independent components is a pair of independent i.i.d.
families. -/
theorem infinitePi_prod_map {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (μ' : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    (Measure.infinitePi fun _ : ι => μ.prod μ').map (fun z => (fun i => (z i).1, fun i => (z i).2)) =
      (Measure.infinitePi fun _ : ι => μ).prod (Measure.infinitePi fun _ : ι => μ') := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow X Y ι with he
  have hfe : (fun z : ι → X × Y => (fun i => (z i).1, fun i => (z i).2)) = ⇑e := rfl
  set P := (Measure.infinitePi fun _ : ι => μ).prod (Measure.infinitePi fun _ : ι => μ') with hP
  have hQ : P.map e.symm = Measure.infinitePi (fun _ : ι => μ.prod μ') := by
    refine (Measure.isProjectiveLimit_infinitePi (fun _ : ι => μ.prod μ')).unique ?_ |>.symm
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) e.symm.measurable]
    have hcomp : (I.restrict ∘ ⇑e.symm : (ι → X) × (ι → Y) → (I → X × Y)) =
        ⇑(MeasurableEquiv.arrowProdEquivProdArrow X Y I).symm ∘
          Prod.map I.restrict I.restrict := rfl
    rw [hcomp, ← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow X Y I).symm.measurable
      ((Finset.measurable_restrict I).prodMap (Finset.measurable_restrict I)), hP,
      ← Measure.map_prod_map _ _ (Finset.measurable_restrict I) (Finset.measurable_restrict I),
      Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
    exact (measurePreserving_arrowProdEquivProdArrow X Y I (fun _ => μ) (fun _ => μ')).symm.map_eq
  rw [hfe, ← hQ, Measure.map_map e.measurable e.symm.measurable]
  simp

/-- Coordinatewise `z ↦ (f z, g z)` with `f z`, `g z` independent: two independent i.i.d.
families. -/
theorem map_infinitePi_prodMk {ι X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (ν : Measure Z) [IsProbabilityMeasure ν] (f : Z → X) (g : Z → Y)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ν.map (fun z => (f z, g z)) = (ν.map f).prod (ν.map g)) :
    (Measure.infinitePi fun _ : ι => ν).map (fun y => (fun i => f (y i), fun i => g (y i))) =
      (Measure.infinitePi fun _ : ι => ν.map f).prod (Measure.infinitePi fun _ : ι => ν.map g) := by
  have hprod_meas : Measurable (fun (z : Z) => (f z, g z)) := hf.prodMk hg
  haveI hprob_f : IsProbabilityMeasure (ν.map f) :=
    ((Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance)
  haveI hprob_g : IsProbabilityMeasure (ν.map g) :=
    ((Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance)
  have h_meas_H : Measurable (fun (y : ι → Z) (i : ι) => (f (y i), g (y i))) := by
    rw [measurable_pi_iff]
    intro i
    exact hprod_meas.comp (measurable_pi_apply i)
  have h_meas_G : Measurable (fun (z : ι → X × Y) => (fun i => (z i).1, fun i => (z i).2)) := by
    have h_fst : Measurable (fun (z : ι → X × Y) (i : ι) => (z i).1) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_fst.comp (measurable_pi_apply i)
    have h_snd : Measurable (fun (z : ι → X × Y) (i : ι) => (z i).2) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_snd.comp (measurable_pi_apply i)
    exact Measurable.prodMk h_fst h_snd
  calc
    (Measure.infinitePi fun _ : ι => ν).map (fun y => (fun i => f (y i), fun i => g (y i)))
        = (Measure.infinitePi fun _ : ι => ν).map
          ((fun (z : ι → X × Y) => (fun i => (z i).1, fun i => (z i).2)) ∘
           (fun (y : ι → Z) (i : ι) => (f (y i), g (y i)))) := by
      rfl
    _ = ((Measure.infinitePi fun _ : ι => ν).map
          (fun (y : ι → Z) (i : ι) => (f (y i), g (y i)))).map
          (fun (z : ι → X × Y) => (fun i => (z i).1, fun i => (z i).2)) := by
      rw [Measure.map_map h_meas_G h_meas_H]
    _ = (Measure.infinitePi fun i : ι => (ν.map (fun (z : Z) => (f z, g z)))).map
          (fun (z : ι → X × Y) => (fun i => (z i).1, fun i => (z i).2)) := by
      rw [Measure.infinitePi_map_pi (fun _ : ι => ν) (fun i => hprod_meas)]
    _ = (Measure.infinitePi fun _ : ι => ((ν.map f).prod (ν.map g))).map
          (fun (z : ι → X × Y) => (fun i => (z i).1, fun i => (z i).2)) := by
      rw [hfg]
    _ = (Measure.infinitePi fun _ : ι => ν.map f).prod (Measure.infinitePi fun _ : ι => ν.map g) := by
      rw [FrogModel.Recursion.infinitePi_prod_map (ν.map f) (ν.map g)]

/-- The first value of an i.i.d. sequence and the rest are independent. -/
theorem map_infinitePi_head_tail {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun x => (x 0, fun t => x (t + 1))) =
      ν.prod (Measure.infinitePi fun _ : ℕ => ν) := by
  set F : (ℕ → E) → ((Unit → E) × (ℕ → E)) := fun x => (fun _ => x 0, fun t => x (t + 1)) with hF
  set G : ((Unit → E) × (ℕ → E)) → (E × (ℕ → E)) := Prod.map (fun u => u ()) id with hG
  have hFG : G ∘ F = fun x => (x 0, fun t => x (t + 1)) := by
    ext x <;> simp [hG, hF]
  have h_pair := FrogModel.Recursion.map_infinitePi_pair (fun (_ : ℕ) => ν)
    (fun (_ : Unit) => (0 : ℕ)) (fun (b : ℕ) => b + 1)
    (fun a b _ => PUnit.ext a b)
    Nat.succ_injective
    (fun a b => by simp)
  have h_eval : (Measure.infinitePi fun (_ : Unit) => ν).map (fun u => u ()) = ν := by
    simpa using Measure.infinitePi_map_eval (μ := fun (_ : Unit) => ν) ()
  have h_map_prod_map : ((Measure.infinitePi fun (_ : Unit) => ν).prod
      (Measure.infinitePi fun (_ : ℕ) => ν)).map G = ν.prod (Measure.infinitePi fun (_ : ℕ) => ν) := by
    rw [hG]
    calc
      ((Measure.infinitePi fun (_ : Unit) => ν).prod
        (Measure.infinitePi fun (_ : ℕ) => ν)).map
        (Prod.map (fun (u : Unit → E) => u ()) id) =
        ((Measure.infinitePi fun (_ : Unit) => ν).map (fun u => u ())).prod
          ((Measure.infinitePi fun (_ : ℕ) => ν).map id) := by
        rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
      _ = ν.prod ((Measure.infinitePi fun (_ : ℕ) => ν).map id) := by rw [h_eval]
      _ = ν.prod (Measure.infinitePi fun (_ : ℕ) => ν) := by simp
  calc
    (Measure.infinitePi fun _ : ℕ => ν).map (fun x => (x 0, fun t => x (t + 1))) =
      (Measure.infinitePi fun _ : ℕ => ν).map (G ∘ F) := by rw [hFG]
    _ = ((Measure.infinitePi fun _ : ℕ => ν).map F).map G := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = ((Measure.infinitePi fun (_ : Unit) => ν).prod
        (Measure.infinitePi fun (_ : ℕ) => ν)).map G := by
      rw [h_pair]
    _ = ν.prod (Measure.infinitePi fun (_ : ℕ) => ν) := by rw [h_map_prod_map]

/-- If every section `F x` maps `ν` to `lam`, `(x, y) ↦ (x, F x y)` maps `μ ⊗ ν` to
`μ ⊗ lam`. -/
theorem map_prod_section {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (lam : Measure Z) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure lam] (F : X → Y → Z)
    (hF : Measurable (Function.uncurry F)) (h : ∀ᵐ x ∂μ, ν.map (F x) = lam) :
    (μ.prod ν).map (fun p => (p.1, F p.1 p.2)) = μ.prod lam := by
  let g : X × Y → X × Z := fun p => (p.1, F p.1 p.2)
  have hg_meas : Measurable g := Measurable.prodMk measurable_fst hF
  -- Use prod_eq: if two measures agree on rectangles, they're equal
  -- We want to show (μ.prod ν).map g = μ.prod lam
  -- prod_eq applied to μ and lam with μν := (μ.prod ν).map g
  -- gives: (rectangle condition) → μ.prod lam = (μ.prod ν).map g
  have h_eq := Measure.prod_eq (μ := μ) (ν := lam) (μν := (μ.prod ν).map g)
  -- h_eq : (∀ s t, MeasurableSet s → MeasurableSet t → ((μ.prod ν).map g) (s ×ˢ t) = μ s * lam t) → μ.prod lam = (μ.prod ν).map g
  apply (h_eq _).symm
  intro s t hs ht
  have hrect_meas : MeasurableSet (s ×ˢ t) := MeasurableSet.prod hs ht
  -- Need: ((μ.prod ν).map g) (s ×ˢ t) = μ s * lam t
  rw [Measure.map_apply hg_meas hrect_meas]
  -- Now: (μ.prod ν) (g ⁻¹' (s ×ˢ t)) = μ s * lam t
  have h_preimage_meas : MeasurableSet (g ⁻¹' (s ×ˢ t)) :=
    MeasurableSet.preimage hrect_meas hg_meas
  rw [Measure.prod_apply h_preimage_meas]
  -- Goal: ∫⁻ (x : X), ν (Prod.mk x ⁻¹' (g ⁻¹' (s ×ˢ t))) ∂μ = μ s * lam t
  classical
  have h_preimage_eq (x : X) : ν (Prod.mk x ⁻¹' (g ⁻¹' (s ×ˢ t))) = s.indicator (fun x' => ν ((F x') ⁻¹' t)) x := by
    by_cases hx : x ∈ s
    · have h_eq : Prod.mk x ⁻¹' (g ⁻¹' (s ×ˢ t)) = (F x) ⁻¹' t := by
        ext y; simp [g, Set.mk_preimage_prod, Set.mem_preimage, hx]
      rw [h_eq, Set.indicator_of_mem hx]
    · have h_eq : Prod.mk x ⁻¹' (g ⁻¹' (s ×ˢ t)) = ∅ := by
        ext y; simp [g, Set.mk_preimage_prod, Set.mem_preimage, hx]
      rw [h_eq, measure_empty, Set.indicator_apply]
      simp [hx]
  rw [lintegral_congr (fun x => h_preimage_eq x)]
  -- Now: ∫⁻ (x : X), s.indicator (fun x' => ν ((F x') ⁻¹' t)) x ∂μ = μ s * lam t
  have h_ae : (fun x => s.indicator (fun x' => ν ((F x') ⁻¹' t)) x) =ᵐ[μ] (fun x => s.indicator (fun _ => lam t) x) := by
    filter_upwards [h] with x hx_eq
    have hFx_meas : Measurable (F x) :=
      hF.comp (measurable_prodMk_left (x := x))
    have h_val : ν ((F x) ⁻¹' t) = lam t := by
      rw [← Measure.map_apply hFx_meas ht, hx_eq]
    simp [Set.indicator_apply, h_val]
  rw [lintegral_congr_ae h_ae]
  rw [lintegral_indicator_const hs (lam t)]
  rw [mul_comm]

/-- **Thinning.** An injective reindexing chosen by an independent variable gives an i.i.d.
family independent of that variable. -/
theorem map_prod_reindex {X J E : Type*} [MeasurableSpace X] [MeasurableSpace E] [Countable J]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (idx : X → J → ℕ) (hidx : ∀ j n, MeasurableSet {x | idx x j = n})
    (hinj : ∀ᵐ x ∂μ, Function.Injective (idx x)) :
    (μ.prod (Measure.infinitePi fun _ : ℕ => ν)).map (fun p => (p.1, fun j => p.2 (idx p.1 j))) =
      μ.prod (Measure.infinitePi fun _ : J => ν) := by
  let ν_ℕ := Measure.infinitePi fun _ : ℕ => ν
  let ν_J := Measure.infinitePi fun _ : J => ν
  let F : X × (ℕ → E) → X × (J → E) := fun p => (p.1, fun j => p.2 (idx p.1 j))
  -- F is measurable
  have h_meas_idx_j (j : J) : Measurable (fun x => idx x j) := by
    intro s hs
    have h_countable : s.Countable := Set.Countable.mono (Set.subset_univ s) Set.countable_univ
    have h_eq : (fun x => idx x j) ⁻¹' s = ⋃ n ∈ s, (fun x => idx x j) ⁻¹' {n} := by
      ext x; simp
    rw [h_eq]
    refine MeasurableSet.biUnion h_countable (fun n hn => ?_)
    exact hidx j n
  have hF_meas : Measurable F := by
    refine Measurable.prodMk measurable_fst ?_
    refine Measurable.of_eval (fun j => ?_)
    -- Goal: Measurable (fun p : X × (ℕ → E) => p.2 (idx p.1 j))
    -- Write as composition: (x, y) ↦ (idx x j, y) then (n, y) ↦ y n
    have h1 : Measurable (fun (p : X × (ℕ → E)) => (idx p.1 j, p.2)) :=
      Measurable.prodMk ((h_meas_idx_j j).comp measurable_fst) measurable_snd
    have h2 : Measurable (fun (q : ℕ × (ℕ → E)) => q.2 q.1) := by
      intro s hs
      have h_eq : (fun (q : ℕ × (ℕ → E)) => q.2 q.1) ⁻¹' s = ⋃ n : ℕ, {n} ×ˢ ((fun f : ℕ → E => f n) ⁻¹' s) := by
        ext ⟨n, y⟩; simp
      rw [h_eq]
      refine MeasurableSet.iUnion (fun n => ?_)
      exact (measurableSet_singleton n).prod ((measurable_pi_apply n) hs)
    exact h2.comp h1
  -- Now use Measure.ext to compare on measurable sets
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hF_meas hA]
  have hmeas_FinvA : MeasurableSet (F⁻¹' A) := hF_meas hA
  rw [Measure.prod_apply hmeas_FinvA, Measure.prod_apply hA]
  -- ∫⁻ x, ν_ℕ (Prod.mk x ⁻¹' (F⁻¹' A)) ∂μ = ∫⁻ x, ν_J (Prod.mk x ⁻¹' A) ∂μ
  refine lintegral_congr_ae ?_
  filter_upwards [hinj] with x hx_inj
  -- Need: ν_ℕ (Prod.mk x ⁻¹' (F⁻¹' A)) = ν_J (Prod.mk x ⁻¹' A)
  have h_set : Prod.mk x ⁻¹' (F⁻¹' A) = (fun y => y ∘ idx x) ⁻¹' (Prod.mk x ⁻¹' A) := by
    ext y
    rfl
  rw [h_set]
  have h_meas_section : MeasurableSet (Prod.mk x ⁻¹' A) :=
    hA.preimage (measurable_prodMk_left (x := x))
  rw [← Measure.map_apply ?_ h_meas_section]
  · -- Now: (ν_ℕ.map (fun y => y ∘ idx x)) (Prod.mk x ⁻¹' A) = ν_J (Prod.mk x ⁻¹' A)
    have h_map_eq : ν_ℕ.map (fun y : ℕ → E => y ∘ idx x) = ν_J := by
      dsimp [ν_ℕ, ν_J]
      have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ => ν) hx_inj
      -- h : (infinitePi (fun _ => ν)).map (fun ω i => ω (idx x i)) = infinitePi (fun i => ν)
      -- We need to rewrite (fun ω i => ω (idx x i)) to (fun y => y ∘ idx x)
      simpa [Function.comp_def] using h
    rw [h_map_eq]
  · -- Need to show that (fun y => y ∘ idx x) is measurable
    refine Measurable.of_eval (fun j => ?_)
    -- Goal: Measurable (fun y : ℕ → E => (fun y' => y' ∘ idx x) y j)
    -- = Measurable (fun y => (y ∘ idx x) j)
    -- = Measurable (fun y => y (idx x j))
    exact measurable_pi_apply (idx x j)

/-- Two finite measures on `X × (ℕ → E)` agreeing on the sets `A × {v | ∀ i < n, v i ∈ D i}` are
equal. -/
theorem prod_ext_box {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (ρ ρ' : Measure (X × (ℕ → E))) [IsFiniteMeasure ρ] [IsFiniteMeasure ρ']
    (h : ∀ A : Set X, MeasurableSet A → ∀ D : ℕ → Set E, (∀ i, MeasurableSet (D i)) → ∀ n : ℕ,
      ρ (A ×ˢ {v | ∀ i < n, v i ∈ D i}) = ρ' (A ×ˢ {v | ∀ i < n, v i ∈ D i})) : ρ = ρ' := by
  -- First, ρ univ = ρ' univ follows from the hypothesis with A = univ, n = 0
  have h_univ : ρ Set.univ = ρ' Set.univ := by
    have h0 := h Set.univ MeasurableSet.univ (fun _ => Set.univ) (fun _ => MeasurableSet.univ) 0
    simpa using h0
  -- Define the collection C of boxes
  set C : Set (Set (X × (ℕ → E))) := {s | ∃ (A : Set X) (_ : MeasurableSet A) (D : ℕ → Set E)
    (_ : ∀ i, MeasurableSet (D i)) (n : ℕ), s = A ×ˢ {v | ∀ i < n, v i ∈ D i}} with hC
  -- Helper lemma: intersection of two cylinder conditions
  have h_inter_lemma : ∀ (D : ℕ → Set E) (n : ℕ) (D' : ℕ → Set E) (n' : ℕ) (v : ℕ → E),
    ((∀ i, i < n → v i ∈ D i) ∧ (∀ i, i < n' → v i ∈ D' i)) ↔
    (∀ i, i < max n n' → v i ∈ ((if i < n then D i else Set.univ) ∩ (if i < n' then D' i else Set.univ))) := by
    intro D n D' n' v
    constructor
    · intro ⟨h1, h2⟩ i hi
      by_cases hi_n : i < n
      · have hD_i : v i ∈ D i := h1 i hi_n
        have hD'_i : v i ∈ (if i < n' then D' i else Set.univ) := by
          by_cases hi_n' : i < n'
          · have := h2 i hi_n'
            simpa [hi_n'] using this
          · simp [hi_n']
        have hD_i' : v i ∈ (if i < n then D i else Set.univ) := by simpa [hi_n]
        exact Set.mem_inter hD_i' hD'_i
      · have hi_n' : i < n' := by
          by_contra! H
          have hmax : max n n' ≤ i := by
            apply Nat.max_le.mpr
            exact ⟨by omega, by omega⟩
          omega
        have hD_i : v i ∈ (if i < n then D i else Set.univ) := by simp [hi_n]
        have hD'_i : v i ∈ D' i := h2 i hi_n'
        have hD'_i' : v i ∈ (if i < n' then D' i else Set.univ) := by simpa [hi_n'] using hD'_i
        exact Set.mem_inter hD_i hD'_i'
    · intro h
      constructor
      · intro i hi_n
        have hi_max : i < max n n' := lt_max_of_lt_left hi_n
        have h_i := h i hi_max
        have hD_i := h_i.1
        simpa [hi_n] using hD_i
      · intro i hi_n'
        have hi_max : i < max n n' := lt_max_of_lt_right hi_n'
        have h_i := h i hi_max
        have hD'_i := h_i.2
        simpa [hi_n'] using hD'_i
  -- C is a π-system
  have hC_pi : IsPiSystem C := by
    dsimp [C, IsPiSystem]
    intro s hs t ht hne
    rcases hs with ⟨A, hA, D, hD, n, hs_eq⟩
    rcases ht with ⟨A', hA', D', hD', n', ht_eq⟩
    rw [hs_eq, ht_eq]
    rw [Set.prod_inter_prod]
    -- (A ∩ A') ×ˢ ({v | ∀ i < n, v i ∈ D i} ∩ {v | ∀ i < n', v i ∈ D' i})
    have h_inter_set : {v : ℕ → E | ∀ i < n, v i ∈ D i} ∩ {v : ℕ → E | ∀ i < n', v i ∈ D' i} =
        {v : ℕ → E | ∀ i < max n n', v i ∈ ((if i < n then D i else Set.univ) ∩ (if i < n' then D' i else Set.univ))} := by
      ext v
      simp [h_inter_lemma D n D' n' v]
    rw [h_inter_set]
    set D'' := fun (i : ℕ) => (if i < n then D i else Set.univ) ∩ (if i < n' then D' i else Set.univ) with hD''
    have hD''_meas : ∀ i, MeasurableSet (D'' i) := by
      intro i
      dsimp [D'']
      by_cases hi : i < n
      · by_cases hi' : i < n'
        · have h1 : MeasurableSet (if i < n then D i else Set.univ) := by simpa [hi] using hD i
          have h2 : MeasurableSet (if i < n' then D' i else Set.univ) := by simpa [hi'] using hD' i
          exact MeasurableSet.inter h1 h2
        · have h1 : MeasurableSet (if i < n then D i else Set.univ) := by simpa [hi] using hD i
          have h2 : MeasurableSet (if i < n' then D' i else Set.univ) := by simpa [hi'] using MeasurableSet.univ
          exact MeasurableSet.inter h1 h2
      · by_cases hi' : i < n'
        · have h1 : MeasurableSet (if i < n then D i else Set.univ) := by simpa [hi] using MeasurableSet.univ
          have h2 : MeasurableSet (if i < n' then D' i else Set.univ) := by simpa [hi'] using hD' i
          exact MeasurableSet.inter h1 h2
        · have h1 : MeasurableSet (if i < n then D i else Set.univ) := by simpa [hi] using MeasurableSet.univ
          have h2 : MeasurableSet (if i < n' then D' i else Set.univ) := by simpa [hi'] using MeasurableSet.univ
          exact MeasurableSet.inter h1 h2
    refine ⟨A ∩ A', MeasurableSet.inter hA hA', D'', hD''_meas, max n n', ?_⟩
    rfl
  -- Every set in C is measurable in the product σ-algebra
  have hC_meas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rcases hs with ⟨A, hA, D, hD, n, hs_eq⟩
    rw [hs_eq]
    apply MeasurableSet.prod hA
    -- Need to show {v | ∀ i < n, v i ∈ D i} is measurable
    -- This is a finite intersection of measurable sets {v | v i ∈ D i}
    -- Each {v | v i ∈ D i} is measurable because it's a cylinder
    have : {v : ℕ → E | ∀ i < n, v i ∈ D i} = ⋂ i ∈ Finset.Iio n, {v : ℕ → E | v i ∈ D i} := by
      ext (v : ℕ → E)
      simp [Set.mem_iInter, Finset.mem_Iio]
    rw [this]
    refine Finset.measurableSet_biInter _ (fun i hi => ?_)
    -- {v | v i ∈ D i} is the preimage of D i under the projection map, which is measurable
    have h_proj : Measurable fun (v : ℕ → E) => v i := by
      apply measurable_pi_apply i
    exact h_proj (hD i)
  -- The σ-algebra generated by C equals the product σ-algebra
  have h_generate : MeasurableSpace.generateFrom C = Prod.instMeasurableSpace := by
    apply le_antisymm
    · -- generateFrom C ≤ Prod.instMeasurableSpace
      apply MeasurableSpace.generateFrom_le
      intro s hs
      exact hC_meas s hs
    · -- Prod.instMeasurableSpace ≤ generateFrom C
      -- By generateFrom_prod, the product σ-algebra is generated by rectangles A ×ˢ B
      rw [← generateFrom_prod]
      -- Goal: generateFrom (image2 (×ˢ) {s | MeasurableSet s} {t | MeasurableSet t}) ≤ generateFrom C
      -- By generateFrom_le, it suffices to show that every set in the image is in generateFrom C
      apply MeasurableSpace.generateFrom_le
      intro s hs
      rcases Set.mem_image2.mp hs with ⟨A, hA_meas, B, hB_meas, hs_eq⟩
      -- hs_eq : A ×ˢ B = s
      -- Goal: MeasurableSet[generateFrom C] s
      rw [← hs_eq]
      -- Goal: MeasurableSet[generateFrom C] (A ×ˢ B)
      -- Write A ×ˢ B = (A ×ˢ univ) ∩ (univ ×ˢ B)
      -- A ×ˢ univ is a box, so in C, hence measurable
      -- univ ×ˢ B: need to show this is measurable in generateFrom C
      let G : Set (Set (ℕ → E)) := {B | ∃ (i : ℕ) (A : Set E), MeasurableSet A ∧ B = {v | v i ∈ A}}
      have h_pi_eq : MeasurableSpace.generateFrom G = MeasurableSpace.pi := by
        rw [MeasurableSpace.pi_eq_generateFrom_projections]
        apply congrArg MeasurableSpace.generateFrom
        ext B
        simp [G, Function.eval, Set.mem_setOf_eq, Set.ext_iff, eq_comm]
      have h_gen_in : ∀ B ∈ G, MeasurableSet[MeasurableSpace.generateFrom C] ((Set.univ : Set X) ×ˢ B) := by
        rintro B ⟨i, A, hA, rfl⟩
        have h_in_C : (Set.univ : Set X) ×ˢ {v : ℕ → E | v i ∈ A} ∈ C := by
          dsimp [C]
          refine ⟨Set.univ, MeasurableSet.univ, fun j => if j = i then A else Set.univ, ?_, i+1, ?_⟩
          · intro j
            by_cases h : j = i
            · simpa [h] using hA
            · simp [h]
          · ext ⟨x, v⟩
            simp
            constructor
            · intro h j hj
              by_cases hji : j = i
              · simpa [hji] using h
              · simp [hji]
            · intro h
              have := h i (by omega)
              simpa using this
        simpa using MeasurableSpace.measurableSet_generateFrom h_in_C
      have h_all : ∀ B, MeasurableSet B → MeasurableSet[MeasurableSpace.generateFrom C] ((Set.univ : Set X) ×ˢ B) := by
        -- Use the fact that MeasurableSpace.pi = generateFrom G
        -- and that generateFrom G ≤ generateFrom C (via the pullback)
        -- Actually, we can use generateFrom_induction on G with the current MeasurableSpace (which is MeasurableSpace.pi)
        -- But the goal is about MeasurableSet[generateFrom C], not the current σ-algebra
        -- So we need to be careful
        -- Let's use a different approach: since G generates MeasurableSpace.pi,
        -- every measurable set B is in generateFrom G.
        -- And we know that for all B ∈ G, univ ×ˢ B ∈ generateFrom C.
        -- We want to show that for all B with MeasurableSet B, univ ×ˢ B ∈ generateFrom C.
        -- This follows by induction on generateFrom G.
        intro B hB
        -- hB : MeasurableSet B (in MeasurableSpace.pi)
        -- We use the induction principle on generateFrom G
        -- But the induction principle expects the current MeasurableSpace to be generateFrom G
        -- Let's change the MeasurableSpace instance temporarily
        -- Actually, we can use `h_pi_eq` to rewrite
        have hB' : MeasurableSet[MeasurableSpace.generateFrom G] B := by
          rw [h_pi_eq]
          exact hB
        -- Now we can use generateFrom_induction on G
        refine MeasurableSpace.generateFrom_induction G
          (fun B _ => MeasurableSet[MeasurableSpace.generateFrom C] ((Set.univ : Set X) ×ˢ B))
          ?_ ?_ ?_ ?_ B hB'
        · -- generators
          intro B hB hBmeas
          simpa using h_gen_in B hB
        · -- empty set
          simp
        · -- complement
          intro B hBmeas hB_in
          have h_univ : MeasurableSet[MeasurableSpace.generateFrom C] ((Set.univ : Set X) ×ˢ (Set.univ : Set (ℕ → E))) := by
            have h : (Set.univ : Set X) ×ˢ (Set.univ : Set (ℕ → E)) ∈ C := by
              dsimp [C]
              refine ⟨Set.univ, MeasurableSet.univ, fun _ => Set.univ, fun _ => MeasurableSet.univ, 0, ?_⟩
              simp
            exact MeasurableSpace.measurableSet_generateFrom h
          have h_compl : MeasurableSet[MeasurableSpace.generateFrom C] (((Set.univ : Set X) ×ˢ B)ᶜ) :=
            hB_in.compl
          have h_inter : MeasurableSet[MeasurableSpace.generateFrom C] (((Set.univ : Set X) ×ˢ (Set.univ : Set (ℕ → E))) ∩ ((Set.univ : Set X) ×ˢ B)ᶜ) :=
            MeasurableSet.inter h_univ h_compl
          have h_eq : ((Set.univ : Set X) ×ˢ (Set.univ : Set (ℕ → E))) ∩ ((Set.univ : Set X) ×ˢ B)ᶜ =
              (Set.univ : Set X) ×ˢ (Bᶜ : Set (ℕ → E)) := by
            ext ⟨x, v⟩
            simp [Set.mem_inter_iff, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ]
          rw [h_eq] at h_inter
          exact h_inter
        · -- countable union
          intro f hfmeas hf_in
          rw [Set.prod_iUnion]
          apply MeasurableSet.iUnion
          intro n
          exact hf_in n
      -- Now prove that s = A ×ˢ B is in generateFrom C
      -- The goal is MeasurableSet[generateFrom C] s, which is MeasurableSet (A ×ˢ B) after rewriting
      -- But hs_eq : A ×ˢ B = s, so we can rewrite
      have hA_box : A ×ˢ (Set.univ : Set (ℕ → E)) ∈ C := by
        dsimp [C]
        refine ⟨A, hA_meas, fun _ => Set.univ, fun _ => MeasurableSet.univ, 0, ?_⟩
        simp
      have hA_box' : MeasurableSet[MeasurableSpace.generateFrom C] (A ×ˢ (Set.univ : Set (ℕ → E))) :=
        MeasurableSpace.measurableSet_generateFrom hA_box
      have hB' : MeasurableSet[MeasurableSpace.generateFrom C] ((Set.univ : Set X) ×ˢ B) := h_all B hB_meas
      -- A ×ˢ B = (A ×ˢ univ) ∩ (univ ×ˢ B)
      have h_eq : A ×ˢ B = (A ×ˢ (Set.univ : Set (ℕ → E))) ∩ ((Set.univ : Set X) ×ˢ B) := by
        ext ⟨x, v⟩
        simp [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ]
      rw [h_eq]
      apply MeasurableSet.inter hA_box' hB'
  -- Now apply ext_of_generate_finite
  refine MeasureTheory.ext_of_generate_finite C h_generate.symm hC_pi ?_ h_univ
  intro s hs
  rcases hs with ⟨A, hA, D, hD, n, hs_eq⟩
  rw [hs_eq]
  exact h A hA D hD n

/-- A measurable event invariant under changing the coordinate `u` is independent of that
coordinate. -/
theorem infinitePi_inter_eval {U E : Type*} [DecidableEq U] [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (u : U) (S : Set (U → E)) (hS : MeasurableSet S)
    (hinv : ∀ (ω : U → E) (e : E), Function.update ω u e ∈ S ↔ ω ∈ S) (D : Set E)
    (hD : MeasurableSet D) :
    Measure.infinitePi (fun _ : U => ν) (S ∩ {ω | ω u ∈ D}) =
      Measure.infinitePi (fun _ : U => ν) S * ν D := by
  have hE : Nonempty E := nonempty_of_isProbabilityMeasure ν
  obtain ⟨e₀⟩ := hE
  let I : Set U := {v | v ≠ u}
  let r : (U → E) → (I → E) := fun ω v => ω v.1
  have hr_eq : r = I.domRestrict := by
    ext ω v
    simp [r, Set.domRestrict]
  let ext : (I → E) → (U → E) := fun z v => if h : v = u then e₀ else z ⟨v, h⟩
  have h_ext_r : ∀ ω, ext (r ω) = Function.update ω u e₀ := by
    intro ω; ext v; simp [ext, r, Function.update_apply]
  have h_ext_meas : Measurable ext := by
    refine measurable_pi_iff.mpr fun v => ?_
    by_cases hv : v = u
    · subst hv; simp [ext]
    · simp [ext, hv, measurable_pi_apply]
  have h_r_meas : Measurable r := by
    refine measurable_pi_iff.mpr fun v => ?_
    simp [r, measurable_pi_apply]
  let S' : Set (I → E) := ext ⁻¹' S
  have hS'_meas : MeasurableSet S' := hS.preimage h_ext_meas
  have hS_eq : S = r ⁻¹' S' := by
    ext ω
    simp [S', r, h_ext_r, hinv]
  have h_phi_meas : Measurable (fun ω : U → E => (r ω, ω u)) := by
    refine Measurable.prodMk h_r_meas (measurable_pi_apply (a := u))
  have h_preimage : (fun ω : U → E => (r ω, ω u)) ⁻¹' (S' ×ˢ D) = S ∩ {ω | ω u ∈ D} := by
    ext ω
    constructor
    · rintro ⟨hS', hD'⟩
      have h_mem : ext (r ω) ∈ S := by simpa [S'] using hS'
      rw [h_ext_r] at h_mem
      exact ⟨((hinv ω e₀).mp h_mem), hD'⟩
    · rintro ⟨hS_mem, hD_mem⟩
      have h_ext_mem : ext (r ω) ∈ S := by
        rw [h_ext_r]
        exact ((hinv ω e₀).mpr hS_mem)
      have h_r_mem : r ω ∈ S' := by
        simpa [S'] using h_ext_mem
      exact ⟨h_r_mem, hD_mem⟩
  have h_map_pair := FrogModel.Recursion.map_infinitePi_pair (P := fun _ : U => ν)
    (f := fun (v : I) => (v : U)) (g := fun (_ : Unit) => u)
    (hf := Subtype.val_injective) (hg := fun _ _ => by simp) (hfg := fun a b => a.2)
  have h_map_prod_map : ((Measure.infinitePi (fun _ : I => ν)).prod
      (Measure.infinitePi (fun _ : Unit => ν))).map
      (Prod.map (id : (I → E) → (I → E)) (fun (z : Unit → E) => z ())) =
      (Measure.infinitePi (fun _ : I => ν)).prod ν := by
    have h_id_meas : Measurable (id : (I → E) → (I → E)) := measurable_id
    have h_eval_meas : Measurable (fun (z : Unit → E) => z ()) :=
      measurable_pi_apply (a := ())
    rw [← Measure.map_prod_map _ _ h_id_meas h_eval_meas, Measure.map_id,
      Measure.infinitePi_map_eval (μ := fun (_ : Unit) => ν) (i := ())]
  have h_phi_map : (Measure.infinitePi (fun _ : U => ν)).map
      (fun ω : U → E => (r ω, ω u)) =
      (Measure.infinitePi (fun _ : I => ν)).prod ν := by
    let f := fun ω : U → E => (fun a : I => ω a.1, fun (_ : Unit) => ω u)
    let g := Prod.map (id : (I → E) → (I → E)) (fun (z : Unit → E) => z ())
    have h_eq_map : (fun ω : U → E => (r ω, ω u)) = g ∘ f := by
      ext ω
      dsimp [f, g, r]
      rfl
    have hf_meas : Measurable f := by
      refine Measurable.prodMk ?_ ?_
      · refine measurable_pi_iff.mpr fun a => ?_
        simp [measurable_pi_apply]
      · refine measurable_pi_iff.mpr fun b => ?_
        simp [measurable_pi_apply]
    have hg_meas : Measurable g :=
      Measurable.prodMap measurable_id (measurable_pi_apply (a := ()))
    rw [h_eq_map, ← Measure.map_map hg_meas hf_meas, h_map_pair, h_map_prod_map]
  have h_infinitePi_map_restrict : (Measure.infinitePi (fun _ : U => ν)).map r =
      Measure.infinitePi (fun _ : I => ν) := by
    rw [hr_eq, Measure.infinitePi_map_restrict' (μ := fun _ : U => ν) (I := I)]
  calc
    Measure.infinitePi (fun _ : U => ν) (S ∩ {ω | ω u ∈ D})
        = Measure.infinitePi (fun _ : U => ν)
            ((fun ω : U → E => (r ω, ω u)) ⁻¹' (S' ×ˢ D)) := by rw [h_preimage]
    _ = ((Measure.infinitePi (fun _ : U => ν)).map
        (fun ω : U → E => (r ω, ω u))) (S' ×ˢ D) := by
      rw [Measure.map_apply h_phi_meas (hS'_meas.prod hD)]
    _ = ((Measure.infinitePi (fun _ : I => ν)).prod ν) (S' ×ˢ D) := by rw [h_phi_map]
    _ = (Measure.infinitePi (fun _ : I => ν) S') * ν D := by rw [Measure.prod_prod]
    _ = ((Measure.infinitePi (fun _ : U => ν)).map r) S' * ν D := by
      rw [h_infinitePi_map_restrict]
    _ = Measure.infinitePi (fun _ : U => ν) (r ⁻¹' S') * ν D := by
      rw [Measure.map_apply h_r_meas hS'_meas]
    _ = Measure.infinitePi (fun _ : U => ν) S * ν D := by rw [hS_eq]

/-- Adaptive reading: changing the coordinate read at step `n` does not change the coordinates
read at steps `0, ..., n`. -/
theorem choice_update {U E : Type*} [DecidableEq U] (isParam : U → Prop)
    (choice : ℕ → (U → E) → U) (hinj : ∀ ω, Function.Injective fun k => choice k ω)
    (hadapt : ∀ k (ω ω' : U → E), (∀ u, isParam u → ω' u = ω u) →
      (∀ i < k, ω' (choice i ω) = ω (choice i ω)) → choice k ω' = choice k ω)
    (u : U) (hu : ¬ isParam u) (ω : U → E) (e : E) (n : ℕ) (hn : choice n ω = u) :
    ∀ i ≤ n, choice i (Function.update ω u e) = choice i ω := by
  intro i hi
  let ω' := Function.update ω u e
  have hparam : ∀ v, isParam v → ω' v = ω v := by
    intro v hv
    apply Function.update_of_ne
    intro hveq
    rw [hveq] at hv
    exact hu hv
  have hearlier : ∀ j < i, ω' (choice j ω) = ω (choice j ω) := by
    intro j hj
    apply Function.update_of_ne
    intro hceq
    have h_eq : choice j ω = choice n ω := by
      rw [hceq, ← hn]
    have : j = n := hinj ω h_eq
    linarith
  exact hadapt i ω ω' hparam (fun j hj => hearlier j hj)

/-- Reading a coordinate chosen measurably among countably many is measurable. -/
theorem measurable_read {U E : Type*} [Countable U] [MeasurableSpace E]
    (choice : (U → E) → U) (hmeas : ∀ u, MeasurableSet {ω | choice ω = u}) :
    Measurable fun ω : U → E => ω (choice ω) := by
  intro s hs
  have h_cover : (fun ω : U → E => ω (choice ω)) ⁻¹' s = ⋃ u, {ω | choice ω = u} ∩ {ω | ω u ∈ s} := by
    ext ω
    constructor
    · intro h
      refine Set.mem_iUnion.mpr ⟨choice ω, ?_⟩
      refine ((Set.mem_inter_iff _ _ _).mpr ⟨?_, ?_⟩)
      · rfl
      · simpa
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨u, hu⟩
      rcases (Set.mem_inter_iff _ _ _).mp hu with ⟨hcu, hu_s⟩
      have hcu' : choice ω = u := hcu
      have hu_s' : ω u ∈ s := hu_s
      simpa [hcu'] using hu_s'
  rw [h_cover]
  refine MeasurableSet.iUnion ?_
  intro u
  refine (hmeas u).inter ?_
  exact (measurable_pi_apply u) hs

/-- **Adaptive reading, boxes.** -/
theorem adapted_box {U E : Type*} [Countable U] [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (isParam : U → Prop) (choice : ℕ → (U → E) → U)
    (hroot : ∀ k ω, ¬ isParam (choice k ω)) (hinj : ∀ ω, Function.Injective fun k => choice k ω)
    (hadapt : ∀ k (ω ω' : U → E), (∀ u, isParam u → ω' u = ω u) →
      (∀ i < k, ω' (choice i ω) = ω (choice i ω)) → choice k ω' = choice k ω)
    (hmeas : ∀ k u, MeasurableSet {ω | choice k ω = u}) (A : Set ({u // isParam u} → E))
    (hA : MeasurableSet A) (D : ℕ → Set E) (hD : ∀ i, MeasurableSet (D i)) (n : ℕ) :
    Measure.infinitePi (fun _ : U => ν)
        {ω | (fun u : {u // isParam u} => ω u) ∈ A ∧ ∀ i < n, ω (choice i ω) ∈ D i} =
      Measure.infinitePi (fun _ : {u // isParam u} => ν) A * ∏ i ∈ Finset.range n, ν (D i) := by
  classical
    let μ := Measure.infinitePi (fun _ : U => ν)
    have h_map_eq : μ.map (fun (ω : U → E) (u : {u // isParam u}) => ω u) =
        Measure.infinitePi (fun _ : {u // isParam u} => ν) := by
      have hinj_subtype : Function.Injective (fun (u : {u // isParam u}) => (u : U)) :=
        Subtype.val_injective
      simpa [μ] using MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj
        (f := Subtype.val) hinj_subtype
    induction' n with n ih
    · have hmeas_restrict : Measurable (fun (ω : U → E) (u : {u // isParam u}) => ω u) :=
        measurable_pi_lambda fun u => measurable_pi_apply u.val
      simp
      calc
        μ {ω | (fun u : {u // isParam u} => ω u) ∈ A} =
            μ ((fun (ω : U → E) (u : {u // isParam u}) => ω u) ⁻¹' A) := rfl
        _ = (μ.map (fun (ω : U → E) (u : {u // isParam u}) => ω u)) A := by
          rw [Measure.map_apply hmeas_restrict hA]
        _ = Measure.infinitePi (fun _ : {u // isParam u} => ν) A := by rw [h_map_eq]
    · let B : Set (U → E) := {ω : U → E | (fun u : {u // isParam u} => ω u) ∈ A ∧ ∀ i < n, ω (choice i ω) ∈ D i}
      have hB_meas : MeasurableSet B := by
        dsimp [B]
        have h1 : MeasurableSet {ω : U → E | (fun u : {u // isParam u} => ω u) ∈ A} :=
          hA.preimage (measurable_pi_lambda fun u => measurable_pi_apply u.val)
        have h2 : MeasurableSet {ω : U → E | ∀ i < n, ω (choice i ω) ∈ D i} := by
          have : {ω : U → E | ∀ i < n, ω (choice i ω) ∈ D i} = ⋂ i ∈ Finset.range n, {ω : U → E | ω (choice i ω) ∈ D i} := by
            ext ω; simp [Finset.mem_range]
          rw [this]
          refine MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_
          have hmeas_read_i : Measurable (fun ω : U → E => ω (choice i ω)) :=
            FrogModel.Recursion.measurable_read (choice i) (hmeas i)
          exact (hD i).preimage hmeas_read_i
        exact MeasurableSet.inter h1 h2
      have h_choice_meas : ∀ u, MeasurableSet (B ∩ {ω | choice n ω = u}) := by
        intro u; exact MeasurableSet.inter hB_meas (hmeas n u)
      have h_disjoint : Pairwise (Function.onFun Disjoint fun (x : U) => B ∩ {ω | choice n ω = x}) := by
        intro x y hxy
        have : Disjoint (B ∩ {ω | choice n ω = x}) (B ∩ {ω | choice n ω = y}) := by
          refine Set.disjoint_iff_inter_eq_empty.mpr ?_
          ext ω; simp
          intro _ h1 _ h2
          exact hxy (h1.symm ▸ h2)
        exact this
      have h_invariant : ∀ (u : U) (ω : U → E) (e : E),
          Function.update ω u e ∈ (B ∩ {ω | choice n ω = u}) ↔ ω ∈ (B ∩ {ω | choice n ω = u}) := by
        intro u ω e
        by_cases hu : isParam u
        · have h_empty : B ∩ {ω | choice n ω = u} = ∅ := by
            ext ω; constructor
            · rintro ⟨hB_ω, h_choice⟩
              exfalso
              apply hroot n ω
              rw [h_choice]
              exact hu
            · intro h; simp at h
          simp [h_empty]
        · -- Helper lemma: forward direction (independent of e)
          have h_forward_gen : ∀ (e : E) (ω' : U → E), choice n ω' = u → ω' ∈ B →
              Function.update ω' u e ∈ (B ∩ {ω | choice n ω = u}) := by
            intro e' ω' h_choice' hB_ω'
            have hB_ω'_def : (fun v : {u // isParam u} => ω' v.val) ∈ A ∧ ∀ i < n, ω' (choice i ω') ∈ D i := by
              simpa [B] using hB_ω'
            rcases hB_ω'_def with ⟨hA_ω', h_reads_ω'⟩
            have h_choice_update : ∀ i ≤ n, choice i (Function.update ω' u e') = choice i ω' :=
              FrogModel.Recursion.choice_update isParam choice hinj hadapt u hu ω' e' n h_choice'
            have h_ne_u' : ∀ (v : {u // isParam u}), u ≠ v.val := by
              intro v
              intro h_eq
              apply hu
              have : isParam v.val := v.property
              rw [← h_eq] at this
              exact this
            have h_par : (fun v : {u // isParam u} => (Function.update ω' u e') v.val) ∈ A := by
              have h_eq : (fun v : {u // isParam u} => (Function.update ω' u e') v.val) =
                  (fun v : {u // isParam u} => ω' v.val) := by
                refine funext fun w => ?_
                exact Function.update_of_ne ((h_ne_u' w).symm) e' ω'
              rw [h_eq]
              exact hA_ω'
            have h_reads : ∀ i < n, (Function.update ω' u e') (choice i (Function.update ω' u e')) ∈ D i := by
              intro i hi
              rw [h_choice_update i (Nat.le_of_lt hi)]
              have h_ne : choice i ω' ≠ u := by
                intro h_eq'
                have : i = n := hinj ω' (h_eq'.trans h_choice'.symm)
                exact Nat.ne_of_lt hi this
              rw [Function.update_of_ne h_ne]
              exact h_reads_ω' i hi
            have h_choice_n : choice n (Function.update ω' u e') = u := by
              rw [h_choice_update n (le_refl n), h_choice']
            have hB_update : Function.update ω' u e' ∈ B := by
              dsimp [B]
              exact ⟨h_par, h_reads⟩
            exact ⟨hB_update, h_choice_n⟩
          constructor
          · intro h
            rcases h with ⟨hB_ω, h_choice⟩
            have h_choice_ω₁ : choice n (Function.update ω u e) = u := h_choice
            have hB_ω₁ : Function.update ω u e ∈ B := hB_ω
            have h_result := h_forward_gen (ω u) (Function.update ω u e) h_choice_ω₁ hB_ω₁
            have h_update_idem : Function.update (Function.update ω u e) u (ω u) = ω := by
              rw [Function.update_idem, Function.update_eq_self]
            rwa [h_update_idem] at h_result
          · intro h
            rcases h with ⟨hB_ω, h_choice⟩
            exact h_forward_gen e ω h_choice hB_ω
      have h_set_eq : {ω : U → E | (fun u : {u // isParam u} => ω u) ∈ A ∧ ∀ i < n + 1, ω (choice i ω) ∈ D i} =
          ⋃ u, (B ∩ {ω | choice n ω = u}) ∩ {ω | ω u ∈ D n} := by
        ext ω; constructor
        · intro hω
          rcases hω with ⟨hA_ω, h_reads⟩
          have h_reads_n : ω (choice n ω) ∈ D n := h_reads n (Nat.lt_succ_self n)
          have h_reads_lt : ∀ i < n, ω (choice i ω) ∈ D i := by
            intro i hi
            exact h_reads i (Nat.lt_succ_of_lt hi)
          have hB_ω : ω ∈ B := by
            dsimp [B]
            exact ⟨hA_ω, h_reads_lt⟩
          apply Set.mem_iUnion.mpr
          refine ⟨choice n ω, ?_, h_reads_n⟩
          exact ⟨hB_ω, rfl⟩
        · intro h
          rcases Set.mem_iUnion.mp h with ⟨u, hω⟩
          rcases hω with ⟨hω_inter, h_read_n⟩
          rcases hω_inter with ⟨hB_ω, h_choice⟩
          have hB_ω' : (fun v : {u // isParam u} => ω v.val) ∈ A ∧ ∀ i < n, ω (choice i ω) ∈ D i := by
            simpa [B] using hB_ω
          have hA_ω : (fun v : {u // isParam u} => ω v.val) ∈ A := hB_ω'.1
          have h_reads_lt : ∀ i < n, ω (choice i ω) ∈ D i := hB_ω'.2
          refine ⟨hA_ω, fun i hi => ?_⟩
          have hi' : i < n ∨ i = n := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
          rcases hi' with (h | h)
          · exact h_reads_lt i h
          · rw [h]; rw [← h_choice] at h_read_n; exact h_read_n
      have h_disjoint' : Pairwise (Function.onFun Disjoint fun (u : U) =>
          (B ∩ {ω | choice n ω = u}) ∩ {ω | ω u ∈ D n}) := by
        intro u v huv
        have hd := h_disjoint huv
        have hsub1 : (B ∩ {ω | choice n ω = u}) ∩ {ω | ω u ∈ D n} ≤ B ∩ {ω | choice n ω = u} :=
          fun x hx => hx.1
        have hsub2 : (B ∩ {ω | choice n ω = v}) ∩ {ω | ω v ∈ D n} ≤ B ∩ {ω | choice n ω = v} :=
          fun x hx => hx.1
        exact Disjoint.mono hsub1 hsub2 hd
      have h_choice_meas' : ∀ u, MeasurableSet ((B ∩ {ω | choice n ω = u}) ∩ {ω | ω u ∈ D n}) := by
        intro u
        refine MeasurableSet.inter (h_choice_meas u) ?_
        have hmeas_eval : Measurable (fun (ω : U → E) => ω u) := by fun_prop
        exact (hD n).preimage hmeas_eval
      have h_cover : B = ⋃ u, B ∩ {ω | choice n ω = u} := by
        ext ω; constructor
        · intro hω; refine Set.mem_iUnion.mpr ⟨choice n ω, hω, rfl⟩
        · intro h; rcases Set.mem_iUnion.mp h with ⟨u, hω⟩; exact hω.1
      calc
        μ {ω | (fun u : {u // isParam u} => ω u) ∈ A ∧ ∀ i < n + 1, ω (choice i ω) ∈ D i} =
            μ (⋃ u, (B ∩ {ω | choice n ω = u}) ∩ {ω | ω u ∈ D n}) := by rw [h_set_eq]
        _ = ∑' u, μ ((B ∩ {ω | choice n ω = u}) ∩ {ω | ω u ∈ D n}) := by
          rw [MeasureTheory.measure_iUnion h_disjoint' h_choice_meas']
        _ = ∑' u, (μ (B ∩ {ω | choice n ω = u}) * ν (D n)) := by
          refine tsum_congr fun u => ?_
          rw [FrogModel.Recursion.infinitePi_inter_eval ν u (B ∩ {ω | choice n ω = u})
            (h_choice_meas u) (h_invariant u) (D n) (hD n)]
        _ = (∑' u, μ (B ∩ {ω | choice n ω = u})) * ν (D n) := by rw [ENNReal.tsum_mul_right]
        _ = μ B * ν (D n) := by
          have hsum : (∑' u, μ (B ∩ {ω | choice n ω = u})) = μ B := by
            rw [← MeasureTheory.measure_iUnion h_disjoint h_choice_meas, ← h_cover]
          rw [hsum]
        _ = μ {ω | (fun u : {u // isParam u} => ω u) ∈ A ∧ ∀ i < n, ω (choice i ω) ∈ D i} * ν (D n) := by dsimp [B]
        _ = (Measure.infinitePi (fun _ : {u // isParam u} => ν) A * ∏ i ∈ Finset.range n, ν (D i)) * ν (D n) := by rw [ih]
        _ = Measure.infinitePi (fun _ : {u // isParam u} => ν) A * ((∏ i ∈ Finset.range n, ν (D i)) * ν (D n)) := by
          rw [mul_assoc]
        _ = Measure.infinitePi (fun _ : {u // isParam u} => ν) A * ∏ i ∈ Finset.range (n + 1), ν (D i) := by
          rw [Finset.prod_range_succ]

/-- **Adaptive reading.** The parameter and the values read are independent i.i.d. families. -/
theorem map_adapted {U E : Type*} [Countable U] [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (isParam : U → Prop) (choice : ℕ → (U → E) → U)
    (hroot : ∀ k ω, ¬ isParam (choice k ω)) (hinj : ∀ ω, Function.Injective fun k => choice k ω)
    (hadapt : ∀ k (ω ω' : U → E), (∀ u, isParam u → ω' u = ω u) →
      (∀ i < k, ω' (choice i ω) = ω (choice i ω)) → choice k ω' = choice k ω)
    (hmeas : ∀ k u, MeasurableSet {ω | choice k ω = u}) :
    (Measure.infinitePi fun _ : U => ν).map
        (fun ω => (fun u : {u // isParam u} => ω u, fun k => ω (choice k ω))) =
      (Measure.infinitePi fun _ : {u // isParam u} => ν).prod
        (Measure.infinitePi fun _ : ℕ => ν) := by
  let f : (U → E) → ({u // isParam u} → E) × (ℕ → E) :=
    fun ω => (fun u : {u // isParam u} => ω u, fun k => ω (choice k ω))
  have hf_meas : Measurable f := by
    refine Measurable.prodMk ?_ ?_
    · -- the parameter component: ω ↦ (fun u => ω u)
      refine (measurable_pi_iff.mpr fun u => ?_)
      exact measurable_pi_apply (u : U)
    · -- the read component: ω ↦ (fun k => ω (choice k ω))
      refine (measurable_pi_iff.mpr fun k => ?_)
      exact FrogModel.Recursion.measurable_read (choice k) (hmeas k)
  have h_cyl_meas : ∀ (D : ℕ → Set E), (∀ i, MeasurableSet (D i)) → ∀ n : ℕ,
      MeasurableSet {v : ℕ → E | ∀ i < n, v i ∈ D i} := by
    intro D hD n
    have : {v : ℕ → E | ∀ i < n, v i ∈ D i} = ⋂ i ∈ (Finset.range n : Set ℕ), (fun v => v i) ⁻¹' (D i) := by
      ext v; simp
    rw [this]
    refine MeasurableSet.biInter (Finset.countable_toSet _) (fun i _ => ?_)
    exact (measurable_pi_apply i) (hD i)
  refine FrogModel.Recursion.prod_ext_box _ _ ?_
  intro A' hA' D hD n
  have h_box_meas' : MeasurableSet (A' ×ˢ {v : ℕ → E | ∀ i < n, v i ∈ D i}) :=
    MeasurableSet.prod hA' (h_cyl_meas D hD n)
  calc
    ((Measure.infinitePi fun _ : U => ν).map f) (A' ×ˢ {v : ℕ → E | ∀ i < n, v i ∈ D i})
        = (Measure.infinitePi fun _ : U => ν) (f ⁻¹' (A' ×ˢ {v : ℕ → E | ∀ i < n, v i ∈ D i})) := by
      rw [Measure.map_apply hf_meas h_box_meas']
    _ = (Measure.infinitePi fun _ : U => ν)
        {ω | (fun u : {u // isParam u} => ω u) ∈ A' ∧ ∀ i < n, ω (choice i ω) ∈ D i} := by
      have h_preimage : f ⁻¹' (A' ×ˢ {v : ℕ → E | ∀ i < n, v i ∈ D i}) =
          {ω | (fun u : {u // isParam u} => ω u) ∈ A' ∧ ∀ i < n, ω (choice i ω) ∈ D i} := by
        ext ω; simp [f]
      rw [h_preimage]
    _ = Measure.infinitePi (fun _ : {u // isParam u} => ν) A' * ∏ i ∈ Finset.range n, ν (D i) := by
      rw [FrogModel.Recursion.adapted_box ν isParam choice hroot hinj hadapt hmeas A' hA' D hD n]
    _ = (Measure.infinitePi (fun _ : {u // isParam u} => ν) A') *
        (Measure.infinitePi (fun _ : ℕ => ν)) {v : ℕ → E | ∀ i < n, v i ∈ D i} := by
      have h_pi : {v : ℕ → E | ∀ i < n, v i ∈ D i} = Set.pi (Finset.range n) D := by
        ext v; simp
      rw [h_pi, MeasureTheory.Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (fun i hi => hD i)]
    _ = ((Measure.infinitePi fun _ : {u // isParam u} => ν).prod
        (Measure.infinitePi fun _ : ℕ => ν)) (A' ×ˢ {v : ℕ → E | ∀ i < n, v i ∈ D i}) := by
      rw [Measure.prod_prod]

/-- Prepending an independent value to an i.i.d. sequence gives an i.i.d. sequence. -/
theorem map_cons_infinitePi {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    (ν.prod (Measure.infinitePi fun _ : ℕ => ν)).map (fun p => seqCons p.1 p.2) =
      Measure.infinitePi fun _ : ℕ => ν := by
  have h := FrogModel.Recursion.map_infinitePi_head_tail ν
  have h_meas_ht : Measurable (fun (x : ℕ → E) => (x 0, fun t => x (t + 1))) := by
    refine Measurable.prod ?_ ?_
    · exact measurable_pi_apply 0
    · refine Measurable.of_eval ?_
      intro t
      exact measurable_pi_apply (t + 1)
  have h_meas_seqCons : Measurable (fun (p : E × (ℕ → E)) => seqCons p.1 p.2) := by
    refine Measurable.of_eval ?_
    intro i
    cases i with
    | zero => exact measurable_fst
    | succ i => exact (measurable_pi_apply i).comp measurable_snd
  have h_comp : (fun (p : E × (ℕ → E)) => seqCons p.1 p.2) ∘ (fun (x : ℕ → E) => (x 0, fun t => x (t + 1))) = id := by
    ext x n
    cases n with
    | zero => rfl
    | succ n => rfl
  rw [← h, Measure.map_map h_meas_seqCons h_meas_ht, h_comp]
  rw [MeasureTheory.Measure.map_id]

open ENNReal Filter in
/-- An i.i.d. uniform sequence on a finite type takes every value infinitely often. -/
theorem ae_infinite_eq {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] :
    ∀ᵐ D ∂(Measure.infinitePi fun _ : ℕ => (uniformOn Set.univ : Measure A)),
      ∀ a, {k | D k = a}.Infinite := by
  let μ := Measure.infinitePi fun _ : ℕ => (uniformOn Set.univ : Measure A)
  -- Step 1: Use ae_all_iff to reduce to pointwise a
  rw [ae_all_iff]
  intro a
  -- Let s n = {D | D n = a}
  let s : ℕ → Set (ℕ → A) := fun n => {D | D n = a}
  have hs_meas : ∀ n, MeasurableSet (s n) := by
    intro n
    have : s n = (fun (D : ℕ → A) => D n) ⁻¹' {a} := by
      ext D; simp [s]
    rw [this]
    exact (measurable_pi_apply n) (measurableSet_singleton a)
  -- Step 2: Prove iIndepSet s μ using iIndepFun_infinitePi
  have h_indep_fun : iIndepFun (fun i (ω : ℕ → A) => ω i) μ := by
    refine iIndepFun_infinitePi (𝓧 := fun _ : ℕ => A) (Ω := fun _ : ℕ => A)
      (P := fun _ : ℕ => (uniformOn Set.univ : Measure A))
      (X := fun _ => id) ?_
    intro i
    exact measurable_id
  have hs_indep : iIndepSet s μ := by
    rw [iIndepSet_iff_meas_biInter hs_meas]
    intro S
    have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp h_indep_fun) S
      (sets := fun _ => {a}) (by
        intro i hi
        exact measurableSet_singleton a)
    have h_preimage : ∀ i, (fun (ω : ℕ → A) => ω i) ⁻¹' {a} = s i := by
      intro i; ext ω; simp [s]
    have h_inter : (⋂ i ∈ S, (fun (ω : ℕ → A) => ω i) ⁻¹' {a}) = (⋂ i ∈ S, s i) := by
      simp [h_preimage]
    have h_prod : (∏ i ∈ S, μ ((fun (ω : ℕ → A) => ω i) ⁻¹' {a})) = (∏ i ∈ S, μ (s i)) := by
      simp [h_preimage]
    simpa [h_inter, h_prod] using h
  -- Step 3: Compute μ (s n) = 1 / card A
  have hμ_s : ∀ n, μ (s n) = (1 : ENNReal) / (Fintype.card A : ENNReal) := by
    intro n
    have h_map := MeasureTheory.Measure.infinitePi_map_eval
      (fun _ : ℕ => (uniformOn Set.univ : Measure A)) n
    have h_preimage : s n = (fun (D : ℕ → A) => D n) ⁻¹' {a} := by
      ext D; simp [s]
    rw [h_preimage]
    rw [← Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton a)]
    rw [h_map]
    rw [uniformOn_univ]
    simp
  -- Step 4: Sum diverges
  have h_sum : (∑' n, μ (s n)) = ∞ := by
    simp_rw [hμ_s]
    simp
  -- Step 5: Apply Borel-Cantelli
  have h_limsup_meas : MeasurableSet (limsup s atTop) :=
    MeasurableSet.measurableSet_limsup hs_meas
  have h_limsup : μ (limsup s atTop) = 1 :=
    measure_limsup_eq_one hs_meas hs_indep h_sum
  -- Step 6: From limsup = 1, get the ae statement
  have h_ae : ∀ᵐ D ∂μ, ∃ᶠ n in atTop, D n = a := by
    have h_compl : μ ((limsup s atTop)ᶜ) = 0 := by
      rw [measure_compl h_limsup_meas (measure_ne_top _ _), h_limsup, measure_univ]
      simp
    rw [ae_iff]
    have h_eq : {D | ¬ (∃ᶠ n in atTop, D n = a)} = (limsup s atTop)ᶜ := by
      ext D
      simp [s, Filter.mem_limsup_iff_frequently_mem]
    rw [h_eq, h_compl]
  -- Step 7: Convert back to the original goal
  filter_upwards [h_ae] with ω hω
  have h_equiv : ({k | ω k = a}.Infinite ↔ ∃ᶠ n in atTop, ω n = a) := by
    rw [← Nat.frequently_atTop_iff_infinite]
  rw [h_equiv]
  exact hω

end FrogModel.Recursion
