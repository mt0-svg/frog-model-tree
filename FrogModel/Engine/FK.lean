module

public import FrogModel.Engine.Core
public import FrogModel.Lemmas.Refresh

@[expose] public section

/-!
# The root engine: Feynman-Kac sums under i.i.d. inputs

Under i.i.d. inputs of law `ν`, an input sequence is its first input followed by an
independent i.i.d. sequence (`map_cons_iid`, `lintegral_iid_cons`); the expected Feynman-Kac sum over
`n` steps is the `n`-th iterate of the linear system with kernel `fkKernel f m ν` and right side
`fkRhs a ν` (`lintegral_fk`), and its supremum over `n` is the least solution (`lintegral_iSup_fk`).
-/

open MeasureTheory
open scoped ENNReal

theorem FrogModel.Engine.fk_mono {X Ξ : Type*} (f : X → Ξ → X) (m a : X → Ξ → ℝ≥0∞) (x : X)
    (w : ℕ → Ξ) : Monotone fun n => FrogModel.Engine.fk f m a n x w := by
  refine monotone_nat_of_le_succ ?_
  intro n
  induction' n with n ih generalizing x w
  · simp [FrogModel.Engine.fk]
  · simp [FrogModel.Engine.fk]
    have h := ih (f x (w 0)) (fun k => w (k + 1))
    gcongr
    exact h

theorem FrogModel.Engine.measurable_fk {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (m a : X → Ξ → ℝ≥0∞) (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y})
    (hm : ∀ x, Measurable (m x)) (ha : ∀ x, Measurable (a x)) (n : ℕ) (x : X) :
    Measurable (FrogModel.Engine.fk f m a n x) := by
  induction' n with n ih generalizing x
  · -- n = 0
    simpa [FrogModel.Engine.fk] using measurable_const
  · -- n + 1
    simp [FrogModel.Engine.fk]
    refine Measurable.add ?_ (Measurable.mul ?_ ?_)
    · -- a x (w 0)
      exact (ha x).comp (measurable_pi_apply 0)
    · -- m x (w 0)
      exact (hm x).comp (measurable_pi_apply 0)
    · -- fk f m a n (f x (w 0)) (λ k => w (k+1))
      have h_shift : Measurable (fun (w : ℕ → Ξ) (k : ℕ) => w (k + 1)) :=
        measurable_pi_iff.mpr fun k => measurable_pi_apply (k + 1)
      have h_eq : (fun (w : ℕ → Ξ) => fk f m a n (f x (w 0)) (fun k => w (k + 1))) =
          (fun w => ∑' (y : X),
            Set.indicator {w' | f x (w' 0) = y}
              (fun w' => fk f m a n y (fun k => w' (k + 1))) w) := by
        ext w
        simpa [Set.indicator] using
          (tsum_eq_single (L := SummationFilter.unconditional X) (f x (w 0))
            (f := fun (y : X) =>
              Set.indicator {w' | f x (w' 0) = y}
                (fun w' => fk f m a n y (fun k => w' (k + 1))) w)
            (by
              intro y hy_ne
              simp [Set.indicator, hy_ne.symm])).symm
      rw [h_eq]
      refine Measurable.ennreal_tsum fun y => ?_
      refine Measurable.indicator (ih y |>.comp h_shift) ?_
      have h_set : {w' : ℕ → Ξ | f x (w' 0) = y} =
          (fun (w' : ℕ → Ξ) => w' 0) ⁻¹' {ξ | f x ξ = y} := by
        ext w'; simp
      rw [h_set]
      exact (hf x y).preimage (measurable_pi_apply 0)

theorem FrogModel.Engine.map_prefix_iid {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun ω (j : Fin n) => ω j) =
      Measure.pi fun _ : Fin n => μ := by
  refine (Measure.pi_eq (μ := fun _ : Fin n => μ) fun s hs => ?_).symm
  have hmeas : Measurable (fun (ω : ℕ → E) (j : Fin n) => ω j) := by
    refine measurable_pi_iff.mpr fun j => ?_
    simpa using measurable_pi_apply (j.val : ℕ)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpreimage : (fun ω (j : Fin n) => ω j) ⁻¹' (Set.univ.pi s) =
      Set.pi (Finset.range n) (fun i => if h : i < n then s ⟨i, h⟩ else Set.univ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi]
    constructor
    · intro h i hi
      have hi' : i < n := Finset.mem_range.1 hi
      simpa [hi'] using h ⟨i, hi'⟩
    · intro h j
      have hj : (j : ℕ) < n := j.2
      have hmem : (j : ℕ) ∈ Finset.range n := Finset.mem_range.2 hj
      simpa [hj] using h (j : ℕ) hmem
  rw [hpreimage]
  have hmeas' : ∀ i ∈ Finset.range n, MeasurableSet
      ((fun i => if h : i < n then s ⟨i, h⟩ else Set.univ) i) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    simp [hi', hs ⟨i, hi'⟩]
  rw [MeasureTheory.Measure.infinitePi_pi (μ := fun _ : ℕ => μ) hmeas']
  have hprod_eq := Finset.prod_fin_eq_prod_range (fun i : Fin n => μ (s i))
  calc
    ∏ i ∈ Finset.range n, μ (if h : i < n then s ⟨i, h⟩ else Set.univ)
        = ∏ i ∈ Finset.range n, (if h : i < n then μ (s ⟨i, h⟩) else 1) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi' : i < n := Finset.mem_range.1 hi
      simp [hi']
    _ = ∏ i : Fin n, μ (s i) := by rw [← hprod_eq]

theorem FrogModel.Engine.map_cons_iid {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] :
    (ν.prod (FrogModel.Engine.iidMeasure ν)).map
        (fun p : Ξ × (ℕ → Ξ) => FrogModel.Engine.consSeq p.1 p.2) =
      FrogModel.Engine.iidMeasure ν := by
  have hpair := FrogModel.infinitePi_map_pair_injective ν Nat.succ Nat.succ_injective 0
    (fun a => Nat.succ_ne_zero a)
  have hcons : Measurable (fun p : Ξ × (ℕ → Ξ) => FrogModel.Engine.consSeq p.1 p.2) := by
    refine measurable_pi_iff.2 fun n => ?_
    cases n with
    | zero => exact measurable_fst
    | succ n => exact (measurable_pi_apply n).comp measurable_snd
  have hp : Measurable fun ω : ℕ → Ξ => (ω 0, fun a => ω (Nat.succ a)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun a => measurable_pi_apply _)
  unfold FrogModel.Engine.iidMeasure
  rw [← hpair, Measure.map_map hcons hp]
  have e : ((fun p : Ξ × (ℕ → Ξ) => FrogModel.Engine.consSeq p.1 p.2) ∘
      fun ω : ℕ → Ξ => (ω 0, fun a => ω (Nat.succ a))) = id := by
    funext ω n
    cases n <;> rfl
  rw [e, Measure.map_id]

theorem FrogModel.Engine.lintegral_iid_cons {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (F : Ξ → (ℕ → Ξ) → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) :
    ∫⁻ w, F (w 0) (fun k => w (k + 1)) ∂(FrogModel.Engine.iidMeasure ν) =
      ∫⁻ ξ, ∫⁻ w, F ξ w ∂(FrogModel.Engine.iidMeasure ν) ∂ν := by
  have hSFinite : SFinite (FrogModel.Engine.iidMeasure ν) := by
    unfold FrogModel.Engine.iidMeasure
    infer_instance
  conv_lhs =>
    rw [← FrogModel.Engine.map_cons_iid ν]
  rw [MeasureTheory.lintegral_map ?hf ?hg]
  · simp [FrogModel.Engine.consSeq]
    have h_eq : (fun (a : Ξ × (ℕ → Ξ)) => F a.1 (fun k => a.2 k)) = (fun a => F a.1 a.2) := by
      ext a; simp
    rw [h_eq]
    simpa [Function.uncurry] using MeasureTheory.lintegral_prod (Function.uncurry F) hF.aemeasurable
  · -- integrand after mapping: fun w => F (w 0) (fun k => w (k + 1))
    have h_eq : (fun (w : ℕ → Ξ) => F (w 0) (fun k => w (k + 1))) =
        (Function.uncurry F) ∘ (fun (w : ℕ → Ξ) => (w 0, fun k => w (k + 1))) := by
      rfl
    rw [h_eq]
    apply hF.comp
    apply Measurable.prodMk
    · exact measurable_pi_apply 0
    · apply Measurable.of_eval
      intro k
      exact measurable_pi_apply (k + 1)
  · -- consSeq is measurable
    unfold FrogModel.Engine.consSeq
    apply Measurable.of_eval
    intro k
    cases k with
    | zero => exact measurable_fst
    | succ k => exact (measurable_pi_apply k).comp measurable_snd

theorem FrogModel.Engine.lintegral_mul_comp_eq_tsum {X Ξ : Type*} [MeasurableSpace Ξ]
    [Countable X] (f : X → Ξ → X) (m : X → Ξ → ℝ≥0∞) (ν : Measure Ξ)
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (hm : ∀ x, Measurable (m x)) (g : X → ℝ≥0∞)
    (x : X) :
    ∫⁻ ξ, m x ξ * g (f x ξ) ∂ν = ∑' y, FrogModel.Engine.fkKernel f m ν x y * g y := by
  simp only [FrogModel.Engine.fkKernel]
  let s : X → Set Ξ := fun y => {ξ | f x ξ = y}
  have hs_meas : ∀ y, MeasurableSet (s y) := hf x
  have hs_disjoint : Pairwise (Function.onFun Disjoint s) := by
    intro y₁ y₂ hne
    apply Set.disjoint_left.mpr
    intro ξ hξ₁ hξ₂
    apply hne
    calc
      y₁ = f x ξ := (hξ₁).symm
      _ = y₂ := hξ₂
  have hs_cover : ⋃ y, s y = Set.univ := by
    ext ξ; simp [s]
  calc
    ∫⁻ ξ, m x ξ * g (f x ξ) ∂ν = ∫⁻ ξ in Set.univ, m x ξ * g (f x ξ) ∂ν := by
      rw [MeasureTheory.Measure.restrict_univ]
    _ = ∫⁻ ξ in ⋃ y, s y, m x ξ * g (f x ξ) ∂ν := by rw [hs_cover]
    _ = ∑' y, ∫⁻ ξ in s y, m x ξ * g (f x ξ) ∂ν :=
      MeasureTheory.lintegral_iUnion hs_meas hs_disjoint _
    _ = ∑' y, ∫⁻ ξ in s y, m x ξ * g y ∂ν := by
      refine tsum_congr (fun y => ?_)
      rw [MeasureTheory.setLIntegral_congr_fun (hs_meas y) ?_]
      intro ξ hξ
      dsimp [s] at hξ
      simp [hξ]
    _ = ∑' y, (∫⁻ ξ in s y, m x ξ ∂ν) * g y := by
      refine tsum_congr (fun y => ?_)
      rw [MeasureTheory.lintegral_mul_const (g y) (hm x)]

theorem FrogModel.Engine.lintegral_fk {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (m a : X → Ξ → ℝ≥0∞) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (hm : ∀ x, Measurable (m x))
    (ha : ∀ x, Measurable (a x)) (n : ℕ) (x : X) :
    ∫⁻ w, FrogModel.Engine.fk f m a n x w ∂(FrogModel.Engine.iidMeasure ν) =
      FrogModel.LinSys.iter (FrogModel.Engine.fkKernel f m ν) (FrogModel.Engine.fkRhs a ν) n x := by
  induction n generalizing x with
  | zero =>
      simp [FrogModel.Engine.fk, FrogModel.LinSys.iter]
  | succ n ih =>
      simp [FrogModel.Engine.fk, FrogModel.LinSys.iter, FrogModel.LinSys.app,
        FrogModel.Engine.fkRhs, FrogModel.Engine.fkKernel]
      have hmeas_a0 : Measurable fun (w : ℕ → Ξ) => a x (w 0) :=
        (ha x).comp (measurable_pi_apply 0)
      rw [lintegral_add_left hmeas_a0]
      -- Goal:
      -- (∫⁻ (w : ℕ → Ξ), a x (w 0) ∂(iidMeasure ν)) +
      -- (∫⁻ (w : ℕ → Ξ), m x (w 0) * fk f m a n (f x (w 0)) (fun k => w (k + 1)) ∂(iidMeasure ν)) =
      --   (∫⁻ (ξ : Ξ), a x ξ ∂ν) + ∑' (y : X), (∫⁻ (ξ : Ξ) in {ξ | f x ξ = y}, m x ξ ∂ν) *
      --     LinSys.iter (fkKernel f m ν) (fkRhs a ν) n y
      have hmeas_fk_uncurry : Measurable (Function.uncurry fun (ξ : Ξ) (w' : ℕ → Ξ) =>
          FrogModel.Engine.fk f m a n (f x ξ) w') := by
        have h_eq : (Function.uncurry fun (ξ : Ξ) (w' : ℕ → Ξ) =>
            FrogModel.Engine.fk f m a n (f x ξ) w') =
            fun (p : Ξ × (ℕ → Ξ)) =>
              ∑' (y : X), Set.indicator {q : Ξ × (ℕ → Ξ) | f x q.1 = y}
                (fun q => FrogModel.Engine.fk f m a n y q.2) p := by
          ext p
          -- Use the property of indicator and tsum
          have h_tsum : (∑' (y : X), Set.indicator {q : Ξ × (ℕ → Ξ) | f x q.1 = y}
              (fun q => FrogModel.Engine.fk f m a n y q.2) p) =
              FrogModel.Engine.fk f m a n (f x p.1) p.2 := by
            -- The sum has only one non-zero term (when y = f x p.1)
            -- Use tsum_eq_single from ENNReal
            have h_single : (∑' (y : X), Set.indicator {q : Ξ × (ℕ → Ξ) | f x q.1 = y}
                (fun q => FrogModel.Engine.fk f m a n y q.2) p) =
                Set.indicator {q : Ξ × (ℕ → Ξ) | f x q.1 = f x p.1}
                (fun q => FrogModel.Engine.fk f m a n (f x p.1) q.2) p :=
              tsum_eq_single (f x p.1) (fun y hy => by
                classical
                  rw [Set.indicator_apply]
                  by_cases h : (p : Ξ × (ℕ → Ξ)) ∈ {q | f x q.1 = y}
                  · exfalso
                    apply hy
                    exact h.symm
                  · simp [h])
            -- h_single : ∑' y, ... = (indicator for y = f x p.1) p
            -- Now compute the indicator at p
            have h_indicator : Set.indicator {q : Ξ × (ℕ → Ξ) | f x q.1 = f x p.1}
                (fun q => FrogModel.Engine.fk f m a n (f x p.1) q.2) p =
                FrogModel.Engine.fk f m a n (f x p.1) p.2 := by
              classical
                rw [Set.indicator_apply]
                simp
            rw [h_single, h_indicator]
          exact h_tsum.symm
        rw [h_eq]
        refine Measurable.tsum fun y => ?_
        have h_set : MeasurableSet {q : Ξ × (ℕ → Ξ) | f x q.1 = y} :=
          measurable_fst (hf x y)
        have h_fun : Measurable (fun q : Ξ × (ℕ → Ξ) =>
            FrogModel.Engine.fk f m a n y q.2) :=
          (measurable_fk f m a hf hm ha n y).comp measurable_snd
        exact h_fun.indicator h_set
      have hmeas_F2 : Measurable (Function.uncurry fun (ξ : Ξ) (w' : ℕ → Ξ) =>
          m x ξ * FrogModel.Engine.fk f m a n (f x ξ) w') := by
        have : (Function.uncurry fun (ξ : Ξ) (w' : ℕ → Ξ) =>
            m x ξ * FrogModel.Engine.fk f m a n (f x ξ) w') =
            (fun p => m x p.1) *
            (Function.uncurry fun (ξ : Ξ) (w' : ℕ → Ξ) =>
              FrogModel.Engine.fk f m a n (f x ξ) w') := by
          ext p; rfl
        rw [this]
        have h1 : Measurable (fun p : Ξ × (ℕ → Ξ) => m x p.1) :=
          (hm x).comp measurable_fst
        have h2 : Measurable (Function.uncurry fun (ξ : Ξ) (w' : ℕ → Ξ) =>
          FrogModel.Engine.fk f m a n (f x ξ) w') := hmeas_fk_uncurry
        exact h1.mul h2
      have hmeas_F1 : Measurable (Function.uncurry fun (ξ : Ξ) (w' : ℕ → Ξ) => a x ξ) :=
        (ha x).comp measurable_fst
      have h_first : (∫⁻ (w : ℕ → Ξ), a x (w 0) ∂(FrogModel.Engine.iidMeasure ν)) =
          (∫⁻ (ξ : Ξ), a x ξ ∂ν) := by
        calc
          (∫⁻ (w : ℕ → Ξ), a x (w 0) ∂(FrogModel.Engine.iidMeasure ν)) =
              (∫⁻ (w : ℕ → Ξ), (fun (ξ : Ξ) (w' : ℕ → Ξ) => a x ξ) (w 0)
                (fun k => w (k + 1)) ∂(FrogModel.Engine.iidMeasure ν)) := rfl
          _ = (∫⁻ (ξ : Ξ), ∫⁻ (w : ℕ → Ξ), a x ξ ∂(FrogModel.Engine.iidMeasure ν) ∂ν) := by
            rw [FrogModel.Engine.lintegral_iid_cons ν (fun (ξ : Ξ) (w' : ℕ → Ξ) => a x ξ) hmeas_F1]
          _ = (∫⁻ (ξ : Ξ), a x ξ * (FrogModel.Engine.iidMeasure ν) Set.univ ∂ν) := by
            simp_rw [lintegral_const]
          _ = (∫⁻ (ξ : Ξ), a x ξ * 1 ∂ν) := by
            haveI : IsProbabilityMeasure (FrogModel.Engine.iidMeasure ν) := by
              dsimp [FrogModel.Engine.iidMeasure]
              infer_instance
            rw [measure_univ]
          _ = (∫⁻ (ξ : Ξ), a x ξ ∂ν) := by simp
      have h_second : (∫⁻ (w : ℕ → Ξ), m x (w 0) *
          FrogModel.Engine.fk f m a n (f x (w 0)) (fun k => w (k + 1))
          ∂(FrogModel.Engine.iidMeasure ν)) =
          ∑' (y : X), FrogModel.Engine.fkKernel f m ν x y *
            FrogModel.LinSys.iter (FrogModel.Engine.fkKernel f m ν)
              (FrogModel.Engine.fkRhs a ν) n y := by
        calc
          (∫⁻ (w : ℕ → Ξ), m x (w 0) *
              FrogModel.Engine.fk f m a n (f x (w 0)) (fun k => w (k + 1))
              ∂(FrogModel.Engine.iidMeasure ν)) =
              (∫⁻ (w : ℕ → Ξ), (fun (ξ : Ξ) (w' : ℕ → Ξ) =>
                m x ξ * FrogModel.Engine.fk f m a n (f x ξ) w') (w 0)
                (fun k => w (k + 1)) ∂(FrogModel.Engine.iidMeasure ν)) := rfl
          _ = (∫⁻ (ξ : Ξ), ∫⁻ (w : ℕ → Ξ),
              m x ξ * FrogModel.Engine.fk f m a n (f x ξ) w
              ∂(FrogModel.Engine.iidMeasure ν) ∂ν) := by
            rw [FrogModel.Engine.lintegral_iid_cons ν
              (fun (ξ : Ξ) (w' : ℕ → Ξ) => m x ξ * FrogModel.Engine.fk f m a n (f x ξ) w')
              hmeas_F2]
          _ = (∫⁻ (ξ : Ξ), m x ξ *
              (∫⁻ (w : ℕ → Ξ), FrogModel.Engine.fk f m a n (f x ξ) w
                ∂(FrogModel.Engine.iidMeasure ν)) ∂ν) := by
            refine lintegral_congr fun ξ => ?_
            rw [lintegral_const_mul (m x ξ)
              (measurable_fk f m a hf hm ha n (f x ξ))]
          _ = (∫⁻ (ξ : Ξ), m x ξ *
              FrogModel.LinSys.iter (FrogModel.Engine.fkKernel f m ν)
                (FrogModel.Engine.fkRhs a ν) n (f x ξ) ∂ν) := by
            refine lintegral_congr fun ξ => ?_
            rw [ih (f x ξ)]
          _ = ∑' (y : X), FrogModel.Engine.fkKernel f m ν x y *
              FrogModel.LinSys.iter (FrogModel.Engine.fkKernel f m ν)
                (FrogModel.Engine.fkRhs a ν) n y := by
            rw [FrogModel.Engine.lintegral_mul_comp_eq_tsum f m ν hf hm
              (FrogModel.LinSys.iter (FrogModel.Engine.fkKernel f m ν) (FrogModel.Engine.fkRhs a ν) n) x]
      rw [h_first, h_second]
      simp [FrogModel.Engine.fkKernel]

theorem FrogModel.Engine.lintegral_iSup_fk {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (m a : X → Ξ → ℝ≥0∞) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (hm : ∀ x, Measurable (m x))
    (ha : ∀ x, Measurable (a x)) (x : X) :
    ∫⁻ w, ⨆ n, FrogModel.Engine.fk f m a n x w ∂(FrogModel.Engine.iidMeasure ν) =
      FrogModel.LinSys.least (FrogModel.Engine.fkKernel f m ν) (FrogModel.Engine.fkRhs a ν) x := by
  have h_meas : ∀ n, Measurable (FrogModel.Engine.fk f m a n x) := by
    intro n
    exact FrogModel.Engine.measurable_fk f m a hf hm ha n x
  have h_mono : Monotone fun n => FrogModel.Engine.fk f m a n x := by
    intro n n' h
    intro w
    exact FrogModel.Engine.fk_mono f m a x w h
  calc
    ∫⁻ w, ⨆ n, FrogModel.Engine.fk f m a n x w ∂(FrogModel.Engine.iidMeasure ν)
        = ⨆ n, ∫⁻ w, FrogModel.Engine.fk f m a n x w ∂(FrogModel.Engine.iidMeasure ν) := by
      rw [MeasureTheory.lintegral_iSup h_meas h_mono]
    _ = ⨆ n, FrogModel.LinSys.iter (FrogModel.Engine.fkKernel f m ν)
        (FrogModel.Engine.fkRhs a ν) n x := by
      refine iSup_congr ?_
      intro n
      rw [FrogModel.Engine.lintegral_fk f m a ν hf hm ha n x]
    _ = FrogModel.LinSys.least (FrogModel.Engine.fkKernel f m ν)
        (FrogModel.Engine.fkRhs a ν) x := rfl
