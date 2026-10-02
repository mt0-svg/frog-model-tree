module

public import FrogModel.Engine.Dominate
public import FrogModel.LinSys.Basic

@[expose] public section

/-!
# The root engine: Markov property and least solutions along trajectories

Under i.i.d. inputs:
the prefix and the shifted tail of the inputs are independent (`map_prefix_shift_iid`,
`lintegral_prefix_shift`), so a reward at step `n` times a functional of the trajectory after it
integrates as the reward times the expected functional from the state reached
(`lintegral_traj_markov`); the expected sum of rewards along a trajectory, and the probability that
an event that happens at most once happens, are least solutions (`lintegral_tsum_traj_eq_least`,
`measure_exists_traj_eq_least`). A sub-solution dominated by a contraction lies below the least
solution (`le_least_of_sub_contract`). Root steps keep monotone outputs recorded below the exit
count (`rstep_outInv`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

theorem FrogModel.Engine.traj_add {X Ξ : Type*} (f : X → Ξ → X) (x : X) (w : ℕ → Ξ) (n k : ℕ) :
    FrogModel.Engine.traj f x w (n + k) =
      FrogModel.Engine.traj f (FrogModel.Engine.traj f x w n) (fun j => w (n + j)) k := by
  induction' k with k ih
  · rfl
  · have h : n + (k + 1) = (n + k) + 1 := by omega
    rw [h, FrogModel.Engine.traj, FrogModel.Engine.traj]
    simp [ih]

theorem FrogModel.Engine.traj_congr_prefix {X Ξ : Type*} (f : X → Ξ → X) (x : X) (w w' : ℕ → Ξ)
    (n : ℕ) (h : ∀ j < n, w j = w' j) :
    FrogModel.Engine.traj f x w n = FrogModel.Engine.traj f x w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [FrogModel.Engine.traj]
    have hn : w n = w' n := h n (Nat.lt_succ_self n)
    have hw : ∀ j < n, w j = w' j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [ih hw, hn]

theorem FrogModel.Engine.map_prefix_shift_iid {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (FrogModel.Engine.iidMeasure ν).map (fun w => ((fun j : Fin n => w j), fun k => w (n + k))) =
      (Measure.pi fun _ : Fin n => ν).prod (FrogModel.Engine.iidMeasure ν) := by
  induction' n with n ih
  · -- n = 0
    have h_empty : (Measure.pi fun _ : Fin 0 => ν) = Measure.dirac (isEmptyElim : Fin 0 → Ξ) := by
      simpa using Measure.pi_of_empty (fun _ : Fin 0 => ν) (isEmptyElim : Fin 0 → Ξ)
    rw [FrogModel.Engine.iidMeasure, h_empty, Measure.dirac_prod]
    congr
    ext w : 2
    · apply Subsingleton.elim
    · ext k; simp
  · -- n → n+1
    set μ := Measure.infinitePi fun _ : ℕ => ν with hμ
    have h_split : μ.map (fun w => (w 0, fun k => w (k + 1))) = ν.prod μ :=
      FrogModel.infinitePi_map_pair_injective ν Nat.succ Nat.succ_injective 0 Nat.succ_ne_zero
    have h_tail : μ.map (fun w' => (fun j : Fin n => w' j, fun k => w' (n + k))) =
      (Measure.pi fun _ : Fin n => ν).prod μ := ih
    set g := fun w : ℕ → Ξ => (w 0, fun k => w (k + 1)) with hg
    set h := fun w' : ℕ → Ξ => (fun j : Fin n => w' j, fun k => w' (n + k)) with hh
    set φ := fun (x : Ξ × ((Fin n → Ξ) × (ℕ → Ξ))) => ((Fin.cons x.1 x.2.1 : Fin (n+1) → Ξ), x.2.2) with hφ
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ξ) 0 with he
    set ψ := Prod.map (id : Ξ → Ξ) h with hψ
    have h_meas_g : Measurable g := by
      unfold g
      measurability
    have h_meas_h : Measurable h := by
      unfold h
      measurability
    have h_meas_φ : Measurable φ := by
      unfold φ
      refine Measurable.prodMk ?_ (measurable_snd.comp measurable_snd)
      -- Prove Measurable (fun x => Fin.cons x.1 x.2.1)
      -- Using the fact that Fin.cons is measurable pointwise
      refine Measurable.of_eval fun j => ?_
      -- Now: Measurable (fun x => Fin.cons x.1 x.2.1 j)
      -- We prove this by cases on j
      induction j using Fin.induction with
      | zero =>
        -- Fin.cons x.1 x.2.1 0 = x.1, which is measurable
        simpa [Fin.cons] using measurable_fst
      | succ i ih =>
        -- Fin.cons x.1 x.2.1 (Fin.succ i) = x.2.1 i, which is measurable
        have h : Measurable (fun (x : Ξ × ((Fin n → Ξ) × (ℕ → Ξ))) => x.2.1 i) := by
          -- The goal is definitionally the same as what we have
          exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
        simpa [Fin.cons] using h
    have h_meas_ψ : Measurable ψ := by
      unfold ψ
      measurability
    have h_f_eq : (fun w : ℕ → Ξ => ((fun j : Fin (n+1) => w j), fun k => w ((n+1) + k))) =
      φ ∘ ψ ∘ g := by
      funext w
      apply Prod.ext
      · funext j
        simp [φ, ψ, h, g, Fin.cons, Function.comp]
        induction j using Fin.induction with
        | zero => rfl
        | succ i ih => simp
      · funext k
        simp [φ, ψ, h, g, Function.comp, add_assoc, add_comm, add_left_comm]
    have h_phi_prodAssoc : φ ∘ (MeasurableEquiv.prodAssoc (α := Ξ) (β := Fin n → Ξ) (γ := ℕ → Ξ)) =
      Prod.map e.symm id := by
      funext ⟨⟨a, p⟩, q⟩
      apply Prod.ext
      · funext i
        simp [φ, e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc, Fin.cons]
      · funext i
        simp [φ, e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc]
    calc
      μ.map (fun w => ((fun j : Fin (n+1) => w j), fun k => w ((n+1) + k)))
          = μ.map (φ ∘ ψ ∘ g) := by rw [h_f_eq]
      _ = Measure.map (φ ∘ ψ ∘ g) μ := rfl
      _ = Measure.map ((φ ∘ ψ) ∘ g) μ := by rfl
      _ = Measure.map (φ ∘ ψ) (Measure.map g μ) := by rw [← Measure.map_map (h_meas_φ.comp h_meas_ψ) h_meas_g]
      _ = Measure.map (φ ∘ ψ) (ν.prod μ) := by rw [h_split]
      _ = Measure.map φ (Measure.map ψ (ν.prod μ)) := by rw [Measure.map_map h_meas_φ h_meas_ψ]
      _ = Measure.map φ ((Measure.map id ν).prod (Measure.map h μ)) := by
        simpa [ψ] using (congrArg (Measure.map φ) (Measure.map_prod_map ν μ measurable_id h_meas_h)).symm
      _ = Measure.map φ (ν.prod (Measure.map h μ)) := by simp
      _ = Measure.map φ (ν.prod ((Measure.pi fun _ : Fin n => ν).prod μ)) := by rw [h_tail]
      _ = Measure.map φ (Measure.map (MeasurableEquiv.prodAssoc (α := Ξ) (β := Fin n → Ξ) (γ := ℕ → Ξ)) ((ν.prod (Measure.pi fun _ : Fin n => ν)).prod μ)) := by
        rw [Measure.prodAssoc_prod]
      _ = Measure.map (φ ∘ (MeasurableEquiv.prodAssoc (α := Ξ) (β := Fin n → Ξ) (γ := ℕ → Ξ))) ((ν.prod (Measure.pi fun _ : Fin n => ν)).prod μ) := by
        have h_meas_prodAssoc : Measurable (MeasurableEquiv.prodAssoc (α := Ξ) (β := Fin n → Ξ) (γ := ℕ → Ξ)) :=
          (MeasurableEquiv.prodAssoc (α := Ξ) (β := Fin n → Ξ) (γ := ℕ → Ξ)).measurable
        rw [Measure.map_map h_meas_φ h_meas_prodAssoc]
      _ = Measure.map (Prod.map e.symm id) ((ν.prod (Measure.pi fun _ : Fin n => ν)).prod μ) := by rw [h_phi_prodAssoc]
      _ = (Measure.map e.symm (ν.prod (Measure.pi fun _ : Fin n => ν))).prod μ := by
        have h_meas_e : Measurable e.symm := e.symm.measurable
        have h_meas_id : Measurable (id : (ℕ → Ξ) → (ℕ → Ξ)) := measurable_id
        rw [← Measure.map_prod_map (ν.prod (Measure.pi fun _ : Fin n => ν)) μ h_meas_e h_meas_id, Measure.map_id]
      _ = (Measure.pi fun _ : Fin (n+1) => ν).prod μ := by
        have h_mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0
        rw [h_mp.symm.map_eq]
      _ = (Measure.pi fun _ : Fin (n+1) => ν).prod (FrogModel.Engine.iidMeasure ν) := rfl

theorem FrogModel.Engine.lintegral_prefix_shift {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (n : ℕ) (F : (Fin n → Ξ) → ℝ≥0∞) (G : (ℕ → Ξ) → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ w, F (fun j : Fin n => w j) * G (fun k => w (n + k)) ∂(FrogModel.Engine.iidMeasure ν) =
      (∫⁻ y, F y ∂(Measure.pi fun _ : Fin n => ν)) *
        ∫⁻ w, G w ∂(FrogModel.Engine.iidMeasure ν) := by
  have h_prefix_meas : Measurable fun (w : ℕ → Ξ) => (fun j : Fin n => w j) :=
    Measurable.of_eval fun j => measurable_pi_apply (j : ℕ)
  have h_shift_meas : Measurable fun (w : ℕ → Ξ) => (fun k : ℕ => w (n + k)) :=
    Measurable.of_eval fun k => measurable_pi_apply (n + k)
  have h_pair_meas : Measurable fun (w : ℕ → Ξ) => ((fun j : Fin n => w j), fun k => w (n + k)) :=
    h_prefix_meas.prodMk h_shift_meas
  have h_prod_meas : Measurable fun (p : (Fin n → Ξ) × (ℕ → Ξ)) => F p.1 * G p.2 :=
    (hF.comp measurable_fst).mul (hG.comp measurable_snd)
  haveI : SFinite (FrogModel.Engine.iidMeasure ν) := by
    unfold FrogModel.Engine.iidMeasure
    infer_instance
  calc
    ∫⁻ w, F (fun j : Fin n => w j) * G (fun k => w (n + k)) ∂(FrogModel.Engine.iidMeasure ν)
        = ∫⁻ w, (F (fun j : Fin n => w j) * G (fun k => w (n + k))) ∂(FrogModel.Engine.iidMeasure ν) := rfl
    _ = ∫⁻ p, (F p.1 * G p.2) ∂((FrogModel.Engine.iidMeasure ν).map fun w => ((fun j : Fin n => w j), fun k => w (n + k))) := by
      rw [lintegral_map h_prod_meas h_pair_meas]
    _ = ∫⁻ p, (F p.1 * G p.2) ∂((Measure.pi fun _ : Fin n => ν).prod (FrogModel.Engine.iidMeasure ν)) := by
      rw [FrogModel.Engine.map_prefix_shift_iid ν n]
    _ = (∫⁻ y, F y ∂(Measure.pi fun _ : Fin n => ν)) * ∫⁻ w, G w ∂(FrogModel.Engine.iidMeasure ν) := by
      rw [lintegral_prod_mul hF.aemeasurable hG.aemeasurable]

theorem FrogModel.Engine.measure_le_of_singleton {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ ν : Measure α) (h : ∀ a, μ {a} ≤ ν {a}) : μ ≤ ν := by
  rw [MeasureTheory.Measure.le_iff]
  intro s hs
  have hcount : s.Countable := Set.to_countable s
  have hmeas : ∀ y ∈ s, MeasurableSet (id ⁻¹' {y}) := by
    intro y hy
    simp [MeasurableSet.singleton y]
  calc
    μ s = μ (id ⁻¹' s) := by simp
    _ = ∑' (b : s), μ (id ⁻¹' {↑b}) := by
      rw [MeasureTheory.tsum_measure_preimage_singleton hcount hmeas]
    _ ≤ ∑' (b : s), ν (id ⁻¹' {↑b}) :=
      ENNReal.tsum_le_tsum fun b => h (b : α)
    _ = ν (id ⁻¹' s) := by
      rw [MeasureTheory.tsum_measure_preimage_singleton hcount hmeas]
    _ = ν s := by simp

theorem FrogModel.Engine.map_eq_restrict_add_compl {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (f : Ω → α)
    (hf : Measurable f) : μ.map f = (μ.restrict A).map f + (μ.restrict Aᶜ).map f := by
  calc
    μ.map f = ((μ.restrict A) + (μ.restrict Aᶜ)).map f := by
      rw [MeasureTheory.Measure.restrict_add_restrict_compl (μ := μ) hA]
    _ = (μ.restrict A).map f + (μ.restrict Aᶜ).map f := Measure.map_add _ _ hf

theorem FrogModel.Engine.app_fkKernel_one {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (ν : Measure Ξ) (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y})
    (h : X → ℝ≥0∞) (x : X) :
    FrogModel.LinSys.app (FrogModel.Engine.fkKernel f (fun _ _ => 1) ν) h x =
      ∫⁻ ξ, h (f x ξ) ∂ν := by
  rw [FrogModel.LinSys.app]
  have h_eq := FrogModel.Engine.lintegral_mul_comp_eq_tsum f (fun _ _ => 1) ν hf
    (fun _ => measurable_const) h x
  simp [one_mul] at h_eq
  rw [← h_eq]

theorem FrogModel.LinSys.le_least_of_sub_contract {ι : Type*} (K : ι → ι → ℝ≥0∞)
    (b V g : ι → ℝ≥0∞) (r C : ℝ≥0∞) (h : V ≤ b + FrogModel.LinSys.app K V)
    (hg : FrogModel.LinSys.app K g ≤ fun i => r * g i) (hr : r < 1) (hgfin : ∀ i, g i ≠ ⊤)
    (hC : C ≠ ⊤) (hVg : ∀ i, V i ≤ C * g i) : V ≤ FrogModel.LinSys.least K b := by
  apply FrogModel.LinSys.le_least_of_sub_tendsto K b V h
  intro i
  apply FrogModel.LinSys.tendsto_iter_of_dom K V g C hC hVg i
  apply FrogModel.LinSys.tendsto_iter_of_contract K g r hg hr i (hgfin i)

theorem FrogModel.Engine.lintegral_tsum_traj_eq_least {X Ξ : Type*} [MeasurableSpace Ξ]
    [Countable X] (f : X → Ξ → X) (a : X → Ξ → ℝ≥0∞) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (ha : ∀ x, Measurable (a x)) (x : X) :
    ∫⁻ w, ∑' k, a (FrogModel.Engine.traj f x w k) (w k) ∂(FrogModel.Engine.iidMeasure ν) =
      FrogModel.LinSys.least (FrogModel.Engine.fkKernel f (fun _ _ => 1) ν)
        (FrogModel.Engine.fkRhs a ν) x := by
  have h_tsum_eq_iSup (x : X) (w : ℕ → Ξ) :
    ∑' k, a (FrogModel.Engine.traj f x w k) (w k) =
    ⨆ n, FrogModel.Engine.fk f (fun _ _ => 1) a n x w := by
    calc
      ∑' k, a (FrogModel.Engine.traj f x w k) (w k) = ⨆ n, ∑ k ∈ Finset.range n, a (FrogModel.Engine.traj f x w k) (w k) := by
        rw [ENNReal.tsum_eq_iSup_nat]
      _ = ⨆ n, FrogModel.Engine.fk f (fun _ _ => 1) a n x w := by
        refine iSup_congr fun n => ?_
        exact (FrogModel.Engine.fk_one_eq_sum f a n x w).symm
  calc
    ∫⁻ w, ∑' k, a (FrogModel.Engine.traj f x w k) (w k) ∂(FrogModel.Engine.iidMeasure ν) =
        ∫⁻ w, ⨆ n, FrogModel.Engine.fk f (fun _ _ => 1) a n x w ∂(FrogModel.Engine.iidMeasure ν) := by
      refine MeasureTheory.lintegral_congr fun w => ?_
      exact h_tsum_eq_iSup x w
    _ = FrogModel.LinSys.least (FrogModel.Engine.fkKernel f (fun _ _ => 1) ν)
        (FrogModel.Engine.fkRhs a ν) x :=
      FrogModel.Engine.lintegral_iSup_fk f (fun _ _ => 1) a ν hf (fun _ => measurable_const) ha x

theorem FrogModel.Engine.measurableSet_exists_traj {X Ξ : Type*} [MeasurableSpace Ξ]
    [Countable X] (f : X → Ξ → X) (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y})
    (E : X → Set Ξ) (hE : ∀ y, MeasurableSet (E y)) (x : X) :
    MeasurableSet {w : ℕ → Ξ | ∃ k, w k ∈ E (FrogModel.Engine.traj f x w k)} := by
  have h_eq : {w : ℕ → Ξ | ∃ k, w k ∈ E (FrogModel.Engine.traj f x w k)} =
      ⋃ (k : ℕ), ⋃ (y : X), {w | FrogModel.Engine.traj f x w k = y} ∩ (fun w => w k) ⁻¹' E y := by
    ext w; simp
  rw [h_eq]
  refine MeasurableSet.iUnion fun k => ?_
  refine MeasurableSet.iUnion fun y => ?_
  refine ((FrogModel.Engine.measurableSet_traj_eq f hf x k y).inter ?_)
  have h_meas : Measurable fun (w : ℕ → Ξ) => w k := measurable_pi_apply k
  exact (hE y).preimage h_meas

theorem FrogModel.Engine.measure_exists_traj_eq_least {X Ξ : Type*} [MeasurableSpace Ξ]
    [Countable X] (f : X → Ξ → X) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (E : X → Set Ξ) (hE : ∀ y, MeasurableSet (E y))
    (x : X)
    (huniq : ∀ (w : ℕ → Ξ) (j k : ℕ), w j ∈ E (FrogModel.Engine.traj f x w j) →
      w k ∈ E (FrogModel.Engine.traj f x w k) → j = k) :
    FrogModel.Engine.iidMeasure ν {w | ∃ k, w k ∈ E (FrogModel.Engine.traj f x w k)} =
      FrogModel.LinSys.least (FrogModel.Engine.fkKernel f (fun _ _ => 1) ν)
        (fun y => ν (E y)) x := by
  classical
  set a := fun (y : X) (ξ : Ξ) => (E y).indicator (1 : Ξ → ℝ≥0∞) ξ with ha_def
  have ha_eq : ∀ y ξ, a y ξ ≠ 0 ↔ ξ ∈ E y := by
    intro y ξ
    dsimp [a]
    rw [Set.indicator_apply]
    split_ifs with h
    · simp [h]
    · simp [h]
  have ha_meas : ∀ y, Measurable (a y) := by
    intro y
    exact (measurable_const.indicator (hE y))
  have hfkRhs : fkRhs a ν = fun y => ν (E y) := by
    ext y
    dsimp [fkRhs, a]
    rw [lintegral_indicator_one (hE y)]
  have h_least : ∫⁻ w, ∑' k, a (traj f x w k) (w k) ∂(iidMeasure ν) =
      LinSys.least (fkKernel f (fun _ _ => 1) ν) (fun y => ν (E y)) x := by
    rw [lintegral_tsum_traj_eq_least f a ν hf ha_meas x, hfkRhs]
  have h_pointwise : ∀ w, ∑' k, a (traj f x w k) (w k) =
      ({w | ∃ k, w k ∈ E (traj f x w k)}).indicator (1 : (ℕ → Ξ) → ℝ≥0∞) w := by
    intro w
    have h01 : ∀ k, a (traj f x w k) (w k) = 0 ∨ a (traj f x w k) (w k) = 1 := by
      intro k
      dsimp [a]
      rw [Set.indicator_apply]
      split_ifs with h
      · right; rfl
      · left; rfl
    have huniq' : ∀ j k, a (traj f x w j) (w j) ≠ 0 → a (traj f x w k) (w k) ≠ 0 → j = k := by
      intro j k hj hk
      apply huniq w j k
      · rwa [ha_eq] at hj
      · rwa [ha_eq] at hk
    rw [tsum_eq_ite_of_unique _ h01 huniq']
    rw [Set.indicator_apply]
    by_cases h : ∃ k, a (traj f x w k) (w k) ≠ 0
    · have h_exists : ∃ k, ¬ a (traj f x w k) (w k) = 0 := by
        rcases h with ⟨k, hk⟩
        exact ⟨k, hk⟩
      have h_mem_set : w ∈ {w | ∃ k, w k ∈ E (traj f x w k)} := by
        rcases h with ⟨k, hk⟩
        have hmem : w k ∈ E (traj f x w k) := by rwa [ha_eq] at hk
        exact ⟨k, hmem⟩
      simp [h_exists, h_mem_set]
    · have h_none : ¬ ∃ k, w k ∈ E (traj f x w k) := by
        rintro ⟨k, hk⟩
        apply h
        exact ⟨k, by rwa [ha_eq]⟩
      have h_noexists : ¬ ∃ k, ¬ a (traj f x w k) (w k) = 0 := by
        rintro ⟨k, hk'⟩
        apply h
        exact ⟨k, hk'⟩
      simp [h_noexists, h_none]
  calc
    (iidMeasure ν) {w | ∃ k, w k ∈ E (traj f x w k)}
        = ∫⁻ w, ({w | ∃ k, w k ∈ E (traj f x w k)}).indicator (1 : (ℕ → Ξ) → ℝ≥0∞) w ∂(iidMeasure ν) := by
      rw [lintegral_indicator_one (measurableSet_exists_traj f hf E hE x)]
    _ = ∫⁻ w, ∑' k, a (traj f x w k) (w k) ∂(iidMeasure ν) := by
      apply lintegral_congr
      intro w
      rw [h_pointwise w]
    _ = LinSys.least (fkKernel f (fun _ _ => 1) ν) (fun y => ν (E y)) x := h_least

theorem FrogModel.Engine.lintegral_traj_markov {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (A : X → Ξ → ℝ≥0∞) (hA : ∀ y, Measurable (A y))
    (H : X → (ℕ → Ξ) → ℝ≥0∞) (hH : ∀ y, Measurable (H y)) (x : X) (n : ℕ) :
    ∫⁻ w, A (FrogModel.Engine.traj f x w n) (w n) *
        H (FrogModel.Engine.traj f x w (n + 1)) (fun k => w (n + 1 + k))
        ∂(FrogModel.Engine.iidMeasure ν) =
      ∫⁻ w, A (FrogModel.Engine.traj f x w n) (w n) *
        ∫⁻ w', H (FrogModel.Engine.traj f x w (n + 1)) w' ∂(FrogModel.Engine.iidMeasure ν)
        ∂(FrogModel.Engine.iidMeasure ν) := by
  classical
  set μ := FrogModel.Engine.iidMeasure ν
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, FrogModel.Engine.iidMeasure]
    infer_instance
  -- The extension map from Fin (n+1) → Ξ to ℕ → Ξ
  set ext : (Fin (n+1) → Ξ) → (ℕ → Ξ) := fun p j =>
    if h : j < n + 1 then p ⟨j, h⟩ else p ⟨n, Nat.lt_succ_self n⟩
  have h_ext_meas : Measurable ext := by
    rw [measurable_pi_iff]
    intro j
    dsimp [ext]
    split_ifs with h
    · exact measurable_pi_apply (⟨j, h⟩ : Fin (n+1))
    · exact measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1))
  -- Define S(w) = A(traj_n)(w n) and T(w) = traj_{n+1}
  set S := fun (w : ℕ → Ξ) => A (FrogModel.Engine.traj f x w n) (w n) with hS
  set T := fun (w : ℕ → Ξ) => FrogModel.Engine.traj f x w (n + 1) with hT
  -- Decompose S(w) = ∑' z, indicator(traj_n = z) * A z (w n)
  have h_S_decomp (w : ℕ → Ξ) : S w = ∑' z : X,
      (if FrogModel.Engine.traj f x w n = z then A z (w n) else 0) := by
    dsimp [S]
    calc
      A (FrogModel.Engine.traj f x w n) (w n) =
          ∑' z : X, (if z = FrogModel.Engine.traj f x w n then A z (w n) else 0) := by
        rw [tsum_ite_eq (FrogModel.Engine.traj f x w n) (fun z => A z (w n))]
      _ = ∑' z : X, (if FrogModel.Engine.traj f x w n = z then A z (w n) else 0) := by
        refine tsum_congr fun z => ?_
        simp [eq_comm]
  -- Measurability of S
  have h_S_meas : Measurable S := by
    dsimp [S]
    -- Use the decomposition
    rw [show (fun w : ℕ → Ξ => A (FrogModel.Engine.traj f x w n) (w n)) =
        fun w => ∑' z : X, (if FrogModel.Engine.traj f x w n = z then A z (w n) else 0) from by
      ext w; exact h_S_decomp w]
    refine Measurable.tsum fun z => ?_
    have h_set_meas : MeasurableSet {w : ℕ → Ξ | FrogModel.Engine.traj f x w n = z} :=
      FrogModel.Engine.measurableSet_traj_eq f hf x n z
    have h_indicator : Measurable fun (w : ℕ → Ξ) =>
      (if FrogModel.Engine.traj f x w n = z then (1 : ℝ≥0∞) else 0) :=
      Measurable.indicator (measurable_const : Measurable fun (_ : ℕ → Ξ) => (1 : ℝ≥0∞)) h_set_meas
    have h_Az_meas : Measurable fun (w : ℕ → Ξ) => A z (w n) :=
      (hA z).comp (measurable_pi_apply n)
    have h_term : Measurable fun (w : ℕ → Ξ) =>
      (if FrogModel.Engine.traj f x w n = z then A z (w n) else 0) := by
      have : (fun (w : ℕ → Ξ) => (if FrogModel.Engine.traj f x w n = z then A z (w n) else 0)) =
          (fun w => (if FrogModel.Engine.traj f x w n = z then (1 : ℝ≥0∞) else 0) * A z (w n)) := by
        ext w; split_ifs <;> simp
      rw [this]
      exact Measurable.mul h_indicator h_Az_meas
    exact h_term
  -- The shift map
  set shift := fun (w : ℕ → Ξ) => fun k => w (n + 1 + k) with hshift
  have h_shift_meas : Measurable shift := by
    rw [measurable_pi_iff]
    intro k
    dsimp [shift]
    exact measurable_pi_apply (n + 1 + k)
  -- Decompose the left integrand
  have h_left_decomp (w : ℕ → Ξ) : S w * H (T w) (shift w) =
      ∑' y : X, (if T w = y then S w * H y (shift w) else 0) := by
    calc
      S w * H (T w) (shift w) =
          ∑' y : X, (if y = T w then S w * H y (shift w) else 0) := by
        rw [tsum_ite_eq (T w) (fun y => S w * H y (shift w))]
      _ = ∑' y : X, (if T w = y then S w * H y (shift w) else 0) := by
        refine tsum_congr fun y => ?_
        simp [eq_comm]
  -- Decompose the right integrand
  have h_right_decomp (w : ℕ → Ξ) : S w * ∫⁻ w', H (T w) w' ∂μ =
      ∑' y : X, (if T w = y then S w * (∫⁻ w', H y w' ∂μ) else 0) := by
    calc
      S w * ∫⁻ w', H (T w) w' ∂μ =
          ∑' y : X, (if y = T w then S w * (∫⁻ w', H y w' ∂μ) else 0) := by
        rw [tsum_ite_eq (T w) (fun y => S w * (∫⁻ w', H y w' ∂μ))]
      _ = ∑' y : X, (if T w = y then S w * (∫⁻ w', H y w' ∂μ) else 0) := by
        refine tsum_congr fun y => ?_
        simp [eq_comm]
  -- For each y, define F_y on Fin (n+1) → Ξ
  set F : X → (Fin (n+1) → Ξ) → ℝ≥0∞ := fun y p =>
    (if FrogModel.Engine.traj f x (ext p) (n + 1) = y then 1 else 0) *
    A (FrogModel.Engine.traj f x (ext p) n) (p ⟨n, Nat.lt_succ_self n⟩)
  -- Measurability of F y
  have hF_meas (y : X) : Measurable (F y) := by
    have h_indicator : Measurable fun (p : Fin (n+1) → Ξ) =>
      (if FrogModel.Engine.traj f x (ext p) (n + 1) = y then (1 : ℝ≥0∞) else 0) := by
      have h_set_meas : MeasurableSet {p : Fin (n+1) → Ξ |
        FrogModel.Engine.traj f x (ext p) (n + 1) = y} := by
        have h_fiber_meas : MeasurableSet {w : ℕ → Ξ |
          FrogModel.Engine.traj f x w (n + 1) = y} :=
          FrogModel.Engine.measurableSet_traj_eq f hf x (n + 1) y
        exact h_fiber_meas.preimage h_ext_meas
      exact Measurable.indicator (measurable_const : Measurable fun (_ : Fin (n+1) → Ξ) => (1 : ℝ≥0∞)) h_set_meas
    have h_A_meas : Measurable fun (p : Fin (n+1) → Ξ) =>
      A (FrogModel.Engine.traj f x (ext p) n) (p ⟨n, Nat.lt_succ_self n⟩) := by
      have h_eq : (fun (p : Fin (n+1) → Ξ) =>
        A (FrogModel.Engine.traj f x (ext p) n) (p ⟨n, Nat.lt_succ_self n⟩)) =
        fun p => ∑' z : X,
          (if FrogModel.Engine.traj f x (ext p) n = z then A z (p ⟨n, Nat.lt_succ_self n⟩) else 0) := by
        ext p
        calc
          A (FrogModel.Engine.traj f x (ext p) n) (p ⟨n, Nat.lt_succ_self n⟩) =
              ∑' z : X, (if z = FrogModel.Engine.traj f x (ext p) n then A z (p ⟨n, Nat.lt_succ_self n⟩) else 0) := by
            rw [tsum_ite_eq (FrogModel.Engine.traj f x (ext p) n)
              (fun z => A z (p ⟨n, Nat.lt_succ_self n⟩))]
          _ = ∑' z : X, (if FrogModel.Engine.traj f x (ext p) n = z then A z (p ⟨n, Nat.lt_succ_self n⟩) else 0) := by
            refine tsum_congr fun z => ?_
            simp [eq_comm]
      rw [h_eq]
      refine Measurable.tsum fun z => ?_
      have h_set_meas_z : MeasurableSet {p : Fin (n+1) → Ξ |
        FrogModel.Engine.traj f x (ext p) n = z} := by
        have h_fiber_meas_z : MeasurableSet {w : ℕ → Ξ |
          FrogModel.Engine.traj f x w n = z} :=
          FrogModel.Engine.measurableSet_traj_eq f hf x n z
        exact h_fiber_meas_z.preimage h_ext_meas
      have h_proj_meas : Measurable fun (p : Fin (n+1) → Ξ) => p ⟨n, Nat.lt_succ_self n⟩ :=
        measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1))
      have h_Az_meas : Measurable fun (p : Fin (n+1) → Ξ) => A z (p ⟨n, Nat.lt_succ_self n⟩) :=
        (hA z).comp h_proj_meas
      exact Measurable.indicator h_Az_meas h_set_meas_z
    dsimp [F]
    refine Measurable.mul h_indicator ?_
    exact h_A_meas
  -- Key identity: ∫ F_y(prefix) * H_y(shift) = (∫ F_y) * (∫ H_y)
  have h_main (y : X) : ∫⁻ w, F y (fun j : Fin (n+1) => w j) * H y (shift w) ∂μ =
      (∫⁻ p : Fin (n+1) → Ξ, F y p ∂(Measure.pi fun _ : Fin (n+1) => ν)) *
      ∫⁻ w', H y w' ∂μ := by
    exact FrogModel.Engine.lintegral_prefix_shift ν (n+1) (F y) (H y) (hF_meas y) (hH y)
  -- Identity with G = 1
  have h_one (y : X) : (∫⁻ p : Fin (n+1) → Ξ, F y p ∂(Measure.pi fun _ : Fin (n+1) => ν)) =
      ∫⁻ w, F y (fun j : Fin (n+1) => w j) ∂μ := by
    have h_one_meas : Measurable (fun (_ : ℕ → Ξ) => (1 : ℝ≥0∞)) := measurable_const
    calc
      (∫⁻ p : Fin (n+1) → Ξ, F y p ∂(Measure.pi fun _ : Fin (n+1) => ν)) =
          (∫⁻ p : Fin (n+1) → Ξ, F y p ∂(Measure.pi fun _ : Fin (n+1) => ν)) * 1 := by simp
      _ = (∫⁻ p : Fin (n+1) → Ξ, F y p ∂(Measure.pi fun _ : Fin (n+1) => ν)) *
          ∫⁻ w', (1 : (ℕ → Ξ) → ℝ≥0∞) w' ∂μ := by simp [IsProbabilityMeasure.measure_univ (μ := μ)]
      _ = ∫⁻ w, F y (fun j : Fin (n+1) => w j) * (1 : (ℕ → Ξ) → ℝ≥0∞) (shift w) ∂μ := by
        simpa [shift] using
          (FrogModel.Engine.lintegral_prefix_shift ν (n+1) (F y) (fun _ => (1 : ℝ≥0∞)) (hF_meas y) h_one_meas).symm
      _ = ∫⁻ w, F y (fun j : Fin (n+1) => w j) * 1 ∂μ := by simp
      _ = ∫⁻ w, F y (fun j : Fin (n+1) => w j) ∂μ := by simp
  -- Relate F_y(prefix) to indicator * S
  have h_F_prefix (y : X) (w : ℕ → Ξ) : F y (fun j : Fin (n+1) => w j) = (if T w = y then S w else 0) := by
    dsimp [F, S, T]
    have h_ext_eq : ∀ j, j < n + 1 → (ext (fun i : Fin (n+1) => w i)) j = w j := by
      intro j hj
      dsimp [ext]
      simp [hj]
    have h_traj_n_eq : FrogModel.Engine.traj f x (ext (fun i : Fin (n+1) => w i)) n =
        FrogModel.Engine.traj f x w n := by
      apply FrogModel.Engine.traj_congr_prefix f x (ext (fun i : Fin (n+1) => w i)) w n
      intro j hj
      apply h_ext_eq j (Nat.lt_succ_of_lt hj)
    have h_traj_n1_eq : FrogModel.Engine.traj f x (ext (fun i : Fin (n+1) => w i)) (n + 1) =
        FrogModel.Engine.traj f x w (n + 1) := by
      apply FrogModel.Engine.traj_congr_prefix f x (ext (fun i : Fin (n+1) => w i)) w (n+1)
      intro j hj
      apply h_ext_eq j hj
    rw [h_traj_n1_eq, h_traj_n_eq]
    split_ifs <;> simp
  calc
    ∫⁻ w, S w * H (T w) (shift w) ∂μ
        = ∫⁻ w, (∑' y : X, (if T w = y then S w * H y (shift w) else 0)) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with w
      rw [h_left_decomp w]
    _ = ∑' y : X, ∫⁻ w, (if T w = y then S w * H y (shift w) else 0) ∂μ := by
      rw [lintegral_tsum]
      intro y
      have h_set_meas : MeasurableSet {w : ℕ → Ξ | T w = y} := by
        dsimp [T]
        exact FrogModel.Engine.measurableSet_traj_eq f hf x (n + 1) y
      have h_indicator_meas : Measurable fun w : ℕ → Ξ => (if T w = y then (1 : ℝ≥0∞) else 0) :=
        Measurable.indicator (measurable_const : Measurable fun (_ : ℕ → Ξ) => (1 : ℝ≥0∞)) h_set_meas
      have h_H_meas : Measurable fun w : ℕ → Ξ => H y (shift w) :=
        (hH y).comp h_shift_meas
      have h_prod : Measurable fun w : ℕ → Ξ =>
        (if T w = y then (1 : ℝ≥0∞) else 0) * S w * H y (shift w) :=
        Measurable.mul (Measurable.mul h_indicator_meas h_S_meas) h_H_meas
      have h_eq : (fun w : ℕ → Ξ => (if T w = y then (1 : ℝ≥0∞) else 0) * S w * H y (shift w)) =
          fun w => (if T w = y then S w * H y (shift w) else 0) := by
        ext w; split_ifs <;> simp
      rw [← h_eq]
      exact h_prod.aemeasurable
    _ = ∑' y : X, ∫⁻ w, F y (fun j : Fin (n+1) => w j) * H y (shift w) ∂μ := by
      refine tsum_congr fun y => ?_
      refine lintegral_congr_ae ?_
      filter_upwards with w
      rw [h_F_prefix y w]
      split_ifs <;> simp
    _ = ∑' y : X, ((∫⁻ p : Fin (n+1) → Ξ, F y p ∂(Measure.pi fun _ : Fin (n+1) => ν)) *
        ∫⁻ w', H y w' ∂μ) := by
      refine tsum_congr fun y => ?_
      simpa using h_main y
    _ = ∑' y : X, ((∫⁻ w, F y (fun j : Fin (n+1) => w j) ∂μ) * ∫⁻ w', H y w' ∂μ) := by
      refine tsum_congr fun y => ?_
      rw [← h_one y]
    _ = ∑' y : X, ((∫⁻ w, (if T w = y then S w else 0) ∂μ) * ∫⁻ w', H y w' ∂μ) := by
      refine tsum_congr fun y => ?_
      have h_eq := h_F_prefix y
      -- h_eq : ∀ w, F y (fun j => w ↑j) = if T w = y then S w else 0
      simp [h_eq]
    _ = ∑' y : X, ∫⁻ w, (if T w = y then S w else 0) * (∫⁻ w', H y w' ∂μ) ∂μ := by
      refine tsum_congr fun y => ?_
      have h_meas : Measurable fun w : ℕ → Ξ => (if T w = y then S w else 0) := by
        have h_set_meas' : MeasurableSet {w : ℕ → Ξ | T w = y} := by
          dsimp [T]
          exact FrogModel.Engine.measurableSet_traj_eq f hf x (n + 1) y
        have h_indicator_meas' : Measurable fun w : ℕ → Ξ => (if T w = y then (1 : ℝ≥0∞) else 0) :=
          Measurable.indicator (measurable_const : Measurable fun (_ : ℕ → Ξ) => (1 : ℝ≥0∞)) h_set_meas'
        have h_eq' : (fun w : ℕ → Ξ => (if T w = y then S w else 0)) =
            fun w => (if T w = y then (1 : ℝ≥0∞) else 0) * S w := by
          ext w; split_ifs <;> simp
        rw [h_eq']
        exact Measurable.mul h_indicator_meas' h_S_meas
      rw [← lintegral_mul_const (∫⁻ w', H y w' ∂μ) h_meas]
    _ = ∫⁻ w, (∑' y : X, (if T w = y then S w * (∫⁻ w', H y w' ∂μ) else 0)) ∂μ := by
      rw [lintegral_tsum]
      · refine tsum_congr fun y => lintegral_congr fun w => ?_
        split_ifs <;> simp
      intro y
      have h_set_meas_y : MeasurableSet {w : ℕ → Ξ | T w = y} := by
        dsimp [T]
        exact FrogModel.Engine.measurableSet_traj_eq f hf x (n + 1) y
      have h_indicator_meas_y : Measurable fun w : ℕ → Ξ => (if T w = y then (1 : ℝ≥0∞) else 0) :=
        Measurable.indicator (measurable_const : Measurable fun (_ : ℕ → Ξ) => (1 : ℝ≥0∞)) h_set_meas_y
      have h_const_meas : Measurable fun _ : ℕ → Ξ => ∫⁻ w', H y w' ∂μ := measurable_const
      have h_eq_y : (fun w : ℕ → Ξ => (if T w = y then S w * (∫⁻ w', H y w' ∂μ) else 0)) =
          fun w => (if T w = y then (1 : ℝ≥0∞) else 0) * S w * (∫⁻ w', H y w' ∂μ) := by
        ext w; split_ifs <;> simp
      rw [h_eq_y]
      exact (Measurable.mul (Measurable.mul h_indicator_meas_y h_S_meas) h_const_meas).aemeasurable
    _ = ∫⁻ w, S w * (∫⁻ w', H (T w) w' ∂μ) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with w
      rw [h_right_decomp w]
    _ = ∫⁻ w, A (FrogModel.Engine.traj f x w n) (w n) *
        ∫⁻ w', H (FrogModel.Engine.traj f x w (n + 1)) w' ∂(FrogModel.Engine.iidMeasure ν)
        ∂(FrogModel.Engine.iidMeasure ν) := by rfl

theorem FrogModel.Engine.rstep_outInv {S U : Type*} {d J : ℕ} (cstep : S → U → ℕ × S)
    (x : FrogModel.Engine.RState S d J) (ξ : Fin (d + 1) × U)
    (hx : Monotone x.out ∧ (∀ k : Fin J, (k : ℕ) < x.i → x.out k ≤ x.e) ∧
      ∀ k : Fin J, x.i ≤ k → x.out k = ⊤) :
    Monotone (FrogModel.Engine.rstep cstep x ξ).out ∧
      (∀ k : Fin J, (k : ℕ) < (FrogModel.Engine.rstep cstep x ξ).i →
        (FrogModel.Engine.rstep cstep x ξ).out k ≤ (FrogModel.Engine.rstep cstep x ξ).e) ∧
      ∀ k : Fin J, (FrogModel.Engine.rstep cstep x ξ).i ≤ k →
        (FrogModel.Engine.rstep cstep x ξ).out k = ⊤ := by
  rcases hx with ⟨hmono, hlt, heq⟩
  by_cases h_lt_J : x.i < J
  · -- x.i < J: rstep does something
    simp [FrogModel.Engine.rstep, h_lt_J]
    by_cases hp0 : (FrogModel.Engine.move cstep x ξ.1 ξ.2).2.1 = 0
    · -- frog finishes: new state has updated output
      simp [hp0]
      have hx_le_e' : (x.e : ℕ∞) ≤ ((FrogModel.Engine.move cstep x ξ.1 ξ.2).1 : ℕ∞) := by
        unfold FrogModel.Engine.move
        split
        · simp
        · simp
      refine ⟨?_, ?_, ?_⟩
      · -- Monotone (Function.update x.out ⟨x.i, h_lt_J⟩ (move ...).1)
        intro a b hle
        have hle_val : (a : ℕ) ≤ (b : ℕ) := Fin.le_iff_val_le_val.mp hle
        by_cases ha_lt : (a : ℕ) < x.i
        · by_cases hb_lt : (b : ℕ) < x.i
          · -- both < x.i
            have ha_ne : a ≠ ⟨x.i, h_lt_J⟩ := by
              intro heq'; have : (a : ℕ) = x.i := Fin.ext_iff.mp heq'; linarith
            have hb_ne : b ≠ ⟨x.i, h_lt_J⟩ := by
              intro heq'; have : (b : ℕ) = x.i := Fin.ext_iff.mp heq'; linarith
            simp [ha_ne, hb_ne]
            exact hmono hle
          · -- a < x.i, b ≥ x.i
            have hb_ge : x.i ≤ (b : ℕ) := by omega
            have hb_fin : (⟨x.i, h_lt_J⟩ : Fin J) ≤ b :=
              Fin.le_iff_val_le_val.mpr hb_ge
            by_cases hb_eq_val : (b : ℕ) = x.i
            · -- b = x.i
              have hb_eq_fin : b = ⟨x.i, h_lt_J⟩ := Fin.ext hb_eq_val
              subst hb_eq_fin
              have ha_ne : a ≠ ⟨x.i, h_lt_J⟩ := by
                intro heq'; have : (a : ℕ) = x.i := Fin.ext_iff.mp heq'; linarith
              simp [ha_ne]
              exact le_trans (hlt a ha_lt) hx_le_e'
            · -- b > x.i
              have hb_ne : b ≠ ⟨x.i, h_lt_J⟩ := by
                intro heq'; have : (b : ℕ) = x.i := Fin.ext_iff.mp heq'; exact hb_eq_val this
              have ha_ne : a ≠ ⟨x.i, h_lt_J⟩ := by
                intro heq'; have : (a : ℕ) = x.i := Fin.ext_iff.mp heq'; linarith
              simp [ha_ne, hb_ne]
              have htop : x.out b = ⊤ := heq b hb_fin
              simp [htop]
        · -- a ≥ x.i
          have ha_ge : x.i ≤ (a : ℕ) := by omega
          have ha_fin : (⟨x.i, h_lt_J⟩ : Fin J) ≤ a :=
            Fin.le_iff_val_le_val.mpr ha_ge
          by_cases ha_eq_val : (a : ℕ) = x.i
          · -- a = x.i
            have ha_eq_fin : a = ⟨x.i, h_lt_J⟩ := Fin.ext ha_eq_val
            subst ha_eq_fin
            by_cases hb_lt : (b : ℕ) < x.i
            · omega
            · -- b ≥ x.i
              have hb_ge : x.i ≤ (b : ℕ) := by omega
              have hb_fin : (⟨x.i, h_lt_J⟩ : Fin J) ≤ b :=
                Fin.le_iff_val_le_val.mpr hb_ge
              by_cases hb_eq_val : (b : ℕ) = x.i
              · -- b = x.i, so a = b
                have hb_eq_fin : b = ⟨x.i, h_lt_J⟩ := Fin.ext hb_eq_val
                subst hb_eq_fin
                simp
              · -- b > x.i
                have hb_ne : b ≠ ⟨x.i, h_lt_J⟩ := by
                  intro heq'; have : (b : ℕ) = x.i := Fin.ext_iff.mp heq'; exact hb_eq_val this
                simp [hb_ne]
                have htop : x.out b = ⊤ := heq b hb_fin
                simp [htop]
          · -- a > x.i
            have ha_ne : a ≠ ⟨x.i, h_lt_J⟩ := by
              intro heq'; have : (a : ℕ) = x.i := Fin.ext_iff.mp heq'; exact ha_eq_val this
            have hb_ge : x.i ≤ (b : ℕ) := by
              have : (a : ℕ) ≤ (b : ℕ) := hle_val
              omega
            have hb_fin : (⟨x.i, h_lt_J⟩ : Fin J) ≤ b :=
              Fin.le_iff_val_le_val.mpr hb_ge
            by_cases hb_eq_val : (b : ℕ) = x.i
            · omega
            · -- b > x.i
              have hb_ne : b ≠ ⟨x.i, h_lt_J⟩ := by
                intro heq'; have : (b : ℕ) = x.i := Fin.ext_iff.mp heq'; exact hb_eq_val this
              simp [ha_ne, hb_ne]
              have htop_a : x.out a = ⊤ := heq a ha_fin
              have htop_b : x.out b = ⊤ := heq b hb_fin
              simp [htop_a, htop_b]
      · -- ∀ k, (k : ℕ) < x.i + 1 → (Function.update ...) k ≤ (move ...).1
        intro k hk
        by_cases hk_lt : (k : ℕ) < x.i
        · have hk_ne : k ≠ ⟨x.i, h_lt_J⟩ := by
            intro heq'; have : (k : ℕ) = x.i := Fin.ext_iff.mp heq'; linarith
          simp [hk_ne]
          exact le_trans (hlt k hk_lt) hx_le_e'
        · -- (k : ℕ) = x.i
          have hk_eq : (k : ℕ) = x.i := by omega
          have hk_eq_fin : k = ⟨x.i, h_lt_J⟩ := Fin.ext hk_eq
          subst hk_eq_fin
          simp
      · -- ∀ k, x.i + 1 ≤ k → (Function.update ...) k = ⊤
        intro k hk
        have hk_ge : x.i + 1 ≤ (k : ℕ) := hk
        have hx_le_k : x.i ≤ (k : ℕ) := by omega
        have hx_fin_le_k : (⟨x.i, h_lt_J⟩ : Fin J) ≤ k :=
          Fin.le_iff_val_le_val.mpr hx_le_k
        have hk_ne : k ≠ ⟨x.i, h_lt_J⟩ := by
          intro heq'; have : (k : ℕ) = x.i := Fin.ext_iff.mp heq'; omega
        simp [hk_ne, heq k hx_fin_le_k]
    · -- frog doesn't finish: state unchanged
      simp [hp0]
      have hx_le_e' : (x.e : ℕ∞) ≤ ((FrogModel.Engine.move cstep x ξ.1 ξ.2).1 : ℕ∞) := by
        unfold FrogModel.Engine.move
        split
        · simp
        · simp
      refine ⟨hmono, ?_, ?_⟩
      · intro k hk
        exact le_trans (hlt k hk) hx_le_e'
      · intro k hk
        have hk_fin : (⟨x.i, h_lt_J⟩ : Fin J) ≤ k :=
          Fin.le_iff_val_le_val.mpr hk
        exact heq k hk_fin
  · -- x.i ≥ J: rstep returns x
    simp [FrogModel.Engine.rstep, h_lt_J]
    exact ⟨hmono, hlt, heq⟩

theorem FrogModel.Engine.monotone_recOut {S : Type*} {d J : ℕ}
    (t : ℕ → FrogModel.Engine.RState S d J) (ht : ∀ n, Monotone (t n).out) :
    Monotone (FrogModel.Engine.recOut t) := by
  intro k k' hkk'
  unfold FrogModel.Engine.recOut
  apply iInf_mono
  intro n
  exact ht n hkk'
