module

public import FrogModel.Pool.Read

@[expose] public section

/-!
# Pools: the sequence law and the one-step kernel (Lemma 4.3 of the paper)

- `measure_ext_of_prefix`: two finite measures on `ℕ → E` with the same laws of the first `n`
  coordinates for every `n` are equal.
- `map_prod_eq_bind`: the image of a product measure under `F` is the first factor bound with
  the kernel `a ↦ ν.map (F (a, ·))`.
- On the fresh space the first `n` pieces and the row `i ↦ ω (n, i)` are independent
  (`indepFun_freshRead_row`), the row has law `infinitePi μ` (`map_row_freshMeasure`), and piece
  `n + 1` is the row at the label of the first `n` (`freshRead_succ_eq`).
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.Pool


/-- Two finite measures on `ℕ → E` with the same laws of the first `n` coordinates for every `n`
are equal. -/
theorem measure_ext_of_prefix {E : Type*} [MeasurableSpace E] {ν ν' : Measure (ℕ → E)} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : ∀ n : ℕ, ν.map (fun x (j : Fin n) => x j) = ν'.map (fun x (j : Fin n) => x j)) :
    ν = ν' := by
  -- Define the projective family P from ν
  let P : (I : Finset ℕ) → Measure ((i : I) → E) := fun I => ν.map (Finset.restrict I)
  have hP_proj : IsProjectiveMeasureFamily (α := fun _ => E) P := by
    intro I J hJI
    dsimp [P]
    rw [Measure.map_map (Finset.measurable_restrict₂ hJI) (Finset.measurable_restrict I)]
    rfl
  have hν_proj : IsProjectiveLimit ν P := by
    intro I
    rfl
  have hν'_proj : IsProjectiveLimit ν' P := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff (X := fun _ => E) hP_proj ν']
    intro n
    dsimp [P]
    -- We need: ν'.map (frestrictLe n) = ν.map (frestrictLe n)
    -- Define the prefix function and the reindexing function inline
    have h_eq : (Preorder.frestrictLe n : (ℕ → E) → (Finset.Iic n → E)) =
      (fun (y : Fin (n+1) → E) (i : Finset.Iic n) => y ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩) ∘
      (fun (x : ℕ → E) (j : Fin (n+1)) => x (j.val)) := by
      ext x i
      rfl
    have h_meas_prefix : Measurable (fun (x : ℕ → E) (j : Fin (n+1)) => x (j.val)) := by
      rw [measurable_pi_iff]
      intro j
      simpa using measurable_pi_apply (j.val : ℕ)
    have h_meas_g : Measurable (fun (y : Fin (n+1) → E) (i : Finset.Iic n) => y ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩) := by
      rw [measurable_pi_iff]
      intro i
      simpa using measurable_pi_apply (⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩ : Fin (n+1))
    calc
      ν'.map (Preorder.frestrictLe n) = ν'.map ((fun (y : Fin (n+1) → E) (i : Finset.Iic n) => y ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩) ∘
        (fun (x : ℕ → E) (j : Fin (n+1)) => x (j.val))) := by rw [h_eq]
      _ = (ν'.map (fun (x : ℕ → E) (j : Fin (n+1)) => x (j.val))).map
        (fun (y : Fin (n+1) → E) (i : Finset.Iic n) => y ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩) := by
        rw [Measure.map_map h_meas_g h_meas_prefix]
      _ = (ν.map (fun (x : ℕ → E) (j : Fin (n+1)) => x (j.val))).map
        (fun (y : Fin (n+1) → E) (i : Finset.Iic n) => y ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩) := by rw [h (n+1)]
      _ = ν.map ((fun (y : Fin (n+1) → E) (i : Finset.Iic n) => y ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩) ∘
        (fun (x : ℕ → E) (j : Fin (n+1)) => x (j.val))) := by
        rw [Measure.map_map h_meas_g h_meas_prefix]
      _ = ν.map (Preorder.frestrictLe n) := by rw [h_eq]
  exact (MeasureTheory.IsProjectiveLimit.unique hν_proj hν'_proj)

/-- The image of a product measure under a measurable `F` is the first factor bound with the
kernel `a ↦ ν.map (F (a, ·))`. -/
theorem map_prod_eq_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite ν] {F : α × β → γ}
    (hF : Measurable F) :
    (μ.prod ν).map F = μ.bind fun a => ν.map fun b => F (a, b) := by
  ext s hs
  have hFs : MeasurableSet (F ⁻¹' s) := hF hs
  have hκmeas : AEMeasurable (fun a => ν.map fun b => F (a, b)) μ := by
    have hmeas : Measurable (fun a => ν.map fun b => F (a, b)) := by
      refine Measure.measurable_of_measurable_coe _ ?_
      intro t ht
      have h_eq : (fun a => (ν.map fun b => F (a, b)) t) = (fun a => ν (Prod.mk a ⁻¹' (F ⁻¹' t))) := by
        ext a
        calc
          (ν.map fun b => F (a, b)) t = (ν.map (F ∘ Prod.mk a)) t := rfl
          _ = ν ((F ∘ Prod.mk a) ⁻¹' t) := by
            rw [Measure.map_apply (μ := ν) (hF.comp (measurable_prodMk_left (x := a))) ht]
          _ = ν (Prod.mk a ⁻¹' (F ⁻¹' t)) := by rw [Set.preimage_comp]
      rw [h_eq]
      exact measurable_measure_prodMk_left (hF ht)
    exact hmeas.aemeasurable
  calc
    ((μ.prod ν).map F) s = (μ.prod ν) (F ⁻¹' s) := by rw [Measure.map_apply hF hs]
    _ = ∫⁻ a, ν (Prod.mk a ⁻¹' (F ⁻¹' s)) ∂μ := by rw [Measure.prod_apply hFs]
    _ = ∫⁻ a, (ν.map fun b => F (a, b)) s ∂μ := by
      refine lintegral_congr ?_
      intro a
      calc
        ν (Prod.mk a ⁻¹' (F ⁻¹' s)) = ν ((F ∘ Prod.mk a) ⁻¹' s) := by rw [Set.preimage_comp]
        _ = (ν.map (F ∘ Prod.mk a)) s := by
          rw [Measure.map_apply (μ := ν) (hF.comp (measurable_prodMk_left (x := a))) hs]
        _ = (ν.map fun b => F (a, b)) s := rfl
    _ = (μ.bind fun a => ν.map fun b => F (a, b)) s := by rw [Measure.bind_apply hs hκmeas]

/-- Reading a row at the label of the pieces before is measurable. -/
theorem measurable_snoc_apply_sel {I E : Type*} [MeasurableSpace E] [Countable I] (n : ℕ) (s : (Fin n → E) → I)
    (hs : ∀ i : I, MeasurableSet {y : Fin n → E | s y = i}) :
    Measurable fun x : (Fin n → E) × (I → E) => Fin.snoc (α := fun _ => E) x.1 (x.2 (s x.1)) := by
  have hg : Measurable fun x : (Fin n → E) × (I → E) => x.2 (s x.1) := by
    intro U hU
    have h_eq : (fun x : (Fin n → E) × (I → E) => x.2 (s x.1)) ⁻¹' U =
      ⋃ i : I, ({y : Fin n → E | s y = i} ×ˢ {r : I → E | r i ∈ U}) := by
      ext ⟨y, r⟩
      simp [eq_comm]
    rw [h_eq]
    refine MeasurableSet.iUnion fun i => ?_
    exact (hs i).prod (measurable_pi_apply i hU)
  refine measurable_pi_iff.2 fun j => ?_
  induction' j using Fin.lastCases with i
  · simpa [Fin.snoc_last] using hg
  · have h_cast : Measurable fun x : (Fin n → E) × (I → E) => x.1 i :=
      (measurable_pi_apply i).comp measurable_fst
    simpa [Fin.snoc_castSucc] using h_cast

/-- Piece `n + 1` on the fresh space is row `n` read at the label of the first `n` pieces. -/
theorem freshRead_succ_eq {I E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I) (ω : ℕ × I → E) (n : ℕ) :
    freshRead sel ω (n + 1) =
      Fin.snoc (α := fun _ => E) (freshRead sel ω n) ((fun i => ω (n, i)) (sel n (freshRead sel ω n))) := by
  rfl

/-- Row `n` of the fresh space has law `infinitePi μ`. -/
theorem map_row_freshMeasure {I E : Type*} [MeasurableSpace E] (μ : I → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) :
    (freshMeasure μ).map (fun ω : ℕ × I → E => fun i => ω (n, i)) = Measure.infinitePi μ := by
  unfold freshMeasure
  refine Measure.map_infinitePi_infinitePi_of_inj ?_
  intro a b h
  exact (Prod.mk.inj h).2

/-- On the fresh space the first `n` pieces are independent of row `n`. -/
theorem indepFun_freshRead_row {I E : Type*} [MeasurableSpace E] [Countable I] (μ : I → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (sel : ∀ k : ℕ, (Fin k → E) → I)
    (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) (n : ℕ) :
    IndepFun (fun ω : ℕ × I → E => freshRead sel ω n) (fun ω : ℕ × I → E => fun i => ω (n, i))
      (freshMeasure μ) := by
  -- Define the σ-algebra generated by each coordinate
  let m : ℕ × I → MeasurableSpace (ℕ × I → E) := fun p =>
    MeasurableSpace.comap (fun ω : ℕ × I → E => ω p) inferInstance
  have hm_le : ∀ p, m p ≤ (by infer_instance : MeasurableSpace (ℕ × I → E)) := fun p =>
    Measurable.comap_le (measurable_pi_apply p)
  have h_indep : iIndep m (freshMeasure μ) := by
    have h_fun : iIndepFun (fun i ω => ω i) (freshMeasure μ) := by
      have := iIndepFun_infinitePi (P := fun p : ℕ × I => μ p.2)
        (X := fun (_ : ℕ × I) (x : E) => x) (by
          intro p; exact measurable_id)
      simpa [freshMeasure] using this
    simpa [m, iIndepFun_iff_iIndep (fun _ => inferInstance) (fun i ω => ω i) (freshMeasure μ)] using h_fun
  -- S = coordinates with first component < n, T = coordinates with first component = n
  let S : Set (ℕ × I) := {p | p.1 < n}
  let T : Set (ℕ × I) := {p | p.1 = n}
  have hST : Disjoint S T := by
    refine Set.disjoint_left.mpr fun p hpS hpT => ?_
    have hlt : p.1 < n := hpS
    have heq : p.1 = n := hpT
    linarith
  have h_indep_sup : Indep (⨆ p ∈ S, m p) (⨆ p ∈ T, m p) (freshMeasure μ) :=
    indep_iSup_of_disjoint hm_le h_indep hST
  -- freshRead is measurable w.r.t. ⨆ p ∈ S, m p
  have h_freshRead : Measurable[(⨆ p ∈ S, m p)] fun ω : ℕ × I → E => freshRead sel ω n := by
    have h_eq : (fun ω : ℕ × I → E => freshRead sel ω n) =
        (fun ω : ℕ × I → E => readGen freshCoord sel ω n) :=
      funext fun ω => freshRead_eq_readGen sel ω n
    rw [h_eq]
    apply measurable_readGen_of freshCoord sel hsel n
    intro ℓ j
    have hmem : cmap freshCoord ℓ j ∈ S := by
      dsimp [S, cmap, freshCoord]
      have hval : (j : ℕ) < n := j.2
      simp [hval]
    have h_comap_le : m (cmap freshCoord ℓ j) ≤ ⨆ p ∈ S, m p :=
      le_iSup₂ (f := fun (q : ℕ × I) (_ : q ∈ S) => m q) (cmap freshCoord ℓ j) hmem
    exact Measurable.of_comap_le h_comap_le
  -- Row n is measurable w.r.t. ⨆ p ∈ T, m p
  have h_row : Measurable[(⨆ p ∈ T, m p)] fun ω : ℕ × I → E => fun i => ω (n, i) := by
    rw [measurable_iff_comap_le]
    have h_eq : MeasurableSpace.comap (fun ω : ℕ × I → E => fun i => ω (n, i)) inferInstance =
        ⨆ i : I, m (n, i) := by
      simp [m, MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
        Function.comp_def]
    rw [h_eq]
    refine iSup_le fun i => ?_
    have hmem : (n, i) ∈ T := by
      dsimp [T]
    exact le_iSup₂ (f := fun (q : ℕ × I) (_ : q ∈ T) => m q) (n, i) hmem
  -- Combine using IndepFun_iff_Indep and indep_of_indep_of_le
  rw [IndepFun_iff_Indep]
  have h_comap_freshRead : MeasurableSpace.comap
      (fun ω : ℕ × I → E => freshRead sel ω n) inferInstance ≤ ⨆ p ∈ S, m p :=
    h_freshRead.comap_le
  have h_comap_row : MeasurableSpace.comap
      (fun ω : ℕ × I → E => fun i => ω (n, i)) inferInstance ≤ ⨆ p ∈ T, m p :=
    h_row.comap_le
  exact indep_of_indep_of_le h_indep_sup h_comap_freshRead h_comap_row

end FrogModel.Pool
