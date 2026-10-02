module

public import FrogModel.Engine.Pools
public import FrogModel.Engine.Exact

@[expose] public section

/-!
# The root engine: the inputs read from pools, measurability

Piece `2 t`
of the sequence read in the order of `driveSel` is the direction of step `t` and piece `2 t + 1`
the uniform from the pool of that direction (`poolSeq_driveSel`); a uniform direction exits
infinitely often almost surely (`ae_dirCountN_unbounded`); the outputs `outPsi` and the child
curves are measurable functions of the inputs (`measurable_outPsi`, `measurable_chainCurve`).
-/

open MeasureTheory
open scoped ENNReal

theorem FrogModel.Engine.card_filter_even (t : ℕ) :
    ((Finset.univ : Finset (Fin (2 * t))).filter fun j : Fin (2 * t) =>
      ¬ (j : ℕ) % 2 = 1).card = t := by
  have hcard : (Finset.range t).card = t := Finset.card_range t
  refine (Finset.card_bij (fun (s : ℕ) (hs : s ∈ Finset.range t) =>
    have hs' : s < t := Finset.mem_range.1 hs
    (⟨2 * s, by omega⟩ : Fin (2 * t)))
    ?hi ?inj ?surj).symm.trans hcard
  · -- hi: the image is in the filter set
    intro s hs
    have hs' : s < t := Finset.mem_range.1 hs
    have hfin : (2 * s : ℕ) < 2 * t := by omega
    simp [Finset.mem_filter, Finset.mem_univ]
  · -- inj: injectivity
    intro s₁ hs₁ s₂ hs₂ h
    have hs₁' : s₁ < t := Finset.mem_range.1 hs₁
    have hs₂' : s₂ < t := Finset.mem_range.1 hs₂
    have h_eq : (⟨2 * s₁, by omega⟩ : Fin (2 * t)) = (⟨2 * s₂, by omega⟩ : Fin (2 * t)) := h
    have h_val : (2 * s₁ : ℕ) = (2 * s₂ : ℕ) := by
      have := Fin.ext_iff.1 h_eq
      simpa using this
    omega
  · -- surj: surjectivity
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have h_not_odd : ¬ (j : ℕ) % 2 = 1 := hj
    have h_even : (j : ℕ) % 2 = 0 := by
      have := Nat.mod_two_eq_zero_or_one (j : ℕ)
      rcases this with h | h
      · exact h
      · exact (h_not_odd h).elim
    have h_val : (j : ℕ) = 2 * ((j : ℕ) / 2) := by
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_even)]
    have h_div_lt : (j : ℕ) / 2 < t := by
      have : (j : ℕ) < 2 * t := j.2
      omega
    refine ⟨(j : ℕ) / 2, Finset.mem_range.2 h_div_lt, ?_⟩
    apply Fin.ext
    simp
    rw [← h_val]

theorem FrogModel.Engine.card_filter_odd {α : Type*} [DecidableEq α] (g : ℕ → α) (a : α)
    (t : ℕ) :
    ((Finset.univ : Finset (Fin (2 * t + 1))).filter fun j : Fin (2 * t + 1) =>
        (j : ℕ) % 2 = 1 ∧ g ((j : ℕ) / 2) = a).card =
      ((Finset.range t).filter fun s => g s = a).card := by
  -- Work with the underlying ℕ sets
  let L : Finset (Fin (2 * t + 1)) := (Finset.univ : Finset (Fin (2 * t + 1))).filter fun j =>
    (j : ℕ) % 2 = 1 ∧ g ((j : ℕ) / 2) = a
  let R : Finset ℕ := (Finset.range t).filter fun s => g s = a
  let A : Finset ℕ := L.image Fin.val
  have hA_card : A.card = L.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  rw [← hA_card]
  -- Now we need A.card = R.card
  -- Show A = R.image (fun s => 2*s+1)
  have hA_eq : A = R.image (fun s => 2 * s + 1) := by
    ext j
    constructor
    · intro hj
      rw [Finset.mem_image] at hj
      rcases hj with ⟨j', hj', rfl⟩
      rw [Finset.mem_filter] at hj'
      rcases hj' with ⟨_, ⟨hj'_odd, hj'_g⟩⟩
      -- j' : Fin (2*t+1), and (j' : ℕ) % 2 = 1, g ((j' : ℕ) / 2) = a
      -- We need to show (j' : ℕ) = 2 * s + 1 for some s ∈ R
      have hj'_val_lt : (j' : ℕ) < 2 * t + 1 := j'.2
      have hj'_eq : (j' : ℕ) = 2 * ((j' : ℕ) / 2) + 1 := by
        have := Nat.div_add_mod (j' : ℕ) 2
        omega
      rw [hj'_eq]
      refine Finset.mem_image.2 ⟨(j' : ℕ) / 2, ?_, rfl⟩
      rw [Finset.mem_filter]
      have h_div_lt : (j' : ℕ) / 2 < t := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).2
        omega
      exact ⟨Finset.mem_range.2 h_div_lt, hj'_g⟩
    · intro hj
      rw [Finset.mem_image] at hj
      rcases hj with ⟨s, hs, rfl⟩
      rw [Finset.mem_filter] at hs
      rcases hs with ⟨hs_range, hs_g⟩
      have hs_lt : s < t := Finset.mem_range.1 hs_range
      have h_bound : 2 * s + 1 < 2 * t + 1 := by omega
      -- Need to show (2*s+1) is the val of some Fin in L
      let j' : Fin (2 * t + 1) := ⟨2 * s + 1, h_bound⟩
      have hj'_mem : j' ∈ L := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have h_odd : (2 * s + 1) % 2 = 1 := by omega
        have h_div : g ((2 * s + 1) / 2) = a := by
          have : (2 * s + 1) / 2 = s := by omega
          rw [this, hs_g]
        simpa [j'] using And.intro h_odd h_div
      refine Finset.mem_image.2 ⟨j', hj'_mem, rfl⟩
  have h_inj2 : Function.Injective (fun (s : ℕ) => 2 * s + 1) := by
    intro x y h
    have : 2 * x + 1 = 2 * y + 1 := h
    omega
  rw [hA_eq, Finset.card_image_of_injective _ h_inj2]

/-- The first `m` pieces of a reading of length `n ≥ m` are the reading of length `m`. -/
theorem FrogModel.Engine.take_poolRead {I E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (ω : I × ℕ → E) (n m : ℕ) (h : m ≤ n) :
    Fin.take m h (FrogModel.Pool.poolRead sel ω n) = FrogModel.Pool.poolRead sel ω m := by
  rw [FrogModel.Pool.poolRead_eq_readGen, FrogModel.Pool.poolRead_eq_readGen,
    FrogModel.Pool.take_readGen]

/-- `driveSel k y` is `none` when `k` is even. -/
theorem FrogModel.Engine.driveSel_even {d : ℕ} {U : Type*} (k : ℕ) (hk : ¬ k % 2 = 1)
    (y : Fin k → Fin (d + 1) × U) : FrogModel.Engine.driveSel k y = none := by
  unfold FrogModel.Engine.driveSel; simp [hk]

/-- `driveSel k y` is the direction of the last piece when `k` is odd. -/
theorem FrogModel.Engine.driveSel_odd {d : ℕ} {U : Type*} (k : ℕ) (hk : k % 2 = 1)
    (y : Fin k → Fin (d + 1) × U) :
    FrogModel.Engine.driveSel k y = some (y ⟨k - 1, by omega⟩).1 := by
  unfold FrogModel.Engine.driveSel; simp [hk]

/-- The selector `driveSel` at a past index `j ≤ n`, read from the first `n` pieces: the direction
of piece `j - 1` for `j` odd, `none` for `j` even. -/
theorem FrogModel.Engine.driveSel_take_poolRead {d : ℕ} {U : Type*} [MeasurableSpace U]
    (ω : Option (Fin (d + 1)) × ℕ → Fin (d + 1) × U) (n j : ℕ) (hj : j ≤ n) :
    FrogModel.Engine.driveSel j (Fin.take j hj (FrogModel.Pool.poolRead FrogModel.Engine.driveSel ω n)) =
      if j % 2 = 1 then some (FrogModel.Pool.poolSeq FrogModel.Engine.driveSel ω (j - 1)).1
      else none := by
  rw [FrogModel.Engine.take_poolRead FrogModel.Engine.driveSel ω n j hj]
  by_cases h : j % 2 = 1
  · rw [FrogModel.Engine.driveSel_odd j h, ite_eq_left h,
      ← FrogModel.Pool.prefix_poolSeq FrogModel.Engine.driveSel ω j]
  · rw [FrogModel.Engine.driveSel_even j h, ite_eq_right h]

/-- Piece `2 t` read in the order of `driveSel` is the direction `ω (none, t)` of step `t`, and
piece `2 t + 1` the next unused element of the pool of that direction. -/
theorem FrogModel.Engine.poolSeq_driveSel {d : ℕ} {U : Type*} [MeasurableSpace U]
    (ω : Option (Fin (d + 1)) × ℕ → Fin (d + 1) × U) (t : ℕ) :
    FrogModel.Pool.poolSeq FrogModel.Engine.driveSel ω (2 * t) = ω (none, t) ∧
      FrogModel.Pool.poolSeq FrogModel.Engine.driveSel ω (2 * t + 1) =
        ω (some (FrogModel.Engine.poolDir ω t),
          FrogModel.Engine.dirCountN (FrogModel.Engine.poolDir ω)
            (FrogModel.Engine.poolDir ω t) t) := by
  have heven : ∀ t, FrogModel.Pool.poolSeq FrogModel.Engine.driveSel ω (2 * t) = ω (none, t) := by
    intro t
    show FrogModel.Pool.poolRead FrogModel.Engine.driveSel ω (2 * t + 1) (Fin.last (2 * t)) = _
    rw [FrogModel.Pool.poolRead, Fin.snoc_last, FrogModel.Engine.driveSel_even (2 * t) (by omega)]
    congr 2
    convert FrogModel.Engine.card_filter_even t using 2
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [FrogModel.Engine.driveSel_take_poolRead]
    split_ifs <;> simp_all
  refine ⟨heven t, ?_⟩
  show FrogModel.Pool.poolRead FrogModel.Engine.driveSel ω (2 * t + 1 + 1) (Fin.last (2 * t + 1)) = _
  rw [FrogModel.Pool.poolRead, Fin.snoc_last]
  have h1 : FrogModel.Engine.driveSel (2 * t + 1)
      (FrogModel.Pool.poolRead FrogModel.Engine.driveSel ω (2 * t + 1)) =
        some (FrogModel.Engine.poolDir ω t) := by
    rw [FrogModel.Engine.driveSel_odd (2 * t + 1) (by omega),
      ← FrogModel.Pool.prefix_poolSeq FrogModel.Engine.driveSel ω (2 * t + 1)]
    simp only [Nat.add_sub_cancel, heven t]
    rfl
  rw [h1]
  congr 2
  unfold FrogModel.Engine.dirCountN
  convert FrogModel.Engine.card_filter_odd (FrogModel.Engine.poolDir ω)
    (FrogModel.Engine.poolDir ω t) t using 2
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [FrogModel.Engine.driveSel_take_poolRead]
  split_ifs with h
  · have e : (j : ℕ) - 1 = 2 * ((j : ℕ) / 2) := by omega
    rw [e, heven]
    simp [h, FrogModel.Engine.poolDir]
  · simp [h]

theorem FrogModel.Engine.measurableSet_driveSel {d : ℕ} {U : Type*} [MeasurableSpace U]
    (k : ℕ) (i : Option (Fin (d + 1))) :
    MeasurableSet {y : Fin k → Fin (d + 1) × U | FrogModel.Engine.driveSel k y = i} := by
  by_cases h : k % 2 = 1
  · -- k is odd: driveSel returns some (y ⟨k-1, _⟩).1
    cases i with
    | some a =>
      -- i = some a: the set is {y | (y ⟨k-1, _⟩).1 = a}
      have hm : Measurable fun (y : Fin k → Fin (d + 1) × U) => (y ⟨k - 1, by omega⟩).1 :=
        measurable_fst.comp (measurable_pi_apply _)
      have h_preimage : MeasurableSet {y : Fin k → Fin (d + 1) × U | (y ⟨k - 1, by omega⟩).1 = a} :=
        hm (measurableSet_singleton a)
      have h_eq : {y : Fin k → Fin (d + 1) × U | FrogModel.Engine.driveSel k y = some a} =
          {y : Fin k → Fin (d + 1) × U | (y ⟨k - 1, by omega⟩).1 = a} := by
        ext y; simp [FrogModel.Engine.driveSel, h]
      rw [h_eq]
      exact h_preimage
    | none =>
      -- i = none: driveSel never returns none when k is odd
      have h_empty : {y : Fin k → Fin (d + 1) × U | FrogModel.Engine.driveSel k y = (none : Option (Fin (d + 1)))} = ∅ := by
        ext y
        dsimp [FrogModel.Engine.driveSel]
        simp [h]
      rw [h_empty]
      exact MeasurableSet.empty
  · -- k is even: driveSel returns none for all y
    have h_none : ∀ y : Fin k → Fin (d + 1) × U, FrogModel.Engine.driveSel (d := d) (U := U) k y = (none : Option (Fin (d + 1))) := by
      intro y
      unfold FrogModel.Engine.driveSel
      simp [h]
    cases i with
    | some a =>
      -- i = some a: impossible
      have h_empty : {y : Fin k → Fin (d + 1) × U | FrogModel.Engine.driveSel k y = some a} = ∅ := by
        ext y; simp [h_none y]
      rw [h_empty]
      exact MeasurableSet.empty
    | none =>
      -- i = none: the set is everything
      have h_univ : {y : Fin k → Fin (d + 1) × U | FrogModel.Engine.driveSel k y = none} = Set.univ := by
        ext y; simp [h_none y]
      rw [h_univ]
      exact MeasurableSet.univ

theorem FrogModel.Engine.map_pair_fst_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ((P.prod Q).prod (P.prod Q)).map (fun z => (z.1.1, z.2.2)) = P.prod Q := by
  have h_meas : Measurable (fun (z : (α × β) × (α × β)) => (z.1.1, z.2.2)) :=
    measurable_fst.fst.prodMk measurable_snd.snd
  refine (Measure.prod_eq (μ := P) (ν := Q) fun s t hs ht => ?_).symm
  rw [Measure.map_apply h_meas (hs.prod ht), show (fun (z : (α × β) × (α × β)) => (z.1.1, z.2.2)) ⁻¹' (s ×ˢ t) = (s ×ˢ Set.univ) ×ˢ (Set.univ ×ˢ t) by
    ext z; simp]
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp [IsProbabilityMeasure.measure_univ]

theorem FrogModel.Engine.map_split_pools {ι α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    (Measure.infinitePi fun _ : Option ι × ℕ => P.prod Q).map
        (fun ω => ((fun t : ℕ => (ω (none, t)).1), fun (a : ι) (m : ℕ) => (ω (some a, m)).2)) =
      (Measure.infinitePi fun _ : ℕ => P).prod
        (Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : ℕ => Q) := by
  let R := P.prod Q
  let S := Measure.infinitePi fun _ : ℕ => R
  -- Step 1: reindex with curry
  have hcurry : (Measure.infinitePi fun _ : Option ι × ℕ => R).map
      (MeasurableEquiv.curry (Option ι) ℕ (α × β)) =
      Measure.infinitePi fun i : Option ι => Measure.infinitePi fun j : ℕ => R := by
    simpa using MeasureTheory.Measure.infinitePi_map_curry (μ := fun (_ : Option ι) (j : ℕ) => R)
  have hcurry' : (Measure.infinitePi fun _ : Option ι × ℕ => R).map
      (MeasurableEquiv.curry (Option ι) ℕ (α × β)) =
      Measure.infinitePi fun _ : Option ι => S := by
    simpa [S] using hcurry
  -- Step 2: split Option ι using pair_injective
  have hpair : (Measure.infinitePi fun _ : Option ι => S).map
      (fun ω => (ω none, fun a => ω (some a))) =
      S.prod (Measure.infinitePi fun _ : ι => S) := by
    simpa using FrogModel.infinitePi_map_pair_injective S Option.some (Option.some_injective _) Option.none (fun a => Option.some_ne_none a)
  -- Step 3: project each component
  have hm_fst : Measurable (fun (w : ℕ → α × β) (t : ℕ) => (w t).1) := by
    apply Measurable.of_eval
    intro t
    exact measurable_fst.comp (measurable_pi_apply t)
  have hm_snd : Measurable (fun (v : ι → ℕ → α × β) (a : ι) (m : ℕ) => (v a m).2) := by
    apply Measurable.of_eval
    intro a
    apply Measurable.of_eval
    intro m
    exact measurable_snd.comp ((measurable_pi_apply m).comp (measurable_pi_apply a))
  have hS_fst : Measure.map (fun (w : ℕ → α × β) (t : ℕ) => (w t).1) S = Measure.infinitePi fun _ : ℕ => P := by
    calc
      Measure.map (fun (w : ℕ → α × β) (t : ℕ) => (w t).1) S
          = Measure.infinitePi fun t : ℕ => Measure.map (fun (x : α × β) => x.1) (P.prod Q) := by
        simpa [S, R] using MeasureTheory.Measure.infinitePi_map_pi (μ := fun _ : ℕ => P.prod Q)
          (f := fun (_ : ℕ) (x : α × β) => x.1) (by intro t; exact measurable_fst)
      _ = Measure.infinitePi fun _ : ℕ => P := by
        simp [Measure.map_fst_prod, measure_univ, one_smul]
  have hS_snd : Measure.map (fun (v : ι → ℕ → α × β) (a : ι) (m : ℕ) => (v a m).2)
      (Measure.infinitePi fun _ : ι => S) = Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : ℕ => Q := by
    calc
      Measure.map (fun (v : ι → ℕ → α × β) (a : ι) (m : ℕ) => (v a m).2)
          (Measure.infinitePi fun a : ι => S)
          = Measure.infinitePi fun a : ι => Measure.map (fun (w : ℕ → α × β) (m : ℕ) => (w m).2) S := by
        simpa using MeasureTheory.Measure.infinitePi_map_pi (μ := fun _ : ι => S)
          (f := fun a w m => (w m).2) (by
            intro a
            apply Measurable.of_eval
            intro m
            exact measurable_snd.comp (measurable_pi_apply m))
      _ = Measure.infinitePi fun a : ι => Measure.infinitePi fun m : ℕ => Measure.map (fun (x : α × β) => x.2) (P.prod Q) := by
        simp [S, R, MeasureTheory.Measure.infinitePi_map_pi (μ := fun _ : ℕ => P.prod Q) (f := fun _ x => x.2) (by intro t; exact measurable_snd)]
      _ = Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : ℕ => Q := by
        simp [Measure.map_snd_prod, measure_univ, one_smul]
  -- Step 4: combine using map_prod_map
  let f := fun (w : ℕ → α × β) (t : ℕ) => (w t).1
  let g := fun (v : ι → ℕ → α × β) (a : ι) (m : ℕ) => (v a m).2
  have hm_fg : Measurable (Prod.map f g) := by
    apply Measurable.prod
    · apply Measurable.of_eval
      intro t
      exact measurable_fst.comp ((measurable_pi_apply t).comp measurable_fst)
    · apply Measurable.of_eval
      intro a
      apply Measurable.of_eval
      intro m
      exact measurable_snd.comp ((measurable_pi_apply m).comp ((measurable_pi_apply a).comp measurable_snd))
  have hfinal : (S.prod (Measure.infinitePi fun _ : ι => S)).map (Prod.map f g) =
      (Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : ℕ => Q) := by
    calc
      (S.prod (Measure.infinitePi fun _ : ι => S)).map (Prod.map f g) =
          (Measure.map f S).prod (Measure.map g (Measure.infinitePi fun _ : ι => S)) := by
        symm
        apply MeasureTheory.Measure.map_prod_map S (Measure.infinitePi fun _ : ι => S) hm_fst hm_snd
      _ = (Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : ℕ => Q) := by
        rw [hS_fst, hS_snd]
  -- Now connect everything
  let pair_map := fun (ω : Option ι → ℕ → α × β) => (ω none, fun a => ω (some a))
  have hmeas_cur : Measurable (MeasurableEquiv.curry (Option ι) ℕ (α × β)) :=
    (MeasurableEquiv.curry (Option ι) ℕ (α × β)).measurable
  have hmeas_pair : Measurable pair_map := by
    apply Measurable.prod
    · exact measurable_pi_apply none
    · apply Measurable.of_eval
      intro a
      exact measurable_pi_apply (some a)
  have hmeas_comp : Measurable (pair_map ∘ (MeasurableEquiv.curry (Option ι) ℕ (α × β))) :=
    Measurable.comp hmeas_pair hmeas_cur
  -- verify the composition equality
  have hcomp_eq : (fun ω => ((fun t : ℕ => (ω (none, t)).1), fun (a : ι) (m : ℕ) => (ω (some a, m)).2)) =
      (Prod.map f g) ∘ pair_map ∘ (MeasurableEquiv.curry (Option ι) ℕ (α × β)) := by
    refine funext fun ω => ?_
    simp [f, g, pair_map, MeasurableEquiv.curry_apply, Prod.map]
  rw [hcomp_eq]
  -- Break the composition using measure_map_map
  rw [← Measure.map_map hm_fg hmeas_comp]
  rw [← Measure.map_map hmeas_pair hmeas_cur]
  -- Now the goal is: Measure.map (Prod.map f g) (Measure.map pair_map (Measure.map curry ...)) = ...
  rw [hcurry']
  rw [hpair]
  rw [hfinal]

theorem FrogModel.Engine.map_pi_succ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (R : Measure α) [IsProbabilityMeasure R] (g : α → β) (hg : Measurable g) (d : ℕ) :
    (Measure.infinitePi fun _ : Fin (d + 1) => R).map (fun V (c : Fin d) => g (V c.succ)) =
      Measure.pi fun _ : Fin d => R.map g := by
  have h_succ_inj : Function.Injective (Fin.succ : Fin d → Fin (d + 1)) := by
    intro a b h
    simpa using h
  have h_meas_restrict : Measurable (fun (V : Fin (d + 1) → α) (c : Fin d) => V c.succ) := by
    refine measurable_pi_iff.2 fun c => ?_
    exact measurable_pi_apply (c.succ)
  have h_meas_g_pi : Measurable (fun (W : Fin d → α) (c : Fin d) => g (W c)) := by
    refine measurable_pi_iff.2 fun c => ?_
    exact hg.comp (measurable_pi_apply c)
  have h_comp_eq : ((fun (W : Fin d → α) (c : Fin d) => g (W c)) ∘ (fun (V : Fin (d + 1) → α) (c : Fin d) => V c.succ)) =
      (fun (V : Fin (d + 1) → α) (c : Fin d) => g (V c.succ)) := by
    ext V c; rfl
  calc
    (Measure.infinitePi fun _ : Fin (d + 1) => R).map (fun V (c : Fin d) => g (V c.succ))
        = ((Measure.infinitePi fun _ : Fin (d + 1) => R).map (fun V (c : Fin d) => V c.succ)).map
          (fun W (c : Fin d) => g (W c)) := by
      rw [Measure.map_map h_meas_g_pi h_meas_restrict
        (μ := Measure.infinitePi fun _ : Fin (d + 1) => R), h_comp_eq]
    _ = (Measure.infinitePi fun _ : Fin d => R).map (fun W (c : Fin d) => g (W c)) := by
      rw [Measure.map_infinitePi_infinitePi_of_inj h_succ_inj]
    _ = Measure.infinitePi (fun _ : Fin d => R.map g) := by
      rw [Measure.infinitePi_map_pi (μ := fun _ : Fin d => R) (fun _ => hg)]
    _ = Measure.pi fun _ : Fin d => R.map g := by
      rw [Measure.infinitePi_eq_pi]

theorem FrogModel.Engine.measurableSet_chainState_eq {S U : Type*} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (s : S) (m : ℕ) (t : S) :
    MeasurableSet {v : ℕ → U | FrogModel.Engine.chainState cstep s v m = t} := by
  induction' m with m ih generalizing t
  · -- m = 0
    have h0 : ∀ v, FrogModel.Engine.chainState cstep s v 0 = s := by
      intro v; rfl
    simp [h0]
  · -- m + 1
    have hchain_succ (v : ℕ → U) : FrogModel.Engine.chainState cstep s v (m + 1) =
      (cstep (FrogModel.Engine.chainState cstep s v m) (v m)).2 := rfl
    have h_eq_set : {v : ℕ → U | FrogModel.Engine.chainState cstep s v (m + 1) = t} =
        ⋃ s' : S, {v : ℕ → U | FrogModel.Engine.chainState cstep s v m = s'} ∩
          (fun v : ℕ → U => v m) ⁻¹' {u | (cstep s' u).2 = t} := by
      ext v
      constructor
      · intro hv
        have hv_eq : FrogModel.Engine.chainState cstep s v (m + 1) = t := hv
        rw [hchain_succ v] at hv_eq
        refine Set.mem_iUnion.mpr ⟨FrogModel.Engine.chainState cstep s v m, ?_⟩
        refine ⟨rfl, ?_⟩
        -- need: v ∈ (fun v => v m) ⁻¹' {u | (cstep (chainState ... m) u).2 = t}
        -- i.e., (cstep (chainState ... m) (v m)).2 = t
        simpa [hchain_succ v] using hv_eq
      · intro hv
        rcases Set.mem_iUnion.mp hv with ⟨s', ⟨hv1, hv2⟩⟩
        have hv1_eq : FrogModel.Engine.chainState cstep s v m = s' := hv1
        have hv2_eq : (cstep s' (v m)).2 = t := hv2
        show FrogModel.Engine.chainState cstep s v (m + 1) = t
        rw [hchain_succ v, hv1_eq]
        exact hv2_eq
    rw [h_eq_set]
    refine MeasurableSet.iUnion fun s' => ?_
    have h_first : MeasurableSet {v : ℕ → U | FrogModel.Engine.chainState cstep s v m = s'} :=
      ih s'
    have h_second : MeasurableSet ((fun v : ℕ → U => v m) ⁻¹' {u | (cstep s' u).2 = t}) := by
      have h_meas_inner : MeasurableSet {u | (cstep s' u).2 = t} := by
        have h_eq_inner : {u | (cstep s' u).2 = t} =
            ⋃ r : {r : ℕ × S // r.2 = t}, {u | cstep s' u = r.val} := by
          ext u; simp
        rw [h_eq_inner]
        refine MeasurableSet.iUnion fun r => ?_
        exact hc s' r.val
      have h_meas_fun : Measurable (fun v : ℕ → U => v m) :=
        measurable_pi_apply m
      exact h_meas_inner.preimage h_meas_fun
    exact h_first.inter h_second

theorem FrogModel.Engine.measurable_chainCurve {S U : Type*} [MeasurableSpace U] [Countable S]
    (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (s : S) :
    Measurable (FrogModel.Engine.chainCurve cstep s) := by
  rw [measurable_pi_iff]
  intro i
  have h_chainDeliv_measurable : Measurable fun (v : ℕ → U) => (chainDeliv cstep s v (i - 1) : ℕ∞) := by
    refine ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℕ∞)).comp ?_)
    refine measurable_to_countable' fun n => ?_
    unfold chainDeliv
    -- Goal: MeasurableSet {v | (∑ j ∈ range (i-1), (cstep (chainState cstep s v j) (v j)).1) = n}
    -- First, show each term is measurable
    have h_term_measurable (j : ℕ) : Measurable fun (v : ℕ → U) => (cstep (chainState cstep s v j) (v j)).1 := by
      refine measurable_to_countable' fun k => ?_
      -- Goal: MeasurableSet ((fun v => (cstep (chainState cstep s v j) (v j)).1) ⁻¹' {k})
      have h_eq : ((fun (v : ℕ → U) => (cstep (chainState cstep s v j) (v j)).1) ⁻¹' {k}) =
          ⋃ s' : S, {v | chainState cstep s v j = s'} ∩ {v | (cstep s' (v j)).1 = k} := by
        ext v; simp
      rw [h_eq]
      refine MeasurableSet.iUnion fun s' => ?_
      refine MeasurableSet.inter ?_ ?_
      · -- {v | chainState cstep s v j = s'} is measurable
        exact measurableSet_chainState_eq cstep hc s j s'
      · -- {v | (cstep s' (v j)).1 = k} is measurable
        -- This is (fun v => v j) ⁻¹' {u | (cstep s' u).1 = k}
        -- = ⋃ s'', (fun v => v j) ⁻¹' {u | cstep s' u = (k, s'')}
        -- = ⋃ s'', {v | cstep s' (v j) = (k, s'')}
        -- Each {v | cstep s' (v j) = (k, s'')} is measurable because v ↦ v j is measurable
        -- and {u | cstep s' u = (k, s'')} is measurable by hc
        have h_set : {v : ℕ → U | (cstep s' (v j)).1 = k} =
            ⋃ s'' : S, {v | cstep s' (v j) = (k, s'')} := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          constructor
          · intro h
            refine ⟨(cstep s' (v j)).2, ?_⟩
            exact Prod.ext h rfl
          · intro ⟨s'', h⟩
            simpa [h] using rfl
        rw [h_set]
        refine MeasurableSet.iUnion fun s'' => ?_
        have h_proj : Measurable (fun (v : ℕ → U) => v j) := measurable_pi_apply j
        have h_set_measurable : MeasurableSet {u : U | cstep s' u = (k, s'')} := hc s' (k, s'')
        exact h_proj h_set_measurable
    -- Now the sum is measurable
    have h_sum_measurable : Measurable fun (v : ℕ → U) =>
        ∑ j ∈ Finset.range (i - 1), (cstep (chainState cstep s v j) (v j)).1 := by
      refine Finset.measurable_sum _ fun j hj => ?_
      exact h_term_measurable j
    have h_singleton : MeasurableSet ({n} : Set ℕ) := MeasurableSet.of_discrete
    exact h_sum_measurable h_singleton
  exact h_chainDeliv_measurable

theorem FrogModel.Engine.measurableSet_childAt_eq {S U : Type*} {d : ℕ} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (σ : Fin d → S) (n : ℕ) (τ : Fin d → S) :
    MeasurableSet {w : ℕ → Fin (d + 1) × U | FrogModel.Engine.childAt cstep σ w n = τ} := by
  induction' n with n ih generalizing τ
  · -- n = 0
    simp [FrogModel.Engine.childAt]
  · -- n → n+1
    -- For each s and t, {u | (cstep s u).2 = t} is measurable
    have h_meas_cstep_snd : ∀ (s : S) (t : S), MeasurableSet {u : U | (cstep s u).2 = t} := by
      intro s t
      have h_eq : {u : U | (cstep s u).2 = t} = ⋃ (r : ℕ × S),
        ({u : U | cstep s u = r} ∩ {u : U | r.2 = t}) := by
        ext u; simp
      rw [h_eq]
      refine MeasurableSet.iUnion ?_
      intro r
      refine MeasurableSet.inter (hc s r) ?_
      by_cases hr : r.2 = t
      · simp [hr]
      · simp [hr]

    have h_target_eq : {ω | FrogModel.Engine.childAt cstep σ ω (n+1) = τ} =
      ⋃ (τ' : Fin d → S), ⋃ (a : Fin (d+1)),
        {ω | FrogModel.Engine.childAt cstep σ ω n = τ'} ∩
        {ω | (ω n).1 = a} ∩
        (if h : a = 0 then {ω | τ' = τ}
         else {ω | Function.update τ' (a.pred h) (cstep (τ' (a.pred h)) ((ω n).2)).2 = τ}) := by
      ext ω
      simp [FrogModel.Engine.childAt]
      by_cases h : (ω n).1 = 0
      · simp [h]
      · simp [h]
    rw [h_target_eq]
    refine MeasurableSet.iUnion ?_
    intro τ'
    refine MeasurableSet.iUnion ?_
    intro a
    -- Goal: MeasurableSet (A ∩ B ∩ C) where A = {ω | childAt ... n = τ'}, B = {ω | (ω n).1 = a}, C = third set
    -- A ∩ B ∩ C is (A ∩ B) ∩ C
    refine MeasurableSet.inter (MeasurableSet.inter (ih τ') ?_) ?_
    · -- {ω | (ω n).1 = a}
      have h_meas_fst_apply : Measurable fun (ω : ℕ → Fin (d+1) × U) => (ω n).1 :=
        measurable_fst.comp (measurable_pi_apply n)
      exact h_meas_fst_apply (MeasurableSet.singleton a)
    · -- the third set: MeasurableSet (if h : a = 0 then {ω | τ' = τ} else {ω | ...})
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha]
        -- After simp, the goal is: Measurable (fun ω => Function.update τ' (a.pred ha) (cstep (τ' (a.pred ha)) ((ω n).2)).2 = τ)
        let i := a.pred ha
        have h_update_eq : (fun (ω : ℕ → Fin (d+1) × U) => Function.update τ' i (cstep (τ' i) ((ω n).2)).2 = τ) =
          (fun (ω : ℕ → Fin (d+1) × U) => (cstep (τ' i) ((ω n).2)).2 = τ i ∧ ∀ j, j ≠ i → τ' j = τ j) := by
          ext ω
          simp
          constructor
          · intro h
            constructor
            · have := congrFun h i
              simpa [i, Function.update] using this
            · intro j hj
              have := congrFun h j
              simpa [i, Function.update, hj] using this
          · rintro ⟨h1, h2⟩
            ext j
            by_cases hji : j = i
            · subst hji; simp [h1]
            · rw [Function.update_of_ne hji]
              exact h2 j hji
        rw [h_update_eq]
        -- Goal: Measurable (fun ω => (cstep (τ' i) ((ω n).2)).2 = τ i ∧ ∀ j, j ≠ i → τ' j = τ j)
        -- This is the intersection of two measurable predicates
        refine Measurable.and ?_ ?_
        · -- (cstep (τ' i) ((ω n).2)).2 = τ i
          have h_meas_snd_apply : Measurable fun (ω : ℕ → Fin (d+1) × U) => (ω n).2 :=
            measurable_snd.comp (measurable_pi_apply n)
          have h_set : MeasurableSet {u : U | (cstep (τ' i) u).2 = τ i} := h_meas_cstep_snd (τ' i) (τ i)
          -- Goal: Measurable (fun ω => (cstep (τ' i) ((ω n).2)).2 = τ i)
          -- This is the preimage under ω ↦ (ω n).2 of {u | (cstep (τ' i) u).2 = τ i}
          have h_preimage : (fun (ω : ℕ → Fin (d+1) × U) => (cstep (τ' i) ((ω n).2)).2 = τ i) =
            (fun (ω : ℕ → Fin (d+1) × U) => (ω n).2) ⁻¹' {u : U | (cstep (τ' i) u).2 = τ i} := by
            ext ω; rfl
          rw [h_preimage]
          -- h_meas_snd_apply h_set : MeasurableSet (preimage ...)
          -- We need Measurable (preimage ...) as a predicate
          -- Use measurableSet_setOfPred to convert
          have h_meas : MeasurableSet ((fun (ω : ℕ → Fin (d+1) × U) => (ω n).2) ⁻¹' {u : U | (cstep (τ' i) u).2 = τ i}) :=
            h_meas_snd_apply h_set
          -- h_meas : MeasurableSet (set), goal : Measurable (fun ω => ...)
          -- Use measurableSet_setOfPred to convert
          exact (measurableSet_setOfPred.mp h_meas)
        · -- ∀ j, j ≠ i → τ' j = τ j
          -- This predicate doesn't depend on ω, so it's constant
          exact measurable_const

/-- The set of inputs with a given delivery at step `t` is measurable. -/
theorem FrogModel.Engine.measurableSet_delivAt_eq {S U : Type*} {d : ℕ} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (σ : Fin d → S) (t k : ℕ) :
    MeasurableSet {ω : ℕ → Fin (d + 1) × U | FrogModel.Engine.delivAt cstep σ ω t = k} := by
  -- The direction function (ω t).1 is measurable
  have h_dir_meas : Measurable fun (ω : ℕ → Fin (d + 1) × U) => (ω t).1 :=
    measurable_fst.comp (measurable_pi_apply t)
  -- The second component (ω t).2 is measurable
  have h_unif_meas : Measurable fun (ω : ℕ → Fin (d + 1) × U) => (ω t).2 :=
    measurable_snd.comp (measurable_pi_apply t)
  -- The function ω ↦ childAt cstep σ ω t is measurable (given by the lemma in Deps)
  have h_child_meas : ∀ (τ : Fin d → S), MeasurableSet {ω : ℕ → Fin (d + 1) × U | FrogModel.Engine.childAt cstep σ ω t = τ} :=
    fun τ => FrogModel.Engine.measurableSet_childAt_eq cstep hc σ t τ
  -- Decompose by (ω t).1
  let S_a (a : Fin (d + 1)) : Set (ℕ → Fin (d + 1) × U) :=
    {ω | (ω t).1 = a ∧ FrogModel.Engine.delivAt cstep σ ω t = k}
  have h_cover : {ω : ℕ → Fin (d + 1) × U | FrogModel.Engine.delivAt cstep σ ω t = k} = ⋃ a : Fin (d + 1), S_a a := by
    ext ω; simp [S_a]
  rw [h_cover]
  refine MeasurableSet.iUnion ?_
  intro a
  by_cases ha0 : a = 0
  · -- a = 0 case
    subst ha0
    by_cases hk0 : k = 0
    · subst hk0
      have hS0 : S_a 0 = {ω : ℕ → Fin (d + 1) × U | (ω t).1 = (0 : Fin (d + 1))} := by
        ext ω; constructor
        · rintro ⟨h, _⟩; exact h
        · intro h
          have h_eq : (ω t).1 = (0 : Fin (d + 1)) := h
          refine ⟨h, ?_⟩
          simp [FrogModel.Engine.delivAt, h_eq]
      rw [hS0]
      exact h_dir_meas (measurableSet_singleton (0 : Fin (d + 1)))
    · -- k ≠ 0, so S_0 = ∅
      have hS0 : S_a 0 = (∅ : Set (ℕ → Fin (d + 1) × U)) := by
        ext ω; constructor
        · rintro ⟨h, hdeliv⟩
          have h_eq : (ω t).1 = (0 : Fin (d + 1)) := h
          simp [FrogModel.Engine.delivAt, h_eq] at hdeliv
          exact hk0 hdeliv.symm
        · intro h; exact False.elim h
      rw [hS0]
      exact MeasurableSet.empty
  · -- a ≠ 0 case
    have hSa_eq : S_a a = ⋃ (τ' : Fin d → S),
        ({ω : ℕ → Fin (d + 1) × U | (ω t).1 = a} ∩
         {ω : ℕ → Fin (d + 1) × U | FrogModel.Engine.childAt cstep σ ω t = τ'} ∩
         {ω : ℕ → Fin (d + 1) × U | (cstep (τ' ((a : Fin (d + 1)).pred ha0)) (ω t).2).1 = k}) := by
      ext ω; constructor
      · rintro ⟨ha, hdeliv⟩
        have hzero : ¬ ((ω t).1 = (0 : Fin (d + 1))) := by
          intro h; apply ha0; rw [← ha, h]
        have h_cstep_eq : (cstep (FrogModel.Engine.childAt cstep σ ω t (((ω t).1).pred hzero)) (ω t).2).1 = k := by
          simp [FrogModel.Engine.delivAt, hzero] at hdeliv
          exact hdeliv
        have h_pred_eq : ((ω t).1).pred hzero = ((a : Fin (d + 1)).pred ha0) := by
          subst ha; rfl
        let τ'val := FrogModel.Engine.childAt cstep σ ω t
        refine Set.mem_iUnion.mpr ⟨τ'val, ?_⟩
        refine ⟨⟨ha, rfl⟩, ?_⟩
        simpa [τ'val, h_pred_eq] using h_cstep_eq
      · intro h
        rcases Set.mem_iUnion.mp h with ⟨τ', hmem⟩
        rcases hmem with ⟨⟨ha, hchild⟩, hcstep⟩
        have ha_eq : (ω t).1 = a := ha
        have hchild_eq : FrogModel.Engine.childAt cstep σ ω t = τ' := hchild
        have hcstep_eq : (cstep (τ' ((a : Fin (d + 1)).pred ha0)) (ω t).2).1 = k := hcstep
        have hzero : ¬ ((ω t).1 = (0 : Fin (d + 1))) := by
          intro hzero'; apply ha0; rw [← ha_eq, hzero']
        have h_pred_eq : ((ω t).1).pred hzero = ((a : Fin (d + 1)).pred ha0) := by
          subst ha_eq
          rfl
        refine ⟨ha_eq, ?_⟩
        simp [FrogModel.Engine.delivAt, hzero, hchild_eq, hcstep_eq, h_pred_eq]
    rw [hSa_eq]
    refine MeasurableSet.iUnion ?_
    intro τ'
    have h1 : MeasurableSet {ω : ℕ → Fin (d + 1) × U | (ω t).1 = a} :=
      h_dir_meas (measurableSet_singleton a)
    have h2 : MeasurableSet {ω : ℕ → Fin (d + 1) × U | FrogModel.Engine.childAt cstep σ ω t = τ'} :=
      h_child_meas τ'
    have h3 : MeasurableSet {ω : ℕ → Fin (d + 1) × U |
        (cstep (τ' ((a : Fin (d + 1)).pred ha0)) (ω t).2).1 = k} := by
      have h_set_u : MeasurableSet {u : U | (cstep (τ' ((a : Fin (d + 1)).pred ha0)) u).1 = k} := by
        have h_eq : {u : U | (cstep (τ' ((a : Fin (d + 1)).pred ha0)) u).1 = k} =
            ⋃ s' : S, {u : U | cstep (τ' ((a : Fin (d + 1)).pred ha0)) u = (k, s')} := by
          ext u; constructor
          · intro h
            -- h : u ∈ {u | (cstep ... u).1 = k}, i.e., (cstep ... u).1 = k
            rw [Set.mem_iUnion]
            refine ⟨(cstep (τ' ((a : Fin (d + 1)).pred ha0)) u).2, ?_⟩
            -- Goal: u ∈ {u | cstep ... u = (k, (cstep ... u).2)}
            -- i.e., cstep ... u = (k, (cstep ... u).2)
            dsimp
            have h' : (cstep (τ' ((a : Fin (d + 1)).pred ha0)) u).1 = k := h
            ext <;> simp [h']
          · intro h
            rw [Set.mem_iUnion] at h
            rcases h with ⟨s', hs'⟩
            -- hs' : u ∈ {u | cstep ... u = (k, s')}, i.e., cstep ... u = (k, s')
            -- Goal: (cstep ... u).1 = k
            -- Extract the equality from the set membership
            have hpair : cstep (τ' ((a : Fin (d + 1)).pred ha0)) u = (k, s') := hs'
            simpa [hpair]
        rw [h_eq]
        refine MeasurableSet.iUnion ?_
        intro s'
        exact hc (τ' ((a : Fin (d + 1)).pred ha0)) (k, s')
      exact measurableSet_preimage h_unif_meas h_set_u
    -- Goal: MeasurableSet (A ∩ B ∩ C) = MeasurableSet ((A ∩ B) ∩ C)
    exact MeasurableSet.inter (MeasurableSet.inter h1 h2) h3

theorem FrogModel.Engine.measurableSet_cumDeliv_eq {S U : Type*} {d : ℕ} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (σ : Fin d → S) (n m : ℕ) :
    MeasurableSet {w : ℕ → Fin (d + 1) × U | FrogModel.Engine.cumDeliv cstep σ w n = m} := by
  have h_cumDeliv_meas : Measurable (fun (ω : ℕ → Fin (d + 1) × U) => FrogModel.Engine.cumDeliv cstep σ ω n) := by
    refine Finset.measurable_sum (Finset.range n) ?_
    intro t ht
    have h_deliv_meas : Measurable (fun (ω : ℕ → Fin (d + 1) × U) => FrogModel.Engine.delivAt cstep σ ω t) := by
      refine measurable_to_countable' ?_
      intro k
      exact measurableSet_delivAt_eq cstep hc σ t k
    simpa using h_deliv_meas
  have h_singleton : MeasurableSet ({m} : Set ℕ) := measurableSet_singleton _
  exact h_cumDeliv_meas h_singleton

theorem FrogModel.Engine.measurableSet_exitCount_eq {U : Type*} {d : ℕ} [MeasurableSpace U]
    (n m : ℕ) :
    MeasurableSet {w : ℕ → Fin (d + 1) × U | FrogModel.Engine.exitCount w n = m} := by
  have h_exitCount_eq (w : ℕ → Fin (d + 1) × U) : FrogModel.Engine.exitCount w n =
      ∑ t ∈ Finset.range n, if (w t).1 = (0 : Fin (d + 1)) then (1 : ℕ) else 0 := by
    rw [FrogModel.Engine.exitCount, Finset.card_filter]
  have h_meas : Measurable fun w : ℕ → Fin (d + 1) × U =>
      ∑ t ∈ Finset.range n, if (w t).1 = (0 : Fin (d + 1)) then (1 : ℕ) else 0 := by
    refine Finset.measurable_sum (Finset.range n) ?_
    intro t ht
    have h_term : Measurable fun w : ℕ → Fin (d + 1) × U =>
        if (w t).1 = (0 : Fin (d + 1)) then (1 : ℕ) else 0 := by
      refine Measurable.ite ?_ measurable_const measurable_const
      have h_fst : Measurable fun w : ℕ → Fin (d + 1) × U => (w t).1 :=
        measurable_fst.comp (measurable_pi_apply t)
      exact h_fst (MeasurableSet.singleton (0 : Fin (d + 1)))
    exact h_term
  have h_set : {w : ℕ → Fin (d + 1) × U | FrogModel.Engine.exitCount w n = m} =
      {w : ℕ → Fin (d + 1) × U | (∑ t ∈ Finset.range n, if (w t).1 = (0 : Fin (d + 1)) then (1 : ℕ) else 0) = m} := by
    ext w; simp [h_exitCount_eq w]
  rw [h_set]
  exact h_meas (MeasurableSet.singleton m)

theorem FrogModel.Engine.measurable_outPsi {S U : Type*} {d J : ℕ} [MeasurableSpace U]
    [Countable S] (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r})
    (x : FrogModel.Engine.RState S d J) :
    Measurable (fun w : ℕ → Fin (d + 1) × U => FrogModel.Engine.outPsi cstep x w) := by
  classical
  refine measurable_pi_iff.2 fun k => ?_
  refine measurable_to_countable' (f := fun w => FrogModel.Engine.outPsi cstep x w k) (fun v => ?_)
  dsimp [FrogModel.Engine.outPsi]
  by_cases h_lt : (k : ℕ) < x.i
  · simp [h_lt]
    by_cases h_eq : (x.out k : ℕ∞) = v
    · simp [h_eq]
    · simp [h_eq]
  · simp [h_lt]
    set P := fun (n : ℕ) (w : ℕ → Fin (d + 1) × U) =>
      FrogModel.Engine.need cstep x w (k : ℕ) n ≤ n with hP
    have hP_meas : ∀ n, MeasurableSet {w : ℕ → Fin (d + 1) × U | P n w} := by
      intro n
      dsimp [P]
      have h_fin : {m : ℕ | x.p + ((k : ℕ) - x.i) + m ≤ n}.Finite := by
        refine Set.Finite.subset (Set.finite_le_nat n) ?_
        intro m hm
        -- hm : m ∈ {m | x.p + (k - x.i) + m ≤ n}
        -- i.e., x.p + (k - x.i) + m ≤ n
        -- Need to show m ≤ n
        have h_bound : x.p + ((k : ℕ) - x.i) + m ≤ n := hm
        have h_le : m ≤ x.p + ((k : ℕ) - x.i) + m := Nat.le_add_left m _
        exact Nat.le_trans h_le h_bound
      have h_eq_set : {w : ℕ → Fin (d + 1) × U | FrogModel.Engine.need cstep x w (k : ℕ) n ≤ n} =
          ⋃ m ∈ {m : ℕ | x.p + ((k : ℕ) - x.i) + m ≤ n},
          {w : ℕ → Fin (d + 1) × U | FrogModel.Engine.cumDeliv cstep x.σ w n = m} := by
        ext ω; constructor
        · intro h
          -- h : ω ∈ {w | need cstep x w (k : ℕ) n ≤ n}
          -- i.e., need cstep x ω (k : ℕ) n ≤ n
          simp only [Set.mem_setOf_eq] at h
          -- h : need cstep x ω (k : ℕ) n ≤ n
          -- need = x.p + (k - x.i) + cumDeliv
          -- So x.p + (k - x.i) + cumDeliv ≤ n
          -- This means cumDeliv ∈ {m | x.p + (k - x.i) + m ≤ n}
          have h_need_eq : FrogModel.Engine.need cstep x ω (k : ℕ) n =
              x.p + ((k : ℕ) - x.i) + FrogModel.Engine.cumDeliv cstep x.σ ω n := rfl
          rw [h_need_eq] at h
          -- h : x.p + (k - x.i) + cumDeliv cstep x.σ ω n ≤ n
          refine Set.mem_iUnion₂.mpr ⟨FrogModel.Engine.cumDeliv cstep x.σ ω n, h, ?_⟩
          rfl
        · intro h
          rcases Set.mem_iUnion₂.mp h with ⟨m, hm, hm'⟩
          have hm_eq : FrogModel.Engine.cumDeliv cstep x.σ ω n = m := hm'
          -- Goal: ω ∈ {w | need cstep x w (k : ℕ) n ≤ n}
          -- i.e., need cstep x ω (k : ℕ) n ≤ n
          simp only [Set.mem_setOf_eq]
          -- need = x.p + (k - x.i) + cumDeliv = x.p + (k - x.i) + m
          -- and hm : x.p + (k - x.i) + m ≤ n
          have h_need_eq : FrogModel.Engine.need cstep x ω (k : ℕ) n =
              x.p + ((k : ℕ) - x.i) + FrogModel.Engine.cumDeliv cstep x.σ ω n := rfl
          rw [h_need_eq, hm_eq]
          exact hm
      rw [h_eq_set]
      refine MeasurableSet.biUnion (h_fin.countable) (fun m hm => ?_)
      exact FrogModel.Engine.measurableSet_cumDeliv_eq cstep hc x.σ n m
    by_cases h_top : v = ⊤
    · rw [h_top]
      -- Goal: MeasurableSet ((fun w => ...) ⁻¹' {⊤})
      -- This is equivalent to MeasurableSet {ω | ... = ⊤}
      -- We show this set equals {ω | ¬ ∃ n, P n ω}
      have h_set : {ω : ℕ → Fin (d + 1) × U |
          (if h : ∃ n, P n ω then (x.e + FrogModel.Engine.exitCount ω (Nat.find h) : ℕ∞) else ⊤) = ⊤} =
          {ω : ℕ → Fin (d + 1) × U | ¬ ∃ n, P n ω} := by
        ext ω; simp
      -- Convert the goal to the form in h_set
      -- The goal is: MeasurableSet ((fun w => ...) ⁻¹' {⊤})
      -- which equals MeasurableSet {ω | ... = ⊤}
      -- h_set gives the equality of these sets
      -- So we can rewrite using h_set
      have h_union : MeasurableSet {ω : ℕ → Fin (d + 1) × U | ∃ n, P n ω} := by
        rw [Set.setOf_exists]
        refine MeasurableSet.iUnion (fun n => ?_)
        exact hP_meas n
      have h_target : MeasurableSet {ω : ℕ → Fin (d + 1) × U |
          (if h : ∃ n, P n ω then (x.e + FrogModel.Engine.exitCount ω (Nat.find h) : ℕ∞) else ⊤) = ⊤} := by
        rw [h_set]
        exact h_union.compl
      -- Now convert back to the preimage form
      have : ((fun w : ℕ → Fin (d + 1) × U =>
          if h : ∃ n, P n w then (x.e + FrogModel.Engine.exitCount w (Nat.find h) : ℕ∞) else ⊤) ⁻¹' {⊤}) =
          {ω : ℕ → Fin (d + 1) × U |
          (if h : ∃ n, P n ω then (x.e + FrogModel.Engine.exitCount ω (Nat.find h) : ℕ∞) else ⊤) = ⊤} := by
        ext ω; simp
      rw [this]
      exact h_target
    · have h_v : ∃ q : ℕ, v = (q : ℕ∞) := by
        rcases ENat.ne_top_iff_exists.mp h_top with ⟨q, hq⟩
        exact ⟨q, hq.symm⟩
      rcases h_v with ⟨q, rfl⟩
      -- Goal: MeasurableSet {ω | (if ...) = (q : ℕ∞)}
      -- This equals ⋃ n, ({ω | P n ω} ∩ ⋂ j < n, {ω | ¬ P j ω}) ∩ {ω | x.e + exitCount ω n = q}
      -- We prove this equality and then show the RHS is measurable
      have h_eq : {ω : ℕ → Fin (d + 1) × U |
          (if h : ∃ n, P n ω then (x.e + FrogModel.Engine.exitCount ω (Nat.find h) : ℕ∞) else ⊤) = (q : ℕ∞)} =
          ⋃ n : ℕ,
          ({ω | P n ω} ∩ ⋂ j ∈ Finset.range n, {ω' | ¬ P j ω'}) ∩
          {ω : ℕ → Fin (d + 1) × U | x.e + FrogModel.Engine.exitCount ω n = q} := by
        ext ω; constructor
        · intro h
          -- h : ω ∈ {ω | ... = ↑q}
          -- Simplify to get the equality
          simp only [Set.mem_setOf_eq] at h
          -- h : (if h : ∃ n, P n ω then ... else ⊤) = (q : ℕ∞)
          by_cases h_exists : ∃ n, P n ω
          · set n₀ := Nat.find h_exists with hn₀
            have h_val : (if h : ∃ n, P n ω then (x.e + FrogModel.Engine.exitCount ω (Nat.find h) : ℕ∞) else ⊤) =
                (x.e + FrogModel.Engine.exitCount ω n₀ : ℕ∞) := by
              simp [h_exists, hn₀]
            rw [h_val] at h
            -- h : (x.e + exitCount ω n₀ : ℕ∞) = (q : ℕ∞)
            have h_exit_eq : x.e + FrogModel.Engine.exitCount ω n₀ = q := by
              have := congrArg ENat.toNat h
              simpa [ENat.toNat_add, ENat.toNat_natCast] using this
            have h_need_n₀ : P n₀ ω := by
              dsimp [P]; exact Nat.find_spec h_exists
            have h_min : ∀ j < n₀, ¬ P j ω := by
              intro j hj
              dsimp [P]
              by_contra hPj
              have h_le : n₀ ≤ j := Nat.find_min' h_exists hPj
              omega
            have h_inter : ω ∈ ⋂ j ∈ Finset.range n₀, {ω' | ¬ P j ω'} := by
              refine Set.mem_iInter₂.mpr (fun j hj => ?_)
              rw [Finset.mem_range] at hj
              exact h_min j hj
            refine Set.mem_iUnion.mpr ⟨n₀, ⟨h_need_n₀, h_inter⟩, h_exit_eq⟩
          · simp [h_exists] at h
        · intro h
          rcases Set.mem_iUnion.mp h with ⟨n, ⟨hPn, h_rest⟩, h_exit⟩
          have h_exists : ∃ n, P n ω := ⟨n, hPn⟩
          simp [h_exists]
          have h_find_eq_n : Nat.find h_exists = n := by
            apply (Nat.find_eq_iff h_exists).mpr
            refine ⟨hPn, ?_⟩
            intro j hj
            have h_mem := Set.mem_iInter₂.mp h_rest j (by
              rw [Finset.mem_range]
              exact hj)
            exact h_mem
          rw [h_find_eq_n]
          -- Goal: (x.e + exitCount ω n : ℕ∞) = (q : ℕ∞)
          -- h_exit : x.e + exitCount ω n = q (in ℕ)
          -- Use Nat.cast to lift to ℕ∞
          exact congrArg (fun t : ℕ => (t : ℕ∞)) h_exit
      -- Now we have a countable union of intersections of measurable sets
      -- The goal is: MeasurableSet ((fun w => ...) ⁻¹' {↑q})
      -- which equals MeasurableSet {ω | ... = ↑q}
      -- h_eq gives the equality of these sets
      -- So we can rewrite using h_eq
      have h_goal : MeasurableSet {ω : ℕ → Fin (d + 1) × U |
          (if h : ∃ n, P n ω then (x.e + FrogModel.Engine.exitCount ω (Nat.find h) : ℕ∞) else ⊤) = (q : ℕ∞)} := by
        rw [h_eq]
        refine MeasurableSet.iUnion (fun n => ?_)
        have h_fin_inter : MeasurableSet (⋂ j ∈ Finset.range n, {ω' : ℕ → Fin (d + 1) × U | ¬ P j ω'}) := by
          refine MeasurableSet.biInter (Finset.countable_toSet _) (fun j hj => ?_)
          exact (hP_meas j).compl
        have h_exit : MeasurableSet {ω : ℕ → Fin (d + 1) × U |
            x.e + FrogModel.Engine.exitCount ω n = q} := by
          by_cases hq : x.e ≤ q
          · have : {z : ℕ → Fin (d + 1) × U | x.e + FrogModel.Engine.exitCount z n = q} =
                {z : ℕ → Fin (d + 1) × U | FrogModel.Engine.exitCount z n = q - x.e} := by
              ext z; simp only [Set.mem_setOf_eq]; constructor
              · intro h
                -- h : x.e + exitCount z n = q
                -- Goal: exitCount z n = q - x.e
                have h_total : x.e + exitCount z n = x.e + (q - x.e) := by
                  rw [Nat.add_sub_cancel' hq, h]
                exact add_left_cancel (a := x.e) h_total
              · intro h
                -- h : exitCount z n = q - x.e
                -- Goal: x.e + exitCount z n = q
                rw [h, Nat.add_sub_cancel' hq]
            rw [this]
            exact FrogModel.Engine.measurableSet_exitCount_eq n (q - x.e)
          · have : {z : ℕ → Fin (d + 1) × U | x.e + FrogModel.Engine.exitCount z n = q} = ∅ := by
              ext z; simp; intro h; omega
            rw [this]
            exact MeasurableSet.empty
        have h_temp : MeasurableSet ({ω | P n ω} ∩ (⋂ j ∈ Finset.range n, {ω' | ¬ P j ω'})) :=
          MeasurableSet.inter (hP_meas n) h_fin_inter
        exact MeasurableSet.inter h_temp h_exit
      -- Now convert back to the preimage form
      -- h_goal : MeasurableSet {ω | ... = ↑q}
      -- Goal: MeasurableSet ((fun w => ...) ⁻¹' {↑q})
      -- These are definitionally equal: f ⁻¹' {v} = {x | f x = v}
      -- But we need to help Lean see this
      have : ((fun w : ℕ → Fin (d + 1) × U =>
          if h : ∃ n, need cstep x w (k : ℕ) n ≤ n then
          (x.e + FrogModel.Engine.exitCount w (Nat.find h) : ℕ∞) else ⊤) ⁻¹' {(q : ℕ∞)}) =
          {ω : ℕ → Fin (d + 1) × U |
          (if h : ∃ n, need cstep x ω (k : ℕ) n ≤ n then
          (x.e + FrogModel.Engine.exitCount ω (Nat.find h) : ℕ∞) else ⊤) = (q : ℕ∞)} := by
        ext ω; simp
      rw [this]
      -- Now the goal matches h_goal (modulo P)
      simpa [P] using h_goal

theorem FrogModel.Engine.ae_dirCountN_unbounded (d : ℕ) :
    ∀ᵐ D ∂(Measure.infinitePi fun _ : ℕ =>
        (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d + 1)))),
      ∀ m, ∃ n, m ≤ FrogModel.Engine.dirCountN D 0 n := by
  -- Let μ be the infinite product measure
  let μ := Measure.infinitePi fun _ : ℕ => (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d+1)))
  -- Define A_t = {D | D t = 0}
  let A : ℕ → Set (ℕ → Fin (d+1)) := fun t => {D | D t = 0}
  have hAmeas : ∀ t, MeasurableSet (A t) := by
    intro t
    unfold A
    have : {D : ℕ → Fin (d+1) | D t = 0} = (fun D => D t) ⁻¹' {0} := by
      ext D; simp
    rw [this]
    exact (measurable_pi_apply t) (measurableSet_singleton _)
  have hAindep : ProbabilityTheory.iIndepSet A μ := by
    unfold μ A
    rw [ProbabilityTheory.iIndepSet_iff_meas_biInter (fun t => by
      have : ({D : ℕ → Fin (d+1) | D t = 0} : Set (ℕ → Fin (d+1))) = (fun D => D t) ⁻¹' {0} := by
        ext D; simp
      rw [this]
      exact (measurable_pi_apply t) (measurableSet_singleton _))]
    intro s
    have h_inter : (⋂ t ∈ s, {D : ℕ → Fin (d+1) | D t = 0}) = (s : Set ℕ).pi (fun t => {0} : (t : ℕ) → Set (Fin (d+1))) := by
      ext D
      simp [Set.mem_pi]
    rw [h_inter]
    rw [MeasureTheory.Measure.infinitePi_pi (fun _ : ℕ => (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d+1)))) ?_]
    · refine Finset.prod_congr rfl (fun t ht => ?_)
      have hpre : {D : ℕ → Fin (d+1) | D t = 0} = (fun D => D t) ⁻¹' {0} := by
        ext D; simp
      rw [hpre]
      have hmeas : Measurable (fun D : ℕ → Fin (d+1) => D t) := measurable_pi_apply t
      rw [← Measure.map_apply hmeas (measurableSet_singleton _)]
      rw [MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d+1)))) t]
    · intro t ht
      exact measurableSet_singleton _
  have hAmeas_nonzero : ∀ t, μ (A t) ≠ 0 := by
    intro t
    unfold μ A
    have hpre : {D : ℕ → Fin (d+1) | D t = 0} = (fun D => D t) ⁻¹' {0} := by
      ext D; simp
    rw [hpre]
    have hmeas : Measurable (fun D : ℕ → Fin (d+1) => D t) := measurable_pi_apply t
    rw [← Measure.map_apply hmeas (measurableSet_singleton _)]
    rw [MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d+1)))) t]
    rw [ProbabilityTheory.uniformOn_univ]
    have hcount : Measure.count ({0} : Set (Fin (d+1))) = 1 := by
      simp
    rw [hcount]
    rw [Fintype.card_fin]
    simp
  -- The sum of measures is infinite
  have hsum : ∑' t, μ (A t) = ∞ := by
    -- Each term equals c = μ (A 0) which is nonzero
    have h_eq : ∀ t, μ (A t) = μ (A 0) := by
      intro t
      unfold μ A
      have hpre_t : {D : ℕ → Fin (d+1) | D t = 0} = (fun D => D t) ⁻¹' {0} := by
        ext D; simp
      have hpre_0 : {D : ℕ → Fin (d+1) | D 0 = 0} = (fun D => D 0) ⁻¹' {0} := by
        ext D; simp
      rw [hpre_t, hpre_0]
      have hmeas_t : Measurable (fun D : ℕ → Fin (d+1) => D t) := measurable_pi_apply t
      have hmeas_0 : Measurable (fun D : ℕ → Fin (d+1) => D 0) := measurable_pi_apply 0
      rw [← Measure.map_apply hmeas_t (measurableSet_singleton _),
        ← Measure.map_apply hmeas_0 (measurableSet_singleton _)]
      rw [MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d+1)))) t,
        MeasureTheory.Measure.infinitePi_map_eval (fun _ : ℕ => (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d+1)))) 0]
    have h_ne_zero : μ (A 0) ≠ 0 := hAmeas_nonzero 0
    rw [tsum_congr h_eq]
    -- Now ∑' t : ℕ, μ (A 0) = ∞ since μ (A 0) ≠ 0 and ℕ is infinite
    exact ENNReal.tsum_const_eq_top_of_ne_zero h_ne_zero
  -- By Borel-Cantelli, μ (limsup A atTop) = 1
  have h_limsup : μ (Filter.limsup A Filter.atTop) = 1 :=
    ProbabilityTheory.measure_limsup_eq_one hAmeas hAindep hsum
  -- For D in limsup A atTop, D t = 0 for infinitely many t
  -- So for any m, there exists n such that at least m values of t < n have D t = 0
  -- This means dirCountN D 0 n ≥ m
  have h_limsup_meas : MeasurableSet (Filter.limsup A Filter.atTop) :=
    MeasurableSet.measurableSet_limsup hAmeas
  have h_limsup' : ∀ᵐ D ∂μ, D ∈ Filter.limsup A Filter.atTop := by
    -- Use the lemma: s ∈ ae μ ↔ μ s = 1
    have := (MeasureTheory.mem_ae_iff_prob_eq_one h_limsup_meas).mpr h_limsup
    simpa using this
  -- Now filter the a.e. statement
  filter_upwards [h_limsup'] with D hD
  -- hD : D ∈ Filter.limsup A Filter.atTop
  -- This means D t = 0 for infinitely many t
  -- Use Filter.mem_limsup_iff_frequently_mem
  have h_freq : ∃ᶠ t in Filter.atTop, D ∈ A t := by
    rwa [Filter.mem_limsup_iff_frequently_mem] at hD
  -- Convert to Nat.frequently
  rw [Nat.frequently_atTop_iff_infinite] at h_freq
  -- h_freq : {t | D ∈ A t}.Infinite
  -- But D ∈ A t means D t = 0
  -- So {t | D t = 0} is infinite
  have h_infinite : {t : ℕ | D t = 0}.Infinite := by
    -- h_freq gives {t | D ∈ A t}.Infinite, and D ∈ A t ↔ D t = 0
    -- So we can rewrite
    have : {t : ℕ | D ∈ A t} = {t : ℕ | D t = 0} := by
      ext t; simp [A]
    rwa [this] at h_freq
  -- Now for any m, we need to find n such that m ≤ dirCountN D 0 n
  intro m
  -- Since {t | D t = 0} is infinite, we can find m distinct elements
  -- Use Set.Infinite.exists_subset_card_eq
  obtain ⟨t, ht_sub, ht_card⟩ := Set.Infinite.exists_subset_card_eq h_infinite m
  -- t is a Finset ℕ with t ⊆ {t | D t = 0} and t.card = m
  -- We need to find n such that m ≤ dirCountN D 0 n
  -- dirCountN D 0 n = |{s < n | D s = 0}|
  -- Since t ⊆ {s | D s = 0}, we just need n large enough so that all elements of t are < n
  -- If m = 0, take n = 0
  by_cases hm : m = 0
  · subst hm
    refine ⟨0, ?_⟩
    simp [FrogModel.Engine.dirCountN]
  · -- m > 0, so t is nonempty
    have ht_nonempty : t.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      rw [Finset.card_eq_zero.mpr h_empty] at ht_card
      exact hm ht_card.symm
    let n := t.max' ht_nonempty + 1
    refine ⟨n, ?_⟩
    -- Need to show m ≤ dirCountN D 0 n
    -- dirCountN D 0 n = |{s < n | D s = 0}|
    -- Since t ⊆ {s | D s = 0} and all elements of t are < n (because n = max t + 1),
    -- we have t ⊆ {s < n | D s = 0}
    -- So m = t.card ≤ dirCountN D 0 n
    rw [FrogModel.Engine.dirCountN]
    -- dirCountN D 0 n = ((Finset.range n).filter fun s => D s = 0).card
    -- We need to show m ≤ ((Finset.range n).filter fun s => D s = 0).card
    -- Since t ⊆ {s | D s = 0} and all elements of t are < n,
    -- we have t as a subset of (Finset.range n).filter fun s => D s = 0
    have h_sub : t ⊆ (Finset.range n).filter fun s => D s = 0 := by
      intro s hs
      rw [Finset.mem_filter]
      constructor
      · -- s ∈ range n, i.e., s < n
        rw [Finset.mem_range]
        have : s ≤ t.max' ht_nonempty := Finset.le_max' t s hs
        omega
      · -- D s = 0
        have : s ∈ {t : ℕ | D t = 0} := ht_sub hs
        simpa using this
    -- Now use Finset.card_le_card
    have h_card := Finset.card_le_card h_sub
    -- h_card : t.card ≤ ((Finset.range n).filter ...).card
    -- But t.card = m
    rw [ht_card] at h_card
    exact h_card

theorem FrogModel.Engine.measurable_poolDrive {U : Type*} {d : ℕ} [MeasurableSpace U] :
    Measurable (fun p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) =>
      FrogModel.Engine.poolDrive p.1 p.2) := by
  unfold FrogModel.Engine.poolDrive
  refine @Measurable.of_eval _ ℕ (fun _ => Fin (d+1) × U) _ _ _ ?_
  intro t
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_pi_apply t).comp measurable_fst
  · have h_outer : Measurable (fun (q : (Fin (d + 1) × ℕ) × ((ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U))) =>
      q.2.2 q.1.1 q.1.2) := by
      refine measurable_from_prod_countable_right ?_
      intro ⟨a, m⟩
      have h : Measurable (fun (f : Fin (d+1) → ℕ → U) => f a m) :=
        (measurable_pi_apply (X := fun _ : ℕ => U) m).comp (measurable_pi_apply (X := fun _ : Fin (d+1) => ℕ → U) a)
      exact h.comp measurable_snd
    have h_inner : Measurable (fun (p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U)) =>
      ((p.1 t, dirCountN p.1 (p.1 t) t), p)) := by
      refine Measurable.prodMk ?_ measurable_id
      refine measurable_to_countable' ?_
      intro ⟨a, m⟩
      have h_first : MeasurableSet {p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) | p.1 t = a} :=
        (measurable_pi_apply (X := fun _ : ℕ => Fin (d+1)) t).comp measurable_fst (measurableSet_singleton a)
      have h_second : MeasurableSet {p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) |
        dirCountN p.1 (p.1 t) t = m} := by
        have h_meas : Measurable (fun (p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U)) =>
          dirCountN p.1 (p.1 t) t) := by
          have h_pair : Measurable (fun (x : (ℕ → Fin (d + 1)) × Fin (d + 1)) =>
            dirCountN x.1 x.2 t) := by
            unfold dirCountN
            have h_eq : (fun (x : (ℕ → Fin (d + 1)) × Fin (d + 1)) =>
              ((Finset.range t).filter fun s => x.1 s = x.2).card) =
              (fun (x : (ℕ → Fin (d + 1)) × Fin (d + 1)) =>
              ∑ s ∈ Finset.range t, if x.1 s = x.2 then (1 : ℕ) else 0) := by
              ext ⟨D, a⟩
              rw [Finset.card_filter]
            rw [h_eq]
            refine Finset.measurable_sum _ ?_
            intro s hs
            have h_f : Measurable (fun (x : (ℕ → Fin (d + 1)) × Fin (d + 1)) => (x.1 s, x.2)) :=
              Measurable.prodMk ((measurable_pi_apply s).comp measurable_fst) measurable_snd
            have h_diag : MeasurableSet (Set.diagonal (Fin (d+1))) :=
              MeasurableEq.measurableSet_diagonal (α := Fin (d+1))
            have h_set : MeasurableSet ({x : (ℕ → Fin (d + 1)) × Fin (d + 1) | x.1 s = x.2} :
              Set ((ℕ → Fin (d + 1)) × Fin (d + 1))) := by
              have h_eq_set : ({x : (ℕ → Fin (d + 1)) × Fin (d + 1) | x.1 s = x.2} :
                Set ((ℕ → Fin (d + 1)) × Fin (d + 1))) =
                (fun (x : (ℕ → Fin (d + 1)) × Fin (d + 1)) => (x.1 s, x.2)) ⁻¹'
                Set.diagonal (Fin (d+1)) := by
                ext ⟨D, a⟩
                simp [Set.diagonal]
              rw [h_eq_set]
              exact h_f h_diag
            have h_indicator : Measurable (({x : (ℕ → Fin (d + 1)) × Fin (d + 1) | x.1 s = x.2} :
              Set ((ℕ → Fin (d + 1)) × Fin (d + 1))).indicator (fun _ => (1 : ℕ))) :=
              Measurable.indicator measurable_const h_set
            have h_eq2 : (({x : (ℕ → Fin (d + 1)) × Fin (d + 1) | x.1 s = x.2} :
              Set ((ℕ → Fin (d + 1)) × Fin (d + 1))).indicator (fun _ => (1 : ℕ))) =
              (fun (x : (ℕ → Fin (d + 1)) × Fin (d + 1)) =>
              if x.1 s = x.2 then (1 : ℕ) else 0) := by
              ext ⟨D, a⟩
              simp [Set.indicator]
            rw [h_eq2] at h_indicator
            exact h_indicator
          have h_proj : Measurable (fun (p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U)) =>
            (p.1, p.1 t)) :=
            Measurable.prodMk measurable_fst ((measurable_pi_apply (X := fun _ : ℕ => Fin (d+1)) t).comp measurable_fst)
          exact h_pair.comp h_proj
        exact h_meas (measurableSet_singleton m)
      have h_inter : MeasurableSet ({p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) |
        p.1 t = a} ∩ {p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) |
        dirCountN p.1 (p.1 t) t = m}) :=
        MeasurableSet.inter h_first h_second
      -- The preimage of {(a, m)} under p ↦ (p.1 t, dirCountN p.1 (p.1 t) t) is exactly this intersection
      have h_eq_preimage : (fun (p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U)) =>
        (p.1 t, dirCountN p.1 (p.1 t) t)) ⁻¹' {(a, m)} =
        {p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) |
        p.1 t = a} ∩ {p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) |
        dirCountN p.1 (p.1 t) t = m} := by
        ext p
        simp
      rw [h_eq_preimage]
      exact h_inter
    exact h_outer.comp h_inner
