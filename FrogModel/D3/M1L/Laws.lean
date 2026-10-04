module

public import FrogModel.D3.M1L.Height0Defs
public import FrogModel.ZeroOne.Glue

@[expose] public section

/-!
# Laws on the stream and on the frog paths

The kill coin, the directions of a value, the steps of the frog pools, the measurability of the
run, and the strong Markov property of an i.i.d. sequence at a stopping time in integrated form
(from `ZeroOne.map_glueAt`).
-/

open MeasureTheory ProbabilityTheory FrogModel
open scoped ENNReal

/-- The kill coin takes the value `n` with probability `2^-(n+1)`. -/
theorem FrogModel.D3.coinLaw_singleton (n : ℕ) : FrogModel.D3.coinLaw {n} = (1 / 2) ^ (n + 1) := by
  unfold FrogModel.D3.coinLaw
  set p : unitInterval := ⟨1/2, by norm_num, by norm_num⟩ with hp_def
  have hp : p ≠ 0 := by
    rw [hp_def]
    intro h
    have hval : ((⟨1/2, by norm_num, by norm_num⟩ : unitInterval) : ℝ) = ((0 : unitInterval) : ℝ) := by
      simpa using congrArg Subtype.val h
    norm_num at hval
  rw [ProbabilityTheory.geometricMeasure_singleton hp n]
  have hsub : ((1 : ℝ) - (p : ℝ)) = (1/2 : ℝ) := by
    rw [hp_def]
    norm_num
  rw [hsub]
  have hpow : ((1/2 : ℝ) ^ n * (1/2 : ℝ)) = ((1/2 : ℝ) ^ (n+1)) := by
    rw [pow_succ]
  rw [hpow]
  have hnonneg : 0 ≤ (1/2 : ℝ) := by norm_num
  rw [ENNReal.ofReal_pow hnonneg]
  simp

/-- The direction of a value read (the second component of its step) is uniform on `Fin 4`. -/
theorem FrogModel.D3.map_dir_valLaw :
    FrogModel.D3.valLaw.map (fun x : FrogModel.D3.Val => x.1.2) = (uniformOn Set.univ : Measure (Fin 4)) := by
  -- valLaw = (stepLaw 3).prod coinLaw, and fun x => x.1.2 = Prod.snd ∘ Prod.fst
  have hvalLaw : valLaw = (stepLaw 3).prod coinLaw := rfl
  have hmap : (fun x : Val => x.1.2) = Prod.snd ∘ Prod.fst := rfl
  rw [hvalLaw, hmap]
  -- map_map: (μ.map f).map g = μ.map (g ∘ f)
  rw [← Measure.map_map measurable_snd measurable_fst]
  -- map_fst_prod: map Prod.fst (μ.prod ν) = (ν univ) • μ
  rw [Measure.map_fst_prod]
  -- coinLaw is a probability measure, so coinLaw univ = 1
  have hcoin_univ : coinLaw (Set.univ : Set ℕ) = 1 := by
    have : IsProbabilityMeasure coinLaw := inferInstance
    exact measure_univ
  rw [hcoin_univ, one_smul]
  -- Now we need: (stepLaw 3).map Prod.snd = uniformOn Set.univ on Fin 4
  -- stepLaw 3 = uniformOn Set.univ on Fin 3 × Fin 4
  unfold stepLaw
  -- Use ext_of_singleton to compare on singletons
  refine Measure.ext_of_singleton fun a => ?_
  -- Compute LHS on {a}
  rw [Measure.map_apply measurable_snd (measurableSet_singleton a)]
  -- The preimage of {a} under Prod.snd is univ ×ˢ {a}
  have hpreimage : Prod.snd ⁻¹' ({a} : Set (Fin 4)) = (Set.univ : Set (Fin 3)) ×ˢ {a} := by
    ext ⟨x, y⟩; simp
  rw [hpreimage]
  -- Now we have: uniformOn Set.univ (univ ×ˢ {a}) = uniformOn Set.univ {a}
  -- Convert everything to Finsets for uniformOn_apply_finset'
  let U3 : Finset (Fin 3) := Finset.univ
  let S : Finset (Fin 4) := {a}
  let U4 : Finset (Fin 4) := Finset.univ
  let U34 : Finset (Fin 3 × Fin 4) := Finset.univ
  let P : Finset (Fin 3 × Fin 4) := U3 ×ˢ S
  have hmeas_U34 : MeasurableSet (U34 : Set (Fin 3 × Fin 4)) := Finset.measurableSet _
  have hmeas_U4 : MeasurableSet (U4 : Set (Fin 4)) := Finset.measurableSet _
  have hmeas_S : MeasurableSet (S : Set (Fin 4)) := Finset.measurableSet _
  have hmeas_P : MeasurableSet (P : Set (Fin 3 × Fin 4)) := Finset.measurableSet _
  -- Rewrite everything to Finsets
  have huniv34 : (Set.univ : Set (Fin 3 × Fin 4)) = (U34 : Set (Fin 3 × Fin 4)) := by simp [U34]
  have huniv3 : (Set.univ : Set (Fin 3)) = (U3 : Set (Fin 3)) := by simp [U3]
  have huniv4 : (Set.univ : Set (Fin 4)) = (U4 : Set (Fin 4)) := by simp [U4]
  have hS : ({a} : Set (Fin 4)) = (S : Set (Fin 4)) := by simp [S]
  have hprod : ((U3 : Set (Fin 3)) ×ˢ (S : Set (Fin 4))) = (P : Set (Fin 3 × Fin 4)) := by
    simp [P]
  rw [huniv34, huniv3, huniv4, hS, hprod]
  -- Now apply uniformOn_apply_finset'
  rw [uniformOn_apply_finset' hmeas_U34 hmeas_P,
    uniformOn_apply_finset' hmeas_U4 hmeas_S]
  -- Now we have: #(U34 ∩ P) / #U34 = #(U4 ∩ S) / #U4
  simp [U3, S, U4, U34, P]
  -- Goal: 3 / 12 = 4⁻¹ in ℝ≥0∞
  have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
  have h3top : (3 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_inv_mul : (3 : ℝ≥0∞)⁻¹ * (3 : ℝ≥0∞) = 1 := ENNReal.inv_mul_cancel h3 h3top
  rw [ENNReal.div_eq_inv_mul]
  have h12 : (12 : ℝ≥0∞) = (3 : ℝ≥0∞) * (4 : ℝ≥0∞) := by norm_num
  rw [h12]
  rw [ENNReal.mul_inv (Or.inl h3) (Or.inl h3top)]
  rw [mul_assoc]
  rw [mul_comm (4 : ℝ≥0∞)⁻¹ (3 : ℝ≥0∞)]
  rw [← mul_assoc]
  rw [h_inv_mul]
  simp

/-- The steps of the frog pools of the frog-path space are i.i.d. uniform steps: the paths of the
planted model. -/
theorem FrogModel.D3.map_fp_paths :
    FrogModel.D3.fpMeasure.map (fun ω (q : FrogModel.D3.Frog × ℕ) => (ω (some q.1, q.2)).1) =
      Measure.infinitePi fun _ : FrogModel.D3.Frog × ℕ => stepLaw 3 := by
  let ι : FrogModel.D3.Frog × ℕ → Option FrogModel.D3.Frog × ℕ :=
    fun (φ, i) => (some φ, i)
  have hι_inj : Function.Injective ι := by
    intro x y h
    rcases x with ⟨φ₁, i₁⟩
    rcases y with ⟨φ₂, i₂⟩
    simp [ι] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  -- g(ω)(q) = ω(ι q)
  let g : (Option FrogModel.D3.Frog × ℕ → Val) → (FrogModel.D3.Frog × ℕ → Val) :=
    fun ω => ω ∘ ι
  have hg_meas : Measurable g := by
    apply measurable_pi_iff.mpr
    intro q
    -- g(ω)(q) = ω(ι q), which is the evaluation at ι q
    exact measurable_pi_apply (ι q)
  -- h(k)(q) = k(q).1 = Prod.fst (k q)
  let h : (FrogModel.D3.Frog × ℕ → Val) → (FrogModel.D3.Frog × ℕ → Step 3) :=
    fun k q => (k q).1
  have hh_meas : Measurable h := by
    apply measurable_pi_iff.mpr
    intro q
    -- h(k)(q) = (k q).1 = Prod.fst (k q)
    -- The map k ↦ k q is measurable_pi_apply q
    -- Composing with Prod.fst gives measurable_fst.comp (measurable_pi_apply q)
    exact measurable_fst.comp (measurable_pi_apply q)
  -- f(ω)(q) = (ω(some q.1, q.2)).1 = h(g ω)(q)
  have h_eq : (fun (ω : Option FrogModel.D3.Frog × ℕ → Val) (q : FrogModel.D3.Frog × ℕ) =>
      (ω (some q.1, q.2)).1) = h ∘ g := by
    ext ω q
    dsimp [g, h, ι]
    rfl
  rw [h_eq]
  -- Now we need: fpMeasure.map (h ∘ g) = infinitePi fun _ => stepLaw 3
  rw [← Measure.map_map hh_meas hg_meas]
  -- Now: (fpMeasure.map g).map h = ...
  rw [show FrogModel.D3.fpMeasure.map g = Measure.infinitePi fun (_ : FrogModel.D3.Frog × ℕ) => valLaw by
    rw [FrogModel.D3.fpMeasure, FrogModel.Pool.poolMeasure]
    dsimp [g]
    exact Measure.map_infinitePi_infinitePi_of_inj hι_inj]
  -- Now: (infinitePi fun _ => valLaw).map h = infinitePi fun _ => stepLaw 3
  -- But h(k)(q) = (k q).1 = Prod.fst (k q)
  -- So h = fun k q => Prod.fst (k q)
  -- We need to rewrite h in the form expected by infinitePi_map_pi
  have h_eq2 : h = (fun (k : FrogModel.D3.Frog × ℕ → Val) (q : FrogModel.D3.Frog × ℕ) => Prod.fst (k q)) := by
    ext k q
    dsimp [h]
    rfl
  rw [h_eq2]
  -- Now: (infinitePi fun _ => valLaw).map (fun k q => Prod.fst (k q)) = infinitePi fun _ => stepLaw 3
  -- Using infinitePi_map_pi with f i := Prod.fst
  -- The goal is: Measure.map (fun k q => Prod.fst (k q)) (Measure.infinitePi fun _ => valLaw) = Measure.infinitePi fun _ => stepLaw 3
  -- Rewrite using infinitePi_map_pi
  have h_pi := Measure.infinitePi_map_pi (μ := fun (_ : FrogModel.D3.Frog × ℕ) => valLaw)
    (f := fun (_ : FrogModel.D3.Frog × ℕ) => Prod.fst) (hf := fun i => measurable_fst)
  -- h_pi : (infinitePi ...).map (fun x i => Prod.fst (x i)) = infinitePi (fun i => (valLaw).map Prod.fst)
  -- But our LHS is (infinitePi ...).map (fun k q => Prod.fst (k q))
  -- These are the same by eta expansion
  simpa [FrogModel.D3.valLaw, Measure.map_fst_prod, measure_univ, one_smul] using h_pi

/-- Every property of the state at time `n` defines a measurable set of value sequences. -/
theorem FrogModel.D3.measurableSet_run (p : FrogModel.D3.Params) (k n : ℕ) (P : FrogModel.D3.St → Prop) :
    MeasurableSet {y : ℕ → FrogModel.D3.Val | P (FrogModel.D3.run p k y n)} := by
  have h_eq : {y : ℕ → FrogModel.D3.Val | P (FrogModel.D3.run p k y n)} =
      (fun (y : ℕ → FrogModel.D3.Val) (j : Fin n) => y j) ⁻¹'
        {z : Fin n → FrogModel.D3.Val | P (FrogModel.D3.runFin p k z)} := by
    ext y; simp [FrogModel.D3.runFin_eq_run]
  rw [h_eq]
  apply measurableSet_preimage
  · apply (measurable_pi_iff (X := fun (_ : Fin n) => FrogModel.D3.Val)).2
    intro j
    exact measurable_pi_apply (a := (j : ℕ))
  · have h_countable_S : Set.Countable {z : Fin n → FrogModel.D3.Val |
        P (FrogModel.D3.runFin p k z)} :=
      (Set.countable_univ (α := Fin n → FrogModel.D3.Val)).mono (Set.subset_univ _)
    exact h_countable_S.measurableSet

/-- **Strong Markov at a stopping time, integrated form.** For a stopping time `e` of an i.i.d. sequence
and a functional `G y b` that reads `y` only before `e y`, the integral of `G y (y shifted by e y)`
over `{e < ⊤}` is the integral of `G a b` over independent `a` (with `e a < ⊤`) and `b`. -/
theorem FrogModel.D3.lintegral_shift_stop {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (ν : Measure α) [IsProbabilityMeasure ν] (e : (ℕ → α) → ℕ∞)
    (he : ∀ (a a' : ℕ → α) (k : ℕ), e a = k → (∀ i < k, a i = a' i) → e a' = k)
    (hm : Measurable e) (G : (ℕ → α) → (ℕ → α) → ℝ≥0∞) (hG : Measurable (Function.uncurry G))
    (hloc : ∀ a a' b, (∀ i : ℕ, (i : ℕ∞) < e a → a i = a' i) → G a b = G a' b) :
    ∫⁻ y, (if e y < ⊤ then G y (fun t => y (t + (e y).toNat)) else 0)
        ∂(Measure.infinitePi fun _ : ℕ => ν) =
      ∫⁻ a, (if e a < ⊤ then ∫⁻ b, G a b ∂(Measure.infinitePi fun _ : ℕ => ν) else 0)
        ∂(Measure.infinitePi fun _ : ℕ => ν) := by
  set P := Measure.infinitePi fun _ : ℕ => ν with hP
  set F : (ℕ → α) → ℝ≥0∞ := fun y =>
    if e y < ⊤ then G y (fun t => y (t + (e y).toNat)) else 0 with hF
  set g : (ℕ → α) × (ℕ → α) → (ℕ → α) := fun p =>
    FrogModel.ZeroOne.glueAt (e p.1) p.1 p.2 with hg
  have h_map : (P.prod P).map g = P := by
    rw [hg]
    exact FrogModel.ZeroOne.map_glueAt ν e he hm
  have hg_meas : Measurable g := by
    rw [hg]
    refine measurable_pi_iff.mpr fun t => ?_
    have hF' : Measurable fun q : ((ℕ → α) × (ℕ → α)) × ℕ∞ =>
      FrogModel.ZeroOne.glueAt q.2 q.1.1 q.1.2 t := by
      refine measurable_from_prod_countable_left fun k => ?_
      by_cases h : (t : ℕ∞) < k
      · simp only [FrogModel.ZeroOne.glueAt, h, ite_true]
        exact (measurable_pi_apply t).comp measurable_fst
      · simp only [FrogModel.ZeroOne.glueAt, h, ite_false]
        exact (measurable_pi_apply _).comp measurable_snd
    exact hF'.comp (measurable_id.prodMk (hm.comp measurable_fst))
  -- Express F as a countable sum of indicator functions, to prove measurability
  have hF_eq : F = fun y => ∑' (k : ℕ), (if e y = (k : ℕ∞) then G y (fun t => y (t + k)) else 0) := by
    ext y
    rw [hF]
    by_cases h_lt_top : e y < ⊤
    · have h_ne_top : e y ≠ ⊤ := by
        intro h_eq_top; rw [h_eq_top] at h_lt_top; exact (by decide : ¬ ((⊤ : ℕ∞) < ⊤)) h_lt_top
      obtain ⟨k, hk⟩ := (ENat.ne_top_iff_exists (n := e y)).mp h_ne_top
      have hk_val : e y = (k : ℕ∞) := hk.symm
      have h_toNat : (e y).toNat = k := by
        rw [hk_val]
        simp
      simp [hk_val]
    · have h_eq_top : e y = ⊤ := by
        by_contra h_ne_top
        obtain ⟨k, hk⟩ := (ENat.ne_top_iff_exists (n := e y)).mp h_ne_top
        apply h_lt_top
        rw [← hk]
        exact ENat.natCast_lt_top k
      simp [h_eq_top]
  have hF_meas : Measurable F := by
    rw [hF_eq]
    refine Measurable.tsum fun k => ?_
    -- Each term: y ↦ (if e y = k then G y (fun t => y (t + k)) else 0)
    have h_set : MeasurableSet {(y : ℕ → α) | e y = (k : ℕ∞)} := by
      have h_singleton : MeasurableSet {x : ℕ∞ | x = (k : ℕ∞)} := MeasurableSet.of_discrete
      exact hm h_singleton
    have h_term_meas : Measurable (fun (y : ℕ → α) => G y (fun t => y (t + k))) := by
      have h_shift : Measurable (fun (y : ℕ → α) => (fun (t : ℕ) => y (t + k))) := by
        refine measurable_pi_iff.mpr fun i => (measurable_pi_apply (i + k))
      have h_pair : Measurable (fun (y : ℕ → α) => (y, fun t => y (t + k))) :=
        Measurable.prodMk measurable_id h_shift
      exact hG.comp h_pair
    refine Measurable.ite h_set h_term_meas measurable_const
  have h_pointwise : ∀ (a b : ℕ → α), F (g (a, b)) = (if e a < ⊤ then G a b else 0) := by
    intro a b
    rw [hF, hg]
    dsimp [FrogModel.ZeroOne.glueAt]
    by_cases h_ea_top : e a < ⊤
    · -- e a = k for some k : ℕ
      have h_ne_top : e a ≠ ⊤ := by
        intro h_eq_top; rw [h_eq_top] at h_ea_top; exact (by decide : ¬ ((⊤ : ℕ∞) < ⊤)) h_ea_top
      obtain ⟨k, hk⟩ := (ENat.ne_top_iff_exists (n := e a)).mp h_ne_top
      have hk_val : e a = (k : ℕ∞) := hk.symm
      have h_toNat : (e a).toNat = k := by rw [hk_val]; simp
      -- e (glueAt ...) = e a using he
      have h_agree : ∀ i < k, a i = (FrogModel.ZeroOne.glueAt (e a) a b) i := by
        intro i hi
        have h_lt : (i : ℕ∞) < e a := by rw [hk_val]; exact ENat.natCast_lt_natCast.mpr hi
        simp [FrogModel.ZeroOne.glueAt, h_lt]
      have h_ey : e (FrogModel.ZeroOne.glueAt (e a) a b) = e a := by
        have h := he a (FrogModel.ZeroOne.glueAt (e a) a b) k hk_val h_agree
        rw [← hk_val] at h
        exact h
      -- The shift: glueAt (e a) a b (t + k) = b t
      have h_shift : (fun t => (FrogModel.ZeroOne.glueAt (e a) a b) (t + k)) = b := by
        ext t
        simp [FrogModel.ZeroOne.glueAt, hk_val]
      -- G (glueAt ...) b = G a b using hloc
      have h_G : G (FrogModel.ZeroOne.glueAt (e a) a b) b = G a b := by
        apply (hloc a (FrogModel.ZeroOne.glueAt (e a) a b) b ?_).symm
        intro i hi
        simp [FrogModel.ZeroOne.glueAt, hi]
      -- Simplify using if_pos
      rw [ite_eq_left h_ea_top]  -- RHS: if e a < ⊤ then G a b else 0 → G a b
      rw [h_ey]  -- LHS: replace e (glueAt ...) with e a
      rw [ite_eq_left h_ea_top]  -- LHS: if e a < ⊤ then ... else 0 → the then branch
      rw [h_toNat]  -- replace (e a).toNat with k
      rw [hk_val]  -- replace e a with (k : ℕ∞)
      -- Goal: G (glueAt (k : ℕ∞) a b) (fun t => if ↑(t + k) < (k : ℕ∞) then a (t + k) else b (t + k - k)) = G a b
      -- The inner condition ↑(t + k) < (k : ℕ∞) is false
      have h_inner : (fun t => if ↑(t + k) < (k : ℕ∞) then a (t + k) else b (t + k - k)) = b := by
        ext t
        have h_lt_false : ¬ (↑(t + k) < (k : ℕ∞)) := by
          intro hlt
          have hle : (k : ℕ∞) ≤ ↑(t + k) := by
            simp [add_comm]
          exact (not_lt.mpr hle) hlt
        by_cases h : ↑(t + k) < (k : ℕ∞)
        · exfalso; exact h_lt_false h
        · simp
      rw [h_inner]
      -- Goal: G (glueAt (k : ℕ∞) a b) b = G a b
      simpa [hk_val] using h_G
    · -- e a = ⊤, then e (glueAt ...) = ⊤ too
      have h_ea_top_eq : e a = ⊤ := by
        by_contra h_ne_top
        obtain ⟨k, hk'⟩ := (ENat.ne_top_iff_exists (n := e a)).mp h_ne_top
        apply h_ea_top
        rw [← hk']
        exact ENat.natCast_lt_top k
      have h_ey_top : ¬ e (FrogModel.ZeroOne.glueAt (e a) a b) < ⊤ := by
        intro h_lt
        have h_ne_top : e (FrogModel.ZeroOne.glueAt (e a) a b) ≠ ⊤ := by
          intro h_eq_top; rw [h_eq_top] at h_lt; exact (by decide : ¬ ((⊤ : ℕ∞) < ⊤)) h_lt
        obtain ⟨k, hk⟩ := (ENat.ne_top_iff_exists (n := e (FrogModel.ZeroOne.glueAt (e a) a b))).mp h_ne_top
        -- For i < k, glueAt agrees with a (since e a = ⊤, so (i : ℕ∞) < e a is true)
        have h_agree : ∀ i < k, (FrogModel.ZeroOne.glueAt (e a) a b) i = a i := by
          intro i hi
          simp [FrogModel.ZeroOne.glueAt, h_ea_top_eq]
        -- Then he gives e a = k, contradicting h_ea_top
        have h_ea_eq_k : e a = (k : ℕ∞) :=
          he (FrogModel.ZeroOne.glueAt (e a) a b) a k (by rw [hk]) h_agree
        rw [h_ea_top_eq] at h_ea_eq_k
        have : (k : ℕ∞) ≠ ⊤ := by exact ENat.natCast_ne_top k
        exact this h_ea_eq_k.symm
      simp [h_ea_top, h_ey_top]
  calc
    ∫⁻ y, F y ∂P = ∫⁻ y, F y ∂((P.prod P).map g) := by rw [h_map]
    _ = ∫⁻ p, F (g p) ∂(P.prod P) := by
      rw [MeasureTheory.lintegral_map hF_meas hg_meas]
    _ = ∫⁻ a, ∫⁻ b, F (g (a, b)) ∂P ∂P := by
      rw [MeasureTheory.lintegral_prod (f := fun p => F (g p)) ?_]
      -- need AEMeasurable (fun p => F (g p)) (P.prod P)
      -- Since F and g are measurable, the composition is measurable
      exact (hF_meas.comp hg_meas).aemeasurable
    _ = ∫⁻ a, ∫⁻ b, (if e a < ⊤ then G a b else 0) ∂P ∂P := by
      refine lintegral_congr fun a => lintegral_congr fun b => ?_
      rw [h_pointwise a b]
    _ = ∫⁻ a, (if e a < ⊤ then ∫⁻ b, G a b ∂P else 0) ∂P := by
      refine lintegral_congr fun a => ?_
      by_cases h_ea_top : e a < ⊤
      · simp [h_ea_top]
      · simp [h_ea_top]
    _ = ∫⁻ a, (if e a < ⊤ then ∫⁻ b, G a b ∂P else 0) ∂P := rfl

/-- Every probability in `[0, 1]` is the mass of a set of coins (binary expansion). -/
theorem FrogModel.D3.exists_coin_set (r : ℝ≥0∞) (hr : r ≤ 1) :
    ∃ A : Set ℕ, FrogModel.D3.coinLaw A = r := by
  have hr_ne_top : r ≠ ∞ := by
    have h_lt : r < ∞ := hr.trans_lt (by norm_num : (1 : ℝ≥0∞) < ∞)
    exact ne_of_lt h_lt
  set p : ℝ := 1/2 with hp_def
  have hp_pos : 0 < p := by norm_num
  have hp_nonneg : 0 ≤ p := by norm_num
  have hp_lt_one : p < 1 := by norm_num
  -- Define the partial sum s n = ∑_{j < n} (if j ∈ A then p^(j+1) else 0)
  -- and A = {n | s n + p^(n+1) ≤ r.toReal}
  let s : ℕ → ℝ := Nat.rec 0 (fun n s_n =>
    s_n + (if s_n + p ^ (n+1 : ℕ) ≤ r.toReal then p ^ (n+1 : ℕ) else 0))
  let A : Set ℕ := {n | s n + p ^ (n+1 : ℕ) ≤ r.toReal}
  have hs0 : s 0 = 0 := rfl
  have hs_succ (n : ℕ) : s (n+1) = s n + (if n ∈ A then p ^ (n+1 : ℕ) else 0) := by
    simp [s, A]
  -- Invariant 1: s n ≤ r.toReal
  have h_s_le (n : ℕ) : s n ≤ r.toReal := by
    induction' n with n ih
    · rw [hs0]
      exact ENNReal.toReal_nonneg
    · rw [hs_succ n]
      split_ifs with h
      · -- h : n ∈ A, which means s n + p^(n+1) ≤ r.toReal
        simpa [A] using h
      · -- h : ¬ n ∈ A, then s (n+1) = s n ≤ r.toReal by IH
        simpa [h] using ih
  -- Invariant 2: r.toReal - s n ≤ p ^ n
  have h_diff_le (n : ℕ) : r.toReal - s n ≤ p ^ n := by
    induction' n with n ih
    · -- n = 0: r.toReal - 0 ≤ p^0 = 1
      rw [hs0, sub_zero]
      have h_r_toReal_le_one : r.toReal ≤ 1 := by
        have := ENNReal.toReal_le_coe_of_le_coe hr
        simpa using this
      simpa using h_r_toReal_le_one
    · -- n → n+1
      rw [hs_succ n]
      split_ifs with h
      · -- h : n ∈ A, so s n + p^(n+1) ≤ r.toReal
        dsimp [A] at h
        -- We need: r.toReal - (s n + p^(n+1)) ≤ p^(n+1)
        -- From IH: r.toReal - s n ≤ p^n
        -- So r.toReal - s n - p^(n+1) ≤ p^n - p^(n+1) = p^(n+1)
        have h_pow_sub : p ^ n - p ^ (n+1 : ℕ) = p ^ (n+1 : ℕ) := by
          calc
            p ^ n - p ^ (n+1 : ℕ) = p ^ n - p ^ n * p := by simp [pow_succ]
            _ = p ^ n * (1 - p) := by ring
            _ = p ^ n * p := by
              dsimp [p]
              ring
            _ = p ^ (n+1 : ℕ) := by simp [pow_succ]
        have h_sub : r.toReal - s n - p ^ (n+1 : ℕ) ≤ p ^ n - p ^ (n+1 : ℕ) := by
          linarith
        rw [h_pow_sub] at h_sub
        linarith
      · -- h : ¬ n ∈ A
        dsimp [A] at h
        -- h : ¬ s n + p ^ (n+1 : ℕ) ≤ r.toReal, so s n + p^(n+1) > r.toReal
        -- Hence r.toReal - s n < p^(n+1)
        have h_lt : r.toReal - s n < p ^ (n+1 : ℕ) := by
          linarith
        -- The goal is r.toReal - (s n + 0) ≤ p^(n+1), which simplifies to r.toReal - s n ≤ p^(n+1)
        -- This follows from h_lt
        simpa using h_lt.le
  -- Now we have: 0 ≤ r.toReal - s n ≤ p^n → 0
  -- Since p^n → 0, we get r.toReal - s n → 0, so s n → r.toReal
  have h_tendsto : Filter.Tendsto s Filter.atTop (nhds (r.toReal)) := by
    have h_nonneg : ∀ n, 0 ≤ r.toReal - s n := by
      intro n
      have : s n ≤ r.toReal := h_s_le n
      linarith
    have h_bound : ∀ n, r.toReal - s n ≤ p ^ n := h_diff_le
    have hp_tendsto : Filter.Tendsto (fun n : ℕ => p ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hp_nonneg hp_lt_one
    -- Use squeeze theorem
    have h_diff_tendsto : Filter.Tendsto (fun n => r.toReal - s n) Filter.atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop _)
        hp_tendsto h_nonneg h_bound
    -- Now s n = r.toReal - (r.toReal - s n) → r.toReal - 0 = r.toReal
    have h_eq : s = fun n => r.toReal - (r.toReal - s n) := by
      ext n
      linarith [h_s_le n]
    rw [h_eq]
    simpa using Filter.Tendsto.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => r.toReal) Filter.atTop _)
      h_diff_tendsto
  -- HasSum (fun n => (if n ∈ A then p^(n+1) else 0)) r.toReal
  have h_hasSum : HasSum (fun n : ℕ => (if n ∈ A then p ^ (n+1 : ℕ) else 0)) r.toReal := by
    -- The partial sums are s n
    have h_partial_sums (n : ℕ) : (∑ i ∈ Finset.range n, (if i ∈ A then p ^ (i+1 : ℕ) else 0)) = s n := by
      induction' n with n ih
      · simp [s, hs0]
      · rw [Finset.sum_range_succ, ih, hs_succ n]
    -- Nonnegativity of terms
    have h_nonneg_terms : ∀ i, 0 ≤ (if i ∈ A then p ^ (i+1 : ℕ) else 0) := by
      intro i
      split_ifs
      · apply pow_nonneg hp_nonneg
      · exact le_refl 0
    -- Now use the lemma that HasSum f r iff the partial sums tend to r
    apply (hasSum_iff_tendsto_nat_of_nonneg h_nonneg_terms r.toReal).mpr
    simpa [h_partial_sums] using h_tendsto
  -- Now convert to ENNReal
  have h_coinLaw_singleton (n : ℕ) : FrogModel.D3.coinLaw {n} = ENNReal.ofReal (p ^ (n+1 : ℕ)) := by
    have hp_ne_zero : (⟨1/2, by norm_num, by norm_num⟩ : unitInterval) ≠ 0 := by
      intro h
      have : (1/2 : ℝ) = 0 := by simpa using congrArg Subtype.val h
      norm_num at this
    calc
      FrogModel.D3.coinLaw {n} = ProbabilityTheory.geometricMeasure ⟨1/2, by norm_num, by norm_num⟩ {n} := rfl
      _ = ENNReal.ofReal (((1 : ℝ) - (1/2 : ℝ)) ^ n * (1/2 : ℝ)) := by
        rw [ProbabilityTheory.geometricMeasure_singleton hp_ne_zero n]
      _ = ENNReal.ofReal ((1/2 : ℝ) ^ (n+1 : ℕ)) := by
        ring_nf
      _ = ENNReal.ofReal (p ^ (n+1 : ℕ)) := by rfl
  have h_coinLaw_A : FrogModel.D3.coinLaw A = r := by
    have h_meas : MeasurableSet A := MeasurableSet.of_discrete (s := A)
    have h_summable : Summable (fun n : ℕ => A.indicator (fun x => p ^ (x+1 : ℕ)) n) := by
      -- h_hasSum gives HasSum for the same function
      simpa [Set.indicator] using h_hasSum.summable
    have h_nonneg_indicator : ∀ n, 0 ≤ A.indicator (fun x => p ^ (x+1 : ℕ)) n := by
      intro n
      simp [Set.indicator]
      split_ifs
      · apply pow_nonneg hp_nonneg
      · exact le_refl 0
    calc
      FrogModel.D3.coinLaw A = (∑' x : ℕ, A.indicator (fun x => FrogModel.D3.coinLaw {x}) x) := by
        rw [Measure.tsum_indicator_apply_singleton FrogModel.D3.coinLaw A h_meas]
      _ = (∑' x : ℕ, A.indicator (fun x => ENNReal.ofReal (p ^ (x+1 : ℕ))) x) := by
        simp [h_coinLaw_singleton]
      _ = (∑' x : ℕ, ENNReal.ofReal (A.indicator (fun x => p ^ (x+1 : ℕ)) x)) := by
        refine tsum_congr (fun n => ?_)
        simp [Set.indicator]
        split_ifs <;> simp
      _ = ENNReal.ofReal (∑' x : ℕ, A.indicator (fun x => p ^ (x+1 : ℕ)) x) := by
        rw [ENNReal.ofReal_tsum_of_nonneg h_nonneg_indicator h_summable]
      _ = ENNReal.ofReal (r.toReal) := by
        simpa [Set.indicator] using congrArg ENNReal.ofReal h_hasSum.tsum_eq
      _ = r := by
        rw [ENNReal.ofReal_toReal hr_ne_top]
  exact ⟨A, h_coinLaw_A⟩

/-- The count never decreases along the run, and the top closure never waits for a kill coin. -/
theorem FrogModel.D3.count_upd_ge (p : FrogModel.D3.Params) (s : FrogModel.D3.St) (x : FrogModel.D3.Val)
    (hs : ∀ f, s.stack.getLast? = some f → f.killing = false) :
    FrogModel.D3.count s ≤ FrogModel.D3.count (FrogModel.D3.upd p s x) ∧
      ∀ f, (FrogModel.D3.upd p s x).stack.getLast? = some f → f.killing = false := by
  -- helper lemma about getLast? of a list with at least one element
  have hgetLast?_cons_ne_nil (a : FrogModel.D3.Frame) (l : List FrogModel.D3.Frame) (h : l ≠ []) :
      (a :: l).getLast? = l.getLast? := by
    cases l
    · contradiction
    · rfl
  -- helper: count is defined via getLast?
  have hcount_def (st : FrogModel.D3.St) : FrogModel.D3.count st =
      match st.stack.getLast? with
      | none => st.out.length
      | some f => f.ups.length := rfl
  -- helper: getLast? of a singleton
  have hgetLast?_singleton (f : FrogModel.D3.Frame) : (f :: []).getLast? = some f := by simp
  -- helper: getLast? of a nonempty list
  have hgetLast?_cons (f : FrogModel.D3.Frame) (l : List FrogModel.D3.Frame) : (f :: l).getLast? =
      match l with
      | [] => some f
      | _ => l.getLast? := by
    cases l
    · simp
    · rfl
  -- We analyze by cases on the stack
  cases hstack : s.stack with
  | nil =>
      simp [FrogModel.D3.upd, hstack, FrogModel.D3.count]
  | cons f rest =>
      simp [FrogModel.D3.upd, hstack]
      -- Now we have the inner match on f.killing
      split
      · -- Case: f.killing = true
        rename_i hkilling
        split
        · -- Subcase: rest = []
          have hlast := hs f (by simp [hstack])
          rw [hlast] at hkilling
          simp at hkilling
        · -- Subcase: rest = g :: rest'
          rename_i g rest'
          -- We need to analyze:
          -- Let kept := p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked s.marks f.v) x.2
          -- Let rets := if kept then f.ups else []
          -- Let marks' := if kept then s.marks else s.marks ∪ kids f.v
          -- The result is: settle marks' ({g with pool := (g.pool ++ rets).take p.P} :: rest')
          -- We need to show count doesn't decrease and the last frame has killing = false
          -- Let's set up local definitions for these
          set kept := p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (FrogModel.D3.unmarked s.marks f.v) x.2 with hkept
          set rets := if kept then f.ups else [] with hrets
          set marks' := if kept then s.marks else s.marks ∪ FrogModel.D3.kids f.v with hmarks'
          set h := {g with pool := (g.pool ++ rets).take p.P} with hh
          -- Goal: count (f :: g :: rest') ≤ count (settle marks' (h :: rest')) ∧ ...
          -- We analyze by cases on rest'
          cases rest' with
          | nil =>
              -- rest' = [], so frames = [h]
              -- Analyze the condition in settle
              simp [FrogModel.D3.settle, hh]
              split
              · -- h.pool = [] ∧ h.ghost = none: settle returns ⟨[], marks', h.ups⟩
                -- count = h.ups.length = g.ups.length = count s
                -- second conjunct: stack empty, vacuously true
                refine ⟨?_, ?_⟩
                · -- count s ≤ count (settle ...)
                  -- count s = g.ups.length, count (result) = h.ups.length = g.ups.length
                  simp [FrogModel.D3.count, hstack]
                · -- ∀ f', ... → f'.killing = false
                  intro f' hf'
                  simp at hf'
              · -- otherwise: settle returns ⟨[h], marks', []⟩
                -- count = h.ups.length = g.ups.length = count s
                -- last frame is h, and h.killing = g.killing = false by hs
                refine ⟨?_, ?_⟩
                · simp [FrogModel.D3.count, hstack]
                · intro f' hf'
                  -- hf' : (⟨[h], marks', []⟩).stack.getLast? = some f'
                  -- which simplifies to some h = some f', so f' = h
                  simp at hf'
                  rcases hf' with rfl
                  -- Need to show h.killing = false
                  -- h.killing = g.killing (since h = {g with ...})
                  -- and g.killing = false by hs (since g is the last frame of f :: g :: [])
                  have hg_killing : g.killing = false := by
                    apply hs g
                    simp [hstack]
                  -- Now h.killing = g.killing = false
                  simp [hg_killing]
          | cons g' rest'' =>
              -- rest' = g' :: rest'', so frames = h :: g' :: rest''
              -- This has at least 2 frames, so settle returns a nonempty stack
              -- Analyze the condition in settle
              simp [FrogModel.D3.settle, hh]
              split
              · -- h.pool = [] ∧ h.ghost = none: returns {h with killing := true} :: g' :: rest''
                -- count = 0 (out = []), last frame is last of (g' :: rest'')
                -- count s = (last of (g :: g' :: rest'')).ups.length = (last of (g' :: rest'')).ups.length
                -- So count s = count (result)
                -- And the last frame has killing = false by hs
                refine ⟨?_, ?_⟩
                · -- count s ≤ count (result)
                  -- Both equal (last frame of (g' :: rest'')).ups.length
                  -- The getLast? is never none because the list is nonempty
                  have hlast : (g' :: rest'').getLast? ≠ none := by simp
                  cases hlast' : (g' :: rest'').getLast? with
                  | none => exact (hlast hlast').elim
                  | some f => simp [FrogModel.D3.count, hstack, hlast']
                · intro f' hf'
                  -- hf' : (settle ...).stack.getLast? = some f'
                  -- The stack is {h with killing := true} :: g' :: rest''
                  -- getLast? = getLast? (g' :: rest'')
                  -- So f' is the last frame of (g' :: rest'')
                  -- By hs, this frame has killing = false
                  simp at hf'
                  -- hf' simplifies to (g' :: rest'').getLast? = some f'
                  -- So f' is the last frame of (g' :: rest'')
                  -- By hs, this frame has killing = false
                  -- We can use hs directly
                  have h_s_last : s.stack.getLast? = some f' := by
                    simp [hstack, hf']
                  exact hs f' h_s_last
              · -- otherwise: returns h :: g' :: rest''
                -- count = 0, last frame is last of (g' :: rest'')
                refine ⟨?_, ?_⟩
                · have hlast : (g' :: rest'').getLast? ≠ none := by simp
                  cases hlast' : (g' :: rest'').getLast? with
                  | none => exact (hlast hlast').elim
                  | some f => simp [FrogModel.D3.count, hstack, hlast']
                · intro f' hf'
                  -- hf' : (h :: g' :: rest'').getLast? = some f'
                  -- getLast? = (g' :: rest'').getLast?
                  simp at hf'
                  -- hf' : (g' :: rest'').getLast? = some f'
                  have h_s_last : s.stack.getLast? = some f' := by
                    simp [hstack, hf']
                  exact hs f' h_s_last
      · -- Case: f.killing = false
        rename_i hkilling
        split
        · -- Subcase: f.ghost = some (φ, u)
          -- `split` on Option (Frog × Vertex 3) introduces 4 hypotheses:
          -- x✝ : Option (Frog × Vertex 3), φ✝ : Frog, snd✝ : Vertex 3, heq✝ : f.ghost = some (φ✝, snd✝)
          -- We rename them: skip x✝, use φ for φ✝, u for snd✝, heq for heq✝
          rename_i _ φ u heq
          -- Now φ : Frog, u : Vertex 3, heq : f.ghost = some (φ, u)
          -- Compute u' := ghostStep u x.1
          set u' := FrogModel.D3.ghostStep u x.1 with hu'
          -- Split on u' = f.v
          split
          · -- u' = f.v
            -- Returns: {f with pool := φ :: f.pool, ghost := none} :: rest
            -- count unchanged (still f.ups.length), last frame unchanged
            refine ⟨?_, ?_⟩
            · -- count s ≤ count (result)
              -- We need to show count s ≤ count (result) where result.stack = {f with ...} :: rest
              -- Since both stacks are nonempty, count only depends on the last frame's ups
              -- The last frame of (f :: rest) equals the last frame of ({f with ...} :: rest)
              cases rest with
              | nil =>
                -- Both stacks are [f] and [{f with ...}], last frame is f in both cases
                simp [FrogModel.D3.count, hstack]
              | cons h t =>
                -- Both stacks have at least 2 elements, last frame is the last of t in both cases
                simp [FrogModel.D3.count, hstack]
                -- Goal: match (h :: t).getLast? with ... ≤ match (h :: t).getLast? with ...
                -- The getLast? is never none because the list is nonempty
                have hlast : (h :: t).getLast? ≠ none := by simp
                cases hlast' : (h :: t).getLast? with
                | none => exact (hlast hlast').elim
                | some f' => simp
            · -- second conjunct: last frame has killing = false
              intro f' hf'
              -- Goal: f'.killing = false
              -- hf' : ({f with ...} :: rest).getLast? = some f'
              -- We use cases on rest to relate this to s.stack
              cases rest with
              | nil =>
                simp at hf'
                -- hf' : {f with ...} = f'
                -- Goal: f'.killing = false
                have hkilling' : f.killing = false := (Bool.not_eq_true f.killing).mp hkilling
                rw [← hf']
                -- Goal: ({f with ...}).killing = false
                simpa using hkilling'
              | cons h t =>
                simp at hf'
                -- hf' : (h :: t).getLast? = some f'
                -- Goal: f'.killing = false
                -- From hs, since s.stack.getLast? = some f'
                have h_s_last : s.stack.getLast? = some f' := by
                  simp [hstack, hf']
                exact hs f' h_s_last
          · -- u' ≠ f.v
            split
            · -- u'.length = f.v.length + p.L
              -- Calls settle s.marks ({f with ghost := none} :: rest)
              -- This is similar to the kill case: settle preserves the last frame
              -- We analyze by cases on rest
              cases rest with
              | nil =>
                -- rest = [], settle on [{f with ghost := none}]
                simp [FrogModel.D3.settle]
                split
                · -- f has empty pool and no ghost: settle returns empty stack, out = f.ups
                  -- count s = f.ups.length = count (result)
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                  · intro f' hf'; simp at hf'
                · -- otherwise: settle returns [{f with ghost := none}], out = []
                  -- count s = f.ups.length = count (result)
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                  · intro f' hf'
                    simp at hf'
                    -- hf' : f' = {f with ghost := none}
                    -- Need: f'.killing = false
                    rw [← hf']
                    -- ({f with ghost := none}).killing = f.killing = false
                    have hkilling' : f.killing = false := (Bool.not_eq_true f.killing).mp hkilling
                    simp [hkilling']
              | cons h t =>
                -- rest = h :: t, settle on ({f with ghost := none} :: h :: t)
                -- This has at least 2 frames, so settle returns a nonempty stack
                simp [FrogModel.D3.settle]
                split
                · -- f has empty pool and no ghost: returns {f with killing := true} :: h :: t
                  -- count = 0, last frame is last of (h :: t)
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                    have hlast : (h :: t).getLast? ≠ none := by simp
                    cases hlast' : (h :: t).getLast? with
                    | none => exact (hlast hlast').elim
                    | some f' => simp
                  · intro f' hf'
                    simp at hf'
                    -- hf' : (h :: t).getLast? = some f'
                    -- Goal: f'.killing = false
                    have h_s_last : s.stack.getLast? = some f' := by
                      simp [hstack, hf']
                    exact hs f' h_s_last
                · -- otherwise: returns {f with ghost := none} :: h :: t
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                    have hlast : (h :: t).getLast? ≠ none := by simp
                    cases hlast' : (h :: t).getLast? with
                    | none => exact (hlast hlast').elim
                    | some f' => simp
                  · intro f' hf'
                    simp at hf'
                    -- hf' : (h :: t).getLast? = some f'
                    have h_s_last : s.stack.getLast? = some f' := by
                      simp [hstack, hf']
                    exact hs f' h_s_last
            · -- otherwise
              -- Returns: {f with ghost := some (φ, u')} :: rest
              -- count unchanged, last frame unchanged
              refine ⟨?_, ?_⟩
              · cases rest with
                | nil => simp [FrogModel.D3.count, hstack]
                | cons h t =>
                  simp [FrogModel.D3.count, hstack]
                  have hlast : (h :: t).getLast? ≠ none := by simp
                  cases hlast' : (h :: t).getLast? with
                  | none => exact (hlast hlast').elim
                  | some f' => simp
              · intro f' hf'
                cases rest with
                | nil =>
                  simp at hf'
                  -- hf' : {f with ...} = f'
                  have hkilling' : f.killing = false := (Bool.not_eq_true f.killing).mp hkilling
                  rw [← hf']
                  simpa using hkilling'
                | cons h t =>
                  simp at hf'
                  -- hf' : (h :: t).getLast? = some f'
                  have h_s_last : s.stack.getLast? = some f' := by
                    simp [hstack, hf']
                  exact hs f' h_s_last
        · -- Subcase: f.ghost = none
          rename_i hghost
          split
          · -- Subcase: f.pool = []
            -- Returns s unchanged
            refine ⟨by simp [FrogModel.D3.count], ?_⟩
            intro f' h
            rw [hstack] at h
            apply hs f'
            rw [hstack]
            exact h
          · -- Subcase: f.pool = φ_head :: φ_tail
            rename_i φ_head φ_tail heq
            -- φ_head : Frog, φ_tail : List Frog, heq : f.pool = φ_head :: φ_tail
            split
            · -- Subcase: x.1.2 = 0
              -- Updates ups: ups' := if f.ups.length < p.V then f.ups ++ [φ_head] else f.ups
              -- Then calls settle s.marks ({f with pool := φ_tail, ups := ups'} :: rest)
              set ups' := if f.ups.length < p.V then f.ups ++ [φ_head] else f.ups with hups'
              -- Result: settle s.marks ({f with pool := φ_tail, ups := ups'} :: rest)
              -- We analyze by cases on rest
              cases rest with
              | nil =>
                -- rest = [], settle on [{f with pool := φ_tail, ups := ups'}]
                simp [FrogModel.D3.settle]
                split
                · -- f has empty pool and no ghost: settle returns empty stack, out = ups'
                  -- count s = f.ups.length ≤ ups'.length = count (result)
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                    -- Need: f.ups.length ≤ ups'.length
                    -- ups' is f.ups or f.ups ++ [φ_head], so length is ≥ f.ups.length
                    rw [hups']
                    split
                    · simp
                    · rfl
                  · intro f' hf'; simp at hf'
                · -- otherwise: settle returns [{f with ...}], out = []
                  -- count s = f.ups.length ≤ ups'.length = count (result)
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                    rw [hups']
                    split
                    · simp
                    · rfl
                  · intro f' hf'
                    simp at hf'
                    -- hf' : f' = {f with pool := φ_tail, ups := ups'}
                    -- Need: f'.killing = false
                    rw [← hf']
                    have hkilling' : f.killing = false := (Bool.not_eq_true f.killing).mp hkilling
                    simp [hkilling']
              | cons h t =>
                -- rest = h :: t, settle on ({f with ...} :: h :: t)
                simp [FrogModel.D3.settle]
                split
                · -- f has empty pool and no ghost: returns {f with killing := true} :: h :: t
                  -- count = 0, last frame is last of (h :: t)
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                    have hlast : (h :: t).getLast? ≠ none := by simp
                    cases hlast' : (h :: t).getLast? with
                    | none => exact (hlast hlast').elim
                    | some f' => simp
                  · intro f' hf'
                    simp at hf'
                    -- hf' : (h :: t).getLast? = some f'
                    have h_s_last : s.stack.getLast? = some f' := by
                      simp [hstack, hf']
                    exact hs f' h_s_last
                · -- otherwise: returns {f with ...} :: h :: t
                  refine ⟨?_, ?_⟩
                  · simp [FrogModel.D3.count, hstack]
                    have hlast : (h :: t).getLast? ≠ none := by simp
                    cases hlast' : (h :: t).getLast? with
                    | none => exact (hlast hlast').elim
                    | some f' => simp
                  · intro f' hf'
                    simp at hf'
                    -- hf' : (h :: t).getLast? = some f'
                    have h_s_last : s.stack.getLast? = some f' := by
                      simp [hstack, hf']
                    exact hs f' h_s_last
            · -- Subcase: x.1.2 ≠ 0
              -- z := x.1.2.pred h_ne_zero :: f.v
              -- Various subcases, all result in frames with killing = false
              rename_i h_ne_zero
              set z := x.1.2.pred h_ne_zero :: f.v with hz
              -- Now analyze the conditions in upd
              -- First condition: f.v.length = p.m ∨ (f.isR = false ∧ z ∈ s.marks)
              split
              · -- f.v.length = p.m ∨ (f.isR = false ∧ z ∈ s.marks)
                -- Returns: {f with pool := φ_tail, ghost := some (φ_head, z)} :: rest
                -- count unchanged (f.ups.length), last frame unchanged
                refine ⟨?_, ?_⟩
                · -- count s ≤ count (result)
                  -- Both sides have the same getLast? since the stack structure is the same
                  cases rest with
                  | nil => simp [FrogModel.D3.count, hstack]
                  | cons h t =>
                    simp [FrogModel.D3.count, hstack]
                    have hlast : (h :: t).getLast? ≠ none := by simp
                    cases hlast' : (h :: t).getLast? with
                    | none => exact (hlast hlast').elim
                    | some f' => simp
                · -- second conjunct: last frame has killing = false
                  intro f' hf'
                  -- hf' : (result.stack).getLast? = some f'
                  -- Goal: f'.killing = false
                  cases rest with
                  | nil =>
                    -- result.stack = [{f with ...}], getLast? = some ({f with ...})
                    -- hf' : some ({f with ...}) = some f' → f' = {f with ...}
                    simp at hf'
                    -- hf' : {f with ...} = f'
                    rw [← hf']
                    -- Goal: ({f with ...}).killing = false
                    have hkilling' : f.killing = false := (Bool.not_eq_true f.killing).mp hkilling
                    simp [hkilling']
                  | cons h t =>
                    -- result.stack = {f with ...} :: h :: t
                    -- getLast? = (h :: t).getLast?
                    simp at hf'
                    -- hf' : (h :: t).getLast? = some f'
                    -- s.stack = f :: h :: t, getLast? = (h :: t).getLast? = some f'
                    have h_s_last : s.stack.getLast? = some f' := by
                      simp [hstack, hf']
                    exact hs f' h_s_last
              · -- ¬ (f.v.length = p.m ∨ (f.isR = false ∧ z ∈ s.marks))
                split
                · -- z ∉ s.marks
                  -- Returns new frame with killing := false pushed on top
                  refine ⟨?_, ?_⟩
                  · -- count s ≤ count (result)
                    cases rest with
                    | nil => simp [FrogModel.D3.count, hstack]
                    | cons h t =>
                      simp [FrogModel.D3.count, hstack]
                      have hlast : (h :: t).getLast? ≠ none := by simp
                      cases hlast' : (h :: t).getLast? with
                      | none => exact (hlast hlast').elim
                      | some f' => simp
                  · intro f' hf'
                    cases rest with
                    | nil =>
                      simp at hf'
                      rw [← hf']
                      have hkilling' : f.killing = false := (Bool.not_eq_true f.killing).mp hkilling
                      simp [hkilling']
                    | cons h t =>
                      simp at hf'
                      have h_s_last : s.stack.getLast? = some f' := by
                        simp [hstack, hf']
                      exact hs f' h_s_last
                · -- z ∈ s.marks
                  -- Returns new frame with killing := false pushed on top
                  refine ⟨?_, ?_⟩
                  · cases rest with
                    | nil => simp [FrogModel.D3.count, hstack]
                    | cons h t =>
                      simp [FrogModel.D3.count, hstack]
                      have hlast : (h :: t).getLast? ≠ none := by simp
                      cases hlast' : (h :: t).getLast? with
                      | none => exact (hlast hlast').elim
                      | some f' => simp
                  · intro f' hf'
                    cases rest with
                    | nil =>
                      simp at hf'
                      rw [← hf']
                      have hkilling' : f.killing = false := (Bool.not_eq_true f.killing).mp hkilling
                      simp [hkilling']
                    | cons h t =>
                      simp at hf'
                      have h_s_last : s.stack.getLast? = some f' := by
                        simp [hstack, hf']
                      exact hs f' h_s_last
