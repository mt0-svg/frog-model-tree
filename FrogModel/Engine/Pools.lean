module

public import FrogModel.Engine.FK
public import FrogModel.Pool.Main

@[expose] public section

/-!
# The root engine: i.i.d. sequences read from pools

With
one law `μ` for every pool, the pieces read from the pools are i.i.d. of law `μ`
(`map_poolSeq_const`), and pairing consecutive coordinates of an i.i.d. sequence gives an i.i.d.
sequence of pairs (`map_pairs_iid`).
-/

open MeasureTheory
open scoped ENNReal

open Set in
/-- Drawing a tuple of length `n` i.i.d. and then one more piece gives a tuple of length `n + 1`
i.i.d. -/
theorem FrogModel.Engine.pi_bind_snoc {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ).bind (fun y => μ.map (Fin.snoc (α := fun _ => E) y)) =
      Measure.pi fun _ : Fin (n + 1) => μ := by
  have hF : Measurable fun p : (Fin n → E) × E => Fin.snoc (α := fun _ => E) p.1 p.2 := by
    refine measurable_pi_iff.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using measurable_snd
    | cast j => simpa only [Fin.snoc_castSucc] using (measurable_fst.eval (a := j) : Measurable fun p : (Fin n → E) × E => p.1 j)
  rw [← FrogModel.Pool.map_prod_eq_bind _ _ hF]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun p : (Fin n → E) × E => Fin.snoc (α := fun _ => E) p.1 p.2) ⁻¹' univ.pi s =
      univ.pi (fun j : Fin n => s j.castSucc) ×ˢ s (Fin.last n) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod, Fin.forall_fin_succ',
      Fin.snoc_castSucc, Fin.snoc_last]
  rw [Measure.map_apply hF (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod, Measure.pi_pi,
    Fin.prod_univ_castSucc]

theorem FrogModel.Engine.map_freshRead_const {I E : Type*} [MeasurableSpace E] [Countable I]
    (μ : Measure E) [IsProbabilityMeasure μ] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) (n : ℕ) :
    (FrogModel.Pool.freshMeasure fun _ : I => μ).map
        (fun ω => FrogModel.Pool.freshRead sel ω n) = Measure.pi fun _ : Fin n => μ := by
  induction' n with n ih
  · -- n = 0: freshRead sel ω 0 = Fin.elim0, constant map
    have h_read_zero : (fun ω : ℕ × I → E => FrogModel.Pool.freshRead sel ω 0) = fun _ => Fin.elim0 := by
      ext ω; rfl
    rw [h_read_zero]
    rw [MeasureTheory.Measure.map_const]
    have h_prob : MeasureTheory.IsProbabilityMeasure (FrogModel.Pool.freshMeasure (fun _ : I => μ)) := by
      dsimp [FrogModel.Pool.freshMeasure]
      infer_instance
    have h_univ : (FrogModel.Pool.freshMeasure (fun _ : I => μ)) Set.univ = 1 :=
      h_prob.measure_univ
    rw [h_univ]
    simp
    rw [MeasureTheory.Measure.pi_of_empty (fun _ : Fin 0 => μ)]
    congr
  · -- n → n+1
    rw [FrogModel.Pool.map_freshRead_succ (fun _ : I => μ) sel hsel n]
    rw [ih]
    rw [FrogModel.Engine.pi_bind_snoc μ n]

/-- With one law `μ` for every pool, the sequence read from the pools is i.i.d. of law `μ`. -/
theorem FrogModel.Engine.map_poolSeq_const {I E : Type*} [MeasurableSpace E] [Countable I]
    (μ : Measure E) [IsProbabilityMeasure μ] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) :
    (FrogModel.Pool.poolMeasure fun _ : I => μ).map (FrogModel.Pool.poolSeq sel) =
      Measure.infinitePi fun _ : ℕ => μ := by
  rw [FrogModel.Pool.map_poolSeq (fun _ : I => μ) sel hsel]
  have hf := (FrogModel.Pool.measurable_poolSeq sel hsel).2
  have : IsProbabilityMeasure (FrogModel.Pool.freshMeasure fun _ : I => μ) := by
    unfold FrogModel.Pool.freshMeasure; infer_instance
  refine FrogModel.Pool.measure_ext_of_prefix fun n => ?_
  have hpre : Measurable fun (x : ℕ → E) (j : Fin n) => x j :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  rw [Measure.map_map hpre hf, FrogModel.Engine.map_prefix_iid μ n]
  have e : (fun x : ℕ → E => fun j : Fin n => x j) ∘ FrogModel.Pool.freshSeq sel =
      fun ω => FrogModel.Pool.freshRead sel ω n :=
    funext fun ω => FrogModel.Pool.prefix_freshSeq sel ω n
  rw [e]
  exact FrogModel.Engine.map_freshRead_const μ sel hsel n


/-- The pairing `(k, j) ↦ 2 k + j` of `ℕ × Fin 2` with `ℕ`. -/
def FrogModel.Engine.pairIdxEquiv : ℕ × Fin 2 ≃ ℕ where
  toFun := fun ⟨k, j⟩ => 2 * k + j.val
  invFun := fun n => (n / 2, ⟨n % 2, Nat.mod_lt n (by norm_num : 0 < 2)⟩)
  left_inv := by
    intro ⟨k, j⟩
    have hk : (2 * k + j.val) / 2 = k := by omega
    have hj : (2 * k + j.val) % 2 = j.val := by omega
    ext <;> simp [hk, hj]
  right_inv := by
    intro n
    simp [Nat.div_add_mod]

theorem FrogModel.Engine.pairIdxEquiv_fst (k : ℕ) (j : Fin 2) : FrogModel.Engine.pairIdxEquiv (k, j) = 2 * k + j.val := rfl

theorem FrogModel.Engine.pairIdxEquiv_zero (k : ℕ) : FrogModel.Engine.pairIdxEquiv (k, 0) = 2 * k := by
  simp [FrogModel.Engine.pairIdxEquiv]

theorem FrogModel.Engine.pairIdxEquiv_one (k : ℕ) : FrogModel.Engine.pairIdxEquiv (k, 1) = 2 * k + 1 := by
  simp [FrogModel.Engine.pairIdxEquiv]

/-- `pairIdxEquiv` as a measurable equivalence. -/
def FrogModel.Engine.pairIdxMEquiv : ℕ × Fin 2 ≃ᵐ ℕ where
  toEquiv := FrogModel.Engine.pairIdxEquiv
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

theorem FrogModel.Engine.map_pairs_iid {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (g : E → E → F)
    (hg : Measurable (Function.uncurry g)) :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun ω k => g (ω (2 * k)) (ω (2 * k + 1))) =
      Measure.infinitePi fun _ : ℕ => (μ.prod μ).map (Function.uncurry g) := by
  let e := FrogModel.Engine.pairIdxMEquiv
  -- Define the intermediate maps
  let f₁ : (ℕ → E) → (ℕ × Fin 2 → E) := fun ω p => ω (e p)
  let f₂ : (ℕ × Fin 2 → E) → (ℕ → Fin 2 → E) := fun f k j => f (k, j)
  let f₃ : (ℕ → Fin 2 → E) → (ℕ → F) := fun f k => g (f k 0) (f k 1)
  -- The full map is f₃ ∘ f₂ ∘ f₁
  have h_full : (fun (ω : ℕ → E) (k : ℕ) => g (ω (2 * k)) (ω (2 * k + 1))) = f₃ ∘ f₂ ∘ f₁ := by
    ext ω k
    -- e (k, 0) = 2*k and e (k, 1) = 2*k + 1
    have h0 : e (k, (0 : Fin 2)) = 2 * k := by
      simp [e, FrogModel.Engine.pairIdxMEquiv, FrogModel.Engine.pairIdxEquiv_zero]
    have h1 : e (k, (1 : Fin 2)) = 2 * k + 1 := by
      simp [e, FrogModel.Engine.pairIdxMEquiv, FrogModel.Engine.pairIdxEquiv_one]
    simp [f₁, f₂, f₃, h0, h1]
  rw [h_full]
  let ν := Measure.infinitePi fun _ : ℕ => μ
  have hf₁_meas : Measurable f₁ := by
    have h_eq : f₁ = (MeasurableEquiv.piCongrLeft (fun _ : ℕ => E) e).symm := by
      ext ω p
      -- f₁ ω p = ω (e p)
      -- (MeasurableEquiv.piCongrLeft ... e).symm ω p = ω (e p)
      rfl
    rw [h_eq]
    exact ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => E) e.toEquiv).symm).measurable
  have hf₂_meas : Measurable f₂ := by
    have h_eq : f₂ = (MeasurableEquiv.curry ℕ (Fin 2) E) := by
      ext f k j; rfl
    rw [h_eq]
    exact (MeasurableEquiv.curry ℕ (Fin 2) E).measurable
  have hf₃_meas : Measurable f₃ := by
    refine Measurable.of_eval (fun k => ?_)
    have h_eval : Measurable (fun (f : ℕ → Fin 2 → E) => (f k 0, f k 1)) := by
      -- f ↦ (f k) is measurable, then evaluate at 0 and 1
      have h1 : Measurable (fun (f : ℕ → Fin 2 → E) => f k) := measurable_pi_apply (a := k)
      have h2 : Measurable (fun (g : Fin 2 → E) => (g 0, g 1)) := by
        refine Measurable.prod (measurable_pi_apply (a := (0 : Fin 2))) (measurable_pi_apply (a := (1 : Fin 2)))
      -- Compose: first apply k, then apply h2
      exact h2.comp h1
    have h_eq : (fun (f : ℕ → Fin 2 → E) => g (f k 0) (f k 1)) =
        (Function.uncurry g) ∘ (fun (f : ℕ → Fin 2 → E) => (f k 0, f k 1)) := by
      ext f; rfl
    rw [h_eq]
    exact hg.comp h_eval
  -- Use Measure.map_map to break down the composition
  have h_map_comp : Measure.map (f₃ ∘ f₂ ∘ f₁) ν = Measure.map f₃ (Measure.map (f₂ ∘ f₁) ν) := by
    rw [Measure.map_map hf₃_meas (hf₂_meas.comp hf₁_meas)]
  have h_map_comp2 : Measure.map (f₂ ∘ f₁) ν = Measure.map f₂ (Measure.map f₁ ν) := by
    rw [Measure.map_map hf₂_meas hf₁_meas]
  rw [h_map_comp, h_map_comp2]
  -- Now the goal is: Measure.map f₃ (Measure.map f₂ (Measure.map f₁ ν)) = Measure.infinitePi fun _ : ℕ => (μ.prod μ).map (Function.uncurry g)
  -- Step 1: Measure.map f₁ ν = Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)
  have h_step1 : Measure.map f₁ ν = Measure.infinitePi (fun _ : ℕ × Fin 2 => μ) := by
    -- f₁ = (MeasurableEquiv.piCongrLeft (fun _ : ℕ => E) e.toEquiv).symm
    let f := (MeasurableEquiv.piCongrLeft (fun _ : ℕ => E) e.toEquiv)
    have h_f₁_eq : f₁ = f.symm := by
      ext ω p; rfl
    rw [h_f₁_eq]
    -- Goal: Measure.map f.symm ν = Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)
    -- ν = Measure.infinitePi (fun _ : ℕ => μ)
    -- Use Measure.infinitePi_map_piCongrLeft
    have h_lemma := Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) e.toEquiv
    -- h_lemma : Measure.map f (Measure.infinitePi fun i => (fun _ : ℕ => μ) (e.toEquiv i)) = Measure.infinitePi (fun _ : ℕ => μ)
    -- The LHS simplifies: (fun _ : ℕ => μ) (e.toEquiv i) = μ
    -- So h_lemma gives: Measure.map f (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)) = ν
    -- Now we want: Measure.map f.symm ν = Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)
    -- Using h_lemma backwards: ν = Measure.map f (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ))
    -- So: Measure.map f.symm ν = Measure.map f.symm (Measure.map f (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)))
    --   = Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)
    have h_lemma' : ν = Measure.map f (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)) := by
      -- From h_lemma, since the LHS simplifies
      simpa [ν] using h_lemma.symm
    rw [h_lemma']
    rw [Measure.map_map f.symm.measurable f.measurable]
    simp
  -- Step 2: Measure.map f₂ (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)) = Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin 2 => μ))
  have h_step2 : Measure.map f₂ (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin 2 => μ)) := by
    have h_f₂_eq : f₂ = (MeasurableEquiv.curry ℕ (Fin 2) E) := by
      ext f k j; rfl
    rw [h_f₂_eq]
    rw [Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin 2) => μ)]
  -- Step 3: Measure.infinitePi (fun _ : Fin 2 => μ) = Measure.pi (fun _ : Fin 2 => μ)
  have h_step3 : Measure.infinitePi (fun _ : Fin 2 => μ) = Measure.pi (fun _ : Fin 2 => μ) := by
    rw [Measure.infinitePi_eq_pi]
  -- Step 4: Combine steps 2 and 3
  have h_step4 : Measure.map f₂ (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ)) =
      Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin 2 => μ)) := by
    rw [h_step2, h_step3]
  -- Step 5: Measure.map f₃ (Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin 2 => μ))) = Measure.infinitePi (fun _ : ℕ => (Measure.pi (fun _ : Fin 2 => μ)).map (fun v => g (v 0) (v 1)))
  have h_step5 : Measure.map f₃ (Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin 2 => μ))) =
      Measure.infinitePi (fun _ : ℕ => (Measure.pi (fun _ : Fin 2 => μ)).map (fun v => g (v 0) (v 1))) := by
    -- Use Measure.infinitePi_map_pi with explicit arguments
    let μ' := fun (_ : ℕ) => Measure.pi (fun _ : Fin 2 => μ)
    let f' := fun (_ : ℕ) => (fun (v : Fin 2 → E) => g (v 0) (v 1))
    have hm : ∀ (i : ℕ), Measurable (f' i) := by
      intro i
      have h_pair : Measurable (fun (v : Fin 2 → E) => (v 0, v 1)) := by
        refine Measurable.prod (measurable_pi_apply (a := (0 : Fin 2))) (measurable_pi_apply (a := (1 : Fin 2)))
      have : f' i = (Function.uncurry g) ∘ (fun (v : Fin 2 → E) => (v 0, v 1)) := by rfl
      rw [this]
      exact hg.comp h_pair
    have h_eq : f₃ = fun (x : (i : ℕ) → (Fin 2 → E)) (i : ℕ) => f' i (x i) := by
      ext x i; simp [f₃, f']
    rw [h_eq]
    rw [Measure.infinitePi_map_pi (Y := fun _ : ℕ => F) (f := f') μ' hm]
  -- Step 6: (Measure.pi (fun _ : Fin 2 => μ)).map (fun v => g (v 0) (v 1)) = (μ.prod μ).map (Function.uncurry g)
  have h_step6 : (Measure.pi (fun _ : Fin 2 => μ)).map (fun v => g (v 0) (v 1)) =
      (μ.prod μ).map (Function.uncurry g) := by
    have h_eq : (fun (v : Fin 2 → E) => g (v 0) (v 1)) =
        (Function.uncurry g) ∘ (MeasurableEquiv.finTwoArrow (α := E)) := by
      ext v; rfl
    rw [h_eq]
    rw [← Measure.map_map hg (MeasurableEquiv.finTwoArrow (α := E)).measurable]
    rw [(measurePreserving_finTwoArrow μ).map_eq]
  -- Now combine everything
  calc
    Measure.map f₃ (Measure.map f₂ (Measure.map f₁ ν))
        = Measure.map f₃ (Measure.map f₂ (Measure.infinitePi (fun _ : ℕ × Fin 2 => μ))) := by rw [h_step1]
    _ = Measure.map f₃ (Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin 2 => μ))) := by rw [h_step4]
    _ = Measure.infinitePi (fun _ : ℕ => (Measure.pi (fun _ : Fin 2 => μ)).map (fun v => g (v 0) (v 1))) := by rw [h_step5]
    _ = Measure.infinitePi (fun _ : ℕ => (μ.prod μ).map (Function.uncurry g)) := by rw [h_step6]
