module

public import FrogModel.Pool.Step

@[expose] public section

/-!
# Pools: the proofs of the frozen statements (Lemma 4.3 of the paper)

Both readings are instances of `readGen` (Pool/Defs.lean): `poolRead` with `poolCoord`,
`freshRead` with `freshCoord`. Along every label sequence both read distinct coordinates whose
laws are the pool laws, so `map_readGen_eq` gives `map_poolRead`; the laws of all prefixes then
give `map_poolSeq` (`measure_ext_of_prefix`). On the fresh space piece `n + 1` is row `n` at the
label of the first `n` pieces, the row is independent of them with law `infinitePi μ`, and
`map_prod_eq_bind` gives `map_freshRead_succ`. The `_holds` theorems at the end prove the frozen
statements of Pool/Statement.lean.
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.Pool

/-- The pieces read on the pool space are measurable (statement `MeasurablePoolRead`). -/
theorem measurable_poolRead {I E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I)
    [Countable I] (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i})
    (n : ℕ) : Measurable fun ω : I × ℕ → E => poolRead sel ω n := by
  have h : (fun ω : I × ℕ → E => poolRead sel ω n) = fun ω => readGen poolCoord sel ω n :=
    funext fun ω => poolRead_eq_readGen sel ω n
  rw [h]
  exact measurable_readGen poolCoord sel hsel n

/-- The pieces read on the fresh space are measurable (statement `MeasurableFreshRead`). -/
theorem measurable_freshRead {I E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I)
    [Countable I] (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i})
    (n : ℕ) : Measurable fun ω : ℕ × I → E => freshRead sel ω n := by
  have h : (fun ω : ℕ × I → E => freshRead sel ω n) = fun ω => readGen freshCoord sel ω n :=
    funext fun ω => freshRead_eq_readGen sel ω n
  rw [h]
  exact measurable_readGen freshCoord sel hsel n

/-- All the pieces read are measurable (statement `MeasurablePoolSeq`). -/
theorem measurable_poolSeq {I E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I)
    [Countable I] (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) :
    Measurable (poolSeq sel) ∧ Measurable (freshSeq sel) :=
  ⟨measurable_pi_iff.2 fun k =>
      (measurable_pi_apply (Fin.last k)).comp (measurable_poolRead sel hsel (k + 1)),
    measurable_pi_iff.2 fun k =>
      (measurable_pi_apply (Fin.last k)).comp (measurable_freshRead sel hsel (k + 1))⟩

/-- **Pools** (statement `MapPoolRead`). -/
theorem map_poolRead {I E : Type*} [MeasurableSpace E] [Countable I] (μ : I → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) (n : ℕ) :
    (poolMeasure μ).map (fun ω => poolRead sel ω n) =
      (freshMeasure μ).map (fun ω => freshRead sel ω n) := by
  have hp : (fun ω : I × ℕ → E => poolRead sel ω n) = fun ω => readGen poolCoord sel ω n :=
    funext fun ω => poolRead_eq_readGen sel ω n
  have hf : (fun ω : ℕ × I → E => freshRead sel ω n) = fun ω => readGen freshCoord sel ω n :=
    funext fun ω => freshRead_eq_readGen sel ω n
  rw [hp, hf]
  exact map_readGen_eq poolCoord freshCoord sel hsel (fun p : I × ℕ => μ p.1)
    (fun p : ℕ × I => μ p.2) μ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ ℓ _ => injective_cmap_poolCoord ℓ) (fun _ ℓ _ => injective_cmap_freshCoord ℓ) n

/-- The first `n` pieces of the sequence are the pieces of a reading of length `n`. -/
theorem prefix_poolSeq {I E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (ω : I × ℕ → E) (n : ℕ) : (fun j : Fin n => poolSeq sel ω j) = poolRead sel ω n := by
  rw [poolRead_eq_readGen, ← readGen_last]
  funext j
  simp only [poolSeq, poolRead_eq_readGen]

/-- The first `n` pieces of the fresh sequence are the pieces of a reading of length `n`. -/
theorem prefix_freshSeq {I E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (ω : ℕ × I → E) (n : ℕ) : (fun j : Fin n => freshSeq sel ω j) = freshRead sel ω n := by
  rw [freshRead_eq_readGen, ← readGen_last]
  funext j
  simp only [freshSeq, freshRead_eq_readGen]

/-- **Pools, whole sequence** (statement `MapPoolSeq`). -/
theorem map_poolSeq {I E : Type*} [MeasurableSpace E] [Countable I] (μ : I → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) :
    (poolMeasure μ).map (poolSeq sel) = (freshMeasure μ).map (freshSeq sel) := by
  obtain ⟨hp, hf⟩ := measurable_poolSeq sel hsel
  have : IsProbabilityMeasure (poolMeasure μ) := by unfold poolMeasure; infer_instance
  have : IsProbabilityMeasure (freshMeasure μ) := by unfold freshMeasure; infer_instance
  refine measure_ext_of_prefix fun n => ?_
  have hpre : Measurable fun (x : ℕ → E) (j : Fin n) => x j :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  rw [Measure.map_map hpre hp, Measure.map_map hpre hf]
  have e1 : (fun x : ℕ → E => fun j : Fin n => x j) ∘ poolSeq sel = fun ω => poolRead sel ω n :=
    funext fun ω => prefix_poolSeq sel ω n
  have e2 : (fun x : ℕ → E => fun j : Fin n => x j) ∘ freshSeq sel =
      fun ω => freshRead sel ω n :=
    funext fun ω => prefix_freshSeq sel ω n
  rw [e1, e2]
  exact map_poolRead μ sel hsel n

/-- `Fin.snoc y` is measurable. -/
theorem measurable_snoc_right {E : Type*} [MeasurableSpace E] {n : ℕ} (y : Fin n → E) :
    Measurable (Fin.snoc (α := fun _ => E) y) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_id'
  | cast i => simpa only [Fin.snoc_castSucc] using measurable_const

/-- **One step on the fresh space** (statement `MapFreshReadSucc`). -/
theorem map_freshRead_succ {I E : Type*} [MeasurableSpace E] [Countable I] (μ : I → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (sel : ∀ k : ℕ, (Fin k → E) → I)
    (hsel : ∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) (n : ℕ) :
    (freshMeasure μ).map (fun ω => freshRead sel ω (n + 1)) =
      ((freshMeasure μ).map (fun ω => freshRead sel ω n)).bind
        (fun y => (μ (sel n y)).map (Fin.snoc (α := fun _ => E) y)) := by
  have : IsProbabilityMeasure (freshMeasure μ) := by unfold freshMeasure; infer_instance
  set F : (Fin n → E) × (I → E) → Fin (n + 1) → E :=
    fun x => Fin.snoc (α := fun _ => E) x.1 (x.2 (sel n x.1)) with hF
  have hFm : Measurable F := measurable_snoc_apply_sel n (sel n) (hsel n)
  have hX := measurable_freshRead sel hsel n
  have hR : Measurable fun ω : ℕ × I → E => fun i => ω (n, i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hpair : (fun ω => freshRead sel ω (n + 1)) =
      F ∘ fun ω : ℕ × I → E => (freshRead sel ω n, fun i => ω (n, i)) :=
    funext fun ω => freshRead_succ_eq sel ω n
  rw [hpair, ← Measure.map_map hFm (hX.prodMk hR),
    (indepFun_freshRead_row μ sel hsel n).map_prod_eq_prod_map_map hX.aemeasurable
      hR.aemeasurable, map_row_freshMeasure μ n, map_prod_eq_bind _ _ hFm]
  congr 1
  funext y
  have hc : (fun r : I → E => F (y, r)) =
      Fin.snoc (α := fun _ => E) y ∘ fun r : I → E => r (sel n y) := rfl
  rw [hc, ← Measure.map_map (measurable_snoc_right y) (measurable_pi_apply _),
    Measure.infinitePi_map_eval]

/-! The frozen statements (Pool/Statement.lean) hold. -/

universe u v

/-- The frozen `MeasurablePoolRead` holds. -/
theorem measurablePoolRead_holds : MeasurablePoolRead.{u, v} :=
  fun _ _ _ sel _ hsel n => measurable_poolRead sel hsel n

/-- The frozen `MeasurablePoolSeq` holds. -/
theorem measurablePoolSeq_holds : MeasurablePoolSeq.{u, v} :=
  fun _ _ _ sel _ hsel => measurable_poolSeq sel hsel

/-- The frozen `MeasurableFreshRead` holds. -/
theorem measurableFreshRead_holds : MeasurableFreshRead.{u, v} :=
  fun _ _ _ sel _ hsel n => measurable_freshRead sel hsel n

/-- The frozen `MapPoolRead` holds. -/
theorem mapPoolRead_holds : MapPoolRead.{u, v} :=
  fun _ _ _ _ μ _ sel hsel n => map_poolRead μ sel hsel n

/-- The frozen `MapPoolSeq` holds. -/
theorem mapPoolSeq_holds : MapPoolSeq.{u, v} :=
  fun _ _ _ _ μ _ sel hsel => map_poolSeq μ sel hsel

/-- The frozen `MapFreshReadSucc` holds. -/
theorem mapFreshReadSucc_holds : MapFreshReadSucc.{u, v} :=
  fun _ _ _ _ μ _ sel hsel n => map_freshRead_succ μ sel hsel n

end FrogModel.Pool
