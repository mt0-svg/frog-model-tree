module

public import FrogModel.D3.LaneA.Meas
public import FrogModel.D3.LaneA.Indep

@[expose] public section

/-!
# Own-path coins, Lemma 10.3 of the paper (d = 3)

The proof of Lemma 10.3. The coin of the entry `i + 1` is the event that the path of the entrant
`inl i` reaches `y` (`coinOf`). It reads only that path and has probability `1/3` (`prob_reach`);
the curve up to `G(i)` and the earlier coins read none of it, since the woken set with `l ≤ i`
entrants and the planted count only read the paths of the frogs other than the entrants
`inl l, inl (l + 1), ...` (`woken_congr`, `plantedG_congr`). When the coin is true, `inl i` is
counted by `G(i + 1)` and not by `G(i)`, so `G(i + 1) ≥ G(i) + 1` (`plantedG_add_coin_le`).
The coupling is the law of `(plantedCurve m, coinOf)` under `pathMeasure`
(`coin_coupling_proof`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface

theorem woken_inl_lt {m k : ℕ} {π : PFrog → ℕ → Step 3} {i : ℕ}
    (h : Woken m k π (Sum.inl i)) : i < k := by
  cases h with
  | ent _ hi => exact hi

theorem not_woken_zero {m : ℕ} {π : PFrog → ℕ → Step 3} {φ : PFrog} (h : Woken m 0 π φ) :
    False := by
  induction h with
  | ent i hi => exact absurd hi (Nat.not_lt_zero i)
  | wake _ _ _ _ _ _ ih => exact ih

theorem woken_mono {m k k' : ℕ} (hk : k ≤ k') {π : PFrog → ℕ → Step 3} {φ : PFrog}
    (h : Woken m k π φ) : Woken m k' π φ := by
  induction h with
  | ent i hi => exact Woken.ent i (by omega)
  | wake ψ v n _ hv hp ih => exact Woken.wake ψ v n ih hv hp

/-- The woken set with `k` entrants reads only the paths of the frogs other than the entrants
`inl i`, `i ≥ k`. -/
theorem woken_congr {m k : ℕ} {π π' : PFrog → ℕ → Step 3}
    (h : ∀ φ : PFrog, (∀ i, φ = Sum.inl i → i < k) → π φ = π' φ) (φ : PFrog)
    (hφ : Woken m k π φ) : Woken m k π' φ := by
  induction hφ with
  | ent i hi => exact Woken.ent i hi
  | wake ψ v n hψ hv hp ih =>
    refine Woken.wake ψ v n ih hv ?_
    have hπ : π ψ = π' ψ := h ψ fun i hi => by subst hi; exact woken_inl_lt hψ
    unfold pos at hp ⊢
    rw [← hπ]
    exact hp

theorem plantedG_congr {m k : ℕ} {π π' : PFrog → ℕ → Step 3}
    (h : ∀ φ : PFrog, (∀ i, φ = Sum.inl i → i < k) → π φ = π' φ) :
    plantedG m k π = plantedG m k π' := by
  have h' : ∀ φ : PFrog, (∀ i, φ = Sum.inl i → i < k) → π' φ = π φ := fun φ hφ =>
    (h φ hφ).symm
  have key : ∀ (ρ ρ' : PFrog → ℕ → Step 3),
      (∀ φ : PFrog, (∀ i, φ = Sum.inl i → i < k) → ρ φ = ρ' φ) → ∀ φ,
      (Woken m k ρ φ ∧ ∃ n, pos ρ φ n = none) → (Woken m k ρ' φ ∧ ∃ n, pos ρ' φ n = none) := by
    rintro ρ ρ' hρ φ ⟨hw, n, hn⟩
    refine ⟨woken_congr hρ φ hw, n, ?_⟩
    have hφ : ρ φ = ρ' φ := hρ φ fun i hi => by subst hi; exact woken_inl_lt hw
    unfold pos at hn ⊢
    rw [← hφ]
    exact hn
  unfold plantedG
  congr 1
  ext φ
  exact ⟨key π π' h φ, key π' π h' φ⟩

theorem plantedG_zero (m : ℕ) (π : PFrog → ℕ → Step 3) : plantedG m 0 π = 0 := by
  unfold plantedG
  rw [Set.encard_eq_zero]
  ext φ
  exact ⟨fun h => (not_woken_zero h.1).elim, fun h => h.elim⟩

open Classical in
/-- The coin of the entry `i + 1`: the path of the entrant `inl i` reaches `y`. -/
noncomputable def coinOf (π : PFrog → ℕ → Step 3) (i : ℕ) : Bool :=
  decide (∃ n, pos π (Sum.inl i) n = none)

open Classical in
theorem coinOf_eq_true {π : PFrog → ℕ → Step 3} {i : ℕ} :
    coinOf π i = true ↔ ∃ n, pos π (Sum.inl i) n = none := by
  unfold coinOf
  exact decide_eq_true_iff

theorem coinOf_congr {π π' : PFrog → ℕ → Step 3} {i : ℕ} (h : π (Sum.inl i) = π' (Sum.inl i)) :
    coinOf π i = coinOf π' i := by
  unfold coinOf pos
  rw [h]

/-- `G(i) + ξ_i ≤ G(i + 1)`, pathwise. -/
theorem plantedG_add_coin_le (m i : ℕ) (π : PFrog → ℕ → Step 3) :
    plantedG m i π + (if coinOf π i then 1 else 0) ≤ plantedG m (i + 1) π := by
  have hsub : {φ | Woken m i π φ ∧ ∃ n, pos π φ n = none} ⊆
      {φ | Woken m (i + 1) π φ ∧ ∃ n, pos π φ n = none} := fun φ h =>
    ⟨woken_mono (Nat.le_succ i) h.1, h.2⟩
  cases hc : coinOf π i with
  | true =>
    simp only [↓reduceIte]
    have hnot : Sum.inl i ∉ {φ | Woken m i π φ ∧ ∃ n, pos π φ n = none} := fun h =>
      lt_irrefl i (woken_inl_lt h.1)
    have hin : Sum.inl i ∈ {φ | Woken m (i + 1) π φ ∧ ∃ n, pos π φ n = none} :=
      ⟨Woken.ent i (Nat.lt_succ_self i), coinOf_eq_true.1 hc⟩
    unfold plantedG
    rw [← Set.encard_insert_of_notMem hnot]
    exact Set.encard_le_encard (Set.insert_subset hin hsub)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    exact Set.encard_le_encard hsub

theorem measurable_coinOf (i : ℕ) : Measurable fun π : PFrog → ℕ → Step 3 => coinOf π i := by
  refine measurable_to_bool ?_
  have hset : (fun π : PFrog → ℕ → Step 3 => coinOf π i) ⁻¹' {true} =
      {π | ∃ n, pos π (Sum.inl i) n = none} := by
    ext π
    exact coinOf_eq_true
  rw [hset]
  exact measurableSet_reach _

/-- The curve and the coins. -/
noncomputable def coinMap (m : ℕ) (π : PFrog → ℕ → Step 3) : (ℕ → ℕ∞) × (ℕ → Bool) :=
  (plantedCurve m π, coinOf π)

theorem measurable_coinMap (m : ℕ) : Measurable (coinMap m) :=
  (measurable_pi_iff.2 fun k => measurable_plantedG m k).prodMk
    (measurable_pi_iff.2 fun i => measurable_coinOf i)

/-- **`coin_coupling`** (Lemma 10.3). -/
theorem coin_coupling_proof : coin_coupling := by
  intro m
  have hΦ := measurable_coinMap m
  refine ⟨pathMeasure.map (coinMap m), inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hΦ]
    rfl
  · intro i
    have hf : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 i := by fun_prop
    have hs : MeasurableSet {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.2 i = true} := by
      show MeasurableSet ((fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 i) ⁻¹' {true})
      exact hf (measurableSet_singleton _)
    rw [Measure.map_apply hΦ hs]
    have hset : coinMap m ⁻¹' {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.2 i = true} =
        {π | ∃ n, pos π (Sum.inl i) n = none} := by
      ext π
      exact coinOf_eq_true
    rw [hset, prob_reach_proof (Sum.inl i)]
    simp [frogDepth]
  · intro i
    have hf : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    have hg : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) =>
        ((fun l : Fin (i + 1) => z.1 l), (fun l : Fin i => z.2 l)) := by fun_prop
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    rw [Measure.map_apply hΦ ((hf hs).inter (hg ht)), Measure.map_apply hΦ (hf hs),
      Measure.map_apply hΦ (hg ht), Set.preimage_inter, Set.inter_comm]
    have key := infinitePi_inter_of_dependsOn (Measure.infinitePi fun _ : ℕ => stepLaw 3)
      ({Sum.inl i} : Set PFrog) _ _ (hΦ (hg ht)) (hΦ (hf hs)) ?_ ?_
    · exact key.trans (mul_comm _ _)
    · intro π π' hππ' hπ
      simp only [Set.mem_preimage] at hπ ⊢
      have heq : ((fun l : Fin (i + 1) => (coinMap m π').1 l), (fun l : Fin i => (coinMap m π').2 l))
          = ((fun l : Fin (i + 1) => (coinMap m π).1 l), (fun l : Fin i => (coinMap m π).2 l)) := by
        refine Prod.ext (funext fun l => ?_) (funext fun l => ?_)
        · show plantedG m l π' = plantedG m l π
          refine plantedG_congr fun φ hφ => (hππ' φ ?_).symm
          rintro rfl
          have := hφ i rfl
          omega
        · show coinOf π' l = coinOf π l
          refine coinOf_congr (hππ' _ ?_).symm
          simp only [Set.mem_singleton_iff, Sum.inl.injEq]
          omega
      rw [heq]
      exact hπ
    · intro π π' hππ' hπ
      simp only [Set.mem_preimage] at hπ ⊢
      have heq : (coinMap m π').2 i = (coinMap m π).2 i :=
        coinOf_congr (hππ' _ rfl).symm
      rw [heq]
      exact hπ
  · have hmeas : MeasurableSet {z : (ℕ → ℕ∞) × (ℕ → Bool) |
        z.1 0 = 0 ∧ ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1)} := by
      have hset : {z : (ℕ → ℕ∞) × (ℕ → Bool) |
          z.1 0 = 0 ∧ ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1)} =
          (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 0) ⁻¹' {0} ∩
            ⋂ i, (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => (z.1 i, z.1 (i + 1), z.2 i)) ⁻¹'
              {p : ℕ∞ × ℕ∞ × Bool | p.1 + (if p.2.2 then 1 else 0) ≤ p.2.1} := by
        ext z
        simp
      have h0 : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 0 := by fun_prop
      rw [hset]
      refine (h0 (measurableSet_singleton 0)).inter (MeasurableSet.iInter fun i => ?_)
      have h3 : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => (z.1 i, z.1 (i + 1), z.2 i) := by
        fun_prop
      exact h3 (Set.to_countable _).measurableSet
    rw [ae_map_iff hΦ.aemeasurable hmeas]
    exact Filter.Eventually.of_forall fun π =>
      ⟨plantedG_zero m π, fun i => plantedG_add_coin_le m i π⟩

end FrogModel.D3.LaneA
