module

public import FrogModel.D3.LaneA.Depth

@[expose] public section

/-!
# The first vertex at depth `D` is uniform (d = 3)

The symmetry step of the proof of Lemma 11.5 of the paper. The level relabeling `relabSeq σ`
permutes, in every step taken at depth `k` (the depth walk `dW`), the child letter by `σ k`, and
keeps the steps to the parent. It keeps the depth walk (`dW_relabSeq`), so `relabSeq σ⁻¹` undoes it, and it preserves the i.i.d. law of the steps (`map_relabSeq`: a prefix
cylinder goes to a prefix cylinder, all of mass `12^-N`). The walk from `w` of the relabeled
steps is the image of the walk by the tree map `relabV σ` (letter at depth `k + 1` permuted by
`σ k`; `walkStar_relabSeq`), which fixes `w` and maps `replicate D 0` to any vertex of depth `D`
for a suitable `σ` (`exists_relabV_replicate`). So the `3^D` events "the first vertex at depth `D`
is `v`" have the same probability, and each has probability at most `3^-D` (`seqLaw_firstD_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface

/-- The step `ξ` with its child letter permuted by `τ`; a step to the parent is kept. -/
def relab (τ : Equiv.Perm (Fin 3)) (ξ : Step 3) : Step 3 :=
  if h : ξ.2 = 0 then ξ else (ξ.1, (τ (ξ.2.pred h)).succ)

/-- The level relabeling: the step at time `n`, taken at depth `dW x n`, has its child letter
permuted by `σ (dW x n).toNat`. -/
def relabSeq (σ : ℕ → Equiv.Perm (Fin 3)) (x : ℕ → Step 3) : ℕ → Step 3 :=
  fun n => relab (σ (dW x n).toNat) (x n)

/-- The tree map of `σ`: the letter at depth `k + 1` permuted by `σ k`. -/
def relabV (σ : ℕ → Equiv.Perm (Fin 3)) : Vertex 3 → Vertex 3
  | [] => []
  | c :: u => σ u.length c :: relabV σ u

theorem inc_relab (τ : Equiv.Perm (Fin 3)) (ξ : Step 3) : inc (relab τ ξ) = inc ξ := by
  by_cases h : ξ.2 = 0
  · simp [relab, h]
  · simp [relab, h, inc, Fin.succ_ne_zero]

theorem relab_inv (τ : Equiv.Perm (Fin 3)) (ξ : Step 3) : relab τ⁻¹ (relab τ ξ) = ξ := by
  by_cases h : ξ.2 = 0
  · simp [relab, h]
  · have h' : (τ (ξ.2.pred h)).succ ≠ 0 := Fin.succ_ne_zero _
    simp only [relab, h, dite_false, h', Fin.pred_succ, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    ext <;> simp

theorem dW_relabSeq (σ : ℕ → Equiv.Perm (Fin 3)) (x : ℕ → Step 3) (n : ℕ) :
    dW (relabSeq σ x) n = dW x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dW, ih]
    show dW x n + inc (relab _ (x n)) = dW x n + inc (x n)
    rw [inc_relab]

theorem relabSeq_inv (σ : ℕ → Equiv.Perm (Fin 3)) (x : ℕ → Step 3) :
    relabSeq (fun k => (σ k)⁻¹) (relabSeq σ x) = x := by
  funext n
  simp only [relabSeq, dW_relabSeq]
  exact relab_inv _ _

theorem length_relabV (σ : ℕ → Equiv.Perm (Fin 3)) (u : Vertex 3) :
    (relabV σ u).length = u.length := by
  induction u with
  | nil => rfl
  | cons c u ih => simp [relabV, ih]

theorem relabV_injective (σ : ℕ → Equiv.Perm (Fin 3)) : Function.Injective (relabV σ) := by
  intro u
  induction u with
  | nil =>
    intro u' h
    cases u' with
    | nil => rfl
    | cons c' u' => simp [relabV] at h
  | cons c u ih =>
    intro u' h
    cases u' with
    | nil => simp [relabV] at h
    | cons c' u' =>
      simp only [relabV, List.cons.injEq] at h
      have hu : u = u' := ih h.2
      subst hu
      simp only [EmbeddingLike.apply_eq_iff_eq] at h
      rw [h.1]

/-- The relabeled steps drive the image walk. -/
theorem walkStar_relabSeq (σ : ℕ → Equiv.Perm (Fin 3)) (x : ℕ → Step 3) (n : ℕ) :
    walkStar (some []) (relabSeq σ x) n = (walkStar (some []) x n).map (relabV σ) := by
  induction n with
  | zero =>
      simp [walkStar, relabV]
  | succ n ih =>
      simp [walkStar, ih]
      cases h : walkStar (some []) x n with
      | none =>
          simp [stepStar]
      | some v =>
          have hlen := (walkStar_dW [] x n).2 v h
          simp at hlen
          -- hlen : (v.length : ℤ) = dW x n
          have htoNat : (dW x n).toNat = v.length := by
            rw [← hlen]
            simp
          have hrelabSeq : relabSeq σ x n = relab (σ v.length) (x n) := by
            dsimp [relabSeq]
            rw [htoNat]
          rw [hrelabSeq]
          by_cases hξ2 : (x n).2 = 0
          · -- Case (x n).2 = 0: relab (σ v.length) (x n) = x n
            have hrelab : relab (σ v.length) (x n) = x n := by
              dsimp [relab]
              simp [hξ2]
            rw [hrelab]
            -- Goal: stepStar (some (relabV σ v)) (x n) = (stepStar (some v) (x n)).map (relabV σ)
            cases v with
            | nil =>
                simp [relabV, stepStar, hξ2]
            | cons c w =>
                simp [relabV, stepStar, hξ2]
          · -- Case (x n).2 ≠ 0
            have hrelab : relab (σ v.length) (x n) = ((x n).1, (σ v.length ((x n).2.pred hξ2)).succ) := by
              dsimp [relab]
              simp [hξ2]
            rw [hrelab]
            have hsucc_ne_zero : (σ v.length ((x n).2.pred hξ2)).succ ≠ 0 :=
              Fin.succ_ne_zero _
            simp [stepStar, hξ2, hsucc_ne_zero, Fin.pred_succ, relabV]

theorem measurable_relabSeq (σ : ℕ → Equiv.Perm (Fin 3)) : Measurable (relabSeq σ) := by
  refine measurable_pi_iff.2 fun n => ?_
  refine measurable_to_countable' fun ξ => ?_
  refine measurableSet_of_prefix (n + 1) fun x x' h hx => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, relabSeq] at hx ⊢
  rw [← dW_congr x x' n fun i hi => h i (by omega), ← h n (by omega)]
  exact hx

/-- The relabelings preserve the i.i.d. law of the steps. -/
theorem map_relabSeq (σ : ℕ → Equiv.Perm (Fin 3)) :
    (LemmaR.seqLaw 3).map (relabSeq σ) = LemmaR.seqLaw 3 := by
  -- Both sides are probability measures on ℕ → Step 3, so by ext_of_prefix
  -- it suffices to compare prefix cylinders.
  apply FrogModel.ext_of_prefix
  intro N a
  -- Apply map_apply to rewrite the left side
  rw [MeasureTheory.Measure.map_apply (measurable_relabSeq σ) (measurableSet_prefix N a)]
  -- Set σ' = inverse of σ, b = relabSeq σ' a
  set σ' := fun k : ℕ => (σ k)⁻¹ with hσ'
  set b := relabSeq σ' a with hb
  -- Key: preimage of prefix cylinder under relabSeq is another prefix cylinder
  have h_set_eq : (relabSeq σ)⁻¹' {x | ∀ i < N, x i = a i} = {x | ∀ i < N, x i = b i} := by
    ext x
    constructor
    · intro hx i hi
      -- hx : x ∈ (relabSeq σ)⁻¹' {x | ∀ i < N, x i = a i}
      -- i.e., ∀ i < N, (relabSeq σ x) i = a i
      have h_relab_eq : ∀ j < N, (relabSeq σ x) j = a j := hx
      have h_dW_eq : ∀ j < N, dW (relabSeq σ x) j = dW a j := by
        intro j hj
        exact dW_congr (relabSeq σ x) a j (fun k hk => h_relab_eq k (lt_trans hk hj))
      have hx_id : x = relabSeq σ' (relabSeq σ x) := by
        symm; exact relabSeq_inv σ x
      rw [hx_id]
      dsimp [b]
      calc
        (relabSeq σ' (relabSeq σ x)) i = relab (σ' (dW (relabSeq σ x) i).toNat) ((relabSeq σ x) i) := rfl
        _ = relab (σ' (dW a i).toNat) (a i) := by rw [h_relab_eq i hi, h_dW_eq i hi]
        _ = (relabSeq σ' a) i := rfl
    · intro hx i hi
      -- hx : ∀ i < N, x i = b i
      have hx_eq : ∀ j < N, x j = b j := hx
      have h_dW_eq : ∀ j < N, dW x j = dW b j := by
        intro j hj
        exact dW_congr x b j (fun k hk => hx_eq k (lt_trans hk hj))
      have h_relab_eq : (relabSeq σ x) i = a i := by
        calc
          (relabSeq σ x) i = relab (σ (dW x i).toNat) (x i) := rfl
          _ = relab (σ (dW b i).toNat) (b i) := by rw [hx_eq i hi, h_dW_eq i hi]
          _ = (relabSeq σ b) i := rfl
          _ = (relabSeq σ (relabSeq σ' a)) i := rfl
          _ = a i := by
            have h := congr_fun (relabSeq_inv σ' a) i
            simpa [σ'] using h
      exact h_relab_eq
  rw [h_set_eq]
  -- Now both sides are infinitePi_prefix of prefix cylinders
  rw [FrogModel.infinitePi_prefix (stepLaw 3) N b, FrogModel.infinitePi_prefix (stepLaw 3) N a]
  -- Both products are ∏ over range N of stepLaw 3 {·} = (12⁻¹)^N
  simp [FrogModel.LemmaR.stepLaw_singleton]

/-- The relabelings act transitively on each depth. -/
theorem exists_relabV_replicate (v : Vertex 3) :
    ∃ σ : ℕ → Equiv.Perm (Fin 3), relabV σ (List.replicate v.length 0) = v := by
  -- Stronger statement: for every σ with σ k 0 = (v.reverse.getD k 0) for all k < v.length,
  -- we have relabV σ (List.replicate v.length 0) = v.
  have h_strong : ∀ (v : Vertex 3) (σ : ℕ → Equiv.Perm (Fin 3)),
      (∀ k, k < v.length → σ k 0 = (v.reverse.getD k 0)) →
      relabV σ (List.replicate v.length 0) = v := by
    intro v
    induction' v with c u ih
    · intro σ hσ
      simp [relabV]
    · intro σ hσ
      -- hσ : ∀ k, k < (c :: u).length → σ k 0 = ((c :: u).reverse.getD k 0)
      have hlen : (c :: u).length = u.length + 1 := by simp
      have hσ0 : σ u.length 0 = c := by
        have hbound : u.length < (c :: u).length := by
          rw [hlen]
          exact Nat.lt_succ_self u.length
        have h_eq := hσ u.length hbound
        -- h_eq : σ u.length 0 = ((c :: u).reverse.getD u.length 0)
        rw [h_eq]
        -- Need: ((c :: u).reverse.getD u.length 0) = c
        have hrev_len : u.reverse.length = u.length := by simp
        simp [List.reverse_cons, hrev_len]
      have hσ_tail : ∀ k, k < u.length → σ k 0 = (u.reverse.getD k 0) := by
        intro k hk
        have hbound : k < (c :: u).length := by
          rw [hlen]
          exact Nat.lt_of_lt_of_le hk (Nat.le_succ u.length)
        have h_eq := hσ k hbound
        rw [h_eq]
        -- Need: ((c :: u).reverse.getD k 0) = u.reverse.getD k 0
        have hrev_len : u.reverse.length = u.length := by simp
        have hk_lt : k < u.reverse.length := by
          rw [hrev_len]
          exact hk
        simpa [List.reverse_cons] using List.getD_append (u.reverse) [c] 0 k hk_lt
      -- Apply induction hypothesis to u with σ
      have h_u := ih σ hσ_tail
      -- Now compute relabV σ (replicate (c :: u).length 0)
      rw [hlen, List.replicate_succ, relabV]
      -- relabV σ (0 :: List.replicate u.length 0) = σ (List.replicate u.length 0).length 0 :: relabV σ (List.replicate u.length 0)
      -- Simplify (List.replicate u.length 0).length = u.length
      simp [h_u, hσ0]
  -- Now construct the required σ for the original statement
  set σ : ℕ → Equiv.Perm (Fin 3) := fun k => Equiv.swap 0 (v.reverse.getD k 0) with hσ_def
  refine ⟨σ, ?_⟩
  apply h_strong v σ
  intro k hk
  dsimp [σ]
  -- Need: Equiv.swap 0 (v.reverse.getD k 0) 0 = v.reverse.getD k 0
  simp

theorem firstD_relabSeq (σ : ℕ → Equiv.Perm (Fin 3)) (D : ℕ) (x : ℕ → Step 3) :
    firstD D (relabSeq σ x) = (firstD D x).map (relabV σ) := by
  classical
  have hat : ∀ n, (∃ v, walkStar (some []) (relabSeq σ x) n = some v ∧ v.length = D) ↔
      (∃ v, walkStar (some []) x n = some v ∧ v.length = D) := by
    intro n
    rw [walkStar_relabSeq]
    constructor
    · rintro ⟨v, hv, hvD⟩
      cases hw : walkStar (some []) x n with
      | none => rw [hw] at hv; cases hv
      | some w =>
        rw [hw] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        exact ⟨w, rfl, by rw [← hv, length_relabV] at hvD; exact hvD⟩
    · rintro ⟨v, hv, hvD⟩
      exact ⟨relabV σ v, by rw [hv]; rfl, by rw [length_relabV]; exact hvD⟩
  have hreach : ReachD D (relabSeq σ x) ↔ ReachD D x := exists_congr hat
  by_cases hr : ReachD D x
  · have hr' : ReachD D (relabSeq σ x) := hreach.2 hr
    have hfind : Nat.find hr' = Nat.find hr := by
      rw [Nat.find_eq_iff]
      exact ⟨(hat _).2 (Nat.find_spec hr), fun n hn => by
        rw [hat]; exact Nat.find_min hr hn⟩
    unfold firstD
    rw [dite_eq_left hr', dite_eq_left hr, hfind, walkStar_relabSeq]
  · have hr' : ¬ ReachD D (relabSeq σ x) := fun h => hr (hreach.1 h)
    simp [firstD, hr, hr']

/-- The events "the first vertex at depth `D` is `v`", `|v| = D`, all have the same
probability. -/
theorem seqLaw_firstD_eq (D : ℕ) (v : Vertex 3) (hv : v.length = D) :
    LemmaR.seqLaw 3 {x | firstD D x = some v} =
      LemmaR.seqLaw 3 {x | firstD D x = some (List.replicate D 0)} := by
  obtain ⟨σ, hσ⟩ := exists_relabV_replicate v
  rw [hv] at hσ
  have hpre : {x : ℕ → Step 3 | firstD D x = some (List.replicate D 0)} =
      relabSeq σ ⁻¹' {x | firstD D x = some v} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, firstD_relabSeq, ← hσ]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      cases hx : firstD D x with
      | none => rw [hx] at h; cases h
      | some w =>
        rw [hx] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [relabV_injective σ h]
  have hms : MeasurableSet {x : ℕ → Step 3 | firstD D x = some v} :=
    measurable_firstD D (measurableSet_singleton (some v))
  rw [hpre, ← Measure.map_apply (measurable_relabSeq σ) hms, map_relabSeq]

/-- **The first vertex at depth `D` is `v` with probability at most `3^-D`.** -/
theorem seqLaw_firstD_le (D : ℕ) (v : Vertex 3) :
    LemmaR.seqLaw 3 {x | firstD D x = some v} ≤ (3⁻¹ : ℝ≥0∞) ^ D := by
  classical
  by_cases hv : v.length = D
  · set c := LemmaR.seqLaw 3 {x | firstD D x = some (List.replicate D 0)} with hc
    set W : Finset (Vertex 3) := (Finset.univ : Finset (Fin D → Fin 3)).image List.ofFn with hW
    have hWcard : W.card = 3 ^ D := by
      rw [hW, Finset.card_image_of_injective _ List.ofFn_injective]
      simp
    have hWmem : ∀ w ∈ W, w.length = D := by
      intro w hw
      simp only [hW, Finset.mem_image, Finset.mem_univ, true_and] at hw
      obtain ⟨f, rfl⟩ := hw
      simp
    have hsum : ∑ w ∈ W, LemmaR.seqLaw 3 {x | firstD D x = some w} ≤ 1 := by
      rw [← measure_biUnion_finset]
      · exact prob_le_one
      · intro w _ w' _ hww'
        refine Set.disjoint_left.2 fun x hx hx' => hww' ?_
        simp only [Set.mem_ofPred_eq] at hx hx'
        rw [hx] at hx'
        exact Option.some.inj hx'
      · exact fun w _ => measurable_firstD D (measurableSet_singleton _)
    have hall : ∑ w ∈ W, LemmaR.seqLaw 3 {x | firstD D x = some w} = (3 ^ D : ℕ) * c := by
      rw [Finset.sum_congr rfl fun w hw => seqLaw_firstD_eq D w (hWmem w hw), Finset.sum_const,
        hWcard, nsmul_eq_mul]
    rw [seqLaw_firstD_eq D v hv, ← hc]
    rw [hall] at hsum
    have h3 : ((3 ^ D : ℕ) : ℝ≥0∞) ≠ 0 := by simp
    have h3' : ((3 ^ D : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
    calc c = ((3 ^ D : ℕ) : ℝ≥0∞)⁻¹ * (((3 ^ D : ℕ) : ℝ≥0∞) * c) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h3 h3', one_mul]
      _ ≤ ((3 ^ D : ℕ) : ℝ≥0∞)⁻¹ * 1 := by gcongr
      _ = (3⁻¹ : ℝ≥0∞) ^ D := by simp [ENNReal.inv_pow]
  · have : {x : ℕ → Step 3 | firstD D x = some v} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨n, -, -, hD⟩ := firstD_spec D x v h
      exact hv hD
    rw [this, measure_empty]
    exact bot_le

end FrogModel.D3.LaneA
