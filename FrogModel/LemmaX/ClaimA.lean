module

public import FrogModel.LemmaX.LawStatement
public import FrogModel.LemmaX.Coupling
public import FrogModel.Lemmas.Refresh

@[expose] public section

/-!
# Claim A (Proposition 5.1 of the paper)

Parts (a), (b) and (c) are parts (1), (2) and (3) of Lemma 5.2 of the paper.

(a) Pathwise domination (`claimAPathwise_holds`): the curve of the original configuration is at
most the block renewal curve of the root-refreshed blocks. A vertex reached by the first `qJ + s`
initial frogs of the original configuration is reached in some block `b ≤ q`, and in no full
block before, so its step sequence in block `b` is the original one (`reachedK_orig`); the frozen
initial frogs are counted block by block (`encard_lt_mul_add`).

(c) The original configuration has the law of the sample of `N_K` (`claimAOrig_holds`): its
coordinates are distinct coordinates of an i.i.d. family (`infinitePi_map_pair_comp`).

(b) The block outputs are i.i.d. with law `E_K` (`claimAIid_holds`): one refresh makes the next
configuration a fresh block configuration independent of the output (`map_blockOut_refresh`,
from `FrogModel.Stage.map_refresh`), and an induction on the number of blocks.

Then Claim A (`claimA_holds`): the pair of the two curves on the probability space of the blocks
is a coupling.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.LemmaX

/-! ## Reachability -/

/-- More initial frogs reach more vertices. -/
theorem reachedK_mono {d : ℕ} (K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d)
    {n n' : ℕ} (hn : n ≤ n') (v : Vertex d) (h : reachedK K ζ ξ n v) : reachedK K ζ ξ n' v := by
  obtain ⟨a, ha, rest⟩ := h
  exact ⟨a, lt_of_lt_of_le ha hn, rest⟩

/-- The reached set is closed under the arcs. -/
theorem reachedK_tail {d : ℕ} (K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d)
    (n : ℕ) (v w : Vertex d) (h : reachedK K ζ ξ n v) (hvw : starArcK K ζ v w) :
    reachedK K ζ ξ n w := by
  obtain ⟨a, ha, u, hu, hau, huv⟩ := h
  exact ⟨a, ha, u, hu, hau, huv.tail hvw⟩

/-- A vertex other than `r` visited by an initial frog `a < n` before the kill is reached. -/
theorem reachedK_of_visit {d : ℕ} (K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d)
    (n a : ℕ) (ha : a < n) (w : Vertex d) (hw : w ≠ []) (hv : visitsK K (some []) (ξ a) (some w)) :
    reachedK K ζ ξ n w :=
  ⟨a, ha, w, hw, hv, Relation.ReflTransGen.refl⟩

/-- The arcs from `v` read only the step sequence at `v`. -/
theorem starArcK_congr {d : ℕ} (K : ℕ) (ζ ζ' : Sample d) (v w : Vertex d)
    (h : ζ v = ζ' v) (hvw : starArcK K ζ v w) : starArcK K ζ' v w := by
  refine ⟨hvw.1, ?_⟩
  rw [← h]
  exact hvw.2

/-! ## The root-refreshed configurations -/

/-- A vertex label is woken in a block when the `J` initial frogs reach it. -/
theorem mem_blockWoken_inl {d : ℕ} (K J : ℕ) (ω : BlockSample d J) (v : Vertex d) :
    (Sum.inl v : Vertex d ⊕ Fin J) ∈ blockWoken K ω ↔
      reachedK K (blockSleep ω) (blockActive ω) J v := by
  simp [blockWoken]

/-- Every initial label is woken. -/
theorem mem_blockWoken_inr {d : ℕ} (K J : ℕ) (ω : BlockSample d J) (t : Fin J) :
    (Sum.inr t : Vertex d ⊕ Fin J) ∈ blockWoken K ω :=
  Or.inl ⟨t, rfl⟩

/-- The initial labels of every root-refreshed configuration are those of its own block. -/
theorem refreshSeq_inr {d : ℕ} (K J : ℕ) (ω : ℕ → BlockSample d J) (b : ℕ)
    (t : Fin J) : refreshSeq K J ω b (.inr t) = ω b (.inr t) := by
  cases b with
  | zero => rfl
  | succ b =>
    simp only [refreshSeq, FrogModel.Stage.refresh, mem_blockWoken_inr K J _ t, ↓reduceIte]

/-- A vertex label not reached in any earlier full block keeps its original step sequence. -/
theorem refreshSeq_inl {d : ℕ} (K J : ℕ) (ω : ℕ → BlockSample d J) (b : ℕ)
    (v : Vertex d) (h : ∀ b' < b, ¬ reachedK K (blockSleep (refreshSeq K J ω b'))
      (blockActive (refreshSeq K J ω b')) J v) :
    refreshSeq K J ω b (.inl v) = ω 0 (.inl v) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hb : (Sum.inl v : Vertex d ⊕ Fin J) ∉ blockWoken K (refreshSeq K J ω b) := by
      rw [mem_blockWoken_inl]
      exact h b (Nat.lt_succ_self b)
    simp only [refreshSeq, FrogModel.Stage.refresh, hb, ↓reduceIte]
    exact ih fun b' hb' => h b' (Nat.lt_succ_of_lt hb')

/-- The initial frog `a < J` of block `b` runs the step sequence of label `a` of `ω b`. -/
theorem blockActive_refreshSeq {d : ℕ} (K J : ℕ) (ω : ℕ → BlockSample d J)
    (b a : ℕ) (ha : a < J) : blockActive (refreshSeq K J ω b) a = ω b (.inr ⟨a, ha⟩) := by
  simp only [blockActive, ha, ↓reduceDIte]
  exact refreshSeq_inr K J ω b ⟨a, ha⟩

/-- The initial frog `i` of the original configuration is the initial frog `i % J` of block
`i / J`. -/
theorem origActive_eq {d : ℕ} (K J : ℕ) (hJ : 0 < J) (ω : ℕ → BlockSample d J)
    (i : ℕ) : origActive J hJ ω i = blockActive (refreshSeq K J ω (i / J)) (i % J) := by
  rw [blockActive_refreshSeq K J ω _ _ (Nat.mod_lt i hJ)]
  rfl

/-- The initial frog `bJ + t`, `t < J`, of the original configuration is the initial frog `t` of
block `b`. -/
theorem origActive_mul_add {d : ℕ} (K J : ℕ) (hJ : 0 < J) (ω : ℕ → BlockSample d J)
    (b t : ℕ) (ht : t < J) :
    origActive J hJ ω (b * J + t) = blockActive (refreshSeq K J ω b) t := by
  have h1 : (b * J + t) / J = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt ht, zero_add]
  have h2 : (b * J + t) % J = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  rw [origActive_eq K J hJ, h1, h2]

/-- **Claim A (a), the reached vertices** (proof of Lemma 5.2 (1) of the paper): a vertex
reached in the original configuration by the first `qJ + s` initial frogs is reached in some
block `b ≤ q` (by `J` initial frogs for `b < q`, by `s` for `b = q`), and in no full block
before. -/
theorem reachedK_orig {d : ℕ} (K J : ℕ) (hJ : 0 < J) (ω : ℕ → BlockSample d J)
    (q s : ℕ) (hs : s < J) (v : Vertex d)
    (h : reachedK K (blockSleep (ω 0)) (origActive J hJ ω) (q * J + s) v) :
    ∃ b ≤ q, reachedK K (blockSleep (refreshSeq K J ω b)) (blockActive (refreshSeq K J ω b))
        (if b < q then J else s) v ∧
      ∀ b' < b, ¬ reachedK K (blockSleep (refreshSeq K J ω b'))
        (blockActive (refreshSeq K J ω b')) J v := by
  classical
  have key : ∀ w : Vertex d, (∃ b, b ≤ q ∧ reachedK K (blockSleep (refreshSeq K J ω b))
      (blockActive (refreshSeq K J ω b)) (if b < q then J else s) w) →
      ∃ b ≤ q, reachedK K (blockSleep (refreshSeq K J ω b)) (blockActive (refreshSeq K J ω b))
        (if b < q then J else s) w ∧
      ∀ b' < b, ¬ reachedK K (blockSleep (refreshSeq K J ω b'))
        (blockActive (refreshSeq K J ω b')) J w := by
    intro w hex
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun b' hb' hr => ?_⟩
    have hb'q : b' < q := lt_of_lt_of_le hb' (Nat.find_spec hex).1
    exact Nat.find_min hex hb' ⟨hb'q.le, by simp only [hb'q, ↓reduceIte]; exact hr⟩
  obtain ⟨a, ha, u, hu, hau, huv⟩ := h
  apply key
  induction huv with
  | refl =>
    have hdm : a / J * J + a % J = a := Nat.div_add_mod' a J
    have hlt : a / J < q + 1 := by
      rw [Nat.div_lt_iff_lt_mul hJ, Nat.add_mul, one_mul]
      omega
    refine ⟨a / J, Nat.lt_succ_iff.1 hlt, ?_⟩
    have hn : a % J < if a / J < q then J else s := by
      split_ifs with hq
      · exact Nat.mod_lt a hJ
      · have hq' : a / J = q := by omega
        rw [hq'] at hdm
        omega
    refine reachedK_of_visit K _ _ _ (a % J) hn u hu ?_
    rw [← origActive_eq K J hJ]
    exact hau
  | @tail c e _ hce ih =>
    obtain ⟨b, hbq, hRb, hmin⟩ := key c ih
    refine ⟨b, hbq, reachedK_tail K _ _ _ c e hRb (starArcK_congr K _ _ c e ?_ hce)⟩
    exact (refreshSeq_inl K J ω b c hmin).symm

/-! ## Counting -/

open Classical in
/-- The `encard` of the indices below `n` with a property, as a sum. -/
theorem encard_lt_and (P : ℕ → Prop) (n : ℕ) :
    {a : ℕ | a < n ∧ P a}.encard = ((∑ a ∈ Finset.range n, if P a then 1 else 0 : ℕ) : ℕ∞) := by
  rw [← Finset.card_filter, ← Set.encard_coe_eq_coe_finsetCard]
  congr 1
  ext a
  simp

/-- Counting the indices `a < qJ + s` block by block. -/
theorem encard_lt_mul_add (P : ℕ → Prop) (J q s : ℕ) :
    {a : ℕ | a < q * J + s ∧ P a}.encard =
      ∑ b ∈ Finset.range q, {t : ℕ | t < J ∧ P (b * J + t)}.encard +
        {t : ℕ | t < s ∧ P (q * J + t)}.encard := by
  classical
  simp only [encard_lt_and]
  rw [Finset.sum_range_add, Nat.cast_add]
  congr 1
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Nat.cast_add, ih, Finset.sum_range_succ]

/-- The `encard` of a finite union is at most the sum of the `encard`s. -/
theorem encard_biUnion_le {α : Type*} (T : ℕ → Set α) (n : ℕ) :
    (⋃ b ∈ Finset.range n, T b).encard ≤ ∑ b ∈ Finset.range n, (T b).encard := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert,
      Finset.sum_insert Finset.notMem_range_self]
    exact (Set.encard_union_le _ _).trans (by gcongr)

/-- The block output as a curve is the curve of the block configuration up to `J`. -/
theorem blockCurve_blockOut {d : ℕ} (K J : ℕ) (ω : BlockSample d J) (s : ℕ)
    (hs : s ≤ J) : blockCurve (blockOut K ω) s = curveK K (blockSleep ω) (blockActive ω) s := by
  unfold blockCurve
  split_ifs with h
  · simp only [blockOut]
    congr 1
    exact Nat.sub_add_cancel h.1
  · have : s = 0 := by omega
    subst this
    rw [curveK_zero]

/-- **Claim A (a), counting** (proof of Lemma 5.2 (1) of the paper): the curve of the original
configuration at `qJ + s` is at most the sum of the curves of the full blocks before `q` and the
curve of block `q` at `s`. -/
theorem curveK_orig_le {d : ℕ} (K J : ℕ) (hJ : 0 < J) (ω : ℕ → BlockSample d J) (q s : ℕ)
    (hs : s < J) :
    curveK K (blockSleep (ω 0)) (origActive J hJ ω) (q * J + s) ≤
      ∑ b ∈ Finset.range q, curveK K (blockSleep (refreshSeq K J ω b))
          (blockActive (refreshSeq K J ω b)) J +
        curveK K (blockSleep (refreshSeq K J ω q)) (blockActive (refreshSeq K J ω q)) s := by
  classical
  let S : ℕ → Sample d := fun b => blockSleep (refreshSeq K J ω b)
  let A : ℕ → ℕ → ℕ → Step d := fun b => blockActive (refreshSeq K J ω b)
  let F : ℕ → ℕ → ℕ∞ := fun b n => {a : ℕ | a < n ∧ visitsK K (some []) (A b a) none}.encard
  let R : ℕ → ℕ → ℕ∞ := fun b n =>
    {v : Vertex d | reachedK K (S b) (A b) n v ∧ visitsK K (some v) (S b v) none}.encard
  have hcurve : ∀ b n, curveK K (S b) (A b) n = F b n + R b n := fun b n => rfl
  change _ ≤ ∑ b ∈ Finset.range q, curveK K (S b) (A b) J + curveK K (S q) (A q) s
  simp only [hcurve, Finset.sum_add_distrib]
  unfold curveK
  have hF : {a : ℕ | a < q * J + s ∧ visitsK K (some []) (origActive J hJ ω a) none}.encard =
      ∑ b ∈ Finset.range q, F b J + F q s := by
    rw [encard_lt_mul_add]
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      ext t
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨ht, h⟩
        exact ⟨ht, by rw [origActive_mul_add K J hJ ω b t ht] at h; exact h⟩
      · rintro ⟨ht, h⟩
        exact ⟨ht, by rw [origActive_mul_add K J hJ ω b t ht]; exact h⟩
    · congr 1
      ext t
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨ht, h⟩
        exact ⟨ht, by rw [origActive_mul_add K J hJ ω q t (ht.trans hs)] at h; exact h⟩
      · rintro ⟨ht, h⟩
        exact ⟨ht, by rw [origActive_mul_add K J hJ ω q t (ht.trans hs)]; exact h⟩
  let T : ℕ → Set (Vertex d) := fun b =>
    {v | reachedK K (S b) (A b) (if b < q then J else s) v ∧ visitsK K (some v) (S b v) none}
  have hR : {v : Vertex d | reachedK K (blockSleep (ω 0)) (origActive J hJ ω) (q * J + s) v ∧
      visitsK K (some v) (blockSleep (ω 0) v) none}.encard ≤
        ∑ b ∈ Finset.range q, R b J + R q s := by
    calc _ ≤ (⋃ b ∈ Finset.range (q + 1), T b).encard := by
          refine Set.encard_le_encard fun v hv => ?_
          obtain ⟨b, hbq, hRb, hmin⟩ := reachedK_orig K J hJ ω q s hs v hv.1
          have hS : S b v = blockSleep (ω 0) v := refreshSeq_inl K J ω b v hmin
          refine Set.mem_iUnion₂.2 ⟨b, Finset.mem_range.2 (Nat.lt_succ_of_le hbq), hRb, ?_⟩
          rw [hS]
          exact hv.2
      _ ≤ ∑ b ∈ Finset.range (q + 1), (T b).encard := encard_biUnion_le T (q + 1)
      _ = ∑ b ∈ Finset.range q, R b J + R q s := by
          rw [Finset.sum_range_succ]
          congr 1
          · refine Finset.sum_congr rfl fun b hb => ?_
            simp only [T, R, Finset.mem_range.1 hb, ↓reduceIte]
          · simp only [T, R, lt_irrefl, ↓reduceIte]
  calc _ ≤ (∑ b ∈ Finset.range q, F b J + F q s) + (∑ b ∈ Finset.range q, R b J + R q s) :=
        add_le_add hF.le hR
    _ = _ := by
        simp only [F, R, S, A]
        abel

/-- **Claim A (a)**: pathwise, the curve of the original configuration is at most the block
renewal curve of the root-refreshed block outputs. -/
theorem claimAPathwise_holds : ClaimAPathwise := by
  intro d K J hJ ω m
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < J ∧ m = q * J + s :=
    ⟨m / J, m % J, Nat.mod_lt m hJ, (Nat.div_add_mod' m J).symm⟩
  have h1 : (q * J + s) / J = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt hs, zero_add]
  have h2 : (q * J + s) % J = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  unfold FrogModel.Order.brCurve
  simp only [h1, h2, blockCurve_blockOut K J _ s hs.le, blockCurve_blockOut K J _ J le_rfl]
  exact curveK_orig_le K J hJ ω q s hs

end FrogModel.LemmaX
