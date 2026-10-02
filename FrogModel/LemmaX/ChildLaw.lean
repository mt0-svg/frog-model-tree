module

public import FrogModel.LemmaX.ChildBasic
public import FrogModel.LemmaX.ClaimALaw
public import FrogModel.LemmaX.Kill
public import FrogModel.Engine.FK
public import FrogModel.Engine.Drive

@[expose] public section

/-!
# The child chain: the law of its delivery curve (Lemma 6.1 of the paper)

From `fresh`, the child chain of a table satisfying (I0) and (I1) runs through blocks: every
move from a well-formed state of level `q` (`CState.level`, `fresh` at level `1`, `bdry` at level
`0`) goes to level `q + 1`, a level `J` read as `bdry` (`chainState_reach`). So the chain is at
`bdry` after `J - 1` entries from `fresh` and every `J` entries after that, and its delivery curve
is `BR` of its blocks with the values at `0` and `1` set to `0` (`chainCurve_eq_brOf`, pathwise).

The blocks are functions of disjoint sets of the i.i.d. uniforms: the first block of the first
`J - 1`, block `b ≥ 1` of the next `J` (`map_pair_shift`, `map_blocks_iid`). By the law of one
move (`lintegral_childStep`) and the shape of the rows, the block from `bdry` has law `H*`
(`map_nextBlk_bdry`) and the first block from `fresh` the law of `H*` with `B(1)` set to `0`
(`map_firstBlk_fresh`); `B(1)` is read only at index `1`, set to `0` by `trimCurve`
(`trimCurve_brOf_zeroFirst`). This gives `ChildLaw` (`childLaw_holds`). `Psi` reads a child
curve `G` through `sup_(i ≤ m + 1) G(i)` at `m ≥ 1`, unchanged by `trimCurve` when
`G(0), G(1) ≤ G(2)`, which holds almost surely under `BR(H*)` (`psiLaw_map_trimCurve`); this gives
`ChildPsiLaw` (`childPsiLaw_holds`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.Cert

/-- The level of a child state: `bdry` at `0`, `fresh` at `1` (its first move uses the first two
transitions of a block and goes to level `2`), the others at their level `q`. -/
def CState.level : CState → ℕ
  | .fresh => 1
  | .bdry => 0
  | .lab q _ => q
  | .tail q => q
  | .maxLab q => q

/-- The returns of the first `m` transitions of a path. -/
def cumSeq (π : List Tr) (m : ℕ) : ℕ := ((π.take m).map Tr.δ).sum

end FrogModel.Cert

namespace FrogModel.LemmaX

open FrogModel.Engine FrogModel.Cert

section Generic

variable {S U : Type*}

/-- `B` with its first coordinate set to `0`. -/
def zeroFirst {J : ℕ} (B : Fin J → ℕ∞) : Fin J → ℕ∞ := fun i => if (i : ℕ) = 0 then 0 else B i

/-- The curve `BR` of a block sequence (the map of `brLaw`). -/
def brOf (J : ℕ) (B : ℕ → Fin J → ℕ∞) : ℕ → ℕ∞ :=
  FrogModel.Order.brCurve J fun b => blockCurve (B b)

/-- The first block of a chain from `s₀`, its first coordinate set to `0`: coordinate `i ≥ 1`
holds the returns of the first `i` entries. -/
def firstBlk (f : S → U → ℕ × S) (s₀ : S) (J : ℕ) (v : ℕ → U) : Fin J → ℕ∞ :=
  fun i => if (i : ℕ) = 0 then 0 else ((chainDeliv f s₀ v i : ℕ) : ℕ∞)

/-- A block of a chain from `s`: coordinate `i` holds the returns of the first `i + 1` entries. -/
def nextBlk (f : S → U → ℕ × S) (s : S) (J : ℕ) (v : ℕ → U) : Fin J → ℕ∞ :=
  fun i => ((chainDeliv f s v ((i : ℕ) + 1) : ℕ) : ℕ∞)

/-- The blocks of a chain from `s`, block `b` read on the inputs `J b, ..., J b + J - 1`. -/
def blockSeq (f : S → U → ℕ × S) (s : S) (J : ℕ) (v : ℕ → U) : ℕ → Fin J → ℕ∞ :=
  fun b => nextBlk f s J fun k => v (J * b + k)

/-! ### The chain alone, pathwise -/

/-- The state after `m + n` entries: `n` entries from the state after `m`, on the shifted inputs. -/
theorem chainState_add (f : S → U → ℕ × S) (s : S) (v : ℕ → U) (m n : ℕ) :
    chainState f s v (m + n) = chainState f (chainState f s v m) (fun k => v (m + k)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (f (chainState f s v (m + n)) (v (m + n))).2 = _
    rw [ih]
    rfl

/-- The returns of the first `m + n` entries. -/
theorem chainDeliv_add (f : S → U → ℕ × S) (s : S) (v : ℕ → U) (m n : ℕ) :
    chainDeliv f s v (m + n) =
      chainDeliv f s v m + chainDeliv f (chainState f s v m) (fun k => v (m + k)) n := by
  unfold chainDeliv
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chainState_add]

/-- The returns of the first `m` entries read only the first `m` inputs. -/
theorem chainDeliv_congr (f : S → U → ℕ × S) (s : S) (v v' : ℕ → U) (m : ℕ)
    (h : ∀ k < m, v k = v' k) : chainDeliv f s v m = chainDeliv f s v' m := by
  have hst : ∀ j ≤ m, chainState f s v j = chainState f s v' j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      show (f (chainState f s v j) (v j)).2 = (f (chainState f s v' j) (v' j)).2
      rw [ih (by omega), h j (by omega)]
  unfold chainDeliv
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.1 hj
  rw [hst j hj'.le, h j hj']

/-- A chain back at `s` every `J` entries delivers the sum of its blocks. -/
theorem chainDeliv_blocks (f : S → U → ℕ × S) (s : S) (J : ℕ)
    (hs : ∀ v, chainState f s v J = s) (v : ℕ → U) (q r : ℕ) :
    chainDeliv f s v (J * q + r) =
      (∑ b ∈ Finset.range q, chainDeliv f s (fun k => v (J * b + k)) J) +
        chainDeliv f s (fun k => v (J * q + k)) r := by
  induction q generalizing v with
  | zero => simp
  | succ q ih =>
    rw [show J * (q + 1) + r = J + (J * q + r) by ring, chainDeliv_add, hs, ih, Finset.sum_range_succ']
    have e1 : ∑ b ∈ Finset.range q, chainDeliv f s (fun k => v (J + (J * b + k))) J =
        ∑ b ∈ Finset.range q, chainDeliv f s (fun k => v (J * (b + 1) + k)) J := by
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      funext k
      congr 1
      ring
    have e2 : chainDeliv f s (fun k => v (J * 0 + k)) J = chainDeliv f s v J := by simp
    have e3 : chainDeliv f s (fun k => v (J + (J * q + k))) r =
        chainDeliv f s (fun k => v (J * (q + 1) + k)) r := by
      congr 1
      funext k
      congr 1
      ring
    rw [e1, e2, e3]
    ring

/-- **The delivery curve of a chain through blocks**: at `s` after `J - 1` entries from `s₀` and
every `J` entries after that, the curve is `BR` of the first block and of the blocks from `s`,
with its values at `0` and `1` set to `0`. -/
theorem chainCurve_eq_brOf (f : S → U → ℕ × S) (s₀ s : S) (J : ℕ) (hJ : 2 ≤ J)
    (h₀ : ∀ v, chainState f s₀ v (J - 1) = s) (hs : ∀ v, chainState f s v J = s) (v : ℕ → U) :
    chainCurve f s₀ v =
      trimCurve (brOf J (consSeq (firstBlk f s₀ J v) (blockSeq f s J fun k => v (J - 1 + k)))) := by
  funext i
  unfold chainCurve trimCurve
  split_ifs with hi
  · have h0 : i - 1 = 0 := by omega
    simp [h0, chainDeliv]
  · rw [not_le] at hi
    unfold brOf FrogModel.Order.brCurve
    rcases Nat.lt_or_ge i J with hiJ | hiJ
    · rw [Nat.div_eq_of_lt hiJ, Nat.mod_eq_of_lt hiJ]
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, consSeq, blockCurve, firstBlk]
      rw [dite_eq_left ⟨by omega, hiJ.le⟩]
      simp only [show i - 1 ≠ 0 by omega, ite_false]
    · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < J ∧ i = J * (q + 1) + r :=
        ⟨i / J - 1, i % J, Nat.mod_lt _ (by omega), by
          have h1 : 1 ≤ i / J := (Nat.one_le_div_iff (by omega)).2 hiJ
          have := Nat.div_add_mod i J
          rw [Nat.sub_add_cancel h1]; omega⟩
      have hdiv : (J * (q + 1) + r) / J = q + 1 := by
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]
      have hmod : (J * (q + 1) + r) % J = r := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      rw [hdiv, hmod, Finset.sum_range_succ']
      have hsplit : J * (q + 1) + r - 1 = (J - 1) + (J * q + r) := by
        rw [Nat.mul_succ]; omega
      rw [hsplit, chainDeliv_add, h₀, chainDeliv_blocks f s J hs]
      have hJ1 : J - 1 + 1 = J := by omega
      have hB0 : blockCurve (consSeq (firstBlk f s₀ J v)
          (blockSeq f s J fun k => v (J - 1 + k)) 0) J = (chainDeliv f s₀ v (J - 1) : ℕ∞) := by
        simp only [consSeq, blockCurve, firstBlk]
        rw [dite_eq_left ⟨by omega, le_rfl⟩]
        simp only [show J - 1 ≠ 0 by omega, ite_false]
      have hBb : ∀ b, blockCurve (consSeq (firstBlk f s₀ J v)
          (blockSeq f s J fun k => v (J - 1 + k)) (b + 1)) J =
          (chainDeliv f s (fun k => v (J - 1 + (J * b + k))) J : ℕ∞) := by
        intro b
        simp only [consSeq, blockCurve, blockSeq, nextBlk]
        rw [dite_eq_left ⟨by omega, le_rfl⟩]
        simp only [hJ1]
      have hBq : blockCurve (consSeq (firstBlk f s₀ J v)
          (blockSeq f s J fun k => v (J - 1 + k)) (q + 1)) r =
          (chainDeliv f s (fun k => v (J - 1 + (J * q + k))) r : ℕ∞) := by
        simp only [consSeq, blockCurve, blockSeq, nextBlk]
        by_cases hr0 : r = 0
        · subst hr0; simp [chainDeliv]
        · rw [dite_eq_left ⟨by omega, hr.le⟩]
          simp only [show r - 1 + 1 = r by omega]
      simp only [hB0, hBb, hBq]
      push_cast
      ring

/-- `B(1)` of the first block is read only at index `1`. -/
theorem trimCurve_brOf_zeroFirst (J : ℕ) (hJ : 2 ≤ J) (B₀ : Fin J → ℕ∞)
    (B : ℕ → Fin J → ℕ∞) :
    trimCurve (brOf J (consSeq (zeroFirst B₀) B)) = trimCurve (brOf J (consSeq B₀ B)) := by
  have hblk : ∀ b s, (b ≠ 0 ∨ s ≠ 1) →
      blockCurve (consSeq (zeroFirst B₀) B b) s = blockCurve (consSeq B₀ B b) s := by
    intro b s hbs
    cases b with
    | zero =>
      have hs : s ≠ 1 := hbs.resolve_left (by simp)
      simp only [consSeq, blockCurve, zeroFirst]
      split_ifs with h1 h2
      · exfalso
        have h3 : s - 1 = 0 := h2
        omega
      · rfl
      · rfl
    | succ b => rfl
  funext i
  unfold trimCurve
  split_ifs with hi
  · rfl
  · unfold brOf FrogModel.Order.brCurve
    congr 1
    · refine Finset.sum_congr rfl fun b _ => hblk b J (Or.inr (by omega))
    · refine hblk _ _ ?_
      by_cases h0 : i / J = 0
      · right
        have : i < J := by
          rcases Nat.lt_or_ge i J with h | h
          · exact h
          · exact absurd ((Nat.div_pos_iff).2 ⟨by omega, h⟩) (by omega)
        rw [Nat.mod_eq_of_lt this]
        omega
      · left; exact h0

/-! ### Measurability -/

theorem measurable_chainDeliv [MeasurableSpace U] [Countable S] (f : S → U → ℕ × S)
    (hf : ∀ s r, MeasurableSet {u | f s u = r}) (s : S) (m : ℕ) :
    Measurable fun v : ℕ → U => chainDeliv f s v m := by
  have hpair : ∀ j (x : S × ℕ),
      MeasurableSet {v : ℕ → U | (chainState f s v j, chainDeliv f s v j) = x} := by
    intro j
    induction j with
    | zero =>
      intro x
      by_cases hx : (s, 0) = x
      · simp [chainState, chainDeliv, hx]
      · simp [chainState, chainDeliv, hx]
    | succ j ih =>
      intro x
      have e : {v : ℕ → U | (chainState f s v (j + 1), chainDeliv f s v (j + 1)) = x} =
          ⋃ y : S × ℕ, ⋃ r : ℕ × S, ⋃ (_ : r.2 = x.1 ∧ y.2 + r.1 = x.2),
            {v : ℕ → U | (chainState f s v j, chainDeliv f s v j) = y} ∩
              {v : ℕ → U | f y.1 (v j) = r} := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
        have h1 : chainState f s v (j + 1) = (f (chainState f s v j) (v j)).2 := rfl
        have h2 : chainDeliv f s v (j + 1) =
            chainDeliv f s v j + (f (chainState f s v j) (v j)).1 := by
          unfold chainDeliv
          rw [Finset.sum_range_succ]
        rw [h1, h2]
        constructor
        · rintro rfl
          exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
        · rintro ⟨y, r, ⟨hr1, hr2⟩, hy, hr⟩
          rw [Prod.ext_iff] at hy
          obtain ⟨hy1, hy2⟩ := hy
          simp only at hy1 hy2
          rw [hy1, hr, hy2]
          exact Prod.ext hr1 hr2
      rw [e]
      exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun r =>
        MeasurableSet.iUnion fun _ => (ih y).inter
          ((show Measurable fun v : ℕ → U => v j from measurable_pi_apply j) (hf y.1 r))
  refine measurable_to_countable' fun n => ?_
  have e : (fun v : ℕ → U => chainDeliv f s v m) ⁻¹' {n} =
      ⋃ t : S, {v : ℕ → U | (chainState f s v m, chainDeliv f s v m) = (t, n)} := by
    ext v
    simp
  rw [e]
  exact MeasurableSet.iUnion fun t => hpair m (t, n)

theorem measurable_firstBlk [MeasurableSpace U] [Countable S] (f : S → U → ℕ × S)
    (hf : ∀ s r, MeasurableSet {u | f s u = r}) (s₀ : S) (J : ℕ) :
    Measurable (firstBlk f s₀ J) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : (i : ℕ) = 0
  · simp only [firstBlk, hi, ite_true]
    exact measurable_const
  · simp only [firstBlk, hi, ite_false]
    exact (measurable_of_countable fun n : ℕ => (n : ℕ∞)).comp (measurable_chainDeliv f hf s₀ i)

theorem measurable_nextBlk [MeasurableSpace U] [Countable S] (f : S → U → ℕ × S)
    (hf : ∀ s r, MeasurableSet {u | f s u = r}) (s : S) (J : ℕ) :
    Measurable (nextBlk f s J) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_of_countable fun n : ℕ => (n : ℕ∞)).comp (measurable_chainDeliv f hf s ((i : ℕ) + 1))

theorem measurable_trim_brOf_cons (J : ℕ) :
    Measurable fun p : (Fin J → ℕ∞) × (ℕ → Fin J → ℕ∞) => trimCurve (brOf J (consSeq p.1 p.2)) := by
  have htrim : Measurable trimCurve := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i ≤ 1
    · simp only [trimCurve, hi, ite_true]; exact measurable_const
    · simp only [trimCurve, hi, ite_false]; exact measurable_pi_apply i
  have hcons : Measurable fun p : (Fin J → ℕ∞) × (ℕ → Fin J → ℕ∞) => consSeq p.1 p.2 := by
    refine measurable_pi_iff.2 fun n => ?_
    cases n with
    | zero => exact measurable_fst
    | succ n => exact (measurable_pi_apply n).comp measurable_snd
  exact htrim.comp ((measurable_brCurve J).comp hcons)

/-! ### Independence of the blocks -/

/-- A function of the first `n` inputs and a function of the inputs after them are independent. -/
theorem map_pair_shift {α β : Type*} [MeasurableSpace U] [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure U) [IsProbabilityMeasure ν] (n : ℕ) (F : (ℕ → U) → α) (G : (ℕ → U) → β)
    (hF : Measurable F) (hG : Measurable G)
    (hFn : ∀ v v' : ℕ → U, (∀ k < n, v k = v' k) → F v = F v') :
    (iidMeasure ν).map (fun v => (F v, G fun k => v (n + k))) =
      ((iidMeasure ν).map F).prod ((iidMeasure ν).map G) := by
  obtain ⟨u₀⟩ : Nonempty U := nonempty_of_isProbabilityMeasure ν
  let ext : (Fin n → U) → ℕ → U := fun w k => if h : k < n then w ⟨k, h⟩ else u₀
  have hext : Measurable ext := measurable_pi_iff.2 fun k => by
    by_cases h : k < n
    · simp only [ext, h, dite_true]; exact measurable_pi_apply _
    · simp only [ext, h, dite_false]; exact measurable_const
  have hFe : ∀ v, F v = F (ext fun i : Fin n => v i) := fun v =>
    hFn _ _ fun k hk => by simp [ext, hk]
  have hres : Measurable fun η : ℕ → U => fun a : Fin n => η a :=
    measurable_pi_iff.2 fun a => measurable_pi_apply _
  have hsh : Measurable fun η : ℕ → U => fun b : ℕ => η (n + b) :=
    measurable_pi_iff.2 fun b => measurable_pi_apply _
  have hpair := infinitePi_map_pair_comp ν (Fin.val : Fin n → ℕ) (fun k : ℕ => n + k)
    Fin.val_injective (fun a b h => by simpa using h) (fun a b => by omega)
  have hfun : (fun v => (F v, G fun k => v (n + k))) =
      Prod.map (F ∘ ext) G ∘ (fun η : ℕ → U => (fun a : Fin n => η a, fun b => η (n + b))) := by
    funext v
    simp only [Function.comp_apply, Prod.map_apply]
    rw [← hFe v]
  have hmF : (iidMeasure ν).map F = (Measure.infinitePi fun _ : Fin n => ν).map (F ∘ ext) := by
    have : F = (F ∘ ext) ∘ (fun η : ℕ → U => fun a : Fin n => η a) := funext fun v => hFe v
    conv_lhs => rw [this]
    rw [← Measure.map_map (hF.comp hext) hres]
    unfold iidMeasure
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective]
  rw [hfun, ← Measure.map_map ((hF.comp hext).prodMap hG) (hres.prodMk hsh)]
  unfold iidMeasure at hmF ⊢
  rw [hpair, ← Measure.map_prod_map _ _ (hF.comp hext) hG, hmF]

/-- A function of the first `J` inputs, read on the consecutive groups of `J` inputs, gives
i.i.d. values. -/
theorem map_blocks_iid {α : Type*} [MeasurableSpace U] [MeasurableSpace α] (ν : Measure U)
    [IsProbabilityMeasure ν] (J : ℕ) (hJ : 1 ≤ J) (G : (ℕ → U) → α) (hG : Measurable G)
    (hGJ : ∀ v v' : ℕ → U, (∀ k < J, v k = v' k) → G v = G v') :
    (iidMeasure ν).map (fun v (b : ℕ) => G fun k => v (J * b + k)) =
      iidMeasure ((iidMeasure ν).map G) := by
  obtain ⟨u₀⟩ : Nonempty U := nonempty_of_isProbabilityMeasure ν
  let ext : (Fin J → U) → ℕ → U := fun w k => if h : k < J then w ⟨k, h⟩ else u₀
  have hext : Measurable ext := measurable_pi_iff.2 fun k => by
    by_cases h : k < J
    · simp only [ext, h, dite_true]; exact measurable_pi_apply _
    · simp only [ext, h, dite_false]; exact measurable_const
  have hGe : ∀ v, G v = G (ext fun i : Fin J => v i) := fun v =>
    hGJ _ _ fun k hk => by simp [ext, hk]
  have hres : Measurable fun η : ℕ → U => fun a : Fin J => η a :=
    measurable_pi_iff.2 fun a => measurable_pi_apply _
  have hmG : (Measure.infinitePi fun _ : Fin J => ν).map (G ∘ ext) = (iidMeasure ν).map G := by
    have : G = (G ∘ ext) ∘ (fun η : ℕ → U => fun a : Fin J => η a) := funext fun v => hGe v
    conv_rhs => rw [this]
    rw [← Measure.map_map (hG.comp hext) hres]
    unfold iidMeasure
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective]
  let e : ℕ × Fin J → ℕ := fun p => J * p.1 + p.2
  have he : Function.Injective e := by
    rintro ⟨b, k⟩ ⟨b', k'⟩ h
    change J * b + (k : ℕ) = J * b' + (k' : ℕ) at h
    have hk := k.isLt
    have hk' := k'.isLt
    have h1 : b = b' := by
      have h2 := congrArg (· / J) h
      simp only [Nat.mul_add_div (by omega : 0 < J), Nat.div_eq_of_lt hk,
        Nat.div_eq_of_lt hk', add_zero] at h2
      exact h2
    subst h1
    have hkk : (k : ℕ) = k' := by omega
    exact Prod.ext rfl (Fin.ext hkk)
  have he' : Measurable fun v : ℕ → U => fun p : ℕ × Fin J => v (e p) :=
    measurable_pi_iff.2 fun p => measurable_pi_apply _
  have hfun : (fun v (b : ℕ) => G fun k => v (J * b + k)) =
      (fun W : ℕ → Fin J → U => fun b => (G ∘ ext) (W b)) ∘
        (MeasurableEquiv.curry ℕ (Fin J) U) ∘ (fun v : ℕ → U => fun p : ℕ × Fin J => v (e p)) := by
    funext v b
    exact hGe _
  have hW : Measurable fun W : ℕ → Fin J → U => fun b => (G ∘ ext) (W b) :=
    measurable_pi_iff.2 fun b => (hG.comp hext).comp (measurable_pi_apply b)
  rw [hfun, ← Measure.map_map hW ((MeasurableEquiv.curry ℕ (Fin J) U).measurable.comp he'),
    ← Measure.map_map (MeasurableEquiv.curry ℕ (Fin J) U).measurable he']
  unfold iidMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj he,
    Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin J) => ν),
    Measure.infinitePi_map_pi (μ := fun _ : ℕ => Measure.infinitePi fun _ : Fin J => ν)
      (fun _ => hG.comp hext)]
  congr 1
  funext b
  rw [hmG]
  rfl

/-! ### The law of the returns, one move at a time -/

/-- **One move of the chain under i.i.d. inputs.** -/
theorem lintegral_chainDeliv_cons [MeasurableSpace U] [Countable S] (f : S → U → ℕ × S)
    (hf : ∀ s r, MeasurableSet {u | f s u = r}) (ν : Measure U) [IsProbabilityMeasure ν] (s : S)
    (G : (ℕ → ℕ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ v, G (chainDeliv f s v) ∂(iidMeasure ν) =
      ∫⁻ u, ∫⁻ v, G (fun m => if m = 0 then 0 else (f s u).1 + chainDeliv f (f s u).2 v (m - 1))
        ∂(iidMeasure ν) ∂ν := by
  have hst : ∀ (v : ℕ → U) j, chainState f s v (j + 1) =
      chainState f (f s (v 0)).2 (fun k => v (k + 1)) j := by
    intro v j
    induction j with
    | zero => rfl
    | succ j ih => simp only [chainState] at ih ⊢; rw [ih]
  have hpath : ∀ v : ℕ → U, chainDeliv f s v = fun m => if m = 0 then 0 else
      (f s (v 0)).1 + chainDeliv f (f s (v 0)).2 (fun k => v (k + 1)) (m - 1) := by
    intro v
    funext m
    split_ifs with hm
    · subst hm; simp [chainDeliv]
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [chainDeliv, Finset.sum_range_succ', hst, Nat.add_sub_cancel]
      rw [add_comm]
      rfl
  have hcoord : ∀ m, Measurable fun p : U × (ℕ → U) =>
      if m = 0 then 0 else (f s p.1).1 + chainDeliv f (f s p.1).2 p.2 (m - 1) := by
    intro m
    by_cases hm : m = 0
    · simp only [hm, ite_true]; exact measurable_const
    · simp only [hm, ite_false]
      refine measurable_to_countable' fun n => ?_
      have hset : (fun p : U × (ℕ → U) => (f s p.1).1 + chainDeliv f (f s p.1).2 p.2 (m - 1)) ⁻¹'
          {n} = ⋃ r : ℕ × S, {u | f s u = r} ×ˢ
            ((fun w => r.1 + chainDeliv f r.2 w (m - 1)) ⁻¹' {n}) := by
        ext p
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_prod,
          Set.mem_ofPred_eq]
        constructor
        · intro h; exact ⟨f s p.1, rfl, h⟩
        · rintro ⟨r, hr, h⟩; rw [hr]; exact h
      rw [hset]
      exact MeasurableSet.iUnion fun r => (hf s r).prod
        (((measurable_chainDeliv f hf r.2 (m - 1)).const_add r.1) (measurableSet_singleton n))
  have hF : Measurable (Function.uncurry fun (u : U) (w : ℕ → U) =>
      G (fun m => if m = 0 then 0 else (f s u).1 + chainDeliv f (f s u).2 w (m - 1))) :=
    hG.comp (measurable_pi_iff.2 hcoord)
  simp only [hpath]
  exact lintegral_iid_cons ν _ hF

/-- The mass of a set under a finite sum of measures. -/
theorem list_sum_measure_apply {α : Type*} [MeasurableSpace α] (l : List (Measure α)) (A : Set α) :
    l.sum A = (l.map fun μ => μ A).sum := by
  induction l with
  | nil => simp
  | cons μ l ih => simp [Measure.add_apply, ih]

end Generic

/-! ### `Psi` does not read a child curve at `0` and `1` -/

/-- `Psi` reads a child curve `G` through `sup_(i ≤ m + 1) G(i)` at `m ≥ 1`. -/
theorem psiG_trimCurve {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1))
    (hG : ∀ c, G c 0 ≤ G c 2 ∧ G c 1 ≤ G c 2) :
    psiG (fun c => trimCurve (G c)) D = psiG G D := by
  have hcr : ∀ c, childRet (trimCurve (G c)) = childRet (G c) := by
    intro c
    funext m
    unfold childRet
    split_ifs with hm
    · rfl
    · have h2 : ((2 : ℕ) : ℕ∞) ≤ m + 1 := by
        have h1 : 1 ≤ m := Order.one_le_iff_ne_zero.2 hm
        calc ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ m + 1 := add_le_add h1 le_rfl
      apply le_antisymm
      · exact extCurve_le_of_le _ _ (fun i => by unfold trimCurve; split_ifs <;> simp) _
      · unfold extCurve
        refine iSup₂_le fun i hi => ?_
        by_cases hi1 : i ≤ 1
        · calc G c i ≤ G c 2 := by
                interval_cases i
                · exact (hG c).1
                · exact (hG c).2
            _ = trimCurve (G c) 2 := by simp [trimCurve]
            _ ≤ ⨆ (i : ℕ) (_ : (i : ℕ∞) ≤ m + 1), trimCurve (G c) i := le_iSup₂_of_le 2 h2 le_rfl
        · exact le_iSup₂_of_le i hi (by simp [trimCurve, hi1])
  unfold psiG psiN psiT
  simp only [hcr]

theorem psiLaw_map_trimCurve (d : ℕ) (P : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure P]
    (hP : ∀ᵐ G ∂P, G 0 ≤ G 2 ∧ G 1 ≤ G 2) :
    FrogModel.Recursion.psiLaw d (P.map trimCurve) = FrogModel.Recursion.psiLaw d P := by
  have htrim : Measurable trimCurve := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i ≤ 1
    · simp only [trimCurve, hi, ite_true]; exact measurable_const
    · simp only [trimCurve, hi, ite_false]; exact measurable_pi_apply i
  have hmeas : Measurable fun G : Fin d → ℕ → ℕ∞ => fun c => trimCurve (G c) :=
    measurable_pi_iff.2 fun c => htrim.comp (measurable_pi_apply c)
  have hdir : IsProbabilityMeasure (FrogModel.Recursion.dirMeasure d) := by
    unfold FrogModel.Recursion.dirMeasure; infer_instance
  unfold FrogModel.Recursion.psiLaw
  rw [← Measure.pi_map_pi (fun _ => htrim.aemeasurable)]
  conv_lhs => rw [← Measure.map_id (μ := FrogModel.Recursion.dirMeasure d)]
  rw [Measure.map_prod_map _ _ hmeas measurable_id,
    Measure.map_map measurable_psiG (hmeas.prodMap measurable_id)]
  refine Measure.map_congr ?_
  have hpi : ∀ᵐ G ∂(Measure.pi fun _ : Fin d => P), ∀ c, G c 0 ≤ G c 2 ∧ G c 1 ≤ G c 2 := by
    rw [ae_all_iff]
    intro c
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin d => P) (i := c)).eventually hP
  have hae : ∀ᵐ x ∂((Measure.pi fun _ : Fin d => P).prod (FrogModel.Recursion.dirMeasure d)),
      ∀ c, x.1 c 0 ≤ x.1 c 2 ∧ x.1 c 1 ≤ x.1 c 2 := by
    exact Measure.quasiMeasurePreserving_fst.ae hpi
  filter_upwards [hae] with x hx
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  exact psiG_trimCurve x.1 x.2 hx

theorem brLaw_ae_trim (J : ℕ) (hJ : 2 ≤ J) (H : Measure (Fin J → ℕ∞)) [IsProbabilityMeasure H]
    (hH : ∀ᵐ B ∂H, B ⟨0, by omega⟩ ≤ B ⟨1, by omega⟩) :
    ∀ᵐ G ∂brLaw J H, G 0 ≤ G 2 ∧ G 1 ≤ G 2 := by
  have hset : MeasurableSet {G : ℕ → ℕ∞ | G 0 ≤ G 2 ∧ G 1 ≤ G 2} := by
    have h : Measurable fun G : ℕ → ℕ∞ => (G 0, G 1, G 2) :=
      (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
    exact h (Set.to_countable {p : ℕ∞ × ℕ∞ × ℕ∞ | p.1 ≤ p.2.2 ∧ p.2.1 ≤ p.2.2}).measurableSet
  unfold brLaw
  rw [ae_map_iff (measurable_brCurve J).aemeasurable hset]
  have h0 : ∀ᵐ B ∂(Measure.infinitePi fun _ : ℕ => H),
      B 0 ⟨0, by omega⟩ ≤ B 0 ⟨1, by omega⟩ := by
    rw [← Measure.infinitePi_map_eval (fun _ : ℕ => H) 0] at hH
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable hH
  filter_upwards [h0] with B hB
  have e0 : FrogModel.Order.brCurve J (fun b => blockCurve (B b)) 0 = 0 := by
    simp [FrogModel.Order.brCurve, blockCurve]
  have e1 : FrogModel.Order.brCurve J (fun b => blockCurve (B b)) 1 = B 0 ⟨0, by omega⟩ := by
    simp only [FrogModel.Order.brCurve, Nat.div_eq_of_lt (show 1 < J by omega),
      Nat.mod_eq_of_lt (show 1 < J by omega), Finset.range_zero, Finset.sum_empty, zero_add,
      blockCurve]
    rw [dite_eq_left ⟨by omega, by omega⟩]
  have e2 : FrogModel.Order.brCurve J (fun b => blockCurve (B b)) 2 = B 0 ⟨1, by omega⟩ := by
    rcases Nat.lt_or_ge 2 J with h2 | h2
    · simp only [FrogModel.Order.brCurve, Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2,
        Finset.range_zero, Finset.sum_empty, zero_add, blockCurve]
      rw [dite_eq_left ⟨by omega, by omega⟩]
    · obtain rfl : J = 2 := by omega
      simp [FrogModel.Order.brCurve, blockCurve]
  simp only [e0, e1, e2]
  exact ⟨zero_le, hB⟩

end FrogModel.LemmaX

/-! ### The child chain of a table -/

namespace FrogModel.Cert.Data

open FrogModel.Engine FrogModel.LemmaX

/-- The blocks of `H*` are non-decreasing. -/
theorem hstar_ae_mono (D : Data) : ∀ᵐ B ∂D.hstar, Monotone B := by
  have hlist : ∀ l : List (Measure (Fin D.J → ℕ∞)), (∀ μ ∈ l, ∀ᵐ B ∂μ, Monotone B) →
      ∀ᵐ B ∂l.sum, Monotone B := by
    intro l hl
    induction l with
    | nil => simp
    | cons μ l ih =>
      rw [List.sum_cons, ae_add_measure_iff]
      exact ⟨hl μ (by simp), ih fun ν hν => hl ν (by simp [hν])⟩
  have htake : ∀ (l : List ℕ) (n m : ℕ), n ≤ m → (l.take n).sum ≤ (l.take m).sum := by
    intro l n m h
    have e := List.sum_take_add_sum_drop (l.take m) n
    rw [List.take_take, min_eq_left h] at e
    omega
  unfold Data.hstar
  rw [ae_add_measure_iff]
  constructor
  · refine Measure.ae_smul_measure ?_ _
    unfold Data.tabLaw
    refine hlist _ fun μ hμ => ?_
    obtain ⟨π, _, rfl⟩ := List.mem_map.1 hμ
    refine Measure.ae_smul_measure ?_ _
    rw [ae_dirac_eq]
    intro i j hij
    simp only [pathBlock, Nat.cast_le]
    rw [List.map_take, List.map_take]
    exact htake _ _ _ (by have : (i : ℕ) ≤ j := hij; omega)
  · refine Measure.ae_smul_measure ?_ _
    unfold Data.tailLaw
    rw [Measure.ae_sum_iff]
    intro n
    refine Measure.ae_smul_measure ?_ _
    rw [ae_dirac_eq]
    exact monotone_const

/-- The uniform selects an entry of positive weight. -/
theorem childStep_spec (D : Data) (h0 : D.I0) (h1 : D.I1) (s : CState) (hs : D.ChildWF s)
    (u : ℝ) :
    ∃ n, D.childStep s u = ((D.rowSeq s n).δ, (D.rowSeq s n).next) ∧ 0 < (D.rowSeq s n).p := by
  classical
  set u' : ℝ := if 0 ≤ u ∧ u < 1 then u else 0 with hu'
  have hu0 : 0 ≤ u' := by rw [hu']; split_ifs with h <;> [exact h.1; exact le_rfl]
  have hu1 : u' < 1 := by rw [hu']; split_ifs with h <;> [exact h.2; exact one_pos]
  have hcum : ∀ n, (D.rowCum s n : ℝ) = ∑ k ∈ Finset.range n, ((D.rowSeq s k).p : ℝ) := by
    intro n
    simp [Data.rowCum, Rat.cast_sum]
  have hex : ∃ n, u' < (D.rowCum s (n + 1) : ℝ) := by
    have ht := (D.rowSeq_hasSum h0 h1 s hs).tendsto_sum_nat
    obtain ⟨N, hN⟩ := (ht.eventually (lt_mem_nhds hu1)).exists_forall_of_atTop
    exact ⟨N, by rw [hcum]; exact hN (N + 1) (Nat.le_succ N)⟩
  have hdef : D.childStep s u = ((D.rowSeq s (Nat.find hex)).δ, (D.rowSeq s (Nat.find hex)).next) := by
    unfold Data.childStep
    rw [dite_eq_left hex]
  refine ⟨Nat.find hex, hdef, ?_⟩
  have hlt := Nat.find_spec hex
  have hle : (D.rowCum s (Nat.find hex) : ℝ) ≤ u' := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h]; simp [Data.rowCum, hu0]
    · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      rw [not_lt] at this
      rw [hm]
      exact this
  rw [hcum, Finset.sum_range_succ, ← hcum] at hlt
  have : (0 : ℝ) < ((D.rowSeq s (Nat.find hex)).p : ℝ) := by linarith
  exact_mod_cast this

/-- An entry of positive weight goes one level up, a level `J` read as `bdry`. -/
theorem rowSeq_level (D : Data) (h0 : D.I0) (_h1 : D.I1) (s : CState) (hs : D.ChildWF s) (n : ℕ)
    (hp : 0 < (D.rowSeq s n).p) :
    (s.level + 1 = D.J ∧ (D.rowSeq s n).next = .bdry) ∨
      (s.level + 1 < D.J ∧ (D.rowSeq s n).next.level = s.level + 1) := by
  have hJ2 : 2 ≤ D.J := h0.1
  have hgood : ∀ (k : ℕ) (X : CState), X.level = k → k ≤ D.J → s.level + 1 = k →
      (s.level + 1 = D.J ∧ (if k = D.J then CState.bdry else X) = .bdry) ∨
        (s.level + 1 < D.J ∧ (if k = D.J then CState.bdry else X).level = s.level + 1) := by
    intro k X hX hk hs
    by_cases h : k = D.J
    · left; exact ⟨by omega, by simp [h]⟩
    · right; refine ⟨by omega, ?_⟩
      simp only [h, ite_false, hX, hs]
  have hfin : ∀ e ∈ D.finRow s,
      (s.level + 1 = D.J ∧ e.next = .bdry) ∨ (s.level + 1 < D.J ∧ e.next.level = s.level + 1) := by
    intro e he
    cases s with
    | fresh =>
      simp only [Data.finRow, Data.freshRow, List.mem_flatMap, List.mem_map] at he
      obtain ⟨t₁, _, t₂, _, rfl⟩ := he
      exact hgood 2 (.lab 2 t₂.s') rfl hJ2 rfl
    | bdry =>
      simp only [Data.finRow, Data.bdryRow, List.mem_map] at he
      obtain ⟨t₁, _, rfl⟩ := he
      exact hgood 1 (.lab 1 t₁.s') rfl (by omega) rfl
    | lab q t =>
      simp only [Data.finRow, Data.labRow, List.mem_mergeSort, List.mem_map] at he
      obtain ⟨t₁, _, rfl⟩ := he
      exact hgood (q + 1) (.lab (q + 1) t₁.s') rfl (by have := hs.2.1; omega) rfl
    | tail q =>
      simp only [Data.finRow, Data.tailRow, List.mem_singleton] at he
      subst he
      exact hgood (q + 1) (.tail (q + 1)) rfl (by have := hs.2; omega) rfl
    | maxLab q =>
      simp only [Data.finRow, Data.maxRow, List.mem_map] at he
      obtain ⟨k, _, rfl⟩ := he
      exact hgood (q + 1) (.maxLab (q + 1)) rfl (by have := hs.2; omega) rfl
  by_cases hn : n < (D.finRow s).length
  · have h := hfin _ (List.getElem_mem hn)
    rwa [Data.rowSeq, dite_eq_left hn]
  · revert hp
    rw [Data.rowSeq, dite_eq_right hn]
    cases s with
    | fresh => intro _; exact hgood 2 (.tail 2) rfl hJ2 rfl
    | bdry => intro _; exact hgood 1 (.tail 1) rfl (by omega) rfl
    | lab q t => intro hp; exact absurd hp (lt_irrefl 0)
    | tail q => intro hp; exact absurd hp (lt_irrefl 0)
    | maxLab q => intro hp; exact absurd hp (lt_irrefl 0)

/-- **The chain reaches `bdry` at level `J`.** -/
theorem chainState_reach (D : Data) (h0 : D.I0) (h1 : D.I1) (n : ℕ) :
    ∀ s : CState, D.ChildWF s → s.level + n = D.J → ∀ v,
      chainState D.childStep s v n = .bdry := by
  have hJ2 : 2 ≤ D.J := h0.1
  have hlt : ∀ s : CState, D.ChildWF s → s.level < D.J := by
    intro s hs
    cases s with
    | fresh => show 1 < D.J; omega
    | bdry => show 0 < D.J; omega
    | lab q t => exact hs.2.1
    | tail q => exact hs.2
    | maxLab q => exact hs.2
  induction n with
  | zero =>
    intro s hs hl
    exact absurd hl (by have := hlt s hs; omega)
  | succ n ih =>
    intro s hs hl v
    have hst : ∀ (s : CState) (v : ℕ → ℝ) j, chainState D.childStep s v (j + 1) =
        chainState D.childStep (D.childStep s (v 0)).2 (fun k => v (k + 1)) j := by
      intro s v j
      induction j with
      | zero => rfl
      | succ j ihj => simp only [chainState] at ihj ⊢; rw [ihj]
    rw [hst]
    obtain ⟨m, hm, hp⟩ := childStep_spec D h0 h1 s hs (v 0)
    have hwf : D.ChildWF (D.childStep s (v 0)).2 := D.childWF_step h0 h1 s hs (v 0)
    rcases rowSeq_level D h0 h1 s hs m hp with ⟨hJ, hb⟩ | ⟨hJ, hlev⟩
    · have hn : n = 0 := by omega
      subst hn
      rw [hm]
      exact hb
    · rw [hm] at hwf ⊢
      exact ih _ hwf (by rw [hlev]; omega) _

/-- A tail state delivers nothing and goes one level up. -/
theorem childStep_tail (D : Data) (q : ℕ) (u : ℝ) :
    D.childStep (.tail q) u = (0, D.nxtTail (q + 1)) := by
  classical
  have hu1 : (if 0 ≤ u ∧ u < 1 then u else 0) < 1 := by
    split_ifs with h
    · exact h.2
    · exact one_pos
  have hr0 : D.rowSeq (.tail q) 0 = ⟨1, 0, D.nxtTail (q + 1)⟩ := by
    simp [Data.rowSeq, Data.finRow, Data.tailRow]
  have hex : ∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum (.tail q) (n + 1) : ℝ) :=
    ⟨0, by simpa [Data.rowCum, hr0] using hu1⟩
  unfold Data.childStep
  rw [dite_eq_left hex]
  have h0 : Nat.find hex = 0 := (Nat.find_eq_zero hex).2 (by simpa [Data.rowCum, hr0] using hu1)
  rw [h0, hr0]

/-- The tail states deliver nothing up to level `J`. -/
theorem chainDeliv_nxtTail (D : Data) (q m : ℕ) (h : q + m ≤ D.J) (v : ℕ → ℝ) :
    chainDeliv D.childStep (D.nxtTail q) v m = 0 := by
  induction m generalizing q v with
  | zero => simp [chainDeliv]
  | succ m ih =>
    have hq : D.nxtTail q = .tail q := by
      simp [Data.nxtTail, show q ≠ D.J by omega]
    rw [add_comm m 1, chainDeliv_add, hq]
    have h1 : chainDeliv D.childStep (.tail q) v 1 = 0 := by
      simp [chainDeliv, chainState, childStep_tail]
    have h2 : chainState D.childStep (.tail q) v 1 = D.nxtTail (q + 1) := by
      simp [chainState, childStep_tail]
    rw [h1, h2, ih (q + 1) (by omega)]

/-- The row sequence: the finite part, then the geometric tail (entries of weight `0` beyond). -/
theorem tsum_rowSeq_split (D : Data) (s : CState) (g : ℕ × CState → ℝ≥0∞) :
    ∑' n, ENNReal.ofReal ((D.rowSeq s n).p : ℝ) * g ((D.rowSeq s n).δ, (D.rowSeq s n).next) =
      ((D.finRow s).map fun e => ENNReal.ofReal (e.p : ℝ) * g (e.δ, e.next)).sum +
        match D.tailNext s with
        | some s' => ∑' m, ENNReal.ofReal (D.tailW m : ℝ) * g (D.T + 1 + m, s')
        | none => 0 := by
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := (D.finRow s).length)]
  congr 1
  · rw [Finset.sum_range]
    have h : ∀ i : Fin (D.finRow s).length, D.rowSeq s i = (D.finRow s)[(i : ℕ)] := by
      intro i
      rw [Data.rowSeq, dite_eq_left i.2]
    simp only [h]
    exact Fin.sum_univ_fun_getElem (D.finRow s) fun e => ENNReal.ofReal (e.p : ℝ) * g (e.δ, e.next)
  · cases htn : D.tailNext s with
    | none =>
      have h : ∀ n, D.rowSeq s (n + (D.finRow s).length) = ⟨0, 0, s⟩ := by
        intro n
        rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, htn]
      simp [h]
    | some s' =>
      have h : ∀ n, D.rowSeq s (n + (D.finRow s).length) = ⟨D.tailW n, D.T + 1 + n, s'⟩ := by
        intro n
        rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, htn]
      simp only [h]

/-- One entry from label `s` of level `q < J`. -/
theorem lintegral_lab_step (D : Data) (h0 : D.I0) (h1 : D.I1) (q s : ℕ) (hq1 : 1 ≤ q)
    (hq : q < D.J) (hs : s < D.nLabels q) (G : (ℕ → ℕ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ v, G (chainDeliv D.childStep (D.nxt q s) v) ∂(iidMeasure lam) =
      ((D.row q s).map fun t => ENNReal.ofReal (t.p : ℝ) *
        ∫⁻ v, G (fun m => if m = 0 then 0 else
          t.δ + chainDeliv D.childStep (D.nxt (q + 1) t.s') v (m - 1)) ∂(iidMeasure lam)).sum := by
  have hnxt : D.nxt q s = .lab q s := by simp [Data.nxt, hq.ne]
  set Φ : ℕ × CState → ℝ≥0∞ := fun r => ∫⁻ v, G (fun m => if m = 0 then 0 else
    r.1 + chainDeliv D.childStep r.2 v (m - 1)) ∂(iidMeasure lam) with hΦ
  have hwf : D.ChildWF (.lab q s) := ⟨hq1, hq, hs⟩
  rw [hnxt, lintegral_chainDeliv_cons D.childStep D.measurableSet_childStep_eq lam _ G hG]
  rw [D.lintegral_childStep h0 h1 _ hwf Φ, D.tsum_rowSeq_split (.lab q s) Φ]
  simp only [Data.tailNext, add_zero, Data.finRow, Data.labRow]
  rw [(List.Perm.map _ (List.mergeSort_perm _ _)).sum_eq, List.map_map]
  rfl

/-- **From label `s` of level `q`, the returns up to level `J` are those of a path of the table.** -/
theorem lintegral_lab (D : Data) (h0 : D.I0) (h1 : D.I1) (n : ℕ) :
    ∀ q s, 1 ≤ q → q + n = D.J → s < D.nLabels q → ∀ G : (ℕ → ℕ) → ℝ≥0∞, Measurable G →
      (∀ h h' : ℕ → ℕ, (∀ m ≤ n, h m = h' m) → G h = G h') →
      ∫⁻ v, G (chainDeliv D.childStep (D.nxt q s) v) ∂(iidMeasure lam) =
        ((D.paths n q s).map fun π => ENNReal.ofReal (pathProb π : ℝ) * G (cumSeq π)).sum := by
  have hlam : IsProbabilityMeasure (iidMeasure lam) := by unfold iidMeasure; infer_instance
  induction n with
  | zero =>
    intro q s hq1 hqn hs G hG hdep
    have hc : ∀ v, G (chainDeliv D.childStep (D.nxt q s) v) = G (cumSeq []) := fun v =>
      hdep _ _ fun m hm => by
        have : m = 0 := by omega
        subst this; simp [chainDeliv, cumSeq]
    simp only [hc, lintegral_const, measure_univ, mul_one]
    simp [Data.paths, pathProb]
  | succ n ih =>
    intro q s hq1 hqn hs G hG hdep
    have hq : q < D.J := by omega
    rw [D.lintegral_lab_step h0 h1 q s hq1 hq hs G hG]
    simp only [Data.paths, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply]
    obtain ⟨htab, hts⟩ := List.mem_filter.1 ht
    simp only [decide_eq_true_eq] at hts
    obtain ⟨-, -, hs', hp⟩ := h1.2.2.2.1 t htab
    rw [hts.1] at hs'
    set G' : (ℕ → ℕ) → ℝ≥0∞ := fun h => G fun m => if m = 0 then 0 else t.δ + h (m - 1) with hG'
    have hmG' : Measurable G' := by
      refine hG.comp (measurable_pi_iff.2 fun m => ?_)
      by_cases hm : m = 0
      · simp only [hm, ite_true]; exact measurable_const
      · simp only [hm, ite_false]; exact measurable_from_top.comp (measurable_pi_apply _)
    have hdep' : ∀ h h' : ℕ → ℕ, (∀ m ≤ n, h m = h' m) → G' h = G' h' := fun h h' hh =>
      hdep _ _ fun m hm => by
        by_cases h0m : m = 0
        · simp [h0m]
        · simp only [h0m, ite_false]; rw [hh (m - 1) (by omega)]
    have := ih (q + 1) t.s' (by omega) (by omega) hs' G' hmG' hdep'
    simp only [hG'] at this
    rw [this, ← List.sum_map_mul_left, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun π _ => ?_)
    simp only [Function.comp_apply, pathProb, List.map_cons, List.prod_cons, Rat.cast_mul]
    rw [ENNReal.ofReal_mul (by exact_mod_cast hp.le), mul_assoc]
    congr 2
    congr 1
    funext m
    cases m with
    | zero => simp [cumSeq]
    | succ k => simp [cumSeq, List.take_succ_cons]

/-- **The returns of a block from `bdry`.** -/
theorem lintegral_bdry (D : Data) (h0 : D.I0) (h1 : D.I1) (G : (ℕ → ℕ) → ℝ≥0∞)
    (hG : Measurable G) (hGJ : ∀ h h' : ℕ → ℕ, (∀ m ≤ D.J, h m = h' m) → G h = G h') :
    ∫⁻ v, G (chainDeliv D.childStep .bdry v) ∂(iidMeasure lam) =
      ((D.paths D.J 0 0).map fun π =>
          ENNReal.ofReal (((1 - D.eps) * pathProb π : ℚ) : ℝ) * G (cumSeq π)).sum +
        ∑' m, ENNReal.ofReal (D.tailW m : ℝ) * G (fun k => if k = 0 then 0 else D.T + 1 + m) := by
  have hJ : 2 ≤ D.J := h0.1
  have heps : (0 : ℚ) ≤ 1 - D.eps := by linarith [h0.2.2.2.1]
  have hlam : IsProbabilityMeasure (iidMeasure lam) := by unfold iidMeasure; infer_instance
  set Φ : ℕ × CState → ℝ≥0∞ := fun r => ∫⁻ v, G (fun m => if m = 0 then 0 else
    r.1 + chainDeliv D.childStep r.2 v (m - 1)) ∂(iidMeasure lam) with hΦ
  rw [lintegral_chainDeliv_cons D.childStep D.measurableSet_childStep_eq lam _ G hG]
  rw [D.lintegral_childStep h0 h1 .bdry (by simp [Data.ChildWF]) Φ, D.tsum_rowSeq_split .bdry Φ]
  simp only [Data.tailNext, Data.finRow, Data.bdryRow]
  congr 1
  · rw [show D.paths D.J 0 0 = D.paths (D.J - 1 + 1) 0 0 by rw [Nat.sub_add_cancel (by omega)]]
    simp only [Data.paths, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply]
    obtain ⟨htab, hts⟩ := List.mem_filter.1 ht
    simp only [decide_eq_true_eq] at hts
    obtain ⟨-, -, hs', hp⟩ := h1.2.2.2.1 t htab
    rw [hts.1] at hs'
    set G' : (ℕ → ℕ) → ℝ≥0∞ := fun h => G fun m => if m = 0 then 0 else t.δ + h (m - 1) with hG'
    have hmG' : Measurable G' := by
      refine hG.comp (measurable_pi_iff.2 fun m => ?_)
      by_cases hm : m = 0
      · simp only [hm, ite_true]; exact measurable_const
      · simp only [hm, ite_false]; exact measurable_from_top.comp (measurable_pi_apply _)
    have hdep' : ∀ h h' : ℕ → ℕ, (∀ m ≤ D.J - 1, h m = h' m) → G' h = G' h' := fun h h' hh =>
      hGJ _ _ fun m hm => by
        by_cases h0m : m = 0
        · simp [h0m]
        · simp only [h0m, ite_false]; rw [hh (m - 1) (by omega)]
    have := D.lintegral_lab h0 h1 (D.J - 1) 1 t.s' le_rfl (by omega) hs' G' hmG' hdep'
    simp only [hG'] at this
    simp only [hΦ]
    rw [this, ← List.sum_map_mul_left, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun π _ => ?_)
    simp only [Function.comp_apply, pathProb, List.map_cons, List.prod_cons, Rat.cast_mul]
    have e1 : (0 : ℝ) ≤ ((1 - D.eps : ℚ) : ℝ) := by exact_mod_cast heps
    have e2 : (0 : ℝ) ≤ (t.p : ℝ) := by exact_mod_cast hp.le
    have hcum : (fun m => if m = 0 then 0 else t.δ + cumSeq π (m - 1)) = cumSeq (t :: π) := by
      funext m
      cases m with
      | zero => simp [cumSeq]
      | succ k => simp [cumSeq, List.take_succ_cons]
    rw [hcum]
    simp only [ENNReal.ofReal_mul e1, ENNReal.ofReal_mul e2]
    ring
  · refine tsum_congr fun m => ?_
    congr 1
    simp only [hΦ]
    have hc : ∀ v, (G fun k => if k = 0 then 0 else
        D.T + 1 + m + chainDeliv D.childStep (D.nxtTail 1) v (k - 1)) =
        G (fun k => if k = 0 then 0 else D.T + 1 + m) := fun v =>
      hGJ _ _ fun k hk => by
        by_cases hk0 : k = 0
        · simp [hk0]
        · simp only [hk0, ite_false, D.chainDeliv_nxtTail 1 (k - 1) (by omega) v, add_zero]
    simp only [hc, lintegral_const, measure_univ, mul_one]

/-- **The returns of the first block from `fresh`.** -/
theorem lintegral_fresh (D : Data) (h0 : D.I0) (h1 : D.I1) (G : (ℕ → ℕ) → ℝ≥0∞)
    (hG : Measurable G) (hGJ : ∀ h h' : ℕ → ℕ, (∀ m ≤ D.J - 1, h m = h' m) → G h = G h') :
    ∫⁻ v, G (chainDeliv D.childStep .fresh v) ∂(iidMeasure lam) =
      ((D.paths D.J 0 0).map fun π => ENNReal.ofReal (((1 - D.eps) * pathProb π : ℚ) : ℝ) *
          G (fun k => if k = 0 then 0 else cumSeq π (k + 1))).sum +
        ∑' m, ENNReal.ofReal (D.tailW m : ℝ) * G (fun k => if k = 0 then 0 else D.T + 1 + m) := by
  have hJ : 2 ≤ D.J := h0.1
  have heps : (0 : ℚ) ≤ 1 - D.eps := by linarith [h0.2.2.2.1]
  have hlam : IsProbabilityMeasure (iidMeasure lam) := by unfold iidMeasure; infer_instance
  set Φ : ℕ × CState → ℝ≥0∞ := fun r => ∫⁻ v, G (fun m => if m = 0 then 0 else
    r.1 + chainDeliv D.childStep r.2 v (m - 1)) ∂(iidMeasure lam) with hΦ
  rw [lintegral_chainDeliv_cons D.childStep D.measurableSet_childStep_eq lam _ G hG]
  rw [D.lintegral_childStep h0 h1 .fresh (by simp [Data.ChildWF]) Φ, D.tsum_rowSeq_split .fresh Φ]
  simp only [Data.tailNext, Data.finRow, Data.freshRow]
  congr 1
  · rw [show D.paths D.J 0 0 = D.paths (D.J - 2 + 1 + 1) 0 0 by congr 1; omega]
    simp only [Data.paths, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun t₁ ht₁ => ?_
    simp only [Function.comp_apply, List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun t₂ ht₂ => ?_
    simp only [Function.comp_apply, List.map_map]
    obtain ⟨htab₁, hts₁⟩ := List.mem_filter.1 ht₁
    obtain ⟨htab₂, hts₂⟩ := List.mem_filter.1 ht₂
    simp only [decide_eq_true_eq] at hts₁ hts₂
    obtain ⟨-, -, -, hp₁⟩ := h1.2.2.2.1 t₁ htab₁
    obtain ⟨-, -, hs₂, hp₂⟩ := h1.2.2.2.1 t₂ htab₂
    rw [hts₂.1] at hs₂
    set G' : (ℕ → ℕ) → ℝ≥0∞ := fun h => G fun m => if m = 0 then 0 else (t₁.δ + t₂.δ) + h (m - 1)
      with hG'
    have hmG' : Measurable G' := by
      refine hG.comp (measurable_pi_iff.2 fun m => ?_)
      by_cases hm : m = 0
      · simp only [hm, ite_true]; exact measurable_const
      · simp only [hm, ite_false]; exact measurable_from_top.comp (measurable_pi_apply _)
    have hdep' : ∀ h h' : ℕ → ℕ, (∀ m ≤ D.J - 2, h m = h' m) → G' h = G' h' := fun h h' hh =>
      hGJ _ _ fun m hm => by
        by_cases h0m : m = 0
        · simp [h0m]
        · simp only [h0m, ite_false]; rw [hh (m - 1) (by omega)]
    have := D.lintegral_lab h0 h1 (D.J - 2) 2 t₂.s' (by norm_num) (by omega) hs₂ G' hmG' hdep'
    simp only [hG'] at this
    simp only [hΦ]
    rw [this, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun π _ => ?_)
    simp only [Function.comp_apply, pathProb, List.map_cons, List.prod_cons, Rat.cast_mul]
    have e1 : (0 : ℝ) ≤ ((1 - D.eps : ℚ) : ℝ) := by exact_mod_cast heps
    have e2 : (0 : ℝ) ≤ (t₁.p : ℝ) := by exact_mod_cast hp₁.le
    have e3 : (0 : ℝ) ≤ (t₂.p : ℝ) := by exact_mod_cast hp₂.le
    have hcum : (fun m => if m = 0 then 0 else t₁.δ + t₂.δ + cumSeq π (m - 1)) =
        fun k => if k = 0 then 0 else cumSeq (t₁ :: t₂ :: π) (k + 1) := by
      funext m
      cases m with
      | zero => simp
      | succ k => simp [cumSeq, List.take_succ_cons, add_assoc]
    rw [hcum]
    simp only [ENNReal.ofReal_mul e1, ENNReal.ofReal_mul e2, ENNReal.ofReal_mul e3,
      ENNReal.ofReal_mul (mul_nonneg e1 e2)]
    ring
  · refine tsum_congr fun m => ?_
    congr 1
    simp only [hΦ]
    have hc : ∀ v, (G fun k => if k = 0 then 0 else
        D.T + 1 + m + chainDeliv D.childStep (D.nxtTail 2) v (k - 1)) =
        G (fun k => if k = 0 then 0 else D.T + 1 + m) := fun v =>
      hGJ _ _ fun k hk => by
        by_cases hk0 : k = 0
        · simp [hk0]
        · simp only [hk0, ite_false, D.chainDeliv_nxtTail 2 (k - 1) (by omega) v, add_zero]
    simp only [hc, lintegral_const, measure_univ, mul_one]

/-- `H*` of a measurable set, path by path and tail atom by tail atom. -/
theorem hstar_apply (D : Data) (h0 : D.I0) (A : Set (Fin D.J → ℕ∞)) (hA : MeasurableSet A) :
    D.hstar A = ((D.paths D.J 0 0).map fun π =>
        ENNReal.ofReal (((1 - D.eps) * pathProb π : ℚ) : ℝ) * A.indicator 1 (pathBlock D.J π)).sum +
      ∑' m, ENNReal.ofReal (D.tailW m : ℝ) * A.indicator 1 (fun _ => ((D.T + 1 + m : ℕ) : ℕ∞)) := by
  have heps : (0 : ℝ) ≤ ((1 - D.eps : ℚ) : ℝ) := by
    have := h0.2.2.2.1; exact_mod_cast (by linarith : (0 : ℚ) ≤ 1 - D.eps)
  have heps' : (0 : ℝ) ≤ ((D.eps : ℚ) : ℝ) := by exact_mod_cast h0.2.2.1.le
  simp only [Data.hstar, Data.tabLaw, Data.tailLaw, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, list_sum_measure_apply, List.map_map, Measure.sum_apply _ hA,
    Measure.dirac_apply' _ hA]
  congr 1
  · rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun π _ => ?_)
    simp only [Function.comp_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA,
      Rat.cast_mul, ENNReal.ofReal_mul heps, mul_assoc]
  · rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun m => ?_
    have ht : ((D.tailW m : ℚ) : ℝ) = ((D.eps : ℚ) : ℝ) * (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) := by
      simp only [Data.tailW]; push_cast; ring
    rw [ht, ENNReal.ofReal_mul heps', mul_assoc]

/-- **The block from `bdry` has law `H*`.** -/
theorem map_nextBlk_bdry (D : Data) (h0 : D.I0) (h1 : D.I1) :
    (iidMeasure lam).map (nextBlk D.childStep .bdry D.J) = D.hstar := by
  ext A hA
  have hN := measurable_nextBlk D.childStep D.measurableSet_childStep_eq .bdry D.J
  rw [Measure.map_apply hN hA, ← lintegral_indicator_one (hN hA), D.hstar_apply h0 A hA]
  set G : (ℕ → ℕ) → ℝ≥0∞ := fun h => A.indicator 1 (fun i : Fin D.J => ((h (i + 1) : ℕ) : ℕ∞))
    with hGdef
  have hmap : Measurable fun h : ℕ → ℕ => fun i : Fin D.J => ((h (i + 1) : ℕ) : ℕ∞) :=
    measurable_pi_iff.2 fun i => measurable_from_top.comp (measurable_pi_apply _)
  have hG : Measurable G := (measurable_const.indicator hA).comp hmap
  have hGJ : ∀ h h' : ℕ → ℕ, (∀ m ≤ D.J, h m = h' m) → G h = G h' := fun h h' hh => by
    simp only [hGdef]
    congr 1
    funext i
    rw [hh _ (by omega)]
  have hL : ∀ v, (nextBlk D.childStep .bdry D.J ⁻¹' A).indicator 1 v =
      G (chainDeliv D.childStep .bdry v) := fun v => by
    simp only [hGdef, Set.indicator, Set.mem_preimage, Pi.one_apply]; rfl
  simp only [hL]
  rw [D.lintegral_bdry h0 h1 G hG hGJ]
  congr 1

/-- **The first block from `fresh` has the law of `H*` with `B(1)` set to `0`.** -/
theorem map_firstBlk_fresh (D : Data) (h0 : D.I0) (h1 : D.I1) :
    (iidMeasure lam).map (firstBlk D.childStep .fresh D.J) = D.hstar.map zeroFirst := by
  ext A hA
  have hF := measurable_firstBlk D.childStep D.measurableSet_childStep_eq .fresh D.J
  have hz : Measurable (zeroFirst (J := D.J)) := measurable_of_countable _
  rw [Measure.map_apply hF hA, Measure.map_apply hz hA, ← lintegral_indicator_one (hF hA),
    D.hstar_apply h0 _ (hz hA)]
  set G : (ℕ → ℕ) → ℝ≥0∞ := fun h => A.indicator 1
    (fun i : Fin D.J => if (i : ℕ) = 0 then 0 else ((h i : ℕ) : ℕ∞)) with hGdef
  have hmap : Measurable fun h : ℕ → ℕ =>
      fun i : Fin D.J => if (i : ℕ) = 0 then (0 : ℕ∞) else ((h i : ℕ) : ℕ∞) := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, ite_true]; exact measurable_const
    · simp only [hi, ite_false]; exact measurable_from_top.comp (measurable_pi_apply _)
  have hG : Measurable G := (measurable_const.indicator hA).comp hmap
  have hGJ : ∀ h h' : ℕ → ℕ, (∀ m ≤ D.J - 1, h m = h' m) → G h = G h' := fun h h' hh => by
    simp only [hGdef]
    congr 1
    funext i
    rw [hh _ (by omega)]
  have hL : ∀ v, (firstBlk D.childStep .fresh D.J ⁻¹' A).indicator 1 v =
      G (chainDeliv D.childStep .fresh v) := fun v => by
    simp only [hGdef, Set.indicator, Set.mem_preimage, Pi.one_apply]; rfl
  simp only [hL]
  rw [D.lintegral_fresh h0 h1 G hG hGJ]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun π _ => ?_)
    congr 1
    have hpt : G (fun k => if k = 0 then 0 else cumSeq π (k + 1)) =
        A.indicator 1 (zeroFirst (pathBlock D.J π)) := by
      simp only [hGdef]
      congr 1
      funext i
      by_cases hi : (i : ℕ) = 0 <;> simp [hi, zeroFirst, pathBlock, cumSeq]
    rw [hpt]
    rfl
  · refine tsum_congr fun m => ?_
    congr 1
    have hpt : G (fun k => if k = 0 then 0 else D.T + 1 + m) =
        A.indicator 1 (zeroFirst fun _ : Fin D.J => ((D.T + 1 + m : ℕ) : ℕ∞)) := by
      simp only [hGdef]
      congr 1
      funext i
      by_cases hi : (i : ℕ) = 0 <;> simp [hi, zeroFirst]
    rw [hpt]
    rfl

end FrogModel.Cert.Data

namespace FrogModel.Cert.Data

open FrogModel.Engine FrogModel.LemmaX

theorem firstBlk_congr (D : Data) (v v' : ℕ → ℝ) (h : ∀ k < D.J - 1, v k = v' k) :
    firstBlk D.childStep .fresh D.J v = firstBlk D.childStep .fresh D.J v' := by
  funext i
  unfold firstBlk
  split_ifs with hi
  · rfl
  · rw [chainDeliv_congr D.childStep .fresh v v' i fun k hk => h k (by omega)]

theorem nextBlk_congr (D : Data) (v v' : ℕ → ℝ) (h : ∀ k < D.J, v k = v' k) :
    nextBlk D.childStep .bdry D.J v = nextBlk D.childStep .bdry D.J v' := by
  funext i
  unfold nextBlk
  rw [chainDeliv_congr D.childStep .bdry v v' (i + 1) fun k hk => h k (by omega)]

/-- **The child chain of a table**: from `fresh`, the delivery curve has the law `BR(H*)` at the
indices `≥ 2`. -/
theorem childLaw_gen (D : Data) (h0 : D.I0) (h1 : D.I1) :
    (iidMeasure lam).map (chainCurve D.childStep .fresh) = (brLaw D.J D.hstar).map trimCurve := by
  have hJ : 2 ≤ D.J := h0.1
  have hf := D.measurableSet_childStep_eq
  have hr0 : ∀ v, chainState D.childStep .fresh v (D.J - 1) = .bdry := fun v =>
    D.chainState_reach h0 h1 _ .fresh trivial (by simp only [CState.level]; omega) v
  have hrb : ∀ v, chainState D.childStep .bdry v D.J = .bdry := fun v =>
    D.chainState_reach h0 h1 _ .bdry trivial (by simp only [CState.level]; omega) v
  set Γ : (Fin D.J → ℕ∞) × (ℕ → Fin D.J → ℕ∞) → ℕ → ℕ∞ :=
    fun p => trimCurve (brOf D.J (consSeq p.1 p.2)) with hΓdef
  have hΓ : Measurable Γ := measurable_trim_brOf_cons D.J
  have hF := measurable_firstBlk D.childStep hf .fresh D.J
  have hN := measurable_nextBlk D.childStep hf .bdry D.J
  have hB : Measurable (blockSeq D.childStep .bdry D.J) :=
    measurable_pi_iff.2 fun b => hN.comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  have hshift : Measurable fun v : ℕ → ℝ => fun k => v (D.J - 1 + k) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply _
  have hpath : chainCurve D.childStep .fresh = Γ ∘ fun v =>
      (firstBlk D.childStep .fresh D.J v, blockSeq D.childStep .bdry D.J fun k => v (D.J - 1 + k)) :=
    funext fun v => chainCurve_eq_brOf D.childStep .fresh .bdry D.J hJ hr0 hrb v
  have hlam : IsProbabilityMeasure (iidMeasure lam) := by unfold iidMeasure; infer_instance
  have hprob : IsProbabilityMeasure D.hstar := by
    rw [← D.map_nextBlk_bdry h0 h1]; infer_instance
  have hprod : (iidMeasure lam).map (fun v =>
      (firstBlk D.childStep .fresh D.J v, blockSeq D.childStep .bdry D.J fun k => v (D.J - 1 + k))) =
      (D.hstar.map zeroFirst).prod (iidMeasure D.hstar) := by
    rw [map_pair_shift lam (D.J - 1) _ _ hF hB (D.firstBlk_congr), D.map_firstBlk_fresh h0 h1]
    congr 1
    unfold blockSeq
    rw [map_blocks_iid lam D.J (by omega) _ hN (D.nextBlk_congr), D.map_nextBlk_bdry h0 h1]
  have hz : Measurable (zeroFirst (J := D.J)) := measurable_of_countable _
  have hcons : Measurable fun p : (Fin D.J → ℕ∞) × (ℕ → Fin D.J → ℕ∞) => consSeq p.1 p.2 := by
    refine measurable_pi_iff.2 fun k => ?_
    cases k with
    | zero => exact measurable_fst
    | succ k => exact (measurable_pi_apply k).comp measurable_snd
  have hbc : ∀ s : ℕ, Measurable fun B : Fin D.J → ℕ∞ => blockCurve B s := fun s =>
    measurable_of_countable _
  have hadd : Measurable fun p : ℕ∞ × ℕ∞ => p.1 + p.2 := measurable_of_countable _
  have hbr : Measurable (brOf D.J) := by
    refine measurable_pi_iff.2 fun n => ?_
    unfold brOf FrogModel.Order.brCurve
    have hsum : ∀ N : ℕ, Measurable fun B : ℕ → Fin D.J → ℕ∞ =>
        ∑ b ∈ Finset.range N, blockCurve (B b) D.J := by
      intro N
      induction N with
      | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact measurable_const
      | succ N ih =>
        simp only [Finset.sum_range_succ]
        exact hadd.comp (ih.prodMk ((hbc _).comp (measurable_pi_apply N)))
    exact hadd.comp ((hsum _).prodMk ((hbc _).comp (measurable_pi_apply _)))
  have htrim : Measurable trimCurve := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i ≤ 1
    · simp only [trimCurve, hi, ite_true]; exact measurable_const
    · simp only [trimCurve, hi, ite_false]; exact measurable_pi_apply i
  have hmeas : Measurable fun v : ℕ → ℝ => (firstBlk D.childStep .fresh D.J v,
      blockSeq D.childStep .bdry D.J fun k => v (D.J - 1 + k)) := hF.prodMk (hB.comp hshift)
  have hiid : IsProbabilityMeasure (iidMeasure D.hstar) := by
    unfold iidMeasure; infer_instance
  rw [hpath, ← Measure.map_map hΓ hmeas, hprod]
  have hbrLaw : brLaw D.J D.hstar = (iidMeasure D.hstar).map (brOf D.J) := rfl
  conv_rhs => rw [hbrLaw, Measure.map_map htrim hbr, ← map_cons_iid D.hstar,
    Measure.map_map (htrim.comp hbr) hcons]
  have hΓz : (trimCurve ∘ brOf D.J) ∘ (fun p : (Fin D.J → ℕ∞) × (ℕ → Fin D.J → ℕ∞) =>
      consSeq p.1 p.2) = Γ ∘ Prod.map zeroFirst id := by
    funext p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, hΓdef]
    exact (trimCurve_brOf_zeroFirst D.J hJ p.1 p.2).symm
  conv_rhs => rw [hΓz, ← Measure.map_map hΓ (hz.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hz measurable_id, Measure.map_id]

/-- The child chain under `Psi`. -/
theorem childPsiLaw_gen (D : Data) (h0 : D.I0) (h1 : D.I1) (d : ℕ) :
    FrogModel.Recursion.psiLaw d ((iidMeasure lam).map (chainCurve D.childStep .fresh)) =
      FrogModel.Recursion.psiLaw d (brLaw D.J D.hstar) := by
  have hJ : 2 ≤ D.J := h0.1
  have hlam : IsProbabilityMeasure (iidMeasure lam) := by unfold iidMeasure; infer_instance
  have hprob : IsProbabilityMeasure D.hstar := by
    rw [← D.map_nextBlk_bdry h0 h1]; infer_instance
  have hbr : IsProbabilityMeasure (brLaw D.J D.hstar) := by
    unfold brLaw; infer_instance
  rw [D.childLaw_gen h0 h1]
  refine psiLaw_map_trimCurve d _ (brLaw_ae_trim D.J hJ D.hstar ?_)
  filter_upwards [D.hstar_ae_mono] with B hB
  exact hB (Fin.mk_le_mk.2 (Nat.zero_le 1))

end FrogModel.Cert.Data

namespace FrogModel.LemmaX

open FrogModel.Engine FrogModel.Cert

/-- **`ChildLaw`** (Lemma 6.1 of the paper). -/
theorem childLaw_holds : ChildLaw := cand.childLaw_gen cand_I0 cand_I1

/-- **`ChildPsiLaw`** (Lemma 6.1 of the paper). -/
theorem childPsiLaw_holds : ChildPsiLaw := cand.childPsiLaw_gen cand_I0 cand_I1 4

end FrogModel.LemmaX
