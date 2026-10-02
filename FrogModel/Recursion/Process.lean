module

public import FrogModel.LemmaX.Psi

@[expose] public section

/-!
# The processing at the root (Lemma 4.3 of the paper, deterministic part)

An abstract arrival system at the root `r` of `T*`. Arrivals `x : α` (a frog at `r`, ready for
its next step) are served one per root step; arrival `x` steps in direction `dir x`
(`0`: to the parent, `c.succ`: into child `c`). The initial arrivals are `init 0, init 1, ...`.
Given a set `S` of served arrivals, child `c` returns the arrivals `out c S`.

- `availSet init dir out S r`: the arrivals available after serving `S` with `r` initial
  arrivals released.
- `procHist`, `proc`, `served`, `released`: the processing. At each step the waiting arrival
  (available, not served) of least code is served; when none waits, the next initial arrival is
  released and served. So the cascade of the first `j` initial arrivals is served before
  `init j`.
- `arrSet init dir out j`: the least set containing `init a`, `a < j`, closed under the returns.
- `psiG_proc_eq`: with `D k = dir (proc k)` and child curves `G` whose returns after the first
  `n` root steps are the returns of the processing (`hG`), `psiG G D j` (LemmaX/Defs.lean) is
  the number of arrivals of `arrSet j` in direction `0`, provided infinitely many root steps
  go in direction `0`. If the release count stays at most `j`, both sides are infinite;
  otherwise `psiN G D j` is the step `n` at which `init j` is released, and the arrivals served
  before it are `arrSet j`.
-/

open FrogModel.LemmaX

namespace FrogModel.Recursion

/-- The arrivals available after serving `S` with the first `r` initial arrivals released. -/
def availSet {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) (S : Set α) (r : ℕ) : Set α :=
  init '' {a | a < r} ∪ ⋃ c : Fin d, out c {x | x ∈ S ∧ dir x = c.succ}

/-- The element of least code of a nonempty set. -/
noncomputable def minCode {α : Type*} [Encodable α] (W : Set α) (h : W.Nonempty) : α :=
  (measure (Encodable.encode : α → ℕ)).wf.min W h

open Classical in
/-- One root step: serve the waiting arrival of least code; if none waits, release and serve
the next initial arrival. The state is the list of served arrivals and the number released. -/
noncomputable def procStep {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (st : List α × ℕ) : List α × ℕ :=
  if h : (availSet init dir out {x | x ∈ st.1} st.2 \ {x | x ∈ st.1}).Nonempty then
    (st.1 ++ [minCode _ h], st.2)
  else (st.1 ++ [init st.2], st.2 + 1)

/-- The state after `k` root steps. -/
noncomputable def procHist {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) : ℕ → List α × ℕ
  | 0 => ([], 0)
  | k + 1 => procStep init dir out (procHist init dir out k)

/-- The arrival served at root step `k`. -/
noncomputable def proc {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (k : ℕ) : α :=
  (procHist init dir out (k + 1)).1.getLastD (init 0)

/-- The arrivals served in the first `n` root steps. -/
def served {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) (n : ℕ) : Set α :=
  {x | ∃ i < n, proc init dir out i = x}

/-- The number of initial arrivals released in the first `n` root steps. -/
noncomputable def released {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (n : ℕ) : ℕ :=
  (procHist init dir out n).2

/-- `A_j`: the least set of arrivals containing `init a`, `a < j`, and closed under the returns
of the children. -/
def arrSet {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) (j : ℕ) : Set α :=
  ⋂₀ {A | init '' {a | a < j} ⊆ A ∧ ∀ c : Fin d, out c {x | x ∈ A ∧ dir x = c.succ} ⊆ A}

/-! ### The history -/

/-- The state after `k + 1` steps extends the state after `k` steps by the arrival served. -/
theorem procHist_succ_fst {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (k : ℕ) :
    (procHist init dir out (k + 1)).1 = (procHist init dir out k).1 ++ [proc init dir out k] := by
  simp [procHist, proc, procStep]
  split_ifs with h
  · simp
  · simp

/-- The arrivals in the list after `k` steps are the arrivals served in the first `k` steps. -/
theorem mem_procHist {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (k : ℕ) (x : α) :
    x ∈ (procHist init dir out k).1 ↔ x ∈ served init dir out k := by
  induction k with
  | zero =>
    simp [procHist, served]
  | succ k ih =>
    rw [procHist_succ_fst]
    rw [List.mem_append, List.mem_singleton]
    have h_served_succ : x ∈ served init dir out (k + 1) ↔
      (x ∈ served init dir out k ∨ x = proc init dir out k) := by
      rw [served, Set.mem_ofPred_eq, served, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨i, hi, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with (hi | rfl)
        · exact Or.inl ⟨i, hi, hx⟩
        · exact Or.inr hx.symm
      · rintro (⟨i, hi, hx⟩ | hx)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
        · exact ⟨k, Nat.lt_succ_self k, hx.symm⟩
    rw [h_served_succ]
    rw [ih]

/-- One step: either a waiting arrival is served and nothing is released, or nothing waits and
the next initial arrival is released and served. -/
theorem proc_cases {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (k : ℕ) :
    (proc init dir out k ∈ availSet init dir out (served init dir out k)
        (released init dir out k) ∧
      proc init dir out k ∉ served init dir out k ∧
      released init dir out (k + 1) = released init dir out k) ∨
    (availSet init dir out (served init dir out k) (released init dir out k) ⊆
        served init dir out k ∧
      proc init dir out k = init (released init dir out k) ∧
      released init dir out (k + 1) = released init dir out k + 1) := by
  set st := procHist init dir out k with hst
  have hserved : served init dir out k = {x | x ∈ st.1} := by
    ext x; simp [FrogModel.Recursion.mem_procHist, hst]
  have hreleased : released init dir out k = st.2 := by
    simp [released, hst]
  have hprocHist_succ : procHist init dir out (k + 1) = procStep init dir out st := by
    simp [procHist, hst]
  have hproc : proc init dir out k = (procHist init dir out (k + 1)).1.getLastD (init 0) := by
    simp [proc]
  rw [hproc, hprocHist_succ]
  dsimp [procStep]
  split_ifs with h
  · -- h : (availSet init dir out {x | x ∈ st.1} st.2 \ {x | x ∈ st.1}).Nonempty
    have hmem_diff : minCode _ h ∈ availSet init dir out {x | x ∈ st.1} st.2 \ {x | x ∈ st.1} :=
      WellFounded.min_mem (measure (Encodable.encode : α → ℕ)).wf _ h
    have hmem_avail : minCode _ h ∈ availSet init dir out {x | x ∈ st.1} st.2 := hmem_diff.1
    have hnotmem_st : minCode _ h ∉ {x | x ∈ st.1} := hmem_diff.2
    have hnotmem_served : minCode _ h ∉ served init dir out k := by
      rw [hserved]
      exact hnotmem_st
    have hreleased_eq : released init dir out (k + 1) = released init dir out k := by
      rw [released, released, hprocHist_succ, ← hst]
      dsimp [procStep]
      simp [h]
    refine Or.inl ⟨?_, ?_, ?_⟩
    · -- proc k ∈ availSet ... (served k) (released k)
      dsimp
      rw [hserved, hreleased]
      simp
      exact hmem_avail
    · -- proc k ∉ served k
      dsimp
      simp
      exact hnotmem_served
    · exact hreleased_eq
  · -- h : ¬ (availSet init dir out {x | x ∈ st.1} st.2 \ {x | x ∈ st.1}).Nonempty
    have hempty : availSet init dir out {x | x ∈ st.1} st.2 \ {x | x ∈ st.1} = ∅ := by
      rwa [Set.not_nonempty_iff_eq_empty] at h
    have hsub : availSet init dir out {x | x ∈ st.1} st.2 ⊆ {x | x ∈ st.1} := by
      intro x hx
      by_contra! hnx
      have hx' : x ∈ availSet init dir out {x | x ∈ st.1} st.2 \ {x | x ∈ st.1} := ⟨hx, hnx⟩
      rw [hempty] at hx'
      simp at hx'
    have hsub_served : availSet init dir out (served init dir out k) (released init dir out k) ⊆ served init dir out k := by
      rw [hserved, hreleased]
      exact hsub
    have hproc_eq : (st.1 ++ [init st.2], st.2 + 1).1.getLastD (init 0) = init st.2 := by
      simp
    have hreleased_succ : released init dir out (k + 1) = released init dir out k + 1 := by
      rw [released, released, hprocHist_succ, ← hst]
      dsimp [procStep]
      simp [h]
    refine Or.inr ⟨?_, ?_, ?_⟩
    · exact hsub_served
    · -- proc k = init (released k)
      dsimp
      rw [hreleased]
      simp
    · exact hreleased_succ

/-- No initial arrival is released before the first step. -/
theorem released_zero {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) : released init dir out 0 = 0 := by
  unfold released procHist; rfl

/-- The number released never decreases. -/
theorem released_mono {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) :
    Monotone (released init dir out) := by
  refine monotone_nat_of_le_succ fun n => ?_
  unfold released
  have h : procHist init dir out (n + 1) = procStep init dir out (procHist init dir out n) := rfl
  rw [h]
  unfold procStep
  split
  · rfl
  · omega

/-- Either at most `j` initial arrivals are ever released, or there is a step `n` that releases
`init j`. -/
theorem released_cases {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (j : ℕ) :
    (∀ n, released init dir out n ≤ j) ∨
      ∃ n, released init dir out n ≤ j ∧ j < released init dir out (n + 1) := by
  by_cases h : ∀ n, released init dir out n ≤ j
  · left; exact h
  · right
    push Not at h
    have hreleased0 : released init dir out 0 = 0 := by
      unfold released procHist
      rfl
    have h0le : released init dir out 0 ≤ j := by
      rw [hreleased0]
      exact Nat.zero_le j
    let n0 := Nat.find h
    have hn0 : j < released init dir out n0 := Nat.find_spec h
    by_cases hn0zero : n0 = 0
    · rw [hn0zero] at hn0
      rw [hreleased0] at hn0
      exact absurd hn0 (Nat.not_lt_zero j)
    · rcases Nat.exists_eq_succ_of_ne_zero hn0zero with ⟨m, hm⟩
      have hm_lt_n0 : m < n0 := by
        rw [hm]
        exact Nat.lt_succ_self m
      have h_not_lt := Nat.find_min h hm_lt_n0
      have hm_le : released init dir out m ≤ j := Nat.le_of_not_gt h_not_lt
      refine ⟨m, hm_le, ?_⟩
      rw [hm] at hn0
      exact hn0

/-- The available set is monotone in the served set and in the number released. -/
theorem availSet_mono {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) (hmono : ∀ c, Monotone (out c)) {S S' : Set α} {r r' : ℕ}
    (hS : S ⊆ S') (hr : r ≤ r') : availSet init dir out S r ⊆ availSet init dir out S' r' := by
  unfold availSet
  apply Set.union_subset_union
  · intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    have ha' : a < r' := lt_of_lt_of_le ha hr
    exact ⟨a, ha', rfl⟩
  · apply Set.iUnion_mono
    intro c
    apply hmono c
    intro x hx
    exact ⟨hS hx.1, hx.2⟩

/-- Every arrival served in the first `k` steps is available after them. -/
theorem served_subset_availSet {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hmono : ∀ c, Monotone (out c))
    (k : ℕ) :
    served init dir out k ⊆
      availSet init dir out (served init dir out k) (released init dir out k) := by
  induction' k with k ih
  · -- k = 0: served set is empty
    intro x hx
    rcases hx with ⟨i, hi, _⟩
    exact (Nat.not_lt_zero i hi).elim
  · -- k → k+1
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    -- i < k+1, so either i < k or i = k
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with (hilt | hieq)
    · -- i < k: use induction hypothesis and monotonicity
      have h_served_k : proc init dir out i ∈ served init dir out k := ⟨i, hilt, rfl⟩
      have h_avail_k : proc init dir out i ∈
          availSet init dir out (served init dir out k) (released init dir out k) :=
        ih h_served_k
      have hserved_mono : served init dir out k ⊆ served init dir out (k + 1) := by
        intro y hy
        rcases hy with ⟨j, hj, rfl⟩
        exact ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hj), rfl⟩
      have hreleased_mono : released init dir out k ≤ released init dir out (k + 1) :=
        released_mono init dir out (Nat.le_succ k)
      exact availSet_mono init dir out hmono hserved_mono hreleased_mono h_avail_k
    · -- i = k: use proc_cases
      rcases proc_cases init dir out k with (hcase | hcase)
      · -- proc k ∈ availSet (served k) (released k)
        have hserved_mono : served init dir out k ⊆ served init dir out (k + 1) := by
          intro y hy
          rcases hy with ⟨j, hj, rfl⟩
          exact ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hj), rfl⟩
        have hreleased_mono : released init dir out k ≤ released init dir out (k + 1) :=
          released_mono init dir out (Nat.le_succ k)
        rw [hieq]
        exact availSet_mono init dir out hmono hserved_mono hreleased_mono hcase.1
      · -- availSet ⊆ served, proc k = init (released k), released (k+1) = released k + 1
        rcases hcase with ⟨_havail_sub, hproc_eq, hrel_eq⟩
        have h_lt : released init dir out k < released init dir out (k + 1) := by
          rw [hrel_eq]
          omega
        have h_mem_image : init (released init dir out k) ∈
            init '' {a | a < released init dir out (k + 1)} := by
          refine Set.mem_image_of_mem init h_lt
        have h_union : init '' {a | a < released init dir out (k + 1)} ⊆
            availSet init dir out (served init dir out (k + 1)) (released init dir out (k + 1)) := by
          intro y hy
          apply Set.mem_union_left
          exact hy
        rw [hieq, hproc_eq]
        exact h_union h_mem_image

/-- The initial arrivals served in the first `k` steps are the ones released. -/
theorem init_mem_served_iff {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hout : ∀ c S a, init a ∉ out c S) (k a : ℕ) :
    init a ∈ served init dir out k ↔ a < released init dir out k := by
  induction' k with k ih generalizing a
  · -- k = 0
    simp [served, released_zero]
  · -- k = k + 1
    have hserved_succ : served init dir out (k + 1) = served init dir out k ∪ {proc init dir out k} := by
      ext x; constructor
      · rintro ⟨i, hi, rfl⟩
        rw [Nat.lt_succ_iff] at hi
        rcases Nat.le_iff_lt_or_eq.mp hi with (hlt | heq)
        · apply Set.mem_union_left; exact ⟨i, hlt, rfl⟩
        · subst heq; apply Set.mem_union_right; exact Set.mem_singleton _
      · rintro (hx | hx)
        · rcases hx with ⟨i, hi, rfl⟩; exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
        · rw [Set.mem_singleton_iff.mp hx]; exact ⟨k, Nat.lt_succ_self k, rfl⟩
    rcases FrogModel.Recursion.proc_cases init dir out k with (hcase | hcase)
    · -- case 1: released (k+1) = released k, proc k ∈ availSet (served k) (released k), proc k ∉ served k
      rcases hcase with ⟨hproc_mem, hproc_not_served, hrel_eq⟩
      have hrel_succ_eq : released init dir out (k + 1) = released init dir out k := hrel_eq
      rw [hserved_succ, hrel_succ_eq]
      rw [Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro (h | h)
        · -- init a ∈ served k
          rcases (ih a).mp h with hlt
          exact Nat.lt_of_lt_of_le hlt (le_refl _)
        · -- init a = proc k
          rw [← h] at hproc_mem
          rw [FrogModel.Recursion.availSet, Set.mem_union] at hproc_mem
          rcases hproc_mem with (himg | hunion)
          · -- proc k ∈ init '' {a | a < released k}
            rw [Set.mem_image] at himg
            rcases himg with ⟨b, hb, h_eq⟩
            have h_init_eq : init a = init b := by rw [← h_eq]
            have ha_eq_b : a = b := hinit h_init_eq
            subst ha_eq_b
            exact hb
          · -- proc k ∈ ⋃ c, out c {x | x ∈ served k ∧ dir x = c.succ}
            rw [Set.mem_iUnion] at hunion
            rcases hunion with ⟨c, hc⟩
            exfalso; exact hout c {x | x ∈ served init dir out k ∧ dir x = c.succ} a hc
      · intro hlt
        exact Or.inl ((ih a).mpr hlt)
    · -- case 2: availSet (served k) (released k) ⊆ served k, proc k = init (released k), released (k+1) = released k + 1
      rcases hcase with ⟨hsub, hproc_eq, hrel_succ⟩
      have hrel_succ_eq : released init dir out (k + 1) = released init dir out k + 1 := hrel_succ
      rw [hserved_succ, hproc_eq, hrel_succ_eq]
      rw [Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro (h | h)
        · -- init a ∈ served k
          rcases (ih a).mp h with hlt
          exact Nat.lt_succ_of_lt hlt
        · -- init a = init (released k)
          have ha_eq : a = released init dir out k := hinit h
          rw [ha_eq]
          exact Nat.lt_succ_self _
      · intro hlt
        have hle : a ≤ released init dir out k := Nat.lt_succ_iff.mp hlt
        rcases lt_or_eq_of_le hle with (hlt' | heq)
        · -- a < released k
          exact Or.inl ((ih a).mpr hlt')
        · -- a = released k
          exact Or.inr (by rw [heq])

/-- The arrival served at step `k` was not served before. -/
theorem proc_not_mem_served {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hout : ∀ c S a, init a ∉ out c S) (k : ℕ) :
    proc init dir out k ∉ served init dir out k := by
  rcases proc_cases init dir out k with (⟨_, hnot, _⟩ | ⟨_, hproc, _⟩)
  · exact hnot
  · rw [hproc]
    intro hmem
    have hlt := ((init_mem_served_iff init dir out hinit hout k (released init dir out k)).mp hmem)
    exact lt_irrefl _ hlt

/-- No arrival is served twice. -/
theorem proc_injective {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hout : ∀ c S a, init a ∉ out c S) : Function.Injective (proc init dir out) := by
  intro i j h
  by_contra! hne
  have hlt : i < j ∨ j < i := Nat.lt_or_gt_of_ne hne
  rcases hlt with (hlt | hlt)
  · have hmem : proc init dir out j ∈ served init dir out j := by
      show ∃ (k : ℕ), k < j ∧ proc init dir out k = proc init dir out j
      exact ⟨i, hlt, h⟩
    exact proc_not_mem_served init dir out hinit hout j hmem
  · have hmem : proc init dir out i ∈ served init dir out i := by
      show ∃ (k : ℕ), k < i ∧ proc init dir out k = proc init dir out i
      exact ⟨j, hlt, h.symm⟩
    exact proc_not_mem_served init dir out hinit hout i hmem

/-- `n` arrivals are served in the first `n` steps. -/
theorem encard_served {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hout : ∀ c S a, init a ∉ out c S) (n : ℕ) :
    (served init dir out n).encard = n := by
  have h_image : served init dir out n = proc init dir out '' {i | i < n} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [h_image]
  have h_inj : Set.InjOn (proc init dir out) {i | i < n} :=
    (proc_injective init dir out hinit hout).injOn (s := {i | i < n})
  have h_encard : ({i | i < n} : Set ℕ).encard = n := by
    have h_eq : ({i | i < n} : Set ℕ) = Set.Iio n := by
      ext i; simp
    rw [h_eq, Set.encard_Iio]
    simp
  rw [Set.InjOn.encard_image h_inj, h_encard]

/-! ### The least closed set -/

/-- `arrSet j` contains the first `j` initial arrivals. -/
theorem init_mem_arrSet {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) {j a : ℕ} (ha : a < j) : init a ∈ arrSet init dir out j := by
  rw [FrogModel.Recursion.arrSet]
  refine Set.mem_sInter.mpr ?_
  intro A hA
  exact hA.1 (Set.mem_image_of_mem init ha)

/-- `arrSet j` is closed under the returns. -/
theorem out_subset_arrSet {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) (hmono : ∀ c, Monotone (out c)) (j : ℕ)
    (c : Fin d) :
    out c {x | x ∈ arrSet init dir out j ∧ dir x = c.succ} ⊆ arrSet init dir out j := by
  unfold arrSet
  refine Set.subset_sInter ?_
  intro A hA
  have hsub : {x | x ∈ ⋂₀ {A | init '' {a | a < j} ⊆ A ∧ ∀ c : Fin d, out c {x | x ∈ A ∧ dir x = c.succ} ⊆ A} ∧ dir x = c.succ} ⊆
    {x | x ∈ A ∧ dir x = c.succ} := by
    intro x hx
    rcases hx with ⟨hx_mem, hx_dir⟩
    refine ⟨Set.sInter_subset_of_mem hA hx_mem, hx_dir⟩
  have hmono' := hmono c hsub
  have hret' := hA.2 c
  exact Set.Subset.trans hmono' hret'

/-- `arrSet j` is contained in every closed set. -/
theorem arrSet_subset {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) (j : ℕ) (A : Set α) (hinit : init '' {a | a < j} ⊆ A)
    (hout : ∀ c, out c {x | x ∈ A ∧ dir x = c.succ} ⊆ A) : arrSet init dir out j ⊆ A := by
  exact Set.sInter_subset_of_mem ⟨hinit, hout⟩

/-- `arrSet` is monotone in `j`. -/
theorem arrSet_mono {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) : Monotone (arrSet init dir out) := by
  intro j j' h
  dsimp [arrSet]
  refine Set.sInter_subset_sInter ?_
  intro A hA
  rcases hA with ⟨hInit, hClosure⟩
  refine ⟨?_, hClosure⟩
  intro x hx
  rcases hx with ⟨a, ha, rfl⟩
  apply hInit
  simp at ha
  simp
  exact ⟨a, lt_of_lt_of_le ha h, rfl⟩

/-- The arrivals served while at most `j` initial arrivals are released lie in `arrSet j`. -/
theorem served_subset_arrSet {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hmono : ∀ c, Monotone (out c))
    {j n : ℕ} (hn : released init dir out n ≤ j) :
    served init dir out n ⊆ arrSet init dir out j := by
  induction n with
  | zero =>
      intro x hx
      rcases hx with ⟨i, hi, hx⟩
      exact (Nat.not_lt_zero _ hi).elim
  | succ n ih =>
      intro x hx
      rcases hx with ⟨i, hi, hx⟩
      have hi_le_n : i ≤ n := Nat.le_of_lt_succ hi
      rcases Nat.eq_or_lt_of_le hi_le_n with (heq | hi_lt_n)
      · -- heq : i = n, so x = proc n
        rw [heq] at hx
        have hreleased_n_le_j : released init dir out n ≤ j := by
          have hreleased_le : released init dir out n ≤ released init dir out (n + 1) :=
            released_mono init dir out (Nat.le_succ n)
          exact Nat.le_trans hreleased_le hn
        rcases proc_cases init dir out n with (hcase | hcase)
        · -- case 1: proc n ∈ availSet (served n) (released n)
          rcases hcase with ⟨hproc_mem, _, _⟩
          unfold availSet at hproc_mem
          rcases hproc_mem with (hinit | hout)
          · -- proc n = init a with a < released n
            rcases hinit with ⟨a, ha, ha'⟩
            have ha_lt_j : a < j := lt_of_lt_of_le ha hreleased_n_le_j
            rw [← hx, ← ha']
            exact init_mem_arrSet init dir out ha_lt_j
          · -- proc n ∈ ⋃ c, out c {x | x ∈ served n ∧ dir x = c.succ}
            rw [Set.mem_iUnion] at hout
            rcases hout with ⟨c, hc⟩
            have hserved_n : served init dir out n ⊆ arrSet init dir out j := ih hreleased_n_le_j
            have hsub : {x | x ∈ served init dir out n ∧ dir x = c.succ} ⊆
                         {x | x ∈ arrSet init dir out j ∧ dir x = c.succ} := by
              intro y hy
              exact ⟨hserved_n hy.1, hy.2⟩
            have hout_sub : out c {x | x ∈ served init dir out n ∧ dir x = c.succ} ⊆
                           out c {x | x ∈ arrSet init dir out j ∧ dir x = c.succ} :=
              (hmono c) hsub
            have hout_arr : out c {x | x ∈ arrSet init dir out j ∧ dir x = c.succ} ⊆
                           arrSet init dir out j := out_subset_arrSet init dir out hmono j c
            rw [← hx]
            exact hout_arr (hout_sub hc)
        · -- case 2: proc n = init (released n)
          rcases hcase with ⟨_, hproc_eq, hreleased_succ⟩
          rw [← hx, hproc_eq]
          have hreleased_n_lt_j : released init dir out n < j := by
            rw [hreleased_succ] at hn
            omega
          exact init_mem_arrSet init dir out hreleased_n_lt_j
      · -- hi_lt_n : i < n, use induction hypothesis
        have hreleased_n_le_j : released init dir out n ≤ j := by
          have hreleased_le : released init dir out n ≤ released init dir out (n + 1) :=
            released_mono init dir out (Nat.le_succ n)
          exact Nat.le_trans hreleased_le hn
        have hserved_n : served init dir out n ⊆ arrSet init dir out j := ih hreleased_n_le_j
        rw [← hx]
        exact hserved_n ⟨i, hi_lt_n, rfl⟩

/-! ### Counting -/

/-- The size of the available set: the released initial arrivals and the returns, all
disjoint. -/
theorem encard_availSet {d : ℕ} {α : Type*} (init : ℕ → α) (dir : α → Fin (d + 1))
    (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hout : ∀ c S a, init a ∉ out c S)
    (hdisj : ∀ c c' S S', c ≠ c' → Disjoint (out c S) (out c' S')) (S : Set α) (r : ℕ) :
    (availSet init dir out S r).encard =
      r + ∑ c : Fin d, (out c {x | x ∈ S ∧ dir x = c.succ}).encard := by
  unfold availSet
  have hdisj_union : Disjoint (init '' {a | a < r}) (⋃ c : Fin d, out c {x | x ∈ S ∧ dir x = c.succ}) := by
    rw [Set.disjoint_left]
    intro x hx_img hx_union
    rcases hx_img with ⟨a, ha, rfl⟩
    have hx_union' := hx_union
    -- hx_union : init a ∈ ⋃ c, out c {x | x ∈ S ∧ dir x = c.succ}
    -- We need to get a contradiction from hout
    rcases Set.mem_iUnion.mp hx_union with ⟨c, hc⟩
    exact hout c {x | x ∈ S ∧ dir x = c.succ} a hc
  rw [Set.encard_union_eq hdisj_union]
  have himage : (init '' {a | a < r}).encard = (r : ℕ∞) := by
    calc
      (init '' {a | a < r}).encard = ({a | a < r} : Set ℕ).encard := Set.InjOn.encard_image (hinit.injOn (s := {a | a < r}))
      _ = (r : ℕ∞) := Set.Nat.encard_range r
  rw [himage]
  have hunion : (⋃ c : Fin d, out c {x | x ∈ S ∧ dir x = c.succ}).encard = ∑ c : Fin d, (out c {x | x ∈ S ∧ dir x = c.succ}).encard := by
    have hpairwise : Pairwise (Function.onFun Disjoint (fun (c : Fin d) => out c {x | x ∈ S ∧ dir x = c.succ})) := by
      intro c c' hne
      exact hdisj c c' {x | x ∈ S ∧ dir x = c.succ} {x | x ∈ S ∧ dir x = c'.succ} hne
    have h := Set.encard_iUnion_of_finite hpairwise
    simpa [finsum_eq_sum_of_fintype] using h
  rw [hunion]

/-- The steps in direction `a` among the first `n`, counted by the arrivals served. -/
theorem dirCount_proc {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hout : ∀ c S a, init a ∉ out c S) (a : Fin (d + 1)) (n : ℕ∞) :
    dirCount (fun k => dir (proc init dir out k)) a n =
      {x | ∃ k : ℕ, (k : ℕ∞) < n ∧ proc init dir out k = x ∧ dir x = a}.encard := by
  unfold dirCount
  have h_image : {x | ∃ k : ℕ, (k : ℕ∞) < n ∧ proc init dir out k = x ∧ dir x = a} =
      (proc init dir out) '' {k : ℕ | (k : ℕ∞) < n ∧ dir (proc init dir out k) = a} := by
    ext x
    constructor
    · rintro ⟨k, hk_n, hk_eq, hk_dir⟩
      refine ⟨k, ⟨hk_n, ?_⟩, hk_eq⟩
      rw [hk_eq]
      exact hk_dir
    · rintro ⟨k, ⟨hk_n, hk_dir⟩, hk_eq⟩
      refine ⟨k, hk_n, hk_eq, ?_⟩
      rw [← hk_eq]
      exact hk_dir
  rw [h_image]
  rw [Set.InjOn.encard_image (proc_injective init dir out hinit hout).injOn]

/-- `T_j(n)` is the size of the set available after `n` steps with `j` initial arrivals. -/
theorem psiT_proc {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hout : ∀ c S a, init a ∉ out c S)
    (hdisj : ∀ c c' S S', c ≠ c' → Disjoint (out c S) (out c' S')) (G : Fin d → ℕ → ℕ∞)
    (hG : ∀ (c : Fin d) (n : ℕ),
      childRet (G c) (dirCount (fun k => dir (proc init dir out k)) c.succ n) =
        (out c {x | x ∈ served init dir out n ∧ dir x = c.succ}).encard) (j n : ℕ) :
    psiT G (fun k => dir (proc init dir out k)) j n =
      (availSet init dir out (served init dir out n) j).encard := by
  dsimp [psiT]
  have hsum : (∑ c : Fin d, childRet (G c) (dirCount (fun k => dir (proc init dir out k)) c.succ (n : ℕ∞))) =
             (∑ c : Fin d, (out c {x | x ∈ served init dir out n ∧ dir x = c.succ}).encard) := by
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [hG c n]
  rw [hsum]
  rw [← encard_availSet init dir out hinit hout hdisj (served init dir out n) j]

/-- While the step `n` releases at most `j` initial arrivals in total, more than `n` arrivals
are available with `j` initial ones. -/
theorem succ_le_encard_availSet {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hmono : ∀ c, Monotone (out c)) (hout : ∀ c S a, init a ∉ out c S) {j n : ℕ}
    (hn : released init dir out (n + 1) ≤ j) :
    (n : ℕ∞) + 1 ≤ (availSet init dir out (served init dir out n) j).encard := by
  set S := served init dir out n
  have hS_sub : S ⊆ availSet init dir out S (released init dir out n) :=
    served_subset_availSet init dir out hmono n
  have h_released_mono : released init dir out n ≤ released init dir out (n + 1) := by
    have := released_mono init dir out
    exact this (Nat.le_succ n)
  have h_released_n_le_j : released init dir out n ≤ j :=
    le_trans h_released_mono hn
  have h_availSet_mono : availSet init dir out S (released init dir out n) ⊆
      availSet init dir out S j :=
    availSet_mono init dir out hmono (by rfl) h_released_n_le_j
  have hS_sub_j : S ⊆ availSet init dir out S j :=
    Set.Subset.trans hS_sub h_availSet_mono
  rcases proc_cases init dir out n with (hcase | hcase)
  · -- case 1: proc n ∈ availSet S (released n) and released n = released (n+1)
    rcases hcase with ⟨hproc_mem, _, hreleased_eq⟩
    have hproc_mem_j : proc init dir out n ∈ availSet init dir out S j :=
      h_availSet_mono hproc_mem
    have h_not_mem : proc init dir out n ∉ S :=
      proc_not_mem_served init dir out hinit hout n
    have h_encard_insert : (insert (proc init dir out n) S).encard = (S.encard : ℕ∞) + 1 := by
      rw [Set.encard_insert_of_notMem h_not_mem]
    have h_encard_S : S.encard = (n : ℕ∞) := encard_served init dir out hinit hout n
    have h_encard_insert' : (insert (proc init dir out n) S).encard = (n : ℕ∞) + 1 := by
      rw [h_encard_insert, h_encard_S]
    have h_insert_sub : insert (proc init dir out n) S ⊆ availSet init dir out S j := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with (rfl | hx)
      · exact hproc_mem_j
      · exact hS_sub_j hx
    have h_le : (insert (proc init dir out n) S).encard ≤ (availSet init dir out S j).encard :=
      Set.encard_le_encard h_insert_sub
    rw [h_encard_insert'] at h_le
    exact h_le
  · -- case 2: availSet S (released n) ⊆ S, proc n = init (released n), released (n+1) = released n + 1
    rcases hcase with ⟨_, hproc_eq, hreleased_succ⟩
    have hreleased_n_lt_j : released init dir out n < j := by
      have : released init dir out n < released init dir out n + 1 := by omega
      rw [← hreleased_succ] at this
      omega
    have hproc_mem_j : proc init dir out n ∈ availSet init dir out S j := by
      rw [hproc_eq]
      apply Set.mem_union_left
      exact Set.mem_image_of_mem init hreleased_n_lt_j
    have h_not_mem : proc init dir out n ∉ S :=
      proc_not_mem_served init dir out hinit hout n
    have h_encard_insert : (insert (proc init dir out n) S).encard = (S.encard : ℕ∞) + 1 := by
      rw [Set.encard_insert_of_notMem h_not_mem]
    have h_encard_S : S.encard = (n : ℕ∞) := encard_served init dir out hinit hout n
    have h_encard_insert' : (insert (proc init dir out n) S).encard = (n : ℕ∞) + 1 := by
      rw [h_encard_insert, h_encard_S]
    have h_insert_sub : insert (proc init dir out n) S ⊆ availSet init dir out S j := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with (rfl | hx)
      · exact hproc_mem_j
      · exact hS_sub_j hx
    have h_le : (insert (proc init dir out n) S).encard ≤ (availSet init dir out S j).encard :=
      Set.encard_le_encard h_insert_sub
    rw [h_encard_insert'] at h_le
    exact h_le

/-- At the step `n` that releases `init j`, the arrivals available with `j` initial ones are
the arrivals served. -/
theorem availSet_eq_served {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hmono : ∀ c, Monotone (out c))
    {j n : ℕ} (hn : released init dir out n ≤ j) (hn' : j < released init dir out (n + 1)) :
    availSet init dir out (served init dir out n) j = served init dir out n := by
  rcases proc_cases init dir out n with (h | h)
  · -- first case: released (n+1) = released n ≤ j, contradicting hn'
    rcases h with ⟨_, _, hrel⟩
    have : released init dir out (n + 1) ≤ j := by
      -- from hrel: released (n+1) = released n, and hn: released n ≤ j
      linarith
    linarith [hn', this]
  · -- second case: released (n+1) = released n + 1, so released n = j
    rcases h with ⟨havail, _, hrel⟩
    have hrel_eq : released init dir out n = j := by
      have hle : j ≤ released init dir out n := by
        -- from hn': j < released (n+1) = released n + 1
        have : j < released init dir out n + 1 := by
          -- hrel: released (n+1) = released n + 1
          linarith
        omega
      omega
    have hsub1 : availSet init dir out (served init dir out n) j ⊆ served init dir out n := by
      -- from havail: availSet (served n) (released n) ⊆ served n, and released n = j
      simpa [hrel_eq] using havail
    have hsub2 : served init dir out n ⊆ availSet init dir out (served init dir out n) j := by
      -- from served_subset_availSet, using released n = j
      have := served_subset_availSet init dir out hmono n
      simpa [hrel_eq] using this
    exact Set.Subset.antisymm hsub1 hsub2

/-- At the step `n` that releases `init j`, the arrivals served are `arrSet j`. -/
theorem arrSet_eq_served {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α)
    (hmono : ∀ c, Monotone (out c)) {j n : ℕ}
    (hn : released init dir out n ≤ j) (hn' : j < released init dir out (n + 1)) :
    arrSet init dir out j = served init dir out n := by
  apply Set.Subset.antisymm
  · apply arrSet_subset init dir out j (served init dir out n)
    · have h : init '' {a | a < j} ⊆ availSet init dir out (served init dir out n) j := by
        unfold availSet
        apply Set.subset_union_left
      exact h.trans (availSet_eq_served init dir out hmono hn hn').le
    · intro c
      have h : out c {x | x ∈ served init dir out n ∧ dir x = c.succ} ⊆
          availSet init dir out (served init dir out n) j := by
        unfold availSet
        apply Set.subset_union_of_subset_right
        refine Set.subset_iUnion (fun (c' : Fin d) => out c' {x | x ∈ served init dir out n ∧ dir x = c'.succ}) c
      exact h.trans (availSet_eq_served init dir out hmono hn hn').le
  · exact served_subset_arrSet init dir out hmono hn

/-- `N(j)` is the step that releases `init j`. -/
theorem psiN_proc_eq {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hmono : ∀ c, Monotone (out c)) (hout : ∀ c S a, init a ∉ out c S)
    (hdisj : ∀ c c' S S', c ≠ c' → Disjoint (out c S) (out c' S')) (G : Fin d → ℕ → ℕ∞)
    (hG : ∀ (c : Fin d) (n : ℕ),
      childRet (G c) (dirCount (fun k => dir (proc init dir out k)) c.succ n) =
        (out c {x | x ∈ served init dir out n ∧ dir x = c.succ}).encard) {j n : ℕ}
    (hn : released init dir out n ≤ j) (hn' : j < released init dir out (n + 1)) :
    psiN G (fun k => dir (proc init dir out k)) j = n := by
  set D := fun k => dir (proc init dir out k) with hD
  have hpsiT_le : psiT G D j (n : ℕ∞) ≤ (n : ℕ∞) := by
    calc
      psiT G D j (n : ℕ∞) = (availSet init dir out (served init dir out n) j).encard := by
        rw [hD]
        exact psiT_proc init dir out hinit hout hdisj G hG j n
      _ = (served init dir out n).encard := by
        rw [availSet_eq_served init dir out hmono hn hn']
      _ = (n : ℕ∞) := by
        rw [encard_served init dir out hinit hout n]
      _ ≤ (n : ℕ∞) := le_refl _
  apply le_antisymm
  · exact psiN_le G D j (n : ℕ∞) hpsiT_le
  · unfold psiN
    apply le_sInf
    intro m hm
    by_cases hm_top : m = ⊤
    · rw [hm_top]
      exact le_top
    · have hm_ne_top : m ≠ ⊤ := hm_top
      rcases ENat.ne_top_iff_exists.mp hm_ne_top with ⟨k, hk⟩
      subst hk
      by_contra! hlt
      have hk_lt_n : k < n := ENat.natCast_lt_natCast.mp hlt
      have hrel : released init dir out (k + 1) ≤ j := by
        have hk1_le_n : k + 1 ≤ n := Nat.succ_le_of_lt hk_lt_n
        have hrel_mono := released_mono init dir out hk1_le_n
        exact le_trans hrel_mono hn
      have hsucc_le : (k : ℕ∞) + 1 ≤ (availSet init dir out (served init dir out k) j).encard :=
        succ_le_encard_availSet init dir out hinit hmono hout hrel
      have hpsiT_eq : psiT G D j (k : ℕ∞) = (availSet init dir out (served init dir out k) j).encard := by
        rw [hD]
        exact psiT_proc init dir out hinit hout hdisj G hG j k
      simp at hm
      rw [hpsiT_eq] at hm
      have h_contra : (k : ℕ∞) + 1 ≤ (k : ℕ∞) := le_trans hsucc_le hm
      have hk_succ_eq : (k : ℕ∞) + 1 = ((k + 1 : ℕ) : ℕ∞) := by
        simp [Nat.cast_succ]
      rw [hk_succ_eq] at h_contra
      have h_lt : (k : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by
        rw [ENat.natCast_lt_natCast]
        exact Nat.lt_succ_self k
      exact not_lt.mpr h_contra h_lt

/-- If `init j` is never released, `N(j)` is infinite. -/
theorem psiN_proc_top {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hmono : ∀ c, Monotone (out c)) (hout : ∀ c S a, init a ∉ out c S)
    (hdisj : ∀ c c' S S', c ≠ c' → Disjoint (out c S) (out c' S')) (G : Fin d → ℕ → ℕ∞)
    (hG : ∀ (c : Fin d) (n : ℕ),
      childRet (G c) (dirCount (fun k => dir (proc init dir out k)) c.succ n) =
        (out c {x | x ∈ served init dir out n ∧ dir x = c.succ}).encard) {j : ℕ}
    (hj : ∀ n, released init dir out n ≤ j) :
    psiN G (fun k => dir (proc init dir out k)) j = ⊤ := by
  rw [FrogModel.LemmaX.psiN_eq_top_iff]
  intro n
  rw [FrogModel.Recursion.psiT_proc init dir out hinit hout hdisj G hG j n]
  have hle : (n : ℕ∞) + 1 ≤ (availSet init dir out (served init dir out n) j).encard :=
    FrogModel.Recursion.succ_le_encard_availSet init dir out hinit hmono hout (hj (n + 1))
  have hlt : (n : ℕ∞) < (n : ℕ∞) + 1 := by
    simpa [Nat.cast_succ] using ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)
  exact hlt.trans_le hle

/-- **The processing computes `Psi`.** -/
theorem psiG_proc_eq {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir : α → Fin (d + 1)) (out : Fin d → Set α → Set α) (hinit : Function.Injective init)
    (hmono : ∀ c, Monotone (out c)) (hout : ∀ c S a, init a ∉ out c S)
    (hdisj : ∀ c c' S S', c ≠ c' → Disjoint (out c S) (out c' S')) (G : Fin d → ℕ → ℕ∞)
    (hG : ∀ (c : Fin d) (n : ℕ),
      childRet (G c) (dirCount (fun k => dir (proc init dir out k)) c.succ n) =
        (out c {x | x ∈ served init dir out n ∧ dir x = c.succ}).encard)
    (hzero : {k | dir (proc init dir out k) = 0}.Infinite) (j : ℕ) :
    psiG G (fun k => dir (proc init dir out k)) j =
      {x | x ∈ arrSet init dir out j ∧ dir x = 0}.encard := by
  rw [psiG]
  rcases released_cases init dir out j with (hj | hj)
  · -- Case: ∀ n, released n ≤ j
    have hpsiN : psiN G (fun k => dir (proc init dir out k)) j = ⊤ :=
      psiN_proc_top init dir out hinit hmono hout hdisj G hG hj
    rw [hpsiN]
    rw [dirCount]
    have hLHS : {k : ℕ | (k : ℕ∞) < (⊤ : ℕ∞) ∧ dir (proc init dir out k) = 0}.encard =
        {k | dir (proc init dir out k) = 0}.encard := by
      refine congrArg Set.encard ?_
      ext k
      simp
    rw [hLHS]
    have hLHS_top : {k | dir (proc init dir out k) = 0}.encard = ⊤ :=
      Set.Infinite.encard_eq hzero
    rw [hLHS_top]
    have hRHS_top : {x | x ∈ arrSet init dir out j ∧ dir x = 0}.encard = ⊤ := by
      have h_infinite : ({x | x ∈ arrSet init dir out j ∧ dir x = 0} : Set α).Infinite := by
        set S : Set ℕ := {k | dir (proc init dir out k) = 0} with hS
        have hS_infinite : S.Infinite := hzero
        have h_inj_on : Set.InjOn (proc init dir out) S :=
          (proc_injective init dir out hinit hout).injOn (s := S)
        have h_image_infinite : (proc init dir out '' S).Infinite :=
          Set.Infinite.image h_inj_on hS_infinite
        have h_subset : proc init dir out '' S ⊆ {x | x ∈ arrSet init dir out j ∧ dir x = 0} := by
          intro x hx
          rcases hx with ⟨k, hk, rfl⟩
          have h_served : proc init dir out k ∈ served init dir out (k + 1) := by
            refine ⟨k, by omega, rfl⟩
          have h_subset_arr : served init dir out (k + 1) ⊆ arrSet init dir out j :=
            served_subset_arrSet init dir out hmono (hj (k + 1))
          exact ⟨h_subset_arr h_served, hk⟩
        exact Set.Infinite.mono h_subset h_image_infinite
      exact Set.Infinite.encard_eq h_infinite
    rw [hRHS_top]
  · -- Case: ∃ n, released n ≤ j ∧ j < released (n+1)
    rcases hj with ⟨n, hn, hn'⟩
    have hpsiN : psiN G (fun k => dir (proc init dir out k)) j = (n : ℕ∞) :=
      psiN_proc_eq init dir out hinit hmono hout hdisj G hG hn hn'
    rw [hpsiN]
    rw [dirCount_proc init dir out hinit hout 0 (n : ℕ∞)]
    rw [arrSet_eq_served init dir out hmono hn hn']
    have h_set_eq : {x | ∃ k : ℕ, (k : ℕ∞) < (n : ℕ∞) ∧ proc init dir out k = x ∧ dir x = 0} =
        {x | x ∈ served init dir out n ∧ dir x = 0} := by
      ext x
      constructor
      · rintro ⟨k, hk_lt, hx, hx_dir⟩
        have hk_lt_n : k < n := by
          rwa [Nat.cast_lt] at hk_lt
        exact ⟨⟨k, hk_lt_n, hx⟩, hx_dir⟩
      · rintro ⟨⟨k, hk_lt_n, hx⟩, hx_dir⟩
        refine ⟨k, ?_, hx, hx_dir⟩
        rw [Nat.cast_lt]
        exact hk_lt_n
    rw [h_set_eq]

end FrogModel.Recursion
