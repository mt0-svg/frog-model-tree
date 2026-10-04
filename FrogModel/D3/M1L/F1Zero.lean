module

public import FrogModel.D3.M1L.Planted
public import FrogModel.D3.M1L.Bridge

@[expose] public section

/-!
# Domination at height 0: the count of M1_L is at most `G_0(k)` on the frog paths

The domination of Lemma 13.1 of the paper, at `m = 0`. On the frog-path space the rule reads, at each
step, the next step of the path of the frog it names (`poolSeq_apply`). At height 0 the top closure
is the only one (every entry into a child of `w` is a ghost entry), so the state is the top frame or
the end of the run. Invariant (`Inv0`): the frogs of the pool are at `w`, the ghost frog is at its
vertex (strictly below `w`), each at the position its own path has after the steps read so far;
the frogs of the ups have paths that reach `y`; the pool, the ghost and the ups are distinct frogs
of the initial pool. Then the ups are distinct woken frogs whose paths reach `y`, at most `G_0(k)`
of them.
-/

namespace FrogModel.D3

/-- The frogs held by a state at height 0: pool, ghost and ups of the top frame, or the final
ups. -/
def held0 (s : St) : List Frog :=
  match s.stack with
  | [] => s.out
  | f :: _ => f.pool ++ (f.ghost.map Prod.fst).toList ++ f.ups

/-- The invariant of the run at height 0, for the paths `π` and the read counts `c`. -/
def Inv0 (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (s : St) : Prop :=
  (held0 s).Nodup ∧ (∀ φ ∈ held0 s, φ ∈ initPool k) ∧
  ((s.stack = [] ∧ ∀ φ ∈ s.out, ∃ i, pos π φ i = none) ∨
   ∃ f, s.stack = [f] ∧ f.v = [] ∧ f.killing = false ∧
     (∀ φ ∈ f.pool, pos π φ (c φ) = some []) ∧
     (∀ φ u, f.ghost = some (φ, u) → pos π φ (c φ) = some u ∧ u ≠ []) ∧
     (∀ φ ∈ f.ups, ∃ i, pos π φ i = none))

/-- The read counts after one more read. -/
def bump (c : Frog → ℕ) (r : Option Frog) : Frog → ℕ := fun ψ => c ψ + if r = some ψ then 1 else 0

theorem pos_succ (π : Frog → ℕ → Step 3) (φ : Frog) (i : ℕ) :
    pos π φ (i + 1) = stepStar (pos π φ i) (π φ i) := rfl

/-- The invariant at the start. -/
theorem inv0_init (k : ℕ) (π : Frog → ℕ → Step 3) : Inv0 k π (fun _ => 0) (init k) := by
  refine ⟨?_, ?_, Or.inr ⟨_, rfl, rfl, rfl, ?_, ?_, ?_⟩⟩
  · simp only [held0, init, Option.map_none, Option.toList_none, List.append_nil]
    refine List.Nodup.append ((List.nodup_range).map Sum.inl_injective) (List.nodup_singleton _) ?_
    simp
  · simp [held0, init, initPool]
  · intro φ hφ
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hφ
    rcases hφ with ⟨i, -, rfl⟩ | rfl <;> rfl
  · simp
  · simp

theorem bump_ne {c : Frog → ℕ} {r : Option Frog} {ψ : Frog} (h : r ≠ some ψ) :
    bump c r ψ = c ψ := by
  simp [bump, h]

theorem bump_self (c : Frog → ℕ) (φ : Frog) : bump c (some φ) φ = c φ + 1 := by
  simp [bump]

/-- A round of the top closure at height 0 keeps the invariant. -/
theorem inv0_round (p : Params) (hm : p.m = 0) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (x : Val)
    (marks : Finset (Vertex 3)) (out : List Frog) (isR : Bool) (f0 : ℕ) (φ : Frog) (ps ups : List Frog)
    (hnd : (φ :: ps ++ [] ++ ups).Nodup) (hI : ∀ a ∈ φ :: ps ++ [] ++ ups, a ∈ initPool k)
    (hpool : ∀ ψ ∈ φ :: ps, pos π ψ (c ψ) = some [])
    (hups : ∀ ψ ∈ ups, ∃ i, pos π ψ i = none)
    (hx : x.1 = π φ (c φ)) :
    Inv0 k π (bump c (some φ)) (upd p ⟨[⟨[], isR, f0, φ :: ps, ups, none, false⟩], marks, out⟩ x) := by
  have hφ := hpool φ (List.mem_cons_self ..)
  have hps : ∀ ψ ∈ ps, bump c (some φ) ψ = c ψ := fun ψ hψ => bump_ne (by
    intro h; cases h; exact (List.nodup_cons.1 (by simpa using hnd)).1 (List.mem_append_left _ hψ))
  have hnd' := hnd
  simp only [List.append_nil, List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd'
  by_cases hd : x.1.2 = 0
  · have hup : pos π φ (c φ + 1) = none := by
      rw [pos_succ, hφ, ← hx]; simp [stepStar, hd]
    simp only [upd, hd, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    set ups' := if ups.length < p.V then ups ++ [φ] else ups with hups'
    have hu' : ∀ ψ ∈ ups', ψ = φ ∨ ψ ∈ ups := by
      intro ψ h; rw [hups'] at h; split_ifs at h
      · simp only [List.mem_append, List.mem_singleton] at h; exact h.symm
      · exact Or.inr h
    have hnd2 : (ps ++ ups').Nodup := by
      rw [hups']; split_ifs
      · rw [← List.append_assoc]
        exact List.nodup_append.2 ⟨hnd'.2, List.nodup_singleton _, by
          simp only [List.mem_append, List.mem_singleton]; rintro a (ha | ha) b rfl rfl <;> simp_all⟩
      · exact hnd'.2
    have hreach : ∀ ψ ∈ ups', ∃ i, pos π ψ i = none := by
      intro ψ h; rcases hu' ψ h with rfl | h
      · exact ⟨_, hup⟩
      · exact hups ψ h
    have hI2 : ∀ a ∈ ps ++ ups', a ∈ initPool k := by
      intro a ha; apply hI; simp only [List.mem_append] at ha ⊢
      rcases ha with h | h
      · simp [h]
      · rcases hu' a h with rfl | h <;> simp [h]
    by_cases hps0 : ps = []
    · subst hps0
      simp only [settle, and_self, ↓reduceIte]
      exact ⟨by simpa [held0] using hnd2, by simpa [held0] using hI2, Or.inl ⟨rfl, hreach⟩⟩
    · simp only [settle, hps0, false_and, ↓reduceIte]
      refine ⟨by simpa [held0] using hnd2, by simpa [held0] using hI2,
        Or.inr ⟨_, rfl, rfl, rfl, ?_, by simp, hreach⟩⟩
      intro ψ hψ; rw [hps ψ hψ]; exact hpool ψ (List.mem_cons_of_mem _ hψ)
  · have hz : pos π φ (c φ + 1) = some [x.1.2.pred hd] := by
      rw [pos_succ, hφ, ← hx]; simp [stepStar, hd]
    simp only [upd, hd, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, List.length_nil, hm, true_or]
    refine ⟨?_, ?_, Or.inr ⟨_, rfl, rfl, rfl, ?_, ?_, hups⟩⟩
    · simp only [held0, Option.map_some, Option.toList_some]
      rw [List.append_assoc, List.singleton_append]; exact List.nodup_middle.2 (by simpa using hnd)
    · intro a ha; apply hI; simp only [held0, Option.map_some, Option.toList_some, List.mem_append,
        List.mem_singleton] at ha; simp only [List.mem_append, List.mem_cons, List.not_mem_nil]; tauto
    · intro ψ hψ; rw [hps ψ hψ]; exact hpool ψ (List.mem_cons_of_mem _ hψ)
    · intro ψ u h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [bump_self]; exact ⟨hz, by simp⟩


/-- A ghost step at height 0 keeps the invariant. -/
theorem inv0_ghost (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (x : Val)
    (marks : Finset (Vertex 3)) (out : List Frog) (isR : Bool) (f0 : ℕ) (φ : Frog) (u : Vertex 3)
    (pool ups : List Frog)
    (hnd : (pool ++ [φ] ++ ups).Nodup) (hI : ∀ a ∈ pool ++ [φ] ++ ups, a ∈ initPool k)
    (hpool : ∀ ψ ∈ pool, pos π ψ (c ψ) = some [])
    (hφ : pos π φ (c φ) = some u) (hu : u ≠ [])
    (hups : ∀ ψ ∈ ups, ∃ i, pos π ψ i = none)
    (hx : x.1 = π φ (c φ)) :
    Inv0 k π (bump c (some φ)) (upd p ⟨[⟨[], isR, f0, pool, ups, some (φ, u), false⟩], marks, out⟩ x) := by
  have hnd' : (φ :: (pool ++ ups)).Nodup := by
    rw [← List.nodup_middle]; simpa [List.append_assoc] using hnd
  have hps : ∀ ψ ∈ pool, bump c (some φ) ψ = c ψ := fun ψ hψ => bump_ne (by
    intro h; cases h; exact (List.nodup_cons.1 hnd').1 (List.mem_append_left _ hψ))
  obtain ⟨c', u0, rfl⟩ := List.exists_cons_of_ne_nil hu
  have hstep : pos π φ (c φ + 1) = some (ghostStep (c' :: u0) x.1) := by
    rw [pos_succ, hφ, ← hx, stepStar_cons]
  have hpool' : ∀ ψ ∈ pool, pos π ψ (bump c (some φ) ψ) = some [] := fun ψ hψ => by
    rw [hps ψ hψ]; exact hpool ψ hψ
  have hI' : ∀ a ∈ pool ++ ups, a ∈ initPool k := fun a ha => hI a (by
    simp only [List.mem_append, List.mem_singleton] at ha ⊢; tauto)
  simp only [upd, Bool.false_eq_true, ↓reduceIte, List.length_nil, zero_add]
  split_ifs with h0 hL
  · -- back at `w`: to the pool
    refine ⟨?_, ?_, Or.inr ⟨_, rfl, rfl, rfl, ?_, by simp, hups⟩⟩
    · simpa [held0] using hnd'
    · intro a ha; apply hI; simp only [held0, Option.map_none, Option.toList_none, List.append_nil,
        List.mem_append, List.mem_cons] at ha; simp only [List.mem_append, List.mem_singleton]; tauto
    · intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · rw [bump_self, hstep, h0]
      · exact hpool' ψ hψ
  · -- lost
    have hnd2 : (pool ++ ups).Nodup := (List.nodup_cons.1 hnd').2
    by_cases hp0 : pool = []
    · subst hp0
      simp only [settle, and_self, ↓reduceIte]
      exact ⟨by simpa [held0] using hnd2, by simpa [held0] using hI', Or.inl ⟨rfl, hups⟩⟩
    · simp only [settle, hp0, false_and, ↓reduceIte]
      exact ⟨by simpa [held0] using hnd2, by simpa [held0] using hI',
        Or.inr ⟨_, rfl, rfl, rfl, hpool', by simp, hups⟩⟩
  · -- the walk goes on
    refine ⟨by simpa [held0] using hnd, by simpa [held0] using hI,
      Or.inr ⟨_, rfl, rfl, rfl, hpool', ?_, hups⟩⟩
    intro ψ v h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [bump_self]; exact ⟨hstep, h0⟩

/-- One step of the run at height 0 keeps the invariant, the read counts bumped at the frog read. -/
theorem inv0_step (p : Params) (hm : p.m = 0) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ)
    (s : St) (x : Val) (h : Inv0 k π c s) (hx : ∀ φ, req s = some φ → x.1 = π φ (c φ)) :
    Inv0 k π (bump c (req s)) (upd p s x) := by
  obtain ⟨hnd, hI, hend | ⟨f, hs, hv, hkill, hpool, hghost, hups⟩⟩ := h
  · obtain ⟨st, marks, out⟩ := s
    simp only at hend
    obtain ⟨rfl, hout⟩ := hend
    simp only [upd, req]
    exact ⟨hnd, hI, Or.inl ⟨rfl, hout⟩⟩
  · obtain ⟨st, marks, out⟩ := s
    simp only at hs
    subst hs
    obtain ⟨v, isR, f0, pool, ups, ghost, killing⟩ := f
    simp only at hv hkill hpool hghost hups
    subst hv hkill
    simp only [held0] at hnd hI
    rcases ghost with _ | ⟨φ, u⟩
    · rcases pool with _ | ⟨φ, ps⟩
      · simp only [upd, req]
        exact ⟨by simpa [held0] using hnd, by simpa [held0] using hI,
          Or.inr ⟨_, rfl, rfl, rfl, by simp, by simp, hups⟩⟩
      · have hr : req ⟨[⟨[], isR, f0, φ :: ps, ups, none, false⟩], marks, out⟩ = some φ := rfl
        rw [hr]
        exact inv0_round p hm k π c x marks out isR f0 φ ps ups (by simpa using hnd)
          (by simpa using hI) hpool hups (hx φ hr)
    · have hr : req ⟨[⟨[], isR, f0, pool, ups, some (φ, u), false⟩], marks, out⟩ = some φ := rfl
      rw [hr]
      obtain ⟨hφ, hu⟩ := hghost φ u rfl
      exact inv0_ghost p k π c x marks out isR f0 φ u pool ups (by simpa using hnd)
        (by simpa using hI) hpool hφ hu hups (hx φ hr)

/-- The paths of the frog-path space: frog `φ` follows the steps of its pool. -/
def fpPaths (ω : Option Frog × ℕ → Val) (φ : Frog) (i : ℕ) : Step 3 := (ω (some φ, i)).1

/-- The number of reads of each frog in the first `n` steps of the run. -/
def reads (p : Params) (k : ℕ) (y : ℕ → Val) (n : ℕ) (φ : Frog) : ℕ :=
  ((Finset.range n).filter fun j => req (run p k y j) = some φ).card

theorem reads_succ (p : Params) (k : ℕ) (y : ℕ → Val) (n : ℕ) :
    reads p k y (n + 1) = bump (reads p k y n) (req (run p k y n)) := by
  funext φ
  simp only [reads, bump, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- **The invariant along the run on the frog paths at height 0.** -/
theorem inv0_run (p : Params) (hm : p.m = 0) (k : ℕ) (ω : Option Frog × ℕ → Val) (n : ℕ) :
    Inv0 k (fpPaths ω) (reads p k (Pool.poolSeq (sel p k) ω) n)
      (run p k (Pool.poolSeq (sel p k) ω) n) := by
  set y := Pool.poolSeq (sel p k) ω with hy
  induction n with
  | zero => exact inv0_init k (fpPaths ω)
  | succ n ih =>
    rw [reads_succ]
    refine inv0_step p hm k (fpPaths ω) _ _ (y n) ih fun φ hφ => ?_
    have h := poolSeq_apply p k ω n
    rw [← hy, hφ] at h
    rw [h]
    rfl

/-- **The domination of Lemma 13.1 of the paper, at height 0.** On the frog paths, the count of M1_L
after any number of reads is at most `G_0(k)`. -/
theorem f1_zero (p : Params) (hm : p.m = 0) (k : ℕ) (hk : 1 ≤ k) (ω : Option Frog × ℕ → Val)
    (n : ℕ) : (count (run p k (Pool.poolSeq (sel p k) ω) n) : ℕ∞) ≤ plantedG 0 k (fpPaths ω) := by
  obtain ⟨hnd, hI, hend | ⟨f, hs, -, -, -, -, hups⟩⟩ := inv0_run p hm k ω n
  all_goals set s := run p k (Pool.poolSeq (sel p k) ω) n
  · obtain ⟨hst, hout⟩ := hend
    have hc : count s = s.out.length := by simp [count, hst]
    rw [hc]
    simp only [held0, hst] at hnd hI
    rw [← List.toFinset_card_of_nodup hnd, ← Set.encard_coe_eq_coe_finsetCard, plantedG]
    refine Set.encard_le_encard fun φ hφ => ?_
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hφ
    exact ⟨woken_of_mem_initPool hk _ (hI φ hφ), hout φ hφ⟩
  · have hc : count s = f.ups.length := by simp [count, hs]
    rw [hc]
    simp only [held0, hs] at hnd hI
    have hnd' : f.ups.Nodup := hnd.sublist (List.sublist_append_right _ _)
    rw [← List.toFinset_card_of_nodup hnd', ← Set.encard_coe_eq_coe_finsetCard, plantedG]
    refine Set.encard_le_encard fun φ hφ => ?_
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hφ
    exact ⟨woken_of_mem_initPool hk _ (hI φ (List.mem_append_right _ hφ)), hups φ hφ⟩

end FrogModel.D3
