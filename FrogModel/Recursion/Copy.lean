module

public import FrogModel.Recursion.Arrive

@[expose] public section

/-!
# The child curves (Lemma 4.3 of the paper)

Below the child `c` of `r`, the vertex `w ++ [c]` of `T*` is the vertex `w` of a copy of `T*`
whose leaf `y` is `r` (`walkStar_append`, Arrive.lean); depth `K + 1` in `T*` is depth `K` in
the copy. The copy at kill depth `K` has the sleeping frogs `copyZeta π c w`, the segments `0`
of the frogs at `w ++ [c]`, and the active frogs `copyXi π c e`: first the frog of `[c]` (woken
by the first entry), then the entries `e 0, e 1, ...` into `c`, each from its second step.

- `encard_starOut`: if the entries of `S` into `c` are `e 0, ..., e (m - 1)`, `m ≥ 1`, child
  `c` returns `curveK K (copyZeta π c) (copyXi π c e) (m + 1)` segments at kill depth `K + 1`.
- `starOut_eq_empty`: without entries, nothing returns.
-/

open MeasureTheory FrogModel.LemmaX

namespace FrogModel.Recursion

/-- The sleeping frogs of the copy below `c`. -/
def copyZeta {d : ℕ} (π : StarSeg d → ℕ → Step d) (c : Fin d) : Sample d :=
  fun w => π (Sum.inl (w ++ [c]), 0)

/-- The active frogs of the copy below `c`: the frog of `[c]`, then the entries `e i` from
their second step. -/
def copyXi {d : ℕ} (π : StarSeg d → ℕ → Step d) (c : Fin d) (e : ℕ → StarSeg d) :
    ℕ → ℕ → Step d
  | 0 => π (Sum.inl [c], 0)
  | i + 1 => fun t => π (e i) (t + 1)

/-- The entries of `S` into `c`. -/
def entrySet {d : ℕ} (π : StarSeg d → ℕ → Step d) (c : Fin d) (S : Set (StarSeg d)) :
    Set (StarSeg d) :=
  {x | x ∈ S ∧ isRootSeg x ∧ dirSeg π x = c.succ}

/-! ### Walks in the copy -/

section CopyWalk

variable {d : ℕ} {c : Fin d}

/-- Relates `stepStar` on `some (v ++ [c])` to `stepStar` on `some v`. -/
theorem stepStar_append (v : Vertex d) (ξ : Step d) :
    stepStar (some (v ++ [c])) ξ =
    match stepStar (some v) ξ with
    | none => some []
    | some w' => some (w' ++ [c]) := by
  by_cases h : ξ.2 = 0
  · simp [stepStar, h]
    by_cases hv : v = []
    · subst hv; simp
    · obtain ⟨a, v', hv_eq⟩ := List.exists_cons_of_ne_nil hv
      rw [hv_eq]
      simp
  · simp [stepStar, h]

/-- Relates `walkStar` on `some (w ++ [c])` to `walkStar` on `some w`, assuming the latter never hits `none`. -/
theorem walkStar_append_copy (w : Vertex d) (p : ℕ → Step d) (n : ℕ)
    (h : ∀ i < n, walkStar (some w) p i ≠ none) :
    walkStar (some (w ++ [c])) p n =
    match walkStar (some w) p n with
    | none => some []
    | some v => some (v ++ [c]) := by
  induction' n with n ih
  · simp [walkStar]
  · have hn : ∀ i < n, walkStar (some w) p i ≠ none := fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_succ _))
    have hn' : walkStar (some w) p n ≠ none := h n (Nat.lt_succ_self n)
    rw [walkStar, walkStar, ih hn]
    cases h_nonone_i : walkStar (some w) p n
    · exact (hn' h_nonone_i).elim
    · rename_i v
      simp [stepStar_append]

/-- If a walk from `some w` hits `none`, it stays at `none` forever. -/
theorem walkStar_none_absorb (w : Vertex d) (p : ℕ → Step d) {i : ℕ} (hi : walkStar (some w) p i = none) :
    ∀ j, i ≤ j → walkStar (some w) p j = none := by
  intro j hij
  induction' hij with k hik ih
  · exact hi
  · simp [walkStar, ih, stepStar]

end CopyWalk

/-- Visits of the copy within depth `K` are visits below `c` within depth `K + 1` before the
return to `r`. -/
theorem visitsK_copy_iff {d : ℕ} (K : ℕ) (c : Fin d) (w w' : Vertex d) (p : ℕ → Step d) :
    visitsK K (some w) p (some w') ↔ segVis (K + 1) (some (w ++ [c])) p (some (w' ++ [c])) := by
  constructor
  · -- forward direction: visitsK → segVis
    intro h
    rcases h with ⟨n, hn, hdepth⟩
    have h_nonone : ∀ i ≤ n, walkStar (some w) p i ≠ none := by
      intro i hi
      by_contra hnone
      have hwalk_none : walkStar (some w) p n = none :=
        walkStar_none_absorb w p hnone n hi
      rw [hn] at hwalk_none
      exact Option.some_ne_none _ hwalk_none
    have hR : walkStar (some (w ++ [c])) p n = some (w' ++ [c]) := by
      rw [walkStar_append_copy (c := c) w p n (fun i hi => h_nonone i (Nat.le_of_lt hi))]
      rw [hn]
    have h_no_return : ∀ i, 1 ≤ i → i < n → walkStar (some (w ++ [c])) p i ≠ some [] := by
      intro i hi1 hi2
      have h_nonone_i : walkStar (some w) p i ≠ none := h_nonone i (Nat.le_of_lt hi2)
      have h_lt_n : ∀ j < i, j < n := fun j hj => Nat.lt_trans hj hi2
      rw [walkStar_append_copy (c := c) w p i (fun j hj => h_nonone j (Nat.le_of_lt (h_lt_n j hj)))]
      cases h_eq : walkStar (some w) p i
      · exact (h_nonone_i h_eq).elim
      · rename_i v
        simp
    have h_depth : ∀ i ≤ n, depthStar (walkStar (some (w ++ [c])) p i) ≤ K + 1 := by
      intro i hi
      have h_nonone_i : walkStar (some w) p i ≠ none := h_nonone i hi
      have h_lt_n : ∀ j < i, j < n := fun j hj => Nat.lt_of_lt_of_le hj hi
      rw [walkStar_append_copy (c := c) w p i (fun j hj => h_nonone j (Nat.le_of_lt (h_lt_n j hj)))]
      have h_depth_i := hdepth i hi
      cases h_eq : walkStar (some w) p i
      · exact (h_nonone_i h_eq).elim
      · rename_i v
        rw [h_eq] at h_depth_i
        simp [depthStar] at h_depth_i ⊢
        exact h_depth_i
    exact ⟨n, hR, h_no_return, h_depth⟩
  · -- reverse direction: segVis → visitsK
    intro h
    rcases h with ⟨n, hn, h_ret, hdepth⟩
    have h_nonone : ∀ i ≤ n, walkStar (some w) p i ≠ none := by
      by_contra h_exists
      push Not at h_exists
      obtain ⟨i, hi, hnone⟩ := h_exists
      have h_exists' : ∃ m, walkStar (some w) p m = none := ⟨i, hnone⟩
      let i_min := Nat.find h_exists'
      have hi_min_le : i_min ≤ n := by
        have h_find_le_i : i_min ≤ i := Nat.find_min' h_exists' hnone
        exact Nat.le_trans h_find_le_i hi
      have hi_min_none : walkStar (some w) p i_min = none := Nat.find_spec h_exists'
      by_cases hi_zero : i_min = 0
      · rw [hi_zero] at hi_min_none
        simp [walkStar] at hi_min_none
      · -- i_min ≥ 1
        have hi_min_ge_one : 1 ≤ i_min := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi_zero)
        have h_min : ∀ j < i_min, walkStar (some w) p j ≠ none :=
          fun j hj => Nat.find_min h_exists' hj
        have h_append := walkStar_append_copy (c := c) w p i_min (fun j hj => h_min j hj)
        rw [hi_min_none] at h_append
        simp at h_append
        by_cases hi_lt_n : i_min < n
        · have h_ret_i := h_ret i_min hi_min_ge_one hi_lt_n
          rw [h_append] at h_ret_i
          exact h_ret_i rfl
        · -- i_min = n
          have hi_eq_n : i_min = n := Nat.le_antisymm hi_min_le (not_lt.mp hi_lt_n)
          subst hi_eq_n
          rw [h_append] at hn
          have h_empty_eq : [] = w' ++ [c] := Option.some_inj.mp hn
          have h_nonempty : w' ++ [c] ≠ [] := by
            simp
          exact h_nonempty h_empty_eq.symm
    have h_walk_n : walkStar (some w) p n = some w' := by
      have h_append := walkStar_append_copy (c := c) w p n (fun j hj => h_nonone j (Nat.le_of_lt hj))
      rw [h_append] at hn
      have h_nonone_n : walkStar (some w) p n ≠ none := h_nonone n (le_refl n)
      cases h_eq_n : walkStar (some w) p n
      · exact (h_nonone_n h_eq_n).elim
      · rename_i v
        have h_match : some (v ++ [c]) = some (w' ++ [c]) := by
          simpa [h_eq_n] using hn
        have h_append_eq : v ++ [c] = w' ++ [c] := Option.some_inj.mp h_match
        have h_v_eq_w' : v = w' := List.append_cancel_right h_append_eq
        simp [h_v_eq_w']
    have h_depth : ∀ i ≤ n, depthStar (walkStar (some w) p i) ≤ K := by
      intro i hi
      have h_nonone_i : walkStar (some w) p i ≠ none := h_nonone i hi
      have h_lt_n : ∀ j < i, j < n := fun j hj => Nat.lt_of_lt_of_le hj hi
      have h_append := walkStar_append_copy (c := c) w p i (fun j hj => h_nonone j (Nat.le_of_lt (h_lt_n j hj)))
      have h_depth_i := hdepth i hi
      cases h_eq : walkStar (some w) p i
      · exact (h_nonone_i h_eq).elim
      · rename_i v
        rw [h_eq] at h_append
        rw [h_append] at h_depth_i
        simp [depthStar] at h_depth_i ⊢
        exact h_depth_i
    exact ⟨n, h_walk_n, h_depth⟩

/-- The frozen frogs of the copy are the returns to `r` within depth `K + 1`. -/
theorem visitsK_copy_none_iff {d : ℕ} (K : ℕ) (c : Fin d) (w : Vertex d) (p : ℕ → Step d) :
    visitsK K (some w) p none ↔ retK (K + 1) (some (w ++ [c])) p := by
  classical
  have hdep : ∀ i, (∀ j < i, walkStar (some w) p j ≠ none) → ∀ v,
      walkStar (some w) p i = some v →
      depthStar (walkStar (some (w ++ [c])) p i) = depthStar (walkStar (some w) p i) + 1 := by
    intro i hi v hv
    rw [walkStar_append_copy (c := c) w p i hi, hv]
    simp [depthStar]
  constructor
  · rintro ⟨n, hn, hd⟩
    have hex : ∃ n, walkStar (some w) p n = none := ⟨n, hn⟩
    set n0 := Nat.find hex with hn0def
    have hn0 : walkStar (some w) p n0 = none := Nat.find_spec hex
    have hmin : ∀ j < n0, walkStar (some w) p j ≠ none := fun j hj => Nat.find_min hex hj
    have hle : n0 ≤ n := Nat.find_min' hex hn
    have hpos : 1 ≤ n0 := by
      rcases Nat.eq_zero_or_pos n0 with h0 | h0
      · rw [h0] at hn0; simp [walkStar] at hn0
      · exact h0
    refine ⟨n0, hpos, ?_, ?_⟩
    · rw [walkStar_append_copy (c := c) w p n0 hmin, hn0]
    · intro i hi
      rcases Nat.lt_or_ge i n0 with hlt | hge
      · have hi' : ∀ j < i, walkStar (some w) p j ≠ none := fun j hj => hmin j (by omega)
        cases hv : walkStar (some w) p i with
        | none => exact absurd hv (hmin i hlt)
        | some v =>
          rw [hdep i hi' v hv]
          have := hd i (by omega)
          omega
      · have hieq : i = n0 := by omega
        subst hieq
        rw [walkStar_append_copy (c := c) w p _ hmin, hn0]
        simp [depthStar]
  · rintro ⟨m, hm1, hm, hd⟩
    have hex : ∃ n, walkStar (some w) p n = none := by
      by_contra H
      push_neg at H
      have h := walkStar_append_copy (c := c) w p m (fun j _ => H j)
      cases hv : walkStar (some w) p m with
      | none => exact H m hv
      | some v =>
        rw [hv, hm] at h
        simp at h
    set n0 := Nat.find hex with hn0def
    have hn0 : walkStar (some w) p n0 = none := Nat.find_spec hex
    have hmin : ∀ j < n0, walkStar (some w) p j ≠ none := fun j hj => Nat.find_min hex hj
    have hle : n0 ≤ m := by
      by_contra H
      push_neg at H
      have h := walkStar_append_copy (c := c) w p m (fun j hj => hmin j (by omega))
      cases hv : walkStar (some w) p m with
      | none => exact hmin m H hv
      | some v =>
        rw [hv, hm] at h
        simp at h
    refine ⟨n0, hn0, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i n0 with hlt | hge
    · have hi' : ∀ j < i, walkStar (some w) p j ≠ none := fun j hj => hmin j (by omega)
      cases hv : walkStar (some w) p i with
      | none => exact absurd hv (hmin i hlt)
      | some v =>
        have h1 := hdep i hi' v hv
        have h2 := hd i (by omega)
        rw [hv] at h1
        omega
    · have hieq : i = n0 := by omega
      subst hieq
      rw [hn0]
      simp [depthStar]

/-- From `r`, a first step of direction `c.succ` goes to `[c]`. -/
theorem stepStar_some_root {d : ℕ} (c : Fin d) (p : ℕ → Step d) (hp : (p 0).2 = c.succ) :
    stepStar (some []) (p 0) = some [c] := by
  unfold stepStar
  simp [hp, Fin.pred_succ c, Fin.succ_ne_zero c]

/-- An entry into `c` visits, before its return, what its walk from `[c]` visits. -/
theorem segVis_root_succ_iff {d : ℕ} (K : ℕ) (c : Fin d) (p : ℕ → Step d) (hp : (p 0).2 = c.succ)
    (u : Vertex d) (hu : u ≠ []) :
    segVis (K + 1) (some []) p (some u) ↔ segVis (K + 1) (some [c]) (fun t => p (t + 1)) (some u) := by
  have hstep : stepStar (some []) (p 0) = some [c] := stepStar_some_root c p hp
  have hwalk : ∀ n, walkStar (some []) p (n + 1) = walkStar (some [c]) (fun t => p (t + 1)) n := by
    intro n
    rw [walkStar_succ', hstep]
  have hne_c : some [c] ≠ some ([] : Vertex d) := by
    intro h
    have : [c] = [] := Option.some_inj.mp h
    exact List.cons_ne_nil _ _ this
  constructor
  · -- forward direction
    rintro ⟨n, hn, hret, hdep⟩
    have hnpos : n ≠ 0 := by
      intro hzero
      have : walkStar (some []) p 0 = some u := by simpa [hzero] using hn
      simp [walkStar] at this
      exact hu this
    rcases Nat.exists_eq_succ_of_ne_zero hnpos with ⟨m, hm⟩
    subst hm
    refine ⟨m, ?_, ?_, ?_⟩
    · -- walkStar (some [c]) ... m = some u
      rw [← hwalk m, walkStar]
      exact hn
    · -- return condition
      intro i hi1 hi_lt_m
      have hi1' : 1 ≤ i + 1 := by omega
      have hi_lt_m_succ : i + 1 < m + 1 := by omega
      have h := hret (i + 1) hi1' hi_lt_m_succ
      rw [← hwalk i]
      exact h
    · -- depth condition
      intro i hi_le_m
      have hi_succ_le_m_succ : i + 1 ≤ m + 1 := by omega
      have h := hdep (i + 1) hi_succ_le_m_succ
      rw [← hwalk i]
      exact h
  · -- backward direction
    rintro ⟨n, hn, hret, hdep⟩
    refine ⟨n + 1, ?_, ?_, ?_⟩
    · -- walkStar (some []) p (n + 1) = some u
      rw [hwalk n, hn]
    · -- return condition
      intro i hi1 hi_lt_succ
      rcases Nat.eq_zero_or_pos i with (hzero | hpos)
      · -- i = 0, but hi1 says 1 ≤ 0, contradiction
        subst hzero
        omega
      · -- i ≥ 1
        rcases Nat.exists_eq_add_of_le (Nat.one_le_of_lt hpos) with ⟨k, hk⟩
        subst hk
        have hk_lt_n : k < n := by omega
        rcases Nat.eq_zero_or_pos k with (hkzero | hkpos)
        · -- k = 0
          subst hkzero
          simp [walkStar, hstep, hne_c]
        · -- k ≥ 1
          have hk1 : 1 ≤ k := Nat.one_le_of_lt hkpos
          have h := hret k hk1 hk_lt_n
          rw [add_comm 1 k, hwalk k]
          exact h
    · -- depth condition
      intro i hi_le_succ
      rcases Nat.eq_zero_or_pos i with (hzero | hpos)
      · -- i = 0
        subst hzero
        simp [walkStar, depthStar]
      · -- i ≥ 1
        rcases Nat.exists_eq_add_of_le (Nat.one_le_of_lt hpos) with ⟨k, hk⟩
        subst hk
        have hk_le_n : k ≤ n := by omega
        have h := hdep k hk_le_n
        rw [add_comm 1 k, hwalk k]
        exact h

/-- An entry into `c` returns iff its walk from `[c]` returns. -/
theorem retK_root_succ_iff {d : ℕ} (K : ℕ) (c : Fin d) (p : ℕ → Step d) (hp : (p 0).2 = c.succ) :
    retK (K + 1) (some []) p ↔ retK (K + 1) (some [c]) (fun t => p (t + 1)) := by
  have hdir_ne_zero : (p 0).2 ≠ 0 := by rw [hp]; exact Fin.succ_ne_zero c
  have hstep_root : stepStar (some ([] : Vertex d)) (p 0) = some [c] := by
    dsimp [stepStar]
    by_cases h : (p 0).2 = 0
    · exfalso; exact hdir_ne_zero h
    · simp [hp]
  constructor
  · -- forward direction: retK (K+1) (some []) p → retK (K+1) (some [c]) (fun t => p (t+1))
    intro h
    rcases h with ⟨c0, hc0, hret, hdepth⟩
    -- c0 ≥ 2, because c0 = 1 would mean walkStar (some []) p 1 = some []
    -- but walkStar (some []) p 1 = stepStar (some []) (p 0) = some [c] ≠ some []
    have hc0_ge2 : 2 ≤ c0 := by
      by_contra! hlt
      have hc0_eq1 : c0 = 1 := by omega
      have hwalk1 : walkStar (some []) p 1 = some [] := by simpa [hc0_eq1] using hret
      have hstep1 : walkStar (some []) p 1 = some [c] := by
        rw [show walkStar (some []) p 1 = stepStar (some []) (p 0) by
          simp [walkStar],
          hstep_root]
      have hne : some [c] ≠ some ([] : Vertex d) := by
        intro heq
        have := Option.some_inj.mp heq
        simp at this
      exact hne (hstep1.symm.trans hwalk1)
    have hc0_sub_one : 1 ≤ c0 - 1 := by omega
    refine ⟨c0 - 1, hc0_sub_one, ?_, ?_⟩
    · -- walkStar (some [c]) (fun t => p (t+1)) (c0-1) = some []
      have hwalk_eq : walkStar (some []) p c0 = walkStar (stepStar (some []) (p 0)) (fun i => p (i + 1)) (c0 - 1) := by
        calc
          walkStar (some []) p c0 = walkStar (some []) p ((c0 - 1) + 1) := by
            rw [Nat.sub_add_cancel hc0]
          _ = walkStar (stepStar (some []) (p 0)) (fun i => p (i + 1)) (c0 - 1) := by rw [walkStar_succ']
      rw [hstep_root] at hwalk_eq
      rw [← hwalk_eq, hret]
    · -- depth bound
      intro i hi
      have hi' : i + 1 ≤ c0 := by omega
      have hwalk_eq : walkStar (some []) p (i + 1) = walkStar (some [c]) (fun t => p (t + 1)) i := by
        rw [walkStar_succ', hstep_root]
      rw [← hwalk_eq]
      exact hdepth (i + 1) hi'
  · -- backward direction: retK (K+1) (some [c]) (fun t => p (t+1)) → retK (K+1) (some []) p
    intro h
    rcases h with ⟨c0, hc0, hret, hdepth⟩
    refine ⟨c0 + 1, by omega, ?_, ?_⟩
    · -- walkStar (some []) p (c0+1) = some []
      rw [walkStar_succ', hstep_root]
      exact hret
    · -- depth bound
      intro i hi
      rcases Nat.eq_zero_or_pos i with (rfl | hpos)
      · -- i = 0
        simp [walkStar, depthStar]
      · -- i > 0
        have hi' : i - 1 < c0 + 1 := by omega
        have hwalk_eq : walkStar (some []) p i = walkStar (some [c]) (fun t => p (t + 1)) (i - 1) := by
          calc
            walkStar (some []) p i = walkStar (some []) p ((i - 1) + 1) := by
              rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]
            _ = walkStar (stepStar (some []) (p 0)) (fun t => p (t + 1)) (i - 1) := by rw [walkStar_succ']
            _ = walkStar (some [c]) (fun t => p (t + 1)) (i - 1) := by rw [hstep_root]
        rw [hwalk_eq]
        apply hdepth (i - 1)
        omega

/-- An entry into `c` visits `[c]` at its first step. -/
theorem segVis_root_succ_self {d : ℕ} (K : ℕ) (c : Fin d) (p : ℕ → Step d)
    (hp : (p 0).2 = c.succ) : segVis (K + 1) (some []) p (some [c]) := by
  have hne : (p 0).2 ≠ 0 := by
    rw [hp]
    exact Fin.succ_ne_zero _
  have hne' : c.succ ≠ 0 := Fin.succ_ne_zero _
  have hwalk : walkStar (some []) p 1 = some [c] :=
    calc
      walkStar (some []) p 1 = stepStar (walkStar (some []) p 0) (p 0) := rfl
      _ = stepStar (some []) (p 0) := by simp [walkStar]
      _ = some (c.succ.pred hne' :: []) := by
        unfold stepStar
        simp [hp, hne']
      _ = some (c :: []) := by simp [Fin.pred_succ]
      _ = some [c] := rfl
  refine ⟨1, hwalk, ?_, ?_⟩
  · -- ∀ i, 1 ≤ i → i < 1 → walkStar (some []) p i ≠ some []
    intro i hi1 hi2
    omega
  · -- ∀ i ≤ 1, depthStar (walkStar (some []) p i) ≤ K + 1
    intro i hi
    rcases Nat.eq_zero_or_pos i with (hzero | hpos)
    · subst hzero
      simp [walkStar, depthStar]
    · have : i = 1 := by omega
      subst this
      rw [hwalk]
      simp [depthStar]

/-! ### The subtree closure is the copy -/

/-- The subtree closure of the entries holds the entries, the frog of `[c]` and the frogs of the
copy reached. -/
theorem subClosure_subset_copy {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) (m : ℕ) (e : ℕ → StarSeg d)
    (he : entrySet π c S = e '' {i | i < m}) :
    subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S ⊆
      entrySet π c S ∪ {(Sum.inl [c], 0)} ∪
        {x | ∃ w, w ≠ [] ∧ x = (Sum.inl (w ++ [c]), 0) ∧
          reachedK K (copyZeta π c) (copyXi π c e) (m + 1) w} := by
  set R := entrySet π c S ∪ {(Sum.inl [c], 0)} ∪
    {x | ∃ w, w ≠ [] ∧ x = (Sum.inl (w ++ [c]), 0) ∧
      reachedK K (copyZeta π c) (copyXi π c e) (m + 1) w} with hR
  have h_base : {x | x ∈ S ∧ isRootSeg x ∧ dirSeg π x = c.succ} ⊆ R := by
    intro x hx
    rcases hx with ⟨hxS, hxRoot, hxDir⟩
    refine Set.mem_union_left _ ?_
    refine Set.mem_union_left _ ⟨hxS, hxRoot, hxDir⟩
  have h_closed : ∀ (σ : StarSeg d), σ ∈ R → ∀ (τ : StarSeg d),
      ((starGen (K + 1) σ (π σ) τ) ∧ subSeg c τ) → τ ∈ R := by
    intro σ hσ τ ⟨hstar, hsub⟩
    rcases hsub with ⟨w, hτ⟩
    subst hτ
    rcases hstar with (hret | hvis)
    · -- return case: τ = (σ.1, σ.2 + 1) but also τ = (Sum.inl (w ++ [c]), 0)
      -- This forces 0 = σ.2 + 1, impossible
      rcases hret with ⟨hτ_eq, hretK⟩
      -- hτ_eq : τ = (σ.1, σ.2 + 1), but we already substituted τ = (Sum.inl (w ++ [c]), 0)
      -- So (Sum.inl (w ++ [c]), 0) = (σ.1, σ.2 + 1)
      -- This implies 0 = σ.2 + 1, contradiction
      have h_eq : (Sum.inl (w ++ [c]), 0) = (σ.1, σ.2 + 1) := hτ_eq
      -- Extract the second component
      have h_snd : 0 = σ.2 + 1 := by
        simpa using congrArg (fun x : StarSeg d => x.2) h_eq
      -- This is impossible since σ.2 + 1 ≥ 1
      omega
    · -- visit case: τ = (Sum.inl u, 0) with u ≠ [] and segVis (K+1) (starStart σ) (π σ) (some u)
      rcases hvis with ⟨u, hu_ne, hτ_eq, hsegVis⟩
      have hu_eq : u = w ++ [c] := by
        injection hτ_eq with h
        -- h : Sum.inl u = Sum.inl (w ++ [c])
        -- So u = w ++ [c]
        simpa using h.symm
      subst hu_eq
      by_cases hw_empty : w = []
      · subst hw_empty
        -- τ = (Sum.inl [c], 0)
        refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
        exact Set.mem_singleton _
      · -- w ≠ []
        rw [hR, Set.mem_union, Set.mem_union, Set.mem_setOf_eq] at hσ
        rcases hσ with (hσ_AB | hσ_C)
        · rcases hσ_AB with (hσ_entry | hσ_singleton)
          · -- σ ∈ entrySet π c S
            rcases hσ_entry with ⟨hσS, hσRoot, hσDir⟩
            -- hσRoot : isRootSeg σ, i.e., starStart σ = some []
            have hstarStart : starStart σ = some [] := hσRoot
            have h_segVis' : segVis (K + 1) (some [c]) (fun t => π σ (t + 1)) (some (w ++ [c])) := by
              rw [← FrogModel.Recursion.segVis_root_succ_iff K c (π σ) hσDir (w ++ [c]) ?_]
              · rw [hstarStart] at hsegVis; exact hsegVis
              · intro h; apply hw_empty; simpa using h
            have h_visitsK : visitsK K (some []) (fun t => π σ (t + 1)) (some w) := by
              rw [FrogModel.Recursion.visitsK_copy_iff K c [] w (fun t => π σ (t + 1))]
              simpa using h_segVis'
            have hσ_eq : ∃ i < m, σ = e i := by
              have : σ ∈ entrySet π c S := ⟨hσS, hσRoot, hσDir⟩
              rw [he] at this
              rcases this with ⟨i, hi, hi_eq⟩
              -- hi_eq : e i = σ, so we need σ = e i
              exact ⟨i, hi, hi_eq.symm⟩
            rcases hσ_eq with ⟨i, hi, hi_eq⟩
            subst hi_eq
            -- Now h_visitsK : visitsK K (some []) (fun t => π (e i) (t + 1)) (some w)
            -- And we need: visitsK K (some []) (copyXi π c e (i + 1)) (some w)
            -- Since copyXi π c e (i + 1) = fun t => π (e i) (t + 1)
            have h_visitsK' : visitsK K (some []) (copyXi π c e (i + 1)) (some w) := by
              simpa [copyXi] using h_visitsK
            refine Set.mem_union_right _ ?_
            rw [Set.mem_setOf_eq]
            refine ⟨w, hw_empty, rfl, ?_⟩
            refine Exists.intro (i + 1) ?_
            refine ⟨by omega, w, hw_empty, h_visitsK', Relation.ReflTransGen.refl⟩
          · -- σ = (Sum.inl [c], 0)
            subst hσ_singleton
            have h_visitsK : visitsK K (some []) (π (Sum.inl [c], 0)) (some w) := by
              rw [FrogModel.Recursion.visitsK_copy_iff K c [] w (π (Sum.inl [c], 0))]
              simpa [starStart, frogStart, segStart] using hsegVis
            refine Set.mem_union_right _ ?_
            rw [Set.mem_setOf_eq]
            refine ⟨w, hw_empty, rfl, ?_⟩
            refine Exists.intro 0 ?_
            refine ⟨by omega, w, hw_empty, ?_, Relation.ReflTransGen.refl⟩
            simpa [copyXi] using h_visitsK
        · -- σ ∈ {x | ∃ w, w ≠ [] ∧ x = (Sum.inl (w ++ [c]), 0) ∧ reachedK ... w}
          rcases hσ_C with ⟨w0, hw0_ne, hσ_eq, hreached⟩
          subst hσ_eq
          -- hsegVis : segVis (K+1) (starStart (Sum.inl (w0 ++ [c]), 0)) (π (Sum.inl (w0 ++ [c]), 0)) (some (w ++ [c]))
          -- starStart (Sum.inl (w0 ++ [c]), 0) = some (w0 ++ [c])
          -- We need: visitsK K (some w0) (copyZeta π c w0) (some w)
          -- Using visitsK_copy_iff with w = w0:
          -- visitsK K (some w0) (π (Sum.inl (w0 ++ [c]), 0)) (some w) ↔ segVis (K+1) (some (w0 ++ [c])) (π (Sum.inl (w0 ++ [c]), 0)) (some (w ++ [c]))
          -- But copyZeta π c w0 = π (Sum.inl (w0 ++ [c]), 0)
          have h_visitsK : visitsK K (some w0) (copyZeta π c w0) (some w) := by
            -- First, rewrite copyZeta
            have h_copyZeta : copyZeta π c w0 = π (Sum.inl (w0 ++ [c]), 0) := by
              simp [copyZeta]
            rw [h_copyZeta]
            -- Now apply visitsK_copy_iff
            rw [FrogModel.Recursion.visitsK_copy_iff K c w0 w (π (Sum.inl (w0 ++ [c]), 0))]
            -- Need: segVis (K+1) (some (w0 ++ [c])) (π (Sum.inl (w0 ++ [c]), 0)) (some (w ++ [c]))
            -- But hsegVis has starStart (Sum.inl (w0 ++ [c]), 0) instead of some (w0 ++ [c])
            simpa [starStart, frogStart, segStart] using hsegVis
          by_cases hw_empty' : w = []
          · subst hw_empty'
            refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
            exact Set.mem_singleton _
          · have h_starArc : starArcK K (copyZeta π c) w0 w := ⟨hw_empty', h_visitsK⟩
            rcases hreached with ⟨a, ha, v, hv_ne, hvisits_v, hchain⟩
            have hchain' : Relation.ReflTransGen (starArcK K (copyZeta π c)) v w :=
              Relation.ReflTransGen.tail hchain h_starArc
            refine Set.mem_union_right _ ?_
            rw [Set.mem_setOf_eq]
            refine ⟨w, hw_empty', rfl, ?_⟩
            refine Exists.intro a ?_
            exact ⟨ha, v, hv_ne, hvisits_v, hchain'⟩
  -- Now use the sInter characterization of Stage.closure
  have h_subClosure_eq : subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S =
      FrogModel.Stage.closure (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
        {x | x ∈ S ∧ isRootSeg x ∧ dirSeg π x = c.succ} := rfl
  rw [h_subClosure_eq]
  -- Show that R is in the family of sets
  have hR_mem : R ∈ {T : Set (StarSeg d) | {x | x ∈ S ∧ isRootSeg x ∧ dirSeg π x = c.succ} ⊆ T ∧
      ∀ (σ : StarSeg d), σ ∈ T → ∀ (τ : StarSeg d),
        ((starGen (K + 1) σ (π σ) τ) ∧ subSeg c τ) → τ ∈ T} := by
    refine ⟨h_base, h_closed⟩
  exact Set.sInter_subset_of_mem hR_mem

/-- Forward induction on a reflexive-transitive closure. -/
theorem reflTransGen_forward {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b)
    {P : α → Prop} (hP : P a) (h_step : ∀ {x y}, r x y → P x → P y) : P b := by
  induction h with
  | refl => exact hP
  | tail h1 h2 ih =>
    exact h_step h2 ih

/-- With at least one entry, the frog of `[c]` and the frogs of the copy reached are in the
subtree closure. -/
theorem copy_subset_subClosure {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) (m : ℕ) (hm : 1 ≤ m) (e : ℕ → StarSeg d)
    (he : entrySet π c S = e '' {i | i < m}) :
    entrySet π c S ∪ {(Sum.inl [c], 0)} ∪
        {x | ∃ w, w ≠ [] ∧ x = (Sum.inl (w ++ [c]), 0) ∧
          reachedK K (copyZeta π c) (copyXi π c e) (m + 1) w} ⊆
      subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S := by
  -- First, prove that (Sum.inl [c], 0) is in the subClosure
  have h_mem_singleton : (Sum.inl [c], 0) ∈ subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S := by
    have h0_lt_m : 0 < m := by omega
    have h_entry0 : e 0 ∈ entrySet π c S := by
      rw [he]
      exact ⟨0, h0_lt_m, rfl⟩
    have h_root0 : isRootSeg (e 0) := h_entry0.2.1
    have h_dir0 : dirSeg π (e 0) = c.succ := h_entry0.2.2
    have hp_dir0 : (π (e 0) 0).2 = c.succ := h_dir0
    have h_segvis0 : segVis (K + 1) (some []) (π (e 0)) (some [c]) :=
      FrogModel.Recursion.segVis_root_succ_self K c (π (e 0)) hp_dir0
    have h_segvis0' : segVis (K + 1) (starStart (e 0)) (π (e 0)) (some [c]) := by
      rw [h_root0]
      exact h_segvis0
    have h_starGen0 : starGen (K + 1) (e 0) (π (e 0)) (Sum.inl [c], 0) := by
      refine Or.inr ⟨[c], ?_, rfl, h_segvis0'⟩
      simp
    have h_subSeg0 : subSeg c (Sum.inl [c], 0) := by
      refine ⟨[], ?_⟩
      simp
    have h_arc0 : (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) (e 0) (π (e 0)) (Sum.inl [c], 0) :=
      ⟨h_starGen0, h_subSeg0⟩
    have h_base0 : e 0 ∈ {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ} := h_entry0
    have h_mem0 : e 0 ∈ subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S :=
      (FrogModel.Stage.subset_closure (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
        {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ}) h_base0
    exact FrogModel.Stage.closure_arc (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
      {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ} (e 0) (Sum.inl [c], 0) h_mem0 h_arc0
  intro x hx
  rcases hx with (hx | hx)
  · rcases hx with (hx | hx)
    · -- x ∈ entrySet π c S
      have hx_base : x ∈ {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ} := hx
      exact (FrogModel.Stage.subset_closure
        (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
        {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ}) hx_base
    · -- x ∈ {(Sum.inl [c], 0)}
      have hx_eq : x = (Sum.inl [c], 0) := by simpa using hx
      subst hx_eq
      exact h_mem_singleton
  · -- x ∈ {x | ∃ w, w ≠ [] ∧ x = (Sum.inl (w ++ [c]), 0) ∧ reachedK ...}
    rcases hx with ⟨w, hw_ne, hx_eq, hw_reached⟩
    subst hx_eq
    rcases hw_reached with ⟨a, ha, v, hv_ne, h_visits, h_chain⟩
    let P (u : Vertex d) : Prop := (Sum.inl (u ++ [c]), 0) ∈
      subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S
    have h_base_chain : P v := by
      rcases Nat.eq_zero_or_pos a with (rfl | ha_pos)
      · -- a = 0
        have h_visits0 : visitsK K (some []) (π (Sum.inl [c], 0)) (some v) := by
          simpa [copyXi] using h_visits
        have h_segvis0 : segVis (K + 1) (some [c]) (π (Sum.inl [c], 0)) (some (v ++ [c])) := by
          have := (FrogModel.Recursion.visitsK_copy_iff K c [] v (π (Sum.inl [c], 0))).mp ?_
          · simpa using this
          · simpa using h_visits0
        have h_starGen0 : starGen (K + 1) (Sum.inl [c], 0) (π (Sum.inl [c], 0)) (Sum.inl (v ++ [c]), 0) := by
          refine Or.inr ⟨v ++ [c], ?_, rfl, h_segvis0⟩
          simp
        have h_subSeg0 : subSeg c (Sum.inl (v ++ [c]), 0) := by
          refine ⟨v, rfl⟩
        have h_arc0 : (fun x p y => starGen (K + 1) x p y ∧ subSeg c y)
            (Sum.inl [c], 0) (π (Sum.inl [c], 0)) (Sum.inl (v ++ [c]), 0) :=
          ⟨h_starGen0, h_subSeg0⟩
        exact FrogModel.Stage.closure_arc (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
          {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ} (Sum.inl [c], 0) (Sum.inl (v ++ [c]), 0)
          h_mem_singleton h_arc0
      · -- a = i + 1 for some i
        rcases Nat.exists_eq_succ_of_ne_zero ha_pos.ne' with ⟨i, rfl⟩
        have hi_lt_m : i < m := by omega
        have h_entry_i : e i ∈ entrySet π c S := by
          rw [he]
          exact ⟨i, hi_lt_m, rfl⟩
        have h_root_i : isRootSeg (e i) := h_entry_i.2.1
        have h_dir_i : dirSeg π (e i) = c.succ := h_entry_i.2.2
        have hp_dir_i : (π (e i) 0).2 = c.succ := h_dir_i
        have h_visits_i : visitsK K (some []) (fun t => π (e i) (t + 1)) (some v) := by
          simpa [copyXi] using h_visits
        have h_segvis_i1 : segVis (K + 1) (some [c]) (fun t => π (e i) (t + 1)) (some (v ++ [c])) := by
          have := (FrogModel.Recursion.visitsK_copy_iff K c [] v (fun t => π (e i) (t + 1))).mp ?_
          · simpa using this
          · simpa using h_visits_i
        have h_segvis_i2 : segVis (K + 1) (some []) (π (e i)) (some (v ++ [c])) :=
          (FrogModel.Recursion.segVis_root_succ_iff K c (π (e i)) hp_dir_i (v ++ [c]) (by simp)).mpr
            h_segvis_i1
        have h_segvis_i2' : segVis (K + 1) (starStart (e i)) (π (e i)) (some (v ++ [c])) := by
          rw [h_root_i]
          exact h_segvis_i2
        have h_starGen_i : starGen (K + 1) (e i) (π (e i)) (Sum.inl (v ++ [c]), 0) := by
          refine Or.inr ⟨v ++ [c], ?_, rfl, h_segvis_i2'⟩
          simp
        have h_subSeg_i : subSeg c (Sum.inl (v ++ [c]), 0) := by
          refine ⟨v, rfl⟩
        have h_arc_i : (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) (e i) (π (e i))
            (Sum.inl (v ++ [c]), 0) := ⟨h_starGen_i, h_subSeg_i⟩
        have h_base_i : e i ∈ {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ} := h_entry_i
        have h_mem_i : e i ∈ subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S :=
          (FrogModel.Stage.subset_closure (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
            {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ}) h_base_i
        exact FrogModel.Stage.closure_arc (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
          {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ} (e i) (Sum.inl (v ++ [c]), 0)
          h_mem_i h_arc_i
    have h_step_chain : ∀ (u u' : Vertex d), starArcK K (copyZeta π c) u u' → P u → P u' := by
      intro u u' h_arc hu_mem
      rcases h_arc with ⟨hu'_ne, h_visits_uu'⟩
      have h_visits_uu'_pi : visitsK K (some u) (π (Sum.inl (u ++ [c]), 0)) (some u') := by
        simpa [copyZeta] using h_visits_uu'
      have h_segvis_uu' : segVis (K + 1) (some (u ++ [c])) (π (Sum.inl (u ++ [c]), 0)) (some (u' ++ [c])) := by
        have := (FrogModel.Recursion.visitsK_copy_iff K c u u' (π (Sum.inl (u ++ [c]), 0))).mp ?_
        · simpa using this
        · simpa using h_visits_uu'_pi
      have h_starGen_u : starGen (K + 1) (Sum.inl (u ++ [c]), 0) (π (Sum.inl (u ++ [c]), 0))
          (Sum.inl (u' ++ [c]), 0) := by
        refine Or.inr ⟨u' ++ [c], ?_, rfl, h_segvis_uu'⟩
        simp
      have h_subSeg_u : subSeg c (Sum.inl (u' ++ [c]), 0) := by
        refine ⟨u', rfl⟩
      have h_arc_u : (fun x p y => starGen (K + 1) x p y ∧ subSeg c y)
          (Sum.inl (u ++ [c]), 0) (π (Sum.inl (u ++ [c]), 0)) (Sum.inl (u' ++ [c]), 0) :=
        ⟨h_starGen_u, h_subSeg_u⟩
      exact FrogModel.Stage.closure_arc (fun x p y => starGen (K + 1) x p y ∧ subSeg c y) π
        {x | x ∈ S ∧ isRootSeg x ∧ (dirSeg π) x = c.succ} (Sum.inl (u ++ [c]), 0)
        (Sum.inl (u' ++ [c]), 0) hu_mem h_arc_u
    -- Now apply induction on the chain
    -- Use the forward induction lemma we just proved
    exact reflTransGen_forward h_chain h_base_chain (fun {x y} h => h_step_chain x y h)

/-- The returns of child `c` are the successors of the returning segments of the subtree
closure. -/
theorem starOut_eq_image {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) :
    starOut K π c S = (fun x : StarSeg d => (x.1, x.2 + 1)) ''
      {x | x ∈ subClosure (dirSeg π) (starGen K) π isRootSeg subSeg c S ∧
        retK K (starStart x) (π x)} := by
  ext y
  constructor
  · intro hy
    have hy' : y ∈ outGen (dirSeg π) (starGen K) π isRootSeg subSeg c S := hy
    rcases hy' with ⟨hisRoot, x, hx, hgen⟩
    rcases hgen with (⟨h_eq, hret⟩ | ⟨u, hu_ne, h_eq, hsegvis⟩)
    · refine ⟨x, ⟨hx, hret⟩, ?_⟩
      simpa [h_eq]
    · have hroot : isRootSeg y := hisRoot
      rw [h_eq] at hroot
      unfold isRootSeg starStart segStart frogStart at hroot
      simp at hroot
      have hu_eq_nil : u = [] := by
        simpa using hroot
      exact absurd hu_eq_nil hu_ne
  · intro hy
    rcases hy with ⟨x, ⟨hx, hret⟩, rfl⟩
    refine ⟨?_, x, hx, ?_⟩
    · unfold isRootSeg starStart segStart
      simp
    · unfold starGen
      left
      exact ⟨rfl, hret⟩

/-- Without entries into `c`, child `c` returns nothing. -/
theorem starOut_eq_empty {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) (h : entrySet π c S = ∅) : starOut K π c S = ∅ := by
  unfold starOut outGen subClosure
  unfold entrySet at h
  rw [h]
  -- Goal: {y | isRootSeg y ∧ ∃ x ∈ Stage.closure ... π ∅, starGen K x (π x) y} = ∅
  -- First show Stage.closure ... π ∅ = ∅
  have h_closure_empty : (FrogModel.Stage.closure (fun (x : StarSeg d) (p : ℕ → Step d) (y : StarSeg d) =>
    starGen K x p y ∧ subSeg c y) π (∅ : Set (StarSeg d))) = ∅ := by
    rw [← Set.subset_empty_iff]
    -- The closure is ⋂₀ of sets containing ∅; ∅ itself qualifies, so ⋂₀ ... ⊆ ∅
    apply Set.sInter_subset_of_mem
    refine ⟨Set.empty_subset _, ?_⟩
    intro σ hσ
    exfalso; simp at hσ
  rw [h_closure_empty]
  simp

/-- **The returns of child `c` are the curve of the copy.** -/
theorem encard_starOut {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) (m : ℕ) (hm : 1 ≤ m) (e : ℕ → StarSeg d)
    (he : entrySet π c S = e '' {i | i < m}) (heinj : Set.InjOn e {i | i < m}) :
    (starOut (K + 1) π c S).encard = curveK K (copyZeta π c) (copyXi π c e) (m + 1) := by
  classical
  set A := entrySet π c S with hA
  set x0 : StarSeg d := (Sum.inl [c], 0) with hx0
  set B : Set (StarSeg d) := {x | ∃ w, w ≠ [] ∧ x = (Sum.inl (w ++ [c]), 0) ∧
    reachedK K (copyZeta π c) (copyXi π c e) (m + 1) w} with hB
  set R : StarSeg d → Prop := fun x => retK (K + 1) (starStart x) (π x) with hR
  have hCeq : subClosure (dirSeg π) (starGen (K + 1)) π isRootSeg subSeg c S = A ∪ {x0} ∪ B :=
    Set.Subset.antisymm (subClosure_subset_copy K π c S m e he)
      (copy_subset_subClosure K π c S m hm e he)
  -- the returns are the successors of the returning segments of the closure
  have h1 : (starOut (K + 1) π c S).encard = {x | x ∈ A ∪ {x0} ∪ B ∧ R x}.encard := by
    rw [starOut_eq_image, hCeq]
    refine Set.InjOn.encard_image ?_
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  -- roots
  have hAroot : ∀ x ∈ A, isRootSeg x := fun x hx => hx.2.1
  have hx0root : ¬ isRootSeg x0 := by
    simp [isRootSeg, starStart, segStart, frogStart, x0]
  have hBroot : ∀ x ∈ B, ¬ isRootSeg x := by
    rintro x ⟨w, -, rfl, -⟩ h
    simp [isRootSeg, starStart, segStart, frogStart] at h
  have hx0B : x0 ∉ B := by
    rintro ⟨w, hw, h, -⟩
    simp only [x0, Prod.mk.injEq, Sum.inl.injEq, and_true] at h
    have := congrArg List.length h
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    exact hw (List.length_eq_zero_iff.1 (by omega))
  have hsplit : {x | x ∈ A ∪ {x0} ∪ B ∧ R x} =
      ({x | x ∈ A ∧ R x} ∪ {x | x = x0 ∧ R x}) ∪ {x | x ∈ B ∧ R x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    tauto
  have hd1 : Disjoint {x | x ∈ A ∧ R x} {x | x = x0 ∧ R x} := by
    rw [Set.disjoint_left]
    rintro x ⟨hx, -⟩ ⟨rfl, -⟩
    exact hx0root (hAroot _ hx)
  have hd2 : Disjoint ({x | x ∈ A ∧ R x} ∪ {x | x = x0 ∧ R x}) {x | x ∈ B ∧ R x} := by
    rw [Set.disjoint_left]
    rintro x (⟨hx, -⟩ | ⟨rfl, -⟩) ⟨hxB, -⟩
    · exact hBroot x hxB (hAroot x hx)
    · exact hx0B hxB
  rw [h1, hsplit, Set.encard_union_eq hd2, Set.encard_union_eq hd1]
  -- the curve of the copy
  unfold curveK
  rw [add_comm (Set.encard {x | x ∈ A ∧ R x})]
  congr 1
  · -- active frogs of the copy: the frog of `[c]` and the entries
    have hP0 : visitsK K (some []) (copyXi π c e 0) none ↔ R x0 := by
      simp only [copyXi, hR, x0]
      exact visitsK_copy_none_iff K c [] (π (Sum.inl [c], 0))
    have hPs : ∀ i < m, (visitsK K (some []) (copyXi π c e (i + 1)) none ↔ R (e i)) := by
      intro i hi
      have hei : e i ∈ A := by rw [he]; exact ⟨i, hi, rfl⟩
      have hroot : starStart (e i) = some [] := hei.2.1
      have hdir : (π (e i) 0).2 = c.succ := hei.2.2
      simp only [copyXi, hR, hroot]
      rw [visitsK_copy_none_iff K c [] (fun t => π (e i) (t + 1))]
      exact (retK_root_succ_iff K c (π (e i)) hdir).symm
    have hsets : {a | a < m + 1 ∧ visitsK K (some []) (copyXi π c e a) none} =
        {a | a = 0 ∧ R x0} ∪ Nat.succ '' {i | i < m ∧ R (e i)} := by
      ext a
      rcases a with _ | i
      · simp [hP0]
      · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Nat.succ_ne_zero, false_and,
          false_or, Nat.succ.injEq, exists_eq_right]
        constructor
        · rintro ⟨hi, hv⟩
          exact ⟨by omega, (hPs i (by omega)).1 hv⟩
        · rintro ⟨hi, hr⟩
          exact ⟨by omega, (hPs i hi).2 hr⟩
    have hdisj : Disjoint {a | a = 0 ∧ R x0} (Nat.succ '' {i | i < m ∧ R (e i)}) := by
      rw [Set.disjoint_left]
      rintro a ⟨rfl, -⟩ ⟨i, -, h⟩
      exact Nat.succ_ne_zero i h
    rw [hsets, Set.encard_union_eq hdisj, Set.InjOn.encard_image (Nat.succ_injective.injOn)]
    congr 1
    · by_cases h : R x0
      · have e1 : {a : ℕ | a = 0 ∧ R x0} = {0} := by ext a; simp [h]
        have e2 : {x | x = x0 ∧ R x} = {x0} := by ext x; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]; constructor; exact fun h' => h'.1; rintro rfl; exact ⟨rfl, h⟩
        rw [e1, e2, Set.encard_singleton, Set.encard_singleton]
      · have e1 : {a : ℕ | a = 0 ∧ R x0} = ∅ := by ext a; simp [h]
        have e2 : {x | x = x0 ∧ R x} = ∅ := by ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; rintro ⟨rfl, h'⟩; exact h h'
        rw [e1, e2, Set.encard_empty, Set.encard_empty]
    · have : {x | x ∈ A ∧ R x} = e '' {i | i < m ∧ R (e i)} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_image]
        rw [he]
        constructor
        · rintro ⟨⟨i, hi, rfl⟩, hr⟩
          exact ⟨i, ⟨hi, hr⟩, rfl⟩
        · rintro ⟨i, ⟨hi, hr⟩, rfl⟩
          exact ⟨⟨i, hi, rfl⟩, hr⟩
      rw [this, Set.InjOn.encard_image (heinj.mono fun i hi => hi.1)]
  · -- the reached frogs of the copy
    have hreach : ∀ w, reachedK K (copyZeta π c) (copyXi π c e) (m + 1) w → w ≠ [] := by
      rintro w ⟨a, -, v, hv, -, hvw⟩
      rcases Relation.ReflTransGen.cases_tail hvw with rfl | ⟨_, -, h⟩
      · exact hv
      · exact h.1
    have : {x | x ∈ B ∧ R x} = (fun w : Vertex d => ((Sum.inl (w ++ [c]), 0) : StarSeg d)) ''
        {w | reachedK K (copyZeta π c) (copyXi π c e) (m + 1) w ∧
          visitsK K (some w) (copyZeta π c w) none} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_image, hB, hR]
      constructor
      · rintro ⟨⟨w, -, rfl, hw⟩, hr⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        rw [visitsK_copy_none_iff K c w]
        simpa [starStart, segStart, frogStart, copyZeta] using hr
      · rintro ⟨w, ⟨hw, hv⟩, rfl⟩
        refine ⟨⟨w, hreach w hw, rfl, hw⟩, ?_⟩
        rw [visitsK_copy_none_iff K c w] at hv
        simpa [starStart, segStart, frogStart, copyZeta] using hv
    rw [this, Set.InjOn.encard_image]
    intro w _ w' _ h
    simp only [Prod.mk.injEq, Sum.inl.injEq, and_true] at h
    exact List.append_cancel_right h

end FrogModel.Recursion
