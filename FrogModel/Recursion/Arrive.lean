module

public import FrogModel.Recursion.Closure
public import FrogModel.Recursion.Glue
public import FrogModel.LemmaX.Kill

@[expose] public section

/-!
# The curve of `T*` counted by the root arrivals (Lemma 4.3 of the paper)

The pieces `π : StarSeg d → ℕ → Step d` index the segments: `(Sum.inl v, s)` is segment `s` of
the sleeping frog at `v`, `(Sum.inr a, s)` segment `s` of the initial frog `a` (at `r`). The
glued sample `(glueZeta π, glueXi π)` (Glue.lean) gives every frog its segments.

- `starGen K x p y`: segment `x` with piece `p` generates `y`: its successor `(x.1, x.2 + 1)` if
  it returns to `r` within depth `K` (`retK`), or the segment `0` of the frog of a vertex
  `u ≠ []` it visits before its return (`segVis`).
- `actSet K π j`: the active segments, the closure of the initial segments `(inr a, 0)`,
  `a < j`.
- Root segments start at `r`; the segments of subtree `c` are the segments `0` of the frogs at
  `w ++ [c]`. `starOut K π c S` (`outGen`, Closure.lean): the returns of child `c`.
- `curveK_eq_arrSet`: `curveK K (glueZeta π) (glueXi π) j` is the number of arrivals of
  `arrSet starInit (dirSeg π) (starOut K π) j` (Process.lean) of direction `0`.
-/

open MeasureTheory FrogModel.LemmaX

namespace FrogModel.Recursion

/-- The segments of the frogs of `T*`: `(Sum.inl v, s)` for the sleeping frog at `v`,
`(Sum.inr a, s)` for the initial frog `a`. -/
abbrev StarSeg (d : ℕ) := (Vertex d ⊕ ℕ) × ℕ

/-- The start of a frog. -/
def frogStart {d : ℕ} : Vertex d ⊕ ℕ → Option (Vertex d)
  | Sum.inl v => some v
  | Sum.inr _ => some []

/-- The start of a segment. -/
def starStart {d : ℕ} (x : StarSeg d) : Option (Vertex d) := segStart (frogStart x.1) x.2

/-- Root segments start at `r`. -/
def isRootSeg {d : ℕ} (x : StarSeg d) : Prop := starStart x = some []

/-- The segments of subtree `c`: the segments `0` of the frogs at `w ++ [c]`. -/
def subSeg {d : ℕ} (c : Fin d) (x : StarSeg d) : Prop := ∃ w : Vertex d, x = (Sum.inl (w ++ [c]), 0)

/-- The direction of the first step of a segment. -/
def dirSeg {d : ℕ} (π : StarSeg d → ℕ → Step d) (x : StarSeg d) : Fin (d + 1) := (π x 0).2

/-- The initial segments. -/
def starInit {d : ℕ} (a : ℕ) : StarSeg d := (Sum.inr a, 0)

/-- Segment `x` with piece `p` generates `y` at kill depth `K`. -/
def starGen {d : ℕ} (K : ℕ) (x : StarSeg d) (p : ℕ → Step d) (y : StarSeg d) : Prop :=
  (y = (x.1, x.2 + 1) ∧ retK K (starStart x) p) ∨
    ∃ u : Vertex d, u ≠ [] ∧ y = (Sum.inl u, 0) ∧ segVis K (starStart x) p (some u)

/-- The pieces of frog `f`. -/
def starPieces {d : ℕ} (π : StarSeg d → ℕ → Step d) (f : Vertex d ⊕ ℕ) : ℕ × ℕ → Step d :=
  fun p => π (f, p.1) p.2

/-- The glued paths of the sleeping frogs. -/
def glueZeta {d : ℕ} [NeZero d] (π : StarSeg d → ℕ → Step d) : Sample d :=
  fun v => gluePath (some v) (starPieces π (Sum.inl v))

/-- The glued paths of the initial frogs. -/
def glueXi {d : ℕ} [NeZero d] (π : StarSeg d → ℕ → Step d) : ℕ → ℕ → Step d :=
  fun a => gluePath (some []) (starPieces π (Sum.inr a))

/-- The active segments at kill depth `K` with `j` initial frogs. -/
def actSet {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ) : Set (StarSeg d) :=
  FrogModel.Stage.closure (starGen K) π (starInit '' {a | a < j})

/-- The returns of child `c` given the segments `S`. -/
def starOut {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d) (S : Set (StarSeg d)) :
    Set (StarSeg d) :=
  outGen (dirSeg π) (starGen K) π isRootSeg subSeg c S

/-- The active frogs: the initial frogs `a < j` and the reached sleeping frogs. -/
def frogActive {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ) :
    Vertex d ⊕ ℕ → Prop
  | Sum.inl b => reachedK K (glueZeta π) (glueXi π) j b
  | Sum.inr a => a < j

/-- The segments before `s` of frog `f` return within depth `K`. -/
def segAlive {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (f : Vertex d ⊕ ℕ) (s : ℕ) : Prop :=
  ∀ s' < s, retK K (starStart (f, s')) (π (f, s'))

/-! ### Walks on `T*` -/

/-- From the leaf `y` the walk stays there. -/
theorem walkStar_none {d : ℕ} (x : ℕ → Step d) (n : ℕ) : walkStar none x n = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [walkStar, ih]
    rfl

/-- One step, then the rest of the walk from the new vertex. -/
theorem walkStar_succ' {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (n : ℕ) :
    walkStar v x (n + 1) = walkStar (stepStar v (x 0)) (fun i => x (i + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [walkStar, ih, walkStar]

/-- A segment from `r` whose first step goes to `y` never returns. -/
theorem not_retK_of_dir_zero {d : ℕ} (K : ℕ) (p : ℕ → Step d) (h : (p 0).2 = 0) :
    ¬ retK K (some []) p := by
  intro hret
  rcases hret with ⟨c, hc1, hc_eq, hc_depth⟩
  have hstep : stepStar (some []) (p 0) = none := by
    unfold stepStar
    simp [h]
  have hwalk1 : walkStar (some []) p 1 = none := by
    unfold walkStar
    simpa [hstep]
  have hwalk_all : ∀ n, 1 ≤ n → walkStar (some []) p n = none := by
    intro n hn
    refine Nat.le_induction hwalk1 (fun k hk ih => ?_) n hn
    unfold walkStar
    rw [ih]
    rfl
  have hcontra := hwalk_all c hc1
  rw [hcontra] at hc_eq
  simp at hc_eq

/-- A segment from `r` whose first step goes to `y` visits no vertex `some u`, `u ≠ []`. -/
theorem not_segVis_of_dir_zero {d : ℕ} (K : ℕ) (p : ℕ → Step d) (h : (p 0).2 = 0) (u : Vertex d)
    (hu : u ≠ []) : ¬ segVis K (some []) p (some u) := by
  intro hseg
  rcases hseg with ⟨n, hn, hno_ret, hdepth⟩
  by_cases hn0 : n = 0
  · subst hn0
    have hroot : walkStar (some []) p 0 = some ([] : Vertex d) := rfl
    have heq : u = ([] : Vertex d) := Option.some_inj.mp (hn.symm.trans hroot)
    exact hu heq
  · have hpos : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn0)
    have hwalk1 : walkStar (some []) p 1 = none := by
      simp [walkStar, stepStar, h]
    have hwalk : ∀ m, 1 ≤ m → walkStar (some []) p m = none := by
      intro m hm
      induction' m with m ih
      · linarith
      · rw [walkStar]
        by_cases hm0 : m = 0
        · subst hm0
          exact hwalk1
        · have hm1 : 1 ≤ m := Nat.one_le_of_lt (Nat.pos_of_ne_zero hm0)
          rw [ih hm1]
          simp [stepStar]
    rw [hwalk n hpos] at hn
    simp at hn

/-- A segment from a vertex visits `y` before its return iff it starts at `r` with a step to
`y`. -/
theorem segVis_none_iff {d : ℕ} (K : ℕ) (w : Vertex d) (p : ℕ → Step d) :
    segVis K (some w) p none ↔ w = [] ∧ (p 0).2 = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with ⟨n, hn_eq, hn_ret, hn_depth⟩
    have h0 : walkStar (some w) p 0 = some w := rfl
    -- Use Nat.find to get the minimal n with walkStar (some w) p n = none
    let S : Set ℕ := {m | walkStar (some w) p m = none}
    have hS_nonempty : S.Nonempty := ⟨n, hn_eq⟩
    let n0 := Nat.find hS_nonempty
    have hn0_eq : walkStar (some w) p n0 = none := Nat.find_spec hS_nonempty
    have hn0_min : ∀ m, m < n0 → m ∉ S := fun m hm => Nat.find_min hS_nonempty hm
    have hn0_pos : n0 ≠ 0 := by
      intro hzero
      rw [hzero] at hn0_eq
      rw [h0] at hn0_eq
      injection hn0_eq
    rcases Nat.exists_eq_succ_of_ne_zero hn0_pos with ⟨k, hk⟩
    have hk_lt_n0 : k < n0 := by omega
    have hk_not_none : walkStar (some w) p k ≠ none := by
      intro h_eq
      have : k ∈ S := h_eq
      exact hn0_min k hk_lt_n0 this
    rcases (Option.ne_none_iff_exists.mp hk_not_none) with ⟨v, hv⟩
    have hv_symm : walkStar (some w) p k = some v := hv.symm
    -- hn0_eq : walkStar (some w) p n0 = none
    -- hk : n0 = k.succ
    rw [hk] at hn0_eq
    -- hn0_eq : walkStar (some w) p (k.succ) = none
    have h_walk_succ : walkStar (some w) p (k.succ) = stepStar (walkStar (some w) p k) (p k) := rfl
    rw [h_walk_succ] at hn0_eq
    rw [hv_symm] at hn0_eq
    -- hn0_eq : stepStar (some v) (p k) = none
    -- Now analyze stepStar (some v) (p k) = none
    simp [stepStar] at hn0_eq
    split_ifs at hn0_eq with h_eq
    · -- h_eq: (p k).2 = 0
      cases v with
      | nil =>
        -- v = [] and (p k).2 = 0
        by_cases hk0 : k = 0
        · subst hk0
          -- walkStar (some w) p 0 = some w = some []
          -- So some w = some [], hence w = []
          have hw_eq : w = [] := by
            have htmp := h0.symm.trans hv_symm
            -- htmp : some w = some []
            injection htmp
          exact ⟨hw_eq, h_eq⟩
        · have hk_pos : 1 ≤ k := by omega
          have hk_lt_n : k < n := by
            -- n0 ≤ n because n0 = Nat.find ... and n ∈ S
            have hn0_le_n : n0 ≤ n := Nat.find_le (by
              -- Need to provide n ∈ S
              dsimp [S]
              exact hn_eq)
            omega
          have h_contra := hn_ret k hk_pos hk_lt_n
          rw [hv_symm] at h_contra
          -- h_contra : some [] ≠ some []
          exact absurd rfl h_contra
      | cons c w' =>
        -- stepStar (some (c :: w')) (p k) = some w' ≠ none
        -- After simp, hn0_eq becomes some w' = none, contradiction
        simp at hn0_eq
  · intro h
    rcases h with ⟨hw, hp0⟩
    subst hw
    refine ⟨1, ?_, ?_, ?_⟩
    · simp [walkStar, stepStar, hp0]
    · intro i hi1 hi2
      omega
    · intro i hi
      have hi_cases : i = 0 ∨ i = 1 := by omega
      rcases hi_cases with (rfl | rfl)
      · simp [walkStar, depthStar]
      · simp [walkStar, stepStar, depthStar, hp0]

/-- The walk from `w ++ [c]` is the walk from `w` moved below the child `c` of `r`, until the
latter reaches `y` (then the former is at `r`). -/
theorem walkStar_append {d : ℕ} (c : Fin d) (w : Vertex d) (x : ℕ → Step d) (n : ℕ)
    (h : ∀ i < n, walkStar (some w) x i ≠ none) :
    walkStar (some (w ++ [c])) x n =
      match walkStar (some w) x n with
      | none => some []
      | some w' => some (w' ++ [c]) := by
  induction' n with n ih
  · rfl
  · have hn : walkStar (some w) x n ≠ none := h n (Nat.lt_succ_self n)
    rcases Option.ne_none_iff_exists'.mp hn with ⟨w', hw'⟩
    have h_restrict : ∀ i < n, walkStar (some w) x i ≠ none := fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_succ n))
    have hw'_append : walkStar (some (w ++ [c])) x n = some (w' ++ [c]) := by
      simpa [hw'] using ih h_restrict
    unfold walkStar
    rw [hw', hw'_append]
    by_cases hzero : (x n).2 = 0
    · simp [stepStar, hzero]
      cases w'
      · rfl
      · simp
    · simp [stepStar, hzero, List.cons_append]

/-- Before its return, a walk from a vertex `w ++ [c]` stays below the child `c`. -/
theorem walkStar_append_mem {d : ℕ} (c : Fin d) (w : Vertex d) (x : ℕ → Step d) (n : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ n → walkStar (some (w ++ [c])) x i ≠ some []) :
    ∃ w', walkStar (some (w ++ [c])) x n = some (w' ++ [c]) := by
  have h_no_none : ∀ i, i ≤ n → walkStar (some w) x i ≠ none := by
    by_contra! H
    let S : Set ℕ := {i | i ≤ n ∧ walkStar (some w) x i = none}
    have hS : S.Nonempty := H
    let i := Nat.find hS
    have hi_mem : i ∈ S := Nat.find_spec hS
    rcases hi_mem with ⟨hi_le_n, hi_eq_none⟩
    have hi_min : ∀ j, j < i → j ∉ S := fun j hj => Nat.find_min hS hj
    have h_lt_none : ∀ j < i, walkStar (some w) x j ≠ none := by
      intro j hj
      intro heq
      apply hi_min j hj
      have hj_le_n : j ≤ n := Nat.le_trans (Nat.le_of_lt hj) hi_le_n
      exact ⟨hj_le_n, heq⟩
    have hi_pos : 1 ≤ i := by
      by_contra! Hpos
      have hi0 : i = 0 := by omega
      rw [hi0] at hi_eq_none
      simp [walkStar] at hi_eq_none
    have h_append := FrogModel.Recursion.walkStar_append c w x i h_lt_none
    rw [hi_eq_none] at h_append
    have h_contra := h i hi_pos hi_le_n
    rw [h_append] at h_contra
    exact h_contra rfl
  have h_last : walkStar (some w) x n ≠ none := h_no_none n (le_refl n)
  obtain ⟨w', hw'⟩ := (Option.ne_none_iff_exists.mp h_last).imp fun t ht => ht.symm
  have h_lt : ∀ i < n, walkStar (some w) x i ≠ none := by
    intro i hi
    apply h_no_none i (Nat.le_of_lt hi)
  have h_append := FrogModel.Recursion.walkStar_append c w x n h_lt
  rw [hw'] at h_append
  exact ⟨w', h_append⟩

/-! ### The arcs respect the subtrees -/

/-- A root segment of direction `0` generates nothing. -/
theorem starGen_root_zero {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (x y : StarSeg d)
    (hx : isRootSeg x) (h0 : dirSeg π x = 0) : ¬ starGen K x (π x) y := by
  intro h
  rcases h with (⟨hy, hret⟩ | ⟨u, hu_ne, hy, hseg⟩)
  · have hstart : starStart x = some [] := hx
    rw [hstart] at hret
    have h0' : (π x 0).2 = 0 := h0
    exact not_retK_of_dir_zero K (π x) h0' hret
  · have hstart : starStart x = some [] := hx
    rw [hstart] at hseg
    have h0' : (π x 0).2 = 0 := h0
    exact not_segVis_of_dir_zero K (π x) h0' u hu_ne hseg

/-- A root segment of direction `c.succ` generates root segments and segments of subtree `c`. -/
theorem starGen_root_succ {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (x y : StarSeg d) (hx : isRootSeg x) (hc : dirSeg π x = c.succ) (h : starGen K x (π x) y) :
    isRootSeg y ∨ subSeg c y := by
  rcases h with (⟨hy, hret⟩ | ⟨u, hu_ne, hy, hsegvis⟩)
  · -- return case: y = (x.1, x.2 + 1)
    left
    rw [hy]
    unfold isRootSeg starStart segStart
    simp
  · -- wake case: y = (Sum.inl u, 0)
    right
    rw [hy]
    unfold isRootSeg at hx
    -- hx : starStart x = some []
    -- hsegvis : segVis K (starStart x) (π x) (some u)
    rw [hx] at hsegvis
    -- hsegvis : segVis K (some []) (π x) (some u)
    rcases hsegvis with ⟨n, h_walk_n, h_no_return, h_depth⟩
    -- h_walk_n : walkStar (some []) (π x) n = some u
    have hn_pos : n ≠ 0 := by
      intro hzero
      rw [hzero] at h_walk_n
      simp [walkStar] at h_walk_n
      exact hu_ne h_walk_n
    have hn_ge1 : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn_pos)
    rcases Nat.exists_eq_succ_of_ne_zero hn_pos with ⟨m, hm⟩
    rw [hm] at h_walk_n
    -- h_walk_n : walkStar (some []) (π x) (m + 1) = some u
    have h_step : stepStar (some []) (π x 0) = some [c] := by
      unfold stepStar
      have h_dir : (π x 0).2 = c.succ := hc
      have h_ne_zero : c.succ ≠ 0 := Fin.succ_ne_zero _
      simp [h_dir, h_ne_zero, Fin.pred_succ]
    have h_walk_succ : walkStar (some []) (π x) (m + 1) = walkStar (some [c]) (fun i => π x (i + 1)) m := by
      rw [walkStar_succ' (some []) (π x) m, h_step]
    rw [h_walk_succ] at h_walk_n
    -- h_walk_n : walkStar (some [c]) (fun i => π x (i + 1)) m = some u
    have h_no_ret : ∀ i, 1 ≤ i → i ≤ m → walkStar (some [c]) (fun i => π x (i + 1)) i ≠ some [] := by
      intro i hi1 hi_le_m
      have h_not_ret' : walkStar (some []) (π x) (i + 1) ≠ some [] := by
        by_cases hi_succ_lt_n : i + 1 < n
        · exact h_no_return (i + 1) (by omega) hi_succ_lt_n
        · have h_eq : i + 1 = n := by omega
          rw [h_eq]
          -- goal: walkStar (some []) (π x) n ≠ some []
          rw [hm, h_walk_succ]
          -- goal: walkStar (some [c]) (fun i => π x (i + 1)) m ≠ some []
          rw [h_walk_n]
          -- goal: some u ≠ some []
          intro h; apply hu_ne; exact Option.some_inj.mp h
      rw [walkStar_succ' (some []) (π x) i, h_step] at h_not_ret'
      exact h_not_ret'
    rcases walkStar_append_mem c [] (fun i => π x (i + 1)) m h_no_ret with ⟨w', hw'_walk⟩
    -- hw'_walk : walkStar (some ([] ++ [c])) (fun i => π x (i + 1)) m = some (w' ++ [c])
    simp at hw'_walk
    -- hw'_walk : walkStar (some [c]) (fun i => π x (i + 1)) m = some (w' ++ [c])
    rw [hw'_walk] at h_walk_n
    -- h_walk_n : some (w' ++ [c]) = some u
    have hu_eq : w' ++ [c] = u := Option.some_inj.mp h_walk_n
    -- Now we need to show subSeg c (Sum.inl u, 0)
    unfold subSeg
    exact ⟨w', by rw [← hu_eq]⟩

/-- A segment of subtree `c` generates root segments and segments of subtree `c`. -/
theorem starGen_sub {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d) (x y : StarSeg d)
    (hx : subSeg c x) (h : starGen K x (π x) y) : isRootSeg y ∨ subSeg c y := by
  rcases hx with ⟨w, hx_eq⟩
  have hstarStart : starStart x = some (w ++ [c]) := by
    rw [hx_eq]
    rfl
  rcases h with (⟨hy_eq, hret⟩ | ⟨u, hu_ne, hy_eq, hsegvis⟩)
  · -- return case: y = (x.1, x.2 + 1)
    left
    rw [hy_eq, hx_eq]
    unfold isRootSeg starStart segStart frogStart
    simp
  · -- wake case: y = (Sum.inl u, 0) with segVis
    rw [hstarStart] at hsegvis
    rcases hsegvis with ⟨n, hwalk_n, h_no_ret_before, h_depth⟩
    have h_no_ret_at_n : walkStar (some (w ++ [c])) (π x) n ≠ some [] := by
      rw [hwalk_n]
      intro h; apply hu_ne; simpa using h
    have h_no_ret : ∀ i, 1 ≤ i → i ≤ n → walkStar (some (w ++ [c])) (π x) i ≠ some [] := by
      intro i hi1 hi2
      by_cases hi_lt_n : i < n
      · exact h_no_ret_before i hi1 hi_lt_n
      · have hi_eq_n : i = n := by omega
        subst hi_eq_n
        exact h_no_ret_at_n
    have hmem := FrogModel.Recursion.walkStar_append_mem c w (π x) n h_no_ret
    rcases hmem with ⟨w', hwalk_n'⟩
    right
    rw [hy_eq]
    refine ⟨w', ?_⟩
    have h_eq : some u = some (w' ++ [c]) := by
      rw [← hwalk_n, hwalk_n']
    simpa using h_eq

/-- A root segment has at most one generator, the previous segment of its frog. -/
theorem starGen_pred {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (x x' y : StarSeg d)
    (hy : isRootSeg y) (h : starGen K x (π x) y) (h' : starGen K x' (π x') y) : x = x' := by
  rcases h with (⟨hy_eq, hret⟩ | ⟨u, hu_ne, hy_eq, hseg⟩)
  · -- y = (x.1, x.2 + 1) and retK K (starStart x) (π x)
    rcases h' with (⟨hy_eq', hret'⟩ | ⟨u', hu'_ne, hy_eq', hseg'⟩)
    · -- both in the return case: y = (x.1, x.2 + 1) = (x'.1, x'.2 + 1)
      have h_eq : (x.1, x.2 + 1) = (x'.1, x'.2 + 1) := by
        calc
          (x.1, x.2 + 1) = y := by symm; exact hy_eq
          _ = (x'.1, x'.2 + 1) := hy_eq'
      have h1 : x.1 = x'.1 := (Prod.mk.inj h_eq).1
      have h2 : x.2 = x'.2 := by
        have := (Prod.mk.inj h_eq).2
        omega
      exact Prod.ext h1 h2
    · -- h' is in the wake case: impossible because y is a root segment
      have hy_root : starStart y = some [] := hy
      rw [hy_eq'] at hy_root
      have h_start : starStart (Sum.inl u', 0) = some u' := by
        simp [starStart, segStart, frogStart]
      rw [h_start] at hy_root
      have : u' = [] := Option.some_inj.mp hy_root
      exact absurd this hu'_ne
  · -- h is in the wake case: impossible because y is a root segment
    have hy_root : starStart y = some [] := hy
    rw [hy_eq] at hy_root
    have h_start : starStart (Sum.inl u, 0) = some u := by
      simp [starStart, segStart, frogStart]
    rw [h_start] at hy_root
    have : u = [] := Option.some_inj.mp hy_root
    exact absurd this hu_ne

/-- No segment generates an initial segment. -/
theorem not_starGen_init {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (x : StarSeg d) (a : ℕ) :
    ¬ starGen K x (π x) (starInit a) := by
  unfold starGen starInit
  intro h
  rcases h with (⟨h_eq, _⟩ | ⟨u, _, h_eq, _⟩)
  · -- h_eq : (x.1, x.2 + 1) = (Sum.inr a, 0)
    have h_snd : x.2 + 1 = 0 := by
      have := congr_arg Prod.snd h_eq
      simpa using this
    omega
  · -- h_eq : (Sum.inl u, 0) = (Sum.inr a, 0)
    have h_fst : Sum.inl u = Sum.inr a := by
      have := congr_arg Prod.fst h_eq
      simpa using this
    injection h_fst

/-- Segments of a subtree are not root segments. -/
theorem not_isRootSeg_of_subSeg {d : ℕ} (c : Fin d) (x : StarSeg d) (h : subSeg c x) :
    ¬ isRootSeg x := by
  rcases h with ⟨w, h⟩
  rw [h]
  have hne : w ++ [c] ≠ [] := List.append_ne_nil_of_right_ne_nil (s := w) (t := [c]) (by simp)
  simp [isRootSeg, starStart, frogStart, segStart, hne]

/-- A segment lies in at most one subtree. -/
theorem subSeg_unique {d : ℕ} (c c' : Fin d) (x : StarSeg d) (h : subSeg c x)
    (h' : subSeg c' x) : c = c' := by
  rcases h with ⟨w, hx⟩
  rcases h' with ⟨w', hx'⟩
  have hx_eq : ((Sum.inl (w ++ [c]) : Vertex d ⊕ ℕ), (0 : ℕ)) = ((Sum.inl (w' ++ [c']) : Vertex d ⊕ ℕ), (0 : ℕ)) := by
    rw [← hx, hx']
  have hsum : (Sum.inl (w ++ [c]) : Vertex d ⊕ ℕ) = (Sum.inl (w' ++ [c']) : Vertex d ⊕ ℕ) := by
    have := congr_arg Prod.fst hx_eq
    simpa using this
  have hlist : w ++ [c] = w' ++ [c'] := by
    injection hsum
  have h_len : ([c] : List (Fin d)).length = ([c'] : List (Fin d)).length := by simp
  have h_tails : [c] = [c'] := List.append_inj_right' hlist h_len
  simpa using h_tails

/-- **The active root segments are the arrivals.** -/
theorem arrSet_star_eq {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ) :
    arrSet starInit (dirSeg π) (starOut K π) j = {x | isRootSeg x} ∩ actSet K π j := by
  have hinitRoot : ∀ a, isRootSeg (d := d) (starInit a) := by
    intro a
    unfold isRootSeg starInit starStart segStart frogStart
    simp
  have hsubRoot : ∀ (c : Fin d) (x : StarSeg d), subSeg (d := d) c x → ¬ isRootSeg (d := d) x :=
    not_isRootSeg_of_subSeg (d := d)
  have hroot0 : ∀ (x y : StarSeg d), isRootSeg (d := d) x → dirSeg π x = 0 → ¬ starGen K x (π x) y :=
    starGen_root_zero (d := d) K π
  have hrootc : ∀ (c : Fin d) (x y : StarSeg d), isRootSeg (d := d) x → dirSeg π x = c.succ →
      starGen K x (π x) y → isRootSeg (d := d) y ∨ subSeg (d := d) c y :=
    starGen_root_succ (d := d) K π
  have hsubc : ∀ (c : Fin d) (x y : StarSeg d), subSeg (d := d) c x → starGen K x (π x) y →
      isRootSeg (d := d) y ∨ subSeg (d := d) c y :=
    starGen_sub (d := d) K π
  unfold starOut actSet
  exact arrSet_eq_closure starInit (dirSeg π) (starGen K) π isRootSeg subSeg hinitRoot hsubRoot hroot0 hrootc hsubc j

/-! ### Frogs and segments -/

/-- An active segment belongs to an active frog and all segments before it return. -/
theorem actSet_subset {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ) :
    actSet K π j ⊆ {x | frogActive K π j x.1 ∧ segAlive K π x.1 x.2} := by
  -- Define the target set R
  let R : Set (StarSeg d) := {z | frogActive K π j z.1 ∧ segAlive K π z.1 z.2}
  have h_base : starInit '' {a | a < j} ⊆ R := by
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · dsimp [frogActive]
      exact ha
    · dsimp [segAlive]
      intro s' hs'
      exact absurd hs' (Nat.not_lt_zero _)
  have h_closed : ∀ σ ∈ R, ∀ τ, starGen K σ (π σ) τ → τ ∈ R := by
    intro σ hσ τ hτ
    rcases hσ with ⟨hfrog, hseg⟩
    rcases σ with ⟨f, s⟩
    rcases hτ with (⟨hτ_eq, hret⟩ | ⟨u, hu_ne, hτ_eq, hsegvis⟩)
    · -- return case: τ = (f, s + 1) and retK holds
      subst hτ_eq
      refine ⟨hfrog, ?_⟩
      dsimp [segAlive]
      intro s' hs'
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hs') with (hs'_lt_s | hs'_eq_s)
      · exact hseg s' hs'_lt_s
      · subst hs'_eq_s
        simpa using hret
    · -- wake case: τ = (Sum.inl u, 0) with u ≠ [] and segVis
      subst hτ_eq
      refine ⟨?_, ?_⟩
      · dsimp [frogActive]
        rcases f with (b | a)
        · -- f = Sum.inl b
          have h_reached_b : reachedK K (glueZeta π) (glueXi π) j b := hfrog
          have h_visits : visitsK K (some b) (glueZeta π b) (some u) := by
            have := visitsK_gluePath_of_segVis K (some b) (starPieces π (Sum.inl b)) (some u) s
              (by
                intro s' hs'
                apply hseg s' hs')
              (by
                apply hsegvis)
            simpa [glueZeta, gluePath, starPieces] using this
          have h_starArc : starArcK K (glueZeta π) b u := by
            dsimp [starArcK]
            exact ⟨hu_ne, h_visits⟩
          rcases h_reached_b with ⟨a', ha', v, hv_ne, hv_visits, hv_chain⟩
          refine ⟨a', ha', v, hv_ne, hv_visits, ?_⟩
          exact Relation.ReflTransGen.tail hv_chain h_starArc
        · -- f = Sum.inr a
          have h_visits : visitsK K (some []) (glueXi π a) (some u) := by
            have := visitsK_gluePath_of_segVis K (some []) (starPieces π (Sum.inr a)) (some u) s
              (by
                intro s' hs'
                apply hseg s' hs')
              (by
                apply hsegvis)
            simpa [glueXi, gluePath, starPieces] using this
          have ha_lt_j : a < j := by
            simpa [frogActive] using hfrog
          refine ⟨a, ha_lt_j, u, hu_ne, h_visits, Relation.ReflTransGen.refl⟩
      · dsimp [segAlive]
        intro s' hs'
        exact absurd hs' (Nat.not_lt_zero _)
  have hR_family : R ∈ {S | starInit '' {a | a < j} ⊆ S ∧ ∀ σ ∈ S, ∀ τ, starGen K σ (π σ) τ → τ ∈ S} := by
    exact ⟨h_base, h_closed⟩
  intro x hx
  have hx_mem : x ∈ ⋂₀ {S | starInit '' {a | a < j} ⊆ S ∧ ∀ σ ∈ S, ∀ τ, starGen K σ (π σ) τ → τ ∈ S} := by
    simpa [actSet, FrogModel.Stage.closure] using hx
  exact Set.sInter_subset_of_mem hR_family hx_mem

/-- From the active segment `0` of a frog, its live segments are active. -/
theorem mem_actSet_of_alive {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ)
    (f : Vertex d ⊕ ℕ) (h0 : (f, 0) ∈ actSet K π j) (s : ℕ) (hs : segAlive K π f s) :
    (f, s) ∈ actSet K π j := by
  induction' s with s ih
  · exact h0
  · have hret : retK K (starStart (f, s)) (π (f, s)) :=
      hs s (Nat.lt_succ_self s)
    have hgen : starGen K (f, s) (π (f, s)) (f, s + 1) := by
      left
      exact ⟨rfl, hret⟩
    have hseg : segAlive K π f s := by
      intro s' hs'
      exact hs s' (Nat.lt_trans hs' (Nat.lt_succ_self s))
    have hmem : (f, s) ∈ actSet K π j := ih hseg
    have hclosure : (f, s + 1) ∈ actSet K π j := by
      intro S hS
      have hmemS : (f, s) ∈ S := hmem S hS
      exact hS.2 (f, s) hmemS (f, s + 1) hgen
    exact hclosure

/-- The segment `0` of an active frog is active. -/
theorem mem_actSet_of_frogActive {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ)
    (f : Vertex d ⊕ ℕ) (hf : frogActive K π j f) : (f, 0) ∈ actSet K π j := by
  cases f with
  | inl b =>
    rcases hf with ⟨a, ha, v, hv_ne, hv_visits, hchain⟩
    -- hv_visits : visitsK K (some []) (glueXi π a) (some v)
    -- hchain : Relation.ReflTransGen (starArcK K (glueZeta π)) v b
    -- First, from hv_visits, get a segment s of the initial frog a that visits v
    have hseg_visits :=
      segVis_of_visitsK_gluePath K (some ([] : Vertex d)) (starPieces π (Sum.inr a)) (some v)
        hv_visits
    rcases hseg_visits with ⟨s, hs_alive, hs_visits⟩
    -- Show that segment 0 of frog a is alive at s
    have h_alive_a : segAlive K π (Sum.inr a) s := by
      intro s' hs'
      exact hs_alive s' hs'
    -- (Sum.inr a, 0) is in the base set
    have hbase_a : (Sum.inr a, 0) ∈ starInit (d := d) '' {a' | a' < j} := by
      refine ⟨a, ha, rfl⟩
    have hmem_a0 : (Sum.inr a, 0) ∈ actSet K π j :=
      FrogModel.Stage.subset_closure (starGen K) π (starInit (d := d) '' {a' | a' < j}) hbase_a
    -- (Sum.inr a, s) is in actSet by mem_actSet_of_alive
    have hmem_as : (Sum.inr a, s) ∈ actSet K π j :=
      mem_actSet_of_alive K π j (Sum.inr a) hmem_a0 s h_alive_a
    -- starGen K (Sum.inr a, s) (π (Sum.inr a, s)) (Sum.inl v, 0)
    have hstar_gen : starGen K (Sum.inr a, s) (π (Sum.inr a, s)) (Sum.inl v, 0) := by
      refine Or.inr ⟨v, hv_ne, rfl, ?_⟩
      exact hs_visits
    -- (Sum.inl v, 0) is in actSet
    have hmem_v0 : (Sum.inl v, 0) ∈ actSet K π j :=
      FrogModel.Stage.closure_arc (starGen K) π (starInit (d := d) '' {a' | a' < j})
        (Sum.inr a, s) (Sum.inl v, 0) hmem_as hstar_gen
    -- Now propagate along the chain from v to b
    induction hchain
    case refl =>
      exact hmem_v0
    case tail w' w hchain' hstep ih =>
      -- w' : intermediate point, w : final point (the original b)
      -- hchain' : Relation.ReflTransGen (starArcK K (glueZeta π)) v w'
      -- hstep : starArcK K (glueZeta π) w' w
      -- ih : (Sum.inl w', 0) ∈ actSet K π j
      rcases hstep with ⟨hw_ne, hw_visits⟩
      -- hw_ne : w ≠ [], hw_visits : visitsK K (some w') (glueZeta π w') (some w)
      have hseg_visits' :=
        segVis_of_visitsK_gluePath K (some w') (starPieces π (Sum.inl w')) (some w)
          hw_visits
      rcases hseg_visits' with ⟨t, ht_alive, ht_visits⟩
      have h_alive_w' : segAlive K π (Sum.inl w') t := by
        intro t' ht'
        exact ht_alive t' ht'
      have hmem_w't : (Sum.inl w', t) ∈ actSet K π j :=
        mem_actSet_of_alive K π j (Sum.inl w') ih t h_alive_w'
      have hstar_gen' : starGen K (Sum.inl w', t) (π (Sum.inl w', t)) (Sum.inl w, 0) := by
        refine Or.inr ⟨w, hw_ne, rfl, ?_⟩
        exact ht_visits
      exact FrogModel.Stage.closure_arc (starGen K) π (starInit (d := d) '' {a' | a' < j})
        (Sum.inl w', t) (Sum.inl w, 0) hmem_w't hstar_gen'
  | inr a =>
    have hbase : (Sum.inr a, 0) ∈ starInit (d := d) '' {a' | a' < j} := by
      refine ⟨a, hf, rfl⟩
    have hmem : (Sum.inr a, 0) ∈ actSet K π j :=
      FrogModel.Stage.subset_closure (starGen K) π (starInit (d := d) '' {a' | a' < j}) hbase
    simpa [actSet] using hmem

/-- The active segments: the live segments of the active frogs. -/
theorem mem_actSet_iff {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ)
    (x : StarSeg d) : x ∈ actSet K π j ↔ frogActive K π j x.1 ∧ segAlive K π x.1 x.2 := by
  exact ⟨fun h => actSet_subset K π j h, fun ⟨hf, hs⟩ =>
    mem_actSet_of_alive K π j x.1 (mem_actSet_of_frogActive K π j x.1 hf) x.2 hs⟩

/-- A glued frog is frozen before it is killed iff one of its live segments is a root segment
of direction `0`. -/
theorem visitsK_none_iff {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d)
    (f : Vertex d ⊕ ℕ) :
    visitsK K (frogStart f) (gluePath (frogStart f) (starPieces π f)) none ↔
      ∃ s, segAlive K π f s ∧ isRootSeg (f, s) ∧ dirSeg π (f, s) = 0 := by
  have h_glue := FrogModel.Recursion.visitsK_gluePath K (frogStart f) (starPieces π f) none
  rw [h_glue]
  constructor
  · rintro ⟨s, h_alive, h_vis⟩
    have h_alive' : segAlive K π f s := by
      intro s' hs'
      have := h_alive s' hs'
      have h1 : segStart (frogStart f) s' = starStart (f, s') := by
        simp [starStart, segStart, frogStart]
      have h2 : segPiece (starPieces π f) s' = π (f, s') := rfl
      rw [h1, h2] at this
      exact this
    have h_vis' : segVis K (starStart (f, s)) (π (f, s)) none := by
      have h1 : segStart (frogStart f) s = starStart (f, s) := by
        simp [starStart, segStart, frogStart]
      have h2 : segPiece (starPieces π f) s = π (f, s) := rfl
      rw [h1, h2] at h_vis
      exact h_vis
    have h_starStart_some : ∃ w : Vertex d, starStart (f, s) = some w := by
      cases f <;> cases s <;> simp [starStart, segStart, frogStart]
    rcases h_starStart_some with ⟨w, hw⟩
    have h_vis'' : segVis K (some w) (π (f, s)) none := by
      rw [← hw]; exact h_vis'
    have h_iff := (FrogModel.Recursion.segVis_none_iff K w (π (f, s))).mp h_vis''
    rcases h_iff with ⟨hw_empty, h_dir⟩
    have h_root : isRootSeg (f, s) := by
      simp [FrogModel.Recursion.isRootSeg, hw, hw_empty]
    have h_dir' : dirSeg π (f, s) = 0 := by
      simp [FrogModel.Recursion.dirSeg, h_dir]
    exact ⟨s, h_alive', h_root, h_dir'⟩
  · rintro ⟨s, h_alive, h_root, h_dir⟩
    have h_alive' : ∀ s' < s, retK K (segStart (frogStart f) s') (segPiece (starPieces π f) s') := by
      intro s' hs'
      have := h_alive s' hs'
      have h1 : segStart (frogStart f) s' = starStart (f, s') := by
        simp [starStart, segStart, frogStart]
      have h2 : segPiece (starPieces π f) s' = π (f, s') := rfl
      rw [h1, h2]
      exact this
    have h_starStart_some : ∃ w : Vertex d, starStart (f, s) = some w := by
      cases f <;> cases s <;> simp [starStart, segStart, frogStart]
    rcases h_starStart_some with ⟨w, hw⟩
    have hw_empty : w = [] := by
      rw [FrogModel.Recursion.isRootSeg] at h_root
      rw [hw] at h_root
      simpa using h_root
    have h_dir' : (π (f, s) 0).2 = 0 := by
      simpa [FrogModel.Recursion.dirSeg] using h_dir
    have h_vis : segVis K (some w) (π (f, s)) none :=
      ((FrogModel.Recursion.segVis_none_iff K w (π (f, s))).mpr ⟨hw_empty, h_dir'⟩)
    have h_vis' : segVis K (starStart (f, s)) (π (f, s)) none := by
      rw [hw]; exact h_vis
    have h_vis'' : segVis K (segStart (frogStart f) s) (segPiece (starPieces π f) s) none := by
      have h1 : segStart (frogStart f) s = starStart (f, s) := by
        simp [starStart, segStart, frogStart]
      have h2 : segPiece (starPieces π f) s = π (f, s) := rfl
      rw [h1, h2]
      exact h_vis'
    exact ⟨s, h_alive', h_vis''⟩

/-- A frog has at most one live root segment of direction `0`. -/
theorem frozen_seg_unique {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (f : Vertex d ⊕ ℕ)
    (s s' : ℕ) (hs : segAlive K π f s) (hs' : segAlive K π f s') (hr : isRootSeg (f, s))
    (h0 : dirSeg π (f, s) = 0) (hr' : isRootSeg (f, s')) (h0' : dirSeg π (f, s') = 0) :
    s = s' := by
  rcases lt_trichotomy s s' with (hlt | heq | hgt)
  · have hret := hs' s hlt
    have hroot : starStart (f, s) = some [] := hr
    have hdir : (π (f, s) 0).2 = 0 := h0
    rw [hroot] at hret
    exact absurd hret (FrogModel.Recursion.not_retK_of_dir_zero K (π (f, s)) hdir)
  · exact heq
  · have hret := hs s' hgt
    have hroot : starStart (f, s') = some [] := hr'
    have hdir : (π (f, s') 0).2 = 0 := h0'
    rw [hroot] at hret
    exact absurd hret (FrogModel.Recursion.not_retK_of_dir_zero K (π (f, s')) hdir)

/-- The curve counts the active frogs that are frozen. -/
theorem curveK_eq_encard_frogs {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ) :
    curveK K (glueZeta π) (glueXi π) j =
      {f | frogActive K π j f ∧
        visitsK K (frogStart f) (gluePath (frogStart f) (starPieces π f)) none}.encard := by
  unfold curveK
  have h_disjoint : Disjoint (Sum.inr '' {a | a < j ∧ visitsK K (some []) (glueXi π a) none})
      (Sum.inl '' {b | reachedK K (glueZeta π) (glueXi π) j b ∧ visitsK K (some b) (glueZeta π b) none}) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases hx1 with ⟨a, ha, rfl⟩
    rcases hx2 with ⟨b, hb, h⟩
    cases h
  have h_image_inr : {a : ℕ | a < j ∧ visitsK K (some []) (glueXi π a) none}.encard =
      ((Sum.inr : ℕ → Vertex d ⊕ ℕ) '' {a | a < j ∧ visitsK K (some []) (glueXi π a) none}).encard := by
    simpa using (Set.InjOn.encard_image (s := {a | a < j ∧ visitsK K (some []) (glueXi π a) none}) Sum.inr_injective.injOn).symm
  have h_image_inl : {b : Vertex d | reachedK K (glueZeta π) (glueXi π) j b ∧ visitsK K (some b) (glueZeta π b) none}.encard =
      ((Sum.inl : Vertex d → Vertex d ⊕ ℕ) '' {b | reachedK K (glueZeta π) (glueXi π) j b ∧ visitsK K (some b) (glueZeta π b) none}).encard := by
    simpa using (Set.InjOn.encard_image (s := {b | reachedK K (glueZeta π) (glueXi π) j b ∧ visitsK K (some b) (glueZeta π b) none}) Sum.inl_injective.injOn).symm
  rw [h_image_inr, h_image_inl, ← Set.encard_union_eq h_disjoint]
  congr 1
  ext f; constructor
  · intro h
    rcases h with (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · refine ⟨ha.1, ?_⟩
      simpa [glueXi, frogStart, starPieces] using ha.2
    · refine ⟨hb.1, ?_⟩
      simpa [glueZeta, frogStart, starPieces] using hb.2
  · intro h
    rcases h with ⟨hfrog, hvis⟩
    cases f with
    | inl b =>
      refine Or.inr ⟨b, ⟨hfrog, ?_⟩, rfl⟩
      simpa [glueZeta, frogStart, starPieces] using hvis
    | inr a =>
      refine Or.inl ⟨a, ⟨hfrog, ?_⟩, rfl⟩
      simpa [glueXi, frogStart, starPieces] using hvis

/-- **The curve of `T*` counts the root arrivals of direction `0`.** -/
theorem curveK_eq_arrSet {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d) (j : ℕ) :
    curveK K (glueZeta π) (glueXi π) j =
      {x | x ∈ arrSet starInit (dirSeg π) (starOut K π) j ∧ dirSeg π x = 0}.encard := by
  rw [curveK_eq_encard_frogs, arrSet_star_eq]
  have hRHS : {x | x ∈ {x | isRootSeg x} ∩ actSet K π j ∧ dirSeg π x = 0} =
      {x | isRootSeg x ∧ x ∈ actSet K π j ∧ dirSeg π x = 0} := by
    ext x; simp [and_assoc]
  rw [hRHS]
  simp only [mem_actSet_iff, and_assoc]
  set S : Set (StarSeg d) := {x | isRootSeg x ∧ frogActive K π j x.1 ∧ segAlive K π x.1 x.2 ∧ dirSeg π x = 0} with hS
  set T : Set (Vertex d ⊕ ℕ) := {f | frogActive K π j f ∧ visitsK K (frogStart f) (gluePath (frogStart f) (starPieces π f)) none} with hT
  have h_image : (Prod.fst '' S) = T := by
    ext f
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨hroot, hfrog, hseg, hdir⟩
      refine ⟨hfrog, ?_⟩
      rw [visitsK_none_iff]
      exact ⟨x.2, hseg, hroot, hdir⟩
    · intro hf
      rcases hf with ⟨hfrog, hvis⟩
      rw [visitsK_none_iff] at hvis
      rcases hvis with ⟨s, hseg, hroot, hdir⟩
      refine ⟨(f, s), ⟨hroot, hfrog, hseg, hdir⟩, rfl⟩
  have h_inj : Set.InjOn Prod.fst S := by
    intro x hx y hy hxy
    rcases hx with ⟨hx_root, hx_act, hx_seg, hx_dir⟩
    rcases hy with ⟨hy_root, hy_act, hy_seg, hy_dir⟩
    have hy_seg' : segAlive K π x.1 y.2 := by simpa [hxy] using hy_seg
    have hy_root' : isRootSeg (x.1, y.2) := by simpa [hxy] using hy_root
    have hy_dir' : dirSeg π (x.1, y.2) = 0 := by simpa [hxy] using hy_dir
    have h_eq_s : x.2 = y.2 :=
      frozen_seg_unique K π x.1 x.2 y.2 hx_seg hy_seg' hx_root hx_dir hy_root' hy_dir'
    ext <;> assumption
  rw [← h_image, Set.InjOn.encard_image h_inj]

end FrogModel.Recursion
