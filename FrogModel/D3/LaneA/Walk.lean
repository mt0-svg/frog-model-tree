module

public import FrogModel.D3.LaneA.Depth

@[expose] public section

/-!
# Walks on `T*` glued at stopping times and copied into subtrees (d = 3)

The pieces of a frog path are glued with `ZeroOne.glueAt`. Before the gluing time the glued walk is
the first walk (`walkStar_glueAt_le`), after it the walk continues from where the first one stopped
(`walkStar_glueAt_add`). The walk from `some (u0 ++ v)` copies the walk from `some u0` below `v`
until the latter exits (`walkStar_append`, `walkStar_glue_copy`), and is at the parent `v.tail` of
`v` at that exit (`walkStar_glue_exit`). A walk whose depth walk reaches `-|u|` reaches the root
`some []` from `some u` (`exists_walkStar_root`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface FrogModel.ZeroOne

/-- The subtree at `w ≠ root` and its parent form a copy of `T*`: before its exit, the walk on
`T*` from `some (v ++ w)` is the image of the walk from `some v` with the same steps. -/
theorem walkStar_append {d : ℕ} (w : Vertex d) (hw : w ≠ []) (v : Vertex d)
    (x : ℕ → Step d) (n : ℕ) (h : ∀ i < n, walkStar (some v) x i ≠ none) :
    walkStar (some (v ++ w)) x n = some (ZeroOne.embedAt w (walkStar (some v) x n)) := by
  induction' n with m ih
  · -- n = 0
    simp [walkStar, ZeroOne.embedAt]
  · -- n = m + 1
    simp [walkStar]
    have h' : ∀ i < m, walkStar (some v) x i ≠ none := fun i hi => h i (by omega)
    rw [ih h']
    -- goal: stepStar (some (ZeroOne.embedAt w (walkStar (some v) x m))) (x m) =
    --   some (ZeroOne.embedAt w (stepStar (walkStar (some v) x m) (x m)))
    -- By hypothesis h, walkStar (some v) x m ≠ none
    have hne : walkStar (some v) x m ≠ none := h m (by omega)
    rcases Option.ne_none_iff_exists'.mp hne with ⟨u, hu⟩
    rw [hu]
    -- goal: stepStar (some (ZeroOne.embedAt w (some u))) (x m) =
    --   some (ZeroOne.embedAt w (stepStar (some u) (x m)))
    simp [ZeroOne.embedAt]
    exact stepStar_embedAt w hw u (x m)
where
  /-- Key lemma: stepStar commutes with embedAt. -/
  stepStar_embedAt (w : Vertex d) (hw : w ≠ []) (u : Vertex d) (ξ : Step d) :
      stepStar (some (u ++ w)) ξ = some (ZeroOne.embedAt w (stepStar (some u) ξ)) := by
    unfold stepStar ZeroOne.embedAt
    by_cases hξ : ξ.2 = 0
    · simp [hξ]
      rcases List.exists_cons_of_ne_nil hw with ⟨c, w', hw_eq⟩
      cases u with
      | nil => simp [hw_eq]
      | cons c' u' => simp
    · simp [hξ]

/-- After the gluing time `e`, the walk driven by the glued sequence continues from its position
at time `e` driven by the second sequence. -/
theorem walkStar_glueAt_add {d : ℕ} (o : Option (Vertex d)) (e : ℕ)
    (a b : ℕ → Step d) (s : ℕ) :
    walkStar o (ZeroOne.glueAt (e : ℕ∞) a b) (e + s) = walkStar (walkStar o a e) b s := by
  induction' s with s ih
  · -- base case s = 0
    have h_prefix : ∀ i < e, ZeroOne.glueAt (e : ℕ∞) a b i = a i := by
      intro i hi
      dsimp [ZeroOne.glueAt]
      have h_lt : (i : ℕ∞) < (e : ℕ∞) := by
        simpa using ENat.natCast_lt_natCast.mpr hi
      simp [h_lt]
    calc
      walkStar o (ZeroOne.glueAt (e : ℕ∞) a b) (e + 0) = walkStar o (ZeroOne.glueAt (e : ℕ∞) a b) e := by simp
      _ = walkStar o a e := by
        rw [ZeroOne.walkStar_prefix o (ZeroOne.glueAt (e : ℕ∞) a b) a e h_prefix]
      _ = walkStar (walkStar o a e) b 0 := rfl
  · -- inductive step: s → s+1
    have h_glue_at_es : ZeroOne.glueAt (e : ℕ∞) a b (e + s) = b s := by
      dsimp [ZeroOne.glueAt]
      split_ifs with h
      · exfalso
        simpa using not_lt.mpr (ENat.natCast_le_natCast.mpr (Nat.le_add_right e s)) h
      · simp
    calc
      walkStar o (ZeroOne.glueAt (e : ℕ∞) a b) (e + (s + 1))
          = walkStar o (ZeroOne.glueAt (e : ℕ∞) a b) ((e + s) + 1) := by rw [add_assoc]
      _ = stepStar (walkStar o (ZeroOne.glueAt (e : ℕ∞) a b) (e + s))
            (ZeroOne.glueAt (e : ℕ∞) a b (e + s)) := rfl
      _ = stepStar (walkStar o (ZeroOne.glueAt (e : ℕ∞) a b) (e + s)) (b s) := by rw [h_glue_at_es]
      _ = stepStar (walkStar (walkStar o a e) b s) (b s) := by rw [ih]
      _ = walkStar (walkStar o a e) b (s + 1) := rfl

theorem glueAt_top {α : Type*} (a b : ℕ → α) : glueAt ⊤ a b = a := by
  funext t
  simp [glueAt]

/-- Before the gluing time, the glued walk is the first walk. -/
theorem walkStar_glueAt_le {d : ℕ} (o : Option (Vertex d)) (e : ℕ∞) (a b : ℕ → Step d) (n : ℕ)
    (hn : (n : ℕ∞) ≤ e) : walkStar o (glueAt e a b) n = walkStar o a n :=
  walkStar_prefix o _ _ n fun i hi => by
    have : (i : ℕ∞) < e := lt_of_lt_of_le (by exact_mod_cast hi) hn
    simp [glueAt, this]

theorem walkStar_none_start {d : ℕ} (x : ℕ → Step d) (n : ℕ) : walkStar none x n = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walkStar, ih, stepStar]

/-- The leaf is absorbing. -/
theorem walkStar_none_of_le {d : ℕ} (o : Option (Vertex d)) (x : ℕ → Step d) {k n : ℕ}
    (hk : walkStar o x k = none) (hkn : k ≤ n) : walkStar o x n = none := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  induction j with
  | zero => simpa using hk
  | succ j ih =>
    rw [← Nat.add_assoc, walkStar, ih (by omega)]
    rfl

/-- The exit time is after every time the walk is not at the leaf. -/
theorem le_exitTime {d : ℕ} (u : Vertex d) (x : ℕ → Step d) (s : ℕ)
    (hs : walkStar (some u) x s ≠ none) : (s : ℕ∞) ≤ exitTime u x := by
  refine le_sInf ?_
  rintro _ ⟨n, hn, rfl⟩
  have hsn : s ≤ n := by
    by_contra hlt
    exact hs (walkStar_none_of_le _ x hn (by omega))
  show (s : ℕ∞) ≤ n
  exact_mod_cast hsn

/-- Before its exit, the walk from `some (u0 ++ v)` on the glued steps copies the walk from
`some u0` below `v`. -/
theorem walkStar_glue_copy {v : Vertex 3} (hv : v ≠ []) (u0 u : Vertex 3) (b c : ℕ → Step 3)
    (s : ℕ) (hs : walkStar (some u0) b s = some u) :
    walkStar (some (u0 ++ v)) (glueAt (exitTime u0 b) b c) s = some (u ++ v) := by
  have hpre : ∀ i < s, walkStar (some u0) b i ≠ none := fun i hi h => by
    rw [walkStar_none_of_le (some u0) b h hi.le] at hs
    cases hs
  rw [walkStar_glueAt_le _ _ _ _ _ (le_exitTime u0 b s (by rw [hs]; simp)),
    walkStar_append v hv u0 b s hpre, hs]
  rfl

/-- At its exit time, the walk from `some (u0 ++ v)` on the glued steps is at `v.tail`, and goes
on with the second sequence. -/
theorem walkStar_glue_exit {v : Vertex 3} (hv : v ≠ []) (u0 : Vertex 3) (b c : ℕ → Step 3)
    (r : ℕ) (hr : exitTime u0 b = r) (s : ℕ) :
    walkStar (some (u0 ++ v)) (glueAt (exitTime u0 b) b c) (r + s) =
      walkStar (some v.tail) c s := by
  obtain ⟨h1, h2⟩ := exitTime_spec u0 b r hr
  rw [hr, walkStar_glueAt_add, walkStar_append v hv u0 b r h2, h1]
  rfl

/-- If the depth walk reaches `-|u|`, the walk from `some u` reaches the root `some []`. -/
theorem exists_walkStar_root (u : Vertex 3) (x : ℕ → Step 3) (h : HitsDown u.length x) :
    ∃ s, walkStar (some u) x s = some [] := by
  classical
  have hex : ∃ s, dW x s ≤ -(u.length : ℤ) := by
    obtain ⟨s, hs⟩ := h
    exact ⟨s, hs.le⟩
  have hs : dW x (Nat.find hex) ≤ -(u.length : ℤ) := Nat.find_spec hex
  have hmin : ∀ i < Nat.find hex, -(u.length : ℤ) < dW x i := fun i hi =>
    not_le.1 (Nat.find_min hex hi)
  have heq : dW x (Nat.find hex) = -(u.length : ℤ) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0] at hs ⊢
      simp only [dW] at hs ⊢
      omega
    · obtain ⟨t, ht⟩ : ∃ t, Nat.find hex = t + 1 := ⟨Nat.find hex - 1, by omega⟩
      have h1 := hmin t (by omega)
      rw [ht] at hs ⊢
      have h2 : dW x (t + 1) = dW x t + inc (x t) := rfl
      rcases inc_cases (x t) with ⟨_, hi⟩ | ⟨_, hi⟩ <;> omega
  refine ⟨Nat.find hex, ?_⟩
  have hnn : walkStar (some u) x (Nat.find hex) ≠ none := by
    rw [ne_eq, walkStar_none_iff]
    rintro ⟨i, hi, hi'⟩
    rcases lt_or_eq_of_le hi with hlt | rfl
    · have := hmin i hlt
      omega
    · omega
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hnn
  have hl := length_walkStar u x _ w hw
  rw [hw]
  have : w.length = 0 := by omega
  rw [List.length_eq_zero_iff.1 this]

end FrogModel.D3.LaneA
