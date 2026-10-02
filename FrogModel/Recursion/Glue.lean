module

public import FrogModel.Pool.Main
public import FrogModel.LemmaX.KillDefs

@[expose] public section

/-!
# One frog of `T*` glued from its segments (Lemma 4.3 of the paper)

A frog of `T*` starting at `v` follows the steps `gluePath v Z`: at time `t`, with `s` returns
to the root `r = some []` at the times `1, ..., t` of its walk and `o` steps since the last one
(or since `0`), it uses the piece value `Z (s, o)`. So segment `s` of the frog (from its `s`-th
return, or from `v` for `s = 0`) is driven by `segPiece Z s = Z (s, ·)` until the next return.
`gluePath` is a reading `Pool.readGen` whose labels `posStar` strictly increase, so for i.i.d.
`Z` the glued steps are i.i.d. (`map_gluePath`).

- `retK K u x`: the walk from `u` returns to `r` at some time `≥ 1`, at depth `≤ K` until then.
- `segVis K u x b`: the walk from `u` visits `b` before its first return at a time `≥ 1`, at
  depth `≤ K` until then.
- `visitsK_gluePath`: the glued frog visits `b` before it is killed at depth `K` iff some
  segment `s` whose earlier segments all return within depth `K` visits `b` (`segVis`).
-/

open MeasureTheory FrogModel.LemmaX

namespace FrogModel.Recursion

/-- The returns to `r` of the walk on `T*` from `v` driven by `x` at the times `1, ..., t`. -/
def returnsStar {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter fun s => walkStar v x s = some []

/-- The position of time `t` in the segments: the number of returns in `[1, t]` and the time
since the last one (or since `0`). -/
def posStar {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (t : ℕ) : ℕ × ℕ :=
  ((returnsStar v x t).card, t - (returnsStar v x t).sup id)

/-- A finite step sequence extended by the step `(0, 0)`. -/
def extendSteps {d : ℕ} [NeZero d] {k : ℕ} (y : Fin k → Step d) : ℕ → Step d :=
  fun i => if h : i < k then y ⟨i, h⟩ else (0, 0)

/-- The label of the step at time `k` after the steps `y`. -/
def selStar {d : ℕ} [NeZero d] (v : Option (Vertex d)) (k : ℕ) (y : Fin k → Step d) : ℕ × ℕ :=
  posStar v (extendSteps y) k

/-- The glued steps of a frog of `T*` starting at `v`, from its pieces `Z`. -/
def gluePath {d : ℕ} [NeZero d] (v : Option (Vertex d)) (Z : ℕ × ℕ → Step d) : ℕ → Step d :=
  fun t => FrogModel.Pool.readGen (fun _ _ i => i) (selStar v) Z (t + 1) (Fin.last t)

/-- The start of segment `s` of a frog starting at `v`. -/
def segStart {d : ℕ} (v : Option (Vertex d)) (s : ℕ) : Option (Vertex d) :=
  if s = 0 then v else some []

/-- The piece of segment `s`. -/
def segPiece {d : ℕ} (Z : ℕ × ℕ → Step d) (s : ℕ) : ℕ → Step d := fun i => Z (s, i)

/-- The walk from `u` returns to `r` at a time `≥ 1`, at depth `≤ K` until then. -/
def retK {d : ℕ} (K : ℕ) (u : Option (Vertex d)) (x : ℕ → Step d) : Prop :=
  ∃ c, 1 ≤ c ∧ walkStar u x c = some [] ∧ ∀ i ≤ c, depthStar (walkStar u x i) ≤ K

/-- The walk from `u` visits `b` before its first return at a time `≥ 1`, at depth `≤ K` until
then. -/
def segVis {d : ℕ} (K : ℕ) (u : Option (Vertex d)) (x : ℕ → Step d) (b : Option (Vertex d)) :
    Prop :=
  ∃ n, walkStar u x n = b ∧ (∀ i, 1 ≤ i → i < n → walkStar u x i ≠ some []) ∧
    ∀ i ≤ n, depthStar (walkStar u x i) ≤ K

/-! ### Positions -/

/-- The walk at time `n` reads only the first `n` steps. -/
theorem walkStar_congr {d : ℕ} (v : Option (Vertex d)) (x y : ℕ → Step d) (n : ℕ)
    (h : ∀ i < n, x i = y i) : walkStar v x n = walkStar v y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold walkStar
    have hn : x n = y n := h n (Nat.lt_succ_self n)
    have hx : ∀ i < n, x i = y i := fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_succ n))
    rw [ih hx, hn]

/-- The position at time `t` reads only the first `t` steps. -/
theorem posStar_congr {d : ℕ} (v : Option (Vertex d)) (x y : ℕ → Step d) (t : ℕ)
    (h : ∀ i < t, x i = y i) : posStar v x t = posStar v y t := by
  have h_returns : returnsStar v x t = returnsStar v y t := by
    unfold returnsStar
    refine Finset.filter_congr (p := fun s => walkStar v x s = some []) (q := fun s => walkStar v y s = some []) ?_
    intro s hs
    have hs_le_t : s ≤ t := (Finset.mem_Icc.mp hs).2
    rcases Nat.lt_or_eq_of_le hs_le_t with (hs_lt | hs_eq)
    · have h' : ∀ i < s, x i = y i := fun i hi => h i (Nat.lt_trans hi hs_lt)
      have h_eq := walkStar_congr v x y s h'
      rw [h_eq]
    · rw [hs_eq]
      have h_eq := walkStar_congr v x y t h
      rw [h_eq]
  unfold posStar
  rw [h_returns]

/-- The position at time `0`. -/
theorem posStar_zero {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) :
    posStar v x 0 = (0, 0) := by
  simp [posStar, returnsStar]

/-- One step: a return starts a new segment, otherwise the offset grows by one. -/
theorem posStar_succ {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (t : ℕ) :
    posStar v x (t + 1) =
      if walkStar v x (t + 1) = some [] then ((posStar v x t).1 + 1, 0)
      else ((posStar v x t).1, (posStar v x t).2 + 1) := by
  unfold posStar returnsStar
  have hle : (1 : ℕ) ≤ Nat.succ t := by omega
  have hIcc : Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
    simpa [add_comm] using (Finset.insert_Icc_right_eq_Icc_succ hle).symm
  rw [hIcc, Finset.filter_insert]
  split_ifs with h
  · let R := (Finset.Icc 1 t).filter fun s => walkStar v x s = some []
    have h_not_mem : t + 1 ∉ R := by
      intro hmem
      rcases Finset.mem_filter.mp hmem with ⟨hmem_Icc, _⟩
      rcases Finset.mem_Icc.mp hmem_Icc with ⟨_, hle'⟩
      omega
    have h_sup_le : R.sup id ≤ t := by
      apply Finset.sup_le
      intro s hs
      rcases Finset.mem_filter.mp hs with ⟨hs_Icc, _⟩
      rcases Finset.mem_Icc.mp hs_Icc with ⟨_, hs_le⟩
      exact hs_le
    have h_card : (insert (t + 1) R).card = R.card + 1 :=
      Finset.card_insert_of_notMem h_not_mem
    have h_sup : (insert (t + 1) R).sup id = t + 1 := by
      rw [Finset.sup_insert, id]
      rw [max_eq_left (by omega : R.sup id ≤ t + 1)]
    rw [h_card, h_sup]
    simp [R]
  · let R := (Finset.Icc 1 t).filter fun s => walkStar v x s = some []
    have h_sup_le : R.sup id ≤ t := by
      apply Finset.sup_le
      intro s hs
      rcases Finset.mem_filter.mp hs with ⟨hs_Icc, _⟩
      rcases Finset.mem_Icc.mp hs_Icc with ⟨_, hs_le⟩
      exact hs_le
    have h_eq : (t + 1) - R.sup id = (t - R.sup id) + 1 := by
      omega
    rw [h_eq]

/-- The returns up to time `a` are among the returns up to a later time. -/
theorem returnsStar_mono {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) {a b : ℕ} (h : a ≤ b) :
    returnsStar v x a ⊆ returnsStar v x b := by
  intro s hs
  rw [returnsStar] at hs ⊢
  rcases Finset.mem_filter.mp hs with ⟨hs_mem, hs_eq⟩
  apply Finset.mem_filter.mpr
  constructor
  · rcases Finset.mem_Icc.mp hs_mem with ⟨h1, h2⟩
    apply Finset.mem_Icc.mpr
    exact ⟨h1, Nat.le_trans h2 h⟩
  · exact hs_eq

/-- The last return up to time `t` is at most `t`. -/
theorem returnsStar_sup_le {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (t : ℕ) :
    (returnsStar v x t).sup id ≤ t := by
  apply Finset.sup_le
  intro s hs
  rw [returnsStar] at hs
  rcases Finset.mem_filter.mp hs with ⟨hs_mem, _⟩
  rcases Finset.mem_Icc.mp hs_mem with ⟨_, h2⟩
  exact h2

/-- The positions of distinct times differ. -/
theorem posStar_injective {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) :
    Function.Injective (posStar v x) := by
  intro t₁ t₂ h
  unfold posStar at h
  have hcard : (returnsStar v x t₁).card = (returnsStar v x t₂).card :=
    congr_arg Prod.fst h
  have hsub_eq : t₁ - (returnsStar v x t₁).sup id = t₂ - (returnsStar v x t₂).sup id :=
    congr_arg Prod.snd h
  by_cases hle : t₁ ≤ t₂
  · have hsub : returnsStar v x t₁ ⊆ returnsStar v x t₂ :=
      returnsStar_mono v x hle
    have h_eq_set : returnsStar v x t₁ = returnsStar v x t₂ :=
      Finset.eq_of_subset_of_card_le hsub (hcard.symm.le)
    have hsup_eq : (returnsStar v x t₁).sup id = (returnsStar v x t₂).sup id := by
      rw [h_eq_set]
    have hsup_le_t₁ : (returnsStar v x t₁).sup id ≤ t₁ := returnsStar_sup_le v x t₁
    have hsup_le_t₂ : (returnsStar v x t₁).sup id ≤ t₂ := by
      rw [hsup_eq]
      exact returnsStar_sup_le v x t₂
    have hsub_eq' : t₁ - (returnsStar v x t₁).sup id = t₂ - (returnsStar v x t₁).sup id := by
      rw [← hsup_eq] at hsub_eq
      exact hsub_eq
    calc
      t₁ = (t₁ - (returnsStar v x t₁).sup id) + (returnsStar v x t₁).sup id := by
        rw [Nat.sub_add_cancel hsup_le_t₁]
      _ = (t₂ - (returnsStar v x t₁).sup id) + (returnsStar v x t₁).sup id := by rw [hsub_eq']
      _ = t₂ := by rw [Nat.sub_add_cancel hsup_le_t₂]
  · have hle' : t₂ ≤ t₁ := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    have hsub : returnsStar v x t₂ ⊆ returnsStar v x t₁ :=
      returnsStar_mono v x hle'
    have h_eq_set : returnsStar v x t₂ = returnsStar v x t₁ :=
      Finset.eq_of_subset_of_card_le hsub (hcard.le)
    have hsup_eq : (returnsStar v x t₁).sup id = (returnsStar v x t₂).sup id := by
      rw [← h_eq_set]
    have hsup_le_t₁ : (returnsStar v x t₁).sup id ≤ t₁ := returnsStar_sup_le v x t₁
    have hsup_le_t₂ : (returnsStar v x t₂).sup id ≤ t₂ := returnsStar_sup_le v x t₂
    calc
      t₁ = (t₁ - (returnsStar v x t₁).sup id) + (returnsStar v x t₁).sup id := by
        rw [Nat.sub_add_cancel hsup_le_t₁]
      _ = (t₂ - (returnsStar v x t₂).sup id) + (returnsStar v x t₁).sup id := by rw [hsub_eq]
      _ = (t₂ - (returnsStar v x t₂).sup id) + (returnsStar v x t₂).sup id := by rw [hsup_eq]
      _ = t₂ := by rw [Nat.sub_add_cancel hsup_le_t₂]

/-- At position `(s, o)` at time `t`, segment `s` started at time `t - o`, at its start, and no
return happened since. -/
theorem posStar_start {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (t : ℕ) :
    (posStar v x t).2 ≤ t ∧
      posStar v x (t - (posStar v x t).2) = ((posStar v x t).1, 0) ∧
      walkStar v x (t - (posStar v x t).2) = segStart v (posStar v x t).1 ∧
      ∀ i, t - (posStar v x t).2 < i → i ≤ t → walkStar v x i ≠ some [] := by
  induction' t with t ih
  · -- t = 0
    rw [posStar_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (0, 0).2 ≤ 0
      simp
    · -- posStar v x (0 - (0, 0).2) = ((0, 0).1, 0)
      simp [posStar_zero]
    · -- walkStar v x (0 - (0, 0).2) = segStart v (0, 0).1
      simp [segStart, walkStar]
    · -- ∀ i, 0 - (0, 0).2 < i → i ≤ 0 → walkStar v x i ≠ some []
      intro i h1 h2
      omega
  · -- t → t+1
    rcases ih with ⟨ih1, ih2, ih3, ih4⟩
    have hpos := posStar_succ v x t
    by_cases hret : walkStar v x (t + 1) = some []
    · -- case: walk returns at t+1
      have hpos' : posStar v x (t + 1) = ((posStar v x t).1 + 1, 0) := by
        rw [hpos, if_pos hret]
      have h1 : (posStar v x (t + 1)).2 ≤ t + 1 := by
        rw [hpos']
        simp
      have h2 : posStar v x ((t + 1) - (posStar v x (t + 1)).2) = ((posStar v x (t + 1)).1, 0) := by
        rw [hpos']
        simp
        exact hpos'
      have h3 : walkStar v x ((t + 1) - (posStar v x (t + 1)).2) = segStart v (posStar v x (t + 1)).1 := by
        rw [hpos']
        simp
        rw [hret, segStart]
        simp
      have h4 : ∀ i, (t + 1) - (posStar v x (t + 1)).2 < i → i ≤ t + 1 → walkStar v x i ≠ some [] := by
        rw [hpos']
        simp
        intro i hlt hle
        omega
      exact ⟨h1, h2, h3, h4⟩
    · -- case: walk does not return at t+1
      have hpos' : posStar v x (t + 1) = ((posStar v x t).1, (posStar v x t).2 + 1) := by
        rw [hpos, if_neg hret]
      have hsub : (t + 1) - (((posStar v x t).1, (posStar v x t).2 + 1).2) = t - (posStar v x t).2 := by
        simp
      have h1 : (posStar v x (t + 1)).2 ≤ t + 1 := by
        rw [hpos']
        simp
        omega
      have h2 : posStar v x ((t + 1) - (posStar v x (t + 1)).2) = ((posStar v x (t + 1)).1, 0) := by
        rw [hpos']
        simp
        -- goal: posStar v x (t - (posStar v x t).2) = ((posStar v x t).1, 0)
        simpa using ih2
      have h3 : walkStar v x ((t + 1) - (posStar v x (t + 1)).2) = segStart v (posStar v x (t + 1)).1 := by
        rw [hpos']
        simp
        -- goal: walkStar v x (t - (posStar v x t).2) = segStart v (posStar v x t).1
        simpa using ih3
      have h4 : ∀ i, (t + 1) - (posStar v x (t + 1)).2 < i → i ≤ t + 1 → walkStar v x i ≠ some [] := by
        rw [hpos']
        simp
        -- goal: ∀ i, t - (posStar v x t).2 < i → i ≤ t+1 → walkStar v x i ≠ some []
        intro i hlt hle
        by_cases hi : i ≤ t
        · exact ih4 i hlt hi
        · have hi' : i = t + 1 := by omega
          subst hi'
          exact hret
      exact ⟨h1, h2, h3, h4⟩

/-- Without a return after the start `T` of segment `s`, time `T + n` has position
`(s, n)`. -/
theorem posStar_add {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) {T s : ℕ} (n : ℕ)
    (hT : posStar v x T = (s, 0)) (hret : ∀ i, T < i → i ≤ T + n → walkStar v x i ≠ some []) :
    posStar v x (T + n) = (s, n) := by
  induction' n with k ih
  · -- n = 0
    simpa using hT
  · -- n = k + 1
    have hret_k : ∀ i, T < i → i ≤ T + k → walkStar v x i ≠ some [] := by
      intro i hiT hiTk
      apply hret i hiT
      omega
    have hwalk : walkStar v x (T + k + 1) ≠ some [] := by
      apply hret (T + k + 1)
      · omega
      · omega
    have ih_result := ih hret_k
    rw [show T + (k + 1) = (T + k) + 1 by omega]
    rw [posStar_succ]
    simp [ih_result, hwalk]

/-! ### The glued steps -/

/-- The glued step at time `t` is the piece value at the position of `t`. -/
theorem gluePath_eq {d : ℕ} [NeZero d] (v : Option (Vertex d)) (Z : ℕ × ℕ → Step d) (t : ℕ) :
    gluePath v Z t = Z (posStar v (gluePath v Z) t) := by
  let coord : ∀ k, (Fin k → ℕ × ℕ) → ℕ × ℕ → ℕ × ℕ := fun k _ i => i
  let R := fun (k : ℕ) => FrogModel.Pool.readGen coord (selStar v) Z k
  have h_gluePath : ∀ n, gluePath v Z n = R (n + 1) (Fin.last n) := by
    intro n
    unfold gluePath R coord
    rfl
  have h_readGen_apply : ∀ (n : ℕ), R (n + 1) (Fin.last n) = Z (FrogModel.Pool.cmap coord (FrogModel.Pool.labels (selStar v) (R (n + 1))) (Fin.last n)) := by
    intro n
    unfold R
    rw [FrogModel.Pool.readGen_apply]
  have h_cmap_id : ∀ {n : ℕ} (ℓ : Fin n → ℕ × ℕ) (j : Fin n), FrogModel.Pool.cmap coord ℓ j = ℓ j := by
    intro n ℓ j
    unfold FrogModel.Pool.cmap coord
    rfl
  have h_labels : ∀ (n : ℕ) (j : Fin (n + 1)), FrogModel.Pool.labels (selStar v) (R (n + 1)) j = selStar v (j : ℕ) (Fin.take (j : ℕ) (Fin.is_lt j).le (R (n + 1))) := by
    intro n j
    unfold FrogModel.Pool.labels R
    rfl
  have h_take : ∀ (n : ℕ), Fin.take n (Nat.le_add_right n 1) (R (n + 1)) = R n := by
    intro n
    unfold R
    rw [FrogModel.Pool.take_readGen]
  have h_extend_eq : ∀ i < t, extendSteps (R t) i = gluePath v Z i := by
    intro i hi
    unfold extendSteps
    simp [hi]
    unfold gluePath R coord
    have h := FrogModel.Pool.readGen_last coord (selStar v) Z t
    have h' := congrFun h ⟨i, hi⟩
    simpa using h'.symm
  have h_take_eq : ∀ (n : ℕ), Fin.take n (Fin.is_lt (Fin.last n)).le (R (n + 1)) = R n := by
    intro n
    have h := h_take n
    -- h: Fin.take n (Nat.le_add_right n 1) (R (n + 1)) = R n
    -- We need: Fin.take n (Fin.is_lt (Fin.last n)).le (R (n + 1)) = R n
    -- These are equal because the proof is irrelevant
    -- Use `funext` to prove equality pointwise
    funext i
    -- Goal: Fin.take n (Fin.is_lt (Fin.last n)).le (R (n + 1)) i = R n i
    -- i.e., R (n+1) (Fin.castLE (Fin.is_lt (Fin.last n)).le i) = R n i
    -- From h: R (n+1) (Fin.castLE (Nat.le_add_right n 1) i) = R n i
    -- So we need Fin.castLE (Fin.is_lt (Fin.last n)).le i = Fin.castLE (Nat.le_add_right n 1) i
    -- This follows from proof irrelevance: both are proofs of n ≤ n+1
    have hcast : Fin.castLE (Fin.is_lt (Fin.last n)).le i = Fin.castLE (Nat.le_add_right n 1) i := by
      simp
    simpa [hcast] using congrFun h i
  calc
    gluePath v Z t = R (t + 1) (Fin.last t) := by rw [h_gluePath]
    _ = Z (FrogModel.Pool.cmap coord (FrogModel.Pool.labels (selStar v) (R (t + 1))) (Fin.last t)) := by rw [h_readGen_apply]
    _ = Z ((FrogModel.Pool.labels (selStar v) (R (t + 1))) (Fin.last t)) := by rw [h_cmap_id]
    _ = Z (selStar v ((Fin.last t : Fin (t+1)) : ℕ) (Fin.take ((Fin.last t : Fin (t+1)) : ℕ) (Fin.is_lt (Fin.last t)).le (R (t + 1)))) := by rw [h_labels]
    _ = Z (selStar v t (Fin.take t (Fin.is_lt (Fin.last t)).le (R (t + 1)))) := by simp
    _ = Z (selStar v t (R t)) := by rw [h_take_eq]
    _ = Z (posStar v (extendSteps (R t)) t) := by
      unfold selStar
      rfl
    _ = Z (posStar v (gluePath v Z) t) := by
      apply congrArg Z
      apply FrogModel.Recursion.posStar_congr v (extendSteps (R t)) (gluePath v Z) t
      exact h_extend_eq

/-- From the start `T` of segment `s`, while the positions stay in segment `s`, the glued walk
is the walk of the segment. -/
theorem walkStar_gluePath_seg {d : ℕ} [NeZero d] (v : Option (Vertex d)) (Z : ℕ × ℕ → Step d)
    {T s : ℕ} (n : ℕ) (hT : posStar v (gluePath v Z) T = (s, 0))
    (hstart : walkStar v (gluePath v Z) T = segStart v s)
    (hpos : ∀ i < n, posStar v (gluePath v Z) (T + i) = (s, i)) :
    walkStar v (gluePath v Z) (T + n) = walkStar (segStart v s) (segPiece Z s) n := by
  induction' n with n ih
  · simp [walkStar, hstart]
  · have hpos_n : posStar v (gluePath v Z) (T + n) = (s, n) := hpos n (Nat.lt_succ_self n)
    have hpos_lt : ∀ i < n, posStar v (gluePath v Z) (T + i) = (s, i) :=
      fun i hi => hpos i (Nat.lt_trans hi (Nat.lt_succ_self n))
    calc
      walkStar v (gluePath v Z) (T + (n + 1)) = walkStar v (gluePath v Z) ((T + n) + 1) := by
        simp [add_assoc]
      _ = stepStar (walkStar v (gluePath v Z) (T + n)) (gluePath v Z (T + n)) := rfl
      _ = stepStar (walkStar v (gluePath v Z) (T + n)) (Z (posStar v (gluePath v Z) (T + n))) := by
        rw [gluePath_eq v Z (T + n)]
      _ = stepStar (walkStar v (gluePath v Z) (T + n)) (Z (s, n)) := by rw [hpos_n]
      _ = stepStar (walkStar v (gluePath v Z) (T + n)) (segPiece Z s n) := rfl
      _ = stepStar (walkStar (segStart v s) (segPiece Z s) n) (segPiece Z s n) := by rw [ih hpos_lt]
      _ = walkStar (segStart v s) (segPiece Z s) (n + 1) := rfl

/-- The glued steps are measurable in the pieces. -/
theorem measurable_gluePath {d : ℕ} [NeZero d] (v : Option (Vertex d)) :
    Measurable (gluePath (d := d) v) := by
  refine measurable_pi_iff.2 fun t => ?_
  have hsel : ∀ (k : ℕ) (i : ℕ × ℕ), MeasurableSet {y : Fin k → Step d | selStar v k y = i} := by
    intro k i
    exact MeasurableSet.of_discrete
  have h_read : Measurable fun (Z : ℕ × ℕ → Step d) =>
      FrogModel.Pool.readGen (fun _ _ i => i) (selStar v) Z (t + 1) :=
    FrogModel.Pool.measurable_readGen (fun _ _ i => i) (selStar v) hsel (t + 1)
  exact (measurable_pi_apply (Fin.last t)).comp h_read

/-- **Gluing.** The glued steps of i.i.d. pieces are i.i.d. -/
theorem map_gluePath {d : ℕ} [NeZero d] (v : Option (Vertex d)) :
    (Measure.infinitePi fun _ : ℕ × ℕ => stepLaw d).map (gluePath v) =
      Measure.infinitePi fun _ : ℕ => stepLaw d := by
  -- Both sides are probability measures on ℕ → Step d.
  -- Use measure_ext_of_prefix to reduce to equality of finite-dimensional distributions.
  refine FrogModel.Pool.measure_ext_of_prefix fun n => ?_
  -- After pushing forward to Fin n → Step d:
  -- LHS: ((infinitePi ...).map (gluePath v)).map (fun x j => x j)
  -- RHS: (infinitePi ...).map (fun x j => x j)
  -- Use map_map to swap the order on the LHS:
  have hmap_map : ((Measure.infinitePi fun _ : ℕ × ℕ => stepLaw d).map (gluePath v)).map
      (fun (x : ℕ → Step d) (j : Fin n) => x j) =
      (Measure.infinitePi fun _ : ℕ × ℕ => stepLaw d).map
      (fun (Z : (ℕ × ℕ) → Step d) (j : Fin n) => gluePath v Z j) := by
    refine Measure.map_map ?hg ?hf
    · -- hg: the projection (x : ℕ → Step d) ↦ (j : Fin n) ↦ x j is measurable
      -- Use Measurable.of_eval
      refine Measurable.of_eval fun j => ?_
      -- Need: Measurable (fun x : ℕ → Step d => x j)
      apply measurable_pi_apply
    · -- hf: gluePath v is measurable
      -- gluePath v Z t = readGen (fun _ _ i => i) (selStar v) Z (t+1) (Fin.last t)
      -- We use measurable_readGen and measurable_pi_iff
      refine Measurable.of_eval fun t => ?_
      -- Need: Measurable (fun Z : (ℕ × ℕ) → Step d => gluePath v Z t)
      -- gluePath v Z t = readGen ... Z (t+1) (Fin.last t)
      -- = (readGen ... Z (t+1)) (Fin.last t)
      -- readGen ... Z (t+1) is measurable by measurable_readGen
      -- and evaluation at Fin.last t is measurable by measurable_pi_apply
      have h_meas_readGen : Measurable (fun (Z : (ℕ × ℕ) → Step d) =>
          FrogModel.Pool.readGen (fun (_ : ℕ) (_ : Fin _ → ℕ × ℕ) (i : ℕ × ℕ) => i) (selStar v) Z (t+1)) :=
        FrogModel.Pool.measurable_readGen (fun (_ : ℕ) (_ : Fin _ → ℕ × ℕ) (i : ℕ × ℕ) => i)
          (selStar v) (by
            intro k i
            -- Need: MeasurableSet {y : Fin k → Step d | selStar v k y = i}
            -- Since Step d has discrete sigma-algebra, every set is measurable
            exact MeasurableSet.of_discrete) (t+1)
      -- Now compose with evaluation at Fin.last t
      have h_eval : Measurable (fun (f : Fin (t+1) → Step d) => f (Fin.last t)) :=
        measurable_pi_apply (Fin.last t)
      -- The composition gives the desired measurability
      -- But we need to express gluePath v Z t in terms of these
      -- gluePath v Z t = readGen ... Z (t+1) (Fin.last t)
      -- = (readGen ... Z (t+1)) (Fin.last t)
      -- So we can write:
      dsimp [gluePath]
      -- Goal: Measurable (fun Z => readGen (fun _ _ i => i) (selStar v) Z (t + 1) (Fin.last t))
      -- This is h_meas_readGen composed with h_eval
      -- Actually, readGen ... Z (t+1) (Fin.last t) = (readGen ... Z (t+1)) (Fin.last t)
      -- So we can use h_meas_readGen and h_eval
      -- But h_meas_readGen gives a function to Fin (t+1) → Step d
      -- and h_eval gives a function from (Fin (t+1) → Step d) to Step d
      -- The composition is measurable
      -- Let's use Measurable.comp
      refine Measurable.comp h_eval h_meas_readGen
  rw [hmap_map]
  -- By readGen_last, for each Z, (fun j => gluePath v Z j) = readGen (fun _ _ i => i) (selStar v) Z n
  have hglue_eq : (fun (Z : (ℕ × ℕ) → Step d) (j : Fin n) => gluePath v Z j) =
      (fun Z => FrogModel.Pool.readGen (fun (_ : ℕ) (_ : Fin _ → ℕ × ℕ) (i : ℕ × ℕ) => i)
        (selStar v) Z n) := by
    -- Prove equality of two functions (ℕ × ℕ) → Fin n → Step d
    refine funext fun Z => ?_
    -- Now goal: (fun j => gluePath v Z j) = readGen ... Z n
    refine funext fun j => ?_
    -- Now goal: gluePath v Z j = readGen ... Z n j
    dsimp [gluePath]
    -- Goal: readGen ... Z (j.val + 1) (Fin.last j.val) = readGen ... Z n j
    have h := FrogModel.Pool.readGen_last (fun (_ : ℕ) (_ : Fin _ → ℕ × ℕ) (i : ℕ × ℕ) => i)
      (selStar v) Z n
    -- h : (fun j => readGen ... Z (j + 1) (Fin.last j)) = readGen ... Z n
    -- Apply h at j
    exact congrFun h j
  rw [hglue_eq]
  -- Now LHS = (infinitePi (fun _ : ℕ×ℕ => stepLaw d)).map (fun Z => readGen (fun _ _ i => i) (selStar v) Z n)
  -- RHS = (infinitePi (fun _ : ℕ => stepLaw d)).map (fun x j => x j)
  -- But fun x j => x j = readGen (fun k _ _ => k) (selStar v) x n
  have h_right_eq : (fun (x : ℕ → Step d) (j : Fin n) => x j) =
      (fun x => FrogModel.Pool.readGen (fun (k : ℕ) (_ : Fin _ → ℕ × ℕ) (_ : ℕ × ℕ) => k)
        (selStar v) x n) := by
    -- Prove equality of two functions ℕ → Fin n → Step d
    refine funext fun x => ?_
    -- Now goal: (fun j => x j) = readGen ... x n
    refine funext fun j => ?_
    -- Now goal: x j = readGen ... x n j
    -- Use readGen_last
    have h := FrogModel.Pool.readGen_last (fun (k : ℕ) (_ : Fin _ → ℕ × ℕ) (_ : ℕ × ℕ) => k)
      (selStar v) x n
    -- h : (fun j => readGen ... x (j+1) (Fin.last j)) = readGen ... x n
    have h' := congrFun h j
    -- h' : readGen ... x (j.val + 1) (Fin.last j.val) = readGen ... x n j
    -- Need to simplify the LHS
    -- readGen ... x (j.val + 1) (Fin.last j.val) = x j.val because coord j _ _ = j
    -- Let's compute using the definition of readGen
    dsimp [FrogModel.Pool.readGen] at h'
    -- h' : x j.val = readGen ... x n j
    -- Goal: x j = readGen ... x n j
    -- Since x j = x j.val, h' is exactly the goal
    simpa using h'
  rw [h_right_eq]
  -- Now both sides are of the form (infinitePi μ).map (fun ω => readGen coord (selStar v) ω n)
  -- with coord₁ = fun _ _ i => i and coord₂ = fun k _ _ => k
  -- Apply map_readGen_eq
  refine FrogModel.Pool.map_readGen_eq
    (fun (_ : ℕ) (_ : Fin _ → ℕ × ℕ) (i : ℕ × ℕ) => i)
    (fun (k : ℕ) (_ : Fin _ → ℕ × ℕ) (_ : ℕ × ℕ) => k)
    (selStar v)
    ?_ -- hsel
    (fun (_ : ℕ × ℕ) => stepLaw d)
    (fun (_ : ℕ) => stepLaw d)
    (fun (_ : ℕ × ℕ) => stepLaw d)
    ?_ ?_ ?_ ?_ n
  · -- hsel: all sets {y | selStar v k y = i} are measurable
    -- Since we have DiscreteMeasurableSpace, every set is measurable
    intro k i
    -- Since we have DiscreteMeasurableSpace, every set is measurable
    exact MeasurableSet.of_discrete
  · -- hμ₁: μ₁ (coord₁ k ℓ i) = μ i
    intro k ℓ i
    rfl
  · -- hμ₂: μ₂ (coord₂ k ℓ i) = μ i
    intro k ℓ i
    rfl
  · -- hinj₁: cmap coord₁ ℓ is injective when ℓ is consistent
    intro n' ℓ hcons
    -- cmap coord₁ ℓ = ℓ (since coord₁ _ _ i = i)
    have h_cmap_eq : FrogModel.Pool.cmap (fun (_ : ℕ) (_ : Fin _ → ℕ × ℕ) (i : ℕ × ℕ) => i) ℓ = ℓ := by
      -- cmap coord₁ ℓ j = coord₁ j (Fin.take j ... ℓ) (ℓ j) = ℓ j
      -- So cmap coord₁ ℓ = ℓ pointwise
      refine funext fun j => ?_
      dsimp [FrogModel.Pool.cmap]
    rw [h_cmap_eq]
    -- Now we need ℓ to be injective.
    -- ℓ is consistent, so there exists q such that labels (selStar v) q = ℓ
    obtain ⟨q, hq⟩ := hcons
    rw [← hq]
    -- Need to show: labels (selStar v) q is injective
    -- Key lemma: labels (selStar v) q j = posStar v (extendSteps q) j
    have h_labels_eq : ∀ (j : Fin n'), FrogModel.Pool.labels (selStar v) q j =
        FrogModel.Recursion.posStar v (extendSteps q) j := by
      intro j
      dsimp [FrogModel.Pool.labels, selStar]
      -- Goal: posStar v (extendSteps (Fin.take j j.isLt.le q)) j = posStar v (extendSteps q) j
      -- By posStar_congr, it suffices to show the two sequences agree on the first j values
      apply FrogModel.Recursion.posStar_congr v (extendSteps (Fin.take j j.isLt.le q)) (extendSteps q) j
      intro i hi
      -- Need: extendSteps (Fin.take j ... q) i = extendSteps q i for i < j
      dsimp [extendSteps]
      -- For i < j, both sides use the "then" branch
      have hi_n' : i < n' := lt_of_lt_of_le hi j.isLt.le
      simp [hi, hi_n']
    intro a b h
    have hpos := FrogModel.Recursion.posStar_injective v (extendSteps q)
    -- hpos : Function.Injective (posStar v (extendSteps q))
    -- From h: labels (selStar v) q a = labels (selStar v) q b
    -- Using h_labels_eq, we get posStar v (extendSteps q) a = posStar v (extendSteps q) b
    -- Then hpos gives a = b
    rw [h_labels_eq a, h_labels_eq b] at h
    -- hpos h : (a : ℕ) = (b : ℕ)
    -- Need: a = b as Fin n'
    exact Fin.ext (hpos h)
  · -- hinj₂: cmap coord₂ ℓ is injective
    intro n' ℓ hcons
    -- cmap coord₂ ℓ j = j (as a ℕ), which is injective
    have h_cmap_eq : FrogModel.Pool.cmap (fun (k : ℕ) (_ : Fin _ → ℕ × ℕ) (_ : ℕ × ℕ) => k) ℓ =
        fun (j : Fin n') => (j : ℕ) := by
      ext j
      simp [FrogModel.Pool.cmap]
    rw [h_cmap_eq]
    -- The natural inclusion Fin n' → ℕ is injective
    exact Fin.val_injective

/-! ### Visits of a glued frog -/

/-- Up to a time within depth `K`, every segment before the current one returns within depth
`K`. -/
theorem retK_of_posStar {d : ℕ} [NeZero d] (K : ℕ) (v : Option (Vertex d))
    (Z : ℕ × ℕ → Step d) (t : ℕ)
    (hdepth : ∀ i ≤ t, depthStar (walkStar v (gluePath v Z) i) ≤ K) :
    ∀ s < (posStar v (gluePath v Z) t).1, retK K (segStart v s) (segPiece Z s) := by
  let x := gluePath v Z
  induction' t with t ih
  · intro s hs
    exfalso
    exact Nat.not_lt_zero _ hs
  · -- Goal: ∀ s < (posStar v x (t+1)).1, retK K (segStart v s) (segPiece Z s)
    rw [posStar_succ v x t]
    by_cases hret : walkStar v x (t + 1) = some []
    · rw [if_pos hret]
      -- Goal: ∀ s < ((posStar v x t).1 + 1), retK K (segStart v s) (segPiece Z s)
      intro s hs
      have hs' : s ≤ (posStar v x t).1 := Nat.le_of_lt_succ hs
      rcases Nat.eq_or_lt_of_le hs' with (rfl | hs_lt)
      · -- s = (posStar v x t).1, i.e., the new segment S
        set S := (posStar v x t).1 with hSdef
        set o := (posStar v x t).2 with ho_def
        have hpos := posStar_start v x t
        rcases hpos with ⟨ho_le_t, hpos_eq, hwalk_start, hno_ret⟩
        -- hpos_eq: posStar v x (t - o) = (S, 0)
        -- hwalk_start: walkStar v x (t - o) = segStart v S
        -- hno_ret: no returns in (t-o, t]
        -- For i ≤ o, we have posStar v x (t - o + i) = (S, i) by posStar_add
        have hpos_add : ∀ i ≤ o, posStar v x (t - o + i) = (S, i) := by
          intro i hi
          refine posStar_add v x (T := t - o) (s := S) i hpos_eq ?_
          intro j hj_lt hj_le
          apply hno_ret j
          · exact hj_lt
          · -- j ≤ t - o + i ≤ t
            have hle : t - o + i ≤ t := by
              have : t - o + i ≤ t - o + o := Nat.add_le_add_left hi (t - o)
              have h_eq : t - o + o = t := Nat.sub_add_cancel ho_le_t
              rw [h_eq] at this
              exact this
            omega
        -- Now use walkStar_gluePath_seg with n = o + 1
        have h_seg_walk : walkStar v x (t - o + (o + 1)) = walkStar (segStart v S) (segPiece Z S) (o + 1) := by
          refine walkStar_gluePath_seg v Z (o + 1) hpos_eq hwalk_start ?_
          intro i hi
          have hi_le_o : i ≤ o := Nat.le_of_lt_succ hi
          rw [hpos_add i hi_le_o]
        -- But t - o + (o + 1) = t + 1
        have h_time : t - o + (o + 1) = t + 1 := by
          omega
        rw [h_time] at h_seg_walk
        rw [hret] at h_seg_walk
        -- So walkStar (segStart v S) (segPiece Z S) (o + 1) = some []
        have h_return : walkStar (segStart v S) (segPiece Z S) (o + 1) = some [] := by
          rw [← h_seg_walk]
        -- Now the depth bound: for all i ≤ o + 1, depthStar (...) ≤ K
        have h_depth : ∀ i ≤ o + 1, depthStar (walkStar (segStart v S) (segPiece Z S) i) ≤ K := by
          intro i hi
          rcases Nat.eq_or_lt_of_le hi with (rfl | hi_lt)
          · -- i = o + 1
            -- walkStar (segStart v S) (segPiece Z S) (o + 1) = some []
            -- from h_seg_walk and hret
            rw [h_seg_walk.symm]
            -- depthStar (some []) = 0 ≤ K
            have : depthStar (some ([] : Vertex d)) = 0 := by simp [depthStar]
            rw [this]
            exact Nat.zero_le _
          · -- i < o + 1, so i ≤ o
            have hi_le_o : i ≤ o := Nat.le_of_lt_succ hi_lt
            -- Relate walkStar (segStart v S) (segPiece Z S) i to walkStar v x (t - o + i)
            have h_eq : walkStar (segStart v S) (segPiece Z S) i = walkStar v x (t - o + i) := by
              refine (walkStar_gluePath_seg v Z i hpos_eq hwalk_start (fun j hj => ?_)).symm
              have hj_le_o : j ≤ o := Nat.le_of_lt (Nat.lt_of_lt_of_le hj hi_le_o)
              rw [hpos_add j hj_le_o]
            rw [h_eq]
            -- Need to show t - o + i ≤ t
            have h_le_t : t - o + i ≤ t := by
              have : t - o + i ≤ t - o + o := Nat.add_le_add_left hi_le_o (t - o)
              have h_eq : t - o + o = t := Nat.sub_add_cancel ho_le_t
              rw [h_eq] at this
              exact this
            apply hdepth (t - o + i)
            omega
        -- Now assemble retK
        refine ⟨o + 1, ?_, h_return, h_depth⟩
        omega
      · -- s < (posStar v x t).1, use induction hypothesis
        have hdepth_t : ∀ i ≤ t, depthStar (walkStar v x i) ≤ K := by
          intro i hi
          apply hdepth i
          omega
        exact ih hdepth_t s hs_lt
    · rw [if_neg hret]
      -- Goal: ∀ s < (posStar v x t).1, retK K (segStart v s) (segPiece Z s)
      intro s hs
      have hdepth_t : ∀ i ≤ t, depthStar (walkStar v x i) ≤ K := by
        intro i hi
        apply hdepth i
        omega
      exact ih hdepth_t s hs

/-- If every segment before `s` returns within depth `K`, segment `s` starts at some time `T`,
at depth `≤ K` before `T`. -/
theorem exists_segStart_time {d : ℕ} [NeZero d] (K : ℕ) (v : Option (Vertex d))
    (Z : ℕ × ℕ → Step d) (s : ℕ) (halive : ∀ s' < s, retK K (segStart v s') (segPiece Z s')) :
    ∃ T, posStar v (gluePath v Z) T = (s, 0) ∧ walkStar v (gluePath v Z) T = segStart v s ∧
      ∀ i < T, depthStar (walkStar v (gluePath v Z) i) ≤ K := by
  induction' s with s ih
  · -- Base case s = 0: take T = 0
    refine ⟨0, ?_, ?_, ?_⟩
    · -- posStar v (gluePath v Z) 0 = (0, 0)
      exact posStar_zero v (gluePath v Z)
    · -- walkStar v (gluePath v Z) 0 = segStart v 0
      simp [walkStar, segStart]
    · -- ∀ i < 0, depthStar ... ≤ K
      intro i hi
      exfalso; exact Nat.not_lt_zero _ hi
  · -- Inductive step: from s to s+1
    have halive_s : ∀ s' < s, retK K (segStart v s') (segPiece Z s') := by
      intro s' hs'
      exact halive s' (Nat.lt_of_lt_of_le hs' (Nat.le_succ _))
    rcases ih halive_s with ⟨T, hTpos, hTwalk, hTdepth⟩
    -- From halive, we have retK for segment s
    have hret_s : retK K (segStart v s) (segPiece Z s) := halive s (Nat.lt_succ_self s)
    -- Extract the minimal return time c (c ≥ 1)
    set c := Nat.find hret_s with hc_def
    have hc_spec : 1 ≤ c ∧ walkStar (segStart v s) (segPiece Z s) c = some [] ∧
        ∀ i ≤ c, depthStar (walkStar (segStart v s) (segPiece Z s) i) ≤ K := by
      simpa [hc_def] using Nat.find_spec hret_s
    rcases hc_spec with ⟨hc1, hcwalk, hcdepth⟩
    -- Minimality: for any 1 ≤ i < c, the segment walk is not at []
    have hc_min : ∀ i, 1 ≤ i → i < c → walkStar (segStart v s) (segPiece Z s) i ≠ some [] := by
      intro i hi1 hi_lt_c
      by_contra h_eq
      have h_not := Nat.find_min hret_s hi_lt_c
      apply h_not
      refine ⟨hi1, h_eq, ?_⟩
      intro j hj
      apply hcdepth j
      omega
    -- Set x = gluePath v Z for brevity
    set x := gluePath v Z with hx_def
    -- Joint induction: for i < c, posStar = (s, i) and walkStar = segment walk
    have h_joint : ∀ i, i < c → posStar v x (T + i) = (s, i) ∧
        walkStar v x (T + i) = walkStar (segStart v s) (segPiece Z s) i := by
      intro i hi
      induction' i using Nat.strong_induction_on with i ih
      rcases Nat.eq_zero_or_pos i with (rfl | hi_pos)
      · exact ⟨hTpos, hTwalk⟩
      · have hi_lt_c : i < c := hi
        have hi_sub_lt : i - 1 < i := by omega
        have hi_sub_lt_c : i - 1 < c := by omega
        rcases ih (i - 1) hi_sub_lt hi_sub_lt_c with ⟨hpos_i_sub, hwalk_i_sub⟩
        have hpos_all : ∀ j < i, posStar v x (T + j) = (s, j) := by
          intro j hj
          have hj_lt_c : j < c := by omega
          exact (ih j hj hj_lt_c).1
        have hwalk_i : walkStar v x (T + i) =
            walkStar (segStart v s) (segPiece Z s) i :=
          walkStar_gluePath_seg v Z i hTpos hTwalk hpos_all
        have hpos_i : posStar v x (T + i) = (s, i) := by
          have h_eq : T + i = (T + (i - 1)) + 1 := by omega
          rw [h_eq, posStar_succ v x (T + (i - 1))]
          rw [hpos_i_sub]
          have hwalk_succ : walkStar v x ((T + (i - 1)) + 1) =
              walkStar (segStart v s) (segPiece Z s) i := by
            have : (T + (i - 1)) + 1 = T + i := by omega
            rw [this]
            exact hwalk_i
          rw [hwalk_succ]
          by_cases h_eq' : walkStar (segStart v s) (segPiece Z s) i = some []
          · exfalso
            apply hc_min i (by omega) hi_lt_c
            exact h_eq'
          · simp [h_eq']
            omega
        exact ⟨hpos_i, hwalk_i⟩
    -- The walk at T + c is []
    have hwalk_c : walkStar v x (T + c) = some [] := by
      have hpos_all : ∀ j < c, posStar v x (T + j) = (s, j) := by
        intro j hj; exact (h_joint j hj).1
      have hwalk_c' := walkStar_gluePath_seg v Z c hTpos hTwalk hpos_all
      simpa [hx_def, hcwalk] using hwalk_c'
    -- posStar at T + c is (s+1, 0)
    have hpos_c : posStar v x (T + c) = (s + 1, 0) := by
      have hc_sub_lt : c - 1 < c := by
        omega
      have hpos_c_sub : posStar v x (T + (c - 1)) = (s, c - 1) :=
        (h_joint (c - 1) hc_sub_lt).1
      have h_eq : T + c = (T + (c - 1)) + 1 := by omega
      rw [h_eq, posStar_succ v x (T + (c - 1))]
      rw [hpos_c_sub]
      have hwalk_succ : walkStar v x ((T + (c - 1)) + 1) = some [] := by
        have : (T + (c - 1)) + 1 = T + c := by omega
        rw [this]
        exact hwalk_c
      simp [hwalk_succ]
    -- Now we have the required T' = T + c for s + 1
    refine ⟨T + c, hpos_c, ?_, ?_⟩
    · -- walkStar v (gluePath v Z) (T + c) = segStart v (s + 1)
      simpa [hx_def, segStart] using hwalk_c
    · -- Depth bound: ∀ i < T + c, depthStar (walkStar v x i) ≤ K
      intro i hi
      by_cases hi_lt_T : i < T
      · -- i < T: use induction hypothesis
        simpa [hx_def] using hTdepth i hi_lt_T
      · -- T ≤ i < T + c
        have h_ge_T : T ≤ i := by omega
        -- Write i = T + j with j < c
        have h_exists_j : ∃ j, i = T + j := Nat.exists_eq_add_of_le h_ge_T
        rcases h_exists_j with ⟨j, hj⟩
        have hj_lt_c : j < c := by
          omega
        have hwalk_j := (h_joint j hj_lt_c).2
        -- hwalk_j : walkStar v x (T + j) = walkStar (segStart v s) (segPiece Z s) j
        have hdepth_j : depthStar (walkStar v x (T + j)) ≤ K := by
          rw [hwalk_j]
          apply hcdepth j
          omega
        simpa [hj, hx_def] using hdepth_j

/-- A visit of the glued frog before it is killed is a visit of one of its live segments. -/
theorem segVis_of_visitsK_gluePath {d : ℕ} [NeZero d] (K : ℕ) (v : Option (Vertex d))
    (Z : ℕ × ℕ → Step d) (b : Option (Vertex d)) (h : visitsK K v (gluePath v Z) b) :
    ∃ s, (∀ s' < s, retK K (segStart v s') (segPiece Z s')) ∧
      segVis K (segStart v s) (segPiece Z s) b := by
  rcases h with ⟨n, hwalk, hdepth⟩
  set p := posStar v (gluePath v Z) n with hp
  set s := p.1 with hs
  set o := p.2 with ho
  have ho_le_n : o ≤ n := (posStar_start v (gluePath v Z) n).1
  have hT : posStar v (gluePath v Z) (n - o) = (s, 0) :=
    (posStar_start v (gluePath v Z) n).2.1
  have hstart : walkStar v (gluePath v Z) (n - o) = segStart v s :=
    (posStar_start v (gluePath v Z) n).2.2.1
  have hno_ret : ∀ i, n - o < i → i ≤ n → walkStar v (gluePath v Z) i ≠ some [] :=
    (posStar_start v (gluePath v Z) n).2.2.2
  have hpos_add : ∀ k, k ≤ o → posStar v (gluePath v Z) ((n - o) + k) = (s, k) := by
    intro k hk
    induction' k with k ih
    · exact hT
    · have hk_succ_le_o : k + 1 ≤ o := hk
      have hk_le_o : k ≤ o := Nat.le_of_succ_le hk_succ_le_o
      have hret : ∀ i, (n - o) < i → i ≤ (n - o) + (k + 1) → walkStar v (gluePath v Z) i ≠ some [] := by
        intro i hi1 hi2
        apply hno_ret i hi1
        have : (n - o) + (k + 1) ≤ n := by
          calc
            (n - o) + (k + 1) ≤ (n - o) + o := Nat.add_le_add_left hk_succ_le_o _
            _ = n := Nat.sub_add_cancel ho_le_n
        exact Nat.le_trans hi2 this
      have hpos_succ := posStar_add v (gluePath v Z) (k + 1) hT hret
      simpa [add_assoc] using hpos_succ
  have h_walk_n_eq : (n - o) + o = n := Nat.sub_add_cancel ho_le_n
  have hwalk_seg_at_o : walkStar v (gluePath v Z) ((n - o) + o) = walkStar (segStart v s) (segPiece Z s) o := by
    apply walkStar_gluePath_seg v Z o hT hstart
    intro i hi
    have hi_le_o : i ≤ o := Nat.le_of_lt hi
    exact hpos_add i hi_le_o
  rw [h_walk_n_eq] at hwalk_seg_at_o
  rw [hwalk] at hwalk_seg_at_o
  have hretK : ∀ s' < s, retK K (segStart v s') (segPiece Z s') := by
    have := retK_of_posStar K v Z n hdepth
    simpa [hs] using this
  have h_segVis : segVis K (segStart v s) (segPiece Z s) b := by
    rw [segVis]
    refine ⟨o, ?_, ?_, ?_⟩
    · -- walkStar (segStart v s) (segPiece Z s) o = b
      rw [← hwalk_seg_at_o]
    · -- no return before o
      intro i hi1 hi2
      have h_no_ret := hno_ret ((n - o) + i) (by omega) (by
        have : (n - o) + i ≤ (n - o) + o := Nat.add_le_add_left (Nat.le_of_lt hi2) _
        rw [h_walk_n_eq] at this
        exact this)
      have h_eq := walkStar_gluePath_seg v Z i hT hstart (fun j hj => hpos_add j (Nat.le_of_lt (Nat.lt_trans hj hi2)))
      rw [h_eq] at h_no_ret
      exact h_no_ret
    · -- depth ≤ K
      intro i hi
      have hi_le_o : i ≤ o := hi
      have hpos_i : posStar v (gluePath v Z) ((n - o) + i) = (s, i) := hpos_add i hi_le_o
      have h_le_n : (n - o) + i ≤ n := by
        calc
          (n - o) + i ≤ (n - o) + o := Nat.add_le_add_left hi_le_o _
          _ = n := h_walk_n_eq
      have hdepth_i : depthStar (walkStar v (gluePath v Z) ((n - o) + i)) ≤ K := hdepth _ h_le_n
      have hpos_bound : ∀ j, j < i → posStar v (gluePath v Z) ((n - o) + j) = (s, j) := by
        intro j hj
        have hj_le_o : j ≤ o := Nat.le_of_lt (Nat.lt_of_lt_of_le hj hi_le_o)
        exact hpos_add j hj_le_o
      have h_eq := walkStar_gluePath_seg v Z i hT hstart hpos_bound
      rw [h_eq] at hdepth_i
      exact hdepth_i
  exact ⟨s, hretK, h_segVis⟩

/-- A visit of a live segment is a visit of the glued frog before it is killed. -/
theorem visitsK_gluePath_of_segVis {d : ℕ} [NeZero d] (K : ℕ) (v : Option (Vertex d))
    (Z : ℕ × ℕ → Step d) (b : Option (Vertex d)) (s : ℕ)
    (halive : ∀ s' < s, retK K (segStart v s') (segPiece Z s'))
    (hvis : segVis K (segStart v s) (segPiece Z s) b) : visitsK K v (gluePath v Z) b := by
  rcases exists_segStart_time K v Z s halive with ⟨T, hT_pos, hT_walk, hT_depth⟩
  rcases hvis with ⟨n, hn_walk, hn_noRet, hn_depth⟩
  -- First, prove posStar equality for all i < n by strong induction
  have h_pos : ∀ i, i < n → posStar v (gluePath v Z) (T + i) = (s, i) := by
    intro i hi
    -- Use strong induction on i, with hi as part of the induction
    revert hi
    refine Nat.strong_induction_on i (fun k IH hi => ?_)
    -- hi : k < n
    cases k with
    | zero => exact hT_pos
    | succ i' =>
      -- hi : i' + 1 < n
      have hi_succ_lt_n : i' + 1 < n := hi
      have h_pos_i' : posStar v (gluePath v Z) (T + i') = (s, i') := IH i' (by omega) (by omega)
      -- Get walk equality at T + (i'+1) using walkStar_gluePath_seg
      have h_walk_succ : walkStar v (gluePath v Z) (T + (i' + 1)) = walkStar (segStart v s) (segPiece Z s) (i' + 1) :=
        walkStar_gluePath_seg v Z (i' + 1) hT_pos hT_walk (fun j hj => IH j (by omega) (by omega))
      -- No-return condition for (T, T+(i'+1)]
      have h_ret : ∀ j, T < j → j ≤ T + (i' + 1) → walkStar v (gluePath v Z) j ≠ some [] := by
        intro j hj_lt hj_le
        have hk : 1 ≤ j - T := by omega
        have hk_le : j - T ≤ i' + 1 := by omega
        by_cases hk_eq_i' : j - T = i' + 1
        · -- k = i'+1
          rw [show j = T + (i' + 1) by omega]
          rw [h_walk_succ]
          have h1 : 1 ≤ i' + 1 := by omega
          exact hn_noRet (i' + 1) h1 hi_succ_lt_n
        · -- k ≤ i'
          have hk_lt_n : j - T < n := by omega
          rw [show j = T + (j - T) by omega]
          rw [walkStar_gluePath_seg v Z (j - T) hT_pos hT_walk (fun j' hj' => IH j' (by omega) (by omega))]
          exact hn_noRet (j - T) hk hk_lt_n
      have h_pos_succ := posStar_add v (gluePath v Z) (i' + 1) hT_pos h_ret
      -- posStar_add gives (s, i' + 1), but we need (s, i' + 1) which is the same
      simpa [add_comm] using h_pos_succ
  -- Now get walk equality for all i ≤ n using walkStar_gluePath_seg
  have h_walk_eq : ∀ i, i ≤ n → walkStar v (gluePath v Z) (T + i) = walkStar (segStart v s) (segPiece Z s) i := by
    intro i hi
    rcases lt_or_eq_of_le hi with (hi_lt | hi_eq)
    · -- i < n
      exact walkStar_gluePath_seg v Z i hT_pos hT_walk (fun j hj => h_pos j (by omega))
    · -- i = n
      rw [hi_eq]
      exact walkStar_gluePath_seg v Z n hT_pos hT_walk (fun j hj => h_pos j hj)
  -- In particular, at i = n: walkStar v (gluePath v Z) (T + n) = b
  have h_walk_n : walkStar v (gluePath v Z) (T + n) = b := by
    rw [h_walk_eq n (le_refl n), hn_walk]
  -- Now assemble the visitsK condition
  refine ⟨T + n, h_walk_n, ?_⟩
  intro i hi
  rcases lt_or_ge i T with (h_lt | h_ge)
  · -- i < T: use hT_depth
    exact hT_depth i h_lt
  · -- T ≤ i ≤ T + n
    have h_i_sub : i - T ≤ n := by omega
    have h_walk_i : walkStar v (gluePath v Z) i = walkStar (segStart v s) (segPiece Z s) (i - T) := by
      have h1 : walkStar v (gluePath v Z) i = walkStar v (gluePath v Z) (T + (i - T)) := by
        congr 1
        omega
      have h2 : walkStar v (gluePath v Z) (T + (i - T)) = walkStar (segStart v s) (segPiece Z s) (i - T) :=
        h_walk_eq (i - T) h_i_sub
      rw [h1, h2]
    rw [h_walk_i]
    exact hn_depth (i - T) h_i_sub

/-- **Visits of a glued frog.** -/
theorem visitsK_gluePath {d : ℕ} [NeZero d] (K : ℕ) (v : Option (Vertex d))
    (Z : ℕ × ℕ → Step d) (b : Option (Vertex d)) :
    visitsK K v (gluePath v Z) b ↔
      ∃ s, (∀ s' < s, retK K (segStart v s') (segPiece Z s')) ∧
        segVis K (segStart v s) (segPiece Z s) b := by
  constructor
  · exact segVis_of_visitsK_gluePath K v Z b
  · rintro ⟨s, halive, hvis⟩
    exact visitsK_gluePath_of_segVis K v Z b s halive hvis

end FrogModel.Recursion
