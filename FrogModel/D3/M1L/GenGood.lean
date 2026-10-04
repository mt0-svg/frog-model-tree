module

public import FrogModel.D3.M1L.GenStep

@[expose] public section

/-!
# M1_L at every height: the good states and the bounds of the candidate

The good states are kept by every read; the ghost walk is a supersolution step; the candidate is
nonnegative, linear in its end value at cost `0`, and `1` for the end value `1`.
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3

/-- One step of a ghost walk: the cost of the step and the mean of the next depth are at most the
value at the current depth. -/
theorem ghost_ineq (p : Params) (hL : 2 ≤ p.L) (d : ℕ) (hd1 : 1 ≤ d) (hdL : d < p.L)
    (c : ℝ) (hc : 0 ≤ c) (A B : ℝ) :
    c + 1 / 4 * ghostV p c A B (d - 1) + 3 / 4 * ghostV p c A B (d + 1) ≤
      ghostV p c A B d := by
  have hL1 : 1 ≤ p.L := by omega
  rcases FrogModel.D3.rL_facts p.L hL1 with ⟨hr0, hrL, hr1, hrec, hbound⟩
  have hpos : ∀ d, 0 ≤ FrogModel.D3.rL p.L d := fun d => (hbound d).1
  have hle1 : ∀ d, FrogModel.D3.rL p.L d ≤ 1 := fun d => (hbound d).2
  unfold FrogModel.D3.ghostV FrogModel.D3.gcost
  have hd0 : d ≠ 0 := by omega
  have hdL_ne : d ≠ p.L := by omega
  -- simplify the central term (d is strictly between 0 and p.L)
  simp [hd0, hdL_ne]
  by_cases hd_eq1 : d = 1
  · -- Case d = 1
    subst hd_eq1
    simp
    by_cases h2L : 2 = p.L
    · -- p.L = 2
      have hrec1 := hrec 1 (by omega) (by omega)
      have hrec1_simp : FrogModel.D3.rL p.L 1 = 1/4 := by
        simpa [h2L, hr0, hrL] using hrec1
      have hL1' : 1 ≤ p.L := by omega
      have cast_sub_1 : ((p.L - 1 : ℕ) : ℝ) = (p.L : ℝ) - 1 := by
        rw [Nat.cast_sub hL1', Nat.cast_one]
      have hgoal : c + 1/4 * A + 3/4 * B ≤ c * (2 * ((p.L : ℝ) - 1)) + (1/4 : ℝ) * A + (1 - (1/4 : ℝ)) * B := by
        have h2L' : (p.L : ℝ) = 2 := by exact_mod_cast h2L.symm
        rw [h2L']
        nlinarith
      simpa [h2L, hr0, hrL, hrec1_simp, cast_sub_1] using hgoal
    · -- p.L > 2
      have h2_lt_L : 2 < p.L := by omega
      have hrec1 := hrec 1 (by omega) (by omega)
      have hrec1_simp : FrogModel.D3.rL p.L 1 = 1/4 + 3/4 * FrogModel.D3.rL p.L 2 := by
        simpa [hr0] using hrec1
      rw [hrec1_simp]
      -- Now we need to handle the casts for p.L - 2 and p.L - 1
      have hL2 : 2 ≤ p.L := by omega
      have hL1' : 1 ≤ p.L := by omega
      have cast_sub_2 : ((p.L - 2 : ℕ) : ℝ) = (p.L : ℝ) - 2 :=
        Nat.cast_sub hL2
      have cast_sub_1 : ((p.L - 1 : ℕ) : ℝ) = (p.L : ℝ) - 1 := by
        rw [Nat.cast_sub hL1', Nat.cast_one]
      rw [cast_sub_2, cast_sub_1]
      have hr2_pos : 0 ≤ FrogModel.D3.rL p.L 2 := hpos 2
      have hr2_le1 : FrogModel.D3.rL p.L 2 ≤ 1 := hle1 2
      -- After rewriting, the goal is:
      -- c + 1/4*A + 3/4*(c*(2*(p.L-2)) + rL2*A + (1-rL2)*B) ≤ c*(2*(p.L-1)) + (1/4+3/4*rL2)*A + (1-(1/4+3/4*rL2))*B
      -- The A and B coefficients match. We need: c + 3/4*c*2*(p.L-2) ≤ c*2*(p.L-1)
      -- Since c ≥ 0, this is: 1 + 3/2*(p.L-2) ≤ 2*(p.L-1)
      -- which simplifies to 0 ≤ 1/2*p.L, true since p.L ≥ 2.
      have hgoal : c + 1/4 * A + 3/4 * (c * (2 * ((p.L : ℝ) - 2)) + FrogModel.D3.rL p.L 2 * A + (1 - FrogModel.D3.rL p.L 2) * B) ≤
          c * (2 * ((p.L : ℝ) - 1)) + (1/4 + 3/4 * FrogModel.D3.rL p.L 2) * A + (1 - (1/4 + 3/4 * FrogModel.D3.rL p.L 2)) * B := by
        -- Simplify the goal: subtract the A and B terms from both sides
        -- The goal is equivalent to: c + 3/4 * c * 2 * (p.L - 2) ≤ c * 2 * (p.L - 1)
        -- Since c ≥ 0, divide by c: 1 + 3/2*(p.L-2) ≤ 2*(p.L-1)
        -- which simplifies to 0 ≤ 1/2*p.L
        have hL_real : (0 : ℝ) ≤ (p.L : ℝ) - 2 := by
          have : (2 : ℝ) ≤ (p.L : ℝ) := by exact_mod_cast hL
          linarith
        nlinarith [hc, hr2_pos, hr2_le1, hL_real]
      -- Now we need to connect hgoal to the actual goal
      -- The actual goal has `if 2 = p.L then ...` but we know 2 ≠ p.L
      simpa [h2L, hr0, hrL] using hgoal
  · -- Case d ≠ 1, so d > 1
    have hd_gt1 : 1 < d := by omega
    have hd1_ne_zero' : d - 1 ≠ 0 := by omega
    have hd1_lt_L : d - 1 < p.L := by omega
    have hd1_ne_L : d - 1 ≠ p.L := by omega
    simp [hd1_ne_zero', hd1_ne_L]
    by_cases hd_plus1_eq_L : d + 1 = p.L
    · -- Case d + 1 = p.L
      have hrec_d := hrec d hd1 hdL
      have hrec_d_simp : FrogModel.D3.rL p.L d = 1/4 * FrogModel.D3.rL p.L (d - 1) := by
        simpa [hrL, hd_plus1_eq_L] using hrec_d
      rw [hd_plus1_eq_L]
      simp [hrec_d_simp]
      -- Now the A and B coefficients match. We need to handle the cost inequality.
      have hLd : d ≤ p.L := by omega
      have hLd1 : d - 1 ≤ p.L := by omega
      have cast_sub_d : ((p.L - d : ℕ) : ℝ) = (p.L : ℝ) - (d : ℝ) :=
        Nat.cast_sub hLd
      have cast_sub_d1 : ((p.L - (d - 1) : ℕ) : ℝ) = (p.L : ℝ) - ((d - 1 : ℕ) : ℝ) :=
        Nat.cast_sub hLd1
      rw [cast_sub_d, cast_sub_d1]
      have cast_sub_d1' : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [cast_sub_d1']
      -- Goal: c + 1/4*(c*(2*(p.L - (d-1))) + rL*(d-1)*A + (1-rL*(d-1))*B) + 3/4*B ≤
      --       c*(2*(p.L-d)) + (1/4*rL*(d-1))*A + (1-1/4*rL*(d-1))*B
      -- The A and B coefficients match. We need: c + 1/4*c*2*(p.L-(d-1)) ≤ c*2*(p.L-d)
      -- i.e., c*(1 + 1/2*(p.L-d+1)) ≤ c*2*(p.L-d)
      -- Since c ≥ 0: 1 + 1/2*(p.L-d+1) ≤ 2*(p.L-d)
      -- 3/2 + (p.L-d)/2 ≤ 2*(p.L-d)
      -- 3/2 ≤ 3/2*(p.L-d)
      -- 1 ≤ p.L-d
      -- True since d < p.L and d ≥ 2.
      have hLd_real : (1 : ℝ) ≤ (p.L : ℝ) - (d : ℝ) := by
        have : (d : ℕ) + 1 ≤ p.L := by omega
        have h' : (d : ℝ) + 1 ≤ (p.L : ℝ) := by exact_mod_cast this
        linarith
      nlinarith [hc, hLd_real]
    · -- Case d + 1 < p.L
      have hd_plus1_lt_L : d + 1 < p.L := by omega
      have hd_plus1_ne_L : d + 1 ≠ p.L := by omega
      simp [hd_plus1_ne_L]
      have hrec_d := hrec d hd1 hdL
      rw [hrec_d]
      -- Now the A and B coefficients match. We need to handle the cost inequality.
      have hLd : d ≤ p.L := by omega
      have hLd1 : d - 1 ≤ p.L := by omega
      have hLd_plus1 : d + 1 ≤ p.L := by omega
      have cast_sub_d : ((p.L - d : ℕ) : ℝ) = (p.L : ℝ) - (d : ℝ) :=
        Nat.cast_sub hLd
      have cast_sub_d1 : ((p.L - (d - 1) : ℕ) : ℝ) = (p.L : ℝ) - ((d - 1 : ℕ) : ℝ) :=
        Nat.cast_sub hLd1
      have cast_sub_dp1 : ((p.L - (d + 1) : ℕ) : ℝ) = (p.L : ℝ) - ((d + 1 : ℕ) : ℝ) :=
        Nat.cast_sub hLd_plus1
      rw [cast_sub_d, cast_sub_d1, cast_sub_dp1]
      have cast_sub_d1' : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      have cast_sub_dp1' : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by
        simp
      rw [cast_sub_d1', cast_sub_dp1']
      -- Goal: c + 1/4*(c*(2*(p.L-(d-1))) + rL*(d-1)*A + (1-rL*(d-1))*B) +
      --        3/4*(c*(2*(p.L-(d+1))) + rL*(d+1)*A + (1-rL*(d+1))*B) ≤
      --       c*(2*(p.L-d)) + (1/4*rL*(d-1)+3/4*rL*(d+1))*A + (1-(1/4*rL*(d-1)+3/4*rL*(d+1)))*B
      -- The A and B coefficients match. We need:
      -- c + 1/4*c*2*(p.L-(d-1)) + 3/4*c*2*(p.L-(d+1)) ≤ c*2*(p.L-d)
      -- c*(1 + 1/2*(p.L-d+1) + 3/2*(p.L-d-1)) ≤ c*2*(p.L-d)
      -- c*(1 + 2*(p.L-d)) ≤ c*2*(p.L-d)
      -- c ≤ c*(p.L-d)
      -- 1 ≤ p.L-d (since c ≥ 0)
      -- True since d < p.L.
      have hLd_real : (1 : ℝ) ≤ (p.L : ℝ) - (d : ℝ) := by
        have : (d : ℕ) + 1 ≤ p.L := by omega
        have h' : (d : ℝ) + 1 ≤ (p.L : ℝ) := by exact_mod_cast this
        linarith
      nlinarith [hc, hLd_real]

/-- The shape of the stack survives new marks. -/
theorem StackOK_mono (p : Params) (marks marks' : Finset (Vertex 3)) (hm : marks ⊆ marks') :
    ∀ (hd : Bool) (l : List Frame), StackOK p marks hd l → StackOK p marks' hd l := by
  intro hd l h
  induction l generalizing hd with
  | nil => exact trivial
  | cons f l ih =>
    cases l with
    | nil => exact h
    | cons g rest =>
      rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, hm h2, h3, h4, h5, ?_⟩
      apply ih false h6

/-- The initial state is good. -/
theorem good_init (p : Params) (k : ℕ) (hk : k + 1 ≤ p.P) :
    init k ∈ Good p := by
  simp [FrogModel.D3.Good, FrogModel.D3.StackOK, FrogModel.D3.FrameOK, FrogModel.D3.MarksAnc, FrogModel.D3.init, hk]

/-- `settle` on a stack whose head neither waits for its kill coin nor has a ghost gives a good
state. -/
theorem settle_good (p : Params) (marks : Finset (Vertex 3)) (f : Frame) (rest : List Frame)
    (hM : MarksAnc marks) (hS : StackOK p marks false (f :: rest)) :
    settle marks (f :: rest) ∈ Good p := by
  cases rest with
  | nil =>
    obtain ⟨hv, hR, hk, -, hg, hF⟩ := hS
    have hg := hg rfl
    simp only [settle]
    split_ifs with h
    · exact ⟨hM, trivial, fun _ => hF.2.1⟩
    · refine ⟨hM, ⟨hv, hR, hk, fun _ => ?_, fun h => absurd h (by simp), hF⟩, fun h => by simp at h⟩
      exact not_and_or.mp h
  | cons g s =>
    obtain ⟨hv, hm, -, hkg, hF, hT⟩ := hS
    obtain ⟨hk, hg⟩ := hkg rfl
    simp only [settle]
    split_ifs with h
    · exact ⟨hM, ⟨hv, hm, fun _ => ⟨fun _ => h, fun _ => rfl⟩, fun h => absurd h (by simp), hF, hT⟩,
        fun h => by simp at h⟩
    · refine ⟨hM, ⟨hv, hm, fun _ => ?_, fun h => absurd h (by simp), hF, hT⟩, fun h => by simp at h⟩
      simp only [hk, Bool.false_eq_true, false_iff]
      exact h

/-- A new head closure, at the same vertex and of the same type, with no ghost and not waiting,
keeps the shape of the stack below the head. -/
theorem StackOK_swap_false (p : Params) (marks : Finset (Vertex 3)) (hd : Bool) (f f' : Frame)
    (rest : List Frame) (hS : StackOK p marks hd (f :: rest)) (hv : f'.v = f.v)
    (hR : f'.isR = f.isR) (hk : f'.killing = false) (hg : f'.ghost = none) (hF : FrameOK p f') :
    StackOK p marks false (f' :: rest) := by
  cases rest with
  | nil =>
    obtain ⟨hv0, hR0, -, -, -, -⟩ := hS
    exact ⟨hv.trans hv0, hR.trans hR0, hk, fun h => absurd h (by simp), fun _ => hg, hF⟩
  | cons g s =>
    obtain ⟨hv0, hm, -, -, -, hT⟩ := hS
    refine ⟨?_, hv ▸ hm, fun h => absurd h (by simp), fun _ => ⟨hk, hg⟩, hF, hT⟩
    rw [hv]
    exact hv0

/-- A new head closure, at the same vertex and of the same type, not waiting, with a frog in its
pool or a ghost, keeps the shape of the stack. -/
theorem StackOK_swap_true (p : Params) (marks : Finset (Vertex 3)) (hd : Bool) (f f' : Frame)
    (rest : List Frame) (hS : StackOK p marks hd (f :: rest)) (hv : f'.v = f.v)
    (hR : f'.isR = f.isR) (hk : f'.killing = false) (hne : f'.pool ≠ [] ∨ f'.ghost ≠ none)
    (hF : FrameOK p f') :
    StackOK p marks true (f' :: rest) := by
  cases rest with
  | nil =>
    obtain ⟨hv0, hR0, -, -, -, -⟩ := hS
    exact ⟨hv.trans hv0, hR.trans hR0, hk, fun _ => hne, fun h => absurd h (by simp), hF⟩
  | cons g s =>
    obtain ⟨hv0, hm, -, -, -, hT⟩ := hS
    refine ⟨?_, hv ▸ hm, fun _ => ?_, fun h => absurd h (by simp), hF, hT⟩
    · rw [hv]
      exact hv0
    · simp only [hk, Bool.false_eq_true, false_iff, not_and]
      intro hp hg
      rcases hne with h | h
      · exact h hp
      · exact h hg

/-- A new mark whose parent is marked (or the root) keeps the marks closed under parents. -/
theorem MarksAnc_insert (marks : Finset (Vertex 3)) (z : Vertex 3) (hM : MarksAnc marks)
    (hz : z ≠ []) (ht : z.tail ≠ [] → z.tail ∈ marks) : MarksAnc (insert z marks) := by
  intro u hu
  rw [Finset.mem_insert] at hu
  rcases hu with rfl | hu
  · exact ⟨hz, fun h => Finset.mem_insert_of_mem (ht h)⟩
  · exact ⟨(hM u hu).1, fun h => Finset.mem_insert_of_mem ((hM u hu).2 h)⟩

/-- Marking the children of a marked vertex (or of the root) keeps the marks closed under
parents. -/
theorem MarksAnc_union_kids (marks : Finset (Vertex 3)) (v : Vertex 3) (hM : MarksAnc marks)
    (hv : v ≠ [] → v ∈ marks) : MarksAnc (marks ∪ kids v) := by
  intro u hu
  rw [Finset.mem_union] at hu
  rcases hu with hu | hu
  · exact ⟨(hM u hu).1, fun h => Finset.mem_union_left _ ((hM u hu).2 h)⟩
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨List.cons_ne_nil _ _, fun h => Finset.mem_union_left _ (hv h)⟩

/-- The vertex of the head of a good stack is the root or marked. -/
theorem StackOK_head_mem (p : Params) (marks : Finset (Vertex 3)) (hd : Bool) (f : Frame)
    (rest : List Frame) (hS : StackOK p marks hd (f :: rest)) : f.v ≠ [] → f.v ∈ marks := by
  intro hne
  cases rest with
  | nil => exact absurd hS.1 hne
  | cons g s => exact hS.2.1

/-- A closure below the head neither waits for its kill coin nor has a ghost. -/
theorem StackOK_false_head (p : Params) (marks : Finset (Vertex 3)) (f : Frame) (rest : List Frame)
    (hS : StackOK p marks false (f :: rest)) : f.killing = false ∧ f.ghost = none := by
  cases rest with
  | nil => exact ⟨hS.2.2.1, hS.2.2.2.2.1 rfl⟩
  | cons g s => exact hS.2.2.2.1 rfl

/-- The head of a good stack is within the caps. -/
theorem StackOK_head_frame (p : Params) (marks : Finset (Vertex 3)) (hd : Bool) (f : Frame)
    (rest : List Frame) (hS : StackOK p marks hd (f :: rest)) : FrameOK p f := by
  cases rest with
  | nil => exact hS.2.2.2.2.2
  | cons g s => exact hS.2.2.2.2.1

/-- A step of a ghost walk that neither comes back to `v` nor reaches depth `L` stays strictly
between them. -/
theorem ghostStep_ok (L : ℕ) (v u : Vertex 3) (ξ : Step 3) (hsuf : v <:+ u)
    (h1 : v.length + 1 ≤ u.length) (hL : u.length < v.length + L) (hne : ghostStep u ξ ≠ v)
    (hlen : (ghostStep u ξ).length ≠ v.length + L) :
    v <:+ ghostStep u ξ ∧ v.length + 1 ≤ (ghostStep u ξ).length ∧
      (ghostStep u ξ).length < v.length + L := by
  obtain ⟨w, rfl⟩ := hsuf
  simp only [List.length_append] at h1 hL
  by_cases hx : ξ.2 = 0
  · have hstep : ghostStep (w ++ v) ξ = w.tail ++ v := by
      simp only [ghostStep, hx, ↓reduceDIte]
      cases w with
      | nil => simp at h1
      | cons a w => rfl
    rw [hstep] at hne hlen ⊢
    have hwt : w.tail ≠ [] := fun h => hne (by rw [h, List.nil_append])
    have hpos : 0 < w.tail.length := List.length_pos_iff.mpr hwt
    refine ⟨⟨w.tail, rfl⟩, ?_, ?_⟩ <;> simp only [List.length_append, List.length_tail] at hpos ⊢ <;> omega
  · have hstep : ghostStep (w ++ v) ξ = (ξ.2.pred hx :: w) ++ v := by
      simp [ghostStep, hx]
    rw [hstep] at hlen ⊢
    simp only [List.length_append, List.length_cons] at hlen ⊢
    exact ⟨⟨ξ.2.pred hx :: w, rfl⟩, by omega, by omega⟩

/-- The read of an up. -/
theorem upd_up (p : Params) (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3))
    (out : List Frog) (x : Val) (hk : f.killing = false) (hg : f.ghost = none) (φ : Frog)
    (ps : List Frog) (hp : f.pool = φ :: ps) (hx : x.1.2 = 0) :
    upd p ⟨f :: rest, marks, out⟩ x =
      settle marks ({f with pool := ps, ups := if f.ups.length < p.V then f.ups ++ [φ] else f.ups} ::
        rest) := by
  simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]

/-- The read of a kill coin. -/
theorem upd_kill (p : Params) (f g : Frame) (rest : List Frame) (marks : Finset (Vertex 3))
    (out : List Frog) (x : Val) (hk : f.killing = true) :
    upd p ⟨f :: g :: rest, marks, out⟩ x =
      settle (if p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v) x.2
          then marks else marks ∪ kids f.v)
        ({g with pool := (g.pool ++ if p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length
          (unmarked marks f.v) x.2 then f.ups else []).take p.P} :: rest) := by
  simp only [upd, hk, ↓reduceIte]

/-- A read sending the head's frog up keeps the state good. -/
theorem good_up (p : Params) (_hL : 2 ≤ p.L) (_hP : 2 ≤ p.P) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : (⟨f :: rest, marks, out⟩ : St) ∈ Good p)
    (hk : f.killing = false) (hg : f.ghost = none) (φ : Frog) (ps : List Frog)
    (hp : f.pool = φ :: ps) (hx : x.1.2 = 0) :
    upd p ⟨f :: rest, marks, out⟩ x ∈ Good p := by
  obtain ⟨hM, hS, -⟩ := hs
  obtain ⟨hP0, hV0, hm0, -⟩ := StackOK_head_frame p marks true f rest hS
  rw [upd_up p f rest marks out x hk hg φ ps hp hx]
  refine settle_good p marks _ rest hM (StackOK_swap_false p marks true f _ rest hS rfl rfl (by simp [hk]) (by simp [hg])
    ⟨?_, ?_, hm0, fun φ' u h => by simp [hg] at h⟩)
  · rw [hp] at hP0
    simp only [List.length_cons] at hP0 ⊢
    omega
  · simp only
    split_ifs with h
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · exact hV0

/-- A read starting a ghost walk keeps the state good. -/
theorem good_ghost_entry (p : Params) (hL : 2 ≤ p.L) (_hP : 2 ≤ p.P) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : (⟨f :: rest, marks, out⟩ : St) ∈ Good p)
    (hk : f.killing = false) (hg : f.ghost = none) (φ : Frog) (ps : List Frog)
    (hp : f.pool = φ :: ps) (hx : x.1.2 ≠ 0)
    (hge : f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx :: f.v ∈ marks)) :
    upd p ⟨f :: rest, marks, out⟩ x ∈ Good p := by
  obtain ⟨hM, hS, -⟩ := hs
  obtain ⟨hP0, hV0, hm0, -⟩ := StackOK_head_frame p marks true f rest hS
  have hpl : ps.length + 1 ≤ p.P := by rw [hp] at hP0; simpa using hP0
  simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, hge]
  refine ⟨hM, StackOK_swap_true p marks true f _ rest hS rfl rfl (by simp) (Or.inr (by simp))
    ⟨by simp only; omega, hV0, hm0, ?_⟩, fun h => by simp at h⟩
  intro φ' u h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨List.suffix_cons _ _, by simp, by simp only [List.length_cons]; omega, by simp only; omega⟩

/-- A read entering an unmarked child keeps the state good. -/
theorem good_R (p : Params) (_hL : 2 ≤ p.L) (hP : 2 ≤ p.P) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : (⟨f :: rest, marks, out⟩ : St) ∈ Good p)
    (hk : f.killing = false) (hg : f.ghost = none) (φ : Frog) (ps : List Frog)
    (hp : f.pool = φ :: ps) (hx : x.1.2 ≠ 0)
    (hnot : ¬(f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx :: f.v ∈ marks)))
    (hz : x.1.2.pred hx :: f.v ∉ marks) :
    upd p ⟨f :: rest, marks, out⟩ x ∈ Good p := by
  obtain ⟨hM, hS, -⟩ := hs
  obtain ⟨hP0, hV0, hm0, -⟩ := StackOK_head_frame p marks true f rest hS
  have hpl : ps.length + 1 ≤ p.P := by rw [hp] at hP0; simpa using hP0
  have hlt : f.v.length < p.m := by
    rcases Nat.lt_or_ge f.v.length p.m with h | h
    · exact h
    · exact absurd (Or.inl (by omega)) hnot
  simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  rw [ite_eq_right hnot, ite_eq_left hz]
  set z := x.1.2.pred hx :: f.v with hzdef
  refine ⟨MarksAnc_insert marks z hM (List.cons_ne_nil _ _)
      (fun h => StackOK_head_mem p marks true f rest hS h), ?_, fun h => by simp at h⟩
  refine ⟨rfl, Finset.mem_insert_self _ _, fun _ => by simp, fun h => absurd h (by simp),
    ⟨by simp only [List.length_cons, List.length_nil]; omega, by simp, by
      simp only [hzdef, List.length_cons]; omega, fun φ' u h => by simp at h⟩, ?_⟩
  exact StackOK_swap_false p (insert z marks) true f _ rest
    (StackOK_mono p marks (insert z marks) (Finset.subset_insert _ _) true _ hS) rfl rfl (by simp) (by simp)
    ⟨by simp only; omega, hV0, hm0, fun φ' u h => by simp at h⟩

/-- A read entering a marked child of an R closure keeps the state good. -/
theorem good_H (p : Params) (_hL : 2 ≤ p.L) (hP : 2 ≤ p.P) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : (⟨f :: rest, marks, out⟩ : St) ∈ Good p)
    (hk : f.killing = false) (hg : f.ghost = none) (φ : Frog) (ps : List Frog)
    (hp : f.pool = φ :: ps) (hx : x.1.2 ≠ 0)
    (hnot : ¬(f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx :: f.v ∈ marks)))
    (hz : x.1.2.pred hx :: f.v ∈ marks) :
    upd p ⟨f :: rest, marks, out⟩ x ∈ Good p := by
  obtain ⟨hM, hS, -⟩ := hs
  obtain ⟨hP0, hV0, hm0, -⟩ := StackOK_head_frame p marks true f rest hS
  have hpl : ps.length + 1 ≤ p.P := by rw [hp] at hP0; simpa using hP0
  have hlt : f.v.length < p.m := by
    rcases Nat.lt_or_ge f.v.length p.m with h | h
    · exact h
    · exact absurd (Or.inl (by omega)) hnot
  simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  rw [ite_eq_right hnot, ite_eq_right (not_not.mpr hz)]
  refine ⟨hM, ?_, fun h => by simp at h⟩
  refine ⟨rfl, hz, fun _ => by simp, fun h => absurd h (by simp),
    ⟨by simp only [List.length_cons, List.length_nil]; omega, by simp, by
      simp only [List.length_cons]; omega, fun φ' u h => by simp at h⟩, ?_⟩
  exact StackOK_swap_false p marks true f _ rest hS rfl rfl (by simp) (by simp)
    ⟨by simp only; omega, hV0, hm0, fun φ' u h => by simp at h⟩

/-- A read of a ghost walk keeps the state good. -/
theorem good_ghost (p : Params) (_hL : 2 ≤ p.L) (_hP : 2 ≤ p.P) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : (⟨f :: rest, marks, out⟩ : St) ∈ Good p)
    (hk : f.killing = false) (φ : Frog) (u : Vertex 3) (hg : f.ghost = some (φ, u)) :
    upd p ⟨f :: rest, marks, out⟩ x ∈ Good p := by
  obtain ⟨hM, hS, -⟩ := hs
  obtain ⟨hP0, hV0, hm0, hgh⟩ := StackOK_head_frame p marks true f rest hS
  obtain ⟨hsuf, h1, hL', hP1⟩ := hgh φ u hg
  simp only [upd, hk, hg, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h1' h2'
  · refine ⟨hM, StackOK_swap_true p marks true f _ rest hS rfl rfl (by simp) (Or.inl (by simp))
      ⟨by simp only [List.length_cons]; omega, hV0, hm0, fun φ' u h => by simp at h⟩,
      fun h => by simp at h⟩
  · exact settle_good p marks _ rest hM (StackOK_swap_false p marks true f _ rest hS rfl rfl (by simp) rfl
      ⟨hP0, hV0, hm0, fun φ' u h => by simp at h⟩)
  · obtain ⟨hs1, hs2, hs3⟩ := ghostStep_ok p.L f.v u x.1 hsuf h1 hL' h1' h2'
    refine ⟨hM, StackOK_swap_true p marks true f _ rest hS rfl rfl (by simp) (Or.inr (by simp))
      ⟨hP0, hV0, hm0, ?_⟩, fun h => by simp at h⟩
    intro φ' u' h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hs1, hs2, hs3, hP1⟩

/-- A kill coin keeps the state good. -/
theorem good_kill (p : Params) (_hL : 2 ≤ p.L) (_hP : 2 ≤ p.P) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : (⟨f :: rest, marks, out⟩ : St) ∈ Good p)
    (hk : f.killing = true) :
    upd p ⟨f :: rest, marks, out⟩ x ∈ Good p := by
  obtain ⟨hM, hS, -⟩ := hs
  cases rest with
  | nil =>
    have := hS.2.2.1
    rw [hk] at this
    exact absurd this (by simp)
  | cons g rest' =>
    rw [upd_kill p f g rest' marks out x hk]
    obtain ⟨-, hfm, -, -, -, hT⟩ := hS
    obtain ⟨hgk, hgg⟩ := StackOK_false_head p marks g rest' hT
    obtain ⟨-, hV0, hm0, -⟩ := StackOK_head_frame p marks false g rest' hT
    have hsub : marks ⊆ (if p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v) x.2
        then marks else marks ∪ kids f.v) := by
      split_ifs
      · exact subset_rfl
      · exact Finset.subset_union_left
    refine settle_good p _ _ rest' ?_ (StackOK_swap_false p _ false g _ rest'
      (StackOK_mono p marks _ hsub false _ hT) rfl rfl hgk hgg
      ⟨by simp only [List.length_take]; omega, hV0, hm0, fun φ' u h => by simp [hgg] at h⟩)
    split_ifs
    · exact hM
    · exact MarksAnc_union_kids marks f.v hM (fun _ => hfm)

/-- With cost `0` per read the additive term is `0`. -/
theorem addC_zero (p : Params) (h : ℕ) (r : Bool) :
    addC p 0 h r (cinp p 0 h) = fun _ => 0 := by
  have hcinp : FrogModel.D3.cinp p 0 h = (0, fun _ => 0) := by
    induction' h with h ih
    · rfl
    · rw [FrogModel.D3.cinp, costs_zero p h]
  rw [hcinp]
  ext k
  unfold FrogModel.D3.addC
  simp
  refine Finset.sum_eq_zero ?_
  intro c'
  cases k c' with
  | none => simp
  | some t => simp

/-- The value of a closure with a nonnegative end value is nonnegative. -/
theorem fv_nonneg (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (hc : 0 ≤ c) (h : ℕ)
    (T : Kid → ℕ → ℝ) (hT : ∀ k a, 0 ≤ T k a) (s : Sm) : 0 ≤ fv p c h T s := by
  have h_inp := inp_ok p hL hV h
  rcases h_inp with ⟨hρ0, -, hK0, hK1, -⟩
  have hp := pL_mem p.L hL
  rcases hp with ⟨hp0, hp1⟩
  have hg : 0 ≤ gcost p.L 1 := by
    unfold gcost
    positivity
  have hadd : ∀ (r : Bool) (k : Kid), 0 ≤ addC p c h r (cinp p c h) k := by
    intro r k
    unfold addC
    refine add_nonneg hc (Finset.sum_nonneg fun c' _ => mul_nonneg (by norm_num) ?_)
    rcases k c' with _ | t
    · have := costs_nonneg p hL hV c hc h
      exact this.1
    · simp only
      split_ifs
      · have := costs_nonneg p hL hV c hc h
        exact this.2 t
      · exact mul_nonneg hc hg
  have hG (r : Bool) (k : Kid) (n a : ℕ) : 0 ≤ GenH p h r (inp p h) (addC p c h r (cinp p c h)) T k n a := by
    unfold GenH
    exact Gen_nonneg p.V p.P (isRe h r) (pL p.L) (inp p h).1 (inp p h).2
      (addC p c h r (cinp p c h)) T hρ0 hK0 hK1 hp0 hp1 (hadd r) hT k n a
  by_cases hd : s.d = 0
  · rw [fv_d0 p c h T s hd]
    exact hG s.isR s.kid s.n s.a
  · rw [fv_ghost p c h T s hd]
    have hg_nonneg : 0 ≤ gcost p.L s.d := by
      unfold gcost
      positivity
    have hrL := rL_facts p.L hL
    rcases hrL with ⟨_, _, _, _, hrL_bounds⟩
    have hrL0 : 0 ≤ rL p.L s.d := (hrL_bounds s.d).1
    have hrL1 : rL p.L s.d ≤ 1 := (hrL_bounds s.d).2
    have hG1 : 0 ≤ GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) T s.kid (s.n + 1) s.a :=
      hG s.isR s.kid (s.n + 1) s.a
    have hG2 : 0 ≤ GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) T s.kid s.n s.a :=
      hG s.isR s.kid s.n s.a
    have hsum : 0 ≤ c * gcost p.L s.d + rL p.L s.d * GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) T s.kid (s.n + 1) s.a +
      (1 - rL p.L s.d) * GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) T s.kid s.n s.a := by
      refine add_nonneg (add_nonneg ?_ ?_) ?_
      · exact mul_nonneg hc hg_nonneg
      · exact mul_nonneg hrL0 hG1
      · have : 0 ≤ 1 - rL p.L s.d := by linarith
        exact mul_nonneg this hG2
    exact hsum

/-- The candidate on a stack of summaries is nonnegative. -/
theorem fold_nonneg (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (hc : 0 ≤ c)
    (top : ℕ → ℝ) (htop : ∀ a, 0 ≤ top a) (l : List Sm) (h : ℕ) :
    0 ≤ fold p c top h l := by
  refine (Nat.strong_induction_on (p := fun m => ∀ (l' : List FrogModel.D3.Sm), l'.length = m → ∀ (h' : ℕ), 0 ≤ FrogModel.D3.fold p c top h' l') l.length ?_ l rfl h)
  intro n ih l' hlen h'
  match l' with
  | [] =>
    rw [FrogModel.D3.fold]
  | f :: rest =>
    match rest with
    | [] =>
      rw [FrogModel.D3.fold]
      exact fv_nonneg p hL hV c hc h' (fun _ a => top a) (fun k a => htop a) _
    | g :: rest' =>
      rw [FrogModel.D3.fold]
      have h_nonneg : ∀ k a, 0 ≤ c + ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
        killP (κm p f.isR h' f.f0 a (nN k)) a (nN k) b f' *
          FrogModel.D3.fold p c top (h' + 1) (FrogModel.D3.applyO p.P b f' f.slot g :: rest') := by
        intro k a
        refine add_nonneg hc ?_
        refine Finset.sum_nonneg fun b _ => ?_
        refine Finset.sum_nonneg fun f' _ => ?_
        have hkm := κm_mem p f.isR h' f.f0 a (nN k)
        have hkill : 0 ≤ killP (κm p f.isR h' f.f0 a (nN k)) a (nN k) b f' :=
          killP_nonneg (κm p f.isR h' f.f0 a (nN k)) hkm.1 hkm.2 a (nN k) b f'
        have hlen_lt : (FrogModel.D3.applyO p.P b f' f.slot g :: rest').length < (f :: g :: rest').length := by
          simp
        have hlen_lt_n : (FrogModel.D3.applyO p.P b f' f.slot g :: rest').length < n := by
          calc
            (FrogModel.D3.applyO p.P b f' f.slot g :: rest').length < (f :: g :: rest').length := hlen_lt
            _ = n := hlen
        have h_ih := ih ((FrogModel.D3.applyO p.P b f' f.slot g :: rest').length) hlen_lt_n (FrogModel.D3.applyO p.P b f' f.slot g :: rest') rfl (h' + 1)
        exact mul_nonneg hkill h_ih
      exact fv_nonneg p hL hV c hc h' _ h_nonneg _

/-- With cost `0` the value of a closure is linear in its end value. -/
theorem fv_sum0 (p : Params) {ι : Type} [DecidableEq ι] (s : Finset ι) (h : ℕ)
    (T : ι → Kid → ℕ → ℝ) (sm : Sm) :
    fv p 0 h (fun k a => ∑ i ∈ s, T i k a) sm = ∑ i ∈ s, fv p 0 h (T i) sm := by
  have hG : ∀ n, GenH p h sm.isR (inp p h) (addC p 0 h sm.isR (cinp p 0 h))
      (fun k a => ∑ i ∈ s, T i k a) sm.kid n sm.a =
      ∑ i ∈ s, GenH p h sm.isR (inp p h) (addC p 0 h sm.isR (cinp p 0 h)) (T i) sm.kid n sm.a := by
    intro n
    unfold GenH
    rw [addC_zero]
    have := Gen_sum0 p.V p.P (isRe h sm.isR) (pL p.L) (inp p h).1 (inp p h).2 s (fun _ => 1) T
      sm.kid n sm.a
    simp only [one_mul] at this
    exact this
  unfold fv
  split_ifs
  · exact hG _
  · rw [hG, hG, Finset.mul_sum, Finset.mul_sum]
    simp only [zero_mul, zero_add]
    rw [← Finset.sum_add_distrib]

/-- With cost `0` and end value `1` at ups `≤ V`, the value of a closure with ups `≤ V` is `1`. -/
theorem fv_one (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (h : ℕ) (T : Kid → ℕ → ℝ)
    (hT : ∀ k a, a ≤ p.V → T k a = 1) (sm : Sm) (ha : sm.a ≤ p.V) : fv p 0 h T sm = 1 := by
  obtain ⟨-, hρ1, hK0, hK1, hK, -, -⟩ := inp_ok p hL hV h
  obtain ⟨hp0, hp1⟩ := pL_mem p.L hL
  have hG : ∀ n, GenH p h sm.isR (inp p h) (addC p 0 h sm.isR (cinp p 0 h)) T sm.kid n sm.a = 1 := by
    intro n
    unfold GenH
    rw [addC_zero, Gen_congr _ _ _ _ _ _ _ T (fun _ _ => 1) (fun k a ha => hT k a ha) _ _ _ ha]
    exact Gen_one _ _ _ _ _ _ hρ1 hK (fun t => hK0 t 1 t) hK1 hp0 hp1 _ _ _
  unfold fv
  split_ifs
  · exact hG _
  · rw [hG, hG]
    ring


/-- With cost `0` the candidate is linear in the value at the end of the run. -/
theorem fold_lin (p : Params) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (top : ι → ℕ → ℝ) (l : List Sm) (h : ℕ) :
    fold p 0 (fun a => ∑ i ∈ s, top i a) h l = ∑ i ∈ s, fold p 0 (top i) h l := by
  cases l with
  | nil => simp [fold]
  | cons s0 L =>
    induction L generalizing h s0 with
    | nil =>
      simp only [fold]
      exact fv_sum0 p s h (fun i _ a => top i a) s0
    | cons g rest ih =>
      simp only [fold]
      simp only [ih]
      rw [← fv_sum0 p s h]
      congr 1
      funext k a
      simp only [zero_add, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact Finset.sum_comm

/-- With cost `0` and value `1` at the end of the run (at ups `≤ V`), the candidate is `1`. -/
theorem fold_one (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (top : ℕ → ℝ)
    (htop : ∀ a, a ≤ p.V → top a = 1) (l : List Sm) (hl : l ≠ [])
    (ha : ∀ s ∈ l, s.a ≤ p.V) (h : ℕ) : fold p 0 top h l = 1 := by
  obtain ⟨s0, L, rfl⟩ := List.exists_cons_of_ne_nil hl
  clear hl
  induction L generalizing h s0 with
  | nil =>
    simp only [fold]
    exact fv_one p hL hV h _ (fun k a ha => htop a ha) s0 (ha s0 (by simp))
  | cons g rest ih =>
    simp only [fold]
    refine fv_one p hL hV h _ (fun k a ha' => ?_) s0 (ha s0 (by simp))
    have hin : ∀ (b : ℕ) (f' : Fin 4),
        fold p 0 top (h + 1) (applyO p.P b f' s0.slot g :: rest) = 1 := by
      intro b f'
      refine ih (h + 1) (applyO p.P b f' s0.slot g) (fun s hs => ?_)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ha g (by simp)
      · exact ha s (by simp [hs])
    simp only [hin, mul_one, zero_add]
    exact killP_sum p.V _ a (nN k) ha' (nN_lt k)

end FrogModel.D3
