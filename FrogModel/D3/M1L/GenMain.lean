module

public import FrogModel.D3.M1L.GenGood
public import FrogModel.D3.M1L.Height1Law

@[expose] public section

/-!
# M1_L at every height: the law of the run (Lemma 13.2 of the paper)

The machine reads a direction and a coin (`updD`), and the candidate `Ucand` (the function `U_b` of
the proof of Lemma 13.2 at cost `0`, and `τ` at cost `1`) is a supersolution of one read at every
good state: a round of the head closure (`read_round`, an equation), a step of its ghost walk
(`read_ghost`, an inequality from the cost of the walk) or its kill coin (`read_kill`, an
equation). With cost `0` the candidates of the outcomes `b ≤ V` sum to `1`, so `chain_law` gives
the law of the count at the end of the run; with cost `1` the candidate bounds the expected number
of reads. On the frog paths, at the initial state, the law of the count is
`GenH` at the height `m` of the top closure (`top_law_gen`).
-/

open MeasureTheory ProbabilityTheory FrogModel
open scoped ENNReal

namespace FrogModel.D3

instance : Countable St := countable_St

/-- The machine driven by a direction and a coin. -/
def updD (p : Params) (s : St) (y : Fin 4 × ℕ) : St := upd p s ((0, y.1), y.2)

theorem run_traj (p : Params) (k : ℕ) (y : ℕ → Val) (n : ℕ) :
    run p k y n = Engine.traj (updD p) (init k) (fun t => ((y t).1.2, (y t).2)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, Engine.traj] at ih ⊢
    rw [ih, upd_dc]
    rfl

/-- A head that does not wait for its kill coin does not read the coin. -/
theorem upd_coin (p : Params) (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3))
    (out : List Frog) (hk : f.killing = false) (x : Val) :
    upd p ⟨f :: rest, marks, out⟩ x = upd p ⟨f :: rest, marks, out⟩ (x.1, 0) := by
  simp only [upd, hk, Bool.false_eq_true, ↓reduceIte]

theorem Ucand_nonneg (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (hc : 0 ≤ c)
    (top : ℕ → ℝ) (htop : ∀ a, 0 ≤ top a) (s : St) : 0 ≤ Ucand p c top s := by
  unfold Ucand
  split
  · exact htop _
  · exact fold_nonneg p hL hV c hc top htop _ _

/-- A ghost entry into the child `c'` is the round of `Gen` into that child. -/
theorem ghost_entry_childV (p : Params) (hL : 1 ≤ p.L) (c : ℝ) (marks : Finset (Vertex 3))
    (v : Vertex 3) (r : Bool) (T : Kid → ℕ → ℝ) (n a : ℕ) (c' : Fin 3)
    (hge : v.length = p.m ∨ (r = false ∧ c' :: v ∈ marks)) (_hle : v.length ≤ p.m) :
    childV p c (p.m - v.length) r T (kidM p marks v none) (n + 1) a c' =
      c * gcost p.L 1 + rL p.L 1 * GenH p (p.m - v.length) r (inp p (p.m - v.length))
          (addC p c (p.m - v.length) r (cinp p c (p.m - v.length))) T (kidM p marks v none) (n + 1) a +
        (1 - rL p.L 1) * GenH p (p.m - v.length) r (inp p (p.m - v.length))
          (addC p c (p.m - v.length) r (cinp p c (p.m - v.length))) T (kidM p marks v none) n a := by
  have hR : isRe (p.m - v.length) r = false := by
    rcases hge with h | ⟨h, -⟩
    · simp [isRe, show p.m - v.length = 0 by omega]
    · simp [isRe, h]
  obtain ⟨t, ht⟩ : ∃ t, kidM p marks v none c' = some t := by
    unfold kidM
    rcases hge with h | ⟨-, h⟩
    · exact ⟨0, by simp [show p.m - v.length = 0 by omega]⟩
    · split_ifs <;> simp_all
  simp only [childV, ht, hR, Bool.false_eq_true, ↓reduceIte, bodyG, Nat.add_sub_cancel]
  rw [(rL_facts p.L hL).2.2.1]

/-- A read into the child `c'` of a head with no ghost: the round of `Gen` into that child. -/
theorem step_child (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (hM : MarksAnc marks) (hch : Chain (f :: rest))
    (hle : f.v.length ≤ p.m) (hP : f.pool.length ≤ p.P) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (c' : Fin 3) :
    Ucand p c top (upd p ⟨f :: rest, marks, out⟩ ((0, c'.succ), 0)) =
      childV p c (p.m - f.v.length) f.isR
        (contF p c top (p.m - f.v.length) f.isR f.f0 (f.v.headD 0) (projS p marks f.v.head? rest))
        (kidM p marks f.v none) (ps.length + 1) f.ups.length c' := by
  have hx : ((((0 : Fin 3), c'.succ), (0 : ℕ)) : Val).1.2 ≠ 0 := Fin.succ_ne_zero c'
  have hpred : ((((0 : Fin 3), c'.succ), (0 : ℕ)) : Val).1.2.pred hx = c' := Fin.pred_succ c'
  by_cases hge : f.v.length = p.m ∨ (f.isR = false ∧ c' :: f.v ∈ marks)
  · rw [step_ghost_entry p c top f rest marks out _ hk hg φ ps hp hx (by rw [hpred]; exact hge),
      ghost_entry_childV p hL c marks f.v f.isR _ ps.length f.ups.length c' hge hle]
    rfl
  · have hnot : ¬(f.v.length = p.m ∨
        (f.isR = false ∧ ((((0 : Fin 3), c'.succ), (0 : ℕ)) : Val).1.2.pred hx :: f.v ∈ marks)) := by
      rw [hpred]; exact hge
    by_cases hz : c' :: f.v ∈ marks
    · rw [step_H p hkeep0 hL hV c top f rest marks out _ hk hg φ ps hp hx hnot
        (by rw [hpred]; exact hz) hle hP, hpred]
    · rw [step_R p c top f rest marks out _ hk hg φ ps hp hx hnot (by rw [hpred]; exact hz) hM hch
        hle, hpred]

/-- A round of the head closure: the candidate is the cost of the read plus the mean over the
direction. -/
theorem read_round (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (hM : MarksAnc marks) (hch : Chain (f :: rest))
    (hle : f.v.length ≤ p.m) (hP : f.pool.length ≤ p.P) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) :
    c + ∑ d : Fin 4, 1 / 4 * Ucand p c top (upd p ⟨f :: rest, marks, out⟩ ((0, d), 0)) =
      Ucand p c top ⟨f :: rest, marks, out⟩ := by
  have hin := inp_ok p hL hV (p.m - f.v.length)
  rw [Fin.sum_univ_succ, step_up p c top f rest marks out _ hk hg φ ps hp rfl]
  simp only [step_child p hkeep0 hL hV c top f rest marks out hM hch hle hP hk hg φ ps hp]
  rw [Ucand_head p c top f rest marks out hg, hp, List.length_cons]
  simp only [headX]
  rw [round_id p hL c (p.m - f.v.length) f.isR _ (fun t => hin.2.2.1 t 1 t) hin.2.2.2.1
    (kidM p marks f.v none) (ps.length + 1) f.ups.length (Nat.succ_ne_zero _), Nat.add_sub_cancel]
  ring

/-- The value of the head inside its ghost walk. -/
theorem ghostV_mid (p : Params) (c A B : ℝ) (e : ℕ) (h0 : e ≠ 0) (hL : e ≠ p.L) :
    ghostV p c A B e = c * gcost p.L e + rL p.L e * A + (1 - rL p.L e) * B := by
  simp [ghostV, h0, hL]

/-- A step of the ghost walk of the head: the candidate is at least the cost of the read plus the
mean over the direction. -/
theorem read_ghost (p : Params) (hL : 2 ≤ p.L) (c : ℝ) (hc : 0 ≤ c) (top : ℕ → ℝ) (f : Frame)
    (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) (hk : f.killing = false)
    (φ : Frog) (u : Vertex 3) (hg : f.ghost = some (φ, u)) (hsuf : f.v <:+ u)
    (hd1 : f.v.length + 1 ≤ u.length) (hdL : u.length < f.v.length + p.L) :
    c + ∑ d : Fin 4, 1 / 4 * Ucand p c top (upd p ⟨f :: rest, marks, out⟩ ((0, d), 0)) ≤
      Ucand p c top ⟨f :: rest, marks, out⟩ := by
  simp only [Fin.sum_univ_four]
  rw [step_ghost p c top f rest marks out _ hk φ u hg hsuf hd1 hdL,
    step_ghost p c top f rest marks out _ hk φ u hg hsuf hd1 hdL,
    step_ghost p c top f rest marks out _ hk φ u hg hsuf hd1 hdL,
    step_ghost p c top f rest marks out _ hk φ u hg hsuf hd1 hdL,
    Ucand_head_ghost p c top f rest marks out φ u hg (by omega)]
  have h1 : ((((0 : Fin 3), (1 : Fin 4)), (0 : ℕ)) : Val).1.2 ≠ 0 := by decide
  have h2 : ((((0 : Fin 3), (2 : Fin 4)), (0 : ℕ)) : Val).1.2 ≠ 0 := by decide
  have h3 : ((((0 : Fin 3), (3 : Fin 4)), (0 : ℕ)) : Val).1.2 ≠ 0 := by decide
  rw [ite_eq_left rfl, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  have hi := ghost_ineq p hL (u.length - f.v.length) (by omega) (by omega) c hc
    (headX p c top marks f rest (kidM p marks f.v none) (f.pool.length + 1) f.ups.length)
    (headX p c top marks f rest (kidM p marks f.v none) f.pool.length f.ups.length)
  rw [ghostV_mid p c _ _ (u.length - f.v.length) (by omega) (by omega)] at hi
  linarith

/-- The kill coin of the head: the candidate is the cost of the read plus the mean over the
coin. -/
theorem read_kill (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (hc : 0 ≤ c) (top : ℕ → ℝ) (htop : ∀ a, 0 ≤ top a)
    (f g : Frame) (rest' : List Frame) (marks : Finset (Vertex 3)) (out : List Frog)
    (hk : f.killing = true) (hp : f.pool = []) (hg : f.ghost = none) (hgg : g.ghost = none)
    (hv : f.v = f.v.headD 0 :: g.v) (hfm : f.v ∈ marks) (hle : f.v.length ≤ p.m)
    (hgP : g.pool.length ≤ p.P) (hch : Chain (g :: rest')) (ha : f.ups.length ≤ p.V) :
    ENNReal.ofReal c + ∫⁻ ξ, ENNReal.ofReal (Ucand p c top (updD p ⟨f :: g :: rest', marks, out⟩ ξ))
        ∂(dirLaw.prod coinLaw) =
      ENNReal.ofReal (Ucand p c top ⟨f :: g :: rest', marks, out⟩) := by
  have hA := fold_nonneg p hL hV c hc top htop
    (applyO p.P f.ups.length ⟨nN (kidM p marks f.v none), nN_lt _⟩ (f.v.headD 0)
      (sm p marks (some (f.v.headD 0)) g) :: projS p marks g.v.head? rest') (p.m - f.v.length + 1)
  have hB := fold_nonneg p hL hV c hc top htop
    (applyO p.P 0 0 (f.v.headD 0) (sm p marks (some (f.v.headD 0)) g) :: projS p marks g.v.head? rest')
    (p.m - f.v.length + 1)
  have hκ := κm_mem p f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v)
  rw [lintegral_ofReal_coin
    (fun j => p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v) j)
    (popV p c top marks f g rest' f.ups.length ⟨nN (kidM p marks f.v none), nN_lt _⟩)
    (popV p c top marks f g rest' 0 0) hA hB
    (fun ξ => ENNReal.ofReal (Ucand p c top (updD p ⟨f :: g :: rest', marks, out⟩ ξ)))
    (fun d j => by
      simp only [updD]
      rw [step_kill p c top f g rest' marks out _ hk hgg hv hfm hle hgP hch])]
  rw [← ENNReal.ofReal_add hc (by unfold κm at hκ; unfold popV; nlinarith),
    kill_value p hkeep0 c top f g rest' marks out hp hg hv hle ha]
  unfold κm
  congr 1
  ring

/-- The facts on the head of a good stack. -/
theorem head_facts (p : Params) (marks : Finset (Vertex 3)) (f : Frame) (rest : List Frame)
    (hS : StackOK p marks true (f :: rest)) :
    FrameOK p f ∧ (f.killing = false → f.pool ≠ [] ∨ f.ghost ≠ none) ∧
      (f.killing = true → ∃ g rest', rest = g :: rest' ∧ f.pool = [] ∧ f.ghost = none ∧
        g.ghost = none ∧ f.v = f.v.headD 0 :: g.v ∧ f.v ∈ marks ∧ FrameOK p g) := by
  cases rest with
  | nil =>
    obtain ⟨-, -, hk, hpg, -, hF⟩ := hS
    refine ⟨hF, fun _ => hpg rfl, fun h => by simp [hk] at h⟩
  | cons g rest' =>
    obtain ⟨hv, hfm, hkill, -, hF, hS'⟩ := hS
    have hg : g.ghost = none ∧ FrameOK p g := by
      cases rest' with
      | nil => exact ⟨hS'.2.2.2.2.1 rfl, hS'.2.2.2.2.2⟩
      | cons _ _ => exact ⟨(hS'.2.2.2.1 rfl).2, hS'.2.2.2.2.1⟩
    refine ⟨hF, fun h => ?_, fun h => ⟨g, rest', rfl, ((hkill rfl).1 h).1, ((hkill rfl).1 h).2, hg.1,
      hv, hfm, hg.2⟩⟩
    by_contra hc
    push Not at hc
    have := (hkill rfl).2 hc
    simp [h] at this

/-- **One read at a good state**: the cost of the read plus the mean of the candidate after it is
at most the candidate. -/
theorem read_le (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (hL : 2 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (hc : 0 ≤ c) (top : ℕ → ℝ) (htop : ∀ a, 0 ≤ top a)
    (s : St) (hs : s ∈ Good p) (hne : s.stack ≠ []) :
    ENNReal.ofReal c + ∫⁻ ξ, ENNReal.ofReal (Ucand p c top (updD p s ξ)) ∂(dirLaw.prod coinLaw) ≤
      ENNReal.ofReal (Ucand p c top s) := by
  obtain ⟨stack, marks, out⟩ := s
  obtain ⟨hM, hS, -⟩ := hs
  have hL1 : 1 ≤ p.L := by omega
  cases stack with
  | nil => exact absurd rfl hne
  | cons f rest =>
    have hch := StackOK.chain p marks true _ hS
    obtain ⟨hF, hnk, hkf⟩ := head_facts p marks f rest hS
    cases hk : f.killing
    · -- a read of the head's frog or of its ghost
      have hdir : ∫⁻ ξ, ENNReal.ofReal (Ucand p c top (updD p ⟨f :: rest, marks, out⟩ ξ))
          ∂(dirLaw.prod coinLaw) = ENNReal.ofReal
            (∑ d : Fin 4, 1 / 4 * Ucand p c top (upd p ⟨f :: rest, marks, out⟩ ((0, d), 0))) :=
        lintegral_ofReal_dir _ (fun d => Ucand_nonneg p hL1 hV c hc top htop _) _ (fun d j => by
          simp only [updD]
          rw [upd_coin p f rest marks out hk])
      rw [hdir, ← ENNReal.ofReal_add hc (Finset.sum_nonneg fun d _ => by
        have := Ucand_nonneg p hL1 hV c hc top htop (upd p ⟨f :: rest, marks, out⟩ ((0, d), 0))
        positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      cases hg : f.ghost with
      | some pu =>
        obtain ⟨φ, u⟩ := pu
        obtain ⟨hsuf, hd1, hdL, -⟩ := hF.2.2.2 φ u hg
        exact read_ghost p hL c hc top f rest marks out hk φ u hg hsuf hd1 hdL
      | none =>
        cases hp : f.pool with
        | nil => exact absurd hg (by simpa [hp] using hnk hk)
        | cons φ ps =>
          exact (read_round p hkeep0 hL1 hV c top f rest marks out hM hch hF.2.2.1
            hF.1 hk hg φ ps hp).le
    · obtain ⟨g, rest', rfl, hp, hg, hgg, hv, hfm, hgF⟩ := hkf hk
      exact (read_kill p hkeep0 hL1 hV c hc top htop f g rest' marks out hk hp hg hgg hv hfm
        hF.2.2.1 hgF.1 (by cases hch; assumption) hF.2.1).le

/-- The good states are kept by every read. -/
theorem good_upd (p : Params) (hL : 2 ≤ p.L) (hP : 2 ≤ p.P) (s : St) (hs : s ∈ Good p)
    (x : Val) : upd p s x ∈ Good p := by
  obtain ⟨stack, marks, out⟩ := s
  cases stack with
  | nil => exact hs
  | cons f rest =>
    cases hk : f.killing
    · cases hg : f.ghost with
      | some pu =>
        obtain ⟨φ, u⟩ := pu
        exact good_ghost p hL hP f rest marks out x hs hk φ u hg
      | none =>
        cases hp : f.pool with
        | nil =>
          have : upd p ⟨f :: rest, marks, out⟩ x = ⟨f :: rest, marks, out⟩ := by
            simp [upd, hk, hg, hp]
          rw [this]; exact hs
        | cons φ ps =>
          by_cases hx : x.1.2 = 0
          · exact good_up p hL hP f rest marks out x hs hk hg φ ps hp hx
          · by_cases hge : f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx :: f.v ∈ marks)
            · exact good_ghost_entry p hL hP f rest marks out x hs hk hg φ ps hp hx hge
            · by_cases hz : x.1.2.pred hx :: f.v ∈ marks
              · exact good_H p hL hP f rest marks out x hs hk hg φ ps hp hx hge hz
              · exact good_R p hL hP f rest marks out x hs hk hg φ ps hp hx hge hz
    · exact good_kill p hL hP f rest marks out x hs hk

/-- The ups of the summaries of a good stack are within the cap. -/
theorem projS_ups (p : Params) (marks : Finset (Vertex 3)) :
    ∀ (hd : Bool) (msk : Option (Fin 3)) (l : List Frame), StackOK p marks hd l →
      ∀ s ∈ projS p marks msk l, s.a ≤ p.V
  | _, _, [], _ => by simp [projS]
  | _, msk, [f], h => by
    intro s hs
    simp only [projS, List.mem_singleton] at hs
    subst hs
    exact h.2.2.2.2.2.2.1
  | _, msk, f :: g :: rest, h => by
    intro s hs
    simp only [projS, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact h.2.2.2.2.1.2.1
    · exact projS_ups p marks false _ (g :: rest) h.2.2.2.2.2 s (by simpa [projS] using hs)

/-- With cost `0` the candidates of the outcomes `b ≤ V` sum to `1`. -/
theorem Ucand_sum (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (s : St) (hs : s ∈ Good p) :
    ∑ b ∈ Finset.range (p.V + 1), Ucand p 0 (fun a => if a = b then 1 else 0) s = 1 := by
  obtain ⟨stack, marks, out⟩ := s
  obtain ⟨-, hS, hend⟩ := hs
  cases stack with
  | nil =>
    simp only [Ucand]
    rw [Finset.sum_ite_eq]
    simp [Nat.lt_succ_of_le (hend rfl)]
  | cons f rest =>
    simp only [Ucand]
    rw [← fold_lin p (Finset.range (p.V + 1)) (fun b a => if a = b then (1 : ℝ) else 0)]
    refine fold_one p hL hV _ (fun a ha => ?_) _ (by simp [projS]) (projS_ups p marks true none _ hS) _
    rw [Finset.sum_ite_eq]
    simp [Nat.lt_succ_of_le ha]

/-- **The law of the end of the run from a good state** (`chain_law` with the candidate of cost `0`
as the solution and the candidate of cost `1` as the bound on the reads). -/
theorem law_gen (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (hL : 2 ≤ p.L) (hV : 1 ≤ p.V) (hP : 2 ≤ p.P) (s : St) (hs : s ∈ Good p) (hsE : s.stack ≠ [])
    (b : ℕ) (hb : b ≤ p.V) :
    Engine.iidMeasure (dirLaw.prod coinLaw)
        {w | ∃ t, Engine.traj (updD p) s w t ∈ {z : St | z.stack = []} ∧
          (Engine.traj (updD p) s w t).out.length = b} =
      ENNReal.ofReal (Ucand p 0 (fun a => if a = b then 1 else 0) s) := by
  have hL1 : 1 ≤ p.L := by omega
  refine chain_law (updD p) (dirLaw.prod coinLaw) (fun _ _ => (Set.to_countable _).measurableSet)
    {z : St | z.stack = []} ?_ (fun z => z.out.length) (Finset.range (p.V + 1)) (Good p)
    (fun z hz ξ => good_upd p hL hP z hz _)
    (fun z hz hzE => Finset.mem_range.2 (Nat.lt_succ_of_le (hz.2.2 hzE)))
    (fun b z => ENNReal.ofReal (Ucand p 0 (fun a => if a = b then 1 else 0) z)) ?_ ?_ ?_
    (fun z => ENNReal.ofReal (Ucand p 1 (fun _ => 0) z)) ?_ (fun _ _ => ENNReal.ofReal_ne_top)
    s hs hsE b (Finset.mem_range.2 (Nat.lt_succ_of_le hb))
  · rintro ⟨stack, marks, out⟩ hz ξ
    simp only [Set.mem_ofPred_eq] at hz
    subst hz
    rfl
  · rintro c ⟨stack, marks, out⟩ - hz
    simp only [Set.mem_ofPred_eq] at hz
    subst hz
    simp only [Ucand]
    split_ifs <;> simp
  · intro c z hz hzE
    have := read_le p hkeep0 hL hV 0 le_rfl (fun a => if a = c then 1 else 0)
      (fun a => by split_ifs <;> norm_num) z hz hzE
    simpa using this
  · intro z hz
    rw [← ENNReal.ofReal_sum_of_nonneg fun c _ =>
      Ucand_nonneg p hL1 hV 0 le_rfl _ (fun a => by split_ifs <;> norm_num) z,
      Ucand_sum p hL1 hV z hz, ENNReal.ofReal_one]
  · intro z hz
    by_cases hzE : z ∈ {z : St | z.stack = []}
    · have hfix : ∀ ξ, updD p z ξ = z := by
        obtain ⟨stack, marks, out⟩ := z
        simp only [Set.mem_ofPred_eq] at hzE
        subst hzE
        intro ξ; rfl
      rw [Set.indicator_of_mem hzE, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hzE)]
      simp only [Pi.zero_apply, zero_add, hfix, lintegral_const, measure_univ, mul_one, le_refl]
    · rw [Set.indicator_of_notMem hzE, Set.indicator_of_mem (Set.mem_compl hzE), Pi.one_apply,
        zero_add, ← ENNReal.ofReal_one]
      exact read_le p hkeep0 hL hV 1 zero_le_one (fun _ => 0) (fun _ => le_rfl) z hz hzE

/-- The candidate at the initial state is `GenH` at the height of the top closure. -/
theorem Ucand_init (p : Params) (top : ℕ → ℝ) (k : ℕ) :
    Ucand p 0 top (init k) =
      GenH p p.m true (inp p p.m) (fun _ => 0) (fun _ a => top a) (initK p.m) (k + 1) 0 := by
  have hkid : kidM p ∅ [] none = initK p.m := by
    funext c
    simp [kidM, initK]
  simp only [Ucand, init, projS, List.length_nil, Nat.sub_zero]
  rw [fold, fv_d0 _ _ _ _ _ (by simp [sm, gdepth])]
  simp only [sm, hkid, addC_zero, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]

/-- The count at the end of the run is the number of ups of the top closure. -/
theorem count_end (s : St) (h : s.stack = []) : count s = s.out.length := by
  simp [count, h]

/-- **Lemma 13.2 of the paper, on the frog paths.** With `k` entrants, `k + 1 ≤ P`, the run of
M1_L on the frog paths ends with `b ≤ V` ups with probability the value of `Gen` at the top
closure: an R closure at height `m` with three unmarked children, `k + 1` frogs and no up. -/
theorem top_law_gen (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (hL : 2 ≤ p.L) (hV : 1 ≤ p.V) (hP : 2 ≤ p.P) (k b : ℕ) (hk : k + 1 ≤ p.P) (hb : b ≤ p.V) :
    fpMeasure {ω | ∃ n, (run p k (Pool.poolSeq (sel p k) ω) n).stack = [] ∧
        count (run p k (Pool.poolSeq (sel p k) ω) n) = b} =
      ENNReal.ofReal (GenH p p.m true (inp p p.m) (fun _ => 0)
        (fun _ a => if a = b then 1 else 0) (initK p.m) (k + 1) 0) := by
  set dc : (ℕ → Val) → (ℕ → Fin 4 × ℕ) := fun y t => ((y t).1.2, (y t).2) with hdc
  set T := {w : ℕ → Fin 4 × ℕ | ∃ t, Engine.traj (updD p) (init k) w t ∈ {z : St | z.stack = []} ∧
      (Engine.traj (updD p) (init k) w t).out.length = b} with hT
  have hS : {y : ℕ → Val | ∃ n, (run p k y n).stack = [] ∧ count (run p k y n) = b} =
      dc ⁻¹' T := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hT, hdc]
    refine exists_congr fun n => ?_
    rw [run_traj]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← count_end _ h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [count_end _ h1]; exact h2⟩
  have hTm : MeasurableSet T := by
    have : T = ⋃ t, ⋃ z ∈ {z : St | z.stack = [] ∧ z.out.length = b},
        {w | Engine.traj (updD p) (init k) w t = z} := by
      ext w
      simp only [hT, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨t, h1, h2⟩
        exact ⟨t, _, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨t, z, ⟨h1, h2⟩, hz⟩
        exact ⟨t, hz ▸ h1, hz ▸ h2⟩
    rw [this]
    exact MeasurableSet.iUnion fun t => MeasurableSet.biUnion (Set.to_countable _) fun z _ =>
      measurableSet_traj_eq _ (fun _ _ => (Set.to_countable _).measurableSet) _ t z
  have hdm : Measurable dc :=
    measurable_pi_iff.2 fun t => (measurable_of_countable (fun x : Val => (x.1.2, x.2))).comp
      (measurable_pi_apply t)
  have hpm := (Pool.measurable_poolSeq (sel p k) (measurableSet_sel p k)).1
  have hev : {ω | ∃ n, (run p k (Pool.poolSeq (sel p k) ω) n).stack = [] ∧
      count (run p k (Pool.poolSeq (sel p k) ω) n) = b} =
      Pool.poolSeq (sel p k) ⁻¹' (dc ⁻¹' T) := by
    rw [← hS]
    rfl
  rw [hev, ← Measure.map_apply hpm (hdm hTm), map_fp_read, ← Measure.map_apply hdm hTm, hdc,
    map_dc_iid, hT, law_gen p hkeep0 hL hV hP _ (good_init p k hk) (by simp [init]) b hb,
    Ucand_init]

end FrogModel.D3
