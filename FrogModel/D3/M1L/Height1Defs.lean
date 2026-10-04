module

public import FrogModel.D3.M1L.Height0Defs

@[expose] public section

/-!
# M1_L at height 1: the top recursion with the loop solved out

The R recursion of Section 13 of the paper at height 1, for the law of the run at `m = 1`
(Lemma 13.2), here with keeps at height 0 that may read `f0`, so that the marked children of height
0 are not lumped into one type. The top closure is an R closure at the root; each child is unmarked
(`0`), marked with its children unmarked (`1`), or marked with its children marked after a kill
(`2`). A round sends the frog up (probability 1/4) or into a child: into an unmarked child, an R
closure at height 0 with two frogs, whose ups have law `ρR` and are kept with probability
`κ true 3`; into a marked child, an H closure at height 0 with one frog, law `ρH`, kept with
probability `κ false f0`. The H entry that returns its frog and keeps it leaves the state
unchanged (the loop); `W1top` solves it out. Well founded on the rank of the child states, then the
pool size.
-/

namespace FrogModel.D3

/-- The rank of the child states at height 1: `0` unmarked, `1` marked with its children
unmarked, `2` marked with its children marked (after a kill). -/
def rank1 (σ : Fin 3 → Fin 3) : ℕ := ∑ c, (2 - (σ c).val)

theorem rank1_update_lt (σ : Fin 3 → Fin 3) (c : Fin 3) (t : Fin 3) (h : (σ c).val < t.val) :
    rank1 (Function.update σ c t) < rank1 σ := by
  unfold rank1
  have ht := t.isLt
  fin_cases c <;> simp [Fin.sum_univ_three, Function.update_apply] at h ⊢ <;> omega

/-- The child states after a kill in an H closure at child `c`. -/
def σkill (σ : Fin 3 → Fin 3) (c : Fin 3) : Fin 3 → Fin 3 :=
  if (σ c).val = 1 then Function.update σ c 2 else σ

/-- The probability that the top closure at height 1, at pool size `n` with `a` ups and child
states `σ`, ends with `b` ups (the R recursion of Section 13 of the paper at height 1, the marked
children not lumped, the loop solved out). -/
noncomputable def W1top (V P b : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ) :
    (Fin 3 → Fin 3) → ℕ → ℕ → ℝ
  | σ, n, a =>
    if hn : n = 0 then (if a = b then 1 else 0) else
    let up := W1top V P b ρR ρH κ σ (n - 1) (if a < V then a + 1 else a)
    let rest : Fin 3 → ℝ := fun c =>
      if h0 : (σ c).val = 0 then
        ∑ b' ∈ Finset.range 3, ρR b' *
          (κ true 3 b' * W1top V P b ρR ρH κ (Function.update σ c 1) (min (n - 1 + b') P) a +
            (1 - κ true 3 b') * W1top V P b ρR ρH κ (Function.update σ c 2) (n - 1) a)
      else if h1 : (σ c).val = 1 then
        ρH 0 * (κ false 3 0 * W1top V P b ρR ρH κ σ (n - 1) a +
            (1 - κ false 3 0) * W1top V P b ρR ρH κ (Function.update σ c 2) (n - 1) a) +
          ρH 1 * (1 - κ false 3 1) * W1top V P b ρR ρH κ (Function.update σ c 2) (n - 1) a
      else
        ρH 0 * W1top V P b ρR ρH κ σ (n - 1) a +
          ρH 1 * (1 - κ false 0 1) * W1top V P b ρR ρH κ σ (n - 1) a
    let loop : ℝ := ∑ c, if (σ c).val = 0 then 0 else
      1 / 4 * ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1
    (1 / 4 * up + ∑ c, 1 / 4 * rest c) / (1 - loop)
termination_by σ n => (rank1 σ, n)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by omega)
    | exact Prod.Lex.left _ _ (rank1_update_lt σ _ _ (by simp_all))

/-- The round of the top at height 1 into child `c`, outside the loop, for a value function `W`. -/
noncomputable def rest1 (P : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ)
    (W : (Fin 3 → Fin 3) → ℕ → ℕ → ℝ) (σ : Fin 3 → Fin 3) (n a : ℕ) (c : Fin 3) : ℝ :=
  if (σ c).val = 0 then
    ∑ b' ∈ Finset.range 3, ρR b' *
      (κ true 3 b' * W (Function.update σ c 1) (min (n - 1 + b') P) a +
        (1 - κ true 3 b') * W (Function.update σ c 2) (n - 1) a)
  else if (σ c).val = 1 then
    ρH 0 * (κ false 3 0 * W σ (n - 1) a + (1 - κ false 3 0) * W (Function.update σ c 2) (n - 1) a) +
      ρH 1 * (1 - κ false 3 1) * W (Function.update σ c 2) (n - 1) a
  else
    ρH 0 * W σ (n - 1) a + ρH 1 * (1 - κ false 0 1) * W σ (n - 1) a

/-- The probability of the loop at height 1: an H entry whose frog comes back up and is kept. -/
noncomputable def loop1 (ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ) (σ : Fin 3 → Fin 3) : ℝ :=
  ∑ c, if (σ c).val = 0 then 0 else 1 / 4 * ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1

/-- An inner closure at height 0: R or H, the child, its chain state, waiting for the kill coin. -/
abbrev In1 := Bool × Fin 3 × (ℕ × ℕ × ℕ) × Bool

/-- The state of the run at height 1: top pool size, top ups, child states, inner closure. -/
abbrev S1 := ℕ × ℕ × (Fin 3 → Fin 3) × Option In1

/-- The value of `f0` and of the unmarked count for a closure at a marked child. -/
def f0of (σ : Fin 3 → Fin 3) (c : Fin 3) : ℕ := if (σ c).val = 1 then 3 else 0

/-- The run of M1_L at `p.m = 1` on the directions and coins read. -/
def h1step (p : Params) : S1 → Fin 4 × ℕ → S1
  | (n, a, σ, none), x =>
    if n = 0 then (n, a, σ, none)
    else if h : x.1 = 0 then (n - 1, if a < p.V then a + 1 else a, σ, none)
    else if (σ (x.1.pred h)).val = 0 then
      (n - 1, a, Function.update σ (x.1.pred h) 1, some (true, x.1.pred h, (2, 0, 0), false))
    else (n - 1, a, σ, some (false, x.1.pred h, (1, 0, 0), false))
  | (n, a, σ, some (r, c, y, false)), x =>
    (n, a, σ, some (r, c, hstep p.V p.L y x.1,
      decide ((hstep p.V p.L y x.1).1 = 0 ∧ (hstep p.V p.L y x.1).2.2 = 0)))
  | (n, a, σ, some (r, c, y, true)), x =>
    if p.keep r 0 (f0of σ c) y.2.1 (f0of σ c) x.2 then (min (n + y.2.1) p.P, a, σ, none)
    else (n, a, Function.update σ c 2, none)

/-- The keep probability of a kill at height 0, from the coin. -/
noncomputable def κ1 (p : Params) (r : Bool) (f b' : ℕ) : ℝ :=
  (coinLaw {j | p.keep r 0 f b' f j = true}).toReal

noncomputable def ρR1 (p : Params) (b' : ℕ) : ℝ := U0 p.V p.L b' (2, 0, 0)
noncomputable def ρH1 (p : Params) (b' : ℕ) : ℝ := U0 p.V p.L b' (1, 0, 0)

noncomputable def Wt (p : Params) (b : ℕ) : (Fin 3 → Fin 3) → ℕ → ℕ → ℝ :=
  W1top p.V p.P b (ρR1 p) (ρH1 p) (κ1 p)

/-- The value after the kill of a closure at child `c` with `b'` ups. -/
noncomputable def K1 (p : Params) (b : ℕ) (r : Bool) (c : Fin 3) (b' n a : ℕ)
    (σ : Fin 3 → Fin 3) : ℝ :=
  κ1 p r (f0of σ c) b' * Wt p b σ (min (n + b') p.P) a +
    (1 - κ1 p r (f0of σ c) b') * Wt p b (Function.update σ c 2) n a

/-- The candidate law at height 1 on every state. -/
noncomputable def W1 (p : Params) (b : ℕ) : S1 → ℝ
  | (n, a, σ, none) => Wt p b σ n a
  | (n, a, σ, some (r, c, y, false)) =>
    ∑ b' ∈ Finset.range (p.V + 1), U0 p.V p.L b' y * K1 p b r c b' n a σ
  | (n, a, σ, some (r, c, y, true)) => K1 p b r c y.2.1 n a σ

/-- The potential of the top at height 1: `(4L + 3) n + (8L + 6) rank`. -/
noncomputable def Φ1 (p : Params) (σ : Fin 3 → Fin 3) (n : ℕ) : ℝ :=
  (4 * p.L + 3) * n + (8 * p.L + 6) * rank1 σ

/-- The potential after the kill of a closure at child `c` with `b'` ups, averaged on the coin. -/
noncomputable def KT1 (p : Params) (r : Bool) (c : Fin 3) (b' n : ℕ) (σ : Fin 3 → Fin 3) : ℝ :=
  κ1 p r (f0of σ c) b' * Φ1 p σ (min (n + b') p.P) +
    (1 - κ1 p r (f0of σ c) b') * Φ1 p (Function.update σ c 2) n

/-- A bound on the expected number of reads before the end at height 1. -/
noncomputable def T1 (p : Params) : S1 → ℝ
  | (n, _, σ, none) => Φ1 p σ n
  | (n, _, σ, some (r, c, y, false)) =>
    T0 p.L y + 1 + ∑ b' ∈ Finset.range (p.V + 1), U0 p.V p.L b' y * KT1 p r c b' n σ
  | (n, _, σ, some (r, c, y, true)) => 1 + KT1 p r c y.2.1 n σ

/-- The states kept by the run at height 1: ups and pool within their caps, a running closure at
depth below `L` with its ups within the cap, flagged exactly when it has ended. -/
def G1 (p : Params) : Set S1 :=
  {x | x.2.1 ≤ p.V ∧ x.1 ≤ p.P ∧ ∀ r c y fl, x.2.2.2 = some (r, c, y, fl) →
    y.2.2 < p.L ∧ y.2.1 ≤ p.V ∧ (fl = true ↔ (y.1 = 0 ∧ y.2.2 = 0))}

/-- The ends at height 1: the top pool is empty and no closure runs. -/
def E1 : Set S1 := {x | x.1 = 0 ∧ x.2.2.2 = none}

/-! ### The machine at `p.m = 1` projected onto the chain -/

/-- The state of child `c` read off the marks: unmarked (`0`), marked with its children unmarked
(`1`), marked with its children marked (`2`). -/
def σof (marks : Finset (Vertex 3)) (c : Fin 3) : Fin 3 :=
  if [c] ∉ marks then 0 else if [0, c] ∈ marks then 2 else 1

/-- The depth of the ghost of a closure at a child, below that child. -/
def gdepth1 (f : Frame) : ℕ :=
  match f.ghost with
  | none => 0
  | some (_, u) => u.length - 1

/-- The machine state at `p.m = 1` projected: the top's pool and ups, the child states, and the
running child closure with its pool, ups, ghost depth and kill flag. -/
def proj1 (s : St) : S1 :=
  match s.stack with
  | [] => (0, s.out.length, σof s.marks, none)
  | [g] => (g.pool.length, g.ups.length, σof s.marks, none)
  | f :: g :: _ => (g.pool.length, g.ups.length, σof s.marks,
      some (f.isR, f.v.headD 0, (f.pool.length, f.ups.length, gdepth1 f), f.killing))

/-- The marks at height 1: children, and grandchildren only as all three children of a marked
child. -/
def MarksOK (marks : Finset (Vertex 3)) : Prop :=
  ∀ v ∈ marks, ∃ c : Fin 3, v = [c] ∨
    ∃ c' : Fin 3, v = [c', c] ∧ [c] ∈ marks ∧ ∀ c'' : Fin 3, [c'', c] ∈ marks

/-- The top closure: at the root, an `R` closure, no ghost, not waiting for a kill, within the
caps. -/
def TopOK (p : Params) (g : Frame) : Prop :=
  g.v = [] ∧ g.isR = true ∧ g.ghost = none ∧ g.killing = false ∧ g.pool.length ≤ p.P ∧
    g.ups.length ≤ p.V

/-- A closure at a marked child `c`: its `f0` is read off the marks, its ups within the cap, its
ghost below `c` at depth below `L`, and it waits for its kill exactly when it has ended. -/
def ChildOK (p : Params) (marks : Finset (Vertex 3)) (f : Frame) : Prop :=
  ∃ c : Fin 3, f.v = [c] ∧ f.f0 = f0of (σof marks) c ∧ (σof marks c).val ≠ 0 ∧
    f.ups.length ≤ p.V ∧
    (∀ φ u, f.ghost = some (φ, u) → u.getLast? = some c ∧ 2 ≤ u.length ∧ u.length - 1 < p.L) ∧
    (f.killing = true ↔ (f.pool = [] ∧ f.ghost = none))

/-- The states of the run at `p.m = 1`: ended, the top alone with frogs in its pool, or the top
with one closure at a child. -/
def Shape1 (p : Params) (s : St) : Prop :=
  MarksOK s.marks ∧
    match s.stack with
    | [] => s.out.length ≤ p.V
    | [g] => TopOK p g ∧ g.pool ≠ []
    | [f, g] => TopOK p g ∧ ChildOK p s.marks f
    | _ => False

end FrogModel.D3
