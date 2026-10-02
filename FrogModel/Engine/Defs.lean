module

public import Mathlib
public import FrogModel.LinSys.Defs

@[expose] public section

/-!
# The root engine: definitions

The root chain (Section 6.3 of the paper) and max chains (Lemma 6.4 of the paper). One engine
serves the exactness of the root chain (Lemma 6.2) and the domination of the redirected chain
(Lemma 6.4).

**Driven systems.** A state `x : X` moves by `f x ξ` for an input `ξ : Ξ`; `traj f x w` is the
trajectory under the inputs `w 0, w 1, ...`. Under i.i.d. inputs of law `ν`, the expected
Feynman-Kac sum `fk f m a n x` (rewards `a`, multiplicative weights `m`, `n` steps) is the `n`-th
iterate of the linear system with kernel `fkKernel f m ν` and right side `fkRhs a ν`, and its
supremum over `n` is the least solution (`LinSys.least`): this is how the law of the output of
the root chain, and the weights of its stopped parts, become least solutions.

**The root chain.** The state at the root `r` (`RState`) is: `i` frogs of `r` finished, `e` exits
so far, `p` pending frogs, the child states `σ`, and the outputs `out` (`out k` is the exits when
frog `k` finished, `⊤` before). An input is a direction `a : Fin (d + 1)` (`0`: exit, `c.succ`:
entry into child `c`) and a uniform `u : U`; an entry moves the child by `cstep (σ c) u`
(delivered returns, next child state). When `p` reaches `0` the frog is finished, its output is
recorded and the next frog starts (`p = 1`); after frog `J - 1` the state is absorbing.

**The output, two ways.** `recOut` reads the outputs recorded along a trajectory (`⊤` for a
frog never finished). `outPsi` is the same output as a closed formula from the present state,
the form of `Psi` (Lemma 4.2 of the paper): frog `k ≥ i` is finished after the first `n` steps
with `need n ≤ n`, `need n = p + (k - i) + (returns delivered in the first n steps)`, with
`e + (exits among them)` as output. The children evolve on their own (`childAt`), so the
returns are a function of the child states and the inputs alone. The formula is monotone in the
child states under a simulation (`IsSim`), which is the monotonicity of the output in the future
deliveries of the children (proof of Lemma 6.4 of the paper), pathwise with shared directions and
shared uniforms of each step.

The subtractions `x.p - 1` (a step with `p ≥ 1`) and `k - x.i` (taken when `x.i ≤ k`) are exact
where they are read: `Valid` gives `p ≥ 1` in a live state, and `outPsi` reads `k - x.i` only
when `¬ k < x.i`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine

section Driven

variable {X Ξ : Type*}

/-- The trajectory of a driven system: `x₀ = x`, `x_{n+1} = f x_n (w n)`. -/
def traj (f : X → Ξ → X) (x : X) (w : ℕ → Ξ) : ℕ → X
  | 0 => x
  | n + 1 => f (traj f x w n) (w n)

/-- The Feynman-Kac sum over the first `n` steps, `∑_{k < n} (∏_{j < k} m x_j w_j) a x_k w_k`,
written by the first step. -/
noncomputable def fk (f : X → Ξ → X) (m a : X → Ξ → ℝ≥0∞) : ℕ → X → (ℕ → Ξ) → ℝ≥0∞
  | 0, _, _ => 0
  | n + 1, x, w => a x (w 0) + m x (w 0) * fk f m a n (f x (w 0)) (fun k => w (k + 1))

/-- The input sequence `ξ, w 0, w 1, ...`. -/
def consSeq (ξ : Ξ) (w : ℕ → Ξ) : ℕ → Ξ
  | 0 => ξ
  | k + 1 => w k

variable [MeasurableSpace Ξ]

/-- The kernel of the system: `K x y = ∫_{f x ξ = y} m x ξ dν(ξ)`. -/
noncomputable def fkKernel (f : X → Ξ → X) (m : X → Ξ → ℝ≥0∞) (ν : Measure Ξ) (x y : X) :
    ℝ≥0∞ :=
  ∫⁻ ξ in {ξ | f x ξ = y}, m x ξ ∂ν

/-- The right side of the system: `b x = ∫ a x ξ dν(ξ)`. -/
noncomputable def fkRhs (a : X → Ξ → ℝ≥0∞) (ν : Measure Ξ) (x : X) : ℝ≥0∞ :=
  ∫⁻ ξ, a x ξ ∂ν

/-- I.i.d. inputs of law `ν`. -/
noncomputable def iidMeasure (ν : Measure Ξ) : Measure (ℕ → Ξ) :=
  Measure.infinitePi fun _ : ℕ => ν

end Driven

section Root

variable {S U : Type*} {d J : ℕ}

/-- The state of the root chain: `i` frogs of `r` finished, `e` exits, `p` pending frogs, the
child states `σ`, the outputs recorded `out` (`⊤` for a frog not finished). -/
structure RState (S : Type*) (d J : ℕ) where
  i : ℕ
  e : ℕ
  p : ℕ
  σ : Fin d → S
  out : Fin J → ℕ∞

theorem RState.injective_tuple :
    Function.Injective fun x : RState S d J => (x.i, x.e, x.p, x.σ, x.out) := by
  rintro ⟨i, e, p, σ, out⟩ ⟨i', e', p', σ', out'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

instance [Countable S] : Countable (RState S d J) := RState.injective_tuple.countable

/-- A state the chain can be in: a live state has a pending frog, and no frog from `i` on has
an output. -/
def Valid (x : RState S d J) : Prop :=
  (x.i < J → 1 ≤ x.p) ∧ ∀ k : Fin J, x.i ≤ k → x.out k = ⊤

/-- One move of a pending frog: the exits, the pending frogs and the child states after it. -/
def move (cstep : S → U → ℕ × S) (x : RState S d J) (a : Fin (d + 1)) (u : U) :
    ℕ × ℕ × (Fin d → S) :=
  if h : a = 0 then (x.e + 1, x.p - 1, x.σ)
  else (x.e, x.p - 1 + (cstep (x.σ (a.pred h)) u).1,
    Function.update x.σ (a.pred h) (cstep (x.σ (a.pred h)) u).2)

/-- One step of the root chain (Section 6.3 of the paper); absorbing once `J` frogs are finished. -/
def rstep (cstep : S → U → ℕ × S) (x : RState S d J) (ξ : Fin (d + 1) × U) : RState S d J :=
  if h : x.i < J then
    if (move cstep x ξ.1 ξ.2).2.1 = 0 then
      ⟨x.i + 1, (move cstep x ξ.1 ξ.2).1, 1, (move cstep x ξ.1 ξ.2).2.2,
        Function.update x.out ⟨x.i, h⟩ (move cstep x ξ.1 ξ.2).1⟩
    else ⟨x.i, (move cstep x ξ.1 ξ.2).1, (move cstep x ξ.1 ξ.2).2.1, (move cstep x ξ.1 ξ.2).2.2,
      x.out⟩
  else x

/-- The outputs recorded along a trajectory: `⊤` for a frog never finished. -/
noncomputable def recOut (t : ℕ → RState S d J) (k : Fin J) : ℕ∞ :=
  ⨅ n, (t n).out k

/-- The child states before step `n` when the children evolve alone under the inputs `w`. -/
def childAt (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U) :
    ℕ → Fin d → S
  | 0 => σ
  | n + 1 =>
    if h : (w n).1 = 0 then childAt cstep σ w n
    else Function.update (childAt cstep σ w n) ((w n).1.pred h)
      (cstep (childAt cstep σ w n ((w n).1.pred h)) (w n).2).2

/-- The returns delivered at step `n`: `0` at an exit. -/
def delivAt (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U) (n : ℕ) : ℕ :=
  if h : (w n).1 = 0 then 0 else (cstep (childAt cstep σ w n ((w n).1.pred h)) (w n).2).1

/-- The returns delivered in the first `n` steps. -/
def cumDeliv (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U) (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, delivAt cstep σ w t

/-- The exits among the first `n` steps. -/
def exitCount (w : ℕ → Fin (d + 1) × U) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun t => (w t).1 = 0).card

/-- The frogs needed for the first `n` steps until frog `k` is finished, against `n`:
`p + (k - i)` frogs at hand and the returns of the first `n` steps. -/
def need (cstep : S → U → ℕ × S) (x : RState S d J) (w : ℕ → Fin (d + 1) × U) (k n : ℕ) : ℕ :=
  x.p + (k - x.i) + cumDeliv cstep x.σ w n

open Classical in
/-- The output as a formula from the present state: a frog `k < i` has its recorded output; frog
`k ≥ i` is finished after the least `n` with `need n ≤ n` steps, with `e` plus the exits among
them as output, and `⊤` if there is no such `n`. -/
noncomputable def outPsi (cstep : S → U → ℕ × S) (x : RState S d J) (w : ℕ → Fin (d + 1) × U)
    (k : Fin J) : ℕ∞ :=
  if (k : ℕ) < x.i then x.out k
  else if h : ∃ n, need cstep x w k n ≤ n then ((x.e + exitCount w (Nat.find h) : ℕ) : ℕ∞)
  else ⊤

/-- A simulation of the child chain: related states deliver ordered returns at every uniform
and move to related states (Lemma 6.4 of the paper: a label below its max label). -/
def IsSim (cstep : S → U → ℕ × S) (R : S → S → Prop) : Prop :=
  ∀ s s', R s s' → ∀ u, (cstep s u).1 ≤ (cstep s' u).1 ∧ R (cstep s u).2 (cstep s' u).2

/-- `y` dominates `x`: the same counts and outputs, the children related by `R`. -/
def Dom (R : S → S → Prop) (x y : RState S d J) : Prop :=
  x.i = y.i ∧ x.e = y.e ∧ x.p = y.p ∧ x.out = y.out ∧ ∀ c, R (x.σ c) (y.σ c)

open Classical in
/-- The reward of the absorption of the chain with outputs `o` at a step: `1` on a live state
whose step finishes the last frog with the outputs `o`. -/
noncomputable def absorbAt (cstep : S → U → ℕ × S) (o : Fin J → ℕ) (x : RState S d J)
    (ξ : Fin (d + 1) × U) : ℝ≥0∞ :=
  if x.i < J ∧ J ≤ (rstep cstep x ξ).i ∧ (rstep cstep x ξ).out = fun k => (o k : ℕ∞) then 1
  else 0

/-- The start: no frog finished, one pending, every child in state `F`. -/
def start (F : S) : RState S d J :=
  ⟨0, 0, 1, fun _ => F, fun _ => ⊤⟩


/-! ### The inputs read from pools, and the child chain alone -/

/-- The steps before `t` with direction `a`. -/
def dirCountN (D : ℕ → Fin (d + 1)) (a : Fin (d + 1)) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun s => D s = a).card

/-- The inputs read from pools: step `t` takes the direction `D t` and the next unused uniform of
pool `D t`; pool `0` is read at the exits, where the uniform is not used. -/
def poolDrive (D : ℕ → Fin (d + 1)) (V : Fin (d + 1) → ℕ → U) (t : ℕ) : Fin (d + 1) × U :=
  (D t, V (D t) (dirCountN D (D t) t))

/-- The child chain alone, from `s`, after `m` entries driven by `v`. -/
def chainState (cstep : S → U → ℕ × S) (s : S) (v : ℕ → U) : ℕ → S
  | 0 => s
  | m + 1 => (cstep (chainState cstep s v m) (v m)).2

/-- The returns delivered by the child chain in its first `m` entries. -/
def chainDeliv (cstep : S → U → ℕ × S) (s : S) (v : ℕ → U) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, (cstep (chainState cstep s v j) (v j)).1

/-- The child chain as a curve of `Psi` (`psiG` reads `G (m + 1)` after `m ≥ 1` entries):
`G i` is the returns of the first `i - 1` entries. -/
def chainCurve (cstep : S → U → ℕ × S) (s : S) (v : ℕ → U) (i : ℕ) : ℕ∞ :=
  chainDeliv cstep s v (i - 1)

/-! ### The root inputs read from pools of pieces (the pools of `FrogModel.Pool`)

A piece is an input `Fin (d + 1) × U`. Piece `2 t` is read from pool `none` and gives the
direction of step `t`; piece `2 t + 1` is read from pool `some a`, `a` the direction just read,
and gives the uniform of step `t`. On the pool space `Option (Fin (d + 1)) × ℕ → Fin (d + 1) × U`
the directions are then `poolDir ω` and the uniforms of pool `a` are `poolUnif ω a`. -/

/-- The pool of piece `k`: `none` for `k` even, `some a` for `k` odd, `a` the direction of
piece `k - 1`. -/
def driveSel (k : ℕ) (y : Fin k → Fin (d + 1) × U) : Option (Fin (d + 1)) :=
  if h : k % 2 = 1 then some (y ⟨k - 1, by omega⟩).1 else none

/-- The directions on the pool space: the first components of pool `none`. -/
def poolDir (ω : Option (Fin (d + 1)) × ℕ → Fin (d + 1) × U) (t : ℕ) : Fin (d + 1) :=
  (ω (none, t)).1

/-- The uniforms on the pool space: the second components of pool `some a`. -/
def poolUnif (ω : Option (Fin (d + 1)) × ℕ → Fin (d + 1) × U) (a : Fin (d + 1)) (m : ℕ) : U :=
  (ω (some a, m)).2

/-- An input from two pieces: the direction of the first and the uniform of the second. -/
def pairInput (e e' : Fin (d + 1) × U) : Fin (d + 1) × U := (e.1, e'.2)

/-! ### Permuting the children (for lumping the ordered children into multisets) -/

/-- The children permuted by `π`: child `π c` of the new state is child `c` of the old one. -/
def permState (π : Equiv.Perm (Fin d)) (x : RState S d J) : RState S d J :=
  ⟨x.i, x.e, x.p, x.σ ∘ π.symm, x.out⟩

/-- The directions permuted by `π`: the exit stays, the entry into `c` becomes the entry into
`π c`. -/
def permDir (π : Equiv.Perm (Fin d)) (a : Fin (d + 1)) : Fin (d + 1) :=
  Fin.cases 0 (fun c => (π c).succ) a

/-- The uniform law of a direction. -/
noncomputable abbrev unifDir (d : ℕ) : Measure (Fin (d + 1)) :=
  (ProbabilityTheory.uniformOn Set.univ : Measure (Fin (d + 1)))

end Root

end FrogModel.Engine
