module

public import FrogModel.D3.M1L.Height0Defs

@[expose] public section

/-!
# M1_L at every height: the recursions of Section 13 of the paper on unlumped child types

A closure at height `h` sees each of its three children as unmarked (`none`, the type N of Section 13)
or marked with `t` unmarked children of its own (`some t`, the type U_t). `Gen` is the law (or,
with an additive term, the expected cost) of a closure from its state `(kid, n, a)`: child types,
pool size, ups. A round reads a direction: up (an up, capped at `V`), or into the child `c`:

* `none`: an R entry, the child returns `(b, f)` with probability `ρ b f`; the pool becomes
  `min (n - 1 + b) P` and the child type `some f`;
* `some t` in an R closure (`isR`): an H entry, outcome `(a', f)` with probability `K t a' f`; the
  outcome `(1, t)` is the loop, `(0, t)` loses the frog, `f < t` lowers the type;
* `some t` in an H closure: a ghost walk, back with probability `pL` (the loop), lost otherwise.

The loop is solved out (division by `1 - loopK`), and every other outcome lowers
`(rankK kid, n)` lexicographically, so `Gen` is a well-founded definition. The outcomes `(a', t)`
of an H entry with `a' ≥ 2` are left out: they have probability `0` for the laws of the run.
At height `0` every entry is a ghost entry: the closure is the H recursion with every child
marked (`some 0`), so that the count of unmarked children is `0` there, as in the rule of Section 13.
-/

namespace FrogModel.D3

/-- The child types of a closure: `none` unmarked, `some t` marked with `t` unmarked children. -/
abbrev Kid := Fin 3 → Option (Fin 4)

/-- The weight of a child type: `4` for an unmarked child, `t` for `U_t`. -/
def krank : Option (Fin 4) → ℕ
  | none => 4
  | some t => t.val

/-- The total type of the children (Section 13 of the paper: N counted as 4, U_t as t). -/
def rankK (k : Kid) : ℕ := ∑ c, krank (k c)

/-- The number of unmarked children. -/
def nN (k : Kid) : ℕ := (Finset.univ.filter fun c => k c = none).card

/-- The ups after an up: one more, capped at `V`. -/
def upA (V a : ℕ) : ℕ := if a < V then a + 1 else a

theorem rankK_update_lt (k : Kid) (c : Fin 3) (x : Option (Fin 4)) (h : krank x < krank (k c)) :
    rankK (Function.update k c x) < rankK k := by
  unfold rankK
  fin_cases c <;> simp [Fin.sum_univ_three, Function.update_apply] at h ⊢ <;> omega

/-- The probability of the loop of a round: an H entry with outcome `(1, t)` (R closure) or a
ghost walk that comes back (H closure), summed over the marked children, each with weight 1/4. -/
noncomputable def loopK (isR : Bool) (pL : ℝ) (K : ℕ → ℕ → ℕ → ℝ) (k : Kid) : ℝ :=
  ∑ c, match k c with
    | none => 0
    | some t => 1 / 4 * (if isR then K t 1 t else pL)

/-- The law (`add = 0`) or the cost of a closure from `(kid, n, a)`, ending at `term kid a`. -/
noncomputable def Gen (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add : Kid → ℝ) (term : Kid → ℕ → ℝ) : Kid → ℕ → ℕ → ℝ
  | k, n, a =>
    if hn : n = 0 then term k a else
    (add k + 1 / 4 * Gen V P isR pL ρ K add term k (n - 1) (upA V a) +
      ∑ c, 1 / 4 * (match hk : k c with
        | none => ∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1),
            ρ b f * Gen V P isR pL ρ K add term (Function.update k c (some f)) (min (n - 1 + b) P) a
        | some t => if isR then
            K t 0 t * Gen V P isR pL ρ K add term k (n - 1) a +
              ∑ f : Fin 4, if _hf : f < t then ∑ a' ∈ Finset.range (V + 1),
                K t a' f * Gen V P isR pL ρ K add term (Function.update k c (some f))
                  (min (n - 1 + a') P) a
              else 0
          else (1 - pL) * Gen V P isR pL ρ K add term k (n - 1) a)) /
      (1 - loopK isR pL K k)
termination_by k n => (rankK k, n)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by omega)
    | exact Prod.Lex.left _ _ (rankK_update_lt _ _ _ (by rw [hk]; simp only [krank]; first | exact _hf | exact f.isLt))

/-- The round of a closure into child `c`, outside the loop, for a value function `X`. -/
noncomputable def bodyG (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (X : Kid → ℕ → ℕ → ℝ) (k : Kid) (n a : ℕ) (c : Fin 3) : ℝ :=
  match k c with
  | none => ∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1),
      ρ b f * X (Function.update k c (some f)) (min (n - 1 + b) P) a
  | some t => if isR then
      K t 0 t * X k (n - 1) a +
        ∑ f : Fin 4, (if f < t then ∑ a' ∈ Finset.range (V + 1),
          K t a' f * X (Function.update k c (some f)) (min (n - 1 + a') P) a else 0)
    else (1 - pL) * X k (n - 1) a

end FrogModel.D3
