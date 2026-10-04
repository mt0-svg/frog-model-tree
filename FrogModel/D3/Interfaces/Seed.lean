module

public import FrogModel.D3.Interfaces.Step

@[expose] public section

/-!
# The interface of Section 13: Proposition 13.3 and the seed at 100 (d = 3)

Section 13 of the paper: the recursion, Proposition 13.3 and Lemma 13.4.

FrogModel/D3/M1L/ (the lower model `M1_L`) proves `f3L`: Proposition 13.3 at a general height
`m ≥ 1`. Its hypotheses are the recursions of Section 13 on stored laws, stated here as real
functions: `Rhat0`, `Khat0` (height 0), `KhatH` (the H recursion `Y_f(s)`), `Wrec` (the R recursion
`W_sigma(p)` with the loop solved out), `Rhat` and `Wtop`. FrogModel/D3/M1K (the check of the stored
run) proves these hypotheses for the stored run; FrogModel/D3/LaneC/Seed.lean proves `seed_valid`
(Lemma 13.4).

Laws on `{0..V} × {0..3}` are functions `ℕ → ℕ → ℝ` (answers, unmarked children); a kernel
`K t a f'` is the law `K(t -> (a, f'))` on `{0..V} × {0..t}`. The bottom outcome is `(0, 0)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## The recursions of Section 13 -/

/-- The return probability of a ghost walk (Section 13): `p_L = (3^(L-1) - 1)/(3^L - 1)`. -/
noncomputable def pL (L : ℕ) : ℝ := ((3 : ℝ) ^ (L - 1) - 1) / ((3 : ℝ) ^ L - 1)

/-- `q_L = 1/(4 - 3 p_L)`: a frog at height `0` goes up before it is lost. -/
noncomputable def qL (L : ℕ) : ℝ := 1 / (4 - 3 * pL L)

/-- `up(L)`: the law shifted by one in its first coordinate, the value `V` absorbing. -/
noncomputable def upV (V : ℕ) (W : ℕ → ℕ → ℝ) (a f : ℕ) : ℝ :=
  if a = 0 then 0 else if a < V then W (a - 1) f else if a = V then W (V - 1) f + W V f else 0

/-- `Rhat_0`: the law of `min(Bin(2, q_L), V)` in the first coordinate, with `f = 0`. -/
noncomputable def Rhat0 (V L : ℕ) (b f : ℕ) : ℝ :=
  if f = 0 then
    ∑ i ∈ Finset.range 3,
      if min i V = b then ((Nat.choose 2 i : ℕ) : ℝ) * qL L ^ i * (1 - qL L) ^ (2 - i) else 0
  else 0

/-- `Khat_0(f -> .)`: mass `q_L` at `(1, f)` and `1 - q_L` at `(0, f)`. -/
noncomputable def Khat0 (L : ℕ) (f a f' : ℕ) : ℝ :=
  if f' = f then (if a = 1 then qL L else if a = 0 then 1 - qL L else 0) else 0

/-- The H recursion at a height `h ≥ 1` (Section 13), `rhobar` the first marginal of the input law:
`Y_f(0)` is the point mass at `(0, f)` and
`Y_f(s) = [(1/4) up(Y_f(s-1)) + ((3-f)/4)(1-p_L) Y_f(s-1)
  + (f/4) sum_b rhobar(b) Y_(f-1)(min(s-1+b, P))] / (1 - (3-f) p_L/4)`. -/
noncomputable def Yrec (V P L : ℕ) (rhobar : ℕ → ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | f, 0, a, f' => if a = 0 ∧ f' = f then 1 else 0
  | f, s + 1, a, f' =>
    (1 / 4 * upV V (fun a' f'' => Yrec V P L rhobar f s a' f'') a f' +
        (3 - (f : ℝ)) / 4 * (1 - pL L) * Yrec V P L rhobar f s a f' +
        (if hf : f = 0 then 0 else
          (f : ℝ) / 4 * ∑ b ∈ Finset.range (V + 1),
            rhobar b * Yrec V P L rhobar (f - 1) (min (s + b) P) a f')) /
      (1 - (3 - (f : ℝ)) * pL L / 4)
termination_by f s => (f, s)
decreasing_by
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · exact Prod.Lex.left _ _ (by omega)

/-- `Khat_h[rho](f -> .) = Y_f(1)`, the H kernel at a height `h ≥ 1`. -/
noncomputable def KhatH (V P L : ℕ) (rho : ℕ → ℕ → ℝ) (f a f' : ℕ) : ℝ :=
  Yrec V P L (fun b => ∑ f'' ∈ Finset.range 4, rho b f'') f 1 a f'

/-- A child type of the R recursion: `none` unmarked (`N`), `some t` marked with `t` unmarked
children (`U_t`). -/
abbrev CType := Option (Fin 4)

/-- The type weight: `N` counts `4`, `U_t` counts `t`. -/
def tval : CType → ℕ
  | none => 4
  | some t => t.val

/-- The total type of the three children. -/
def rankS (σ : Fin 3 → CType) : ℕ := ∑ c, tval (σ c)

theorem rankS_update_lt (σ : Fin 3 → CType) (c : Fin 3) (t : CType) (h : tval t < tval (σ c)) :
    rankS (Function.update σ c t) < rankS σ := by
  unfold rankS
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), ← Finset.add_sum_erase _ _ (Finset.mem_univ c)]
  have : ∑ x ∈ Finset.univ.erase c, tval (Function.update σ c t x) =
      ∑ x ∈ Finset.univ.erase c, tval (σ x) :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]
  omega

/-- The number of unmarked children. -/
def numN (σ : Fin 3 → CType) : ℕ := (Finset.univ.filter fun c => σ c = none).card

/-- `loop_sigma = (1/4) sum over the children of type U_t of K(t -> (1, t))`. -/
noncomputable def loopS (K : ℕ → ℕ → ℕ → ℝ) (σ : Fin 3 → CType) : ℝ :=
  1 / 4 * ∑ c, match σ c with
    | none => 0
    | some t => K t 1 t

/-- `lost_sigma = (1/4) sum over the children of type U_t of K(t -> (0, t))`. -/
noncomputable def lostS (K : ℕ → ℕ → ℕ → ℝ) (σ : Fin 3 → CType) : ℝ :=
  1 / 4 * ∑ c, match σ c with
    | none => 0
    | some t => K t 0 t

/-- The R recursion at a height `h ≥ 1` (Section 13), the loop solved out: `W_sigma(0)` is the point
mass at `(0, #N(sigma))` and
`W_sigma(p) = [(1/4) up(W_sigma(p-1)) + lost_sigma W_sigma(p-1)
  + (1/4) sum_(c : N) sum_(b, f') rho(b, f') W_(sigma(c -> U_f'))(min(p-1+b, P))
  + (1/4) sum_(c : U_t) sum_(a, f' < t) K(t -> (a, f')) W_(sigma(c -> U_f'))(min(p-1+a, P))]
  / (1 - loop_sigma)`. -/
noncomputable def Wrec (V P : ℕ) (rho : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) :
    (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ
  | σ, 0, x, g => if x = 0 ∧ g = numN σ then 1 else 0
  | σ, p + 1, x, g =>
    (1 / 4 * upV V (fun x' g' => Wrec V P rho K σ p x' g') x g +
        lostS K σ * Wrec V P rho K σ p x g +
        1 / 4 * ∑ c : Fin 3, (match _hc : σ c with
          | none => ∑ b ∈ Finset.range (V + 1), ∑ f' : Fin 4,
              rho b f' * Wrec V P rho K (Function.update σ c (some f')) (min (p + b) P) x g
          | some t => ∑ a ∈ Finset.range (V + 1), ∑ f' : Fin 4,
              if _hf : f' < t then
                K t a f' * Wrec V P rho K (Function.update σ c (some f')) (min (p + a) P) x g
              else 0)) /
      (1 - loopS K σ)
termination_by σ p => (rankS σ, p)
decreasing_by
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · refine Prod.Lex.left _ _ (rankS_update_lt σ c _ ?_)
    rw [_hc]; simp only [tval]; omega
  · refine Prod.Lex.left _ _ (rankS_update_lt σ c _ ?_)
    rw [_hc]; simp only [tval]; exact _hf

/-- `Rhat_h[rho, K] = W_NNN(2)`. -/
noncomputable def Rhat (V P : ℕ) (rho : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (b f : ℕ) : ℝ :=
  Wrec V P rho K (fun _ => none) 2 b f

/-- `Wtop_q[rho, K] = W_NNN(q)`. -/
noncomputable def Wtop (V P : ℕ) (rho : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (q x f : ℕ) : ℝ :=
  Wrec V P rho K (fun _ => none) q x f

/-! ## Proposition 13.3 -/

/-- Stored laws of a run: `rho h b f'` (`rho*_h`), `K h t a f'` (`K*_h(t -> (a, f'))`) and the top
arrays `Wt q x f'` (`Wtil_q`). -/
structure M1Run where
  rho : ℕ → ℕ → ℕ → ℝ
  K : ℕ → ℕ → ℕ → ℕ → ℝ
  Wt : ℕ → ℕ → ℕ → ℝ

/-- A probability vector on `{0..V} × {0..n}`. -/
def IsProbVec (V n : ℕ) (w : ℕ → ℕ → ℝ) : Prop :=
  (∀ a f, 0 ≤ w a f) ∧ (∀ a f, V < a ∨ n < f → w a f = 0) ∧
    ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (n + 1), w a f = 1

/-- `w ≤ w'` entrywise on `{0..V} × {0..n}` off the bottom `(0, 0)`. -/
def OffBottomLe (V n : ℕ) (w w' : ℕ → ℕ → ℝ) : Prop :=
  ∀ a ≤ V, ∀ f ≤ n, (a ≠ 0 ∨ f ≠ 0) → w a f ≤ w' a f

/-- The hypotheses (i) and (ii) of Proposition 13.3 for the heights `0..m-1`: probability vectors,
`rho*_0 ≤ Rhat_0`, `K*_0(f -> .) ≤ Khat_0(f -> .)`, and for `1 ≤ h ≤ m - 1`,
`rho*_h ≤ Rhat_h[rho*_(h-1), K*_(h-1)]` and `K*_h(f -> .) ≤ Khat_h[rho*_(h-1)](f -> .)`, entrywise
off the bottom. -/
def F3Hyp (V P L m : ℕ) (R : M1Run) : Prop :=
  (∀ h < m, IsProbVec V 3 (R.rho h)) ∧ (∀ h < m, ∀ t ≤ 3, IsProbVec V t (R.K h t)) ∧
    OffBottomLe V 3 (R.rho 0) (Rhat0 V L) ∧ (∀ t ≤ 3, OffBottomLe V t (R.K 0 t) (Khat0 L t)) ∧
    ∀ h, 1 ≤ h → h < m →
      OffBottomLe V 3 (R.rho h) (Rhat V P (R.rho (h - 1)) (R.K (h - 1))) ∧
        ∀ t ≤ 3, OffBottomLe V t (R.K h t) (KhatH V P L (R.rho (h - 1)) t)

/-- **Proposition 13.3 of the paper**. For the truncated model `M1_L` with answer cap `V ≥ 1`, pool
cap `P ≥ 2`, `L ≥ 2`, at height `m ≥ 1` with `1 ≤ k` entrants and `k + 1 ≤ P`: if the stored laws
satisfy (i) and (ii) and
`Wtil ≤ Wtop_(k+1)[rho*_(m-1), K*_(m-1)]` entrywise, then for `g < V`,
`P(G_m(k) ≤ g) ≤ 1 - sum over x > g of Wtil(x, .)`, and `E G_m(k) ≥ sum over x of x Wtil(x, .)`. -/
def f3L : Prop :=
  ∀ (V P L m : ℕ) (_hV : 1 ≤ V) (_hP : 2 ≤ P) (_hL : 2 ≤ L) (_hm : 1 ≤ m) (R : M1Run)
    (_hR : F3Hyp V P L m R) (k : ℕ) (_hk : 1 ≤ k) (_hkP : k + 1 ≤ P) (Wtil : ℕ → ℕ → ℝ)
    (_hW : ∀ x ≤ V, ∀ f ≤ 3, Wtil x f ≤ Wtop V P (R.rho (m - 1)) (R.K (m - 1)) (k + 1) x f),
    (∀ g < V, cdfG m k g ≤ 1 - ∑ x ∈ Finset.Ioc g V, ∑ f ∈ Finset.range 4, Wtil x f) ∧
      ∑ x ∈ Finset.range (V + 1), (x : ℝ) * ∑ f ∈ Finset.range 4, Wtil x f ≤ meanG m k

/-! ## The seed (Lemma 13.4) -/

/-- `e_k = sum over x of x W_k(x)`. -/
noncomputable def eS (W : ℕ → ℕ → ℝ) (V k : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (V + 1), (x : ℝ) * W k x

/-- `c_k(g) = 1 - sum over x > g of W_k(x)`. -/
noncomputable def cS (W : ℕ → ℕ → ℝ) (V k g : ℕ) : ℝ :=
  1 - ∑ x ∈ Finset.Ioc g V, W k x

/-- `min(mu_m0(k), D0(k))`, `D0(k) = min over 1 ≤ k' ≤ k of (mu_m0(k') - e_k')`; it is
`delta0(k) mu_m0(k)` with `delta0(k) = min(1, D0(k)/mu_m0(k))`, and `mu_m0(0)` at `k = 0`. -/
noncomputable def D0 (W : ℕ → ℕ → ℝ) (V m0 k : ℕ) : ℝ :=
  (Finset.Icc 1 k).fold min (mu m0 k) fun k' => mu m0 k' - eS W V k'

/-- The terms of the seed's cdf entry `(k, g)`: `R` (`c_k(g)`, `g < V`), `C`, `L` and `t<i>` with
`Delta = delta0(k) mu_m0(k)` at `mu_m0(k)`, and `J` (`prev = F0(k - 1, g)`). -/
noncomputable def preSeed (W : ℕ → ℕ → ℝ) (V m0 k g : ℕ) (prev : ℝ) : ℝ :=
  min (min (if g < V then cS W V k g else 1) (binCdf k (1 / 3) g))
    (min (L12 (D0 W V m0 k) (mu m0 k) g) prev)

/-- The seed's cdf rows, each the minimum over `g' ≥ g` (`g' ≤ GM`) of its terms. -/
noncomputable def F0 (W : ℕ → ℕ → ℝ) (V m0 GM : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun g => (Finset.Icc g GM).fold min (preSeed W V m0 (k + 1) g (F0 W V m0 GM k g))
      fun g' => preSeed W V m0 (k + 1) g' (F0 W V m0 GM k g')

/-- The seed state `S0 = (F0, delta0)` of Section 13, from the masses `W k x = W_k(x)`. -/
noncomputable def seedState (V m0 GM : ℕ) (W : ℕ → ℕ → ℝ) : State :=
  ⟨F0 W V m0 GM, fun k => D0 W V m0 k / mu m0 k⟩

/-- **Lemma 13.4 of the paper**: from `P(G_m0(k) ≤ g) ≤ c_k(g)` (`g < V`) and
`E G_m0(k) ≥ e_k` for `1 ≤ k ≤ E`, the seed state is valid at `m0`. -/
def seed_valid : Prop :=
  ∀ (V m0 : ℕ) (P : StParams) (W : ℕ → ℕ → ℝ)
    (_hc : ∀ k, 1 ≤ k → k ≤ P.E → ∀ g < V, cdfG m0 k g ≤ cS W V k g)
    (_he : ∀ k, 1 ≤ k → k ≤ P.E → eS W V k ≤ meanG m0 k),
    Valid P m0 (seedState V m0 P.GM W)

end FrogModel.D3.Iface
