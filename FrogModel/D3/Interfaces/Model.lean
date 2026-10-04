module

public import FrogModel.Pieces.Defs
public import FrogModel.LemmaR.Planted.Statement

@[expose] public section

/-!
# The interface of Sections 8 and 10: the planted model and the closure (d = 3)

Definition 8.1, Lemma 8.3 and Lemmas 10.1 to 10.4 of the paper. Everything below is stated over
Mathlib objects and the frozen definitions of FrogModel/Defs.lean and FrogModel/Pieces/Defs.lean
(`stepLaw`, `walkStar` on the planted tree `T*`). The statements are `Prop` definitions, proved in
FrogModel/D3/LaneA and FrogModel/D3/LaneB under names of their own; the other definitions are used
throughout FrogModel/D3.

The planted model on frog paths (Definition 8.1). The vertex `w` is `some []` of `T*`, its parent
the leaf `y = none`. The frogs are the entrants `inl i` (`i < k`) and the frog `inr v` of every
vertex `v` of `T(w)` (`v = []` is `w`); every frog follows its own walk, an i.i.d. sequence of
uniform steps (`pathMeasure`). `Woken m k π` is the least set of frogs containing the entrants and
the frog of every vertex of depth at most `m` visited by the path of a woken frog; `plantedG m k π`
is `G_m(k)`, the number of woken frogs whose path reaches `y`, and `presN m k π` the number of
presences at `w` (pairs of a woken frog and a time it is at `w`), the `N` of the closure.

The closure (Section 10 of the paper). Three child curves `G c` and the directions `D i` at
`w` (`0`: up, `c.succ`: into the child `c`, counted from `i = 0`). With `q` initial frogs,
`T(n) = q + ∑_c G_c(k_c(n))`, `N` the least `n ≥ q` with `T(n) ≤ n` (`⊤` if there is none),
`X = k_up(N)` and `e_c = k_c(N)` (`T`, `N` and `k_a` are `Lambda_q`, `nu(q)` and `n_a` in the
paper). For `j ≥ 1` entrants, `q = j + 1`.

Real-valued quantities: `cdfG m k g = P(G_m(k) ≤ g)`, `tailG m k x = P(G_m(k) ≥ x)`,
`meanG m k = E G_m(k)`, `mu m k = (m + 1 + k)/3`, `deficit m k = mu m k - meanG m k`. `meanG` is the
real part of a lintegral; `lintegral_plantedG_le` makes it finite, so no junk value enters.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## The planted model on frog paths -/

/-- The frogs of the planted model at `w`: the entrants `inl i` and the frog `inr v` of the vertex
`v` of `T(w)`. -/
abbrev PFrog := ℕ ⊕ Vertex 3

/-- Where a frog starts: an entrant at `w`, the frog of `v` at `v`. -/
def frogStart : PFrog → Vertex 3
  | Sum.inl _ => []
  | Sum.inr v => v

/-- The depth of a frog's start in `T(w)`. -/
def frogDepth : PFrog → ℕ
  | Sum.inl _ => 0
  | Sum.inr v => v.length

/-- The law of the frog paths: the steps of every frog i.i.d. of law `stepLaw 3`. -/
noncomputable def pathMeasure : Measure (PFrog → ℕ → Step 3) :=
  Measure.infinitePi fun _ : PFrog => Measure.infinitePi fun _ : ℕ => stepLaw 3

instance : IsProbabilityMeasure pathMeasure := by unfold pathMeasure; infer_instance

/-- The position on `T*` of frog `φ` after `i` steps of its path. -/
def pos (π : PFrog → ℕ → Step 3) (φ : PFrog) (i : ℕ) : Option (Vertex 3) :=
  walkStar (some (frogStart φ)) (π φ) i

/-- The woken set at height `m` with `k` entrants. -/
inductive Woken (m k : ℕ) (π : PFrog → ℕ → Step 3) : PFrog → Prop
  | ent (i : ℕ) : i < k → Woken m k π (Sum.inl i)
  | wake (φ : PFrog) (v : Vertex 3) (n : ℕ) :
      Woken m k π φ → v.length ≤ m → pos π φ n = some v → Woken m k π (Sum.inr v)

/-- `G_m(k)`: the woken frogs whose path reaches `y`. -/
noncomputable def plantedG (m k : ℕ) (π : PFrog → ℕ → Step 3) : ℕ∞ :=
  {φ | Woken m k π φ ∧ ∃ n, pos π φ n = none}.encard

/-- `N`: the presences at `w`, pairs of a woken frog and a time at which it is at `w`. -/
noncomputable def presN (m k : ℕ) (π : PFrog → ℕ → Step 3) : ℕ∞ :=
  {p : PFrog × ℕ | Woken m k π p.1 ∧ pos π p.1 p.2 = some []}.encard

/-- The planted curve `k ↦ G_m(k)`. -/
noncomputable def plantedCurve (m : ℕ) (π : PFrog → ℕ → Step 3) : ℕ → ℕ∞ :=
  fun k => plantedG m k π

/-- The presence curve `k ↦ N_m(k)`. -/
noncomputable def presCurve (m : ℕ) (π : PFrog → ℕ → Step 3) : ℕ → ℕ∞ :=
  fun k => presN m k π

/-- The law of the planted curve at height `m`. -/
noncomputable def curveLaw (m : ℕ) : Measure (ℕ → ℕ∞) :=
  pathMeasure.map (plantedCurve m)

instance (m : ℕ) : IsProbabilityMeasure (curveLaw m) := by unfold curveLaw; infer_instance

/-- `P(G_m(k) ≤ g)`. -/
noncomputable def cdfG (m k g : ℕ) : ℝ :=
  (pathMeasure {π | plantedG m k π ≤ (g : ℕ∞)}).toReal

/-- `P(G_m(k) ≥ x)`. -/
noncomputable def tailG (m k x : ℕ) : ℝ :=
  (pathMeasure {π | (x : ℕ∞) ≤ plantedG m k π}).toReal

/-- `E G_m(k)`. -/
noncomputable def meanG (m k : ℕ) : ℝ :=
  (∫⁻ π, (plantedG m k π : ℝ≥0∞) ∂pathMeasure).toReal

/-- `mu_m(k) = (m + 1 + k)/3`, the mean of the all-awake count. -/
noncomputable def mu (m k : ℕ) : ℝ := ((m : ℝ) + 1 + k) / 3

/-- `Delta_m(k) = mu_m(k) - E G_m(k)`. -/
noncomputable def deficit (m k : ℕ) : ℝ := mu m k - meanG m k

/-! ## The closure at `w` -/

/-- The directions at `w`: i.i.d. uniform on `Fin 4` (`0` up, `c.succ` into the child `c`). -/
noncomputable def dirMeasure : Measure (ℕ → Fin 4) :=
  Measure.infinitePi fun _ : ℕ => (uniformOn Set.univ : Measure (Fin 4))

instance : IsProbabilityMeasure dirMeasure := by unfold dirMeasure; infer_instance

/-- A sample of the closure: three child curves and the directions at `w`. -/
abbrev ClosSample := (Fin 3 → ℕ → ℕ∞) × (ℕ → Fin 4)

/-- The closure measure: the three child curves i.i.d. of law `Q`, the directions independent. -/
noncomputable def closMeasure (Q : Measure (ℕ → ℕ∞)) [SigmaFinite Q] : Measure ClosSample :=
  (Measure.pi fun _ : Fin 3 => Q).prod dirMeasure

instance (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] : IsProbabilityMeasure (closMeasure Q) := by
  unfold closMeasure; infer_instance

/-- `k_a(n)`: the number of `i < n` with `D i = a`. -/
def dirCount (D : ℕ → Fin 4) (a : Fin 4) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => D i = a).card

/-- `T(n) = q + ∑_c G_c(k_c(n))`: the presences at `w` created after `n` steps from `w`. -/
noncomputable def closT (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) (n : ℕ) : ℕ∞ :=
  q + ∑ c : Fin 3, G c (dirCount D c.succ n)

/-- `N`: the least `n ≥ q` with `T(n) ≤ n`, `⊤` if there is none. -/
noncomputable def closN (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : q ≤ n ∧ closT q G D n ≤ n), (n : ℕ∞)

/-- `k_a(N)` for `N ∈ ℕ∞`: the directions `a` among the first `N`. -/
noncomputable def countAt (D : ℕ → Fin 4) (a : Fin 4) (N : ℕ∞) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : (n : ℕ∞) ≤ N), (dirCount D a n : ℕ∞)

/-- `X = k_up(N)`: the frogs frozen at `y`. -/
noncomputable def closX (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) : ℕ∞ :=
  countAt D 0 (closN q G D)

/-- `e_c = k_c(N)`: the entries into the child `c`. -/
noncomputable def closE (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) (c : Fin 3) : ℕ∞ :=
  countAt D c.succ (closN q G D)

/-- The parent curve: `0` entrants give `0`, `j ≥ 1` entrants give `X` with `q = j + 1`. -/
noncomputable def closCurve (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) : ℕ → ℕ∞ :=
  fun j => if j = 0 then 0 else closX (j + 1) G D

/-- The presence curve of the closure: `N` with `q = j + 1` for `j ≥ 1`, `0` for `j = 0`. -/
noncomputable def closNCurve (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) : ℕ → ℕ∞ :=
  fun j => if j = 0 then 0 else closN (j + 1) G D

/-! ## The statements -/

/-- Measurability of the planted and presence curves (the maps below are not junk values). -/
def measurable_plantedPair : Prop :=
  ∀ (m : ℕ),
    Measurable fun π : PFrog → ℕ → Step 3 => (plantedCurve m π, presCurve m π)

/-- Measurability of the closure's parent and presence curves. -/
def measurable_closPair : Prop :=
  Measurable fun x : ClosSample => (closCurve x.1 x.2, closNCurve x.1 x.2)

/-- **Lemma 10.1 of the paper** (the closure identity, by the pool argument):
the planted curve and the presence curve at height `m + 1` on the frog paths have the joint law of
the parent curve and the presence curve of the closure whose three children are i.i.d. planted
curves at height `m`. -/
def curveLaw_succ : Prop :=
  ∀ (m : ℕ),
    pathMeasure.map (fun π => (plantedCurve (m + 1) π, presCurve (m + 1) π)) =
      (closMeasure (curveLaw m)).map fun x => (closCurve x.1 x.2, closNCurve x.1 x.2)

/-- The path of a frog at depth `i` of `T(w)` reaches `y` with probability `3^-(i+1)`
(Lemma 10.2 (1) of the paper; a walk from `w` reaches its parent with probability `1/3`). -/
def prob_reach : Prop :=
  ∀ (φ : PFrog),
    pathMeasure {π | ∃ n, pos π φ n = none} = (3⁻¹ : ℝ≥0∞) ^ (frogDepth φ + 1)

/-- `E G_m(k) ≤ mu_m(k)`: `G_m(k) ≤ U_m(k)` pathwise and `E U_m(k) = mu_m(k)` (Lemma 10.2 (1)). -/
def lintegral_plantedG_le : Prop :=
  ∀ (m k : ℕ),
    ∫⁻ π, (plantedG m k π : ℝ≥0∞) ∂pathMeasure ≤ ENNReal.ofReal (mu m k)

/-- Lemma 10.2 (2) of the paper: the planted curve is nondecreasing in the number of entrants, pathwise. -/
theorem plantedG_mono (m k : ℕ) (π : PFrog → ℕ → Step 3) :
    plantedG m k π ≤ plantedG m (k + 1) π := by
  have hW : ∀ φ, Woken m k π φ → Woken m (k + 1) π φ := by
    intro φ h
    induction h with
    | ent i hi => exact Woken.ent i (by omega)
    | wake φ v n _ hv hp ih => exact Woken.wake φ v n ih hv hp
  exact Set.encard_le_encard fun φ h => ⟨hW φ h.1, h.2⟩

/-- A planted curve counts each frog at most once: `G_m(k) ≤ k + (3^(m+1) - 1)/2`, pathwise
(Lemma 10.2 (2) of the paper). -/
def plantedG_le_frogs : Prop :=
  ∀ (m k : ℕ) (π : PFrog → ℕ → Step 3),
    plantedG m k π ≤ (k + (3 ^ (m + 1) - 1) / 2 : ℕ)

/-- **Lemma 10.3 of the paper (coins), at the level of laws.** There is a coupling of the planted
curve at height `m` with coins `ξ i` (the coin of the entry `i + 1`), each true with probability
`1/3`, `ξ i` independent of `(G(0), ..., G(i), ξ 0, ..., ξ (i - 1))`, and
`G(i + 1) ≥ G(i) + ξ i`, `G(0) = 0`, almost surely. -/
def coin_coupling : Prop :=
  ∀ (m : ℕ),
    ∃ μ : Measure ((ℕ → ℕ∞) × (ℕ → Bool)), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = curveLaw m ∧
      (∀ i, μ {z | z.2 i = true} = 3⁻¹) ∧
      (∀ i, IndepFun (fun z => z.2 i)
        (fun z => ((fun l : Fin (i + 1) => z.1 l), (fun l : Fin i => z.2 l))) μ) ∧
      ∀ᵐ z ∂μ, z.1 0 = 0 ∧ ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1)

/-- **Lemma 10.4 of the paper (future domination), in the form used by Lemma 10.6.** For `e ≤ J` and
an event `A` of `(G(0), ..., G(e))`: `E[G(J) 1_A] ≤ E[G(e) 1_A] + P(A) E G(J - e)`. -/
def future_dom : Prop :=
  ∀ (m e J : ℕ) (_heJ : e ≤ J) (B : Set (Fin (e + 1) → ℕ∞)),
    ∫⁻ G in {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ B}, (G J : ℝ≥0∞) ∂curveLaw m ≤
      ∫⁻ G in {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ B}, (G e : ℝ≥0∞) ∂curveLaw m +
        curveLaw m {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ B} *
          ∫⁻ G, (G (J - e) : ℝ≥0∞) ∂curveLaw m

/-- **Lemma 8.3 of the paper** (stated at `m + 1`): `E Z_(m+1) ≥ (1 + E G_m(1))/4`, with `Z` the Lean
planted count `FrogModel.LemmaR.plantedCount` on the frozen model. -/
def lemma19 : Prop :=
  ∀ (m : ℕ),
    (1 + ∫⁻ π, (plantedG m 1 π : ℝ≥0∞) ∂pathMeasure) / 4 ≤
      ∫⁻ ζ, LemmaR.plantedCount (m + 1) ζ ∂frogMeasure 3

end FrogModel.D3.Iface
