module

public import Mathlib

@[expose] public section

/-!
# Abstract objects of Sections 3 and 4 of the paper

Stages of an exploration over indexed pieces (Section 3.2) and the curve of a block sequence
(Section 4.4, `BR(H)`).
-/

namespace FrogModel.Stage

variable {ι P : Type*}

/-- The least set of indices containing `base` and closed under the arcs: `σ` in the set and
`arc σ (ω σ) τ` (the piece of `σ` reaches the index `τ`) put `τ` in the set. -/
def closure (arc : ι → P → ι → Prop) (ω : ι → P) (base : Set ι) : Set ι :=
  ⋂₀ {S | base ⊆ S ∧ ∀ σ ∈ S, ∀ τ, arc σ (ω σ) τ → τ ∈ S}

/-- The stages `Σ_m` (Section 3.2 of the paper): `Σ_0 = ∅`, and `Σ_(m+1)` is the closure of
`σ₀`, `Σ_m` and the successors `succ σ` of the members `σ` of `Σ_m` whose piece is closed. -/
def stages (arc : ι → P → ι → Prop) (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι) (ω : ι → P) :
    ℕ → Set ι
  | 0 => ∅
  | m + 1 => closure arc ω (insert σ₀ (stages arc closed succ σ₀ ω m ∪
      {τ | ∃ σ ∈ stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}))

section Refresh

variable {X : ι → Type*}

/-- `K` is a stopping set: the coordinates of `ω` in `K ω` determine `K ω`. -/
def IsStoppingSet (K : (∀ i, X i) → Set ι) : Prop :=
  ∀ ω ω' : ∀ i, X i, (∀ i ∈ K ω, ω i = ω' i) → K ω' = K ω

/-- The event `G` is determined by the coordinates in the stopping set `K`. -/
def IsDetermined (K : (∀ i, X i) → Set ι) (G : Set (∀ i, X i)) : Prop :=
  ∀ ω ω' : ∀ i, X i, (∀ i ∈ K ω, ω i = ω' i) → (ω ∈ G ↔ ω' ∈ G)

open Classical in
/-- `ω` with its coordinates in `K ω` replaced by those of `ω'` (fresh coordinates). -/
noncomputable def refresh (K : (∀ i, X i) → Set ι) (ω ω' : ∀ i, X i) : ∀ i, X i :=
  fun i => if i ∈ K ω then ω' i else ω i

end Refresh

end FrogModel.Stage

namespace FrogModel.Order

/-- The curve of a block sequence (Section 4.4 of the paper, `BR(H)`), blocks numbered from `0`:
`G(qJ + s) = B_0(J) + ... + B_(q-1)(J) + B_q(s)` for `0 ≤ s < J`. -/
def brCurve (J : ℕ) (B : ℕ → ℕ → ℕ∞) (n : ℕ) : ℕ∞ :=
  (∑ b ∈ Finset.range (n / J), B b J) + B (n / J) (n % J)

open scoped ENNReal in
/-- The mass of `μ` strictly below `x` (the quantile coupling of the proof of Theorem 6.5). -/
noncomputable def cumBelow (μ : ℕ∞ → ℝ≥0∞) (x : ℕ∞) : ℝ≥0∞ := ∑' z, if z < x then μ z else 0

end FrogModel.Order
