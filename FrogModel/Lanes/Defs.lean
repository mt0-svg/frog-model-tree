module

public import Mathlib

@[expose] public section

/-!
# Packed lanes

A vector of `L` natural numbers in lanes of `W` bits, packed in one natural number, and the
lane-by-lane comparison with guard bits used by the kernel check of the backward certificate
(Section 8.2 of the paper): with every lane below `2^(W-1)`, `a ≤ b` holds in every lane
iff the guard bit (bit `W - 1`) of every lane of `b + G - a` is set.
-/

namespace FrogModel.Lanes

/-- `L` lanes of `W` bits: `pack W L f = ∑_{l < L} f l * 2^(W l)`. -/
def pack (W L : ℕ) (f : ℕ → ℕ) : ℕ := ∑ l ∈ Finset.range L, f l * 2 ^ (W * l)

/-- The guard bits: bit `W - 1` of every lane. -/
def guard (W L : ℕ) : ℕ := pack W L fun _ => 2 ^ (W - 1)

/-- Lane by lane `a ≤ b`, with the guard bits `G`. -/
def leLanes (G a b : ℕ) : Bool := Nat.beq ((b + G - a) &&& G) G

end FrogModel.Lanes
