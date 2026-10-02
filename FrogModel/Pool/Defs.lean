module

public import FrogModel.Pool.Statement

@[expose] public section

/-!
# Pools: the generic reading map (Lemma 4.3 of the paper)

`readGen coord sel ω n` reads `n` values from `ω : K → E`: at step `k`, with `y` the values read
before and `ℓ` their labels, the label of the step is `sel k y` and the value is
`ω (coord k ℓ (sel k y))`. The pool reading (`poolCoord`, the first unused element of the pool) and
the fresh reading (`freshCoord`, coordinate `(k, i)`) are the two instances (Pool/Read.lean).

`consistent sel ℓ` is the set of value sequences whose labels are `ℓ`, and `cmap coord ℓ` the
coordinates read along `ℓ`.
-/

namespace FrogModel.Pool

variable {J K E : Type*}

/-- The labels of a sequence of values: label `j` is `sel j` of the first `j` values. -/
def labels (sel : ∀ k : ℕ, (Fin k → E) → J) {n : ℕ} (p : Fin n → E) (j : Fin n) : J :=
  sel j (Fin.take j j.isLt.le p)

/-- The values read from `ω`: at step `k` the coordinate `coord k ℓ (sel k y)`, `y` the values
read before and `ℓ` their labels. -/
def readGen (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J) (ω : K → E) :
    (n : ℕ) → Fin n → E
  | 0 => Fin.elim0
  | n + 1 =>
    Fin.snoc (readGen coord sel ω n)
      (ω (coord n (labels sel (readGen coord sel ω n)) (sel n (readGen coord sel ω n))))

/-- The coordinates read along the label sequence `ℓ`. -/
def cmap (coord : ∀ k : ℕ, (Fin k → J) → J → K) {n : ℕ} (ℓ : Fin n → J) (j : Fin n) : K :=
  coord j (Fin.take j j.isLt.le ℓ) (ℓ j)

/-- The value sequences whose labels are `ℓ`. -/
def consistent (sel : ∀ k : ℕ, (Fin k → E) → J) {n : ℕ} (ℓ : Fin n → J) : Set (Fin n → E) :=
  {q | labels sel q = ℓ}

open Classical in
/-- The pool coordinate: label `i` after the labels `ℓ` reads element `#{j | ℓ j = i}` of pool `i`. -/
noncomputable def poolCoord {I : Type*} (k : ℕ) (ℓ : Fin k → I) (i : I) : I × ℕ :=
  (i, ((Finset.univ : Finset (Fin k)).filter fun j => ℓ j = i).card)

/-- The fresh coordinate: step `k` with label `i` reads coordinate `(k, i)`. -/
def freshCoord {I : Type*} (k : ℕ) (_ℓ : Fin k → I) (i : I) : ℕ × I := (k, i)

end FrogModel.Pool
