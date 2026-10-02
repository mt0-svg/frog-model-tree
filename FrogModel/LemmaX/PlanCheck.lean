module

public import FrogModel.LemmaX.CertStatement

@[expose] public section

/-!
# The check of (I4) in the kernel (condition (C7) of the paper)

`planCheck A den pl` is a data-free Boolean check of a plan `pl` from the atoms `A` of `L`
(`latMeasure A`) into the finite part `hstarFin` of `H*`. The plan has one list of entries
`(i, a)` per path of `cand.paths 4 0 0`, in that order: the entry sends `a / den` from atom `i`
of `A` to the block of the path. The check asks that

- every path is filled exactly: the amounts of its entries sum to `den (1 - eps) pathProb`;
- every entry comes from an atom of `A` below the block of the path, coordinatewise;
- no atom is overdrawn: the amounts drawn from atom `i` are at most `m_i den / 2^40`.

Lookups and per-atom sums go through Kronecker substitution, so that the kernel works on a few
big integers (GMP) instead of quadratic list traversals: the blocks of the atoms are the digits
of `atomCode A` in base `2^16` (coordinates below 16), and the amounts drawn from the atoms are
the digits of `kron planBits pl.flatten` in base `2^planBits` (no carry: the total amount is
below `2^planBits`).

`planI4_of_check` (PlanSound.lean) turns `planCheck A den pl = true` into `PlanI4 (latMeasure A)`.
-/

namespace FrogModel.LemmaX

open FrogModel.Cert

/-- `B(k)` of a path: the sum of its first `k` increments. -/
def cumInc (π : List Tr) (k : ℕ) : ℕ := ((π.take k).map Tr.δ).sum

/-- The block `x` is below the block of the path `π`, coordinatewise. -/
def blockLE (x : ℕ × ℕ × ℕ × ℕ) (π : List Tr) : Bool :=
  decide (x.1 ≤ cumInc π 1) && decide (x.2.1 ≤ cumInc π 2) && decide (x.2.2.1 ≤ cumInc π 3) &&
    decide (x.2.2.2 ≤ cumInc π 4)

/-- Digits to a number in base `B`, least significant first. -/
def packDigits (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: L => d + B * packDigits B L

/-- Kronecker substitution at `2^s` of a list of pairs `(index, value)`. -/
def kron (s : ℕ) (l : List (ℕ × ℕ)) : ℕ := (l.map fun e => e.2 * 2 ^ (s * e.1)).sum

/-- Digit `k` of `N` in base `2^s`. -/
def digit (s N k : ℕ) : ℕ := (N >>> (s * k)) % 2 ^ s

/-- A block with coordinates below 16 as a number below `2^16`. -/
def code4 (x : ℕ × ℕ × ℕ × ℕ) : ℕ := x.1 + 16 * (x.2.1 + 16 * (x.2.2.1 + 16 * x.2.2.2))

/-- The block of a code. -/
def decode4 (c : ℕ) : ℕ × ℕ × ℕ × ℕ := (c % 16, c / 16 % 16, c / 256 % 16, c / 4096 % 16)

/-- The blocks of the atoms as the digits of one number in base `2^16`. -/
def atomCode (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) : ℕ := packDigits (2 ^ 16) (A.map fun a => code4 a.1)

/-- The coordinates of every atom are below 16. -/
def atomsSmall (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) : Bool :=
  A.all fun a => decide (a.1.1 < 16) && decide (a.1.2.1 < 16) && decide (a.1.2.2.1 < 16) &&
    decide (a.1.2.2.2 < 16)

/-- One path and its entries: filled exactly, every entry from an atom (index below `n`, block
the digit of `KA`) below the path. -/
def pathOK (n KA den : ℕ) (π : List Tr) (es : List (ℕ × ℕ)) : Bool :=
  decide ((((es.map Prod.snd).sum : ℕ) : ℚ) = (den : ℚ) * ((1 - cand.eps) * pathProb π)) &&
    es.all fun e => decide (e.1 < n) && blockLE (decode4 (digit 16 KA e.1)) π

/-- The width of a digit of the amounts drawn. -/
def planBits : ℕ := 256

/-- No atom is overdrawn, the amounts drawn being the digits of `N` in base `2^planBits`. -/
def drawnOK (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (den N : ℕ) : Bool :=
  A.zipIdx.all fun a => decide (digit planBits N a.2 * 2 ^ 40 ≤ a.1.2 * den)

/-- **The check of (I4).** -/
def planCheck (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (den : ℕ) (pl : List (List (ℕ × ℕ))) : Bool :=
  decide (0 < den) && atomsSmall A && (cand.paths 4 0 0).length == pl.length &&
    ((cand.paths 4 0 0).zip pl).all (fun q => pathOK A.length (atomCode A) den q.1 q.2) &&
    decide (((pl.flatten).map Prod.snd).sum < 2 ^ planBits) &&
    drawnOK A den (kron planBits pl.flatten)

end FrogModel.LemmaX
