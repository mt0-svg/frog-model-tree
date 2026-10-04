module

public import FrogModel.D3.LaneD.K.Check

@[expose] public section

/-!
# The cdf terms checked at a single height (the seed and the extension)

The seed (Lemma 13.4 of the paper) and the extension (Definition 12.4) bound each cdf entry by terms
read at one height: the coins `C`, the term `L` of Lemma 11.1 (3) at `mu = N/3`, and stored values.
`lOK` and `cOK` test one stored value `o` (at `2^-52`) against `L` and `C` exactly in integers;
`allN` and `anyN` are the loops.
-/

namespace FrogModel.D3.LaneD.K

/-- `f 0 && ... && f (n - 1)`. -/
def allN (n : Nat) (f : Nat → Bool) : Bool := natFold n true (fun i acc => acc && f i)

/-- `f 0 || ... || f (n - 1)`. -/
def anyN (n : Nat) (f : Nat → Bool) : Bool := natFold n false (fun i acc => acc || f i)

/-- The term `L` (the second bound of Lemma 11.1 (3) of the paper) at entry `v`, `mu = N/3` and
`D ≤ U 2^-128 mu`, against the stored `o`: `3 (v + 1) < N`, the witness `3 rho^2 ≥ N 2^256` and
`2 U N + 3 rho ≤ o 2^77 (N - 3 (v + 1))`. -/
def lOK (N U rho v o : Nat) : Bool :=
  Nat.blt (Nat.mul 3 (Nat.add v 1)) N &&
    Nat.ble (Nat.shiftLeft N 256) (Nat.mul 3 (Nat.mul rho rho)) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 2 U) N) (Nat.mul 3 rho))
      (Nat.mul (Nat.shiftLeft o 77) (Nat.sub N (Nat.mul 3 (Nat.add v 1))))

/-- The coin term `C`: `P(Bin(k, 1/3) ≤ v) ≤ o 2^-52`. -/
def cOK (k v o : Nat) : Bool := Nat.ble (Nat.shiftLeft (binCdfN k v 2) 52) (Nat.mul o (Nat.pow 3 k))

/-- The shape of a stored state with rows `0..E` of slots `0..GM` and deficits `0..E`: values at most
`2^52`, rows nondecreasing, row `0` and deficit `0` equal to `2^52`. -/
def shapeOK (E GM : Nat) (F : List Nat) (D : Nat) : Bool :=
  allN (Nat.add E 1) (fun k =>
      let row := getN F k
      allN (Nat.add GM 1) (fun g => Nat.ble (slot 64 row g) one52 &&
        (Nat.beq g GM || Nat.ble (slot 64 row g) (slot 64 row (Nat.add g 1))))) &&
    allN (Nat.add E 1) (fun k => Nat.ble (slot 64 D k) one52) &&
    allN (Nat.add GM 1) (fun g => Nat.beq (slot 64 (getN F 0) g) one52) &&
    Nat.beq (slot 64 D 0) one52

end FrogModel.D3.LaneD.K
