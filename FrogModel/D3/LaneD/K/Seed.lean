module

public import FrogModel.D3.LaneD.K.Single

@[expose] public section

/-!
# The check of the seed state (Lemma 13.4 of the paper)

The masses `n_k(x) = 2^62 W_k(x)` (`k = 1..32`, `x = 0..48`) are the 64-bit slots `49 (k - 1) + x` of
`massPk`. The stored seed is the state `(F, D)` at `(E, GM) = (32, 96)`, values at `2^-52`; the hint
holds the square root witnesses `rho_k` (256-bit slot `k`, `3 rho_k^2 ≥ (101 + k) 2^256`).

Each stored value is tested against a disjunction of its terms, exactly in integers. Deficit `k`: the
term `1` or a term `M<k'>`, `(mu_100(k') - e_k')/mu_100(k)` with `mu_100(k) = (101 + k)/3`. Cdf entry
`(k, g)`: `G` (the stored `F(k, g + 1)`), `J` (the stored `F(k - 1, g)`), `1`, `R` (`c_k(g)`, `g < 48`),
`L` (the second bound of Lemma 11.1 (3) at the stored deficit, `N = 101 + k`) and `C`.
-/

namespace FrogModel.D3.LaneD.K

/-- `n_k(x)`. -/
def mass (massPk k x : Nat) : Nat := slot 64 massPk (Nat.add (Nat.mul 49 (Nat.sub k 1)) x)

/-- `sum over x in (g, 48] of n_k(x)`. -/
def massAbove (massPk k g : Nat) : Nat :=
  natFold (Nat.sub 48 g) 0 (fun i acc => Nat.add acc (mass massPk k (Nat.add (Nat.add g 1) i)))

/-- `2^62 e_k = sum over x ≤ 48 of x n_k(x)`. -/
def massMean (massPk k : Nat) : Nat :=
  natFold 49 0 (fun x acc => Nat.add acc (Nat.mul x (mass massPk k x)))

/-- The deficit `k` of the seed, stored `o`: the term `1`, or a term `M<k'>`, `1 ≤ k' ≤ k`:
`(101 + k') 2^62 ≤ o (101 + k) 2^10 + 3 E_k'`. -/
def seedDef (massPk D k : Nat) : Bool :=
  let o := slot 64 D k
  Nat.ble one52 o ||
    anyN k (fun i => Nat.ble (Nat.shiftLeft (Nat.add 101 (Nat.add i 1)) 62)
      (Nat.add (Nat.shiftLeft (Nat.mul o (Nat.add 101 k)) 10) (Nat.mul 3 (massMean massPk (Nat.add i 1)))))

/-- The cdf entry `(k, g)` of the seed, stored `o`, with the stored `prev = F(k - 1, g)`,
`next = F(k, g + 1)`, `U = delta(k) 2^76` and the witness `rho`. -/
def seedEntry (massPk k g o prev next U rho : Nat) : Bool :=
  (Nat.blt g 96 && Nat.ble next o) || Nat.ble prev o || Nat.ble one52 o ||
    (Nat.blt g 48 && Nat.ble (Nat.shiftLeft 1 62) (Nat.add (Nat.shiftLeft o 10) (massAbove massPk k g))) ||
    lOK (Nat.add 101 k) U rho g o || cOK k g o

/-- The cdf row `k` of the seed. -/
def seedRow (massPk : Nat) (F : List Nat) (D hint k : Nat) : Bool :=
  let row := getN F k
  let prevRow := getN F (Nat.sub k 1)
  let U := Nat.shiftLeft (slot 64 D k) 76
  let rho := slot 256 hint k
  allN 97 (fun g => seedEntry massPk k g (slot 64 row g) (slot 64 prevRow g) (slot 64 row (Nat.add g 1))
    U rho)

/-- The check of the stored seed `(F, D)` against the masses `massPk`. -/
def seedCheck (massPk : Nat) (F : List Nat) (D hint : Nat) : Bool :=
  shapeOK 32 96 F D && allN 32 (fun i => seedDef massPk D (Nat.add i 1)) &&
    allN 32 (fun i => seedRow massPk F D hint (Nat.add i 1))

end FrogModel.D3.LaneD.K
