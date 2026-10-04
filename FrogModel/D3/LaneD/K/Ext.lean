module

public import FrogModel.D3.LaneD.K.Single

@[expose] public section

/-!
# The check of one extension (Definition 12.4 of the paper)

The extension at height `h` from `(E0, G0)` to `(E, GM)`: the input state `(Fi, Di)` and the stored
output `(Fo, Do)`, values at `2^-52`; the hint holds the square root witnesses `rho_k` (256-bit slot
`k`, `3 rho_k^2 ≥ (h + 1 + k) 2^256`).

Each stored value is tested against a disjunction of its terms, exactly in integers. Deficit `k`: `1`,
`T` (`mu_h(0)/mu_h(k) = (h + 1)/(h + 1 + k)`), `P` (the stored deficit `k - 1`), the copy (`k ≤ E0`)
and `X` (`E0 < k`: `delta(E0) mu_h(E0)/mu_h(k)`). Cdf entry `(k, g)`: `G`, `J`, the copy (`k ≤ E0`,
`g ≤ G0`), `1`, `L` (the second bound of Lemma 11.1 (3) at the stored deficit, `N = h + 1 + k`) and
`C`.
-/

namespace FrogModel.D3.LaneD.K

/-- The deficit `k` of the extension, stored `o`. -/
def extDef (E0 h Di Do k : Nat) : Bool :=
  let o := slot 64 Do k
  Nat.ble one52 o ||
    Nat.ble (Nat.mul one52 (Nat.add h 1)) (Nat.mul o (Nat.add (Nat.add h 1) k)) ||
    Nat.ble (slot 64 Do (Nat.sub k 1)) o ||
    (Nat.ble k E0 && Nat.ble (slot 64 Di k) o) ||
    (Nat.blt E0 k &&
      Nat.ble (Nat.mul (slot 64 Di E0) (Nat.add (Nat.add h 1) E0)) (Nat.mul o (Nat.add (Nat.add h 1) k)))

/-- The cdf entry `(k, g)` of the extension, stored `o`, with the stored `prev = F(k - 1, g)`,
`next = F(k, g + 1)`, the input value `inV = F_in(k, g)`, `U = delta(k) 2^76` and the witness `rho`. -/
def extEntry (E0 G0 GM h k g o prev next inV U rho : Nat) : Bool :=
  (Nat.blt g GM && Nat.ble next o) || Nat.ble prev o ||
    (Nat.ble k E0 && Nat.ble g G0 && Nat.ble inV o) || Nat.ble one52 o ||
    lOK (Nat.add (Nat.add h 1) k) U rho g o || cOK k g o

/-- The cdf row `k` of the extension. -/
def extRow (E0 G0 GM h : Nat) (Fi Fo : List Nat) (Do hint k : Nat) : Bool :=
  let row := getN Fo k
  let prevRow := getN Fo (Nat.sub k 1)
  let inRow := getN Fi k
  let U := Nat.shiftLeft (slot 64 Do k) 76
  let rho := slot 256 hint k
  allN (Nat.add GM 1) (fun g => extEntry E0 G0 GM h k g (slot 64 row g) (slot 64 prevRow g)
    (slot 64 row (Nat.add g 1)) (slot 64 inRow g) U rho)

/-- The check of the stored extension `(Fo, Do)` of `(Fi, Di)` at height `h`, from `(E0, G0)` to
`(E, GM)`. -/
def extCheck (E0 G0 E GM h : Nat) (Fi : List Nat) (Di : Nat) (Fo : List Nat) (Do hint : Nat) : Bool :=
  Nat.ble E0 E && Nat.ble G0 GM && shapeOK E GM Fo Do &&
    allN E (fun i => extDef E0 h Di Do (Nat.add i 1)) &&
    allN E (fun i => extRow E0 G0 GM h Fi Fo Do hint (Nat.add i 1))

end FrogModel.D3.LaneD.K
