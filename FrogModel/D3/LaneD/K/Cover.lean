module

public import FrogModel.D3.LaneD.K.Check
public import FrogModel.D3.LaneD.K.Single

@[expose] public section

/-!
# The parts of a line and their coverage

A line of the certificate is checked in parts. A part is the line with its own deficit range
`d0..d1`, cdf rows `f0..f1`, mask and families (`Part`, `Line.withPart`); each part is one
declaration. `covers L ps` tests that the parts together check every deficit `j = 1..E`, every cdf
entry `(j, v)` (`j = 1..E`, `v ≤ GM`), the shape of every row `j = 1..E`, and, in one part at least,
the shape of the deficits and of row `0`; every part starts at `d0 ≥ 1` and `f0 ≥ 1` (its loops read the
laws of the lower closures and the previous row from there).
-/

namespace FrogModel.D3.LaneD.K

structure Part where
  d0 : Nat
  d1 : Nat
  f0 : Nat
  f1 : Nat
  mask : Nat
  famsA : List (Nat × Nat)
  famsB : List Nat
  shsB : List Nat

/-- The line `L` with the ranges, mask and families of the part `p`. -/
def Line.withPart (L : Line) (p : Part) : Line :=
  { L with d0 := p.d0, d1 := p.d1, f0 := p.f0, f1 := p.f1, mask := p.mask, famsA := p.famsA,
           famsB := p.famsB, shsB := p.shsB }

/-- `lo ≤ j ≤ hi`. -/
def inRange (lo hi j : Nat) : Bool := Nat.ble lo j && Nat.ble j hi

def covers (L : Line) (ps : List Part) : Bool :=
  allN L.E (fun i =>
    let j := Nat.add i 1
    ps.any (fun p => inRange p.d0 p.d1 j && doDef (L.withPart p) j) &&
    ps.any (fun p => inRange p.f0 p.f1 j && bit p.mask 2) &&
    allN (Nat.add L.GM 1) (fun v =>
      ps.any (fun p => inRange p.f0 p.f1 j && doCdf (L.withPart p) j v))) &&
  ps.any (fun p => bit p.mask 2) &&
  ps.all (fun p => Nat.ble 1 p.d0 && Nat.ble 1 p.f0)

end FrogModel.D3.LaneD.K
