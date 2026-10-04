module


@[expose] public section

/-!
# Loops, slots and lists for the kernel checker of FrogModel/D3/LaneD

Every loop is a `Nat.rec` (which both the Lean kernel and the compiler evaluate), every selection a
`cond`, the arithmetic through `Nat.*` on naturals. A packed natural holds slots of `w` bits, slot
`i` in the bits `[w i, w (i + 1))`.
-/

namespace FrogModel.D3.LaneD.K

/-- `f (n - 1) (… (f 0 init))`. -/
def natFold {α : Type} (n : Nat) (init : α) (f : Nat → α → α) : α :=
  Nat.rec (motive := fun _ => α) init (fun i acc => f i acc) n

def minN (a b : Nat) : Nat := Nat.sub a (Nat.sub a b)
def maxN (a b : Nat) : Nat := Nat.add b (Nat.sub a b)

/-- `2^w - 1`. -/
def mask (w : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 w) 1

/-- Slot `i` of width `w`. -/
def slot (w x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul w i)) (mask w)

/-- `1` in each of the slots `0..n-1` of width `w`. -/
def ones (w n : Nat) : Nat := Nat.div (mask (Nat.mul w n)) (mask w)

def hd (l : List Nat) : Nat := l.headD 0
def tl (l : List Nat) : List Nat := l.tail
def hdL (l : List (List Nat)) : List Nat := l.headD []
def tlL (l : List (List Nat)) : List (List Nat) := l.tail

/-- The list without its first `n` entries. -/
def dropN (n : Nat) (l : List Nat) : List Nat := natFold n l (fun _ acc => tl acc)
def dropL (n : Nat) (l : List (List Nat)) : List (List Nat) := natFold n l (fun _ acc => tlL acc)

/-- Entry `n` (`0` past the end). -/
def getN (l : List Nat) (n : Nat) : Nat := hd (dropN n l)
def getL (l : List (List Nat)) (n : Nat) : List Nat := hdL (dropL n l)

/-- The `2^d` units of `w` bits of `N` (low first), followed by `acc` (split by halving). -/
def splitAux (w d : Nat) : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun N acc => N :: acc)
    (fun i r N acc =>
      r (Nat.land N (mask (Nat.mul (Nat.shiftLeft 1 i) w)))
        (r (Nat.shiftRight N (Nat.mul (Nat.shiftLeft 1 i) w)) acc)) d

/-- The least `d` with `2^d ≥ n`. -/
def clog (n : Nat) : Nat := cond (Nat.ble n 1) 0 (Nat.add (Nat.log2 (Nat.sub n 1)) 1)

/-- The units of `w` bits of `N`, `n` of them at least (zeros past the end of `N`). -/
def split (w n N : Nat) : List Nat := splitAux w (clog n) N []

/-- `C(n, k)` by the multiplicative formula. -/
def choose (n k : Nat) : Nat :=
  natFold k 1 (fun i c => Nat.div (Nat.mul c (Nat.sub n i)) (Nat.add i 1))

def fact (n : Nat) : Nat := natFold n 1 (fun i r => Nat.mul r (Nat.add i 1))

/-- `ceil(a / b)`. -/
def cdiv (a b : Nat) : Nat := Nat.div (Nat.sub (Nat.add a b) 1) b

/-- The failure count of the test `a ≤ b`: `0` if it holds, `1` if not. -/
def bad (a b : Nat) : Nat := cond (Nat.ble a b) 0 1

end FrogModel.D3.LaneD.K

namespace FrogModel.D3.LaneD.K

/-- Pack a list at the stride `w` (pairs merged level by level). -/
def packRows (w : Nat) (l : List Nat) : Nat :=
  let lvl := fun (w : Nat) (l : List Nat) =>
    (natFold (Nat.div (Nat.add l.length 1) 2) ([], l) (fun _ (st : List Nat × List Nat) =>
      (Nat.add (hd st.2) (Nat.shiftLeft (hd (tl st.2)) w) :: st.1, tl (tl st.2)))).1.reverse
  (natFold (clog l.length) (w, l) (fun _ (st : Nat × List Nat) =>
    (Nat.mul 2 st.1, lvl st.1 st.2))).2.headD 0

end FrogModel.D3.LaneD.K

namespace FrogModel.D3.LaneD.K

/-- `sum over i < 2^d of f(lo + i) 2^(w i)`, by halving (no lists). -/
def packTree (w : Nat) (f : Nat → Nat) (d : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) f
    (fun i r lo => Nat.add (r lo)
      (Nat.shiftLeft (r (Nat.add lo (Nat.shiftLeft 1 i))) (Nat.mul w (Nat.shiftLeft 1 i)))) d

end FrogModel.D3.LaneD.K
