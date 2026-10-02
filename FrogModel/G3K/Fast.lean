module

public import FrogModel.G3K.Spec

@[expose] public section

/-!
# The kernel form of the checker

The functions of `G3K.Spec`, written for `decide +kernel` in the Lean kernel and in nanoda: the
tree, the lists of row transitions and of gathers walked by their recursors (`Tree.rec`,
`List.rec`), the tail atoms by `Nat.rec`, every conditional a `Bool.rec` on `Nat.ble` or `Nat.beq`,
the arithmetic through the `Nat.*` functions that both kernels evaluate on literals, numerals as raw
literals. `G3K.Equiv` proves each function equal to its reference form. Kernel only: these
definitions have no compiled code.
-/

namespace FrogModel.G3K.Fast
open FrogModel.G3K FrogModel.G3K.Spec

noncomputable section

/-- The key is an argument of the motive, not a variable of the minor premises: then the recursor
terms `Tree.rec … u` are the same for every lookup of a declaration and the kernel's cache shares
them (with the key in the minor premise, 20000 lookups cost 30 times 5000, out/g3k_forms.txt). -/
def findF (t : Tree) (k : Nat) : E :=
  Tree.rec (motive := fun _ => Nat → E) (fun e _ => e)
    (fun p _ _ fl fr k => Bool.rec (motive := fun _ => E) (fl k) (fr k) (Nat.ble p k)) t k

def allF (P : E → Bool) (t : Tree) : Bool :=
  Tree.rec (motive := fun _ => Bool) (fun e => P e) (fun _ _ _ bl br => Bool.rec false br bl) t

def encF (q a b c d p : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul
    (Nat.add (Nat.mul q (nat_lit 128)) a) (nat_lit 128)) b) (nat_lit 128)) c) (nat_lit 128)) d)
    (nat_lit 128)) p

def decQF (k : Nat) : Nat := Nat.div k (nat_lit 34359738368)
def decC1F (k : Nat) : Nat := Nat.mod (Nat.div k (nat_lit 268435456)) (nat_lit 128)
def decC2F (k : Nat) : Nat := Nat.mod (Nat.div k (nat_lit 2097152)) (nat_lit 128)
def decC3F (k : Nat) : Nat := Nat.mod (Nat.div k (nat_lit 16384)) (nat_lit 128)
def decC4F (k : Nat) : Nat := Nat.mod (Nat.div k (nat_lit 128)) (nat_lit 128)
def decPF (k : Nat) : Nat := Nat.mod k (nat_lit 128)

def encInsF (q x y z w p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (encF q x y z w p) (encF q x y w z p) (Nat.ble w z))
      (encF q x w y z p) (Nat.ble w y))
    (encF q w x y z p) (Nat.ble w x)

def sort3F (a b c : Nat) : Nat × Nat × Nat :=
  Bool.rec (motive := fun _ => Nat × Nat × Nat)
    (Bool.rec (motive := fun _ => Nat × Nat × Nat)
      (Bool.rec (motive := fun _ => Nat × Nat × Nat) (b, a, c) (b, c, a) (Nat.ble c a))
      (c, b, a) (Nat.ble c b))
    (Bool.rec (motive := fun _ => Nat × Nat × Nat)
      (Bool.rec (motive := fun _ => Nat × Nat × Nat) (a, b, c) (a, c, b) (Nat.ble c b))
      (c, a, b) (Nat.ble c a))
    (Nat.ble a b)

def lumpCF (c : Nat) : Nat := Nat.mod (Nat.div lumpTab (Nat.pow (nat_lit 64) c)) (nat_lit 64)

def tailOfF (c : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (tailOf 1) (tailOf 0) (Nat.beq c 0)

def lumpKey4F (q c1 c2 c3 c4 p : Nat) : Nat :=
  let s := sort3F (lumpCF c1) (lumpCF c2) (lumpCF c3)
  encInsF q s.1 s.2.1 s.2.2 (lumpCF c4) p

def lo48F (n d : Nat) : Nat := Nat.div (Nat.mul n (nat_lit 281474976710656)) d
def up48F (n d : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.add (Nat.mul n (nat_lit 281474976710656)) d) (nat_lit 1)) d

def lookF (t : Tree) (k lk : Nat) : E :=
  let e := findF t k
  let f := findF t lk
  Bool.rec (motive := fun _ => E)
    (Bool.rec (motive := fun _ => E) bad f (Nat.beq f.key lk))
    e (Bool.rec (motive := fun _ => Bool) false (Nat.beq e.flag (nat_lit 1)) (Nat.beq e.key k))

def addSameF (lo hi : Nat) (t : E) (a : Acc) : Acc :=
  Acc.mk (Nat.add a.vs (Nat.mul lo t.v)) a.vn a.av (Nat.add a.ww (Nat.mul hi t.w)) a.pp
    (Nat.add a.sl lo) (Nat.add a.sh hi)
    (Bool.rec (motive := fun _ => Bool) false (Nat.ble t.flag (nat_lit 1)) a.ok)
def addNextF (lo hi : Nat) (t : E) (a : Acc) : Acc :=
  Acc.mk a.vs (Nat.add a.vn (Nat.mul lo t.v)) a.av (Nat.add a.ww (Nat.mul hi t.w)) a.pp
    (Nat.add a.sl lo) (Nat.add a.sh hi)
    (Bool.rec (motive := fun _ => Bool) false (Nat.ble t.flag (nat_lit 1)) a.ok)
def addAbsF (lo : Nat) (a : Acc) : Acc :=
  Acc.mk a.vs a.vn (Nat.add a.av (Nat.mul lo (nat_lit 1099511627776))) a.ww a.pp
    (Nat.add a.sl lo) a.sh a.ok
def addStopF (x : Nat) (a : Acc) : Acc :=
  Acc.mk a.vs a.vn a.av a.ww (Nat.add a.pp x) a.sl a.sh a.ok

def stopWF (n3 d3 w num pd e : Nat) : Nat :=
  up48F (Nat.mul (Nat.mul num (Nat.pow phiN e)) (Nat.mul n3 (wNF w)))
    (Nat.mul (Nat.mul pd (Nat.pow phiD e)) (Nat.mul d3 (wDF w)))

def moveF (t : Tree) (q x y z l1 l2 l3 n3 d3 w p2 num pd : Nat) (a : Acc) : Acc :=
  Bool.rec (motive := fun _ => Acc)
    (Bool.rec (motive := fun _ => Acc)
      (addSameF (lo48F num pd) (up48F num pd)
        (lookF t (encInsF q x y z w p2) (encInsF q l1 l2 l3 (lumpCF w) p2)) a)
      (Bool.rec (motive := fun _ => Acc)
        (addNextF (lo48F num pd) (up48F num pd)
          (lookF t (encInsF (Nat.add q (nat_lit 1)) x y z w (nat_lit 1))
            (encInsF (Nat.add q (nat_lit 1)) l1 l2 l3 (lumpCF w) (nat_lit 1))) a)
        (addAbsF (lo48F num pd) a) (Nat.beq q cJ))
      (Nat.beq p2 (nat_lit 0)))
    (addStopF (stopWF n3 d3 w num pd (Nat.sub (Nat.add p2 cJ) q)) a)
    (Nat.ble (Nat.succ cTP) p2)

def rowLoopF (t : Tree) (q x y z l1 l2 l3 n3 d3 p1 m : Nat) (rs : List Tr) (a : Acc) : Acc :=
  List.rec (motive := fun _ => Acc → Acc) (fun a => a)
    (fun r _ ih a => ih (moveF t q x y z l1 l2 l3 n3 d3 r.next (Nat.add p1 r.delta)
      (Nat.mul m r.pn) r.pd a)) rs a

def tailNF (k : Nat) : Nat := Nat.mul (Nat.mul epsN (Nat.sub rhoD rhoN)) (Nat.pow rhoN k)
def tailDF (k : Nat) : Nat :=
  Nat.mul (Nat.mul (nat_lit 5) epsD) (Nat.pow rhoD (Nat.add k (nat_lit 1)))

def tailLoopF (t : Tree) (q x y z l1 l2 l3 n3 d3 ct p1 m : Nat) (k n : Nat) (a : Acc) : Acc :=
  Nat.rec (motive := fun _ => Nat → Acc → Acc) (fun _ a => a)
    (fun _ ih k a => ih (Nat.add k (nat_lit 1))
      (moveF t q x y z l1 l2 l3 n3 d3 ct (Nat.add p1 (Nat.add (Nat.add cT (nat_lit 1)) k))
        (Nat.mul m (tailNF k)) (tailDF k) a)) n k a

def cfWF (n3 d3 ct m t0 e : Nat) : Nat :=
  up48F
    (Nat.mul (Nat.mul (Nat.mul (Nat.mul m (tailNF (Nat.sub t0 (Nat.add cT (nat_lit 1)))))
      (Nat.mul (Nat.pow phiN t0) (Nat.mul phiD rhoD))) (Nat.pow phiN e)) (Nat.mul n3 (wNF ct)))
    (Nat.mul (Nat.mul (Nat.mul (tailDF (Nat.sub t0 (Nat.add cT (nat_lit 1))))
      (Nat.mul (Nat.pow phiD t0) (Nat.sub (Nat.mul phiD rhoD) (Nat.mul phiN rhoN))))
      (Nat.pow phiD e)) (Nat.mul d3 (wDF ct)))

def maxF (a b : Nat) : Nat := Bool.rec (motive := fun _ => Nat) a b (Nat.ble a b)

def withTailsF (t : Tree) (q x y z l1 l2 l3 n3 d3 ct p m : Nat) (a : Acc) : Acc :=
  addStopF (cfWF n3 d3 ct m (maxF (Nat.add cT (nat_lit 1)) (Nat.sub (Nat.add cTP (nat_lit 2)) p))
      (Nat.sub (Nat.add (Nat.sub p (nat_lit 1)) cJ) q))
    (tailLoopF t q x y z l1 l2 l3 n3 d3 ct (Nat.sub p (nat_lit 1)) m (nat_lit 0)
      (Nat.sub (Nat.add cTP (nat_lit 1)) (Nat.add p cT)) a)

def childF (t : Tree) (q c x y z p m : Nat) (a : Acc) : Acc :=
  let s := sort3F (lumpCF x) (lumpCF y) (lumpCF z)
  let n3 := Nat.mul (Nat.mul (wNF x) (wNF y)) (wNF z)
  let d3 := Nat.mul (Nat.mul (wDF x) (wDF y)) (wDF z)
  Bool.rec (motive := fun _ => Acc)
    (rowLoopF t q x y z s.1 s.2.1 s.2.2 n3 d3 (Nat.sub p (nat_lit 1)) m (rowF c) a)
    (withTailsF t q x y z s.1 s.2.1 s.2.2 n3 d3 (tailOfF c) p m
      (rowLoopF t q x y z s.1 s.2.1 s.2.2 n3 d3 (Nat.sub p (nat_lit 1)) m (rowF c) a))
    (Nat.ble c (nat_lit 1))

def movesF (t : Tree) (q c1 c2 c3 c4 p : Nat) : Acc :=
  Bool.rec (motive := fun _ => Acc)
    (childF t q c4 c1 c2 c3 p (nat_lit 1)
      (Bool.rec (motive := fun _ => Acc)
        (Bool.rec (motive := fun _ => Acc)
          (childF t q c3 c1 c2 c4 p (nat_lit 1) (childF t q c2 c1 c3 c4 p (nat_lit 1)
            (childF t q c1 c2 c3 c4 p (nat_lit 1) acc0)))
          (childF t q c3 c1 c2 c4 p (nat_lit 1) (childF t q c1 c2 c3 c4 p (nat_lit 2) acc0))
          (Nat.beq c2 c1))
        (Bool.rec (motive := fun _ => Acc)
          (childF t q c2 c1 c3 c4 p (nat_lit 2) (childF t q c1 c2 c3 c4 p (nat_lit 1) acc0))
          (childF t q c1 c2 c3 c4 p (nat_lit 3) acc0)
          (Nat.beq c2 c1))
        (Nat.beq c3 c2)))
    (Bool.rec (motive := fun _ => Acc)
      (Bool.rec (motive := fun _ => Acc)
        (childF t q c3 c1 c2 c4 p (nat_lit 2) (childF t q c2 c1 c3 c4 p (nat_lit 1)
          (childF t q c1 c2 c3 c4 p (nat_lit 1) acc0)))
        (childF t q c3 c1 c2 c4 p (nat_lit 2) (childF t q c1 c2 c3 c4 p (nat_lit 2) acc0))
        (Nat.beq c2 c1))
      (Bool.rec (motive := fun _ => Acc)
        (childF t q c2 c1 c3 c4 p (nat_lit 3) (childF t q c1 c2 c3 c4 p (nat_lit 1) acc0))
        (childF t q c1 c2 c3 c4 p (nat_lit 4) acc0)
        (Nat.beq c2 c1))
      (Nat.beq c3 c2))
    (Nat.beq c4 c3)

def laneMaskF (a b : Nat) : Nat :=
  Nat.sub (Nat.pow (nat_lit 2) (Nat.mul (nat_lit 96) b)) (Nat.pow (nat_lit 2) (Nat.mul (nat_lit 96) a))

def gatherF (u : Nat) (l : List (Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add (Nat.mul (Nat.land u (laneMaskF x.1 x.2.1))
      (Nat.pow (nat_lit 2) (Nat.mul (nat_lit 96) x.2.2))) ih) l

def leLanesF (G a b : Nat) : Bool := Nat.beq (Nat.land (Nat.sub (Nat.add b G) a) G) G

def wUpF (t : E) : Nat :=
  Nat.mul (Nat.land t.w lowW) (nat_lit 340282366920938463463374607431768211456)

def finalF (s : E) (q : Nat) (a : Acc) (ev ew e0 : Nat) (eok : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (leLanesF gW (Nat.add (Nat.add a.ww ew)
        (Nat.add (Nat.mul (Nat.mul a.pp (nat_lit 1099511627776)) onesW)
          (Nat.mul e0 (nat_lit 1099511627776))))
      (Nat.mul s.w (nat_lit 281474976710656)))
    (Bool.rec (motive := fun _ => Bool) false
      (leLanesF (phaseF q).gV (Nat.mul s.v (nat_lit 281474976710656))
        (Nat.add (Nat.add a.vs (gatherF a.vn (phaseF q).cp0)) (Nat.add a.av ev)))
      (Bool.rec (motive := fun _ => Bool) false
        (Nat.ble (Nat.add (Nat.add a.pp e0) (nat_lit 1)) (nat_lit 77371252455336267181195264))
        (Bool.rec (motive := fun _ => Bool) false
          (Nat.ble (Nat.add a.sh exitHi) (nat_lit 562949953421312))
          (Bool.rec (motive := fun _ => Bool) false
            (Nat.ble (Nat.add a.sl exitLo) (nat_lit 281474976710656))
            (Bool.rec (motive := fun _ => Bool) false eok a.ok)))))

def exitSameF (s : E) (q : Nat) (a : Acc) (e0 : Nat) (t : E) : Bool :=
  finalF s q a (gatherF (Nat.mul exitLo t.v) (phaseF q).gx) (Nat.mul exitHi (wUpF t)) e0
    (Nat.ble t.flag (nat_lit 1))
def exitNextF (s : E) (q : Nat) (a : Acc) (e0 : Nat) (t : E) : Bool :=
  finalF s q a (gatherF (Nat.mul exitLo t.v) (phaseF q).cp1) (Nat.mul exitHi (wUpF t)) e0
    (Nat.ble t.flag (nat_lit 1))

def finishF (t : Tree) (s : E) (q c1 c2 c3 c4 p : Nat) (a : Acc) (e0 : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (exitSameF s q a e0 (lookF t (encF q c1 c2 c3 c4 (Nat.sub p (nat_lit 1)))
      (lumpKey4F q c1 c2 c3 c4 (Nat.sub p (nat_lit 1)))))
    (Bool.rec (motive := fun _ => Bool)
      (exitNextF s q a e0 (lookF t (encF (Nat.add q (nat_lit 1)) c1 c2 c3 c4 (nat_lit 1))
        (lumpKey4F (Nat.add q (nat_lit 1)) c1 c2 c3 c4 (nat_lit 1))))
      (finalF s q a (Nat.mul (Nat.mul exitLo (nat_lit 1099511627776))
        (nat_lit 79228162514264337593543950336)) (nat_lit 0) e0 true)
      (Nat.beq q cJ))
    (Nat.beq p (nat_lit 1))

def exitStopF (q c1 c2 c3 c4 p : Nat) : Nat :=
  up48F (Nat.mul (Nat.mul th5N (Nat.pow phiN (Nat.sub (Nat.add (Nat.sub p (nat_lit 1)) cJ) q)))
      (Nat.mul (Nat.mul (Nat.mul (wNF c1) (wNF c2)) (wNF c3)) (wNF c4)))
    (Nat.mul (Nat.mul th5D (Nat.pow phiD (Nat.sub (Nat.add (Nat.sub p (nat_lit 1)) cJ) q)))
      (Nat.mul (Nat.mul (Nat.mul (wDF c1) (wDF c2)) (wDF c3)) (wDF c4)))

def checkSF (t : Tree) (s : E) (q c1 c2 c3 c4 p : Nat) : Bool :=
  finishF t s q c1 c2 c3 c4 p (movesF t q c1 c2 c3 c4 p) (exitStopF q c1 c2 c3 c4 p)

def stateCheckF (t : Tree) (s : E) (k : Nat) : Bool :=
  checkSF t s (decQF k) (decC1F k) (decC2F k) (decC3F k) (decC4F k) (decPF k)

def boundsOKF (s : E) (q : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.beq (Nat.land s.w lowWb) s.w)
    (Nat.beq (Nat.land s.v (phaseF q).lowV) s.v)

def stateOKF (t : Tree) (e : E) : Bool :=
  let s := findF t e.key
  Bool.rec (motive := fun _ => Bool) false (stateCheckF t s e.key)
    (Bool.rec (motive := fun _ => Bool) false (boundsOKF s (decQF e.key)) (Nat.beq s.key e.key))

/-- The checked statement: every leaf of `t` checked as a state. -/
def checkAllF (t : Tree) : Bool := allF (stateOKF t) t

end

theorem allF_node {P : E → Bool} {p : Nat} {l r : Tree} (hl : allF P l = true)
    (hr : allF P r = true) : allF P (Tree.node p l r) = true := by
  show Bool.rec false (allF P r) (allF P l) = true
  rw [hl]; exact hr

end FrogModel.G3K.Fast
