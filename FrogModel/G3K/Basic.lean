module

@[expose] public section

/-!
# Records of the kernel checker of a version 4 certificate (code/certificate/FORMAT.md, items 3 to 5)

`E` is an entry of the data: its key, its flag, its packed vectors V' and W'. `Tr` is a transition
of a child row, with weight `pn / pd` (the factor 1/5 of the step included), increment `delta` and
next child state `next`. `Tree` holds the data: a binary search tree on the keys whose leaves are
the entries, `node p l r` sending the keys `k < p` to `l` and the others to `r`.

A phase-1 vector V' has 495 lanes of 96 bits; the data write it as `cat4 a b c d`, four literals of
at most 124 lanes each, assembled in the kernel (a literal's elaboration and its parse by
Comparator are quadratic in its length).
-/

namespace FrogModel.G3K

structure E where
  key : Nat
  flag : Nat
  v : Nat
  w : Nat
deriving Inhabited

structure Tr where
  pn : Nat
  pd : Nat
  delta : Nat
  next : Nat
deriving Inhabited

inductive Tree where
  | leaf (e : E)
  | node (piv : Nat) (l r : Tree)
deriving Inhabited

/-! Conditionals of the reference forms against the `Bool.rec` of the kernel forms. -/

theorem ite_le {α : Sort _} (a b : Nat) (x y : α) :
    (if a ≤ b then x else y) = Bool.rec (motive := fun _ => α) y x (Nat.ble a b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by simp [Nat.ble_eq_true_of_le hab] at h
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

theorem ite_eq {α : Sort _} (a b : Nat) (x y : α) :
    (if a = b then x else y) = Bool.rec (motive := fun _ => α) y x (Nat.beq a b) := by
  cases h : Nat.beq a b
  · have : ¬ a = b := fun hab => by simp [hab] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem ite_lt {α : Sort _} (a b : Nat) (x y : α) :
    (if a < b then x else y) = Bool.rec (motive := fun _ => α) y x (Nat.ble (Nat.succ a) b) :=
  ite_le (Nat.succ a) b x y

theorem decide_le (a b : Nat) : decide (a ≤ b) = Nat.ble a b := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by simp [Nat.ble_eq_true_of_le hab] at h
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

theorem decide_lt (a b : Nat) : decide (a < b) = Nat.ble (Nat.succ a) b :=
  decide_le (Nat.succ a) b

theorem decide_eq (a b : Nat) : decide (a = b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · have : ¬ a = b := fun hab => by simp [hab] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem and_rec (x y : Bool) : (x && y) = Bool.rec (motive := fun _ => Bool) false y x := by
  cases x <;> rfl

/-- `2 ^ (96 * 124)`, the weight of the second literal of a phase-1 vector. -/
def cutB : Nat := Nat.pow 2 11904

/-- The vector `a + b B + c B^2 + d B^3`, `B = 2 ^ (96 * 124)`. -/
def cat4 (a b c d : Nat) : Nat :=
  Nat.add a (Nat.mul (Nat.add b (Nat.mul (Nat.add c (Nat.mul d cutB)) cutB)) cutB)

end FrogModel.G3K
