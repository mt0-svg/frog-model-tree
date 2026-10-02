module

public import FrogModel.G3K.Fast

@[expose] public section

/-!
# The kernel form equals the reference form

One equation per function of `G3K.Fast`, ending in `checkAllF_eq : checkAllF = checkAll` and
`allF_stateOKF_eq` (the statement of a chunk theorem). With `Spec.checkAll_sound`, a proof of
`checkAllF t = true` by `decide +kernel` on chunks gives the reference checks at every entry that
`find` returns for its own key (`checkAllF_sound`).
-/

namespace FrogModel.G3K.Equiv
open FrogModel.G3K FrogModel.G3K.Spec FrogModel.G3K.Fast

theorem ite_and_eq {α : Sort _} (a b c d : Nat) (x y : α) :
    (if a = b ∧ c = d then x else y) =
      Bool.rec (motive := fun _ => α) y x
        (Bool.rec (motive := fun _ => Bool) false (Nat.beq c d) (Nat.beq a b)) := by
  rw [← decide_eq a b, ← decide_eq c d]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2]

theorem findF_eq (t : Tree) (k : Nat) : findF t k = t.find k := by
  induction t with
  | leaf e => rfl
  | node p l r ihl ihr =>
    show Bool.rec (motive := fun _ => E) (findF l k) (findF r k) (Nat.ble p k) = _
    rw [ihl, ihr, Tree.find, ite_le]

theorem allF_eq (P : E → Bool) (t : Tree) : allF P t = t.all P := by
  induction t with
  | leaf e => rfl
  | node p l r ihl ihr =>
    show Bool.rec (motive := fun _ => Bool) false (allF P r) (allF P l) = _
    rw [ihl, ihr, Tree.all, and_rec]

theorem encF_eq : encF = enc := rfl
theorem decQF_eq : decQF = decQ := rfl
theorem decC1F_eq : decC1F = decC1 := rfl
theorem decC2F_eq : decC2F = decC2 := rfl
theorem decC3F_eq : decC3F = decC3 := rfl
theorem decC4F_eq : decC4F = decC4 := rfl
theorem decPF_eq : decPF = decP := rfl

theorem encInsF_eq : encInsF = encIns := by
  funext q x y z w p; simp only [encInsF, encIns, ite_le, encF_eq]

theorem sort3F_eq : sort3F = sort3 := by
  funext a b c; simp only [sort3F, sort3, ite_le]

theorem lumpCF_eq : lumpCF = lumpC := rfl

theorem tailOfF_eq : tailOfF = tailOf := by
  funext c; simp only [tailOfF, tailOf, ite_eq]; rfl

theorem lumpKey4F_eq : lumpKey4F = lumpKey4 := by
  funext q c1 c2 c3 c4 p; simp only [lumpKey4F, lumpKey4, sort3F_eq, lumpCF_eq, encInsF_eq]

theorem lo48F_eq : lo48F = lo48 := rfl
theorem up48F_eq : up48F = up48 := rfl

theorem lookF_eq : lookF = look := by
  funext t k lk; simp only [lookF, look, findF_eq, ite_and_eq, ite_eq]

theorem addSameF_eq : addSameF = addSame := by
  funext lo hi t a; simp only [addSameF, addSame, and_rec, decide_le]; rfl
theorem addNextF_eq : addNextF = addNext := by
  funext lo hi t a; simp only [addNextF, addNext, and_rec, decide_le]; rfl
theorem addAbsF_eq : addAbsF = addAbs := rfl
theorem addStopF_eq : addStopF = addStop := rfl

theorem stopWF_eq : stopWF = stopW := by
  funext n3 d3 w num pd e; simp only [stopWF, stopW, wNF_eq, wDF_eq, up48F_eq]; rfl

theorem moveF_eq : moveF = move := by
  funext t q x y z l1 l2 l3 n3 d3 w p2 num pd a
  simp only [moveF, move, ite_lt, ite_eq, addSameF_eq, addNextF_eq, addAbsF_eq, addStopF_eq,
    lookF_eq, encInsF_eq, lumpCF_eq, stopWF_eq, lo48F_eq, up48F_eq]
  rfl

theorem rowLoopF_eq (t : Tree) (q x y z l1 l2 l3 n3 d3 p1 m : Nat) (rs : List Tr) (a : Acc) :
    rowLoopF t q x y z l1 l2 l3 n3 d3 p1 m rs a = rowLoop t q x y z l1 l2 l3 n3 d3 p1 m rs a := by
  induction rs generalizing a with
  | nil => rfl
  | cons r rs ih =>
    show rowLoopF t q x y z l1 l2 l3 n3 d3 p1 m rs
      (moveF t q x y z l1 l2 l3 n3 d3 r.next (Nat.add p1 r.delta) (Nat.mul m r.pn) r.pd a) = _
    rw [ih, moveF_eq, rowLoop]; rfl

theorem tailNF_eq : tailNF = tailN := rfl
theorem tailDF_eq : tailDF = tailD := rfl

theorem tailLoopF_eq (t : Tree) (q x y z l1 l2 l3 n3 d3 ct p1 m : Nat) (k n : Nat) (a : Acc) :
    tailLoopF t q x y z l1 l2 l3 n3 d3 ct p1 m k n a =
      tailLoop t q x y z l1 l2 l3 n3 d3 ct p1 m k n a := by
  induction n generalizing k a with
  | zero => rfl
  | succ n ih =>
    show tailLoopF t q x y z l1 l2 l3 n3 d3 ct p1 m (Nat.add k 1)
      n (moveF t q x y z l1 l2 l3 n3 d3 ct (Nat.add p1 (Nat.add (Nat.add cT 1) k))
        (Nat.mul m (tailNF k)) (tailDF k) a) = _
    rw [ih, moveF_eq, tailLoop]; rfl

theorem cfWF_eq : cfWF = cfW := by
  funext n3 d3 ct m t0 e; simp only [cfWF, cfW, wNF_eq, wDF_eq, up48F_eq]; rfl

theorem maxF_eq (a b : Nat) : maxF a b = max a b := by
  show _ = (if a ≤ b then b else a); rw [ite_le]; rfl

theorem withTailsF_eq : withTailsF = withTails := by
  funext t q x y z l1 l2 l3 n3 d3 ct p m a
  simp only [withTailsF, withTails, addStopF_eq, cfWF_eq, maxF_eq, tailLoopF_eq]; rfl

theorem childF_eq : childF = child := by
  funext t q c x y z p m a
  simp only [childF, child, ite_le, sort3F_eq, lumpCF_eq, wNF_eq, wDF_eq, rowLoopF_eq, rowF_eq,
    withTailsF_eq, tailOfF_eq]
  rfl

theorem movesF_eq : movesF = moves := by
  funext t q c1 c2 c3 c4 p; simp only [movesF, moves, ite_eq, childF_eq]

theorem laneMaskF_eq : laneMaskF = laneMask := rfl

theorem gatherF_eq (u : Nat) (l : List (Nat × Nat × Nat)) : gatherF u l = gather u l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨a, b, s⟩ := x
    show Nat.add (Nat.mul (Nat.land u (laneMaskF a b)) (Nat.pow 2 (Nat.mul 96 s))) (gatherF u l) = _
    rw [ih, gather]; rfl

theorem leLanesF_eq : leLanesF = leLanes := by
  funext G a b; simp only [leLanesF, leLanes, decide_eq]; rfl

theorem wUpF_eq : wUpF = wUp := rfl

theorem finalF_eq : finalF = final := by
  funext s q a ev ew e0 eok
  simp only [finalF, final, and_rec, decide_le, decide_lt, leLanesF_eq, phaseF_eq, gatherF_eq]; rfl

theorem exitSameF_eq : exitSameF = exitSame := by
  funext s q a e0 t
  simp only [exitSameF, exitSame, finalF_eq, gatherF_eq, phaseF_eq, wUpF_eq, decide_le]; rfl
theorem exitNextF_eq : exitNextF = exitNext := by
  funext s q a e0 t
  simp only [exitNextF, exitNext, finalF_eq, gatherF_eq, phaseF_eq, wUpF_eq, decide_le]; rfl

theorem finishF_eq : finishF = finish := by
  funext t s q c1 c2 c3 c4 p a e0
  simp only [finishF, finish, ite_eq, exitSameF_eq, exitNextF_eq, finalF_eq, lookF_eq, encF_eq,
    lumpKey4F_eq]
  rfl

theorem exitStopF_eq : exitStopF = exitStop := by
  funext q c1 c2 c3 c4 p; simp only [exitStopF, exitStop, wNF_eq, wDF_eq, up48F_eq]; rfl

theorem checkSF_eq : checkSF = checkS := by
  funext t s q c1 c2 c3 c4 p; simp only [checkSF, checkS, finishF_eq, movesF_eq, exitStopF_eq]

theorem stateCheckF_eq : stateCheckF = stateCheck := by
  funext t s k; simp only [stateCheckF, stateCheck, checkSF_eq]; rfl

theorem boundsOKF_eq : boundsOKF = boundsOK := by
  funext s q; simp only [boundsOKF, boundsOK, and_rec, decide_eq, phaseF_eq]; rfl

theorem stateOKF_eq : stateOKF = stateOK := by
  funext t e
  simp only [stateOKF, stateOK, and_rec, decide_eq, findF_eq, boundsOKF_eq, stateCheckF_eq,
    decQF_eq]

/-- The statement of a chunk theorem, in reference form. -/
theorem allF_stateOKF_eq (t u : Tree) : allF (stateOKF t) u = u.all (stateOK t) := by
  rw [allF_eq, stateOKF_eq]

theorem checkAllF_eq : checkAllF = checkAll := by
  funext t; simp only [checkAllF, checkAll, allF_stateOKF_eq]

/-- Soundness of the kernel form, for any tree. -/
theorem checkAllF_sound {t : Tree} (h : checkAllF t = true) (k : Nat)
    (hk : (t.find k).key = k) :
    boundsOK (t.find k) (decQ k) = true ∧ stateCheck t (t.find k) k = true :=
  checkAll_sound (by rw [← checkAllF_eq]; exact h) k hk

end FrogModel.G3K.Equiv
