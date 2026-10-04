module

public import FrogModel.D3.M1L.GenLaw

@[expose] public section

/-!
# M1_L at every height: the candidate along one read of the machine

The candidate `Ucand` on a machine state is the value `fv` of its head closure, whose end value
`contF` continues with the closures below it. Along a read the closures below the head keep their
summaries (`projS_congr`: the marks change only in the subtree of the head), so the read acts on
the head only, through the equation of a round of `Gen` (`round_id`), the ghost walk (`rL`), an
entry into a child (the child's value is its cost plus the mean over its law, `Gen_lin`), or the
kill coin (`killP_mul_sum`).
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3

/-- The end value of the head closure: the end of the run, or the kill and the closures below. -/
noncomputable def contF (p : Params) (c : ℝ) (top : ℕ → ℝ) (h : ℕ) (r : Bool) (f0 : ℕ)
    (slot : Fin 3) : List Sm → Kid → ℕ → ℝ
  | [] => fun _ a => top a
  | g :: rest => fun k a => c + ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
      killP (κm p r h f0 a (nN k)) a (nN k) b f' *
        fold p c top (h + 1) (applyO p.P b f' slot g :: rest)

theorem fold_cons (p : Params) (c : ℝ) (top : ℕ → ℝ) (h : ℕ) (s0 : Sm) (L : List Sm) :
    fold p c top h (s0 :: L) = fv p c h (contF p c top h s0.isR s0.f0 s0.slot L) s0 := by
  cases L <;> rw [fold] <;> rfl

theorem Ucand_cons (p : Params) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) :
    Ucand p c top ⟨f :: rest, marks, out⟩ =
      fv p c (p.m - f.v.length) (contF p c top (p.m - f.v.length) f.isR f.f0 (f.v.headD 0)
        (projS p marks f.v.head? rest)) (sm p marks none f) := by
  simp only [Ucand, projS]
  rw [fold_cons]
  rfl

theorem fv_d0 (p : Params) (c : ℝ) (h : ℕ) (T : Kid → ℕ → ℝ) (s : Sm) (hd : s.d = 0) :
    fv p c h T s = GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) T s.kid s.n s.a := by
  simp [fv, hd]

theorem fv_ghost (p : Params) (c : ℝ) (h : ℕ) (T : Kid → ℕ → ℝ) (s : Sm) (hd : s.d ≠ 0) :
    fv p c h T s = c * gcost p.L s.d +
      rL p.L s.d * GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) T s.kid (s.n + 1) s.a +
      (1 - rL p.L s.d) * GenH p h s.isR (inp p h) (addC p c h s.isR (cinp p c h)) T s.kid s.n s.a := by
  simp [fv, hd]

/-- A closure that ends (empty pool, no ghost) ends the run if it is the top one, and otherwise
waits for its kill coin: the candidate does not see the difference. -/
theorem Ucand_settle (p : Params) (c : ℝ) (top : ℕ → ℝ) (marks : Finset (Vertex 3))
    (f : Frame) (rest : List Frame) :
    Ucand p c top (settle marks (f :: rest)) = Ucand p c top ⟨f :: rest, marks, []⟩ := by
  cases rest with
  | nil =>
    simp only [settle]
    split_ifs with h
    · rw [Ucand_cons, fv_d0 _ _ _ _ _ (by simp [sm, gdepth, h.2])]
      simp only [Ucand, sm, h.1, List.length_nil, GenH]
      rw [Gen_zero]
      rfl
    · rfl
  | cons g rest' =>
    simp only [settle]
    split_ifs <;> rfl

/-- The stack below the head is a chain of parents. -/
def Chain : List Frame → Prop
  | [] => True
  | [_] => True
  | f :: g :: rest => f.v = f.v.headD 0 :: g.v ∧ Chain (g :: rest)

theorem StackOK.chain (p : Params) (marks : Finset (Vertex 3)) :
    ∀ (hd : Bool) (l : List Frame), StackOK p marks hd l → Chain l
  | _, [], _ => trivial
  | _, [_], _ => trivial
  | _, _ :: g :: rest, h => ⟨h.1, StackOK.chain p marks false (g :: rest) h.2.2.2.2.2⟩

/-- The summaries below the head do not see a change of the marks in the subtree of the head. -/
theorem projS_congr (p : Params) (marks marks' : Finset (Vertex 3)) (v0 : Vertex 3)
    (hM : ∀ w, (w ∈ marks' ↔ w ∈ marks) ∨ v0 <:+ w) :
    ∀ (rest : List Frame) (m : Fin 3), Chain rest → (∀ g ∈ rest.head?, (m :: g.v) <:+ v0) →
      projS p marks' (some m) rest = projS p marks (some m) rest
  | [], _, _, _ => rfl
  | g :: rest, m, hc, hs => by
    have hsg : (m :: g.v) <:+ v0 := hs g (by simp)
    simp only [projS]
    congr 1
    · simp only [sm]
      rw [kidM_congr p marks marks' g.v m fun w => (hM w).imp_right fun h => hsg.trans h]
    · cases rest with
      | nil => rfl
      | cons g2 rest3 =>
        obtain ⟨hv, hc'⟩ := hc
        have hhead : g.v.head? = some (g.v.headD 0) := by rw [hv]; rfl
        rw [hhead]
        refine projS_congr p marks marks' v0 hM (g2 :: rest3) (g.v.headD 0) hc' ?_
        intro g' hg'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg'
        subst hg'
        rw [← hv]
        exact (List.suffix_cons m g.v).trans hsg

/-- The value function of the head closure `f` of a stack `f :: rest`. -/
noncomputable def headX (p : Params) (c : ℝ) (top : ℕ → ℝ) (marks : Finset (Vertex 3)) (f : Frame)
    (rest : List Frame) : Kid → ℕ → ℕ → ℝ :=
  GenH p (p.m - f.v.length) f.isR (inp p (p.m - f.v.length))
    (addC p c (p.m - f.v.length) f.isR (cinp p c (p.m - f.v.length)))
    (contF p c top (p.m - f.v.length) f.isR f.f0 (f.v.headD 0) (projS p marks f.v.head? rest))

theorem Ucand_head (p : Params) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (hg : f.ghost = none) :
    Ucand p c top ⟨f :: rest, marks, out⟩ =
      headX p c top marks f rest (kidM p marks f.v none) f.pool.length f.ups.length := by
  rw [Ucand_cons, fv_d0 _ _ _ _ _ (by simp [sm, gdepth, hg])]
  rfl

theorem Ucand_head_ghost (p : Params) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (φ : Frog) (u : Vertex 3)
    (hg : f.ghost = some (φ, u)) (hd : u.length - f.v.length ≠ 0) :
    Ucand p c top ⟨f :: rest, marks, out⟩ =
      c * gcost p.L (u.length - f.v.length) +
        rL p.L (u.length - f.v.length) *
          headX p c top marks f rest (kidM p marks f.v none) (f.pool.length + 1) f.ups.length +
        (1 - rL p.L (u.length - f.v.length)) *
          headX p c top marks f rest (kidM p marks f.v none) f.pool.length f.ups.length := by
  have hgd : gdepth f = u.length - f.v.length := by simp [gdepth, hg]
  rw [Ucand_cons, fv_ghost _ _ _ _ _ (by simp only [sm]; rw [hgd]; exact hd)]
  simp only [sm, hgd]
  rfl

/-- A read sending the head's frog up. -/
theorem step_up (p : Params) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx : x.1.2 = 0) :
    Ucand p c top (upd p ⟨f :: rest, marks, out⟩ x) =
      headX p c top marks f rest (kidM p marks f.v none) ps.length (upA p.V f.ups.length) := by
  simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  rw [Ucand_settle, Ucand_head _ _ _ _ _ _ _ (by simp)]
  simp only [upA]
  split_ifs <;> simp_all [headX]

/-- A read starting a ghost walk from the head: a child at height `0`, or a marked child of an H
closure. -/
theorem step_ghost_entry (p : Params) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx : x.1.2 ≠ 0)
    (hge : f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx :: f.v ∈ marks)) :
    Ucand p c top (upd p ⟨f :: rest, marks, out⟩ x) =
      c * gcost p.L 1 + rL p.L 1 * headX p c top marks f rest (kidM p marks f.v none)
        (ps.length + 1) f.ups.length +
      (1 - rL p.L 1) * headX p c top marks f rest (kidM p marks f.v none) ps.length f.ups.length := by
  simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, hge]
  rw [Ucand_head_ghost _ _ _ _ _ _ _ φ (x.1.2.pred hx :: f.v) rfl (by simp)]
  simp [headX]

/-- The closures below the head keep their summaries when the marks change in the subtree of the
head. -/
theorem projS_rest (p : Params) (marks marks' : Finset (Vertex 3)) (f : Frame) (rest : List Frame)
    (hch : Chain (f :: rest)) (hM : ∀ w, (w ∈ marks' ↔ w ∈ marks) ∨ f.v <:+ w) :
    projS p marks' f.v.head? rest = projS p marks f.v.head? rest := by
  cases rest with
  | nil => rfl
  | cons g rest2 =>
    obtain ⟨hv, hc⟩ := hch
    have hhead : f.v.head? = some (f.v.headD 0) := by rw [hv]; rfl
    rw [hhead]
    refine projS_congr p marks marks' f.v hM (g :: rest2) _ hc ?_
    intro g' hg'
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg'
    subst hg'
    rw [← hv]

/-- The value of the parent after its child at `c'` returns `(b, f')`. -/
theorem fold_parent (p : Params) (c : ℝ) (top : ℕ → ℝ) (marks : Finset (Vertex 3)) (f : Frame)
    (rest : List Frame) (h : ℕ) (hh : p.m - f.v.length = h) (c' : Fin 3) (n : ℕ) (k : Kid)
    (b : ℕ) (f' : Fin 4) :
    fold p c top h (applyO p.P b f' c'
        ⟨f.isR, f.f0, n, f.ups.length, k, 0, f.v.headD 0⟩ :: projS p marks f.v.head? rest) =
      headX p c top marks f rest (Function.update k c' (some f')) (min (n + b) p.P)
        f.ups.length := by
  rw [fold_cons, fv_d0 _ _ _ _ _ rfl]
  subst hh
  rfl

/-- A read entering an unmarked child of the head: an R closure starts there. -/
theorem step_R (p : Params) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx : x.1.2 ≠ 0)
    (hnot : ¬(f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx :: f.v ∈ marks)))
    (hz : x.1.2.pred hx :: f.v ∉ marks) (hM : MarksAnc marks) (hch : Chain (f :: rest))
    (hle : f.v.length ≤ p.m) :
    Ucand p c top (upd p ⟨f :: rest, marks, out⟩ x) =
      childV p c (p.m - f.v.length) f.isR
        (contF p c top (p.m - f.v.length) f.isR f.f0 (f.v.headD 0) (projS p marks f.v.head? rest))
        (kidM p marks f.v none) (ps.length + 1) f.ups.length (x.1.2.pred hx) := by
  set c' := x.1.2.pred hx with hc'
  have hlt : f.v.length < p.m := by
    rcases Nat.lt_or_ge f.v.length p.m with h | h
    · exact h
    · exact absurd (Or.inl (by omega)) hnot
  obtain ⟨h', hh⟩ : ∃ h', p.m - f.v.length = h' + 1 := ⟨p.m - f.v.length - 1, by omega⟩
  have hzl : p.m - (c' :: f.v).length = h' := by simp; omega
  have hkid : kidM p marks f.v none c' = none := by
    unfold kidM
    rw [ite_eq_right (by omega), ite_eq_right (by simp), ite_eq_left hz]
  have hupd : upd p ⟨f :: rest, marks, out⟩ x =
      ⟨⟨c' :: f.v, true, 3, [φ, Sum.inr (c' :: f.v)], [], none, false⟩ :: {f with pool := ps} :: rest,
        insert (c' :: f.v) marks, []⟩ := by
    simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    rw [ite_eq_right hnot, ite_eq_left hz]
  rw [hupd, Ucand_cons, fv_d0 _ _ _ _ _ (by simp [sm, gdepth])]
  simp only [sm, projS, gdepth, List.headD_cons, List.head?_cons, List.length_cons,
    List.length_nil]
  rw [kidM_fresh p marks hM (c' :: f.v) (by simp) hz, kidM_push p marks f.v c' (by omega),
    projS_rest p marks (insert (c' :: f.v) marks) f rest hch (fun w => by
      by_cases hw : w = c' :: f.v
      · exact Or.inr (by rw [hw]; exact List.suffix_cons _ _)
      · exact Or.inl (by simp [hw]))]
  simp only [hg, hzl, Nat.reduceAdd]
  rw [show p.m - (f.v.length + 1) = h' by omega]
  -- the child's value: its cost plus the mean over its law
  rw [contF.eq_2]
  rw [show (fun k a => c + ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
      killP (κm p true h' 3 a (nN k)) a (nN k) b f' *
        fold p c top (h' + 1) (applyO p.P b f' c'
          ⟨f.isR, f.f0, ps.length, f.ups.length, Function.update (kidM p marks f.v none) c' none, 0,
            f.v.headD 0⟩ :: projS p marks f.v.head? rest)) =
      (fun k a => c + ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
        killP (κm p true h' 3 a (nN k)) a (nN k) b f' *
          headX p c top marks f rest (Function.update (kidM p marks f.v none) c' (some f'))
            (min (ps.length + b) p.P) f.ups.length) from by
    funext k a
    congr 1
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun f' _ => ?_
    rw [fold_parent p c top marks f rest (h' + 1) hh c' ps.length _ b f', Function.update_idem]]
  have hc1 : (cinp p c (p.m - f.v.length)).1 =
      GenH p h' true (inp p h') (addC p c h' true (cinp p c h')) (fun _ _ => c) (initK h') 2 0 := by
    rw [hh]
    show (costs p c h').1 = _
    rw [costs_eq]
    rfl
  have hρ : (inp p (p.m - f.v.length)).1 = fun b f => GenH p h' true (inp p h') (fun _ => 0)
      (fun k a => killP (κm p true h' 3 a (nN k)) a (nN k) b f) (initK h') 2 0 := by
    rw [hh]
    show (laws p h').1 = _
    rw [laws_eq]
    rfl
  unfold GenH
  rw [Gen_lin]
  simp only [childV, hkid, bodyG, Nat.add_sub_cancel, hc1, hρ]
  unfold GenH
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f' _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]
  rfl

/-- At height `0` the keep probabilities do not read the counts of unmarked children. -/
theorem κm_zero (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (r : Bool) (f a g : ℕ) : κm p r 0 f a g = κm p r 0 0 a 0 := by
  unfold κm
  rw [show {j | p.keep r 0 f a g j = true} = {j | p.keep r 0 0 a 0 j = true} from by
    ext j; simp [hkeep0]]

/-- A read entering a marked child of the head, an R closure: an H closure starts there. -/
theorem step_H (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx : x.1.2 ≠ 0)
    (hnot : ¬(f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx :: f.v ∈ marks)))
    (hz : x.1.2.pred hx :: f.v ∈ marks) (hle : f.v.length ≤ p.m) (hP : f.pool.length ≤ p.P) :
    Ucand p c top (upd p ⟨f :: rest, marks, out⟩ x) =
      childV p c (p.m - f.v.length) f.isR
        (contF p c top (p.m - f.v.length) f.isR f.f0 (f.v.headD 0) (projS p marks f.v.head? rest))
        (kidM p marks f.v none) (ps.length + 1) f.ups.length (x.1.2.pred hx) := by
  set c' := x.1.2.pred hx with hc'
  have hlt : f.v.length < p.m := by
    rcases Nat.lt_or_ge f.v.length p.m with h | h
    · exact h
    · exact absurd (Or.inl (by omega)) hnot
  have hR : f.isR = true := by
    cases h : f.isR
    · exact absurd (Or.inr ⟨h, hz⟩) hnot
    · rfl
  obtain ⟨h', hh⟩ : ∃ h', p.m - f.v.length = h' + 1 := ⟨p.m - f.v.length - 1, by omega⟩
  have hzl : p.m - (f.v.length + 1) = h' := by omega
  have hpl : ps.length + 1 ≤ p.P := by rw [hp] at hP; simpa using hP
  -- the type of the entered child
  obtain ⟨t, hkid, ht1, ht0⟩ : ∃ t : Fin 4, kidM p marks f.v none c' = some t ∧
      (h' ≠ 0 → (t : ℕ) = unmarked marks (c' :: f.v)) ∧ (h' = 0 → t = 0) := by
    by_cases h0 : h' = 0
    · refine ⟨0, ?_, fun h => absurd h0 h, fun _ => rfl⟩
      unfold kidM
      rw [ite_eq_right (by omega), ite_eq_right (by simp), ite_eq_right (by simpa using hz), ite_eq_left (by omega)]
    · refine ⟨⟨unmarked marks (c' :: f.v), unmarked_lt _ _⟩, ?_, fun _ => rfl, fun h => absurd h h0⟩
      unfold kidM
      rw [ite_eq_right (by omega), ite_eq_right (by simp), ite_eq_right (by simpa using hz), ite_eq_right (by omega)]
  have hupd : upd p ⟨f :: rest, marks, out⟩ x =
      ⟨⟨c' :: f.v, false, unmarked marks (c' :: f.v), [φ], [], none, false⟩ ::
        {f with pool := ps} :: rest, marks, []⟩ := by
    simp only [upd, hk, hg, hp, hx, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    rw [ite_eq_right hnot, ite_eq_right (not_not.mpr hz)]
  rw [hupd, Ucand_cons, fv_d0 _ _ _ _ _ (by simp [sm, gdepth])]
  simp only [sm, projS, gdepth, hg, List.headD_cons, List.head?_cons, List.length_cons,
    List.length_nil, Nat.reduceAdd, hzl]
  rw [kidM_mask p marks f.v c' (by omega), contF.eq_2]
  rw [show (fun k a => c + ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
      killP (κm p false h' (unmarked marks (c' :: f.v)) a (nN k)) a (nN k) b f' *
        fold p c top (h' + 1) (applyO p.P b f' c'
          ⟨f.isR, f.f0, ps.length, f.ups.length, Function.update (kidM p marks f.v none) c' none, 0,
            f.v.headD 0⟩ :: projS p marks f.v.head? rest)) =
      (fun k a => c + ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
        killP (κm p false h' t a (nN k)) a (nN k) b f' *
          headX p c top marks f rest (Function.update (kidM p marks f.v none) c' (some f'))
            (min (ps.length + b) p.P) f.ups.length) from by
    funext k a
    congr 1
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun f' _ => ?_
    rw [fold_parent p c top marks f rest (h' + 1) hh c' ps.length _ b f', Function.update_idem]
    congr 2
    by_cases h0 : h' = 0
    · subst h0
      rw [κm_zero p hkeep0, κm_zero p hkeep0 false t]
    · rw [ht1 h0]]
  -- lump the H closure to the representative child types with `t` unmarked children
  have hnN : nN (kidM p marks (c' :: f.v) none) = nN (kidOf h' t) := by
    by_cases h0 : h' = 0
    · rw [nN_kidM_zero p marks _ none (by simp; omega), nN_kidOf h' t (by have := t.isLt; omega),
        ite_eq_left h0]
    · rw [nN_kidM p marks _ (by simp; omega), nN_kidOf h' t (by have := t.isLt; omega), ite_eq_right h0,
        ht1 h0]
  unfold GenH
  have hRe : isRe h' false = false := by simp [isRe]
  rw [hRe, Gen_lump p.V p.P (pL p.L) _ _ _ _ (fun k k' hkk => by rw [addC_H, addC_H, hkk])
    (fun k k' a hkk => by simp only [hkk]) _ (kidOf h' t) 1 0 hnN, Gen_lin]
  -- the cost and the law of the H closure
  have hc2 : (cinp p c (p.m - f.v.length)).2 t =
      Gen p.V p.P false (pL p.L) (inp p h').1 (inp p h').2 (addC p c h' false (cinp p c h'))
        (fun _ _ => c) (kidOf h' t) 1 0 := by
    rw [hh]
    show (costs p c h').2 t = _
    rw [costs_eq]
    simp [costsAt, GenH, hRe]
  have hK : ∀ b f', (inp p (p.m - f.v.length)).2 t b f' =
      Gen p.V p.P false (pL p.L) (inp p h').1 (inp p h').2 (fun _ => 0)
        (fun k a => killP (κm p false h' t a (nN k)) a (nN k) b f') (kidOf h' t) 1 0 := by
    intro b f'
    rw [hh]
    show (laws p h').2 t b f' = _
    rw [laws_eq]
    simp [lawsAt, GenH, hRe]
  obtain ⟨-, -, -, -, -, hKf, hKa⟩ := inp_ok p hL hV (p.m - f.v.length)
  have hsplit := K_split p.V hV (inp p (p.m - f.v.length)).2 t
    (fun a f' htf => hKf t a f' htf) (fun a ha => hKa t a ha)
    (fun b f' => headX p c top marks f rest (Function.update (kidM p marks f.v none) c' (some f'))
      (min (ps.length + b) p.P) f.ups.length)
  simp only [hK] at hsplit
  simp only [childV, hkid, isRe, hR, Bool.true_and, decide_not, hh, Nat.add_one_ne_zero,
    decide_false, Bool.not_false, ↓reduceIte, bodyG, Nat.add_sub_cancel]
  rw [← hh, hc2]
  simp only [hK]
  have hY0 : headX p c top marks f rest (Function.update (kidM p marks f.v none) c' (some t))
      (min (ps.length + 0) p.P) f.ups.length =
      headX p c top marks f rest (kidM p marks f.v none) ps.length f.ups.length := by
    rw [Function.update_eq_self_iff.mpr hkid.symm, add_zero, min_eq_left (by omega)]
  have hY1 : headX p c top marks f rest (Function.update (kidM p marks f.v none) c' (some t))
      (min (ps.length + 1) p.P) f.ups.length =
      headX p c top marks f rest (kidM p marks f.v none) (ps.length + 1) f.ups.length := by
    rw [Function.update_eq_self_iff.mpr hkid.symm, min_eq_left hpl]
  rw [hY0, hY1] at hsplit
  have hcomm : ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
      headX p c top marks f rest (Function.update (kidM p marks f.v none) c' (some f'))
        (min (ps.length + b) p.P) f.ups.length *
      Gen p.V p.P false (pL p.L) (inp p h').1 (inp p h').2 (fun _ => 0)
        (fun k a => killP (κm p false h' t a (nN k)) a (nN k) b f') (kidOf h' t) 1 0 =
      ∑ b ∈ Finset.range (p.V + 1), ∑ f' : Fin 4,
      Gen p.V p.P false (pL p.L) (inp p h').1 (inp p h').2 (fun _ => 0)
        (fun k a => killP (κm p false h' t a (nN k)) a (nN k) b f') (kidOf h' t) 1 0 *
      headX p c top marks f rest (Function.update (kidM p marks f.v none) c' (some f'))
        (min (ps.length + b) p.P) f.ups.length :=
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun f' _ => mul_comm _ _
  rw [hcomm, hsplit]
  unfold headX GenH
  simp only [hR]
  ring

/-- The value of the head closure with its ghost frog at depth `e` (`0`: back in the pool, `L`:
lost). -/
noncomputable def ghostV (p : Params) (c : ℝ) (A B : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then A else if e = p.L then B else c * gcost p.L e + rL p.L e * A + (1 - rL p.L e) * B

/-- A read of the ghost walk of the head. -/
theorem step_ghost (p : Params) (c : ℝ) (top : ℕ → ℝ) (f : Frame) (rest : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val) (hk : f.killing = false) (φ : Frog)
    (u : Vertex 3) (hg : f.ghost = some (φ, u)) (hsuf : f.v <:+ u)
    (hd1 : f.v.length + 1 ≤ u.length) (hdL : u.length < f.v.length + p.L) :
    Ucand p c top (upd p ⟨f :: rest, marks, out⟩ x) =
      ghostV p c (headX p c top marks f rest (kidM p marks f.v none) (f.pool.length + 1)
          f.ups.length)
        (headX p c top marks f rest (kidM p marks f.v none) f.pool.length f.ups.length)
        (if x.1.2 = 0 then u.length - f.v.length - 1 else u.length - f.v.length + 1) := by
  obtain ⟨w, rfl⟩ := hsuf
  simp only [List.length_append] at hd1 hdL ⊢
  simp only [upd, hk, hg, Bool.false_eq_true, ↓reduceIte]
  by_cases hx : x.1.2 = 0
  · -- up: the tail of the walk
    have hstep : ghostStep (w ++ f.v) x.1 = w.tail ++ f.v := by
      simp only [ghostStep, hx, ↓reduceDIte]
      cases w with
      | nil => simp at hd1
      | cons a w => rfl
    simp only [hstep, hx, ↓reduceIte]
    by_cases hw : w.length = 1
    · have hwt : w.tail = [] := by
        cases w with
        | nil => simp at hw
        | cons a w => simpa using hw
      rw [ite_eq_left (by simp [hwt])]
      rw [Ucand_head _ _ _ _ _ _ _ rfl]
      simp [ghostV, hw, headX]
    · rw [ite_eq_right (fun h => by
          have := congrArg List.length h
          simp at this
          omega)]
      rw [ite_eq_right (by simp; omega)]
      rw [Ucand_head_ghost _ _ _ _ _ _ _ φ (w.tail ++ f.v) rfl (by simp; omega)]
      simp only [ghostV, List.length_append, List.length_tail]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [headX]
      congr 4 <;> omega
  · -- down: one more step below
    have hstep : ghostStep (w ++ f.v) x.1 = (x.1.2.pred hx :: w) ++ f.v := by
      simp [ghostStep, hx]
    simp only [hstep, hx, ↓reduceIte]
    rw [ite_eq_right (fun h => by
        have := congrArg List.length h
        simp at this
        omega)]
    by_cases hL : w.length + 1 = p.L
    · rw [ite_eq_left (by simp; omega), Ucand_settle, Ucand_head _ _ _ _ _ _ _ rfl]
      simp only [ghostV]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      rfl
    · rw [ite_eq_right (by simp; omega)]
      rw [Ucand_head_ghost _ _ _ _ _ _ _ φ ((x.1.2.pred hx :: w) ++ f.v) rfl (by simp; omega)]
      simp only [ghostV, List.length_append, List.length_cons]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [headX]
      congr 4 <;> omega

/-- The parent `g` of the head after the head returns `b` frogs and leaves `f'` unmarked
children. -/
noncomputable def popV (p : Params) (c : ℝ) (top : ℕ → ℝ) (marks : Finset (Vertex 3)) (f g : Frame)
    (rest' : List Frame) (b : ℕ) (f' : Fin 4) : ℝ :=
  fold p c top (p.m - f.v.length + 1)
    (applyO p.P b f' (f.v.headD 0) (sm p marks (some (f.v.headD 0)) g) :: projS p marks g.v.head? rest')

/-- The kill coin of the head: kept, its ups go to the parent; killed, its children are marked. -/
theorem step_kill (p : Params) (c : ℝ) (top : ℕ → ℝ) (f g : Frame) (rest' : List Frame)
    (marks : Finset (Vertex 3)) (out : List Frog) (x : Val) (hk : f.killing = true)
    (_hgg : g.ghost = none) (hv : f.v = f.v.headD 0 :: g.v) (hfm : f.v ∈ marks)
    (hle : f.v.length ≤ p.m) (hgP : g.pool.length ≤ p.P) (hch : Chain (g :: rest')) :
    Ucand p c top (upd p ⟨f :: g :: rest', marks, out⟩ x) =
      if p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v) x.2 then
        popV p c top marks f g rest' f.ups.length ⟨nN (kidM p marks f.v none), nN_lt _⟩
      else popV p c top marks f g rest' 0 0 := by
  have hgl : p.m - g.v.length = p.m - f.v.length + 1 := by
    rw [hv] at hle ⊢
    simp only [List.length_cons] at hle ⊢
    omega
  have hgm : p.m - g.v.length ≠ 0 := by omega
  have hslot : f.v.headD 0 :: g.v ∈ marks := by rw [← hv]; exact hfm
  simp only [upd, hk, ↓reduceIte]
  split_ifs with hkept
  · rw [Ucand_settle, Ucand_cons]
    simp only [popV]
    rw [fold_cons, hgl]
    congr 1
    simp only [sm, applyO, List.length_take, List.length_append, gdepth]
    rw [kidM_pop_kept p marks g.v (f.v.headD 0) hgm hslot (by rw [← hv]; exact nN_lt _)]
    simp only [← hv, min_comm]
  · rw [Ucand_settle, Ucand_cons]
    simp only [popV]
    rw [fold_cons, hgl]
    have hM : ∀ w, (w ∈ marks ∪ kids f.v ↔ w ∈ marks) ∨ g.v <:+ w := by
      intro w
      by_cases hw : w ∈ kids f.v
      · right
        obtain ⟨c'', -, rfl⟩ := Finset.mem_image.mp hw
        rw [hv]
        exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
      · left
        simp [hw]
    rw [projS_rest p marks (marks ∪ kids f.v) g rest' hch hM]
    congr 1
    simp only [sm, applyO, List.length_take, List.length_append, gdepth, List.length_nil,
      add_zero]
    rw [hv, kidM_pop_killed p marks g.v (f.v.headD 0) hgm hslot, ← hv]
    simp only [min_eq_right hgP, min_eq_left hgP]

/-- The value of a head waiting for its kill coin: the coin, then the parent. -/
theorem kill_value (p : Params) (hkeep0 : ∀ r f a f' n, p.keep r 0 f a f' n = p.keep r 0 0 a 0 n)
    (c : ℝ) (top : ℕ → ℝ) (f g : Frame) (rest' : List Frame) (marks : Finset (Vertex 3))
    (out : List Frog) (hp : f.pool = []) (hg : f.ghost = none) (hv : f.v = f.v.headD 0 :: g.v)
    (_hle : f.v.length ≤ p.m) (ha : f.ups.length ≤ p.V) :
    Ucand p c top ⟨f :: g :: rest', marks, out⟩ =
      c + κm p f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v) *
          popV p c top marks f g rest' f.ups.length ⟨nN (kidM p marks f.v none), nN_lt _⟩ +
        (1 - κm p f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v)) *
          popV p c top marks f g rest' 0 0 := by
  have hhead : f.v.head? = some (f.v.headD 0) := by rw [hv]; rfl
  rw [Ucand_head _ _ _ _ _ _ _ hg]
  simp only [headX, GenH, hp, List.length_nil]
  rw [Gen_zero]
  simp only [contF, projS, hhead]
  rw [killP_mul_sum p.V _ _ _ ha (nN_lt _)]
  have hκ : κm p f.isR (p.m - f.v.length) f.f0 f.ups.length (nN (kidM p marks f.v none)) =
      κm p f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v) := by
    by_cases h0 : p.m - f.v.length = 0
    · rw [h0, κm_zero p hkeep0, κm_zero p hkeep0 _ f.f0]
    · rw [nN_kidM p marks f.v h0]
  rw [hκ]
  simp only [popV]
  ring

end FrogModel.D3
