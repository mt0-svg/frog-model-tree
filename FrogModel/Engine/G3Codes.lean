module

public import FrogModel.G3K.Spec
public import FrogModel.Engine.CandKernel

@[expose] public section

/-!
# The codes of the G3 checker against the child chain of `cand`

The checker G3K.Spec numbers the well-formed child states of `cand` by codes `0` to `37` (the list
at the head of G3K.Table): `0` fresh, `1` bdry, the labels of levels 1, 2, 3 from `2`, `11`, `21`,
the tail states of levels 1 to 3 at `32` to `34`, the max labels at `35` to `37`. `decC` reads a
code, `code` writes one (`127` off the well-formed states).

The data of G3K.Table are those of `cand`, checked by the kernel code by code: the row of code `c`
is the finite row of `decC c` with the weights divided by 5 (`row_spec`), the potential `wN / wD`
is `wQ` (`w_spec`), the lump of a code is the code of the lump (`lump_spec`); the tail targets and
the constants (`cJ`, `cT`, `eps`, `rho`, `phi`, `theta / 5`) agree (`tail_spec`, `const_spec`).

The key of a root state with `i < 4` (`keyOf`) is `enc (i + 1) c1 c2 c3 c4 p`, `c1 ≤ c2 ≤ c3 ≤ c4`
the codes of the children sorted (`Multiset.sort`); it depends on the children only through their
multiset, and the keys the checker computes by insertion (`encIns`, `sort3`) are these keys.
-/

namespace FrogModel.Engine.G3

open FrogModel.Cert FrogModel.LemmaX

/-- The child state of code `c`. -/
def decC (c : ℕ) : CState :=
  if c = 0 then .fresh else if c = 1 then .bdry
  else if c ≤ 10 then .lab 1 (c - 2) else if c ≤ 20 then .lab 2 (c - 11)
  else if c ≤ 31 then .lab 3 (c - 21) else if c ≤ 34 then .tail (c - 31)
  else .maxLab (c - 34)

/-- The code of a child state, `127` off the well-formed states of `cand`. -/
def code : CState → ℕ
  | .fresh => 0
  | .bdry => 1
  | .lab q s =>
    if q = 1 ∧ s < 9 then s + 2 else if q = 2 ∧ s < 10 then s + 11
    else if q = 3 ∧ s < 11 then s + 21 else 127
  | .tail q => if 1 ≤ q ∧ q ≤ 3 then q + 31 else 127
  | .maxLab q => if 1 ≤ q ∧ q ≤ 3 then q + 34 else 127

theorem nLabels_cand : cand.nLabels 1 = 9 ∧ cand.nLabels 2 = 10 ∧ cand.nLabels 3 = 11 := by
  decide +kernel

theorem cand_J : cand.J = 4 := rfl

theorem code_lt (s : CState) (hs : cand.ChildWF s) : code s < 38 := by
  obtain ⟨h1, h2, h3⟩ := nLabels_cand
  cases s with
  | fresh => decide
  | bdry => decide
  | lab q t =>
    obtain ⟨hq1, hq2, ht⟩ := hs
    rw [cand_J] at hq2
    interval_cases q <;> simp_all [code] <;> omega
  | tail q =>
    obtain ⟨hq1, hq2⟩ := hs
    rw [cand_J] at hq2
    simp only [code]; split_ifs <;> omega
  | maxLab q =>
    obtain ⟨hq1, hq2⟩ := hs
    rw [cand_J] at hq2
    simp only [code]; split_ifs <;> omega

theorem decC_code (s : CState) (hs : cand.ChildWF s) : decC (code s) = s := by
  obtain ⟨h1, h2, h3⟩ := nLabels_cand
  cases s with
  | fresh => decide
  | bdry => decide
  | lab q t =>
    obtain ⟨hq1, hq2, ht⟩ := hs
    rw [cand_J] at hq2
    interval_cases q
    · rw [h1] at ht
      simp only [code, decC]
      interval_cases t <;> rfl
    · rw [h2] at ht
      simp only [code, decC]
      interval_cases t <;> rfl
    · rw [h3] at ht
      simp only [code, decC]
      interval_cases t <;> rfl
  | tail q =>
    obtain ⟨hq1, hq2⟩ := hs
    rw [cand_J] at hq2
    interval_cases q <;> rfl
  | maxLab q =>
    obtain ⟨hq1, hq2⟩ := hs
    rw [cand_J] at hq2
    interval_cases q <;> rfl

theorem childWF_decC_all : ∀ c < 38, cand.ChildWF (decC c) := by
  decide +kernel

theorem code_decC_all : ∀ c < 38, code (decC c) = c := by
  decide +kernel

theorem childWF_decC (c : ℕ) (hc : c < 38) : cand.ChildWF (decC c) := childWF_decC_all c hc

theorem code_decC (c : ℕ) (hc : c < 38) : code (decC c) = c := code_decC_all c hc

/-! ### The table of the checker is the table of `cand` -/

/-- The row of code `c` is the finite row of `decC c`, weights divided by 5. -/
def RowSpec (c : ℕ) : Prop :=
  (G3K.row c).map (fun r => ((r.pn : ℚ) / r.pd, r.delta, decC r.next)) =
      (cand.finRow (decC c)).map (fun e => (e.p / 5, e.δ, e.next)) ∧
    ∀ r ∈ G3K.row c, r.next < 38 ∧ 0 < r.pd

theorem finRow_lab (q s : ℕ)
    (h : ((cand.row q s).map fun t => (⟨t.p, t.δ, cand.nxt (q + 1) t.s'⟩ : Entry)).Pairwise
      (fun a b => decide (a.δ ≤ b.δ) = true)) :
    cand.finRow (.lab q s) = (cand.row q s).map fun t => (⟨t.p, t.δ, cand.nxt (q + 1) t.s'⟩ : Entry) :=
  List.mergeSort_of_pairwise h

theorem rowSpec_0 : RowSpec 0 := by unfold RowSpec; decide +kernel
theorem rowSpec_1 : RowSpec 1 := by unfold RowSpec; decide +kernel
theorem rowSpec_2 : RowSpec 2 := by
  unfold RowSpec
  rw [show decC 2 = .lab 1 0 from rfl, finRow_lab 1 0 (by decide +kernel)]
  decide +kernel
theorem rowSpec_3 : RowSpec 3 := by
  unfold RowSpec
  rw [show decC 3 = .lab 1 1 from rfl, finRow_lab 1 1 (by decide +kernel)]
  decide +kernel
theorem rowSpec_4 : RowSpec 4 := by
  unfold RowSpec
  rw [show decC 4 = .lab 1 2 from rfl, finRow_lab 1 2 (by decide +kernel)]
  decide +kernel
theorem rowSpec_5 : RowSpec 5 := by
  unfold RowSpec
  rw [show decC 5 = .lab 1 3 from rfl, finRow_lab 1 3 (by decide +kernel)]
  decide +kernel
theorem rowSpec_6 : RowSpec 6 := by
  unfold RowSpec
  rw [show decC 6 = .lab 1 4 from rfl, finRow_lab 1 4 (by decide +kernel)]
  decide +kernel
theorem rowSpec_7 : RowSpec 7 := by
  unfold RowSpec
  rw [show decC 7 = .lab 1 5 from rfl, finRow_lab 1 5 (by decide +kernel)]
  decide +kernel
theorem rowSpec_8 : RowSpec 8 := by
  unfold RowSpec
  rw [show decC 8 = .lab 1 6 from rfl, finRow_lab 1 6 (by decide +kernel)]
  decide +kernel
theorem rowSpec_9 : RowSpec 9 := by
  unfold RowSpec
  rw [show decC 9 = .lab 1 7 from rfl, finRow_lab 1 7 (by decide +kernel)]
  decide +kernel
theorem rowSpec_10 : RowSpec 10 := by
  unfold RowSpec
  rw [show decC 10 = .lab 1 8 from rfl, finRow_lab 1 8 (by decide +kernel)]
  decide +kernel
theorem rowSpec_11 : RowSpec 11 := by
  unfold RowSpec
  rw [show decC 11 = .lab 2 0 from rfl, finRow_lab 2 0 (by decide +kernel)]
  decide +kernel
theorem rowSpec_12 : RowSpec 12 := by
  unfold RowSpec
  rw [show decC 12 = .lab 2 1 from rfl, finRow_lab 2 1 (by decide +kernel)]
  decide +kernel
theorem rowSpec_13 : RowSpec 13 := by
  unfold RowSpec
  rw [show decC 13 = .lab 2 2 from rfl, finRow_lab 2 2 (by decide +kernel)]
  decide +kernel
theorem rowSpec_14 : RowSpec 14 := by
  unfold RowSpec
  rw [show decC 14 = .lab 2 3 from rfl, finRow_lab 2 3 (by decide +kernel)]
  decide +kernel
theorem rowSpec_15 : RowSpec 15 := by
  unfold RowSpec
  rw [show decC 15 = .lab 2 4 from rfl, finRow_lab 2 4 (by decide +kernel)]
  decide +kernel
theorem rowSpec_16 : RowSpec 16 := by
  unfold RowSpec
  rw [show decC 16 = .lab 2 5 from rfl, finRow_lab 2 5 (by decide +kernel)]
  decide +kernel
theorem rowSpec_17 : RowSpec 17 := by
  unfold RowSpec
  rw [show decC 17 = .lab 2 6 from rfl, finRow_lab 2 6 (by decide +kernel)]
  decide +kernel
theorem rowSpec_18 : RowSpec 18 := by
  unfold RowSpec
  rw [show decC 18 = .lab 2 7 from rfl, finRow_lab 2 7 (by decide +kernel)]
  decide +kernel
theorem rowSpec_19 : RowSpec 19 := by
  unfold RowSpec
  rw [show decC 19 = .lab 2 8 from rfl, finRow_lab 2 8 (by decide +kernel)]
  decide +kernel
theorem rowSpec_20 : RowSpec 20 := by
  unfold RowSpec
  rw [show decC 20 = .lab 2 9 from rfl, finRow_lab 2 9 (by decide +kernel)]
  decide +kernel
theorem rowSpec_21 : RowSpec 21 := by
  unfold RowSpec
  rw [show decC 21 = .lab 3 0 from rfl, finRow_lab 3 0 (by decide +kernel)]
  decide +kernel
theorem rowSpec_22 : RowSpec 22 := by
  unfold RowSpec
  rw [show decC 22 = .lab 3 1 from rfl, finRow_lab 3 1 (by decide +kernel)]
  decide +kernel
theorem rowSpec_23 : RowSpec 23 := by
  unfold RowSpec
  rw [show decC 23 = .lab 3 2 from rfl, finRow_lab 3 2 (by decide +kernel)]
  decide +kernel
theorem rowSpec_24 : RowSpec 24 := by
  unfold RowSpec
  rw [show decC 24 = .lab 3 3 from rfl, finRow_lab 3 3 (by decide +kernel)]
  decide +kernel
theorem rowSpec_25 : RowSpec 25 := by
  unfold RowSpec
  rw [show decC 25 = .lab 3 4 from rfl, finRow_lab 3 4 (by decide +kernel)]
  decide +kernel
theorem rowSpec_26 : RowSpec 26 := by
  unfold RowSpec
  rw [show decC 26 = .lab 3 5 from rfl, finRow_lab 3 5 (by decide +kernel)]
  decide +kernel
theorem rowSpec_27 : RowSpec 27 := by
  unfold RowSpec
  rw [show decC 27 = .lab 3 6 from rfl, finRow_lab 3 6 (by decide +kernel)]
  decide +kernel
theorem rowSpec_28 : RowSpec 28 := by
  unfold RowSpec
  rw [show decC 28 = .lab 3 7 from rfl, finRow_lab 3 7 (by decide +kernel)]
  decide +kernel
theorem rowSpec_29 : RowSpec 29 := by
  unfold RowSpec
  rw [show decC 29 = .lab 3 8 from rfl, finRow_lab 3 8 (by decide +kernel)]
  decide +kernel
theorem rowSpec_30 : RowSpec 30 := by
  unfold RowSpec
  rw [show decC 30 = .lab 3 9 from rfl, finRow_lab 3 9 (by decide +kernel)]
  decide +kernel
theorem rowSpec_31 : RowSpec 31 := by
  unfold RowSpec
  rw [show decC 31 = .lab 3 10 from rfl, finRow_lab 3 10 (by decide +kernel)]
  decide +kernel
theorem rowSpec_32 : RowSpec 32 := by unfold RowSpec; decide +kernel
theorem rowSpec_33 : RowSpec 33 := by unfold RowSpec; decide +kernel
theorem rowSpec_34 : RowSpec 34 := by unfold RowSpec; decide +kernel
theorem rowSpec_35 : RowSpec 35 := by unfold RowSpec; decide +kernel
theorem rowSpec_36 : RowSpec 36 := by unfold RowSpec; decide +kernel
theorem rowSpec_37 : RowSpec 37 := by unfold RowSpec; decide +kernel

theorem row_spec (c : ℕ) (hc : c < 38) : RowSpec c := by
  interval_cases c
  · exact rowSpec_0
  · exact rowSpec_1
  · exact rowSpec_2
  · exact rowSpec_3
  · exact rowSpec_4
  · exact rowSpec_5
  · exact rowSpec_6
  · exact rowSpec_7
  · exact rowSpec_8
  · exact rowSpec_9
  · exact rowSpec_10
  · exact rowSpec_11
  · exact rowSpec_12
  · exact rowSpec_13
  · exact rowSpec_14
  · exact rowSpec_15
  · exact rowSpec_16
  · exact rowSpec_17
  · exact rowSpec_18
  · exact rowSpec_19
  · exact rowSpec_20
  · exact rowSpec_21
  · exact rowSpec_22
  · exact rowSpec_23
  · exact rowSpec_24
  · exact rowSpec_25
  · exact rowSpec_26
  · exact rowSpec_27
  · exact rowSpec_28
  · exact rowSpec_29
  · exact rowSpec_30
  · exact rowSpec_31
  · exact rowSpec_32
  · exact rowSpec_33
  · exact rowSpec_34
  · exact rowSpec_35
  · exact rowSpec_36
  · exact rowSpec_37

/-- The potential of code `c` is `wQ (decC c)`. -/
theorem w_spec : ∀ c < 38, ((G3K.wN c : ℚ) / G3K.wD c = cand.wQ (decC c) ∧ 0 < G3K.wD c) := by
  decide +kernel

/-- The lump of code `c` is the code of the lump of `decC c`. -/
theorem lump_spec : ∀ c < 38, G3K.lumpC c < 38 ∧ decC (G3K.lumpC c) = lumpC cand (decC c) := by
  decide +kernel

theorem tail_spec : cand.tailNext (decC 0) = some (decC (G3K.tailOf 0)) ∧
    cand.tailNext (decC 1) = some (decC (G3K.tailOf 1)) ∧
    (∀ c < 38, 2 ≤ c → cand.tailNext (decC c) = none) ∧ G3K.tailOf 0 < 38 ∧ G3K.tailOf 1 < 38 := by
  decide +kernel

theorem const_spec : cand.J = G3K.cJ ∧ cand.T = G3K.cT ∧ G3K.cTP = 16 ∧
    cand.eps = (G3K.epsN : ℚ) / G3K.epsD ∧ cand.rho = (G3K.rhoN : ℚ) / G3K.rhoD ∧
    cand.phi = (G3K.phiN : ℚ) / G3K.phiD ∧ cand.theta / 5 = (G3K.th5N : ℚ) / G3K.th5D ∧
    0 < G3K.epsD ∧ 0 < G3K.rhoD ∧ G3K.rhoN < G3K.rhoD ∧ 0 < G3K.phiD ∧ 0 < G3K.th5D ∧
    G3K.phiN * G3K.rhoN < G3K.phiD * G3K.rhoD := by
  decide +kernel

/-! ### Keys -/

/-- `enc q` of a sorted list of four codes. -/
def encL (q : ℕ) (l : List ℕ) (p : ℕ) : ℕ :=
  G3K.Spec.enc q (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) p

/-- The multiset of the codes of the children. -/
def codeMs (σ : Fin 4 → CState) : Multiset ℕ := Multiset.map (fun c => code (σ c)) Finset.univ.val

/-- The key of a root state: phase `i + 1`, the codes of the children sorted, `p`. -/
def keyOf (x : RState CState 4 4) : ℕ :=
  encL (x.i + 1) ((codeMs x.σ).sort (· ≤ ·)) x.p

/-- `sort3` sorts. -/
theorem sort3_eq (a b c : ℕ) :
    [(G3K.Spec.sort3 a b c).1, (G3K.Spec.sort3 a b c).2.1, (G3K.Spec.sort3 a b c).2.2] =
      ({a, b, c} : Multiset ℕ).sort (· ≤ ·) := by
  unfold G3K.Spec.sort3
  by_cases h1 : a ≤ b
  · by_cases h2 : c ≤ a
    · -- case: a ≤ b, c ≤ a → (c, a, b)
      simp [h1, h2]
      have h_sorted : List.Pairwise (· ≤ ·) [c, a, b] := by
        have hac : c ≤ a := h2
        have hab : a ≤ b := h1
        have hcb : c ≤ b := le_trans hac hab
        refine ((List.pairwise_cons (R := (· ≤ ·)) (a := c) (l := [a, b])).mpr ?_)
        refine ⟨?_, ?_⟩
        · intro x hx; simp at hx; rcases hx with (rfl | rfl); exacts [hac, hcb]
        · refine ((List.pairwise_cons (R := (· ≤ ·)) (a := a) (l := [b])).mpr ?_)
          refine ⟨?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with rfl; exact hab
          · simp
      have h_perm : ({c, a, b} : Multiset ℕ) = {a, b, c} := by
        calc
          {c, a, b} = c ::ₘ a ::ₘ (b ::ₘ 0) := rfl
          _ = a ::ₘ c ::ₘ (b ::ₘ 0) := by rw [Multiset.cons_swap]
          _ = a ::ₘ b ::ₘ (c ::ₘ 0) := by rw [Multiset.cons_swap c b 0]
          _ = {a, b, c} := rfl
      have h_sorted_rhs : List.Pairwise (· ≤ ·) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
        simpa using Multiset.sort_sorted _ (· ≤ ·)
      have h_perm' : List.Perm ([c, a, b] : List ℕ) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
        apply (Multiset.coe_eq_coe (α := ℕ)).mp
        calc
          (↑([c, a, b] : List ℕ) : Multiset ℕ) = {c, a, b} := rfl
          _ = ({a, b, c} : Multiset ℕ) := h_perm
          _ = (↑(({a, b, c} : Multiset ℕ).sort (· ≤ ·)) : Multiset ℕ) := by rw [Multiset.sort_eq]
      exact List.Perm.eq_of_pairwise' h_sorted h_sorted_rhs h_perm'
    · by_cases h3 : c ≤ b
      · -- case: a ≤ b, ¬ c ≤ a, c ≤ b → (a, c, b)
        simp [h1, h2, h3]
        have h_sorted : List.Pairwise (· ≤ ·) [a, c, b] := by
          have hac : a ≤ c := by omega
          have hcb : c ≤ b := h3
          have hab : a ≤ b := le_trans hac hcb
          refine ((List.pairwise_cons (R := (· ≤ ·)) (a := a) (l := [c, b])).mpr ?_)
          refine ⟨?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with (rfl | rfl); exacts [hac, hab]
          · refine ((List.pairwise_cons (R := (· ≤ ·)) (a := c) (l := [b])).mpr ?_)
            refine ⟨?_, ?_⟩
            · intro x hx; simp at hx; rcases hx with rfl; exact hcb
            · simp
        have h_perm : ({a, c, b} : Multiset ℕ) = {a, b, c} := by
          calc
            {a, c, b} = a ::ₘ c ::ₘ (b ::ₘ 0) := rfl
            _ = a ::ₘ b ::ₘ (c ::ₘ 0) := by rw [Multiset.cons_swap c b 0]
            _ = {a, b, c} := rfl
        have h_sorted_rhs : List.Pairwise (· ≤ ·) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          simpa using Multiset.sort_sorted _ (· ≤ ·)
        have h_perm' : List.Perm ([a, c, b] : List ℕ) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          apply (Multiset.coe_eq_coe (α := ℕ)).mp
          calc
            (↑([a, c, b] : List ℕ) : Multiset ℕ) = {a, c, b} := rfl
            _ = ({a, b, c} : Multiset ℕ) := h_perm
            _ = (↑(({a, b, c} : Multiset ℕ).sort (· ≤ ·)) : Multiset ℕ) := by rw [Multiset.sort_eq]
        exact List.Perm.eq_of_pairwise' h_sorted h_sorted_rhs h_perm'
      · -- case: a ≤ b, ¬ c ≤ a, ¬ c ≤ b → (a, b, c)
        simp [h1, h2, h3]
        have h_sorted : List.Pairwise (· ≤ ·) [a, b, c] := by
          have hab : a ≤ b := h1
          have hbc : b ≤ c := by omega
          refine ((List.pairwise_cons (R := (· ≤ ·)) (a := a) (l := [b, c])).mpr ?_)
          refine ⟨?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with (rfl | rfl); exacts [hab, hab.trans hbc]
          · refine ((List.pairwise_cons (R := (· ≤ ·)) (a := b) (l := [c])).mpr ?_)
            refine ⟨?_, ?_⟩
            · intro x hx; simp at hx; rcases hx with rfl; exact hbc
            · simp
        have h_perm : ({a, b, c} : Multiset ℕ) = {a, b, c} := rfl
        have h_sorted_rhs : List.Pairwise (· ≤ ·) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          simpa using Multiset.sort_sorted _ (· ≤ ·)
        have h_perm' : List.Perm ([a, b, c] : List ℕ) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          apply (Multiset.coe_eq_coe (α := ℕ)).mp
          calc
            (↑([a, b, c] : List ℕ) : Multiset ℕ) = {a, b, c} := rfl
            _ = ({a, b, c} : Multiset ℕ) := rfl
            _ = (↑(({a, b, c} : Multiset ℕ).sort (· ≤ ·)) : Multiset ℕ) := by rw [Multiset.sort_eq]
        exact List.Perm.eq_of_pairwise' h_sorted h_sorted_rhs h_perm'
  · by_cases h4 : c ≤ b
    · -- case: ¬ a ≤ b, c ≤ b → (c, b, a)
      simp [h1, h4]
      have h_sorted : List.Pairwise (· ≤ ·) [c, b, a] := by
        have hcb : c ≤ b := h4
        have hba : b ≤ a := by omega
        have hca : c ≤ a := le_trans hcb hba
        refine ((List.pairwise_cons (R := (· ≤ ·)) (a := c) (l := [b, a])).mpr ?_)
        refine ⟨?_, ?_⟩
        · intro x hx; simp at hx; rcases hx with (rfl | rfl); exacts [hcb, hcb.trans hba]
        · refine ((List.pairwise_cons (R := (· ≤ ·)) (a := b) (l := [a])).mpr ?_)
          refine ⟨?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with rfl; exact hba
          · simp
      have h_perm : ({c, b, a} : Multiset ℕ) = {a, b, c} := by
        calc
          {c, b, a} = c ::ₘ b ::ₘ (a ::ₘ 0) := rfl
          _ = b ::ₘ c ::ₘ (a ::ₘ 0) := by rw [Multiset.cons_swap]
          _ = b ::ₘ a ::ₘ (c ::ₘ 0) := by rw [Multiset.cons_swap c a 0]
          _ = a ::ₘ b ::ₘ (c ::ₘ 0) := by rw [Multiset.cons_swap b a (c ::ₘ 0)]
          _ = {a, b, c} := rfl
      have h_sorted_rhs : List.Pairwise (· ≤ ·) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
        simpa using Multiset.sort_sorted _ (· ≤ ·)
      have h_perm' : List.Perm ([c, b, a] : List ℕ) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
        apply (Multiset.coe_eq_coe (α := ℕ)).mp
        calc
          (↑([c, b, a] : List ℕ) : Multiset ℕ) = {c, b, a} := rfl
          _ = ({a, b, c} : Multiset ℕ) := h_perm
          _ = (↑(({a, b, c} : Multiset ℕ).sort (· ≤ ·)) : Multiset ℕ) := by rw [Multiset.sort_eq]
      exact List.Perm.eq_of_pairwise' h_sorted h_sorted_rhs h_perm'
    · by_cases h5 : c ≤ a
      · -- case: ¬ a ≤ b, ¬ c ≤ b, c ≤ a → (b, c, a)
        simp [h1, h4, h5]
        have h_sorted : List.Pairwise (· ≤ ·) [b, c, a] := by
          have hbc : b ≤ c := by omega
          have hca : c ≤ a := h5
          have hba : b ≤ a := le_trans hbc hca
          refine ((List.pairwise_cons (R := (· ≤ ·)) (a := b) (l := [c, a])).mpr ?_)
          refine ⟨?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with (rfl | rfl); exacts [hbc, hba]
          · refine ((List.pairwise_cons (R := (· ≤ ·)) (a := c) (l := [a])).mpr ?_)
            refine ⟨?_, ?_⟩
            · intro x hx; simp at hx; rcases hx with rfl; exact hca
            · simp
        have h_perm : ({b, c, a} : Multiset ℕ) = {a, b, c} := by
          calc
            {b, c, a} = b ::ₘ c ::ₘ (a ::ₘ 0) := rfl
            _ = c ::ₘ b ::ₘ (a ::ₘ 0) := by rw [Multiset.cons_swap]
            _ = c ::ₘ a ::ₘ (b ::ₘ 0) := by rw [Multiset.cons_swap b a 0]
            _ = a ::ₘ c ::ₘ (b ::ₘ 0) := by rw [Multiset.cons_swap c a (b ::ₘ 0)]
            _ = a ::ₘ b ::ₘ (c ::ₘ 0) := by rw [Multiset.cons_swap c b 0]
            _ = {a, b, c} := rfl
        have h_sorted_rhs : List.Pairwise (· ≤ ·) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          simpa using Multiset.sort_sorted _ (· ≤ ·)
        have h_perm' : List.Perm ([b, c, a] : List ℕ) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          apply (Multiset.coe_eq_coe (α := ℕ)).mp
          calc
            (↑([b, c, a] : List ℕ) : Multiset ℕ) = {b, c, a} := rfl
            _ = ({a, b, c} : Multiset ℕ) := h_perm
            _ = (↑(({a, b, c} : Multiset ℕ).sort (· ≤ ·)) : Multiset ℕ) := by rw [Multiset.sort_eq]
        exact List.Perm.eq_of_pairwise' h_sorted h_sorted_rhs h_perm'
      · -- case: ¬ a ≤ b, ¬ c ≤ b, ¬ c ≤ a → (b, a, c)
        simp [h1, h4, h5]
        have h_sorted : List.Pairwise (· ≤ ·) [b, a, c] := by
          have hba : b ≤ a := by omega
          have hac : a ≤ c := by omega
          have hbc : b ≤ c := le_trans hba hac
          refine ((List.pairwise_cons (R := (· ≤ ·)) (a := b) (l := [a, c])).mpr ?_)
          refine ⟨?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with (rfl | rfl); exacts [hba, hbc]
          · refine ((List.pairwise_cons (R := (· ≤ ·)) (a := a) (l := [c])).mpr ?_)
            refine ⟨?_, ?_⟩
            · intro x hx; simp at hx; rcases hx with rfl; exact hac
            · simp
        have h_perm : ({b, a, c} : Multiset ℕ) = {a, b, c} := by
          calc
            {b, a, c} = b ::ₘ a ::ₘ (c ::ₘ 0) := rfl
            _ = a ::ₘ b ::ₘ (c ::ₘ 0) := by rw [Multiset.cons_swap]
            _ = {a, b, c} := rfl
        have h_sorted_rhs : List.Pairwise (· ≤ ·) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          simpa using Multiset.sort_sorted _ (· ≤ ·)
        have h_perm' : List.Perm ([b, a, c] : List ℕ) (({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by
          apply (Multiset.coe_eq_coe (α := ℕ)).mp
          calc
            (↑([b, a, c] : List ℕ) : Multiset ℕ) = {b, a, c} := rfl
            _ = ({a, b, c} : Multiset ℕ) := h_perm
            _ = (↑(({a, b, c} : Multiset ℕ).sort (· ≤ ·)) : Multiset ℕ) := by rw [Multiset.sort_eq]
        exact List.Perm.eq_of_pairwise' h_sorted h_sorted_rhs h_perm'

-- Helper lemma: sorted list for w ≤ x ≤ y ≤ z
theorem sort4_le_wx (x y z w : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) (hwx : w ≤ x) :
    ({x, y, z, w} : Multiset ℕ).sort (· ≤ ·) = [w, x, y, z] := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Multiset.pairwise_sort _ _
  · have hwz : w ≤ z := le_trans hwx (le_trans hxy hyz)
    have hwy : w ≤ y := le_trans hwx hxy
    have hxz : x ≤ z := le_trans hxy hyz
    -- Prove Pairwise (· ≤ ·) [w, x, y, z]
    rw [List.pairwise_cons]
    constructor
    · intro a ha
      simp at ha
      rcases ha with (h | h | h)
      · rw [h]; exact hwx
      · rw [h]; exact hwy
      · rw [h]; exact hwz
    · rw [List.pairwise_cons]
      constructor
      · intro a ha
        simp at ha
        rcases ha with (h | h)
        · rw [h]; exact hxy
        · rw [h]; exact hxz
      · rw [List.pairwise_cons]
        constructor
        · intro a ha
          simp at ha
          cases ha
          exact hyz
        · rw [List.pairwise_cons]
          constructor
          · intro a ha
            simp at ha
          · exact List.Pairwise.nil
  · -- (sort ...).Perm [w, x, y, z]
    have hsort_eq := Multiset.sort_eq (s := ({x, y, z, w} : Multiset ℕ)) (r := (· ≤ ·))
    have hperm1 : (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·)).Perm [x, y, z, w] :=
      (Multiset.coe_eq_coe (l₁ := (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·))) (l₂ := [x, y, z, w])).mp hsort_eq
    have hperm2 : ([x, y, z, w] : List ℕ).Perm [w, x, y, z] := by
      rw [List.perm_iff_count]
      intro a
      simp [List.count_cons, List.count_nil]
      omega
    exact List.Perm.trans hperm1 hperm2

-- Helper lemma: sorted list for x ≤ w ≤ y ≤ z
theorem sort4_le_xw (x y z w : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) (hwx : ¬ w ≤ x) (hwy : w ≤ y) :
    ({x, y, z, w} : Multiset ℕ).sort (· ≤ ·) = [x, w, y, z] := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Multiset.pairwise_sort _ _
  · have hwz : w ≤ z := le_trans hwy hyz
    have hxw : x ≤ w := Nat.le_of_lt (Nat.lt_of_not_ge hwx)
    have hxz : x ≤ z := le_trans hxw hwz
    -- Prove Pairwise (· ≤ ·) [x, w, y, z]
    rw [List.pairwise_cons]
    constructor
    · intro a ha
      simp at ha
      rcases ha with (h | h | h)
      · rw [h]; exact hxw
      · rw [h]; exact hxy
      · rw [h]; exact hxz
    · rw [List.pairwise_cons]
      constructor
      · intro a ha
        simp at ha
        rcases ha with (h | h)
        · rw [h]; exact hwy
        · rw [h]; exact hwz
      · rw [List.pairwise_cons]
        constructor
        · intro a ha
          simp at ha
          cases ha
          exact hyz
        · rw [List.pairwise_cons]
          constructor
          · intro a ha
            simp at ha
          · exact List.Pairwise.nil
  · -- (sort ...).Perm [x, w, y, z]
    have hsort_eq := Multiset.sort_eq (s := ({x, y, z, w} : Multiset ℕ)) (r := (· ≤ ·))
    have hperm1 : (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·)).Perm [x, y, z, w] :=
      (Multiset.coe_eq_coe (l₁ := (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·))) (l₂ := [x, y, z, w])).mp hsort_eq
    have hperm2 : ([x, y, z, w] : List ℕ).Perm [x, w, y, z] := by
      rw [List.perm_iff_count]
      intro a
      simp [List.count_cons, List.count_nil]
      omega
    exact List.Perm.trans hperm1 hperm2

-- Helper lemma: sorted list for x ≤ y ≤ w ≤ z
theorem sort4_le_xyw (x y z w : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) (hwx : ¬ w ≤ x) (hwy : ¬ w ≤ y) (hwz : w ≤ z) :
    ({x, y, z, w} : Multiset ℕ).sort (· ≤ ·) = [x, y, w, z] := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Multiset.pairwise_sort _ _
  · have hxw : x ≤ w := Nat.le_of_lt (Nat.lt_of_not_ge hwx)
    have hyw : y ≤ w := Nat.le_of_lt (Nat.lt_of_not_ge hwy)
    have hxz : x ≤ z := le_trans hxy hyz
    -- Prove Pairwise (· ≤ ·) [x, y, w, z]
    rw [List.pairwise_cons]
    constructor
    · intro a ha
      simp at ha
      rcases ha with (h | h | h)
      · rw [h]; exact hxy
      · rw [h]; exact hxw
      · rw [h]; exact hxz
    · rw [List.pairwise_cons]
      constructor
      · intro a ha
        simp at ha
        rcases ha with (h | h)
        · rw [h]; exact hyw
        · rw [h]; exact hyz
      · rw [List.pairwise_cons]
        constructor
        · intro a ha
          simp at ha
          cases ha
          exact hwz
        · rw [List.pairwise_cons]
          constructor
          · intro a ha
            simp at ha
          · exact List.Pairwise.nil
  · -- (sort ...).Perm [x, y, w, z]
    have hsort_eq := Multiset.sort_eq (s := ({x, y, z, w} : Multiset ℕ)) (r := (· ≤ ·))
    have hperm1 : (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·)).Perm [x, y, z, w] :=
      (Multiset.coe_eq_coe (l₁ := (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·))) (l₂ := [x, y, z, w])).mp hsort_eq
    have hperm2 : ([x, y, z, w] : List ℕ).Perm [x, y, w, z] := by
      rw [List.perm_iff_count]
      intro a
      simp [List.count_cons, List.count_nil]
      omega
    exact List.Perm.trans hperm1 hperm2

-- Helper lemma: sorted list for x ≤ y ≤ z ≤ w
theorem sort4_le_xyzw (x y z w : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) (hwx : ¬ w ≤ x) (hwy : ¬ w ≤ y) (hwz : ¬ w ≤ z) :
    ({x, y, z, w} : Multiset ℕ).sort (· ≤ ·) = [x, y, z, w] := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Multiset.pairwise_sort _ _
  · have hxw : x ≤ w := Nat.le_of_lt (Nat.lt_of_not_ge hwx)
    have hyw : y ≤ w := Nat.le_of_lt (Nat.lt_of_not_ge hwy)
    have hzw : z ≤ w := Nat.le_of_lt (Nat.lt_of_not_ge hwz)
    have hxz : x ≤ z := le_trans hxy hyz
    -- Prove Pairwise (· ≤ ·) [x, y, z, w]
    rw [List.pairwise_cons]
    constructor
    · intro a ha
      simp at ha
      rcases ha with (h | h | h)
      · rw [h]; exact hxy
      · rw [h]; exact hxz
      · rw [h]; exact hxw
    · rw [List.pairwise_cons]
      constructor
      · intro a ha
        simp at ha
        rcases ha with (h | h)
        · rw [h]; exact hyz
        · rw [h]; exact hyw
      · rw [List.pairwise_cons]
        constructor
        · intro a ha
          simp at ha
          cases ha
          exact hzw
        · rw [List.pairwise_cons]
          constructor
          · intro a ha
            simp at ha
          · exact List.Pairwise.nil
  · -- (sort ...).Perm [x, y, z, w]
    have hsort_eq := Multiset.sort_eq (s := ({x, y, z, w} : Multiset ℕ)) (r := (· ≤ ·))
    have hperm1 : (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·)).Perm [x, y, z, w] :=
      (Multiset.coe_eq_coe (l₁ := (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·))) (l₂ := [x, y, z, w])).mp hsort_eq
    have hperm2 : ([x, y, z, w] : List ℕ).Perm [x, y, z, w] := by
      rfl
    exact List.Perm.trans hperm1 hperm2

/-- Insertion into three sorted codes gives the key of the four. -/
theorem encIns_eq (q x y z w p : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) :
    G3K.Spec.encIns q x y z w p = encL q (({x, y, z, w} : Multiset ℕ).sort (· ≤ ·)) p := by
  unfold G3K.Spec.encIns FrogModel.Engine.G3.encL G3K.Spec.enc
  by_cases hwx : w ≤ x
  · -- Case w ≤ x
    rw [ite_eq_left hwx]
    rw [sort4_le_wx x y z w hxy hyz hwx]
    simp
  · -- Case ¬ w ≤ x
    rw [ite_eq_right hwx]
    by_cases hwy : w ≤ y
    · -- Case ¬ w ≤ x ∧ w ≤ y
      rw [ite_eq_left hwy]
      rw [sort4_le_xw x y z w hxy hyz hwx hwy]
      simp
    · -- Case ¬ w ≤ x ∧ ¬ w ≤ y
      rw [ite_eq_right hwy]
      by_cases hwz : w ≤ z
      · -- Case ¬ w ≤ x ∧ ¬ w ≤ y ∧ w ≤ z
        rw [ite_eq_left hwz]
        rw [sort4_le_xyw x y z w hxy hyz hwx hwy hwz]
        simp
      · -- Case ¬ w ≤ x ∧ ¬ w ≤ y ∧ ¬ w ≤ z
        rw [ite_eq_right hwz]
        rw [sort4_le_xyzw x y z w hxy hyz hwx hwy hwz]
        simp

/-- The key reads back. -/
theorem dec_enc (q a b c d p : ℕ) (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128)
    (hp : p < 128) :
    G3K.Spec.decQ (G3K.Spec.enc q a b c d p) = q ∧ G3K.Spec.decC1 (G3K.Spec.enc q a b c d p) = a ∧
      G3K.Spec.decC2 (G3K.Spec.enc q a b c d p) = b ∧ G3K.Spec.decC3 (G3K.Spec.enc q a b c d p) = c ∧
      G3K.Spec.decC4 (G3K.Spec.enc q a b c d p) = d ∧ G3K.Spec.decP (G3K.Spec.enc q a b c d p) = p := by
  unfold G3K.Spec.decQ G3K.Spec.decC1 G3K.Spec.decC2 G3K.Spec.decC3 G3K.Spec.decC4 G3K.Spec.decP G3K.Spec.enc
  omega

/-- Equal keys with codes and `p` below 128: equal phases, sorted codes and `p`. -/
theorem enc_inj (q a b c d p q' a' b' c' d' p' : ℕ) (ha : a < 128) (hb : b < 128) (hc : c < 128)
    (hd : d < 128) (hp : p < 128) (ha' : a' < 128) (hb' : b' < 128) (hc' : c' < 128)
    (hd' : d' < 128) (hp' : p' < 128)
    (h : G3K.Spec.enc q a b c d p = G3K.Spec.enc q' a' b' c' d' p') :
    q = q' ∧ a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ p = p' := by
  unfold G3K.Spec.enc at h
  omega

end FrogModel.Engine.G3
