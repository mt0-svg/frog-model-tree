module

public import FrogModel.LemmaX.ChildBasic
public import FrogModel.Engine.Redirect

@[expose] public section

/-!
# The max label dominates the labels of its level (Lemma 6.4 of the paper)

For a table `D` with (I0) and (I1), the child chain `D.childStep` driven by one uniform per entry
is simulated (`IsSim`) by the relation `simRel D`: equal states, or a well-formed label `lab q t`
below the max label `maxLab q` of its level. With the same uniform, the max label delivers at
least as many returns (the max row has `P(δ ≥ k) = max_t P_t(δ ≥ k)`, both rows are sorted by
`δ` and read by their inverse distribution functions) and moves to the max label of the next
level, or to `bdry` at level `J` as the label does.

The lump of a root state (`lumpState`) replaces every well-formed label by the max label of its
level; it dominates its argument (`dom_lumpState`).
-/

namespace FrogModel.Engine

open FrogModel.Cert

variable {d J : ℕ}

/-- Equal states, or a well-formed label below the max label of its level. -/
def simRel (D : Data) (s s' : CState) : Prop :=
  s = s' ∨ ∃ q t, D.ChildWF (.lab q t) ∧ s = .lab q t ∧ s' = .maxLab q

/-- The lump of a child state: a well-formed label goes to the max label of its level. -/
def lumpC (D : Data) : CState → CState
  | .lab q t => if D.ChildWF (.lab q t) then .maxLab q else .lab q t
  | s => s

/-- The lump of a root state: every child lumped, the counts and outputs kept. -/
def lumpState (D : Data) (x : RState CState d J) : RState CState d J :=
  ⟨x.i, x.e, x.p, fun c => lumpC D (x.σ c), x.out⟩

theorem simRel_refl (D : Data) (s : CState) : simRel D s s := Or.inl rfl

theorem simRel_lumpC (D : Data) (s : CState) : simRel D s (lumpC D s) := by
  cases s with
  | lab q t =>
    by_cases h : D.ChildWF (.lab q t)
    · rw [show lumpC D (.lab q t) = .maxLab q by simp [lumpC, h]]
      exact Or.inr ⟨q, t, h, rfl, rfl⟩
    · rw [show lumpC D (.lab q t) = .lab q t by simp [lumpC, h]]
      exact Or.inl rfl
  | _ => exact Or.inl rfl

theorem dom_lumpState (D : Data) (x : RState CState d J) : Dom (simRel D) x (lumpState D x) :=
  ⟨rfl, rfl, rfl, rfl, fun c => simRel_lumpC D (x.σ c)⟩

/-! ### The rows of a label and of the max label of its level -/

/-- `childStep` reads the least index whose cumulative weight exceeds the uniform. -/
theorem childStep_eq_of_least (D : Data) (s : CState) (u : ℝ) (n : ℕ)
    (hn : (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum s (n + 1) : ℝ))
    (hmin : ∀ j < n, ¬ (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum s (j + 1) : ℝ)) :
    D.childStep s u = ((D.rowSeq s n).δ, (D.rowSeq s n).next) := by
  have h : ∃ m, (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum s (m + 1) : ℝ) := ⟨n, hn⟩
  unfold Data.childStep
  rw [dite_eq_left_of_eq_true (eq_true h), (Nat.find_eq_iff h).mpr ⟨hn, hmin⟩]

theorem rowSeq_of_lt (D : Data) (s : CState) (n : ℕ) (hn : n < (D.finRow s).length) :
    D.rowSeq s n = (D.finRow s)[n] := by
  simp [Data.rowSeq, hn]

/-- Within the finite row, the cumulative weight is the sum of a prefix. -/
theorem rowCum_eq_take (D : Data) (s : CState) (n : ℕ) (hn : n ≤ (D.finRow s).length) :
    D.rowCum s n = (((D.finRow s).take n).map Entry.p).sum := by
  induction n with
  | zero => simp [Data.rowCum]
  | succ n ih =>
    have hlt : n < (D.finRow s).length := hn
    rw [Data.rowCum, Finset.sum_range_succ, ← Data.rowCum, ih hlt.le, rowSeq_of_lt D s n hlt]
    rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hlt)]
    simp

theorem maxRow_length (D : Data) (q : ℕ) : (D.maxRow q).length = D.maxDelta + 1 := by
  simp [Data.maxRow]

/-- Entry `n` of the max row delivers `n`. -/
theorem rowSeq_maxLab (D : Data) (q n : ℕ) (hn : n ≤ D.maxDelta) :
    D.rowSeq (.maxLab q) n = ⟨D.tailMax q n - D.tailMax q (n + 1), n, D.nxtMax (q + 1)⟩ := by
  have hlt : n < (D.finRow (.maxLab q)).length := by
    show n < (D.maxRow q).length
    rw [maxRow_length]; omega
  rw [rowSeq_of_lt D _ n hlt]
  simp [Data.finRow, Data.maxRow]

/-- The max row telescopes: the weight of `δ < n` is `1 - max_t P_t(δ ≥ n)`. -/
theorem rowCum_maxLab (D : Data) (h1 : D.I1) (q n : ℕ) (hq : q < D.J)
    (hn : n ≤ D.maxDelta + 1) : D.rowCum (.maxLab q) n = 1 - D.tailMax q n := by
  unfold Data.rowCum
  rw [Finset.sum_congr rfl (g := fun k => D.tailMax q k - D.tailMax q (k + 1)) fun k hk => by
    rw [rowSeq_maxLab D q k (by simp at hk; omega)], Finset.sum_range_sub', D.tailMax_zero h1 q hq]

/-- In a list sorted by `f`, the entries with `f ≤ k` form a prefix. -/
theorem takeWhile_eq_filter_of_pairwise {α : Type*} (f : α → ℕ) (k : ℕ) (l : List α)
    (hl : l.Pairwise fun a b => f a ≤ f b) :
    l.takeWhile (fun a => decide (f a ≤ k)) = l.filter (fun a => decide (f a ≤ k)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    by_cases ha : f a ≤ k
    · simp [ha, ih hl.2]
    · have : l.filter (fun a => decide (f a ≤ k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := hl.1 b hb
        simp; omega
      simp [ha, this]

/-- The row of a label is sorted by `δ`. -/
theorem labRow_pairwise (D : Data) (q t : ℕ) : (D.labRow q t).Pairwise fun a b => a.δ ≤ b.δ := by
  have := List.pairwise_mergeSort (le := fun a b : Entry => decide (a.δ ≤ b.δ))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega)
    ((D.row q t).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry))
  simpa [Data.labRow] using this

/-- The entries of the row of a label with `δ > k` weigh `P_t(δ ≥ k + 1)`. -/
theorem labRow_filter_gt_sum (D : Data) (q t k : ℕ) :
    (((D.labRow q t).filter fun e => !decide (e.δ ≤ k)).map Entry.p).sum =
      D.tailMass q t (k + 1) := by
  unfold Data.labRow Data.tailMass
  rw [(((List.mergeSort_perm _ _).filter _).map Entry.p).sum_eq, List.filter_map, List.map_map]
  congr 2
  · apply List.filter_congr
    intro x _
    by_cases h : x.δ ≤ k
    · simp [h]
    · simp [h]
      omega

/-- The prefix of the row of a label with `δ ≤ k` weighs `1 - P_t(δ ≥ k + 1)`. -/
theorem labRow_takeWhile_sum (D : Data) (h1 : D.I1) (q t k : ℕ) (hq : q < D.J)
    (ht : t < D.nLabels q) :
    (((D.labRow q t).takeWhile fun e => decide (e.δ ≤ k)).map Entry.p).sum =
      1 - D.tailMass q t (k + 1) := by
  rw [takeWhile_eq_filter_of_pairwise (fun e : Entry => e.δ) k _ (labRow_pairwise D q t),
    ← labRow_filter_gt_sum D q t k, ← D.labRow_sum h1 q t hq ht,
    ← (((List.filter_append_perm (fun e : Entry => decide (e.δ ≤ k)) (D.labRow q t))).map
      Entry.p).sum_eq]
  simp

theorem tailMass_le_tailMax (D : Data) (q t k : ℕ) (ht : t < D.nLabels q) :
    D.tailMass q t k ≤ D.tailMax q k := by
  have key : ∀ (l : List ℚ) (a : ℚ), a ∈ l → a ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_max_left _ _
      · exact le_max_of_le_right (ih a ha)
  exact key _ _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)

/-- Every entry of the row of a label of level `q` moves to a label of level `q + 1`. -/
theorem labRow_next (D : Data) (q t : ℕ) (e : Entry) (he : e ∈ D.labRow q t) :
    ∃ s, e.next = D.nxt (q + 1) s := by
  unfold Data.labRow at he
  obtain ⟨tr, -, rfl⟩ := List.mem_map.mp ((List.mergeSort_perm _ _).mem_iff.mp he)
  exact ⟨tr.s', rfl⟩

/-- **One move under the same uniform.** A well-formed label delivers at most what the max label
of its level delivers (both rows are read by their inverse distribution functions, and the max
row puts at most as much weight on `δ ≤ k` as the label row, for every `k`), and the next states
are related by `simRel`. -/
theorem childStep_lab_maxLab (D : Data) (h0 : D.I0) (h1 : D.I1) (q t : ℕ)
    (hwf : D.ChildWF (.lab q t)) (u : ℝ) :
    (D.childStep (.lab q t) u).1 ≤ (D.childStep (.maxLab q) u).1 ∧
      simRel D (D.childStep (.lab q t) u).2 (D.childStep (.maxLab q) u).2 := by
  have hwf' := hwf
  obtain ⟨hq1, hqJ, ht⟩ := hwf
  set x : ℝ := if 0 ≤ u ∧ u < 1 then u else 0 with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; split_ifs with h
    · exact h.1
    · exact le_rfl
  have hx1 : x < 1 := by
    rw [hx]; split_ifs with h
    · exact h.2
    · exact zero_lt_one
  have hBtop : x < (D.rowCum (.maxLab q) (D.maxDelta + 1) : ℝ) := by
    rw [rowCum_maxLab D h1 q _ hqJ le_rfl, D.tailMax_big]
    simpa using hx1
  classical
  have hBex : ∃ n, x < (D.rowCum (.maxLab q) (n + 1) : ℝ) := ⟨D.maxDelta, hBtop⟩
  obtain ⟨nB, hnB, hminB⟩ : ∃ n, x < (D.rowCum (.maxLab q) (n + 1) : ℝ) ∧
      ∀ j < n, ¬ x < (D.rowCum (.maxLab q) (j + 1) : ℝ) :=
    ⟨Nat.find hBex, Nat.find_spec hBex, fun j hj => Nat.find_min hBex hj⟩
  have hnBle : nB ≤ D.maxDelta := by
    by_contra h
    exact hminB _ (by omega) hBtop
  rw [childStep_eq_of_least D (.maxLab q) u nB hnB hminB, rowSeq_maxLab D q nB hnBle]
  -- the label row
  have hfin : D.finRow (.lab q t) = D.labRow q t := rfl
  have hpre := List.takeWhile_prefix (l := D.labRow q t) fun e => decide (e.δ ≤ nB)
  set m := ((D.labRow q t).takeWhile fun e => decide (e.δ ≤ nB)).length with hm
  have hm_le : m ≤ (D.finRow (.lab q t)).length := hpre.length_le
  have hcum_m : D.rowCum (.lab q t) m = 1 - D.tailMass q t (nB + 1) := by
    rw [rowCum_eq_take D _ m hm_le, hfin, hm, ← List.prefix_iff_eq_take.mp hpre,
      labRow_takeWhile_sum D h1 q t nB hqJ ht]
  have hxm : x < (D.rowCum (.lab q t) m : ℝ) := by
    have hB' := hnB
    rw [rowCum_maxLab D h1 q _ hqJ (by omega)] at hB'
    have := tailMass_le_tailMax D q t (nB + 1) ht
    rw [hcum_m]
    calc x < ((1 - D.tailMax q (nB + 1) : ℚ) : ℝ) := hB'
      _ ≤ ((1 - D.tailMass q t (nB + 1) : ℚ) : ℝ) := by exact_mod_cast (by linarith)
  have hm0 : m ≠ 0 := by
    intro h0m
    rw [h0m] at hxm
    simp [Data.rowCum] at hxm
    linarith
  have hAex : ∃ n, x < (D.rowCum (.lab q t) (n + 1) : ℝ) :=
    ⟨m - 1, by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]⟩
  obtain ⟨nA, hnA, hminA⟩ : ∃ n, x < (D.rowCum (.lab q t) (n + 1) : ℝ) ∧
      ∀ j < n, ¬ x < (D.rowCum (.lab q t) (j + 1) : ℝ) :=
    ⟨Nat.find hAex, Nat.find_spec hAex, fun j hj => Nat.find_min hAex hj⟩
  have hnAm : nA < m := by
    by_contra h
    exact hminA (m - 1) (by omega) (by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)])
  have hnAL : nA < (D.finRow (.lab q t)).length := lt_of_lt_of_le hnAm hm_le
  have hnAL' : nA < (D.labRow q t).length := hnAL
  have hrow : D.rowSeq (.lab q t) nA = (D.labRow q t)[nA] := rowSeq_of_lt D (.lab q t) nA hnAL
  rw [childStep_eq_of_least D (.lab q t) u nA hnA hminA]
  refine ⟨?_, ?_⟩
  · show (D.rowSeq (.lab q t) nA).δ ≤ nB
    rw [hrow, ← hpre.getElem hnAm]
    have := List.mem_takeWhile_imp (p := fun e : Entry => decide (e.δ ≤ nB)) (List.getElem_mem hnAm)
    simpa using this
  · show simRel D (D.rowSeq (.lab q t) nA).next (D.nxtMax (q + 1))
    have hwfn := D.rowSeq_next_wf h0 h1 (.lab q t) hwf' nA
    obtain ⟨s'', hs''⟩ := labRow_next D q t _ (hrow ▸ List.getElem_mem hnAL')
    rw [hs''] at hwfn ⊢
    by_cases hJ : q + 1 = D.J
    · left
      simp [Data.nxt, Data.nxtMax, hJ]
    · right
      refine ⟨q + 1, s'', ?_, ?_, ?_⟩
      · simpa [Data.nxt, hJ] using hwfn
      · simp [Data.nxt, hJ]
      · simp [Data.nxtMax, hJ]

/-- **The max label simulates the labels of its level.** -/
theorem isSim_childStep (D : Data) (h0 : D.I0) (h1 : D.I1) : IsSim D.childStep (simRel D) := by
  rintro s s' (rfl | ⟨q, t, hwf, rfl, rfl⟩) u
  · exact ⟨le_rfl, simRel_refl D _⟩
  · exact childStep_lab_maxLab D h0 h1 q t hwf u

end FrogModel.Engine
