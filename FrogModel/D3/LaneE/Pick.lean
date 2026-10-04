module

public import FrogModel.D3.LaneE.Interval

@[expose] public section

/-!
# The entry of a height in a linked table

A table is a first entry `d` and the list `es` of the next ones. It is linked when every entry ends
where the next begins, `J` does not decrease along the table, and the last entry ends at `10^30`.
`pickE es d m` is the last entry whose left end is at most `m` (`d` when there is none).
-/

open FrogModel.D3.Iface

namespace FrogModel.D3.LaneE

/-- The last entry of `d :: es` whose left end is at most `m`, `d` by default. -/
def pickE : List Entry → Entry → ℕ → Entry
  | [], d, _ => d
  | e :: es, d, m => if e.ml ≤ m then pickE es e m else d

/-- `d :: es` is linked: each entry ends where the next begins, `J` is nondecreasing, the last
entry ends at `10^30`. -/
def linked : Entry → List Entry → Bool
  | d, [] => d.mh == 10 ^ 30
  | d, e :: es => d.mh == e.ml && decide (d.J ≤ e.J) && linked e es

theorem pickE_spec (es : List Entry) (d : Entry) (m : ℕ) (hl : linked d es = true)
    (hd : d.ml ≤ m) (hm : m ≤ 10 ^ 30) :
    (pickE es d m = d ∨ pickE es d m ∈ es) ∧ (pickE es d m).ml ≤ m ∧ m ≤ (pickE es d m).mh := by
  induction es generalizing d with
  | nil =>
    simp only [linked, beq_iff_eq] at hl
    simp only [pickE, true_or, true_and]
    exact ⟨hd, hl ▸ hm⟩
  | cons e es ih =>
    simp only [linked, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl
    obtain ⟨⟨hde, -⟩, hl⟩ := hl
    by_cases he : e.ml ≤ m
    · simp only [pickE, he, ite_true]
      obtain ⟨h1, h2⟩ := ih e hl he
      refine ⟨Or.inr ?_, h2⟩
      rcases h1 with h1 | h1
      · rw [h1]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    · simp only [pickE, he, ite_false, true_or, true_and]
      exact ⟨hd, by omega⟩

theorem pickE_J_ge (es : List Entry) (d : Entry) (m : ℕ) (hl : linked d es = true) :
    d.J ≤ (pickE es d m).J := by
  induction es generalizing d with
  | nil => simp [pickE]
  | cons e es ih =>
    simp only [linked, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl
    obtain ⟨⟨-, hJ⟩, hl⟩ := hl
    by_cases he : e.ml ≤ m
    · simp only [pickE, he, ite_true]; exact hJ.trans (ih e hl)
    · simp [pickE, he]

theorem pickE_J_mono (es : List Entry) (d : Entry) (hl : linked d es = true) :
    Monotone fun m => (pickE es d m).J := by
  intro m m' hmm'
  induction es generalizing d with
  | nil => simp [pickE]
  | cons e es ih =>
    have hl' := hl
    simp only [linked, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl
    obtain ⟨⟨-, hJ⟩, hl⟩ := hl
    simp only [pickE]
    by_cases he : e.ml ≤ m
    · have he' : e.ml ≤ m' := he.trans hmm'
      simp only [he, he', ite_true]; exact ih e hl
    · by_cases he' : e.ml ≤ m'
      · simp only [he, he', ite_true, ite_false]; exact hJ.trans (pickE_J_ge es e m' hl)
      · simp [he, he']

end FrogModel.D3.LaneE
