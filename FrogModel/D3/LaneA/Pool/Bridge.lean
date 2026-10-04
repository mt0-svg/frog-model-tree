module

public import FrogModel.D3.Interfaces.Model
public import FrogModel.LemmaX.Defs

@[expose] public section

/-!
# The closure map of `LemmaX` and the closure of the interface (d = 3)

`FrogModel.LemmaX.psiG` (used by Recursion/Process.lean) feeds a child curve as `F(0) = 0`,
`F(e) = G(e + 1)` and works on `ℕ∞`; the interface closure (`closT`, `closN`, `closX`) feeds the
child curves directly and counts on `ℕ`. For non-decreasing child curves with `G 0 = 0`, the
shifted curves `shiftC G c e = G c (e - 1)` make the two agree (`psiN_shiftC`, `psiG_shiftC`).
-/

open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel.D3.Iface

/-- A curve of the closure as a curve of `Psi`: `shiftC G c (e + 1) = G c e`. -/
def shiftC (G : Fin 3 → ℕ → ℕ∞) : Fin 3 → ℕ → ℕ∞ := fun c e => G c (e - 1)

/-- The two direction counts agree at finite times. -/
theorem lx_dirCount_coe (D : ℕ → Fin 4) (a : Fin 4) (n : ℕ) :
    FrogModel.LemmaX.dirCount D a (n : ℕ∞) = (dirCount D a n : ℕ∞) := by
  unfold FrogModel.LemmaX.dirCount dirCount
  have h : {k : ℕ | (k : ℕ∞) < n ∧ D k = a} =
      ↑((Finset.range n).filter fun i => D i = a) := by
    ext k
    simp
  rw [h, Set.encard_coe_eq_coe_finsetCard]

/-- `countAt` is the `LemmaX` direction count, also at `⊤`. -/
theorem countAt_eq_lx (D : ℕ → Fin 4) (a : Fin 4) (N : ℕ∞) :
    countAt D a N = FrogModel.LemmaX.dirCount D a N := by
  unfold countAt
  apply le_antisymm
  · refine iSup₂_le fun n hn => ?_
    rw [← lx_dirCount_coe]
    unfold FrogModel.LemmaX.dirCount
    exact Set.encard_le_encard fun k hk => ⟨lt_of_lt_of_le hk.1 hn, hk.2⟩
  · induction N using ENat.recTopCoe with
    | coe m => exact le_iSup₂_of_le m le_rfl (lx_dirCount_coe D a m).le
    | top =>
      rcases Set.finite_or_infinite {k : ℕ | D k = a} with hf | hi
      · obtain ⟨n0, hn0⟩ := hf.bddAbove
        refine le_iSup₂_of_le (n0 + 1) le_top ?_
        rw [← lx_dirCount_coe]
        unfold FrogModel.LemmaX.dirCount
        refine Set.encard_le_encard fun k hk => ⟨?_, hk.2⟩
        have hk' : k ≤ n0 := hn0 hk.2
        exact_mod_cast Nat.lt_succ_of_le hk'
      · have htop : (⨆ (n : ℕ) (_ : (n : ℕ∞) ≤ ⊤), (dirCount D a n : ℕ∞)) = ⊤ := by
          refine ENat.eq_top_iff_forall_ge.2 fun m => ?_
          obtain ⟨t, ht, htc⟩ := hi.exists_subset_card_eq m
          refine le_iSup₂_of_le (t.sup id + 1) le_top ?_
          rw [← htc]
          unfold dirCount
          refine Nat.cast_le.2 (Finset.card_le_card fun k hk => ?_)
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hk), ht hk⟩
        rw [htop]
        exact le_top

/-- Feeding a shifted non-decreasing curve with `G 0 = 0` through `childRet`. -/
theorem childRet_shift (G : ℕ → ℕ∞) (hmono : Monotone G) (h0 : G 0 = 0) (k : ℕ) :
    FrogModel.LemmaX.childRet (fun e => G (e - 1)) (k : ℕ∞) = G k := by
  unfold FrogModel.LemmaX.childRet FrogModel.LemmaX.extCurve
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [h0]
  · rw [ite_eq_right (by exact_mod_cast hk.ne')]
    apply le_antisymm
    · refine iSup₂_le fun i hi => hmono ?_
      have hi' : i ≤ k + 1 := by exact_mod_cast hi
      omega
    · refine le_iSup₂_of_le (k + 1) (by push_cast; exact le_rfl) ?_
      simp

/-- `T` of `Psi` on the shifted curves is the closure's `T`. -/
theorem psiT_shiftC (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (hmono : ∀ c, Monotone (G c))
    (h0 : ∀ c, G c 0 = 0) (D : ℕ → Fin 4) (n : ℕ) :
    FrogModel.LemmaX.psiT (shiftC G) D q (n : ℕ∞) = closT q G D n := by
  unfold FrogModel.LemmaX.psiT closT shiftC
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lx_dirCount_coe]
  exact childRet_shift (G c) (hmono c) (h0 c) _

/-- `N` of `Psi` on the shifted curves is the closure's `N`. -/
theorem psiN_shiftC (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (hmono : ∀ c, Monotone (G c))
    (h0 : ∀ c, G c 0 = 0) (D : ℕ → Fin 4) :
    FrogModel.LemmaX.psiN (shiftC G) D q = closN q G D := by
  have hT : ∀ n : ℕ, FrogModel.LemmaX.psiT (shiftC G) D q n ≤ n ↔
      q ≤ n ∧ closT q G D n ≤ n := by
    intro n
    rw [psiT_shiftC q G hmono h0 D n]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    have hq : (q : ℕ∞) ≤ closT q G D n := le_self_add
    exact_mod_cast hq.trans h
  unfold FrogModel.LemmaX.psiN closN
  apply le_antisymm
  · exact le_iInf₂ fun n hn => sInf_le ((hT n).2 hn)
  · refine le_sInf fun x hx => ?_
    induction x using ENat.recTopCoe with
    | top => exact le_top
    | coe n => exact iInf₂_le n ((hT n).1 hx)

/-- `G` of `Psi` on the shifted curves is the closure's `X`. -/
theorem psiG_shiftC (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (hmono : ∀ c, Monotone (G c))
    (h0 : ∀ c, G c 0 = 0) (D : ℕ → Fin 4) :
    FrogModel.LemmaX.psiG (shiftC G) D q = closX q G D := by
  unfold FrogModel.LemmaX.psiG closX
  rw [psiN_shiftC q G hmono h0 D, countAt_eq_lx]

end FrogModel.D3.LaneA
