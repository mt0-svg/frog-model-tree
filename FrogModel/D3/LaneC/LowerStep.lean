module

public import FrogModel.D3.LaneC.LowerDefs
public import FrogModel.D3.LaneB.ClosureFacts
public import FrogModel.D3.LaneB.Counts

@[expose] public section

/-!
# The first step of a lower closure (deterministic)

For the proof of Lemma 12.1 of the paper. The closure after its first step is a closure with one
frog less (plus what the entered child returned) and the remaining directions: `closN_shift`,
`countAt_shift`, and for the lower curves `cnt_step`. Also the monotonicity of the counts in the
child curves and the lower curve below the planted curve given the coin increments (`lcurve_le`).
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC.Lower

theorem closN_eq_iInf (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) :
    closN q G D = ⨅ (n : ℕ) (_ : closT q G D n ≤ n), (n : ℕ∞) := by
  unfold closN
  apply le_antisymm
  · refine le_iInf₂ ?_
    intro n hn
    have hq_le_n : q ≤ n := by
      have hpos : (q : ℕ∞) ≤ closT q G D n := by
        unfold closT
        exact le_self_add
      have hq_n' : (q : ℕ∞) ≤ (n : ℕ∞) := le_trans hpos hn
      exact (Nat.cast_le (α := ℕ∞)).mp hq_n'
    exact iInf₂_le n ⟨hq_le_n, hn⟩
  · refine le_iInf₂ ?_
    intro n hn
    exact iInf₂_le n hn.2

theorem closN_shift (q q' : ℕ) (G G' : Fin 3 → ℕ → ℕ∞) (D D' : ℕ → Fin 4) (hq : 1 ≤ q)
    (h : ∀ n, closT q G D (n + 1) = closT q' G' D' n + 1) :
    closN q G D = closN q' G' D' + 1 := by
  rw [closN_eq_iInf, closN_eq_iInf]
  set P := fun (n : ℕ) => closT q G D n ≤ (n : ℕ∞)
  set Q := fun (n : ℕ) => closT q' G' D' n ≤ (n : ℕ∞)
  have h1_ne_top : (1 : ℕ∞) ≠ ⊤ := by decide
  have hP0 : ¬ P 0 := by
    intro hP0
    have hq_le : (1 : ℕ∞) ≤ closT q G D 0 := by
      have hq' : (1 : ℕ∞) ≤ (q : ℕ∞) := by exact_mod_cast hq
      rw [closT]
      have hsum : (0 : ℕ∞) ≤ ∑ c : Fin 3, G c (dirCount D c.succ 0) :=
        Finset.sum_nonneg fun c _ => zero_le (a := G c (dirCount D c.succ 0))
      -- q + sum ≥ q ≥ 1
      have hq_sum : (q : ℕ∞) ≤ (q : ℕ∞) + ∑ c : Fin 3, G c (dirCount D c.succ 0) :=
        le_add_of_nonneg_right hsum
      exact le_trans hq' hq_sum
    have h10 : (1 : ℕ∞) ≤ (0 : ℕ∞) := le_trans hq_le hP0
    have hpos : (0 : ℕ∞) < 1 := by norm_num
    exact (lt_irrefl 0 (lt_of_lt_of_le hpos h10)).elim
  have hP_succ_iff_Q : ∀ m, P (m + 1) ↔ Q m := by
    intro m
    unfold P Q
    rw [h m]
    -- Goal: (closT q' G' D' m + 1 ≤ (m + 1 : ℕ∞)) ↔ (closT q' G' D' m ≤ (m : ℕ∞))
    have hcast : ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + (1 : ℕ∞) := by simp
    rw [hcast]
    exact ENat.add_le_add_iff_right h1_ne_top
  apply le_antisymm
  · rw [ENat.iInf_add]
    refine le_iInf fun n => ?_
    rw [ENat.iInf_add]
    refine le_iInf fun hnQ => ?_
    have hP_succ : P (n + 1) := (hP_succ_iff_Q n).mpr hnQ
    have hL_le : (⨅ (n : ℕ) (_ : P n), (n : ℕ∞)) ≤ (n + 1 : ℕ∞) := iInf₂_le (n + 1) hP_succ
    simpa [Nat.cast_add] using hL_le
  · refine le_iInf₂ fun n hnP => ?_
    by_cases hn0 : n = 0
    · exfalso; exact hP0 (hn0 ▸ hnP)
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [hm] at hnP ⊢
      have hQm : Q m := (hP_succ_iff_Q m).mp hnP
      have hR_le : (⨅ (n : ℕ) (_ : Q n), (n : ℕ∞)) ≤ (m : ℕ∞) := iInf₂_le m hQm
      simpa [Nat.cast_add] using add_le_add_right hR_le (1 : ℕ∞)

theorem countAt_shift (D : ℕ → Fin 4) (b : Fin 4) (N : ℕ∞) :
    countAt D b (N + 1) = (if D 0 = b then 1 else 0) + countAt (fun i => D (i + 1)) b N := by
  set a := (if D 0 = b then (1 : ℕ∞) else 0) with ha
  have h_dirCount_zero : (dirCount D b 0 : ℕ∞) = 0 := by
    simp [dirCount]
  have h_dirCount_succ (m : ℕ) : (dirCount D b (m + 1) : ℕ∞) = a + (dirCount (fun i => D (i + 1)) b m : ℕ∞) := by
    dsimp [dirCount, a]
    rw [Finset.card_filter]
    rw [Finset.sum_range_succ']
    simp [add_comm]
  have h_add_one_cancel {x y : ℕ∞} (h : x + (1 : ℕ∞) ≤ y + (1 : ℕ∞)) : x ≤ y := by
    by_contra! hlt
    -- hlt : y < x
    have hlt' : y + (1 : ℕ∞) < x + (1 : ℕ∞) :=
      WithTop.add_lt_add_right (hz := (by simp : (1 : ℕ∞) ≠ ⊤)) hlt
    exact not_lt.mpr h hlt'
  apply le_antisymm
  · -- countAt D b (N + 1) ≤ a + countAt (fun i => D (i + 1)) b N
    unfold countAt
    refine iSup₂_le fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with (rfl | hpos)
    · rw [h_dirCount_zero]
      exact bot_le
    · rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨m, rfl⟩
      rw [h_dirCount_succ m]
      have hm_le_N : (m : ℕ∞) ≤ N := h_add_one_cancel hn
      have hle : (dirCount (fun i => D (i + 1)) b m : ℕ∞) ≤
          ⨆ (n : ℕ) (_ : (n : ℕ∞) ≤ N), (dirCount (fun i => D (i + 1)) b n : ℕ∞) :=
        le_iSup₂ (f := fun (n : ℕ) (_ : (n : ℕ∞) ≤ N) => (dirCount (fun i => D (i + 1)) b n : ℕ∞)) m hm_le_N
      simpa [add_comm] using add_le_add_right hle a
  · -- a + countAt (fun i => D (i + 1)) b N ≤ countAt D b (N + 1)
    unfold countAt
    have h_add := ENat.add_iSup (a := a) (f := fun (n : ℕ) => ⨆ (_ : (n : ℕ∞) ≤ N), (dirCount (fun i => D (i + 1)) b n : ℕ∞))
    rw [h_add]
    -- Goal: ⨆ n, a + (⨆ (_ : ↑n ≤ N), ↑(dirCount D' b n)) ≤ ⨆ n, ⨆ (_ : ↑n ≤ N + 1), ↑(dirCount D b n)
    refine iSup_le fun n => ?_
    -- Goal: a + (⨆ (_ : ↑n ≤ N), ↑(dirCount D' b n)) ≤ ⨆ n, ⨆ (_ : ↑n ≤ N + 1), ↑(dirCount D b n)
    by_cases hn : (n : ℕ∞) ≤ N
    · -- Then the inner iSup is just dirCount D' b n
      have h_inner : (⨆ (_ : (n : ℕ∞) ≤ N), (dirCount (fun i => D (i + 1)) b n : ℕ∞)) = (dirCount (fun i => D (i + 1)) b n : ℕ∞) := by
        simp [hn]
      rw [h_inner, ← h_dirCount_succ n]
      -- Goal: (dirCount D b (n + 1) : ℕ∞) ≤ ⨆ n, ⨆ (_ : ↑n ≤ N + 1), ↑(dirCount D b n)
      have hn_succ : ((n + 1 : ℕ) : ℕ∞) ≤ N + 1 := by
        simpa [Nat.cast_add, Nat.cast_one] using add_le_add_right hn (1 : ℕ∞)
      exact le_iSup₂ (f := fun (n : ℕ) (_ : (n : ℕ∞) ≤ N + 1) => (dirCount D b n : ℕ∞)) (n + 1) hn_succ
    · -- Then the inner iSup is 0 (bottom)
      have h_inner : (⨆ (_ : (n : ℕ∞) ≤ N), (dirCount (fun i => D (i + 1)) b n : ℕ∞)) = 0 := by
        simp [hn]
      rw [h_inner, add_zero]
      -- Goal: a ≤ ⨆ n, ⨆ (_ : ↑n ≤ N + 1), ↑(dirCount D b n)
      -- Since a = dirCount D b 1 and (1 : ℕ∞) ≤ N + 1
      have h1 : (1 : ℕ∞) ≤ N + 1 := by
        simp
      -- Now we need to show a ≤ dirCount D b 1 or directly a ≤ the sup
      -- Actually, dirCount D b 1 = a
      have h_dirCount_one : (dirCount D b 1 : ℕ∞) = a := by
        simp [dirCount, a, Finset.range_one, Finset.filter_singleton]
        split_ifs <;> simp
      rw [← h_dirCount_one]
      exact le_iSup₂ (f := fun (n : ℕ) (_ : (n : ℕ∞) ≤ N + 1) => (dirCount D b n : ℕ∞)) 1 h1

theorem dirCount_shift (D : ℕ → Fin 4) (a : Fin 4) (n : ℕ) :
    dirCount D a (n + 1) = dirCount (fun i => D (i + 1)) a n + (if D 0 = a then 1 else 0) := by
  induction n with
  | zero => rw [dirCount_succ, dirCount_zero, dirCount_zero]
  | succ n ih =>
    rw [dirCount_succ, ih, dirCount_succ (fun i => D (i + 1))]
    omega

theorem closT_step_up (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) (hq : 1 ≤ q) (hD : D 0 = 0) (n : ℕ) :
    closT q G D (n + 1) = closT (q - 1) G (fun i => D (i + 1)) n + 1 := by
  have hterm : ∀ c : Fin 3, G c (dirCount D c.succ (n + 1)) =
      G c (dirCount (fun i => D (i + 1)) c.succ n) := by
    intro c
    rw [dirCount_shift, ite_eq_right (by rw [hD]; exact (Fin.succ_ne_zero c).symm), add_zero]
  unfold closT
  rw [Finset.sum_congr rfl fun c _ => hterm c]
  have hq' : (q : ℕ∞) = ((q - 1 : ℕ) : ℕ∞) + 1 := by
    rw [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.sub_add_cancel hq]
  rw [hq']
  ring

theorem closT_step_child (q x : ℕ) (s : Fin 3) (G G' : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) (hq : 1 ≤ q) (hD : D 0 = s.succ)
    (hs : ∀ k, G s (k + 1) = G' s k + x) (ht : ∀ t, t ≠ s → G' t = G t) (n : ℕ) :
    closT q G D (n + 1) = closT (q - 1 + x) G' (fun i => D (i + 1)) n + 1 := by
  have hterm : ∀ c : Fin 3, G c (dirCount D c.succ (n + 1)) =
      G' c (dirCount (fun i => D (i + 1)) c.succ n) + (if c = s then (x : ℕ∞) else 0) := by
    intro c
    rw [dirCount_shift]
    by_cases hc : c = s
    · subst hc
      rw [ite_eq_left hD, ite_eq_left rfl, hs]
    · have hne : ¬ D 0 = c.succ := by
        rw [hD]; exact fun h => hc (Fin.succ_injective _ h).symm
      rw [ite_eq_right hne, add_zero, ite_eq_right hc, add_zero, ht c hc]
  unfold closT
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hq' : (q : ℕ∞) = ((q - 1 : ℕ) : ℕ∞) + 1 := by
    rw [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.sub_add_cancel hq]
  rw [hq', Nat.cast_add]
  ring

theorem cnt_step_of (b : Fin 4) (q q' : ℕ) (τ τ' : Fin 3 → Ty) (ω ω' : LSample) (hq : 1 ≤ q)
    (hD : ω'.1 = fun i => ω.1 (i + 1))
    (h : ∀ n, closT q (curves τ ω) ω.1 (n + 1) = closT q' (curves τ' ω') ω'.1 n + 1) :
    cnt b q τ ω = (if ω.1 0 = b then 1 else 0) + cnt b q' τ' ω' := by
  unfold cnt
  rw [closN_shift q q' _ _ _ _ hq h, countAt_shift, hD]

theorem cnt_step (b : Fin 4) (q : ℕ) (τ : Fin 3 → Ty) (ω : LSample) (hq : 1 ≤ q) :
    cnt b q τ ω = (if ω.1 0 = b then 1 else 0) +
      cnt b (stepA (ω.1 0) q τ (shiftD ω)).1 (stepA (ω.1 0) q τ (shiftD ω)).2.1
        (stepA (ω.1 0) q τ (shiftD ω)).2.2 := by
  have key : ∀ a, ω.1 0 = a → cnt b q τ ω = (if ω.1 0 = b then 1 else 0) +
      cnt b (stepA a q τ (shiftD ω)).1 (stepA a q τ (shiftD ω)).2.1
        (stepA a q τ (shiftD ω)).2.2 := by
    intro a ha
    cases a using Fin.cases with
    | zero =>
      simp only [stepA, Fin.cases_zero]
      exact cnt_step_of b q (q - 1) τ τ ω (shiftD ω) hq rfl
        fun n => closT_step_up q (curves τ ω) ω.1 hq ha n
    | succ s =>
      simp only [stepA, Fin.cases_succ]
      cases hτ : τ s with
      | dead =>
        refine cnt_step_of b q (q - 1) τ τ ω (shiftD ω) hq rfl fun n => ?_
        have h := closT_step_child q 0 s (curves τ ω) (curves τ ω) ω.1 hq ha
          (fun k => by simp [curves, hτ, lcurve]) (fun _ _ => rfl) n
        rw [Nat.add_zero] at h
        exact h
      | fresh =>
        refine cnt_step_of b q _ τ _ ω (shiftD ω) hq rfl fun n => ?_
        refine closT_step_child q (ω.2.1 s) s (curves τ ω) (curves (Function.update τ s .coin) ω)
          ω.1 hq ha (fun k => ?_) (fun t ht => ?_) n
        · simp only [curves, hτ, Function.update_self, lcurve, Nat.add_sub_cancel,
            Nat.add_one_ne_zero, ite_false]
          push_cast
          ring
        · simp only [curves, Function.update_of_ne ht]
      | coin =>
        refine cnt_step_of b q _ τ _ ω _ hq rfl fun n => ?_
        refine closT_step_child q (ω.2.2 s 0).toNat s (curves τ ω) _ ω.1 hq ha (fun k => ?_)
          (fun t ht => ?_) n
        · simp only [curves, hτ, shiftD, Function.update_self, lcurve]
          rw [Finset.sum_range_succ']
          push_cast
          ring
        · simp only [curves, shiftD, Function.update_of_ne ht]
  exact key _ rfl

theorem cnt_zero (b : Fin 4) (τ : Fin 3 → Ty) (ω : LSample) : cnt b 0 τ ω = 0 := by
  unfold cnt countAt
  have hcurve0 : ∀ i : Fin 3, curves τ ω i 0 = 0 := by
    intro i
    unfold curves
    cases τ i <;> simp [lcurve]
  have hT0 : closT 0 (curves τ ω) ω.1 0 ≤ (0 : ℕ) := by
    unfold closT
    simp [hcurve0, dirCount]
  have h0 : (0 : ℕ) ≤ (0 : ℕ) := le_refl 0
  have hN : closN 0 (curves τ ω) ω.1 ≤ (0 : ℕ∞) := by
    apply iInf₂_le (0 : ℕ)
    exact ⟨h0, hT0⟩
  have hN0 : closN 0 (curves τ ω) ω.1 = 0 := by
    apply le_antisymm hN
    exact zero_le
  rw [hN0]
  simp [dirCount]

theorem countAt_closN_mono (q : ℕ) (G G' : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) (a : Fin 4)
    (h : ∀ c k, G c k ≤ G' c k) : countAt D a (closN q G D) ≤ countAt D a (closN q G' D) := by
  have hT : ∀ n, closT q G D n ≤ closT q G' D n := by
    intro n
    unfold closT
    have hsum : (∑ c : Fin 3, G c (dirCount D c.succ n)) ≤ (∑ c : Fin 3, G' c (dirCount D c.succ n)) :=
      Finset.sum_le_sum fun c _ => h c (dirCount D c.succ n)
    exact add_le_add (le_refl (q : ℕ∞)) hsum
  have hN : closN q G D ≤ closN q G' D := by
    refine le_iInf₂ fun n hn' => ?_
    rcases hn' with ⟨hq, hTn⟩
    have hP : q ≤ n ∧ closT q G D n ≤ n := ⟨hq, le_trans (hT n) hTn⟩
    exact iInf₂_le n hP
  have h_mono : Monotone (countAt D a) := (countAt_facts D a).2.2
  exact h_mono hN

theorem enat_toNat_le (x : ℕ∞) : (x.toNat : ℕ∞) ≤ x := by
  by_cases hx : x = ⊤
  · subst x; simp
  · have hx_eq : (x.toNat : ℕ∞) = x := (ENat.natCast_toNat_eq_self.mpr hx)
    rw [hx_eq]

theorem lcurve_le (G : ℕ → ℕ∞) (ξ : ℕ → Bool) (GM : ℕ) (h : ∀ i, G i + (if ξ i then 1 else 0) ≤ G (i + 1))
    (k : ℕ) : lcurve .fresh (min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat (fun i => ξ (i + 1)) k ≤ G k := by
  induction' k with k ih
  · -- k = 0
    simp [lcurve]
  · -- k → k+1
    by_cases hk : k = 0
    · -- k = 0, need R ≤ G 1
      subst hk
      simp [lcurve]
      have hbase : (min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat ≤ G 1 := by
        have h := enat_toNat_le (min (G 1) ((GM + 1 : ℕ) : ℕ∞))
        exact le_trans h (min_le_left _ _)
      exact hbase
    · -- k ≥ 1
      have hkpos : 1 ≤ k := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk)
      -- Expand lcurve for k+1
      simp [lcurve]
      -- Goal: ↑(min (G 1) (↑GM + 1)).toNat + ∑ x ∈ Finset.range k, ↑(ξ (x + 1)).toNat ≤ G (k + 1)
      -- Get the explicit formula for lcurve at k (since k ≥ 1)
      have h_lcurve_k : lcurve .fresh (min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat (fun i => ξ (i + 1)) k =
          ((min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat + ∑ i ∈ Finset.range (k - 1), (ξ (i + 1)).toNat : ℕ∞) := by
        simp [lcurve, hk]
      -- From IH, we get an inequality for the sum up to k-1
      have ih' : ((min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat + ∑ i ∈ Finset.range (k - 1), (ξ (i + 1)).toNat : ℕ∞) ≤ G k := by
        -- ih gives: lcurve ... k ≤ G k
        -- and h_lcurve_k gives the explicit form
        rw [h_lcurve_k] at ih
        exact ih
      -- Relate the sum for k to the sum for k-1
      -- ∑ i ∈ range k, (ξ (i+1)).toNat = (∑ i ∈ range (k-1), (ξ (i+1)).toNat) + (ξ k).toNat
      have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hkpos).symm
      have h_sum_nat : (∑ i ∈ Finset.range k, (ξ (i + 1)).toNat : ℕ) =
          (∑ i ∈ Finset.range (k - 1), (ξ (i + 1)).toNat : ℕ) + (ξ k).toNat := by
        rw [hk_eq, Finset.sum_range_succ]
        simp [Nat.sub_add_cancel hkpos]
      -- Convert to ℕ∞
      have h_sum : (∑ i ∈ Finset.range k, (ξ (i + 1)).toNat : ℕ∞) =
          (∑ i ∈ Finset.range (k - 1), (ξ (i + 1)).toNat : ℕ∞) + (ξ k).toNat := by
        exact_mod_cast h_sum_nat
      -- Now rewrite the goal using h_sum
      rw [h_sum]
      -- Goal: ↑(min (G 1) (↑GM + 1)).toNat + ((∑ i ∈ range (k - 1), ↑(ξ (i + 1)).toNat) + ↑(ξ k).toNat) ≤ G (k + 1)
      -- Get T = (ξ k).toNat in terms of if
      have hT : (ξ k).toNat = if ξ k then 1 else 0 := by
        by_cases hξ : ξ k
        · simp [hξ]
        · simp [hξ]
      -- Use calc block with proper handling of casts
      -- Let R := ↑(min ...).toNat, S := ∑ i ∈ range (k-1), ↑(ξ (i+1)).toNat, T := ↑(ξ k).toNat
      calc
        ((min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat : ℕ∞) + ((∑ i ∈ Finset.range (k - 1), (ξ (i + 1)).toNat : ℕ∞) + (ξ k).toNat)
            = (((min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat : ℕ∞) + (∑ i ∈ Finset.range (k - 1), (ξ (i + 1)).toNat : ℕ∞)) + (ξ k).toNat := by
          ring
        _ ≤ G k + (ξ k).toNat := by
          -- ih' : ↑(min ...).toNat + ↑(∑ ...) ≤ G k
          -- We need: (R + S) + T ≤ G k + T
          -- Use add_le_add_left: b + a ≤ c + a
          -- But ih' has ↑(∑ ...) while goal has ∑ ↑(...)
          -- These are equal by Nat.cast_sum
          have htemp := add_le_add_left ih' ((ξ k).toNat : ℕ∞)
          -- htemp: (↑(min ...).toNat + ↑(∑ ...)) + ↑(ξ k).toNat ≤ G k + ↑(ξ k).toNat
          simpa [Nat.cast_sum, add_assoc] using htemp
        _ = G k + ((ξ k).toNat : ℕ∞) := rfl
        _ = G k + (if ξ k then (1 : ℕ∞) else 0) := by
          rw [hT]
          -- Push the cast through the if
          simp
        _ ≤ G (k + 1) := h k

theorem lcurve_zero (t : Ty) (R : ℕ) (ζ : ℕ → Bool) : lcurve t R ζ 0 = 0 := by
  cases t <;> simp [lcurve]

theorem lcurve_congr (t : Ty) (R : ℕ) (ζ ζ' : ℕ → Bool) (k : ℕ) (h : ∀ i < k, ζ i = ζ' i) :
    lcurve t R ζ k = lcurve t R ζ' k := by
  cases t with
  | dead => rfl
  | fresh =>
    simp only [lcurve]
    split_ifs with hk
    · rfl
    · rw [Finset.sum_congr rfl fun i hi => (show (ζ i).toNat = (ζ' i).toNat by
        rw [h i (by have := Finset.mem_range.1 hi; omega)])]
  | coin =>
    simp only [lcurve]
    rw [Finset.sum_congr rfl fun i hi => (show (ζ i).toNat = (ζ' i).toNat by
      rw [h i (Finset.mem_range.1 hi)])]

/-- A curve of type other than `fresh` does not read its first answer. -/
theorem curves_update_R (τ : Fin 3 → Ty) (s : Fin 3) (hs : τ s ≠ .fresh) (ω : LSample) (r : ℕ) :
    curves τ ((ω.1, Function.update ω.2.1 s r, ω.2.2) : LSample) = curves τ ω := by
  funext t k
  by_cases hts : t = s
  · subst hts
    simp only [curves, Function.update_self]
    cases h : τ t with
    | dead => rfl
    | fresh => exact absurd h hs
    | coin => rfl
  · simp [curves, Function.update_of_ne hts]

/-- A dead child reads nothing. -/
theorem curves_dead (τ : Fin 3 → Ty) (s : Fin 3) (hs : τ s = .dead) (ω ω' : LSample)
    (hR : ∀ t, t ≠ s → ω.2.1 t = ω'.2.1 t) (hζ : ∀ t, t ≠ s → ω.2.2 t = ω'.2.2 t) :
    curves τ ω = curves τ ω' := by
  funext t k
  by_cases hts : t = s
  · subst hts
    simp [curves, hs, lcurve]
  · simp [curves, hR t hts, hζ t hts]

end FrogModel.D3.LaneC.Lower
