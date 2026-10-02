module

public import FrogModel.LemmaX.Defs

@[expose] public section

/-!
# Lemma X: the map `Psi` as a deterministic map

Lemma 4.2 of the paper. The extended curves and the direction counts (`extCurve`,
`dirCount`, `childRet`), then `T_j` (`psiT`: monotone, monotone in `j` and in the child curves,
commuting with suprema of non-decreasing sequences), its least fixed point `N(j)` (`psiN`: fixed
point, least, the limit of the iterates, `k < N(j)` gives `k < T_j(k)`, monotone in `j` and in
the child curves) and the curve `G` (`psiG`: `G(0) = 0`, non-decreasing, monotone in the child
curves).
-/

open scoped ENNReal
open FrogModel.LemmaX

/-- The extended curve is non-decreasing, whatever `G`. -/
theorem FrogModel.LemmaX.extCurve_mono (G : ℕ → ℕ∞) : Monotone (extCurve G) := by
  intro m m' h
  exact iSup₂_mono' fun i hi => ⟨i, hi.trans h, le_rfl⟩

/-- A non-decreasing curve agrees with its extension at the finite points. -/
theorem FrogModel.LemmaX.extCurve_coe (G : ℕ → ℕ∞) (hG : Monotone G) (m : ℕ) :
    extCurve G m = G m := by
  refine le_antisymm (iSup₂_le fun i hi => hG (by exact_mod_cast hi)) ?_
  exact le_iSup₂_of_le (f := fun (i : ℕ) (_ : (i : ℕ∞) ≤ m) => G i) m le_rfl le_rfl

/-- The extension is monotone in the curve. -/
theorem FrogModel.LemmaX.extCurve_le_of_le (G G' : ℕ → ℕ∞) (h : ∀ i, G i ≤ G' i) (m : ℕ∞) :
    extCurve G m ≤ extCurve G' m := by
  exact iSup₂_mono fun i _ => h i

/-- The extension commutes with suprema of sequences. -/
theorem FrogModel.LemmaX.extCurve_iSup (G : ℕ → ℕ∞) (m : ℕ → ℕ∞) :
    extCurve G (⨆ t, m t) = ⨆ t, extCurve G (m t) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    obtain ⟨t, ht⟩ : ∃ t, (i : ℕ∞) ≤ m t := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨0, by simp⟩
      · have h1 : ((i - 1 : ℕ) : ℕ∞) < ⨆ t, m t :=
          lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hi0 one_pos) hi
        obtain ⟨t, ht⟩ := lt_iSup_iff.1 h1
        refine ⟨t, ?_⟩
        have h2 := Order.add_one_le_of_lt ht
        have h3 : ((i - 1 : ℕ) : ℕ∞) + 1 = i := by norm_cast; omega
        rwa [h3] at h2
    exact le_iSup_of_le t (le_iSup₂_of_le (f := fun (i : ℕ) (_ : (i : ℕ∞) ≤ m t) => G i) i ht le_rfl)
  · exact iSup_le fun t => extCurve_mono G (le_iSup m t)

/-- The direction count is non-decreasing in the number of steps. -/
theorem FrogModel.LemmaX.dirCount_mono {d : ℕ} (D : ℕ → Fin (d + 1)) (a : Fin (d + 1)) :
    Monotone (dirCount D a) := by
  intro n n' h
  exact Set.encard_le_encard fun k hk => ⟨lt_of_lt_of_le hk.1 h, hk.2⟩

/-- The direction count at a finite number of steps is a finset card. -/
theorem FrogModel.LemmaX.dirCount_coe {d : ℕ} (D : ℕ → Fin (d + 1)) (a : Fin (d + 1)) (n : ℕ) :
    dirCount D a n = (((Finset.range n).filter fun k => D k = a).card : ℕ∞) := by
  unfold dirCount
  have h : {k : ℕ | (k : ℕ∞) < n ∧ D k = a} = ↑((Finset.range n).filter fun k => D k = a) := by
    ext k
    simp [Nat.cast_lt]
  rw [h, Set.encard_coe_eq_coe_finsetCard]

/-- One more step adds one to the count of its direction. -/
theorem FrogModel.LemmaX.dirCount_succ {d : ℕ} (D : ℕ → Fin (d + 1)) (a : Fin (d + 1)) (k : ℕ) :
    dirCount D a ((k + 1 : ℕ) : ℕ∞) = dirCount D a k + if D k = a then 1 else 0 := by
  rw [dirCount_coe, dirCount_coe, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
    push_cast
    rfl
  · simp

/-- Every step goes to the parent or to one child. -/
theorem FrogModel.LemmaX.dirCount_add_sum {d : ℕ} (D : ℕ → Fin (d + 1)) (n : ℕ) :
    dirCount D 0 n + ∑ c : Fin d, dirCount D c.succ n = n := by
  simp only [dirCount_coe]
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.range n) (t := Finset.univ) (f := D)
    (fun _ _ => Finset.mem_univ _)
  rw [Fin.sum_univ_succ, Finset.card_range] at h
  exact_mod_cast h.symm

/-- The direction count commutes with suprema of non-decreasing sequences. -/
theorem FrogModel.LemmaX.dirCount_iSup {d : ℕ} (D : ℕ → Fin (d + 1)) (a : Fin (d + 1))
    (n : ℕ → ℕ∞) (_hn : Monotone n) :
    dirCount D a (⨆ t, n t) = ⨆ t, dirCount D a (n t) := by
  refine le_antisymm ?_ (iSup_le fun t => dirCount_mono D a (le_iSup n t))
  set U : Set ℕ := {k : ℕ | (k : ℕ∞) < ⨆ t, n t ∧ D k = a} with hU
  -- a finite subset of `U` lies in one of the sets at `n t`
  have hfin : ∀ T : Set ℕ, T.Finite → T ⊆ U →
      ∃ t, T ⊆ {k : ℕ | (k : ℕ∞) < n t ∧ D k = a} := by
    intro T hT hTU
    rcases T.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, Set.empty_subset _⟩
    · set M := hT.toFinset.max' (hT.toFinset_nonempty.2 hne) with hM
      have hMT : M ∈ T := hT.mem_toFinset.1 (Finset.max'_mem _ _)
      obtain ⟨t, ht⟩ := lt_iSup_iff.1 (hTU hMT).1
      refine ⟨t, fun k hk => ⟨lt_of_le_of_lt ?_ ht, (hTU hk).2⟩⟩
      exact_mod_cast Finset.le_max' _ k (hT.mem_toFinset.2 hk)
  by_contra hlt
  push Not at hlt
  have hne : (⨆ t, dirCount D a (n t)) ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  have h1 : ((N + 1 : ℕ) : ℕ∞) ≤ U.encard := by
    have := Order.add_one_le_of_lt (hN ▸ hlt : (N : ℕ∞) < dirCount D a (⨆ t, n t))
    exact_mod_cast this
  obtain ⟨T, hTU, hTc⟩ := Set.exists_subset_encard_eq h1
  have hTf : T.Finite := Set.finite_of_encard_eq_coe hTc
  obtain ⟨t, ht⟩ := hfin T hTf hTU
  have h2 : T.encard ≤ ⨆ t, dirCount D a (n t) :=
    (Set.encard_le_encard ht).trans (le_iSup (fun t => dirCount D a (n t)) t)
  rw [hTc, ← hN] at h2
  exact absurd h2 (by norm_cast; omega)

/-- The child returns are non-decreasing in the number of entries. -/
theorem FrogModel.LemmaX.childRet_mono (G : ℕ → ℕ∞) : Monotone (childRet G) := by
  intro m m' h
  unfold childRet
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : m' ≠ 0 := fun h0 => hm (le_antisymm (h0 ▸ h) (zero_le))
    simp only [hm, hm', ite_false]
    exact extCurve_mono G (by gcongr)

/-- The child returns commute with suprema of non-decreasing sequences. -/
theorem FrogModel.LemmaX.childRet_iSup (G : ℕ → ℕ∞) (m : ℕ → ℕ∞) (hm : Monotone m) :
    childRet G (⨆ t, m t) = ⨆ t, childRet G (m t) := by
  by_cases h0 : (⨆ t, m t) = 0
  · have hz : ∀ t, m t = 0 := fun t => le_antisymm (h0 ▸ le_iSup m t) zero_le
    simp [childRet, hz]
  · obtain ⟨t0, ht0⟩ : ∃ t0, m t0 ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by simp [h])
    have hc : childRet G (⨆ t, m t) = extCurve G ((⨆ t, m t) + 1) := by simp [childRet, h0]
    rw [hc, ENat.iSup_add, extCurve_iSup]
    refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun t => ?_)
    · have hne : m (max t t0) ≠ 0 := fun h => ht0 (le_antisymm (h ▸ hm (le_max_right t t0)) zero_le)
      refine le_iSup_of_le (max t t0) ?_
      simp only [childRet, hne, ite_false]
      exact extCurve_mono G (by gcongr; exact hm (le_max_left t t0))
    · unfold childRet
      split_ifs with h
      · exact zero_le
      · exact le_iSup (fun t => extCurve G (m t + 1)) t

/-- `T_j` is non-decreasing. -/
theorem FrogModel.LemmaX.psiT_mono {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ) :
    Monotone (psiT G D j) := by
  intro n n' h
  unfold psiT
  gcongr with c
  exact childRet_mono (G c) (dirCount_mono D c.succ h)

/-- `T_j` is non-decreasing in `j`. -/
theorem FrogModel.LemmaX.psiT_mono_left {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1))
    (j j' : ℕ) (h : j ≤ j') (n : ℕ∞) : psiT G D j n ≤ psiT G D j' n := by
  unfold psiT
  gcongr

/-- `T_j` is monotone in the child curves. -/
theorem FrogModel.LemmaX.psiT_le_of_le {d : ℕ} (G G' : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1))
    (h : ∀ c i, G c i ≤ G' c i) (j : ℕ) (n : ℕ∞) : psiT G D j n ≤ psiT G' D j n := by
  unfold psiT childRet
  gcongr with c
  split_ifs
  · exact le_rfl
  · exact extCurve_le_of_le (G c) (G' c) (h c) _

/-- `T_j(n) ≥ j`. -/
theorem FrogModel.LemmaX.le_psiT {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ)
    (n : ℕ∞) : (j : ℕ∞) ≤ psiT G D j n := by
  exact le_self_add

/-- `T_j` commutes with suprema of non-decreasing sequences. -/
theorem FrogModel.LemmaX.psiT_iSup {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ)
    (n : ℕ → ℕ∞) (hn : Monotone n) :
    psiT G D j (⨆ t, n t) = ⨆ t, psiT G D j (n t) := by
  unfold psiT
  have hc : ∀ c : Fin d, childRet (G c) (dirCount D c.succ (⨆ t, n t)) =
      ⨆ t, childRet (G c) (dirCount D c.succ (n t)) := by
    intro c
    rw [dirCount_iSup D c.succ n hn]
    exact childRet_iSup (G c) _ fun s t h => dirCount_mono D c.succ (hn h)
  simp_rw [hc]
  rw [ENat.sum_iSup_of_monotone fun c s t h =>
    childRet_mono (G c) (dirCount_mono D c.succ (hn h)), ENat.add_iSup]

/-- `N(j)` is below every prefixed point of `T_j`. -/
theorem FrogModel.LemmaX.psiN_le {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ)
    (n : ℕ∞) (h : psiT G D j n ≤ n) : psiN G D j ≤ n := by
  exact sInf_le h

/-- `N(j)` is a fixed point of `T_j`. -/
theorem FrogModel.LemmaX.psiN_fixed {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ) :
    psiT G D j (psiN G D j) = psiN G D j := by
  have hT := psiT_mono G D j
  have h1 : psiT G D j (psiN G D j) ≤ psiN G D j :=
    le_sInf fun n hn => (hT (psiN_le G D j n hn)).trans hn
  exact le_antisymm h1 (psiN_le G D j _ (hT h1))

/-- `N(j) ≥ j`. -/
theorem FrogModel.LemmaX.le_psiN {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ) :
    (j : ℕ∞) ≤ psiN G D j := by
  exact le_sInf fun n hn => (le_psiT G D j n).trans hn

/-- `N(j)` is non-decreasing in `j`. -/
theorem FrogModel.LemmaX.psiN_mono_left {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) :
    Monotone (psiN G D) := by
  intro j j' h
  refine psiN_le G D j _ ?_
  calc psiT G D j (psiN G D j') ≤ psiT G D j' (psiN G D j') := psiT_mono_left G D j j' h _
    _ = psiN G D j' := psiN_fixed G D j'

/-- `N(j)` is monotone in the child curves. -/
theorem FrogModel.LemmaX.psiN_le_of_le {d : ℕ} (G G' : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1))
    (h : ∀ c i, G c i ≤ G' c i) (j : ℕ) : psiN G D j ≤ psiN G' D j := by
  refine psiN_le G D j _ ?_
  calc psiT G D j (psiN G' D j) ≤ psiT G' D j (psiN G' D j) := psiT_le_of_le G G' D h j _
    _ = psiN G' D j := psiN_fixed G' D j

/-- No initial frog, no step: `N(0) = 0`. -/
theorem FrogModel.LemmaX.psiN_zero {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) :
    psiN G D 0 = 0 := by
  refine le_antisymm (psiN_le G D 0 0 ?_) zero_le
  simp [psiT, childRet, dirCount]

/-- With zero child curves, `N(j) = j`. -/
theorem FrogModel.LemmaX.psiN_of_zero {d : ℕ} (D : ℕ → Fin (d + 1)) (j : ℕ) :
    psiN (fun _ _ => 0 : Fin d → ℕ → ℕ∞) D j = j := by
  have hT : ∀ n, psiT (fun _ _ => 0 : Fin d → ℕ → ℕ∞) D j n = j := by
    intro n
    simp [psiT, childRet, extCurve]
  exact le_antisymm (psiN_le _ D j j (hT j).le) (le_psiN _ D j)

/-- Before `N(j)` steps, a frog is there for the next step: `k < T_j(k)`. -/
theorem FrogModel.LemmaX.lt_psiT_of_lt_psiN {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1))
    (j k : ℕ) (hk : (k : ℕ∞) < psiN G D j) : (k : ℕ∞) < psiT G D j k := by
  exact lt_of_not_ge fun h => absurd (psiN_le G D j k h) (not_le.2 hk)

/-- `N(j) = ⊤` exactly when `T_j` has no finite prefixed point. -/
theorem FrogModel.LemmaX.psiN_eq_top_iff {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1))
    (j : ℕ) : psiN G D j = ⊤ ↔ ∀ n : ℕ, (n : ℕ∞) < psiT G D j n := by
  constructor
  · intro h n
    exact lt_psiT_of_lt_psiN G D j n (h ▸ ENat.natCast_lt_top n)
  · intro h
    by_contra hne
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
    have := h n
    rw [hn, psiN_fixed] at this
    exact lt_irrefl _ this

/-- `N(j)` is the limit of the iterates of `T_j` from `0`. -/
theorem FrogModel.LemmaX.psiN_eq_iSup_iterate {d : ℕ} (G : Fin d → ℕ → ℕ∞)
    (D : ℕ → Fin (d + 1)) (j : ℕ) : psiN G D j = ⨆ t : ℕ, (psiT G D j)^[t] 0 := by
  set T := psiT G D j with hT
  have hmono : Monotone T := psiT_mono G D j
  have ha : Monotone fun t : ℕ => T^[t] 0 := by
    refine monotone_nat_of_le_succ fun t => ?_
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' T (t + 1)]
      exact hmono ih
  have hle : ∀ t, T^[t] 0 ≤ psiN G D j := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc T (T^[t] 0) ≤ T (psiN G D j) := hmono ih
        _ = psiN G D j := psiN_fixed G D j
  refine le_antisymm (psiN_le G D j _ ?_) (iSup_le hle)
  rw [psiT_iSup G D j _ ha]
  refine iSup_le fun t => ?_
  have h := le_iSup (fun t : ℕ => T^[t] 0) (t + 1)
  rw [Function.iterate_succ_apply'] at h
  exact h

/-- Nesting: `G(j)` is non-decreasing in `j`. -/
theorem FrogModel.LemmaX.psiG_mono {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) :
    Monotone (psiG G D) := by
  exact fun _ _ h => dirCount_mono D 0 (psiN_mono_left G D h)

/-- `G(0) = 0`. -/
theorem FrogModel.LemmaX.psiG_zero {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) :
    psiG G D 0 = 0 := by
  simp [psiG, psiN_zero, dirCount]

/-- `G(j)` is monotone in the child curves (Lemma 4.2 (4) of the paper). -/
theorem FrogModel.LemmaX.psiG_le_of_le {d : ℕ} (G G' : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1))
    (h : ∀ c i, G c i ≤ G' c i) (j : ℕ) : psiG G D j ≤ psiG G' D j := by
  exact dirCount_mono D 0 (psiN_le_of_le G G' D h j)
