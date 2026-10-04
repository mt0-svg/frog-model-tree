module

public import FrogModel.D3.LaneD.CheckSpec
public import FrogModel.D3.LaneD.ConvSound
public import FrogModel.D3.LaneD.SLawSound
public import FrogModel.D3.LaneD.Terms
public import FrogModel.D3.LaneD.Decode

@[expose] public section

/-!
# The terms of `Phi^S` against the tests of the check

For a part `L` of a line, with input state `S = decState L.inF L.inD` at the parameters `lnP L`:
`dTerm_sound` bounds `delta'(j)` by the deficit term the kernel computed for `j` (codes `T`, `P`,
`L`, `S2`), and `cdf_sound` bounds the terms of `F'(j, v)` by the stored value (codes `1`, `C`, `L`,
`A`, `S3`, `J`), or gives the comparison with the next stored value (code `G`).
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K Finset

/-! ## Kernel facts -/

theorem cond01_eq_true (b : Bool) (h : cond b 0 1 = 0) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

theorem row0Bad_spec (L : Line) (h : row0Bad L = 0) :
    (∀ g ≤ L.GM, slot 64 (getN L.outF 0) g = 2 ^ 52) ∧ slot 64 L.outD 0 = 2 ^ 52 := by
  have h2 := Nat.add_eq_zero_iff.1 h
  have hA : ∑ g ∈ range (L.GM + 1), cond (Nat.beq (slot 64 (getN L.outF 0) g) one52) 0 1 = 0 :=
    (natFold_add (L.GM + 1) _).symm.trans h2.1
  refine ⟨fun g hg => ?_, ?_⟩
  · have := cond01_eq_true _ ((sum_eq_zero_iff.1 hA) g (mem_range.2 (Nat.lt_succ_of_le hg)))
    exact Nat.eq_of_beq_eq_true this
  · exact Nat.eq_of_beq_eq_true (cond01_eq_true _ h2.2)

theorem inGrid_spec (GM q n : ℕ) (h : K.inGrid GM q n = true) :
    n ∈ Iface.grid GM q ∧ q < n ∧ n ≤ q + GM + 1 := by
  unfold K.inGrid at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq, Nat.add_eq,
    Nat.sub_eq, List.any_eq_true] at h
  rcases h with h | ⟨⟨h1, h2⟩, o, ho, hno⟩
  · subst h
    exact ⟨Finset.mem_insert_self _ _, by omega, le_rfl⟩
  · have hno' : n - q = o := hno
    refine ⟨Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨o, ?_, by omega⟩), h2, h1⟩
    simp only [K.gridOffsets, List.mem_cons, List.not_mem_nil, or_false] at ho
    simp only [Iface.gridOffsets, Finset.mem_insert, Finset.mem_singleton]
    exact ho

theorem findB_spec (l : List (ℕ × ℕ)) (code : ℕ) (h : (findB l code).2 = 0) :
    ∃ t ∈ l, t.1 = code ∧ (findB l code).1 = t.2 := by
  unfold findB at h ⊢
  cases hf : l.find? (fun t => Nat.beq t.1 code) with
  | none => rw [hf] at h; exact absurd h Nat.one_ne_zero
  | some t =>
    have ht := List.find?_some hf
    exact ⟨t, List.mem_of_find?_eq_some hf, Nat.eq_of_beq_eq_true ht, rfl⟩

theorem findA_spec (l : List (ℕ × ℕ × List ℕ)) (sh v : ℕ) (h : (findA l sh v).2 = 0) :
    ∃ t ∈ l, t.1 = sh ∧ bit t.2.1 v = true ∧ (findA l sh v).1 = getN t.2.2 v := by
  unfold findA at h ⊢
  cases hf : l.find? (fun t => Nat.beq t.1 sh) with
  | none => rw [hf] at h; exact absurd h Nat.one_ne_zero
  | some t =>
    rw [hf] at h
    have ht := List.find?_some hf
    exact ⟨t, List.mem_of_find?_eq_some hf, Nat.eq_of_beq_eq_true ht, cond01_eq_true _ h, rfl⟩
theorem st_envS_le (NN M q sh nh : ℕ) (Rv : ℕ → ℕ) (hq : q + sh ≤ NN) :
    envS NN M q sh nh Rv ≤ 4 ^ NN * ∑ s ∈ range (sh + 1), Rv s := by
  unfold envS
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  split_ifs
  · refine Nat.mul_le_mul_right _ ?_
    unfold envW
    refine Finset.sup_le fun m hm => om_le _ _ _ ?_
    rw [Finset.mem_Icc] at hm
    omega
  · exact Nat.zero_le _

theorem st_geom3_lt (n : ℕ) : ∑ M ∈ range n, 3 ^ M < 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

theorem envSum_lt (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c) (J : ℕ) (hJ : J ≤ c.E)
    (n : ℕ) (hn : n ≤ 3 * c.E) (q sh : ℕ) (nh : ℕ → ℕ) (hsh : sh ≤ c.GM) (hq : q + sh ≤ c.NN) :
    ∑ M ∈ Finset.range n, envS c.NN M q sh (nh M) (fun s => M.factorial * rT c.E c.GM J rows M s) < 2 ^ c.SW := by
  have hrT : ∀ M, ∑ s ∈ range (sh + 1), M.factorial * rT c.E c.GM J rows M s ≤
      (c.E - 1).factorial ^ 3 * 2 ^ 156 * 3 ^ M := by
    intro M
    rw [← Finset.mul_sum]
    refine le_trans (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset
      (Finset.range_subset_range.mpr (by omega : sh + 1 ≤ 3 * c.GM + 1)))) ?_
    exact rT_total c.E c.GM J rows hrows hJ M
  have h1 : ∑ M ∈ range n, envS c.NN M q sh (nh M) (fun s => M.factorial * rT c.E c.GM J rows M s) ≤
      ∑ M ∈ range n, 4 ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156 * 3 ^ M) :=
    Finset.sum_le_sum fun M _ => (st_envS_le _ _ _ _ _ _ hq).trans (Nat.mul_le_mul_left _ (hrT M))
  have h2 : ∑ M ∈ range n, 4 ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156 * 3 ^ M) =
      4 ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156) * ∑ M ∈ range n, 3 ^ M := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun M _ => by ring
  have h3 : ∑ M ∈ range n, 3 ^ M < 3 ^ (3 * c.E) :=
    lt_of_lt_of_le (st_geom3_lt n) (Nat.pow_le_pow_right (by norm_num) hn)
  have hA : 0 < 4 ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156) := by positivity
  have h4 : 4 ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156) * 3 ^ (3 * c.E) ≤
      (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) * 3 ^ (3 * c.E) := by
    have e1 : 4 ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156) =
        (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 156) := by
      rw [pow_add, pow_mul]; norm_num; ring
    rw [e1]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
  calc _ ≤ _ := h1
    _ = _ := h2
    _ < 4 ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156) * 3 ^ (3 * c.E) := (Nat.mul_lt_mul_left hA).mpr h3
    _ ≤ _ := h4
    _ < 2 ^ c.SW := hG

theorem fold_Icc_mono (f : ℕ → ℝ) (v GM : ℕ) (hv : v < GM) :
    (Finset.Icc v GM).fold min (f v) f ≤ (Finset.Icc (v + 1) GM).fold min (f (v + 1)) f := by
  rw [Finset.le_fold_min]
  refine ⟨(Finset.fold_min_le _).mpr (Or.inr ⟨v + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, le_rfl⟩),
    fun x hx => (Finset.fold_min_le _).mpr (Or.inr ⟨x, ?_, le_rfl⟩)⟩
  rw [Finset.mem_Icc] at hx ⊢
  omega

theorem guard_of_size (c : ConvCfg)
    (h : bad (Nat.mul (Nat.shiftLeft (Nat.mul (fact (Nat.sub c.E 1)) (Nat.mul (fact (Nat.sub c.E 1))
      (fact (Nat.sub c.E 1)))) (Nat.add (Nat.mul 2 c.NN) 172)) (Nat.pow 3 (Nat.mul 3 c.E))) (mask c.SW) = 0) :
    Guard c := by
  have h' := (bad_eq_zero _ _).mp h
  rw [mask_eq, fact_eq, Nat.shiftLeft_eq'] at h'
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq, Nat.pow_eq, Nat.shiftLeft_eq] at h'
  unfold Guard
  have h2 : 1 ≤ 2 ^ c.SW := Nat.one_le_two_pow
  have e : (c.E - 1).factorial * ((c.E - 1).factorial * (c.E - 1).factorial) = (c.E - 1).factorial ^ 3 := by ring
  rw [e] at h'
  omega

theorem split_getN (w n N x : ℕ) (hN : N < 2 ^ (w * n)) (hx : x < n) :
    getN (split w n N) x = slot w N x := by
  have hn := clog_spec n
  rw [split_eq w n N (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hn))),
    getN_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-! ## The line and its input state -/

/-- The parameters of a line. -/
def lnP (L : Line) : StParams := ⟨L.E, L.GM, L.VM, L.JM⟩

theorem one52_eq : one52 = 2 ^ 52 := by
  unfold one52
  rw [st_shl_eq, one_mul]

theorem lnDen_eq (L : Line) : lnDen L = (L.E - 1).factorial ^ 3 * 2 ^ (156 + 2 * (L.E + L.GM + 1)) := by
  unfold lnDen lnNN
  rw [st_shl_eq, fact_eq]
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  ring

theorem lnDen_pos (L : Line) : 0 < lnDen L := by
  rw [lnDen_eq]
  positivity

/-- The input rows and deficits of a well-formed input state. -/
theorem WF_slots (L : Line) (hW : (decState L.inF L.inD).WF (lnP L)) :
    RowsOK L.E L.GM L.inF ∧ (∀ k ≤ L.E, slot 64 L.inD k ≤ 2 ^ 52) ∧ slot 64 L.inD 0 = 2 ^ 52 := by
  obtain ⟨hF, hmono, hD, -, hD0⟩ := hW
  have h52 : (0 : ℝ) < 2 ^ 52 := by positivity
  refine ⟨⟨fun e he g hg => ?_, fun e he g hg => ?_⟩, fun k hk => ?_, ?_⟩
  · have h := (hF e he g hg).2
    simp only [decState] at h
    rw [div_le_one h52] at h
    show slot 64 (getN L.inF e) g ≤ 2 ^ 52
    exact_mod_cast h
  · have h := hmono e he g hg
    simp only [decState] at h
    rw [div_le_div_iff_of_pos_right h52] at h
    show slot 64 (getN L.inF e) g ≤ slot 64 (getN L.inF e) (g + 1)
    exact_mod_cast h
  · have h := (hD k hk).2
    simp only [decState] at h
    rw [div_le_one h52] at h
    exact_mod_cast h
  · simp only [decState] at hD0
    rw [div_eq_one_iff_eq h52.ne'] at hD0
    exact_mod_cast hD0

/-! ## The deficits -/

theorem deltaNew_le_dTerms (P : StParams) (S : State) (a b j : ℕ) (hj : 1 ≤ j) :
    deltaNew P S a b j ≤ dTerms P S a b j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  cases i with
  | zero => exact le_rfl
  | succ i =>
    show deltaNew P S a b (i + 2) ≤ _
    rw [deltaNew]
    exact min_le_left _ _

theorem deltaNew_succ_le (P : StParams) (S : State) (a b j : ℕ) (hj : 1 ≤ j) :
    deltaNew P S a b (j + 1) ≤ deltaNew P S a b j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  show deltaNew P S a b (i + 2) ≤ _
  rw [deltaNew]
  exact min_le_right _ _

theorem dTerms_le_T (P : StParams) (S : State) (a b j : ℕ) : dTerms P S a b j ≤ ratio a b 0 j := by
  unfold dTerms
  exact (min_le_left _ _).trans ((Finset.fold_min_le _).mpr (Or.inl le_rfl))

theorem dTerms_le_L (P : StParams) (S : State) (a b j J : ℕ) (hJ1 : 1 ≤ J) (hJ : J ≤ P.JM) :
    dTerms P S a b j ≤ (S.delta J * (1 - PB P S j J) + PB P S j J) * ratio a b J j := by
  unfold dTerms
  exact (min_le_left _ _).trans
    ((Finset.fold_min_le _).mpr (Or.inr ⟨J, Finset.mem_Icc.mpr ⟨hJ1, hJ⟩, le_rfl⟩))

theorem dTerms_le_S2 (P : StParams) (S : State) (a b j : ℕ) :
    dTerms P S a b j ≤ ∑ k ∈ range (P.E + 1), lawS2 P.GM P.E (S.F 1) (j + 1) k * Dt S a b j k := by
  unfold dTerms
  exact min_le_right _ _

/-- The code of a (B) family: `J + 2^16 sh`. -/
theorem famCode_spec (J sh : ℕ) (hJ : J < 65536) :
    Nat.shiftRight (Nat.add J (Nat.shiftLeft sh 16)) 16 = sh ∧
      Nat.land (Nat.add J (Nat.shiftLeft sh 16)) 65535 = J := by
  simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.add_eq, st_shl_eq]
  constructor
  · rw [Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  · rw [show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    norm_num
    omega

/-- The (B) vector of a family the kernel found. -/
theorem vB_find (L : Line) (J sh : ℕ) (hJ16 : J < 65536)
    (hfb : (findB (lnVB L) (Nat.add J (Nat.shiftLeft sh 16))).2 = 0) :
    (findB (lnVB L) (Nat.add J (Nat.shiftLeft sh 16))).1 =
      famB (lnC L) sh (lnOms L) (mkTab (lnC L) (lnX L) (lnQ L) J) := by
  obtain ⟨t, ht, ht1, hfb1⟩ := findB_spec _ _ hfb
  obtain ⟨f, -, rfl⟩ := List.mem_map.mp ht
  rw [hfb1]
  have hf : f = Nat.add J (Nat.shiftLeft sh 16) := ht1
  obtain ⟨hc1, hc2⟩ := famCode_spec J sh hJ16
  show famB (lnC L) (Nat.shiftRight f 16) (lnOms L) (mkTab (lnC L) (lnX L) (lnQ L) (Nat.land f 65535)) = _
  rw [hf, hc1, hc2]

theorem famB_main (L : Line) (hrows : RowsOK L.E L.GM L.inF) (hG : Guard (lnC L)) (j : ℕ) (hj1 : 1 ≤ j)
    (hjE : j ≤ L.E) (J : ℕ) (hJ1 : 1 ≤ J) (hJE : J ≤ L.E) (sh : ℕ) (hsh : sh ≤ L.GM) :
    slot (lnC L).SW (famB (lnC L) sh (lnOms L) (mkTab (lnC L) (lnX L) (lnQ L) J)) (Nat.sub (lnC L).Q0 (j + 1)) =
      ∑ M ∈ range (J + 2 * L.E - 2), envS (L.E + L.GM + 1) M (j + 1) sh
        (L.E + L.GM + 1) (fun s => M.factorial * rT L.E L.GM J L.inF M s) := by
  have hQ0 : (lnC L).Q0 = L.E + 1 := rfl
  have hNN : (lnC L).NN = L.E + L.GM + 1 := rfl
  have h1 := famB_eq (lnC L) L.inF hrows hG J hJ1 hJE sh hsh
  have h2 : famB (lnC L) sh (lnOms L) (mkTab (lnC L) (lnX L) (lnQ L) J) =
      famB (lnC L) sh (omRows (lnC L).SW (lnC L).NN (3 * (lnC L).E - 2))
        (mkTab (lnC L) (buildX (lnC L) L.inF) (sqQ (lnC L) (buildX (lnC L) L.inF)) J) := rfl
  rw [h2, h1, slot_pk]
  · rw [ite_eq_left (by rw [hQ0]; change L.E + 1 - (j + 1) < L.E; omega), hQ0, hNN]
    have hq : L.E + 1 - Nat.sub (L.E + 1) (j + 1) = j + 1 := by
      change L.E + 1 - (L.E + 1 - (j + 1)) = j + 1; omega
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [hq]
    rfl
  · intro t ht
    exact envSum_lt (lnC L) L.inF hrows hG J hJE _ (by change J + 2 * L.E - 2 ≤ 3 * L.E; omega) _ _
      (fun _ => (lnC L).NN) hsh (by rw [hQ0, hNN]; change t < L.E at ht; omega)

/-- `P_B(j, J)` is at most the (B) bound at a cut `K` the kernel checked. -/
theorem PB_le (L : Line) (hOK : (lnP L).OK) (hW : (decState L.inF L.inD).WF (lnP L))
    (hG : Guard (lnC L)) (j : ℕ) (hj1 : 1 ≤ j) (hjE : j ≤ L.E) (J K : ℕ) (hJ1 : 1 ≤ J) (hJM : J ≤ L.JM)
    (hJ16 : J < 65536) (hK : inGrid L.GM (j + 1) K = true)
    (hfb : (findB (lnVB L) (Nat.add J (Nat.shiftLeft (Nat.sub (Nat.sub K (j + 1)) 1) 16))).2 = 0) :
    PB (lnP L) (decState L.inF L.inD) j J ≤
      (slot (lnC L).SW (findB (lnVB L) (Nat.add J (Nat.shiftLeft (Nat.sub (Nat.sub K (j + 1)) 1) 16))).1
          (Nat.sub (lnC L).Q0 (j + 1)) : ℝ) / (lnDen L : ℝ) +
        2 * binGe (L.E + J - 1) (1 / 2) L.E * ((slot 64 (getN L.inF L.E) (K - (j + 1) - 1) : ℝ) / 2 ^ 52) +
        binLt K (1 / 4) J := by
  obtain ⟨hgrid, hqK, hKq⟩ := inGrid_spec _ _ _ hK
  obtain ⟨hrows, -, -⟩ := WF_slots L hW
  have hJE : J ≤ L.E := hJM.trans hOK.2.1
  have hsh : K - (j + 1) - 1 ≤ L.GM := by omega
  rw [vB_find L J _ hJ16 hfb]
  rw [famB_main L hrows hG j hj1 hjE J hJ1 hJE (Nat.sub (Nat.sub K (j + 1)) 1) hsh, lnDen_eq]
  have hPB : PB (lnP L) (decState L.inF L.inD) j J ≤
      boundB (decState L.inF L.inD).F L.E L.GM (j + 1) J K :=
    Finset.inf'_le (fun K => boundB (decState L.inF L.inD).F L.E L.GM (j + 1) J K) hgrid
  unfold boundB at hPB
  rw [boundB_main L.E L.GM L.inF hrows (decState L.inF L.inD).F (fun e _ g _ => rfl) (j + 1) J K
    (by omega) hJ1 hJE hqK hsh] at hPB
  push_cast
  exact hPB

/-- The deficit term `L` in integers: `L_arith` and `B_val` in the kernel's form. -/
theorem L_kernel (main DenB nF nJ E J K rN dd : ℕ) (PB δ : ℝ) (hJ : 1 ≤ J) (hDen : 0 < DenB)
    (hdd : 0 < dd) (hnJ : nJ ≤ 2 ^ 52) (hδ : δ = (nJ : ℝ) / 2 ^ 52)
    (hPB : PB ≤ (main : ℝ) / DenB + 2 * binGe (E + J - 1) (1 / 2) E * ((nF : ℝ) / 2 ^ 52) +
      binLt K (1 / 4) J) :
    (δ * (1 - PB) + PB) * ((rN : ℝ) / dd) ≤
      (cdiv (Nat.shiftLeft (Nat.mul (Nat.add (Nat.mul nJ (Nat.shiftLeft DenB
          (Nat.add (Nat.add (Nat.sub (Nat.add E J) 1) 52) (Nat.mul 2 K))))
        (Nat.mul (Nat.add (Nat.add (Nat.shiftLeft main
            (Nat.add (Nat.add (Nat.sub (Nat.add E J) 1) 52) (Nat.mul 2 K)))
          (Nat.shiftLeft (Nat.mul (Nat.mul 2 (binSum (Nat.sub (Nat.add E J) 1) (Nat.sub J 1)))
            (Nat.mul nF DenB)) (Nat.mul 2 K)))
          (Nat.shiftLeft (Nat.mul (binLt4 K J) DenB) (Nat.add (Nat.sub (Nat.add E J) 1) 52)))
          (Nat.sub one52 nJ))) rN) 76)
        (Nat.mul (Nat.shiftLeft DenB (Nat.add (Nat.add (Nat.sub (Nat.add E J) 1) 52) (Nat.mul 2 K))) dd) :
          ℝ) / 2 ^ 128 := by
  subst hδ
  have hB := B_val main DenB nF E J K hJ hDen
  simp only [st_shl_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, one52_eq]
  exact L_arith nJ _ _ rN dd _ PB hnJ (by positivity) hdd hPB (le_of_eq hB.symm)

/-- The S2 term in integers. -/
theorem s2row_eq (L : Line) (j : ℕ) (hj1 : 1 ≤ j) (hb0 : bit L.mask 0 = true) :
    getN (lnS2 L) (Nat.sub j 1) = getN (s2Laws WL L.E L.GM (getN L.inF 1)) (j + 1) := by
  unfold lnS2
  rw [hb0, Bool.cond_true]
  change getN (dropN 2 (s2Laws WL L.E L.GM (getN L.inF 1))) (j - 1) = _
  rw [st_getN_dropN, show 2 + (j - 1) = j + 1 by omega]

theorem s2row_law (L : Line) (hW : (decState L.inF L.inD).WF (lnP L)) (hE64 : L.E ≤ 64)
    (hG256 : L.GM ≤ 256) (hE1 : 1 ≤ L.E) (j : ℕ) (hj1 : 1 ≤ j) (hjE : j ≤ L.E)
    (hb0 : bit L.mask 0 = true) (k : ℕ) (hk : k < L.E + 1) :
    lawS2 L.GM L.E ((decState L.inF L.inD).F 1) (j + 1) k ≤
      ((split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.E 1) (getN (lnS2 L) (Nat.sub j 1))).getD k 0 : ℝ) /
        2 ^ 64 := by
  obtain ⟨hrows, -, -⟩ := WF_slots L hW
  have hmono : ∀ g < L.GM, slot 64 (getN L.inF 1) g ≤ slot 64 (getN L.inF 1) (g + 1) :=
    fun g hg => hrows.2 1 hE1 g hg
  have htop : slot 64 (getN L.inF 1) L.GM ≤ 2 ^ 52 := hrows.1 1 hE1 L.GM le_rfl
  have hlt := s2Laws_lt L.E L.GM (getN L.inF 1) hmono htop (j + 1) (by omega)
  rw [s2row_eq L j hj1 hb0, ← getN_eq]
  have hb : getN (s2Laws WL L.E L.GM (getN L.inF 1)) (j + 1) < 2 ^ (Nat.add (Nat.mul 2 WL) 8 * Nat.add L.E 1) :=
    hlt
  rw [split_getN _ _ _ _ hb hk]
  have := s2Laws_sound L.E L.GM (getN L.inF 1) ((decState L.inF L.inD).F 1) (fun g _ => rfl) hmono htop
    hE64 hG256 (j + 1) k (by omega) (by omega)
  exact this

theorem delta_dec (L : Line) (hW : (decState L.inF L.inD).WF (lnP L)) (k : ℕ) :
    (decState L.inF L.inD).delta k = ((cond (Nat.beq k 0) one52 (slot 64 L.inD k) : ℕ) : ℝ) / 2 ^ 52 := by
  obtain ⟨-, -, hD0⟩ := WF_slots L hW
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · show (slot 64 L.inD 0 : ℝ) / 2 ^ 52 = ((cond (Nat.beq 0 0) one52 (slot 64 L.inD 0) : ℕ) : ℝ) / 2 ^ 52
    rw [hD0, show Nat.beq 0 0 = true from rfl, Bool.cond_true, one52_eq]
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl

theorem S2_sound (L : Line) (hW : (decState L.inF L.inD).WF (lnP L)) (hE64 : L.E ≤ 64)
    (hG256 : L.GM ≤ 256) (hE1 : 1 ≤ L.E) (j : ℕ) (hj1 : 1 ≤ j) (hjE : j ≤ L.E)
    (hb0 : bit L.mask 0 = true) :
    ∑ k ∈ range (L.E + 1), lawS2 L.GM L.E ((decState L.inF L.inD).F 1) (j + 1) k *
        Dt (decState L.inF L.inD) L.a L.b j k ≤
      (cdiv (Nat.shiftLeft (natFold (Nat.add L.E 1)
          (0, 0, split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.E 1) (getN (lnS2 L) (Nat.sub j 1)))
          (fun k (st : ℕ × ℕ × List ℕ) =>
            let x := Nat.mul (cond (Nat.beq k 0) one52 (slot 64 L.inD k)) (ratioN L.a L.b k j)
            let dt := cond (Nat.beq k 0) x (minN st.2.1 x)
            (Nat.add st.1 (Nat.mul (hd st.2.2) dt), dt, tl st.2.2))).1 128)
        (Nat.shiftLeft (ratioD L.a L.b j) (Nat.add WL 52)) : ℝ) / 2 ^ 128 := by
  set s2row := split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.E 1) (getN (lnS2 L) (Nat.sub j 1)) with hs2row
  have hfold := runmin_fold (Nat.add L.E 1)
    (fun k => Nat.mul (cond (Nat.beq k 0) one52 (slot 64 L.inD k)) (ratioN L.a L.b k j)) s2row
  rw [hfold]
  have hDt : ∀ k, Dt (decState L.inF L.inD) L.a L.b j k =
      (((range (k + 1)).inf' nonempty_range_add_one (fun k' =>
        Nat.mul (cond (Nat.beq k' 0) one52 (slot 64 L.inD k')) (ratioN L.a L.b k' j)) : ℕ) : ℝ) /
        (2 ^ 52 * ratioD L.a L.b j) :=
    fun k => Dt_eq _ _ _ _ _ (fun k' => cond (Nat.beq k' 0) one52 (slot 64 L.inD k'))
      (fun k' _ => delta_dec L hW k')
  simp only [hDt]
  have hdd : 0 < ratioD L.a L.b j := by unfold ratioD; simp only [Nat.mul_eq, Nat.add_eq]; positivity
  have key := S2_arith (L.E + 1) (ratioD L.a L.b j) hdd (fun k => s2row.getD k 0)
    (fun k => (range (k + 1)).inf' nonempty_range_add_one (fun k' =>
        Nat.mul (cond (Nat.beq k' 0) one52 (slot 64 L.inD k')) (ratioN L.a L.b k' j)))
    (fun k => lawS2 L.GM L.E ((decState L.inF L.inD).F 1) (j + 1) k)
    (fun k hk => s2row_law L hW hE64 hG256 hE1 j hj1 hjE hb0 k hk)
  rw [st_shl_eq, st_shl_eq]
  convert key using 4
  simp only [WL]

/-- **The deficit term** of `j` bounds `delta'(j)`. -/
theorem dTerm_sound (L : Line) (hOK : (lnP L).OK) (hE64 : L.E ≤ 64) (hG256 : L.GM ≤ 256)
    (hW : (decState L.inF L.inD).WF (lnP L)) (hG : Guard (lnC L)) (j : ℕ) (hj1 : 1 ≤ j)
    (hjE : j ≤ L.E) (hdo : doDef L j = true) (h2 : (dTerm L j (getN (lnS2 L) (j - 1))).2 = 0)
    (hprev : 2 ≤ j → deltaNew (lnP L) (decState L.inF L.inD) L.a L.b (j - 1) ≤
      (slot 128 L.uD (j - 1) : ℝ) / 2 ^ 128) :
    deltaNew (lnP L) (decState L.inF L.inD) L.a L.b j ≤
      ((dTerm L j (getN (lnS2 L) (j - 1))).1 : ℝ) / 2 ^ 128 := by
  have hD := deltaNew_le_dTerms (lnP L) (decState L.inF L.inD) L.a L.b j hj1
  obtain ⟨-, hDs, -⟩ := WF_slots L hW
  have hdd : 0 < ratioD L.a L.b j := by unfold ratioD; simp only [Nat.mul_eq, Nat.add_eq]; positivity
  unfold dTerm deficitTerm at h2 ⊢
  unfold doDef at hdo
  dsimp only at h2 hdo ⊢
  revert h2 hdo
  generalize slot 64 L.dn j = nm
  cases hc1 : Nat.beq (Nat.land nm 255) 1
  swap
  · intro _ _
    exact hD.trans ((dTerms_le_T _ _ _ _ _).trans (T_bound _ _ _))
  cases hc2 : Nat.beq (Nat.land nm 255) 2
  swap
  · intro _ h2
    dsimp only [Bool.cond_true, Bool.cond_false] at h2 ⊢
    have h2j : 2 ≤ j := (bad_eq_zero _ _).mp h2
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact (deltaNew_succ_le _ _ _ _ i (by omega)).trans (hprev h2j)
  cases hc3 : Nat.beq (Nat.land nm 255) 3
  swap
  · intro _ h2
    dsimp only [Bool.cond_true, Bool.cond_false] at h2 ⊢
    have hJle : Nat.land (Nat.shiftRight nm 8) 65535 ≤ 65535 := by
      rw [Nat.land_eq]; exact Nat.and_le_right
    generalize Nat.land (Nat.shiftRight nm 8) 65535 = J at h2 hJle ⊢
    generalize Nat.shiftRight nm 24 = K at h2 ⊢
    obtain ⟨hfb, hok0⟩ := Nat.add_eq_zero_iff.mp h2
    have hok := cond01_eq_true _ hok0
    simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨⟨hJ1, hJM⟩, hKg⟩ := hok
    refine hD.trans ((dTerms_le_L _ _ _ _ _ J hJ1 hJM).trans ?_)
    rw [ratio_eq]
    exact L_kernel _ (lnDen L) _ (slot 64 L.inD J) L.E J K (ratioN L.a L.b J j) (ratioD L.a L.b j) _ _
      hJ1 (lnDen_pos L) hdd (hDs J (hJM.trans hOK.2.1)) rfl
      (PB_le L hOK hW hG j hj1 hjE J K hJ1 hJM (by omega) hKg hfb)
  cases hc4 : Nat.beq (Nat.land nm 255) 4
  swap
  · intro hdo _
    dsimp only [Bool.cond_true, Bool.cond_false] at hdo ⊢
    exact hD.trans ((dTerms_le_S2 _ _ _ _ _).trans (S2_sound L hW hE64 hG256 hOK.1 j hj1 hjE hdo))
  · intro _ h2
    dsimp only [Bool.cond_true, Bool.cond_false] at h2
    exact absurd h2 (by decide)

/-- The (A) vector of a cut the kernel found. -/
theorem famA_main (L : Line) (hrows : RowsOK L.E L.GM L.inF) (hG : Guard (lnC L)) (j : ℕ)
    (hj1 : 1 ≤ j) (hjE : j ≤ L.E) (sh : ℕ) (hsh : sh ≤ L.GM) (v : ℕ) (hv : v ≤ L.VM)
    (hfa : (findA (lnVA L) sh v).2 = 0) :
    slot (lnC L).SW (findA (lnVA L) sh v).1 (Nat.sub (lnC L).Q0 (j + 1)) =
      ∑ M ∈ range (3 * L.E - 2), envS (L.E + L.GM + 1) M (j + 1) sh (M + v)
        (fun s => M.factorial * rT L.E L.GM L.E L.inF M s) := by
  obtain ⟨t, ht, ht1, htb, hfa1⟩ := findA_spec _ _ _ hfa
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp ht
  dsimp only at ht1 htb hfa1
  subst ht1
  rw [hfa1]
  have hQ0 : (lnC L).Q0 = L.E + 1 := rfl
  have hNN : (lnC L).NN = L.E + L.GM + 1 := rfl
  have h1 := famA_eq (lnC L) L.inF hrows hG L.VM p.1 p.2 hsh v hv
  rw [ite_eq_left htb] at h1
  have h2 : getN (famA (lnC L) L.VM p.1 p.2 (lnOms L) (mkTab (lnC L) (lnX L) (lnQ L) L.E)) v =
      getN (famA (lnC L) L.VM p.1 p.2 (omRows (lnC L).SW (lnC L).NN (3 * (lnC L).E - 2))
        (mkTab (lnC L) (buildX (lnC L) L.inF) (sqQ (lnC L) (buildX (lnC L) L.inF)) (lnC L).E)) v := rfl
  rw [h2, h1, slot_pk]
  · rw [ite_eq_left (by rw [hQ0]; change L.E + 1 - (j + 1) < L.E; omega), hQ0, hNN]
    have hq : L.E + 1 - Nat.sub (L.E + 1) (j + 1) = j + 1 := by
      change L.E + 1 - (L.E + 1 - (j + 1)) = j + 1; omega
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [hq]
    rfl
  · intro t ht
    exact envSum_lt (lnC L) L.inF hrows hG (lnC L).E le_rfl _ (by change 3 * L.E - 2 ≤ 3 * L.E; omega)
      _ _ (fun M => M + v) hsh (by rw [hQ0, hNN]; change t < L.E at ht; omega)
/-- `P_A(j, v)` is at most the (A) bound at a cut `n0` the kernel checked. -/
theorem PA_le (L : Line) (hOK : (lnP L).OK) (hW : (decState L.inF L.inD).WF (lnP L))
    (hG : Guard (lnC L)) (j : ℕ) (hj1 : 1 ≤ j) (hjE : j ≤ L.E) (v n0 : ℕ) (hv : v ≤ L.VM)
    (hK : inGrid L.GM (j + 1) n0 = true)
    (hfa : (findA (lnVA L) (Nat.sub (Nat.sub n0 (j + 1)) 1) v).2 = 0) :
    PA (lnP L) (decState L.inF L.inD) j v ≤
      (slot (lnC L).SW (findA (lnVA L) (Nat.sub (Nat.sub n0 (j + 1)) 1) v).1
          (Nat.sub (lnC L).Q0 (j + 1)) : ℝ) / (lnDen L : ℝ) +
        3 * binGe (L.E + v) (1 / 2) L.E * ((slot 64 (getN L.inF L.E) (n0 - (j + 1) - 1) : ℝ) / 2 ^ 52) +
        binCdf n0 (1 / 4) v := by
  obtain ⟨hgrid, hqK, hKq⟩ := inGrid_spec _ _ _ hK
  obtain ⟨hrows, -, -⟩ := WF_slots L hW
  have hsh : n0 - (j + 1) - 1 ≤ L.GM := by omega
  rw [famA_main L hrows hG j hj1 hjE (Nat.sub (Nat.sub n0 (j + 1)) 1) hsh v hv hfa, lnDen_eq]
  have hPA : PA (lnP L) (decState L.inF L.inD) j v ≤
      boundA (decState L.inF L.inD).F L.E L.GM (j + 1) v n0 :=
    Finset.inf'_le (fun n0 => boundA (decState L.inF L.inD).F L.E L.GM (j + 1) v n0) hgrid
  unfold boundA at hPA
  rw [boundA_main L.E L.GM L.inF hrows (decState L.inF L.inD).F (fun e _ g _ => rfl) (j + 1) v n0
    (by omega) hOK.1 hqK hsh] at hPA
  push_cast
  exact hPA

/-- The cdf term `A` in integers. -/
theorem A_kernel (main DenA nF nF' E v n0 : ℕ) (hDen : 0 < DenA)
    (h : bad (Nat.add (Nat.add (Nat.shiftLeft main (Nat.add (Nat.add (Nat.add E v) 52) (Nat.mul 2 n0)))
        (Nat.shiftLeft (Nat.mul (Nat.mul 3 (binSum (Nat.add E v) v)) (Nat.mul nF DenA)) (Nat.mul 2 n0)))
      (Nat.shiftLeft (Nat.mul (binCdfN n0 v 3) DenA) (Nat.add (Nat.add E v) 52)))
      (Nat.shiftLeft (Nat.mul nF' DenA) (Nat.add (Nat.sub (Nat.add (Nat.add E v) 52) 52) (Nat.mul 2 n0))) = 0) :
    (main : ℝ) / DenA + 3 * binGe (E + v) (1 / 2) E * ((nF : ℝ) / 2 ^ 52) + binCdf n0 (1 / 4) v ≤
      (nF' : ℝ) / 2 ^ 52 := by
  have h' := (bad_eq_zero _ _).mp h
  simp only [st_shl_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, Nat.add_sub_cancel] at h'
  exact A_arith main DenA nF nF' E v n0 hDen h'

theorem preF_le_C (P : StParams) (S : State) (a b j v : ℕ) (prev : ℝ) :
    preF P S a b j v prev ≤ binCdf j (1 / 3) v :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem preF_le_L (P : StParams) (S : State) (a b j v : ℕ) (prev : ℝ) :
    preF P S a b j v prev ≤ L12 (deltaNew P S a b j * mu (a + 1) j) (mu (a + 1) j) v :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem preF_le_A (P : StParams) (S : State) (a b j v : ℕ) (prev : ℝ) :
    preF P S a b j v prev ≤ if v ≤ P.VM then PA P S j v else 1 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem preF_le_S3 (P : StParams) (S : State) (a b j v : ℕ) (prev : ℝ) :
    preF P S a b j v prev ≤ cdfS3 P.GM (S.F 1) (j + 1) v :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem preF_le_prev (P : StParams) (S : State) (a b j v : ℕ) (prev : ℝ) :
    preF P S a b j v prev ≤ prev :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem preF_le_one (P : StParams) (S : State) (a b j v : ℕ) (prev : ℝ) : preF P S a b j v prev ≤ 1 :=
  (preF_le_C P S a b j v prev).trans (binCdf_le_one j v _ (by norm_num) (by norm_num))

theorem le_of_one52 (x : ℝ) (hx : x ≤ 1) (n : ℕ) (h : bad one52 n = 0) : x ≤ (n : ℝ) / 2 ^ 52 := by
  have h' := (bad_eq_zero _ _).mp h
  rw [one52_eq] at h'
  refine hx.trans ?_
  rw [le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast h'

theorem mu_succ_eq (a j : ℕ) : mu (a + 1) j = ((Nat.add (Nat.add a 2) j : ℕ) : ℝ) / 3 := by
  unfold mu
  simp only [Nat.add_eq]
  push_cast
  ring

/-- **The cdf terms** of `(j, v)` against the stored value `nF'`: the terms other than `G` bound
`F'(j, v)` before the minimum over `v' ≥ v`; `G` compares with the next stored value. -/
theorem cdf_sound (L : Line) (hOK : (lnP L).OK) (hW : (decState L.inF L.inD).WF (lnP L))
    (hG : Guard (lnC L)) (j : ℕ) (hj1 : 1 ≤ j) (hjE : j ≤ L.E) (v : ℕ) (hdo : doCdf L j v = true)
    (U nF' nPrev nNext cum : ℕ) (h : cdfTerm L (lnC L) (lnDen L) (lnVA L) U j v nF' nPrev nNext cum = 0)
    (hU : deltaNew (lnP L) (decState L.inF L.inD) L.a L.b j ≤ (U : ℝ) / 2 ^ 128)
    (hrho : bit L.mask 2 = true → (L.a + 2 + j) * 2 ^ 256 ≤ 3 * (slot 256 L.sq j * slot 256 L.sq j))
    (hcum : bit L.mask 2 = true →
      cdfS3 L.GM ((decState L.inF L.inD).F 1) (j + 1) v ≤ (cum : ℝ) / 2 ^ WL)
    (prev : ℝ) (hprev : prev ≤ (nPrev : ℝ) / 2 ^ 52) :
    preF (lnP L) (decState L.inF L.inD) L.a L.b j v prev ≤ (nF' : ℝ) / 2 ^ 52 ∨ nNext ≤ nF' := by
  have h52 : (0 : ℝ) < 2 ^ 52 := by positivity
  unfold cdfTerm at h
  unfold doCdf at hdo
  dsimp only at h hdo
  revert h hdo
  generalize slot 32 (getN L.fn j) v = nm
  cases hc0 : Nat.beq (Nat.land nm 255) 0
  swap
  · intro _ h
    dsimp only [Bool.cond_true, Bool.cond_false] at h
    exact Or.inl (le_of_one52 _ (preF_le_one _ _ _ _ _ _ _) _ h)
  cases hc1 : Nat.beq (Nat.land nm 255) 1
  swap
  · intro _ h
    dsimp only [Bool.cond_true, Bool.cond_false] at h
    have h' := (bad_eq_zero _ _).mp h
    simp only [st_shl_eq, Nat.mul_eq, Nat.pow_eq] at h'
    refine Or.inl ((preF_le_C _ _ _ _ _ _ _).trans ?_)
    rw [binCdf_third, div_le_div_iff₀ (by positivity) h52]
    exact_mod_cast h'
  cases hc2 : Nat.beq (Nat.land nm 255) 2
  swap
  · intro hdo h
    have hc4 : Nat.beq (Nat.land nm 255) 4 = false := by rw [Nat.eq_of_beq_eq_true hc2]; rfl
    rw [hc4] at hdo
    dsimp only [Bool.cond_true, Bool.cond_false] at h hdo
    refine Or.inl ((preF_le_L _ _ _ _ _ _ _).trans ?_)
    revert h
    cases hv : Nat.blt (Nat.mul 3 (Nat.add v 1)) (Nat.add (Nat.add L.a 2) j)
    · intro h
      dsimp only [Bool.cond_true, Bool.cond_false] at h
      refine le_of_one52 _ ?_ _ h
      unfold L12
      exact (min_le_right _ _).trans (Finset.fold_min_le _ |>.mpr (Or.inl le_rfl))
    · intro h
      dsimp only [Bool.cond_true, Bool.cond_false] at h
      have hc := (bad_eq_zero _ _).mp h
      simp only [st_shl_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq] at hc
      have hv' : 3 * (v + 1) < L.a + 2 + j := by
        have := Nat.blt_eq.mp hv
        simpa only [Nat.mul_eq, Nat.add_eq] using this
      have hr := hrho hdo
      unfold L12
      refine (min_le_left _ _).trans ?_
      rw [mu_succ_eq]
      refine lemma12B_check (Nat.add (Nat.add L.a 2) j) v U (slot 256 L.sq j) nF' _ ?_ (by
        simp only [Nat.add_eq]; rw [sq]; exact hr) (by simpa only [Nat.add_eq] using hv') (by
        simpa only [Nat.add_eq] using hc)
      rw [← mu_succ_eq]
      exact mul_le_mul_of_nonneg_right hU (by unfold mu; positivity)
  cases hc4 : Nat.beq (Nat.land nm 255) 4
  swap
  · intro _ h
    dsimp only [Bool.cond_true, Bool.cond_false] at h
    obtain ⟨h12, hok0⟩ := Nat.add_eq_zero_iff.mp h
    obtain ⟨hbad, hfa⟩ := Nat.add_eq_zero_iff.mp h12
    have hok := cond01_eq_true _ hok0
    simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨hvV, hKg⟩ := hok
    refine Or.inl ((preF_le_A _ _ _ _ _ _ _).trans ?_)
    rw [ite_eq_left (show v ≤ (lnP L).VM from hvV)]
    exact (PA_le L hOK hW hG j hj1 hjE v _ hvV hKg hfa).trans
      (A_kernel _ _ _ nF' L.E v _ (lnDen_pos L) hbad)
  cases hc5 : Nat.beq (Nat.land nm 255) 5
  swap
  · intro hdo h
    dsimp only [Bool.cond_true, Bool.cond_false] at h hdo
    have h' := (bad_eq_zero _ _).mp h
    simp only [st_shl_eq, WL] at h'
    refine Or.inl ((preF_le_S3 _ _ _ _ _ _ _).trans ((hcum hdo).trans ?_))
    rw [WL, div_le_div_iff₀ (by positivity) h52]
    exact_mod_cast h'
  cases hc6 : Nat.beq (Nat.land nm 255) 6
  swap
  · intro _ h
    dsimp only [Bool.cond_true, Bool.cond_false] at h
    have h' := (bad_eq_zero _ _).mp h
    refine Or.inl ((preF_le_prev _ _ _ _ _ _ _).trans (hprev.trans ?_))
    exact div_le_div_of_nonneg_right (by exact_mod_cast h') h52.le
  cases hc7 : Nat.beq (Nat.land nm 255) 7
  swap
  · intro _ h
    dsimp only [Bool.cond_true, Bool.cond_false] at h
    exact Or.inr ((bad_eq_zero _ _).mp h)
  · intro _ h
    dsimp only [Bool.cond_true, Bool.cond_false] at h
    exact absurd h (by decide)

end FrogModel.D3.LaneD
