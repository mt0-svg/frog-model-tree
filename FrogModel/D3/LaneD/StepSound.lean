module

public import FrogModel.D3.LaneD.StepTerms

@[expose] public section

/-!
# Soundness of the step check

`step_sound`: if every part of a line passes the kernel check and the parts cover the line, the
stored output state is at least `Phi^S` (children heights `a..b`) of the stored input state, and
it has the shape of a state. This gives `CertStep.plain` (at `a = b = h`) and the final check
`(phiS P hn b T).Le P T` (a line whose input and output are the same state `T`).

The deficits by induction on `j` (`dTerm_sound`, the term `P` reading `U(j - 1)`); the cdf rows by
induction on `j` and, in a row, on `v` downwards (`cdf_sound`, the term `G` reading the entry
`v + 1`); the shape of the output from the shape tests of the parts with bit 2.
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K Finset

theorem s3row_eq (L : Line) (j : ℕ) (hj1 : 1 ≤ j) (hb2 : bit L.mask 2 = true) :
    getN (lnS3 L) (j - 1) = getN (s3Laws WL L.E L.GM (getN L.inF 1)) (j + 1) := by
  unfold lnS3
  rw [hb2, Bool.cond_true]
  change getN (dropN 2 (s3Laws WL L.E L.GM (getN L.inF 1))) (j - 1) = _
  rw [st_getN_dropN, show 2 + (j - 1) = j + 1 by omega]

/-- The S3 partial sum the kernel reads bounds `P(X'' ≤ v)`. -/
theorem s3_cum (L : Line) (hW : (decState L.inF L.inD).WF (lnP L)) (hE64 : L.E ≤ 64)
    (hG256 : L.GM ≤ 256) (hE1 : 1 ≤ L.E) (j : ℕ) (hj1 : 1 ≤ j) (hjE : j ≤ L.E)
    (hb2 : bit L.mask 2 = true) (v : ℕ) (hv : v ≤ L.GM) :
    cdfS3 L.GM ((decState L.inF L.inD).F 1) (j + 1) v ≤
      ((∑ x ∈ range (v + 1), getN (split (2 * WL + 8) (L.GM + 2) (getN (lnS3 L) (j - 1))) x : ℕ) : ℝ) /
        2 ^ WL := by
  obtain ⟨hrows, -, -⟩ := WF_slots L hW
  have hmono : ∀ g < L.GM, slot 64 (getN L.inF 1) g ≤ slot 64 (getN L.inF 1) (g + 1) :=
    fun g hg => hrows.2 1 hE1 g hg
  have htop : slot 64 (getN L.inF 1) L.GM ≤ 2 ^ 52 := hrows.1 1 hE1 L.GM le_rfl
  have hlt := s3Laws_lt L.E L.GM (getN L.inF 1) hmono htop (j + 1) (by omega)
  rw [s3row_eq L j hj1 hb2]
  have hs : ∀ x ∈ range (v + 1), getN (split (2 * WL + 8) (L.GM + 2)
      (getN (s3Laws WL L.E L.GM (getN L.inF 1)) (j + 1))) x =
      slot (2 * WL + 8) (getN (s3Laws WL L.E L.GM (getN L.inF 1)) (j + 1)) x :=
    fun x hx => split_getN _ _ _ _ hlt (by rw [mem_range] at hx; omega)
  rw [sum_congr rfl hs]
  push_cast
  exact s3Laws_sound L.E L.GM (getN L.inF 1) _ (fun g _ => rfl) hmono htop hE64 hG256 (j + 1) v
    (by omega) hv

theorem Fnew_le_pre (P : StParams) (S : State) (a b j v : ℕ) :
    Fnew P S a b (j + 1) v ≤ preF P S a b (j + 1) v (Fnew P S a b j v) := by
  show (Finset.Icc v P.GM).fold min _ _ ≤ _
  exact (Finset.fold_min_le _).mpr (Or.inl le_rfl)

theorem Fnew_mono (P : StParams) (S : State) (a b j v : ℕ) (hv : v < P.GM) :
    Fnew P S a b (j + 1) v ≤ Fnew P S a b (j + 1) (v + 1) :=
  fold_Icc_mono (fun v' => preF P S a b (j + 1) v' (Fnew P S a b j v')) v P.GM hv

/-- The term `G`: the stored entry `v` is at least the stored entry `v + 1` (or at least `1` at
`v = GM`). -/
theorem G_case (L : Line) (j v : ℕ) (hv : v ≤ L.GM) (X : ℝ) (hX1 : X ≤ 1)
    (hnext : v < L.GM → X ≤ (slot 64 (getN L.outF j) (v + 1) : ℝ) / 2 ^ 52)
    (hres : cond (Nat.beq v L.GM) one52 (slot 64 (getN L.outF j) (v + 1)) ≤ slot 64 (getN L.outF j) v) :
    X ≤ (slot 64 (getN L.outF j) v : ℝ) / 2 ^ 52 := by
  revert hres
  cases hc : Nat.beq v L.GM
  · intro hres
    rw [Bool.cond_false] at hres
    have hvG : v < L.GM := by
      rcases Nat.lt_or_ge v L.GM with h | h
      · exact h
      · have h1 : Nat.beq v L.GM = true := by rw [show v = L.GM by omega]; exact Nat.beq_refl _
        rw [hc] at h1
        exact absurd h1 Bool.false_ne_true
    refine (hnext hvG).trans ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast hres) (by positivity)
  · intro hres
    rw [Bool.cond_true] at hres
    exact le_of_one52 X hX1 _ ((bad_eq_zero _ _).mpr hres)

/-- **Soundness of the step check.** -/
theorem step_sound (P : StParams) (a b : ℕ) (L : Line) (ps : List Part)
    (hE : L.E = P.E) (hGM : L.GM = P.GM) (hVM : L.VM = P.VM) (hJM : L.JM = P.JM)
    (ha : L.a = a) (hb : L.b = b) (hP : P.OK) (hE64 : P.E ≤ 64) (hG256 : P.GM ≤ 256)
    (hW : (decState L.inF L.inD).WF P)
    (hchk : ∀ p ∈ ps, check (L.withPart p) = true) (hcov : covers L ps = true) :
    (phiS P a b (decState L.inF L.inD)).Le P (decState L.outF L.outD) ∧
      (decState L.outF L.outD).WF P := by
  obtain ⟨E, GM, VM, JM⟩ := P
  dsimp only at hE hGM hVM hJM hE64 hG256
  subst hE hGM hVM hJM ha hb
  change (lnP L).OK at hP
  change (decState L.inF L.inD).WF (lnP L) at hW
  have h52 : (0 : ℝ) < 2 ^ 52 := by positivity
  obtain ⟨hcD, hcR, hcC, ⟨p2, hp2, hb2⟩, hstart⟩ := covers_spec L ps hcov
  obtain ⟨-, -, hsize, hvec⟩ := check_parts _ (hchk p2 hp2)
  obtain ⟨hshv, hr0⟩ := hvec hb2
  have hG : Guard (lnC L) := guard_of_size (lnC L) hsize
  have hrow0 : ∀ g ≤ L.GM, slot 64 (getN L.outF 0) g = 2 ^ 52 := (row0Bad_spec _ hr0).1
  have hdel0 : slot 64 L.outD 0 = 2 ^ 52 := (row0Bad_spec _ hr0).2
  have hshv' : shapeVec (L.E + 1) L.outD = 0 := hshv
  -- the deficits
  have hdel : ∀ j, 1 ≤ j → j ≤ L.E →
      deltaNew (lnP L) (decState L.inF L.inD) L.a L.b j ≤ (slot 128 L.uD j : ℝ) / 2 ^ 128 ∧
        slot 128 L.uD j ≤ slot 64 L.outD j * 2 ^ 76 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj1 hjE
      obtain ⟨p, hp, hp0, hp1, hdo⟩ := hcD j hj1 hjE
      obtain ⟨h2, hle, hout⟩ := dTest_ok (L.withPart p) (hchk p hp) (hstart p hp).1 j hp0 hp1 hdo
      refine ⟨?_, hout⟩
      have h := dTerm_sound (L.withPart p) hP hE64 hG256 hW hG j hj1 hjE hdo h2
        (fun h2j => (ih (j - 1) (by omega) (by omega) (by omega)).1)
      exact h.trans (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity))
  have hdelT : ∀ k ≤ L.E, deltaNew (lnP L) (decState L.inF L.inD) L.a L.b k ≤
      (decState L.outF L.outD).delta k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · show (1 : ℝ) ≤ (slot 64 L.outD 0 : ℝ) / 2 ^ 52
      rw [hdel0, Nat.cast_pow, Nat.cast_ofNat, div_self h52.ne']
    · obtain ⟨h1, h2⟩ := hdel k hk1 hk
      refine h1.trans ?_
      show (slot 128 L.uD k : ℝ) / 2 ^ 128 ≤ (slot 64 L.outD k : ℝ) / 2 ^ 52
      rw [div_le_div_iff₀ (by positivity) h52]
      have : (slot 128 L.uD k : ℝ) ≤ (slot 64 L.outD k : ℝ) * 2 ^ 76 := by exact_mod_cast h2
      calc (slot 128 L.uD k : ℝ) * 2 ^ 52 ≤ (slot 64 L.outD k : ℝ) * 2 ^ 76 * 2 ^ 52 := by gcongr
        _ = (slot 64 L.outD k : ℝ) * 2 ^ 128 := by ring
  -- the cdf rows
  have hFr : ∀ j ≤ L.E, ∀ v ≤ L.GM,
      Fnew (lnP L) (decState L.inF L.inD) L.a L.b j v ≤ (decState L.outF L.outD).F j v := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      show (1 : ℝ) ≤ (slot 64 (getN L.outF 0) v : ℝ) / 2 ^ 52
      rw [hrow0 v hv, Nat.cast_pow, Nat.cast_ofNat, div_self h52.ne']
    | succ j ihj =>
      intro hjE
      have hent : ∀ v ≤ L.GM,
          (v < L.GM → Fnew (lnP L) (decState L.inF L.inD) L.a L.b (j + 1) (v + 1) ≤
            (decState L.outF L.outD).F (j + 1) (v + 1)) →
          Fnew (lnP L) (decState L.inF L.inD) L.a L.b (j + 1) v ≤ (decState L.outF L.outD).F (j + 1) v := by
        intro v hv hnext
        obtain ⟨p, hp, hp0, hp1, hdo⟩ := hcC (j + 1) (by omega) hjE v hv
        have hz := cdfTest_ok (L.withPart p) (hchk p hp) (hstart p hp).2 (j + 1) hp0 hp1 v hv hdo
        have hres := cdf_sound (L.withPart p) hP hW hG (j + 1) (by omega) hjE v hdo _ _ _ _ _ hz
          (hdel (j + 1) (by omega) hjE).1
          (fun hb => (rowShape_ok (L.withPart p) (hchk p hp) (hstart p hp).2 (j + 1) hp0 hp1 hb).2)
          (fun hb => s3_cum (L.withPart p) hW hE64 hG256 hP.1 (j + 1) (by omega) hjE hb v hv)
          (Fnew (lnP L) (decState L.inF L.inD) L.a L.b j v) (ihj (by omega) v hv)
        have hpre := Fnew_le_pre (lnP L) (decState L.inF L.inD) L.a L.b j v
        rcases hres with hres | hres
        · exact hpre.trans hres
        · exact G_case L (j + 1) v hv _ (hpre.trans (preF_le_one _ _ _ _ _ _ _))
            (fun hvG => (Fnew_mono _ _ _ _ _ _ hvG).trans (hnext hvG)) hres
      have hrow : ∀ w v, v + w = L.GM →
          Fnew (lnP L) (decState L.inF L.inD) L.a L.b (j + 1) v ≤ (decState L.outF L.outD).F (j + 1) v := by
        intro w
        induction w with
        | zero => exact fun v hvw => hent v (by omega) (fun hv => absurd hv (by omega))
        | succ w ihw => exact fun v hvw => hent v (by omega) (fun _ => ihw (v + 1) (by omega))
      exact fun v hv => hrow (L.GM - v) v (by omega)
  refine ⟨⟨hFr, hdelT⟩, ?_⟩
  have hshape : ∀ k, 1 ≤ k → k ≤ L.E → shapeRow (L.GM + 1) (getN L.outF k) = 0 := by
    intro k hk1 hkE
    obtain ⟨p, hp, hp0, hp1, hbp⟩ := hcR k hk1 hkE
    exact (rowShape_ok (L.withPart p) (hchk p hp) (hstart p hp).2 k hp0 hp1 hbp).1
  refine decState_WF (lnP L) L.outF L.outD (fun k hk g hg => ?_) (fun k hk g hg => ?_)
    (fun k hk => shapeVec_spec _ _ hshv' k (by change k ≤ L.E at hk; omega)) hrow0 hdel0
  · rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact (hrow0 g hg).le
    · exact (shapeRow_spec _ _ (hshape k hk1 hk)).1 g (by change g ≤ L.GM at hg; omega)
  · rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [hrow0 g (by change g < L.GM at hg; omega), hrow0 (g + 1) (by change g < L.GM at hg; omega)]
    · exact (shapeRow_spec _ _ (hshape k hk1 hk)).2 g (by change g < L.GM at hg; omega)

end FrogModel.D3.LaneD
