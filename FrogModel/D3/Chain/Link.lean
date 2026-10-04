module

public import FrogModel.D3.Chain.Basic
public import FrogModel.D3.LaneD.StepSound
public import FrogModel.D3.LaneD.SeedSound
public import FrogModel.D3.LaneD.ExtSound

@[expose] public section

/-!
# The chain of the certificate (Proposition 15.1 (2) of the paper): the links

The generated modules of `FrogModel.D3.CertData` (code/d3chain) compose these lemmas: the seed
(`seed_start`), a plain step (`plain_link`), an extension (`ext_link`), and the end of the chain with
the CHECK line (`certS1_of`), each from the soundness statement of its check, taken as a hypothesis
(`StepSoundT`, `SeedSoundT`, `ExtSoundT`, the types of `step_sound`, `seedCheck_sound` and
`extCheck_sound` of FrogModel/D3/LaneD). `CertReach X P h F D`: the stored state `(F, D)` at `(P, h)`
is reached from `X` by a chain of `CertStep`, and it is well formed at `P`.
-/

namespace FrogModel.D3.Chain

open FrogModel.D3.Iface FrogModel.D3.LaneD FrogModel.D3.LaneD.K

/-- The type of `LaneD.step_sound`. -/
abbrev StepSoundT : Prop := type_of% @step_sound

/-- The type of `LaneD.seedCheck_sound`. -/
abbrev SeedSoundT : Prop := type_of% @seedCheck_sound

/-- The type of `LaneD.extCheck_sound`. -/
abbrev ExtSoundT : Prop := type_of% @extCheck_sound

/-- The parameters of the steps after the extension: `(E, GM, VM, JM) = (64, 224, 32, 24)`. -/
def P1 : StParams := ⟨64, 224, 32, 24⟩

theorem P0_OK : P0.OK := by unfold StParams.OK P0; decide
theorem P0_E64 : P0.E ≤ 64 := by decide
theorem P0_G256 : P0.GM ≤ 256 := by decide
theorem P1_OK : P1.OK := by unfold StParams.OK P1; decide
theorem P1_E64 : P1.E ≤ 64 := by decide
theorem P1_G256 : P1.GM ≤ 256 := by decide

/-- The stored state `(F, D)` at `(P, h)` is reached from `X` and well formed at `P`. -/
def CertReach (X : StParams × ℕ × State) (P : StParams) (h : ℕ) (F : List ℕ) (D : ℕ) : Prop :=
  Relation.ReflTransGen CertStep X (P, h, decState F D) ∧ (decState F D).WF P

/-- The seed: the stored seed is above the seed state of the masses, and it starts a chain. -/
theorem seed_start (hsd : SeedSoundT) (massPk : ℕ) (F : List ℕ) (D hint : ℕ)
    (hc : K.seedCheck massPk F D hint = true) (W : ℕ → ℕ → ℝ) (hW : ∀ k, 1 ≤ k → k ≤ 32 → ∀ x ≤ 48,
      W k x = (((massPk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 : ℕ) : ℝ) / 2 ^ 62) :
    ((seedState 48 100 96 W).Le P0 (decState F D) ∧ (decState F D).WF P0) ∧
      CertReach (P0, 100, decState F D) P0 100 F D :=
  have h := hsd massPk F D hint hc W hW
  ⟨h, Relation.ReflTransGen.refl, h.2⟩

/-- A plain step: a line whose parts pass the kernel check and cover it. -/
theorem plain_link (hs : StepSoundT) (P : StParams) (h : ℕ) (L : Line) (ps : List Part)
    (hpar : L.E = P.E ∧ L.GM = P.GM ∧ L.VM = P.VM ∧ L.JM = P.JM ∧ L.a = h ∧ L.b = h)
    (hP : P.OK) (hE64 : P.E ≤ 64) (hG256 : P.GM ≤ 256)
    (hchk : AllP (fun p => check (L.withPart p) = true) ps) (hcov : covers L ps = true)
    (X : StParams × ℕ × State) (hX : CertReach X P h L.inF L.inD) : CertReach X P (h + 1) L.outF L.outD := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpar
  obtain ⟨hle, hW⟩ :=
    hs P h h L ps h1 h2 h3 h4 h5 h6 hP hE64 hG256 hX.2 (forall_mem_of_allP hchk) hcov
  exact ⟨hX.1.tail (CertStep.plain P h _ _ hP hW hle), hW⟩

/-- An extension at `h` from `P0'` to `P`. -/
theorem ext_link (hx : ExtSoundT) (P0' P : StParams) (h : ℕ) (Fi : List ℕ) (Di : ℕ) (Fo : List ℕ)
    (Do hint : ℕ) (hc : K.extCheck P0'.E P0'.GM P.E P.GM h Fi Di Fo Do hint = true)
    (X : StParams × ℕ × State) (hX : CertReach X P0' h Fi Di) : CertReach X P h Fo Do := by
  obtain ⟨hE, hG, hle, hW⟩ := hx P0' P h Fi Di Fo Do hint hc
  exact ⟨hX.1.tail (CertStep.ext P0' P h _ _ hE hG hW hle), hW⟩

theorem allN_iff (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero =>
      constructor
      · intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
      · intro _; rfl
  | succ n ih =>
      have h_succ : allN (Nat.succ n) f = (allN n f && f n) := rfl
      rw [h_succ, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h_allN, h_fn⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with (hlt | rfl)
        · exact h_allN i hlt
        · exact h_fn
      · intro h
        constructor
        · intro i hi
          exact h i (Nat.lt_succ_of_lt hi)
        · exact h n (Nat.lt_succ_self n)

theorem leCheck_spec (E GM : ℕ) (F : List ℕ) (D : ℕ) (F' : List ℕ) (D' : ℕ)
    (h : leCheck E GM F D F' D' = true) :
    (∀ k ≤ E, ∀ g ≤ GM, slot 64 (getN F k) g ≤ slot 64 (getN F' k) g) ∧
      ∀ k ≤ E, slot 64 D k ≤ slot 64 D' k := by
  unfold FrogModel.D3.Chain.leCheck at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hF, hD⟩
  have hF_iff := (FrogModel.D3.Chain.allN_iff (Nat.add E 1)
    (fun k => allN (Nat.add GM 1) (fun g => Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F' k) g)))).mp hF
  have hD_iff := (FrogModel.D3.Chain.allN_iff (Nat.add E 1)
    (fun k => Nat.ble (slot 64 D k) (slot 64 D' k))).mp hD
  have hF_all : ∀ k < Nat.add E 1, allN (Nat.add GM 1) (fun g => Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F' k) g)) = true := by
    intro k hk; simpa using hF_iff k hk
  have hD_all : ∀ k < Nat.add E 1, Nat.ble (slot 64 D k) (slot 64 D' k) = true := by
    intro k hk; simpa using hD_iff k hk
  have h_inner : ∀ k < Nat.add E 1, ∀ g < Nat.add GM 1, Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F' k) g) = true := by
    intro k hk
    have hk_allN := (FrogModel.D3.Chain.allN_iff (Nat.add GM 1)
      (fun g => Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F' k) g))).mp (hF_all k hk)
    intro g hg; simpa using hk_allN g hg
  have h_left : ∀ k ≤ E, ∀ g ≤ GM, slot 64 (getN F k) g ≤ slot 64 (getN F' k) g := by
    intro k hk g hg
    have hk_lt : k < Nat.add E 1 := Nat.lt_succ_of_le hk
    have hg_lt : g < Nat.add GM 1 := Nat.lt_succ_of_le hg
    have h_ble_eq := (Nat.ble_eq (x := slot 64 (getN F k) g) (y := slot 64 (getN F' k) g)).mp
      (h_inner k hk_lt g hg_lt)
    exact h_ble_eq
  have h_right : ∀ k ≤ E, slot 64 D k ≤ slot 64 D' k := by
    intro k hk
    have hk_lt : k < Nat.add E 1 := Nat.lt_succ_of_le hk
    have h_ble_eq := (Nat.ble_eq (x := slot 64 D k) (y := slot 64 D' k)).mp (hD_all k hk_lt)
    exact h_ble_eq
  exact And.intro h_left h_right

theorem wfCheck_spec (E GM : ℕ) (F : List ℕ) (D : ℕ) (h : wfCheck E GM F D = true) :
    (∀ k ≤ E, ∀ g ≤ GM, slot 64 (getN F k) g ≤ 2 ^ 52) ∧
      (∀ k ≤ E, ∀ g < GM, slot 64 (getN F k) g ≤ slot 64 (getN F k) (g + 1)) ∧
      (∀ k ≤ E, slot 64 D k ≤ 2 ^ 52) ∧ (∀ g ≤ GM, slot 64 (getN F 0) g = 2 ^ 52) ∧
      slot 64 D 0 = 2 ^ 52 := by
  have h_one52 : one52 = 2 ^ 52 := by
    calc
      one52 = Nat.shiftLeft 1 52 := rfl
      _ = 1 * 2 ^ 52 := by simp
      _ = 2 ^ 52 := by simp
  have h_wfCheck := h
  unfold FrogModel.D3.Chain.wfCheck at h_wfCheck
  rcases (Bool.and_eq_true_iff.mp h_wfCheck) with ⟨hABC, hD⟩
  rcases (Bool.and_eq_true_iff.mp hABC) with ⟨hAB, hC⟩
  rcases (Bool.and_eq_true_iff.mp hAB) with ⟨hA, hB⟩
  have hA' := (FrogModel.D3.Chain.allN_iff (Nat.add E 1) (fun k => allN (Nat.add GM 1) (fun g =>
      Nat.ble (slot 64 (getN F k) g) one52 &&
        (Nat.beq g GM || Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F k) (Nat.add g 1)))))).mp hA
  have hB' := (FrogModel.D3.Chain.allN_iff (Nat.add E 1) (fun k => Nat.ble (slot 64 D k) one52)).mp hB
  have hC' := (FrogModel.D3.Chain.allN_iff (Nat.add GM 1) (fun g => Nat.beq (slot 64 (getN F 0) g) one52)).mp hC
  have hD' : slot 64 D 0 = one52 := (Nat.beq_eq (x := slot 64 D 0) (y := one52)).mp hD
  have h_bound : ∀ k ≤ E, ∀ g ≤ GM, slot 64 (getN F k) g ≤ 2 ^ 52 := by
    intro k hk g hg
    have hk' : k < Nat.add E 1 := by
      have : Nat.add E 1 = E + 1 := rfl
      rw [this]
      omega
    have hg' : g < Nat.add GM 1 := by
      have : Nat.add GM 1 = GM + 1 := rfl
      rw [this]
      omega
    have h_entry := hA' k hk'
    have hallN_iff := FrogModel.D3.Chain.allN_iff (Nat.add GM 1) (fun g' =>
      Nat.ble (slot 64 (getN F k) g') one52 &&
        (Nat.beq g' GM || Nat.ble (slot 64 (getN F k) g') (slot 64 (getN F k) (Nat.add g' 1))))
    have h_entry' := (hallN_iff.mp h_entry) g hg'
    rcases (Bool.and_eq_true_iff.mp h_entry') with ⟨h_ble, h_or⟩
    have h_le_one52 : slot 64 (getN F k) g ≤ one52 := (Nat.ble_eq.mp h_ble)
    rw [h_one52] at h_le_one52
    exact h_le_one52
  have h_mono : ∀ k ≤ E, ∀ g < GM, slot 64 (getN F k) g ≤ slot 64 (getN F k) (g + 1) := by
    intro k hk g hg
    have hk' : k < Nat.add E 1 := by
      have : Nat.add E 1 = E + 1 := rfl
      rw [this]
      omega
    have hg' : g < Nat.add GM 1 := by
      have : Nat.add GM 1 = GM + 1 := rfl
      rw [this]
      omega
    have h_entry := hA' k hk'
    have hallN_iff := FrogModel.D3.Chain.allN_iff (Nat.add GM 1) (fun g' =>
      Nat.ble (slot 64 (getN F k) g') one52 &&
        (Nat.beq g' GM || Nat.ble (slot 64 (getN F k) g') (slot 64 (getN F k) (Nat.add g' 1))))
    have h_entry' := (hallN_iff.mp h_entry) g hg'
    rcases (Bool.and_eq_true_iff.mp h_entry') with ⟨h_ble, h_or⟩
    rcases (Bool.or_eq_true_iff.mp h_or) with (h_beq | h_ble2)
    · -- h_beq : Nat.beq g GM = true → g = GM, but g < GM, contradiction
      have h_eq : g = GM := (Nat.beq_eq (x := g) (y := GM)).mp h_beq
      exfalso; exact Nat.lt_irrefl g (h_eq ▸ hg)
    · -- h_ble2 : Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F k) (Nat.add g 1)) = true
      have h_le : slot 64 (getN F k) g ≤ slot 64 (getN F k) (Nat.add g 1) := (Nat.ble_eq.mp h_ble2)
      -- Need to relate Nat.add g 1 to g + 1
      have : Nat.add g 1 = g + 1 := rfl
      rw [this] at h_le
      exact h_le
  have h_D_bound : ∀ k ≤ E, slot 64 D k ≤ 2 ^ 52 := by
    intro k hk
    have hk' : k < Nat.add E 1 := by
      have : Nat.add E 1 = E + 1 := rfl
      rw [this]
      omega
    have h_entry := hB' k hk'
    have h_le_one52 : slot 64 D k ≤ one52 := (Nat.ble_eq.mp h_entry)
    rw [h_one52] at h_le_one52
    exact h_le_one52
  have h_row0 : ∀ g ≤ GM, slot 64 (getN F 0) g = 2 ^ 52 := by
    intro g hg
    have hg' : g < Nat.add GM 1 := by
      have : Nat.add GM 1 = GM + 1 := rfl
      rw [this]
      omega
    have h_entry := hC' g hg'
    have h_eq_one52 : slot 64 (getN F 0) g = one52 := (Nat.beq_eq (x := slot 64 (getN F 0) g) (y := one52)).mp h_entry
    rw [h_one52] at h_eq_one52
    exact h_eq_one52
  have h_D0 : slot 64 D 0 = 2 ^ 52 := by
    rw [h_one52] at hD'
    exact hD'
  exact And.intro h_bound (And.intro h_mono (And.intro h_D_bound (And.intro h_row0 h_D0)))

theorem div_le_of (n a b : ℕ) (hb : 0 < b) (h : n * b ≤ a * 2 ^ 52) :
    (n : ℝ) / 2 ^ 52 ≤ (a : ℝ) / b := by
  have hb' : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hpow : (0 : ℝ) < (2 ^ 52 : ℝ) := by norm_num
  rw [div_le_div_iff₀ hpow hb']
  exact_mod_cast h

theorem leCheck_sound (P : StParams) (F : List ℕ) (D : ℕ) (F' : List ℕ) (D' : ℕ)
    (h : leCheck P.E P.GM F D F' D' = true) : (decState F D).Le P (decState F' D') := by
  obtain ⟨hF, hD⟩ := leCheck_spec _ _ _ _ _ _ h
  have h52 : (0 : ℝ) < 2 ^ 52 := by positivity
  refine ⟨fun k hk g hg => ?_, fun k hk => ?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hF k hk g hg) h52.le
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hD k hk) h52.le

theorem wfCheck_sound (P : StParams) (F : List ℕ) (D : ℕ) (h : wfCheck P.E P.GM F D = true) :
    (decState F D).WF P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := wfCheck_spec _ _ _ _ h
  exact decState_WF P F D h1 h2 h3 h4 h5

/-- The end of the chain: the state `(Fn, Dn)` reached at `(P, hn)` is at most the CHECK state
`T = (TF, TD)`, and the CHECK line (input and output `T`, children heights `hn..m1 - 1`) passes; with
the bounds on `T` this is Proposition 15.1 (2). -/
theorem certS1_of (hs : StepSoundT) (W : ℕ → ℕ → ℝ) (F0 : List ℕ) (D0 : ℕ)
    (hseed : (seedState 48 100 96 W).Le P0 (decState F0 D0) ∧ (decState F0 D0).WF P0)
    (P : StParams) (hn : ℕ) (Fn : List ℕ) (Dn : ℕ) (hr : CertReach (P0, 100, decState F0 D0) P hn Fn Dn)
    (TF : List ℕ) (TD : ℕ) (hle : leCheck P.E P.GM Fn Dn TF TD = true)
    (hwf : wfCheck P.E P.GM TF TD = true) (L : Line) (ps : List Part)
    (hpar : L.E = P.E ∧ L.GM = P.GM ∧ L.VM = P.VM ∧ L.JM = P.JM ∧ L.a = hn ∧ L.b = m1 - 1)
    (hio : L.inF = TF ∧ L.inD = TD ∧ L.outF = TF ∧ L.outD = TD)
    (hP : P.OK) (hE64 : P.E ≤ 64) (hG256 : P.GM ≤ 256)
    (hchk : AllP (fun p => check (L.withPart p) = true) ps) (hcov : covers L ps = true)
    (hhn : hn ≤ m1 - 30) (hE : 62 ≤ P.E) (hd1 : slot 64 TD 1 * 5 ≤ 2 * 2 ^ 52)
    (hd62 : slot 64 TD 62 * 88917100 ≤ 7045771 * 2 ^ 52) :
    CertS1 (seedState 48 100 96 W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpar
  obtain ⟨hiF, hiD, hoF, hoD⟩ := hio
  have hWT := wfCheck_sound P TF TD hwf
  have hfix := hs P hn (m1 - 1) L ps h1 h2 h3 h4 h5 h6 hP hE64 hG256 (by rw [hiF, hiD]; exact hWT)
    (forall_mem_of_allP hchk) hcov
  rw [hiF, hiD, hoF, hoD] at hfix
  refine ⟨decState F0 D0, P, hn, decState Fn Dn, decState TF TD, hseed.1, hseed.2, hr.1,
    leCheck_sound P Fn Dn TF TD hle, hWT, hP, hfix.1, hhn, hE, ?_, ?_⟩
  · exact div_le_of _ 2 5 (by norm_num) hd1
  · exact div_le_of _ 7045771 88917100 (by norm_num) hd62

end FrogModel.D3.Chain
