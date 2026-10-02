module

public import FrogModel.Pool.Defs

@[expose] public section

/-!
# Pools: the law of the generic reading map (Lemma 4.3 of the paper)

The values read by `readGen coord sel` from `ω : K → E` (Pool/Defs.lean), with labels in a
countable `J`. On the event that the labels are `ℓ`, the values read are the coordinates
`cmap coord ℓ` of `ω` (`readGen_eq_of_consistent`), so the preimage of a set `B` of values is the
disjoint union over `ℓ` of the preimages of `B ∩ consistent sel ℓ` under these coordinate maps
(`preimage_readGen`). When `cmap coord ℓ` is injective and every coordinate `coord k ℓ i` has law
`μ i`, each piece has the law of independent values with laws `μ (ℓ j)`
(`measure_preimage_readGen`), whatever `coord` is: two such readings have the same law
(`map_readGen_eq`).
-/

open MeasureTheory

namespace FrogModel.Pool


/-- The first `m` values of `Fin.snoc p y` are the first `m` values of `p`. -/
theorem take_snoc_of_le {E : Type*} {n : ℕ} (p : Fin n → E) (y : E) (m : ℕ) (h : m ≤ n) :
    Fin.take m (h.trans n.le_succ) (Fin.snoc (α := fun _ => E) p y) = Fin.take m h p := by
  rw [← Fin.take_init m h (Fin.snoc (α := fun _ => E) p y), Fin.init_snoc]

/-- The labels of `Fin.snoc p y`: those of `p`, then `sel n p`. -/
theorem labels_snoc {J E : Type*} (sel : ∀ k : ℕ, (Fin k → E) → J) {n : ℕ} (p : Fin n → E) (y : E) :
    labels sel (Fin.snoc (α := fun _ => E) p y) =
      Fin.snoc (α := fun _ => J) (labels sel p) (sel n p) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [labels, Fin.snoc, Fin.val_last]
  · intro i
    simp [labels, Fin.snoc, Fin.val_castSucc]
    refine congrArg (sel (i : ℕ)) ?_
    ext k : 1
    have hk : (k : ℕ) < n := lt_trans k.isLt i.isLt
    simpa [Fin.take_apply, Fin.snoc, Fin.val_castLE, hk] using (by
      have h_eq : (Fin.castLE (i.isLt.le.trans n.le_succ) k).castLT hk = Fin.castLE i.isLt.le k := by
        apply Fin.ext
        simp [Fin.val_castLE]
      rw [h_eq])

/-- The labels of the first `m` values are the first `m` labels. -/
theorem labels_take {J E : Type*} (sel : ∀ k : ℕ, (Fin k → E) → J) {n : ℕ} (p : Fin n → E) (m : ℕ)
    (h : m ≤ n) : labels sel (Fin.take m h p) = Fin.take m h (labels sel p) := by
  funext j
  simp only [labels, Fin.take_apply]
  simp

/-- The first `m` values read are the values of a reading of length `m`. -/
theorem take_readGen {J K E : Type*} (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J)
    (ω : K → E) (n m : ℕ) (h : m ≤ n) :
    Fin.take m h (readGen coord sel ω n) = readGen coord sel ω m := by
  induction' n with n ih
  · -- n = 0
    have hm : m = 0 := by omega
    subst hm
    ext i
    exact i.elim0
  · -- n + 1
    rcases Nat.eq_or_lt_of_le h with (rfl | hmn)
    · -- m = n + 1
      apply Fin.take_eq_self
    · -- m < n + 1, i.e., m ≤ n
      have hmn' : m ≤ n := Nat.le_of_lt_succ hmn
      rw [readGen]
      rw [take_snoc_of_le (readGen coord sel ω n) (ω (coord n (labels sel (readGen coord sel ω n)) (sel n (readGen coord sel ω n)))) m hmn']
      rw [ih hmn']

/-- Value `j` read is the coordinate `cmap coord ℓ j` of `ω`, `ℓ` the labels of the values read. -/
theorem readGen_apply {J K E : Type*} (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J)
    (ω : K → E) (n : ℕ) (j : Fin n) :
    readGen coord sel ω n j = ω (cmap coord (labels sel (readGen coord sel ω n)) j) := by
  have h1 : readGen coord sel ω n j = readGen coord sel ω (j + 1) (Fin.last j) := by
    rw [← take_readGen coord sel ω n (j + 1) j.isLt, Fin.take_apply]
    congr 1
  rw [h1]
  simp only [cmap]
  rw [← labels_take, take_readGen]
  show Fin.snoc (α := fun _ => E) (readGen coord sel ω j)
    (ω (coord j (labels sel (readGen coord sel ω j)) (sel j (readGen coord sel ω j))))
    (Fin.last j) = _
  rw [Fin.snoc_last]
  simp only [labels, take_readGen]

/-- If the coordinates of `ω` along `ℓ` have the labels `ℓ`, they are the values read. -/
theorem readGen_eq_of_consistent {J K E : Type*} (coord : ∀ k : ℕ, (Fin k → J) → J → K)
    (sel : ∀ k : ℕ, (Fin k → E) → J) (ω : K → E) {n : ℕ} (ℓ : Fin n → J)
    (h : (fun j : Fin n => ω (cmap coord ℓ j)) ∈ consistent sel ℓ) :
    readGen coord sel ω n = fun j : Fin n => ω (cmap coord ℓ j) := by
  set q : Fin n → E := fun j : Fin n => ω (cmap coord ℓ j) with hq
  have hl : labels sel q = ℓ := h
  have key : ∀ m (hm : m ≤ n), readGen coord sel ω m = Fin.take m hm q := by
    intro m
    induction m with
    | zero => intro _; funext t; exact t.elim0
    | succ m ih =>
      intro hm
      rw [Fin.take_succ_eq_snoc m hm q]
      show Fin.snoc (α := fun _ => E) (readGen coord sel ω m)
        (ω (coord m (labels sel (readGen coord sel ω m)) (sel m (readGen coord sel ω m)))) = _
      rw [ih (by omega)]
      have h1 : labels sel (Fin.take m (by omega) q) = Fin.take m (by omega) ℓ := by
        rw [labels_take, hl]
      have h2 : sel m (Fin.take m (by omega) q) = ℓ ⟨m, hm⟩ := congrFun hl ⟨m, hm⟩
      rw [h1, h2]
      rfl
  rw [key n le_rfl, Fin.take_eq_self]

/-- The preimage of a set of values, split by the labels. -/
theorem preimage_readGen {J K E : Type*} (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J)
    {n : ℕ} (B : Set (Fin n → E)) :
    (fun ω => readGen coord sel ω n) ⁻¹' B =
      ⋃ ℓ : Fin n → J, (fun ω : K → E => fun j : Fin n => ω (cmap coord ℓ j)) ⁻¹'
        (B ∩ consistent sel ℓ) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro h
    set ℓ := labels sel (readGen coord sel ω n) with hℓ
    have h_eq : (fun j : Fin n => ω (cmap coord ℓ j)) = readGen coord sel ω n := by
      funext j
      dsimp [ℓ]
      rw [← readGen_apply coord sel ω n j]
    refine ⟨ℓ, ?_, ?_⟩
    · rw [h_eq]; exact h
    · rw [h_eq]; exact hℓ.symm
  · intro h
    rcases h with ⟨ℓ, hB, hc⟩
    have h_eq := readGen_eq_of_consistent coord sel ω ℓ hc
    rw [h_eq]
    exact hB

/-- The pieces of `preimage_readGen` are pairwise disjoint. -/
theorem pairwise_disjoint_readGen {J K E : Type*} (coord : ∀ k : ℕ, (Fin k → J) → J → K)
    (sel : ∀ k : ℕ, (Fin k → E) → J) {n : ℕ} (B : Set (Fin n → E)) :
    Pairwise (Function.onFun Disjoint fun ℓ : Fin n → J =>
      (fun ω : K → E => fun j : Fin n => ω (cmap coord ℓ j)) ⁻¹' (B ∩ consistent sel ℓ)) := by
  intro ℓ ℓ' hne
  refine Set.disjoint_left.2 fun ω h1 h2 => hne ?_
  simp only [Set.mem_preimage, Set.mem_inter_iff] at h1 h2
  have hcons₁ : (fun j : Fin n => ω (cmap coord ℓ j)) ∈ consistent sel ℓ := h1.2
  have hcons₂ : (fun j : Fin n => ω (cmap coord ℓ' j)) ∈ consistent sel ℓ' := h2.2
  have hlabels₁ : labels sel (readGen coord sel ω n) = ℓ := by
    rw [readGen_eq_of_consistent coord sel ω ℓ hcons₁]
    exact hcons₁
  have hlabels₂ : labels sel (readGen coord sel ω n) = ℓ' := by
    rw [readGen_eq_of_consistent coord sel ω ℓ' hcons₂]
    exact hcons₂
  rw [← hlabels₁, ← hlabels₂]

/-- The value sequences with given labels form a measurable set. -/
theorem measurableSet_consistent {J E : Type*} [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → J)
    (hsel : ∀ (k : ℕ) (i : J), MeasurableSet {y : Fin k → E | sel k y = i}) {n : ℕ}
    (ℓ : Fin n → J) : MeasurableSet (consistent sel ℓ) := by
  have h_eq : consistent sel ℓ = ⋂ j : Fin n, (fun q : Fin n → E => Fin.take j j.isLt.le q) ⁻¹' {y | sel j y = ℓ j} := by
    ext q
    simp [consistent, labels, funext_iff]
  rw [h_eq]
  refine MeasurableSet.iInter ?_
  intro j
  have h_meas_set : MeasurableSet {y : Fin j → E | sel j y = ℓ j} := hsel j (ℓ j)
  have h_meas_map : Measurable (fun q : Fin n → E => Fin.take j j.isLt.le q) := by
    rw [measurable_pi_iff]
    intro t
    have : (fun q : Fin n → E => (Fin.take j j.isLt.le q) t) = (fun q => q (Fin.castLE j.isLt.le t)) := by
      ext q; rfl
    rw [this]
    exact measurable_pi_apply (Fin.castLE j.isLt.le t)
  exact h_meas_set.preimage h_meas_map

/-- The values read are measurable for every σ-algebra `m` on `K → E` for which the coordinates
read along every label sequence are measurable. -/
theorem measurable_readGen_of {J K E : Type*} [MeasurableSpace E] [Countable J] {m : MeasurableSpace (K → E)}
    (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J)
    (hsel : ∀ (k : ℕ) (i : J), MeasurableSet {y : Fin k → E | sel k y = i}) (n : ℕ)
    (hm : ∀ (ℓ : Fin n → J) (j : Fin n), Measurable[m] fun ω : K → E => ω (cmap coord ℓ j)) :
    Measurable[m] fun ω : K → E => readGen coord sel ω n := by
  intro B hB
  rw [preimage_readGen coord sel B]
  refine MeasurableSet.iUnion ?_
  intro ℓ
  have h_consistent : MeasurableSet (consistent sel ℓ) := measurableSet_consistent sel hsel ℓ
  have h_inter : MeasurableSet (B ∩ consistent sel ℓ) := hB.inter h_consistent
  have hm_pi : Measurable[m] (fun ω : K → E => fun j : Fin n => ω (cmap coord ℓ j)) := by
    rw [measurable_pi_iff]
    intro j
    exact hm ℓ j
  exact hm_pi h_inter

/-- The values read are measurable. -/
theorem measurable_readGen {J K E : Type*} [MeasurableSpace E] [Countable J]
    (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J)
    (hsel : ∀ (k : ℕ) (i : J), MeasurableSet {y : Fin k → E | sel k y = i}) (n : ℕ) :
    Measurable fun ω : K → E => readGen coord sel ω n := by
  apply measurable_readGen_of coord sel hsel n
  intro ℓ j
  exact measurable_pi_apply (cmap coord ℓ j)

/-- The law of the values read, as a sum over the label sequences. -/
theorem measure_preimage_readGen {J K E : Type*} [MeasurableSpace E] [Countable J]
    (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J)
    (hsel : ∀ (k : ℕ) (i : J), MeasurableSet {y : Fin k → E | sel k y = i})
    (μ' : K → Measure E) [∀ κ, IsProbabilityMeasure (μ' κ)] (μ : J → Measure E)
    [∀ j, IsProbabilityMeasure (μ j)] (hμ : ∀ (k : ℕ) (ℓ : Fin k → J) (i : J), μ' (coord k ℓ i) = μ i)
    (hinj : ∀ (n : ℕ) (ℓ : Fin n → J), (consistent sel ℓ).Nonempty →
      Function.Injective (cmap coord ℓ))
    {n : ℕ} {B : Set (Fin n → E)} (hB : MeasurableSet B) :
    Measure.infinitePi μ' ((fun ω => readGen coord sel ω n) ⁻¹' B) =
      ∑' ℓ : Fin n → J, Measure.infinitePi (fun j : Fin n => μ (ℓ j)) (B ∩ consistent sel ℓ) := by
  rw [preimage_readGen coord sel B]
  have hf : ∀ ℓ : Fin n → J, Measurable fun ω : K → E => fun j : Fin n => ω (cmap coord ℓ j) :=
    fun ℓ => measurable_pi_iff.2 fun j => measurable_pi_apply _
  rw [measure_iUnion (pairwise_disjoint_readGen coord sel B)
    (fun ℓ => (hf ℓ) (hB.inter (measurableSet_consistent sel hsel ℓ)))]
  refine tsum_congr fun ℓ => ?_
  by_cases hne : (B ∩ consistent sel ℓ).Nonempty
  · have hi := hinj n ℓ (hne.mono Set.inter_subset_right)
    rw [← Measure.map_apply (hf ℓ) (hB.inter (measurableSet_consistent sel hsel ℓ)),
      Measure.map_infinitePi_infinitePi_of_inj hi]
    simp only [cmap, hμ]
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp

/-- Two readings with the same labels and the same laws along every label sequence have the same
law. -/
theorem map_readGen_eq {J E : Type*} [MeasurableSpace E] [Countable J] {K₁ K₂ : Type*}
    (coord₁ : ∀ k : ℕ, (Fin k → J) → J → K₁) (coord₂ : ∀ k : ℕ, (Fin k → J) → J → K₂)
    (sel : ∀ k : ℕ, (Fin k → E) → J)
    (hsel : ∀ (k : ℕ) (i : J), MeasurableSet {y : Fin k → E | sel k y = i})
    (μ₁ : K₁ → Measure E) [∀ κ, IsProbabilityMeasure (μ₁ κ)]
    (μ₂ : K₂ → Measure E) [∀ κ, IsProbabilityMeasure (μ₂ κ)] (μ : J → Measure E)
    [∀ j, IsProbabilityMeasure (μ j)]
    (hμ₁ : ∀ (k : ℕ) (ℓ : Fin k → J) (i : J), μ₁ (coord₁ k ℓ i) = μ i)
    (hμ₂ : ∀ (k : ℕ) (ℓ : Fin k → J) (i : J), μ₂ (coord₂ k ℓ i) = μ i)
    (hinj₁ : ∀ (n : ℕ) (ℓ : Fin n → J), (consistent sel ℓ).Nonempty →
      Function.Injective (cmap coord₁ ℓ))
    (hinj₂ : ∀ (n : ℕ) (ℓ : Fin n → J), (consistent sel ℓ).Nonempty →
      Function.Injective (cmap coord₂ ℓ)) (n : ℕ) :
    (Measure.infinitePi μ₁).map (fun ω => readGen coord₁ sel ω n) =
      (Measure.infinitePi μ₂).map (fun ω => readGen coord₂ sel ω n) := by
  ext B hB
  rw [Measure.map_apply (measurable_readGen coord₁ sel hsel n) hB,
    Measure.map_apply (measurable_readGen coord₂ sel hsel n) hB]
  rw [measure_preimage_readGen coord₁ sel hsel μ₁ μ hμ₁ hinj₁ hB,
    measure_preimage_readGen coord₂ sel hsel μ₂ μ hμ₂ hinj₂ hB]

/-- The values read at the steps `j < n`, each read at its own length, are the reading of
length `n`. -/
theorem readGen_last {J K E : Type*} (coord : ∀ k : ℕ, (Fin k → J) → J → K) (sel : ∀ k : ℕ, (Fin k → E) → J)
    (ω : K → E) (n : ℕ) :
    (fun j : Fin n => readGen coord sel ω (j + 1) (Fin.last j)) = readGen coord sel ω n := by
  induction' n with n ih
  · ext j; exact Fin.elim0 j
  · ext j
    simp only [readGen]
    refine Fin.lastCases ?_ ?_ j
    · simp
    · intro j'
      simp
      simpa [readGen] using congrFun ih j'

/-! ### The two instances -/

/-- The pool reading is the generic reading with the pool coordinates. -/
theorem poolRead_eq_readGen {E : Type*} [MeasurableSpace E] {I : Type*} (sel : ∀ k : ℕ, (Fin k → E) → I) (ω : I × ℕ → E)
    (n : ℕ) : poolRead sel ω n = readGen poolCoord sel ω n := by
  induction' n with n ih
  · ext i; exact i.elim0
  · simp only [poolRead, readGen]
    rw [ih]
    congr

/-- The fresh reading is the generic reading with the fresh coordinates. -/
theorem freshRead_eq_readGen {E : Type*} [MeasurableSpace E] {I : Type*} (sel : ∀ k : ℕ, (Fin k → E) → I) (ω : ℕ × I → E)
    (n : ℕ) : freshRead sel ω n = readGen freshCoord sel ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [freshRead, readGen, freshCoord, ih]

/-- Along any label sequence the pool coordinates are distinct: two steps with the same label
read elements of the pool with distinct numbers of earlier uses. -/
theorem injective_cmap_poolCoord {I : Type*} {n : ℕ} (ℓ : Fin n → I) :
    Function.Injective (cmap poolCoord ℓ) := by
  classical
  intro a b h
  have h_label : ℓ a = ℓ b := by
    have := congr_arg Prod.fst h
    simpa [cmap, poolCoord] using this
  have h_count_eq : ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a).card =
      ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b).card := by
    have := congr_arg Prod.snd h
    simpa [cmap, poolCoord] using this
  by_contra h_ne
  have h_lt_or : a < b ∨ b < a := Fin.lt_or_lt_of_ne h_ne
  rcases h_lt_or with (h_lt | h_lt)
  · -- a < b
    have h_le : (a : ℕ) ≤ (b : ℕ) := Nat.le_of_lt h_lt
    set f : Fin a ↪ Fin b := Fin.castLEEmb h_le with hf
    have h_map_sub : Finset.map f
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) ⊆
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨t, ht, rfl⟩
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨_, ht_eq⟩
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      · -- goal: (Fin.take b b.isLt.le ℓ) (f t) = ℓ b
        rw [hf, Fin.castLEEmb_apply, Fin.take_apply]
        -- goal: ℓ (Fin.castLE b.isLt.le (Fin.castLE h_le t)) = ℓ b
        rw [← h_label]
        -- goal: ℓ (Fin.castLE b.isLt.le (Fin.castLE h_le t)) = ℓ a
        rw [Fin.take_apply] at ht_eq
        -- ht_eq: ℓ (Fin.castLE a.isLt.le t) = ℓ a
        have h_eq_fin : Fin.castLE b.isLt.le (Fin.castLE h_le t) = Fin.castLE a.isLt.le t := by
          apply Fin.ext; simp
        rw [h_eq_fin, ht_eq]
    have h_not_mem : (⟨a, h_lt⟩ : Fin b) ∉ Finset.map f
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) := by
      intro hmem
      rcases Finset.mem_map.mp hmem with ⟨t, ht, h_eq⟩
      have h_val : (f t).val < a := by
        rw [hf, Fin.castLEEmb_apply]
        have : (Fin.castLE h_le t).val = t.val := by simp
        rw [this]
        exact t.isLt
      have h_val_a : (f t).val = a := by
        simp [h_eq]
      rw [h_val_a] at h_val
      exact lt_irrefl a h_val
    have h_card_map : (Finset.map f
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a)).card =
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a).card :=
      Finset.card_map f
    have h_ne_sets : Finset.map f
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) ≠
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) := by
      intro h_eq
      apply h_not_mem
      have h_mem : (⟨a, h_lt⟩ : Fin b) ∈ ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · rw [Fin.take_apply]
          -- goal: ℓ (Fin.castLE b.isLt.le ⟨a, h_lt⟩) = ℓ b
          -- Fin.castLE b.isLt.le ⟨a, h_lt⟩ = a (both have value a.val)
          have h_eq : Fin.castLE b.isLt.le (⟨a, h_lt⟩ : Fin b) = a := by
            apply Fin.ext; simp
          rw [h_eq, h_label]
      exact h_eq.symm ▸ h_mem
    have h_strict_sub : Finset.map f
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) ⊂
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) :=
      (Finset.ssubset_iff_subset_ne).mpr ⟨h_map_sub, h_ne_sets⟩
    have h_card_lt : (Finset.map f
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a)).card <
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b).card :=
      Finset.card_lt_card h_strict_sub
    rw [h_card_map] at h_card_lt
    linarith
  · -- b < a, symmetric
    have h_le : (b : ℕ) ≤ (a : ℕ) := Nat.le_of_lt h_lt
    set f : Fin b ↪ Fin a := Fin.castLEEmb h_le with hf
    have h_map_sub : Finset.map f
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) ⊆
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨t, ht, rfl⟩
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨_, ht_eq⟩
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      · rw [hf, Fin.castLEEmb_apply, Fin.take_apply]
        -- goal: ℓ (Fin.castLE a.isLt.le (Fin.castLE h_le t)) = ℓ a
        rw [Fin.take_apply] at ht_eq
        -- ht_eq: ℓ (Fin.castLE b.isLt.le t) = ℓ b
        rw [← h_label] at ht_eq
        -- ht_eq: ℓ (Fin.castLE b.isLt.le t) = ℓ a
        have h_eq_fin : Fin.castLE a.isLt.le (Fin.castLE h_le t) = Fin.castLE b.isLt.le t := by
          apply Fin.ext; simp
        rw [h_eq_fin, ht_eq]
    have h_not_mem : (⟨b, h_lt⟩ : Fin a) ∉ Finset.map f
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) := by
      intro hmem
      rcases Finset.mem_map.mp hmem with ⟨t, ht, h_eq⟩
      have h_val : (f t).val < b := by
        rw [hf, Fin.castLEEmb_apply]
        have : (Fin.castLE h_le t).val = t.val := by simp
        rw [this]
        exact t.isLt
      have h_val_b : (f t).val = b := by
        simp [h_eq]
      rw [h_val_b] at h_val
      exact lt_irrefl b h_val
    have h_card_map : (Finset.map f
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b)).card =
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b).card :=
      Finset.card_map f
    have h_ne_sets : Finset.map f
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) ≠
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) := by
      intro h_eq
      apply h_not_mem
      have h_mem : (⟨b, h_lt⟩ : Fin a) ∈ ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · rw [Fin.take_apply]
          -- goal: ℓ (Fin.castLE a.isLt.le ⟨b, h_lt⟩) = ℓ a
          -- Fin.castLE a.isLt.le ⟨b, h_lt⟩ = b (both have value b.val)
          have h_eq : Fin.castLE a.isLt.le (⟨b, h_lt⟩ : Fin a) = b := by
            apply Fin.ext; simp
          rw [h_eq, h_label.symm]
      exact h_eq.symm ▸ h_mem
    have h_strict_sub : Finset.map f
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b) ⊂
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a) :=
      (Finset.ssubset_iff_subset_ne).mpr ⟨h_map_sub, h_ne_sets⟩
    have h_card_lt : (Finset.map f
        ((Finset.univ : Finset (Fin b)).filter fun t => (Fin.take b b.isLt.le ℓ) t = ℓ b)).card <
        ((Finset.univ : Finset (Fin a)).filter fun t => (Fin.take a a.isLt.le ℓ) t = ℓ a).card :=
      Finset.card_lt_card h_strict_sub
    rw [h_card_map] at h_card_lt
    linarith

/-- Along any label sequence the fresh coordinates are distinct. -/
theorem injective_cmap_freshCoord {I : Type*} {n : ℕ} (ℓ : Fin n → I) :
    Function.Injective (cmap freshCoord ℓ) := by
  intro a b h
  simp only [cmap, freshCoord, Prod.mk.injEq] at h
  exact Fin.ext h.1

end FrogModel.Pool
