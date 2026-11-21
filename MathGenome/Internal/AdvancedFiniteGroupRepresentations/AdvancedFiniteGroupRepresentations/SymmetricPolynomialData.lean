import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SymmetricPolynomialData
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Partitions
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace AdvancedFiniteGroupRepresentations

abbrev PolynomialRing := Specs.AdvancedFiniteGroupRepresentations.PolynomialRing
abbrev Word := Specs.AdvancedFiniteGroupRepresentations.Word
noncomputable abbrev weakWords := Specs.AdvancedFiniteGroupRepresentations.weakWords
noncomputable abbrev strictWords := Specs.AdvancedFiniteGroupRepresentations.strictWords
noncomputable abbrev wordWeight := @Specs.AdvancedFiniteGroupRepresentations.wordWeight
noncomputable abbrev wordContent := @Specs.AdvancedFiniteGroupRepresentations.wordContent
noncomputable abbrev h := Specs.AdvancedFiniteGroupRepresentations.h
noncomputable abbrev e := Specs.AdvancedFiniteGroupRepresentations.e
abbrev Filling := @Specs.AdvancedFiniteGroupRepresentations.Filling
abbrev IsSemistandard := @Specs.AdvancedFiniteGroupRepresentations.IsSemistandard
abbrev SemistandardFilling := @Specs.AdvancedFiniteGroupRepresentations.SemistandardFilling
noncomputable abbrev semistandardFillings := @Specs.AdvancedFiniteGroupRepresentations.semistandardFillings
noncomputable abbrev fillingWeight := @Specs.AdvancedFiniteGroupRepresentations.fillingWeight
noncomputable abbrev fillingContent := @Specs.AdvancedFiniteGroupRepresentations.fillingContent
noncomputable abbrev tableauWeight := @Specs.AdvancedFiniteGroupRepresentations.tableauWeight
noncomputable abbrev tableauContent := @Specs.AdvancedFiniteGroupRepresentations.tableauContent
noncomputable abbrev tableauSum := @Specs.AdvancedFiniteGroupRepresentations.tableauSum
abbrev cellFromOneBased := @Specs.AdvancedFiniteGroupRepresentations.cellFromOneBased
abbrev entryOneBased := @Specs.AdvancedFiniteGroupRepresentations.entryOneBased

theorem mem_weakWords : ∀ {r k} (w : Word r k), w ∈ weakWords r k ↔ Monotone w := by
  classical
  intro r k w
  simp [weakWords, Specs.AdvancedFiniteGroupRepresentations.weakWords]

theorem mem_strictWords : ∀ {r k} (w : Word r k), w ∈ strictWords r k ↔ StrictMono w := by
  classical
  intro r k w
  simp [strictWords, Specs.AdvancedFiniteGroupRepresentations.strictWords]

theorem h_nat : ∀ r k : ℕ, h r (k : ℤ) = ∑ w ∈ weakWords r k, wordWeight w := by
  intro r k
  simp [h, Specs.AdvancedFiniteGroupRepresentations.h]

theorem e_nat : ∀ r k : ℕ, e r (k : ℤ) = ∑ w ∈ strictWords r k, wordWeight w := by
  intro r k
  simp [e, Specs.AdvancedFiniteGroupRepresentations.e]

theorem h_neg : ∀ (r : ℕ) (k : ℤ), k < 0 → h r k = 0 := by
  intro r k hk
  simp [h, Specs.AdvancedFiniteGroupRepresentations.h, hk]

theorem e_neg : ∀ (r : ℕ) (k : ℤ), k < 0 → e r k = 0 := by
  intro r k hk
  simp [e, Specs.AdvancedFiniteGroupRepresentations.e, hk]

theorem h_zero : ∀ r, h r 0 = 1 := by
  classical
  intro r
  rw [show (0 : ℤ) = (0 : ℕ) from rfl, h_nat]
  have hm : ∀ w : Word r 0, Monotone w := by
    intro w a
    exact Fin.elim0 a
  simp [weakWords, Specs.AdvancedFiniteGroupRepresentations.weakWords, hm,
    wordWeight, Specs.AdvancedFiniteGroupRepresentations.wordWeight]

theorem e_zero : ∀ r, e r 0 = 1 := by
  classical
  intro r
  rw [show (0 : ℤ) = (0 : ℕ) from rfl, e_nat]
  have hm : ∀ w : Word r 0, StrictMono w := by
    intro w a
    exact Fin.elim0 a
  simp [strictWords, Specs.AdvancedFiniteGroupRepresentations.strictWords, hm,
    wordWeight, Specs.AdvancedFiniteGroupRepresentations.wordWeight]

theorem strictWords_eq_empty : ∀ r k, r < k → strictWords r k = ∅ := by
  classical
  intro r k hk
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hi := (mem_strictWords w).mp hw
  have hc := Fintype.card_le_of_injective w hi.injective
  simp only [Fintype.card_fin] at hc
  omega

theorem e_eq_zero_of_lt_degree : ∀ (r : ℕ) (k : ℤ), (r : ℤ) < k → e r k = 0 := by
  intro r k hk
  have hpos : 0 ≤ k := by omega
  rw [e, Specs.AdvancedFiniteGroupRepresentations.e, ite_eq_right (by omega)]
  change (∑ w ∈ strictWords r k.toNat, wordWeight w) = 0
  rw [strictWords_eq_empty r k.toNat (by omega)]
  simp

theorem h_no_variables : ∀ k : ℤ, 0 < k → h 0 k = 0 := by
  classical
  intro k hk
  rw [h, Specs.AdvancedFiniteGroupRepresentations.h, ite_eq_right (by omega)]
  have he : weakWords 0 k.toNat = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w _
    exact Fin.elim0 (w ⟨0, by omega⟩)
  change (∑ w ∈ weakWords 0 k.toNat, wordWeight w) = 0
  rw [he]
  simp

theorem wordWeight_eq_monomial : ∀ {r k} (w : Word r k),
    wordWeight w = MvPolynomial.monomial (wordContent w) 1 := by
  intro r k w
  simp only [wordWeight, wordContent, Specs.AdvancedFiniteGroupRepresentations.wordWeight,
    Specs.AdvancedFiniteGroupRepresentations.wordContent, MvPolynomial.monomial_sum_one]
  rfl

theorem wordContent_apply : ∀ {r k} (w : Word r k) (a : Fin r),
    wordContent w a = (Finset.univ.filter (fun i => w i = a)).card := by
  classical
  intro r k w a
  simp [wordContent, Specs.AdvancedFiniteGroupRepresentations.wordContent,
    Finsupp.single_apply, eq_comm]

theorem mem_semistandardFillings : ∀ {n r} {p : Partition n} (t : Filling p r),
    t ∈ semistandardFillings p r ↔ IsSemistandard t := by
  classical
  intro n r p t
  simp [semistandardFillings, Specs.AdvancedFiniteGroupRepresentations.semistandardFillings]

theorem tableau_row_weak : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (a b : Cell p), a.val.1 = b.val.1 → a.val.2 ≤ b.val.2 → T.val a ≤ T.val b := by
  intro n r p T
  exact T.property.1

theorem tableau_column_strict : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (a b : Cell p), a.val.2 = b.val.2 → a.val.1 < b.val.1 → T.val a < T.val b := by
  intro n r p T
  exact T.property.2

theorem fillingWeight_eq_monomial : ∀ {n r} {p : Partition n} (t : Filling p r),
    fillingWeight t = MvPolynomial.monomial (fillingContent t) 1 := by
  intro n r p t
  simp only [fillingWeight, fillingContent, Specs.AdvancedFiniteGroupRepresentations.fillingWeight,
    Specs.AdvancedFiniteGroupRepresentations.fillingContent, MvPolynomial.monomial_sum_one]
  rfl

theorem fillingContent_apply : ∀ {n r} {p : Partition n} (t : Filling p r) (a : Fin r),
    fillingContent t a = (Finset.univ.filter (fun c => t c = a)).card := by
  classical
  intro n r p t a
  simp [fillingContent, Specs.AdvancedFiniteGroupRepresentations.fillingContent,
    Finsupp.single_apply, eq_comm]

theorem tableauWeight_eq_monomial : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r),
    tableauWeight T = MvPolynomial.monomial (tableauContent T) 1 := by
  intro n r p T
  exact fillingWeight_eq_monomial T.val

theorem entryOneBased_bounds : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (i j : ℕ) (hc : cellOneBased p i j),
    1 ≤ entryOneBased T i j hc ∧ entryOneBased T i j hc ≤ r := by
  intro n r p T i j hc
  have hb := (T.val (cellFromOneBased hc)).isLt
  change 1 ≤ _ + 1 ∧ _ + 1 ≤ r
  omega

theorem cellOneBased_succ_iff : ∀ {n} (p : Partition n) (i j : ℕ),
    cellOneBased p (i + 1) (j + 1) ↔ (i, j) ∈ cells p := by
  intro n p i j
  simp [cellOneBased, Specs.AdvancedFiniteGroupRepresentations.cellOneBased]

theorem entryOneBased_succ : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (c : Cell p) (hc : cellOneBased p (c.val.1 + 1) (c.val.2 + 1)),
    entryOneBased T (c.val.1 + 1) (c.val.2 + 1) hc = (T.val c).val + 1 := by
  intro n r p T c hc
  simp [entryOneBased, Specs.AdvancedFiniteGroupRepresentations.entryOneBased,
    Specs.AdvancedFiniteGroupRepresentations.cellFromOneBased]

theorem wordContent_total : ∀ {r k} (w : Word r k), ∑ a, wordContent w a = k := by
  classical
  intro r k w
  simp only [wordContent, Specs.AdvancedFiniteGroupRepresentations.wordContent,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

theorem fillingContent_total : ∀ {n r} {p : Partition n} (t : Filling p r),
    ∑ a, fillingContent t a = n := by
  classical
  intro n r p t
  simp only [fillingContent, Specs.AdvancedFiniteGroupRepresentations.fillingContent,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply, Cell, Specs.AdvancedFiniteGroupRepresentations.Cell]
  exact diagram_card p

theorem entryOneBased_row_weak : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (i j₁ j₂ : ℕ) (h₁ : cellOneBased p i j₁) (h₂ : cellOneBased p i j₂),
    j₁ ≤ j₂ → entryOneBased T i j₁ h₁ ≤ entryOneBased T i j₂ h₂ := by
  intro n r p T i j₁ j₂ h₁ h₂ hj
  have hl := tableau_row_weak T (cellFromOneBased h₁) (cellFromOneBased h₂)
    rfl (Nat.sub_le_sub_right hj 1)
  exact Nat.add_le_add_right hl 1

theorem entryOneBased_column_strict : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (i₁ i₂ j : ℕ) (h₁ : cellOneBased p i₁ j) (h₂ : cellOneBased p i₂ j),
    i₁ < i₂ → entryOneBased T i₁ j h₁ < entryOneBased T i₂ j h₂ := by
  intro n r p T i₁ i₂ j h₁ h₂ hi
  have hp : 0 < i₁ := h₁.1
  have hl := tableau_column_strict T (cellFromOneBased h₁) (cellFromOneBased h₂)
    rfl (show i₁ - 1 < i₂ - 1 by omega)
  exact Nat.add_lt_add_right hl 1

theorem tableau_columnLength_le : ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (j : ℕ), columnLength p j ≤ r := by
  intro n r p T j
  let f : Fin (columnLength p j) → Fin r := fun i =>
    T.val ⟨(i.val, j), (cell_iff_column p i.val j).mpr i.isLt⟩
  have hm : StrictMono f := by
    intro a b hab
    exact tableau_column_strict T _ _ rfl hab
  have hc := Fintype.card_le_of_injective f hm.injective
  simpa using hc

theorem no_tall_column_filling : ∀ {n r} {p : Partition n} (j : ℕ),
    r < columnLength p j → IsEmpty (SemistandardFilling p r) := by
  intro n r p j hj
  exact ⟨fun T => (Nat.not_le_of_lt hj) (tableau_columnLength_le T j)⟩

theorem no_filling_of_length_gt : ∀ {n r} {p : Partition n},
    r < length p → IsEmpty (SemistandardFilling p r) := by
  intro n r p hp
  apply no_tall_column_filling 0
  rwa [← length_eq_columnLength_zero]

theorem empty_filling_unique : ∀ r, ∃! T : SemistandardFilling emptyPartition r, True := by
  intro r
  have hc : IsEmpty (Cell emptyPartition) := ⟨fun c => by
    have h := c.property
    change c.val ∈ cells emptyPartition at h
    rw [empty_cells] at h
    exact Finset.notMem_empty _ h⟩
  let t : Filling emptyPartition r := fun c => isEmptyElim c
  have ht : IsSemistandard t := by
    constructor <;> intro a <;> exact isEmptyElim a
  refine ⟨⟨t, ht⟩, trivial, ?_⟩
  intro T _
  apply Subtype.ext
  funext c
  exact isEmptyElim c

theorem empty_filling_weight : ∀ {r} (t : Filling emptyPartition r), fillingWeight t = 1 := by
  intro r t
  have hc : IsEmpty (Cell emptyPartition) := ⟨fun c => by
    have h := c.property
    change c.val ∈ cells emptyPartition at h
    rw [empty_cells] at h
    exact Finset.notMem_empty _ h⟩
  simp [fillingWeight, Specs.AdvancedFiniteGroupRepresentations.fillingWeight]

theorem empty_tableauSum : ∀ r, tableauSum emptyPartition r = 1 := by
  classical
  intro r
  obtain ⟨T, _, hu⟩ := empty_filling_unique r
  have he : semistandardFillings emptyPartition r = {T.val} := by
    ext t
    rw [mem_semistandardFillings, Finset.mem_singleton]
    constructor
    · intro ht
      exact congrArg Subtype.val (hu ⟨t, ht⟩ trivial)
    · intro ht
      rw [ht]
      exact T.property
  simp [tableauSum, Specs.AdvancedFiniteGroupRepresentations.tableauSum, he, empty_filling_weight]

theorem tableauSum_eq_zero_of_length_gt : ∀ {n r} {p : Partition n},
    r < length p → tableauSum p r = 0 := by
  classical
  intro n r p hp
  have hi := no_filling_of_length_gt hp
  have he : semistandardFillings p r = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact hi.false ⟨t, (mem_semistandardFillings t).mp ht⟩
  simp [tableauSum, Specs.AdvancedFiniteGroupRepresentations.tableauSum, he]

end AdvancedFiniteGroupRepresentations
