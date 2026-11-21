import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Partitions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic

/-! FR, Chapter 3, lines 975–993. Finite alphabets use zero-based labels;
printed labels are their successors. A filling is defined on diagram cells
only, so no values outside the diagram, or unbounded tableau entries, occur. -/
open scoped BigOperators

namespace Specs.AdvancedFiniteGroupRepresentations

abbrev PolynomialRing (r : ℕ) := MvPolynomial (Fin r) ℂ
abbrev Word (r k : ℕ) := Fin k → Fin r

noncomputable def weakWords (r k : ℕ) : Finset (Word r k) := by
  classical
  exact Finset.univ.filter Monotone

noncomputable def strictWords (r k : ℕ) : Finset (Word r k) := by
  classical
  exact Finset.univ.filter StrictMono

noncomputable def wordWeight {r k : ℕ} (w : Word r k) : PolynomialRing r :=
  ∏ i, MvPolynomial.X (w i)

noncomputable def wordContent {r k : ℕ} (w : Word r k) : Fin r →₀ ℕ :=
  ∑ i, Finsupp.single (w i) 1

noncomputable def h (r : ℕ) (k : ℤ) : PolynomialRing r :=
  if k < 0 then 0 else ∑ w ∈ weakWords r k.toNat, wordWeight w

noncomputable def e (r : ℕ) (k : ℤ) : PolynomialRing r :=
  if k < 0 then 0 else ∑ w ∈ strictWords r k.toNat, wordWeight w

abbrev Filling {n : ℕ} (p : Partition n) (r : ℕ) := Cell p → Fin r

/-- Weak along each row and strict down each column, on the actual cells. -/
def IsSemistandard {n r : ℕ} {p : Partition n} (t : Filling p r) : Prop :=
  (∀ a b : Cell p, a.val.1 = b.val.1 → a.val.2 ≤ b.val.2 → t a ≤ t b) ∧
  (∀ a b : Cell p, a.val.2 = b.val.2 → a.val.1 < b.val.1 → t a < t b)

abbrev SemistandardFilling {n : ℕ} (p : Partition n) (r : ℕ) :=
  {t : Filling p r // IsSemistandard t}

noncomputable def semistandardFillings {n : ℕ} (p : Partition n) (r : ℕ) :
    Finset (Filling p r) := by
  classical
  exact Finset.univ.filter IsSemistandard

noncomputable def fillingWeight {n r : ℕ} {p : Partition n} (t : Filling p r) :
    PolynomialRing r := ∏ c, MvPolynomial.X (t c)

noncomputable def fillingContent {n r : ℕ} {p : Partition n} (t : Filling p r) :
    Fin r →₀ ℕ := ∑ c, Finsupp.single (t c) 1

noncomputable def tableauWeight {n r : ℕ} {p : Partition n}
    (T : SemistandardFilling p r) : PolynomialRing r := fillingWeight T.val

noncomputable def tableauContent {n r : ℕ} {p : Partition n}
    (T : SemistandardFilling p r) : Fin r →₀ ℕ := fillingContent T.val

noncomputable def tableauSum {n : ℕ} (p : Partition n) (r : ℕ) : PolynomialRing r :=
  ∑ t ∈ semistandardFillings p r, fillingWeight t

/-- Translate positive printed coordinates to zero-based cells. -/
def cellFromOneBased {n : ℕ} {p : Partition n} {i j : ℕ}
    (hc : cellOneBased p i j) : Cell p := ⟨(i - 1, j - 1), hc.2.2⟩

/-- Printed entries lie in {1,...,r}. -/
def entryOneBased {n r : ℕ} {p : Partition n} (T : SemistandardFilling p r)
    (i j : ℕ) (hc : cellOneBased p i j) : ℕ :=
  (T.val (cellFromOneBased hc)).val + 1

def PolynomialRingType := ℕ → Type

def WordType := ℕ → ℕ → Type

def weakWordsType := (r k : ℕ) → Finset (Word r k)

def strictWordsType := (r k : ℕ) → Finset (Word r k)

def wordWeightType := {r k : ℕ} → Word r k → PolynomialRing r

def wordContentType := {r k : ℕ} → Word r k → (Fin r →₀ ℕ)

def hType := (r : ℕ) → ℤ → PolynomialRing r

def eType := (r : ℕ) → ℤ → PolynomialRing r

def FillingType := {n : ℕ} → Partition n → ℕ → Type

def IsSemistandardType := {n r : ℕ} → {p : Partition n} → Filling p r → Prop

def SemistandardFillingType := {n : ℕ} → Partition n → ℕ → Type

def semistandardFillingsType := {n : ℕ} → (p : Partition n) → (r : ℕ) → Finset (Filling p r)

def fillingWeightType := {n r : ℕ} → {p : Partition n} → Filling p r → PolynomialRing r

def fillingContentType := {n r : ℕ} → {p : Partition n} → Filling p r → (Fin r →₀ ℕ)

def tableauWeightType := {n r : ℕ} → {p : Partition n} → SemistandardFilling p r → PolynomialRing r

def tableauContentType := {n r : ℕ} → {p : Partition n} → SemistandardFilling p r → (Fin r →₀ ℕ)

def tableauSumType := {n : ℕ} → (p : Partition n) → (r : ℕ) → PolynomialRing r

def cellFromOneBasedType := {n : ℕ} → {p : Partition n} → {i j : ℕ} → cellOneBased p i j → Cell p

def entryOneBasedType := {n r : ℕ} → {p : Partition n} → SemistandardFilling p r → (i j : ℕ) → cellOneBased p i j → ℕ

def mem_weakWordsType : Prop :=
  ∀ {r k} (w : Word r k), w ∈ weakWords r k ↔ Monotone w

def mem_strictWordsType : Prop :=
  ∀ {r k} (w : Word r k), w ∈ strictWords r k ↔ StrictMono w

def h_natType : Prop :=
  ∀ r k : ℕ, h r (k : ℤ) = ∑ w ∈ weakWords r k, wordWeight w

def e_natType : Prop :=
  ∀ r k : ℕ, e r (k : ℤ) = ∑ w ∈ strictWords r k, wordWeight w

def h_negType : Prop :=
  ∀ (r : ℕ) (k : ℤ), k < 0 → h r k = 0

def e_negType : Prop :=
  ∀ (r : ℕ) (k : ℤ), k < 0 → e r k = 0

def h_zeroType : Prop :=
  ∀ r, h r 0 = 1

def e_zeroType : Prop :=
  ∀ r, e r 0 = 1

def strictWords_eq_emptyType : Prop :=
  ∀ r k, r < k → strictWords r k = ∅

def e_eq_zero_of_lt_degreeType : Prop :=
  ∀ (r : ℕ) (k : ℤ), (r : ℤ) < k → e r k = 0

def h_no_variablesType : Prop :=
  ∀ k : ℤ, 0 < k → h 0 k = 0

def wordWeight_eq_monomialType : Prop :=
  ∀ {r k} (w : Word r k),
    wordWeight w = MvPolynomial.monomial (wordContent w) 1

def wordContent_applyType : Prop :=
  ∀ {r k} (w : Word r k) (a : Fin r),
    wordContent w a = (Finset.univ.filter (fun i => w i = a)).card

def mem_semistandardFillingsType : Prop :=
  ∀ {n r} {p : Partition n} (t : Filling p r),
    t ∈ semistandardFillings p r ↔ IsSemistandard t

def tableau_row_weakType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (a b : Cell p), a.val.1 = b.val.1 → a.val.2 ≤ b.val.2 → T.val a ≤ T.val b

def tableau_column_strictType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (a b : Cell p), a.val.2 = b.val.2 → a.val.1 < b.val.1 → T.val a < T.val b

def fillingWeight_eq_monomialType : Prop :=
  ∀ {n r} {p : Partition n} (t : Filling p r),
    fillingWeight t = MvPolynomial.monomial (fillingContent t) 1

def fillingContent_applyType : Prop :=
  ∀ {n r} {p : Partition n} (t : Filling p r) (a : Fin r),
    fillingContent t a = (Finset.univ.filter (fun c => t c = a)).card

def tableauWeight_eq_monomialType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r),
    tableauWeight T = MvPolynomial.monomial (tableauContent T) 1

def entryOneBased_boundsType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (i j : ℕ) (hc : cellOneBased p i j),
    1 ≤ entryOneBased T i j hc ∧ entryOneBased T i j hc ≤ r

def cellOneBased_succ_iffType : Prop :=
  ∀ {n} (p : Partition n) (i j : ℕ),
    cellOneBased p (i + 1) (j + 1) ↔ (i, j) ∈ cells p

def entryOneBased_succType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (c : Cell p) (hc : cellOneBased p (c.val.1 + 1) (c.val.2 + 1)),
    entryOneBased T (c.val.1 + 1) (c.val.2 + 1) hc = (T.val c).val + 1

def wordContent_totalType : Prop :=
  ∀ {r k} (w : Word r k), ∑ a, wordContent w a = k

def fillingContent_totalType : Prop :=
  ∀ {n r} {p : Partition n} (t : Filling p r),
    ∑ a, fillingContent t a = n

def entryOneBased_row_weakType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (i j₁ j₂ : ℕ) (h₁ : cellOneBased p i j₁) (h₂ : cellOneBased p i j₂),
    j₁ ≤ j₂ → entryOneBased T i j₁ h₁ ≤ entryOneBased T i j₂ h₂

def entryOneBased_column_strictType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (i₁ i₂ j : ℕ) (h₁ : cellOneBased p i₁ j) (h₂ : cellOneBased p i₂ j),
    i₁ < i₂ → entryOneBased T i₁ j h₁ < entryOneBased T i₂ j h₂

def tableau_columnLength_leType : Prop :=
  ∀ {n r} {p : Partition n} (T : SemistandardFilling p r)
    (j : ℕ), columnLength p j ≤ r

def no_tall_column_fillingType : Prop :=
  ∀ {n r} {p : Partition n} (j : ℕ),
    r < columnLength p j → IsEmpty (SemistandardFilling p r)

def no_filling_of_length_gtType : Prop :=
  ∀ {n r} {p : Partition n},
    r < length p → IsEmpty (SemistandardFilling p r)

def empty_filling_uniqueType : Prop :=
  ∀ r, ∃! T : SemistandardFilling emptyPartition r, True

def empty_filling_weightType : Prop :=
  ∀ {r} (t : Filling emptyPartition r), fillingWeight t = 1

def empty_tableauSumType : Prop :=
  ∀ r, tableauSum emptyPartition r = 1

def tableauSum_eq_zero_of_length_gtType : Prop :=
  ∀ {n r} {p : Partition n},
    r < length p → tableauSum p r = 0

end Specs.AdvancedFiniteGroupRepresentations
