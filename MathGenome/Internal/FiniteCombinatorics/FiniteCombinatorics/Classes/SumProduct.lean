import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.SumProduct
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Classes.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.CoefficientAlgebra
import Mathlib.Data.Nat.Choose.Sum

/-! Disjoint sum and additive-size product, paper.tex p204:W19.
The labelled constructions below operate on the actual finite label set.
Their series are the shared EGFs of their object counts on standard labels. -/
noncomputable section
universe u v w r
open scoped BigOperators
namespace FiniteCombinatorics.Classes

def unlabelledSum (A : UnlabelledClass.{v}) (B : UnlabelledClass.{w}) :
    UnlabelledClass.{max v w} :=
  Specs.FiniteCombinatorics.Classes.SumProduct.unlabelledSumValue A B
def unlabelledProduct (A : UnlabelledClass.{v}) (B : UnlabelledClass.{w}) :
    UnlabelledClass.{max v w} :=
  Specs.FiniteCombinatorics.Classes.SumProduct.unlabelledProductValue A B
abbrev LabelledSumObjects := Specs.FiniteCombinatorics.Classes.SumProduct.labelledSumObjectsValue

def labelledSumCount (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) (n : ℕ) : ℕ :=
  Nat.card (LabelledSumObjects A B (StandardLabels.{u} n))
def labelledProductCount (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) (n : ℕ) : ℕ :=
  Nat.card (LabelledProductObjects A B (StandardLabels.{u} n))
def labelledSumEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) : PowerSeries R :=
  Series.egf (fun n => (labelledSumCount A B n : R))
def labelledProductEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) : PowerSeries R :=
  Series.egf (fun n => (labelledProductCount A B n : R))

theorem unlabelledSum_count (A : UnlabelledClass.{v}) (B : UnlabelledClass.{w}) (n : ℕ) :
    (unlabelledSum A B).count n = A.count n + B.count n := by
  exact Nat.card_sum

theorem unlabelledProduct_count (A : UnlabelledClass.{v}) (B : UnlabelledClass.{w}) (n : ℕ) :
    (unlabelledProduct A B).count n =
      ∑ i ∈ Finset.range (n + 1), A.count i * B.count (n - i) := by
  change Nat.card ((i : Fin (n + 1)) × (A.Obj i.val × B.Obj (n - i.val))) = _
  simp only [Nat.card_sigma, Nat.card_prod, UnlabelledClass.count]
  exact Fin.sum_univ_eq_sum_range
    (fun i => Nat.card (A.Obj i) * Nat.card (B.Obj (n - i))) (n + 1)

theorem unlabelledSum_ogf {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (B : UnlabelledClass.{w}) :
    (unlabelledSum A B).ogf (R := R) = A.ogf + B.ogf := by
  apply PowerSeries.ext
  intro n
  simp [unlabelledSum_count]

theorem unlabelledProduct_ogf {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (B : UnlabelledClass.{w}) :
    (unlabelledProduct A B).ogf (R := R) = A.ogf * B.ogf := by
  apply PowerSeries.ext
  intro n
  simp only [UnlabelledClass.coeff_ogf, Series.coeff_mul, unlabelledProduct_count,
    Nat.cast_sum, Nat.cast_mul]

theorem labelledSum_card (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w})
    (S : Type u) [Finite S] :
    Nat.card (LabelledSumObjects A B S) = A.count (Nat.card S) + B.count (Nat.card S) := by
  rw [LabelledSumObjects, Specs.FiniteCombinatorics.Classes.SumProduct.labelledSumObjectsValue,
    Nat.card_sum, A.card_on_labels, B.card_on_labels]

theorem labelledProduct_card (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w})
    (S : Type u) [Finite S] :
    Nat.card (LabelledProductObjects A B S) =
      ∑ i ∈ Finset.range (Nat.card S + 1),
        Nat.choose (Nat.card S) i * A.count i * B.count (Nat.card S - i) := by
  classical
  let := Fintype.ofFinite S
  change Nat.card ((L : Finset S) × (A.Obj ↥L × B.Obj ↥(Lᶜ))) = _
  -- Sum the independent choices on each actual complementary pair of subsets.
  rw [Nat.card_sigma]
  simp only [Nat.card_prod, A.card_on_labels, B.card_on_labels,
    Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl]
  -- The summand now depends only on the left subset's size.
  rw [← Finset.powerset_univ]
  rw [Finset.sum_powerset_apply_card (fun k => A.count k * B.count (Fintype.card S - k))]
  simp only [Finset.card_univ, nsmul_eq_mul, Nat.cast_id, mul_assoc]

theorem labelledSum_count (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) (n : ℕ) :
    labelledSumCount A B n = A.count n + B.count n := by
  simpa only [labelledSumCount, card_standardLabels] using
    labelledSum_card A B (StandardLabels.{u} n)

theorem labelledProduct_count (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) (n : ℕ) :
    labelledProductCount A B n = ∑ i ∈ Finset.range (n + 1),
      Nat.choose n i * A.count i * B.count (n - i) := by
  simpa only [labelledProductCount, card_standardLabels] using
    labelledProduct_card A B (StandardLabels.{u} n)

theorem labelledSum_egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) :
    labelledSumEGF (R := R) A B = A.egf + B.egf := by
  apply PowerSeries.ext
  intro n
  simp [labelledSumEGF, labelledSum_count, add_mul]

theorem labelledProduct_egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w}) :
    labelledProductEGF (R := R) A B = A.egf * B.egf := by
  rw [LabelledClass.egf, LabelledClass.egf, Series.egf_mul]
  unfold labelledProductEGF
  congr 1
  funext n
  simp only [labelledProduct_count, Nat.cast_sum, Nat.cast_mul]

end FiniteCombinatorics.Classes
