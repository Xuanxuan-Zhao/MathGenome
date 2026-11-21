import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.Foundations
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Nat.Choose.Basic

/-! Independent specification for paper.tex, Proposition p204:W19.
Products are defined by their objects, never by their counting formulas.
In particular the labelled product is the shared sigma type of complementary
subsets. All sizes, including zero, are allowed. -/
noncomputable section
universe u v w r
open scoped BigOperators
namespace Specs.FiniteCombinatorics.Classes.SumProduct
open Specs.FiniteCombinatorics.Classes

/-- Tagged disjoint union at each size. -/
def unlabelledSumValue (A : UnlabelledFamily.{v}) (B : UnlabelledFamily.{w}) :
    UnlabelledFamily.{max v w} where
  Obj n := A.Obj n ⊕ B.Obj n
  finiteObj _ := inferInstance

def unlabelledSumType := UnlabelledFamily.{v} → UnlabelledFamily.{w} →
  UnlabelledFamily.{max v w}

/-- A pair with additive total size; the first size is recorded explicitly. -/
def unlabelledProductValue (A : UnlabelledFamily.{v}) (B : UnlabelledFamily.{w}) :
    UnlabelledFamily.{max v w} where
  Obj n := (i : Fin (n + 1)) × (A.Obj i.val × B.Obj (n - i.val))
  finiteObj _ := inferInstance

def unlabelledProductType := UnlabelledFamily.{v} → UnlabelledFamily.{w} →
  UnlabelledFamily.{max v w}

/-- Tags keep the two summands disjoint on the same finite label set. -/
def labelledSumObjectsValue (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w})
    (S : Type u) [Finite S] : Type (max v w) := A.Obj S ⊕ B.Obj S

def labelledSumObjectsType := LabelledFamily.{u,v} → LabelledFamily.{u,w} →
  (S : Type u) → [Finite S] → Type (max v w)

/-- Count actual objects on the fixed n-element label set. -/
def labelledSumCountValue (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w})
    (n : ℕ) : ℕ := Nat.card (labelledSumObjectsValue A B (standardLabelsValue n))
def labelledProductCountValue (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w})
    (n : ℕ) : ℕ := Nat.card (productObjectsValue A B (standardLabelsValue n))
def labelledCountType := LabelledFamily.{u,v} → LabelledFamily.{u,w} → ℕ → ℕ

def labelledSumEGFValue {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w}) : PowerSeries R :=
  Series.egfValue (fun n => (labelledSumCountValue A B n : R))
def labelledProductEGFValue {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w}) : PowerSeries R :=
  Series.egfValue (fun n => (labelledProductCountValue A B n : R))
def labelledEGFType := ∀ {R : Type r} [CommRing R] [Algebra ℚ R],
  LabelledFamily.{u,v} → LabelledFamily.{u,w} → PowerSeries R

def UnlabelledSumCount : Prop := ∀ (A : UnlabelledFamily.{v})
    (B : UnlabelledFamily.{w}) (n : ℕ),
  unlabelledCountValue (unlabelledSumValue A B) n =
    unlabelledCountValue A n + unlabelledCountValue B n

def UnlabelledProductCount : Prop := ∀ (A : UnlabelledFamily.{v})
    (B : UnlabelledFamily.{w}) (n : ℕ),
  unlabelledCountValue (unlabelledProductValue A B) n =
    ∑ i ∈ Finset.range (n + 1), unlabelledCountValue A i * unlabelledCountValue B (n - i)

def UnlabelledSumOGF : Prop := ∀ {R : Type r} [CommRing R]
    (A : UnlabelledFamily.{v}) (B : UnlabelledFamily.{w}),
  unlabelledOGFValue (R := R) (unlabelledSumValue A B) =
    unlabelledOGFValue A + unlabelledOGFValue B

def UnlabelledProductOGF : Prop := ∀ {R : Type r} [CommRing R]
    (A : UnlabelledFamily.{v}) (B : UnlabelledFamily.{w}),
  unlabelledOGFValue (R := R) (unlabelledProductValue A B) =
    unlabelledOGFValue A * unlabelledOGFValue B

/-- Formulas on every finite label set also establish independence of its names. -/
def LabelledSumCard : Prop := ∀ (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w})
    (S : Type u) [Finite S],
  Nat.card (labelledSumObjectsValue A B S) =
    labelledCountValue A (Nat.card S) + labelledCountValue B (Nat.card S)

def LabelledProductCard : Prop := ∀ (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w})
    (S : Type u) [Finite S],
  Nat.card (productObjectsValue A B S) =
    ∑ i ∈ Finset.range (Nat.card S + 1),
      Nat.choose (Nat.card S) i * labelledCountValue A i * labelledCountValue B (Nat.card S - i)

def LabelledSumCount : Prop := ∀ (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w}) (n : ℕ),
  labelledSumCountValue A B n = labelledCountValue A n + labelledCountValue B n

def LabelledProductCount : Prop := ∀ (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w}) (n : ℕ),
  labelledProductCountValue A B n = ∑ i ∈ Finset.range (n + 1),
    Nat.choose n i * labelledCountValue A i * labelledCountValue B (n - i)

def LabelledSumEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w}),
  labelledSumEGFValue (R := R) A B = labelledEGFValue A + labelledEGFValue B

def LabelledProductEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w}),
  labelledProductEGFValue (R := R) A B = labelledEGFValue A * labelledEGFValue B

end Specs.FiniteCombinatorics.Classes.SumProduct
