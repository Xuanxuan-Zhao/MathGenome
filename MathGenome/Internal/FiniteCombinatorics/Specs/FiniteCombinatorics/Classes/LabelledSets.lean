import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.Foundations
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution

/-! Independent specification of the labelled SET assertion of p204:W20.
The unordered objects are the shared actual label-block partitions. An order is
a bijection from `Fin k` to the blocks, not an order on component isomorphism
types. Thus structurally identical components on different blocks stay distinct.
The formal exponential means substitution into `PowerSeries.exp`.
The hypothesis `labelledCountValue A 0 = 0` says exactly that there are no
size-zero objects: all the object types are finite, and all empty label types
are bijective to the standard empty label type.
-/
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v r
open scoped BigOperators
namespace Specs.FiniteCombinatorics.Classes.LabelledSets
open Specs.FiniteCombinatorics.Classes

def fixedObjectsValue (A : LabelledFamily.{u,v}) (k : ℕ) (S : Type u) [Finite S] :
    Type (max u v) :=
  {x : componentObjectsValue A S // x.1.parts.card = k}
def fixedObjectsType := LabelledFamily.{u,v} → ℕ → (S : Type u) → [Finite S] →
  Type (max u v)

def orderedObjectsValue (A : LabelledFamily.{u,v}) (k : ℕ) (S : Type u) [Finite S] :
    Type (max u v) :=
  (x : fixedObjectsValue A k S) × (Fin k ≃ x.1.1.parts)
def orderedObjectsType := LabelledFamily.{u,v} → ℕ → (S : Type u) → [Finite S] →
  Type (max u v)

def fixedCountValue (A : LabelledFamily.{u,v}) (k n : ℕ) : ℕ :=
  Nat.card (fixedObjectsValue A k (standardLabelsValue n))
def setCountValue (A : LabelledFamily.{u,v}) (n : ℕ) : ℕ :=
  Nat.card (componentObjectsValue A (standardLabelsValue n))
def orderedCountValue (A : LabelledFamily.{u,v}) (k n : ℕ) : ℕ :=
  Nat.card (orderedObjectsValue A k (standardLabelsValue n))
def fixedCountType := LabelledFamily.{u,v} → ℕ → ℕ → ℕ
def setCountType := LabelledFamily.{u,v} → ℕ → ℕ

def fixedEGFValue {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledFamily.{u,v}) (k : ℕ) : PowerSeries R :=
  Series.egfValue (fun n => (fixedCountValue A k n : R))
def setEGFValue {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledFamily.{u,v}) : PowerSeries R :=
  Series.egfValue (fun n => (setCountValue A n : R))
def orderedEGFValue {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledFamily.{u,v}) (k : ℕ) : PowerSeries R :=
  Series.egfValue (fun n => (orderedCountValue A k n : R))
def fixedEGFType := ∀ {R : Type r} [CommRing R] [Algebra ℚ R],
  LabelledFamily.{u,v} → ℕ → PowerSeries R
def setEGFType := ∀ {R : Type r} [CommRing R] [Algebra ℚ R],
  LabelledFamily.{u,v} → PowerSeries R

def FixedFinite : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S], Finite (fixedObjectsValue A k S)
def SetFinite : Prop := ∀ (A : LabelledFamily.{u,v})
  (S : Type u) [Finite S], Finite (componentObjectsValue A S)
def OrderedFinite : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S], Finite (orderedObjectsValue A k S)

/-- Every particular unordered object has exactly `k!` orders of its blocks. -/
def OrdersCard : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S] (x : fixedObjectsValue A k S),
  Nat.card (Fin k ≃ x.1.1.parts) = k.factorial
def OrderedCard : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S],
  Nat.card (orderedObjectsValue A k S) = k.factorial * Nat.card (fixedObjectsValue A k S)
def FixedAbove : Prop := ∀ (A : LabelledFamily.{u,v}) (k n : ℕ),
  n < k → fixedCountValue A k n = 0
def TotalCount : Prop := ∀ (A : LabelledFamily.{u,v}) (n : ℕ),
  setCountValue A n = ∑ k ∈ Finset.range (n + 1), fixedCountValue A k n
def EmptyCount : Prop := ∀ (A : LabelledFamily.{u,v}), setCountValue A 0 = 1
def FixedZeroCount : Prop := ∀ (A : LabelledFamily.{u,v}) (n : ℕ),
  fixedCountValue A 0 n = if n = 0 then 1 else 0
def FixedZeroEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), fixedEGFValue (R := R) A 0 = 1

/-- The orders exhaust the ordinary ordered labelled tuples; this is not a
definition of the ordered count by a power-series coefficient. -/
def OrderedEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), labelledCountValue A 0 = 0 → ∀ k,
  orderedEGFValue (R := R) A k = labelledEGFValue A ^ k
def FixedEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), labelledCountValue A 0 = 0 → ∀ k,
  fixedEGFValue (R := R) A k =
    PowerSeries.C (algebraMap ℚ R ((k.factorial : ℚ)⁻¹)) * labelledEGFValue A ^ k
def SetEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), labelledCountValue A 0 = 0 →
  setEGFValue (R := R) A = (PowerSeries.exp R).subst (labelledEGFValue A)

end Specs.FiniteCombinatorics.Classes.LabelledSets
