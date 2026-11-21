import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.SumProduct
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Independent specification for the unlabelled assertion of paper.tex W20.
A fixed-length sequence is an iterated additive-size product: it records the
size and the actual object at each position. The zero-fold product has exactly
one object in degree zero. Sequences are collected over lengths at most the
total size; the length-bound and equivalence obligations below ensure that this
includes ALL finite sequences when the component class has no empty objects. -/
noncomputable section
universe v r
open scoped BigOperators
namespace Specs.FiniteCombinatorics.Classes.Sequences
open Specs.FiniteCombinatorics.Classes

def emptySequence : UnlabelledFamily.{v} where
  Obj n := ULift.{v} (Fin (if n = 0 then 1 else 0))
  finiteObj _ := inferInstance

def fixedLengthValue (A : UnlabelledFamily.{v}) : ℕ → UnlabelledFamily.{v}
  | 0 => emptySequence
  | k + 1 => SumProduct.unlabelledProductValue A (fixedLengthValue A k)
def fixedLengthType := UnlabelledFamily.{v} → ℕ → UnlabelledFamily.{v}

/-- A sequence records its length and the objects in their order. -/
def sequencesValue (A : UnlabelledFamily.{v}) : UnlabelledFamily.{v} where
  Obj n := (k : Fin (n + 1)) × (fixedLengthValue A k.val).Obj n
  finiteObj _ := inferInstance
def sequencesType := UnlabelledFamily.{v} → UnlabelledFamily.{v}

def LengthBound : Prop := ∀ (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) →
  ∀ k n, (fixedLengthValue A k).Obj n → k ≤ n

def AllSequences : Prop := ∀ (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) → ∀ n,
  Nonempty ((sequencesValue A).Obj n ≃ ((k : ℕ) × (fixedLengthValue A k).Obj n))

def LocallyFinite : Prop := ∀ (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) → ∀ n,
  Finite ((k : ℕ) × (fixedLengthValue A k).Obj n)

def FixedLengthOGF : Prop := ∀ {R : Type r} [CommRing R]
  (A : UnlabelledFamily.{v}) (k : ℕ),
  unlabelledOGFValue (R := R) (fixedLengthValue A k) = (unlabelledOGFValue A) ^ k

def EmptySequenceCount : Prop := ∀ (A : UnlabelledFamily.{v}),
  unlabelledCountValue (sequencesValue A) 0 = 1

def ConstantZero : Prop := ∀ {R : Type r} [CommRing R]
  (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) →
  PowerSeries.constantCoeff (unlabelledOGFValue (R := R) A) = 0

def PowersVanish : Prop := ∀ {R : Type r} [CommRing R]
  (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) → ∀ k n, n < k →
  PowerSeries.coeff n ((unlabelledOGFValue (R := R) A) ^ k) = 0

/-- The infinite geometric sum is interpreted coefficientwise, with finite support. -/
def GeometricCoefficients : Prop := ∀ {R : Type r} [CommRing R]
  (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) → ∀ n,
  PowerSeries.coeff n (unlabelledOGFValue (R := R) (sequencesValue A)) =
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n ((unlabelledOGFValue A) ^ k)

def InverseIdentities : Prop := ∀ {R : Type r} [CommRing R]
  (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) →
  (1 - unlabelledOGFValue (R := R) A) * unlabelledOGFValue (sequencesValue A) = 1 ∧
  unlabelledOGFValue (sequencesValue A) * (1 - unlabelledOGFValue (R := R) A) = 1

/-- Unit-based reciprocal works over arbitrary commutative coefficient rings. -/
def OGFInverse : Prop := ∀ {R : Type r} [CommRing R]
  (A : UnlabelledFamily.{v}), IsEmpty (A.Obj 0) →
  unlabelledOGFValue (R := R) (sequencesValue A) =
    PowerSeries.invOfUnit (1 - unlabelledOGFValue A) 1

end Specs.FiniteCombinatorics.Classes.Sequences
