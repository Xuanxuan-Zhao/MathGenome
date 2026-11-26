import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.Smooth.Basic

namespace Specs.CommutativeAlgebraNotes.CoefficientRings.FieldFormalSmoothness

universe u v

/-- Every field is formally smooth over its prime subfield. -/
def primeSubfieldFormallySmooth : Prop :=
  ∀ (L : Type u) [Field L], Algebra.FormallySmooth (↥(⊥ : Subfield L)) L

/-- Infinitesimal lifting over the prime subfield, with an arbitrary target ring. -/
def primeSubfieldSquareZeroLift : Prop :=
  ∀ (L : Type u) [Field L] (T : Type v) [CommRing T] [Algebra (↥(⊥ : Subfield L)) T]
    (N : Ideal T), N ^ 2 = ⊥ →
    ∀ f : L →ₐ[↥(⊥ : Subfield L)] T ⧸ N,
      ∃ g : L →ₐ[↥(⊥ : Subfield L)] T,
        (Ideal.Quotient.mkₐ (↥(⊥ : Subfield L)) N).comp g = f

end Specs.CommutativeAlgebraNotes.CoefficientRings.FieldFormalSmoothness
