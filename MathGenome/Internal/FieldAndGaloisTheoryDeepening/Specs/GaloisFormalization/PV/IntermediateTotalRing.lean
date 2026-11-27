import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.TransitiveProductProjectionKernels
import Mathlib.RingTheory.FiniteType

namespace GaloisFormalization.PV.Specs

open scoped nonZeroDivisors

universe u v

set_option linter.checkUnivs false in
def isIntermediateTotalRingType :=
  {kind : OperatorKind} → {k : Type u} → {Q : Type v} →
    [Field k] → [CommRing Q] → [Algebra k Q] →
    operator kind Q → Subalgebra k Q → Prop

/-- An intermediate operator algebra that is already its own total ring of fractions. -/
def isIntermediateTotalRing : isIntermediateTotalRingType.{u, v} := fun T F =>
  isStable T (F : Set _) ∧ ProjectionKernels.RegularElementsAreUnits (F : Type v)

set_option linter.checkUnivs false in
def relativePicardVessiotSubalgebraType :=
  {k : Type u} → {Q : Type v} → [Field k] → [CommRing Q] → [Algebra k Q] →
    {n : ℕ} → (F : Subalgebra k Q) → Matrix.GeneralLinearGroup (Fin n) Q →
    Subalgebra (F : Type v) Q

/-- The ring generated inside the total extension by the entries of the given
matrix and the inverse of its determinant, with coefficients in the intermediate ring. -/
def relativePicardVessiotSubalgebra : relativePicardVessiotSubalgebraType.{u, v} :=
  fun F Y => matrixGeneratedSubalgebra (F : Type v) Y

/-- The field structure in each operator case, including the transport maps
between factors in the difference case. -/
def intermediateFieldStructure {S : Type v} [CommRing S] {kind : OperatorKind} :
    operator kind S → Prop :=
  match kind with
  | .differential => fun _ => IsField S
  | .difference => fun σ =>
    ∃ (ι : Type v) (L : ι → Type v) (hL : ∀ j, Field (L j)),
      letI := hL
      Finite ι ∧ Nonempty ι ∧
      ∃ (e : S ≃+* (∀ j, L j)) (p : Equiv.Perm ι) (f : ∀ j, L j ≃+* L (p j)),
        ProjectionKernels.Transitive p ∧
        ∀ x j, e ((toRingEquiv σ) x) (p j) = f j (e x j)

/-- Lemma 2.3 with all the inclusions taken inside the given total extension. -/
def intermediateTotalRingStructure : Prop :=
  ∀ {kind : OperatorKind} {k : Type u} {R : Type v}
    [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (D : operatorField kind k) (A : linearSystem kind k n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R))
    (Y : Matrix.GeneralLinearGroup (Fin n) R),
    isBaseField D → isPicardVessiotTotalExtension D A E T → isFundamental A E Y →
    ∀ (F : Subalgebra k (totalQuotientRing R)), isIntermediateTotalRing T F →
      let Q := totalQuotientRing R
      let B := relativePicardVessiotSubalgebra F
        (Matrix.GeneralLinearGroup.map (algebraMap R Q) Y)
      ∃ (D_F : operator kind (F : Type v)) (E_B : operator kind (B : Type v))
        (i : R →+* (B : Type v)) (hDF : isExtension D D_F),
        isExtension D_F T ∧
        isExtension D_F E_B ∧
        isExtension E_B T ∧
        commutes E E_B i ∧
        (∀ r, (i r : Q) = algebraMap R Q r) ∧
        Function.Bijective (mapConstants (D := D) (E := D_F) ⟨algebraMap k F, hDF.1⟩) ∧
        intermediateFieldStructure D_F ∧
        Algebra.FiniteType (F : Type v) (B : Type v) ∧
        IsNoetherianRing (B : Type v) ∧
        (∀ x : B, x ∈ (B : Type v)⁰ ↔ IsUnit (x : Q)) ∧
        (∀ r : R, r ∈ R⁰ → i r ∈ (B : Type v)⁰) ∧
        IsFractionRing (B : Type v) Q

end GaloisFormalization.PV.Specs
