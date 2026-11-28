import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.BialgebraDeformation.FirstOrder
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.BialgebraDeformation.SkewPrimitiveHopf
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Basic

open scoped TensorProduct

namespace LieNotes.BialgebraDeformation

open PowerSeries

noncomputable section

universe u v

variable {k : Type u} [Field k]

/-- The canonical two coefficients, with the formal parameter sent to the dual-number epsilon. -/
def firstOrderSeries {A : Type v} [CommRing A] [Algebra k A] :
    PowerSeries A → Extended k A :=
  fun p => (1 : D k) ⊗ₜ[k] constantCoeff p + (DualNumber.eps : D k) ⊗ₜ[k] coeff 1 p

/-- The coefficient of the formal parameter in the coproduct of a constant series. -/
def firstOrderPlaneComul [CharZero k] (H : CompletedPlaneHopf k) :
    Plane k →ₗ[k] PlaneTensorSquare k :=
  ((PowerSeries.coeff 1).restrictScalars k).comp (onSeriesConstants H.comul).toLinearMap

/-- The primitive degree-one subspace of the coefficient algebra. -/
def PrimitiveDegreeOne (k : Type u) [Field k] : Submodule k (Plane k) :=
  Submodule.span k (Set.range (MvPolynomial.X : Fin 2 → Plane k))

def primitiveDegreeOneGenerator (i : Fin 2) : PrimitiveDegreeOne k :=
  ⟨MvPolynomial.X i, Submodule.subset_span ⟨i, rfl⟩⟩

instance : LieRing (PrimitiveDegreeOne k) where
  bracket _ _ := 0
  add_lie _ _ _ := (zero_add _).symm
  lie_add _ _ _ := (zero_add _).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (zero_add _).symm

instance : LieAlgebra k (PrimitiveDegreeOne k) where
  lie_smul t _ _ := (smul_zero t).symm

namespace Expected

/-- The scalar extension presentation of reduction modulo the square of the formal parameter. -/
def firstOrderSeries : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A],
    let q := BialgebraDeformation.firstOrderSeries (k := k) (A := A)
    Function.Surjective q ∧
    (∀ p r : PowerSeries A, q p = q r ↔ p - r ∈ seriesVariableIdeal A ^ 2) ∧
    (∀ p r, q (p + r) = q p + q r) ∧
    (∀ p r, q (p * r) = q p * q r) ∧
    q 1 = 1 ∧ q X = (DualNumber.eps : D k) ⊗ₜ[k] (1 : A) ∧
    ∀ (p : PowerSeries k) (r : PowerSeries A),
      q (algebraMap (PowerSeries k) (PowerSeries A) p * r) =
        scalarCoordinates k (BialgebraDeformation.firstOrderSeries (k := k) p) • q r

/-- Reduction respects the canonical pairing of the two completed tensor factors. -/
def firstOrderTensor : Prop :=
  ∀ (k : Type u) (A B : Type*) [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B],
    ∀ (p : PowerSeries A) (r : PowerSeries B),
      (tensorComparison (k := k) (X := A) (Y := B)).symm
        (BialgebraDeformation.firstOrderSeries (k := k) p ⊗ₜ[D k]
          BialgebraDeformation.firstOrderSeries (k := k) r) =
      BialgebraDeformation.firstOrderSeries (k := k) (seriesTensorPair (k := k) p r)

/-- The completed structure, its actual first-order reduction, and the skew cobracket. -/
def nontrivialPolynomial : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ H : CompletedPlaneHopf k,
      let g := firstOrderPlaneComul H
      (∀ p, BialgebraDeformation.firstOrderSeries (k := k) (H.comul p) =
        jet (primitivePlaneComul (k := k)).toLinearMap g
          (BialgebraDeformation.firstOrderSeries p)) ∧
      (∀ p, BialgebraDeformation.firstOrderSeries (k := k) (H.counit p) =
        jet (primitivePlaneCounit (k := k)).toLinearMap 0
          (BialgebraDeformation.firstOrderSeries p)) ∧
      g planeX = 0 ∧ g planeY = planeX ⊗ₜ[k] planeY ∧
      (∃ b : Bialgebra k (Plane k), b.toAlgebra = (inferInstance : Algebra k (Plane k)) ∧
        letI := b
        (∀ p : Plane k, HEq (comul k (Plane k) p) (primitivePlaneComul p) ∧
          counit k (Plane k) p = primitivePlaneCounit p) ∧
        ∃ deformation trivial : Deformation k (Plane k),
          deformation.f = 0 ∧ HEq deformation.g g ∧
          trivial.f = 0 ∧ trivial.g = 0 ∧ ¬ Equivalent deformation trivial) ∧
      (∃ basis : Module.Basis (Fin 2) k (PrimitiveDegreeOne k),
        ∀ i, basis i = primitiveDegreeOneGenerator i) ∧
      (∀ v : PrimitiveDegreeOne k,
        primitivePlaneComul (v : Plane k) = (v : Plane k) ⊗ₜ[k] 1 + 1 ⊗ₜ[k] (v : Plane k)) ∧
      ∃ δ : PrimitiveDegreeOne k →ₗ[k] ⋀[k]^2 (PrimitiveDegreeOne k),
        δ (primitiveDegreeOneGenerator 0) = 0 ∧
        δ (primitiveDegreeOneGenerator 1) =
          Specs.LieNotes.Coboundary.wedge₂Value (primitiveDegreeOneGenerator 0) (primitiveDegreeOneGenerator 1) ∧
        Specs.LieNotes.Coboundary.isLieBialgebraCobracketValue δ ∧
        ∀ v : PrimitiveDegreeOne k,
          TensorProduct.map (PrimitiveDegreeOne k).subtype (PrimitiveDegreeOne k).subtype
            (Specs.LieNotes.Coboundary.alternatingTensorValue (δ v)) =
            g v - (TensorProduct.comm k (Plane k) (Plane k)) (g v)

end Expected

end

end LieNotes.BialgebraDeformation
