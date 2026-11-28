import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.BialgebraDeformation.CompletedPolynomialMaps
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic

open scoped TensorProduct

namespace LieNotes.BialgebraDeformation

open PowerSeries

noncomputable section

section Coefficients

variable {k : Type*} [Field k]

/-- The two polynomial generators in the order used for the deformation. -/
abbrev planeX : Plane k := MvPolynomial.X 0
abbrev planeY : Plane k := MvPolynomial.X 1

/-- The coefficientwise form of the series `exp(ta)`. -/
def parameterExp {A : Type*} [CommRing A] [Algebra k A] (a : A) : PowerSeries A :=
  PowerSeries.mk fun n => a ^ n * algebraMap k A (1 / (n.factorial : k))

/-- The ordinary coproduct for which the two polynomial variables are primitive. -/
def primitivePlaneComul : Plane k →ₐ[k] PlaneTensorSquare k :=
  MvPolynomial.aeval fun i => MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i

/-- The ordinary counit is evaluation at the origin. -/
def primitivePlaneCounit : Plane k →ₐ[k] k :=
  MvPolynomial.aeval fun _ => 0

/-- The ordinary antipode acts by negation on both generators. -/
def primitivePlaneAntipode : Plane k →ₐ[k] Plane k :=
  MvPolynomial.aeval fun i => -MvPolynomial.X i

/-- Restrict a formal scalar algebra map to its constant series. -/
def onSeriesConstants {A D : Type*} [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]
    (f : PowerSeries A →ₐ[PowerSeries k] PowerSeries D) : A →ₐ[k] PowerSeries D :=
  (restrictSeriesMap f).comp (seriesConstants k A)

/-- A completed map induced by multiplication of the values of two leg maps. -/
def ExtendsSeriesProduct {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
    [Algebra k A] [Algebra k B] [Algebra k D]
    (f : PowerSeries A →ₐ[PowerSeries k] PowerSeries D)
    (g : PowerSeries B →ₐ[PowerSeries k] PowerSeries D)
    (F : PowerSeries (A ⊗[k] B) →ₐ[PowerSeries k] PowerSeries D) : Prop :=
  ExtendsSeriesMap (Algebra.TensorProduct.productMap (onSeriesConstants f) (onSeriesConstants g)) F

/-- The scalar unit of the completed polynomial algebra. -/
def completedPlaneUnit : PowerSeries k →ₐ[PowerSeries k] PowerSeries (Plane k) :=
  seriesMap (Algebra.ofId k (Plane k))

/-- The completed tensor leg with a map on the left and the identity on the right. -/
def ExtendsLeftPlaneTensor {D : Type*} [CommRing D] [Algebra k D]
    (f : PowerSeries (Plane k) →ₐ[PowerSeries k] PowerSeries D)
    (F : PowerSeries (PlaneTensorSquare k) →ₐ[PowerSeries k] PowerSeries (D ⊗[k] Plane k)) :
    Prop :=
  ExtendsSeriesMap (tensorSeriesCoefficient (onSeriesConstants f) (seriesConstants k (Plane k))) F

/-- The completed tensor leg with the identity on the left and a map on the right. -/
def ExtendsRightPlaneTensor {D : Type*} [CommRing D] [Algebra k D]
    (f : PowerSeries (Plane k) →ₐ[PowerSeries k] PowerSeries D)
    (F : PowerSeries (PlaneTensorSquare k) →ₐ[PowerSeries k] PowerSeries (Plane k ⊗[k] D)) :
    Prop :=
  ExtendsSeriesMap (tensorSeriesCoefficient (seriesConstants k (Plane k)) (onSeriesConstants f)) F

end Coefficients

section Hopf

variable (k : Type*) [Field k] [CharZero k]

/-- The continuous Hopf operations on the ordinary Cauchy algebra `k[x,y][[t]]`.
The coproduct squares and cubes use the canonical completed tensor models. -/
structure CompletedPlaneHopf where
  comul : PowerSeries (Plane k) →ₐ[PowerSeries k] PowerSeries (PlaneTensorSquare k)
  counit : PowerSeries (Plane k) →ₐ[PowerSeries k] PowerSeries k
  antipode : PowerSeries (Plane k) →ₐ[PowerSeries k] PowerSeries (Plane k)
  comul_continuous : SeriesContinuous comul
  counit_continuous : SeriesContinuous counit
  antipode_continuous : SeriesContinuous antipode
  comul_x : comul (C planeX) = seriesTensorPair (k := k) (C planeX) 1 + seriesTensorPair (k := k) 1 (C planeX)
  comul_y : comul (C planeY) = seriesTensorPair (k := k) (C planeY) 1 +
    seriesTensorPair (k := k) (parameterExp (k := k) planeX) (C planeY)
  counit_x : counit (C planeX) = 0
  counit_y : counit (C planeY) = 0
  antipode_x : antipode (C planeX) = -C planeX
  antipode_y : antipode (C planeY) = -parameterExp (k := k) (-planeX) * C planeY
  exp_groupLike : comul (parameterExp (k := k) planeX) =
    seriesTensorPair (k := k) (parameterExp (k := k) planeX) (parameterExp (k := k) planeX)
  counit_exp : counit (parameterExp (k := k) planeX) = 1
  coassociative :
    ∃ L : PowerSeries (PlaneTensorSquare k) →ₐ[PowerSeries k] PowerSeries (PlaneTensorCube k),
    ∃ R : PowerSeries (PlaneTensorSquare k) →ₐ[PowerSeries k] PowerSeries (PlaneTensorCubeRight k),
      ExtendsLeftPlaneTensor comul L ∧ ExtendsRightPlaneTensor comul R ∧
      ∀ p, seriesMap (k := k)
        (Algebra.TensorProduct.assoc k k k (Plane k) (Plane k) (Plane k)).toAlgHom
        (L (comul p)) = R (comul p)
  left_counit :
    ∃ F, ExtendsSeriesProduct ((completedPlaneUnit (k := k)).comp counit) (AlgHom.id _ _) F ∧
      F.comp comul = AlgHom.id _ _
  right_counit :
    ∃ F, ExtendsSeriesProduct (AlgHom.id _ _) ((completedPlaneUnit (k := k)).comp counit) F ∧
      F.comp comul = AlgHom.id _ _
  left_antipode :
    ∃ F, ExtendsSeriesProduct antipode (AlgHom.id _ _) F ∧
      F.comp comul = (completedPlaneUnit (k := k)).comp counit
  right_antipode :
    ∃ F, ExtendsSeriesProduct (AlgHom.id _ _) antipode F ∧
      F.comp comul = (completedPlaneUnit (k := k)).comp counit
  specialize_comul (p : PowerSeries (Plane k)) :
    constantCoeff (comul p) = primitivePlaneComul (constantCoeff p)
  specialize_counit (p : PowerSeries (Plane k)) :
    constantCoeff (counit p) = primitivePlaneCounit (constantCoeff p)
  specialize_antipode (p : PowerSeries (Plane k)) :
    constantCoeff (antipode p) = primitivePlaneAntipode (constantCoeff p)
  primitive_hopf :
    ∃ H : HopfAlgebra k (Plane k),
      H.toBialgebra.toAlgebra = (inferInstance : Algebra k (Plane k)) ∧
      letI := H
      let Q := H.toBialgebra.toCoalgebra.toCoalgebraStruct
      ∀ p : Plane k,
        HEq (Q.comul p) (primitivePlaneComul p) ∧
        Q.counit p = primitivePlaneCounit p ∧
        HopfAlgebra.antipode k p = primitivePlaneAntipode p
  primitive_cocommutative :
    (Algebra.TensorProduct.comm k (Plane k) (Plane k)).toAlgHom.comp primitivePlaneComul =
      primitivePlaneComul

def CompletedPlaneHopfSpec : Prop :=
  ∀ (k : Type*) [Field k] [CharZero k], Nonempty (CompletedPlaneHopf k)

end Hopf

end

end LieNotes.BialgebraDeformation
