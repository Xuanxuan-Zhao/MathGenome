import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitModel

/-! Removal of the diagonal parameters for the split octonion input in NA13-C04.04. -/

namespace LinearAlgebraicGroups.Albert.RemoveParametersSpecification

open _root_.LinearAlgebraicGroups.Composition
open Composition.Specification (OctonionNormConditions)
open HermitianSpecification CubicSpecification LowerRankSpecification SplitSpecification
open QuadraticOperatorSpecification (applyOperator)
open Composition.Specification (normBaseChange)
open scoped TensorProduct
open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)

universe u v

variable {R : Type u} [CommRing R]

/-- Scaling of the four Zorn slots in the block opposite the diagonal index `i`. -/
def blockScaling (γ : Fin 3 → Rˣ) (i : Fin 3) : Zorn R ≃ₗ[R] Zorn R :=
  (Zorn.coordinates R).trans <|
    ((LinearEquiv.smulOfUnit (M := R) (γ i)).prodCongr <|
      (LinearEquiv.smulOfUnit (M := Fin 3 → R) (γ (cyclicNext i))).prodCongr <|
      (LinearEquiv.smulOfUnit (M := Fin 3 → R) (γ (cyclicPrev i))).prodCongr <|
      LinearEquiv.smulOfUnit (M := R) (γ (cyclicNext i) * γ (cyclicPrev i) * (γ i)⁻¹)).trans
      (Zorn.coordinates R).symm

abbrev Model (R : Type u) := Coordinates R (Zorn R)

/-- Leave the three diagonal entries fixed and scale the three off-diagonal blocks. -/
def removeZornWeights (γ : Fin 3 → Rˣ) : Model R ≃ₗ[R] Model R :=
  (LinearEquiv.refl R _).prodCongr (LinearEquiv.piCongrRight (blockScaling γ))

def RemoveZornWeightsType :=
  ∀ {R : Type u} [CommRing R], (Fin 3 → Rˣ) → Model R ≃ₗ[R] Model R

/-- Compatibility of the weighted and untwisted cubic norms after scalar extension. -/
def PreservesCubicNormAfterBaseChange (γ : Fin 3 → Rˣ) (F : Model R ≃ₗ[R] Model R) : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] (x : S ⊗[R] Model R),
    let q := normBaseChange S (zornNorm R)
    let e := coordinatesBaseChange (A := Zorn R) S
    cubicNorm q (untwisted S) (e (F.toLinearMap.baseChange S x)) =
      cubicNorm q (baseChangedWeights S γ) (e x)

def ZornWeightRemovalType : Prop :=
  ∀ (R : Type u) [CommRing R] (γ : Fin 3 → Rˣ),
    let F := removeZornWeights γ
    let n := zornNorm R
    let δ := untwisted R
    F cubicUnit = cubicUnit ∧
    (∀ x, cubicNorm n δ (F x) = cubicNorm n γ x) ∧
    PreservesCubicNormAfterBaseChange.{u, v} γ F ∧
    (∀ x y, tracePairing n δ (F x) (F y) = tracePairing n γ x y) ∧
    (∀ x, linearTrace n δ (F x) = linearTrace n γ x) ∧
    (∀ x, quadraticTrace n δ (F x) = quadraticTrace n γ x) ∧
    (∀ x, F (cubicAdjoint n γ x) = cubicAdjoint n δ (F x)) ∧
    (∀ x y, F (applyOperator n γ x y) = applyOperator n δ (F x) (F y)) ∧
    ∃ (h : OctonionNormConditions n) (J K : QuadraticJordan R (Model R)),
      IsReducedModel h γ (ParaQuadratic.ofJordan J) ∧
      IsReducedModel h δ (ParaQuadratic.ofJordan K) ∧
      (ParaQuadratic.ofJordan J).IsIso (ParaQuadratic.ofJordan K) F

end LinearAlgebraicGroups.Albert.RemoveParametersSpecification
