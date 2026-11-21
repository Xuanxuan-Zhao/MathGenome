import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedAtlas
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedBoundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedDerivative

/-! M10.08: the calculus comparison on the common smooth embedded domain.
The shared objects and the complete component propositions are those of the
accepted atlas, boundary and derivative interfaces. In particular their D04
objects are the actual chart-range tangent submodules, alternating forms,
outward conormals, signed zero-dimensional orientations, and within derivatives.
The component types below are transparent aliases of full independent Props;
no comparison conclusion is assumed as additional manifold data.
The final statements assemble the canonical identification, every-chart formula,
and agreement with the smooth derivative family and the intrinsic C¹ selector.
-/
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace Specs.SmoothManifolds.Integration.EmbeddedCalculus
universe u v

def tangent_identificationType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.tangent_identificationType

def form_evaluationType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.form_evaluationType.{u,v}

def form_bijectiveType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.form_bijectiveType.{u,v}

def restriction_transportType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.restriction_transportType.{u,v}

def coefficient_evaluationType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.coefficient_evaluationType.{u}

def support_identificationType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.support_identificationType

def chart_pullbackType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.chart_pullbackType

def induced_structure_existsType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_structure_existsType

def induced_euclidean_structure_existsType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_euclidean_structure_existsType

def induced_tangent_identificationType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_tangent_identificationType

def matching_chart_pullbackType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.matching_chart_pullbackType

def transportField_bijectiveType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedAtlas.transportField_bijectiveType

def boundary_setType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_setType

def boundary_baseType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_baseType

def boundary_zeroType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_zeroType

def boundary_geometryType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_geometryType

def boundary_tangent_hyperplaneType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_tangent_hyperplaneType

def boundary_outward_raysType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_outward_raysType

def boundary_restrictionType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_restrictionType

def orientation_transportType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.orientation_transportType

def zero_orientation_transportType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.zero_orientation_transportType

def boundary_orientationType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_orientationType

def boundary_point_comparisonType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.boundary_point_comparisonType

def interval_comparisonType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.interval_comparisonType

def interval_positiveType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedBoundary.interval_positiveType

def regularity_transportType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedDerivative.regularity_transportType

def continuous_transportType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedDerivative.continuous_transportType

def hasDerivative_transportType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedDerivative.hasDerivative_transportType

def intrinsicExteriorDerivative_transportType : Prop :=
  Specs.SmoothManifolds.Integration.EmbeddedDerivative.intrinsicExteriorDerivative_transportType

open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.EmbeddedCalculusData _root_.SmoothManifolds.EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model

/-- One canonical identification simultaneously gives the all-degree bijection,
support, continuity, C¹ regularity, and the two literal derivative relations.
There are no supplied chart or differential compatibility hypotheses. -/
def common_domainType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
  ∀ S : SmoothManifold n a M, IsInducedSmoothStructure S →
  ∃! I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I ∧
    (∀ k, Function.Bijective (transportField S I k)) ∧
    (∀ (k : ℕ) (ξ : Field S k),
      sectionSupport (transportField S I k ξ) = sectionSupport ξ) ∧
    (∀ (C : CotangentBundle S) (k : ℕ) (ξ : Field S k),
      IsRegularField C 1 k ξ ↔
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicC1
          (transportField S I k ξ)) ∧
    (∀ (C : CotangentBundle S) (k : ℕ) (ξ : Field S k),
      IsContinuousField C k ξ ↔
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicContinuous
          (transportField S I k ξ)) ∧
    (∀ (C : CotangentBundle S) (k : ℕ) (ξ : Field S k) (η : Field S (k+1)),
      IsRegularField C 1 k ξ →
      (HasExteriorDerivative C ξ η ↔
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicContinuous
          (transportField S I (k+1) η) ∧
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.HasIntrinsicExteriorDerivative
          (transportField S I k ξ) (transportField S I (k+1) η))) ∧
    (∀ (C : CotangentBundle S) (k : ℕ) (ξ : Field S k),
      IsRegularField C 1 k ξ →
      ∃! η : Field S (k+1), IsContinuousField C (k+1) η ∧
        HasExteriorDerivative C ξ η ∧ transportField S I (k+1) η =
          Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
            (transportField S I k ξ))

/-- Every intrinsic chart of the actual induced structure has a genuine smooth
D04 parametrization. Its coordinate vectors, full alternating pullback and
ordered coefficients agree without supplying any raw extension data. -/
def every_chart_pullbackType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M), IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I →
  ∀ (C : CotangentBundle S) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val),
  ∃ c : EmbeddedChart ∞ n N M, MatchesEmbeddedChart e c ∧
    ∀ (u : E n) (hu : u ∈ c.source),
    let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
    ∃ hp : p ∈ e.source,
    let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
    (∀ w : E n,
      I p ((C.tangent.fiberCoordinates.equiv e he p hp).symm
        (piCoordinates n w)) =
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap c₂ u hu w) ∧
    ∀ (k : ℕ) (ξ : Field S k),
      (∀ w : Fin k → E n,
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂
          (transportField S I k ξ) u w =
        evaluate (TangentSpace S p) k (ξ p)
          (fun j => (C.tangent.fiberCoordinates.equiv e he p hp).symm
            (piCoordinates n (w j)))) ∧
      ∀ J : Index n k,
        Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient (standardBasis n)
          (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂
            (transportField S I k ξ) u) J = coefficients C k e he ξ ⟨p, hp⟩ J

/-- Existence, uniqueness and D04 agreement for the actual real-linear smooth
exterior-derivative family. Its characterizing axioms are conclusions. -/
def smooth_operator_comparisonType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
  ∀ S : SmoothManifold n a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
    IsInclusionIdentification S I →
  ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k),
  ∃ D : ∀ k, Field S k → Field S (k+1), DerivativeAxioms C B D ∧
    (∀ E, DerivativeAxioms C B E → ∀ k ξ, IsForm (B k) ξ → D k ξ = E k ξ) ∧
    ∀ k ξ, IsForm (B k) ξ →
      transportField S I (k+1) (D k ξ) =
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
          (transportField S I k ξ)

/-- At degree zero the scalar unit and every scalar value are preserved,
including on zero-dimensional tangent spaces. -/
def degree_zero_transportType : Prop :=
  ∀ {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (I : V ≃ₗ[ℝ] W) (r : ℝ) (w : Fin 0 → W),
    transportCovector I 0
      ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).symm r) w = r

/-- Zero-dimensional tangents are zero, scalar fields remain unrestricted,
all fields are regular, all derivatives vanish, and positive-degree forms
vanish. The empty base is included. -/
def zero_dimension_comparisonType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ 0 M →
  ∀ S : SmoothManifold 0 a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 0 M p.val,
    IsInclusionIdentification S I → ∀ C : CotangentBundle S,
    (∀ p : M, tangentSpace 2 0 M p.val = ⊥ ∧
      ∀ v : TangentSpace S p, v = 0) ∧
    (∀ (k : ℕ) (ξ : Field S k), IsRegularField C 1 k ξ ∧
      HasExteriorDerivative C ξ 0 ∧
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
        (transportField S I k ξ) = fun _ => 0) ∧
    (∀ (k : ℕ), 0 < k → ∀ ξ : Field S k, ξ = 0)

end Specs.SmoothManifolds.Integration.EmbeddedCalculus
