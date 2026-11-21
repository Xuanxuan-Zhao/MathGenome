import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.IntrinsicExteriorDerivative

/-! Independent specification for the atlas part of M10.08.
The coordinate norm change is explicit: D04 uses EuclideanSpace, whereas
our intrinsic charts use Pi coordinates. No compatibility certificate is
added to D04's original objects. The pointwise tangent statement below
uses literal local extensions and a literal intrinsic parametrization.
The raw maximal-atlas condition uses local parametrization extensions and
full rank. Global availability and the tangent/form comparisons are theorem
types below; no compatibility conclusion is assumed as manifold data. -/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.EmbeddedCalculusData
open ModelData AtlasData TangentData ExteriorData
open Specs.D04.C01.EuclideanInterfaces.Model
universe u v

abbrev piCoordinates (n : ℕ) : E n ≃L[ℝ] Euclidean n :=
  EuclideanSpace.equiv (Fin n) ℝ

def ambientInclusion {N : ℕ} (M : Set (E N)) : M → Euclidean N :=
  fun p => piCoordinates N p.val

/-- Change of coordinate norm for an actual Euclidean extension. -/
def parameterExtension {n N : ℕ} (G : E n → E N) : Euclidean n → Euclidean N :=
  fun z => piCoordinates N (G ((piCoordinates n).symm z))

/-- Transport through the determinant-normalized evaluation of the exterior
power, followed by change of tangent arguments. It includes degree zero. -/
def transportCovector {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (I : V ≃ₗ[ℝ] W) (k : ℕ) (ω : Fiber V k) : W [⋀^Fin k]→ₗ[ℝ] ℝ :=
  (evaluate V k ω).compLinearMap I.symm.toLinearMap

/-- The D04 field on exactly its original C² tangent spaces. -/
def transportField {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ]
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.Tangent (k := n) M p)
    (k : ℕ) (ω : Field S k) :
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k :=
  fun p => transportCovector (I p) k (ω p)

end SmoothManifolds.EmbeddedCalculusData

namespace Specs.SmoothManifolds.Integration.EmbeddedAtlas
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.EmbeddedData _root_.SmoothManifolds.EmbeddedCalculusData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Set
universe u v

/-- Identification with D04's supremum-of-chart-ranges submodule, through the
actual inclusion differential. Raw extension agreement is required only near
the marked chart point; no derivative-compatibility assertion is assumed. -/
def tangent_identificationType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M),
    HasFullRankParametrizations S (ambientInclusion M) → n ≤ N →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
    euclideanChart N ∈ T.smoothStructure.val → ∀ (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (ambientInclusion M p))
    (F : TangentSpace T (ambientInclusion M p) ≃ₗ[ℝ] Euclidean N),
    IsDifferential S T (ambientInclusion M) p L →
    IsChartCoordinates T (ambientInclusion M p) (euclideanChart N) F →
    ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (c : EmbeddedChart 2 n N M) (u : E n) (hu : u ∈ c.source),
    c.toFun u = p.val → (e p).val = piCoordinates n u →
    ∀ (W : Set (E n)) (G : E n → E N), IsOpen W → u ∈ W →
    EqOn G c.toFun (c.source ∩ W) → DifferentiableAt ℝ G u →
    ∀ V : Set (Euclidean n),
    IsParametrizationAt (ambientInclusion M) e p V (parameterExtension G) →
    ∃ I : TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
      ∀ v, (I v).val = (piCoordinates N).symm (F (L v))

/-- A form evaluated on the identified vectors is unchanged. -/
def form_evaluationType : Prop :=
  ∀ {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (I : V ≃ₗ[ℝ] W) (k : ℕ) (ω : Fiber V k) (v : Fin k → V),
    transportCovector I k ω (fun j => I (v j)) = evaluate V k ω v

/-- No nonzero degree-zero forms are lost: transport is bijective in all
finite-dimensional degrees, including k=0 and degrees above dimension. -/
def form_bijectiveType : Prop :=
  ∀ {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (I : V ≃ₗ[ℝ] W) (k : ℕ), Function.Bijective (transportCovector I k)

/-- Algebraic restriction compatibility for the actual exterior pullback
and D04's restriction by composition of alternating maps. The commuting
square is a statement about linear maps, not a form-compatibility certificate. -/
def restriction_transportType : Prop :=
  ∀ {V W : Type u} {X Y : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (I : V ≃ₗ[ℝ] X) (J : W ≃ₗ[ℝ] Y) (L : V →ₗ[ℝ] W) (K : X →ₗ[ℝ] Y),
    (∀ v, J (L v) = K (I v)) → ∀ (k : ℕ) (ω : Fiber W k),
    transportCovector I k (FormPullbackData.fiberPullback k L ω) =
      (transportCovector J k ω).compLinearMap K

/-- The coefficient in the actual homogeneous exterior basis is the value
on the ordered intrinsic coordinate vectors, with determinant normalization. -/
def coefficient_evaluationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : BundleOperationsData.CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (p : c.source) (I : Index n k),
    coefficients C k c hc ω p I = evaluate (TangentSpace S p.val) k (ω p.val)
      (fun j => CovectorData.coordinateVector C.tangent.fiberCoordinates c hc p.val p.property
        (Set.powersetCard.ofFinEmbEquiv.symm I j))

/-- The closed supports are equal in the original common base topology. -/
def support_identificationType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ]
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.Tangent (k := n) M p)
    (k : ℕ) (ω : Field S k),
    sectionSupport (transportField S I k ω) = sectionSupport ω

/-- The actual D04 chart pullback is evaluation on the abstract coordinate
vectors. The tangent identification is specified by the genuine inclusion
differential; no chart-vector or form compatibility is assumed. Global
availability and the matching-chart specialization are specified below. -/
def chart_pullbackType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M),
    HasFullRankParametrizations S (ambientInclusion M) →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
    euclideanChart N ∈ T.smoothStructure.val →
    ∀ (C : BundleOperationsData.CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart 2 n N M) (u : E n) (hu : u ∈ c.source),
    let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
    ∀ (hp : p ∈ e.source), (e p).val = piCoordinates n u →
    ∀ (W : Set (E n)) (G : E n → E N), IsOpen W → u ∈ W →
    EqOn G c.toFun (c.source ∩ W) → DifferentiableAt ℝ G u →
    ∀ V : Set (Euclidean n),
    IsParametrizationAt (ambientInclusion M) e p V (parameterExtension G) →
    ∀ (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (ambientInclusion M p))
    (F : TangentSpace T (ambientInclusion M p) ≃ₗ[ℝ] Euclidean N),
    IsDifferential S T (ambientInclusion M) p L →
    IsChartCoordinates T (ambientInclusion M p) (euclideanChart N) F →
    ∀ I : (q : M) → TangentSpace S q ≃ₗ[ℝ]
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.Tangent (k := n) M q,
    (∀ v, (I p v).val = (piCoordinates N).symm (F (L v))) →
    (∀ w : E n,
      I p ((C.tangent.fiberCoordinates.equiv e he p hp).symm (piCoordinates n w)) =
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap c u hu w) ∧
    ∀ (k : ℕ) (ω : Field S k),
      (∀ w : Fin k → E n,
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c
          (transportField S I k ω) u w =
        evaluate (TangentSpace S p) k (ω p)
          (fun j => (C.tangent.fiberCoordinates.equiv e he p hp).symm
            (piCoordinates n (w j)))) ∧
      ∀ J : Index n k,
        Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient (standardBasis n)
          (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c
            (transportField S I k ω) u) J =
          coefficients C k e he ω ⟨p, hp⟩ J

end Specs.SmoothManifolds.Integration.EmbeddedAtlas

namespace SmoothManifolds.EmbeddedAtlasData
open ModelData AtlasData TangentData EmbeddedData EmbeddedCalculusData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open scoped ContDiff
open Set

/-- Forget regularity without changing any parametrization, domain or inverse. -/
def lowerChart {r s : ℕ∞ω} {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart r n N M) (hsr : s ≤ r) : EmbeddedChart s n N M where
  half := c.half
  half_pos := c.half_pos
  source := c.source
  source_open := c.source_open
  ambient := c.ambient
  ambient_open := c.ambient_open
  toFun := c.toFun
  invFun := c.invFun
  map_source := c.map_source
  map_target := c.map_target
  left_inv := c.left_inv
  right_inv := c.right_inv
  continuous_toFun := c.continuous_toFun
  continuous_invFun := c.continuous_invFun
  regular := by
    intro u hu
    obtain ⟨W, G, hW, huW, heq, hG, hinj⟩ := c.regular u hu
    exact ⟨W, G, hW, huW, heq, hG.of_le hsr, hinj⟩

/-- A raw chart of the induced structure: only local smooth extension of the
subset inclusion and full column rank are required. This condition contains
no tangent identification or form-compatibility assertion. -/
def IsRawEmbeddedChart {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) : Prop :=
  ∀ p ∈ e.source, ∃ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N),
    IsOpen V ∧ (e p).val ∈ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
    (fun y => H (e y).val) =ᶠ[nhds p] ambientInclusion M ∧
    Function.Injective (fderiv ℝ H (e p).val)

/-- The maximal smooth atlas consists exactly of the raw embedded charts.
The topology is the original subspace topology throughout. -/
def IsInducedSmoothStructure {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) : Prop :=
  S.smoothStructure.val = {e | IsRawEmbeddedChart e}

end SmoothManifolds.EmbeddedAtlasData

namespace Specs.SmoothManifolds.Integration.EmbeddedAtlas
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.EmbeddedData _root_.SmoothManifolds.EmbeddedCalculusData
  _root_.SmoothManifolds.EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open scoped ContDiff
open Set

def lowerChartType := {r s : ℕ∞ω} → {n N : ℕ} → {M : Set (E N)} →
  EmbeddedChart r n N M → s ≤ r → EmbeddedChart s n N M
def lowerChartValue : lowerChartType := @lowerChart

def IsRawEmbeddedChartType := {n N : ℕ} → {a : ModelKind} → {M : Set (E N)} →
  ModelChart n a M → Prop
def IsRawEmbeddedChartValue : IsRawEmbeddedChartType := @IsRawEmbeddedChart

def IsInducedSmoothStructureType := {n N : ℕ} → {a : ModelKind} → {M : Set (E N)} →
  SmoothManifold n a M → Prop
def IsInducedSmoothStructureValue : IsInducedSmoothStructureType := @IsInducedSmoothStructure

/-- Availability in the uniform half-space model, including dimension zero
and the empty manifold. -/
def induced_structure_existsType : Prop :=
  ∀ {n N : ℕ} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
    ∃ S : SmoothManifold n .halfSpace M, IsInducedSmoothStructure S

/-- The Euclidean model is available in the boundaryless case. -/
def induced_euclidean_structure_existsType : Prop :=
  ∀ {n N : ℕ} {M : Set (E N)}, IsBoundarylessEmbeddedManifold ∞ n M →
    ∃ S : SmoothManifold n .euclidean M, IsInducedSmoothStructure S

/-- Full rank is derived from the raw maximal-atlas characterization. -/
def induced_fullRankType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)} (S : SmoothManifold n a M),
    IsInducedSmoothStructure S → HasFullRankParametrizations S (ambientInclusion M)

/-- Smooth charts may be forgotten to C² charts, with literally the same
ambient tangent submodule even at the flat face. -/
def smooth_c2_tangentsType : Prop :=
  ∀ {n N : ℕ} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
    IsEmbeddedManifold 2 n M ∧ ∀ p ∈ M,
      tangentSpace ∞ n M p = tangentSpace 2 n M p

/-- These are genuine C² transitions from an arbitrary D04 C² chart to a
smooth chart. The smooth chart is forgotten to C², and no C² chart is
asserted to belong to a maximal smooth atlas. The Jacobian uses D04's
literal fderivWithin differential and the inverse derivative is included. -/
def mixed_transitionType : Prop :=
  ∀ {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart 2 n N M) (d : EmbeddedChart ∞ n N M), n ≤ N →
    let d₂ := lowerChart d (by simp : (2 : ℕ∞ω) ≤ ∞)
    ContDiffOn ℝ 2 (chartTransition c d₂) (chartOverlap c d₂) ∧
    (∀ u ∈ chartOverlap c d₂,
      ∃ (W : Set (E n)) (H : E n → E n), IsOpen W ∧ u ∈ W ∧
        ContDiffOn ℝ 2 H W ∧ EqOn H (chartTransition c d₂) (chartOverlap c d₂ ∩ W)) ∧
    ∀ u ∈ chartOverlap c d₂, ∃ A : E n ≃L[ℝ] E n,
      HasFDerivWithinAt (chartTransition c d₂) A.toContinuousLinearMap
        (chartOverlap c d₂) u ∧
      HasFDerivWithinAt (chartTransition d₂ c) A.symm.toContinuousLinearMap
        (chartOverlap d₂ c) (chartTransition c d₂ u) ∧
      chartDifferential c u = (chartDifferential d (chartTransition c d₂ u)).comp
        A.toContinuousLinearMap

/-- Uniqueness of the induced linear map once its ambient inclusion is
specified. No choice of chart can change a subtype element with that value. -/
def tangent_identification_uniqueType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (p : M)
    (I J : TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val),
    (∀ v, (I v).val = (J v).val) → I = J

end Specs.SmoothManifolds.Integration.EmbeddedAtlas

namespace SmoothManifolds.EmbeddedAtlasData
open ModelData AtlasData TangentData DifferentialData EmbeddedData EmbeddedCalculusData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Set

/-- Characterization by the genuine inclusion differential in every ambient
standard-chart realization. This is a conclusion to prove, not manifold data. -/
def IsInclusionIdentification {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val) : Prop :=
  ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
    euclideanChart N ∈ T.smoothStructure.val → ∀ (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (ambientInclusion M p))
    (F : TangentSpace T (ambientInclusion M p) ≃ₗ[ℝ] Euclidean N),
    IsDifferential S T (ambientInclusion M) p L →
    IsChartCoordinates T (ambientInclusion M p) (euclideanChart N) F →
    ∀ v, (I p v).val = (piCoordinates N).symm (F (L v))

/-- Literal raw agreement with a parametrization. No differential or form
identity is part of this condition. -/
def MatchesEmbeddedChart {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (c : EmbeddedChart (⊤ : ℕ∞) n N M) : Prop :=
  ∀ p ∈ e.source, p.val ∈ c.ambient ∧ (e p).val = piCoordinates n (c.invFun p.val)

end SmoothManifolds.EmbeddedAtlasData

namespace Specs.SmoothManifolds.Integration.EmbeddedAtlas
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.EmbeddedData _root_.SmoothManifolds.EmbeddedCalculusData
  _root_.SmoothManifolds.EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open scoped ContDiff
open Set

def IsInclusionIdentificationType := {n N : ℕ} → {a : ModelKind} → {M : Set (E N)} →
  (S : SmoothManifold n a M) →
  ((p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val) → Prop
def IsInclusionIdentificationValue : IsInclusionIdentificationType := @IsInclusionIdentification

def MatchesEmbeddedChartType := {n N : ℕ} → {a : ModelKind} → {M : Set (E N)} →
  ModelChart n a M → EmbeddedChart ∞ n N M → Prop
def MatchesEmbeddedChartValue : MatchesEmbeddedChartType := @MatchesEmbeddedChart

/-- Once the induced structure is available, the inclusion constructs a
unique family of isomorphisms with D04's actual C² tangent spaces. No matching
chart hypothesis is needed, and all ambient differential choices agree. -/
def induced_tangent_identificationType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
    ∀ S : SmoothManifold n a M, IsInducedSmoothStructure S →
    ∃! I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
      IsInclusionIdentification S I

/-- Literal chart-vector, pullback and ordered coefficient formulas on every
matching smooth parametrization. Smooth local extensions are supplied by the
original D04 EmbeddedChart; they are not extra hypotheses. -/
def matching_chart_pullbackType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val),
    IsInclusionIdentification S I →
    ∀ (C : BundleOperationsData.CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val),
    ∀ c : EmbeddedChart ∞ n N M, MatchesEmbeddedChart e c →
    ∀ (u : E n) (hu : u ∈ c.source),
    let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
    ∀ hp : p ∈ e.source,
    let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
    (∀ w : E n,
      I p ((C.tangent.fiberCoordinates.equiv e he p hp).symm
        (piCoordinates n w)) =
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap c₂ u hu w) ∧
    ∀ (k : ℕ) (η : ExteriorData.Field S k),
      (∀ w : Fin k → E n,
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂
          (transportField S I k η) u w =
        ExteriorData.evaluate (TangentSpace S p) k (η p)
          (fun j => (C.tangent.fiberCoordinates.equiv e he p hp).symm
            (piCoordinates n (w j)))) ∧
      ∀ J : ExteriorData.Index n k,
        Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient (standardBasis n)
          (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c₂
            (transportField S I k η) u) J =
          ExteriorData.coefficients C k e he η ⟨p, hp⟩ J

end Specs.SmoothManifolds.Integration.EmbeddedAtlas

namespace Specs.SmoothManifolds.Integration.EmbeddedAtlas
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.EmbeddedData _root_.SmoothManifolds.EmbeddedCalculusData
  _root_.SmoothManifolds.EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Set
universe u v

def piCoordinatesType := (n : ℕ) → E n ≃L[ℝ] Euclidean n
def piCoordinatesValue : piCoordinatesType := piCoordinates

def ambientInclusionType := {N : ℕ} → (M : Set (E N)) → M → Euclidean N
def ambientInclusionValue : ambientInclusionType := @ambientInclusion

def parameterExtensionType := {n N : ℕ} → (E n → E N) → Euclidean n → Euclidean N
def parameterExtensionValue : parameterExtensionType := @parameterExtension

def transportCovectorType := {V : Type u} → {W : Type v} →
  [AddCommGroup V] → [Module ℝ V] → [AddCommGroup W] → [Module ℝ W] →
  (V ≃ₗ[ℝ] W) → (k : ℕ) → Fiber V k → W [⋀^Fin k]→ₗ[ℝ] ℝ
def transportCovectorValue : transportCovectorType.{u,v} := @transportCovector

def transportFieldType := {n N : ℕ} → {a : ModelKind} → {M : Set (E N)} →
  (S : SmoothManifold n a M) →
  ((p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val) →
  (k : ℕ) → Field S k →
  Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm (k := n) M k
def transportFieldValue : transportFieldType := @transportField

def transportField_bijectiveType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)} (S : SmoothManifold n a M)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val) (k : ℕ),
    Function.Bijective (transportField S I k)

def raw_chart_inverseType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M), IsRawEmbeddedChart e → ∀ p ∈ e.source,
    LocalCoordinateExtension (⊤ : ℕ∞) (ambientInclusion M) (fun y => (e y).val) p

def induced_model_equivalenceType : Prop :=
  ∀ {n N : ℕ} {a b : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (T : SmoothManifold n b M),
    IsInducedSmoothStructure S → IsInducedSmoothStructure T →
    IsSmoothMap S T id ∧ IsSmoothMap T S id

def induced_structure_of_raw_coverType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)},
    IsAtlas {e : ModelChart n a M | IsRawEmbeddedChart e} →
    ∃ S : SmoothManifold n a M, IsInducedSmoothStructure S

def euclidean_chart_of_embeddedType : Prop :=
  ∀ {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart (⊤ : ℕ∞) n N M), c.half = false → ∀ p₀ : M,
    ∃ e : ModelChart n .euclidean M,
      e.source = {p : M | p.val ∈ c.ambient} ∧
      IsRawEmbeddedChart e ∧ MatchesEmbeddedChart e c

/-- The half-space convention in dimension zero is also available without
an assumption that the embedded set is nonempty. -/
def induced_zero_structure_existsType : Prop :=
  ∀ {N : ℕ} {M : Set (E N)}, IsEmbeddedManifold (⊤ : ℕ∞) 0 M →
    ∃ S : SmoothManifold 0 .halfSpace M, IsInducedSmoothStructure S

end Specs.SmoothManifolds.Integration.EmbeddedAtlas
