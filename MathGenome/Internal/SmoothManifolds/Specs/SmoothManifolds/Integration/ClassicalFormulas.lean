import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClassicalIntegralIdentifications
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClassicalBoundaryGeometry
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Stokes
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix

/-! Coordinate calculations for paper.tex:1927–1940.
The coordinate forms and intrinsic applications use the same determinant
normalization and genuine inclusion differentials.
The coordinate forms use determinant-normalized alternating evaluation.
Within-set derivatives allow arbitrary ambient representatives off the domain;
the theorems explicitly require uniqueness of differentiation at the point.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators Matrix

namespace SmoothManifolds.ClassicalData
open ModelData

def frame (n : ℕ) (i : Fin n) : Euclidean n := Pi.single i 1

/-- The standard determinant volume, evaluated on ordered ROWS of vectors.
Transposition gives the equivalent ordered-column convention. -/
def volume (n : ℕ) : (Euclidean n) [⋀^Fin n]→L[ℝ] ℝ :=
  { (Matrix.detRowAlternating : AlternatingMap ℝ (Euclidean n) ℝ (Fin n)) with
    cont := continuous_id.matrix_det }

/-- First-slot insertion, as in the source's convention for ι_X. -/
def fluxForm {n : ℕ} (X : Euclidean (n+1) → Euclidean (n+1)) :
    Euclidean (n+1) → (Euclidean (n+1)) [⋀^Fin n]→L[ℝ] ℝ :=
  fun x => (volume (n+1)).curryLeft (X x)

/-- The linear coefficient-to-one-form map; no derivative is built into it. -/
def oneFormMap (n : ℕ) : Euclidean n →L[ℝ] (Euclidean n) [⋀^Fin 1]→L[ℝ] ℝ :=
  ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight
    (ContinuousAlternatingMap.ofSubsingleton ℝ (Euclidean n) ℝ (0 : Fin 1)
      (ContinuousLinearMap.proj i))

def oneForm {n : ℕ} (A : Euclidean n → Euclidean n) :
    Euclidean n → (Euclidean n) [⋀^Fin 1]→L[ℝ] ℝ := fun x => oneFormMap n (A x)

def partialWithin {n : ℕ} (s : Set (Euclidean n))
    (A : Euclidean n → Euclidean n) (x : Euclidean n) (i j : Fin n) : ℝ :=
  fderivWithin ℝ A s x (frame n i) j

def divergenceWithin {n : ℕ} (s : Set (Euclidean n))
    (X : Euclidean n → Euclidean n) (x : Euclidean n) : ℝ :=
  ∑ i : Fin n, partialWithin s X x i i

def curlWithin (s : Set (Euclidean 3)) (A : Euclidean 3 → Euclidean 3)
    (x : Euclidean 3) : Euclidean 3 :=
  ![partialWithin s A x 1 2 - partialWithin s A x 2 1,
    partialWithin s A x 2 0 - partialWithin s A x 0 2,
    partialWithin s A x 0 1 - partialWithin s A x 1 0]

/-- The Euclidean area of the parallelogram, from the induced Gram metric. -/
def surfaceArea (u v : Euclidean 3) : ℝ :=
  Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v)^2)

/-- Normal compatible with the ordered tangent pair. It is a unit vector when
the pair is independent; the zero default at dependent pairs is explicit. -/
def frameNormal (u v : Euclidean 3) : Euclidean 3 :=
  (surfaceArea u v)⁻¹ • (u ⨯₃ v)

end SmoothManifolds.ClassicalData

namespace Specs.SmoothManifolds.Integration.ClassicalFormulas
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.ClassicalData

def oneForm_applyType : Prop :=
  ∀ {n : ℕ} (A : Euclidean n → Euclidean n) (x v : Euclidean n),
    oneForm A x (fun _ => v) = A x ⬝ᵥ v

def oneForm_derivativeType : Prop :=
  ∀ {n : ℕ} (s : Set (Euclidean n)) (A : Euclidean n → Euclidean n)
    (x u v : Euclidean n),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ A s x →
    extDerivWithin (oneForm A) s x ![u, v] =
      (fderivWithin ℝ A s x u) ⬝ᵥ v - (fderivWithin ℝ A s x v) ⬝ᵥ u

def green_coefficientType : Prop :=
  ∀ (s : Set (Euclidean 2)) (A : Euclidean 2 → Euclidean 2) (x : Euclidean 2),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ A s x →
    extDerivWithin (oneForm A) s x (frame 2) =
      partialWithin s A x 0 1 - partialWithin s A x 1 0

def curl_coefficientType : Prop :=
  ∀ (s : Set (Euclidean 3)) (A : Euclidean 3 → Euclidean 3) (x u v : Euclidean 3),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ A s x →
    extDerivWithin (oneForm A) s x ![u, v] = curlWithin s A x ⬝ᵥ (u ⨯₃ v)

def flux_omitted_coefficientType : Prop :=
  ∀ (n : ℕ) (X : Euclidean (n+1) → Euclidean (n+1))
    (x : Euclidean (n+1)) (i : Fin (n+1)),
    fluxForm X x (i.removeNth (frame (n+1))) = (-1 : ℝ)^i.val * X x i

def divergence_coefficientType : Prop :=
  ∀ (n : ℕ) (s : Set (Euclidean (n+1))) (X : Euclidean (n+1) → Euclidean (n+1))
    (x : Euclidean (n+1)),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ X s x →
    extDerivWithin (fluxForm X) s x (frame (n+1)) = divergenceWithin s X x

def green_formType : Prop :=
  ∀ (s : Set (Euclidean 2)) (A : Euclidean 2 → Euclidean 2) (x : Euclidean 2),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ A s x →
    extDerivWithin (oneForm A) s x =
      (partialWithin s A x 0 1 - partialWithin s A x 1 0) • volume 2

def divergence_formType : Prop :=
  ∀ (n : ℕ) (s : Set (Euclidean (n+1))) (X : Euclidean (n+1) → Euclidean (n+1))
    (x : Euclidean (n+1)),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ X s x →
    extDerivWithin (fluxForm X) s x = divergenceWithin s X x • volume (n+1)

def frame_normalType : Prop :=
  ∀ (u v : Euclidean 3), u ⨯₃ v ≠ 0 →
    0 < surfaceArea u v ∧
    frameNormal u v ⬝ᵥ frameNormal u v = 1 ∧
    u ⬝ᵥ frameNormal u v = 0 ∧ v ⬝ᵥ frameNormal u v = 0 ∧
    u ⨯₃ v = surfaceArea u v • frameNormal u v

/-- The actual normal/Gram-area coefficient in a regular parametrization.
The intrinsic metric and orientation are identified in the global surface statement below. -/
def curl_normal_areaType : Prop :=
  ∀ (s : Set (Euclidean 3)) (A : Euclidean 3 → Euclidean 3) (x u v : Euclidean 3),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ A s x → u ⨯₃ v ≠ 0 →
    extDerivWithin (oneForm A) s x ![u, v] =
      (curlWithin s A x ⬝ᵥ frameNormal u v) * surfaceArea u v

def curl_formType : Prop :=
  ∀ (s : Set (Euclidean 3)) (A : Euclidean 3 → Euclidean 3) (x : Euclidean 3),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ A s x →
    extDerivWithin (oneForm A) s x = fluxForm (curlWithin s A) x

/-- Normal/area formula after the actual linear pullback by a parametrization
differential. Its normalization is the square root of the induced Gram
determinant, rather than a supplied scalar named “area”. -/
def curl_pullbackType : Prop :=
  ∀ (s : Set (Euclidean 3)) (A : Euclidean 3 → Euclidean 3) (x : Euclidean 3)
    (L : Euclidean 2 →L[ℝ] Euclidean 3),
    UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ A s x →
    (L (frame 2 0)) ⨯₃ (L (frame 2 1)) ≠ 0 →
    (extDerivWithin (oneForm A) s x).compContinuousLinearMap L =
      ((curlWithin s A x ⬝ᵥ frameNormal (L (frame 2 0)) (L (frame 2 1))) *
        surfaceArea (L (frame 2 0)) (L (frame 2 1))) • volume 2

/-- The pointwise flux identity on every tuple tangent to the unit normal's
orthogonal hyperplane, including the empty tuple when the bulk dimension is one.
For an outward unit normal, the normal-first factor on the right is precisely
the boundary area form, as proved in the regular-domain applications below. -/
def normal_fluxType : Prop :=
  ∀ (n : ℕ) (X ν : Euclidean (n+1)) (v : Fin n → Euclidean (n+1)),
    ν ⬝ᵥ ν = 1 → (∀ i, v i ⬝ᵥ ν = 0) →
    volume (n+1) (Matrix.vecCons X v) =
      (X ⬝ᵥ ν) * volume (n+1) (Matrix.vecCons ν v)

end Specs.SmoothManifolds.Integration.ClassicalFormulas


namespace SmoothManifolds.ClassicalData
open ModelData AtlasData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData ClassicalIntegralData ClassicalBoundaryData
open scoped Topology

/-- The canonical geometric data of a regular Euclidean domain, with all
normal, metric and orientation assertions retained as conclusions of existence. -/
structure DomainGeometry {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d) where
  boundary : SmoothManifold n .euclidean (intrinsicBoundary S)
  ambient : (p : d) → TangentSpace S p ≃ₗ[ℝ] Euclidean (n+1)
  inclusion : (p : intrinsicBoundary S) → TangentSpace boundary p →ₗ[ℝ] TangentSpace S p.val
  normal : intrinsicBoundary S → Euclidean (n+1)
  orientation : Orientation S
  boundaryOrientation : Orientation boundary
  cotangent : CotangentBundle boundary
  formBundle : FormBundle cotangent n
  metric : Metric cotangent
  area : Form formBundle
  density : DensityField boundary
  natural : IsNaturalBoundary S boundary
  ambient_differential : ∀ p, IsEuclideanDifferential S T Subtype.val p (ambient p).toLinearMap
  normal_smooth : FrameData.VectorSmooth boundary.smoothStructure.val normal
  standard : ∀ p (v : DeterminantLine S p), IsPositive (orientation.val p) v ↔
    0 < standardAmbientDet (n+1) (exteriorPower.map (n+1) (ambient p).toLinearMap v)
  induced : IsInducedOrientation orientation boundaryOrientation
  differential : ∀ p, IsDifferential boundary S Subtype.val p (inclusion p)
  normal_unit : ∀ p, dotProduct (normal p) (normal p) = 1
  outward : ∀ p, BoundaryOrientationData.IsOutward S p ((ambient p.val).symm (normal p))
  tangent_hyperplane : ∀ p, LinearMap.range ((ambient p.val).toLinearMap.comp (inclusion p)) =
    LinearMap.ker (dotFunctional (normal p))
  induced_metric : ∀ p, metricForm metric p =
    euclideanPullback (V := TangentSpace boundary p)
      ((ambient p.val).toLinearMap.comp (inclusion p))
  metric_area : IsMetricVolume metric boundaryOrientation area
  metric_density : IsMetricDensity metric density
  smooth_density : IsSmoothDensity density
  positive_density : IsPositiveDensity density
  nonzero_density : ∀ p, density p ≠ 0
  area_normal : ∀ p (v : Fin n → TangentSpace boundary p),
    pairing p (area.field p) (exteriorPower.ιMulti ℝ n v) =
      (Matrix.of (Fin.cons (normal p) (fun i => ambient p.val (inclusion p (v i))))).det
  density_normal : ∀ p (v : Fin n → TangentSpace boundary p),
    (density p).val (exteriorPower.ιMulti ℝ n v) =
      |(Matrix.of (Fin.cons (normal p) (fun i => ambient p.val (inclusion p (v i))))).det|
  endpoints : ∀ hn : n = 0, ∀ p,
    let one := BoundaryOrientationData.castExterior hn.symm
      ((exteriorPower.zeroEquiv ℝ (TangentSpace boundary p)).symm 1)
    pairing p (area.field p) one = normal p 0 ∧ (density p).val one = 1

end SmoothManifolds.ClassicalData

namespace SmoothManifolds.ClassicalData
open ModelData
/-- An arbitrary ambient representative of a vector field on a subset.
Only derivatives within the original domain are used. -/
def extendVector {n q : ℕ} (d : Set (Euclidean n)) (X : d → Euclidean q)
    (x : Euclidean n) : Euclidean q := by
  classical
  exact if hx : x ∈ d then X ⟨x,hx⟩ else 0
end SmoothManifolds.ClassicalData

namespace SmoothManifolds.ClassicalData
open ModelData AtlasData TangentData DifferentialData BoundaryData BoundaryOrientationData
  OrientationData ClassicalBoundaryData
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan
open Specs.D13Unified.Ch21.IndexProperties (index circleLoop)
open scoped Topology
/-- Genuine induced boundary components and their Jordan-side winding signs. -/
def PlanarBoundaryComponents {a : ModelKind} {d : Set (Euclidean 2)}
    (S : SmoothManifold 2 a d)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (J : (p : d) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (b : Orientation B) : Prop :=
  ∀ p : intrinsicBoundary S,
        ∃ (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ),
          Set.range γ = ClassicalBoundaryData.planeComplexEquiv ''
            ((fun q : intrinsicBoundary S => q.val.val) '' connectedComponent p) ∧
          (∀ t : ℝ, ∃ (q : intrinsicBoundary S) (w : TangentSpace B q) (r : ℝ),
            q ∈ connectedComponent p ∧ realLift γ t = ClassicalBoundaryData.planeComplexEquiv q.val.val ∧
            0 < r ∧ HasDerivAt (realLift γ)
              (r • ClassicalBoundaryData.planeComplexEquiv (J q.val (K q w))) t ∧
            IsPositive (b.val q) (exteriorPower.ιMulti ℝ 1 ![w])) ∧
          ∃ Ω E N : Set ℂ,
            TwoComponents (Set.range γ)ᶜ Ω E ∧
            IsOpen Ω ∧ IsOpen E ∧ IsPathConnected Ω ∧ IsPathConnected E ∧
            Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
            frontier Ω = Set.range γ ∧ frontier E = Set.range γ ∧
            IsOpen N ∧ Set.range γ ⊆ N ∧
            (∀ z ∈ E, index (circleLoop (regularLoopMap γ hγ)) z = 0) ∧
            (((ClassicalBoundaryData.planeComplexEquiv '' d) ∩ N = N ∩ closure Ω ∧
                ∀ z ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) z = 1) ∨
             ((ClassicalBoundaryData.planeComplexEquiv '' d) ∩ N = N ∩ closure E ∧
                ∀ z ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) z = -1))
end SmoothManifolds.ClassicalData


namespace Specs.SmoothManifolds.Integration.ClassicalFormulas
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ExteriorDerivativeData _root_.SmoothManifolds.FormPullbackData
  _root_.SmoothManifolds.LocalIntegrationData _root_.SmoothManifolds.GlobalIntegrationData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.BoundaryData
  _root_.SmoothManifolds.BoundaryOrientationData _root_.SmoothManifolds.MetricVolumeData
  _root_.SmoothManifolds.ClassicalIntegralData _root_.SmoothManifolds.ClassicalBoundaryData
  _root_.SmoothManifolds.ClassicalData _root_.SmoothManifolds.EmbeddedData Set MeasureTheory
open scoped Topology BigOperators Matrix

def divergence_differentialType : Prop :=
  ∀ {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (X : d → Euclidean (n+1))
    (hX : LocallyContDiffOn 1 d X) ,
∃ G : DomainGeometry T d S,
      HasExteriorDerivative C
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p))
        (scalarVolume (fun p => divergenceWithin d (extendVector d X) p.val)
          (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap))) ∧
      pullbackField G.boundary S Subtype.val G.inclusion
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p)) =
        scalarVolume (fun p => X p.val ⬝ᵥ G.normal p) G.area.field

def divergence_theoremType : Prop :=
  ∀ {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (X : d → Euclidean (n+1))
    (hX : LocallyContDiffOn 1 d X)
    (hcomp : IsCompact d ∨ IsCompact (sectionSupport X)) ,
∃ G : DomainGeometry T d S,
      HasExteriorDerivative C
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p))
        (scalarVolume (fun p => divergenceWithin d (extendVector d X) p.val)
          (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap))) ∧
      pullbackField G.boundary S Subtype.val G.inclusion
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p)) =
        scalarVolume (fun p => X p.val ⬝ᵥ G.normal p) G.area.field ∧
      Integrable (extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val)) ∧
      ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm G.boundary → ℝ),
        IsIntegral G.orientation I → IsIntegral G.boundaryOrientation Ib →
        ∃ (η : CompactTopForm S) (β : CompactTopForm G.boundary),
          η.field = scalarVolume (fun p => divergenceWithin d (extendVector d X) p.val)
            (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap)) ∧
          β.field = scalarVolume (fun p => X p.val ⬝ᵥ G.normal p) G.area.field ∧
          I η = ∫ x in d, extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val) x ∧
          (∫ x in d, extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val) x) = Ib β ∧
          ∀ (K : FiberCoordinates G.boundary) {ι : Type}
            (c : ι → ModelChart n .euclidean (intrinsicBoundary S))
            (hc : ∀ i, c i ∈ G.boundary.smoothStructure.val) (ρ : ι → intrinsicBoundary S → ℝ),
            IsLocalization c ρ β →
            (∫ x in d, extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val) x) =
              ∑ᶠ i, ∫ x, surfaceIntegrand
                (fun p => (G.ambient p.val).toLinearMap.comp (G.inclusion p)) K (c i) (hc i)
                (fun p => ρ i p * (X p.val ⬝ᵥ G.normal p)) x

def green_theoremType : Prop :=
  ∀ {a : ModelKind}
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : EmbeddedData.euclideanChart 2 ∈ T.smoothStructure.val)
    (d : Set (Euclidean 2)) (S : SmoothManifold 2 a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (P Q : d → ℝ)
    (hP : LocallyContDiffOn 1 d P) (hQ : LocallyContDiffOn 1 d Q) (hd : IsCompact d) ,
∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
      (J : (p : d) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
      (Kb : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (o : Orientation S) (b : Orientation B),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      (∀ p v, IsPositive (o.val p) v ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap v)) ∧
      IsInducedOrientation o b ∧
      (∀ p, IsDifferential B S Subtype.val p (Kb p)) ∧
      PlanarBoundaryComponents S B J Kb b ∧
      HasExteriorDerivative C
        (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => ![P p, Q p]))
        (scalarVolume (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0)
          (euclideanVolumeForm S (fun p => (J p).toLinearMap))) ∧
      Integrable (extendScalar d
        (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0)) ∧
      ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm B → ℝ),
        IsIntegral o I → IsIntegral b Ib →
        ∃ (η : CompactTopForm S) (β : CompactTopForm B),
          η.field = scalarVolume
            (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0)
            (euclideanVolumeForm S (fun p => (J p).toLinearMap)) ∧
          β.field = euclideanOneForm B
            (fun p => (J p.val).toLinearMap.comp (Kb p)) (fun p => ![P p.val, Q p.val]) ∧
          I η = ∫ x in d, extendScalar d
            (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0) x ∧
          (∫ x in d, extendScalar d
            (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0) x) = Ib β ∧
          ∀ (s : SignedCharts B), RepresentsSignedCharts b.val s →
          ∀ (K : FiberCoordinates B) {ι : Type}
            (c : ι → ModelChart 1 .euclidean (intrinsicBoundary S))
            (hc : ∀ i, c i ∈ B.smoothStructure.val) (ρ : ι → intrinsicBoundary S → ℝ),
            IsLocalization c ρ β →
            (∫ x in d, extendScalar d
              (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0) x) =
              ∑ᶠ i, ∫ x, lineIntegrand s K (c i) (hc i)
                (fun p => (J p.val).toLinearMap.comp (Kb p))
                (fun p => ρ i p • ![P p.val, Q p.val]) x

def classical_surface_stokesType : Prop :=
  ∀ {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3)
    (hT : euclideanChart 3 ∈ T.smoothStructure.val)
    (hj : MapClassData.IsSmoothEmbedding S T j)
    (o : Orientation S) (C : CotangentBundle S) (D : FormBundle C 2)
    (U : Set (Euclidean 3)) (hU : IsOpen U) (hjU : ∀ p, j p ∈ U)
    (A : Euclidean 3 → Euclidean 3) (hA : ContDiffOn ℝ 1 A U) ,
∃ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
      (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean 3)
      (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (Cb : CotangentBundle B)
      (b : Orientation B)
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
      (∀ p, IsDifferential S T j p (L p)) ∧
      (∀ p, IsChartCoordinates T (j p) (euclideanChart 3) (F p)) ∧
      IsNaturalBoundary S B ∧ IsInducedOrientation o b ∧
      (∀ p, IsDifferential B S Subtype.val p (K p)) ∧
    let J := fun p => (F p).toLinearMap.comp (L p)
    let ω := euclideanOneForm S J (fun p => A (j p))
    ∃ (g : Metric C) (vol : Form D) (ν : M → Euclidean 3),
      (∀ p, metricForm g p = euclideanPullback (V := TangentSpace S p) (J p)) ∧ IsMetricVolume g o vol ∧
      FrameData.VectorSmooth S.smoothStructure.val ν ∧
      (∀ p, ν p ⬝ᵥ ν p = 1 ∧ ∀ v, ν p ⬝ᵥ J p v = 0) ∧
      (∀ p u v, J p u ⨯₃ J p v =
        pairing p (vol.field p) (exteriorPower.ιMulti ℝ 2 ![u,v]) • ν p) ∧
      HasExteriorDerivative C ω
        (scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) ∧
      (∀ p (v : Fin 2 → TangentSpace S p),
        extDeriv (ClassicalData.oneForm A) (j p) (fun i => J p (v i)) =
          evaluate (TangentSpace S p) 2
            ((scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) p) v) ∧
      ((IsCompact (univ : Set M) ∨ IsCompact (sectionSupport ω)) →
        ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm B → ℝ),
          IsIntegral o I → IsIntegral b Ib →
          ∃ (η : CompactTopForm S) (β : CompactTopForm B),
            η.field = scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field ∧
            β.field = euclideanOneForm B (fun p => (J p.val).comp (K p))
              (fun p => A (j p.val)) ∧
            I η = Ib β ∧
            ∀ (Ks : FiberCoordinates S) (Kb : FiberCoordinates B)
              (s : SignedCharts B), RepresentsSignedCharts b.val s →
            ∀ {ι κ : Type} (c : ι → ModelChart 2 a M)
              (hc : ∀ i, c i ∈ S.smoothStructure.val) (ρ : ι → M → ℝ),
              IsLocalization c ρ η →
            ∀ (d : κ → ModelChart 1 .euclidean (intrinsicBoundary S))
              (hd : ∀ i, d i ∈ B.smoothStructure.val)
              (σ : κ → intrinsicBoundary S → ℝ), IsLocalization d σ β →
              (∑ᶠ i, ∫ x, surfaceIntegrand J Ks (c i) (hc i)
                (fun p => ρ i p * (ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p)) x) =
              ∑ᶠ i, ∫ x, lineIntegrand s Kb (d i) (hd i)
                (fun p => (J p.val).comp (K p)) (fun p => σ i p • A (j p.val)) x)

end Specs.SmoothManifolds.Integration.ClassicalFormulas
