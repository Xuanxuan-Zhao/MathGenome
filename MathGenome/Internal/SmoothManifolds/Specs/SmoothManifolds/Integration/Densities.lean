import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.DensityIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Independent formulation of M10.05, paper.tex 1944--1976.
The density fibers are the existing canonical absolute duals of ΛⁿTM.
No orientation, metric, invertibility or nonvanishing is part of density data.
The analytic examples below are in the standard real coordinate x. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators
open Module

namespace Specs.SmoothManifolds.Integration.Densities
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.MetricVolumeData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.LocalIntegrationData _root_.SmoothManifolds.TensorData
  _root_.SmoothManifolds.DensityIntegrationData Set MeasureTheory
universe u

/-- Complete frame law and the mandated extension to dependent lists. -/
def tuple_lawType : Prop :=
  ∀ {n : ℕ} {V : Type u} [AddCommGroup V] [Module ℝ V]
    (ρ : densitySubmodule (⋀[ℝ]^n V)),
    (∀ v : Fin n → V, ¬ LinearIndependent ℝ v → tupleEvaluation ρ v = 0) ∧
    ∀ (b : Basis (Fin n) ℝ V) (v : Fin n → V),
      tupleEvaluation ρ v = |b.det v| * tupleEvaluation ρ b

/-- Pullback agrees with evaluation on the image list even at rank drop. -/
def fiber_pullbackType : Prop :=
  ∀ {n : ℕ} {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W)
    (ρ : densitySubmodule (⋀[ℝ]^n W)) (v : Fin n → V),
    tupleEvaluation (DensityIntegrationData.fiberPullback L ρ) v =
      tupleEvaluation ρ (L ∘ v)

/-- Coefficient formula in the actual intrinsic tangent coordinates. -/
def pullback_coefficientType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (K : FiberCoordinates S) (J : FiberCoordinates T)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n b N) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hq : f p ∈ d.source) (ρ : DensityField T),
    densityCoefficient K c hc ⟨p, hp⟩ (DensityIntegrationData.pullbackField S T f L ρ p) =
      densityCoefficient J d hd ⟨f p, hq⟩ (ρ (f p)) *
        |(Matrix.of (fun i j => J.equiv d hd (f p) hq
          (L p ((K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) j))) i)).det|

/-- No invertibility hypothesis, including on the boundary and at rank drops. -/
def pullback_continuousType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f →
    ∀ (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, IsDifferential S T f p (L p)) → ∀ ρ : DensityField T,
    IsContinuousDensity ρ →
      IsContinuousDensity (DensityIntegrationData.pullbackField S T f L ρ)

def pullback_smoothType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsLocalDiffeomorphism S T f →
    ∀ (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, IsDifferential S T f p (L p)) → ∀ ρ : DensityField T,
    IsSmoothDensity ρ → IsSmoothDensity (DensityIntegrationData.pullbackField S T f L ρ)

def absolute_coefficientType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (ω : Field S n) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source),
    densityCoefficient K c hc p (absoluteTopForm ω p.val) =
      |FormPullbackData.topCoefficient K c hc p.val p.property ω|

/-- This is continuity only; no claim of smoothness at zeros. -/
def absolute_continuousType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (ω : Field S n),
    IsContinuousTopForm ω → IsContinuousDensity (absoluteTopForm ω)

def integral_exists_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), ∃! I : CompactDensity S → ℝ, IsDensityIntegral I

/-- Invariance includes the compact-support theorem for diffeomorphic pullback. -/
def diffeomorphismType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (I : CompactDensity S → ℝ) (J : CompactDensity T → ℝ),
    IsDensityIntegral I → IsDensityIntegral J →
    ∀ (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (F.toEquiv p)),
    (∀ p, IsDifferential S T F.toEquiv p (L p)) → ∀ ρ : CompactDensity T,
    ∃ σ : CompactDensity S,
      σ.field = DensityIntegrationData.pullbackField S T F.toEquiv L ρ.field ∧ I σ = J ρ

/-- Every finite chart localization computes the same integral. Arbitrary
locally finite subordinate partitions reduce to this on a compact support. -/
def finite_localizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (I : CompactDensity S → ℝ), IsDensityIntegral I →
    ∀ (k : ℕ) (ρ : CompactDensity S) (σ : Fin k → CompactDensity S)
      (K : FiberCoordinates S) (c : Fin k → ModelChart n a M)
      (hc : ∀ i, c i ∈ S.smoothStructure.val),
    (∀ i, sectionSupport (σ i).field ⊆ (c i).source) →
    ρ.field = ∑ i, (σ i).field →
      I ρ = ∑ i, DensityIntegrationData.coordinateIntegral K (c i) (hc i) (σ i).field

def zero_finite_sumType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (I : CompactDensity S → ℝ), IsDensityIntegral I →
    ∀ ρ : CompactDensity S, ∃ h : (sectionSupport ρ.field).Finite,
      I ρ = ∑ p ∈ h.toFinset, DensityIntegrationData.zeroCoefficient ρ.field p

/-- Include the already constructed canonical μ_g without assuming orientation. -/
def metricType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : BundleOperationsData.CotangentBundle S) (g : Metric C),
    ∃! ρ : DensityField S, IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧
      IsContinuousDensity ρ ∧ IsPositiveDensity ρ ∧
      ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
        (p : c.source), densityCoefficient K c hc p (ρ p.val) =
          Real.sqrt (metricMatrix g K c hc p).det

/-- Bridges from actual density/exterior fibers to the two scalar examples.
The linear map (f′ x) id is the ordinary tangent differential on ℝ. -/
def real_coordinate_bridgeType : Prop :=
  (∀ (f b : ℝ → ℝ) (x : ℝ),
    tupleEvaluation (DensityIntegrationData.fiberPullback
      ((deriv f x) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (realDensity (b (f x))))
      (fun _ : Fin 1 => (1 : ℝ)) = realPullbackCoefficient f b x) ∧
  ∀ x : ℝ, |exteriorPower.pairingDual ℝ ℝ 1 (realTopForm x)
    (exteriorPower.ιMulti ℝ 1 (fun _ : Fin 1 => (1 : ℝ)))| = |x|

/-- x² pulls the constant density coefficient back to 2|x|. Failure of
first differentiability proves failure of smoothness, not just a cusp formula. -/
def square_counterexampleType : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ 2) ∧
  ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℝ)) ∧
  (∀ x : ℝ, realPullbackCoefficient (fun t => t ^ 2) (fun _ => 1) x = 2 * |x|) ∧
  Continuous (realPullbackCoefficient (fun t => t ^ 2) (fun _ => 1)) ∧
  ¬ DifferentiableAt ℝ (realPullbackCoefficient (fun t => t ^ 2) (fun _ => 1)) 0 ∧
  ¬ ContDiffAt ℝ (⊤ : ℕ∞) (realPullbackCoefficient (fun t => t ^ 2) (fun _ => 1)) 0

/-- The smooth one-form x dx has a zero at 0 and absolute density coefficient
|x|, which is continuous and not even differentiable at that zero. -/
def absolute_counterexampleType : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x) ∧
  (fun x : ℝ => x) 0 = 0 ∧ Continuous (fun x : ℝ => |x|) ∧
  ¬ DifferentiableAt ℝ (fun x : ℝ => |x|) 0 ∧
  ¬ ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => |x|) 0

end Specs.SmoothManifolds.Integration.Densities
