import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.DensityCharts
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Differential

/-! Global integration of real densities, paper.tex M10.05, 1944–1970,
with the localization conventions and common-refinement argument at 1789–1844.
These propositions impose no orientation or partition as an extra hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators
namespace Specs.SmoothManifolds.Integration.DensityIntegral
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.MetricVolumeData _root_.SmoothManifolds.DensityIntegrationData
  Set MeasureTheory
universe u v

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

/-- Closure includes arbitrary continuous localizing weights, of either sign. -/
def compact_closureType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
    (∃ ρ : CompactDensity S, ρ.field = 0) ∧
    (∀ ρ σ : CompactDensity S, ∃ τ : CompactDensity S, τ.field = ρ.field + σ.field) ∧
    (∀ (f : M → ℝ), Continuous f → ∀ ρ : CompactDensity S,
      ∃ σ : CompactDensity S, σ.field = fun p => f p • ρ.field p)

/-- Closed supports of the weights are locally finite. The weights need only
sum to one near the density support and need not be positive or smooth. -/
def locally_finite_localizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (I : CompactDensity S → ℝ), IsDensityIntegral I →
    ∀ {ι : Type v} (ρ : CompactDensity S) (f : ι → M → ℝ)
      (K : FiberCoordinates S) (c : ι → ModelChart n a M)
      (hc : ∀ i, c i ∈ S.smoothStructure.val),
    (∀ i, Continuous (f i)) →
    LocallyFinite (fun i => sectionSupport (f i)) →
    (∀ i, sectionSupport (f i) ⊆ (c i).source) →
    (∃ U : Set M, IsOpen U ∧ sectionSupport ρ.field ⊆ U ∧
      ∀ p ∈ U, ∑ᶠ i, f i p = 1) →
    ∃ (σ : ι → CompactDensity S) (s : Finset ι),
      (∀ i, (σ i).field = fun p => f i p • ρ.field p) ∧
      (∀ i ∉ s, (σ i).field = 0) ∧
      (∀ i, sectionSupport (σ i).field ⊆ (c i).source) ∧
      ρ.field = ∑ i ∈ s, (σ i).field ∧
      I ρ = ∑ i ∈ s, coordinateIntegral K (c i) (hc i) (σ i).field ∧
      I ρ = ∑ᶠ i, coordinateIntegral K (c i) (hc i) (σ i).field

end Specs.SmoothManifolds.Integration.DensityIntegral
