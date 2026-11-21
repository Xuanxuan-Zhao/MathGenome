import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalSigned

/-! Local unsigned integration for M10.05, paper.tex 1944--1968, with the
chart-support conventions of 1789--1814. Shared DensityIntegrationData definitions
are adopted from the parent interface, including the data used in its global
integration and regularity results. The density fibers are the canonical absolute
duals of ΛⁿTM; no orientation or metric is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators
open Module

namespace SmoothManifolds.DensityIntegrationData
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  OrientationData MetricVolumeData ExteriorData LocalIntegrationData TensorData Set MeasureTheory
universe u

/-- Evaluation on every ordered list, including dependent lists. -/
def tupleEvaluation {n : ℕ} {V : Type u} [AddCommGroup V] [Module ℝ V]
    (ρ : densitySubmodule (⋀[ℝ]^n V)) (v : Fin n → V) : ℝ :=
  ρ.val (exteriorPower.ιMulti ℝ n v)

/-- Pullback in the canonical density lines. Singular maps are allowed. -/
def fiberPullback {n : ℕ} {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) :
    densitySubmodule (⋀[ℝ]^n W) →ₗ[ℝ] densitySubmodule (⋀[ℝ]^n V) where
  toFun ρ := ⟨fun v => ρ.val (exteriorPower.map n L v), by
    intro t v
    dsimp only
    rw [map_smul, ρ.property]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Tangent maps are explicit, following the upstream differential interface.
The regularity theorems require them to be the actual differentials. -/
def pullbackField {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (ρ : DensityField T) : DensityField S :=
  fun p => fiberPullback (L p) (ρ (f p))

/-- Coefficient continuity in the canonical density atlas. -/
def IsContinuousDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ρ : DensityField S) : Prop :=
  ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    Continuous (fun p : c.source => densityCoefficient K c hc p (ρ p.val))

structure CompactDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) where
  field : DensityField S
  continuous : IsContinuousDensity field
  compact_support : IsCompact (sectionSupport field)

/-- Absolute value of a top form is taken on its determinant-line pairing. -/
def absoluteTopForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ω : Field S n) : DensityField S :=
  fun p => ⟨fun v => |pairing p (ω p) v|, by
    intro t v
    dsimp only
    unfold pairing
    rw [map_smul, smul_eq_mul, abs_mul]⟩

/-- Zero off the chart target inside the model; then zero off the model in ℝⁿ.
At the true boundary this ambient extension need not be continuous. -/
def coordinateDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ρ : DensityField S) :
    Euclidean n → ℝ :=
  extendModel (fun x => if hx : x ∈ c.target then
    densityCoefficient K c hc ⟨c.symm x, c.map_target hx⟩ (ρ (c.symm x)) else 0)

def coordinateIntegral {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ρ : DensityField S) : ℝ :=
  ∫ x, coordinateDensity K c hc ρ x

/-- Exact linearity and coordinate normalization, on the compact continuous
sections. Using field equations avoids imposing arbitrary bundle realizations. -/
def IsDensityIntegral {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (I : CompactDensity S → ℝ) : Prop :=
  (∀ ρ σ τ, τ.field = ρ.field + σ.field → I τ = I ρ + I σ) ∧
  (∀ (t : ℝ) ρ σ, σ.field = t • ρ.field → I σ = t * I ρ) ∧
  ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ρ : CompactDensity S), sectionSupport ρ.field ⊆ c.source →
      I ρ = coordinateIntegral K c hc ρ.field

def zeroCoefficient {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (ρ : DensityField S) (p : M) : ℝ :=
  (ρ p).val ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1)

/-- The canonical real-coordinate density a |dx| on the actual determinant
line Λ¹ℝ; it is not just an untyped coefficient function. -/
def realDensity (a : ℝ) : densitySubmodule (⋀[ℝ]^1 ℝ) :=
  ⟨fun v => a * |exteriorPower.oneEquiv ℝ ℝ v|, by
    intro t v
    dsimp only
    rw [map_smul, smul_eq_mul, abs_mul]
    ring⟩

/-- The one-form a dx in the actual exterior cotangent fiber of ℝ. -/
def realTopForm (a : ℝ) : Fiber ℝ 1 :=
  exteriorPower.ιMulti ℝ 1 (fun _ => a • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

/-- Standard real coordinate version of the absolute-Jacobian coefficient. -/
def realPullbackCoefficient (f b : ℝ → ℝ) (x : ℝ) : ℝ := b (f x) * |deriv f x|

end SmoothManifolds.DensityIntegrationData

namespace Specs.SmoothManifolds.Integration.DensityCharts
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.MetricVolumeData
  _root_.SmoothManifolds.DensityIntegrationData Set MeasureTheory
universe u

def integrableType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ρ : CompactDensity S),
    sectionSupport ρ.field ⊆ c.source → Integrable (coordinateDensity K c hc ρ.field)

/-- No orientation or nonvanishing condition is imposed. -/
def chart_independenceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K L : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (ρ : CompactDensity S),
    sectionSupport ρ.field ⊆ c.source → sectionSupport ρ.field ⊆ d.source →
      coordinateIntegral K c hc ρ.field = coordinateIntegral L d hd ρ.field

def artificial_edgesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ρ : CompactDensity S),
    sectionSupport ρ.field ⊆ c.source → ∀ x : ModelSpace n a, x ∉ c.target →
      ∃ U : Set (Euclidean n), IsOpen U ∧ x.val ∈ U ∧
        ∀ y ∈ U, coordinateDensity K c hc ρ.field y = 0

/-- Continuity is asserted in the relative model, including its true face. -/
def model_continuousType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ρ : CompactDensity S),
    sectionSupport ρ.field ⊆ c.source →
      Continuous (fun x : ModelSpace n a => coordinateDensity K c hc ρ.field x.val)

/-- All compact subsets, not only section supports, are finite. -/
def zero_compact_finiteType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (C : Set M), IsCompact C → C.Finite

/-- Includes empty chart domains via the finite sum formula. -/
def zero_coordinateType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (K : FiberCoordinates S)
    (c : ModelChart 0 a M) (hc : c ∈ S.smoothStructure.val) (ρ : CompactDensity S),
    sectionSupport ρ.field ⊆ c.source →
      (∃ h : (sectionSupport ρ.field).Finite,
        coordinateIntegral K c hc ρ.field = ∑ p ∈ h.toFinset, zeroCoefficient ρ.field p) ∧
      ∀ p : c.source, coordinateIntegral K c hc ρ.field = zeroCoefficient ρ.field p.val

end Specs.SmoothManifolds.Integration.DensityCharts
