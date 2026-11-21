import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
Independent statements for paper.tex:16945–16984, `fa2:p4:l1-gliding-hump`.
The continuous dual is scalar-linear, over either ℝ or ℂ. All integrals
below are integrals of the norm, including the finite-measure tail condition.
The weakly convergent version includes both the original and centered sequence.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace ExpandedFA.FunctionSpaces.WeakL1UniformIntegrabilitySpec

/-- Convergence against every continuous scalar-linear functional. -/
def WeaklyConverges {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ) : Prop :=
  ∀ L : Lp 𝕜 1 μ →L[𝕜] 𝕜, Tendsto (fun n => L (f n)) atTop (𝓝 (L g))

/-- Uniform absolute continuity of norm integrals on measurable small sets. -/
def SmallSetControl {X : Type u} {ι : Type v} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (f : ι → X → 𝕜) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ A : Set X, MeasurableSet A → μ A < ENNReal.ofReal δ →
      ∀ i, (∫ x in A, ‖f i x‖ ∂μ) < ε

/-- Uniform tightness in L¹; no assumption of finite total measure. -/
def TailControl {X : Type u} {ι : Type v} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (f : ι → X → 𝕜) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ F : Set X, MeasurableSet F ∧ μ F < ∞ ∧
    ∀ i, (∫ x in Fᶜ, ‖f i x‖ ∂μ) < ε

def Controls {X : Type u} {ι : Type v} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (f : ι → X → 𝕜) : Prop :=
  SmallSetControl μ f ∧ TailControl μ f

/-- The full source conclusion for weakly null sequences. -/
def WeakNullControls : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : ℕ → Lp 𝕜 1 μ),
    WeaklyConverges μ f 0 → Controls μ (fun n => (f n : X → 𝕜))

/-- Both assertions persist under subtracting or adding the weak limit. -/
def WeakConvergentControls : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ),
    WeaklyConverges μ f g →
      Controls μ (fun n => (f n : X → 𝕜)) ∧
      Controls μ (fun n : ℕ => ((f n - g : Lp 𝕜 1 μ) : X → 𝕜))

/-- The endpoint duality tests are bilinear multiplication/integration,
with no antidual or conjugated density hidden in weak convergence. -/
def WeakConvergenceTests : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ),
    WeaklyConverges μ f g ↔
      ∀ h : Lp 𝕜 ∞ μ,
        Tendsto (fun n => ∫ x, f n x * h x ∂μ) atTop
          (𝓝 (∫ x, g x * h x ∂μ))

def Centering : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ),
    WeaklyConverges μ f g ↔ WeaklyConverges μ (fun n => f n - g) 0

/-- The auxiliary controls do not depend on representatives. -/
def ControlsAeInvariant : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f g : ι → X → 𝕜),
    (∀ i, f i =ᵐ[μ] g i) → (Controls μ f ↔ Controls μ g)

def ControlsAdd : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f g : ι → X → 𝕜),
    (∀ i, Integrable (f i) μ) → (∀ i, Integrable (g i) μ) →
    Controls μ f → Controls μ g → Controls μ (fun i x => f i x + g i x)

/-- Finite families, including a single integrable limit, have both controls
on arbitrary measure spaces. -/
def FiniteFamilyControls : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [Finite ι] (μ : Measure X) (f : ι → X → 𝕜),
    (∀ i, Integrable (f i) μ) → Controls μ f

/-- Equivalence with the native weak topology, not norm convergence. -/
def NativeWeakConvergence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ),
    WeaklyConverges μ f g ↔
      Tendsto (fun n => toWeakSpace 𝕜 (Lp 𝕜 1 μ) (f n)) atTop
        (𝓝 (toWeakSpace 𝕜 (Lp 𝕜 1 μ) g))

/-- Bounded measurable raw test functions are legitimate dual tests. -/
def BoundedTests : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ),
    WeaklyConverges μ f g →
    ∀ h : X → 𝕜, AEStronglyMeasurable h μ →
      (∀ᵐ x ∂μ, ‖h x‖ ≤ 1) →
      Tendsto (fun n => ∫ x, f n x * h x ∂μ) atTop
        (𝓝 (∫ x, g x * h x ∂μ))

/-- Adding or subtracting one fixed integrable function preserves both controls. -/
def CenteringControls : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ),
    Controls μ (fun n => (f n : X → 𝕜)) ↔
      Controls μ (fun n : ℕ => ((f n - g : Lp 𝕜 1 μ) : X → 𝕜))

/-- Scalar phase alignment used in the complex as well as real patch argument. -/
def UnitPhaseAlignment : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) (r : ℝ), 0 ≤ r →
    ∃ c : 𝕜, ‖c‖ = 1 ∧ ‖z + c * (r : 𝕜)‖ = ‖z‖ + r

end ExpandedFA.FunctionSpaces.WeakL1UniformIntegrabilitySpec
