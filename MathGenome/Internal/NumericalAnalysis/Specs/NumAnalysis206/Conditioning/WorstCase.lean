import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent specification of the worst-case interpretation after W09.
The supremum is a real conditional supremum; boundedness on a sufficiently
small ball is a separate required assertion, so its totalized value on
unbounded sets is never used as a finite supremum. -/

universe u v w
namespace Specs.NumAnalysis206.Conditioning
open Filter Metric Set
open scoped Topology

/-- Output changes for all perturbations in the closed input ball. -/
def outputNorms {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (f : X → Y) (x : X) (r : ℝ) : Set ℝ :=
  (fun v => ‖f (x + v) - f x‖) '' closedBall 0 r

/-- The absolute worst-case gain, with input radius `r`. -/
noncomputable def worstCase {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (f : X → Y) (x : X) (r : ℝ) : ℝ := sSup (outputNorms f x r) / r

/-- Output relative error per unit of relative input radius. -/
noncomputable def relativeWorstCase {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (f : X → Y) (x : X) (r : ℝ) : ℝ :=
  sSup (outputNorms f x (r * ‖x‖)) / (r * ‖f x‖)

/-- The closed perturbation balls lie in the domain and have bounded output changes. -/
def LocalBoundedType : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X) (_ : IsOpen U) (f : X → Y) (x : X),
    x ∈ U → DifferentiableAt 𝕜 f x →
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ →
      (∀ v, ‖v‖ ≤ r → x + v ∈ U) ∧
      BddAbove (outputNorms f x r) ∧ 0 ≤ worstCase f x r

/-- A uniform Fréchet remainder modulus on closed balls, tending to zero
from positive radii, also bounds the error in the worst-case gain. -/
def UniformRemainderType : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X) (_ : IsOpen U) (f : X → Y) (x : X),
    x ∈ U → DifferentiableAt 𝕜 f x →
    ∃ (ω : ℝ → ℝ) (δ : ℝ), 0 < δ ∧
      Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
      ∀ r, 0 < r → r ≤ δ →
        0 ≤ ω r ∧
        (∀ v, ‖v‖ ≤ r →
          ‖f (x + v) - f x - fderiv 𝕜 f x v‖ ≤ ω r * ‖v‖) ∧
        |worstCase f x r - ‖fderiv 𝕜 f x‖| ≤ ω r

/-- The absolute worst-case interpretation of W09. -/
def WorstCaseLimitType : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X) (_ : IsOpen U) (f : X → Y) (x : X),
    x ∈ U → DifferentiableAt 𝕜 f x →
    Tendsto (worstCase f x) (𝓝[>] 0) (𝓝 ‖fderiv 𝕜 f x‖)

/-- Relative scaling is the actual supremum at radius `r * ‖x‖`,
normalized by `r * ‖f x‖`, and has the stated relative limit. -/
def RelativeWorstCaseType : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (U : Set X) (_ : IsOpen U) (f : X → Y) (x : X),
    x ∈ U → DifferentiableAt 𝕜 f x → x ≠ 0 → f x ≠ 0 →
    (∀ r, 0 < r → relativeWorstCase f x r =
      worstCase f x (r * ‖x‖) * ‖x‖ / ‖f x‖) ∧
    Tendsto (relativeWorstCase f x) (𝓝[>] 0)
      (𝓝 (‖fderiv 𝕜 f x‖ * ‖x‖ / ‖f x‖))

/-- The zero-dimensional input case has exactly zero worst-case gain. -/
def ZeroDimensionalType : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    Module.finrank 𝕜 X = 0 → ∀ (f : X → Y) (x : X) (r : ℝ),
    0 < r → worstCase f x r = 0

end Specs.NumAnalysis206.Conditioning
