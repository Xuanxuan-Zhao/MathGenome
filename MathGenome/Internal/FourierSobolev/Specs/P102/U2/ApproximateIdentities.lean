import MathGenome.Internal.FourierSobolev.Specs.P102.U2.Young
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements for paper.tex:821–836. The positive real parameter
tends to zero from above. The bound on the L¹ norms need not be optimal.
Neither positivity nor compact support of the kernels is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace P102.U2.ApproximateIdentitiesExpected

def Conditions {G 𝕜 : Type*} [Zero G] [PseudoMetricSpace G]
    [MeasurableSpace G] [RCLike 𝕜] (μ : Measure G) (k : ℝ → G → 𝕜) : Prop :=
  (∀ ε > 0, Integrable (k ε) μ) ∧
  (∀ ε > 0, (∫ y, k ε y ∂μ) = 1) ∧
  (∃ A : ℝ, 0 ≤ A ∧ ∀ ε > 0, (∫ y, ‖k ε y‖ ∂μ) ≤ A) ∧
  ∀ δ > 0, Tendsto (fun ε => ∫ y in {y | δ < dist y 0}, ‖k ε y‖ ∂μ)
    (𝓝[>] 0) (𝓝 0)

/-- The original order k*f(x)=∫k(x-y)f(y), with absolute existence a.e.
and Lp membership at each positive parameter, followed by convergence in norm.
`eLpNorm` has value in the extended nonnegative reals. -/
def LpResult {G 𝕜 : Type*} [Sub G] [MeasurableSpace G] [RCLike 𝕜]
    (μ : Measure G) (k : ℝ → G → 𝕜) : Prop :=
  ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → ∀ f : G → 𝕜, MemLp f p μ →
    (∀ ε > 0, (∀ᵐ x ∂μ, Integrable (fun y => k ε (x - y) * f y) μ) ∧
      MemLp (fun x => ∫ y, k ε (x - y) * f y ∂μ) p μ) ∧
    Tendsto (fun ε => eLpNorm (fun x => (∫ y, k ε (x - y) * f y ∂μ) - f x) p μ)
      (𝓝[>] 0) (𝓝 0)

/-- This conclusion concerns actual points of the given representative. It
does not assume f belongs to any Lp space. -/
def UniformResult {G 𝕜 : Type*} [Sub G] [UniformSpace G] [MeasurableSpace G]
    [RCLike 𝕜] (μ : Measure G) (k : ℝ → G → 𝕜) : Prop :=
  ∀ f : G → 𝕜, UniformContinuous f → (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) →
    (∀ ε > 0, ∀ x, Integrable (fun y => k ε (x - y) * f y) μ) ∧
    TendstoUniformly (fun ε x => ∫ y, k ε (x - y) * f y ∂μ) f (𝓝[>] 0)

def EuclideanLp : Prop :=
  ∀ d : ℕ, 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → EuclideanSpace ℝ (Fin d) → 𝕜),
    Conditions volume k → LpResult volume k

def CircleLp : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → Periodic.Expected.Circle T → 𝕜),
    Conditions (Periodic.Expected.haar T) k → LpResult (Periodic.Expected.haar T) k

def EuclideanUniform : Prop :=
  ∀ d : ℕ, 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → EuclideanSpace ℝ (Fin d) → 𝕜),
    Conditions volume k → UniformResult volume k

def CircleUniform : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → Periodic.Expected.Circle T → 𝕜),
    Conditions (Periodic.Expected.haar T) k → UniformResult (Periodic.Expected.haar T) k

def CompletedConditions {G 𝕜 : Type*} [Zero G] [PseudoMetricSpace G]
    [MeasurableSpace G] [RCLike 𝕜] (μ : Measure G) (k : ℝ → G → 𝕜) : Prop :=
  (∀ ε > 0, Integrable (α := NullMeasurableSpace G μ) (k ε) μ.completion) ∧
  (∀ ε > 0, (∫ y : NullMeasurableSpace G μ, k ε y ∂μ.completion) = 1) ∧
  (∃ A : ℝ, 0 ≤ A ∧ ∀ ε > 0,
    (∫ y : NullMeasurableSpace G μ, ‖k ε y‖ ∂μ.completion) ≤ A) ∧
  ∀ δ > 0, Tendsto (fun ε =>
    ∫ y : NullMeasurableSpace G μ in {y | δ < @dist G _ y (0 : G)}, ‖k ε y‖ ∂μ.completion)
    (𝓝[>] 0) (𝓝 0)

def CompletedLpResult {G 𝕜 : Type*} [Sub G] [MeasurableSpace G] [RCLike 𝕜]
    (μ : Measure G) (k : ℝ → G → 𝕜) : Prop :=
  ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → ∀ f : G → 𝕜,
    MemLp (α := NullMeasurableSpace G μ) f p μ.completion →
    (∀ ε > 0, (∀ᵐ x ∂μ.completion,
      Integrable (fun y : NullMeasurableSpace G μ => k ε (@Sub.sub G _ x y) * f y)
        μ.completion) ∧
      MemLp (fun x : NullMeasurableSpace G μ =>
        ∫ y : NullMeasurableSpace G μ, k ε (@Sub.sub G _ x y) * f y ∂μ.completion)
        p μ.completion) ∧
    Tendsto (fun ε => eLpNorm (fun x : NullMeasurableSpace G μ =>
      (∫ y : NullMeasurableSpace G μ, k ε (@Sub.sub G _ x y) * f y ∂μ.completion) - f x)
      p μ.completion) (𝓝[>] 0) (𝓝 0)

def CompletedUniformResult {G 𝕜 : Type*} [Sub G] [UniformSpace G] [MeasurableSpace G]
    [RCLike 𝕜] (μ : Measure G) (k : ℝ → G → 𝕜) : Prop :=
  ∀ f : G → 𝕜, UniformContinuous f → (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) →
    (∀ ε > 0, ∀ x : G,
      Integrable (fun y : NullMeasurableSpace G μ => k ε (@Sub.sub G _ x y) * f y)
        μ.completion) ∧
    TendstoUniformly (fun ε (x : G) =>
      ∫ y : NullMeasurableSpace G μ, k ε (@Sub.sub G _ x y) * f y ∂μ.completion)
      f (𝓝[>] 0)

-- The same statements for completed measures, with unchanged pointwise functions.
def EuclideanCompletedLp : Prop :=
  ∀ d : ℕ, 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → EuclideanSpace ℝ (Fin d) → 𝕜),
    CompletedConditions volume k → CompletedLpResult volume k

def CircleCompletedLp : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → Periodic.Expected.Circle T → 𝕜),
    CompletedConditions (Periodic.Expected.haar T) k →
      CompletedLpResult (Periodic.Expected.haar T) k

def EuclideanCompletedUniform : Prop :=
  ∀ d : ℕ, 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → EuclideanSpace ℝ (Fin d) → 𝕜),
    CompletedConditions volume k → CompletedUniformResult volume k

def CircleCompletedUniform : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜]
    (k : ℝ → Periodic.Expected.Circle T → 𝕜),
    CompletedConditions (Periodic.Expected.haar T) k →
      CompletedUniformResult (Periodic.Expected.haar T) k

end P102.U2.ApproximateIdentitiesExpected
