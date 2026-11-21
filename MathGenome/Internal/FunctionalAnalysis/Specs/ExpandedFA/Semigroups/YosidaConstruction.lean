import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements for the zero-shift Hille–Yosida construction,
paper.tex 14746–14781. Resolvents have the original exact domain. The
power estimates range over every positive integer. No convergence,
semigroup, or generator certificate is assumed. The constant is left
unrestricted: its necessary nonnegativity follows from the estimates;
in particular the zero space is retained without an extra assumption. -/

noncomputable section
open Filter Topology
open scoped NNReal

namespace ExpandedFA.Semigroups.YosidaConstructionSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- The canonical bounded resolvent at a real spectral parameter. -/
def positiveResolvent (A : Unbounded.Operator 𝕜 X X) (r : ℝ) : X →L[𝕜] X :=
  Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 r) A

/-- r R(r,A). -/
def scaledResolvent (A : Unbounded.Operator 𝕜 X X) (r : ℝ) : X →L[𝕜] X :=
  algebraMap ℝ 𝕜 r • positiveResolvent A r

/-- The everywhere bounded form r²R(r,A) − rI. -/
def approximant (A : Unbounded.Operator 𝕜 X X) (r : ℝ) : X →L[𝕜] X :=
  algebraMap ℝ 𝕜 r • (scaledResolvent A r - ContinuousLinearMap.id 𝕜 X)

/-- e^(t A_r), with nonnegative real time in the conclusions below. -/
def exponential (A : Unbounded.Operator 𝕜 X X) (r t : ℝ) : X →L[𝕜] X :=
  NormedSpace.exp (algebraMap ℝ 𝕜 t • approximant A r)

/-- The original positive resolvent membership and all positive power bounds. -/
def ResolventEstimates (A : Unbounded.Operator 𝕜 X X) (M : ℝ) : Prop :=
  (∀ r : ℝ, 0 < r → Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r))) ∧
  ∀ (r : ℝ), 0 < r → ∀ n : ℕ,
    ‖positiveResolvent A r ^ (n + 1)‖ ≤ M / r ^ (n + 1)

/-- All original assumptions, including density and closedness of A. -/
def Hypotheses (A : Unbounded.Operator 𝕜 X X) (M : ℝ) : Prop :=
  Dense (A.domain : Set X) ∧ A.IsClosed ∧ ResolventEstimates A M

/-- The bounded expression in the source, with its scalar square explicit. -/
def ApproximantFormula : Prop := ∀ (A : Unbounded.Operator 𝕜 X X) (r : ℝ),
  approximant A r = (algebraMap ℝ 𝕜 r) ^ 2 • positiveResolvent A r -
    algebraMap ℝ 𝕜 r • ContinuousLinearMap.id 𝕜 X

/-- A_r = r A R(r,A) on every vector, using the resolvent's actual domain. -/
def ApproximantIdentity : Prop := ∀ (A : Unbounded.Operator 𝕜 X X) (r : ℝ)
    (hr : Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r))) (x : X),
  approximant A r x = algebraMap ℝ 𝕜 r •
    A (Unbounded.OperatorDomainsSpec.resolventToDomainValue (algebraMap ℝ 𝕜 r) A hr x)

/-- Strong convergence rR(r,A)x → x on all of X. -/
def ScaledResolventLimit : Prop := ∀ (A : Unbounded.Operator 𝕜 X X) (M : ℝ),
  Hypotheses A M → ∀ x : X,
    Tendsto (fun r : ℝ => scaledResolvent A r x) atTop (𝓝 x)

/-- Strong convergence A_rx → Ax on the original domain. -/
def ApproximantLimit : Prop := ∀ (A : Unbounded.Operator 𝕜 X X) (M : ℝ),
  Hypotheses A M → ∀ x : A.domain,
    Tendsto (fun r : ℝ => approximant A r x) atTop (𝓝 (A x))

/-- The common M bound, including t=0. -/
def ExponentialBound : Prop := ∀ (A : Unbounded.Operator 𝕜 X X) (M : ℝ),
  Hypotheses A M → ∀ r : ℝ, 0 < r → ∀ t : ℝ, 0 ≤ t →
    ‖exponential A r t‖ ≤ M

/-- The limiting C₀ semigroup has precisely A as generator, with no proper
extension of its domain, and convergence is uniform down to time zero on
every bounded nonnegative time interval, for each vector of X. -/
def Generation : Prop := ∀ (A : Unbounded.Operator 𝕜 X X) (M : ℝ),
  Hypotheses A M → ∃ T : C0Semigroup 𝕜 X,
    C0SemigroupSpec.generatorValue T = A ∧
    (∀ t : ℝ≥0, ‖T.operators t‖ ≤ M) ∧
    ∀ (x : X) (b : ℝ), 0 ≤ b →
      TendstoUniformlyOn (fun r : ℝ => fun t : ℝ => exponential A r t x)
        (fun t : ℝ => T.operators t.toNNReal x) atTop (Set.Icc 0 b)


/-! Fully quantified expected types for the implementation bindings. -/

def ApproximantFormulaExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ApproximantFormula (𝕜 := 𝕜) (X := X)


def ApproximantIdentityExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ApproximantIdentity (𝕜 := 𝕜) (X := X)

def ScaledResolventLimitExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ScaledResolventLimit (𝕜 := 𝕜) (X := X)

def ApproximantLimitExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ApproximantLimit (𝕜 := 𝕜) (X := X)

def ExponentialBoundExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  ExponentialBound (𝕜 := 𝕜) (X := X)

def GenerationExpected : Prop := ∀ {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
  Generation (𝕜 := 𝕜) (X := X)

end ExpandedFA.Semigroups.YosidaConstructionSpec
