import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Topology.Order.Basic

/-!
Independent specification of `fa2:p1:smoothness-definitions`, paper.tex 4755–4770.
All duals are continuous scalar-linear duals; no completeness is imposed.
Real parameters act through their canonical inclusion into the scalar field.
-/
namespace ExpandedFA.P1.SmoothnessDefinitions.Spec

open Filter
open scoped Topology
universe u v

def NormingFunctionalsType :=
  ∀ (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], E → Set (E →L[𝕜] 𝕜)

/-- At a unit vector, D(x) is the set of norm-one functionals taking value one.
The equality is in 𝕜, so in the complex case the value is actually real one. -/
def NormingFunctionalsValue : NormingFunctionalsType :=
  fun _ _ _ _ _ x => {f | ‖f‖ = 1 ∧ f x = 1}

def SmoothAtType :=
  ∀ (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], E → Prop

/-- Smoothness at a unit vector means that D(x) is a singleton.
The source uses this definition only for ‖x‖ = 1. -/
def SmoothAtValue : SmoothAtType :=
  fun 𝕜 _ _ _ _ x => ∃ f, NormingFunctionalsValue 𝕜 x = {f}

def ModulusType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], ℝ → ℝ

/-- The maximum with zero is essential for the zero vector space.
The supremum uses two independently quantified closed-unit-ball vectors. -/
noncomputable def ModulusValue : ModulusType :=
  fun 𝕜 E _ _ _ t => max 0 (sSup {r : ℝ | ∃ x y : E,
    ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1})

def UniformlySmoothType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Prop

/-- The limit is through strictly positive real parameters decreasing to zero. -/
def UniformlySmoothValue : UniformlySmoothType :=
  fun 𝕜 E _ _ _ => Tendsto (fun t : ℝ => ModulusValue 𝕜 E t / t) (𝓝[>] 0) (𝓝 0)

/-- The raw ball and sphere suprema coincide in every nonzero space. -/
def BallSphereSupremum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E] (t : ℝ),
    sSup {r : ℝ | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1} =
    sSup {r : ℝ | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1}

/-- In a nonzero space even the outer maximum may be omitted in the sphere formula. -/
def SphereFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E] (t : ℝ),
    ModulusValue 𝕜 E t =
    sSup {r : ℝ | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      r = (‖x + (t : 𝕜) • y‖ + ‖x - (t : 𝕜) • y‖) / 2 - 1}

/-- Includes every realization of the zero vector space, for all real parameters. -/
def ZeroSpaceModulus : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E] (t : ℝ),
    ModulusValue 𝕜 E t = 0

def ZeroSpaceUniformlySmooth : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E],
    UniformlySmoothValue 𝕜 E

end ExpandedFA.P1.SmoothnessDefinitions.Spec
