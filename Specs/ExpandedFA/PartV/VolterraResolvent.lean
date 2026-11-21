import Specs.ExpandedFA.PartV.VolterraFactorial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-! Full operator and iteration conclusions of `fa2:p5:volterra-resolvent`.
`‖k‖` is the actual maximum on the compact triangle (upstream KernelMaximum).
All norms and limits use the native supremum/operator norms. No positive length,
nonzero state, or smallness premise is imposed. -/
noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.PartV.VolterraResolventSpec

def Resolvent : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜),
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  ∃ S : C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E),
    Summable (fun n : ℕ => ‖lam ^ n • V ^ n‖) ∧
    HasSum (fun n : ℕ => lam ^ n • V ^ n) S ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, lam ^ n • V ^ n) atTop (𝓝 S) ∧
    (1 - lam • V) * S = 1 ∧ S * (1 - lam • V) = 1 ∧
    ‖S‖ ≤ Real.exp (‖lam‖ * ‖k‖ * (b - a))

def SolvabilityAndIteration : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (lam : 𝕜) (f : C(VolterraInterval a b, E)),
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  ∃ u : C(VolterraInterval a b, E),
    u - lam • V u = f ∧
    (∀ v : C(VolterraInterval a b, E), v - lam • V v = f → v = u) ∧
    HasSum (fun n : ℕ => lam ^ n • ((V ^ n) f)) u ∧
    ‖u‖ ≤ Real.exp (‖lam‖ * ‖k‖ * (b - a)) * ‖f‖ ∧
    ∀ u₀ : C(VolterraInterval a b, E),
      let T := fun v : C(VolterraInterval a b, E) => f + lam • V v
      (∀ n : ℕ, ‖T^[n] u₀ - u‖ ≤
        (‖lam‖ * ‖k‖ * (b - a)) ^ n / (n.factorial : ℝ) * ‖u₀ - u‖) ∧
      Tendsto (fun n : ℕ => T^[n] u₀) atTop (𝓝 u) ∧
      TendstoUniformly (fun n : ℕ => ⇑(T^[n] u₀)) u atTop

/-- The sum is the actual two-sided inverse, in the operator norm. -/
def InverseSeries : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜),
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  IsUnit (1 - lam • V) ∧
  HasSum (fun n : ℕ => lam ^ n • V ^ n) (Ring.inverse (1 - lam • V)) ∧
  ‖Ring.inverse (1 - lam • V)‖ ≤ Real.exp (‖lam‖ * ‖k‖ * (b - a))

/-- The exponential estimate for every uniform kernel bound M. Nonnegativity
of M follows from the nonempty triangle, including a=b. -/
def UniformInverseBound : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (M : ℝ), (∀ p, ‖k p‖ ≤ M) → ∀ lam : 𝕜,
  ‖Ring.inverse (1 - lam • VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k)‖ ≤
    Real.exp (‖lam‖ * M * (b - a))

/-- Evaluation at the initial point annihilates the range. -/
def EvaluationAtLeft : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (u : C(VolterraInterval a b, E)),
  VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k u ⟨a, le_rfl, hab⟩ = 0

def NotSurjective : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [Nontrivial E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)),
  ¬ Function.Surjective (VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k)

/-- This includes every a<b and, more strongly, the singleton interval:
C({a},E) remains nonzero if E is nonzero, so the zero operator has spectrum {0}.
The zero state space is not subject to this nonempty-spectrum assertion. -/
def ComplexSpectrum : Prop := ∀ (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[ℂ] E)),
  spectrum ℂ (VolterraOperatorSpec.OperatorValue ℂ E a b hab k) = {0}

/-- A singleton interval gives the zero integral operator and identity inverse,
without any nonzero-state assumption. -/
def SingletonResolvent : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a : ℝ) (k : C(volterraTriangle a a, E →L[𝕜] E)),
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a a (le_refl a) k
  V = 0 ∧ ∀ lam : 𝕜, Ring.inverse (1 - lam • V) = 1

end ExpandedFA.PartV.VolterraResolventSpec
