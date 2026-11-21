import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Exact-domain formulation of the extension clause of
`fa2:p3:derivative-domains`. All endpoint conditions refer to the continuous
primitive representative of the original weak Sobolev class. -/
noncomputable section
open Set
namespace ExpandedFA.Unbounded.IntervalDerivative
open ExpandedFA.Sobolev.OneDimensional

/-- The boundary condition is imposed on an actual AC Sobolev representative. -/
def boundaryCondition (z : ℂ) (u : H1) : Prop :=
  ∃ f : ℝ → ℂ, PrimitiveRepresentative u f ∧ f 1 = z * f 0

/-- The span makes this construction independent of any unproved trace
linearity. `phase_domain` proves its exact existential domain, so the span
introduces no extra vectors. -/
def phaseDomain (z : ℂ) : Submodule ℂ L2 :=
  Submodule.span ℂ (baseMap '' {u | boundaryCondition z u})

def phaseOperator (z : ℂ) : Operator ℂ L2 L2 :=
  maximal.domRestrict (phaseDomain z)

def thetaOperator (θ : ℝ) : Operator ℂ L2 L2 :=
  phaseOperator (Complex.exp ((θ : ℂ) * Complex.I))
end ExpandedFA.Unbounded.IntervalDerivative

namespace Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions
open _root_.ExpandedFA.Unbounded _root_.ExpandedFA.Unbounded.IntervalDerivative
open _root_.ExpandedFA.Sobolev.OneDimensional
open SymmetryAndDeficienciesSpec HilbertAdjointSpec

def Domain : Prop := ∀ (z : ℂ) (v : L2),
  v ∈ (phaseOperator z).domain ↔
    ∃ u : H1, baseLp u = v ∧ boundaryCondition z u

def Action : Prop := ∀ (z : ℂ) (u : H1)
  (h : baseLp u ∈ (phaseOperator z).domain),
    phaseOperator z ⟨baseLp u, h⟩ = (-Complex.I) • derivativeLp u

def Extension : Prop := ∀ z : ℂ, minimal ≤ phaseOperator z

def AdjointEquality : Prop := ∀ z : ℂ, ‖z‖ = 1 →
  adjointValue (phaseOperator z) = phaseOperator z

def SelfAdjoint : Prop := ∀ θ : ℝ, selfAdjointValue (thetaOperator θ)

/-- Both directions, with equality of partial maps (and hence exact domains
and actions), and the original half-open range of the real parameter. -/
def Classification : Prop := ∀ T : Operator ℂ L2 L2,
  (minimal ≤ T ∧ selfAdjointValue T) ↔
    ∃ θ ∈ Ico (0 : ℝ) (2 * Real.pi), T = thetaOperator θ
end Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions
