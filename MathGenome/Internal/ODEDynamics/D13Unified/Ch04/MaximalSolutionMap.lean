import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolution
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap

/-! Canonical maximal solutions, lifespan endpoints, and actual solution domains.
 The independent conditional choice is verified using unique maximal existence.
 All public objects reduce to the single shared choice in the Specs. -/
noncomputable section
open Set
open Specs.D13Unified.Ch04.MaximalSolutionMap

namespace D13Unified
universe u v

/-- See the independent `maximalDataValue` definition for domains and defaults. -/
def ODE.maximalData : maximalDataExpectedType := maximalDataValue

/-- See the independent `maximalIntervalValue` definition for domains and defaults. -/
def ODE.maximalInterval : maximalIntervalExpectedType := maximalIntervalValue

/-- See the independent `solutionCurveValue` definition for domains and defaults. -/
def ODE.solutionCurve : solutionCurveExpectedType := solutionCurveValue

/-- See the independent `lowerEndpointValue` definition for domains and defaults. -/
def ODE.lowerEndpoint : lowerEndpointExpectedType := lowerEndpointValue

/-- See the independent `upperEndpointValue` definition for domains and defaults. -/
def ODE.upperEndpoint : upperEndpointExpectedType := upperEndpointValue

/-- See the independent `solutionValueValue` definition for domains and defaults. -/
def ODE.solutionValue : solutionValueExpectedType := solutionValueValue

def ODE.solutionDomain : solutionDomainExpectedType := solutionDomainValue

def ODE.solutionMap : solutionMapExpectedType := solutionMapValue

/-- See the independent `parameterMaximalDataValue` definition for domains and defaults. -/
def ParameterODE.maximalData : parameterMaximalDataExpectedType := parameterMaximalDataValue

/-- See the independent `parameterMaximalIntervalValue` definition for domains and defaults. -/
def ParameterODE.maximalInterval : parameterMaximalIntervalExpectedType := parameterMaximalIntervalValue

/-- See the independent `parameterSolutionCurveValue` definition for domains and defaults. -/
def ParameterODE.solutionCurve : parameterSolutionCurveExpectedType := parameterSolutionCurveValue

/-- See the independent `parameterLowerEndpointValue` definition for domains and defaults. -/
def ParameterODE.lowerEndpoint : parameterLowerEndpointExpectedType := parameterLowerEndpointValue

/-- See the independent `parameterUpperEndpointValue` definition for domains and defaults. -/
def ParameterODE.upperEndpoint : parameterUpperEndpointExpectedType := parameterUpperEndpointValue

/-- See the independent `parameterSolutionValueValue` definition for domains and defaults. -/
def ParameterODE.solutionValue : parameterSolutionValueExpectedType := parameterSolutionValueValue

def ParameterODE.solutionDomain : parameterSolutionDomainExpectedType := parameterSolutionDomainValue

def ParameterODE.solutionMap : parameterSolutionMapExpectedType := parameterSolutionMapValue

/-- The full correctness statement for the canonical unparameterized choice. -/
theorem ODE.canonical_solution : canonicalSolutionExpected.{u} := by
  intro E _ _ _ F hF s ξ hs
  have h := Ch04.MaximalSolution.maximal_solution F hF s ξ hs
  have hx := Classical.choose_spec h
  have he := hx.2.2.2.1
  have hab := Classical.choose_spec (Classical.choose_spec he)
  unfold maximalDataValue
  rw [dite_eq_left h]
  exact ⟨(Classical.choose h).isSolution, hx.1, hx.2.1, hx.2.2.1,
    ⟨hab.1, hab.2.1, hab.2.2⟩, hx.2.2.2.2.1, hx.2.2.2.2.2⟩

/-- Parameterized correctness retains the entire original triple domain. -/
theorem ParameterODE.canonical_solution : parameterCanonicalSolutionExpected.{u, v} := by
  intro E _ _ _ P _ _ _ F hF s ξ p hs
  exact ODE.canonical_solution (F.atParameter p)
    (ParameterODE.LocallyLipschitzInState.atParameter F hF p) s ξ hs

/-- Evaluation on D has the value of the chosen curve and stays in U. -/
theorem ODE.solutionValue_on_domain : solutionValueExpected.{u} := by
  intro E _ _ _ F hF t s ξ ht
  have hv : solutionValueValue F t s ξ = solutionCurveValue F s ξ t := by
    unfold solutionValueValue
    exact dite_eq_left ht
  obtain ⟨hx, _⟩ := ODE.canonical_solution F hF s ξ ht.1
  exact ⟨hv, hv ▸ hx.2.1 t ht.2⟩

/-- Fixed-parameter evaluation agrees exactly with ordinary slice evaluation. -/
theorem ParameterODE.solutionValue_on_domain : parameterSolutionValueExpected.{u, v} := by
  intro E _ _ _ P _ _ _ F hF t s ξ p ht
  exact ODE.solutionValue_on_domain (F.atParameter p)
    (ParameterODE.LocallyLipschitzInState.atParameter F hF p) t s ξ ht

/-- The ambient totalization has the same classical IVP on the chosen interval. -/
theorem ODE.solutionValue_ivp : solutionValueIVPExpected.{u} := by
  intro E _ _ _ F hF s ξ hs
  obtain ⟨hx, hsi, hξ, _⟩ := ODE.canonical_solution F hF s ξ hs
  have heq : EqOn (fun t => solutionValueValue F t s ξ)
      (solutionCurveValue F s ξ) (maximalIntervalValue F s ξ).carrier := by
    intro t ht
    exact (ODE.solutionValue_on_domain F hF t s ξ ⟨hs, ht⟩).1
  have hwithin := (classical_iff_solutionOn F (maximalIntervalValue F s ξ)
    (solutionCurveValue F s ξ)).mp hx
  have hwithin' := (solutionOn_congr F (maximalIntervalValue F s ξ).toTimeInterval
    (solutionCurveValue F s ξ) (fun t => solutionValueValue F t s ξ) heq.symm).mp hwithin
  exact ⟨(classical_iff_solutionOn F (maximalIntervalValue F s ξ)
    (fun t => solutionValueValue F t s ξ)).mpr hwithin', hsi, (heq hsi).trans hξ⟩

/-- The parameter is held constant and the original parameter IVP is satisfied. -/
theorem ParameterODE.solutionValue_ivp : parameterSolutionValueIVPExpected.{u, v} := by
  intro E _ _ _ P _ _ _ F hF s ξ p hs
  apply (classicalParameterIVPOn_iff F p _ _ s ξ).mpr
  exact ODE.solutionValue_ivp (F.atParameter p)
    (ParameterODE.LocallyLipschitzInState.atParameter F hF p) s ξ hs

end D13Unified
