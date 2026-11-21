import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.OpenDomain
import Mathlib.Topology.Semicontinuity.Defs

/-! Independent statements of `paper.tex`, Corollary d13:05:lifespan.
The endpoints are the canonical maximal endpoints, valued in `EReal`.
The source is the subtype of the actual open joint initial-data domain,
with coordinates `((s, ξ), p)`. Semicontinuity tests all extended-real
thresholds, in particular every finite threshold at an infinite endpoint.
No differentiability in the parameter or product shape of the domain is assumed.
-/
noncomputable section
namespace Specs.D13Unified.Ch05.Lifespan
open _root_.D13Unified
open Ch03.LocalLipschitz Ch04.MaximalSolutionMap
universe u v

/-- The forward endpoint is lower semicontinuous on the initial-data domain. -/
def lowerSemicontinuousUpperEndpointExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), parameterLocallyLipschitzInStateValue F →
      LowerSemicontinuous (fun q : F.domain =>
        parameterUpperEndpointValue F q.val.1.1 q.val.1.2 q.val.2)

/-- The backward endpoint is upper semicontinuous on the same domain. -/
def upperSemicontinuousLowerEndpointExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), parameterLocallyLipschitzInStateValue F →
      UpperSemicontinuous (fun q : F.domain =>
        parameterLowerEndpointValue F q.val.1.1 q.val.1.2 q.val.2)

end Specs.D13Unified.Ch05.Lifespan
