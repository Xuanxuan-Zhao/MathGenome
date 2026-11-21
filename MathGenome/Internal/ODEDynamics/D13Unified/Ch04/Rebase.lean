import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.Rebase

/-! Changing the base time of a maximal solution, without translating the
nonautonomous field. The original maximal solution is also maximal through
its value at the new time, so uniqueness of maximal solutions applies. -/
noncomputable section
open Set
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch04.Rebase

namespace D13Unified
universe u v

/-- The maximal interval and solution values are unchanged on rebasing. -/
theorem ODE.rebase : rebaseExpected.{u} := by
  intro E _ _ _ F hF s ξ hs r hr η hη
  obtain ⟨hx, hsi, hxξ, hxm, hends, hcover, hunique⟩ :=
    ODE.canonical_solution F hF s ξ hs
  have hvr := ODE.solutionValue_on_domain F hF r s ξ ⟨hs, hr⟩
  have hrη : (r, η) ∈ F.domain := hη.symm ▸ hvr.2
  obtain ⟨hy, hri, hyη, hym, hyends, hycover, hyunique⟩ :=
    ODE.canonical_solution F hF r η hrη
  let x : Solution F :=
    ⟨maximalIntervalValue F s ξ, solutionCurveValue F s ξ, hx⟩
  have hxr : x.representative r = η := hvr.1.symm.trans hη.symm
  obtain ⟨hI, heq⟩ := hyunique x hr hxr hxm
  change (maximalIntervalValue F s ξ).carrier =
    (maximalIntervalValue F r η).carrier at hI
  change EqOn (solutionCurveValue F s ξ) (solutionCurveValue F r η)
    (maximalIntervalValue F s ξ).carrier at heq
  refine ⟨hI.symm, ?_⟩
  intro t ht
  have hty : t ∈ (maximalIntervalValue F r η).carrier := hI ▸ ht
  exact (ODE.solutionValue_on_domain F hF t r η ⟨hrη, hty⟩).1.trans
    ((heq ht).symm.trans (ODE.solutionValue_on_domain F hF t s ξ ⟨hs, ht⟩).1.symm)

/-- Rebasing on a fixed parameter slice preserves the original absolute times,
parameter, actual interval and all solution values there. -/
theorem ParameterODE.rebase : parameterRebaseExpected.{u, v} := by
  intro E _ _ _ P _ _ _ F hF s ξ p hs r hr η hη
  exact ODE.rebase (F.atParameter p)
    (ParameterODE.LocallyLipschitzInState.atParameter F hF p) s ξ hs r hr η hη

end D13Unified
