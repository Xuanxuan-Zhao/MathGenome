import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ProximalExistence
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.Existence

/-!
The MathGenome existence theorem applies to arbitrary real Hilbert spaces and
extended-valued functions. Its proof uses an affine minorant, the parallelogram
law, completeness, and a closed epigraph. Below we bridge the finite-domain,
convexity, semicontinuity and objective conventions explicitly.
-/
noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis

def proximalObjective : Specs.proximalObjectiveType.{u} := Specs.proximalObjective
def moreauEnvelope : Specs.moreauEnvelopeType.{u} := Specs.moreauEnvelope
def IsProximalMinimizer : Specs.IsProximalMinimizerType.{u} := Specs.IsProximalMinimizer
def proximalMap : Specs.proximalMapType.{u} := Specs.proximalMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem proximalObjective_eq_mathGenome (f : H → WithTop ℝ) (μ : ℝ) (x z : H) :
    proximalObjective f μ x z = ExpandedFA.Proximal.proximalObjective H f μ x z := by
  change f z + ((‖z - x‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ) =
    f z + ((‖x - z‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ)
  rw [norm_sub_rev z x]

theorem isProximalMinimizer_iff_mathGenome (f : H → WithTop ℝ) (μ : ℝ) (x p : H) :
    IsProximalMinimizer f μ x p ↔ ExpandedFA.Proximal.IsProximalMinimizer H f μ x p := by
  change (f p < ⊤ ∧ ∀ z, proximalObjective f μ x p ≤ proximalObjective f μ x z) ↔
    (f p ≠ ⊤ ∧ ∀ z, ExpandedFA.Proximal.proximalObjective H f μ x p ≤
      ExpandedFA.Proximal.proximalObjective H f μ x z)
  simp only [WithTop.lt_top_iff_ne_top, proximalObjective_eq_mathGenome]

theorem exists_unique_proximalMinimizer : Specs.exists_unique_proximalMinimizer.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  have hp' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue H f := by
    obtain ⟨z, hz⟩ := hp
    exact ⟨z, ne_of_lt hz⟩
  have hc' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H f :=
    (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H f).mpr hc
  have hl' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H f :=
    (lowerSemicontinuous_iff_closed_sublevels f).mp hl
  obtain ⟨p, hpmin, huniq⟩ :=
    ExpandedFA.Proximal.exists_unique_proximalMinimizer H f hp' hc' hl' μ hμ x
  refine ⟨p, (isProximalMinimizer_iff_mathGenome f μ x p).mpr hpmin, ?_⟩
  intro z hz
  exact huniq z ((isProximalMinimizer_iff_mathGenome f μ x z).mp hz)

theorem proximalMap_minimizes : Specs.proximalMap_minimizes.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  exact Classical.epsilon_spec (exists_unique_proximalMinimizer f hp hc hl μ hμ x).exists

theorem minimizer_iff_eq_proximalMap : Specs.minimizer_iff_eq_proximalMap.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x p
  have hP := proximalMap_minimizes f hp hc hl μ hμ x
  constructor
  · intro h
    exact (exists_unique_proximalMinimizer f hp hc hl μ hμ x).unique h hP
  · intro h
    simpa only [h] using hP

theorem moreauEnvelope_eq_objective : Specs.moreauEnvelope_eq_objective.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  have hP := proximalMap_minimizes f hp hc hl μ hμ x
  apply le_antisymm (iInf_le _ (proximalMap f μ x))
  exact le_iInf fun z => WithBot.coe_le_coe.mpr (hP.2 z)

theorem moreauEnvelope_finite : Specs.moreauEnvelope_finite.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  have hP := proximalMap_minimizes f hp hc hl μ hμ x
  obtain ⟨r, hr⟩ := (mem_domain_iff f (proximalMap f μ x)).mp hP.1
  refine ⟨r + ‖proximalMap f μ x - x‖ ^ 2 / (2 * μ), ?_⟩
  rw [moreauEnvelope_eq_objective f hp hc hl μ hμ x]
  change toEReal (f (proximalMap f μ x) + _) = _
  rw [hr]
  rfl

end VariationalNotes.ConvexAnalysis
