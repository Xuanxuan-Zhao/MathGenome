import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.MoreauDecomposition
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.EnvelopeGradient
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.HilbertProjection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.MoreauDecomposition

noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis

def hilbertConjugateFunction : Specs.hilbertConjugateFunctionType.{u} :=
  Specs.hilbertConjugateFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The finite-domain supremum in the manuscript equals the unrestricted
supremum used by MathGenome: infinite primal values contribute minus infinity. -/
lemma hilbertConjugateFunction_eq_mathGenome (f : H → WithTop ℝ) :
    hilbertConjugateFunction f = ExpandedFA.Proximal.conjugateFunction H f := by
  funext w
  change (conjugate f (InnerProductSpace.toDual ℝ H w)).unbotD ⊤ =
    (ExpandedFA.Proximal.hilbertConjugate H f w).unbotD ⊤
  have he : conjugate f (InnerProductSpace.toDual ℝ H w) =
      ExpandedFA.Proximal.hilbertConjugate H f w :=
    conjugate_eq_iSup_sub f (InnerProductSpace.toDual ℝ H w)
  exact congrArg (fun t : EReal => t.unbotD ⊤) he

theorem hilbertConjugateFunction_identification :
    Specs.hilbertConjugateFunction_identification.{u} := by
  intro H _ _ _ f hp w
  have hn := conjugate_ne_bot f hp (InnerProductSpace.toDual ℝ H w)
  change WithBot.some ((Specs.conjugate f (InnerProductSpace.toDual ℝ H w)).unbotD ⊤) =
    Specs.conjugate f (InnerProductSpace.toDual ℝ H w)
  obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hn
  rw [← hr]
  rfl

theorem hilbertConjugateFunction_regular : Specs.hilbertConjugateFunction_regular.{u} := by
  intro H _ _ _ f hp hc hl
  have hp' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue H f := by
    obtain ⟨z, hz⟩ := hp
    exact ⟨z, ne_of_lt hz⟩
  have hc' := (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H f).mpr hc
  have hl' := (lowerSemicontinuous_iff_closed_sublevels f).mp hl
  obtain ⟨hpr, hcr, hlr⟩ := ExpandedFA.Proximal.conjugateFunction_regular H f hp' hc' hl'
  change Proper (hilbertConjugateFunction f) ∧ IsConvex (hilbertConjugateFunction f) ∧
    IsLowerSemicontinuous (hilbertConjugateFunction f)
  rw [hilbertConjugateFunction_eq_mathGenome]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hpr
    exact ⟨w, lt_top_iff_ne_top.mpr hw⟩
  · exact (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H _).mp hcr
  · exact (lowerSemicontinuous_iff_closed_sublevels _).mpr hlr

theorem moreau_decomposition : Specs.moreau_decomposition.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  have hp' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue H f := by
    obtain ⟨z, hz⟩ := hp
    exact ⟨z, ne_of_lt hz⟩
  have hc' := (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H f).mpr hc
  have hl' := (lowerSemicontinuous_iff_closed_sublevels f).mp hl
  obtain ⟨hd, r, s, a, b, _, _, _, _, ha, hb, he⟩ :=
    ExpandedFA.Proximal.moreau_decomposition H f hp' hc' hl' μ hμ x
  obtain ⟨hpr, hcr, hlr⟩ := hilbertConjugateFunction_regular f hp hc hl
  have hpmap := proximalMap_eq_mathGenome f hp hc hl μ hμ x
  have hqmap := proximalMap_eq_mathGenome (hilbertConjugateFunction f) hpr hcr hlr
    μ⁻¹ (inv_pos.mpr hμ) (μ⁻¹ • x)
  rw [hilbertConjugateFunction_eq_mathGenome] at hqmap
  change x = proximalMap f μ x +
      μ • proximalMap (hilbertConjugateFunction f) μ⁻¹ (μ⁻¹ • x) ∧ _
  constructor
  · rw [hpmap, hilbertConjugateFunction_eq_mathGenome, hqmap]
    exact hd.symm
  · change moreauEnvelope f μ x +
      moreauEnvelope (hilbertConjugateFunction f) μ⁻¹ (μ⁻¹ • x) = _
    rw [moreauEnvelope_eq_mathGenome, hilbertConjugateFunction_eq_mathGenome,
      moreauEnvelope_eq_mathGenome]
    change ExpandedFA.Proximal.moreauEnvelope H f μ x = (a : EReal) at ha
    change ExpandedFA.Proximal.moreauEnvelope H (ExpandedFA.Proximal.conjugateFunction H f)
      μ⁻¹ (μ⁻¹ • x) = (b : EReal) at hb
    rw [ha, hb, ← EReal.coe_add, he]

/-- For an indicator, minimizing the proximal objective is precisely finding
a nearest point. This also identifies the total Hilbert-epsilon choice without
adding regularity assumptions to its input. -/
theorem proximalMap_indicator_eq_projection : Specs.proximalMap_indicator_eq_projection.{u} := by
  intro H _ _ _ C hne hclosed hconv μ hμ x
  classical
  let p := VariationalNotes.Existence.realProjection C hne hclosed hconv x
  have hp := VariationalNotes.Existence.realProjection_nearest C hne hclosed hconv x
  change p ∈ C ∧ ∀ z ∈ C, ‖x - p‖ ≤ ‖x - z‖ at hp
  have hmin : IsProximalMinimizer (indicator C) μ x p := by
    refine ⟨?_, ?_⟩
    · simp [indicator, Specs.indicator, hp.1]
    · intro z
      by_cases hz : z ∈ C
      · change indicator C p + _ ≤ indicator C z + _
        have hn : ‖p - x‖ ^ 2 ≤ ‖z - x‖ ^ 2 := by
          rw [norm_sub_rev p x, norm_sub_rev z x]
          exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hp.2 z hz)
        simpa only [indicator, Specs.indicator, ite_eq_left hp.1, ite_eq_left hz,
          zero_add, WithTop.coe_le_coe] using
          (div_le_div_of_nonneg_right hn (mul_pos two_pos hμ).le)
      · simp [Specs.proximalObjective, indicator, Specs.indicator, hz]
  have hq : IsProximalMinimizer (indicator C) μ x (proximalMap (indicator C) μ x) :=
    Classical.epsilon_spec ⟨p, hmin⟩
  let q := proximalMap (indicator C) μ x
  have hqC : q ∈ C := by
    by_contra hn
    have hqfinite : indicator C q < ⊤ := hq.1
    simp [indicator, Specs.indicator, hn] at hqfinite
  apply (VariationalNotes.Existence.realProjection_unique C hne hclosed hconv x q).mp
  refine ⟨hqC, ?_⟩
  intro z hz
  have hi := hq.2 z
  change indicator C q + _ ≤ indicator C z + _ at hi
  simp only [indicator, Specs.indicator, ite_eq_left hqC, ite_eq_left hz,
    zero_add, WithTop.coe_le_coe] at hi
  have hs := (div_le_div_iff_of_pos_right (mul_pos two_pos hμ)).mp hi
  rw [norm_sub_rev q x, norm_sub_rev z x] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem moreau_theorem : Specs.moreau_theorem.{u} := by
  intro H _ _ _ f hp hc hl μ hμ
  exact ⟨realMoreauEnvelope_coe f hp hc hl μ hμ,
    realMoreauEnvelope_convex f hp hc hl μ hμ,
    realMoreauEnvelope_hasFDerivAt f hp hc hl μ hμ,
    moreauGradient_lipschitz f hp hc hl μ hμ,
    moreau_decomposition f hp hc hl μ hμ⟩

end VariationalNotes.ConvexAnalysis
