import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.EnvelopeGradient
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ProximalCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.EnvelopeGradient

noncomputable section
open scoped InnerProductSpace
universe u
namespace VariationalNotes.ConvexAnalysis

def realMoreauEnvelope : Specs.realMoreauEnvelopeType.{u} := Specs.realMoreauEnvelope
def moreauGradient : Specs.moreauGradientType.{u} := Specs.moreauGradient

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Both infima use the same extended-real objective; the squared norm is
unchanged by reversing the displacement. This bridge needs no existence. -/
lemma moreauEnvelope_eq_mathGenome (f : H → WithTop ℝ) (μ : ℝ) (x : H) :
    moreauEnvelope f μ x = ExpandedFA.Proximal.moreauEnvelope H f μ x := by
  apply iInf_congr
  intro z
  change toEReal (proximalObjective f μ x z) =
    toEReal (ExpandedFA.Proximal.proximalObjective H f μ x z)
  rw [proximalObjective_eq_mathGenome]

lemma realMoreauEnvelope_eq_mathGenome (f : H → WithTop ℝ) (μ : ℝ) :
    realMoreauEnvelope f μ = ExpandedFA.Proximal.realMoreauEnvelope H f μ := by
  funext x
  change (moreauEnvelope f μ x).toReal =
    (ExpandedFA.Proximal.moreauEnvelope H f μ x).toReal
  rw [moreauEnvelope_eq_mathGenome]

/-- Uniqueness identifies the two total choices under the original hypotheses. -/
lemma proximalMap_eq_mathGenome [CompleteSpace H] (f : H → WithTop ℝ)
    (hp : Proper f) (hc : IsConvex f) (hl : IsLowerSemicontinuous f)
    (μ : ℝ) (hμ : 0 < μ) (x : H) :
    proximalMap f μ x = ExpandedFA.Proximal.proximalMap H f μ x := by
  have hc' := (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H f).mpr hc
  have hl' := (lowerSemicontinuous_iff_closed_sublevels f).mp hl
  have hp' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue H f := by
    obtain ⟨z, hz⟩ := hp
    exact ⟨z, ne_of_lt hz⟩
  have hm := ExpandedFA.Proximal.proximalMap_minimizes H f hp' hc' hl' μ hμ x
  exact ((minimizer_iff_eq_proximalMap f hp hc hl μ hμ x _).mp
    ((isProximalMinimizer_iff_mathGenome f μ x _).mpr hm)).symm

lemma moreauGradient_eq_mathGenome [CompleteSpace H] (f : H → WithTop ℝ)
    (hp : Proper f) (hc : IsConvex f) (hl : IsLowerSemicontinuous f)
    (μ : ℝ) (hμ : 0 < μ) (x : H) :
    moreauGradient f μ x = ExpandedFA.Proximal.moreauGradient H f μ x := by
  change μ⁻¹ • (x - proximalMap f μ x) =
    μ⁻¹ • (x - ExpandedFA.Proximal.proximalMap H f μ x)
  rw [proximalMap_eq_mathGenome f hp hc hl μ hμ x]

theorem realMoreauEnvelope_coe : Specs.realMoreauEnvelope_coe.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  obtain ⟨r, hr⟩ := moreauEnvelope_finite f hp hc hl μ hμ x
  change moreauEnvelope f μ x = (r : EReal) at hr
  change moreauEnvelope f μ x = ((moreauEnvelope f μ x).toReal : EReal)
  rw [hr, EReal.toReal_coe]

/-- A supporting functional at each point, inherited from the proximal
subgradient, proves convexity by applying it at the convex combination. -/
lemma realMoreauEnvelope_support [CompleteSpace H] (f : H → WithTop ℝ)
    (hp : Proper f) (hc : IsConvex f) (hl : IsLowerSemicontinuous f)
    (μ : ℝ) (hμ : 0 < μ) (x y : H) :
    0 ≤ realMoreauEnvelope f μ y - realMoreauEnvelope f μ x -
      ⟪moreauGradient f μ x, y - x⟫_ℝ := by
  have hp' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue H f := by
    obtain ⟨z, hz⟩ := hp
    exact ⟨z, ne_of_lt hz⟩
  have hc' := (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H f).mpr hc
  have hl' := (lowerSemicontinuous_iff_closed_sublevels f).mp hl
  rw [realMoreauEnvelope_eq_mathGenome, moreauGradient_eq_mathGenome f hp hc hl μ hμ]
  exact (ExpandedFA.Proximal.moreauEnvelope_remainder f hp' hc' hl' μ hμ x y).1

theorem realMoreauEnvelope_convex : Specs.realMoreauEnvelope_convex.{u} := by
  intro H _ _ _ f hp hc hl μ hμ
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := realMoreauEnvelope_support f hp hc hl μ hμ z x
  have hy := realMoreauEnvelope_support f hp hc hl μ hμ z y
  have hi : a * ⟪moreauGradient f μ z, x - z⟫_ℝ +
      b * ⟪moreauGradient f μ z, y - z⟫_ℝ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have hz : a • (x - z) + b • (y - z) = (0 : H) := by
      rw [smul_sub, smul_sub]
      calc
        a • x - a • z + (b • y - b • z) = z - (a + b) • z := by
          dsimp [z]
          rw [add_smul]
          abel
        _ = 0 := by rw [hab, one_smul, sub_self]
    rw [hz, inner_zero_right]
  have hx' := mul_nonneg ha hx
  have hy' := mul_nonneg hb hy
  change realMoreauEnvelope f μ z ≤ a * realMoreauEnvelope f μ x +
    b * realMoreauEnvelope f μ y
  have hz := congrArg (fun c : ℝ => c * realMoreauEnvelope f μ z) hab
  nlinarith only [hx', hy', hi, hz]

theorem realMoreauEnvelope_hasFDerivAt : Specs.realMoreauEnvelope_hasFDerivAt.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  have hp' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue H f := by
    obtain ⟨z, hz⟩ := hp
    exact ⟨z, ne_of_lt hz⟩
  have hc' := (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H f).mpr hc
  have hl' := (lowerSemicontinuous_iff_closed_sublevels f).mp hl
  change HasFDerivAt (realMoreauEnvelope f μ)
    (InnerProductSpace.toDual ℝ H (moreauGradient f μ x)) x
  rw [realMoreauEnvelope_eq_mathGenome, moreauGradient_eq_mathGenome f hp hc hl μ hμ]
  exact ExpandedFA.Proximal.realMoreauEnvelope_hasFDerivAt f hp' hc' hl' μ hμ x

theorem moreauGradient_lipschitz : Specs.moreauGradient_lipschitz.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x y
  change ‖μ⁻¹ • (x - proximalMap f μ x) - μ⁻¹ • (y - proximalMap f μ y)‖ ≤
    ‖x - y‖ / μ
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμ)]
  calc
    μ⁻¹ * ‖(x - proximalMap f μ x) - (y - proximalMap f μ y)‖ ≤
        μ⁻¹ * ‖x - y‖ := mul_le_mul_of_nonneg_left
      (proximalResidual_nonexpansive f hp hc hl μ hμ x y) (inv_nonneg.mpr hμ.le)
    _ = ‖x - y‖ / μ := by rw [div_eq_mul_inv, mul_comm]

end VariationalNotes.ConvexAnalysis
