import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Rectifiable
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.C1Variation

/-! K03.15.rectifiable: length and rectifiability of continuous paths.
The length/variation bridge follows from their identical strict endpoint
partition formulas. The C¹ formula reuses the upstream proper Riemann theorem.
-/
namespace SingleVariableAnalysis.BV
universe u

abbrev IsContinuousPath := @Specs.SingleVariableAnalysis.Ch15.Rectifiable.continuousPathValue
noncomputable abbrev pathLength := @Specs.SingleVariableAnalysis.Ch15.Rectifiable.pathLengthValue
abbrev IsRectifiable := @Specs.SingleVariableAnalysis.Ch15.Rectifiable.rectifiableValue

theorem pathLength_eq_variation :
    Specs.SingleVariableAnalysis.Ch15.Rectifiable.lengthEqVariation := by
  intro E _ f a b hp
  rfl

theorem rectifiable_iff_continuous_bv :
    Specs.SingleVariableAnalysis.Ch15.Rectifiable.rectifiableIffContinuousBV := by
  intro E _ f a b
  constructor
  · rintro ⟨hp, hfinite⟩
    exact ⟨hp, hfinite⟩
  · rintro ⟨hp, hfinite⟩
    exact ⟨hp, hfinite⟩

theorem rectifiable_iff_finite_length :
    Specs.SingleVariableAnalysis.Ch15.Rectifiable.rectifiableIffFiniteLength := by
  intro E _ f a b hp
  constructor
  · rintro ⟨_, hfinite⟩
    exact hfinite
  · intro hfinite
    exact ⟨hp, hfinite⟩

theorem pathLength_degenerate :
    Specs.SingleVariableAnalysis.Ch15.Rectifiable.degenerateLength := by
  intro E _ f a hp
  rw [pathLength_eq_variation]
  exact totalVariation_degenerate f a

theorem discontinuous_not_path :
    Specs.SingleVariableAnalysis.Ch15.Rectifiable.discontinuousNotPath := by
  intro E _ f a b hdiscontinuous
  constructor
  · intro hp
    exact hdiscontinuous hp.2
  · rintro ⟨hp, _⟩
    exact hdiscontinuous hp.2

theorem c1_path_length : Specs.SingleVariableAnalysis.Ch15.Rectifiable.c1PathLength := by
  intro E _ _ f g a b hab hd hg
  have hp : IsContinuousPath f a b :=
    ⟨hab, fun x hx => (hd x hx).continuousWithinAt⟩
  obtain ⟨hn, heq⟩ := c1_variation f g a b hab hd hg
  have hlength : pathLength f a b hp =
      ENNReal.ofReal (Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue
        (fun x => ‖g x‖) hn) := (pathLength_eq_variation f a b hp).trans heq
  refine ⟨hp, hn, hlength, hp, ?_⟩
  change pathLength f a b hp < ⊤
  rw [hlength]
  exact ENNReal.ofReal_lt_top

end SingleVariableAnalysis.BV
