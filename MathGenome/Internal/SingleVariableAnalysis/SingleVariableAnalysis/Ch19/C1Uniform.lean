import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.C1Uniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.C1Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Uniqueness

/-! Absolute uniform convergence to the periodic extension.
The upstream C1Absolute theorem constructs the sum and preserves its
coefficients; uniqueness identifies it with the continuous extension below.
Only values, not derivatives, are matched at the period seams. -/
noncomputable section
namespace SingleVariableAnalysis
open Set Riemann
open scoped BigOperators

abbrev fourierPeriodicExtension :=
  Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue

/-- A continuous function with matching endpoint values descends to the circle. -/
theorem fourier_periodic_extension :
    Specs.SingleVariableAnalysis.Ch19.C1Uniform.extensionProperties := by
  intro f hf hend
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hseam : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hend' : f (-Real.pi) = f (-Real.pi + 2 * Real.pi) := by
    rwa [hseam]
  have hc : Continuous (fourierPeriodicExtension f) :=
    (AddCircle.liftIco_continuous hend' (by rwa [hseam])).comp
      (AddCircle.continuous_mk' (2 * Real.pi))
  have hp : Function.Periodic (fourierPeriodicExtension f) (2 * Real.pi) := by
    intro x
    change AddCircle.liftIco _ _ f (↑(x + 2 * Real.pi)) =
      AddCircle.liftIco _ _ f (↑x)
    rw [AddCircle.coe_add_period]
  have he : EqOn (fourierPeriodicExtension f) f (Icc (-Real.pi) Real.pi) := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · exact AddCircle.liftIco_coe_apply ⟨hx.1, by rwa [hseam]⟩
    · rw [← hseam, hp (-Real.pi)]
      change AddCircle.liftIco _ _ f (↑(-Real.pi)) = _
      rw [AddCircle.liftIco_coe_apply (by constructor <;> linarith [Real.pi_pos])]
      exact hend'
  exact ⟨hc, hp, he⟩

namespace Fourier

/-- The coefficient is determined by the values on the closed reference period. -/
lemma coefficient_eq_of_eqOn {f g : ℝ → ℂ}
    (hf : FourierProjection.Integrable f) (hg : FourierProjection.Integrable g)
    (Hf : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f)
    (Hg : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights g)
    (h : EqOn f g (Icc (-Real.pi) Real.pi)) (n : ℤ) :
    fourierCoeff f n (Hf n) = fourierCoeff g n (Hg n) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact FourierAbsolute.coefficient_distance_le hf hg Hf Hg n (M := 0)
    (fun x hx => by rw [h hx, sub_self, norm_zero])

end Fourier

/-- K03.19.c1_uniform: the absolute uniform Fourier sum equals the actual
periodic extension at every real argument. -/
theorem fourier_c1_uniform_to_extension :
    Specs.SingleVariableAnalysis.Ch19.C1Uniform.absoluteUniformToExtension := by
  intro f hf hend
  obtain ⟨H, hs, g, hgc, hgp, hu, ha, hsum, Hg, hcoeff⟩ :=
    fourier_c1_absolute_uniform f hf hend
  obtain ⟨hec, hep, heq⟩ := fourier_periodic_extension f hf.continuousOn hend
  have hfi := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hf.continuousOn
  have hei := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hec.continuousOn
  let He := fourierCoeff_integrable _ hei
  have hce (n : ℤ) : fourierCoeff (fourierPeriodicExtension f) n (He n) =
      fourierCoeff f n (H n) :=
    Fourier.coefficient_eq_of_eqOn hei hfi He H heq n
  have hge : g = fourierPeriodicExtension f :=
    fourierCoeff_unique g (fourierPeriodicExtension f) hgc hec hgp hep Hg He
      (fun n => (hcoeff n).trans (hce n).symm)
  rw [hge] at hu hsum
  exact ⟨H, hs, hec, hep, heq, hu, ha, hsum⟩

end SingleVariableAnalysis
