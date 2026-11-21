import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.SelfAdjointSpectrumNormalRadius
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.Unitization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.SpectralRadius
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! Fundamental C*-spectral facts, without representations or order assumptions.
Mathlib's self-adjoint spectrum proof uses the unitary exp(i a), exponential
spectral mapping, and the unitary spectrum bound. Its normal-radius proof uses
the C*-identity, commuting powers and Gelfand's formula. We identify its
extended-real radius with the manuscript's real supremum using the accepted
Banach-algebra bridge. The nonunital statements apply these proofs in the
native C*-unitization, whose inclusion preserves the original norm and star.
-/

noncomputable section
namespace ExpandedFA.CStar.SelfAdjointSpectrumNormalRadius
universe u

theorem unital_selfAdjoint_spectrum : Spec.UnitalSelfAdjointSpectrum.{u} := by
  intro A _ a ha z hz
  exact ha.im_eq_zero_of_mem_spectrum hz

theorem unital_normal_radius : Spec.UnitalNormalRadius.{u} := by
  intro A _ a ha
  let : IsStarNormal a := ha
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let : Subsingleton A := h
    change sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ a) = ‖a‖
    rw [spectrum.of_subsingleton, Set.image_empty, Real.sSup_empty,
      Subsingleton.elim a 0, norm_zero]
  | inr h =>
    let : Nontrivial A := h
    have hA : ExpandedFA.BanachAlgebra.IsUnitalBanachAlgebra A :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    have hr := ExpandedFA.BanachAlgebra.algebraSpectralRadius_eq_native A hA a
    have hnonneg :=
      (ExpandedFA.BanachAlgebra.algebraSpectralRadius_maximum A hA a).2.2.1
    have ht := congrArg ENNReal.toReal hr
    simpa only [ENNReal.toReal_ofReal hnonneg,
      IsStarNormal.spectralRadius_eq_nnnorm, ENNReal.coe_toReal,
      coe_nnnorm] using ht

theorem nonunital_selfAdjoint_spectrum : Spec.NonunitalSelfAdjointSpectrum.{u} := by
  intro A _ a ha
  exact unital_selfAdjoint_spectrum (Unitization ℂ A)
    (Unitization.inrNonUnitalStarAlgHom ℂ A a)
    (ha.map (Unitization.inrNonUnitalStarAlgHom ℂ A))

theorem nonunital_normal_radius : Spec.NonunitalNormalRadius.{u} := by
  intro A _ a ha
  have hi : IsStarNormal (Unitization.inr a : Unitization ℂ A) :=
    (Unitization.isStarNormal_inr (R := ℂ)).mpr ha
  have hr := unital_normal_radius (Unitization ℂ A) (Unitization.inr a) hi
  change sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ
    (Unitization.inr a : Unitization ℂ A)) = ‖a‖
  change sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ
    (Unitization.inr a : Unitization ℂ A)) = ‖(Unitization.inr a : Unitization ℂ A)‖ at hr
  simpa only [Unitization.norm_inr] using hr

theorem banach_nonunital_normal_radius : Spec.BanachNonunitalNormalRadius.{u} := by
  intro A _ a ha
  have hr := nonunital_normal_radius A a ha
  rw [Conventions.nonunitalSpectrum_eq_banach A a] at hr
  exact hr

end ExpandedFA.CStar.SelfAdjointSpectrumNormalRadius
