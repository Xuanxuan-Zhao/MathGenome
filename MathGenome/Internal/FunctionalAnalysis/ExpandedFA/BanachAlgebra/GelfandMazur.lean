import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.SpectralRadius
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.GelfandMazur

/-!
The complete spectrum-and-radius theorem and its Gelfand–Mazur consequence.
The preceding spectral conclusions use the accepted spectral and resolvent
theorems with exactly the chapter's hypotheses. For the remaining consequence,
choose a spectral value z of a. Since z1-a is not a unit and every nonzero
element is a unit, z1=a. The normalized scalar inclusion is an isometry,
hence injective; its surjectivity gives the canonical algebra equivalence.
-/

namespace ExpandedFA.BanachAlgebra

open Specs.ExpandedFA.BanachAlgebra.GelfandMazur

universe u

theorem spectrum_and_spectral_radius : SpectrumAndRadius.{u} := by
  intro A _ _ hA a
  obtain ⟨hne, hc, hbound⟩ := algebra_spectrum_properties A hA a
  exact ⟨hne, hc, hbound, algebra_resolvent_analytic A hA a,
    algebra_resolvent_identity A hA a, algebraSpectralRadius_root_limit A hA a,
    algebraSpectralRadius_root_infimum A hA a⟩

theorem division_algebra_scalar_representation : ScalarRepresentation.{u} := by
  intro A _ _ hA hdiv a
  let : NormOneClass A := hA.2.2
  obtain ⟨z, hz⟩ := (algebra_spectrum_properties A hA a).1
  have heq : algebraMap ℂ A z = a := by
    have hn : ¬ IsUnit (algebraMap ℂ A z - a) := hz
    by_contra h
    exact hn (hdiv _ (sub_ne_zero.mpr h))
  refine ⟨z, ?_, ?_⟩
  · simpa only [Algebra.algebraMap_eq_smul_one] using heq
  · intro w hw
    apply (algebraMap_isometry ℂ A).injective
    simpa only [Algebra.algebraMap_eq_smul_one] using hw.trans
      (by simpa only [Algebra.algebraMap_eq_smul_one] using heq.symm)

theorem gelfand_mazur : CanonicalIsometricIdentification.{u} := by
  intro A _ _ hA hdiv
  let : NormOneClass A := hA.2.2
  have hsurj : Function.Surjective (algebraMap ℂ A) := by
    intro a
    obtain ⟨z, hz, _⟩ := division_algebra_scalar_representation A hA hdiv a
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  let e : ℂ ≃ₐ[ℂ] A := AlgEquiv.ofBijective (Algebra.ofId ℂ A)
    ⟨(algebraMap_isometry ℂ A).injective, hsurj⟩
  have he : ∀ z : ℂ, e z = algebraMap ℂ A z := fun _ => rfl
  refine ⟨e, ⟨?_, ?_⟩, ?_⟩
  · intro z
    rw [he, Algebra.algebraMap_eq_smul_one]
  · change Isometry (algebraMap ℂ A)
    exact algebraMap_isometry ℂ A
  · intro f hf
    ext z
    rw [hf.1 z, he z, Algebra.algebraMap_eq_smul_one]

end ExpandedFA.BanachAlgebra
