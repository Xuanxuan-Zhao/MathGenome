import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NeumannResolvent
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.NonemptySpectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
The nonempty compact spectrum assertion of `fa2:p2:spectrum-radius`.

Mathlib's spectrum is definitionally the accepted set
{z | ¬ IsUnit (algebraMap ℂ A z - a)}. Its nonemptiness theorem applies
to arbitrary nontrivial complete normed complex algebras, including
noncommutative ones. That theorem uses the Banach-valued Liouville
theorem on the entire resolvent and its limit zero at infinity.
Compactness uses openness of the resolvent set and the Neumann bound;
the normalization ‖1‖ = 1 gives the stated radius ‖a‖.
-/

namespace ExpandedFA.BanachAlgebra

open Specs.ExpandedFA.BanachAlgebra.NonemptySpectrum

universe u

theorem algebra_spectrum_properties : SpectrumProperties.{u} := by
  intro A _ _ hA a
  let : CompleteSpace A := hA.1
  let : Nontrivial A := hA.2.1
  let : NormOneClass A := hA.2.2
  change (spectrum ℂ a).Nonempty ∧ IsCompact (spectrum ℂ a) ∧
    spectrum ℂ a ⊆ {z : ℂ | ‖z‖ ≤ ‖a‖}
  exact ⟨spectrum.nonempty a, spectrum.isCompact a,
    fun _ hz => spectrum.norm_le_norm_of_mem hz⟩

end ExpandedFA.BanachAlgebra
