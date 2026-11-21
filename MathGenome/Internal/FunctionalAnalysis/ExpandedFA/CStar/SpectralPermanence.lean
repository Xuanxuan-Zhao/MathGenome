import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.SpectralPermanence
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
C*-spectral permanence, without a commutativity assumption.

The library proof of `StarSubalgebra.coe_isUnit` first obtains spectral
equality for self-adjoint elements using connectedness of their spectral
complements and Banach-subalgebra permanence. For a general ambient unit a,
both star a * a and a * star a are ambient units and self-adjoint. Their
spectral equalities transfer invertibility to the subalgebra. The resulting
left and right inverses of a agree. Thus the general case uses invertibility
of star a * a, not a boundary argument applied to a general spectrum.
-/

namespace ExpandedFA.CStar.SpectralPermanence
universe u

theorem invertibility_permanence : Spec.InvertibilityPermanence.{u} := by
  intro A _ B hB a
  let : IsClosed (B : Set A) := hB
  exact B.coe_isUnit

theorem spectral_permanence : Spec.SpectrumEquality.{u} := by
  intro A _ B hB a
  change spectrum ℂ a = spectrum ℂ (a : A)
  ext z
  -- Apply invertibility permanence to z * 1 - a, for every complex z.
  exact not_iff_not.mpr (invertibility_permanence A B hB
    (algebraMap ℂ B z - a)).symm

end ExpandedFA.CStar.SpectralPermanence
