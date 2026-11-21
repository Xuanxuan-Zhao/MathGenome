import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions

/-!
Independent specification for the nonempty compact spectrum assertion of
`fa2:p2:spectrum-radius`, paper.tex:10041–10060.

The algebra is the chapter's nonzero complex unital Banach algebra, with
submultiplicative norm and ‖1‖ = 1. The spectrum is the accepted algebraic
set of scalars z for which z1-a is not invertible; no commutativity,
finite-dimensionality, or operator representation is assumed.
-/

namespace Specs.ExpandedFA.BanachAlgebra.NonemptySpectrum

open Conventions

universe u

/-- Every element has a nonempty compact spectrum in the closed norm disk. -/
def SpectrumProperties : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A,
      (AlgebraSpectrumValue ℂ A a).Nonempty ∧
      IsCompact (AlgebraSpectrumValue ℂ A a) ∧
      AlgebraSpectrumValue ℂ A a ⊆ {z : ℂ | ‖z‖ ≤ ‖a‖}

end Specs.ExpandedFA.BanachAlgebra.NonemptySpectrum
