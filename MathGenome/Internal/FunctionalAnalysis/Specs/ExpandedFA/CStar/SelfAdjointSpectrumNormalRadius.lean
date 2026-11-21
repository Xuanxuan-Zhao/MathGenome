import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions

/-! The fundamental spectral stage in the proof of
`fa2:p2:commutative-cstar` (paper.tex:12209–12214).
These statements use the original norm and involution. Spectral radii are
real suprema, with the nonunital spectrum taken in the actual C*-unitization.
No nonzero, representation, positivity, or order hypothesis is imposed. -/

noncomputable section
namespace ExpandedFA.CStar.SelfAdjointSpectrumNormalRadius.Spec

open ExpandedFA.CStar.Conventions.Spec
open Specs.ExpandedFA.BanachAlgebra.Conventions
universe u

def UnitalSelfAdjointSpectrum : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (a : A), IsSelfAdjoint a →
    ∀ z ∈ UnitalSpectrumValue A a, z.im = 0

def UnitalNormalRadius : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (a : A), IsStarNormal a →
    AlgebraSpectralRadiusValue ℂ A a = ‖a‖

def NonunitalSelfAdjointSpectrum : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a : A), IsSelfAdjoint a →
    ∀ z ∈ ExpandedFA.CStar.Conventions.Spec.NonunitalSpectrumValue A a, z.im = 0

def NonunitalNormalRadius : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a : A), IsStarNormal a →
    sSup ((fun z : ℂ => ‖z‖) ''
      ExpandedFA.CStar.Conventions.Spec.NonunitalSpectrumValue A a) = ‖a‖

/-- The same radius in the earlier Banach-algebra convention, whose spectrum
is algebraically identical even though the unitization norm is different. -/
def BanachNonunitalNormalRadius : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a : A), IsStarNormal a →
    NonunitalSpectralRadiusValue A a = ‖a‖

end ExpandedFA.CStar.SelfAdjointSpectrumNormalRadius.Spec
