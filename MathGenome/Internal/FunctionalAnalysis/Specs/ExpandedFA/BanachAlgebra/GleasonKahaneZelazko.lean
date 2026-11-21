import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions

/-! Independent statement of paper.tex, 10228–10232, under the unital Banach
algebra convention at 9907–9914. In particular neither continuity nor
multiplicativity is part of the hypotheses on the scalar-linear functional. -/

namespace Specs.ExpandedFA.BanachAlgebra.GleasonKahaneZelazko

universe u

/-- GKZ includes arbitrary, possibly noncommutative, complex unital Banach algebras. -/
def GleasonKahaneZelazko : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A],
    Conventions.IsUnitalBanachAlgebraValue A →
    ∀ (φ : A →ₗ[ℂ] ℂ), φ 1 = 1 →
      (∀ a : A, IsUnit a → φ a ≠ 0) →
      Continuous φ ∧ φ ∈ Conventions.CharacterSpaceValue ℂ A

end Specs.ExpandedFA.BanachAlgebra.GleasonKahaneZelazko
