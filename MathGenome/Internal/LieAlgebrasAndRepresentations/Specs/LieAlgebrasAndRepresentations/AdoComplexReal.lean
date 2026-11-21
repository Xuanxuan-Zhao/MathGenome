import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
LA-I11, Theorem 9.11 of the Lie volume. A faithful representation is
an injective Lie homomorphism to the endomorphisms of a finite-dimensional
vector space over the indicated field. The endomorphism bracket is the commutator.
-/

namespace Specs.LieAlgebrasAndRepresentations.AdoComplexReal

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Ado's theorem over the complex field. -/
def complexAdoType : Prop :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G],
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V),
      FiniteDimensional ℂ V ∧
        ∃ ρ : G →ₗ⁅ℂ⁆ Module.End ℂ V, Function.Injective ρ

/-- Ado's theorem over the real field. -/
def realAdoType : Prop :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G],
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V),
      FiniteDimensional ℝ V ∧
        ∃ ρ : G →ₗ⁅ℝ⁆ Module.End ℝ V, Function.Injective ρ

end Specs.LieAlgebrasAndRepresentations.AdoComplexReal
