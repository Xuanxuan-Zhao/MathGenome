import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergData
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
HA-G01, notes/002/advanced-homological-algebra.tex:2391–2451.
The conclusion uses all fields of the shared `ResolutionData`, including the
four induced augmented resolutions. The specified horizontal bound is retained.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace AdvancedHomologicalAlgebra.CartanEilenbergExistence.Specs

open CartanEilenbergData

/-- Existence with any prescribed lower bound for the source complex. -/
def ExistenceAtBound : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (K : CochainComplex C ℤ) (L : ℤ),
    (∀ p : ℤ, p < L → IsZero (K.X p)) →
    ∃ R : ResolutionData K,
      ∀ p q : ℤ, p < L → IsZero ((R.bicomplex.X p).X q)

/-- The bounded-below existence assertion, without selecting a bound in advance. -/
def Existence : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (K : CochainComplex C ℤ),
    (∃ L : ℤ, ∀ p : ℤ, p < L → IsZero (K.X p)) →
    Nonempty (ResolutionData K)

end AdvancedHomologicalAlgebra.CartanEilenbergExistence.Specs
