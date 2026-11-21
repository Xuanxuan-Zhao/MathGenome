import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergData
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness

/-! HA-G08, notes/002/advanced-homological-algebra.tex, 2454–2498.
The rows and their vertical maps are those of an arbitrary resolution in HA-G00.
Admissibility is precisely the two monomorphism tests of HA-G07.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace AdvancedHomologicalAlgebra.SplitRowExtension

open CartanEilenbergData

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Degreewise injection, also injective on the quotients by boundaries. -/
def Admissible {U V : CochainComplex C ℤ} (i : U ⟶ V) : Prop :=
  (∀ p, Mono (i.f p)) ∧ (∀ p, Mono (opcyclesMap i p))

/-- Extension in the category of complexes, with equality of chain maps. -/
def HasExtensionProperty (L : CochainComplex C ℤ) : Prop :=
  ∀ {U V : CochainComplex C ℤ} (i : U ⟶ V), Admissible i →
    ∀ f : U ⟶ L, ∃ g : V ⟶ L, i ≫ g = f

namespace Specs

def RowExtension : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K) (q : ℤ), 0 ≤ q →
    HasExtensionProperty (R.bicomplex.flip.X q)

/-- The kernel is taken in the category of horizontal cochain complexes. -/
def VerticalKernelAdmissible : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K) (q : ℤ), 0 ≤ q →
    Admissible (kernel.ι (R.bicomplex.flip.d q (q + 1)))

/-- At vertical degree zero the previous row is the augmented source K. -/
def AugmentationAdmissible : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K), Admissible R.augmentation

end Specs
end AdvancedHomologicalAlgebra.SplitRowExtension
