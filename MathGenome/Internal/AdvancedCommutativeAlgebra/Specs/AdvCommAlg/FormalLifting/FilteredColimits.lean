import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Filtered.Basic

/-! FL-16, paper.tex:857–870. A colimit is expressed by an arbitrary cocone
and its universal property, so the statements apply to every choice of algebra
colimit. No finite generation or nonzero-ring hypotheses are imposed.
The algebra universe contains the base universe; the diagram and its morphisms
have independent universes. -/
namespace Specs.AdvCommAlg.FormalLifting

open CategoryTheory Limits
universe u v w t

/-- Filtered colimits preserve the existence and uniqueness of square-zero lifts. -/
def filteredColimitFormallyEtale : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Type w) [Category.{t} J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{max u v} A) (c : Cocone F),
    IsColimit c → (∀ j, formallyEtaleValue A (F.obj j)) →
      formallyEtaleValue A c.pt

/-- Filtered colimits preserve uniqueness of square-zero lifts. -/
def filteredColimitFormallyUnramified : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Type w) [Category.{t} J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{max u v} A) (c : Cocone F),
    IsColimit c → (∀ j, formallyUnramifiedValue A (F.obj j)) →
      formallyUnramifiedValue A c.pt

end Specs.AdvCommAlg.FormalLifting
