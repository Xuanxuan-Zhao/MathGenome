import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Localization.Away.Basic

/-! ET-15, paper.tex:1941–1944 and 1955–1961.
The diagram is indexed by an arbitrary small filtered category. Its maps need
not be injective. All rings, including the zero ring, are allowed.
The universe of the diagram and its rings is arbitrary; the algebra being
descended may lie in a separate universe. -/
namespace Specs.AdvCommAlg.Etale

open CategoryTheory Limits
open scoped TensorProduct

universe u v

/-- Descent from a filtered colimit of commutative rings. The algebra structure
on the colimit used in the tensor product is the specified cocone map. -/
def filteredColimitDescent : Prop :=
  ∀ (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F), IsColimit c →
    ∀ (B : Type v) [CommRing B] [Algebra c.pt B], Algebra.Etale c.pt B →
    ∃ (i : J) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i) Bᵢ),
      letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      Algebra.Etale (F.obj i) Bᵢ ∧ Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj i] Bᵢ)

/-- Descent from an arbitrary localization to one principal localization.
The structural map from the principal localization is the canonical lift of
`R → A`; no injectivity or nonzero denominator assumption is made. -/
def principalLocalizationDescent : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    (B : Type v) [CommRing B] [Algebra A B], Algebra.Etale A B →
    ∃ (s : S) (Bₛ : Type u) (_ : CommRing Bₛ) (_ : Algebra (Localization.Away (s : R)) Bₛ),
      letI : Algebra (Localization.Away (s : R)) A :=
        (IsLocalization.Away.lift (s : R) (IsLocalization.map_units A s)).toAlgebra
      Algebra.Etale (Localization.Away (s : R)) Bₛ ∧
        Nonempty (B ≃ₐ[A] A ⊗[Localization.Away (s : R)] Bₛ)

end Specs.AdvCommAlg.Etale
