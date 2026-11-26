import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.CategoryTheory.Abelian.RightDerived

/-! The ideal torsion submodule, its inclusion, and the local cohomology functors
of Chapter 1 (Definition 1.1 and the opening of Theorem 1.2). -/

open CategoryTheory
open scoped ZeroObject

namespace Specs.CommutativeAlgebraNotes.IdealTorsion

universe v u

-- The closed signatures below live in the maximum of the ring and module universes.
set_option linter.checkUnivs false

def idealTorsionType :=
  ∀ {R : Type u} [CommRing R], Ideal R →
    ∀ (M : Type v) [AddCommGroup M] [Module R M], Submodule R M

/-- The submodule of elements killed by a power of the ideal. -/
abbrev idealTorsion {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] : Submodule R M :=
  I.primaryComponent M

def memIdealTorsionType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) {M : Type v} [AddCommGroup M] [Module R M]
    (x : M), x ∈ idealTorsion I M ↔ ∃ n : ℕ, 1 ≤ n ∧ ∀ a ∈ I ^ n, a • x = 0

def idealTorsionUnionType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M],
    (Monotone fun n : ℕ => Submodule.torsionBySet R M (↑(I ^ (n + 1)) : Set R)) ∧
      idealTorsion I M = ⨆ n : ℕ, Submodule.torsionBySet R M (↑(I ^ (n + 1)) : Set R)

def idealTorsionFunctorType :=
  ∀ {R : Type u} [CommRing R], Ideal R → (ModuleCat.{v} R ⥤ ModuleCat.{v} R)

/-- Sections supported in an ideal, with morphisms given by restriction. -/
def idealTorsionFunctor {R : Type u} [CommRing R] (I : Ideal R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (idealTorsion I M)
  map f := ModuleCat.ofHom (Ideal.primaryComponent.map I f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

instance (R : Type u) [CommRing R] (I : Ideal R) : (idealTorsionFunctor.{v} I).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    ext x
    rfl

def idealTorsionAdditiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R), (idealTorsionFunctor.{v} I).Additive

def idealTorsionInclusionType :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R), idealTorsionFunctor.{v} I ⟶ 𝟭 (ModuleCat.{v} R)

/-- The natural submodule inclusion into the identity functor. -/
def idealTorsionInclusion {R : Type u} [CommRing R] (I : Ideal R) :
    idealTorsionFunctor.{v} I ⟶ 𝟭 (ModuleCat.{v} R) where
  app M := ModuleCat.ofHom (idealTorsion I M).subtype
  naturality M N f := by
    apply ModuleCat.hom_ext
    rfl

def localCohomologyType :=
  ∀ {R : Type u} [CommRing R] (_ : Ideal R) [Small.{v} R],
    ℤ → (ModuleCat.{v} R ⥤ ModuleCat.{v} R)

/-- Integer-graded local cohomology, defined by right derivation in nonnegative
degrees and by the zero functor in negative degrees. The ring is small in the
module universe so that `ModuleCat` has injective resolutions. -/
noncomputable def localCohomology {R : Type u} [CommRing R] (I : Ideal R) [Small.{v} R]
    (q : ℤ) : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  match q with
  | .ofNat n => (idealTorsionFunctor I).rightDerived n
  | .negSucc _ => 0

def localCohomologyNonnegType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) [Small.{v} R] (q : ℤ), 0 ≤ q →
    localCohomology.{v} I q = (idealTorsionFunctor I).rightDerived q.toNat

def localCohomologyNegType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) [Small.{v} R] (q : ℤ), q < 0 →
    localCohomology.{v} I q = 0

end Specs.CommutativeAlgebraNotes.IdealTorsion
