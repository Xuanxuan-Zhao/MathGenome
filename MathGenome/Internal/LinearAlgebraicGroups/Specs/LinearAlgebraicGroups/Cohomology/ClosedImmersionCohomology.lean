import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
noncomputable section

namespace LinearAlgebraicGroups.Specs.ClosedImmersionCohomology

open OrderedCechComparison

/-- The lift goes from the direct image of the source resolution into a
resolution of the direct image. -/
def LiftsIdentity {X Z : Scheme.{u}} {j : Z ⟶ X} {G : Z.Modules}
    (J : InjectiveResolution G) (I : InjectiveResolution ((Scheme.Modules.pushforward j).obj G))
    (l : ((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℕ)).obj
    J.cocomplex ⟶ I.cocomplex) : Prop :=
  (Scheme.Modules.pushforward j).map (J.ι.f 0) ≫ l.f 0 = I.ι.f 0

variable {A B : Type u} [CommRing A] [CommRing B]
  {X : SchemeOverRing A} {Z : SchemeOverRing B}
  (φ : A →+* B) (j : Z.left ⟶ X.left)
  (hj : j ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom φ))

/-- The section complex of a direct image, identified by the same maps
as the identification of actual sections in each degree. -/
def pushforwardSectionsComplexIso (K : CochainComplex Z.left.Modules ℕ) :
    ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (.up ℕ)).obj
      (((sectionsFunctor Z).mapHomologicalComplex (.up ℕ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (pushforwardSectionsIso φ j hj).app (K.X n))
    (fun p q _ => (pushforwardSectionsIso φ j hj).hom.naturality (K.d p q))

variable {j} {G : Z.left.Modules}
  (J : InjectiveResolution G) (I : InjectiveResolution ((Scheme.Modules.pushforward j).obj G))

/-- The map from the cohomology of the closed subscheme, with restricted
scalars, to the cohomology of its direct image, computed using a lift. -/
def inverseComparisonOfLift (l : ((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℕ)).obj
    J.cocomplex ⟶ I.cocomplex) (n : ℕ) :
    (ModuleCat.restrictScalars.{u} φ).obj ((cohomology Z n).obj G) ⟶
      (cohomology X n).obj ((Scheme.Modules.pushforward j).obj G) :=
  let ΓX := (sectionsFunctor X).mapHomologicalComplex (.up ℕ)
  let ΓZ := (sectionsFunctor Z).mapHomologicalComplex (.up ℕ)
  (ModuleCat.restrictScalars φ).map (J.isoRightDerivedObj (sectionsFunctor Z) n).hom ≫
    (restrictCohomologyIso φ (ΓZ.obj J.cocomplex) n).hom ≫
    homologyMap ((pushforwardSectionsComplexIso φ j hj J.cocomplex).inv ≫ ΓX.map l) n ≫
    (I.isoRightDerivedObj (sectionsFunctor X) n).inv

/-- Exactness of the direct image in the category of all sheaves of modules.
Finite limits are already preserved by the direct image adjunction. -/
def PushforwardExact : Prop :=
  ∀ {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j],
    PreservesFiniteColimits (Scheme.Modules.pushforward j)

/-- The canonical comparison in all degrees. The statement holds for all
coefficient sheaves and hence for quasi-coherent coefficients on the
quasi-compact separated schemes in the arithmetic application. -/
def Comparison : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Z : SchemeOverRing B}
    (φ : A →+* B) (j : Z.left ⟶ X.left) [IsClosedImmersion j]
    (hj : j ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom φ)) (n : ℕ),
    ∃ c : Scheme.Modules.pushforward j ⋙ cohomology X n ≅
        cohomology Z n ⋙ ModuleCat.restrictScalars.{u} φ,
      ∀ (G : Z.left.Modules) (J : InjectiveResolution G)
        (I : InjectiveResolution ((Scheme.Modules.pushforward j).obj G)),
        (∃ l, LiftsIdentity J I l) ∧
        ∀ l, LiftsIdentity J I l →
          QuasiIso (((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).map l) ∧
            inverseComparisonOfLift φ hj J I l n = c.inv.app G

end LinearAlgebraicGroups.Specs.ClosedImmersionCohomology
