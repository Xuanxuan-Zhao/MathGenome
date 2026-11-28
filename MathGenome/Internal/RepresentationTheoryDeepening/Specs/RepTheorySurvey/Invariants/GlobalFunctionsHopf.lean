import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits hiding prodComparison
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace RepTheorySurvey.Invariants.GlobalFunctions

open LinearAlgebraicGroups (SchemeOver TestAlgebra Points testSpec HopfAlgebraCategory
  AffineGroupCategory coordinateHopf coordinateHopfSpecIso affineGroupInclusion)
open LinearAlgebraicGroups.Specs (GroupScheme)

noncomputable section

variable {k : Type u} [Field k]

abbrev sectionsFunctor (k : Type u) [Field k] := algΓ (CommRingCat.of k)

abbrev Sections (X : SchemeOver k) : CommAlgCat.{u} k :=
  ((sectionsFunctor k).obj X).unop

def pull {X Y : SchemeOver k} (f : X ⟶ Y) : Sections Y →ₐ[k] Sections X :=
  ((sectionsFunctor k).map f).unop.hom

def tensorComparison (X Y : SchemeOver k) :
    Sections X ⊗[k] Sections Y →ₐ[k] Sections (X ⊗ Y) :=
  (prodComparison (sectionsFunctor k) X Y).unop.hom

def affinization (X : SchemeOver k) : SchemeOver k :=
  (testSpec k).obj (op (Sections X))

def unit (X : SchemeOver k) : X ⟶ affinization X :=
  (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app X

def testSectionsIso (R : TestAlgebra k) : Sections ((testSpec k).obj (op R)) ≅ R := by
  letI := algSpec.instFull (R := CommRingCat.of k)
  letI := algSpec.instFaithful (R := CommRingCat.of k)
  exact ((asIso ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op R))).unop).symm

def evaluate {X : SchemeOver k} {R : TestAlgebra k} (p : Points X R) :
    Sections X →ₐ[k] R :=
  (testSectionsIso R).hom.hom.comp (pull p)

namespace Specs

def ProductFormula : Prop :=
  ∀ {k : Type u} [Field k] (X Y : SchemeOver k) (f : Sections X) (g : Sections Y),
    tensorComparison X Y (f ⊗ₜ[k] g) = pull (fst X Y) f * pull (snd X Y) g

def ProductNaturality : Prop :=
  ∀ {k : Type u} [Field k] {X X' Y Y' : SchemeOver k} (f : X ⟶ X') (g : Y ⟶ Y'),
    (pull (f ⊗ₘ g)).comp (tensorComparison X' Y') =
      (tensorComparison X Y).comp (Algebra.TensorProduct.map (pull f) (pull g))

def ProductIsomorphism : Prop :=
  ∀ {k : Type u} [Field k] (X Y : SchemeOver k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left],
    Function.Bijective (tensorComparison X Y)

def FiniteTypeTopology : Prop :=
  ∀ {k : Type u} [Field k] (X : SchemeOver k) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    CompactSpace X.left ∧ QuasiSeparatedSpace X.left

def AffinizationUniversal : Prop :=
  ∀ {k : Type u} [Field k] (X L : SchemeOver k) [IsAffine L.left] (f : X ⟶ L),
    ∃! g : affinization X ⟶ L, unit X ≫ g = f

def ProductAffinizationUniversal : Prop :=
  ∀ {k : Type u} [Field k] (X Y L : SchemeOver k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] [IsAffine L.left] (f : X ⊗ Y ⟶ L),
    ∃! g : affinization X ⊗ affinization Y ⟶ L, (unit X ⊗ₘ unit Y) ≫ g = f

def EvaluationFormula : Prop :=
  ∀ {k : Type u} [Field k] {X : SchemeOver k} {R : TestAlgebra k} (p : Points X R),
    p ≫ unit X =
      (testSpec k).map (CommAlgCat.ofHom (evaluate p)).op

/-- The Hopf operations on actual global sections, expressed as a cogroup in algebras. -/
structure GlobalHopf {k : Type u} [Field k] (G : GroupScheme k) where
  group : GrpObj (op (Sections G.X))
  comultiplication :
    (tensorComparison G.X G.X).comp
        (MonObj.mul (X := op (Sections G.X)) (self := group.toMonObj)).unop.hom =
      pull (MonObj.mul (X := G.X))
  counit :
    (MonObj.one (X := op (Sections G.X)) (self := group.toMonObj)).unop.hom =
      evaluate (toUnit ((testSpec k).obj (op (CommAlgCat.of k k))) ≫ MonObj.one (X := G.X))
  antipode :
    (GrpObj.inv (X := op (Sections G.X)) (self := group)).unop.hom =
      pull (GrpObj.inv (X := G.X))

namespace GlobalHopf

variable {G : GroupScheme k}

/-- Corresponding commutative Hopf algebra in the pinned category. -/
def hopf (H : GlobalHopf G) : HopfAlgebraCategory k :=
  (commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of k)).inverse.obj
    (op { X := op (Sections G.X), grp := H.group })

def spectrum (H : GlobalHopf G) : GroupScheme k :=
  (hopfSpec (CommRingCat.of k)).obj (op H.hopf)

end GlobalHopf

def HopfOperationFormulas : Prop :=
  ∀ {k : Type u} [Field k] (G : GroupScheme k) (H : GlobalHopf G),
    (tensorComparison G.X G.X).comp (Bialgebra.comulAlgHom k H.hopf) =
      pull (MonObj.mul (X := G.X)) ∧
    Bialgebra.counitAlgHom k H.hopf =
      evaluate (toUnit ((testSpec k).obj (op (CommAlgCat.of k k))) ≫ MonObj.one (X := G.X)) ∧
    HopfAlgebra.antipodeAlgHom k H.hopf = pull (GrpObj.inv (X := G.X))

def GlobalHopfExists : Prop :=
  ∀ {k : Type u} [Field k] (G : GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom],
    ∃ (H : GlobalHopf G) (a : G ⟶ H.spectrum),
      a.hom.hom = unit G.X ∧
      ∀ (L : GroupScheme k) [IsAffine L.X.left] (f : G ⟶ L),
        ∃! g : H.spectrum ⟶ L, a ≫ g = f

def AffineCompatibility : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineGroupCategory k) (H : GlobalHopf G.val)
    (a : G.val ⟶ H.spectrum), a.hom.hom = unit G.val.X →
    ∃ e : H.hopf ≅ coordinateHopf G,
      ∀ (R : TestAlgebra k) (p : Points G.val.X R),
        (evaluate p).comp e.inv.hom.toAlgHom =
          (evaluate (p ≫ ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso G)).inv.hom.hom)).comp
            (testSectionsIso (CommAlgCat.of k (coordinateHopf G))).inv.hom

end Specs
end
end RepTheorySurvey.Invariants.GlobalFunctions
