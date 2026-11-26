import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra HopfAlgebra WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct MonoidAlgebra

universe u

namespace LinearAlgebraicGroups.Specs.DiagonalizableGroups

noncomputable section

variable (k : Type u) [Field k]

/-- Finitely generated abelian groups, written multiplicatively. -/
abbrev FGAbelianGroup := (show ObjectProperty CommGrpCat.{u} from fun M => Group.FG M).FullSubcategory

abbrev groupAlgebra (M : Type u) [CommGroup M] : HopfAlgebraCategory k :=
  CommHopfAlgCat.of k (MonoidAlgebra k M)

abbrev groupAlgebraMap {M N : Type u} [CommGroup M] [CommGroup N] (f : M →* N) :
    groupAlgebra k M ⟶ groupAlgebra k N :=
  CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k f)

/-- The coordinate Hopf algebra of `D(M)` is the group algebra with its standard Hopf structure. -/
abbrev diagonalGroup (M : Type u) [CommGroup M] [Group.FG M] : AffineAlgebraicGroup k :=
  StandardGroups.spectrum k (MonoidAlgebra k M)

abbrev DiagonalGroupType :=
  ∀ (k : Type u) [Field k] (M : Type u) [CommGroup M] [Group.FG M], AffineAlgebraicGroup k

def groupAlgebraFunctor : FGAbelianGroup.{u} ⥤ FiniteTypeHopfAlgebraCategory k where
  obj M :=
    letI : Group.FG M.obj := M.property
    ⟨groupAlgebra k M.obj, inferInstanceAs (Algebra.FiniteType k (MonoidAlgebra k M.obj))⟩
  map f := InducedCategory.homMk (groupAlgebraMap k f.hom.hom)
  map_id _ := by
    apply InducedCategory.hom_ext
    apply CommHopfAlgCat.hom_ext
    exact MonoidAlgebra.mapDomainBialgHom_id
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply CommHopfAlgCat.hom_ext
    exact (MonoidAlgebra.mapDomainBialgHom_comp (R := k) g.hom.hom f.hom.hom)

def diagonalFunctor : FGAbelianGroup.{u}ᵒᵖ ⥤ AffineAlgebraicGroupCategory k :=
  (groupAlgebraFunctor k).op ⋙ finiteTypeHopfSpec k

abbrev DiagonalFunctorType :=
  ∀ (k : Type u) [Field k], FGAbelianGroup.{u}ᵒᵖ ⥤ AffineAlgebraicGroupCategory k

/-- Diagonalizable groups are the groups isomorphic to a split group-algebra spectrum. -/
abbrev DiagonalizableGroup := (diagonalFunctor k).EssImageSubcategory

def GroupAlgebraBasisAndHopfStructure : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M],
    ∃ b : Module.Basis M k (MonoidAlgebra k M),
      (∀ m, b m = MonoidAlgebra.single m 1) ∧
      ∀ m, comul (R := k) (b m) = b m ⊗ₜ[k] b m ∧
        counit (R := k) (b m) = 1 ∧
        antipode k (b m) = b m⁻¹

/-- The point groups and their action on maps of test algebras. -/
def characterValuedPoints (M : Type u) [CommGroup M] : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (M →* Rˣ)
  map a := GrpCat.ofHom
    { toFun := fun f => (Units.map a.hom.toMonoidHom).comp f
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp }
  map_id _ := by apply GrpCat.ext; intro f; ext x; rfl
  map_comp _ _ := by apply GrpCat.ext; intro f; ext x; rfl

def DiagonalPoints : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] [Group.FG M],
    StandardGroups.Represents (MonoidAlgebra k M) (characterValuedPoints k M)
      (fun R f g => ∀ m, ((show M →* Rˣ from g) m).val = f (MonoidAlgebra.single m 1))

def DiagonalAntiequivalence : Prop :=
  ∀ (k : Type u) [Field k], (diagonalFunctor k).toEssImage.IsEquivalence

/-- The group homomorphism on exponents obtained by applying a Hopf map to the basis. -/
def imageCharacters {M : Type u} [CommGroup M] {A : HopfAlgebraCategory k}
    (a : groupAlgebra k M ⟶ A) : M →* GroupLike k A where
  toFun m := ⟨a.hom (MonoidAlgebra.of k M m),
    (MonoidAlgebra.isGroupLikeElem_of m).map a.hom⟩
  map_one' := GroupLike.val_injective (by
    change a.hom (MonoidAlgebra.of k M 1) = 1
    rw [map_one, map_one])
  map_mul' m n := GroupLike.val_injective (by
    change a.hom (MonoidAlgebra.of k M (m * n)) =
      a.hom (MonoidAlgebra.of k M m) * a.hom (MonoidAlgebra.of k M n)
    rw [map_mul, map_mul])

def HopfQuotientClassification : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] {A : HopfAlgebraCategory k}
    (a : groupAlgebra k M ⟶ A),
    Function.Surjective a.hom ↔
      ∃! N : Subgroup M, ∃ e : MonoidAlgebra k (M ⧸ N) ≃ₐc[k] A,
        e.toBialgHom.comp (MonoidAlgebra.mapDomainBialgHom k (QuotientGroup.mk' N)) = a.hom

def HopfSubalgebraClassification : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] {A : HopfAlgebraCategory k}
    (a : A ⟶ groupAlgebra k M),
    Function.Injective a.hom ↔
      ∃! N : Subgroup M, ∃ e : MonoidAlgebra k N ≃ₐc[k] A,
        a.hom.comp e.toBialgHom = MonoidAlgebra.mapDomainBialgHom k N.subtype

/-- The subgroup cut out by the quotient of the character group. -/
def diagonalClosedInclusion {M : Type u} [CommGroup M] (N : Subgroup M) :=
  specGroupMap (groupAlgebraMap k (QuotientGroup.mk' N))

/-- Restriction of characters to a subgroup of the character group. -/
def diagonalRestriction {M : Type u} [CommGroup M] (N : Subgroup M) :=
  specGroupMap (groupAlgebraMap k N.subtype)

def DiagonalClosedSubgroups : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] [Group.FG M]
    (H : GroupScheme k) (i : H ⟶ (diagonalGroup k M).val),
    IsClosedImmersion i.hom.hom.left ↔
      ∃! N : Subgroup M,
        ∃ e : H ≅ specGroup (groupAlgebra k (M ⧸ N)),
          e.hom ≫ diagonalClosedInclusion k N = i

def DiagonalFaithfullyFlatQuotients : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] [Group.FG M]
    (H : AffineGroupCategory k) (p : (diagonalGroup k M).val ⟶ H.val),
    (Flat p.hom.hom.left ∧ Surjective p.hom.hom.left) ↔
      ∃! N : Subgroup M,
        ∃ e : specGroup (groupAlgebra k N) ≅ H.val,
          diagonalRestriction k N ≫ e.hom = p

def DiagonalRestrictionKernelAndQuotient : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] [Group.FG M] (N : Subgroup M),
    ∃ h : IsClosedImmersion (diagonalClosedInclusion k N).hom.hom.left,
      let K : ClosedSubgroup (diagonalGroup k M).val :=
        ⟨specGroup (groupAlgebra k (M ⧸ N)), diagonalClosedInclusion k N, h⟩
      Flat (diagonalRestriction k N).hom.hom.left ∧
      Surjective (diagonalRestriction k N).hom.hom.left ∧
      LocallyOfFinitePresentation (diagonalRestriction k N).hom.hom.left ∧
      IsSchemeKernel (diagonalRestriction k N) K ∧
      ∃ e : rightQuotientSheaf K ≅ schemeFppfSheaf (specGroup (groupAlgebra k N)).X,
        rightQuotientProjection K ≫ e.hom =
          (fppfOver k).uliftYoneda.map (diagonalRestriction k N).hom.hom

abbrev IntegerCharacters := ULift.{u} (Multiplicative ℤ)

abbrev integerGenerator : IntegerCharacters.{u} := ⟨Multiplicative.ofAdd 1⟩

/-- The point functor of the group scheme `μₙ`, including in characteristic dividing `n`. -/
def rootsOfUnityPoints (n : ℕ) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (rootsOfUnity n R)
  map a := GrpCat.ofHom (restrictRootsOfUnity a.hom n)
  map_id _ := by apply GrpCat.ext; intro x; ext; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext; rfl

def DiagonalIntegerPowers : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι],
    Nonempty ((diagonalGroup k (Multiplicative (ι → ℤ))).val ≅
      (StandardGroups.multiplicativePowerGroup k ι).val)

def DiagonalCyclic : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) [NeZero n],
    ∃ e : (groupPointsFunctor k).obj
        (diagonalGroup k (ULift.{u} (Multiplicative (ZMod n)))).val ≅ rootsOfUnityPoints k n,
      ∀ (R : TestAlgebra k)
        (f : MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod n))) →ₐ[k] R)
        (x : ((groupPointsFunctor k).obj
          (diagonalGroup k (ULift.{u} (Multiplicative (ZMod n)))).val).obj R),
        (show Points (diagonalGroup k (ULift.{u} (Multiplicative (ZMod n)))).val.X R from x).left =
          Spec.map (CommRingCat.ofHom f.toRingHom) →
        ((show rootsOfUnity n R from e.hom.app R x).val : R) =
          f (MonoidAlgebra.single ⟨Multiplicative.ofAdd 1⟩ 1)

/-- The factors of a split diagonalizable group on all test algebras. -/
def splitProductPoints (ι κ : Type) (n : κ → ℕ) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of ((ι → Rˣ) × (∀ j, rootsOfUnity (n j) R))
  map a := GrpCat.ofHom <|
    ((MonoidHom.pi fun i : ι => (Units.map a.hom.toMonoidHom).comp
      (Pi.evalMonoidHom _ i)).comp (MonoidHom.fst _ _)).prod
    ((MonoidHom.pi fun j : κ => (restrictRootsOfUnity a.hom (n j)).comp
      (Pi.evalMonoidHom _ j)).comp (MonoidHom.snd _ _))
  map_id _ := by apply GrpCat.ext; intro x; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; rfl

def DiagonalCyclicDecomposition : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] [Group.FG M],
    ∃ (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ) (n : κ → ℕ),
      (∀ j, 0 < n j) ∧
        Nonempty ((groupPointsFunctor k).obj (diagonalGroup k M).val ≅ splitProductPoints k ι κ n)

/-- The inverse on characters is evaluation at the exponent, compatible with precomposition. -/
def CharacterRecovery : Prop :=
  ∀ (k : Type u) [Field k] (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ StandardGroups.multiplicativePoints k),
    ∃ (P : ∀ (M : Type u) [CommGroup M] [Group.FG M],
          (groupPointsFunctor k).obj (diagonalGroup k M).val ≅ characterValuedPoints k M)
      (χ : ∀ (M : Type u) [CommGroup M] [Group.FG M],
          M ≃ ((diagonalGroup k M).val ⟶ T.val)),
      (∀ (M : Type u) [CommGroup M] [Group.FG M] (R : TestAlgebra k)
        (f : MonoidAlgebra k M →ₐ[k] R)
        (x : ((groupPointsFunctor k).obj (diagonalGroup k M).val).obj R),
        (show Points (diagonalGroup k M).val.X R from x).left =
          Spec.map (CommRingCat.ofHom f.toRingHom) →
        ∀ m, ((show M →* Rˣ from (P M).hom.app R x) m).val =
          f (MonoidAlgebra.single m 1)) ∧
      (∀ (M : Type u) [CommGroup M] [Group.FG M] (m : M) (R : TestAlgebra k)
        (x : ((groupPointsFunctor k).obj (diagonalGroup k M).val).obj R),
        t.hom.app R (((groupPointsFunctor k).map (χ M m)).app R x) =
          (show M →* Rˣ from (P M).hom.app R x) m) ∧
      (∀ (M N : Type u) [CommGroup M] [CommGroup N] [Group.FG M] [Group.FG N]
        (f : M →* N) (m : M),
        specGroupMap (groupAlgebraMap k f) ≫ χ M m = χ N (f m))

/-- Each group-like element of the split group algebra is exactly one basis element. -/
def GroupLikeElements : Prop :=
  ∀ (k M : Type u) [Field k] [CommGroup M] (a : MonoidAlgebra k M),
    IsGroupLikeElem k a ↔ ∃! m : M, MonoidAlgebra.single m 1 = a

/-- The group-algebra description is equivalent to being spanned by characters. -/
def GroupLikeSpanning : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) [Algebra.FiniteType k A],
    Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤ ↔
      ∃ (M : Type u) (_ : CommGroup M) (_ : Group.FG M),
        Nonempty (MonoidAlgebra k M ≃ₐc[k] A)

/-- The inverse functor gives the character group on every diagonalizable group. -/
def CharactersAreInverse : Prop :=
  ∀ (k : Type u) [Field k] (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ StandardGroups.multiplicativePoints k),
    ∃ E : FGAbelianGroup.{u}ᵒᵖ ≌ DiagonalizableGroup k,
      E.functor = (diagonalFunctor k).toEssImage ∧
      ∃ χ : ∀ G : DiagonalizableGroup k, (E.inverse.obj G).unop.obj ≃ (G.obj.val ⟶ T.val),
        (∀ (G H : DiagonalizableGroup k) (f : G ⟶ H) (m : (E.inverse.obj H).unop.obj),
          χ G ((E.inverse.map f).unop.hom.hom m) = f.hom.hom ≫ χ H m) ∧
        (∀ (G : DiagonalizableGroup k) (m n : (E.inverse.obj G).unop.obj)
          (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj G.obj.val).obj R),
          let eval (c : G.obj.val ⟶ T.val) :=
            t.hom.app R (((groupPointsFunctor k).map c).app R x)
          eval (χ G (m * n)) = eval (χ G m) * eval (χ G n))

def DiagonalInteger : Prop :=
  ∀ (k : Type u) [Field k] (T : AffineAlgebraicGroup k),
    Nonempty ((groupPointsFunctor k).obj T.val ≅ StandardGroups.multiplicativePoints k) →
    Nonempty (specGroup (groupAlgebra k IntegerCharacters) ≅ T.val)

end

end LinearAlgebraicGroups.Specs.DiagonalizableGroups
