import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.MoritaCriterion

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization

namespace Specs.DerivedFormalization.DG.EndomorphismGenerator

open AmbientDerived (category strictInput)
open BalancedTensor (bimodule)
open CompactFiniteCells (CompactAt)
open CompactRepresentables (LocalizationMapAdditive)
open Derived (HomotopyCategoryLaws)
open DerivedBimoduleAdjunction (AmbientSignedModels DerivedAdjunctionData SignedModels)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (component dgModuleCategory gradedHom homComplex)
open KProjective (isKProjective)
open MoritaUnit (toComplexHom)

universe u v w z

noncomputable section

variable {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k}

/-- The unital dg algebra of homogeneous right-linear endomorphisms of `P`,
with the commutator differential and composition of the dg module category. -/
def endomorphismAlgebra (P : RightDGModuleModel B) : DGAlgebraModel.{u,max v z} k :=
  Basic.endAlgebra (dgModuleCategory B) P

/-- The one-object presentation uses a singleton in the chosen object universe. -/
@[reducible] def endomorphismCategory (P : RightDGModuleModel B) :
    DGCategoryModel.{u,max v z,w} k :=
  ⟨PUnit.{w+1}, (endomorphismAlgebra P).reindex (fun _ => ())⟩

/-- The bimodule with value `P` and left action by the endomorphisms themselves. -/
def endomorphismAction (P : RightDGModuleModel B) :
    bimodule (endomorphismCategory.{u,v,w,z} P) B where
  obj _ := P
  map _ _ :=
    { f := fun _ => LinearMap.id
      comm := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

/-- The actual represented source and target at the common bound
`max v w z`. The singleton universe can be chosen to reach any larger bound. -/
abbrev ambientEnd (P : RightDGModuleModel B) :=
  category.{u,max v z,w,max v z} (endomorphismCategory.{u,v,w,z} P)

abbrev ambientBase (B : DGCategoryModel.{u,v,z} k) :=
  category.{u,v,z,max v w z} B

abbrev ambientModule (P : RightDGModuleModel B) :
    RightDGModuleModel (ambientBase.{u,v,w,z} B) :=
  (strictInput.{u,v,z,max v w z} B).obj P

/-- G13's common-bound models of the canonical endomorphism action. -/
abbrev AmbientModels (P : RightDGModuleModel B) :=
  AmbientSignedModels.{u,v,w,max v z,z,0} (endomorphismAction.{u,v,w,z} P)

/-- At the common bound the actual endomorphisms of the coefficient lift are
the lifted original endomorphisms by conjugation. The dg functor preserves
unit, multiplication, and differential. The represented left action has this
same map on the endomorphism complex after identifying its value with the
canonical coefficient lift. -/
def EndomorphismLiftComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k} (P : RightDGModuleModel B),
    ∃ F : DGFunctorModel (ambientEnd.{u,v,w,z} P)
        (endomorphismCategory.{u,max v w z,w,z} (ambientModule.{u,v,w,z} P)),
      (∀ a b, IsIso (F.map a b)) ∧
      (∀ (r : ℤ) (g : gradedHom P P r) (b : B.Obj)
          (i j : ℤ) (h : i+r=j) (x : (P.complex b).X i),
        component ((F.map PUnit.unit PUnit.unit).f r (ULift.up g)) b i j h (ULift.up x) =
          ULift.up (component g b i j h x)) ∧
      ∀ m : AmbientModels.{u,v,w,z} P,
        ∃ e : m.bimodule.obj PUnit.unit = ambientModule.{u,v,w,z} P,
          toComplexHom (m.bimodule.map PUnit.unit PUnit.unit) ≫
            eqToHom (congrArg (fun M => homComplex M M) e) =
              F.map PUnit.unit PUnit.unit

/-- The shifts of this module detect zero in the specified localization. -/
def ShiftedModuleDetectsZero (P : RightDGModuleModel B)
    (hB : HomotopyCategoryLaws B) : Prop :=
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance B hB
  let Q := Derived.quotient B hB
  ∀ Y : Derived.derivedCategory B hB,
    (∀ n : ℤ, Subsingleton (Q.obj (ShiftCone.shift P n) ⟶ Y)) → IsZero Y

/-- The exact derived tensor of the represented endomorphism action is an
equivalence for a compact K-projective generator. All three hypotheses are
on the canonical coefficient lift in the same target localization.
The signed models and the realization laws specify the G13 adjunction. -/
def AmbientEndomorphismEquivalence : Prop :=
  ∀ {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k}
    (P : RightDGModuleModel B) (m : AmbientModels.{u,v,w,z} P)
    (hA : HomotopyCategoryLaws (ambientEnd.{u,v,w,z} P))
    (hB : HomotopyCategoryLaws (ambientBase.{u,v,w,z} B)),
    letI := Derived.homotopyCategory _ hA
    letI := Derived.homotopyCategory _ hB
    letI := derivedCategoryInstance _ hA
    letI := derivedCategoryInstance _ hB
    ∀ (S : Preadditive (Derived.derivedCategory _ hB))
      (d : DerivedAdjunctionData.{u,v,w,z} m.models.tensor m.models.hom hA hB),
      LocalizationMapAdditive hB S →
      d.Realizes m.models.adjunction → d.ComputesRepresentatives → d.IsExact →
      isKProjective (ambientModule.{u,v,w,z} P) →
      CompactAt.{u,z,max v w z,max v w z} hB S
        ((Derived.quotient _ hB).obj (ambientModule.{u,v,w,z} P)) →
      ShiftedModuleDetectsZero (ambientModule.{u,v,w,z} P) hB →
      d.tensor.IsEquivalence

/-- At an already adequate bound the same assertion uses the actual native
localizations and the endomorphism action on the original module. -/
def NativeEndomorphismEquivalence : Prop :=
  ∀ {k : Type u} [CommRing k] {B : DGCategoryModel.{u,max v w z,z} k}
    (P : RightDGModuleModel B)
    (m : SignedModels.{u,v,w,z} (endomorphismAction.{u,max v w z,w,z} P))
    (hA : HomotopyCategoryLaws (endomorphismCategory.{u,max v w z,w,z} P))
    (hB : HomotopyCategoryLaws B),
    letI := Derived.homotopyCategory _ hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance _ hA
    letI := derivedCategoryInstance B hB
    ∀ (S : Preadditive (Derived.derivedCategory B hB))
      (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB),
      LocalizationMapAdditive hB S →
      d.Realizes m.adjunction → d.ComputesRepresentatives → d.IsExact →
      isKProjective P →
      CompactAt.{u,z,max v w z,max v w z} hB S ((Derived.quotient B hB).obj P) →
      ShiftedModuleDetectsZero P hB →
      d.tensor.IsEquivalence

end

end Specs.DerivedFormalization.DG.EndomorphismGenerator
