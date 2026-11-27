import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.PretriangulatedHull

open CategoryTheory
open _root_.DerivedFormalization

universe u v w t

namespace Specs.DerivedFormalization.DG.MoritaHull

open BalancedTensor (bimodule)
open Derived (HomotopyCategoryLaws)
open DerivedBimoduleAdjunction (DerivedAdjunctionData SignedModels)
open DerivedKProjective (derivedCategoryInstance)
open FiniteCellConstructions (pretr)
open HomComplex (component)
open PretriangulatedHull (IsWrittenYoneda)

noncomputable section

variable {k : Type u} [CommRing k]

/-- The base and its written hull, with the same coefficient bound and the
original object sets. -/
abbrev source (A : DGCategoryModel.{u,v,w} k) : DGCategoryModel.{u,max v w t,w} k :=
  AmbientDerived.category.{u,v,w,max v t} A

abbrev target (A : DGCategoryModel.{u,v,w} k) : DGCategoryModel.{u,max v w t,max v w} k :=
  AmbientDerived.category.{u,max v w,max v w,t} (pretr A)

/-- Extension of scalars along the inclusion into the written pretriangulated
hull is an exact equivalence at every common adequate bound. The bimodule
uses representables of the Yoneda image; its arrow map is postcomposition
with the very morphism given by the original enriched Yoneda functor. -/
def HullDerivedEquivalence : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (hA : HomotopyCategoryLaws (source.{u,v,w,t} A))
    (hB : HomotopyCategoryLaws (target.{u,v,w,t} A)),
    let C := source.{u,v,w,t} A
    let B := target.{u,v,w,t} A
    letI := Derived.homotopyCategory C hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance C hA
    letI := derivedCategoryInstance B hB
    ∃ (Y : DGFunctorModel (Yoneda.liftCategory A) (pretr A)) (T : bimodule C B)
      (m : SignedModels.{u,max v w t,w,max v w} T)
      (d : DerivedAdjunctionData.{u,max v w t,w,max v w} m.tensor m.hom hA hB),
      IsWrittenYoneda Y ∧
      (∃ e : ∀ a, T.obj a ≅ Yoneda.representable (A := B) (Y.obj a),
        ∀ (a b : A.Obj) (r : ℤ) (f : (A.hom a b).X r) (X : B.Obj)
          (i j : ℤ) (h : i+r=j) (x : ((T.obj a).complex X).X i),
          ((e b).hom.app X).f j (component ((T.map a b).f r (ULift.up f)) X i j h x) =
            B.comp r i j (by omega) (ULift.up ((Y.map a b).f r (ULift.up f)))
              (((e a).hom.app X).f i x)) ∧
      d.Realizes m.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact ∧
      d.tensor.IsEquivalence

end
end Specs.DerivedFormalization.DG.MoritaHull
