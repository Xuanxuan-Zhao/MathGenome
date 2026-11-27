import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLift
import Mathlib.Logic.Small.Basic

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization

universe u v w j t

namespace Specs.DerivedFormalization.DG.IndexedSums

open IndexedSemiFree (StrictSum SumTerm)
open CoefficientLift (liftCategory liftModule liftMap)

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {I : Type j} (F : I → RightDGModuleModel A)

def TermsSmall : Prop := ∀ a n, Small.{v} (SumTerm F a n)

def Realization : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} (F : I → RightDGModuleModel A), TermsSmall F →
    ∃ S, Nonempty (StrictSum F S)

def UniversalProperty : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {F : I → RightDGModuleModel A} {S : RightDGModuleModel A}
    (s : StrictSum F S), Nonempty (IsColimit (Cofan.mk S s.inclusion))

def ExistingCoproduct : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {F : I → RightDGModuleModel A} (c : Cofan F), IsColimit c →
    TermsSmall F ∧ ∃ s : StrictSum F c.pt, ∀ i, s.inclusion i = c.inj i

def ExistenceCriterion : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} (F : I → RightDGModuleModel A), HasCoproduct F ↔ TermsSmall F

def StrictComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {F : I → RightDGModuleModel A} {S T : RightDGModuleModel A}
    (s : StrictSum F S) (r : StrictSum F T),
    ∃ e : S ≅ T, (∀ i, s.inclusion i ≫ e.hom = r.inclusion i) ∧
      ∀ a n x, r.coordinates a n ((e.hom.app a).f n x) = s.coordinates a n x

def EmptyFamily : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} [IsEmpty I] (F : I → RightDGModuleModel A),
    ∃ (S : RightDGModuleModel A) (s : StrictSum F S),
      Nonempty (IsColimit (Cofan.mk S s.inclusion)) ∧
      ∀ a n (x : (S.complex a).X n), x = 0

def SmallIndex : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type v} (F : I → RightDGModuleModel A),
    ∃ s : StrictSum F (SemiFree.directSum F),
      (∀ i, s.inclusion i = SemiFree.sumInclusion F i) ∧
      (∀ a n x, s.coordinates a n x = x) ∧
      Nonempty (IsColimit (Cofan.mk (SemiFree.directSum F) (SemiFree.sumInclusion F)))

abbrev liftedFamily {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} (F : I → RightDGModuleModel A) (i : I) :=
  liftModule.{u,v,w,t} (F i)

/-- The index fits into the enlarged coefficient universe even when it did not fit
into the original one. The degreewise finite-support construction applies there. -/
def AdequateIndex : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} (F : I → RightDGModuleModel A),
    TermsSmall (liftedFamily.{u,v,w,j,j} F) ∧
      ∃ (S : RightDGModuleModel (liftCategory.{u,v,w,j} A))
        (s : StrictSum (liftedFamily.{u,v,w,j,j} F) S),
        Nonempty (IsColimit (Cofan.mk S s.inclusion))

/-- Lifting a realized sum preserves the finite-support coordinates themselves.
This applies at any enlargement, even if the index still exceeds that bound. -/
def LiftComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {F : I → RightDGModuleModel A} {S : RightDGModuleModel A}
    (s : StrictSum F S),
    ∃ r : StrictSum (liftedFamily.{u,v,w,j,t} F) (liftModule.{u,v,w,t} S),
      (∀ i, r.inclusion i = liftMap.{u,v,w,t} (s.inclusion i)) ∧
      (∀ a n x i, (r.coordinates a n x i).down = s.coordinates a n x.down i) ∧
      Nonempty (IsColimit (Cofan.mk (liftModule.{u,v,w,t} S) r.inclusion)) ∧
      ∀ {T} (q : StrictSum (liftedFamily.{u,v,w,j,t} F) T),
        ∃ e : liftModule.{u,v,w,t} S ≅ T,
          (∀ i, liftMap.{u,v,w,t} (s.inclusion i) ≫ e.hom = q.inclusion i) ∧
          ∀ a n x i, (q.coordinates a n ((e.hom.app a).f n x) i).down =
            s.coordinates a n x.down i

end Specs.DerivedFormalization.DG.IndexedSums
