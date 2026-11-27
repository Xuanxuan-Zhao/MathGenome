import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLift

universe u v w

open CategoryTheory

namespace Specs.DerivedFormalization.DG.SemiFreeResolution

open _root_.DerivedFormalization

/-- The resolution in the given coefficient universe when it contains the object type. -/
def NativeResolution : Prop :=
  ∀ (k : Type u) [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (M : RightDGModuleModel A),
    ∃ (P : RightDGModuleModel A) (p : P ⟶ M),
      IndexedSemiFree.semiFree P ∧ Module.degreewiseSurjective p ∧ Module.quasiIsomorphism p

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

/-- The degree maps of the augmentation evaluated in the original target module. -/
def originalComponent {M : RightDGModuleModel A}
    {P : RightDGModuleModel (CoefficientLift.liftCategory.{u,v,w,w} A)}
    (p : P ⟶ CoefficientLift.liftModule.{u,v,w,w} M) (a : A.Obj) (n : ℤ) :
    (P.complex a).X n →ₗ[k] (M.complex a).X n :=
  ULift.moduleEquiv.toLinearMap.comp ((p.app a).f n).hom

/-- The comparison to the original target preserves its action and differential
and is surjective on terms and bijective on cycles modulo boundaries. -/
def ResolvesOriginal {M : RightDGModuleModel A}
    {P : RightDGModuleModel (CoefficientLift.liftCategory.{u,v,w,w} A)}
    (p : P ⟶ CoefficientLift.liftModule.{u,v,w,w} M) : Prop :=
  (∀ a n, Function.Surjective (originalComponent p a n)) ∧
  (∀ a n (x : (P.complex a).X n),
    originalComponent p a (n + 1) ((P.complex a).d n (n + 1) x) =
      (M.complex a).d n (n + 1) (originalComponent p a n x)) ∧
  (∀ (a b : A.Obj) (i j n : ℤ) (h : i + j = n)
      (x : (P.complex b).X i) (f : (A.hom a b).X j),
    originalComponent p a n (P.act i j n h x (ULift.up f)) =
      M.act i j n h (originalComponent p b i x) f) ∧
  (∀ (a : A.Obj) (n : ℤ) (y : (M.complex a).X n),
    (M.complex a).d n (n + 1) y = 0 →
      ∃ x : (P.complex a).X n, (P.complex a).d n (n + 1) x = 0 ∧
        originalComponent p a n x = y) ∧
  (∀ (a : A.Obj) (n : ℤ) (x : (P.complex a).X n),
    (P.complex a).d n (n + 1) x = 0 →
      (∃ y : (M.complex a).X (n - 1),
        (M.complex a).d (n - 1) n y = originalComponent p a n x) →
      ∃ z : (P.complex a).X (n - 1), (P.complex a).d (n - 1) n z = x)

/-- Every original module admits a resolution over the same objects and canonically
lifted arrows, with the strict augmentation compared to the original complexes. -/
def UnboundedSemiFreeResolution : Prop :=
  ∀ (k : Type u) [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (M : RightDGModuleModel A),
    ∃ (P : RightDGModuleModel (CoefficientLift.liftCategory.{u,v,w,w} A))
      (p : P ⟶ CoefficientLift.liftModule.{u,v,w,w} M),
      IndexedSemiFree.semiFree P ∧ Module.degreewiseSurjective p ∧
        Module.quasiIsomorphism p ∧ ResolvesOriginal p

end Specs.DerivedFormalization.DG.SemiFreeResolution
