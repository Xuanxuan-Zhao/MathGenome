import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.Tensor
import Mathlib.Order.SuccPred.Limit

open CategoryTheory
open scoped Classical DirectSum

universe u v w z

namespace Specs.DerivedFormalization.Affine.FlatFiltration

open _root_.DerivedFormalization _root_.DerivedFormalization.Affine
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor term regular)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component)
open Specs.DerivedFormalization.DG.ShiftCone (shift)

variable {k : Type u} [Field k] [CharZero k]
variable {A : CommDGAlgebra.{u,v} k}

/-- A short exact sequence of dg modules split by right-linear maps of the
underlying graded modules. -/
structure GradedSplit {L M N : A.Module} (f : L ⟶ M) (g : M ⟶ N) where
  zero : f ≫ g = 0
  retraction : gradedHom M L 0
  sectionMap : gradedHom N M 0
  retract (n : ℤ) (x : term L n) :
    component retraction () n n (add_zero n) ((f.app ()).f n x) = x
  section_id (n : ℤ) (z : term N n) :
    (g.app ()).f n (component sectionMap () n n (add_zero n) z) = z
  decompose (n : ℤ) (y : term M n) :
    (f.app ()).f n (component retraction () n n (add_zero n) y) +
      component sectionMap () n n (add_zero n) ((g.app ()).f n y) = y

/-- A union of a linearly ordered diagram in a given dg module, with
injective structure maps and degreewise exhaustive images. -/
structure Union {J : Type w} [LinearOrder J] (F : J ⥤ A.Module) (M : A.Module) where
  incl : ∀ j, F.obj j ⟶ M
  comm {i j : J} (h : i ≤ j) : F.map (homOfLE h) ≫ incl j = incl i
  injective (j : J) (n : ℤ) : Function.Injective (((incl j).app ()).f n)
  exhaustive (n : ℤ) (x : term M n) : ∃ (j : J) (y : term (F.obj j) n), ((incl j).app ()).f n y = x

/-- The diagram of stages strictly earlier than a given stage. -/
abbrev earlier {J : Type w} [LinearOrder J] (F : J ⥤ A.Module) (j : J) :
    Set.Iio j ⥤ A.Module :=
  (show Monotone (fun i : Set.Iio j => i.val) from fun _ _ h => h).functor ⋙ F

/-- Continuity is degreewise exhaustiveness of the actual earlier-stage inclusions. -/
def Continuous {J : Type w} [LinearOrder J] (F : J ⥤ A.Module) : Prop :=
  ∀ j, Order.IsSuccLimit j → ∀ (n : ℤ) (x : term (F.obj j) n),
    ∃ (i : Set.Iio j) (y : term (F.obj i.val) n),
      ((F.map (homOfLE i.property.le)).app ()).f n y = x

/-- The specified closed inclusions exhibit the direct sum in every degree. -/
structure GradedDirectSum {I : Type z} (P : I → A.Module) (M : A.Module) where
  incl : ∀ i, P i ⟶ M
  bijective (n : ℤ) : Function.Bijective
    (DirectSum.toModule k I _ (fun i => ((incl i).app ()).f n |>.hom))

/-- A dg module which is a direct sum of shifts of the regular module. -/
def ShiftedFree (M : A.Module) : Prop :=
  ∃ (I : Type z) (s : I → ℤ), Nonempty (GradedDirectSum (fun i => shift (regular A) (s i)) M)

def ShiftFlatness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}
    (_ : ∀ N : A.Module, T.Formulas (𝟙 A) N)
    (M : A.Module) (s : ℤ), T.KFlat M → T.KFlat (shift M s)

def DirectSumFlatness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}
    (_ : ∀ N : A.Module, T.Formulas (𝟙 A) N)
    {I : Type z} {P : I → A.Module} {M : A.Module},
    GradedDirectSum P M → (∀ i, T.KFlat (P i)) → T.KFlat M

/-- K-flat modules are closed under degreewise unions with compatible injective
structure maps, with the tensor taken in the original dg-module category. -/
def UnionFlatness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}
    (_ : ∀ N : A.Module, T.Formulas (𝟙 A) N)
    {J : Type w} [LinearOrder J] {F : J ⥤ A.Module} {M : A.Module},
    Union F M → (∀ i, T.KFlat (F.obj i)) → T.KFlat M

def GradedSplitFlatness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}
    (_ : ∀ N : A.Module, T.Formulas (𝟙 A) N)
    {L M N : A.Module} {f : L ⟶ M} {g : M ⟶ N},
    GradedSplit f g → T.KFlat L → T.KFlat N → T.KFlat M

def FilteredFlatness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}
    (_ : ∀ N : A.Module, T.Formulas (𝟙 A) N)
    {J : Type w} [LinearOrder J] [WellFoundedLT J]
    (F : J ⥤ A.Module) {M : A.Module},
    Union F M → Continuous F →
    (∀ i, IsMin i → T.KFlat (F.obj i)) →
    (∀ i j, (h : i ⋖ j) → ∃ (Q : A.Module) (p : F.obj j ⟶ Q),
      Nonempty (GradedSplit (F.map (homOfLE h.lt.le)) p) ∧ T.KFlat Q) →
    T.KFlat M

def SemifreeFlatness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}
    (_ : ∀ N : A.Module, T.Formulas (𝟙 A) N)
    {J : Type w} [LinearOrder J] [WellFoundedLT J]
    (F : J ⥤ A.Module) {M : A.Module},
    Union F M → Continuous F →
    (∀ i, IsMin i → ShiftedFree.{u,v,z} (F.obj i)) →
    (∀ i j, (h : i ⋖ j) → ∃ (Q : A.Module) (p : F.obj j ⟶ Q),
      Nonempty (GradedSplit (F.map (homOfLE h.lt.le)) p) ∧ ShiftedFree.{u,v,z} Q) →
    T.KFlat M

end Specs.DerivedFormalization.Affine.FlatFiltration
