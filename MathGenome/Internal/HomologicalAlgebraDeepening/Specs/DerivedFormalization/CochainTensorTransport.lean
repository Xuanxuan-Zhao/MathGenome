import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorMonoidal
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainRingTransport
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! Signed cochain tensor and Hom at an independent module universe, and the
closed symmetric monoidal comparison over a represented coefficient ring. -/

namespace Specs.DerivedFormalization.CochainTensorTransport

open CategoryTheory MonoidalCategory
open scoped TensorProduct
open CochainComplex.HomComplex (Cochain)
open Cochains (compValue homotopyValue quotientValue stalkValue)
open CochainModels (internalHomValue internalHomMapValue isKProjectiveValue isKInjectiveValue)
open CochainTensor (tensor pure map isKFlat)
open CochainRingTransport
  (complexFunctorValue homotopyFunctorValue homotopyFactorsValue rankOneValue rankOneComparisonValue)

universe u v a

set_option linter.checkUnivs false
attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

noncomputable section

variable {R : Type u} [CommRing R]

/-- The raw signed tensor with a fixed factor on the right. -/
abbrev tensorWith (Y : compValue.{v} R) : compValue.{v} R ⥤ compValue.{v} R :=
  ((DG.Basic.moduleTensor.{u,v} R).map₂CochainComplex).flip.obj Y

/-- The raw signed Hom complex with a fixed source. -/
@[implicit_reducible]
def homFrom (Y : compValue.{v} R) : compValue.{v} R ⥤ compValue.{v} R where
  obj Z := internalHomValue Y Z
  map f := internalHomMapValue (𝟙 Y) f
  map_id Z := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext z : 1
    apply Cochain.ext
    intro i j hij
    simp [internalHomMapValue]
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext z : 1
    apply Cochain.ext
    intro i j hij
    simp [internalHomMapValue, Cochain.comp_zero_cochain_v]

/-- Component families for the comparison of currying over the original ring. -/
structure Currying (R : Type u) [CommRing R] where
  iso (X Y Z : compValue.{v} R) :
    internalHomValue (tensor X Y) Z ≅ internalHomValue X (internalHomValue Y Z)
  on_pure (X Y Z : compValue.{v} R) {q i j l m : ℤ} (hi : i + q = l) (hj : j + l = m)
      (f : Cochain (tensor X Y) Z q) (x : X.X i) (y : Y.X j) :
    (((iso X Y Z).hom.f q f).v i l hi x).v j m hj y =
      f.v (i + j) m (by omega) (pure X Y rfl x y)
  natural {X X' Y Y' Z Z' : compValue.{v} R}
      (b₁ : X' ⟶ X) (b₂ : Y' ⟶ Y) (c : Z ⟶ Z') :
    internalHomMapValue (map b₁ b₂) c ≫ (iso X' Y' Z').hom =
      (iso X Y Z).hom ≫ internalHomMapValue b₁ (internalHomMapValue b₂ c)
  differential (X Y Z : compValue.{v} R) {q i j l m : ℤ}
      (hi : i + (q + 1) = l) (hj : j + l = m)
      (f : Cochain (tensor X Y) Z q) (x : X.X i) (y : Y.X j) :
    ((((internalHomValue X (internalHomValue Y Z)).d q (q + 1)
        ((iso X Y Z).hom.f q f)).v i l hi x).v j m hj) y =
      Z.d (i + j + q) m (f.v (i + j) (i + j + q) rfl (pure X Y rfl x y)) -
      q.negOnePow • f.v (i + j + 1) m (by omega)
        (pure X Y (by omega : i + 1 + j = i + j + 1) (X.d i (i + 1) x) y) -
      (q + i).negOnePow • f.v (i + j + 1) m (by omega)
        (pure X Y (by omega : i + (j + 1) = i + j + 1) x (Y.d j (j + 1) y))

def curryingType : Prop :=
  ∀ (R : Type u) [CommRing R], Nonempty (Currying.{u,v} R)

/-- The chain and homotopy adjunctions with the same homogeneous evaluations. -/
structure ClosedAdjunction {R : Type u} [CommRing R] (Y : compValue.{v} R) where
  adj : tensorWith Y ⊣ homFrom Y
  left : homotopyValue.{v} R ⥤ homotopyValue.{v} R
  right : homotopyValue.{v} R ⥤ homotopyValue.{v} R
  adjK : left ⊣ right
  leftFactors : quotientValue R ⋙ left ≅ tensorWith Y ⋙ quotientValue R
  rightFactors : quotientValue R ⋙ right ≅ homFrom Y ⋙ quotientValue R
  on_pure (X Z : compValue.{v} R) (f : tensor X Y ⟶ Z) (i j : ℤ)
      (x : X.X i) (y : Y.X j) :
    ((adj.homEquiv X Z f).f i x).v j (i + j) (add_comm j i) y =
      f.f (i + j) (pure X Y rfl x y)
  counit_on_pure (Z : compValue.{v} R) (i j : ℤ)
      (f : (internalHomValue Y Z).X i) (y : Y.X j) :
    (adj.counit.app Z).f (i + j) (pure (internalHomValue Y Z) Y rfl f y) =
      f.v j (i + j) (add_comm j i) y
  homotopy (X Z : compValue.{v} R) (f : tensor X Y ⟶ Z) :
    adjK.homEquiv ((quotientValue R).obj X) ((quotientValue R).obj Z)
        (leftFactors.hom.app X ≫ (quotientValue R).map f) ≫ rightFactors.hom.app Z =
      (quotientValue R).map (adj.homEquiv X Z f)

def closedAdjunctionType : Prop :=
  ∀ {R : Type u} [CommRing R] (Y : compValue.{v} R), Nonempty (ClosedAdjunction Y)

section Representation

variable {A : Type a} [CommRing A] (e : R ≃+* A)

local notation "F" => complexFunctorValue e
local notation "FK" => homotopyFunctorValue e

/-- Comparison of the signed complexes under the exact same-carrier ring equivalence. -/
structure RingComparison where
  tensorIso (X Y : compValue.{a} R) : tensor ((F).obj X) ((F).obj Y) ≅ (F).obj (tensor X Y)
  tensor_on_pure (X Y : compValue.{a} R) {i j n : ℤ} (h : i + j = n)
      (x : X.X i) (y : Y.X j) :
    (tensorIso X Y).hom.f n (pure ((F).obj X) ((F).obj Y) h x y) = pure X Y h x y
  tensor_natural {X X' Y Y' : compValue.{a} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    map ((F).map f) ((F).map g) ≫ (tensorIso X' Y').hom =
      (tensorIso X Y).hom ≫ (F).map (map f g)
  homIso (X Y : compValue.{a} R) :
    (F).obj (internalHomValue X Y) ≅ internalHomValue ((F).obj X) ((F).obj Y)
  hom_on_eval (X Y : compValue.{a} R) {q i j : ℤ} (h : i + q = j)
      (f : Cochain X Y q) (x : X.X i) :
    ((homIso X Y).hom.f q f).v i j h x = f.v i j h x
  hom_natural {X X' Y Y' : compValue.{a} R} (f : X' ⟶ X) (g : Y ⟶ Y') :
    (F).map (internalHomMapValue f g) ≫ (homIso X' Y').hom =
      (homIso X Y).hom ≫ internalHomMapValue ((F).map f) ((F).map g)
  kFlat (X : compValue.{a} R) : isKFlat ((F).obj X) ↔ isKFlat X
  kProjective (X : compValue.{a} R) : isKProjectiveValue ((F).obj X) ↔ isKProjectiveValue X
  kInjective (X : compValue.{a} R) : isKInjectiveValue ((F).obj X) ↔ isKInjectiveValue X

def ringComparisonType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A),
    Nonempty (RingComparison e)

/-- The original ring's rank-one stalk using the chosen representative. -/
abbrev representedUnit : compValue.{a} R := (stalkValue R).obj (rankOneValue e)

abbrev representedUnitZero : (representedUnit e).X 0 ≅ rankOneValue e :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 (rankOneValue e)

/-- The ordinary structures and comparisons over a represented ring.
The diagonal cochain category uses the established Mathlib monoidal structure. -/
structure AdequateModel extends RingComparison e where
  chainMonoidal : MonoidalCategory (compValue.{a} R)
  chainSymmetric : @SymmetricCategory (compValue.{a} R) _ chainMonoidal
  chainClosed : @MonoidalClosed (compValue.{a} R) _ chainMonoidal
  homotopyMonoidal : MonoidalCategory (homotopyValue.{a} R)
  homotopySymmetric : @SymmetricCategory (homotopyValue.{a} R) _ homotopyMonoidal
  homotopyClosed : @MonoidalClosed (homotopyValue.{a} R) _ homotopyMonoidal
  nativeSymmetric : SymmetricCategory (compValue.{a} A)
  nativeKoszul : CochainTensorMonoidal.HasKoszulBraiding nativeSymmetric
  nativeHomotopyMonoidal : MonoidalCategory (homotopyValue.{a} A)
  nativeHomotopySymmetric : @SymmetricCategory (homotopyValue.{a} A) _ nativeHomotopyMonoidal
  chainTransport :
    letI := chainMonoidal
    letI := chainSymmetric
    letI := nativeSymmetric
    (F).Braided
  homotopyTransport :
    letI := homotopyMonoidal
    letI := homotopySymmetric
    letI := nativeHomotopyMonoidal
    letI := nativeHomotopySymmetric
    (FK).Braided
  quotientBraided :
    letI := chainMonoidal
    letI := chainSymmetric
    letI := homotopyMonoidal
    letI := homotopySymmetric
    (quotientValue.{a} R).Braided
  nativeQuotientBraided :
    letI := nativeSymmetric
    letI := nativeHomotopyMonoidal
    letI := nativeHomotopySymmetric
    (quotientValue.{a} A).Braided
  nativeQuotientModels :
    letI := nativeSymmetric
    letI := nativeHomotopyMonoidal
    letI := nativeHomotopySymmetric
    letI := nativeQuotientBraided
    (∃ h : 𝟙_ (homotopyValue.{a} A) =
        (quotientValue.{a} A).obj (CochainTensorMonoidal.tensorUnitValue A),
      Functor.LaxMonoidal.ε (quotientValue.{a} A) = eqToHom h) ∧
    ∀ X Y : compValue.{a} A,
      ∃ h : (quotientValue A).obj X ⊗ (quotientValue A).obj Y =
          (quotientValue A).obj (CochainModels.tensorComplexValue X Y),
        Functor.LaxMonoidal.μ (quotientValue A) X Y = eqToHom h
  quotientTransport :
    letI := chainMonoidal
    letI := chainSymmetric
    letI := homotopyMonoidal
    letI := homotopySymmetric
    letI := nativeSymmetric
    letI := nativeHomotopyMonoidal
    letI := nativeHomotopySymmetric
    letI := chainTransport
    letI := homotopyTransport
    letI := quotientBraided
    letI := nativeQuotientBraided
    NatTrans.IsMonoidal (homotopyFactorsValue e).hom
  tensorModel (X Y : compValue.{a} R) :
    letI := chainMonoidal
    tensor X Y ≅ X ⊗ Y
  unitModel :
    letI := chainMonoidal
    representedUnit e ≅ 𝟙_ (compValue.{a} R)
  tensorModel_transport (X Y : compValue.{a} R) :
    letI := chainMonoidal
    letI := chainSymmetric
    letI := nativeSymmetric
    letI := chainTransport
    Functor.LaxMonoidal.μ F X Y = (tensorIso X Y).hom ≫ (F).map (tensorModel X Y).hom
  unitModel_transport :
    letI := chainMonoidal
    letI := chainSymmetric
    letI := nativeSymmetric
    letI := chainTransport
    Functor.LaxMonoidal.ε F = (rankOneComparisonValue e).inv ≫ (F).map unitModel.hom
  tensorModel_natural {X X' Y Y' : compValue.{a} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := chainMonoidal
    map f g ≫ (tensorModel X' Y').hom = (tensorModel X Y).hom ≫ (f ⊗ₘ g)
  homModel (Y : compValue.{a} R) :
    letI := chainMonoidal
    letI := chainClosed
    ihom Y ≅ homFrom Y
  rawClosed (Y : compValue.{a} R) : ClosedAdjunction Y
  homotopyHomModel (Y : compValue.{a} R) :
    letI := homotopyMonoidal
    letI := homotopyClosed
    ihom ((quotientValue R).obj Y) ≅ (rawClosed Y).right
  chainAdjunction (Y : compValue.{a} R) :
    letI := chainMonoidal
    letI := chainSymmetric
    letI := chainClosed
    ∀ (X Z : compValue.{a} R) (f : X ⊗ Y ⟶ Z),
      ((ihom.adjunction Y).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight Y)).homEquiv
        X Z f ≫ (homModel Y).hom.app Z =
      (rawClosed Y).adj.homEquiv X Z ((tensorModel X Y).hom ≫ f)
  homotopyAdjunction (Y : compValue.{a} R) :
    letI := chainMonoidal
    letI := chainSymmetric
    letI := homotopyMonoidal
    letI := homotopySymmetric
    letI := homotopyClosed
    letI := quotientBraided
    ∀ (X Z : compValue.{a} R) (f : tensor X Y ⟶ Z),
      let q := quotientValue.{a} R
      let L := Functor.LaxMonoidal.μ q X Y ≫ q.map (tensorModel X Y).inv
      ((ihom.adjunction (q.obj Y)).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight (q.obj Y))).homEquiv (q.obj X) (q.obj Z)
        (L ≫ q.map f) ≫ (homotopyHomModel Y).hom.app (q.obj Z) ≫
          (rawClosed Y).rightFactors.hom.app Z =
        q.map ((rawClosed Y).adj.homEquiv X Z f)
  associator_on_pure (X Y Z : compValue.{a} R) (i j k : ℤ) {m l n : ℤ}
      (h : i + j = m) (hn : m + k = n) (h' : j + k = l) (hn' : i + l = n)
      (x : X.X i) (y : Y.X j) (z : Z.X k) :
    letI := chainMonoidal
    let L := tensorModel (tensor X Y) Z ≪≫ MonoidalCategory.tensorIso (tensorModel X Y) (Iso.refl Z)
    let U := tensorModel X (tensor Y Z) ≪≫ MonoidalCategory.tensorIso (Iso.refl X) (tensorModel Y Z)
    (L ≪≫ α_ X Y Z ≪≫ U.symm).hom.f n
      (pure (tensor X Y) Z hn (pure X Y h x y) z) =
      pure X (tensor Y Z) hn' x (pure Y Z h' y z)
  leftUnitor_on_pure (X : compValue.{a} R) (i : ℤ) (r : A) (x : X.X i) :
    letI := chainMonoidal
    (tensorModel (representedUnit e) X ≪≫ MonoidalCategory.tensorIso unitModel (Iso.refl X) ≪≫ λ_ X).hom.f i
      (pure (representedUnit e) X (zero_add i) ((representedUnitZero e).inv r) x) = e.symm r • x
  rightUnitor_on_pure (X : compValue.{a} R) (i : ℤ) (x : X.X i) (r : A) :
    letI := chainMonoidal
    (tensorModel X (representedUnit e) ≪≫ MonoidalCategory.tensorIso (Iso.refl X) unitModel ≪≫ ρ_ X).hom.f i
      (pure X (representedUnit e) (add_zero i) x ((representedUnitZero e).inv r)) = e.symm r • x
  braiding_on_pure (X Y : compValue.{a} R) {i j n : ℤ} (h : i + j = n)
      (x : X.X i) (y : Y.X j) :
    letI := chainMonoidal
    letI := chainSymmetric
    (tensorModel X Y ≪≫ β_ X Y ≪≫ (tensorModel Y X).symm).hom.f n (pure X Y h x y) =
      (i * j).negOnePow • pure Y X (by omega : j + i = n) y x

/-- Use a shrink at any bound in which R is small, a lift at a common
larger bound, or R itself with the identity equivalence. -/
def adequateModelType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A),
    Nonempty (AdequateModel e)

end Representation

end

end Specs.DerivedFormalization.CochainTensorTransport
