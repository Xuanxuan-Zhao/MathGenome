import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! Independent specifications for the ordinary symmetric cochain tensor and its descent. -/

namespace Specs.DerivedFormalization.CochainTensorMonoidal

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Cochains (compValue homotopyValue quotientValue stalkValue)
open CochainModels (tensorComplexValue)
open scoped TensorProduct

universe u w w'

noncomputable section

variable {R : Type u} [CommRing R]

local instance (M : ModuleCat.{u} R) :
    PreservesColimitsOfSize.{w, w'} ((curriedTensor (ModuleCat R)).obj M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

local instance (M : ModuleCat.{u} R) :
    PreservesColimitsOfSize.{w, w'} ((curriedTensor (ModuleCat R)).flip.obj M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

def cochainMonoidalType := ∀ {R : Type u} [CommRing R], MonoidalCategory (compValue.{u} R)

abbrev cochainMonoidalValue : MonoidalCategory (compValue.{u} R) :=
  HomologicalComplex.monoidalCategory (ModuleCat R) (.up ℤ)

def pureTensorType :=
  ∀ {R : Type u} [CommRing R] (X Y : compValue.{u} R) (i j : ℤ) {n : ℤ},
    i + j = n → X.X i → Y.X j → (tensorComplexValue X Y).X n

abbrev pureTensorValue (X Y : compValue.{u} R) (i j : ℤ) {n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) : (tensorComplexValue X Y).X n :=
  HomologicalComplex.ιTensorObj X Y i j n h (x ⊗ₜ[R] y)

def tensorUnitType := ∀ (R : Type u) [CommRing R], compValue.{u} R

abbrev tensorUnitValue (R : Type u) [CommRing R] : compValue.{u} R :=
  (stalkValue R).obj (ModuleCat.of R R)

def tensorUnitZeroType :=
  ∀ (R : Type u) [CommRing R], (tensorUnitValue R).X 0 ≅ ModuleCat.of R R

abbrev tensorUnitZeroValue (R : Type u) [CommRing R] :
    (tensorUnitValue R).X 0 ≅ ModuleCat.of R R :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)

def associatorApplyType : Prop :=
  ∀ {R : Type u} [CommRing R] (X Y Z : compValue.{u} R) (i j k : ℤ) {m l n : ℤ}
    (h : i + j = m) (hn : m + k = n) (h' : j + k = l) (hn' : i + l = n)
    (x : X.X i) (y : Y.X j) (z : Z.X k),
    (α_ X Y Z).hom.f n
      (pureTensorValue (tensorComplexValue X Y) Z m k hn (pureTensorValue X Y i j h x y) z) =
    pureTensorValue X (tensorComplexValue Y Z) i l hn' x (pureTensorValue Y Z j k h' y z)

def leftUnitorApplyType : Prop :=
  ∀ {R : Type u} [CommRing R] (X : compValue.{u} R) (i : ℤ) (r : R) (x : X.X i),
    (λ_ X).hom.f i
      (pureTensorValue (tensorUnitValue R) X 0 i (zero_add i) ((tensorUnitZeroValue R).inv r) x) =
    r • x

def rightUnitorApplyType : Prop :=
  ∀ {R : Type u} [CommRing R] (X : compValue.{u} R) (i : ℤ) (x : X.X i) (r : R),
    (ρ_ X).hom.f i
      (pureTensorValue X (tensorUnitValue R) i 0 (add_zero i) x ((tensorUnitZeroValue R).inv r)) =
    r • x

/-- The braiding of the stated symmetric structure has the Koszul sign on every summand. -/
def HasKoszulBraiding (s : SymmetricCategory (compValue.{u} R)) : Prop :=
  letI := s
  ∀ (X Y : compValue.{u} R) (i j : ℤ) {n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j),
    (β_ X Y).hom.f n (pureTensorValue X Y i j h x y) =
      (i * j).negOnePow • pureTensorValue Y X j i (by omega : j + i = n) y x

def cochainSymmetricType : Prop :=
  ∀ (R : Type u) [CommRing R], ∃ s : SymmetricCategory (compValue.{u} R), HasKoszulBraiding s

/-- The quotient is strong symmetric monoidal with identity tensor and unit comparisons. -/
def homotopySymmetricType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ (s : SymmetricCategory (compValue.{u} R)) (m : MonoidalCategory (homotopyValue.{u} R)),
      HasKoszulBraiding s ∧
      letI := s
      letI := m
      ∃ t : SymmetricCategory (homotopyValue.{u} R),
        letI := t
        ∃ b : (quotientValue.{u} R).Braided,
          letI := b
          (∃ h : 𝟙_ (homotopyValue.{u} R) = (quotientValue.{u} R).obj (tensorUnitValue R),
            Functor.LaxMonoidal.ε (quotientValue.{u} R) = eqToHom h) ∧
          ∀ X Y : compValue.{u} R,
            ∃ h : (quotientValue R).obj X ⊗ (quotientValue R).obj Y =
                (quotientValue R).obj (tensorComplexValue X Y),
              Functor.LaxMonoidal.μ (quotientValue R) X Y = eqToHom h

end

end Specs.DerivedFormalization.CochainTensorMonoidal
