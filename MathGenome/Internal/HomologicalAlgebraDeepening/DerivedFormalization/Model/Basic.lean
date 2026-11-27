import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

universe w v u

namespace DerivedFormalization

namespace FunctorialModelCategory

/-- Equip a Mathlib model category with the full small (co)limits and
the two functorial factorizations of Q01. -/
@[instance_reducible]
def ofInstances (C : Type u) [Category.{v} C] [ModelCategory C] [HasLimits C] [HasColimits C]
    [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
    [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] :
    FunctorialModelCategory C where
  toModelCategory := inferInstance
  hasLimits := inferInstance
  hasColimits := inferInstance
  cofibrationFactorization := inferInstance
  fibrationFactorization := inferInstance

end FunctorialModelCategory

namespace Model

variable {C : Type u} [Category.{v} C]

theorem hasLiftingProperty_iff_exists_diagonal {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔
      ∀ (a : A ⟶ X) (b : B ⟶ Y), a ≫ p = i ≫ b →
        ∃ d : B ⟶ X, i ≫ d = a ∧ d ≫ p = b := by
  constructor
  · intro h a b comm
    let sq : CommSq a i p b := ⟨comm⟩
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
  · intro h
    refine ⟨fun {a b} sq ↦ ?_⟩
    obtain ⟨d, hd₁, hd₂⟩ := h a b sq.w
    exact CommSq.HasLift.mk' { l := d, fac_left := hd₁, fac_right := hd₂ }

theorem arrowRetract_iff {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) :
    Nonempty (RetractArrow f g) ↔
      ∃ (s₀ : A ⟶ X) (s₁ : B ⟶ Y) (r₀ : X ⟶ A) (r₁ : Y ⟶ B),
        s₀ ≫ g = f ≫ s₁ ∧ r₀ ≫ f = g ≫ r₁ ∧
          s₀ ≫ r₀ = 𝟙 A ∧ s₁ ≫ r₁ = 𝟙 B := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.i.left, h.i.right, h.r.left, h.r.right, h.i_w, h.r_w,
      h.retract_left, h.retract_right⟩
  · rintro ⟨s₀, s₁, r₀, r₁, hs, hr, h₀, h₁⟩
    exact ⟨{ i := Arrow.homMk s₀ s₁ hs
             r := Arrow.homMk r₀ r₁ hr
             retract := Arrow.hom_ext _ _ h₀ h₁ }⟩

variable [ModelCategory C]

theorem isomorphisms (C : Type u) [Category.{v} C] [ModelCategory C] :
    MorphismProperty.isomorphisms C ≤ weakEquivalences C ∧
      MorphismProperty.isomorphisms C ≤ cofibrations C ∧
      MorphismProperty.isomorphisms C ≤ fibrations C := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B f hf
    have : IsIso f := hf
    exact mem_weakEquivalences f
  · intro A B f hf
    have : IsIso f := hf
    exact mem_cofibrations f
  · intro A B f hf
    have : IsIso f := hf
    exact mem_fibrations f

theorem isCofibrant_iff (A : C) :
    IsCofibrant A ↔ cofibrations C (initial.to A) :=
  cofibration_iff _

theorem isFibrant_iff (A : C) :
    IsFibrant A ↔ fibrations C (terminal.from A) :=
  fibration_iff _

theorem liftingClasses (C : Type u) [Category.{v} C] [ModelCategory C] :
    (trivialFibrations C).llp = cofibrations C ∧
      (cofibrations C).rlp = trivialFibrations C ∧
      (fibrations C).llp = trivialCofibrations C ∧
      (trivialCofibrations C).rlp = fibrations C :=
  ⟨trivialFibrations_llp C, cofibrations_rlp C, fibrations_llp C, trivialCofibrations_rlp C⟩

instance cofibrations_transfiniteComposition :
    IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
  rw [← trivialFibrations_llp C]
  infer_instance

instance trivialCofibrations_transfiniteComposition :
    IsStableUnderTransfiniteComposition.{w} (trivialCofibrations C) := by
  rw [← fibrations_llp C]
  infer_instance

instance fibrations_inverseTransfiniteComposition :
    IsStableUnderTransfiniteComposition.{w} (fibrations C).op := by
  rw [← cofibrations_op C]
  exact cofibrations_transfiniteComposition

instance trivialFibrations_inverseTransfiniteComposition :
    IsStableUnderTransfiniteComposition.{w} (trivialFibrations C).op := by
  rw [← trivialCofibrations_op C]
  exact trivialCofibrations_transfiniteComposition

open Specs.ModelBasic in
theorem liftingClassClosure (C : Type u) [Category.{v} C] [ModelCategory C] :
    LeftClassClosed.{w} (cofibrations C) ∧
      RightClassClosed.{w} (trivialFibrations C) ∧
      LeftClassClosed.{w} (trivialCofibrations C) ∧
      RightClassClosed.{w} (fibrations C) :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩⟩

end Model
end DerivedFormalization
