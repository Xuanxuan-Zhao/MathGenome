import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergData
import Mathlib.Algebra.Homology.HomotopyCategory

/-! HA-G02 (comparison part), source 2499–2550.
A vertical homotopy is a homotopy in the category of horizontal complexes.
Thus every component is a horizontal chain map. No choice of splitting of
any row is part of the hypotheses.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

universe v u

namespace AdvancedHomologicalAlgebra.CartanEilenbergComparison
open CartanEilenbergData

variable {C : Type u} [Category.{v} C] [Abelian C]

abbrev rowMap {I J : DoubleComplex C} (a : I ⟶ J) : I.flip ⟶ J.flip :=
  (HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map a

def IsLift {K L : CochainComplex C ℤ} (R : ResolutionData K) (J : ResolutionData L)
    (f : K ⟶ L) (a : R.bicomplex ⟶ J.bicomplex) : Prop :=
  R.augmentation ≫ (rowMap a).f 0 = f ≫ J.augmentation

abbrev VerticalHomotopy {I J : DoubleComplex C} (a b : I ⟶ J) :=
  Homotopy (rowMap a) (rowMap b)

noncomputable abbrev totalMap {I J : DoubleComplex C}
    [I.HasTotal (ComplexShape.up ℤ)] [J.HasTotal (ComplexShape.up ℤ)] (a : I ⟶ J) :=
  HomologicalComplex₂.total.map a (ComplexShape.up ℤ)

/-- The complete component formula for the signed total homotopy. -/
def HasSignFormula {I J : DoubleComplex C}
    [I.HasTotal (ComplexShape.up ℤ)] [J.HasTotal (ComplexShape.up ℤ)]
    {a b : I ⟶ J} (s : VerticalHomotopy a b)
    (h : Homotopy (totalMap a) (totalMap b)) : Prop :=
  ∀ p q n : ℤ, ∀ e : p + q = n,
    I.ιTotal (ComplexShape.up ℤ) p q n e ≫ h.hom n (n - 1) =
      p.negOnePow • ((s.hom q (q - 1)).f p ≫
        J.ιTotal (ComplexShape.up ℤ) p (q - 1) (n - 1)
          (by change p + (q - 1) = n - 1; omega))

namespace Specs

def LiftExists : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K L : CochainComplex C ℤ}
    (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L),
    ∃ a : R.bicomplex ⟶ J.bicomplex, IsLift R J f a

def LiftHomotopy : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K L : CochainComplex C ℤ}
    (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L)
    (a b : R.bicomplex ⟶ J.bicomplex), IsLift R J f a → IsLift R J f b →
    Nonempty (VerticalHomotopy a b)

/-- This stronger statement applies to every vertical homotopy, not only those
constructed in the comparison proof. -/
def SignedTotalHomotopy : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] (I J : DoubleComplex C)
    [I.HasTotal (ComplexShape.up ℤ)] [J.HasTotal (ComplexShape.up ℤ)]
    (a b : I ⟶ J) (s : VerticalHomotopy a b),
    ∃ h : Homotopy (totalMap a) (totalMap b), HasSignFormula s h

def ComparisonIndependence : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K L : CochainComplex C ℤ}
    (R : ResolutionData K) (J : ResolutionData L)
    [R.bicomplex.HasTotal (ComplexShape.up ℤ)] [J.bicomplex.HasTotal (ComplexShape.up ℤ)]
    (f : K ⟶ L) (a b : R.bicomplex ⟶ J.bicomplex),
    IsLift R J f a → IsLift R J f b →
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (totalMap a) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (totalMap b)

/-- Compatibility with the components of the canonical total augmentations.
The augmentation in degree p is augmentation.f p followed by the (p,0)
diagonal inclusion; equality of these components is equality of chain maps. -/
def TotalAugmentationCompatibility : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K L : CochainComplex C ℤ}
    (R : ResolutionData K) (J : ResolutionData L)
    [R.bicomplex.HasTotal (ComplexShape.up ℤ)] [J.bicomplex.HasTotal (ComplexShape.up ℤ)]
    (f : K ⟶ L) (a : R.bicomplex ⟶ J.bicomplex), IsLift R J f a → ∀ p : ℤ,
    R.augmentation.f p ≫ R.bicomplex.ιTotal (ComplexShape.up ℤ) p 0 p (by simp) ≫
      (totalMap a).f p =
    f.f p ≫ J.augmentation.f p ≫ J.bicomplex.ιTotal (ComplexShape.up ℤ) p 0 p (by simp)

/-- Inverse vertical comparisons require no hypothesis about diagonal sums. -/
def VerticalInverseComparisons : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R J : ResolutionData K),
    ∃ (a : R.bicomplex ⟶ J.bicomplex) (b : J.bicomplex ⟶ R.bicomplex),
      IsLift R J (𝟙 K) a ∧ IsLift J R (𝟙 K) b ∧
      Nonempty (VerticalHomotopy (a ≫ b) (𝟙 R.bicomplex)) ∧
      Nonempty (VerticalHomotopy (b ≫ a) (𝟙 J.bicomplex))

/-- Inverse comparisons both vertically and after signed totalization. -/
def InverseComparisons : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R J : ResolutionData K)
    [R.bicomplex.HasTotal (ComplexShape.up ℤ)] [J.bicomplex.HasTotal (ComplexShape.up ℤ)],
    ∃ (a : R.bicomplex ⟶ J.bicomplex) (b : J.bicomplex ⟶ R.bicomplex),
      IsLift R J (𝟙 K) a ∧ IsLift J R (𝟙 K) b ∧
      Nonempty (VerticalHomotopy (a ≫ b) (𝟙 R.bicomplex)) ∧
      Nonempty (VerticalHomotopy (b ≫ a) (𝟙 J.bicomplex)) ∧
      ∃ e : HomotopyEquiv (DoubleTotalization.sumTotal R.bicomplex)
          (DoubleTotalization.sumTotal J.bicomplex),
        e.hom = totalMap a ∧ e.inv = totalMap b

end Specs
end AdvancedHomologicalAlgebra.CartanEilenbergComparison
