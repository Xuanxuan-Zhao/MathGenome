import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation
import Mathlib.Logic.Equiv.Fin.Basic

/-! SM-11, paper.tex:1288–1308. Counts refer to the specified finite
presentations, including when the algebra is the zero ring. No assertion of
uniqueness of a module rank is made. -/
namespace Specs.AdvCommAlg.Smooth

universe u v w
noncomputable section
open scoped TensorProduct

def standardSmoothComposition : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    standardSmoothValue A B → standardSmoothValue B C → standardSmoothValue A C

def standardSmoothBaseChange : Prop :=
  ∀ {A : Type u} {B : Type v} {T : Type w}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T],
    standardSmoothValue A B → standardSmoothValue T (T ⊗[A] B)

def standardSmoothTargetLocalization : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g : B) [IsLocalization.Away g C],
    standardSmoothValue A B → standardSmoothValue A C

/-- The actual combined presentation, with the new variables and equations
first. Reindexing merely identifies the two finite disjoint unions with Fin. -/
def compositionPresentation : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {n c m d : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin c))
    (Q : Algebra.Presentation B C (Fin m) (Fin d)),
    presentationStandardSmooth P → presentationStandardSmooth Q →
    let R : Algebra.Presentation A C (Fin (m + n)) (Fin (d + c)) :=
      (Q.comp P).reindex finSumFinEquiv.symm finSumFinEquiv.symm
    presentationStandardSmooth R ∧ R.dimension = (n - c) + (m - d)

/-- Transport the specified equations coefficientwise; neither finite index
set changes. The base algebra T is arbitrary. -/
def baseChangePresentation : Prop :=
  ∀ {A : Type u} {B : Type v} {T : Type w}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]
    {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c)),
    presentationStandardSmooth P →
    presentationStandardSmooth (P.baseChange T) ∧ (P.baseChange T).dimension = n - c

/-- Adjoin one inverse variable and its one equation to the given presentation.
The localization construction uses a polynomial lift of g through P. -/
def targetLocalizationPresentation : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g : B) [IsLocalization.Away g C]
    {n c : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin c)),
    presentationStandardSmooth P →
    let R : Algebra.Presentation A C (Fin (1 + n)) (Fin (1 + c)) :=
      ((Algebra.Presentation.localizationAway C g).comp P).reindex
        (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))
        (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))
    presentationStandardSmooth R ∧ R.dimension = n - c

end
end Specs.AdvCommAlg.Smooth
