import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Away.Basic

/-! Independent statements for the finite principal cover assertion of FL-10
(paper.tex:683–738). The properties are the square-zero lifting properties
of FL-01. Only existence statements require finite presentation. The family
may be empty, and no nontriviality assumption is imposed on either ring. -/
namespace Specs.AdvCommAlg.FormalLifting.FiniteCoverLocality

universe u v

/-- Formal smoothness descends and ascends along a finite principal cover
of a finitely presented algebra. -/
def smoothFinitePrincipalCover : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] (n : ℕ) (b : Fin n → B),
    Ideal.span (Set.range b) = ⊤ →
      (formallySmoothValue A B ↔
        ∀ i, formallySmoothValue A (Localization.Away (b i)))

/-- Uniqueness descends and ascends without a finite presentation hypothesis. -/
def unramifiedFinitePrincipalCover : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) (b : Fin n → B), Ideal.span (Set.range b) = ⊤ →
      (formallyUnramifiedValue A B ↔
        ∀ i, formallyUnramifiedValue A (Localization.Away (b i)))

/-- Existence and uniqueness descend and ascend for finitely presented algebras. -/
def etaleFinitePrincipalCover : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] (n : ℕ) (b : Fin n → B),
    Ideal.span (Set.range b) = ⊤ →
      (formallyEtaleValue A B ↔
        ∀ i, formallyEtaleValue A (Localization.Away (b i)))

end Specs.AdvCommAlg.FormalLifting.FiniteCoverLocality
