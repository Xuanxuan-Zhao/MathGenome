import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Character stage of fa2:p2:gelfand, paper.tex:10190–10219, with the
chapter convention at 9907–9914: complex, complete, nonzero, and ‖1‖ = 1.
Characters are the shared algebraic nonzero linear multiplicative maps;
continuity is a conclusion. The initial topology of all evaluations is the
weak-star topology after their continuous-dual identification.
-/
noncomputable section

namespace Specs.ExpandedFA.BanachAlgebra.Characters
universe u
open Conventions

abbrev Character (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] :=
  CharacterValue ℂ A

def CharacterTopologyType :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A],
    TopologicalSpace (Character A)

def CharacterTopologyValue : CharacterTopologyType.{u} :=
  fun _ _ _ => TopologicalSpace.induced
    (fun χ a => χ.val a) Pi.topologicalSpace

def MaximalClosed : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A]
    (I : Ideal A), I.IsMaximal → IsClosed (I : Set A)

def AutomaticBoundedness : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] (χ : Character A),
    ∃ f : A →L[ℂ] ℂ, f.toLinearMap = χ.val ∧ ‖f‖ = 1 ∧
      ∀ a : A, ‖χ.val a‖ ≤ ‖a‖

/-- Every maximal ideal gives a quotient character, with the actual algebra
quotient and its scalar algebra isomorphism retained. -/
def MaximalQuotient : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A]
    (I : Ideal A), I.IsMaximal →
    ∃ (e : (A ⧸ I) ≃ₐ[ℂ] ℂ) (χ : Character A),
      (∀ a : A, χ.val a = e (Ideal.Quotient.mk I a)) ∧
      (∀ a : A, χ.val a = 0 ↔ a ∈ I)

/-- Conversely, every algebraic character is a quotient map of this form. -/
def CharacterQuotient : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] (χ : Character A),
    ∃ (I : Ideal A), I.IsMaximal ∧
      ∃ e : (A ⧸ I) ≃ₐ[ℂ] ℂ,
        (∀ a : A, χ.val a = e (Ideal.Quotient.mk I a)) ∧
        (∀ a : A, χ.val a = 0 ↔ a ∈ I)

/-- Kernels identify characters and maximal ideals bijectively. -/
def MaximalCorrespondence : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A]
    (I : Ideal A), I.IsMaximal ↔
      ∃! χ : Character A, ∀ a : A, χ.val a = 0 ↔ a ∈ I

/-- The topology agrees with the subspace topology in the weak continuous dual,
with the underlying scalar evaluations unchanged. -/
def NativeWeakStarIdentification : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A],
    letI := CharacterTopologyValue A
    ∃ e : Character A ≃ₜ WeakDual.characterSpace ℂ A,
      ∀ (χ : Character A) (a : A), e χ a = χ.val a

def CompactHausdorff : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A],
    @CompactSpace (Character A) (CharacterTopologyValue A) ∧
      @T2Space (Character A) (CharacterTopologyValue A)

def SpectrumCharacters : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] (a : A),
    AlgebraSpectrumValue ℂ A a = Set.range (fun χ : Character A => χ.val a)

end Specs.ExpandedFA.BanachAlgebra.Characters
