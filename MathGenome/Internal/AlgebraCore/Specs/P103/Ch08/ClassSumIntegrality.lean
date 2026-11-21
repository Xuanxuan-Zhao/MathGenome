import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterConstructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-! Class sums and their scalars, paper.tex 1707–1722.
A class is an actual conjugacy class; a representative is any element of it.
The shared irreducibility convention includes nonzeroness. -/
noncomputable section
universe u v
namespace P103.Ch08.ClassSumIntegrality
open scoped MonoidAlgebra

variable {G : Type u} [Group G] [Fintype G]

/-- The finite set of elements of a conjugacy class. -/
def classMembers (D : ConjClasses G) : Finset G := by
  classical
  exact Finset.univ.filter (fun g => ConjClasses.mk g = D)

/-- The class sum in the finite-support group algebra. -/
def classSum (R : Type*) [CommRing R] (D : ConjClasses G) : R[G] :=
  ∑ g ∈ classMembers D, MonoidAlgebra.single g 1

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The scalar specified by the class size, character, and degree. -/
def classScalar (ρ : Representation ℂ G V) (D : ConjClasses G) (g : G) : ℂ :=
  (classMembers D).card * CharacterSpecs.characterValue ρ g / Module.finrank ℂ V

namespace Specs
/-- The given group algebra action equals the stated scalar action on every vector. -/
def scalarActionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
    ∀ (D : ConjClasses G) (g : G), ConjClasses.mk g = D →
      ∀ v : V, (representationModule ℂ G V ρ).act (classSum ℂ D) v =
        classScalar ρ D g • v

/-- No integrality certificate is part of the hypotheses. -/
def scalarIntegralType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
    ∀ (D : ConjClasses G) (g : G), ConjClasses.mk g = D →
      IsIntegral ℤ (classScalar ρ D g)
end Specs
end P103.Ch08.ClassSumIntegrality
