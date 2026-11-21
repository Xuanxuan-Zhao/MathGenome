import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.VirtualCharacterRing
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InducedCharacter
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Rational Artin induction, paper.tex 2182–2196, 2206–2226.
The character lattice is the shared concrete ring of complex virtual characters.
A family is a set of subgroups; this is finite for a finite group, so its product
of modules is canonically its direct sum. Rationalization is the actual tensor
product over ℤ, with no rational-valuedness condition on characters. -/
noncomputable section
open scoped BigOperators TensorProduct Classical
universe u
namespace P103.Ch09.RationalInductionSpecs
open VirtualCharacterSpecs

variable {G : Type u} [Group G]

/-- Conjugates of the selected subgroups cover every element. -/
def Covers (ℋ : Set (Subgroup G)) : Prop :=
  ∀ g : G, ∃ H : ℋ, ∃ x : G, x⁻¹ * g * x ∈ H.1

variable [Fintype G]
local instance (ℋ : Set (Subgroup G)) : Fintype ℋ := Fintype.ofFinite ℋ

/-- Agreement with the actual induced-character formula on all virtual inputs.
Together with existence, this uniquely characterizes integral induction. -/
def IsInduction (ℋ : Set (Subgroup G))
    (ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G) : Prop :=
  ∀ H x, (ind H x).1 = InducedCharacterSpecs.inductionValue H.1 x.1

/-- The sum on integral lattices. -/
def integralTotal (ℋ : Set (Subgroup G)) (ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G) :
    (∀ H : ℋ, VirtualCharacterSpecs.Ring H.1) →ₗ[ℤ] VirtualCharacterSpecs.Ring G :=
  ∑ H : ℋ, (ind H).toIntLinearMap.comp (LinearMap.proj H)

/-- The map in the source: a finite direct sum of rationalized character
lattices, followed by the sum of induction maps. -/
def rationalSum (ℋ : Set (Subgroup G)) (ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G) :
    (∀ H : ℋ, ℚ ⊗[ℤ] VirtualCharacterSpecs.Ring H.1) →ₗ[ℚ] (ℚ ⊗[ℤ] VirtualCharacterSpecs.Ring G) :=
  ((integralTotal ℋ ind).baseChange ℚ).comp
    (TensorProduct.piRight ℤ ℚ ℚ (fun H : ℋ => VirtualCharacterSpecs.Ring H.1)).symm.toLinearMap

/-- All cyclic subgroups, including the trivial subgroup. -/
def cyclicFamily (G : Type u) [Group G] : Set (Subgroup G) :=
  {H | IsCyclic H}

namespace Expected

def integralInductionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (ℋ : Set (Subgroup G)),
    ∃ ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G, IsInduction ℋ ind

/-- Applies to every additive induction system with the prescribed formula;
`integralInductionType` supplies such a system unconditionally. -/
def criterionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (ℋ : Set (Subgroup G))
    (ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G),
    IsInduction ℋ ind → (Function.Surjective (rationalSum ℋ ind) ↔ Covers ℋ)

/-- Arbitrary virtual characters, hence in particular ordinary characters,
are rational combinations of inductions of virtual characters of cyclic groups. -/
def artinType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (χ : VirtualCharacterSpecs.Ring G),
    ∃ (n : ℕ) (H : Fin n → Subgroup G) (ψ : ∀ i, VirtualCharacterSpecs.Ring (H i)) (q : Fin n → ℚ),
      (∀ i, IsCyclic (H i)) ∧
      χ.1 = ∑ i, (q i : ℂ) • InducedCharacterSpecs.inductionValue (H i) (ψ i).1

/-- Coefficients are absorbed into virtual subgroup characters. The finite
sum is therefore precisely an integral linear combination of inductions. -/
def integralMultipleType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (χ : VirtualCharacterSpecs.Ring G),
    ∃ (N : ℕ) (n : ℕ) (H : Fin n → Subgroup G) (ψ : ∀ i, VirtualCharacterSpecs.Ring (H i)),
      0 < N ∧ (∀ i, IsCyclic (H i)) ∧
      N • χ.1 = ∑ i, InducedCharacterSpecs.inductionValue (H i) (ψ i).1

end Expected
end P103.Ch09.RationalInductionSpecs
