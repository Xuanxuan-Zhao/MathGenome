import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.MackeyDecomposition
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Basic

/-! Mackey's irreducibility criterion, paper.tex 2088–2122.
The intersection is a subgroup of H, not a differently oriented conjugate.
A constituent is a nonzero simple submodule of the canonical group-algebra
module. Over a finite complex group every representation is semisimple, so
this is exactly the irreducible-constituent convention in the source. -/
noncomputable section
universe u v w
namespace P103.Ch09.MackeyIrreducibility
open scoped MonoidAlgebra

variable {J : Type u} [Group J]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- The representations have no isomorphic nonzero simple submodules. -/
def NoCommonConstituent (ρ : Representation ℂ J V) (σ : Representation ℂ J W) : Prop :=
  ∀ (S : Submodule ℂ[J] ρ.asModule) (T : Submodule ℂ[J] σ.asModule),
    IsSimpleModule ℂ[J] S → IsSimpleModule ℂ[J] T →
      ¬ Nonempty (S ≃ₗ[ℂ[J]] T)

variable {G : Type u} [Group G] (H : Subgroup G)

/-- Every representative outside the identity double coset is tested.
`HsH = H` is equivalent to `s ∈ H`. -/
def DisjointConjugates (ρ : Representation ℂ H V) : Prop :=
  ∀ s : G, s ∉ H → NoCommonConstituent
    (restrict (Mackey.intersection H H s) ρ) (Mackey.twist H H ρ s)

/-- For a normal subgroup the conjugate acts on H itself, by s⁻¹ h s. -/
def normalConjugation [H.Normal] (s : G) : H →* H where
  toFun h := ⟨s⁻¹ * (h : G) * s, Subgroup.Normal.conj_mem' inferInstance _ h.2 s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

def normalTwist [H.Normal] (ρ : Representation ℂ H V) (s : G) :
    Representation ℂ H V := ρ.comp (normalConjugation H s)

namespace Specs

/-- The induced action is quantified by its full tensor construction interface;
no irreducibility or nonzero fact about it is supplied as a hypothesis. -/
def criterionType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ H V) (D : InductionData H ρ),
    letI := D.module
    Ch08.Irreducible ℂ G (Induced H ρ) D.representation ↔
      Ch08.Irreducible ℂ H V ρ ∧ DisjointConjugates H ρ

def normalCriterionType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (H : Subgroup G) [H.Normal]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ H V) (D : InductionData H ρ),
    letI := D.module
    Ch08.Irreducible ℂ G (Induced H ρ) D.representation ↔
      Ch08.Irreducible ℂ H V ρ ∧
        ∀ s : G, s ∉ H → ¬ Nonempty (ρ.Equiv (normalTwist H ρ s))

/-- Nonzeroness must be derived from the actual tensor object. -/
def inducedNonzeroType : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ H V), Nontrivial (Induced H ρ)

/-- The normal-subgroup simplification, independently of the main criterion. -/
def normalDisjointnessType : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G) [H.Normal]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V), Ch08.Irreducible ℂ H V ρ →
      (DisjointConjugates H ρ ↔
        ∀ s : G, s ∉ H → ¬ Nonempty (ρ.Equiv (normalTwist H ρ s)))

end Specs
end P103.Ch09.MackeyIrreducibility
