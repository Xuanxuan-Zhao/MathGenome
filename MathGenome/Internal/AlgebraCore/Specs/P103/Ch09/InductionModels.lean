import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules
import Mathlib.GroupTheory.Complement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.RepresentationTheory.Induced

/-! The Chapter 9 left-tensor convention, for arbitrary groups and vector spaces.
The tensor object is the shared noncommutative tensor, not a new quotient.
Construction witnesses below must supply the scalar and group actions together
with their values on all elementary tensors. -/

noncomputable section
universe u v w x
namespace P103.Ch09
open scoped MonoidAlgebra DirectSum

variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)

/-- The inclusion of subgroup algebras. -/
def subgroupAlgebra : k[H] →ₐ[k] k[G] :=
  MonoidAlgebra.mapDomainAlgHom k k H.subtype

/-- Right multiplication by the subgroup algebra, as an opposite-ring action. -/
@[instance_reducible] def rightSubgroupModule : Module k[H]ᵐᵒᵖ k[G] :=
  Module.compHom k[G] (subgroupAlgebra (k := k) H).toRingHom.op

attribute [local instance] rightSubgroupModule

variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Restriction leaves the vector space and each subgroup operator unchanged. -/
def restrict (ρ : Representation k G V) : Representation k H V := ρ.comp H.subtype

/-- The underlying group of `k[G] ⊗_{k[H]} V`. The type synonym on the second
factor carries precisely the algebra action established in Chapter 8. -/
abbrev Induced (ρ : Representation k H V) :=
  BalancedTensor.Tensor k[H] k[G] ρ.asModule

/-- Elementary tensors with arguments on the original vector space. -/
def tensor (ρ : Representation k H V) (a : k[G]) (z : V) : Induced H ρ :=
  BalancedTensor.tmul k[H] a (ρ.asModuleEquiv.symm z)

/-- A construction of the left induced action, characterized on the shared
tensor product. Neither dimension nor index is assumed finite. -/
structure InductionData (ρ : Representation k H V) where
  module : Module k (Induced H ρ)
  representation : @Representation k G (Induced H ρ) _ _ _ module
  scalar_tensor : ∀ (c : k) (a : k[G]) (z : V),
    (letI := module; c • tensor H ρ a z) = tensor H ρ (c • a) z
  action_tensor : ∀ (g : G) (a : k[G]) (z : V),
    representation g (tensor H ρ a z) = tensor H ρ (MonoidAlgebra.single g 1 * a) z

/-- Covariant functions with support in finitely many left cosets. -/
def functions (ρ : Representation k H V) : Submodule k (G → V) where
  carrier := {f | (∀ (x : G) (h : H), f (x * h) = ρ h⁻¹ (f x)) ∧
    (QuotientGroup.mk '' Function.support f : Set (G ⧸ H)).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    refine ⟨by intro x h; simp [hf.1, hg.1], ?_⟩
    apply (hf.2.union hg.2).subset
    rintro q ⟨x, hx, rfl⟩
    by_cases hfx : f x = 0
    · right
      exact ⟨x, by simpa [Function.mem_support, hfx] using hx, rfl⟩
    · left
      exact ⟨x, hfx, rfl⟩
  smul_mem' := by
    intro c f hf
    refine ⟨by intro x h; simp [hf.1], ?_⟩
    apply hf.2.subset
    rintro q ⟨x, hx, rfl⟩
    exact ⟨x, by
      change c • f x ≠ 0 at hx
      change f x ≠ 0
      intro hz
      exact hx (by simp [hz]), rfl⟩


/-- A function-model comparison in precisely the source's left-coset convention.
The two generator formulas characterize the image on every point of G. -/
structure FunctionModelData (ρ : Representation k H V) (D : InductionData H ρ) where
  equivalence : letI := D.module; Induced H ρ ≃ₗ[k] functions H ρ
  equivariant : ∀ (g : G) (z : Induced H ρ) (x : G),
    (equivalence (D.representation g z)).1 x = (equivalence z).1 (g⁻¹ * x)
  generator_mul : ∀ (t : G) (h : H) (z : V),
    (equivalence (tensor H ρ (MonoidAlgebra.single t 1) z)).1 (t * h) = ρ h⁻¹ z
  generator_zero : ∀ (t x : G) (z : V),
    (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk t →
      (equivalence (tensor H ρ (MonoidAlgebra.single t 1) z)).1 x = 0

namespace Specs

def restrictionType : Type (max (u + 1) (v + 1) (w + 1)) :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V],
    Representation k G V → Representation k H V

def restrictionValue : restrictionType.{u,v,w} :=
  fun {_ _} _ _ H {_} _ _ ρ => restrict H ρ

def tensorConstructionType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V),
    Nonempty (InductionData H ρ)


/-- The function space carries the stated left-translation action. -/
def functionConstructionType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V),
    ∃ τ : Representation k G (functions H ρ),
      ∀ (g : G) (f : functions H ρ) (x : G), (τ g f).1 x = f.1 (g⁻¹ * x)

/-- One representative-free function comparison works with every left
transversal. The finite-sum inverse also explicitly implies independence from
representatives. Finsupp is the usual algebraic direct sum of copies of V. -/
def modelsType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V),
    ∃ (D : InductionData H ρ) (E : FunctionModelData H ρ D),
      (∀ (T : Set G) (_hT : Subgroup.IsComplement T (H : Set G)),
        letI := D.module
        ∃ L : (T →₀ V) ≃ₗ[k] Induced H ρ,
          (∀ (t : T) (z : V), L (Finsupp.single t z) =
            tensor H ρ (MonoidAlgebra.single (t : G) 1) z) ∧
          (∀ (f : functions H ρ) (s : Finset T),
            (∀ t : T, f.1 t ≠ 0 → t ∈ s) →
            E.equivalence.symm f =
              ∑ t ∈ s, tensor H ρ (MonoidAlgebra.single (t : G) 1) (f.1 t))) ∧
      (∀ [H.FiniteIndex] [FiniteDimensional k V],
        letI := D.module
        FiniteDimensional k (Induced H ρ) ∧
          Module.finrank k (Induced H ρ) = H.index * Module.finrank k V)


/-- The same decomposition expressed as the algebraic direct sum, with its
actual summand inclusion formula. -/
def directSumType : Prop := by
  classical
  exact ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V),
    ∃ D : InductionData H ρ,
      ∀ (T : Set G) (_hT : Subgroup.IsComplement T (H : Set G)),
        letI : DecidableEq T := Classical.decEq _
        letI := D.module
        ∃ L : (⨁ _ : T, V) ≃ₗ[k] Induced H ρ,
          ∀ (t : T) (z : V), L (DirectSum.lof k T (fun _ => V) t z) =
            tensor H ρ (MonoidAlgebra.single (t : G) 1) z

/-- Any two tensor-action constructions admit the induced intertwiner with its
actual elementary-tensor formula; no representative choice enters the map. -/
def tensorFunctorialityType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (σ : Representation k H W)
    (D : InductionData H ρ) (D' : InductionData H σ),
    letI := D.module
    letI := D'.module
    ∀ f : ρ.IntertwiningMap σ,
      ∃ F : D.representation.IntertwiningMap D'.representation,
        ∀ (a : k[G]) (z : V), F (tensor H ρ a z) = tensor H σ a (f z)

/-- The tensor/function comparison commutes with every H-intertwiner, for
all constructions with the specified generator formulas. -/
def modelNaturalityType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (σ : Representation k H W)
    (D : InductionData H ρ) (D' : InductionData H σ)
    (E : FunctionModelData H ρ D) (E' : FunctionModelData H σ D'),
    letI := D.module
    letI := D'.module
    ∀ (f : ρ.IntertwiningMap σ) (F : Induced H ρ →ₗ[k] Induced H σ),
      (∀ (a : k[G]) (z : V), F (tensor H ρ a z) = tensor H σ a (f z)) →
      ∀ (z : Induced H ρ) (x : G),
        (E'.equivalence (F z)).1 x = f ((E.equivalence z).1 x)


/-- Mathlib uses right multiplication by the inverse on coinvariant generators.
Inverting the basis coordinate gives an action- and balance-preserving bridge. -/
def mathlibBridgeType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V),
    ∃ D : InductionData H ρ,
      letI := D.module
      ∃ e : Induced H ρ ≃ₗ[k] Representation.IndV H.subtype ρ,
        (∀ (g : G) (z : V), e (tensor H ρ (MonoidAlgebra.single g 1) z) =
          Representation.IndV.mk H.subtype ρ g⁻¹ z) ∧
        (∀ (g : G) (z : V), e.symm (Representation.IndV.mk H.subtype ρ g z) =
          tensor H ρ (MonoidAlgebra.single g⁻¹ 1) z) ∧
        (∀ (g : G) (z : Induced H ρ), e (D.representation g z) =
          Representation.ind H.subtype ρ g (e z)) ∧
        (∀ (a : k[G]) (b : k[H]) (z : V),
          e (tensor H ρ (a * subgroupAlgebra H b) z) =
            e (tensor H ρ a (ρ.asAlgebraHom b z)))

end Specs
end P103.Ch09
