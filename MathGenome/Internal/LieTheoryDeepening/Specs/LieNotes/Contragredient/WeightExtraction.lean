import Mathlib.Algebra.DirectSum.Module
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace Specs.LieNotes.Contragredient.WeightExtraction

open scoped BigOperators

variable {H V ι : Type*} [AddCommGroup H] [Module ℂ H]
  [AddCommGroup V] [Module ℂ V]

set_option linter.checkUnivs false in
def WeightSpaceType :=
  ∀ {H V : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V],
    (H →ₗ[ℂ] Module.End ℂ V) → Module.Dual ℂ H → Submodule ℂ V

/-- The common eigenspace for the linear weight `μ`. -/
def weightSpace (ρ : H →ₗ[ℂ] Module.End ℂ V) (μ : Module.Dual ℂ H) : Submodule ℂ V where
  carrier := {v | ∀ h : H, ρ h v = μ h • v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy h
    exact (map_add (ρ h) x y).trans (by rw [hx h, hy h, smul_add])
  smul_mem' := by
    intro c x hx h
    exact (map_smul (ρ h) c x).trans (by rw [hx h, smul_comm])

def MemWeightSpace : Prop :=
  ∀ {H V : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    {ρ : H →ₗ[ℂ] Module.End ℂ V} {μ : Module.Dual ℂ H} {v : V},
    v ∈ weightSpace ρ μ ↔ ∀ h : H, ρ h v = μ h • v

def ExistsSeparatingElement : Prop :=
  ∀ {H ι : Type*} [AddCommGroup H] [Module ℂ H]
    (μ : ι → Module.Dual ℂ H) (s : Finset ι),
    Set.InjOn μ (s : Set ι) → ∃ h : H, Set.InjOn (fun i ↦ μ i h) (s : Set ι)

def MemOfWeightSumMem : Prop :=
  ∀ {H V ι : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    (ρ : H →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V),
    (∀ (h : H) ⦃v : V⦄, v ∈ W → ρ h v ∈ W) →
    ∀ (μ : ι → Module.Dual ℂ H) (s : Finset ι), Set.InjOn μ (s : Set ι) →
    ∀ v : ι → V, (∀ i ∈ s, v i ∈ weightSpace ρ (μ i)) →
      (∑ i ∈ s, v i) ∈ W → ∀ i ∈ s, v i ∈ W

def WeightSpaceISupIndep : Prop :=
  ∀ {H V : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    (ρ : H →ₗ[ℂ] Module.End ℂ V), iSupIndep (weightSpace ρ)

def ISupInfWeightSpaceEq : Prop :=
  ∀ {H V ι : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    (ρ : H →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V),
    (∀ (h : H) ⦃v : V⦄, v ∈ W → ρ h v ∈ W) →
    ∀ μ : ι → Module.Dual ℂ H, Function.Injective μ →
    (⨆ i, weightSpace ρ (μ i)) = ⊤ →
    (⨆ i, W ⊓ weightSpace ρ (μ i)) = W

open Classical in
def IsInternalWeightSpaceIntersections : Prop :=
  ∀ {H V ι : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup V] [Module ℂ V]
    (ρ : H →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V),
    (∀ (h : H) ⦃v : V⦄, v ∈ W → ρ h v ∈ W) →
    ∀ μ : ι → Module.Dual ℂ H, Function.Injective μ →
    (⨆ i, weightSpace ρ (μ i)) = ⊤ →
    DirectSum.IsInternal (fun i ↦ (weightSpace ρ (μ i)).comap W.subtype)

def SingleOperatorFamilyType :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V],
    Module.End ℂ V → ℂ →ₗ[ℂ] Module.End ℂ V

/-- The linear family `z ↦ z • T` associated with one operator. -/
def singleOperatorFamily (T : Module.End ℂ V) : ℂ →ₗ[ℂ] Module.End ℂ V :=
  LinearMap.toSpanSingleton ℂ (Module.End ℂ V) T

def WeightSpaceSingleOperatorFamily : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (μ : Module.Dual ℂ ℂ),
    weightSpace (singleOperatorFamily T) μ = T.eigenspace (μ 1)

end Specs.LieNotes.Contragredient.WeightExtraction
