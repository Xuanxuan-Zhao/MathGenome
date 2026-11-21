import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryIntegral

/-! Independent statements for the compact-support part of
`d11:23:dini-elementary-examples`, paper.tex:6314–6321.
The subspace below is the image of the canonical native Cc space in actual
functions. The explicit linear equivalence keeps the two interfaces identified.
No unit, countability, or nonemptiness assumption is made. -/

universe u
open Filter Topology

namespace D11.Ch23.Specs

/-- The canonical Cc functions, viewed as a subspace of actual finite functions. -/
def ccFunctions (X : Type u) [TopologicalSpace X] : Submodule ℝ (X → ℝ) where
  carrier := {f | Continuous f ∧ HasCompactSupport f}
  zero_mem' := ⟨continuous_const, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun _ _ hf => ⟨continuous_const.smul hf.1, hf.2.smul_left⟩

/-- Identification with the native Cc type, preserving every pointwise value. -/
def ccFunctionsEquiv (X : Type u) [TopologicalSpace X] :
    CompactlySupportedContinuousMap X ℝ ≃ₗ[ℝ] ccFunctions X where
  toFun f := ⟨f, f.continuous, f.hasCompactSupport⟩
  invFun f := ⟨⟨f.val, f.property.1⟩, f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def CcFunctionsType := ∀ (X : Type u) [TopologicalSpace X], Submodule ℝ (X → ℝ)

def CcFunctionsEquivType := ∀ (X : Type u) [TopologicalSpace X],
  CompactlySupportedContinuousMap X ℝ ≃ₗ[ℝ] ccFunctions X

def CcFunctionsStone : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X],
    IsVectorLattice (ccFunctions X) ∧ IsStone (ccFunctions X)

/-- The order-continuity conclusion on the native Cc type itself. -/
def CcPositiveOrderContinuous : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (L : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ),
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f) →
    ∀ f : ℕ → CompactlySupportedContinuousMap X ℝ,
      (∀ x, Antitone (fun n => f n x)) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 0)) →
      Tendsto (fun n => L (f n)) atTop (𝓝 0)

/-- The same assertion in the shared elementary-integral interface. -/
def CcPositiveElementary : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (L : ccFunctions X →ₗ[ℝ] ℝ),
    (∀ f, (∀ x, 0 ≤ f.val x) → 0 ≤ L f) →
    IsElementaryIntegral (ccFunctions X) L

end D11.Ch23.Specs
