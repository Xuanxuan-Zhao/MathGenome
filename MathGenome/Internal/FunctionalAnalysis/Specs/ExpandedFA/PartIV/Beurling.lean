import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BeurlingWandering

/-! Beurling's theorem, paper.tex:18805–18838, in the canonical coefficient
Hardy space. Products are specified by their actual analytic evaluations. -/
noncomputable section
namespace ExpandedFA.PartIV.BeurlingSpec
open HardyDiskSpec BeurlingWanderingSpec

/-- The analytic product subspace, expressed without assuming that products exist. -/
def ProductRange (θ : H2) : Set H2 :=
  {h | ∃ f : H2, ∀ z ∈ disk, eval h z = eval θ z * eval f z}

/-- Invariance under every bounded holomorphic function on the whole disk. -/
def MultiplierInvariant (M : Submodule ℂ H2) : Prop :=
  ∀ (b : HInfinity) (f : H2), f ∈ M → ∀ g : H2,
    (∀ z : Disk, eval g z = b.val z * eval f z) → g ∈ M

/-- Multiplication is a linear isometry, with its analytic product law and closed range. -/
def InnerIsometry : Prop := ∀ θ : H2, IsInner θ →
  ∃ T : H2 →ₗᵢ[ℂ] H2,
    (∀ (f : H2) (z : ℂ), z ∈ disk → eval (T f) z = eval θ z * eval f z) ∧
    Set.range T = ProductRange θ ∧ IsClosed (Set.range T)

/-- Full classification of nonzero closed shift-invariant subspaces. -/
def Classification : Prop := ∀ M : Submodule ℂ H2,
  IsClosed (M : Set H2) → M ≠ ⊥ → ShiftInvariant M →
  ∃ θ : H2, IsInner θ ∧ (M : Set H2) = ProductRange θ

/-- Any two inner generators of the same subspace differ by a unimodular scalar. -/
def Uniqueness : Prop := ∀ θ η : H2, IsInner θ → IsInner η →
  ProductRange θ = ProductRange η → ∃ c : ℂ, ‖c‖ = 1 ∧ η = c • θ

/-- Includes the zero subspace: closure is the only subspace hypothesis. -/
def MultiplierEquivalence : Prop := ∀ M : Submodule ℂ H2,
  IsClosed (M : Set H2) → (ShiftInvariant M ↔ MultiplierInvariant M)

end ExpandedFA.PartIV.BeurlingSpec
