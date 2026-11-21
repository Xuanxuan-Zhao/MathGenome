import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero

/-!
Independent statements for the norm, completeness, and density assertions of
paper.tex:5486–5494. All spaces below are the canonical native spaces from the
definition interface. No measure or countability hypothesis is involved.
-/

namespace Specs.D11.Ch19.CzeroBanachDensity

universe u v

/-- The canonical inclusion of compactly supported maps into maps vanishing at infinity. -/
def ccInclusionType :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜],
    CompactlySupportedContinuousMap X 𝕜 →ₗ[𝕜] ZeroAtInftyContinuousMap X 𝕜

def ccInclusionValue : ccInclusionType.{u, v} := fun X _ 𝕜 _ =>
  { toFun := fun f => ⟨f.toContinuousMap, zero_at_infty f⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The compact-support subspace inside the same native C0 space. -/
def ccSubspaceType :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜],
    Submodule 𝕜 (ZeroAtInftyContinuousMap X 𝕜)

def ccSubspaceValue : ccSubspaceType.{u, v} :=
  fun X _ 𝕜 _ => LinearMap.range (ccInclusionValue X 𝕜)

def czero_bounded : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : ZeroAtInftyContinuousMap X 𝕜), ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C

/-- This infimum of nonnegative bounds defines the uniform norm also on the empty space. -/
def czero_norm_eq : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : ZeroAtInftyContinuousMap X 𝕜),
    ‖f‖ = sInf {C : ℝ | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C}

def czero_norm_le_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : ZeroAtInftyContinuousMap X 𝕜) (C : ℝ), 0 ≤ C →
    (‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C)

/-- Native scalar operations are the usual pointwise ones; the native norm is a scalar norm. -/
def czero_scalar_operations : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f g : ZeroAtInftyContinuousMap X 𝕜) (a : 𝕜),
    (∀ x, (0 : ZeroAtInftyContinuousMap X 𝕜) x = 0) ∧
    (∀ x, (f + g) x = f x + g x) ∧
    (∀ x, (a • f) x = a * f x) ∧ ‖a • f‖ = ‖a‖ * ‖f‖

/-- Completeness for the same native uniform norm and metric. -/
def czero_complete : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜],
    CompleteSpace (ZeroAtInftyContinuousMap X 𝕜)

def cc_inclusion_apply : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (g : CompactlySupportedContinuousMap X 𝕜) (x : X),
    ccInclusionValue X 𝕜 g x = g x

def cc_inclusion_injective : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜],
    Function.Injective (ccInclusionValue X 𝕜)

/-- The image is exactly the compactly supported functions, with the closed-support convention. -/
def cc_subspace_mem_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜]
    (f : ZeroAtInftyContinuousMap X 𝕜),
    f ∈ ccSubspaceValue X 𝕜 ↔ IsCompact (closure {x | f x ≠ 0})

def cc_uniform_approximation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (𝕜 : Type v) [RCLike 𝕜] (f : ZeroAtInftyContinuousMap X 𝕜)
    (ε : ℝ), 0 < ε →
    ∃ g : CompactlySupportedContinuousMap X 𝕜, ‖f - ccInclusionValue X 𝕜 g‖ ≤ ε

def cc_denseRange : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (𝕜 : Type v) [RCLike 𝕜], DenseRange (ccInclusionValue X 𝕜)

end Specs.D11.Ch19.CzeroBanachDensity
