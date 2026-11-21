import MathGenome.Internal.Specs.D05.M13.SimultaneousSpectral.JointProjections
import Mathlib.LinearAlgebra.Lagrange

/-! Independent statements for the generated-algebra part of
K05.13.simultaneous_spectral, paper.tex:2294–2311. The family index is arbitrary.
The finite set below indexes exactly all nonzero intrinsic joint eigenspaces.
The algebra is unital over the original scalar field, including in dimension zero.
`Lagrange.basis univ a j` is the polynomial ∏ k ≠ j, (X-a k)/(a j-a k).
Real labels in the complex case are embedded by the canonical real embedding. -/
noncomputable section
open scoped BigOperators
namespace D05

/-- A scalar combination of the actual orthogonal joint-space projections. -/
def jointProjectionSum {F V ι : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : ι → Module.End F V) (s : Finset (ι → F)) (c : {χ // χ ∈ s} → F) :
    Module.End F V :=
  ∑ χ : {χ // χ ∈ s}, c χ • orthogonalProjection (jointEigenspace T χ.val)

/-- The full algebra conclusion for a given exhaustive joint-space index set. -/
def JointAlgebraOn {F V ι : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : ι → Module.End F V) (s : Finset (ι → F)) : Prop := by
  classical
  exact
   (∀ A : Module.End F V, A ∈ Algebra.adjoin F (Set.range T) ↔
    ∃ c, A = jointProjectionSum T s c) ∧
  (∀ c, LinearMap.adjoint (jointProjectionSum T s c) =
    jointProjectionSum T s (fun χ => star (c χ))) ∧
  (∀ A ∈ Algebra.adjoin F (Set.range T),
    LinearMap.adjoint A ∈ Algebra.adjoin F (Set.range T)) ∧
  (∀ t : {χ // χ ∈ s} → ℝ, Function.Injective t →
    let D := jointProjectionSum T s (fun χ => (t χ : F))
    selfAdjoint D ∧ Algebra.adjoin F {D} = Algebra.adjoin F (Set.range T) ∧
    ∀ j : {χ // χ ∈ s},
      Polynomial.aeval D (Lagrange.basis Finset.univ (fun χ => (t χ : F)) j) =
        orthogonalProjection (jointEigenspace T j.val))

/-- Existence is asserted from the original operator hypotheses, rather than
assuming the joint decomposition as an extra hypothesis. -/
def JointAlgebraConclusion {F V ι : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : ι → Module.End F V) : Prop := by
  classical
  exact ∃ s : Finset (ι → F),
    (∀ χ, χ ∈ s ↔ jointEigenspace T χ ≠ ⊥) ∧
    (∀ χ ∈ s, ∀ ψ ∈ s, χ ≠ ψ →
      jointEigenspace T χ ≤ (jointEigenspace T ψ).orthogonal) ∧
    DirectSum.IsInternal (fun χ : {χ // χ ∈ s} => jointEigenspace T χ.val) ∧
    JointAlgebraOn T s

end D05
namespace Specs.D05.M13.SimultaneousSpectral.JointAlgebra

def real_joint_algebra : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : ι → Module.End ℝ V),
    (∀ i, _root_.D05.selfAdjoint (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    _root_.D05.JointAlgebraConclusion T

def complex_joint_algebra : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : ι → Module.End ℂ V),
    (∀ i, _root_.D05.normalOperator (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    _root_.D05.JointAlgebraConclusion T

/-- Existence of a single self-adjoint generator, with no nonzero-space premise. -/
def real_single_generator : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : ι → Module.End ℝ V),
    (∀ i, _root_.D05.selfAdjoint (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    ∃ D : Module.End ℝ V, _root_.D05.selfAdjoint D ∧
      Algebra.adjoin ℝ {D} = Algebra.adjoin ℝ (Set.range T)

/-- The generator is self-adjoint even when the original members are only normal. -/
def complex_single_generator : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : ι → Module.End ℂ V),
    (∀ i, _root_.D05.normalOperator (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    ∃ D : Module.End ℂ V, _root_.D05.selfAdjoint D ∧
      Algebra.adjoin ℂ {D} = Algebra.adjoin ℂ (Set.range T)

/-- For an empty family the generated algebra consists of scalar identities,
and the zero map is a self-adjoint single generator. -/
def empty_family_algebra : Prop :=
  ∀ {F V ι : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [IsEmpty ι] (T : ι → Module.End F V),
    (∀ A : Module.End F V, A ∈ Algebra.adjoin F (Set.range T) ↔
      ∃ c : F, A = c • (1 : Module.End F V)) ∧
    _root_.D05.selfAdjoint (0 : Module.End F V) ∧
    Algebra.adjoin F {(0 : Module.End F V)} = Algebra.adjoin F (Set.range T)

/-- On the zero space the joint list is empty and the algebra has only zero. -/
def zero_space_algebra : Prop :=
  ∀ {F V ι : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [Subsingleton V] (T : ι → Module.End F V),
    (∀ χ, _root_.D05.jointEigenspace T χ = ⊥) ∧
    _root_.D05.JointAlgebraOn T ∅ ∧
    (∀ A : Module.End F V, A ∈ Algebra.adjoin F (Set.range T) ↔ A = 0) ∧
    _root_.D05.selfAdjoint (0 : Module.End F V) ∧
    Algebra.adjoin F {(0 : Module.End F V)} = Algebra.adjoin F (Set.range T)

end Specs.D05.M13.SimultaneousSpectral.JointAlgebra
