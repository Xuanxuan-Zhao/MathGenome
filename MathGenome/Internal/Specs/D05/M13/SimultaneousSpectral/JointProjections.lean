import MathGenome.Internal.Specs.D05.M13.SimultaneousSpectral
import MathGenome.Internal.Specs.D05.M13.AlgebraicProjections
import MathGenome.Internal.Specs.D05.M12.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-! Independent interface for the joint-projection stage of
K05.13.simultaneous_spectral, paper.tex:2294–2311. The later algebra equality,
adjoint closure and single generator have separate ownership.
Joint spaces are intersections of actual eigenspaces, indexed by functions on
the whole family. No finite-family or positive-dimension premise is imposed. -/
noncomputable section
namespace D05

/-- The intrinsic joint eigenspace for an eigenvalue function on the whole family. -/
def jointEigenspace {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : ι → Module.End F V) (χ : ι → F) : Submodule F V :=
  ⨅ i, (T i).eigenspace (χ i)

/-- A finite intrinsic orthogonal decomposition together with literal products
of Lagrange projections. The list may contain repeated separating factors;
its empty product is the identity. Each listed polynomial uses the complete,
distinct spectrum of its selected family member. -/
def JointProjectionResolution {F V ι : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : ι → Module.End F V) : Prop :=
  by
    classical
    exact
      ∃ s : Finset (ι → F),
        (∀ χ, χ ∈ s ↔ jointEigenspace T χ ≠ ⊥) ∧
        (∀ χ ∈ s, ∀ ψ ∈ s, χ ≠ ψ →
          jointEigenspace T χ ≤ (jointEigenspace T ψ).orthogonal) ∧
        DirectSum.IsInternal (fun χ : {χ // χ ∈ s} => jointEigenspace T χ.val) ∧
        (∀ χ ∈ s, ∃ L : List (ι × Polynomial F),
          (∀ z ∈ L, ∃ (r : ℕ) (a : Fin r → F) (j : Fin r),
            Function.Injective a ∧
            (∀ μ, (T z.1).HasEigenvalue μ ↔ ∃ k, a k = μ) ∧
            a j = χ z.1 ∧
            z.2 = Specs.D05.M08.Interpolation.lagrangePolynomial_value F r a j) ∧
          (∀ ψ ∈ s, ψ ≠ χ → ∃ z ∈ L, χ z.1 ≠ ψ z.1) ∧
          (L.map (fun z => Polynomial.aeval (T z.1) z.2)).prod =
            orthogonalProjection (jointEigenspace T χ)) ∧
        (∀ χ ∈ s, orthogonalProjection (jointEigenspace T χ) ∈
          Algebra.adjoin F (Set.range T))

end D05
namespace Specs.D05.M13.SimultaneousSpectral.JointProjections

/-- Grouping any common basis by equality of whole eigenvalue functions
recovers exactly the intrinsic intersections. This also proves basis independence. -/
def basis_grouping : Prop :=
  ∀ {F V ι κ : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype κ] (T : ι → Module.End F V) (b : Module.Basis κ F V)
    (μ : ι → κ → F), (∀ i k, T i (b k) = μ i k • b k) → ∀ χ,
      _root_.D05.jointEigenspace T χ =
        Submodule.span F (b '' {k | (fun i => μ i k) = χ})

def real_joint_projections : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : ι → Module.End ℝ V),
    (∀ i, _root_.D05.selfAdjoint (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    _root_.D05.JointProjectionResolution T

def complex_joint_projections : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : ι → Module.End ℂ V),
    (∀ i, _root_.D05.normalOperator (T i)) →
    (∀ i j, (T i).comp (T j) = (T j).comp (T i)) →
    _root_.D05.JointProjectionResolution T

/-- An empty family on a nonzero space has precisely one eigenvalue function,
one nonzero joint space, namely V, and projection I. -/
def empty_family : Prop :=
  ∀ {F V ι : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [IsEmpty ι] [Nontrivial V] (T : ι → Module.End F V),
    (∃! χ : ι → F, _root_.D05.jointEigenspace T χ ≠ ⊥) ∧
    ∀ χ, _root_.D05.jointEigenspace T χ = ⊤ ∧
      _root_.D05.orthogonalProjection (_root_.D05.jointEigenspace T χ) = 1

/-- In the zero space there are no nonzero joint eigenspaces, for any family. -/
def zero_space : Prop :=
  ∀ {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Subsingleton V] (T : ι → Module.End F V),
    {χ : ι → F | _root_.D05.jointEigenspace T χ ≠ ⊥} = ∅

end Specs.D05.M13.SimultaneousSpectral.JointProjections
