import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Group.Submonoid.Defs

/-! LA-E09 (highest-root part), source lines 2448–2479.
The roots are the weights of the actual adjoint module. A positive system is
specified by a real linear functional on the complex dual, nonzero on every
root. On the real root span this is exactly the regular-vector convention
`(v, α) > 0`. The simple roots are the indecomposable positive roots.
The positive root monoid consists of finite sums of simple roots. Membership
of `θ - β` expresses the source's simple-root order for roots of either sign.
Simplicity includes nonabelianness; nontriviality is stated explicitly.
-/

universe u v
namespace LieAlgebrasAndRepresentations.HighestRoot
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The chosen positive system of adjoint roots. -/
def positiveRoots (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) : Set (Module.Dual ℂ H) :=
  {α | α ∈ rootSet_value H ∧ 0 < φ α}

/-- Simple roots for the chosen positive system. -/
def simpleRoots (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) : Set (Module.Dual ℂ H) :=
  {α | α ∈ positiveRoots H φ ∧ ∀ β ∈ positiveRoots H φ,
    ∀ γ ∈ positiveRoots H φ, α ≠ β + γ}

/-- The monoid Q₊ of nonnegative integral combinations of simple roots. -/
def positiveRootMonoid (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) : AddSubmonoid (Module.Dual ℂ H) :=
  AddSubmonoid.closure (simpleRoots H φ)

end LieAlgebrasAndRepresentations.HighestRoot
namespace Specs.LieAlgebrasAndRepresentations.HighestRoot
open RootDecomposition
open _root_.LieAlgebrasAndRepresentations.HighestRoot

/-- The unique highest root dominates every root of the adjoint module. -/
def highest_root_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [Nontrivial L] [LieAlgebra.IsSimple ℂ L],
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Module.Dual ℝ (Module.Dual ℂ H)),
      (∀ α ∈ rootSet_value H, φ α ≠ 0) →
      ∃! θ : Module.Dual ℂ H, θ ∈ positiveRoots H φ ∧
        ∀ β ∈ rootSet_value H, θ - β ∈ positiveRootMonoid H φ

/-- The source's regular-vector formulation on a Euclidean model of the
real root space. The embedding identifies its roots with the adjoint roots. -/
def highest_root_regular_vector_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [Nontrivial L] [LieAlgebra.IsSimple ℂ L],
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (j : E →ₗ[ℝ] Module.Dual ℂ H), Function.Injective j →
      rootSet_value H ⊆ Set.range j →
      let R : Set E := j ⁻¹' rootSet_value H
      ∀ w : E, _root_.LieAlgebrasAndRepresentations.RootRegular R w →
        ∃! θ : E, θ ∈ _root_.LieAlgebrasAndRepresentations.positiveRoots R w ∧
          ∀ β ∈ R, θ - β ∈
            AddSubmonoid.closure (_root_.LieAlgebrasAndRepresentations.simpleRoots R w)

end Specs.LieAlgebrasAndRepresentations.HighestRoot
