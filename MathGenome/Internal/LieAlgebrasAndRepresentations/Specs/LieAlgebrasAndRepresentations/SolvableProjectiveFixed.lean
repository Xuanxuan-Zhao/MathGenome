import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LinearJordan
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Constructions

/-!
Independent draft for LA-solvable-projective-fixed, source lines 2953–2981.
The topology is the usual quotient topology from nonzero vectors. The norm
on the finite-dimensional complex space only presents its usual topology.
No inner product, algebraicity, nonzero dimension, faithfulness, or
irreducibility is assumed. A fixed projective point means an invariant line,
not a vector annihilated by the representation.
-/

universe u v

namespace LieAlgebrasAndRepresentations.SolvableProjectiveFixed

open scoped LinearAlgebra.Projectivization

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The standard quotient topology on complex projective space. -/
instance projectiveTopology : TopologicalSpace (ℙ ℂ V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ V)))

variable [FiniteDimensional ℂ V]

/-- The actual exponential of `z A`, in the Banach algebra of continuous operators. -/
noncomputable def exponential (A : Module.End ℂ V) (z : ℂ) : V →L[ℂ] V :=
  NormedSpace.exp (z • (LinearMap.toContinuousLinearMap A))

/-- Invertibility is proved from the two opposite exponential series. -/
theorem exponential_injective (A : Module.End ℂ V) (z : ℂ) :
    Function.Injective (exponential A z) := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  have h : exponential A (-z) * exponential A z = 1 := by
    unfold exponential
    rw [neg_smul, ← NormedSpace.exp_add_of_commute (Commute.refl (z • (LinearMap.toContinuousLinearMap A))).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  intro x y hxy
  have h' := congrArg (fun T : V →L[ℂ] V => T x) h
  have h'' := congrArg (fun T : V →L[ℂ] V => T y) h
  change exponential A (-z) (exponential A z x) = x at h'
  change exponential A (-z) (exponential A z y) = y at h''
  rw [← h', ← h'', hxy]

/-- The projective transformation induced by `exp(z A)`. -/
noncomputable def projectiveFlow (A : Module.End ℂ V) (z : ℂ) : ℙ ℂ V → ℙ ℂ V :=
  Projectivization.map (exponential A z).toLinearMap (exponential_injective A z)

/-- Infinitesimal fixation of a projective point by one operator. -/
def IsEigenline (A : Module.End ℂ V) (p : ℙ ℂ V) : Prop :=
  ∀ v ∈ p.submodule, A v ∈ p.submodule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- Every represented operator preserves this projective line. -/
def IsFixed (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (p : ℙ ℂ V) : Prop :=
  ∀ x, IsEigenline (ρ x) p

/-- Invariance under every complex one-parameter exponential, as in the source. -/
def IsInvariant (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (X : Set (ℙ ℂ V)) : Prop :=
  ∀ x z p, p ∈ X → projectiveFlow (ρ x) z p ∈ X

end LieAlgebrasAndRepresentations.SolvableProjectiveFixed

namespace Specs.LieAlgebrasAndRepresentations.SolvableProjectiveFixed

open _root_.LieAlgebrasAndRepresentations.SolvableProjectiveFixed
open scoped LinearAlgebra.Projectivization Topology
open Filter

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Required conclusion: a fixed projective point lying in the specified compact set. -/
def solvable_projective_fixed_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra.IsSolvable L]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (X : Set (ℙ ℂ V)),
    X.Nonempty → IsCompact X → IsInvariant ρ X → ∃ p ∈ X, IsFixed ρ p

/-- A vector-level form of the source's spectral/Jordan limit. The scalar `c`
rotates the finitely many distinct eigenvalues; the integer `m` absorbs any
Jordan block length and any multiplicity. The limit is nonzero. This statement
has no simple-spectrum or single-Jordan-block hypothesis. -/
def spectral_jordan_limit_type : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (v : V), v ≠ 0 →
    ∃ (c μ : ℂ) (m : ℕ) (w : V), c ≠ 0 ∧ w ≠ 0 ∧ A w = μ • w ∧
      Tendsto (fun t : ℝ =>
        (Complex.exp (-(t : ℂ) * c * μ) / (t : ℂ) ^ m) •
          exponential A ((t : ℂ) * c) v) atTop (𝓝 w)

end Specs.LieAlgebrasAndRepresentations.SolvableProjectiveFixed
