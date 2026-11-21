import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.GrowthDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Exponential

/-! Independent statement of Theorem d13:18:linear-exponents.

`VectorAbscissa` uses an actual finite generalized-eigenspace decomposition of
coordinates. Its maximum includes exactly the nonzero components. This relational
form avoids choosing a real maximum of an empty set. Existence is part of the
conclusion for every nonzero vector. Real data are embedded coordinatewise in
ℂ before taking this decomposition. The norm is the arbitrary norm on the
realization E; matrix norms are its induced operator norms.

The positive-dimensional operator statement includes existence of the maximum.
In dimension zero the explicit convention is the upstream extended logarithm
of the zero operator norm, hence −∞. No diagonalizability is assumed.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch18.LinearExponents

/-- A finite decomposition in the actual maximal generalized eigenspaces. -/
def IsSpectralDecomposition {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (f : ℂ →₀ (n → ℂ)) : Prop :=
  (∀ μ, f μ ∈ Module.End.maxGenEigenspace (Matrix.toLinAlgEquiv' A) μ) ∧
    f.sum (fun _ w => w) = v

/-- Largest real part among the nonzero generalized-eigenspace components. -/
def VectorAbscissa {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (α : ℝ) : Prop :=
  ∃ f : ℂ →₀ (n → ℂ), IsSpectralDecomposition A v f ∧
    IsGreatest (Complex.re '' {μ | f μ ≠ 0}) α

/-- The largest real part of an eigenvalue, when such a maximum exists. -/
def OperatorAbscissa {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (α : ℝ) : Prop :=
  IsGreatest (Complex.re '' {μ | Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' A) μ}) α

end D13Unified.Ch18.LinearExponents

namespace Specs.D13Unified.Ch18.LinearExponents
open _root_.D13Unified.Ch18.LinearExponents
open _root_.D13Unified.Ch07
open Specs.D13Unified.Ch07.MatrixExponential (exponentialValue)
open Specs.D13Unified.Ch18.GrowthDefinitions (logarithmicRate)
universe u v

/-- All nonzero complex vectors, in any fixed finite-dimensional norm. -/
def complexDirectionalStatement : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (b : Module.Basis n ℂ E) (A : Matrix n n ℂ)
    (v : E), v ≠ 0 →
    (∃ α : ℝ, VectorAbscissa A (b.equivFun v) α) ∧
    ∀ α : ℝ, VectorAbscissa A (b.equivFun v) α →
      Tendsto (fun t : ℝ => Real.log ‖matrixOperatorEquiv b (exponentialValue A t) v‖ / t)
        atTop (𝓝 α)

/-- Real matrices use the same complex generalized-eigenspace decomposition. -/
def realDirectionalStatement : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (v : E), v ≠ 0 →
    (∃ α : ℝ, VectorAbscissa (A.map Complex.ofReal) (fun k => (b.equivFun v k : ℂ)) α) ∧
    ∀ α : ℝ, VectorAbscissa (A.map Complex.ofReal) (fun k => (b.equivFun v k : ℂ)) α →
      Tendsto (fun t : ℝ => Real.log ‖matrixOperatorEquiv b (exponentialValue A t) v‖ / t)
        atTop (𝓝 α)

def complexOperatorStatement : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (b : Module.Basis n ℂ E) (A : Matrix n n ℂ),
    (∃ α : ℝ, OperatorAbscissa A α) ∧
    ∀ α : ℝ, OperatorAbscissa A α →
      Tendsto (fun t : ℝ => Real.log (matrixOperatorNorm b (exponentialValue A t)) / t)
        atTop (𝓝 α)

def realOperatorStatement : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis n ℝ E) (A : Matrix n n ℝ),
    (∃ α : ℝ, OperatorAbscissa (A.map Complex.ofReal) α) ∧
    ∀ α : ℝ, OperatorAbscissa (A.map Complex.ofReal) α →
      Tendsto (fun t : ℝ => Real.log (matrixOperatorNorm b (exponentialValue A t)) / t)
        atTop (𝓝 α)

/-- The zero-dimensional convention retains log 0 = −∞, at all positive times. -/
def zeroDimensionalStatement : Prop :=
  ∀ {𝕂 : Type} [RCLike 𝕂] {n : Type u} [Fintype n] [DecidableEq n] [IsEmpty n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [FiniteDimensional 𝕂 E] (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂),
    (∀ t : ℝ, logarithmicRate t (matrixOperatorNorm b (exponentialValue A t)) = ⊥) ∧
    Tendsto (fun t : ℝ => logarithmicRate t (matrixOperatorNorm b (exponentialValue A t)))
      atTop (𝓝 ⊥)

end Specs.D13Unified.Ch18.LinearExponents
