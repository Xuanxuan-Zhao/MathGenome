import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open scoped Matrix.Norms.Operator ContDiff
open Filter

namespace Specs.D13Unified.Ch07.ExponentialCalculus

universe u v w

open Specs.D13Unified.Ch07.MatrixExponential (exponentialValue)

/-- Locally uniform convergence of the actual defining partial sums, with real time.
The auxiliary coordinate norm induces the finite-dimensional matrix topology. -/
def locallyUniformType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂),
    TendstoLocallyUniformly
      (fun N : ℕ => fun t : ℝ =>
        ∑ j ∈ Finset.range N, (t ^ j / (Nat.factorial j : ℝ)) • A ^ j)
      (exponentialValue A) atTop

/-- Smoothness with respect to real time, also for complex matrices. -/
def smoothType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂), ContDiff ℝ ∞ (exponentialValue A)

def derivativeLeftType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (t : ℝ),
    HasDerivAt (exponentialValue A) (A * exponentialValue A t) t

def derivativeRightType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (t : ℝ),
    HasDerivAt (exponentialValue A) (exponentialValue A t * A) t

def zeroType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂), exponentialValue A 0 = 1

/-- The coefficient-one bound for the induced operator norm of any fixed state norm.
There is no nonzero-dimension or special choice of vector norm hypothesis. -/
def normType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
    (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (t : ℝ),
    D13Unified.Ch07.matrixOperatorNorm b (exponentialValue A t) ≤
      Real.exp (|t| * D13Unified.Ch07.matrixOperatorNorm b A)

def addTimeType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (s t : ℝ),
    exponentialValue A (s + t) = exponentialValue A s * exponentialValue A t

def inverseType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (t : ℝ), (exponentialValue A t)⁻¹ = exponentialValue A (-t)

/-- The commuting hypothesis is retained. -/
def commutingSumType : Prop :=
  ∀ {𝕂 : Type u} {n : Type v} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A B : Matrix n n 𝕂), A * B = B * A →
    exponentialValue (A + B) 1 = exponentialValue A 1 * exponentialValue B 1

end Specs.D13Unified.Ch07.ExponentialCalculus
