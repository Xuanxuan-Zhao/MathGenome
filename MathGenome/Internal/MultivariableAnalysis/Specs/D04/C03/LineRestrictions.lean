import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Independent statement of d04:03:line-restriction. The existence predicate
is pointwise iterated total differentiability, with no continuity of the top
derivative. Ambient functions represent the local extensions at endpoints.
All results allow zero-dimensional spaces and zero increments. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C03.LineRestrictions
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model


def lineRestriction_iteratedDerivType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (j : ℕ) (U : Set X) (f : X → Y) (a h : X) (t : ℝ),
    TimesDifferentiableAt j U f (a + t • h) →
    iteratedDeriv j (fun s : ℝ => f (a + s • h)) t =
      differentialDiagonal (higherDifferential j f (a + t • h)) h

def lineRestriction_hasDerivAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (j : ℕ) (U : Set X) (f : X → Y) (a h : X) (t : ℝ),
    TimesDifferentiableAt (j+1) U f (a + t • h) →
    HasDerivAt (iteratedDeriv j (fun s : ℝ => f (a + s • h)))
      (differentialDiagonal (higherDifferential (j+1) f (a + t • h)) h) t

/-- All indicated orders on the closed segment, including endpoints interpreted
using the given local ambient extensions. Order zero asserts the value identity. -/
def lineRestriction_segmentType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (U : Set X) (f : X → Y) (a h : X),
    (∀ t ∈ Icc (0 : ℝ) 1, TimesDifferentiableAt k U f (a + t • h)) →
    ∀ j ≤ k, ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDeriv j (fun s : ℝ => f (a + s • h)) t =
        differentialDiagonal (higherDifferential j f (a + t • h)) h

/-- The full differential of T[x^(j+1)]/(j+1)!, as a continuous linear map. -/
def homogeneousTerm_hasFDerivAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (j : ℕ) (T : Differential X Y (j+1)),
    (∀ (σ : Equiv.Perm (Fin (j+1))) (v : Fin (j+1) → X), T (v ∘ σ) = T v) →
    ∀ x : X, HasFDerivAt
      (fun y : X => (((j+1).factorial : ℝ)⁻¹) • differentialDiagonal T y)
      (((j.factorial : ℝ)⁻¹) • T.toContinuousLinearMap (fun _ => x) 0) x

/-- Explicit application of the total derivative: Dp(x)v = T[v,x^j]/j!. -/
def homogeneousTerm_totalDerivative_applyType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (j : ℕ) (T : Differential X Y (j+1)),
    (∀ (σ : Equiv.Perm (Fin (j+1))) (v : Fin (j+1) → X), T (v ∘ σ) = T v) →
    ∀ x v : X,
      totalDerivative
        (fun y : X => (((j+1).factorial : ℝ)⁻¹) • differentialDiagonal T y) x v =
      ((j.factorial : ℝ)⁻¹) • T (Fin.cons v (fun _ => x))

/-- The order-zero term is constant, and its differential is zero. -/
def homogeneousTerm_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (T : Differential X Y 0) (x : X),
    (((Nat.factorial 0 : ℝ)⁻¹) • differentialDiagonal T x =
      T (fun i => Fin.elim0 i)) ∧
    HasFDerivAt (fun y : X => (((Nat.factorial 0 : ℝ)⁻¹) • differentialDiagonal T y))
      (0 : X →L[ℝ] Y) x

end Specs.D04.C03.LineRestrictions
