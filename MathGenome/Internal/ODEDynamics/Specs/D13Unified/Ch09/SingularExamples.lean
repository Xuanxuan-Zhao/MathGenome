import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.Indicial

/-! Independent statements for paper.tex, Example d13:09:singular-examples.
All logarithms and powers retain the freely supplied branch. The Bessel
normalization is the displayed product normalization, with no gamma factor. -/
noncomputable section
namespace Specs.D13Unified.Ch09.SingularExamples
open Specs.D13Unified.Ch09.Indicial
open scoped BigOperators

def eulerEquation (R : ℝ) (hR : 0 < R) (a b : ℂ) : Equation where
  radius := R
  radius_pos := hR
  p := fun _ => a
  q := fun _ => b
  p_holomorphic := differentiableOn_const a
  q_holomorphic := differentiableOn_const b

def besselEquation (R : ℝ) (hR : 0 < R) (ν : ℝ) : Equation where
  radius := R
  radius_pos := hR
  p := fun _ => 1
  q := fun z => z ^ 2 - (ν : ℂ) ^ 2
  p_holomorphic := differentiableOn_const 1
  q_holomorphic := (differentiableOn_id.pow 2).sub (differentiableOn_const _)

def besselCoefficient (ν : ℝ) (j : ℕ) : ℂ :=
  (-1) ^ j / ((4 : ℂ) ^ j * (j.factorial : ℂ) *
    ∏ k ∈ Finset.Icc 1 j, ((ν : ℂ) + (k : ℂ)))

def besselFactor (ν : ℝ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, besselCoefficient ν j * z ^ (2 * j)

def eulerDistinctType : Prop :=
  ∀ (R : ℝ) (hR : 0 < R) (a b : ℂ) (L : LogBranch R) (r₁ r₂ : ℂ),
    r₁ * (r₁ - 1) + a * r₁ + b = 0 →
    r₂ * (r₂ - 1) + a * r₂ + b = 0 → r₁ ≠ r₂ →
    solutionValue (eulerEquation R hR a b) L (powerValue L r₁) ∧
    solutionValue (eulerEquation R hR a b) L (powerValue L r₂) ∧
    independentValue L (powerValue L r₁) (powerValue L r₂)

/-- Vieta's identities express a repeated root, without choosing an ordering. -/
def eulerRepeatedType : Prop :=
  ∀ (R : ℝ) (hR : 0 < R) (a b r : ℂ) (L : LogBranch R),
    a = 1 - 2 * r → b = r ^ 2 →
    solutionValue (eulerEquation R hR a b) L (powerValue L r) ∧
    solutionValue (eulerEquation R hR a b) L (fun z => powerValue L r z * L.log z) ∧
    independentValue L (powerValue L r) (fun z => powerValue L r z * L.log z)

/-- Absolute convergence at every complex point and holomorphy everywhere
express the infinite convergence radius of the ordinary power-series factor. -/
def besselEntireType : Prop :=
  ∀ (ν : ℝ), 0 ≤ ν →
    (∀ z : ℂ, Summable (fun j : ℕ => ‖besselCoefficient ν j * z ^ (2 * j)‖)) ∧
    Differentiable ℂ (besselFactor ν) ∧ besselFactor ν 0 = 1

def besselSolutionType : Prop :=
  ∀ (ν : ℝ), 0 ≤ ν → ∀ (R : ℝ) (hR : 0 < R) (L : LogBranch R),
    solutionValue (besselEquation R hR ν) L
      (fun z => powerValue L (ν : ℂ) z * besselFactor ν z)
end Specs.D13Unified.Ch09.SingularExamples
