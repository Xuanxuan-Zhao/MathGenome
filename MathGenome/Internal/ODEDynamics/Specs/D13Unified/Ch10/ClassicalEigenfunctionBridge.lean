import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.GreenOperator
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
open Set MeasureTheory
namespace Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge
open RegularProblem
open GreenWeakInverse
open _root_.D13Unified.Ch10.GreenKernel hiding Problem

/-- The classical eigenspace in H, including zero. Actual representatives
are unique on [a,b]; their values outside [a,b] carry no mathematical data. -/
def classicalEigenspace (P : Problem) (lam : ℂ) : Set (hilbertValue P) :=
  {f | f = 0 ∨ ∃ (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasureValue P)),
    classicalEigenfunctionValue P dirichletValue lam y ∧ toHilbertValue P y hy = f}

def Forward : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ (mu : ℝ), 0 < mu → ∀ f : hilbertValue P, f ≠ 0 →
  operatorValue P c f = (mu : ℂ) • f →
  ∃ (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasureValue P)),
    classicalEigenfunctionValue P dirichletValue ((mu⁻¹ - c : ℝ) : ℂ) y ∧
    toHilbertValue P y hy = f ∧
    ∀ (z : ℝ → ℂ) (hz : MemLp z 2 (weightedMeasureValue P)),
      ContinuousOn z (interval P) → toHilbertValue P z hz = f → EqOn z y (interval P)

def Converse : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ (lam : ℂ) (y : ℝ → ℂ), classicalEigenfunctionValue P dirichletValue lam y →
  ∀ hy : MemLp y 2 (weightedMeasureValue P),
    lam.im = 0 ∧ 0 < lam.re + c ∧
    toHilbertValue P y hy = (lam + (c : ℂ)) • operatorValue P c (toHilbertValue P y hy) ∧
    operatorValue P c (toHilbertValue P y hy) =
      (lam + (c : ℂ))⁻¹ • toHilbertValue P y hy

def Eigenspaces : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) → ∀ mu : ℝ, 0 < mu →
  classicalEigenspace P ((mu⁻¹ - c : ℝ) : ℂ) =
    {f | operatorValue P c f = (mu : ℂ) • f}

def Simplicity : Prop := ∀ (P : Problem) (lam : ℂ),
  (∃ y : ℝ → ℂ, classicalEigenfunctionValue P dirichletValue lam y) →
  ∃ v : hilbertValue P, v ≠ 0 ∧
    classicalEigenspace P lam = (ℂ ∙ v : Submodule ℂ (hilbertValue P)) ∧
    Module.finrank ℂ (ℂ ∙ v : Submodule ℂ (hilbertValue P)) = 1

def RealNormalized : Prop := ∀ (P : Problem) (lam : ℂ),
  (∃ y : ℝ → ℂ, classicalEigenfunctionValue P dirichletValue lam y) →
  ∃ (r : ℝ → ℝ) (hr : MemLp (fun x => (r x : ℂ)) 2 (weightedMeasureValue P)),
    classicalEigenfunctionValue P dirichletValue lam (fun x => (r x : ℂ)) ∧
    ‖toHilbertValue P (fun x => (r x : ℂ)) hr‖ = 1

end Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge
