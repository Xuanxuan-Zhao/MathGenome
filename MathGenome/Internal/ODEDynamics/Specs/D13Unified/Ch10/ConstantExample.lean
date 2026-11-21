import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Oscillation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Independent statements for paper.tex, d13:10:dirichlet-example.
Natural index n represents the paper's positive index j = n+1. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Specs.D13Unified.Ch10.ConstantExample
open RegularProblem

def problemValue (ell : ℝ) (hell : 0 < ell) : Problem where
  a := 0
  b := ell
  a_lt_b := hell
  p := fun _ => 1
  q := fun _ => 0
  w := fun _ => 1
  p_regular := contDiffOn_const
  q_continuous := continuousOn_const
  w_continuous := continuousOn_const
  p_positive := fun _ _ => zero_lt_one
  w_positive := fun _ _ => zero_lt_one

def eigenvalueValue (ell : ℝ) (n : ℕ) : ℝ := (((n : ℝ) + 1) * Real.pi / ell)^2

def eigenfunctionValue (ell : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (2 / ell) * Real.sin (((n : ℝ) + 1) * Real.pi * x / ell)

def problemType := (ell : ℝ) → 0 < ell → Problem
def eigenvalueType := ℝ → ℕ → ℝ
def eigenfunctionType := ℝ → ℕ → ℝ → ℝ

def ClassicalModes : Prop := ∀ (ell : ℝ) (hell : 0 < ell) (n : ℕ),
  classicalEigenfunctionValue (problemValue ell hell) dirichletValue
    (eigenvalueValue ell n : ℂ) (fun x => (eigenfunctionValue ell n x : ℂ))

def Endpoints : Prop := ∀ (ell : ℝ) (hell : 0 < ell) (n : ℕ),
  eigenfunctionValue ell n 0 = 0 ∧ eigenfunctionValue ell n ell = 0

def Zeros : Prop := ∀ (ell : ℝ) (hell : 0 < ell) (n : ℕ),
  {x ∈ Ioo 0 ell | eigenfunctionValue ell n x = 0}.Finite ∧
  {x ∈ Ioo 0 ell | eigenfunctionValue ell n x = 0}.ncard = n

/-- Exhaustiveness includes possible complex classical spectral parameters. -/
def AllEigenvalues : Prop := ∀ (ell : ℝ) (hell : 0 < ell) (z : ℂ),
  (∃ y, classicalEigenfunctionValue (problemValue ell hell) dirichletValue z y) ↔
    ∃ n : ℕ, z = (eigenvalueValue ell n : ℂ)

def DiscreteSequence : Prop := ∀ (ell : ℝ) (hell : 0 < ell),
  StrictMono (eigenvalueValue ell) ∧ Tendsto (eigenvalueValue ell) atTop atTop

/-- A basis of the actual weighted complex L² quotient with these precise,
normalized real representatives, plus the two expansion identities. -/
def CompleteOrthonormal : Prop := ∀ (ell : ℝ) (hell : 0 < ell),
  ∃ (hm : ∀ n, MemLp (fun x => (eigenfunctionValue ell n x : ℂ)) 2
      (weightedMeasureValue (problemValue ell hell)))
    (B : HilbertBasis ℕ ℂ (hilbertValue (problemValue ell hell))),
    (∀ n, B n = toHilbertValue (problemValue ell hell)
      (fun x => (eigenfunctionValue ell n x : ℂ)) (hm n)) ∧
    ∀ f : hilbertValue (problemValue ell hell),
      HasSum (fun n => paperInnerValue (problemValue ell hell) f (B n) • B n) f ∧
      HasSum (fun n => ‖paperInnerValue (problemValue ell hell) f (B n)‖ ^ 2) (‖f‖ ^ 2)

/-- Global classical IVP solutions; no sign restriction on the parameter.
Equality is equality of functions on the full real time domain. -/
def InitialValue : Prop := ∀ (lam s A B : ℝ),
  ∃! y : ℝ → ℝ, ContDiff ℝ 2 y ∧ y s = A ∧ deriv y s = B ∧
    ∀ t : ℝ, deriv (deriv y) t + lam * y t = 0

end Specs.D13Unified.Ch10.ConstantExample
