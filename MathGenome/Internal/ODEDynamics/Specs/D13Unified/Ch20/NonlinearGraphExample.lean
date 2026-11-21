import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Independent specification of paper.tex, Example d13:20:example-graph.
The plane is ℝ × ℝ; its product norm is an equivalent finite-dimensional norm.
All time variables are real. The decay sets use the complete original equation,
not a cutoff extension. -/
noncomputable section
open Set Filter Topology
namespace Specs.D13Unified.Ch20.NonlinearGraphExample
open _root_.D13Unified

/-- The original polynomial vector field on the entire plane. -/
def fieldValue (p : ℝ × ℝ) : ℝ × ℝ := (-p.1 + p.2 ^ 2, p.2)

def odeValue : ODE (ℝ × ℝ) where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => fieldValue p.val.2
  continuous_field := by unfold fieldValue; fun_prop

/-- The explicit orbit through p at time zero. -/
def orbitValue (p : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (Real.exp (-t) * (p.1 - p.2 ^ 2 / 3) + (p.2 ^ 2 / 3) * Real.exp (2*t),
   p.2 * Real.exp t)

def unstableParam (y : ℝ) : ℝ × ℝ := (y^2/3, y)

def fieldType := (ℝ × ℝ) → ℝ × ℝ
def orbitType := (ℝ × ℝ) → ℝ → ℝ × ℝ

def exactSolutionExpected : Prop :=
  ∀ p, orbitValue p 0 = p ∧ ContDiff ℝ 1 (orbitValue p) ∧
    ∀ t, HasDerivAt (orbitValue p) (fieldValue (orbitValue p t)) t

/-- Every classical solution on any open interval containing zero has the
stated formula throughout that actual interval. -/
def allSolutionsExpected : Prop :=
  ∀ (I : OpenTimeInterval) (z : ℝ → ℝ × ℝ) (p : ℝ × ℝ),
    0 ∈ I.carrier → z 0 = p →
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue odeValue I z →
    ∀ t ∈ I.carrier, z t = orbitValue p t

/-- Complete classical IVP, with the actual domain equal to all real time. -/
def globalIVPExpected : Prop :=
  ∀ p, Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue odeValue
    ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩ (orbitValue p) 0 p

def stableSetExpected : Prop :=
  {p : ℝ × ℝ | Tendsto (orbitValue p) atTop (𝓝 0)} = {p | p.2 = 0}

def unstableSetExpected : Prop :=
  {p : ℝ × ℝ | Tendsto (orbitValue p) atBot (𝓝 0)} = {p | p.1 = p.2^2/3}

/-- Both graphs are invariant for every real time, so in particular in their
respective forward and backward time directions. -/
def invarianceExpected : Prop :=
  (∀ p t, p.2 = 0 → (orbitValue p t).2 = 0) ∧
  (∀ p t, p.1 = p.2^2/3 → (orbitValue p t).1 = (orbitValue p t).2^2/3) ∧
  (∀ y t, orbitValue (unstableParam y) t = unstableParam (y * Real.exp t))

/-- Smooth parametrization tangent to the vertical (unstable) axis, together
with its invariance equation and a point distinguishing the graph from the axis. -/
def geometryExpected : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) unstableParam ∧ unstableParam 0 = 0 ∧
  HasDerivAt unstableParam (0, 1) 0 ∧
  (∀ y, HasDerivAt unstableParam (2*y/3, 1) y ∧
    fieldValue (unstableParam y) = y • (2*y/3, 1)) ∧
  {p : ℝ × ℝ | p.1 = p.2^2/3} ≠ {p | p.1 = 0}

/-- The derivative at the equilibrium is diag(-1,1); this identifies the
horizontal and vertical axes as the stable and unstable linear directions. -/
def linearizationExpected : Prop :=
  ∀ v : ℝ × ℝ, fderiv ℝ fieldValue 0 v = (-v.1, v.2)

end Specs.D13Unified.Ch20.NonlinearGraphExample
