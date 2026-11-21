import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Filter
open scoped Topology Asymptotics BigOperators

namespace P203Specs.Ch03

/-- The source's real harmonic sum, including the empty sum at zero. -/
noncomputable def harmonicNumber (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m, 1 / (j : ℝ)

/-- The constant shared by the harmonic limit and later average orders. -/
noncomputable def gamma : ℝ := Real.eulerMascheroniConstant

namespace HarmonicBasel

def HarmonicLibraryBridge : Prop :=
  ∀ m : ℕ, harmonicNumber m = (harmonic m : ℝ)

def GammaIdentification : Prop := gamma = Real.eulerMascheroniConstant

def HarmonicLimit : Prop :=
  Tendsto (fun m : ℕ => harmonicNumber m - Real.log (m : ℝ)) atTop (𝓝 gamma)

def HarmonicLimitExists : Prop :=
  ∃ c : ℝ, Tendsto (fun m : ℕ => harmonicNumber m - Real.log (m : ℝ)) atTop (𝓝 c)

/-- A quantitative estimate for every positive integer, stronger than the required O-term. -/
def HarmonicErrorBound : Prop :=
  ∀ m : ℕ, 0 < m →
    0 ≤ harmonicNumber m - Real.log (m : ℝ) - gamma ∧
    |harmonicNumber m - Real.log (m : ℝ) - gamma| ≤ 1 / (m : ℝ)

def HarmonicAsymptotic : Prop :=
  (fun m : ℕ => harmonicNumber m - (Real.log (m : ℝ) + gamma))
    =O[atTop] (fun m : ℕ => 1 / (m : ℝ))

/-- Index n corresponds to the positive integer n+1. -/
def BaselHasSum : Prop :=
  HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6)

def BaselSummable : Prop :=
  Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)

end HarmonicBasel
end P203Specs.Ch03
