import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Prufer
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Spectrum
import Mathlib.Data.Set.Card

/-! Independent statements for paper.tex, d13:10:oscillation.
The sequence uses a natural subscript `n` for the paper's subscript `n+1`.
The final count below also states the result with the paper's one-based `j`.
All eigenfunctions are classical representatives on the original [a,b].
No nodal, positivity, or angle condition is included in the sequence data. -/
noncomputable section
open Set Filter
namespace Specs.D13Unified.Ch10.Oscillation
open RegularProblem Prufer

def RealDirichletEigenfunction (P : Problem) (lam : ℝ) (y : ℝ → ℝ) : Prop :=
  classicalEigenfunctionValue P dirichletValue (lam : ℂ) (fun x => (y x : ℂ))

/-- An increasing, exhaustive regular Dirichlet sequence. Its existence is
supplied by the independent spectrum theorem, rather than assumed globally. -/
def IsDirichletSequence (P : Problem) (lam : ℕ → ℝ) : Prop :=
  StrictMono lam ∧ Tendsto lam atTop atTop ∧
  (∀ n, ∃ y : ℝ → ℝ, RealDirichletEigenfunction P (lam n) y) ∧
  ∀ mu : ℝ, (∃ y : ℝ → ℝ, RealDirichletEigenfunction P mu y) →
    ∃ n, mu = lam n

def SequenceExists : Prop := ∀ P : Problem, ∃ lam, IsDirichletSequence P lam

def PositiveFirst : Prop := ∀ (P : Problem) (lam : ℕ → ℝ),
  IsDirichletSequence P lam →
  ∃ y : ℝ → ℝ, RealDirichletEigenfunction P (lam 0) y ∧
    ∀ x ∈ Ioo P.a P.b, 0 < y x

def EndpointAngles : Prop := ∀ (P : Problem) (lam : ℕ → ℝ),
  IsDirichletSequence P lam →
  ∀ j : ℕ, 1 ≤ j → angle P (lam (j - 1)) P.b = (j : ℝ) * Real.pi

/-- Finiteness is explicit because `Set.ncard` alone is also zero for an
infinite set. Distinct zeros are counted, and both endpoints are excluded. -/
def OscillationCount : Prop := ∀ (P : Problem) (lam : ℕ → ℝ),
  IsDirichletSequence P lam → ∀ j : ℕ, 1 ≤ j → ∀ y : ℝ → ℝ,
  RealDirichletEigenfunction P (lam (j - 1)) y →
    {x ∈ Ioo P.a P.b | y x = 0}.Finite ∧
    {x ∈ Ioo P.a P.b | y x = 0}.ncard = j - 1

def TerminalStrictMono : Prop := ∀ P : Problem,
  StrictMono (fun mu => angle P mu P.b)

end Specs.D13Unified.Ch10.Oscillation
