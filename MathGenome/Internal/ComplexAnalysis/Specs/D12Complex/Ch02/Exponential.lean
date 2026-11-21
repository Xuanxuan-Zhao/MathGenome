import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Independent statements for the exponential part of paper.tex:367–424,
D12.02.03. The real functions in the polar formula are Mathlib's `Real.exp`,
`Real.cos`, and `Real.sin`. The other elementary functions are allocated to
the separate Trigonometric goal.
-/

noncomputable section

namespace D12Complex

/-- The exponential constructed as the sum of the scalar factorial series. -/
def E (z : ℂ) : ℂ := ∑' n : ℕ, z ^ n / (Nat.factorial n : ℂ)

end D12Complex

namespace Specs.D12Complex.Ch02.Exponential

open _root_.D12Complex

def E_type := ℂ → ℂ

def E_value : E_type := fun z => ∑' n : ℕ, z ^ n / (Nat.factorial n : ℂ)

/-- Explicit identification of the constructed series with the canonical exponential. -/
def E_eq_exp_type : Prop := E = Complex.exp

/-- The defining series actually converges to E at every complex argument. -/
def hasSum_E_type : Prop :=
  ∀ z : ℂ, HasSum (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) (E z)

def summable_norm_E_type : Prop :=
  ∀ z : ℂ, Summable (fun n : ℕ => ‖z ^ n / (Nat.factorial n : ℂ)‖)

/-- Entire means weak holomorphy on the whole plane, using the shared predicate. -/
def holomorphicOn_E_type : Prop := HolomorphicOn Set.univ E

def hasDerivAt_E_type : Prop := ∀ z : ℂ, HasDerivAt E (E z) z

/-- The derivative also satisfies the original punctured increment definition. -/
def hasComplexDerivativeAt_E_type : Prop :=
  ∀ z : ℂ, HasComplexDerivativeAt E (E z) z

def deriv_E_type : Prop := deriv E = E

def E_add_type : Prop := ∀ z w : ℂ, E (z + w) = E z * E w

def E_zero_type : Prop := E 0 = 1

def E_ne_zero_type : Prop := ∀ z : ℂ, E z ≠ 0

def E_ofReal_type : Prop := ∀ x : ℝ, E (x : ℂ) = (Real.exp x : ℂ)

def E_polar_type : Prop :=
  ∀ x y : ℝ, E ((x : ℂ) + Complex.I * (y : ℂ)) =
    (Real.exp x : ℂ) * ((Real.cos y : ℂ) + Complex.I * (Real.sin y : ℂ))

def E_eq_E_iff_type : Prop :=
  ∀ z w : ℂ, E z = E w ↔
    ∃ k : ℤ, z - w = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ)

end Specs.D12Complex.Ch02.Exponential
