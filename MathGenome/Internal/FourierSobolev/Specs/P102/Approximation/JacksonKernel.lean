import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Independent definitions and full proposition types for the Jackson kernel
in the angular circle. The integral in `firstMomentStatement` uses the original
representative on [-π,π] and the probability normalization dv/(2π). -/
noncomputable section
open MeasureTheory Set
open scoped Real ComplexConjugate

namespace P102.Approximation.Jackson.Expected

abbrev AngularCircle := P102.Periodic.Expected.Circle (2 * Real.pi)
abbrev angularHaar := P102.Periodic.Expected.haar (2 * Real.pi)

def sumValue (m : ℕ) : C(AngularCircle, ℂ) :=
  ∑ k ∈ Finset.range m, P102.Periodic.Expected.mode (2 * Real.pi) (k : ℤ)

def rawValue (m : ℕ) : C(AngularCircle, ℝ) :=
  ⟨fun x => ‖sumValue m x‖ ^ 4, by fun_prop⟩

def massValue (m : ℕ) : ℝ := ∫ x, rawValue m x ∂angularHaar

def kernelValue (m : ℕ) : C(AngularCircle, ℝ) :=
  ⟨fun x => rawValue m x / massValue m, by fun_prop⟩

def sumType := ℕ → C(AngularCircle, ℂ)
def rawType := ℕ → C(AngularCircle, ℝ)
def massType := ℕ → ℝ
def kernelType := ℕ → C(AngularCircle, ℝ)

def massPositiveStatement : Prop := ∀ m : ℕ, 1 ≤ m → 0 < massValue m

def nonnegativeStatement : Prop := ∀ m : ℕ, 1 ≤ m → ∀ x, 0 ≤ kernelValue m x

def evenStatement : Prop := ∀ m : ℕ, 1 ≤ m → ∀ x, kernelValue m (-x) = kernelValue m x

def integralStatement : Prop := ∀ m : ℕ, 1 ≤ m →
  (∫ x, kernelValue m x ∂angularHaar) = 1

def degreeStatement : Prop := ∀ m : ℕ, 1 ≤ m →
  kernelValue m ∈ P102.Periodic.Expected.realTrigDegree (2 * Real.pi) (2 * m - 2)

def firstMomentStatement : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
  (2 * Real.pi)⁻¹ * (∫ v in -Real.pi..Real.pi,
    |v| * kernelValue m (v : AngularCircle)) ≤ C / (m : ℝ)

end P102.Approximation.Jackson.Expected
