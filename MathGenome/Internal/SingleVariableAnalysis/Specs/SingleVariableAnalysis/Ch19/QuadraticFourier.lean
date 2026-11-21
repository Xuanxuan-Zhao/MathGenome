import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.C1Uniform

/-! K03.19.examples, paper.tex:5044–5054. The actual continuous periodic
extension, proper Darboux Fourier coefficients, positive frequencies n=k+1,
pointwise equality including both endpoints, and uniform absolute convergence.
The fourth-power Parseval application is a separate allocated obligation. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.QuadraticFourier
open Set PeriodicSetup Representation
open scoped BigOperators

def quadraticValue (x : ℝ) : ℝ :=
  (C1Uniform.periodicExtensionValue (fun t => ((t ^ 2 : ℝ) : ℂ)) x).re
abbrev quadraticType := ℝ → ℝ

def termValue (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (k+1) * Real.cos (((k+1 : ℕ) : ℝ) * x) / ((k+1 : ℕ) : ℝ) ^ 2

def partialValue (N : ℕ) (x : ℝ) : ℝ :=
  Real.pi ^ 2 / 3 + 4 * ∑ k ∈ Finset.range N, termValue k x

def extensionProperties : Prop :=
  Continuous quadraticValue ∧ Function.Periodic quadraticValue (2 * Real.pi) ∧
  EqOn quadraticValue (fun x => x ^ 2) (Icc (-Real.pi) Real.pi)

def integrability : Prop := periodicRealValue quadraticValue ∧
  CosineWeights quadraticValue ∧ SineWeights quadraticValue

def coefficients : Prop :=
  ∀ (h : Ch08.Integral.realIntegrableValue quadraticValue (-Real.pi) Real.pi)
    (ha : CosineWeights quadraticValue) (hb : SineWeights quadraticValue),
  aZeroValue quadraticValue h / 2 = Real.pi ^ 2 / 3 ∧
  ∀ n : ℕ+, sineCoefficientValue quadraticValue n (hb n) = 0 ∧
    cosineCoefficientValue quadraticValue n (ha n) = 4 * (-1 : ℝ) ^ (n : ℕ) / (n : ℝ) ^ 2

def uniformExpansion : Prop :=
  Ch12.Uniform.realUniformConvergesValue partialValue quadraticValue

def absoluteConvergence : Prop :=
  (∀ x : ℝ, Summable (fun k => |termValue k x|)) ∧
  TendstoUniformly (fun N x => ∑ k ∈ Finset.range N, |termValue k x|)
    (fun x => ∑' k, |termValue k x|) Filter.atTop

def seriesIdentity : Prop := ∀ x ∈ Icc (-Real.pi) Real.pi,
  HasSum (fun k => termValue k x) ((x ^ 2 - Real.pi ^ 2 / 3) / 4)

def baselSum : Prop :=
  HasSum (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ) ^ 2)) (Real.pi ^ 2 / 6)

end Specs.SingleVariableAnalysis.Ch19.QuadraticFourier
