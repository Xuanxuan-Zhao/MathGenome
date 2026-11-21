import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-! Independent specification of K03.12.integral_failure, paper.tex:1327–1333.
The formula extends the stated function outside [0,1]; only its restriction
is asserted. The sequence uses n+2 so that its terms are exactly the source's
terms with integer index at least 2. All integral values are proper Darboux
integrals and explicitly require integrability. -/
namespace Specs.SingleVariableAnalysis.Ch12.IntegralFailure

abbrev triangleType := ℕ → ℝ → ℝ
noncomputable def triangleValue : triangleType := fun n x =>
  if x ≤ 1 / (n : ℝ) then (n : ℝ)^2 * x
  else if x ≤ 2 / (n : ℝ) then (n : ℝ) * (2 - (n : ℝ) * x) else 0

def triangleContinuous : Prop :=
  ∀ n : ℕ, 2 ≤ n → ContinuousOn (triangleValue n) (Set.Icc 0 1)

def zeroContinuous : Prop := ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 1)

def trianglePointwise : Prop :=
  Pointwise.realPointwiseConvergesValue
    (fun n (x : Set.Icc (0 : ℝ) 1) => triangleValue (n+2) x) (fun _ => 0)

def triangleIntegral : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ h : Ch08.Integral.realIntegrableValue (triangleValue n) 0 1,
    Ch08.Integral.realIntegralValue (triangleValue n) h = 1

def zeroIntegral : Prop :=
  ∃ h : Ch08.Integral.realIntegrableValue (fun _ => 0) 0 1,
    Ch08.Integral.realIntegralValue (fun _ => 0) h = 0

def trianglePeak : Prop :=
  ∀ n : ℕ, 2 ≤ n → 1 / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
    triangleValue n (1 / (n : ℝ)) = n

def triangleNotUniform : Prop :=
  ¬ Uniform.realUniformConvergesValue
    (fun n (x : Set.Icc (0 : ℝ) 1) => triangleValue (n+2) x) (fun _ => 0)

end Specs.SingleVariableAnalysis.Ch12.IntegralFailure
