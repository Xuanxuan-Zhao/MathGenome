import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.C1Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Monotone

/-! K03.19.c1_uniform, paper.tex:4922–4927.
The derivative is continuous only on each OPEN partition cell, and has
separate finite limits from within that cell. Its values at partition nodes
are arbitrary. There is no global continuous derivative hypothesis.
The same real-variable condition is used for real and complex targets.
All coefficients use the canonical proper Darboux integral. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform
open _root_.SingleVariableAnalysis.Riemann Set Filter
open Ch08.Integral PeriodicSetup Representation
open scoped Topology BigOperators

/-- A piecewise continuous derivative, including its actual derivative relation
on every open cell. Endpoint limits are finite elements of the scalar space. -/
def CellwiseDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (f df : ℝ → E) (P : PartitionData a b) : Prop :=
  ∀ i : Fin P.n,
    (∀ x ∈ Ioo (P.point i.castSucc) (P.point i.succ), HasDerivAt f (df x) x) ∧
    ContinuousOn df (Ioo (P.point i.castSucc) (P.point i.succ)) ∧
    ∃ L R : E, Tendsto df (𝓝[>] (P.point i.castSucc)) (𝓝 L) ∧
      Tendsto df (𝓝[<] (P.point i.succ)) (𝓝 R)

/-- Continuous piecewise C¹, with finite one-sided derivative limits. The
existential derivative is a function, not an assumed analytic certificate. -/
def PiecewiseC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (f : ℝ → E) (P : PartitionData a b) : Prop :=
  ContinuousOn f (Icc a b) ∧ ∃ df : ℝ → E, CellwiseDerivative f df P

/-- Integration by parts over all cells. Internal boundary terms cancel at the
actual, continuous node values of u and v; du and dv may jump there. -/
def partitionParts : Prop := ∀ (u v du dv : ℝ → ℂ) {a b : ℝ}
  (P : PartitionData a b),
  ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) →
  (∀ i : Fin P.n, ∀ x ∈ Ioo (P.point i.castSucc) (P.point i.succ),
    HasDerivAt u (du x) x ∧ HasDerivAt v (dv x) x) →
  complexIntegrableValue du a b → complexIntegrableValue dv a b →
  ∃ h₁ : complexIntegrableValue (fun x => u x * dv x) a b,
  ∃ h₂ : complexIntegrableValue (fun x => du x * v x) a b,
    complexIntegralValue _ h₁ = u b * v b - u a * v a - complexIntegralValue _ h₂

/-- Integrability is proved from piecewise continuity and finite limits, and
coefficient differentiation is proved with no matching of derivative limits. -/
def derivativeCoefficients : Prop := ∀ (f df : ℝ → ℂ)
  (P : PartitionData (-Real.pi) Real.pi),
  ContinuousOn f (Icc (-Real.pi) Real.pi) → CellwiseDerivative f df P →
  f (-Real.pi) = f Real.pi →
  ∃ _hdi : complexIntegrableValue df (-Real.pi) Real.pi,
  ∃ H : ComplexWeights f, ∃ Hd : ComplexWeights df,
    ∀ n : ℤ, coefficientValue df n (Hd n) =
      (Complex.I * (n : ℂ)) * coefficientValue f n (H n)

/-- Full absolute/uniform synthesis, including pointwise equality at the seams,
uniform convergence of the absolute sums, and the unordered integer HasSum. -/
def AbsoluteUniform (f : ℝ → ℂ) : Prop :=
  ∃ H : ComplexWeights f,
    Summable (fun n : ℤ => ‖coefficientValue f n (H n)‖) ∧
    Continuous (C1Uniform.periodicExtensionValue f) ∧
    Function.Periodic (C1Uniform.periodicExtensionValue f) (2 * Real.pi) ∧
    EqOn (C1Uniform.periodicExtensionValue f) f (Icc (-Real.pi) Real.pi) ∧
    Ch12.Uniform.complexUniformConvergesValue (partialSumValue f H)
      (C1Uniform.periodicExtensionValue f) ∧
    Ch12.Uniform.realUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖coefficientValue f n (H n) * modeValue n x‖)
      (fun _ => ∑' n : ℤ, ‖coefficientValue f n (H n)‖) ∧
    (∀ x : ℝ, HasSum (fun n : ℤ => coefficientValue f n (H n) * modeValue n x)
      (C1Uniform.periodicExtensionValue f x))

def absoluteUniformToExtension : Prop := ∀ (f : ℝ → ℂ)
  (P : PartitionData (-Real.pi) Real.pi),
  PiecewiseC1 f P → f (-Real.pi) = f Real.pi → AbsoluteUniform f

/-- The original periodic formulation; continuity and periodicity hold globally,
while all derivative hypotheses are confined to one finite partition. -/
def absoluteUniformPeriodic : Prop := ∀ (f : ℝ → ℂ)
  (P : PartitionData (-Real.pi) Real.pi),
  Continuous f → Function.Periodic f (2 * Real.pi) →
  (∃ df : ℝ → ℂ, CellwiseDerivative f df P) →
  ∃ H : ComplexWeights f,
    Summable (fun n : ℤ => ‖coefficientValue f n (H n)‖) ∧
    Ch12.Uniform.complexUniformConvergesValue (partialSumValue f H) f ∧
    Ch12.Uniform.realUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖coefficientValue f n (H n) * modeValue n x‖)
      (fun _ => ∑' n : ℤ, ‖coefficientValue f n (H n)‖) ∧
    (∀ x : ℝ, HasSum (fun n : ℤ => coefficientValue f n (H n) * modeValue n x) (f x))

/-- Real scalars use the canonical complex embedding and the same coefficients;
the upstream real/complex finite-sum identities give the real Fourier notation. -/
def realAbsoluteUniformToExtension : Prop := ∀ (f : ℝ → ℝ)
  (P : PartitionData (-Real.pi) Real.pi),
  PiecewiseC1 f P → f (-Real.pi) = f Real.pi →
  AbsoluteUniform (fun x => (f x : ℂ))

end Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform
