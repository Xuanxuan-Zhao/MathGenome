import MathGenome.Internal.LinearPDE.P201Specs.Potential.Fundamental
import MathGenome.Internal.LinearPDE.P201Specs.Potential.BallPoisson
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The Green-kernel portion of paper.tex:951–1011. The symmetric expression
for the harmonic correction gives the source's extension at either zero point.
Values on the diagonal are totalized and have no mathematical significance. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace P201Specs.BallGreen

abbrev ImagePointType := {n : ℕ} → ℝ → Space n → Space n
/-- Kelvin image in the radius-r sphere centered at zero. -/
def imagePoint : ImagePointType := fun r x => (r ^ 2 / ‖x‖ ^ 2) • x

abbrev SymmetricPolynomialType := {n : ℕ} → ℝ → Space n → Space n → ℝ
/-- The polynomial |x|² |y-x*|² in the source's symmetry argument. -/
def symmetricPolynomial : SymmetricPolynomialType := fun r x y =>
  r ^ 4 - 2 * r ^ 2 * inner ℝ x y + ‖x‖ ^ 2 * ‖y‖ ^ 2

abbrev KernelType := {n : ℕ} → Space n → ℝ → Space n → Space n → ℝ
/-- The symmetric formula has no artificial image pole at x=0. -/
def kernel : KernelType := fun {n} a r x y =>
  fundamentalKernel n (y - x) -
    fundamentalProfile n (Real.sqrt (symmetricPolynomial r (x-a) (y-a)) / r)

abbrev PointDiracType := {n : ℕ} → (Ω : Domain n) → Space n → Distribution ℝ Ω
/-- The actual evaluation distribution on the test-function space. -/
def pointDirac : PointDiracType := fun _Ω x =>
  { toFun := fun φ => φ x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    cont := continuous_eval_const _ }

def ImageFormulaHigherStatement : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (r : ℝ), 0 < r → ∀ (x y : Space n),
    x ≠ 0 → y ≠ x → y ≠ imagePoint r x →
    kernel 0 r x y = fundamentalKernel n (y-x) -
      (r / ‖x‖) ^ (n-2) * fundamentalKernel n (y-imagePoint r x)

def ImageFormulaTwoStatement : Prop :=
  ∀ (r : ℝ), 0 < r → ∀ (x y : Space 2),
    x ≠ 0 → y ≠ x → y ≠ imagePoint r x →
    kernel 0 r x y = (1 / (2 * Real.pi)) *
      Real.log (‖x‖ * ‖y-imagePoint r x‖ / (r * ‖y-x‖))

def CenterStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r → ∀ y : Space n,
    kernel a r a y = fundamentalKernel n (y-a) - fundamentalProfile n r

def TranslationStatement : Prop :=
  ∀ {n : ℕ} (a : Space n) (r : ℝ) (x y : Space n),
    kernel a r x y = kernel 0 r (x-a) (y-a)

def SymmetryStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x y : Space n, kernel a r x y = kernel a r y x

def BoundaryZeroStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x ∈ ball a r, ∀ ζ ∈ sphere a r, kernel a r x ζ = 0

/-- Joint smoothness, including x=a or y=a, and up to the boundary away
from the diagonal. ContDiffAt asserts an actual smooth local extension. -/
def SmoothStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x ∈ ball a r, ∀ y ∈ closedBall a r, x ≠ y →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space n × Space n => kernel a r p.1 p.2) (x,y)

/-- The correction is genuinely harmonic, with no singularity at the center. -/
def CorrectionHarmonicStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x ∈ ball a r, MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩
      (fun y => fundamentalProfile n (Real.sqrt (symmetricPolynomial r (x-a) (y-a)) / r))

/-- Local integrability is explicit; the regular distribution cannot use its
fallback value for a nonintegrable function. The sign is -Delta_y G = delta_x. -/
def DistributionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x ∈ ball a r,
      LocallyIntegrableOn (kernel a r x) (ball a r) volume ∧
      -distributionLaplacian (regularDistribution ⟨ball a r, isOpen_ball⟩ (kernel a r x)) =
        pointDirac ⟨ball a r, isOpen_ball⟩ x

/-- The normal is the geometric outward unit normal, and the Poisson
kernel is the exact shared kernel, including its logarithmic normalization. -/
def NormalDerivativeStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (a : Space n) (r : ℝ), 0 < r →
    ∀ x ∈ ball a r, ∀ ζ ∈ sphere a r,
      -fderiv ℝ (kernel a r x) ζ (r⁻¹ • (ζ-a)) = BallPoisson.kernel a r x ζ

end P201Specs.BallGreen
