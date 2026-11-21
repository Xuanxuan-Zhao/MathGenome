import Mathlib.Analysis.Fourier.AddCircle

/-!
Fourier analysis used in paper.tex:14576–14588, 15588–15598, 18017–18028.
All positive periods are allowed, in particular the angular and period-one circles.
The scalar L² and L¹ spaces are the canonical strongly measurable a.e. quotients
used by the upstream Bochner Specs. Measures below are explicitly normalized Haar
measures, not the default unnormalized volume on `AddCircle T`.
-/
noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology

namespace ExpandedFA.Fourier.TorusFourierBasisSpec

instance angularPeriodPositive : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The actual quotient-group rescaling, from x mod 1 to θ mod 2π. -/
def angleChange : AddCircle (1 : ℝ) ≃+ AddCircle (2 * π) :=
  AddCircle.equivAddCircle 1 (2 * π) one_ne_zero (by positivity)

def CompleteOrthonormal : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)],
    Orthonormal ℂ (fourierLp (T := T) 2) ∧
      (Submodule.span ℂ (Set.range (fourierLp (T := T) 2))).topologicalClosure = ⊤

def Basis : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)],
    ∃ b : HilbertBasis ℤ ℂ (Lp ℂ 2 (AddCircle.haarAddCircle (T := T))),
      ∀ n, b n = fourierLp (T := T) 2 n

def Expansion : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))),
    HasSum (fun n : ℤ => fourierCoeff f n • fourierLp 2 n) f

def Parseval : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))),
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) (‖f‖ ^ 2)

/-- Every square-summable sequence occurs, with its given integer indexing. -/
def CoefficientSurjective : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (a : lp (fun _ : ℤ => ℂ) 2),
    ∃ f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)), ∀ n, fourierCoeff f n = a n

/-- The coefficient integrals themselves form a unitary map onto ℓ². -/
def CoefficientUnitary : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)],
    ∃ U : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) ≃ₗᵢ[ℂ]
        lp (fun _ : ℤ => ℂ) 2,
      ∀ f n, U f n = fourierCoeff f n

def L1Unique : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f g : AddCircle T → ℂ),
    Integrable f AddCircle.haarAddCircle → Integrable g AddCircle.haarAddCircle →
    (∀ n, fourierCoeff f n = fourierCoeff g n) → f =ᵐ[AddCircle.haarAddCircle] g

/-- Continuous periodic functions, represented on their quotient circle. -/
def ContinuousUnique : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f g : C(AddCircle T, ℂ)),
    (∀ n, fourierCoeff f n = fourierCoeff g n) → f = g

/-- An explicit version for continuous periodic real-variable functions,
using the actual normalized interval Fourier integrals at any basepoint. -/
def PeriodicUnique : Prop :=
  ∀ (T : ℝ) [hT : Fact (0 < T)] (f g : ℝ → ℂ),
    Continuous f → Continuous g → Function.Periodic f T → Function.Periodic g T →
    ∀ a : ℝ,
      (∀ n, fourierCoeffOn (lt_add_of_pos_right a hT.out) f n =
        fourierCoeffOn (lt_add_of_pos_right a hT.out) g n) → f = g

/-- Uniform trigonometric density also permits uniqueness of finite circle measures. -/
def TrigonometricDensity : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)],
    (Submodule.span ℂ (Set.range (fourier (T := T)))).topologicalClosure = ⊤

/-- The angular modes e^{inθ} and the period-one modes e^{2πinx}. -/
def Modes : Prop :=
  (∀ (n : ℤ) (θ : ℝ), fourier (T := 2 * π) n (θ : AddCircle (2 * π)) =
    Complex.exp (Complex.I * n * θ)) ∧
  (∀ (n : ℤ) (x : ℝ), fourier (T := 1) n (x : AddCircle (1 : ℝ)) =
    Complex.exp (2 * π * Complex.I * n * x))

/-- This identifies the normalized measures with dθ/(2π) and dx on one period. -/
def NormalizedIntegral : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : AddCircle T → ℂ) (a : ℝ),
    (∫ t, f t ∂AddCircle.haarAddCircle) =
      T⁻¹ • ∫ x in a..a + T, f (x : AddCircle T)

def CoordinateMap : Prop :=
  (∀ x : ℝ, angleChange (x : AddCircle (1 : ℝ)) =
      ((2 * π * x : ℝ) : AddCircle (2 * π))) ∧
  (∀ θ : ℝ, angleChange.symm (θ : AddCircle (2 * π)) =
      ((θ / (2 * π) : ℝ) : AddCircle (1 : ℝ)))

def CoordinateMeasurePreserving : Prop :=
  MeasurePreserving angleChange AddCircle.haarAddCircle AddCircle.haarAddCircle ∧
  MeasurePreserving angleChange.symm AddCircle.haarAddCircle AddCircle.haarAddCircle

/-- A complex linear isometric equivalence given by actual composition with θ=2πx,
including its action on modes and on the Fourier coefficient integrals. -/
def CoordinateUnitary : Prop :=
  ∃ U : Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)),
    (∀ f, (U f : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun x => f (angleChange x)) ∧
    (∀ n, U (fourierLp (T := 2 * π) 2 n) = fourierLp (T := 1) 2 n) ∧
    (∀ f n, fourierCoeff (U f) n = fourierCoeff f n)

/-- Pointwise intertwining of the actual exponential characters. -/
def CoordinateModes : Prop :=
  ∀ (n : ℤ) (x : AddCircle (1 : ℝ)),
    fourier (T := 2 * π) n (angleChange x) = fourier (T := 1) n x

/-- Chain rule on the real lifts, for arbitrary differentiable scalar functions. -/
def CoordinateDerivative : Prop :=
  ∀ (f : ℝ → ℂ) (f' : ℂ) (x : ℝ), HasDerivAt f f' (2 * π * x) →
    HasDerivAt (fun y : ℝ => f (2 * π * y)) ((2 * π : ℝ) • f') x

/-- The derivative rule for real lifts of actual angular-circle functions. -/
def CircleCoordinateDerivative : Prop :=
  ∀ (f : AddCircle (2 * π) → ℂ) (f' : ℂ) (x : ℝ),
    HasDerivAt (fun θ : ℝ => f (θ : AddCircle (2 * π))) f' (2 * π * x) →
    HasDerivAt (fun y : ℝ => f (angleChange (y : AddCircle (1 : ℝ))))
      ((2 * π : ℝ) • f') x

/-- The period-one derivative multiplier gives the stated Sobolev weight. -/
def SobolevWeight : Prop :=
  ∀ n : ℤ, 1 + ‖(2 * π * Complex.I * n : ℂ)‖ ^ 2 =
    1 + 4 * π ^ 2 * (n : ℝ) ^ 2

/-- Explicit derivative multipliers in both circle conventions. -/
def ModeDerivatives : Prop :=
  (∀ (n : ℤ) (θ : ℝ), HasDerivAt
    (fun y : ℝ => fourier (T := 2 * π) n (y : AddCircle (2 * π)))
    (Complex.I * n * fourier n (θ : AddCircle (2 * π))) θ) ∧
  (∀ (n : ℤ) (x : ℝ), HasDerivAt
    (fun y : ℝ => fourier (T := 1) n (y : AddCircle (1 : ℝ)))
    (2 * π * Complex.I * n * fourier n (x : AddCircle (1 : ℝ))) x)

end ExpandedFA.Fourier.TorusFourierBasisSpec
