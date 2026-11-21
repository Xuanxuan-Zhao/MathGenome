import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-! Independent objects and full propositions for d04:04:counterexamples.
Scalar examples use ℝ itself; the two-dimensional examples use the shared
Euclidean space, with its Euclidean norm and standard coordinate basis. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace Specs.D04.C04.InverseCounterexamples
open Specs.D04.C01.EuclideanInterfaces.Model
namespace Model

def polarExp (z : E 2) : E 2 :=
  WithLp.toLp 2 ![Real.exp (z 0) * Real.cos (z 1), Real.exp (z 0) * Real.sin (z 1)]

def circle (t : ℝ) : E 2 := WithLp.toLp 2 ![Real.cos t, Real.sin t]

def oscillatory (x : ℝ) : ℝ := if x = 0 then 0 else x / 2 + x ^ 2 * Real.sin (1 / x)

end Model
open Model

abbrev polarExpType := E 2 → E 2
def polarExpValue : polarExpType := polarExp

abbrev circleType := ℝ → E 2
def circleValue : circleType := circle

abbrev oscillatoryType := ℝ → ℝ
def oscillatoryValue : oscillatoryType := oscillatory

def polar_jacobianType : Prop := ∀ z : E 2,
  matrixOfLinearMap (fderiv ℝ polarExp z).toLinearMap =
    !![Real.exp (z 0) * Real.cos (z 1), -(Real.exp (z 0) * Real.sin (z 1));
       Real.exp (z 0) * Real.sin (z 1), Real.exp (z 0) * Real.cos (z 1)]

def polar_determinantType : Prop := ∀ z : E 2,
  (matrixOfLinearMap (fderiv ℝ polarExp z).toLinearMap).det = Real.exp (2 * z 0) ∧
    0 < (matrixOfLinearMap (fderiv ℝ polarExp z).toLinearMap).det

def polar_periodicType : Prop := ∀ z : E 2,
  polarExp (z + WithLp.toLp 2 ![0, 2 * Real.pi]) = polarExp z

def polar_local_inverseType : Prop := ∀ a : E 2,
  ∃ e : OpenPartialHomeomorph (E 2) (E 2),
    a ∈ e.source ∧ (e : E 2 → E 2) = polarExp ∧
    ContDiffOn ℝ ∞ e.symm e.target

def polar_global_failureType : Prop :=
  ¬ Function.Injective polarExp ∧
  (¬ ∃ g : E 2 → E 2, Function.LeftInverse g polarExp) ∧
  (0 : E 2) ∉ range polarExp

def exponential_submersionType : Prop :=
  (∀ x : ℝ, Function.Surjective (fderiv ℝ Real.exp x)) ∧
  range Real.exp = Ioi 0 ∧ IsOpen (range Real.exp) ∧ range Real.exp ≠ univ

def circle_derivativeType : Prop := ∀ t : ℝ,
  HasDerivAt circle (WithLp.toLp 2 ![-Real.sin t, Real.cos t]) t ∧
    Function.Injective (fderiv ℝ circle t)

def circle_local_embeddingType : Prop := ∀ a : ℝ,
  ∃ U : Set ℝ, IsOpen U ∧ a ∈ U ∧ Topology.IsEmbedding (fun t : U => circle t)

def circle_global_failureType : Prop :=
  Function.Periodic circle (2 * Real.pi) ∧ ¬ Function.Injective circle ∧
    ¬ Topology.IsEmbedding circle

def cubic_failureType : Prop :=
  Function.Bijective (fun x : ℝ => x ^ 3) ∧
  HasDerivAt (fun x : ℝ => x ^ 3) 0 0 ∧
  ∀ g : ℝ → ℝ, Function.LeftInverse g (fun x => x ^ 3) → ¬ DifferentiableAt ℝ g 0

def square_failureType : Prop :=
  fderiv ℝ (fun x : ℝ => x ^ 2) 0 = 0 ∧
  ∀ U ∈ 𝓝 (0 : ℝ), ¬ ∃ c : ℝ, EqOn (fun x : ℝ => x ^ 2) (fun _ => c) U

def oscillatory_derivative_zeroType : Prop := HasDerivAt oscillatory (1 / 2) 0

def oscillatory_derivative_ne_zeroType : Prop := ∀ x : ℝ, x ≠ 0 →
  HasDerivAt oscillatory (1 / 2 + 2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x

/-- The actual reciprocal-π witnesses, with even and odd multiples separately. -/
def oscillatory_derivative_valuesType : Prop :=
  (∀ n : ℕ, deriv oscillatory (1 / ((2 * (n + 1) : ℕ) * Real.pi)) = -(1 / 2)) ∧
  (∀ n : ℕ, deriv oscillatory (1 / ((2 * n + 1 : ℕ) * Real.pi)) = 3 / 2) ∧
  (∀ ε > (0 : ℝ), ∃ n : ℕ,
    0 < 1 / ((2 * (n + 1) : ℕ) * Real.pi) ∧
    1 / ((2 * (n + 1) : ℕ) * Real.pi) < ε) ∧
  (∀ ε > (0 : ℝ), ∃ n : ℕ,
    0 < 1 / ((2 * n + 1 : ℕ) * Real.pi) ∧
    1 / ((2 * n + 1 : ℕ) * Real.pi) < ε)

def interval_injective_monotoneType : Prop := ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
  ContinuousOn f (Ioo a b) → InjOn f (Ioo a b) →
    StrictMonoOn f (Ioo a b) ∨ StrictAntiOn f (Ioo a b)

def oscillatory_not_locally_injectiveType : Prop :=
  ∀ U ∈ 𝓝 (0 : ℝ), ¬ InjOn oscillatory U

end Specs.D04.C04.InverseCounterexamples
