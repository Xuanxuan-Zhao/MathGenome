import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for `fa2:p5:nonunique-blowup-third`, including the
adopted positive-length correction to the inhomogeneous third-kind example.
Functions are ordinary functions of real time; equations and continuity are
required on the indicated interval only. The square and third-kind examples
are stated over either scalar field. -/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV.NonlinearCounterexamples

def waiting (c t : ℝ) : ℝ := (max (t - c) 0) ^ 2

def IsWaitingSolution (T : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, u t = ∫ s in 0..t, 2 * Real.sqrt |u s|

/-- The same real-valued nonlinearity embedded in either scalar field. -/
def IsScalarWaitingSolution (𝕜 : Type*) [RCLike 𝕜] (T : ℝ) (u : ℝ → 𝕜) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ∀ t ∈ Icc 0 T,
    u t = ∫ s in 0..t, ((2 * Real.sqrt ‖u s‖ : ℝ) : 𝕜)

def IsSquareSolution (𝕜 : Type*) [RCLike 𝕜] (T : ℝ) (u : ℝ → 𝕜) : Prop :=
  ContinuousOn u (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, u t = 1 + ∫ s in 0..t, (u s)^2

def blowup (𝕜 : Type*) [RCLike 𝕜] (t : ℝ) : 𝕜 := (1 - (t : 𝕜))⁻¹

def IsThirdSolution (𝕜 : Type*) [RCLike 𝕜] (T : ℝ) (inhom : Bool)
    (u : ℝ → 𝕜) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ∀ t ∈ Icc 0 T,
    (t : 𝕜) * u t = (if inhom then (t : 𝕜) else 0) + ∫ s in 0..t, u s

namespace Spec

def WaitingFamily : Prop := ∀ T : ℝ, 0 ≤ T → ∀ c : ℝ, 0 ≤ c →
  IsWaitingSolution T (waiting c) ∧
  (∀ t, t ≤ c → waiting c t = 0) ∧
  (∀ t, c ≤ t → waiting c t = (t-c)^2) ∧
  (∀ t ∈ Icc 0 T, 0 ≤ waiting c t ∧ waiting c t ≤ t^2)

def Nonuniqueness : Prop := ∀ T : ℝ, 0 < T →
  ∃ u v : ℝ → ℝ, IsWaitingSolution T u ∧ IsWaitingSolution T v ∧
    u 0 = v 0 ∧ u T ≠ v T

def ScalarWaitingFamily : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜] (T : ℝ), 0 ≤ T →
  (∀ c : ℝ, 0 ≤ c → IsScalarWaitingSolution 𝕜 T (fun t => (waiting c t : 𝕜))) ∧
  (0 < T → ∃ u v : ℝ → 𝕜,
    IsScalarWaitingSolution 𝕜 T u ∧ IsScalarWaitingSolution 𝕜 T v ∧
    u 0 = v 0 ∧ u T ≠ v T)

def BlowupExistence : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜] (T : ℝ),
  0 ≤ T → T < 1 → IsSquareSolution 𝕜 T (blowup 𝕜)

def BlowupUniqueness : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜] (T : ℝ),
  0 ≤ T → T < 1 → ∀ u, IsSquareSolution 𝕜 T u →
    EqOn u (blowup 𝕜) (Icc 0 T)

/-- Existence and uniqueness on the complete half-open pre-blow-up interval.
Uniqueness is equality on that interval, leaving values outside it free. -/
def BlowupOnMaximalInterval : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜],
  ContinuousOn (blowup 𝕜) (Ico 0 1) ∧
  (∀ t ∈ Ico 0 1, blowup 𝕜 t = 1 + ∫ s in 0..t, (blowup 𝕜 s)^2) ∧
  ∀ u : ℝ → 𝕜, ContinuousOn u (Ico 0 1) →
    (∀ t ∈ Ico 0 1, u t = 1 + ∫ s in 0..t, (u s)^2) →
    EqOn u (blowup 𝕜) (Ico 0 1)

/-- Even a bounded function agreeing with the solution up to time one is
impossible, so no bounded continuation through one exists. -/
def NoBoundedContinuation : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜],
  ¬ ∃ (u : ℝ → 𝕜) (M : ℝ),
    EqOn u (blowup 𝕜) (Ico 0 1) ∧ ∀ t ∈ Ico 0 1, ‖u t‖ ≤ M

def NoSolutionThroughOne : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜] (T : ℝ),
  1 ≤ T → ¬ ∃ u, IsSquareSolution 𝕜 T u

def HomogeneousConstants : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜] (T : ℝ),
  0 ≤ T → ∀ z : 𝕜, IsThirdSolution 𝕜 T false (fun _ => z)

def InhomogeneousNonexistence : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜] (T : ℝ),
  0 < T → ¬ ∃ u, IsThirdSolution 𝕜 T true u

/-- On the singleton interval no value is prescribed or excluded. -/
def ThirdSingleton : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜] (u : ℝ → 𝕜),
  IsThirdSolution 𝕜 0 true u ∧ IsThirdSolution 𝕜 0 false u

end Spec
end ExpandedFA.PartV.NonlinearCounterexamples
