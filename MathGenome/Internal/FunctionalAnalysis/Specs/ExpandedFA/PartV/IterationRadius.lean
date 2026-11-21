import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The complete spectral-radius iteration criterion, paper.tex
`fa2:p5:iteration-radius`. Complex Banach spaces include the zero space.
The shift is on the actual square-summable complex sequences, indexed from zero.
The affine estimate is uniform over every bounded set of initial errors. -/
noncomputable section
open Filter
open scoped Topology ENNReal
namespace Specs.ExpandedFA.PartV.IterationRadius
open BanachAlgebra.Conventions
universe u

abbrev Radius {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) : ℝ := AlgebraSpectralRadiusValue ℂ (X →L[ℂ] X) T

def Geometric {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) : Prop :=
  ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ C * q ^ n

def Criterion : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X),
    (Radius T < 1 ↔ Tendsto (fun n : ℕ => ‖T ^ n‖) atTop (𝓝 0)) ∧
    (Radius T < 1 ↔ Geometric T)

def StrongConsequence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X), Radius T < 1 →
    ∀ x : X, Tendsto (fun n : ℕ => (T ^ n) x) atTop (𝓝 0)

def AffineIteration : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X), Radius T < 1 →
    ∃ (S : X →L[ℂ] X) (C q : ℝ),
      (1 - T) * S = 1 ∧ S * (1 - T) = 1 ∧
      0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ b : X,
        (∀ y : X, T y + b = y ↔ y = S b) ∧
        (∀ (x : ℕ → X), (∀ n, x (n + 1) = T (x n) + b) →
          (∀ n, x n - S b = (T ^ n) (x 0 - S b)) ∧
          Tendsto x atTop (𝓝 (S b))) ∧
        (∀ (x₀ : X) (R : ℝ), ‖x₀ - S b‖ ≤ R → ∀ n : ℕ,
          ‖(fun x => T x + b)^[n] x₀ - S b‖ ≤ C * q ^ n * R)

abbrev ShiftSpace := lp (fun _ : ℕ => ℂ) 2

private def leftShiftLinear : ShiftSpace →ₗ[ℂ] ShiftSpace where
  toFun x := ⟨fun k => x (k + 1), memℓp_gen <|
    (summable_nat_add_iff 1).2 ((lp.memℓp x).summable (by norm_num))⟩
  map_add' x y := by apply lp.ext; rfl
  map_smul' c x := by apply lp.ext; rfl

private theorem leftShiftLinear_bound (x : ShiftSpace) : ‖leftShiftLinear x‖ ≤ 1 * ‖x‖ := by
  have hs := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have he := hs.sum_add_tsum_nat_add 1
  have hn (v : ShiftSpace) : ‖v‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  have hh : ‖leftShiftLinear x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hn, hn]
    change (∑' k, ‖x (k + 1)‖ ^ 2) ≤ ∑' k, ‖x k‖ ^ 2
    have he' : ‖x 0‖ ^ 2 + (∑' k, ‖x (k + 1)‖ ^ 2) = ∑' k, ‖x k‖ ^ 2 := by
      simpa using he
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg x, norm_nonneg (leftShiftLinear x)]

/-- The literal left shift, deleting coordinate zero. -/
def leftShift : ShiftSpace →L[ℂ] ShiftSpace := leftShiftLinear.mkContinuous 1 leftShiftLinear_bound

def ShiftCoordinates : Prop := ∀ (x : ShiftSpace) (k : ℕ), leftShift x k = x (k + 1)

def ShiftCounterexample : Prop :=
  (∀ x : ShiftSpace, Tendsto (fun n : ℕ => (leftShift ^ n) x) atTop (𝓝 0)) ∧
  (∀ n : ℕ, ‖leftShift ^ n‖ = 1) ∧
  AlgebraSpectrumValue ℂ (ShiftSpace →L[ℂ] ShiftSpace) leftShift = Metric.closedBall 0 1 ∧
  Radius leftShift = 1 ∧ ¬ Geometric leftShift

end Specs.ExpandedFA.PartV.IterationRadius
