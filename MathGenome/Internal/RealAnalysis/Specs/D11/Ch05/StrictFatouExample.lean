import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Measure.Map

/-! Independent statements for paper.tex:1743–1755.
The real line is identified with the shared one-dimensional Euclidean space
by its single coordinate. We transport the full Carathéodory sigma-algebra
and its measure, so the measure below is completed Lebesgue measure, with
no replacement by just its Borel restriction. Natural indices include zero;
discarding that initial interval gives the source's indexing from one.
The integral is the shared supremum over finite nonnegative simple minorants.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace D11.Ch05.StrictFatouExample

/-- The usual identification of the real line with one-dimensional Euclidean space. -/
def lineEquiv : ℝ ≃ D11.Ch03.Point 1 where
  toFun x := WithLp.toLp 2 (fun _ => x)
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
    funext i
    exact congrArg x (Subsingleton.elim (0 : Fin 1) i)

/-- Pull back the full Lebesgue sigma-algebra, not the Borel sigma-algebra. -/
abbrev realLebesgueSpace : MeasurableSpace ℝ :=
  (Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1).comap lineEquiv

/-- The shared completed Lebesgue measure in real coordinates. -/
def realLebesgue : @Measure ℝ realLebesgueSpace :=
  @Measure.map (D11.Ch03.Point 1) ℝ
    (Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1) realLebesgueSpace
    lineEquiv.symm (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)

/-- Exactly the indicator of [n,n+1), valued in the nonnegative extended reals. -/
def escaping (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ico (n : ℝ) ((n : ℝ) + 1)).indicator (fun _ => 1)

end D11.Ch05.StrictFatouExample

namespace Specs.D11.Ch05.StrictFatouExample

open _root_.D11.Ch05.StrictFatouExample
open NonnegativeIntegral

local instance : MeasurableSpace ℝ := realLebesgueSpace

/-- Normalization of the transported full measure on literal real intervals. -/
def interval_measure : Prop := ∀ a b : ℝ,
  realLebesgue (Ico a b) = ENNReal.ofReal (b - a)

def measurable_escaping : Prop := ∀ n : ℕ, Measurable (escaping n)

def eventually_zero : Prop := ∀ x : ℝ, ∀ᶠ n : ℕ in atTop, escaping n x = 0

def pointwise_tendsto : Prop := ∀ x : ℝ,
  Tendsto (fun n => escaping n x) atTop (𝓝 0)

def pointwise_liminf : Prop := ∀ x : ℝ,
  liminf (fun n => escaping n x) atTop = 0

def integral_each : Prop := ∀ n : ℕ,
  nonnegativeIntegral_value realLebesgue (escaping n) = 1

def integral_liminf_zero : Prop :=
  nonnegativeIntegral_value realLebesgue
    (fun x => liminf (fun n => escaping n x) atTop) = 0

def liminf_integral_one : Prop :=
  liminf (fun n => nonnegativeIntegral_value realLebesgue (escaping n)) atTop = 1

/-- The complete displayed strict inequality, including both endpoint values. -/
def strict_fatou : Prop :=
  nonnegativeIntegral_value realLebesgue
    (fun x => liminf (fun n => escaping n x) atTop) = 0 ∧
  (0 : ℝ≥0∞) < 1 ∧
  1 = liminf (fun n => nonnegativeIntegral_value realLebesgue (escaping n)) atTop

def strict_inequality : Prop :=
  nonnegativeIntegral_value realLebesgue
    (fun x => liminf (fun n => escaping n x) atTop) <
  liminf (fun n => nonnegativeIntegral_value realLebesgue (escaping n)) atTop

/-- Pointwise convergence and nonnegativity do not give convergence of integrals. -/
def integrals_not_tendsto_zero : Prop :=
  ¬ Tendsto (fun n => nonnegativeIntegral_value realLebesgue (escaping n))
    atTop (𝓝 0)

end Specs.D11.Ch05.StrictFatouExample
