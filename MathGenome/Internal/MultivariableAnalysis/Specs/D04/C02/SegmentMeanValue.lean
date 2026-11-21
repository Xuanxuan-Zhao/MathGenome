import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import Mathlib.Analysis.Convex.Segment

/-! Independent propositions for `d04:02:mean-value`.
The domain is an ambient open set; the function represents its restriction.
The interior hypotheses explicitly exclude both endpoints, so a singleton
segment imposes no differentiability or sign condition on M. All Euclidean
dimensions, including zero, are allowed. No derivative continuity is assumed.
-/
noncomputable section
open Set
namespace Specs.D04.C02.SegmentMeanValue
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model

def segment_mean_value_boundType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a b : E n) (M : ℝ),
    IsOpen U → segment ℝ a b ⊆ U → ContinuousOn f (segment ℝ a b) →
    (∀ x ∈ segment ℝ a b, x ≠ a → x ≠ b → TotalDifferentiableAt U f x) →
    (∀ x ∈ segment ℝ a b, x ≠ a → x ≠ b → ‖totalDerivative f x‖ ≤ M) →
    ‖f b - f a‖ ≤ M * ‖b - a‖

def scalar_segment_mean_valueType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a b : E n),
    IsOpen U → segment ℝ a b ⊆ U → a ≠ b →
    ContinuousOn f (segment ℝ a b) →
    (∀ x ∈ segment ℝ a b, x ≠ a → x ≠ b → TotalDifferentiableAt U f x) →
    ∃ t ∈ Ioo (0 : ℝ) 1,
      f b - f a = totalDerivative f (a + t • (b - a)) (b - a)

namespace Model
/-- The paper's polynomial curve, with the shared Euclidean norm and coordinates. -/
def meanValueCounterexample (t : ℝ) : E 2 := WithLp.toLp 2 ![t ^ 2, t ^ 3]
end Model

def meanValueCounterexampleType := ℝ → E 2
def meanValueCounterexampleValue : meanValueCounterexampleType := Model.meanValueCounterexample

def meanValueCounterexample_continuousType : Prop := Continuous Model.meanValueCounterexample

def meanValueCounterexample_hasDerivAtType : Prop :=
  ∀ c : ℝ, HasDerivAt Model.meanValueCounterexample (WithLp.toLp 2 ![2 * c, 3 * c ^ 2]) c

def vector_mean_value_no_common_pointType : Prop :=
  ¬ ∃ c ∈ Ioo (0 : ℝ) 1,
    Model.meanValueCounterexample 1 - Model.meanValueCounterexample 0 =
      totalDerivative Model.meanValueCounterexample c (1 - 0)

end Specs.D04.C02.SegmentMeanValue
