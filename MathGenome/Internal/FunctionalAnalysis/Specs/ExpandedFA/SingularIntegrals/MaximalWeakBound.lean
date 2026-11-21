import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Independent specification of the definition, weak (1,1) estimate and supremum
bound in paper.tex:18180–18210. The other clauses of that theorem are allocated
to `ops_maximal_strong`. Euclidean balls carry their usual Euclidean metric and
Lebesgue volume. Extended nonnegative values retain possible infinite suprema.
The norm formulation applies in particular to both real and complex scalars.
-/
noncomputable section
open MeasureTheory Metric
open scoped ENNReal
universe u v

namespace ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec

def MaximalType :=
  ∀ {X : Type u} {F : Type v} [PseudoMetricSpace X] [MeasurableSpace X]
    [NormedAddCommGroup F], Measure X → (X → F) → X → ℝ≥0∞

/-- The centered maximal function, with a supremum over all positive real radii. -/
def MaximalValue : MaximalType.{u,v} := fun μ f x =>
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r)

/-- Agreement with the paper's ordinary norm integrals for locally integrable
functions; no conversion of the potentially infinite supremum to a real number. -/
def BallIntegralFormula : Prop :=
  ∀ (d : ℕ) {F : Type v} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin d) → F) (_hf : LocallyIntegrable f volume)
    (x : EuclideanSpace ℝ (Fin d)),
    MaximalValue volume f x =
      ⨆ r : ℝ, ⨆ (_ : 0 < r),
        ENNReal.ofReal ((volume.real (ball x r))⁻¹ * ∫ y in ball x r, ‖f y‖)

/-- Explicit dimension-only constant, valid also in dimension zero. -/
def WeakBound : Prop :=
  ∀ (d : ℕ) {F : Type v} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin d) → F) (_hf : Integrable f volume)
    (a : ℝ) (_ha : 0 < a),
    volume {x | ENNReal.ofReal a < MaximalValue volume f x} ≤
      (5 : ℝ≥0∞) ^ d * ENNReal.ofReal (∫ x, ‖f x‖) / ENNReal.ofReal a

/-- An essential bound on the input controls every ball average, hence the
maximal function at every center. This is stronger than the a.e. output bound. -/
def InfinityPointwiseBound : Prop :=
  ∀ (d : ℕ) {F : Type v} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin d) → F) (_hf : MemLp f ∞ volume)
    (x : EuclideanSpace ℝ (Fin d)),
    MaximalValue volume f x ≤ eLpNorm f ∞ volume

/-- The supremum norm estimate with constant one, stated without discarding
infinite values by `toReal`. -/
def InfinityBound : Prop :=
  ∀ (d : ℕ) {F : Type v} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin d) → F) (_hf : MemLp f ∞ volume),
    essSup (MaximalValue volume f) volume ≤ eLpNorm f ∞ volume

/-- The extended maximal function is Borel measurable. -/
def MeasurableMaximal : Prop :=
  ∀ (d : ℕ) {F : Type v} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin d) → F), Measurable (MaximalValue volume f)

/-- A.e. replacement does not change any of the averages, even at exceptional
centers. Thus the construction is compatible with the upstream a.e. quotients. -/
def Congruence : Prop :=
  ∀ {X : Type u} {F : Type v} [PseudoMetricSpace X] [MeasurableSpace X]
    [NormedAddCommGroup F] (μ : Measure X) (f g : X → F),
    f =ᵐ[μ] g → MaximalValue μ f = MaximalValue μ g

end ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec
