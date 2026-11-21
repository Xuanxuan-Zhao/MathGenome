import MathGenome.Internal.LinearPDE.P201Specs.Common.TimeTrace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.ParabolicForms

/-! Independent statement of paper.tex, Section H05, theorem pde:parabolic-form.
The operator is the canonical bounded representative of the algebraic bilinear
form, changed to zero only on its common exceptional null set. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
universe u v

namespace P201Specs.Heat.ParabolicForms
open ExpandedFA.Evolution
open HilbertTripleSpec HilbertTripleTraceSpec ParabolicGalerkinSpec

section Data
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Only strong trajectories and the simultaneous form bounds are hypotheses.
Scalar measurability is a consequence, not an extra assumption. -/
structure FormAssumptions (j : HilbertTriple V H) (T : ℝ)
    (a : BilinearForms V) (M α c₀ : ℝ) : Prop where
  strong_measurable : ∀ x, AEStronglyMeasurable (fun t => formOperator a M t x)
    (timeMeasureValue T)
  bounds : ∀ᵐ t ∂timeMeasureValue T, BoundedAt a M t ∧
    ∀ x, α * ‖x‖ ^ 2 - c₀ * ‖j.embedding x‖ ^ 2 ≤ a t x x

/-- The two integrals are genuine Lebesgue integrals on every initial interval. -/
def EnergyIdentity {j : HilbertTriple V H} {T : ℝ} {hT : 0 ≤ T}
    {a : BilinearForms V} {M : ℝ}
    {f : timeLpValue (StrongDual ℝ V) 2 T} {u₀ : H}
    (z : WeakSolution j T hT a M f u₀) : Prop :=
  ∀ t : Set.Icc 0 T,
    IntervalIntegrable (fun s => a s (z.value s) (z.value s)) volume 0 t.val ∧
    IntervalIntegrable (fun s => f s (z.value s)) volume 0 t.val ∧
    (1 / 2 : ℝ) * ‖z.curve t‖ ^ 2 +
        (∫ s in 0..t.val, a s (z.value s) (z.value s)) =
      (1 / 2 : ℝ) * ‖u₀‖ ^ 2 + (∫ s in 0..t.val, f s (z.value s))

/-- `curve` has the supremum norm on C([0,T];H). The other norms are the
original Bochner L²(V) and L²(V') norms. -/
def SolutionConclusion (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : BilinearForms V) (M K : ℝ)
    (f : timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H) : Prop :=
  ∃ z : WeakSolution j T hT a M f u₀,
    EnergyIdentity z ∧
    ‖z.curve‖ ^ 2 + ‖z.value‖ ^ 2 + ‖z.derivative‖ ^ 2 ≤
      K * (‖u₀‖ ^ 2 + ‖f‖ ^ 2) ∧
    ∀ w : WeakSolution j T hT a M f u₀, w = z
end Data

/-- K precedes both spaces and the embedding, as well as the form and data;
thus it depends only on M, α, c₀ and T. No symmetry or separability occurs. -/
def GeneralTheorem : Prop :=
  ∀ (T M α c₀ : ℝ) (hT : 0 < T), 0 < α → 0 ≤ c₀ →
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {V : Type u} {H : Type v}
        [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
        [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (j : HilbertTriple V H) (a : BilinearForms V),
        FormAssumptions j T a M α c₀ →
        ∀ (f : timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H),
          SolutionConclusion j T hT.le a M K f u₀

/-- Explicit autonomous bounded coercive specialization, for algebraic
bilinear forms with the given global bound and without symmetry. -/
def AutonomousTheorem : Prop :=
  ∀ (T M α : ℝ) (hT : 0 < T), 0 < α →
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {V : Type u} {H : Type v}
        [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
        [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (j : HilbertTriple V H) (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ),
        (∀ x y, ‖a x y‖ ≤ M * ‖x‖ * ‖y‖) →
        (∀ x, α * ‖x‖ ^ 2 ≤ a x x) →
        ∀ (f : timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H),
          SolutionConclusion j T hT.le (fun _ => a) M K f u₀

/-- Full original theorem, including the scalar-to-strong separable bridge. -/
def ParabolicFormsTheorem : Prop :=
  GeneralTheorem.{u,v} ∧ AutonomousTheorem.{u,v} ∧
    ExpandedFA.Evolution.ParabolicFormsSpec.SeparableMeasurabilityExpected.{u}

end P201Specs.Heat.ParabolicForms
