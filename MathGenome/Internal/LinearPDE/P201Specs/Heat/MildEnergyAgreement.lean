import MathGenome.Internal.LinearPDE.P201Specs.Heat.SpectralSemigroup
import MathGenome.Internal.LinearPDE.P201Specs.Heat.ParabolicForms
import MathGenome.Internal.LinearPDE.P201Specs.Common.IntegratedMild

/-! Independent formulation of paper.tex, Proposition pde:heat-mild-energy.
The conditional clause uses precisely L²(V) with distributional derivative in
L²(V'), a continuous H representative, and the equation in V'. It does not
require the H-valued forcing to be square integrable. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
universe u v
namespace P201.Heat.MildEnergyAgreement
open ExpandedFA.Evolution ExpandedFA.Semigroups
open HilbertTripleSpec HilbertTripleTraceSpec ParabolicGalerkinSpec
open P201.Common.IntegratedMild

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The original dense continuous injection, with its canonical pivot. -/
def triple (d : CoerciveForm V H) : HilbertTriple V H :=
  ⟨d.j, d.injective, d.dense⟩

/-- The algebraic form supplied to the autonomous energy theorem. -/
def algebraicForm (d : CoerciveForm V H) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => d.a x y)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)

/-- The energy class for an arbitrary H-valued forcing representative.
No integrability is encoded by a totalized integral. -/
structure EnergySolution (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : H) (f : ℝ → H) where
  value : timeLpValue V 2 T
  derivative : timeLpValue (StrongDual ℝ V) 2 T
  curve : TraceCurve H T
  represents : Represents (triple d) T value curve
  has_derivative : tripleDerivativeValue (triple d) T value derivative
  equation : ∀ᵐ t ∂timeMeasureValue T,
    derivative t = pivotValue (triple d) (f t) - d.a (value t)
  initial : curve ⟨0, by simp [hT]⟩ = u₀

namespace Expected

/-- Genuine H-valued Bochner convolution, continuous including t=0, and
agreement at every time with every energy solution that exists. -/
def MildConclusion (d : CoerciveForm V H) (S : C0Semigroup ℝ H)
    (T : ℝ≥0) (u₀ : H) (f : ℝ → H) : Prop :=
  (∀ t ∈ Icc 0 (T : ℝ),
    IntervalIntegrable (fun s => S.operators (t - s).toNNReal (f s)) volume 0 t) ∧
  mildSolution S u₀ f 0 = u₀ ∧
  IsMildSolution S T u₀ f (mildSolution S u₀ f) ∧
  IsIntegratedSolution S T u₀ f (mildSolution S u₀ f) ∧
  (∀ u, IsIntegratedSolution S T u₀ f u ↔ IsMildSolution S T u₀ f u) ∧
  ∀ z : EnergySolution d T T.coe_nonneg u₀ f,
    ∀ t : Icc 0 (T : ℝ), z.curve t = mildSolution S u₀ f t

/-- The semigroup is the spectral exponential of the very same canonical
form operator, and exists without a compact embedding. -/
def MildEnergyTheorem : Prop :=
  ∀ (d : CoerciveForm V H), ∃ S : C0Semigroup ℝ H,
    SpectralSemigroupExpected.HeatSemigroup d S ∧
    ∀ (T : ℝ≥0), 0 < (T : ℝ) → ∀ (u₀ : H) (f : ℝ → H),
      IntegrableOn f (Icc 0 (T : ℝ)) → MildConclusion d S T u₀ f

/-- L²(H) is sent to L²(V') by the canonical pivot. Existence in the
energy class and equality with the identical H-valued formula follow. -/
def L2Agreement : Prop :=
  ∀ (d : CoerciveForm V H) (S : C0Semigroup ℝ H),
    SpectralSemigroupExpected.HeatSemigroup d S →
    ∀ (T : ℝ≥0), 0 < (T : ℝ) → ∀ (u₀ : H) (f : timeLpValue H 2 T),
      IntegrableOn (f : ℝ → H) (Icc 0 (T : ℝ)) ∧
      ∃ z : EnergySolution d T T.coe_nonneg u₀ f,
        ∀ t : Icc 0 (T : ℝ), z.curve t = mildSolution S u₀ f t

/-- Arbitrary L²(V') data retain the autonomous energy theorem in their
own spaces. There is no H-valued convolution asserted for these data. -/
def DualEnergyExistence : Prop :=
  ∀ (d : CoerciveForm V H) (T : ℝ) (hT : 0 < T),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : timeLpValue (StrongDual ℝ V) 2 T) (u₀ : H),
      P201Specs.Heat.ParabolicForms.SolutionConclusion (triple d) T hT.le
        (fun _ => algebraicForm d) ‖d.a‖ K f u₀


/-- Closed binding types, with both spaces and their Hilbert structures quantified. -/
def MildEnergyTheoremStatement : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    MildEnergyTheorem (V := V) (H := H)

def L2AgreementStatement : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    L2Agreement (V := V) (H := H)

def DualEnergyExistenceStatement : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    DualEnergyExistence (V := V) (H := H)

end Expected
end P201.Heat.MildEnergyAgreement
