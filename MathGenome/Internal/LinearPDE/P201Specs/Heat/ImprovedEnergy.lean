import MathGenome.Internal.LinearPDE.P201Specs.Heat.MildEnergyAgreement

/-! Independent scope of the abstract part of paper.tex, pde:heat-improved,
Section H08. The spatial H² corollary is separately allocated. No spectral
cutoffs, strong derivative, or extra initial regularity are hypotheses. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
universe u v

namespace P201.Heat.ImprovedEnergy
open ExpandedFA.Evolution
open HilbertTripleSpec HilbertTripleTraceSpec
open MildEnergyAgreement

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The square of the supremum V norm on the full closed interval.
Boundedness is required separately wherever this real supremum is used. -/
def supremumSquare {T : ℝ} (w : Icc 0 T → V) : ℝ :=
  sSup (Set.range (fun t => ‖w t‖ ^ 2))

/-- Strong L²(H) derivative, actual canonical operator graph, and a V lift
at every time of the given continuous H representative. The L∞ assertion
uses the original V-valued Bochner representative. -/
structure Regularity (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT (d.j u₀) f) where
  lift : Icc 0 T → V
  lift_eq : ∀ t, d.j (lift t) = z.curve t
  velocity : timeLpValue H 2 T
  operatorValue : timeLpValue H 2 T
  has_derivative : derivativeValue T (extendCurve z.curve) velocity
  derivative_eq : z.derivative =ᵐ[timeMeasureValue T]
    fun t => pivotValue (triple d) (velocity t)
  graph : ∀ᵐ t ∂timeMeasureValue T,
    (extendCurve z.curve t, operatorValue t) ∈ d.operator.graph
  equation : ∀ᵐ t ∂timeMeasureValue T, velocity t + operatorValue t = f t
  lift_bounded : BddAbove (Set.range (fun t => ‖lift t‖ ^ 2))
  value_linf : MemLp (fun t => z.value t) ∞ (timeMeasureValue T)

/-- The full regularity and quantitative conclusion. C is fixed before T,
the spaces, the embedding, the form and the data. -/
def Conclusion (C : ℝ) (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT (d.j u₀) f) : Prop :=
  ∃ r : Regularity d T hT u₀ f z,
    ‖r.velocity‖ ^ 2 + ‖r.operatorValue‖ ^ 2 + supremumSquare r.lift ≤
      C * (‖u₀‖ ^ 2 + ‖f‖ ^ 2)

/-- Original hypotheses and full abstract conclusion, for every energy
solution. The operator is always d.operator, never an arbitrary realization. -/
def ImprovedEnergyTheorem : Prop :=
  ∀ (M α : ℝ), 0 ≤ M → 0 < α →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {V : Type u} {H : Type v}
        [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
        [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (d : CoerciveForm V H), ‖d.a‖ ≤ M →
        (∀ x, α * ‖x‖ ^ 2 ≤ d.a x x) →
        ∀ (T : ℝ) (hT : 0 < T) (u₀ : V) (f : timeLpValue H 2 T)
          (z : EnergySolution d T hT.le (d.j u₀) f),
          Conclusion C d T hT.le u₀ f z

/-- A sharper intermediate estimate. This is a proof obligation, not an
extra hypothesis in ImprovedEnergyTheorem. Bounding by the full forcing
norm for each t is sufficient; no subinterval estimate is needed. -/
def APriori (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT (d.j u₀) f) : Prop :=
  ∃ (w : Icc 0 T → V) (g : timeLpValue H 2 T),
    (∀ t, d.j (w t) = z.curve t) ∧
    derivativeValue T (extendCurve z.curve) g ∧
    ‖g‖ ^ 2 ≤ d.a u₀ u₀ + ‖f‖ ^ 2 ∧
    ∀ t, d.a (w t) (w t) ≤ d.a u₀ u₀ + ‖f‖ ^ 2

/-- Uniformly quantified central analytic obligation for the spectral or
Galerkin approximation argument. It retains all original data and solutions. -/
def APrioriTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : CoerciveForm V H) (T : ℝ) (hT : 0 < T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT.le (d.j u₀) f), APriori d T hT.le u₀ f z

namespace Expected
/-- Binding for the assembly reduction. The analytic a priori estimate is
proved separately in the implementation under its original hypotheses. -/
def APrioriSuffices : Prop := APrioriTheorem.{u,v} → ImprovedEnergyTheorem.{u,v}
end Expected

end P201.Heat.ImprovedEnergy
