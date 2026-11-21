import MathGenome.Internal.LinearPDE.P201Specs.Heat.ImprovedEnergy
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.GlobalH2

/-! The full additional-energy-derivative theorem, paper.tex H08.
The abstract conclusion has no spatial hypotheses. The conditional spatial
clause identifies the original form and inclusion, rather than postulating
operator regularity or an H² measurable lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open Set MeasureTheory
open scoped ENNReal NNReal
namespace P201.Heat.ImprovedSpatialRegularity
open ExpandedFA.Evolution HilbertTripleSpec HilbertTripleTraceSpec
open MildEnergyAgreement ImprovedEnergy
open P201Specs

/-- Exactly the Dirichlet form of the coefficient field on the canonical
full-H¹ zero-trace space and its actual L² inclusion. -/
def IsDirichletForm {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n)
    (d : CoerciveForm (H10 ℝ Ω) (Lp ℝ Ω 2)) : Prop :=
  d.j = hZeroUnderlying Ω ∧ ∀ u v : H10 ℝ Ω,
    d.a u v = ∫ x in Ω, inner ℝ (A x (hGradient u.val x)) (hGradient v.val x)

/-- Identifies the canonical associated operator with the weak Dirichlet
realization, in both directions and on exactly its domain. -/
def CanonicalGraphStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (d : CoerciveForm (H10 ℝ Ω) (Lp ℝ Ω 2)), IsDirichletForm Ω A d →
    ContinuousOn A Ω → ∀ M : ℝ, (∀ x ∈ Ω, ‖A x‖ ≤ M) →
    ∀ x f : Lp ℝ Ω 2, (x, f) ∈ d.operator.graph ↔
      ∃ u : H10 ℝ Ω, hZeroUnderlying Ω u = x ∧
        InteriorH2.WeakEquation Ω A u.val f

/-- The H² representative is a genuine Bochner L² class. Both its spatial
L² value and its norm estimate refer to the original energy solution. -/
def SpatialConclusion {n : ℕ} (Ω : Domain n) (C Cdata : ℝ)
    (d : CoerciveForm (H10 ℝ Ω) (Lp ℝ Ω 2)) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : H10 ℝ Ω) (f : timeLpValue (Lp ℝ Ω 2) 2 T)
    (z : EnergySolution d T hT (d.j u₀) f) : Prop :=
  ∃ (r : Regularity d T hT u₀ f z) (w : timeLpValue (H ℝ Ω 2) 2 T),
    ‖r.velocity‖ ^ 2 + ‖r.operatorValue‖ ^ 2 + supremumSquare r.lift ≤
      Cdata * (‖u₀‖ ^ 2 + ‖f‖ ^ 2) ∧
    AEStronglyMeasurable (fun t => w t) (timeMeasureValue T) ∧
    (∀ᵐ t ∂timeMeasureValue T, hUnderlying Ω 2 (w t) = extendCurve z.curve t) ∧
    (∀ᵐ t ∂timeMeasureValue T, ‖w t‖ ≤ C * (‖r.operatorValue t‖ + ‖z.value t‖)) ∧
    ‖w‖ ≤ C * (‖r.operatorValue‖ + ‖z.value‖)

/-- Uniform elliptic constant first, followed by a data constant depending
on the form and geometry, before the time interval and data. No a.e. pointwise
membership is substituted for Bochner integrability. -/
def SpatialTheorem : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasC11Boundary Ω →
    ∀ (M L : ℝ≥0) (theta : ℝ), 0 < theta →
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1)),
      InteriorH2.CoefficientBounds Ω A M L theta → BoundaryH2.SymmetricOn Ω A →
      ∀ d : CoerciveForm (H10 ℝ Ω) (Lp ℝ Ω 2), IsDirichletForm Ω A d →
      ∃ Cdata Cspatial : ℝ, 0 ≤ Cdata ∧ 0 ≤ Cspatial ∧
      ∀ (T : ℝ) (hT : 0 < T) (u₀ : H10 ℝ Ω) (f : timeLpValue (Lp ℝ Ω 2) 2 T)
        (z : EnergySolution d T hT.le (d.j u₀) f),
        SpatialConclusion Ω C Cdata d T hT.le u₀ f z ∧
        ∃ w : timeLpValue (H ℝ Ω 2) 2 T,
          (∀ᵐ t ∂timeMeasureValue T, hUnderlying Ω 2 (w t) = extendCurve z.curve t) ∧
          ‖w‖ ^ 2 ≤ Cspatial * (‖u₀‖ ^ 2 + ‖f‖ ^ 2)

end P201.Heat.ImprovedSpatialRegularity
