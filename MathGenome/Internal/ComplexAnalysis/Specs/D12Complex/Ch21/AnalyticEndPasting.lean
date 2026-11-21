import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.FiniteEndGluing
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity

/-! Analytic attachment in paper.tex:3705–3711. The only analytic input
concerns the actual punctured parameter maps in the original surface.
There is no complex structure or regularity assumption on the completion. -/
noncomputable section
open Set Topology

namespace D12Complex.AnalyticEndPasting
open Surfaces FiniteEndGluing
universe u v w

/-- Transport an arbitrary partial old chart through an open embedding. -/
def transportChart {Y : Type*} {X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] {i : Y → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart Y) : ComplexChart X :=
  ⟨e.val.lift_openEmbedding hi, e.property⟩

/-- Exact punctured inverse charts. Compatibility here is solely on E:
`CompatibleCharts` is weak holomorphy in both directions on the actual
open overlap. The two equations identify these charts with the given θ. -/
structure AnalyticParameters {E : Type u} {J : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace B]
    (d : Data E J B) (S : RiemannSurface E) where
  chart : J → ComplexChart E
  source : ∀ j, (chart j).val.source = range (d.theta j)
  target : ∀ j, (chart j).val.target = {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < d.radius j}
  apply_theta : ∀ j (t : Parameter (d.radius j)), (chart j).val (d.theta j t) = (t : ℂ)
  symm_parameter : ∀ j (t : Parameter (d.radius j)),
    (chart j).val.symm (t : ℂ) = d.theta j t
  compatible : ∀ j e, e ∈ S.atlas → CompatibleCharts (chart j) e

/-- Literal value pasting, including the prescribed old values at poles. -/
def paste {E : Type u} {J : Type v} (F : E → RiemannSphere)
    (G : J → ℂ → RiemannSphere) : E ⊕ J → RiemannSphere :=
  Sum.elim F (fun j => G j 0)

/-- The constructed atlas and its complete analytic and pasting conclusions.
In particular the same atlas works for every compatible scalar function. -/
structure Completion {E : Type u} {J : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace (E ⊕ J)]
    (d : Data E J B) (S : RiemannSurface E) where
  oldEmbedding : IsOpenEmbedding (Sum.inl : E → E ⊕ J)
  surface : RiemannSurface (E ⊕ J)
  parameterChart : J → ComplexChart (E ⊕ J)
  atlas_eq : surface.atlas =
    (transportChart oldEmbedding '' S.atlas) ∪ range parameterChart
  parameter_source : ∀ j, (parameterChart j).val.source = range (d.psi j)
  parameter_target : ∀ j, (parameterChart j).val.target = Metric.ball (0 : ℂ) (d.radius j)
  parameter_center : ∀ j, (parameterChart j).val (Sum.inr j) = 0
  parameter_apply : ∀ j (t : FullDisk (d.radius j)),
    (parameterChart j).val (d.psi j t) = (t : ℂ)
  parameter_symm : ∀ j (t : FullDisk (d.radius j)),
    (parameterChart j).val.symm (t : ℂ) = d.psi j t
  old_holomorphic : HolomorphicMap S surface Sum.inl
  old_locallyBiholomorphic : ∀ x : E,
    LocallyBiholomorphicAt S surface Sum.inl x
  old_structure : ∀ e : ComplexChart E,
    e ∈ maximalAtlas S.atlas ↔ transportChart oldEmbedding e ∈ maximalAtlas surface.atlas
  meromorphic_paste : ∀ (F : E → RiemannSphere) (G : J → ℂ → RiemannSphere),
    ScalarMeromorphic S F →
    (∀ j, ScalarMeromorphicOn (Metric.ball (0 : ℂ) (d.radius j)) (G j)) →
    (∀ j (t : Parameter (d.radius j)), G j (t : ℂ) = F (d.theta j t)) →
    ScalarMeromorphic surface (paste F G)

end D12Complex.AnalyticEndPasting

namespace Specs.D12Complex.Ch21.AnalyticEndPasting
open _root_.D12Complex _root_.D12Complex.Surfaces
open _root_.D12Complex.FiniteEndGluing _root_.D12Complex.AnalyticEndPasting
universe u v w

def analytic_end_pasting_type : Prop :=
  ∀ {E : Type u} {J : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [Finite J] [T2Space B]
    (d : Data E J B) (S : RiemannSurface E),
    AnalyticParameters d S → letI := d.topology; Nonempty (Completion d S)

/-- Local scalar meromorphy in covering atlas charts suffices, with exclusion
of identically infinite germs proved from those local hypotheses. -/
def scalarMeromorphic_of_local_charts_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {S : RiemannSurface X}
    {F : X → RiemannSphere},
    (∀ a : X, ∃ e ∈ S.atlas, a ∈ e.val.source ∧
      ScalarMeromorphicOn e.val.target (F ∘ e.val.symm)) →
    ScalarMeromorphic S F

end Specs.D12Complex.Ch21.AnalyticEndPasting
