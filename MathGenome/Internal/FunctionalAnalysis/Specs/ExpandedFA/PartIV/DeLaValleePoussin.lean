import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.RCLike.Basic

/-!
Independent statements of paper.tex:19865–19893, fa2:p4:de-la-vallee-poussin.
The scalar field is real or complex. The family is a set in the a.e. L¹ quotient;
no countability or nonemptiness is imposed. `UniformIntegrable ... 1 μ` is
Mathlib's conjunction of uniform absolute continuity on small sets and a common
finite L¹ bound. The nonnegative Lebesgue integral expresses a finite integral
bound without the totalized Bochner integral's convention for nonintegrable
functions. A real function restricted to `[0,∞)` represents the stated G.
Only that restriction is constrained. No normalization G(0)=0 is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
universe u v

namespace ExpandedFA.PartIV.DeLaValleePoussinSpec

/-- Continuous, increasing, nonnegative convex growth on the nonnegative half-line. -/
def GrowthFunction (G : ℝ → ℝ) : Prop :=
  ContinuousOn G (Ici 0) ∧ MonotoneOn G (Ici 0) ∧ ConvexOn ℝ (Ici 0) G ∧
    (∀ t, 0 ≤ t → 0 ≤ G t) ∧ Tendsto (fun t => G t / t) atTop atTop

/-- A common finite Orlicz integral bound, including the empty family. -/
def HasGrowthBound {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : ι → X → E) : Prop :=
  ∃ G : ℝ → ℝ, GrowthFunction G ∧ ∃ C : ℝ≥0,
    ∀ i, (∫⁻ x, ENNReal.ofReal (G ‖f i x‖) ∂μ) ≤ C

/-- The complete finite-measure criterion, for scalar L¹ families. -/
def Criterion : Prop :=
  ∀ {X : Type u} {𝕂 : Type v} [MeasurableSpace X] [RCLike 𝕂]
    (μ : Measure X) [IsFiniteMeasure μ] (F : Set (Lp 𝕂 1 μ)),
    ((∃ C : ℝ≥0, ∀ f ∈ F, ‖f‖ ≤ (C : ℝ)) ∧
      UnifIntegrable (fun f : F => (f.1 : X → 𝕂)) 1 μ) ↔
      HasGrowthBound μ (fun f : F => (f.1 : X → 𝕂))

end ExpandedFA.PartIV.DeLaValleePoussinSpec
