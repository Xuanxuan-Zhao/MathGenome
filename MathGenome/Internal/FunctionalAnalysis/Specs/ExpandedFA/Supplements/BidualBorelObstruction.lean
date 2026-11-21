import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BoundedBorelBidual
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.UnitInterval

/-! Independent specification of the obstruction in `fa2:p1:ck-bidual-borel`.
The interval has its Borel structure and its canonical Lebesgue probability.
Scalar measures are countably additive vector measures, not finitely additive
set functions. All sums below are unconditional sums over the actual points. -/

noncomputable section

namespace ExpandedFA.Supplements.BidualBorelObstructionSpec

open MeasureTheory Set
open scoped unitInterval
open FunctionSpaces.ScalarRieszMarkovSpec BoundedBorelBidualSpec

universe u

-- Cache the canonical instances for this concrete compact domain. This avoids
-- repeated nested typeclass searches while retaining the usual supremum norm.
local instance (𝕜 : Type) [RCLike 𝕜] : NormedAddCommGroup C(I, 𝕜) := inferInstance
local instance (𝕜 : Type) [RCLike 𝕜] : NormedSpace 𝕜 C(I, 𝕜) := inferInstance

/-- The mass remaining after subtraction of all point masses. -/
def diffuseMass {X : Type*} [MeasurableSpace X] {𝕜 : Type*} [RCLike 𝕜]
    (ν : VectorMeasure X 𝕜) : 𝕜 :=
  ν univ - ∑' x : X, ν {x}

/-- The complete concrete obstruction, including the quantitative estimate,
Dirac tests, the actual Lebesgue test, and non-surjectivity for every embedding
with the specified integration pairing. -/
def AtomicObstruction (𝕜 : Type) [RCLike 𝕜] : Prop :=
  (∀ ν : VectorMeasure I 𝕜, FiniteScalarRadon ν →
    {x : I | ν {x} ≠ 0}.Countable ∧
    Summable (fun x : I => ‖ν {x}‖) ∧
    (∑' x : I, ‖ν {x}‖) ≤ ν.variation.real univ) ∧
  ∃ Φ : StrongDual 𝕜 (StrongDual 𝕜 C(I, 𝕜)),
    ‖Φ‖ ≤ 2 ∧
    (∀ (ν : VectorMeasure I 𝕜), FiniteScalarRadon ν →
      ∀ L : StrongDual 𝕜 C(I, 𝕜),
      (∀ f : C(I, 𝕜), L f = scalarIntegral ν f) → Φ L = diffuseMass ν) ∧
    (∀ x : I, Φ (ContinuousMap.evalCLM 𝕜 x) = 0) ∧
    (∃ L : StrongDual 𝕜 C(I, 𝕜),
      (∀ f : C(I, 𝕜), L f = ∫ x, f x ∂(volume : Measure I)) ∧ Φ L = 1) ∧
    (∀ e : BoundedBorel I 𝕜 →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 C(I, 𝕜)),
      (∀ (h : BoundedBorel I 𝕜) (ν : VectorMeasure I 𝕜), FiniteScalarRadon ν →
        ∀ L : StrongDual 𝕜 C(I, 𝕜),
        (∀ f : C(I, 𝕜), L f = scalarIntegral ν f) → e h L = scalarIntegral ν h) →
      ¬ Function.Surjective e)

/-- The general compact-Hausdorff embedding and the interval obstruction. -/
def RealConclusion : Prop := BorelEmbedding.{u} ℝ ∧ AtomicObstruction ℝ

def ComplexConclusion : Prop := BorelEmbedding.{u} ℂ ∧ AtomicObstruction ℂ

end ExpandedFA.Supplements.BidualBorelObstructionSpec
