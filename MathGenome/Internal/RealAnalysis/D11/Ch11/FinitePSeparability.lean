import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.FinitePSeparability
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.D11.Ch04.CompletionVersions
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

open Set MeasureTheory TopologicalSpace
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch11.FinitePSeparability

open Specs.D11.Ch11.FinitePSeparability

variable {X : Type u} {𝕜 : Type} [m : MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Transfer to the project's ordinary quotient using the accepted canonical
representative-compatible isometry. -/
theorem ordinary_separable_of_native (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [SecondCountableTopology (Lp 𝕜 p μ)] : SeparableOrdinaryLp (𝕜 := 𝕜) μ p := by
  refine ⟨inferInstance, Ch10.QuotientConstruction.quotientNormedAddCommGroup μ p,
    Ch10.QuotientConstruction.quotientNormedSpace μ p,
    Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p,
    Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf μ p, ?_⟩
  exact (Ch10.QuotientConstruction.nativeLinearIsometryEquiv (𝕜 := 𝕜) μ p).isometry.isEmbedding.separableSpace

/-- Countable generation plus sigma-finiteness yields a countable measure-dense
algebra. Mathlib's proof uses symmetric-difference approximation on finite
pieces and then finite sums of indicators, exactly for finite exponents. -/
theorem finite_p_separability : Specs.D11.Ch11.FinitePSeparability.finite_p_separability := by
  intro X 𝕜 m _ _ _ _ μ _ p _ hp
  let : Fact (p ≠ ∞) := ⟨hp⟩
  exact ordinary_separable_of_native μ p


/-- The identity from the completed space to the original space preserves
measure; its measurability uses only inclusion of the original sigma-algebra. -/
theorem completion_identity_measurePreserving (μ : Measure X) :
    @MeasurePreserving X X (Ch02.Completion.completedSpace μ) m id (Ch02.Completion.completedMeasure μ) μ := by
  have hid : @Measurable X X (Ch02.Completion.completedSpace μ) m id :=
    measurable_id.mono le_eventuallyMeasurableSpace le_rfl
  refine @MeasurePreserving.mk X X (Ch02.Completion.completedSpace μ) m id
    (Ch02.Completion.completedMeasure μ) μ hid ?_
  apply @Measure.ext X m
  intro s hs
  rw [Measure.map_apply hid hs]
  rfl

/-- Completion does not change the original measurable functions' p-norms. -/
theorem completion_trim (μ : Measure X) :
    (Ch02.Completion.completedMeasure μ).trim (le_eventuallyMeasurableSpace (m := m) (l := ae μ)) = μ := by
  apply @Measure.ext X m
  intro s hs
  rw [trim_measurableSet_eq _ hs]
  rfl

/-- The canonical inclusion of original classes in completed classes. -/
def completionEmbedding (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p μ →ₗᵢ[𝕜] Lp 𝕜 p (Ch02.Completion.completedMeasure μ) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 id (completion_identity_measurePreserving μ)

/-- Every completed scalar class has an original measurable representative,
which proves surjectivity of the isometric inclusion. -/
theorem completionEmbedding_surjective (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Surjective (completionEmbedding (𝕜 := 𝕜) μ p) := by
  intro g
  obtain ⟨h, hh, heq⟩ := Ch04.CompletionVersions.version_of_countablyGenerated μ
    (g : X → 𝕜) (Lp.stronglyMeasurable g).measurable
  have heq' : h =ᵐ[μ] (g : X → 𝕜) :=
    (Ch04.AeCommonException.aeEq_iff_native μ _ _).mp heq
  have hhc : MemLp h p (Ch02.Completion.completedMeasure μ) :=
    (Lp.memLp g).ae_eq heq'.symm
  have hho : MemLp h p μ := by
    change eLpNorm h p μ < ∞
    rw [← completion_trim μ]
    rw [eLpNorm_trim (m := m) (m0 := Ch02.Completion.completedSpace μ)
      le_eventuallyMeasurableSpace hh.stronglyMeasurable]
    exact hhc
  refine ⟨hho.toLp h, ?_⟩
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ (completion_identity_measurePreserving μ)).trans
    ((MemLp.coeFn_toLp hho).trans heq')

/-- Representative-preserving linear isometry of ordinary completion. -/
def completionEquiv (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p μ ≃ₗᵢ[𝕜] Lp 𝕜 p (Ch02.Completion.completedMeasure μ) :=
  LinearIsometryEquiv.ofSurjective (completionEmbedding μ p)
    (completionEmbedding_surjective μ p)

theorem completion_isometry : Specs.D11.Ch11.FinitePSeparability.completion_isometry := by
  intro X 𝕜 m _ _ _ μ p _
  refine ⟨completionEquiv μ p, ?_⟩
  intro f
  exact Lp.coeFn_compMeasurePreserving f (completion_identity_measurePreserving μ)

/-- Passing to the completion uses the representative isometry, without
assuming countable generation of that completion. -/
theorem completed_ordinary_separable [MeasurableSpace.CountablyGenerated X]
    (μ : Measure X) [SigmaFinite μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    SeparableOrdinaryLp (𝕜 := 𝕜) (m := Ch02.Completion.completedSpace μ) (Ch02.Completion.completedMeasure μ) p := by
  let : Fact (p ≠ ∞) := ⟨hp⟩
  let : SecondCountableTopology (Lp 𝕜 p (Ch02.Completion.completedMeasure μ)) :=
    (completionEquiv (𝕜 := 𝕜) μ p).symm.isometry.isEmbedding.secondCountableTopology
  exact ordinary_separable_of_native (m := Ch02.Completion.completedSpace μ)
    (Ch02.Completion.completedMeasure μ) p

/-- Borel Euclidean volume is sigma-finite on a countably generated Borel
space. Its ordinary completion therefore has separable scalar Lp spaces. -/
theorem completed_euclidean_separability :
    Specs.D11.Ch11.FinitePSeparability.completed_euclidean_separability := by
  intro n _hn 𝕜 _ _ _ p _ hp
  exact completed_ordinary_separable (𝕜 := 𝕜)
    (volume : Measure (Ch03.BorelGenerators.Space n)) p hp

end D11.Ch11.FinitePSeparability
