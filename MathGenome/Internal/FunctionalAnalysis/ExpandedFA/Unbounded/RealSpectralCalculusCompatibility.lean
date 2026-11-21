import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealSpectralCalculusCompatibility
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.RealSpectralProductAndSumDomains
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SpectralProductAndSumDomains

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal NNReal
namespace ExpandedFA.Unbounded.RealSpectralCalculusCompatibility
open ExpandedFA.SpectralMeasure
universe u v
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def toGeneralPVM : Spec.ToGeneralType.{v} := Spec.ToGeneralValue

def toHalfLinePVM : Spec.ToHalfLineType.{v} := Spec.ToHalfLineValue

theorem toHalfLine_toGeneral (E : RealNonnegativeSpectralCalculus.ProjectionValuedMeasure H) :
    toHalfLinePVM (toGeneralPVM E) = E := by cases E; rfl

theorem toGeneral_toHalfLine (E : RealProjectionValuedMeasure ℝ≥0 H) :
    toGeneralPVM (toHalfLinePVM E) = E := by cases E; rfl

def pvmEquiv : RealNonnegativeSpectralCalculus.ProjectionValuedMeasure H ≃ RealProjectionValuedMeasure ℝ≥0 H where
  toFun := toGeneralPVM
  invFun := toHalfLinePVM
  left_inv := toHalfLine_toGeneral
  right_inv := toGeneral_toHalfLine

theorem pvm_equivalence : Spec.PVMEquivalence.{v} := by
  intro H _ _ _
  exact ⟨pvmEquiv, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Use the bounded calculus constructed from the converted PVM itself. -/
def generalRealization (C : RealNonnegativeSpectralCalculus.Calculus (H := H)) :
    RealBoundedRealization (toGeneralPVMValue C.E) :=
  (toGeneralPVMValue C.E).boundedRealization

theorem scalar_eq (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E)) (x : H) :
    D.scalar x = C.measure x := by
  ext B hB
  rw [D.scalar_apply x B hB, C.measure_apply x B hB]
  congr 1
  exact ((toGeneralPVMValue C.E).inner_self_projected hB x).symm

theorem coefficient_eq (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E)) (x y : H) :
    D.coefficient x y = C.coefficient x y := by
  apply VectorMeasure.ext
  intro B hB
  rw [D.coefficient_apply x y B hB, C.coefficient_apply x y B hB]
  rfl

theorem bounded_measurable (f : RealBoundedFunction ℝ≥0) :
    RealNonnegativeSpectralCalculus.IsBoundedMeasurable f :=
  ⟨f.measurable, f.bounded.choose, f.bounded.choose_spec.2⟩

theorem bounded_eq (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E)) (f : RealBoundedFunction ℝ≥0) :
    D.integral f = C.bounded f := by
  have hf := bounded_measurable f
  have hb := C.bounded_agrees f hf
  ext y
  apply ext_inner_left ℝ
  intro x
  have hy : y ∈ (C.integral f).domain := by rw [hb]; trivial
  have hi := C.inner_integral f f.measurable x ⟨y, hy⟩
  have hv := (LinearPMap.ext_iff.mp hb).2 (x := y) (hf := hy) (hg := Submodule.mem_top)
  change C.integral f ⟨y, hy⟩ = C.bounded f y at hv
  rw [hv] at hi
  rw [D.coefficient_integral, coefficient_eq C D]
  exact hi.symm


/-- The old bounded integral is the identical finite-fibre sum. -/
theorem bounded_simple (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E)) (a : SimpleFunc ℝ≥0 ℝ) :
    C.bounded a = realSimpleSpectralIntegral (toGeneralPVMValue C.E) a := by
  exact (bounded_eq C D (.ofSimple a)).symm.trans (D.integral_simple a)

/-- This pins down the old calculus by the same uniform simple-limit
characterization used to construct the new bounded calculus. -/
theorem bounded_uniform_limit (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E)) (f : RealBoundedFunction ℝ≥0)
    (a : ℕ → SimpleFunc ℝ≥0 ℝ)
    (ha : TendstoUniformly (fun n => (a n : ℝ≥0 → ℝ)) f atTop) :
    Tendsto (fun n => C.bounded (a n)) atTop (𝓝 (C.bounded f)) := by
  have h := D.integral_uniform_limit f a ha
  simpa only [bounded_eq C D f, ← bounded_simple C D] using h

theorem truncation_eq (f : ℝ≥0 → ℝ) (hf : Measurable f) (n : ℕ) :
    (RealMeasurableSpectralCalculus.truncation f hf n : ℝ≥0 → ℝ) = RealNonnegativeSpectralCalculus.truncation f n := rfl

theorem truncatedOperator_eq (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E))
    (f : ℝ≥0 → ℝ) (hf : Measurable f) (n : ℕ) :
    RealMeasurableSpectralCalculus.truncatedOperator D f hf n = C.bounded (RealNonnegativeSpectralCalculus.truncation f n) :=
  bounded_eq C D (RealMeasurableSpectralCalculus.truncation f hf n)

theorem square_integrability_eq (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E)) (f : ℝ≥0 → ℝ) (x : H) :
    RealMeasurableSpectralCalculus.squareMoment D f x < ∞ ↔ RealNonnegativeSpectralCalculus.SquareIntegrable (C.measure x) f := by
  simp only [RealMeasurableSpectralCalculus.squareMoment, RealNonnegativeSpectralCalculus.SquareIntegrable, scalar_eq C D]

/-- Both maximal domains are the actual square-integrability domain. -/
theorem domain_eq (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E))
    (f : ℝ≥0 → ℝ) (hf : Measurable f) :
    (RealMeasurableSpectralCalculus.measurableIntegral D f hf).domain = (C.integral f).domain := by
  ext x
  exact (RealMeasurableSpectralCalculus.maximal_domain D f hf x).trans
    ((square_integrability_eq C D f x).trans (C.domain f hf x).symm)

/-- Equality as partial linear maps, proved by uniqueness of the same norm
limits on the common maximal domain. -/
theorem integral_eq (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E))
    (f : ℝ≥0 → ℝ) (hf : Measurable f) :
    RealMeasurableSpectralCalculus.measurableIntegral D f hf = C.integral f := by
  apply LinearPMap.ext (domain_eq C D f hf)
  intro x hx hy
  have h := RealMeasurableSpectralCalculus.truncations_converge D f hf ⟨x, hx⟩
  simp only [truncatedOperator_eq C D] at h
  exact tendsto_nhds_unique h (C.truncation_limit f hf ⟨x, hy⟩)

theorem calculus_compatibility : Spec.CalculusCompatibility.{v} := by
  intro H _ _ _ C
  let D := generalRealization C
  exact ⟨D, scalar_eq C D, coefficient_eq C D, bounded_eq C D,
    bounded_simple C D, bounded_uniform_limit C D,
    fun f hf n => ⟨truncation_eq f hf n, truncatedOperator_eq C D f hf n⟩,
    square_integrability_eq C D, integral_eq C D⟩

theorem halfLine_domain_laws : Spec.HalfLineDomainLaws.{v} := by
  intro H _ _ _ C f g hf hg
  let D := generalRealization C
  change (OperatorDomainsSpec.productValue (C.integral f) (C.integral g)).domain =
    (C.integral g).domain ⊓ (C.integral (f * g)).domain ∧
    OperatorDomainsSpec.productValue (C.integral f) (C.integral g) ≤ C.integral (f * g) ∧
    (OperatorDomainsSpec.productValue (C.integral f) (C.integral g)).IsClosable ∧
    (OperatorDomainsSpec.productValue (C.integral f) (C.integral g)).closure = C.integral (f * g) ∧
    (C.integral f + C.integral g).IsClosable ∧
    (C.integral f + C.integral g).closure = C.integral (f + g)
  rw [← integral_eq C D f hf, ← integral_eq C D g hg,
    ← integral_eq C D (f * g) (hf.mul hg), ← integral_eq C D (f + g) (hf.add hg)]
  exact ⟨(RealSpectralProductAndSumDomains.product_law D f g hf hg).1,
    (RealSpectralProductAndSumDomains.product_law D f g hf hg).2,
    (RealSpectralProductAndSumDomains.product_closure D f g hf hg).1,
    (RealSpectralProductAndSumDomains.product_closure D f g hf hg).2,
    RealSpectralProductAndSumDomains.sum_closure D f g hf hg⟩

theorem full_scalar_bounded_theorem : Spec.FullScalarBoundedTheorem.{u,v} := by
  refine ⟨?_, RealDefinitions.projection_properties,
    RealDefinitions.ordered_additivity_equivalence, RealDefinitions.bounded_realization_exists⟩
  intro S H _ _ _ _
  refine ⟨SpectralMeasure.source_realization, ?_, ?_, ?_, ?_,
    SpectralMeasure.scalar_measures, SpectralMeasure.functional_calculus⟩
  · intro E; exact E.map_empty
  · intro E B hB
    exact ⟨E.selfAdjoint B hB, E.idempotent B hB, E.norm_le_one B hB, E.norm_apply_le B hB⟩
  · intro E B hB x y
    exact E.coefficient_projection B hB x y
  · intro E B F hB hF hd x y
    exact E.orthogonality B F hB hF hd x y

theorem full_scalar_unbounded_theorem : Spec.FullScalarUnboundedTheorem.{u,v} :=
  ⟨⟨MeasurableSpectralCalculus.measurable_spectral_calculus,
    MeasurableSpectralCalculus.exists_measurable_spectral_calculus,
    SpectralProductAndSumDomains.product_rule, SpectralProductAndSumDomains.product_closure,
    SpectralProductAndSumDomains.sum_closure, SpectralProductAndSumDomains.strict_domain_example⟩,
   ⟨RealMeasurableSpectralCalculus.calculus_for_every_realization, RealMeasurableSpectralCalculus.calculus_exists,
    RealSpectralProductAndSumDomains.complete_theorem⟩⟩

end ExpandedFA.Unbounded.RealSpectralCalculusCompatibility
