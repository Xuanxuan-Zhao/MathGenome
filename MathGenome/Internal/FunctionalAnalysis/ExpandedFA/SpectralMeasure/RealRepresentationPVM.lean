import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealRepresentationPVM
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RealRepresentationBorelExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RealDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RepresentationPVM

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open Classical

namespace ExpandedFA.SpectralMeasure.RealRepresentationPVM
universe u v
open FunctionSpaces.ScalarRieszMarkovSpec
open RealRepresentationBorelExtension
variable {S : Type u} {H : Type v} [TopologicalSpace S] [CompactSpace S]
  [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev indicatorOne (B : Set S) : S → ℝ := B.indicator (fun _ => 1)

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [BorelSpace S] in
lemma indicatorOne_bounded (B : Set S) (hB : MeasurableSet B) :
    RealRepresentationBorelExtension.Spec.IsBoundedBorel (indicatorOne B) :=
  ⟨measurable_const.indicator hB, 1, zero_le_one,
    fun s => by by_cases hs : s ∈ B <;> simp [indicatorOne, hs]⟩

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [BorelSpace S] in
lemma scalarIntegral_indicatorOne (ν : VectorMeasure S ℝ) [IsFiniteMeasure ν.variation]
    (B : Set S) (hB : MeasurableSet B) : scalarIntegral ν (indicatorOne B) = ν B := by
  rw [scalarIntegral, VectorMeasure.integral_eq_setToFun,
    setToFun_indicator_const _ hB (measure_ne_top _ _)]
  simp [VectorMeasure.transpose, ContinuousLinearMap.mul_apply']

variable (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))

/-- Projections are the actual Borel extension at indicators. -/
abbrev projection (B : Set S) : H →L[ℝ] H := borelOperator π (indicatorOne B)

lemma projection_coefficient (B : Set S) (hB : MeasurableSet B) (x y : H) :
    ⟪x, projection π B y⟫_ℝ = coefficientMeasure π x y B := by
  rw [borelOperator_inner π (indicatorOne_bounded B hB), scalarIntegral_indicatorOne _ B hB]

lemma projection_univ : projection π univ = 1 := by
  simpa [projection, indicatorOne] using borelOperator_one π

lemma projection_selfAdjoint (B : Set S) (hB : MeasurableSet B) (x y : H) :
    ⟪projection π B x, y⟫_ℝ = ⟪x, projection π B y⟫_ℝ :=
  (show IsSelfAdjoint (projection π B) from
    borelOperator_selfAdjoint π (indicatorOne_bounded B hB)).isSymmetric x y

lemma projection_inter (B C : Set S) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    projection π B * projection π C = projection π (B ∩ C) := by
  have h : (fun s => indicatorOne B s * indicatorOne C s) = indicatorOne (B ∩ C) := by
    funext s
    by_cases hs : s ∈ B <;> by_cases ht : s ∈ C <;> simp [indicatorOne, hs, ht]
  rw [projection, projection, ← borelOperator_mul π
    (indicatorOne_bounded B hB) (indicatorOne_bounded C hC), h]

@[simp] lemma projection_empty : projection π ∅ = 0 := by
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [projection_coefficient π _ MeasurableSet.empty]
  simp

lemma projection_diagonal (B : Set S) (hB : MeasurableSet B) (x : H) :
    coefficientMeasure π x x B = ‖projection π B x‖ ^ 2 := by
  rw [← projection_coefficient π B hB]
  have hid : projection π B * projection π B = projection π B := by
    simpa using projection_inter π B B hB hB
  have hi := congrArg (fun T : H →L[ℝ] H => T x) hid
  change projection π B (projection π B x) = projection π B x at hi
  rw [← hi, ← projection_selfAdjoint π B hB, real_inner_self_eq_norm_sq, hi]

/-- Orthogonality and scalar countable additivity give unconditional norm
summability, without a scalar control measure or a countability assumption. -/
lemma projection_iUnion (B : ℕ → Set S) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (x : H) :
    HasSum (fun n => projection π (B n) x) (projection π (⋃ n, B n) x) := by
  let v : ℕ → H := fun n => projection π (B n) x
  have hv : Pairwise (fun i j => ⟪v i, v j⟫_ℝ = 0) := by
    intro i j hij
    change ⟪projection π (B i) x, projection π (B j) x⟫_ℝ = 0
    rw [projection_selfAdjoint π _ (hB i)]
    have hi := congrArg (fun T : H →L[ℝ] H => T x)
      (projection_inter π (B i) (B j) (hB i) (hB j))
    change projection π (B i) (projection π (B j) x) = projection π (B i ∩ B j) x at hi
    rw [hi, disjoint_iff_inter_eq_empty.mp (hd hij), projection_empty]
    simp
  have hsq : Summable (fun n => ‖v n‖ ^ 2) := by
    have h := (coefficientMeasure π x x).m_iUnion hB hd
    simp only [projection_diagonal π _ (hB _)] at h
    exact h.summable
  let M : ℕ → Submodule ℝ H := fun i => ℝ ∙ v i
  let w : ∀ i, M i := fun i => ⟨v i, Submodule.mem_span_singleton_self (v i)⟩
  have hM : OrthogonalFamily ℝ (fun i => M i) (fun i => (M i).subtypeₗᵢ) := by
    intro i j hij a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp a.property
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp b.property
    change ⟪(a : H), (b : H)⟫_ℝ = 0
    rw [← hc, ← hd, inner_smul_left, inner_smul_right, hv hij]
    simp
  have hsum : Summable v := (hM.summable_iff_norm_sq_summable w).mpr hsq
  have hz : (∑' n, v n) = projection π (⋃ n, B n) x := by
    apply ext_inner_left ℝ
    intro y
    have h := (innerSL ℝ y).hasSum hsum.hasSum
    have heq : (fun n => (innerSL ℝ y) (v n)) =
        (fun n => coefficientMeasure π y x (B n)) := by
      funext n
      exact projection_coefficient π _ (hB n) y x
    rw [heq] at h
    rw [projection_coefficient π _ (MeasurableSet.iUnion hB)]
    exact h.unique ((coefficientMeasure π y x).m_iUnion hB hd)
  exact hz ▸ hsum.hasSum

def pvm : RealProjectionValuedMeasure S H where
  toFun := projection π
  univ := projection_univ π
  selfAdjoint := projection_selfAdjoint π
  inter := projection_inter π
  countablyAdditive := projection_iUnion π

/-- Every bounded realization has the same actual signed coefficients. -/
lemma realization_coefficient (C : RealBoundedRealization (pvm π)) (x y : H) :
    C.coefficient x y = coefficientMeasure π x y := by
  ext B hB
  rw [C.coefficient_apply x y B hB]
  exact projection_coefficient π B hB x y

/-- Identifying coefficients identifies all bounded integrals, not just the
continuous calculus or an almost-everywhere quotient. -/
lemma realization_integral (C : RealBoundedRealization (pvm π))
    (g : RealBoundedFunction S) : C.integral g = borelOperator π g := by
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [C.coefficient_integral, realization_coefficient π C]
  exact (borelOperator_inner π ⟨g.measurable, g.bounded⟩ x y).symm

lemma realization_scalar (C : RealBoundedRealization (pvm π)) (x : H) :
    C.scalar x = (coefficientMeasure π x x).variation := by
  letI := C.scalar_finite x
  rw [← realization_coefficient π C x x, C.coefficient_diagonal,
    Measure.variation_toSignedMeasure]

lemma realization_regular (C : RealBoundedRealization (pvm π)) (x : H) :
    Measure.Regular (C.scalar x) := by
  rw [realization_scalar π C]
  exact (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp
    (coefficientMeasure_represents π x x).1.2

lemma pvm_represents (C : RealBoundedRealization (pvm π)) :
    Spec.Represents (pvm π) C π := by
  constructor
  · intro x y
    rw [realization_coefficient π C]
    exact (coefficientMeasure_represents π x y).1
  · intro f
    rw [realization_integral π C]
    exact borelOperator_continuous π f

/-- Regularity and the continuous integral identity suffice for uniqueness.
No extension identity is imposed on a competing PVM or realization. -/
lemma pvm_unique (F : RealProjectionValuedMeasure S H)
    (D : RealBoundedRealization F) (hD : Spec.Represents F D π)
    (B : Set S) (hB : MeasurableSet B) : F B = pvm π B := by
  have hm (x y : H) : D.coefficient x y = coefficientMeasure π x y := by
    apply coefficient_unique π x y ?_ (coefficientMeasure_represents π x y)
    refine ⟨hD.1 x y, ?_⟩
    intro f
    let g : RealBoundedFunction S :=
      ⟨f, f.continuous.measurable, ‖f‖, norm_nonneg _, f.norm_coe_le_norm⟩
    refine ⟨D.coefficient_integrable g x y, ?_⟩
    rw [← hD.2 f]
    exact D.coefficient_integral g x y
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [← D.coefficient_apply x y B hB, hm]
  exact (projection_coefficient π B hB x y).symm

/-- The full real representation theorem on the original H. -/
theorem real_representations_give_pvms : Spec.RealRepresentationTheorem.{u, v} := by
  intro S H _ _ _ _ _ _ _ _ π
  let C := (pvm π).boundedRealization
  refine ⟨pvm π, C, coefficientMeasure π, borelOperator π,
    coefficientMeasure_system π, borelOperator_extension π, ?_,
    realization_coefficient π C, realization_scalar π C,
    realization_regular π C, pvm_represents π C, realization_integral π C,
    pvm_unique π⟩
  intro B _
  rfl

/-- Complete real and complex scalar coverage of the manuscript theorem. -/
theorem full_scalar_representations_give_pvms :
    Spec.FullScalarRepresentationTheorem.{u, v} :=
  ⟨real_representations_give_pvms, RepresentationPVM.representations_give_pvms⟩

end ExpandedFA.SpectralMeasure.RealRepresentationPVM
