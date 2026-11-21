import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RepresentationPVM
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RepresentationBorelExtension

noncomputable section
open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter
open Classical

namespace ExpandedFA.SpectralMeasure.RepresentationPVM
universe u v
variable {S : Type u} {H : Type v} [TopologicalSpace S] [CompactSpace S]
  [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open FunctionSpaces.ScalarRieszMarkovSpec
open RepresentationBorelExtension

abbrev indicatorOne (B : Set S) : S → ℂ := B.indicator (fun _ => 1)

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [BorelSpace S] in
theorem indicatorOne_bounded (B : Set S) (hB : MeasurableSet B) :
    SpectralMeasure.Spec.IsBoundedMeasurable (indicatorOne B) := by
  refine ⟨measurable_const.indicator hB, 1, ?_⟩
  intro s
  by_cases hs : s ∈ B <;> simp [indicatorOne, hs]

omit [CompactSpace S] [T2Space S] [BorelSpace S] in
theorem scalarIntegral_indicatorOne (μ : ComplexMeasure S)
    (hμ : FiniteScalarRadon μ) (B : Set S) (hB : MeasurableSet B) :
    scalarIntegral μ (indicatorOne B) = μ B := by
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  rw [scalarIntegral, VectorMeasure.integral_eq_setToFun,
    setToFun_indicator_const _ hB (measure_ne_top _ _)]
  simp [VectorMeasure.transpose, ContinuousLinearMap.mul_apply']

variable (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
  (hμ : RepresentationBorelExtension.Spec.RepresentsCoefficients π μ)

abbrev projection (B : Set S) : H →L[ℂ] H :=
  borelOperator π μ hμ (indicatorOne B)

theorem projection_coefficient (B : Set S) (hB : MeasurableSet B) (x y : H) :
    ⟪x, projection π μ hμ B y⟫_ℂ = μ x y B := by
  rw [borelOperator_coefficient π μ hμ _ (indicatorOne_bounded B hB),
    scalarIntegral_indicatorOne _ (hμ.1 x y) B hB]

theorem projection_univ : projection π μ hμ univ = 1 := by
  have h : indicatorOne (univ : Set S) = ((1 : C(S, ℂ)) : S → ℂ) := by
    ext s
    simp [indicatorOne]
  rw [projection, h, borelOperator_continuous, map_one]

theorem projection_selfAdjoint (B : Set S) (hB : MeasurableSet B) :
    IsSelfAdjoint (projection π μ hμ B) := by
  have h : star (indicatorOne B) = indicatorOne B := by
    ext s
    by_cases hs : s ∈ B <;> simp [indicatorOne, hs]
  change star (borelOperator π μ hμ (indicatorOne B)) = _
  rw [← borelOperator_star π μ hμ _ (indicatorOne_bounded B hB), h]

theorem projection_inter (B C : Set S) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    projection π μ hμ B * projection π μ hμ C = projection π μ hμ (B ∩ C) := by
  have h : indicatorOne B * indicatorOne C = indicatorOne (B ∩ C) := by
    ext s
    by_cases hs : s ∈ B <;> by_cases ht : s ∈ C <;> simp [indicatorOne, hs, ht]
  rw [projection, projection, ← borelOperator_mul π μ hμ _ _
    (indicatorOne_bounded B hB) (indicatorOne_bounded C hC), h]

@[simp] theorem projection_empty : projection π μ hμ ∅ = 0 := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [projection_coefficient π μ hμ _ MeasurableSet.empty]
  simp

theorem projection_inner_left (B : Set S) (hB : MeasurableSet B) (x y : H) :
    ⟪projection π μ hμ B x, y⟫_ℂ = ⟪x, projection π μ hμ B y⟫_ℂ :=
  (projection_selfAdjoint π μ hμ B hB).isSymmetric x y

theorem projection_coefficient_diagonal (B : Set S) (hB : MeasurableSet B) (x : H) :
    (μ x x B).re = ‖projection π μ hμ B x‖ ^ 2 := by
  rw [← projection_coefficient π μ hμ B hB]
  have hid : projection π μ hμ B * projection π μ hμ B = projection π μ hμ B := by
    simpa using projection_inter π μ hμ B B hB hB
  have hi := congrArg (fun T : H →L[ℂ] H => T x) hid
  change projection π μ hμ B (projection π μ hμ B x) = projection π μ hμ B x at hi
  calc
    (⟪x, projection π μ hμ B x⟫_ℂ).re =
        (⟪projection π μ hμ B x, projection π μ hμ B x⟫_ℂ).re := by
      rw [projection_inner_left π μ hμ B hB, hi]
    _ = _ := inner_self_eq_norm_sq (𝕜 := ℂ) (projection π μ hμ B x)

/-- Scalar countable additivity plus orthogonality upgrades to norm HasSum.
The square norms are a summable scalar coefficient measure. -/
theorem projection_iUnion (B : ℕ → Set S) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (x : H) :
    HasSum (fun n => projection π μ hμ (B n) x) (projection π μ hμ (⋃ n, B n) x) := by
  let v : ℕ → H := fun n => projection π μ hμ (B n) x
  have hv : Pairwise (fun i j => ⟪v i, v j⟫_ℂ = 0) := by
    intro i j hij
    change ⟪projection π μ hμ (B i) x, projection π μ hμ (B j) x⟫_ℂ = 0
    rw [projection_inner_left π μ hμ _ (hB i)]
    have hi := congrArg (fun T : H →L[ℂ] H => T x)
      (projection_inter π μ hμ (B i) (B j) (hB i) (hB j))
    change projection π μ hμ (B i) (projection π μ hμ (B j) x) =
      projection π μ hμ (B i ∩ B j) x at hi
    rw [hi, disjoint_iff_inter_eq_empty.mp (hd hij), projection_empty]
    simp
  have hsq : Summable (fun n => ‖v n‖ ^ 2) := by
    have h := Complex.reCLM.hasSum ((μ x x).m_iUnion hB hd)
    simp only [Complex.reCLM_apply, projection_coefficient_diagonal π μ hμ _ (hB _)] at h
    exact h.summable
  let M : ℕ → Submodule ℂ H := fun i => ℂ ∙ v i
  let w : ∀ i, M i := fun i => ⟨v i, Submodule.mem_span_singleton_self (v i)⟩
  have hM : OrthogonalFamily ℂ (fun i => M i) (fun i => (M i).subtypeₗᵢ) := by
    intro i j hij a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp a.property
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp b.property
    change ⟪(a : H), (b : H)⟫_ℂ = 0
    rw [← hc, ← hd, inner_smul_left, inner_smul_right, hv hij]
    simp
  have hsum : Summable v := (hM.summable_iff_norm_sq_summable w).mpr hsq
  have hz : (∑' n, v n) = projection π μ hμ (⋃ n, B n) x := by
    apply ext_inner_left ℂ
    intro y
    have h := (innerSL ℂ y).hasSum hsum.hasSum
    have h' := (μ y x).m_iUnion hB hd
    have heq : (fun n => ⟪y, v n⟫_ℂ) = (fun n => μ y x (B n)) := by
      funext n
      exact projection_coefficient π μ hμ _ (hB n) y x
    rw [show (fun n => (innerSL ℂ y) (v n)) = (fun n => μ y x (B n)) from heq] at h
    rw [projection_coefficient π μ hμ _ (MeasurableSet.iUnion hB)]
    exact h.unique h'
  exact hz ▸ hsum.hasSum

/-- The normalized orthogonal PVM constructed from the bounded Borel extension. -/
def pvm : ProjectionValuedMeasure S H where
  toFun := projection π μ hμ
  univ := projection_univ π μ hμ
  selfAdjoint := projection_selfAdjoint π μ hμ
  inter := projection_inter π μ hμ
  iUnion := projection_iUnion π μ hμ

/-- The original regular scalar measures are precisely the PVM coefficients. -/
theorem pvm_coefficientMeasure (x y : H) :
    (pvm π μ hμ).coefficientMeasure x y = μ x y := by
  ext B hB
  rw [ProjectionValuedMeasure.coefficientMeasure_apply _ x y B hB]
  exact projection_coefficient π μ hμ B hB x y

/-- The extension agrees with the spectral integral constructed by uniform
simple approximation in the accepted PVM calculus. -/
theorem pvm_spectralIntegral_eq (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    (pvm π μ hμ).spectralIntegral g = borelOperator π μ hμ g := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ProjectionValuedMeasure.spectralIntegral_coefficient _ g hg x y,
    pvm_coefficientMeasure π μ hμ,
    borelOperator_coefficient π μ hμ g hg]
  rfl

theorem pvm_continuous_integral (f : C(S, ℂ)) :
    (pvm π μ hμ).spectralIntegral f = π f := by
  rw [pvm_spectralIntegral_eq π μ hμ f
    ⟨f.continuous.measurable, ‖f‖, f.norm_coe_le_norm⟩,
    borelOperator_continuous]

/-- Regularity and the continuous integral identity suffice for uniqueness;
no Borel extension or uniqueness certificate is assumed of the competing PVM. -/
theorem pvm_unique (F : ProjectionValuedMeasure S H) (hF : Spec.Represents F π)
    (B : Set S) (hB : MeasurableSet B) : F B = pvm π μ hμ B := by
  obtain ⟨η, hηreg, hηcoeff, hηcont⟩ := hF
  ext y
  apply ext_inner_left ℂ
  intro x
  have hη : η x y = μ x y := hμ.2.2.2 x y (η x y) (hηreg x y) (hηcont x y)
  rw [← hηcoeff x y B hB]
  change η x y B = ⟪x, projection π μ hμ B y⟫_ℂ
  rw [hη, projection_coefficient π μ hμ B hB]

theorem pvm_represents : Spec.Represents (pvm π μ hμ) π := by
  refine ⟨μ, hμ.1, ?_, hμ.2.1⟩
  intro x y B hB
  exact (projection_coefficient π μ hμ B hB x y).symm

theorem pvm_borelCalculus : Spec.BorelCalculus (pvm π μ hμ) π (borelOperator π μ hμ) := by
  refine ⟨borelOperator_continuous π μ hμ, ?_, ?_, borelOperator_add π μ hμ,
    borelOperator_smul π μ hμ, borelOperator_mul π μ hμ,
    borelOperator_star π μ hμ, ?_⟩
  · intro B _
    rfl
  · change borelOperator π μ hμ ((1 : C(S, ℂ)) : S → ℂ) = 1
    rw [borelOperator_continuous, map_one]
  · intro f C hf hC hbound
    exact borelOperator_norm_le π μ hμ f hf C hC hbound

/-- Representations of C(S) give unique regular Borel PVMs and extend to all
bounded Borel functions as contractive unital complex *-homomorphisms. -/
theorem representations_give_pvms : Spec.RepresentationTheorem.{u, v} := by
  intro S H _ _ _ _ _ _ _ _ π
  obtain ⟨μ, hμ⟩ := RepresentationBorelExtension.scalar_measures S H π
  refine ⟨pvm π μ hμ, μ, borelOperator π μ hμ, hμ, ?_,
    pvm_borelCalculus π μ hμ, ?_, pvm_unique π μ hμ⟩
  · intro x y B hB
    exact (projection_coefficient π μ hμ B hB x y).symm
  · intro g hg x y
    exact ⟨bounded_borel_integrable _ (hμ.1 x y) g hg,
      borelOperator_coefficient π μ hμ g hg x y⟩

end ExpandedFA.SpectralMeasure.RepresentationPVM
