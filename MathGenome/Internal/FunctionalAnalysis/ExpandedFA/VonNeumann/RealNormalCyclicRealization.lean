import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalCyclicRealization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.RealNormalControlMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.CyclicModel

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
namespace ExpandedFA.VonNeumann.RealNormalCyclicRealization
universe u
open TraceIdeals.RealComplexification
open RealAbelianComplexification.Spec.NativeLp
namespace Target
abbrev complexCyclicSpace := @RealNormalControlTopology.Spec.complexCyclicSpace
abbrev realCyclicSpace := @RealNormalControlTopology.Spec.realCyclicSpace
end Target
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

/-- The supplied measure is the actual, unnormalized diagonal measure. -/
theorem measure_eq {N : H →L[ℝ] H} (C : RealNormalControlMeasure.Spec.AlgebraModel N) :
    C.μ = C.E.diagonalMeasure (inclusion C.e) := by
  apply Measure.ext
  intro B hB
  exact (C.vectorMeasure B hB).trans (C.E.diagonalMeasure_apply _ B hB).symm

section Transport
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : K →L[ℂ] K} (hT : IsStarNormal T)
  (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ T) K)
  (hE : SpectralMeasure.NormalPVM.Spec.Resolves T E) (e : K)
  (μ : Measure (spectrum ℂ T)) (hμ : μ = E.diagonalMeasure e)

/-- Transport the upstream vector model along equality of measures. -/
def embedding : Lp ℂ 2 μ →ₗᵢ[ℂ] K := by
  subst μ
  exact NormalAlgebraControlMeasure.vectorModel hT E hE e

theorem embedding_continuous [IsFiniteMeasure μ] (f : C(spectrum ℂ T, ℂ)) :
    embedding hT E hE e μ hμ (ContinuousMap.toLp 2 μ ℂ f) = E.spectralIntegral f e := by
  subst μ
  exact NormalAlgebraControlMeasure.vectorModel_continuous hT E hE e f

theorem embedding_intertwines [IsFiniteMeasure μ] (h : Lp ℂ ∞ μ)
    {f : spectrum ℂ T → ℂ} (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (heq : f =ᵐ[μ] h) (v : Lp ℂ 2 μ) :
    embedding hT E hE e μ hμ (ScalarMultiplicationCommutant.Spec.multiplier μ h v) =
      E.spectralIntegral f (embedding hT E hE e μ hμ v) := by
  subst μ
  exact NormalAlgebraControlMeasure.vectorModel_intertwines hT E hE e h hf heq v

theorem embedding_range_invariant {f : spectrum ℂ T → ℂ}
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (x : K)
    (hx : x ∈ (embedding hT E hE e μ hμ).toLinearMap.range) :
    E.spectralIntegral f x ∈ (embedding hT E hE e μ hμ).toLinearMap.range := by
  subst μ
  exact NormalAlgebraControlMeasure.vectorModel_range_invariant hT E hE e hf x hx
end Transport

variable {N : H →L[ℝ] H} (hN : IsStarNormal N)
  (C : RealNormalControlMeasure.Spec.AlgebraModel N)

/-- The embedding uses precisely C's original measure. -/
def complexEmbedding : Lp ℂ 2 C.μ →ₗᵢ[ℂ] Space H :=
  embedding (SpectralMeasure.RealFugledePutnam.operator_normal N hN)
    C.E C.resolves (inclusion C.e) C.μ (measure_eq C)

lemma complexEmbedding_continuous (f : C(RealNormalControlMeasure.Spec.Spectrum N, ℂ)) :
    letI := C.finite
    complexEmbedding hN C (ContinuousMap.toLp 2 C.μ ℂ f) = C.Φ f (inclusion C.e) := by
  letI := C.finite
  rw [complexEmbedding, embedding_continuous,
    SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus f
      (SpectralMeasure.NormalPVM.continuous_bounded f)]

lemma complexEmbedding_one :
    letI := C.finite
    complexEmbedding hN C (ContinuousMap.toLp 2 C.μ ℂ 1) = inclusion C.e := by
  letI := C.finite
  rw [complexEmbedding, embedding_continuous]
  change C.E.spectralIntegral (fun _ => 1) _ = _
  rw [C.E.spectralIntegral_one]
  rfl

lemma complexEmbedding_intertwines (f : C(RealNormalControlMeasure.Spec.Spectrum N, ℂ))
    (v : Lp ℂ 2 C.μ) :
    letI := C.finite
    complexEmbedding hN C (SpectralMeasure.CyclicModel.Spec.multiplier C.μ f v) =
      C.Φ f (complexEmbedding hN C v) := by
  letI := C.finite
  rw [SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus f
      (SpectralMeasure.NormalPVM.continuous_bounded f)]
  exact embedding_intertwines _ _ _ _ _ _ _
    (SpectralMeasure.NormalPVM.continuous_bounded f)
    (ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) C.μ f).symm v

lemma complexEmbedding_range_closed :
    IsClosed ((complexEmbedding hN C).toLinearMap.range : Set (Space H)) :=
  (complexEmbedding hN C).isometry.isClosedEmbedding.isClosed_range

/-- The range agrees with the specified closed cyclic space, even when the
ambient representation has arbitrary multiplicity. -/
lemma complexEmbedding_range :
    (complexEmbedding hN C).toLinearMap.range = Target.complexCyclicSpace N C.e := by
  letI := C.finite
  let hNC := SpectralMeasure.RealFugledePutnam.operator_normal N hN
  have hcfc (f : C(RealNormalControlMeasure.Spec.Spectrum N, ℂ)) :
      C.Φ f = cfcHom hNC f := by
    rw [SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus f
      (SpectralMeasure.NormalPVM.continuous_bounded f)]
    exact congrArg (fun π : C(RealNormalControlMeasure.Spec.Spectrum N, ℂ) →⋆ₐ[ℂ]
      (Space H →L[ℂ] Space H) => π f)
      (SpectralMeasure.CyclicModel.continuousIntegral_eq_cfcHom _ hNC C.E C.resolves)
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    refine (SpectralMeasure.CyclicModel.continuous_density (Space H) (operator N) C.μ).induction_on
      (p := fun v => complexEmbedding hN C v ∈ Target.complexCyclicSpace N C.e) v ?_ ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage (complexEmbedding hN C).continuous
    · intro f
      rw [complexEmbedding_continuous, hcfc]
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      have hf : cfcHom hNC f ∈ StarAlgebra.elemental ℂ (operator N) := by
        rw [← range_cfcHom ℂ hNC]
        exact ⟨f, rfl⟩
      exact ⟨⟨_, hf⟩, rfl⟩
  · apply Submodule.topologicalClosure_minimal _ ?_ (complexEmbedding_range_closed hN C)
    apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    have ha : (a : Space H →L[ℂ] Space H) ∈ (cfcHom (R := ℂ) hNC).range := by
      rw [range_cfcHom ℂ hNC]
      exact a.property
    obtain ⟨f, hf⟩ := ha
    refine ⟨ContinuousMap.toLp 2 C.μ ℂ f, ?_⟩
    change complexEmbedding hN C (ContinuousMap.toLp 2 C.μ ℂ f) =
      (a : Space H →L[ℂ] Space H) (inclusion C.e)
    rw [complexEmbedding_continuous, hcfc]
    exact congrArg (fun A : Space H →L[ℂ] Space H => A (inclusion C.e)) hf

/-- Continuous conjugate pullback is represented by the same pointwise formula. -/
lemma conjugatePullback_toLp (f : C(RealNormalControlMeasure.Spec.Spectrum N, ℂ)) :
    letI := C.finite
    conjugatePullback C.involutionData (ContinuousMap.toLp 2 C.μ ℂ f) =
      ContinuousMap.toLp 2 C.μ ℂ (star (f.comp ⟨C.τ, C.τ.continuous⟩)) := by
  letI := C.finite
  apply Lp.ext
  filter_upwards [coeFn_conjugatePullback C.involutionData
      (ContinuousMap.toLp 2 C.μ ℂ f),
    C.measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) C.μ f),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) C.μ (star (f.comp ⟨C.τ, C.τ.continuous⟩))]
    with x hx hf hg
  exact hx.trans ((congrArg star hf).trans hg.symm)

/-- Equivariance holds on all L² classes, not just continuous symbols. -/
lemma complexEmbedding_conjugation (v : Lp ℂ 2 C.μ) :
    complexEmbedding hN C (conjugatePullback C.involutionData v) =
      conjugation (complexEmbedding hN C v) := by
  letI := C.finite
  refine (SpectralMeasure.CyclicModel.continuous_density (Space H) (operator N) C.μ).induction_on
    (p := fun v => complexEmbedding hN C (conjugatePullback C.involutionData v) =
      conjugation (complexEmbedding hN C v)) v ?_ ?_
  · exact isClosed_eq ((complexEmbedding hN C).continuous.comp
      (isometry_conjugatePullback C.involutionData).continuous)
      (conjugation.continuous.comp (complexEmbedding hN C).continuous)
  · intro f
    rw [conjugatePullback_toLp]
    simp only [complexEmbedding, embedding_continuous]
    have hh := congrArg (fun A : Space H →L[ℂ] Space H => A (inclusion C.e))
      (SpectralMeasure.RealFugledePutnam.integral_conjugation N C.E C.resolves f
        (SpectralMeasure.NormalPVM.continuous_bounded f))
    rw [← RealNormalControlMeasure.tau_eq N C.toSpectralControl] at hh
    have hj : conjugation (inclusion C.e) = inclusion C.e := by
      change (C.e, -(0 : H)) = (C.e, 0)
      simp
    simp only [SpectralMeasure.RealFugledePutnam.conjugateOperator_apply, hj] at hh
    convert hh.symm using 1
    apply congrArg (fun g : RealNormalControlMeasure.Spec.Spectrum N → ℂ =>
      C.E.spectralIntegral g (inclusion C.e))
    ext z
    rfl

lemma complexEmbedding_projection (B : Set (RealNormalControlMeasure.Spec.Spectrum N))
    (hB : MeasurableSet B) (s : (complexEmbedding hN C).toLinearMap.range) :
    C.E B s ∈ (complexEmbedding hN C).toLinearMap.range := by
  rw [← SpectralMeasure.BorelNormSpectrum.integral_indicator_one C.E B hB]
  exact embedding_range_invariant _ _ _ _ _ _
    (SpectralMeasure.BorelNormSpectrum.bounded_indicator B hB
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1)) s s.property

/-- The genuine surjective complex unitary onto the canonical cyclic space. -/
def complexUnitary : Lp ℂ 2 C.μ ≃ₗᵢ[ℂ] Target.complexCyclicSpace N C.e :=
  (complexEmbedding hN C).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (complexEmbedding_range hN C))

@[simp] lemma complexUnitary_coe (v : Lp ℂ 2 C.μ) :
    (complexUnitary hN C v : Space H) = complexEmbedding hN C v := rfl

/-- All native fixed multipliers intertwine before restricting the real form. -/
lemma complexEmbedding_fixed_multiplier (f : Fixed C.involutionData ∞)
    (v : Fixed C.involutionData 2) :
    complexEmbedding hN C (restrictedMultiplier C.involutionData f v).val =
      operator (C.Ψ f : H →L[ℝ] H) (complexEmbedding hN C v.val) := by
  letI := C.finite
  obtain ⟨g, hg, hgc, hge⟩ := C.representatives f
  have hop : operator (C.Ψ f : H →L[ℝ] H) = C.Φ g :=
    (C.on_representatives f g hg hgc hge).2
  calc
    _ = C.E.spectralIntegral g (complexEmbedding hN C v.val) :=
      embedding_intertwines _ _ _ _ _ _ f.val hg hge v.val
    _ = _ := congrArg (fun A : Space H →L[ℂ] Space H => A (complexEmbedding hN C v.val))
      ((SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus g hg).symm.trans hop.symm)

section RealCyclicBridge
open RealAbelianComplexification
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification (csmul)

/-- Complexification is isometric also for the operator norm. -/
def operatorIsometry : (H →L[ℝ] H) →ₗᵢ[ℝ] (Space H →L[ℂ] Space H) where
  toFun := operator
  map_add' := operator_add
  map_smul' := operator_real_smul
  norm_map' := operator_norm

lemma coordinate_norm_le (p : Space H) : ‖p.1‖ ≤ ‖p‖ ∧ ‖p.2‖ ≤ ‖p‖ := by
  have h := TraceIdeals.RealComplexification.Spec.norm_sq p
  constructor <;> nlinarith [norm_nonneg p, norm_nonneg p.1, norm_nonneg p.2,
    sq_nonneg ‖p.1‖, sq_nonneg ‖p.2‖]

/-- Coordinate extraction is continuous in the operator norm. -/
def operatorRealPartCLM : (Space H →L[ℂ] Space H) →L[ℝ] (H →L[ℝ] H) :=
  ({ toFun := operatorRealPart
     map_add' := fun _ _ => rfl
     map_smul' := by
       intro r A
       ext x
       change operatorRealPart ((r : ℂ) • A) x = r • operatorRealPart A x
       rw [RealAbelianComplexification.realPart_smul]
       simp } :
    (Space H →L[ℂ] Space H) →ₗ[ℝ] (H →L[ℝ] H)).mkContinuous 1 (by
      intro A
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
      intro x
      exact (coordinate_norm_le (A (inclusion x))).1.trans
        (by simpa only [inclusion.norm_map] using A.le_opNorm (inclusion x)))

def operatorImagPartCLM : (Space H →L[ℂ] Space H) →L[ℝ] (H →L[ℝ] H) :=
  ({ toFun := operatorImagPart
     map_add' := fun _ _ => rfl
     map_smul' := by
       intro r A
       ext x
       change operatorImagPart ((r : ℂ) • A) x = r • operatorImagPart A x
       rw [RealAbelianComplexification.imagPart_smul]
       simp } :
    (Space H →L[ℂ] Space H) →ₗ[ℝ] (H →L[ℝ] H)).mkContinuous 1 (by
      intro A
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
      intro x
      exact (coordinate_norm_le (A (inclusion x))).2.trans
        (by simpa only [inclusion.norm_map] using A.le_opNorm (inclusion x)))

lemma complex_elemental_coordinates (a : Space H →L[ℂ] Space H)
    (ha : a ∈ StarAlgebra.elemental ℂ (operator N)) :
    operatorRealPart a ∈ StarAlgebra.elemental ℝ N ∧
      operatorImagPart a ∈ StarAlgebra.elemental ℝ N := by
  have hc : IsClosed (complexAlgebra (StarAlgebra.elemental ℝ N) : Set (Space H →L[ℂ] Space H)) := by
    have h := (StarAlgebra.elemental.isClosed ℝ N).preimage
      (operatorRealPartCLM (H := H)).continuous
    have h' := (StarAlgebra.elemental.isClosed ℝ N).preimage
      (operatorImagPartCLM (H := H)).continuous
    convert h.inter h' using 1
    ext A
    exact mem_complexAlgebra _ A
  have hn : operator N ∈ complexAlgebra (StarAlgebra.elemental ℝ N) := by
    apply (mem_complexAlgebra _ _).mpr
    simp only [realPart_operator, imagPart_operator]
    exact ⟨StarAlgebra.elemental.self_mem ℝ N, zero_mem _⟩
  exact (mem_complexAlgebra _ _).mp ((StarAlgebra.elemental.le_of_mem hc hn) ha)

lemma operator_mem_complex_elemental (a : H →L[ℝ] H)
    (ha : a ∈ StarAlgebra.elemental ℝ N) :
    operator a ∈ StarAlgebra.elemental ℂ (operator N) := by
  have hclosed := (StarAlgebra.elemental.isClosed ℂ (operator N)).preimage
    (operatorIsometry (H := H)).continuous
  refine closure_minimal (s := (StarAlgebra.adjoin ℝ {N} : Set (H →L[ℝ] H)))
    (t := (operatorIsometry (H := H)) ⁻¹'
      (StarAlgebra.elemental ℂ (operator N) : Set (Space H →L[ℂ] Space H))) ?_ hclosed ha
  intro b hb
  apply StarSubalgebra.le_topologicalClosure
  rw [← generated_algebra N]
  change operator b ∈ complexAlgebra (StarAlgebra.adjoin ℝ {N})
  exact (mem_complexAlgebra _ _).mpr ⟨by simpa using hb, by simp⟩

/-- The real cyclic space complexifies to a closed complex subspace. -/
def realCyclicComplexification (N : H →L[ℝ] H) (e : H) : Submodule ℂ (Space H) where
  carrier := {p | p.1 ∈ Target.realCyclicSpace N e ∧ p.2 ∈ Target.realCyclicSpace N e}
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  add_mem' hp hq := ⟨add_mem hp.1 hq.1, add_mem hp.2 hq.2⟩
  smul_mem' a p hp := by
    rw [csmul]
    exact ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ hp.1) (Submodule.smul_mem _ _ hp.2),
      add_mem (Submodule.smul_mem _ _ hp.1) (Submodule.smul_mem _ _ hp.2)⟩

lemma realCyclicComplexification_closed (e : H) :
    IsClosed (realCyclicComplexification N e : Set (Space H)) :=
  ((Submodule.isClosed_topologicalClosure _).preimage realPart.continuous).inter
    ((Submodule.isClosed_topologicalClosure _).preimage imagPart.continuous)

lemma complexCyclic_coordinates (e : H) :
    Target.complexCyclicSpace N e ≤ realCyclicComplexification N e := by
  apply Submodule.topologicalClosure_minimal _ ?_ (realCyclicComplexification_closed e)
  apply Submodule.span_le.mpr
  rintro p ⟨a, rfl⟩
  obtain ⟨hr, hi⟩ := complex_elemental_coordinates (a : Space H →L[ℂ] Space H) a.property
  exact ⟨Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨_, hr⟩, rfl⟩),
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨_, hi⟩, rfl⟩)⟩

lemma inclusion_mem_complexCyclic (e x : H) (hx : x ∈ Target.realCyclicSpace N e) :
    inclusion x ∈ Target.complexCyclicSpace N e := by
  let P := (Target.complexCyclicSpace N e).restrictScalars ℝ
  have hc : IsClosed (P : Set (Space H)) := Submodule.isClosed_topologicalClosure _
  have hsub : Submodule.span ℝ (Set.range (fun a : StarAlgebra.elemental ℝ N =>
      (a : H →L[ℝ] H) e)) ≤ P.comap inclusion.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change inclusion ((a : H →L[ℝ] H) e) ∈ Target.complexCyclicSpace N e
    rw [← operator_inclusion]
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨⟨operator a, operator_mem_complex_elemental (N := N) (H := H) a a.property⟩, rfl⟩
  exact Submodule.topologicalClosure_minimal _ hsub (hc.preimage inclusion.continuous) hx

/-- Real fixed vectors in the complex cyclic space lie in the actual real
cyclic subspace, with its original inherited norm. -/
lemma realCyclic_iff (e x : H) :
    inclusion x ∈ Target.complexCyclicSpace N e ↔ x ∈ Target.realCyclicSpace N e := by
  constructor
  · intro hx
    exact (complexCyclic_coordinates e hx).1
  · exact inclusion_mem_complexCyclic e x
end RealCyclicBridge

lemma inclusion_realPart_fixed (v : Fixed C.involutionData 2) :
    inclusion (realPart (complexEmbedding hN C v.val)) = complexEmbedding hN C v.val := by
  have hf : conjugation (complexEmbedding hN C v.val) = complexEmbedding hN C v.val := by
    rw [← complexEmbedding_conjugation]
    exact congrArg (complexEmbedding hN C)
      (show conjugatePullback C.involutionData v.val = v.val from v.property)
  obtain ⟨x, hx⟩ := ((coordinates H).2.1 _).mp hf
  rw [← hx]
  rfl

/-- Restriction to the native fixed real Hilbert space, with original-real
vectors as codomain. -/
def realEmbedding : Fixed C.involutionData 2 →ₗᵢ[ℝ] Target.realCyclicSpace N C.e := by
  let F : Fixed C.involutionData 2 →ₗ[ℝ] H :=
    realPart.toLinearMap.comp
      (((complexEmbedding hN C).toLinearMap.restrictScalars ℝ).comp
        (fixedSubmodule C.involutionData 2).subtype)
  let G := F.codRestrict (Target.realCyclicSpace N C.e) (by
    intro v
    apply (realCyclic_iff C.e _).mp
    rw [show inclusion (F v) = complexEmbedding hN C v.val from inclusion_realPart_fixed hN C v]
    rw [← complexEmbedding_range hN C]
    exact ⟨v.val, rfl⟩)
  refine { G with norm_map' := ?_ }
  intro v
  change ‖F v‖ = ‖v.val‖
  rw [← inclusion.norm_map (F v), show inclusion (F v) = complexEmbedding hN C v.val from
    inclusion_realPart_fixed hN C v]
  exact (complexEmbedding hN C).norm_map v.val

lemma realEmbedding_inclusion (v : Fixed C.involutionData 2) :
    inclusion (realEmbedding hN C v : H) = complexEmbedding hN C v.val :=
  inclusion_realPart_fixed hN C v

lemma realEmbedding_surjective : Function.Surjective (realEmbedding hN C) := by
  intro x
  let z : Target.complexCyclicSpace N C.e := ⟨inclusion (x : H), (realCyclic_iff C.e (x : H)).mpr x.property⟩
  let v := (complexUnitary hN C).symm z
  have hv : complexEmbedding hN C v = inclusion (x : H) := by
    exact congrArg Subtype.val ((complexUnitary hN C).apply_symm_apply z)
  have hf : v ∈ fixedSubmodule C.involutionData 2 := by
    change conjugatePullback C.involutionData v = v
    apply (complexEmbedding hN C).injective
    rw [complexEmbedding_conjugation, hv]
    change ((x : H), -(0 : H)) = ((x : H), 0)
    simp
  refine ⟨⟨v, hf⟩, ?_⟩
  apply Subtype.ext
  apply inclusion.injective
  exact (realEmbedding_inclusion hN C ⟨v, hf⟩).trans hv

/-- A real unitary onto the real generated cyclic space, not onto the entire
complex space viewed with restricted scalars. -/
def realUnitary : Fixed C.involutionData 2 ≃ₗᵢ[ℝ] Target.realCyclicSpace N C.e :=
  LinearIsometryEquiv.ofSurjective (realEmbedding hN C) (realEmbedding_surjective hN C)

lemma realUnitary_multiplier (f : Fixed C.involutionData ∞) (v : Fixed C.involutionData 2) :
    (realUnitary hN C (restrictedMultiplier C.involutionData f v) : H) =
      (C.Ψ f : H →L[ℝ] H) (realUnitary hN C v : H) := by
  apply inclusion.injective
  change inclusion (realEmbedding hN C (restrictedMultiplier C.involutionData f v) : H) = _
  rw [realEmbedding_inclusion, ← operator_inclusion]
  change complexEmbedding hN C (restrictedMultiplier C.involutionData f v).val =
    operator (C.Ψ f : H →L[ℝ] H) (inclusion (realEmbedding hN C v : H))
  rw [realEmbedding_inclusion]
  exact complexEmbedding_fixed_multiplier hN C f v

/-- Normalized, equivariant same-measure cyclic realization, for every
supplied algebra model and with no cyclicity assumption on the ambient H. -/
theorem cyclic_realization : RealNormalControlTopology.Spec.CyclicRealization.{u} := by
  intro H _ _ _ N hN C
  letI := C.finite
  let S := Target.complexCyclicSpace N C.e
  have hS : IsClosed (S : Set (Space H)) := Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace S := hS.completeSpace_coe
  let U := complexUnitary hN C
  let eS := U (ContinuousMap.toLp 2 C.μ ℂ 1)
  refine ⟨S, hS, U, eS, rfl, complexEmbedding_one hN C, rfl, ?_, ?_, ?_,
    realUnitary hN C, ?_, realUnitary_multiplier hN C⟩
  · exact complexEmbedding_conjugation hN C
  · exact complexEmbedding_intertwines hN C
  · intro B hB s
    have hs : (s : Space H) ∈ (complexEmbedding hN C).toLinearMap.range := by
      rw [complexEmbedding_range hN C]
      exact s.property
    have hp := complexEmbedding_projection hN C B hB ⟨s, hs⟩
    change C.E B (s : Space H) ∈ (complexEmbedding hN C).toLinearMap.range at hp
    rw [complexEmbedding_range hN C] at hp
    exact hp
  · exact realEmbedding_inclusion hN C

end ExpandedFA.VonNeumann.RealNormalCyclicRealization
