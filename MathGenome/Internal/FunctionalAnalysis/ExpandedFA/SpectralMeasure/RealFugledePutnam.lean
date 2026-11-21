import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealFugledePutnam
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RealFugledeIntertwining
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.FugledePutnam

/-! The complexified transport uses the rectangular complex theorem. The real
similarity proof uses the actual scalar-generic modulus and polar factor. -/
noncomputable section
namespace ExpandedFA.SpectralMeasure.RealFugledePutnam
universe u v
open TraceIdeals.RealComplexification

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

lemma operator_normal (N : H →L[ℝ] H) (hN : IsStarNormal N) :
    IsStarNormal (operator N) := by
  constructor
  change (operator N).adjoint.comp (operator N) =
    (operator N).comp (operator N).adjoint
  have h : N.adjoint.comp N = N.comp N.adjoint := hN.star_comm_self.eq
  rw [operator_adjoint, ← operator_comp, ← operator_comp, h]

lemma operator_intertwines (N : H →L[ℝ] H) (M : K →L[ℝ] K) (T : K →L[ℝ] H)
    (hT : N.comp T = T.comp M) :
    (operator N).comp (operator T) = (operator T).comp (operator M) := by
  rw [← operator_comp, hT, operator_comp]

theorem adjoint_intertwining : Spec.AdjointIntertwining.{u,v} :=
  RealFugledeIntertwining.adjoint_intertwining

theorem borel_intertwining : Spec.BorelIntertwining.{u,v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT
  exact FugledePutnam.borel_intertwining (Space H) (Space K)
    (operator N) (operator M) (operator T)
    (operator_normal N hN) (operator_normal M hM) (operator_intertwines N M T hT)

theorem spectral_projections : Spec.SpectralProjections.{u,v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT
  exact FugledePutnam.spectral_projections (Space H) (Space K)
    (operator N) (operator M) (operator T)
    (operator_normal N hN) (operator_normal M hM) (operator_intertwines N M T hT)

theorem similarity_orthogonal : Spec.SimilarityOrthogonal.{u, v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT
  have hstar := adjoint_intertwining H K N M T.toContinuousLinearMap
    hN.star_comm_self.eq hM.star_comm_self.eq hT
  have hTs : T.toContinuousLinearMap.adjoint.comp N =
      M.comp T.toContinuousLinearMap.adjoint := by
    have hh := congrArg ContinuousLinearMap.adjoint hstar
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using hh
  have hc : Commute M (T.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap) := by
    change M.comp (T.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap) =
      (T.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap).comp M
    ext x
    change M (T.toContinuousLinearMap.adjoint (T x)) = T.toContinuousLinearMap.adjoint (T (M x))
    calc
      _ = T.toContinuousLinearMap.adjoint (N (T x)) :=
        (congrArg (fun A : H →L[ℝ] K => A (T x)) hTs).symm
      _ = _ := congrArg T.toContinuousLinearMap.adjoint
        (congrArg (fun A : K →L[ℝ] H => A x) hT)
  have hmod : Commute M (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap) :=
    PolarDecomposition.positiveSqrt_commutes _ M hc
  obtain ⟨U, hU, _⟩ := PolarDecomposition.polar_decomposition ℝ K H T.toContinuousLinearMap
  obtain ⟨e, he⟩ := PolarDecomposition.invertible_unitary ℝ K H T U hU
  refine ⟨e, he ▸ hU, ?_⟩
  rw [he]
  apply PolarDecomposition.ext_of_comp_modulus_eq T.toContinuousLinearMap
  · ext x
    have hu (y : K) : U (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap y) = T y :=
      congrArg (fun A : K →L[ℝ] H => A y) hU.2.2.2
    have hm (y : K) : M (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap y) =
        PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap (M y) :=
      congrArg (fun A : K →L[ℝ] K => A y) hmod.eq
    change N (U (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap x)) =
      U (M (PolarDecomposition.Spec.modulusValue T.toContinuousLinearMap x))
    rw [hu, hm, hu]
    exact congrArg (fun A : K →L[ℝ] H => A x) hT
  · intro x hx
    have hx0 : x = 0 := T.injective (hx.trans (map_zero T).symm)
    simp [hx0]


@[simp] lemma conjugation_involution (p : Space H) : conjugation (conjugation p) = p :=
  (coordinates H).2.2.1 p

lemma conjugation_smul (a : ℂ) (p : Space H) :
    conjugation (a • p) = star a • conjugation p :=
  (coordinates H).2.2.2.1 a p

/-- Conjugating on both sides is again complex linear. -/
def conjugateOperator (A : Space H →L[ℂ] Space H) : Space H →L[ℂ] Space H :=
  ({ toFun := fun p => conjugation (A (conjugation p))
     map_add' := by intro p q; simp only [map_add]
     map_smul' := by
       intro a p
       simp only [conjugation_smul, map_smul, star_star, RingHom.id_apply]
    } : Space H →ₗ[ℂ] Space H).mkContinuous ‖A‖ (fun p => by
      change ‖conjugation (A (conjugation p))‖ ≤ ‖A‖ * ‖p‖
      simpa only [conjugation.norm_map] using A.le_opNorm (conjugation p))

@[simp] lemma conjugateOperator_apply (A : Space H →L[ℂ] Space H) (p : Space H) :
    conjugateOperator A p = conjugation (A (conjugation p)) := rfl

@[simp] lemma conjugateOperator_involution (A : Space H →L[ℂ] Space H) :
    conjugateOperator (conjugateOperator A) = A := by
  ext p
  simp only [conjugateOperator_apply, conjugation_involution]

/-- A ring equivalence, semilinear for complex coefficients. -/
def conjugateOperatorEquiv : (Space H →L[ℂ] Space H) ≃+* (Space H →L[ℂ] Space H) where
  toFun := conjugateOperator
  invFun := conjugateOperator
  left_inv := conjugateOperator_involution
  right_inv := conjugateOperator_involution
  map_add' A B := by ext p; simp only [conjugateOperator_apply, add_apply, map_add]
  map_mul' A B := by ext p; simp only [conjugateOperator_apply,
    mul_apply_eq_comp, conjugation_involution]

lemma conjugateOperator_smul (a : ℂ) (A : Space H →L[ℂ] Space H) :
    conjugateOperator (a • A) = star a • conjugateOperator A := by
  ext p
  simp only [conjugateOperator_apply, smul_apply, conjugation_smul]

@[simp] lemma conjugateOperator_real (N : H →L[ℝ] H) :
    conjugateOperator (operator N) = operator N := by
  ext p
  change (N p.1, -(N (-p.2))) = (N p.1, N p.2)
  simp only [map_neg, neg_neg]

/-- The symmetry of the complex spectrum holds for every bounded real
operator, without normality or a nonzero-space assumption. -/
lemma spectrum_conjugation (N : H →L[ℝ] H) (z : ℂ) :
    z ∈ spectrum ℂ (operator N) ↔ star z ∈ spectrum ℂ (operator N) := by
  have hmap : conjugateOperatorEquiv (H := H)
      (algebraMap ℂ (Space H →L[ℂ] Space H) z - operator N) =
      algebraMap ℂ (Space H →L[ℂ] Space H) (star z) - operator N := by
    rw [map_sub]
    change conjugateOperator (algebraMap ℂ (Space H →L[ℂ] Space H) z) -
      conjugateOperator (operator N) = _
    rw [Algebra.algebraMap_eq_smul_one, conjugateOperator_smul,
      conjugateOperator_real]
    have h1 : conjugateOperator (1 : Space H →L[ℂ] Space H) = 1 :=
      (conjugateOperatorEquiv (H := H)).map_one
    rw [h1, Algebra.algebraMap_eq_smul_one]
  rw [spectrum.mem_iff, spectrum.mem_iff, ← hmap,
    MulEquiv.isUnit_map (conjugateOperatorEquiv (H := H))]

/-- The componentwise extension reflects equality even for rectangular maps. -/
lemma operator_injective : Function.Injective (operator (H := H) (K := K)) := by
  intro A B h
  ext x
  apply inclusion.injective
  rw [← operator_inclusion A, h, operator_inclusion B]

/-- The only possible real restriction, whenever the real form is preserved. -/
def realRestriction (A : Space H →L[ℂ] Space H) : H →L[ℝ] H :=
  realPart.comp ((A.restrictScalars ℝ).comp inclusion.toContinuousLinearMap)

lemma restriction_of_fixed (A : Space H →L[ℂ] Space H)
    (hA : ∀ p : Space H, conjugation p = p → conjugation (A p) = A p) :
    Spec.UniqueRealRestriction A (realRestriction A) ∧
      operator (realRestriction A) = A := by
  have hR : Spec.IsRealRestriction A (realRestriction A) := by
    intro x
    have hx : conjugation (inclusion x) = inclusion x := by
      change (x, -(0:H)) = (x, 0)
      simp
    obtain ⟨y, hy⟩ := ((coordinates H).2.1 (A (inclusion x))).mp (hA _ hx)
    change A (inclusion x) = inclusion ((A (inclusion x)).1)
    rw [← hy]
    rfl
  refine ⟨⟨hR, ?_⟩, (operator_unique (realRestriction A) A hR).symm⟩
  intro S hS
  ext x
  apply inclusion.injective
  exact (hS x).symm.trans (hR x)

lemma restriction_intertwines (A : Space H →L[ℂ] Space H)
    (B : Space K →L[ℂ] Space K) (T : K →L[ℝ] H)
    (R : H →L[ℝ] H) (S : K →L[ℝ] K)
    (hR : Spec.IsRealRestriction A R) (hS : Spec.IsRealRestriction B S)
    (hT : A.comp (operator T) = (operator T).comp B) :
    R.comp T = T.comp S := by
  ext x
  apply inclusion.injective
  change inclusion (R (T x)) = inclusion (T (S x))
  change ∀ x : H, A (inclusion x) = inclusion (R x) at hR
  change ∀ x : K, B (inclusion x) = inclusion (S x) at hS
  calc
    inclusion (R (T x)) = A (inclusion (T x)) := (hR _).symm
    _ = A (operator T (inclusion x)) := congrArg A (operator_inclusion T x).symm
    _ = operator T (B (inclusion x)) :=
      congrArg (fun L : Space K →L[ℂ] Space H => L (inclusion x)) hT
    _ = operator T (inclusion (S x)) := congrArg (operator T) (hS x)
    _ = inclusion (T (S x)) := operator_inclusion T _

lemma restriction_projection (A : Space H →L[ℂ] Space H) (R : H →L[ℝ] H)
    (hR : operator R = A) (hA : IsSelfAdjoint A) (hAA : A.comp A = A) :
    R.adjoint = R ∧ R.comp R = R := by
  constructor
  · apply operator_injective
    rw [← operator_adjoint, hR]
    exact hA
  · apply operator_injective
    rw [operator_comp, hR, hAA]

/-- This assembly lemma leaves the full covariance assertion explicit. -/
lemma real_projections_of_covariance
    (hH : Spec.ConjugationCovariance.{u}) (hK : Spec.ConjugationCovariance.{v}) :
    Spec.RealSpectralProjections.{u,v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT E F hE hF B hB hconj
  have hEN := (hH H N hN).2 E hE B hB
  have hFM := (hK K M hM).2 F hF B hB
  rw [hconj] at hEN hFM
  have fixedN (p : Space H) (hp : conjugation p = p) :
      conjugation (E (Subtype.val ⁻¹' B) p) = E (Subtype.val ⁻¹' B) p := by
    simpa only [hp] using hEN p
  have fixedM (p : Space K) (hp : conjugation p = p) :
      conjugation (F (Subtype.val ⁻¹' B) p) = F (Subtype.val ⁻¹' B) p := by
    simpa only [hp] using hFM p
  obtain ⟨hP, hPC⟩ := restriction_of_fixed _ fixedN
  obtain ⟨hQ, hQC⟩ := restriction_of_fixed _ fixedM
  have hbN : MeasurableSet (Subtype.val ⁻¹' B : Set (spectrum ℂ (operator N))) :=
    measurable_subtype_coe hB
  have hbM : MeasurableSet (Subtype.val ⁻¹' B : Set (spectrum ℂ (operator M))) :=
    measurable_subtype_coe hB
  have hPP := restriction_projection _ _ hPC (E.selfAdjoint _ hbN) (E.idempotent _ hbN)
  have hQQ := restriction_projection _ _ hQC (F.selfAdjoint _ hbM) (F.idempotent _ hbM)
  exact ⟨_, _, hP, hQ, hPC, hQC, hPP.1, hPP.2, hQQ.1, hQQ.2,
    restriction_intertwines _ _ T _ _ hP.1 hQ.1
      (spectral_projections H K N M T hN hM hT E F hE hF B hB)⟩


theorem spectrum_symmetry : Spec.SpectrumConjugation.{u} := by
  intro H _ _ _ N z
  exact spectrum_conjugation N z

/-- Fixed-form invariance gives unique real restrictions, and complex
Fuglede–Putnam gives their real intertwining. -/
lemma real_borel_of_invariance
    (hH : Spec.CompatibleBorelInvariance.{u}) (hK : Spec.CompatibleBorelInvariance.{v}) :
    Spec.RealBorelTransport.{u,v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT E F hE hF Φ Ψ hΦ hΨ s _ hNs hMs hs f hf hconj
  obtain ⟨hR, hRC⟩ := restriction_of_fixed _
    (hH H N hN E hE Φ hΦ s hNs hs f hf hconj)
  obtain ⟨hS, hSC⟩ := restriction_of_fixed _
    (hK K M hM F hF Ψ hΨ s hMs hs f hf hconj)
  refine ⟨hH H N hN E hE Φ hΦ s hNs hs f hf hconj,
    hK K M hM F hF Ψ hΨ s hMs hs f hf hconj,
    _, _, hR, hS, hRC, hSC, ?_⟩
  exact restriction_intertwines _ _ T _ _ hR.1 hS.1
    (borel_intertwining H K N M T hN hM hT E F hE hF Φ Ψ hΦ hΨ s hNs hMs f hf)

/-- Combine the covariance and invariance statements with complex and real
Fuglede–Putnam and the actual real polar decomposition. -/
lemma full_scalar_of_covariance_and_invariance
    (hCH : Spec.ConjugationCovariance.{u}) (hCK : Spec.ConjugationCovariance.{v})
    (hIH : Spec.CompatibleBorelInvariance.{u}) (hIK : Spec.CompatibleBorelInvariance.{v}) :
    Spec.FullScalarConclusion.{u,v} :=
  ⟨FugledePutnam.adjoint_intertwining, FugledePutnam.borel_intertwining,
    FugledePutnam.spectral_projections, FugledePutnam.similarity_unitary,
    adjoint_intertwining, borel_intertwining, spectral_projections,
    hCH, hCK, real_borel_of_invariance hIH hIK,
    real_projections_of_covariance hCH hCK, similarity_orthogonal⟩


open scoped InnerProductSpace
open MeasureTheory Set Filter Topology

lemma conjugation_inner (p q : Space H) :
    ⟪conjugation p, conjugation q⟫_ℂ = star ⟪p, q⟫_ℂ := by
  change Hilbert.PreHilbertCompactSpectral.Spec.Complexification.ip H (p.1, -p.2) (q.1, -q.2) = _
  change _ = star (Hilbert.PreHilbertCompactSpectral.Spec.Complexification.ip H p q)
  apply Complex.ext <;> simp [Hilbert.PreHilbertCompactSpectral.Spec.Complexification.ip, sub_eq_add_neg, add_comm]

lemma conjugateOperator_continuous :
    Continuous (conjugateOperator (H := H)) := by
  have hn (A : Space H →L[ℂ] Space H) : ‖conjugateOperator A‖ ≤ ‖A‖ := by
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (fun p => by
      change ‖conjugation (A (conjugation p))‖ ≤ ‖A‖ * ‖p‖
      simpa only [conjugation.norm_map] using A.le_opNorm (conjugation p))
  have hl : LipschitzWith 1 (conjugateOperator (H := H)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro A B
    have hh : conjugateOperator (A - B) = conjugateOperator A - conjugateOperator B :=
      (conjugateOperatorEquiv (H := H)).map_sub A B
    simpa only [dist_eq_norm, hh, NNReal.coe_one, one_mul] using hn (A - B)
  exact hl.continuous

/-- Conjugation on the actual spectrum, including the empty spectrum. -/
def spectrumConjugation (N : H →L[ℝ] H) :
    spectrum ℂ (operator N) ≃ₜ spectrum ℂ (operator N) where
  toFun z := ⟨star z.val, (spectrum_conjugation N z.val).mp z.property⟩
  invFun z := ⟨star z.val, (spectrum_conjugation N z.val).mp z.property⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp
  continuous_toFun := (continuous_star.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_star.comp continuous_subtype_val).subtype_mk _

lemma continuous_conjugation (N : H →L[ℝ] H)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator N)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator N) E)
    (f : C(spectrum ℂ (operator N), ℂ)) :
    conjugateOperator (NormalPVM.continuousIntegral E f) =
      NormalPVM.continuousIntegral E (star (f.comp (⟨spectrumConjugation N, (spectrumConjugation N).continuous⟩ : C(_, _)))) := by
  let π := NormalPVM.continuousIntegral E
  let c := (⟨spectrumConjugation N, (spectrumConjugation N).continuous⟩ : C(_, _))
  have hc : π ((ContinuousMap.id ℂ).restrict (spectrum ℂ (operator N))) = operator N :=
    NormalPVM.continuousIntegral_coordinate E hE
  change conjugateOperator (π f) = π (star (f.comp c))
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have hh : star ((ContinuousMap.const _ r).comp c) = ContinuousMap.const _ (star r) := rfl
    rw [hh]
    rw [show π (ContinuousMap.const _ r) = algebraMap ℂ _ r from π.commutes r,
      show π (ContinuousMap.const _ (star r)) = algebraMap ℂ _ (star r) from π.commutes (star r)]
    rw [Algebra.algebraMap_eq_smul_one, conjugateOperator_smul]
    rw [show conjugateOperator (1 : Space H →L[ℂ] Space H) = 1 from
      (conjugateOperatorEquiv (H := H)).map_one, Algebra.algebraMap_eq_smul_one]
  | id =>
    have hh : star (((ContinuousMap.id ℂ).restrict (spectrum ℂ (operator N))).comp c) =
        (ContinuousMap.id ℂ).restrict (spectrum ℂ (operator N)) := by ext z; exact star_star z.val
    rw [hh, hc, conjugateOperator_real]
  | star_id =>
    have hh : star ((star ((ContinuousMap.id ℂ).restrict (spectrum ℂ (operator N)))).comp c) =
        star ((ContinuousMap.id ℂ).restrict (spectrum ℂ (operator N))) := by ext z; simp [c, spectrumConjugation]
    rw [hh, map_star, hc]
    change conjugateOperator (operator N).adjoint = (operator N).adjoint
    rw [operator_adjoint, conjugateOperator_real]
  | add f g hf hg =>
    have hh : star ((f + g).comp c) = star (f.comp c) + star (g.comp c) := by ext z; simp
    rw [hh, map_add, map_add, show conjugateOperator (π f + π g) = conjugateOperator (π f) + conjugateOperator (π g) from
      (conjugateOperatorEquiv (H := H)).map_add _ _, hf, hg]
  | mul f g hf hg =>
    have hh : star ((f * g).comp c) = star (f.comp c) * star (g.comp c) := by ext z; simp
    rw [hh, map_mul, map_mul, show conjugateOperator (π f * π g) = conjugateOperator (π f) * conjugateOperator (π g) from
      (conjugateOperatorEquiv (H := H)).map_mul _ _, hf, hg]
  | frequently f hf =>
    have hclosed : IsClosed {g : C(spectrum ℂ (operator N), ℂ) |
        conjugateOperator (π g) = π (star (g.comp c))} := by
      apply isClosed_eq
      · exact conjugateOperator_continuous.comp (NormalPVM.continuousIntegral_continuous E)
      · simp only [map_star]
        exact ContinuousLinearMap.adjoint.continuous.comp
          ((NormalPVM.continuousIntegral_continuous E).comp
            (ContinuousMap.compRightAlgHom_continuous ℂ ℂ c))
    exact hclosed.mem_of_frequently_of_tendsto hf tendsto_id

lemma conjugateOperator_inner (A : Space H →L[ℂ] Space H) (x y : Space H) :
    ⟪conjugation x, A (conjugation y)⟫_ℂ = star ⟪x, conjugateOperator A y⟫_ℂ := by
  simpa only [conjugateOperator_apply, conjugation_involution] using
    (conjugation_inner x (conjugation (A (conjugation y))))

lemma inner_conjugation_right (x q : Space H) :
    ⟪x, conjugation q⟫_ℂ = star ⟪conjugation x, q⟫_ℂ := by
  simpa only [conjugation_involution] using conjugation_inner (conjugation x) q

/-- Uniqueness of regular scalar coefficient measures extends polynomial
conjugation to all Borel sets, without a scalar control measure. -/
lemma conjugated_coefficientMeasure (N : H →L[ℝ] H)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator N)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator N) E) (x y : Space H) :
    (E.coefficientMeasure (conjugation x) (conjugation y)).map (spectrumConjugation N) =
      E.coefficientMeasure y x := by
  let c := spectrumConjugation N
  have hc := c.measurableEmbedding
  apply FunctionSpaces.ScalarRieszMarkov.scalarIntegral_injective _ _
    ⟨measure_lt_top _ _,
      (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr inferInstance⟩
    ⟨measure_lt_top _ _,
      (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr inferInstance⟩
  intro g
  unfold FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral
  rw [hc.integral_map_vectorMeasure]
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable (fun z => g (c z)) :=
    NormalPVM.continuous_bounded (g.toContinuousMap.comp (⟨c, c.continuous⟩ : C(_, _)))
  rw [← E.spectralIntegral_coefficient _ hg,
    ← E.spectralIntegral_coefficient (g : _ → ℂ) (NormalPVM.continuous_bounded g.toContinuousMap),
    conjugateOperator_inner]
  have hh := continuous_conjugation N E hE (g.toContinuousMap.comp (⟨c, c.continuous⟩ : C(_, _)))
  have hi : star ((g.toContinuousMap.comp (⟨c, c.continuous⟩ : C(_, _))).comp (⟨c, c.continuous⟩ : C(_, _))) =
      star g.toContinuousMap := by ext z; simp [c, spectrumConjugation]
  change conjugateOperator (E.spectralIntegral (fun z => g (c z))) = _ at hh
  rw [hi, map_star] at hh
  rw [hh]
  change star ⟪x, (E.spectralIntegral g).adjoint y⟫_ℂ = ⟪y, E.spectralIntegral g x⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]
  exact star_star _

/-- Full conjugation covariance for the integral of any bounded Borel
symbol, whether or not that symbol has a real restriction. -/
lemma integral_conjugation (N : H →L[ℝ] H)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator N)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator N) E)
    (f : spectrum ℂ (operator N) → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    conjugateOperator (E.spectralIntegral f) =
      E.spectralIntegral (star (f ∘ spectrumConjugation N)) := by
  let c := spectrumConjugation N
  have hc := c.measurableEmbedding
  have hm (x y : Space H) := conjugated_coefficientMeasure N E hE x y
  have heqstar : E.spectralIntegral (star f ∘ c) = conjugateOperator (E.spectralIntegral f) := by
    have hsf := SpectralMeasure.Spec.IsBoundedMeasurable.star hf
    -- The same coefficient equality applies with the symbol conjugated.
    ext y
    apply ext_inner_left ℂ
    intro x
    have hm' := hm (conjugation x) (conjugation y)
    simp only [conjugation_involution] at hm'
    have hint := congrArg (fun μ : ComplexMeasure (spectrum ℂ (operator N)) =>
      μ.integral (star f) (ContinuousLinearMap.mul ℝ ℂ)) hm'
    rw [hc.integral_map_vectorMeasure] at hint
    have hsfc : SpectralMeasure.Spec.IsBoundedMeasurable (star f ∘ c) :=
      ⟨hsf.1.comp hc.measurable, hsf.2.imp (fun C hC z => hC (c z))⟩
    rw [E.spectralIntegral_coefficient _ hsfc]
    change _ = ⟪x, conjugation (E.spectralIntegral f (conjugation y))⟫_ℂ
    rw [inner_conjugation_right]
    rw [← E.spectralIntegral_coefficient (star f) hsf (conjugation y) (conjugation x),
      E.spectralIntegral_star f hf] at hint
    change _ = ⟪conjugation y, (E.spectralIntegral f).adjoint (conjugation x)⟫_ℂ at hint
    rw [ContinuousLinearMap.adjoint_inner_right] at hint
    rw [← inner_conj_symm] at hint
    exact hint
  exact heqstar.symm

/-- All ambient Borel spectral projections transform covariantly under J. -/
theorem conjugation_covariance : Spec.ConjugationCovariance.{u} := by
  intro H _ _ _ N hN
  refine ⟨spectrum_conjugation N, ?_⟩
  intro E hE B hB p
  let f : spectrum ℂ (operator N) → ℂ := (Subtype.val ⁻¹' B).indicator (fun _ => 1)
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f :=
    BorelNormSpectrum.bounded_indicator _ (measurable_subtype_coe hB)
      (BorelNormSpectrum.bounded_const 1)
  have hi : star (f ∘ spectrumConjugation N) =
      (Subtype.val ⁻¹' (star '' B)).indicator (fun _ : spectrum ℂ (operator N) => (1 : ℂ)) := by
    classical
    funext z
    have hz : star z.val ∈ B ↔ z.val ∈ star '' B := by
      constructor
      · intro hz
        exact ⟨star z.val, hz, star_star z.val⟩
      · rintro ⟨w, hw, he⟩
        simpa only [← he, star_star] using hw
    change star ((if star z.val ∈ B then (1 : ℂ) else 0)) =
      (if z.val ∈ star '' B then 1 else 0)
    by_cases hzB : star z.val ∈ B
    · rw [ite_eq_left hzB, ite_eq_left (hz.mp hzB), star_one]
    · rw [ite_eq_right hzB, ite_eq_right (mt hz.mpr hzB), star_zero]
  have hBi : MeasurableSet (star '' B) := by
    have him : star '' B = (star : ℂ → ℂ) ⁻¹' B := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa only [Set.mem_preimage, star_star] using hw
      · intro hz
        exact ⟨star z, hz, star_star z⟩
    rw [him]
    exact (continuous_star : Continuous (star : ℂ → ℂ)).measurable hB
  have hh := integral_conjugation N E hE f hf
  rw [hi, BorelNormSpectrum.integral_indicator_one E _ (measurable_subtype_coe hBi)] at hh
  have hval : E.spectralIntegral f = E (Subtype.val ⁻¹' B) :=
    BorelNormSpectrum.integral_indicator_one E _ (measurable_subtype_coe hB)
  rw [hval] at hh
  exact congrArg (fun A : Space H →L[ℂ] Space H => A p) hh

/-- A compatible symbol has conjugation-invariant spectral integral, so it
preserves the canonical fixed real form. -/
theorem compatible_borel_invariance : Spec.CompatibleBorelInvariance.{u} := by
  intro H _ _ _ N hN E hE Φ hΦ s _ hNs hs f hf hconj p hp
  let i := FugledePutnam.Spec.inclusion (operator N) s hNs
  have hfi : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ i) :=
    ⟨hf.1.comp i.continuous.measurable, hf.2.imp (fun C hC z => hC (i z))⟩
  have heq : star ((f ∘ i) ∘ spectrumConjugation N) = f ∘ i := by
    funext z
    change star (f ⟨star z.val, _⟩) = f (i z)
    have hh := hconj (i z)
    exact (congrArg star hh).trans (star_star (f (i z)))
  have hC := integral_conjugation N E hE (f ∘ i) hfi
  rw [heq] at hC
  have hΦi := FugledePutnam.calculus_eq_integral E Φ hΦ (f ∘ i) hfi
  rw [hΦi]
  have hh := congrArg (fun A : Space H →L[ℂ] Space H => A p) hC
  simpa only [conjugateOperator_apply, hp] using hh

/-- The descended operators live on the original real Hilbert spaces. -/
theorem real_borel_transport : Spec.RealBorelTransport.{u,v} :=
  real_borel_of_invariance compatible_borel_invariance compatible_borel_invariance

theorem real_spectral_projections : Spec.RealSpectralProjections.{u,v} :=
  real_projections_of_covariance conjugation_covariance conjugation_covariance

theorem full_scalar_conclusion : Spec.FullScalarConclusion.{u,v} :=
  full_scalar_of_covariance_and_invariance conjugation_covariance conjugation_covariance
    compatible_borel_invariance compatible_borel_invariance

end ExpandedFA.SpectralMeasure.RealFugledePutnam
