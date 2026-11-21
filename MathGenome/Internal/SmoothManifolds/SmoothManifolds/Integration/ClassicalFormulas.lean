import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.ClassicalFormulas
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.ClassicalIntegralIdentifications
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.ClassicalBoundaryGeometry
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Stokes
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical Topology BigOperators Matrix

namespace SmoothManifolds.ClassicalResults
open ModelData ClassicalData

theorem oneFormMap_apply {n : ℕ} (a : Euclidean n) (v : Fin 1 → Euclidean n) :
    oneFormMap n a v = a ⬝ᵥ v 0 := by
  simp [oneFormMap, dotProduct]

theorem oneForm_apply : Specs.SmoothManifolds.Integration.ClassicalFormulas.oneForm_applyType := by
  intro n A x v
  exact oneFormMap_apply (A x) (fun _ => v)

theorem oneForm_derivative :
    Specs.SmoothManifolds.Integration.ClassicalFormulas.oneForm_derivativeType := by
  intro n s A x u v hs hA
  have hd : fderivWithin ℝ (oneForm A) s x = (oneFormMap n).comp (fderivWithin ℝ A s x) :=
    ((oneFormMap n).hasFDerivAt.comp_hasFDerivWithinAt x hA.hasFDerivWithinAt).fderivWithin hs
  rw [extDerivWithin, hd, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp [Fin.sum_univ_two, oneFormMap_apply, Fin.removeNth, Fin.succAbove,
    sub_eq_add_neg]

theorem green_coefficient :
    Specs.SmoothManifolds.Integration.ClassicalFormulas.green_coefficientType := by
  intro s A x hs hA
  have hf : frame 2 = ![frame 2 0, frame 2 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hf, oneForm_derivative s A x _ _ hs hA]
  simp [dotProduct, partialWithin, frame, Pi.single_apply]

theorem linearMap_apply_frame_sum {n : ℕ} (D : Euclidean n →L[ℝ] Euclidean n)
    (w : Euclidean n) : D w = ∑ i : Fin n, w i • D (frame n i) := by
  have hw : w = ∑ i : Fin n, w i • frame n i := by
    ext j
    simp [frame, Pi.single_apply]
  conv_lhs => rw [hw, map_sum]
  simp

theorem curl_coefficient :
    Specs.SmoothManifolds.Integration.ClassicalFormulas.curl_coefficientType := by
  intro s A x u v hs hA
  rw [oneForm_derivative s A x u v hs hA,
    linearMap_apply_frame_sum (fderivWithin ℝ A s x) u,
    linearMap_apply_frame_sum (fderivWithin ℝ A s x) v]
  simp [curlWithin, partialWithin, cross_apply, dotProduct, Fin.sum_univ_succ]
  ring

theorem frame_matrix (n : ℕ) : frame n = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp [frame, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem det_update_frame {n : ℕ} (i : Fin n) (v : Euclidean n) :
    Matrix.det (Function.update (frame n) i v) = v i := by
  have hv : v = ∑ j : Fin n, v j • (1 : Matrix (Fin n) (Fin n) ℝ) j := by
    ext k
    simp [Matrix.one_apply]
  rw [frame_matrix]
  conv_lhs => rw [hv]
  exact Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) ℝ) i v |>.trans (by simp)

theorem flux_omitted_coefficient :
    Specs.SmoothManifolds.Integration.ClassicalFormulas.flux_omitted_coefficientType := by
  intro n X x i
  change Matrix.detRowAlternating (Matrix.vecCons (X x) (i.removeNth (frame (n+1)))) = _
  rw [← AlternatingMap.neg_one_pow_smul_map_insertNth
    (Matrix.detRowAlternating : AlternatingMap ℝ (Euclidean (n+1)) ℝ (Fin (n+1)))
      i (X x) (i.removeNth (frame (n+1))),
    Fin.insertNth_removeNth]
  change ((-1 : ℤ)^i.val) • Matrix.det (Function.update (frame (n+1)) i (X x)) = _
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [det_update_frame]

theorem divergence_coefficient :
    Specs.SmoothManifolds.Integration.ClassicalFormulas.divergence_coefficientType := by
  intro n s X x hs hX
  have hω : DifferentiableWithinAt ℝ (fluxForm X) s x :=
    (volume (n+1)).curryLeft.differentiableAt.comp_differentiableWithinAt x hX
  rw [extDerivWithin_apply hω hs]
  change (∑ i : Fin (n+1), (-1)^i.val • fderivWithin ℝ
    (fun z => fluxForm X z (i.removeNth (frame (n+1)))) s x (frame (n+1) i)) = _
  have hcf (i : Fin (n+1)) :
      (fun z => fluxForm X z (i.removeNth (frame (n+1)))) =
        (fun z => (-1 : ℝ)^i.val * X z i) :=
    funext (fun z => flux_omitted_coefficient n X z i)
  simp_rw [hcf]
  unfold divergenceWithin partialWithin
  apply Finset.sum_congr rfl
  intro i _
  have hp := (ContinuousLinearMap.proj i : Euclidean (n+1) →L[ℝ] ℝ).hasFDerivAt (x := X x)
  have hd := ((hp.comp_hasFDerivWithinAt x hX.hasFDerivWithinAt).const_mul
    ((-1 : ℝ)^i.val)).fderivWithin hs
  simp only [Function.comp_apply, ContinuousLinearMap.proj_apply] at hd
  rw [hd]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [← mul_assoc, ← pow_two, ← pow_mul, Nat.mul_comm i.val 2, pow_mul]
  norm_num

theorem topForm_eq_coefficient_volume {n : ℕ}
    (α : (Euclidean n) [⋀^Fin n]→L[ℝ] ℝ) : α = α (frame n) • volume n := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change α.toAlternatingMap = α (frame n) • Matrix.detRowAlternating
  have h := α.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n))
  have hb : (Pi.basisFun ℝ (Fin n) : Fin n → Euclidean n) = frame n := by
    ext i j
    simp [Pi.basisFun_apply, frame, Pi.single_apply]
  rw [Pi.basisFun_det, hb] at h
  exact h

theorem green_form : Specs.SmoothManifolds.Integration.ClassicalFormulas.green_formType := by
  intro s A x hs hA
  rw [topForm_eq_coefficient_volume (extDerivWithin (oneForm A) s x),
    green_coefficient s A x hs hA]

theorem divergence_form :
    Specs.SmoothManifolds.Integration.ClassicalFormulas.divergence_formType := by
  intro n s X x hs hX
  rw [topForm_eq_coefficient_volume (extDerivWithin (fluxForm X) s x),
    divergence_coefficient n s X x hs hX]

theorem surfaceArea_eq_sqrt_cross (u v : Euclidean 3) :
    surfaceArea u v = Real.sqrt ((u ⨯₃ v) ⬝ᵥ (u ⨯₃ v)) := by
  rw [cross_dot_cross, dotProduct_comm v u, ← pow_two]
  rfl

theorem frame_normal : Specs.SmoothManifolds.Integration.ClassicalFormulas.frame_normalType := by
  intro u v huv
  have hnn : 0 ≤ (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((u ⨯₃ v) i))
  have hpos : 0 < (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) :=
    lt_of_le_of_ne hnn (Ne.symm (dotProduct_self_eq_zero.not.mpr huv))
  have ha : 0 < surfaceArea u v := by
    rw [surfaceArea_eq_sqrt_cross]
    exact Real.sqrt_pos.2 hpos
  have hsquare : (surfaceArea u v)^2 = (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) := by
    rw [surfaceArea_eq_sqrt_cross, Real.sq_sqrt hnn]
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · rw [frameNormal, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← hsquare, pow_two]
    field_simp
  · simp [frameNormal, dotProduct_smul]
  · simp [frameNormal, dotProduct_smul]
  · rw [frameNormal, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

theorem curl_normal_area :
    Specs.SmoothManifolds.Integration.ClassicalFormulas.curl_normal_areaType := by
  intro s A x u v hs hA huv
  rw [curl_coefficient s A x u v hs hA]
  have hcross := (frame_normal u v huv).2.2.2.2
  conv_lhs => rw [hcross]
  rw [dotProduct_smul, smul_eq_mul, mul_comm]

theorem curl_form : Specs.SmoothManifolds.Integration.ClassicalFormulas.curl_formType := by
  intro s A x hs hA
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, curl_coefficient s A x _ _ hs hA, triple_product_eq_det]
  rfl

theorem curl_pullback : Specs.SmoothManifolds.Integration.ClassicalFormulas.curl_pullbackType := by
  intro s A x L hs hA hL
  rw [topForm_eq_coefficient_volume ((extDerivWithin (oneForm A) s x).compContinuousLinearMap L)]
  congr 1
  change extDerivWithin (oneForm A) s x (fun i => L (frame 2 i)) = _
  have hv : (fun i => L (frame 2 i)) = ![L (frame 2 0), L (frame 2 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact curl_normal_area s A x _ _ hs hA hL

theorem normal_flux : Specs.SmoothManifolds.Integration.ClassicalFormulas.normal_fluxType := by
  intro n X ν v hν hv
  have hν0 : ν ≠ 0 := by
    intro h
    simp [h] at hν
  let t := X - (X ⬝ᵥ ν) • ν
  have ht : t ⬝ᵥ ν = 0 := by
    simp [t, sub_dotProduct, smul_dotProduct, hν]
  have hzero : (Matrix.vecCons t v : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) *ᵥ ν = 0 := by
    ext i
    cases i using Fin.cases with
    | zero => exact ht
    | succ i => exact hv i
  have hdet : Matrix.det (Matrix.vecCons t v) = 0 := by
    by_contra h
    have hinj := Matrix.mulVec_injective_of_det_ne_zero h
    apply hν0
    apply hinj
    exact hzero.trans (Matrix.mulVec_zero _).symm
  have hz : volume (n+1) (Matrix.vecCons t v) = 0 := hdet
  change ((volume (n+1)).curryLeft (X - (X ⬝ᵥ ν) • ν)) v = 0 at hz
  rw [map_sub, map_smul] at hz
  simpa [sub_eq_zero] using hz

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData ClassicalData
@[simp] theorem extendVector_coe {n q : ℕ} (d : Set (Euclidean n))
    (X : d → Euclidean q) (p : d) : extendVector d X p.val = X p := by
  simp [extendVector, p.property]
end SmoothManifolds.ClassicalResults

namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData ClassicalIntegralData ClassicalBoundaryData ClassicalData

theorem domain_geometry_exists {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) : Nonempty (DomainGeometry T d S) := by
  obtain ⟨B,J,K,ν,o,b,hB,hJ,hν,ho,hb,hnormal,hmetric⟩ :=
    ClassicalBoundaryResults.regular_domain_boundary_geometry T hT d S hreg
  obtain ⟨Cb⟩ := BundleOperations.exists_cotangent B
  obtain ⟨Db⟩ := ExteriorAlgebraResults.exists_formBundle Cb n
  obtain ⟨g,area,ρ,hg,ha,hρ,hsρ,hpρ,hnρ,heval,hzero⟩ := hmetric Cb Db
  exact ⟨{
    boundary := B
    ambient := J
    inclusion := K
    normal := ν
    orientation := o
    boundaryOrientation := b
    cotangent := Cb
    formBundle := Db
    metric := g
    area := area
    density := ρ
    natural := hB
    ambient_differential := hJ
    normal_smooth := hν
    standard := ho
    induced := hb
    differential := fun p => (hnormal p).1
    normal_unit := fun p => (hnormal p).2.1
    outward := fun p => (hnormal p).2.2.1
    tangent_hyperplane := fun p => (hnormal p).2.2.2
    induced_metric := hg
    metric_area := ha
    metric_density := hρ
    smooth_density := hsρ
    positive_density := hpρ
    nonzero_density := hnρ
    area_normal := fun p v => (heval p v).1
    density_normal := fun p v => (heval p v).2
    endpoints := hzero
  }⟩
end SmoothManifolds.ClassicalResults

namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  BundleOperationsData CovectorData ExteriorData FormPullbackData ExteriorDerivativeData
  EmbeddedData Set Filter

/-- The intrinsic derivative of a local ambient restriction is its actual
ambient derivative evaluated on the inclusion differential. Ambient regularity
is needed only at the point; agreement is local in the source manifold. -/
theorem ambient_restriction_derivative {n N k : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (j : M → Euclidean N) (hj : HasFullRankParametrizations S j)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : euclideanChart N ∈ T.smoothStructure.val)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace T (j q))
    (hL : ∀ q, IsDifferential S T j q (L q))
    (F : (q : M) → TangentSpace T (j q) ≃ₗ[ℝ] Euclidean N)
    (hF : ∀ q, IsChartCoordinates T (j q) (euclideanChart N) (F q))
    (ω : Field S k) (η : Field S (k+1))
    (hω : IsRegularField C 1 k ω) (hη : HasExteriorDerivative C ω η)
    (p : M) (α : Euclidean N → (Euclidean N) [⋀^Fin k]→L[ℝ] ℝ)
    (hα : DifferentiableAt ℝ α (j p))
    (heα : ∀ᶠ q in 𝓝 p, ∀ v : Fin k → TangentSpace S q,
      evaluate (TangentSpace S q) k (ω q) v = α (j q) (fun i => F q (L q (v i))))
    (w : Fin (k+1) → TangentSpace S p) :
    evaluate (TangentSpace S p) (k+1) (η p) w =
      extDeriv α (j p) (fun i => F p (L p (w i))) := by
  classical
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let E := C.tangent.fiberCoordinates.equiv c hc p hp
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := hω c hc ⟨p,hp⟩
  obtain ⟨V, H, hH, _⟩ := hj p c hc hp
  obtain ⟨hV, hpV, hdH, heH⟩ := hH
  have hHeq : H (c p).val = j p := heH.eq_of_nhds
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp heH
  let Φ : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ := fun z =>
    (α (H z)).compContinuousLinearMap (fderiv ℝ H z)
  have hf : IsSmoothMap S T j := (embedded_differential_exists S j hj T hT).1
  have hJac (q : M) (hq : q ∈ c.source) (hqV : (c q).val ∈ V) (hqO : q ∈ O) :
      ∀ v : TangentSpace S q,
        F q (L q v) = fderiv ℝ H (c q).val
          (C.tangent.fiberCoordinates.equiv c hc q hq v) := by
    apply differential_jacobian S T j hf q (L q) (hL q) c
      (euclideanChart N) hc hT hq (by trivial)
      (C.tangent.fiberCoordinates.equiv c hc q hq) (F q)
      (C.tangent.fiberCoordinates.isCoordinates c hc q hq) (hF q) V H hV hqV hdH
    filter_upwards [hO.mem_nhds hqO] with y hy
    exact hOsub hy
  have hcoord : ContinuousAt (fun q => (c q).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have heM : (fun q => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (G (c q).val)) =ᶠ[𝓝 p]
      (fun q => Φ (c q).val) := by
    filter_upwards [c.open_source.mem_nhds hp,
      hcoord.preimage_mem_nhds (hU.mem_nhds hpU),
      hcoord.preimage_mem_nhds (hV.mem_nhds hpV), hO.mem_nhds hpO, heα]
      with q hq hqU hqV hqO hqα
    ext v
    dsimp only [Φ]
    have hqH : H (c q).val = j q := hOsub hqO
    rw [heG ⟨q,hq⟩ hqU, hqH]
    change ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k
      ((((Pi.basisFun ℝ (Fin n)).map
        (C.tangent.fiberCoordinates.equiv c hc q hq).symm).dualBasis.exteriorPower k).equivFun
          (ω q)) v = _
    rw [@ExteriorDerivativeResults.coefficientAlternating_evaluate (TangentSpace S q) _ _ n k
      (C.tangent.fiberCoordinates.equiv c hc q hq) (ω q) v,
      hqα (fun i => (C.tangent.fiberCoordinates.equiv c hc q hq).symm (v i))]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    rw [hJac q hq hqV hqO, LinearEquiv.apply_symm_apply]
    rfl
  have heModel : (fun z : ModelSpace n a => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (G z.val))
      =ᶠ[𝓝 (c p)] (fun z => Φ z.val) := by
    rw [← c.map_nhds_eq hp]
    exact heM
  have heAmbient : (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (G z))
      =ᶠ[𝓝[Subtype.val '' c.target] (c p).val] Φ := by
    have hh : (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (G z))
        =ᶠ[𝓝[modelSet n a] (c p).val] Φ := by
      rw [← map_nhds_subtype_val (c p)]
      exact heModel
    exact hh.filter_mono (nhdsWithin_mono _ (by
      rintro z ⟨y,hy,rfl⟩
      exact y.property))
  have hdG : DifferentiableAt ℝ (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (G z)) (c p).val :=
    (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k).differentiableAt.comp _
      ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num))
  have hHcont := hdH.contDiffAt (hV.mem_nhds hpV)
  have hαH : DifferentiableAt ℝ α (H (c p).val) := hHeq.symm ▸ hα
  have hdHpoint := hHcont.differentiableAt (by simp)
  have hdDH : DifferentiableAt ℝ (fderiv ℝ H) (c p).val :=
    (hHcont.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have hdΦ : DifferentiableAt ℝ Φ (c p).val :=
    (hαH.comp _ hdHpoint).continuousAlternatingMapCompContinuousLinearMap hdDH
  have heD := ExteriorDerivativeResults.extension_independence n k (Subtype.val '' c.target)
    (uniqueDiffOn_modelDomain c.open_target) (c p).val ⟨c p,c.map_source hp,rfl⟩
      (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (G z)) Φ hdG hdΦ heAmbient
  have hnat := extDeriv_pullback hαH hHcont (by simp)
  let v : Fin (k+1) → Euclidean n := fun i => E (w i)
  have hv : (fun i => E.symm (v i)) = w := by funext i; exact E.symm_apply_apply (w i)
  rw [hη c hc p hp, ← hv]
  calc
    _ = extDeriv (fun z => ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k (G z)) (c p).val v :=
      ExteriorDerivativeResults.coordinateDerivative_evaluate_extension C k c hc ω p hp U hU hpU G hG heG v
    _ = extDeriv Φ (c p).val v := congrArg (fun A => A v) heD
    _ = extDeriv α (j p) (fun i => fderiv ℝ H (c p).val (v i)) := by
      have hh := congrArg (fun A : (Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ => A v) hnat
      simpa only [Φ, hHeq, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] using hh
    _ = _ := by
      congr 1
      funext i
      rw [hJac p hp hpV hpO, LinearEquiv.apply_symm_apply]

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData BundleOperationsData ExteriorData
  OrientationData MetricVolumeData FormPullbackData ClassicalIntegralData ClassicalBoundaryData

theorem euclideanFluxForm_evaluate {m N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold m a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean (N+1))
    (X : M → Euclidean (N+1)) (p : M) (v : Fin N → TangentSpace S p) :
    evaluate (TangentSpace S p) N (euclideanFluxForm S J X p) v =
      ClassicalData.volume (N+1) (Fin.cons (X p) (fun i => J p (v i))) := by
  rw [ClassicalIntegralResults.flux_evaluation]
  change (Matrix.of (Fin.cons (X p) (fun i => J p (v i)))).transpose.det = _
  rw [Matrix.det_transpose]
  rfl

theorem euclideanVolumeForm_evaluate {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean n)
    (p : M) (v : Fin n → TangentSpace S p) :
    evaluate (TangentSpace S p) n (euclideanVolumeForm S J p) v =
      ClassicalData.volume n (fun i => J p (v i)) := by
  unfold euclideanVolumeForm
  rw [ExteriorAlgebraResults.determinant_normalization]
  change (Matrix.of (fun i => J p (v i))).transpose.det = _
  rw [Matrix.det_transpose]
  rfl

/-- The shared coordinate volume and the standard ambient determinant use exactly
    the same sign and determinant normalization on the original fibers. -/
theorem euclideanVolume_pairing {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean n)
    (p : M) (η : DeterminantLine S p) :
    pairing p (euclideanVolumeForm S J p) η =
      standardAmbientDet n (exteriorPower.map n (J p) η) := by
  have he : exteriorPower.pairingDual ℝ (TangentSpace S p) n
      (euclideanVolumeForm S J p) =
      (standardAmbientDet n).comp (exteriorPower.map n (J p)) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [euclideanVolumeForm, standardAmbientDet,
      exteriorPower.pairingDual_ιMulti_ιMulti, Function.comp_def]
    rfl
  exact LinearMap.congr_fun he η

theorem boundary_range_orthogonal {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : V →ₗ[ℝ] Euclidean (n+1)) (ν : Euclidean (n+1))
    (hH : LinearMap.range H = LinearMap.ker (dotFunctional ν)) :
    ∀ w, H w ⬝ᵥ ν = 0 := by
  intro w
  have hm : H w ∈ LinearMap.ker (dotFunctional ν) := by
    rw [← hH]
    exact ⟨w, rfl⟩
  change ν ⬝ᵥ H w = 0 at hm
  rw [dotProduct_comm]
  exact hm

theorem planar_oneform_eq_flux {m : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold m a M)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 2)
    (A : M → Euclidean 2) :
    euclideanOneForm S J A = euclideanFluxForm S J (fun p => ![A p 1, - A p 0]) := by
  funext p
  apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  simp [euclideanOneForm, euclideanFluxForm, Fin.sum_univ_two]
  exact add_comm _ _

theorem pullback_euclideanOneForm {m n N : ℕ} {a b : ModelKind} {M P : Type}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold m a M) (B : SmoothManifold n b P)
    (j : P → M) (K : (p : P) → TangentSpace B p →ₗ[ℝ] TangentSpace S (j p))
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N) (A : M → Euclidean N) :
    pullbackField B S j K (euclideanOneForm S J A) =
      euclideanOneForm B (fun p => (J (j p)).comp (K p)) (A ∘ j) := by
  funext p
  letI := (tangent_dimension B p).1
  apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace B p) 1).1
  ext v
  rw [FormPullbackResults.pullback_apply,
    ClassicalIntegralResults.evaluate_one, ClassicalIntegralResults.evaluate_one]
  simp [euclideanOneForm, LinearMap.comp_apply]

/-- Restriction of the actual first-slot contracted Euclidean volume to a unit
normal's tangent hyperplane equals the normal component times its volume form.
The tuple condition is exactly what regular_domain_boundary_geometry concludes.
This statement also covers degree zero and bulk dimension one. -/
theorem boundary_flux_restriction {n : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (BoundaryData.intrinsicBoundary S))
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean (n+1))
    (K : (p : BoundaryData.intrinsicBoundary S) →
      TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (ν : BoundaryData.intrinsicBoundary S → Euclidean (n+1))
    (hunit : ∀ p, ν p ⬝ᵥ ν p = 1)
    (horth : ∀ p w, (J p.val (K p w)) ⬝ᵥ ν p = 0)
    (ω : Field B n)
    (hω : ∀ p (v : Fin n → TangentSpace B p),
      pairing p (ω p) (exteriorPower.ιMulti ℝ n v) =
        (Matrix.of (Fin.cons (ν p) (fun i => J p.val (K p (v i))))).det)
    (X : M → Euclidean (n+1)) :
    pullbackField B S Subtype.val K (euclideanFluxForm S J X) =
      scalarVolume (fun p => X p.val ⬝ᵥ ν p) ω := by
  funext p
  letI := (tangent_dimension B p).1
  apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace B p) n).1
  ext v
  rw [FormPullbackResults.pullback_apply, ClassicalIntegralResults.flux_evaluation]
  dsimp only [scalarVolume]

  rw [map_smul, AlternatingMap.smul_apply, smul_eq_mul,
    FormPullbackResults.evaluate_eq_pairing]
  change _ = (X p.val ⬝ᵥ ν p) * pairing p (ω p) (exteriorPower.ιMulti ℝ n v)
  rw [hω]
  have hf := normal_flux n (X p.val) (ν p) (fun i => J p.val (K p (v i)))
    (hunit p) (fun i => horth p (v i))
  change (Matrix.of (Fin.cons (X p.val) (fun k => J p.val (K p (v k))))).transpose.det = _
  rw [Matrix.det_transpose]
  exact hf

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData DifferentialData EmbeddedData ClassicalData Set Filter

/-- Full-dimensional regular domains retain uniqueness of ambient differentiation
at every point, including their true boundary. -/
theorem regular_domain_uniqueDiffOn {n : ℕ} {a : ModelKind}
    (T : SmoothManifold n .euclidean (Euclidean n))
    (hT : euclideanChart n ∈ T.smoothStructure.val)
    (d : Set (Euclidean n)) (S : SmoothManifold n a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) : UniqueDiffOn ℝ d := by
  intro x hx
  let p : d := ⟨x, hx⟩
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  have hj := ClassicalIntegralResults.regular_domain_parametrizations T hT d S hreg
  obtain ⟨V, H, hH, hrank⟩ := hj p c hc hp
  have hd := ClassicalIntegralResults.parametrizationMap_derivative Subtype.val c p hp V H hH
  have hsurj : Function.Surjective (fderiv ℝ H (c p).val) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa [Euclidean] using hrank
  have huniq := hd.uniqueDiffWithinAt
    (uniqueDiffOn_modelDomain c.open_target _ ⟨c p, c.map_source hp, rfl⟩)
    hsurj.denseRange
  have hval : ClassicalIntegralResults.parametrizationMap Subtype.val c (c p).val = x := by
    rw [ClassicalIntegralResults.parametrizationMap_at, c.left_inv hp]
  rw [hval] at huniq
  apply huniq.mono
  rw [(ClassicalIntegralResults.euclidean_chart_geometry d c).2]
  rintro _ ⟨q, _, rfl⟩
  exact q.property

/-- A local representative computes the within-set derivative intrinsically,
without fixing any values away from the original domain. -/
theorem fderivWithin_eq_local_extension {n q : ℕ}
    (d : Set (Euclidean n)) (X : Euclidean n → Euclidean q)
    (hu : UniqueDiffOn ℝ d) (U : Set (Euclidean n)) (hU : IsOpen U)
    (H : Euclidean n → Euclidean q) (hH : ContDiffOn ℝ 1 H U)
    (heH : ∀ y : d, y.val ∈ U → H y.val = X y.val)
    (p : d) (hp : p.val ∈ U) :
    fderivWithin ℝ X d p.val = fderiv ℝ H p.val := by
  have he : H =ᶠ[𝓝[d] p.val] X := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hp), self_mem_nhdsWithin] with y hyU hyd
    exact heH ⟨y, hyd⟩ hyU
  exact (((hH.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq he.symm (heH p hp).symm).fderivWithin (hu p.val p.property)

/-- Local C¹ extensions yield a continuous ambient derivative on the domain. -/
theorem local_extension_fderivWithin_continuous {n q : ℕ}
    (d : Set (Euclidean n)) (X : Euclidean n → Euclidean q)
    (hu : UniqueDiffOn ℝ d)
    (hX : LocallyContDiffOn 1 d (fun p => X p.val)) :
    Continuous (fun p : d => fderivWithin ℝ X d p.val) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := hX p
  have hder : ContinuousAt (fun p : d => fderiv ℝ H p.val) p :=
    ((hH.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hpU)).comp
      continuous_subtype_val.continuousAt
  apply hder.congr
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)] with q hq
  exact (fderivWithin_eq_local_extension d X hu U hU H hH heH q hq).symm

theorem local_extension_differentiableWithinAt {n q : ℕ}
    (d : Set (Euclidean n)) (X : Euclidean n → Euclidean q)
    (hX : LocallyContDiffOn 1 d (fun p => X p.val)) (p : d) :
    DifferentiableWithinAt ℝ X d p.val := by
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := hX p
  have he : H =ᶠ[𝓝[d] p.val] X := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hpU), self_mem_nhdsWithin] with y hyU hyd
    exact heH ⟨y, hyd⟩ hyU
  exact (((hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq he.symm (heH p hpU).symm).differentiableWithinAt

theorem local_extension_divergence_continuous {n : ℕ}
    (d : Set (Euclidean n)) (X : Euclidean n → Euclidean n)
    (hu : UniqueDiffOn ℝ d)
    (hX : LocallyContDiffOn 1 d (fun p => X p.val)) :
    Continuous (fun p : d => divergenceWithin d X p.val) := by
  have hd := local_extension_fderivWithin_continuous d X hu hX
  unfold divergenceWithin partialWithin
  fun_prop

theorem fderivWithin_restriction_support {n q : ℕ}
    (d : Set (Euclidean n)) (X : Euclidean n → Euclidean q) :
    sectionSupport (fun p : d => fderivWithin ℝ X d p.val) ⊆
      sectionSupport (fun p : d => X p.val) := by
  apply closure_minimal _ isClosed_closure
  intro p hp
  by_contra hn
  have heSub : (fun p : d => X p.val) =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with q hq
    by_contra hne
    exact hq (subset_closure hne)
  have he : X =ᶠ[𝓝[d] p.val] fun _ => 0 := by
    rw [← map_nhds_subtype_val p]
    exact heSub
  apply hp
  change fderivWithin ℝ X d p.val = 0
  rw [he.fderivWithin_eq_of_mem p.property]
  simp

theorem divergenceWithin_restriction_support {n : ℕ}
    (d : Set (Euclidean n)) (X : Euclidean n → Euclidean n) :
    sectionSupport (fun p : d => divergenceWithin d X p.val) ⊆
      sectionSupport (fun p : d => X p.val) := by
  apply (closure_mono (show
    {p : d | divergenceWithin d X p.val ≠ 0} ⊆
      {p : d | fderivWithin ℝ X d p.val ≠ 0} from ?_)).trans
      (fderivWithin_restriction_support d X)
  intro p hp hz
  apply hp
  simp [divergenceWithin, partialWithin, hz]

theorem local_extension_green_continuous
    (d : Set (Euclidean 2)) (X : Euclidean 2 → Euclidean 2)
    (hu : UniqueDiffOn ℝ d)
    (hX : LocallyContDiffOn 1 d (fun p => X p.val)) :
    Continuous (fun p : d => partialWithin d X p.val 0 1 - partialWithin d X p.val 1 0) := by
  have hd := local_extension_fderivWithin_continuous d X hu hX
  unfold partialWithin
  fun_prop

theorem greenWithin_restriction_support
    (d : Set (Euclidean 2)) (X : Euclidean 2 → Euclidean 2) :
    sectionSupport (fun p : d => partialWithin d X p.val 0 1 - partialWithin d X p.val 1 0) ⊆
      sectionSupport (fun p : d => X p.val) := by
  apply (closure_mono (show
    {p : d | partialWithin d X p.val 0 1 - partialWithin d X p.val 1 0 ≠ 0} ⊆
      {p : d | fderivWithin ℝ X d p.val ≠ 0} from ?_)).trans
      (fderivWithin_restriction_support d X)
  intro p hp hz
  apply hp
  simp [partialWithin, hz]

/-- The divergence coefficient computed from any local C¹ extension is the
actual within-domain divergence, independent of that extension. -/
theorem extDeriv_flux_local_extension {n : ℕ}
    (d : Set (Euclidean (n+1))) (X : Euclidean (n+1) → Euclidean (n+1))
    (hu : UniqueDiffOn ℝ d) (U : Set (Euclidean (n+1))) (hU : IsOpen U)
    (H : Euclidean (n+1) → Euclidean (n+1)) (hH : ContDiffOn ℝ 1 H U)
    (heH : ∀ y : d, y.val ∈ U → H y.val = X y.val)
    (p : d) (hp : p.val ∈ U) :
    extDeriv (fluxForm H) p.val = divergenceWithin d X p.val • volume (n+1) := by
  rw [← extDerivWithin_univ]
  rw [divergence_form n univ H p.val (uniqueDiffWithinAt_univ)
    ((hH.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)).differentiableWithinAt]
  congr 1
  simp only [divergenceWithin, partialWithin, fderivWithin_univ,
    fderivWithin_eq_local_extension d X hu U hU H hH heH p hp]

theorem extDeriv_oneForm_local_extension
    (d : Set (Euclidean 2)) (X : Euclidean 2 → Euclidean 2)
    (hu : UniqueDiffOn ℝ d) (U : Set (Euclidean 2)) (hU : IsOpen U)
    (H : Euclidean 2 → Euclidean 2) (hH : ContDiffOn ℝ 1 H U)
    (heH : ∀ y : d, y.val ∈ U → H y.val = X y.val)
    (p : d) (hp : p.val ∈ U) :
    extDeriv (oneForm H) p.val =
      (partialWithin d X p.val 0 1 - partialWithin d X p.val 1 0) • volume 2 := by
  rw [← extDerivWithin_univ]
  rw [green_form univ H p.val (uniqueDiffWithinAt_univ)
    ((hH.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)).differentiableWithinAt]
  simp only [partialWithin, fderivWithin_univ,
    fderivWithin_eq_local_extension d X hu U hU H hH heH p hp]

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData DifferentialData EmbeddedData ClassicalData Set Filter
  ExteriorData ExteriorDerivativeData ClassicalIntegralData BundleOperationsData

/-- C¹ first-slot contraction on an arbitrary regular domain differentiates to
its actual within-domain divergence times standard Euclidean volume. -/
theorem domain_flux_derivative {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val)
    (hL : ∀ p, IsDifferential S T Subtype.val p (L p))
    (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hF : ∀ p, IsChartCoordinates T p.val (euclideanChart (n+1)) (F p))
    (X : Euclidean (n+1) → Euclidean (n+1))
    (hX : LocallyContDiffOn 1 d (fun p => X p.val))
    (η : Field S (n+1))
    (hη : HasExteriorDerivative C
      (euclideanFluxForm S (fun p => (F p).toLinearMap.comp (L p)) (fun p => X p.val)) η) :
    η = scalarVolume (fun p => divergenceWithin d X p.val)
      (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p))) := by
  have hj := ClassicalIntegralResults.regular_domain_parametrizations T hT d S hreg
  have hu := regular_domain_uniqueDiffOn T hT d S hreg
  have hω := (ClassicalIntegralResults.euclidean_flux_regular S C Subtype.val hj
    (fun p => X p.val) hX T hT L hL F hF).1
  funext p
  letI := (tangent_dimension S p).1
  apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace S p) (n+1)).1
  ext w
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := hX p
  have hα : DifferentiableAt ℝ (fluxForm H) p.val :=
    (volume (n+1)).curryLeft.differentiableAt.comp _
      ((hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num))
  have heα : ∀ᶠ q in 𝓝 p, ∀ v : Fin n → TangentSpace S q,
      evaluate (TangentSpace S q) n
        (euclideanFluxForm S (fun p => (F p).toLinearMap.comp (L p)) (fun p => X p.val) q) v =
        fluxForm H q.val (fun i => F q (L q (v i))) := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hpU)] with q hq
    intro v
    rw [euclideanFluxForm_evaluate]
    change volume (n+1) (Fin.cons (X q.val) (fun i => F q (L q (v i)))) = _
    have hqH : H q.val = X q.val := heH q hq
    rw [← hqH]
    rfl
  rw [ambient_restriction_derivative S C Subtype.val hj T hT L hL F hF _ η hω hη
    p (fluxForm H) hα heα w, extDeriv_flux_local_extension d X hu U hU H hH heH p hpU]
  change divergenceWithin d X p.val * volume (n+1) (fun i => F p (L p (w i))) =
    evaluate (TangentSpace S p) (n+1)
      (divergenceWithin d X p.val • euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)) p) w
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [euclideanVolumeForm_evaluate]
  rfl

/-- Green's actual coefficient is the derivative of the original Euclidean
one-form on a regular planar domain with local C¹ coefficients. -/
theorem domain_green_derivative {a : ModelKind}
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : euclideanChart 2 ∈ T.smoothStructure.val)
    (d : Set (Euclidean 2)) (S : SmoothManifold 2 a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val)
    (hL : ∀ p, IsDifferential S T Subtype.val p (L p))
    (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean 2)
    (hF : ∀ p, IsChartCoordinates T p.val (euclideanChart 2) (F p))
    (X : Euclidean 2 → Euclidean 2)
    (hX : LocallyContDiffOn 1 d (fun p => X p.val))
    (η : Field S 2)
    (hη : HasExteriorDerivative C
      (euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) (fun p => X p.val)) η) :
    η = scalarVolume (fun p => partialWithin d X p.val 0 1 - partialWithin d X p.val 1 0)
      (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p))) := by
  have hj := ClassicalIntegralResults.regular_domain_parametrizations T hT d S hreg
  have hu := regular_domain_uniqueDiffOn T hT d S hreg
  have hω := (ClassicalIntegralResults.euclidean_oneform_regular S C Subtype.val hj
    (fun p => X p.val) hX T hT L hL F hF).1
  funext p
  letI := (tangent_dimension S p).1
  apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace S p) 2).1
  ext w
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := hX p
  have hα : DifferentiableAt ℝ (oneForm H) p.val :=
    (oneFormMap 2).differentiableAt.comp _
      ((hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num))
  have heα : ∀ᶠ q in 𝓝 p, ∀ v : Fin 1 → TangentSpace S q,
      evaluate (TangentSpace S q) 1
        (euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) (fun p => X p.val) q) v =
        oneForm H q.val (fun i => F q (L q (v i))) := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hpU)] with q hq
    intro v
    rw [ClassicalIntegralResults.evaluate_one]
    simp only [euclideanOneForm, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [show oneForm H q.val (fun i => F q (L q (v i))) = H q.val ⬝ᵥ F q (L q (v 0)) from
      oneFormMap_apply _ _]
    rw [heH q hq]
    rfl
  rw [ambient_restriction_derivative S C Subtype.val hj T hT L hL F hF _ η hω hη
    p (oneForm H) hα heα w, extDeriv_oneForm_local_extension d X hu U hU H hH heH p hpU]
  change _ = evaluate (TangentSpace S p) 2
    ((partialWithin d X p.val 0 1 - partialWithin d X p.val 1 0) •
      euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)) p) w
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [euclideanVolumeForm_evaluate]
  rfl

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData ClassicalIntegralData Set MeasureTheory

universe u

theorem compactTopForm_ext {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {η ζ : CompactTopForm S} (h : η.field = ζ.field) : η = ζ := by
  cases η
  cases ζ
  cases h
  rfl

theorem scalar_volume_continuous {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D) (hω : IsMetricVolume g o ω)
    (f : M → ℝ) (h : IsContinuousTopForm (scalarVolume f ω.field)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let K := C.tangent.fiberCoordinates
  have hnum := h K c hc
  have hden := ClassicalIntegralResults.metric_volume_continuous C D g o ω hω K c hc
  have hne (q : c.source) : topCoefficient K c hc q.val q.property ω.field ≠ 0 := by
    rw [ClassicalIntegralResults.topCoefficient_pairing]
    exact MetricVolumeResults.pairing_coordinate_ne_zero
      ⟨ω, ClassicalIntegralResults.metric_volume_ne_zero C D g o ω hω⟩ K c hc q
  have hquot : Continuous (fun q : c.source => f q.val) := by
    apply Continuous.congr (hnum.div hden hne)
    intro q
    change topCoefficient K c hc q.val q.property (fun p => f p • ω.field p) /
      topCoefficient K c hc q.val q.property ω.field = f q.val
    rw [GlobalIntegrationResults.topCoefficient_weight]
    exact mul_div_cancel_right₀ (f q.val) (hne q)
  have hcOn : ContinuousOn f c.source := continuousOn_iff_continuous_domRestrict.mpr hquot
  exact (hcOn p hp).continuousAt (c.open_source.mem_nhds hp)

theorem scalar_volume_compact_support {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (D : FormBundle C n) (g : Metric C) (o : Orientation S)
    (ω : Form D) (hω : IsMetricVolume g o ω) (f : M → ℝ)
    (η : CompactTopForm S) (hη : η.field = scalarVolume f ω.field) :
    Continuous f ∧ IsCompact (sectionSupport f) := by
  refine ⟨scalar_volume_continuous C D g o ω hω f (hη ▸ η.continuous), ?_⟩
  rw [← ClassicalIntegralResults.scalarVolume_support C D g o ω hω f, ← hη]
  exact η.compact_support

/-- Literal Gram integral of a given scalar multiple of the induced metric volume. -/
theorem metric_integral_localization {n N : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (D : FormBundle C n) (g : Metric C) (o : Orientation S)
    (ω : Form D) (hω : IsMetricVolume g o ω)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N)
    (hg : ∀ p v w, metricForm g p v w = ∑ i, J p v i * J p w i)
    (f : M → ℝ) (η : CompactTopForm S) (hη : η.field = scalarVolume f ω.field)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (K : FiberCoordinates S) {ι : Type u} (c : ι → ModelChart n a M)
    (hc : ∀ i, c i ∈ S.smoothStructure.val) (ρ : ι → M → ℝ)
    (hρ : IsLocalization c ρ η) :
    I η = ∑ᶠ i, ∫ x, surfaceIntegrand J K (c i) (hc i) (fun p => ρ i p * f p) x := by
  obtain ⟨hf, hfc⟩ := scalar_volume_compact_support C D g o ω hω f η hη
  obtain ⟨ζ, hζ, hloc⟩ := ClassicalIntegralResults.scalar_volume_localization S C D g o ω hω f hf hfc
  have he : ζ = η := compactTopForm_ext (hζ.trans hη.symm)
  subst ζ
  rw [hloc I hI K c hc ρ hρ]
  apply finsum_congr
  intro i
  rw [ClassicalIntegralResults.gramIntegrand_induced S C g J hg]

end SmoothManifolds.ClassicalResults

namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData ClassicalIntegralData Set MeasureTheory

theorem domain_integral_from_derivative {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S)
    (C : CotangentBundle S) (D : FormBundle C (n+1))
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (hB : IsNaturalBoundary S B) (o : Orientation S) (b : Orientation B)
    (hb : IsInducedOrientation o b)
    (L : (p : d) → TangentSpace S p →ₗ[ℝ] TangentSpace T p.val)
    (hL : ∀ p, IsDifferential S T Subtype.val p (L p))
    (F : (p : d) → TangentSpace T p.val ≃ₗ[ℝ] Euclidean (n+1))
    (hF : ∀ p, IsChartCoordinates T p.val (EmbeddedData.euclideanChart (n+1)) (F p))
    (hpos : ∀ p v, IsPositive (o.val p) v ↔
      0 < pairing p (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)) p) v)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    (ω : Field S n) (hω : IsRegularField C 1 n ω)
    (hcompact : IsCompact (sectionSupport ω)) (f : d → ℝ) (hf : Continuous f)
    (hη : HasExteriorDerivative C ω
      (scalarVolume f (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)))))
    (hfc : IsCompact (sectionSupport f)) :
    Integrable (extendScalar d f) ∧
    ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm B → ℝ),
      IsIntegral o I → IsIntegral b Ib →
      ∃ (η : CompactTopForm S) (β : CompactTopForm B),
        η.field = scalarVolume f (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p))) ∧
        β.field = pullbackField B S Subtype.val K ω ∧
        I η = ∫ x in d, extendScalar d f x ∧
        (∫ x in d, extendScalar d f x) = Ib β := by
  obtain ⟨ζ, hζ, hint, hζint⟩ := ClassicalIntegralResults.standard_oriented_domain_integral
    T hT d S hreg C D o L hL F hF hpos f hf hfc
  refine ⟨hint, ?_⟩
  intro I Ib hI hIb
  obtain ⟨η, β, hdη, hsη, hβ, he⟩ := StokesResults.stokes S C B A hB o b hb K hK
    I Ib hI hIb ω hω hcompact
  have heη := ExteriorDerivativeResults.derivative_unique C n ω η.field
    (scalarVolume f (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)))) hdη hη
  have hζeq : η = ζ := compactTopForm_ext (heη.trans hζ.symm)
  have hiη : I η = ∫ x in d, extendScalar d f x := hζeq ▸ hζint I hI
  exact ⟨η, β, heη, hβ, hiη, hiη.symm.trans he⟩
end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  BundleOperationsData CovectorData ExteriorData FormPullbackData ExteriorDerivativeData
  ClassicalIntegralData ClassicalIntegralResults EmbeddedData Set Filter

-- Intended to be appended after ambient_restriction_derivative.
theorem surface_curl_evaluation {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold 2 a M) (C : CotangentBundle S)
    (j : M → Euclidean 3) (hj : HasFullRankParametrizations S j)
    (T : SmoothManifold 3 .euclidean (Euclidean 3))
    (hT : euclideanChart 3 ∈ T.smoothStructure.val)
    (L : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace T (j q))
    (hL : ∀ q, IsDifferential S T j q (L q))
    (F : (q : M) → TangentSpace T (j q) ≃ₗ[ℝ] Euclidean 3)
    (hF : ∀ q, IsChartCoordinates T (j q) (euclideanChart 3) (F q))
    (U : Set (Euclidean 3)) (hU : IsOpen U) (hjU : ∀ p, j p ∈ U)
    (A : Euclidean 3 → Euclidean 3) (hA : ContDiffOn ℝ 1 A U)
    (η : Field S 2)
    (hη : HasExteriorDerivative C
      (euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) (fun p => A (j p))) η)
    (p : M) (w : Fin 2 → TangentSpace S p) :
    evaluate (TangentSpace S p) 2 (η p) w =
      ClassicalData.curlWithin univ A (j p) ⬝ᵥ (F p (L p (w 0)) ⨯₃ F p (L p (w 1))) := by
  have hreg := (ambient_oneform_regular S C j hj U hU hjU A hA T hT L hL F hF).1
  have hAd : DifferentiableAt ℝ A (j p) :=
    ((hA (j p) (hjU p)).contDiffAt (hU.mem_nhds (hjU p))).differentiableAt (by norm_num)
  have hform : DifferentiableAt ℝ (ClassicalData.oneForm A) (j p) :=
    (ClassicalData.oneFormMap 3).differentiableAt.comp _ hAd
  have heval := ambient_restriction_derivative S C j hj T hT L hL F hF
    (euclideanOneForm S (fun p => (F p).toLinearMap.comp (L p)) (fun p => A (j p))) η
    hreg hη p (ClassicalData.oneForm A) hform (Filter.Eventually.of_forall (fun q v => by
      rw [evaluate_one, euclideanOneForm_apply]
      simpa only [ClassicalData.oneForm, oneFormMap_apply, dotProduct,
        LinearMap.comp_apply, LinearEquiv.coe_coe])) w
  rw [heval, ← extDerivWithin_univ]
  have hw : (fun i : Fin 2 => F p (L p (w i))) =
      ![F p (L p (w 0)), F p (L p (w 1))] := by
    funext i
    fin_cases i <;> rfl
  rw [hw]
  exact curl_coefficient univ A (j p) _ _ uniqueDiffWithinAt_univ hAd.differentiableWithinAt

end SmoothManifolds.ClassicalResults

namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData BundleOperationsData ExteriorData
  ClassicalIntegralData OrientationData

theorem surface_curl_field {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M) (C : CotangentBundle S)
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean 3)
    (β : Field S 2) (ν X : M → Euclidean 3)
    (hcross : ∀ p u v, J p u ⨯₃ J p v =
      pairing p (β p) (exteriorPower.ιMulti ℝ 2 ![u, v]) • ν p)
    (η : Field S 2)
    (hη : ∀ p (w : Fin 2 → TangentSpace S p),
      evaluate (TangentSpace S p) 2 (η p) w = X p ⬝ᵥ (J p (w 0) ⨯₃ J p (w 1))) :
    η = scalarVolume (fun p => X p ⬝ᵥ ν p) β := by
  funext p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let E := C.tangent.fiberCoordinates.equiv c hc p hp
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective E.toLinearMap E.injective
  apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace S p) 2).1
  ext w
  rw [hη, hcross, dotProduct_smul]
  have hw : ![w 0, w 1] = w := by
    funext i
    fin_cases i <;> rfl
  have hpair : pairing p (β p) (exteriorPower.ιMulti ℝ 2 ![w 0,w 1]) =
      evaluate (TangentSpace S p) 2 (β p) w := by
    rw [hw]
    exact (exteriorPower.alternatingMapLinearEquiv_symm_apply
      (R := ℝ) (M := TangentSpace S p) (N := ℝ)
      ((exteriorPower.pairingDual ℝ (TangentSpace S p) 2) (β p)) w).symm
  rw [hpair]
  simp only [scalarVolume, map_smul, smul_apply, smul_eq_mul]
  exact mul_comm _ _

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData ClassicalIntegralData ClassicalBoundaryData ClassicalData
open Set MeasureTheory
open scoped Topology BigOperators

/-- The pointwise divergence and outward-flux identifications hold on every
regular Euclidean domain, independently of support or compactness. -/
theorem classical_divergence_differential {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (X : Euclidean (n+1) → Euclidean (n+1))
    (hX : LocallyContDiffOn 1 d (fun p => X p.val)) :
    ∃ G : DomainGeometry T d S,
      HasExteriorDerivative C
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val))
        (scalarVolume (fun p => divergenceWithin d X p.val)
          (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap))) ∧
      pullbackField G.boundary S Subtype.val G.inclusion
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val)) =
        scalarVolume (fun p => X p.val.val ⬝ᵥ G.normal p) G.area.field := by
  classical
  obtain ⟨G⟩ := domain_geometry_exists T hT d S hreg
  choose L F hL hF hJF using G.ambient_differential
  have hJF' : (fun p => (F p).toLinearMap.comp (L p)) =
      (fun p => (G.ambient p).toLinearMap) := funext (fun p => (hJF p).symm)
  have hj := ClassicalIntegralResults.regular_domain_parametrizations T hT d S hreg
  have hωreg := ClassicalIntegralResults.euclidean_flux_regular S C Subtype.val hj
    (fun p => X p.val) hX T hT L hL F hF
  rw [hJF'] at hωreg
  obtain ⟨ξ, hξ, _⟩ := ExteriorDerivativeResults.c1_derivative_exists C n
    (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val)) hωreg.1
  have hξ' := hξ
  rw [← hJF'] at hξ'
  have hξeq := domain_flux_derivative T hT d S hreg C L hL F hF X hX ξ hξ'
  rw [hJF'] at hξeq
  rw [hξeq] at hξ
  have hflux := boundary_flux_restriction S G.boundary
    (fun p => (G.ambient p).toLinearMap) G.inclusion G.normal G.normal_unit
    (fun p w => boundary_range_orthogonal
      ((G.ambient p.val).toLinearMap.comp (G.inclusion p))
      (G.normal p) (G.tangent_hyperplane p) w)
    G.area.field G.area_normal (fun p => X p.val)
  exact ⟨G, hξ, hflux⟩

/-- Divergence theorem with the genuine outward Euclidean normal and metric
boundary density. Both integrals are identified with their classical coordinate
integrals, and no values away from d are required to be C¹. -/
theorem classical_divergence {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (X : Euclidean (n+1) → Euclidean (n+1))
    (hX : LocallyContDiffOn 1 d (fun p => X p.val))
    (hcomp : IsCompact d ∨ IsCompact (sectionSupport (fun p : d => X p.val))) :
    ∃ G : DomainGeometry T d S,
      HasExteriorDerivative C
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val))
        (scalarVolume (fun p => divergenceWithin d X p.val)
          (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap))) ∧
      pullbackField G.boundary S Subtype.val G.inclusion
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val)) =
        scalarVolume (fun p => X p.val.val ⬝ᵥ G.normal p) G.area.field ∧
      Integrable (extendScalar d (fun p => divergenceWithin d X p.val)) ∧
      ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm G.boundary → ℝ),
        IsIntegral G.orientation I → IsIntegral G.boundaryOrientation Ib →
        ∃ (η : CompactTopForm S) (β : CompactTopForm G.boundary),
          η.field = scalarVolume (fun p => divergenceWithin d X p.val)
            (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap)) ∧
          β.field = scalarVolume (fun p => X p.val.val ⬝ᵥ G.normal p) G.area.field ∧
          I η = ∫ x in d, extendScalar d (fun p => divergenceWithin d X p.val) x ∧
          (∫ x in d, extendScalar d (fun p => divergenceWithin d X p.val) x) = Ib β ∧
          ∀ (K : FiberCoordinates G.boundary) {ι : Type}
            (c : ι → ModelChart n .euclidean (intrinsicBoundary S))
            (hc : ∀ i, c i ∈ G.boundary.smoothStructure.val) (ρ : ι → intrinsicBoundary S → ℝ),
            IsLocalization c ρ β →
            (∫ x in d, extendScalar d (fun p => divergenceWithin d X p.val) x) =
              ∑ᶠ i, ∫ x, surfaceIntegrand
                (fun p => (G.ambient p.val).toLinearMap.comp (G.inclusion p)) K (c i) (hc i)
                (fun p => ρ i p * (X p.val.val ⬝ᵥ G.normal p)) x := by
  classical
  obtain ⟨G⟩ := domain_geometry_exists T hT d S hreg
  choose L F hL hF hJF using G.ambient_differential
  have hJF' : (fun p => (F p).toLinearMap.comp (L p)) =
      (fun p => (G.ambient p).toLinearMap) := funext (fun p => (hJF p).symm)
  have hj := ClassicalIntegralResults.regular_domain_parametrizations T hT d S hreg
  have hωreg := ClassicalIntegralResults.euclidean_flux_regular S C Subtype.val hj
    (fun p => X p.val) hX T hT L hL F hF
  rw [hJF'] at hωreg
  have hXcompact : IsCompact (sectionSupport (fun p : d => X p.val)) := by
    rcases hcomp with hd | hXc
    · letI : CompactSpace d := isCompact_iff_compactSpace.mp hd
      exact isClosed_closure.isCompact
    · exact hXc
  have hωcomp := hωreg.2.2 hXcompact
  obtain ⟨ξ, hξ, _⟩ := ExteriorDerivativeResults.c1_derivative_exists C n
    (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val)) hωreg.1
  have hξ' := hξ
  rw [← hJF'] at hξ'
  have hξeq := domain_flux_derivative T hT d S hreg C L hL F hF X hX ξ hξ'
  rw [hJF'] at hξeq
  rw [hξeq] at hξ
  have hflux := boundary_flux_restriction S G.boundary
    (fun p => (G.ambient p).toLinearMap) G.inclusion G.normal G.normal_unit
    (fun p w => boundary_range_orthogonal
      ((G.ambient p.val).toLinearMap.comp (G.inclusion p))
      (G.normal p) (G.tangent_hyperplane p) w)
    G.area.field G.area_normal (fun p => X p.val)
  obtain ⟨D⟩ := ExteriorAlgebraResults.exists_formBundle C (n+1)
  have hpositive : ∀ p v, IsPositive (G.orientation.val p) v ↔
      0 < pairing p (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)) p) v := by
    intro p v
    rw [hJF', euclideanVolume_pairing]
    exact G.standard p v
  have hu := regular_domain_uniqueDiffOn T hT d S hreg
  have hf := local_extension_divergence_continuous d X hu hX
  have hfc : IsCompact (sectionSupport (fun p : d => divergenceWithin d X p.val)) :=
    hXcompact.of_isClosed_subset isClosed_closure (divergenceWithin_restriction_support d X)
  have hξ'' : HasExteriorDerivative C
      (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val))
      (scalarVolume (fun p => divergenceWithin d X p.val)
        (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)))) := by
    rw [hJF']
    exact hξ
  have hmain := domain_integral_from_derivative T hT d S hreg C D G.boundary G.cotangent
    G.natural G.orientation G.boundaryOrientation G.induced L hL F hF hpositive
    G.inclusion G.differential
    (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p.val))
    hωreg.1 hωcomp (fun p => divergenceWithin d X p.val) hf hξ'' hfc
  refine ⟨G, hξ, hflux, hmain.1, ?_⟩
  intro I Ib hI hIb
  obtain ⟨η,β,hη,hβ,hint,he⟩ := hmain.2 I Ib hI hIb
  rw [hJF'] at hη
  have hβflux := hβ.trans hflux
  refine ⟨η,β,hη,hβflux,hint,he,?_⟩
  intro K ι c hc ρ hρ
  rw [he]
  exact metric_integral_localization G.cotangent G.formBundle G.metric G.boundaryOrientation
    G.area G.metric_area (fun p => (G.ambient p.val).toLinearMap.comp (G.inclusion p))
    (fun p v w => by rw [G.induced_metric]; rfl)
    (fun p => X p.val.val ⬝ᵥ G.normal p) β hβflux Ib hIb K c hc ρ hρ

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData ClassicalIntegralData ClassicalBoundaryData ClassicalData
open Set MeasureTheory
open scoped Topology BigOperators

/-- Green's theorem on every compact regular planar domain, with the actual
standard orientation and its actual induced boundary line integral. The
coefficient functions need only admit local C¹ extensions along the domain. -/
theorem classical_green {a : ModelKind}
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : EmbeddedData.euclideanChart 2 ∈ T.smoothStructure.val)
    (d : Set (Euclidean 2)) (S : SmoothManifold 2 a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (A : Euclidean 2 → Euclidean 2)
    (hA : LocallyContDiffOn 1 d (fun p => A p.val)) (hd : IsCompact d) :
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
      (J : (p : d) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
      (Kb : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (o : Orientation S) (b : Orientation B),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      (∀ p v, IsPositive (o.val p) v ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap v)) ∧
      IsInducedOrientation o b ∧
      (∀ p, IsDifferential B S Subtype.val p (Kb p)) ∧
      PlanarBoundaryComponents S B J Kb b ∧
      HasExteriorDerivative C
        (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => A p.val))
        (scalarVolume (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0)
          (euclideanVolumeForm S (fun p => (J p).toLinearMap))) ∧
      Integrable (extendScalar d
        (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0)) ∧
      ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm B → ℝ),
        IsIntegral o I → IsIntegral b Ib →
        ∃ (η : CompactTopForm S) (β : CompactTopForm B),
          η.field = scalarVolume
            (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0)
            (euclideanVolumeForm S (fun p => (J p).toLinearMap)) ∧
          β.field = euclideanOneForm B
            (fun p => (J p.val).toLinearMap.comp (Kb p)) (fun p => A p.val.val) ∧
          I η = ∫ x in d, extendScalar d
            (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0) x ∧
          (∫ x in d, extendScalar d
            (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0) x) = Ib β ∧
          ∀ (s : SignedCharts B), RepresentsSignedCharts b.val s →
          ∀ (K : FiberCoordinates B) {ι : Type}
            (c : ι → ModelChart 1 .euclidean (intrinsicBoundary S))
            (hc : ∀ i, c i ∈ B.smoothStructure.val) (ρ : ι → intrinsicBoundary S → ℝ),
            IsLocalization c ρ β →
            (∫ x in d, extendScalar d
              (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0) x) =
              ∑ᶠ i, ∫ x, lineIntegrand s K (c i) (hc i)
                (fun p => (J p.val).toLinearMap.comp (Kb p))
                (fun p => ρ i p • A p.val.val) x := by
  classical
  letI : CompactSpace d := isCompact_iff_compactSpace.mp hd
  obtain ⟨B,J,Kb,o,b,hB,hJ,ho,hb,hKb,hcomponents⟩ :=
    ClassicalBoundaryResults.compact_planar_boundary_components T hT d S hreg hd
  obtain ⟨Cb⟩ := BundleOperations.exists_cotangent B
  have hJoriginal := hJ
  choose L F hL hF hJF using hJ
  have hJF' : (fun p => (F p).toLinearMap.comp (L p)) =
      (fun p => (J p).toLinearMap) := funext (fun p => (hJF p).symm)
  have hj := ClassicalIntegralResults.regular_domain_parametrizations T hT d S hreg
  have hωreg := ClassicalIntegralResults.euclidean_oneform_regular S C Subtype.val hj
    (fun p => A p.val) hA T hT L hL F hF
  rw [hJF'] at hωreg
  have hωcomp : IsCompact (sectionSupport
      (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => A p.val))) :=
    isClosed_closure.isCompact
  obtain ⟨ξ, hξ, _⟩ := ExteriorDerivativeResults.c1_derivative_exists C 1
    (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => A p.val)) hωreg.1
  have hξ' := hξ
  rw [← hJF'] at hξ'
  have hξeq := domain_green_derivative T hT d S hreg C L hL F hF A hA ξ hξ'
  rw [hJF'] at hξeq
  rw [hξeq] at hξ
  obtain ⟨D⟩ := ExteriorAlgebraResults.exists_formBundle C 2
  have hpositive : ∀ p v, IsPositive (o.val p) v ↔
      0 < pairing p (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)) p) v := by
    intro p v
    rw [hJF', euclideanVolume_pairing]
    exact ho p v
  have hu := regular_domain_uniqueDiffOn T hT d S hreg
  have hf := local_extension_green_continuous d A hu hA
  have hfc : IsCompact (sectionSupport
      (fun p : d => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0)) :=
    isClosed_closure.isCompact
  have hξ'' : HasExteriorDerivative C
      (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => A p.val))
      (scalarVolume (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0)
        (euclideanVolumeForm S (fun p => (F p).toLinearMap.comp (L p)))) := by
    rw [hJF']
    exact hξ
  have hmain := domain_integral_from_derivative T hT d S hreg C D B Cb
    hB o b hb L hL F hF hpositive
    Kb hKb
    (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => A p.val))
    hωreg.1 hωcomp (fun p => partialWithin d A p.val 0 1 - partialWithin d A p.val 1 0)
    hf hξ'' hfc
  have hpull := pullback_euclideanOneForm S B Subtype.val Kb
    (fun p => (J p).toLinearMap) (fun p => A p.val)
  obtain ⟨ζ,hζ,hζreg,_⟩ := StokesResults.boundary_top_form S C B Cb
    hB Kb hKb
    (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => A p.val))
    hωreg.1 hωcomp
  have hζfield : ζ.field = euclideanOneForm B
      (fun p => (J p.val).toLinearMap.comp (Kb p)) (fun p => A p.val.val) :=
    hζ.trans hpull
  have hζcont := ExteriorDerivativeResults.regular_continuous Cb 1 1 ζ.field hζreg
  have hζcomp := ζ.compact_support
  rw [hζfield] at hζcont hζcomp
  obtain ⟨βline,hβline,hline⟩ := ClassicalIntegralResults.line_integral B Cb
    b (fun p => (J p.val).toLinearMap.comp (Kb p))
    (fun p => A p.val.val) hζcont hζcomp
  refine ⟨B,J,Kb,o,b,hB,hJoriginal,ho,hb,hKb,hcomponents,hξ,hmain.1,?_⟩
  intro I Ib hI hIb
  obtain ⟨η,β,hη,hβ,hint,he⟩ := hmain.2 I Ib hI hIb
  rw [hJF'] at hη
  have hβfield : β.field = euclideanOneForm B
      (fun p => (J p.val).toLinearMap.comp (Kb p)) (fun p => A p.val.val) :=
    hβ.trans hpull
  have hβeq : β = βline := compactTopForm_ext (hβfield.trans hβline.symm)
  refine ⟨η,β,hη,hβfield,hint,he,?_⟩
  intro s hs K ι c hc ρ hρ
  have hloc := (hline Ib hIb s hs K).2 c hc ρ
  rw [← hβeq] at hloc
  exact he.trans (hloc hρ)

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData ClassicalIntegralData ClassicalIntegralResults
  ClassicalBoundaryData EmbeddedData Set MeasureTheory

theorem pullback_euclidean_oneform {n m N : ℕ} {a b : ModelKind} {M P : Type}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (B : SmoothManifold m b P) (f : P → M)
    (K : (p : P) → TangentSpace B p →ₗ[ℝ] TangentSpace S (f p))
    (J : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean N) (A : M → Euclidean N) :
    pullbackField B S f K (euclideanOneForm S J A) =
      euclideanOneForm B (fun p => (J (f p)).comp (K p)) (fun p => A (f p)) := by
  funext p
  apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace B p))).injective
  ext v
  have h := @FormPullbackResults.evaluate_fiberPullback
    (TangentSpace B p) (TangentSpace S (f p)) _ _ _ _ 1 (K p)
    (euclideanOneForm S J A (f p)) (fun _ => v)
  rw [evaluate_one, evaluate_one] at h
  exact h.trans (by simp)

/-- Full classical surface Stokes, with the actual induced metric, smooth normal,
compact-support alternative on the pulled-back one-form, and literal localized
Gram and oriented line integrals. B,b,K and L,F represent the canonical natural
boundary and actual inclusion differentials supplied by the upstream interfaces. -/
theorem surface_stokes {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3)
    (hT : euclideanChart 3 ∈ T.smoothStructure.val)
    (hj : MapClassData.IsSmoothEmbedding S T j)
    (o : Orientation S) (C : CotangentBundle S) (D : FormBundle C 2)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (hL : ∀ p, IsDifferential S T j p (L p))
    (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean 3)
    (hF : ∀ p, IsChartCoordinates T (j p) (euclideanChart 3) (F p))
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (Cb : CotangentBundle B)
    (hB : IsNaturalBoundary S B) (b : Orientation B) (hb : IsInducedOrientation o b)
    (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hK : ∀ p, IsDifferential B S Subtype.val p (K p))
    (U : Set (Euclidean 3)) (hU : IsOpen U) (hjU : ∀ p, j p ∈ U)
    (A : Euclidean 3 → Euclidean 3) (hA : ContDiffOn ℝ 1 A U) :
    let J := fun p => (F p).toLinearMap.comp (L p)
    let ω := euclideanOneForm S J (fun p => A (j p))
    ∃ (g : Metric C) (vol : Form D) (ν : M → Euclidean 3),
      (∀ p, metricForm g p = euclideanPullback (V := TangentSpace S p) (J p)) ∧ IsMetricVolume g o vol ∧
      FrameData.VectorSmooth S.smoothStructure.val ν ∧
      (∀ p, ν p ⬝ᵥ ν p = 1 ∧ ∀ v, ν p ⬝ᵥ J p v = 0) ∧
      (∀ p u v, J p u ⨯₃ J p v =
        pairing p (vol.field p) (exteriorPower.ιMulti ℝ 2 ![u,v]) • ν p) ∧
      HasExteriorDerivative C ω
        (scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) ∧
      (∀ p (v : Fin 2 → TangentSpace S p),
        extDeriv (ClassicalData.oneForm A) (j p) (fun i => J p (v i)) =
          evaluate (TangentSpace S p) 2
            ((scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) p) v) ∧
      ((IsCompact (univ : Set M) ∨ IsCompact (sectionSupport ω)) →
        ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm B → ℝ),
          IsIntegral o I → IsIntegral b Ib →
          ∃ (η : CompactTopForm S) (β : CompactTopForm B),
            η.field = scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field ∧
            β.field = euclideanOneForm B (fun p => (J p.val).comp (K p))
              (fun p => A (j p.val)) ∧
            I η = Ib β ∧
            ∀ (Ks : FiberCoordinates S) (Kb : FiberCoordinates B)
              (s : SignedCharts B), RepresentsSignedCharts b.val s →
            ∀ {ι κ : Type} (c : ι → ModelChart 2 a M)
              (hc : ∀ i, c i ∈ S.smoothStructure.val) (ρ : ι → M → ℝ),
              IsLocalization c ρ η →
            ∀ (d : κ → ModelChart 1 .euclidean (intrinsicBoundary S))
              (hd : ∀ i, d i ∈ B.smoothStructure.val)
              (σ : κ → intrinsicBoundary S → ℝ), IsLocalization d σ β →
              (∑ᶠ i, ∫ x, surfaceIntegrand J Ks (c i) (hc i)
                (fun p => ρ i p * (ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p)) x) =
              ∑ᶠ i, ∫ x, lineIntegrand s Kb (d i) (hd i)
                (fun p => (J p.val).comp (K p)) (fun p => σ i p • A (j p.val)) x) := by
  classical
  dsimp only
  let J := fun p => (F p).toLinearMap.comp (L p)
  let ω := euclideanOneForm S J (fun p => A (j p))
  obtain ⟨Jg, g, vol, ν, hJg, hg, hvol, hνsm, hν, hcross, hpos⟩ :=
    ClassicalBoundaryResults.surface_geometry S T j hT hj o C D
  have heJ : Jg = J := by
    funext p
    apply (ClassicalBoundaryResults.euclidean_differential_exists_unique S T j hT hj.1 p).unique
    · exact hJg p
    · exact ⟨L p, F p, hL p, hF p, rfl⟩
  subst Jg
  have hparam := immersion_parametrizations S T hT j hj.1 hj.2.2.1
  have hω := (ambient_oneform_regular S C j hparam U hU hjU A hA T hT L hL F hF).1
  have hderiv : HasExteriorDerivative C ω
      (scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) := by
    obtain ⟨ζ, hζ, _⟩ := ExteriorDerivativeResults.c1_derivative_exists C 1 ω hω
    have heζ := surface_curl_field S C J vol.field ν
      (fun p => ClassicalData.curlWithin univ A (j p)) hcross ζ
      (fun p w => surface_curl_evaluation S C j hparam T hT L hL F hF U hU hjU A hA ζ hζ p w)
    exact heζ ▸ hζ
  have hpullback (p : M) (v : Fin 2 → TangentSpace S p) :
      extDeriv (ClassicalData.oneForm A) (j p) (fun i => J p (v i)) =
        evaluate (TangentSpace S p) 2
          ((scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) p) v := by
    have hAd : DifferentiableAt ℝ A (j p) :=
      ((hA (j p) (hjU p)).contDiffAt (hU.mem_nhds (hjU p))).differentiableAt (by norm_num)
    have hform : DifferentiableAt ℝ (ClassicalData.oneForm A) (j p) :=
      (ClassicalData.oneFormMap 3).differentiableAt.comp _ hAd
    exact (ambient_restriction_derivative S C j hparam T hT L hL F hF ω
      (scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field)
      hω hderiv p (ClassicalData.oneForm A) hform
      (Filter.Eventually.of_forall (fun q w => by
        rw [evaluate_one, euclideanOneForm_apply]
        simp only [J, ClassicalData.oneForm, oneFormMap_apply, dotProduct,
          LinearMap.comp_apply, LinearEquiv.coe_coe])) v).symm
  refine ⟨g, vol, ν, hg, hvol, hνsm, hν, hcross, hderiv, hpullback, ?_⟩
  intro hcompact I Ib hI hIb
  have hωc : IsCompact (sectionSupport ω) := by
    rcases hcompact with hcompact | hcompact
    · letI : CompactSpace M := isCompact_univ_iff.mp hcompact
      exact isClosed_closure.isCompact
    · exact hcompact
  obtain ⟨η, β, hη, hsη, hβ, hstokes⟩ :=
    StokesResults.stokes S C B Cb hB o b hb K hK I Ib hI hIb ω hω hωc
  have heη := ExteriorDerivativeResults.derivative_unique C 1 ω η.field
    (scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) hη hderiv
  have heβ : β.field = euclideanOneForm B (fun p => (J p.val).comp (K p))
      (fun p => A (j p.val)) := hβ.trans (pullback_euclidean_oneform S B Subtype.val K J _)
  refine ⟨η, β, heη, heβ, hstokes, ?_⟩
  intro Ks Kb s hs ι κ c hc ρ hρ d hd σ hσ
  have hi := metric_integral_localization C D g o vol hvol J
    (fun p v w => congrArg (fun z : LinearMap.BilinForm ℝ (TangentSpace S p) => z v w) (hg p))
    (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) η heη I hI Ks c hc ρ hρ
  rw [← hi, hstokes]
  rw [GlobalIntegrationResults.localization B b Ib hIb s hs Kb d hd σ β hσ]
  apply finsum_congr
  intro i
  have hf : (fun p => σ i p • β.field p) = euclideanOneForm B
      (fun p => (J p.val).comp (K p)) (fun p => σ i p • A (j p.val)) := by
    rw [heβ]
    funext p
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace B p))).injective
    simp only [map_smul, euclideanOneForm, LinearEquiv.apply_symm_apply,
      Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  rw [hf, coordinateIntegral, line_coefficient]


/-- The canonical-data-free form: all actual inclusion and boundary
differentials, the natural boundary, and its outward-first orientation are
constructed from the original smooth oriented embedding. -/
theorem classical_surface_stokes {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold 2 a M)
    (T : SmoothManifold 3 .euclidean (Euclidean 3)) (j : M → Euclidean 3)
    (hT : euclideanChart 3 ∈ T.smoothStructure.val)
    (hj : MapClassData.IsSmoothEmbedding S T j)
    (o : Orientation S) (C : CotangentBundle S) (D : FormBundle C 2)
    (U : Set (Euclidean 3)) (hU : IsOpen U) (hjU : ∀ p, j p ∈ U)
    (A : Euclidean 3 → Euclidean 3) (hA : ContDiffOn ℝ 1 A U) :
    ∃ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
      (F : (p : M) → TangentSpace T (j p) ≃ₗ[ℝ] Euclidean 3)
      (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) (Cb : CotangentBundle B)
      (b : Orientation B)
      (K : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
      (∀ p, IsDifferential S T j p (L p)) ∧
      (∀ p, IsChartCoordinates T (j p) (euclideanChart 3) (F p)) ∧
      IsNaturalBoundary S B ∧ IsInducedOrientation o b ∧
      (∀ p, IsDifferential B S Subtype.val p (K p)) ∧
    let J := fun p => (F p).toLinearMap.comp (L p)
    let ω := euclideanOneForm S J (fun p => A (j p))
    ∃ (g : Metric C) (vol : Form D) (ν : M → Euclidean 3),
      (∀ p, metricForm g p = euclideanPullback (V := TangentSpace S p) (J p)) ∧ IsMetricVolume g o vol ∧
      FrameData.VectorSmooth S.smoothStructure.val ν ∧
      (∀ p, ν p ⬝ᵥ ν p = 1 ∧ ∀ v, ν p ⬝ᵥ J p v = 0) ∧
      (∀ p u v, J p u ⨯₃ J p v =
        pairing p (vol.field p) (exteriorPower.ιMulti ℝ 2 ![u,v]) • ν p) ∧
      HasExteriorDerivative C ω
        (scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) ∧
      (∀ p (v : Fin 2 → TangentSpace S p),
        extDeriv (ClassicalData.oneForm A) (j p) (fun i => J p (v i)) =
          evaluate (TangentSpace S p) 2
            ((scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field) p) v) ∧
      ((IsCompact (univ : Set M) ∨ IsCompact (sectionSupport ω)) →
        ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm B → ℝ),
          IsIntegral o I → IsIntegral b Ib →
          ∃ (η : CompactTopForm S) (β : CompactTopForm B),
            η.field = scalarVolume (fun p => ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p) vol.field ∧
            β.field = euclideanOneForm B (fun p => (J p.val).comp (K p))
              (fun p => A (j p.val)) ∧
            I η = Ib β ∧
            ∀ (Ks : FiberCoordinates S) (Kb : FiberCoordinates B)
              (s : SignedCharts B), RepresentsSignedCharts b.val s →
            ∀ {ι κ : Type} (c : ι → ModelChart 2 a M)
              (hc : ∀ i, c i ∈ S.smoothStructure.val) (ρ : ι → M → ℝ),
              IsLocalization c ρ η →
            ∀ (d : κ → ModelChart 1 .euclidean (intrinsicBoundary S))
              (hd : ∀ i, d i ∈ B.smoothStructure.val)
              (σ : κ → intrinsicBoundary S → ℝ), IsLocalization d σ β →
              (∑ᶠ i, ∫ x, surfaceIntegrand J Ks (c i) (hc i)
                (fun p => ρ i p * (ClassicalData.curlWithin univ A (j p) ⬝ᵥ ν p)) x) =
              ∑ᶠ i, ∫ x, lineIntegrand s Kb (d i) (hd i)
                (fun p => (J p.val).comp (K p)) (fun p => σ i p • A (j p.val)) x) := by
  classical
  have hparam := immersion_parametrizations S T hT j hj.1 hj.2.2.1
  choose L F hL hF using (embedded_differential_exists S j hparam T hT).2
  obtain ⟨B, hB⟩ := (BoundaryOrientations.boundary_orientation S o).1
  obtain ⟨b, ⟨hb, _⟩, _⟩ := (BoundaryOrientations.boundary_orientation S o).2 B hB
  obtain ⟨Cb⟩ := BundleOperations.exists_cotangent B
  choose K hK hKunique using differential_exists B S Subtype.val hB.1
  refine ⟨L, F, B, Cb, b, K, hL, hF, hB, hb, hK, ?_⟩
  exact surface_stokes S T j hT hj o C D L hL F hF B Cb hB b hb K hK U hU hjU A hA

end SmoothManifolds.ClassicalResults


namespace SmoothManifolds.ClassicalResults
open ModelData
  AtlasData MapData
  TangentData TangentBundleData
  DifferentialData CovectorData
  BundleOperationsData ExteriorData
  ExteriorDerivativeData FormPullbackData
  LocalIntegrationData GlobalIntegrationData
  OrientationData BoundaryData
  BoundaryOrientationData MetricVolumeData
  ClassicalIntegralData ClassicalBoundaryData
  ClassicalData EmbeddedData Set MeasureTheory
open scoped Topology BigOperators Matrix

theorem divergence_differential {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (X : d → Euclidean (n+1))
    (hX : LocallyContDiffOn 1 d X) :
    ∃ G : DomainGeometry T d S,
      HasExteriorDerivative C
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p))
        (scalarVolume (fun p => divergenceWithin d (extendVector d X) p.val)
          (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap))) ∧
      pullbackField G.boundary S Subtype.val G.inclusion
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p)) =
        scalarVolume (fun p => X p.val ⬝ᵥ G.normal p) G.area.field := by
  have hX' : LocallyContDiffOn 1 d (fun p => extendVector d X p.val) := by
    simpa only [extendVector_coe] using hX
  simpa only [extendVector_coe] using
    classical_divergence_differential T hT d S hreg C (extendVector d X) hX'


theorem divergence_theorem {n : ℕ} {a : ModelKind}
    (T : SmoothManifold (n+1) .euclidean (Euclidean (n+1)))
    (hT : EmbeddedData.euclideanChart (n+1) ∈ T.smoothStructure.val)
    (d : Set (Euclidean (n+1))) (S : SmoothManifold (n+1) a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (X : d → Euclidean (n+1))
    (hX : LocallyContDiffOn 1 d X)
    (hcomp : IsCompact d ∨ IsCompact (sectionSupport X)) :
    ∃ G : DomainGeometry T d S,
      HasExteriorDerivative C
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p))
        (scalarVolume (fun p => divergenceWithin d (extendVector d X) p.val)
          (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap))) ∧
      pullbackField G.boundary S Subtype.val G.inclusion
        (euclideanFluxForm S (fun p => (G.ambient p).toLinearMap) (fun p => X p)) =
        scalarVolume (fun p => X p.val ⬝ᵥ G.normal p) G.area.field ∧
      Integrable (extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val)) ∧
      ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm G.boundary → ℝ),
        IsIntegral G.orientation I → IsIntegral G.boundaryOrientation Ib →
        ∃ (η : CompactTopForm S) (β : CompactTopForm G.boundary),
          η.field = scalarVolume (fun p => divergenceWithin d (extendVector d X) p.val)
            (euclideanVolumeForm S (fun p => (G.ambient p).toLinearMap)) ∧
          β.field = scalarVolume (fun p => X p.val ⬝ᵥ G.normal p) G.area.field ∧
          I η = ∫ x in d, extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val) x ∧
          (∫ x in d, extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val) x) = Ib β ∧
          ∀ (K : FiberCoordinates G.boundary) {ι : Type}
            (c : ι → ModelChart n .euclidean (intrinsicBoundary S))
            (hc : ∀ i, c i ∈ G.boundary.smoothStructure.val) (ρ : ι → intrinsicBoundary S → ℝ),
            IsLocalization c ρ β →
            (∫ x in d, extendScalar d (fun p => divergenceWithin d (extendVector d X) p.val) x) =
              ∑ᶠ i, ∫ x, surfaceIntegrand
                (fun p => (G.ambient p.val).toLinearMap.comp (G.inclusion p)) K (c i) (hc i)
                (fun p => ρ i p * (X p.val ⬝ᵥ G.normal p)) x := by
  have hX' : LocallyContDiffOn 1 d (fun p => extendVector d X p.val) := by
    simpa only [extendVector_coe] using hX
  have hcomp' : IsCompact d ∨ IsCompact (sectionSupport
      (fun p : d => extendVector d X p.val)) := by
    simpa only [extendVector_coe] using hcomp
  simpa only [extendVector_coe] using
    classical_divergence T hT d S hreg C (extendVector d X) hX' hcomp'


theorem green_theorem {a : ModelKind}
    (T : SmoothManifold 2 .euclidean (Euclidean 2))
    (hT : EmbeddedData.euclideanChart 2 ∈ T.smoothStructure.val)
    (d : Set (Euclidean 2)) (S : SmoothManifold 2 a d)
    (hreg : RegularDomainData.IsRegularDomain T d S) (C : CotangentBundle S)
    (P Q : d → ℝ)
    (hP : LocallyContDiffOn 1 d P) (hQ : LocallyContDiffOn 1 d Q) (hd : IsCompact d) :
    ∃ (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
      (J : (p : d) → TangentSpace S p ≃ₗ[ℝ] Euclidean 2)
      (Kb : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (o : Orientation S) (b : Orientation B),
      IsNaturalBoundary S B ∧
      (∀ p, IsEuclideanDifferential S T Subtype.val p (J p).toLinearMap) ∧
      (∀ p v, IsPositive (o.val p) v ↔
        0 < standardAmbientDet 2 (exteriorPower.map 2 (J p).toLinearMap v)) ∧
      IsInducedOrientation o b ∧
      (∀ p, IsDifferential B S Subtype.val p (Kb p)) ∧
      PlanarBoundaryComponents S B J Kb b ∧
      HasExteriorDerivative C
        (euclideanOneForm S (fun p => (J p).toLinearMap) (fun p => ![P p, Q p]))
        (scalarVolume (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0)
          (euclideanVolumeForm S (fun p => (J p).toLinearMap))) ∧
      Integrable (extendScalar d
        (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0)) ∧
      ∀ (I : CompactTopForm S → ℝ) (Ib : CompactTopForm B → ℝ),
        IsIntegral o I → IsIntegral b Ib →
        ∃ (η : CompactTopForm S) (β : CompactTopForm B),
          η.field = scalarVolume
            (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0)
            (euclideanVolumeForm S (fun p => (J p).toLinearMap)) ∧
          β.field = euclideanOneForm B
            (fun p => (J p.val).toLinearMap.comp (Kb p)) (fun p => ![P p.val, Q p.val]) ∧
          I η = ∫ x in d, extendScalar d
            (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0) x ∧
          (∫ x in d, extendScalar d
            (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0) x) = Ib β ∧
          ∀ (s : SignedCharts B), RepresentsSignedCharts b.val s →
          ∀ (K : FiberCoordinates B) {ι : Type}
            (c : ι → ModelChart 1 .euclidean (intrinsicBoundary S))
            (hc : ∀ i, c i ∈ B.smoothStructure.val) (ρ : ι → intrinsicBoundary S → ℝ),
            IsLocalization c ρ β →
            (∫ x in d, extendScalar d
              (fun p => partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 0 1 - partialWithin d (extendVector d (fun p => ![P p, Q p])) p.val 1 0) x) =
              ∑ᶠ i, ∫ x, lineIntegrand s K (c i) (hc i)
                (fun p => (J p.val).toLinearMap.comp (Kb p))
                (fun p => ρ i p • ![P p.val, Q p.val]) x := by
  have hPQ : LocallyContDiffOn 1 d (fun p => ![P p, Q p]) := by
    apply ClassicalIntegralResults.coefficientwise_local_extensions 1 Subtype.val
    intro i
    fin_cases i
    · simpa [ModelData.LocallyContDiffOn] using hP
    · simpa [ModelData.LocallyContDiffOn] using hQ
  have hA : LocallyContDiffOn 1 d
      (fun p => extendVector d (fun p => ![P p, Q p]) p.val) := by
    simpa only [extendVector_coe] using hPQ
  simpa only [extendVector_coe] using
    classical_green T hT d S hreg C (extendVector d (fun p => ![P p, Q p])) hA hd


end SmoothManifolds.ClassicalResults
