import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedAtlas
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.MultivariableAnalysis.D04.C14.ChartIndependentTangentSpaces

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
noncomputable section

namespace SmoothManifolds.EmbeddedCalculusResults
open ModelData AtlasData TangentData DifferentialData ExteriorData EmbeddedData
  EmbeddedCalculusData Set
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
universe u v

/-- The norm change introduces the expected conjugation of the derivative. -/
theorem parameterExtension_hasFDerivAt {n N : ℕ} (G : E n → E N) (u : E n)
    (hG : DifferentiableAt ℝ G u) :
    HasFDerivAt (parameterExtension G)
      ((piCoordinates N).toContinuousLinearMap.comp
        ((fderiv ℝ G u).comp (piCoordinates n).symm.toContinuousLinearMap))
      (piCoordinates n u) := by
  have h := (piCoordinates N).hasFDerivAt.comp u hG.hasFDerivAt
  have h' := h.comp (piCoordinates n u) (piCoordinates n).symm.hasFDerivAt
  convert h' using 1 <;> ext <;> rfl

/-- Local pointwise bridge to D04's actual chart-independent tangent space. -/
theorem tangent_identification_proof :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.tangent_identificationType := by
  intro n N a M S hj hn T hT p L F hL hF e he hp c u hu hcu heu W G hW huW heq hG V hH
  let A := coordinateDerivationEquiv S p e he hp
  let J : TangentSpace S p →ₗ[ℝ] E N :=
    (piCoordinates N).symm.toLinearMap.comp (F.toLinearMap.comp L)
  have hd : chartDifferential c u = fderiv ℝ G u :=
    D04.EmbeddedChart.differential_extension c hu hW huW heq hG
  have hformula (v : TangentSpace S p) :
      J v = chartDifferential c u ((piCoordinates n).symm (A v)) := by
    have h := embedded_differential_jacobian S (ambientInclusion M) hj T hT p L F hL hF
      e he hp V (parameterExtension G) hH v
    rw [heu, (parameterExtension_hasFDerivAt G u hG).fderiv] at h
    apply (piCoordinates N).injective
    change F (L v) = (piCoordinates N) ((chartDifferential c u)
      ((piCoordinates n).symm (A v)))
    rw [hd]
    exact h
  have hJ : Function.Injective J :=
    (piCoordinates N).symm.injective.comp
      (embedded_tangent_comparison S (ambientInclusion M) hj T hT p L F hL hF).2.1
  have hrange : LinearMap.range J = tangentSpace 2 n M p.val := by
    rw [← hcu, D04.tangentSpace_chart c (by constructor <;> norm_num) hn u hu]
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(piCoordinates n).symm (A v), (hformula v).symm⟩
    · rintro ⟨w, rfl⟩
      refine ⟨A.symm (piCoordinates n w), ?_⟩
      rw [hformula, A.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
      rfl
  let I := (LinearEquiv.ofInjective J hJ).trans (LinearEquiv.ofEq _ _ hrange)
  exact ⟨I, fun _ => rfl⟩

/-- Transport commutes with evaluation, including the empty argument tuple. -/
theorem form_evaluation_proof :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.form_evaluationType.{u,v} := by
  intro V W _ _ _ _ I k ω v
  change evaluate V k ω (fun j => I.symm (I (v j))) = _
  simp only [I.symm_apply_apply]

/-- Transport is an equivalence of forms, not a one-way interpretation. -/
theorem form_bijective_proof :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.form_bijectiveType.{u,v} := by
  intro V W _ _ _ _ _ I k
  have hev := ExteriorAlgebraResults.alternating_interpretation V k
  have hdom := (AlternatingMap.domLCongr ℝ ℝ (Fin k) ℝ I).bijective
  exact hdom.comp hev

/-- Pullback and change of tangent model commute under a commuting square. -/
theorem restriction_transport_proof :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.restriction_transportType.{u,v} := by
  intro V W X Y _ _ _ _ _ _ _ _ I J L K h k ω
  apply AlternatingMap.ext
  intro z
  change evaluate V k (FormPullbackData.fiberPullback k L ω)
    (fun j => I.symm (z j)) = evaluate W k ω (fun j => J.symm (K (z j)))
  rw [FormPullbackResults.evaluate_fiberPullback]
  congr 1
  funext j
  apply J.injective
  rw [J.apply_symm_apply, h, I.apply_symm_apply]

/-- Coefficients of an exterior dual basis are alternating evaluations. -/
theorem basis_coefficient_evaluation {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (k : ℕ) (ω : Fiber V k) (I : Index n k) :
    (b.dualBasis.exteriorPower k).repr ω I =
      evaluate V k ω (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm I j)) := by
  change _ = exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual ℝ V k ω) _
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  change _ = exteriorPower.pairingDual ℝ V k ω
    (exteriorPower.ιMulti ℝ k (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm I j)))
  have hI : b.exteriorPower k I =
      exteriorPower.ιMulti ℝ k (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm I j)) :=
    exteriorPower.basis_apply ℝ k b I
  rw [← hI]
  conv_rhs => rw [← (b.dualBasis.exteriorPower k).sum_repr ω]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    exteriorPower.pairingDual_apply_dualBasis_exteriorPower]
  simp only [Module.Basis.dualBasis_apply_self, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The manuscript's abstract pullback coefficients, in its original fibers. -/
theorem coefficient_evaluation_proof :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.coefficient_evaluationType.{u} := by
  intro n a M _ S C k c hc ω p I
  let b := (Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm
  change (b.dualBasis.exteriorPower k).repr (ω p.val) I = _
  have hh := @basis_coefficient_evaluation (TangentSpace S p.val) inferInstance
    inferInstance n b k (ω p.val) I
  simpa only [b, Module.Basis.map_apply, Pi.basisFun_apply, CovectorData.coordinateVector] using hh

/-- A pointwise tangent isomorphism preserves the exact closed support. -/
theorem support_identification_proof :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.support_identificationType := by
  intro n N a M S I k ω
  change closure {p | transportCovector (I p) k (ω p) ≠ 0} =
    closure {p | ω p ≠ 0}
  congr 1
  ext p
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective (I p).toLinearMap (I p).injective
  have hev : Function.Injective (evaluate (TangentSpace S p) k) :=
    (ExteriorAlgebraResults.alternating_interpretation (TangentSpace S p) k).1
  have hz : transportCovector (V := TangentSpace S p) (I p) k (ω p) = 0 ↔ ω p = 0 := by
    constructor
    · intro h
      apply hev
      apply AlternatingMap.ext
      intro v
      have hh := congrArg (fun A => A (fun j => I p (v j))) h
      simpa only [transportCovector, AlternatingMap.compLinearMap_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, zero_apply,
        map_zero] using hh
    · intro h
      rw [h]
      simp [transportCovector]
  exact not_congr hz

/-- Public names use the real imported upstream proofs, without frozen premises. -/
theorem tangent_identification :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.tangent_identificationType :=
  tangent_identification_proof

theorem form_evaluation :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.form_evaluationType.{u,v} :=
  form_evaluation_proof

theorem form_bijective :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.form_bijectiveType.{u,v} :=
  form_bijective_proof

theorem restriction_transport :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.restriction_transportType.{u,v} :=
  restriction_transport_proof

theorem coefficient_evaluation :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.coefficient_evaluationType.{u} :=
  coefficient_evaluation_proof

theorem support_identification :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.support_identificationType :=
  support_identification_proof

/-- Coordinates from an arbitrary tangent-bundle realization give the same
actual inclusion Jacobian and hence the literal D04 chart tangent map. -/
theorem chart_pullback :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.chart_pullbackType := by
  intro n N a M S hj T hT C e he c u hu p hp heu W G hW huW heq hG V hH L F hL hF I hI
  let A := C.tangent.fiberCoordinates.equiv e he p hp
  have hA : A = coordinateDerivationEquiv S p e he hp :=
    TangentBundle.chartCoordinates_unique
      (C.tangent.fiberCoordinates.isCoordinates e he p hp)
      (coordinateDerivationEquiv_isChartCoordinates S p e he hp)
  have hd : chartDifferential c u = fderiv ℝ G u :=
    D04.EmbeddedChart.differential_extension c hu hW huW heq hG
  have hformula (v : TangentSpace S p) :
      (I p v).val = chartDifferential c u ((piCoordinates n).symm (A v)) := by
    rw [hI]
    have h := embedded_differential_jacobian S (ambientInclusion M) hj T hT p L F hL hF
      e he hp V (parameterExtension G) hH v
    rw [heu, (parameterExtension_hasFDerivAt G u hG).fderiv] at h
    apply (piCoordinates N).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, hd, hA]
    exact h
  have hcoord (w : E n) :
      I p (A.symm (piCoordinates n w)) =
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap c u hu w := by
    apply Subtype.ext
    change (I p (A.symm (piCoordinates n w))).val = chartDifferential c u w
    rw [hformula, A.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨hcoord, ?_⟩
  intro k ω
  have heval (w : Fin k → E n) :
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c
        (transportField S I k ω) u w =
      evaluate (TangentSpace S p) k (ω p)
        (fun j => A.symm (piCoordinates n (w j))) := by
    simp only [Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback, dif_pos hu,
      AlternatingMap.compLinearMap_apply]
    change evaluate (TangentSpace S p) k (ω p)
      (fun j => (I p).symm
        (Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap c u hu (w j))) = _
    simp only [← hcoord, LinearEquiv.symm_apply_apply]
  refine ⟨heval, ?_⟩
  intro J
  change Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback c
    (transportField S I k ω) u
      (fun j => standardBasis n (Set.powersetCard.ofFinEmbEquiv.symm J j)) = _
  rw [heval, coefficient_evaluation]
  congr 1
  funext j
  congr 1
  ext l
  simp [piCoordinates, standardBasis, EuclideanSpace.basisFun_apply, Pi.single_apply]

end SmoothManifolds.EmbeddedCalculusResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData TangentData EmbeddedData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Set
open scoped ContDiff

abbrev lowerChart := @EmbeddedAtlasData.lowerChart
abbrev IsRawEmbeddedChart := @EmbeddedAtlasData.IsRawEmbeddedChart
abbrev IsInducedSmoothStructure := @EmbeddedAtlasData.IsInducedSmoothStructure

@[simp] theorem lowerChart_differential {r s : ℕ∞ω} {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart r n N M) (hsr : s ≤ r) (u : E n) :
    chartDifferential (lowerChart c hsr) u = chartDifferential c u := rfl

theorem induced_fullRank :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_fullRankType := by
  intro n N a M S hS p e he hp
  have he' : IsRawEmbeddedChart e := by
    rw [hS] at he
    exact he
  obtain ⟨V, H, hV, hpV, hH, heq, hinj⟩ := he' p hp
  refine ⟨V, H, ⟨hV, hpV, hH, heq⟩, ?_⟩
  rw [LinearMap.finrank_range_of_inj hinj]
  simp [Euclidean, ModelData.Euclidean]

theorem lower_manifold {r s : ℕ∞ω} {n N : ℕ} {M : Set (E N)}
    (hM : IsEmbeddedManifold r n M) (hsr : s ≤ r) (hs : ManifoldRegularity s) :
    IsEmbeddedManifold s n M := by
  refine ⟨hs, hM.2.1, ?_⟩
  intro p hp
  obtain ⟨c, u, hu, hcu⟩ := hM.2.2 p hp
  exact ⟨lowerChart c hsr, u, hu, hcu⟩

theorem smooth_c2_tangents :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.smooth_c2_tangentsType := by
  intro n N M hM
  refine ⟨lower_manifold hM (by simp) (by constructor <;> norm_num), ?_⟩
  intro p hp
  obtain ⟨c, u, hu, hcu⟩ := hM.2.2 p hp
  have hs := D04.tangentSpace_chart c hM.1 hM.2.1 u hu.1
  have ht := D04.tangentSpace_chart (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞))
      (by constructor <;> norm_num) hM.2.1 u hu.1
  exact (hcu ▸ hs).trans (hcu ▸ ht).symm

theorem mixed_transition :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.mixed_transitionType := by
  intro n N M c d hn d₂
  have hr : ManifoldRegularity 2 := by constructor <;> norm_num
  obtain ⟨hc, hext⟩ := D04.chart_transition_regular c d₂ hr hn
  refine ⟨hc, hext, ?_⟩
  intro u hu
  obtain ⟨A, hA, hB⟩ := D04.chart_transition_derivatives c d₂ hr hn u hu
  refine ⟨A, hA, hB, ?_⟩
  apply (D04.EmbeddedChart.overlap_uniqueDiff c d₂ u hu).eq (f := c.toFun)
  · exact (D04.EmbeddedChart.hasDifferential c hr hu.1).mono inter_subset_left
  · exact ((D04.EmbeddedChart.hasDifferential d₂ hr
      (D04.EmbeddedChart.transition_mem c d₂ hu).1).comp u hA
      (fun v hv => (D04.EmbeddedChart.transition_mem c d₂ hv).1)).congr'
      (fun v hv => (d₂.right_inv _ ⟨(c.map_source hv.1).1, hv.2⟩).symm) hu

theorem tangent_identification_unique :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.tangent_identification_uniqueType := by
  intro n N a M S p I J h
  exact LinearEquiv.ext (fun v => Subtype.ext (h v))

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData TangentData DifferentialData EmbeddedData EmbeddedCalculusData
  EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Set Filter
open scoped ContDiff Topology

/-- Smoothness survives the explicit Pi/L2 conversion on both sides. -/
theorem parameterExtension_contDiffOn {n N : ℕ} {r : ℕ∞ω}
    {G : E n → E N} {W : Set (E n)} (hG : ContDiffOn ℝ r G W) :
    ContDiffOn ℝ r (parameterExtension G) ((piCoordinates n).symm ⁻¹' W) := by
  exact (piCoordinates N).contDiff.comp_contDiffOn
    (hG.comp (piCoordinates n).symm.contDiff.contDiffOn (fun _ hx => hx))

/-- A genuine local smooth retraction onto the parametrization. Its ambient
range need not lie in M across a true face; only its restriction to M is
identity. Its derivative nevertheless lands in the literal D04 tangent. -/
theorem local_ambient_retraction {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart ∞ n N M) (hn : n ≤ N) (u : E n) (hu : u ∈ c.source) :
    ∃ (O : Set (E N)) (R : E N → E N),
      IsOpen O ∧ c.toFun u ∈ O ∧ ContDiffOn ℝ ∞ R O ∧
      EqOn R id (M ∩ O) ∧ DifferentiableAt ℝ R (c.toFun u) ∧
      ∀ v, fderiv ℝ R (c.toFun u) v ∈ tangentSpace 2 n M (c.toFun u) := by
  have hr : ManifoldRegularity ∞ := by constructor <;> simp
  obtain ⟨W, G, hW, huW, heG, hG, _⟩ := c.regular u hu
  obtain ⟨U, J, hU, hpU, hJ, heJ⟩ := D04.chart_inverse_extension c hr hn u hu
  have hJu : J (c.toFun u) = u :=
    (heJ ⟨c.map_source hu, hpU⟩).trans (c.left_inv u hu)
  let O := c.ambient ∩ (U ∩ J ⁻¹' W)
  have hO : IsOpen O :=
    c.ambient_open.inter (hJ.continuousOn.isOpen_inter_preimage hU hW)
  have hpO : c.toFun u ∈ O := ⟨(c.map_source hu).2, hpU, by change J (c.toFun u) ∈ W; rwa [hJu]⟩
  have hR : ContDiffOn ℝ ∞ (G ∘ J) O :=
    hG.comp (hJ.mono (fun _ hx => hx.2.1)) (fun _ hx => hx.2.2)
  have hdG := (hG.contDiffAt (hW.mem_nhds huW)).differentiableAt (by simp)
  have hdJ := (hJ.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hdG' : HasFDerivAt G (fderiv ℝ G u) (J (c.toFun u)) := by
    simpa only [hJu] using hdG.hasFDerivAt
  have hDR := hdG'.comp (c.toFun u) hdJ.hasFDerivAt
  refine ⟨O, G ∘ J, hO, hpO, hR, ?_, hDR.differentiableAt, ?_⟩
  · intro x hx
    change G (J x) = x
    have hxma : x ∈ M ∩ c.ambient := ⟨hx.1, hx.2.1⟩
    have hJe : J x = c.invFun x := heJ ⟨hxma, hx.2.2.1⟩
    have hin : c.invFun x ∈ W := by
      have hw : J x ∈ W := hx.2.2.2
      rwa [hJe] at hw
    rw [hJe, heG ⟨c.map_target hxma, hin⟩, c.right_inv x hxma]
  · intro v
    rw [hDR.fderiv]
    have hd : chartDifferential c u = fderiv ℝ G u :=
      D04.EmbeddedChart.differential_extension c hu hW huW heG hdG
    have ht := D04.tangentSpace_chart
      (EmbeddedAtlasData.lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞))
      (by constructor <;> norm_num) hn u hu
    change tangentSpace 2 n M (c.toFun u) =
      LinearMap.range (chartDifferential c u).toLinearMap at ht
    rw [ht, hd]
    exact ⟨fderiv ℝ J (c.toFun u) v, rfl⟩

/-- The image of the actual inclusion differential is the actual D04 tangent,
without a supplied matching intrinsic/D04 chart. -/
theorem inclusion_range {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hM : IsEmbeddedManifold ∞ n M) (S : SmoothManifold n a M)
    (hj : HasFullRankParametrizations S (ambientInclusion M))
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : euclideanChart N ∈ T.smoothStructure.val) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (ambientInclusion M p))
    (F : TangentSpace T (ambientInclusion M p) ≃ₗ[ℝ] Euclidean N)
    (hL : IsDifferential S T (ambientInclusion M) p L)
    (hF : IsChartCoordinates T (ambientInclusion M p) (euclideanChart N) F) :
    LinearMap.range ((piCoordinates N).symm.toLinearMap.comp (F.toLinearMap.comp L)) =
      tangentSpace 2 n M p.val := by
  let A : TangentSpace S p →ₗ[ℝ] E N :=
    (piCoordinates N).symm.toLinearMap.comp (F.toLinearMap.comp L)
  obtain ⟨c, u, hu, hcu⟩ := hM.2.2 p.val p.property
  obtain ⟨O, R, hO, hpO, hR, heR, hdR, hDR⟩ :=
    local_ambient_retraction c hM.2.1 u hu.1
  rw [hcu] at hpO hdR hDR
  have heRbase : (fun y : M => parameterExtension R (ambientInclusion M y)) =ᶠ[𝓝 p]
      ambientInclusion M := by
    have hcont : Continuous (fun y : M => y.val) := continuous_subtype_val
    filter_upwards [hcont.continuousAt.eventually (hO.mem_nhds hpO)] with y hy
    change piCoordinates N (R y.val) = piCoordinates N y.val
    rw [heR ⟨y.property, hy⟩]
    rfl
  have hle : LinearMap.range A ≤ tangentSpace 2 n M p.val := by
    rintro z ⟨v, rfl⟩
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨V, H, hH, _⟩ := hj p e he hp
    have hH0 : H (e p).val = ambientInclusion M p := hH.2.2.2.eq_of_nhds
    let U := (piCoordinates N).symm ⁻¹' O
    have hU : IsOpen U := hO.preimage (piCoordinates N).symm.continuous
    have hpU : ambientInclusion M p ∈ U := by
      simpa [U, ambientInclusion] using hpO
    let V' := V ∩ H ⁻¹' U
    have hV' : IsOpen V' := hH.2.2.1.continuousOn.isOpen_inter_preimage hH.1 hU
    have hpV' : (e p).val ∈ V' := ⟨hH.2.1, by change H (e p).val ∈ U; rwa [hH0]⟩
    have hKH : IsParametrizationAt (ambientInclusion M) e p V'
        (parameterExtension R ∘ H) := by
      refine ⟨hV', hpV', ?_, ?_⟩
      · exact (parameterExtension_contDiffOn hR).comp
          (hH.2.2.1.mono inter_subset_left) (fun _ hx => hx.2)
      · exact (hH.2.2.2.fun_comp (parameterExtension R)).trans heRbase
    have hJ := embedded_differential_jacobian S (ambientInclusion M) hj T hT p L F
      hL hF e he hp V H hH v
    have hK := embedded_differential_jacobian S (ambientInclusion M) hj T hT p L F
      hL hF e he hp V' (parameterExtension R ∘ H) hKH v
    have hdH := (hH.2.2.1.contDiffAt (hH.1.mem_nhds hH.2.1)).differentiableAt (by simp)
    have hdRP := EmbeddedCalculusResults.parameterExtension_hasFDerivAt R p.val hdR
    have hdRP' : HasFDerivAt (parameterExtension R)
        ((piCoordinates N).toContinuousLinearMap.comp
          ((fderiv ℝ R p.val).comp (piCoordinates N).symm.toContinuousLinearMap))
        (H (e p).val) := by
      simpa only [hH0, ambientInclusion] using hdRP
    rw [(hdRP'.comp (e p).val hdH.hasFDerivAt).fderiv] at hK
    have hfix : fderiv ℝ R p.val (A v) = A v := by
      apply (piCoordinates N).injective
      change piCoordinates N (fderiv ℝ R p.val
        ((piCoordinates N).symm (F (L v)))) = F (L v)
      exact (congrArg
        (fun z => piCoordinates N (fderiv ℝ R p.val ((piCoordinates N).symm z))) hJ).trans hK.symm
    change A v ∈ tangentSpace 2 n M p.val
    rw [← hfix]
    exact hDR (A v)
  have hinj : Function.Injective A :=
    (piCoordinates N).symm.injective.comp
      (embedded_tangent_comparison S (ambientInclusion M) hj T hT p L F hL hF).2.1
  apply Submodule.eq_of_le_of_finrank_eq hle
  letI := (tangent_dimension S p).1
  rw [LinearMap.finrank_range_of_inj hinj]
  have hdim := D04.tangentSpace_finrank (smooth_c2_tangents hM).1 p.val p.property
  rw [hdim]
  exact (tangent_dimension S p).2

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData TangentData DifferentialData EmbeddedData EmbeddedCalculusData
  EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Set Filter
open scoped ContDiff Topology

abbrev IsInclusionIdentification := @EmbeddedAtlasData.IsInclusionIdentification
abbrev MatchesEmbeddedChart := @EmbeddedAtlasData.MatchesEmbeddedChart

theorem induced_tangent_identification :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_tangent_identificationType := by
  intro n N a M hM S hS
  have hj := induced_fullRank S hS
  obtain ⟨T, hT⟩ := standardEuclidean_exists N
  have hex := (embedded_differential_exists S (ambientInclusion M) hj T hT).2
  have hpI (p : M) : ∃ I : TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
      ∀ (T' : SmoothManifold N .euclidean (Euclidean N))
      (hT' : euclideanChart N ∈ T'.smoothStructure.val)
      (L' : TangentSpace S p →ₗ[ℝ] TangentSpace T' (ambientInclusion M p))
      (F' : TangentSpace T' (ambientInclusion M p) ≃ₗ[ℝ] Euclidean N),
      IsDifferential S T' (ambientInclusion M) p L' →
      IsChartCoordinates T' (ambientInclusion M p) (euclideanChart N) F' →
      ∀ v, (I v).val = (piCoordinates N).symm (F' (L' v)) := by
    obtain ⟨L, F, hL, hF⟩ := hex p
    let A := (piCoordinates N).symm.toLinearMap.comp (F.toLinearMap.comp L)
    have hinj : Function.Injective A :=
      (piCoordinates N).symm.injective.comp
        (embedded_tangent_comparison S (ambientInclusion M) hj T hT p L F hL hF).2.1
    have hrange := inclusion_range hM S hj T hT p L F hL hF
    let I := (LinearEquiv.ofInjective A hinj).trans (LinearEquiv.ofEq _ _ hrange)
    refine ⟨I, ?_⟩
    intro T' hT' L' F' hL' hF' v
    change (piCoordinates N).symm (F (L v)) = (piCoordinates N).symm (F' (L' v))
    congr 1
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨V, H, hH, _⟩ := hj p e he hp
    exact (embedded_differential_jacobian S (ambientInclusion M) hj T hT p L F hL hF
      e he hp V H hH v).trans
      (embedded_differential_jacobian S (ambientInclusion M) hj T' hT' p L' F' hL' hF'
        e he hp V H hH v).symm
  choose I hI using hpI
  refine ⟨I, ?_, ?_⟩
  · intro T' hT' p L' F' hL' hF' v
    exact hI p T' hT' L' F' hL' hF' v
  · intro J hJ
    funext p
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    obtain ⟨L, F, hL, hF⟩ := hex p
    exact (hJ T hT p L F hL hF v).trans (hI p T hT L F hL hF v).symm

/-- Raw matching implies the actual smooth extension of the inverse chart.
This supplies rather than assumes the local extension used by the original
pointwise comparison proof. -/
theorem matching_parametrization {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (c : EmbeddedChart ∞ n N M)
    (hm : MatchesEmbeddedChart e c) (p : M) (hp : p ∈ e.source)
    (u : E n) (hu : u ∈ c.source) (hcu : c.toFun u = p.val) :
    (e p).val = piCoordinates n u ∧
    ∃ (W : Set (E n)) (G : E n → E N), IsOpen W ∧ u ∈ W ∧
      EqOn G c.toFun (c.source ∩ W) ∧ DifferentiableAt ℝ G u ∧
      IsParametrizationAt (ambientInclusion M) e p
        ((piCoordinates n).symm ⁻¹' W) (parameterExtension G) := by
  have hep : (e p).val = piCoordinates n u := by
    rw [(hm p hp).2, ← hcu, c.left_inv u hu]
  obtain ⟨W, G, hW, huW, heG, hG, _⟩ := c.regular u hu
  refine ⟨hep, W, G, hW, huW, heG,
    (hG.contDiffAt (hW.mem_nhds huW)).differentiableAt (by simp), ?_⟩
  have hV : IsOpen ((piCoordinates n).symm ⁻¹' W) :=
    hW.preimage (piCoordinates n).symm.continuous
  have hpV : (e p).val ∈ (piCoordinates n).symm ⁻¹' W := by
    simpa only [hep, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using huW
  refine ⟨hV, hpV, parameterExtension_contDiffOn hG, ?_⟩
  have hcont : ContinuousAt (fun y : M => (e y).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  filter_upwards [e.open_source.mem_nhds hp, hcont.eventually (hV.mem_nhds hpV)] with y hy hyW
  change piCoordinates N (G ((piCoordinates n).symm (e y).val)) = piCoordinates N y.val
  rw [(hm y hy).2, ContinuousLinearEquiv.symm_apply_apply]
  have hyma : y.val ∈ M ∩ c.ambient := ⟨y.property, (hm y hy).1⟩
  have hyinv : c.invFun y.val ∈ W := by
    simpa only [mem_preimage, (hm y hy).2, ContinuousLinearEquiv.symm_apply_apply] using hyW
  rw [heG ⟨c.map_target hyma, hyinv⟩, c.right_inv y.val hyma]

theorem matching_chart_pullback :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.matching_chart_pullbackType := by
  intro n N a M S hS I hI C e he c hm u hu p hp c₂
  have hj := induced_fullRank S hS
  obtain ⟨hep, W, G, hW, huW, heG, hdG, hpar⟩ :=
    matching_parametrization e c hm p hp u hu rfl
  obtain ⟨T, hT⟩ := standardEuclidean_exists N
  obtain ⟨L, F, hL, hF⟩ := (embedded_differential_exists S (ambientInclusion M) hj T hT).2 p
  exact EmbeddedCalculusResults.chart_pullback S hj T hT C e he c₂ u hu hp hep
    W G hW huW heG hdG ((piCoordinates n).symm ⁻¹' W) hpar L F hL hF I
    (hI T hT p L F hL hF)

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Set Filter
open scoped ContDiff Topology
open private D04.inverse_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction

/-- Convert an intrinsic extension back to the fixed L2 coordinates. -/
def l2ParameterExtension {n N : ℕ} (H : ModelData.Euclidean n → ModelData.Euclidean N) :
    E n → E N := fun u => (piCoordinates N).symm (H (piCoordinates n u))

theorem l2ParameterExtension_contDiffOn {n N : ℕ} {r : ℕ∞ω}
    {H : ModelData.Euclidean n → ModelData.Euclidean N}
    {V : Set (ModelData.Euclidean n)} (hH : ContDiffOn ℝ r H V) :
    ContDiffOn ℝ r (l2ParameterExtension H) (piCoordinates n ⁻¹' V) :=
  (piCoordinates N).symm.contDiff.comp_contDiffOn
    (hH.comp (piCoordinates n).contDiff.contDiffOn (fun _ hx => hx))

/-- The coordinates of a raw full-rank embedded chart have a smooth ambient
extension locally. The inverse theorem is applied before restricting to the
half-space, so it includes face points and dimension zero. -/
theorem raw_chart_inverse {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (he : IsRawEmbeddedChart e) (p : M) (hp : p ∈ e.source) :
    LocalCoordinateExtension (⊤ : ℕ∞) (ambientInclusion M) (fun y => (e y).val) p := by
  obtain ⟨V, H, hV, hpV, hH, heH, hinj⟩ := he p hp
  let u := (piCoordinates n).symm (e p).val
  let H₂ := l2ParameterExtension H
  let V₂ := piCoordinates n ⁻¹' V
  have huV : u ∈ V₂ := by
    change piCoordinates n ((piCoordinates n).symm (e p).val) ∈ V
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hV₂ : IsOpen V₂ := hV.preimage (piCoordinates n).continuous
  have hH₂ : ContDiffOn ℝ ∞ H₂ V₂ := l2ParameterExtension_contDiffOn hH
  have hdH := (hH.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hdH' : HasFDerivAt H (fderiv ℝ H (e p).val) (piCoordinates n u) := by
    simpa only [u, ContinuousLinearEquiv.apply_symm_apply] using hdH.hasFDerivAt
  have hdH₂ : HasFDerivAt H₂
      ((piCoordinates N).symm.toContinuousLinearMap.comp
        ((fderiv ℝ H (e p).val).comp (piCoordinates n).toContinuousLinearMap)) u :=
    (piCoordinates N).symm.hasFDerivAt.comp u
      (hdH'.comp u (piCoordinates n).hasFDerivAt)
  have hinj₂ : Function.Injective (fderiv ℝ H₂ u) := by
    rw [hdH₂.fderiv]
    exact (piCoordinates N).symm.injective.comp (hinj.comp (piCoordinates n).injective)
  obtain ⟨s, B, hB⟩ := D04.independent_coordinate_projection (fderiv ℝ H₂ u) hinj₂
  let P := D04.coordinateProjection s
  have hPH : ContDiffOn ℝ ∞ (P ∘ H₂) V₂ := P.contDiff.comp_contDiffOn hH₂
  have hdPH := P.hasFDerivAt.comp u hdH₂
  have hBP : B.toContinuousLinearMap = fderiv ℝ (P ∘ H₂) u := by
    rw [hB, hdPH.fderiv, hdH₂.fderiv]
  obtain ⟨X, Y, q, hInv, hq⟩ := D04.inverse_neighborhood V₂ (P ∘ H₂) u B
    (by simp) hV₂ hPH huV hBP
  obtain ⟨hX, hY, huX, hPuY, hXV, _, _, hleft, _⟩ := hInv
  let K := P.comp (piCoordinates N).symm.toContinuousLinearMap
  let U := K ⁻¹' Y
  have hU : IsOpen U := hY.preimage K.continuous
  have hH0 : H₂ u = p.val := by
    change (piCoordinates N).symm (H (piCoordinates n u)) = p.val
    rw [show piCoordinates n u = (e p).val from (piCoordinates n).apply_symm_apply _,
      heH.eq_of_nhds]
    exact (piCoordinates N).symm_apply_apply p.val
  have hpU : ambientInclusion M p ∈ U := by
    change P ((piCoordinates N).symm (piCoordinates N p.val)) ∈ Y
    rw [ContinuousLinearEquiv.symm_apply_apply, ← hH0]
    exact hPuY
  refine ⟨U, hU, hpU, fun z => piCoordinates n (q (K z)),
    (piCoordinates n).contDiff.comp_contDiffOn
      (hq.comp K.contDiff.contDiffOn (fun _ hx => hx)), ?_⟩
  have hcont : ContinuousAt (fun y : M => (piCoordinates n).symm (e y).val) p :=
    (piCoordinates n).symm.continuousAt.comp
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp))
  have hcoord : (piCoordinates n).symm (e p).val ∈ X := huX
  filter_upwards [hcont.eventually (hX.mem_nhds hcoord), heH] with y hy hHy
  have hval : H₂ ((piCoordinates n).symm (e y).val) = y.val := by
    change (piCoordinates N).symm (H (piCoordinates n ((piCoordinates n).symm (e y).val))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, hHy]
    exact (piCoordinates N).symm_apply_apply y.val
  have hqi := hleft hy
  dsimp only [Function.comp_apply] at hqi
  rw [hval] at hqi
  change piCoordinates n (q (P ((piCoordinates N).symm (piCoordinates N y.val)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, hqi, ContinuousLinearEquiv.apply_symm_apply]

/-- Raw embedded coordinates of either model have smooth transitions. -/
theorem raw_chart_transition {n N : ℕ} {a b : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (d : ModelChart n b M)
    (he : IsRawEmbeddedChart e) (hd : IsRawEmbeddedChart d) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) e d id p := by
  obtain ⟨V, H, hV, hpV, hH, heH, _⟩ := he p hp
  exact (raw_chart_inverse d hd p hpd).comp ⟨V, hV, hpV, H, hH, heH⟩

/-- Both uniform model choices induce the same smooth structure on the
common base, expressed as smoothness of the identity in both directions. -/
theorem induced_model_equivalence {n N : ℕ} {a b : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (T : SmoothManifold n b M)
    (hS : IsInducedSmoothStructure S) (hT : IsInducedSmoothStructure T) :
    IsSmoothMap S T id ∧ IsSmoothMap T S id := by
  have hmap {a b : ModelKind} (S : SmoothManifold n a M) (T : SmoothManifold n b M)
      (hS : IsInducedSmoothStructure S) (hT : IsInducedSmoothStructure T) :
      IsSmoothMap S T id := by
    intro p
    refine ⟨continuousAt_id, ?_⟩
    intro e he d hd hp hpd
    rw [hS] at he
    rw [hT] at hd
    exact raw_chart_transition e d he hd p hp hpd
  exact ⟨hmap S T hS hT, hmap T S hT hS⟩

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData MapData TangentData DifferentialData EmbeddedData
  EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Set Filter
open scoped Topology

/-- Construct the unique induced maximal atlas once raw embedded charts cover
the base. Only chart extension and rank data enter this construction. -/
theorem induced_structure_of_raw_cover {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hcover : IsAtlas {e : ModelChart n a M | IsRawEmbeddedChart e}) :
    ∃ S : SmoothManifold n a M, IsInducedSmoothStructure S := by
  let A : Set (ModelChart n a M) := {e | IsRawEmbeddedChart e}
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A := by
    refine ⟨hcover, ?_⟩
    intro e he d hd
    exact contDiffCompatible_of_germs
      (fun p hp hpd => raw_chart_transition e d he hd p hp hpd)
      (fun p hp hpe => raw_chart_transition d e hd he p hp hpe)
  let S : SmoothManifold n a M :=
    ⟨⟨inferInstance, inferInstance, A, hcover⟩,
      ⟨maximalExtension (⊤ : ℕ∞) A, maximalExtension_isMaximal hA⟩⟩
  have hAS : A ⊆ S.smoothStructure.val := subset_maximalExtension hA
  obtain ⟨T, hT⟩ := standardEuclidean_exists N
  have hs : IsSmoothMap S T (ambientInclusion M) := by
    intro p
    obtain ⟨e, he, hp⟩ := hcover p
    obtain ⟨V, H, hV, hpV, hH, heH, _⟩ := he p hp
    have hcont : ContinuousAt (ambientInclusion M) p :=
      (piCoordinates N).continuousAt.comp continuous_subtype_val.continuousAt
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      S.smoothStructure.property.1 T.smoothStructure.property.1 _ p).mpr
    exact ⟨hcont, e, hAS he, euclideanChart N, hT, hp, mem_univ _,
      V, hV, hpV, H, hH, heH⟩
  have hSraw : S.smoothStructure.val ⊆ A := by
    intro e he p hp
    obtain ⟨L, hL, _⟩ := differential_exists S T (ambientInclusion M) hs p
    let F := coordinateDerivationEquiv T (ambientInclusion M p) (euclideanChart N) hT (mem_univ _)
    have hF : IsChartCoordinates T (ambientInclusion M p) (euclideanChart N) F :=
      coordinateDerivationEquiv_isChartCoordinates T _ _ hT (mem_univ _)
    obtain ⟨d, hd, hpd⟩ := hcover p
    obtain ⟨W, G, hW, hpW, hG, heG, hinjG⟩ := hd p hpd
    let D := coordinateDerivationEquiv S p d (hAS hd) hpd
    have hD := coordinateDerivationEquiv_isChartCoordinates S p d (hAS hd) hpd
    have hdform := differential_jacobian S T (ambientInclusion M) hs p L hL
      d (euclideanChart N) (hAS hd) hT hpd (mem_univ _) D F hD hF W G hW hpW hG heG
    have hJ : Function.Injective (F.toLinearMap.comp L) := by
      intro v w hvw
      apply D.injective
      apply hinjG
      exact (hdform v).symm.trans (hvw.trans (hdform w))
    obtain ⟨V, hV, hpV, H, hH, heH⟩ :=
      (hs p).2 e he (euclideanChart N) hT hp (mem_univ _)
    let C := coordinateDerivationEquiv S p e he hp
    have hC := coordinateDerivationEquiv_isChartCoordinates S p e he hp
    have heform := differential_jacobian S T (ambientInclusion M) hs p L hL
      e (euclideanChart N) he hT hp (mem_univ _) C F hC hF V H hV hpV hH heH
    refine ⟨V, H, hV, hpV, hH, heH, ?_⟩
    intro z w hzw
    have haux : (F.toLinearMap.comp L) (C.symm z) = (F.toLinearMap.comp L) (C.symm w) := by
      change F (L (C.symm z)) = F (L (C.symm w))
      rw [heform, heform, C.apply_symm_apply, C.apply_symm_apply]
      exact hzw
    have hv := congrArg C (hJ haux)
    simpa only [C.apply_symm_apply] using hv
  refine ⟨S, Set.Subset.antisymm hSraw ?_⟩
  intro e he
  change ∀ d ∈ A, ContDiffCompatible (⊤ : ℕ∞) e d
  intro d hd
  exact contDiffCompatible_of_germs
    (fun p hp hpd => raw_chart_transition e d he hd p hp hpd)
    (fun p hp hpe => raw_chart_transition d e hd he p hp hpe)

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData MapData EmbeddedData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Set Filter
open scoped ContDiff Topology

/-- An open Euclidean embedded parametrization is an actual intrinsic chart
with the subspace topology. No manifold or comparison certificate is used. -/
theorem euclidean_chart_of_embedded {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart ∞ n N M) (hc : c.half = false) (p₀ : M) :
    ∃ e : ModelChart n .euclidean M,
      e.source = {p : M | p.val ∈ c.ambient} ∧
      IsRawEmbeddedChart e ∧ MatchesEmbeddedChart e c := by
  classical
  have hsource : IsOpen c.source := by
    obtain ⟨W, hW, he⟩ := c.source_open
    simpa [he, Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, hc] using hW
  let f : M → ModelSpace n .euclidean :=
    fun p => ⟨piCoordinates n (c.invFun p.val), mem_univ _⟩
  let g : ModelSpace n .euclidean → M := fun z =>
    if hz : (piCoordinates n).symm z.val ∈ c.source then
      ⟨c.toFun ((piCoordinates n).symm z.val), (c.map_source hz).1⟩ else p₀
  let e : ModelChart n .euclidean M := {
    toFun := f
    invFun := g
    source := {p : M | p.val ∈ c.ambient}
    target := {z | (piCoordinates n).symm z.val ∈ c.source}
    map_source' := by
      intro p hp
      change (piCoordinates n).symm (piCoordinates n (c.invFun p.val)) ∈ c.source
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact c.map_target ⟨p.property, hp⟩
    map_target' := by
      intro z hz
      change (piCoordinates n).symm z.val ∈ c.source at hz
      dsimp [g]
      rw [dif_pos hz]
      exact (c.map_source hz).2
    left_inv' := by
      intro p hp
      have hin := c.map_target ⟨p.property, hp⟩
      change g (f p) = p
      dsimp [f, g]
      simp only [ContinuousLinearEquiv.symm_apply_apply, dif_pos hin]
      exact Subtype.ext (c.right_inv p.val ⟨p.property, hp⟩)
    right_inv' := by
      intro z hz
      change (piCoordinates n).symm z.val ∈ c.source at hz
      change f (g z) = z
      dsimp [f, g]
      rw [dif_pos hz]
      apply Subtype.ext
      rw [c.left_inv _ hz, ContinuousLinearEquiv.apply_symm_apply]
    open_source := c.ambient_open.preimage continuous_subtype_val
    open_target := hsource.preimage ((piCoordinates n).symm.continuous.comp continuous_subtype_val)
    continuousOn_toFun := by
      apply continuousOn_iff_continuous_restrict.mpr
      apply Continuous.subtype_mk
      exact (piCoordinates n).continuous.comp
        (c.continuous_invFun.comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val)
          (fun z => ⟨z.val.property, z.property⟩))
    continuousOn_invFun := by
      apply continuousOn_iff_continuous_restrict.mpr
      have hgcont : Continuous (fun z : {z : ModelSpace n .euclidean |
          (piCoordinates n).symm z.val ∈ c.source} =>
          (⟨c.toFun ((piCoordinates n).symm z.val.val),
            (c.map_source z.property).1⟩ : M)) :=
        (c.continuous_toFun.comp_continuous
          ((piCoordinates n).symm.continuous.comp
            (continuous_subtype_val.comp continuous_subtype_val))
          (fun z => z.property)).subtype_mk _
      exact hgcont.congr (fun z => by
        dsimp [g]
        rw [dif_pos (show (piCoordinates n).symm z.val.val ∈ c.source from z.property)]) }
  have hm : MatchesEmbeddedChart e c := by
    intro p hp
    exact ⟨hp, rfl⟩
  refine ⟨e, rfl, ?_, hm⟩
  intro p hp
  have hu := c.map_target ⟨p.property, hp⟩
  obtain ⟨W, G, hW, huW, heG, hG, hDG⟩ := c.regular (c.invFun p.val) hu
  have heq : c.toFun (c.invFun p.val) = p.val := c.right_inv p.val ⟨p.property, hp⟩
  have hep : (e p).val = piCoordinates n (c.invFun p.val) := rfl
  have hdG := (hG.contDiffAt (hW.mem_nhds huW)).differentiableAt (by simp)
  refine ⟨(piCoordinates n).symm ⁻¹' W, parameterExtension G,
    hW.preimage (piCoordinates n).symm.continuous, ?_,
    parameterExtension_contDiffOn hG, ?_, ?_⟩
  · change (piCoordinates n).symm (piCoordinates n (c.invFun p.val)) ∈ W
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  · have hcontOn : ContinuousOn (fun y : M => c.invFun y.val) e.source :=
      c.continuous_invFun.comp continuous_subtype_val.continuousOn
        (fun y hy => ⟨y.property, hy⟩)
    have hcont := hcontOn.continuousAt (e.open_source.mem_nhds hp)
    filter_upwards [e.open_source.mem_nhds hp, hcont.eventually (hW.mem_nhds huW)] with y hy hyW
    change piCoordinates N (G ((piCoordinates n).symm
      (piCoordinates n (c.invFun y.val)))) = piCoordinates N y.val
    rw [ContinuousLinearEquiv.symm_apply_apply,
      heG ⟨c.map_target ⟨y.property, hy⟩, hyW⟩,
      c.right_inv y.val ⟨y.property, hy⟩]
  · rw [hep, (EmbeddedCalculusResults.parameterExtension_hasFDerivAt G _ hdG).fderiv]
    exact (piCoordinates N).injective.comp
      ((hDG _ huW).comp (piCoordinates n).symm.injective)

/-- Availability of the actual induced smooth structure on every boundaryless
D04 smooth embedded manifold, including empty and zero-dimensional cases. -/
theorem induced_euclidean_structure_exists :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_euclidean_structure_existsType := by
  intro n N M hM
  apply induced_structure_of_raw_cover
  intro p
  obtain ⟨c, u, hc, hu, hcu⟩ := hM.2.2 p.val p.property
  obtain ⟨e, he, hraw, hm⟩ := euclidean_chart_of_embedded c hc p
  refine ⟨e, hraw, ?_⟩
  rw [he]
  change p.val ∈ c.ambient
  rw [← hcu]
  exact (c.map_source hu).2

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData TangentData ExteriorData EmbeddedData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Set

abbrev piCoordinates := EmbeddedCalculusData.piCoordinates
abbrev ambientInclusion := @EmbeddedCalculusData.ambientInclusion
abbrev parameterExtension := @EmbeddedCalculusData.parameterExtension
abbrev transportCovector := @EmbeddedCalculusData.transportCovector
abbrev transportField := @EmbeddedCalculusData.transportField

theorem transportField_bijective :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.transportField_bijectiveType := by
  intro n N a M S I k
  have hbij (p : M) : Function.Bijective
      (transportCovector (V := TangentSpace S p) (W := tangentSpace 2 n M p.val) (I p) k) := by
    letI := (tangent_dimension S p).1
    exact EmbeddedCalculusResults.form_bijective
      (V := TangentSpace S p) (W := tangentSpace 2 n M p.val) (I p) k
  constructor
  · intro α β h
    funext p
    exact (hbij p).1 (congrArg (fun η => η p) h)
  · intro η
    choose α hα using (fun p : M => (hbij p).2 (η p))
    exact ⟨α, funext hα⟩

theorem induced_zero_structure_exists :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_zero_structure_existsType := by
  intro N M hM
  have hb : Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model.IsBoundarylessEmbeddedManifold
      (⊤ : ℕ∞) 0 M :=
    D04.boundaryless_iff.mpr ⟨hM, D04.zero_intrinsicBoundary _ M⟩
  obtain ⟨T, hT⟩ := induced_euclidean_structure_exists hb
  let S : SmoothManifold 0 .halfSpace M :=
    ⟨⟨T.topologicalManifold.hausdorff, T.topologicalManifold.secondCountable,
      T.topologicalManifold.atlas, T.topologicalManifold.covers⟩, T.smoothStructure⟩
  exact ⟨S, hT⟩

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData MapData EmbeddedData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Set Filter
open scoped ContDiff Topology

/-- A genuine half-space embedded chart gives a raw intrinsic boundary chart. -/
theorem halfSpace_chart_of_embedded {n N : ℕ} {M : Set (E N)}
    (c : EmbeddedChart ∞ n N M) (hc : c.half = true) (p₀ : M) :
    ∃ e : ModelChart n .halfSpace M,
      e.source = {p : M | p.val ∈ c.ambient} ∧
      IsRawEmbeddedChart e ∧ MatchesEmbeddedChart e c := by
  classical
  have hmodel (u : E n) (hu : u ∈ c.source) :
      piCoordinates n u ∈ modelSet n .halfSpace := by
    obtain ⟨W, hW, he⟩ := c.source_open
    have hh : u ∈ halfSpace n := by
      rw [he] at hu
      simpa [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, hc] using hu.1
    cases n <;> exact hh
  have hz : (0 : ModelData.Euclidean n) ∈ modelSet n .halfSpace := by
    cases n <;> simp [ModelData.modelSet, ModelData.halfSpaceSet]
  let f : M → ModelSpace n .halfSpace := fun p =>
    if hp : p.val ∈ c.ambient then
      ⟨piCoordinates n (c.invFun p.val), hmodel _ (c.map_target ⟨p.property, hp⟩)⟩
    else ⟨0, hz⟩
  have hf (p : M) (hp : p.val ∈ c.ambient) :
      (f p).val = piCoordinates n (c.invFun p.val) := by simp only [f, dif_pos hp]
  let g : ModelSpace n .halfSpace → M := fun z =>
    if hz : (piCoordinates n).symm z.val ∈ c.source then
      ⟨c.toFun ((piCoordinates n).symm z.val), (c.map_source hz).1⟩ else p₀
  let e : ModelChart n .halfSpace M := {
    toFun := f
    invFun := g
    source := {p : M | p.val ∈ c.ambient}
    target := {z | (piCoordinates n).symm z.val ∈ c.source}
    map_source' := by
      intro p hp
      change (piCoordinates n).symm (f p).val ∈ c.source
      rw [hf p hp, ContinuousLinearEquiv.symm_apply_apply]
      exact c.map_target ⟨p.property, hp⟩
    map_target' := by
      intro z hz
      change (piCoordinates n).symm z.val ∈ c.source at hz
      dsimp [g]
      rw [dif_pos hz]
      exact (c.map_source hz).2
    left_inv' := by
      intro p hp
      have hin := c.map_target ⟨p.property, hp⟩
      change g (f p) = p
      dsimp only [g]
      rw [hf p hp, dif_pos (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hin)]
      exact Subtype.ext (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        (c.right_inv p.val ⟨p.property, hp⟩))
    right_inv' := by
      intro z hz
      change (piCoordinates n).symm z.val ∈ c.source at hz
      change f (g z) = z
      dsimp only [g]
      rw [dif_pos hz]
      apply Subtype.ext
      rw [hf _ (c.map_source hz).2, c.left_inv _ hz,
        ContinuousLinearEquiv.apply_symm_apply]
    open_source := c.ambient_open.preimage continuous_subtype_val
    open_target := by
      obtain ⟨W, hW, he⟩ := c.source_open
      have ht : {z : ModelSpace n .halfSpace | (piCoordinates n).symm z.val ∈ c.source} =
          (fun z : ModelSpace n .halfSpace => (piCoordinates n).symm z.val) ⁻¹' W := by
        ext z
        rw [he]
        have hh : (piCoordinates n).symm z.val ∈ parameterSpace n c.half := by
          rw [hc]
          change (piCoordinates n).symm z.val ∈ halfSpace n
          have h := z.property
          cases n <;> exact h
        simp only [mem_setOf_eq, mem_inter_iff, hh, true_and, mem_preimage]
      rw [ht]
      exact hW.preimage ((piCoordinates n).symm.continuous.comp continuous_subtype_val)
    continuousOn_toFun := by
      apply continuousOn_iff_continuous_restrict.mpr
      have hcont := ((piCoordinates n).continuous.comp
        (c.continuous_invFun.comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val)
          (fun z : {p : M | p.val ∈ c.ambient} => ⟨z.val.property, z.property⟩))).subtype_mk
            (fun z => hmodel _ (c.map_target ⟨z.val.property, z.property⟩))
      exact hcont.congr (fun z => Subtype.ext (hf z.val z.property).symm)
    continuousOn_invFun := by
      apply continuousOn_iff_continuous_restrict.mpr
      have hgcont : Continuous (fun z : {z : ModelSpace n .halfSpace |
          (piCoordinates n).symm z.val ∈ c.source} =>
          (⟨c.toFun ((piCoordinates n).symm z.val.val),
            (c.map_source z.property).1⟩ : M)) :=
        (c.continuous_toFun.comp_continuous
          ((piCoordinates n).symm.continuous.comp
            (continuous_subtype_val.comp continuous_subtype_val))
          (fun z => z.property)).subtype_mk _
      exact hgcont.congr (fun z => by
        dsimp [g]
        rw [dif_pos (show (piCoordinates n).symm z.val.val ∈ c.source from z.property)]) }
  have hm : MatchesEmbeddedChart e c := by
    intro p hp
    exact ⟨hp, hf p hp⟩
  refine ⟨e, rfl, ?_, hm⟩
  intro p hp
  have hu := c.map_target ⟨p.property, hp⟩
  obtain ⟨W, G, hW, huW, heG, hG, hDG⟩ := c.regular (c.invFun p.val) hu
  have hep : (e p).val = piCoordinates n (c.invFun p.val) := hf p hp
  have hdG := (hG.contDiffAt (hW.mem_nhds huW)).differentiableAt (by simp)
  refine ⟨(piCoordinates n).symm ⁻¹' W, parameterExtension G,
    hW.preimage (piCoordinates n).symm.continuous, ?_,
    parameterExtension_contDiffOn hG, ?_, ?_⟩
  · rw [hep]
    change (piCoordinates n).symm (piCoordinates n (c.invFun p.val)) ∈ W
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  · have hcontOn : ContinuousOn (fun y : M => c.invFun y.val) e.source :=
      c.continuous_invFun.comp continuous_subtype_val.continuousOn
        (fun y hy => ⟨y.property, hy⟩)
    have hcont := hcontOn.continuousAt (e.open_source.mem_nhds hp)
    filter_upwards [e.open_source.mem_nhds hp, hcont.eventually (hW.mem_nhds huW)] with y hy hyW
    change piCoordinates N (G ((piCoordinates n).symm (e y).val)) = piCoordinates N y.val
    rw [(hm y hy).2, ContinuousLinearEquiv.symm_apply_apply,
      heG ⟨c.map_target ⟨y.property, hy⟩, hyW⟩,
      c.right_inv y.val ⟨y.property, hy⟩]
  · rw [hep, (EmbeddedCalculusResults.parameterExtension_hasFDerivAt G _ hdG).fderiv]
    exact (piCoordinates N).injective.comp
      ((hDG _ huW).comp (piCoordinates n).symm.injective)

end SmoothManifolds.EmbeddedAtlasResults

namespace SmoothManifolds.EmbeddedAtlasResults
open ModelData AtlasData MapData EmbeddedData EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Set Filter
open scoped ContDiff Topology

private theorem halfSpaceModel_mem_of_nonneg {d : ℕ}
    (z : ModelData.Euclidean (d+1)) (hz : 0 ≤ z (Fin.last d)) :
    z ∈ ModelData.modelSet (d+1) .halfSpace := hz

/-- Translation identifies an open part of Euclidean space with the interior
of the half-space. The value outside the source is immaterial. -/
def interiorHalfSpaceChart (d : ℕ) (b : ModelData.Euclidean (d+1)) :
    OpenPartialHomeomorph (ModelSpace (d+1) .euclidean) (ModelSpace (d+1) .halfSpace) := by
  classical
  let f : ModelSpace (d+1) .euclidean → ModelSpace (d+1) .halfSpace := fun x =>
    if hx : 0 < (x.val + b) (Fin.last d) then
      ⟨x.val + b, halfSpaceModel_mem_of_nonneg _ (le_of_lt hx)⟩
    else ⟨0, halfSpaceModel_mem_of_nonneg _ (by simp)⟩
  let g : ModelSpace (d+1) .halfSpace → ModelSpace (d+1) .euclidean :=
    fun z => ⟨z.val - b, mem_univ _⟩
  refine {
    toFun := f
    invFun := g
    source := {x | 0 < (x.val + b) (Fin.last d)}
    target := {z | 0 < z.val (Fin.last d)}
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := isOpen_lt continuous_const
      ((continuous_apply (Fin.last d)).comp (continuous_subtype_val.add continuous_const))
    open_target := isOpen_lt continuous_const
      ((continuous_apply (Fin.last d)).comp continuous_subtype_val)
    continuousOn_toFun := ?_
    continuousOn_invFun :=
      ((continuous_subtype_val.sub continuous_const).subtype_mk _).continuousOn }
  · intro x hx
    change 0 < (x.val + b) (Fin.last d) at hx
    change 0 < (f x).val (Fin.last d)
    simpa only [f, dif_pos hx] using hx
  · intro z hz
    change 0 < z.val (Fin.last d) at hz
    change 0 < (z.val - b + b) (Fin.last d)
    simpa only [sub_add_cancel] using hz
  · intro x hx
    change 0 < (x.val + b) (Fin.last d) at hx
    apply Subtype.ext
    change (f x).val - b = x.val
    simp only [f, dif_pos hx, add_sub_cancel_right]
  · intro z hz
    change 0 < z.val (Fin.last d) at hz
    apply Subtype.ext
    change (f (g z)).val = z.val
    have hzg : 0 < ((g z).val + b) (Fin.last d) := by
      simpa only [g, sub_add_cancel] using hz
    simp only [f, dif_pos hzg, g, sub_add_cancel]
  · apply continuousOn_iff_continuous_restrict.mpr
    have hcont : Continuous (fun x :
        {x : ModelSpace (d+1) .euclidean | 0 < (x.val + b) (Fin.last d)} =>
        (⟨x.val.val + b, halfSpaceModel_mem_of_nonneg _ (le_of_lt x.property)⟩ :
          ModelSpace (d+1) .halfSpace)) :=
      ((continuous_subtype_val.comp continuous_subtype_val).add continuous_const).subtype_mk _
    exact hcont.congr (fun x => by
      apply Subtype.ext
      change x.val.val + b = (f x.val).val
      have hx : 0 < (x.val.val + b) (Fin.last d) := x.property
      simp only [f, dif_pos hx])

/-- Every raw Euclidean chart can be translated and restricted to a raw
half-space chart about any selected point, with unchanged full rank. -/
theorem raw_halfSpace_chart_at {d N : ℕ} {M : Set (E N)}
    (e : ModelChart (d+1) .euclidean M) (he : IsRawEmbeddedChart e)
    (p : M) (hp : p ∈ e.source) :
    ∃ f : ModelChart (d+1) .halfSpace M, IsRawEmbeddedChart f ∧ p ∈ f.source := by
  let b : ModelData.Euclidean (d+1) := fun _ => 1 - (e p).val (Fin.last d)
  let t := interiorHalfSpaceChart d b
  have ht (x : ModelSpace (d+1) .euclidean) (hx : x ∈ t.source) :
      (t x).val = x.val + b := by
    change 0 < (x.val + b) (Fin.last d) at hx
    change (if h : 0 < (x.val + b) (Fin.last d) then
      (⟨x.val + b, halfSpaceModel_mem_of_nonneg _ (le_of_lt h)⟩ :
        ModelSpace (d+1) .halfSpace)
      else ⟨0, halfSpaceModel_mem_of_nonneg _ (by simp)⟩).val = _
    rw [dif_pos hx]
  have hpt : e p ∈ t.source := by
    change 0 < (e p).val (Fin.last d) + (1 - (e p).val (Fin.last d))
    linarith
  refine ⟨e.trans t, ?_, hp, hpt⟩
  intro q hq
  have hqe : q ∈ e.source := hq.1
  have hqt : e q ∈ t.source := hq.2
  obtain ⟨V, H, hV, hqV, hH, heH, hinj⟩ := he q hqe
  have hcoord : ((e.trans t) q).val = (e q).val + b := ht _ hqt
  let V' := (fun z : ModelData.Euclidean (d+1) => z - b) ⁻¹' V
  have hV' : IsOpen V' := hV.preimage (continuous_id.sub continuous_const)
  refine ⟨V', fun z => H (z - b), hV', ?_, ?_, ?_, ?_⟩
  · change ((e.trans t) q).val - b ∈ V
    rwa [hcoord, add_sub_cancel_right]
  · exact hH.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)
  · filter_upwards [(e.trans t).open_source.mem_nhds hq, heH] with y hy hHy
    change H ((t (e y)).val - b) = _
    rw [ht (e y) (show e y ∈ t.source from hy.2), add_sub_cancel_right]
    exact hHy
  · rw [fderiv_comp_sub, hcoord, add_sub_cancel_right]
    exact hinj

/-- Availability of the actual induced structure in the uniform half-space
model, with no full-rank or compatibility assumptions added to D04's data. -/
theorem induced_structure_exists :
    Specs.SmoothManifolds.Integration.EmbeddedAtlas.induced_structure_existsType := by
  intro n N M hM
  cases n with
  | zero => exact induced_zero_structure_exists hM
  | succ d =>
    apply induced_structure_of_raw_cover
    intro p
    obtain ⟨c, u, hu, hcu⟩ := hM.2.2 p.val p.property
    have hp : p.val ∈ c.ambient := by
      rw [← hcu]
      exact (c.map_source hu.1).2
    cases hc : c.half with
    | false =>
      obtain ⟨e, he, hraw, hm⟩ := euclidean_chart_of_embedded c hc p
      obtain ⟨f, hf, hpf⟩ := raw_halfSpace_chart_at e hraw p (by rwa [he])
      exact ⟨f, hf, hpf⟩
    | true =>
      obtain ⟨e, he, hraw, hm⟩ := halfSpace_chart_of_embedded c hc p
      exact ⟨e, hraw, by rwa [he]⟩

end SmoothManifolds.EmbeddedAtlasResults
