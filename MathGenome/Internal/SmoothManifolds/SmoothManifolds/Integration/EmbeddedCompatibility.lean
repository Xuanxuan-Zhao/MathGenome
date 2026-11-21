import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedCompatibility
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedCalculus
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Stokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Densities
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.DensityIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedAtlas
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.EmbeddedBoundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Global
import MathGenome.Internal.MultivariableAnalysis.D04.C15.OrientedManifoldAndDensityIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C15.ManifoldIntegralIndependence
import MathGenome.Internal.MultivariableAnalysis.D04.C14.FiniteCompactPartition
import MathGenome.Internal.MultivariableAnalysis.D04.C15.GeneralizedStokes

/-! M10.08: comparison with the genuine D04 embedded integration and intrinsic Stokes constructions. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical ContDiff BigOperators

namespace SmoothManifolds.EmbeddedIntegrationResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData
  ExteriorData EmbeddedCalculusData EmbeddedAtlasData OrientationData
  LocalIntegrationData GlobalIntegrationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Set MeasureTheory

/-- Proper integrability provides a box around the support, so its indicator
is the original zero extension. D04's checked box bridge then applies. -/
theorem proper_integral_bridge :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.proper_integral_bridgeType := by
  intro n U f hf
  obtain ⟨Q, hQ, hi⟩ := hf.2
  obtain ⟨hi', hv⟩ := D04.DirectedSubstitution.proper_on_box hf Q hQ
  obtain ⟨_, hL, heq⟩ := D04.MeasureBridge.box_bridge (zeroExtension f) Q hi'
  have he : (Specs.D04.C06.DarbouxIntegral.Model.carrier Q).indicator
      (zeroExtension f) = zeroExtension f := by
    funext x
    by_cases hx : x ∈ Specs.D04.C06.DarbouxIntegral.Model.carrier Q
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      symm
      apply Function.notMem_support.mp
      intro hs
      exact hx (interior_subset (hQ (subset_closure hs)))
  rw [he] at hL
  refine ⟨hL, hv.trans (heq.trans ?_)⟩
  rw [← integral_indicator (D04.MeasureBridge.measurableSet_carrier Q), he]

theorem proper_integral_pi_bridge :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.proper_integral_pi_bridgeType := by
  intro n U f hf
  rw [(proper_integral_bridge f hf).2]
  symm
  exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (zeroExtension f)

theorem localized_top_integral :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.localized_top_integralType := by
  intro r n N M η hη K P i
  exact proper_integral_bridge _
    (D04.ManifoldIntegral.top_coefficients_integrable η hη P i).2.2

private theorem piCoordinates_basis (n : ℕ) (i : Fin n) :
    piCoordinates n (standardBasis n i) = Pi.single i 1 := by
  change piCoordinates n (EuclideanSpace.basisFun (Fin n) ℝ i) = _
  rw [EuclideanSpace.basisFun_apply]
  rfl

theorem matching_localized_coefficient :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.matching_localized_coefficientType := by
  intro n N a M S hS I hI C e he c hm ξ w u p hp
  have hv := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he
    c hm u u.property hp).2 n ξ
  have ht : Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback
      (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) (transportField S I n ξ) u
        (standardBasis n) =
      FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he
        ⟨c.toFun u, (c.map_source u.property).1⟩ hp ξ := by
    change _ = evaluate (TangentSpace S p) n (ξ p)
      (fun j => (C.tangent.fiberCoordinates.equiv e he p hp).symm (Pi.single j 1))
    convert hv.1 (standardBasis n) using 1
    congr 1
    funext j
    congr 1
    exact (piCoordinates_basis n j).symm
  change w (c.toFun u) *
    Specs.D04.C14.MetricTopFormsAndDensities.Model.tangentPullback
      (transportField S I n ξ) (lowerChart c (by simp)) u u.property (standardBasis n) = _
  congr 1
  convert ht using 1
  have hu₂ : (u : E n) ∈ (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)).source := u.property
  unfold Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback
  rw [dite_eq_left hu₂]
  rfl

theorem zero_integral_comparison :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.zero_integral_comparisonType := by
  classical
  intro N a M S o
  obtain ⟨F, hF⟩ := EmbeddedBoundaryResults.zero_orientation_transport M S
  have hs (p : M) : (F o p).val = zeroSign o p := by
    unfold zeroSign
    split_ifs with hp
    · exact (hF o p).mpr hp
    · rcases (F o p).property with h | h
      · exact False.elim (hp ((hF o p).mp h))
      · exact h
  refine ⟨F o, hs, ?_⟩
  intro I J hJ ξ
  rw [GlobalIntegrationResults.zero_dimension S o J hJ ξ]
  unfold LocalIntegrationData.zeroIntegral
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.zeroIntegral
  apply finsum_congr
  intro p
  rw [hs]
  congr 1
  symm
  have hz := EmbeddedCompatibilityResults.degree_zero_transport (V := TangentSpace S p)
    (W := ↥(tangentSpace 2 0 M p.val)) (I p) (zeroCoefficient ξ.field p)
    (fun j => Fin.elim0 j)
  simpa only [transportField, zeroCoefficient, LinearEquiv.symm_apply_apply] using hz


theorem matching_density_coefficient :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.matching_density_coefficientType := by
  intro n N a M S hS I hI C g hg μ hμ e he c hm ρ w u p hp
  let K := C.tangent.fiberCoordinates
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hc := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he
    c hm u u.property hp).1
  have hc' (i : Fin n) :
      (I p ((K.equiv e he p hp).symm ((Pi.basisFun ℝ (Fin n)) i))).val =
        chartDifferential c₂ u (standardBasis n i) := by
    have h := congrArg Subtype.val (hc (standardBasis n i))
    rw [piCoordinates_basis] at h
    simpa only [Pi.basisFun_apply, K, c₂, p,
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap,
      LinearMap.codRestrict_apply, ContinuousLinearMap.coe_coe] using h
  have hmatrix : MetricVolumeData.metricMatrix g K e he ⟨p, hp⟩ =
      fun i j => inner ℝ (chartDifferential c₂ u (standardBasis n i))
        (chartDifferential c₂ u (standardBasis n j)) := by
    ext i j
    change MetricVolumeData.metricForm g p _ _ = _
    rw [hg, hc', hc']
  have hcoef : MetricVolumeData.densityCoefficient K e he ⟨p, hp⟩ (ρ p • μ p) =
      densityCoefficient ρ c₂ u := by
    change ρ p * (μ p).val (OrientationData.coordinateVector K e he ⟨p, hp⟩) = _
    rw [hμ]
    rw [((MetricVolumeResults.gram S C g K e he).1 ⟨p, hp⟩).1, hmatrix]
    rfl
  exact ⟨hcoef, congrArg (fun t : ℝ => w p.val * t) hcoef⟩

theorem localized_density_integral :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.localized_density_integralType := by
  intro r n N M hM ρ hρ K P i
  exact proper_integral_bridge _
    (D04.ManifoldIntegral.density_coefficients_integrable hM ρ hρ P i).2.2

/-- A chart and its matching parametrization give the same ambient extension. -/
theorem matching_chart_zeroExtension
    {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (e : ModelChart n a M) (c : EmbeddedChart ∞ n N M)
    (hm : MatchesEmbeddedChart e c)
    (hcover : ∀ z (hz : z ∈ c.source),
      (⟨c.toFun z, (c.map_source hz).1⟩ : M) ∈ e.source)
    (f : e.source → ℝ) (g : c.source → ℝ)
    (hf : ∀ z (hz : z ∈ c.source),
      f ⟨⟨c.toFun z, (c.map_source hz).1⟩, hcover z hz⟩ = g ⟨z, hz⟩)
    (x : Euclidean n) :
    extendModel (fun t => if ht : t ∈ e.target then
      f ⟨e.symm t, e.map_target ht⟩ else 0) x =
      zeroExtension g ((piCoordinates n).symm x) := by
  classical
  let z := (piCoordinates n).symm x
  have hxz : piCoordinates n z = x := (piCoordinates n).apply_symm_apply x
  by_cases hz : z ∈ c.source
  · let p : M := ⟨c.toFun z, (c.map_source hz).1⟩
    have hp : p ∈ e.source := hcover z hz
    have hep : (e p).val = x :=
      (hm p hp).2.trans (by
        change piCoordinates n (c.invFun (c.toFun z)) = x
        rw [c.left_inv z hz]
        exact hxz)
    have hx : x ∈ modelSet n a := by rw [← hep]; exact (e p).property
    have ht : (⟨x, hx⟩ : ModelSpace n a) ∈ e.target := by
      have hh := e.map_source hp
      convert hh using 1
      exact Subtype.ext hep.symm
    have hpe : e.symm ⟨x, hx⟩ = p := by
      have hh : (⟨x, hx⟩ : ModelSpace n a) = e p := Subtype.ext hep.symm
      rw [hh, e.left_inv hp]
    unfold extendModel zeroExtension
    rw [dite_eq_left hx]
    dsimp only []
    rw [dite_eq_left ht, dite_eq_left hz]
    simpa only [hpe] using hf z hz
  · have hzero : zeroExtension g z = 0 := dite_eq_right hz
    rw [hzero]
    unfold extendModel
    by_cases hx : x ∈ modelSet n a
    · rw [dite_eq_left hx]
      dsimp only []
      by_cases ht : (⟨x, hx⟩ : ModelSpace n a) ∈ e.target
      · exfalso
        let p : M := e.symm ⟨x, hx⟩
        have hp : p ∈ e.source := e.map_target ht
        have hpx : (e p).val = x := congrArg Subtype.val (e.right_inv ht)
        have hcp : c.invFun p.val = z := by
          apply (piCoordinates n).injective
          exact (hm p hp).2.symm.trans (hpx.trans hxz.symm)
        apply hz
        rw [← hcp]
        exact c.map_target ⟨p.property, (hm p hp).1⟩
      · exact dite_eq_right ht
    · exact dite_eq_right hx

/-- Matching parametrizations covering the same chart have identical full
zero extensions, including the true boundary and every artificial chart edge. -/
theorem matching_coordinate_coefficient
    {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (hcover : ∀ z (hz : z ∈ c.source),
      (⟨c.toFun z, (c.map_source hz).1⟩ : M) ∈ e.source)
    (ξ : Field S n) (w : E N → ℝ) (x : Euclidean n) :
    coordinateCoefficient C.tangent.fiberCoordinates e he
        (fun p => w p.val • ξ p) x =
      zeroExtension (localizedTopCoefficient (transportField S I n ξ)
        (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) w)
        ((piCoordinates n).symm x) := by
  apply matching_chart_zeroExtension e c hm hcover
    (fun p => FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he
      p.val p.property (fun p => w p.val • ξ p)) _ ?_ x
  intro z hz
  rw [matching_localized_coefficient S hS I hI C e he c hm ξ w
    ⟨z, hz⟩ (hcover z hz)]
  change evaluate (TangentSpace S _) n (w _ • ξ _) _ =
    w _ * evaluate (TangentSpace S _) n (ξ _) _
  rw [map_smul, smul_apply]
  rfl

/-- Degree-zero alternating forms are determined by their sole value. -/
theorem topSupport_zero_value {r : ℕ∞ω} {N : ℕ} {M : Set (E N)}
    (η : Specs.D04.C14.MetricTopFormsAndDensities.Model.TangentTopField r 0 M) :
    tsupport (fun p : M => η p (fun j => Fin.elim0 j)) = topSupport η := by
  change closure {p | η p (fun j => Fin.elim0 j) ≠ 0} = closure {p | η p ≠ 0}
  congr 1
  ext p
  change η p (fun j => Fin.elim0 j) ≠ 0 ↔ η p ≠ 0
  constructor
  · intro hv hh
    exact hv (by rw [hh]; rfl)
  · intro hh hv
    apply hh
    ext v
    change η p v = 0
    have he : v = (fun j => Fin.elim0 j) := Subsingleton.elim _ _
    rwa [he]

/-- The full actual D04 integral predicate in dimension zero, with the same
signed scalar sum and without finiteness of the underlying manifold. -/
theorem zero_hasManifoldIntegral
    {N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hM : IsEmbeddedManifold ∞ 0 M)
    (S : SmoothManifold 0 a M) (o : Orientation S) :
    ∃ O : Specs.D04.C14.OrientationsAndChartSigns.Model.ZeroManifoldOrientation M,
      (∀ p, (O p).val = zeroSign o p) ∧
      ∀ (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 0 M p.val)
        (J : CompactTopForm S → ℝ), IsIntegral o J → ∀ ξ : CompactTopForm S,
        Specs.D04.C15.GeneralizedStokes.Model.HasManifoldIntegral 2 0 O
          (transportField S I 0 ξ.field) (J ξ) := by
  obtain ⟨O, hs, hv⟩ := zero_integral_comparison S o
  refine ⟨O, hs, ?_⟩
  intro I J hJ ξ
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  have hc : IsCompact (topSupport (transportField S I 0 ξ.field)) := by
    have hs := EmbeddedCalculusResults.support_identification S I 0 ξ.field
    change IsCompact (ModelData.sectionSupport (transportField S I 0 ξ.field))
    exact hs.symm ▸ ξ.compact_support
  refine ⟨hM₂, hc, ?_, (hv I J hJ ξ).symm⟩
  apply D04.ManifoldIntegral.zero_support_finite hM₂
  change IsCompact (tsupport _)
  rw [topSupport_zero_value]
  exact hc

open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.FiniteCompactPartition.Model

/-- Literal matching chart signs, with the orientation identified by its actual
basis criterion. This is valid without requiring the chart sign to be constant. -/
theorem matching_chart_sign {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (o : OrientationData.Orientation S) (s : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s)
    (O : TangentOrientationField 2 n M)
    (hO : ∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
      b.orientation = O p.val p.property ↔
        IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j))))
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (u : E n) (hu : u ∈ c.source)
    (hp : (⟨c.toFun u, (c.map_source hu).1⟩ : M) ∈ e.source) :
    chartSign O (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) u hu =
      signValue (s.sign e he ⟨⟨c.toFun u, (c.map_source hu).1⟩, hp⟩) := by
  classical
  let c₂ := lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  let K := C.tangent.fiberCoordinates
  let A := K.equiv e he p hp
  let b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val) :=
    D04.Orientations.chartBasis c₂ (by constructor <;> norm_num) hM.2.1 u hu
  have hcoord := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he c hm u hu hp).1
  have hvec (j : Fin n) : (I p).symm (b j) = A.symm ((Pi.basisFun ℝ (Fin n)) j) := by
    apply (I p).injective
    rw [LinearEquiv.apply_symm_apply]
    have hb : b j = Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartTangentMap c₂ u hu (standardBasis n j) := rfl
    rw [hb, ← hcoord]
    congr 1
  have hpos := (BoundaryOrientations.positive_signed_generator_iff (o.val p)
    (coordinateVector K e he ⟨p, hp⟩) (s.sign e he ⟨p, hp⟩) (hs K e he ⟨p, hp⟩)).1
  have hbpos : b.orientation = O p.val p.property ↔ s.sign e he ⟨p, hp⟩ = true := by
    rw [hO p b]
    simpa only [hvec, coordinateVector] using hpos
  have hsign : chartSign O c₂ u hu = 1 ↔ s.sign e he ⟨p, hp⟩ = true :=
    (D04.Orientations.chartSign_basis O c₂ u hu b (fun _ => rfl)).trans hbpos
  rcases D04.Orientations.chartSign_values O c₂ (by constructor <;> norm_num) hM.2.1 u hu with hv | hv
  · rw [hv, (hsign.mp hv)]
    rfl
  · have hfalse : s.sign e he ⟨p, hp⟩ = false := by
      cases h : s.sign e he ⟨p, hp⟩
      · rfl
      · have hh := hsign.mpr h
        linarith
    rw [hv, hfalse]
    rfl

/-- Matching ordered top coefficients before multiplication by a weight. -/
theorem matching_top_coefficient {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (ξ : Field S n) (u : c.source)
    (hp : (⟨c.toFun u, (c.map_source u.property).1⟩ : M) ∈ e.source) :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.topCoefficient
      (transportField S I n ξ) (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) u =
    FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he
      ⟨c.toFun u, (c.map_source u.property).1⟩ hp ξ := by
  have hv := (EmbeddedAtlasResults.matching_chart_pullback S hS I hI C e he
    c hm u u.property hp).2 n ξ
  have ht : Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback
      (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) (transportField S I n ξ) u
        (standardBasis n) =
      FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he
        ⟨c.toFun u, (c.map_source u.property).1⟩ hp ξ := by
    change _ = evaluate (TangentSpace S _) n (ξ _)
      (fun j => (C.tangent.fiberCoordinates.equiv e he _ hp).symm (Pi.single j 1))
    convert hv.1 (standardBasis n) using 1
    congr 1
    funext j
    congr 1
    symm
    change piCoordinates n (EuclideanSpace.basisFun (Fin n) ℝ j) = _
    rw [EuclideanSpace.basisFun_apply]
    rfl
  convert ht using 1
  have hu₂ : (u : E n) ∈ (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)).source := u.property
  unfold Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback
  rw [dite_eq_left hu₂]
  rfl

/-- Signs remain inside the coefficient and may vary between chart components. -/
theorem matching_signed_coordinate_coefficient
    {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (o : OrientationData.Orientation S) (s : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s)
    (O : PositiveManifoldOrientation 2 n M)
    (hO : ∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
      b.orientation = O.atPoint p.val p.property ↔
        IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j))))
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (c : EmbeddedChart ∞ n N M) (hm : MatchesEmbeddedChart e c)
    (hcover : ∀ z (hz : z ∈ c.source),
      (⟨c.toFun z, (c.map_source hz).1⟩ : M) ∈ e.source)
    (ξ : Field S n) (w : E N → ℝ) (x : Euclidean n) :
    signedCoordinateCoefficient s C.tangent.fiberCoordinates e he
        (fun p => w p.val • ξ p) x =
      zeroExtension (D04.ManifoldIntegralIndependence.weightedCoefficient
        (D04.ManifoldIntegralIndependence.signedCoefficient O (transportField S I n ξ))
        (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) w)
        ((piCoordinates n).symm x) := by
  apply matching_chart_zeroExtension e c hm hcover
    (fun p => signValue (s.sign e he p) *
      FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he
        p.val p.property (fun p => w p.val • ξ p)) _ ?_ x
  intro z hz
  change signValue (s.sign e he _) *
    FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he _ _
      (fun p => w p.val • ξ p) =
    w (c.toFun z) * (chartSign O.atPoint (lowerChart c (by simp)) z hz *
      Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.topCoefficient
        (transportField S I n ξ) (lowerChart c (by simp)) ⟨z, hz⟩)
  have ht : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.topCoefficient
      (transportField S I n ξ) (lowerChart c (by simp : (2 : ℕ∞ω) ≤ ∞)) ⟨z, hz⟩ =
      FormPullbackData.topCoefficient C.tangent.fiberCoordinates e he
        ⟨c.toFun z, (c.map_source hz).1⟩ (hcover z hz) ξ :=
    matching_top_coefficient S hS I hI C e he c hm ξ ⟨z, hz⟩ (hcover z hz)
  rw [matching_chart_sign hM S hS I hI C o s hs O.atPoint hO e he c hm z hz (hcover z hz),
    ht, GlobalIntegrationResults.topCoefficient_weight]
  ring

/-- A finite ambient partition can be chosen in literal matching smooth charts.
The construction does not replace or restrict the arbitrary C² partition used
in the final value statement. -/
theorem exists_matching_partition {n N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (K : Set M) (hK : IsCompact K) :
    ∃ (m : ℕ) (e : Fin m → ModelChart n a M)
      (he : ∀ i, e i ∈ S.smoothStructure.val)
      (c : Fin m → EmbeddedChart ∞ n N M) (w : Fin m → E N → ℝ),
      (∀ i, MatchesEmbeddedChart (e i) (c i)) ∧
      (∀ i (u : E n) (hu : u ∈ (c i).source),
        (⟨(c i).toFun u, ((c i).map_source hu).1⟩ : M) ∈ (e i).source) ∧
      PartitionNear M K (fun i => (e i).source) m id w := by
  classical
  have hchoices : ∀ p : K, ∃ (e : ModelChart n a M),
      e ∈ S.smoothStructure.val ∧ p.val ∈ e.source ∧
      ∃ c : EmbeddedChart ∞ n N M, MatchesEmbeddedChart e c ∧
      ∀ (u : E n) (hu : u ∈ c.source),
        (⟨c.toFun u, (c.map_source hu).1⟩ : M) ∈ e.source := by
    intro p
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p.val
    have hraw : IsRawEmbeddedChart e := by
      have he' := he
      rw [hS] at he'
      exact he'
    obtain ⟨c, hm, hcover, _⟩ := EmbeddedBoundaryResults.embedded_chart_of_raw e hraw p.val hp
    exact ⟨e, he, hp, c, hm, hcover⟩
  choose e he hp c hm hcover using hchoices
  let c₂ : K → EmbeddedChart 2 n N M := fun p => lowerChart (c p) (by simp)
  have hc (p : K) : p.val.val ∈ (c₂ p).ambient := (hm p p.val (hp p)).1
  obtain ⟨m, a', p, w, hw, hsub⟩ := D04.FiniteCompactPartition.finite_partition_refined
    (r := (2 : ℕ∞ω)) (k := n) (M := M) (EmbeddedAtlasResults.smooth_c2_tangents hM).1
    K hK (fun _ : Unit => (univ : Set M)) (fun _ => isOpen_univ)
    (by intro p hp; simp) c₂ hc (fun p => (e p).source)
    (fun p => (e p).open_source) hp
  refine ⟨m, fun i => e (p i), fun i => he (p i), fun i => c (p i), w,
    fun i => hm (p i), fun i => hcover (p i), ?_⟩
  exact ⟨hw.1, hw.2.1, fun i => ⟨(hw.2.2.1 i).1,
    fun x hx => (hsub i hx).1⟩, hw.2.2.2⟩

/-- Continuity of the bundled abstract top section is already exactly the
common D04 continuity condition; no extra smoothness premise is needed. -/
theorem continuous_transport_top
    {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (ξ : CompactTopForm S) :
    ContinuousTopField (transportField S I n ξ.field) := by
  have hcont : ExteriorDerivativeData.IsContinuousField C n ξ.field := by
    intro e he J
    have htuple : (fun j => Set.powersetCard.ofFinEmbEquiv.symm J j) = id :=
      (Set.powersetCard.ofFinEmbEquiv.symm J).strictMono.eq_id
    apply Continuous.congr (ξ.continuous C.tangent.fiberCoordinates e he)
    intro p
    rw [EmbeddedCalculusResults.coefficient_evaluation C n e he ξ.field p J]
    unfold FormPullbackData.topCoefficient CovectorData.coordinateVector
    congr 1
    funext j
    rw [congrFun htuple j]
    rfl
  exact D04Stokes.intrinsic_top_continuous _
    ((EmbeddedDerivativeResults.continuous_transport hM S hS I hI C n ξ.field).mp hcont)

/-- The actual finite D04 sum equals every abstract integral characterized by
its signed coordinate normalization. P remains an arbitrary C² test partition. -/
theorem orientedIntegral_comparison
    {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (o : OrientationData.Orientation S) (O : PositiveManifoldOrientation 2 n M)
    (hO : ∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
      b.orientation = O.atPoint p.val p.property ↔
        IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j))))
    (J : CompactTopForm S → ℝ) (hJ : IsIntegral o J)
    (ξ : CompactTopForm S)
    (hη : ContinuousTopField (transportField S I n ξ.field))
    (P : SignedChartPartition O (topSupport (transportField S I n ξ.field))) :
    orientedIntegral (transportField S I n ξ.field) P = J ξ := by
  classical
  let η := transportField S I n ξ.field
  have hsupp : topSupport η = sectionSupport ξ.field :=
    EmbeddedCalculusResults.support_identification S I n ξ.field
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨m, e, he, c, w, hm, hcover, hw⟩ :=
    exists_matching_partition hM S hS (sectionSupport ξ.field) ξ.compact_support
  let Q : ChartPartition 2 n M (sectionSupport ξ.field) := {
    count := m
    chart := fun i => lowerChart (c i) (by simp)
    weight := w
    partition := ⟨hw.1, hw.2.1,
      fun i => ⟨(hw.2.2.1 i).1,
        fun p hp => (hm i p ((hw.2.2.1 i).2 hp)).1⟩, hw.2.2.2⟩ }
  have hloc : IsLocalization e (fun i p => w i p.val) ξ := by
    refine ⟨fun i => (hw.1 i).continuous.comp continuous_subtype_val,
      locallyFinite_of_finite _, fun i => (hw.2.2.1 i).2, ?_⟩
    obtain ⟨V, hV, hKV, hVsum⟩ := hw.2.2.2.1
    exact ⟨V, hV, hKV, fun p hp => by simpa only [finsum_eq_sum_of_fintype] using hVsum p hp⟩
  have hglobal : J ξ = ∑ i : Fin m, coordinateIntegral s C.tangent.fiberCoordinates
      (e i) (he i) (fun p => w i p.val • ξ.field p) := by
    simpa only [finsum_eq_sum_of_fintype] using
      GlobalIntegrationResults.localization S o J hJ s hs C.tangent.fiberCoordinates e he
        (fun i p => w i p.val) ξ hloc
  let A := D04.ManifoldIntegralIndependence.signedCoefficient O η
  have hlocal (i : Fin m) :
      coefficientIntegral (D04.ManifoldIntegralIndependence.weightedCoefficient A
        (Q.chart i) (Q.weight i)) =
      coordinateIntegral s C.tangent.fiberCoordinates (e i) (he i)
        (fun p => w i p.val • ξ.field p) := by
    have hi := D04.ManifoldIntegral.localized_coefficient_integrable (Q.chart i) (Q.weight i)
      (A (Q.chart i)) (Q.partition.1 i).continuous
      (D04.ManifoldIntegralIndependence.signedCoefficient_continuous O η hη (Q.chart i))
      (Q.partition.2.2.1 i).1 (Q.partition.2.2.1 i).2
    have hip : ProperIntegrable (D04.ManifoldIntegralIndependence.weightedCoefficient A
        (Q.chart i) (Q.weight i)) := hi.2.2
    rw [proper_integral_pi_bridge _ hip]
    unfold coordinateIntegral
    apply integral_congr_ae
    filter_upwards [] with x
    exact (matching_signed_coordinate_coefficient hM S hS I hI C o s hs O hO
      (e i) (he i) (c i) (hm i) (hcover i) ξ.field (w i) x).symm
  calc
    orientedIntegral η P = ∑ i, coefficientIntegral
        (D04.ManifoldIntegralIndependence.weightedCoefficient A (P.chart i) (P.weight i)) :=
      D04.ManifoldIntegralIndependence.signed_expression O η hη P
    _ = ∑ i, coefficientIntegral
        (D04.ManifoldIntegralIndependence.weightedCoefficient A (Q.chart i) (Q.weight i)) :=
      D04.ManifoldIntegralIndependence.partition_independence A
        (D04.ManifoldIntegralIndependence.signedCoefficient_continuous O η hη)
        (D04.ManifoldIntegralIndependence.signedCoefficient_transition O η)
        O.manifold.1 O.manifold.2.1 P.toChartPartition Q
        (fun c u hu => D04.ManifoldIntegralIndependence.signedCoefficient_support O η c u hu)
        (fun c u hu => hsupp ▸ D04.ManifoldIntegralIndependence.signedCoefficient_support O η c u hu)
    _ = _ := (Finset.sum_congr rfl (fun i _ => hlocal i)).trans hglobal.symm

/-- The full original D04 value predicate, including existence, proper
integrability and equality for every C² finite signed chart partition. -/
theorem hasPositiveIntegral_comparison
    {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (o : OrientationData.Orientation S) (O : PositiveManifoldOrientation 2 n M)
    (hO : ∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
      b.orientation = O.atPoint p.val p.property ↔
        IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j))))
    (J : CompactTopForm S → ℝ) (hJ : IsIntegral o J)
    (ξ : CompactTopForm S)
    :
    Specs.D04.C15.GeneralizedStokes.Model.HasPositiveIntegral O
      (transportField S I n ξ.field) (J ξ) := by
  have hη := continuous_transport_top hM S hS I hI C ξ
  have hk : IsCompact (topSupport (transportField S I n ξ.field)) := by
    rw [show topSupport (transportField S I n ξ.field) = sectionSupport ξ.field from
      EmbeddedCalculusResults.support_identification S I n ξ.field]
    exact ξ.compact_support
  refine ⟨hη, hk, D04.ManifoldIntegral.signed_partition_exists O _ hk, ?_⟩
  intro P
  exact ⟨fun i => (D04.ManifoldIntegral.top_coefficients_integrable _ hη P.toChartPartition i).2.2,
    orientedIntegral_comparison hM S hS I hI C o O hO J hJ ξ hη P⟩



/-- The actual D04 manifold integral agrees with the abstract integral in
every dimension, with the two orientation conventions explicitly identified. -/
theorem integral_comparison
    {n N : ℕ} {a : ModelKind} {M : Set (E N)} (hM : IsEmbeddedManifold ∞ n M)
    (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (o : OrientationData.Orientation S) :
    ∃ O : ManifoldOrientation 2 n M,
      (∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
        EmbeddedIntegrationData.D04PositiveBasis n M O p b ↔
          IsPositive (o.val p) (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j)))) ∧
      ∀ (J : CompactTopForm S → ℝ), IsIntegral o J → ∀ ξ : CompactTopForm S,
        Specs.D04.C15.GeneralizedStokes.Model.HasManifoldIntegral 2 n O
          (transportField S I n ξ.field) (J ξ) := by
  cases n with
  | zero =>
    obtain ⟨O, hs, hval⟩ := zero_hasManifoldIntegral hM S o
    refine ⟨O, ?_, fun J hJ ξ => hval I J hJ ξ⟩
    intro p b
    have hz : exteriorPower.ιMulti ℝ 0 (fun j : Fin 0 => (I p).symm (b j)) =
        (exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1 := by
      apply (exteriorPower.zeroEquiv ℝ (TangentSpace S p)).injective
      simp
    change (O p).val = 1 ↔ _
    rw [hs p, hz]
    unfold zeroSign
    split_ifs with hp <;> simp_all <;> norm_num
  | succ d =>
    obtain ⟨O, hO, _⟩ := EmbeddedBoundaryResults.orientation_transport
      (by omega : 0 < d+1) hM S hS I hI C o
    exact ⟨O, hO, fun J hJ ξ =>
      hasPositiveIntegral_comparison hM S hS I hI C o O hO J hJ ξ⟩


end SmoothManifolds.EmbeddedIntegrationResults

namespace SmoothManifolds.EmbeddedIntegrationResults
open ModelData AtlasData TangentData DifferentialData BoundaryData
  BoundaryOrientationData BundleOperationsData ExteriorData
  FormPullbackData OrientationData
  EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model (IsEmbeddedManifold)
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace)
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.IntrinsicExteriorDerivative.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.GeneralizedStokes.Model

open EmbeddedIntegrationData

/-- Independent outward-first realizations retain the same signs, including
independent zero-dimensional boundary point signs. -/
theorem outwardFirst_unique {r : ℕ∞ω} {d N : ℕ} {M : Set (E N)}
    (o : PositiveManifoldOrientation r (d+1) M)
    {bO cO : ManifoldOrientation r d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary r (d+1) M)}
    (hb : OutwardFirst d o bO) (hc : OutwardFirst d o cO) : bO = cO := by
  cases d with
  | zero =>
    obtain ⟨ν, hνcont, hν, hb⟩ := hb
    obtain ⟨μ, hμcont, hμ, hc⟩ := hc
    have hνμ : ν = μ :=
      (D04BoundaryOrientation.continuous_conormal o.manifold).unique
        ⟨hνcont, hν⟩ ⟨hμcont, hμ⟩
    subst μ
    exact (D04BoundaryOrientation.boundary_point_sign o ν hν).unique hb hc
  | succ d =>
    obtain ⟨ν, hνcont, hν, hb⟩ := hb
    obtain ⟨μ, hμcont, hμ, hc⟩ := hc
    have hνμ : ν = μ :=
      (D04BoundaryOrientation.continuous_conormal o.manifold).unique
        ⟨hνcont, hν⟩ ⟨hμcont, hμ⟩
    subst μ
    exact (D04BoundaryOrientation.boundary_orientation o ν hν).unique hb hc

/-- Once the genuine bulk integral is identified with a value, D04's intrinsic
Stokes theorem uses that same value and any actual outward-first realization. -/
theorem intrinsic_stokes_at_value {d N : ℕ} {M : Set (E N)}
    (o : PositiveManifoldOrientation 2 (d+1) M)
    (ξ : IntrinsicForm (k := d+1) M d) (hξ : IntrinsicC1 ξ)
    (hcompact : IsCompact (formSupport ξ))
    (bO : ManifoldOrientation 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M))
    (hout : OutwardFirst d o bO) {v : ℝ}
    (hbulk : HasPositiveIntegral o (intrinsicExteriorDerivative ξ) v) :
    HasManifoldIntegral 2 d bO (boundaryRestriction ξ) v := by
  obtain ⟨cO, hcO, w, hwbulk, hwbdry⟩ := D04Stokes.intrinsic_stokes o ξ hξ hcompact
  have hbc : bO = cO := outwardFirst_unique o hout hcO
  have hwv : w = v := D04Stokes.positive_integral_unique o _ hwbulk hbulk
  simpa only [hbc, hwv] using hwbdry



/-- The actual D04 outward-first boundary orientation agrees with any natural
intrinsic realization q under the canonical boundary tangent identification. -/
theorem outwardFirst_orientation_transport
    {d N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hM : IsEmbeddedManifold ∞ (d+1) M)
    (S : SmoothManifold (d+1) a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (B : SmoothManifold d .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundary S B) (o : OrientationData.Orientation S)
    (q : OrientationData.Orientation B) (hq : IsInducedOrientation o q)
    (hb : ∀ p : intrinsicBoundary S, p.val.val ∈
      Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential B S Subtype.val p (L p))
    (K : (p : intrinsicBoundary S) → TangentSpace B p ≃ₗ[ℝ]
      tangentSpace 2 d
        (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val.val)
    (hK : ∀ p v, (K p v).val = (I p.val (L p v)).val) :
    ∃ O : PositiveManifoldOrientation 2 (d+1) M,
      (∀ (p : M) (b : Module.Basis (Fin (d+1)) ℝ (tangentSpace 2 (d+1) M p.val)),
        b.orientation = O.atPoint p.val p.property ↔
          IsPositive (o.val p) (exteriorPower.ιMulti ℝ (d+1) (fun j => (I p).symm (b j)))) ∧
      ∃ bO : ManifoldOrientation 2 d
          (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M),
        OutwardFirst d O bO ∧
        ∀ (p : intrinsicBoundary S) (b : Module.Basis (Fin d) ℝ
            (tangentSpace 2 d
              (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
              p.val.val)),
          D04PositiveBasis d
              (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
              bO ⟨p.val.val, hb p⟩ b ↔
            IsPositive (q.val p) (exteriorPower.ιMulti ℝ d (fun j => (K p).symm (b j))) := by
  cases d with
  | zero =>
    obtain ⟨O, hO, hrest⟩ :=
      EmbeddedBoundaryResults.boundary_point_comparison hM S hS I hI C o
    obtain ⟨hb', hrest⟩ := hrest B hB q hq
    obtain ⟨ν, hν, _⟩ := D04BoundaryOrientation.continuous_conormal O.manifold
    obtain ⟨s, hs, _⟩ := hrest ν hν.2
    refine ⟨O, hO, s, ⟨ν, hν.1, hν.2, hs.1⟩, ?_⟩
    intro p b
    have hz : exteriorPower.ιMulti ℝ 0 (fun j => (K p).symm (b j)) =
        (exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1 := by
      apply (exteriorPower.zeroEquiv ℝ (TangentSpace B p)).injective
      simp
    change (s ⟨p.val.val, hb p⟩).val = 1 ↔ _
    rw [hz]
    exact hs.2 p
  | succ d =>
    obtain ⟨O, hO, hrest⟩ :=
      EmbeddedBoundaryResults.boundary_orientation hM S hS I hI C o
    obtain ⟨hb', L', K', hL', hK', hrest⟩ := hrest B hB q hq
    obtain ⟨ν, hν, _⟩ := D04BoundaryOrientation.continuous_conormal O.manifold
    obtain ⟨bO, hbO, _⟩ := hrest ν hν.2
    have heL (p : intrinsicBoundary S) : L' p = L p :=
      (differential_exists B S Subtype.val hB.1 p).unique (hL' p) (hL p)
    have heK (p : intrinsicBoundary S) : K' p = K p := by
      apply LinearEquiv.ext
      intro v
      apply Subtype.ext
      exact (hK' p v).trans ((congrArg (fun z => (I p.val (z v)).val) (heL p)).trans (hK p v).symm)
    refine ⟨O, hO, bO, ⟨ν, hν.1, hν.2, hbO.1⟩, ?_⟩
    intro p b
    have hh := hbO.2 p b
    rw [heK p] at hh
    exact hh

end SmoothManifolds.EmbeddedIntegrationResults

namespace SmoothManifolds.EmbeddedIntegrationResults
open ModelData AtlasData TangentData DifferentialData BoundaryData
  BoundaryOrientationData BundleOperationsData ExteriorData ExteriorDerivativeData
  FormPullbackData OrientationData LocalIntegrationData GlobalIntegrationData
  EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace)
open Specs.D04.C14.EmbeddedManifoldCharts.Model (IsEmbeddedManifold)

/-- The accepted abstract Stokes identity, with its actual derivative and
boundary pullback transported to the fixed D04 C² tangent model. -/
theorem stokes_calculus_transport
    {d N : ℕ} {a : ModelKind} {M : Set (E N)}
    (hM : IsEmbeddedManifold ∞ (d+1) M)
    (S : SmoothManifold (d+1) a M) (hS : IsInducedSmoothStructure S)
    (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val)
    (hI : IsInclusionIdentification S I) (C : CotangentBundle S)
    (B : SmoothManifold d .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (hB : IsNaturalBoundary S B) (o : Orientation S) (q : Orientation B)
    (hq : IsInducedOrientation o q)
    (Jbulk : CompactTopForm S → ℝ) (Jbdry : CompactTopForm B → ℝ)
    (hJbulk : IsIntegral o Jbulk) (hJbdry : IsIntegral q Jbdry)
    (ξ : Field S d) (hξ : IsRegularField C 1 d ξ)
    (hc : IsCompact (sectionSupport ξ)) :
    ∃ (hb : ∀ p : intrinsicBoundary S, p.val.val ∈
        Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
      (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (K : (p : intrinsicBoundary S) → TangentSpace B p ≃ₗ[ℝ]
        tangentSpace 2 d
          (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val.val)
      (η : CompactTopForm S) (β : CompactTopForm B),
      (∀ p, IsDifferential B S Subtype.val p (L p)) ∧
      (∀ p v, (K p v).val = (I p.val (L p v)).val) ∧
      HasExteriorDerivative C ξ η.field ∧
      sectionSupport η.field ⊆ sectionSupport ξ ∧
      β.field = pullbackField B S Subtype.val L ξ ∧
      transportField S I (d+1) η.field =
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
          (transportField S I d ξ) ∧
      (∀ p : intrinsicBoundary S,
        transportCovector (K p) d (β.field p) =
          Specs.D04.C15.GeneralizedStokes.Model.boundaryRestriction
            (transportField S I d ξ) ⟨p.val.val, hb p⟩) ∧
      Jbulk η = Jbdry β := by
  obtain ⟨hb, L, hL, K, hK, _⟩ :=
    EmbeddedCompatibilityResults.boundary_restriction hM S hS I hI C B hB
  obtain ⟨η, β, hη, hηsupp, hβ, hval⟩ :=
    StokesResults.stokes S C B A hB o q hq L hL Jbulk Jbdry hJbulk hJbdry ξ hξ hc
  obtain ⟨δ, hδ, _⟩ :=
    EmbeddedCompatibilityResults.intrinsicExteriorDerivative_transport hM S hS I hI C d ξ hξ
  have hδη : η.field = δ :=
    ExteriorDerivativeResults.derivative_unique C d ξ η.field δ hη hδ.2.1
  refine ⟨hb, L, K, η, β, hL, hK.1, hη, hηsupp, hβ, ?_, ?_, hval⟩
  · rw [hδη]
    exact hδ.2.2
  · intro p
    rw [hβ]
    exact hK.2.2 ξ p

end SmoothManifolds.EmbeddedIntegrationResults

namespace SmoothManifolds.EmbeddedIntegrationResults
open ModelData AtlasData TangentData DifferentialData BoundaryData
  BoundaryOrientationData BundleOperationsData ExteriorData ExteriorDerivativeData
  FormPullbackData OrientationData LocalIntegrationData GlobalIntegrationData
  EmbeddedCalculusData EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace)
open Specs.D04.C14.EmbeddedManifoldCharts.Model (IsEmbeddedManifold)

open EmbeddedIntegrationData

/-- The original abstract Stokes identity becomes the literal intrinsic D04
identity under the actual tangent, orientation and integral comparisons. -/
theorem stokes_specialization :
    Specs.SmoothManifolds.Integration.EmbeddedCompatibility.stokes_specializationType := by
  intro d N a M hM S hS I hI C B A hB o q hq Jbulk Jbdry hJbulk hJbdry ξ hξ hc
  obtain ⟨hb, L, K, η, β, hL, hK, hη, hηsupp, hβ, hder, hbd, hval⟩ :=
    stokes_calculus_transport hM S hS I hI C B A hB o q hq Jbulk Jbdry
      hJbulk hJbdry ξ hξ hc
  obtain ⟨O, hO, bO, hout, hmatch⟩ :=
    outwardFirst_orientation_transport hM S hS I hI C B hB o q hq hb L hL K hK
  have hbulk := hasPositiveIntegral_comparison
    hM S hS I hI C o O hO Jbulk hJbulk η
  rw [hder] at hbulk
  have hξd := (EmbeddedCompatibilityResults.regularity_transport
    hM S hS I hI C d ξ).mp hξ
  have hcompact : IsCompact
      (Specs.D04.C15.GeneralizedStokes.Model.formSupport (transportField S I d ξ)) := by
    change IsCompact (ModelData.sectionSupport (transportField S I d ξ))
    rw [EmbeddedCompatibilityResults.support_identification S I d ξ]
    exact hc
  have hboundary := intrinsic_stokes_at_value
    O (transportField S I d ξ) hξd hcompact bO hout hbulk
  rw [hval] at hboundary
  exact ⟨hb, L, K, η, β, hL, hK, hη, hηsupp, hβ, hder, hbd, hval,
    O, hO, hbulk, bO, hout, hmatch, hboundary⟩


end SmoothManifolds.EmbeddedIntegrationResults

namespace SmoothManifolds.EmbeddedIntegrationResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  EmbeddedData EmbeddedCalculusData EmbeddedAtlasData BundleData BundleOperationsData
  BundleMetricData MetricVolumeData DensityIntegrationData FrameData LocalIntegrationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C06.JordanRegions.Model
open Set Filter
open scoped Classical ContDiff Topology BigOperators

variable {n N : ℕ} {a : ModelKind} {M : Set (E N)}
  (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
  (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
  (hI : IsInclusionIdentification S I)

private def inducedBilinear (p : M) : LinearMap.BilinForm ℝ (TangentSpace S p) :=
  (innerₗ (E N)).compl₁₂ ((tangentSpace 2 n M p.val).subtype.comp (I p).toLinearMap)
    ((tangentSpace 2 n M p.val).subtype.comp (I p).toLinearMap)

@[simp] theorem inducedBilinear_apply (p : M) (v z : TangentSpace S p) :
    inducedBilinear S I p v z = inner ℝ (I p v).val (I p z).val := rfl

include hS hI in
 theorem inclusion_coordinate_vector (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : euclideanChart N ∈ T.smoothStructure.val)
    (K : FiberCoordinates S) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (j : Fin n) :
    (I p ((K.equiv e he p hp).symm (Pi.single j 1))).val =
      (piCoordinates N).symm (FiniteRegularityData.chartDerivative e (euclideanChart N)
        (ambientInclusion M) p (Pi.single j 1)) := by
  have hj := EmbeddedAtlasResults.induced_fullRank S hS
  obtain ⟨hf, hex⟩ := embedded_differential_exists S (ambientInclusion M) hj T hT
  obtain ⟨L, F, hL, hF⟩ := hex p
  rw [hI T hT p L F hL hF]
  rw [FiniteRegularity.smooth_jacobian_coordinateDerivative S T (ambientInclusion M)
    hf p L hL e (euclideanChart N) he hT hp (mem_univ _)
    (K.equiv e he p hp) F (K.isCoordinates e he p hp) hF]
  rw [LinearEquiv.apply_symm_apply]

include hS hI in
 theorem inducedMetric_exists (C : CotangentBundle S) :
    ∃ g : Metric C, ∀ p v z, metricForm g p v z = inner ℝ (I p v).val (I p z).val := by
  letI := C.realization.space.topology
  let B := C.realization.space.bundle
  obtain ⟨T, hT⟩ := standardEuclidean_exists N
  have hj := EmbeddedAtlasResults.induced_fullRank S hS
  have hf := (embedded_differential_exists S (ambientInclusion M) hj T hT).1
  have hcoord (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
      (p : M) (hp : p ∈ e.source) (j : Fin n) :
      (B.trivialization ⟨e, he⟩).symm p (Pi.single j 1) =
        (C.tangent.fiberCoordinates.equiv e he p hp).symm (Pi.single j 1) := by
    have hb : p ∈ B.baseSet ⟨e, he⟩ := by rwa [C.realization.baseSet]
    have hE : B.fiberCoordinates ⟨e, he⟩ p hb =
        C.tangent.fiberCoordinates.equiv e he p hp := by
      apply LinearEquiv.ext
      intro v
      exact C.realization.coordinates ⟨e, he⟩ p hp v
    rw [← SmoothVectorBundle.fiberCoordinates_symm_apply B ⟨e, he⟩ p hb, hE]
  let g : Metric C := {
    form := inducedBilinear S I
    symmetric := by
      intro p v z
      change inner ℝ (I p v).val (I p z).val = inner ℝ (I p z).val (I p v).val
      exact real_inner_comm _ _
    positive := by
      intro p v hv
      change 0 < inner ℝ (I p v).val (I p v).val
      apply real_inner_self_pos.mpr
      intro hz
      apply hv
      apply (I p).injective
      apply Subtype.ext
      simpa using hz
    smooth := by
      rintro ⟨e, he⟩ j k p hp
      rw [C.realization.baseSet] at hp
      let A := FiniteRegularityData.chartDerivative e (euclideanChart N) (ambientInclusion M)
      let V (j : Fin n) (q : M) : E N := (piCoordinates N).symm (A q (Pi.single j 1))
      have hV (j : Fin n) : VectorSmoothAt S.smoothStructure.val (V j) p := by
        have hA := Tensors.chartDerivative_smoothAt S T (ambientInclusion M) hf e
          (euclideanChart N) he hT p hp (mem_univ _)
        exact (hA.clm_apply (VectorSmoothAt.const _ (Pi.single j 1) _)).postcomp
          (piCoordinates N).symm.contDiff
      have hs : VectorSmoothAt S.smoothStructure.val
          (fun q => inner ℝ (V j q) (V k q)) p :=
        ((hV j).prod (hV k)).postcomp (contDiff_fst.inner ℝ contDiff_snd)
      apply hs.congr
      filter_upwards [e.open_source.mem_nhds hp] with q hq
      rw [inducedBilinear_apply, hcoord e he q hq j, hcoord e he q hq k,
        inclusion_coordinate_vector S hS I hI T hT C.tangent.fiberCoordinates e he q hq j,
        inclusion_coordinate_vector S hS I hI T hT C.tangent.fiberCoordinates e he q hq k]
  }
  exact ⟨g, fun _ _ _ => rfl⟩

 theorem scalar_density_support (μ : DensityField S) (hμ : ∀ p, μ p ≠ 0)
    (ρ : M → ℝ) : sectionSupport (fun p => ρ p • μ p) = sectionSupport ρ := by
  change closure {p | ρ p • μ p ≠ 0} = closure {p | ρ p ≠ 0}
  congr 1
  ext p
  change ρ p • μ p ≠ 0 ↔ ρ p ≠ 0
  exact smul_ne_zero_iff_left (hμ p)

 private def compactScalarDensity (μ : DensityField S) (hμ : IsContinuousDensity μ)
    (ρ : M → ℝ) (hρ : Continuous ρ) (hc : IsCompact (sectionSupport ρ)) :
    CompactDensity S where
  field := fun p => ρ p • μ p
  continuous := by
    intro K e he
    exact ((hρ.comp continuous_subtype_val).mul (hμ K e he)).congr
      (fun p => (map_smul (densityCoefficient K e he p) _ _).symm)
  compact_support := hc.of_isClosed_subset isClosed_closure
    (fun p hp => (DensityIntegralResults.support_weight_subset ρ μ hp).1)

include hS hI in
 theorem induced_density_exists (C : CotangentBundle S) :
    ∃ (g : Metric C) (μ : DensityField S),
      (∀ p v z, metricForm g p v z = inner ℝ (I p v).val (I p z).val) ∧
      IsMetricDensity g μ ∧ IsSmoothDensity μ ∧ IsContinuousDensity μ ∧
      IsPositiveDensity μ ∧ (∀ p, μ p ≠ 0) ∧
      ∀ (ρ : M → ℝ), Continuous ρ → IsCompact (sectionSupport ρ) →
      ∃ σ : CompactDensity S, σ.field = (fun p => ρ p • μ p) ∧
        sectionSupport σ.field = sectionSupport ρ := by
  obtain ⟨g, hg⟩ := inducedMetric_exists S hS I hI C
  obtain ⟨μ, hμ, _⟩ := MetricVolumeResults.density_exists_unique S C g
  have hcont := DensityIntegrationResults.smooth_density_continuous μ hμ.2.1
  refine ⟨g, μ, hg, hμ.1, hμ.2.1, hcont, hμ.2.2.1, hμ.2.2.2.1, ?_⟩
  intro ρ hρ hc
  exact ⟨compactScalarDensity S μ hcont ρ hρ hc, rfl,
    scalar_density_support S μ hμ.2.2.2.1 ρ⟩

 theorem zero_scalar_integral (S₀ : SmoothManifold 0 a M) (C : CotangentBundle S₀)
    (g : Metric C) (μ : DensityField S₀) (hμ : IsMetricDensity g μ)
    (ρ : M → ℝ) (σ : CompactDensity S₀) (hσ : σ.field = fun p => ρ p • μ p)
    (J : CompactDensity S₀ → ℝ) (hJ : IsDensityIntegral J) :
    J σ = ∑ᶠ p : M, ρ p := by
  classical
  have hz (p : M) : DensityIntegrationData.zeroCoefficient σ.field p = ρ p := by
    unfold DensityIntegrationData.zeroCoefficient
    rw [hσ]
    change ρ p * (μ p).val _ = ρ p
    rw [hμ, MetricVolumeResults.zero_norm]
    exact mul_one _
  obtain ⟨h, hv⟩ := DensityIntegralResults.zero_finite_sum S₀ J hJ σ
  rw [hv]
  have hs : Function.support ρ ⊆ (h.toFinset : Set M) := by
    intro p hp
    apply h.mem_toFinset.mpr
    apply subset_closure
    intro hp₀
    apply hp
    exact (hz p).symm.trans (by simp [DensityIntegrationData.zeroCoefficient, hp₀])
  calc
    _ = ∑ p ∈ h.toFinset, ρ p := Finset.sum_congr rfl (fun p _ => hz p)
    _ = ∑ᶠ p : M, ρ p := (finsum_eq_finsetSum_of_support_subset ρ hs).symm

 theorem zero_density_comparison (S₀ : SmoothManifold 0 a M) (C : CotangentBundle S₀)
    (g : Metric C) (μ : DensityField S₀) (hμ : IsMetricDensity g μ)
    (ρ : M → ℝ) (hc : HasCompactSupport ρ) (σ : CompactDensity S₀)
    (hσ : σ.field = fun p => ρ p • μ p)
    (J : CompactDensity S₀ → ℝ) (hJ : IsDensityIntegral J)
    (hM : Specs.D04.C14.EmbeddedManifoldCharts.Model.IsEmbeddedManifold 2 0 M)
    (P : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition 2 0 M
      (tsupport ρ)) :
    J σ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral ρ P := by
  rw [zero_scalar_integral S₀ C g μ hμ ρ σ hσ J hJ,
    D04.ManifoldIntegralIndependence.density_zero_sum hM ρ hc P]

end SmoothManifolds.EmbeddedIntegrationResults

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
namespace SmoothManifolds.EmbeddedIntegrationResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  EmbeddedData EmbeddedCalculusData EmbeddedAtlasData BundleData BundleOperationsData
  BundleMetricData MetricVolumeData DensityIntegrationData FrameData LocalIntegrationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C06.JordanRegions.Model
open Set Filter
open scoped Classical ContDiff Topology BigOperators

variable {n N : ℕ} {a : ModelKind} {M : Set (E N)}
  (S : SmoothManifold n a M) (hS : IsInducedSmoothStructure S)
  (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val)
  (hI : IsInclusionIdentification S I)

include hS hI in
 theorem density_integral_comparison (hM : IsEmbeddedManifold ∞ n M)
    (C : CotangentBundle S) (g : Metric C)
    (hg : ∀ p v z, metricForm g p v z = inner ℝ (I p v).val (I p z).val)
    (μ : DensityField S) (hμ : IsMetricDensity g μ)
    (ρ : M → ℝ) (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (σ : CompactDensity S) (hσ : σ.field = fun p => ρ p • μ p)
    (J : CompactDensity S → ℝ) (hJ : IsDensityIntegral J)
    (P : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition 2 n M
      (tsupport ρ)) :
    J σ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral ρ P := by
  classical
  let K := C.tangent.fiberCoordinates
  have hM₂ := (EmbeddedAtlasResults.smooth_c2_tangents hM).1
  obtain ⟨m, e, he, c, w, hm, hcover, hw⟩ :=
    exists_matching_partition hM S hS (tsupport ρ) hc
  let c₂ : Fin m → EmbeddedChart 2 n N M := fun i => lowerChart (c i) (by simp)
  let Q : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition 2 n M
      (tsupport ρ) := {
    count := m
    chart := c₂
    weight := w
    partition := ⟨hw.1, hw.2.1, fun i => ⟨(hw.2.2.1 i).1, fun p hp =>
      (hm i p ((hw.2.2.1 i).2 hp)).1⟩, hw.2.2.2⟩ }
  have hcont (i : Fin m) : Continuous (fun p : M => w i p.val) :=
    (hw.1 i).continuous.comp continuous_subtype_val
  let τ : Fin m → CompactDensity S := fun i =>
    DensityIntegralResults.compactWeight (fun p : M => w i p.val) (hcont i) σ
  have hs (i : Fin m) : sectionSupport (τ i).field ⊆ (e i).source := by
    intro p hp
    exact (hw.2.2.1 i).2
      (DensityIntegralResults.support_weight_subset (fun p : M => w i p.val) σ.field hp).1
  have hsum : σ.field = ∑ i, (τ i).field := by
    funext p
    simp only [Finset.sum_apply]
    change σ.field p = ∑ i, w i p.val • σ.field p
    by_cases hp : p ∈ tsupport ρ
    · obtain ⟨V, hV, hKV, hsum⟩ := hw.2.2.2.1
      calc
        σ.field p = (1 : ℝ) • σ.field p := (one_smul ℝ _).symm
        _ = (∑ i : Fin m, w i p.val) • σ.field p :=
          (congrArg (fun t : ℝ => t • σ.field p) (hsum p (hKV hp))).symm
        _ = ∑ i : Fin m, w i p.val • σ.field p :=
          Finset.sum_smul (s := Finset.univ) (f := fun i : Fin m => w i p.val)
            (x := σ.field p)
    · have hzero : ρ p = 0 := not_not.mp (fun h => hp (subset_tsupport ρ h))
      simp [hσ, hzero]
  rw [DensityIntegralResults.finite_localization S J hJ m σ τ K e he hs hsum]
  have hlocal (i : Fin m) : DensityIntegrationData.coordinateIntegral K (e i) (he i) (τ i).field =
      coefficientIntegral
        (Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.localizedDensityCoefficient
          ρ (c₂ i) (w i)) := by
    have hproper := (D04.ManifoldIntegral.density_coefficients_integrable hM₂ ρ hρ Q i).2.2
    rw [EmbeddedIntegrationResults.proper_integral_pi_bridge _ hproper]
    unfold DensityIntegrationData.coordinateIntegral
    congr 1
    funext x
    apply matching_chart_zeroExtension (e i) (c i) (hm i) (hcover i)
      (fun p => densityCoefficient K (e i) (he i) p ((τ i).field p.val)) _ ?_ x
    intro z hz
    let p : M := ⟨(c i).toFun z, ((c i).map_source hz).1⟩
    change densityCoefficient K (e i) (he i) ⟨p, hcover i z hz⟩
      ((w i p.val) • σ.field p) = _
    rw [hσ, map_smul]
    exact (EmbeddedIntegrationResults.matching_density_coefficient S hS I hI C g hg μ hμ
      (e i) (he i) (c i) (hm i) ρ (w i) ⟨z, hz⟩ (hcover i z hz)).2
  calc
    _ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral ρ Q :=
      Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = _ := D04.ManifoldIntegralIndependence.density_independent hM₂ ρ hρ Q P

include hS hI in
 theorem density_comparison (hM : IsEmbeddedManifold ∞ n M)
    (C : CotangentBundle S) :
    ∃ (g : Metric C) (μ : DensityField S),
      (∀ p v z, metricForm g p v z = inner ℝ (I p v).val (I p z).val) ∧
      IsMetricDensity g μ ∧ IsSmoothDensity μ ∧ IsContinuousDensity μ ∧
      IsPositiveDensity μ ∧ (∀ p, μ p ≠ 0) ∧
      ∀ (ρ : M → ℝ), Continuous ρ → HasCompactSupport ρ →
      ∃ σ : CompactDensity S, σ.field = (fun p => ρ p • μ p) ∧
        sectionSupport σ.field = tsupport ρ ∧
        ∀ (J : CompactDensity S → ℝ), IsDensityIntegral J →
        ∀ P : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.ChartPartition 2 n M
          (tsupport ρ),
          J σ = Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.densityIntegral ρ P := by
  obtain ⟨g, μ, hg, hmetric, hsmooth, hcont, hpos, hneq, hsections⟩ :=
    induced_density_exists S hS I hI C
  refine ⟨g, μ, hg, hmetric, hsmooth, hcont, hpos, hneq, ?_⟩
  intro ρ hρ hc
  obtain ⟨σ, hσ, hsupport⟩ := hsections ρ hρ hc
  refine ⟨σ, hσ, hsupport, ?_⟩
  intro J hJ P
  exact density_integral_comparison S hS I hI hM C g hg μ hmetric ρ hρ hc σ hσ J hJ P

end SmoothManifolds.EmbeddedIntegrationResults
