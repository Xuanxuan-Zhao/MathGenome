import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.RegularDomainRiemannManifoldBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C12.RegularDomainGeometryAndJordanMeasurability
import MathGenome.Internal.MultivariableAnalysis.D04.C15.ManifoldIntegralIndependence

noncomputable section
set_option maxHeartbeats 1200000
open Set Function Topology
open scoped ContDiff BigOperators
namespace D04.RegularDomainBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge

abbrev volumeField := @Model.volumeField
abbrev IsAmbientOrientation := @Model.IsAmbientOrientation

/-- This is a calculation on the actual tangent restriction, not a new
coordinate representation of the integral. -/
theorem volume_coefficient : volume_coefficientType := by
  intro n M f c u
  change f (chartPoint c u) *
    omega n (fun i => chartDifferential c u (standardBasis n i)) = _
  change f (chartPoint c u) *
    (standardBasis n).det ((chartDifferential c u).toLinearMap ∘ standardBasis n) = _
  rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]

theorem volume_field_continuous : volume_field_continuousType := by
  intro n M f hf c
  have hd : Continuous (fun u : c.source => (chartDifferential c u).det) :=
    ContinuousLinearMap.continuous_det.comp
      (D04MetricDensity.chartDifferential_continuous c RegularDomainGeometry.regularity_one).domRestrict
  have hc := (hf.comp (ManifoldIntegral.chartPoint_continuous c)).mul hd
  exact hc.congr (fun u => (volume_coefficient f c u).symm)

/-- Every full-dimensional tangent space equals the entire ambient vector space. -/
lemma tangentSpace_eq_top {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (x : M) : tangentSpace 1 n M x = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  simpa using D04.tangentSpace_finrank hM x x.property

/-- The actual restricted volume covector never vanishes on a full-dimensional
embedded manifold. -/
lemma restricted_volume_ne_zero {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (x : M) :
    (omega n).compLinearMap (tangentSpace 1 n M x).subtype ≠ 0 := by
  let v : Fin n → tangentSpace 1 n M x := fun i =>
    ⟨standardBasis n i, by rw [tangentSpace_eq_top hM x]; trivial⟩
  intro hz
  have hh := congrArg (fun q : Covector (tangentSpace 1 n M x) n => q v) hz
  change (standardBasis n).det (standardBasis n) = 0 at hh
  exact one_ne_zero ((Module.Basis.det_self (standardBasis n)).symm.trans hh)

/-- A convenient orientation field defined by the restricted ambient covector. -/
def ambientOrientationField {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) : TangentOrientationField 1 n M :=
  fun x hx => rayOfNeZero ℝ ((omega n).compLinearMap (tangentSpace 1 n M x).subtype)
    (restricted_volume_ne_zero hM ⟨x, hx⟩)

/-- Changing from an orientation's chosen representative to its defining
nonzero covector preserves every evaluation sign. -/
lemma ray_evaluation_sign {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (q : Covector V n) (hq : q ≠ 0) (v : Fin n → V) :
    Real.sign ((rayOfNeZero ℝ q hq).someVector v) = Real.sign (q v) := by
  let o := rayOfNeZero ℝ q hq
  have hr : SameRay ℝ o.someVector q :=
    (ray_eq_iff o.someVector_ne_zero hq).mp (Module.Ray.someVector_ray o)
  obtain ⟨a, b, ha, hb, he⟩ := hr.exists_pos o.someVector_ne_zero hq
  have hev : a * o.someVector v = b * q v := by
    exact congrArg (fun z : Covector V n => z v) he
  have hh := congrArg Real.sign hev
  simpa only [D04.Orientations.sign_mul, Real.sign_of_pos ha,
    Real.sign_of_pos hb, one_mul] using hh

lemma ambientOrientationField_chart_sign {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (c : EmbeddedChart 1 n n M) (u : c.source) :
    chartSign (ambientOrientationField hM) c u u.property =
      Real.sign ((chartDifferential c u).det) := by
  change Real.sign ((ambientOrientationField hM _ _).someVector _) = _
  dsimp only [ambientOrientationField]
  rw [ray_evaluation_sign]
  change Real.sign ((standardBasis n).det
    ((chartDifferential c u).toLinearMap ∘ standardBasis n)) = _
  rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]

/-- The ambient orientation as an object of the shared manifold interface. -/
def ambientOrientation {n : ℕ} {M : Set (E n)}
    (hn : 0 < n) (hM : IsEmbeddedManifold 1 n M) : PositiveManifoldOrientation 1 n M where
  positive_dimension := hn
  manifold := hM
  atPoint := ambientOrientationField hM
  locally_constant := by
    intro c
    have hd : Continuous (fun u : c.source => (chartDifferential c u).det) :=
      ContinuousLinearMap.continuous_det.comp
        (D04MetricDensity.chartDifferential_continuous c hM.1).domRestrict
    have hnz : ∀ u : c.source, (chartDifferential c u).det ≠ 0 := by
      intro u
      exact (LinearEquiv.ofInjectiveEndo (chartDifferential c u).toLinearMap
        (D04.EmbeddedChart.differential_injective c hM.1 u.property)).isUnit_det'.ne_zero
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro u
    have heq : ∀ v : c.source, chartSign (ambientOrientationField hM) c v v.property =
        Real.sign ((chartDifferential c v).det) := ambientOrientationField_chart_sign hM c
    rcases lt_or_gt_of_ne (hnz u) with hu | hu
    · have he := hd.continuousAt.eventually (gt_mem_nhds hu)
      filter_upwards [he] with v hv
      rw [heq v, heq u, Real.sign_of_neg hv, Real.sign_of_neg hu]
    · have he := hd.continuousAt.eventually (lt_mem_nhds hu)
      filter_upwards [he] with v hv
      rw [heq v, heq u, Real.sign_of_pos hv, Real.sign_of_pos hu]

/-- Positivity of the actual ambient covector identifies the orientation. -/
lemma ambientOrientation_spec {n : ℕ} {M : Set (E n)}
    (hn : 0 < n) (hM : IsEmbeddedManifold 1 n M) :
    IsAmbientOrientation (ambientOrientation hn hM) := by
  intro x b
  change b.orientation = ambientOrientationField hM x x.property ↔ _
  rw [← D04.Orientations.representative_pos_iff]
  rw [← D04.Orientations.sign_eq_one_iff]
  dsimp only [ambientOrientationField]
  rw [ray_evaluation_sign, D04.Orientations.sign_eq_one_iff]
  rfl

theorem ambient_orientation_exists : ambient_orientation_existsType := by
  intro n M hn hM
  exact ⟨ambientOrientation hn hM, ambientOrientation_spec hn hM⟩

theorem ambient_chart_sign : ambient_chart_signType := by
  intro n M o ho c u
  let b := D04.Orientations.chartBasis c o.manifold.1 le_rfl u u.property
  have hb : ∀ i, (b i).val = chartDifferential c u (standardBasis n i) := fun _ => rfl
  have hpos : chartSign o.atPoint c u u.property = 1 ↔
      0 < (chartDifferential c u).det := by
    calc
      chartSign o.atPoint c u u.property = 1 ↔
          b.orientation = o.atPoint (c.toFun u) (c.map_source u.property).1 :=
        D04.Orientations.chartSign_basis o.atPoint c u u.property b hb
      _ ↔ 0 < omega n (fun i => (b i).val) := ho (chartPoint c u) b
      _ ↔ 0 < (chartDifferential c u).det := by
        change 0 < (standardBasis n).det
          ((chartDifferential c u).toLinearMap ∘ standardBasis n) ↔ _
        rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  have hnz : (chartDifferential c u).det ≠ 0 :=
    (LinearEquiv.ofInjectiveEndo (chartDifferential c u).toLinearMap
      (D04.EmbeddedChart.differential_injective c o.manifold.1 u.property)).isUnit_det'.ne_zero
  rcases D04.Orientations.chartSign_values o.atPoint c o.manifold.1 le_rfl u u.property with hs | hs
  · rw [hs, Real.sign_of_pos (hpos.mp hs)]
  · have hnp : ¬ 0 < (chartDifferential c u).det := by
      intro hp
      have := hpos.mpr hp
      linarith
    rw [hs, Real.sign_of_neg (lt_of_le_of_ne (not_lt.mp hnp) hnz)]

theorem signed_volume_coefficient : signed_volume_coefficientType := by
  intro n M o ho f L P i u
  change (P.sign i).val * (P.weight i ((P.chart i).toFun u) *
    topCoefficient (volumeField f) (P.chart i) u) = _
  rw [← P.agrees i u, ambient_chart_sign o ho, volume_coefficient]
  rw [show Real.sign ((chartDifferential (P.chart i) u).det) *
      (P.weight i ((P.chart i).toFun u) *
        (f (chartPoint (P.chart i) u) * (chartDifferential (P.chart i) u).det)) =
      P.weight i ((P.chart i).toFun u) * f (chartPoint (P.chart i) u) *
        (Real.sign ((chartDifferential (P.chart i) u).det) *
          (chartDifferential (P.chart i) u).det) by ring,
    D04.ManifoldIntegralIndependence.sign_mul_value]

/-- The top support is exactly the scalar support, since the ambient volume
covector is nonzero on every tangent space. -/
lemma volume_topSupport {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (f : M → ℝ) :
    topSupport (volumeField f) = tsupport f := by
  change closure {x | volumeField f x ≠ 0} = closure (support f)
  congr 1
  ext x
  change f x • (omega n).compLinearMap (tangentSpace 1 n M x).subtype ≠ 0 ↔ f x ≠ 0
  exact smul_ne_zero_iff_left (restricted_volume_ne_zero hM x)

/-- Compactness provides precisely the compact support required by the
manifold integral, including when f is nonzero on the entire boundary. -/
lemma volume_support_compact {n : ℕ} {D : Set (E n)}
    (hD : IsClassicalRegularDomain D) (f : closure D → ℝ) :
    IsCompact (topSupport (volumeField f)) := by
  letI : CompactSpace (closure D) :=
    isCompact_iff_compactSpace.mp (RegularDomainGeometry.closure_manifold hD).1
  exact (isClosed_closure : IsClosed (topSupport (volumeField f))).isCompact

/-- All non-integral data and both ordinary Riemann integrals are available
without an assumed equivalence with the manifold integral. -/
lemma regular_domain_data {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) :
    ∃ o : PositiveManifoldOrientation 1 (d+1) (closure D),
      IsAmbientOrientation o ∧ IsCompact (closure D) ∧
      intrinsicBoundary 1 (d+1) (closure D) = frontier D ∧
      Jordan D ∧ Jordan (closure D) ∧
      (∀ p : frontier D,
        IsOutwardUnitConormal 1 d (closure D) p (outwardNormal hD p)) ∧
      ∀ (f : closure D → ℝ), Continuous f →
        ContinuousTopField (volumeField f) ∧ IsCompact (topSupport (volumeField f)) ∧
        Nonempty (SignedChartPartition o (topSupport (volumeField f))) ∧
        RegionIntegrable f ∧
        RegionIntegrable (fun x : D => f ⟨x, subset_closure x.property⟩) ∧
        regionIntegral f = regionIntegral (fun x : D => f ⟨x, subset_closure x.property⟩) := by
  obtain ⟨hK, hM⟩ := RegularDomainGeometry.closure_manifold hD
  obtain ⟨o, ho⟩ := ambient_orientation_exists hD.dimension hM
  obtain ⟨hJD, hJK⟩ := RegularDomainGeometry.jordan_domain_and_closure hD
  refine ⟨o, ho, hK, RegularDomainGeometry.intrinsic_boundary hD, hJD, hJK,
    RegularDomainGeometry.outward_normal_conormal hD, ?_⟩
  intro f hf
  obtain ⟨hiK, hiD, heq⟩ := RegularDomainGeometry.continuous_integral hD f hf
  have hη := volume_field_continuous f hf
  have hkη := volume_support_compact hD f
  exact ⟨hη, hkη, ManifoldIntegral.signed_partition_exists o _ hkη, hiK, hiD, heq⟩

/-- Absolute-Jacobian substitution for a full-dimensional chart which is the
restriction of an ambient diffeomorphism. Its coefficient is zero-extended
across the genuine boundary, so no continuity of that extension is assumed. -/
lemma chart_absolute_substitution {n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 n n M) (e : OpenPartialHomeomorph (E n) (E n))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hcs : c.source ⊆ e.source) (hca : c.ambient = e.target)
    (hce : EqOn c.toFun e c.source)
    (hde : ∀ u ∈ c.source, chartDifferential c u = fderiv ℝ e u)
    (f : M → ℝ) (hi : RegionIntegrable f) (hk : HasCompactSupport f)
    (hs : tsupport f ⊆ Subtype.val ⁻¹' c.ambient) :
    coefficientIntegral (fun u : c.source =>
      f (chartPoint c u) * |(chartDifferential c u).det|) = regionIntegral f := by
  classical
  let F : e.target → ℝ := fun y => zeroExtension f y
  have ht : tsupport (zeroExtension f) ⊆ e.target := by
    rw [D04.Localization.zeroExtension_tsupport hk]
    rintro y ⟨x, hx, rfl⟩
    exact hca ▸ hs hx
  have hFz : zeroExtension F = zeroExtension f := by
    funext y
    by_cases hy : y ∈ e.target
    · exact D04.JordanRegions.zeroExtension_apply F ⟨y, hy⟩
    · rw [show zeroExtension F y = 0 from D04.JordanRegions.zeroExtension_of_not_mem F hy]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hy (ht h))).symm
  have hFk : HasCompactSupport F := D04.RiemannSubstitution.compact_restrict
    (D04.Localization.zeroExtension_compact hk) ht
  have hFb : RegionBounded F := D04.DirectedSubstitution.extension_regionBounded hi.1
  have hFi : OpenIntegrable F := by
    obtain ⟨Q, hQ, hiQ⟩ := hi.2
    refine ⟨e.open_target, ?_, Q, ?_, ?_⟩
    · rw [hFz]
      exact (D04.Localization.zeroExtension_compact hk).isCompact.isBounded.subset
        (subset_tsupport _)
    · rw [hFz]
      exact (closure_mono (D04.RegionSubstitution.support_zeroExtension_subset f)).trans hQ
    · rwa [hFz]
  let p : e.source → ℝ := fun x => F ⟨e x, e.map_source x.property⟩ * |(fderiv ℝ e x).det|
  have hsub := D04.RiemannSubstitution.riemann_substitution e.toHomeomorphSourceTarget
    e e.symm e.open_source e.open_target he hei (fun _ => rfl) (fun _ => rfl) F hFb hFk
  have hpval : openIntegral F = openIntegral p := hsub.2.2.2.2.2 (Or.inl hFi)
  let g : c.source → ℝ := fun u => f (chartPoint c u) * |(chartDifferential c u).det|
  have hsource {x : E n} (hx : x ∈ e.source) (hm : e x ∈ M) : x ∈ c.source := by
    have hy : e x ∈ M ∩ c.ambient := ⟨hm, hca ▸ e.map_source hx⟩
    have hv := c.map_target hy
    have hev : e (c.invFun (e x)) = e x :=
      (hce hv).symm.trans (c.right_inv _ hy)
    have hxe : c.invFun (e x) = x := e.injOn (hcs hv) hx hev
    exact hxe ▸ hv
  have hext : zeroExtension g = zeroExtension p := by
    funext x
    by_cases hx : x ∈ c.source
    · rw [show zeroExtension g x = g ⟨x, hx⟩ from D04.JordanRegions.zeroExtension_apply g ⟨x, hx⟩,
        show zeroExtension p x = p ⟨x, hcs hx⟩ from D04.JordanRegions.zeroExtension_apply p ⟨x, hcs hx⟩]
      have hv : e x = c.toFun x := (hce hx).symm
      change f (chartPoint c ⟨x, hx⟩) * |(chartDifferential c x).det| =
        zeroExtension f (e x) * |(fderiv ℝ e x).det|
      rw [hde x hx, hv]
      congr 1
      exact (D04.JordanRegions.zeroExtension_apply f (chartPoint c ⟨x, hx⟩)).symm
    · rw [show zeroExtension g x = 0 from D04.JordanRegions.zeroExtension_of_not_mem g hx]
      by_cases hxe : x ∈ e.source
      · rw [show zeroExtension p x = p ⟨x, hxe⟩ from D04.JordanRegions.zeroExtension_apply p ⟨x, hxe⟩]
        have hm : e x ∉ M := fun hm => hx (hsource hxe hm)
        change 0 = zeroExtension f (e x) * _
        rw [show zeroExtension f (e x) = 0 from D04.JordanRegions.zeroExtension_of_not_mem f hm, zero_mul]
      · exact (D04.JordanRegions.zeroExtension_of_not_mem p hxe).symm
  exact (D04.DirectedSubstitution.proper_congr hext).2.trans
    (hpval.symm.trans (D04.OneCoordinate.open_eq_region F f hFi hi hFz))

/-- A chart together with its proved ambient inverse-function extension. -/
structure AmbientChart {n : ℕ} (M : Set (E n)) where
  chart : EmbeddedChart 1 n n M
  extension : OpenPartialHomeomorph (E n) (E n)
  regular : ContDiffOn ℝ 1 extension extension.source
  inverse_regular : ContDiffOn ℝ 1 extension.symm extension.target
  source_subset : chart.source ⊆ extension.source
  ambient_eq : chart.ambient = extension.target
  agrees : EqOn chart.toFun extension chart.source
  differential : ∀ u ∈ chart.source, chartDifferential chart u = fderiv ℝ extension u

lemma ambient_chart_at {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (x : closure D) :
    ∃ C : AmbientChart (closure D), (x : E (d+1)) ∈ C.chart.ambient := by
  by_cases hx : (x : E (d+1)) ∈ D
  · let c := RegularDomainGeometry.interiorChart hD.isOpen
    let e := OpenPartialHomeomorph.ofSet D hD.isOpen
    refine ⟨⟨c, e, contDiff_id.contDiffOn, contDiff_id.contDiffOn,
      Subset.rfl, rfl, fun _ _ => rfl, ?_⟩, hx⟩
    intro u hu
    exact D04.chartDifferential_extension c RegularDomainGeometry.regularity_one u hu
      univ id isOpen_univ (mem_univ _) (fun _ _ => rfl) differentiableAt_id
  · have hxb : (x : E (d+1)) ∈ frontier D := by
      rw [frontier, hD.isOpen.interior_eq]
      exact ⟨x.property, hx⟩
    obtain ⟨U, ρ, hxU, hρ⟩ := hD.defining x hxb
    obtain ⟨C⟩ := RegularDomainGeometry.boundary_coordinates hρ ⟨hxb, hxU⟩
    obtain ⟨hX, hY, hpX, hFpY, hXU, hbij, hgmap, hleft, hright,
      hDF, hDg, hLip, huniq⟩ := C.inverse
    let e : OpenPartialHomeomorph (E (d+1)) (E (d+1)) := {
      toFun := C.g
      invFun := C.F
      source := C.Y
      target := C.X
      map_source' := hgmap
      map_target' := hbij.mapsTo
      left_inv' := hright
      right_inv' := hleft
      open_source := hY
      open_target := hX
      continuousOn_toFun := C.backward_regular.continuousOn
      continuousOn_invFun := C.forward_regular.continuousOn }
    let c := C.chart hD.isOpen hρ
    refine ⟨⟨c, e, C.backward_regular, C.forward_regular,
      inter_subset_right, rfl, fun _ _ => rfl, ?_⟩, hpX⟩
    intro u hu
    exact D04.chartDifferential_extension c RegularDomainGeometry.regularity_one u hu
      C.Y C.g hY hu.2 (fun _ _ => rfl)
      ((C.backward_regular.contDiffAt (hY.mem_nhds hu.2)).differentiableAt one_ne_zero)

/-- Finite linearity on a bounded region, proved on a common enclosing box. -/
lemma region_integral_sum {n m : ℕ} {M : Set (E n)}
    (hM : Bornology.IsBounded M) (f : Fin m → M → ℝ)
    (hf : ∀ i, RegionIntegrable (f i)) (g : M → ℝ) (hg : RegionIntegrable g)
    (heq : ∀ x, g x = ∑ i, f i x) : regionIntegral g = ∑ i, regionIntegral (f i) := by
  classical
  let Q := enclosingBox M
  have hQ : Encloses M Q := D04.JordanRegions.enclosingBox_encloses hM
  have hi i := (D04.JordanRegions.region_integrable_iff_box (f i) hQ).mp (hf i)
  have hig := (D04.JordanRegions.region_integrable_iff_box g hQ).mp hg
  have hz : zeroExtension g = fun x => ∑ i, zeroExtension (f i) x := by
    funext x
    by_cases hx : x ∈ M
    · calc
        zeroExtension g x = g ⟨x, hx⟩ := D04.JordanRegions.zeroExtension_apply g ⟨x, hx⟩
        _ = ∑ i, f i ⟨x, hx⟩ := heq _
        _ = ∑ i, zeroExtension (f i) x := by
          apply Finset.sum_congr rfl
          intro i _
          exact (D04.JordanRegions.zeroExtension_apply (f i) ⟨x, hx⟩).symm
    · have hzg : zeroExtension g x = 0 := D04.JordanRegions.zeroExtension_of_not_mem g hx
      rw [hzg]
      exact (Finset.sum_eq_zero (fun i _ => D04.JordanRegions.zeroExtension_of_not_mem (f i) hx)).symm
  rw [show regionIntegral g = D04.Darboux.integral (zeroExtension g) Q hig from
    D04.JordanRegions.integral_eq_on_enclosing_box g hg hQ hig]
  have his : D04.Darboux.Integrable (fun x => ∑ i, zeroExtension (f i) x) Q := hz ▸ hig
  have hv := D04.Darboux.integral_sum Finset.univ (fun i => zeroExtension (f i))
    (fun i _ => hi i) his
  change D04.Darboux.lowerIntegral _ Q = _ at hv ⊢
  rw [hz]
  exact hv.trans (Finset.sum_congr rfl (fun i _ => by
    simpa only [Finset.mem_univ, dite_eq_left] using
      (D04.JordanRegions.integral_eq_on_enclosing_box (f i) (hf i) hQ (hi i)).symm))

/-- The global compact partition can be chosen in charts with proved ambient
extensions, including the half-space charts at the boundary. -/
lemma ambient_partition {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) :
    ∃ (Q : ChartPartition 1 (d+1) (closure D) univ)
      (C : Fin Q.count → AmbientChart (closure D)), ∀ i, (C i).chart = Q.chart i := by
  classical
  obtain ⟨hK, hM⟩ := RegularDomainGeometry.closure_manifold hD
  letI : CompactSpace (closure D) := isCompact_iff_compactSpace.mp hK
  choose C hC using fun p : (univ : Set (closure D)) => ambient_chart_at hD p.val
  obtain ⟨m, a, p, w, hw, hs⟩ := D04.FiniteCompactPartition.finite_partition_refined
    hM univ isCompact_univ (fun _ : Unit => (univ : Set (closure D)))
    (fun _ => isOpen_univ) (by intro x hx; exact mem_iUnion.mpr ⟨(), mem_univ _⟩)
    (fun p => (C p).chart) hC (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  let Q : ChartPartition 1 (d+1) (closure D) univ := ⟨m, fun i => (C (p i)).chart,
    w, hw.1, hw.2.1, fun i => ⟨(hw.2.2.1 i).1, fun x hx => (hs i hx).2⟩,
    hw.2.2.2⟩
  exact ⟨Q, fun i => C (p i), fun _ => rfl⟩

lemma signedCoefficient_volume {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 n M) (ho : IsAmbientOrientation o)
    (f : M → ℝ) (c : EmbeddedChart 1 n n M) (u : c.source) :
    D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f) c u =
      f (chartPoint c u) * |(chartDifferential c u).det| := by
  change chartSign o.atPoint c u u.property * topCoefficient (volumeField f) c u = _
  rw [ambient_chart_sign o ho, volume_coefficient]
  calc
    _ = f (chartPoint c u) * (Real.sign ((chartDifferential c u).det) *
      (chartDifferential c u).det) := by ring
    _ = _ := by rw [D04.ManifoldIntegralIndependence.sign_mul_value]

/-- The actual signed manifold integral agrees with the bounded-region
Darboux integral, for every admitted partition. -/
lemma manifold_integral_eq_region {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D)
    (o : PositiveManifoldOrientation 1 (d+1) (closure D)) (ho : IsAmbientOrientation o)
    (f : closure D → ℝ) (hf : Continuous f)
    (P : SignedChartPartition o (topSupport (volumeField f))) :
    orientedIntegral (volumeField f) P = regionIntegral f := by
  classical
  obtain ⟨Q, C, hC⟩ := ambient_partition hD
  have hη := volume_field_continuous f hf
  have hc : ∀ i, Continuous (fun x : closure D => Q.weight i x * f x) :=
    fun i => ((Q.partition.1 i).continuous.comp continuous_subtype_val).mul hf
  have hi : ∀ i, RegionIntegrable (fun x : closure D => Q.weight i x * f x) :=
    fun i => (RegularDomainGeometry.continuous_integral hD _ (hc i)).1
  have hfi := (RegularDomainGeometry.continuous_integral hD f hf).1
  have hv i : coefficientIntegral
      (D04.ManifoldIntegralIndependence.weightedCoefficient
        (D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f))
        (Q.chart i) (Q.weight i)) =
      regionIntegral (fun x : closure D => Q.weight i x * f x) := by
    have hs : tsupport (fun x : closure D => Q.weight i x * f x) ⊆
        Subtype.val ⁻¹' (C i).chart.ambient := by
      rw [hC i]
      exact tsupport_mul_subset_left.trans (Q.partition.2.2.1 i).2
    have hk : HasCompactSupport (fun x : closure D => Q.weight i x * f x) :=
      (Q.partition.2.2.1 i).1.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
    rw [← hC i]
    have heq : D04.ManifoldIntegralIndependence.weightedCoefficient
        (D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f))
        (C i).chart (Q.weight i) =
        fun u : (C i).chart.source =>
          (Q.weight i (chartPoint (C i).chart u) * f (chartPoint (C i).chart u)) *
            |(chartDifferential (C i).chart u).det| := by
      funext u
      change Q.weight i ((C i).chart.toFun u) *
        D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f) (C i).chart u = _
      rw [signedCoefficient_volume o ho]
      exact (mul_assoc _ _ _).symm
    rw [heq]
    exact chart_absolute_substitution (C i).chart (C i).extension (C i).regular
      (C i).inverse_regular (C i).source_subset (C i).ambient_eq (C i).agrees
      (C i).differential (fun x : closure D => Q.weight i x * f x) (hi i) hk hs
  change (∑ i, (P.sign i).val * coefficientIntegral
    (localizedTopCoefficient (volumeField f) (P.chart i) (P.weight i))) = _
  rw [D04.ManifoldIntegralIndependence.signed_expression o (volumeField f) hη P]
  have hcmp := D04.ManifoldIntegralIndependence.partition_independence
    (D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f))
    (D04.ManifoldIntegralIndependence.signedCoefficient_continuous o (volumeField f) hη)
    (D04.ManifoldIntegralIndependence.signedCoefficient_transition o (volumeField f))
    o.manifold.1 o.manifold.2.1 P.toChartPartition Q
    (fun c u hu => D04.ManifoldIntegralIndependence.signedCoefficient_support o (volumeField f) c u hu)
    (fun _ _ _ => mem_univ _)
  apply hcmp.trans
  rw [Finset.sum_congr rfl (fun i _ => hv i)]
  apply (region_integral_sum hD.bounded.closure _ hi f hfi ?_).symm
  intro x
  obtain ⟨V, hV, hKV, hsum⟩ := Q.partition.2.2.2.1
  have hx := hsum x (hKV (mem_univ x))
  rw [← Finset.sum_mul, hx, one_mul]

/-- The regular-domain/Riemann interface, with the intrinsic geometry,
ambient orientation, outward-first normal, and the two actual integrals. -/
theorem regular_domain_interface : regular_domain_interfaceType := by
  intro d D hD
  obtain ⟨o, ho, hK, hb, hJD, hJK, hn, hdata⟩ := regular_domain_data hD
  refine ⟨o, ho, hK, o.manifold, hb, hJD, hJK, hn, ?_, ?_⟩
  · intro U ρ hρ p hp
    exact RegularDomainGeometry.defining_normal_conormal hD hρ p hp
  · intro f hf
    obtain ⟨hη, hkη, hP, hiK, hiD, heq⟩ := hdata f hf
    refine ⟨hη, hkη, hP, hiK, hiD, ?_⟩
    intro P
    exact ⟨(manifold_integral_eq_region hD o ho f hf P).trans heq, heq.symm⟩

end D04.RegularDomainBridge
