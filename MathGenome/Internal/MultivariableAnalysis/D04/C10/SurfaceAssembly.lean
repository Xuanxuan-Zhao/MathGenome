import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SurfaceAssembly
import MathGenome.Internal.MultivariableAnalysis.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C14.ChartIndependentTangentSpaces
import MathGenome.Internal.MultivariableAnalysis.D04.C15.ManifoldIntegralIndependence
import Mathlib.Topology.TietzeExtension

noncomputable section
open Set Function Topology Filter
open scoped RealInnerProductSpace BigOperators ContDiff Classical
namespace D04SurfaceAssembly
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C10.SurfaceAssembly.Model


lemma compact_support {n : ℕ} {M : Set (E n)} (hM : IsCompact M) (f : M → ℝ) :
    HasCompactSupport f := by
  let : CompactSpace M := isCompact_iff_compactSpace.mp hM
  exact (isClosed_tsupport f).isCompact

theorem scalar_density_identification :
    Specs.D04.C10.SurfaceAssembly.scalar_density_identificationType := by
  intro n M hM hc f hf P
  dsimp only [surfaceIntegral, Specs.D04.C10.SurfaceAssembly.Model.surfaceIntegral]
  rw [dite_eq_left ⟨P⟩]
  exact D04.ManifoldIntegralIndependence.density_independent hM f hf _ P

theorem scalar_chart_formula : Specs.D04.C10.SurfaceAssembly.scalar_chart_formulaType := by
  intro n M hM hc f hf K P hs
  obtain ⟨Q⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) (compact_support hc f)
  rw [scalar_density_identification hM hc f hf Q]
  exact D04.ManifoldIntegralIndependence.density_comparison hM f hf Q P Subset.rfl hs

theorem scalar_construction : Specs.D04.C10.SurfaceAssembly.scalar_constructionType := by
  intro n M hM hc f hf
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) (compact_support hc f)
  refine ⟨P, fun i => (D04.ManifoldIntegral.density_coefficients_integrable hM f hf P i).2.2, ?_⟩
  rw [scalar_chart_formula hM hc f hf P Subset.rfl]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext u
  dsimp only [localizedDensityCoefficient, densityCoefficient]
  rw [D04MetricDensity.chartDensity_matrix]
  ring

theorem scalar_add : Specs.D04.C10.SurfaceAssembly.scalar_addType := by
  intro n M hM hc f g hf hg
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) (compact_support hc f)
  obtain ⟨Q⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport g) (compact_support hc g)
  obtain ⟨R⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport (f + g))
    (compact_support hc (f + g))
  rw [scalar_density_identification hM hc (f + g) (hf.add hg) R,
    scalar_density_identification hM hc f hf P, scalar_density_identification hM hc g hg Q]
  exact D04.ManifoldIntegralIndependence.density_add hM f g hf hg
    (compact_support hc f) (compact_support hc g) P Q R

theorem scalar_smul : Specs.D04.C10.SurfaceAssembly.scalar_smulType := by
  intro n M hM hc a f hf
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) (compact_support hc f)
  obtain ⟨Q⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport (a • f))
    (compact_support hc (a • f))
  rw [scalar_density_identification hM hc (a • f) (continuous_const.smul hf) Q,
    scalar_density_identification hM hc f hf P]
  exact D04.ManifoldIntegralIndependence.density_smul hM a f hf P Q

theorem scalar_localization : Specs.D04.C10.SurfaceAssembly.scalar_localizationType := by
  classical
  intro n M hM hc f hf m w hw hs
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) (compact_support hc f)
  let Q (i : Fin m) : ChartPartition 1 2 M (tsupport (fun x : M => w i x * f x)) :=
    Classical.choice (D04.ManifoldIntegral.chart_partition_exists hM _ (compact_support hc _))
  rw [scalar_density_identification hM hc f hf P,
    D04.ManifoldIntegralIndependence.density_finite_localization hM f hf w hw hs P Q]
  apply Finset.sum_congr rfl
  intro i _
  exact (scalar_density_identification hM hc _
    (((hw i).comp continuous_subtype_val).mul hf) (Q i)).symm

theorem scalar_single_chart : Specs.D04.C10.SurfaceAssembly.scalar_single_chartType := by
  intro n M hM hc f hf c hs
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) (compact_support hc f)
  rw [scalar_density_identification hM hc f hf P]
  exact D04.ManifoldIntegralIndependence.density_single_chart hM f hf (compact_support hc f) P c hs

theorem tangent_chart_independence :
    Specs.D04.C10.SurfaceAssembly.tangent_chart_independenceType := by
  intro n M hM c d u v he
  exact ⟨D04.tangentSpace_chart c hM.1 hM.2.1 u u.property,
    D04.chart_independence c d hM.1 hM.2.1 u u.property v v.property he⟩

theorem regular_locally_embedded :
    Specs.D04.C10.SurfaceAssembly.regular_locally_embeddedType := by
  intro n U φ hφ u hu
  have hkn : 2 ≤ n := by
    have h := LinearMap.finrank_le_finrank_of_injective (hφ.2.2 u hu)
    simpa only [finrank_euclideanSpace_fin] using h
  have hr : ManifoldRegularity (1 : ℕ∞ω) := ⟨le_rfl, by simp⟩
  have hext : FullRankLocalExtension 1 U φ :=
    (D04.open_fullRankLocalExtension_iff U φ hφ.1).mpr hφ.2
  obtain ⟨s, W, g, X, Y, q, H⟩ := D04.local_graph_and_ambient_inverse U φ u false hr hkn
    (by simp) ⟨U, hφ.1, by simp [parameterSpace]⟩ hext hu
  obtain ⟨hX, hY, huX, _, _, _, _, _, _, _⟩ := H.inverse
  let V := U ∩ X
  let T := φ '' V
  let e : V ≃ₜ T :=
    { toFun := fun v => ⟨φ v, ⟨v, v.property, rfl⟩⟩
      invFun := fun x => ⟨q (Specs.D04.C14.LocalGraphAndAmbientInverse.Model.coordinateProjection s x),
        H.inverse_maps x.property⟩
      left_inv := fun v => Subtype.ext (H.inverse_left v.property)
      right_inv := fun x => Subtype.ext (H.inverse_right x.property)
      continuous_toFun := ((hφ.2.1.continuousOn.mono inter_subset_left).domRestrict).subtype_mk _
      continuous_invFun := (H.inverse_ambient_regular.continuousOn.comp_continuous
        continuous_subtype_val (fun x => by
          have hx := H.inverse_maps x.property
          have hp := H.projected_domain ▸ (show
            Specs.D04.C14.LocalGraphAndAmbientInverse.Model.coordinateProjection s x ∈
              (Specs.D04.C14.LocalGraphAndAmbientInverse.Model.coordinateProjection s ∘ φ) '' V from by
            obtain ⟨v, hv, he⟩ := x.property
            exact ⟨v, hv, congrArg _ he⟩)
          exact hp.1)).subtype_mk _ }
  refine ⟨V, hφ.1.inter hX, ⟨hu, huX⟩, inter_subset_left,
    ⟨hφ.1.inter hX, hφ.2.1.mono inter_subset_left,
      fun v hv => hφ.2.2 v hv.1⟩, ?_⟩
  exact Topology.IsEmbedding.subtypeVal.comp e.isEmbedding

theorem flux_chart_formula : Specs.D04.C10.SurfaceAssembly.flux_chart_formulaType := by
  intro M hM hc N F hF P
  rw [show surfaceFlux N F = surfaceIntegral M (fun x => ⟪F x, N.toFun x⟫) from rfl,
    scalar_chart_formula hM hc _ (hF.inner N.continuous) P Subset.rfl]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext u
  dsimp [localizedDensityCoefficient, densityCoefficient]
  ring

lemma flux_form_coefficient {M : Set (E 3)} (F : M → E 3)
    (c : EmbeddedChart 1 2 3 M) (u : c.source) :
    topCoefficient (surfaceFluxForm F) c u =
      ⟪F (chartPoint c u), euclideanCross (chartDifferential c u (standardBasis 2 0))
        (chartDifferential c u (standardBasis 2 1))⟫ := by
  change beta (fun _ => F (chartPoint c u)) (c.toFun u)
    (fun i => chartDifferential c u (standardBasis 2 i)) = _
  have hv : (fun i => chartDifferential c u (standardBasis 2 i)) =
      ![chartDifferential c u (standardBasis 2 0), chartDifferential c u (standardBasis 2 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, D04.Dictionary.beta_cross]

lemma flux_form_continuous {M : Set (E 3)} (F : M → E 3) (hF : Continuous F) :
    ContinuousTopField (surfaceFluxForm F) := by
  intro c
  have hd := (D04MetricDensity.chartDifferential_continuous c
    (show ManifoldRegularity (1 : ℕ∞ω) from ⟨le_rfl, by simp⟩)).domRestrict
  have hcol (i : Fin 2) : Continuous (fun u : c.source => chartDifferential c u (standardBasis 2 i)) :=
    hd.clm_apply continuous_const
  have hcross : Continuous (fun u : c.source =>
      euclideanCross (chartDifferential c u (standardBasis 2 0))
        (chartDifferential c u (standardBasis 2 1))) :=
    D04.AreaIntegral.continuous_cross.comp ((hcol 0).prodMk (hcol 1))
  have he : topCoefficient (surfaceFluxForm F) c = fun u =>
      ⟪F (chartPoint c u), euclideanCross (chartDifferential c u (standardBasis 2 0))
        (chartDifferential c u (standardBasis 2 1))⟫ := funext (flux_form_coefficient F c)
  rw [he]
  exact (hF.comp (D04.ManifoldIntegral.chartPoint_continuous c)).inner hcross

lemma chart_normal_choices {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (N : UnitNormalField M) (c : EmbeddedChart 1 2 3 M) (u : c.source) :
    N.toFun (chartPoint c u) = surfaceChartNormal c u ∨
      N.toFun (chartPoint c u) = -surfaceChartNormal c u := by
  apply D04.PatchGeometryGram.normal_choices_linear (chartDifferential c u).toLinearMap
    (D04.EmbeddedChart.differential_injective c hM.1 u.property) (N.toFun (chartPoint c u)) |>.mp
  have hn := N.normal (chartPoint c u)
  change IsUnitNormal (tangentSpace 1 2 M (c.toFun u)) _ at hn
  rwa [D04.tangentSpace_chart c hM.1 hM.2.1 u u.property] at hn

lemma chart_normal_norm {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (c : EmbeddedChart 1 2 3 M) (u : c.source) : ‖surfaceChartNormal c u‖ = 1 := by
  have hcross : euclideanCross (chartDifferential c u (standardBasis 2 0))
      (chartDifferential c u (standardBasis 2 1)) ≠ 0 :=
    (D04.PatchGeometryGram.cross_rank (chartDifferential c u).toLinearMap).mpr
      (D04.EmbeddedChart.differential_injective c hM.1 u.property)
  dsimp only [surfaceChartNormal, Specs.D04.C10.SurfaceAssembly.Model.surfaceChartNormal]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hcross)]

theorem normal_chart_sign : Specs.D04.C10.SurfaceAssembly.normal_chart_signType := by
  intro M hM N c u
  have hn := chart_normal_norm hM c u
  have hi : ⟪surfaceChartNormal c u, surfaceChartNormal c u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hJ : chartDensity c u = ‖euclideanCross (chartDifferential c u (standardBasis 2 0))
      (chartDifferential c u (standardBasis 2 1))‖ :=
    D04MetricDensity.gram_cross (chartDifferential c u)
  have hnorm := (D04MetricDensity.chartDensity_positive c hM.1 u u.property).ne'
  have hvec : chartDensity c u • surfaceChartNormal c u =
      euclideanCross (chartDifferential c u (standardBasis 2 0))
        (chartDifferential c u (standardBasis 2 1)) := by
    dsimp only [surfaceChartNormal, Specs.D04.C10.SurfaceAssembly.Model.surfaceChartNormal]
    rw [← hJ, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  rcases chart_normal_choices hM N c u with h | h
  · have hs : normalChartSign N c u = 1 := by
      change ⟪N.toFun (chartPoint c u), surfaceChartNormal c u⟫ = 1
      rw [h, hi]
    refine ⟨Or.inl hs, by rw [hs, one_smul]; exact h, ?_⟩
    intro F
    rw [hs, one_mul, flux_form_coefficient, ← hvec, h, inner_smul_right]
    ring
  · have hs : normalChartSign N c u = -1 := by
      change ⟪N.toFun (chartPoint c u), surfaceChartNormal c u⟫ = -1
      rw [h, inner_neg_left, hi]
    refine ⟨Or.inr hs, by rw [hs, neg_one_smul]; exact h, ?_⟩
    intro F
    rw [hs, flux_form_coefficient, ← hvec, h, inner_smul_right, inner_neg_right]
    ring

lemma normal_coefficient {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (N : UnitNormalField M) (c : EmbeddedChart 1 2 3 M) (u : c.source) :
    topCoefficient (surfaceFluxForm N.toFun) c u = normalChartSign N c u * chartDensity c u := by
  have h := (normal_chart_sign hM N c u).2.2 N.toFun
  have hn : ⟪N.toFun (chartPoint c u), N.toFun (chartPoint c u)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, (N.normal _).1, one_pow]
  rw [hn, one_mul] at h
  rcases (normal_chart_sign hM N c u).1 with hs | hs <;> rw [hs] at h ⊢ <;> linarith

lemma normal_form_ne_zero {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (N : UnitNormalField M) (x : M) : surfaceFluxForm N.toFun x ≠ 0 := by
  obtain ⟨c, u, hu, he⟩ := hM.2.2 x x.property
  let v : c.source := ⟨u, hu.1⟩
  have hx : chartPoint c v = x := Subtype.ext he
  have hcoef : topCoefficient (surfaceFluxForm N.toFun) c v ≠ 0 := by
    rw [normal_coefficient hM N]
    apply mul_ne_zero
    · rcases (normal_chart_sign hM N c v).1 with h | h <;> rw [h] <;> norm_num
    · exact (D04MetricDensity.chartDensity_positive c hM.1 v v.property).ne'
  intro hz
  apply hcoef
  change (surfaceFluxForm N.toFun (chartPoint c v)) _ = 0
  have hz' : surfaceFluxForm N.toFun (chartPoint c v) = 0 := hx.symm ▸ hz
  rw [hz']
  rfl

lemma sign_normal_coefficient {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (N : UnitNormalField M) (c : EmbeddedChart 1 2 3 M) (u : c.source) :
    Real.sign (topCoefficient (surfaceFluxForm N.toFun) c u) = normalChartSign N c u := by
  rw [normal_coefficient hM N]
  have hp := D04MetricDensity.chartDensity_positive c hM.1 u u.property
  rcases (normal_chart_sign hM N c u).1 with h | h
  · rw [h, one_mul, Real.sign_of_pos hp]
  · rw [h, neg_one_mul, Real.sign_of_neg (neg_neg_of_pos hp)]

lemma positive_ray_evaluation_sign {V : Type} [AddCommGroup V] [Module ℝ V]
    (η : Covector V 2) (hη : η ≠ 0) (v : Fin 2 → V) :
    Real.sign ((rayOfNeZero ℝ η hη).someVector v) = Real.sign (η v) := by
  let o := rayOfNeZero ℝ η hη
  have h : SameRay ℝ o.someVector η :=
    (ray_eq_iff o.someVector_ne_zero hη).mp o.someVector_ray
  obtain ⟨a, ha, he⟩ := h.exists_pos_right o.someVector_ne_zero hη
  rw [he]
  change Real.sign (a * η v) = _
  rcases lt_trichotomy (η v) 0 with h | h | h
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ha h), Real.sign_of_neg h]
  · rw [h, mul_zero]
  · rw [Real.sign_of_pos (mul_pos ha h), Real.sign_of_pos h]

lemma flux_scalar_support_subset {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (N : UnitNormalField M) (F : M → E 3) :
    tsupport (fun x => ⟪F x, N.toFun x⟫) ⊆ topSupport (surfaceFluxForm F) := by
  apply closure_mono
  intro x hx hz
  obtain ⟨c, u, hu, he⟩ := hM.2.2 x x.property
  let v : c.source := ⟨u, hu.1⟩
  have hxv : chartPoint c v = x := Subtype.ext he
  have hz' : surfaceFluxForm F (chartPoint c v) = 0 := hxv.symm ▸ hz
  have hc0 : topCoefficient (surfaceFluxForm F) c v = 0 := by
    change (surfaceFluxForm F (chartPoint c v)) _ = 0
    rw [hz']
    rfl
  have h := (normal_chart_sign hM N c v).2.2 F
  rw [hc0, mul_zero] at h
  have hval : ⟪F (chartPoint c v), N.toFun (chartPoint c v)⟫ = 0 :=
    (mul_eq_zero.mp h.symm).resolve_right
      (D04MetricDensity.chartDensity_positive c hM.1 v v.property).ne'
  rw [hxv] at hval
  exact hx hval

/-- The positive ray of beta_N gives exactly the orientation chosen by N.
Continuity is proved from its nonzero continuous chart coefficients. -/
theorem normal_orientation {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (N : UnitNormalField M) :
    ∃ o : PositiveManifoldOrientation 1 2 M,
      ∀ (c : EmbeddedChart 1 2 3 M) (u : c.source),
        chartSign o.atPoint c u u.property = normalChartSign N c u := by
  let η := surfaceFluxForm N.toFun
  let a : TangentOrientationField 1 2 M := fun x hx =>
    rayOfNeZero ℝ (η ⟨x, hx⟩) (normal_form_ne_zero hM N ⟨x, hx⟩)
  have hs (c : EmbeddedChart 1 2 3 M) (u : c.source) :
      chartSign a c u u.property = normalChartSign N c u := by
    change Real.sign ((rayOfNeZero ℝ (η (chartPoint c u)) _).someVector _) = _
    exact (positive_ray_evaluation_sign (η (chartPoint c u))
      (normal_form_ne_zero hM N (chartPoint c u))
      (fun i => tangentChartMap c u u.property (standardBasis 2 i))).trans
        (sign_normal_coefficient hM N c u)
  have hloc (c : EmbeddedChart 1 2 3 M) :
      IsLocallyConstant (fun u : c.source => chartSign a c u u.property) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro u
    have hcoef : topCoefficient η c u ≠ 0 := by
      rw [normal_coefficient hM N]
      refine mul_ne_zero ?_ (D04MetricDensity.chartDensity_positive c hM.1 u u.property).ne'
      rcases (normal_chart_sign hM N c u).1 with h | h <;> rw [h] <;> norm_num
    have hcont := (flux_form_continuous N.toFun N.continuous c).continuousAt (x := u)
    rcases lt_or_gt_of_ne hcoef with hneg | hpos
    · have hev := hcont.eventually (gt_mem_nhds hneg)
      filter_upwards [hev] with v hv
      rw [hs, hs, ← sign_normal_coefficient hM N c v,
        ← sign_normal_coefficient hM N c u, Real.sign_of_neg hv, Real.sign_of_neg hneg]
    · have hev := hcont.eventually (lt_mem_nhds hpos)
      filter_upwards [hev] with v hv
      rw [hs, hs, ← sign_normal_coefficient hM N c v,
        ← sign_normal_coefficient hM N c u, Real.sign_of_pos hv, Real.sign_of_pos hpos]
  exact ⟨⟨by norm_num, hM, a, hloc⟩, hs⟩

theorem flux_beta_identification : Specs.D04.C10.SurfaceAssembly.flux_beta_identificationType := by
  intro M hM hc N
  obtain ⟨o, ho⟩ := normal_orientation hM N
  refine ⟨o, ho, ?_⟩
  intro F hF
  have hη := flux_form_continuous F hF
  refine ⟨hη, ?_⟩
  intro P
  change surfaceIntegral M (fun x => ⟪F x, N.toFun x⟫) = _
  rw [scalar_chart_formula hM hc _ (hF.inner N.continuous) P.toChartPartition
    (flux_scalar_support_subset hM N F)]
  dsimp only [orientedIntegral]
  apply Finset.sum_congr rfl
  intro i _
  rw [← D04.ManifoldIntegralIndependence.coefficientIntegral_smul (P.sign i).val
    (D04.ManifoldIntegral.top_coefficients_integrable (surfaceFluxForm F) hη P.toChartPartition i).2.2]
  congr 1
  funext u
  dsimp only [localizedDensityCoefficient, densityCoefficient, localizedTopCoefficient]
  rw [← (normal_chart_sign hM N (P.chart i) u).2.2 F]
  have hs : normalChartSign N (P.chart i) u = (P.sign i).val :=
    (ho (P.chart i) u).symm.trans (P.agrees i u)
  rw [hs]
  ring

theorem flux_adjusted_chart_formula :
    Specs.D04.C10.SurfaceAssembly.flux_adjusted_chart_formulaType := by
  intro M hM hc N F hF P
  rw [flux_chart_formula hM hc N F hF P]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext u
  rw [mul_assoc, ← (normal_chart_sign hM N (P.chart i) u).2.2 F]
  ring

theorem flux_construction : Specs.D04.C10.SurfaceAssembly.flux_constructionType := by
  intro M hM hc N F hF
  obtain ⟨o, ho, h⟩ := flux_beta_identification hM hc N
  have hη := (h F hF).1
  have hk : IsCompact (topSupport (surfaceFluxForm F)) := by
    let : CompactSpace M := isCompact_iff_compactSpace.mp hc
    exact isClosed_closure.isCompact
  obtain ⟨P⟩ := D04.ManifoldIntegral.signed_partition_exists o _ hk
  exact ⟨o, ho, P, fun i =>
    (D04.ManifoldIntegral.top_coefficients_integrable (surfaceFluxForm F) hη P.toChartPartition i).2.2,
    (h F hF).2 P⟩

theorem overlap_double_count : Specs.D04.C10.SurfaceAssembly.overlap_double_countType := by
  intro n M hM hc f hf c d hsc hsd
  have hcv := (scalar_single_chart hM hc f hf c hsc).2
  have hdv := (scalar_single_chart hM hc f hf d hsd).2
  rw [← hcv, ← hdv]
  constructor
  · ring
  · intro hn he
    apply hn
    linarith

theorem piece_integrable : Specs.D04.C10.SurfaceAssembly.piece_integrableType := by
  intro n M hM p f hf
  apply D04.AreaIntegral.region_integrable_of_continuous p.compact p.jordan
  have hg : Continuous (fun u : p.domain =>
      (⟨u, p.subset_source u.property⟩ : p.chart.source)) :=
    continuous_subtype_val.subtype_mk _
  exact (hf.comp ((D04.ManifoldIntegral.chartPoint_continuous p.chart).comp hg)).mul
    ((D04MetricDensity.chartDensity_continuous p.chart hM.1).comp_continuous
      continuous_subtype_val (fun u => p.subset_source u.property))

/-! Proper Riemann coefficients need not be continuous: piece indicators jump
at their Jordan boundaries. These lemmas retain actual proper integrability. -/
namespace PieceAssembly
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.DarbouxIntegral.Model hiding E
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open D04.DirectedSubstitution (proper_congr extension_regionBounded overlapHomeomorph)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

@[simp] lemma zeroExtension_apply {k : ℕ} {S : Set (E k)} (f : S → ℝ) (x : S) :
    zeroExtension f x = f x := D04.JordanRegions.zeroExtension_apply f x

lemma zeroExtension_of_not_mem {k : ℕ} {S : Set (E k)} (f : S → ℝ)
    {x : E k} (hx : x ∉ S) : zeroExtension f x = 0 :=
  D04.JordanRegions.zeroExtension_of_not_mem f hx

lemma zeroExtension_sum {k : ℕ} {S : Set (E k)} {ι : Type} [Fintype ι] (F : ι → S → ℝ) :
    zeroExtension (fun x => ∑ i, F i x) = fun x => ∑ i, zeroExtension (F i) x :=
  D04.Localization.zeroExtension_sum F

lemma coefficientIntegral_eq_on_box {k : ℕ} {S : Set (E k)} {f : S → ℝ} (hf : ProperIntegrable f)
    (Q : Box k) (hQ : Encloses (support (zeroExtension f)) Q) :
    ∃ hi : Integrable (zeroExtension f) Q,
      coefficientIntegral f = Specs.D04.C06.DarbouxIntegral.Model.integral (zeroExtension f) Q hi :=
  D04.DirectedSubstitution.proper_on_box hf Q hQ

lemma regionBounded_of_proper {k : ℕ} {S : Set (E k)} {f : S → ℝ}
    (hf : ProperIntegrable f) : RegionBounded f := by
  obtain ⟨Q, hQ, hi⟩ := hf.2
  obtain ⟨a, ha⟩ := hi.1.1
  obtain ⟨b, hb⟩ := hi.1.2
  refine ⟨max |a| |b|, fun x => ?_⟩
  by_cases hx : f x = 0
  · simp only [hx, norm_zero]
    exact (abs_nonneg a).trans (le_max_left _ _)
  · have hs : (x : E k) ∈ support (zeroExtension f) := by
      simpa only [mem_support, zeroExtension_apply] using hx
    have hxc := D04.JordanRegions.encloses_subset hQ hs
    have hl := ha (mem_image_of_mem _ hxc)
    have hu := hb (mem_image_of_mem _ hxc)
    rw [zeroExtension_apply] at hl hu
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hl),
      hu.trans ((le_abs_self b).trans (le_max_right _ _))⟩

/-- Extend a multiplier only on the compact support where its value matters.
This works on relative half-space domains without extending the integrand. -/
lemma multiplier_extension {k : ℕ} {S : Set (E k)} {f : S → ℝ}
    (hk : HasCompactSupport f) (b : S → ℝ) (hb : Continuous b) :
    ∃ B : C(E k, ℝ), ∀ x : S, f x * b x = f x * B x := by
  let e : tsupport f → E k := fun x => x.val.val
  have he : IsClosedEmbedding e := by
    refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
    have hr : Set.range e = Subtype.val '' tsupport f := by
      ext x
      simp only [Set.mem_range, Set.mem_image, e]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y.val, y.property, hy⟩
      · rintro ⟨y, hy, he⟩
        exact ⟨⟨y, hy⟩, he⟩
    rw [hr]
    exact (hk.image continuous_subtype_val).isClosed
  let b' : C(tsupport f, ℝ) := ⟨fun x => b x.val, hb.comp continuous_subtype_val⟩
  obtain ⟨B, hB⟩ := b'.exists_extension' he
  refine ⟨B, fun x => ?_⟩
  by_cases hx : f x = 0
  · simp [hx]
  · have h := congrFun hB ⟨x, subset_tsupport f hx⟩
    exact congrArg (fun t => f x * t) h.symm

lemma proper_mul_continuous {k : ℕ} (hkpos : 0 < k) {S : Set (E k)}
    {f : S → ℝ} (hf : ProperIntegrable f) (hk : HasCompactSupport f)
    (b : S → ℝ) (hb : Continuous b) :
    ProperIntegrable (fun x => f x * b x) := by
  obtain ⟨B, hB⟩ := multiplier_extension hk b hb
  have he : zeroExtension (fun x => f x * b x) = fun x => zeroExtension f x * B x := by
    funext x
    by_cases hx : x ∈ S
    · rw [zeroExtension_apply _ ⟨x, hx⟩, zeroExtension_apply f ⟨x, hx⟩]
      exact hB ⟨x, hx⟩
    · simp [zeroExtension, hx]
  have hs : support (zeroExtension (fun x => f x * b x)) ⊆ support (zeroExtension f) := by
    rw [he]
    exact support_mul_subset_left _ _
  obtain ⟨Q, hQ, hi⟩ := hf.2
  refine ⟨hf.1.subset hs, Q, (closure_mono hs).trans hQ, ?_⟩
  rw [he]
  exact D04.Darboux.integrable_mul hi
    (D04.ExceptionalSets.integrable_continuous hkpos Q B B.continuous.continuousOn)

lemma proper_sum {k : ℕ} {S : Set (E k)} {ι : Type} [Fintype ι]
    (F : ι → S → ℝ) (hF : ∀ i, ProperIntegrable (F i)) :
    ProperIntegrable (fun x => ∑ i, F i x) ∧
    coefficientIntegral (fun x => ∑ i, F i x) = ∑ i, coefficientIntegral (F i) := by
  classical
  let K := ⋃ i, support (zeroExtension (F i))
  have hK : Bornology.IsBounded K := Bornology.isBounded_iUnion.mpr fun i => (hF i).1
  obtain ⟨Q, hQ⟩ := (D04.JordanRegions.encloses_exists_iff_bounded K).mpr hK
  have hqi i : Encloses (support (zeroExtension (F i))) Q :=
    (closure_mono (subset_iUnion (fun j => support (zeroExtension (F j))) i)).trans hQ
  have his i := (coefficientIntegral_eq_on_box (hF i) Q (hqi i)).choose
  have hqsum : Encloses (support (zeroExtension (fun x => ∑ i, F i x))) Q := by
    apply (closure_mono (show support (zeroExtension (fun x => ∑ i, F i x)) ⊆ K from ?_)).trans hQ
    rw [zeroExtension_sum]
    intro x hx
    by_contra hxK
    apply hx
    exact Finset.sum_eq_zero (fun i _ => by
      exact notMem_support.mp (fun h => hxK (mem_iUnion.mpr ⟨i, h⟩)))
  have hi : Integrable (zeroExtension (fun x => ∑ i, F i x)) Q := by
    rw [zeroExtension_sum]
    exact D04.Darboux.integrable_sum Finset.univ _ (fun i _ => his i)
  have hsum : ProperIntegrable (fun x => ∑ i, F i x) :=
    ⟨D04.JordanRegions.encloses_bounded hqsum, Q, hqsum, hi⟩
  refine ⟨hsum, ?_⟩
  rw [(coefficientIntegral_eq_on_box hsum Q hqsum).choose_spec]
  have hv := D04.Darboux.integral_sum Finset.univ (fun i => zeroExtension (F i))
    (fun i _ => his i) (by simpa only [zeroExtension_sum] using hi)
  simpa only [Finset.mem_univ, ↓reduceDIte, ← zeroExtension_sum,
    ← (coefficientIntegral_eq_on_box (hF _) Q (hqi _)).choose_spec] using hv

/-- Restriction retaining all the support preserves the ambient zero extension. -/
lemma proper_restrict {k : ℕ} {S T : Set (E k)} (hST : S ⊆ T)
    {f : T → ℝ} (hf : ProperIntegrable f) (hk : HasCompactSupport f)
    (hs : Subtype.val '' tsupport f ⊆ S) :
    let g : S → ℝ := fun x => f ⟨x, hST x.property⟩
    ProperIntegrable g ∧ HasCompactSupport g ∧ coefficientIntegral g = coefficientIntegral f := by
  let g : S → ℝ := fun x => f ⟨x, hST x.property⟩
  have he : zeroExtension g = zeroExtension f := by
    funext x
    by_cases hx : x ∈ S
    · rw [zeroExtension_apply g ⟨x, hx⟩, zeroExtension_apply f ⟨x, hST hx⟩]
    · rw [zeroExtension_of_not_mem g hx]
      symm
      apply image_eq_zero_of_notMem_tsupport
      rw [D04.Localization.zeroExtension_tsupport hk]
      exact fun h => hx (hs h)
  refine ⟨(proper_congr he).1.mpr hf, ?_, (proper_congr he).2⟩
  have hg : g = fun x : S => zeroExtension f x := by
    funext x
    exact (zeroExtension_apply f ⟨x, hST x.property⟩).symm
  change HasCompactSupport g
  rw [hg]
  exact D04.RiemannSubstitution.compact_restrict (D04.Localization.zeroExtension_compact hk)
    ((D04.Localization.zeroExtension_tsupport hk) ▸ hs)

/-- In a Euclidean extension neighborhood, zero extension intertwines the
chart transition with the extension. No continuity of f is used here. -/
lemma transition_zeroExtension {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (e : OpenPartialHomeomorph (E k) (E k))
    (he : EqOn e (chartTransition c d) (chartOverlap c d ∩ e.source))
    {f : chartOverlap d c → ℝ} (hk : HasCompactSupport f)
    (hs : ∀ y ∈ tsupport f, chartTransition d c y ∈ e.source) :
    (tsupport (zeroExtension f) ⊆ e.target) ∧
    ∀ x : E k, zeroExtension (fun u : chartOverlap c d =>
      f (overlapHomeomorph c d u)) x =
      zeroExtension (fun u : e.source => zeroExtension f (e u)) x := by
  have hmap (y : chartOverlap d c) (hy : y ∈ tsupport f) :
      e (chartTransition d c y) = y :=
    (he ⟨D04.EmbeddedChart.transition_mem d c y.property, hs y hy⟩).trans
      (D04.EmbeddedChart.transition_left_inv d c y.property)
  constructor
  · rw [D04.Localization.zeroExtension_tsupport hk]
    rintro _ ⟨y, hy, rfl⟩
    rw [← hmap y hy]
    exact e.map_source (hs y hy)
  · intro x
    by_cases hS : x ∈ chartOverlap c d
    · rw [zeroExtension_apply _ ⟨x, hS⟩]
      by_cases hx : x ∈ e.source
      · rw [zeroExtension_apply _ ⟨x, hx⟩, he ⟨hS, hx⟩]
        exact (zeroExtension_apply f (overlapHomeomorph c d ⟨x, hS⟩)).symm
      · rw [zeroExtension_of_not_mem _ hx]
        apply image_eq_zero_of_notMem_tsupport
        intro hy
        have h := hs (overlapHomeomorph c d ⟨x, hS⟩) hy
        exact hx ((D04.EmbeddedChart.transition_left_inv c d hS) ▸ h)
    · rw [zeroExtension_of_not_mem _ hS]
      by_cases hx : x ∈ e.source
      · rw [zeroExtension_apply _ ⟨x, hx⟩]
        symm
        by_contra hn
        have hy : e x ∈ chartOverlap d c := by
          by_contra hy
          exact hn (zeroExtension_of_not_mem f hy)
        let y : chartOverlap d c := ⟨e x, hy⟩
        have hyf : y ∈ tsupport f := subset_tsupport f (fun hz => hn ((zeroExtension_apply f y).trans hz))
        have heq : e (chartTransition d c y) = e x := hmap y hyf
        have hxq := e.injOn (hs y hyf) hx heq
        exact hS (hxq ▸ D04.EmbeddedChart.transition_mem d c hy)
      · exact (zeroExtension_of_not_mem _ hx).symm

lemma local_proper_unsigned {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M)
    (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (heq : EqOn e (chartTransition c d) (chartOverlap c d ∩ e.source))
    (hd : ∀ x ∈ chartOverlap c d ∩ e.source,
      fderiv ℝ e x = fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x)
    {f : chartOverlap d c → ℝ} (hf : ProperIntegrable f) (hk : HasCompactSupport f)
    (hs : ∀ y ∈ tsupport f, chartTransition d c y ∈ e.source) :
    let g : chartOverlap c d → ℝ := fun x => f (overlapHomeomorph c d x) *
      |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det|
    ProperIntegrable g ∧ coefficientIntegral g = coefficientIntegral f := by
  obtain ⟨ht, hv⟩ := transition_zeroExtension c d e heq hk hs
  let F : e.target → ℝ := fun y => zeroExtension f y
  have hF : zeroExtension F = zeroExtension f := by
    funext y
    by_cases hy : y ∈ e.target
    · exact zeroExtension_apply F ⟨y, hy⟩
    · rw [zeroExtension_of_not_mem F hy]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hy (ht h))).symm
  have hFi : OpenIntegrable F := ⟨e.open_target, (proper_congr hF).1.mpr hf⟩
  have hFk := D04.RiemannSubstitution.compact_restrict
    (D04.Localization.zeroExtension_compact hk) ht
  have hFb : RegionBounded F := extension_regionBounded (regionBounded_of_proper hf)
  have hsub := D04.RiemannSubstitution.riemann_substitution e.toHomeomorphSourceTarget e e.symm
    e.open_source e.open_target he hei (fun _ => rfl) (fun _ => rfl) F hFb hFk
  let p : e.source → ℝ := fun x => F ⟨e x, e.map_source x.property⟩ * |(fderiv ℝ e x).det|
  have hpi : OpenIntegrable p := hsub.2.2.2.2.1.mp hFi
  let g : chartOverlap c d → ℝ := fun x => f (overlapHomeomorph c d x) *
    |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det|
  have hgp : zeroExtension g = zeroExtension p := by
    funext x
    by_cases hx : x ∈ chartOverlap c d ∩ e.source
    · obtain ⟨hS, heS⟩ := hx
      rw [zeroExtension_apply g ⟨x, hS⟩, zeroExtension_apply p ⟨x, heS⟩]
      change f (overlapHomeomorph c d ⟨x, hS⟩) * _ = zeroExtension f (e x) * _
      rw [hd x ⟨hS, heS⟩, heq ⟨hS, heS⟩]
      exact congrArg (fun t => t * |(fderivWithin ℝ (chartTransition c d)
        (chartOverlap c d) x).det|) (zeroExtension_apply f (overlapHomeomorph c d ⟨x, hS⟩)).symm
    · have hz : zeroExtension (fun u : chartOverlap c d => f (overlapHomeomorph c d u)) x = 0 := by
        by_cases hS : x ∈ chartOverlap c d
        · rw [hv, zeroExtension_of_not_mem _ (fun h => hx ⟨hS, h⟩)]
        · exact zeroExtension_of_not_mem _ hS
      have hpz := (hv x).symm.trans hz
      by_cases hS : x ∈ chartOverlap c d
      · rw [zeroExtension_apply _ ⟨x, hS⟩] at hz ⊢
        change _ * _ = _
        rw [hz, zero_mul, zeroExtension_of_not_mem p (fun h => hx ⟨hS, h⟩)]
      · rw [zeroExtension_of_not_mem g hS]
        by_cases heS : x ∈ e.source
        · rw [zeroExtension_apply _ ⟨x, heS⟩] at hpz ⊢
          change 0 = zeroExtension f (e x) * _
          rw [hpz, zero_mul]
        · exact (zeroExtension_of_not_mem p heS).symm
  exact ⟨(proper_congr hgp).1.mpr hpi.2,
    (proper_congr hgp).2.trans (hsub.2.2.2.2.2 (Or.inl hFi)).symm |>.trans
      (proper_congr hF).2⟩

/-- Localize a discontinuous proper coefficient with continuous weights. -/
lemma proper_decomposition {k : ℕ} (hkpos : 0 < k) {S : Set (E k)}
    [LocallyCompactSpace S] {ι : Type} (U : ι → Set S) (hU : ∀ i, IsOpen (U i))
    (f : S → ℝ) (hf : ProperIntegrable f) (hk : HasCompactSupport f)
    (hc : tsupport f ⊆ ⋃ i, U i) :
    ∃ (s : Finset ι) (F : s → S → ℝ),
      (∀ i, ProperIntegrable (F i) ∧ HasCompactSupport (F i) ∧ tsupport (F i) ⊆ U i) ∧
      f = fun x => ∑ i, F i x := by
  classical
  obtain ⟨s, hs⟩ := hk.elim_finite_subcover U hU hc
  have hcover : tsupport f ⊆ ⋃ i : s, U i := by simpa only [iUnion_subtype] using hs
  obtain ⟨ρ, hρ, _⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hk (fun i : s => U i) (fun i => hU i) (locallyFinite_of_finite _) hcover
  refine ⟨s, fun i x => f x * ρ i x, ?_, ?_⟩
  · intro i
    exact ⟨proper_mul_continuous hkpos hf hk _ (ρ i).continuous, hk.mul_right,
      tsupport_mul_subset_right.trans (hρ i)⟩
  · funext x
    by_cases hx : x ∈ tsupport f
    · have ht : ∑ i : s, ρ i x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [← Finset.mul_sum, ht, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Absolute substitution for compactly supported proper Riemann coefficients
on a chart overlap, allowing both genuine flat faces and Jordan jumps. -/
lemma proper_overlap_unsigned {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hkpos : 0 < k) (c d : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hkn : k ≤ n)
    {f : chartOverlap d c → ℝ} (hf : ProperIntegrable f) (hk : HasCompactSupport f) :
    let g : chartOverlap c d → ℝ := fun x => f (overlapHomeomorph c d x) *
      |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det|
    ProperIntegrable g ∧ coefficientIntegral g = coefficientIntegral f := by
  let T := chartOverlap d c
  let S := chartOverlap c d
  have hext (y : T) := D04.DirectedSubstitution.local_transition_diffeomorph c d hr hkn
    (D04.EmbeddedChart.transition_mem d c y.property)
  choose e hae he hei heq hd using hext
  let U : T → Set T := fun y => {z | chartTransition d c z ∈ (e y).source}
  have hU y : IsOpen (U y) :=
    (e y).open_source.preimage (D04.EmbeddedChart.transition_continuous d c).domRestrict
  let : LocallyCompactSpace T := D04.DirectedSubstitution.parameter_locallyCompact d.half
    (D04.DirectedSubstitution.overlap_parameter_domain d c)
  obtain ⟨s, F, hF, hsum⟩ := proper_decomposition hkpos U hU f hf hk
    (fun y _ => mem_iUnion.mpr ⟨y, hae y⟩)
  let G : s → S → ℝ := fun i x => F i (overlapHomeomorph c d x) *
    |(fderivWithin ℝ (chartTransition c d) S x).det|
  have hG i : ProperIntegrable (G i) ∧ coefficientIntegral (G i) = coefficientIntegral (F i) :=
    local_proper_unsigned c d (e i.val) (he i.val) (hei i.val) (heq i.val) (hd i.val)
      (hF i).1 (hF i).2.1 (fun y hy => (hF i).2.2 hy)
  have hg : (fun x : S => f (overlapHomeomorph c d x) *
      |(fderivWithin ℝ (chartTransition c d) S x).det|) = fun x => ∑ i, G i x := by
    funext x
    rw [congrFun hsum (overlapHomeomorph c d x), Finset.sum_mul]
  dsimp only
  rw [hg]
  refine ⟨(proper_sum G (fun i => (hG i).1)).1, ?_⟩
  rw [(proper_sum G (fun i => (hG i).1)).2]
  calc
    ∑ i, coefficientIntegral (G i) = ∑ i, coefficientIntegral (F i) :=
      Finset.sum_congr rfl (fun i _ => (hG i).2)
    _ = coefficientIntegral f :=
      (proper_sum F (fun i => (hF i).1)).2.symm.trans (congrArg coefficientIntegral hsum.symm)

lemma zeroExtension_restrict {k : ℕ} {S T : Set (E k)} (hST : S ⊆ T)
    (f : T → ℝ) (hk : HasCompactSupport f) (hs : Subtype.val '' tsupport f ⊆ S) :
    zeroExtension (fun x : S => f ⟨x, hST x.property⟩) = zeroExtension f := by
  funext x
  by_cases hx : x ∈ S
  · rw [zeroExtension_apply _ ⟨x, hx⟩, zeroExtension_apply f ⟨x, hST hx⟩]
  · rw [zeroExtension_of_not_mem _ hx]
    symm
    apply image_eq_zero_of_notMem_tsupport
    rw [D04.Localization.zeroExtension_tsupport hk]
    exact fun h => hx (hs h)

lemma proper_chart_transfer {n : ℕ} {M : Set (E n)} (hM : IsEmbeddedManifold 1 2 M)
    (c d : EmbeddedChart 1 2 n M) (a : c.source → ℝ) (b : d.source → ℝ)
    (ha : HasCompactSupport a) (hb : HasCompactSupport b) (hbi : ProperIntegrable b)
    (has : ∀ u ∈ tsupport a, c.toFun u ∈ d.ambient)
    (hbs : ∀ u ∈ tsupport b, d.toFun u ∈ c.ambient)
    (he : ∀ u : chartOverlap c d,
      a ⟨u, u.property.1⟩ = b ⟨chartTransition c d u,
        (D04.EmbeddedChart.transition_mem c d u.property).1⟩ *
          |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det|) :
    ProperIntegrable a ∧ coefficientIntegral a = coefficientIntegral b := by
  have hsa : Subtype.val '' tsupport a ⊆ chartOverlap c d := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u.property, has u hu⟩
  have hsb : Subtype.val '' tsupport b ⊆ chartOverlap d c := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u.property, hbs u hu⟩
  obtain ⟨hB, hkB, hvB⟩ := proper_restrict inter_subset_left hbi hb hsb
  have hA := zeroExtension_restrict inter_subset_left a ha hsa
  have hc := proper_overlap_unsigned (by norm_num) c d hM.1 hM.2.1 hB hkB
  have hfun : (fun u : chartOverlap c d => a ⟨u, u.property.1⟩) =
      fun u : chartOverlap c d => b ⟨(overlapHomeomorph c d u),
        (overlapHomeomorph c d u).property.1⟩ *
          |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det| := funext he
  have hEq := proper_congr hA
  refine ⟨hEq.1.mp ?_, hEq.2.symm.trans ?_⟩
  · change ProperIntegrable (fun u : chartOverlap c d => a ⟨u, u.property.1⟩)
    exact hfun.symm ▸ hc.1
  · exact (congrArg (fun t : (chartOverlap c d → ℝ) => coefficientIntegral t) hfun).trans
      (hc.2.trans hvB)

lemma piece_image_compact {n : ℕ} {M : Set (E n)} (p : ChartPiece M) :
    IsCompact (pieceImage p) :=
  p.compact.image_of_continuousOn (p.chart.continuous_toFun.mono p.subset_source)

lemma piece_image_source {n : ℕ} {M : Set (E n)} (p : ChartPiece M)
    (u : p.chart.source) : p.chart.toFun u ∈ pieceImage p ↔ (u : E 2) ∈ p.domain := by
  constructor
  · rintro ⟨v, hv, he⟩
    have h := congrArg p.chart.invFun he
    rw [p.chart.left_inv v (p.subset_source hv), p.chart.left_inv u u.property] at h
    exact h ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- A piece coefficient expressed in any chart; sharp domain membership is
retained instead of replacing it by a continuous weight. -/
def pieceChartCoefficient {n : ℕ} {M : Set (E n)} (p : ChartPiece M)
    (f : M → ℝ) (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) : c.source → ℝ :=
  fun u => if c.toFun u ∈ pieceImage p then w (c.toFun u) * densityCoefficient f c u else 0

lemma pieceChartCoefficient_support {n : ℕ} {M : Set (E n)} (p : ChartPiece M)
    (f : M → ℝ) (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) :
    tsupport (pieceChartCoefficient p f c w) ⊆ c.toFun ∘ Subtype.val ⁻¹' pieceImage p := by
  apply closure_minimal _
    ((piece_image_compact p).isClosed.preimage
      (c.continuous_toFun.comp_continuous continuous_subtype_val (fun u => u.property)))
  intro u hu
  by_contra hn
  change c.toFun u ∉ pieceImage p at hn
  exact hu (by simp [pieceChartCoefficient, hn])

lemma pieceChartCoefficient_weight_support {n : ℕ} {M : Set (E n)} (p : ChartPiece M)
    (f : M → ℝ) (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) :
    tsupport (pieceChartCoefficient p f c w) ⊆
      tsupport (fun u : c.source => w (c.toFun u)) := by
  apply closure_mono
  intro u hu
  by_contra hn
  have hz : w (c.toFun u) = 0 := notMem_support.mp hn
  exact hu (by simp [pieceChartCoefficient, hz])

lemma pieceChartCoefficient_transition {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 2 M) (p : ChartPiece M) (f : M → ℝ)
    (w : E n → ℝ) (c d : EmbeddedChart 1 2 n M) (u : chartOverlap c d) :
    pieceChartCoefficient p f c w ⟨u, u.property.1⟩ =
      pieceChartCoefficient p f d w ⟨chartTransition c d u,
        (D04.EmbeddedChart.transition_mem c d u.property).1⟩ *
          |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det| := by
  have hp : d.toFun (chartTransition c d u) = c.toFun u :=
    d.right_inv _ ⟨(c.map_source u.property.1).1, u.property.2⟩
  dsimp only [pieceChartCoefficient]
  rw [hp]
  split_ifs with h
  · rw [D04.ManifoldIntegralIndependence.densityCoefficient_transition hM f c d u]
    ring
  · exact (zero_mul _).symm

lemma piece_own_chart {n : ℕ} {M : Set (E n)} (hM : IsEmbeddedManifold 1 2 M)
    (p : ChartPiece M) (f : M → ℝ) (hf : Continuous f)
    (w : E n → ℝ) (hw : Continuous w) :
    let b := pieceChartCoefficient p f p.chart w
    ProperIntegrable b ∧ HasCompactSupport b ∧
      coefficientIntegral b = pieceIntegral p (fun x => w x * f x) := by
  let g : M → ℝ := fun x => w x * f x
  let b := pieceChartCoefficient p f p.chart w
  have hg : Continuous g := (hw.comp continuous_subtype_val).mul hf
  have hi := piece_integrable hM p g hg
  have he : zeroExtension b = zeroExtension (pieceCoefficient p g) := by
    funext x
    by_cases hx : x ∈ p.domain
    · rw [zeroExtension_apply _ ⟨x, p.subset_source hx⟩, zeroExtension_apply _ ⟨x, hx⟩]
      have hxI := (piece_image_source p ⟨x, p.subset_source hx⟩).mpr hx
      simp only [b, pieceChartCoefficient, hxI, ite_true, pieceCoefficient, densityCoefficient, g, chartPoint]
      ring
    · rw [zeroExtension_of_not_mem _ hx]
      by_cases hS : x ∈ p.chart.source
      · rw [zeroExtension_apply _ ⟨x, hS⟩]
        have hxI := mt (piece_image_source p ⟨x, hS⟩).mp hx
        simp [b, pieceChartCoefficient, hxI]
      · exact zeroExtension_of_not_mem b hS
  have hs : support (zeroExtension b) ⊆ p.domain := by
    rw [he]
    intro x hx
    by_contra hn
    exact hx (zeroExtension_of_not_mem _ hn)
  obtain ⟨Q, hQ, hQi⟩ := hi.2
  have hb : ProperIntegrable b :=
    ⟨p.compact.isBounded.subset hs, Q, (closure_mono hs).trans hQ, he ▸ hQi⟩
  have hK : IsCompact (Subtype.val ⁻¹' p.domain : Set p.chart.source) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using p.subset_source)).mpr p.compact
  have hbK : HasCompactSupport b := hK.of_isClosed_subset (isClosed_tsupport _) (by
    intro u hu
    exact (piece_image_source p u).mp (pieceChartCoefficient_support p f p.chart w hu))
  refine ⟨hb, hbK, ?_⟩
  have hv := (coefficientIntegral_eq_on_box hb Q ((closure_mono hs).trans hQ)).choose_spec
  have hv' := D04.JordanRegions.integral_eq_on_enclosing_box (pieceCoefficient p g) hi hQ hQi
  change coefficientIntegral b = regionIntegral (pieceCoefficient p g)
  rw [hv]
  change lowerIntegral (zeroExtension b) Q = _
  rw [he]
  exact hv'.symm

lemma piece_chart_comparison {n : ℕ} {M : Set (E n)} (hM : IsEmbeddedManifold 1 2 M)
    (p : ChartPiece M) (f : M → ℝ) (hf : Continuous f)
    (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) (hw : Continuous w)
    (hwK : IsCompact (tsupport (fun x : M => w x)))
    (hwc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    ProperIntegrable (pieceChartCoefficient p f c w) ∧
      coefficientIntegral (pieceChartCoefficient p f c w) =
        pieceIntegral p (fun x => w x * f x) := by
  obtain ⟨hbi, hbk, hvb⟩ := piece_own_chart hM p f hf w hw
  have hweight (d : EmbeddedChart 1 2 n M) :
      tsupport (pieceChartCoefficient p f d w) ⊆
        chartPoint d ⁻¹' tsupport (fun x : M => w x) := by
    apply (pieceChartCoefficient_weight_support p f d w).trans
    apply closure_minimal
    · intro u hu
      exact subset_tsupport (fun x : M => w x) hu
    · exact (isClosed_tsupport _).preimage (D04.ManifoldIntegral.chartPoint_continuous d)
  have hak : HasCompactSupport (pieceChartCoefficient p f c w) :=
    (D04.ManifoldIntegral.chart_weight_compact c w hwK hwc).of_isClosed_subset
      (isClosed_tsupport _) (pieceChartCoefficient_weight_support p f c w)
  have h := proper_chart_transfer hM c p.chart _ _ hak hbk hbi
    (fun u hu => by
      obtain ⟨v, hv, he⟩ := pieceChartCoefficient_support p f c w hu
      change p.chart.toFun v = c.toFun u at he
      rw [← he]
      exact (p.chart.map_source (p.subset_source hv)).2)
    (fun u hu => hwc (hweight p.chart hu))
    (pieceChartCoefficient_transition hM p f w c p.chart)
  exact ⟨h.1, h.2.trans hvb⟩

lemma piece_localization {n : ℕ} {M : Set (E n)} (hM : IsEmbeddedManifold 1 2 M)
    (p : ChartPiece M) (f : M → ℝ) (hf : Continuous f)
    {ι : Type} [Fintype ι] (w : ι → E n → ℝ) (hw : ∀ i, Continuous (w i))
    (hs : ∀ x : M, f x ≠ 0 → ∑ i, w i x = 1) :
    pieceIntegral p f = ∑ i, pieceIntegral p (fun x => w i x * f x) := by
  have hone := piece_own_chart hM p f hf (fun _ => 1) continuous_const
  have hpart i := piece_own_chart hM p f hf (w i) (hw i)
  have he : pieceChartCoefficient p f p.chart (fun _ => 1) =
      fun u => ∑ i, pieceChartCoefficient p f p.chart (w i) u := by
    funext u
    by_cases hI : p.chart.toFun u ∈ pieceImage p
    · simp only [pieceChartCoefficient, hI, ite_true, one_mul]
      by_cases hzero : f (chartPoint p.chart u) = 0
      · simp [densityCoefficient, hzero]
      · have hsum := hs (chartPoint p.chart u) hzero
        change ∑ i, w i (p.chart.toFun u) = 1 at hsum
        rw [← Finset.sum_mul, hsum, one_mul]
    · simp [pieceChartCoefficient, hI]
  have hsum := (proper_sum (fun i => pieceChartCoefficient p f p.chart (w i))
    (fun i => (hpart i).1)).2
  have hone' : coefficientIntegral (pieceChartCoefficient p f p.chart (fun _ => 1)) =
      pieceIntegral p f := by simpa only [one_mul] using hone.2.2
  rw [← hone', he, hsum]
  exact Finset.sum_congr rfl (fun i _ => (hpart i).2.2)

lemma proper_integral_eq_off_null {S : Set (E 2)} {a b : S → ℝ}
    (ha : ProperIntegrable a) (hb : ProperIntegrable b)
    {Z : Set (E 2)} (hZ : Specs.D04.C06.NullCovers.Model.Null Z)
    (he : ∀ x, x ∉ Z → zeroExtension a x = zeroExtension b x) :
    coefficientIntegral a = coefficientIntegral b := by
  obtain ⟨Q, hQ⟩ := (D04.JordanRegions.encloses_exists_iff_bounded
    (support (zeroExtension a) ∪ support (zeroExtension b))).mpr (ha.1.union hb.1)
  obtain ⟨hia, hva⟩ := coefficientIntegral_eq_on_box ha Q ((closure_mono subset_union_left).trans hQ)
  obtain ⟨hib, hvb⟩ := coefficientIntegral_eq_on_box hb Q ((closure_mono subset_union_right).trans hQ)
  rw [hva, hvb]
  exact D04.ExceptionalSets.integral_eq_of_eq_off_null (by norm_num) hia hib hZ
    (fun x _ hx => he x hx)

lemma chart_piece_sum {n : ℕ} {M : Set (E n)} (hM : IsEmbeddedManifold 1 2 M)
    (f : M → ℝ) (hf : Continuous f) {m : ℕ} (p : Fin m → ChartPiece M)
    (hc : (⋃ i, pieceImage (p i)) = M)
    (hn : ∀ i j, i ≠ j → AreaNull M (pieceImage (p i) ∩ pieceImage (p j)))
    (c : EmbeddedChart 1 2 n M) (w : E n → ℝ) (hw : Continuous w)
    (hwK : IsCompact (tsupport (fun x : M => w x)))
    (hwc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    coefficientIntegral (localizedDensityCoefficient f c w) =
      ∑ i, pieceIntegral (p i) (fun x => w x * f x) := by
  let B i := pieceChartCoefficient (p i) f c w
  have hB i := piece_chart_comparison hM (p i) f hf c w hw hwK hwc
  have hsum := proper_sum B (fun i => (hB i).1)
  let Z : Set (E 2) := ⋃ q : Fin m × Fin m,
    if q.1 = q.2 then ∅ else
      c.source ∩ c.toFun ⁻¹' (pieceImage (p q.1) ∩ pieceImage (p q.2))
  have hZ : Specs.D04.C06.NullCovers.Model.Null Z := by
    apply D04.NullCovers.null_iUnion_countable
    intro q
    split_ifs with h
    · exact D04.ExceptionalSets.null_empty
    · exact hn q.1 q.2 h c
  have hAi := (D04.ManifoldIntegral.localized_coefficient_integrable c w
    (densityCoefficient f c) hw
    (D04.ManifoldIntegralIndependence.densityCoefficient_continuous hM f hf c) hwK hwc).2.2
  have heq : coefficientIntegral (localizedDensityCoefficient f c w) =
      coefficientIntegral (fun u => ∑ i, B i u) := by
    apply proper_integral_eq_off_null hAi hsum.1 hZ
    intro x hx
    by_cases hS : x ∈ c.source
    · rw [zeroExtension_apply _ ⟨x, hS⟩, zeroExtension_apply _ ⟨x, hS⟩]
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hc.ge (c.map_source hS).1)
      have hother (i : Fin m) (hij : i ≠ j) : c.toFun x ∉ pieceImage (p i) := by
        intro hi
        apply hx
        apply mem_iUnion.mpr
        exact ⟨(i, j), by simp only [hij, ite_false, mem_inter_iff, mem_preimage]; exact ⟨hS, hi, hj⟩⟩
      rw [Finset.sum_eq_single j]
      · simp only [B, pieceChartCoefficient, hj, ite_true]
      · intro i _ hij
        simp [B, pieceChartCoefficient, hother i hij]
      · simp
    · rw [zeroExtension_of_not_mem _ hS, zeroExtension_of_not_mem _ hS]
  rw [heq, hsum.2]
  exact Finset.sum_congr rfl (fun i _ => (hB i).2)

end PieceAssembly

theorem finite_piece_additivity : Specs.D04.C10.SurfaceAssembly.finite_piece_additivityType := by
  intro n M hM hc f hf m p hcover hnull
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport f) (compact_support hc f)
  have hsum (x : M) (hx : f x ≠ 0) : ∑ i, P.weight i x = 1 := by
    obtain ⟨V, _, hV, hsum⟩ := P.partition.2.2.2.1
    exact hsum x (hV (subset_tsupport f hx))
  rw [scalar_chart_formula hM hc f hf P Subset.rfl]
  calc
    _ = ∑ j, ∑ i, pieceIntegral (p i) (fun x => P.weight j x * f x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact PieceAssembly.chart_piece_sum hM f hf p hcover hnull (P.chart j) (P.weight j)
        (P.partition.1 j).continuous (P.partition.2.2.1 j).1 (P.partition.2.2.1 j).2
    _ = ∑ i, ∑ j, pieceIntegral (p i) (fun x => P.weight j x * f x) := Finset.sum_comm
    _ = ∑ i, pieceIntegral (p i) f := by
      apply Finset.sum_congr rfl
      intro i _
      exact (PieceAssembly.piece_localization hM (p i) f hf P.weight
        (fun j => (P.partition.1 j).continuous) hsum).symm

theorem finite_flux_piece_additivity :
    Specs.D04.C10.SurfaceAssembly.finite_flux_piece_additivityType := by
  intro M hM hc N F hF m p hcover hnull
  exact finite_piece_additivity hM hc (fun x => ⟪F x, N.toFun x⟫)
    (hF.inner N.continuous) p hcover hnull

abbrev surfaceIntegral := @Specs.D04.C10.SurfaceAssembly.Model.surfaceIntegral
abbrev UnitNormalField := Specs.D04.C10.SurfaceAssembly.Model.UnitNormalField
abbrev surfaceFlux := @Specs.D04.C10.SurfaceAssembly.Model.surfaceFlux
abbrev surfaceFluxForm := @Specs.D04.C10.SurfaceAssembly.Model.surfaceFluxForm
abbrev surfaceChartNormal := @Specs.D04.C10.SurfaceAssembly.Model.surfaceChartNormal
abbrev normalChartSign := @Specs.D04.C10.SurfaceAssembly.Model.normalChartSign

abbrev AreaNull := @Specs.D04.C10.SurfaceAssembly.Model.AreaNull
abbrev ChartPiece := @Specs.D04.C10.SurfaceAssembly.Model.ChartPiece
abbrev pieceImage := @Specs.D04.C10.SurfaceAssembly.Model.pieceImage
abbrev pieceCoefficient := @Specs.D04.C10.SurfaceAssembly.Model.pieceCoefficient
abbrev pieceIntegral := @Specs.D04.C10.SurfaceAssembly.Model.pieceIntegral

end D04SurfaceAssembly
