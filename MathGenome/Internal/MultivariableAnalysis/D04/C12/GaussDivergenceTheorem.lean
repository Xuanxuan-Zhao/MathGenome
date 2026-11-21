import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GaussDivergenceTheorem
import MathGenome.Internal.MultivariableAnalysis.D04.C12.RegularDomainRiemannManifoldBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FinitePiecewiseStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C14.MetricTopFormsAndDensities
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OutwardFirstBoundaryOrientation

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Function Topology
open scoped ContDiff BigOperators Classical
namespace D04.Gauss
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.GaussDivergenceTheorem
open Specs.D04.C12.GaussDivergenceTheorem.Model
local notation "divergence" => Specs.D04.C11.EuclideanVectorOperators.Model.divergence
local notation "exteriorDerivative" => Specs.D04.C13.ExteriorDerivative.Model.exteriorDerivative
local notation "intrinsicBoundary" => Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary
local notation "cellExtension" => Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension

theorem exterior_flux : exterior_fluxType := D04.Dictionary.exterior_flux_divergence

/-- An alternating (d+1)-covector vanishes on a d-dimensional subspace. -/
lemma top_vanishes_on_hyperplane {d : ℕ} (T : Submodule ℝ (E (d+1)))
    (hT : Module.finrank ℝ T = d) (w : Fin (d+1) → T) :
    omega (d+1) (fun i => (w i).val) = 0 := by
  apply ((omega (d+1)).compLinearMap T.subtype).map_linearDependent w
  intro h
  have := h.fintype_card_le_finrank
  simp only [Fintype.card_fin, hT] at this
  omega

/-- The tangential component of F contributes zero to contraction with volume. -/
lemma flux_normal_factor {d : ℕ} {M : Set (E (d+1))}
    (hM : IsEmbeddedManifold 1 (d+1) M)
    (x : intrinsicBoundary 1 (d+1) M) (ν : E (d+1))
    (hν : IsOutwardUnitConormal 1 d M x ν) (F : E (d+1))
    (v : Fin d → tangentSpace 1 d (intrinsicBoundary 1 (d+1) M) x) :
    omega (d+1) (Fin.cons F (fun i => (v i).val)) =
      inner ℝ F ν * omega (d+1) (Fin.cons ν (fun i => (v i).val)) := by
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold hM)).1
  let T := tangentSpace 1 d (intrinsicBoundary 1 (d+1) M) x
  have hT : Module.finrank ℝ T = d := D04.tangentSpace_finrank hbM x x.property
  have hF : F ∈ tangentSpace 1 (d+1) M x := by
    rw [D04.RegularDomainBridge.tangentSpace_eq_top hM ⟨x, x.property.1⟩]
    trivial
  obtain ⟨t, ht⟩ := D04BoundaryOrientation.conormal_spans hM hν F hF
  have he : inner ℝ F ν + t = 0 := by
    have hh := hν.2.2.1 (F + t • ν) ht
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hν.2.1] at hh
    simpa only [one_pow, mul_one, real_inner_comm] using hh
  have hz := top_vanishes_on_hyperplane T hT (Fin.cons ⟨F + t • ν, ht⟩ v)
  have hv : (fun i => ((Fin.cons (⟨F + t • ν, ht⟩ : T) v : Fin (d+1) → T) i).val) =
      Fin.cons (F + t • ν) (fun i => (v i).val) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [hv] at hz
  change ((omega (d+1)).curryLeft (F + t • ν)) (fun i => (v i).val) = 0 at hz
  rw [map_add, map_smul] at hz
  change omega (d+1) (Fin.cons F (fun i => (v i).val)) +
    t * omega (d+1) (Fin.cons ν (fun i => (v i).val)) = 0 at hz
  have htval : t = -inner ℝ F ν := by linarith
  rw [htval] at hz
  linarith

/-- A unit normal adjoined to an orthonormal tangent frame has unit Gram density. -/
lemma gram_cons_unit {d : ℕ} (T : Submodule ℝ (E (d+1)))
    (ν : E (d+1)) (hν : ‖ν‖ = 1) (hperp : ∀ w : T, inner ℝ ν w = 0)
    (b : OrthonormalBasis (Fin d) ℝ T) :
    gramDensity (Fin.cons ν (fun i => (b i).val)) = 1 := by
  have hon : Orthonormal ℝ (Fin.cons ν (fun i => (b i).val)) := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [real_inner_self_eq_norm_sq, hν]
      | succ j => simp [hperp, (Fin.succ_ne_zero j).symm]
    | succ i =>
      cases j using Fin.cases with
      | zero => simp [real_inner_comm, hperp]
      | succ j => simpa using (orthonormal_iff_ite.mp b.orthonormal i j)
  change Real.sqrt (Matrix.gram ℝ (Fin.cons ν (fun i => (b i).val))).det = 1
  rw [Matrix.gram_eq_one_iff_orthonormal.mpr hon, Matrix.det_one, Real.sqrt_one]

/-- On a positive orthonormal boundary basis, the outward-first ambient
volume is exactly one, with no orientation or Gram factor suppressed. -/
lemma outward_volume_normalized {d : ℕ} {M : Set (E (d+2))}
    (o : PositiveManifoldOrientation 1 (d+2) M) (ho : IsAmbientOrientation o)
    (bO : PositiveManifoldOrientation 1 (d+1) (intrinsicBoundary 1 (d+2) M))
    (hO : OutwardFirst (d+1) o bO)
    (x : intrinsicBoundary 1 (d+2) M) (ν : E (d+2))
    (hν : IsOutwardUnitConormal 1 (d+1) M x ν)
    (b : OrthonormalBasis (Fin (d+1)) ℝ
      (tangentSpace 1 (d+1) (intrinsicBoundary 1 (d+2) M) x))
    (hb : b.toBasis.orientation = bO.atPoint x x.property) :
    omega (d+2) (Fin.cons ν (fun i => (b i).val)) = 1 := by
  obtain ⟨ν', _, hn', hpos⟩ := hO
  have he : ν = ν' x :=
    (D04BoundaryOrientation.conormal_exists_unique o.manifold x x.property).unique hν (hn' x)
  obtain ⟨B, hB0, hBs, hBor⟩ := (hpos x b.toBasis).mp hb
  have htuple : (fun i => (B i).val) = Fin.cons ν (fun i => (b i).val) := by
    funext i
    cases i using Fin.cases with
    | zero => exact hB0.trans he.symm
    | succ i => exact hBs i
  have hp := (ho ⟨x, x.property.1⟩ B).mp hBor
  rw [htuple] at hp
  letI : Fact (Module.finrank ℝ (E (d+2)) = d+2) := ⟨by simp [E]⟩
  have ha := D04.Dictionary.metricTopForm_gram (standardBasis (d+2)).orientation
    (Fin.cons ν (fun i => (b i).val))
  rw [← D04.Dictionary.omega_metricTopForm] at ha
  change |omega (d+2) (Fin.cons ν (fun i => (b i).val))| =
    gramDensity (Fin.cons ν (fun i => (b i).val)) at ha
  rw [gram_cons_unit _ ν hν.2.1 (fun w => hν.2.2.1 w w.property) b, abs_of_pos hp] at ha
  exact ha

lemma boundary_flux_positive {d : ℕ} {M : Set (E (d+2))}
    (o : PositiveManifoldOrientation 1 (d+2) M) (ho : IsAmbientOrientation o)
    (bO : PositiveManifoldOrientation 1 (d+1) (intrinsicBoundary 1 (d+2) M))
    (hO : OutwardFirst (d+1) o bO)
    (ν : intrinsicBoundary 1 (d+2) M → E (d+2))
    (hν : ∀ x : intrinsicBoundary 1 (d+2) M, IsOutwardUnitConormal 1 (d+1) M x (ν x))
    (F : E (d+2) → E (d+2)) :
    tangentRestriction 1 (d+1) (intrinsicBoundary 1 (d+2) M) (fluxForm F) =
      fun x => normalFlux F ν x • metricVolume bO.atPoint x := by
  funext x
  letI : Fact (Module.finrank ℝ
      (tangentSpace 1 (d+1) (intrinsicBoundary 1 (d+2) M) x) = d+1) :=
    ⟨D04.tangentSpace_finrank bO.manifold x x.property⟩
  let b := (bO.atPoint x x.property).finOrthonormalBasis (Nat.succ_pos d)
    (D04.tangentSpace_finrank bO.manifold x x.property)
  have hb : b.toBasis.orientation = bO.atPoint x x.property :=
    (bO.atPoint x x.property).finOrthonormalBasis_orientation (Nat.succ_pos d) _
  suffices he : (tangentRestriction 1 (d+1) (intrinsicBoundary 1 (d+2) M)
      (fluxForm F) x) b.toBasis =
      (normalFlux F ν x • metricVolume bO.atPoint x) b.toBasis by
    rw [(tangentRestriction 1 (d+1) (intrinsicBoundary 1 (d+2) M)
      (fluxForm F) x).eq_smul_basis_det b.toBasis,
      (normalFlux F ν x • metricVolume bO.atPoint x).eq_smul_basis_det b.toBasis, he]
  change fluxForm F x (fun i => (b i).val) = _
  rw [D04.Dictionary.fluxForm_volume, flux_normal_factor o.manifold x (ν x) (hν x),
    outward_volume_normalized o ho bO hO x (ν x) (hν x) b hb, mul_one]
  change _ = normalFlux F ν x * metricVolume bO.atPoint x b
  rw [D04MetricDensity.metricVolume_normalized bO.manifold bO.atPoint x b hb, mul_one]
  rfl

lemma boundary_point_normal {M : Set (E 1)}
    (o : PositiveManifoldOrientation 1 1 M) (ho : IsAmbientOrientation o)
    (s : ZeroManifoldOrientation (intrinsicBoundary 1 1 M)) (hO : OutwardFirst 0 o s)
    (x : intrinsicBoundary 1 1 M) (ν : E 1)
    (hν : IsOutwardUnitConormal 1 0 M x ν) : (s x).val = ν 0 := by
  obtain ⟨ν', _, hn', hpos⟩ := hO
  have he : ν = ν' x :=
    (D04BoundaryOrientation.conormal_exists_unique o.manifold x x.property).unique hν (hn' x)
  have hp : PositiveOutwardLine o x ν ↔ 0 < ν 0 := by
    obtain ⟨B, hB⟩ := D04BoundaryOrientation.line_basis_exists o.manifold x ν hν
    have htest : B.orientation = o.atPoint x x.property.1 ↔ 0 < ν 0 := by
      have hh := ho ⟨x, x.property.1⟩ B
      have hh' : omega 1 (fun i => (B i).val) = ν 0 := by
        change Matrix.det (fun i j : Fin 1 => (B j).val i) = ν 0
        rw [Matrix.det_fin_one, hB]
      rwa [hh'] at hh
    constructor
    · rintro ⟨C, hC, hCo⟩
      have hCB : C = B := by
        apply DFunLike.ext
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact Subtype.ext (hC.trans hB.symm)
      exact htest.mp (hCB ▸ hCo)
    · intro h
      exact ⟨B, hB, htest.mpr h⟩
  have hs : (s x).val = 1 ↔ 0 < ν 0 := (hpos x).1.trans (he ▸ hp)
  have habs : |ν 0| = 1 := by
    have hn := hν.2.1
    simpa [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs] using hn
  rcases (s x).property with hh | hh
  · have hνp := hs.mp hh
    rw [abs_of_pos hνp] at habs
    exact hh.trans habs.symm
  · have hn : ¬ 0 < ν 0 := by
      intro h
      have := hs.mpr h
      linarith
    rw [abs_of_nonpos (not_lt.mp hn)] at habs
    rw [hh]
    linarith

theorem boundary_flux : boundary_fluxType := by
  intro d M o ho bO hO ν hν F
  cases d with
  | zero =>
    funext x
    ext v
    rw [show orientedMetric 0 bO x = zeroMetricVolume bO x from rfl]
    change fluxForm F x (fun i => (v i).val) =
      inner ℝ (F x) (ν x) * (bO x).val
    rw [D04.Dictionary.fluxForm_volume, flux_normal_factor o.manifold x (ν x) (hν x)]
    have he : omega 1 (Fin.cons (ν x) (fun i => (v i).val)) = ν x 0 := by
      change Matrix.det (fun i j : Fin 1 => ((Fin.cons (ν x) (fun i => (v i).val) : Fin 1 → E 1) j) i) = _
      rw [Matrix.det_fin_one]
      rfl
    rw [he, boundary_point_normal o ho bO hO x (ν x) (hν x)]
  | succ d => exact boundary_flux_positive o ho bO hO ν hν F

/-- Passing from a signed metric top form to the unsigned Gram-density
integral cancels the chart signs twice. The zero-dimensional case cancels
the independent point sign twice instead. -/
lemma metric_density_integral {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 d M) (hK : IsCompact M)
    (o : ManifoldOrientation 1 d M) (ρ : M → ℝ) (hρ : Continuous ρ) (I : ℝ)
    (hI : HasManifoldIntegral 1 d o (fun x => ρ x • orientedMetric d o x) I) :
    HasDensityIntegral (d := d) ρ I := by
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hK
  have hkρ : HasCompactSupport ρ := (isClosed_tsupport ρ).isCompact
  obtain ⟨Q⟩ := D04.ManifoldIntegral.chart_partition_exists hM (tsupport ρ) hkρ
  refine ⟨hρ, hkρ, ⟨Q⟩, ?_⟩
  intro P
  refine ⟨fun i => (D04.ManifoldIntegral.density_coefficients_integrable hM ρ hρ P i).2.2, ?_⟩
  cases d with
  | zero =>
    have hv : densityIntegral ρ P = ∑ᶠ x : M, ρ x :=
      D04.ManifoldIntegralIndependence.density_zero_sum hM ρ hkρ P
    rw [hv]
    have hi := hI.2.2.2
    change (∑ᶠ x : M, (o x).val * (ρ x * (o x).val)) = I at hi
    have he : (fun x : M => (o x).val * (ρ x * (o x).val)) = ρ := by
      funext x
      rcases (o x).property with hx | hx <;> rw [hx] <;> ring
    rwa [he] at hi
  | succ d =>
    change PositiveManifoldOrientation 1 (d+1) M at o
    let η : TangentTopField 1 (d+1) M := fun x => ρ x • metricVolume o.atPoint x
    have hs : topSupport η = tsupport ρ := by
      change closure {x | η x ≠ 0} = closure (support ρ)
      congr 1
      ext x
      change ρ x • metricVolume o.atPoint x ≠ 0 ↔ ρ x ≠ 0
      apply smul_ne_zero_iff_left
      letI : Fact (Module.finrank ℝ (tangentSpace 1 (d+1) M x) = d+1) :=
        ⟨D04.tangentSpace_finrank hM x x.property⟩
      let b := (o.atPoint x x.property).finOrthonormalBasis (Nat.succ_pos d)
        (D04.tangentSpace_finrank hM x x.property)
      intro hz
      have hh := D04MetricDensity.metricVolume_normalized hM o.atPoint x b
        ((o.atPoint x x.property).finOrthonormalBasis_orientation (Nat.succ_pos d) _)
      rw [hz, zero_apply] at hh
      exact zero_ne_one hh
    change HasPositiveIntegral o η I at hI
    obtain ⟨S⟩ := hI.2.2.1
    have hcoef (c : EmbeddedChart 1 (d+1) n M) (u : c.source) :
        D04.ManifoldIntegralIndependence.signedCoefficient o η c u = densityCoefficient ρ c u := by
      have hm := congrArg (fun a : Covector (E (d+1)) (d+1) => a (standardBasis (d+1)))
        (D04MetricDensity.metricVolume_pullback hM (Nat.succ_pos d) o.atPoint c u u.property)
      have hsval := D04.Orientations.chartSign_values o.atPoint c hM.1 hM.2.1 u u.property
      change chartSign o.atPoint c u u.property *
        (ρ (chartPoint c u) * topCoefficient (metricVolume o.atPoint) c u) =
        ρ (chartPoint c u) * chartDensity c u
      change topCoefficient (metricVolume o.atPoint) c u =
        (chartSign o.atPoint c u u.property * chartDensity c u) *
          omega (d+1) (standardBasis (d+1)) at hm
      rw [show omega (d+1) (standardBasis (d+1)) = 1 from Module.Basis.det_self _, mul_one] at hm
      rw [hm]
      rcases hsval with h | h <;> rw [h] <;> ring
    have hv : orientedIntegral η S =
        ∑ i, coefficientIntegral (localizedDensityCoefficient ρ (S.chart i) (S.weight i)) := by
      change (∑ i, (S.sign i).val * coefficientIntegral
        (localizedTopCoefficient η (S.chart i) (S.weight i))) = _
      rw [D04.ManifoldIntegralIndependence.signed_expression o η hI.1 S]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext u
      change S.weight i ((S.chart i).toFun u) *
        D04.ManifoldIntegralIndependence.signedCoefficient o η (S.chart i) u = _
      rw [hcoef]
      rfl
    have hcmp := D04.ManifoldIntegralIndependence.density_comparison hM ρ hρ P S.toChartPartition
      Subset.rfl (by rw [hs])
    exact hcmp.trans (hv.symm.trans (hI.2.2.2 S).2)

lemma divergence_continuousOn {d : ℕ} (U : Set (E (d+1)))
    (F : E (d+1) → E (d+1)) (hU : IsOpen U) (hF : CrOn 1 U F) :
    ContinuousOn (divergence F) U := by
  have hβ := D04.Dictionary.fluxForm_isCr 1 U F hU hF
  have hdβ := D04.exteriorDerivative_continuous U (fluxForm F) hβ
  have hc := D04.LocalStokes.form_evaluation_continuous U
    (exteriorDerivative (fluxForm F)) hdβ (standardBasis (d+1))
  apply hc.congr
  intro x hx
  change divergence F x = exteriorDerivative (fluxForm F) x (standardBasis (d+1))
  erw [exterior_flux U F hU hF x hx]
  change divergence F x = divergence F x * omega (d+1) (standardBasis (d+1))
  rw [show omega (d+1) (standardBasis (d+1)) = 1 from Module.Basis.det_self _, mul_one]

lemma density_transport {d n : ℕ} {S T : Set (E n)} (h : S = T)
    (ρ : T → ℝ) (I : ℝ)
    (hi : HasDensityIntegral (d := d) (fun x : S => ρ ⟨x, h ▸ x.property⟩) I) :
    HasDensityIntegral (d := d) ρ I := by
  subst T
  exact hi

/-- Stokes applied to the actual contraction form, followed by the proved
volume and normal-density bridges. -/
theorem gauss : gaussType := by
  intro d D hD U F hU hDU hF
  obtain ⟨o, ho, hK, hM, hb, hJD, hJK, hn, hdef, hdata⟩ :=
    D04.RegularDomainBridge.regular_domain_interface hD
  have hdiv : Continuous (fun x : closure D => divergence F x) :=
    (divergence_continuousOn U F hU hF).comp_continuous continuous_subtype_val (fun x => hDU x.property)
  obtain ⟨hc, hkc, hpart, hiK, hiD, hval⟩ := hdata _ hdiv
  have hbulk : tangentRestriction 1 (d+1) (closure D) (exteriorDerivative (fluxForm F)) =
      volumeField (fun x : closure D => divergence F x) := by
    funext x
    change (exteriorDerivative (fluxForm F) x).compLinearMap _ = _
    erw [exterior_flux U F hU hF x (hDU x.property)]
    rfl
  obtain ⟨bO, hO, I, hI, hB⟩ := D04Stokes.ambient_stokes_compact o hK U (fluxForm F) hDU
    (D04.Dictionary.fluxForm_isCr 1 U F hU hF)
  rw [hbulk] at hI
  obtain ⟨P⟩ := hI.2.2.1
  have hvalI : I = regionIntegral (fun x : D => divergence F x) :=
    (hI.2.2.2 P).2.symm.trans (hval P).1
  let ν : intrinsicBoundary 1 (d+1) (closure D) → E (d+1) :=
    fun x => outwardNormal hD ⟨x, hb ▸ x.property⟩
  have hν (x : intrinsicBoundary 1 (d+1) (closure D)) :
      IsOutwardUnitConormal 1 d (closure D) x (ν x) := hn ⟨x, hb ▸ x.property⟩
  have heν : ν = D04BoundaryOrientation.outwardConormal hM := by
    funext x
    exact (D04BoundaryOrientation.conormal_exists_unique hM x x.property).unique (hν x)
      (D04BoundaryOrientation.outwardConormal_spec hM x)
  have hcν : Continuous ν := heν ▸ D04BoundaryOrientation.outwardConormal_continuous hM
  have hρ : Continuous (normalFlux F ν) :=
    ((D04.crOn_iff_contDiffOn 1 U F hU).mp hF).continuousOn.comp_continuous
      continuous_subtype_val (fun x => hDU x.property.1) |>.inner hcν
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold hM)).1
  have hbK : IsCompact (intrinsicBoundary 1 (d+1) (closure D)) := by
    exact hb.symm ▸ hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  rw [boundary_flux o ho bO hO ν hν F] at hB
  have hden := metric_density_integral hbM hbK bO (normalFlux F ν) hρ I hB
  rw [hvalI] at hden
  exact ⟨hiD, density_transport hb (normalFlux F (outwardNormal hD)) _ hden⟩

theorem gauss_endpoints : gauss_endpointsType := by
  intro D hD U F hU hDU hF
  have hg := (gauss hD U F hU hDU hF).2
  obtain ⟨hK, hM⟩ := D04.RegularDomainGeometry.closure_manifold hD
  have hb := D04.RegularDomainGeometry.intrinsic_boundary hD
  have hbM : IsEmbeddedManifold 1 0 (frontier D) := by
    have h := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold hM)).1
    exact hb ▸ h
  have hbK : IsCompact (frontier D) :=
    hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfin : (frontier D).Finite := D04.compact_zero_manifold_finite 1 (frontier D) hbM
    ((D04.compact_iff_isCompact (frontier D)).mpr hbK)
  refine ⟨hfin, ?_⟩
  letI := hfin.fintype
  obtain ⟨P⟩ := hg.2.2.1
  have heq := (hg.2.2.2 P).2
  rw [D04.ManifoldIntegralIndependence.density_zero_sum hbM _ hg.2.1 P] at heq
  rw [finsum_eq_sum_of_fintype] at heq
  apply heq.symm.trans
  apply Finset.sum_congr rfl
  intro x _
  change inner ℝ (F x) (outwardNormal hD x) = F x 0 * outwardNormal hD x 0
  rw [D04.inner_coordinates]
  simp [Fin.sum_univ_one]

/-- Gram's determinant for a unit normal and an arbitrary tangential frame. -/
lemma gram_cons_normal {d : ℕ} (ν : E (d+1)) (v : Fin d → E (d+1))
    (hn : ‖ν‖ = 1) (hp : ∀ i, inner ℝ ν (v i) = 0) :
    gramDensity (Fin.cons ν v) = gramDensity v := by
  change Real.sqrt (Matrix.gram ℝ (Fin.cons ν v)).det = Real.sqrt (Matrix.gram ℝ v).det
  congr 1
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin d, (Matrix.gram ℝ (Fin.cons ν v)) 0 j.succ = 0 := by
    intro j
    exact hp j
  simp [Matrix.gram_apply, hn, hp, real_inner_self_eq_norm_sq, Fin.succAbove_zero,
    Matrix.submatrix]
  rfl

/-- Algebraic flux on an oriented hyperplane frame. The hypotheses describe
a unit perpendicular vector and its orientation, and contain no integral
identity. The result includes d=0, with the empty Gram determinant equal to 1. -/
lemma frame_flux {d : ℕ} (F ν : E (d+1)) (v : Fin d → E (d+1))
    (hn : ‖ν‖ = 1) (hp : ∀ i, inner ℝ ν (v i) = 0) (s : ℝ)
    (hs : s = 1 ∨ s = -1)
    (ho : 0 < s * omega (d+1) (Fin.cons ν v)) :
    s * omega (d+1) (Fin.cons F v) = inner ℝ F ν * gramDensity v := by
  let T := (ℝ ∙ ν)ᗮ
  letI : Fact (Module.finrank ℝ (E (d+1)) = d+1) := ⟨by simp [E]⟩
  have hν0 : ν ≠ 0 := by intro h; simpa [h] using hn
  have hT : Module.finrank ℝ T = d := Submodule.finrank_orthogonal_span_singleton hν0
  have hv (i : Fin d) : v i ∈ T := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hp i)
  have ht : F - inner ℝ F ν • ν ∈ T := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
    simp [real_inner_comm]
  have hz := top_vanishes_on_hyperplane T hT
    (Fin.cons ⟨F - inner ℝ F ν • ν, ht⟩ (fun i => ⟨v i, hv i⟩))
  have htuple : (fun i => ((Fin.cons (⟨F - inner ℝ F ν • ν, ht⟩ : T)
      (fun i => (⟨v i, hv i⟩ : T)) : Fin (d+1) → T) i).val) =
      Fin.cons (F - inner ℝ F ν • ν) v := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [htuple] at hz
  change ((omega (d+1)).curryLeft (F - inner ℝ F ν • ν)) v = 0 at hz
  rw [map_sub, map_smul] at hz
  change omega (d+1) (Fin.cons F v) -
    inner ℝ F ν * omega (d+1) (Fin.cons ν v) = 0 at hz
  have hfactor := sub_eq_zero.mp hz
  have hg := D04.Dictionary.metricTopForm_gram (standardBasis (d+1)).orientation (Fin.cons ν v)
  rw [← D04.Dictionary.omega_metricTopForm] at hg
  change |omega (d+1) (Fin.cons ν v)| = gramDensity (Fin.cons ν v) at hg
  rw [gram_cons_normal ν v hn hp] at hg
  have habs : |s * omega (d+1) (Fin.cons ν v)| = |omega (d+1) (Fin.cons ν v)| := by
    rcases hs with h | h <;> simp [h]
  rw [abs_of_pos ho] at habs
  rw [hfactor, ← hg, ← habs]
  ring

open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

lemma cell_integral_congrOn {k n : ℕ} {O : Set (E n)} (c : Cell 1 k O)
    (α β : FormField n k) (heq : EqOn α β O) : cellIntegral c α = cellIntegral c β := by
  apply D04.Cells.lowerIntegral_congr
  intro x hx
  change α (cellExtension c x) _ = β (cellExtension c x) _
  have hm : cellExtension c x ∈ O := by
    change D04.Cells.cellExtension c x ∈ O
    rw [D04.Cells.extension_on_cube c ⟨x,hx⟩]
    exact (c.toFun ⟨x,hx⟩).property
  exact congrArg (fun a : Covector (E n) k => a _) (heq hm)

lemma representation_integral_congr {k n : ℕ} {K M O : Set (E n)}
    {o : PositiveManifoldOrientation 1 k M} (R : PieceRepresentation K M o O)
    (α β : FormField n k) (heq : EqOn α β O) (I : ℝ) :
    R.HasIntegral α I ↔ R.HasIntegral β I := by
  cases R with
  | manifold he inside =>
    have hr : Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) (M := M) α =
        Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1) (M := M) β := by
      funext x
      change (α x).compLinearMap _ = (β x).compLinearMap _
      exact congrArg (fun a : Covector (E n) k => a.compLinearMap _) (heq (inside (he.symm ▸ x.property)))
    change (∀ P, orientedIntegral _ P = I) ↔ (∀ P, orientedIntegral _ P = I)
    rw [hr]
  | cell c _ _ _ _ _ _ _ _ =>
    change cellIntegral c α = I ↔ cellIntegral c β = I
    rw [cell_integral_congrOn c α β heq]

lemma form_C0_congr {k n : ℕ} {O : Set (E n)} (α β : FormField n k)
    (ha : IsCrForm (some 0) O α) (heq : EqOn α β O) : IsCrForm (some 0) O β := by
  refine ⟨ha.1, ?_⟩
  intro J
  change ContinuousOn (fun x => coefficient (standardBasis n) (β x) J) O
  apply (ha.2 J).congr
  intro x hx
  exact congrArg (fun a : Covector (E n) k => coefficient (standardBasis n) a J) (heq hx).symm

/-- The geometric integral only uses values on its declared ambient domain.
This is proved for both original cell and manifold representations. -/
lemma geometric_integral_congr {k n : ℕ} {O : Set (E n)} (D : GeometricDecomposition k n O)
    (α β : FormField n k) (ha : IsCrForm (some 0) O α) (heq : EqOn α β O) :
    geometricUnionIntegral D α = geometricUnionIntegral D β := by
  choose I hI using D04.GeometricUnion.geometric_piece_integral_exists D α ha
  have hIβ i := (representation_integral_congr (D.representation i) α β heq (I i)).mp (hI i)
  have hcomp := D04.GeometricUnion.compatible_regular_refl D.toRegularDecomposition
  exact (D04.GeometricUnion.geometric_union_integral_eq_sum D D hcomp α ha I hI).trans
    (D04.GeometricUnion.geometric_union_integral_eq_sum D D hcomp β
      (form_C0_congr α β ha heq) I hIβ).symm

theorem geometric_cell_piecewise_gauss : geometric_cell_piecewise_gaussType := by
  intro k N L O c P hp outer left right b s hs hmatch hw hassembly hinj hrank Z hover F hO hF
  have hβ := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  obtain ⟨D, hD, hv⟩ := D04.FinitePiecewiseStokes.geometric_cell_piecewise_stokes
    c P hp outer left right b s hs hmatch hw hassembly hinj hrank Z hover (fluxForm F) hβ
  refine ⟨D, hD, ?_⟩
  apply (geometric_integral_congr D (exteriorDerivative (fluxForm F)) (divergenceVolume F)
    (D04.exteriorDerivative_continuous O (fluxForm F) hβ) ?_).symm.trans hv
  intro x hx
  exact exterior_flux O F hO hF x hx

theorem geometric_manifold_piecewise_gauss : geometric_manifold_piecewise_gaussType := by
  intro d q O M bO hbO m P s hreg Z hZ hrepeat hover hcover Zbulk hbulk l p e Q tSign b
    deltaOut hdout hOut hout deltaPair hdp hPair hpair F hO hF
  have hβ := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  obtain ⟨D, hD, hv⟩ := D04.FinitePiecewiseStokes.geometric_manifold_piecewise_stokes
    M bO hbO m P s hreg Z hZ hrepeat hover hcover Zbulk hbulk e Q tSign b deltaOut hdout hOut
      hout deltaPair hdp hPair hpair (fluxForm F) hβ
  refine ⟨D, hD, ?_⟩
  apply (geometric_integral_congr D (exteriorDerivative (fluxForm F)) (divergenceVolume F)
    (D04.exteriorDerivative_continuous O (fluxForm F) hβ) ?_).symm.trans hv
  intro x hx
  exact exterior_flux O F hO hF x hx

theorem geometric_manifold_piecewise_gauss_points : geometric_manifold_piecewise_gauss_pointsType := by
  intro q O M bO hbO l p e P s c hout hpair Z hover F hO hF
  have hβ := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  obtain ⟨D, hD, hv⟩ := D04.FinitePiecewiseStokes.geometric_manifold_piecewise_stokes_points
    M bO hbO e P s c hout hpair Z hover (fluxForm F) hβ
  refine ⟨D, hD, ?_⟩
  apply (geometric_integral_congr D (exteriorDerivative (fluxForm F)) (divergenceVolume F)
    (D04.exteriorDerivative_continuous O (fluxForm F) hβ) ?_).symm.trans hv
  intro x hx
  exact exterior_flux O F hO hF x hx

theorem patch_flux : patch_fluxType := by
  intro d O P F hO hF w hw s hs ν hn
  have hβ := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  have hi := D04.GeometricPatches.weighted_integrable P (fluxForm F)
    (D04.LocalStokes.form_C0 O _ hβ) w hw
  change s * regionIntegral (fun x : P.region =>
    Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.weightedCoefficient P w (fluxForm F) x) = _
  rw [← (D04.Orientation.regionIntegral_smul s hi).2]
  apply congrArg regionIntegral
  funext x
  obtain ⟨hunit, hperp, hpos⟩ := hn x x.property
  have he := frame_flux (F (P.map x)) (ν x)
    (fun i => fderiv ℝ P.map x (standardBasis d i)) hunit hperp s hs hpos
  change s * (w (P.map x) * fluxForm F (P.map x)
    (fun i => fderiv ℝ P.map x (standardBasis d i))) = _
  rw [D04.Dictionary.fluxForm_volume]
  calc
    _ = w (P.map x) * (s * omega (d+1) (Fin.cons (F (P.map x))
      (fun i => fderiv ℝ P.map x (standardBasis d i)))) := by ring
    _ = _ := by rw [he]; exact (mul_assoc _ _ _).symm

theorem frame_normal_exists : frame_normal_existsType := by
  intro d v hv s hs
  let T := Submodule.span ℝ (range v)
  have hdim : Module.finrank ℝ T = d := by
    simpa using finrank_span_eq_card hv
  have hperpdim : Module.finrank ℝ Tᗮ = 1 := by
    have h := T.finrank_add_finrank_orthogonal
    rw [hdim] at h
    simp only [Specs.D04.C01.EuclideanInterfaces.Model.E, finrank_euclideanSpace,
      Fintype.card_fin] at h
    exact Nat.add_left_cancel h
  let i : Fin (Module.finrank ℝ Tᗮ) := ⟨0, by rw [hperpdim]; decide⟩
  let b := stdOrthonormalBasis ℝ Tᗮ
  let w : E (d+1) := (b i).val
  have hw : ‖w‖ = 1 := b.norm_eq_one i
  have hwp : w ∈ Tᗮ := (b i).property
  have hp (j : Fin d) : inner ℝ w (v j) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (mem_range_self j)) hwp
  have hwT : w ∉ T := by
    intro hwT
    have hh := Submodule.inner_right_of_mem_orthogonal hwT hwp
    rw [real_inner_self_eq_norm_sq, hw] at hh
    norm_num at hh
  have hli : LinearIndependent ℝ (Fin.cons w v : Fin (d+1) → E (d+1)) :=
    linearIndependent_finCons.mpr ⟨hv, hwT⟩
  let B := basisOfLinearIndependentOfCardEqFinrank' (Fin.cons w v) hli (by simp [E])
  have hnonzero : omega (d+1) (Fin.cons w v) ≠ 0 := by
    have hh := (standardBasis (d+1)).isUnit_det B |>.ne_zero
    have hh' : (standardBasis (d+1)).det (Fin.cons w v) ≠ 0 := by
      simpa only [B, coe_basisOfLinearIndependentOfCardEqFinrank'] using hh
    exact hh' 
  have hsn : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  rcases lt_or_gt_of_ne (mul_ne_zero hsn hnonzero) with hneg | hpos
  · refine ⟨-w, by simpa using hw, ?_, ?_⟩
    · intro j
      simp [inner_neg_left, hp j]
    · have hn : omega (d+1) (Fin.cons (-w) v) = -omega (d+1) (Fin.cons w v) := by
        change ((omega (d+1)).curryLeft (-w)) v = _
        rw [map_neg]
        rfl
      rw [hn]
      linarith
  · exact ⟨w, hw, hp, hpos⟩

theorem patch_flux_exists : patch_flux_existsType := by
  intro d O P hr F hO hF w hw s hs
  have hlin (x : P.region) : LinearIndependent ℝ
      (fun i => fderiv ℝ P.map x (standardBasis d i)) :=
    (standardBasis d).linearIndependent.map' (fderiv ℝ P.map x).toLinearMap (LinearMap.ker_eq_bot.mpr (hr x x.property))
  choose ν hν using fun x : P.region => frame_normal_exists _ (hlin x) s hs
  let N : E d → E (d+1) := fun x => if hx : x ∈ P.region then ν ⟨x,hx⟩ else 0
  have hN : ∀ x ∈ P.region, ‖N x‖ = 1 ∧
      (∀ i, inner ℝ (N x) (fderiv ℝ P.map x (standardBasis d i)) = 0) ∧
      0 < s * omega (d+1) (Fin.cons (N x) (fun i => fderiv ℝ P.map x (standardBasis d i))) := by
    intro x hx
    simpa only [N, dite_eq_left hx] using hν ⟨x,hx⟩
  refine ⟨N, hN, ?_, patch_flux P F hO hF w hw s hs N hN⟩
  have hβ := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  have hi := D04.GeometricPatches.weighted_integrable P (fluxForm F)
    (D04.LocalStokes.form_C0 O _ hβ) w hw
  have hsi := (D04.Orientation.regionIntegral_smul s hi).1
  convert hsi using 1
  funext x
  obtain ⟨hu,hp,hpos⟩ := hN x x.property
  have hh := frame_flux (F (P.map x)) (N x)
    (fun i => fderiv ℝ P.map x (standardBasis d i)) hu hp s hs hpos
  change _ = s * (w (P.map x) * fluxForm F (P.map x)
    (fun i => fderiv ℝ P.map x (standardBasis d i)))
  rw [D04.Dictionary.fluxForm_volume]
  calc
    _ = w (P.map x) * (s * omega (d+1) (Fin.cons (F (P.map x))
      (fun i => fderiv ℝ P.map x (standardBasis d i)))) := by
        rw [hh]
        exact mul_assoc _ _ _
    _ = _ := by ring

theorem patch_chain_flux : patch_chain_fluxType := by
  intro d O C hr F hO hF
  choose ν hν hi hv using fun P : C.support =>
    patch_flux_exists P.val.patch (hr P.val P.property) F hO hF P.val.weight P.val.continuous 1 (Or.inl rfl)
  refine ⟨ν, ?_, hi, ?_⟩
  · intro P x hx
    simpa only [one_mul] using hν P x hx
  · change C.sum (fun P a => a • patchIntegral P.patch P.weight (fluxForm F)) = _
    simp only [Finsupp.sum, zsmul_eq_mul]
    rw [Finset.sum_subtype C.support (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro P _
    rw [show patchIntegral P.val.patch P.val.weight (fluxForm F) = _ from
      by simpa only [one_mul] using hv P]

theorem geometric_cell_piecewise_gauss_flux : geometric_cell_piecewise_gauss_fluxType := by
  intro k N L O c P hp outer left right b s hs hmatch hw hassembly hinj hrank Z hover F hO hF hrOuter
  obtain ⟨D,hD,hv⟩ := geometric_cell_piecewise_gauss c P hp outer left right b s hs hmatch hw
    hassembly hinj hrank Z hover F hO hF
  obtain ⟨ν,hν,hi,hval⟩ := patch_chain_flux outer hrOuter F hO hF
  exact ⟨D,hD,ν,hν,hi,hv.trans hval⟩

lemma finite_patch_flux {d N : ℕ} {O : Set (E (d+1))}
    (P : Fin N → Patch d O) (s : Fin N → PointSign) (a : Fin N → ℤ)
    (hr : ∀ j x, x ∈ (P j).region → Function.Injective (fderiv ℝ (P j).map x))
    (F : E (d+1) → E (d+1)) (hO : IsOpen O) (hF : CrOn 1 O F) :
    HasFinitePatchFlux P s a F
      (∑ j, a j • ((s j).val * patchIntegral (P j) (fun _ => 1) (fluxForm F))) := by
  choose ν hν hi hv using fun j =>
    patch_flux_exists (P j) (hr j) F hO hF (fun _ => 1) continuousOn_const (s j).val (s j).property
  refine ⟨ν, hν, ?_, ?_⟩
  · intro j
    simpa only [one_mul] using hi j
  · apply Finset.sum_congr rfl
    intro j _
    rw [hv j]
    simp only [one_mul, zsmul_eq_mul]

theorem geometric_manifold_piecewise_gauss_flux : geometric_manifold_piecewise_gauss_fluxType := by
  intro d q O M bO hbO m P s hreg Z hZ hrepeat hover hcover Zbulk hbulk l p e Q tSign b
    deltaOut hdout hOut hout deltaPair hdp hPair hpair F hO hF hrOuter
  obtain ⟨D,hD,hv⟩ := geometric_manifold_piecewise_gauss M bO hbO m P s hreg Z hZ hrepeat
    hover hcover Zbulk hbulk e Q tSign b deltaOut hdout hOut hout deltaPair hdp hPair hpair F hO hF
  refine ⟨D,hD,?_⟩
  rw [hv]
  exact finite_patch_flux Q tSign b hrOuter F hO hF

theorem geometric_manifold_piecewise_gauss_flux_points :
    geometric_manifold_piecewise_gauss_flux_pointsType := by
  intro q O M bO hbO l p e P s c hout hpair Z hover F hO hF
  obtain ⟨D,hD,hv⟩ := geometric_manifold_piecewise_gauss_points M bO hbO e P s c hout hpair Z hover F hO hF
  refine ⟨D,hD,?_⟩
  have hr : ∀ j x, x ∈ (P j).region → Function.Injective (fderiv ℝ (P j).map x) :=
    fun _ _ _ => fun _ _ _ => Subsingleton.elim _ _
  have hf := finite_patch_flux P s c hr F hO hF
  have heq : (∑ t, c t • ((s t).val * patchIntegral (P t) (fun _ => 1) (fluxForm F))) =
      ∑ t, c t • (s t).val * patchIntegral (P t) (fun _ => 1) (fluxForm F) := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [zsmul_eq_mul]
    ring
  rw [heq, ← hv] at hf
  exact hf


/-! The scalar Riemann bulk bridge for finite pieces. -/
open Filter
open Specs.D04.C06.NullCovers.Model

/-- An open-parameter full-rank chart in equal dimensions has open image.
The inverse theorem is applied to a C¹ Euclidean extension. -/
lemma full_dimensional_boundaryless_open {n : ℕ} {M : Set (E n)}
    (hM : IsBoundarylessEmbeddedManifold 1 n M) : IsOpen M := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨c, u, hc, hu, hux⟩ := hM.2.2 x hx
  obtain ⟨W, hW, hs⟩ := c.source_open
  have hsource : IsOpen c.source := by
    simpa [hs, Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, hc] using hW
  obtain ⟨V, g, hV, huV, hge, hg, hr⟩ := c.regular u hu
  let A := (LinearEquiv.ofInjectiveEndo (fderiv ℝ g u).toLinearMap (hr u huV)).toContinuousLinearEquiv
  have hd : HasFDerivAt g A.toContinuousLinearMap u :=
    (hg.contDiffAt (hV.mem_nhds huV)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hgd := hg.contDiffAt (hV.mem_nhds huV)
  let e := hgd.toOpenPartialHomeomorph g hd one_ne_zero
  have hue : u ∈ e.source := hgd.mem_toOpenPartialHomeomorph_source hd _
  let S := e.source ∩ (c.source ∩ V)
  have hS : IsOpen S := e.open_source.inter (hsource.inter hV)
  have hi : e '' S ⊆ M := by
    rintro y ⟨v, hv, rfl⟩
    change g v ∈ M
    rw [hge hv.2]
    exact (c.map_source hv.2.1).1
  have hmem : x ∈ e '' S := by
    refine ⟨u, ⟨hue, hu, huV⟩, ?_⟩
    exact (hge ⟨hu, huV⟩).trans hux
  exact mem_of_superset ((e.isOpen_image_of_subset_source hS inter_subset_left).mem_nhds hmem) hi

/-- The ambient frontier of a closed, full-dimensional manifold is contained
in its intrinsic boundary. -/
lemma manifold_frontier_subset {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (hclosed : IsClosed M) :
    frontier M ⊆ intrinsicBoundary 1 n M := by
  intro x hx
  by_contra hb
  have hxi : x ∈ M \ intrinsicBoundary 1 n M := ⟨hclosed.closure_subset hx.1, hb⟩
  have hopen := full_dimensional_boundaryless_open (D04.intrinsic_interior_manifold hM)
  exact hx.2 (interior_mono diff_subset (hopen.interior_eq ▸ hxi))

/-- Every compact manifold piece has an actual lower-dimensional presentation
of its ambient frontier, also in ambient dimension one. -/
lemma manifold_frontier_seams {d : ℕ} {M : Set (E (d+1))}
    (hM : IsEmbeddedManifold 1 (d+1) M) (hK : IsCompact M) :
    ∃ s : AmbientSeams (d+1) (d+1), s.carrier = frontier M := by
  have hb := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold hM)).1
  exact D04.GeometricUnion.embedded_seams (fun _ : Unit => d) (fun _ => Nat.lt_succ_self d)
    (fun _ => intrinsicBoundary 1 (d+1) M) (fun _ => hb) (frontier M)
    (hK.of_isClosed_subset isClosed_frontier (frontier_subset_closure.trans hK.isClosed.closure_subset))
    (by intro x hx; exact mem_iUnion.mpr ⟨(), manifold_frontier_subset hM hK.isClosed hx⟩)


lemma ambient_seams_contentZero {n : ℕ} (s : AmbientSeams n n) : ContentZero s.carrier := by
  let c := D04.RegularDomainGeometry.interiorChart (n := n) isOpen_univ
  have h := (D04.GeometricUnion.chart_seams_contentZero c le_rfl s s.carrier s.isCompact
    (by intro x hx; exact ⟨by simp, mem_univ _⟩)).2
  simpa [c, D04.RegularDomainGeometry.interiorChart] using h

/-- The identity is an ambient chart wherever a set contains an ambient open set. -/
def identityChart {n : ℕ} {M : Set (E n)} (W : Set (E n))
    (hW : IsOpen W) (hWM : W ⊆ M) : EmbeddedChart 1 n n M where
  half := false
  half_pos := by simp
  source := W
  source_open := ⟨W, hW, by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := W
  ambient_open := hW
  toFun := id
  invFun := id
  map_source := fun _ hx => ⟨hWM hx, hx⟩
  map_target := fun _ hx => hx.2
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  continuous_toFun := continuousOn_id
  continuous_invFun := continuousOn_id
  regular := by
    intro u hu
    refine ⟨univ, id, isOpen_univ, mem_univ _, (fun _ _ => rfl), contDiff_id.contDiffOn, ?_⟩
    intro v hv
    simpa using (Function.injective_id : Function.Injective (id : E n → E n))

lemma identityChart_differential {n : ℕ} {M : Set (E n)}
    (W : Set (E n)) (hW : IsOpen W) (hWM : W ⊆ M) (u : W) :
    chartDifferential (identityChart W hW hWM) u = ContinuousLinearMap.id ℝ (E n) := by
  simpa only [fderiv_id] using D04.chartDifferential_extension (identityChart W hW hWM)
    D04.RegularDomainGeometry.regularity_one u u.property univ id isOpen_univ
    (mem_univ _) (fun _ _ => rfl) differentiableAt_id

/-- A form supported in the ambient interior is already an ordinary scalar
integral, by the actual single-chart theorem in the identity chart. -/
lemma volume_integral_away_frontier {n : ℕ} {K M : Set (E n)}
    (hK : IsCompact K) (hMK : M ⊆ K)
    (o : PositiveManifoldOrientation 1 n M) (ho : IsAmbientOrientation o)
    (s : AmbientSeams n n) (hKM : K \ M ⊆ s.carrier)
    (hfront : frontier K ⊆ s.carrier)
    (V : Set (E n)) (hV : IsOpen V) (hsV : s.carrier ⊆ V)
    (f : E n → ℝ) (hf : ContinuousOn f K) (hz : EqOn f (fun _ => 0) V)
    (P : SignedChartPartition o (topSupport (volumeField (fun x : M => f x))))
    (hJ : Jordan K) (hi : RegionIntegrable (fun x : K => f x)) :
    orientedIntegral (volumeField (fun x : M => f x)) P =
      regionIntegral (fun x : K => f x) := by
  let A := interior K \ s.carrier
  have hA : IsOpen A := isOpen_interior.inter s.isCompact.isClosed.isOpen_compl
  have hAM : A ⊆ M := by
    intro x hx
    by_contra hn
    exact hx.2 (hKM ⟨interior_subset hx.1, hn⟩)
  let c := identityChart A hA hAM
  have hsupp : topSupport (volumeField (fun x : M => f x)) ⊆
      Subtype.val ⁻¹' (K \ V) := by
    apply closure_minimal _ ((hK.diff hV).isClosed.preimage continuous_subtype_val)
    intro x hx
    refine ⟨hMK x.property, ?_⟩
    intro hxV
    apply hx
    change f x • _ = 0
    rw [hz hxV, zero_smul]
  have hrem : K \ V ⊆ M := by
    intro x hx
    by_contra hn
    exact hx.2 (hsV (hKM ⟨hx.1, hn⟩))
  have hk : IsCompact (topSupport (volumeField (fun x : M => f x))) := by
    have hC : IsCompact ((Subtype.val : M → E n) ⁻¹' (K \ V)) :=
      (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
        (by simpa only [Subtype.range_coe] using hrem)).mpr (hK.diff hV)
    exact hC.of_isClosed_subset isClosed_closure hsupp
  have hs : topSupport (volumeField (fun x : M => f x)) ⊆ Subtype.val ⁻¹' c.ambient := by
    intro x hx
    have hxK := (hsupp hx).1
    have hxV := (hsupp hx).2
    refine ⟨?_, fun hh => hxV (hsV hh)⟩
    by_contra hn
    exact hxV (hsV (hfront ⟨subset_closure hxK, hn⟩))
  have hcont : Continuous (fun x : M => f x) :=
    hf.comp_continuous continuous_subtype_val (fun x => hMK x.property)
  have hv := D04.ManifoldIntegralIndependence.oriented_single_chart_variable_sign o
    (volumeField (fun x : M => f x)) (D04.RegularDomainBridge.volume_field_continuous _ hcont)
    hk P c hs
  have hc : (fun u : c.source => chartSign o.atPoint c u u.property *
      topCoefficient (volumeField (fun x : M => f x)) c u) = fun u : A => f u := by
    funext u
    change D04.ManifoldIntegralIndependence.signedCoefficient o
      (volumeField (fun x : M => f x)) c u = _
    rw [D04.RegularDomainBridge.signedCoefficient_volume o ho]
    have hd := identityChart_differential A hA hAM u
    change f u * |(chartDifferential c u).det| = f u
    rw [hd, show (ContinuousLinearMap.id ℝ (E n)).det = 1 from LinearMap.det_id, abs_one, mul_one]
  rw [hc] at hv
  have hext : Specs.D04.C06.JordanRegions.Model.zeroExtension (fun u : A => f u) = Specs.D04.C06.JordanRegions.Model.zeroExtension (fun x : K => f x) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [Specs.D04.C06.JordanRegions.Model.zeroExtension, dif_pos hx,
        dif_pos (interior_subset hx.1)]
    · simp only [Specs.D04.C06.JordanRegions.Model.zeroExtension, dif_neg hx]
      by_cases hxK : x ∈ K
      · simp only [dif_pos hxK]
        have hxS : x ∈ s.carrier := by
          by_cases hxi : x ∈ interior K
          · exact Classical.byContradiction (fun hn => hx ⟨hxi, hn⟩)
          · exact hfront ⟨subset_closure hxK, hxi⟩
        exact (hz (hsV hxS)).symm
      · simp only [dif_neg hxK]
  exact hv.2.trans ((D04.DirectedSubstitution.proper_congr hext).2.trans
    (D04.GeometricPatches.region_coefficient_integral hJ _ hi).2.symm)


lemma fullRank_open_image {n : ℕ} {S : Set (E n)} (hS : IsOpen S)
    (f : E n → E n) (hf : FullRankLocalExtension 1 S f) : IsOpen (f '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨u, hu, rfl⟩
  obtain ⟨V, g, hV, huV, hge, hg, hr⟩ := hf u hu
  let A := (LinearEquiv.ofInjectiveEndo (fderiv ℝ g u).toLinearMap (hr u huV)).toContinuousLinearEquiv
  have hd : HasFDerivAt g A.toContinuousLinearMap u :=
    (hg.contDiffAt (hV.mem_nhds huV)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hgd := hg.contDiffAt (hV.mem_nhds huV)
  let e := hgd.toOpenPartialHomeomorph g hd one_ne_zero
  have hue : u ∈ e.source := hgd.mem_toOpenPartialHomeomorph_source hd _
  let T := e.source ∩ (S ∩ V)
  have hT : IsOpen T := e.open_source.inter (hS.inter hV)
  have hi : e '' T ⊆ f '' S := by
    rintro z ⟨v, hv, rfl⟩
    exact ⟨v, hv.2.1, (hge hv.2).symm⟩
  have hm : f u ∈ e '' T := ⟨u, ⟨hue, hu, huV⟩, hge ⟨hu, huV⟩⟩
  exact mem_of_superset ((e.isOpen_image_of_subset_source hT inter_subset_left).mem_nhds hm) hi

lemma representation_frontier_seams {d : ℕ} {K M O : Set (E (d+1))}
    {o : PositiveManifoldOrientation 1 (d+1) M} (R : PieceRepresentation K M o O)
    (hK : IsCompact K) :
    ∃ s : AmbientSeams (d+1) (d+1), frontier K ⊆ s.carrier := by
  cases R with
  | manifold same inside =>
    subst K
    obtain ⟨s, hs⟩ := manifold_frontier_seams o.manifold hK
    exact ⟨s, hs.symm ▸ Subset.rfl⟩
  | cell a hi hr hKe hMe c hs hm hp =>
    have hsource : IsOpen c.source := hs.symm ▸ isOpen_interior
    have hM : IsOpen M := by
      rw [hMe, ← hm, ← hs]
      exact fullRank_open_image hsource c.toFun c.regular
    obtain ⟨s, hs⟩ := D04.GeometricUnion.cell_frontier_seams a
    refine ⟨s, ?_⟩
    intro x hx
    have hxK : x ∈ K := hK.isClosed.closure_subset hx.1
    have hxM : x ∉ M := by
      intro hxm
      have hMK : M ⊆ K := by rw [hKe, hMe]; exact image_mono interior_subset
      have hxmI : x ∈ interior M := by rwa [hM.interior_eq]
      exact hx.2 (interior_mono hMK hxmI)
    rw [hs, hKe, hMe] at *
    obtain ⟨u, hu, rfl⟩ := hxK
    exact ⟨u, ⟨subset_closure hu, fun h => hxM (mem_image_of_mem _ h)⟩, rfl⟩

lemma identity_fullRank {n : ℕ} (S : Set (E n)) : FullRankLocalExtension 1 S id := by
  intro x hx
  refine ⟨univ, id, isOpen_univ, mem_univ _, (fun _ _ => rfl), contDiff_id.contDiffOn, ?_⟩
  intro v hv
  simpa using (Function.injective_id : Function.Injective (id : E n → E n))

lemma scalar_volume_C0 {n : ℕ} {O : Set (E n)} (hO : IsOpen O)
    (f : E n → ℝ) (hf : ContinuousOn f O) :
    IsCrForm (some 0) O (fun x => f x • omega n) := by
  refine ⟨hO, fun J => ?_⟩
  change ContinuousOn (fun x => f x *
    Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient (standardBasis n) (omega n) J) O
  exact hf.mul continuousOn_const

/-- One representation's positively oriented form integral is its scalar
Riemann integral, for both compact manifolds and regular cells with corners. -/
lemma representation_volume_integral {d : ℕ} {K M O : Set (E (d+1))}
    {o : PositiveManifoldOrientation 1 (d+1) M} (R : PieceRepresentation K M o O)
    (hK : IsCompact K) (hMK : M ⊆ K) (ho : IsAmbientOrientation o)
    (s : AmbientSeams (d+1) (d+1)) (hKM : K \ M ⊆ s.carrier)
    (hfront : frontier K ⊆ s.carrier)
    (f : E (d+1) → ℝ) (hO : IsOpen O) (hf : ContinuousOn f O)
    (v : ℝ) (hv : R.HasIntegral (fun x => f x • omega (d+1)) v) :
    Jordan K ∧ RegionIntegrable (fun x : K => f x) ∧
      v = regionIntegral (fun x : K => f x) := by
  have hsnull := ambient_seams_contentZero s
  have hJ : Jordan K := (D04.JordanRegions.jordan_iff_boundary (Nat.succ_pos d) K hK.isBounded).mpr
    (D04.NullCovers.contentZero_mono hfront hsnull)
  have hKO := D04.GeometricUnion.representation_inside R
  have hfK : ContinuousOn f K := hf.mono hKO
  have hi : RegionIntegrable (fun x : K => f x) :=
    D04.GeometricPatches.continuous_integrable hJ (by simpa only [hK.isClosed.closure_eq] using hfK)
  refine ⟨hJ, hi, ?_⟩
  obtain ⟨chi, hchi, hval, hzero, hone⟩ :=
    D04.GeometricUnion.smooth_seam_cutoff_sequence s.carrier s.isCompact
  let alpha : FormField (d+1) (d+1) := fun x => f x • omega (d+1)
  have ha : IsCrForm (some 0) O alpha := scalar_volume_C0 hO f hf
  let D : RegularDecomposition (d+1) (d+1) := {
    count := 1
    piece := fun _ => K
    compact := fun _ => hK
    regular := fun _ => M
    subset := fun _ => hMK
    orientation := fun _ => o
    seams := s
    singular := fun _ => hKM
    overlap := by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)) }
  have hfield (m : ℕ) :
      (fun x : M => chi m x • Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction
        (r := 1) alpha x) = volumeField (fun x : M => chi m x * f x) := by
    funext x
    change chi m x • (f x • (omega (d+1)).compLinearMap _) = _
    rw [smul_smul]
    rfl
  have hcompact (m : ℕ) : IsCompact (topSupport
      (fun x : M => chi m x • Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction
        (r := 1) alpha x)) := by
    obtain ⟨V, hV, hsV, hz⟩ := hzero m
    rw [← D04.GeometricUnion.ambientRestriction_weight]
    exact D04.GeometricUnion.regular_topSupport_compact D _ V hV hsV
      (by intro x hx; change chi m x • alpha x = 0; rw [hz hx, zero_smul]) 0
  let P (m : ℕ) := Classical.choice (D04.ManifoldIntegral.signed_partition_exists o _ (hcompact m))
  have hlim := D04.GeometricUnion.representation_cutoff_limit R hK s hKM alpha ha v hv
    chi hchi hval hzero hone P
  have hscalar := (D04.GeometricUnion.compact_parameter_cutoff_limit K id le_rfl hK hJ
    continuousOn_id (fun _ _ _ _ h => h) (identity_fullRank K) s f hfK
    chi hchi hval hone).2
  have heq (m : ℕ) : orientedIntegral
      (fun x : M => chi m x • Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction
        (r := 1) alpha x) (P m) =
      regionIntegral (fun x : K => chi m x * f x) := by
    obtain ⟨V, hV, hsV, hz⟩ := hzero m
    have hfi : RegionIntegrable (fun x : K => chi m x * f x) :=
      D04.GeometricPatches.continuous_integrable hJ
        (by simpa only [hK.isClosed.closure_eq] using (hchi m).continuous.continuousOn.mul hfK)
    apply (D04.GeometricUnion.oriented_integral_cast (hfield m) (P m)).trans
    exact volume_integral_away_frontier hK hMK o ho s hKM hfront V hV hsV _
      ((hchi m).continuous.continuousOn.mul hfK) (by intro x hx; change chi m x * f x = 0; rw [hz hx, zero_mul])
      ((hfield m) ▸ P m) hJ hfi
  simp_rw [heq] at hlim
  exact tendsto_nhds_unique hlim hscalar


/-- The form selector is identified with the actual scalar region integral;
positivity is imposed on orientations, never on an assumed integral. -/
theorem geometric_volume_riemann : geometric_volume_riemannType := by
  intro d O D hpos f hO hf
  choose s hs using fun i => representation_frontier_seams (D.representation i) (D.compact i)
  obtain ⟨t, ht⟩ := D04.GeometricUnion.finite_seams s
  let z := appendSeams D.seams t
  have hbase : D.seams.carrier ⊆ z.carrier := by
    rw [D04.GeometricUnion.append_seams_carrier]
    exact subset_union_left
  have hfront (i : Fin D.count) : frontier (D.piece i) ⊆ z.carrier := by
    rw [D04.GeometricUnion.append_seams_carrier, ht]
    exact (hs i).trans (fun x hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
  have ha := scalar_volume_C0 hO f hf
  choose v hv using D04.GeometricUnion.geometric_piece_integral_exists D _ ha
  have hpiece (i : Fin D.count) := representation_volume_integral (D.representation i)
    (D.compact i) (D.subset i) (hpos i) z ((D.singular i).trans hbase)
    (hfront i) f hO hf (v i) (hv i)
  have hclosed : IsClosed D.carrier := (isCompact_iUnion D.compact).isClosed
  have hfc : ContinuousOn f (closure D.carrier) := by
    rw [hclosed.closure_eq]
    exact hf.mono (D04.GeometricUnion.geometric_carrier_inside D)
  obtain ⟨hJ, hi, hsum⟩ := D04.GeometricUnion.coordinate_union_integral D.piece
    (fun i => (hpiece i).1) z.carrier (ambient_seams_contentZero z)
    (fun i j hij => (D.overlap i j hij).trans hbase) f hfc
  refine ⟨hJ, hi, ?_⟩
  exact (D04.GeometricUnion.geometric_union_integral_eq_sum D D
    (D04.GeometricUnion.compatible_regular_refl D.toRegularDecomposition) _ ha v hv).trans
    ((Finset.sum_congr rfl (fun i _ => (hpiece i).2.2)).trans hsum.symm)


lemma ambientOrientation_of_positive_chart {d : ℕ} {M : Set (E (d+1))}
    (o : PositiveManifoldOrientation 1 (d+1) M) (c : EmbeddedChart 1 (d+1) (d+1) M)
    (hcover : ∀ x : M, ∃ u : c.source, c.toFun u = x)
    (hsgn : ∀ u : c.source, chartSign o.atPoint c u u.property = 1)
    (hdet : ∀ u : c.source, 0 < (chartDifferential c u).det) : IsAmbientOrientation o := by
  let a := D04.RegularDomainBridge.ambientOrientation (Nat.succ_pos d) o.manifold
  have ha := D04.RegularDomainBridge.ambientOrientation_spec (Nat.succ_pos d) o.manifold
  intro x B
  obtain ⟨u, hu⟩ := hcover x
  have hx : chartPoint c u = x := Subtype.ext hu
  subst x
  let b := D04.Orientations.chartBasis c o.manifold.1 le_rfl u u.property
  have hb : ∀ i, (b i).val = chartDifferential c u (standardBasis (d+1) i) := fun _ => rfl
  have ho' := (D04.Orientations.chartSign_basis o.atPoint c u u.property b hb).mp (hsgn u)
  have ha' := (D04.Orientations.chartSign_basis a.atPoint c u u.property b hb).mp
    (by rw [D04.RegularDomainBridge.ambient_chart_sign a ha, Real.sign_of_pos (hdet u)])
  have he : o.atPoint (c.toFun u) (c.map_source u.property).1 =
      a.atPoint (c.toFun u) (c.map_source u.property).1 := ho'.symm.trans ha'
  change B.orientation = o.atPoint (c.toFun u) (c.map_source u.property).1 ↔ _
  rw [he]
  exact ha _ B

lemma cell_chart_differential {d : ℕ} {O M : Set (E (d+1))}
    (a : Cell 1 (d+1) O) (c : EmbeddedChart 1 (d+1) (d+1) M)
    (hs : c.source = interior (cube (d+1))) (hm : c.toFun = cellExtension a)
    (u : c.source) : chartDifferential c u = fderiv ℝ (cellExtension a) u := by
  apply D04.chartDifferential_extension c D04.RegularDomainGeometry.regularity_one u u.property
    (extensionDomain a) (cellExtension a) (extension_spec a).1
    ((extension_spec a).2.1 (interior_subset (hs ▸ u.property))) (fun x hx => (congrFun hm x).symm)
  exact ((D04.Cells.extension_C1 a).contDiffAt
    ((extension_spec a).1.mem_nhds ((extension_spec a).2.1 (interior_subset (hs ▸ u.property))))).differentiableAt one_ne_zero

/-- Scalar integration over a finite positive cell union, before any boundary
assembly is selected. -/
lemma cell_union_volume {d N : ℕ} {O : Set (E (d+1))}
    (c : Fin N → Cell 1 (d+1) O)
    (hinj : ∀ j, InjOn (cellExtension (c j)) (cube (d+1)))
    (hrank : ∀ j x, x ∈ cube (d+1) → Function.Injective (fderiv ℝ (cellExtension (c j)) x))
    (hpositive : ∀ j x, x ∈ cube (d+1) → 0 < (fderiv ℝ (cellExtension (c j)) x).det)
    (Z : AmbientSeams (d+1) (d+1))
    (hover : ∀ i j, i ≠ j → (cellExtension (c i) '' cube (d+1)) ∩
      (cellExtension (c j) '' cube (d+1)) ⊆ Z.carrier)
    (f : E (d+1) → ℝ) (hO : IsOpen O) (hf : ContinuousOn f O) :
    Jordan (⋃ j, cellExtension (c j) '' cube (d+1)) ∧
    RegionIntegrable (fun x : (⋃ j, cellExtension (c j) '' cube (d+1)) => f x) ∧
    regionIntegral (fun x : (⋃ j, cellExtension (c j) '' cube (d+1)) => f x) =
      ∑ j, cellIntegral (c j) (fun x => f x • omega (d+1)) := by
  obtain ⟨D, e, hD, hZ, hpieces, hcharts, hv⟩ :=
    D04.GeometricUnion.cell_family_display (Nat.succ_pos d) le_rfl c hinj hrank Z hover
  have hpos (i : Fin D.count) : IsAmbientOrientation (D.orientation i) := by
    obtain ⟨a, hs, hm, hsign⟩ := hcharts i
    apply ambientOrientation_of_positive_chart (D.orientation i) a
    · intro x
      have hx : x.val ∈ cellExtension (c (e i)) '' interior (cube (d+1)) := by
        rw [← (hpieces i).2]
        exact x.property
      obtain ⟨u, hu, hux⟩ := hx
      exact ⟨⟨u, hs.symm ▸ hu⟩, (congrFun hm u).trans hux⟩
    · intro u
      exact hsign u u.property
    · intro u
      rw [cell_chart_differential (c (e i)) a hs hm u]
      exact hpositive (e i) u (interior_subset (hs ▸ u.property))
  obtain ⟨hJ, hi, heq⟩ := geometric_volume_riemann D hpos f hO hf
  have hv' := hv (fun x => f x • omega (d+1)) (scalar_volume_C0 hO f hf)
  have hj' : Jordan (⋃ j, cellExtension (c j) '' cube (d+1)) := hD ▸ hJ
  have hi' : RegionIntegrable (fun x : (⋃ j, cellExtension (c j) '' cube (d+1)) => f x) := hD ▸ hi
  have hval : regionIntegral (fun x : D.carrier => f x) =
      regionIntegral (fun x : (⋃ j, cellExtension (c j) '' cube (d+1)) => f x) := by
    exact (D04.GeometricPatches.region_domain_congr hD f).2
  exact ⟨hj', hi', hval.symm.trans (heq.symm.trans hv')⟩

/-- Scalar bulk integration over arbitrary standard-oriented compact manifold
pieces with multiplicity-one overlaps. -/
lemma manifold_union_divergence {d q : ℕ} {O : Set (E (d+1))}
    (M : Fin q → CompactManifold d (d+1) O)
    (hpos : ∀ j, IsAmbientOrientation (M j).orientation)
    (Z : AmbientSeams (d+1) (d+1))
    (hover : ∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Z.carrier)
    (F : E (d+1) → E (d+1)) (hO : IsOpen O) (hF : CrOn 1 O F)
    (I : Fin q → ℝ)
    (hI : ∀ j, HasPositiveIntegral (M j).orientation
      (tangentRestriction 1 (d+1) (M j).carrier (exteriorDerivative (fluxForm F))) (I j)) :
    Jordan (⋃ j, (M j).carrier) ∧
    RegionIntegrable (fun x : (⋃ j, (M j).carrier) => divergence F x) ∧
    regionIntegral (fun x : (⋃ j, (M j).carrier) => divergence F x) = ∑ j, I j := by
  let C : CompactManifoldDecomposition (d+1) (d+1) := {
    count := q
    piece := fun j => (M j).carrier
    compact := fun j => (M j).compact
    orientation := fun j => (M j).orientation
    seams := Z
    overlap := hover }
  have hCO : C.carrier ⊆ O := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (M i).subset_domain hi
  let D := manifoldGeometricDecomposition C hCO
  obtain ⟨hJ, hi, hv⟩ := geometric_volume_riemann D hpos (divergence F) hO
    (divergence_continuousOn O F hO hF)
  refine ⟨hJ, hi, hv.symm.trans ?_⟩
  apply D04.GeometricUnion.geometric_union_integral_eq_sum D D
    (D04.GeometricUnion.compatible_regular_refl D.toRegularDecomposition) _
    (scalar_volume_C0 hO _ (divergence_continuousOn O F hO hF)) I
  intro i P
  have hb : tangentRestriction 1 (d+1) (M i).carrier (exteriorDerivative (fluxForm F)) =
      Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.ambientRestriction (r := 1)
        (M := (M i).carrier) (divergenceVolume F) := by
    funext x
    change (exteriorDerivative (fluxForm F) x).compLinearMap _ = _
    rw [exterior_flux O F hO hF x ((M i).subset_domain x.property)]
    rfl
  have hIi := hI i
  rw [hb] at hIi
  exact ((hIi.2.2.2 P).2)


/-- Finite-cell Gauss with the ordinary Riemann divergence integral. -/
theorem riemann_cell_piecewise_gauss : riemann_cell_piecewise_gaussType := by
  intro k N L O c P hp outer left right b s hs hmatch hw hassembly hinj hrank Z hover
    F hO hF hrOuter hpositive
  obtain ⟨hJ, hi, hbulk⟩ := cell_union_volume c hinj hrank hpositive Z hover
    (divergence F) hO (divergence_continuousOn O F hO hF)
  have hbeta := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  have hst := D04.FinitePiecewiseStokes.cell_piecewise_stokes_patches c (fun _ => 1)
    P hp outer left right b s hs hmatch hw hassembly (fluxForm F) hbeta
  simp only [Int.cast_one, one_mul] at hst
  have heq : regionIntegral (fun x : (⋃ j, cellExtension (c j) '' cube (k+1)) => divergence F x) =
      patchChainIntegral (fluxForm F) outer := by
    apply hbulk.trans
    apply Eq.trans ?_ hst
    apply Finset.sum_congr rfl
    intro j _
    exact (cell_integral_congrOn (c j) (exteriorDerivative (fluxForm F)) (divergenceVolume F)
      (exterior_flux O F hO hF)).symm
  obtain ⟨nu, hnu, hint, hval⟩ := patch_chain_flux outer hrOuter F hO hF
  exact ⟨hJ, hi, heq, nu, hnu, hint, heq.trans hval⟩

/-- The finite compact-manifold branch, with standard ambient bulk
orientations and the actual scalar Riemann divergence integral. -/
theorem riemann_manifold_piecewise_gauss : riemann_manifold_piecewise_gaussType := by
  intro d q O M bO hbO m P s hreg Z hZ hrepeat hover hcover Zbulk hbulk l p e Q tSign b
    deltaOut hdout hOut hout deltaPair hdp hPair hpair F hO hF hrOuter hpositive
  have hbeta := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  obtain ⟨I, hI, hB, hst⟩ := D04.FinitePiecewiseStokes.manifold_piecewise_stokes
    M bO hbO m P s hreg Z hZ hrepeat hover hcover (fun _ => 1) e Q tSign b
    deltaOut hdout hOut hout deltaPair hdp hPair
    (fun i => ⟨(hpair i).1, (hpair i).2, rfl⟩) (fluxForm F) hbeta
  obtain ⟨hJ, hi, hv⟩ := manifold_union_divergence M hpositive Zbulk hbulk F hO hF I hI
  have hsum : (∑ j, I j) = ∑ t, b t • ((tSign t).val *
      patchIntegral (Q t) (fun _ => 1) (fluxForm F)) := by
    simpa only [one_zsmul] using hst
  have heq := hv.trans hsum
  refine ⟨hJ, hi, heq, ?_⟩
  rw [heq]
  exact finite_patch_flux Q tSign b hrOuter F hO hF

lemma flux_patch_zero {O : Set (E 1)} (P : Patch 0 O) (hP : (0 : E 0) ∈ P.region)
    (F : E 1 → E 1) : patchIntegral P (fun _ => 1) (fluxForm F) = F (P.map 0) 0 := by
  have he : fluxForm F = fun x => scalarCovector (F x 0) := by
    funext x
    ext v
    rw [D04.Dictionary.fluxForm_volume]
    change Matrix.det (fun i j : Fin 1 => ((Fin.cons (F x) v : Fin 1 → E 1) j) i) = F x 0
    rw [Matrix.det_fin_one]
    rfl
  rw [he, D04.GeometricPatches.patch_zero_dimension, if_pos hP, one_mul]

/-- The complete one-dimensional finite-manifold branch. The zero-dimensional
Gram factors are one, while the normal signs remain explicit. -/
theorem riemann_manifold_piecewise_gauss_points : riemann_manifold_piecewise_gauss_pointsType := by
  intro q O M bO hbO l p e P s c hout hpair Z hover F hO hF hpositive
  have hbeta := D04.Dictionary.fluxForm_isCr 1 O F hO hF
  obtain ⟨I, hI, hB, hst⟩ := D04.FinitePiecewiseStokes.manifold_piecewise_stokes_points
    M bO hbO (fun _ => 1) e P s c hout
    (fun i => ⟨(hpair i).1, rfl, (hpair i).2⟩) (fluxForm F) hbeta
  obtain ⟨hJ, hi, hv⟩ := manifold_union_divergence M hpositive Z hover F hO hF I hI
  have hsum : (∑ j, I j) = ∑ t, c t • ((s t).val *
      patchIntegral (P t) (fun _ => 1) (fluxForm F)) := by
    simpa only [one_zsmul, zsmul_eq_mul, Int.cast_one, one_mul, mul_assoc] using hst
  have heq := hv.trans hsum
  refine ⟨hJ, hi, heq, ?_, ?_⟩
  · rw [heq]
    exact finite_patch_flux P s c (fun _ _ _ => fun _ _ _ => Subsingleton.elim _ _) F hO hF
  · apply heq.trans
    apply Finset.sum_congr rfl
    intro t _
    rw [flux_patch_zero (P t) (hout t).1 F]
    simp only [zsmul_eq_mul]
    ring

end D04.Gauss
