import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteManifoldBoundaryAssembly
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FiniteGeometricPatchIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C15.GeneralizedStokes

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Function Topology
open scoped ContDiff BigOperators Classical
namespace D04.ManifoldBoundaryAssembly
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly
open Model

abbrev CompactManifold := Model.CompactManifold
abbrev RegularPiece := @Model.RegularPiece

/-- A compact embedded manifold has compact intrinsic boundary in ambient space. -/
lemma boundary_compact {d n} {O : Set (E n)} (M : CompactManifold d n O) :
    IsCompact (intrinsicBoundary 1 (d+1) M.carrier) := by
  letI : CompactSpace M.carrier := isCompact_iff_compactSpace.mp M.compact
  have hc : IsCompact (Subtype.val ⁻¹' intrinsicBoundary 1 (d+1) M.carrier : Set M.carrier) :=
    (D04Stokes.intrinsicBoundary_closed_relative M.orientation.manifold).isCompact
  have he : Subtype.val '' (Subtype.val ⁻¹' intrinsicBoundary 1 (d+1) M.carrier : Set M.carrier) =
      intrinsicBoundary 1 (d+1) M.carrier := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨⟨x,hx.1⟩,hx,rfl⟩
  rw [← he]
  exact hc.image continuous_subtype_val

theorem manifold_localization : manifold_localizationType := by
  intro r k n M hM o eta heta I hI m w hw hsum
  have hc : IsCompact (topSupport eta) := by
    cases k with
    | zero => exact hI.2.1
    | succ k => exact hI.2.1
  have hex i : ∃ J, HasManifoldIntegral r k o (fun x => w i x • eta x) J :=
    D04Stokes.manifold_integral_exists hM o _
      (D04.ManifoldIntegralIndependence.continuousTopField_weight (w i) (hw i) heta)
      (hc.of_isClosed_subset isClosed_closure
        (D04.ManifoldIntegralIndependence.topSupport_weight_subset _ eta))
  choose J hJ using hex
  refine ⟨J,hJ,?_⟩
  have he : (∑ i, (fun x : M => w i x • eta x)) = eta := by
    funext x
    simp only [Finset.sum_apply]
    change (∑ i, w i x • eta x) = eta x
    by_cases hz : eta x = 0
    · simp [hz]
    · rw [← Finset.sum_smul,hsum x hz,one_smul]
  have htotal := D04Stokes.manifold_integral_sum hM o
    (fun i => fun x : M => w i x • eta x) J Finset.univ (fun i _ => hJ i)
  rw [he] at htotal
  exact D04Stokes.manifold_integral_unique o eta hI htotal

theorem paired_patch_cancellation : paired_patch_cancellationType := by
  intro d n O P Q delta hd h he s t hst a b hab omega ho w hw
  rw [GeometricPatches.local_reparametrization P Q delta hd h he omega ho w hw]
  rw [← mul_assoc, hst, neg_mul, hab, smul_neg]
  exact neg_add_cancel _

/-- Compatibility with any fixed finite ambient weights is a consequence of
Stokes and finite linearity, rather than a field of a boundary display. -/
lemma boundary_values_localized {d n m} {O : Set (E n)}
    (M : CompactManifold d n O) (omega : FormField n d)
    (ho : IsCrForm (some 1) O omega) (w : Fin m → E n → ℝ)
    (hw : ∀ i, Continuous (w i))
    (hs : ∀ x ∈ intrinsicBoundary 1 (d+1) M.carrier, ∑ i, w i x = 1) :
    ∃ (bO : ManifoldOrientation 1 d (intrinsicBoundary 1 (d+1) M.carrier))
      (I : ℝ) (J : Fin m → ℝ),
      OutwardFirst d M.orientation bO ∧
      HasPositiveIntegral M.orientation
        (tangentRestriction 1 (d+1) M.carrier (exteriorDerivative omega)) I ∧
      HasManifoldIntegral 1 d bO
        (tangentRestriction 1 d (intrinsicBoundary 1 (d+1) M.carrier) omega) I ∧
      (∀ i, HasManifoldIntegral 1 d bO
        (fun x => w i x • tangentRestriction 1 d
          (intrinsicBoundary 1 (d+1) M.carrier) omega x) (J i)) ∧ I = ∑ i, J i := by
  obtain ⟨bO,hout,I,hbulk,hboundary⟩ := D04Stokes.ambient_stokes_compact
    M.orientation M.compact O omega M.subset_domain ho
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold M.orientation.manifold)).1
  have hcont := D04Stokes.tangentRestriction_top_continuous hbM O omega
    (fun x hx => M.subset_domain hx.1) (D04.LocalStokes.form_C0 O omega ho)
  obtain ⟨J,hJ,he⟩ := manifold_localization hbM bO _ hcont hboundary w hw
    (fun x _ => hs x x.property)
  exact ⟨bO,I,J,hout,hbulk,hboundary,hJ,he⟩

theorem common_boundary_localization : common_boundary_localizationType := by
  intro d n q O M omega ho ι U hU hcover
  classical
  let K := ⋃ j, intrinsicBoundary 1 (d+1) (M j).carrier
  have hK : IsCompact K := isCompact_iUnion (fun j => boundary_compact (M j))
  obtain ⟨m,a,A,hA⟩ := GeometricPatches.ambient_partition_exists K hK U hU hcover
  obtain ⟨V,hV,hKV,hsum⟩ := A.sum_one
  have hex (j : Fin q) := boundary_values_localized (M j) omega ho A.weight
    (fun i => (A.smooth i).continuous) (fun x hx => hsum x (hKV (mem_iUnion.mpr ⟨j,hx⟩)))
  choose bO I J hout hbulk hboundary hJ he using hex
  refine ⟨m,a,A,bO,I,J,hA,hout,hbulk,hboundary,hJ,he,?_⟩
  intro multiplicity
  calc
    _ = ∑ j, ∑ i, multiplicity j • J j i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [he j, Finset.smul_sum]
    _ = _ := Finset.sum_comm

theorem common_boundary_patch_localization : common_boundary_patch_localizationType := by
  intro d n q l O M P omega ho ι U hU hcover
  classical
  let K := (⋃ j, intrinsicBoundary 1 (d+1) (M j).carrier) ∪
    (⋃ t, (P t).map '' closure (P t).region)
  have hK : IsCompact K := (isCompact_iUnion (fun j => boundary_compact (M j))).union
    (isCompact_iUnion (fun t => (GeometricPatches.region_compact (P t)).image_of_continuousOn
      ((P t).regular.continuousOn.mono (P t).contains)))
  obtain ⟨m,a,A,hA⟩ := GeometricPatches.ambient_partition_exists K hK U hU hcover
  obtain ⟨V,hV,hKV,hsum⟩ := A.sum_one
  refine ⟨m,a,A,hA,?_,?_⟩
  · intro t
    have hv := GeometricPatches.finite_weight_localization (P t) omega
      (D04.LocalStokes.form_C0 O omega ho) (fun _ => 1) A.weight continuousOn_const
      (fun i => (A.smooth i).continuous.continuousOn)
      (fun x hx => hsum _ (hKV (Or.inr (mem_iUnion.mpr
        ⟨t,mem_image_of_mem _ (subset_closure hx)⟩))))
    simpa only [one_mul] using hv
  · intro j
    exact boundary_values_localized (M j) omega ho A.weight
      (fun i => (A.smooth i).continuous)
      (fun x hx => hsum x (hKV (Or.inl (mem_iUnion.mpr ⟨j,hx⟩))))
/-- Outward-first point signs are forced by the unique outward conormal. -/
lemma outward_point_orientation_unique {r : ℕ∞ω} {n} {M : Set (E n)}
    (o : PositiveManifoldOrientation r 1 M)
    (s t : ZeroManifoldOrientation (intrinsicBoundary r 1 M))
    (hs : OutwardFirst 0 o s) (ht : OutwardFirst 0 o t) : s = t := by
  obtain ⟨nu,hnu,hns,hsp⟩ := hs
  obtain ⟨mu,hmu,hms,htp⟩ := ht
  have hnm : nu = mu := by
    funext x
    exact (D04BoundaryOrientation.conormal_exists_unique o.manifold x x.property).unique
      (hns x) (hms x)
  subst mu
  obtain ⟨v,hv,hunique⟩ := D04BoundaryOrientation.boundary_point_sign o nu hns
  exact (hunique s hsp).trans (hunique t htp).symm

lemma signed_point_stokes {n} {O : Set (E n)} (M : CompactManifold 0 n O)
    (bO : ZeroManifoldOrientation (intrinsicBoundary 1 1 M.carrier))
    (hbO : OutwardFirst 0 M.orientation bO)
    (omega : FormField n 0) (ho : IsCrForm (some 1) O omega) :
    ∃ I : ℝ, HasPositiveIntegral M.orientation
      (tangentRestriction 1 1 M.carrier (exteriorDerivative omega)) I ∧
      HasManifoldIntegral 1 0 bO
        (tangentRestriction 1 0 (intrinsicBoundary 1 1 M.carrier) omega) I := by
  obtain ⟨s,hs,I,hI,hB⟩ := D04Stokes.ambient_stokes_compact
    M.orientation M.compact O omega M.subset_domain ho
  rw [outward_point_orientation_unique M.orientation s bO hs hbO] at hB
  exact ⟨I,hI,hB⟩

theorem signed_point_boundary_assembly : signed_point_boundary_assemblyType := by
  intro n q O M bO hbO a l p e P s c houter hpair omega ho
  classical
  have hex j := signed_point_stokes (M j) (bO j) (hbO j) omega ho
  choose I hI hB using hex
  refine ⟨I,hI,hB,?_⟩
  let B := fun j : Fin q => intrinsicBoundary 1 1 (M j).carrier
  have hfin (j : Fin q) : Finite (B j) := by
    letI : Fintype ((j : Fin q) × B j) := Fintype.ofEquiv _ e
    exact Finite.of_injective
      (fun x : B j => (⟨j,x⟩ : (j : Fin q) × B j)) (by
        intro x y h
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h)
  letI (j : Fin q) : Fintype (B j) := @Fintype.ofFinite (B j) (hfin j)
  let F : ((j : Fin q) × B j) → ℝ := fun z =>
    a z.1 • ((bO z.1 z.2).val * omega z.2.val (fun j => Fin.elim0 j))
  have hvalues : (∑ j, a j • I j) = ∑ z, F z := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    have hj := (hB j).2.2.2
    have hfun : (fun x => tangentRestriction 1 0 (intrinsicBoundary 1 1 (M j).carrier)
        omega x (fun i => Fin.elim0 i)) =
        (fun x => omega x.val (fun i => Fin.elim0 i)) := by
      funext x
      change omega x.val (fun i => _) = _
      congr 1
      funext i
      exact Fin.elim0 i
    rw [hfun] at hj
    rw [← hj]
    unfold zeroIntegral
    rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  rw [hvalues, ← e.sum_comp F, Fintype.sum_sum_type]
  have hcancel : ∑ z : Fin p × Bool, F (e (Sum.inr z)) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro i _
    rw [Fintype.sum_bool]
    obtain ⟨hpoint,ha,hs⟩ := hpair i
    dsimp only [F]
    rw [ha,hs,hpoint,neg_mul,smul_neg]
    exact add_neg_cancel _
  rw [hcancel,add_zero]
  apply Finset.sum_congr rfl
  intro t _
  obtain ⟨ht,hmap,hs,hc⟩ := houter t
  have hv : patchIntegral (P t) (fun _ => 1) omega =
      omega ((P t).map 0) (fun j => Fin.elim0 j) := by
    change Specs.D04.C06.JordanRegions.Model.regionIntegral
      (fun x : (P t).region => _) = _
    have hz := ((D04.JordanRegions.zero_dimension (P t).region).2.2
      (fun x : (P t).region => weightedCoefficient (P t) (fun _ => 1) omega x)).2
    rw [dite_eq_left ht] at hz
    refine hz.trans ?_
    simp only [Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.weightedCoefficient,
      one_mul, Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient,
      D04.pullback_apply]
    congr 1
    funext i
    exact Fin.elim0 i
  rw [hv,hmap,hs,hc]
  dsimp only [F]
  simp only [zsmul_eq_mul]
  ring

/-- This local comparison supplies actual manifold-to-patch integral values,
without requesting equality of those values as display data. -/
theorem weighted_chart_patch_integral : weighted_chart_patch_integralType := by
  intro k n O M o hM hMO c P hsource hmap hd omega ho w hw s hsign hs hr
  let eta : TangentTopField 1 k M := fun x => w x • tangentRestriction 1 k M omega x
  have hcont : ContinuousTopField eta :=
    D04.ManifoldIntegralIndependence.continuousTopField_weight w hw
      (D04Stokes.tangentRestriction_top_continuous o.manifold O omega hMO ho)
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hM
  have hc : IsCompact (topSupport eta) := isClosed_closure.isCompact
  have hsupport : topSupport eta ⊆ tsupport (fun x : M => w x) := by
    apply closure_mono
    intro x hx
    change w x ≠ 0
    intro hz
    exact hx (by simp [eta,hz])
  obtain ⟨R⟩ := D04.ManifoldIntegral.signed_partition_exists o (topSupport eta) hc
  have hsingle := D04.ManifoldIntegralIndependence.oriented_single_chart o eta hcont hc
    R c (hsupport.trans hs) s hsign
  have hb := GeometricPatches.chart_integral_bridge c P hsource hmap hd omega ho w hw.continuousOn
  let f : c.source → ℝ := fun u => if u.val ∈ P.region then
    localizedTopCoefficient (ambientRestriction omega) c w u else 0
  have he : topCoefficient eta c = f := by
    funext u
    by_cases hu : u.val ∈ P.region
    · simp only [f,ite_eq_left hu]
      exact D04.ManifoldIntegralIndependence.topCoefficient_weight w
        (tangentRestriction 1 k M omega) c u
    · simp only [f,ite_eq_right hu]
      have hz : w (c.toFun u) = 0 := by
        by_contra hn
        let x : M := chartPoint c u
        have hx : x ∈ tsupport (fun x : M => w x) := subset_tsupport _ hn
        have hv := hr x hx
        apply hu
        simpa only [x,chartPoint,c.left_inv u u.property] using hv
      change w (c.toFun u) * topCoefficient (tangentRestriction 1 k M omega) c u = 0
      rw [hz,zero_mul]
  have hv : Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
      (topCoefficient eta c) = patchIntegral P w omega := by
    rw [he]
    exact hb.2
  refine ⟨hcont,hc,⟨R⟩,?_⟩
  intro Q
  have hQ := D04.ManifoldIntegral.top_coefficients_integrable eta hcont Q.toChartPartition
  refine ⟨fun i => (hQ i).2.2,?_⟩
  exact (D04.ManifoldIntegralIndependence.oriented_independent o eta hcont Q R).trans
    (hsingle.2.trans (congrArg (s.val * ·) hv))

/-- Proper Darboux coefficient integrals ignore a content-zero set, even
when their parameter domains are not bounded Jordan regions. -/
lemma coefficientIntegral_congr_off {k : ℕ} {S T : Set (E k)} {f : S → ℝ} {g : T → ℝ}
    (hf : Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable f)
    (hg : Specs.D04.C15.DirectedSubstitution.Model.ProperIntegrable g)
    {Z : Set (E k)} (hZ : Specs.D04.C06.NullCovers.Model.ContentZero Z)
    (he : ∀ x, x ∉ Z → Specs.D04.C06.JordanRegions.Model.zeroExtension f x =
      Specs.D04.C06.JordanRegions.Model.zeroExtension g x) :
    Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f =
      Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral g := by
  let U := Function.support (Specs.D04.C06.JordanRegions.Model.zeroExtension f) ∪
    Function.support (Specs.D04.C06.JordanRegions.Model.zeroExtension g)
  obtain ⟨Q,hQ⟩ := (D04.JordanRegions.encloses_exists_iff_bounded U).mpr (hf.1.union hg.1)
  obtain ⟨hfi,hfv⟩ := D04.DirectedSubstitution.proper_on_box hf Q
    ((closure_mono subset_union_left).trans hQ)
  obtain ⟨hgi,hgv⟩ := D04.DirectedSubstitution.proper_on_box hg Q
    ((closure_mono subset_union_right).trans hQ)
  have hfve : Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral f =
      Specs.D04.C06.DarbouxIntegral.Model.integral _ Q hfi := hfv
  have hgve : Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral g =
      Specs.D04.C06.DarbouxIntegral.Model.integral _ Q hgi := hgv
  rw [hfve,hgve]
  cases k with
  | zero =>
    change Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral _ Q =
      Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral _ Q
    have hn : (0 : E 0) ∉ Z := by
      intro hz
      apply D04.NullCovers.zero_dim_point_not_null
      exact D04.NullCovers.null_mono (singleton_subset_iff.mpr hz)
        (D04.NullCovers.contentZero_null hZ)
    exact (D04.Darboux.zero_dimension Q
      (Specs.D04.C06.JordanRegions.Model.zeroExtension f)).2.2.1.trans
        ((he 0 hn).trans (D04.Darboux.zero_dimension Q
          (Specs.D04.C06.JordanRegions.Model.zeroExtension g)).2.2.1.symm)
  | succ k =>
    exact D04.ExceptionalSets.integral_eq_of_eq_off_null (Nat.succ_pos _) hfi hgi
      (D04.NullCovers.contentZero_null hZ) (fun x _ hx => he x hx)

/-- The patch may omit finitely many lower-dimensional seams. The comparison
uses actual zero extensions and proves their negligible discrepancy. -/
theorem weighted_chart_patch_integral_off_seams :
    weighted_chart_patch_integral_off_seamsType := by
  intro k n O M o hM hMO c P hsource hmap hd seams omega ho w hw s hsign hs hr
  let eta : TangentTopField 1 k M := fun x => w x • tangentRestriction 1 k M omega x
  have hcont : ContinuousTopField eta :=
    D04.ManifoldIntegralIndependence.continuousTopField_weight w hw
      (D04Stokes.tangentRestriction_top_continuous o.manifold O omega hMO ho)
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hM
  have hc : IsCompact (topSupport eta) := isClosed_closure.isCompact
  have hsupport : topSupport eta ⊆ tsupport (fun x : M => w x) := by
    apply closure_mono
    intro x hx
    change w x ≠ 0
    intro hz
    exact hx (by simp [eta,hz])
  obtain ⟨R⟩ := D04.ManifoldIntegral.signed_partition_exists o (topSupport eta) hc
  have hsingle := D04.ManifoldIntegralIndependence.oriented_single_chart o eta hcont hc
    R c (hsupport.trans hs) s hsign
  have hb := GeometricPatches.chart_integral_bridge c P hsource hmap hd omega ho w hw.continuousOn
  let f : c.source → ℝ := fun u => if u.val ∈ P.region then
    localizedTopCoefficient (ambientRestriction omega) c w u else 0
  have he : ∀ z, z ∉ seams.carrier →
      Specs.D04.C06.JordanRegions.Model.zeroExtension (topCoefficient eta c) z =
        Specs.D04.C06.JordanRegions.Model.zeroExtension f z := by
    intro z hz
    by_cases hu : z ∈ c.source
    · rw [show Specs.D04.C06.JordanRegions.Model.zeroExtension (topCoefficient eta c) z =
          topCoefficient eta c ⟨z,hu⟩ from D04.JordanRegions.zeroExtension_apply _ ⟨z,hu⟩,
        show Specs.D04.C06.JordanRegions.Model.zeroExtension f z = f ⟨z,hu⟩ from
          D04.JordanRegions.zeroExtension_apply f ⟨z,hu⟩]
      by_cases hp : z ∈ P.region
      · simp only [f,ite_eq_left hp]
        exact D04.ManifoldIntegralIndependence.topCoefficient_weight w
          (tangentRestriction 1 k M omega) c ⟨z,hu⟩
      · simp only [f,ite_eq_right hp]
        have hwz : w (c.toFun z) = 0 := by
          by_contra hn
          let x : M := chartPoint c ⟨z,hu⟩
          have hx : x ∈ tsupport (fun x : M => w x) := subset_tsupport _ hn
          have hv := hr x hx
          have hi : c.invFun x = z := c.left_inv z hu
          rw [hi] at hv
          exact hv.elim hp hz
        change w (c.toFun z) * topCoefficient (tangentRestriction 1 k M omega) c ⟨z,hu⟩ = 0
        rw [hwz,zero_mul]
    · rw [show Specs.D04.C06.JordanRegions.Model.zeroExtension (topCoefficient eta c) z = 0 from
          D04.JordanRegions.zeroExtension_of_not_mem _ hu,
        show Specs.D04.C06.JordanRegions.Model.zeroExtension f z = 0 from
          D04.JordanRegions.zeroExtension_of_not_mem f hu]
  have hv : Specs.D04.C15.DirectedSubstitution.Model.coefficientIntegral
      (topCoefficient eta c) = patchIntegral P w omega :=
    (coefficientIntegral_congr_off hsingle.1 hb.1
      (GeometricPatches.seams_contentZero seams) he).trans hb.2
  refine ⟨hcont,hc,⟨R⟩,?_⟩
  intro Q
  have hQ := D04.ManifoldIntegral.top_coefficients_integrable eta hcont Q.toChartPartition
  refine ⟨fun i => (hQ i).2.2,?_⟩
  exact (D04.ManifoldIntegralIndependence.oriented_independent o eta hcont Q R).trans
    (hsingle.2.trans (congrArg (s.val * ·) hv))

/-- Finite geometric decomposition of a chart-supported integral. Extensions
of the individual patches need agree only on their Jordan regions. -/
theorem weighted_chart_patch_cover : weighted_chart_patch_coverType := by
  intro k n l O M o hM hMO hO c P hsource hmap seams hp omega ho w hw s hsign hs hr
  let S : Set (E k) := ⋃ t, (P t).region
  have hS : Specs.D04.C06.JordanRegions.Model.Jordan S := by
    simpa only [Finset.mem_univ, iUnion_true] using
      D04.JordanRegions.jordan_finite_union Finset.univ (fun t => (P t).region)
        (fun t _ => (P t).jordan)
  have hSc : closure S ⊆ c.source := by
    rw [show S = ⋃ t, (P t).region from rfl, closure_iUnion_of_finite]
    exact iUnion_subset (fun t => hsource t)
  obtain ⟨Q,hQS,hQmap,hQd⟩ := GeometricPatches.chart_patch_exists c
    o.manifold.1 O hO S hS hSc
    (fun u hu => hMO (c.map_source (hSc hu)).1)
  have hQsource : Q.region ⊆ c.source := by
    rw [hQS]; exact subset_closure.trans hSc
  have hQ := weighted_chart_patch_integral_off_seams o hM hMO c Q hQsource
    (fun u hu => hQmap (subset_closure (hQS ▸ hu)))
    (fun u hu => hQd u (subset_closure (hQS ▸ hu))) seams omega ho w hw s hsign hs
    (fun x hx => by rw [hQS]; exact hr x hx)
  have hsub (t : Fin l) : (P t).region ⊆ Q.region := by
    rw [hQS]; exact subset_iUnion (fun t => (P t).region) t
  have hcover := GeometricPatches.finite_region_cover Q omega ho w hw.continuousOn
    (fun t => (P t).region) (fun t => (P t).jordan) hsub hQS seams hp
  have hv (t : Fin l) : patchIntegral
      (restrictPatch Q (P t).region (P t).jordan (hsub t)) w omega =
      patchIntegral (P t) w omega := by
    apply GeometricPatches.representative_independent
      (restrictPatch Q (P t).region (P t).jordan (hsub t)) (P t) rfl
    · intro u hu
      exact (hQmap (subset_closure (hQS ▸ hsub t hu))).trans (hmap t hu).symm
    · exact ho
    · exact hw.continuousOn
  simp_rw [hv] at hcover
  rw [hcover, Finset.mul_sum] at hQ
  exact hQ

/-- Independently extended geometric pieces may be transported into a reference
chart before applying the finite cover comparison. -/
theorem transported_chart_patch_cover : transported_chart_patch_coverType := by
  intro k n l O M o hM hMO hO c S hS hsource seams hp P delta hd h he s tSign
    hsign hts omega ho w hw hs hr
  have hex t := GeometricPatches.chart_patch_exists c o.manifold.1 O hO
    (S t) (hS t) (hsource t) (fun u hu => hMO (c.map_source (hsource t hu)).1)
  choose R hR hmap hdiff using hex
  have hRsource t : closure (R t).region ⊆ c.source := by
    rw [hR t]; exact hsource t
  have hRmap t : EqOn (R t).map c.toFun (R t).region := by
    intro u hu
    exact hmap t (by rw [← hR t]; exact subset_closure hu)
  have hpair : ∀ i j, i ≠ j → (R i).region ∩ (R j).region ⊆ seams.carrier := by
    intro i j hij
    rw [hR i,hR j]
    exact hp i j hij
  have hsupport : ∀ x ∈ tsupport (fun x : M => w x),
      c.invFun x ∈ (⋃ t, (R t).region) ∪ seams.carrier := by
    simpa only [hR] using hr
  have hI := weighted_chart_patch_cover o hM hMO hO c R hRsource hRmap seams hpair
    omega ho w hw s hsign hs hsupport
  have hv t : patchIntegral (R t) w omega = delta t * patchIntegral (P t) w omega := by
    let h' : LocalReparametrization (R t).region (P t).region (delta t) := {
      map := (h t).map
      bijective := by rw [hR t]; exact (h t).bijective
      localCharts := by rw [hR t]; exact (h t).localCharts }
    apply GeometricPatches.local_reparametrization (R t) (P t) (delta t) (hd t) h'
    · intro u hu
      exact (hRmap t hu).trans (he t (by rwa [← hR t]))
    · exact ho
    · exact hw.continuousOn
  have heq : (∑ t, s.val * patchIntegral (R t) w omega) =
      ∑ t, (tSign t).val * patchIntegral (P t) w omega := by
    apply Finset.sum_congr rfl
    intro t _
    rw [hv t, ← mul_assoc,hts t]
  rw [heq] at hI
  exact hI

/-- Build the local extension data from the upstream transition theorem;
no common Euclidean extension over the entire closed region is required. -/
theorem chart_region_reparametrization : chart_region_reparametrizationType := by
  intro k n M c d hkn S T delta hsource hbij hsign
  refine ⟨⟨chartTransition c d,hbij,?_⟩,rfl⟩
  intro x hx
  have hxcd := hsource hx
  obtain ⟨e,hxe,he,hei,heq,hde⟩ := D04.DirectedSubstitution.local_transition_diffeomorph
    c d (by constructor <;> norm_num) hkn hxcd
  let C := connectedComponentIn e.source x
  let er := e.restrOpen C e.open_source.connectedComponentIn
  have hC : C ⊆ e.source := connectedComponentIn_subset e.source x
  have hsrc : er.source = C := inter_eq_right.mpr hC
  have hxC : x ∈ C := mem_connectedComponentIn hxe
  have hxer : x ∈ er.source := hsrc ▸ hxC
  have her : ContDiffOn ℝ 1 er er.source := he.mono inter_subset_left
  have hier : ContDiffOn ℝ 1 er.symm er.target := hei.mono inter_subset_left
  obtain ⟨sigma,_,hsg⟩ := D04.DirectedSubstitution.open_sign er her hier
    (hsrc ▸ isPreconnected_connectedComponentIn)
  have hsig : sigma = delta := by
    calc
      sigma = Real.sign ((fderiv ℝ er x).det) := (hsg x hxer).symm
      _ = Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det) :=
        congrArg (fun A => Real.sign A.det) (hde x ⟨hxcd,hxe⟩)
      _ = delta := hsign x hx
  refine ⟨er,hxer,her,hier,?_,?_⟩
  · intro y hy
    exact heq ⟨hsource hy.1,hC (hsrc ▸ hy.2)⟩
  · intro y hy
    exact (hsg y hy).trans hsig

/-- A locally represented parameter diffeomorphism transports arbitrary
Jordan regions. The proof first localizes into Jordan pieces, avoiding any
assumption that the original region has unique derivatives. -/
theorem local_reparametrization_image : local_reparametrization_imageType := by
  intro k S T delta hS h
  classical
  have hK : IsCompact (closure S) := (D04.JordanRegions.jordan_bounded hS).isCompact_closure
  choose e hxe he hei heq hsign using fun x : closure S => h.localCharts x x.property
  have hcover : closure S ⊆ ⋃ x : closure S, (e x).source := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, hxe ⟨x,hx⟩⟩
  obtain ⟨m,a,R,hR,hRS,hRe,hdisj,hunion⟩ :=
    GeometricPatches.jordan_localization S hS (fun x : closure S => (e x).source)
      (fun x => (e x).open_source) hcover
  have himage (i : Fin m) : (e (a i)) '' R i = h.map '' R i := by
    apply Set.EqOn.image_eq
    intro x hx
    exact heq (a i) ⟨subset_closure (hRS i hx),hRe i (subset_closure hx)⟩
  have hj (i : Fin m) : Specs.D04.C06.JordanRegions.Model.Jordan (h.map '' R i) := by
    rw [← himage i]
    exact (D04.RegionSubstitution.jordan_image (e (a i)) (he _) (hei _) (R i)
      (hR i) (D04.JordanRegions.jordan_bounded (hR i)).isCompact_closure (hRe i)).2
  have hT : T = ⋃ i, h.map '' R i := by
    calc
      T = h.map '' S := h.bijective.image_eq.symm
      _ = h.map '' (⋃ i, R i) := congrArg (fun V => h.map '' V) hunion
      _ = _ := image_iUnion
  have hjT : Specs.D04.C06.JordanRegions.Model.Jordan T := by
    rw [hT]
    simpa only [Finset.mem_univ, iUnion_true] using
      D04.JordanRegions.jordan_finite_union Finset.univ (fun i => h.map '' R i)
        (fun i _ => hj i)
  obtain ⟨F,hF,hFeq⟩ := GeometricPatches.compact_local_extension (closure S) h.map hK (by
    intro x hx
    obtain ⟨e,hxe,he,hei,heq,hsg⟩ := h.localCharts x hx
    exact ⟨e.source,e,e.open_source,hxe,he,heq⟩)
  have hcont : ContinuousOn h.map (closure S) :=
    hF.continuous.continuousOn.congr hFeq.symm
  exact ⟨hjT,(D04.JordanRegions.jordan_bounded hjT).isCompact_closure,
    (congrArg closure h.bijective.image_eq).symm.trans
      (image_closure_of_isCompact hK hcont).symm⟩

/-- Both directions of a chart-region transport are built from geometry.
In particular the reverse determinant sign is not an extra display field. -/
theorem chart_region_transport : chart_region_transportType := by
  intro k n M o c d s t hcs hdt R hR hsource
  let S := chartTransition d c '' R
  have hbij : BijOn (chartTransition d c) R S := by
    refine ⟨mapsTo_image _ _,?_,surjOn_image _ _⟩
    intro x hx y hy hxy
    exact (D04.EmbeddedChart.transition_left_inv d c (hsource (subset_closure hx))).symm.trans
      ((congrArg (chartTransition c d) hxy).trans
        (D04.EmbeddedChart.transition_left_inv d c (hsource (subset_closure hy))))
  have hdet (a b : EmbeddedChart 1 k n M) (p q : PointSign)
      (ha : ∀ u : a.source, chartSign o.atPoint a u u.property = p.val)
      (hb : ∀ u : b.source, chartSign o.atPoint b u u.property = q.val)
      (u : E k) (hu : u ∈ chartOverlap a b) :
      Real.sign ((fderivWithin ℝ (chartTransition a b) (chartOverlap a b) u).det) =
        p.val * q.val := by
    have hh := D04.Orientations.chartSign_transition o.atPoint a b o.manifold.1
      o.manifold.2.1 u hu (D04.EmbeddedChart.transition_mem a b hu).1
    rw [ha ⟨u,hu.1⟩, hb ⟨_,(D04.EmbeddedChart.transition_mem a b hu).1⟩] at hh
    rcases q.property with hq | hq <;> rw [hq] at hh ⊢ <;> linarith
  obtain ⟨f,hf⟩ := chart_region_reparametrization d c o.manifold.2.1 R S
    (t.val * s.val) hsource hbij (fun u hu => hdet d c t s hdt hcs u (hsource hu))
  have hjS := local_reparametrization_image hR f
  have hcl : closure S = chartTransition d c '' closure R := by rw [hjS.2.2,hf]
  have hSc : closure S ⊆ chartOverlap c d := by
    rw [hcl]
    rintro y ⟨u,hu,rfl⟩
    exact D04.EmbeddedChart.transition_mem d c (hsource hu)
  have hrev : BijOn (chartTransition c d) S R := by
    refine ⟨?_,?_,?_⟩
    · rintro y ⟨u,hu,rfl⟩
      rw [D04.EmbeddedChart.transition_left_inv d c (hsource (subset_closure hu))]
      exact hu
    · intro x hx y hy hxy
      exact (D04.EmbeddedChart.transition_left_inv c d (hSc (subset_closure hx))).symm.trans
        ((congrArg (chartTransition d c) hxy).trans
          (D04.EmbeddedChart.transition_left_inv c d (hSc (subset_closure hy))))
    · intro u hu
      refine ⟨chartTransition d c u,mem_image_of_mem _ hu,?_⟩
      exact D04.EmbeddedChart.transition_left_inv d c (hsource (subset_closure hu))
  obtain ⟨h,hh⟩ := chart_region_reparametrization c d o.manifold.2.1 S R
    (s.val * t.val) hSc hrev (fun u hu => hdet c d s t hcs hdt u (hSc hu))
  refine ⟨S,rfl,hjS.1,hSc,h,hh,?_,?_⟩
  · intro u hu
    rw [hh]
    exact (d.right_inv _ ⟨(c.map_source (hSc (subset_closure hu)).1).1,
      (hSc (subset_closure hu)).2⟩).symm
  · rcases s.property with hs | hs <;> rw [hs] <;> ring

/-- Compactness lets one shrink against every member of the family at
once, using a signed chart when the point lies on it and its closed complement
otherwise. This also handles distinct intersecting boundary manifolds. -/
theorem simultaneous_chart_localization : simultaneous_chart_localizationType := by
  intro k n q B o hB ι U hU hcover
  classical
  let K := ⋃ j, B j
  have hK : IsCompact K := isCompact_iUnion hB
  have hex (x : K) (j : Fin q) :
      ∃ V : Set (E n), IsOpen V ∧ x.val ∈ V ∧
        (Disjoint V (B j) ∨ ∃ (c : EmbeddedChart 1 k n (B j)) (s : PointSign),
          V ⊆ c.ambient ∧ ∀ u : c.source,
            chartSign (o j).atPoint c u u.property = s.val) := by
    by_cases hx : x.val ∈ B j
    · obtain ⟨c,s,hxc,hcs⟩ := D04.ManifoldIntegral.constant_signed_chart_at (o j) ⟨x,hx⟩
      exact ⟨c.ambient,c.ambient_open,hxc,Or.inr ⟨c,s,Subset.rfl,hcs⟩⟩
    · refine ⟨(B j)ᶜ,(hB j).isClosed.isOpen_compl,hx,Or.inl ?_⟩
      exact disjoint_compl_left
  choose V hV hxV hcases using hex
  choose alpha halpha using fun x : K => mem_iUnion.mp (hcover x.property)
  let W : K → Set (E n) := fun x => U (alpha x) ∩ ⋂ j, V x j
  have hW (x : K) : IsOpen (W x) :=
    (hU _).inter (isOpen_iInter_of_finite (fun j => hV x j))
  have hKW : K ⊆ ⋃ x : K, W x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,halpha ⟨x,hx⟩,mem_iInter.mpr (hxV ⟨x,hx⟩)⟩
  obtain ⟨m,b,A,hA⟩ := GeometricPatches.ambient_partition_exists K hK W hW hKW
  refine ⟨m,fun i => alpha (b i),A,fun i => (hA i).trans inter_subset_left,?_⟩
  intro i j
  have hsub : tsupport (A.weight i) ⊆ V (b i) j := by
    intro x hx
    exact mem_iInter.mp (hA i hx).2 j
  rcases hcases (b i) j with hz | ⟨c,s,hVc,hcs⟩
  · left
    intro x hx
    by_contra hw
    exact Set.disjoint_left.mp hz (hsub (subset_tsupport _ hw)) hx
  · right
    refine ⟨c,s,hcs,?_⟩
    have ht : tsupport (fun x : B j => A.weight i x) ⊆
        Subtype.val ⁻¹' tsupport (A.weight i) :=
      continuous_subtype_val.closure_preimage_subset (Function.support (A.weight i))
    exact ht.trans (preimage_mono (hsub.trans hVc))

/-- Transfer ambient covering and intersection data through the derived chart
transitions, then use the finite chart integral comparison. -/
theorem chart_patches_ambient_cover : chart_patches_ambient_coverType := by
  intro k n l O M o hM hMO hO c s hcs P d tSign hsource hmap hdSign
    seams hp omega ho w hw hs hr
  have hex t := chart_region_transport o c (d t) s (tSign t) hcs (hdSign t)
    (P t).region (P t).jordan (hsource t)
  choose S hSdef hS hSc h hhe hval hsg using hex
  have he (t : Fin l) : EqOn c.toFun ((P t).map ∘ (h t).map) (S t) := by
    intro u hu
    exact (hval t hu).trans (hmap t ((h t).bijective.mapsTo hu)).symm
  have hamb (t : Fin l) {u : E k} (hu : u ∈ S t) :
      c.toFun u ∈ (P t).map '' (P t).region := by
    exact ⟨(h t).map u,(h t).bijective.mapsTo hu,(he t hu).symm⟩
  have hpair : ∀ i j, i ≠ j → S i ∩ S j ⊆ seams.carrier := by
    intro i j hij u hu
    obtain ⟨z,hz,hzu⟩ := hp i j hij ⟨hamb i hu.1,hamb j hu.2⟩
    have hzu' : z = u := by
      have heq := congrArg c.invFun hzu
      rwa [c.left_inv z hz.1,c.left_inv u (hSc i (subset_closure hu.1)).1] at heq
    exact hzu' ▸ hz.2
  have hcover : ∀ x ∈ tsupport (fun x : M => w x),
      c.invFun x ∈ (⋃ t, S t) ∪ seams.carrier := by
    intro x hx
    rcases hr x hx with hpatch | hseam
    · obtain ⟨t,u,hu,hux⟩ := mem_iUnion.mp hpatch
      left
      refine mem_iUnion.mpr ⟨t,?_⟩
      rw [hSdef t]
      refine ⟨u,hu,?_⟩
      change c.invFun ((d t).toFun u) = c.invFun x
      rw [← hmap t hu,hux]
    · right
      obtain ⟨z,hz,hzx⟩ := hseam
      have hi : c.invFun x = z := by
        rw [← hzx,c.left_inv z hz.1]
      rw [hi]
      exact hz.2
  apply transported_chart_patch_cover o hM hMO hO c S hS
    (fun t => (hSc t).trans inter_subset_left) seams hpair P
    (fun t => s.val * (tSign t).val) ?_ h he s tSign hcs hsg
    omega ho w hw hs hcover
  intro t
  rcases s.property with hs | hs <;> rcases (tSign t).property with ht | ht <;>
    simp [hs,ht]

/-- Use open neighborhoods of the support complement, rather than cutting
a Jordan region by an arbitrary closed support. -/
theorem chart_region_weight_localization : chart_region_weight_localizationType := by
  intro k n M c d R hR hsource w hs
  classical
  let V0 : Set d.source := (fun u => d.toFun u) ⁻¹' c.ambient
  let V1 : Set d.source := chartPoint d ⁻¹' (tsupport (fun x : M => w x))ᶜ
  have hV0 : IsOpen V0 := c.ambient_open.preimage d.continuous_toFun.domRestrict
  have hV1 : IsOpen V1 := (isClosed_tsupport _).isOpen_compl.preimage
    (D04.ManifoldIntegral.chartPoint_continuous d)
  obtain ⟨W0,hW0,he0⟩ := isOpen_induced_iff.mp hV0
  obtain ⟨W1,hW1,he1⟩ := isOpen_induced_iff.mp hV1
  let U : Bool → Set (E k) := fun b => if b then W0 else W1
  have hU : ∀ b, IsOpen (U b) := by intro b; cases b <;> assumption
  have hcover : closure R ⊆ ⋃ b, U b := by
    intro u hu
    have hus := hsource hu
    by_cases hx : d.toFun u ∈ c.ambient
    · refine mem_iUnion.mpr ⟨true,?_⟩
      exact show (⟨u,hus⟩ : d.source) ∈ Subtype.val ⁻¹' W0 from he0 ▸ hx
    · refine mem_iUnion.mpr ⟨false,?_⟩
      have hnot : chartPoint d ⟨u,hus⟩ ∉ tsupport (fun x : M => w x) :=
        fun h => hx (hs h)
      exact show (⟨u,hus⟩ : d.source) ∈ Subtype.val ⁻¹' W1 from he1 ▸ hnot
  obtain ⟨m,a,S,hS,hSR,hSU,hdisj,heq⟩ :=
    GeometricPatches.jordan_localization R hR U hU hcover
  refine ⟨m,S,hS,hSR,hdisj,heq,?_⟩
  intro i
  have hcl : closure (S i) ⊆ d.source := (closure_mono (hSR i)).trans hsource
  cases hai : a i with
  | false =>
    right
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,rfl⟩ ⟨y,hy,hyu⟩
    have huW : (⟨u,hcl hu⟩ : d.source) ∈ Subtype.val ⁻¹' W1 := by
      change u ∈ W1
      simpa only [U,hai,Bool.false_eq_true,ite_false] using hSU i hu
    have hnot : chartPoint d ⟨u,hcl hu⟩ ∉ tsupport (fun x : M => w x) := by
      change (⟨u,hcl hu⟩ : d.source) ∈ V1
      rw [← he1]
      exact huW
    apply hnot
    have hxy : y = chartPoint d ⟨u,hcl hu⟩ := Subtype.ext hyu
    exact hxy ▸ hy
  | true =>
    left
    intro u hu
    refine ⟨hcl hu,?_⟩
    have huW : (⟨u,hcl hu⟩ : d.source) ∈ Subtype.val ⁻¹' W0 := by
      change u ∈ W0
      simpa only [U,hai,ite_true] using hSU i hu
    change (⟨u,hcl hu⟩ : d.source) ∈ V0
    rw [← he0]
    exact huW

/-- Lift the actual seam parametrizations using separate ambient inverse
extensions; no differentiability of the chart inverse away from its target
is asserted. -/
theorem chart_seams_lift : chart_seams_liftType := by
  intro k n M c hkn Z hlower hZ
  let A : Seams k := {
    count := Z.count
    dim := Z.dim
    lower := hlower
    parameter := Z.parameter
    compact := Z.compact
    map := fun i => c.invFun ∘ Z.map i
    localC1 := by
      intro i x hx
      have hfx : Z.map i x ∈ M ∩ c.ambient :=
        hZ (mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩)
      obtain ⟨O,J,hO,hJO,hJ,hJeq⟩ := D04.chart_inverse_extension c
        (by constructor <;> norm_num) hkn (c.invFun (Z.map i x)) (c.map_target hfx)
      have hfxO : Z.map i x ∈ O := by
        rwa [c.right_inv _ hfx] at hJO
      obtain ⟨U,g,hU,hg,hgeq⟩ := Z.localC1 i x hx
      have hgx : g x = Z.map i x := hgeq ⟨hx,mem_of_mem_nhds hU⟩
      have hgO : g ⁻¹' O ∈ nhds x :=
        hg.continuousAt.preimage_mem_nhds (by rw [hgx]; exact hO.mem_nhds hfxO)
      refine ⟨U ∩ g ⁻¹' O,J ∘ g,Filter.inter_mem hU hgO,?_,?_⟩
      · exact ((hJ (g x) (by rw [hgx]; exact hfxO)).contDiffAt
          (hO.mem_nhds (by rw [hgx]; exact hfxO))).comp x hg
      · intro y hy
        have hgy : g y = Z.map i y := hgeq ⟨hy.1,hy.2.1⟩
        change J (g y) = c.invFun (Z.map i y)
        rw [hgy]
        exact hJeq ⟨hZ (mem_iUnion.mpr ⟨i,mem_image_of_mem _ hy.1⟩),
          by rw [← hgy]; exact hy.2.2⟩ }
  refine ⟨A,?_⟩
  ext y
  simp only [Seams.carrier, A, image_iUnion, image_image]
  rfl

/-- Closed restrictions of geometric seams are still finite compact
locally C¹ pieces. This permits cutting seams by compact patch images. -/
theorem seams_closed_restriction : seams_closed_restrictionType := by
  intro k n Z hlower H hH
  have hc (i : Fin Z.count) : ContinuousOn (Z.map i) (Z.parameter i) := by
    intro x hx
    obtain ⟨U,g,hU,hg,heq⟩ := Z.localC1 i x hx
    apply hg.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem _ hx
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hU] with y hy hyU
    exact (heq ⟨hy,hyU⟩).symm
  have hK (i : Fin Z.count) : IsCompact (Z.parameter i ∩ Z.map i ⁻¹' H) := by
    letI : CompactSpace (Z.parameter i) := isCompact_iff_compactSpace.mp (Z.compact i)
    have hp : IsCompact ((fun x : Z.parameter i => Z.map i x) ⁻¹' H) :=
      (hH.preimage (hc i).domRestrict).isCompact
    have he : Subtype.val '' ((fun x : Z.parameter i => Z.map i x) ⁻¹' H) =
        Z.parameter i ∩ Z.map i ⁻¹' H := by
      ext x
      constructor
      · rintro ⟨u,hu,rfl⟩; exact ⟨u.property,hu⟩
      · rintro ⟨hx,hfx⟩; exact ⟨⟨x,hx⟩,hfx,rfl⟩
    rw [← he]
    exact hp.image continuous_subtype_val
  let A : Seams n := {
    count := Z.count
    dim := Z.dim
    lower := Z.lower
    parameter := fun i => Z.parameter i ∩ Z.map i ⁻¹' H
    compact := hK
    map := Z.map
    localC1 := by
      intro i x hx
      obtain ⟨U,g,hU,hg,heq⟩ := Z.localC1 i x hx.1
      exact ⟨U,g,hU,hg,fun y hy => heq ⟨hy.1.1,hy.2⟩⟩ }
  refine ⟨A,hlower,?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨i,u,hu,rfl⟩ := mem_iUnion.mp hy
    exact ⟨mem_iUnion.mpr ⟨i,mem_image_of_mem _ hu.1⟩,hu.2⟩
  · rintro ⟨hy,hHy⟩
    obtain ⟨i,u,hu,rfl⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨i,mem_image_of_mem _ ⟨hu,hHy⟩⟩

/-- Vanishing of the actual ambient weight on the patch gives the zero
Darboux integral, including in parameter dimension zero. -/
lemma patch_integral_zero_of_weight_zero {k n} {O : Set (E n)} (P : Patch k O)
    (w : E n → ℝ) (omega : FormField n k)
    (hz : ∀ u ∈ P.region, w (P.map u) = 0) : patchIntegral P w omega = 0 := by
  have he : Specs.D04.C06.JordanRegions.Model.zeroExtension
      (fun u : P.region => weightedCoefficient P w omega u) = (fun _ => 0) := by
    funext u
    by_cases hu : u ∈ P.region
    · refine (D04.JordanRegions.zeroExtension_apply
        (fun v : P.region => weightedCoefficient P w omega v) ⟨u,hu⟩).trans ?_
      change w (P.map u) * Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient P omega u = 0
      rw [hz u hu,zero_mul]
    · exact D04.JordanRegions.zeroExtension_of_not_mem _ hu
  change Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral _
    (Specs.D04.C06.JordanRegions.Model.enclosingBox P.region) = 0
  rw [he]
  exact (D04.Darboux.constant_integrals _ 0).1.trans (zero_mul _)

/-- The refinement chooses Jordan regions through an open cover; the support
is used only to prove the complementary terms vanish. -/
theorem weighted_patch_chart_refinement : weighted_patch_chart_refinementType := by
  intro k n O M c d P hsource hmap w hw hs
  classical
  obtain ⟨m,S,hS,hSP,hdisj,hunion,hcases⟩ :=
    chart_region_weight_localization c d P.region P.jordan hsource w hs
  have hzero (i : Fin m) (hi : ¬ closure (S i) ⊆ chartOverlap d c) :
      ∀ u ∈ closure (S i), w (P.map u) = 0 := by
    have hz := (hcases i).resolve_left hi
    intro u hu
    by_contra hn
    have huP := closure_mono (hSP i) hu
    have hdsource := hsource huP
    let x : M := ⟨d.toFun u,(d.map_source hdsource).1⟩
    have hx : x ∈ tsupport (fun x : M => w x) :=
      subset_tsupport _ (by change w (d.toFun u) ≠ 0; rwa [← hmap huP])
    exact Set.disjoint_left.mp hz (mem_image_of_mem _ hu) ⟨x,hx,rfl⟩
  refine ⟨m,S,hS,hSP,hdisj,hunion,?_,?_⟩
  · intro i
    by_cases hi : closure (S i) ⊆ chartOverlap d c
    · exact Or.inl hi
    · exact Or.inr (hzero i hi)
  · intro omega ho
    have hnull : Specs.D04.C06.NullCovers.Model.ContentZero (∅ : Set (E k)) :=
      D04.NullCovers.compact_null_contentZero _ isCompact_empty D04.ExceptionalSets.null_empty
    have hp : ∀ i j, i ≠ j → S i ∩ S j ⊆ (∅ : Set (E k)) := by
      intro i j hij u hu
      exact False.elim (Set.disjoint_left.mp (hdisj hij) hu.1 hu.2)
    have hsum := GeometricPatches.region_integral_finite_cover P.jordan
      (weightedCoefficient P w omega) (GeometricPatches.weighted_continuous P omega ho w
        hw.continuousOn) S hS hSP hunion hnull hp
    change patchIntegral P w omega =
      ∑ i, patchIntegral (restrictPatch P (S i) (hS i) (hSP i)) w omega at hsum
    refine hsum.trans (Finset.sum_congr rfl ?_)
    intro i _
    split_ifs with hi
    · rfl
    · apply patch_integral_zero_of_weight_zero
      intro u hu
      exact hzero i hi u (subset_closure hu)

/-- The ambient-cover comparison is unchanged by finite reindexing. -/
lemma chart_patches_ambient_cover_finite {k n : ℕ} {ι : Type} [Fintype ι]
    {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M)
    (hM : IsCompact M) (hMO : M ⊆ O) (hO : IsOpen O)
    (c : EmbeddedChart 1 k n M) (s : PointSign)
    (hcs : ∀ u : c.source, chartSign o.atPoint c u u.property = s.val)
    (P : ι → Patch k O) (d : ι → EmbeddedChart 1 k n M) (tSign : ι → PointSign)
    (hsource : ∀ t, closure (P t).region ⊆ chartOverlap (d t) c)
    (hmap : ∀ t, EqOn (P t).map (d t).toFun (P t).region)
    (hdSign : ∀ t (u : (d t).source), chartSign o.atPoint (d t) u u.property = (tSign t).val)
    (seams : Seams k)
    (hp : ∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩ ((P j).map '' (P j).region) ⊆
      c.toFun '' (c.source ∩ seams.carrier))
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (w : E n → ℝ) (hw : Continuous w)
    (hs : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient)
    (hr : ∀ x ∈ tsupport (fun x : M => w x),
      x.val ∈ (⋃ t, (P t).map '' (P t).region) ∪ c.toFun '' (c.source ∩ seams.carrier)) :
    HasPositiveIntegral o (fun x => w x • tangentRestriction 1 k M omega x)
      (∑ t, (tSign t).val * patchIntegral (P t) w omega) := by
  let e := Fintype.equivFin ι
  have h := chart_patches_ambient_cover o hM hMO hO c s hcs
    (fun t => P (e.symm t)) (fun t => d (e.symm t)) (fun t => tSign (e.symm t))
    (fun t => hsource _) (fun t => hmap _) (fun t => hdSign _) seams
    (fun i j hij => hp _ _ (fun h => hij (e.symm.injective h))) omega ho w hw hs
    (fun x hx => by
      rcases hr x hx with hp | hz
      · obtain ⟨t,ht⟩ := mem_iUnion.mp hp
        exact Or.inl (mem_iUnion.mpr ⟨e t,by simpa only [Equiv.symm_apply_apply] using ht⟩)
      · exact Or.inr hz)
  rw [e.symm.sum_comp (fun t => (tSign t).val * patchIntegral (P t) w omega)] at h
  exact h

/-- Refine every displayed patch against the actual relative weight support.
The original weighted sum is recovered after the comparison in the reference
chart; no region or integral identity is required from the display. -/
theorem weighted_chart_display : weighted_chart_displayType := by
  intro k n l O M o hM hMO hO P d s hsource hmap hsign Z hlower hp hcover
    c cs hcs omega ho w hw hs
  classical
  have hex t := chart_region_weight_localization c (d t) (P t).region
    (P t).jordan (hsource t) w hs
  choose m S hS hSP hdisj hunion hcases using hex
  let T := (t : Fin l) × Fin (m t)
  let good : T → Prop := fun z => closure (S z.1 z.2) ⊆ chartOverlap (d z.1) c
  let I := {z : T // good z}
  let Q : I → Patch k O := fun z =>
    restrictPatch (P z.val.1) (S z.val.1 z.val.2) (hS _ _) (hSP _ _)
  have hQsource (z : I) : closure (Q z).region ⊆ chartOverlap (d z.val.1) c := z.property
  have hQmap (z : I) : EqOn (Q z).map (d z.val.1).toFun (closure (Q z).region) :=
    (hmap _).mono (closure_mono (hSP _ _))
  have hQcompact (z : I) : IsCompact ((Q z).map '' closure (Q z).region) :=
    (GeometricPatches.region_compact (Q z)).image_of_continuousOn
      ((Q z).regular.continuousOn.mono (Q z).contains)
  have hQtarget (z : I) : (Q z).map '' closure (Q z).region ⊆ M ∩ c.ambient := by
    rintro y ⟨u,hu,rfl⟩
    rw [hQmap z hu]
    exact ⟨((d z.val.1).map_source (hQsource z hu).1).1,(hQsource z hu).2⟩
  let W := tsupport (fun x : M => w x)
  have hW : IsCompact (Subtype.val '' W) := by
    letI : CompactSpace M := isCompact_iff_compactSpace.mp hM
    exact (isClosed_tsupport _).isCompact.image continuous_subtype_val
  let H := (⋃ z : I, (Q z).map '' closure (Q z).region) ∪ Subtype.val '' W
  have hH : IsCompact H := (isCompact_iUnion hQcompact).union hW
  have hHtarget : H ⊆ M ∩ c.ambient := by
    rintro y (hy | ⟨x,hx,rfl⟩)
    · obtain ⟨z,hz⟩ := mem_iUnion.mp hy
      exact hQtarget z hz
    · exact ⟨x.property,hs hx⟩
  obtain ⟨Z',hlower',hZ'⟩ := seams_closed_restriction Z hlower H hH.isClosed
  obtain ⟨A,hA⟩ := chart_seams_lift c o.manifold.2.1 Z' hlower'
    (fun y hy => hHtarget ((hZ' ▸ hy).2))
  have hseam {y : E n} (hy : y ∈ Z.carrier) (hyH : y ∈ H) :
      y ∈ c.toFun '' (c.source ∩ A.carrier) := by
    have hyt := hHtarget hyH
    refine ⟨c.invFun y,⟨c.map_target hyt,?_⟩,c.right_inv y hyt⟩
    rw [hA]
    exact mem_image_of_mem _ (by rw [hZ']; exact ⟨hy,hyH⟩)
  have hQpair : ∀ i j : I, i ≠ j →
      ((Q i).map '' (Q i).region) ∩ ((Q j).map '' (Q j).region) ⊆
        c.toFun '' (c.source ∩ A.carrier) := by
    intro i j hij y hy
    have hyH : y ∈ H := Or.inl (mem_iUnion.mpr
      ⟨i,image_mono subset_closure hy.1⟩)
    apply hseam _ hyH
    by_cases ht : i.val.1 = j.val.1
    · obtain ⟨u,hu,huy⟩ := hy.1
      obtain ⟨v,hv,hvy⟩ := hy.2
      have huSource := hsource _ (subset_closure (hSP _ _ hu))
      have hvSource : v ∈ (d i.val.1).source := by
        rw [ht]; exact hsource _ (subset_closure (hSP _ _ hv))
      have hmaps : (d i.val.1).toFun u = (d i.val.1).toFun v :=
        (hQmap i (subset_closure hu)).symm.trans
          (huy.trans (hvy.symm.trans (by rw [ht]; exact hQmap j (subset_closure hv))))
      have huv : u = v := ((d i.val.1).left_inv u huSource).symm.trans
        ((congrArg (d i.val.1).invFun hmaps).trans ((d i.val.1).left_inv v hvSource))
      have hne : i.val ≠ j.val := fun he => hij (Subtype.ext he)
      have hdis : Disjoint (S i.val.1 i.val.2) (S j.val.1 j.val.2) := by
        cases i with | mk i hi =>
          cases j with | mk j hj =>
            rcases i with ⟨it,ii⟩
            rcases j with ⟨jt,ji⟩
            dsimp at ht hne ⊢
            subst jt
            exact hdisj it (fun he => hne (by cases he; rfl))
      exact False.elim (Set.disjoint_left.mp hdis hu (huv.symm ▸ hv))
    · apply hp _ _ ht
      exact ⟨image_mono (hSP _ _) hy.1,image_mono (hSP _ _) hy.2⟩
  have hQcover : ∀ x ∈ W,
      x.val ∈ (⋃ z : I, (Q z).map '' (Q z).region) ∪
        c.toFun '' (c.source ∩ A.carrier) := by
    intro x hx
    rcases hcover x.property with hp | hz
    · obtain ⟨t,u,hu,hux⟩ := mem_iUnion.mp hp
      have huS : u ∈ ⋃ i, S t i := (hunion t) ▸ hu
      obtain ⟨i,hi⟩ := mem_iUnion.mp huS
      by_cases hg : good ⟨t,i⟩
      · exact Or.inl (mem_iUnion.mpr ⟨⟨⟨t,i⟩,hg⟩,u,hi,hux⟩)
      · have hz := (hcases t i).resolve_left hg
        exact False.elim (Set.disjoint_left.mp hz
          (mem_image_of_mem _ (subset_closure hi))
          ⟨x,hx,((hmap t (subset_closure hu)).symm.trans hux).symm⟩)
    · exact Or.inr (hseam hz (Or.inr ⟨x,hx,rfl⟩))
  have hlocal := chart_patches_ambient_cover_finite o hM hMO hO c cs hcs Q
    (fun z => d z.val.1) (fun z => s z.val.1) hQsource
    (fun z => (hQmap z).mono subset_closure) (fun z => hsign _) A hQpair
    omega ho w hw hs hQcover
  have hsum (t : Fin l) : patchIntegral (P t) w omega = ∑ i,
      if good ⟨t,i⟩ then
        patchIntegral (restrictPatch (P t) (S t i) (hS _ _) (hSP _ _)) w omega else 0 := by
    have hnull : Specs.D04.C06.NullCovers.Model.ContentZero (∅ : Set (E k)) :=
      D04.NullCovers.compact_null_contentZero _ isCompact_empty D04.ExceptionalSets.null_empty
    have he := GeometricPatches.region_integral_finite_cover (P t).jordan
      (weightedCoefficient (P t) w omega)
      (GeometricPatches.weighted_continuous (P t) omega ho w hw.continuousOn)
      (S t) (hS t) (hSP t) (hunion t) hnull
      (fun i j hij u hu => False.elim (Set.disjoint_left.mp (hdisj t hij) hu.1 hu.2))
    change patchIntegral (P t) w omega =
      ∑ i, patchIntegral (restrictPatch (P t) (S t i) (hS _ _) (hSP _ _)) w omega at he
    refine he.trans (Finset.sum_congr rfl ?_)
    intro i _
    split_ifs with hi
    · rfl
    · apply patch_integral_zero_of_weight_zero
      intro u hu
      by_contra hn
      have hx : chartPoint (d t) ⟨u,hsource t (subset_closure (hSP t i hu))⟩ ∈ W :=
        subset_tsupport _ (by change w ((d t).toFun u) ≠ 0; rwa [← hmap t (subset_closure (hSP t i hu))])
      exact Set.disjoint_left.mp ((hcases t i).resolve_left hi)
        (mem_image_of_mem _ (subset_closure hu)) ⟨_,hx,rfl⟩
  have hvalues : (∑ z : I, (s z.val.1).val * patchIntegral (Q z) w omega) =
      ∑ t, (s t).val * patchIntegral (P t) w omega := by
    rw [← Finset.sum_subtype (Finset.univ.filter good) (by simp)
      (fun z : T => (s z.1).val * patchIntegral
        (restrictPatch (P z.1) (S z.1 z.2) (hS _ _) (hSP _ _)) w omega),
      Finset.sum_filter]
    change (∑ z : T, if good z then
      (s z.1).val * patchIntegral
        (restrictPatch (P z.1) (S z.1 z.2) (hS _ _) (hSP _ _)) w omega else 0) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t _
    rw [hsum t,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all only [mul_zero]
  rw [hvalues] at hlocal
  exact hlocal

/-- Global decomposition follows by choosing a partition, proving every
localized comparison, then adding actual integrals. -/
theorem chart_display_integral : chart_display_integralType := by
  intro k n l O M o hM hMO P d s hsource hmap hsign Z hlower hp hcover omega ho
  classical
  have himage (t : Fin l) (u : E k) (hu : u ∈ (P t).region) : (P t).map u ∈ M := by
    rw [hmap t (subset_closure hu)]
    exact ((d t).map_source (hsource t (subset_closure hu))).1
  obtain ⟨m,a,A,_,hloc⟩ := simultaneous_chart_localization
    (fun _ : Fin 1 => M) (fun _ => o) (fun _ => hM)
    (fun _ : Unit => (Set.univ : Set (E n))) (fun _ => isOpen_univ)
    (fun x _ => mem_iUnion.mpr ⟨(),mem_univ x⟩)
  have hweights (x : M) : ∑ i, A.weight i x = 1 := by
    obtain ⟨V,_,hV,he⟩ := A.sum_one
    exact he x (hV (mem_iUnion.mpr ⟨0,x.property⟩))
  let I : Fin m → ℝ := fun i => ∑ t, (s t).val * patchIntegral (P t) (A.weight i) omega
  have hI (i : Fin m) : HasPositiveIntegral o
      (fun x => A.weight i x • tangentRestriction 1 k M omega x) (I i) := by
    rcases hloc i 0 with hz | ⟨c,cs,hcs,hs⟩
    · have hfield : (fun x : M => A.weight i x • tangentRestriction 1 k M omega x) = 0 := by
        funext x; rw [hz x x.property,zero_smul]; rfl
      have hvalue : I i = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        rw [patch_integral_zero_of_weight_zero (P t) (A.weight i) omega
          (fun u hu => hz _ (himage t u hu)),mul_zero]
      rw [hfield,hvalue]
      exact D04Stokes.positive_integral_zero o
    · exact weighted_chart_display o hM hMO ho.1 P d s hsource hmap hsign Z
        hlower hp hcover c cs hcs omega ho (A.weight i) (A.smooth i).continuous hs
  have htotal := D04Stokes.positive_integral_sum o
    (fun i => fun x => A.weight i x • tangentRestriction 1 k M omega x)
    I Finset.univ (fun i _ => hI i)
  have he : (∑ i, (fun x : M => A.weight i x • tangentRestriction 1 k M omega x)) =
      tangentRestriction 1 k M omega := by
    funext x
    simp only [Finset.sum_apply]
    rw [← Finset.sum_smul,hweights x,one_smul]
  rw [he] at htotal
  have hpatch (t : Fin l) : patchIntegral (P t) (fun _ => 1) omega =
      ∑ i, patchIntegral (P t) (A.weight i) omega := by
    have hv := GeometricPatches.finite_weight_localization (P t) omega ho
      (fun _ => 1) A.weight continuousOn_const
      (fun i => (A.smooth i).continuous.continuousOn)
      (fun u hu => hweights ⟨(P t).map u,himage t u hu⟩)
    simpa only [one_mul] using hv
  have hvalue : (∑ i, I i) = ∑ t, (s t).val * patchIntegral (P t) (fun _ => 1) omega := by
    dsimp only [I]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [hpatch t,Finset.mul_sum]
  rw [hvalue] at htotal
  exact htotal

/-- Global decomposition is invariant under an arbitrary finite reindexing. -/
lemma chart_display_integral_finite {k n : ℕ} {ι : Type} [Fintype ι]
    {O M : Set (E n)} (o : PositiveManifoldOrientation 1 k M)
    (hM : IsCompact M) (hMO : M ⊆ O)
    (P : ι → Patch k O) (d : ι → EmbeddedChart 1 k n M) (s : ι → PointSign)
    (hsource : ∀ t, closure (P t).region ⊆ (d t).source)
    (hmap : ∀ t, EqOn (P t).map (d t).toFun (closure (P t).region))
    (hsign : ∀ t (u : (d t).source), chartSign o.atPoint (d t) u u.property = (s t).val)
    (Z : Seams n) (hlower : ∀ i, Z.dim i < k)
    (hp : ∀ i j, i ≠ j → ((P i).map '' (P i).region) ∩ ((P j).map '' (P j).region) ⊆ Z.carrier)
    (hcover : M ⊆ (⋃ t, (P t).map '' (P t).region) ∪ Z.carrier)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega) :
    HasPositiveIntegral o (tangentRestriction 1 k M omega)
      (∑ t, (s t).val * patchIntegral (P t) (fun _ => 1) omega) := by
  let e := Fintype.equivFin ι
  have h := chart_display_integral o hM hMO
    (fun t => P (e.symm t)) (fun t => d (e.symm t)) (fun t => s (e.symm t))
    (fun t => hsource _) (fun t => hmap _) (fun t => hsign _) Z hlower
    (fun i j hij => hp _ _ (fun h => hij (e.symm.injective h)))
    (fun x hx => by
      rcases hcover hx with hp | hz
      · obtain ⟨t,ht⟩ := mem_iUnion.mp hp
        exact Or.inl (mem_iUnion.mpr ⟨e t,by simpa only [Equiv.symm_apply_apply] using ht⟩)
      · exact Or.inr hz) omega ho
  rw [e.symm.sum_comp (fun t => (s t).val * patchIntegral (P t) (fun _ => 1) omega)] at h
  exact h

/-- Finite Jordan localization converts locally embedded regular pieces into
chart patches and proves additivity for their actual integrals. -/
theorem regular_display_integral : regular_display_integralType := by
  intro k n l O M o hM hMO P s hregular Z hlower hself hp hcover omega ho
  classical
  choose U d hU hmem hsource hmap hsign using
    fun (t : Fin l) (u : closure (P t).region) => hregular t u u.property
  have hex (t : Fin l) := GeometricPatches.jordan_localization (P t).region
    (P t).jordan (U t) (hU t)
    (fun u hu => mem_iUnion.mpr ⟨⟨u,hu⟩,hmem t ⟨u,hu⟩⟩)
  choose m a S hS hSP hSU hdisj hunion using hex
  let T := (t : Fin l) × Fin (m t)
  let Q : T → Patch k O := fun z => restrictPatch (P z.1) (S z.1 z.2) (hS _ _) (hSP _ _)
  let c : T → EmbeddedChart 1 k n M := fun z => d z.1 (a z.1 z.2)
  have hQc (z : T) : closure (Q z).region ⊆ (c z).source := by
    intro u hu
    exact hsource _ _ ⟨closure_mono (hSP _ _) hu,hSU _ _ hu⟩
  have hQmap (z : T) : EqOn (Q z).map (c z).toFun (closure (Q z).region) := by
    intro u hu
    exact hmap _ _ ⟨closure_mono (hSP _ _) hu,hSU _ _ hu⟩
  have hQpair : ∀ i j : T, i ≠ j →
      ((Q i).map '' (Q i).region) ∩ ((Q j).map '' (Q j).region) ⊆ Z.carrier := by
    intro i j hij y hy
    by_cases ht : i.1 = j.1
    · obtain ⟨u,hu,huy⟩ := hy.1
      obtain ⟨v,hv,hvy⟩ := hy.2
      have hvP : v ∈ (P i.1).region := by rw [ht]; exact hSP _ _ hv
      have hmaps : (P i.1).map u = (P i.1).map v := by
        exact huy.trans (hvy.symm.trans (by rw [ht]; rfl))
      have hdis : Disjoint (S i.1 i.2) (S j.1 j.2) := by
        rcases i with ⟨it,ii⟩
        rcases j with ⟨jt,ji⟩
        dsimp at ht hij ⊢
        subst jt
        exact hdisj it (fun he => hij (by cases he; rfl))
      have hneuv : u ≠ v := by
        intro huv
        exact Set.disjoint_left.mp hdis hu (huv.symm ▸ hv)
      exact huy ▸ hself i.1 u (hSP _ _ hu) v hvP hneuv hmaps
    · exact hp _ _ ht ⟨image_mono (hSP _ _) hy.1,image_mono (hSP _ _) hy.2⟩
  have hQcover : M ⊆ (⋃ z : T, (Q z).map '' (Q z).region) ∪ Z.carrier := by
    intro x hx
    rcases hcover hx with hp | hz
    · obtain ⟨t,u,hu,hux⟩ := mem_iUnion.mp hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp ((hunion t) ▸ hu)
      exact Or.inl (mem_iUnion.mpr ⟨⟨t,i⟩,u,hi,hux⟩)
    · exact Or.inr hz
  have hI := chart_display_integral_finite o hM hMO Q c (fun z => s z.1)
    hQc hQmap (fun z => hsign _ _) Z hlower hQpair hQcover omega ho
  have hsum (t : Fin l) : patchIntegral (P t) (fun _ => 1) omega =
      ∑ i, patchIntegral (Q ⟨t,i⟩) (fun _ => 1) omega := by
    have hnull : Specs.D04.C06.NullCovers.Model.ContentZero (∅ : Set (E k)) :=
      D04.NullCovers.compact_null_contentZero _ isCompact_empty D04.ExceptionalSets.null_empty
    exact GeometricPatches.region_integral_finite_cover (P t).jordan
      (weightedCoefficient (P t) (fun _ => 1) omega)
      (GeometricPatches.weighted_continuous (P t) omega ho (fun _ => 1) continuousOn_const)
      (S t) (hS t) (hSP t) (hunion t) hnull
      (fun i j hij u hu => False.elim (Set.disjoint_left.mp (hdisj t hij) hu.1 hu.2))
  have he : (∑ z : T, (s z.1).val * patchIntegral (Q z) (fun _ => 1) omega) =
      ∑ t, (s t).val * patchIntegral (P t) (fun _ => 1) omega := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t _
    rw [hsum t,Finset.mul_sum]
  rw [he] at hI
  exact hI

/-- Weighting the ambient form preserves its C⁰ coefficients and commutes
with tangential restriction and the canonical patch coefficient. -/
theorem regular_display_weighted_integral : regular_display_weighted_integralType := by
  intro k n l O M o hM hMO P s hregular Z hlower hself hp hcover omega ho w hw
  let theta : FormField n k := fun x => w x • omega x
  have htheta : IsCrForm (some 0) O theta := by
    refine ⟨ho.1,fun I => ?_⟩
    change ContinuousOn (fun x => w x *
      Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient (standardBasis n) (omega x) I) O
    exact hw.continuousOn.mul (ho.2 I)
  have hrestrict : tangentRestriction 1 k M theta =
      (fun x : M => w x • tangentRestriction 1 k M omega x) := by
    funext x
    ext v
    rfl
  have hpatch (t : Fin l) : patchIntegral (P t) (fun _ => 1) theta =
      patchIntegral (P t) w omega := by
    unfold patchIntegral
    congr 1
    funext u
    change 1 * (w ((P t).map u) *
      Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient (P t) omega u) = _
    rw [one_mul]
    rfl
  have h := regular_display_integral o hM hMO P s hregular Z hlower hself hp hcover theta htheta
  rw [hrestrict] at h
  simpa only [hpatch] using h

/-- Outward-first determines the entire boundary orientation, also in degree
zero where the orientation consists of independent point signs. -/
lemma outward_orientation_unique {r : ℕ∞ω} {d n} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M)
    (s t : ManifoldOrientation r d (intrinsicBoundary r (d+1) M))
    (hs : OutwardFirst d o s) (ht : OutwardFirst d o t) : s = t := by
  cases d with
  | zero => exact outward_point_orientation_unique o s t hs ht
  | succ d =>
    obtain ⟨nu,hnu,hns,hsp⟩ := hs
    obtain ⟨mu,hmu,hms,htp⟩ := ht
    have hnm : nu = mu := by
      funext x
      exact (D04BoundaryOrientation.conormal_exists_unique o.manifold x x.property).unique
        (hns x) (hms x)
    subst mu
    obtain ⟨v,hv,hunique⟩ := D04BoundaryOrientation.boundary_orientation o nu hns
    exact (hunique s hsp).trans (hunique t htp).symm

/-- The common partition is constructed from the compact geometric union.
Uniqueness identifies its whole-boundary values with the regular display. -/
theorem regular_boundary_localization : regular_boundary_localizationType := by
  intro d n q O M bO hbO m P s hregular Z hlower hself hp hcover omega ho ι U hU hUCover
  classical
  let T := (j : Fin q) × Fin (m j)
  let e := (Fintype.equivFin T).symm
  let Q : Fin (Fintype.card T) → Patch (d+1) O := fun t => P (e t).1 (e t).2
  have he (z : T) : e (e.symm z) = z := e.apply_symm_apply z
  have hK : (⋃ t, (Q t).map '' closure (Q t).region) =
      ⋃ z : T, (P z.1 z.2).map '' closure (P z.1 z.2).region := by
    ext y
    constructor
    · intro hy
      obtain ⟨t,ht⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨e t,ht⟩
    · intro hy
      obtain ⟨z,hz⟩ := mem_iUnion.mp hy
      refine mem_iUnion.mpr ⟨e.symm z,?_⟩
      change y ∈ (P (e (e.symm z)).1 (e (e.symm z)).2).map ''
        closure (P (e (e.symm z)).1 (e (e.symm z)).2).region
      rw [he z]
      exact hz
  have hUCover' : ((⋃ j, intrinsicBoundary 1 (d+2) (M j).carrier) ∪
      ⋃ t, (Q t).map '' closure (Q t).region) ⊆ ⋃ a, U a := by
    rw [hK]; exact hUCover
  have h := common_boundary_patch_localization M Q omega ho U hU hUCover'
  rw [hK] at h
  obtain ⟨L,a,A,hA,hpatch,hvalues⟩ := h
  refine ⟨L,a,A,hA,?_,?_⟩
  · intro j t
    have hq : Q (e.symm ⟨j,t⟩) = P j t := by
      change P (e (e.symm ⟨j,t⟩)).1 (e (e.symm ⟨j,t⟩)).2 = P j t
      rw [he ⟨j,t⟩]
    have hv := hpatch (e.symm ⟨j,t⟩)
    rw [hq] at hv
    exact hv
  · intro j
    obtain ⟨o,I,J,hout,hI,hB,hJ,hsum⟩ := hvalues j
    have heO : o = bO j := outward_orientation_unique
      (M j).orientation _ _ hout (hbO j)
    rw [heO] at hB hJ
    refine ⟨I,J,hI,hB,hJ,?_,hsum⟩
    intro i
    exact D04Stokes.positive_integral_unique (bO j) _ (hJ i)
      (regular_display_weighted_integral (bO j) (boundary_compact (M j))
        (fun x hx => (M j).subset_domain hx.1) (P j) (s j) (hregular j)
        (Z j) (hlower j) (hself j) (hp j) (hcover j) omega
        (D04.LocalStokes.form_C0 O omega ho) (A.weight i) (A.smooth i).continuous)

/-- Each whole-boundary Stokes value is first identified with its geometric
regular display. Summing then cancels every internal pair by actual signed
substitution and leaves the independently prescribed outer integral. -/
theorem positive_boundary_assembly : positive_boundary_assemblyType := by
  intro d n q O M bO hbO m P s hregular Z hlower hself hp hcover a l p e Q tSign b
    deltaOut hdOut hOut houter deltaPair hdPair hPair hpair omega ho
  classical
  have hex j := D04Stokes.ambient_stokes_compact
    (M j).orientation (M j).compact O omega (M j).subset_domain ho
  choose bO' hout I hI hB using hex
  have heO j : bO' j = bO j := outward_orientation_unique
    (M j).orientation _ _ (hout j) (hbO j)
  have hB' j : HasManifoldIntegral 1 (d+1) (bO j)
      (tangentRestriction 1 (d+1) (intrinsicBoundary 1 (d+2) (M j).carrier) omega) (I j) := by
    rw [← heO j]; exact hB j
  refine ⟨I,hI,hB',?_⟩
  have hvalues j : I j = ∑ t, (s j t).val * patchIntegral (P j t) (fun _ => 1) omega :=
    D04Stokes.positive_integral_unique (bO j) _ (hB' j)
      (regular_display_integral (bO j) (boundary_compact (M j))
        (fun x hx => (M j).subset_domain hx.1) (P j) (s j) (hregular j)
        (Z j) (hlower j) (hself j) (hp j) (hcover j) omega (D04.LocalStokes.form_C0 O omega ho))
  let F : ((j : Fin q) × Fin (m j)) → ℝ := fun z =>
    a z.1 • ((s z.1 z.2).val * patchIntegral (P z.1 z.2) (fun _ => 1) omega)
  have hsum : (∑ j, a j • I j) = ∑ z, F z := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    rw [hvalues j,Finset.smul_sum]
  rw [hsum,← e.sum_comp F,Fintype.sum_sum_type]
  have hcancel : ∑ z : Fin p × Bool, F (e (Sum.inr z)) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro i _
    rw [Fintype.sum_bool]
    obtain ⟨hmap,hsgn,hmult⟩ := hpair i
    rw [add_comm]
    exact paired_patch_cancellation _ _ _ (hdPair i) (hPair i) hmap _ _ hsgn
      _ _ hmult omega (D04.LocalStokes.form_C0 O omega ho) (fun _ => 1) continuousOn_const
  rw [hcancel,add_zero]
  apply Finset.sum_congr rfl
  intro t _
  obtain ⟨hmap,hsgn,hmult⟩ := houter t
  dsimp only [F]
  rw [GeometricPatches.local_reparametrization _ _ _ (hdOut t) (hOut t) hmap omega
    (D04.LocalStokes.form_C0 O omega ho) (fun _ => 1) continuousOn_const,
    ← mul_assoc,hsgn,hmult]

end D04.ManifoldBoundaryAssembly
