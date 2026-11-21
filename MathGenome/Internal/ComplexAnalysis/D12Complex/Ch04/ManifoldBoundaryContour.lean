import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.ManifoldBoundaryContour
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.ManifoldBoundaryDensity
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FiniteManifoldBoundaryAssembly
import Mathlib.Topology.DiscreteSubset
import Mathlib.Order.Monotone.Union
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge

/-! The original-cycle dictionary for the finite manifold branch of real Green.
The final comparison is derived from geometric signed integer occurrence counts,
using the actual curve area formula and the original Jordan displays. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators Classical
namespace D12Complex.ManifoldBoundaryContour
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model

abbrev Display := @RegularBoundaryDisplay
abbrev displayPatchChain := @RegularBoundaryDisplay.patchChain

/-- Select genuine restrictions of the original path from an open cover.
No smoothness, nonzero velocity, or finite seam-preimage assertion is used
to choose the cuts. Repeated nodes and degenerate intervals are allowed. -/
theorem finite_open_cover_subdivision {ι : Type} (γ : PiecewiseC1Path)
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (hcover : γ.trace ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (node : Fin (n+1) → ℝ) (index : Fin n → ι)
      (arc : Fin n → PiecewiseC1Path),
      Monotone node ∧ node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      (∀ i, (arc i).path.a = node i.castSucc ∧ (arc i).path.b = node i.succ ∧
        EqOn (arc i) γ (Icc (node i.castSucc) (node i.succ)) ∧
        (arc i).trace ⊆ U (index i)) ∧
      ∀ f : ℂ → ℂ, ContinuousOn f γ.trace →
        γ.integral f = ∑ i, (arc i).integral f := by
  let c : ι → Set (Icc γ.path.a γ.path.b) :=
    fun i => γ.path.onInterval ⁻¹' U i
  have hc : ∀ i, IsOpen (c i) := fun i => (hU i).preimage γ.path.onInterval.continuous
  have hcov : univ ⊆ ⋃ i, c i := by
    intro t _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨t, t.property, rfl⟩)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, hfirst, hmono, ⟨n, hlast⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc γ.path.ordered hc hcov
  let node : Fin (n+1) → ℝ := fun i => (t i.val).val
  have hm : Monotone node := fun i j hij => hmono hij
  have h0 : node 0 = γ.path.a := hfirst
  have hn : node (Fin.last n) = γ.path.b := hlast n le_rfl
  choose index hindex using (fun i : Fin n => hsub i.val)
  choose arc harca harcb heq using (fun i : Fin n =>
    γ.exists_restriction (node i.castSucc) (node i.succ)
      (t i.val).property.1 (hm (Fin.castSucc_le_succ i)) (t (i.val+1)).property.2)
  have htrace : ∀ i, (arc i).trace ⊆ γ.trace := by
    intro i z hz
    obtain ⟨s, hs, rfl⟩ := hz
    have hs' : s ∈ Icc (node i.castSucc) (node i.succ) := by
      simpa only [harca, harcb] using hs
    exact ⟨s, ⟨(t i.val).property.1.trans hs'.1,
      hs'.2.trans (t (i.val+1)).property.2⟩, (heq i hs').symm⟩
  refine ⟨n, node, index, arc, hm, h0, hn, ?_, ?_⟩
  · intro i
    refine ⟨harca i, harcb i, heq i, ?_⟩
    rintro z ⟨s, hs, rfl⟩
    have hs' : s ∈ Icc (node i.castSucc) (node i.succ) := by
      simpa only [harca, harcb] using hs
    have hst : s ∈ Icc γ.path.a γ.path.b :=
      ⟨(t i.val).property.1.trans hs'.1, hs'.2.trans (t (i.val+1)).property.2⟩
    rw [heq i hs']
    exact hindex i (show (⟨s, hst⟩ : Icc γ.path.a γ.path.b) ∈
      Icc (t i.val) (t (i.val+1)) from hs')
  · intro f hf
    have hint := C1Partition.parameter_integrable γ.path γ.partition f hf
    have hi : ∀ i : Fin n, IntervalIntegrable (fun s => f (γ s) * deriv γ s)
        volume (node i.castSucc) (node i.succ) := by
      intro i
      apply hint.mono_set
      rw [uIcc_of_le (hm (Fin.castSucc_le_succ i)), uIcc_of_le γ.path.ordered]
      exact Icc_subset_Icc (t i.val).property.1 (t (i.val+1)).property.2
    calc
      γ.integral f = ∫ s in γ.path.a..γ.path.b, f (γ s) * deriv γ s :=
        C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf
      _ = ∑ i : Fin n, ∫ s in node i.castSucc..node i.succ, f (γ s) * deriv γ s := by
        simpa only [h0, hn] using (intervalIntegral_fin_partition node _ hi).2.symm
      _ = ∑ i, (arc i).integral f := by
        apply Finset.sum_congr rfl
        intro i _
        have hr := PiecewiseC1Path.integral_congr_representative (arc i) γ f
          (hf.mono (htrace i)) (by simpa only [harca, harcb] using heq i)
        simpa only [harca, harcb] using hr.symm

theorem countable_nonzero_derivative_fiber (f : ℝ → ℂ) (z : ℂ) :
    {t | f t = z ∧ deriv f t ≠ 0}.Countable := by
  let T := {t | f t = z ∧ deriv f t ≠ 0}
  have hd : IsDiscrete T := by
    apply isDiscrete_iff_nhdsNE.mpr
    intro t ht
    have h := (differentiableAt_of_deriv_ne_zero ht.2).hasDerivAt.eventually_ne
      (c := z) ht.2
    apply Filter.eventually_false_iff_eq_bot.mp
    have h' : ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 T, f s ≠ z :=
      h.filter_mono inf_le_left
    have h'' : ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 T, s ∈ T :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [h', h''] with s hs hT
    exact hs hT.1
  exact (HereditarilyLindelofSpace.isLindelof T).countable_of_isDiscrete hd

theorem ae_deriv_zero_on_countable_image (f : ℝ → ℂ) (S : Set ℂ)
    (hS : S.Countable) :
    ∀ᵐ t ∂(volume : Measure ℝ), f t ∈ S → deriv f t = 0 := by
  have hc : (⋃ z ∈ S, {t | f t = z ∧ deriv f t ≠ 0}).Countable :=
    hS.biUnion (fun z _ => countable_nonzero_derivative_fiber f z)
  filter_upwards [hc.ae_notMem (μ := (volume : Measure ℝ))] with t ht hmem
  by_contra hn
  apply ht
  exact mem_iUnion.mpr ⟨f t, mem_iUnion.mpr ⟨hmem, rfl, hn⟩⟩

theorem planar_boundary_seams_finite (Z : Seams 2) (hZ : ∀ i, Z.dim i < 1) :
    Z.carrier.Finite := by
  apply Set.finite_iUnion
  intro i
  have hi : Z.dim i = 0 := by have := hZ i; omega
  let : Subsingleton (E (Z.dim i)) := by rw [hi]; infer_instance
  exact (Set.subsingleton_of_subsingleton : (Z.parameter i).Subsingleton).finite.image _

theorem contour_integral_off_countable (γ : PiecewiseC1Path) (f : ℂ → ℂ)
    (S : Set ℂ) (hf : ContinuousOn f γ.trace) (hS : S.Countable) :
    γ.integral f = ∫ t in γ.path.a..γ.path.b,
      if γ t ∈ S then 0 else f (γ t) * deriv γ t := by
  rw [show γ.integral f = ∫ t in γ.path.a..γ.path.b, f (γ t) * deriv γ t from
    C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_deriv_zero_on_countable_image γ S hS] with t ht
  by_cases h : γ t ∈ S
  · simp [h, ht h]
  · simp [h]

theorem cycle_integral_off_boundary_seams (Γ : IntegralCycle) (f : ℂ → ℂ)
    (Z : Seams 2) (hf : ContinuousOn f Γ.trace) (hZ : ∀ i, Z.dim i < 1) :
    Γ.integral f = Γ.chain.sum (fun γ m => (m : ℂ) *
      ∫ t in γ.path.a..γ.path.b,
        if complexCoordinates (γ t) ∈ Z.carrier then 0
        else f (γ t) * deriv γ t) := by
  have hS : (complexCoordinates ⁻¹' Z.carrier).Countable :=
    ((planar_boundary_seams_finite Z hZ).preimage complexCoordinates.injective.injOn).countable
  apply Finset.sum_congr rfl
  intro γ hγ
  change (Γ.chain γ : ℂ) * _ = (Γ.chain γ : ℂ) * _
  congr 1
  apply contour_integral_off_countable γ f _ _ hS
  exact hf.mono (fun z hz => ⟨γ, hγ, hz⟩)

theorem patch_complex_coefficient {O : Set (E 2)} (C : Patch 1 O)
    (f : ℂ → ℂ) (u : E 1) :
    (coefficient C (circulationForm
      (fun x => (f (complexCoordinates.symm x)).re)
      (fun x => -(f (complexCoordinates.symm x)).im)) u : ℂ) +
    Complex.I * (coefficient C (circulationForm
      (fun x => (f (complexCoordinates.symm x)).im)
      (fun x => (f (complexCoordinates.symm x)).re)) u : ℂ) =
    f (complexCoordinates.symm (C.map u)) *
      complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0)) := by
  rw [(D04.Green.patch_line_coefficients C _ _ u).1,
    (D04.Green.patch_line_coefficients C _ _ u).1]
  let a := f (complexCoordinates.symm (C.map u))
  let v := fderiv ℝ C.map u (standardBasis 1 0)
  change ((a.re * v 0 + -a.im * v 1 : ℝ) : ℂ) +
    Complex.I * ((a.im * v 0 + a.re * v 1 : ℝ) : ℂ) = a * (⟨v 0, v 1⟩ : ℂ)
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem regular_display_has_integral {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (hM : IsCompact M) (hMO : M ⊆ O)
    (d : RegularBoundaryDisplay (O := O) o) (omega : FormField 2 1)
    (ho : IsCrForm (some 0) O omega) :
    HasPositiveIntegral o (tangentRestriction 1 1 M omega)
      (patchChainIntegral omega d.patchChain) := by
  have h := D04.ManifoldBoundaryAssembly.regular_display_integral o hM hMO
    d.patch d.sign d.regular d.seams d.lower d.self_intersection d.intersection d.cover omega ho
  have heq : patchChainIntegral omega d.patchChain =
      ∑ i, (d.sign i).val * patchIntegral (d.patch i) (fun _ => 1) omega := by
    rw [RegularBoundaryDisplay.patchChain, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [patchChainIntegral, Finsupp.liftAddHom_apply_single]
    rcases (d.sign i).property with hs | hs <;> norm_num [hs]
  rwa [heq]

theorem regular_display_independent {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (hM : IsCompact M) (hMO : M ⊆ O)
    (d e : RegularBoundaryDisplay (O := O) o) (omega : FormField 2 1)
    (ho : IsCrForm (some 0) O omega) :
    patchChainIntegral omega d.patchChain = patchChainIntegral omega e.patchChain := by
  exact D04Stokes.positive_integral_unique o _
    (regular_display_has_integral o hM hMO d omega ho)
    (regular_display_has_integral o hM hMO e omega ho)

theorem complex_circulation_regular (O : Set (E 2)) (hO : IsOpen O)
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)) :
    IsCrForm (some 1) O
      (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
        (fun x => -(q (complexCoordinates.symm x)).im)) ∧
    IsCrForm (some 1) O
      (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
        (fun x => (q (complexCoordinates.symm x)).re)) := by
  have hc : ContDiff ℝ 1 (fun x : E 2 => complexCoordinates.symm x) :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff
  have hq' : ContDiffOn ℝ 1 (fun x => q (complexCoordinates.symm x)) O :=
    hq.comp hc.contDiffOn (fun x hx => ⟨x, hx, rfl⟩)
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hq'
  have hi := Complex.imCLM.contDiff.comp_contDiffOn hq'
  exact ⟨D04.Green.circulation_regular O _ _ hO
    ((D04.crOn_iff_contDiffOn 1 O _ hO).mpr hr)
    ((D04.crOn_iff_contDiffOn 1 O _ hO).mpr hi.neg),
    D04.Green.circulation_regular O _ _ hO
    ((D04.crOn_iff_contDiffOn 1 O _ hO).mpr hi)
    ((D04.crOn_iff_contDiffOn 1 O _ hO).mpr hr)⟩

theorem regular_display_complex_independent :
    Specs.D12Complex.Ch04.ManifoldBoundaryContour.regular_display_complex_independent_type := by
  intro O M o hO hM hMO d e q hq
  have hzero {omega : FormField 2 1} (h : IsCrForm (some 1) O omega) :
      IsCrForm (some 0) O omega := by
    refine ⟨h.1, fun I => ?_⟩
    apply (D04.crOn_iff_contDiffOn 0 O _ hO).mpr
    exact ((D04.crOn_iff_contDiffOn 1 O _ hO).mp (h.2 I)).of_le (by norm_num)
  obtain ⟨hr, hi⟩ := complex_circulation_regular O hO q hq
  rw [regular_display_independent o hM hMO d e _ (hzero hr),
    regular_display_independent o hM hMO d e _ (hzero hi)]

/-- Lower the checked C1 form regularity without adding any hypothesis. -/
lemma form_continuous_of_c1 {O : Set (E 2)} (hO : IsOpen O)
    {omega : FormField 2 1} (h : IsCrForm (some 1) O omega) :
    IsCrForm (some 0) O omega := by
  refine ⟨h.1, fun I => ?_⟩
  apply (D04.crOn_iff_contDiffOn 0 O _ hO).mpr
  exact ((D04.crOn_iff_contDiffOn 1 O _ hO).mp (h.2 I)).of_le (by norm_num)

/-- A genuine integral dictionary on every supplied Jordan parameter region.
No measurability, interval-shape or injectivity premise is added to the patch.
The zero extension is integrable even for a non-Borel Jordan set. -/
theorem patch_complex_integral {O : Set (E 2)} (hO : IsOpen O)
    (C : Patch 1 O) (q : ℂ → ℂ)
    (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)) :
    Integrable (fun u => if u ∈ C.region then
      q (complexCoordinates.symm (C.map u)) *
        complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0)) else 0) ∧
    (patchIntegral C (fun _ => 1)
      (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
        (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
    Complex.I * (patchIntegral C (fun _ => 1)
      (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
        (fun x => (q (complexCoordinates.symm x)).re)) : ℂ) =
    ∫ u, if u ∈ C.region then
      q (complexCoordinates.symm (C.map u)) *
        complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0)) else 0 := by
  let R := circulationForm (fun x => (q (complexCoordinates.symm x)).re)
    (fun x => -(q (complexCoordinates.symm x)).im)
  let J := circulationForm (fun x => (q (complexCoordinates.symm x)).im)
    (fun x => (q (complexCoordinates.symm x)).re)
  obtain ⟨hr, hj⟩ := complex_circulation_regular O hO q hq
  have hir := D04.GeometricPatches.weighted_integrable C R
    (form_continuous_of_c1 hO hr) (fun _ => 1) continuousOn_const
  have hij := D04.GeometricPatches.weighted_integrable C J
    (form_continuous_of_c1 hO hj) (fun _ => 1) continuousOn_const
  obtain ⟨_, hir', her⟩ := D04.MeasureBridge.region_bridge _ hir
  obtain ⟨_, hij', hej⟩ := D04.MeasureBridge.region_bridge _ hij
  let r := Specs.D04.C06.JordanRegions.Model.zeroExtension
    (fun u : C.region => weightedCoefficient C (fun _ => 1) R u)
  let j := Specs.D04.C06.JordanRegions.Model.zeroExtension
    (fun u : C.region => weightedCoefficient C (fun _ => 1) J u)
  have he : (fun u => (r u : ℂ) + Complex.I * (j u : ℂ)) =
      (fun u => if u ∈ C.region then q (complexCoordinates.symm (C.map u)) *
        complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0)) else 0) := by
    funext u
    by_cases hu : u ∈ C.region
    · simp only [r, j, Specs.D04.C06.JordanRegions.Model.zeroExtension, hu,
        dite_eq_left, weightedCoefficient, one_mul, ite_true]
      exact patch_complex_coefficient C q u
    · simp [r, j, hu]
  have hirC : Integrable (fun u => (r u : ℂ)) := hir'.ofReal
  have hijC : Integrable (fun u => (j u : ℂ)) := hij'.ofReal
  refine ⟨he ▸ hirC.add (hijC.const_mul Complex.I), ?_⟩
  change (patchIntegral C (fun _ => 1) R : ℂ) +
    Complex.I * (patchIntegral C (fun _ => 1) J : ℂ) = _
  change patchIntegral C (fun _ => 1) R = ∫ u, r u at her
  change patchIntegral C (fun _ => 1) J = ∫ u, j u at hej
  rw [her, hej, ← integral_complex_ofReal,
    ← integral_complex_ofReal, ← integral_const_mul, ← integral_add hirC (hijC.const_mul _)]
  exact congrArg (fun F : E 1 → ℂ => ∫ u, F u) he

/-- Integral comparison with an original traversal whose values agree with
an actual interval patch. Original parameters and stationary velocities are
retained; the arbitrary total extensions need not agree at other points. -/
theorem interval_patch_contour {O : Set (E 2)} (hO : IsOpen O)
    (C : Patch 1 O) (γ : PiecewiseC1Path)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr ''
      Icc γ.path.a γ.path.b)
    (hmap : ∀ t ∈ Icc γ.path.a γ.path.b,
      complexCoordinates.symm (C.map ((OrthonormalBasis.singleton (Fin 1) ℝ).repr t)) = γ t)
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)) :
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ) := by
  let e : ℝ ≃ₗᵢ[ℝ] E 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let F : E 1 → ℂ := fun u => if u ∈ C.region then
    q (complexCoordinates.symm (C.map u)) *
      complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0)) else 0
  have he1 : e 1 = standardBasis 1 0 := by
    ext i
    fin_cases i
    simp [e, standardBasis, EuclideanSpace.basisFun_apply]
    exact OrthonormalBasis.singleton_repr 1 0
  change C.region = e '' Icc γ.path.a γ.path.b at hregion
  change ∀ t ∈ Icc γ.path.a γ.path.b, complexCoordinates.symm (C.map (e t)) = γ t at hmap
  have hdiff {t : ℝ} (ht : t ∈ Icc γ.path.a γ.path.b) :
      HasDerivAt (fun s => complexCoordinates.symm (C.map (e s)))
        (complexCoordinates.symm (fderiv ℝ C.map (e t) (standardBasis 1 0))) t := by
    have htC : e t ∈ C.domain := C.contains
      (subset_closure (hregion ▸ mem_image_of_mem e ht))
    have hC := ((C.regular.differentiableOn (by norm_num)) (e t) htC).differentiableAt
      (C.open_domain.mem_nhds htC)
    have he := e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt (x := t)
    have he' : HasDerivAt e (e 1) t := by
      simpa using (he.comp_hasDerivAt t (hasDerivAt_id t))
    exact complexCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      t (by simpa only [he1, Function.comp_def] using hC.hasFDerivAt.comp_hasDerivAt t he')
  have hderiv {t : ℝ} (ht : t ∈ Ioo γ.path.a γ.path.b) :
      deriv γ t = complexCoordinates.symm
        (fderiv ℝ C.map (e t) (standardBasis 1 0)) := by
    have heq : (γ : ℝ → ℂ) =ᶠ[𝓝 t]
        (fun s => complexCoordinates.symm (C.map (e s))) := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      exact (hmap s hs).symm
    exact heq.deriv_eq.trans (hdiff (Ioo_subset_Icc_self ht)).deriv
  have htrace : γ.trace ⊆ complexCoordinates.symm '' O := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨C.map (e t), C.mapsTo (C.contains (subset_closure ?_)), hmap t ht⟩
    rw [hregion]
    exact mem_image_of_mem e ht
  have hint := C1Partition.integral_eq_intervalIntegral γ.path γ.partition q
    (hq.continuousOn.mono htrace)
  change γ.integral q = _ at hint
  rw [hint, (patch_complex_integral hO C q hq).2]
  change (∫ t in γ.path.a..γ.path.b, q (γ t) * deriv γ t) = ∫ u, F u
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding F]
  rw [intervalIntegral.integral_of_le γ.path.ordered, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [(countable_singleton γ.path.a).ae_notMem (volume : Measure ℝ),
    (countable_singleton γ.path.b).ae_notMem (volume : Measure ℝ)] with t hta htb
  have hta : t ≠ γ.path.a := hta
  have htb : t ≠ γ.path.b := htb
  by_cases ht : t ∈ Icc γ.path.a γ.path.b
  · have ht' : t ∈ Ioo γ.path.a γ.path.b :=
      ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩
    have het : e t ∈ C.region := hregion ▸ mem_image_of_mem e ht
    simp only [indicator_of_mem ht, F, ite_eq_left het, hmap t ht, hderiv ht']
  · have het : e t ∉ C.region := by
      rw [hregion]
      simpa only [e.injective.mem_set_image] using ht
    simp only [indicator_of_notMem ht, F, ite_eq_right het]

/-- The actual inverse coordinate of an embedded chart is C1 along every
C1 original traversal in its image. Smooth ambient inverse extensions are
proved upstream, rather than added as a hypothesis on the chart or path. -/
theorem chart_inverse_contDiffOn {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    {S : Set ℝ} (f : ℝ → ℂ) (hf : ContDiffOn ℝ 1 f S)
    (hmaps : MapsTo (fun t => complexCoordinates (f t)) S (M ∩ c.ambient)) :
    ContDiffOn ℝ 1 (fun t => c.invFun (complexCoordinates (f t))) S := by
  have hg : ContDiffOn ℝ 1 (fun t => complexCoordinates (f t)) S :=
    complexCoordinates.toContinuousLinearEquiv.contDiff.comp_contDiffOn hf
  intro t ht
  have htarget := hmaps ht
  obtain ⟨V, J, hV, hxV, hJ, heq⟩ := D04.chart_inverse_extension c
    (by constructor <;> norm_num) (by norm_num) (c.invFun (complexCoordinates (f t)))
    (c.map_target htarget)
  rw [c.right_inv _ htarget] at hxV
  have hcomp := ((hJ _ hxV).contDiffAt (hV.mem_nhds hxV)).comp_contDiffWithinAt t (hg t ht)
  apply hcomp.congr_of_eventuallyEq
  · have hnear : ∀ᶠ s in 𝓝[S] t, complexCoordinates (f s) ∈ V :=
      (hg.continuousOn t ht).preimage_mem_nhdsWithin (hV.mem_nhds hxV)
    filter_upwards [hnear, self_mem_nhdsWithin] with s hs hsS
    exact (heq ⟨hmaps hsS, hs⟩).symm
  · exact (heq ⟨htarget, hxV⟩).symm

/-- Recover a genuine scalar parameter with C1 regularity on the original
finite pieces, even when their velocities vanish or they contain pauses. -/
theorem chart_parameter_piecewiseC1 {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient)) :
    ∃ (n : ℕ) (node : Fin (n+1) → ℝ), StrictMono node ∧
      node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      ∀ i : Fin n, ContDiffOn ℝ 1
        (fun t => (c.invFun (complexCoordinates (γ t))) 0)
        (Icc (node i.castSucc) (node i.succ)) := by
  refine ⟨γ.partition.count, γ.partition.node, γ.partition.strictMono,
    γ.partition.first, γ.partition.last, ?_⟩
  intro i
  have hsub : Icc (γ.partition.node i.castSucc) (γ.partition.node i.succ) ⊆
      Icc γ.path.a γ.path.b := by
    apply Icc_subset_Icc
    · rw [← γ.partition.first]
      exact γ.partition.strictMono.monotone (Fin.zero_le _)
    · rw [← γ.partition.last]
      exact γ.partition.strictMono.monotone (Fin.le_last _)
  have h := chart_inverse_contDiffOn c γ (γ.partition.smooth i) (hmaps.mono hsub Subset.rfl)
  exact (EuclideanSpace.proj 0).contDiff.comp_contDiffOn h

/-- Glue order on adjacent closed intervals. Repeated nodes and the
zero-piece case are admitted. This is an order statement, not an integral
comparison assumption. -/
theorem monotoneOn_finite_partition (f : ℝ → ℝ) :
    ∀ (n : ℕ) (node : Fin (n+1) → ℝ), Monotone node →
      (∀ i : Fin n, MonotoneOn f (Icc (node i.castSucc) (node i.succ))) →
      MonotoneOn f (Icc (node 0) (node (Fin.last n))) := by
  intro n
  induction n with
  | zero =>
      intro node _ _ x hx y hy _
      have hx' : x = node 0 := le_antisymm hx.2 hx.1
      have hy' : y = node 0 := le_antisymm hy.2 hy.1
      rw [hx', hy']
  | succ n ih =>
      intro node hm hp
      let v : Fin (n+1) → ℝ := fun i => node i.castSucc
      have hv : Monotone v := fun i j hij => hm (Fin.castSucc_le_castSucc_iff.mpr hij)
      have hpv : ∀ i : Fin n, MonotoneOn f (Icc (v i.castSucc) (v i.succ)) := by
        intro i
        simpa only [v, Fin.castSucc_succ] using hp i.castSucc
      have hfirst := ih v hv hpv
      have hlast := hp (Fin.last n)
      have hleft : node 0 ≤ node (Fin.last n).castSucc := hm (Fin.zero_le _)
      have hright : node (Fin.last n).castSucc ≤ node (Fin.last n).succ :=
        hm (Fin.castSucc_le_succ _)
      have hglue := hfirst.union_right hlast
        (show IsGreatest (Icc (v 0) (v (Fin.last n))) (v (Fin.last n)) from
          ⟨⟨hleft, le_rfl⟩, fun _ hx => hx.2⟩)
        (show IsLeast (Icc (node (Fin.last n).castSucc) (node (Fin.last n).succ))
            (node (Fin.last n).castSucc) from
          ⟨⟨le_rfl, hright⟩, fun _ hx => hx.1⟩)
      change MonotoneOn f (Icc (node 0) (node (Fin.last n).castSucc) ∪
        Icc (node (Fin.last n).castSucc) (node (Fin.last n).succ)) at hglue
      rw [Icc_union_Icc_eq_Icc hleft hright] at hglue
      exact hglue

/-- Nonnegative direction on the original smooth pieces implies order.
The proof does not assume strict positive velocity and retains all pauses. -/
theorem piecewiseC1_monotone_of_deriv_nonneg (f : ℝ → ℝ) (n : ℕ)
    (node : Fin (n+1) → ℝ) (hm : Monotone node)
    (hf : ∀ i : Fin n, ContDiffOn ℝ 1 f (Icc (node i.castSucc) (node i.succ)))
    (hn : ∀ i : Fin n, ∀ t ∈ Ioo (node i.castSucc) (node i.succ), 0 ≤ deriv f t) :
    MonotoneOn f (Icc (node 0) (node (Fin.last n))) := by
  apply monotoneOn_finite_partition f n node hm
  intro i
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hf i).continuousOn
  · exact ((hf i).differentiableOn_one).mono interior_subset
  · simpa only [interior_Icc] using hn i

/-- Local tangent direction expressed in the actual chart coordinate derives
monotone traversal of that coordinate on the original path interval. -/
theorem chart_parameter_monotone {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hnonneg : ∀ t ∈ Ioo γ.path.a γ.path.b,
      0 ≤ deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t) :
    MonotoneOn (fun s => (c.invFun (complexCoordinates (γ s))) 0)
      (Icc γ.path.a γ.path.b) := by
  obtain ⟨n, node, hs, hfirst, hlast, hf⟩ := chart_parameter_piecewiseC1 c γ hmaps
  have h := piecewiseC1_monotone_of_deriv_nonneg _ n node hs.monotone hf
    (fun i t ht => hnonneg t ⟨?_, ?_⟩)
  · simpa only [hfirst, hlast] using h
  · have hl := hs.monotone (Fin.zero_le i.castSucc)
    rw [hfirst] at hl
    exact hl.trans_lt ht.1
  · have hr := hs.monotone (Fin.le_last i.succ)
    rw [hlast] at hr
    exact ht.2.trans_le hr

/-- Compare an original local traversal with its actual chart interval patch.
The scalar reparametrization, its piecewise C1 regularity, order and surjectivity
are derived. The tangent condition permits zero velocity and constant intervals.
This is a local theorem; extracting and counting these arcs globally is separate. -/
theorem chart_interval_patch_contour {O M : Set (E 2)} (hO : IsOpen O)
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (C : Patch 1 O) (a b : ℝ) (hab : a ≤ b)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr '' Icc a b)
    (hchart : EqOn C.map c.toFun C.region)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hstart : (c.invFun (complexCoordinates (γ γ.path.a))) 0 = a)
    (hend : (c.invFun (complexCoordinates (γ γ.path.b))) 0 = b)
    (hnonneg : ∀ t ∈ Ioo γ.path.a γ.path.b,
      0 ≤ deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t)
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)) :
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ) := by
  let e : ℝ ≃ₗᵢ[ℝ] E 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let φ : ℝ → ℝ := fun t => (c.invFun (complexCoordinates (γ t))) 0
  have hc : ContinuousOn φ (Icc γ.path.a γ.path.b) := by
    exact (EuclideanSpace.proj 0).continuous.comp_continuousOn
      (c.continuous_invFun.comp
        (complexCoordinates.toContinuousLinearEquiv.continuous.comp_continuousOn
          γ.path.continuousOn) hmaps)
  have hm : MonotoneOn φ (Icc γ.path.a γ.path.b) := chart_parameter_monotone c γ hmaps hnonneg
  have hφa : φ γ.path.a = a := hstart
  have hφb : φ γ.path.b = b := hend
  have hφmaps : MapsTo φ (Icc γ.path.a γ.path.b) (Icc a b) := by
    simpa only [hφa, hφb] using hm.mapsTo_Icc
  have hφsurj : SurjOn φ (Icc γ.path.a γ.path.b) (Icc a b) := by
    intro t ht
    have heq := hc.image_Icc_of_monotoneOn γ.path.ordered hm
    rw [hφa, hφb] at heq
    exact (show t ∈ φ '' Icc γ.path.a γ.path.b from heq.symm ▸ ht)
  have heC : MapsTo e (Icc a b) C.domain := by
    intro t ht
    apply C.contains
    exact subset_closure (hregion ▸ mem_image_of_mem e ht)
  have hsmooth : ContDiffOn ℝ 1 (fun t => complexCoordinates.symm (C.map (e t)))
      (Icc a b) :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (C.regular.comp e.toContinuousLinearEquiv.contDiff.contDiffOn heC)
  let reference : ComplexPath := ⟨a, b, hab,
    fun t => complexCoordinates.symm (C.map (e t)), hsmooth.continuousOn⟩
  let η : PiecewiseC1Path := ⟨reference, ⟨C1Partition.single reference hsmooth⟩⟩
  have hmatch : ∀ t ∈ Icc γ.path.a γ.path.b, γ t = η (φ t) := by
    intro t ht
    have hu : e (φ t) ∈ C.region := hregion ▸ mem_image_of_mem e (hφmaps ht)
    have heφ : e (φ t) = c.invFun (complexCoordinates (γ t)) := by
      ext i
      fin_cases i
      exact OrthonormalBasis.singleton_repr (φ t) 0
    change γ t = complexCoordinates.symm (C.map (e (φ t)))
    rw [hchart hu, heφ, c.right_inv _ (hmaps ht), complexCoordinates.symm_apply_apply]
  have htrace : η.trace ⊆ complexCoordinates.symm '' O := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨C.map (e t), C.mapsTo (heC ht), rfl⟩
  have heq := PiecewiseC1Path.integral_monotone_parameter η γ φ q hc hm
    hφmaps hφsurj (chart_parameter_piecewiseC1 c γ hmaps) hmatch
    (hq.continuousOn.mono htrace)
  rw [heq]
  exact interval_patch_contour hO C η hregion (fun _ _ => rfl) q hq

/-- Evaluate the integer signs in an actual regular display chain. -/
lemma display_patchChain_integral {O M : Set (E 2)}
    {o : PositiveManifoldOrientation 1 1 M} (d : RegularBoundaryDisplay (O := O) o)
    (omega : FormField 2 1) :
    patchChainIntegral omega d.patchChain =
      ∑ i, (d.sign i).val * patchIntegral (d.patch i) (fun _ => 1) omega := by
  rw [RegularBoundaryDisplay.patchChain, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [patchChainIntegral, Finsupp.liftAddHom_apply_single]
  rcases (d.sign i).property with hs | hs <;> norm_num [hs]

/-- Cancellation of the supplied D04 boundary occurrences, independent of
any contour representation. Arbitrary Jordan displays, actual local signed
reparametrizations, the enumeration and all integer coefficients are retained. -/
theorem boundary_occurrence_cancellation {r l p : ℕ} {O : Set (E 2)}
    (B : Fin r → Set (E 2))
    (o : (j : Fin r) → PositiveManifoldOrientation 1 1 (B j))
    (d : (j : Fin r) → RegularBoundaryDisplay (O := O) (o j))
    (a : Fin r → ℤ)
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin r) × Fin (d j).count))
    (Q : Fin l → Patch 1 O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
    (deltaOut : Fin l → ℝ) (hdOut : ∀ t, deltaOut t = 1 ∨ deltaOut t = -1)
    (hOut : (t : Fin l) → LocalReparametrization
      ((d (e (Sum.inl t)).1).patch (e (Sum.inl t)).2).region (Q t).region (deltaOut t))
    (houter : ∀ t,
      EqOn ((d (e (Sum.inl t)).1).patch (e (Sum.inl t)).2).map
        ((Q t).map ∘ (hOut t).map)
        ((d (e (Sum.inl t)).1).patch (e (Sum.inl t)).2).region ∧
      ((d (e (Sum.inl t)).1).sign (e (Sum.inl t)).2).val * deltaOut t = (tSign t).val ∧
      b t = a (e (Sum.inl t)).1)
    (deltaPair : Fin p → ℝ) (hdPair : ∀ i, deltaPair i = 1 ∨ deltaPair i = -1)
    (hPair : (i : Fin p) → LocalReparametrization
      ((d (e (Sum.inr (i,false))).1).patch (e (Sum.inr (i,false))).2).region
      ((d (e (Sum.inr (i,true))).1).patch (e (Sum.inr (i,true))).2).region (deltaPair i))
    (hpair : ∀ i,
      EqOn ((d (e (Sum.inr (i,false))).1).patch (e (Sum.inr (i,false))).2).map
        (((d (e (Sum.inr (i,true))).1).patch (e (Sum.inr (i,true))).2).map ∘ (hPair i).map)
        ((d (e (Sum.inr (i,false))).1).patch (e (Sum.inr (i,false))).2).region ∧
      ((d (e (Sum.inr (i,false))).1).sign (e (Sum.inr (i,false))).2).val * deltaPair i =
        -((d (e (Sum.inr (i,true))).1).sign (e (Sum.inr (i,true))).2).val ∧
      a (e (Sum.inr (i,false))).1 = a (e (Sum.inr (i,true))).1)
    (omega : FormField 2 1) (ho : IsCrForm (some 0) O omega) :
    (∑ j, a j • patchChainIntegral omega (d j).patchChain) =
      ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) omega) := by
  let F : ((j : Fin r) × Fin (d j).count) → ℝ := fun z =>
    a z.1 • (((d z.1).sign z.2).val * patchIntegral ((d z.1).patch z.2) (fun _ => 1) omega)
  have hsum : (∑ j, a j • patchChainIntegral omega (d j).patchChain) = ∑ z, F z := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    rw [display_patchChain_integral, Finset.smul_sum]
  rw [hsum, ← e.sum_comp F, Fintype.sum_sum_type]
  have hcancel : ∑ z : Fin p × Bool, F (e (Sum.inr z)) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro i _
    rw [Fintype.sum_bool, add_comm]
    obtain ⟨hmap, hsgn, hmult⟩ := hpair i
    exact D04.ManifoldBoundaryAssembly.paired_patch_cancellation _ _ _
      (hdPair i) (hPair i) hmap _ _ hsgn _ _ hmult omega ho (fun _ => 1) continuousOn_const
  rw [hcancel, add_zero]
  apply Finset.sum_congr rfl
  intro t _
  obtain ⟨hmap, hsgn, hmult⟩ := houter t
  dsimp only [F]
  rw [D04.GeometricPatches.local_reparametrization _ _ _ (hdOut t) (hOut t)
    hmap omega ho (fun _ => 1) continuousOn_const, ← mul_assoc, hsgn, hmult]

/-- Substitution on one C1 piece does not require an ordered parameter map.
The continuous integrand is controlled on its entire actual image. -/
theorem continuous_substitution_piece {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ContDiffOn ℝ 1 φ (Icc a b)) {g : ℝ → ℂ}
    (hg : ContinuousOn g (φ '' Icc a b)) :
    IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume a b ∧
      (∫ t in a..b, deriv φ t • g (φ t)) = ∫ s in φ a..φ b, g s := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  have hd := hφ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hcont : ContinuousOn (fun t => derivWithin φ (Icc a b) t • g (φ t))
      (Icc a b) := hd.smul (hg.comp hφ.continuousOn (mapsTo_image _ _))
  have heq : ∀ t ∈ Ioo a b, deriv φ t = derivWithin φ (Icc a b) t := by
    intro t ht
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm
  have hi : IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume a b := by
    have hcont' : ContinuousOn (fun t => derivWithin φ (Icc a b) t • g (φ t))
        (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hcont
    apply hcont'.intervalIntegrable.congr_uIoo
    rw [uIoo_of_le hab.le]
    intro t ht
    dsimp only
    rw [heq t ht]
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ t in a..b, derivWithin φ (Icc a b) t • g (φ t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab.le
      intro t ht
      dsimp only
      rw [heq t ht]
    _ = _ := by
      apply intervalIntegral.integral_deriv_smul_comp''
      · simpa only [uIcc_of_le hab.le] using hφ.continuousOn
      · intro t ht
        have ht' : t ∈ Ioo a b := by
          simpa only [min_eq_left hab.le, max_eq_right hab.le] using ht
        rw [← heq t ht']
        exact ((hφ.differentiableOn_one t (Ioo_subset_Icc_self ht')).differentiableAt
          (Icc_mem_nhds ht'.1 ht'.2)).hasDerivAt.hasDerivWithinAt
      · simpa only [uIcc_of_le hab.le] using hd
      · simpa only [uIcc_of_le hab.le] using hg

/-- Finite piecewise C1 substitution with arbitrary backtracking and pauses.
Target nodes need not be ordered, and each original source interval is retained. -/
theorem continuous_substitution_partition (φ : ℝ → ℝ) {a b : ℝ} (_hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) (n : ℕ) (node : Fin (n+1) → ℝ)
    (hm : Monotone node) (hfirst : node 0 = a) (hlast : node (Fin.last n) = b)
    (hs : ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
    (g : ℝ → ℂ) (hg : ContinuousOn g (φ '' Icc a b)) :
    IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume a b ∧
      (∫ t in a..b, deriv φ t • g (φ t)) = ∫ s in φ a..φ b, g s := by
  have hnode : ∀ i, node i ∈ Icc a b := by
    intro i
    constructor
    · rw [← hfirst]; exact hm (Fin.zero_le _)
    · rw [← hlast]; exact hm (Fin.le_last _)
  have hpieces := fun i : Fin n => continuous_substitution_piece
    (hm (Fin.castSucc_le_succ i)) (hs i)
    (hg.mono (image_mono (Icc_subset_Icc (hnode i.castSucc).1 (hnode i.succ).2)))
  have htarget : ∀ i : Fin n,
      IntervalIntegrable g volume (φ (node i.castSucc)) (φ (node i.succ)) := by
    intro i
    apply ContinuousOn.intervalIntegrable
    exact hg.mono (hc.surjOn_uIcc (hnode i.castSucc) (hnode i.succ))
  obtain ⟨hi, _, he⟩ := Ch03.PC1MonotoneSubstitution.weighted_substitution_partition
    (fun t => deriv φ t • g (φ t)) g n node (fun i => φ (node i))
    (fun i => (hpieces i).1) htarget (fun i => (hpieces i).2)
  simpa only [hfirst, hlast] using And.intro hi he

/-- An original path factoring through one C1 scalar coordinate has the
oriented endpoint integral. No monotonicity or nonzero original speed is needed. -/
theorem local_coordinate_endpoint_integral
    (γ : PiecewiseC1Path) (U : Set ℝ) (hU : IsOpen U)
    (ψ : ℝ → ℂ) (hψ : ContDiffOn ℝ 1 ψ U)
    (φ : ℝ → ℝ) (hc : ContinuousOn φ (Icc γ.path.a γ.path.b))
    (hmaps : MapsTo φ (Icc γ.path.a γ.path.b) U)
    (n : ℕ) (node : Fin (n+1) → ℝ) (hm : Monotone node)
    (hfirst : node 0 = γ.path.a) (hlast : node (Fin.last n) = γ.path.b)
    (hs : ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
    (heq : ∀ t ∈ Icc γ.path.a γ.path.b, γ t = ψ (φ t))
    (q : ℂ → ℂ) (hq : ContinuousOn q (ψ '' U)) :
    γ.integral q = ∫ s in φ γ.path.a..φ γ.path.b, q (ψ s) * deriv ψ s := by
  let g : ℝ → ℂ := fun s => q (ψ s) * deriv ψ s
  have hgU : ContinuousOn g U :=
    (hq.comp hψ.continuousOn (mapsTo_image _ _)).mul
      (hψ.continuousOn_deriv_of_isOpen hU le_rfl)
  have hg : ContinuousOn g (φ '' Icc γ.path.a γ.path.b) :=
    hgU.mono (image_subset_iff.mpr hmaps)
  obtain ⟨hsub, hsubeq⟩ := continuous_substitution_partition φ γ.path.ordered
    hc n node hm hfirst hlast hs g hg
  have htrace : γ.trace ⊆ ψ '' U := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨φ t, hmaps ht, (heq t ht).symm⟩
  have hqγ := hq.mono htrace
  have hfull := C1Partition.parameter_integrable γ.path γ.partition q hqγ
  have hnode : ∀ i, node i ∈ Icc γ.path.a γ.path.b := by
    intro i
    constructor
    · rw [← hfirst]; exact hm (Fin.zero_le _)
    · rw [← hlast]; exact hm (Fin.le_last _)
  have hpiece : ∀ i : Fin n,
      (∫ t in node i.castSucc..node i.succ, q (γ t) * deriv γ t) =
        ∫ t in node i.castSucc..node i.succ, deriv φ t • g (φ t) := by
    intro i
    apply intervalIntegral.integral_congr_Ioo_of_le (hm (Fin.castSucc_le_succ i))
    intro t ht
    have htfull : t ∈ Ioo γ.path.a γ.path.b :=
      ⟨(hnode i.castSucc).1.trans_lt ht.1, ht.2.trans_le (hnode i.succ).2⟩
    have hφd := ((hs i).differentiableOn_one t (Ioo_subset_Icc_self ht)).differentiableAt
      (Icc_mem_nhds ht.1 ht.2)
    have hψd := (hψ.differentiableOn_one (φ t) (hmaps (Ioo_subset_Icc_self htfull))).differentiableAt
      (hU.mem_nhds (hmaps (Ioo_subset_Icc_self htfull)))
    have heq' : (γ : ℝ → ℂ) =ᶠ[𝓝 t] ψ ∘ φ := by
      filter_upwards [Icc_mem_nhds htfull.1 htfull.2] with s hs'
      exact heq s hs'
    have hd : deriv γ t = deriv φ t • deriv ψ (φ t) :=
      heq'.deriv_eq.trans (hψd.hasDerivAt.scomp t hφd.hasDerivAt).deriv
    dsimp only
    rw [hd, heq t (Ioo_subset_Icc_self htfull)]
    simp only [g, Complex.real_smul]
    ring
  have hlocal {F : ℝ → ℂ} (hF : IntervalIntegrable F volume γ.path.a γ.path.b)
      (i : Fin n) : IntervalIntegrable F volume (node i.castSucc) (node i.succ) := by
    apply hF.mono_set
    rw [uIcc_of_le (hm (Fin.castSucc_le_succ i)), uIcc_of_le γ.path.ordered]
    exact Icc_subset_Icc (hnode i.castSucc).1 (hnode i.succ).2
  have hint := C1Partition.integral_eq_intervalIntegral γ.path γ.partition q hqγ
  change γ.integral q = _ at hint
  rw [hint, ← hfirst, ← hlast]
  calc
    _ = ∑ i : Fin n, ∫ t in node i.castSucc..node i.succ, q (γ t) * deriv γ t :=
      (intervalIntegral_fin_partition node _ (hlocal hfull)).2.symm
    _ = ∑ i : Fin n, ∫ t in node i.castSucc..node i.succ, deriv φ t • g (φ t) := by
      exact Finset.sum_congr rfl (fun i _ => hpiece i)
    _ = ∫ t in node 0..node (Fin.last n), deriv φ t • g (φ t) :=
      (intervalIntegral_fin_partition node _ (hlocal hsub)).2
    _ = _ := by simpa only [hfirst, hlast] using hsubeq

/-- Interval-patch dictionary for an arbitrary piecewise C1 parameter.
The parameter may backtrack; the comparison uses its ordered endpoint values,
not a surjectivity or monotonicity certificate. -/
theorem interval_patch_parameter_contour {O : Set (E 2)} (hO : IsOpen O)
    (C : Patch 1 O) (a b : ℝ) (hab : a ≤ b)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr '' Icc a b)
    (γ : PiecewiseC1Path) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Icc γ.path.a γ.path.b))
    (hmaps : MapsTo φ (Icc γ.path.a γ.path.b) (Icc a b))
    (hstart : φ γ.path.a = a) (hend : φ γ.path.b = b)
    (n : ℕ) (node : Fin (n+1) → ℝ) (hm : Monotone node)
    (hfirst : node 0 = γ.path.a) (hlast : node (Fin.last n) = γ.path.b)
    (hs : ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
    (heq : ∀ t ∈ Icc γ.path.a γ.path.b,
      γ t = complexCoordinates.symm
        (C.map ((OrthonormalBasis.singleton (Fin 1) ℝ).repr (φ t))))
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)) :
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ) := by
  let e : ℝ ≃ₗᵢ[ℝ] E 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let U : Set ℝ := e ⁻¹' C.domain
  let ψ : ℝ → ℂ := fun s => complexCoordinates.symm (C.map (e s))
  have hU : IsOpen U := C.open_domain.preimage e.continuous
  have hψ : ContDiffOn ℝ 1 ψ U :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (C.regular.comp e.toContinuousLinearEquiv.contDiff.contDiffOn (mapsTo_preimage _ _))
  have hsub : Icc a b ⊆ U := by
    intro t ht
    exact C.contains (subset_closure (hregion ▸ mem_image_of_mem e ht))
  have hqψ : ContinuousOn q (ψ '' U) := by
    apply hq.continuousOn.mono
    rintro z ⟨t, ht, rfl⟩
    exact ⟨C.map (e t), C.mapsTo ht, rfl⟩
  have hγ := local_coordinate_endpoint_integral γ U hU ψ hψ φ hc
    (hmaps.mono Subset.rfl hsub) n node hm hfirst hlast hs heq q hqψ
  rw [hstart, hend] at hγ
  let reference : ComplexPath := ⟨a, b, hab, ψ, (hψ.mono hsub).continuousOn⟩
  let η : PiecewiseC1Path := ⟨reference, ⟨C1Partition.single reference (hψ.mono hsub)⟩⟩
  have hηtrace : η.trace ⊆ ψ '' U := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, hsub ht, rfl⟩
  have hη := C1Partition.integral_eq_intervalIntegral η.path η.partition q
    (hqψ.mono hηtrace)
  change η.integral q = ∫ s in a..b, q (ψ s) * deriv ψ s at hη
  exact hγ.trans (hη.symm.trans
    (interval_patch_contour hO C η hregion (fun _ _ => rfl) q hq))

/-- Recover the actual chart parameter and compare its integral without
requiring a direction condition. The image constraint is geometric and local;
no integral equality, regular reparametrization or velocity hypothesis is input. -/
theorem chart_interval_patch_contour_unordered {O M : Set (E 2)} (hO : IsOpen O)
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (C : Patch 1 O) (a b : ℝ) (hab : a ≤ b)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr '' Icc a b)
    (hchart : EqOn C.map c.toFun C.region)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hcoordinate : ∀ t ∈ Icc γ.path.a γ.path.b,
      (c.invFun (complexCoordinates (γ t))) 0 ∈ Icc a b)
    (hstart : (c.invFun (complexCoordinates (γ γ.path.a))) 0 = a)
    (hend : (c.invFun (complexCoordinates (γ γ.path.b))) 0 = b)
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)) :
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ) := by
  let e : ℝ ≃ₗᵢ[ℝ] E 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let φ : ℝ → ℝ := fun t => (c.invFun (complexCoordinates (γ t))) 0
  have hc : ContinuousOn φ (Icc γ.path.a γ.path.b) :=
    (EuclideanSpace.proj 0).continuous.comp_continuousOn
      (c.continuous_invFun.comp
        (complexCoordinates.toContinuousLinearEquiv.continuous.comp_continuousOn
          γ.path.continuousOn) hmaps)
  obtain ⟨n, node, hm, hfirst, hlast, hs⟩ := chart_parameter_piecewiseC1 c γ hmaps
  apply interval_patch_parameter_contour hO C a b hab hregion γ φ hc hcoordinate
    hstart hend n node hm.monotone hfirst hlast hs ?_ q hq
  intro t ht
  have heφ : e (φ t) = c.invFun (complexCoordinates (γ t)) := by
    ext i
    fin_cases i
    exact OrthonormalBasis.singleton_repr (φ t) 0
  have hu : e (φ t) ∈ C.region := hregion ▸ mem_image_of_mem e (hcoordinate t ht)
  change γ t = complexCoordinates.symm (C.map (e (φ t)))
  rw [hchart hu, heφ, c.right_inv _ (hmaps ht), complexCoordinates.symm_apply_apply]

/-- Finite actual chart localization is derived from the manifold axiom and
compactness of the original parameter interval. Each coordinate keeps the
original finite C1 pieces. This statement concerns one manifold, before the
seam and incidence analysis for an assembly of several pieces. -/
theorem manifold_chart_subdivision {M : Set (E 2)}
    (hM : Specs.D04.C14.EmbeddedManifoldCharts.Model.IsEmbeddedManifold 1 1 M)
    (γ : PiecewiseC1Path) (htrace : complexCoordinates '' γ.trace ⊆ M) :
    ∃ (n : ℕ) (node : Fin (n+1) → ℝ)
      (chart : Fin n → Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
      (arc : Fin n → PiecewiseC1Path),
      Monotone node ∧ node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      (∀ i, (arc i).path.a = node i.castSucc ∧ (arc i).path.b = node i.succ ∧
        EqOn (arc i) γ (Icc (node i.castSucc) (node i.succ)) ∧
        MapsTo (fun t => complexCoordinates (arc i t))
          (Icc (arc i).path.a (arc i).path.b) (M ∩ (chart i).ambient) ∧
        ∃ (k : ℕ) (v : Fin (k+1) → ℝ), StrictMono v ∧
          v 0 = (arc i).path.a ∧ v (Fin.last k) = (arc i).path.b ∧
          ∀ j : Fin k, ContDiffOn ℝ 1
            (fun t => ((chart i).invFun (complexCoordinates (arc i t))) 0)
            (Icc (v j.castSucc) (v j.succ))) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q γ.trace →
        γ.integral q = ∑ i, (arc i).integral q := by
  let U : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M → Set ℂ :=
    fun c => complexCoordinates ⁻¹' c.ambient
  have hopen : ∀ c, IsOpen (U c) := fun c =>
    c.ambient_open.preimage complexCoordinates.toContinuousLinearEquiv.continuous
  have hcover : γ.trace ⊆ ⋃ c, U c := by
    intro z hz
    obtain ⟨c, u, hu, he⟩ := hM.2.2 _ (htrace (mem_image_of_mem _ hz))
    apply mem_iUnion.mpr
    refine ⟨c, ?_⟩
    change complexCoordinates z ∈ c.ambient
    rw [← he]
    exact (c.map_source hu.1).2
  obtain ⟨n, node, chart, arc, hm, hfirst, hlast, harc, hint⟩ :=
    finite_open_cover_subdivision γ U hopen hcover
  refine ⟨n, node, chart, arc, hm, hfirst, hlast, ?_, hint⟩
  intro i
  obtain ⟨ha, hb, he, hc⟩ := harc i
  have hmaps : MapsTo (fun t => complexCoordinates (arc i t))
      (Icc (arc i).path.a (arc i).path.b) (M ∩ (chart i).ambient) := by
    intro t ht
    have ht' : t ∈ Icc (node i.castSucc) (node i.succ) := by
      simpa only [ha, hb] using ht
    have htg : t ∈ Icc γ.path.a γ.path.b := by
      constructor
      · rw [← hfirst]; exact (hm (Fin.zero_le _)).trans ht'.1
      · rw [← hlast]; exact ht'.2.trans (hm (Fin.le_last _))
    constructor
    · apply htrace
      refine ⟨γ t, ⟨t, htg, rfl⟩, ?_⟩
      dsimp only
      rw [he ht']
    · exact hc ⟨t, ht, rfl⟩
  exact ⟨ha, hb, he, hmaps, chart_parameter_piecewiseC1 (chart i) (arc i) hmaps⟩

/-- The actual ambient velocity is the chart differential applied to the
recovered scalar velocity, including zero velocity. The original traversal
need be differentiable only at the marked interior parameter. -/
theorem chart_coordinate_velocity {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    {t : ℝ} (ht : t ∈ Ioo γ.path.a γ.path.b)
    (hd : DifferentiableAt ℝ γ t) :
    complexCoordinates (deriv γ t) =
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
        (c.invFun (complexCoordinates (γ t)))
        (deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t • standardBasis 1 0) := by
  let F : ℝ → E 2 := fun s => complexCoordinates (γ s)
  let H : ℝ → E 1 := fun s => c.invFun (F s)
  have hx := hmaps (Ioo_subset_Icc_self ht)
  have hu := c.map_target hx
  have hF : HasDerivAt F (complexCoordinates (deriv γ t)) t :=
    complexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      t hd.hasDerivAt
  obtain ⟨V, J, hV, hxV, hJ, he⟩ := D04.chart_inverse_extension c
    (by constructor <;> norm_num) (by norm_num) (H t) hu
  rw [c.right_inv _ hx] at hxV
  have hJd := ((hJ _ hxV).contDiffAt (hV.mem_nhds hxV)).differentiableAt (by norm_num)
  have heq : H =ᶠ[𝓝 t] J ∘ F := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2,
      hF.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV)] with s hs hsV
    exact (he ⟨hmaps hs, hsV⟩).symm
  have hH := (hJd.hasFDerivAt.comp_hasDerivAt t hF).congr_of_eventuallyEq heq
  have hscalar := (EuclideanSpace.proj (0 : Fin 1)).hasFDerivAt.comp_hasDerivAt t hH
  have hv : fderiv ℝ J (F t) (complexCoordinates (deriv γ t)) =
      deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t • standardBasis 1 0 := by
    ext i
    fin_cases i
    have hdscalar := hscalar.deriv
    simpa [F, H, Function.comp_def, standardBasis, EuclideanSpace.basisFun_apply] using hdscalar.symm
  have hnear : ∀ᶠ s in 𝓝 t, H s ∈ c.source := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact c.map_target (hmaps hs)
  have hchart := (D04.EmbeddedChart.hasDifferential c
    (by constructor <;> norm_num) hu).comp_hasDerivAt t hH hnear
  have heq' : F =ᶠ[𝓝 t] c.toFun ∘ H := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact (c.right_inv _ (hmaps hs)).symm
  have hvel := (hchart.congr_of_eventuallyEq heq').unique hF
  rw [hv] at hvel
  exact hvel.symm

/-- Geometric tangent rays imply order on the actual recovered coordinate.
This uses original C1 pieces; pauses and stationary points are admitted. -/
theorem chart_parameter_monotone_of_tangent_ray {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hray : ∀ i : Fin γ.partition.count,
      ∀ t ∈ Ioo (γ.partition.node i.castSucc) (γ.partition.node i.succ),
      ∃ r : ℝ, 0 ≤ r ∧ complexCoordinates (deriv γ t) =
        r • Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
          (c.invFun (complexCoordinates (γ t))) (standardBasis 1 0)) :
    MonotoneOn (fun s => (c.invFun (complexCoordinates (γ s))) 0)
      (Icc γ.path.a γ.path.b) := by
  -- Use the very same original partition, whose smoothness is recovered directly.
  have hpieces : ∀ i : Fin γ.partition.count, ContDiffOn ℝ 1
      (fun s => (c.invFun (complexCoordinates (γ s))) 0)
      (Icc (γ.partition.node i.castSucc) (γ.partition.node i.succ)) := by
    intro i
    have h := chart_inverse_contDiffOn c γ (γ.partition.smooth i)
      (hmaps.mono (γ.partition.piece_subset i) Subset.rfl)
    exact (EuclideanSpace.proj (0 : Fin 1)).contDiff.comp_contDiffOn h
  have h := piecewiseC1_monotone_of_deriv_nonneg _ γ.partition.count
    γ.partition.node γ.partition.strictMono.monotone hpieces ?_
  · simpa only [γ.partition.first, γ.partition.last] using h
  intro i t ht
  have htfull : t ∈ Ioo γ.path.a γ.path.b := by
    constructor
    · have hh := γ.partition.strictMono.monotone (Fin.zero_le i.castSucc)
      rw [γ.partition.first] at hh
      exact hh.trans_lt ht.1
    · have hh := γ.partition.strictMono.monotone (Fin.le_last i.succ)
      rw [γ.partition.last] at hh
      exact ht.2.trans_le hh
  obtain ⟨r, hr, hvel⟩ := hray i t ht
  have he := chart_coordinate_velocity c γ hmaps htfull
    (γ.partition.differentiableAt_piece i ht)
  have hinj := D04.EmbeddedChart.differential_injective c
    (by constructor <;> norm_num) (c.map_target (hmaps (Ioo_subset_Icc_self htfull)))
  have heqv :
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
        (c.invFun (complexCoordinates (γ t)))
        (deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t • standardBasis 1 0) =
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
        (c.invFun (complexCoordinates (γ t))) (r • standardBasis 1 0) := by
    rw [← he, map_smul]
    exact hvel
  have he' := congrArg (fun v : E 1 => v 0) (hinj heqv)
  have hderiv : deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t = r := by
    simpa [standardBasis, EuclideanSpace.basisFun_apply] using he'
  exact hderiv ▸ hr

end D12Complex.ManifoldBoundaryContour


namespace D12Complex.ManifoldBoundaryContour

/-- The first moment of integer signed incidence is twice the oriented vector
sum. Opposite directions represent the same tangent line with reversed sign. -/
theorem signedIncidence_moment {α : Type} [Fintype α]
    (c : α → ℤ) (d : α → ℂ) (S : Finset ℂ)
    (hpos : ∀ i, d i ∈ S) (hneg : ∀ i, -d i ∈ S) :
    (∑ v ∈ S, (signedIncidence c d v : ℂ) * v) =
      2 * ∑ i, (c i : ℂ) * d i := by
  classical
  simp only [signedIncidence, tsum_fintype, Int.cast_sub, Int.cast_sum,
    Int.cast_ite, Int.cast_zero, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (s := S), Finset.sum_comm (s := S)]
  have hp (i : α) :
      (∑ v ∈ S, (if d i = v then (c i : ℂ) else 0) * v) = (c i : ℂ) * d i := by
    simp only [ite_mul, zero_mul, eq_comm (a := d i)]
    exact Finset.sum_ite_eq' S (d i) (fun v => (c i : ℂ) * v) |>.trans (if_pos (hpos i))
  have hn (i : α) :
      (∑ v ∈ S, (if d i = -v then (c i : ℂ) else 0) * v) = -(c i : ℂ) * d i := by
    have he (v : ℂ) : (d i = -v) ↔ v = -d i := by constructor <;> intro h <;> linear_combination h
    simp only [he, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' S (-d i), if_pos (hneg i)]
    ring
  simp_rw [hp, hn]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, 2 * ((c i : ℂ) * d i) := Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Equal actual signed occurrence counts imply equal oriented vector sums.
This is a finite algebraic incidence argument, not an integral assumption. -/
theorem signedIncidence_vector {α β : Type} [Fintype α] [Fintype β]
    (c : α → ℤ) (d : α → ℂ) (b : β → ℤ) (e : β → ℂ)
    (h : ∀ v, signedIncidence c d v = signedIncidence b e v) :
    (∑ i, (c i : ℂ) * d i) = ∑ j, (b j : ℂ) * e j := by
  classical
  let S := (Finset.univ.image d ∪ Finset.univ.image (fun i => -d i)) ∪
    (Finset.univ.image e ∪ Finset.univ.image (fun i => -e i))
  have hmem : (∀ i, d i ∈ S) ∧ (∀ i, -d i ∈ S) ∧
      (∀ j, e j ∈ S) ∧ (∀ j, -e j ∈ S) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i <;> simp [S]
  have heq : 2 * (∑ i, (c i : ℂ) * d i) = 2 * ∑ j, (b j : ℂ) * e j := by
    rw [← signedIncidence_moment c d S hmem.1 hmem.2.1,
      ← signedIncidence_moment b e S hmem.2.2.1 hmem.2.2.2]
    simp_rw [h]
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) heq

end D12Complex.ManifoldBoundaryContour

namespace D12Complex.ManifoldBoundaryContour
open ManifoldBoundaryDensity SignedCurveMultiplicity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

/-- There are finitely many nonstationary original occurrences at almost
 every geometric point. Stationary fibers themselves need not be finite. -/
theorem cycle_occurrences_finite (Γ : IntegralCycle) :
    ∀ᵐ z ∂(μH[1] : Measure ℂ), Finite (CycleOccurrence Γ z) := by
  classical
  have hf : ∀ᵐ z ∂(μH[1] : Measure ℂ), ∀ γ ∈ Γ.chain.support,
      (regularFiber γ (Ioo γ.path.a γ.path.b) z).Finite :=
    Γ.chain.support.eventually_all.mpr (fun γ _ => (path_area γ).2.1)
  filter_upwards [hf] with z hz
  letI (γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}) :
      Fintype (regularFiber γ.val (Ioo γ.val.path.a γ.val.path.b) z) :=
    (hz γ.val γ.property).fintype
  exact inferInstanceAs (Finite (Sigma _))

/-- The original seam carrier is finite in geometric space. -/
theorem assembly_seams_finite {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) : (assemblySeams A).Finite := by
  exact (Set.finite_iUnion fun j =>
    boundary_seams_finite (A.display j).seams (A.display j).lower).image _

/-- Off the supplied geometric seams, every original regular patch has at
most one occurrence. No global injectivity is imposed on a Jordan patch. -/
theorem outer_occurrences_finite {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) :
    ∀ᵐ z ∂(μH[1] : Measure ℂ), Finite (OuterOccurrence A z) := by
  classical
  letI : NullSingletonClass (μH[1] : Measure ℂ) :=
    MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ zero_lt_one
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    ((assembly_seams_finite A).countable.measure_zero (μH[1] : Measure ℂ))] with z hz
  have hf (t : Fin l) : (regularFiber
      (patchCurve ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2))
      (patchParameters ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)) z).Finite := by
    apply Set.Subsingleton.finite
    intro u hu v hv
    apply scalarCoordinates.injective
    by_contra hne
    have heq :
        ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2).map
          (scalarCoordinates u) =
        ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2).map
          (scalarCoordinates v) :=
      complexCoordinates.symm.injective (hu.2.1.trans hv.2.1.symm)
    have hs := (A.display (A.enumerate (Sum.inl t)).1).self_intersection
      (A.enumerate (Sum.inl t)).2 _ hu.1 _ hv.1 hne heq
    exact hz ⟨_, mem_iUnion.mpr ⟨_, hs⟩, hu.2.1⟩
  letI (t : Fin l) : Fintype (regularFiber
      (patchCurve ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2))
      (patchParameters ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)) z) :=
    (hf t).fintype
  exact inferInstanceAs (Finite (Sigma _))

/-- The actual occurrence vector is precisely the canonical signed density. -/
theorem cycle_occurrence_vector (Γ : IntegralCycle) (z : ℂ)
    [Finite (CycleOccurrence Γ z)] :
    (∑' i : CycleOccurrence Γ z,
      (cycleOccurrenceWeight Γ z i : ℂ) * cycleOccurrenceDirection Γ z i) =
      chainDensity Γ.chain z := by
  classical
  letI (γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}) :
      Finite (regularFiber γ.val (Ioo γ.val.path.a γ.val.path.b) z) :=
    @Finite.of_injective _ (CycleOccurrence Γ z) _
      (fun i => ⟨γ, i⟩) (by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  letI (γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}) :
      Fintype (regularFiber γ.val (Ioo γ.val.path.a γ.val.path.b) z) := Fintype.ofFinite _
  change (∑' i : (γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}) ×
    regularFiber γ.val (Ioo γ.val.path.a γ.val.path.b) z,
      (Γ.chain i.1.val : ℂ) * unitVelocity i.1.val i.2.val) = _
  rw [tsum_fintype, Fintype.sum_sigma]
  unfold chainDensity
  rw [← Finset.sum_coe_sort Γ.chain.support]
  apply Finset.sum_congr rfl
  intro γ _
  change (∑ t : regularFiber γ.val (Ioo γ.val.path.a γ.val.path.b) z,
    (Γ.chain γ.val : ℂ) * unitVelocity γ.val t.val) =
    (Γ.chain γ.val : ℂ) * ∑' t : regularFiber γ.val (Ioo γ.val.path.a γ.val.path.b) z,
      unitVelocity γ.val t.val
  rw [tsum_fintype, Finset.mul_sum]

/-- The same expansion for the original unpaired Jordan occurrences. -/
theorem outer_occurrence_vector {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) [Finite (OuterOccurrence A z)] :
    (∑' i : OuterOccurrence A z,
      (outerOccurrenceWeight A z i : ℂ) * outerOccurrenceDirection A z i) =
      geometricOuterDensity A z := by
  classical
  letI (t : Fin l) : Finite (regularFiber
      (patchCurve ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2))
      (patchParameters ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)) z) :=
    @Finite.of_injective _ (OuterOccurrence A z) _
      (fun i => ⟨t, i⟩) (by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  letI (t : Fin l) : Fintype (regularFiber
      (patchCurve ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2))
      (patchParameters ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)) z) :=
    Fintype.ofFinite _
  change (∑' i : (t : Fin l) × regularFiber
      (patchCurve ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2))
      (patchParameters ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)) z,
    (pointSignInt ((A.display (A.enumerate (Sum.inl i.1)).1).sign
      (A.enumerate (Sum.inl i.1)).2) : ℂ) *
    unitVelocity (patchCurve ((A.display (A.enumerate (Sum.inl i.1)).1).patch
      (A.enumerate (Sum.inl i.1)).2)) i.2.val) = _
  rw [tsum_fintype, Fintype.sum_sigma]
  unfold geometricOuterDensity
  apply Finset.sum_congr rfl
  intro t _
  have hc : (pointSignInt ((A.display (A.enumerate (Sum.inl t)).1).sign
      (A.enumerate (Sum.inl t)).2) : ℂ) =
      (((A.display (A.enumerate (Sum.inl t)).1).sign (A.enumerate (Sum.inl t)).2).val : ℂ) := by
    exact_mod_cast pointSignInt_cast _
  dsimp only
  rw [← Finset.mul_sum, hc]
  congr 1
  exact (tsum_fintype _).symm

/-- Derive the vector incidence from geometric signed integer multiplicity. -/
theorem full_positive_boundary_density {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ) :
    chainDensity Γ.chain =ᵐ[μH[1]] geometricOuterDensity A := by
  filter_upwards [cycle_occurrences_finite Γ, outer_occurrences_finite A, hΓ.incidence]
    with z hc ho hi
  letI := hc
  letI := ho
  letI : Fintype (CycleOccurrence Γ z) := Fintype.ofFinite _
  letI : Fintype (OuterOccurrence A z) := Fintype.ofFinite _
  rw [← cycle_occurrence_vector Γ z, ← outer_occurrence_vector A z,
    tsum_fintype, tsum_fintype]
  exact signedIncidence_vector _ _ _ _ hi

/-- The unchanged original contour integral is the signed actual D04 real
boundary integral in both coordinates. Continuity on the compact carrier
already suffices; holomorphy is unnecessary. -/
theorem full_positive_boundary_contour {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier))) :
    Γ.integral f =
      (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).re)
          (fun x => -(f (complexCoordinates.symm x)).im)) (outerPatchChain A) : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).im)
          (fun x => (f (complexCoordinates.symm x)).re)) (outerPatchChain A) : ℂ) := by
  have hc := cycle_pushforward Γ f (hf.mono hΓ.carrier)
  have ha := geometric_assembly_pushforward A f hf
  have he := (full_positive_boundary_density A Γ hΓ).mono
    (fun z hz => congrArg (fun d => f z * d) hz)
  exact hc.2.2.trans ((integral_congr_ae he).trans ha.2.2.2)

/-- In particular, the source's real C1 neighborhood hypothesis supplies the
dictionary for any supplied whole or disk-deleted planar assembly. -/
theorem full_positive_boundary_contour_c1 {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ)
    (U : Set ℂ) (f : ℂ → ℂ) (_hU : IsOpen U)
    (hKU : complexCoordinates.symm '' (⋃ j, (A.piece j).carrier) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    Γ.integral f =
      (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).re)
          (fun x => -(f (complexCoordinates.symm x)).im)) (outerPatchChain A) : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).im)
          (fun x => (f (complexCoordinates.symm x)).re)) (outerPatchChain A) : ℂ) :=
  full_positive_boundary_contour A Γ hΓ f (hf.continuousOn.mono hKU)

end D12Complex.ManifoldBoundaryContour

namespace D12Complex.ManifoldBoundaryContour
open ManifoldBoundaryDensity SignedCurveMultiplicity
open Specs.D04.C01.EuclideanInterfaces.Model

/-- The original cycle also equals the sum over the original arbitrary Jordan
displays. Together with the outer-chain formula this explicitly derives
cancellation of all supplied internal occurrences. -/
theorem full_positive_boundary_display_sum {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier))) :
    Γ.integral f = ∑ j, ∑ t, (((A.display j).sign t).val : ℂ) *
      complexPatchIntegral ((A.display j).patch t) f := by
  have hc := cycle_pushforward Γ f (hf.mono hΓ.carrier)
  have ha := geometric_assembly_pushforward A f hf
  have he := (full_positive_boundary_density A Γ hΓ).mono
    (fun z hz => congrArg (fun d => f z * d) hz)
  exact hc.2.2.trans ((integral_congr_ae he).trans ha.2.1)

/-- The weights in the geometric incidence condition are the actual signs of
positive tangent directions in the outward-first boundary orientation. This
is verified locally on each original patch interior, not postulated for an
arbitrary extension on a Jordan frontier. -/
theorem outer_occurrence_orientation {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) (i : OuterOccurrence A z)
    (hi : scalarCoordinates i.2.val ∈ interior
      ((A.display (A.enumerate (Sum.inl i.1)).1).patch (A.enumerate (Sum.inl i.1)).2).region) :
    let j := (A.enumerate (Sum.inl i.1)).1
    let t := (A.enumerate (Sum.inl i.1)).2
    ∃ (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2
        (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 1 2 (A.piece j).carrier))
      (hu : scalarCoordinates i.2.val ∈ c.source),
      ((A.display j).patch t).map (scalarCoordinates i.2.val) = c.toFun (scalarCoordinates i.2.val) ∧
      Specs.D04.C14.OrientationsAndChartSigns.Model.chartSign
        (A.boundaryOrientation j).atPoint c (scalarCoordinates i.2.val) hu = ((A.display j).sign t).val ∧
      (outerOccurrenceWeight A z i : ℂ) * outerOccurrenceDirection A z i =
        complexCoordinates.symm
          ((((A.display j).sign t).val /
            ‖Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
              (scalarCoordinates i.2.val) (standardBasis 1 0)‖) •
            Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
              (scalarCoordinates i.2.val) (standardBasis 1 0)) ∧
      0 < ((A.boundaryOrientation j).atPoint (c.toFun (scalarCoordinates i.2.val))
        (c.map_source hu).1).someVector
          (fun a => (((A.display j).sign t).val /
            ‖Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
              (scalarCoordinates i.2.val) (standardBasis 1 0)‖) •
            Specs.D04.C14.OrientationsAndChartSigns.Model.tangentChartMap c
              (scalarCoordinates i.2.val) hu (standardBasis 1 a)) := by
  have h := regular_piece_oriented_unit
    (A.boundaryOrientation (A.enumerate (Sum.inl i.1)).1)
    ((A.display (A.enumerate (Sum.inl i.1)).1).patch (A.enumerate (Sum.inl i.1)).2)
    ((A.display (A.enumerate (Sum.inl i.1)).1).sign (A.enumerate (Sum.inl i.1)).2)
    ((A.display (A.enumerate (Sum.inl i.1)).1).regular (A.enumerate (Sum.inl i.1)).2)
    i.2.val hi
  dsimp only [outerOccurrenceWeight, outerOccurrenceDirection]
  have hc : (pointSignInt ((A.display (A.enumerate (Sum.inl i.1)).1).sign
      (A.enumerate (Sum.inl i.1)).2) : ℂ) =
      (((A.display (A.enumerate (Sum.inl i.1)).1).sign (A.enumerate (Sum.inl i.1)).2).val : ℂ) := by
    exact_mod_cast pointSignInt_cast _
  rw [hc]
  exact h

namespace Definitions
abbrev signedIncidence := @D12Complex.ManifoldBoundaryContour.signedIncidence
abbrev CycleOccurrence := @D12Complex.ManifoldBoundaryContour.CycleOccurrence
abbrev cycleOccurrenceWeight := @D12Complex.ManifoldBoundaryContour.cycleOccurrenceWeight
abbrev cycleOccurrenceDirection := @D12Complex.ManifoldBoundaryContour.cycleOccurrenceDirection
abbrev OuterOccurrence := @D12Complex.ManifoldBoundaryContour.OuterOccurrence
abbrev outerOccurrenceWeight := @D12Complex.ManifoldBoundaryContour.outerOccurrenceWeight
abbrev outerOccurrenceDirection := @D12Complex.ManifoldBoundaryContour.outerOccurrenceDirection
abbrev outerTrace := @D12Complex.ManifoldBoundaryContour.outerTrace
abbrev assemblySeams := @D12Complex.ManifoldBoundaryContour.assemblySeams
abbrev FullPositiveBoundary := @D12Complex.ManifoldBoundaryContour.FullPositiveBoundary
end Definitions
end D12Complex.ManifoldBoundaryContour
