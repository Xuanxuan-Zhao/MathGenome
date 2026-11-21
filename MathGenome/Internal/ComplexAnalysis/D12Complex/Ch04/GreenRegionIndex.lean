import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.ManifoldBoundaryContour
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.CellBoundaryContour
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.GreenRegionIndex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PiecewiseC1Length
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.WindingIndex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyFormula
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.LaplaceError
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.BigOperators.Option
import MathGenome.Internal.MultivariableAnalysis.D04.C06.ConditionalOrder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set
open scoped BigOperators
namespace D12Complex.GreenRegionIndex
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

@[simp] theorem coordinates_symm (z : ℂ) :
    planeCoordinates.symm (planeCoordinates z) = z := planeCoordinates.symm_apply_apply z

@[simp] theorem coordinates_zero (z : ℂ) : planeCoordinates z 0 = z.re := rfl
@[simp] theorem coordinates_one (z : ℂ) : planeCoordinates z 1 = z.im := rfl

/-- The signs here are the directed circulation signs in Green's theorem. -/
theorem realForm_apply : Specs.D12Complex.Ch04.GreenRegionIndex.realForm_apply_type := by
  intro q z v
  constructor
  · change (q (planeCoordinates.symm (planeCoordinates z))).re * v.re +
      -(q (planeCoordinates.symm (planeCoordinates z))).im * v.im = _
    simp [Complex.mul_re, sub_eq_add_neg]
  · change (q (planeCoordinates.symm (planeCoordinates z))).im * v.re +
      (q (planeCoordinates.symm (planeCoordinates z))).re * v.im = _
    simp [Complex.mul_im, add_comm]

/-- Project a contour piecewise before comparing the proper Riemann values.
The same argument works for any real linear projection of a complex integral. -/
theorem real_line_projection {γ : ComplexPath} (P : C1Partition γ)
    (q : ℂ → ℂ) (hq : ContinuousOn q γ.trace) (L : ℂ →L[ℝ] ℝ)
    (ω : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1)
    (hω : ∀ z v : ℂ,
      ω (planeCoordinates z) (fun _ => planeCoordinates v) = L (q z * v)) :
    ∃ h : OneFormIntegrable (realData P) ω,
      oneFormIntegral (realData P) ω h = L (P.integral q) := by
  have hc (i : Fin P.count) : ContinuousOn
      (fun t => ω ((realPath γ) t) (fun _ => (realData P).velocity i t))
      (P.pieceSet i) := by
    change ContinuousOn (fun t => ω (planeCoordinates (γ t))
      (fun _ => planeCoordinates (derivWithin γ (P.pieceSet i) t))) _
    simp_rw [hω]
    apply L.continuous.comp_continuousOn
    exact (hq.comp (γ.continuousOn.mono (P.piece_subset i))
      (fun t ht => ⟨t, P.piece_subset i ht, rfl⟩)).mul
        (((P.piece_c1_iff i).mp (P.smooth i)).2)
  have hI : OneFormIntegrable (realData P) ω := by
    intro i
    change Fin P.count at i
    exact SingleVariableAnalysis.Riemann.real_continuous_integrable _ (P.piece_lt i).le
      (fun t ht => (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr
        (hc i t ht))
  refine ⟨hI, ?_⟩
  change (∑ i : Fin P.count, Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue
    (fun t => ω ((realPath γ) t) (fun _ => (realData P).velocity i t)) (hI i)) =
    L (∑ i : Fin P.count, ∫ t in P.node i.castSucc..P.node i.succ,
      q (γ t) * derivWithin γ (P.pieceSet i) t)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ t in P.node i.castSucc..P.node i.succ,
        ω ((realPath γ) t) (fun _ => (realData P).velocity i t) :=
      SingleVariableAnalysis.LaplaceError.real_continuous_integral_eq _ _ _
        (P.piece_lt i).le (hc i) (hI i)
    _ = _ := by
      rw [← L.intervalIntegral_comp_comm (P.piece_integrable q hq i)]
      apply intervalIntegral.integral_congr
      intro t _
      exact hω _ _

theorem path_real_green_dictionary :
    Specs.D12Complex.Ch04.GreenRegionIndex.path_real_green_dictionary_type := by
  intro γ q hq
  obtain ⟨hr, her⟩ := real_line_projection γ.partition q hq Complex.reCLM (realForm q)
    (fun z v => (realForm_apply q z v).1)
  obtain ⟨hi, hei⟩ := real_line_projection γ.partition q hq Complex.imCLM (imagForm q)
    (fun z v => (realForm_apply q z v).2)
  refine ⟨hr, hi, ?_⟩
  rw [her, hei]
  simpa only [PiecewiseC1Path.integral, Complex.reCLM_apply, Complex.imCLM_apply,
    mul_comm] using (Complex.re_add_im (γ.integral q)).symm

open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model

@[simp] theorem symm_standardBasis_zero :
    planeCoordinates.symm (standardBasis 2 0) = 1 := by
  apply Complex.ext
  · change (D04.standardBasis 2 0) 0 = 1
    simp only [D04.standardBasis_apply, ite_true]
  · change (D04.standardBasis 2 0) 1 = 0
    rw [D04.standardBasis_apply, ite_eq_right (by decide)]

@[simp] theorem symm_standardBasis_one :
    planeCoordinates.symm (standardBasis 2 1) = Complex.I := by
  apply Complex.ext
  · change (D04.standardBasis 2 1) 0 = 0
    rw [D04.standardBasis_apply, ite_eq_right (by decide)]
  · change (D04.standardBasis 2 1) 1 = 1
    simp only [D04.standardBasis_apply, ite_true]

theorem scalarPartialDerivative_zero (f : ℂ → ℝ) (z : ℂ) :
    scalarPartialDerivative (fun x => f (planeCoordinates.symm x))
      (planeCoordinates z) 0 = partialX f z := by
  unfold scalarPartialDerivative directionalDerivative partialX
  congr 1
  funext t
  simp only [map_add, map_smul, coordinates_symm, symm_standardBasis_zero]
  simp

theorem scalarPartialDerivative_one (f : ℂ → ℝ) (z : ℂ) :
    scalarPartialDerivative (fun x => f (planeCoordinates.symm x))
      (planeCoordinates z) 1 = partialY f z := by
  unfold scalarPartialDerivative directionalDerivative partialY
  congr 1
  funext t
  simp only [map_add, map_smul, coordinates_symm, symm_standardBasis_one]
  simp [Complex.real_smul]

theorem green_densities_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.green_densities_zero_type := by
  intro q z hq
  obtain ⟨h₁, h₂⟩ := (complexDifferentiableAt_iff_CR q z (hq.restrictScalars ℝ)).mp
    ((complexDifferentiableAt_iff q z).mpr hq)
  constructor
  · change scalarPartialDerivative (fun x => -(q (planeCoordinates.symm x)).im)
      (planeCoordinates z) 0 -
      scalarPartialDerivative (fun x => (q (planeCoordinates.symm x)).re)
        (planeCoordinates z) 1 = 0
    have hn : scalarPartialDerivative (fun x => -(q (planeCoordinates.symm x)).im)
        (planeCoordinates z) 0 =
        -scalarPartialDerivative (fun x => (q (planeCoordinates.symm x)).im)
          (planeCoordinates z) 0 := D04.Green.partial_neg (fun x => (q (planeCoordinates.symm x)).im)
      (planeCoordinates z) 0
    rw [hn, scalarPartialDerivative_zero (fun z => (q z).im) z,
      scalarPartialDerivative_one (fun z => (q z).re) z, h₂]
    ring
  · change scalarPartialDerivative (fun x => (q (planeCoordinates.symm x)).re)
      (planeCoordinates z) 0 -
      scalarPartialDerivative (fun x => (q (planeCoordinates.symm x)).im)
        (planeCoordinates z) 1 = 0
    rw [scalarPartialDerivative_zero (fun z => (q z).re) z,
      scalarPartialDerivative_one (fun z => (q z).im) z, h₁, sub_self]

theorem green_fields_regular :
    Specs.D12Complex.Ch04.GreenRegionIndex.green_fields_regular_type := by
  intro U q hU hq
  have hV : IsOpen (planeCoordinates.symm ⁻¹' U) := hU.preimage planeCoordinates.symm.continuous
  have hcomp : ContDiffOn ℝ 1 (fun x => q (planeCoordinates.symm x))
      (planeCoordinates.symm ⁻¹' U) :=
    hq.comp planeCoordinates.symm.contDiff.contDiffOn (fun _ hx => hx)
  constructor
  · apply (D04.crOn_iff_contDiffOn 1 _ _ hV).mpr
    exact Complex.reCLM.contDiff.comp_contDiffOn hcomp
  · apply (D04.crOn_iff_contDiffOn 1 _ _ hV).mpr
    exact Complex.imCLM.contDiff.comp_contDiffOn hcomp

theorem reciprocal_regular :
    Specs.D12Complex.Ch04.GreenRegionIndex.reciprocal_regular_type := by
  intro a
  constructor
  · simpa only [one_div] using!
      (contDiffOn_id.sub contDiffOn_const : ContDiffOn ℝ 1 (fun z : ℂ => z - a) ({a}ᶜ)).inv
        (fun z hz => sub_ne_zero.mpr (by simpa using hz))
  · intro z hz
    exact (differentiableAt_const (c := (1 : ℂ))).div (differentiableAt_id.sub_const a)
      (sub_ne_zero.mpr hz)

theorem two_pi_I_ne_zero : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem cycle_index_zero_iff :
    Specs.D12Complex.Ch04.GreenRegionIndex.cycle_index_zero_iff_type := by
  intro Γ a ha
  rw [Γ.index_eq_integral a ha]
  rw [mul_eq_zero]
  simp only [inv_eq_zero, two_pi_I_ne_zero, false_or]

theorem cycle_index_one_iff :
    Specs.D12Complex.Ch04.GreenRegionIndex.cycle_index_one_iff_type := by
  intro Γ a ha
  rw [Γ.index_eq_integral a ha, inv_mul_eq_iff_eq_mul₀ two_pi_I_ne_zero, mul_one]

open Specs.D04.C06.DarbouxIntegral.Model hiding E
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

/-- The prior Darboux region value on an interval agrees with the ordinary
real interval integral. Both endpoints, and a collapsed interval, are allowed. -/
theorem interval_region_integral_eq (a b : ℝ) (hab : a ≤ b) (v : E 1 → ℝ)
    (hv : ContinuousOn v (Specs.D04.C06.DarbouxIntegral.Model.carrier
      (intervalBox a b hab))) :
    RegionIntegrable (fun x : Specs.D04.C06.DarbouxIntegral.Model.carrier
      (intervalBox a b hab) => v x) ∧
    regionIntegral (fun x : Specs.D04.C06.DarbouxIntegral.Model.carrier
      (intervalBox a b hab) => v x) = ∫ t in a..b, v (scalarPoint t) := by
  have hI := D04.ExceptionalSets.integrable_continuous (by decide) _ _ hv
  obtain ⟨hR, hval⟩ := D04.ConditionalOrder.region_interval hab v hI
  refine ⟨hR, hval.trans ?_⟩
  obtain ⟨hs, hscalar⟩ := (D04.Darboux.scalar_integral v a b hab).2 hI
  refine hscalar.trans ?_
  apply SingleVariableAnalysis.LaplaceError.real_continuous_integral_eq _ _ _ hab _ hs
  apply hv.comp (show ContinuousOn scalarPoint (Icc a b) from ?_) ?_
  · exact (show Continuous scalarPoint from by
      unfold scalarPoint
      fun_prop).continuousOn
  · intro t ht i
    exact ht

/-- An actual interval patch, with its actual pullback coefficient and weight.
This is a comparison of the two integrals, not a certificate assumed in a
boundary representation. -/
theorem patch_interval_integral_eq {O : Set (E 2)} (C : Patch 1 O)
    (a b : ℝ) (hab : a ≤ b)
    (hregion : C.region = Specs.D04.C06.DarbouxIntegral.Model.carrier
      (intervalBox a b hab))
    (w : E 2 → ℝ)
    (ω : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1)
    (hc : ContinuousOn (weightedCoefficient C w ω) (closure C.region)) :
    patchIntegral C w ω = ∫ t in a..b, weightedCoefficient C w ω (scalarPoint t) := by
  unfold patchIntegral
  rw [hregion]
  apply (interval_region_integral_eq a b hab _ ?_).2
  rw [← hregion]
  exact hc.mono subset_closure

/-- Unit coordinate inclusion, with its directed derivative. -/
theorem scalarPoint_eq_smul (t : ℝ) : scalarPoint t = t • standardBasis 1 0 := by
  ext i
  fin_cases i
  change t = t * (D04.standardBasis 1 0) 0
  simp [D04.standardBasis_apply]

theorem hasDerivAt_scalarPoint (t : ℝ) :
    HasDerivAt scalarPoint (standardBasis 1 0) t := by
  have he : scalarPoint = fun t : ℝ => t • standardBasis 1 0 :=
    funext scalarPoint_eq_smul
  rw [he]
  simpa using (hasDerivAt_id t).smul_const (standardBasis 1 0)

/-- Equality of the supplied patch and path values forces equality of their
velocities on each nondegenerate closed smooth piece. Stationary points are
included; neither regular speed nor equality off the parameter region is used. -/
theorem patch_piece_velocity {O : Set (E 2)} (C : Patch 1 O)
    {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count)
    (hregion : C.region = Specs.D04.C06.DarbouxIntegral.Model.carrier
      (intervalBox (P.node i.castSucc) (P.node i.succ) (P.piece_lt i).le))
    (hmap : ∀ t ∈ P.pieceSet i, C.map (scalarPoint t) = planeCoordinates (γ t))
    {t : ℝ} (ht : t ∈ P.pieceSet i) :
    fderiv ℝ C.map (scalarPoint t) (standardBasis 1 0) =
      planeCoordinates (derivWithin γ (P.pieceSet i) t) := by
  have hu : scalarPoint t ∈ C.domain := C.contains (subset_closure (by
    rw [hregion]
    intro j
    exact ht))
  have hCd := (C.regular.differentiableOn (by decide) (scalarPoint t) hu).differentiableAt
    (C.open_domain.mem_nhds hu)
  have hD := hCd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_scalarPoint t)
  have hγd := ((P.piece_c1_iff i).mp (P.smooth i)).1 t ht
  have hγD := planeCoordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
    hγd.hasDerivWithinAt
  have he := derivWithin_congr hmap (hmap t ht)
  exact (hD.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc (P.piece_lt i) t ht)).symm.trans
    (he.trans (hγD.derivWithin (uniqueDiffOn_Icc (P.piece_lt i) t ht)))

open Specs.D04.C13.NormalizedFormsAndWedge.Model

/-- A directed patch on a canonical smooth contour piece computes exactly
the indicated real projection of that piece's complex contour integral. -/
theorem patch_piece_projection {O : Set (E 2)} (C : Patch 1 O)
    {γ : ComplexPath} (P : C1Partition γ) (i : Fin P.count)
    (hregion : C.region = Specs.D04.C06.DarbouxIntegral.Model.carrier
      (intervalBox (P.node i.castSucc) (P.node i.succ) (P.piece_lt i).le))
    (hmap : ∀ t ∈ P.pieceSet i, C.map (scalarPoint t) = planeCoordinates (γ t))
    (q : ℂ → ℂ) (hq : ContinuousOn q γ.trace) (L : ℂ →L[ℝ] ℝ)
    (ω : FormField 2 1) (hreg : IsCrForm (some 0) O ω)
    (hω : ∀ z v : ℂ, ω (planeCoordinates z) (fun _ => planeCoordinates v) =
      L (q z * v)) :
    patchIntegral C (fun _ => 1) ω =
      L (∫ t in P.node i.castSucc..P.node i.succ,
        q (γ t) * derivWithin γ (P.pieceSet i) t) := by
  rw [patch_interval_integral_eq C _ _ (P.piece_lt i).le hregion _ _
    (D04.GeometricPatches.weighted_continuous C ω hreg _ continuousOn_const)]
  rw [← L.intervalIntegral_comp_comm (P.piece_integrable q hq i)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ P.pieceSet i := by
    simpa [C1Partition.pieceSet, Set.uIcc_of_le (P.piece_lt i).le] using ht
  change 1 * ω (C.map (scalarPoint t))
    (fun j => fderiv ℝ C.map (scalarPoint t) (standardBasis 1 j)) = _
  rw [one_mul, hmap t ht']
  have he : (fun j : Fin 1 => fderiv ℝ C.map (scalarPoint t) (standardBasis 1 j)) =
      fun _ => planeCoordinates (derivWithin γ (P.pieceSet i) t) := by
    funext j
    fin_cases j
    exact patch_piece_velocity C P i hregion hmap ht'
  rw [he, hω]

theorem path_patch_projection {O : Set (E 2)} (γ : PiecewiseC1Path)
    (d : PathPatchData O γ) (q : ℂ → ℂ) (hq : ContinuousOn q γ.trace)
    (L : ℂ →L[ℝ] ℝ) (ω : FormField 2 1) (hreg : IsCrForm (some 0) O ω)
    (hω : ∀ z v : ℂ, ω (planeCoordinates z) (fun _ => planeCoordinates v) =
      L (q z * v)) :
    ∑ i, patchIntegral (d.patch i) (fun _ => 1) ω = L (γ.integral q) := by
  change _ = L (∑ i, ∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
    q (γ t) * derivWithin γ (γ.partition.pieceSet i) t)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact patch_piece_projection (d.patch i) γ.partition i (d.region i) (d.map i)
    q hq L ω hreg hω

theorem path_patch_green_dictionary :
    Specs.D12Complex.Ch04.GreenRegionIndex.path_patch_green_dictionary_type := by
  intro O γ d q hq hr hi
  rw [path_patch_projection γ d q hq Complex.reCLM (realForm q) hr
      (fun z v => (realForm_apply q z v).1),
    path_patch_projection γ d q hq Complex.imCLM (imagForm q) hi
      (fun z v => (realForm_apply q z v).2)]
  simpa only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm] using
    (Complex.re_add_im (γ.integral q)).symm

/-- Real projections commute with both the integer contour coefficients and
the finite sum of its displayed smooth patches. -/
theorem contour_patch_projection {O : Set (E 2)} (Γ : IntegralChain)
    (d : ContourPatchData O Γ) (q : ℂ → ℂ)
    (hq : ∀ j, ContinuousOn q (d.path j).trace)
    (L : ℂ →L[ℝ] ℝ) (ω : FormField 2 1) (hreg : IsCrForm (some 0) O ω)
    (hω : ∀ z v : ℂ, ω (planeCoordinates z) (fun _ => planeCoordinates v) =
      L (q z * v)) :
    patchChainIntegral ω d.patchChain = L (Γ.integral q) := by
  have hΓ : Γ.integral q = ∑ j, (d.multiplicity j : ℂ) * (d.path j).integral q := by
    conv_lhs => rw [d.chain_eq]
    unfold IntegralChain.integral
    rw [← Finsupp.sum_finsetSum_index (fun γ => by simp)
      (fun γ m n => by simp [add_mul])]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.sum_single_index]
    simp
  rw [hΓ, map_sum]
  unfold ContourPatchData.patchChain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul, map_sum]
  have hs : ∑ i, patchChainIntegral ω
      (Finsupp.single
        (⟨(d.pieces j).patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) =
      L ((d.path j).integral q) := by
    simpa [patchChainIntegral] using path_patch_projection (d.path j) (d.pieces j)
      q (hq j) L ω hreg hω
  rw [hs]
  have he : (d.multiplicity j : ℂ) * (d.path j).integral q =
      (d.multiplicity j) • (d.path j).integral q := by simp [zsmul_eq_mul]
  rw [he, map_zsmul]

theorem assembled_patch_green_dictionary :
    Specs.D12Complex.Ch04.GreenRegionIndex.assembled_patch_green_dictionary_type := by
  intro O Γ d C hC q hq hr hi
  rw [D04.GeometricPatches.geometric_equivalence_sound (realForm q) hr C d.patchChain hC,
    D04.GeometricPatches.geometric_equivalence_sound (imagForm q) hi C d.patchChain hC,
    contour_patch_projection Γ d q hq Complex.reCLM (realForm q) hr
      (fun z v => (realForm_apply q z v).1),
    contour_patch_projection Γ d q hq Complex.imCLM (imagForm q) hi
      (fun z v => (realForm_apply q z v).2)]
  simpa only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm] using
    (Complex.re_add_im (Γ.integral q)).symm

open Specs.D04.C14.OrientationsAndChartSigns.Model

@[simp] theorem orientationInteger_real (s : PointSign) :
    (orientationInteger s : ℝ) = s.val := by
  rcases s.property with h | h <;> norm_num [orientationInteger, h]

/-- Integer patch coefficients express exactly the induced orientation signs. -/
theorem outerChain_integral {O : Set (E 2)} (d : ManifoldGreenData O)
    (ω : FormField 2 1) :
    patchChainIntegral ω d.outerChain =
      ∑ t, (d.outerSign t).val * patchIntegral (d.outer t) (fun _ => 1) ω := by
  unfold ManifoldGreenData.outerChain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp [patchChainIntegral, zsmul_eq_mul]

/-- Zero density has zero value in the actual Darboux region integral. -/
theorem region_integral_zero {n : ℕ} (S : Set (E n)) :
    regionIntegral (fun _ : S => (0 : ℝ)) = 0 := by
  unfold regionIntegral
  have he : zeroExtension (fun _ : S => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp [zeroExtension]
  rw [he]
  exact (D04.Darboux.constant_integrals _ 0).1.trans (zero_mul _)

/-- Real Green, with all geometry supplied explicitly, for a curl-free field. -/
theorem manifold_circulation_zero_on {O : Set (E 2)} (d : ManifoldGreenData O)
    (f g : E 2 → ℝ) (hO : IsOpen O) (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hzero : ∀ x ∈ d.carrier, circulationDensity f g x = 0) :
    patchChainIntegral (circulationForm f g) d.outerChain = 0 := by
  have h := D04.Green.riemann_manifold_green d.piece d.ambient d.boundaryOrientation
    d.outward d.patchCount d.patch d.sign d.regular d.seams d.seamsDim d.repeats
    d.overlap d.cover d.bulkSeams d.bulkOverlap d.occurrence d.outer d.outerSign
    (fun _ => 1) d.outerDirection d.outerDirection_sign d.outerReparam
    (fun t => ⟨(d.outerMatch t).1, (d.outerMatch t).2, rfl⟩)
    d.pairDirection d.pairDirection_sign d.pairReparam d.pairMatch f g hO hf hg
  have he : (fun x : d.carrier => circulationDensity f g x) = fun _ => 0 := by
    funext x
    exact hzero x x.property
  have hv := h.2.2.2.1
  change regionIntegral (fun x : d.carrier => circulationDensity f g x) = _ at hv
  rw [he, region_integral_zero] at hv
  rw [outerChain_integral]
  simpa using hv.symm

theorem manifold_circulation_zero {O : Set (E 2)} (d : ManifoldGreenData O)
    (f g : E 2 → ℝ) (hO : IsOpen O) (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hzero : ∀ x ∈ O, circulationDensity f g x = 0) :
    patchChainIntegral (circulationForm f g) d.outerChain = 0 := by
  apply manifold_circulation_zero_on d f g hO hf hg
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact hzero x ((d.piece j).subset_domain hj)

theorem manifold_green_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.manifold_green_zero_type := by
  intro U q hU hq hhol d
  obtain ⟨hr, hi⟩ := green_fields_regular U q hU hq
  have hO : IsOpen (planeCoordinates.symm ⁻¹' U) :=
    hU.preimage planeCoordinates.symm.continuous
  have hneg : CrOn 1 (planeCoordinates.symm ⁻¹' U)
      (fun x => -(q (planeCoordinates.symm x)).im) := by
    apply (D04.crOn_iff_contDiffOn 1 _ _ hO).mpr
    exact ((D04.crOn_iff_contDiffOn 1 _ _ hO).mp hi).neg
  constructor
  · apply manifold_circulation_zero d _ _ hO hr hneg
    intro x hx
    have hz := (green_densities_zero q (planeCoordinates.symm x)
      (hhol _ hx)).1
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
  · apply manifold_circulation_zero d _ _ hO hi hr
    intro x hx
    have hz := (green_densities_zero q (planeCoordinates.symm x)
      (hhol _ hx)).2
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz

/-- C1 regularity of coefficients includes the exact C0 hypothesis used by
geometric equivalence of patch chains. -/
theorem form_c1_to_c0 {O : Set (E 2)} {ω : FormField 2 1}
    (h : IsCrForm (some 1) O ω) : IsCrForm (some 0) O ω := by
  refine ⟨h.1, fun I => ?_⟩
  exact ((D04.crOn_iff_contDiffOn 1 O _ h.1).mp (h.2 I)).continuousOn

theorem green_contour_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.green_contour_zero_type := by
  intro U K Γ d q hU hq hhol
  obtain ⟨hr, hi⟩ := green_fields_regular U q hU hq
  have hO : IsOpen (planeCoordinates.symm ⁻¹' U) :=
    hU.preimage planeCoordinates.symm.continuous
  have hn : CrOn 1 (planeCoordinates.symm ⁻¹' U)
      (fun x => -(q (planeCoordinates.symm x)).im) := by
    apply (D04.crOn_iff_contDiffOn 1 _ _ hO).mpr
    exact ((D04.crOn_iff_contDiffOn 1 _ _ hO).mp hi).neg
  have hreal : IsCrForm (some 0) (planeCoordinates.symm ⁻¹' U) (realForm q) :=
    form_c1_to_c0 (D04.Green.circulation_regular _ _ _ hO hr hn)
  have himag : IsCrForm (some 0) (planeCoordinates.symm ⁻¹' U) (imagForm q) :=
    form_c1_to_c0 (D04.Green.circulation_regular _ _ _ hO hi hr)
  have he := assembled_patch_green_dictionary _ Γ d.contour d.geometry.outerChain
    d.represents q (fun j => hq.continuousOn.mono (d.contour_in j)) hreal himag
  obtain ⟨hzr, hzi⟩ := manifold_green_zero U q hU hq hhol d.geometry
  simpa only [hzr, hzi, Complex.ofReal_zero, mul_zero, add_zero] using he

/-- A reciprocal field with no pole on the closed integration region has zero
boundary integral, by the supplied geometric data and the proved real Green
calculation. This also applies to a hole of the specified region. -/
theorem reciprocal_boundary_zero (K : Set ℂ) (Γ : IntegralChain)
    (hΓ : HasManifoldGreenBoundary K Γ) (a : ℂ) (ha : a ∉ K) :
    Γ.integral (fun z => 1 / (z - a)) = 0 := by
  have hU : IsOpen ({a}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  obtain ⟨d⟩ := hΓ {a}ᶜ hU (by
    intro z hz
    change z ≠ a
    intro he
    exact ha (he ▸ hz))
  exact green_contour_zero {a}ᶜ K Γ d _ hU (reciprocal_regular a).1
    (fun z hz => (reciprocal_regular a).2 z (by simpa using hz))

theorem specified_manifold_region_index :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_manifold_region_index_type := by
  intro D Γ hD
  constructor
  · intro a ha
    have ht : a ∉ Γ.trace := by
      intro htrace
      have hf := hD.boundary_trace htrace
      change a ∈ closure D \ interior D at hf
      rw [hD.isOpen.interior_eq] at hf
      exact hf.2 ha
    obtain ⟨r, hr, _hball, hdeleted⟩ := hD.deleted a ha
    have hno : a ∉ closure (D \ Metric.closedBall a r) := by
      have hsub : closure (D \ Metric.closedBall a r) ⊆ (Metric.ball a r)ᶜ :=
        closure_minimal (fun z hz hb => hz.2 (Metric.ball_subset_closedBall hb))
          Metric.isOpen_ball.isClosed_compl
      intro hm
      exact hsub hm (Metric.mem_ball_self hr)
    have hz := reciprocal_boundary_zero _ _ hdeleted a hno
    have he : (deletedDiskBoundary Γ a r).integral (fun z => 1 / (z - a)) =
        Γ.integral (fun z => 1 / (z - a)) -
          (DiskCauchyFormula.circlePath a r).integral (fun z => 1 / (z - a)) := by
      unfold deletedDiskBoundary IntegralChain.integral IntegralCycle.integral
      rw [Finsupp.sum_sub_index (fun γ m n => by push_cast; ring)]
      simp [Finsupp.sum_single_index, IntegralChain.integral]
    rw [he, sub_eq_zero] at hz
    apply (cycle_index_one_iff Γ a ht).mpr
    rw [hz]
    simpa only [one_div] using DiskCauchyFormula.circle_integral_sub_inv a a r hr
      (by simpa using hr)
  · intro a ha
    have ht : a ∉ Γ.trace := fun h => ha (frontier_subset_closure (hD.boundary_trace h))
    apply (cycle_index_zero_iff Γ a ht).mpr
    exact reciprocal_boundary_zero _ _ hD.whole a ha

open Specs.D04.C15.CellsChainsAndIntegrals.Model

/-- Apply the cell branch of the actual scalar Green theorem. -/
theorem cell_circulation_zero_on {O : Set (E 2)} (d : CellGreenData O)
    (f g : E 2 → ℝ) (hO : IsOpen O) (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hzero : ∀ x ∈ d.carrier, circulationDensity f g x = 0) :
    patchChainIntegral (circulationForm f g) d.outerChain = 0 := by
  have h := D04.Green.riemann_cell_green d.cell d.face d.faces d.outerChain
    d.left d.right d.multiplicity d.direction d.direction_sign d.reparam d.weights
    d.assembly d.injective d.positive d.seams d.overlap f g hO hf hg
  have he : (fun x : d.carrier => circulationDensity f g x) = fun _ => 0 := by
    funext x
    exact hzero x x.property
  have hv := h.2.2.2.1
  change regionIntegral (fun x : d.carrier => circulationDensity f g x) = _ at hv
  rw [he, region_integral_zero] at hv
  exact hv.symm

theorem cell_carrier_subset {O : Set (E 2)} (d : CellGreenData O) :
    d.carrier ⊆ O := by
  intro x hx
  obtain ⟨j, y, hy, he⟩ := Set.mem_iUnion.mp hx
  rw [← he, (extension_spec (d.cell j)).2.2.2 ⟨y, hy⟩]
  exact ((d.cell j).toFun ⟨y, hy⟩).property

theorem cell_circulation_zero {O : Set (E 2)} (d : CellGreenData O)
    (f g : E 2 → ℝ) (hO : IsOpen O) (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hzero : ∀ x ∈ O, circulationDensity f g x = 0) :
    patchChainIntegral (circulationForm f g) d.outerChain = 0 :=
  cell_circulation_zero_on d f g hO hf hg (fun x hx => hzero x (cell_carrier_subset d hx))

/-- Green uses holomorphy only on the integration carrier. The C1 field is
still defined on the ambient open neighborhood required by the prior theorem. -/
theorem finite_green_zero_on (U : Set ℂ) (q : ℂ → ℂ) (hU : IsOpen U)
    (hq : ContDiffOn ℝ 1 q U) (d : FiniteGreenData (planeCoordinates.symm ⁻¹' U))
    (hhol : ∀ x ∈ d.carrier, DifferentiableAt ℂ q (planeCoordinates.symm x)) :
    patchChainIntegral (realForm q) d.outerChain = 0 ∧
    patchChainIntegral (imagForm q) d.outerChain = 0 := by
  obtain ⟨hr, hi⟩ := green_fields_regular U q hU hq
  have hO : IsOpen (planeCoordinates.symm ⁻¹' U) :=
    hU.preimage planeCoordinates.symm.continuous
  have hn : CrOn 1 (planeCoordinates.symm ⁻¹' U)
      (fun x => -(q (planeCoordinates.symm x)).im) := by
    apply (D04.crOn_iff_contDiffOn 1 _ _ hO).mpr
    exact ((D04.crOn_iff_contDiffOn 1 _ _ hO).mp hi).neg
  have hz : ∀ x ∈ d.carrier,
      circulationDensity (fun x => (q (planeCoordinates.symm x)).re)
        (fun x => -(q (planeCoordinates.symm x)).im) x = 0 ∧
      circulationDensity (fun x => (q (planeCoordinates.symm x)).im)
        (fun x => (q (planeCoordinates.symm x)).re) x = 0 := by
    intro x hx
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      green_densities_zero q _ (hhol x hx)
  cases d with
  | manifold d => exact ⟨manifold_circulation_zero_on d _ _ hO hr hn
      (fun x hx => (hz x hx).1), manifold_circulation_zero_on d _ _ hO hi hr
      (fun x hx => (hz x hx).2)⟩
  | cells d => exact ⟨cell_circulation_zero_on d _ _ hO hr hn
      (fun x hx => (hz x hx).1), cell_circulation_zero_on d _ _ hO hi hr
      (fun x hx => (hz x hx).2)⟩

theorem finite_green_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.finite_green_zero_type := by
  intro U q hU hq hhol d
  cases d with
  | manifold d => exact manifold_green_zero U q hU hq hhol d
  | cells d =>
    obtain ⟨hr, hi⟩ := green_fields_regular U q hU hq
    have hO : IsOpen (planeCoordinates.symm ⁻¹' U) :=
      hU.preimage planeCoordinates.symm.continuous
    have hn : CrOn 1 (planeCoordinates.symm ⁻¹' U)
        (fun x => -(q (planeCoordinates.symm x)).im) := by
      apply (D04.crOn_iff_contDiffOn 1 _ _ hO).mpr
      exact ((D04.crOn_iff_contDiffOn 1 _ _ hO).mp hi).neg
    constructor
    · apply cell_circulation_zero d _ _ hO hr hn
      intro x hx
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (green_densities_zero q _ (hhol _ hx)).1
    · apply cell_circulation_zero d _ _ hO hi hr
      intro x hx
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (green_densities_zero q _ (hhol _ hx)).2

/-- The canonical chain integral viewed as an additive homomorphism. -/
def contourIntegralHom (q : ℂ → ℂ) : IntegralChain →+ ℂ :=
  Finsupp.liftAddHom (fun γ => {
    toFun := fun m : ℤ => (m : ℂ) * γ.integral q
    map_zero' := by simp
    map_add' := fun m n => by push_cast; ring })

@[simp] theorem contourIntegralHom_apply (q : ℂ → ℂ) (C : IntegralChain) :
    contourIntegralHom q C = C.integral q := rfl

@[simp] theorem chain_single_integral (q : ℂ → ℂ) (γ : PiecewiseC1Path) :
    IntegralChain.integral (Finsupp.single γ 1) q = γ.integral q := by
  simp [IntegralChain.integral]

theorem contour_equivalent_integral :
    Specs.D12Complex.Ch04.GreenRegionIndex.contour_equivalent_integral_type := by
  intro U C D h q hq
  change contourIntegralHom q C = contourIntegralHom q D
  induction h with
  | constant γ z he =>
    simpa only [map_zero, contourIntegralHom_apply, chain_single_integral] using
      γ.integral_of_constant z he q
  | refl C => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | add h₁ h₂ ih₁ ih₂ => simpa only [map_add] using congrArg₂ (· + ·) ih₁ ih₂
  | zsmul m h ih => simpa only [map_zsmul] using congrArg (m • ·) ih
  | monotone γ η φ hin hc hm hmaps hs hsm he =>
    simpa only [contourIntegralHom_apply, chain_single_integral] using
      PiecewiseC1Path.integral_monotone_parameter γ η φ q hc hm hmaps hs hsm he
        (hq.mono hin)
  | subdivision γ γ₁ γ₂ c hin hc hfirst hj₁ hj₂ hlast he₁ he₂ =>
    simpa only [map_add, contourIntegralHom_apply, chain_single_integral] using
      PiecewiseC1Path.integral_subdivision γ γ₁ γ₂ c q hc hfirst hj₁ hj₂ hlast
        he₁ he₂ (hq.mono hin)
  | reversal γ η hin hfirst hlast he =>
    simpa only [map_neg, contourIntegralHom_apply, chain_single_integral] using
      PiecewiseC1Path.integral_reversal γ η q hfirst hlast he (hq.mono hin)

open Specs.D04.C06.JordanRegions.Model

theorem finite_parameter_patch_integral_zero {O : Set (E 2)} (P : Patch 1 O)
    (hfinite : P.region.Finite) (w : E 2 → ℝ) (hw : ContinuousOn w O)
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω) :
    patchIntegral P w ω = 0 := by
  have hZ := D04.NullCovers.compact_null_contentZero P.region hfinite.isCompact
    (D04.NullCovers.countable_null (by decide : 0 < 1) hfinite.countable)
  have hzero : RegionIntegrable (fun _ : P.region => (0 : ℝ)) :=
    D04.GeometricPatches.continuous_integrable P.jordan continuousOn_const
  have he := D04.GeometricPatches.region_integral_congr_off P.jordan
    (D04.GeometricPatches.weighted_integrable P ω hω w hw) hzero hZ
    (fun x hx => False.elim (hx x.property))
  exact he.trans (region_integral_zero P.region)

private theorem finite_parameter_jordan (Z : Set (E 1)) (hZ : Z.Finite) : Jordan Z := by
  apply (D04.JordanRegions.jordan_iff_boundary (by decide) Z hZ.isCompact.isBounded).mpr
  apply D04.NullCovers.contentZero_mono
    (show frontier Z ⊆ Z from hZ.isClosed.frontier_subset)
  exact D04.NullCovers.compact_null_contentZero Z hZ.isCompact
    (D04.NullCovers.countable_null (by decide : 0 < 1) hZ.countable)

/-- The common-chart cover calculation may omit finitely many seam
parameters. Their zero contribution is proved rather than assumed as a
geometric equivalence. Empty covers and arbitrary Jordan subregions work. -/
theorem patch_integral_finite_cover_off_finite {O : Set (E 2)} (P : Patch 1 O)
    (m : ℕ) (R : Fin m → Set (E 1)) (hR : ∀ i, Jordan (R i))
    (hsub : ∀ i, R i ⊆ P.region) (Z : Set (E 1)) (hZ : Z.Finite)
    (hcover : P.region \ Z ⊆ ⋃ i, R i)
    (hpair : ∀ i j, i ≠ j → R i ∩ R j ⊆ Z)
    (w : E 2 → ℝ) (hw : ContinuousOn w O)
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω) :
    patchIntegral P w ω =
      ∑ i, patchIntegral (restrictPatch P (R i) (hR i) (hsub i)) w ω := by
  classical
  let T : Option (Fin m) → Set (E 1)
    | none => P.region ∩ Z
    | some i => R i
  have hT (i) : Jordan (T i) := by
    cases i with
    | none => exact finite_parameter_jordan _ (hZ.subset inter_subset_right)
    | some i => exact hR i
  have hTsub (i) : T i ⊆ P.region := by
    cases i with
    | none => exact inter_subset_left
    | some i => exact hsub i
  have hTcover : P.region = ⋃ i, T i := by
    apply Subset.antisymm
    · intro u hu
      by_cases hz : u ∈ Z
      · exact mem_iUnion.mpr ⟨none, hu, hz⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hu, hz⟩)
        exact mem_iUnion.mpr ⟨some i, hi⟩
    · exact iUnion_subset hTsub
  have hTpair (i j : Option (Fin m)) (hij : i ≠ j) : T i ∩ T j ⊆ Z := by
    cases i with
    | none => exact fun _ hu => hu.1.2
    | some i =>
      cases j with
      | none => exact fun _ hu => hu.2.2
      | some j => exact hpair i j (fun he => hij (congrArg some he))
  have hZc := D04.NullCovers.compact_null_contentZero Z hZ.isCompact
    (D04.NullCovers.countable_null (by decide : 0 < 1) hZ.countable)
  have he := D04.GeometricPatches.region_integral_finite_cover P.jordan
    (weightedCoefficient P w ω) (D04.GeometricPatches.weighted_continuous P ω hω w hw)
    T hT hTsub hTcover hZc hTpair
  have he' : patchIntegral P w ω =
      ∑ i, patchIntegral (restrictPatch P (T i) (hT i) (hTsub i)) w ω := he
  rw [univ_option, Finset.sum_insertNone] at he'
  have hz : patchIntegral (restrictPatch P (T none) (hT none) (hTsub none)) w ω = 0 :=
    finite_parameter_patch_integral_zero _ (hZ.subset inter_subset_right) w hw ω hω
  simpa only [hz, zero_add] using he'


/-- Evaluate a signed geometric display with precisely its induced signs. -/
theorem regular_boundary_display_chain_integral {O M : Set (E 2)}
    {o : PositiveManifoldOrientation 1 1 M}
    (d : RegularBoundaryDisplay (O := O) o) (ω : FormField 2 1) :
    patchChainIntegral ω d.patchChain =
      ∑ i, (d.sign i).val * patchIntegral (d.patch i) (fun _ => 1) ω := by
  unfold RegularBoundaryDisplay.patchChain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [patchChainIntegral, zsmul_eq_mul]

/-- Independence of arbitrary Jordan displays follows from the actual D04
whole-manifold integral and its proved uniqueness. Reference-chart transport,
seam deletion, and orientation signs are proved by that upstream theorem. -/
theorem regular_boundary_display_independent {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (hM : IsCompact M) (hMO : M ⊆ O)
    (d e : RegularBoundaryDisplay (O := O) o)
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω) :
    patchChainIntegral ω d.patchChain = patchChainIntegral ω e.patchChain := by
  rw [regular_boundary_display_chain_integral, regular_boundary_display_chain_integral]
  exact D04Stokes.positive_integral_unique o _
    (D04.ManifoldBoundaryAssembly.regular_display_integral o hM hMO d.patch d.sign
      d.regular d.seams d.seamsDim d.repeats d.overlap d.cover ω hω)
    (D04.ManifoldBoundaryAssembly.regular_display_integral o hM hMO e.patch e.sign
      e.regular e.seams e.seamsDim e.repeats e.overlap e.cover ω hω)

/-- Finite seam deletion is proved using the actual Darboux patch integral. -/
theorem patch_equivalent_off_finite_integral {O : Set (E 2)}
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω)
    (C D : PatchChain 1 O) (h : PatchEquivalentOffFinite C D) :
    patchChainIntegral ω C = patchChainIntegral ω D := by
  induction h with
  | geometric h => exact D04.GeometricPatches.geometric_equivalence_sound ω hω _ _ h
  | display o hM hMO d e => exact regular_boundary_display_independent o hM hMO d e ω hω
  | cover p m R hR hsub Z hZ hcover hpair =>
      simpa [patchChainIntegral, restrictWeighted] using
        patch_integral_finite_cover_off_finite p.patch m R hR hsub Z hZ
          hcover hpair p.weight p.continuous ω hω
  | refl C => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | add h₁ h₂ ih₁ ih₂ => simpa only [map_add, ih₁, ih₂]
  | zsmul a h ih => simpa only [map_zsmul, ih]

/-- The contour dictionary now also permits finite parameter seams. -/
theorem assembled_patch_green_dictionary_off_finite
    (O : Set (E 2)) (Γ : IntegralChain) (d : ContourPatchData O Γ)
    (C : PatchChain 1 O) (hC : PatchEquivalentOffFinite C d.patchChain)
    (q : ℂ → ℂ) (hq : ∀ j, ContinuousOn q (d.path j).trace)
    (hr : IsCrForm (some 0) O (realForm q))
    (hi : IsCrForm (some 0) O (imagForm q)) :
    Γ.integral q = (patchChainIntegral (realForm q) C : ℂ) +
      Complex.I * (patchChainIntegral (imagForm q) C : ℂ) := by
  rw [patch_equivalent_off_finite_integral (realForm q) hr C d.patchChain hC,
    patch_equivalent_off_finite_integral (imagForm q) hi C d.patchChain hC,
    contour_patch_projection Γ d q hq Complex.reCLM (realForm q) hr
      (fun z v => (realForm_apply q z v).1),
    contour_patch_projection Γ d q hq Complex.imCLM (imagForm q) hi
      (fun z v => (realForm_apply q z v).2)]
  simpa only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm] using
    (Complex.re_add_im (Γ.integral q)).symm

theorem finite_green_contour_zero_on (U K : Set ℂ) (Γ : IntegralChain)
    (d : FiniteBoundaryRepresentation U K Γ) (q : ℂ → ℂ) (hU : IsOpen U)
    (hq : ContDiffOn ℝ 1 q U) (hhol : ∀ z ∈ K, DifferentiableAt ℂ q z) :
    Γ.integral q = 0 := by
  rw [contour_equivalent_integral U Γ d.representedChain d.traversal q hq.continuousOn]
  obtain ⟨hr, hi⟩ := green_fields_regular U q hU hq
  have hO : IsOpen (planeCoordinates.symm ⁻¹' U) :=
    hU.preimage planeCoordinates.symm.continuous
  have hn : CrOn 1 (planeCoordinates.symm ⁻¹' U)
      (fun x => -(q (planeCoordinates.symm x)).im) := by
    apply (D04.crOn_iff_contDiffOn 1 _ _ hO).mpr
    exact ((D04.crOn_iff_contDiffOn 1 _ _ hO).mp hi).neg
  have hreal := form_c1_to_c0 (D04.Green.circulation_regular _ _ _ hO hr hn)
  have himag := form_c1_to_c0 (D04.Green.circulation_regular _ _ _ hO hi hr)
  have he := assembled_patch_green_dictionary_off_finite _ d.representedChain d.contour
    d.geometry.outerChain d.represents q
    (fun j => hq.continuousOn.mono (d.contour_in j)) hreal himag
  obtain ⟨hzr, hzi⟩ := finite_green_zero_on U q hU hq d.geometry (by
    intro x hx
    rw [d.carrier_eq] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simpa only [coordinates_symm] using hhol z hz)
  simpa only [hzr, hzi, Complex.ofReal_zero, mul_zero, add_zero] using he

theorem finite_green_contour_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.finite_green_contour_zero_type := by
  intro U K Γ d q hU hq hhol
  rw [contour_equivalent_integral U Γ d.representedChain d.traversal q hq.continuousOn]
  obtain ⟨hr, hi⟩ := green_fields_regular U q hU hq
  have hO : IsOpen (planeCoordinates.symm ⁻¹' U) :=
    hU.preimage planeCoordinates.symm.continuous
  have hn : CrOn 1 (planeCoordinates.symm ⁻¹' U)
      (fun x => -(q (planeCoordinates.symm x)).im) := by
    apply (D04.crOn_iff_contDiffOn 1 _ _ hO).mpr
    exact ((D04.crOn_iff_contDiffOn 1 _ _ hO).mp hi).neg
  have hreal := form_c1_to_c0 (D04.Green.circulation_regular _ _ _ hO hr hn)
  have himag := form_c1_to_c0 (D04.Green.circulation_regular _ _ _ hO hi hr)
  have he := assembled_patch_green_dictionary_off_finite _ d.representedChain d.contour
    d.geometry.outerChain d.represents q
    (fun j => hq.continuousOn.mono (d.contour_in j)) hreal himag
  obtain ⟨hzr, hzi⟩ := finite_green_zero U q hU hq hhol d.geometry
  simpa only [hzr, hzi, Complex.ofReal_zero, mul_zero, add_zero] using he

theorem reciprocal_finite_boundary_zero (K : Set ℂ) (Γ : IntegralChain)
    (hΓ : HasFiniteGreenBoundary K Γ) (a : ℂ) (ha : a ∉ K) :
    Γ.integral (fun z => 1 / (z - a)) = 0 := by
  have hU : IsOpen ({a}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  obtain ⟨d⟩ := hΓ {a}ᶜ hU (by
    intro z hz
    change z ≠ a
    intro he
    exact ha (he ▸ hz))
  exact finite_green_contour_zero {a}ᶜ K Γ d _ hU (reciprocal_regular a).1
    (fun z hz => (reciprocal_regular a).2 z (by simpa using hz))

theorem specified_finite_region_index :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_finite_region_index_type := by
  intro D Γ hD
  constructor
  · intro a ha
    have ht : a ∉ Γ.trace := by
      intro htrace
      have hf := hD.boundary_trace htrace
      change a ∈ closure D \ interior D at hf
      rw [hD.isOpen.interior_eq] at hf
      exact hf.2 ha
    obtain ⟨r, hr, _hball, hdeleted⟩ := hD.deleted a ha
    have hno : a ∉ closure (D \ Metric.closedBall a r) := by
      have hsub : closure (D \ Metric.closedBall a r) ⊆ (Metric.ball a r)ᶜ :=
        closure_minimal (fun z hz hb => hz.2 (Metric.ball_subset_closedBall hb))
          Metric.isOpen_ball.isClosed_compl
      intro hm
      exact hsub hm (Metric.mem_ball_self hr)
    have hz := reciprocal_finite_boundary_zero _ _ hdeleted a hno
    have he : (deletedDiskBoundary Γ a r).integral (fun z => 1 / (z - a)) =
        Γ.integral (fun z => 1 / (z - a)) -
          (DiskCauchyFormula.circlePath a r).integral (fun z => 1 / (z - a)) := by
      change contourIntegralHom _ (_ - _) = _
      rw [map_sub]
      simp only [contourIntegralHom_apply, chain_single_integral]
      rfl
    rw [he, sub_eq_zero] at hz
    apply (cycle_index_one_iff Γ a ht).mpr
    rw [hz]
    simpa only [one_div] using DiskCauchyFormula.circle_integral_sub_inv a a r hr
      (by simpa using hr)
  · intro a ha
    have ht : a ∉ Γ.trace := fun h => ha (frontier_subset_closure (hD.boundary_trace h))
    apply (cycle_index_zero_iff Γ a ht).mpr
    exact reciprocal_finite_boundary_zero _ _ hD.whole a ha

open scoped Topology
open Filter

/-- Remove the pole smoothly in a ball disjoint from a closed set. The result
agrees with the original reciprocal on a neighborhood of every point of that
set. This permits use of a single supplied ambient Green decomposition. -/
theorem reciprocal_smooth_extension (K : Set ℂ) (hK : IsClosed K)
    (a : ℂ) (ha : a ∉ K) :
    ∃ q : ℂ → ℂ, ContDiff ℝ 1 q ∧
      ∀ z ∈ K, q =ᶠ[𝓝 z] (fun w => 1 / (w - a)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl a ha
  let b : ContDiffBump a := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let q : ℂ → ℂ := fun z => (1 - (b z : ℂ)) * (1 / (z - a))
  refine ⟨q, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro z
    by_cases hz : z = a
    · subst z
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [b.eventuallyEq_one] with z hz
      simp [q, hz]
    · have hb : ContDiffAt ℝ 1 (fun z => (b z : ℂ)) z :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp z b.contDiffAt
      have hrec : ContDiffAt ℝ 1 (fun z : ℂ => 1 / (z - a)) z := by
        simpa only [one_div] using!
          (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hz)
      exact (contDiffAt_const.sub hb).mul hrec
  · intro z hz
    have hd : r ≤ dist z a := by
      by_contra! hn
      exact hball hn hz
    have hout : z ∈ (Metric.closedBall a (r / 2))ᶜ := by
      change ¬ dist z a ≤ r / 2
      linarith
    filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hout] with w hw
    have hb : b w = 0 := b.zero_of_le_dist (by
      change ¬ dist w a ≤ r / 2 at hw
      exact (not_le.mp hw).le)
    simp [q, hb]

/-- Equality on the active trace determines the coordinate contour integral. -/
theorem chain_integral_congr_on (Γ : IntegralChain) (q p : ℂ → ℂ)
    (he : EqOn q p Γ.trace) : Γ.integral q = Γ.integral p := by
  unfold IntegralChain.integral Finsupp.sum
  apply Finset.sum_congr rfl
  intro γ hγ
  apply congrArg (fun z : ℂ => (Γ γ : ℂ) * z)
  change (∑ i, ∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
      q (γ t) * derivWithin γ (γ.partition.pieceSet i) t) =
    ∑ i, ∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
      p (γ t) * derivWithin γ (γ.partition.pieceSet i) t
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [he (show γ t ∈ Γ.trace from ⟨γ, hγ, ⟨t,
    γ.partition.piece_subset i (by
      simpa [C1Partition.pieceSet, uIcc_of_le (γ.partition.piece_lt i).le] using ht), rfl⟩⟩)]

/-- No new geometric restriction to a smaller ambient domain is needed.
Closedness separates the pole from the carrier; compactness of the active
contour separates it from the trace, including a disk-deleted contour. -/
theorem reciprocal_fixed_boundary_zero (U K : Set ℂ) (Γ : IntegralChain)
    (d : FiniteBoundaryRepresentation U K Γ) (hU : IsOpen U) (hK : IsClosed K)
    (a : ℂ) (ha : a ∉ K) (htrace : a ∉ Γ.trace) :
    Γ.integral (fun z => 1 / (z - a)) = 0 := by
  have hclosed := hK.union (PiecewiseC1Length.chain_trace_compact Γ).isClosed
  obtain ⟨q, hq, he⟩ := reciprocal_smooth_extension (K ∪ Γ.trace) hclosed a
    (by simpa only [mem_union, not_or] using And.intro ha htrace)
  have hhol : ∀ z ∈ K, DifferentiableAt ℂ q z := by
    intro z hz
    have hza : z ≠ a := fun e => ha (e ▸ hz)
    exact ((reciprocal_regular a).2 z hza).congr_of_eventuallyEq
      (he z (Or.inl hz))
  have hz := finite_green_contour_zero_on U K Γ d q hU hq.contDiffOn hhol
  rw [← chain_integral_congr_on Γ q (fun z => 1 / (z - a))
    (fun z hz => (he z (Or.inr hz)).self_of_nhds)]
  exact hz

/-- Extend C1 data on a nondegenerate closed interval, including the one-sided
endpoint derivatives. Integrating the clamped derivative avoids any speed
assumption and avoids gluing mismatched endpoint jets. -/
theorem exists_c1_interval_extension (a b : ℝ) (hab : a < b) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    ∃ F : ℝ → ℂ, ContDiff ℝ 1 F ∧ EqOn F f (Icc a b) := by
  let d := derivWithin f (Icc a b)
  have hd : ContinuousOn d (Icc a b) :=
    ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mp hf).2
  let g : ℝ → ℂ := IccExtend hab.le (fun t : Icc a b => d t)
  have hg : Continuous g := hd.domRestrict.Icc_extend'
  have he : EqOn g d (Icc a b) := fun _ ht => IccExtend_of_mem hab.le _ ht
  let F : ℝ → ℂ := fun t => f a + ∫ s in a..t, g s
  have hF (t : ℝ) : HasDerivAt F (g t) t := by
    exact (hg.integral_hasStrictDerivAt a t).hasDerivAt.const_add (f a)
  have hder : deriv F = g := funext (fun t => (hF t).deriv)
  refine ⟨F, contDiff_one_iff_deriv.mpr ⟨fun t => (hF t).differentiableAt, ?_⟩, ?_⟩
  · rw [hder]
    exact hg
  · intro t ht
    have hInt : (∫ s in a..t, g s) = f t - f a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
        (hf.continuousOn.mono (Icc_subset_Icc_right ht.2))
      · intro s hs
        have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.le.trans ht.2⟩
        rw [he hs']
        exact ((hf.differentiableOn (by decide) s hs').hasDerivWithinAt).hasDerivAt
          (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
      · exact hg.intervalIntegrable a t
    change f a + _ = _
    rw [hInt, add_sub_cancel]

/-- Every canonical C1 partition has actual prior interval patches in any
open neighborhood of its trace. This includes arbitrary stationary pieces. -/
theorem path_patch_exists (U : Set ℂ) (γ : PiecewiseC1Path)
    (hU : IsOpen U) (hin : γ.trace ⊆ U) :
    Nonempty (PathPatchData (planeCoordinates.symm ⁻¹' U) γ) := by
  classical
  have hF (i : Fin γ.partition.count) :
      ∃ F : ℝ → ℂ, ContDiff ℝ 1 F ∧ EqOn F γ (γ.partition.pieceSet i) :=
    exists_c1_interval_extension _ _ (γ.partition.piece_lt i) γ (γ.partition.smooth i)
  choose F hFc hFe using hF
  have heval : ContDiff ℝ 1 (fun x : E 1 => x 0) :=
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).comp
      ((coordinates 1).toContinuousLinearEquiv.contDiff)
  let m : Fin γ.partition.count → E 1 → E 2 :=
    fun i x => planeCoordinates (F i (x 0))
  have hmc (i) : ContDiff ℝ 1 (m i) :=
    planeCoordinates.contDiff.comp ((hFc i).comp heval)
  let S (i : Fin γ.partition.count) := Specs.D04.C06.DarbouxIntegral.Model.carrier
    (intervalBox (γ.partition.node i.castSucc) (γ.partition.node i.succ)
      (γ.partition.piece_lt i).le)
  have hS (i) : IsClosed (S i) := (D04.DiscontinuityCriterion.carrier_compact _).isClosed
  let p (i : Fin γ.partition.count) : Patch 1 (planeCoordinates.symm ⁻¹' U) := {
    region := S i
    jordan := D04.ImproperExhaustions.jordan_box _
    map := m i
    domain := (fun x => planeCoordinates.symm (m i x)) ⁻¹' U
    open_domain := hU.preimage (planeCoordinates.symm.continuous.comp (hmc i).continuous)
    contains := by
      rw [(hS i).closure_eq]
      intro x hx
      change planeCoordinates.symm (planeCoordinates (F i (x 0))) ∈ U
      rw [coordinates_symm, hFe i (show x 0 ∈ γ.partition.pieceSet i from hx 0)]
      exact hin ⟨x 0, γ.partition.piece_subset i (hx 0), rfl⟩
    regular := (hmc i).contDiffOn
    mapsTo := fun _ hx => hx }
  refine ⟨⟨p, fun _ => rfl, ?_⟩⟩
  intro i t ht
  change planeCoordinates (F i t) = planeCoordinates (γ t)
  rw [hFe i ht]

/-- Removing a path which misses a point cannot introduce that point into
the active trace. This respects cancellations of integer coefficients. -/
theorem sub_single_trace_avoids (C : IntegralChain) (γ : PiecewiseC1Path)
    (a : ℂ) (hC : a ∉ C.trace) (hγ : a ∉ γ.trace) :
    a ∉ IntegralChain.trace (C - Finsupp.single γ 1) := by
  intro ha
  obtain ⟨η, hη, haη⟩ := (IntegralChain.mem_trace_iff _ _).mp ha
  by_cases he : γ = η
  · exact hγ (he ▸ haη)
  · apply hC
    apply (IntegralChain.mem_trace_iff _ _).mpr
    refine ⟨η, ?_, haη⟩
    simpa [Finsupp.single_apply, he, Ne.symm he] using hη

/-- The full interior and exterior calculation from one supplied finite Green
assembly, using either positive cells or ambient-oriented manifold pieces. -/
theorem specified_fixed_region_index :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_fixed_region_index_type := by
  intro D Γ hD
  constructor
  · intro a ha
    have ht : a ∉ Γ.trace := by
      intro htrace
      have hf := hD.boundary_trace htrace
      change a ∈ closure D \ interior D at hf
      rw [hD.isOpen.interior_eq] at hf
      exact hf.2 ha
    obtain ⟨r, hr, _hball, U, hU, ⟨d⟩⟩ := hD.deleted a ha
    have hno : a ∉ closure (D \ Metric.closedBall a r) := by
      have hsub : closure (D \ Metric.closedBall a r) ⊆ (Metric.ball a r)ᶜ :=
        closure_minimal (fun z hz hb => hz.2 (Metric.ball_subset_closedBall hb))
          Metric.isOpen_ball.isClosed_compl
      intro hm
      exact hsub hm (Metric.mem_ball_self hr)
    have hcircle : a ∉ (DiskCauchyFormula.circlePath a r).trace := by
      rw [DiskCauchyFormula.circlePath_trace a r hr.le]
      simp only [Metric.mem_sphere, dist_self]
      exact hr.ne
    have htrace : a ∉ (deletedDiskBoundary Γ a r).trace :=
      sub_single_trace_avoids Γ.chain (DiskCauchyFormula.circlePath a r) a ht hcircle
    have hz := reciprocal_fixed_boundary_zero U _ _ d hU isClosed_closure a hno htrace
    have he : (deletedDiskBoundary Γ a r).integral (fun z => 1 / (z - a)) =
        Γ.integral (fun z => 1 / (z - a)) -
          (DiskCauchyFormula.circlePath a r).integral (fun z => 1 / (z - a)) := by
      change contourIntegralHom _ (_ - _) = _
      rw [map_sub]
      simp only [contourIntegralHom_apply, chain_single_integral]
      rfl
    rw [he, sub_eq_zero] at hz
    apply (cycle_index_one_iff Γ a ht).mpr
    rw [hz]
    simpa only [one_div] using DiskCauchyFormula.circle_integral_sub_inv a a r hr
      (by simpa using hr)
  · intro a ha
    have ht : a ∉ Γ.trace := fun h => ha (frontier_subset_closure (hD.boundary_trace h))
    apply (cycle_index_zero_iff Γ a ht).mpr
    obtain ⟨U, hU, ⟨d⟩⟩ := hD.whole
    exact reciprocal_fixed_boundary_zero U _ _ d hU isClosed_closure a ha ht

/-- A regular complex curve has a smooth scalar coordinate on a neighborhood
of each of its parameter values. No regularity of another traversal is assumed. -/
theorem regular_curve_local_coordinate (g : ℝ → ℂ) (s : ℝ)
    (hg : ContDiffAt ℝ 1 g s) (hv : deriv g s ≠ 0) :
    ∃ ψ : ℂ → ℝ, ContDiffAt ℝ 1 ψ (g s) ∧
      ∀ᶠ t in nhds s, ψ (g t) = t := by
  have hcoord (L : ℂ →L[ℝ] ℝ) (hL : L (deriv g s) ≠ 0) :
      ∃ ψ : ℂ → ℝ, ContDiffAt ℝ 1 ψ (g s) ∧
        ∀ᶠ t in nhds s, ψ (g t) = t := by
    let f : ℝ → ℝ := fun t => L (g t)
    have hf : ContDiffAt ℝ 1 f s := L.contDiff.contDiffAt.comp s hg
    have hd : HasDerivAt f (L (deriv g s)) s :=
      L.hasFDerivAt.comp_hasDerivAt s (hg.differentiableAt (by decide)).hasDerivAt
    let A : ℝ ≃L[ℝ] ℝ :=
      (LinearEquiv.smulOfNeZero ℝ ℝ (L (deriv g s)) hL).toContinuousLinearEquiv
    have hA : HasFDerivAt f (A : ℝ →L[ℝ] ℝ) s := by
      convert hd.hasFDerivAt using 1
      ext
      simp [A, mul_comm]
    let ψ : ℂ → ℝ := fun z => hf.localInverse hA (by decide) (L z)
    refine ⟨ψ, (hf.to_localInverse hA (by decide)).comp (g s) L.contDiff.contDiffAt, ?_⟩
    exact (hf.hasStrictFDerivAt' hA (by decide)).eventually_left_inverse
  by_cases hre : (deriv g s).re = 0
  · apply hcoord Complex.imCLM
    intro him
    apply hv
    exact Complex.ext hre him
  · exact hcoord Complex.reCLM hre

/-- Smoothness of a parameter is recovered from the traversed curve using
its regular local coordinate. The parameter is allowed to be stationary. -/
theorem recover_parameter_contDiffOn (f g : ℝ → ℂ) (φ : ℝ → ℝ) (S : Set ℝ)
    (hf : ContDiffOn ℝ 1 f S) (hφ : ContinuousOn φ S)
    (hg : ∀ t ∈ S, ContDiffAt ℝ 1 g (φ t))
    (hv : ∀ t ∈ S, deriv g (φ t) ≠ 0)
    (he : EqOn f (fun t => g (φ t)) S) : ContDiffOn ℝ 1 φ S := by
  intro t ht
  obtain ⟨ψ, hψ, hleft⟩ := regular_curve_local_coordinate g (φ t) (hg t ht) (hv t ht)
  have heq : ψ ∘ f =ᶠ[nhdsWithin t S] φ := by
    filter_upwards [(hφ t ht).tendsto.eventually hleft, self_mem_nhdsWithin] with x hx hxs
    change ψ (f x) = φ x
    rw [he hxs]
    exact hx
  have hc : ContDiffWithinAt ℝ 1 (ψ ∘ f) S t := by
    apply ContDiffAt.comp_contDiffWithinAt t _ (hf t ht)
    rwa [he ht]
  exact hc.congr_of_eventuallyEq_of_mem heq.symm ht

/-- A continuous directed parameter change into a regular boundary arc is
already piecewise C1 because the original traversal is piecewise C1.
In particular no strict-speed condition is placed on the original traversal. -/
theorem regular_monotone_contour_equivalent (U : Set ℂ)
    (γ η : PiecewiseC1Path) (φ : ℝ → ℝ) (g : ℝ → ℂ)
    (hin : γ.trace ⊆ U)
    (hc : ContinuousOn φ (Icc η.path.a η.path.b))
    (hm : MonotoneOn φ (Icc η.path.a η.path.b))
    (hmap : MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
    (hsurj : SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
    (hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (hγ : EqOn γ g (Icc γ.path.a γ.path.b))
    (he : EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b)) :
    ContourEquivalentOn U (Finsupp.single η 1) (Finsupp.single γ 1) := by
  refine ContourEquivalentOn.monotone γ η φ hin hc hm hmap hsurj ?_ he
  refine ⟨η.partition.count, η.partition.node, η.partition.strictMono,
    η.partition.first, η.partition.last, ?_⟩
  intro i
  apply recover_parameter_contDiffOn η g φ (η.partition.pieceSet i)
    (η.partition.smooth i) (hc.mono (η.partition.piece_subset i))
  · intro t ht
    exact hg _ (hmap (η.partition.piece_subset i ht))
  · intro t ht
    exact hv _ (hmap (η.partition.piece_subset i ht))
  · intro t ht
    exact (he (η.partition.piece_subset i ht)).trans
      (hγ (hmap (η.partition.piece_subset i ht)))

/-- Equal arc images together with the directed order of visits determine a
continuous nondecreasing onto parameter map. Trace equality alone is not used
as an orientation condition. Flat parts of the new traversal are permitted. -/
theorem ordered_arc_parameter_exists (γ η : PiecewiseC1Path)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace)
    (horder : ∀ x ∈ Icc η.path.a η.path.b, ∀ y ∈ Icc η.path.a η.path.b,
      x ≤ y → ∀ s ∈ Icc γ.path.a γ.path.b, ∀ t ∈ Icc γ.path.a γ.path.b,
        γ s = η x → γ t = η y → s ≤ t) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MonotoneOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b) := by
  classical
  let φ : ℝ → ℝ := fun t => Function.invFunOn γ (Icc γ.path.a γ.path.b) (η t)
  have hex (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) :
      ∃ s ∈ Icc γ.path.a γ.path.b, γ s = η t := by
    have hm : η t ∈ η.trace := ⟨t, ht, rfl⟩
    rw [htrace] at hm
    exact hm
  have hmaps : MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) :=
    fun t ht => Function.invFunOn_mem (hex t ht)
  have he (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) : γ (φ t) = η t :=
    Function.invFunOn_eq (hex t ht)
  have hc : ContinuousOn φ (Icc η.path.a η.path.b) := by
    let F : Icc η.path.a η.path.b → Icc γ.path.a γ.path.b :=
      fun t => ⟨φ t, hmaps t.property⟩
    have hEmb := γ.path.continuousOn.domRestrict.isClosedEmbedding hinj.injective
    have hFc : Continuous F := hEmb.isEmbedding.continuous_iff.mpr (by
      convert η.path.continuousOn.domRestrict using 1
      funext t
      exact he t t.property)
    exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hFc)
  refine ⟨φ, hc, ?_, hmaps, ?_, fun t ht => (he t ht).symm⟩
  · intro x hx y hy hxy
    exact horder x hx y hy hxy _ (hmaps hx) _ (hmaps hy) (he x hx) (he y hy)
  · intro s hs
    have hm : γ s ∈ η.trace := htrace.symm ▸ (show γ s ∈ γ.trace from ⟨s, hs, rfl⟩)
    obtain ⟨t, ht, heq⟩ := hm
    refine ⟨t, ht, ?_⟩
    exact hinj (hmaps ht) hs ((he t ht).trans heq)

/-- The geometrically ordered traversal of a regular arc yields the precise
comparison required by Green, without supplied parameter maps or integral
identities. This includes stationary velocities of the new traversal. -/
theorem ordered_regular_arc_contour_equivalent (U : Set ℂ)
    (γ η : PiecewiseC1Path) (g : ℝ → ℂ) (hin : γ.trace ⊆ U)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace)
    (horder : ∀ x ∈ Icc η.path.a η.path.b, ∀ y ∈ Icc η.path.a η.path.b,
      x ≤ y → ∀ s ∈ Icc γ.path.a γ.path.b, ∀ t ∈ Icc γ.path.a γ.path.b,
        γ s = η x → γ t = η y → s ≤ t)
    (hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (hγ : EqOn γ g (Icc γ.path.a γ.path.b)) :
    ContourEquivalentOn U (Finsupp.single η 1) (Finsupp.single γ 1) := by
  obtain ⟨φ, hc, hm, hmap, hsurj, he⟩ :=
    ordered_arc_parameter_exists γ η hinj htrace horder
  exact regular_monotone_contour_equivalent U γ η φ g hin hc hm hmap hsurj hg hv hγ he

/-- Every finite canonical contour has an enumeration by its active paths and
actual interval patches. No boundary-matching data is assumed here. -/
theorem contour_patch_exists (U : Set ℂ) (Γ : IntegralChain)
    (hU : IsOpen U) (hin : Γ.trace ⊆ U) :
    ∃ d : ContourPatchData (planeCoordinates.symm ⁻¹' U) Γ,
      ∀ j, (d.path j).trace ⊆ U := by
  classical
  let n := Fintype.card Γ.support
  let e : Fin n ≃ Γ.support := (Fintype.equivFin Γ.support).symm
  let path : Fin n → PiecewiseC1Path := fun j => (e j).val
  have hpath (j : Fin n) : (path j).trace ⊆ U := by
    intro z hz
    exact hin ⟨path j, (e j).property, hz⟩
  let pieces := fun j => Classical.choice (path_patch_exists U (path j) hU (hpath j))
  let d : ContourPatchData (planeCoordinates.symm ⁻¹' U) Γ := {
    count := n
    path := path
    multiplicity := fun j => Γ (path j)
    chain_eq := by
      conv_lhs => rw [← Γ.sum_single]
      change (∑ γ ∈ Γ.support, Finsupp.single γ (Γ γ)) = _
      rw [← Finset.sum_attach]
      simpa only [Finset.attach_eq_univ, path] using
        (e.sum_comp (fun γ : Γ.support => Finsupp.single γ.val (Γ γ.val))).symm
    pieces := pieces }
  exact ⟨d, hpath⟩

/-- Choosing a different C1 extension for a canonical contour piece changes
only the representative, hence gives the prior geometric equivalence. -/
theorem path_patch_representatives {O : Set (E 2)} (γ : PiecewiseC1Path)
    (d e : PathPatchData O γ) :
    GeometricEquivalent
      (∑ i, Finsupp.single
        (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
      (∑ i, Finsupp.single
        (⟨e.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
  classical
  have hi (i : Fin γ.partition.count) :
      GeometricEquivalent
        (Finsupp.single (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
        (Finsupp.single (⟨e.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
    apply GeometricEquivalent.representative
    · exact (d.region i).trans (e.region i).symm
    · intro x hx
      have ht : x 0 ∈ γ.partition.pieceSet i := by
        rw [d.region i] at hx
        exact hx 0
      have heq : scalarPoint (x 0) = x := by
        ext j
        fin_cases j
        rfl
      rw [← heq, d.map i _ ht, e.map i _ ht]
    · intro x hx
      rfl
  have hs (s : Finset (Fin γ.partition.count)) :
      GeometricEquivalent
        (∑ i ∈ s, Finsupp.single
          (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
        (∑ i ∈ s, Finsupp.single
          (⟨e.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact .refl 0
    | @insert i s hnot ih =>
      simpa only [Finset.sum_insert hnot] using (hi i).add ih
  exact hs Finset.univ

/-- A finite geometric subdivision of the original interval gives the
comparison with its actual restricted traversals. Zero-length cells are allowed. -/
theorem finite_subdivision_contour_equivalent (U : Set ℂ)
    (γ : PiecewiseC1Path) (n : ℕ) (node : Fin (n + 1) → ℝ)
    (hmono : Monotone node) (hfirst : node 0 = γ.path.a)
    (hlast : node (Fin.last n) = γ.path.b)
    (parts : Fin n → PiecewiseC1Path)
    (hleft : ∀ i, (parts i).path.a = node i.castSucc)
    (hright : ∀ i, (parts i).path.b = node i.succ)
    (he : ∀ i, EqOn (parts i) γ (Icc (parts i).path.a (parts i).path.b))
    (hin : γ.trace ⊆ U) :
    ContourEquivalentOn U (Finsupp.single γ 1)
      (∑ i, Finsupp.single (parts i) 1) := by
  classical
  induction n generalizing γ with
  | zero =>
    have hab : γ.path.a = γ.path.b := hfirst.symm.trans hlast
    simpa only [Fin.sum_univ_zero] using
      (ContourEquivalentOn.constant γ (γ γ.path.a) (by
        intro t ht
        have ht' : t = γ.path.a := le_antisymm (hab ▸ ht.2) ht.1
        rw [ht']))
  | succ n ih =>
    let c := node (Fin.last n).castSucc
    have hac : γ.path.a ≤ c := by
      rw [← hfirst]
      exact hmono (Fin.zero_le _)
    have hcb : c ≤ γ.path.b := by
      rw [← hlast]
      exact hmono (Fin.le_last _)
    obtain ⟨δ, hδa, hδb, hδmap⟩ :=
      PiecewiseC1Path.exists_restriction γ γ.path.a c le_rfl hac hcb
    have hδin : δ.trace ⊆ U := by
      rintro z ⟨t, ht, rfl⟩
      have htc : t ∈ Icc γ.path.a c := by simpa only [hδa, hδb] using ht
      rw [hδmap htc]
      exact hin ⟨t, ⟨htc.1, htc.2.trans hcb⟩, rfl⟩
    have hprefix : ContourEquivalentOn U (Finsupp.single δ 1)
        (∑ i : Fin n, Finsupp.single (parts i.castSucc) 1) := by
      apply ih δ (fun i => node i.castSucc)
        (fun i j hij => hmono (by simpa using hij))
      · exact hfirst.trans hδa.symm
      · exact hδb.symm
      · intro i
        exact hleft i.castSucc
      · intro i
        exact hright i.castSucc
      · intro i t ht
        have htc : t ∈ Icc γ.path.a c := by
          rw [hleft, hright] at ht
          constructor
          · calc
              γ.path.a = node 0 := hfirst.symm
              _ ≤ node i.castSucc.castSucc := hmono (Fin.zero_le _)
              _ ≤ t := ht.1
          · exact ht.2.trans (hmono (by simp))
        exact (he i.castSucc ht).trans (hδmap htc).symm
      · exact hδin
    have hsplit : ContourEquivalentOn U (Finsupp.single γ 1)
        (Finsupp.single δ 1 + Finsupp.single (parts (Fin.last n)) 1) := by
      apply ContourEquivalentOn.subdivision γ δ (parts (Fin.last n)) c hin ⟨hac,hcb⟩
        hδa hδb
      · exact hleft (Fin.last n)
      · exact (hright (Fin.last n)).trans hlast
      · simpa only [hδa, hδb] using hδmap
      · exact he (Fin.last n)
    have hfinal := hsplit.trans (hprefix.add (.refl (Finsupp.single (parts (Fin.last n)) 1)))
    simpa only [Fin.sum_univ_castSucc] using hfinal

/-- Arbitrary monotone finite nodes admit actual PC1 restrictions and the
proved subdivision comparison, including a degenerate original interval. -/
theorem finite_subdivision_exists (U : Set ℂ) (γ : PiecewiseC1Path)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (hmono : Monotone node)
    (hfirst : node 0 = γ.path.a) (hlast : node (Fin.last n) = γ.path.b)
    (hin : γ.trace ⊆ U) :
    ∃ parts : Fin n → PiecewiseC1Path,
      (∀ i, (parts i).path.a = node i.castSucc) ∧
      (∀ i, (parts i).path.b = node i.succ) ∧
      (∀ i, EqOn (parts i) γ (Icc (parts i).path.a (parts i).path.b)) ∧
      ContourEquivalentOn U (Finsupp.single γ 1) (∑ i, Finsupp.single (parts i) 1) := by
  have hp (i : Fin n) : ∃ η : PiecewiseC1Path,
      η.path.a = node i.castSucc ∧ η.path.b = node i.succ ∧
        EqOn η γ (Icc (node i.castSucc) (node i.succ)) := by
    apply PiecewiseC1Path.exists_restriction
    · rw [← hfirst]
      exact hmono (Fin.zero_le _)
    · exact hmono i.castSucc_le_succ
    · rw [← hlast]
      exact hmono (Fin.le_last _)
  choose parts hleft hright he using hp
  have he' (i) : EqOn (parts i) γ (Icc (parts i).path.a (parts i).path.b) := by
    simpa only [hleft i, hright i] using he i
  exact ⟨parts, hleft, hright, he',
    finite_subdivision_contour_equivalent U γ n node hmono hfirst hlast parts hleft hright he' hin⟩

/-- Any open boundary-chart cover admits a finite subdivision of the actual
PC1 traversal subordinate to those charts. The comparison is constructed,
not included as an assumption; stationary and degenerate paths are retained. -/
theorem subdivision_subordinate_open_cover (U : Set ℂ) (γ : PiecewiseC1Path)
    {ι : Type*} (V : ι → Set ℂ) (hV : ∀ j, IsOpen (V j))
    (hcover : γ.trace ⊆ ⋃ j, V j) (hin : γ.trace ⊆ U) :
    ∃ (n : ℕ) (parts : Fin n → PiecewiseC1Path),
      ContourEquivalentOn U (Finsupp.single γ 1) (∑ i, Finsupp.single (parts i) 1) ∧
      (∀ i, ∃ j, (parts i).trace ⊆ V j) := by
  let c : ι → Set (Icc γ.path.a γ.path.b) :=
    fun j => γ.path.onInterval ⁻¹' V j
  have hc (j) : IsOpen (c j) := (hV j).preimage γ.path.onInterval.continuous
  have hcc : univ ⊆ ⋃ j, c j := by
    intro t ht
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨t, t.property, rfl⟩)
    exact mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨t, ht0, htmono, ⟨n, hn⟩, hgrid⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc γ.path.ordered hc hcc
  let node : Fin (n + 1) → ℝ := fun i => t i.val
  have hmono : Monotone node := fun i j hij => htmono hij
  have hfirst : node 0 = γ.path.a := ht0
  have hlast : node (Fin.last n) = γ.path.b := hn n le_rfl
  obtain ⟨parts, hleft, hright, he, hequiv⟩ :=
    finite_subdivision_exists U γ n node hmono hfirst hlast hin
  refine ⟨n, parts, hequiv, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := hgrid i.val
  refine ⟨j, ?_⟩
  rintro z ⟨s, hs, rfl⟩
  have hsi : s ∈ Icc (node i.castSucc) (node i.succ) := by
    simpa only [hleft i, hright i] using hs
  have hsγ : s ∈ Icc γ.path.a γ.path.b :=
    ⟨(t i.val).property.1.trans hsi.1, hsi.2.trans (t (i.val + 1)).property.2⟩
  have hsV : γ s ∈ V j := hj (show (⟨s,hsγ⟩ : Icc γ.path.a γ.path.b) ∈
      Icc (t i.val) (t (i.val + 1)) from hsi)
  rwa [he i hs]

open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model

/-- The lower-dimensional seams in a planar boundary display are finite
sets of points. This uses their actual parameter dimensions, not merely
their zero area in the ambient plane. -/
theorem boundary_seams_finite (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1) :
    Z.carrier.Finite := by
  apply Set.finite_iUnion
  intro i
  have he : Z.dim i = 0 := by have := hdim i; omega
  haveI : Subsingleton (E (Z.dim i)) := by
    rw [he]
    infer_instance
  exact (show (Z.parameter i).Subsingleton from
    fun _ _ _ _ => Subsingleton.elim _ _).finite.image (Z.map i)

/-- A displayed regular patch need not itself be regular off its Jordan
parameter set. The embedded chart nevertheless supplies a full-rank local
extension which agrees on the original closed parameter set. -/
theorem regular_piece_local_extension {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (u : E 1) (hu : u ∈ closure P.region) :
    ∃ (V : Set (E 1)) (g : E 1 → E 2),
      IsOpen V ∧ u ∈ V ∧ ContDiffOn ℝ 1 g V ∧
      EqOn P.map g (closure P.region ∩ V) ∧
      ∀ v ∈ V, Function.Injective (fderiv ℝ g v) := by
  obtain ⟨U, c, hU, huU, hsub, he, _hsign⟩ := hP u hu
  obtain ⟨W, g, hW, huW, hg, hgc, hgr⟩ := c.regular u (hsub ⟨hu, huU⟩)
  refine ⟨U ∩ W, g, hU.inter hW, ⟨huU, huW⟩,
    hgc.mono inter_subset_right, ?_, fun v hv => hgr v hv.2⟩
  intro v hv
  exact (he ⟨hv.1, hv.2.1⟩).trans (hg ⟨hsub ⟨hv.1, hv.2.1⟩, hv.2.2⟩).symm

/-- A genuine nonstationary real curve can be chosen locally for every
regular displayed boundary patch, including at isolated parameter points.
Only its values on the original closed parameter set are identified. -/
theorem regular_piece_local_curve {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (u : E 1) (hu : u ∈ closure P.region) :
    ∃ (V : Set ℝ) (g : ℝ → ℂ),
      IsOpen V ∧ u 0 ∈ V ∧ ContDiffOn ℝ 1 g V ∧
      (∀ t ∈ V, deriv g t ≠ 0) ∧
      ∀ t ∈ V, scalarPoint t ∈ closure P.region →
        planeCoordinates.symm (P.map (scalarPoint t)) = g t := by
  obtain ⟨W, f, hW, huW, hf, he, hr⟩ := regular_piece_local_extension o P s hP u hu
  have hscalar : ContDiff ℝ 1 scalarPoint := by
    have h : scalarPoint = fun t : ℝ => t • standardBasis 1 0 :=
      funext scalarPoint_eq_smul
    rw [h]
    exact contDiff_id.smul contDiff_const
  have hu' : scalarPoint (u 0) = u := by
    ext i
    fin_cases i
    rfl
  let V := scalarPoint ⁻¹' W
  let g : ℝ → ℂ := fun t => planeCoordinates.symm (f (scalarPoint t))
  refine ⟨V, g, hW.preimage hscalar.continuous, ?_,
    planeCoordinates.symm.contDiff.comp_contDiffOn
      (hf.comp hscalar.contDiffOn (fun _ ht => ht)), ?_, ?_⟩
  · change scalarPoint (u 0) ∈ W
    rwa [hu']
  · intro t ht
    have hd := (hf.contDiffAt (hW.mem_nhds ht)).differentiableAt (by decide)
    have hder : HasDerivAt g
        (planeCoordinates.symm (fderiv ℝ f (scalarPoint t) (standardBasis 1 0))) t :=
      planeCoordinates.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
        (hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_scalarPoint t))
    rw [hder.deriv]
    intro hz
    have hz' : fderiv ℝ f (scalarPoint t) (standardBasis 1 0) = 0 :=
      planeCoordinates.symm.injective (by simpa only [map_zero] using hz)
    have hb : (standardBasis 1 0 : E 1) = 0 :=
      hr _ ht (hz'.trans (map_zero _).symm)
    have h0 := congrArg (fun x : E 1 => x 0) hb
    change (D04.standardBasis 1 0) 0 = 0 at h0
    simpa [D04.standardBasis_apply] using h0
  · intro t ht htc
    exact congrArg planeCoordinates.symm (he ⟨htc, ht⟩)

/-- The local scalar inverse is derived from the actual D04 regular-piece
data. No nonzero derivative of the arbitrary patch representative is needed. -/
theorem regular_piece_local_coordinate {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (u : E 1) (hu : u ∈ closure P.region) :
    ∃ (V : Set ℝ) (ψ : ℂ → ℝ), IsOpen V ∧ u 0 ∈ V ∧
      ContDiffAt ℝ 1 ψ (planeCoordinates.symm (P.map u)) ∧
      ∀ t ∈ V, scalarPoint t ∈ closure P.region →
        ψ (planeCoordinates.symm (P.map (scalarPoint t))) = t := by
  obtain ⟨W, g, hW, huW, hg, hv, he⟩ := regular_piece_local_curve o P s hP u hu
  obtain ⟨ψ, hψ, hleft⟩ := regular_curve_local_coordinate g (u 0)
    (hg.contDiffAt (hW.mem_nhds huW)) (hv _ huW)
  obtain ⟨V, hVsub, hVopen, huV⟩ := mem_nhds_iff.mp hleft
  have hu' : scalarPoint (u 0) = u := by
    ext i
    fin_cases i
    rfl
  have hecenter : planeCoordinates.symm (P.map u) = g (u 0) := by
    simpa only [hu'] using he (u 0) huW (by rwa [hu'])
  refine ⟨W ∩ V, ψ, hW.inter hVopen, ⟨huW, huV⟩, ?_, ?_⟩
  · rwa [hecenter]
  · intro t ht htc
    rw [he t ht.1 htc]
    exact hVsub ht.2

/-- Smoothness of a parameter into an actual D04 boundary patch is a
consequence of smoothness of the traced curve. The parameter is assumed
continuous, but may have stationary points and flat intervals. -/
theorem regular_piece_recover_parameter {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (f : ℝ → ℂ) (φ : ℝ → E 1) (S : Set ℝ)
    (hf : ContDiffOn ℝ 1 f S) (hφ : ContinuousOn φ S)
    (hmap : MapsTo φ S (closure P.region))
    (he : EqOn f (fun t => planeCoordinates.symm (P.map (φ t))) S) :
    ContDiffOn ℝ 1 φ S := by
  have heval : Continuous (fun x : E 1 => x 0) :=
    (continuous_apply 0).comp (coordinates 1).toContinuousLinearEquiv.continuous
  have hscalar : ContDiff ℝ 1 scalarPoint := by
    have h : scalarPoint = fun t : ℝ => t • standardBasis 1 0 :=
      funext scalarPoint_eq_smul
    rw [h]
    exact contDiff_id.smul contDiff_const
  have hscalar_eval (u : E 1) : scalarPoint (u 0) = u := by
    ext i
    fin_cases i
    rfl
  intro t ht
  obtain ⟨V, ψ, hV, htV, hψ, hinv⟩ :=
    regular_piece_local_coordinate o P s hP (φ t) (hmap ht)
  have heq : (fun x => scalarPoint (ψ (f x))) =ᶠ[nhdsWithin t S] φ := by
    filter_upwards [((heval.comp_continuousOn hφ) t ht).eventually
      (hV.mem_nhds htV), self_mem_nhdsWithin] with x hx hxS
    have hxi := hinv (φ x 0) hx (by
      rw [hscalar_eval]
      exact hmap hxS)
    rw [hscalar_eval] at hxi
    rw [he hxS]
    exact (congrArg scalarPoint hxi).trans (hscalar_eval (φ x))
  have hc : ContDiffWithinAt ℝ 1 (fun x => scalarPoint (ψ (f x))) S t := by
    apply hscalar.contDiffAt.comp_contDiffWithinAt
    apply ContDiffAt.comp_contDiffWithinAt t _ (hf t ht)
    rwa [he ht]
  exact hc.congr_of_eventuallyEq_of_mem heq.symm ht

/-- Compactness and the actual chart inverse make every fibre of a regular
displayed patch finite, even if its Jordan parameter set is disconnected. -/
theorem regular_piece_fiber_finite {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (z : E 2) :
    (closure P.region ∩ P.map ⁻¹' {z}).Finite := by
  classical
  have hlocal (u : closure P.region) :
      ∃ V : Set (E 1), IsOpen V ∧ u.val ∈ V ∧
        InjOn P.map (closure P.region ∩ V) := by
    obtain ⟨V, c, hV, huV, hsub, he, _⟩ := hP u u.property
    refine ⟨V, hV, huV, ?_⟩
    intro x hx y hy hxy
    have hchart : c.toFun x = c.toFun y := (he hx).symm.trans (hxy.trans (he hy))
    calc
      x = c.invFun (c.toFun x) := (c.left_inv x (hsub hx)).symm
      _ = c.invFun (c.toFun y) := congrArg c.invFun hchart
      _ = y := c.left_inv y (hsub hy)
  choose V hV huV hinj using hlocal
  obtain ⟨t, ht⟩ := (D04.GeometricPatches.region_compact P).elim_finite_subcover V hV
    (fun u hu => mem_iUnion.mpr ⟨⟨u, hu⟩, huV ⟨u, hu⟩⟩)
  have hfin : (⋃ i ∈ t, (closure P.region ∩ P.map ⁻¹' {z}) ∩ V i).Finite := by
    apply t.finite_toSet.biUnion
    intro i _
    apply Set.Subsingleton.finite
    intro x hx y hy
    exact hinj i ⟨hx.1.1, hx.2⟩ ⟨hy.1.1, hy.2⟩ (hx.1.2.trans hy.1.2.symm)
  apply hfin.subset
  intro u hu
  obtain ⟨i, hi, hui⟩ := mem_iUnion₂.mp (ht hu.1)
  exact mem_iUnion₂.mpr ⟨i, hi, hu, hui⟩

/-- In particular all parameter values mapping into an actual boundary seam
form a finite set. This justifies using finitely many cut parameters. -/
theorem regular_piece_seam_parameters_finite {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1) :
    (closure P.region ∩ P.map ⁻¹' Z.carrier).Finite := by
  have hfin := (boundary_seams_finite Z hdim).biUnion
    (fun z _ => regular_piece_fiber_finite o P s hP z)
  apply hfin.subset
  intro u hu
  exact mem_iUnion₂.mpr ⟨P.map u, hu.2, hu.1, rfl⟩

/-- The arbitrary Jordan parameter set has a finite disjoint Jordan
localization on each of which the regular reference curve is available.
This does not assert that these localized sets are intervals. -/
theorem regular_piece_localized_curves {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) :
    ∃ (m : ℕ) (R : Fin m → Set (E 1)) (V : Fin m → Set ℝ) (g : Fin m → ℝ → ℂ),
      (∀ i, Jordan (R i)) ∧ (∀ i, R i ⊆ P.region) ∧
      (Pairwise fun i j => Disjoint (R i) (R j)) ∧ P.region = ⋃ i, R i ∧
      (∀ i, IsOpen (V i)) ∧ (∀ i, (fun u : E 1 => u 0) '' closure (R i) ⊆ V i) ∧
      (∀ i, ContDiffOn ℝ 1 (g i) (V i)) ∧
      (∀ i t, t ∈ V i → deriv (g i) t ≠ 0) ∧
      ∀ i u, u ∈ closure (R i) → planeCoordinates.symm (P.map u) = g i (u 0) := by
  classical
  choose V g hV huV hg hv he using
    (fun u : closure P.region => regular_piece_local_curve o P s hP u u.property)
  have heval : Continuous (fun x : E 1 => x 0) :=
    (continuous_apply 0).comp (coordinates 1).toContinuousLinearEquiv.continuous
  obtain ⟨m, a, R, hR, hsub, hclose, hpair, hcover⟩ :=
    D04.GeometricPatches.jordan_localization P.region P.jordan
      (fun u : closure P.region => (fun x : E 1 => x 0) ⁻¹' V u)
      (fun u => (hV u).preimage heval)
      (fun u hu => mem_iUnion.mpr ⟨⟨u, hu⟩, huV ⟨u, hu⟩⟩)
  refine ⟨m, R, fun i => V (a i), fun i => g (a i), hR, hsub, hpair, hcover,
    fun i => hV (a i), ?_, fun i => hg (a i), fun i => hv (a i), ?_⟩
  · intro i t ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact hclose i hu
  · intro i u hu
    have hPu : u ∈ closure P.region := closure_mono (hsub i) hu
    have hu' : scalarPoint (u 0) = u := by
      ext j
      fin_cases j
      rfl
    simpa only [hu'] using he (a i) (u 0) (hclose i hu) (by rwa [hu'])

/-- A regular Jordan display can be replaced geometrically by finitely many
patches with actual nonstationary curve representatives. Both the Jordan
subsets and the signed patch equivalence are retained; no interval claim or
integral equality is an assumption. -/
theorem regular_piece_regular_representatives {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hO : IsOpen O) (hP : RegularPiece o P s) :
    ∃ (m : ℕ) (Q : Fin m → Patch 1 O) (V : Fin m → Set ℝ) (g : Fin m → ℝ → ℂ),
      P.region = ⋃ i, (Q i).region ∧
      (Pairwise fun i j => Disjoint (Q i).region (Q j).region) ∧
      (∀ i, IsOpen (V i)) ∧ (∀ i, ContDiffOn ℝ 1 (g i) (V i)) ∧
      (∀ i t, t ∈ V i → deriv (g i) t ≠ 0) ∧
      (∀ i u, u ∈ closure (Q i).region → u 0 ∈ V i) ∧
      (∀ i u, (Q i).map u = planeCoordinates (g i (u 0))) ∧
      (∀ i, EqOn P.map (Q i).map (closure (Q i).region)) ∧
      GeometricEquivalent
        (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
        (∑ i, Finsupp.single
          (⟨Q i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
  classical
  obtain ⟨m, R, V, g, hR, hsub, hpair, hcover, hV, hclose, hg, hv, he⟩ :=
    regular_piece_localized_curves o P s hP
  have heval : ContDiff ℝ 1 (fun x : E 1 => x 0) :=
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).comp
      ((coordinates 1).toContinuousLinearEquiv.contDiff)
  have heplane (i) (u) (hu : u ∈ closure (R i)) :
      P.map u = planeCoordinates (g i (u 0)) := by
    rw [← he i u hu, ContinuousLinearEquiv.apply_symm_apply]
  let f (i : Fin m) (u : E 1) := planeCoordinates (g i (u 0))
  let W (i : Fin m) := ((fun u : E 1 => u 0) ⁻¹' V i) ∩ f i ⁻¹' O
  have hfc (i) : ContDiffOn ℝ 1 (f i) ((fun u : E 1 => u 0) ⁻¹' V i) :=
    planeCoordinates.contDiff.comp_contDiffOn
      ((hg i).comp heval.contDiffOn (fun _ hu => hu))
  have hWo (i) : IsOpen (W i) := by
    exact (hfc i).continuousOn.isOpen_inter_preimage
      ((hV i).preimage heval.continuous) hO
  have hcontains (i) : closure (R i) ⊆ W i := by
    intro u hu
    refine ⟨hclose i ⟨u, hu, rfl⟩, ?_⟩
    change planeCoordinates (g i (u 0)) ∈ O
    rw [← heplane i u hu]
    exact P.mapsTo (P.contains (closure_mono (hsub i) hu))
  let Q (i : Fin m) : Patch 1 O := {
    region := R i
    jordan := hR i
    map := f i
    domain := W i
    open_domain := hWo i
    contains := hcontains i
    regular := (hfc i).mono inter_subset_left
    mapsTo := fun _ hu => hu.2 }
  refine ⟨m, Q, V, g, hcover, hpair, hV, hg, hv,
    fun i u hu => hclose i ⟨u, hu, rfl⟩, fun _ _ => rfl, ?_, ?_⟩
  · intro i u hu
    exact heplane i u hu
  · let Z : Seams 1 := {
      count := 0
      dim := Fin.elim0
      lower := fun i => Fin.elim0 i
      parameter := fun i => Fin.elim0 i
      compact := fun i => Fin.elim0 i
      map := fun i => Fin.elim0 i
      localC1 := fun i => Fin.elim0 i }
    have hcoverGE := GeometricEquivalent.cover
      (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      m R hR hsub hcover Z (by
        intro i j hij u hu
        exact False.elim (Set.disjoint_left.mp (hpair hij) hu.1 hu.2))
    apply hcoverGE.trans
    have hsingle (i : Fin m) : GeometricEquivalent
        (Finsupp.single
          (restrictWeighted (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
            (R i) (hR i) (hsub i)) 1)
        (Finsupp.single (⟨Q i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
      apply GeometricEquivalent.representative
      · rfl
      · exact fun u hu => heplane i u (subset_closure hu)
      · exact fun _ _ => rfl
    have hsum (t : Finset (Fin m)) : GeometricEquivalent
        (∑ i ∈ t, Finsupp.single
          (restrictWeighted (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
            (R i) (hR i) (hsub i)) 1)
        (∑ i ∈ t, Finsupp.single
          (⟨Q i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
      induction t using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact .refl 0
      | @insert i t hnot ih =>
        simpa only [Finset.sum_insert hnot] using (hsingle i).add ih
    exact hsum Finset.univ

/-- Additive gluing retains all integer coefficients. -/
theorem PatchEquivalentOffFinite.sum {O : Set (E 2)} {ι : Type*}
    (t : Finset ι) (C D : ι → PatchChain 1 O)
    (h : ∀ i ∈ t, PatchEquivalentOffFinite (C i) (D i)) :
    PatchEquivalentOffFinite (∑ i ∈ t, C i) (∑ i ∈ t, D i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact .refl 0
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i t)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- A common reference patch may be covered by arbitrary Jordan regions in
other charts. Transport is through actual C1 diffeomorphisms with checked
Jacobian signs; finite omissions and repeated seam points contribute zero. -/
theorem patch_chart_cover_equivalent {O : Set (E 2)}
    (p : WeightedPatch 1 O) (m : ℕ) (Q : Fin m → WeightedPatch 1 O)
    (e : Fin m → OpenPartialHomeomorph (E 1) (E 1))
    (he : ∀ i, ContDiffOn ℝ 1 (e i) (e i).source)
    (hei : ∀ i, ContDiffOn ℝ 1 (e i).symm (e i).target)
    (hsource : ∀ i, closure (Q i).patch.region ⊆ (e i).source)
    (hsub : ∀ i, (e i) '' (Q i).patch.region ⊆ p.patch.region)
    (δ : Fin m → ℤ) (hδ : ∀ i, δ i = 1 ∨ δ i = -1)
    (hsign : ∀ i x, x ∈ (e i).source →
      Real.sign ((fderiv ℝ (e i) x).det) = (δ i : ℝ))
    (hmap : ∀ i, EqOn (Q i).patch.map (p.patch.map ∘ (e i)) (Q i).patch.region)
    (hweight : ∀ i, EqOn (Q i).weight p.weight
      (p.patch.map '' ((e i) '' (Q i).patch.region)))
    (Z : Set (E 1)) (hZ : Z.Finite)
    (hcover : p.patch.region \ Z ⊆ ⋃ i, (e i) '' (Q i).patch.region)
    (hpair : ∀ i j, i ≠ j →
      ((e i) '' (Q i).patch.region) ∩ ((e j) '' (Q j).patch.region) ⊆ Z) :
    PatchEquivalentOffFinite (Finsupp.single p 1)
      (∑ i, δ i • Finsupp.single (Q i) 1) := by
  classical
  let R (i : Fin m) := (e i) '' (Q i).patch.region
  have hR (i : Fin m) : Jordan (R i) :=
    (D04.RegionSubstitution.jordan_image (e i) (he i) (hei i) (Q i).patch.region
      (Q i).patch.jordan (D04.JordanRegions.jordan_bounded (Q i).patch.jordan).isCompact_closure
      (hsource i)).2
  apply PatchEquivalentOffFinite.trans (.cover p m R hR hsub Z hZ hcover hpair)
  apply PatchEquivalentOffFinite.sum
  intro i _
  let q := restrictWeighted p (R i) (hR i) (hsub i)
  let hh : LocalReparametrization (Q i).patch.region q.patch.region (δ i : ℝ) := {
    map := e i
    bijective := ⟨fun u hu => mem_image_of_mem (e i) hu,
      (e i).injOn.mono (fun _ hu => hsource i (subset_closure hu)),
      fun _ hu => hu⟩
    localCharts := fun u hu => ⟨e i, hsource i hu, he i, hei i,
      fun _ _ => rfl, hsign i⟩ }
  have hgeom : PatchEquivalentOffFinite (Finsupp.single (Q i) 1)
      (δ i • Finsupp.single q 1) := .geometric
    (.reparam (Q i) q (δ i) (hδ i) hh (hmap i) (hweight i))
  have hrev := hgeom.symm.zsmul (δ i)
  rcases hδ i with hi | hi <;> simpa [hi] using hrev

/-- The integer encoding agrees with every actual directed reparametrization. -/
theorem signed_patch_reparam_equivalent {O : Set (E 2)}
    (p q : WeightedPatch 1 O) (a b : ℤ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h : LocalReparametrization p.patch.region q.patch.region σ)
    (hmap : EqOn p.patch.map (q.patch.map ∘ h.map) p.patch.region)
    (hweight : EqOn p.weight q.weight (q.patch.map '' q.patch.region))
    (hab : (a : ℝ) * σ = (b : ℝ)) :
    PatchEquivalentOffFinite (Finsupp.single p a) (Finsupp.single q b) := by
  rcases hσ with rfl | rfl
  · have hab' : a = b := by exact_mod_cast (show (a : ℝ) = (b : ℝ) by simpa using hab)
    subst b
    let h' : LocalReparametrization p.patch.region q.patch.region ((1 : ℤ) : ℝ) := {
      map := h.map
      bijective := h.bijective
      localCharts := by simpa only [Int.cast_one] using h.localCharts }
    have he : PatchEquivalentOffFinite (Finsupp.single p 1)
        ((1 : ℤ) • Finsupp.single q 1) := .geometric
      (.reparam p q 1 (Or.inl rfl) h' hmap hweight)
    simpa [Finsupp.smul_single, smul_eq_mul] using he.zsmul a
  · have hab' : -a = b := by exact_mod_cast (show -(a : ℝ) = (b : ℝ) by simpa using hab)
    subst b
    let h' : LocalReparametrization p.patch.region q.patch.region ((-1 : ℤ) : ℝ) := {
      map := h.map
      bijective := h.bijective
      localCharts := by simpa only [Int.cast_neg, Int.cast_one] using h.localCharts }
    have he : PatchEquivalentOffFinite (Finsupp.single p 1)
        ((-1 : ℤ) • Finsupp.single q 1) := .geometric
      (.reparam p q (-1) (Or.inr rfl) h' hmap hweight)
    simpa [Finsupp.smul_single, smul_eq_mul] using he.zsmul a

/-- Reindex the supplied occurrences, match the outer orientations, and
cancel each actual internal pair. No integral identity is an input. -/
theorem manifold_boundary_assembly_equivalent {O : Set (E 2)}
    (d : ManifoldGreenData O) :
    PatchEquivalentOffFinite (∑ j, (d.boundaryDisplay j).patchChain) d.outerChain := by
  classical
  let f : ((j : Fin d.count) × Fin (d.patchCount j)) → PatchChain 1 O :=
    fun z => Finsupp.single
      (⟨d.patch z.1 z.2, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      (orientationInteger (d.sign z.1 z.2))
  have hreindex : (∑ j, (d.boundaryDisplay j).patchChain) =
      (∑ t, f (d.occurrence (Sum.inl t))) +
      ∑ i, (f (d.occurrence (Sum.inr (i, false))) +
        f (d.occurrence (Sum.inr (i, true)))) := by
    change (∑ j, ∑ t, f ⟨j,t⟩) = _
    rw [← Fintype.sum_sigma, ← d.occurrence.sum_comp, Fintype.sum_sum_type]
    congr 1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fintype.sum_bool, add_comm]
  rw [hreindex]
  have hout : PatchEquivalentOffFinite (∑ t, f (d.occurrence (Sum.inl t))) d.outerChain := by
    unfold ManifoldGreenData.outerChain
    apply PatchEquivalentOffFinite.sum
    intro t _
    dsimp only [f]
    apply signed_patch_reparam_equivalent
      (⟨d.patch (d.occurrence (Sum.inl t)).1 (d.occurrence (Sum.inl t)).2,
        fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      (⟨d.outer t, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      _ _ (d.outerDirection t)
      (d.outerDirection_sign t) (d.outerReparam t) (d.outerMatch t).1
      (fun _ _ => rfl)
    simpa only [orientationInteger_real] using (d.outerMatch t).2
  have hpairs : PatchEquivalentOffFinite
      (∑ i, (f (d.occurrence (Sum.inr (i, false))) +
        f (d.occurrence (Sum.inr (i, true))))) (∑ _ : Fin d.pairCount, (0 : PatchChain 1 O)) := by
    apply PatchEquivalentOffFinite.sum
    intro i _
    have he : PatchEquivalentOffFinite
        (f (d.occurrence (Sum.inr (i, false))))
        (-f (d.occurrence (Sum.inr (i, true)))) := by
      dsimp only [f]
      rw [← Finsupp.single_neg]
      apply signed_patch_reparam_equivalent
        (⟨d.patch (d.occurrence (Sum.inr (i,false))).1 (d.occurrence (Sum.inr (i,false))).2,
          fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
        (⟨d.patch (d.occurrence (Sum.inr (i,true))).1 (d.occurrence (Sum.inr (i,true))).2,
          fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
        _ _ (d.pairDirection i)
        (d.pairDirection_sign i) (d.pairReparam i) (d.pairMatch i).1
        (fun _ _ => rfl)
      simpa only [Int.cast_neg, orientationInteger_real] using (d.pairMatch i).2
    simpa only [neg_add_cancel] using he.add (.refl (f (d.occurrence (Sum.inr (i,true)))))
  simpa only [Finset.sum_const_zero, add_zero] using hout.add hpairs

/-- Any independently supplied regular displays of the same boundary pieces
can replace the original displays. Internal cancellation and induced signs
remain those of the original Green assembly. -/
theorem manifold_boundary_displays_equivalent {O : Set (E 2)}
    (d : ManifoldGreenData O)
    (e : (j : Fin d.count) → RegularBoundaryDisplay (O := O) (d.boundaryOrientation j)) :
    PatchEquivalentOffFinite d.outerChain (∑ j, (e j).patchChain) := by
  apply (manifold_boundary_assembly_equivalent d).symm.trans
  apply PatchEquivalentOffFinite.sum
  intro j _
  exact .display (d.boundaryOrientation j)
    (D04.ManifoldBoundaryAssembly.boundary_compact (d.piece j))
    (fun _ hx => (d.piece j).subset_domain hx.1) (d.boundaryDisplay j) (e j)

/-- Construct the regular reference traversal instead of asking for it as input.
Only its speed is nonzero; the original directed PC1 traversal may pause. -/
theorem regular_arc_representative_exists (U : Set ℂ) (γ : PiecewiseC1Path)
    (φ : ℝ → ℝ) (g : ℝ → ℂ)
    (hc : ContinuousOn φ (Icc γ.path.a γ.path.b))
    (hm : MonotoneOn φ (Icc γ.path.a γ.path.b))
    (hg : ∀ t ∈ Icc (φ γ.path.a) (φ γ.path.b), ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc (φ γ.path.a) (φ γ.path.b), deriv g t ≠ 0)
    (he : EqOn γ (fun t => g (φ t)) (Icc γ.path.a γ.path.b))
    (hin : γ.trace ⊆ U) :
    ∃ η : PiecewiseC1Path, η.path.a = φ γ.path.a ∧ η.path.b = φ γ.path.b ∧
      EqOn η g (Icc η.path.a η.path.b) ∧ η.trace = γ.trace ∧
      ContourEquivalentOn U (Finsupp.single γ 1) (Finsupp.single η 1) := by
  have ha : γ.path.a ∈ Icc γ.path.a γ.path.b := ⟨le_rfl, γ.path.ordered⟩
  have hb : γ.path.b ∈ Icc γ.path.a γ.path.b := ⟨γ.path.ordered, le_rfl⟩
  have hab : φ γ.path.a ≤ φ γ.path.b := hm ha hb γ.path.ordered
  have hgOn : ContDiffOn ℝ 1 g (Icc (φ γ.path.a) (φ γ.path.b)) :=
    fun t ht => (hg t ht).contDiffWithinAt
  let p : ComplexPath := ⟨φ γ.path.a, φ γ.path.b, hab, g, hgOn.continuousOn⟩
  let η : PiecewiseC1Path := ⟨p, ⟨C1Partition.single p hgOn⟩⟩
  have hmaps : MapsTo φ (Icc γ.path.a γ.path.b) (Icc η.path.a η.path.b) :=
    fun t ht => ⟨hm ha ht ht.1, hm ht hb ht.2⟩
  have hsurj : SurjOn φ (Icc γ.path.a γ.path.b) (Icc η.path.a η.path.b) :=
    hc.surjOn_Icc ha hb
  have htrace : η.trace = γ.trace := by
    apply Subset.antisymm
    · rintro z ⟨t,ht,rfl⟩
      obtain ⟨u,hu,heq⟩ := hsurj ht
      exact ⟨u,hu,(he hu).trans (congrArg g heq)⟩
    · rintro z ⟨t,ht,rfl⟩
      exact ⟨φ t,hmaps ht,(he ht).symm⟩
  refine ⟨η,rfl,rfl,(fun _ _ => rfl),htrace,?_⟩
  exact regular_monotone_contour_equivalent U η γ φ g (htrace ▸ hin) hc hm
    hmaps hsurj hg hv (fun _ _ => rfl) he

/-- Regularity of a geometric boundary patch depends on its values on the
closed parameter set, including restricted Jordan subsets. -/
theorem regular_piece_closed_restriction {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P Q : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (hsub : closure Q.region ⊆ closure P.region)
    (he : EqOn Q.map P.map (closure Q.region)) : RegularPiece o Q s := by
  intro u hu
  obtain ⟨V,c,hV,huV,hsource,hmap,hsign⟩ := hP u (hsub hu)
  exact ⟨V,c,hV,huV,(fun v hv => hsource ⟨hsub hv.1,hv.2⟩),
    (fun v hv => (he hv.1).trans (hmap ⟨hsub hv.1,hv.2⟩)),hsign⟩

/-- Construct the local boundary comparison from actual replacement displays
and an algebraic enumeration of their signed patches. -/
theorem finite_boundary_representation_of_displays (U K : Set ℂ) (Γ : IntegralChain)
    (d : ManifoldGreenData (planeCoordinates.symm ⁻¹' U))
    (hcarrier : d.carrier = planeCoordinates '' K)
    (C : IntegralChain) (htraversal : ContourEquivalentOn U Γ C)
    (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C)
    (hc : ∀ j, (c.path j).trace ⊆ U)
    (e : (j : Fin d.count) → RegularBoundaryDisplay
      (O := planeCoordinates.symm ⁻¹' U) (d.boundaryOrientation j))
    (he : (∑ j, (e j).patchChain) = c.patchChain) :
    Nonempty (FiniteBoundaryRepresentation U K Γ) := by
  exact ⟨{ geometry := .manifold d
           carrier_eq := hcarrier
           representedChain := C
           traversal := htraversal
           contour := c
           contour_in := hc
           represents := he ▸ manifold_boundary_displays_equivalent d e }⟩

/-- The canonical interval patches of a traversal in a regular displayed
patch inherit its actual orientation, independently of their C1 extensions. -/
theorem path_patches_regular {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path) (d : PathPatchData O γ)
    (hparameter : MapsTo scalarPoint (Icc γ.path.a γ.path.b) (closure P.region))
    (hmap : ∀ t ∈ Icc γ.path.a γ.path.b,
      planeCoordinates (γ t) = P.map (scalarPoint t)) :
    ∀ i, RegularPiece o (d.patch i) s := by
  intro i
  have hclosed : IsClosed (d.patch i).region := by
    rw [d.region i]
    exact (D04.DiscontinuityCriterion.carrier_compact _).isClosed
  have hcoord (u : E 1) : scalarPoint (u 0) = u := by
    ext j
    fin_cases j
    rfl
  have hmem {u : E 1} (hu : u ∈ closure (d.patch i).region) :
      u 0 ∈ γ.partition.pieceSet i := by
    rw [hclosed.closure_eq, d.region i] at hu
    exact hu 0
  apply regular_piece_closed_restriction o P (d.patch i) s hP
  · intro u hu
    rw [← hcoord u]
    exact hparameter (γ.partition.piece_subset i (hmem hu))
  · intro u hu
    have ht := hmem hu
    rw [← hcoord u]
    exact (d.map i _ ht).trans (hmap _ (γ.partition.piece_subset i ht))

/-- A path in the image of an injective compact patch determines its own
continuous parameter. No parameter map is an input. -/
theorem patch_parameter_exists {O : Set (E 2)} (P : Patch 1 O)
    (γ : PiecewiseC1Path) (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region) :
    ∃ φ : ℝ → E 1, ContinuousOn φ (Icc γ.path.a γ.path.b) ∧
      MapsTo φ (Icc γ.path.a γ.path.b) (closure P.region) ∧
      ∀ t ∈ Icc γ.path.a γ.path.b, P.map (φ t) = planeCoordinates (γ t) := by
  classical
  let φ : ℝ → E 1 := fun t => Function.invFunOn P.map (closure P.region)
    (planeCoordinates (γ t))
  have hex (t : ℝ) (ht : t ∈ Icc γ.path.a γ.path.b) :
      ∃ u ∈ closure P.region, P.map u = planeCoordinates (γ t) :=
    hin ⟨γ t, ⟨t, ht, rfl⟩, rfl⟩
  have hmap : MapsTo φ (Icc γ.path.a γ.path.b) (closure P.region) :=
    fun t ht => Function.invFunOn_mem (hex t ht)
  have he (t : ℝ) (ht : t ∈ Icc γ.path.a γ.path.b) :
      P.map (φ t) = planeCoordinates (γ t) := Function.invFunOn_eq (hex t ht)
  refine ⟨φ, ?_, hmap, he⟩
  letI : CompactSpace (closure P.region) :=
    isCompact_iff_compactSpace.mp (D04.GeometricPatches.region_compact P)
  let F : Icc γ.path.a γ.path.b → closure P.region := fun t => ⟨φ t, hmap t.property⟩
  have hPc : ContinuousOn P.map (closure P.region) :=
    P.regular.continuousOn.mono P.contains
  have hEmb := hPc.domRestrict.isClosedEmbedding hinj.injective
  have hFc : Continuous F := hEmb.isEmbedding.continuous_iff.mpr (by
    convert planeCoordinates.continuous.comp γ.path.continuousOn.domRestrict using 1
    funext t
    exact he t t.property)
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hFc)

/-- Geometric order on an injective regular patch gives a nondecreasing
scalar parameter, whose piecewise C1 regularity is derived even at pauses. -/
theorem ordered_regular_piece_parameter_exists {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (horder : ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b,
      x ≤ y → ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc γ.path.a γ.path.b) ∧
      MonotoneOn φ (Icc γ.path.a γ.path.b) ∧
      MapsTo (fun t => scalarPoint (φ t)) (Icc γ.path.a γ.path.b) (closure P.region) ∧
      (∀ t ∈ Icc γ.path.a γ.path.b,
        planeCoordinates.symm (P.map (scalarPoint (φ t))) = γ t) ∧
      ∀ i, ContDiffOn ℝ 1 φ (γ.partition.pieceSet i) := by
  obtain ⟨ψ, hc, hmap, he⟩ := patch_parameter_exists P γ hinj hin
  have heval : ContDiff ℝ 1 (fun u : E 1 => u 0) :=
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).comp (coordinates 1).toContinuousLinearEquiv.contDiff
  have hs (u : E 1) : scalarPoint (u 0) = u := by
    ext j
    fin_cases j
    rfl
  refine ⟨fun t => ψ t 0, heval.continuous.comp_continuousOn hc, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact horder x hx y hy hxy _ (hmap hx) _ (hmap hy) (he x hx) (he y hy)
  · intro t ht
    simpa only [hs] using hmap ht
  · intro t ht
    rw [hs, he t ht, coordinates_symm]
  · intro i
    apply heval.comp_contDiffOn
    apply regular_piece_recover_parameter o P s hP γ ψ (γ.partition.pieceSet i)
      (γ.partition.smooth i) (hc.mono (γ.partition.piece_subset i))
      (hmap.mono (γ.partition.piece_subset i) Subset.rfl)
    intro t ht
    simpa only [coordinates_symm] using
      (congrArg planeCoordinates.symm (he t (γ.partition.piece_subset i ht))).symm

/-- On a nondegenerate scalar interval contained in a regular patch's closed
parameter set, the actual representative has nonzero velocity, also at the
endpoints. No regularity off that closed set is inferred. -/
theorem regular_piece_interval_curve {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (a b : ℝ) (hab : a < b)
    (hin : MapsTo scalarPoint (Icc a b) (closure P.region)) :
    ∀ t ∈ Icc a b,
      ContDiffAt ℝ 1 (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t ∧
      deriv (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t ≠ 0 := by
  have hscalar : ContDiff ℝ 1 scalarPoint := by
    have heq : scalarPoint = fun t : ℝ => t • standardBasis 1 0 :=
      funext scalarPoint_eq_smul
    rw [heq]
    exact contDiff_id.smul contDiff_const
  intro t ht
  have hf : ContDiffAt ℝ 1 (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t :=
    planeCoordinates.symm.contDiff.contDiffAt.comp t
      ((P.regular.contDiffAt (P.open_domain.mem_nhds (P.contains (hin ht)))).comp t
        hscalar.contDiffAt)
  refine ⟨hf, ?_⟩
  obtain ⟨V, g, hV, htV, hg, hv, he⟩ :=
    regular_piece_local_curve o P s hP (scalarPoint t) (hin ht)
  change t ∈ V at htV
  have heq : (fun u => planeCoordinates.symm (P.map (scalarPoint u)))
      =ᶠ[nhdsWithin t (Icc a b)] g := by
    filter_upwards [(show ∀ᶠ u in nhds t, u ∈ V from hV.mem_nhds htV).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu huI
    exact he u hu (hin huI)
  have hu := (uniqueDiffOn_Icc hab) t ht
  have hd : deriv (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t = deriv g t := by
    rw [← (hf.differentiableAt (by decide)).derivWithin hu,
      heq.derivWithin_eq_of_mem ht,
      (hg.contDiffAt (hV.mem_nhds htV)).differentiableAt (by decide) |>.derivWithin hu]
  rw [hd]
  exact hv t htV

/-- Recover and normalize the traversal of an injective regular boundary
patch. Its scalar parameter and the reference path are constructed, with the
original induced sign inherited by every canonical reference interval patch.
Original stationary points, flat portions, and degenerate intervals are allowed. -/
theorem ordered_regular_piece_representative_exists {O M : Set (E 2)}
    (U : Set ℂ) (o : PositiveManifoldOrientation 1 1 M)
    (P : Patch 1 O) (s : PointSign) (hP : RegularPiece o P s)
    (γ : PiecewiseC1Path) (hU : γ.trace ⊆ U)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (horder : ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b,
      x ≤ y → ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0) :
    ∃ (φ : ℝ → ℝ) (η : PiecewiseC1Path),
      ContinuousOn φ (Icc γ.path.a γ.path.b) ∧
      MonotoneOn φ (Icc γ.path.a γ.path.b) ∧
      η.path.a = φ γ.path.a ∧ η.path.b = φ γ.path.b ∧
      EqOn η (fun t => planeCoordinates.symm (P.map (scalarPoint t)))
        (Icc η.path.a η.path.b) ∧
      η.trace = γ.trace ∧
      ContourEquivalentOn U (Finsupp.single γ 1) (Finsupp.single η 1) ∧
      (∀ d : PathPatchData O η, ∀ i, RegularPiece o (d.patch i) s) ∧
      (η.path.a < η.path.b → ∀ t ∈ Icc η.path.a η.path.b,
        deriv (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t ≠ 0) := by
  obtain ⟨φ, hc, hm, hmap, he, hφsmooth⟩ :=
    ordered_regular_piece_parameter_exists o P s hP γ hinj hin horder
  have ha : γ.path.a ∈ Icc γ.path.a γ.path.b := ⟨le_rfl, γ.path.ordered⟩
  have hb : γ.path.b ∈ Icc γ.path.a γ.path.b := ⟨γ.path.ordered, le_rfl⟩
  have hab : φ γ.path.a ≤ φ γ.path.b := hm ha hb γ.path.ordered
  have hsurj : SurjOn φ (Icc γ.path.a γ.path.b)
      (Icc (φ γ.path.a) (φ γ.path.b)) := hc.surjOn_Icc ha hb
  have hinterval : MapsTo scalarPoint (Icc (φ γ.path.a) (φ γ.path.b))
      (closure P.region) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := hsurj ht
    exact hmap hu
  have hscalar : ContDiff ℝ 1 scalarPoint := by
    have heq : scalarPoint = fun t : ℝ => t • standardBasis 1 0 :=
      funext scalarPoint_eq_smul
    rw [heq]
    exact contDiff_id.smul contDiff_const
  let g : ℝ → ℂ := fun t => planeCoordinates.symm (P.map (scalarPoint t))
  have hg : ContDiffOn ℝ 1 g (Icc (φ γ.path.a) (φ γ.path.b)) :=
    planeCoordinates.symm.contDiff.comp_contDiffOn
      (P.regular.comp hscalar.contDiffOn (fun t ht => P.contains (hinterval ht)))
  let p : ComplexPath := ⟨φ γ.path.a, φ γ.path.b, hab, g, hg.continuousOn⟩
  let η : PiecewiseC1Path := ⟨p, ⟨C1Partition.single p hg⟩⟩
  have hφin : MapsTo φ (Icc γ.path.a γ.path.b) (Icc η.path.a η.path.b) :=
    fun t ht => ⟨hm ha ht ht.1, hm ht hb ht.2⟩
  have htrace : η.trace = γ.trace := by
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      obtain ⟨u, hu, hut⟩ := hsurj ht
      exact ⟨u, hu, (he u hu).symm.trans (congrArg g hut)⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨φ t, hφin ht, he t ht⟩
  refine ⟨φ, η, hc, hm, rfl, rfl, (fun _ _ => rfl), htrace, ?_, ?_, ?_⟩
  · exact .monotone η γ φ (htrace ▸ hU) hc hm hφin hsurj
      ⟨γ.partition.count, γ.partition.node, γ.partition.strictMono,
        γ.partition.first, γ.partition.last, hφsmooth⟩ (fun t ht => (he t ht).symm)
  · intro d
    apply path_patches_regular o P s hP η d hinterval
    intro t ht
    exact planeCoordinates.apply_symm_apply _
  · intro hlt t ht
    exact (regular_piece_interval_curve o P s hP _ _ hlt hinterval t ht).2

/-- Any actual interval patch of a path agrees geometrically, up to finitely
many partition endpoints, with its canonical C1 interval patches. This also
includes a degenerate original interval and its empty canonical partition. -/
theorem path_patch_interval_equivalent {O : Set (E 2)}
    (P : Patch 1 O) (γ : PiecewiseC1Path) (d : PathPatchData O γ)
    (hregion : P.region = carrier (intervalBox γ.path.a γ.path.b γ.path.ordered))
    (hmap : ∀ t ∈ Icc γ.path.a γ.path.b, P.map (scalarPoint t) = planeCoordinates (γ t)) :
    PatchEquivalentOffFinite
      (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
      (∑ i, Finsupp.single
        (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
  classical
  have hscalar (u : E 1) : scalarPoint (u 0) = u := by
    ext j
    fin_cases j
    rfl
  let R (i : Fin γ.partition.count) := (d.patch i).region
  have hR : ∀ i, Jordan (R i) := fun i => (d.patch i).jordan
  have hmem (i : Fin γ.partition.count) (u : E 1) :
      u ∈ R i ↔ u 0 ∈ γ.partition.pieceSet i := by
    rw [show R i = _ from d.region i]
    constructor
    · exact fun hu => hu 0
    · intro hu j
      fin_cases j
      exact hu
  have hsub : ∀ i, R i ⊆ P.region := by
    intro i u hu
    rw [hregion]
    intro j
    fin_cases j
    exact γ.partition.piece_subset i ((hmem i u).mp hu)
  let Z : Set (E 1) := scalarPoint '' Set.range γ.partition.node
  have hZ : Z.Finite := (Set.finite_range γ.partition.node).image scalarPoint
  have hnode (j : Fin (γ.partition.count + 1)) (u : E 1)
      (he : u 0 = γ.partition.node j) : u ∈ Z :=
    ⟨γ.partition.node j, ⟨j, rfl⟩, by rw [← he, hscalar]⟩
  have hcover : P.region \ Z ⊆ ⋃ i, R i := by
    intro u hu
    have hut : u 0 ∈ Icc γ.path.a γ.path.b := by
      rw [hregion] at hu
      exact hu.1 0
    have hlast : u 0 < γ.partition.node (Fin.last γ.partition.count) := by
      rw [γ.partition.last]
      apply lt_of_le_of_ne hut.2
      intro he
      exact hu.2 (hnode _ u (he.trans γ.partition.last.symm))
    have hex : ∃ j, u 0 < γ.partition.node j := ⟨_, hlast⟩
    let j := Fin.find (fun j => u 0 < γ.partition.node j) hex
    have hj : j ≠ 0 := by
      intro he
      have hlt := Fin.find_spec hex
      change u 0 < γ.partition.node j at hlt
      rw [he, γ.partition.first] at hlt
      exact (not_lt_of_ge hut.1) hlt
    obtain ⟨i, hij⟩ := Fin.exists_succ_eq_of_ne_zero hj
    refine mem_iUnion.mpr ⟨i, (hmem i u).mpr ⟨?_, ?_⟩⟩
    · exact le_of_not_gt (Fin.find_min hex (show i.castSucc < j from
        hij ▸ Fin.castSucc_lt_succ))
    · have hs := Fin.find_spec hex
      change u 0 < γ.partition.node j at hs
      rw [← hij] at hs
      exact hs.le
  have hpair : ∀ i j, i ≠ j → R i ∩ R j ⊆ Z := by
    intro i j hij u hu
    have hi := (hmem i u).mp hu.1
    have hj := (hmem j u).mp hu.2
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hle := γ.partition.strictMono.monotone
        (Fin.succ_le_castSucc_iff.mpr hlt)
      exact hnode i.succ u (le_antisymm hi.2 (hle.trans hj.1))
    · have hle := γ.partition.strictMono.monotone
        (Fin.succ_le_castSucc_iff.mpr hlt)
      exact hnode j.succ u (le_antisymm hj.2 (hle.trans hi.1))
  apply (PatchEquivalentOffFinite.cover
    (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
    γ.partition.count R hR hsub Z hZ hcover hpair).trans
  apply PatchEquivalentOffFinite.sum
  intro i _
  apply PatchEquivalentOffFinite.geometric
  apply GeometricEquivalent.representative
  · rfl
  · intro u hu
    rw [← hscalar u]
    exact (hmap _ (γ.partition.piece_subset i ((hmem i u).mp hu))).trans
      (d.map i _ ((hmem i u).mp hu)).symm
  · intro _ _
    rfl

open Specs.D04.C15.FinitePiecewiseStokes.Model

/-- The actual cell face occurrence assembly cancels its supplied internal
pairs as geometric chains, without using a Green or line-integral identity. -/

theorem cell_boundary_assembly_equivalent {O : Set (E 2)} (d : CellGreenData O) :
    PatchEquivalentOffFinite (∑ j, patchBoundary (d.face j)) d.outerChain := by
  classical
  have hp (i : Fin d.pairCount) :
      PatchEquivalentOffFinite (Finsupp.single (d.left i) 1 -
        d.direction i • Finsupp.single (d.right i) 1) 0 := by
    obtain ⟨h, hm⟩ := d.reparam i
    have he : PatchEquivalentOffFinite (Finsupp.single (d.left i) 1)
        (d.direction i • Finsupp.single (d.right i) 1) :=
      .geometric (.reparam _ _ _ (d.direction_sign i) h hm (d.weights i))
    have hz := he.add ((PatchEquivalentOffFinite.refl
      (d.direction i • Finsupp.single (d.right i) 1)).zsmul (-1))
    convert hz using 1 <;> simp [sub_eq_add_neg]
  have hsum : PatchEquivalentOffFinite
      (∑ i, d.multiplicity i • (Finsupp.single (d.left i) 1 -
        d.direction i • Finsupp.single (d.right i) 1)) 0 := by
    simpa only [Finset.sum_const_zero] using
      (PatchEquivalentOffFinite.sum Finset.univ _ (fun _ => 0)
        (fun i _ => by simpa only [smul_zero] using (hp i).zsmul (d.multiplicity i)))
  have hass : PatchEquivalentOffFinite (∑ j, patchBoundary (d.face j))
      (d.outerChain + ∑ i, d.multiplicity i • (Finsupp.single (d.left i) 1 -
        d.direction i • Finsupp.single (d.right i) 1)) := by
    simpa only [one_smul] using PatchEquivalentOffFinite.geometric d.assembly
  exact hass.trans (by simpa only [add_zero] using (PatchEquivalentOffFinite.refl d.outerChain).add hsum)

/-- A supplied interval patch has a canonical PC1 traversal, and every
choice of its path patches gives the same geometric boundary contribution. -/
theorem interval_patch_path_exists (U : Set ℂ)
    (P : Patch 1 (planeCoordinates.symm ⁻¹' U))
    (a b : ℝ) (hab : a ≤ b)
    (hregion : P.region = carrier (intervalBox a b hab)) :
    ∃ γ : PiecewiseC1Path, γ.path.a = a ∧ γ.path.b = b ∧
      (∀ t ∈ Icc a b, γ t = planeCoordinates.symm (P.map (scalarPoint t))) ∧
      γ.trace ⊆ U ∧
      ∀ d : PathPatchData (planeCoordinates.symm ⁻¹' U) γ,
        PatchEquivalentOffFinite
          (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
            (planeCoordinates.symm ⁻¹' U)) 1)
          (∑ i, Finsupp.single
            (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
              (planeCoordinates.symm ⁻¹' U)) 1) := by
  have hin : MapsTo scalarPoint (Icc a b) P.region := by
    intro t ht
    rw [hregion]
    intro j
    fin_cases j
    exact ht
  have hscalar : ContDiff ℝ 1 scalarPoint := by
    have heq : scalarPoint = fun t : ℝ => t • standardBasis 1 0 :=
      funext scalarPoint_eq_smul
    rw [heq]
    exact contDiff_id.smul contDiff_const
  let g : ℝ → ℂ := fun t => planeCoordinates.symm (P.map (scalarPoint t))
  have hg : ContDiffOn ℝ 1 g (Icc a b) :=
    planeCoordinates.symm.contDiff.comp_contDiffOn
      (P.regular.comp hscalar.contDiffOn
        (fun t ht => P.contains (subset_closure (hin ht))))
  let p : ComplexPath := ⟨a, b, hab, g, hg.continuousOn⟩
  let γ : PiecewiseC1Path := ⟨p, ⟨C1Partition.single p hg⟩⟩
  refine ⟨γ, rfl, rfl, (fun _ _ => rfl), ?_, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    exact P.mapsTo (P.contains (subset_closure (hin ht)))
  · intro d
    apply path_patch_interval_equivalent P γ d hregion
    intro t ht
    exact (planeCoordinates.apply_symm_apply _).symm

/-- Construct the entire canonical contour display of the supplied cell
boundary, including its integer face signs and geometric internal cancellation.
No comparison with a separately given original contour is assumed here. -/
theorem cell_boundary_contour_exists (U : Set ℂ) (hU : IsOpen U)
    (d : CellGreenData (planeCoordinates.symm ⁻¹' U)) :
    ∃ (C : IntegralChain) (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C),
      (∀ k, (c.path k).trace ⊆ U) ∧
      PatchEquivalentOffFinite d.outerChain c.patchChain := by
  classical
  have hex (j : Fin d.count) (i : Fin 2) (ε : Bool) :=
    interval_patch_path_exists U (d.face j i ε) 0 1 zero_le_one (by
      rw [(d.faces j i ε).1]
      rfl)
  choose γ hleft hright hmap hin hgeom using hex
  let pd (j : Fin d.count) (i : Fin 2) (ε : Bool) :=
    Classical.choice (path_patch_exists U (γ j i ε) hU (hin j i ε))
  let T (j : Fin d.count) (i : Fin 2) (ε : Bool) :
      PatchChain 1 (planeCoordinates.symm ⁻¹' U) :=
    ∑ k, Finsupp.single
      (⟨(pd j i ε).patch k, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
        (planeCoordinates.symm ⁻¹' U)) 1
  have hface (j : Fin d.count) (i : Fin 2) (ε : Bool) :
      PatchEquivalentOffFinite
        (Finsupp.single (plainPatch (d.face j i ε)) 1) (T j i ε) :=
    hgeom j i ε (pd j i ε)
  let I := Fin d.count × Fin 2 × Bool
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let path (k : Fin n) := γ (e k).1 (e k).2.1 (e k).2.2
  let mult (k : Fin n) : ℤ := (-1) ^ ((e k).2.1).val * (if (e k).2.2 then 1 else -1)
  let C : IntegralChain := ∑ k, Finsupp.single (path k) (mult k)
  let c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C := {
    count := n
    path := path
    multiplicity := mult
    chain_eq := rfl
    pieces := fun k => pd (e k).1 (e k).2.1 (e k).2.2 }
  have hc : c.patchChain = ∑ j, ∑ i, (-1 : ℤ) ^ i.val •
      (T j i true - T j i false) := by
    change (∑ k, mult k • T (e k).1 (e k).2.1 (e k).2.2) = _
    change (∑ k, ((-1 : ℤ) ^ ((e k).2.1).val *
      (if (e k).2.2 then 1 else -1)) • T (e k).1 (e k).2.1 (e k).2.2) = _
    rw [e.sum_comp (fun x : I => ((-1 : ℤ) ^ x.2.1.val *
      (if x.2.2 then 1 else -1)) • T x.1 x.2.1 x.2.2)]
    dsimp only [I]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true,
      ite_false, mul_one, mul_neg, neg_smul, sub_eq_add_neg, smul_add, smul_neg]
  have hcells : PatchEquivalentOffFinite (∑ j, patchBoundary (d.face j)) c.patchChain := by
    rw [hc]
    apply PatchEquivalentOffFinite.sum
    intro j _
    unfold patchBoundary
    apply PatchEquivalentOffFinite.sum
    intro i _
    simpa only [sub_eq_add_neg, neg_one_zsmul] using
      ((hface j i true).add ((hface j i false).zsmul (-1))).zsmul ((-1 : ℤ) ^ i.val)
  exact ⟨C, c, (fun k => hin (e k).1 (e k).2.1 (e k).2.2),
    (cell_boundary_assembly_equivalent d).symm.trans hcells⟩

/-- Monotonicity on the closed cells of a finite ordered subdivision glues
across its joints. Repeated nodes and the empty degenerate subdivision are allowed. -/
theorem monotoneOn_of_finite_pieces (f : ℝ → ℝ) (n : ℕ)
    (node : Fin (n + 1) → ℝ) (hnode : Monotone node)
    (hpieces : ∀ i : Fin n, MonotoneOn f (Icc (node i.castSucc) (node i.succ))) :
    MonotoneOn f (Icc (node 0) (node (Fin.last n))) := by
  induction n with
  | zero =>
    intro x hx y hy hxy
    have hx' : x = node 0 := le_antisymm hx.2 hx.1
    have hy' : y = node 0 := le_antisymm hy.2 hy.1
    simp [hx', hy']
  | succ n ih =>
    have hp := ih (fun i => node i.castSucc)
      (fun _ _ h => hnode (by simpa using h)) (fun i => hpieces i.castSucc)
    have hl := hpieces (Fin.last n)
    let c := node (Fin.last n).castSucc
    have hfirst : node 0 ≤ c := hnode (Fin.zero_le _)
    have hlast : c ≤ node (Fin.last (n + 1)) := hnode (Fin.le_last _)
    intro x hx y hy hxy
    by_cases hxc : x ≤ c
    · by_cases hyc : y ≤ c
      · exact hp ⟨hx.1, hxc⟩ ⟨hy.1, hyc⟩ hxy
      · exact (hp ⟨hx.1, hxc⟩ ⟨hfirst, le_rfl⟩ hxc).trans
          (hl ⟨le_rfl, hlast⟩ ⟨(le_of_not_ge hyc), hy.2⟩ (le_of_not_ge hyc))
    · exact hl ⟨le_of_not_ge hxc, hx.2⟩
        ⟨(le_of_not_ge hxc).trans hxy, hy.2⟩ hxy

/-- A scalar function which is C1 on the actual smooth pieces of a path and
has nonnegative derivative in their interiors is nondecreasing on the full
parameter interval. Corners need not be differentiability points. -/
theorem parameter_monotone_of_deriv_nonneg (γ : PiecewiseC1Path) (φ : ℝ → ℝ)
    (hsmooth : ∀ i : Fin γ.partition.count, ContDiffOn ℝ 1 φ (γ.partition.pieceSet i))
    (hpositive : ∀ i : Fin γ.partition.count, ∀ t ∈ Ioo (γ.partition.node i.castSucc)
      (γ.partition.node i.succ), 0 ≤ deriv φ t) :
    MonotoneOn φ (Icc γ.path.a γ.path.b) := by
  rw [← γ.partition.first, ← γ.partition.last]
  apply monotoneOn_of_finite_pieces φ _ _ γ.partition.strictMono.monotone
  intro i
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hsmooth i).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    exact ((hsmooth i).contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
      (by decide) |>.differentiableWithinAt
  · simpa only [interior_Icc] using hpositive i

/-- An injective compact reference arc gives a continuous onto parameter for
any PC1 path with the same trace, before orientation or smoothness is imposed. -/
theorem arc_parameter_exists (γ η : PiecewiseC1Path)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b) := by
  classical
  let φ : ℝ → ℝ := fun t => Function.invFunOn γ (Icc γ.path.a γ.path.b) (η t)
  have hex (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) :
      ∃ s ∈ Icc γ.path.a γ.path.b, γ s = η t := by
    have hm : η t ∈ η.trace := ⟨t, ht, rfl⟩
    rw [htrace] at hm
    exact hm
  have hmaps : MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) :=
    fun t ht => Function.invFunOn_mem (hex t ht)
  have he (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) : γ (φ t) = η t :=
    Function.invFunOn_eq (hex t ht)
  have hc : ContinuousOn φ (Icc η.path.a η.path.b) := by
    let F : Icc η.path.a η.path.b → Icc γ.path.a γ.path.b :=
      fun t => ⟨φ t, hmaps t.property⟩
    have hEmb := γ.path.continuousOn.domRestrict.isClosedEmbedding hinj.injective
    have hFc : Continuous F := hEmb.isEmbedding.continuous_iff.mpr (by
      convert η.path.continuousOn.domRestrict using 1
      funext t
      exact he t t.property)
    exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hFc)
  refine ⟨φ, hc, hmaps, ?_, fun t ht => (he t ht).symm⟩
  intro s hs
  have hm : γ s ∈ η.trace := htrace.symm ▸ (show γ s ∈ γ.trace from ⟨s, hs, rfl⟩)
  obtain ⟨t, ht, heq⟩ := hm
  exact ⟨t, ht, hinj (hmaps ht) hs ((he t ht).trans heq)⟩

/-- Positive tangent direction forces an arbitrary PC1 traversal of a regular
embedded arc to respect its order. Zero tangent vectors and whole pauses are
allowed. No order of visits or scalar parameter is assumed. -/
theorem directed_regular_arc_parameter_exists
    (γ η : PiecewiseC1Path) (g : ℝ → ℂ)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace)
    (hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (hγ : EqOn γ g (Icc γ.path.a γ.path.b))
    (hdirection : ∀ i : Fin η.partition.count, ∀ t ∈ Ioo (η.partition.node i.castSucc)
      (η.partition.node i.succ), ∀ s ∈ Icc γ.path.a γ.path.b,
        γ s = η t → ∃ c : ℝ, 0 ≤ c ∧ deriv η t = c • deriv g s) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MonotoneOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b) := by
  obtain ⟨φ, hc, hmaps, hsurj, he⟩ := arc_parameter_exists γ η hinj htrace
  have he' : EqOn η (fun t => g (φ t)) (Icc η.path.a η.path.b) :=
    fun t ht => (he ht).trans (hγ (hmaps ht))
  have hsmooth (i : Fin η.partition.count) :
      ContDiffOn ℝ 1 φ (η.partition.pieceSet i) :=
    recover_parameter_contDiffOn η g φ _ (η.partition.smooth i)
      (hc.mono (η.partition.piece_subset i))
      (fun t ht => hg _ (hmaps (η.partition.piece_subset i ht)))
      (fun t ht => hv _ (hmaps (η.partition.piece_subset i ht)))
      (he'.mono (η.partition.piece_subset i))
  refine ⟨φ, hc, parameter_monotone_of_deriv_nonneg η φ hsmooth ?_, hmaps, hsurj, he⟩
  intro i t ht
  have htcc : t ∈ η.partition.pieceSet i := ⟨ht.1.le, ht.2.le⟩
  have htall := η.partition.piece_subset i htcc
  have hdφ := ((hsmooth i).contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
    (by decide)
  have hdg := (hg _ (hmaps htall)).differentiableAt (by decide)
  have heq : η =ᶠ[nhds t] (fun u => g (φ u)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    exact he' (η.partition.piece_subset i hu)
  have hderiv : deriv η t = deriv φ t • deriv g (φ t) :=
    heq.deriv_eq.trans (deriv.scomp t hdg hdφ)
  obtain ⟨c, hcpos, hec⟩ := hdirection i t ht (φ t) (hmaps htall) (he htall).symm
  have hscalar : deriv φ t = c := (smul_left_injective ℝ (hv _ (hmaps htall)))
    (hderiv.symm.trans hec)
  rwa [hscalar]

/-- The local comparison needed by Green follows from a geometric positive
tangent condition, with the scalar parameter and its order both derived. -/
theorem directed_regular_arc_contour_equivalent (U : Set ℂ)
    (γ η : PiecewiseC1Path) (g : ℝ → ℂ) (hin : γ.trace ⊆ U)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace)
    (hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (hγ : EqOn γ g (Icc γ.path.a γ.path.b))
    (hdirection : ∀ i : Fin η.partition.count, ∀ t ∈ Ioo (η.partition.node i.castSucc)
      (η.partition.node i.succ), ∀ s ∈ Icc γ.path.a γ.path.b,
        γ s = η t → ∃ c : ℝ, 0 ≤ c ∧ deriv η t = c • deriv g s) :
    ContourEquivalentOn U (Finsupp.single η 1) (Finsupp.single γ 1) := by
  obtain ⟨φ, hc, hm, hmaps, hsurj, he⟩ :=
    directed_regular_arc_parameter_exists γ η g hinj htrace hg hv hγ hdirection
  exact regular_monotone_contour_equivalent U γ η φ g hin hc hm hmaps hsurj hg hv hγ he

/-- Replace a directed traversal in an injective regular chart by one actual
interval patch. Its image is the original trace even if that traversal pauses;
the new patch itself is injective and keeps the original induced sign. -/
theorem ordered_regular_piece_interval_display {M : Set (E 2)}
    (U : Set ℂ) (o : PositiveManifoldOrientation 1 1 M)
    (P : Patch 1 (planeCoordinates.symm ⁻¹' U)) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (horder : ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b,
      x ≤ y → ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0) :
    ∃ (η : PiecewiseC1Path) (Q : Patch 1 (planeCoordinates.symm ⁻¹' U)),
      ContourEquivalentOn U (Finsupp.single γ 1) (Finsupp.single η 1) ∧
      η.trace ⊆ U ∧ RegularPiece o Q s ∧ InjOn Q.map Q.region ∧
      Q.map '' Q.region = planeCoordinates '' γ.trace ∧
      ∀ d : PathPatchData (planeCoordinates.symm ⁻¹' U) η,
        PatchEquivalentOffFinite
          (Finsupp.single (⟨Q, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
            (planeCoordinates.symm ⁻¹' U)) 1)
          (∑ i, Finsupp.single
            (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
              (planeCoordinates.symm ⁻¹' U)) 1) := by
  obtain ⟨φ, hc, hm, hmaps, he, hsmooth⟩ :=
    ordered_regular_piece_parameter_exists o P s hP γ hinj hin horder
  have ha : γ.path.a ∈ Icc γ.path.a γ.path.b := ⟨le_rfl, γ.path.ordered⟩
  have hb : γ.path.b ∈ Icc γ.path.a γ.path.b := ⟨γ.path.ordered, le_rfl⟩
  have hab : φ γ.path.a ≤ φ γ.path.b := hm ha hb γ.path.ordered
  have hsurj := hc.surjOn_Icc ha hb
  let R := carrier (intervalBox (φ γ.path.a) (φ γ.path.b) hab)
  have hRclosed : IsClosed R := (D04.DiscontinuityCriterion.carrier_compact _).isClosed
  have hRsub : R ⊆ closure P.region := by
    intro u hu
    obtain ⟨t, ht, htu⟩ := hsurj (hu 0)
    have hscalar : scalarPoint (φ t) = u := by
      ext i
      fin_cases i
      exact htu
    exact hscalar ▸ hmaps ht
  let Q : Patch 1 (planeCoordinates.symm ⁻¹' U) := {
    region := R
    jordan := D04.ImproperExhaustions.jordan_box _
    map := P.map
    domain := P.domain
    open_domain := P.open_domain
    contains := by simpa only [hRclosed.closure_eq] using hRsub.trans P.contains
    regular := P.regular
    mapsTo := P.mapsTo }
  have hQr : RegularPiece o Q s := regular_piece_closed_restriction o P Q s hP
    (by simpa only [show Q.region = R from rfl, hRclosed.closure_eq] using hRsub)
    (fun _ _ => rfl)
  obtain ⟨η, hηa, hηb, hηmap, hηin, hηgeom⟩ :=
    interval_patch_path_exists U Q (φ γ.path.a) (φ γ.path.b) hab rfl
  have hφmaps : MapsTo φ (Icc γ.path.a γ.path.b) (Icc η.path.a η.path.b) := by
    rw [hηa, hηb]
    exact fun t ht => ⟨hm ha ht ht.1, hm ht hb ht.2⟩
  have hφonto : SurjOn φ (Icc γ.path.a γ.path.b) (Icc η.path.a η.path.b) := by
    rwa [hηa, hηb]
  have htraversal : ContourEquivalentOn U (Finsupp.single γ 1) (Finsupp.single η 1) := by
    refine .monotone η γ φ hηin hc hm hφmaps hφonto
      ⟨γ.partition.count, γ.partition.node, γ.partition.strictMono,
        γ.partition.first, γ.partition.last, hsmooth⟩ ?_
    intro t ht
    change γ t = η (φ t)
    rw [hηmap _ (by simpa only [hηa, hηb] using hφmaps ht)]
    exact (he t ht).symm
  refine ⟨η, Q, htraversal, hηin, hQr, hinj.mono hRsub, ?_, hηgeom⟩
  apply Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    obtain ⟨t, ht, hut⟩ := hsurj (hu 0)
    have hscalar : scalarPoint (φ t) = u := by
      ext i
      fin_cases i
      exact hut
    refine ⟨γ t, ⟨t, ht, rfl⟩, ?_⟩
    rw [← hscalar]
    exact (congrArg planeCoordinates (he t ht)).symm.trans
      (planeCoordinates.apply_symm_apply _)
  · rintro z ⟨w, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨scalarPoint (φ t), ?_, ?_⟩
    · intro i
      fin_cases i
      exact ⟨hm ha ht ht.1, hm ht hb ht.2⟩
    · exact (planeCoordinates.apply_symm_apply _).symm.trans
        (congrArg planeCoordinates (he t ht))

/-- Finite contour comparisons retain every integer multiplicity. -/
theorem ContourEquivalentOn.sum {U : Set ℂ} {ι : Type*}
    (S : Finset ι) (C D : ι → IntegralChain)
    (h : ∀ i ∈ S, ContourEquivalentOn U (C i) (D i)) :
    ContourEquivalentOn U (∑ i ∈ S, C i) (∑ i ∈ S, D i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ContourEquivalentOn.refl (U := U) 0
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- A finite family of original directed chart traversals with actual geometric
coverage and overlap data constructs a regular boundary display and its contour
comparison. Pauses require no self-overlap hypothesis on the original paths. -/
theorem regular_boundary_display_of_ordered_arcs {M : Set (E 2)}
    (U : Set ℂ) (hU : IsOpen U) (o : PositiveManifoldOrientation 1 1 M)
    (n : ℕ) (γ : Fin n → PiecewiseC1Path)
    (P : Fin n → Patch 1 (planeCoordinates.symm ⁻¹' U)) (s : Fin n → PointSign)
    (hP : ∀ i, RegularPiece o (P i) (s i))
    (hinj : ∀ i, InjOn (P i).map (closure (P i).region))
    (hin : ∀ i, planeCoordinates '' (γ i).trace ⊆ (P i).map '' closure (P i).region)
    (horder : ∀ i, ∀ x ∈ Icc (γ i).path.a (γ i).path.b,
      ∀ y ∈ Icc (γ i).path.a (γ i).path.b, x ≤ y →
      ∀ u ∈ closure (P i).region, ∀ v ∈ closure (P i).region,
        (P i).map u = planeCoordinates (γ i x) →
        (P i).map v = planeCoordinates (γ i y) → u 0 ≤ v 0)
    (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1)
    (hoverlap : ∀ i j, i ≠ j →
      (planeCoordinates '' (γ i).trace) ∩ (planeCoordinates '' (γ j).trace) ⊆ Z.carrier)
    (hcover : M ⊆ (⋃ i, planeCoordinates '' (γ i).trace) ∪ Z.carrier) :
    ∃ (e : RegularBoundaryDisplay (O := planeCoordinates.symm ⁻¹' U) o)
      (C : IntegralChain) (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C),
      ContourEquivalentOn U (∑ i, (orientationInteger (s i)) • Finsupp.single (γ i) 1) C ∧
      (∀ i, (c.path i).trace ⊆ U) ∧
      PatchEquivalentOffFinite e.patchChain c.patchChain := by
  classical
  have hex (i : Fin n) := ordered_regular_piece_interval_display U o (P i) (s i)
    (hP i) (γ i) (hinj i) (hin i) (horder i)
  choose η Q htr hηin hQr hQinj hQimage hQgeom using hex
  let e : RegularBoundaryDisplay (O := planeCoordinates.symm ⁻¹' U) o := {
    count := n
    patch := Q
    sign := s
    regular := hQr
    seams := Z
    seamsDim := hdim
    repeats := by
      intro i u hu v hv huv heq
      exact (huv (hQinj i hu hv heq)).elim
    overlap := by
      intro i j hij
      rw [hQimage i, hQimage j]
      exact hoverlap i j hij
    cover := by simpa only [hQimage] using hcover }
  let pd (i : Fin n) := Classical.choice (path_patch_exists U (η i) hU (hηin i))
  let C : IntegralChain := ∑ i, (orientationInteger (s i)) • Finsupp.single (η i) 1
  let c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C := {
    count := n
    path := η
    multiplicity := fun i => orientationInteger (s i)
    chain_eq := by simp only [C, Finsupp.smul_single, smul_eq_mul, mul_one]
    pieces := pd }
  refine ⟨e, C, c, ?_, hηin, ?_⟩
  · exact ContourEquivalentOn.sum Finset.univ _ _
      (fun i _ => (htr i).zsmul (orientationInteger (s i)))
  · unfold RegularBoundaryDisplay.patchChain ContourPatchData.patchChain
    apply PatchEquivalentOffFinite.sum
    intro i _
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
      (hQgeom i (pd i)).zsmul (orientationInteger (s i))

/-- On an injective regular Jordan patch, the original nonnegative tangent
condition determines the order of visits. The full parameter range of a
continuous traversal is an interval, even when the patch region is disconnected. -/
theorem regular_piece_order_of_tangent {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (hdirection : ∀ i : Fin γ.partition.count,
      ∀ t ∈ Ioo (γ.partition.node i.castSucc) (γ.partition.node i.succ),
      ∀ u ∈ closure P.region, P.map u = planeCoordinates (γ t) →
        ∃ c : ℝ, 0 ≤ c ∧ deriv γ t =
          c • deriv (fun v => planeCoordinates.symm (P.map (scalarPoint v))) (u 0)) :
    ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b, x ≤ y →
      ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0 := by
  obtain ⟨ψ, hψc, hψmaps, hψe⟩ := patch_parameter_exists P γ hinj hin
  let φ : ℝ → ℝ := fun t => ψ t 0
  have heval : ContDiff ℝ 1 (fun u : E 1 => u 0) :=
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).comp
      (coordinates 1).toContinuousLinearEquiv.contDiff
  have hc : ContinuousOn φ (Icc γ.path.a γ.path.b) :=
    heval.continuous.comp_continuousOn hψc
  have hscalar (u : E 1) : scalarPoint (u 0) = u := by
    ext i
    fin_cases i
    rfl
  have he : EqOn γ (fun t => planeCoordinates.symm (P.map (scalarPoint (φ t))))
      (Icc γ.path.a γ.path.b) := by
    intro t ht
    dsimp only [φ]
    rw [hscalar, hψe t ht, coordinates_symm]
  have hsmooth (i : Fin γ.partition.count) : ContDiffOn ℝ 1 φ (γ.partition.pieceSet i) := by
    apply heval.comp_contDiffOn
    apply regular_piece_recover_parameter o P s hP γ ψ (γ.partition.pieceSet i)
      (γ.partition.smooth i) (hψc.mono (γ.partition.piece_subset i))
      (hψmaps.mono (γ.partition.piece_subset i) Subset.rfl)
    intro t ht
    simpa only [coordinates_symm] using
      (congrArg planeCoordinates.symm (hψe t (γ.partition.piece_subset i ht))).symm
  have hne : (Icc γ.path.a γ.path.b).Nonempty := nonempty_Icc.mpr γ.path.ordered
  obtain ⟨l, hl, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  have hbounds (t) (ht : t ∈ Icc γ.path.a γ.path.b) : φ t ∈ Icc (φ l) (φ r) :=
    ⟨hmin ht, hmax ht⟩
  have hm : MonotoneOn φ (Icc γ.path.a γ.path.b) := by
    by_cases heq : φ l = φ r
    · intro x hx y hy _
      exact (hbounds x hx).2.trans (heq ▸ (hbounds y hy).1)
    have hlt : φ l < φ r := lt_of_le_of_ne (hmin hr) heq
    have hinterval : MapsTo scalarPoint (Icc (φ l) (φ r)) (closure P.region) := by
      intro u hu
      obtain ⟨t, ht, htu⟩ := isPreconnected_Icc.intermediate_value hl hr hc hu
      rw [← htu, show scalarPoint (φ t) = ψ t from hscalar _]
      exact hψmaps ht
    let g : ℝ → ℂ := fun v => planeCoordinates.symm (P.map (scalarPoint v))
    have hg (t) (ht : t ∈ Icc γ.path.a γ.path.b) :=
      regular_piece_interval_curve o P s hP _ _ hlt hinterval (φ t) (hbounds t ht)
    apply parameter_monotone_of_deriv_nonneg γ φ hsmooth
    intro i t ht
    have htcc : t ∈ γ.partition.pieceSet i := ⟨ht.1.le, ht.2.le⟩
    have htall := γ.partition.piece_subset i htcc
    have hdφ := ((hsmooth i).contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
      (by decide)
    have heq : γ =ᶠ[nhds t] (fun v => g (φ v)) := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with v hv
      exact he (γ.partition.piece_subset i hv)
    have hd : deriv γ t = deriv φ t • deriv g (φ t) :=
      heq.deriv_eq.trans (deriv.scomp t ((hg t htall).1.differentiableAt (by decide)) hdφ)
    obtain ⟨c, hcpos, hdc⟩ := hdirection i t ht (ψ t) (hψmaps htall) (hψe t htall)
    have hdc' : deriv γ t = c • deriv g (φ t) := hdc
    have hec : deriv φ t = c := (smul_left_injective ℝ (hg t htall).2)
      (hd.symm.trans hdc')
    rwa [hec]
  intro x hx y hy hxy u hu v hv hue hve
  have hxu : ψ x = u := hinj (hψmaps hx) hu ((hψe x hx).trans hue.symm)
  have hyv : ψ y = v := hinj (hψmaps hy) hv ((hψe y hy).trans hve.symm)
  simpa only [φ, hxu, hyv] using hm hx hy hxy

/-- Finite directed regular-chart traversals construct their own boundary
display. The scalar order premise of the preceding construction follows from
the tangent directions of the original PC1 paths, with no speed lower bound. -/
theorem regular_boundary_display_of_directed_arcs {M : Set (E 2)}
    (U : Set ℂ) (hU : IsOpen U) (o : PositiveManifoldOrientation 1 1 M)
    (n : ℕ) (γ : Fin n → PiecewiseC1Path)
    (P : Fin n → Patch 1 (planeCoordinates.symm ⁻¹' U)) (s : Fin n → PointSign)
    (hP : ∀ i, RegularPiece o (P i) (s i))
    (hinj : ∀ i, InjOn (P i).map (closure (P i).region))
    (hin : ∀ i, planeCoordinates '' (γ i).trace ⊆ (P i).map '' closure (P i).region)
    (hdirection : ∀ j, ∀ i : Fin (γ j).partition.count,
      ∀ t ∈ Ioo ((γ j).partition.node i.castSucc) ((γ j).partition.node i.succ),
      ∀ u ∈ closure (P j).region, (P j).map u = planeCoordinates (γ j t) →
        ∃ c : ℝ, 0 ≤ c ∧ deriv (γ j) t = c • deriv
          (fun v => planeCoordinates.symm ((P j).map (scalarPoint v))) (u 0))
    (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1)
    (hoverlap : ∀ i j, i ≠ j →
      (planeCoordinates '' (γ i).trace) ∩ (planeCoordinates '' (γ j).trace) ⊆ Z.carrier)
    (hcover : M ⊆ (⋃ i, planeCoordinates '' (γ i).trace) ∪ Z.carrier) :
    ∃ (e : RegularBoundaryDisplay (O := planeCoordinates.symm ⁻¹' U) o)
      (C : IntegralChain) (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C),
      ContourEquivalentOn U (∑ i, (orientationInteger (s i)) • Finsupp.single (γ i) 1) C ∧
      (∀ i, (c.path i).trace ⊆ U) ∧
      PatchEquivalentOffFinite e.patchChain c.patchChain := by
  apply regular_boundary_display_of_ordered_arcs U hU o n γ P s hP hinj hin
    (fun i => regular_piece_order_of_tangent o (P i) (s i) (hP i) (γ i)
      (hinj i) (hin i) (hdirection i)) Z hdim hoverlap hcover

/-- Select finitely many actual embedded charts from local regularity, then
localize the Jordan parameter region inside their open neighborhoods. Closed-set
injectivity follows from each selected chart's left inverse. The original
parametrization and its induced sign are retained exactly. -/
theorem regular_piece_injective_localization {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) :
    ∃ (m : ℕ) (Q : Fin m → Patch 1 O)
      (c : Fin m → EmbeddedChart 1 1 2 M),
      P.region = ⋃ i, (Q i).region ∧
      (Pairwise fun i j => Disjoint (Q i).region (Q j).region) ∧
      (∀ i, (Q i).region ⊆ P.region) ∧
      (∀ i, EqOn (Q i).map P.map (closure (Q i).region)) ∧
      (∀ i, RegularPiece o (Q i) s) ∧
      (∀ i, closure (Q i).region ⊆ (c i).source) ∧
      (∀ i, EqOn (Q i).map (c i).toFun (closure (Q i).region)) ∧
      (∀ i, ∀ v : (c i).source,
        chartSign o.atPoint (c i) v v.property = s.val) ∧
      (∀ i, InjOn (Q i).map (closure (Q i).region)) ∧
      GeometricEquivalent
        (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
        (∑ i, Finsupp.single
          (⟨Q i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1) := by
  classical
  choose V c hV huV hsource hmap hsign using
    (fun u : closure P.region => hP u u.property)
  obtain ⟨m, a, R, hR, hsub, hclose, hpair, hcover⟩ :=
    D04.GeometricPatches.jordan_localization P.region P.jordan V hV
      (fun u hu => mem_iUnion.mpr ⟨⟨u, hu⟩, huV ⟨u, hu⟩⟩)
  let Q (i : Fin m) : Patch 1 O := restrictPatch P (R i) (hR i) (hsub i)
  have hclosed (i : Fin m) : closure (Q i).region ⊆ closure P.region :=
    closure_mono (hsub i)
  have hchart (i : Fin m) : closure (Q i).region ⊆ (c (a i)).source :=
    fun u hu => hsource (a i) ⟨hclosed i hu, hclose i hu⟩
  have he (i : Fin m) : EqOn (Q i).map (c (a i)).toFun (closure (Q i).region) :=
    fun u hu => hmap (a i) ⟨hclosed i hu, hclose i hu⟩
  refine ⟨m, Q, fun i => c (a i), hcover, hpair, hsub, ?_, ?_, hchart, he,
    fun i => hsign (a i), ?_, ?_⟩
  · exact fun _ _ _ => rfl
  · intro i
    exact regular_piece_closed_restriction o P (Q i) s hP (hclosed i)
      (fun _ _ => rfl)
  · intro i u hu v hv huv
    calc
      u = (c (a i)).invFun ((c (a i)).toFun u) :=
        ((c (a i)).left_inv u (hchart i hu)).symm
      _ = (c (a i)).invFun ((c (a i)).toFun v) :=
        congrArg (c (a i)).invFun ((he i hu).symm.trans (huv.trans (he i hv)))
      _ = v := (c (a i)).left_inv v (hchart i hv)
  · let Z : Seams 1 := {
      count := 0
      dim := Fin.elim0
      lower := fun i => Fin.elim0 i
      parameter := fun i => Fin.elim0 i
      compact := fun i => Fin.elim0 i
      map := fun i => Fin.elim0 i
      localC1 := fun i => Fin.elim0 i }
    exact GeometricEquivalent.cover
      (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      m R hR hsub hcover Z (by
        intro i j hij u hu
        exact False.elim (Set.disjoint_left.mp (hpair hij) hu.1 hu.2))

/-- A complete supplied regular display admits a finite replacement by
injective chart pieces. The original seams, cover and induced signs are
preserved, and the signed geometric comparison is proved. -/
theorem regular_boundary_injective_display {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M)
    (d : RegularBoundaryDisplay (O := O) o) :
    ∃ (e : RegularBoundaryDisplay (O := O) o)
      (c : Fin e.count → EmbeddedChart 1 1 2 M),
      e.seams = d.seams ∧
      (∀ i, closure (e.patch i).region ⊆ (c i).source) ∧
      (∀ i, EqOn (e.patch i).map (c i).toFun (closure (e.patch i).region)) ∧
      (∀ i, ∀ v : (c i).source,
        chartSign o.atPoint (c i) v v.property = (e.sign i).val) ∧
      (∀ i, InjOn (e.patch i).map (closure (e.patch i).region)) ∧
      GeometricEquivalent d.patchChain e.patchChain := by
  classical
  choose m Q c hcover hpair hsub he hreg hsource hmap hsign hinj hgeom using
    (fun i => regular_piece_injective_localization o (d.patch i) (d.sign i) (d.regular i))
  let J := (i : Fin d.count) × Fin (m i)
  let n := Fintype.card J
  let f : Fin n ≃ J := (Fintype.equivFin J).symm
  have himage (i : Fin d.count) (k : Fin (m i)) :
      (Q i k).map '' (Q i k).region ⊆ (d.patch i).map '' (d.patch i).region := by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨u, hsub i k hu, (he i k (subset_closure hu)).symm⟩
  have hoverlap (x y : J) (hxy : x ≠ y) :
      ((Q x.1 x.2).map '' (Q x.1 x.2).region) ∩
        ((Q y.1 y.2).map '' (Q y.1 y.2).region) ⊆ d.seams.carrier := by
    rcases x with ⟨i, k⟩
    rcases y with ⟨j, l⟩
    by_cases hij : i = j
    · subst j
      have hkl : k ≠ l := by intro h; exact hxy (by subst l; rfl)
      rintro z ⟨⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩
      have huv : u ≠ v := by
        intro h
        subst v
        exact Set.disjoint_left.mp (hpair i hkl) hu hv
      have huP := hsub i k hu
      have hvP := hsub i l hv
      have huMap : (d.patch i).map u = z := (he i k (subset_closure hu)).symm.trans huz
      have hvMap : (d.patch i).map v = z := (he i l (subset_closure hv)).symm.trans hvz
      exact huMap ▸ d.repeats i u huP v hvP huv (huMap.trans hvMap.symm)
    · intro z hz
      exact d.overlap i j hij ⟨himage i k hz.1, himage j l hz.2⟩
  let e : RegularBoundaryDisplay (O := O) o := {
    count := n
    patch := fun i => Q (f i).1 (f i).2
    sign := fun i => d.sign (f i).1
    regular := fun i => hreg (f i).1 (f i).2
    seams := d.seams
    seamsDim := d.seamsDim
    repeats := by
      intro i u hu v hv huv huvmap
      exact (huv (hinj (f i).1 (f i).2 (subset_closure hu) (subset_closure hv) huvmap)).elim
    overlap := fun i j hij => hoverlap (f i) (f j) (fun h => hij (f.injective h))
    cover := by
      intro z hz
      rcases d.cover hz with hz | hz
      · left
        obtain ⟨i, u, hu, huz⟩ := mem_iUnion.mp hz
        rw [hcover i] at hu
        obtain ⟨k, huk⟩ := mem_iUnion.mp hu
        refine mem_iUnion.mpr ⟨f.symm ⟨i,k⟩, ?_⟩
        rw [show f (f.symm ⟨i,k⟩) = ⟨i,k⟩ from f.apply_symm_apply _]
        exact ⟨u, huk, (he i k (subset_closure huk)).trans huz⟩
      · exact Or.inr hz }
  refine ⟨e, (fun i => c (f i).1 (f i).2), rfl,
    (fun i => hsource (f i).1 (f i).2),
    (fun i => hmap (f i).1 (f i).2),
    (fun i => hsign (f i).1 (f i).2),
    (fun i => hinj (f i).1 (f i).2), ?_⟩
  have hsum : GeometricEquivalent d.patchChain
      (∑ i, ∑ k, Finsupp.single
        (⟨Q i k, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
        (orientationInteger (d.sign i))) := by
    have hlocal (i : Fin d.count) : GeometricEquivalent
        (Finsupp.single
          (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
          (orientationInteger (d.sign i)))
        (∑ k, Finsupp.single
          (⟨Q i k, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
          (orientationInteger (d.sign i))) := by
      simpa only [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_one] using
        (hgeom i).zsmul (orientationInteger (d.sign i))
    have hfinite (S : Finset (Fin d.count)) : GeometricEquivalent
        (∑ i ∈ S, Finsupp.single
          (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
          (orientationInteger (d.sign i)))
        (∑ i ∈ S, ∑ k, Finsupp.single
          (⟨Q i k, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
          (orientationInteger (d.sign i))) := by
      induction S using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact .refl 0
      | @insert i S hi ih => simpa only [Finset.sum_insert hi] using (hlocal i).add ih
    exact hfinite Finset.univ
  have hreindex : e.patchChain = ∑ i, ∑ k, Finsupp.single
      (⟨Q i k, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      (orientationInteger (d.sign i)) := by
    change (∑ i, Finsupp.single
      (⟨Q (f i).1 (f i).2, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      (orientationInteger (d.sign (f i).1))) = _
    rw [f.sum_comp (fun x : J => Finsupp.single
      (⟨Q x.1 x.2, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
      (orientationInteger (d.sign x.1)))]
    exact Fintype.sum_sigma _
  exact hreindex.symm ▸ hsum

end D12Complex.GreenRegionIndex



namespace D12Complex.GreenRegionIndex
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C06.JordanRegions.Model
open ManifoldBoundaryDensity

/-- Actual D04 Green on the supplied original assembly, with zero density only
on the integration carrier. -/
theorem planar_assembly_circulation_zero_on {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (f g : E 2 → ℝ) (hO : IsOpen O)
    (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hz : ∀ x ∈ ⋃ j, (A.piece j).carrier, circulationDensity f g x = 0) :
    patchChainIntegral (circulationForm f g) (outerPatchChain A) = 0 := by
  have h := D04.Green.riemann_manifold_green A.piece A.ambient_positive
    A.boundaryOrientation A.outward (fun j => (A.display j).count)
    (fun j => (A.display j).patch) (fun j => (A.display j).sign)
    (fun j => (A.display j).regular) (fun j => (A.display j).seams)
    (fun j => (A.display j).lower) (fun j => (A.display j).self_intersection)
    (fun j => (A.display j).intersection) (fun j => (A.display j).cover)
    A.bulkSeams A.bulk_intersection A.enumerate A.outerPatch A.outerSign
    A.outerMultiplicity A.deltaOut A.deltaOut_sign A.outerReparam A.outer_match
    A.deltaPair A.deltaPair_sign A.pairReparam A.pair_match f g hO hf hg
  have he : (fun x : (⋃ j, (A.piece j).carrier) => circulationDensity f g x) =
      fun _ => 0 := by
    funext x
    exact hz x x.property
  have hv := h.2.2.2.1
  rw [he, region_integral_zero] at hv
  rw [outerPatchChain_integral]
  exact hv.symm

/-- The unchanged original cycle has zero contour integral for an ambient C1
field whose CR equations hold only along the compact carrier. -/
theorem planar_assembly_contour_zero_on {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle)
    (hΓ : ManifoldBoundaryContour.FullPositiveBoundary A Γ)
    (Q : ℂ → ℂ) (hQ : ContDiff ℝ 1 Q) (hO : IsOpen O)
    (hhol : ∀ z ∈ complexCoordinates.symm '' (⋃ j, (A.piece j).carrier),
      DifferentiableAt ℂ Q z) :
    Γ.integral Q = 0 := by
  have hc : ContDiff ℝ 1 (fun x : E 2 => Q (complexCoordinates.symm x)) :=
    hQ.comp complexCoordinates.symm.toContinuousLinearEquiv.contDiff
  have hr : CrOn 1 O (fun x => (Q (complexCoordinates.symm x)).re) :=
    (D04.crOn_iff_contDiffOn 1 O _ hO).mpr (Complex.reCLM.contDiff.comp hc).contDiffOn
  have hi : CrOn 1 O (fun x => (Q (complexCoordinates.symm x)).im) :=
    (D04.crOn_iff_contDiffOn 1 O _ hO).mpr (Complex.imCLM.contDiff.comp hc).contDiffOn
  have hn : CrOn 1 O (fun x => -(Q (complexCoordinates.symm x)).im) :=
    (D04.crOn_iff_contDiffOn 1 O _ hO).mpr (Complex.imCLM.contDiff.comp hc).neg.contDiffOn
  have hz (x : E 2) (hx : x ∈ ⋃ j, (A.piece j).carrier) :=
    green_densities_zero Q (complexCoordinates.symm x) (hhol _ ⟨x, hx, rfl⟩)
  have hzr : patchChainIntegral
      (circulationForm (fun x => (Q (complexCoordinates.symm x)).re)
        (fun x => -(Q (complexCoordinates.symm x)).im)) (outerPatchChain A) = 0 := by
    apply planar_assembly_circulation_zero_on A _ _ hO hr hn
    intro x hx
    have hz' := (hz x hx).1
    change circulationDensity (fun y => (Q (complexCoordinates.symm y)).re)
      (fun y => -(Q (complexCoordinates.symm y)).im)
      (complexCoordinates (complexCoordinates.symm x)) = 0 at hz'
    simpa only [LinearEquiv.apply_symm_apply] using hz'
  have hzi : patchChainIntegral
      (circulationForm (fun x => (Q (complexCoordinates.symm x)).im)
        (fun x => (Q (complexCoordinates.symm x)).re)) (outerPatchChain A) = 0 := by
    apply planar_assembly_circulation_zero_on A _ _ hO hi hr
    intro x hx
    have hz' := (hz x hx).2
    change circulationDensity (fun y => (Q (complexCoordinates.symm y)).im)
      (fun y => (Q (complexCoordinates.symm y)).re)
      (complexCoordinates (complexCoordinates.symm x)) = 0 at hz'
    simpa only [LinearEquiv.apply_symm_apply] using hz'
  have hd := ManifoldBoundaryContour.full_positive_boundary_contour A Γ hΓ Q
    hQ.continuous.continuousOn
  simpa only [hzr, hzi, Complex.ofReal_zero, mul_zero, add_zero] using hd

/-- C1 regularity and holomorphy are required only on an arbitrary open
neighborhood of the supplied compact integration carrier. -/
theorem planar_assembly_contour_zero_near {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle)
    (hΓ : ManifoldBoundaryContour.FullPositiveBoundary A Γ) (hO : IsOpen O)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : complexCoordinates.symm '' (⋃ j, (A.piece j).carrier) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hhol : ∀ z ∈ U, DifferentiableAt ℂ f z) :
    Γ.integral f = 0 := by
  have hK : IsCompact (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier)) :=
    (isCompact_iUnion (fun j => (A.piece j).compact)).image
      complexCoordinates.symm.toContinuousLinearEquiv.continuous
  obtain ⟨Q, hQ, V, hV, hKV, hVU, he⟩ :=
    CellBoundaryContour.complex_field_C1_extension _ hK f U hU hKU hf
  have hholQ : ∀ z ∈ complexCoordinates.symm '' (⋃ j, (A.piece j).carrier),
      DifferentiableAt ℂ Q z := by
    intro z hz
    exact (hhol z (hKU hz)).congr_of_eventuallyEq
      (he.eventuallyEq_of_mem (hV.mem_nhds (hKV hz)))
  have hzero := planar_assembly_contour_zero_on A Γ hΓ Q hQ hO hholQ
  have hcongr : Γ.integral Q = Γ.integral f :=
    chain_integral_congr_on Γ.chain Q f (he.mono (hΓ.carrier.trans hKV))
  exact hcongr.symm.trans hzero
end D12Complex.GreenRegionIndex

open Set Filter Topology
namespace D12Complex.GreenRegionIndex
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

/-- The actual directional coordinate derivatives depend only on the field near the point. -/
theorem scalarPartialDerivative_eq_of_eventuallyEq {n : ℕ} {f g : E n → ℝ}
    {x : E n} (h : f =ᶠ[𝓝 x] g) (i : Fin n) :
    scalarPartialDerivative f x i = scalarPartialDerivative g x i := by
  unfold scalarPartialDerivative directionalDerivative
  apply Filter.EventuallyEq.deriv_eq
  apply h.comp_tendsto
  simpa using (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.tendsto
    (x := (0 : ℝ)) (f := fun t : ℝ => x + t • standardBasis n i)

/-- Both Green densities and the full first real differential are preserved by local field agreement. -/
theorem green_densities_eq_of_eventuallyEq (Q q : ℂ → ℂ) (z : ℂ)
    (heq : Q =ᶠ[𝓝 z] q) :
    fderiv ℝ Q z = fderiv ℝ q z ∧
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
      (fun x => -(Q (planeCoordinates.symm x)).im) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).re)
        (fun x => -(q (planeCoordinates.symm x)).im) (planeCoordinates z) ∧
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
      (fun x => (Q (planeCoordinates.symm x)).re) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).im)
        (fun x => (q (planeCoordinates.symm x)).re) (planeCoordinates z) := by
  have hc := heq.comp_tendsto (planeCoordinates.symm.continuousAt.tendsto (x := planeCoordinates z))
  dsimp only [Function.comp_def] at hc
  refine ⟨heq.fderiv_eq, ?_, ?_⟩
  · unfold circulationDensity
    rw [scalarPartialDerivative_eq_of_eventuallyEq (hc.mono (fun x hx => congrArg (fun w : ℂ => -w.im) hx)),
      scalarPartialDerivative_eq_of_eventuallyEq (hc.mono (fun x hx => congrArg Complex.re hx))]
  · unfold circulationDensity
    rw [scalarPartialDerivative_eq_of_eventuallyEq (hc.mono (fun x hx => congrArg Complex.re hx)),
      scalarPartialDerivative_eq_of_eventuallyEq (hc.mono (fun x hx => congrArg Complex.im hx))]

/-- Equality of the first real differentials transfers the actual two CR bulk densities. -/
theorem green_densities_eq_of_fderiv_eq (Q q : ℂ → ℂ) (z : ℂ)
    (hQ : DifferentiableAt ℝ Q z) (hq : DifferentiableAt ℝ q z)
    (hfd : fderiv ℝ Q z = fderiv ℝ q z) :
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
      (fun x => -(Q (planeCoordinates.symm x)).im) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).re)
        (fun x => -(q (planeCoordinates.symm x)).im) (planeCoordinates z) ∧
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
      (fun x => (Q (planeCoordinates.symm x)).re) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).im)
        (fun x => (q (planeCoordinates.symm x)).re) (planeCoordinates z) := by
  obtain ⟨hQrx, hQry, hQix, hQiy⟩ := coordinate_partials Q z hQ
  obtain ⟨hqrx, hqry, hqix, hqiy⟩ := coordinate_partials q z hq
  constructor
  · have hQn : scalarPartialDerivative (fun x => -(Q (planeCoordinates.symm x)).im)
        (planeCoordinates z) 0 =
        -scalarPartialDerivative (fun x => (Q (planeCoordinates.symm x)).im)
          (planeCoordinates z) 0 :=
      D04.Green.partial_neg (fun x => (Q (planeCoordinates.symm x)).im) (planeCoordinates z) 0
    have hqn : scalarPartialDerivative (fun x => -(q (planeCoordinates.symm x)).im)
        (planeCoordinates z) 0 =
        -scalarPartialDerivative (fun x => (q (planeCoordinates.symm x)).im)
          (planeCoordinates z) 0 :=
      D04.Green.partial_neg (fun x => (q (planeCoordinates.symm x)).im) (planeCoordinates z) 0
    simp only [circulationDensity]
    rw [hQn, hqn, scalarPartialDerivative_zero (fun w => (Q w).im),
      scalarPartialDerivative_one (fun w => (Q w).re),
      scalarPartialDerivative_zero (fun w => (q w).im),
      scalarPartialDerivative_one (fun w => (q w).re), hQix, hQry, hqix, hqry, hfd]
  · simp only [circulationDensity]
    rw [scalarPartialDerivative_zero (fun w => (Q w).re),
      scalarPartialDerivative_one (fun w => (Q w).im),
      scalarPartialDerivative_zero (fun w => (q w).re),
      scalarPartialDerivative_one (fun w => (q w).im), hQrx, hQiy, hqrx, hqiy, hfd]

/-- Scalar Green for the actual positive-cell union, with no change to its supplied assembly. -/
theorem positive_cell_circulation_zero_on {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (f g : E 2 → ℝ)
    (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hzero : ∀ x ∈ (⋃ j, cellExtension (d.cells j) '' cube 2),
      circulationDensity f g x = 0) :
    patchChainIntegral (circulationForm f g) d.outer = 0 := by
  have h := D04.Green.riemann_cell_green d.cells d.faces d.faces_agree d.outer
    d.left d.right d.multiplicity d.sign d.sign_unit d.pair_maps d.pair_weights
    d.assembly d.injective d.positive d.bulkSeams d.bulk_overlap f g d.open_ambient hf hg
  have he : (fun x : (⋃ j, cellExtension (d.cells j) '' cube 2) =>
      circulationDensity f g x) = fun _ => 0 := by
    funext x
    exact hzero x x.property
  have hv := h.2.2.2.1
  rw [he, region_integral_zero] at hv
  exact hv.symm

/-- The two real Green values of a global C1 field vanish when it is holomorphic on the carrier. -/
theorem positive_cell_green_zero {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (Q : ℂ → ℂ)
    (hQ : ContDiff ℝ 1 Q)
    (hzero : ∀ z ∈ d.carrier,
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
        (fun x => -(Q (planeCoordinates.symm x)).im) (planeCoordinates z) = 0 ∧
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
        (fun x => (Q (planeCoordinates.symm x)).re) (planeCoordinates z) = 0) :
    patchChainIntegral (CellBoundaryContour.realForm Q) d.outer = 0 ∧
    patchChainIntegral (CellBoundaryContour.imagForm Q) d.outer = 0 := by
  have hc : ContDiff ℝ 1 (fun x : E 2 => Q (planeCoordinates.symm x)) :=
    hQ.comp planeCoordinates.symm.contDiff
  have hr : CrOn 1 O (fun x => (Q (planeCoordinates.symm x)).re) :=
    (D04.crOn_iff_contDiffOn 1 _ _ d.open_ambient).mpr
      (Complex.reCLM.contDiff.comp hc).contDiffOn
  have hi : CrOn 1 O (fun x => (Q (planeCoordinates.symm x)).im) :=
    (D04.crOn_iff_contDiffOn 1 _ _ d.open_ambient).mpr
      (Complex.imCLM.contDiff.comp hc).contDiffOn
  have hn : CrOn 1 O (fun x => -(Q (planeCoordinates.symm x)).im) :=
    (D04.crOn_iff_contDiffOn 1 _ _ d.open_ambient).mpr
      ((Complex.imCLM.contDiff.comp hc).neg).contDiffOn
  have hz : ∀ x ∈ (⋃ j, cellExtension (d.cells j) '' cube 2),
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
        (fun x => -(Q (planeCoordinates.symm x)).im) x = 0 ∧
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
        (fun x => (Q (planeCoordinates.symm x)).re) x = 0 := by
    intro x hx
    have hz : planeCoordinates.symm x ∈ d.carrier := by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨j, mem_image_of_mem _ hj⟩
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hzero _ hz
  exact ⟨positive_cell_circulation_zero_on d _ _ hr hn (fun x hx => (hz x hx).1),
    positive_cell_circulation_zero_on d _ _ hi hr (fun x hx => (hz x hx).2)⟩

/-- Extend near the actual compact carrier, transfer first derivatives and CR, then apply the given Green assembly. -/
theorem positive_cell_contour_zero_near {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : CellBoundaryContour.IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U)
    (hhol : ∀ z ∈ d.carrier, DifferentiableAt ℂ q z) :
    Γ.integral q = 0 := by
  obtain ⟨Q, V, hQ, hV, hKV, _hVU, hQq, hfd, hdict, _hr, _hi⟩ :=
    CellBoundaryContour.cell_boundary_dictionary_extension_with_derivatives
      d Γ hΓ q U hU hKU hq
  have hz : ∀ z ∈ d.carrier,
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
        (fun x => -(Q (planeCoordinates.symm x)).im) (planeCoordinates z) = 0 ∧
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
        (fun x => (Q (planeCoordinates.symm x)).re) (planeCoordinates z) = 0 := by
    intro z hz
    have hfirst : fderiv ℝ Q z = fderiv ℝ q z := hfd (hKV hz)
    obtain ⟨hr, hi⟩ := green_densities_eq_of_fderiv_eq Q q z
      (hQ.differentiable (by norm_num) z) ((hhol z hz).restrictScalars ℝ) hfirst
    obtain ⟨hcr, hci⟩ := green_densities_zero q z (hhol z hz)
    exact ⟨hr.trans hcr, hi.trans hci⟩
  obtain ⟨hr, hi⟩ := positive_cell_green_zero d Q hQ hz
  simpa only [hr, hi, Complex.ofReal_zero, mul_zero, add_zero] using hdict

/-- A reciprocal without a pole on the actual closed cell union has zero original boundary integral. -/
theorem positive_cell_reciprocal_boundary_zero {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : CellBoundaryContour.IsFullPositiveBoundary d.carrier Γ)
    (a : ℂ) (ha : a ∉ d.carrier) :
    Γ.integral (fun z => 1 / (z - a)) = 0 := by
  apply positive_cell_contour_zero_near d Γ hΓ _ {a}ᶜ isClosed_singleton.isOpen_compl
  · intro z hz
    change z ≠ a
    intro he
    exact ha (he ▸ hz)
  · exact (reciprocal_regular a).1
  · intro z hz
    exact (reciprocal_regular a).2 z (fun he => ha (he ▸ hz))

end D12Complex.GreenRegionIndex

namespace D12Complex.GreenRegionIndex

/-- The geometric full boundary is supported on its actual integration carrier. -/
theorem specified_green_boundary_trace_subset :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_green_boundary_trace_subset_type := by
  intro K Γ hK
  cases hK with
  | manifold hO A he hΓ =>
    simpa only [he] using hΓ.carrier
  | cells d he hΓ =>
    have ht : Γ.trace ⊆ d.carrier := by
      rw [hΓ.1]
      exact frontier_subset_closure.trans (le_of_eq d.carrier_compact.isClosed.closure_eq)
    simpa only [he] using ht

/-- Green and CR for the original boundary, with the field defined only near
the compact carrier. In the cell branch the constructed C1 extension retains
the original first derivatives, hence the original zero bulk densities. -/
theorem specified_green_boundary_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_green_boundary_zero_type := by
  intro K Γ hK U q hU hKU hq hhol
  cases hK with
  | manifold hO A he hΓ =>
    exact planar_assembly_contour_zero_near A Γ hΓ hO q U hU
      (by simpa only [he] using hKU) hq hhol
  | cells d he hΓ =>
    have hdU : d.carrier ⊆ U := by simpa only [he] using hKU
    exact positive_cell_contour_zero_near d Γ hΓ q U hU hdU hq
      (fun z hz => hhol z (hdU hz))

/-- No-pole Green calculation, valid even when the pole lies elsewhere in
the ambient set of a supplied cell decomposition. -/
theorem specified_green_reciprocal_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_green_reciprocal_zero_type := by
  intro K Γ hK a ha
  apply specified_green_boundary_zero K Γ hK {a}ᶜ _
    isClosed_singleton.isOpen_compl
  · intro z hz
    change z ≠ a
    intro he
    exact ha (he ▸ hz)
  · exact (reciprocal_regular a).1
  · intro z hz
    exact (reciprocal_regular a).2 z (by simpa using hz)

/-- This includes every hole or other complementary component with no pole
on the same specified Green integration carrier. -/
theorem specified_green_boundary_index_zero :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_green_boundary_index_zero_type := by
  intro K Γ hK a ha
  have ht : a ∉ Γ.trace := fun h => ha (specified_green_boundary_trace_subset K Γ hK h)
  exact (cycle_index_zero_iff Γ a ht).mpr (specified_green_reciprocal_zero K Γ hK a ha)

/-- Index one in the specified region and zero outside its closure. Disk
deletion retains the original cycle and subtracts the positive small circle. -/
theorem specified_green_region_index :
    Specs.D12Complex.Ch04.GreenRegionIndex.specified_green_region_index_type := by
  intro D Γ hD
  constructor
  · intro a ha
    have ht : a ∉ Γ.trace := by
      intro htrace
      have hf := hD.boundary_trace htrace
      change a ∈ closure D \ interior D at hf
      rw [hD.isOpen.interior_eq] at hf
      exact hf.2 ha
    obtain ⟨r, hr, _hball, hdeleted⟩ := hD.deleted a ha
    have hno : a ∉ closure (D \ Metric.closedBall a r) := by
      have hsub : closure (D \ Metric.closedBall a r) ⊆ (Metric.ball a r)ᶜ :=
        closure_minimal (fun z hz hb => hz.2 (Metric.ball_subset_closedBall hb))
          Metric.isOpen_ball.isClosed_compl
      intro hm
      exact hsub hm (Metric.mem_ball_self hr)
    have hz := specified_green_reciprocal_zero _ _ hdeleted a hno
    have he : (deletedDiskCycle Γ a r).integral (fun z => 1 / (z - a)) =
        Γ.integral (fun z => 1 / (z - a)) -
          (DiskCauchyFormula.circlePath a r).integral (fun z => 1 / (z - a)) := by
      change contourIntegralHom _ (_ - _) = _
      rw [map_sub]
      simp only [contourIntegralHom_apply, chain_single_integral]
      rfl
    rw [he, sub_eq_zero] at hz
    apply (cycle_index_one_iff Γ a ht).mpr
    rw [hz]
    simpa only [one_div] using DiskCauchyFormula.circle_integral_sub_inv a a r hr
      (by simpa using hr)
  · intro a ha
    exact specified_green_boundary_index_zero _ Γ hD.whole a ha

end D12Complex.GreenRegionIndex
