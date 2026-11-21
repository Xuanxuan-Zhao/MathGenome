import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.CellBoundaryContour
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellStokesC2
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.DerivativeTest

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set MeasureTheory Filter Topology
open scoped BigOperators

namespace D12Complex.CellBoundaryContour

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

@[simp] theorem scalarLine_apply (t : ℝ) (i : Fin 1) : scalarLine t i = t := rfl

theorem scalarLine_eq_scalarPoint :
    (scalarLine : ℝ → E 1) = D04.Darboux.scalarPoint := rfl

@[simp] theorem scalarLine_coordinate (x : E 1) : scalarLine (x 0) = x := by
  ext i
  fin_cases i
  rfl

@[simp] theorem scalarLine_mem_cube (t : ℝ) : scalarLine t ∈ cube 1 ↔ t ∈ Icc 0 1 := by
  constructor
  · intro h
    exact h 0
  · intro h i
    exact h

theorem cube_integral_eq_interval :
    Specs.D12Complex.Ch04.CellBoundaryContour.cube_integral_eq_interval_type := by
  intro g hg
  let f : ℝ → ℝ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num)
    (fun t : Icc (0 : ℝ) 1 => g (scalarLine t))
  have hcont : Continuous f := by
    apply Continuous.Icc_extend'
    exact (hg.comp scalarLine.continuous.continuousOn
      (fun t ht => (scalarLine_mem_cube t).mpr ht)).domRestrict
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t = g (scalarLine t) := by
    exact IccExtend_of_mem zero_le_one _ ht
  have hftc := D04.Cells.cube_interval_ftc (fun x => ∫ t in (0 : ℝ)..x, f t) g
    (intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).continuousOn hg ?_
  · simp only [intervalIntegral.integral_same, sub_zero] at hftc
    exact hftc.trans (intervalIntegral.integral_congr (fun t ht => heq t
      (by simpa only [uIcc_of_le zero_le_one] using ht)))
  · intro t ht
    rw [← scalarLine_eq_scalarPoint, ← heq t ⟨ht.1.le, ht.2.le⟩]
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) (hcont.continuousAt)

theorem cellPath_trace :
    Specs.D12Complex.Ch04.CellBoundaryContour.cellPath_trace_type := by
  intro O c
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨scalarLine t, (scalarLine_mem_cube t).mpr ht, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u 0, hu 0, ?_⟩
    change complexCoordinates.symm (cellExtension c (scalarLine (u 0))) = _
    rw [scalarLine_coordinate]

theorem realForm_apply (q : ℂ → ℂ) (z : ℂ) (v : Fin 1 → ℂ) :
    realForm q (complexCoordinates z) (fun i => complexCoordinates (v i)) =
      (q z * v 0).re := by
  change (q (complexCoordinates.symm (complexCoordinates z))).re * (v 0).re +
    -(q (complexCoordinates.symm (complexCoordinates z))).im * (v 0).im = _
  simp only [LinearEquiv.symm_apply_apply, Complex.mul_re]
  ring

theorem imagForm_apply (q : ℂ → ℂ) (z : ℂ) (v : Fin 1 → ℂ) :
    imagForm q (complexCoordinates z) (fun i => complexCoordinates (v i)) =
      (q z * v 0).im := by
  change (q (complexCoordinates.symm (complexCoordinates z))).im * (v 0).re +
    (q (complexCoordinates.symm (complexCoordinates z))).re * (v 0).im = _
  simp only [LinearEquiv.symm_apply_apply, Complex.mul_im]
  ring

theorem coordinate_forms_continuous {O : Set (E 2)} (hO : IsOpen O)
    (q : ℂ → ℂ) (hq : ContinuousOn q (complexCoordinates ⁻¹' O)) :
    IsCrForm (some 0) O (realForm q) ∧ IsCrForm (some 0) O (imagForm q) := by
  have hc : ContinuousOn (fun x => q (complexCoordinates.symm x)) O :=
    hq.comp complexCoordinates.symm.toContinuousLinearEquiv.continuous.continuousOn
      (fun x hx => by simpa only [mem_preimage, LinearEquiv.apply_symm_apply] using hx)
  constructor
  · refine ⟨hO, fun J => ?_⟩
    change ContinuousOn (fun x => (q (complexCoordinates.symm x)).re * _ +
      -(q (complexCoordinates.symm x)).im * _) O
    exact ((Complex.continuous_re.comp_continuousOn hc).mul continuousOn_const).add
      ((Complex.continuous_im.comp_continuousOn hc).neg.mul continuousOn_const)
  · refine ⟨hO, fun J => ?_⟩
    change ContinuousOn (fun x => (q (complexCoordinates.symm x)).im * _ +
      (q (complexCoordinates.symm x)).re * _) O
    exact ((Complex.continuous_im.comp_continuousOn hc).mul continuousOn_const).add
      ((Complex.continuous_re.comp_continuousOn hc).mul continuousOn_const)

theorem cellCurve_hasDerivAt {O : Set (E 2)} (c : Cell 1 1 O)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (cellCurve c)
      (complexCoordinates.symm
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0))) t := by
  have hs : scalarLine (1 : ℝ) = standardBasis 1 0 := by
    ext i
    fin_cases i
    change 1 = standardBasis 1 0 0
    simpa only [standardBasis, D04.standardBasis, ite_true] using (D04.standardBasis_apply (n := 1) 0 0).symm
  have hd := ((D04.Cells.extension_C1 c).contDiffAt
    ((extension_spec c).1.mem_nhds
      ((extension_spec c).2.1 ((scalarLine_mem_cube t).mpr ht)))).differentiableAt
      (by norm_num)
  have hh := complexCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hd.hasFDerivAt.comp_hasDerivAt t (scalarLine.hasDerivAt (x := t)))
  rw [hs] at hh
  convert hh using 1 <;> rfl

theorem cell_coefficient_coordinates {O : Set (E 2)} (c : Cell 1 1 O)
    (q : ℂ → ℂ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    cellCoefficient c (realForm q) (scalarLine t) =
        (q (cellCurve c t) * deriv (cellCurve c) t).re ∧
      cellCoefficient c (imagForm q) (scalarLine t) =
        (q (cellCurve c t) * deriv (cellCurve c) t).im := by
  rw [(cellCurve_hasDerivAt c t ht).deriv]
  constructor
  · change (q (cellCurve c t)).re * _ + -(q (cellCurve c t)).im * _ = _
    change (q (cellCurve c t)).re *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 0 +
      -(q (cellCurve c t)).im *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 1 = _
    change _ = (q (cellCurve c t)).re *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 0 -
      (q (cellCurve c t)).im *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 1
    ring
  · change (q (cellCurve c t)).im * _ + (q (cellCurve c t)).re * _ = _
    change (q (cellCurve c t)).im *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 0 +
      (q (cellCurve c t)).re *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 1 = _
    change _ = (q (cellCurve c t)).re *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 1 +
      (q (cellCurve c t)).im *
        (fderiv ℝ (cellExtension c) (scalarLine t) (standardBasis 1 0)) 0
    ring

theorem cellPath_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.cellPath_integral_type := by
  intro O c q hq
  have hforms := coordinate_forms_continuous c.open_target q hq
  have htrace : (cellPath c).trace ⊆ complexCoordinates ⁻¹' O := by
    rw [cellPath_trace]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    change complexCoordinates (complexCoordinates.symm (cellExtension c u)) ∈ O
    rw [LinearEquiv.apply_symm_apply]
    change D04.Cells.cellExtension c (⟨u, hu⟩ : cube 1) ∈ O
    rw [D04.Cells.extension_on_cube c ⟨u, hu⟩]
    exact (c.toFun ⟨u, hu⟩).property
  have he := C1Partition.integral_eq_intervalIntegral (cellPath c).path
    (cellPath c).partition q (hq.mono htrace)
  have hr := cube_integral_eq_interval (cellCoefficient c (realForm q))
    (D04.Cells.cellCoefficient_continuous c (realForm q) hforms.1)
  have hi := cube_integral_eq_interval (cellCoefficient c (imagForm q))
    (D04.Cells.cellCoefficient_continuous c (imagForm q) hforms.2)
  change (cellPath c).partition.integral q = _
  rw [he]
  change (∫ t in (0 : ℝ)..1, q (cellCurve c t) * deriv (cellCurve c) t) = _
  have hr' : cellIntegral c (realForm q) =
      ∫ t in (0 : ℝ)..1, (q (cellCurve c t) * deriv (cellCurve c) t).re := by
    exact hr.trans (intervalIntegral.integral_congr (fun t ht =>
      (cell_coefficient_coordinates c q t (by simpa only [uIcc_of_le zero_le_one] using ht)).1))
  have hi' : cellIntegral c (imagForm q) =
      ∫ t in (0 : ℝ)..1, (q (cellCurve c t) * deriv (cellCurve c) t).im := by
    exact hi.trans (intervalIntegral.integral_congr (fun t ht =>
      (cell_coefficient_coordinates c q t (by simpa only [uIcc_of_le zero_le_one] using ht)).2))
  have hint' : IntervalIntegrable (fun t => q (cellCurve c t) * deriv (cellCurve c) t)
      volume 0 1 := by
    exact C1Partition.parameter_integrable (cellPath c).path (cellPath c).partition q (hq.mono htrace)
  rw [hr', hi']
  have hR := Complex.reCLM.intervalIntegral_comp_comm hint'
  have hI := Complex.imCLM.intervalIntegral_comp_comm hint'
  simp only [Complex.reCLM_apply] at hR
  simp only [Complex.imCLM_apply] at hI
  rw [hR, hI]
  simpa only [mul_comm] using (Complex.re_add_im
    (∫ t in (0 : ℝ)..1, q (cellCurve c t) * deriv (cellCurve c) t)).symm

private def contourIntegralHom (q : ℂ → ℂ) : IntegralChain →+ ℂ :=
  Finsupp.liftAddHom (fun γ =>
    { toFun := fun a : ℤ => (a : ℂ) * γ.integral q
      map_zero' := by simp
      map_add' := fun a b => by simp [add_mul] })

private theorem contourIntegralHom_apply (q : ℂ → ℂ) (Γ : IntegralChain) :
    contourIntegralHom q Γ = Γ.integral q := rfl

@[simp] theorem cellContour_single {O : Set (E 2)} (c : Cell 1 1 O) (a : ℤ) :
    cellContour (Finsupp.single c a) = Finsupp.single (cellPath c) a :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem cellContour_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.cellContour_integral_type := by
  intro O C q hq
  let H : Chain 1 1 O →+ ℂ :=
    { toFun := fun C => (chainIntegral (realForm q) C : ℂ) +
        Complex.I * chainIntegral (imagForm q) C
      map_zero' := by simp
      map_add' := fun C D => by simp only [map_add, Complex.ofReal_add]; ring }
  have hh : (contourIntegralHom q).comp cellContour = H := by
    ext c
    change contourIntegralHom q (cellContour (Finsupp.single c 1)) = H (Finsupp.single c 1)
    rw [cellContour_single]
    rw [show contourIntegralHom q (Finsupp.single (cellPath c) 1) =
      (1 : ℂ) * (cellPath c).integral q by
        unfold contourIntegralHom
        rw [Finsupp.liftAddHom_apply_single]
        simp]
    change _ = (chainIntegral (realForm q) (Finsupp.single c 1) : ℂ) +
      Complex.I * chainIntegral (imagForm q) (Finsupp.single c 1)
    rw [D04.Cells.chainIntegral_single, D04.Cells.chainIntegral_single, cellPath_integral c q hq]
    simp only [zsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  exact (contourIntegralHom_apply q (cellContour C)).symm.trans
    (DFunLike.congr_fun hh C)

theorem cellBoundary_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.cellBoundary_integral_type := by
  intro O c q hq
  exact cellContour_integral (cellBoundary c) q hq

theorem face_patch_dictionary :
    Specs.D12Complex.Ch04.CellBoundaryContour.face_patch_dictionary_type := by
  intro O c P hregion hmap q hq
  have hforms := coordinate_forms_continuous c.open_target q hq
  obtain ⟨Q, hQ, hQmap, hQI⟩ := D04.GeometricPatches.cell_patch_exists c
  have hregion' : P.region = Q.region := hregion.trans hQ.symm
  have hmap' : EqOn P.map Q.map P.region := by
    intro x hx
    rw [hQmap]
    exact hmap (by simpa only [← hregion] using hx)
  have hR := D04.GeometricPatches.representative_independent P Q hregion' hmap'
    (realForm q) hforms.1 (fun _ => 1) continuousOn_const
  have hI := D04.GeometricPatches.representative_independent P Q hregion' hmap'
    (imagForm q) hforms.2 (fun _ => 1) continuousOn_const
  rw [hQI _ hforms.1] at hR
  rw [hQI _ hforms.2] at hI
  rw [hR, hI]
  exact cellPath_integral c q hq

theorem cell_assembly_real_boundary :
    Specs.D12Complex.Ch04.CellBoundaryContour.cell_assembly_real_boundary_type := by
  intro O d ω hω
  have cancel (i : Fin d.pairs) : patchChainIntegral ω
      (Finsupp.single (d.left i) 1 - d.sign i • Finsupp.single (d.right i) 1) = 0 := by
    obtain ⟨h, hm⟩ := d.pair_maps i
    have hv := D04.GeometricPatches.matching_reparametrization
      (d.left i).patch (d.right i).patch (d.sign i : ℝ)
      (by rcases d.sign_unit i with he | he <;> simp [he]) h hm ω hω
      (d.left i).weight (d.right i).weight
      (d.left i).continuous (d.right i).continuous (d.pair_weights i)
    simpa only [map_sub, map_zsmul, D04.GeometricPatches.chain_integral_single,
      one_zsmul, zsmul_eq_mul, Int.cast_one, one_mul, sub_eq_zero] using hv
  calc
    _ = patchChainIntegral ω (∑ j, (1 : ℤ) • patchBoundary (d.faces j)) := by
      simp only [map_sum, one_zsmul]
      apply Finset.sum_congr rfl
      intro j _
      exact (D04.FinitePiecewiseStokes.patchBoundary_integral
        (d.cells j) (d.faces j) (d.faces_agree j) ω hω).symm
    _ = patchChainIntegral ω
        (d.outer + ∑ i, d.multiplicity i •
          (Finsupp.single (d.left i) 1 - d.sign i • Finsupp.single (d.right i) 1)) :=
      D04.GeometricPatches.geometric_equivalence_sound ω hω _ _ d.assembly
    _ = patchChainIntegral ω d.outer := by
      simp only [map_add, map_sum, map_zsmul, cancel, zsmul_zero,
        Finset.sum_const_zero, add_zero]

theorem cell_assembly_dictionary :
    Specs.D12Complex.Ch04.CellBoundaryContour.cell_assembly_dictionary_type := by
  intro O d q hq
  have hforms := coordinate_forms_continuous d.open_ambient q hq
  change (cellContour (∑ j, (1 : ℤ) • cellBoundary (d.cells j))).integral q = _
  rw [cellContour_integral _ q hq,
    cell_assembly_real_boundary d (realForm q) hforms.1,
    cell_assembly_real_boundary d (imagForm q) hforms.2]

theorem finite_subpath_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.finite_subpath_integral_type := by
  intro γ n node hm ha hb δ hδ q hq
  have hlo (i : Fin (n + 1)) : γ.path.a ≤ node i := by
    rw [← ha]
    exact hm (Fin.zero_le i)
  have hhi (i : Fin (n + 1)) : node i ≤ γ.path.b := by
    rw [← hb]
    exact hm (Fin.le_last i)
  have hEq (i : Fin n) : EqOn (δ i) γ (Icc (δ i).path.a (δ i).path.b) := by
    rw [(hδ i).1, (hδ i).2.1]
    exact (hδ i).2.2
  have hcont (i : Fin n) : ContinuousOn q (δ i).trace :=
    PiecewiseC1Path.continuousOn_trace_of_restriction γ (δ i) q hq
      (by rw [(hδ i).1]; exact hlo _) (by rw [(hδ i).2.1]; exact hhi _) (hEq i)
  have he (i : Fin n) : (δ i).integral q =
      ∫ t in node i.castSucc..node i.succ, q (γ t) * deriv γ t := by
    rw [PiecewiseC1Path.integral_congr_representative (δ i) γ q (hcont i) (hEq i),
      (hδ i).1, (hδ i).2.1]
  have hint := C1Partition.parameter_integrable γ.path γ.partition q hq
  have hpart := intervalIntegral_fin_partition node (fun t => q (γ t) * deriv γ t)
    (fun i => hint.mono_set (by
      rw [uIcc_of_le (hm (Fin.castSucc_le_succ i)), uIcc_of_le γ.path.ordered]
      exact Icc_subset_Icc (hlo _) (hhi _)))
  simp_rw [he]
  rw [ha, hb] at hpart
  exact (C1Partition.integral_eq_intervalIntegral γ.path γ.partition q hq).trans hpart.2.symm

theorem finite_subpath_selection :
    Specs.D12Complex.Ch04.CellBoundaryContour.finite_subpath_selection_type := by
  intro γ ι U hU hcover
  let V : ι → Set (Icc γ.path.a γ.path.b) :=
    fun i => (fun t : Icc γ.path.a γ.path.b => γ t) ⁻¹' U i
  have hV (i : ι) : IsOpen (V i) :=
    (hU i).preimage γ.path.onInterval.continuous
  have hVc : univ ⊆ ⋃ i, V i := by
    intro t _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨t, t.property, rfl⟩)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, hpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc γ.path.ordered hV hVc
  let node : Fin (n + 1) → ℝ := fun i => t i.val
  have hm : Monotone node := fun i j hij => (htm hij)
  have ha : node 0 = γ.path.a := ht0
  have hb : node (Fin.last n) = γ.path.b := htn n le_rfl
  have hselect (i : Fin n) : ∃ j, ∀ s ∈ Icc (node i.castSucc) (node i.succ),
      γ s ∈ U j := by
    obtain ⟨j, hj⟩ := hpiece i.val
    refine ⟨j, fun s hs => ?_⟩
    have hs' : s ∈ Icc γ.path.a γ.path.b :=
      ⟨(t i.val).property.1.trans hs.1, hs.2.trans (t (i.val + 1)).property.2⟩
    exact hj (show (⟨s, hs'⟩ : Icc γ.path.a γ.path.b) ∈ Icc (t i.val) (t (i.val + 1)) from hs)
  choose select hsel using hselect
  have hrestrict (i : Fin n) := PiecewiseC1Path.exists_restriction γ
    (node i.castSucc) (node i.succ) (t i.val).property.1
    (hm (Fin.castSucc_le_succ i)) (t (i.val + 1)).property.2
  choose δ hδ using hrestrict
  refine ⟨n, node, select, δ, hm, ha, hb, ?_, ?_⟩
  · intro i
    refine ⟨(hδ i).1, (hδ i).2.1, (hδ i).2.2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [(hδ i).1, (hδ i).2.1] at hs
    rw [(hδ i).2.2 hs]
    exact hsel i s hs
  · exact finite_subpath_integral γ n node hm ha hb δ hδ

theorem scalar_piecewise_substitution :
    Specs.D12Complex.Ch04.CellBoundaryContour.scalar_piecewise_substitution_type := by
  intro φ c d a b n node hm ha hb hφ hmaps hsmooth g hg
  have hnode (i : Fin (n + 1)) : node i ∈ Icc c d := by
    rw [← ha, ← hb]
    exact ⟨hm.monotone (Fin.zero_le i), hm.monotone (Fin.le_last i)⟩
  have hsub (i : Fin n) : Icc (node i.castSucc) (node i.succ) ⊆ Icc c d :=
    Icc_subset_Icc (hnode _).1 (hnode _).2
  have hφnode (i : Fin (n + 1)) : φ (node i) ∈ Icc a b := hmaps (hnode i)
  have hint (i : Fin n) : IntervalIntegrable g volume
      (φ (node i.castSucc)) (φ (node i.succ)) :=
    (hg.mono (uIcc_subset_Icc (hφnode _) (hφnode _))).intervalIntegrable
  have he (i : Fin n) :
      (∫ t in node i.castSucc..node i.succ,
        derivWithin φ (Icc (node i.castSucc) (node i.succ)) t • g (φ t)) =
      ∫ s in φ (node i.castSucc)..φ (node i.succ), g s := by
    have hlt : node i.castSucc < node i.succ := hm (Fin.castSucc_lt_succ (i := i))
    have hdiff := (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hlt)).mp (hsmooth i)
    apply intervalIntegral.integral_deriv_smul_comp''
    · simpa only [uIcc_of_le hlt.le] using hφ.mono (hsub i)
    · intro t ht
      simp only [min_eq_left hlt.le, max_eq_right hlt.le] at ht
      exact ((hdiff.1 t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2) |>.hasDerivWithinAt
    · simpa only [uIcc_of_le hlt.le] using hdiff.2
    · apply hg.mono
      rw [uIcc_of_le hlt.le]
      rintro _ ⟨t, ht, rfl⟩
      exact hmaps (hsub i ht)
  simp_rw [he]
  have hp := (intervalIntegral_fin_partition (fun i => φ (node i)) g hint).2
  simpa only [ha, hb] using hp

theorem arc_factorization_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.arc_factorization_integral_type := by
  intro η g φ a b V hV habV hg hφ hmaps hη hsmooth q hq
  let P := η.partition
  have hgdiff (s : ℝ) (hs : s ∈ Icc a b) : DifferentiableAt ℝ g s :=
    (hg.contDiffAt (hV.mem_nhds (habV hs))).differentiableAt (by norm_num)
  have hH : ContinuousOn (fun s => q (g s) * deriv g s) (Icc a b) := by
    apply ContinuousOn.mul
    · exact hq.comp (hg.continuousOn.mono habV) (mapsTo_image g _)
    · exact (hg.continuousOn_deriv_of_isOpen hV le_rfl).mono habV
  have he (i : Fin P.count) :
      (∫ t in P.node i.castSucc..P.node i.succ,
        q (η t) * derivWithin η (P.pieceSet i) t) =
      ∫ t in P.node i.castSucc..P.node i.succ,
        derivWithin φ (P.pieceSet i) t • (q (g (φ t)) * deriv g (φ t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htp : t ∈ P.pieceSet i := by
      simpa only [C1Partition.pieceSet, uIcc_of_le (P.piece_lt i).le] using ht
    have hfull := P.piece_subset i htp
    have hφd := (hsmooth i).differentiableOn (by norm_num) t htp
    have hd := (hgdiff (φ t) (hmaps hfull)).hasDerivAt.scomp_hasDerivWithinAt t
      hφd.hasDerivWithinAt
    have heq : EqOn η (g ∘ φ) (P.pieceSet i) := hη.mono (P.piece_subset i)
    have hdη : HasDerivWithinAt η
        (derivWithin φ (P.pieceSet i) t • deriv g (φ t)) (P.pieceSet i) t :=
      hd.congr (fun x hx => heq hx) (heq htp)
    change q (η t) * derivWithin η (P.pieceSet i) t = _
    rw [hdη.derivWithin ((uniqueDiffOn_Icc (P.piece_lt i)) t htp), hη hfull]
    exact mul_smul_comm _ _ _
  change (∑ i : Fin P.count, _) = _
  apply (Finset.sum_congr rfl (fun i _ => he i)).trans
  exact scalar_piecewise_substitution φ η.path.a η.path.b a b P.count P.node
    P.strictMono P.first P.last hφ hmaps hsmooth (fun s => q (g s) * deriv g s) hH

theorem cellFace_differential_column {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool) (u : E 1) (hu : u ∈ cube 1) :
    fderiv ℝ (cellExtension (cellFace c i e)) u (standardBasis 1 0) =
      fderiv ℝ (cellExtension c) (faceInsertion i e u) (standardBasis 2 (i.succAbove 0)) := by
  let W := faceInsertion i e ⁻¹' extensionDomain c
  have hW : IsOpen W :=
    (extension_spec c).1.preimage (faceInsertion_contDiff i e).continuous
  have hsub : cube 1 ⊆ W := fun x hx =>
    (extension_spec c).2.1 (faceInsertion_mem i e hx)
  have hreg : ContDiffOn ℝ 1 (cellExtension c ∘ faceInsertion i e) W :=
    (D04.Cells.extension_C1 c).comp
      ((faceInsertion_contDiff i e).of_le (by norm_num)).contDiffOn (fun _ hx => hx)
  have huniq := D04.Cells.extension_derivative_unique (cellFace c i e)
    (cellExtension c ∘ faceInsertion i e) W hW hsub hreg
    (fun x => (extension_spec c).2.2.2 ⟨faceInsertion i e x, faceInsertion_mem i e x.property⟩)
    ⟨u, hu⟩
  have hd := ((D04.Cells.extension_C1 c).contDiffAt
    ((extension_spec c).1.mem_nhds (hsub hu))).differentiableAt (by norm_num)
  change fderiv ℝ (cellExtension (cellFace c i e)) u =
    fderiv ℝ (cellExtension c ∘ faceInsertion i e) u at huniq
  rw [huniq, fderiv_comp _ hd ((faceInsertion_contDiff i e).differentiable (by norm_num) u)]
  change fderiv ℝ (cellExtension c) (faceInsertion i e u)
    (fderiv ℝ (faceInsertion i e) u (standardBasis 1 0)) = _
  apply congrArg (fderiv ℝ (cellExtension c) (faceInsertion i e u))
  simpa only [D04.totalDerivative, Specs.D04.C02.DerivativeInterfaces.totalDerivativeValue,
    Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative,
    D04.standardBasis, standardBasis] using
    D04.Cells.faceInsertion_derivative i e u 0

theorem regular_cell_face :
    Specs.D12Complex.Ch04.CellBoundaryContour.regular_cell_face_type := by
  intro O c hc hpos i e
  have hval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      cellCurve (cellFace c i e) t =
        complexCoordinates.symm (cellExtension c (faceInsertion i e (scalarLine t))) := by
    change complexCoordinates.symm (cellExtension (cellFace c i e) (scalarLine t)) = _
    rw [show cellExtension (cellFace c i e) (scalarLine t) =
      ((cellFace c i e).toFun ⟨scalarLine t, (scalarLine_mem_cube t).mpr ht⟩).val from
        (extension_spec (cellFace c i e)).2.2.2 ⟨scalarLine t, (scalarLine_mem_cube t).mpr ht⟩]
    rw [show cellExtension c (faceInsertion i e (scalarLine t)) =
      (c.toFun ⟨faceInsertion i e (scalarLine t),
        faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ht)⟩).val from
        (extension_spec c).2.2.2 ⟨faceInsertion i e (scalarLine t),
          faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ht)⟩]
    rfl
  constructor
  · intro s hs t ht heq
    rw [hval s hs, hval t ht] at heq
    have hface := hc
      (faceInsertion_mem i e ((scalarLine_mem_cube s).mpr hs))
      (faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ht))
      (complexCoordinates.symm.injective heq)
    have hcoord := congrArg (fun x : E 2 => x (i.succAbove 0)) hface
    simpa only [D04.Cells.faceInsertion_other, scalarLine_apply] using hcoord
  · intro t ht
    rw [(cellCurve_hasDerivAt (cellFace c i e) t ht).deriv,
      cellFace_differential_column c i e (scalarLine t) ((scalarLine_mem_cube t).mpr ht)]
    have hdet : (fderiv ℝ (cellExtension c) (faceInsertion i e (scalarLine t))).toLinearMap.det ≠ 0 :=
      (hpos _ (faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ht))).ne'
    have hinj : Function.Injective (fderiv ℝ (cellExtension c) (faceInsertion i e (scalarLine t))) := by
      apply LinearMap.ker_eq_bot.mp
      by_contra hker
      exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
    intro hz
    have hzero : fderiv ℝ (cellExtension c) (faceInsertion i e (scalarLine t))
        (standardBasis 2 (i.succAbove 0)) = 0 := by
      apply complexCoordinates.symm.injective
      simpa only [map_zero] using hz
    exact (standardBasis 2).ne_zero (i.succAbove 0)
      (hinj (hzero.trans (map_zero _).symm))

theorem regular_curve_coordinate :
    Specs.D12Complex.Ch04.CellBoundaryContour.regular_curve_coordinate_type := by
  intro g s hg hne
  have hex : ∃ L : ℂ →L[ℝ] ℝ, L (deriv g s) ≠ 0 := by
    by_cases hr : (deriv g s).re = 0
    · refine ⟨Complex.imCLM, ?_⟩
      intro hi
      exact hne (Complex.ext hr hi)
    · exact ⟨Complex.reCLM, hr⟩
  obtain ⟨L, hL⟩ := hex
  let F : ℝ → ℝ := L ∘ g
  have hF : ContDiffAt ℝ 1 F s := L.contDiff.comp_contDiffAt s hg
  have hd : HasDerivAt F (L (deriv g s)) s :=
    L.hasFDerivAt.comp_hasDerivAt s ((hg.differentiableAt (by norm_num)).hasDerivAt)
  let hf := hd.hasFDerivAt_equiv hL
  let inv := hF.localInverse hf (by norm_num)
  have hInv : ContDiffAt ℝ 1 inv (F s) := hF.to_localInverse hf (by norm_num)
  let e := hF.toOpenPartialHomeomorph F hf (by norm_num)
  have hs : s ∈ e.source := hF.mem_toOpenPartialHomeomorph_source hf (by norm_num)
  refine ⟨inv ∘ L, hInv.comp (g s) L.contDiff.contDiffAt, ?_⟩
  filter_upwards [e.open_source.mem_nhds hs] with t ht
  change e.symm (e t) = t
  exact e.left_inv ht

theorem recover_parameter_contDiffOn :
    Specs.D12Complex.Ch04.CellBoundaryContour.recover_parameter_contDiffOn_type := by
  intro S f g φ hf hφ hfactor hreg t ht
  obtain ⟨ψ, hψ, hleft⟩ := regular_curve_coordinate g (φ t) (hreg t ht).1 (hreg t ht).2
  have hψf : ContDiffAt ℝ 1 ψ (f t) := by
    rw [hfactor ht]
    exact hψ
  have hcomp := hψf.comp_contDiffWithinAt t (hf t ht)
  have he : φ =ᶠ[nhdsWithin t S] ψ ∘ f := by
    filter_upwards [(hφ t ht) hleft, self_mem_nhdsWithin] with x hx hxS
    change φ x = ψ (f x)
    rw [hfactor hxS]
    exact hx.symm
  apply hcomp.congr_of_eventuallyEq he
  change φ t = ψ (f t)
  rw [hfactor ht]
  exact (hleft.self_of_nhds).symm

theorem regular_arc_factorization_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.regular_arc_factorization_integral_type := by
  intro η g φ a b V hV hsub hg hreg hφ hmaps hfactor q hq
  apply arc_factorization_integral η g φ a b V hV hsub hg hφ hmaps hfactor _ q hq
  intro i
  apply recover_parameter_contDiffOn (η.partition.pieceSet i) η g φ
    (η.partition.smooth i) (hφ.mono (η.partition.piece_subset i))
    (hfactor.mono (η.partition.piece_subset i))
  intro t ht
  have hpt := hmaps (η.partition.piece_subset i ht)
  exact ⟨hg.contDiffAt (hV.mem_nhds (hsub hpt)), hreg _ hpt⟩

theorem parameter_on_injective_arc :
    Specs.D12Complex.Ch04.CellBoundaryContour.parameter_on_injective_arc_type := by
  intro η g a b hg hinj htrace
  let φ : ℝ → ℝ := fun t => Function.invFunOn g (Icc a b) (η t)
  have hm (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) :
      ∃ s ∈ Icc a b, g s = η t := htrace ⟨t, ht, rfl⟩
  have hmap : MapsTo φ (Icc η.path.a η.path.b) (Icc a b) :=
    fun t ht => Function.invFunOn_mem (hm t ht)
  have heq : EqOn η (g ∘ φ) (Icc η.path.a η.path.b) :=
    fun t ht => (Function.invFunOn_eq (hm t ht)).symm
  let G : Icc a b → ℂ := fun s => g s
  have hG : Topology.IsEmbedding G :=
    (hg.domRestrict.isClosedEmbedding (fun s t h =>
      Subtype.ext (hinj s.property t.property h))).isEmbedding
  let Φ : Icc η.path.a η.path.b → Icc a b := fun t => ⟨φ t, hmap t.property⟩
  have hΦ : Continuous Φ := hG.continuous_iff.mpr (by
    have he : G ∘ Φ = (fun t : Icc η.path.a η.path.b => η t) :=
      funext (fun t => (heq t.property).symm)
    rw [he]
    exact η.path.onInterval.continuous)
  refine ⟨φ, ?_, hmap, heq⟩
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp hΦ)

theorem trace_regular_arc_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.trace_regular_arc_integral_type := by
  intro η g a b V hV hsub hg hinj hreg htrace
  obtain ⟨φ, hφ, hmap, heq⟩ := parameter_on_injective_arc η g a b
    (hg.continuousOn.mono hsub) hinj htrace
  have hsmooth (i : Fin η.partition.count) :
      ContDiffOn ℝ 1 φ (η.partition.pieceSet i) := by
    apply recover_parameter_contDiffOn (η.partition.pieceSet i) η g φ
      (η.partition.smooth i) (hφ.mono (η.partition.piece_subset i))
      (heq.mono (η.partition.piece_subset i))
    intro t ht
    have hpt := hmap (η.partition.piece_subset i ht)
    exact ⟨hg.contDiffAt (hV.mem_nhds (hsub hpt)), hreg _ hpt⟩
  exact ⟨φ, hφ, hmap, heq, hsmooth, fun q hq =>
    arc_factorization_integral η g φ a b V hV hsub hg hφ hmap heq hsmooth q hq⟩

theorem cellCurve_extension {O : Set (E 2)} (c : Cell 1 1 O) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc (0 : ℝ) 1 ⊆ V ∧ ContDiffOn ℝ 1 (cellCurve c) V := by
  let V := scalarLine ⁻¹' extensionDomain c
  refine ⟨V, (extension_spec c).1.preimage scalarLine.continuous, ?_, ?_⟩
  · exact fun t ht => (extension_spec c).2.1 ((scalarLine_mem_cube t).mpr ht)
  · exact complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      ((D04.Cells.extension_C1 c).comp scalarLine.contDiff.contDiffOn (fun _ hx => hx))

theorem cell_face_traversal_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.cell_face_traversal_integral_type := by
  intro O c hinj hpos i e η htrace
  obtain ⟨V, hV, hsub, hg⟩ := cellCurve_extension (cellFace c i e)
  have hreg := regular_cell_face c hinj hpos i e
  obtain ⟨φ, hφ, hmaps, heq, hsmooth, hint⟩ := trace_regular_arc_integral
    η (cellCurve (cellFace c i e)) 0 1 V hV hsub hg hreg.1 hreg.2 htrace
  refine ⟨φ, hφ, hmaps, heq, hsmooth, fun q hq => hint q (hq.mono ?_)⟩
  rintro _ ⟨t, ht, rfl⟩
  change complexCoordinates (complexCoordinates.symm
    (cellExtension (cellFace c i e) (scalarLine t))) ∈ O
  rw [LinearEquiv.apply_symm_apply]
  rw [(extension_spec (cellFace c i e)).2.2.2 ⟨scalarLine t, (scalarLine_mem_cube t).mpr ht⟩]
  exact ((cellFace c i e).toFun ⟨scalarLine t, (scalarLine_mem_cube t).mpr ht⟩).property

/-- A nonzero derivative makes a point isolated within its level set. -/
theorem nonzero_deriv_fiber_countable (f : ℝ → ℂ) (z : ℂ) :
    {t : ℝ | f t = z ∧ deriv f t ≠ 0}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_nhdsNE.mpr
  intro t ht
  apply Filter.inf_principal_eq_bot.mpr
  have h := (differentiableAt_of_deriv_ne_zero ht.2).hasDerivAt.eventually_ne
    (c := z) ht.2
  exact h.mono (fun u hu hmem => hu hmem.1)

theorem nonzero_deriv_countable_preimage :
    Specs.D12Complex.Ch04.CellBoundaryContour.nonzero_deriv_countable_preimage_type := by
  intro f Z hZ
  have hsub : {t : ℝ | f t ∈ Z ∧ deriv f t ≠ 0} ⊆
      ⋃ z ∈ Z, {t : ℝ | f t = z ∧ deriv f t ≠ 0} := by
    intro t ht
    exact mem_iUnion.mpr ⟨f t, mem_iUnion.mpr ⟨ht.1, rfl, ht.2⟩⟩
  exact (hZ.biUnion (fun z _ => nonzero_deriv_fiber_countable f z)).mono hsub

theorem deriv_zero_ae_on_countable_preimage :
    Specs.D12Complex.Ch04.CellBoundaryContour.deriv_zero_ae_on_countable_preimage_type := by
  intro f Z hZ
  filter_upwards [(nonzero_deriv_countable_preimage f Z hZ).ae_notMem volume] with t ht
  intro hz
  by_contra hd
  exact ht ⟨hz, hd⟩

theorem path_integral_congr_off_countable :
    Specs.D12Complex.Ch04.CellBoundaryContour.path_integral_congr_off_countable_type := by
  intro γ Z hZ q r heq
  have hae : ∀ᵐ t : ℝ, t ∈ Icc γ.path.a γ.path.b →
      q (γ t) * deriv γ t = r (γ t) * deriv γ t := by
    filter_upwards [deriv_zero_ae_on_countable_preimage γ Z hZ] with t ht hmem
    by_cases hz : γ t ∈ Z
    · simp [ht hz]
    · rw [heq ⟨⟨t, hmem, rfl⟩, hz⟩]
  have hp : γ.partition.integral q = γ.partition.integral r := by
    unfold C1Partition.integral
    apply Finset.sum_congr rfl
    intro i hi
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae, volume.ae_ne (γ.partition.node i.succ)] with t ht hne hmem
    have hlt := γ.partition.piece_lt i
    by_cases hin : t ∈ Ioo (γ.partition.node i.castSucc) (γ.partition.node i.succ)
    · have hIcc : t ∈ Icc γ.path.a γ.path.b :=
        γ.partition.piece_subset i ⟨hin.1.le, hin.2.le⟩
      simpa only [C1Partition.pieceSet,
        derivWithin_of_mem_nhds (Icc_mem_nhds hin.1 hin.2)] using ht hIcc
    · have hm : t ∈ Ioc (γ.partition.node i.castSucc) (γ.partition.node i.succ) := by
        simpa only [uIoc_of_le hlt.le] using hmem
      exact (hin ⟨hm.1, lt_of_le_of_ne hm.2 hne⟩).elim
  exact hp

/-- The canonical partition integral agrees with the parameter integral whenever
that integrand is integrable, including discontinuous geometric cutoffs. -/
theorem path_integral_eq_interval_of_integrable (γ : PiecewiseC1Path) (q : ℂ → ℂ)
    (hq : IntervalIntegrable (fun t => q (γ t) * deriv γ t) volume γ.path.a γ.path.b) :
    γ.integral q = ∫ t in γ.path.a..γ.path.b, q (γ t) * deriv γ t := by
  have hi (i : Fin γ.partition.count) : IntervalIntegrable
      (fun t => q (γ t) * deriv γ t) volume
      (γ.partition.node i.castSucc) (γ.partition.node i.succ) := by
    apply hq.mono_set
    simpa only [uIcc_of_le (γ.partition.piece_lt i).le,
      uIcc_of_le γ.path.ordered, C1Partition.pieceSet] using γ.partition.piece_subset i
  have hs := (intervalIntegral_fin_partition γ.partition.node _ hi).2
  change γ.partition.integral q = _
  unfold C1Partition.integral
  rw [← γ.partition.first, ← γ.partition.last]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hs
  apply intervalIntegral.integral_congr_Ioo_of_le (γ.partition.piece_lt i).le
  intro t ht
  simp only [C1Partition.pieceSet, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

private theorem path_indicator_formula (γ : PiecewiseC1Path) (U : Set ℂ)
    (hU : MeasurableSet U) (q : ℂ → ℂ) (hq : ContinuousOn q γ.trace) :
    let G := IccExtend γ.path.ordered γ.path.onInterval
    γ.integral (U.indicator q) = ∫ t in γ.path.a..γ.path.b,
      (G ⁻¹' U).indicator (fun t => q (γ t) * deriv γ t) t := by
  intro G
  have hG : Continuous G := γ.path.onInterval.continuous.Icc_extend'
  have hA : MeasurableSet (G ⁻¹' U) := hU.preimage hG.measurable
  have heq : (fun t => (U.indicator q) (γ t) * deriv γ t) =ᵐ[
      volume.restrict (Ioc γ.path.a γ.path.b)]
      (G ⁻¹' U).indicator (fun t => q (γ t) * deriv γ t) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    have hGt : G t = γ t := IccExtend_of_mem γ.path.ordered _ ⟨ht.1.le, ht.2⟩
    by_cases hmem : γ t ∈ U <;> simp [Set.indicator, hGt, hmem]
  have hf := C1Partition.parameter_integrable γ.path γ.partition q hq
  have hi := hf.1.indicator hA
  have hraw : IntervalIntegrable (fun t => (U.indicator q) (γ t) * deriv γ t)
      volume γ.path.a γ.path.b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le γ.path.ordered).mpr
    exact hi.congr heq.symm
  rw [path_integral_eq_interval_of_integrable γ _ hraw,
    intervalIntegral.integral_of_le γ.path.ordered,
    intervalIntegral.integral_of_le γ.path.ordered]
  exact MeasureTheory.integral_congr_ae heq

theorem seam_neighborhood_integral_tendsto :
    Specs.D12Complex.Ch04.CellBoundaryContour.seam_neighborhood_integral_tendsto_type := by
  intro γ Z hZ U hU hshrink q hq
  let G := IccExtend γ.path.ordered γ.path.onInterval
  let F := fun t => q (γ t) * deriv γ t
  let μ := volume.restrict (Ioc γ.path.a γ.path.b)
  have hG : Continuous G := γ.path.onInterval.continuous.Icc_extend'
  have hA (n : ℕ) : MeasurableSet (G ⁻¹' U n) := (hU n).preimage hG.measurable
  have hf : Integrable F μ :=
    (C1Partition.parameter_integrable γ.path γ.partition q hq).1
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun n => (G ⁻¹' U n).indicator F t)
      atTop (nhds (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae (deriv_zero_ae_on_countable_preimage γ Z hZ),
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    have hGt : G t = γ t := IccExtend_of_mem γ.path.ordered _ ⟨hmem.1.le, hmem.2⟩
    by_cases hz : γ t ∈ Z
    · have hzero : F t = 0 := by simp [F, ht hz]
      have hall : (fun n => (G ⁻¹' U n).indicator F t) = fun _ => (0 : ℂ) := by
        funext n
        simp [Set.indicator, hzero]
      rw [hall]
      exact tendsto_const_nhds
    · apply tendsto_const_nhds.congr'
      filter_upwards [hshrink (γ t) hz] with n hn
      simp [Set.indicator, hGt, hn]
  have h := tendsto_integral_of_dominated_convergence (fun t => ‖F t‖)
    (fun n => hf.aestronglyMeasurable.indicator (hA n)) hf.norm
    (fun n => Filter.Eventually.of_forall (fun t => norm_indicator_le_norm_self _ _)) hlim
  simp only [integral_zero] at h
  have heq (n : ℕ) : γ.integral ((U n).indicator q) =
      ∫ t, (G ⁻¹' U n).indicator F t ∂μ := by
    rw [path_indicator_formula γ (U n) (hU n) q hq,
      intervalIntegral.integral_of_le γ.path.ordered]
  exact h.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm))

theorem chain_integral_congr_off_countable :
    Specs.D12Complex.Ch04.CellBoundaryContour.chain_integral_congr_off_countable_type := by
  intro Γ Z hZ q r heq
  unfold IntegralChain.integral Finsupp.sum
  apply Finset.sum_congr rfl
  intro γ hγ
  dsimp only
  congr 1
  apply path_integral_congr_off_countable γ Z hZ q r
  intro z hz
  exact heq ⟨⟨γ, hγ, hz.1⟩, hz.2⟩

theorem seam_neighborhood_chain_integral_tendsto :
    Specs.D12Complex.Ch04.CellBoundaryContour.seam_neighborhood_chain_integral_tendsto_type := by
  intro Γ Z hZ U hU hshrink q hq
  have h (γ : PiecewiseC1Path) (hγ : γ ∈ Γ.support) :
      Tendsto (fun n => (Γ γ : ℂ) * γ.integral ((U n).indicator q))
        atTop (nhds ((Γ γ : ℂ) * 0)) := by
    apply tendsto_const_nhds.mul
    apply seam_neighborhood_integral_tendsto γ Z hZ U hU hshrink q
    exact hq.mono (fun z hz => ⟨γ, hγ, hz⟩)
  have hs := tendsto_finsetSum Γ.support h
  simpa only [IntegralChain.integral, Finsupp.sum, mul_zero, Finset.sum_const_zero] using hs

theorem ambient_one_seam_countable :
    Specs.D12Complex.Ch04.CellBoundaryContour.ambient_one_seam_countable_type := by
  intro n Z
  obtain ⟨P, hP, hcover⟩ := Z.cover
  have hp (p : Specs.D04.C15.FiniteGeometricUnionIntegral.Model.CompactSeam 1 n) :
      (p.map '' p.parameter).Countable := by
    have hdim : p.dim = 0 := by have := p.lower; omega
    have : Subsingleton (E p.dim) := by rw [hdim]; infer_instance
    exact (Set.Countable.of_subsingleton p.parameter).image p.map
  have : Countable P := hP.to_subtype
  exact (Set.countable_iUnion (fun p : P => hp p.val)).mono hcover

theorem ambient_seam_chain_integral_tendsto :
    Specs.D12Complex.Ch04.CellBoundaryContour.ambient_seam_chain_integral_tendsto_type := by
  intro Γ Z ε hε q hq
  have hZ : (complexCoordinates.symm '' Z.carrier).Countable :=
    (ambient_one_seam_countable Z).image complexCoordinates.symm
  have hclosed : IsClosed (complexCoordinates.symm '' Z.carrier) :=
    (Z.isCompact.image complexCoordinates.symm.toContinuousLinearEquiv.continuous).isClosed
  apply seam_neighborhood_chain_integral_tendsto Γ _ hZ
    (fun n => Metric.thickening (ε n) (complexCoordinates.symm '' Z.carrier))
    (fun _ => Metric.isOpen_thickening.measurableSet) _ q hq
  intro z hz
  exact hε.eventually (p := fun r => z ∉ Metric.thickening r
    (complexCoordinates.symm '' Z.carrier))
    (Metric.eventually_notMem_thickening_of_infEDist_pos (by rwa [hclosed.closure_eq]))

theorem seam_multiplier_integral_tendsto :
    Specs.D12Complex.Ch04.CellBoundaryContour.seam_multiplier_integral_tendsto_type := by
  intro γ Z hZ A hA hbound hlim q hq
  let F := fun t => q (γ t) * deriv γ t
  let μ := volume.restrict (Ioc γ.path.a γ.path.b)
  have hf : Integrable F μ :=
    (C1Partition.parameter_integrable γ.path γ.partition q hq).1
  have hn (n : ℕ) : Integrable (fun t => A n (γ t) * F t) μ := by
    have h := (C1Partition.parameter_integrable γ.path γ.partition
      (fun z => A n z * q z) ((hA n).mul hq)).1
    simpa only [F, μ, IntegrableOn, mul_assoc] using h
  have hb (n : ℕ) : ∀ᵐ t ∂μ, ‖A n (γ t) * F t‖ ≤ ‖F t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbound n _ ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩)
  have hl : ∀ᵐ t ∂μ, Tendsto (fun n => A n (γ t) * F t) atTop (nhds (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae (deriv_zero_ae_on_countable_preimage γ Z hZ),
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    by_cases hz : γ t ∈ Z
    · have hzero : F t = 0 := by simp [F, ht hz]
      simpa only [hzero, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
    · have h := (hlim _ ⟨⟨t, ⟨hmem.1.le, hmem.2⟩, rfl⟩, hz⟩).mul
        (tendsto_const_nhds (x := F t))
      simpa only [zero_mul] using h
  have h := tendsto_integral_of_dominated_convergence (fun t => ‖F t‖)
    (fun n => (hn n).aestronglyMeasurable) hf.norm hb hl
  simp only [integral_zero] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  change (∫ t, A n (γ t) * F t ∂μ) = γ.partition.integral (fun z => A n z * q z)
  rw [C1Partition.integral_eq_intervalIntegral γ.path γ.partition
      (fun z => A n z * q z) ((hA n).mul hq),
    intervalIntegral.integral_of_le γ.path.ordered]
  simp only [F, μ, mul_assoc]

theorem seam_multiplier_chain_integral_tendsto :
    Specs.D12Complex.Ch04.CellBoundaryContour.seam_multiplier_chain_integral_tendsto_type := by
  intro Γ Z hZ A hA hbound hlim q hq
  have h (γ : PiecewiseC1Path) (hγ : γ ∈ Γ.support) :
      Tendsto (fun n => (Γ γ : ℂ) * γ.integral (fun z => A n z * q z))
        atTop (nhds ((Γ γ : ℂ) * 0)) := by
    have hsub : γ.trace ⊆ Γ.trace := fun z hz => ⟨γ, hγ, hz⟩
    apply tendsto_const_nhds.mul
    exact seam_multiplier_integral_tendsto γ Z hZ A
      (fun n => (hA n).mono hsub) (fun n z hz => hbound n z (hsub hz))
      (fun z hz => hlim z ⟨hsub hz.1, hz.2⟩) q (hq.mono hsub)
  have hs := tendsto_finsetSum Γ.support h
  simpa only [IntegralChain.integral, Finsupp.sum, mul_zero, Finset.sum_const_zero] using hs

theorem finite_arc_selection_away_seams :
    Specs.D12Complex.Ch04.CellBoundaryContour.finite_arc_selection_away_seams_type := by
  intro γ ι V U g a b W hV hU hcover htrace hreg
  classical
  let C : Option ι → Set ℂ := fun j => j.elim V U
  have hC (j : Option ι) : IsOpen (C j) := by
    cases j with
    | none => exact hV
    | some j => exact hU j
  have hcoverC : γ.trace ⊆ ⋃ j, C j := by
    intro z hz
    rcases hcover hz with hzV | hzU
    · exact mem_iUnion.mpr ⟨none, hzV⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hzU
      exact mem_iUnion.mpr ⟨some j, hj⟩
  obtain ⟨n, node, select, δ, hm, ha, hb, hδ, hsum⟩ :=
    finite_subpath_selection γ C hC hcoverC
  have hδtrace (k : Fin n) : (δ k).trace ⊆ γ.trace := by
    rintro z ⟨t, ht, rfl⟩
    have ht' : t ∈ Icc (node k.castSucc) (node k.succ) := by
      simpa only [(hδ k).1, (hδ k).2.1] using ht
    refine ⟨t, ?_, ((hδ k).2.2.1 ht').symm⟩
    constructor
    · rw [← ha]
      exact (hm (Fin.zero_le _)).trans ht'.1
    · rw [← hb]
      exact ht'.2.trans (hm (Fin.le_last _))
  have hnone (k : Fin n) (hk : select k = none) : (δ k).trace ⊆ V := by
    simpa only [hk, C, Option.elim_none] using (hδ k).2.2.2
  refine ⟨n, node, select, δ, hm, ha, hb,
    fun k => ⟨(hδ k).1, (hδ k).2.1, (hδ k).2.2.1, hδtrace k⟩,
    hnone, ?_, ?_⟩
  · intro k j hk
    have hsub : (δ k).trace ⊆ U j := by
      simpa only [hk, C, Option.elim_some] using (hδ k).2.2.2
    refine ⟨hsub, ?_⟩
    exact trace_regular_arc_integral (δ k) (g j) (a j) (b j) (W j)
      (hreg j).1 (hreg j).2.1 (hreg j).2.2.1 (hreg j).2.2.2.1
      (hreg j).2.2.2.2 (fun z hz => htrace j ⟨hδtrace k hz, hsub hz⟩)
  · intro q hq hzero
    rw [hsum q hq]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    have hk' : select k = none := by
      cases hs : select k with
      | none => rfl
      | some j => simp [hs] at hnot
    change (δ k).partition.integral q = 0
    unfold C1Partition.integral
    apply Finset.sum_eq_zero
    intro l hl
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t ht
    have hmem : t ∈ (δ k).partition.pieceSet l := by
      have hlt := (δ k).partition.piece_lt l
      have ht' : t ∈ Ioc ((δ k).partition.node l.castSucc)
          ((δ k).partition.node l.succ) := by
        simpa only [uIoc_of_le hlt.le] using ht
      exact ⟨ht'.1.le, ht'.2⟩
    have hpath : δ k t ∈ (δ k).trace :=
      ⟨t, (δ k).partition.piece_subset l hmem, rfl⟩
    have hz : q (δ k t) = 0 := hzero ⟨hδtrace k hpath, hnone k hk' hpath⟩
    simp [hz]

open scoped ContDiff

theorem smooth_seam_cutoffs :
    Specs.D12Complex.Ch04.CellBoundaryContour.smooth_seam_cutoffs_type := by
  intro Z hZ
  obtain ⟨f, hsupport, hf, hbound⟩ :=
    hZ.isOpen_compl.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  let B : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let A : ℕ → ℂ → ℝ := fun n z => B (((n : ℝ) + 1) * f z)
  let V : ℕ → Set ℂ := fun n =>
    (fun z => ((n : ℝ) + 1) * f z) ⁻¹' Metric.ball 0 1
  refine ⟨A, V, fun n => B.contDiff.comp (contDiff_const.mul hf),
    fun n z => ⟨B.nonneg, B.le_one⟩, ?_, ?_⟩
  · intro n
    refine ⟨Metric.isOpen_ball.preimage (continuous_const.mul hf.continuous), ?_, ?_⟩
    · intro z hz
      have hfz : f z = 0 := by
        apply Function.notMem_support.mp
        rwa [hsupport, mem_compl_iff, not_not]
      simp [V, hfz]
    · intro z hz
      exact B.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  · intro z hz
    have hfz : 0 < f z := by
      have hne : f z ≠ 0 := by
        change z ∈ Function.support f
        rwa [hsupport]
      exact lt_of_le_of_ne (hbound (mem_range_self z)).1 hne.symm
    have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * f z) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hfz
    filter_upwards [hlim.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
    apply B.zero_of_le_dist
    change 2 ≤ dist (((n : ℝ) + 1) * f z) 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    exact hn

private theorem chain_field_sub (Γ : IntegralChain) (q r : ℂ → ℂ)
    (hq : ContinuousOn q Γ.trace) (hr : ContinuousOn r Γ.trace) :
    Γ.integral (fun z => q z - r z) = Γ.integral q - Γ.integral r := by
  unfold IntegralChain.integral Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hsub : γ.trace ⊆ Γ.trace := fun z hz => ⟨γ, hγ, hz⟩
  have hq' := hq.mono hsub
  have hr' := hr.mono hsub
  have hpath : γ.integral (fun z => q z - r z) = γ.integral q - γ.integral r := by
    change γ.partition.integral (q - r) = γ.partition.integral q - γ.partition.integral r
    rw [C1Partition.integral_eq_intervalIntegral γ.path γ.partition _ (hq'.sub hr'),
      C1Partition.integral_eq_intervalIntegral γ.path γ.partition _ hq',
      C1Partition.integral_eq_intervalIntegral γ.path γ.partition _ hr']
    simp only [Pi.sub_apply, sub_mul]
    exact intervalIntegral.integral_sub
      (C1Partition.parameter_integrable γ.path γ.partition q hq')
      (C1Partition.parameter_integrable γ.path γ.partition r hr')
  dsimp only
  rw [hpath, mul_sub]

theorem smooth_seam_removal :
    Specs.D12Complex.Ch04.CellBoundaryContour.smooth_seam_removal_type := by
  intro Γ Z hclosed hcount
  obtain ⟨A, V, hA, hb, hV, haway⟩ := smooth_seam_cutoffs Z hclosed
  let χ : ℕ → ℂ → ℝ := fun n z => 1 - A n z
  refine ⟨χ, V, fun n => contDiff_const.sub (hA n),
    fun n z => ⟨sub_nonneg.mpr (hb n z).2, by linarith [(hb n z).1]⟩,
    fun n => ⟨(hV n).1, (hV n).2.1, fun z hz => by
      dsimp only [χ]; rw [(hV n).2.2 hz]; simp⟩, ?_⟩
  intro q hq
  have hcont (n : ℕ) : ContinuousOn (fun z => (A n z : ℂ)) Γ.trace :=
    Complex.continuous_ofReal.comp_continuousOn (hA n).continuous.continuousOn
  have hlim := seam_multiplier_chain_integral_tendsto Γ Z hcount
    (fun n z => (A n z : ℂ)) hcont (fun n z _ => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hb n z).1]
      exact (hb n z).2) (fun z hz => by
        apply tendsto_const_nhds.congr'
        filter_upwards [haway z hz.2] with n hn
        simp [hn]) q hq
  have heq (n : ℕ) : Γ.integral (fun z => (χ n z : ℂ) * q z) =
      Γ.integral q - Γ.integral (fun z => (A n z : ℂ) * q z) := by
    have he : (fun z => (χ n z : ℂ) * q z) =
        (fun z => q z - (A n z : ℂ) * q z) := by
      funext z
      simp only [χ, Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
    rw [he]
    exact chain_field_sub Γ q _ hq ((hcont n).mul hq)
  have h := (tendsto_const_nhds (x := Γ.integral q)).sub hlim
  simp only [sub_zero] at h
  exact h.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm))

theorem chain_comparison_of_smooth_seam_removal :
    Specs.D12Complex.Ch04.CellBoundaryContour.chain_comparison_of_smooth_seam_removal_type := by
  intro Γ Δ Z hclosed hcount q hq heq
  obtain ⟨A, W, hA, hbound, hW, haway⟩ := smooth_seam_cutoffs Z hclosed
  have hcut (C : IntegralChain) (hc : ContinuousOn q C.trace) :
      Tendsto (fun n => C.integral (fun z => (1 - (A n z : ℂ)) * q z))
        atTop (nhds (C.integral q)) := by
    have hAc (n : ℕ) : ContinuousOn (fun z => (A n z : ℂ)) C.trace :=
      Complex.continuous_ofReal.comp_continuousOn (hA n).continuous.continuousOn
    have hz := seam_multiplier_chain_integral_tendsto C Z hcount
      (fun n z => (A n z : ℂ)) hAc (fun n z _ => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hbound n z).1]
        exact (hbound n z).2) (fun z hz => by
          apply tendsto_const_nhds.congr'
          filter_upwards [haway z hz.2] with n hn
          simp [hn]) q hc
    have h := (tendsto_const_nhds (x := C.integral q)).sub hz
    simp only [sub_zero] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro n
    simp_rw [sub_mul, one_mul]
    exact (chain_field_sub C q _ hc ((hAc n).mul hc)).symm
  have hΓ := hcut Γ (hq.mono subset_union_left)
  have hΔ := hcut Δ (hq.mono subset_union_right)
  have hsame (n : ℕ) : Γ.integral (fun z => (1 - (A n z : ℂ)) * q z) =
      Δ.integral (fun z => (1 - (A n z : ℂ)) * q z) := by
    have h := heq (fun z => 1 - A n z) (contDiff_const.sub (hA n))
      (fun z => ⟨sub_nonneg.mpr (hbound n z).2, by linarith [(hbound n z).1]⟩)
      ⟨W n, (hW n).1, (hW n).2.1, fun z hz => by
        change 1 - A n z = 0
        rw [(hW n).2.2 hz]; simp⟩
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using h
  exact tendsto_nhds_unique hΓ (hΔ.congr' (Filter.Eventually.of_forall (fun n => (hsame n).symm)))

private theorem directed_integrand (u v t : ℝ) (g : ℝ → ℂ) :
    (directedIntervalMultiplicity u v t : ℂ) * g t =
      (Ioc u v).indicator g t - (Ioc v u).indicator g t := by
  simp only [directedIntervalMultiplicity, Int.cast_sub, sub_mul]
  by_cases h₁ : t ∈ Ioc u v <;> by_cases h₂ : t ∈ Ioc v u <;>
    simp [Set.indicator, h₁, h₂]

private theorem directed_integrand_integrable (a b u v : ℝ) (hab : a ≤ b) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Icc a b)) :
    IntervalIntegrable (fun t => (directedIntervalMultiplicity u v t : ℂ) * g t)
      volume a b := by
  have hi : IntervalIntegrable g volume a b :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hab] using hg)
  have hi₁ : IntervalIntegrable ((Ioc u v).indicator g) volume a b :=
    ⟨hi.1.indicator measurableSet_Ioc, hi.2.indicator measurableSet_Ioc⟩
  have hi₂ : IntervalIntegrable ((Ioc v u).indicator g) volume a b :=
    ⟨hi.1.indicator measurableSet_Ioc, hi.2.indicator measurableSet_Ioc⟩
  simpa only [directed_integrand] using hi₁.sub hi₂

theorem directed_interval_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.directed_interval_integral_type := by
  intro a b u v hu hv g hg
  have hab : a ≤ b := hu.1.trans hu.2
  have hi : IntervalIntegrable g volume a b :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hab] using hg)
  have hi₁ : IntervalIntegrable ((Ioc u v).indicator g) volume a b :=
    ⟨hi.1.indicator measurableSet_Ioc, hi.2.indicator measurableSet_Ioc⟩
  have hi₂ : IntervalIntegrable ((Ioc v u).indicator g) volume a b :=
    ⟨hi.1.indicator measurableSet_Ioc, hi.2.indicator measurableSet_Ioc⟩
  have hind (s t : ℝ) (hs : a ≤ s) (ht : t ≤ b) :
      (∫ r in a..b, (Ioc s t).indicator g r) = ∫ r in Ioc s t, g r := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset, integral_indicator measurableSet_Ioc]
    intro r hr
    apply Ioc_subset_Ioc hs ht
    by_contra hmem
    exact hr (Set.indicator_of_notMem hmem g)
  simp_rw [directed_integrand]
  rw [intervalIntegral.integral_sub hi₁ hi₂, hind u v hu.1 hv.2, hind v u hv.1 hu.2]
  rfl

theorem finite_directed_incidence_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.finite_directed_incidence_integral_type := by
  intro a b n m u v x y c d huv hxy hinc g hg
  by_cases hab : a ≤ b
  swap
  · have hn : n = 0 := by
      by_contra hn
      have h := (huv ⟨0, Nat.pos_of_ne_zero hn⟩).1
      exact hab (h.1.trans h.2)
    have hm : m = 0 := by
      by_contra hm
      have h := (hxy ⟨0, Nat.pos_of_ne_zero hm⟩).1
      exact hab (h.1.trans h.2)
    subst n m
    simp
  have hsum (N : ℕ) (s t : Fin N → ℝ) (w : Fin N → ℤ)
      (hst : ∀ i, s i ∈ Icc a b ∧ t i ∈ Icc a b) :
      (∑ i, (w i : ℂ) * ∫ r in s i..t i, g r) =
        ∫ r in a..b, (∑ i, (w i : ℂ) *
          (directedIntervalMultiplicity (s i) (t i) r : ℂ)) * g r := by
    simp_rw [← directed_interval_integral a b _ _ (hst _).1 (hst _).2 g hg,
      ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro r hr
      simp only [Finset.sum_mul, mul_assoc]
    · intro i hi
      exact (directed_integrand_integrable a b (s i) (t i) hab g hg).const_mul _
  rw [hsum n u v c huv, hsum m x y d hxy]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  filter_upwards [hinc] with t ht
  have hc : (∑ i, (c i : ℂ) * (directedIntervalMultiplicity (u i) (v i) t : ℂ)) =
      ∑ j, (d j : ℂ) * (directedIntervalMultiplicity (x j) (y j) t : ℂ) := by
    exact_mod_cast ht
  rw [hc]

theorem arc_parameter_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.arc_parameter_integral_type := by
  intro η g a b V hV hsub hg hinj hreg htrace
  obtain ⟨φ, hφ, hmaps, heq, hsmooth, hint⟩ :=
    trace_regular_arc_integral η g a b V hV hsub hg hinj hreg htrace
  have hparam (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) :
      arcParameter g a b η t = φ t := by
    change Function.invFunOn g (Icc a b) (η t) = φ t
    rw [heq ht]
    exact hinj.leftInvOn_invFunOn (hmaps ht)
  refine ⟨fun t ht => by rw [hparam t ht]; exact hmaps ht, ?_⟩
  intro q hq
  rw [hparam η.path.a (left_mem_Icc.mpr η.path.ordered),
    hparam η.path.b (right_mem_Icc.mpr η.path.ordered)]
  exact hint q hq

theorem finite_arc_incidence_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.finite_arc_incidence_integral_type := by
  intro g a b V hV hsub hg hinj hreg n m η θ c d hη hθ hinc q hq
  have hη' (i : Fin n) := arc_parameter_integral (η i) g a b V
    hV hsub hg hinj hreg (hη i)
  have hθ' (j : Fin m) := arc_parameter_integral (θ j) g a b V
    hV hsub hg hinj hreg (hθ j)
  simp_rw [fun i => (hη' i).2 q hq, fun j => (hθ' j).2 q hq]
  apply finite_directed_incidence_integral a b n m
    (fun i => arcParameter g a b (η i) (η i).path.a)
    (fun i => arcParameter g a b (η i) (η i).path.b)
    (fun j => arcParameter g a b (θ j) (θ j).path.a)
    (fun j => arcParameter g a b (θ j) (θ j).path.b) c d
    (fun i => ⟨(hη' i).1 (left_mem_Icc.mpr (η i).path.ordered),
      (hη' i).1 (right_mem_Icc.mpr (η i).path.ordered)⟩)
    (fun j => ⟨(hθ' j).1 (left_mem_Icc.mpr (θ j).path.ordered),
      (hθ' j).1 (right_mem_Icc.mpr (θ j).path.ordered)⟩) hinc
    (fun s => q (g s) * deriv g s)
  exact (hq.comp (hg.continuousOn.mono hsub) (fun s hs => ⟨s, hs, rfl⟩)).mul
    ((hg.continuousOn_deriv_of_isOpen hV le_rfl).mono hsub)

theorem regular_values_on_interval :
    Specs.D12Complex.Ch04.CellBoundaryContour.regular_values_on_interval_type := by
  intro φ c d B hB hcont hdiff
  let C : Set ℝ := {t | t ∈ Icc c d ∧ t ∉ B ∧ deriv φ t = 0}
  have hcrit : volume (φ '' C) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun _ => (0 : ℝ →L[ℝ] ℝ))
    · intro t ht
      have hd := (hdiff t ⟨ht.1, ht.2.1⟩).hasDerivAt
      rw [ht.2.2] at hd
      simpa using hd.hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      simp
  have hbad : volume (φ '' B) = 0 := (hB.image φ).measure_zero volume
  have hgood : ∀ᵐ s : ℝ, s ∉ φ '' B ∧ s ∉ φ '' C := by
    have h₁ : ∀ᵐ s : ℝ, s ∉ φ '' B := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hbad
    have h₂ : ∀ᵐ s : ℝ, s ∉ φ '' C := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hcrit
    exact h₁.and h₂
  filter_upwards [hgood] with s hs
  have hreg (t : ℝ) (ht : t ∈ Icc c d) (he : φ t = s) :
      t ∉ B ∧ DifferentiableAt ℝ φ t ∧ deriv φ t ≠ 0 := by
    have htB : t ∉ B := fun h => hs.1 ⟨t, h, he⟩
    exact ⟨htB, hdiff t ⟨ht, htB⟩,
      fun hz => hs.2 ⟨t, ⟨ht, htB, hz⟩, he⟩⟩
  refine ⟨?_, hreg⟩
  have hclosed : IsClosed {t : ℝ | t ∈ Icc c d ∧ φ t = s} :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  apply (isCompact_Icc.of_isClosed_subset hclosed (fun _ ht => ht.1)).finite
  apply isDiscrete_iff_nhdsNE.mpr
  intro t ht
  apply Filter.inf_principal_eq_bot.mpr
  have hd := (hreg t ht.1 ht.2).2.1.hasDerivAt.eventually_ne (c := s)
    (hreg t ht.1 ht.2).2.2
  exact hd.mono (fun u hu hmem => hu hmem.2)

theorem arc_parameter_regular :
    Specs.D12Complex.Ch04.CellBoundaryContour.arc_parameter_regular_type := by
  intro η g a b V hV hsub hg hinj hreg htrace
  obtain ⟨φ, hφ, hmaps, heq, hsmooth, _⟩ :=
    trace_regular_arc_integral η g a b V hV hsub hg hinj hreg htrace
  have hparam : EqOn (arcParameter g a b η) φ (Icc η.path.a η.path.b) := by
    intro t ht
    change Function.invFunOn g (Icc a b) (η t) = φ t
    rw [heq ht]
    exact hinj.leftInvOn_invFunOn (hmaps ht)
  refine ⟨hφ.congr (fun _ ht => hparam ht), ?_, ?_, ?_⟩
  · intro t ht
    rw [hparam ht]
    exact hmaps ht
  · intro t ht
    rw [Function.comp_apply, hparam ht]
    exact heq ht
  · intro i
    exact (hsmooth i).congr (fun t ht => hparam (η.partition.piece_subset i ht))

/-- A point away from all nodes lies in the interior of one actual piece. -/
theorem finite_partition_interior (n : ℕ) (node : Fin (n + 1) → ℝ)
    (hm : Monotone node) (t : ℝ) (ht : t ∈ Icc (node 0) (node (Fin.last n)))
    (hne : t ∉ Set.range node) :
    ∃ i : Fin n, t ∈ Ioo (node i.castSucc) (node i.succ) := by
  induction n with
  | zero =>
    have he : t = node 0 := le_antisymm ht.2 ht.1
    exact (hne ⟨0, he.symm⟩).elim
  | succ n ih =>
    by_cases h : t < node 1
    · refine ⟨0, ?_, h⟩
      exact lt_of_le_of_ne ht.1 (fun he => hne ⟨0, he⟩)
    · have htail : t ∈ Icc ((fun i : Fin (n + 1) => node i.succ) 0)
          ((fun i : Fin (n + 1) => node i.succ) (Fin.last n)) :=
        ⟨le_of_not_gt h, ht.2⟩
      obtain ⟨i, hi⟩ := ih (fun i => node i.succ)
        (fun i j hij => hm (by simpa using hij)) htail
        (fun ⟨i, hi⟩ => hne ⟨i.succ, hi⟩)
      exact ⟨i.succ, by simpa only [Fin.succ_castSucc] using hi⟩

theorem arc_regular_values :
    Specs.D12Complex.Ch04.CellBoundaryContour.arc_regular_values_type := by
  intro η g a b V hV hsub hg hinj hreg htrace
  obtain ⟨hφ, hmaps, hfactor, hpieces⟩ :=
    arc_parameter_regular η g a b V hV hsub hg hinj hreg htrace
  let φ := arcParameter g a b η
  have hdiff (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b \ Set.range η.partition.node) :
      DifferentiableAt ℝ φ t := by
    obtain ⟨i, hi⟩ := finite_partition_interior η.partition.count η.partition.node
      η.partition.strictMono.monotone t (by simpa only [η.partition.first,
        η.partition.last] using ht.1) ht.2
    exact (hpieces i).differentiableOn (by norm_num) t ⟨hi.1.le, hi.2.le⟩
      |>.differentiableAt (Icc_mem_nhds hi.1 hi.2)
  have hae := regular_values_on_interval φ η.path.a η.path.b _
    (Set.finite_range η.partition.node).countable hφ hdiff
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Icc] with s hs hsab
  have hiff (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) :
      η t = g s ↔ φ t = s := by
    rw [hfactor ht]
    exact ⟨fun h => hinj (hmaps ht) hsab h, fun h => congrArg g h⟩
  have heq : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s} =
      {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ φ t = s} := by
    ext t
    exact and_congr_right (fun ht => hiff t ht)
  refine ⟨heq.symm ▸ hs.1, ?_⟩
  intro t ht he
  obtain ⟨hnot, hdφ, hφne⟩ := hs.2 t ht ((hiff t ht).mp he)
  have htleft : η.path.a < t := lt_of_le_of_ne ht.1 (fun h =>
    hnot ⟨0, η.partition.first.trans h⟩)
  have htright : t < η.path.b := lt_of_le_of_ne ht.2 (fun h =>
    hnot ⟨Fin.last _, η.partition.last.trans h.symm⟩)
  have hdg : DifferentiableAt ℝ g (φ t) :=
    (hg.contDiffAt (hV.mem_nhds (hsub (hmaps ht)))).differentiableAt (by norm_num)
  have hlocal : η =ᶠ[nhds t] g ∘ φ :=
    Filter.eventuallyEq_of_mem (Icc_mem_nhds htleft htright) hfactor
  have hdη : HasDerivAt η (deriv φ t • deriv g (φ t)) t :=
    (hdg.hasDerivAt.scomp t hdφ.hasDerivAt).congr_of_eventuallyEq hlocal
  refine ⟨⟨htleft, htright⟩, hnot, hdη.differentiableAt, ?_⟩
  rw [hdη.deriv]
  exact smul_ne_zero hφne (hreg _ (hmaps ht))

private def crossingValue (φ : ℝ → ℝ) (s t : ℝ) : ℤ :=
  if s < φ t then 1 else if φ t = s ∧ deriv φ t < 0 then 1 else 0

private def parameterStep (r t : ℝ) : ℤ := if r < t then 1 else 0

private theorem crossingValue_eventually (φ : ℝ → ℝ) (s t : ℝ) (S : Set ℝ)
    (hc : ContinuousWithinAt φ S t) (hne : φ t ≠ s) :
    ∀ᶠ u in nhdsWithin t S, crossingValue φ s u = crossingValue φ s t := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [hc.eventually (gt_mem_nhds h)] with u hu
    simp [crossingValue, not_lt.mpr hu.le, hu.ne, not_lt.mpr h.le, h.ne]
  · filter_upwards [hc.eventually (lt_mem_nhds h)] with u hu
    simp [crossingValue, hu, h]

private theorem parameterStep_eventually (r t : ℝ) (hne : r ≠ t) :
    ∀ᶠ u in nhds t, parameterStep r u = parameterStep r t := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [Ioi_mem_nhds h] with u hu
    change r < u at hu
    simp [parameterStep, hu, h]
  · filter_upwards [Iio_mem_nhds h] with u hu
    change u < r at hu
    simp [parameterStep, not_lt.mpr hu.le, not_lt.mpr h.le]

private theorem crossingValue_jump (φ : ℝ → ℝ) (s t : ℝ)
    (he : φ t = s) (hd : HasDerivAt φ (deriv φ t) t) (hne : deriv φ t ≠ 0) :
    ∀ᶠ u in nhds t,
      crossingValue φ s u - (if 0 < deriv φ t then (1 : ℤ) else -1) * parameterStep t u =
        crossingValue φ s t := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hev : ∀ᶠ u in nhdsWithin t ({t}ᶜ), slope φ t u < 0 :=
      hd.tendsto_slope.eventually (gt_mem_nhds hneg)
    have hsign : ∀ᶠ u in nhds t, u ≠ t → (φ u - s) / (u - t) < 0 := by
      simpa only [nhdsWithin, eventually_inf_principal, mem_compl_iff,
        mem_singleton_iff, slope_def_field, he] using hev
    filter_upwards [hsign] with u hu
    by_cases hut : u = t
    · subst u
      simp [crossingValue, parameterStep, he, hneg, not_lt.mpr hneg.le]
    · have hslope := hu hut
      rcases lt_or_gt_of_ne hut with hlt | hgt
      · have hf : s < φ u := by
          have hh := (div_neg_iff.mp hslope)
          rcases hh with hh | hh
          · linarith [hh.1]
          · exact (not_lt_of_ge (sub_nonpos.mpr hlt.le) hh.2).elim
        simp [crossingValue, parameterStep, hf, not_lt.mpr hlt.le, he, hneg,
          not_lt.mpr hneg.le]
      · have hf : φ u < s := by
          rcases div_neg_iff.mp hslope with hh | hh
          · exact (not_lt_of_ge (sub_nonneg.mpr hgt.le) hh.2).elim
          · linarith [hh.1]
        simp [crossingValue, parameterStep, not_lt.mpr hf.le, hf.ne, hgt, he, hneg,
          not_lt.mpr hneg.le]
  · have hev : ∀ᶠ u in nhdsWithin t ({t}ᶜ), 0 < slope φ t u :=
      hd.tendsto_slope.eventually (lt_mem_nhds hpos)
    have hsign : ∀ᶠ u in nhds t, u ≠ t → 0 < (φ u - s) / (u - t) := by
      simpa only [nhdsWithin, eventually_inf_principal, mem_compl_iff,
        mem_singleton_iff, slope_def_field, he] using hev
    filter_upwards [hsign] with u hu
    by_cases hut : u = t
    · subst u
      simp [crossingValue, parameterStep, he, hpos, not_lt.mpr hpos.le]
    · have hslope := hu hut
      rcases lt_or_gt_of_ne hut with hlt | hgt
      · have hf : φ u < s := by
          rcases div_pos_iff.mp hslope with hh | hh
          · exact (not_lt_of_ge (sub_nonpos.mpr hlt.le) hh.2).elim
          · linarith [hh.1]
        simp [crossingValue, parameterStep, not_lt.mpr hf.le, hf.ne,
          not_lt.mpr hlt.le, he, hpos, not_lt.mpr hpos.le]
      · have hf : s < φ u := by
          rcases div_pos_iff.mp hslope with hh | hh
          · linarith [hh.1]
          · exact (not_lt_of_ge (sub_nonneg.mpr hgt.le) hh.2).elim
        simp [crossingValue, parameterStep, hf, hgt, he, hpos, not_lt.mpr hpos.le]

theorem regular_value_signed_count (φ : ℝ → ℝ) (c d s : ℝ) (hcd : c ≤ d)
    (hc : ContinuousOn φ (Icc c d)) (hleft : φ c ≠ s) (hright : φ d ≠ s)
    (hreg : ∀ t ∈ Icc c d, φ t = s → DifferentiableAt ℝ φ t ∧ deriv φ t ≠ 0)
    (hf : {t : ℝ | t ∈ Icc c d ∧ φ t = s}.Finite) :
    (∑ t ∈ hf.toFinset, if 0 < deriv φ t then (1 : ℤ) else -1) =
      directedIntervalMultiplicity (φ c) (φ d) s := by
  classical
  let R := hf.toFinset
  let w : ℝ → ℤ := fun t => if 0 < deriv φ t then 1 else -1
  let F : ℝ → ℤ := fun t => crossingValue φ s t - ∑ r ∈ R, w r * parameterStep r t
  have hR (t : ℝ) : t ∈ R ↔ t ∈ Icc c d ∧ φ t = s := hf.mem_toFinset
  have hsum (t : ℝ) (J : Finset ℝ) (hJ : t ∉ J) :
      ContinuousAt (fun u => ∑ r ∈ J, w r * parameterStep r u) t := by
    apply tendsto_finsetSum
    intro r hr
    apply continuousAt_const.mul
    exact continuousAt_const.congr_of_eventuallyEq
      (parameterStep_eventually r t (fun he => hJ (he ▸ hr)))
  have hF : ContinuousOn F (Icc c d) := by
    intro t ht
    by_cases he : φ t = s
    · have htR : t ∈ R := (hR t).mpr ⟨ht, he⟩
      have hjump := crossingValue_jump φ s t he (hreg t ht he).1.hasDerivAt (hreg t ht he).2
      have hj : ContinuousAt (fun u => crossingValue φ s u - w t * parameterStep t u) t :=
        continuousAt_const.congr_of_eventuallyEq hjump
      have hrest := hsum t (R.erase t) (Finset.notMem_erase t R)
      have heq : F = fun u => (crossingValue φ s u - w t * parameterStep t u) -
          ∑ r ∈ R.erase t, w r * parameterStep r u := by
        funext u
        dsimp only [F]
        rw [← Finset.sum_erase_add _ _ htR]
        ring
      rw [heq]
      exact (hj.sub hrest).continuousWithinAt
    · have hcross : ContinuousWithinAt (crossingValue φ s) (Icc c d) t :=
        continuousWithinAt_const.congr_of_eventuallyEq
          (crossingValue_eventually φ s t (Icc c d) (hc t ht) he) rfl
      exact hcross.sub ((hsum t R (fun h => he ((hR t).mp h).2)).continuousWithinAt)
  have hconstant := isPreconnected_Icc.constant hF (left_mem_Icc.mpr hcd) (right_mem_Icc.mpr hcd)
  have hsumc : ∑ r ∈ R, w r * parameterStep r c = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [parameterStep, not_lt.mpr ((hR r).mp hr).1.1]
  have hsumd : (∑ r ∈ R, w r * parameterStep r d) = ∑ r ∈ R, w r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrd : r < d := lt_of_le_of_ne ((hR r).mp hr).1.2
      (fun he => hright (he ▸ ((hR r).mp hr).2))
    simp [parameterStep, hrd]
  change crossingValue φ s c - (∑ r ∈ R, w r * parameterStep r c) =
    crossingValue φ s d - (∑ r ∈ R, w r * parameterStep r d) at hconstant
  rw [hsumc, hsumd, sub_zero] at hconstant
  have hcount : (∑ r ∈ R, w r) = crossingValue φ s d - crossingValue φ s c := by
    omega
  change (∑ r ∈ R, w r) = _
  rw [hcount]
  unfold crossingValue directedIntervalMultiplicity
  simp only [hleft, hright, false_and, ite_false, Set.indicator, mem_Ioc]
  split_ifs <;> grind

theorem arc_signed_multiplicity :
    Specs.D12Complex.Ch04.CellBoundaryContour.arc_signed_multiplicity_type := by
  intro η g a b V hV hsub hg hinj hreg htrace
  classical
  obtain ⟨hφ, hmaps, hfactor, hpieces⟩ :=
    arc_parameter_regular η g a b V hV hsub hg hinj hreg htrace
  let φ := arcParameter g a b η
  have hdiff (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b \ Set.range η.partition.node) :
      DifferentiableAt ℝ φ t := by
    obtain ⟨i, hi⟩ := finite_partition_interior η.partition.count η.partition.node
      η.partition.strictMono.monotone t (by simpa only [η.partition.first,
        η.partition.last] using ht.1) ht.2
    exact (hpieces i).differentiableOn (by norm_num) t ⟨hi.1.le, hi.2.le⟩
      |>.differentiableAt (Icc_mem_nhds hi.1 hi.2)
  have hae := regular_values_on_interval φ η.path.a η.path.b _
    (Set.finite_range η.partition.node).countable hφ hdiff
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Icc] with s hs hsab
  have hiff (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) :
      η t = g s ↔ φ t = s := by
    rw [hfactor ht]
    exact ⟨fun h => hinj (hmaps ht) hsab h, fun h => congrArg g h⟩
  have heq : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s} =
      {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ φ t = s} := by
    ext t
    exact and_congr_right (fun ht => hiff t ht)
  have hf : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s}.Finite := heq.symm ▸ hs.1
  have hfinset : hf.toFinset = hs.1.toFinset := by
    ext t
    simp only [Set.Finite.mem_toFinset]
    exact and_congr_right (fun ht => hiff t ht)
  have hleft : φ η.path.a ≠ s := fun he =>
    (hs.2 _ (left_mem_Icc.mpr η.path.ordered) he).1 ⟨0, η.partition.first⟩
  have hright : φ η.path.b ≠ s := fun he =>
    (hs.2 _ (right_mem_Icc.mpr η.path.ordered) he).1 ⟨Fin.last _, η.partition.last⟩
  unfold arcSignedMultiplicity
  rw [dite_eq_left hf, hfinset]
  have hcount := regular_value_signed_count φ η.path.a η.path.b s η.path.ordered hφ hleft hright
    (fun t ht he => (hs.2 t ht he).2) hs.1
  apply Eq.trans _ hcount
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := hs.1.mem_toFinset.mp ht
  have hne := (hs.2 t ht'.1 ht'.2).2.2
  by_cases hp : 0 < deriv φ t
  · simp only [φ] at hp
    simp [φ, hp]
  · have hn : deriv φ t < 0 := lt_of_le_of_ne (le_of_not_gt hp) hne
    simp only [φ] at hp hn
    simp [φ, hp, hn]

theorem arc_occurrence_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.arc_occurrence_integral_type := by
  intro η g a b V hV hsub hg hinj hreg htrace q hq
  obtain ⟨hmaps, hint⟩ := arc_parameter_integral η g a b V hV hsub hg hinj hreg htrace
  have hleft := hmaps (left_mem_Icc.mpr η.path.ordered)
  have hright := hmaps (right_mem_Icc.mpr η.path.ordered)
  have hab : a ≤ b := hleft.1.trans hleft.2
  have hcont : ContinuousOn (fun s => q (g s) * deriv g s) (Icc a b) :=
    (hq.comp (hg.continuousOn.mono hsub) (fun s hs => ⟨s, hs, rfl⟩)).mul
      ((hg.continuousOn_deriv_of_isOpen hV le_rfl).mono hsub)
  rw [hint q hq, ← directed_interval_integral a b _ _ hleft hright _ hcont]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  have h := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
    (arc_signed_multiplicity η g a b V hV hsub hg hinj hreg htrace)
  filter_upwards [h] with s hs
  rw [hs]
  rfl

theorem finite_arc_occurrence_integral :
    Specs.D12Complex.Ch04.CellBoundaryContour.finite_arc_occurrence_integral_type := by
  intro g a b V hV hsub hg hinj hreg n m η θ c d hη hθ hinc q hq
  apply finite_arc_incidence_integral g a b V hV hsub hg hinj hreg n m η θ c d hη hθ _ q hq
  have hη' : ∀ᵐ s ∂volume.restrict (Ioc a b), ∀ i : Fin n,
      arcSignedMultiplicity g a b (η i) s = arcTraversalMultiplicity g a b (η i) s := by
    rw [ae_all_iff]
    intro i
    exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (arc_signed_multiplicity (η i) g a b V hV hsub hg hinj hreg (hη i))
  have hθ' : ∀ᵐ s ∂volume.restrict (Ioc a b), ∀ j : Fin m,
      arcSignedMultiplicity g a b (θ j) s = arcTraversalMultiplicity g a b (θ j) s := by
    rw [ae_all_iff]
    intro j
    exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (arc_signed_multiplicity (θ j) g a b V hV hsub hg hinj hreg (hθ j))
  filter_upwards [hinc, hη', hθ'] with s hs hηs hθs
  simpa only [hηs, hθs] using hs

theorem arc_velocity_relation :
    Specs.D12Complex.Ch04.CellBoundaryContour.arc_velocity_relation_type := by
  intro η g a b V hV hsub hg hinj hreg htrace t ht hnot
  obtain ⟨hφ, hmaps, hfactor, hpieces⟩ :=
    arc_parameter_regular η g a b V hV hsub hg hinj hreg htrace
  let φ := arcParameter g a b η
  obtain ⟨i, hi⟩ := finite_partition_interior η.partition.count η.partition.node
    η.partition.strictMono.monotone t (by simpa only [η.partition.first,
      η.partition.last] using ht) hnot
  have hdφ : DifferentiableAt ℝ φ t :=
    (hpieces i).differentiableOn (by norm_num) t ⟨hi.1.le, hi.2.le⟩
      |>.differentiableAt (Icc_mem_nhds hi.1 hi.2)
  have hdg : DifferentiableAt ℝ g (φ t) :=
    (hg.contDiffAt (hV.mem_nhds (hsub (hmaps ht)))).differentiableAt (by norm_num)
  have hlocal : η =ᶠ[nhds t] g ∘ φ :=
    Filter.eventuallyEq_of_mem (Icc_mem_nhds hi.1 hi.2)
      (hfactor.mono (η.partition.piece_subset i))
  exact (hdg.hasDerivAt.scomp t hdφ.hasDerivAt).congr_of_eventuallyEq hlocal


/-- A null set can be checked in neighborhoods, with no measurability premise. -/
theorem measure_zero_of_local_null (S : Set ℝ)
    (h : ∀ x ∈ S, ∃ U ∈ nhds x, volume (S ∩ U) = 0) : volume S = 0 := by
  classical
  choose! U hU hz using h
  obtain ⟨T, hT, hTS, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof S).elim_nhds_subcover U hU
  have hsub : S ⊆ ⋃ x ∈ T, S ∩ U x := by
    intro y hy
    obtain ⟨x, hxT, hx⟩ := mem_iUnion₂.mp (hcover hy)
    exact mem_iUnion₂.mpr ⟨x, hxT, hy, hx⟩
  exact measure_mono_null hsub (measure_biUnion_null_iff hT |>.mpr
    (fun x hx => hz x (hTS x hx)))

/-- Pullback of a null set through a real C1 function is null wherever its
actual scalar derivative is nonzero. Global injectivity is unnecessary. -/
theorem noncritical_preimage_null (f : ℝ → ℝ) (V N : Set ℝ)
    (hV : IsOpen V) (hf : ContDiffOn ℝ 1 f V) (hN : volume N = 0) :
    volume {x | x ∈ V ∧ f x ∈ N ∧ deriv f x ≠ 0} = 0 := by
  classical
  let S := {x | x ∈ V ∧ f x ∈ N ∧ deriv f x ≠ 0}
  apply measure_zero_of_local_null S
  intro x hx
  have hfx : ContDiffAt ℝ 1 f x := hf.contDiffAt (hV.mem_nhds hx.1)
  let hd := hfx.differentiableAt_one.hasDerivAt.hasFDerivAt_equiv hx.2.2
  let e := hfx.toOpenPartialHomeomorph f hd (by norm_num)
  have hxsource : x ∈ e.source :=
    hfx.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hinv : ContDiffAt ℝ 1 e.symm (f x) :=
    hfx.to_localInverse hd (by norm_num)
  obtain ⟨W, hW, hdiff⟩ := hinv.contDiffOn (m := 1) le_rfl (by simp)
  let U := e.source ∩ f ⁻¹' W
  have hUnhds : U ∈ nhds x := inter_mem (e.open_source.mem_nhds hxsource)
    (hfx.continuousAt hW)
  refine ⟨U, hUnhds, ?_⟩
  have hnull : volume (e.symm '' (N ∩ W)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((hdiff.differentiableOn (by norm_num)).mono inter_subset_right)
      (measure_mono_null inter_subset_left hN)
  apply measure_mono_null _ hnull
  rintro y ⟨hyS, hyU⟩
  exact ⟨f y, ⟨hyS.2.1, hyU.2⟩, e.left_inv hyU.1⟩

/-- A real projection of an original PC1 path is differentiable off its
original partition nodes, regardless of its stationary portions. -/
theorem projected_path_differentiable (η : PiecewiseC1Path) (L : ℂ →L[ℝ] ℝ)
    (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b)
    (hnot : t ∉ Set.range η.partition.node) :
    DifferentiableAt ℝ (L ∘ η) t := by
  obtain ⟨i, hi⟩ := finite_partition_interior η.partition.count η.partition.node
    η.partition.strictMono.monotone t (by simpa only [η.partition.first,
      η.partition.last] using ht) hnot
  have hη : DifferentiableAt ℝ η t :=
    ((η.partition.smooth i).differentiableOn (by norm_num) t ⟨hi.1.le, hi.2.le⟩).differentiableAt (Icc_mem_nhds hi.1 hi.2)
  exact L.differentiableAt.comp t hη

/-- Generic regular reference points have finite regular original fibers.
The original path need not lie in the reference curve, and the regular
reference curve itself need not be globally injective. -/
theorem regular_curve_visit_values (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (habV : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) :
    ∀ᵐ s ∂volume.restrict (Icc a b),
      {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s}.Finite ∧
      ∀ t ∈ Icc η.path.a η.path.b, η t = g s →
        t ∈ Ioo η.path.a η.path.b ∧ t ∉ Set.range η.partition.node ∧
        DifferentiableAt ℝ η t ∧ deriv η t ≠ 0 := by
  let good (L : ℂ →L[ℝ] ℝ) (y : ℝ) : Prop :=
    {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ L (η t) = y}.Finite ∧
      ∀ t ∈ Icc η.path.a η.path.b, L (η t) = y →
        t ∉ Set.range η.partition.node ∧
        DifferentiableAt ℝ (L ∘ η) t ∧ deriv (L ∘ η) t ≠ 0
  have hgood (L : ℂ →L[ℝ] ℝ) : ∀ᵐ y : ℝ, good L y :=
    regular_values_on_interval (L ∘ η) η.path.a η.path.b
      (Set.range η.partition.node) (Set.finite_range _).countable
      (L.continuous.comp_continuousOn η.path.continuousOn)
      (fun t ht => projected_path_differentiable η L t ht.1 ht.2)
  have hpull (L : ℂ →L[ℝ] ℝ) : ∀ᵐ s ∂volume.restrict (Icc a b),
      deriv (L ∘ g) s ≠ 0 → good L (L (g s)) := by
    have hbad : volume {y | ¬ good L y} = 0 := by
      simpa only [ae_iff] using hgood L
    have hn := noncritical_preimage_null (L ∘ g) V {y | ¬ good L y} hV
      (L.contDiff.comp_contDiffOn hg) hbad
    have hn' : ∀ᵐ s : ℝ, s ∈ V → deriv (L ∘ g) s ≠ 0 → good L (L (g s)) := by
      have he : ∀ᵐ s : ℝ, s ∉ {x | x ∈ V ∧ (L ∘ g) x ∈ {y | ¬ good L y} ∧
          deriv (L ∘ g) x ≠ 0} := by
        simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hn
      filter_upwards [he] with s hs hsV hd
      by_contra hh
      exact hs ⟨hsV, hh, hd⟩
    filter_upwards [ae_restrict_of_ae hn', ae_restrict_mem measurableSet_Icc] with s hs hsab
    exact hs (habV hsab)
  filter_upwards [hpull Complex.reCLM, hpull Complex.imCLM,
    ae_restrict_mem measurableSet_Icc] with s hre him hsab
  have hdg := (hg.contDiffAt (hV.mem_nhds (habV hsab))).differentiableAt_one.hasDerivAt
  have hproj (L : ℂ →L[ℝ] ℝ) : deriv (L ∘ g) s = L (deriv g s) :=
    (L.hasFDerivAt.comp_hasDerivAt s hdg).deriv
  have hex : ∃ L : ℂ →L[ℝ] ℝ, good L (L (g s)) := by
    by_cases hr : (deriv g s).re = 0
    · refine ⟨Complex.imCLM, him ?_⟩
      rw [hproj]
      intro hi
      exact hreg s hsab (Complex.ext hr hi)
    · exact ⟨Complex.reCLM, hre (by simpa only [hproj, Complex.reCLM_apply] using hr)⟩
  obtain ⟨L, hL⟩ := hex
  refine ⟨hL.1.subset (fun t ht => ⟨ht.1, congrArg L ht.2⟩), ?_⟩
  intro t ht he
  obtain ⟨hnot, hdiff, hne⟩ := hL.2 t ht (congrArg L he)
  obtain ⟨i, hi⟩ := finite_partition_interior η.partition.count η.partition.node
    η.partition.strictMono.monotone t (by simpa only [η.partition.first,
      η.partition.last] using ht) hnot
  have hη := ((η.partition.smooth i).differentiableOn (by norm_num) t ⟨hi.1.le, hi.2.le⟩).differentiableAt (Icc_mem_nhds hi.1 hi.2)
  refine ⟨?_, hnot, hη, ?_⟩
  · constructor
    · exact lt_of_le_of_ne ht.1 (fun he => hnot ⟨0, η.partition.first.trans he⟩)
    · exact lt_of_le_of_ne ht.2 (fun he => hnot ⟨Fin.last _, η.partition.last.trans he.symm⟩)
  · intro hz
    have hh := (L.hasFDerivAt.comp_hasDerivAt t hη.hasDerivAt).deriv
    rw [hz, map_zero] at hh
    exact hne hh


/-- Actual velocity counts are unchanged by the choice of recovered arc
coordinate on a regular injective arc. -/
theorem arc_tangent_signed_multiplicity (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hinj : InjOn g (Icc a b))
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (htrace : η.trace ⊆ g '' Icc a b) :
    ∀ᵐ s ∂volume.restrict (Icc a b),
      arcSignedMultiplicity g a b η s = tangentSignedMultiplicity η (g s) (deriv g s) := by
  classical
  have hmaps := (arc_parameter_regular η g a b V hV hsub hg hinj hreg htrace).2.1
  have hfactor := (arc_parameter_regular η g a b V hV hsub hg hinj hreg htrace).2.2.1
  filter_upwards [arc_regular_values η g a b V hV hsub hg hinj hreg htrace,
    ae_restrict_mem measurableSet_Icc] with s hs hsab
  unfold arcSignedMultiplicity tangentSignedMultiplicity
  rw [dite_eq_left hs.1, dite_eq_left hs.1]
  apply Finset.sum_congr rfl
  intro t ht
  have htf := hs.1.mem_toFinset.mp ht
  have hφ : arcParameter g a b η t = s :=
    hinj (hmaps htf.1) hsab ((hfactor htf.1).symm.trans htf.2)
  have hd := arc_velocity_relation η g a b V hV hsub hg hinj hreg htrace t htf.1
    (hs.2 t htf.1 htf.2).2.1
  have he : (deriv η t / deriv g s).re = deriv (arcParameter g a b η) t := by
    rw [hd.deriv, hφ, Complex.real_smul, mul_div_cancel_right₀ _ (hreg s hsab),
      Complex.ofReal_re]
  rw [he]

/-- Finite subdivision preserves actual signed occurrence counts away from
its finite set of endpoint images. Repeated nodes and degenerate pieces are
allowed. No curve-containment or velocity condition is assumed. -/
theorem tangent_signed_multiplicity_subdivision (η : PiecewiseC1Path)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (hm : Monotone node)
    (ha : node 0 = η.path.a) (hb : node (Fin.last n) = η.path.b)
    (δ : Fin n → PiecewiseC1Path)
    (hδ : ∀ i, (δ i).path.a = node i.castSucc ∧ (δ i).path.b = node i.succ ∧
      EqOn (δ i) η (Icc (node i.castSucc) (node i.succ)))
    (z v : ℂ) (hz : z ∉ η '' Set.range node)
    (hf : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = z}.Finite) :
    tangentSignedMultiplicity η z v = ∑ i, tangentSignedMultiplicity (δ i) z v := by
  classical
  let R := hf.toFinset
  let w (t : ℝ) : ℤ :=
    if 0 < (deriv η t / v).re then 1 else if (deriv η t / v).re < 0 then -1 else 0
  have hR (t : ℝ) : t ∈ R ↔ t ∈ Icc η.path.a η.path.b ∧ η t = z := hf.mem_toFinset
  have hnode (i : Fin (n + 1)) : node i ∈ Icc η.path.a η.path.b := by
    rw [← ha, ← hb]
    exact ⟨hm (Fin.zero_le i), hm (Fin.le_last i)⟩
  have hsub (i : Fin n) : Icc (node i.castSucc) (node i.succ) ⊆ Icc η.path.a η.path.b :=
    Icc_subset_Icc (hnode _).1 (hnode _).2
  have hnot (t : ℝ) (ht : t ∈ R) : t ∉ Set.range node := by
    intro htN
    exact hz ⟨t, htN, (hR t).mp ht |>.2⟩
  have hlocal (i : Fin n) (t : ℝ) (ht : t ∈ Icc (node i.castSucc) (node i.succ))
      (htR : t ∈ R) : deriv (δ i) t = deriv η t := by
    have hleft : node i.castSucc < t := lt_of_le_of_ne ht.1
      (fun he => hnot t htR ⟨i.castSucc, he⟩)
    have hright : t < node i.succ := lt_of_le_of_ne ht.2
      (fun he => hnot t htR ⟨i.succ, he.symm⟩)
    exact (Filter.eventuallyEq_of_mem (Icc_mem_nhds hleft hright) (hδ i).2.2).deriv_eq
  have hpiece (i : Fin n) : tangentSignedMultiplicity (δ i) z v =
      ∑ t ∈ R, if t ∈ Icc (node i.castSucc) (node i.succ) then w t else 0 := by
    have hset : {t : ℝ | t ∈ Icc (δ i).path.a (δ i).path.b ∧ δ i t = z} =
        {t : ℝ | t ∈ R ∧ t ∈ Icc (node i.castSucc) (node i.succ)} := by
      ext t
      rw [(hδ i).1, (hδ i).2.1]
      constructor
      · intro ht
        exact ⟨(hR t).mpr ⟨hsub i ht.1, ((hδ i).2.2 ht.1).symm.trans ht.2⟩, ht.1⟩
      · intro ht
        exact ⟨ht.2, ((hδ i).2.2 ht.2).trans ((hR t).mp ht.1).2⟩
    have hfin : {t : ℝ | t ∈ Icc (δ i).path.a (δ i).path.b ∧ δ i t = z}.Finite := by
      rw [hset]
      exact R.finite_toSet.subset (fun t ht => ht.1)
    have hfinset : hfin.toFinset = R.filter
        (fun t => t ∈ Icc (node i.castSucc) (node i.succ)) := by
      ext t
      simpa only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq] using (show (t ∈ Icc (δ i).path.a (δ i).path.b ∧ δ i t = z) ↔
        (t ∈ R ∧ t ∈ Icc (node i.castSucc) (node i.succ)) from Set.ext_iff.mp hset t)
    unfold tangentSignedMultiplicity
    rw [dite_eq_left hfin, hfinset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : t ∈ Icc (node i.castSucc) (node i.succ)
    · rw [ite_eq_left h, ite_eq_left h, hlocal i t h ht]
    · rw [ite_eq_right h, ite_eq_right h]
  have hone (t : ℝ) (ht : t ∈ R) :
      (∑ i : Fin n, if t ∈ Icc (node i.castSucc) (node i.succ) then w t else 0) = w t := by
    obtain ⟨i, hi⟩ := finite_partition_interior n node hm t
      (by simpa only [ha, hb] using ((hR t).mp ht).1) (hnot t ht)
    rw [Finset.sum_eq_single i]
    · simp only [ite_eq_left (show t ∈ Icc (node i.castSucc) (node i.succ) from ⟨hi.1.le, hi.2.le⟩)]
    · intro j hj hji
      have hdisj : t ∉ Icc (node j.castSucc) (node j.succ) := by
        intro hjt
        rcases lt_or_gt_of_ne hji with hj | hj
        · have hle : node j.succ ≤ node i.castSucc := hm (by simpa using hj)
          exact (not_lt_of_ge (hjt.2.trans hle)) hi.1
        · have hle : node i.succ ≤ node j.castSucc := hm (by simpa using hj)
          exact (not_lt_of_ge (hle.trans hjt.1)) hi.2
      simp only [ite_eq_right hdisj]
    · simp
  have hmain : tangentSignedMultiplicity η z v = ∑ t ∈ R, w t := by
    unfold tangentSignedMultiplicity
    rw [dite_eq_left hf]
  rw [hmain]
  simp_rw [hpiece]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t ht => (hone t ht).symm)


/-- An arbitrary countable geometric exceptional set has null inverse image
on a regular reference interval. This says nothing about its inverse image
on an original path with stationary parts. -/
theorem regular_curve_avoids_countable (g : ℝ → ℂ) (a b : ℝ)
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (Z : Set ℂ) (hZ : Z.Countable) :
    ∀ᵐ s ∂volume.restrict (Icc a b), g s ∉ Z := by
  filter_upwards [ae_restrict_of_ae ((nonzero_deriv_countable_preimage g Z hZ).ae_notMem volume),
    ae_restrict_mem measurableSet_Icc] with s hs hsab
  exact fun hz => hs ⟨hz, hreg s hsab⟩

/-- Signed visit subdivision holds a.e. on any regular reference curve,
without assuming containment of the original path or of its restrictions. -/
theorem tangent_signed_multiplicity_subdivision_ae (η : PiecewiseC1Path)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (hm : Monotone node)
    (ha : node 0 = η.path.a) (hb : node (Fin.last n) = η.path.b)
    (δ : Fin n → PiecewiseC1Path)
    (hδ : ∀ i, (δ i).path.a = node i.castSucc ∧ (δ i).path.b = node i.succ ∧
      EqOn (δ i) η (Icc (node i.castSucc) (node i.succ)))
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (hV : IsOpen V)
    (hsub : Icc a b ⊆ V) (hg : ContDiffOn ℝ 1 g V)
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) :
    ∀ᵐ s ∂volume.restrict (Icc a b),
      tangentSignedMultiplicity η (g s) (deriv g s) =
        ∑ i, tangentSignedMultiplicity (δ i) (g s) (deriv g s) := by
  filter_upwards [regular_curve_visit_values η g a b V hV hsub hg hreg,
    regular_curve_avoids_countable g a b hreg (η '' Set.range node)
      ((Set.finite_range node).countable.image η)] with s hs havoid
  exact tangent_signed_multiplicity_subdivision η n node hm ha hb δ hδ
    (g s) (deriv g s) havoid hs.1

/-- The signed counting representation uses actual original velocities.
Integrability is proved as well, for later localization and finite summation. -/
theorem arc_tangent_occurrence_integral (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hinj : InjOn g (Icc a b))
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (htrace : η.trace ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (hq : ContinuousOn q (g '' Icc a b)) :
    IntervalIntegrable (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) volume a b ∧
    η.integral q = ∫ s in a..b,
      (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
  obtain ⟨hmaps, _⟩ := arc_parameter_integral η g a b V hV hsub hg hinj hreg htrace
  have hab : a ≤ b :=
    let h := hmaps (left_mem_Icc.mpr η.path.ordered)
    h.1.trans h.2
  have hcont : ContinuousOn (fun s => q (g s) * deriv g s) (Icc a b) :=
    (hq.comp (hg.continuousOn.mono hsub) (mapsTo_image g _)).mul
      ((hg.continuousOn_deriv_of_isOpen hV le_rfl).mono hsub)
  have hsame : (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) =ᵐ[volume.restrict (Ioc a b)]
      (fun s => (arcTraversalMultiplicity g a b η s : ℂ) * (q (g s) * deriv g s)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
        (arc_tangent_signed_multiplicity η g a b V hV hsub hg hinj hreg htrace),
      ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
        (arc_signed_multiplicity η g a b V hV hsub hg hinj hreg htrace)] with s ht hd
    rw [← ht, hd]
  have hint := directed_integrand_integrable a b
    (arcParameter g a b η η.path.a) (arcParameter g a b η η.path.b) hab
    (fun s => q (g s) * deriv g s) hcont
  refine ⟨?_, ?_⟩
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    exact hint.1.congr hsame.symm
  · rw [arc_occurrence_integral η g a b V hV hsub hg hinj hreg htrace q hq]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (arc_tangent_signed_multiplicity η g a b V hV hsub hg hinj hreg htrace)] with s hs
    rw [hs]

/-- If a point is not visited on the original parameter interval, its actual
signed visit count is zero, regardless of the total representative elsewhere. -/
theorem tangent_signed_multiplicity_of_not_mem_trace (η : PiecewiseC1Path)
    (z v : ℂ) (hz : z ∉ η.trace) : tangentSignedMultiplicity η z v = 0 := by
  have hempty : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = z} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨ht, he⟩
    exact hz ⟨t, ht, he⟩
  unfold tangentSignedMultiplicity
  simp only [hempty, Set.finite_empty, dite_eq_left, Set.Finite.toFinset_empty, Finset.sum_empty]


theorem path_integral_zero_of_zero_on_trace (η : PiecewiseC1Path) (q : ℂ → ℂ)
    (hq : EqOn q 0 η.trace) : η.integral q = 0 := by
  have he := path_integral_congr_off_countable η ∅ Set.countable_empty q 0
    (fun z hz => hq hz.1)
  exact he.trans (by simp [PiecewiseC1Path.integral, C1Partition.integral])

/-- Localization on an ambient arc chart. The original path can leave the
chart and traverse other arcs; only its intersection with U must lie on g.
All its actual signed visits are counted. -/
theorem localized_tangent_occurrence_integral (η : PiecewiseC1Path)
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (hV : IsOpen V)
    (hsub : Icc a b ⊆ V) (hg : ContDiffOn ℝ 1 g V)
    (hinj : InjOn g (Icc a b)) (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (htrace : η.trace ∩ U ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (hq : ContinuousOn q (η.trace ∪ g '' Icc a b))
    (hsupp : tsupport q ⊆ U) (hab : a ≤ b) :
    IntervalIntegrable (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) volume a b ∧
    η.integral q = ∫ s in a..b,
      (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
  classical
  let C : Bool → Set ℂ := fun e => if e then U else (tsupport q)ᶜ
  have hC (e : Bool) : IsOpen (C e) := by
    cases e
    · exact (isClosed_closure : IsClosed (tsupport q)).isOpen_compl
    · exact hU
  have hcover : η.trace ⊆ ⋃ e, C e := by
    intro z hz
    by_cases h : z ∈ tsupport q
    · exact mem_iUnion.mpr ⟨true, hsupp h⟩
    · exact mem_iUnion.mpr ⟨false, h⟩
  obtain ⟨n, node, select, δ, hm, ha, hb, hδ, hsum⟩ :=
    finite_subpath_selection η C hC hcover
  have hδtrace (i : Fin n) : (δ i).trace ⊆ η.trace := by
    rintro z ⟨t, ht, he⟩
    rw [(hδ i).1, (hδ i).2.1] at ht
    refine ⟨t, ?_, ((hδ i).2.2.1 ht).symm.trans he⟩
    constructor
    · rw [← ha]
      exact (hm (Fin.zero_le _)).trans ht.1
    · rw [← hb]
      exact ht.2.trans (hm (Fin.le_last _))
  let F (γ : PiecewiseC1Path) (s : ℝ) : ℂ :=
    (tangentSignedMultiplicity γ (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)
  have hpiece (i : Fin n) : IntervalIntegrable (F (δ i)) volume a b ∧
      (δ i).integral q = ∫ s in a..b, F (δ i) s := by
    cases he : select i with
    | true =>
      have hinside : (δ i).trace ⊆ U := by
        simpa only [C, he, ite_true] using (hδ i).2.2.2
      exact arc_tangent_occurrence_integral (δ i) g a b V hV hsub hg hinj hreg
        (fun z hz => htrace ⟨hδtrace i hz, hinside hz⟩) q (hq.mono subset_union_right)
    | false =>
      have hzero (z : ℂ) (hz : z ∈ (δ i).trace) : q z = 0 := by
        have hout : z ∉ tsupport q := by
          simpa only [C, he, Bool.false_eq_true, ite_false, mem_compl_iff] using (hδ i).2.2.2 hz
        exact image_eq_zero_of_notMem_tsupport hout
      have hF : F (δ i) = 0 := by
        funext s
        by_cases hz : g s ∈ (δ i).trace
        · simp only [F, hzero _ hz, zero_mul, mul_zero, Pi.zero_apply]
        · simp only [F, tangent_signed_multiplicity_of_not_mem_trace (δ i) (g s) (deriv g s) hz,
            Int.cast_zero, zero_mul, Pi.zero_apply]
      refine ⟨by rw [hF]; exact intervalIntegrable_const, ?_⟩
      simp only [hF, Pi.zero_apply, intervalIntegral.integral_zero]
      exact path_integral_zero_of_zero_on_trace (δ i) q hzero
  have heq : (fun s => ∑ i, F (δ i) s) =ᵐ[volume.restrict (uIoc a b)] F η := by
    rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (tangent_signed_multiplicity_subdivision_ae η n node hm ha hb δ
        (fun i => ⟨(hδ i).1, (hδ i).2.1, (hδ i).2.2.1⟩)
        g a b V hV hsub hg hreg)] with s hs
    dsimp only [F]
    rw [hs, Int.cast_sum, Finset.sum_mul]
  have hsumint : IntervalIntegrable (fun s => ∑ i, F (δ i) s) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    exact integrable_finsetSum Finset.univ (fun i _ => (hpiece i).1.1)
  refine ⟨hsumint.congr_ae heq, ?_⟩
  rw [hsum q (hq.mono subset_union_left)]
  simp_rw [fun i => (hpiece i).2]
  rw [← intervalIntegral.integral_finsetSum (fun i _ => (hpiece i).1)]
  exact intervalIntegral.integral_congr_ae_restrict heq


/-- Local counting representation for the actual finite integer chain,
retaining its original paths and all of their intervals. -/
theorem localized_chain_tangent_occurrence_integral (Γ : IntegralChain)
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (hV : IsOpen V)
    (hsub : Icc a b ⊆ V) (hg : ContDiffOn ℝ 1 g V)
    (hinj : InjOn g (Icc a b)) (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (htrace : Γ.trace ∩ U ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (hq : ContinuousOn q (Γ.trace ∪ g '' Icc a b))
    (hsupp : tsupport q ⊆ U) (hab : a ≤ b) :
    Γ.integral q = ∫ s in a..b,
      (chainTangentMultiplicity Γ (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
  have hlocal (η : PiecewiseC1Path) (hη : η ∈ Γ.support) :=
    localized_tangent_occurrence_integral η g a b V hV hsub hg hinj hreg U hU
      (fun z hz => htrace ⟨⟨η, hη, hz.1⟩, hz.2⟩) q
      (hq.mono (union_subset_union_left _ (fun z hz => ⟨η, hη, hz⟩))) hsupp hab
  calc
    _ = ∑ η ∈ Γ.support, (Γ η : ℂ) * ∫ s in a..b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
      unfold IntegralChain.integral Finsupp.sum
      exact Finset.sum_congr rfl (fun η hη => congrArg ((Γ η : ℂ) * ·) (hlocal η hη).2)
    _ = ∫ s in a..b, ∑ η ∈ Γ.support, (Γ η : ℂ) *
        ((tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)) := by
      simp_rw [← intervalIntegral.integral_const_mul]
      exact (intervalIntegral.integral_finsetSum
        (fun η hη => (hlocal η hη).1.const_mul (Γ η : ℂ))).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [chainTangentMultiplicity, Finsupp.sum, Int.cast_sum, Int.cast_mul, Finset.sum_mul,
        mul_assoc]

/-- Geometric equality of actual signed visits gives the local equality of
canonical integrals. The paths may leave the reference arc chart. -/
theorem localized_chain_occurrence_comparison (Γ Δ : IntegralChain)
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (hV : IsOpen V)
    (hsub : Icc a b ⊆ V) (hg : ContDiffOn ℝ 1 g V)
    (hinj : InjOn g (Icc a b)) (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (U : Set ℂ) (hU : IsOpen U)
    (htrace : (Γ.trace ∪ Δ.trace) ∩ U ⊆ g '' Icc a b)
    (hcount : ∀ᵐ s ∂volume.restrict (Ioc a b),
      chainTangentMultiplicity Γ (g s) (deriv g s) =
        chainTangentMultiplicity Δ (g s) (deriv g s))
    (q : ℂ → ℂ) (hq : ContinuousOn q ((Γ.trace ∪ Δ.trace) ∪ g '' Icc a b))
    (hsupp : tsupport q ⊆ U) (hab : a ≤ b) : Γ.integral q = Δ.integral q := by
  rw [localized_chain_tangent_occurrence_integral Γ g a b V hV hsub hg hinj hreg U hU
      (fun z hz => htrace ⟨Or.inl hz.1, hz.2⟩) q
      (hq.mono (union_subset_union_left _ subset_union_left)) hsupp hab,
    localized_chain_tangent_occurrence_integral Δ g a b V hV hsub hg hinj hreg U hU
      (fun z hz => htrace ⟨Or.inr hz.1, hz.2⟩) q
      (hq.mono (union_subset_union_left _ subset_union_right)) hsupp hab]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  filter_upwards [hcount] with s hs
  rw [hs]


/-- Differentiable curves have the same velocity at all but countably many
points where their parameter representatives agree. The coincidence set can
be an arbitrary closed or measurable set; it need not contain an interval. -/
theorem coincidence_deriv_exception_countable (f g : ℝ → ℂ) :
    {t : ℝ | f t = g t ∧ DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ g t ∧
      deriv f t ≠ deriv g t}.Countable := by
  apply (nonzero_deriv_fiber_countable (fun t => f t - g t) 0).mono
  rintro t ⟨he, hf, hg, hd⟩
  refine ⟨sub_eq_zero.mpr he, ?_⟩
  change deriv (f - g) t ≠ 0
  rw [deriv_sub hf hg]
  exact sub_ne_zero.mpr hd

/-- Equality only on the actual coincidence set suffices for a.e. equality
of velocities. No differentiability is assumed away from that set. -/
theorem deriv_eq_ae_on_coincidence (f g : ℝ → ℂ) :
    ∀ᵐ t : ℝ, f t = g t → DifferentiableAt ℝ f t →
      DifferentiableAt ℝ g t → deriv f t = deriv g t := by
  filter_upwards [(coincidence_deriv_exception_countable f g).ae_notMem volume]
    with t ht he hf hg
  by_contra hd
  exact ht ⟨he, hf, hg, hd⟩

/-- The chain rule on a coincidence set holds a.e. even if the path leaves
the reference curve arbitrarily close to every point of that set. -/
theorem coincidence_velocity_relation_ae (η g : ℝ → ℂ) (φ : ℝ → ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) (heq : EqOn η (g ∘ φ) S)
    (hη : ∀ t ∈ S, DifferentiableAt ℝ η t)
    (hφ : ∀ t ∈ S, DifferentiableAt ℝ φ t)
    (hg : ∀ t ∈ S, DifferentiableAt ℝ g (φ t)) :
    ∀ᵐ t ∂volume.restrict S, deriv η t = deriv φ t • deriv g (φ t) := by
  filter_upwards [ae_restrict_of_ae (deriv_eq_ae_on_coincidence η (g ∘ φ)),
    ae_restrict_mem hS] with t ht hs
  exact (ht (heq hs) (hη t hs) ((hg t hs).hasDerivAt.scomp t
    (hφ t hs).hasDerivAt).differentiableAt).trans
    ((hg t hs).hasDerivAt.scomp t (hφ t hs).hasDerivAt).deriv

/-- The elementary orientation factor in the signed one-dimensional
Jacobian formula, including stationary parameter values. -/
theorem abs_mul_real_sign (r : ℝ) : |r| * Real.sign r = r := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · simp [h]
  · rw [Real.sign_of_pos h, abs_of_pos h, mul_one]

/-- Signed change of variables on an arbitrary measurable coincidence set.
Only the scalar coordinate φ is injective on that set. Neither curve must
coincide with the other on an open interval, and zero scalar velocity is
allowed. Integrability is proved equivalent as well as the integral identity. -/
theorem coincidence_change_of_variables (η g : ℝ → ℂ) (φ : ℝ → ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) (heq : EqOn η (g ∘ φ) S)
    (hη : ∀ t ∈ S, DifferentiableAt ℝ η t)
    (hφ : ∀ t ∈ S, DifferentiableAt ℝ φ t)
    (hg : ∀ t ∈ S, DifferentiableAt ℝ g (φ t))
    (hinj : InjOn φ S) (q : ℂ → ℂ) :
    let F : ℝ → ℂ := fun s =>
      Real.sign (deriv φ (Function.invFunOn φ S s)) • (q (g s) * deriv g s)
    (IntegrableOn (fun t => q (η t) * deriv η t) S ↔ IntegrableOn F (φ '' S)) ∧
      (∫ t in S, q (η t) * deriv η t) = ∫ s in φ '' S, F s := by
  dsimp only
  let F : ℝ → ℂ := fun s =>
    Real.sign (deriv φ (Function.invFunOn φ S s)) • (q (g s) * deriv g s)
  have hsame : (fun t => q (η t) * deriv η t) =ᵐ[volume.restrict S]
      (fun t => |deriv φ t| • F (φ t)) := by
    filter_upwards [coincidence_velocity_relation_ae η g φ S hS heq hη hφ hg,
      ae_restrict_mem hS] with t ht hs
    dsimp only [F]
    rw [hinj.leftInvOn_invFunOn hs, ht, heq hs, smul_smul, abs_mul_real_sign]
    simp only [Function.comp_apply, Complex.real_smul]
    ring
  have hd (t : ℝ) (ht : t ∈ S) : HasDerivWithinAt φ (deriv φ t) S t :=
    (hφ t ht).hasDerivAt.hasDerivWithinAt
  refine ⟨?_, ?_⟩
  · exact (integrable_congr hsame).trans
      (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hd hinj F).symm
  · exact (integral_congr_ae hsame).trans
      (integral_image_eq_integral_abs_deriv_smul hS hd hinj F).symm


/-- One of three elementary real projections is noncritical on both of two
nonzero planar vectors. This includes transverse as well as tangent visits. -/
theorem common_nonzero_projection (v w : ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℝ, L v ≠ 0 ∧ L w ≠ 0 := by
  have hv' : v.re ≠ 0 ∨ v.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (Complex.ext h.1 h.2)
  have hw' : w.re ≠ 0 ∨ w.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (Complex.ext h.1 h.2)
  by_cases hvr : v.re = 0
  · have hvi := hv'.resolve_left (not_not.mpr hvr)
    by_cases hwi : w.im = 0
    · refine ⟨Complex.reCLM + Complex.imCLM, ?_, ?_⟩
      · simpa [hvr] using hvi
      · simpa [hwi] using hw'.resolve_right (not_not.mpr hwi)
    · exact ⟨Complex.imCLM, hvi, hwi⟩
  · by_cases hwr : w.re = 0
    · have hwi := hw'.resolve_left (not_not.mpr hwr)
      by_cases hvi : v.im = 0
      · refine ⟨Complex.reCLM + Complex.imCLM, ?_, ?_⟩
        · simpa [hvi] using hvr
        · simpa [hwr] using hwi
      · exact ⟨Complex.imCLM, hvi, hwi⟩
    · exact ⟨Complex.reCLM, hvr, hwr⟩

/-- Construct scalar coordinates for a pair of regular curve visits. Only
local regularity at the two supplied parameters is required. Neither curve
is assumed globally injective or contained in the other. The coordinate
matches every actual coincident pair in the resulting parameter rectangle. -/
theorem regular_coincidence_chart (f g : ℝ → ℂ) (t s : ℝ)
    (hf : ContDiffAt ℝ 1 f t) (hg : ContDiffAt ℝ 1 g s)
    (hfr : deriv f t ≠ 0) (hgr : deriv g s ≠ 0) (he : f t = g s) :
    ∃ (U W : Set ℝ) (φ : ℝ → ℝ),
      IsOpen U ∧ t ∈ U ∧ IsOpen W ∧ s ∈ W ∧
      ContDiffOn ℝ 1 f U ∧ ContDiffOn ℝ 1 g W ∧
      ContDiffOn ℝ 1 φ U ∧ InjOn φ U ∧ MapsTo φ U W ∧
      ∀ u ∈ U, ∀ v ∈ W, f u = g v → φ u = v := by
  obtain ⟨L, hLf, hLg⟩ := common_nonzero_projection (deriv f t) (deriv g s) hfr hgr
  let F : ℝ → ℝ := L ∘ f
  let G : ℝ → ℝ := L ∘ g
  have hF : ContDiffAt ℝ 1 F t := L.contDiff.comp_contDiffAt t hf
  have hG : ContDiffAt ℝ 1 G s := L.contDiff.comp_contDiffAt s hg
  have hdF : HasDerivAt F (L (deriv f t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t hf.differentiableAt_one.hasDerivAt
  have hdG : HasDerivAt G (L (deriv g s)) s :=
    L.hasFDerivAt.comp_hasDerivAt s hg.differentiableAt_one.hasDerivAt
  let eF := hF.toOpenPartialHomeomorph F (hdF.hasFDerivAt_equiv hLf) (by norm_num)
  let eG := hG.toOpenPartialHomeomorph G (hdG.hasFDerivAt_equiv hLg) (by norm_num)
  have htF : t ∈ eF.source := hF.mem_toOpenPartialHomeomorph_source _ (by norm_num)
  have hsG : s ∈ eG.source := hG.mem_toOpenPartialHomeomorph_source _ (by norm_num)
  have hFG : F t = G s := congrArg L he
  let φ : ℝ → ℝ := eG.symm ∘ F
  have hφt : φ t = s := by
    change eG.symm (F t) = s
    rw [hFG]
    exact eG.left_inv hsG
  have hφ : ContDiffAt ℝ 1 φ t := by
    have hi : ContDiffAt ℝ 1 eG.symm (G s) := hG.to_localInverse (hdG.hasFDerivAt_equiv hLg) (by norm_num)
    exact (hFG.symm ▸ hi).comp t hF
  obtain ⟨fN, hfN, hfNdiff⟩ := hf.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨gN, hgN, hgNdiff⟩ := hg.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨φN, hφN, hφNdiff⟩ := hφ.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨W, hWsub, hWopen, hsW⟩ := mem_nhds_iff.mp
    (inter_mem (eG.open_source.mem_nhds hsG) hgN)
  have htarget : F t ∈ eG.target := hFG ▸ eG.map_source hsG
  have hpre : φ ⁻¹' W ∈ nhds t :=
    hφ.continuousAt (hφt ▸ hWopen.mem_nhds hsW)
  let A := eF.source ∩ (F ⁻¹' eG.target ∩ (φ ⁻¹' W ∩ (fN ∩ φN)))
  have hA : A ∈ nhds t := inter_mem (eF.open_source.mem_nhds htF)
    (inter_mem (hF.continuousAt (eG.open_target.mem_nhds htarget))
      (inter_mem hpre (inter_mem hfN hφN)))
  obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp hA
  refine ⟨U, W, φ, hUopen, htU, hWopen, hsW,
    hfNdiff.mono (fun u hu => (hUsub hu).2.2.2.1),
    hgNdiff.mono (fun v hv => (hWsub hv).2),
    hφNdiff.mono (fun u hu => (hUsub hu).2.2.2.2), ?_,
    (fun u hu => (hUsub hu).2.2.1), ?_⟩
  · intro u hu v hv huv
    apply eF.injOn (hUsub hu).1 (hUsub hv).1
    exact eG.symm.injOn (hUsub hu).2.1 (hUsub hv).2.1 huv
  · intro u hu v hv huv
    change eG.symm (L (f u)) = v
    rw [huv]
    exact eG.left_inv (hWsub hv).1


/-- A countable family of genuine scalar coincidence coordinates is derived
for any collection of regular matching visits. No atlas or whole-path
containment is a hypothesis. The cover is in the two original parameter
variables, so sheets that meet on complicated closed sets are retained. -/
theorem countable_regular_coincidence_charts (f g : ℝ → ℂ) (C : Set (ℝ × ℝ))
    (hC : ∀ p ∈ C, ContDiffAt ℝ 1 f p.1 ∧ ContDiffAt ℝ 1 g p.2 ∧
      deriv f p.1 ≠ 0 ∧ deriv g p.2 ≠ 0 ∧ f p.1 = g p.2) :
    ∃ (T : Set (ℝ × ℝ)), T.Countable ∧ T ⊆ C ∧
      ∃ (U W : (ℝ × ℝ) → Set ℝ) (φ : (ℝ × ℝ) → ℝ → ℝ),
        (∀ p ∈ T, IsOpen (U p) ∧ p.1 ∈ U p ∧ IsOpen (W p) ∧ p.2 ∈ W p ∧
          ContDiffOn ℝ 1 f (U p) ∧ ContDiffOn ℝ 1 g (W p) ∧
          ContDiffOn ℝ 1 (φ p) (U p) ∧ InjOn (φ p) (U p) ∧ MapsTo (φ p) (U p) (W p) ∧
          ∀ u ∈ U p, ∀ v ∈ W p, f u = g v → φ p u = v) ∧
        C ⊆ ⋃ p ∈ T, (U p) ×ˢ (W p) := by
  classical
  have hc (p : ℝ × ℝ) (hp : p ∈ C) :=
    regular_coincidence_chart f g p.1 p.2 (hC p hp).1 (hC p hp).2.1
      (hC p hp).2.2.1 (hC p hp).2.2.2.1 (hC p hp).2.2.2.2
  choose! U W φ hUo htU hWo hsW hfU hgW hφU hφinj hφmap hmatch using hc
  obtain ⟨T, hT, hTC, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof C).elim_nhds_subcover
      (fun p => U p ×ˢ W p) (fun p hp =>
        ((hUo p hp).prod (hWo p hp)).mem_nhds ⟨htU p hp, hsW p hp⟩)
  refine ⟨T, hT, hTC, U, W, φ, ?_, hcover⟩
  intro p hp
  have hpc := hTC p hp
  exact ⟨hUo p hpc, htU p hpc, hWo p hpc, hsW p hpc, hfU p hpc, hgW p hpc,
    hφU p hpc, hφinj p hpc, hφmap p hpc, hmatch p hpc⟩

/-- Integrate over any measurable portion of a coincidence chart. The
factorization on that portion is derived from the actual equal values,
not assumed on the surrounding open interval. -/
theorem coincidence_chart_integral (f g : ℝ → ℂ) (U W : Set ℝ) (φ : ℝ → ℝ)
    (hU : IsOpen U) (hW : IsOpen W) (hf : ContDiffOn ℝ 1 f U)
    (hg : ContDiffOn ℝ 1 g W) (hφ : ContDiffOn ℝ 1 φ U)
    (hinj : InjOn φ U) (hmaps : MapsTo φ U W)
    (hmatch : ∀ u ∈ U, ∀ v ∈ W, f u = g v → φ u = v)
    (S : Set ℝ) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (htrace : ∀ u ∈ S, ∃ v ∈ W, f u = g v) (q : ℂ → ℂ) :
    let F : ℝ → ℂ := fun s =>
      Real.sign (deriv φ (Function.invFunOn φ S s)) • (q (g s) * deriv g s)
    (IntegrableOn (fun t => q (f t) * deriv f t) S ↔ IntegrableOn F (φ '' S)) ∧
      (∫ t in S, q (f t) * deriv f t) = ∫ s in φ '' S, F s := by
  apply coincidence_change_of_variables f g φ S hS
  · intro u hu
    obtain ⟨v, hv, he⟩ := htrace u hu
    change f u = g (φ u)
    rw [hmatch u (hSU hu) v hv he]
    exact he
  · intro u hu
    exact (hf.contDiffAt (hU.mem_nhds (hSU hu))).differentiableAt_one
  · intro u hu
    exact (hφ.contDiffAt (hU.mem_nhds (hSU hu))).differentiableAt_one
  · intro u hu
    exact (hg.contDiffAt (hW.mem_nhds (hmaps (hSU hu)))).differentiableAt_one
  · exact hinj.mono hSU


/-- On a measurable coincidence piece the sign in change of variables is
the sign of the actual original velocity relative to the reference tangent.
The norm identity also controls countable sums of these pieces. -/
theorem coincidence_tangent_change_of_variables (η g : ℝ → ℂ) (φ : ℝ → ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) (heq : EqOn η (g ∘ φ) S)
    (hη : ∀ t ∈ S, DifferentiableAt ℝ η t)
    (hφ : ∀ t ∈ S, DifferentiableAt ℝ φ t)
    (hg : ∀ t ∈ S, DifferentiableAt ℝ g (φ t))
    (hreg : ∀ t ∈ S, deriv g (φ t) ≠ 0) (hinj : InjOn φ S) (q : ℂ → ℂ) :
    let F : ℝ → ℂ := fun s =>
      Real.sign ((deriv η (Function.invFunOn φ S s) / deriv g s).re) •
        (q (g s) * deriv g s)
    (IntegrableOn (fun t => q (η t) * deriv η t) S ↔ IntegrableOn F (φ '' S)) ∧
      (∫ t in S, q (η t) * deriv η t) = (∫ s in φ '' S, F s) ∧
      (∫ t in S, ‖q (η t) * deriv η t‖) = ∫ s in φ '' S, ‖F s‖ := by
  dsimp only
  let F : ℝ → ℂ := fun s =>
    Real.sign ((deriv η (Function.invFunOn φ S s) / deriv g s).re) •
      (q (g s) * deriv g s)
  have hsame : (fun t => q (η t) * deriv η t) =ᵐ[volume.restrict S]
      (fun t => |deriv φ t| • F (φ t)) := by
    filter_upwards [coincidence_velocity_relation_ae η g φ S hS heq hη hφ hg,
      ae_restrict_mem hS] with t ht hs
    dsimp only [F]
    rw [hinj.leftInvOn_invFunOn hs, ht, Complex.real_smul,
      mul_div_cancel_right₀ _ (hreg t hs), Complex.ofReal_re,
      smul_smul, abs_mul_real_sign, heq hs]
    simp only [Function.comp_apply, Complex.real_smul]
    ring
  have hd (t : ℝ) (ht : t ∈ S) : HasDerivWithinAt φ (deriv φ t) S t :=
    (hφ t ht).hasDerivAt.hasDerivWithinAt
  refine ⟨(integrable_congr hsame).trans
    (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hd hinj F).symm,
    (integral_congr_ae hsame).trans
      (integral_image_eq_integral_abs_deriv_smul hS hd hinj F).symm, ?_⟩
  calc
    (∫ t in S, ‖q (η t) * deriv η t‖) =
        ∫ t in S, |deriv φ t| * ‖F (φ t)‖ := by
      apply integral_congr_ae
      filter_upwards [hsame] with t ht
      rw [ht, norm_smul, Real.norm_eq_abs, abs_abs]
    _ = ∫ s in φ '' S, ‖F s‖ := by
      simpa only [smul_eq_mul] using
        (integral_image_eq_integral_abs_deriv_smul hS hd hinj (fun s => ‖F s‖)).symm

/-- Original PC1 representatives are C1 near every parameter off their
actual finite partition nodes, without any assumption on their velocity. -/
theorem path_contDiffAt_of_not_node (η : PiecewiseC1Path) (t : ℝ)
    (ht : t ∈ Icc η.path.a η.path.b) (hnot : t ∉ Set.range η.partition.node) :
    ContDiffAt ℝ 1 η t := by
  obtain ⟨i, hi⟩ := finite_partition_interior η.partition.count η.partition.node
    η.partition.strictMono.monotone t (by simpa only [η.partition.first,
      η.partition.last] using ht) hnot
  exact (η.partition.smooth i).contDiffAt (Icc_mem_nhds hi.1 hi.2)

/-- A countable coincidence atlas is constructed for almost every reference
value and all its original PC1 visits. No nonzero original velocity, finite
seam preimage, or single-arc ambient cover is supplied as a premise. -/
theorem pc1_regular_coincidence_charts (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) :
    ∃ (T : Set (ℝ × ℝ)), T.Countable ∧
      ∃ (U W : (ℝ × ℝ) → Set ℝ) (φ : (ℝ × ℝ) → ℝ → ℝ),
        (∀ p ∈ T, IsOpen (U p) ∧ p.1 ∈ U p ∧ IsOpen (W p) ∧ p.2 ∈ W p ∧
          ContDiffOn ℝ 1 η (U p) ∧ ContDiffOn ℝ 1 g (W p) ∧
          ContDiffOn ℝ 1 (φ p) (U p) ∧ InjOn (φ p) (U p) ∧ MapsTo (φ p) (U p) (W p) ∧
          ∀ u ∈ U p, ∀ v ∈ W p, η u = g v → φ p u = v) ∧
        ∀ᵐ s ∂volume.restrict (Icc a b),
          ∀ t ∈ Icc η.path.a η.path.b, η t = g s →
            ∃ p ∈ T, t ∈ U p ∧ s ∈ W p := by
  let C : Set (ℝ × ℝ) := {p | p.1 ∈ Icc η.path.a η.path.b ∧ p.2 ∈ Icc a b ∧
    p.1 ∉ Set.range η.partition.node ∧ deriv η p.1 ≠ 0 ∧ η p.1 = g p.2}
  have hC (p : ℝ × ℝ) (hp : p ∈ C) :
      ContDiffAt ℝ 1 η p.1 ∧ ContDiffAt ℝ 1 g p.2 ∧
        deriv η p.1 ≠ 0 ∧ deriv g p.2 ≠ 0 ∧ η p.1 = g p.2 :=
    ⟨path_contDiffAt_of_not_node η p.1 hp.1 hp.2.2.1,
      hg.contDiffAt (hV.mem_nhds (hsub hp.2.1)), hp.2.2.2.1,
      hreg p.2 hp.2.1, hp.2.2.2.2⟩
  obtain ⟨T, hT, hTC, U, W, φ, hcharts, hcover⟩ :=
    countable_regular_coincidence_charts η g C hC
  refine ⟨T, hT, U, W, φ, hcharts, ?_⟩
  filter_upwards [regular_curve_visit_values η g a b V hV hsub hg hreg,
    ae_restrict_mem measurableSet_Icc] with s hs hsab
  intro t ht he
  have htgood := hs.2 t ht he
  have hp : (t, s) ∈ C := ⟨ht, hsab, htgood.2.1, htgood.2.2.2, he⟩
  obtain ⟨p, hpT, hmem⟩ := mem_iUnion₂.mp (hcover hp)
  exact ⟨p, hpT, hmem.1, hmem.2⟩


/-- At an injective reference visit the actual fiber is the singleton of its
original parameter, including endpoint and stationary reference visits. -/
theorem tangent_signed_multiplicity_of_injective (η : PiecewiseC1Path)
    (hinj : InjOn η (Icc η.path.a η.path.b)) (t : ℝ)
    (ht : t ∈ Icc η.path.a η.path.b) (v : ℂ) :
    tangentSignedMultiplicity η (η t) v =
      if 0 < (deriv η t / v).re then 1
      else if (deriv η t / v).re < 0 then -1 else 0 := by
  classical
  have hset : {u : ℝ | u ∈ Icc η.path.a η.path.b ∧ η u = η t} = {t} := by
    ext u
    constructor
    · intro hu
      exact mem_singleton_iff.mpr (hinj hu.1 ht hu.2)
    · rintro rfl
      exact ⟨ht, rfl⟩
  unfold tangentSignedMultiplicity
  simp only [hset, Set.finite_singleton, dite_eq_left, Set.Finite.toFinset_singleton,
    Finset.sum_singleton]

private def tangentMultiplicityHom (z v : ℂ) : IntegralChain →+ ℤ :=
  Finsupp.liftAddHom (fun η =>
    { toFun := fun c : ℤ => c * tangentSignedMultiplicity η z v
      map_zero' := by simp
      map_add' := fun c d => by simp [add_mul] })

/-- Linear realization of real cells preserves their actual signed visits,
including identification of repeated path objects and cancellation of integer
coefficients in the canonical Finsupp representation. -/
theorem cellContour_tangent_multiplicity {O : Set (E 2)} (C : Chain 1 1 O) (z v : ℂ) :
    chainTangentMultiplicity (cellContour C) z v =
      C.sum (fun c m => m * tangentSignedMultiplicity (cellPath c) z v) := by
  let H := tangentMultiplicityHom z v
  let K : Chain 1 1 O →+ ℤ := Finsupp.liftAddHom (fun c =>
    { toFun := fun m : ℤ => m * tangentSignedMultiplicity (cellPath c) z v
      map_zero' := by simp
      map_add' := fun m n => by simp [add_mul] })
  have hh : H.comp cellContour = K := by
    ext c
    change H (cellContour (Finsupp.single c 1)) = K (Finsupp.single c 1)
    rw [cellContour_single]
    simp only [H, K, tangentMultiplicityHom, Finsupp.liftAddHom_apply_single]
  exact DFunLike.congr_fun hh C

/-- The actual alternating face signs are retained in the occurrence density
of the realized cell boundary. This is an incidence calculation on the actual
face chain; no comparison with an original boundary cycle is a premise. -/
theorem cell_assembly_tangent_multiplicity {O : Set (E 2)} (d : PositiveCellData O)
    (z v : ℂ) :
    chainTangentMultiplicity d.faceContour z v =
      ∑ j, ∑ i : Fin 2, (-1 : ℤ) ^ i.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells j) i true)) z v -
          tangentSignedMultiplicity (cellPath (cellFace (d.cells j) i false)) z v) := by
  change tangentMultiplicityHom z v
    (cellContour (∑ j, (1 : ℤ) • cellBoundary (d.cells j))) = _
  simp only [one_zsmul, map_sum, cellBoundary, map_zsmul, map_sub,
    cellContour_single, zsmul_eq_mul]
  simp [tangentMultiplicityHom]


/-- Measurability of original regular coincidence times uses the actual
continuous original representative and the actual measurable derivative. -/
theorem regularArcSource_measurable (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (hg : ContinuousOn g (Icc a b)) :
    MeasurableSet (regularArcSource η g a b) := by
  let G := IccExtend η.path.ordered η.path.onInterval
  have hG : Continuous G := η.path.onInterval.continuous.Icc_extend'
  have he : regularArcSource η g a b =
      (Icc η.path.a η.path.b \ Set.range η.partition.node) ∩
        ((deriv η) ⁻¹' {0}ᶜ ∩ G ⁻¹' (g '' Icc a b)) := by
    ext t
    by_cases ht : t ∈ Icc η.path.a η.path.b
    · have hGt : G t = η t := IccExtend_of_mem η.path.ordered _ ht
      simp only [regularArcSource, mem_ofPred_eq, mem_inter_iff, Set.mem_sdiff,
        mem_preimage, mem_compl_iff, mem_singleton_iff, hGt, ht, true_and]
    · change (t ∈ Icc η.path.a η.path.b ∧ _) ↔ (t ∈ Icc η.path.a η.path.b ∧ _) ∧ _
      simp only [ht, false_and]
  rw [he]
  exact (measurableSet_Icc.diff (Set.finite_range η.partition.node).measurableSet).inter
    (((measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_deriv η)).inter
      ((isCompact_Icc.image_of_continuousOn hg).measurableSet.preimage hG.measurable))

/-- Disjoint Borel pieces and genuine local scalar coordinates are selected
from the original regular coincidences. Empty families give empty pieces. -/
theorem pc1_coincidence_partition (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) :
    Nonempty (ArcCoincidencePartition η g a b) := by
  classical
  let R := regularArcSource η g a b
  have hR : MeasurableSet R := regularArcSource_measurable η g a b
    (hg.continuousOn.mono hsub)
  let C : Set (ℝ × ℝ) := {p | p.1 ∈ R ∧ p.2 ∈ Icc a b ∧ η p.1 = g p.2}
  have hC (p : ℝ × ℝ) (hp : p ∈ C) :
      ContDiffAt ℝ 1 η p.1 ∧ ContDiffAt ℝ 1 g p.2 ∧
        deriv η p.1 ≠ 0 ∧ deriv g p.2 ≠ 0 ∧ η p.1 = g p.2 :=
    ⟨path_contDiffAt_of_not_node η p.1 hp.1.1 hp.1.2.1,
      hg.contDiffAt (hV.mem_nhds (hsub hp.2.1)), hp.1.2.2.1,
      hreg p.2 hp.2.1, hp.2.2⟩
  obtain ⟨T, hT, hTC, U, W, φ, hcharts, hcover⟩ :=
    countable_regular_coincidence_charts η g C hC
  obtain ⟨e, he⟩ := Set.countable_iff_exists_subset_range.mp hT
  let A : ℕ → Set ℝ := fun n => if e n ∈ T then
    R ∩ (U (e n) ∩ {t | φ (e n) t ∈ Icc a b ∧ η t = g (φ (e n) t)}) else ∅
  have hA (n : ℕ) : MeasurableSet (A n) := by
    dsimp only [A]
    split_ifs with hn
    · have hc := hcharts (e n) hn
      let f₀ := (U (e n)).piecewise η 0
      let φ₀ := (U (e n)).piecewise (φ (e n)) 0
      let g₀ := (U (e n)).piecewise (g ∘ φ (e n)) 0
      have hf₀ : Measurable f₀ :=
        hc.2.2.2.2.1.continuousOn.measurable_piecewise continuousOn_const hc.1.measurableSet
      have hφ₀ : Measurable φ₀ :=
        hc.2.2.2.2.2.2.1.continuousOn.measurable_piecewise continuousOn_const hc.1.measurableSet
      have hg₀ : Measurable g₀ :=
        (hc.2.2.2.2.2.1.continuousOn.comp hc.2.2.2.2.2.2.1.continuousOn
          hc.2.2.2.2.2.2.2.2.1).measurable_piecewise continuousOn_const hc.1.measurableSet
      have hm := hR.inter (hc.1.measurableSet.inter
        (((measurableSet_Icc : MeasurableSet (Icc a b)).preimage hφ₀).inter
          (measurableSet_eq_fun hf₀ hg₀)))
      convert hm using 1
      ext t
      by_cases ht : t ∈ U (e n) <;> simp [f₀, φ₀, g₀, ht]
    · exact MeasurableSet.empty
  have hUnion : (⋃ n, A n) = R := by
    apply Subset.antisymm
    · intro t ht
      obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      by_cases hnT : e n ∈ T
      · simp only [A, ite_eq_left hnT] at hn
        exact hn.1
      · simp [A, hnT] at hn
    · intro t ht
      obtain ⟨s, hs, hts⟩ := ht.2.2.2
      have hpair : (t, s) ∈ C := ⟨ht, hs, hts.symm⟩
      obtain ⟨p, hp, htp, hsp⟩ := mem_iUnion₂.mp (hcover hpair)
      obtain ⟨n, rfl⟩ := he hp
      refine mem_iUnion.mpr ⟨n, ?_⟩
      have hφs := (hcharts (e n) hp).2.2.2.2.2.2.2.2.2 t htp s hsp hts.symm
      simp only [A, ite_eq_left hp, mem_inter_iff, mem_ofPred_eq]
      exact ⟨ht, htp, hφs.symm ▸ hs, by simpa only [hφs] using hts.symm⟩
  let S := disjointed A
  have hSA (n : ℕ) : S n ⊆ A n := disjointed_subset A n
  have hSR (n : ℕ) : S n ⊆ R := fun t ht => hUnion ▸ mem_iUnion.mpr ⟨n, hSA n ht⟩
  let B : ℕ → Set ℝ := fun n => if e n ∈ T then U (e n) else ∅
  refine ⟨⟨S, B, fun n => φ (e n), MeasurableSet.disjointed hA,
    disjoint_disjointed A, by simpa only [S, iUnion_disjointed] using hUnion,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro n
    dsimp only [B]
    split_ifs with hn
    · exact (hcharts (e n) hn).1
    · exact isOpen_empty
  · intro n t ht
    have htA := hSA n ht
    by_cases hn : e n ∈ T
    · simp only [A, ite_eq_left hn] at htA
      simpa only [B, ite_eq_left hn] using htA.2.1
    · simp [A, hn] at htA
  · intro n
    by_cases hn : e n ∈ T
    · simpa only [B, ite_eq_left hn] using (hcharts (e n) hn).2.2.2.2.1
    · simp only [B, ite_eq_right hn]
      exact contDiffOn_empty
  · intro n
    by_cases hn : e n ∈ T
    · simpa only [B, ite_eq_left hn] using (hcharts (e n) hn).2.2.2.2.2.2.1
    · simp only [B, ite_eq_right hn]
      exact contDiffOn_empty
  · intro n
    by_cases hn : e n ∈ T
    · simpa only [B, ite_eq_left hn] using (hcharts (e n) hn).2.2.2.2.2.2.2.1
    · simp [B, hn]
  · intro n t ht
    have htA := hSA n ht
    by_cases hn : e n ∈ T
    · simp only [A, ite_eq_left hn] at htA
      exact htA.2.2.1
    · simp [A, hn] at htA
  · intro n t ht
    have htA := hSA n ht
    by_cases hn : e n ∈ T
    · simp only [A, ite_eq_left hn] at htA
      exact htA.2.2.2
    · simp [A, hn] at htA


namespace ArcCoincidencePartition

/-- Each piece consists of actual regular original times. -/
theorem piece_subset {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (n : ℕ) :
    P.piece n ⊆ regularArcSource η g a b := by
  intro t ht
  rw [← P.cover]
  exact mem_iUnion.mpr ⟨n, ht⟩

theorem measurable_image {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (n : ℕ) :
    MeasurableSet (P.parameter n '' P.piece n) :=
  (P.measurable n).image_of_continuousOn_injOn
    ((P.parameter_smooth n).continuousOn.mono (P.subset_chart n))
    ((P.parameter_injective n).mono (P.subset_chart n))

/-- Actual signed change of variables on every constructed piece, with the
norm equality needed to justify the eventual countable sum. -/
theorem transport {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (V : Set ℝ) (hV : IsOpen V)
    (hsub : Icc a b ⊆ V) (hg : ContDiffOn ℝ 1 g V)
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (q : ℂ → ℂ) (n : ℕ) :
    (IntegrableOn (fun t => q (η t) * deriv η t) (P.piece n) ↔
      Integrable (P.density q n)) ∧
    (∫ t in P.piece n, q (η t) * deriv η t) = ∫ s, P.density q n s ∧
    (∫ t in P.piece n, ‖q (η t) * deriv η t‖) = ∫ s, ‖P.density q n s‖ := by
  have H := coincidence_tangent_change_of_variables η g (P.parameter n)
    (P.piece n) (P.measurable n) (P.factorization n)
    (fun t ht => ((P.path_smooth n).contDiffAt
      ((P.chart_open n).mem_nhds (P.subset_chart n ht))).differentiableAt_one)
    (fun t ht => ((P.parameter_smooth n).contDiffAt
      ((P.chart_open n).mem_nhds (P.subset_chart n ht))).differentiableAt_one)
    (fun t ht => (hg.contDiffAt
      (hV.mem_nhds (hsub (P.parameter_mem n ht)))).differentiableAt_one)
    (fun t ht => hreg _ (P.parameter_mem n ht))
    ((P.parameter_injective n).mono (P.subset_chart n)) q
  dsimp only at H
  refine ⟨H.1.trans ?_, ?_, ?_⟩
  · exact (integrable_indicator_iff (P.measurable_image n)).symm
  · rw [density, integral_indicator (P.measurable_image n)]
    exact H.2.1
  · simp only [density, norm_indicator_eq_indicator_norm]
    rw [integral_indicator (P.measurable_image n)]
    exact H.2.2

/-- Countable transport has absolute norm control, derived from the original
integrability rather than assumed on the target densities. -/
theorem hasSum_transport {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (V : Set ℝ) (hV : IsOpen V)
    (hsub : Icc a b ⊆ V) (hg : ContDiffOn ℝ 1 g V)
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (q : ℂ → ℂ)
    (hq : IntegrableOn (fun t => q (η t) * deriv η t) (regularArcSource η g a b)) :
    (∀ n, Integrable (P.density q n)) ∧
    HasSum (fun n => ∫ s, P.density q n s)
      (∫ t in regularArcSource η g a b, q (η t) * deriv η t) ∧
    HasSum (fun n => ∫ s, ‖P.density q n s‖)
      (∫ t in regularArcSource η g a b, ‖q (η t) * deriv η t‖) := by
  have htransport (n : ℕ) := P.transport V hV hsub hg hreg q n
  refine ⟨fun n => (htransport n).1.mp (hq.mono_set (P.piece_subset n)), ?_, ?_⟩
  · have hs := hasSum_integral_iUnion P.measurable P.disjoint (P.cover ▸ hq)
    simpa only [P.cover, funext (fun n => (htransport n).2.1)] using hs
  · have hs := hasSum_integral_iUnion P.measurable P.disjoint (P.cover ▸ hq.norm)
    simpa only [P.cover, funext (fun n => (htransport n).2.2)] using hs


/-- The countable chart sum is exactly the intrinsic signed original fiber
count at every finite regular fiber. Disjoint source pieces prevent counting
a visit twice, even when target chart images overlap. -/
theorem density_sum {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (hinj : InjOn g (Icc a b))
    (s : ℝ) (hs : s ∈ Icc a b)
    (hf : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s}.Finite)
    (hgood : ∀ t ∈ Icc η.path.a η.path.b, η t = g s →
      t ∉ Set.range η.partition.node ∧ deriv η t ≠ 0)
    (q : ℂ → ℂ) :
    (∑' n, P.density q n s) =
      (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
  classical
  let J : Set ℕ := {n | s ∈ P.parameter n '' P.piece n}
  let B : Set ℝ := {t | t ∈ Icc η.path.a η.path.b ∧ η t = g s}
  let f : J → B := fun n =>
    ⟨Function.invFunOn (P.parameter n) (P.piece n) s, by
      have ht := Function.invFunOn_mem n.property
      refine ⟨(P.piece_subset n ht).1, ?_⟩
      rw [P.factorization n ht, Function.comp_apply, Function.invFunOn_eq n.property]⟩
  have hf_inj : Function.Injective f := by
    intro n m hnm
    apply Subtype.ext
    by_contra hne
    have hv := congrArg Subtype.val hnm
    change Function.invFunOn (P.parameter n) (P.piece n) s =
      Function.invFunOn (P.parameter m) (P.piece m) s at hv
    have hn := Function.invFunOn_mem n.property
    have hm := Function.invFunOn_mem m.property
    have hh := Set.disjoint_left.mp (P.disjoint hne) hn
    exact hh (hv.symm ▸ hm)
  have hf_surj : Function.Surjective f := by
    intro t
    have htR : (t : ℝ) ∈ regularArcSource η g a b :=
      ⟨t.property.1, (hgood t t.property.1 t.property.2).1,
        (hgood t t.property.1 t.property.2).2, ⟨s, hs, t.property.2.symm⟩⟩
    rw [← P.cover] at htR
    obtain ⟨n, htn⟩ := mem_iUnion.mp htR
    have hφt : P.parameter n t = s :=
      hinj (P.parameter_mem n htn) hs ((P.factorization n htn).symm.trans t.property.2)
    have hn : n ∈ J := ⟨t, htn, hφt⟩
    refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
    change Function.invFunOn (P.parameter n) (P.piece n) s = t
    rw [← hφt]
    exact ((P.parameter_injective n).mono (P.subset_chart n)).leftInvOn_invFunOn htn
  let e : J ≃ B := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let H : ℝ → ℂ := fun t =>
    Real.sign ((deriv η t / deriv g s).re) • (q (g s) * deriv g s)
  have hsupport : Function.support (fun n => P.density q n s) ⊆ J := by
    intro n hn
    by_contra hnJ
    change s ∉ P.parameter n '' P.piece n at hnJ
    exact hn (Set.indicator_of_notMem hnJ _)
  calc
    (∑' n, P.density q n s) = ∑' n : J, P.density q n s :=
      (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' n : J, H (e n) := by
      apply tsum_congr
      intro n
      change (P.parameter n '' P.piece n).indicator _ s = _
      rw [Set.indicator_of_mem (show s ∈ P.parameter n '' P.piece n from n.property)]
      rfl
    _ = ∑' t : B, H t := e.tsum_eq (fun t : B => H t)
    _ = ∑ t ∈ hf.toFinset, H t := by
      rw [tsum_subtype B H]
      calc
        (∑' t, B.indicator H t) = ∑ t ∈ hf.toFinset, B.indicator H t :=
          tsum_eq_sum (fun t ht => Set.indicator_of_notMem
            (by simpa only [hf.mem_toFinset] using ht) _)
        _ = _ := Finset.sum_congr rfl (fun t ht =>
          Set.indicator_of_mem (hf.mem_toFinset.mp ht) _)
    _ = _ := by
      unfold tangentSignedMultiplicity
      rw [dite_eq_left hf, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [H]
      rcases lt_trichotomy ((deriv η t / deriv g s).re) 0 with h | h | h
      · simp [Real.sign_of_neg h, h, not_lt.mpr h.le]
      · simp [h]
      · simp [Real.sign_of_pos h, h]


/-- The countable transported density is integrable; its absolute integral
is controlled by the sum of the actual piece norm integrals. -/
theorem integrable_density_sum {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (q : ℂ → ℂ)
    (hF : ∀ n, Integrable (P.density q n))
    (hsum : Summable (fun n => ∫ s, ‖P.density q n s‖)) :
    Integrable (fun s => ∑' n, P.density q n s) := by
  refine ⟨(AEMeasurable.tsum (fun n => (hF n).aemeasurable)).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun s => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun n => (hF n).aestronglyMeasurable.enorm)]
  have he (n : ℕ) : (∫⁻ s, ‖P.density q n s‖ₑ) =
      ENNReal.ofReal (∫ s, ‖P.density q n s‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hF n).norm (ae_of_all _ fun s => norm_nonneg _)]
    simp only [ofReal_norm]
  simp_rw [he]
  exact hsum.tsum_ofReal_lt_top

/-- The weighted many-to-one formula on a measurable coincidence set is
obtained by summing the constructed injective pieces and reindexing the
actual finite fibers. The original path may leave the reference arc. -/
theorem occurrence_integral {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (V : Set ℝ) (hV : IsOpen V)
    (hsub : Icc a b ⊆ V) (hg : ContDiffOn ℝ 1 g V)
    (hinj : InjOn g (Icc a b)) (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (q : ℂ → ℂ)
    (hq : IntegrableOn (fun t => q (η t) * deriv η t) (regularArcSource η g a b)) :
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) (Icc a b) ∧
    (∫ t in regularArcSource η g a b, q (η t) * deriv η t) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
  classical
  have H := P.hasSum_transport V hV hsub hg hreg q hq
  have hgvisit := regular_curve_visit_values η g a b V hV hsub hg hreg
  rw [ae_restrict_iff' measurableSet_Icc] at hgvisit
  let F : ℝ → ℂ := fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
    (q (g s) * deriv g s)
  have heq : (fun s => ∑' n, P.density q n s) =ᵐ[volume] (Icc a b).indicator F := by
    filter_upwards [hgvisit] with s hvisit
    by_cases hs : s ∈ Icc a b
    · rw [Set.indicator_of_mem hs]
      exact P.density_sum hinj s hs (hvisit hs).1
        (fun t ht he => ⟨((hvisit hs).2 t ht he).2.1,
          ((hvisit hs).2 t ht he).2.2.2⟩) q
    · rw [Set.indicator_of_notMem hs]
      have hz (n : ℕ) : P.density q n s = 0 := by
        apply Set.indicator_of_notMem
        rintro ⟨t, ht, he⟩
        exact hs (he ▸ P.parameter_mem n ht)
      simp only [hz, tsum_zero]
  have hi := P.integrable_density_sum q H.1 H.2.2.summable
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mp (hi.congr heq), ?_⟩
  calc
    (∫ t in regularArcSource η g a b, q (η t) * deriv η t) =
        ∑' n, ∫ s, P.density q n s := H.2.1.tsum_eq.symm
    _ = ∫ s, ∑' n, P.density q n s :=
      integral_tsum_of_summable_integral_norm H.1 H.2.2.summable
    _ = ∫ s, (Icc a b).indicator F s := integral_congr_ae heq
    _ = _ := integral_indicator measurableSet_Icc

end ArcCoincidencePartition



/-- Removing only stationary times and the actual finite original partition
nodes preserves the integral on the geometric reference arc. In particular,
the whole preimage of an endpoint or a seam need not be finite or null. -/
theorem path_arc_indicator_integral (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (hg : ContinuousOn g (Icc a b))
    (q : ℂ → ℂ)
    (hq : IntegrableOn (fun t => q (η t) * deriv η t) (Icc η.path.a η.path.b)) :
    η.integral ((g '' Icc a b).indicator q) =
      ∫ t in regularArcSource η g a b, q (η t) * deriv η t := by
  classical
  let G := IccExtend η.path.ordered η.path.onInterval
  let F := fun t => q (η t) * deriv η t
  have hG : Continuous G := η.path.onInterval.continuous.Icc_extend'
  have hK : MeasurableSet (g '' Icc a b) := (isCompact_Icc.image_of_continuousOn hg).measurableSet
  have hA : MeasurableSet (G ⁻¹' (g '' Icc a b)) := hK.preimage hG.measurable
  have he (t : ℝ) (ht : t ∈ Icc η.path.a η.path.b) :
      (g '' Icc a b).indicator q (η t) * deriv η t =
        (G ⁻¹' (g '' Icc a b)).indicator F t := by
    have hGt : G t = η t := IccExtend_of_mem η.path.ordered _ ht
    by_cases hmem : η t ∈ g '' Icc a b <;> simp [Set.indicator, F, hGt, hmem]
  have hraw : IntervalIntegrable (fun t => (g '' Icc a b).indicator q (η t) * deriv η t)
      volume η.path.a η.path.b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le η.path.ordered).mpr
    exact (hq.indicator hA).congr_fun (fun t ht => (he t ht).symm) measurableSet_Icc
  rw [path_integral_eq_interval_of_integrable η _ hraw,
    intervalIntegral.integral_of_le η.path.ordered, ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ t in Icc η.path.a η.path.b,
      (g '' Icc a b).indicator q (η t) * deriv η t) =
        ∫ t in Icc η.path.a η.path.b, (G ⁻¹' (g '' Icc a b)).indicator F t :=
      setIntegral_congr_fun measurableSet_Icc he
    _ = ∫ t in (Icc η.path.a η.path.b) ∩ (G ⁻¹' (g '' Icc a b)), F t :=
      setIntegral_indicator hA
    _ = _ := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        (measurableSet_Icc.inter hA).nullMeasurableSet
      · intro t ht
        have hGt : G t = η t := IccExtend_of_mem η.path.ordered _ ht.1
        exact ⟨ht.1, by simpa only [mem_preimage, hGt] using ht.2.2.2⟩
      · filter_upwards [(Set.finite_range η.partition.node).countable.ae_notMem volume]
          with t hnode ht
        have hGt : G t = η t := IccExtend_of_mem η.path.ordered _ ht.1.1
        have hn : deriv η t = 0 := by
          by_contra hne
          apply ht.2
          exact ⟨ht.1.1, hnode, hne, by simpa only [mem_preimage, hGt] using ht.1.2⟩
        simp only [F, hn, mul_zero]

/-- Full signed occurrence formula for the part of an arbitrary original PC1
path on an injective regular reference arc. No local or global containment
of the original path in that arc is required. -/
theorem pc1_arc_coincidence_integral_of_integrable (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hinj : InjOn g (Icc a b))
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (q : ℂ → ℂ)
    (hparam : IntegrableOn (fun t => q (η t) * deriv η t) (Icc η.path.a η.path.b)) :
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) (Icc a b) ∧
    η.integral ((g '' Icc a b).indicator q) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
  obtain ⟨P⟩ := pc1_coincidence_partition η g a b V hV hsub hg hreg
  have H := P.occurrence_integral V hV hsub hg hinj hreg q
    (hparam.mono_set (fun t ht => ht.1))
  exact ⟨H.1, (path_arc_indicator_integral η g a b (hg.continuousOn.mono hsub) q hparam).trans H.2⟩

/-- Continuous fields on the actual original trace satisfy the integrability
hypothesis of the measurable coincidence formula. -/
theorem pc1_arc_coincidence_integral (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hinj : InjOn g (Icc a b))
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (q : ℂ → ℂ) (hq : ContinuousOn q η.trace) :
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) (Icc a b) ∧
    η.integral ((g '' Icc a b).indicator q) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s) := by
  apply pc1_arc_coincidence_integral_of_integrable η g a b V hV hsub hg hinj hreg q
  exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
    (C1Partition.parameter_integrable η.path η.partition q hq).1


/-- Borel geometric restrictions preserve original parameter integrability.
No regularity of the field across the restricting set is required. -/
theorem path_parameter_indicator_integrable (η : PiecewiseC1Path)
    (S : Set ℂ) (hS : MeasurableSet S) (q : ℂ → ℂ)
    (hq : IntegrableOn (fun t => q (η t) * deriv η t) (Icc η.path.a η.path.b)) :
    IntegrableOn (fun t => S.indicator q (η t) * deriv η t) (Icc η.path.a η.path.b) := by
  classical
  let G := IccExtend η.path.ordered η.path.onInterval
  have hG : Continuous G := η.path.onInterval.continuous.Icc_extend'
  have hm : MeasurableSet (G ⁻¹' S) := hS.preimage hG.measurable
  apply (hq.indicator hm).congr_fun _ measurableSet_Icc
  intro t ht
  have hGt : G t = η t := IccExtend_of_mem η.path.ordered _ ht
  by_cases hmem : η t ∈ S <;> simp [Set.indicator, hGt, hmem]

/-- Signed counting on an arbitrary Borel subset of a regular reference arc.
This permits assigning overlapping faces to disjoint geometric pieces, even
when the overlap has a complicated closed or positive-length subset. -/
theorem pc1_arc_subset_integral (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hinj : InjOn g (Icc a b))
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (S : Set ℂ) (hS : MeasurableSet S) (hSK : S ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (hq : ContinuousOn q η.trace) :
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (S.indicator q (g s) * deriv g s)) (Icc a b) ∧
    η.integral (S.indicator q) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
          (S.indicator q (g s) * deriv g s) := by
  have hparam : IntegrableOn (fun t => q (η t) * deriv η t) (Icc η.path.a η.path.b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      (C1Partition.parameter_integrable η.path η.partition q hq).1
  have H := pc1_arc_coincidence_integral_of_integrable η g a b V hV hsub hg hinj hreg
    (S.indicator q) (path_parameter_indicator_integrable η S hS q hparam)
  have he : (g '' Icc a b).indicator (S.indicator q) = S.indicator q := by
    classical
    ext z
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (hSK hz)]
    · by_cases hzK : z ∈ g '' Icc a b <;> simp [Set.indicator, hz, hzK]
  rw [he] at H
  exact H

/-- The measurable coincidence formula preserves every original integer
coefficient, including an empty chain and cancellations of identical paths. -/
theorem chain_arc_subset_integral (Γ : IntegralChain) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hinj : InjOn g (Icc a b))
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (S : Set ℂ) (hS : MeasurableSet S) (hSK : S ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (hq : ContinuousOn q Γ.trace) :
    IntegrableOn (fun s => (chainTangentMultiplicity Γ (g s) (deriv g s) : ℂ) *
      (S.indicator q (g s) * deriv g s)) (Icc a b) ∧
    Γ.integral (S.indicator q) =
      ∫ s in Icc a b,
        (chainTangentMultiplicity Γ (g s) (deriv g s) : ℂ) *
          (S.indicator q (g s) * deriv g s) := by
  have H (η : PiecewiseC1Path) (hη : η ∈ Γ.support) :=
    pc1_arc_subset_integral η g a b V hV hsub hg hinj hreg S hS hSK q
      (hq.mono (fun z hz => ⟨η, hη, hz⟩))
  have heq (s : ℝ) :
      (∑ η ∈ Γ.support, (Γ η : ℂ) *
        ((tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
          (S.indicator q (g s) * deriv g s))) =
      (chainTangentMultiplicity Γ (g s) (deriv g s) : ℂ) *
        (S.indicator q (g s) * deriv g s) := by
    simp only [chainTangentMultiplicity, Finsupp.sum, Int.cast_sum, Int.cast_mul,
      Finset.sum_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · have hi : IntegrableOn (fun s => ∑ η ∈ Γ.support, (Γ η : ℂ) *
        ((tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
          (S.indicator q (g s) * deriv g s))) (Icc a b) :=
        integrable_finsetSum Γ.support (fun η hη => (H η hη).1.const_mul (Γ η : ℂ))
    exact hi.congr_fun (fun s _ => heq s) measurableSet_Icc
  · calc
      Γ.integral (S.indicator q) = ∑ η ∈ Γ.support, (Γ η : ℂ) *
          ∫ s in Icc a b, (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
            (S.indicator q (g s) * deriv g s) := by
        exact Finset.sum_congr rfl (fun η hη => congrArg ((Γ η : ℂ) * ·) (H η hη).2)
      _ = ∫ s in Icc a b, ∑ η ∈ Γ.support, (Γ η : ℂ) *
          ((tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
            (S.indicator q (g s) * deriv g s)) := by
        simp_rw [← integral_const_mul]
        exact (integral_finsetSum Γ.support (fun η hη =>
          (H η hη).1.const_mul (Γ η : ℂ))).symm
      _ = _ := setIntegral_congr_fun measurableSet_Icc (fun s _ => heq s)

/-- Equality of intrinsic signed visits on a reference arc gives comparison
on every Borel subset of that arc. No single-sheet ambient atlas is assumed. -/
theorem chain_arc_subset_comparison (Γ Δ : IntegralChain) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) (hinj : InjOn g (Icc a b))
    (hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (hcount : ∀ᵐ s ∂volume.restrict (Icc a b),
      chainTangentMultiplicity Γ (g s) (deriv g s) =
        chainTangentMultiplicity Δ (g s) (deriv g s))
    (S : Set ℂ) (hS : MeasurableSet S) (hSK : S ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (hq : ContinuousOn q (Γ.trace ∪ Δ.trace)) :
    Γ.integral (S.indicator q) = Δ.integral (S.indicator q) := by
  rw [(chain_arc_subset_integral Γ g a b V hV hsub hg hinj hreg S hS hSK q
      (hq.mono subset_union_left)).2,
    (chain_arc_subset_integral Δ g a b V hV hsub hg hinj hreg S hS hSK q
      (hq.mono subset_union_right)).2]
  apply integral_congr_ae
  filter_upwards [hcount] with s hs
  rw [hs]


/-- A finite disjoint Borel partition of the geometric image gives the sum
of the actual restricted original path integrals. -/
theorem path_integral_indicator_iUnion (η : PiecewiseC1Path) {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (q : ℂ → ℂ) (hq : ContinuousOn q η.trace) :
    η.integral ((⋃ i, S i).indicator q) = ∑ i, η.integral ((S i).indicator q) := by
  let G := IccExtend η.path.ordered η.path.onInterval
  let F := fun t => q (η t) * deriv η t
  let μ := volume.restrict (Ioc η.path.a η.path.b)
  have hG : Continuous G := η.path.onInterval.continuous.Icc_extend'
  have hF : Integrable F μ :=
    (C1Partition.parameter_integrable η.path η.partition q hq).1
  have hformula (A : Set ℂ) (hA : MeasurableSet A) :
      η.integral (A.indicator q) = ∫ t in G ⁻¹' A, F t ∂μ := by
    rw [path_indicator_formula η A hA q hq, intervalIntegral.integral_of_le η.path.ordered,
      integral_indicator (hA.preimage hG.measurable)]
  rw [hformula _ (MeasurableSet.iUnion hS), preimage_iUnion]
  rw [integral_iUnion_fintype (fun i => (hS i).preimage hG.measurable)
    (fun i j hij => (hd hij).preimage G) (fun _ => hF.integrableOn)]
  exact Finset.sum_congr rfl (fun i _ => (hformula _ (hS i)).symm)

/-- Finite Borel subdivision also respects all original chain coefficients. -/
theorem chain_integral_indicator_iUnion (Γ : IntegralChain) {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (q : ℂ → ℂ) (hq : ContinuousOn q Γ.trace) :
    Γ.integral ((⋃ i, S i).indicator q) = ∑ i, Γ.integral ((S i).indicator q) := by
  calc
    Γ.integral ((⋃ i, S i).indicator q) =
        ∑ η ∈ Γ.support, (Γ η : ℂ) * ∑ i, η.integral ((S i).indicator q) := by
      exact Finset.sum_congr rfl (fun η hη => congrArg ((Γ η : ℂ) * ·)
        (path_integral_indicator_iUnion η S hS hd q
          (hq.mono (fun z hz => ⟨η, hη, hz⟩))))
    _ = _ := by
      simp only [IntegralChain.integral, Finsupp.sum, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Global analytic comparison from actual signed occurrences on a finite
regular arc carrier. The original paths may move among the arcs infinitely
often, and distinct arcs may meet on arbitrary measurable sets. A countable
seam is treated by zero original velocity a.e., never by finite preimages.
This is a comparison lemma; the source full-positive geometric relation and
its induced signed incidence still have to be established for a cell region. -/
theorem finite_regular_arc_comparison (Γ Δ : IntegralChain)
    (n : ℕ) (g : Fin n → ℝ → ℂ) (a b : Fin n → ℝ) (V : Fin n → Set ℝ)
    (hV : ∀ i, IsOpen (V i)) (hsub : ∀ i, Icc (a i) (b i) ⊆ V i)
    (hg : ∀ i, ContDiffOn ℝ 1 (g i) (V i))
    (hinj : ∀ i, InjOn (g i) (Icc (a i) (b i)))
    (hreg : ∀ i s, s ∈ Icc (a i) (b i) → deriv (g i) s ≠ 0)
    (Z : Set ℂ) (hZ : Z.Countable)
    (hcover : Γ.trace ∪ Δ.trace ⊆ Z ∪ ⋃ i, g i '' Icc (a i) (b i))
    (hcount : ∀ i, ∀ᵐ s ∂volume.restrict (Icc (a i) (b i)),
      chainTangentMultiplicity Γ (g i s) (deriv (g i) s) =
        chainTangentMultiplicity Δ (g i s) (deriv (g i) s))
    (q : ℂ → ℂ) (hq : ContinuousOn q (Γ.trace ∪ Δ.trace)) :
    Γ.integral q = Δ.integral q := by
  let K : Fin n → Set ℂ := fun i => g i '' Icc (a i) (b i)
  have hK (i : Fin n) : MeasurableSet (K i) :=
    (isCompact_Icc.image_of_continuousOn ((hg i).continuousOn.mono (hsub i))).measurableSet
  let S := disjointed K
  have hS (i : Fin n) : MeasurableSet (S i) := by
    rw [show S i = K i ∩ ⋂ j < i, (K j)ᶜ from disjointed_eq_inter_compl K i]
    exact (hK i).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hK j).compl)
  have hUnion : (⋃ i, S i) = ⋃ i, K i := iUnion_disjointed
  have heq (C : IntegralChain) (hC : C.trace ⊆ Γ.trace ∪ Δ.trace) :
      C.integral q = C.integral ((⋃ i, S i).indicator q) := by
    apply chain_integral_congr_off_countable C Z hZ
    intro z hz
    have hzK : z ∈ ⋃ i, S i := by
      rw [hUnion]
      exact (hcover (hC hz.1)).resolve_left hz.2
    exact (Set.indicator_of_mem hzK q).symm
  rw [heq Γ subset_union_left, heq Δ subset_union_right,
    chain_integral_indicator_iUnion Γ S hS (disjoint_disjointed K) q (hq.mono subset_union_left),
    chain_integral_indicator_iUnion Δ S hS (disjoint_disjointed K) q (hq.mono subset_union_right)]
  apply Finset.sum_congr rfl
  intro i _
  exact chain_arc_subset_comparison Γ Δ (g i) (a i) (b i) (V i) (hV i) (hsub i)
    (hg i) (hinj i) (hreg i) (hcount i) (S i) (hS i) (disjointed_subset K i) q hq

/-- The inverse function theorem makes an interior parameter point an
interior image point. No assertion about a smooth chart at a cube corner
is needed. -/
theorem cell_interior_image_mem {O : Set (E 2)} (c : Cell 1 2 O)
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    {x : E 2} (hx : x ∈ interior (cube 2)) :
    cellExtension c x ∈ interior (cellExtension c '' cube 2) := by
  have hc : ContDiffAt ℝ 1 (cellExtension c) x :=
    (D04.Cells.extension_C1 c).contDiffAt
      ((extension_spec c).1.mem_nhds ((extension_spec c).2.1 (interior_subset hx)))
  have hdet : (fderiv ℝ (cellExtension c) x).toLinearMap.det ≠ 0 :=
    (hpos x (interior_subset hx)).ne'
  have hsur : Function.Surjective (fderiv ℝ (cellExtension c) x) :=
    (LinearMap.equivOfDetNeZero _ hdet).surjective
  have hmap := (hc.hasStrictFDerivAt (by norm_num)).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr hsur)
  apply mem_interior_iff_mem_nhds.mpr
  rw [← hmap]
  exact Filter.image_mem_map (mem_interior_iff_mem_nhds.mp hx)

/-- The frontier of an actual regular closed cell is covered by its actual
faces. This is a topological coverage statement, with no signed incidence
or contour comparison among its hypotheses. -/
theorem cell_image_frontier_subset_faces {O : Set (E 2)} (c : Cell 1 2 O)
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det) :
    frontier (cellExtension c '' cube 2) ⊆
      ⋃ i : Fin 2, ⋃ e : Bool, cellExtension (cellFace c i e) '' cube 1 := by
  have hcompact : IsCompact (cellExtension c '' cube 2) :=
    (D04.DiscontinuityCriterion.carrier_compact (cubeBox 2)).image_of_continuousOn
      ((D04.Cells.extension_C1 c).continuousOn.mono (extension_spec c).2.1)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hcompact.isClosed.closure_subset hy.1
  have hxf : x ∈ frontier (cube 2) := by
    refine ⟨subset_closure hx, ?_⟩
    intro hxi
    exact hy.2 (cell_interior_image_mem c hpos hxi)
  rw [D04.GeometricUnion.cube_frontier_faces 1] at hxf
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxf
  obtain ⟨e, u, hu, rfl⟩ := mem_iUnion.mp hi
  refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨e, u, hu, ?_⟩⟩
  exact (D04.Cells.extension_on_cube (cellFace c i e) ⟨u, hu⟩).trans
    (D04.Cells.extension_on_cube c ⟨faceInsertion i e u, faceInsertion_mem i e hu⟩).symm

/-- The finite carrier is the specified actual closed union, including an
empty family. Compactness is derived from the actual extensions. -/
theorem PositiveCellData.carrier_compact {O : Set (E 2)} (d : PositiveCellData O) :
    IsCompact d.carrier := by
  apply isCompact_iUnion
  intro j
  apply IsCompact.image _ complexCoordinates.symm.toContinuousLinearEquiv.continuous
  exact (D04.DiscontinuityCriterion.carrier_compact (cubeBox 2)).image_of_continuousOn
    ((D04.Cells.extension_C1 (d.cells j)).continuousOn.mono (extension_spec (d.cells j)).2.1)

/-- Boundary coverage is derived for the finite actual cell union. Internal
faces are retained; their signed cancellation is a separate issue. -/
theorem PositiveCellData.frontier_subset_faceCarrier {O : Set (E 2)}
    (d : PositiveCellData O) : frontier d.carrier ⊆ d.faceCarrier := by
  have hfront : frontier d.carrier ⊆
      ⋃ j, frontier (complexCoordinates.symm '' (cellExtension (d.cells j) '' cube 2)) := by
    simpa only [PositiveCellData.carrier, Finset.mem_univ, iUnion_true] using
      (Finset.univ : Finset (Fin d.count)).frontier_biUnion_subset
        (fun j => complexCoordinates.symm '' (cellExtension (d.cells j) '' cube 2))
  intro z hz
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hfront hz)
  have heq : complexCoordinates.symm '' frontier (cellExtension (d.cells j) '' cube 2) =
      frontier (complexCoordinates.symm '' (cellExtension (d.cells j) '' cube 2)) :=
    complexCoordinates.symm.toContinuousLinearEquiv.toHomeomorph.image_frontier _
  rw [← heq] at hj
  obtain ⟨y, hy, rfl⟩ := hj
  obtain ⟨i, hi⟩ := mem_iUnion.mp (cell_image_frontier_subset_faces (d.cells j) (d.positive j) hy)
  obtain ⟨e, u, hu, rfl⟩ := mem_iUnion.mp hi
  refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨e, ?_⟩⟩⟩
  rw [cellPath_trace]
  exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩

/-- A finite carrier may use any finite index type; no ordering of the faces
or nonemptiness is required. -/
theorem finite_regular_arc_comparison_fintype (Γ Δ : IntegralChain)
    {ι : Type*} [Fintype ι] (g : ι → ℝ → ℂ) (a b : ι → ℝ) (V : ι → Set ℝ)
    (hV : ∀ i, IsOpen (V i)) (hsub : ∀ i, Icc (a i) (b i) ⊆ V i)
    (hg : ∀ i, ContDiffOn ℝ 1 (g i) (V i))
    (hinj : ∀ i, InjOn (g i) (Icc (a i) (b i)))
    (hreg : ∀ i s, s ∈ Icc (a i) (b i) → deriv (g i) s ≠ 0)
    (Z : Set ℂ) (hZ : Z.Countable)
    (hcover : Γ.trace ∪ Δ.trace ⊆ Z ∪ ⋃ i, g i '' Icc (a i) (b i))
    (hcount : ∀ i, ∀ᵐ s ∂volume.restrict (Icc (a i) (b i)),
      chainTangentMultiplicity Γ (g i s) (deriv (g i) s) =
        chainTangentMultiplicity Δ (g i s) (deriv (g i) s))
    (q : ℂ → ℂ) (hq : ContinuousOn q (Γ.trace ∪ Δ.trace)) :
    Γ.integral q = Δ.integral q := by
  classical
  let e := Fintype.equivFin ι
  apply finite_regular_arc_comparison Γ Δ (Fintype.card ι)
    (fun i => g (e.symm i)) (fun i => a (e.symm i)) (fun i => b (e.symm i))
    (fun i => V (e.symm i)) (fun i => hV _) (fun i => hsub _)
    (fun i => hg _) (fun i => hinj _) (fun i => hreg _) Z hZ ?_
    (fun i => hcount _) q hq
  intro z hz
  rcases hcover hz with hz | hz
  · exact Or.inl hz
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact Or.inr (mem_iUnion.mpr ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩)

/-- Taking support after the actual Finsupp cancellations can only remove
face traces. Repeated faces and zero coefficients do not create extra trace. -/
theorem PositiveCellData.faceContour_trace_subset {O : Set (E 2)}
    (d : PositiveCellData O) : d.faceContour.trace ⊆ d.faceCarrier := by
  classical
  rintro z ⟨η, hη, hz⟩
  by_contra hn
  have hne (j : Fin d.count) (i : Fin 2) (e : Bool) :
      cellPath (cellFace (d.cells j) i e) ≠ η := by
    intro he
    apply hn
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨i,
      mem_iUnion.mpr ⟨e, he.symm ▸ hz⟩⟩⟩
  have hzero : d.faceContour η = 0 := by
    simp [PositiveCellData.faceContour, cellBoundary, map_sum,
      map_sub, cellContour_single, hne]
  exact (Finsupp.mem_support_iff.mp hη) hzero

theorem PositiveCellData.faceCarrier_subset_ambient {O : Set (E 2)}
    (d : PositiveCellData O) : d.faceCarrier ⊆ complexCoordinates ⁻¹' O := by
  intro z hz
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hj
  obtain ⟨e, he⟩ := mem_iUnion.mp hi
  rw [cellPath_trace] at he
  obtain ⟨y, ⟨u, hu, rfl⟩, rfl⟩ := he
  change complexCoordinates (complexCoordinates.symm _) ∈ O
  rw [LinearEquiv.apply_symm_apply,
    (extension_spec (cellFace (d.cells j) i e)).2.2.2 ⟨u, hu⟩]
  exact ((cellFace (d.cells j) i e).toFun ⟨u, hu⟩).property

/-- Specialization to the actual regular cell faces. The hypothesis is still
the explicit signed incidence; this helper does not assert that it follows
from a full positive boundary relation. Coverage, regularity and all choices
of open face neighborhoods are conclusions of the proof. -/
theorem cell_comparison_of_face_incidence {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralChain)
    (hboundary : Γ.trace ⊆ frontier d.carrier)
    (hcount : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      chainTangentMultiplicity Γ (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s) =
      ∑ k, ∑ l : Fin 2, (-1 : ℤ) ^ l.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l true))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s) -
        tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l false))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (hq : ContinuousOn q (complexCoordinates ⁻¹' O)) :
    Γ.integral q = d.faceContour.integral q := by
  let ι := Fin d.count × (Fin 2 × Bool)
  let c : ι → Cell 1 1 O := fun p => cellFace (d.cells p.1) p.2.1 p.2.2
  let g : ι → ℝ → ℂ := fun p => cellCurve (c p)
  let V : ι → Set ℝ := fun p => scalarLine ⁻¹' extensionDomain (c p)
  have hV (p : ι) : IsOpen (V p) :=
    (extension_spec (c p)).1.preimage scalarLine.continuous
  have hsub (p : ι) : Icc (0 : ℝ) 1 ⊆ V p := fun t ht =>
    (extension_spec (c p)).2.1 ((scalarLine_mem_cube t).mpr ht)
  have hg (p : ι) : ContDiffOn ℝ 1 (g p) (V p) :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      ((D04.Cells.extension_C1 (c p)).comp scalarLine.contDiff.contDiffOn (fun _ ht => ht))
  have hregular (p : ι) := regular_cell_face (d.cells p.1)
    (d.injective p.1) (d.positive p.1) p.2.1 p.2.2
  have htr : Γ.trace ∪ d.faceContour.trace ⊆ d.faceCarrier :=
    union_subset (hboundary.trans d.frontier_subset_faceCarrier) d.faceContour_trace_subset
  apply finite_regular_arc_comparison_fintype Γ d.faceContour g (fun _ => 0)
    (fun _ => 1) V hV hsub hg (fun p => (hregular p).1)
    (fun p => (hregular p).2) ∅ Set.countable_empty ?_ ?_ q
    (hq.mono (htr.trans d.faceCarrier_subset_ambient))
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (htr hz)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hj
    obtain ⟨e, he⟩ := mem_iUnion.mp hi
    exact Or.inr (mem_iUnion.mpr ⟨⟨j, i, e⟩, he⟩)
  · intro p
    filter_upwards [hcount p.1 p.2.1 p.2.2] with s hs
    exact hs.trans (cell_assembly_tangent_multiplicity d _ _).symm

/-- The actual D04 signed patch-chain boundary value follows once the
explicit original geometric face incidence has been supplied. This remains
a conditional support theorem, not the source-facing full-boundary theorem. -/
theorem cell_dictionary_of_face_incidence {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralChain)
    (hboundary : Γ.trace ⊆ frontier d.carrier)
    (hcount : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      chainTangentMultiplicity Γ (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s) =
      ∑ k, ∑ l : Fin 2, (-1 : ℤ) ^ l.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l true))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s) -
        tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l false))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (hq : ContinuousOn q (complexCoordinates ⁻¹' O)) :
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer := by
  rw [cell_comparison_of_face_incidence d Γ hboundary hcount q hq]
  exact cell_assembly_dictionary d q hq

/-- The standard oriented coordinate area of the two actual differential
columns is their actual real determinant. -/
theorem determinant_coordinates (A : E 2 →L[ℝ] E 2) :
    A.det =
      (A (standardBasis 2 0)) 0 * (A (standardBasis 2 1)) 1 -
        (A (standardBasis 2 1)) 0 * (A (standardBasis 2 0)) 1 := by
  change A.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix (standardBasis 2), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  rfl

/-- The actual alternating sign makes the positive face tangent and the
inward parameter vector have exactly the ambient cell determinant. -/
theorem cell_face_orientation_det {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) *
        (cellFaceInward c i e t).im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) *
        (cellFaceInward c i e t).re =
      (fderiv ℝ (cellExtension c) (faceInsertion i e (scalarLine t))).det := by
  rw [(cellCurve_hasDerivAt (cellFace c i e) t ht).deriv,
    cellFace_differential_column c i e (scalarLine t) ((scalarLine_mem_cube t).mpr ht),
    determinant_coordinates]
  fin_cases i <;> cases e <;>
    simp [cellFaceSign, cellFaceInward, complexCoordinates, Fin.succAbove] <;> ring

/-- Positive ambient determinant supplies the induced local boundary
orientation. No regularity or nonzero velocity of an original cycle is used. -/
theorem cell_face_induced_orientation {O : Set (E 2)} (c : Cell 1 2 O)
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) *
        (cellFaceInward c i e t).im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) *
        (cellFaceInward c i e t).re := by
  rw [cell_face_orientation_det c i e t ht]
  exact hpos _ (faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ht))

/-- The stipulated lower-dimensional bulk overlaps rule out overlapping
interiors. Their nullity is derived in the actual first cell parameter space,
using D04's full-cube seam theorem and its checked measure bridge. -/
theorem PositiveCellData.cell_interior_image_disjoint {O : Set (E 2)}
    (d : PositiveCellData O) (i j : Fin d.count) (hij : i ≠ j) :
    Disjoint (cellExtension (d.cells i) '' interior (cube 2))
      (interior (cellExtension (d.cells j) '' cube 2)) := by
  have hrank (x : E 2) (hx : x ∈ cube 2) :
      Function.Injective (fderiv ℝ (cellExtension (d.cells i)) x) :=
    (LinearMap.equivOfDetNeZero _ (d.positive i x hx).ne').injective
  have hn := (D04.GeometricUnion.cell_seams_contentZero (d.cells i)
    (show 2 ≤ 2 from le_rfl) (d.injective i) hrank d.bulkSeams).2
  have hzero := D04.MeasureBridge.null_measure_zero (D04.NullCovers.contentZero_null hn)
  let W := interior (cube 2) ∩
    cellExtension (d.cells i) ⁻¹' interior (cellExtension (d.cells j) '' cube 2)
  have hopen : IsOpen W :=
    (((D04.Cells.extension_C1 (d.cells i)).continuousOn).mono
      (interior_subset.trans (extension_spec (d.cells i)).2.1)).isOpen_inter_preimage
        isOpen_interior isOpen_interior
  have hW : W ⊆ cube 2 ∩ cellExtension (d.cells i) ⁻¹' d.bulkSeams.carrier := by
    intro x hx
    refine ⟨interior_subset hx.1, d.bulk_overlap i j hij ?_⟩
    exact ⟨⟨x, interior_subset hx.1, rfl⟩, interior_subset hx.2⟩
  have hempty : W = ∅ := (hopen.measure_eq_zero_iff volume).mp
    (measure_mono_null hW hzero)
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hy
  have hxW : x ∈ W := ⟨hx, hy⟩
  simp only [hempty, mem_empty_iff_false] at hxW

/-- The actual countable lower-dimensional compact-image cover of an ambient
seam is null in full ambient dimension. No finite cover is inferred. -/
theorem ambient_seams_null {k n : ℕ}
    (s : Specs.D04.C15.FiniteGeometricUnionIntegral.Model.AmbientSeams k n)
    (hkn : k ≤ n) : volume s.carrier = 0 := by
  obtain ⟨P, hP, hcover⟩ := s.cover
  have := hP.to_subtype
  have hnull (p : P) : volume (p.val.map '' p.val.parameter) = 0 :=
    D04.MeasureBridge.null_measure_zero (D04.NullCovers.contentZero_null
      (D04.LowerDimensionalImages.compact_local_C1_image
        (lt_of_lt_of_le p.val.lower hkn) p.val.parameter p.val.map
        p.val.compact p.val.localC1).2)
  exact measure_mono_null hcover (measure_iUnion_null hnull)

/-- In particular the interiors of the actual closed cell images are
pairwise disjoint. This follows from the supplied geometric bulk seams,
not from an added disjointness assumption. -/
theorem PositiveCellData.cell_interiors_disjoint {O : Set (E 2)}
    (d : PositiveCellData O) :
    Pairwise (fun i j => Disjoint (interior (cellExtension (d.cells i) '' cube 2))
      (interior (cellExtension (d.cells j) '' cube 2))) := by
  intro i j hij
  have hzero : volume (interior (cellExtension (d.cells i) '' cube 2) ∩
      interior (cellExtension (d.cells j) '' cube 2)) = 0 := by
    apply measure_mono_null _ (ambient_seams_null d.bulkSeams le_rfl)
    intro x hx
    exact d.bulk_overlap i j hij ⟨interior_subset hx.1, interior_subset hx.2⟩
  exact Set.disjoint_iff_inter_eq_empty.mpr
    ((isOpen_interior.inter isOpen_interior).measure_eq_zero_iff volume |>.mp hzero)

/-- At every actual closed-cube point an ambient inverse chart represents
membership in the whole cell image by membership in the actual cube. Compact
injectivity excludes remote sheets. This includes cube corners, without
asserting that the image has a smooth boundary there. -/
theorem cell_local_membership {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (x : E 2) (hx : x ∈ cube 2) :
    ∃ (e : OpenPartialHomeomorph (E 2) (E 2)) (W : Set (E 2)),
      (e : E 2 → E 2) = cellExtension c ∧ x ∈ e.source ∧
      ContDiffAt ℝ 1 e.symm (cellExtension c x) ∧
      IsOpen W ∧ cellExtension c x ∈ W ∧ W ⊆ e.target ∧
      ∀ y ∈ W, (y ∈ cellExtension c '' cube 2 ↔ e.symm y ∈ cube 2) := by
  have hc : ContDiffAt ℝ 1 (cellExtension c) x :=
    (D04.Cells.extension_C1 c).contDiffAt
      ((extension_spec c).1.mem_nhds ((extension_spec c).2.1 hx))
  let A := (fderiv ℝ (cellExtension c) x).toContinuousLinearEquivOfDetNeZero
    (hpos x hx).ne'
  have hA : (A : E 2 →L[ℝ] E 2) = fderiv ℝ (cellExtension c) x :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have hd : HasFDerivAt (cellExtension c) (A : E 2 →L[ℝ] E 2) x := by
    rw [hA]
    exact (hc.differentiableAt (by norm_num)).hasFDerivAt
  let e := hc.toOpenPartialHomeomorph (cellExtension c) hd (by norm_num)
  have hsource : x ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have htarget : cellExtension c x ∈ e.target := e.map_source hsource
  have hInv : ContDiffAt ℝ 1 e.symm (cellExtension c x) :=
    hc.to_localInverse hd (by norm_num)
  let R := cellExtension c '' (cube 2 \ e.source)
  have hR : IsCompact R :=
    ((D04.DiscontinuityCriterion.carrier_compact (cubeBox 2)).diff e.open_source).image_of_continuousOn
      ((D04.Cells.extension_C1 c).continuousOn.mono
        (sdiff_subset.trans (extension_spec c).2.1))
  have hxR : cellExtension c x ∉ R := by
    rintro ⟨u, hu, he⟩
    exact hu.2 (hinj hu.1 hx he ▸ hsource)
  refine ⟨e, e.target ∩ Rᶜ, rfl, hsource, hInv,
    e.open_target.inter hR.isClosed.isOpen_compl, ⟨htarget, hxR⟩, inter_subset_left, ?_⟩
  intro y hy
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huS : u ∈ e.source := by
      by_contra hn
      exact hy.2 ⟨u, ⟨hu, hn⟩, rfl⟩
    exact (e.left_inv huS).symm ▸ hu
  · intro h
    exact ⟨e.symm y, h, e.right_inv hy.1⟩

/-- At a relative interior face point the actual cell region has a genuine
local scalar half-space description, constructed from its ambient inverse.
The other parameter coordinate remains strictly between zero and one. -/
theorem cell_face_local_halfspace {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    let z := cellExtension c (faceInsertion i e (scalarLine t))
    ∃ (W : Set (E 2)) (φ : E 2 → ℝ), IsOpen W ∧ z ∈ W ∧
      ContDiffAt ℝ 1 φ z ∧ φ z = 0 ∧
      fderiv ℝ φ z (complexCoordinates (cellFaceInward c i e t)) = 1 ∧
      fderiv ℝ φ z (complexCoordinates (deriv (cellCurve (cellFace c i e)) t)) = 0 ∧
      ∀ y ∈ W, (y ∈ cellExtension c '' cube 2 ↔ 0 ≤ φ y) := by
  dsimp only
  let x := faceInsertion i e (scalarLine t)
  have hx : x ∈ cube 2 := faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨h, W, hmap, hsource, hInv, hW, hzW, hWt, hmem⟩ :=
    cell_local_membership c hinj hpos x hx
  have hinvx : h.symm (cellExtension c x) = x := by
    rw [← hmap]
    exact h.left_inv hsource
  let L : Fin 2 → E 2 →L[ℝ] ℝ := fun j =>
    (ContinuousLinearMap.proj j).comp (coordinates 2).toContinuousLinearEquiv.toContinuousLinearMap
  have hL (j : Fin 2) (u : E 2) : L j u = u j := rfl
  let U : Set (E 2) := {u | (if e then 0 < L i u else L i u < 1) ∧
    L (i.succAbove 0) u ∈ Ioo (0 : ℝ) 1}
  have hU : IsOpen U := by
    apply IsOpen.inter _ ((L (i.succAbove 0)).continuous.isOpen_preimage _ isOpen_Ioo)
    cases e
    · exact isOpen_lt (L i).continuous continuous_const
    · exact isOpen_lt continuous_const (L i).continuous
  have hxU : x ∈ U := by
    change (if e then 0 < L i x else L i x < 1) ∧ L (i.succAbove 0) x ∈ Ioo 0 1
    simp only [hL, x, D04.Cells.faceInsertion_same, D04.Cells.faceInsertion_other, scalarLine_apply]
    cases e <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_lt_one, true_and] <;> exact ht
  let φ : E 2 → ℝ := fun y => if e then 1 - L i (h.symm y) else L i (h.symm y)
  have hφ : ContDiffAt ℝ 1 φ (cellExtension c x) := by
    have hc := (L i).contDiff.comp_contDiffAt (cellExtension c x) hInv
    cases e
    · exact hc
    · exact contDiffAt_const.sub hc
  have hφx : φ (cellExtension c x) = 0 := by
    dsimp only [φ]
    rw [hinvx, hL]
    simp only [x, D04.Cells.faceInsertion_same]
    cases e <;> norm_num
  have hc : DifferentiableAt ℝ (cellExtension c) x :=
    ((D04.Cells.extension_C1 c).contDiffAt
      ((extension_spec c).1.mem_nhds ((extension_spec c).2.1 hx))).differentiableAt_one
  have hleft : h.symm ∘ cellExtension c =ᶠ[nhds x] id := by
    filter_upwards [h.open_source.mem_nhds hsource] with u hu
    change h.symm (cellExtension c u) = u
    rw [← hmap]
    exact h.left_inv hu
  have hBA : (fderiv ℝ h.symm (cellExtension c x)).comp
      (fderiv ℝ (cellExtension c) x) = ContinuousLinearMap.id ℝ (E 2) := by
    rw [← fderiv_comp x hInv.differentiableAt_one hc, hleft.fderiv_eq]
    exact fderiv_id
  have hBAapply (u : E 2) :
      fderiv ℝ h.symm (cellExtension c x) (fderiv ℝ (cellExtension c) x u) = u :=
    DFunLike.congr_fun hBA u
  have hb : L i (standardBasis 2 i) = 1 := by
    simpa only [hL, standardBasis, D04.standardBasis, ite_true] using
      D04.standardBasis_apply i i
  have hproj := (L i).hasFDerivAt.comp (cellExtension c x)
    hInv.differentiableAt_one.hasFDerivAt
  change HasFDerivAt (fun y => L i (h.symm y))
    ((L i).comp (fderiv ℝ h.symm (cellExtension c x))) (cellExtension c x) at hproj
  have hnormal : fderiv ℝ φ (cellExtension c x)
      (complexCoordinates (cellFaceInward c i e t)) = 1 := by
    cases e
    · change fderiv ℝ (fun y => L i (h.symm y)) (cellExtension c x)
        (complexCoordinates (1 • complexCoordinates.symm
          (fderiv ℝ (cellExtension c) x (standardBasis 2 i)))) = 1
      rw [hproj.fderiv, one_smul, LinearEquiv.apply_symm_apply]
      exact (congrArg (L i) (hBAapply (standardBasis 2 i))).trans hb
    · change fderiv ℝ (fun y => 1 - L i (h.symm y)) (cellExtension c x)
        (complexCoordinates ((-1 : ℝ) • complexCoordinates.symm
          (fderiv ℝ (cellExtension c) x (standardBasis 2 i)))) = 1
      rw [(hproj.const_sub 1).fderiv, map_smul, LinearEquiv.apply_symm_apply]
      simp only [neg_apply, ContinuousLinearMap.comp_apply,
        map_smul, hBAapply, hb, smul_eq_mul, neg_mul, one_mul, neg_neg]
  have hbzero : L i (standardBasis 2 (i.succAbove 0)) = 0 := by
    simpa only [hL, standardBasis, D04.standardBasis, Fin.ne_succAbove, ite_false] using
      D04.standardBasis_apply (i.succAbove 0) i
  have htangent : fderiv ℝ φ (cellExtension c x)
      (complexCoordinates (deriv (cellCurve (cellFace c i e)) t)) = 0 := by
    rw [(cellCurve_hasDerivAt (cellFace c i e) t ⟨ht.1.le, ht.2.le⟩).deriv,
      cellFace_differential_column c i e (scalarLine t)
        ((scalarLine_mem_cube t).mpr ⟨ht.1.le, ht.2.le⟩), LinearEquiv.apply_symm_apply]
    cases e
    · change fderiv ℝ (fun y => L i (h.symm y)) (cellExtension c x)
        (fderiv ℝ (cellExtension c) x (standardBasis 2 (i.succAbove 0))) = 0
      rw [hproj.fderiv]
      exact (congrArg (L i) (hBAapply (standardBasis 2 (i.succAbove 0)))).trans hbzero
    · change fderiv ℝ (fun y => 1 - L i (h.symm y)) (cellExtension c x)
        (fderiv ℝ (cellExtension c) x (standardBasis 2 (i.succAbove 0))) = 0
      rw [(hproj.const_sub 1).fderiv]
      simp only [neg_apply, ContinuousLinearMap.comp_apply, hBAapply, hbzero, neg_zero]
  have hcube (u : E 2) (hu : u ∈ U) :
      u ∈ cube 2 ↔ 0 ≤ (if e then 1 - L i u else L i u) := by
    change (if e then 0 < L i u else L i u < 1) ∧
      L (i.succAbove 0) u ∈ Ioo 0 1 at hu
    constructor
    · intro hcu
      cases e
      · exact (hcu i).1
      · exact sub_nonneg.mpr (hcu i).2
    · intro hcu j
      refine Fin.succAboveCases i ?_ (fun l => ?_) j
      · cases e
        · exact ⟨hcu, hu.1.le⟩
        · exact ⟨hu.1.le, sub_nonneg.mp hcu⟩
      · have hl : l = 0 := Subsingleton.elim _ _
        subst l
        exact ⟨hu.2.1.le, hu.2.2.le⟩
  refine ⟨W ∩ (h.target ∩ h.symm ⁻¹' U), φ,
    hW.inter (h.continuousOn_symm.isOpen_inter_preimage h.open_target hU),
    ⟨hzW, hWt hzW, ?_⟩, hφ, hφx, hnormal, htangent, ?_⟩
  · change h.symm (cellExtension c x) ∈ U
    rw [hinvx]
    exact hxU
  · intro y hy
    exact (hmem y hy.1).trans (hcube (h.symm y) hy.2.2)

/-- The actual inward differential column enters the cell interior, and its
negative exits the whole closed cell, for all sufficiently small positive
steps. This is a geometric side statement, derived from the local inverse
and its normalized defining function. -/
theorem cell_face_inward_sides {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    let z := cellExtension c (faceInsertion i e (scalarLine t))
    let v := complexCoordinates (cellFaceInward c i e t)
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • v ∈ interior (cellExtension c '' cube 2) ∧
      z - r • v ∉ cellExtension c '' cube 2 := by
  dsimp only
  let z := cellExtension c (faceInsertion i e (scalarLine t))
  let v := complexCoordinates (cellFaceInward c i e t)
  obtain ⟨W, φ, hW, hzW, hφ, hφz, hnormal, _, hmem⟩ :=
    cell_face_local_halfspace c hinj hpos i e t ht
  change fderiv ℝ φ z v = 1 at hnormal
  let line : ℝ → E 2 := fun r => z + r • v
  have hline : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  have hlinezero : line 0 = z := by simp only [line, zero_smul, add_zero]
  have hdline : HasDerivAt line v 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z using 1 <;>
      simp [line]
  let F := φ ∘ line
  have hdF : HasDerivAt F 1 0 := by
    have hd := hφ.differentiableAt_one.hasFDerivAt.comp_hasDerivAt_of_eq 0 hdline hlinezero.symm
    change HasDerivAt F (fderiv ℝ φ z v) 0 at hd
    rwa [hnormal] at hd
  have hFzero : F 0 = 0 := by simpa only [F, Function.comp_apply, hlinezero] using hφz
  have hsign : ∀ᶠ r in nhds (0 : ℝ), SignType.sign (F r) = SignType.sign r := by
    simpa only [sub_zero] using eventually_nhdsWithin_sign_eq_of_deriv_pos
      (show 0 < deriv F 0 by rw [hdF.deriv]; norm_num) hFzero
  have hcl : Tendsto line (nhds (0 : ℝ)) (nhds z) := by
    have hc0 := hline.continuousAt (x := 0)
    change Tendsto line (nhds (0 : ℝ)) (nhds (line 0)) at hc0
    rwa [hlinezero] at hc0
  have hlineW : ∀ᶠ r in nhds (0 : ℝ), line r ∈ W := hcl (hW.mem_nhds hzW)
  have hcont : ∀ᶠ r in nhds (0 : ℝ), ContinuousAt φ (line r) := by
    have hp := hcl (hφ.eventually (by norm_num))
    filter_upwards [hp] with r hr
    change ContDiffAt ℝ 1 φ (line r) at hr
    exact hr.continuousAt
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp (hsign.and (hlineW.and hcont))
  refine ⟨ε, hε, ?_⟩
  intro r hr
  have hp := hεprop (y := r) (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr.1] using hr.2)
  have hm := hεprop (y := -r) (by simpa only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hr.1] using hr.2)
  have hFpos : 0 < F r := by
    have hs : SignType.sign (F r) = 1 := hp.1.trans (sign_pos hr.1)
    exact sign_eq_one_iff.mp hs
  have hFneg : F (-r) < 0 := by
    have hs : SignType.sign (F (-r)) = -1 := hm.1.trans (sign_neg (neg_neg_of_pos hr.1))
    exact sign_eq_neg_one_iff.mp hs
  constructor
  · apply mem_interior_iff_mem_nhds.mpr
    have hpos : {y | 0 < φ y} ∈ nhds (line r) :=
      hp.2.2.preimage_mem_nhds (Ioi_mem_nhds hFpos)
    exact mem_of_superset (inter_mem (hW.mem_nhds hp.2.1) hpos)
      (fun y hy => (hmem y hy.1).mpr hy.2.le)
  · have hneg : φ (z - r • v) < 0 := by
      simpa only [F, Function.comp_apply, line, neg_smul, sub_eq_add_neg] using hFneg
    have hmW : z - r • v ∈ W := by
      simpa only [line, neg_smul, sub_eq_add_neg] using hm.2.1
    intro hK
    exact (not_le_of_gt hneg) ((hmem _ hmW).mp hK)


/-- The chosen extension of a face agrees on its entire closed interval
with the restriction of the ambient cell extension. -/
theorem cellCurve_face_value {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    cellCurve (cellFace c i e) t =
      complexCoordinates.symm (cellExtension c (faceInsertion i e (scalarLine t))) := by
  apply congrArg complexCoordinates.symm
  exact (D04.Cells.extension_on_cube (cellFace c i e)
    ⟨scalarLine t, (scalarLine_mem_cube t).mpr ht⟩).trans
      (D04.Cells.extension_on_cube c
        ⟨faceInsertion i e (scalarLine t),
          faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ht)⟩).symm

/-- A real covector computes oriented area relative to its tangent kernel.
This identity does not assume that any of the vectors are nonzero. -/
theorem linear_functional_area (L : ℂ →L[ℝ] ℝ) (v n w : ℂ) :
    L w * (v.re * n.im - v.im * n.re) =
      L n * (v.re * w.im - v.im * w.re) -
        L v * (n.re * w.im - n.im * w.re) := by
  have hL (z : ℂ) : L z = z.re * L 1 + z.im * L Complex.I := by
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hL w, hL n, hL v]
  ring

/-- A positive derivative through a local defining function enters its
nonnegative region, and the reverse direction leaves the whole region. -/
theorem halfspace_transverse_sides (K W : Set (E 2)) (φ : E 2 → ℝ)
    (z w : E 2) (hW : IsOpen W) (hzW : z ∈ W)
    (hφ : ContDiffAt ℝ 1 φ z) (hzero : φ z = 0)
    (hmem : ∀ y ∈ W, (y ∈ K ↔ 0 ≤ φ y))
    (hpositive : 0 < fderiv ℝ φ z w) :
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • w ∈ interior K ∧ z - r • w ∉ K := by
  let line : ℝ → E 2 := fun r => z + r • w
  have hline : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  have hlinezero : line 0 = z := by simp only [line, zero_smul, add_zero]
  have hdline : HasDerivAt line w 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z using 1 <;> simp [line]
  let F := φ ∘ line
  have hdF : HasDerivAt F (fderiv ℝ φ z w) 0 :=
    hφ.differentiableAt_one.hasFDerivAt.comp_hasDerivAt_of_eq 0 hdline hlinezero.symm
  have hFzero : F 0 = 0 := by simpa only [F, Function.comp_apply, hlinezero] using hzero
  have hsign : ∀ᶠ r in nhds (0 : ℝ), SignType.sign (F r) = SignType.sign r := by
    simpa only [sub_zero] using eventually_nhdsWithin_sign_eq_of_deriv_pos
      (show 0 < deriv F 0 by rw [hdF.deriv]; exact hpositive) hFzero
  have hcl : Tendsto line (nhds (0 : ℝ)) (nhds z) := by
    have hc0 := hline.continuousAt (x := 0)
    change Tendsto line (nhds (0 : ℝ)) (nhds (line 0)) at hc0
    rwa [hlinezero] at hc0
  have hlineW : ∀ᶠ r in nhds (0 : ℝ), line r ∈ W := hcl (hW.mem_nhds hzW)
  have hcont : ∀ᶠ r in nhds (0 : ℝ), ContinuousAt φ (line r) := by
    have hp := hcl (hφ.eventually (by norm_num))
    filter_upwards [hp] with r hr
    exact (show ContDiffAt ℝ 1 φ (line r) from hr).continuousAt
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp (hsign.and (hlineW.and hcont))
  refine ⟨ε, hε, ?_⟩
  intro r hr
  have hp := hεprop (y := r) (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr.1] using hr.2)
  have hm := hεprop (y := -r) (by simpa only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hr.1] using hr.2)
  have hFpos : 0 < F r := sign_eq_one_iff.mp (hp.1.trans (sign_pos hr.1))
  have hFneg : F (-r) < 0 :=
    sign_eq_neg_one_iff.mp (hm.1.trans (sign_neg (neg_neg_of_pos hr.1)))
  constructor
  · apply mem_interior_iff_mem_nhds.mpr
    have hpos : {y | 0 < φ y} ∈ nhds (line r) :=
      hp.2.2.preimage_mem_nhds (Ioi_mem_nhds hFpos)
    exact mem_of_superset (inter_mem (hW.mem_nhds hp.2.1) hpos)
      (fun y hy => (hmem y hy.1).mpr hy.2.le)
  · have hneg : φ (z - r • w) < 0 := by
      simpa only [F, Function.comp_apply, line, neg_smul, sub_eq_add_neg] using hFneg
    have hmW : z - r • w ∈ W := by
      simpa only [line, neg_smul, sub_eq_add_neg] using hm.2.1
    intro hK
    exact (not_le_of_gt hneg) ((hmem _ hmW).mp hK)

/-- Every transversal on the induced left side enters the actual cell.
The transversal need not equal the cell's own inward differential column. -/
theorem cell_face_transverse_sides {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (w : ℂ)
    (hleft : 0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) * w.im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) * w.re) :
    let z := cellExtension c (faceInsertion i e (scalarLine t))
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • complexCoordinates w ∈ interior (cellExtension c '' cube 2) ∧
      z - r • complexCoordinates w ∉ cellExtension c '' cube 2 := by
  dsimp only
  let z := cellExtension c (faceInsertion i e (scalarLine t))
  let T : ℂ := (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace c i e)) t
  let N := cellFaceInward c i e t
  obtain ⟨W, φ, hW, hzW, hφ, hzero, hnormal, htangent, hmem⟩ :=
    cell_face_local_halfspace c hinj hpos i e t ht
  let L : ℂ →L[ℝ] ℝ := (fderiv ℝ φ z).comp
    complexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap
  have hLN : L N = 1 := hnormal
  have hLT : L T = 0 := by
    change fderiv ℝ φ z (complexCoordinates ((cellFaceSign i e : ℝ) • _)) = 0
    rw [map_smul, map_smul, htangent, smul_zero]
  have harea : 0 < T.re * N.im - T.im * N.re := by
    simpa only [T, Complex.smul_re, Complex.smul_im, smul_eq_mul] using
      cell_face_induced_orientation c hpos i e t ⟨ht.1.le, ht.2.le⟩
  have hw : 0 < L w := by
    have h := linear_functional_area L T N w
    rw [hLN, hLT, one_mul, zero_mul, sub_zero] at h
    apply (mul_pos_iff_of_pos_right harea).mp
    rw [h]
    simpa only [T, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hleft
  exact halfspace_transverse_sides _ W φ z (complexCoordinates w)
    hW hzW hφ hzero hmem hw

/-- At a common relative-interior face point, disjoint cell interiors force
parallel induced tangents to point in opposite directions. This includes
isolated and positive-length tangential contacts. -/
theorem disjoint_cell_face_orientation {O : Set (E 2)} (c d : Cell 1 2 O)
    (hc : InjOn (cellExtension c) (cube 2))
    (hd : InjOn (cellExtension d) (cube 2))
    (hpc : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (hpd : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension d) x).det)
    (hdisjoint : Disjoint (interior (cellExtension c '' cube 2))
      (interior (cellExtension d '' cube 2)))
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace c i e) t = cellCurve (cellFace d j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace c i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace d j f)) s)) :
    a < 0 := by
  let T : ℂ := (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace c i e)) t
  let S : ℂ := (cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace d j f)) s
  let w := cellFaceInward c i e t
  have hleft : 0 < T.re * w.im - T.im * w.re := by
    simpa only [T, Complex.smul_re, Complex.smul_im, smul_eq_mul] using
      cell_face_induced_orientation c hpc i e t ⟨ht.1.le, ht.2.le⟩
  have hmul : T.re * w.im - T.im * w.re = a * (S.re * w.im - S.im * w.re) := by
    change T = a • S at htangent
    rw [htangent, Complex.smul_re, Complex.smul_im]
    simp only [smul_eq_mul]
    ring
  by_contra hnot
  have ha : 0 < a := by
    have hane : a ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hmul
      linarith
    exact lt_of_le_of_ne (le_of_not_gt hnot) hane.symm
  have hright : 0 < S.re * w.im - S.im * w.re := by
    apply (mul_pos_iff_of_pos_left ha).mp
    rwa [← hmul]
  obtain ⟨ε, hε, hεside⟩ := cell_face_transverse_sides c hc hpc i e t ht w
    (by simpa only [T, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hleft)
  obtain ⟨δ, hδ, hδside⟩ := cell_face_transverse_sides d hd hpd j f s hs w
    (by simpa only [S, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hright)
  have hz : cellExtension c (faceInsertion i e (scalarLine t)) =
      cellExtension d (faceInsertion j f (scalarLine s)) := by
    rw [cellCurve_face_value c i e t ⟨ht.1.le, ht.2.le⟩,
      cellCurve_face_value d j f s ⟨hs.1.le, hs.2.le⟩] at hpoint
    exact complexCoordinates.symm.injective hpoint
  obtain ⟨r, hr0, hr⟩ := exists_between (lt_min hε hδ)
  have hcinside := (hεside r ⟨hr0, (lt_min_iff.mp hr).1⟩).1
  have hdinside := (hδside r ⟨hr0, (lt_min_iff.mp hr).2⟩).1
  rw [← hz] at hdinside
  exact Set.disjoint_left.mp hdisjoint hcinside hdinside


/-- Almost every parameter of either regular curve sees only parallel
velocities at all regular coincidences with the other curve. The images
may intersect on an arbitrary closed set; no common-arc neighborhood is
assumed. -/
theorem regular_curve_coincidence_tangents (f g : ℝ → ℂ) (U V : Set ℝ)
    (hf : ∀ t ∈ U, ContDiffAt ℝ 1 f t) (hg : ∀ s ∈ V, ContDiffAt ℝ 1 g s)
    (hfr : ∀ t ∈ U, deriv f t ≠ 0) (hgr : ∀ s ∈ V, deriv g s ≠ 0) :
    ∀ᵐ t : ℝ, t ∈ U → ∀ s ∈ V, f t = g s →
      ∃ a : ℝ, a ≠ 0 ∧ deriv f t = a • deriv g s := by
  let C : Set (ℝ × ℝ) := {p | p.1 ∈ U ∧ p.2 ∈ V ∧ f p.1 = g p.2}
  have hC (p : ℝ × ℝ) (hp : p ∈ C) :
      ContDiffAt ℝ 1 f p.1 ∧ ContDiffAt ℝ 1 g p.2 ∧
        deriv f p.1 ≠ 0 ∧ deriv g p.2 ≠ 0 ∧ f p.1 = g p.2 :=
    ⟨hf _ hp.1, hg _ hp.2.1,
      hfr _ hp.1, hgr _ hp.2.1, hp.2.2⟩
  obtain ⟨T, hT, _, A, B, φ, hcharts, hcover⟩ :=
    countable_regular_coincidence_charts f g C hC
  have : Countable T := hT.to_subtype
  have hmany : ∀ᵐ t : ℝ, ∀ p : T,
      f t = (g ∘ φ p) t → DifferentiableAt ℝ f t →
        DifferentiableAt ℝ (g ∘ φ p) t → deriv f t = deriv (g ∘ φ p) t :=
    ae_all_iff.mpr (fun p => deriv_eq_ae_on_coincidence f (g ∘ φ p))
  filter_upwards [hmany] with t hmany
  intro ht s hs heq
  obtain ⟨p, hp, hpair⟩ := mem_iUnion₂.mp (hcover (show (t, s) ∈ C from ⟨ht, hs, heq⟩))
  obtain ⟨hA, _, hB, _, _, hgB, hφ, _, hmaps, hmatch⟩ := hcharts p hp
  have hparam : φ p t = s := hmatch t hpair.1 s hpair.2 heq
  have hdφ : DifferentiableAt ℝ (φ p) t :=
    (hφ.contDiffAt (hA.mem_nhds hpair.1)).differentiableAt_one
  have hdg : DifferentiableAt ℝ g (φ p t) :=
    (hgB.contDiffAt (hB.mem_nhds (hmaps hpair.1))).differentiableAt_one
  have hdf : DifferentiableAt ℝ f t := (hf t ht).differentiableAt_one
  have hderiv := hmany ⟨p, hp⟩ (by simpa only [Function.comp_apply, hparam] using heq)
    hdf (hdg.comp t hdφ)
  change deriv f t = deriv (g ∘ φ p) t at hderiv
  rw [deriv.scomp t hdg hdφ, hparam] at hderiv
  have he : deriv f t = deriv (φ p) t • deriv g s := by
    simpa only [smul_eq_mul, mul_comm] using hderiv
  refine ⟨deriv (φ p) t, ?_, he⟩
  intro hz
  rw [hz, zero_smul] at he
  exact hfr t ht he

/-- The orientation conclusion at contact applies directly to the actual
cells of the supplied finite Green decomposition. Disjointness of their
interiors is derived from the original bulk-seam data. -/
theorem PositiveCellData.contact_orientation {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s)) :
    a < 0 :=
  disjoint_cell_face_orientation (d.cells k) (d.cells l) (d.injective k) (d.injective l)
    (d.positive k) (d.positive l) (d.cell_interiors_disjoint hkl)
    i j e f t s a ht hs hpoint htangent


/-- Almost every point of an actual reference face has opposite induced
orientation to every coincident relative-interior face of a different cell.
This is derived from geometric bulk seams and differentiation at coincidence;
there is no signed-incidence or contour-equivalence premise. -/
theorem PositiveCellData.contact_orientation_ae {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      t ∈ Ioo (0 : ℝ) 1 → ∀ s ∈ Ioo (0 : ℝ) 1,
        cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
        ∃ a : ℝ, a < 0 ∧
          (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
            a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s) := by
  let c := cellFace (d.cells k) i e
  let c' := cellFace (d.cells l) j f
  have hsmooth (c : Cell 1 1 O) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 (cellCurve c) t := by
    have h := (D04.Cells.extension_C1 c).contDiffAt
      ((extension_spec c).1.mem_nhds
        ((extension_spec c).2.1 ((scalarLine_mem_cube t).mpr ht)))
    exact complexCoordinates.symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp t
      (h.comp t scalarLine.contDiff.contDiffAt)
  have H := regular_curve_coincidence_tangents (cellCurve c) (cellCurve c')
    (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) (hsmooth c) (hsmooth c')
    (regular_cell_face (d.cells k) (d.injective k) (d.positive k) i e).2
    (regular_cell_face (d.cells l) (d.injective l) (d.positive l) j f).2
  filter_upwards [ae_restrict_of_ae H] with t hparallel
  intro ht s hs hpoint
  obtain ⟨a, _, ha⟩ := hparallel ⟨ht.1.le, ht.2.le⟩ s ⟨hs.1.le, hs.2.le⟩ hpoint
  let b := (cellFaceSign i e : ℝ) * a / (cellFaceSign j f : ℝ)
  have hsign : (cellFaceSign j f : ℝ) ≠ 0 := by
    fin_cases j <;> cases f <;> norm_num [cellFaceSign]
  have htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve c) t =
      b • ((cellFaceSign j f : ℝ) • deriv (cellCurve c') s) := by
    rw [ha, smul_smul, smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hsign).symm
  exact ⟨b, d.contact_orientation k l hkl i j e f t s b ht hs hpoint htangent, htangent⟩


/-- Three cells with disjoint interiors cannot have a common relative-interior
face point with mutually parallel tangents. The ratios may have any magnitudes. -/
theorem PositiveCellData.no_three_parallel_contacts {O : Set (E 2)}
    (d : PositiveCellData O) (k l m : Fin d.count)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (i j q : Fin 2) (e f h : Bool) (t s u a b : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hpointl : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (hpointm : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells m) q h) u)
    (htangentl : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s))
    (htangentm : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      b • ((cellFaceSign q h : ℝ) • deriv (cellCurve (cellFace (d.cells m) q h)) u)) :
    False := by
  have ha := d.contact_orientation k l hkl i j e f t s a ht hs hpointl htangentl
  have hb := d.contact_orientation k m hkm i q e h t u b ht hu hpointm htangentm
  have he : (cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s =
      (b / a) • ((cellFaceSign q h : ℝ) • deriv (cellCurve (cellFace (d.cells m) q h)) u) := by
    calc
      _ = a⁻¹ • ((cellFaceSign i e : ℝ) •
          deriv (cellCurve (cellFace (d.cells k) i e)) t) := by
        rw [htangentl, smul_smul, inv_mul_cancel₀ ha.ne, one_smul]
      _ = _ := by rw [htangentm, smul_smul, div_eq_inv_mul]
  have hneg := d.contact_orientation l m hlm j q f h s u (b / a) hs hu
    (hpointl.symm.trans hpointm) he
  exact (not_lt_of_gt (div_pos_of_neg_of_neg hb ha)) hneg

/-- For almost every reference-face parameter, at most one other cell has
any relative-interior face at the same point. Finiteness is in the cell family;
no finiteness of geometric seam visits or intersections is asserted. -/
theorem PositiveCellData.at_most_two_face_contacts_ae {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      t ∈ Ioo (0 : ℝ) 1 → ∀ (l m : Fin d.count), k ≠ l → k ≠ m →
        ∀ (j q : Fin 2) (f h : Bool) (s u : ℝ),
          s ∈ Ioo (0 : ℝ) 1 → u ∈ Ioo (0 : ℝ) 1 →
          cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
          cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells m) q h) u →
          l = m := by
  have H : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ∀ (l : Fin d.count) (j : Fin 2) (f : Bool), k ≠ l →
        t ∈ Ioo (0 : ℝ) 1 → ∀ s ∈ Ioo (0 : ℝ) 1,
          cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
          ∃ a : ℝ, a < 0 ∧
            (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
              a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s) := by
    apply ae_all_iff.mpr
    intro l
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro f
    by_cases hkl : k = l
    · exact Filter.Eventually.of_forall (by simp [hkl])
    · filter_upwards [d.contact_orientation_ae k l hkl i j e f] with t ht
      exact fun _ => ht
  filter_upwards [H] with t ht
  intro htI l m hkl hkm j q f h s u hs hu hpointl hpointm
  by_contra hlm
  obtain ⟨a, _, ha⟩ := ht l j f hkl htI s hs hpointl
  obtain ⟨b, _, hb⟩ := ht m q h hkm htI u hu hpointm
  exact d.no_three_parallel_contacts k l m hkl hkm hlm i j q e f h t s u a b
    htI hs hu hpointl hpointm ha hb


private theorem signed_count_neg_mul (a x : ℝ) (ha : a < 0) :
    (if 0 < a * x then (1 : ℤ) else if a * x < 0 then -1 else 0) =
      -(if 0 < x then 1 else if x < 0 then -1 else 0) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hp : 0 < a * x := mul_pos_of_neg_of_neg ha hx
    simp only [hp, ↓reduceIte, not_lt_of_gt hx, hx, neg_neg]
  · subst x
    norm_num
  · have hn : a * x < 0 := mul_neg_of_neg_of_pos ha hx
    simp only [not_lt_of_gt hn, hn, hx, ↓reduceIte]

private theorem oriented_signed_count (c : ℤ) (hc : c = 1 ∨ c = -1) (x : ℝ) :
    c * (if 0 < x then (1 : ℤ) else if x < 0 then -1 else 0) =
      if 0 < (c : ℝ) * x then 1 else if (c : ℝ) * x < 0 then -1 else 0 := by
  rcases hc with rfl | rfl
  · norm_num
  · simpa only [Int.cast_neg, Int.cast_one, neg_one_mul] using
      (signed_count_neg_mul (-1) x (by norm_num)).symm

private theorem cellFaceSign_unit (i : Fin 2) (e : Bool) :
    cellFaceSign i e = 1 ∨ cellFaceSign i e = -1 := by
  fin_cases i <;> cases e <;> norm_num [cellFaceSign]

/-- The two actual signed face occurrences cancel at a tangential contact.
This holds relative to every supplied reference velocity, including zero.
The face coefficients are the actual alternating D04 coefficients. -/
theorem PositiveCellData.contact_cancellation {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s))
    (v : ℂ) :
    cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
        (cellCurve (cellFace (d.cells k) i e) t) v +
      cellFaceSign j f * tangentSignedMultiplicity (cellPath (cellFace (d.cells l) j f))
        (cellCurve (cellFace (d.cells k) i e) t) v = 0 := by
  have ha := d.contact_orientation k l hkl i j e f t s a ht hs hpoint htangent
  have hratio : (cellFaceSign i e : ℝ) *
      (deriv (cellCurve (cellFace (d.cells k) i e)) t / v).re =
      a * ((cellFaceSign j f : ℝ) *
        (deriv (cellCurve (cellFace (d.cells l) j f)) s / v).re) := by
    have hh := congrArg (fun z : ℂ => (z / v).re) htangent
    simpa only [smul_div_assoc, Complex.smul_re, smul_eq_mul] using hh
  have hc := tangent_signed_multiplicity_of_injective
    (cellPath (cellFace (d.cells k) i e))
    (regular_cell_face (d.cells k) (d.injective k) (d.positive k) i e).1
    t ⟨ht.1.le, ht.2.le⟩ v
  have hd := tangent_signed_multiplicity_of_injective
    (cellPath (cellFace (d.cells l) j f))
    (regular_cell_face (d.cells l) (d.injective l) (d.positive l) j f).1
    s ⟨hs.1.le, hs.2.le⟩ v
  change tangentSignedMultiplicity _ (cellCurve (cellFace (d.cells k) i e) t) v = _ at hc
  change tangentSignedMultiplicity _ (cellCurve (cellFace (d.cells l) j f) s) v = _ at hd
  rw [hc, hpoint, hd]
  change cellFaceSign i e * (if 0 < (deriv (cellCurve (cellFace (d.cells k) i e)) t / v).re
      then 1 else if (deriv (cellCurve (cellFace (d.cells k) i e)) t / v).re < 0 then -1 else 0) +
    cellFaceSign j f * (if 0 < (deriv (cellCurve (cellFace (d.cells l) j f)) s / v).re
      then 1 else if (deriv (cellCurve (cellFace (d.cells l) j f)) s / v).re < 0 then -1 else 0) = 0
  rw [oriented_signed_count _ (cellFaceSign_unit i e),
    oriented_signed_count _ (cellFaceSign_unit j f), hratio, signed_count_neg_mul _ _ ha]
  exact neg_add_cancel _

/-- The cancellation of actual alternating face occurrences holds almost
everywhere on each reference face, at every regular contact with another cell.
No exceptional contact set is discarded just for lying in a bulk seam. -/
theorem PositiveCellData.contact_cancellation_ae {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      t ∈ Ioo (0 : ℝ) 1 → ∀ s ∈ Ioo (0 : ℝ) 1,
        cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
        ∀ v : ℂ,
          cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
              (cellCurve (cellFace (d.cells k) i e) t) v +
            cellFaceSign j f * tangentSignedMultiplicity (cellPath (cellFace (d.cells l) j f))
              (cellCurve (cellFace (d.cells k) i e) t) v = 0 := by
  filter_upwards [d.contact_orientation_ae k l hkl i j e f] with t ht
  intro htI s hs heq v
  obtain ⟨a, _, ha⟩ := ht htI s hs heq
  exact d.contact_cancellation k l hkl i j e f t s a htI hs heq ha v


/-- At a regular tangential contact the two actual cells occupy opposite
sides of the same transversal. Both sides enter the real cell union, even
when the contact point itself lies on the topological frontier of that union.
No smooth-boundary neighborhood of the union is asserted. -/
theorem PositiveCellData.contact_two_sides {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s)) :
    let z := cellExtension (d.cells k) (faceInsertion i e (scalarLine t))
    let w := complexCoordinates (cellFaceInward (d.cells k) i e t)
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • w ∈ interior (cellExtension (d.cells k) '' cube 2) ∧
      z - r • w ∈ interior (cellExtension (d.cells l) '' cube 2) := by
  dsimp only
  let T := (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t
  let S := (cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s
  let w := cellFaceInward (d.cells k) i e t
  have ha := d.contact_orientation k l hkl i j e f t s a ht hs hpoint htangent
  have hleft : 0 < T.re * w.im - T.im * w.re := by
    simpa only [T, Complex.smul_re, Complex.smul_im, smul_eq_mul] using
      cell_face_induced_orientation (d.cells k) (d.positive k) i e t ⟨ht.1.le, ht.2.le⟩
  have hmul : T.re * w.im - T.im * w.re = a * (S.re * w.im - S.im * w.re) := by
    change T = a • S at htangent
    rw [htangent, Complex.smul_re, Complex.smul_im]
    simp only [smul_eq_mul]
    ring
  have hneg : S.re * w.im - S.im * w.re < 0 := by nlinarith
  have hother : 0 < S.re * (-w).im - S.im * (-w).re := by
    simp only [Complex.neg_re, Complex.neg_im]
    linarith
  obtain ⟨ε, hε, hεside⟩ := cell_face_transverse_sides (d.cells k) (d.injective k)
    (d.positive k) i e t ht w
    (by simpa only [T, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hleft)
  obtain ⟨δ, hδ, hδside⟩ := cell_face_transverse_sides (d.cells l) (d.injective l)
    (d.positive l) j f s hs (-w)
    (by simpa only [S, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hother)
  have hz : cellExtension (d.cells k) (faceInsertion i e (scalarLine t)) =
      cellExtension (d.cells l) (faceInsertion j f (scalarLine s)) := by
    rw [cellCurve_face_value (d.cells k) i e t ⟨ht.1.le, ht.2.le⟩,
      cellCurve_face_value (d.cells l) j f s ⟨hs.1.le, hs.2.le⟩] at hpoint
    exact complexCoordinates.symm.injective hpoint
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro r hr
  refine ⟨(hεside r ⟨hr.1, (lt_min_iff.mp hr.2).1⟩).1, ?_⟩
  have H := (hδside r ⟨hr.1, (lt_min_iff.mp hr.2).2⟩).1
  rw [← hz] at H
  simpa only [map_neg, smul_neg, sub_eq_add_neg] using H


/-- The geometric membership jump at a fixed point and tangent is unique. -/
theorem GeometricBoundaryJump.unique {K : Set ℂ} {z v : ℂ} {m n : ℤ}
    (hm : GeometricBoundaryJump K z v m) (hn : GeometricBoundaryJump K z v n) : m = n := by
  obtain ⟨ε, hε, hm⟩ := hm
  obtain ⟨δ, hδ, hn⟩ := hn
  obtain ⟨r, hr0, hr⟩ := exists_between (lt_min hε hδ)
  exact (hm r ⟨hr0, (lt_min_iff.mp hr).1⟩).symm.trans
    (hn r ⟨hr0, (lt_min_iff.mp hr).2⟩)

/-- A conditional assembly step from geometric side jumps. The original cycle
uses the full positive condition on the actual region. The additional face-jump
hypothesis is explicitly retained: it still needs to be derived from the cell
geometry before this becomes the source-facing dictionary. -/
theorem cell_dictionary_of_boundary_jumps {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (hfaces : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s)
        (chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (hq : ContinuousOn q (complexCoordinates ⁻¹' O)) :
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer := by
  apply cell_dictionary_of_face_incidence d Γ.chain (by rw [← hΓ.1]; exact subset_rfl) ?_ q hq
  intro j i e
  let c := cellFace (d.cells j) i e
  let V := scalarLine ⁻¹' extensionDomain c
  have hV : IsOpen V := (extension_spec c).1.preimage scalarLine.continuous
  have hsub : Icc (0 : ℝ) 1 ⊆ V := fun t ht =>
    (extension_spec c).2.1 ((scalarLine_mem_cube t).mpr ht)
  have hg : ContDiffOn ℝ 1 (cellCurve c) V :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      ((D04.Cells.extension_C1 c).comp scalarLine.contDiff.contDiffOn (fun _ ht => ht))
  have hreg := regular_cell_face (d.cells j) (d.injective j) (d.positive j) i e
  have H := hΓ.2 (cellCurve c) 0 1 V hV hsub hg hreg.1 hreg.2
  filter_upwards [H, hfaces j i e] with s hΓs hds
  exact (hΓs.unique hds).trans (cell_assembly_tangent_multiplicity d _ _)


/-- Every relative-interior face point is approached by actual interior cell
points. This is a statement about the whole cell image, derived from its
local inverse and induced inward direction. -/
theorem cell_face_mem_closure_interior {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    cellExtension c (faceInsertion i e (scalarLine t)) ∈
      closure (interior (cellExtension c '' cube 2)) := by
  let z := cellExtension c (faceInsertion i e (scalarLine t))
  let w := complexCoordinates (cellFaceInward c i e t)
  obtain ⟨ε, hε, hside⟩ := cell_face_inward_sides c hinj hpos i e t ht
  have hcont : Continuous (fun r : ℝ => z + r • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hlim : Tendsto (fun r : ℝ => z + r • w) (nhdsWithin 0 (Ioi 0)) (nhds z) := by
    simpa only [zero_smul, add_zero] using
      (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  exact (hside r hr).1

/-- A regular face point cannot lie in the interior of any other cell of the
supplied decomposition. This rules out an interior-cell contribution when
classifying the region's local boundary jump. -/
theorem PositiveCellData.face_not_mem_other_interior {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    cellExtension (d.cells k) (faceInsertion i e (scalarLine t)) ∉
      interior (cellExtension (d.cells l) '' cube 2) := by
  have hd := (d.cell_interiors_disjoint hkl).closure_left isOpen_interior
  exact Set.disjoint_left.mp hd
    (cell_face_mem_closure_interior (d.cells k) (d.injective k) (d.positive k) i e t ht)

lemma faceInsertion_unique (i j : Fin 2) (e f : Bool) (t s : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (_hs : s ∈ Icc (0 : ℝ) 1)
    (heq : faceInsertion i e (scalarLine t) = faceInsertion j f (scalarLine s)) :
    i = j ∧ e = f ∧ t = s := by
  have hij : i = j := by
    by_contra hne
    have hj : j = i.succAbove 0 := by fin_cases i <;> fin_cases j <;> simp_all
    have h := congrArg (fun x : E 2 => x j) heq
    rw [hj, D04.Cells.faceInsertion_other, scalarLine_apply] at h
    rw [← hj, D04.Cells.faceInsertion_same] at h
    cases f <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> linarith [ht.1, ht.2]
  subst j
  have hef : e = f := by
    have h := congrArg (fun x : E 2 => x i) heq
    simp only [D04.Cells.faceInsertion_same] at h
    cases e <;> cases f <;> simp_all
  subst f
  refine ⟨rfl, rfl, ?_⟩
  have h := congrArg (fun x : E 2 => x (i.succAbove 0)) heq
  simpa only [D04.Cells.faceInsertion_other, scalarLine_apply] using h

lemma cell_face_value_unique {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (i j : Fin 2) (e f : Bool) (t s : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (heq : cellCurve (cellFace c i e) t = cellCurve (cellFace c j f) s) :
    i = j ∧ e = f ∧ t = s := by
  rw [cellCurve_face_value c i e t ⟨ht.1.le, ht.2.le⟩,
    cellCurve_face_value c j f s hs] at heq
  exact faceInsertion_unique i j e f t s ht hs
    (hinj (faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ⟨ht.1.le, ht.2.le⟩))
      (faceInsertion_mem j f ((scalarLine_mem_cube s).mpr hs))
      (complexCoordinates.symm.injective heq))

lemma cell_face_transverse_sides_complex {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : ℂ)
    (hleft : 0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) * w.im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) * w.re) :
    let z := cellCurve (cellFace c i e) t
    let K := complexCoordinates.symm '' (cellExtension c '' cube 2)
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • w ∈ K ∧ z - r • w ∉ K := by
  dsimp only
  obtain ⟨ε, hε, hside⟩ := cell_face_transverse_sides c hinj hpos i e t ht w hleft
  refine ⟨ε, hε, ?_⟩
  intro r hr
  have h := hside r hr
  rw [cellCurve_face_value c i e t ⟨ht.1.le, ht.2.le⟩]
  constructor
  · refine ⟨_, interior_subset h.1, ?_⟩
    simp only [map_add, map_smul, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, heq⟩
    apply h.2
    have hyz := congrArg complexCoordinates heq
    simp only [LinearEquiv.apply_symm_apply, map_sub, map_smul] at hyz
    exact hyz ▸ hy

lemma cell_face_normal_jump {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    GeometricBoundaryJump (complexCoordinates.symm '' (cellExtension c '' cube 2))
      (cellCurve (cellFace c i e) t) (deriv (cellCurve (cellFace c i e)) t)
      (cellFaceSign i e) := by
  let v := deriv (cellCurve (cellFace c i e)) t
  have hv : v ≠ 0 := (regular_cell_face c hinj hpos i e).2 t ⟨ht.1.le, ht.2.le⟩
  have hnorm : 0 < v.re ^ 2 + v.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_pos.mpr hv
  have hsign : cellFaceSign i e = 1 ∨ cellFaceSign i e = -1 := by
    fin_cases i <;> cases e <;> norm_num [cellFaceSign]
  rcases hsign with hs | hs
  · obtain ⟨ε, hε, hside⟩ := cell_face_transverse_sides_complex c hinj hpos i e t ht
      (Complex.I * v) (by simpa [hs, Complex.mul_re, Complex.mul_im, v, pow_two] using hnorm)
    refine ⟨ε, hε, ?_⟩
    intro r hr
    obtain ⟨hin, hout⟩ := hside r hr
    rw [indicator_of_mem hin, indicator_of_notMem hout, hs]
    norm_num
  · obtain ⟨ε, hε, hside⟩ := cell_face_transverse_sides_complex c hinj hpos i e t ht
      (-(Complex.I * v)) (by simpa [hs, Complex.mul_re, Complex.mul_im, v, pow_two] using hnorm)
    refine ⟨ε, hε, ?_⟩
    intro r hr
    obtain ⟨hin, hout⟩ := hside r hr
    simp only [smul_neg, ← sub_eq_add_neg, sub_neg_eq_add] at hin hout
    rw [indicator_of_notMem hout, indicator_of_mem hin, hs]
    norm_num

lemma jump_of_eventually_same {K L : Set ℂ} {z v : ℂ} {m : ℤ}
    (h : GeometricBoundaryJump L z v m)
    (hlocal : ∀ᶠ y in nhds z, (y ∈ K ↔ y ∈ L)) :
    GeometricBoundaryJump K z v m := by
  have hp : ∀ᶠ r in nhds (0 : ℝ),
      (z + r • (Complex.I * v) ∈ K ↔ z + r • (Complex.I * v) ∈ L) := by
    have hc : Tendsto (fun r : ℝ => z + r • (Complex.I * v)) (nhds 0) (nhds z) := by
      have hcont : Continuous (fun r : ℝ => z + r • (Complex.I * v)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul, add_zero] using hcont.tendsto (0 : ℝ)
    exact hc hlocal
  have hm : ∀ᶠ r in nhds (0 : ℝ),
      (z - r • (Complex.I * v) ∈ K ↔ z - r • (Complex.I * v) ∈ L) := by
    have hc : Tendsto (fun r : ℝ => z - r • (Complex.I * v)) (nhds 0) (nhds z) := by
      have hcont : Continuous (fun r : ℝ => z - r • (Complex.I * v)) :=
        continuous_const.sub (continuous_id.smul continuous_const)
      simpa only [zero_smul, sub_zero] using hcont.tendsto (0 : ℝ)
    exact hc hlocal
  obtain ⟨δ, hδ, hsame⟩ := Metric.eventually_nhds_iff.mp (hp.and hm)
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro r hr
  have H := hsame (y := r)
    (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr.1] using (lt_min_iff.mp hr.2).2)
  have hind (y : ℂ) (heq : y ∈ K ↔ y ∈ L) :
      K.indicator (fun _ => (1 : ℤ)) y = L.indicator (fun _ => (1 : ℤ)) y := by
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy, indicator_of_mem (heq.mp hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (heq.mpr h))]
  rw [hind _ H.1, hind _ H.2]
  exact h r ⟨hr.1, (lt_min_iff.mp hr.2).1⟩

lemma cell_data_isolated_jump {O : Set (E 2)} (d : PositiveCellData O)
    (k : Fin d.count) (i : Fin 2) (e : Bool) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hisolated : ∀ l : Fin d.count, l ≠ k →
      cellCurve (cellFace (d.cells k) i e) t ∉
        complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)) :
    GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells k) i e) t)
      (deriv (cellCurve (cellFace (d.cells k) i e)) t) (cellFaceSign i e) := by
  let K : Fin d.count → Set ℂ := fun l =>
    complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)
  let R := ⋃ l : {l : Fin d.count // l ≠ k}, K l
  have hcomp (l : Fin d.count) : IsCompact (K l) :=
    ((D04.DiscontinuityCriterion.carrier_compact (cubeBox 2)).image_of_continuousOn
      ((D04.Cells.extension_C1 (d.cells l)).continuousOn.mono (extension_spec (d.cells l)).2.1)).image
        complexCoordinates.symm.toContinuousLinearEquiv.continuous
  have hR : IsClosed R := (isCompact_iUnion (fun l : {l : Fin d.count // l ≠ k} => hcomp l.val)).isClosed
  have hzR : cellCurve (cellFace (d.cells k) i e) t ∉ R := by
    intro hz
    obtain ⟨l, hl⟩ := mem_iUnion.mp hz
    exact hisolated l.val l.property hl
  apply jump_of_eventually_same
    (cell_face_normal_jump (d.cells k) (d.injective k) (d.positive k) i e t ht)
  filter_upwards [hR.isOpen_compl.mem_nhds hzR] with y hy
  change y ∉ R at hy
  constructor
  · intro hK
    obtain ⟨l, hl⟩ := mem_iUnion.mp hK
    by_cases hlk : l = k
    · exact hlk ▸ hl
    · exact False.elim (hy (mem_iUnion.mpr ⟨⟨l, hlk⟩, hl⟩))
  · intro hK
    exact mem_iUnion.mpr ⟨k, hK⟩

lemma cell_data_contact_transverse {O : Set (E 2)} (d : PositiveCellData O)
    (k l : Fin d.count) (hkl : k ≠ l) (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s))
    (w : ℂ)
    (hleft : 0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace (d.cells k) i e)) t).re) * w.im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace (d.cells k) i e)) t).im) * w.re) :
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      cellCurve (cellFace (d.cells k) i e) t + r • w ∈ d.carrier ∧
      cellCurve (cellFace (d.cells k) i e) t - r • w ∈ d.carrier := by
  let T := (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t
  let S := (cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s
  have ha := d.contact_orientation k l hkl i j e f t s a ht hs hpoint htangent
  have hT : 0 < T.re * w.im - T.im * w.re := by
    simpa only [T, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hleft
  have hmul : T.re * w.im - T.im * w.re = a * (S.re * w.im - S.im * w.re) := by
    change T = a • S at htangent
    rw [htangent, Complex.smul_re, Complex.smul_im]
    simp only [smul_eq_mul]
    ring
  have hneg : S.re * w.im - S.im * w.re < 0 := by nlinarith
  have hother : 0 < S.re * (-w).im - S.im * (-w).re := by
    simp only [Complex.neg_re, Complex.neg_im]
    linarith
  obtain ⟨ε, hε, hεside⟩ := cell_face_transverse_sides_complex (d.cells k) (d.injective k)
    (d.positive k) i e t ht w hleft
  obtain ⟨δ, hδ, hδside⟩ := cell_face_transverse_sides_complex (d.cells l) (d.injective l)
    (d.positive l) j f s hs (-w)
    (by simpa only [S, Complex.smul_re, Complex.smul_im, smul_eq_mul] using hother)
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro r hr
  constructor
  · exact mem_iUnion.mpr ⟨k, (hεside r ⟨hr.1, (lt_min_iff.mp hr.2).1⟩).1⟩
  · apply mem_iUnion.mpr
    refine ⟨l, ?_⟩
    have H := (hδside r ⟨hr.1, (lt_min_iff.mp hr.2).2⟩).1
    rw [← hpoint] at H
    simpa only [smul_neg, ← sub_eq_add_neg] using H

lemma cell_data_contact_jump {O : Set (E 2)} (d : PositiveCellData O)
    (k l : Fin d.count) (hkl : k ≠ l) (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s)) :
    GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells k) i e) t)
      (deriv (cellCurve (cellFace (d.cells k) i e)) t) 0 := by
  let v := deriv (cellCurve (cellFace (d.cells k) i e)) t
  have hv : v ≠ 0 := (regular_cell_face (d.cells k) (d.injective k) (d.positive k) i e).2
    t ⟨ht.1.le, ht.2.le⟩
  have hnorm : 0 < v.re ^ 2 + v.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_pos.mpr hv
  have hsign : cellFaceSign i e = 1 ∨ cellFaceSign i e = -1 := by
    fin_cases i <;> cases e <;> norm_num [cellFaceSign]
  rcases hsign with hc | hc
  · obtain ⟨ε, hε, hside⟩ := cell_data_contact_transverse d k l hkl i j e f t s a ht hs hpoint htangent
      (Complex.I * v) (by simpa [hc, Complex.mul_re, Complex.mul_im, v, pow_two] using hnorm)
    refine ⟨ε, hε, ?_⟩
    intro r hr
    obtain ⟨hin, hout⟩ := hside r hr
    rw [indicator_of_mem hin, indicator_of_mem hout]
    norm_num
  · obtain ⟨ε, hε, hside⟩ := cell_data_contact_transverse d k l hkl i j e f t s a ht hs hpoint htangent
      (-(Complex.I * v)) (by simpa [hc, Complex.mul_re, Complex.mul_im, v, pow_two] using hnorm)
    refine ⟨ε, hε, ?_⟩
    intro r hr
    obtain ⟨hin, hout⟩ := hside r hr
    simp only [smul_neg, ← sub_eq_add_neg, sub_neg_eq_add] at hin hout
    rw [indicator_of_mem hout, indicator_of_mem hin]
    norm_num



open Specs.D04.C06.JordanRegions.Model

/-- Restriction of fields to the actual path trace suffices without any regularity premise. -/
theorem path_integral_field_congr (η : PiecewiseC1Path) (q Q : ℂ → ℂ)
    (h : EqOn q Q η.trace) : η.integral q = η.integral Q := by
  change η.partition.integral q = η.partition.integral Q
  unfold C1Partition.integral
  apply Finset.sum_congr rfl
  intro i hi
  apply intervalIntegral.integral_congr
  intro t ht
  change q (η t) * _ = Q (η t) * _
  rw [h ⟨t, η.partition.piece_subset i (by
    change t ∈ Icc _ _
    simpa only [uIcc_of_le (η.partition.piece_lt i).le] using ht), rfl⟩]

/-- Restriction of fields to the active chain trace suffices. -/
theorem chain_integral_field_congr (Γ : IntegralChain) (q Q : ℂ → ℂ)
    (h : EqOn q Q Γ.trace) : Γ.integral q = Γ.integral Q := by
  apply Finset.sum_congr rfl
  intro η hη
  change (Γ η : ℂ) * η.integral q = (Γ η : ℂ) * η.integral Q
  rw [path_integral_field_congr η q Q (fun z hz => h ⟨η, hη, hz⟩)]

/-- Only points with nonzero actual ambient weight need field agreement. -/
theorem patch_integral_form_congr_weighted {k n} {O : Set (E n)}
    (P : Patch k O) (w : E n → ℝ) (omega Omega : FormField n k)
    (h : ∀ y ∈ P.map '' P.region, w y ≠ 0 → omega y = Omega y) :
    patchIntegral P w omega = patchIntegral P w Omega := by
  apply congrArg regionIntegral
  funext x
  change w (P.map x) * _ = w (P.map x) * _
  by_cases hw : w (P.map x) = 0
  · simp only [hw, zero_mul]
  · congr 1
    exact congrArg (fun W => W (fun j => fderiv ℝ P.map x (standardBasis k j)))
      (h _ (mem_image_of_mem _ x.property) hw)

/-- The same locality statement with all actual integer coefficients. -/
theorem patchChain_integral_form_congr_weighted {k n} {O : Set (E n)}
    (C : PatchChain k O) (omega Omega : FormField n k)
    (h : ∀ p ∈ C.support, ∀ y ∈ p.patch.map '' p.patch.region,
      p.weight y ≠ 0 → omega y = Omega y) :
    patchChainIntegral omega C = patchChainIntegral Omega C := by
  change C.sum _ = C.sum _
  apply Finset.sum_congr rfl
  intro p hp
  change (C p) • patchIntegral p.patch p.weight omega = (C p) • patchIntegral p.patch p.weight Omega
  rw [patch_integral_form_congr_weighted p.patch p.weight omega Omega (h p hp)]

/-- A C1 field near a compact carrier admits a global C1 extension agreeing
on an open neighborhood of that carrier, so first derivatives also agree there. -/
theorem complex_field_C1_extension (K : Set ℂ) (hK : IsCompact K)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hq : ContDiffOn ℝ 1 q U) :
    ∃ Q : ℂ → ℂ, ContDiff ℝ 1 Q ∧
      ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn Q q V := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  let L := complexCoordinates '' closure V
  let g : E 2 → E 2 := fun x => complexCoordinates (q (complexCoordinates.symm x))
  have hL : IsCompact L := hVc.image complexCoordinates.toContinuousLinearEquiv.continuous
  have hg : ContDiffOn ℝ 1 g (complexCoordinates.symm ⁻¹' U) :=
    complexCoordinates.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hq.comp complexCoordinates.symm.toContinuousLinearEquiv.contDiff.contDiffOn
        (fun _ hx => hx))
  obtain ⟨F, hF, hFg⟩ := D04.GeometricPatches.compact_local_extension L g hL (by
    intro x hx
    refine ⟨complexCoordinates.symm ⁻¹' U, g,
      hU.preimage complexCoordinates.symm.toContinuousLinearEquiv.continuous, ?_, hg, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := hx
      simpa only [mem_preimage, LinearEquiv.symm_apply_apply] using hVU hz
    · intro y hy
      rfl)
  refine ⟨fun z => complexCoordinates.symm (F (complexCoordinates z)),
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp
      (hF.comp complexCoordinates.toContinuousLinearEquiv.contDiff),
    V, hV, hKV, (fun _ hz => hVU (subset_closure hz)), ?_⟩
  intro z hz
  change complexCoordinates.symm (F (complexCoordinates z)) = q z
  rw [hFg (mem_image_of_mem complexCoordinates (subset_closure hz)),
    show g (complexCoordinates z) = complexCoordinates (q z) by
      simp only [g, LinearEquiv.symm_apply_apply], LinearEquiv.symm_apply_apply]

theorem cell_comparison_of_face_incidence_on_faces {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralChain)
    (hboundary : Γ.trace ⊆ frontier d.carrier)
    (hcount : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      chainTangentMultiplicity Γ (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s) =
      ∑ k, ∑ l : Fin 2, (-1 : ℤ) ^ l.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l true))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s) -
        tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l false))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (hq : ContinuousOn q d.faceCarrier) :
    Γ.integral q = d.faceContour.integral q := by
  let ι := Fin d.count × (Fin 2 × Bool)
  let c : ι → Cell 1 1 O := fun p => cellFace (d.cells p.1) p.2.1 p.2.2
  let g : ι → ℝ → ℂ := fun p => cellCurve (c p)
  let V : ι → Set ℝ := fun p => scalarLine ⁻¹' extensionDomain (c p)
  have hV (p : ι) : IsOpen (V p) :=
    (extension_spec (c p)).1.preimage scalarLine.continuous
  have hsub (p : ι) : Icc (0 : ℝ) 1 ⊆ V p := fun t ht =>
    (extension_spec (c p)).2.1 ((scalarLine_mem_cube t).mpr ht)
  have hg (p : ι) : ContDiffOn ℝ 1 (g p) (V p) :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      ((D04.Cells.extension_C1 (c p)).comp scalarLine.contDiff.contDiffOn (fun _ ht => ht))
  have hregular (p : ι) := regular_cell_face (d.cells p.1)
    (d.injective p.1) (d.positive p.1) p.2.1 p.2.2
  have htr : Γ.trace ∪ d.faceContour.trace ⊆ d.faceCarrier :=
    union_subset (hboundary.trans d.frontier_subset_faceCarrier) d.faceContour_trace_subset
  apply finite_regular_arc_comparison_fintype Γ d.faceContour g (fun _ => 0)
    (fun _ => 1) V hV hsub hg (fun p => (hregular p).1)
    (fun p => (hregular p).2) ∅ Set.countable_empty ?_ ?_ q
    (hq.mono htr)
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (htr hz)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hj
    obtain ⟨e, he⟩ := mem_iUnion.mp hi
    exact Or.inr (mem_iUnion.mpr ⟨⟨j, i, e⟩, he⟩)
  · intro p
    filter_upwards [hcount p.1 p.2.1 p.2.2] with s hs
    exact hs.trans (cell_assembly_tangent_multiplicity d _ _).symm


theorem PositiveCellData.faceCarrier_subset_carrier {O : Set (E 2)}
    (d : PositiveCellData O) : d.faceCarrier ⊆ d.carrier := by
  intro z hz
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hj
  obtain ⟨e, t, ht, rfl⟩ := mem_iUnion.mp hi
  refine mem_iUnion.mpr ⟨j, ?_⟩
  refine ⟨cellExtension (d.cells j) (faceInsertion i e (scalarLine t)),
    ⟨faceInsertion i e (scalarLine t), faceInsertion_mem i e
      ((scalarLine_mem_cube t).mpr ht), rfl⟩, ?_⟩
  exact (cellCurve_face_value (d.cells j) i e t ht).symm

/-- The literal supplied outer-patch formula for a field defined only near
its compact carrier, when the actual weighted outer support is contained there. -/
theorem cell_assembly_dictionary_near_carrier {O : Set (E 2)}
    (d : PositiveCellData O)
    (hsupport : ∀ p ∈ d.outer.support,
      ∀ y ∈ p.patch.map '' p.patch.region, p.weight y ≠ 0 →
        complexCoordinates.symm y ∈ d.carrier)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U) :
    d.faceContour.integral q =
      (patchChainIntegral (realForm q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm q) d.outer := by
  obtain ⟨Q, hQ, V, hV, hKV, hVU, hQq⟩ :=
    complex_field_C1_extension d.carrier d.carrier_compact q U hU hKU hq
  have hfield : EqOn q Q d.carrier := fun z hz => (hQq (hKV hz)).symm
  have htrace := d.faceContour_trace_subset.trans d.faceCarrier_subset_carrier
  rw [chain_integral_field_congr d.faceContour q Q (hfield.mono htrace),
    cell_assembly_dictionary d Q hQ.continuous.continuousOn]
  have hreal : patchChainIntegral (realForm q) d.outer =
      patchChainIntegral (realForm Q) d.outer := by
    apply patchChain_integral_form_congr_weighted
    intro p hp y hy hw
    unfold realForm Specs.D04.C12.GreenCirculationAndFlux.Model.circulationForm
    simp only
    rw [hfield (hsupport p hp y hy hw)]
  have himag : patchChainIntegral (imagForm q) d.outer =
      patchChainIntegral (imagForm Q) d.outer := by
    apply patchChain_integral_form_congr_weighted
    intro p hp y hy hw
    unfold imagForm Specs.D04.C12.GreenCirculationAndFlux.Model.circulationForm
    simp only
    rw [hfield (hsupport p hp y hy hw)]
  rw [hreal, himag]


theorem tangentSignedMultiplicity_eq_zero_of_not_mem_trace
    (η : PiecewiseC1Path) (z v : ℂ) (hz : z ∉ η.trace) :
    tangentSignedMultiplicity η z v = 0 := by
  classical
  unfold tangentSignedMultiplicity
  split_ifs with hf
  · apply Finset.sum_eq_zero
    intro t ht
    obtain ⟨htI, heq⟩ := hf.mem_toFinset.mp ht
    exact False.elim (hz ⟨t, htI, heq⟩)
  · rfl

theorem cell_face_multiplicity_other {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (i j : Fin 2) (e f : Bool) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hface : i ≠ j ∨ e ≠ f) (v : ℂ) :
    tangentSignedMultiplicity (cellPath (cellFace c j f))
      (cellCurve (cellFace c i e) t) v = 0 := by
  apply tangentSignedMultiplicity_eq_zero_of_not_mem_trace
  rintro ⟨s, hs, heq⟩
  have H := cell_face_value_unique c hinj i j e f t s ht hs heq.symm
  exact hface.elim (fun h => h H.1) (fun h => h H.2.1)

theorem PositiveCellData.face_avoids_endpoints_ae {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ∀ (l : Fin d.count) (j : Fin 2) (f : Bool),
        cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 0 ∧
        cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 1 := by
  let Z : Set ℂ := ⋃ l : Fin d.count, ⋃ j : Fin 2, ⋃ f : Bool,
    {cellCurve (cellFace (d.cells l) j f) 0, cellCurve (cellFace (d.cells l) j f) 1}
  have hZ : Z.Finite := Set.finite_iUnion (fun l => Set.finite_iUnion (fun j =>
    Set.finite_iUnion (fun f => Set.toFinite _)))
  filter_upwards [regular_curve_avoids_countable _ 0 1
    (regular_cell_face (d.cells k) (d.injective k) (d.positive k) i e).2 Z hZ.countable] with t ht
  intro l j f
  constructor
  · intro he
    apply ht
    exact mem_iUnion_of_mem l (mem_iUnion_of_mem j (mem_iUnion_of_mem f (by simp [he])))
  · intro he
    apply ht
    exact mem_iUnion_of_mem l (mem_iUnion_of_mem j (mem_iUnion_of_mem f (by simp [he])))

theorem face_parameter_interior_of_not_endpoints {O : Set (E 2)} (c : Cell 1 1 O)
    (z : ℂ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (heq : cellCurve c s = z)
    (hzero : z ≠ cellCurve c 0) (hone : z ≠ cellCurve c 1) :
    s ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · apply lt_of_le_of_ne hs.1
    intro h
    exact hzero (heq.symm.trans (congrArg (cellCurve c) h.symm))
  · apply lt_of_le_of_ne hs.2
    intro h
    exact hone (heq.symm.trans (congrArg (cellCurve c) h))

theorem cell_faces_multiplicity {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (v : ℂ) :
    (∑ j : Fin 2, ∑ f : Bool, cellFaceSign j f *
      tangentSignedMultiplicity (cellPath (cellFace c j f))
        (cellCurve (cellFace c i e) t) v) =
    cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace c i e))
      (cellCurve (cellFace c i e) t) v := by
  classical
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_eq_single e
    · intro f _ hfe
      rw [cell_face_multiplicity_other c hinj i i e f t ht (Or.inr hfe.symm)]
      exact mul_zero _
    · simp
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro f _
    rw [cell_face_multiplicity_other c hinj i j e f t ht (Or.inl hji.symm)]
    exact mul_zero _
  · simp

theorem cell_assembly_tangent_multiplicity_faces {O : Set (E 2)}
    (d : PositiveCellData O) (z v : ℂ) :
    chainTangentMultiplicity d.faceContour z v =
      ∑ k : Fin d.count, ∑ i : Fin 2, ∑ e : Bool,
        cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e)) z v := by
  rw [cell_assembly_tangent_multiplicity]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool, cellFaceSign, Bool.false_eq_true, ↓reduceIte,
    mul_one, mul_neg_one, neg_mul, mul_sub]
  ring

theorem PositiveCellData.multiplicity_of_single_contact {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (v : ℂ)
    (habsent : ∀ l : Fin d.count, l ≠ k → ∀ j : Fin 2, ∀ f : Bool,
      cellCurve (cellFace (d.cells k) i e) t ∉ (cellPath (cellFace (d.cells l) j f)).trace) :
    chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells k) i e) t) v =
      cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
        (cellCurve (cellFace (d.cells k) i e) t) v := by
  classical
  rw [cell_assembly_tangent_multiplicity_faces, Finset.sum_eq_single k]
  · exact cell_faces_multiplicity (d.cells k) (d.injective k) i e t ht v
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro f _
    rw [tangentSignedMultiplicity_eq_zero_of_not_mem_trace _ _ _ (habsent l hl j f)]
    exact mul_zero _
  · simp

theorem PositiveCellData.multiplicity_of_two_contacts {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s) (v : ℂ)
    (habsent : ∀ m : Fin d.count, m ≠ k → m ≠ l → ∀ q : Fin 2, ∀ h : Bool,
      cellCurve (cellFace (d.cells k) i e) t ∉ (cellPath (cellFace (d.cells m) q h)).trace) :
    chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells k) i e) t) v =
      cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
        (cellCurve (cellFace (d.cells k) i e) t) v +
      cellFaceSign j f * tangentSignedMultiplicity (cellPath (cellFace (d.cells l) j f))
        (cellCurve (cellFace (d.cells k) i e) t) v := by
  classical
  rw [cell_assembly_tangent_multiplicity_faces]
  let F : Fin d.count → ℤ := fun m => ∑ q : Fin 2, ∑ h : Bool,
    cellFaceSign q h * tangentSignedMultiplicity (cellPath (cellFace (d.cells m) q h))
      (cellCurve (cellFace (d.cells k) i e) t) v
  have hk : F k = cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
      (cellCurve (cellFace (d.cells k) i e) t) v :=
    cell_faces_multiplicity (d.cells k) (d.injective k) i e t ht v
  have hl : F l = cellFaceSign j f * tangentSignedMultiplicity (cellPath (cellFace (d.cells l) j f))
      (cellCurve (cellFace (d.cells k) i e) t) v := by
    dsimp [F]
    rw [hpoint]
    exact cell_faces_multiplicity (d.cells l) (d.injective l) j f s hs v
  change (∑ m, F m) = _
  rw [← hk, ← hl]
  have heq (m : Fin d.count) : F m = (if m = k then F k else 0) +
      (if m = l then F l else 0) := by
    by_cases hmk : m = k
    · subst m
      simp [hkl]
    by_cases hml : m = l
    · subst m
      simp [hkl.symm]
    have hz : F m = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      apply Finset.sum_eq_zero
      intro h _
      rw [tangentSignedMultiplicity_eq_zero_of_not_mem_trace _ _ _ (habsent m hmk hml q h)]
      exact mul_zero _
    simp [hmk, hml, hz]
  calc
    (∑ m, F m) = (∑ m, if m = k then F k else 0) + (∑ m, if m = l then F l else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => heq m)
    _ = F k + F l := by simp

theorem PositiveCellData.other_cell_contact_is_face {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hmem : cellCurve (cellFace (d.cells k) i e) t ∈
      complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)) :
    ∃ (j : Fin 2) (f : Bool) (s : ℝ), s ∈ Icc (0 : ℝ) 1 ∧
      cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s := by
  obtain ⟨y, hy, heq⟩ := hmem
  rw [cellCurve_face_value (d.cells k) i e t ⟨ht.1.le, ht.2.le⟩] at heq
  have hyz := complexCoordinates.symm.injective heq
  subst y
  have hfront : cellExtension (d.cells k) (faceInsertion i e (scalarLine t)) ∈
      frontier (cellExtension (d.cells l) '' cube 2) :=
    ⟨subset_closure hy, d.face_not_mem_other_interior k l hkl i e t ht⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (cell_image_frontier_subset_faces (d.cells l) (d.positive l) hfront)
  obtain ⟨f, u, hu, hpoint⟩ := mem_iUnion.mp hj
  refine ⟨j, f, u 0, hu 0, ?_⟩
  change cellCurve (cellFace (d.cells k) i e) t =
    complexCoordinates.symm (cellExtension (cellFace (d.cells l) j f) (scalarLine (u 0)))
  rw [scalarLine_coordinate, hpoint]
  exact cellCurve_face_value (d.cells k) i e t ⟨ht.1.le, ht.2.le⟩

theorem PositiveCellData.other_cell_contact_is_interior_face {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcorner : ∀ (j : Fin 2) (f : Bool),
      cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 0 ∧
      cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 1)
    (hmem : cellCurve (cellFace (d.cells k) i e) t ∈
      complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)) :
    ∃ (j : Fin 2) (f : Bool) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 ∧
      cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s := by
  obtain ⟨j, f, s, hs, heq⟩ := d.other_cell_contact_is_face k l hkl i e t ht hmem
  refine ⟨j, f, s, ?_, heq⟩
  exact face_parameter_interior_of_not_endpoints _ _ s hs heq.symm
    (hcorner j f).1 (hcorner j f).2

theorem cell_face_trace_subset_cell_image {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool) : (cellPath (cellFace c i e)).trace ⊆
      complexCoordinates.symm '' (cellExtension c '' cube 2) := by
  rintro z ⟨t, ht, rfl⟩
  refine ⟨cellExtension c (faceInsertion i e (scalarLine t)),
    ⟨faceInsertion i e (scalarLine t), faceInsertion_mem i e ((scalarLine_mem_cube t).mpr ht), rfl⟩, ?_⟩
  exact (cellCurve_face_value c i e t ht).symm

theorem PositiveCellData.face_boundary_jump_ae {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells k) i e) t)
        (deriv (cellCurve (cellFace (d.cells k) i e)) t)
        (chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells k) i e) t)
          (deriv (cellCurve (cellFace (d.cells k) i e)) t)) := by
  have Horient : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ∀ (l : Fin d.count) (j : Fin 2) (f : Bool), k ≠ l →
        t ∈ Ioo (0 : ℝ) 1 → ∀ s ∈ Ioo (0 : ℝ) 1,
          cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
          ∃ a : ℝ, a < 0 ∧
            (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
              a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s) := by
    apply ae_all_iff.mpr
    intro l
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro f
    by_cases hkl : k = l
    · exact Filter.Eventually.of_forall (by simp [hkl])
    · filter_upwards [d.contact_orientation_ae k l hkl i j e f] with t ht
      exact fun _ => ht
  have HI : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_of_ae (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
      ae_restrict_mem measurableSet_Icc] with t ht htI
    exact ht.mpr htI
  filter_upwards [d.face_avoids_endpoints_ae k i e,
    d.at_most_two_face_contacts_ae k i e, Horient, HI] with t hcorner htwo horient ht
  by_cases hcontact : ∃ l : Fin d.count, l ≠ k ∧
      cellCurve (cellFace (d.cells k) i e) t ∈
        complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)
  · obtain ⟨l, hlk, hl⟩ := hcontact
    obtain ⟨j, f, s, hs, hpoint⟩ := d.other_cell_contact_is_interior_face k l hlk.symm i e t ht
      (hcorner l) hl
    obtain ⟨a, ha, htangent⟩ := horient l j f hlk.symm ht s hs hpoint
    have habsent : ∀ m : Fin d.count, m ≠ k → m ≠ l → ∀ q : Fin 2, ∀ h : Bool,
        cellCurve (cellFace (d.cells k) i e) t ∉ (cellPath (cellFace (d.cells m) q h)).trace := by
      intro m hmk hml q h hm
      obtain ⟨u, hu, hupoint⟩ := hm
      have huI : u ∈ Ioo (0 : ℝ) 1 := face_parameter_interior_of_not_endpoints _ _ u hu hupoint
        (hcorner m q h).1 (hcorner m q h).2
      exact hml (htwo ht m l hmk.symm hlk.symm q j h f u s huI hs hupoint.symm hpoint)
    have hmult := d.multiplicity_of_two_contacts k l hlk.symm i j e f t s ht hs hpoint
      (deriv (cellCurve (cellFace (d.cells k) i e)) t) habsent
    rw [hmult, d.contact_cancellation k l hlk.symm i j e f t s a ht hs hpoint htangent]
    exact cell_data_contact_jump d k l hlk.symm i j e f t s a ht hs hpoint htangent
  · have hisolated : ∀ l : Fin d.count, l ≠ k →
        cellCurve (cellFace (d.cells k) i e) t ∉
          complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2) := by
      intro l hl hz
      exact hcontact ⟨l, hl, hz⟩
    have habsent : ∀ l : Fin d.count, l ≠ k → ∀ j : Fin 2, ∀ f : Bool,
        cellCurve (cellFace (d.cells k) i e) t ∉ (cellPath (cellFace (d.cells l) j f)).trace := by
      intro l hl j f hz
      exact hisolated l hl (cell_face_trace_subset_cell_image (d.cells l) j f hz)
    have hmult := d.multiplicity_of_single_contact k i e t ht
      (deriv (cellCurve (cellFace (d.cells k) i e)) t) habsent
    have hreg := (regular_cell_face (d.cells k) (d.injective k) (d.positive k) i e).2
      t ⟨ht.1.le, ht.2.le⟩
    have hone := tangent_signed_multiplicity_of_injective
      (cellPath (cellFace (d.cells k) i e))
      (regular_cell_face (d.cells k) (d.injective k) (d.positive k) i e).1
      t ⟨ht.1.le, ht.2.le⟩ (deriv (cellCurve (cellFace (d.cells k) i e)) t)
    change tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
      (cellCurve (cellFace (d.cells k) i e) t) (deriv (cellCurve (cellFace (d.cells k) i e)) t) =
      (if 0 < (deriv (cellCurve (cellFace (d.cells k) i e)) t /
          deriv (cellCurve (cellFace (d.cells k) i e)) t).re then 1
        else if (deriv (cellCurve (cellFace (d.cells k) i e)) t /
          deriv (cellCurve (cellFace (d.cells k) i e)) t).re < 0 then -1 else 0) at hone
    simp only [div_self hreg, Complex.one_re, zero_lt_one, ↓reduceIte] at hone
    rw [hmult, hone, mul_one]
    exact cell_data_isolated_jump d k i e t ht hisolated

/-- The original cycle and the actual alternating face contour have the same
integral. Signed incidence is derived from the region's side membership;
there is no comparison certificate among the geometric premises. Continuity
is needed only on the actual compact cell union. -/
theorem cell_boundary_comparison {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (hq : ContinuousOn q d.carrier) :
    Γ.integral q = d.faceContour.integral q := by
  apply cell_comparison_of_face_incidence_on_faces d Γ.chain
    (by rw [← hΓ.1]; exact subset_rfl) ?_ q
    (hq.mono d.faceCarrier_subset_carrier)
  intro j i e
  let c := cellFace (d.cells j) i e
  let V := scalarLine ⁻¹' extensionDomain c
  have hV : IsOpen V := (extension_spec c).1.preimage scalarLine.continuous
  have hsub : Icc (0 : ℝ) 1 ⊆ V := fun t ht =>
    (extension_spec c).2.1 ((scalarLine_mem_cube t).mpr ht)
  have hg : ContDiffOn ℝ 1 (cellCurve c) V :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      ((D04.Cells.extension_C1 c).comp scalarLine.contDiff.contDiffOn (fun _ ht => ht))
  have hreg := regular_cell_face (d.cells j) (d.injective j) (d.positive j) i e
  have H := hΓ.2 (cellCurve c) 0 1 V hV hsub hg hreg.1 hreg.2
  filter_upwards [H, d.face_boundary_jump_ae j i e] with s hΓs hds
  exact (hΓs.unique hds).trans (cell_assembly_tangent_multiplicity d _ _)

/-- The boundary dictionary for the original cycle, with exactly the common
ambient field domain used by the actual D04 real patch-chain assembly. -/
theorem cell_boundary_dictionary {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (hq : ContinuousOn q (complexCoordinates ⁻¹' O)) :
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer := by
  exact cell_dictionary_of_boundary_jumps d Γ hΓ d.face_boundary_jump_ae q hq

/-- The literal near-carrier formula when the supplied outer display also
has its actual nonzero weighted support in that carrier. This support premise
is explicit and is not asserted for arbitrary D04 geometric equivalences. -/
theorem cell_boundary_dictionary_near_carrier {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (hsupport : ∀ p ∈ d.outer.support,
      ∀ y ∈ p.patch.map '' p.patch.region, p.weight y ≠ 0 →
        complexCoordinates.symm y ∈ d.carrier)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U) :
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer := by
  rw [cell_boundary_comparison d Γ hΓ q (hq.continuousOn.mono hKU)]
  exact cell_assembly_dictionary_near_carrier d hsupport q U hU hKU hq

/-- A field C1 near the compact union can always be evaluated on the actual
D04 display after a constructed global C1 extension. Agreement holds on an
open neighborhood of the carrier, and the original integral is unchanged. -/
theorem cell_boundary_dictionary_extension {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U) :
    ∃ (Q : ℂ → ℂ) (V : Set ℂ), ContDiff ℝ 1 Q ∧ IsOpen V ∧
      d.carrier ⊆ V ∧ V ⊆ U ∧ EqOn Q q V ∧
      Γ.integral q = (patchChainIntegral (realForm Q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm Q) d.outer := by
  obtain ⟨Q, hQ, V, hV, hKV, hVU, hQq⟩ :=
    complex_field_C1_extension d.carrier d.carrier_compact q U hU hKU hq
  refine ⟨Q, V, hQ, hV, hKV, hVU, hQq, ?_⟩
  have htrace : Γ.chain.trace ⊆ d.carrier := by
    rw [show Γ.chain.trace = frontier d.carrier from hΓ.1]
    exact d.frontier_subset_faceCarrier.trans d.faceCarrier_subset_carrier
  change Γ.chain.integral q = _
  rw [chain_integral_field_congr Γ.chain q Q (fun z hz => (hQq (hKV (htrace hz))).symm)]
  exact cell_boundary_dictionary d Γ hΓ Q hQ.continuous.continuousOn

/-- The actual D04 boundary value of a continuous ambient field depends
only on its restriction to the cell union. In particular the extension
constructed in `cell_boundary_dictionary_extension` gives a unique value. -/
theorem cell_boundary_extension_independent {O : Set (E 2)}
    (d : PositiveCellData O) (q Q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates ⁻¹' O))
    (hQ : ContinuousOn Q (complexCoordinates ⁻¹' O))
    (heq : EqOn q Q d.carrier) :
    (patchChainIntegral (realForm q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm q) d.outer =
      (patchChainIntegral (realForm Q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm Q) d.outer := by
  rw [← cell_assembly_dictionary d q hq, ← cell_assembly_dictionary d Q hQ]
  exact chain_integral_field_congr d.faceContour q Q
    (heq.mono (d.faceContour_trace_subset.trans d.faceCarrier_subset_carrier))

/-- The real outer value is independent of the ambient extension. Agreement
on the carrier suffices, so in particular agreement near the carrier suffices.
The extensions need only be continuous on the supplied ambient set. -/
theorem cell_boundary_extension_real_independent {O : Set (E 2)}
    (d : PositiveCellData O) (q Q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates ⁻¹' O))
    (hQ : ContinuousOn Q (complexCoordinates ⁻¹' O))
    (heq : EqOn q Q d.carrier) :
    patchChainIntegral (realForm q) d.outer =
      patchChainIntegral (realForm Q) d.outer := by
  have h := congrArg Complex.re (cell_boundary_extension_independent d q Q hq hQ heq)
  simpa using h

/-- The imaginary outer value is separately independent of the ambient
extension, also for extensions C1 only on the supplied ambient set. -/
theorem cell_boundary_extension_imag_independent {O : Set (E 2)}
    (d : PositiveCellData O) (q Q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates ⁻¹' O))
    (hQ : ContinuousOn Q (complexCoordinates ⁻¹' O))
    (heq : EqOn q Q d.carrier) :
    patchChainIntegral (imagForm q) d.outer =
      patchChainIntegral (imagForm Q) d.outer := by
  have h := congrArg Complex.im (cell_boundary_extension_independent d q Q hq hQ heq)
  simpa using h

/-- Agreement on an open neighborhood preserves the full first real
differential, including all coordinate partial derivatives used in Green. -/
theorem field_fderiv_eqOn_open (Q q : ℂ → ℂ) (V : Set ℂ)
    (hV : IsOpen V) (heq : EqOn Q q V) :
    EqOn (fderiv ℝ Q) (fderiv ℝ q) V := by
  intro z hz
  exact (heq.eventuallyEq_of_mem (hV.mem_nhds hz)).fderiv_eq

/-- The carrier-local dictionary, including agreement of first real
derivatives on the same neighborhood and the separate real outer values.
No support restriction on the supplied outer display is needed. -/
theorem cell_boundary_dictionary_extension_with_derivatives {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U) :
    ∃ (Q : ℂ → ℂ) (V : Set ℂ), ContDiff ℝ 1 Q ∧ IsOpen V ∧
      d.carrier ⊆ V ∧ V ⊆ U ∧ EqOn Q q V ∧
      EqOn (fderiv ℝ Q) (fderiv ℝ q) V ∧
      Γ.integral q = (patchChainIntegral (realForm Q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm Q) d.outer ∧
      (Γ.integral q).re = patchChainIntegral (realForm Q) d.outer ∧
      (Γ.integral q).im = patchChainIntegral (imagForm Q) d.outer := by
  obtain ⟨Q, V, hQ, hV, hKV, hVU, hQq, hdict⟩ :=
    cell_boundary_dictionary_extension d Γ hΓ q U hU hKU hq
  refine ⟨Q, V, hQ, hV, hKV, hVU, hQq,
    field_fderiv_eqOn_open Q q V hV hQq, hdict, ?_, ?_⟩
  · simpa using congrArg Complex.re hdict
  · simpa using congrArg Complex.im hdict

end D12Complex.CellBoundaryContour
