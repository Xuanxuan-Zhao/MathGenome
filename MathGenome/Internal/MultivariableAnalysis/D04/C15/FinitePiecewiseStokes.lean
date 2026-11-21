import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FinitePiecewiseStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C15.LowerDimensionalImagesHaveZeroContent
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FiniteManifoldBoundaryAssembly
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FiniteGeometricUnionIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped ContDiff BigOperators Classical
namespace D04.FinitePiecewiseStokes
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.PullbackCalculus.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.FinitePiecewiseStokes
open Model

theorem manifold_summands : manifold_summandsType := by
  intro k n N M o hc a V omega hMV homega
  have hs (j : Fin N) := D04Stokes.ambient_stokes_compact (o j) (hc j)
    V omega (hMV j) homega
  choose bO hb I hI hJ using hs
  exact ⟨bO, I, I, fun j => ⟨hb j, hI j, hJ j⟩, rfl⟩

theorem multiplicity_one_off_seams : multiplicity_one_off_seamsType := by
  intro n N pieces seams h x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    have hn : x ∉ pieces j := fun hmem => hx.2 (h j i hji ⟨hmem, hi⟩)
    simp [hn]
  · simp

theorem finite_seam_invariance : finite_seam_invarianceType := by
  intro k m hk d K f hd hK hf Q a b ha hb heq
  have hz := (LowerDimensionalImages.finite_C1_images d K f hd hK hf).2
  obtain ⟨hi, hv⟩ := LowerDimensionalImages.coefficient_integral_unchanged
    hk _ hz Q a b ha hb heq
  exact ⟨hi, hv⟩

/-- Continuity only requires regularity near the actual cell image; the
ambient form domain need not coincide with the cell's declared target. -/
theorem coefficient_continuous_near_image {k n : ℕ} {O V : Set (E n)}
    (c : Cell 1 k O) (omega : FormField n k)
    (homega : IsCrForm (some 0) V omega)
    (hmap : ∀ x : cube k, (c.toFun x).val ∈ V) :
    ContinuousOn (cellCoefficient c omega) (cube k) := by
  apply Cells.C1.pullback_evaluation_continuousOn omega homega (standardBasis k)
  · exact (Cells.extension_C1 c).continuousOn.mono (extension_spec c).2.1
  · exact ((Cells.extension_C1 c).continuousOn_fderiv_of_isOpen
      (extension_spec c).1 le_rfl).mono (extension_spec c).2.1
  · intro x hx
    change Cells.cellExtension c x ∈ V
    rw [Cells.extension_on_cube c ⟨x, hx⟩]
    exact hmap ⟨x, hx⟩

/-- The coefficient transforms by the signed determinant, also on the closed
faces of the parameter cube. Extension uniqueness handles its corners. -/
theorem reparametrized_coefficient {k n : ℕ} {O : Set (E n)}
    (c d : Cell 1 k O) (s : ℤ) (R : CubeReparametrization c d s)
    (omega : FormField n k) (x : cube k) :
    cellCoefficient c omega x = cellCoefficient d omega (R.change x) *
      (fderiv ℝ R.change x).det := by
  have hm : MapsTo R.change (cube k) (cube k) := by
    intro u hu
    rw [← R.image]
    exact mem_image_of_mem R.change hu
  let W := R.change.source ∩ R.change ⁻¹' extensionDomain d
  have hW : IsOpen W := R.change.isOpen_inter_preimage (extension_spec d).1
  have hsub : cube k ⊆ W := fun u hu =>
    ⟨R.domain hu, (extension_spec d).2.1 (hm hu)⟩
  have hreg : ContDiffOn ℝ 1 (cellExtension d ∘ R.change) W :=
    (Cells.extension_C1 d).comp (R.regular.mono inter_subset_left) (fun _ hu => hu.2)
  have heq (u : cube k) : (cellExtension d ∘ R.change) u = (c.toFun u).val := by
    exact (Cells.extension_on_cube d ⟨R.change u, hm u.property⟩).trans (R.agrees u).symm
  have heC : cellCoefficient c omega x =
      pullback (cellExtension d ∘ R.change) omega x (standardBasis k) :=
    Cells.cellCoefficient_extension_independent c (cellExtension d ∘ R.change)
      W hW hsub hreg heq omega x
  rw [heC]
  have hdf : DifferentiableAt ℝ (cellExtension d) (R.change x) :=
    ((Cells.extension_C1 d).differentiableOn (by norm_num)).differentiableAt
      ((extension_spec d).1.mem_nhds ((extension_spec d).2.1 (hm x.property)))
  have hde : DifferentiableAt ℝ R.change x :=
    (R.regular.differentiableOn (by norm_num)).differentiableAt
      (R.change.open_source.mem_nhds (R.domain x.property))
  have hp : pullback (cellExtension d ∘ R.change) omega x =
      pullback R.change (pullback (cellExtension d) omega) x := by
    ext v
    change omega ((cellExtension d ∘ R.change) x)
      (fun j => fderiv ℝ (cellExtension d ∘ R.change) x (v j)) = _
    rw [fderiv_comp (x : E k) hdf hde]
    rfl
  rw [hp]
  have ht : pullback (cellExtension d) omega =
      fun y => cellCoefficient d omega y • volumeForm k :=
    funext (Cells.cell_pullback_top d omega)
  rw [ht]
  exact Orientation.pullback_coefficient _ _ _

/-- Directed change of parameters for a complete closed cube. Unlike the
compact-supported open-domain formula, coefficients may be nonzero at its
boundary. The region substitution theorem supplies precisely that case. -/
theorem cell_reparametrization : cell_reparametrizationType := by
  intro k n O c d s hR V omega homega hmap
  obtain ⟨R⟩ := hR
  have hm : MapsTo R.change (cube k) (cube k) := by
    intro u hu
    rw [← R.image]
    exact mem_image_of_mem R.change hu
  have hcc := coefficient_continuous_near_image c omega homega
    (fun x => by rw [R.agrees x]; exact hmap ⟨R.change x, hm x.property⟩)
  have hcd := coefficient_continuous_near_image d omega homega hmap
  have hdi := D04Stokes.regionIntegrable_box (cubeBox k) (cellCoefficient d omega) hcd
  have hdi' : JordanRegions.RegionIntegrable
      (fun y : R.change '' cube k => cellCoefficient d omega y) := by
    change Specs.D04.C06.JordanRegions.Model.RegionIntegrable
      (S := R.change '' cube k) (fun y => cellCoefficient d omega y)
    rw [R.image]
    exact hdi
  have hc : IsCompact (cube k) := DiscontinuityCriterion.carrier_compact (cubeBox k)
  have hK : IsCompact (closure (cube k)) := hc.closure
  have hdom : closure (cube k) ⊆ R.change.source := by
    rw [hc.isClosed.closure_eq]
    exact R.domain
  have hs : (s : ℝ) = 1 ∨ (s : ℝ) = -1 := by
    rcases R.unit_sign with h | h <;> simp [h]
  have hsub := Orientation.signed_region_substitution R.change R.regular R.inverse_regular
    (cube k) (OneCoordinate.Boxes.jordan_carrier (cubeBox k)) hK hdom (s : ℝ) hs
    R.sign (fun y : R.change '' cube k => cellCoefficient d omega y) hdi'.1
  have hv := hsub.2.2 (Or.inl hdi')
  have heq : (fun x : cube k => pullback R.change
      (fun y => JordanRegions.zeroExtension
        (fun y : R.change '' cube k => cellCoefficient d omega y) y • volumeForm k)
        x (standardBasis k)) = (fun x : cube k => cellCoefficient c omega x) := by
    funext x
    rw [Orientation.pullback_coefficient,
      JordanRegions.zeroExtension_apply _ ⟨R.change x, mem_image_of_mem R.change x.property⟩]
    exact (reparametrized_coefficient c d s R omega x).symm
  have hv' : JordanRegions.regionIntegral (fun x : cube k => cellCoefficient c omega x) =
      (s : ℝ) * JordanRegions.regionIntegral
        (fun y : R.change '' cube k => cellCoefficient d omega y) :=
    (congrArg (fun F : cube k → ℝ => JordanRegions.regionIntegral F) heq).symm.trans hv
  change Specs.D04.C06.JordanRegions.Model.regionIntegral _ =
    (s : ℝ) * Specs.D04.C06.JordanRegions.Model.regionIntegral _ at hv'
  rw [R.image] at hv'
  change Darboux.lowerIntegral (cellCoefficient c omega) (cubeBox k) =
    (s : ℝ) * Darboux.lowerIntegral (cellCoefficient d omega) (cubeBox k)
  rw [D04Stokes.box_integral_eq_region (cubeBox k) (fun i => by norm_num [cubeBox]) _ hcc,
    D04Stokes.box_integral_eq_region (cubeBox k) (fun i => by norm_num [cubeBox]) _ hcd]
  exact hv'

/-- Integer multiplicities are carried through each cancellation. No rank or
injectivity of the original cells is used in this chain identity. -/
theorem cell_piecewise_stokes : cell_piecewise_stokesType := by
  intro k n N P O c a outer left right b s hR hboundary V omega homega hmap hright
  have hzero : IsCrForm (some 0) V omega := by
    exact ⟨homega.1, fun I =>
      ((crOn_iff_contDiffOn 1 V _ homega.1).mp (homega.2 I)).continuousOn⟩
  have hp (i : Fin P) : chainIntegral omega
      (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) = 0 := by
    rw [map_sub, map_zsmul, Cells.chainIntegral_single, Cells.chainIntegral_single]
    simp only [zsmul_eq_mul, Int.cast_one, one_mul]
    exact sub_eq_zero.mpr (cell_reparametrization (left i) (right i) (s i) (hR i)
      V omega hzero (hright i))
  calc
    _ = ∑ j, (a j : ℝ) * chainIntegral omega (cellBoundary (c j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Cells.cell_stokes_c1 (c j) V omega homega (hmap j)]
    _ = chainIntegral omega (∑ j, a j • cellBoundary (c j)) := by
      simp only [map_sum, map_zsmul, zsmul_eq_mul]
    _ = chainIntegral omega outer := by
      rw [hboundary, map_add, map_sum]
      simp only [map_zsmul, hp, zsmul_zero, Finset.sum_const_zero, add_zero]

/-- This cancellation uses the geometric orientation field and the actual
manifold integral. It also treats isolated signed boundary points. -/
theorem manifold_opposite_cancel : manifold_opposite_cancelType := by
  intro r k n M o p hp eta I J hi hj
  have hv : J = -I := by
    cases k with
    | zero =>
      have he : (fun x : M => (p x).val * eta x (fun j => Fin.elim0 j)) =
          (fun x : M => -((o x).val * eta x (fun j => Fin.elim0 j))) := by
        funext x
        rw [hp x, neg_mul]
      have hval : Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.zeroIntegral p
          (fun x => eta x (fun j => Fin.elim0 j)) =
          -Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.zeroIntegral o
          (fun x => eta x (fun j => Fin.elim0 j)) := by
        unfold Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.zeroIntegral
        rw [he, finsum_neg_distrib]
      exact hj.2.2.2.symm.trans (hval.trans (congrArg Neg.neg hi.2.2.2))
    | succ k =>
      obtain ⟨P⟩ := hi.2.2.1
      obtain ⟨Q⟩ := hj.2.2.1
      exact ((hj.2.2.2 Q).2).symm.trans
        ((ManifoldIntegralIndependence.oriented_reverse_comparison o p hp eta hi.1 P Q).trans
          (congrArg Neg.neg (hi.2.2.2 P).2))
  rw [hv, add_neg_cancel]

/-- Use a single enclosing rectangle for all zero extensions. Outside the
seams their sum equals the coefficient on the union. The finite-content-zero
exception theorem supplies both integrability and equality of the integrals. -/
theorem integral_union_off_seams : integral_union_off_seamsType := by
  intro k N hk pieces seams hz hpieces hover f hf
  let U := ⋃ i, pieces i
  have hU : JordanRegions.Jordan U := by
    simpa only [Finset.mem_univ, iUnion_true] using
      JordanRegions.jordan_finite_union Finset.univ pieces (fun i _ => hpieces i)
  let Q := JordanRegions.enclosingBox U
  have hQ : JordanRegions.Encloses U Q :=
    JordanRegions.enclosingBox_encloses (JordanRegions.jordan_bounded hU)
  have hiQ (i : Fin N) : JordanRegions.Encloses (pieces i) Q :=
    (closure_mono (subset_iUnion pieces i)).trans hQ
  let F (i : Fin N) : E k → ℝ :=
    JordanRegions.zeroExtension (fun x : pieces i => f x)
  have hFi (i : Fin N) : Darboux.Integrable (F i) Q :=
    (JordanRegions.region_integrable_iff_box _ (hiQ i)).mp (hf i)
  have hsum : Darboux.Integrable (fun x => ∑ i, F i x) Q :=
    Darboux.integrable_sum Finset.univ F (fun i _ => hFi i)
  choose C hC using fun i => (hf i).1
  have hb : JordanRegions.RegionBounded (fun x : U => f x) := by
    refine ⟨∑ i, |C i|, ?_⟩
    intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp x.property
    exact (hC i ⟨x, hxi⟩).trans ((le_abs_self (C i)).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)))
  have heq : ∀ x ∈ Darboux.carrier Q, x ∉ seams →
      (∑ i, F i x) = JordanRegions.zeroExtension (fun x : U => f x) x := by
    intro x hx hxs
    by_cases hxu : x ∈ U
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxu
      rw [Finset.sum_eq_single i]
      · exact (JordanRegions.zeroExtension_apply (fun x : pieces i => f x) ⟨x, hxi⟩).trans
          (JordanRegions.zeroExtension_apply (fun x : U => f x) ⟨x, hxu⟩).symm
      · intro j hj hji
        have hxj : x ∉ pieces j := fun h => hxs (hover j i hji ⟨h, hxi⟩)
        exact JordanRegions.zeroExtension_of_not_mem _ hxj
      · simp
    · rw [JordanRegions.zeroExtension_of_not_mem _ hxu]
      apply Finset.sum_eq_zero
      intro i hi
      exact JordanRegions.zeroExtension_of_not_mem _
        (fun h => hxu (mem_iUnion.mpr ⟨i, h⟩))
  obtain ⟨hi, hv⟩ := LowerDimensionalImages.coefficient_integral_unchanged
    hk seams hz Q _ _ hsum (JordanRegions.zeroExtension_bounded _ hb Q) heq
  have hfu := (JordanRegions.region_integrable_iff_box _ hQ).mpr hi
  refine ⟨hfu, ?_⟩
  change JordanRegions.regionIntegral (fun x : U => f x) =
    ∑ i, JordanRegions.regionIntegral (fun x : pieces i => f x)
  rw [JordanRegions.integral_eq_on_enclosing_box _ hfu hQ hi]
  calc
    _ = Darboux.integral (fun x => ∑ i, F i x) Q hsum := hv
    _ = ∑ i, Darboux.integral (F i) Q (hFi i) := by
      simpa only [Finset.mem_univ, ↓reduceDIte] using
        Darboux.integral_sum Finset.univ F (fun i _ => hFi i) hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (JordanRegions.integral_eq_on_enclosing_box _ (hf i) (hiQ i) (hFi i)).symm

/-- First derivatives on the closed cube agree with those of the composed
extension. This includes boundary points of both parameter subregions. -/
theorem parameter_piece_coefficient {k n : ℕ} {O : Set (E n)}
    (c d : Cell 1 k O) (s : ℤ) (R : CubeParameterPiece c d s)
    (omega : FormField n k) (x : cube k) :
    cellCoefficient d omega x = cellCoefficient c omega (R.change x) *
      (fderiv ℝ R.change x).det := by
  have hm : MapsTo R.change (cube k) (cube k) := fun u hu =>
    R.range_subset (mem_image_of_mem R.change hu)
  let W := R.change.source ∩ R.change ⁻¹' extensionDomain c
  have hW : IsOpen W := R.change.isOpen_inter_preimage (extension_spec c).1
  have hsub : cube k ⊆ W := fun u hu =>
    ⟨R.domain hu, (extension_spec c).2.1 (hm hu)⟩
  have hreg : ContDiffOn ℝ 1 (cellExtension c ∘ R.change) W :=
    (Cells.extension_C1 c).comp (R.regular.mono inter_subset_left) (fun _ hu => hu.2)
  have heq (u : cube k) : (cellExtension c ∘ R.change) u = (d.toFun u).val :=
    (R.agrees u).symm
  have heC : cellCoefficient d omega x =
      pullback (cellExtension c ∘ R.change) omega x (standardBasis k) :=
    Cells.cellCoefficient_extension_independent d (cellExtension c ∘ R.change)
      W hW hsub hreg heq omega x
  rw [heC]
  have hdf : DifferentiableAt ℝ (cellExtension c) (R.change x) :=
    ((Cells.extension_C1 c).differentiableOn (by norm_num)).differentiableAt
      ((extension_spec c).1.mem_nhds ((extension_spec c).2.1 (hm x.property)))
  have hde : DifferentiableAt ℝ R.change x :=
    (R.regular.differentiableOn (by norm_num)).differentiableAt
      (R.change.open_source.mem_nhds (R.domain x.property))
  have hp : pullback (cellExtension c ∘ R.change) omega x =
      pullback R.change (pullback (cellExtension c) omega) x := by
    ext v
    change omega ((cellExtension c ∘ R.change) x)
      (fun j => fderiv ℝ (cellExtension c ∘ R.change) x (v j)) = _
    rw [fderiv_comp (x : E k) hdf hde]
    rfl
  rw [hp]
  have ht : pullback (cellExtension c) omega =
      fun y => cellCoefficient c omega y • volumeForm k :=
    funext (Cells.cell_pullback_top c omega)
  rw [ht]
  exact Orientation.pullback_coefficient _ _ _

theorem cell_parameter_piece : cell_parameter_pieceType := by
  intro k n O c d s R V omega homega hmap
  have hm : MapsTo R.change (cube k) (cube k) := fun u hu =>
    R.range_subset (mem_image_of_mem R.change hu)
  have hcc := coefficient_continuous_near_image c omega homega hmap
  have hcd := coefficient_continuous_near_image d omega homega (fun x => by
    have he : (d.toFun x).val = (c.toFun ⟨R.change x, hm x.property⟩).val :=
      (R.agrees x).trans (Cells.extension_on_cube c ⟨R.change x, hm x.property⟩)
    exact he.symm ▸ hmap ⟨R.change x, hm x.property⟩)
  have hci := D04Stokes.regionIntegrable_box (cubeBox k) (cellCoefficient c omega) hcc
  have hdi := D04Stokes.regionIntegrable_box (cubeBox k) (cellCoefficient d omega) hcd
  have hc : IsCompact (cube k) := DiscontinuityCriterion.carrier_compact (cubeBox k)
  have hK : IsCompact (closure (cube k)) := hc.closure
  have hdom : closure (cube k) ⊆ R.change.source := by
    rw [hc.isClosed.closure_eq]
    exact R.domain
  have hs : (s : ℝ) = 1 ∨ (s : ℝ) = -1 := by
    rcases R.unit_sign with h | h <;> simp [h]
  have hb : JordanRegions.RegionBounded
      (fun y : R.change '' cube k => cellCoefficient c omega y) := by
    obtain ⟨B, hB⟩ := hci.1
    exact ⟨B, fun y => hB ⟨y, R.range_subset y.property⟩⟩
  have hsub := Orientation.signed_region_substitution R.change R.regular R.inverse_regular
    (cube k) (OneCoordinate.Boxes.jordan_carrier (cubeBox k)) hK hdom (s : ℝ) hs
    R.sign (fun y : R.change '' cube k => cellCoefficient c omega y) hb
  have heq : (fun x : cube k => pullback R.change
      (fun y => JordanRegions.zeroExtension
        (fun y : R.change '' cube k => cellCoefficient c omega y) y • volumeForm k)
        x (standardBasis k)) = (fun x : cube k => cellCoefficient d omega x) := by
    funext x
    rw [Orientation.pullback_coefficient,
      JordanRegions.zeroExtension_apply _ ⟨R.change x, mem_image_of_mem R.change x.property⟩]
    exact (parameter_piece_coefficient c d s R omega x).symm
  let F : R.change '' cube k → ℝ := fun y => cellCoefficient c omega y
  let G : cube k → ℝ := fun x => pullback R.change
    (fun y => JordanRegions.zeroExtension F y • volumeForm k) x (standardBasis k)
  have hsub' : JordanRegions.RegionBounded G ∧
      (JordanRegions.RegionIntegrable F ↔ JordanRegions.RegionIntegrable G) ∧
      ((JordanRegions.RegionIntegrable F ∨ JordanRegions.RegionIntegrable G) →
        JordanRegions.regionIntegral G = (s : ℝ) * JordanRegions.regionIntegral F) := hsub
  have heq' : G = fun x : cube k => cellCoefficient d omega x := heq
  rw [heq'] at hsub'
  refine ⟨hsub'.2.1.mpr hdi, ?_⟩
  change Darboux.lowerIntegral (cellCoefficient d omega) (cubeBox k) = _
  rw [D04Stokes.box_integral_eq_region (cubeBox k) (fun i => by norm_num [cubeBox]) _ hcd]
  exact hsub'.2.2 (Or.inr hdi)

theorem cell_subdivision : cell_subdivisionType := by
  intro k n N hk O c d s R seams hz hcover hover V omega homega hmap
  have hc : IsCompact (cube k) := DiscontinuityCriterion.carrier_compact (cubeBox k)
  have hdom (i : Fin N) : closure (cube k) ⊆ (R i).change.source := by
    rw [hc.isClosed.closure_eq]
    exact (R i).domain
  have hj (i : Fin N) : JordanRegions.Jordan ((R i).change '' cube k) :=
    (RegionSubstitution.jordan_image (R i).change (R i).regular (R i).inverse_regular
      (cube k) (OneCoordinate.Boxes.jordan_carrier (cubeBox k)) hc.closure (hdom i)).2
  have hp (i : Fin N) := cell_parameter_piece c (d i) (s i) (R i) V omega homega hmap
  have hu := integral_union_off_seams hk (fun i => (R i).change '' cube k)
    seams hz hj hover (cellCoefficient c omega) (fun i => (hp i).1)
  have hsum : JordanRegions.regionIntegral (fun x : cube k => cellCoefficient c omega x) =
      ∑ i, JordanRegions.regionIntegral
        (fun x : (R i).change '' cube k => cellCoefficient c omega x) := by
    have hv := hu.2
    change Specs.D04.C06.JordanRegions.Model.regionIntegral _ = _ at hv
    rw [hcover] at hv
    exact hv
  have hcc := coefficient_continuous_near_image c omega homega hmap
  have hbox : cellIntegral c omega =
      JordanRegions.regionIntegral (fun x : cube k => cellCoefficient c omega x) :=
    D04Stokes.box_integral_eq_region (cubeBox k) (fun i => by norm_num [cubeBox]) _ hcc
  apply hbox.trans (hsum.trans _)
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (s i : ℝ) * ((s i : ℝ) * JordanRegions.regionIntegral
        (fun x : (R i).change '' cube k => cellCoefficient c omega x)) := by
      rcases (R i).unit_sign with hs | hs <;> simp [hs]
    _ = (s i : ℝ) * cellIntegral (d i) omega :=
      congrArg (fun t => (s i : ℝ) * t) (hp i).2.symm

/-- Compact injectivity globalizes the local inverse neighborhoods. The
open image property and inverse regularity are then checked pointwise. -/
theorem compact_parameter_extension : compact_parameter_extensionType := by
  intro k K h U hK hU hKU hh hinj hdet
  have hA (x : E k) (hx : x ∈ K) :
      ∃ A : E k ≃L[ℝ] E k, A.toContinuousLinearMap = fderiv ℝ h x := by
    refine ⟨((fderiv ℝ h x).toLinearMap.equivOfDetNeZero (hdet x hx)).toContinuousLinearEquiv, ?_⟩
    ext v
    rfl
  have hW (x : K) : ∃ W : Set (E k), IsOpen W ∧ x.val ∈ W ∧ W ⊆ U ∧
      ∀ z ∈ W, ∃ B : E k ≃L[ℝ] E k, B.toContinuousLinearMap = fderiv ℝ h z := by
    obtain ⟨A, ha⟩ := hA x x.property
    have hdcont : ContinuousAt (fderiv ℝ h) x :=
      (hh.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds (hKU x.property))
    have hn : {z : E k | ∃ B : E k ≃L[ℝ] E k,
        B.toContinuousLinearMap = fderiv ℝ h z} ∈ nhds (x.val) := by
      have ht := hdcont.preimage_mem_nhds (by rw [← ha]; exact A.nhds)
      exact ht
    obtain ⟨W, hw, hWo, hxW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds (hKU x.property)) hn)
    exact ⟨W, hWo, hxW, fun _ hz => (hw hz).1, fun _ hz => (hw hz).2⟩
  choose W hWo hxW hWU hWB using hW
  let G := ⋃ x : K, W x
  have hGo : IsOpen G := isOpen_iUnion hWo
  have hKG : K ⊆ G := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hGU : G ⊆ U := iUnion_subset hWU
  have hGB (z : E k) (hz : z ∈ G) :
      ∃ B : E k ≃L[ℝ] E k, B.toContinuousLinearMap = fderiv ℝ h z := by
    obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    exact hWB x z hx
  have hlocal (x : E k) (hx : x ∈ G) :
      ∃ e : OpenPartialHomeomorph (E k) (E k), (e : E k → E k) = h ∧ x ∈ e.source := by
    obtain ⟨B, hB⟩ := hGB x hx
    have hc : ContDiffAt ℝ 1 h x := hh.contDiffAt (hU.mem_nhds (hGU hx))
    have hd : HasFDerivAt h B.toContinuousLinearMap x := by
      rw [hB]
      exact (hc.differentiableAt (by norm_num)).hasFDerivAt
    exact ⟨hc.toOpenPartialHomeomorph h hd (by norm_num), rfl,
      hc.mem_toOpenPartialHomeomorph_source hd (by norm_num)⟩
  obtain ⟨T, hTo, hKT, hTinj⟩ := hinj.exists_isOpen_superset hK
    (fun x hx => (hh.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt)
    (fun x hx => by
      obtain ⟨e, he, hx⟩ := hlocal x (hKG hx)
      exact ⟨e.source, e.open_source.mem_nhds hx, he ▸ e.injOn⟩)
  let V := T ∩ G
  have hVo : IsOpen V := hTo.inter hGo
  have hKV : K ⊆ V := subset_inter hKT hKG
  have hVU : V ⊆ U := inter_subset_right.trans hGU
  have hVi : InjOn h V := hTinj.mono inter_subset_left
  have hopen : IsOpenMap (V.domRestrict h) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    obtain ⟨e, he, hx⟩ := hlocal x x.property.2
    have hmap : Filter.map h (nhds (x.val)) = nhds (h x) := by
      simpa only [he] using e.map_nhds_eq hx
    have hval := hVo.isOpenEmbedding_subtypeVal.map_nhds_eq x
    change nhds (h x) ≤ Filter.map (h ∘ Subtype.val) (nhds x)
    rw [← Filter.map_map, hval, hmap]
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hVi.toPartialEquiv h V) (hh.continuousOn.mono hVU) hopen hVo
  have he : (e : E k → E k) = h := rfl
  have heS : e.source = V := rfl
  refine ⟨e, he, hKV, hVU, hh.mono hVU, ?_⟩
  intro y hy
  have hx : e.symm y ∈ V := e.map_target hy
  obtain ⟨B, hB⟩ := hGB (e.symm y) hx.2
  have hc : ContDiffAt ℝ 1 h (e.symm y) := hh.contDiffAt (hU.mem_nhds (hVU hx))
  have hd : HasFDerivAt h B.toContinuousLinearMap (e.symm y) := by
    rw [hB]
    exact (hc.differentiableAt (by norm_num)).hasFDerivAt
  exact (e.contDiffAt_symm hy (f₀' := B) (by simpa only [he] using hd)
    (by simpa only [he] using hc)).contDiffWithinAt

theorem cube_reparametrization_from_map : cube_reparametrization_from_mapType := by
  intro k n O c d s h U hU hcube hh hi himage hs hsign hagrees
  have hd : ∀ x ∈ cube k, (fderiv ℝ h x).det ≠ 0 := by
    intro x hx hz
    have hzsign := hsign x hx
    rw [hz, Real.sign_zero] at hzsign
    rcases hs with hs | hs <;> norm_num [hs] at hzsign
  obtain ⟨e, he, hsource, hSU, heC, heiC⟩ := compact_parameter_extension
    (cube k) h U (DiscontinuityCriterion.carrier_compact (cubeBox k)) hU hcube hh hi hd
  have hmap : MapsTo h (cube k) (cube k) := fun x hx =>
    himage.subset (mem_image_of_mem h hx)
  refine ⟨{
    change := e
    regular := heC
    inverse_regular := heiC
    domain := hsource
    image := ?_
    unit_sign := hs
    sign := ?_
    agrees := ?_
  }⟩
  · simpa only [he] using himage
  · simpa only [he] using hsign
  · intro x
    have hv : (c.toFun x).val = cellExtension d (e x) := by
      simpa only [he] using hagrees x
    exact hv.trans (Cells.extension_on_cube d ⟨e x, by simpa only [he] using hmap x.property⟩)

theorem cell_assembly_integral : cell_assembly_integralType := by
  intro k n O V C D h omega homega
  induction h with
  | refl C => rfl
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | add h h' ih ih' => simpa only [map_add] using congrArg₂ (· + ·) ih ih'
  | smul a h ih => simpa only [map_zsmul] using congrArg (fun t : ℝ => a • t) ih
  | reparametrize c d s R hmap =>
    simpa only [map_zsmul, Cells.chainIntegral_single, zsmul_eq_mul, Int.cast_one, one_mul] using
      cell_reparametrization c d s ⟨R⟩ V omega homega hmap
  | subdivide hk c d s R seams hz cover overlap hmap =>
    simpa only [map_sum, map_zsmul, Cells.chainIntegral_single, zsmul_eq_mul,
      Int.cast_one, one_mul] using
      cell_subdivision hk c d s R seams hz cover overlap V omega homega hmap

theorem cell_piecewise_stokes_refined : cell_piecewise_stokes_refinedType := by
  intro k n N P O V c a outer refined left right b s hassembly hR hboundary
    omega homega hmap hright
  have hzero : IsCrForm (some 0) V omega :=
    ⟨homega.1, fun I =>
      ((crOn_iff_contDiffOn 1 V _ homega.1).mp (homega.2 I)).continuousOn⟩
  have hp (i : Fin P) : chainIntegral omega
      (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) = 0 := by
    rw [map_sub, map_zsmul, Cells.chainIntegral_single, Cells.chainIntegral_single]
    simp only [zsmul_eq_mul, Int.cast_one, one_mul]
    exact sub_eq_zero.mpr (cell_reparametrization (left i) (right i) (s i) (hR i)
      V omega hzero (hright i))
  calc
    _ = ∑ j, (a j : ℝ) * chainIntegral omega (cellBoundary (c j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Cells.cell_stokes_c1 (c j) V omega homega (hmap j)]
    _ = chainIntegral omega (∑ j, a j • cellBoundary (c j)) := by
      simp only [map_sum, map_zsmul, zsmul_eq_mul]
    _ = chainIntegral omega refined := cell_assembly_integral hassembly omega hzero
    _ = chainIntegral omega outer := by
      rw [hboundary, map_add, map_sum]
      simp only [map_zsmul, hp, zsmul_zero, Finset.sum_const_zero, add_zero]

/-- Continuity on the actual closed parameter subregion only. -/
theorem region_coefficient_continuous {k n : ℕ} {O V : Set (E n)}
    (c : CellRegion k O) (omega : FormField n k)
    (homega : IsCrForm (some 0) V omega)
    (hmap : ∀ x ∈ closure c.domain, cellExtension c.cell x ∈ V) :
    ContinuousOn (cellCoefficient c.cell omega) (closure c.domain) := by
  have hcube : closure c.domain ⊆ cube k :=
    (DiscontinuityCriterion.carrier_compact (cubeBox k)).isClosed.closure_subset_iff.mpr
      c.subset_cube
  apply Cells.C1.pullback_evaluation_continuousOn omega homega (standardBasis k)
  · exact (Cells.extension_C1 c.cell).continuousOn.mono
      (hcube.trans (extension_spec c.cell).2.1)
  · exact ((Cells.extension_C1 c.cell).continuousOn_fderiv_of_isOpen
      (extension_spec c.cell).1 le_rfl).mono (hcube.trans (extension_spec c.cell).2.1)
  · exact hmap

theorem region_coefficient_integrable {k n : ℕ} {O V : Set (E n)}
    (c : CellRegion k O) (hj : JordanRegions.Jordan c.domain)
    (omega : FormField n k) (homega : IsCrForm (some 0) V omega)
    (hmap : ∀ x ∈ closure c.domain, cellExtension c.cell x ∈ V) :
    JordanRegions.RegionIntegrable (fun x : c.domain => cellCoefficient c.cell omega x) := by
  cases k with
  | zero => exact ((JordanRegions.zero_dimension c.domain).2.2 _).1
  | succ k =>
    exact JordanRegions.integrable_continuous_on_closure (Nat.succ_pos k) hj
      (fun x : closure c.domain => cellCoefficient c.cell omega x)
      (continuousOn_iff_continuous_domRestrict.mp (region_coefficient_continuous c omega homega hmap))

/-- Jordan frontiers can be discarded even when the two coefficients are
not equal there. In degree zero every subset is open, so equality in the
interior already is equality everywhere. -/
theorem region_integral_congr_interior {k : ℕ} {S : Set (E k)}
    (hj : JordanRegions.Jordan S) (f g : E k → ℝ)
    (hf : JordanRegions.RegionIntegrable (fun x : S => f x))
    (hg : JordanRegions.RegionBounded (fun x : S => g x))
    (heq : ∀ x ∈ interior S, f x = g x) :
    JordanRegions.RegionIntegrable (fun x : S => g x) ∧
    JordanRegions.regionIntegral (fun x : S => f x) =
      JordanRegions.regionIntegral (fun x : S => g x) := by
  cases k with
  | zero =>
    have hS : IsOpen S := isOpen_discrete S
    have he : (fun x : S => f x) = (fun x : S => g x) := by
      funext x
      exact heq x (hS.interior_eq.symm ▸ x.property)
    rw [← he]
    exact ⟨hf, rfl⟩
  | succ k =>
    let Q := JordanRegions.enclosingBox S
    have hQ : JordanRegions.Encloses S Q :=
      JordanRegions.enclosingBox_encloses (JordanRegions.jordan_bounded hj)
    have hfi := (JordanRegions.region_integrable_iff_box _ hQ).mp hf
    have hz := (JordanRegions.jordan_iff_boundary (Nat.succ_pos k) S
      (JordanRegions.jordan_bounded hj)).mp hj
    have he : ∀ x ∈ Darboux.carrier Q, x ∉ frontier S →
        JordanRegions.zeroExtension (fun x : S => f x) x =
          JordanRegions.zeroExtension (fun x : S => g x) x := by
      intro x hx hfront
      by_cases hs : x ∈ S
      · rw [JordanRegions.zeroExtension_apply _ ⟨x, hs⟩,
          JordanRegions.zeroExtension_apply _ ⟨x, hs⟩]
        apply heq
        by_contra hn
        exact hfront ⟨subset_closure hs, hn⟩
      · rw [JordanRegions.zeroExtension_of_not_mem _ hs,
          JordanRegions.zeroExtension_of_not_mem _ hs]
    obtain ⟨hgi, hv⟩ := LowerDimensionalImages.coefficient_integral_unchanged
      (Nat.succ_pos k) (frontier S) hz Q _ _ hfi
      (JordanRegions.zeroExtension_bounded _ hg Q) he
    have hgr := (JordanRegions.region_integrable_iff_box _ hQ).mpr hgi
    refine ⟨hgr, ?_⟩
    exact (JordanRegions.integral_eq_on_enclosing_box _ hf hQ hfi).trans
      (hv.symm.trans (JordanRegions.integral_eq_on_enclosing_box _ hgr hQ hgi).symm)

/-- Matching parametrizations have the same first jet in the interior
of a displayed subregion. No derivative equality on its frontier is used. -/
theorem region_reparametrized_coefficient {k n : ℕ} {O : Set (E n)}
    (c d : CellRegion k O) (s : ℤ) (R : RegionReparametrization c d s)
    (omega : FormField n k) (x : E k) (hx : x ∈ interior c.domain) :
    cellCoefficient c.cell omega x = cellCoefficient d.cell omega (R.change x) *
      (fderiv ℝ R.change x).det := by
  have hs : x ∈ c.domain := interior_subset hx
  have ht : R.change x ∈ d.domain := R.image.subset (mem_image_of_mem R.change hs)
  have he : cellExtension c.cell =ᶠ[nhds x] cellExtension d.cell ∘ R.change :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hx)
      (fun y hy => R.agrees y (interior_subset hy))
  have hjet := he.fderiv_eq (𝕜 := ℝ)
  have hdf : DifferentiableAt ℝ (cellExtension d.cell) (R.change x) :=
    ((Cells.extension_C1 d.cell).differentiableOn (by norm_num)).differentiableAt
      ((extension_spec d.cell).1.mem_nhds ((extension_spec d.cell).2.1 (d.subset_cube ht)))
  have hde : DifferentiableAt ℝ R.change x :=
    (R.regular.differentiableOn (by norm_num)).differentiableAt
      (R.change.open_source.mem_nhds (R.domain (subset_closure hs)))
  have hp : pullback (cellExtension c.cell) omega x =
      pullback R.change (pullback (cellExtension d.cell) omega) x := by
    ext v
    change omega (cellExtension c.cell x)
      (fun j => fderiv ℝ (cellExtension c.cell) x (v j)) = _
    rw [R.agrees x hs, hjet, fderiv_comp x hdf hde]
    rfl
  change pullback (cellExtension c.cell) omega x (standardBasis k) = _
  rw [hp]
  have htform : pullback (cellExtension d.cell) omega =
      fun y => cellCoefficient d.cell omega y • volumeForm k :=
    funext (Cells.cell_pullback_top d.cell omega)
  rw [htform]
  exact Orientation.pullback_coefficient _ _ _

theorem region_reparametrization : region_reparametrizationType := by
  intro k n O c d s hj R V omega homega hmapc hmapd
  have hc : IsCompact (closure c.domain) := (JordanRegions.jordan_bounded hj).isCompact_closure
  have htarget := (RegionSubstitution.jordan_image R.change R.regular R.inverse_regular
    c.domain hj hc R.domain).2
  have hdj : JordanRegions.Jordan d.domain := by simpa only [R.image] using htarget
  have hci := region_coefficient_integrable c hj omega homega hmapc
  have hdi := region_coefficient_integrable d hdj omega homega hmapd
  have hb : JordanRegions.RegionBounded
      (fun y : R.change '' c.domain => cellCoefficient d.cell omega y) := by
    change Specs.D04.C06.JordanRegions.Model.RegionBounded
      (S := R.change '' c.domain) _
    rw [R.image]
    exact hdi.1
  have hs : (s : ℝ) = 1 ∨ (s : ℝ) = -1 := by
    rcases R.unit_sign with h | h <;> simp [h]
  have hsub := Orientation.signed_region_substitution R.change R.regular R.inverse_regular
    c.domain hj hc R.domain (s : ℝ) hs R.sign
    (fun y : R.change '' c.domain => cellCoefficient d.cell omega y) hb
  let G : E k → ℝ := fun x =>
    pullback R.change (fun y => JordanRegions.zeroExtension
      (fun y : R.change '' c.domain => cellCoefficient d.cell omega y) y • volumeForm k)
      x (standardBasis k)
  have heq : ∀ x ∈ interior c.domain, cellCoefficient c.cell omega x = G x := by
    intro x hx
    dsimp only [G]
    rw [Orientation.pullback_coefficient,
      JordanRegions.zeroExtension_apply _ ⟨R.change x,
        mem_image_of_mem R.change (interior_subset hx)⟩]
    exact region_reparametrized_coefficient c d s R omega x hx
  obtain ⟨hgi, hcg⟩ := region_integral_congr_interior hj
    (cellCoefficient c.cell omega) G hci hsub.1 heq
  have hgd : JordanRegions.regionIntegral (fun x : c.domain => G x) =
      (s : ℝ) * JordanRegions.regionIntegral
        (fun y : R.change '' c.domain => cellCoefficient d.cell omega y) :=
    hsub.2.2 (Or.inr hgi)
  change Specs.D04.C06.JordanRegions.Model.regionIntegral _ =
    (s : ℝ) * Specs.D04.C06.JordanRegions.Model.regionIntegral _ at hgd
  rw [R.image] at hgd
  exact hcg.trans hgd

@[simp] theorem regionChainIntegral_single {k n : ℕ} {O : Set (E n)}
    (omega : FormField n k) (c : CellRegion k O) (a : ℤ) :
    regionChainIntegral omega (Finsupp.single c a) = a • cellRegionIntegral c omega := by
  simp [regionChainIntegral]

theorem region_assembly_integral : region_assembly_integralType := by
  intro k n O V C D h omega homega
  induction h with
  | refl C => rfl
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | add h h' ih ih' => simpa only [map_add] using congrArg₂ (· + ·) ih ih'
  | smul a h ih => simpa only [map_zsmul] using congrArg (fun t : ℝ => a • t) ih
  | reparametrize c d s hj R hmapc hmapd =>
    simpa only [map_zsmul, regionChainIntegral_single, zsmul_eq_mul, Int.cast_one, one_mul] using
      region_reparametrization c d s hj R V omega homega hmapc hmapd
  | subdivide hk c S hS hj seams hz cover overlap hmap =>
    have hi (i : Fin _) := region_coefficient_integrable
      (⟨c.cell, S i, (hS i).trans c.subset_cube⟩ : CellRegion k O) (hj i) omega homega
      (fun x hx => hmap x (closure_mono (hS i) hx))
    have hu := integral_union_off_seams hk S seams hz hj overlap
      (cellCoefficient c.cell omega) hi
    have hsum : cellRegionIntegral c omega =
        ∑ i, cellRegionIntegral
          (⟨c.cell, S i, (hS i).trans c.subset_cube⟩ : CellRegion k O) omega := by
      have hv := hu.2
      change Specs.D04.C06.JordanRegions.Model.regionIntegral _ =
        ∑ i, Specs.D04.C06.JordanRegions.Model.regionIntegral _ at hv
      rw [cover] at hv
      exact hv
    simpa only [map_sum, regionChainIntegral_single, one_zsmul] using hsum

theorem wholeCellRegion_integral {k n : ℕ} {O V : Set (E n)}
    (c : Cell 1 k O) (omega : FormField n k) (homega : IsCrForm (some 0) V omega)
    (hmap : ∀ x : cube k, (c.toFun x).val ∈ V) :
    cellRegionIntegral (wholeCellRegion c) omega = cellIntegral c omega := by
  exact (D04Stokes.box_integral_eq_region (cubeBox k)
    (fun i => by norm_num [cubeBox]) _
    (coefficient_continuous_near_image c omega homega hmap)).symm

theorem regionBoundary_integral {k n : ℕ} {O V : Set (E n)}
    (c : Cell 1 (k+1) O) (omega : FormField n k) (homega : IsCrForm (some 0) V omega)
    (hmap : ∀ x : cube (k+1), (c.toFun x).val ∈ V) :
    regionChainIntegral omega (regionBoundary c) = chainIntegral omega (cellBoundary c) := by
  simp only [regionBoundary, cellBoundary, map_sum, map_zsmul, map_sub,
    regionChainIntegral_single, Cells.chainIntegral_single]
  apply Finset.sum_congr rfl
  intro i hi
  rw [wholeCellRegion_integral (cellFace c i true) omega homega
      (fun x => hmap ⟨faceInsertion i true x, faceInsertion_mem i true x.property⟩),
    wholeCellRegion_integral (cellFace c i false) omega homega
      (fun x => hmap ⟨faceInsertion i false x, faceInsertion_mem i false x.property⟩)]

theorem cell_piecewise_stokes_regions : cell_piecewise_stokes_regionsType := by
  intro k n N P O V c a outer refined left right b s hassembly hj hR hboundary houter
    omega homega hmap hleft hright
  have hzero : IsCrForm (some 0) V omega :=
    ⟨homega.1, fun I =>
      ((crOn_iff_contDiffOn 1 V _ homega.1).mp (homega.2 I)).continuousOn⟩
  have hp (i : Fin P) : regionChainIntegral omega
      (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) = 0 := by
    rw [map_sub, map_zsmul, regionChainIntegral_single, regionChainIntegral_single]
    simp only [zsmul_eq_mul, Int.cast_one, one_mul]
    exact sub_eq_zero.mpr (region_reparametrization (left i) (right i) (s i)
      (hj i) (hR i) V omega hzero (hleft i) (hright i))
  refine ⟨?_, ?_⟩
  · intro p hp
    exact region_coefficient_integrable p (houter p hp).1 omega hzero (houter p hp).2
  calc
    _ = ∑ j, (a j : ℝ) * regionChainIntegral omega (regionBoundary (c j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Cells.cell_stokes_c1 (c j) V omega homega (hmap j),
        regionBoundary_integral (c j) omega hzero (hmap j)]
    _ = regionChainIntegral omega (∑ j, a j • regionBoundary (c j)) := by
      simp only [map_sum, map_zsmul, zsmul_eq_mul]
    _ = regionChainIntegral omega refined := region_assembly_integral hassembly omega hzero
    _ = regionChainIntegral omega outer := by
      rw [hboundary, map_add, map_sum]
      simp only [map_zsmul, hp, zsmul_zero, Finset.sum_const_zero, add_zero]

theorem manifold_cell_display_exists : manifold_cell_display_existsType := by
  intro k n M o K hK
  obtain ⟨m, R, w, hw⟩ := D04Stokes.finite_ambient_stokes_partition o K hK
  let P : SignedChartPartition o K := {
    count := m
    chart := fun i => (R i).chart
    weight := w
    partition := ⟨hw.1, hw.2.1, fun i => ⟨(hw.2.2.1 i).1,
      ((hw.2.2.1 i).2).trans (R i).in_chart⟩, hw.2.2.2⟩
    sign := fun i => (R i).sign
    agrees := fun i => (R i).agrees
  }
  refine ⟨{
    partition := P
    rectangle := fun i => {
      box := (R i).box
      nondegenerate := (R i).nondegenerate
      source_box := (R i).source_box
      domain := (R i).domain
      open_domain := (R i).open_domain
      domain_box := (R i).domain_box
      extension := (R i).extension
      regular := (R i).regular
      agrees := (R i).agrees_extension
    }
    coordinates := ?_
  }⟩
  intro i x hx
  have ht := (R i).coordinates x ((hw.2.2.1 i).2 hx)
  cases hh : (R i).chart.half with
  | false =>
    simp only [hh, Bool.false_eq_true, ↓reduceIte] at ht
    exact fun j => ⟨(ht j).1.le, (ht j).2.le⟩
  | true =>
    simp only [hh, ↓reduceIte] at ht
    exact D04Stokes.halfBoxInterior_subset_carrier (R i).box ht

theorem manifold_cell_display_integral : manifold_cell_display_integralType := by
  intro k n M o K D V omega hMV homega hsupport I hI
  let eta := tangentRestriction 1 k M omega
  let A := D.partition
  have hp : Specs.D04.C14.FiniteCompactPartition.Model.PartitionNear M
      (topSupport eta) (fun i => Subtype.val ⁻¹' (A.chart i).ambient) A.count id A.weight := by
    refine ⟨A.partition.1, A.partition.2.1, A.partition.2.2.1, ?_, A.partition.2.2.2.2⟩
    obtain ⟨U, hU, hKU, hsum⟩ := A.partition.2.2.2.1
    exact ⟨U, hU, hsupport.trans hKU, hsum⟩
  let P : SignedChartPartition o (topSupport eta) := {
    count := A.count
    chart := A.chart
    weight := A.weight
    partition := hp
    sign := A.sign
    agrees := A.agrees
  }
  have hval : I = ∑ i, (A.sign i).val *
      coefficientIntegral (localizedTopCoefficient eta (A.chart i) (A.weight i)) :=
    ((hI.2.2.2 P).2).symm
  apply hval.trans
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun t => (A.sign i).val * t)
  let beta : FormField n k := fun x => A.weight i x • omega x
  have hbeta : IsCrForm (some 0) V beta :=
    D04.isCrForm_function_smul 0 V (A.weight i) omega homega.1
      ((crOn_iff_contDiffOn 0 V _ homega.1).mpr
        ((A.partition.1 i).of_le (by simp)).contDiffOn) homega
  have hbs : topSupport (tangentRestriction 1 k M beta) ⊆
      tsupport (fun x : M => A.weight i x) :=
    D04Stokes.tangentRestriction_weight_support omega (A.weight i)
  have hbc := D04Stokes.tangentRestriction_top_continuous o.manifold V beta hMV hbeta
  have hc := (A.partition.2.2.1 i).1.of_isClosed_subset isClosed_closure hbs
  let R := D.rectangle i
  have hrect := D04Stokes.ambient_chart_rectangle_coefficient (A.chart i) beta hbc hc
    (hbs.trans (A.partition.2.2.1 i).2) R.box R.nondegenerate R.source_box
    (fun x hx => D.coordinates i x (hbs hx))
    R.domain R.open_domain R.domain_box R.extension R.regular R.agrees
  have hmap : MapsTo R.extension (Darboux.carrier R.box) V := by
    intro x hx
    rw [R.agrees ⟨R.source_box hx, R.domain_box hx⟩]
    exact hMV ((A.chart i).map_source (R.source_box hx)).1
  have hcell := D04Stokes.rectangle_cell_integral R.box R.nondegenerate R.extension
    R.domain R.open_domain R.domain_box R.regular V beta hbeta hmap
  have he : localizedTopCoefficient eta (A.chart i) (A.weight i) =
      topCoefficient (tangentRestriction 1 k M beta) (A.chart i) := by
    funext u
    rfl
  rw [he]
  exact hrect.2.trans hcell.symm

theorem compact_manifold_cell_integral : compact_manifold_cell_integralType := by
  intro k n M o hc V omega hMV homega
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hc
  obtain ⟨D⟩ := manifold_cell_display_exists o univ isCompact_univ
  have hcont := D04Stokes.tangentRestriction_top_continuous o.manifold V omega hMV homega
  have hs : IsCompact (topSupport (tangentRestriction 1 (k+1) M omega)) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  obtain ⟨I, hI⟩ := D04Stokes.positive_integral_exists o _ hcont hs
  exact ⟨D, I, hI, manifold_cell_display_integral o D V omega hMV homega
    (subset_univ _) I hI⟩

theorem jordan_regions_of_finite_seams : jordan_regions_of_finite_seamsType := by
  intro k m N hk d K f hd hK hf S hS hfront i
  have hz := (LowerDimensionalImages.finite_C1_images d K f hd hK hf).2
  exact (JordanRegions.jordan_iff_boundary hk (S i)
    ((DiscontinuityCriterion.carrier_compact (cubeBox k)).isBounded.subset (hS i))).mpr
      (NullCovers.contentZero_mono (hfront i) hz)

/-- A finite smooth Euclidean partition with support in prescribed open
neighborhoods. Its sum is one on an open neighborhood of the compact set. -/
theorem finite_parameter_partition {k : ℕ} (K : Set (E k)) (hK : IsCompact K)
    (U : K → Set (E k)) (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x.val ∈ U x) :
    ∃ (m : ℕ) (p : Fin m → K) (w : Fin m → E k → ℝ) (V : Set (E k)),
      (∀ i, ContDiff ℝ ∞ (w i)) ∧ (∀ i, tsupport (w i) ⊆ U (p i)) ∧
      IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∑ i, w i x = 1 := by
  have hc (x : K) := D04.EuclideanSmoothCutoffs.exists_smooth_cutoff
    {x.val} (U x) isCompact_singleton (hU x) (singleton_subset_iff.mpr (hxU x))
  choose ρ hρ using hc
  choose V hVo hxV hρone using fun x : K => (hρ x).2.2.2.1
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hVo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩ (mem_singleton x)⟩)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let p : Fin (Fintype.card I) → K := fun i => (e i).val
  obtain ⟨w, hw, hn, hs, hr, hone⟩ := D04.FiniteCompactPartition.normalize_bumps
    (fun i => ρ (p i)) (fun i => (hρ (p i)).1)
    (fun i x => ((hρ (p i)).2.2.1 x).1)
  refine ⟨Fintype.card I, p, w, ⋃ q ∈ I, V q, hw, ?_,
    isOpen_biUnion (fun q _ => hVo q), hI, ?_⟩
  · intro i
    exact (hs (id : E k → E k) i).trans (hρ (p i)).2.2.2.2.2
  · intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
    obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
    have hpi : p i = q := congrArg Subtype.val hi
    apply hone
    have hval : ρ (p i) x = 1 := by rw [hpi]; exact hρone q hxq
    rw [← hval]
    exact Finset.single_le_sum
      (fun j _ => ((hρ (p j)).2.2.1 x).1) (Finset.mem_univ i)

/-- Multiplying by a smooth weight whose closed support lies in a C¹
patch produces a globally C¹ map, even if that patch's chosen representative
is irregular elsewhere. -/
theorem contDiff_weighted_local {k l : ℕ} (w : E k → ℝ) (g : E k → E l)
    (U : Set (E k)) (hw : ContDiff ℝ 1 w) (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U) (hs : tsupport w ⊆ U) :
    ContDiff ℝ 1 (fun x => w x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport w
  · exact hw.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hs hx)))
  · have he : (fun y => w y • g y) =ᶠ[nhds x] (fun _ => (0 : E l)) := by
      filter_upwards [(isClosed_tsupport w).isOpen_compl.mem_nhds hx] with y hy
      have hz : w y = 0 := by
        by_contra hn
        exact hy (subset_tsupport w hn)
      simp only [hz, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem compact_local_extension : compact_local_extensionType := by
  intro k l K h hK hlocal
  choose U g hU hxU hg heq using fun x : K => hlocal x x.property
  obtain ⟨m, p, w, V, hw, hs, hV, hKV, hsum⟩ :=
    finite_parameter_partition K hK U hU hxU
  let F : E k → E l := fun x => ∑ i, w i x • g (p i) x
  have hF : ContDiff ℝ 1 F := ContDiff.sum (fun i _ =>
    contDiff_weighted_local (w i) (g (p i)) (U (p i))
      ((hw i).of_le (by simp)) (hU (p i)) (hg (p i)) (hs i))
  refine ⟨F, hF, ?_⟩
  intro x hx
  change (∑ i, w i x • g (p i) x) = h x
  calc
    _ = ∑ i, w i x • h x := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hwx : w i x = 0
      · simp [hwx]
      · rw [heq (p i) ⟨hx, hs i (subset_tsupport _ hwx)⟩]
    _ = (∑ i, w i x) • h x := Finset.sum_smul.symm
    _ = h x := by rw [hsum x (hKV hx), one_smul]

/-- Equality on a full-dimensional parameter germ determines the derivative
of every local extension, including derivatives at closed-cube corners. -/
theorem local_extension_derivative {k l : ℕ} {K U : Set (E k)}
    {F g h : E k → E l} {x : E k} (hx : x ∈ K) (hU : IsOpen U) (hxU : x ∈ U)
    (hK : UniqueDiffWithinAt ℝ K x) (hF : DifferentiableAt ℝ F x)
    (hg : DifferentiableAt ℝ g x) (hFK : EqOn F h K) (hgK : EqOn g h (K ∩ U)) :
    fderiv ℝ F x = fderiv ℝ g x := by
  have he : F =ᶠ[nhdsWithin x K] g := by
    filter_upwards [inter_mem_nhdsWithin K (hU.mem_nhds hxU)] with y hy
    exact (hFK hy.1).trans (hgK hy).symm
  rw [← hF.fderivWithin hK, ← hg.fderivWithin hK]
  exact Filter.EventuallyEq.fderivWithin_eq he ((hFK hx).trans (hgK ⟨hx, hxU⟩).symm)

theorem compact_local_diffeomorphism : compact_local_diffeomorphismType := by
  intro k K h hK hdiff hinj hlocal
  obtain ⟨F, hF, hFK⟩ := compact_local_extension K h hK (by
    intro x hx
    obtain ⟨U, g, hU, hxU, hg, he, hd⟩ := hlocal x hx
    exact ⟨U, g, hU, hxU, hg, he⟩)
  have hdet : ∀ x ∈ K, (fderiv ℝ F x).det ≠ 0 := by
    intro x hx
    obtain ⟨U, g, hU, hxU, hg, he, hd⟩ := hlocal x hx
    rw [local_extension_derivative hx hU hxU (hdiff x hx)
      (hF.differentiable (by norm_num) x)
      ((hg.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)) hFK he]
    exact hd
  have hFi : InjOn F K := by
    intro x hx y hy he
    exact hinj hx hy ((hFK hx).symm.trans (he.trans (hFK hy)))
  obtain ⟨e, he, hsource, hSU, heC, heiC⟩ := compact_parameter_extension
    K F univ hK isOpen_univ (subset_univ _) hF.contDiffOn hFi hdet
  exact ⟨e, fun x hx => he ▸ hFK hx, hsource, heC, heiC⟩

theorem cube_reparametrization_from_local : cube_reparametrization_from_localType := by
  intro k n O c d s h hi himage hs hlocal hagrees
  have hn (x : E k) (hx : x ∈ cube k) :
      ∃ (U : Set (E k)) (g : E k → E k),
        IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (cube k ∩ U) ∧
        (fderiv ℝ g x).det ≠ 0 := by
    obtain ⟨U, g, hU, hxU, hg, he, hsign⟩ := hlocal x hx
    refine ⟨U, g, hU, hxU, hg, he, ?_⟩
    intro hz
    rw [hz, Real.sign_zero] at hsign
    rcases hs with hs | hs <;> norm_num [hs] at hsign
  obtain ⟨e, he, hsource, heC, heiC⟩ := compact_local_diffeomorphism
    (cube k) h (DiscontinuityCriterion.carrier_compact (cubeBox k))
    (Cells.cube_uniqueDiff k) hi hn
  have heimage : e '' cube k = cube k := by
    rw [he.image_eq]
    exact himage
  refine ⟨{
    change := e
    regular := heC
    inverse_regular := heiC
    domain := hsource
    image := heimage
    unit_sign := hs
    sign := ?_
    agrees := ?_
  }⟩
  · intro x hx
    obtain ⟨U, g, hU, hxU, hg, heq, hsign⟩ := hlocal x hx
    rw [local_extension_derivative hx hU hxU (Cells.cube_uniqueDiff k x hx)
      ((heC.contDiffAt (e.open_source.mem_nhds (hsource hx))).differentiableAt (by norm_num))
      ((hg.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)) he heq]
    exact hsign
  · intro x
    have hex : (c.toFun x).val = cellExtension d (e x) := by rw [he x.property]; exact hagrees x
    exact hex.trans (Cells.extension_on_cube d
      ⟨e x, heimage.subset (mem_image_of_mem e x.property)⟩)

/-! Assembly on canonical geometric patches, including arbitrary Jordan regions
and parameter changes given by separate local diffeomorphisms. -/
theorem patch_local_reparametrization : patch_local_reparametrizationType :=
  D04.GeometricPatches.local_reparametrization

theorem patch_of_local_extensions : patch_of_local_extensionsType :=
  D04.GeometricPatches.patch_of_local_extensions

theorem geometric_assembly_integral : geometric_assembly_integralType :=
  D04.GeometricPatches.geometric_equivalence_sound

theorem manifold_boundary_localization : manifold_boundary_localizationType :=
  D04.ManifoldBoundaryAssembly.regular_boundary_localization

theorem manifold_piecewise_stokes : manifold_piecewise_stokesType :=
  D04.ManifoldBoundaryAssembly.positive_boundary_assembly

theorem manifold_piecewise_stokes_points : manifold_piecewise_stokes_pointsType :=
  D04.ManifoldBoundaryAssembly.signed_point_boundary_assembly

theorem geometric_integral_exists : geometric_integral_existsType :=
  D04.GeometricUnion.geometric_union_integral_exists

theorem geometric_integral_eq_sum : geometric_integral_eq_sumType :=
  D04.GeometricUnion.geometric_union_integral_eq_sum

theorem geometric_integral_independent : geometric_integral_independentType :=
  D04.GeometricUnion.geometric_union_integral_independent

theorem regular_cell_geometric_display : regular_cell_geometric_displayType :=
  D04.GeometricUnion.cell_family_display

theorem cell_union_from_lower_parameters : cell_union_from_lower_parametersType :=
  D04.GeometricUnion.cell_family_from_lower_parameters

theorem cell_union_from_lower_manifolds : cell_union_from_lower_manifoldsType :=
  D04.GeometricUnion.cell_family_from_lower_manifolds

theorem manifold_union_from_lower_parameters : manifold_union_from_lower_parametersType :=
  D04.GeometricUnion.manifold_family_from_lower_parameters

theorem manifold_union_from_lower_manifolds : manifold_union_from_lower_manifoldsType :=
  D04.GeometricUnion.manifold_family_from_lower_manifolds


open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model

theorem cell_boundary_patch_display : cell_boundary_patch_displayType := by
  intro k n N O c
  have hex (j : Fin N) (i : Fin (k+1)) (e : Bool) :=
    GeometricPatches.cell_patch_exists (cellFace (c j) i e)
  choose P hr hm hi using hex
  exact ⟨P, fun j i e => ⟨hr j i e, fun x _ => congrFun (hm j i e) x⟩⟩

theorem cell_patch_integral : cell_patch_integralType := by
  intro k n O c P hregion hmap omega ho
  obtain ⟨Q, hQregion, hQmap, hQintegral⟩ := GeometricPatches.cell_patch_exists c
  apply (GeometricPatches.representative_independent P Q
    (hregion.trans hQregion.symm) ?_ omega ho (fun _ => 1) continuousOn_const).trans
      (hQintegral omega ho)
  intro x hx
  rw [hQmap]
  exact hmap (hregion ▸ hx)

theorem patchBoundary_integral {k n : ℕ} {O : Set (E n)}
    (c : Cell 1 (k+1) O) (P : Fin (k+1) → Bool → Patch k O)
    (hp : ∀ i e, (P i e).region = cube k ∧
      EqOn (P i e).map (cellExtension (cellFace c i e)) (cube k))
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega) :
    patchChainIntegral omega (patchBoundary P) = chainIntegral omega (cellBoundary c) := by
  simp only [patchBoundary, cellBoundary, map_sum, map_zsmul, map_sub,
    GeometricPatches.chain_integral_single, Cells.chainIntegral_single,
    one_zsmul, plainPatch]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun t : ℝ => (-1 : ℤ) ^ i.val • t)
  exact congrArg₂ (· - ·)
    (cell_patch_integral (cellFace c i true) (P i true) (hp i true).1 (hp i true).2 omega ho)
    (cell_patch_integral (cellFace c i false) (P i false) (hp i false).1 (hp i false).2 omega ho)

theorem cell_piecewise_stokes_patches : cell_piecewise_stokes_patchesType := by
  intro k n N L O c a P hp outer left right b s hs hmatch hweight hassembly omega ho
  have hzero := D04.LocalStokes.form_C0 O omega ho
  have cancel (i : Fin L) : patchChainIntegral omega
      (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) = 0 := by
    obtain ⟨h, hm⟩ := hmatch i
    have hv := GeometricPatches.matching_reparametrization (left i).patch (right i).patch
      (s i : ℝ) (by rcases hs i with he | he <;> simp [he]) h hm omega hzero
      (left i).weight (right i).weight (left i).continuous (right i).continuous (hweight i)
    simpa only [map_sub, map_zsmul, GeometricPatches.chain_integral_single,
      one_zsmul, zsmul_eq_mul, Int.cast_one, one_mul, sub_eq_zero] using hv
  calc
    _ = ∑ j, (a j : ℝ) * chainIntegral omega (cellBoundary (c j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Cells.cell_stokes_c1 (c j) O omega ho (fun x => ((c j).toFun x).property)]
    _ = patchChainIntegral omega (∑ j, a j • patchBoundary (P j)) := by
      simp only [map_sum, map_zsmul, zsmul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun t : ℝ => (a j : ℝ) * t)
        (patchBoundary_integral (c j) (P j) (hp j) omega hzero).symm
    _ = patchChainIntegral omega
        (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) :=
      GeometricPatches.geometric_equivalence_sound omega hzero _ _ hassembly
    _ = patchChainIntegral omega outer := by
      rw [map_add, map_sum]
      simp only [map_zsmul, cancel, zsmul_zero, Finset.sum_const_zero, add_zero]

theorem local_reparametrization_from_extensions : local_reparametrization_from_extensionsType := by
  intro k S T h sigma hs hbij hlocal
  refine ⟨⟨h, hbij, ?_⟩, rfl⟩
  intro x hx
  obtain ⟨U, g, hU, hxU, hg, hgh, hsign⟩ := hlocal x hx
  have hdet : (fderiv ℝ g x).det ≠ 0 := by
    intro hz
    rw [hz, Real.sign_zero] at hsign
    rcases hs with hs | hs <;> norm_num [hs] at hsign
  obtain ⟨e, he, hxsource, hsourceU, heC, heiC⟩ := compact_parameter_extension
    {x} g U isCompact_singleton hU (singleton_subset_iff.mpr hxU) hg
    (by intro u hu v hv _; exact (mem_singleton_iff.mp hu).trans (mem_singleton_iff.mp hv).symm)
    (by intro u hu; simpa only [mem_singleton_iff.mp hu] using hdet)
  have hxe : x ∈ e.source := hxsource (mem_singleton x)
  let C := connectedComponentIn e.source x
  let er := e.restrOpen C e.open_source.connectedComponentIn
  have hC : C ⊆ e.source := connectedComponentIn_subset e.source x
  have hsrc : er.source = C := inter_eq_right.mpr hC
  have hxer : x ∈ er.source := hsrc ▸ mem_connectedComponentIn hxe
  have her : ContDiffOn ℝ 1 er er.source := heC.mono inter_subset_left
  have hier : ContDiffOn ℝ 1 er.symm er.target := heiC.mono inter_subset_left
  obtain ⟨delta, _, hsg⟩ := D04.DirectedSubstitution.open_sign er her hier
    (hsrc ▸ isPreconnected_connectedComponentIn)
  have hefun : (er : E k → E k) = g := he
  have hd : delta = sigma := by
    calc
      delta = Real.sign ((fderiv ℝ er x).det) := (hsg x hxer).symm
      _ = sigma := by rw [hefun]; exact hsign
  refine ⟨er, hxer, her, hier, ?_, fun y hy => (hsg y hy).trans hd⟩
  intro y hy
  rw [hefun]
  exact hgh ⟨hy.1, hsourceU (hC (hsrc ▸ hy.2))⟩

theorem patch_reparametrization_from_extensions : patch_reparametrization_from_extensionsType := by
  intro k n O P Q h sigma hs hbij hlocal hmap omega ho w hw
  obtain ⟨R, hR⟩ := local_reparametrization_from_extensions P.region Q.region h sigma hs hbij hlocal
  exact patch_local_reparametrization P Q sigma hs R (by simpa only [hR] using hmap) omega ho w hw

theorem geometric_cell_piecewise_stokes : geometric_cell_piecewise_stokesType := by
  intro k n N L O c P hp outer left right b s hs hmatch hweight hassembly hi hr Z hover omega ho
  cases N with
  | zero =>
    let D : GeometricDecomposition (k+1) n O := {
      count := 0
      piece := fun i => Fin.elim0 i
      compact := fun i => Fin.elim0 i
      regular := fun i => Fin.elim0 i
      subset := fun i => Fin.elim0 i
      orientation := fun i => Fin.elim0 i
      seams := {
        carrier := ∅
        isCompact := isCompact_empty
        cover := ⟨∅, Set.countable_empty, empty_subset _⟩ }
      singular := fun i => Fin.elim0 i
      overlap := fun i => Fin.elim0 i
      representation := fun i => Fin.elim0 i }
    have hv : geometricUnionIntegral D (exteriorDerivative omega) = 0 := by
      have hh := geometric_integral_eq_sum D D
        (GeometricUnion.compatible_regular_refl D.toRegularDecomposition)
        (exteriorDerivative omega) (D04.exteriorDerivative_continuous O omega ho)
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      simpa [D] using hh
    have hst := cell_piecewise_stokes_patches c (fun _ => 1) P hp outer left right b s hs
      hmatch hweight hassembly omega ho
    refine ⟨D, ?_, hv.trans ?_⟩
    · simp [D, RegularDecomposition.carrier]
    · simpa using hst
  | succ N =>
    have hkn : k+1 ≤ n := by
      have hl := LinearMap.finrank_le_finrank_of_injective
        (f := (fderiv ℝ (cellExtension (c 0)) 0).toLinearMap) (hr 0 0 (Cells.zero_mem_cube _))
      simpa only [E, finrank_euclideanSpace_fin] using hl
    obtain ⟨D, e, hD, hZ, hpieces, hcharts, hv⟩ :=
      regular_cell_geometric_display (Nat.succ_pos k) hkn c hi hr Z hover
    refine ⟨D, hD, ?_⟩
    rw [hv (exteriorDerivative omega) (D04.exteriorDerivative_continuous O omega ho)]
    have hst := cell_piecewise_stokes_patches c (fun _ => 1) P hp outer left right b s hs
      hmatch hweight hassembly omega ho
    simpa only [Int.cast_one, one_mul] using hst

open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model

theorem geometric_manifold_piecewise_stokes : geometric_manifold_piecewise_stokesType := by
  intro d n q O M bO hbO m P s hregular Z hlower hself hp hcover Zbulk hover
    l p e Q tSign b deltaOut hdOut hOut houter deltaPair hdPair hPair hpair omega ho
  obtain ⟨I, hI, hB, hst⟩ := manifold_piecewise_stokes M bO hbO m P s hregular Z hlower
    hself hp hcover (fun _ => 1) e Q tSign b deltaOut hdOut hOut houter
    deltaPair hdPair hPair (fun i => ⟨(hpair i).1, (hpair i).2, rfl⟩) omega ho
  obtain ⟨D, hD, hv⟩ := GeometricUnion.manifold_family_from_seams
    (fun j => (M j).carrier) (fun j => (M j).compact) (fun j => (M j).orientation)
    (fun j => (M j).subset_domain) Zbulk hover
  let A (j : Fin q) := Classical.choice (hI j).2.2.1
  refine ⟨D, hD, ?_⟩
  apply (hv (exteriorDerivative omega) (D04.exteriorDerivative_continuous O omega ho) A).trans
  calc
    _ = ∑ j, I j := Finset.sum_congr rfl (fun j _ => ((hI j).2.2.2 (A j)).2)
    _ = _ := by simpa only [one_zsmul] using hst

theorem geometric_manifold_piecewise_stokes_points : geometric_manifold_piecewise_stokes_pointsType := by
  intro n q O M bO hbO l p e P s c houter hpair Z hover omega ho
  obtain ⟨I, hI, hB, hst⟩ := manifold_piecewise_stokes_points M bO hbO (fun _ => 1)
    e P s c houter (fun i => ⟨(hpair i).1, rfl, (hpair i).2⟩) omega ho
  obtain ⟨D, hD, hv⟩ := GeometricUnion.manifold_family_from_seams
    (fun j => (M j).carrier) (fun j => (M j).compact) (fun j => (M j).orientation)
    (fun j => (M j).subset_domain) Z hover
  let A (j : Fin q) := Classical.choice (hI j).2.2.1
  refine ⟨D, hD, ?_⟩
  apply (hv (exteriorDerivative omega) (D04.exteriorDerivative_continuous O omega ho) A).trans
  calc
    _ = ∑ j, I j := Finset.sum_congr rfl (fun j _ => ((hI j).2.2.2 (A j)).2)
    _ = _ := by simpa only [one_zsmul] using hst

theorem cell_integral_of_same_map {k n : ℕ} {O V : Set (E n)}
    (c : Cell 1 k O) (d : Cell 1 k V)
    (h : ∀ x : cube k, (c.toFun x).val = (d.toFun x).val)
    (omega : FormField n k) : cellIntegral c omega = cellIntegral d omega := by
  apply Cells.lowerIntegral_congr
  intro x hx
  exact Cells.cellCoefficient_extension_independent c (cellExtension d) (extensionDomain d)
    (extension_spec d).1 (extension_spec d).2.1 (Cells.extension_C1 d)
    (fun u => (Cells.extension_on_cube d u).trans (h u).symm) omega ⟨x, hx⟩

theorem cell_retarget : cell_retargetType := by
  intro k n O c V hV hmap
  let d : Cell 1 k V := {
    toFun := fun x => ⟨(c.toFun x).val, hmap x⟩
    open_target := hV
    positive := c.positive
    hasExtension := c.hasExtension }
  exact ⟨d, fun _ => rfl, cell_integral_of_same_map d c (fun _ => rfl)⟩

end D04.FinitePiecewiseStokes
