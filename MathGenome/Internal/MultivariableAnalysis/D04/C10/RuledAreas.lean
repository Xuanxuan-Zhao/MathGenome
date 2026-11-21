import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.RuledAreas
import MathGenome.Internal.MultivariableAnalysis.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C10.NegligibleSeams
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace BigOperators
namespace D04.RuledAreas
open PatchGeometryGram AreaIntegral JordanRegions
open Specs.D04.C10.RuledAreas.Model

private abbrev proj (i : Fin 2) : E 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

lemma ruled_columns (a b : ℝ → E 3) (x : E 2) (da db : E 3)
    (ha : HasDerivAt a da (x 0)) (hb : HasDerivAt b db (x 0)) :
    columns (fderiv ℝ (ruled a b) x).toLinearMap 0 = da + x 1 • db ∧
    columns (fderiv ℝ (ruled a b) x).toLinearMap 1 = b (x 0) := by
  have h := (ha.hasFDerivAt.comp x (proj 0).hasFDerivAt).add
    ((proj 1).hasFDerivAt.smul (hb.hasFDerivAt.comp x (proj 0).hasFDerivAt))
  change HasFDerivAt (ruled a b) _ x at h
  rw [h.fderiv]
  constructor <;> simp [columns, PatchGeometryGram.columns,
    Specs.D04.C10.PatchGeometryGram.columnsValue,
    Specs.D04.C10.PatchGeometryGram.Model.columns, proj,
    standardBasis, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

lemma ruled_density (a b : ℝ → E 3) (x : E 2) (da db : E 3)
    (ha : HasDerivAt a da (x 0)) (hb : HasDerivAt b db (x 0)) :
    patchJacobian (ruled a b) x = ‖cross (da + x 1 • db) (b (x 0))‖ := by
  have hc := ruled_columns a b x da db ha hb
  exact (gram_cross _).trans (by rw [hc.1, hc.2])

lemma ruled_rank (a b : ℝ → E 3) (x : E 2) (da db : E 3)
    (ha : HasDerivAt a da (x 0)) (hb : HasDerivAt b db (x 0)) :
    Function.Injective (fderiv ℝ (ruled a b) x) ↔
      cross (da + x 1 • db) (b (x 0)) ≠ 0 := by
  have hc := ruled_columns a b x da db ha hb
  exact (cross_rank _).symm.trans (by rw [hc.1, hc.2])

lemma ruled_contDiff (a b : ℝ → E 3) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (ruled a b) := by
  exact (ha.comp (proj 0).contDiff).add ((proj 1).contDiff.smul (hb.comp (proj 0).contDiff))

lemma ruled_regular (a b : ℝ → E 3) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (U : Set (E 2)) (hU : IsOpen U)
    (hr : ∀ x ∈ U, cross (deriv a (x 0) + x 1 • deriv b (x 0)) (b (x 0)) ≠ 0) :
    RegularPatch U (ruled a b) := by
  refine ⟨hU, (ruled_contDiff a b ha hb).contDiffOn, fun x hx => ?_⟩
  exact (ruled_rank a b x _ _ (ha.differentiable (by norm_num) |>.differentiableAt.hasDerivAt)
    (hb.differentiable (by norm_num) |>.differentiableAt.hasDerivAt)).mpr (hr x hx)

lemma cylinder_contDiff (R : ℝ) : ContDiff ℝ 1 (cylinder R) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [cylinder] <;> fun_prop

lemma cone_contDiff (R H : ℝ) : ContDiff ℝ 1 (cone R H) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [cone] <;> fun_prop

-- Derivative columns are calculated in the shared L2 representation.
lemma cylinder_columns (R : ℝ) (x : E 2) :
    columns (fderiv ℝ (cylinder R) x).toLinearMap 0 =
      WithLp.toLp 2 ![-R * Real.sin (x 0), R * Real.cos (x 0), 0] ∧
    columns (fderiv ℝ (cylinder R) x).toLinearMap 1 =
      WithLp.toLp 2 ![0, 0, 1] := by
  have hd : HasFDerivAt (cylinder R)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi ![(-R * Real.sin (x 0)) • proj 0,
          (R * Real.cos (x 0)) • proj 0, proj 1])) x := by
    apply (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp x
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert ((Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x (proj 0).hasFDerivAt).const_mul R using 1 <;> simp [proj]; module
    · convert ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x (proj 0).hasFDerivAt).const_mul R using 1 <;> simp [proj, mul_smul]
    · exact (proj 1).hasFDerivAt
  rw [hd.fderiv]
  constructor <;> ext i <;> fin_cases i <;>
    simp [columns, PatchGeometryGram.columns, Specs.D04.C10.PatchGeometryGram.columnsValue,
      Specs.D04.C10.PatchGeometryGram.Model.columns, proj,
      standardBasis, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

lemma cone_columns (R H : ℝ) (x : E 2) :
    columns (fderiv ℝ (cone R H) x).toLinearMap 0 =
      WithLp.toLp 2 ![-(1-x 1)*R*Real.sin (x 0), (1-x 1)*R*Real.cos (x 0), 0] ∧
    columns (fderiv ℝ (cone R H) x).toLinearMap 1 =
      WithLp.toLp 2 ![-R*Real.cos (x 0), -R*Real.sin (x 0), H] := by
  let A : E 2 →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    ![((-(1-x 1)*R*Real.sin (x 0)) • proj 0) + ((-R*Real.cos (x 0)) • proj 1),
      (((1-x 1)*R*Real.cos (x 0)) • proj 0) + ((-R*Real.sin (x 0)) • proj 1), H • proj 1]
  have hd : HasFDerivAt (cone R H)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp A) x := by
    apply (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp x
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert ((((hasFDerivAt_const (1 : ℝ) x).sub (proj 1).hasFDerivAt).mul_const R).mul
        ((Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x (proj 0).hasFDerivAt)) using 1 <;>
        ext h <;> simp [A, proj] <;> ring
    · convert ((((hasFDerivAt_const (1 : ℝ) x).sub (proj 1).hasFDerivAt).mul_const R).mul
        ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x (proj 0).hasFDerivAt)) using 1 <;>
        ext h <;> simp [A, proj] <;> ring
    · convert (proj 1).hasFDerivAt.mul_const H using 1 <;>
        ext h <;> simp [A, proj] <;> ring
  rw [hd.fderiv]
  constructor <;> ext i <;> fin_cases i <;>
    simp [columns, PatchGeometryGram.columns, Specs.D04.C10.PatchGeometryGram.columnsValue,
      Specs.D04.C10.PatchGeometryGram.Model.columns, proj, A,
      Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

lemma cylinder_cross (R : ℝ) (x : E 2) :
    cross (columns (fderiv ℝ (cylinder R) x).toLinearMap 0)
      (columns (fderiv ℝ (cylinder R) x).toLinearMap 1) =
      WithLp.toLp 2 ![R*Real.cos (x 0), R*Real.sin (x 0), 0] := by
  rw [(cylinder_columns R x).1, (cylinder_columns R x).2]
  ext i
  fin_cases i <;> simp [cross, PatchGeometryGram.cross,
    Specs.D04.C10.PatchGeometryGram.crossValue, Specs.D04.C10.PatchGeometryGram.Model.cross,
    crossProduct] <;> ring

lemma cone_cross (R H : ℝ) (x : E 2) :
    cross (columns (fderiv ℝ (cone R H) x).toLinearMap 0)
      (columns (fderiv ℝ (cone R H) x).toLinearMap 1) =
      WithLp.toLp 2 ![(1-x 1)*R*H*Real.cos (x 0),
        (1-x 1)*R*H*Real.sin (x 0), (1-x 1)*R^2] := by
  rw [(cone_columns R H x).1, (cone_columns R H x).2]
  ext i
  fin_cases i <;> simp [cross, PatchGeometryGram.cross,
    Specs.D04.C10.PatchGeometryGram.crossValue, Specs.D04.C10.PatchGeometryGram.Model.cross,
    crossProduct] <;> try ring
  linear_combination (1-x 1)*R^2*(Real.sin_sq_add_cos_sq (x 0))

lemma cylinder_density (R : ℝ) (hR : 0 < R) (x : E 2) :
    patchJacobian (cylinder R) x = R := by
  rw [show patchJacobian (cylinder R) x = _ from gram_cross _, cylinder_cross]
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  change Real.sqrt ((R*Real.cos (x 0))^2 + (R*Real.sin (x 0))^2 + 0^2) = R
  rw [pow_two (0 : ℝ), mul_zero, add_zero]
  rw [show (R * Real.cos (x 0))^2 + (R * Real.sin (x 0))^2 = R^2 by
    linear_combination R^2*(Real.sin_sq_add_cos_sq (x 0))]
  exact Real.sqrt_sq hR.le

lemma cone_density (R H : ℝ) (hR : 0 < R) (x : E 2) (ht : x 1 ≤ 1) :
    patchJacobian (cone R H) x = R*(1-x 1)*Real.sqrt (R^2+H^2) := by
  rw [show patchJacobian (cone R H) x = _ from gram_cross _, cone_cross]
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  change Real.sqrt (((1-x 1)*R*H*Real.cos (x 0))^2 +
    ((1-x 1)*R*H*Real.sin (x 0))^2 + ((1-x 1)*R^2)^2) = _
  have hs := Real.sin_sq_add_cos_sq (x 0)
  have he : ((1-x 1)*R*H*Real.cos (x 0))^2 +
      ((1-x 1)*R*H*Real.sin (x 0))^2 + ((1-x 1)*R^2)^2 =
        (R*(1-x 1))^2*(R^2+H^2) := by linear_combination ((1-x 1)*R*H)^2*hs
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hR.le (sub_nonneg.mpr ht))]

lemma cylinder_regular (R : ℝ) (hR : 0 < R) : RegularPatch univ (cylinder R) := by
  refine ⟨isOpen_univ, (cylinder_contDiff R).contDiffOn, fun x _ => ?_⟩
  apply (cross_rank _).mp
  intro hz
  have hj := cylinder_density R hR x
  have hn : patchJacobian (cylinder R) x = 0 := (gram_cross _).trans (by rw [hz, norm_zero])
  linarith

lemma cone_regular (R H : ℝ) (hR : 0 < R) :
    RegularPatch {x | x 1 < 1} (cone R H) := by
  refine ⟨isOpen_lt (by fun_prop) continuous_const,
    (cone_contDiff R H).contDiffOn, fun x hx => ?_⟩
  apply (cross_rank _).mp
  intro hz
  have hn : patchJacobian (cone R H) x = 0 := (gram_cross _).trans (by rw [hz, norm_zero])
  have hp : 0 < R*(1-x 1)*Real.sqrt (R^2+H^2) :=
    mul_pos (mul_pos hR (sub_pos.mpr hx)) (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg H]))
  rw [cone_density R H hR x hx.le] at hn
  linarith

lemma cone_apex (R H s : ℝ) :
    cone R H (WithLp.toLp 2 ![s, 1]) = WithLp.toLp 2 ![0, 0, H] ∧
    ¬ Function.Injective (fderiv ℝ (cone R H) (WithLp.toLp 2 ![s, 1])) := by
  constructor
  · ext i; fin_cases i <;> simp [cone]
  · intro hi
    have hc := (cone_columns R H (WithLp.toLp 2 ![s, 1])).1
    have hz : columns (fderiv ℝ (cone R H) (WithLp.toLp 2 ![s, 1])).toLinearMap 0 = 0 := by
      rw [hc]; ext i; fin_cases i <;> simp
    have he : (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 2) 0 = 0 := hi (by
      simpa [columns, PatchGeometryGram.columns, Specs.D04.C10.PatchGeometryGram.columnsValue,
        Specs.D04.C10.PatchGeometryGram.Model.columns] using hz)
    have := congrArg (fun v : E 2 => v 0) he
    simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply,
      PiLp.single_apply] at this

private def intervalSet (l r : ℝ) : Set (E 1) := {x | x 0 ∈ Icc l r}

private lemma intervalSet_between (l r : ℝ) : intervalSet l r =
    SlicingAndMoments.between (univ : Set (E 0)) (fun _ => l) (fun _ => r) := by
  ext x
  simp [intervalSet, SlicingAndMoments.between,
    Specs.D04.C06.SlicingAndMoments.Model.between,
    Specs.D04.C06.SlicingAndMoments.Model.height]

private lemma intervalSet_jordan (l r : ℝ) (hlr : l ≤ r) : Jordan (intervalSet l r) := by
  rw [intervalSet_between]
  exact SlicingAndMoments.between_jordan _ (JordanRegions.zero_dimension univ).1
    _ _ continuousOn_const continuousOn_const (fun _ _ => hlr)

private lemma intervalSet_volume (l r : ℝ) (hlr : l ≤ r) :
    volume (intervalSet l r) = r-l := by
  rw [intervalSet_between]
  have hv := (SlicingAndMoments.between_volume (univ : Set (E 0)) (fun _ => l) (fun _ => r)
    (JordanRegions.zero_dimension univ).1 continuousOn_const continuousOn_const
    (fun _ _ => hlr)).2
  exact hv.trans (by simpa using
    (SlicingAndMoments.base_zero_evaluation (univ : Set (E 0)) (fun _ => r-l)).2)

lemma rectangle_between (l r a b : ℝ) : rectangle l r a b =
    SlicingAndMoments.between (intervalSet l r) (fun _ => a) (fun _ => b) := by
  ext x
  simp [rectangle, SlicingAndMoments.between, intervalSet,
    Specs.D04.C06.SlicingAndMoments.Model.between,
    Specs.D04.C06.SlicingAndMoments.Model.basePoint,
    Specs.D04.C06.SlicingAndMoments.Model.height]

lemma rectangle_jordan (l r a b : ℝ) (hlr : l ≤ r) (hab : a ≤ b) :
    Jordan (rectangle l r a b) := by
  rw [rectangle_between]
  exact SlicingAndMoments.between_jordan _ (intervalSet_jordan l r hlr)
    _ _ continuousOn_const continuousOn_const (fun _ _ => hab)

lemma rectangle_compact (l r a b : ℝ) (hlr : l ≤ r) (hab : a ≤ b) :
    IsCompact (rectangle l r a b) := by
  let Q : Darboux.Box 2 := ⟨WithLp.toLp 2 ![l,a], WithLp.toLp 2 ![r,b], by
    intro i; fin_cases i <;> assumption⟩
  have he : rectangle l r a b = Darboux.carrier Q := by
    ext x
    constructor
    · rintro ⟨hx,hy⟩ i
      fin_cases i <;> assumption
    · intro hx
      exact ⟨hx 0, hx 1⟩
  rw [he]
  exact D04.DiscontinuityCriterion.carrier_compact Q

private lemma region_constant {n : ℕ} (hn : 0 < n) {S : Set (E n)} (hS : Jordan S) (c : ℝ) :
    RegionIntegrable (fun _ : S => c) ∧ regionIntegral (fun _ : S => c) = c*volume S := by
  have hi := integrable_continuous_on_closure hn hS (fun _ => (1 : ℝ)) continuous_const
  have hs := SlicingAndMoments.region_smul (jordan_bounded hS) (fun _ : S => (1 : ℝ)) hi c
  simpa only [mul_one, regionIntegral_one] using hs

private lemma affine_interval (a b c d : ℝ) (hab : a ≤ b) :
    Darboux.lowerIntegral (fun y : E 1 => c+d*y 0) (Darboux.intervalBox a b hab) =
      c*(b-a)+d*(b^2-a^2)/2 := by
  have hi := SlicingAndMoments.continuous_box_integrable (fun y : E 1 => c+d*y 0)
    (by fun_prop) (Darboux.intervalBox a b hab)
  obtain ⟨hs, hv⟩ := (Darboux.scalar_integral (fun y : E 1 => c+d*y 0) a b hab).2 hi
  change Darboux.lowerIntegral _ _ = SingleVariableAnalysis.Riemann.realIntegral (fun t => c+d*t) hs at hv
  rw [hv]
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => c*t+d*t^2/2) (c+d*t) t := by
    convert ((hasDerivAt_id t).const_mul c).add
      ((((hasDerivAt_id t).pow 2).const_mul d).div_const 2) using 1
    · funext y; dsimp <;> ring
    · dsimp <;> ring
  have ht := SingleVariableAnalysis.Riemann.real_ftc_second
    (fun t : ℝ => c*t+d*t^2/2) (fun t => c+d*t) a b hab
    (by fun_prop) (fun t _ => hd t) hs
  exact ht.trans (by ring)

lemma rectangle_affine_integral (l r a b c d : ℝ) (hlr : l ≤ r) (hab : a ≤ b) :
    RegionIntegrable (fun x : rectangle l r a b => c+d*(x : E 2) 1) ∧
    regionIntegral (fun x : rectangle l r a b => c+d*(x : E 2) 1) =
      (r-l)*(c*(b-a)+d*(b^2-a^2)/2) := by
  rw [rectangle_between]
  obtain ⟨hi, _, hout, hv⟩ := (SlicingAndMoments.slicing (intervalSet l r)
    (fun _ => a) (fun _ => b) (intervalSet_jordan l r hlr)
    continuousOn_const continuousOn_const (fun _ _ => hab)).2.2
    (fun x : E 2 => c+d*x 1) (by fun_prop)
  refine ⟨hi, hv.trans ?_⟩
  have he : (fun x : intervalSet l r => SlicingAndMoments.sliceIntegral (fun _ => a)
      (fun _ => b) (fun z : E 2 => c+d*z 1) x) =
      (fun _ => c*(b-a)+d*(b^2-a^2)/2) := by
    funext x
    change Darboux.lowerIntegral (fun y => c+d*(Darboux.productPoint (x : E 1) y) 1)
      (SlicingAndMoments.sliceBox (fun _ => a) (fun _ => b) (x : E 1)) = _
    rw [SlicingAndMoments.sliceBox_eq_interval (fun _ : E 1 => a) (fun _ => b) (x : E 1) hab]
    have hh (y : E 1) : Darboux.productPoint (x : E 1) y 1 = y 0 :=
      Darboux.Fubini.blockPoint_right finSumFinEquiv (x : E 1) y 0
    simp_rw [hh]
    exact affine_interval a b c d hab
  rw [he, (region_constant (by decide : 0 < 1) (intervalSet_jordan l r hlr) _).2,
    intervalSet_volume l r hlr]
  ring

lemma cylinder_rectangle_area (R H l r : ℝ) (hR : 0 < R) (hH : 0 ≤ H) (hlr : l ≤ r) :
    AreaIntegrable (rectangle l r 0 H) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (rectangle l r 0 H) (cylinder R) = (r-l)*R*H := by
  have he : areaIntegrand (rectangle l r 0 H) (cylinder R) (fun _ => 1) =
      (fun _ => R) := by funext x; change 1 * patchJacobian _ _ = _; rw [one_mul, cylinder_density R hR]
  have ha := rectangle_affine_integral l r 0 H R 0 hlr hH
  simp only [zero_mul, add_zero, zero_div, sub_zero] at ha
  constructor
  · refine ⟨⟨1, by intro x; norm_num⟩, ?_⟩
    change RegionIntegrable (areaIntegrand _ _ _)
    rw [he]
    exact ha.1
  · change regionIntegral (areaIntegrand _ _ _) = _
    rw [he, ha.2]
    ring

lemma cylinder_area (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H) :
    AreaIntegrable (rectangle 0 (2*Real.pi) 0 H) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) 0 H) (cylinder R) = 2*Real.pi*R*H := by
  simpa only [sub_zero] using cylinder_rectangle_area R H 0 (2*Real.pi) hR hH (by positivity)

lemma cone_rectangle_area (R H l r a b : ℝ) (hR : 0 < R)
    (hlr : l ≤ r) (hab : a ≤ b) (hb : b ≤ 1) :
    AreaIntegrable (rectangle l r a b) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle l r a b) (cone R H) =
      (r-l)*R*Real.sqrt (R^2+H^2)*((b-a)-(b^2-a^2)/2) := by
  let C := R*Real.sqrt (R^2+H^2)
  have he : areaIntegrand (rectangle l r a b) (cone R H) (fun _ => 1) =
      (fun x : rectangle l r a b => C+(-C)*(x : E 2) 1) := by
    funext x
    change 1 * patchJacobian _ _ = _
    rw [one_mul, cone_density R H hR x (x.property.2.2.trans hb)]
    dsimp [C]; ring
  have ha := rectangle_affine_integral l r a b C (-C) hlr hab
  constructor
  · refine ⟨⟨1, by intro x; norm_num⟩, ?_⟩
    change RegionIntegrable (areaIntegrand _ _ _)
    rw [he]
    exact ha.1
  · change regionIntegral (areaIntegrand _ _ _) = _
    rw [he, ha.2]
    dsimp [C]; ring

lemma cone_area (R H : ℝ) (hR : 0 < R) :
    AreaIntegrable (rectangle 0 (2*Real.pi) 0 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) 0 1) (cone R H) =
      Real.pi*R*Real.sqrt (R^2+H^2) := by
  obtain ⟨hi,hv⟩ := cone_rectangle_area R H 0 (2*Real.pi) 0 1 hR (by positivity) (by norm_num) le_rfl
  exact ⟨hi, hv.trans (by ring)⟩

lemma cone_apex_cap (R H ε : ℝ) (hR : 0 < R) (hε : 0 ≤ ε) :
    AreaIntegrable (rectangle 0 (2*Real.pi) (1-ε) 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) (1-ε) 1) (cone R H) =
      Real.pi*R*Real.sqrt (R^2+H^2)*ε^2 := by
  obtain ⟨hi,hv⟩ := cone_rectangle_area R H 0 (2*Real.pi) (1-ε) 1 hR
    (by positivity) (by linarith) le_rfl
  exact ⟨hi, hv.trans (by ring)⟩

lemma cone_apex_zero_area (R H : ℝ) (hR : 0 < R) :
    AreaIntegrable (rectangle 0 (2*Real.pi) 1 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 (2*Real.pi) 1 1) (cone R H) = 0 := by
  obtain ⟨hi,hv⟩ := cone_rectangle_area R H 0 (2*Real.pi) 1 1 hR (by positivity) le_rfl le_rfl
  exact ⟨hi, hv.trans (by ring)⟩

private lemma angle_injective {s t : ℝ} (hs : s ∈ Ioo 0 (2*Real.pi))
    (ht : t ∈ Ioo 0 (2*Real.pi))
    (hc : Real.cos s = Real.cos t) (hi : Real.sin s = Real.sin t) : s = t := by
  letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2*Real.pi)
    (a := 0) (x := s) (y := t) (by simpa using ⟨hs.1.le, hs.2⟩)
      (by simpa using ⟨ht.1.le, ht.2⟩)).mp
  exact Real.Angle.cos_sin_inj hc hi

lemma cylinder_injective (R : ℝ) (hR : 0 < R) :
    InjOn (cylinder R) {x | x 0 ∈ Ioo 0 (2*Real.pi)} := by
  intro x hx y hy hxy
  have hc := congrArg (fun v : E 3 => v 0) hxy
  have hs := congrArg (fun v : E 3 => v 1) hxy
  have ht := congrArg (fun v : E 3 => v 2) hxy
  change R*Real.cos (x 0) = R*Real.cos (y 0) at hc
  change R*Real.sin (x 0) = R*Real.sin (y 0) at hs
  change x 1 = y 1 at ht
  have hst := angle_injective hx hy ((mul_left_cancel₀ hR.ne') hc) ((mul_left_cancel₀ hR.ne') hs)
  ext i
  fin_cases i <;> assumption

lemma cone_injective (R H : ℝ) (hR : 0 < R) :
    InjOn (cone R H) {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 < 1} := by
  intro x hx y hy hxy
  have hc := congrArg (fun v : E 3 => v 0) hxy
  have hs := congrArg (fun v : E 3 => v 1) hxy
  change (1-x 1)*R*Real.cos (x 0) = (1-y 1)*R*Real.cos (y 0) at hc
  change (1-x 1)*R*Real.sin (x 0) = (1-y 1)*R*Real.sin (y 0) at hs
  have hp : 0 < (1-x 1)*R := mul_pos (sub_pos.mpr hx.2) hR
  have hq : 0 < (1-y 1)*R := mul_pos (sub_pos.mpr hy.2) hR
  have he : ((1-x 1)*R)^2 = ((1-y 1)*R)^2 := by
    calc
      _ = ((1-x 1)*R*Real.cos (x 0))^2 + ((1-x 1)*R*Real.sin (x 0))^2 := by
        linear_combination -((1-x 1)*R)^2*(Real.sin_sq_add_cos_sq (x 0))
      _ = ((1-y 1)*R*Real.cos (y 0))^2 + ((1-y 1)*R*Real.sin (y 0))^2 := by rw [hc,hs]
      _ = _ := by linear_combination ((1-y 1)*R)^2*(Real.sin_sq_add_cos_sq (y 0))
  have hep : (1-x 1)*R = (1-y 1)*R := (sq_eq_sq₀ hp.le hq.le).mp he
  have ht : x 1 = y 1 := by nlinarith
  rw [ht] at hc hs
  have hst := angle_injective hx.1 hy.1 ((mul_left_cancel₀ hq.ne') hc) ((mul_left_cancel₀ hq.ne') hs)
  ext i
  fin_cases i <;> assumption

lemma cylinder_truncation (R H δ : ℝ) (hR : 0 < R) (hH : 0 ≤ H)
    (hδ : 0 < δ) (hπ : δ < Real.pi) :
    IsCompact (cylinderTruncation H δ) ∧ Jordan (cylinderTruncation H δ) ∧
    InjOn (cylinder R) (cylinderTruncation H δ) ∧
    AreaIntegrable (cylinderTruncation H δ) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (cylinderTruncation H δ) (cylinder R) =
      (2*Real.pi-2*δ)*R*H := by
  have hlr : δ ≤ 2*Real.pi-δ := by linarith
  refine ⟨rectangle_compact _ _ _ _ hlr hH, rectangle_jordan _ _ _ _ hlr hH,
    (cylinder_injective R hR).mono ?_, ?_⟩
  · intro x hx
    exact ⟨hδ.trans_le hx.1.1, by linarith [hx.1.2]⟩
  · obtain ⟨hi,hv⟩ := cylinder_rectangle_area R H δ (2*Real.pi-δ) hR hH hlr
    exact ⟨hi, hv.trans (by ring)⟩

lemma cone_truncation (R H δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (hπ : δ < Real.pi) (h1 : δ < 1) :
    IsCompact (coneTruncation δ) ∧ Jordan (coneTruncation δ) ∧
    (coneTruncation δ ⊆ {x | x 1 < 1}) ∧
    InjOn (cone R H) (coneTruncation δ) ∧
    AreaIntegrable (coneTruncation δ) (cone R H) (fun _ => 1) ∧
    parametrizedArea (coneTruncation δ) (cone R H) =
      (2*Real.pi-2*δ)*R*Real.sqrt (R^2+H^2)*((1-δ)-(1-δ)^2/2) := by
  have hlr : δ ≤ 2*Real.pi-δ := by linarith
  have hab : 0 ≤ 1-δ := by linarith
  refine ⟨rectangle_compact _ _ _ _ hlr hab, rectangle_jordan _ _ _ _ hlr hab,
    ?_, (cone_injective R H hR).mono ?_, ?_⟩
  · intro x hx
    change x 1 < 1
    linarith [hx.2.2]
  · intro x hx
    exact ⟨⟨hδ.trans_le hx.1.1, by linarith [hx.1.2]⟩, by linarith [hx.2.2]⟩
  · obtain ⟨hi,hv⟩ := cone_rectangle_area R H δ (2*Real.pi-δ) 0 (1-δ) hR hlr hab (by linarith)
    exact ⟨hi, hv.trans (by ring)⟩

lemma cylinder_area_limit (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H) :
    Tendsto (fun δ => parametrizedArea (cylinderTruncation H δ) (cylinder R))
      (𝓝[>] (0 : ℝ)) (𝓝 (2*Real.pi*R*H)) := by
  have ht : Tendsto (fun δ : ℝ => (2*Real.pi-2*δ)*R*H) (𝓝 0)
      (𝓝 (2*Real.pi*R*H)) := by
    have hc : Continuous (fun δ : ℝ => (2*Real.pi-2*δ)*R*H) := by fun_prop
    simpa using hc.tendsto 0
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  have hu : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < Real.pi :=
    (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hu] with δ hδ hπ
  exact (cylinder_truncation R H δ hR hH hδ hπ).2.2.2.2.symm

lemma cone_area_limit (R H : ℝ) (hR : 0 < R) :
    Tendsto (fun δ => parametrizedArea (coneTruncation δ) (cone R H))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi*R*Real.sqrt (R^2+H^2))) := by
  have ht : Tendsto (fun δ : ℝ => (2*Real.pi-2*δ)*R*Real.sqrt (R^2+H^2)*
      ((1-δ)-(1-δ)^2/2)) (𝓝 0) (𝓝 (Real.pi*R*Real.sqrt (R^2+H^2))) := by
    have hc : Continuous (fun δ : ℝ => (2*Real.pi-2*δ)*R*Real.sqrt (R^2+H^2)*
      ((1-δ)-(1-δ)^2/2)) := by fun_prop
    convert hc.tendsto 0 using 1 <;> ring
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  have hu : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < min Real.pi 1 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < min Real.pi 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hu] with δ hδ hu
  exact (cone_truncation R H δ hR hδ (lt_min_iff.mp hu).1 (lt_min_iff.mp hu).2).2.2.2.2.2.symm

lemma cylinder_seam_area (R H : ℝ) (hR : 0 < R) (hH : 0 ≤ H) :
    cylinder R '' rectangle 0 0 0 H = cylinderSeam R H ∧
    AreaIntegrable (rectangle 0 0 0 H) (cylinder R) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 0 0 H) (cylinder R) = 0 := by
  constructor
  · ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hs : x 0 = 0 := le_antisymm hx.1.2 hx.1.1
      refine ⟨x 1, hx.2, ?_⟩
      ext i; fin_cases i <;> simp [cylinder, hs]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨WithLp.toLp 2 ![0,t], ⟨⟨le_rfl,le_rfl⟩,ht⟩, ?_⟩
      ext i; fin_cases i <;> simp [cylinder]
  · obtain ⟨hi,hv⟩ := cylinder_rectangle_area R H 0 0 hR hH le_rfl
    exact ⟨hi, hv.trans (by ring)⟩

lemma cone_seam_area (R H : ℝ) (hR : 0 < R) :
    cone R H '' rectangle 0 0 0 1 = coneSeam R H ∧
    AreaIntegrable (rectangle 0 0 0 1) (cone R H) (fun _ => 1) ∧
    parametrizedArea (rectangle 0 0 0 1) (cone R H) = 0 := by
  constructor
  · ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hs : x 0 = 0 := le_antisymm hx.1.2 hx.1.1
      refine ⟨x 1, hx.2, ?_⟩
      ext i; fin_cases i <;> simp [cone, hs]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨WithLp.toLp 2 ![0,t], ⟨⟨le_rfl,le_rfl⟩,ht⟩, ?_⟩
      ext i; fin_cases i <;> simp [cone]
  · obtain ⟨hi,hv⟩ := cone_rectangle_area R H 0 0 0 1 hR le_rfl (by norm_num) le_rfl
    exact ⟨hi, hv.trans (by ring)⟩

lemma cylinder_seam_endpoints (R t : ℝ) :
    cylinder R (WithLp.toLp 2 ![0,t]) = cylinder R (WithLp.toLp 2 ![2*Real.pi,t]) := by
  ext i; fin_cases i <;> simp [cylinder]

lemma cone_seam_endpoints (R H t : ℝ) :
    cone R H (WithLp.toLp 2 ![0,t]) = cone R H (WithLp.toLp 2 ![2*Real.pi,t]) := by
  ext i; fin_cases i <;> simp [cone]

lemma cylinder_seam_compact_curve (R H : ℝ) (hH : 0 ≤ H) :
    IsCompact (cylinderSeam R H) ∧ Specs.D04.C10.NegligibleSeams.Model.FiniteSeam (cylinderSeam R H) := by
  let γ : Specs.D04.C10.NegligibleSeams.Model.CompactCurve 3 :=
    ⟨0,H,hH,fun t => WithLp.toLp 2 ![R,0,t], by
      apply ContDiff.contDiffOn
      apply (contDiff_piLp 2).mpr
      intro i; fin_cases i <;> dsimp <;> fun_prop⟩
  have he : Specs.D04.C10.NegligibleSeams.Model.curveTrace γ = cylinderSeam R H := rfl
  refine ⟨he ▸ NegligibleSeams.curveTrace_compact γ, ?_⟩
  refine ⟨1, fun _ => γ, ∅, ?_⟩
  simp only [Finset.coe_empty, union_empty]
  rw [iUnion_const]
  exact he.symm

lemma cone_seam_compact_curve (R H : ℝ) :
    IsCompact (coneSeam R H) ∧ Specs.D04.C10.NegligibleSeams.Model.FiniteSeam (coneSeam R H) := by
  let γ : Specs.D04.C10.NegligibleSeams.Model.CompactCurve 3 :=
    ⟨0,1,by norm_num,fun t => WithLp.toLp 2 ![(1-t)*R,0,t*H], by
      apply ContDiff.contDiffOn
      apply (contDiff_piLp 2).mpr
      intro i; fin_cases i <;> dsimp <;> fun_prop⟩
  have he : Specs.D04.C10.NegligibleSeams.Model.curveTrace γ = coneSeam R H := rfl
  refine ⟨he ▸ NegligibleSeams.curveTrace_compact γ, ?_⟩
  refine ⟨1, fun _ => γ, ∅, ?_⟩
  simp only [Finset.coe_empty, union_empty]
  rw [iUnion_const]
  exact he.symm

private lemma compact_positive_lower_bound {K : Set (E 2)} (hK : IsCompact K)
    (f : E 2 → ℝ) (hf : Continuous f) (hp : ∀ x ∈ K, 0 < f x) :
    ∃ η > 0, ∀ x ∈ K, η ≤ f x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMinOn hne hf.continuousOn
    exact ⟨f x, hp x hx, fun y hy => hm hy⟩
  · exact ⟨1, by norm_num, fun x hx => (hne ⟨x,hx⟩).elim⟩

/-- Compact cofinality in the single-traversal parameter strip. -/
lemma cylinder_truncations_cofinal (H : ℝ) (K : Set (E 2)) (hK : IsCompact K)
    (hsub : K ⊆ {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Icc 0 H}) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, K ⊆ cylinderTruncation H δ := by
  obtain ⟨η,hη,hm⟩ := compact_positive_lower_bound hK
    (fun x => min (x 0) (2*Real.pi-x 0)) (by fun_prop) (by
      intro x hx
      have h := hsub hx
      exact lt_min h.1.1 (sub_pos.mpr h.1.2))
  have hu : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < η :=
    (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds
  filter_upwards [hu] with δ hδ x hx
  have h := le_min_iff.mp (hm x hx)
  exact ⟨⟨hδ.le.trans h.1, by linarith [h.2]⟩, (hsub hx).2⟩

lemma cone_truncations_cofinal (K : Set (E 2)) (hK : IsCompact K)
    (hsub : K ⊆ {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Ico 0 1}) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, K ⊆ coneTruncation δ := by
  obtain ⟨η,hη,hm⟩ := compact_positive_lower_bound hK
    (fun x => min (min (x 0) (2*Real.pi-x 0)) (1-x 1)) (by fun_prop) (by
      intro x hx
      have h := hsub hx
      exact lt_min (lt_min h.1.1 (sub_pos.mpr h.1.2)) (sub_pos.mpr h.2.2))
  have hu : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < η :=
    (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds
  filter_upwards [hu] with δ hδ x hx
  have h := le_min_iff.mp (hm x hx)
  have hs := le_min_iff.mp h.1
  exact ⟨⟨hδ.le.trans hs.1, by linarith [hs.2]⟩, ⟨(hsub hx).2.1, by linarith [h.2]⟩⟩

lemma cylinder_complement_covered (R H : ℝ) :
    cylinder R '' rectangle 0 (2*Real.pi) 0 H \ cylinderSeam R H ⊆
      cylinder R '' {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Icc 0 H} := by
  rintro v ⟨⟨x,hx,rfl⟩,hnot⟩
  have h0 : x 0 ≠ 0 := by
    intro he
    apply hnot
    refine ⟨x 1,hx.2,?_⟩
    ext i; fin_cases i <;> simp [cylinder,he]
  have h2 : x 0 ≠ 2*Real.pi := by
    intro he
    apply hnot
    refine ⟨x 1,hx.2,?_⟩
    ext i; fin_cases i <;> simp [cylinder,he]
  exact ⟨x,⟨⟨lt_of_le_of_ne hx.1.1 (Ne.symm h0),lt_of_le_of_ne hx.1.2 h2⟩,hx.2⟩,rfl⟩

lemma cone_complement_covered (R H : ℝ) :
    cone R H '' rectangle 0 (2*Real.pi) 0 1 \ coneSeam R H ⊆
      cone R H '' {x | x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 ∈ Ico 0 1} := by
  rintro v ⟨⟨x,hx,rfl⟩,hnot⟩
  have h0 : x 0 ≠ 0 := by
    intro he
    apply hnot
    refine ⟨x 1,hx.2,?_⟩
    ext i; fin_cases i <;> simp [cone,he]
  have h2 : x 0 ≠ 2*Real.pi := by
    intro he
    apply hnot
    refine ⟨x 1,hx.2,?_⟩
    ext i; fin_cases i <;> simp [cone,he]
  have h1 : x 1 ≠ 1 := by
    intro he
    apply hnot
    refine ⟨1,⟨by norm_num,le_rfl⟩,?_⟩
    ext i; fin_cases i <;> simp [cone,he]
  exact ⟨x,⟨⟨lt_of_le_of_ne hx.1.1 (Ne.symm h0),lt_of_le_of_ne hx.1.2 h2⟩,
    ⟨hx.2.1,lt_of_le_of_ne hx.2.2 h1⟩⟩,rfl⟩

/-- The single-traversal strips really omit the geometric seams. -/
lemma cylinder_strip_avoids_seam (R H : ℝ) (hR : 0 < R) (x : E 2)
    (hx : x 0 ∈ Ioo 0 (2*Real.pi)) : cylinder R x ∉ cylinderSeam R H := by
  rintro ⟨t, _, he⟩
  have hc := congrArg (fun v : E 3 => v 0) he
  change R = R * Real.cos (x 0) at hc
  have hcos : Real.cos (x 0) = 1 := by nlinarith
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hx.1]) hx.2).mp hcos
  linarith [hx.1]

lemma cone_strip_avoids_seam (R H : ℝ) (hR : 0 < R) (x : E 2)
    (hx : x 0 ∈ Ioo 0 (2*Real.pi) ∧ x 1 < 1) : cone R H x ∉ coneSeam R H := by
  rintro ⟨t, ht, he⟩
  have hc := congrArg (fun v : E 3 => v 0) he
  have hs := congrArg (fun v : E 3 => v 1) he
  change (1-t)*R = (1-x 1)*R*Real.cos (x 0) at hc
  change 0 = (1-x 1)*R*Real.sin (x 0) at hs
  have hp : 0 < (1-x 1)*R := mul_pos (sub_pos.mpr hx.2) hR
  have hsin : Real.sin (x 0) = 0 := (mul_eq_zero.mp hs.symm).resolve_left hp.ne'
  have hcos_nonneg : 0 ≤ Real.cos (x 0) := by
    have hn : 0 ≤ (1-t)*R := mul_nonneg (sub_nonneg.mpr ht.2) hR.le
    rw [hc] at hn
    exact nonneg_of_mul_nonneg_right hn hp
  have hcos : Real.cos (x 0) = 1 := by
    have hi := Real.sin_sq_add_cos_sq (x 0)
    rw [hsin] at hi
    nlinarith
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hx.1.1]) hx.1.2).mp hcos
  linarith [hx.1.1]

lemma cylinder_truncation_avoids_seam (R H δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) :
    cylinder R '' cylinderTruncation H δ ⊆
      cylinder R '' rectangle 0 (2*Real.pi) 0 H \ cylinderSeam R H := by
  rintro v ⟨x,hx,rfl⟩
  have hs : x 0 ∈ Ioo 0 (2*Real.pi) := ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  exact ⟨⟨x,⟨⟨hs.1.le, hs.2.le⟩,hx.2⟩,rfl⟩, cylinder_strip_avoids_seam R H hR x hs⟩

lemma cone_truncation_avoids_seam (R H δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) :
    cone R H '' coneTruncation δ ⊆
      cone R H '' rectangle 0 (2*Real.pi) 0 1 \ coneSeam R H := by
  rintro v ⟨x,hx,rfl⟩
  have hs : x 0 ∈ Ioo 0 (2*Real.pi) := ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  have ht : x 1 < 1 := by linarith [hx.2.2]
  exact ⟨⟨x,⟨⟨hs.1.le,hs.2.le⟩,⟨hx.2.1,ht.le⟩⟩,rfl⟩,
    cone_strip_avoids_seam R H hR x ⟨hs,ht⟩⟩

lemma cone_apex_cap_limit (R H : ℝ) (hR : 0 < R) :
    Tendsto (fun ε => parametrizedArea (rectangle 0 (2*Real.pi) (1-ε) 1) (cone R H))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht : Tendsto (fun ε : ℝ => Real.pi*R*Real.sqrt (R^2+H^2)*ε^2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => Real.pi*R*Real.sqrt (R^2+H^2)*ε^2) := by fun_prop
    simpa using hc.tendsto 0
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (cone_apex_cap R H ε hR hε.le).2.symm

lemma cone_disk_limit (R : ℝ) (hR : 0 < R) :
    Tendsto (fun δ => parametrizedArea (coneTruncation δ) (cone R 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi*R^2)) := by
  have h := cone_area_limit R 0 hR
  have he : Real.pi*R*Real.sqrt (R^2+(0 : ℝ)^2) = Real.pi*R^2 := by
    rw [zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq hR.le]
    ring
  rwa [he] at h

end D04.RuledAreas
