import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.DiskHemisphereAndBoxSigns
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OutwardFirstBoundaryOrientation
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.D04.C15.BoundarySquaredAndFaceSigns
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Concrete orientation examples, paper.tex d04:12:signs.
The disk and hemisphere conormals are certified by explicit half-space charts.
Rotations carry the charts to every equatorial point. Cross-product frames
identify the outward-first signs; a single-traversal equator cell supplies the
cancelling proper integrals. Affine box faces retain the free-coordinate order
and use the cell theorem at corners. -/

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace BigOperators ContDiff
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.SignExamples
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C12.DiskHemisphereAndBoxSigns
open Model

-- Expand directly to the canonical upstream objects; these introduce no new definitions.
local notation "Eucl" => Specs.D04.C01.EuclideanInterfaces.Model.E
local notation "stdBasis" => Specs.D04.C01.EuclideanInterfaces.Model.standardBasis
local notation "coords" => Specs.D04.C01.EuclideanInterfaces.Model.coordinates

private lemma ext3 {x y : Eucl 3} (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) : x = y := by
  apply PiLp.ext
  intro i
  fin_cases i <;> assumption

private lemma norm_sq3 (x : Eucl 3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    star_trivial]
  norm_num [pow_two] <;> ring

private lemma inner3 (x y : Eucl 3) : ⟪x,y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, add_assoc]
  <;> ring

private lemma cross3 (x y : Eucl 3) : euclideanCross x y = WithLp.toLp 2
    ![x 1*y 2-x 2*y 1, x 2*y 0-x 0*y 2, x 0*y 1-x 1*y 0] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

private lemma basis3 (i : Fin 3) (j : Fin 3) :
    stdBasis 3 i j = if i = j then 1 else 0 := by
  simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

lemma equator_frame {R : ℝ} (hR : 0 < R) {x : Eucl 3} (hx : x ∈ equator R) :
    ‖radial R x‖ = 1 ∧ ‖ccw R x‖ = 1 ∧
    euclideanCross (stdBasis 3 2) (radial R x) = ccw R x ∧
    euclideanCross (radial R x) (ccw R x) = stdBasis 3 2 := by
  obtain ⟨hz,hs⟩ := hx
  have hn : ‖radial R x‖ ^ 2 = 1 := by
    rw [norm_sq3]
    simp only [radial, PiLp.smul_apply, smul_eq_mul, hz, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    field_simp
    nlinarith [hs]
  have ht : ‖ccw R x‖ ^ 2 = 1 := by
    rw [norm_sq3]
    simp only [ccw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
      WithLp.ofLp_toLp, zero_pow (by decide : 2 ≠ 0), add_zero]
    field_simp
    nlinarith [hs]
  refine ⟨by nlinarith [norm_nonneg (radial R x)],
    by nlinarith [norm_nonneg (ccw R x)], ?_, ?_⟩
  · apply ext3 <;> simp [cross3, basis3, radial, ccw, div_eq_mul_inv, mul_comm]
  · apply ext3
    · simp [cross3, radial, ccw, hz, basis3]
    · simp [cross3, radial, ccw, hz, basis3]
    · simp only [cross3, radial, ccw, PiLp.smul_apply, smul_eq_mul, basis3]
      simp
      field_simp
      nlinarith [hs]

theorem hemisphere_union : hemisphere_unionType := by
  intro R
  constructor
  · ext x
    simp only [hemisphere, mem_union, mem_ofPred_eq, ↓reduceIte]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total 0 (x 2) with hp | hn
      · exact Or.inl ⟨h,hp⟩
      · exact Or.inr ⟨h,hn⟩
  · ext x
    simp only [hemisphere, equator, mem_inter_iff, mem_ofPred_eq, ↓reduceIte]
    constructor
    · rintro ⟨⟨hs,hp⟩,⟨_,hn⟩⟩
      have hz : x 2 = 0 := le_antisymm hn hp
      exact ⟨hz, by simpa [hz] using hs⟩
    · rintro ⟨hz,hs⟩
      simp [hz, hs]


private lemma circle_basis (R θ : ℝ) : circle R θ =
    (R * Real.cos θ) • stdBasis 3 0 +
      (R * Real.sin θ) • stdBasis 3 1 := by
  apply ext3 <;> simp [circle, basis3]

lemma circle_derivative (R θ : ℝ) : HasDerivAt (circle R)
    ((-R * Real.sin θ) • stdBasis 3 0 +
      (R * Real.cos θ) • stdBasis 3 1) θ := by
  have h := (((Real.hasDerivAt_cos θ).const_mul R).smul_const (stdBasis 3 0)).add
      (((Real.hasDerivAt_sin θ).const_mul R).smul_const (stdBasis 3 1))
  convert h using 1
  · exact funext (circle_basis R)
  · module

theorem circle_traversal : circle_traversalType := by
  intro R hR
  have hn : R ≠ 0 := ne_of_gt hR
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    constructor
    · change (circle R θ) 2 = 0 ∧ _
      simp only [circle, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, WithLp.ofLp_toLp]
      exact ⟨trivial, by nlinarith [Real.cos_sq_add_sin_sq θ]⟩
    · convert circle_derivative R θ using 1
      apply ext3 <;> simp [basis3, ccw, circle, hn, mul_div_cancel_left₀] <;> field_simp <;> ring
  · intro x hx
    obtain ⟨hz,hs⟩ := hx
    let z : ℂ := ⟨x 0, x 1⟩
    have hnorm : ‖z‖ = R := by
      have hh := Complex.sq_norm z
      simp only [Complex.normSq_apply, z] at hh
      nlinarith [norm_nonneg z]
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hnorm ▸ hn)
    refine ⟨Complex.arg z, ?_⟩
    apply ext3
    · simp only [circle, Matrix.cons_val_zero, WithLp.ofLp_toLp]
      rw [Complex.cos_arg hz0, hnorm]
      exact mul_div_cancel₀ _ hn
    · simp only [circle, Matrix.cons_val_one, WithLp.ofLp_toLp]
      rw [Complex.sin_arg, hnorm]
      exact mul_div_cancel₀ _ hn
    · simpa [circle] using hz.symm
  · apply ext3 <;> simp [circle]

private def boxLinear {n : ℕ} (a b : Eucl n) : Eucl n →ₗ[ℝ] Eucl n where
  toFun u := WithLp.toLp 2 (fun i => (b i - a i) * u i)
  map_add' u v := by apply PiLp.ext; intro i; simp [mul_add]
  map_smul' t u := by apply PiLp.ext; intro i; simp [mul_comm, mul_left_comm]

private lemma boxMap_affine {n : ℕ} (a b : Eucl n) :
    boxMap a b = fun u => boxLinear a b u + a := by
  funext u
  apply PiLp.ext
  intro i
  simp [boxMap, boxLinear, add_comm]

private lemma boxMap_hasFDerivAt {n : ℕ} (a b : Eucl n) (u : Eucl n) :
    HasFDerivAt (boxMap a b) (boxLinear a b).toContinuousLinearMap u := by
  rw [boxMap_affine]
  exact (boxLinear a b).toContinuousLinearMap.hasFDerivAt.add_const a

theorem box_face_derivative : box_face_derivativeType := by
  intro k a b i upper u j
  have hf := (faceInsertion_contDiff i upper).differentiable (by simp)
  have hd := (boxMap_hasFDerivAt a b (faceInsertion i upper u)).comp u
    (hf u).hasFDerivAt
  change fderiv ℝ (boxFace a b i upper) u _ = _
  rw [show boxFace a b i upper = boxMap a b ∘ faceInsertion i upper from rfl,
    hd.fderiv]
  change boxLinear a b (Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (faceInsertion i upper) u (stdBasis k j)) = _
  have he : Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (faceInsertion i upper) u (stdBasis k j) =
      stdBasis (k+1) (i.succAbove j) :=
    D04.Cells.faceInsertion_derivative i upper u j
  rw [he]
  apply PiLp.ext
  intro l
  simp [boxLinear, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]
  split_ifs with h
  · subst l; simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply]
  · simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply, h, eq_comm]

private lemma coordinate_front (k : ℕ) (i : Fin (k+1)) (t : ℝ) :
    (stdBasis (k+1)).det
      (Fin.cons (t • stdBasis (k+1) i)
        (fun j : Fin k => stdBasis (k+1) (i.succAbove j))) = (-1 : ℝ)^i.val*t := by
  simpa only [D04.standardBasis, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis] using
    D04.Cells.coordinate_front_determinant i t

theorem box_face_signs : box_face_signsType := by
  intro k a b hab i upper u
  change
    let ν := if upper then stdBasis (k+1) i else -stdBasis (k+1) i
    let d := (stdBasis (k+1)).det
      (Fin.cons ν (fun j : Fin k => Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (boxFace a b i upper) u (stdBasis k j)))
    let s := if upper then (-1 : ℝ)^i.val else -(-1 : ℝ)^i.val
    d = s * ∏ j : Fin k, (b (i.succAbove j)-a (i.succAbove j)) ∧ Real.sign d = s
  dsimp only
  have hcol (j : Fin k) := box_face_derivative a b i upper u j
  simp_rw [hcol]
  let ν : Eucl (k+1) := if upper then stdBasis (k+1) i else -stdBasis (k+1) i
  let s : ℝ := if upper then (-1 : ℝ)^i.val else -(-1 : ℝ)^i.val
  have he : Fin.cons ν (fun j : Fin k =>
      (b (i.succAbove j) - a (i.succAbove j)) • stdBasis (k+1) (i.succAbove j)) =
      fun j : Fin (k+1) => (Fin.cons (α := fun _ => ℝ) 1 (fun j : Fin k => b (i.succAbove j) - a (i.succAbove j)) j) •
        (Fin.cons ν (fun j : Fin k => stdBasis (k+1) (i.succAbove j)) : Fin (k+1) → Eucl (k+1)) j := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  rw [he, AlternatingMap.map_smul_univ, Fin.prod_univ_succ]
  have hdet : (stdBasis (k+1)).det
      (Fin.cons ν (fun j : Fin k => stdBasis (k+1) (i.succAbove j))) = s := by
    cases upper
    · simpa only [ν,s,Bool.false_eq_true,↓reduceIte,neg_one_smul,mul_neg_one] using coordinate_front k i (-1)
    · simpa only [ν,s,↓reduceIte,one_smul,mul_one] using coordinate_front k i 1
  rw [hdet]
  simp only [Fin.cons_zero,Fin.cons_succ,one_mul, smul_eq_mul]
  have hp : 0 < ∏ j : Fin k, (b (i.succAbove j) - a (i.succAbove j)) :=
    Finset.prod_pos (fun j _ => sub_pos.mpr (hab _))
  constructor
  · ring
  · rcases neg_one_pow_eq_or ℝ i.val with hs | hs <;>
      cases upper <;> simp [s, hs, Real.sign_of_pos hp, Real.sign_of_neg (neg_neg_of_pos hp)]

theorem box_face_normal : box_face_normalType := by
  intro k a b hab i upper u hu
  dsimp only
  have hc := D04.Cells.cube_face_normal i upper u hu
  dsimp only at hc
  refine ⟨?_, hc.1, hc.2.1, ?_⟩
  · intro j
    have hj := (D04.Cells.mem_cube _).mp (faceInsertion_mem i upper hu) j
    change a j ≤ a j + (b j - a j) * faceInsertion i upper u j ∧
      a j + (b j - a j) * faceInsertion i upper u j ≤ b j
    constructor <;> nlinarith [hab j]
  · intro t ht hmem
    have hh := hmem i
    have hb : stdBasis (k+1) i i = 1 := by
      simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply]
    change a i ≤ _ ∧ _ ≤ b i at hh
    cases upper <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
        boxFace, Function.comp_apply, boxMap, WithLp.ofLp_toLp,
        D04.Cells.faceInsertion_same, Bool.false_eq_true, ↓reduceIte, hb] at hh <;>
      linarith

private lemma regular_of_inverse {k n : ℕ} (U : Set (Eucl k)) (hU : IsOpen U)
    (f : Eucl k → Eucl n) (g : Eucl n → Eucl k) (hf : ContDiffOn ℝ 1 f U)
    (hg : ∀ u ∈ U, DifferentiableAt ℝ g (f u))
    (hinv : g ∘ f = id) : FullRankLocalExtension 1 U f := by
  intro u hu
  refine ⟨U, f, hU, hu, fun _ _ => rfl, hf, ?_⟩
  intro v hv
  have hd := (hf.differentiableOn (by simp) v hv).differentiableAt (hU.mem_nhds hv)
  have he := fderiv_comp v (hg v hv) hd
  rw [hinv, fderiv_id] at he
  intro a b hab
  have hh := congrArg (fderiv ℝ g (f v)) hab
  simpa only [← ContinuousLinearMap.comp_apply, ← he, ContinuousLinearMap.id_apply] using hh

private def diskParam (R : ℝ) (u : Eucl 2) : Eucl 3 :=
  WithLp.toLp 2 ![Real.sqrt (R^2-u 0^2)-u 1, u 0, 0]
private def diskInverse (R : ℝ) (x : Eucl 3) : Eucl 2 :=
  WithLp.toLp 2 ![x 1, Real.sqrt (R^2-x 1^2)-x 0]
private def diskW (R : ℝ) : Set (Eucl 2) :=
  {u | u 0^2 < R^2 ∧ u 1 < Real.sqrt (R^2-u 0^2)}
private def diskO (R : ℝ) : Set (Eucl 3) :=
  {x | 0 < x 0 ∧ x 1^2 < R^2}

private lemma diskW_open (R : ℝ) : IsOpen (diskW R) := by
  exact (isOpen_lt (show Continuous (fun u : Eucl 2 => u 0^2) by fun_prop) continuous_const).inter
    (isOpen_lt (show Continuous (fun u : Eucl 2 => u 1) by fun_prop)
      (show Continuous (fun u : Eucl 2 => Real.sqrt (R^2-u 0^2)) by fun_prop))
private lemma diskO_open (R : ℝ) : IsOpen (diskO R) := by
  exact (isOpen_lt continuous_const (show Continuous (fun x : Eucl 3 => x 0) by fun_prop)).inter
    (isOpen_lt (show Continuous (fun x : Eucl 3 => x 1^2) by fun_prop) continuous_const)

private lemma diskParam_smooth (R : ℝ) : ContDiffOn ℝ 1 (diskParam R) (diskW R) := by
  apply (coords 3).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (ContDiffOn.sqrt (by fun_prop) (fun u hu => ne_of_gt (sub_pos.mpr hu.1))).sub
      (by fun_prop)
  · change ContDiffOn ℝ 1 (fun u : Eucl 2 => u 0) _
    fun_prop
  · change ContDiffOn ℝ 1 (fun _ : Eucl 2 => (0:ℝ)) _
    fun_prop

private lemma disk_inverse_left (R : ℝ) : diskInverse R ∘ diskParam R = id := by
  funext u
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [diskInverse, diskParam]

private def diskChart (R : ℝ) (hR : 0 < R) : EmbeddedChart 1 2 3 (disk R) where
  half := true
  half_pos := by simp
  source := halfSpace 2 ∩ diskW R
  source_open := ⟨diskW R, diskW_open R, rfl⟩
  ambient := diskO R
  ambient_open := diskO_open R
  toFun := diskParam R
  invFun := diskInverse R
  map_source := by
    intro u hu
    have hsq := Real.sq_sqrt (le_of_lt (sub_pos.mpr hu.2.1))
    have ht : 0 ≤ u 1 := hu.1
    have hs := Real.sqrt_nonneg (R^2-u 0^2)
    change ((diskParam R u) 2 = 0 ∧ _) ∧ _
    simp only [diskParam, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    exact ⟨⟨trivial, by nlinarith [hu.2.2]⟩, sub_pos.mpr hu.2.2, hu.2.1⟩
  map_target := by
    intro x hx
    obtain ⟨⟨hz,hbound⟩,hpos,hsmall⟩ := hx
    have hsq := Real.sq_sqrt (le_of_lt (sub_pos.mpr hsmall))
    have hs := Real.sqrt_nonneg (R^2-x 1^2)
    simp only [mem_inter_iff,halfSpace,mem_ofPred_eq,diskW,diskInverse, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]
    change 0 ≤ Real.sqrt (R^2-x 1^2)-x 0 ∧ x 1^2<R^2 ∧ _
    exact ⟨by nlinarith, hsmall, by linarith⟩
  left_inv u hu := congrFun (disk_inverse_left R) u
  right_inv := by
    intro x hx
    apply ext3 <;> simp [diskParam, diskInverse, hx.1.1]
  continuous_toFun := (diskParam_smooth R).continuousOn.mono inter_subset_right
  continuous_invFun := by
    apply Continuous.continuousOn
    unfold diskInverse
    fun_prop
  regular := by
    have hh := regular_of_inverse (diskW R) (diskW_open R) (diskParam R) (diskInverse R)
      (diskParam_smooth R) ?_ (disk_inverse_left R)
    · intro u hu
      obtain ⟨W,g,hW,huW,he,hg,hi⟩ := hh u hu.2
      exact ⟨W,g,hW,huW,fun v hv => he ⟨hv.1.2,hv.2⟩,hg,hi⟩
    · intro u hu
      apply (coords 2).symm.toContinuousLinearEquiv.differentiableAt.comp
      apply differentiableAt_pi.mpr
      intro i
      fin_cases i
      · change DifferentiableAt ℝ (fun x : Eucl 3 => x 1) _
        fun_prop
      · apply DifferentiableAt.sub
        · apply DifferentiableAt.sqrt (by fun_prop)
          simpa [diskParam] using ne_of_gt (sub_pos.mpr hu.1)
        · fun_prop

private lemma conormal_of_chart {M : Set (Eucl 3)} (c : EmbeddedChart 1 2 3 M)
    (u : Eucl 2) (hu : u ∈ c.source) (hc : c.half = true) (hflat : u 1 = 0)
    (ν : Eucl 3) (hn : ‖ν‖ = 1)
    (ho : ∀ w : Eucl 2, w 1 = 0 → ⟪ν,chartDifferential c u w⟫ = 0)
    (z : Eucl 2) (hz : chartDifferential c u z = ν) (hzneg : z 1 < 0) :
    c.toFun u ∈ intrinsicBoundary 1 2 M ∧
    IsOutwardUnitConormal 1 1 M (c.toFun u) ν := by
  have hr : ManifoldRegularity (1 : ℕ∞ω) := ⟨le_rfl, by simp⟩
  refine ⟨⟨(c.map_source hu).1,c,u,hc,hu,hflat,rfl⟩, ?_, hn, ?_, c,u,z,hu,
    ⟨hc,hflat⟩,rfl,hz,hzneg⟩
  · rw [D04.tangentSpace_chart c hr (by norm_num) u hu]
    exact ⟨z,hz⟩
  · intro w hw
    change w ∈ (Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace 1 1
      (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 1 2 M) (c.toFun u) : Set _) at hw
    rw [D04.tangentSpace_intrinsic_boundary c hr (by norm_num) hc u hu hflat] at hw
    obtain ⟨v,hv,rfl⟩ := hw
    exact ho v hv

private def diskA : Eucl 2 →ₗ[ℝ] Eucl 3 where
  toFun w := WithLp.toLp 2 ![-w 1,w 0,0]
  map_add' w v := by apply PiLp.ext; intro i; fin_cases i <;> simp <;> ring
  map_smul' t w := by apply PiLp.ext; intro i; fin_cases i <;> simp <;> ring

private lemma diskParam_derivative_zero (R : ℝ) (hR : 0 < R) :
    HasFDerivAt (diskParam R) diskA.toContinuousLinearMap 0 := by
  let P0 : Eucl 2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let P1 : Eucl 2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hs := ((hasFDerivAt_const (R^2) (0 : Eucl 2)).sub
    (P0.hasFDerivAt.pow 2)).sqrt (show R^2-(0:Eucl 2) 0^2 ≠ 0 by simpa using ne_of_gt (sq_pos_of_pos hR))
  have hzero : HasFDerivAt (𝕜 := ℝ) (fun u : Eucl 2 => Real.sqrt (R^2-u 0^2)) 0 (0 : Eucl 2) := by
    convert hs using 1 <;> ext w <;> simp [P0]
  have hp : HasFDerivAt (fun u : Eucl 2 =>
      ![Real.sqrt (R^2-u 0^2)-u 1,u 0,0])
      (ContinuousLinearMap.pi (fun i : Fin 3 => ![-P1,P0,0] i)) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert hzero.sub P1.hasFDerivAt using 1 <;> ext v <;> simp [P1]
    · exact P0.hasFDerivAt
    · exact hasFDerivAt_const _ _
  convert (coords 3).symm.toContinuousLinearEquiv.hasFDerivAt.comp 0 hp using 1
  all_goals first | rfl | (ext w i; fin_cases i <;> rfl)

private lemma disk_chart_zero (R : ℝ) (hR : 0 < R) :
    (0 : Eucl 2) ∈ (diskChart R hR).source ∧
    (diskChart R hR).toFun 0 = R • stdBasis 3 0 ∧
    chartDifferential (diskChart R hR) 0 = diskA.toContinuousLinearMap := by
  have hu : (0 : Eucl 2) ∈ (diskChart R hR).source := by
    change 0 ≤ (0 : Eucl 2) 1 ∧ _
    simp [diskW, Real.sqrt_sq hR.le, sq_pos_of_pos hR, hR]
  refine ⟨hu, ?_, ?_⟩
  · apply ext3 <;> simp [diskChart, diskParam, Real.sqrt_sq hR.le, basis3]
  · rw [D04.EmbeddedChart.differential_extension _ hu (diskW_open R) hu.2
      (fun _ _ => rfl) (diskParam_derivative_zero R hR).differentiableAt]
    exact (diskParam_derivative_zero R hR).fderiv

private def turnLinear (a b : ℝ) : Eucl 3 →ₗ[ℝ] Eucl 3 where
  toFun x := WithLp.toLp 2 ![a*x 0-b*x 1,b*x 0+a*x 1,x 2]
  map_add' x y := by apply PiLp.ext; intro i; fin_cases i <;> simp <;> ring
  map_smul' t x := by apply PiLp.ext; intro i; fin_cases i <;> simp <;> ring

private def turn (a b : ℝ) (h : a^2+b^2=1) : Eucl 3 ≃ₗᵢ[ℝ] Eucl 3 where
  toLinearEquiv := {
    toLinearMap := turnLinear a b
    invFun := turnLinear a (-b)
    left_inv := by
      intro x
      apply ext3
      all_goals simp only [turnLinear,LinearMap.coe_mk,AddHom.coe_mk, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,WithLp.ofLp_toLp]
      · change a*(a*x 0-b*x 1)-(-b)*(b*x 0+a*x 1)=x 0
        linear_combination x 0 * h
      · change -b*(a*x 0-b*x 1)+a*(b*x 0+a*x 1)=x 1
        linear_combination x 1 * h
    right_inv := by
      intro x
      apply ext3
      all_goals simp only [turnLinear,LinearMap.coe_mk,AddHom.coe_mk, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,WithLp.ofLp_toLp]
      · change a*(a*x 0-(-b)*x 1)-b*(-b*x 0+a*x 1)=x 0
        linear_combination x 0 * h
      · change b*(a*x 0-(-b)*x 1)+a*(-b*x 0+a*x 1)=x 1
        linear_combination x 1 * h }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq3, norm_sq3]
    change (a*x 0-b*x 1)^2+(b*x 0+a*x 1)^2+x 2^2=x 0^2+x 1^2+x 2^2
    linear_combination (x 0^2+x 1^2)*h

private lemma turn_shape (R a b : ℝ) (h : a^2+b^2=1) (x : Eucl 3) :
    turn a b h x ∈ disk R ↔ x ∈ disk R := by
  have he : (turn a b h x) 0^2+(turn a b h x) 1^2 = x 0^2+x 1^2 := by
    change (a*x 0-b*x 1)^2+(b*x 0+a*x 1)^2 = _
    linear_combination (x 0^2+x 1^2)*h
  change (turn a b h x) 2 = 0 ∧ _ ↔ _
  rw [he]
  rfl

private def mapChart {M N : Set (Eucl 3)} (e : Eucl 3 ≃ₗᵢ[ℝ] Eucl 3)
    (he : ∀ x, e x ∈ N ↔ x ∈ M) (c : EmbeddedChart 1 2 3 M) :
    EmbeddedChart 1 2 3 N where
  half := c.half
  half_pos := c.half_pos
  source := c.source
  source_open := c.source_open
  ambient := e.symm ⁻¹' c.ambient
  ambient_open := c.ambient_open.preimage e.symm.continuous
  toFun := e ∘ c.toFun
  invFun := c.invFun ∘ e.symm
  map_source := by
    intro u hu
    exact ⟨(he _).mpr (c.map_source hu).1, by simpa using (c.map_source hu).2⟩
  map_target := by
    intro x hx
    apply c.map_target
    exact ⟨(he (e.symm x)).mp (by simpa using hx.1),hx.2⟩
  left_inv u hu := by simpa using c.left_inv u hu
  right_inv x hx := by
    change e (c.toFun (c.invFun (e.symm x))) = x
    rw [c.right_inv _ ⟨(he _).mp (by simpa using hx.1),hx.2⟩, e.apply_symm_apply]
  continuous_toFun := e.continuous.comp_continuousOn c.continuous_toFun
  continuous_invFun := c.continuous_invFun.comp e.symm.continuous.continuousOn
    (fun x hx => ⟨(he _).mp (by simpa using hx.1),hx.2⟩)
  regular := by
    intro u hu
    obtain ⟨W,g,hW,huW,hg,hgd,hgi⟩ := c.regular u hu
    refine ⟨W,e ∘ g,hW,huW,fun v hv => congrArg e (hg hv),
      e.toContinuousLinearEquiv.contDiff.comp_contDiffOn hgd, ?_⟩
    intro v hv
    have hd := (hgd.differentiableOn (by simp) v hv).differentiableAt (hW.mem_nhds hv)
    change Function.Injective (fderiv ℝ (fun y => e.toContinuousLinearEquiv (g y)) v)
    have hcomp := (e.toContinuousLinearEquiv.hasFDerivAt.comp v hd.hasFDerivAt).fderiv
    change fderiv ℝ (fun y => e.toContinuousLinearEquiv (g y)) v =
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ g v) at hcomp
    rw [hcomp]
    exact e.injective.comp (hgi v hv)

private lemma mapChart_differential {M N : Set (Eucl 3)} (e : Eucl 3 ≃ₗᵢ[ℝ] Eucl 3)
    (he : ∀ x, e x ∈ N ↔ x ∈ M) (c : EmbeddedChart 1 2 3 M)
    (u : Eucl 2) (hu : u ∈ c.source) :
    chartDifferential (mapChart e he c) u =
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp (chartDifferential c u) := by
  apply HasFDerivWithinAt.fderivWithin _ (D04.EmbeddedChart.source_uniqueDiff c u hu)
  exact e.toContinuousLinearEquiv.hasFDerivAt.comp_hasFDerivWithinAt u
    (c.hasDifferential ⟨le_rfl, by simp⟩ hu)

private lemma conormal_turn_disk {R : ℝ} (hR : 0 < R) (a b : ℝ) (h : a^2+b^2=1) :
    turn a b h (R • stdBasis 3 0) ∈ intrinsicBoundary 1 2 (disk R) ∧
    IsOutwardUnitConormal 1 1 (disk R) (turn a b h (R • stdBasis 3 0))
      (turn a b h (stdBasis 3 0)) := by
  let e := turn a b h
  let c := mapChart e (turn_shape R a b h) (diskChart R hR)
  obtain ⟨hu,hpoint,hd⟩ := disk_chart_zero R hR
  have hD : ∀ w, chartDifferential c 0 w = e (diskA w) := by
    intro w
    rw [mapChart_differential e _ _ 0 hu, hd]
    rfl
  have hh := conormal_of_chart c 0 hu rfl rfl (e (stdBasis 3 0))
    (by rw [e.norm_map]; simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply]) ?_
    (WithLp.toLp 2 ![0,-1]) ?_ (by norm_num)
  · simpa [c,mapChart,hpoint] using hh
  · intro w hw
    rw [hD,e.inner_map_map]
    simp [inner3, diskA, basis3, hw]
  · rw [hD]
    congr 1
    apply ext3 <;> simp [diskA, basis3]

theorem disk_signs : disk_signsType := by
  intro R hR x hx
  have hn : R ≠ 0 := ne_of_gt hR
  let a := x 0/R
  let b := x 1/R
  have hab : a^2+b^2=1 := by
    dsimp [a,b]
    field_simp
    exact hx.2
  obtain ⟨hb,hc⟩ := conormal_turn_disk hR a b hab
  have hx' : turn a b hab (R • stdBasis 3 0) = x := by
    apply ext3 <;> simp [turn,turnLinear,basis3,a,b,hn,hx.1] <;> field_simp <;> ring
  have hr : turn a b hab (stdBasis 3 0) = radial R x := by
    apply ext3 <;> simp [turn,turnLinear,basis3,a,b,radial,div_eq_mul_inv,hx.1,mul_comm]
  rw [hx'] at hb hc
  rw [hr] at hc
  have hf := equator_frame hR hx
  exact ⟨hb,hc,hf.2.2.1,hf.2.1,hf.2.2.2⟩

private def hemiParam (R : ℝ) (upper : Bool) (u : Eucl 2) : Eucl 3 :=
  WithLp.toLp 2 ![Real.sqrt (R^2-u 0^2-u 1^2),u 0,if upper then u 1 else -u 1]
private def hemiInverse (upper : Bool) (x : Eucl 3) : Eucl 2 :=
  WithLp.toLp 2 ![x 1,if upper then x 2 else -x 2]
private def hemiW (R : ℝ) : Set (Eucl 2) := {u | u 0^2+u 1^2<R^2}
private def hemiO : Set (Eucl 3) := {x | 0 < x 0}

private lemma hemiW_open (R : ℝ) : IsOpen (hemiW R) :=
  isOpen_lt (show Continuous (fun u : Eucl 2 => u 0^2+u 1^2) by fun_prop) continuous_const

private lemma hemiParam_smooth (R : ℝ) (upper : Bool) :
    ContDiffOn ℝ 1 (hemiParam R upper) (hemiW R) := by
  apply (coords 3).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · apply ContDiffOn.sqrt (by fun_prop)
    intro u hu
    exact ne_of_gt (by change u 0^2+u 1^2<R^2 at hu; linarith)
  · change ContDiffOn ℝ 1 (fun u : Eucl 2 => u 0) _
    fun_prop
  · change ContDiffOn ℝ 1 (fun u : Eucl 2 => if upper then u 1 else -u 1) _
    cases upper <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop

private lemma hemiInverse_smooth (upper : Bool) : ContDiff ℝ 1 (hemiInverse upper) := by
  apply (coords 2).symm.toContinuousLinearEquiv.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ 1 (fun x : Eucl 3 => x 1)
    fun_prop
  · change ContDiff ℝ 1 (fun x : Eucl 3 => if upper then x 2 else -x 2)
    cases upper <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop

private lemma hemi_inverse_left (R : ℝ) (upper : Bool) : hemiInverse upper ∘ hemiParam R upper = id := by
  funext u
  apply PiLp.ext
  intro i
  fin_cases i <;> cases upper <;> simp [hemiInverse,hemiParam]

private def hemiChart (R : ℝ) (hR : 0 < R) (upper : Bool) :
    EmbeddedChart 1 2 3 (hemisphere R upper) where
  half := true
  half_pos := by simp
  source := halfSpace 2 ∩ hemiW R
  source_open := ⟨hemiW R,hemiW_open R,rfl⟩
  ambient := hemiO
  ambient_open := isOpen_lt continuous_const
    (show Continuous (fun x : Eucl 3 => x 0) by fun_prop)
  toFun := hemiParam R upper
  invFun := hemiInverse upper
  map_source := by
    intro u hu
    have hp0 : u 0^2+u 1^2<R^2 := hu.2
    have hp : 0 < R^2-u 0^2-u 1^2 := by linarith
    have hsq := Real.sq_sqrt hp.le
    have ht : 0 ≤ u 1 := hu.1
    change ((hemiParam R upper u) 0^2+(hemiParam R upper u) 1^2+(hemiParam R upper u) 2^2=R^2 ∧ _) ∧ _
    cases upper <;> simp only [hemiParam,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Bool.false_eq_true,↓reduceIte]
    all_goals exact ⟨⟨by nlinarith,by simpa using ht⟩,Real.sqrt_pos.mpr hp⟩
  map_target := by
    intro x hx
    have hx0 : 0 < x 0 := hx.2
    have hs := hx.1.1
    have ht := hx.1.2
    simp only [mem_inter_iff,Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace,hemiW,mem_ofPred_eq,hemiInverse,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    cases upper <;> simp only [Bool.false_eq_true,↓reduceIte] at ht ⊢
    · exact ⟨by change 0 ≤ -x 2; linarith,by nlinarith [sq_pos_of_pos hx0]⟩
    · exact ⟨ht,by nlinarith [sq_pos_of_pos hx0]⟩
  left_inv u hu := congrFun (hemi_inverse_left R upper) u
  right_inv := by
    intro x hx
    have hx0 : 0 < x 0 := hx.2
    have hs := hx.1.1
    apply ext3
    · change Real.sqrt (R^2-x 1^2-(if upper then x 2 else -x 2)^2)=x 0
      have he : R^2-x 1^2-(if upper then x 2 else -x 2)^2=x 0^2 := by
        cases upper <;> simp <;> nlinarith [hs]
      rw [he,Real.sqrt_sq hx0.le]
    · rfl
    · cases upper <;> simp [hemiParam,hemiInverse]
  continuous_toFun := (hemiParam_smooth R upper).continuousOn.mono inter_subset_right
  continuous_invFun := (hemiInverse_smooth upper).continuous.continuousOn
  regular := by
    intro u hu
    obtain ⟨W,g,hW,huW,he,hg,hi⟩ := regular_of_inverse (hemiW R) (hemiW_open R)
      (hemiParam R upper) (hemiInverse upper) (hemiParam_smooth R upper)
      (fun _ _ => (hemiInverse_smooth upper).differentiable (by simp) _)
      (hemi_inverse_left R upper) u hu.2
    exact ⟨W,g,hW,huW,fun v hv => he ⟨hv.1.2,hv.2⟩,hg,hi⟩

private def hemiA (upper : Bool) : Eucl 2 →ₗ[ℝ] Eucl 3 where
  toFun w := WithLp.toLp 2 ![0,w 0,if upper then w 1 else -w 1]
  map_add' w v := by apply PiLp.ext; intro i; fin_cases i <;> cases upper <;> simp <;> ring
  map_smul' t w := by apply PiLp.ext; intro i; fin_cases i <;> cases upper <;> simp <;> ring

private lemma hemiParam_derivative_zero (R : ℝ) (hR : 0 < R) (upper : Bool) :
    HasFDerivAt (hemiParam R upper) (hemiA upper).toContinuousLinearMap 0 := by
  let P0 : Eucl 2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let P1 : Eucl 2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hs := (((hasFDerivAt_const (R^2) (0 : Eucl 2)).sub
    (P0.hasFDerivAt.pow 2)).sub (P1.hasFDerivAt.pow 2)).sqrt
    (show R^2-(0:Eucl 2) 0^2-(0:Eucl 2) 1^2 ≠ 0 by simpa using ne_of_gt (sq_pos_of_pos hR))
  have hzero : HasFDerivAt (𝕜 := ℝ) (fun u : Eucl 2 => Real.sqrt (R^2-u 0^2-u 1^2)) 0 (0 : Eucl 2) := by
    convert hs using 1 <;> ext w <;> simp [P0,P1]
  have hp : HasFDerivAt (fun u : Eucl 2 =>
      ![Real.sqrt (R^2-u 0^2-u 1^2),u 0,if upper then u 1 else -u 1])
      (ContinuousLinearMap.pi (fun i : Fin 3 => ![0,P0,if upper then P1 else -P1] i)) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hzero
    · exact P0.hasFDerivAt
    · cases upper
      · exact P1.hasFDerivAt.neg
      · exact P1.hasFDerivAt
  convert (coords 3).symm.toContinuousLinearEquiv.hasFDerivAt.comp 0 hp using 1
  all_goals first | rfl | (ext w i; fin_cases i <;> cases upper <;> rfl)

private lemma hemi_chart_zero (R : ℝ) (hR : 0 < R) (upper : Bool) :
    (0 : Eucl 2) ∈ (hemiChart R hR upper).source ∧
    (hemiChart R hR upper).toFun 0 = R • stdBasis 3 0 ∧
    chartDifferential (hemiChart R hR upper) 0 = (hemiA upper).toContinuousLinearMap := by
  have hu : (0 : Eucl 2) ∈ (hemiChart R hR upper).source := by
    change 0 ≤ (0 : Eucl 2) 1 ∧ _
    simp [hemiW,sq_pos_of_pos hR]
  refine ⟨hu, ?_, ?_⟩
  · apply ext3 <;> cases upper <;> simp [hemiChart,hemiParam,Real.sqrt_sq hR.le,basis3]
  · rw [D04.EmbeddedChart.differential_extension _ hu (hemiW_open R) hu.2
      (fun _ _ => rfl) (hemiParam_derivative_zero R hR upper).differentiableAt]
    exact (hemiParam_derivative_zero R hR upper).fderiv

private lemma turn_hemi (R a b : ℝ) (h : a^2+b^2=1) (upper : Bool) (x : Eucl 3) :
    turn a b h x ∈ hemisphere R upper ↔ x ∈ hemisphere R upper := by
  have he : (turn a b h x) 0^2+(turn a b h x) 1^2 = x 0^2+x 1^2 := by
    change (a*x 0-b*x 1)^2+(b*x 0+a*x 1)^2 = _
    linear_combination (x 0^2+x 1^2)*h
  change ((turn a b h x) 0^2+(turn a b h x) 1^2)+(turn a b h x) 2^2 = _ ∧ _ ↔ _
  rw [he]
  rfl

private lemma conormal_turn_hemi {R : ℝ} (hR : 0 < R) (a b : ℝ) (h : a^2+b^2=1)
    (upper : Bool) :
    turn a b h (R • stdBasis 3 0) ∈ intrinsicBoundary 1 2 (hemisphere R upper) ∧
    IsOutwardUnitConormal 1 1 (hemisphere R upper) (turn a b h (R • stdBasis 3 0))
      (if upper then -stdBasis 3 2 else stdBasis 3 2) := by
  let e := turn a b h
  let c := mapChart e (turn_hemi R a b h upper) (hemiChart R hR upper)
  obtain ⟨hu,hpoint,hd⟩ := hemi_chart_zero R hR upper
  have hD : ∀ w, chartDifferential c 0 w = e (hemiA upper w) := by
    intro w
    rw [mapChart_differential e _ _ 0 hu, hd]
    rfl
  let ν : Eucl 3 := if upper then -stdBasis 3 2 else stdBasis 3 2
  have heν : e ν = ν := by
    apply ext3 <;> cases upper <;> simp [ν,e,turn,turnLinear,basis3]
  have hh := conormal_of_chart c 0 hu rfl rfl (e ν)
    (by rw [e.norm_map]; cases upper <;> simp [ν,Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,EuclideanSpace.basisFun_apply]) ?_
    (WithLp.toLp 2 ![0,-1]) ?_ (by norm_num)
  · simpa [c,mapChart,hpoint,heν] using hh
  · intro w hw
    rw [hD,e.inner_map_map]
    cases upper <;> simp [ν,inner3,hemiA,basis3,hw]
  · rw [hD]
    congr 1
    apply ext3 <;> cases upper <;> simp [hemiA,ν,basis3]

lemma hemisphere_frame {R : ℝ} (hR : 0 < R) (upper : Bool) {x : Eucl 3} (hx : x ∈ equator R) :
    euclideanCross (radial R x) (if upper then -stdBasis 3 2 else stdBasis 3 2) =
      (if upper then ccw R x else -ccw R x) ∧
    euclideanCross (if upper then -stdBasis 3 2 else stdBasis 3 2)
      (if upper then ccw R x else -ccw R x) = radial R x := by
  have hf := equator_frame hR hx
  cases upper <;> constructor
  all_goals apply ext3 <;> simp [cross3,ccw,radial,basis3,hx.1,div_eq_mul_inv,mul_comm]

theorem hemisphere_signs : hemisphere_signsType := by
  intro R hR upper x hx
  have hn : R ≠ 0 := ne_of_gt hR
  let a := x 0/R
  let b := x 1/R
  have hab : a^2+b^2=1 := by dsimp [a,b]; field_simp; exact hx.2
  obtain ⟨hb,hc⟩ := conormal_turn_hemi hR a b hab upper
  have hx' : turn a b hab (R • stdBasis 3 0) = x := by
    apply ext3 <;> simp [turn,turnLinear,basis3,a,b,hn,hx.1] <;> field_simp <;> ring
  rw [hx'] at hb hc
  have hf := hemisphere_frame hR upper hx
  exact ⟨hb,hc,hf.1,hf.2⟩

private lemma circle_contDiff (R : ℝ) : ContDiff ℝ 1 (circle R) := by
  apply (coords 3).symm.toContinuousLinearEquiv.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ 1 (fun t : ℝ => R*Real.cos t)
    fun_prop
  · change ContDiff ℝ 1 (fun t : ℝ => R*Real.sin t)
    fun_prop
  · change ContDiff ℝ 1 (fun _ : ℝ => (0:ℝ))
    fun_prop

private def equatorCell (R : ℝ) : Cell 1 1 (Set.univ : Set (Eucl 3)) where
  toFun u := ⟨circle R (2*Real.pi*u.val 0), mem_univ _⟩
  open_target := isOpen_univ
  positive := le_rfl
  hasExtension := ⟨fun u => circle R (2*Real.pi*u 0),univ,isOpen_univ,subset_univ _,
    ((circle_contDiff R).comp (show ContDiff ℝ 1 (fun u : Eucl 1 => 2*Real.pi*u 0) by fun_prop)).contDiffOn,
    fun _ => rfl⟩

theorem hemisphere_seam : hemisphere_seamType := by
  intro R hR
  refine ⟨equatorCell R,fun _ => rfl,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ((circle_traversal R hR).1 _).1
    · intro hx
      let z : ℂ := ⟨x 0,x 1⟩
      have hnorm : ‖z‖=R := by
        have hh := Complex.sq_norm z
        simp only [Complex.normSq_apply,z] at hh
        nlinarith [hx.2,norm_nonneg z]
      have hz : z ≠ 0 := norm_ne_zero_iff.mp (hnorm ▸ ne_of_gt hR)
      let θ := if 0 ≤ z.arg then z.arg else z.arg+2*Real.pi
      have hθ : 0 ≤ θ ∧ θ ≤ 2*Real.pi := by
        dsimp [θ]
        split_ifs with h
        · exact ⟨h,by linarith [Complex.arg_le_pi z,Real.pi_pos]⟩
        · exact ⟨by linarith [Complex.neg_pi_lt_arg z,Real.pi_pos],by linarith⟩
      have hp : 0 < 2*Real.pi := by positivity
      let u : Eucl 1 := WithLp.toLp 2 (fun _ => θ/(2*Real.pi))
      have hu : u ∈ cube 1 := by
        apply (D04.Cells.mem_cube _).mpr
        intro i
        change 0 ≤ θ/(2*Real.pi) ∧ θ/(2*Real.pi) ≤ 1
        exact ⟨div_nonneg hθ.1 hp.le,(div_le_one hp).mpr hθ.2⟩
      refine ⟨⟨u,hu⟩,?_⟩
      change circle R (2*Real.pi*(θ/(2*Real.pi))) = x
      rw [mul_div_cancel₀ _ (ne_of_gt hp)]
      have hcos : Real.cos θ = Real.cos z.arg := by
        dsimp [θ]; split_ifs <;> simp
      have hsin : Real.sin θ = Real.sin z.arg := by
        dsimp [θ]; split_ifs <;> simp
      apply ext3
      · change R*Real.cos θ=x 0
        rw [hcos,Complex.cos_arg hz,hnorm]
        exact mul_div_cancel₀ _ (ne_of_gt hR)
      · change R*Real.sin θ=x 1
        rw [hsin,Complex.sin_arg,hnorm]
        exact mul_div_cancel₀ _ (ne_of_gt hR)
      · simpa [circle] using hx.1.symm
  · intro eta
    simp only [map_neg,add_neg_cancel]

private def boxCell {n : ℕ} (a b : Eucl n) : Cell 1 n (Set.univ : Set (Eucl n)) where
  toFun u := ⟨boxMap a b u,mem_univ _⟩
  open_target := isOpen_univ
  positive := le_rfl
  hasExtension := by
    refine ⟨boxMap a b,univ,isOpen_univ,subset_univ _,?_,fun _ => rfl⟩
    rw [boxMap_affine]
    exact ((boxLinear a b).toContinuousLinearMap.contDiff.add contDiff_const).contDiffOn

theorem box_cell_stokes : box_cell_stokesType := by
  intro k a b hab
  refine ⟨boxCell a b,fun _ => rfl,?_⟩
  intro V eta heta hmap
  have he := D04.Cells.cell_stokes_c1 (boxCell a b) V eta heta
    (fun u => hmap u u.property)
  refine he.trans ?_
  change Specs.D04.C15.CellsChainsAndIntegrals.Model.chainIntegral eta (∑ i : Fin (k+1), (-1:ℤ)^i.val •
    (Finsupp.single (cellFace (boxCell a b) i true) 1 -
      Finsupp.single (cellFace (boxCell a b) i false) 1)) = _
  simp only [map_sum,map_zsmul,map_sub,D04.Cells.chainIntegral_single,one_smul,
    zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]

theorem box_parametrization : box_parametrizationType := by
  intro n a b hab
  have hd (i : Fin n) : 0 < b i-a i := sub_pos.mpr (hab i)
  constructor
  · ext x
    constructor
    · rintro ⟨u,hu,rfl⟩ j
      have hj := (D04.Cells.mem_cube _).mp hu j
      change a j ≤ a j+(b j-a j)*u j ∧ a j+(b j-a j)*u j ≤ b j
      constructor <;> nlinarith [hd j]
    · intro hx
      let u : Eucl n := WithLp.toLp 2 (fun j => (x j-a j)/(b j-a j))
      have hu : u ∈ cube n := by
        apply (D04.Cells.mem_cube _).mpr
        intro i
        change 0 ≤ (x i-a i)/(b i-a i) ∧ (x i-a i)/(b i-a i) ≤ 1
        exact ⟨div_nonneg (sub_nonneg.mpr (hx i).1) (hd i).le,
          (div_le_one (hd i)).mpr (by linarith [(hx i).2])⟩
      refine ⟨u,hu,?_⟩
      apply PiLp.ext
      intro i
      change a i+(b i-a i)*((x i-a i)/(b i-a i))=x i
      rw [mul_div_cancel₀ _ (ne_of_gt (hd i))]
      ring
  · intro u v huv
    apply PiLp.ext
    intro i
    have hi := congrArg (fun x : Eucl n => x i) huv
    change a i+(b i-a i)*u i=a i+(b i-a i)*v i at hi
    nlinarith [hd i]

theorem circle_single_traversal : circle_single_traversalType := by
  intro R hR θ hθ φ hφ he
  have hn : R ≠ 0 := ne_of_gt hR
  have hc : Real.cos θ=Real.cos φ := by
    apply mul_left_cancel₀ hn
    exact congrArg (fun x : Eucl 3 => x 0) he
  have hs : Real.sin θ=Real.sin φ := by
    apply mul_left_cancel₀ hn
    exact congrArg (fun x : Eucl 3 => x 1) he
  have ha := Real.Angle.cos_sin_inj hc hs
  letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2*Real.pi) (a := 0)
    (by simpa using hθ) (by simpa using hφ)).mp ha

theorem equator_integrable : equator_integrableType := by
  intro R hR c hparam V eta heta hV
  have hext := Specs.D04.C15.CellsChainsAndIntegrals.Model.extension_spec c
  have hc : ContinuousOn (cellCoefficient c eta) (cube 1) := by
    apply D04.Cells.C1.pullback_evaluation_continuousOn eta heta
      (fun j => stdBasis 1 j)
      ((D04.Cells.extension_C1 c).continuousOn.mono hext.2.1)
      (((D04.Cells.extension_C1 c).continuousOn_fderiv_of_isOpen hext.1 le_rfl).mono hext.2.1)
    intro u hu
    rw [D04.Cells.extension_on_cube c ⟨u,hu⟩,hparam ⟨u,hu⟩]
    exact hV (((circle_traversal R hR).1 _).1)
  exact ⟨D04.ExceptionalSets.integrable_continuous (by norm_num) (cubeBox 1)
    (cellCoefficient c eta) hc,rfl⟩

end D04.SignExamples
