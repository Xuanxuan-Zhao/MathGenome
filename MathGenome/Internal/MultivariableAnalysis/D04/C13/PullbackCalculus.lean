import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.PullbackCalculus
import MathGenome.Internal.MultivariableAnalysis.D04.C13.NormalizedFormsAndWedge
import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import MathGenome.Internal.MultivariableAnalysis.D04.C02.CrCalculus
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped BigOperators Classical
open Set Filter Topology
namespace D04
abbrev pullback := @Specs.D04.C13.PullbackCalculus.Model.pullback
abbrev coordinateOneForm := Specs.D04.C13.PullbackCalculus.Model.coordinateOneForm
abbrev volumeForm := Specs.D04.C13.PullbackCalculus.Model.volumeForm

@[simp] theorem pullback_apply {m n k : ℕ} (f : E m → E n) (ω : FormField n k)
    (x : E m) (v : Fin k → E m) :
    pullback f ω x v = ω (f x) (fun i => totalDerivative f x (v i)) := rfl

theorem pullback_zero_degree {m n : ℕ} (f : E m → E n) (a : E n → ℝ) :
    pullback f (fun y => scalarCovector (a y)) = fun x => scalarCovector (a (f x)) := by
  funext x
  ext v
  rfl

theorem pullback_add {m n k : ℕ} (f : E m → E n) (α β : FormField n k) :
    pullback f (fun y => α y + β y) = fun x => pullback f α x + pullback f β x := by
  funext x
  ext v
  rfl

theorem pullback_smul {m n k : ℕ} (f : E m → E n) (a : E n → ℝ) (ω : FormField n k) :
    pullback f (fun y => a y • ω y) = fun x => a (f x) • pullback f ω x := by
  funext x
  ext v
  rfl

theorem pullback_wedge {m n p q : ℕ} (f : E m → E n) (α : FormField n p)
    (β : FormField n q) :
    pullback f (fun y => wedge (α y) (β y)) =
      fun x => wedge (pullback f α x) (pullback f β x) := by
  funext x
  ext v
  simp only [pullback_apply, wedge_apply]

theorem pullback_comp {m n l k : ℕ} (U : Set (E m)) (V : Set (E n)) (W : Set (E l))
    (f : E m → E n) (g : E n → E l) (ω : FormField l k) (x : E m)
    (hfV : MapsTo f U V) (_hgW : MapsTo g V W) (hx : x ∈ U)
    (hf : TotalDifferentiableOn U f) (hg : TotalDifferentiableOn V g) :
    pullback (g ∘ f) ω x = pullback f (pullback g ω) x := by
  ext v
  simp only [pullback_apply, Function.comp_apply,
    totalDerivative_comp U V f g x (hf x hx) (hg (f x) (hfV hx)),
    ContinuousLinearMap.comp_apply]

/-- Evaluation of a field on variable vectors, via its finite coefficient expansion. -/
theorem formField_evaluation {n k : ℕ} (ω : FormField n k) (x : E n) (v : Fin k → E n) :
    ω x v = ∑ I : MultiIndex n k, coefficient (standardBasis n) (ω x) I *
      dx (standardBasis n) I v := by
  conv_lhs => rw [covector_expansion (standardBasis n) (ω x)]
  simp only [sum_apply, smul_apply, smul_eq_mul]

@[simp] theorem coordinateOneForm_apply {n : ℕ} (i : Fin n) (v : Fin 1 → E n) :
    coordinateOneForm n i v = v 0 i := by
  rfl

@[simp] theorem volumeForm_apply {n : ℕ} (v : Fin n → E n) :
    volumeForm n v = Matrix.det (fun i j => v j i) := by
  exact wedgeList_apply n (fun i => (standardBasis n).coord i) v

/-- Expansion of any linear map in the shared column coordinates. -/
theorem linearMap_coordinate_sum {m n : ℕ} (A : E m →ₗ[ℝ] E n) (v : E m) (i : Fin n) :
    A v i = ∑ j : Fin m, matrixOfLinearMap A i j * v j := by
  have h := congrArg (fun B : E m →ₗ[ℝ] E n => B v i) (matrix_linear_roundtrip A)
  exact h.symm

theorem pullback_coordinate {m n : ℕ} (U : Set (E m)) (f : E m → E n)
    (x : E m) (i : Fin n) (hf : TotalDifferentiableAt U f x) :
    pullback f (fun _ => coordinateOneForm n i) x =
      ∑ j : Fin m, scalarPartialDerivative (fun y => f y i) x j • coordinateOneForm m j := by
  ext v
  simp only [pullback_apply, coordinateOneForm_apply,
    sum_apply, smul_apply, smul_eq_mul]
  calc
    _ = ∑ j : Fin m, jacobian f x i j * (v 0) j :=
      linearMap_coordinate_sum (totalDerivative f x).toLinearMap (v 0) i
    _ = _ := Finset.sum_congr rfl (fun j _ =>
      congrArg (fun c : ℝ => c * (v 0) j) (jacobian_apply U f x hf i j))

theorem pullback_volume {n : ℕ} (f : E n → E n) (a : E n → ℝ) (x : E n) :
    pullback f (fun y => a y • volumeForm n) x =
      (a (f x) * Matrix.det (jacobian f x)) • volumeForm n := by
  ext v
  simp only [pullback_apply, smul_apply, smul_eq_mul, volumeForm_apply]
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => v j i)
  have hm : ((fun i j => totalDerivative f x (v j) i) : Matrix (Fin n) (Fin n) ℝ) =
      jacobian f x * B := by
    ext i j
    exact linearMap_coordinate_sum (totalDerivative f x).toLinearMap (v j) i
  rw [hm, Matrix.det_mul, mul_assoc]
  rfl

/-- Regularity of the evaluation of a Cʳ field on Cʳ vector fields. -/
theorem isCrForm_evaluation {m n k : ℕ} (r : ℕ) (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k) (v : Fin k → E m → E n)
    (hU : IsOpen U) (hmap : MapsTo f U V) (hf : CrOn r U f)
    (hω : IsCrForm (some r) V ω) (hv : ∀ i, CrOn r U (v i)) :
    CrOn r U (fun x => ω (f x) (fun i => v i x)) := by
  simp_rw [formField_evaluation]
  apply crOn_sum r Finset.univ U _ hU
  intro I _
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  apply ContDiffOn.mul
  · exact (crOn_iff_contDiffOn r U _ hU).mp
      (crOn_comp r U V f _ hU hω.1 hmap hf (hω.2 I))
  · exact (crOn_iff_contDiffOn r U _ hU).mp
      (crOn_multilinear r k (fun _ => E n) (dx (standardBasis n) I).toMultilinearMap
        U v hU hv)

theorem pullback_isCrForm {m n k : ℕ} (r : ℕ) (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k) (hU : IsOpen U) (hmap : MapsTo f U V)
    (hf : CrOn (r + 1) U f) (hω : IsCrForm (some r) V ω) :
    IsCrForm (some r) U (pullback f ω) := by
  refine ⟨hU, fun I => ?_⟩
  have hdf : CrOn r U (totalDerivative f) := hf.2
  have hfr : CrOn r U f := (crOn_iff_contDiffOn r U f hU).mpr
    (((crOn_iff_contDiffOn (r+1) U f hU).mp hf).of_le (by exact_mod_cast Nat.le_succ r))
  exact isCrForm_evaluation r U V f ω
    (fun i x => totalDerivative f x (standardBasis m (indexTuple I i))) hU hmap hfr hω
    (fun i => (crOn_iff_contDiffOn r U _ hU).mpr
      (((crOn_iff_contDiffOn r U _ hU).mp hdf).clm_apply contDiffOn_const))

theorem pullback_continuous {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k) (hU : IsOpen U) (hmap : MapsTo f U V)
    (hf : CrOn 1 U f) (hω : IsCrForm (some 0) V ω) :
    IsCrForm (some 0) U (pullback f ω) :=
  pullback_isCrForm 0 U V f ω hU hmap hf hω

theorem pullback_smooth {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k) (hU : IsOpen U) (hmap : MapsTo f U V)
    (hf : SmoothOn U f) (hω : IsCrForm none V ω) :
    IsCrForm none U (pullback f ω) := by
  refine ⟨hU, fun I r => ?_⟩
  exact (pullback_isCrForm r U V f ω hU hmap (hf (r+1))
    ⟨hω.1, fun J => hω.2 J r⟩).2 I

abbrev roughMap := Specs.D04.C13.PullbackCalculus.Model.roughMap

private def lineIn : ℝ →L[ℝ] E 1 :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (standardBasis 1 0)

private def lineOut : E 1 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((standardBasis 1).coord 0)

private theorem lineOut_apply (x : E 1) : lineOut x = x 0 := rfl

private theorem lineIn_apply (t : ℝ) : lineIn t = t • standardBasis 1 0 := rfl

private theorem lineOut_lineIn (t : ℝ) : lineOut (lineIn t) = t := by
  simp [lineOut_apply, lineIn_apply, standardBasis_apply]

private theorem mul_abs_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => s * |s|) (2 * |t|) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · convert (hasDerivAt_id t).mul (hasDerivAt_abs_neg ht) using 1
    all_goals first | rfl | (simp only [id_eq, abs_of_neg ht, mul_one, one_mul]; ring)
  · apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have he : (fun s : ℝ => s⁻¹ • ((0+s) * |0+s| - 0 * |0|)) =ᶠ[𝓝[≠] 0]
        (fun s : ℝ => |s|) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
      simp [smul_eq_mul, hs]
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds |>.congr' he.symm
  · convert (hasDerivAt_id t).mul (hasDerivAt_abs_pos ht) using 1
    all_goals first | rfl | (simp only [id_eq, abs_of_pos ht, mul_one, one_mul]; ring)

private theorem mul_abs_contDiff : ContDiff ℝ 1 (fun s : ℝ => s * |s|) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (mul_abs_hasDerivAt t).differentiableAt, ?_⟩
  have he : deriv (fun s : ℝ => s * |s|) = fun t => 2 * |t| :=
    funext fun t => (mul_abs_hasDerivAt t).deriv
  rw [he]
  exact continuous_const.mul continuous_abs

theorem roughMap_crOn : CrOn 1 Set.univ roughMap := by
  apply (crOn_iff_contDiffOn 1 Set.univ roughMap isOpen_univ).mpr
  exact (lineIn.contDiff.comp (mul_abs_contDiff.comp lineOut.contDiff)).contDiffOn

theorem coordinateOneForm_smooth (n : ℕ) (i : Fin n) :
    IsCrForm none Set.univ (fun _ => coordinateOneForm n i) := by
  refine ⟨isOpen_univ, fun I r => ?_⟩
  exact (crOn_iff_contDiffOn r Set.univ _ isOpen_univ).mpr contDiffOn_const

private theorem roughMap_hasFDerivAt (x : E 1) :
    HasFDerivAt roughMap
      (lineIn.comp (((ContinuousLinearMap.id ℝ ℝ).smulRight (2 * |x 0|)).comp lineOut)) x := by
  have h1 := (mul_abs_hasDerivAt (lineOut x)).hasFDerivAt.comp x lineOut.hasFDerivAt
  have h2 := lineIn.hasFDerivAt.comp x h1
  exact h2

theorem roughMap_pullback (x : E 1) :
    pullback roughMap (fun _ => coordinateOneForm 1 0) x =
      (2 * |x 0|) • coordinateOneForm 1 0 := by
  ext v
  simp only [pullback_apply, coordinateOneForm_apply, smul_apply, smul_eq_mul]
  change (fderiv ℝ roughMap x (v 0)) 0 = _
  rw [(roughMap_hasFDerivAt x).fderiv]
  simp [ContinuousLinearMap.comp_apply, lineIn_apply, lineOut_apply,
    ContinuousLinearMap.smulRight_apply, standardBasis_apply, mul_comm]

/-- The coefficient 2|t| fails to be differentiable at zero, on every open
neighborhood. The incoming coordinate form is smooth by the previous theorem. -/
theorem roughMap_pullback_not_C1 (U : Set (E 1)) (hU : IsOpen U) (h0 : (0 : E 1) ∈ U) :
    ¬ IsCrForm (some 1) U (pullback roughMap (fun _ => coordinateOneForm 1 0)) := by
  intro h
  let I : MultiIndex 1 1 := ⟨Finset.univ, by simp⟩
  let c : E 1 → ℝ := fun x => coefficient (standardBasis 1)
    (pullback roughMap (fun _ => coordinateOneForm 1 0) x) I
  have hc : DifferentiableAt ℝ c 0 :=
    (totalDifferentiableAt_iff_differentiableAt U c 0 hU h0).mp ((h.2 I).1 0 h0)
  have he : (fun t => c (lineIn t)) = fun t : ℝ => 2 * |t| := by
    funext t
    dsimp [c]
    rw [roughMap_pullback]
    change (2 * |(lineIn t) 0|) *
      (standardBasis 1 (indexTuple I 0)) 0 = 2 * |t|
    have hi : indexTuple I 0 = 0 := Subsingleton.elim _ _
    simp [hi, lineIn_apply, standardBasis_apply]
  have hd : DifferentiableAt ℝ (fun t : ℝ => 2 * |t|) 0 := by
    rw [← he]
    have hbase : lineIn (0 : ℝ) = 0 := by simp [lineIn_apply]
    exact (hbase ▸ hc).comp 0 lineIn.differentiableAt
  apply not_differentiableAt_abs_zero
  have := hd.const_mul (1/2 : ℝ)
  convert this using 1
  simp

end D04
