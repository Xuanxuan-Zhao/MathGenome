import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.ExactC1FormsAreClosed
import MathGenome.Internal.MultivariableAnalysis.D04.C13.ClosedAndExactForms
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellStokesC2

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped BigOperators Classical
namespace D04.Cells

/-- Cell integration depends only on the values of the form on its target. -/
theorem cellIntegral_congrOn {r k n} {U : Set (E n)} (c : Cell r k U)
    {α β : FormField n k} (h : EqOn α β U) : cellIntegral c α = cellIntegral c β := by
  apply lowerIntegral_congr
  intro x hx
  change α (cellExtension c x) _ = β (cellExtension c x) _
  rw [extension_on_cube c ⟨x,hx⟩, h (c.toFun ⟨x,hx⟩).property]

theorem chainIntegral_congrOn {r k n} {U : Set (E n)} (C : Chain r k U)
    {α β : FormField n k} (h : EqOn α β U) : chainIntegral α C = chainIntegral β C := by
  simp only [chainIntegral_sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [cellIntegral_congrOn c h]

/-- Two applications of C²-cell Stokes require only C¹ regularity of each form. -/
theorem integral_exteriorDerivative_eq_zero_of_C1_primitive {n k : ℕ}
    (U : Set (E n)) (ω : FormField n (k+1)) (η : FormField n k)
    (hω : IsCrForm (some 1) U ω) (hη : IsCrForm (some 1) U η)
    (heq : EqOn ω (exteriorDerivative η) U) (c : Cell 2 (k+2) U) :
    cellIntegral c (exteriorDerivative ω) = 0 := by
  calc
    _ = chainIntegral ω (cellBoundary c) :=
      cell_stokes c U ω hω (fun x => (c.toFun x).property)
    _ = chainIntegral (exteriorDerivative η) (cellBoundary c) :=
      chainIntegral_congrOn (cellBoundary c) heq
    _ = chainIntegral η (chainBoundarySucc (cellBoundary c)) :=
      chain_stokes (cellBoundary c) U η hη (fun d _ x => (d.toFun x).property)
    _ = 0 := by rw [cellBoundary_boundary, map_zero]

/-- A frame defines a linear parametrization, without an independence assumption. -/
def frameLinear {n m : ℕ} (v : Fin m → E n) : E m →L[ℝ] E n :=
  ((standardBasis m).constr ℝ v).toContinuousLinearMap

@[simp] theorem frameLinear_basis {n m : ℕ} (v : Fin m → E n) (i : Fin m) :
    frameLinear v (standardBasis m i) = v i := by
  exact (standardBasis m).constr_basis ℝ v i

/-- An affine cube is a legitimate C² cell in any open set containing its image. -/
def affineCube {n m : ℕ} (U : Set (E n)) (hU : IsOpen U)
    (a : E n) (v : Fin m → E n) (h : ℝ)
    (hmap : ∀ u ∈ cube m, a + h • frameLinear v u ∈ U) : Cell 2 m U where
  toFun u := ⟨a + h • frameLinear v u, hmap u u.property⟩
  open_target := hU
  positive := by norm_num
  hasExtension := ⟨fun u => a + h • frameLinear v u, univ, isOpen_univ,
    subset_univ _, (contDiff_const.add ((frameLinear v).contDiff.const_smul h)).contDiffOn,
    fun _ => rfl⟩

theorem affineCube_coefficient {n m : ℕ} (U : Set (E n)) (hU : IsOpen U)
    (a : E n) (v : Fin m → E n) (h : ℝ)
    (hmap : ∀ u ∈ cube m, a + h • frameLinear v u ∈ U)
    (α : FormField n m) (u : E m) (hu : u ∈ cube m) :
    cellCoefficient (affineCube U hU a v h hmap) α u =
      h^m * α (a + h • frameLinear v u) v := by
  rw [cellCoefficient_extension_independent _ (fun u => a + h • frameLinear v u)
    univ isOpen_univ (subset_univ _) 
    (contDiff_const.add ((frameLinear v).contDiff.const_smul h)).contDiffOn
    (fun _ => rfl) α ⟨u,hu⟩]
  have hd : totalDerivative (fun u => a + h • frameLinear v u) u = h • frameLinear v := by
    change fderiv ℝ (fun u => a + h • frameLinear v u) u = _
    convert ((hasFDerivAt_const a u).add
      ((frameLinear v).hasFDerivAt.const_smul h)).fderiv using 1 <;> simp
  simp only [pullback_apply, hd, smul_apply, frameLinear_basis]
  simpa using (α (a + h • frameLinear v u)).map_smul_univ (fun _ => h) v

/-- The image of the unit cube under a frame has a uniform elementary bound. -/
theorem frameLinear_norm_le {n m : ℕ} (v : Fin m → E n)
    (u : E m) (hu : u ∈ cube m) :
    ‖frameLinear v u‖ ≤ ∑ i, ‖v i‖ := by
  have he : frameLinear v u = ∑ i, u i • v i := by
    change (standardBasis m).constr ℝ v u = _
    rw [Module.Basis.constr_apply_fintype]
    rfl
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hu i).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (hu i).2

/-- A continuous form is determined by its integrals on small affine cubes.
The proof uses the fixed sign of a nonzero coefficient near a point. -/
theorem form_eq_zero_of_cellIntegral_eq_zero {n m : ℕ} (U : Set (E n))
    (α : FormField n m) (hα : IsCrForm (some 0) U α)
    (hz : ∀ c : Cell 2 m U, cellIntegral c α = 0) :
    ∀ a ∈ U, α a = 0 := by
  intro a ha
  ext v
  change α a v = 0
  let f : E n → ℝ := fun y => α y v
  have hc : ContinuousOn f U := isCrForm_evaluation 0 U U id α
    (fun i _ => v i) hα.1 (fun _ hy => hy) continuousOn_id hα
    (fun _ => continuousOn_const)
  by_contra hn
  have heps : 0 < |f a| / 2 := half_pos (abs_pos.mpr hn)
  have hnb : {y | y ∈ U ∧ |f y - f a| < |f a| / 2} ∈ 𝓝 a := by
    have ht := (Metric.tendsto_nhds.mp (hc.continuousAt (hα.1.mem_nhds ha)))
      (|f a| / 2) heps
    filter_upwards [hα.1.mem_nhds ha, ht] with y hy hfy
    exact ⟨hy, by simpa only [Real.dist_eq] using hfy⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnb
  let S : ℝ := ∑ i, ‖v i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let h : ℝ := r / (S + 1)
  have hh : 0 < h := div_pos hr (by positivity)
  have hsmall : h * S < r := by
    have he : h * (S+1) = r := div_mul_cancel₀ r (by positivity)
    nlinarith
  have hclose (u : E m) (hu : u ∈ cube m) :
      a + h • frameLinear v u ∈ U ∧
        |f (a + h • frameLinear v u) - f a| < |f a| / 2 := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hh]
    exact (mul_le_mul_of_nonneg_left (frameLinear_norm_le v u hu) hh.le).trans_lt hsmall
  let c : Cell 2 m U := affineCube U hα.1 a v h (fun u hu => (hclose u hu).1)
  have hcoeff (u : E m) (hu : u ∈ cube m) :
      cellCoefficient c α u = h^m * f (a + h • frameLinear v u) :=
    affineCube_coefficient U hα.1 a v h _ α u hu
  have hi := cellCoefficient_integrable c α hα
  have hp : 0 < h^m := pow_pos hh m
  have hzero : Darboux.integral (cellCoefficient c α) (cubeBox m) hi = 0 := hz c
  have hconst := Darboux.constant_integrals (cubeBox m) (h^m * (f a / 2))
  have hvol : Darboux.content (cubeBox m) = 1 := by
    simp [Darboux.content, Specs.D04.C06.DarbouxIntegral.Model.content,
      cubeBox, Specs.D04.C15.CellsChainsAndIntegrals.Model.cubeBox]
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hle := Darboux.integral_mono hi
      (Darboux.integrable_const (cubeBox m) (h^m * (f a / 2))) (fun u hu => by
        rw [hcoeff u hu]
        apply mul_le_mul_of_nonneg_left _ hp.le
        have ht := (abs_lt.mp (hclose u hu).2).2
        rw [abs_of_neg hneg] at ht
        linarith)
    rw [hzero] at hle
    change (0 : ℝ) ≤ Darboux.lowerIntegral (fun _ => h^m * (f a / 2)) (cubeBox m) at hle
    rw [hconst.1, hvol, mul_one] at hle
    have : h^m * (f a / 2) < 0 := mul_neg_of_pos_of_neg hp (by linarith)
    linarith
  · have hle := Darboux.integral_mono
      (Darboux.integrable_const (cubeBox m) (h^m * (f a / 2))) hi (fun u hu => by
        rw [hcoeff u hu]
        apply mul_le_mul_of_nonneg_left _ hp.le
        have ht := (abs_lt.mp (hclose u hu).2).1
        rw [abs_of_pos hpos] at ht
        linarith)
    rw [hzero] at hle
    change Darboux.lowerIntegral (fun _ => h^m * (f a / 2)) (cubeBox m) ≤ 0 at hle
    rw [hconst.1, hvol, mul_one] at hle
    have : 0 < h^m * (f a / 2) := mul_pos hp (by linarith)
    linarith

end D04.Cells

namespace D04
/-- A C¹ exact form is closed even when its primitive is only C¹. -/
theorem exteriorDerivative_eq_zero_of_C1_primitive {n k : ℕ}
    (U : Set (E n)) (ω : FormField n (k+1)) (η : FormField n k)
    (hω : IsCrForm (some 1) U ω) (hη : IsCrForm (some 1) U η)
    (heq : EqOn ω (exteriorDerivative η) U) :
    ∀ x ∈ U, exteriorDerivative ω x = 0 := by
  exact Cells.form_eq_zero_of_cellIntegral_eq_zero U (exteriorDerivative ω)
    (exteriorDerivative_continuous U ω hω)
    (Cells.integral_exteriorDerivative_eq_zero_of_C1_primitive U ω η hω hη heq)

theorem isClosedForm_of_isExactForm {n k : ℕ} (U : Set (E n))
    (ω : FormField n (k+1)) (hω : IsCrForm (some 1) U ω)
    (h : IsExactForm U ω) : IsClosedForm U ω := by
  obtain ⟨η, hη, heq⟩ := h
  exact ⟨hω, exteriorDerivative_eq_zero_of_C1_primitive U ω η hω hη heq⟩
end D04
