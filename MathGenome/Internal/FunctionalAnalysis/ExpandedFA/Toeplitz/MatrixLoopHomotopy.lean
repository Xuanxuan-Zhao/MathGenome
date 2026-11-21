import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.MatrixLoopHomotopy
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Monoid
noncomputable section
open scoped unitInterval
open unitInterval

namespace ExpandedFA.Toeplitz.MatrixLoops

@[simp] theorem phase_toUnits (z : Circle) : phase (Circle.toUnits z) = z := by
  apply Circle.ext
  change (z : ℂ) / (‖(z : ℂ)‖ : ℂ) = (z : ℂ)
  simp

@[simp] theorem determinant_diagonal : Spec.DeterminantDiagonal := by
  intro n u
  apply Units.ext
  change Matrix.det (Matrix.diagonal (fun j : Fin (n + 1) =>
    if j = 0 then (u : ℂ) else 1)) = (u : ℂ)
  simp

/-- Determinants of a matrix homotopy remain nonzero throughout. -/
theorem determinant_homotopy : Spec.DeterminantHomotopy := by
  intro n f g h
  exact (ContinuousMap.Homotopic.refl (determinant n)).comp h

/-- A real-valued argument lift measures winding by its total increment. -/
theorem winding_eq_lift (f : C(Circle, ℂˣ)) (a : C(I, ℝ))
    (ha : ∀ t, Circle.exp (a t) = phase (f (circleParam t))) :
    (winding f : ℝ) = (a 1 - a 0) / (2 * Real.pi) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  apply AddCircle.windingNumber_eq_div _ a
  funext t
  apply AddCircle.homeomorphCircle'.injective
  simpa only [Function.comp_apply, AddCircle.homeomorphCircle'_apply_mk,
    Path.map_coe, ContinuousMap.coe_comp, Homeomorph.apply_symm_apply] using ha t

/-- In particular the chosen winding convention sends `z^k` to `k`. -/
@[simp] theorem winding_power : Spec.WindingPower := by
  intro k
  have h := winding_eq_lift (powerLoop k)
    ⟨fun t => (k : ℝ) * (t : ℝ) * (2 * Real.pi), by fun_prop⟩ (by
      intro t
      simp only [ContinuousMap.coe_mk, powerLoop, phase_toUnits, circleParam]
      change Circle.exp ((k : ℝ) * (t : ℝ) * (2 * Real.pi)) =
        Circle.exp (2 * Real.pi * (t : ℝ)) ^ k
      rw [← Circle.exp_intCast_mul]
      congr 1
      ring)
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have hk : ((winding (powerLoop k) : ℤ) : ℝ) = (k : ℝ) := by
    simpa [hp] using h
  exact_mod_cast hk

@[simp] theorem determinant_normalForm (n : ℕ) (k : ℤ) :
    (determinant n).comp (normalForm n k) = powerLoop k := by
  apply ContinuousMap.ext
  intro z
  exact determinant_diagonal n _

@[simp] theorem winding_determinant_normalForm (n : ℕ) (k : ℤ) :
    winding ((determinant n).comp (normalForm n k)) = k := by
  rw [determinant_normalForm, winding_power]

private def radialScale (t : I) (u : ℂˣ) : ℝ :=
  (1 - (t : ℝ)) * ‖(u : ℂ)‖ + (t : ℝ)

private theorem radialScale_pos (t : I) (u : ℂˣ) : 0 < radialScale t u := by
  have hu : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr u.ne_zero
  rcases lt_or_eq_of_le t.2.2 with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) hu) t.2.1
  · simp [radialScale, h]

/-- Explicit radial deformation of the punctured plane to its unit circle. -/
def radialHomotopy (f : C(Circle, ℂˣ)) :
    f.Homotopy (unitEmbedding.comp (phase.comp f)) where
  toFun p := Units.mk0
    ((radialScale p.1 (f p.2) : ℂ) * (phase (f p.2) : ℂ))
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (radialScale_pos _ _).ne')
      (phase _).coe_ne_zero)
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    have hr : Continuous (fun p : I × Circle =>
        (radialScale p.1 (f p.2) : ℂ) * (phase (f p.2) : ℂ)) := by
      apply Continuous.mul
      · apply Complex.continuous_ofReal.comp
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (Units.continuous_val.comp (f.continuous.comp continuous_snd)).norm).add
          (continuous_subtype_val.comp continuous_fst)
      · exact continuous_subtype_val.comp
          (phase.continuous.comp (f.continuous.comp continuous_snd))
    exact ⟨hr, hr.inv₀ (fun p =>
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (radialScale_pos _ _).ne')
        (phase _).coe_ne_zero)⟩
  map_zero_left z := by
    apply Units.ext
    change (radialScale 0 (f z) : ℂ) * ((f z : ℂ) / (‖(f z : ℂ)‖ : ℂ)) = (f z : ℂ)
    simp [radialScale, mul_div_cancel₀, (norm_ne_zero_iff.mpr (f z).ne_zero)]
  map_one_left z := by
    apply Units.ext
    change (radialScale 1 (f z) : ℂ) * (phase (f z) : ℂ) = (phase (f z) : ℂ)
    simp [radialScale]

/-- Removing the winding power leaves a globally continuous real argument.
The argument is obtained by covering-space lifting on `ℝ`, then descending
its endpoint-matched residual from `[0,2π]` to the circle. -/
theorem exists_phase_factorization (f : C(Circle, ℂˣ)) :
    ∃ a : C(Circle, ℝ), ∀ z,
      phase (f z) = Circle.exp (a z) * z ^ winding f := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let F : C(ℝ, Circle) := (phase.comp f).comp Circle.exp
  obtain ⟨r, hr, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F (0 : ℝ) (Complex.arg (F 0)) (Circle.exp_arg (F 0))
  have hrx (x : ℝ) : Circle.exp (r x) = phase (f (Circle.exp x)) :=
    congrFun hr.2 x
  have hw := winding_eq_lift f
    ⟨fun t => r (2 * Real.pi * (t : ℝ)), r.continuous.comp (by fun_prop)⟩
    (by intro t; exact hrx _)
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have hend : r (2 * Real.pi) - r 0 = (winding f : ℝ) * (2 * Real.pi) := by
    simpa using ((eq_div_iff hp).mp hw).symm
  let b : ℝ → ℝ := fun x => r x - (winding f : ℝ) * x
  have hb : b 0 = b (2 * Real.pi) := by
    dsimp only [b]
    linarith
  let B : C(AddCircle (2 * Real.pi), ℝ) :=
    ⟨AddCircle.liftIco (2 * Real.pi) 0 b,
      AddCircle.liftIco_zero_continuous hb
        ((r.continuous.sub (continuous_const.mul continuous_id)).continuousOn)⟩
  refine ⟨B.comp (AddCircle.homeomorphCircle'.symm : C(Circle, AddCircle (2 * Real.pi))), ?_⟩
  intro z
  obtain ⟨x, hx, hxe⟩ := AddCircle.eq_coe_Ico (AddCircle.homeomorphCircle'.symm z)
  have hz : Circle.exp x = z := by
    change AddCircle.homeomorphCircle' (x : AddCircle (2 * Real.pi)) = z
    rw [hxe, Homeomorph.apply_symm_apply]
  rw [← hz]
  change phase (f (Circle.exp x)) =
    Circle.exp (AddCircle.liftIco (2 * Real.pi) 0 b
      (AddCircle.homeomorphCircle'.symm (Circle.exp x))) * Circle.exp x ^ winding f
  have he : AddCircle.homeomorphCircle'.symm (Circle.exp x) =
      (x : AddCircle (2 * Real.pi)) := by
    rw [← AddCircle.homeomorphCircle'_apply_mk, Homeomorph.symm_apply_apply]
  rw [he, AddCircle.liftIco_zero_coe_apply hx, ← hrx,
    ← Circle.exp_intCast_mul, ← Circle.exp_add]
  congr 1
  dsimp only [b]
  ring

/-- The full scalar nonvanishing-loop classification. -/
theorem scalar_classification : Spec.ScalarClassification := by
  intro f
  obtain ⟨a, ha⟩ := exists_phase_factorization f
  let H : (unitEmbedding.comp (phase.comp f)).Homotopy (powerLoop (winding f)) :=
    { toFun := fun p => Circle.toUnits
        (Circle.exp ((1 - (p.1 : ℝ)) * a p.2) * p.2 ^ winding f)
      continuous_toFun := by
        apply unitEmbedding.continuous.comp
        exact (Circle.exp.continuous.comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            (a.continuous.comp continuous_snd))).mul (continuous_snd.zpow _)
      map_zero_left := by
        intro z
        change Circle.toUnits _ = Circle.toUnits (phase (f z))
        congr 1
        simpa using (ha z).symm
      map_one_left := by
        intro z
        change Circle.toUnits _ = Circle.toUnits (z ^ winding f)
        simp }
  exact ⟨(radialHomotopy f).trans H⟩

/-- The lift of a homotopy square has constant argument increment around each
circle; uniqueness of covering lifts proves this without differentiability. -/
theorem winding_homotopy : Spec.WindingHomotopy := by
  intro f g ⟨H⟩
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let F : C(I × I, Circle) :=
    phase.comp (H.toContinuousMap.comp
      ⟨fun p => (p.1, circleParam p.2), continuous_fst.prodMk
        (circleParam.continuous.comp continuous_snd)⟩)
  obtain ⟨r, hr, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F (0, 0) (Complex.arg (F (0, 0))) (Circle.exp_arg (F (0, 0)))
  have hrx (t s : I) : Circle.exp (r (t, s)) = phase (H (t, circleParam s)) :=
    congrFun hr.2 (t, s)
  have hc : Continuous (fun t : I => r (t, 1) - r (t, 0)) :=
    (r.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (r.continuous.comp (continuous_id.prodMk continuous_const))
  have he (t : I) : Circle.exp (r (t, 1) - r (t, 0)) = 1 := by
    rw [Circle.exp_sub, hrx, hrx]
    simp
  have heq := Circle.isCoveringMap_exp.const_of_comp hc
    (fun t s => (he t).trans (he s).symm) (0 : I) 1
  have hf := winding_eq_lift f
    ⟨fun s => r (0, s), r.continuous.comp (continuous_const.prodMk continuous_id)⟩
    (by intro s; simpa using hrx 0 s)
  have hg := winding_eq_lift g
    ⟨fun s => r (1, s), r.continuous.comp (continuous_const.prodMk continuous_id)⟩
    (by intro s; simpa using hrx 1 s)
  have hw : (winding f : ℝ) = (winding g : ℝ) := by
    rw [hf, hg]
    exact congrArg (fun x : ℝ => x / (2 * Real.pi)) heq
  exact_mod_cast hw

/-- In dimension one the determinant reconstructs the entire matrix. -/
@[simp] theorem diagonal_determinant_dimension_one (A : MatrixGroup 0) :
    diagonal 0 (determinant 0 A) = A := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hi : i = 0 := Fin.fin_one_eq_zero i
  have hj : j = 0 := Fin.fin_one_eq_zero j
  subst i
  subst j
  change (Matrix.diagonal (fun k : Fin 1 => if k = 0 then
    Matrix.det (A : Matrix (Fin 1) (Fin 1) ℂ) else 1)) 0 0 = A.val 0 0
  simp

/-- The full assigned classification is proved for all one-by-one symbols. -/
theorem dimension_one_classification : Spec.DimensionOneClassification := by
  intro Φ
  have h := (ContinuousMap.Homotopic.refl (diagonal 0)).comp
    (scalar_classification ((determinant 0).comp Φ))
  have hΦ : (diagonal 0).comp ((determinant 0).comp Φ) = Φ := by
    apply ContinuousMap.ext
    intro z
    exact diagonal_determinant_dimension_one (Φ z)
  rw [hΦ] at h
  exact h

/-- Once a matrix loop has been reduced to one scalar entry, its exponent is
forced to be the winding of the original determinant. This is the final assembly
step; its scalar-reduction premise is proved below by dimension induction. -/
theorem classification_of_scalar_reduction (reduce : Spec.ScalarReduction) :
    Spec.Classification := by
  intro n Φ
  obtain ⟨u, h⟩ := reduce n Φ
  have hw := winding_homotopy _ _ (determinant_homotopy n _ _ h)
  have hu : (determinant n).comp ((diagonal n).comp u) = u := by
    apply ContinuousMap.ext
    intro z
    exact determinant_diagonal n _
  rw [hu] at hw
  rw [hw]
  exact h.trans ((ContinuousMap.Homotopic.refl (diagonal n)).comp
    (scalar_classification u))

section PolarDeformation

-- These scoped instances use the operator norm and the positive-semidefinite
-- order. Their topology agrees with the native matrix topology in the Specs.
open scoped Matrix.Norms.L2Operator MatrixOrder

variable {n : ℕ}
private abbrev MatrixAlgebra (n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) ℂ

private theorem gram_positive (a : MatrixGroup n) :
    IsStrictlyPositive (star (a : MatrixAlgebra n) * a) :=
  (a.isUnit.star.mul a.isUnit).isStrictlyPositive (star_mul_self_nonneg _)

private def polarRoot (a : MatrixGroup n) : MatrixGroup n :=
  ((gram_positive a).isUnit_cfcSqrt _).unit

private theorem polarRoot_nonneg (a : MatrixGroup n) :
    (0 : MatrixAlgebra n) ≤ polarRoot a := by
  simpa only [polarRoot, IsUnit.unit_spec] using CFC.sqrt_nonneg (star (a : MatrixAlgebra n) * a)

private theorem polarRoot_sq (a : MatrixGroup n) :
    (polarRoot a : MatrixAlgebra n) * polarRoot a = star (a : MatrixAlgebra n) * a := by
  simpa only [polarRoot, IsUnit.unit_spec] using
    CFC.sqrt_mul_sqrt_self (star (a : MatrixAlgebra n) * a) (star_mul_self_nonneg _)

private theorem continuous_polarRoot : Continuous (polarRoot (n := n)) := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun a : MatrixGroup n => (polarRoot a : MatrixAlgebra n)) := by
    simp only [polarRoot, IsUnit.unit_spec]
    exact CFC.continuousOn_sqrt.comp_continuous
      (Units.continuous_val.star.mul Units.continuous_val) (fun a => show (0 : MatrixAlgebra n) ≤ star (a : MatrixAlgebra n) * (a : MatrixAlgebra n) from
        star_mul_self_nonneg _)
  refine ⟨h, continuous_iff_continuousAt.mpr fun a => ?_⟩
  have hi : ContinuousAt (Ring.inverse : MatrixAlgebra n → MatrixAlgebra n) (polarRoot a : MatrixAlgebra n) :=
    NormedRing.inverse_continuousAt (polarRoot a)
  simpa only [Function.comp_def, Ring.inverse_unit] using (hi.comp (x := a) h.continuousAt)

private def polarUnit (a : MatrixGroup n) : MatrixGroup n := a * (polarRoot a)⁻¹

private theorem polarUnit_unitary (a : MatrixGroup n) : (polarUnit a : MatrixAlgebra n) ∈ unitary (MatrixAlgebra n) := by
  apply (polarUnit a).isUnit.mem_unitary_of_star_mul_self
  have hs : star (polarRoot a : MatrixAlgebra n) = polarRoot a := (polarRoot_nonneg a).isSelfAdjoint.star_eq
  have hsi : star ((polarRoot a)⁻¹ : MatrixGroup n) = (polarRoot a)⁻¹ := by
    rw [star_inv]
    congr 1
    exact Units.ext hs
  change star ((a : MatrixAlgebra n) * (polarRoot a).inv) * ((a : MatrixAlgebra n) * (polarRoot a).inv) = 1
  have hsiM : star ((polarRoot a).inv : MatrixAlgebra n) = (polarRoot a).inv :=
    congrArg (fun u : MatrixGroup n => (u : MatrixAlgebra n)) hsi
  rw [star_mul, hsiM, mul_assoc, ← mul_assoc (star (a : MatrixAlgebra n)),
    ← polarRoot_sq a, ← mul_assoc]
  simp

private theorem polarRoot_inv_positive (a : MatrixGroup n) :
    IsStrictlyPositive ((polarRoot a).inv : MatrixAlgebra n) := by
  have h := ((polarRoot a).isStrictlyPositive_of_le (polarRoot_nonneg a)).ringInverse
  rw [Ring.inverse_unit] at h
  exact h

private def polarBlend (t : I) (a : MatrixGroup n) : MatrixAlgebra n :=
  (1 - (t : ℝ)) • (1 : MatrixAlgebra n) + (t : ℝ) • (polarRoot a).inv

private theorem polarBlend_positive (t : I) (a : MatrixGroup n) :
    IsStrictlyPositive (polarBlend t a) := by
  rcases lt_or_eq_of_le t.2.2 with h | h
  · exact (IsStrictlyPositive.smul (sub_pos.mpr h) isStrictlyPositive_one).add_nonneg
      (smul_nonneg t.2.1 (polarRoot_inv_positive a).nonneg)
  · simpa [polarBlend, h] using polarRoot_inv_positive a

private def polarBlendUnit (t : I) (a : MatrixGroup n) : MatrixGroup n :=
  (polarBlend_positive t a).isUnit.unit

private theorem continuous_polarBlendUnit :
    Continuous (fun p : I × MatrixGroup n => polarBlendUnit p.1 p.2) := by
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  change Continuous (fun p : I × MatrixGroup n => polarBlend p.1 p.2)
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    continuous_const).add ((continuous_subtype_val.comp continuous_fst).smul
      (Units.continuous_val.comp (show Continuous (fun p : I × MatrixGroup n => (polarRoot p.2)⁻¹) from
        continuous_polarRoot.inv.comp continuous_snd)))

private def polarMap : C(MatrixGroup n, MatrixGroup n) :=
  ⟨polarUnit, continuous_id.mul continuous_polarRoot.inv⟩

private def polarHomotopy : (ContinuousMap.id (MatrixGroup n)).Homotopy polarMap where
  toFun p := p.2 * polarBlendUnit p.1 p.2
  continuous_toFun := continuous_snd.mul continuous_polarBlendUnit
  map_zero_left a := by
    apply Units.ext
    change (a : MatrixAlgebra n) * (polarBlendUnit 0 a : MatrixAlgebra n) = a
    simp [polarBlendUnit, polarBlend]
  map_one_left a := by
    apply Units.ext
    change (a : MatrixAlgebra n) * (polarBlendUnit 1 a : MatrixAlgebra n) = (a : MatrixAlgebra n) * (polarRoot a).inv
    simp [polarBlendUnit, polarBlend]

/-- The polar unitary is a continuous unitary-valued map, with no chosen
frames or pointwise eigenvectors in its continuity proof. -/
private def polarUnitaryMap : C(MatrixGroup n, UnitaryMatrixGroup n) where
  toFun a := ⟨polarUnit a, polarUnit_unitary a⟩
  continuous_toFun := (Units.continuous_val.comp polarMap.continuous).subtype_mk _

/-- Polar decomposition deforms an arbitrary continuous matrix loop to a unitary
loop through actual invertible matrices in every positive dimension. -/
theorem unitary_reduction : Spec.UnitaryReduction := by
  intro n Φ
  refine ⟨polarUnitaryMap.comp Φ, ?_⟩
  have he : (unitaryEmbedding n).comp (polarUnitaryMap.comp Φ) = polarMap.comp Φ := by
    apply ContinuousMap.ext
    intro z
    apply Units.ext
    rfl
  rw [he]
  exact ⟨polarHomotopy.compContinuousMap Φ⟩

end PolarDeformation

end ExpandedFA.Toeplitz.MatrixLoops



noncomputable section
open scoped ComplexConjugate
open Matrix
namespace ExpandedFA.Toeplitz.MatrixLoops.UnitaryTransport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev E (ι : Type*) := EuclideanSpace ℂ ι
def outer (v : E ι) : Matrix ι ι ℂ := Matrix.vecMulVec v (star v)
omit [Fintype ι] [DecidableEq ι] in
lemma outer_star (v : E ι) : star (outer v) = outer v := by
  change (outer v)ᴴ = outer v
  simp [outer, Matrix.conjTranspose_vecMulVec]
omit [DecidableEq ι] in
lemma outer_sq (v : E ι) : outer v * outer v = (inner ℂ v v) • outer v := by
  rw [outer, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  congr 1
  rw [dotProduct_comm]
  exact (EuclideanSpace.inner_eq_star_dotProduct v v).symm
lemma outer_inner (v x : E ι) : Matrix.toEuclideanLin (outer v) x = (inner ℂ v x) • v := by
  unfold outer
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne]
  simp
lemma unitary_rank_adjust (v : E ι) (a : ℂ)
    (h : a + star a = (star a * a) * inner ℂ v v) :
    1 - a • outer v ∈ unitary (Matrix ι ι ℂ) := by
  apply Unitary.mem_iff.mpr
  have h₁ : star (1 - a • outer v) = 1 - star a • outer v := by
    simp [star_sub, star_smul, outer_star]
  have ha : a * (star a * inner ℂ v v) = a + star a := by
    rw [← mul_assoc, mul_comm a (star a), ← h]
  have hb : star a * (a * inner ℂ v v) = a + star a := by
    rw [← mul_assoc, ← h]
  have h₂ : (1 - star a • outer v) * (1 - a • outer v) = 1 := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, outer_sq]
    rw [ha, add_smul]
    abel
  exact ⟨by rw [h₁]; exact h₂, by
    rw [h₁, sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, outer_sq]
    rw [hb, add_smul]
    abel⟩
def pairDenom (v w : E ι) : ℂ := 1 + inner ℂ w v

def pairReflect (v w : E ι) : Matrix ι ι ℂ :=
  1 - (pairDenom v w)⁻¹ • outer (v + w)

omit [DecidableEq ι] in
lemma unit_inner (v : E ι) (hv : ‖v‖ = 1) : inner ℂ v v = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hv]
  norm_num

lemma pairReflect_unitary (v w : E ι) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hne : pairDenom v w ≠ 0) : pairReflect v w ∈ unitary (Matrix ι ι ℂ) := by
  apply unitary_rank_adjust
  have hd : inner ℂ (v + w) (v + w) = pairDenom v w + star (pairDenom v w) := by
    simp only [inner_add_left, inner_add_right, unit_inner v hv, unit_inner w hw,
      pairDenom, star_add, star_one]
    have hc : star (inner ℂ w v) = inner ℂ v w := by
      simpa only [starRingEnd_apply] using inner_conj_symm v w
    rw [hc]
    ring
  rw [hd]
  simp only [star_inv₀]
  have hs : star (pairDenom v w) ≠ 0 := star_ne_zero.mpr hne
  field_simp
  ring

lemma pairReflect_apply (v w : E ι) (hv : ‖v‖ = 1)
    (hne : pairDenom v w ≠ 0) : Matrix.toEuclideanLin (pairReflect v w) v = -w := by
  simp only [pairReflect, map_sub, map_smul, Matrix.toEuclideanLin, Matrix.toLpLin_one,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]
  change v - (pairDenom v w)⁻¹ • Matrix.toEuclideanLin (outer (v + w)) v = -w
  rw [outer_inner, inner_add_left, unit_inner v hv, ← pairDenom, smul_smul,
    inv_mul_cancel₀ hne, one_smul]
  abel

lemma selfReflect_sq (v : E ι) (hv : ‖v‖ = 1) :
    (1 - (2 : ℂ) • outer v) * (1 - (2 : ℂ) • outer v) = 1 := by
  have hh : (2 : ℂ) + star (2 : ℂ) = (star (2 : ℂ) * 2) * inner ℂ v v := by
    rw [unit_inner v hv]
    norm_num
  have hu := (Unitary.mem_iff.mp (unitary_rank_adjust v 2 hh)).1
  simpa [star_sub, star_smul, outer_star] using hu

lemma selfReflect_unitary (v : E ι) (hv : ‖v‖ = 1) :
    1 - (2 : ℂ) • outer v ∈ unitary (Matrix ι ι ℂ) := by
  apply unitary_rank_adjust
  rw [unit_inner v hv]
  norm_num

lemma selfReflect_apply (v : E ι) (hv : ‖v‖ = 1) :
    Matrix.toEuclideanLin (1 - (2 : ℂ) • outer v) v = -v := by
  simp only [map_sub, map_smul, Matrix.toEuclideanLin, Matrix.toLpLin_one,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]
  change v - (2 : ℂ) • Matrix.toEuclideanLin (outer v) v = -v
  rw [outer_inner, unit_inner v hv, one_smul]
  module

def transporter (v w : E ι) : Matrix ι ι ℂ :=
  pairReflect v w * (1 - (2 : ℂ) • outer v)

lemma transporter_unitary (v w : E ι) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hne : pairDenom v w ≠ 0) : transporter v w ∈ unitary (Matrix ι ι ℂ) := by
  exact mul_mem (pairReflect_unitary v w hv hw hne) (selfReflect_unitary v hv)

lemma transporter_apply (v w : E ι) (hv : ‖v‖ = 1)
    (hne : pairDenom v w ≠ 0) : Matrix.toEuclideanLin (transporter v w) v = w := by
  rw [transporter, Matrix.toEuclideanLin, Matrix.toLpLin_mul 2 2 2]
  change Matrix.toEuclideanLin (pairReflect v w)
    (Matrix.toEuclideanLin (1 - (2 : ℂ) • outer v) v) = w
  rw [selfReflect_apply v hv, map_neg, pairReflect_apply v w hv hne, neg_neg]

lemma pairReflect_self (v : E ι) (hv : ‖v‖ = 1) :
    pairReflect v v = 1 - (2 : ℂ) • outer v := by
  rw [pairReflect, pairDenom, unit_inner v hv]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, outer,
    Matrix.vecMulVec_apply, PiLp.add_apply, Pi.star_apply, star_add]
  norm_num
  ring

lemma transporter_self (v : E ι) (hv : ‖v‖ = 1) : transporter v v = 1 := by
  rw [transporter, pairReflect_self v hv]
  exact selfReflect_sq v hv

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_outer : Continuous (outer : E ι → Matrix ι ι ℂ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun v : E ι => v i * star (v j))
  fun_prop

omit [DecidableEq ι] in
lemma continuous_pairDenom : Continuous (fun p : E ι × E ι => pairDenom p.1 p.2) := by
  unfold pairDenom
  fun_prop

lemma continuous_transporter {X : Type*} [TopologicalSpace X] {v w : X → E ι}
    (hv : Continuous v) (hw : Continuous w)
    (hne : ∀ x, pairDenom (v x) (w x) ≠ 0) :
    Continuous (fun x => transporter (v x) (w x)) := by
  unfold transporter pairReflect
  apply Continuous.mul
  · apply Continuous.sub continuous_const
    apply continuous_matrix
    intro i j
    exact ((continuous_pairDenom.comp (hv.prodMk hw)).inv₀ hne).mul
      ((continuous_outer.comp (hv.add hw)).matrix_elem i j)
  · apply Continuous.sub continuous_const
    apply continuous_matrix
    intro i j
    exact continuous_const.mul ((continuous_outer.comp hv).matrix_elem i j)

open ExpandedFA.Toeplitz.MatrixLoops in
 theorem local_unitary_transport : Spec.LocalUnitaryTransport := by
  intro n
  let V : Set (UnitColumn n × UnitColumn n) :=
    {p | pairDenom p.1.val p.2.val ≠ 0}
  have hc : Continuous (fun p : UnitColumn n × UnitColumn n =>
      pairDenom p.1.val p.2.val) :=
    continuous_pairDenom.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  have hopen : IsOpen V := isOpen_ne.preimage hc
  have hdiag : ∀ v : UnitColumn n, (v, v) ∈ V := by
    intro v
    change 1 + inner ℂ v.val v.val ≠ 0
    rw [unit_inner v.val v.property]
    norm_num
  let L : C(V, UnitaryMatrixGroup n) :=
    { toFun := fun p => ⟨transporter p.val.1.val p.val.2.val,
        transporter_unitary _ _ p.val.1.property p.val.2.property p.property⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply continuous_transporter
        · exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
        · exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
        · exact fun p => p.property }
  refine ⟨V, hopen, hdiag, L, ?_, ?_⟩
  · intro p
    exact transporter_apply _ _ p.val.1.property p.property
  · intro p hp
    apply Subtype.ext
    change transporter p.val.1.val p.val.2.val = 1
    rw [← hp]
    exact transporter_self _ p.val.1.property

end ExpandedFA.Toeplitz.MatrixLoops.UnitaryTransport


open scoped unitInterval Topology ContDiff
open unitInterval
open Set Metric
noncomputable section
namespace ExpandedFA.Toeplitz.MatrixLoops.SphereContraction
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := {v : E | ‖v‖ = 1}

omit [NormedSpace ℝ E] in
@[simp] lemma norm_unit (v : UnitSphere E) : ‖v.val‖ = 1 := v.2

/-- Radial normalization of a nonzero vector. -/
def normalize (v : E) (hv : v ≠ 0) : UnitSphere E :=
  ⟨‖v‖⁻¹ • v, norm_smul_inv_norm (𝕜 := ℝ) hv⟩

/-- A segment between unit vectors avoids zero when the endpoints are not antipodal. -/
lemma unit_segment_ne_zero {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hne : v ≠ -w) (t : I) : (1 - (t : ℝ)) • v + (t : ℝ) • w ≠ 0 := by
  intro h
  have he : (1 - (t : ℝ)) • v = (t : ℝ) • (-w) := by
    simpa only [smul_neg] using eq_neg_of_add_eq_zero_left h
  have hh := congrArg norm he
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.2.2),
    abs_of_nonneg t.2.1, norm_neg, hv, hw, mul_one] at hh
  have ht : (t : ℝ) = 1 / 2 := by linarith
  apply hne
  apply smul_right_injective E (show (1 / 2 : ℝ) ≠ 0 by norm_num)
  convert he using 1 <;> norm_num [ht]

/-- Straight interpolation stays nonzero when the second endpoint lies within distance one
of a unit vector. The second endpoint need not have unit norm. -/
lemma close_segment_ne_zero {v w : E} (hv : ‖v‖ = 1)
    (hvw : dist v w < 1) (t : I) : (1 - (t : ℝ)) • v + (t : ℝ) • w ≠ 0 := by
  intro h
  have h' : v + (t : ℝ) • (w-v) = 0 := by
    convert h using 1
    rw [smul_sub, sub_smul, one_smul]
    abel
  have he := congrArg norm (eq_neg_of_add_eq_zero_left h')
  rw [hv, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1] at he
  have hd : ‖w-v‖ < 1 := by simpa only [dist_eq_norm, norm_sub_rev] using hvw
  have hmul : (t : ℝ) * ‖w-v‖ ≤ ‖w-v‖ := mul_le_of_le_one_left (norm_nonneg _) t.2.2
  linarith

/-- Normalize straight interpolation between nonantipodal sphere-valued maps. -/
def unitHomotopy (f g : C(X, UnitSphere E))
    (hne : ∀ x, (f x).val ≠ -(g x).val) : f.Homotopy g where
  toFun p := normalize ((1 - (p.1 : ℝ)) • (f p.2).val + (p.1 : ℝ) • (g p.2).val)
    (unit_segment_ne_zero (f p.2).property (g p.2).property (hne p.2) p.1)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : I × X =>
        (1 - (p.1 : ℝ)) • (f p.2).val + (p.1 : ℝ) • (g p.2).val) := by fun_prop
    exact (hc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr
      (unit_segment_ne_zero (f p.2).property (g p.2).property (hne p.2) p.1))).smul hc
  map_zero_left := by intro x; apply Subtype.ext; simp [normalize]
  map_one_left := by intro x; apply Subtype.ext; simp [normalize]

/-- A sphere-valued map omitting a point contracts to its antipode. -/
lemma homotopic_const_of_omits (f : C(X, UnitSphere E)) (p : UnitSphere E)
    (hp : ∀ x, f x ≠ p) : f.Homotopic (.const X ⟨-p.val, by simp⟩) := by
  refine ⟨unitHomotopy f (.const X ⟨-p.val, by simp⟩) (fun x he => ?_)⟩
  apply hp x
  apply Subtype.ext
  simpa using he

/-- Smooth approximation on a prescribed compact subset of the complex plane. -/
lemma exists_contDiff_close_on_compact [CompleteSpace E]
    (F : C(ℂ, E)) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(ℂ, E), ContDiff ℝ ∞ g ∧ ∀ z ∈ K, dist (g z) (F z) < ε := by
  have hF : F ∈ closure {g : C(ℂ, E) | ContDiff ℝ ∞ g} :=
    ContinuousMap.dense_setOfPred_contDiff F
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)] at hF
  exact hF (K, ε) ⟨hK, hε⟩

/-- The real cone over a smooth map from the complex plane has Hausdorff dimension at
most three. Consequently it omits a nonzero vector in real dimension at least four. -/
lemma smooth_cone_omits [FiniteDimensional ℝ E] (hd : 3 < Module.finrank ℝ E)
    (g : C(ℂ, E)) (hg : ContDiff ℝ ∞ g) :
    ∃ p : E, p ≠ 0 ∧ ∀ (r : ℝ) (z : ℂ), r • g z ≠ p := by
  let G : ℝ × ℂ → E := fun p => p.1 • g p.2
  have hG : Differentiable ℝ G := differentiable_fst.smul (hg.differentiable (by simp) |>.comp differentiable_snd)
  have hdim : Module.finrank ℝ (ℝ × ℂ) < Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, Complex.finrank_real_complex] using hd
  obtain ⟨p, hp⟩ := (hG.dense_compl_range_of_finrank_lt_finrank hdim).nonempty
  have hp' : ∀ (r : ℝ) (z : ℂ), r • g z ≠ p := by
    intro r z he
    exact hp ⟨(r,z), he⟩
  refine ⟨p, ?_, hp'⟩
  intro h
  exact hp' 0 0 (by simp [h])


def normalizedMap (g : C(X, E)) (hg : ∀ x, g x ≠ 0) : C(X, UnitSphere E) where
  toFun x := normalize (g x) (hg x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (g.continuous.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hg x))).smul g.continuous

def closeHomotopy (f : C(X, UnitSphere E)) (g : C(X, E))
    (hclose : ∀ x, dist (f x).val (g x) < 1)
    (hg : ∀ x, g x ≠ 0) : f.Homotopy (normalizedMap g hg) where
  toFun p := normalize ((1 - (p.1 : ℝ)) • (f p.2).val + (p.1 : ℝ) • g p.2)
    (close_segment_ne_zero (f p.2).property (hclose p.2) p.1)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : I × X =>
        (1 - (p.1 : ℝ)) • (f p.2).val + (p.1 : ℝ) • g p.2) := by fun_prop
    exact (hc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr
      (close_segment_ne_zero (f p.2).property (hclose p.2) p.1))).smul hc
  map_zero_left := by intro x; apply Subtype.ext; simp [normalize]
  map_one_left := by intro x; apply Subtype.ext; simp [normalize, normalizedMap]

lemma normalizedMap_omits (g : C(X, E)) (hg : ∀ x, g x ≠ 0)
    (p : E) (hp : p ≠ 0) (hcone : ∀ (r : ℝ) x, r • g x ≠ p) :
    ∀ x, normalizedMap g hg x ≠ normalize p hp := by
  intro x he
  have he' := congrArg (fun v : UnitSphere E => ‖p‖ • v.val) he
  apply hcone (‖p‖ * ‖g x‖⁻¹) x
  simpa only [normalizedMap, ContinuousMap.coe_mk, normalize, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp), one_smul] using he'

/-- Extend a sphere-valued loop to the plane, approximate smoothly on the circle,
and normalize. A vector outside the smooth cone supplies an omitted sphere point. -/
lemma loop_homotopic_some_const [FiniteDimensional ℝ E]
    (hd : 3 < Module.finrank ℝ E) (f : C(Circle, UnitSphere E)) :
    ∃ q : UnitSphere E, f.Homotopic (.const Circle q) := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let : TietzeExtension E := TietzeExtension.of_homeo e.toHomeomorph
  let f' : C(Circle, E) := ⟨fun z => (f z).val, continuous_subtype_val.comp f.continuous⟩
  obtain ⟨F, hF⟩ := f'.exists_extension (isClosed_sphere.isClosedEmbedding_subtypeVal)
  obtain ⟨g, hg, hclose⟩ := exists_contDiff_close_on_compact F
    (isCompact_sphere (0 : ℂ) 1) (show (0 : ℝ) < 1 by norm_num)
  let g' : C(Circle, E) := ⟨fun z => g z.val, g.continuous.comp continuous_subtype_val⟩
  have hdist (z : Circle) : dist (f z).val (g' z) < 1 := by
    have he : F z.val = (f z).val := congrArg (fun u : C(Circle, E) => u z) hF
    simpa only [g', ContinuousMap.coe_mk, he, dist_comm] using hclose z.val z.property
  have hgnz (z : Circle) : g' z ≠ 0 := by
    simpa using close_segment_ne_zero (f z).property (hdist z) (1 : I)
  obtain ⟨p, hp, hcone⟩ := smooth_cone_omits hd g hg
  have homit : ∀ z, normalizedMap g' hgnz z ≠ normalize p hp :=
    normalizedMap_omits g' hgnz p hp (fun r z => hcone r z.val)
  refine ⟨⟨-(normalize p hp).val, by simp⟩, ?_⟩
  exact (show f.Homotopic (normalizedMap g' hgnz) from ⟨closeHomotopy f g' hdist hgnz⟩).trans
    (homotopic_const_of_omits _ _ homit)

/-- Every sphere-valued complex loop contracts to any chosen unit vector in real
ambient dimension at least four. -/
lemma loop_homotopic_const [FiniteDimensional ℝ E]
    (hd : 3 < Module.finrank ℝ E) (f : C(Circle, UnitSphere E)) (q : UnitSphere E) :
    f.Homotopic (.const Circle q) := by
  obtain ⟨p, hp⟩ := loop_homotopic_some_const hd f
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ E by omega)
  have hpc : IsPathConnected (UnitSphere E) := by
    convert isPathConnected_sphere hrank (0 : E) (show (0 : ℝ) ≤ 1 by norm_num) using 1
    ext v
    simp [UnitSphere]
  let : PathConnectedSpace (UnitSphere E) := isPathConnected_iff_pathConnectedSpace.mp hpc
  exact hp.trans (ContinuousMap.homotopic_const_iff.mpr (PathConnectedSpace.joined p q))

end ExpandedFA.Toeplitz.MatrixLoops.SphereContraction

namespace ExpandedFA.Toeplitz.MatrixLoops
/-- Every loop of unit columns in complex dimension at least two contracts to any
chosen unit column. All homotopy values remain actual unit columns. -/
theorem unitColumn_loop_homotopic_const (n : ℕ) (f : C(Circle, UnitColumn (n+1))) (q : UnitColumn (n+1)) :
    f.Homotopic (.const Circle q) := by
  apply SphereContraction.loop_homotopic_const
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin (n+1+1))),
    Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  omega
end ExpandedFA.Toeplitz.MatrixLoops


open Function Topology unitInterval Set
open scoped unitInterval
noncomputable section

namespace ExpandedFA.Toeplitz.MatrixLoops.CompactHomotopyLift

variable {B X G : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [CompactSpace X] [TopologicalSpace G] [Monoid G] [ContinuousMul G]

lemma exists_pair_cover (H : C(I × X, B)) (V : Set (B × B))
    (hV : IsOpen V) (hd : ∀ b, (b,b) ∈ V) :
    ∃ c : I → Set I, (∀ a, IsOpen (c a)) ∧ (∀ a, a ∈ c a) ∧
      ∀ a s, s ∈ c a → ∀ t, t ∈ c a → ∀ x,
        (H (s,x), H (t,x)) ∈ V := by
  have hF : Continuous (fun z : (I × I) × X => (H (z.1.1,z.2), H (z.1.2,z.2))) := by
    fun_prop
  have hlocal : ∀ a : I, ∃ c : Set I, IsOpen c ∧ a ∈ c ∧
      ∀ s ∈ c, ∀ t ∈ c, ∀ x, (H (s,x), H (t,x)) ∈ V := by
    intro a
    obtain ⟨u,v,hu,hv,hau,hxv,huv⟩ := generalized_tube_lemma
      (isCompact_singleton : IsCompact ({(a,a)} : Set (I × I)))
      (isCompact_univ : IsCompact (univ : Set X)) (hV.preimage hF) (by
        rintro ⟨⟨s,t⟩,x⟩ ⟨hst,_⟩
        have : (s,t) = (a,a) := hst
        cases this
        exact hd _)
    obtain ⟨u₁,u₂,hu₁,hu₂,ha₁,ha₂,hsub⟩ := isOpen_prod_iff.mp hu a a (hau (by simp))
    refine ⟨u₁ ∩ u₂, hu₁.inter hu₂, ⟨ha₁,ha₂⟩, ?_⟩
    intro s hs t ht x
    exact huv (show ((s,t),x) ∈ u ×ˢ v from ⟨hsub ⟨hs.1,ht.2⟩, hxv trivial⟩)
  choose c hc hm he using hlocal
  exact ⟨c,hc,hm,he⟩

 theorem lift_relation (R : G → B → Prop) (H : C(I × X,B)) (f : C(X,G))
    (h0 : ∀ x, R (f x) (H (0,x)))
    (V : Set (B × B)) (hV : IsOpen V) (hd : ∀ b, (b,b) ∈ V)
    (L : C(V,G))
    (hL : ∀ z : V, ∀ g, R g z.val.1 → R (L z * g) z.val.2)
    (hLd : ∀ z : V, z.val.1 = z.val.2 → L z = 1) :
    ∃ F : C(I × X,G), (∀ x, F (0,x) = f x) ∧ ∀ z, R (F z) (H z) := by
  classical
  let l : B × B → G := fun z => if hz : z ∈ V then L ⟨z,hz⟩ else 1
  have lc : ContinuousOn l V := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact L.continuous.congr (by intro z; simp [l])
  have ld : ∀ b, l (b,b) = 1 := by
    intro b
    simp only [l, dite_eq_left (hd b)]
    exact hLd _ rfl
  have lp : ∀ b c, ∀ h : (b,c) ∈ V, ∀ g, R g b → R (l (b,c) * g) c := by
    intro b c h g hp
    simpa only [l, dite_eq_left h] using hL ⟨(b,c),h⟩ g hp
  obtain ⟨c,hc,hm,he⟩ := exists_pair_cover H V hV hd
  obtain ⟨t,t0,tm,⟨N,hN⟩,ts⟩ := exists_monotone_Icc_subset_open_cover_unitInterval hc (by
    intro s _
    exact mem_iUnion.mpr ⟨s,hm s⟩)
  have hex : ∀ n, ∃ F : I × X → G, ContinuousOn F (Icc 0 (t n) ×ˢ univ) ∧
      (∀ z ∈ Icc 0 (t n) ×ˢ univ, R (F z) (H z)) ∧ ∀ x, F (0,x) = f x := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun z => f z.2, (f.continuous.comp continuous_snd).continuousOn, ?_, fun _ => rfl⟩
      intro ⟨s,x⟩ hs
      have : s = 0 := by simpa [t0] using hs.1
      subst s
      exact h0 x
    | succ n ih =>
      obtain ⟨F,Fc,Fp,F0⟩ := ih
      obtain ⟨a,ha⟩ := ts n
      have hleft : t n ∈ c a := ha ⟨le_rfl,tm n.le_succ⟩
      have Fb : Continuous (fun x => F (t n,x)) := by
        rw [← continuousOn_univ]
        exact Fc.comp (Continuous.prodMk_right (t n)).continuousOn (by
          intro x hx
          exact ⟨⟨bot_le,le_rfl⟩,trivial⟩)
      let Q : I × X → G := fun z => l (H (t n,z.2),H z) * F (t n,z.2)
      have Qc : ContinuousOn Q (Icc (t n) (t (n+1)) ×ˢ univ) := by
        apply ContinuousOn.mul
        · exact lc.comp (by fun_prop) (by
            intro z hz
            exact he a (t n) hleft z.1 (ha hz.1) z.2)
        · exact (Fb.comp continuous_snd).continuousOn
      have Qb : ∀ x, Q (t n,x) = F (t n,x) := by
        intro x
        simp [Q,ld]
      refine ⟨fun z => if z.1 ≤ t n then F z else Q z, ?_, ?_, ?_⟩
      · apply ContinuousOn.if
        · intro z hz
          have hz' := mem_ofPred.mp (frontier_le_subset_eq continuous_fst continuous_const hz.2)
          have hzv : z = (t n,z.2) := Prod.ext hz' rfl
          rw [hzv]
          exact (Qb z.2).symm
        · apply Fc.mono
          intro z hz
          rw [closure_le_eq continuous_fst continuous_const] at hz
          exact ⟨⟨hz.1.1.1,hz.2⟩,trivial⟩
        · apply Qc.mono
          intro z hz
          simp_rw [not_le] at hz
          exact ⟨⟨closure_lt_subset_le continuous_const continuous_fst hz.2,hz.1.1.2⟩,trivial⟩
      · intro z hz
        dsimp only
        split_ifs with h
        · exact Fp z ⟨⟨hz.1.1,h⟩,trivial⟩
        · apply lp _ _ (he a (t n) hleft z.1 (ha ⟨le_of_not_ge h,hz.1.2⟩) z.2)
          exact Fp (t n,z.2) ⟨⟨bot_le,le_rfl⟩,trivial⟩
      · intro x
        change (if (0 : I) ≤ t n then F (0,x) else Q (0,x)) = f x
        rw [ite_eq_left (show (0 : I) ≤ t n from (t n).property.1)]
        exact F0 x
  obtain ⟨F,Fc,Fp,F0⟩ := hex N
  have htN : t N = 1 := hN N le_rfl
  have hs : Icc 0 (t N) ×ˢ (univ : Set X) = univ := by
    rw [htN]
    apply Set.eq_univ_of_forall
    intro z
    exact ⟨⟨bot_le,le_top⟩,trivial⟩
  refine ⟨⟨F,continuousOn_univ.mp (hs ▸ Fc)⟩,F0,?_⟩
  intro z
  exact Fp z (hs.symm ▸ mem_univ z)

end ExpandedFA.Toeplitz.MatrixLoops.CompactHomotopyLift

open ExpandedFA.Toeplitz.MatrixLoops

namespace ExpandedFA.Toeplitz.MatrixLoops.UnitaryColumnLifting
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

 theorem unitary_column_lift (ht : Spec.LocalUnitaryTransport)
    (n : ℕ) (e : EuclideanSpace ℂ (Fin (n+1)))
    (H : C(I × X, UnitColumn n)) (f : C(X,UnitaryMatrixGroup n))
    (h0 : ∀ x, Matrix.toEuclideanLin (f x : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) e = (H (0,x)).val) :
    ∃ F : C(I × X,UnitaryMatrixGroup n),
      (∀ x, F (0,x) = f x) ∧
      ∀ z, Matrix.toEuclideanLin (F z : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) e = (H z).val := by
  obtain ⟨V,hV,hd,L,hL,hLd⟩ := ht n
  apply CompactHomotopyLift.lift_relation
    (fun (g : UnitaryMatrixGroup n) (v : UnitColumn n) => Matrix.toEuclideanLin (g : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) e = v.val)
    H f h0 V hV hd L ?_ hLd
  intro z g hg
  change Matrix.toEuclideanLin ((L z : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) *
    (g : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) e = z.val.2.val
  rw [Matrix.toLpLin_mul_same]
  change Matrix.toEuclideanLin (L z : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (Matrix.toEuclideanLin (g : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) e) = _
  rw [hg]
  exact hL z

end ExpandedFA.Toeplitz.MatrixLoops.UnitaryColumnLifting



noncomputable section
open scoped unitInterval
open unitInterval
namespace ExpandedFA.Toeplitz.MatrixLoops

-- Adjoin a last identity coordinate.
def stabilize (n : ℕ) : C(MatrixGroup n, MatrixGroup (n+1)) where
  toFun A :=
    Units.map (Matrix.reindexRingEquiv ℂ (finSumFinEquiv :
      Fin (n+1) ⊕ Fin 1 ≃ Fin (n+2))).toMonoidHom
      { val := Matrix.fromBlocks (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)
        inv := Matrix.fromBlocks (A.inv : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)
        val_inv := by simp [Matrix.fromBlocks_multiply]
        inv_val := by simp [Matrix.fromBlocks_multiply] }
  continuous_toFun := by
    have hv : Continuous (fun A : MatrixGroup n => (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      Units.continuous_val
    have hi : Continuous (fun A : MatrixGroup n => (A.inv : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      Units.continuous_coe_inv
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : MatrixGroup n => Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)))
      exact (hv.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _
    · change Continuous (fun A : MatrixGroup n => Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (A.inv : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)))
      exact (hi.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _

@[simp] theorem stabilize_castSucc (n : ℕ) (A : MatrixGroup n) (i j : Fin (n+1)) :
    (stabilize n A : Matrix (Fin (n+2)) (Fin (n+2)) ℂ) i.castSucc j.castSucc = A.val i j := by
  change (Matrix.fromBlocks _ 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm j.castSucc) = _
  simp

@[simp] theorem stabilize_last_col (n : ℕ) (A : MatrixGroup n) (i : Fin (n+2)) :
    (stabilize n A : Matrix (Fin (n+2)) (Fin (n+2)) ℂ) i (Fin.last (n+1)) =
      if i = Fin.last (n+1) then 1 else 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    change (Matrix.fromBlocks _ 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (finSumFinEquiv.symm _) (finSumFinEquiv.symm (Fin.last (n+1))) = _
  · simp
  · simp

@[simp] theorem stabilize_diagonal (n : ℕ) (u : ℂˣ) :
    stabilize n (diagonal n u) = diagonal (n+1) u := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [stabilize_last_col, diagonal]
    · change (Matrix.fromBlocks _ 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (finSumFinEquiv.symm (Fin.last (n+1))) (finSumFinEquiv.symm j.castSucc) = _
      simp [diagonal, Ne.symm (Fin.castSucc_ne_last _)]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [stabilize_last_col, diagonal]
    · simp [diagonal, Matrix.diagonal_apply]

end ExpandedFA.Toeplitz.MatrixLoops

namespace ExpandedFA.Toeplitz.MatrixLoops

def FixesLast (n : ℕ) : Set (MatrixGroup (n+1)) :=
  {A | ∀ i, A.val i (Fin.last (n+1)) = if i = Fin.last (n+1) then 1 else 0}

lemma inverse_fixesLast {n : ℕ} (A : MatrixGroup (n+1)) (h : A ∈ FixesLast n) :
    A⁻¹ ∈ FixesLast n := by
  intro i
  change ∀ j, A.val j (Fin.last (n+1)) = _ at h
  have hi := congrArg (fun M : Matrix (Fin (n+2)) (Fin (n+2)) ℂ => M i (Fin.last (n+1))) A.inv_val
  change A.inv i (Fin.last (n+1)) = _
  change (A.inv * A.val) i (Fin.last (n+1)) = _ at hi
  simpa [Matrix.mul_apply, h, Matrix.one_apply] using hi

private def fixedLastBlock (n : ℕ) (A : FixesLast n) : MatrixGroup n where
  val := A.val.val.submatrix Fin.castSucc Fin.castSucc
  inv := A.val.inv.submatrix Fin.castSucc Fin.castSucc
  val_inv := by
    apply Matrix.ext
    intro i j
    have hi := congrArg (fun M : Matrix (Fin (n+2)) (Fin (n+2)) ℂ => M i.castSucc j.castSucc) A.val.val_inv
    have hc := A.property i.castSucc
    simp only [Fin.castSucc_ne_last, ite_false] at hc
    simpa [Matrix.mul_apply, Fin.sum_univ_castSucc, hc, Matrix.one_apply] using hi
  inv_val := by
    apply Matrix.ext
    intro i j
    have hi := congrArg (fun M : Matrix (Fin (n+2)) (Fin (n+2)) ℂ => M i.castSucc j.castSucc) A.val.inv_val
    change (A.val.inv * A.val.val) i.castSucc j.castSucc = _ at hi
    have hc := inverse_fixesLast A.val A.property i.castSucc
    change A.val.inv i.castSucc (Fin.last (n+1)) = _ at hc
    simp only [Fin.castSucc_ne_last, ite_false] at hc
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hc, zero_mul, add_zero] at hi
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Fin.castSucc_inj] using hi

/-- Restriction of an invertible matrix fixing the last basis vector to the
quotient by that coordinate, as a continuous invertible matrix. -/
def fixedLastBlockMap (n : ℕ) : C(FixesLast n, MatrixGroup n) where
  toFun := fixedLastBlock n
  continuous_toFun := by
    have hv : Continuous (fun A : FixesLast n => (A.val : Matrix (Fin (n+2)) (Fin (n+2)) ℂ)) :=
      (Units.continuous_val (M := Matrix (Fin (n+2)) (Fin (n+2)) ℂ)).comp continuous_subtype_val
    have hi : Continuous (fun A : FixesLast n => (A.val.inv : Matrix (Fin (n+2)) (Fin (n+2)) ℂ)) :=
      (Units.continuous_coe_inv (M := Matrix (Fin (n+2)) (Fin (n+2)) ℂ)).comp continuous_subtype_val
    apply Units.continuous_iff.mpr
    exact ⟨hv.matrix_submatrix Fin.castSucc Fin.castSucc, hi.matrix_submatrix Fin.castSucc Fin.castSucc⟩

private def triangularUnit (n : ℕ) (A : MatrixGroup n)
    (c : Matrix (Fin 1) (Fin (n+1)) ℂ) : MatrixGroup (n+1) :=
  Units.map (Matrix.reindexRingEquiv ℂ (finSumFinEquiv :
      Fin (n+1) ⊕ Fin 1 ≃ Fin (n+2))).toMonoidHom
    { val := Matrix.fromBlocks (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 c (1 : Matrix (Fin 1) (Fin 1) ℂ)
      inv := Matrix.fromBlocks (A.inv : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 (-c * A.inv) (1 : Matrix (Fin 1) (Fin 1) ℂ)
      val_inv := by simp [Matrix.fromBlocks_multiply]
      inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc] }

private lemma continuous_triangularUnit (n : ℕ) :
    Continuous (fun p : MatrixGroup n × Matrix (Fin 1) (Fin (n+1)) ℂ => triangularUnit n p.1 p.2) := by
  have hv : Continuous (fun p : MatrixGroup n × Matrix (Fin 1) (Fin (n+1)) ℂ =>
      (p.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
    (Units.continuous_val (M := Matrix (Fin (n+1)) (Fin (n+1)) ℂ)).comp continuous_fst
  have hi : Continuous (fun p : MatrixGroup n × Matrix (Fin 1) (Fin (n+1)) ℂ =>
      (p.1.inv : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
    (Units.continuous_coe_inv (M := Matrix (Fin (n+1)) (Fin (n+1)) ℂ)).comp continuous_fst
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun p : MatrixGroup n × Matrix (Fin 1) (Fin (n+1)) ℂ =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (p.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 p.2 (1 : Matrix (Fin 1) (Fin 1) ℂ)))
    exact (hv.matrix_fromBlocks continuous_const continuous_snd continuous_const).matrix_reindex _ _
  · change Continuous (fun p : MatrixGroup n × Matrix (Fin 1) (Fin (n+1)) ℂ =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (p.1.inv : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0
          (-p.2 * p.1.inv) (1 : Matrix (Fin 1) (Fin 1) ℂ)))
    exact (hi.matrix_fromBlocks continuous_const (continuous_snd.neg.matrix_mul hi)
      continuous_const).matrix_reindex _ _

private lemma triangularUnit_zero (n : ℕ) (A : MatrixGroup n) :
    triangularUnit n A 0 = stabilize n A := by
  apply Units.ext
  rfl

private lemma triangularUnit_reconstruct (n : ℕ) (A : FixesLast n) :
    triangularUnit n (fixedLastBlock n A)
      (fun _ j => A.val.val (Fin.last (n+1)) j.castSucc) = A.val := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · change (Matrix.fromBlocks _ 0 _ (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (finSumFinEquiv.symm (Fin.last (n+1))) (finSumFinEquiv.symm (Fin.last (n+1))) = _
      simpa [Matrix.fromBlocks] using (A.property (Fin.last (n+1))).symm
    · change (Matrix.fromBlocks _ 0 _ (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (finSumFinEquiv.symm (Fin.last (n+1))) (finSumFinEquiv.symm j.castSucc) = _
      simp [Matrix.fromBlocks]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · change (Matrix.fromBlocks _ 0 _ (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm (Fin.last (n+1))) = _
      simpa [Matrix.fromBlocks] using (A.property i.castSucc).symm
    · change (Matrix.fromBlocks _ 0 _ (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm j.castSucc) = _
      simp [fixedLastBlock, Matrix.fromBlocks]

private def fixedLastRow (n : ℕ) (A : FixesLast n) : Matrix (Fin 1) (Fin (n+1)) ℂ :=
  fun _ j => A.val.val (Fin.last (n+1)) j.castSucc

private lemma continuous_fixedLastRow (n : ℕ) : Continuous (fixedLastRow n) := by
  apply continuous_matrix
  intro i j
  exact (((Units.continuous_val (M := Matrix (Fin (n+2)) (Fin (n+2)) ℂ)).comp
    continuous_subtype_val).matrix_elem (Fin.last (n+1)) j.castSucc)

/-- The last row off the diagonal can be contracted while every matrix remains
invertible. No orthogonality assumption is needed. -/
def fixedLastHomotopy (n : ℕ) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(FixesLast n, MatrixGroup (n+1))).Homotopy
      ((stabilize n).comp (fixedLastBlockMap n)) where
  toFun p := triangularUnit n (fixedLastBlock n p.2)
    ((1 - (p.1 : ℝ)) • fixedLastRow n p.2)
  continuous_toFun := by
    refine (continuous_triangularUnit n).comp (Continuous.prodMk ?_ ?_)
    · exact (fixedLastBlockMap n).continuous.comp continuous_snd
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        ((continuous_fixedLastRow n).comp continuous_snd)
  map_zero_left A := by
    change triangularUnit n (fixedLastBlock n A) ((1 - (0 : ℝ)) • fixedLastRow n A) = A.val
    rw [sub_zero, one_smul]
    exact triangularUnit_reconstruct n A
  map_one_left A := by
    change triangularUnit n (fixedLastBlock n A) ((1 - (1 : ℝ)) • _) = _
    rw [sub_self]
    simp only [zero_smul]
    exact triangularUnit_zero n (fixedLastBlock n A)

end ExpandedFA.Toeplitz.MatrixLoops



noncomputable section
open scoped unitInterval
open unitInterval
open Matrix
namespace ExpandedFA.Toeplitz.MatrixLoops

/-- The explicitly constructed local transporter has all required properties. -/
theorem local_unitary_transport : Spec.LocalUnitaryTransport :=
  UnitaryTransport.local_unitary_transport

/-- Every sphere column loop in complex dimension at least two contracts. -/
theorem sphere_loop_contraction : Spec.SphereLoopContraction :=
  unitColumn_loop_homotopic_const

lemma matrix_apply_standardColumn (n : ℕ) (j : Fin (n+1))
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Matrix.toEuclideanLin A (standardColumn n j).val = matrixColumn n j A := by
  ext i
  change (A *ᵥ _) i = A i j
  simp [Matrix.mulVec, dotProduct, standardColumn_apply]

/-- The column lift starts at the prescribed frame and follows the entire
specified sphere homotopy, including its loop periodicity. -/
theorem column_homotopy_lift : Spec.ColumnHomotopyLift := by
  intro n j U v H
  obtain ⟨F,F0,Fc⟩ := UnitaryColumnLifting.unitary_column_lift
    local_unitary_transport n (standardColumn n j).val H.toContinuousMap U (by
      intro x
      rw [matrix_apply_standardColumn]
      exact congrArg Subtype.val (H.map_zero_left x).symm)
  let V : C(Circle, UnitaryMatrixGroup n) :=
    ⟨fun x => F (1,x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let K : U.Homotopy V :=
    { toContinuousMap := F
      map_zero_left := F0
      map_one_left := fun x => rfl }
  refine ⟨V,K,?_⟩
  intro p
  apply Subtype.ext
  change matrixColumn n j (F p).val = (H p).val
  rw [← matrix_apply_standardColumn]
  exact Fc p

end ExpandedFA.Toeplitz.MatrixLoops

namespace ExpandedFA.Toeplitz.MatrixLoops

/-- Contract the last column and remove its last coordinate. The smaller block
is invertible throughout; the scalar entry remains in the first coordinate. -/
theorem unitary_scalar_step (n : ℕ) (U : C(Circle, UnitaryMatrixGroup (n+1))) :
    ∃ Ψ : C(Circle, MatrixGroup n),
      ((unitaryEmbedding (n+1)).comp U).Homotopic ((stabilize n).comp Ψ) := by
  let j : Fin (n+2) := Fin.last (n+1)
  obtain ⟨H⟩ := sphere_loop_contraction n ((unitaryColumn (n+1) j).comp U)
    (standardColumn (n+1) j)
  obtain ⟨V,K,hK⟩ := column_homotopy_lift (n+1) j U _ H
  have hfix : ∀ z, unitaryEmbedding (n+1) (V z) ∈ FixesLast n := by
    intro z i
    have hc : unitaryColumn (n+1) j (V z) = standardColumn (n+1) j := by
      rw [← K.map_one_left z]
      exact (hK (1,z)).trans (H.map_one_left z)
    have hi := congrArg (fun v : UnitColumn (n+1) => v.val i) hc
    change (V z).val i (Fin.last (n+1)) = _
    simpa only [unitaryColumn_apply, standardColumn_apply] using hi
  let W : C(Circle, FixesLast n) :=
    { toFun := fun z => ⟨unitaryEmbedding (n+1) (V z), hfix z⟩
      continuous_toFun := ((unitaryEmbedding (n+1)).continuous.comp V.continuous).subtype_mk _ }
  refine ⟨(fixedLastBlockMap n).comp W, ?_⟩
  have hUV := (ContinuousMap.Homotopic.refl (unitaryEmbedding (n+1))).comp
    (show U.Homotopic V from ⟨K⟩)
  have hVW := (fixedLastHomotopy n).compContinuousMap W
  have hs : (⟨Subtype.val, continuous_subtype_val⟩ : C(FixesLast n, MatrixGroup (n+1))).comp W =
      (unitaryEmbedding (n+1)).comp V := rfl
  have ht : ((stabilize n).comp (fixedLastBlockMap n)).comp W =
      (stabilize n).comp ((fixedLastBlockMap n).comp W) := rfl
  rw [hs, ht] at hVW
  exact hUV.trans ⟨hVW⟩

/-- Dimension induction reduces every continuous invertible matrix loop to one
nonvanishing scalar entry, without any homotopy certificate as an assumption. -/
theorem scalar_reduction : Spec.ScalarReduction := by
  intro n
  induction n with
  | zero =>
    intro Φ
    exact ⟨powerLoop (winding ((determinant 0).comp Φ)), dimension_one_classification Φ⟩
  | succ n ih =>
    intro Φ
    obtain ⟨U,hU⟩ := unitary_reduction (n+1) Φ
    obtain ⟨Ψ,hΨ⟩ := unitary_scalar_step n U
    obtain ⟨u,hu⟩ := ih Ψ
    refine ⟨u, ?_⟩
    have h := (ContinuousMap.Homotopic.refl (stabilize n)).comp hu
    have hd : (stabilize n).comp ((diagonal n).comp u) = (diagonal (n+1)).comp u := by
      apply ContinuousMap.ext
      intro z
      exact stabilize_diagonal n (u z)
    rw [hd] at h
    exact hU.trans (hΨ.trans h)

/-- Every continuous loop of complex invertible matrices deforms through
invertible matrices to the diagonal winding normal form in every positive dimension. -/
theorem classification : Spec.Classification :=
  classification_of_scalar_reduction scalar_reduction

end ExpandedFA.Toeplitz.MatrixLoops

