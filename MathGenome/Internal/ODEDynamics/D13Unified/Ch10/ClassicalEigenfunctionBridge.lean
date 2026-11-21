import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.GreenOperator
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.Lagrange
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The Hilbert/classical bridge for paper.tex, d13:10:spectrum.
The forward construction starts with the weak Green representative; all
pointwise conclusions and uniqueness are on the original closed interval. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ComplexConjugate Matrix
namespace D13Unified.Ch10.ClassicalEigenfunctionBridge
open RegularProblem
open GreenKernel hiding Problem interval
open GreenWeakInverse

lemma toHilbert_smul (P : Problem) (z : ℂ) (y : ℝ → ℂ)
    (hy : MemLp y 2 (weightedMeasure P)) :
    toHilbert P (fun x => z * y x) (hy.const_smul z) = z • toHilbert P y hy := by
  exact MemLp.toLp_const_smul z hy

lemma operator_class (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) (f : Hilbert P) :
    operator P c f = toHilbert P (representative P c f)
      (class_representative P c hc hQ f).1 := by
  unfold operator Specs.D13Unified.Ch10.GreenWeakInverse.operatorValue
  exact dite_eq_left (class_representative P c hc hQ f).1

lemma expression_smul (P : Problem) (z : ℂ) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ 2 y (interval P)) (x : ℝ) (hx : x ∈ interval P) :
    expression P (fun t => z * y t) x = z * expression P y x := by
  have ud := uniqueDiffOn_Icc P.a_lt_b
  have hd : ∀ t ∈ interval P, derivative P (fun t => z * y t) t = z * derivative P y t := by
    intro t ht
    exact ((hy.differentiableOn (by norm_num) t ht).hasDerivWithinAt.const_mul z).derivWithin (ud t ht)
  have hflux : ContDiffOn ℝ 1 (fun t => (P.p t : ℂ) * derivative P y t) (interval P) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn P.p_regular).mul
      (hy.derivWithin ud (by norm_num))
  have heq : EqOn (fun t => (P.p t : ℂ) * derivative P (fun t => z * y t) t)
      (fun t => z * ((P.p t : ℂ) * derivative P y t)) (interval P) := by
    intro t ht
    dsimp only
    rw [hd t ht]; ring
  unfold expression Specs.D13Unified.Ch10.RegularProblem.expressionValue
  rw [derivWithin_congr heq (heq hx),
    ((hflux.differentiableOn (by norm_num) x hx).hasDerivWithinAt.const_mul z).derivWithin (ud x hx)]
  ring

lemma classical_smul (P : Problem) (lam z : ℂ) (y : ℝ → ℂ)
    (hy : IsClassicalEigenfunction P dirichlet lam y) (hz : z ≠ 0) :
    IsClassicalEigenfunction P dirichlet lam (fun x => z * y x) := by
  refine ⟨contDiffOn_const.mul hy.1, ?_, ?_, ?_⟩
  · obtain ⟨x,hx,hn⟩ := hy.2.1
    exact ⟨x,hx,mul_ne_zero hz hn⟩
  · have hb := (dirichlet_boundary P y).mp hy.2.2.1
    apply (dirichlet_boundary P _).mpr
    exact ⟨by simp [hb.1], by simp [hb.2]⟩
  · intro x hx
    change expression P (fun t => z * y t) x = lam * (P.w x : ℂ) * (z * y x)
    have he : expression P y x = lam * (P.w x : ℂ) * y x := hy.2.2.2 x hx
    rw [expression_smul P z y hy.1 x hx, he]
    ring


/-- Bootstrap from the weak inverse and equality of L² classes. -/
theorem forward : Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.Forward := by
  intro P c hc hQ mu hmu f hfn heigen
  change operator P c f = (mu : ℂ) • f at heigen
  let R := representative P c f
  have hweak := (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).1
  have hRc : ContinuousOn R (interval P) := hweak.1.continuousOn
  have hRm : MemLp R 2 (weightedMeasure P) := continuous_memLp P R hRc
  let y : ℝ → ℂ := fun x => (mu : ℂ)⁻¹ * R x
  have hym : MemLp y 2 (weightedMeasure P) := hRm.const_smul (mu : ℂ)⁻¹
  have hyc : ContinuousOn y (interval P) := continuousOn_const.mul hRc
  have hmu : (mu : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmu.ne'
  have hyclass : toHilbert P y hym = f := by
    change toHilbert P (fun x => (mu : ℂ)⁻¹ * R x) _ = f
    rw [toHilbert_smul P _ R hRm, ← operator_class P c hc hQ f, heigen, smul_smul,
      inv_mul_cancel₀ hmu, one_smul]
  have heR : R = applyKernel P c y := by
    apply representative_independent P c (f : ℝ → ℂ) y (Lp.memLp f) hym
    change (Lp.memLp f).toLp (f : ℝ → ℂ) = toHilbert P y hym
    rw [Lp.toLp_coeFn, hyclass]
  have hsol := (inverse_continuous ℂ P c hc hQ y hyc).1
  rw [← heR] at hsol
  have hyr : ContDiffOn ℝ 2 y (interval P) := contDiffOn_const.mul hsol.1
  have hyn : ∃ x ∈ interval P, y x ≠ 0 :=
    (continuous_nonzero P y hyc hym).mp (hyclass ▸ hfn)
  refine ⟨y, hym, ⟨hyr, hyn, ?_, ?_⟩, hyclass, ?_⟩
  · apply (dirichlet_boundary P y).mpr
    exact ⟨by simp [y, hsol.2.1], by simp [y, hsol.2.2.1]⟩
  · intro x hx
    change expression P (fun t => (mu : ℂ)⁻¹ * R t) x = _
    rw [expression_smul P (mu : ℂ)⁻¹ R hsol.1 x hx]
    have he := hsol.2.2.2 x hx
    have hL : expression P R x = (P.w x : ℂ) * y x -
        (c : ℂ) * (P.w x : ℂ) * R x := by
      dsimp [expression, Specs.D13Unified.Ch10.RegularProblem.expressionValue,
        derivative, Specs.D13Unified.Ch10.RegularProblem.derivativeValue, Q] at he ⊢
      push_cast at he
      linear_combination he
    rw [hL]
    dsimp [y]
    push_cast
    ring
  · intro z hz hzc hzclass
    exact (continuous_equality P z y hzc hyc hz hym).mp (hzclass.trans hyclass.symm)

lemma kernel_smul (P : Problem) (c : ℝ) (z : ℂ) (y : ℝ → ℂ) :
    applyKernel P c (fun x => z * y x) = fun x => z * applyKernel P c y x := by
  funext x
  simp only [applyKernel, ← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

/-- The scalar identity is obtained before positivity or division. -/
lemma classical_green_identity (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) (lam : ℂ) (y : ℝ → ℂ)
    (hy : IsClassicalEigenfunction P dirichlet lam y)
    (hym : MemLp y 2 (weightedMeasure P)) :
    toHilbert P y hym = (lam + (c : ℂ)) • operator P c (toHilbert P y hym) := by
  let z := lam + (c : ℂ)
  have hs : IsDirichletSolution P c (fun x => z * y x) y := by
    have hb := (dirichlet_boundary P y).mp hy.2.2.1
    refine ⟨hy.1, hb.1, hb.2, ?_⟩
    intro x hx
    have he := hy.2.2.2 x hx
    dsimp [expression, Specs.D13Unified.Ch10.RegularProblem.expressionValue,
      Specs.D13Unified.Ch10.RegularProblem.derivativeValue] at he
    dsimp [Q, z]
    push_cast
    linear_combination he
  have heq := (inverse_continuous ℂ P c hc hQ (fun x => z * y x)
    (continuousOn_const.mul hy.1.continuousOn)).2 y hs
  have hrep : representative P c (toHilbert P y hym) = applyKernel P c y := by
    apply representative_independent P c (toHilbert P y hym : ℝ → ℂ) y
      (Lp.memLp (toHilbert P y hym)) hym
    exact Lp.toLp_coeFn _ _
  rw [kernel_smul] at heq
  rw [operator_class P c hc hQ]
  rw [← toHilbert_smul P z]
  apply (continuous_equality P _ _ hy.1.continuousOn
    (continuousOn_const.mul (inverse_weak P c hc hQ _
      (Lp.memLp (toHilbert P y hym))).1.1.continuousOn) _ _).mpr
  intro x hx
  change y x = z * representative P c (toHilbert P y hym) x
  rw [hrep]
  exact heq hx

theorem converse : Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.Converse := by
  intro P c hc hQ lam y hy hym
  have hr := Lagrange.eigenvalue_real P dirichlet lam y hy
  let f := toHilbert P y hym
  have hfn : f ≠ 0 := (continuous_nonzero P y hy.1.continuousOn hym).mpr hy.2.1
  have hid := classical_green_identity P c hc hQ lam y hy hym
  change f = (lam + (c : ℂ)) • operator P c f at hid
  have hp := (GreenOperator.strictlyPositive P c hc hQ f hfn).1
  have hn : 0 < (paperInner P f f).re := by
    rw [inner_norm]
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos (norm_pos_iff.mpr hfn)
  have hprod : (paperInner P f f).re =
      (lam.re + c) * (paperInner P (operator P c f) f).re := by
    have hi := congrArg (fun u => paperInner P u f) hid
    rw [inner_linear_first] at hi
    simpa [Complex.mul_re, hr] using congrArg Complex.re hi
  have hpos : 0 < lam.re + c := by nlinarith
  have hz : lam + (c : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  refine ⟨hr, hpos, hid, ?_⟩
  change operator P c f = (lam + (c : ℂ))⁻¹ • f
  calc
    _ = (lam + (c : ℂ))⁻¹ • ((lam + (c : ℂ)) • operator P c f) := by
      rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
    _ = _ := congrArg (fun u => (lam + (c : ℂ))⁻¹ • u) hid.symm


open Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge (classicalEigenspace)

theorem eigenspaces : Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.Eigenspaces := by
  intro P c hc hQ mu hmu
  ext f
  constructor
  · rintro (rfl | ⟨y, hym, hy, rfl⟩)
    · have hz := (GreenOperator.linearity P c hc hQ).2 (0 : ℂ) (0 : Hilbert P)
      simpa using hz
    · have he := (converse P c hc hQ _ y hy hym).2.2.2
      have hz : (((mu⁻¹ - c : ℝ) : ℂ) + (c : ℂ))⁻¹ = (mu : ℂ) := by
        push_cast; simp
      change operator P c (toHilbert P y hym) = (mu : ℂ) • toHilbert P y hym
      rw [hz] at he
      exact he
  · intro hf
    by_cases hzero : f = 0
    · exact Or.inl hzero
    · obtain ⟨y, hym, hy, he, _⟩ := forward P c hc hQ mu hmu f hzero hf
      exact Or.inr ⟨y, hym, hy, he⟩

/-- Congruence of the actual second-order expression on its domain. -/
lemma expression_congr (P : Problem) (u v : ℝ → ℂ)
    (he : EqOn u v (interval P)) (x : ℝ) (hx : x ∈ interval P) :
    expression P u x = expression P v x := by
  have hd : EqOn (derivative P u) (derivative P v) (interval P) :=
    fun t ht => derivWithin_congr he (he ht)
  have hf : EqOn (fun t => (P.p t : ℂ) * derivative P u t)
      (fun t => (P.p t : ℂ) * derivative P v t) (interval P) :=
    fun t ht => congrArg (fun z => (P.p t : ℂ) * z) (hd ht)
  dsimp [expression, Specs.D13Unified.Ch10.RegularProblem.expressionValue]
  rw [derivWithin_congr hf (hf hx), he hx]

def complexMatrix (P : Problem) (lam : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (P.p x : ℂ)⁻¹; (P.q x : ℂ) - lam * (P.w x : ℂ), 0]

def complexState (P : Problem) (y : ℝ → ℂ) (x : ℝ) : Fin 2 → ℂ :=
  ![y x, (P.p x : ℂ) * derivative P y x]

lemma complexMatrix_continuous (P : Problem) (lam : ℂ) :
    ContinuousOn (complexMatrix P lam) (interval P) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact continuousOn_const
  · exact (Complex.continuous_ofReal.comp_continuousOn P.p_regular.continuousOn).inv₀
      (fun x hx => Complex.ofReal_ne_zero.mpr (P.p_positive x hx).ne')
  · exact (Complex.continuous_ofReal.comp_continuousOn P.q_continuous).sub
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn P.w_continuous))
  · exact continuousOn_const

lemma complexState_continuous (P : Problem) (y : ℝ → ℂ)
    (hy : ContDiffOn ℝ 2 y (interval P)) :
    ContinuousOn (complexState P y) (interval P) := by
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact hy.continuousOn
  · exact (Complex.continuous_ofReal.comp_continuousOn P.p_regular.continuousOn).mul
      (hy.continuousOn_derivWithin (uniqueDiffOn_Icc P.a_lt_b) (by norm_num))

lemma complexState_derivative (P : Problem) (lam : ℂ) (y : ℝ → ℂ)
    (hy : IsClassicalEigenfunction P dirichlet lam y) (x : ℝ) (hx : x ∈ interval P) :
    HasDerivWithinAt (complexState P y) (complexMatrix P lam x *ᵥ complexState P y x)
      (interval P) x := by
  have ud := uniqueDiffOn_Icc P.a_lt_b
  have hd := (hy.1.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  change HasDerivWithinAt y (derivative P y x) (interval P) x at hd
  have hflux : ContDiffOn ℝ 1 (fun t => (P.p t : ℂ) * derivative P y t) (interval P) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn P.p_regular).mul
      (hy.1.derivWithin ud (by norm_num))
  have he := hy.2.2.2 x hx
  change -derivWithin (fun t => (P.p t : ℂ) * derivative P y t) (interval P) x +
    (P.q x : ℂ) * y x = lam * (P.w x : ℂ) * y x at he
  have he' : derivWithin (fun t => (P.p t : ℂ) * derivative P y t) (interval P) x =
      ((P.q x : ℂ) - lam * (P.w x : ℂ)) * y x := by linear_combination -he
  have hfd := (hflux.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  rw [he'] at hfd
  apply hasDerivWithinAt_pi.mpr
  intro i
  fin_cases i
  · convert hd using 1 <;>
      simp [complexState, complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Complex.ofReal_ne_zero.mpr (P.p_positive x hx).ne']
  · simpa [complexState, complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hfd

lemma vector_unique (P : Problem) (lam : ℂ) (Y Z : ℝ → Fin 2 → ℂ)
    (hYc : ContinuousOn Y (interval P)) (hZc : ContinuousOn Z (interval P))
    (hYd : ∀ x ∈ interval P, HasDerivWithinAt Y (complexMatrix P lam x *ᵥ Y x) (interval P) x)
    (hZd : ∀ x ∈ interval P, HasDerivWithinAt Z (complexMatrix P lam x *ᵥ Z x) (interval P) x)
    (hinit : Y P.a = Z P.a) : EqOn Y Z (interval P) := by
  obtain ⟨V, _, _, _, _, hu⟩ := Ch07.LinearSystemExistence.vector_existence ℂ 2
    (timeInterval P) (complexMatrix P lam) P.a (Y P.a)
    (left_mem_Icc.mpr P.a_lt_b.le) (complexMatrix_continuous P lam)
  have hY := hu Y hYc rfl hYd
  have hZ := hu Z hZc hinit.symm hZd
  exact fun x hx => (hY hx).trans (hZ hx).symm


open private cast_derivative from MathGenome.Internal.ODEDynamics.D13Unified.Ch10.GreenKernel

/-- The real left-normalized mode, available for every real spectral value. -/
def leftState (P : Problem) (lam : ℂ) (x : ℝ) : Fin 2 → ℂ :=
  ![(leftMode P (-lam.re) x : ℂ), (leftFlux P (-lam.re) x : ℂ)]

lemma leftState_continuous (P : Problem) (lam : ℂ) :
    ContinuousOn (leftState P lam) (interval P) := by
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact Complex.continuous_ofReal.comp_continuousOn (left_mode_c1 P (-lam.re)).continuousOn
  · exact Complex.continuous_ofReal.comp_continuousOn (left_flux_c1 P (-lam.re)).continuousOn

lemma leftState_derivative (P : Problem) (lam : ℂ) (hlam : lam.im = 0)
    (x : ℝ) (hx : x ∈ interval P) :
    HasDerivWithinAt (leftState P lam) (complexMatrix P lam x *ᵥ leftState P lam x)
      (interval P) x := by
  have hre : (lam.re : ℂ) = lam := Complex.ext (by simp) (by simp [hlam])
  apply hasDerivWithinAt_pi.mpr
  intro i
  fin_cases i
  · convert! cast_derivative (𝕂 := ℂ) (left_mode_derivative P (-lam.re) x hx) using 1
    simp [leftState, complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      div_eq_mul_inv, mul_comm]
  · convert! cast_derivative (𝕂 := ℂ) (left_flux_derivative P (-lam.re) x hx) using 1
    simp only [leftState, complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    rw [← hre]
    dsimp [Q]
    push_cast
    ring

/-- Every classical Dirichlet eigenfunction is its initial flux times the
same real left-normalized mode. This is a statement on the actual interval. -/
lemma proportional_to_real_mode (P : Problem) (lam : ℂ) (y : ℝ → ℂ)
    (hy : IsClassicalEigenfunction P dirichlet lam y) :
    let A := (P.p P.a : ℂ) * derivative P y P.a
    A ≠ 0 ∧ EqOn y (fun x => A * (leftMode P (-lam.re) x : ℂ)) (interval P) := by
  let A := (P.p P.a : ℂ) * derivative P y P.a
  have hlam := Lagrange.eigenvalue_real P dirichlet lam y hy
  have he := vector_unique P lam (complexState P y) (fun x => A • leftState P lam x)
    (complexState_continuous P y hy.1) ((leftState_continuous P lam).const_smul A)
    (fun x hx => complexState_derivative P lam y hy x hx) (by
      intro x hx
      convert (leftState_derivative P lam hlam x hx).const_smul A using 1
      simp only [Matrix.mulVec_smul]) (by
      have hb := (dirichlet_boundary P y).mp hy.2.2.1
      ext i
      fin_cases i <;> simp [complexState, leftState, A, hb.1, left_initial])
  have heq : EqOn y (fun x => A * (leftMode P (-lam.re) x : ℂ)) (interval P) := by
    intro x hx
    exact congrFun (he hx) 0
  refine ⟨?_, heq⟩
  intro hA
  obtain ⟨x, hx, hn⟩ := hy.2.1
  apply hn
  rw [heq hx]
  change A * (leftMode P (-lam.re) x : ℂ) = 0
  change A = 0 at hA
  rw [hA, zero_mul]

lemma real_mode_classical (P : Problem) (lam : ℂ) (y : ℝ → ℂ)
    (hy : IsClassicalEigenfunction P dirichlet lam y) :
    IsClassicalEigenfunction P dirichlet lam (fun x => (leftMode P (-lam.re) x : ℂ)) := by
  obtain ⟨hA, heq⟩ := proportional_to_real_mode P lam y hy
  let A := (P.p P.a : ℂ) * derivative P y P.a
  let u : ℝ → ℂ := fun x => (leftMode P (-lam.re) x : ℂ)
  have hur : ContDiffOn ℝ 2 u (interval P) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (left_mode_c2 P (-lam.re))
  have hun : ∃ x ∈ interval P, u x ≠ 0 := by
    obtain ⟨x, hx, hn⟩ := hy.2.1
    refine ⟨x, hx, ?_⟩
    intro hzero
    exact hn (by rw [heq hx]; change A * u x = 0; rw [hzero, mul_zero])
  refine ⟨hur, hun, ?_, ?_⟩
  · apply (dirichlet_boundary P u).mpr
    have hb := (dirichlet_boundary P y).mp hy.2.2.1
    refine ⟨by simp [u, (left_initial P (-lam.re)).1], ?_⟩
    have he := heq (right_mem_Icc.mpr P.a_lt_b.le)
    rw [hb.2] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hA
  · intro x hx
    change expression P u x = lam * (P.w x : ℂ) * u x
    apply mul_left_cancel₀ hA
    calc
      A * expression P u x = expression P (fun t => A * u t) x :=
        (expression_smul P A u hur x hx).symm
      _ = expression P y x := (expression_congr P y _ heq x hx).symm
      _ = lam * (P.w x : ℂ) * y x := hy.2.2.2 x hx
      _ = A * (lam * (P.w x : ℂ) * u x) := by rw [heq hx]; ring

lemma classical_proportional (P : Problem) (lam : ℂ) (u v : ℝ → ℂ)
    (hu : IsClassicalEigenfunction P dirichlet lam u)
    (hv : IsClassicalEigenfunction P dirichlet lam v) :
    ∃ z : ℂ, EqOn v (fun x => z * u x) (interval P) := by
  obtain ⟨hA, heA⟩ := proportional_to_real_mode P lam u hu
  obtain ⟨_, heB⟩ := proportional_to_real_mode P lam v hv
  refine ⟨((P.p P.a : ℂ) * derivative P v P.a) /
    ((P.p P.a : ℂ) * derivative P u P.a), ?_⟩
  intro x hx
  dsimp only
  rw [heA hx, heB hx]
  field_simp [(mul_ne_zero_iff.mp hA).1, (mul_ne_zero_iff.mp hA).2]


/-- The classical space is precisely a complex line in H, with finrank one. -/
theorem simplicity : Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.Simplicity := by
  intro P lam hex
  obtain ⟨y, hy⟩ := hex
  let hym := continuous_memLp P y hy.1.continuousOn
  let v := toHilbert P y hym
  have hv : v ≠ 0 := (continuous_nonzero P y hy.1.continuousOn hym).mpr hy.2.1
  refine ⟨v, hv, ?_, finrank_span_singleton hv⟩
  ext f
  constructor
  · rintro (rfl | ⟨z, hzm, hz, rfl⟩)
    · exact Submodule.zero_mem _
    · obtain ⟨a, heq⟩ := classical_proportional P lam y z hy hz
      apply Submodule.mem_span_singleton.mpr
      refine ⟨a, ?_⟩
      change a • toHilbert P y hym = toHilbert P z hzm
      rw [← toHilbert_smul P a y hym]
      exact (continuous_equality P _ _ (continuousOn_const.mul hy.1.continuousOn)
        hz.1.continuousOn _ _).mpr heq.symm
  · intro hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
    by_cases ha : a = 0
    · exact Or.inl (by simp [ha])
    · refine Or.inr ⟨fun x => a * y x, hym.const_smul a, classical_smul P lam a y hy ha, ?_⟩
      exact toHilbert_smul P a y hym

/-- Select a real normalized representative at every classical eigenvalue. -/
theorem real_normalized : Specs.D13Unified.Ch10.ClassicalEigenfunctionBridge.RealNormalized := by
  intro P lam hex
  obtain ⟨y, hy⟩ := hex
  let u : ℝ → ℂ := fun x => (leftMode P (-lam.re) x : ℂ)
  have hu : IsClassicalEigenfunction P dirichlet lam u := real_mode_classical P lam y hy
  let hum := continuous_memLp P u hu.1.continuousOn
  have hu0 : toHilbert P u hum ≠ 0 :=
    (continuous_nonzero P u hu.1.continuousOn hum).mpr hu.2.1
  let s : ℝ := ‖toHilbert P u hum‖⁻¹
  have hs : 0 < s := inv_pos.mpr (norm_pos_iff.mpr hu0)
  let r : ℝ → ℝ := fun x => s * leftMode P (-lam.re) x
  have hr : IsClassicalEigenfunction P dirichlet lam (fun x => (r x : ℂ)) := by
    convert classical_smul P lam (s : ℂ) u hu (Complex.ofReal_ne_zero.mpr hs.ne') using 1
    funext x
    simp [r, u]
  refine ⟨r, continuous_memLp P _ hr.1.continuousOn, hr, ?_⟩
  have he : (fun x => (r x : ℂ)) = fun x => (s : ℂ) * u x := by
    funext x; simp [r, u]
  have heH : toHilbert P (fun x => (r x : ℂ)) (continuous_memLp P _ hr.1.continuousOn) =
      (s : ℂ) • toHilbert P u hum := by
    rw [← toHilbert_smul P (s : ℂ) u hum]
    apply (continuous_equality P _ _ hr.1.continuousOn
      (continuousOn_const.mul hu.1.continuousOn) _ _).mpr
    intro x _
    exact congrFun he x
  change ‖toHilbert P (fun x => (r x : ℂ)) (continuous_memLp P _ hr.1.continuousOn)‖ = 1
  rw [heH, norm_smul]
  simp [s, Complex.norm_real, norm_ne_zero_iff.mpr hu0]

end D13Unified.Ch10.ClassicalEigenfunctionBridge
