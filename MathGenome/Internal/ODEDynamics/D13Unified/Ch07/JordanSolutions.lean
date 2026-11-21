import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.ExponentialCalculus
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.JordanSolutions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert

noncomputable section
open scoped Matrix.Norms.Operator ContDiff
open Finset
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch07
variable {𝕂 n : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]

theorem matrixExp_nilpotent (N : Matrix n n 𝕂) (m : ℕ) (hN : N ^ m = 0) (t : ℝ) :
    matrixExp N t = ∑ j ∈ range m, (t ^ j / (Nat.factorial j : ℝ)) • N ^ j := by
  rw [matrixExp_eq_tsum]
  exact tsum_eq_sum (fun j hj => by
    have hmj : m ≤ j := Nat.le_of_not_gt (by simpa using hj)
    rw [pow_eq_zero_of_le hmj hN, smul_zero])

theorem matrixExp_similarity : Specs.D13Unified.Ch07.JordanSolutions.similarityType := by
  intro 𝕂 n _ _ _ P A t
  change matrixExp (P.val * A * (P⁻¹).val) t = P.val * matrixExp A t * (P⁻¹).val
  simpa only [matrixExp, smul_mul_assoc, mul_smul_comm] using
    NormedSpace.exp_units_conj P (t • A)

lemma matrixExp_scalar_add {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (μ : ℂ) (t : ℝ) :
    matrixExp (μ • (1 : Matrix n n ℂ) + N) t =
      Complex.exp (μ * (t : ℂ)) •
        matrixExp N t := by
  have hc : Commute (t • (μ • (1 : Matrix n n ℂ))) (t • N) :=
    by simpa only [Algebra.algebraMap_eq_smul_one] using
      (((Algebra.commute_algebraMap_left μ N).smul_left t).smul_right t)
  rw [matrixExp, smul_add, NormedSpace.exp_add_of_commute hc]
  have hs : NormedSpace.exp (t • (μ • (1 : Matrix n n ℂ))) =
      Complex.exp (μ * (t : ℂ)) • (1 : Matrix n n ℂ) := by
    have ht : t • (μ • (1 : Matrix n n ℂ)) =
        (μ * (t : ℂ)) • (1 : Matrix n n ℂ) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
      rfl
    rw [ht]
    simpa only [Algebra.algebraMap_eq_smul_one, Complex.exp_eq_exp_ℂ] using
      (NormedSpace.map_exp (algebraMap ℂ (Matrix n n ℂ))
        (continuous_algebraMap ℂ (Matrix n n ℂ)) (μ * (t : ℂ))).symm
  rw [hs, smul_mul_assoc, one_mul]
  rfl

theorem matrixExp_block {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (μ : ℂ) (m : ℕ) (_hm : 1 ≤ m) (hN : N ^ m = 0) (t : ℝ) :
    matrixExp (μ • (1 : Matrix n n ℂ) + N) t =
      Complex.exp (μ * (t : ℂ)) •
        ∑ j ∈ range m, (t ^ j / (Nat.factorial j : ℝ)) • N ^ j := by
  rw [matrixExp_scalar_add, matrixExp_nilpotent N m hN]

/-- Matrix-vector multiplication as a continuous real bilinear map. -/
private def mulVecContinuous :
    Matrix n n 𝕂 →L[ℝ] (n → 𝕂) →L[ℝ] (n → 𝕂) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap.comp
      (Matrix.mulVecBilin ℝ ℝ))

omit [DecidableEq n] in
lemma hasDerivAt_mulVec {M M' : ℝ → Matrix n n 𝕂} {v v' : ℝ → n → 𝕂}
    {t : ℝ} (hM : HasDerivAt M (M' t) t) (hv : HasDerivAt v (v' t) t) :
    HasDerivAt (fun r => (M r).mulVec (v r))
      ((M t).mulVec (v' t) + (M' t).mulVec (v t)) t := by
  exact ContinuousLinearMap.hasDerivAt_of_bilinear (B := mulVecContinuous)
    (fun _ => hM) (fun _ => hv)

lemma matrixExp_mulVec_hasDerivAt (A : Matrix n n 𝕂) (s : ℝ) (v : n → 𝕂) (t : ℝ) :
    HasDerivAt (fun r => (matrixExp A (r - s)).mulVec v)
      (A.mulVec ((matrixExp A (t - s)).mulVec v)) t := by
  have hM : HasDerivAt (fun r => matrixExp A (r - s))
      (A * matrixExp A (t - s)) t := by
    convert! (matrixExp_hasDerivAt_left A (t - s)).scomp t
      ((hasDerivAt_id t).sub_const s) using 1; simp
  simpa only [Matrix.mulVec_zero, zero_add, Matrix.mulVec_mulVec] using
    hasDerivAt_mulVec (M' := fun r => A * matrixExp A (r - s))
      (v' := fun _ => 0) hM (hasDerivAt_const t v)

theorem matrix_solution_exists :
    Specs.D13Unified.Ch07.JordanSolutions.solutionExistsType := by
  intro 𝕂 n _ _ _ A s v
  refine ⟨?_, matrixExp_mulVec_hasDerivAt A s v,
    by simp [Specs.D13Unified.Ch07.MatrixExponential.exponentialValue]⟩
  let ev := (mulVecContinuous (𝕂 := 𝕂) (n := n)).flip v
  have hM := (matrixExp_smooth A).comp
    (show ContDiff ℝ ∞ (fun r : ℝ => r - s) from contDiff_id.sub contDiff_const)
  have hpath : ContDiff ℝ ∞ (fun r => (matrixExp A (r - s)).mulVec v) := by
    convert! ev.contDiff.comp hM using 1
  exact hpath.of_le (by simp)

theorem matrix_solution_formula :
    Specs.D13Unified.Ch07.JordanSolutions.solutionType := by
  intro 𝕂 n _ _ _ A I x hx s hs t ht
  let y := fun r => (matrixExp A (s - r)).mulVec (x r)
  have hy : ∀ r ∈ I.carrier, HasDerivAt y 0 r := by
    intro r hr
    have hM : HasDerivAt (fun u => matrixExp A (s - u))
        (-(matrixExp A (s - r) * A)) r := by
      convert! (matrixExp_hasDerivAt_right A (s - r)).scomp r
        ((hasDerivAt_id r).const_sub s) using 1; simp
    have hx' : HasDerivAt x (A.mulVec (x r)) r := by
      simpa only [matrixODE, ODE.eval, dite_eq_left (Set.mem_univ _)] using hx.2.2 r hr
    have h := hasDerivAt_mulVec (M' := fun u => -(matrixExp A (s - u) * A))
      (v' := fun u => A.mulVec (x u)) hM hx'
    simpa only [Matrix.neg_mulVec, Matrix.mulVec_mulVec, add_neg_cancel] using h
  have heq : y t = y s := I.isOpen.is_const_of_deriv_eq_zero
    I.ordConnected.isPreconnected
    (fun r hr => (hy r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hy r hr).deriv) ht hs
  have hys : y s = x s := by simp [y]
  have hh := congrArg (fun v => (matrixExp A (t - s)).mulVec v) (heq.trans hys)
  change x t = (matrixExp A (t - s)).mulVec (x s)
  simpa only [y, Matrix.mulVec_mulVec, ← matrixExp_add_time,
    sub_add_sub_cancel, sub_self, matrixExp_zero, Matrix.one_mulVec] using hh

lemma matrixExp_mulVec_of_annihilated (N : Matrix n n 𝕂) (v : n → 𝕂)
    (m : ℕ) (hv : (N ^ m).mulVec v = 0) (t : ℝ) :
    (matrixExp N t).mulVec v =
      ∑ j ∈ range m, (t ^ j / (Nat.factorial j : ℝ)) • (N ^ j).mulVec v := by
  let ev := (mulVecContinuous (𝕂 := 𝕂) (n := n)).flip v
  have h := (matrixExp_hasSum N t).map ev ev.continuous
  change HasSum (fun j => ev ((t ^ j / (Nat.factorial j : ℝ)) • N ^ j))
    (ev (matrixExp N t)) at h
  simp only [map_smul] at h
  change HasSum (fun j => (t ^ j / (Nat.factorial j : ℝ)) • (N ^ j).mulVec v)
    ((matrixExp N t).mulVec v) at h
  rw [← h.tsum_eq]
  apply tsum_eq_sum
  intro j hj
  have hmj : m ≤ j := by simpa using hj
  have he : j = (j - m) + m := by omega
  rw [he, pow_add N, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero]

lemma matrixExp_generalized_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (μ : ℂ) (v : n → ℂ) (m : ℕ)
    (hv : ((A - μ • 1) ^ m).mulVec v = 0) :
    ∃ p : n → Polynomial ℂ, ∀ t : ℝ, ∀ k,
      (matrixExp A t).mulVec v k =
        (p k).eval (t : ℂ) * Complex.exp (μ * (t : ℂ)) := by
  let N := A - μ • (1 : Matrix n n ℂ)
  refine ⟨fun k => ∑ j ∈ range m,
    Polynomial.monomial j (((N ^ j).mulVec v k) / (Nat.factorial j : ℂ)), ?_⟩
  intro t k
  have hA : A = μ • (1 : Matrix n n ℂ) + N := by dsimp [N]; abel
  conv_lhs => rw [hA, matrixExp_scalar_add]
  rw [Matrix.smul_mulVec, matrixExp_mulVec_of_annihilated N v m hv]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [RCLike.real_smul_eq_coe_mul]
  change Complex.exp (μ * (t : ℂ)) *
    ((↑(t ^ j / (Nat.factorial j : ℝ)) : ℂ) * (N ^ j).mulVec v k) = _
  push_cast
  ring

lemma matrixExp_orbit_representation {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) :
    ∃ (r : ℕ) (μ : Fin r → ℂ) (p : n → Fin r → Polynomial ℂ),
      ∀ t : ℝ, ∀ k, (matrixExp A t).mulVec v k =
        ∑ l : Fin r, (p k l).eval (t : ℂ) * Complex.exp (μ l * (t : ℂ)) := by
  classical
  let T : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' A
  have htop := Module.End.iSup_maxGenEigenspace_eq_top T
  obtain ⟨f, hf, heq⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun μ => T.maxGenEigenspace μ) v).mp
      (htop.symm ▸ Submodule.mem_top)
  have hrep : ∀ μ : ℂ, ∃ p : n → Polynomial ℂ, ∀ t : ℝ, ∀ k,
      (matrixExp A t).mulVec (f μ) k =
        (p k).eval (t : ℂ) * Complex.exp (μ * (t : ℂ)) := by
    intro μ
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace T μ (f μ)).mp (hf μ)
    have hm' : ((A - μ • (1 : Matrix n n ℂ)) ^ m).mulVec (f μ) = 0 := by
      simpa only [← Matrix.toLinAlgEquiv'_apply, map_pow, map_sub, map_smul, map_one]
        using hm
    exact matrixExp_generalized_eigenvector A μ (f μ) m hm'
  choose p hp using hrep
  let e : f.support ≃ Fin (Fintype.card f.support) := Fintype.equivFin f.support
  refine ⟨Fintype.card f.support, fun l => (e.symm l).val,
    fun k l => p (e.symm l).val k, ?_⟩
  intro t k
  rw [← heq]
  change (matrixExp A t).mulVec (∑ μ ∈ f.support, f μ) k = _
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  simp_rw [hp]
  rw [← Finset.sum_attach f.support (fun μ => (p μ k).eval (t : ℂ) *
    Complex.exp (μ * (t : ℂ)))]
  exact
    (Fintype.sum_equiv e (fun μ => (p μ.val k).eval (t : ℂ) *
      Complex.exp (μ.val * (t : ℂ)))
      (fun l => (p (e.symm l).val k).eval (t : ℂ) *
        Complex.exp ((e.symm l).val * (t : ℂ))) (fun μ => by simp))

theorem complex_solution_representation :
    Specs.D13Unified.Ch07.JordanSolutions.complexRepresentationType := by
  intro n _ _ A I x hx s hs
  obtain ⟨r, μ, p, hp⟩ := matrixExp_orbit_representation A (x s)
  refine ⟨r, μ, p, fun t ht k => ?_⟩
  rw [matrix_solution_formula A I x hx s hs t ht]
  exact hp (t - s) k

theorem real_jordan_term : Specs.D13Unified.Ch07.JordanSolutions.realTermType := by
  intro c α β t j
  have hre : ((t : ℂ) ^ j).re = t ^ j := by rw [← Complex.ofReal_pow]; rfl
  have him : ((t : ℂ) ^ j).im = 0 := by rw [← Complex.ofReal_pow]; rfl
  constructor <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, hre, him, mul_comm] <;> ring

lemma complex_polynomial_real_imaginary (p : Polynomial ℂ) :
    ∃ a b : Polynomial ℝ, ∀ t : ℝ,
      (p.eval (t : ℂ)).re = a.eval t ∧ (p.eval (t : ℂ)).im = b.eval t := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, b, hab⟩ := hp
    obtain ⟨c, d, hcd⟩ := hq
    refine ⟨a + c, b + d, fun t => ?_⟩
    simp only [Polynomial.eval_add, Complex.add_re, Complex.add_im,
      (hab t).1, (hab t).2, (hcd t).1, (hcd t).2, and_self]
  | monomial j c =>
    refine ⟨Polynomial.monomial j c.re, Polynomial.monomial j c.im, fun t => ?_⟩
    simp only [Polynomial.eval_monomial]
    have hre : ((t : ℂ) ^ j).re = t ^ j := by rw [← Complex.ofReal_pow]; rfl
    have him : ((t : ℂ) ^ j).im = 0 := by rw [← Complex.ofReal_pow]; rfl
    simp [Complex.mul_re, Complex.mul_im, hre, him]

lemma complexify_matrix_solution {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (I : OpenTimeInterval) (x : ℝ → n → ℝ)
    (hx : Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue (matrixODE A) I x) :
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
      (matrixODE (A.map Complex.ofReal)) I (fun t k => (x t k : ℂ)) := by
  let c : (n → ℝ) →L[ℝ] (n → ℂ) :=
    ContinuousLinearMap.pi (fun k => Complex.ofRealCLM.comp (ContinuousLinearMap.proj k))
  have hc (v : n → ℝ) : c v = fun k => (v k : ℂ) := rfl
  refine ⟨?_, fun t ht => Set.mem_univ _, ?_⟩
  · exact c.contDiff.comp_contDiffOn hx.1
  · intro t ht
    have hd : HasDerivAt x (A.mulVec (x t)) t := by
      simpa only [matrixODE, ODE.eval, dite_eq_left (Set.mem_univ _)] using hx.2.2 t ht
    have h := c.hasFDerivAt.comp_hasDerivAt t hd
    have heq : c (A.mulVec (x t)) = (A.map Complex.ofReal).mulVec (c (x t)) := by
      ext i
      exact Complex.ofRealHom.map_mulVec A (x t) i
    rw [heq] at h
    simpa only [hc, Function.comp_def, matrixODE, ODE.eval,
      dite_eq_left (Set.mem_univ _)] using h

theorem real_solution_representation :
    Specs.D13Unified.Ch07.JordanSolutions.realRepresentationType := by
  intro n _ _ A I x hx s hs
  classical
  have hy := complexify_matrix_solution A I x hx
  obtain ⟨r, μ, p, hp⟩ := complex_solution_representation
    (A.map Complex.ofReal) I (fun t k => (x t k : ℂ)) hy s hs
  have hparts : ∀ k l, ∃ a b : Polynomial ℝ, ∀ t : ℝ,
      ((p k l).eval (t : ℂ)).re = a.eval t ∧
      ((p k l).eval (t : ℂ)).im = b.eval t :=
    fun k l => complex_polynomial_real_imaginary (p k l)
  choose a b hab using hparts
  refine ⟨r, fun l => (μ l).re, fun l => (μ l).im, a,
    fun k l => -(b k l), ?_⟩
  intro t ht k
  have h := congrArg Complex.re (hp t ht k)
  simp only [Complex.ofReal_re] at h
  rw [h]
  change Complex.reCLM (∑ l : Fin r, (p k l).eval (↑(t - s)) *
    Complex.exp (μ l * ↑(t - s))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  change ((p k l).eval (↑(t - s)) * Complex.exp (μ l * ↑(t - s))).re = _
  rw [Complex.mul_re, (hab k l (t - s)).1, (hab k l (t - s)).2]
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im, Polynomial.eval_neg]
  ring

lemma matrix_solution_real_linear {n : Type*} [Fintype n] [DecidableEq n]
    (σ : ℂ →L[ℝ] ℝ) (A : Matrix n n ℝ) (I : OpenTimeInterval)
    (z : ℝ → n → ℂ)
    (hz : Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
      (matrixODE (A.map Complex.ofReal)) I z) :
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
      (matrixODE A) I (fun t k => σ (z t k)) := by
  let c : (n → ℂ) →L[ℝ] (n → ℝ) :=
    ContinuousLinearMap.pi (fun k => σ.comp (ContinuousLinearMap.proj k))
  have hc (v : n → ℂ) : c v = fun k => σ (v k) := rfl
  refine ⟨c.contDiff.comp_contDiffOn hz.1, fun t ht => Set.mem_univ _, ?_⟩
  intro t ht
  have hd : HasDerivAt z ((A.map Complex.ofReal).mulVec (z t)) t := by
    simpa only [matrixODE, ODE.eval, dite_eq_left (Set.mem_univ _)] using hz.2.2 t ht
  have heq : c ((A.map Complex.ofReal).mulVec (z t)) = A.mulVec (c (z t)) := by
    ext k
    change σ (∑ j, (A k j : ℂ) * z t j) = ∑ j, A k j * σ (z t j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    convert! (map_smul σ (A k j) (z t j)) using 1
  have h := c.hasFDerivAt.comp_hasDerivAt t hd
  rw [heq] at h
  simpa only [hc, Function.comp_def, matrixODE, ODE.eval,
    dite_eq_left (Set.mem_univ _)] using h

theorem matrix_solution_real_imaginary :
    Specs.D13Unified.Ch07.JordanSolutions.realImaginarySolutionType := by
  intro n _ _ A I z hz
  exact ⟨matrix_solution_real_linear Complex.reCLM A I z hz,
    matrix_solution_real_linear Complex.imCLM A I z hz⟩

theorem real_generalized_eigenvector :
    Specs.D13Unified.Ch07.JordanSolutions.realGeneralizedEigenvectorType := by
  intro n _ _ A α β v m _hm hv
  classical
  obtain ⟨p, hp⟩ := matrixExp_generalized_eigenvector
    (A.map Complex.ofReal) (α + β * Complex.I) v m hv
  have hparts : ∀ k, ∃ a b : Polynomial ℝ, ∀ t : ℝ,
      ((p k).eval (t : ℂ)).re = a.eval t ∧
      ((p k).eval (t : ℂ)).im = b.eval t :=
    fun k => complex_polynomial_real_imaginary (p k)
  choose a b hab using hparts
  refine ⟨a, b, fun t k => ?_⟩
  change ((matrixExp (A.map Complex.ofReal) t).mulVec v k).re = _ ∧
    ((matrixExp (A.map Complex.ofReal) t).mulVec v k).im = _
  rw [hp t k]
  constructor <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
      (hab k t).1, (hab k t).2] <;> ring

end D13Unified.Ch07
