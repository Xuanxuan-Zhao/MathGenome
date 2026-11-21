import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.MalgrangeEhrenpreis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ProperSupportConvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.MvPolynomial.CommRing

noncomputable section
open scoped BigOperators fwdDiff
open MvPolynomial

theorem MvPolynomial.exists_real_eval_ne_zero {σ : Type*} (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    ∃ η : σ → ℝ, MvPolynomial.eval (fun i => (η i : ℂ)) P ≠ 0 := by
  by_contra! h
  apply hP
  apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  have hex : ∀ i, ∃ r : ℝ, (r : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose η hη using hex
  simpa only [map_zero] using (show MvPolynomial.eval x P = 0 by simpa only [hη] using h η)


theorem MvPolynomial.top_homogeneousComponent_ne_zero {σ : Type*} (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    MvPolynomial.homogeneousComponent P.totalDegree P ≠ 0 := by
  have hs : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP
  obtain ⟨α, hα, heq⟩ := Finset.exists_mem_eq_sup P.support hs (fun s => s.sum fun _ e => e)
  intro hz
  have hdeg : α.degree = P.totalDegree := heq.symm
  have hc := congrArg (fun Q : MvPolynomial σ ℂ => Q.coeff α) hz
  rw [MvPolynomial.coeff_homogeneousComponent, ite_eq_left hdeg, AddMonoidAlgebra.coeff_zero] at hc
  exact MvPolynomial.mem_support_iff.mp hα hc

namespace Polynomial
variable {R : Type*} [CommSemiring R]
lemma coeff_pow_of_natDegree_le' (p : R[X]) (D n : ℕ) (hp : p.natDegree ≤ D) :
    (p ^ n).coeff (n * D) = (p.coeff D) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul, coeff_mul_add_eq_of_natDegree_le
      (natDegree_pow_le.trans (Nat.mul_le_mul_left n hp)) hp, ih, pow_succ]

lemma coeff_prod_of_natDegree_le' {ι : Type*} (s : Finset ι) (p : ι → R[X])
    (D : ι → ℕ) (hp : ∀ i ∈ s, (p i).natDegree ≤ D i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, D i) = ∏ i ∈ s, (p i).coeff (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [coeff_mul_add_eq_of_natDegree_le (hp i (Finset.mem_insert_self ..))
      ((natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun j hj => hp j (Finset.mem_insert_of_mem hj)))),
      ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]
end Polynomial

namespace MvPolynomial
variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ]
def affineRestriction (P : MvPolynomial σ R) (a b : σ → R) : Polynomial R :=
  P.eval₂ Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i))

lemma affineRestriction_degree (P : MvPolynomial σ R) (a b : σ → R) :
    (affineRestriction P a b).natDegree ≤ P.totalDegree := by
  classical
  unfold affineRestriction
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro α hα
  apply le_trans Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_C, zero_add]
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  calc
    ∑ i, ((Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i)) ^ α i).natDegree
      ≤ ∑ i, α i := by
        apply Finset.sum_le_sum
        intro i _
        apply le_trans Polynomial.natDegree_pow_le
        calc
          α i * (Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i)).natDegree
            ≤ α i * 1 := by
              apply Nat.mul_le_mul_left
              exact Polynomial.natDegree_add_le_of_degree_le
                (Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using Polynomial.natDegree_X_le)) (by simp)
          _ = α i := Nat.mul_one _
    _ ≤ P.totalDegree := by
      rw [← Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)]
      exact MvPolynomial.le_totalDegree hα

lemma affineFactor_degree (a b : R) :
    (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1 :=
  Polynomial.natDegree_add_le_of_degree_le
    (Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, zero_add] using Polynomial.natDegree_X_le)) (by simp)

lemma affineProduct_degree (α : σ →₀ ℕ) (a b : σ → R) :
    (∏ i, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i)) ^ α i).natDegree
      ≤ α.degree := by
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  change _ ≤ α.sum (fun _ e => e)
  rw [Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)]
  apply Finset.sum_le_sum
  intro i _
  exact Polynomial.natDegree_pow_le.trans (by
    simpa using Nat.mul_le_mul_left (α i) (affineFactor_degree (a i) (b i)))

lemma affineProduct_coeff (α : σ →₀ ℕ) (a b : σ → R) :
    (∏ i, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i)) ^ α i).coeff α.degree =
      ∏ i, a i ^ α i := by
  change (∏ i, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i)) ^ α i).coeff (α.sum (fun _ e => e)) = _
  rw [Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)]
  rw [Polynomial.coeff_prod_of_natDegree_le' _ _ (fun i => α i) (fun i _ =>
    Polynomial.natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left (α i) (affineFactor_degree (a i) (b i))))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Nat.mul_one, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
    Polynomial.coeff_C, one_ne_zero, ite_eq_right, mul_one, add_zero, ite_false]
    using Polynomial.coeff_pow_of_natDegree_le'
      (Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i)) 1 (α i)
      (affineFactor_degree (a i) (b i))

lemma affineRestriction_top_coeff (P : MvPolynomial σ R) (a b : σ → R) :
    (affineRestriction P a b).coeff P.totalDegree =
      MvPolynomial.eval a (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  unfold affineRestriction
  rw [MvPolynomial.eval₂_eq', Polynomial.finsetSum_coeff]
  rw [MvPolynomial.homogeneousComponent_apply]
  simp only [map_sum, MvPolynomial.eval_monomial, Finsupp.prod_pow]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  rw [Polynomial.coeff_C_mul]
  by_cases hdeg : α.degree = P.totalDegree
  · rw [ite_eq_left hdeg, ← hdeg, affineProduct_coeff]
  · have hlt : α.degree < P.totalDegree :=
      lt_of_le_of_ne (MvPolynomial.le_totalDegree hα) hdeg
    rw [ite_eq_right hdeg, Polynomial.coeff_eq_zero_of_natDegree_lt
      ((affineProduct_degree α a b).trans_lt hlt), mul_zero]

end MvPolynomial
namespace Polynomial
variable {R : Type*} [CommRing R]
lemma finite_difference_top_coeff (Q : R[X]) (n : ℕ) (hQ : Q.natDegree ≤ n) :
    ∑ j ∈ Finset.range (n + 1), (((-1 : ℤ) ^ (n-j) * n.choose j) : ℤ) • Q.eval (j : R) =
      Q.coeff n * (n.factorial : R) := by
  have heq : (∑ j ∈ Finset.range (n + 1),
      (((-1 : ℤ) ^ (n-j) * n.choose j) : ℤ) • Q.eval (j : R)) =
      (fwdDiff (1 : R))^[n] Q.eval 0 := by
    simpa only [zero_add, nsmul_eq_mul, mul_one] using
      (fwdDiff_iter_eq_sum_shift (1 : R) Q.eval n 0).symm
  rw [heq]
  by_cases hn : Q.natDegree = n
  · rw [← hn, Q.fwdDiff_iter_degree_eq_factorial]
    simp only [Pi.smul_apply, Polynomial.leadingCoeff, smul_eq_mul, Pi.natCast_apply]
  · have hlt : Q.natDegree < n := lt_of_le_of_ne hQ hn
    rw [Q.fwdDiff_iter_eq_zero_of_degree_lt hlt,
      Q.coeff_eq_zero_of_natDegree_lt hlt, zero_mul, Pi.zero_apply]
end Polynomial

namespace MvPolynomial
variable {σ : Type*} [Fintype σ]
def reflectedTranslate (P : MvPolynomial σ ℂ) (b : σ → ℝ) : MvPolynomial σ ℂ :=
  P.eval₂ MvPolynomial.C (fun i => MvPolynomial.C (b i : ℂ) - MvPolynomial.X i)

lemma reflectedTranslate_eval (P : MvPolynomial σ ℂ) (b : σ → ℝ) (x : σ → ℂ) :
    MvPolynomial.eval x (reflectedTranslate P b) = MvPolynomial.eval (fun i => (b i : ℂ) - x i) P := by
  rw [reflectedTranslate, MvPolynomial.eval₂_eq']
  conv_rhs => rw [MvPolynomial.eval_eq']
  simp only [map_sum, map_mul, map_prod, map_pow, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
end MvPolynomial
namespace MvPolynomial
variable {σ R : Type*} [Fintype σ] [CommRing R]
lemma affineRestriction_eval (P : MvPolynomial σ R) (a b : σ → R) (t : R) :
    (affineRestriction P a b).eval t = MvPolynomial.eval (fun i => a i * t + b i) P := by
  classical
  rw [affineRestriction, MvPolynomial.eval₂_eq']
  conv_rhs => rw [MvPolynomial.eval_eq']
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]

lemma finite_difference_reflected_translate (P : MvPolynomial σ ℂ) (η : σ → ℝ) :
    ∑ j ∈ Finset.range (P.totalDegree + 1),
      (((-1 : ℤ) ^ (P.totalDegree-j) * P.totalDegree.choose j) : ℤ) •
        reflectedTranslate P (fun i => j * η i) =
    MvPolynomial.C (MvPolynomial.eval (fun i => (η i : ℂ))
      (MvPolynomial.homogeneousComponent P.totalDegree P) * (P.totalDegree.factorial : ℂ)) := by
  classical
  apply MvPolynomial.funext
  intro x
  simp only [map_sum, map_zsmul, MvPolynomial.eval_C]
  have h := Polynomial.finite_difference_top_coeff
    (affineRestriction P (fun i => (η i : ℂ)) (fun i => -x i)) P.totalDegree
    (affineRestriction_degree _ _ _)
  rw [affineRestriction_top_coeff] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [reflectedTranslate_eval, affineRestriction_eval]
  congr 2
  congr 1
  funext i
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast, sub_eq_add_neg]
  ring
end MvPolynomial

namespace MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- A nonzero polynomial admits a finite integer combination of real reflected
translates equal to a nonzero constant. The factor two matches the exponential
weight identity in the distributional construction. -/
theorem exists_reflected_translate_cancellation (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    ∃ (η : σ → ℝ) (c : ℂ), c ≠ 0 ∧
      (∑ j ∈ Finset.range (P.totalDegree + 1),
        (((-1 : ℤ) ^ (P.totalDegree-j) * P.totalDegree.choose j) : ℤ) •
          reflectedTranslate P (fun i => (2 * j : ℝ) * η i)) = MvPolynomial.C c := by
  obtain ⟨η, hη⟩ := exists_real_eval_ne_zero
    (MvPolynomial.homogeneousComponent P.totalDegree P) (top_homogeneousComponent_ne_zero P hP)
  refine ⟨fun i => η i / 2,
    MvPolynomial.eval (fun i => (η i : ℂ)) (MvPolynomial.homogeneousComponent P.totalDegree P) *
      (P.totalDegree.factorial : ℂ),
    mul_ne_zero hη (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), ?_⟩
  convert finite_difference_reflected_translate P η using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  funext i
  ring

omit [Fintype σ] in
lemma map_conj_ne_zero (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    MvPolynomial.map (starRingEnd ℂ) P ≠ 0 := by
  intro hz
  apply hP
  exact (MvPolynomial.map_injective (starRingEnd ℂ) (star_injective))
    (by simpa only [map_zero] using hz)


end MvPolynomial

open Set TopologicalSpace
open scoped Distributions

namespace ExpandedFA.Fourier.MalgrangeEhrenpreis
open ExpandedFA.Distributions
open Specs.ExpandedFA.Fourier.MalgrangeEhrenpreis

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

@[simp] theorem diracZero_apply (φ : GlobalTests 𝕜 d) : diracZero 𝕜 d φ = φ 0 := rfl

@[simp] theorem multiIndexWord_zero : multiIndexWord (fun _ : Fin d => 0) = [] := by
  simp [multiIndexWord]

@[simp] theorem testOperator_C (s c : 𝕜) :
    testOperator (d := d) s (MvPolynomial.C c) = c • LinearMap.id := by
  unfold testOperator
  rw [MvPolynomial.sum_C (by simp)]
  change (c * (-s) ^ (∑ i : Fin d, (0 : Fin d →₀ ℕ) i)) •
    (testPartialCLM (𝕜 := 𝕜) (Ω := ⊤) (multiIndexWord (fun _ => 0))).toLinearMap = _
  rw [multiIndexWord_zero]
  simp [testPartialCLM]

@[simp] theorem operator_C (s c : 𝕜) (u : GlobalDistribution 𝕜 d) :
    operator s (MvPolynomial.C c) u = c • u := by
  unfold operator
  rw [MvPolynomial.sum_C (b := fun α a =>
    ((a * s ^ (∑ i, α i)) •
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d ⊤ α u : GlobalDistribution 𝕜 d)) (by
      ext φ
      change (0 * s ^ (∑ i : Fin d, (0 : Fin d →₀ ℕ) i)) * _ = 0
      rw [zero_mul, zero_mul])]
  change (c * s ^ (∑ i : Fin d, (0 : Fin d →₀ ℕ) i)) •
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue 𝕜 d ⊤
      (multiIndexWord (fun _ => 0)) u = _
  rw [multiIndexWord_zero]
  simp [Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue, testPartialCLM]

theorem order_zero : OrderZero := by
  intro 𝕜 _ d s c hc
  rw [operator_C, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem zero_dimension : ZeroDimension := by
  intro 𝕜 _ s P hP
  have hC := MvPolynomial.eq_C_of_isEmpty P
  have hc : P.coeff 0 ≠ 0 := by
    intro h
    apply hP
    rw [hC, h, map_zero]
  refine ⟨(P.coeff 0)⁻¹ • diracZero 𝕜 0, ?_⟩
  conv_lhs => rw [hC]
  simpa using order_zero 𝕜 0 s (P.coeff 0) hc

theorem operator_formula : OperatorFormula := by
  intro 𝕜 _ d s P u φ
  classical
  simp only [operator, testOperator, Finsupp.sum,
    sum_apply, LinearMap.sum_apply, map_sum,
    smul_apply, LinearMap.smul_apply, map_smul,
    ContinuousLinearMap.coe_coe,
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue,
    ExpandedFA.Distributions.multiIndexWord_length, smul_eq_mul,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro α _
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

theorem pairing_criterion : PairingCriterion := by
  intro 𝕜 _ d s P E
  constructor
  · intro h φ
    rw [← operator_formula 𝕜 d s P E φ, h, diracZero_apply]
  · intro h
    ext φ
    rw [operator_formula 𝕜 d s P E φ, diracZero_apply, h]

/-- The operator is scalar-linear in its distribution argument. -/
def operatorLM (s : 𝕜) (P : Symbol 𝕜 d) :
    GlobalDistribution 𝕜 d →ₗ[𝕜] GlobalDistribution 𝕜 d where
  toFun := operator s P
  map_add' u v := by
    ext φ
    simp only [operator_formula 𝕜 d s P, add_apply]
  map_smul' c u := by
    ext φ
    simp only [operator_formula 𝕜 d s P, smul_apply, RingHom.id_apply]

def operatorSymbolLM (s : 𝕜) (u : GlobalDistribution 𝕜 d) :
    Symbol 𝕜 d →ₗ[𝕜] GlobalDistribution 𝕜 d where
  toFun P := operator s P u
  map_add' P Q := by
    unfold operator
    change (P.coeff + Q.coeff).sum _ = _
    rw [Finsupp.sum_add_index']
    · intro α; ext φ; simp
    · intro α a b; ext φ; simp [add_mul]
  map_smul' c P := by
    unfold operator
    change (c • P.coeff).sum _ = _
    rw [Finsupp.sum_smul_index]
    · simp only [Finsupp.sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro α _
      simp [smul_smul, mul_assoc]
    · intro α; ext φ; simp

@[simp] theorem operatorSymbolLM_apply (s : 𝕜) (u : GlobalDistribution 𝕜 d)
    (P : Symbol 𝕜 d) : operatorSymbolLM s u P = operator s P u := rfl

@[simp] theorem operator_monomial (s : 𝕜) (α : Fin d →₀ ℕ) (c : 𝕜)
    (u : GlobalDistribution 𝕜 d) :
    operator s (MvPolynomial.monomial α c) u =
      (c * s ^ (∑ i, α i)) •
        Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
          𝕜 d ⊤ α u := by
  unfold operator
  rw [MvPolynomial.sum_monomial_eq (by ext φ; simp)]

/-- Absorb a common derivative normalization into the polynomial coefficients. -/
def rescaleSymbol (s : 𝕜) (P : Symbol 𝕜 d) : Symbol 𝕜 d :=
  P.coeff.sum fun α c => MvPolynomial.monomial α (c * s ^ (∑ i, α i))

@[simp] theorem coeff_rescaleSymbol (s : 𝕜) (P : Symbol 𝕜 d) (α : Fin d →₀ ℕ) :
    (rescaleSymbol s P).coeff α = P.coeff α * s ^ (∑ i, α i) := by
  classical
  simp only [rescaleSymbol, Finsupp.sum, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.notMem_support_iff.mp h, zero_mul]

theorem rescaleSymbol_ne_zero (s : 𝕜) (hs : s ≠ 0) (P : Symbol 𝕜 d) (hP : P ≠ 0) :
    rescaleSymbol s P ≠ 0 := by
  intro h
  apply hP
  ext α
  have ha := congrArg (fun Q : Symbol 𝕜 d => Q.coeff α) h
  simpa [coeff_rescaleSymbol, pow_ne_zero _ hs] using ha

@[simp] theorem operator_rescaleSymbol (s : 𝕜) (P : Symbol 𝕜 d)
    (u : GlobalDistribution 𝕜 d) :
    operator 1 (rescaleSymbol s P) u = operator s P u := by
  change operatorSymbolLM 1 u (rescaleSymbol s P) = _
  classical
  simp only [rescaleSymbol, Finsupp.sum, map_sum, operatorSymbolLM_apply,
    operator_monomial, one_pow, mul_one]
  rfl


/-- The native compact-step topology controls every Schwartz seminorm.
This is the continuity bridge from LF tests; compact support is used uniformly
on an entire step, rather than separately for each test. -/
def stepSchwartzLM (K : Compacts (Domain d)) :
    Step 𝕜 K →ₗ[𝕜] SchwartzMap (Domain d) 𝕜 where
  toFun φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

theorem stepSchwartz_bound (K : Compacts (Domain d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (k n : ℕ) (φ : Step 𝕜 K),
      SchwartzMap.seminorm 𝕜 k n (stepSchwartzLM K φ) ≤
        R ^ k * ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K n φ := by
  obtain ⟨R, hR, hbound⟩ := K.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R, hR, ?_⟩
  intro k n φ
  apply SchwartzMap.seminorm_le_bound 𝕜 k n _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n φ x‖ ≤ _
  by_cases hx : x ∈ K
  · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hbound x hx) k)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜)
      (norm_nonneg _) (by positivity)
  · simp only [φ.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
    positivity

/-- Continuous inclusion of a fixed compact step into Schwartz space. -/
def stepSchwartzCLM (K : Compacts (Domain d)) :
    Step 𝕜 K →L[𝕜] SchwartzMap (Domain d) 𝕜 where
  toLinearMap := stepSchwartzLM K
  cont := by
    apply WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms 𝕜 (Domain d) 𝕜 ⊤ K)
      (schwartz_withSeminorms 𝕜 (Domain d) 𝕜)
    obtain ⟨R, hR, hbound⟩ := stepSchwartz_bound (𝕜 := 𝕜) K
    rintro ⟨k, n⟩
    refine ⟨{n}, ⟨R ^ k, by positivity⟩, ?_⟩
    intro φ
    simp only [Finset.sup_singleton]
    change SchwartzMap.seminorm 𝕜 k n (stepSchwartzLM K φ) ≤
      R ^ k * ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ K n φ
    exact hbound k n φ

/-- Continuous inclusion of the actual LF test space into Schwartz space. -/
def testSchwartzCLM : GlobalTests 𝕜 d →L[𝕜] SchwartzMap (Domain d) 𝕜 :=
  TestFunction.mkCLM 𝕜
    (fun φ => φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    (fun φ ψ => by ext x; rfl) (fun c φ => by ext x; rfl)
    (fun K _ => (stepSchwartzCLM K).continuous)

@[simp] theorem testSchwartzCLM_apply (φ : GlobalTests 𝕜 d) (x : Domain d) :
    testSchwartzCLM φ x = φ x := rfl

/-- The Fourier transform uses the Euclidean norm; the distribution test space
uses the coordinate sup norm. This continuous bridge retains the exact function. -/
def euclideanTestSchwartzCLM : GlobalTests 𝕜 d →L[𝕜] ExpandedFA.Fourier.Schwartz 𝕜 d :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜
    (EuclideanSpace.equiv (Fin d) ℝ)).comp testSchwartzCLM

@[simp] theorem euclideanTestSchwartzCLM_apply (φ : GlobalTests 𝕜 d)
    (x : ExpandedFA.Fourier.Euclidean d) :
    euclideanTestSchwartzCLM φ x = φ (fun i => x i) := rfl

/-- The Schwartz embedding intertwines the genuine first derivatives. -/
theorem testSchwartzCLM_partial (i : Fin d) (φ : GlobalTests 𝕜 d) :
    testSchwartzCLM (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ) =
      LineDeriv.lineDerivOpCLM 𝕜 (SchwartzMap (Domain d) 𝕜)
        (coordinateVector i) (testSchwartzCLM φ) := by
  ext x
  rw [testSchwartzCLM_apply, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ φ x (coordinateVector i) = fderiv ℝ φ x (coordinateVector i)
  exact (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv

/-- The norm change also preserves the coordinate derivatives. -/
theorem euclideanTestSchwartzCLM_partial (i : Fin d) (φ : GlobalTests 𝕜 d) :
    euclideanTestSchwartzCLM (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ) =
      LineDeriv.lineDerivOpCLM 𝕜 (ExpandedFA.Fourier.Schwartz 𝕜 d)
        (ExpandedFA.Fourier.basisVector i) (euclideanTestSchwartzCLM φ) := by
  change SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 _
      (testSchwartzCLM (TestFunction.lineDerivCLM 𝕜 _ φ)) = _
  rw [testSchwartzCLM_partial]
  symm
  apply (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv
    (𝕜 := 𝕜) (ExpandedFA.Fourier.basisVector i)
    (EuclideanSpace.equiv (Fin d) ℝ) (testSchwartzCLM φ)).trans
  congr 2

open scoped FourierTransform in
theorem inverseFourier_testPartial (w : List (Fin d)) (φ : GlobalTests ℂ d)
    (ξ : ExpandedFA.Fourier.Euclidean d) :
    (𝓕⁻ (euclideanTestSchwartzCLM (testPartialCLM w φ))) ξ =
      (w.map (fun i => -(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ))).prod *
        (𝓕⁻ (euclideanTestSchwartzCLM φ)) ξ := by
  induction w with
  | nil => simp [testPartialCLM]
  | cons i w ih =>
    change (𝓕⁻ (euclideanTestSchwartzCLM
      (TestFunction.lineDerivCLM ℂ (coordinateVector i) (testPartialCLM w φ)))) ξ = _
    rw [euclideanTestSchwartzCLM_partial]
    change (𝓕⁻ (LineDeriv.lineDerivOp (ExpandedFA.Fourier.basisVector i)
      (euclideanTestSchwartzCLM (testPartialCLM w φ)))) ξ = _
    rw [SchwartzMap.fourierInv_lineDerivOp_eq]
    have ht : (fun x : ExpandedFA.Fourier.Euclidean d =>
        inner ℝ x (ExpandedFA.Fourier.basisVector i)).HasTemperateGrowth := by fun_prop
    simp only [smul_apply, SchwartzMap.smulLeftCLM_apply ht, smul_eq_mul,
      List.map_cons, List.prod_cons]
    rw [ih]
    simp [ExpandedFA.Fourier.basisVector, EuclideanSpace.inner_single_right,
      mul_assoc]

theorem multiIndexWord_prod (α : Fin d → ℕ) (a : Fin d → ℂ) :
    ((multiIndexWord α).map a).prod = ∏ i, a i ^ α i := by
  have h (l : List (Fin d)) :
      ((l.flatMap (fun i => List.replicate (α i) i)).map a).prod =
        (l.map (fun i => a i ^ α i)).prod := by
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]
  simpa [multiIndexWord, List.map_ofFn, List.prod_ofFn] using
    h (List.ofFn (fun i : Fin d => i))

open scoped FourierTransform in
/-- The complete transpose operator has precisely the normalized Fourier
symbol, including its scale and every multi-index sign. -/
theorem inverseFourier_testOperator (s : ℂ) (P : Symbol ℂ d) (φ : GlobalTests ℂ d)
    (ξ : ExpandedFA.Fourier.Euclidean d) :
    (𝓕⁻ (euclideanTestSchwartzCLM (testOperator s P φ))) ξ =
      MvPolynomial.eval (fun i => s * (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ)) P *
        (𝓕⁻ (euclideanTestSchwartzCLM φ)) ξ := by
  classical
  let T := (FourierTransform.fourierInvCLM ℂ (ExpandedFA.Fourier.Schwartz ℂ d)).comp
    (euclideanTestSchwartzCLM (𝕜 := ℂ) (d := d))
  change T (testOperator s P φ) ξ = _
  simp only [testOperator, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, sum_apply, smul_apply,
    MvPolynomial.eval_eq', Finset.sum_mul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro α _
  change (P.coeff α * (-s) ^ (∑ i, α i)) *
    (𝓕⁻ (euclideanTestSchwartzCLM (testPartialCLM (multiIndexWord α) φ))) ξ = _
  rw [inverseFourier_testPartial, multiIndexWord_prod]
  rw [← Finset.prod_pow_eq_pow_sum]
  have hp : (∏ i, (-s) ^ α i) *
      (∏ i, (-(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ)) ^ α i) =
      ∏ i, (s * (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ)) ^ α i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = (P.coeff α * ((∏ i, (-s) ^ α i) *
        (∏ i, (-(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ)) ^ α i))) *
        (𝓕⁻ (euclideanTestSchwartzCLM φ)) ξ := by ring
    _ = _ := by rw [hp]

/-- The quotient is assigned zero at a zero of z. This leaves the
polynomial cancellation identity valid everywhere. -/
def conjugateQuotient (z : ℂ) : ℂ := starRingEnd ℂ z / z

theorem norm_conjugateQuotient_le (z : ℂ) : ‖conjugateQuotient z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [conjugateQuotient, hz]
  · simp [conjugateQuotient, norm_ne_zero_iff.mpr hz]

theorem mul_conjugateQuotient (z : ℂ) : z * conjugateQuotient z = starRingEnd ℂ z := by
  by_cases hz : z = 0
  · simp [conjugateQuotient, hz]
  · simp [conjugateQuotient, mul_div_assoc', hz]

open MeasureTheory in
/-- Any measurable bounded symbol, without smoothness, defines a continuous
scalar-linear functional on Schwartz space. -/
def boundedSymbolFunctional (q : ExpandedFA.Fourier.Euclidean d → ℂ)
    (hq : Measurable q) (C : ℝ) (hC : ∀ ξ, ‖q ξ‖ ≤ C) :
    ExpandedFA.Fourier.Tempered ℂ d :=
  let hqLp : MemLp q ⊤ volume := memLp_top_of_bound hq.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing volume ⊤ 1 (hqLp.toLp q)).comp
    (SchwartzMap.toLpCLM ℂ ℂ 1 volume)

open MeasureTheory in
theorem boundedSymbolFunctional_apply (q : ExpandedFA.Fourier.Euclidean d → ℂ)
    (hq : Measurable q) (C : ℝ) (hC : ∀ ξ, ‖q ξ‖ ≤ C)
    (φ : ExpandedFA.Fourier.Schwartz ℂ d) :
    boundedSymbolFunctional q hq C hC φ = ∫ ξ, φ ξ * q ξ := by
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume ⊤ 1
    ((memLp_top_of_bound hq.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC) : MemLp q ⊤ volume).toLp q)
    (SchwartzMap.toLpCLM ℂ ℂ 1 volume φ) = _
  rw [SchwartzMap.toLpCLM_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(memLp_top_of_bound hq.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC) : MemLp q ⊤ volume).coeFn_toLp,
    φ.coeFn_toLp 1 volume] with ξ hξ hφ
  simp [hξ, hφ, mul_comm]

/-- An inverse Fourier transform of a bounded measurable symbol, restricted
to the actual LF test space. Its type includes distributional continuity. -/
def boundedSymbolDistribution (q : ExpandedFA.Fourier.Euclidean d → ℂ)
    (hq : Measurable q) (C : ℝ) (hC : ∀ ξ, ‖q ξ‖ ≤ C) : GlobalDistribution ℂ d :=
  (boundedSymbolFunctional q hq C hC).comp
    ((FourierTransform.fourierInvCLM ℂ (ExpandedFA.Fourier.Schwartz ℂ d)).comp
      euclideanTestSchwartzCLM)

open MeasureTheory in
theorem boundedSymbolDistribution_apply (q : ExpandedFA.Fourier.Euclidean d → ℂ)
    (hq : Measurable q) (C : ℝ) (hC : ∀ ξ, ‖q ξ‖ ≤ C) (φ : GlobalTests ℂ d) :
    boundedSymbolDistribution q hq C hC φ =
      ∫ ξ, (FourierTransform.fourierInvCLM ℂ (ExpandedFA.Fourier.Schwartz ℂ d)
        (euclideanTestSchwartzCLM φ)) ξ * q ξ :=
  boundedSymbolFunctional_apply q hq C hC _

open MeasureTheory in
open scoped FourierTransform in
theorem integral_inverseFourier_schwartz (φ : ExpandedFA.Fourier.Schwartz ℂ d) :
    ∫ ξ, (𝓕⁻ φ : ExpandedFA.Fourier.Schwartz ℂ d) ξ = φ 0 := by
  have h := congrArg (fun f : ExpandedFA.Fourier.Schwartz ℂ d => f 0)
    (FourierTransform.fourier_fourierInv_eq (F := ExpandedFA.Fourier.Schwartz ℂ d) φ)
  change (𝓕 ((𝓕⁻ φ : ExpandedFA.Fourier.Schwartz ℂ d) : ExpandedFA.Fourier.Euclidean d → ℂ)) 0 = φ 0 at h
  simpa only [Real.fourier_eq', inner_zero_right, Complex.ofReal_zero,
    mul_zero, zero_mul, Complex.exp_zero, one_smul] using h


open MeasureTheory in
open scoped FourierTransform in
theorem boundedSymbolDistribution_operator (q : ExpandedFA.Fourier.Euclidean d → ℂ)
    (hq : Measurable q) (C : ℝ) (hC : ∀ ξ, ‖q ξ‖ ≤ C)
    (P Q : Symbol ℂ d)
    (hcancel : ∀ ξ, MvPolynomial.eval
      (fun i => 2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) P * q ξ =
      MvPolynomial.eval (fun i => 2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) Q) :
    operator 1 P (boundedSymbolDistribution q hq C hC) =
      operator 1 Q (diracZero ℂ d) := by
  ext φ
  rw [operator_formula, boundedSymbolDistribution_apply, operator_formula,
    diracZero_apply]
  have hi := integral_inverseFourier_schwartz
    (euclideanTestSchwartzCLM (testOperator 1 Q φ))
  have heval : euclideanTestSchwartzCLM (testOperator 1 Q φ)
      (0 : ExpandedFA.Fourier.Euclidean d) = testOperator 1 Q φ 0 := by
    rw [euclideanTestSchwartzCLM_apply]
    congr 1
  rw [heval] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with ξ
  change (𝓕⁻ (euclideanTestSchwartzCLM (testOperator 1 P φ))) ξ * q ξ = _
  rw [inverseFourier_testOperator, inverseFourier_testOperator]
  simp only [one_mul]
  rw [mul_right_comm, hcancel]

/-- The polynomial evaluated along the real frequency plane translated by b. -/
def shiftedSymbol (P : Symbol ℂ d) (b : Domain d)
    (ξ : ExpandedFA.Fourier.Euclidean d) : ℂ :=
  MvPolynomial.eval (fun i => 2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ) + (b i : ℂ)) P

theorem shiftedSymbol_continuous (P : Symbol ℂ d) (b : Domain d) :
    Continuous (shiftedSymbol P b) := by
  apply P.continuous_eval.comp
  exact continuous_pi fun i => by fun_prop

theorem shiftedQuotient_measurable (P : Symbol ℂ d) (b : Domain d) :
    Measurable (fun ξ => conjugateQuotient (shiftedSymbol P b ξ)) := by
  exact ((Complex.continuous_conj.comp (shiftedSymbol_continuous P b)).measurable).div
    (shiftedSymbol_continuous P b).measurable

/-- The continuous distribution obtained from the bounded quotient. -/
def quotientDistribution (P : Symbol ℂ d) (b : Domain d) : GlobalDistribution ℂ d :=
  boundedSymbolDistribution (fun ξ => conjugateQuotient (shiftedSymbol P b ξ))
    (shiftedQuotient_measurable P b) 1 (fun _ξ => norm_conjugateQuotient_le _)

section ExponentialWeight
open MeasureTheory
open scoped FourierTransform
def exponentialLinearForm (b : Domain d) : Domain d →L[ℝ] ℂ :=
  ∑ i, (b i : ℂ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))
@[simp] theorem exponentialLinearForm_apply (b x : Domain d) :
    exponentialLinearForm b x = ∑ i, (b i : ℂ) * (x i : ℂ) := by
  simp [exponentialLinearForm, smul_eq_mul]
@[simp] theorem exponentialLinearForm_coordinate (b : Domain d) (i : Fin d) :
    exponentialLinearForm b (coordinateVector i) = (b i : ℂ) := by
  classical
  simp [exponentialLinearForm_apply, coordinateVector, Pi.single_apply, apply_ite]
def exponentialWeight (b : Domain d) : SmoothCoefficient ℂ (⊤ : Opens (Domain d)) :=
  ⟨fun x => Complex.exp (exponentialLinearForm b x),
    ((exponentialLinearForm b).contDiff.cexp).contDiffOn⟩
@[simp] theorem exponentialWeight_partial (b : Domain d) (i : Fin d) (x : Domain d) :
    fderiv ℝ (exponentialWeight b).val x (coordinateVector i) =
      (b i : ℂ) * (exponentialWeight b).val x := by
  change fderiv ℝ (fun y => Complex.exp (exponentialLinearForm b y)) x _ = _
  rw [((exponentialLinearForm b).hasFDerivAt.cexp).fderiv]
  change Complex.exp (exponentialLinearForm b x) *
    exponentialLinearForm b (coordinateVector i) = _
  rw [exponentialLinearForm_coordinate]
  exact mul_comm _ _
def exponentialTestCLM (b : Domain d) : GlobalTests ℂ d →L[ℂ] GlobalTests ℂ d :=
  multiplyTestCLM (exponentialWeight b)
@[simp] theorem exponentialTestCLM_apply (b : Domain d) (φ : GlobalTests ℂ d) (x) :
    exponentialTestCLM b φ x = Complex.exp (exponentialLinearForm b x) * φ x := rfl

theorem exponentialTestCLM_partial (b : Domain d) (i : Fin d) (φ : GlobalTests ℂ d) :
    testPartialCLM [i] (exponentialTestCLM b φ) =
      (b i : ℂ) • exponentialTestCLM b φ + exponentialTestCLM b (testPartialCLM [i] φ) := by
  rw [exponentialTestCLM, partial_multiplyTest]
  congr 1
  ext x
  simp [coefficientPartial, exponentialWeight_partial, mul_assoc]
theorem inverseFourier_exponential_partial (b : Domain d) (i : Fin d)
    (φ : GlobalTests ℂ d) (ξ : ExpandedFA.Fourier.Euclidean d) :
    (𝓕⁻ (euclideanTestSchwartzCLM (exponentialTestCLM b (testPartialCLM [i] φ)))) ξ =
      (-(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) - (b i : ℂ)) *
        (𝓕⁻ (euclideanTestSchwartzCLM (exponentialTestCLM b φ))) ξ := by
  let T := (FourierTransform.fourierInvCLM ℂ (ExpandedFA.Fourier.Schwartz ℂ d)).comp
    (euclideanTestSchwartzCLM (𝕜 := ℂ) (d := d))
  have h := congrArg (fun ψ => T ψ ξ) (exponentialTestCLM_partial b i φ)
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at h
  change (𝓕⁻ (euclideanTestSchwartzCLM
    (testPartialCLM [i] (exponentialTestCLM b φ)))) ξ = _ at h
  rw [inverseFourier_testPartial] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  change T (exponentialTestCLM b (testPartialCLM [i] φ)) ξ = _
  change -(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) *
    T (exponentialTestCLM b φ) ξ = _ at h
  change T (exponentialTestCLM b (testPartialCLM [i] φ)) ξ =
    (-(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) - (b i : ℂ)) *
      T (exponentialTestCLM b φ) ξ
  linear_combination -h

theorem inverseFourier_exponential_testPartial (b : Domain d) (w : List (Fin d))
    (φ : GlobalTests ℂ d) (ξ : ExpandedFA.Fourier.Euclidean d) :
    (𝓕⁻ (euclideanTestSchwartzCLM (exponentialTestCLM b (testPartialCLM w φ)))) ξ =
      (w.map (fun i => -(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) - (b i : ℂ))).prod *
        (𝓕⁻ (euclideanTestSchwartzCLM (exponentialTestCLM b φ))) ξ := by
  induction w with
  | nil => simp [testPartialCLM]
  | cons i w ih =>
    change (𝓕⁻ (euclideanTestSchwartzCLM
      (exponentialTestCLM b (testPartialCLM [i] (testPartialCLM w φ))))) ξ = _
    rw [inverseFourier_exponential_partial, ih]
    simp [List.map_cons, List.prod_cons, mul_assoc]

theorem inverseFourier_exponential_testOperator (b : Domain d) (P : Symbol ℂ d)
    (φ : GlobalTests ℂ d) (ξ : ExpandedFA.Fourier.Euclidean d) :
    (𝓕⁻ (euclideanTestSchwartzCLM (exponentialTestCLM b (testOperator 1 P φ)))) ξ =
      shiftedSymbol P b ξ *
        (𝓕⁻ (euclideanTestSchwartzCLM (exponentialTestCLM b φ))) ξ := by
  classical
  let T := ((FourierTransform.fourierInvCLM ℂ (ExpandedFA.Fourier.Schwartz ℂ d)).comp
    (euclideanTestSchwartzCLM (𝕜 := ℂ) (d := d))).comp (exponentialTestCLM b)
  change T (testOperator 1 P φ) ξ = _
  simp only [testOperator, shiftedSymbol, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, sum_apply, smul_apply,
    MvPolynomial.eval_eq', Finset.sum_mul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro α _
  change (P.coeff α * (-1 : ℂ) ^ (∑ i, α i)) *
    (𝓕⁻ (euclideanTestSchwartzCLM
      (exponentialTestCLM b (testPartialCLM (multiIndexWord α) φ)))) ξ = _
  rw [inverseFourier_exponential_testPartial, multiIndexWord_prod]
  rw [← Finset.prod_pow_eq_pow_sum]
  calc
    _ = P.coeff α * ((∏ i : Fin d, (-1 : ℂ) ^ α i) *
        (∏ i, (-(2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) - (b i : ℂ)) ^ α i)) *
        (𝓕⁻ (euclideanTestSchwartzCLM (exponentialTestCLM b φ))) ξ := by ring
    _ = _ := by
      congr 2
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← mul_pow]
      congr 1
      ring

def translateSymbol (P : Symbol ℂ d) (c : Fin d → ℂ) : Symbol ℂ d :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (c i)) P

@[simp] theorem eval_translateSymbol (P : Symbol ℂ d) (c z : Fin d → ℂ) :
    MvPolynomial.eval z (translateSymbol P c) = MvPolynomial.eval (fun i => z i + c i) P := by
  rw [translateSymbol, ← MvPolynomial.eval_assoc]
  apply congrArg (fun z : Fin d → ℂ => MvPolynomial.eval z P)
  funext i
  simp

theorem euclideanTestSchwartzCLM_injective :
    Function.Injective (euclideanTestSchwartzCLM (𝕜 := ℂ) (d := d)) := by
  intro φ ψ h
  ext x
  have hx := congrArg (fun f : ExpandedFA.Fourier.Schwartz ℂ d =>
    f ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) h
  change φ ((EuclideanSpace.equiv (Fin d) ℝ)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) =
    ψ ((EuclideanSpace.equiv (Fin d) ℝ)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) at hx
  rw [ContinuousLinearEquiv.apply_symm_apply] at hx
  exact hx

theorem exponentialTestCLM_testOperator (b : Domain d) (Q : Symbol ℂ d)
    (φ : GlobalTests ℂ d) :
    testOperator 1 Q (exponentialTestCLM b φ) =
      exponentialTestCLM b (testOperator 1 (translateSymbol Q (fun i => -(b i : ℂ))) φ) := by
  apply euclideanTestSchwartzCLM_injective
  apply (FourierTransform.fourierCLE ℂ (ExpandedFA.Fourier.Schwartz ℂ d)).symm.injective
  ext ξ
  change (𝓕⁻ (euclideanTestSchwartzCLM (testOperator 1 Q (exponentialTestCLM b φ)))) ξ =
    (𝓕⁻ (euclideanTestSchwartzCLM
      (exponentialTestCLM b (testOperator 1 (translateSymbol Q (fun i => -(b i : ℂ))) φ)))) ξ
  rw [inverseFourier_testOperator, inverseFourier_exponential_testOperator]
  simp [shiftedSymbol]


theorem weightedBoundedSymbolDistribution_operator
    (q : ExpandedFA.Fourier.Euclidean d → ℂ) (hq : Measurable q)
    (C : ℝ) (hC : ∀ ξ, ‖q ξ‖ ≤ C) (b : Domain d) (P Q : Symbol ℂ d)
    (hcancel : ∀ ξ, shiftedSymbol P b ξ * q ξ =
      MvPolynomial.eval (fun i => 2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) Q) :
    operator 1 P ((boundedSymbolDistribution q hq C hC).comp (exponentialTestCLM b)) =
      operator 1 (translateSymbol Q (fun i => -(b i : ℂ))) (diracZero ℂ d) := by
  ext φ
  rw [operator_formula, ContinuousLinearMap.comp_apply, boundedSymbolDistribution_apply,
    operator_formula, diracZero_apply]
  have hi := integral_inverseFourier_schwartz
    (euclideanTestSchwartzCLM (testOperator 1 Q (exponentialTestCLM b φ)))
  have heval : euclideanTestSchwartzCLM (testOperator 1 Q (exponentialTestCLM b φ))
      (0 : ExpandedFA.Fourier.Euclidean d) =
        testOperator 1 (translateSymbol Q (fun i => -(b i : ℂ))) φ 0 := by
    rw [euclideanTestSchwartzCLM_apply, exponentialTestCLM_testOperator,
      exponentialTestCLM_apply]
    simp [exponentialLinearForm_apply]
    congr 1
  rw [heval] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with ξ
  change (𝓕⁻ (euclideanTestSchwartzCLM
    (exponentialTestCLM b (testOperator 1 P φ)))) ξ * q ξ = _
  rw [inverseFourier_exponential_testOperator, inverseFourier_testOperator]
  simp only [one_mul]
  rw [mul_right_comm, hcancel]

theorem eval_reflected_conjugate (P : Symbol ℂ d) (b : Domain d)
    (ξ : ExpandedFA.Fourier.Euclidean d) :
    MvPolynomial.eval (fun i => 2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ))
        (MvPolynomial.reflectedTranslate (P.map (starRingEnd ℂ)) b) =
      starRingEnd ℂ (shiftedSymbol P b ξ) := by
  rw [MvPolynomial.reflectedTranslate_eval, MvPolynomial.eval_map,
    shiftedSymbol, MvPolynomial.eval₂_comp]
  apply congrArg (fun z : Fin d → ℂ => MvPolynomial.eval₂ (starRingEnd ℂ) z P)
  funext i
  simp [map_ofNat]
  ring

theorem translateSymbol_reflectedTranslate (Q : Symbol ℂ d) (b : Domain d) :
    translateSymbol (MvPolynomial.reflectedTranslate Q b) (fun i => -(b i : ℂ)) =
      MvPolynomial.reflectedTranslate Q (fun i => 2 * b i) := by
  unfold translateSymbol MvPolynomial.reflectedTranslate
  change MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.X i + MvPolynomial.C (-(b i : ℂ)))
    (MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.C (b i : ℂ) - MvPolynomial.X i) Q) = _
  rw [MvPolynomial.hom_eval₂ Q MvPolynomial.C
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : Fin d => MvPolynomial.X i + MvPolynomial.C (-(b i : ℂ))))]
  congr 1
  · ext c
    simp
  · funext i
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_ofNat]
    ring

def exponentialQuotientDistribution (P : Symbol ℂ d) (b : Domain d) : GlobalDistribution ℂ d :=
  (quotientDistribution P b).comp (exponentialTestCLM b)

theorem exponentialQuotientDistribution_operator (P : Symbol ℂ d) (b : Domain d) :
    operator 1 P (exponentialQuotientDistribution P b) =
      operator 1 (MvPolynomial.reflectedTranslate (P.map (starRingEnd ℂ))
        (fun i => 2 * b i)) (diracZero ℂ d) := by
  have h := weightedBoundedSymbolDistribution_operator
    (fun ξ => conjugateQuotient (shiftedSymbol P b ξ))
    (shiftedQuotient_measurable P b) 1 (fun _ => norm_conjugateQuotient_le _)
    b P (MvPolynomial.reflectedTranslate (P.map (starRingEnd ℂ)) b)
    (fun ξ => by rw [mul_conjugateQuotient, eval_reflected_conjugate])
  rw [translateSymbol_reflectedTranslate] at h
  exact h


end ExponentialWeight

open ExpandedFA.Distributions.ProperSupportConvolution

/-- A cutoff on the larger set ℝᵈ × supp v works for every left distribution.
This supplies a common cutoff for the linearity proof, even when supports cancel. -/
private def UniversalLeftCutoff (v : GlobalDistribution 𝕜 d) (φ : GlobalTests 𝕜 d)
    (χ : ProductTests ℝ d) : Prop :=
  ∃ V : Set (Domain d × Domain d), IsOpen V ∧
    additionSlice Set.univ (distributionSupport v) (tsupport φ) ⊆ V ∧ EqOn χ 1 V

private theorem universalLeftCutoff_exists (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) (φ : GlobalTests 𝕜 d) :
    ∃ χ : ProductTests ℝ d, UniversalLeftCutoff v φ χ := by
  have hp := compact_support_suffices d Set.univ (distributionSupport v)
    isClosed_univ (support_closed 𝕜 d v) (Or.inr hv)
  exact compact_product_cutoff _ (hp _ φ.hasCompactSupport)

private theorem UniversalLeftCutoff.admissible {v : GlobalDistribution 𝕜 d}
    {φ : GlobalTests 𝕜 d} {χ : ProductTests ℝ d} (hχ : UniversalLeftCutoff v φ χ)
    (u : GlobalDistribution 𝕜 d) : AdmissibleConvolutionCutoff u v φ χ := by
  obtain ⟨V, hV, hslice, hone⟩ := hχ
  refine ⟨V, hV, ?_, hone⟩
  intro p hp
  exact hslice ⟨⟨Set.mem_univ _, hp.1.2⟩, hp.2⟩

/-- The usual convolution, with the right support compact. No restriction on
or chosen bound for the left support is imposed. -/
def compactConvolution (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) (u : GlobalDistribution 𝕜 d) :
    GlobalDistribution 𝕜 d :=
  convolution 𝕜 d u v (compact_distribution_suffices 𝕜 d u v (Or.inr hv))

theorem compactConvolution_spec (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) (u : GlobalDistribution 𝕜 d) :
    IsProperConvolution u v (compactConvolution v hv u) :=
  convolution_spec 𝕜 d u v (compact_distribution_suffices 𝕜 d u v (Or.inr hv))

private theorem compactConvolution_pairing (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) (u : GlobalDistribution 𝕜 d)
    (φ : GlobalTests 𝕜 d) (χ : ProductTests ℝ d) (hχ : UniversalLeftCutoff v φ χ) :
    compactConvolution v hv u φ = u (kernelActionTest v (cutoffAdditionTest χ φ)) :=
  (compactConvolution_spec v hv u).2.2 (iteratedTensor u v)
    (iteratedTensor_isTensorProduct u v) φ χ (hχ.admissible u)

/-- For a fixed compactly supported right factor, convolution is scalar-linear. -/
def compactConvolutionLM (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) :
    GlobalDistribution 𝕜 d →ₗ[𝕜] GlobalDistribution 𝕜 d where
  toFun := compactConvolution v hv
  map_add' u w := by
    ext φ
    obtain ⟨χ, hχ⟩ := universalLeftCutoff_exists v hv φ
    simp only [add_apply]
    rw [compactConvolution_pairing v hv (u+w) φ χ hχ,
      compactConvolution_pairing v hv u φ χ hχ,
      compactConvolution_pairing v hv w φ χ hχ]
    rfl
  map_smul' c u := by
    ext φ
    obtain ⟨χ, hχ⟩ := universalLeftCutoff_exists v hv φ
    simp only [smul_apply, RingHom.id_apply]
    rw [compactConvolution_pairing v hv (c • u) φ χ hχ,
      compactConvolution_pairing v hv u φ χ hχ]
    rfl

/-- Convolution commutes with every ordinary multi-index derivative. -/
theorem compactConvolution_derivative (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) (u : GlobalDistribution 𝕜 d)
    (α : Fin d →₀ ℕ) :
    compactConvolutionLM v hv
      (Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d ⊤ α u) =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d ⊤ α (compactConvolutionLM v hv u) := by
  apply convolution_uniqueness 𝕜 d _ v
  · exact compactConvolution_spec v hv _
  · exact (convolution_derivatives 𝕜 d u v (compactConvolution v hv u)
      (multiIndexWord α) (compactConvolution_spec v hv u)).1

/-- The entire constant-coefficient operator commutes with convolution. -/
theorem compactConvolution_operator (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) (u : GlobalDistribution 𝕜 d)
    (s : 𝕜) (P : Symbol 𝕜 d) :
    compactConvolutionLM v hv (operator s P u) =
      operator s P (compactConvolutionLM v hv u) := by
  classical
  simp only [operator, Finsupp.sum, map_sum, map_smul, compactConvolution_derivative]

/-- The Dirac distribution is the convolution unit. The proof uses the actual
tensor/cutoff construction and locality on supp v. -/
theorem compactConvolution_dirac (v : GlobalDistribution 𝕜 d)
    (hv : IsCompact (distributionSupport v)) :
    compactConvolutionLM v hv (diracZero 𝕜 d) = v := by
  ext φ
  obtain ⟨χ, V, hV, hslice, hχ⟩ := universalLeftCutoff_exists v hv φ
  rw [show compactConvolutionLM v hv (diracZero 𝕜 d) φ =
      compactConvolution v hv (diracZero 𝕜 d) φ from rfl,
    compactConvolution_pairing v hv (diracZero 𝕜 d) φ χ ⟨V, hV, hslice, hχ⟩,
    diracZero_apply, kernelActionTest_apply]
  let O : Set (Domain d) := (fun y => ((0 : Domain d), y)) ⁻¹' V ∪ (tsupport φ)ᶜ
  have hO : IsOpen O :=
    (hV.preimage (continuous_const.prodMk continuous_id)).union (isClosed_tsupport φ).isOpen_compl
  apply pairing_locality 𝕜 d ⊤ v (kernelSection (cutoffAdditionTest χ φ) 0) φ O hO
  · intro y hy
    by_cases h : y ∈ tsupport φ
    · exact Or.inl (hslice ⟨⟨Set.mem_univ _, hy⟩, by simpa using h⟩)
    · exact Or.inr h
  · intro y hy
    change χ (0,y) • φ (0+y) = φ y
    rcases hy with hy | hy
    · simp [hχ hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]

theorem compact_rhs : CompactRhs := by
  intro 𝕜 _ d s P E v hv hE
  refine ⟨compact_distribution_suffices 𝕜 d E v (Or.inr hv), ?_⟩
  change operator s P (compactConvolutionLM v hv E) = v
  rw [← compactConvolution_operator v hv E s P, hE, compactConvolution_dirac]

/-- Finite polynomial cancellation assembles continuous weighted quotient pieces. -/
theorem fundamental_from_reflected_translates (P : Symbol ℂ d) (hP : P ≠ 0)
    (E : Domain d → GlobalDistribution ℂ d)
    (hE : ∀ b, operator 1 P (E b) = operator 1
      (MvPolynomial.reflectedTranslate (MvPolynomial.map (starRingEnd ℂ) P)
        (fun i => 2 * b i)) (diracZero ℂ d)) :
    ∃ F : GlobalDistribution ℂ d, operator 1 P F = diracZero ℂ d := by
  classical
  let Q := MvPolynomial.map (starRingEnd ℂ) P
  obtain ⟨η, c, hc, hcancel⟩ := MvPolynomial.exists_reflected_translate_cancellation
    Q (MvPolynomial.map_conj_ne_zero P hP)
  let w : ℕ → ℤ := fun j => (-1 : ℤ) ^ (Q.totalDegree - j) * Q.totalDegree.choose j
  let b : ℕ → Domain d := fun j i => (j : ℝ) * η i
  let A : GlobalDistribution ℂ d :=
    ∑ j ∈ Finset.range (Q.totalDegree + 1), w j • E (b j)
  have hA : operator 1 P A = c • diracZero ℂ d := by
    change operatorLM 1 P A = _
    simp only [A, map_sum, map_zsmul, operatorLM]
    change (∑ j ∈ Finset.range (Q.totalDegree + 1), w j • operator 1 P (E (b j))) = _
    simp only [hE]
    have hb (j : ℕ) : (fun i => 2 * b j i) = (fun i => (2 * j : ℝ) * η i) := by
      funext i
      simp only [b]
      ring
    simp only [hb]
    have hlin := congrArg (operatorSymbolLM (1 : ℂ) (diracZero ℂ d)) hcancel
    simp only [map_sum, map_zsmul, operatorSymbolLM_apply, operator_C] at hlin
    exact hlin
  refine ⟨c⁻¹ • A, ?_⟩
  change operatorLM 1 P (c⁻¹ • A) = _
  rw [map_smul]
  change c⁻¹ • operator 1 P A = _
  rw [hA, smul_smul, inv_mul_cancel₀ hc, one_smul]


def toComplexHom : 𝕜 →+* ℂ where
  toFun a := (RCLike.re a : ℂ) + (RCLike.im a : ℂ) * Complex.I
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_mul' a b := by
    simp only [RCLike.mul_re, Complex.ofReal_sub, Complex.ofReal_mul,
      RCLike.mul_im, Complex.ofReal_add]
    ring_nf
    rw [Complex.I_sq]
    ring

@[simp] theorem fromComplex_toComplex (a : 𝕜) :
    RCLike.map ℂ 𝕜 (toComplexHom a) = a := by
  change (Complex.re ((RCLike.re a : ℂ) + (RCLike.im a : ℂ) * Complex.I) : 𝕜) +
    (Complex.im ((RCLike.re a : ℂ) + (RCLike.im a : ℂ) * Complex.I) : 𝕜) * RCLike.I = a
  simp

theorem fromComplex_mul_toComplex (a : 𝕜) (z : ℂ) :
    RCLike.map ℂ 𝕜 (toComplexHom a * z) = a * RCLike.map ℂ 𝕜 z := by
  obtain h | h := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · have ha : a = (RCLike.re a : 𝕜) := by simpa [h] using (RCLike.re_add_im a).symm
    change (Complex.re (toComplexHom a * z) : 𝕜) + (Complex.im (toComplexHom a * z) : 𝕜) * RCLike.I = _
    rw [show toComplexHom a = (RCLike.re a : ℂ) from by
      simp [toComplexHom, RCLike.im_eq_zero h]]
    change (Complex.re ((RCLike.re a : ℂ) * z) : 𝕜) +
      (Complex.im ((RCLike.re a : ℂ) * z) : 𝕜) * RCLike.I =
      a * ((Complex.re z : 𝕜) + (Complex.im z : 𝕜) * RCLike.I)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      h, mul_zero, add_zero]
    rw [ha]
    simp only [RCLike.ofReal_mul, RCLike.ofReal_re]
  · change (RCLike.complexRingEquiv h).symm ((RCLike.complexRingEquiv h) a * z) = _
    rw [map_mul, (RCLike.complexRingEquiv h).symm_apply_apply]
    rfl

def complexifyTests : GlobalTests 𝕜 d →L[ℝ] GlobalTests ℂ d :=
  TestFunction.postcompCLM (RCLike.map 𝕜 ℂ)

@[simp] theorem complexifyTests_apply (φ : GlobalTests 𝕜 d) (x : Domain d) :
    complexifyTests φ x = toComplexHom (φ x) := rfl

def restrictComplexDistribution (E : GlobalDistribution ℂ d) : GlobalDistribution 𝕜 d where
  toFun φ := RCLike.map ℂ 𝕜 (E (complexifyTests φ))
  map_add' φ ψ := by simp only [map_add]
  map_smul' a φ := by
    have htest : complexifyTests (a • φ) = toComplexHom a • complexifyTests φ := by
      ext x
      change toComplexHom (a * φ x) = toComplexHom a * toComplexHom (φ x)
      exact map_mul _ _ _
    rw [htest, E.map_smul]
    exact fromComplex_mul_toComplex a _
  cont := (RCLike.map ℂ 𝕜).continuous.comp
    (E.continuous.comp complexifyTests.continuous)

@[simp] theorem restrictComplexDistribution_apply (E : GlobalDistribution ℂ d)
    (φ : GlobalTests 𝕜 d) :
    restrictComplexDistribution E φ = RCLike.map ℂ 𝕜 (E (complexifyTests φ)) := rfl
theorem complexifyTests_partial_single (i : Fin d) (φ : GlobalTests 𝕜 d) :
    complexifyTests (TestFunction.lineDerivCLM 𝕜 (coordinateVector i) φ) =
      TestFunction.lineDerivCLM ℂ (coordinateVector i) (complexifyTests φ) := by
  ext x
  rw [complexifyTests_apply, TestFunction.lineDerivCLM_apply_of_le (by simp),
    TestFunction.lineDerivCLM_apply_of_le (by simp)]
  have hφ : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable (by simp)).differentiableAt
  rw [hφ.lineDeriv_eq_fderiv,
    ((complexifyTests φ).contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  change (RCLike.map 𝕜 ℂ) (fderiv ℝ φ x (coordinateVector i)) =
    fderiv ℝ ((RCLike.map 𝕜 ℂ) ∘ φ) x (coordinateVector i)
  rw [fderiv_comp _ (RCLike.map 𝕜 ℂ).differentiableAt hφ, (RCLike.map 𝕜 ℂ).fderiv]
  rfl

theorem complexifyTests_partial (w : List (Fin d)) (φ : GlobalTests 𝕜 d) :
    complexifyTests (testPartialCLM w φ) = testPartialCLM w (complexifyTests φ) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change complexifyTests (TestFunction.lineDerivCLM 𝕜 (coordinateVector i)
      (testPartialCLM w φ)) = _
    rw [complexifyTests_partial_single, ih]
    rfl
theorem toComplexHom_injective : Function.Injective (toComplexHom (𝕜 := 𝕜)) :=
  Function.LeftInverse.injective fromComplex_toComplex

theorem complexifyTests_smul (a : 𝕜) (φ : GlobalTests 𝕜 d) :
    complexifyTests (a • φ) = toComplexHom a • complexifyTests φ := by
  ext x
  change toComplexHom (a * φ x) = toComplexHom a * toComplexHom (φ x)
  exact map_mul _ _ _

theorem complexifyTests_operator (s : 𝕜) (P : Symbol 𝕜 d) (φ : GlobalTests 𝕜 d) :
    complexifyTests (testOperator s P φ) =
      testOperator (toComplexHom s) (MvPolynomial.map toComplexHom P) (complexifyTests φ) := by
  classical
  simp only [testOperator, Finsupp.sum, LinearMap.sum_apply, map_sum,
    LinearMap.smul_apply, complexifyTests_smul, map_mul, map_pow, map_neg,
    MvPolynomial.coeff_map, ContinuousLinearMap.coe_coe,
    complexifyTests_partial]
  change (∑ α ∈ P.support, _) = ∑ α ∈ (MvPolynomial.map toComplexHom P).support, _
  rw [MvPolynomial.support_map_of_injective P toComplexHom_injective]

/-- Scalar transport preserves the genuine weak PDE equation. -/
theorem restrictComplexDistribution_fundamental (s : 𝕜) (P : Symbol 𝕜 d)
    (E : GlobalDistribution ℂ d)
    (hE : operator (toComplexHom s) (MvPolynomial.map toComplexHom P) E = diracZero ℂ d) :
    operator s P (restrictComplexDistribution E) = diracZero 𝕜 d := by
  apply (pairing_criterion 𝕜 d s P _).2
  intro φ
  rw [restrictComplexDistribution_apply, complexifyTests_operator,
    (pairing_criterion ℂ d (toComplexHom s) (MvPolynomial.map toComplexHom P) E).1 hE]
  exact fromComplex_toComplex (φ 0)
/-- The full theorem over complex coefficients suffices for every RCLike field. -/
theorem fundamental_of_complex
    (hcomplex : ∀ (d : ℕ) (s : ℂ), s ≠ 0 → ∀ (P : Symbol ℂ d), P ≠ 0 →
      ∃ E : GlobalDistribution ℂ d, operator s P E = diracZero ℂ d) :
    Specs.ExpandedFA.Fourier.MalgrangeEhrenpreis.FundamentalSolution := by
  intro 𝕜 _ d s hs P hP
  have hs' : toComplexHom s ≠ 0 := by
    intro h
    exact hs (toComplexHom_injective (by simpa using h))
  have hP' : MvPolynomial.map toComplexHom P ≠ 0 := by
    intro h
    exact hP (MvPolynomial.map_injective toComplexHom toComplexHom_injective (by simpa using h))
  obtain ⟨E, hE⟩ := hcomplex d (toComplexHom s) hs' (MvPolynomial.map toComplexHom P) hP'
  exact ⟨restrictComplexDistribution E, restrictComplexDistribution_fundamental s P E hE⟩

/-- Every nonzero complex constant-coefficient operator has a continuous
fundamental solution, obtained as a finite sum of exponentially weighted
inverse Fourier transforms of bounded measurable quotients. -/
theorem complex_unit_fundamental (P : Symbol ℂ d) (hP : P ≠ 0) :
    ∃ E : GlobalDistribution ℂ d, operator 1 P E = diracZero ℂ d :=
  fundamental_from_reflected_translates P hP (exponentialQuotientDistribution P)
    (exponentialQuotientDistribution_operator P)

/-- Malgrange–Ehrenpreis, including every dimension, order zero, both scalar
fields, and every nonzero common derivative normalization. -/
theorem fundamental_solution : FundamentalSolution := by
  apply fundamental_of_complex
  intro d s hs P hP
  obtain ⟨E, hE⟩ := complex_unit_fundamental (rescaleSymbol s P)
    (rescaleSymbol_ne_zero s hs P hP)
  exact ⟨E, by simpa only [operator_rescaleSymbol] using hE⟩

end ExpandedFA.Fourier.MalgrangeEhrenpreis
