import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PositiveDefiniteContinuity
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The finite Gram form is only positive semidefinite: no quotient,
completeness, nonzero mass, or regularity is needed for its Cauchy–Schwarz
inequality. All algebraic estimates below hold on any abelian group. -/

noncomputable section
set_option autoImplicit false

namespace ExpandedFA.PartIV.PositiveDefiniteContinuity

open Complex
open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddCommGroup G] {φ : G → ℂ}

lemma value_zero (hφ : Spec.PositiveDefinite φ) :
    (φ 0).im = 0 ∧ 0 ≤ (φ 0).re := by
  simpa using hφ 1 (fun _ => 0) (fun _ => 1)

lemma conjugate_neg (hφ : Spec.PositiveDefinite φ) (x : G) :
    conj (φ (-x)) = φ x := by
  have h₀ := (value_zero hφ).1
  have h₁ := (hφ 2 ![0, x] ![1, 1]).1
  have hI := (hφ 2 ![0, x] ![1, I]).1
  simp [Fin.sum_univ_two] at h₁ hI
  apply Complex.ext <;> simp only [conj_re, conj_im]
  · linarith
  · linarith

/-- The finite Gram form; this does not identify distinct points or quotient null vectors. -/
def gramForm {n : ℕ} (φ : G → ℂ) (x : Fin n → G)
    (a b : Fin n → ℂ) : ℂ :=
  ∑ j, ∑ k, conj (a j) * b k * φ (x k - x j)

lemma gramForm_conj_symm {n : ℕ} (hφ : Spec.PositiveDefinite φ)
    (x : Fin n → G) (a b : Fin n → ℂ) :
    conj (gramForm φ x b a) = gramForm φ x a b := by
  simp only [gramForm, map_sum, map_mul, conj_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [show x j - x k = -(x k - x j) by abel, conjugate_neg hφ]
  ring

@[instance_reducible]
def gramCore {n : ℕ} (hφ : Spec.PositiveDefinite φ) (x : Fin n → G) :
    PreInnerProductSpace.Core ℂ (Fin n → ℂ) where
  inner := gramForm φ x
  conj_inner_symm := gramForm_conj_symm hφ x
  re_inner_nonneg a := (hφ n x a).2
  add_left a b c := by
    simp only [gramForm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  smul_left a b r := by
    simp only [gramForm, Pi.smul_apply, smul_eq_mul, map_mul]
    simp_rw [mul_assoc (conj r), ← Finset.mul_sum]

lemma gramForm_cauchy_schwarz {n : ℕ} (hφ : Spec.PositiveDefinite φ)
    (x : Fin n → G) (a b : Fin n → ℂ) :
    ‖gramForm φ x a b‖ ^ 2 ≤
      (gramForm φ x a a).re * (gramForm φ x b b).re := by
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ (Fin n → ℂ)
    _ _ _ (gramCore hφ x) a b
  change ‖gramForm φ x a b‖ * ‖gramForm φ x b a‖ ≤
    (gramForm φ x a a).re * (gramForm φ x b b).re at h
  rw [← norm_conj (gramForm φ x b a), gramForm_conj_symm hφ] at h
  simpa only [pow_two, InnerProductSpace.Core.toPreInner', gramCore] using h

lemma norm_le_value_zero (hφ : Spec.PositiveDefinite φ) (x : G) :
    ‖φ x‖ ≤ (φ 0).re := by
  have h := gramForm_cauchy_schwarz hφ ![0, x] ![1, 0] ![0, 1]
  simp [gramForm, Fin.sum_univ_two] at h
  exact (sq_le_sq₀ (norm_nonneg _) (value_zero hφ).2).mp (by simpa [pow_two] using h)

lemma increment_estimate (hφ : Spec.PositiveDefinite φ) (x h : G) :
    ‖φ (x + h) - φ x‖ ^ 2 ≤
      2 * (φ 0).re * ((φ 0).re - (φ h).re) := by
  have hc := gramForm_cauchy_schwarz hφ ![0, x, x + h] ![1, 0, 0] ![0, -1, 1]
  have hn : (φ (-h)).re = (φ h).re := by
    have := congrArg Complex.re (conjugate_neg hφ h)
    simpa using this
  simp [gramForm, Fin.sum_univ_three, add_sub_cancel_left,
    show x - (x + h) = -h by abel] at hc
  rw [hn] at hc
  convert hc using 1 <;> simp only [sub_eq_neg_add]
  ring

lemma eq_zero_of_value_zero (hφ : Spec.PositiveDefinite φ) (h₀ : φ 0 = 0) : φ = 0 := by
  funext x
  have := norm_le_value_zero hφ x
  simpa [h₀] using this

lemma uniformContinuous_of_continuousAt_zero
    {E : Type*} [SeminormedAddCommGroup E] {φ : E → ℂ}
    (hφ : Spec.PositiveDefinite φ) (hcont : ContinuousAt φ 0) :
    UniformContinuous φ := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have hM : 0 ≤ (φ 0).re := (value_zero hφ).2
  have hden : 0 < 2 * (φ 0).re + 1 := by linarith
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp hcont
    (ε ^ 2 / (2 * (φ 0).re + 1)) (div_pos (sq_pos_of_pos hε) hden)
  refine ⟨δ, hδ, ?_⟩
  intro a b hab
  have hs := hsmall (x := a - b) (by simpa [dist_eq_norm] using hab)
  have hre : (φ 0).re - (φ (a - b)).re ≤ dist (φ (a - b)) (φ 0) := by
    simpa [dist_eq_norm, norm_sub_rev] using Complex.re_le_norm (φ 0 - φ (a - b))
  have hmul := mul_le_mul_of_nonneg_left hre (show 0 ≤ 2 * (φ 0).re by positivity)
  have hb := increment_estimate hφ b (a - b)
  rw [show b + (a - b) = a by abel] at hb
  have hs' := (lt_div_iff₀ hden).mp hs
  have hdist := dist_nonneg (x := φ (a - b)) (y := φ 0)
  rw [dist_eq_norm]
  nlinarith [sq_nonneg (‖φ a - φ b‖ - ε)]

theorem estimates : Spec.Estimates := by
  intro d φ hφ
  exact ⟨(value_zero hφ).1, (value_zero hφ).2,
    norm_le_value_zero hφ, increment_estimate hφ⟩

theorem continuity : Spec.Continuity := by
  intro d φ hφ hcont
  exact uniformContinuous_of_continuousAt_zero hφ hcont

theorem zero_case : Spec.ZeroCase := by
  intro d φ hφ h₀
  exact eq_zero_of_value_zero hφ h₀

end ExpandedFA.PartIV.PositiveDefiniteContinuity
