import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Floquet
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.Translation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.MatrixLogarithm
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.ExponentialCalculus
import Mathlib.Tactic.NoncommRing

noncomputable section
open Set
open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch08.Floquet
open D13Unified.Ch07 D13Unified.Ch07.EvolutionMatrix
open D13Unified.Ch08.Monodromy
variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

lemma exp_mul_neg (B : Mat) (t : ℝ) : matrixExp B t * matrixExp B (-t) = 1 := by
  rw [← matrixExp_add_time, add_neg_cancel, matrixExp_zero]

lemma exp_neg_mul (B : Mat) (t : ℝ) : matrixExp B (-t) * matrixExp B t = 1 := by
  rw [← matrixExp_add_time, neg_add_cancel, matrixExp_zero]

lemma exp_isUnit (B : Mat) (t : ℝ) : IsUnit (matrixExp B t) :=
  ⟨⟨matrixExp B t, matrixExp B (-t), exp_mul_neg B t, exp_neg_mul B t⟩, rfl⟩

lemma exp_commutes (B : Mat) (t : ℝ) : B * matrixExp B t = matrixExp B t * B :=
  (matrixExp_hasDerivAt_left B t).unique (matrixExp_hasDerivAt_right B t)

lemma hasDerivAt_exp_neg (B : Mat) (t : ℝ) :
    HasDerivAt (fun r => matrixExp B (-r)) (-matrixExp B (-t) * B) t := by
  convert! (matrixExp_hasDerivAt_right B (-t)).scomp t ((hasDerivAt_id t).neg) using 1
  simp

lemma principal_contDiff (A : ℝ → Mat) (hA : Continuous A) :
    ContDiff ℝ 1 (principalMatrix A) := by
  exact contDiffOn_univ.mp (contDiffOn_U wholeTime A 0 (wholeTime_mem 0) hA.continuousOn)

lemma factor_derivative (A : ℝ → Mat) (hA : Continuous A) (B : Mat) (t : ℝ) :
    HasDerivAt (fun r => principalMatrix A r * matrixExp B (-r))
      (A t * (principalMatrix A t * matrixExp B (-t)) -
        (principalMatrix A t * matrixExp B (-t)) * B) t := by
  convert! (hasDerivAt_U A hA 0 t).mul (hasDerivAt_exp_neg B t) using 1
  dsimp [principalMatrix]
  noncomm_ring

lemma factor_periodic (A : ℝ → Mat) (T : ℝ) (hA : Continuous A)
    (hper : Function.Periodic A T) (B : Mat) (hB : matrixExp B T = monodromy A T) :
    Function.Periodic (fun t => principalMatrix A t * matrixExp B (-t)) T := by
  intro t
  dsimp only
  rw [principal_period A hA T hper t, ← hB]
  have ht : -(t + T) = -T + -t := by ring
  rw [ht, matrixExp_add_time]
  simp only [mul_assoc, ← mul_assoc (matrixExp B T), exp_mul_neg, one_mul]

/-- Matrix action as a continuous real bilinear map, including complex states. -/
def mulVecCLM : Mat →L[ℝ] (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.mulVecBilin ℝ ℝ))

lemma hasDerivWithinAt_mulVec {P : ℝ → Mat} {P' : Mat}
    {y : ℝ → Fin n → ℂ} {y' : Fin n → ℂ} {S : Set ℝ} {t : ℝ}
    (hP : HasDerivWithinAt P P' S t) (hy : HasDerivWithinAt y y' S t) :
    HasDerivWithinAt (fun r => P r *ᵥ y r) (P' *ᵥ y t + P t *ᵥ y') S t :=
  (mulVecCLM.hasFDerivAt.comp_hasDerivWithinAt t hP).clm_apply hy

lemma contDiffOn_mulVec {P : ℝ → Mat} {y : ℝ → Fin n → ℂ} {S : Set ℝ}
    (hP : ContDiffOn ℝ 1 P S) (hy : ContDiffOn ℝ 1 y S) :
    ContDiffOn ℝ 1 (fun r => P r *ᵥ y r) S :=
  (mulVecCLM.contDiff.comp_contDiffOn hP).clm_apply hy

/-- Differentiate the actual inverse and cancel on the correct sides. -/
lemma inverse_factor_derivative (A : ℝ → Mat) (B : Mat) (P : ℝ → Mat)
    (hu : ∀ t, IsUnit (P t))
    (hdP : ∀ t, HasDerivAt P (A t * P t - P t * B) t) (t : ℝ) :
    HasDerivAt (fun r => Ring.inverse (P r))
      (B * Ring.inverse (P t) - Ring.inverse (P t) * A t) t := by
  let u := (hu t).unit
  have hv : (u : Mat) = P t := (hu t).unit_spec
  have hvi : (↑(u⁻¹) : Mat) = Ring.inverse (P t) := by
    rw [← hv, Ring.inverse_unit]
  have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt t (hdP t)
  convert! hd using 1
  change B * Ring.inverse (P t) - Ring.inverse (P t) * A t =
    -((↑(u⁻¹) : Mat) * (A t * P t - P t * B) * (↑(u⁻¹) : Mat))
  rw [hvi]
  have hpq := Ring.mul_inverse_cancel (P t) (hu t)
  have hqp := Ring.inverse_mul_cancel (P t) (hu t)
  calc
    _ = (Ring.inverse (P t) * P t) * (B * Ring.inverse (P t)) -
        (Ring.inverse (P t) * A t) * (P t * Ring.inverse (P t)) := by rw [hpq, hqp]; simp
    _ = _ := by noncomm_ring

lemma inverse_factor_contDiff (P : ℝ → Mat) (hP : ContDiff ℝ 1 P)
    (hu : ∀ t, IsUnit (P t)) : ContDiff ℝ 1 (fun t => Ring.inverse (P t)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hi : ContDiffAt ℝ 1 Ring.inverse (P t) := by
    simpa only [(hu t).unit_spec] using (contDiffAt_ringInverse ℝ (hu t).unit (n := 1))
  exact hi.comp t hP.contDiffAt

/-- The inverse change proves the converse without assuming y differentiable.
Both directions hold on exactly the original interval, including endpoints. -/
lemma solution_change (A : ℝ → Mat) (B : Mat) (P : ℝ → Mat)
    (hP : ContDiff ℝ 1 P) (hu : ∀ t, IsUnit (P t))
    (hdP : ∀ t, HasDerivAt P (A t * P t - P t * B) t)
    (I : D13Unified.TimeInterval) (y : ℝ → Fin n → ℂ) :
    IsLinearSolutionOn I A (fun t => P t *ᵥ y t) ↔
      IsLinearSolutionOn I (fun _ => B) y := by
  let Q := fun t => Ring.inverse (P t)
  have hQP (t : ℝ) : Q t * P t = 1 := Ring.inverse_mul_cancel _ (hu t)
  have hQPv (t : ℝ) (v : Fin n → ℂ) : Q t *ᵥ (P t *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  constructor
  · rintro ⟨hx, hdx⟩
    have heq : (fun t => Q t *ᵥ (P t *ᵥ y t)) = y := by funext t; exact hQPv t _
    have hQ := inverse_factor_contDiff P hP hu
    refine ⟨?_, ?_⟩
    · rw [← heq]
      exact contDiffOn_mulVec hQ.contDiffOn hx
    · intro t ht
      have hd := hasDerivWithinAt_mulVec
        (inverse_factor_derivative A B P hu hdP t).hasDerivWithinAt (hdx t ht)
      change HasDerivWithinAt (fun r => Q r *ᵥ (P r *ᵥ y r))
        ((B * Q t - Q t * A t) *ᵥ (P t *ᵥ y t) +
          Q t *ᵥ (A t *ᵥ (P t *ᵥ y t))) I.carrier t at hd
      have hv : (B * Q t - Q t * A t) *ᵥ (P t *ᵥ y t) +
          Q t *ᵥ (A t *ᵥ (P t *ᵥ y t)) = B *ᵥ y t := by
        simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hQPv, sub_add_cancel]
      rw [heq, hv] at hd
      exact hd
  · rintro ⟨hy, hdy⟩
    refine ⟨contDiffOn_mulVec hP.contDiffOn hy, ?_⟩
    intro t ht
    have hd := hasDerivWithinAt_mulVec (hdP t).hasDerivWithinAt (hdy t ht)
    convert! hd using 1
    simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, sub_add_cancel]

/-- Floquet representation with the same factors for every conclusion. -/
theorem representation : Specs.D13Unified.Ch08.Floquet.Representation := by
  intro n A T hA hT hper
  obtain ⟨L, hL⟩ := matrix_exists_log (monodromy A T)
    ((principal_properties ℂ n A hA).2 T)
  let B : Matrix (Fin n) (Fin n) ℂ := T⁻¹ • L
  have hscale : T • B = L := by simp [B, smul_smul, ne_of_gt hT]
  have hB : matrixExp B T = monodromy A T := by
    simpa only [matrixExp, hscale, one_smul] using hL
  let P : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => principalMatrix A t * matrixExp B (-t)
  have hE : ContDiff ℝ 1 (matrixExp B) := (matrixExp_smooth B).of_le (by simp)
  have hP : ContDiff ℝ 1 P :=
    (principal_contDiff A hA).mul (hE.comp contDiff_neg)
  have hu : ∀ t, IsUnit (P t) := fun t =>
    ((principal_properties ℂ n A hA).2 t).mul (exp_isUnit B (-t))
  have hdP : ∀ t, HasDerivAt P (A t * P t - P t * B) t :=
    factor_derivative A hA B
  refine ⟨B, P, hP, hu, factor_periodic A T hA hper B hB, ?_, ?_, hdP, ?_⟩
  · change principalMatrix A 0 * matrixExp B (-0) = 1
    rw [neg_zero, matrixExp_zero, mul_one]
    exact (principal_properties ℂ n A hA).1
  · intro t
    change principalMatrix A t = (principalMatrix A t * matrixExp B (-t)) * matrixExp B t
    rw [mul_assoc, exp_neg_mul, mul_one]
  · exact solution_change A B P hP hu hdP

/-- The real system is included entrywise in ℂ; the factors are complex and
have the original period T. The evolution bridge identifies its principal matrix. -/
theorem real_representation : Specs.D13Unified.Ch08.Floquet.RealRepresentation := by
  intro n A T hA hT hper
  let C : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => complexify (A t)
  have hC : Continuous C := continuous_complexify.comp hA
  have hpC : Function.Periodic C T := by
    intro t
    dsimp [C]
    rw [hper t]
  obtain ⟨B, P, hP⟩ := representation n C T hC hT hpC
  refine ⟨B, P, ?_⟩
  have hX : (fun t => Specs.D13Unified.Ch08.Monodromy.complexifyValue
      (Specs.D13Unified.Ch08.Monodromy.principalMatrixValue A t)) =
      Specs.D13Unified.Ch08.Monodromy.principalMatrixValue C := by
    funext t
    exact (complexification_bridge n A hA t 0).symm
  rw [hX]
  exact hP

end D13Unified.Ch08.Floquet
