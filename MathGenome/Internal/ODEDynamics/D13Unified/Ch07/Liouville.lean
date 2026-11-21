import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.Liouville
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ScalarLinear
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch07.Liouville
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

/-- The determinant as a continuous multilinear function of its rows. -/
def detRows : ContinuousMultilinearMap 𝕂 (fun _ : Fin n => Fin n → 𝕂) 𝕂 where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

lemma detRows_apply (M : Matrix (Fin n) (Fin n) 𝕂) : detRows M = M.det := rfl

/-- Row multilinearity gives the determinant derivative without dividing by it. -/
lemma determinant_derivative {J : Set ℝ} {X : ℝ → Matrix (Fin n) (Fin n) 𝕂}
    {A : Matrix (Fin n) (Fin n) 𝕂} {t : ℝ}
    (hX : HasDerivWithinAt X (A * X t) J t) :
    HasDerivWithinAt (fun r => (X r).det) (A.trace * (X t).det) J t := by
  let d := (detRows (𝕂 := 𝕂) (n := n)).restrictScalars ℝ
  have hd := (d.hasFDerivAt (X t)).comp_hasDerivWithinAt t hX
  have hv : d.linearDeriv (X t) (A * X t) = A.trace * (X t).det := by
    change d.linearDeriv (fun i j => X t i j) (fun i j => (A * X t) i j) = _
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    change (∑ i, ((X t).updateRow i ((A * X t) i)).det) = _
    have hr (i : Fin n) : ((X t).updateRow i ((A * X t) i)).det =
        A i i * (X t).det := by
      have row : (A * X t) i = ∑ k, A i k • X t k := by
        funext j
        simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [row]
      exact Matrix.det_updateRow_sum (X t) i (A i)
    simp_rw [hr]
    rw [← Finset.sum_mul]
    rfl
  rw [hv] at hd
  change HasDerivWithinAt (fun r => (X r).det) (A.trace * (X t).det) J t at hd
  exact hd

/-- Liouville's identity holds even without the invertibility assumption. -/
theorem det_eq_exp_trace_integral (I : TimeInterval)
    (A X : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (ha : ContinuousOn A I.carrier) (hc : ContinuousOn X I.carrier)
    (hx : ∀ t ∈ I.carrier, HasDerivWithinAt X (A t * X t) I.carrier t)
    {s t : ℝ} (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    (X t).det = (X s).det * NormedSpace.exp (∫ r in s..t, (A r).trace) := by
  have ha' : ContinuousOn (fun r => (A r).trace) I.carrier := by
    exact continuous_id.matrix_trace.comp_continuousOn ha
  have hc' : ContinuousOn (fun r => (X r).det) I.carrier := by
    exact continuous_id.matrix_det.comp_continuousOn hc
  have hd : ScalarLinear.IsIVP I (fun r => (A r).trace) (fun _ => 0)
      s (X s).det (fun r => (X r).det) := by
    refine ⟨hc', hs, rfl, ?_⟩
    intro r hr
    simpa only [add_zero] using determinant_derivative (hx r hr)
  have he := ScalarLinear.eq_variation_of_isIVP I (fun r => (A r).trace)
    (fun _ => 0) s (X s).det ha' continuousOn_const hd ht
  simpa [ScalarLinear.variation, ScalarLinear.primitive, mul_comm] using he

/-- A real fundamental determinant has one nonzero sign throughout its interval. -/
theorem real_determinant_constant_sign (n : ℕ) (I : TimeInterval)
    (A X : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ha : ContinuousOn A I.carrier) (hx : EvolutionMatrix.IsFundamentalMatrixOn I A X) :
    (∀ t ∈ I.carrier, 0 < (X t).det) ∨ (∀ t ∈ I.carrier, (X t).det < 0) := by
  obtain ⟨s, hs⟩ := I.nonempty
  have hn : (X s).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (X s)).mp (hx.2.2 s hs)).ne_zero
  have hf (t : ℝ) (ht : t ∈ I.carrier) :=
    det_eq_exp_trace_integral I A X ha hx.1.continuousOn hx.2.1 hs ht
  have hp (t : ℝ) : 0 < NormedSpace.exp (∫ r in s..t, (A r).trace) := by
    rw [← Real.exp_eq_exp_ℝ]
    exact Real.exp_pos _
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · right
    intro t ht
    rw [hf t ht]
    exact mul_neg_of_neg_of_pos hneg (hp t)
  · left
    intro t ht
    rw [hf t ht]
    exact mul_pos hpos (hp t)

/-- Liouville's formula on the original real time interval, for either scalar field. -/
theorem formula : Specs.D13Unified.Ch07.Liouville.Formula := by
  intro 𝕂 _ n I A X ha hx s hs t ht
  exact det_eq_exp_trace_integral I A X ha hx.1.continuousOn hx.2.1 hs ht

/-- A real fundamental determinant keeps one strict sign on the entire interval. -/
theorem real_constant_sign : Specs.D13Unified.Ch07.Liouville.RealConstantSign :=
  real_determinant_constant_sign

end D13Unified.Ch07.Liouville
