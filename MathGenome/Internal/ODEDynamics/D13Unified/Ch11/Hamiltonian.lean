import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Hamiltonian
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.FirstIntegral
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.Jacobian

/-! Hamiltonian energy and volume on the actual partial flow domains. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace D13Unified.Ch11.Hamiltonian
open Specs.D13Unified.Ch11.Hamiltonian
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch11.Flow
open Ch06.StateDerivative

variable {m : ℕ} {Ω : Set (Phase m)} (hΩ : IsOpen Ω)
  {H : Phase m → ℝ} (hH : ContDiffOn ℝ 2 H Ω)

lemma equation_eval {x : Phase m} (hx : x ∈ Ω) :
    (equation Ω hΩ H hH).eval x = vectorField H x := by
  simp [AutonomousODE.eval, autonomousEvalValue, equation, hx]

lemma equation_eval_eventually {x : Phase m} (hx : x ∈ Ω) :
    (equation Ω hΩ H hH).eval =ᶠ[𝓝 x] vectorField H := by
  filter_upwards [hΩ.mem_nhds hx] with y hy
  exact equation_eval hΩ hH hy

lemma equation_contDiffOn :
    ContDiffOn ℝ 1 (equation Ω hΩ H hH).eval Ω := by
  exact (vectorField_contDiffOn hΩ hH).congr (fun x hx => equation_eval hΩ hH hx)

/-- Expand a linear functional in the standard coordinate basis. -/
lemma apply_eq_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  calc
    L v = L (∑ i, Pi.single i (v i)) := congrArg L (LinearMap.sum_single_apply (fun _ : Fin n => ℝ) v).symm
    _ = _ := ?_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [he, map_smul]
  rfl

/-- The two paired coordinate contributions cancel, also for an empty sum. -/
lemma energy_derivative (x : Phase m) :
    (fderiv ℝ H x) (vectorField H x) = 0 := by
  rw [apply_eq_sum, Fin.sum_univ_add]
  simp only [vectorField, Fin.addCases_left, Fin.addCases_right]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring

theorem energy : Energy := by
  intro m Ω hΩ H hH I x hx s hs t ht
  apply Ch11.FirstIntegral.conservation (equation Ω hΩ H hH)
    (equation_contDiffOn hΩ hH) H (hH.of_le (by norm_num)) _ I x hx s hs t ht
  intro y hy
  rw [show autonomousEvalValue (equation Ω hΩ H hH) y = vectorField H y from
    equation_eval hΩ hH hy]
  exact energy_derivative y

/-- The derivative of (H_p,-H_q), assembled from the second derivative of H. -/
def vectorFieldDerivative (H : Phase m → ℝ) (x : Phase m) : Phase m →L[ℝ] Phase m :=
  ContinuousLinearMap.pi <| Fin.addCases
    (fun i : Fin m => (ContinuousLinearMap.apply ℝ ℝ (Pi.single (Fin.natAdd m i) 1)).comp
      (fderiv ℝ (fderiv ℝ H) x))
    (fun i : Fin m => -((ContinuousLinearMap.apply ℝ ℝ (Pi.single (Fin.castAdd m i) 1)).comp
      (fderiv ℝ (fderiv ℝ H) x)))

include hΩ hH in
lemma hasFDerivAt_vectorField {x : Phase m} (hx : x ∈ Ω) :
    HasFDerivAt (vectorField H) (vectorFieldDerivative H x) x := by
  have hc : ContDiffOn ℝ 1 (fderiv ℝ H) Ω := hH.fderiv_of_isOpen hΩ (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) x) x :=
    ((hc.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)).hasFDerivAt
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [vectorField, vectorFieldDerivative, ContinuousLinearMap.pi_apply,
      Fin.addCases_left, Function.comp_def, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.apply_apply, Pi.neg_apply] using!
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single (Fin.natAdd m j) 1)).hasFDerivAt.comp x hd
  · simpa only [vectorField, vectorFieldDerivative, ContinuousLinearMap.pi_apply,
      Fin.addCases_right, Function.comp_def, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.apply_apply, Pi.neg_apply] using!
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single (Fin.castAdd m j) 1)).hasFDerivAt.comp x hd).neg

/-- Equality of mixed second derivatives makes the divergence vanish. -/
lemma divergence_eq_zero {x : Phase m} (hx : x ∈ Ω) :
    (LinearMap.toMatrix' (fderiv ℝ (equation Ω hΩ H hH).eval x).toLinearMap).trace = 0 := by
  rw [(equation_eval_eventually hΩ hH hx).fderiv_eq,
    (hasFDerivAt_vectorField hΩ hH hx).fderiv]
  have hsym := ((hH x hx).contDiffAt (hΩ.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix'_apply]
  rw [Fin.sum_univ_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  change (vectorFieldDerivative H x) (Pi.single (Fin.castAdd m i) 1) (Fin.castAdd m i) +
    (vectorFieldDerivative H x) (Pi.single (Fin.natAdd m i) 1) (Fin.natAdd m i) = 0
  simp only [vectorFieldDerivative, ContinuousLinearMap.pi_apply,
    Fin.addCases_left, Fin.addCases_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, neg_apply]
  rw [hsym]
  exact add_neg_cancel _

section MatrixBridge
open scoped Matrix.Norms.Operator

/-- Standard-coordinate representation of an operator, with the operator norm
on matrices used in the upstream Liouville theorem. -/
def operatorMatrix {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix' L.toLinearMap

def operatorMatrixCLM (n : ℕ) :
    ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ((LinearMap.toMatrix' : ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≃ₗ[ℝ]
      Matrix (Fin n) (Fin n) ℝ).toLinearMap.comp
    (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

lemma operatorMatrixCLM_apply {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    operatorMatrixCLM n L = operatorMatrix L := rfl

lemma operatorMatrix_comp {n : ℕ} (A B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    operatorMatrix (A.comp B) = operatorMatrix A * operatorMatrix B :=
  LinearMap.toMatrix'_comp _ _

/-- Liouville's formula applied to the actual state derivative on its whole
maximal interval. All times, including negative times, remain in that interval. -/
lemma det_flow_of_divergence_zero {n : ℕ} (F : AutonomousODE (Fin n → ℝ))
    (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (hdiv : ∀ z ∈ F.domain, (operatorMatrix (fderiv ℝ F.eval z)).trace = 0)
    {x : Fin n → ℝ} {t : ℝ} (hx : x ∈ timeDomainValue F t) :
    (fderiv ℝ (flow F t) x).det = 1 := by
  let I := flowInterval F x
  let Y (r : ℝ) := fderiv ℝ (flow F r) x
  let A (r : ℝ) := coefficient F x r
  have hX := flow_ivp F hF hx.1
  have hV := (maximal_domain_derivative F hF).2.2 x hx.1
  have hY : ContinuousOn Y I.carrier := by
    intro r hr
    exact (hV.2.1 r hr).continuousAt.continuousWithinAt
  have hA : ContinuousOn A I.carrier :=
    (hF.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp
      hX.1.1.continuousOn (fun r hr => hX.1.2.1 r hr)
  have hmat (r : ℝ) (hr : r ∈ I.carrier) :
      HasDerivWithinAt (fun v => operatorMatrix (Y v))
        (operatorMatrix (A r) * operatorMatrix (Y r)) I.carrier r := by
    have hd : HasDerivAt (fun v => operatorMatrix (Y v))
        (operatorMatrixCLM n ((A r).comp (Y r))) r :=
      (operatorMatrixCLM n).hasFDerivAt.comp_hasDerivAt r (hV.2.1 r hr)
    exact (hd.congr_deriv (operatorMatrix_comp _ _)).hasDerivWithinAt
  have hdet := Ch07.Liouville.det_eq_exp_trace_integral I.toTimeInterval
    (fun r => operatorMatrix (A r)) (fun r => operatorMatrix (Y r))
    ((operatorMatrixCLM n).continuous.comp_continuousOn hA)
    ((operatorMatrixCLM n).continuous.comp_continuousOn hY) hmat hX.2.1 hx.2
  have hz : (∫ r in (0 : ℝ)..t, (operatorMatrix (A r)).trace) = 0 := by
    apply intervalIntegral.integral_zero_ae
    refine Filter.Eventually.of_forall (fun r hr => ?_)
    apply hdiv _
    exact hX.1.2.1 r (I.ordConnected.uIcc_subset hX.2.1 hx.2 (Set.uIoc_subset_uIcc hr))
  rw [hz] at hdet
  have hi : operatorMatrix (Y 0) = 1 := by
    rw [show Y 0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) from hV.1]
    exact LinearMap.toMatrix'_id
  rw [hi] at hdet
  simpa only [operatorMatrix, LinearMap.det_toMatrix', Matrix.det_one,
    NormedSpace.exp_zero, mul_one] using hdet

end MatrixBridge

lemma jacobian_one {t : ℝ} {x : Phase m}
    (hx : x ∈ timeDomainValue (equation Ω hΩ H hH) t) :
    (fderiv ℝ (flow (equation Ω hΩ H hH) t) x).det = 1 := by
  apply det_flow_of_divergence_zero _ (equation_contDiffOn hΩ hH) _ hx
  intro z hz
  exact divergence_eq_zero hΩ hH hz

theorem time_maps : TimeMaps := by
  intro m Ω hΩ H hH t
  obtain ⟨ho, hor, hi, he⟩ := Ch11.Flow.time_diffeomorphism 1 le_rfl
    (equation Ω hΩ H hH) (equation_contDiffOn hΩ hH) t
  exact ⟨ho, hor, hi, he, fun x hx => jacobian_one hΩ hH hx⟩

/-- Change of variables needs injectivity only on the actual survival domain;
Lebesgue measure of the image is taken in the ambient target space. -/
theorem volume_preservation : Volume := by
  intro m Ω hΩ H hH t
  dsimp only [Volume]
  intro A hA hAm
  let F := equation Ω hΩ H hH
  have hF : ContDiffOn ℝ 1 F.eval F.domain := equation_contDiffOn hΩ hH
  have hd (x : Phase m) (hx : x ∈ A) :
      HasFDerivWithinAt (flow F t) (fderiv ℝ (flow F t) x) A x :=
    ((maximal_domain_derivative F hF).1 (t,x) (hA hx)).hasFDerivWithinAt
  have hinj : InjOn (flow F t) A := by
    intro x hx y hy he
    have h1 := (Ch11.Flow.reverse_flow F hF (hA hx)).2
    have h2 := (Ch11.Flow.reverse_flow F hF (hA hy)).2
    rw [he] at h1
    exact h1.symm.trans h2
  refine ⟨nullMeasurable_image_of_fderivWithin volume hAm hd hinj, ?_⟩
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hAm hd hinj]
  calc
    (∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ (flow F t) x).det|) = ∫⁻ _ in A, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun₀ hAm
      intro x hx
      have hj : (fderiv ℝ (flow F t) x).det = 1 := jacobian_one hΩ hH (hA hx)
      simp only [hj, abs_one, ENNReal.ofReal_one]
    _ = volume A := by simp

end D13Unified.Ch11.Hamiltonian
