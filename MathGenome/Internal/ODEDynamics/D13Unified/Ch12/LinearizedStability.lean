import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.LinearizedStability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.MatrixLyapunov
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.Lyapunov
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.LinearizedInstability
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch12.LinearizedStability
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch12.StabilityDefinitions
open Specs.D13Unified.Ch12.Lyapunov
open D13Unified.Ch12.LinearizedInstability
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Positive quadratic forms bound the square of any fixed finite-dimensional
norm, including in dimension zero. -/
lemma positive_bilinear_lower_bound (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ x : E, x ≠ 0 → 0 < B x x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : E, m * ‖x‖ ^ 2 ≤ B x x := by
  have hc : Continuous (fun x => B x x) := B.isBoundedBilinearMap.continuous.comp (continuous_id.prodMk continuous_id)
  obtain ⟨m, hm, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hc.continuousOn (a := 0) (by
      intro x hx
      apply hpos x
      intro hx0
      simp [hx0] at hx)
  refine ⟨m, hm, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y : E := ‖x‖⁻¹ • x
  have hy : y ∈ sphere (0 : E) 1 := by
    simp [y, norm_smul, hn]
  have hxy : x = ‖x‖ • y := by simp [y, smul_smul, hn]
  have hh := mul_le_mul_of_nonneg_left (hmin y hy) (sq_nonneg ‖x‖)
  calc
    m * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 * B y y := by linarith
    _ = B x x := by
      conv_rhs => rw [hxy]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring

/-- A strictly dissipative positive quadratic form for the linearization
remains dissipative for the actual field on a sufficiently small ball. -/
lemma stability_of_bilinear_decay (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (h0 : (0 : E) ∈ F.domain)
    (heq : F.eval 0 = 0) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ x : E, x ≠ 0 → 0 < B x x)
    (d : ℝ) (hd : 0 < d)
    (hdec : ∀ x : E, B x ((fderiv ℝ F.eval 0) x) +
      B ((fderiv ℝ F.eval 0) x) x ≤ -d * ‖x‖ ^ 2) :
    locallyExponentiallyStableValue F hF h0 heq := by
  let V : E → ℝ := fun x => B x x
  have hV : ContDiff ℝ 1 V :=
    B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
  obtain ⟨m, hm, hlow⟩ := positive_bilinear_lower_bound B hpos
  let C : ℝ := 2 * ‖B‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hupper (x : E) : V x ≤ C * ‖x‖ ^ 2 := by
    have h := B.le_opNorm₂ x x
    have hBC : ‖B‖ ≤ C := by dsimp [C]; nlinarith [norm_nonneg B]
    have h' : |V x| ≤ ‖B‖ * ‖x‖ * ‖x‖ := by simpa [V] using h
    nlinarith [le_abs_self (V x), mul_le_mul_of_nonneg_right hBC (sq_nonneg ‖x‖)]
  have hDV (x : E) : ‖fderiv ℝ V x‖ ≤ C * ‖x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC.le (norm_nonneg x))
    intro y
    rw [show V = (fun z => B z z) from rfl, bilinear_diagonal_fderiv]
    calc
      ‖B x y + B y x‖ ≤ ‖B x y‖ + ‖B y x‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖x‖ * ‖y‖ + ‖B‖ * ‖y‖ * ‖x‖ :=
        add_le_add (B.le_opNorm₂ x y) (B.le_opNorm₂ y x)
      _ ≤ (C * ‖x‖) * ‖y‖ := by
        dsimp [C]
        nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  let a : ℝ := d / (2 * C)
  have ha : 0 < a := div_pos hd (mul_pos (by norm_num) hC)
  have hac : C * a = d / 2 := by dsimp [a]; field_simp
  obtain ⟨r₁, hr₁, hrem⟩ := local_remainder_bound F hF h0 heq ha
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp F.isOpen_domain 0 h0
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hUΩ : ball (0 : E) r ⊆ F.domain := by
    intro x hx
    apply hball
    exact mem_ball.mpr ((mem_ball.mp hx).trans_le (min_le_right _ _))
  apply (Lyapunov.exponential_stability F hF h0 heq (ball 0 r) isOpen_ball
    (mem_ball_self hr) hUΩ V hV.contDiffOn m C (d/2) hm hC (half_pos hd)
    (fun x _ => ⟨hlow x, hupper x⟩) ?_).1
  intro x hx
  have hxr : ‖x‖ < r := by simpa using hx
  let A := fderiv ℝ F.eval 0
  have hb : ‖F.eval x - A x‖ ≤ a * ‖x‖ :=
    hrem x (hxr.trans_le (min_le_left _ _))
  have herr : |(fderiv ℝ V x) (F.eval x - A x)| ≤ (d / 2) * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖fderiv ℝ V x‖ * ‖F.eval x - A x‖ := by
        simpa only [Real.norm_eq_abs] using (fderiv ℝ V x).le_opNorm (F.eval x - A x)
      _ ≤ (C * ‖x‖) * (a * ‖x‖) :=
        mul_le_mul (hDV x) hb (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))
      _ = (d / 2) * ‖x‖ ^ 2 := by rw [mul_mul_mul_comm, hac, ← pow_two]
  have hlin : (fderiv ℝ V x) (A x) ≤ -d * ‖x‖ ^ 2 := by
    rw [show V = (fun z => B z z) from rfl, bilinear_diagonal_fderiv]
    exact hdec x
  have hadd : (fderiv ℝ V x) (F.eval x) = (fderiv ℝ V x) (A x) +
      (fderiv ℝ V x) (F.eval x - A x) := by rw [← map_add]; congr 1; abel
  change (fderiv ℝ V x) (F.eval x) ≤ _
  rw [hadd]
  have := le_abs_self ((fderiv ℝ V x) (F.eval x - A x))
  linarith

/-- A Hurwitz derivative yields a genuine positive quadratic Lyapunov
function in any real basis and for any fixed finite-dimensional norm. -/
theorem linearized_stability :
    Specs.D13Unified.Ch12.LinearizedStability.linearizedStabilityType.{u, v} := by
  intro E _ _ _ n _ _ basis F hF h0 heq hspec
  let A := fderiv ℝ F.eval 0
  let M := LinearMap.toMatrix basis basis A.toLinearMap
  let T : E ≃L[ℝ] (n → ℝ) := basis.equivFun.toContinuousLinearEquiv
  obtain ⟨P, hP, heP⟩ := (matrix_lyapunov_iff M).mp hspec 1 Matrix.PosDef.one
  let B : E →L[ℝ] E →L[ℝ] ℝ :=
    (Matrix.toBilin' P).toContinuousBilinearMap.bilinearComp T.toContinuousLinearMap
      T.toContinuousLinearMap
  let D : E →L[ℝ] E →L[ℝ] ℝ :=
    (Matrix.toBilin' (1 : Matrix n n ℝ)).toContinuousBilinearMap.bilinearComp
      T.toContinuousLinearMap T.toContinuousLinearMap
  have hB (x y : E) : B x y = T x ⬝ᵥ P.mulVec (T y) := Matrix.toBilin'_apply' _ _ _
  have hD (x y : E) : D x y = T x ⬝ᵥ T y := by
    change Matrix.toBilin' (1 : Matrix n n ℝ) (T x) (T y) = _
    simp only [Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hposB (x : E) (hx : x ≠ 0) : 0 < B x x := by
    rw [hB]
    exact hP.dotProduct_mulVec_pos (fun h => hx (T.injective (by simpa using h)))
  have hposD (x : E) (hx : x ≠ 0) : 0 < D x x := by
    have hh := (Matrix.PosDef.one : (1 : Matrix n n ℝ).PosDef).dotProduct_mulVec_pos
      (show T x ≠ 0 from fun h => hx (T.injective (by simpa using h)))
    simpa only [hD, Matrix.one_mulVec, star_trivial] using hh
  obtain ⟨d, hd, hlow⟩ := positive_bilinear_lower_bound D hposD
  have hsym : P.transpose = P := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian
  have hTA (x : E) : T (A x) = M.mulVec (T x) := by
    exact (A.toLinearMap.toMatrix_mulVec_repr basis basis x).symm
  have hlin (x : E) : B x (A x) + B (A x) x = -D x x := by
    rw [hB, hB, hD, symmetric_dotProduct P hsym (T (A x)) (T x), hTA]
    have hh := quadratic_lyapunovOperator M P hsym (T x)
    rw [heP] at hh
    simp only [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg] at hh
    linarith
  apply stability_of_bilinear_decay F hF h0 heq B hposB d hd
  intro x
  rw [hlin]
  linarith [hlow x]

/-- The positive-real-part implication retains the independent escape proof. -/
theorem linearized_instability :
    Specs.D13Unified.Ch12.LinearizedStability.linearizedInstabilityType.{u, v} :=
  D13Unified.Ch12.LinearizedInstability.linearized_instability

end D13Unified.Ch12.LinearizedStability
