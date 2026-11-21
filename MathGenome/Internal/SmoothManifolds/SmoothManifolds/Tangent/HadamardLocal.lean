import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.HadamardLocal
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Models
import MathGenome.Internal.MultivariableAnalysis.D04.C05.MorseCoefficients
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace SmoothManifolds

namespace Hadamard

/-- Integration of a continuous function on the compact unit interval is a
bounded linear functional for the supremum norm. -/
def intervalIntegralCLM : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in (0 : ℝ)..1, IccExtend zero_le_one f t
      map_add' := by
        intro f g
        change (∫ t in (0 : ℝ)..1,
          (IccExtend zero_le_one f t + IccExtend zero_le_one g t)) = _
        exact intervalIntegral.integral_add
          (f.continuous.Icc_extend'.intervalIntegrable 0 1)
          (g.continuous.Icc_extend'.intervalIntegrable 0 1)
      map_smul' := by
        intro c f
        change (∫ t in (0 : ℝ)..1, c • IccExtend zero_le_one f t) = _
        exact intervalIntegral.integral_smul c _ }
    1 (by
      intro f
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (f := IccExtend zero_le_one f)
        (fun t _ => f.norm_coe_le_norm _))

theorem intervalIntegralCLM_mkD (v : ℝ → ℝ)
    (hv : ContinuousOn v (Icc (0 : ℝ) 1)) :
    intervalIntegralCLM (ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => v t) 0) =
      ∫ t in (0 : ℝ)..1, v t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
  rw [IccExtend_of_mem zero_le_one _ ht']
  exact ContinuousMap.mkD_apply_of_continuous hv.domRestrict

/-- A jointly smooth integrand on an open neighborhood of V × [0,1] has a
smooth integral on V. The compact-family theorem is applied at every finite
order, so no analytic regularity is assumed. -/
theorem contDiffOn_integral {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (W : Set (X × ℝ)) (hW : IsOpen W) (f : X × ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W) (V : Set X) (hV : IsOpen V)
    (hVW : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, (x,t) ∈ W) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∫ t in (0 : ℝ)..1, f (x,t)) V := by
  apply contDiffOn_infty.mpr
  intro r
  have h := intervalIntegralCLM.contDiff.comp_contDiffOn
    (D04.MorseParameter.contDiffOn_curry r W hW f
      (hf.of_le (by simp)) V hV hVW)
  apply h.congr
  intro x hx
  exact (intervalIntegralCLM_mkD _
    (hf.continuousOn.comp (by fun_prop) (fun t ht => hVW x hx t ht))).symm

end Hadamard

/-- Local smooth Hadamard factorization on an arbitrary open Euclidean domain.
The proof also covers `n = 0`, where the coordinate sum is empty. -/
theorem smooth_hadamard_local (n : ℕ) (U : Set (Euclidean n))
    (a : Euclidean n) (F : Euclidean n → ℝ)
    (hU : IsOpen U) (ha : a ∈ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    ∃ V : Set (Euclidean n), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∃ g : Fin n → Euclidean n → ℝ,
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (g i) V) ∧
        (∀ x ∈ V, F x - F a = ∑ i, (x i - a i) * g i x) ∧
        (∀ i, g i a = fderiv ℝ F a (Pi.single i 1)) := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let V := Metric.ball a r
  have haV : a ∈ V := Metric.mem_ball_self hr
  let S : Euclidean n × ℝ → Euclidean n := fun p => a + p.2 • (p.1 - a)
  have hS : ContDiff ℝ (⊤ : ℕ∞) S := by dsimp [S]; fun_prop
  let W := S ⁻¹' U
  have hW : IsOpen W := hU.preimage hS.continuous
  have hVW (x : Euclidean n) (hx : x ∈ V) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (x,t) ∈ W := by
    apply hrU
    exact (convex_ball a r).add_smul_mem haV (by simpa [V] using hx) ht
  have hDF : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  let K : Fin n → Euclidean n × ℝ → ℝ :=
    fun i p => fderiv ℝ F (S p) (Pi.single i 1)
  have hK (i : Fin n) : ContDiffOn ℝ (⊤ : ℕ∞) (K i) W :=
    (hDF.clm_apply contDiffOn_const).comp hS.contDiffOn (fun _ hp => hp)
  let g : Fin n → Euclidean n → ℝ :=
    fun i x => ∫ t in (0 : ℝ)..1, K i (x,t)
  have hC (x : Euclidean n) (hx : x ∈ V) (i : Fin n) :
      ContinuousOn (fun t => K i (x,t)) (Icc (0 : ℝ) 1) :=
    (hK i).continuousOn.comp (by fun_prop) (fun t ht => hVW x hx t ht)
  refine ⟨V, Metric.isOpen_ball, haV, hrU, g, ?_, ?_, ?_⟩
  · intro i
    exact Hadamard.contDiffOn_integral W hW (K i) (hK i) V Metric.isOpen_ball hVW
  · intro x hx
    have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : S (x,t) ∈ U := hVW x hx t ht
    have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun t => F (S (x,t))) (fderiv ℝ F (S (x,t)) (x-a)) t := by
      have hf := ((hF.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt
        (by simp)).hasFDerivAt
      convert hf.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const (x-a)).const_add a) using 1 <;> simp [S, Function.comp_def]
    have hdc : ContinuousOn (fun t => fderiv ℝ F (S (x,t)) (x-a))
        (Icc (0 : ℝ) 1) :=
      (hDF.continuousOn.clm_apply continuousOn_const).comp
        (by dsimp [S]; fun_prop) hseg
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (fun t ht => hd t (by simpa [uIcc_of_le zero_le_one] using ht))
      (hdc.intervalIntegrable_of_Icc zero_le_one)
    have hsplit (t : ℝ) : fderiv ℝ F (S (x,t)) (x-a) =
        ∑ i, (x i - a i) * K i (x,t) := by
      conv_lhs => arg 2; rw [pi_eq_sum_univ' (x-a)]
      simp only [map_sum, map_smul, Pi.sub_apply, smul_eq_mul, K]
    calc
      F x - F a = ∫ t in (0 : ℝ)..1, fderiv ℝ F (S (x,t)) (x-a) := by
        simpa [S] using hFTC.symm
      _ = ∫ t in (0 : ℝ)..1, ∑ i, (x i - a i) * K i (x,t) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hsplit t
      _ = ∑ i, ∫ t in (0 : ℝ)..1, (x i - a i) * K i (x,t) := by
        apply intervalIntegral.integral_finsetSum
        intro i _
        exact ((hC x hx i).intervalIntegrable_of_Icc zero_le_one).const_mul _
      _ = ∑ i, (x i - a i) * g i x := by
        simp only [g, intervalIntegral.integral_const_mul]
  · intro i
    simp [g, K, S]

end SmoothManifolds
