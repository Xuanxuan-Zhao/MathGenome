import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.PitchforkExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.Pitchfork

/-! The stable branches of μx-x³ and the loss of symmetry under a nonzero
constant perturbation (paper.tex, Chapter 16). -/
noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch16.PitchforkExample
open Specs.D13Unified.Ch16.PitchforkExample
open Specs.D13Unified.Ch16.SimplePersistence
open Specs.D13Unified.Ch12.StabilityDefinitions
open Specs.D13Unified.Ch01.AutonomousParameters
open Ch06.StateDerivative

theorem persistent_symmetry_branch : persistentSymmetryBranch := by
  intro μ
  constructor
  · intro x
    dsimp [normalField]
    ring
  · simp [normalField]

/-- The actual state derivative of the cubic, with μ held fixed. -/
lemma normalField_stateDerivative (μ p : ℝ) :
    stateDerivative normalField (μ,p) = μ - 3*p^2 := by
  have hc : ContDiff ℝ 1 normalField := by unfold normalField; fun_prop
  have hslice := SimplePersistence.state_derivative_slice normalField (μ,p)
    hc.differentiable_one.differentiableAt
  have hd : HasDerivAt (fun x : ℝ => normalField (μ,x)) (μ-3*p^2) p := by
    convert ((hasDerivAt_id p).const_mul μ).sub ((hasDerivAt_id p).pow 3) using 1 <;>
      first | rfl | norm_num
  exact hslice.unique hd

/-- An exponential estimate implies stability and real-time convergence of
nearby canonical flow trajectories. Forward completeness is retained. -/
lemma asymptotic_of_exponential (F : AutonomousODE ℝ)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (h0 : (0 : ℝ) ∈ F.domain) (heq : autonomousEvalValue F 0 = 0)
    (h : locallyExponentiallyStableValue F hF h0 heq) :
    locallyAsymptoticallyStableValue F hF h0 heq := by
  obtain ⟨C,α,δ,hC,hα,hδ,hbound⟩ := h
  constructor
  · intro ε hε
    refine ⟨min δ (ε/C), lt_min hδ (div_pos hε hC), ?_⟩
    intro x hx hsmall
    obtain ⟨hcomplete,hestimate⟩ := hbound x hx (hsmall.trans_le (min_le_left _ _))
    refine ⟨hcomplete, fun t ht => ?_⟩
    have hexp : Real.exp (-α*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hxε : C * ‖x‖ < ε := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp
        (hsmall.trans_le (min_le_right _ _))
    calc
      ‖flow F t x‖ ≤ C * Real.exp (-α*t) * ‖x‖ := hestimate t ht
      _ ≤ C * 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hC.le) (norm_nonneg x)
      _ < ε := by simpa using hxε
  · refine ⟨δ,hδ,?_⟩
    intro x hx hsmall
    obtain ⟨hcomplete,hestimate⟩ := hbound x hx hsmall
    refine ⟨hcomplete,?_⟩
    have hexp : Tendsto (fun t : ℝ => Real.exp (-α*t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hα))
    have hlim : Tendsto (fun t : ℝ => C * Real.exp (-α*t) * ‖x‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hexp).mul_const ‖x‖
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_ge_atTop 0 |>.mono fun t ht => hestimate t ht) hlim

/-- The elementary equation p²=μ gives the root and the negative derivative;
no smallness restriction on the positive parameter is introduced. -/
lemma attracting_of_square (μ p : ℝ) (hμ : 0 < μ) (hp : p^2 = μ) :
    AttractingEquilibrium μ p := by
  have heq : normalField (μ,p) = 0 := by
    change μ*p-p^3 = 0
    calc
      μ*p-p^3 = (μ-p^2)*p := by ring
      _ = 0 := by rw [hp]; ring
  have hc : ContDiffOn ℝ 1 normalField (univ : Set (ℝ × ℝ)) := by
    unfold normalField
    fun_prop
  obtain ⟨F,hdom,heval,hF,h0,hzero,hstable,_⟩ :=
    Pitchfork.scalar_stability_at SimplePersistence.scalar_flow_stability
      SimplePersistence.state_derivative_slice isOpen_univ hc (mem_univ _) heq
  have hexp := hstable (by rw [normalField_stateDerivative, hp]; linarith)
  refine ⟨heq,F,?_,?_,hF,h0,hzero,hexp,
    asymptotic_of_exponential F hF h0 hzero hexp⟩
  · simpa only [mem_univ, ofPred_true] using hdom
  · intro y
    exact heval y (by rw [hdom]; trivial)

theorem stable_branches : stableBranches := by
  intro μ hμ
  have hs : (Real.sqrt μ)^2 = μ := Real.sq_sqrt hμ.le
  exact ⟨attracting_of_square μ _ hμ hs,
    attracting_of_square μ _ hμ (by simpa using hs)⟩

theorem constant_perturbation : constantPerturbation := by
  intro ε hε μ
  refine ⟨?_,by simpa [normalField] using hε,?_⟩
  · intro ho
    have hz := ho 0
    simp only [normalField, mul_zero, zero_pow (by decide : 3 ≠ 0), sub_zero,
      zero_add, neg_zero] at hz
    exact hε (by linarith)
  · intro x
    rfl

end D13Unified.Ch16.PitchforkExample
