import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Gronwall
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraResolvent
import Mathlib.Analysis.ODE.Gronwall

/-! Pointwise order comparison for continuous Volterra operators. Positivity
of each term of the convergent inverse series yields positivity of the inverse;
its left inverse identity then compares subsolutions and supersolutions.
The scalar exponential estimate uses the differentiable integral majorant.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV

section Ordered
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]
  {a b : ℝ} (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[ℝ] E))
  (hk : ∀ p x, 0 ≤ x → 0 ≤ k p x)

include hk in
lemma volterra_nonnegative (f : C(VolterraInterval a b, E)) (hf : 0 ≤ f) :
    0 ≤ VolterraOperatorSpec.OperatorValue ℝ E a b hab k f := by
  intro t
  change 0 ≤ VolterraOperatorSpec.OperatorValue ℝ E a b hab k f t
  rw [(volterra_operator_properties ℝ E a b hab k).1]
  unfold volterraIntegralValue
  rw [intervalIntegral.integral_of_le t.property.1]
  exact MeasureTheory.integral_nonneg (fun s => hk _ _ (hf _))

omit [CompleteSpace E] [IsOrderedModule ℝ E] [ClosedIciTopology E] in
/-- A linear map on continuous functions is monotone if it preserves the
pointwise nonnegative cone. No compatibility between order and norm is needed. -/
lemma monotone_of_nonnegative
    (A : C(VolterraInterval a b, E) →L[ℝ] C(VolterraInterval a b, E))
    (hA : ∀ f, 0 ≤ f → 0 ≤ A f) : Monotone A := by
  intro f g hfg t
  have hp : 0 ≤ A (g - f) t := hA (g - f) (fun s => sub_nonneg.mpr (hfg s)) t
  rw [map_sub] at hp
  exact sub_nonneg.mp hp

include hk in
lemma volterra_order_conclusions (lam : ℝ) (hlam : 0 ≤ lam) :
    GronwallSpec.OrderConclusions hab k lam := by
  let V := VolterraOperatorSpec.OperatorValue ℝ E a b hab k
  let S := Ring.inverse (1 - lam • V)
  have hV : ∀ f, 0 ≤ f → 0 ≤ V f := volterra_nonnegative hab k hk
  have hVm : Monotone V := monotone_of_nonnegative V hV
  have hpow : ∀ n (f : C(VolterraInterval a b, E)), 0 ≤ f → 0 ≤ (V ^ n) f := by
    intro n
    induction n with
    | zero => intro f hf; simpa using hf
    | succ n ih =>
      intro f hf
      rw [pow_succ', mul_apply_eq_comp]
      exact hV _ (ih f hf)
  have hS : ∀ f, 0 ≤ f → 0 ≤ S f := by
    intro f hf t
    have hs := (volterra_inverse_series ℝ E a b hab k lam).2.1
    have hs' := (hs.mapL (ContinuousLinearMap.apply ℝ _ f)).mapL
      (ContinuousMap.evalCLM ℝ t)
    apply ge_of_tendsto' hs'.tendsto_sum_nat
    intro N
    apply Finset.sum_nonneg
    intro n _
    change 0 ≤ lam ^ n • ((V ^ n) f t)
    exact smul_nonneg (pow_nonneg hlam _) (hpow n f hf t)
  have hSm : Monotone S := monotone_of_nonnegative S hS
  obtain ⟨S', _, _, _, hl, hr, _⟩ := volterra_resolvent ℝ E a b hab k lam
  have hSid : S = S' := (ring_inverse_eq_of_two_sided _ _ hl hr).2
  have hleft : ∀ u : C(VolterraInterval a b, E), S (u - lam • V u) = u := by
    intro u
    change (S * (1 - lam • V)) u = u
    rw [hSid, hr]
    rfl
  refine ⟨hV, hVm, ?_, hS, hSm, ?_, ?_⟩
  · intro f g u₀ v₀ hfg huv n
    induction n with
    | zero => exact huv
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      intro t
      exact add_le_add (hfg t) (smul_le_smul_of_nonneg_left (hVm ih t) hlam)
  · intro u f hu
    calc
      u = S (u - lam • V u) := (hleft u).symm
      _ ≤ S f := hSm hu
  · intro u f hu
    calc
      S f ≤ S (u - lam • V u) := hSm hu
      _ = u := hleft u
end Ordered

/-- Integral majorant proof, valid also when `a=0`, `M=0`, or `T=0`. -/
theorem gronwall : GronwallSpec.Gronwall := by
  intro T hT a M ha hM z hz hineq t
  let g : ℝ → ℝ := fun s => z (Set.projIcc 0 T hT s)
  have hg : Continuous g := z.continuous.comp continuous_projIcc
  have hg0 : ∀ s, 0 ≤ g s := fun s => hz _
  let F : ℝ → ℝ := fun s => a + M * ∫ r in 0..s, g r
  have hF' : ∀ s, HasDerivAt F (M * g s) s := by
    intro s
    exact ((intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_mul M).const_add a
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun s => (hF' s).continuousAt)
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hF.continuousOn
    (fun s _ => (hF' s).hasDerivWithinAt) (δ := a) (K := M) (ε := 0)
    (a := 0) (b := T)
  have hbound : ∀ s ∈ Ico 0 T, ‖M * g s‖ ≤ M * ‖F s‖ + 0 := by
    intro s hs
    have hzF : g s ≤ F s := by
      have hi := hineq ⟨s, hs.1, hs.2.le⟩
      simpa only [g, Set.projIcc_of_mem hT ⟨hs.1, hs.2.le⟩] using hi
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM (hg0 s)), add_zero]
    exact mul_le_mul_of_nonneg_left (hzF.trans (le_abs_self _)) hM
  have hinit : ‖F 0‖ ≤ a := by simp [F, abs_of_nonneg ha]
  have ht := hb hinit hbound (t : ℝ) t.property
  rw [gronwallBound_ε0, sub_zero] at ht
  exact (hineq t).trans ((le_abs_self (F t)).trans ht)

lemma scalarVolterraKernel_apply {a b : ℝ} (k : C(volterraTriangle a b, ℝ))
    (p : volterraTriangle a b) (x : ℝ) : scalarVolterraKernel k p x = k p * x := by
  rfl

lemma matrixVolterraKernel_apply {a b : ℝ} {n : ℕ}
    (k : Fin n → Fin n → C(volterraTriangle a b, ℝ))
    (p : volterraTriangle a b) (x : Fin n → ℝ) (i : Fin n) :
    matrixVolterraKernel k p x i = ∑ j, k i j p * x j := by
  classical
  simp [matrixVolterraKernel, matrixCoordinateOperator,
    Finset.sum_apply, Pi.single_apply, mul_ite]

theorem scalar_volterra_comparison : GronwallSpec.ScalarComparison := by
  intro a b hab k hk lam hlam
  apply volterra_order_conclusions hab (scalarVolterraKernel k) _ lam hlam
  intro p x hx
  exact mul_nonneg (hk p) hx

theorem system_volterra_comparison : GronwallSpec.SystemComparison := by
  intro a b hab n k hk lam hlam
  letI : IsOrderedModule ℝ (Fin n → ℝ) :=
    { smul_le_smul_of_nonneg_left := by
        intro c hc x y hxy i
        exact mul_le_mul_of_nonneg_left (hxy i) hc
      smul_le_smul_of_nonneg_right := by
        intro x hx c d hcd i
        exact mul_le_mul_of_nonneg_right hcd (hx i) }
  apply volterra_order_conclusions hab (matrixVolterraKernel k) _ lam hlam
  intro p x hx i
  rw [matrixVolterraKernel_apply]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hk i j p) (hx j))

theorem scalar_volterra_integral_formula : GronwallSpec.ScalarIntegralFormula := by
  intro a b hab k f t
  rw [(volterra_operator_properties ℝ ℝ a b hab (scalarVolterraKernel k)).1]
  rfl

theorem system_volterra_integral_formula : GronwallSpec.SystemIntegralFormula := by
  intro a b hab n k f t i
  rw [(volterra_operator_properties ℝ (Fin n → ℝ) a b hab (matrixVolterraKernel k)).1]
  unfold volterraIntegralValue
  have hi : IntervalIntegrable (volterraIntegrand hab (matrixVolterraKernel k) f t)
      volume a (t : ℝ) :=
    ((continuous_volterraIntegrand hab (matrixVolterraKernel k) f).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have he := (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hi
  change (∫ s in a..(t : ℝ), volterraIntegrand hab (matrixVolterraKernel k) f t s i) =
    (∫ s in a..(t : ℝ), volterraIntegrand hab (matrixVolterraKernel k) f t s) i at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro s _
  exact matrixVolterraKernel_apply k _ _ i

end ExpandedFA.PartV
