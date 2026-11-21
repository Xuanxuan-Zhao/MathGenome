import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.Gronwall
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.PerturbationResidual
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory

namespace D13Unified.Ch05.PerturbationResidual

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating a bound on the difference of velocities controls the change
between any two times in the actual interval. -/
lemma norm_increment_le_integral [CompleteSpace E]
    {a b L δ p q : ℝ} {x y v w : ℝ → E}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hdx : ∀ r ∈ Icc a b, HasDerivWithinAt x (v r) (Icc a b) r)
    (hdy : ∀ r ∈ Icc a b, HasDerivWithinAt y (w r) (Icc a b) r)
    (hvw : ∀ r ∈ Icc a b, ‖v r - w r‖ ≤ L * ‖x r - y r‖ + δ)
    (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) (hpq : p ≤ q) :
    ‖(x q - y q) - (x p - y p)‖ ≤
      ∫ r in p..q, (L * ‖x r - y r‖ + δ) := by
  have hi := integral_eq_sub_on_interval ordConnected_Icc (hx.sub hy) (hv.sub hw)
    (fun r hr => (hdx r hr).sub (hdy r hr)) hp hq
  change (∫ r in p..q, v r - w r) = (x q - y q) - (x p - y p) at hi
  rw [← hi]
  apply intervalIntegral.norm_integral_le_of_norm_le hpq
  · exact Filter.Eventually.of_forall fun r hr => hvw r
      ⟨hp.1.trans hr.1.le, hr.2.trans hq.2⟩
  · exact ((continuousOn_const.mul (hx.sub hy).norm).add continuousOn_const |>.mono
      (by rw [uIcc_of_le hpq]; exact Icc_subset_Icc hp.1 hq.2)).intervalIntegrable

/-- Comparison for C¹ curves with specified continuous velocities. This
form isolates the calculus and keeps both orientations of time explicit. -/
theorem curve_comparison [CompleteSpace E]
    {a b s L δ : ℝ} {x y v w : ℝ → E}
    (hs : s ∈ Icc a b) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hdx : ∀ r ∈ Icc a b, HasDerivWithinAt x (v r) (Icc a b) r)
    (hdy : ∀ r ∈ Icc a b, HasDerivWithinAt y (w r) (Icc a b) r)
    (hvw : ∀ r ∈ Icc a b, ‖v r - w r‖ ≤ L * ‖x r - y r‖ + δ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖x t - y t‖ ≤ Real.exp (L * |t - s|) * ‖x s - y s‖ +
      δ * Gronwall.E L |t - s| := by
  have hu : ContinuousOn (fun r => ‖x r - y r‖) (Icc a b) := (hx.sub hy).norm
  by_cases hst : s ≤ t
  · have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hbound : ∀ r ∈ Icc s t, ‖x r - y r‖ ≤ ‖x s - y s‖ +
        ∫ q in s..r, (L * ‖x q - y q‖ + δ) := by
      intro r hr
      have hi := norm_increment_le_integral hx hy hv hw hdx hdy hvw hs (hsub hr) hr.1
      have hn := norm_sub_norm_le (x r - y r) (x s - y s)
      linarith
    have h := Gronwall.constant_forward s t ‖x s - y s‖ L δ
      (fun r => ‖x r - y r‖) hst (norm_nonneg _) hL hδ (hu.mono hsub)
      (fun _ _ => norm_nonneg _) hbound t ⟨hst, le_rfl⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst), mul_comm ‖x s - y s‖,
      Gronwall.E] using h
  · have hts : t ≤ s := le_of_not_ge hst
    have hsub : Icc t s ⊆ Icc a b := Icc_subset_Icc ht.1 hs.2
    have hbound : ∀ r ∈ Icc t s, ‖x r - y r‖ ≤ ‖x s - y s‖ +
        ∫ q in r..s, (L * ‖x q - y q‖ + δ) := by
      intro r hr
      have hi := norm_increment_le_integral hx hy hv hw hdx hdy hvw (hsub hr) hs hr.2
      rw [norm_sub_rev (x s - y s) (x r - y r)] at hi
      have hn := norm_sub_norm_le (x r - y r) (x s - y s)
      linarith
    have h := Gronwall.constant_backward t s ‖x s - y s‖ L δ
      (fun r => ‖x r - y r‖) hts (norm_nonneg _) hL hδ (hu.mono hsub)
      (fun _ _ => norm_nonneg _) hbound t ⟨le_rfl, hts⟩
    simpa only [mul_comm ‖x s - y s‖, Gronwall.E] using h

/-- Perturbation by a bounded residual; only the displayed difference of
field values along the two curves needs the coefficient L. -/
theorem residual : Specs.D13Unified.Ch05.PerturbationResidual.residualExpected := by
  intro E _ _ _ F a b s L δ x y v hx hs hL hδ hy hv hdy hgraph hLip hres t ht
  have hf : ContinuousOn (fun r => F.eval r (x r)) (Icc a b) :=
    F.continuousOn_eval.comp (continuousOn_id.prodMk hx.2.1) hx.2.2.1
  apply curve_comparison hs hL hδ hx.2.1 hy hf hv hx.2.2.2 hdy _ ht
  intro r hr
  calc
    ‖F.eval r (x r) - v r‖ ≤
        ‖F.eval r (x r) - F.eval r (y r)‖ + ‖F.eval r (y r) - v r‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L * ‖x r - y r‖ + δ :=
      add_le_add (hLip r hr) (by simpa only [norm_sub_rev] using hres r hr)

/-- The two-field case is the residual estimate with velocity g(t,y(t)). -/
theorem two_fields : Specs.D13Unified.Ch05.PerturbationResidual.twoFieldsExpected := by
  intro E _ _ _ F g S a b s L δ x y hx hs hL hδ hy hg hdy hgraph hS hLip hdiff
  apply residual F a b s L δ x y (fun r => g r (y r)) hx hs hL hδ hy hg hdy
    hgraph hLip
  intro r hr
  simpa only [norm_sub_rev] using hdiff (r, y r) (hS r hr)

end D13Unified.Ch05.PerturbationResidual
