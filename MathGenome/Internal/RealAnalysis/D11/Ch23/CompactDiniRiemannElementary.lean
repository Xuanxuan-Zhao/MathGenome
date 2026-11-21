import MathGenome.Internal.RealAnalysis.D11.Ch23.ElementaryIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.CompactDiniRiemannElementary
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order

/-!
Compact Dini and the classical Riemann elementary integral (paper.tex:6314–6316).
All integral laws used here are calculus laws for the proper Darboux integral.
There is no measure representation or Riemann–Lebesgue bridge in this proof.
-/
universe u
open Filter Topology
open SingleVariableAnalysis SingleVariableAnalysis.Riemann

namespace D11.Ch23

abbrev continuousFunctions (X : Type u) [TopologicalSpace X] : Submodule ℝ (X → ℝ) :=
  Specs.continuousFunctions X

noncomputable abbrev riemannFunctional {a b : ℝ} (hab : a ≤ b) :
    continuousFunctions (Set.Icc a b) →ₗ[ℝ] ℝ := Specs.riemannFunctional hab

/-- Dini includes the empty compact Hausdorff space. -/
theorem compact_dini : Specs.CompactDini.{u} := by
  intro X _ _ _ f hcont _ hanti hlim
  exact Antitone.tendstoUniformly_of_forall_tendsto hcont
    (fun _ _ hmn x => hanti x hmn) continuous_const hlim

/-- Continuity is preserved by both lattice operations and truncation at one. -/
theorem continuousFunctions_stone : Specs.ContinuousFunctionsStone.{u} := by
  intro X _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro f hf g hg
    exact Continuous.min hf hg
  · intro f hf g hg
    exact Continuous.max hf hg
  · intro f hf
    exact Continuous.min hf continuous_const
  · exact continuous_const

/-- A direct Darboux estimate, valid also when the interval is a singleton. -/
theorem riemann_norm_bound : Specs.RiemannNormBound := by
  intro a b hab f
  obtain ⟨hn, htri, _⟩ := real_norm_estimate (Set.IccExtend hab f.val)
    (Specs.interval_continuous_integrable hab f)
  change |realIntegral _ (Specs.interval_continuous_integrable hab f)| ≤ _
  calc
    _ = ‖realIntegral _ (Specs.interval_continuous_integrable hab f)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ realIntegral _ hn := htri
    _ ≤ (b - a) * ‖Specs.asContinuousMap f‖ := by
      apply realIntegral_le_mul_bound hn
      intro x _
      exact ContinuousMap.norm_coe_le_norm (Specs.asContinuousMap f) (Set.projIcc a b hab x)

/-- Positivity follows from the order law for the Darboux integral. -/
theorem riemann_nonneg {a b : ℝ} (hab : a ≤ b)
    (f : continuousFunctions (Set.Icc a b)) (hf : ∀ x, 0 ≤ f.val x) :
    0 ≤ riemannFunctional hab f := by
  obtain ⟨hz, he⟩ := real_zero_value hab
  have hm := realIntegral_mono (fun _ => 0) (Set.IccExtend hab f.val)
    hz (Specs.interval_continuous_integrable hab f) (fun x _ => hf (Set.projIcc a b hab x))
  calc
    0 = realIntegral (fun _ => 0) hz := he.symm
    _ ≤ riemannFunctional hab f := hm

/-- Pointwise decrease to zero implies norm convergence on the compact interval,
and the calculus estimate then implies convergence of the integral values. -/
theorem riemann_elementary : Specs.RiemannElementary := by
  intro a b hab
  constructor
  · exact riemann_nonneg hab
  · intro f hanti hlim
    have hmaps : Tendsto (fun n => Specs.asContinuousMap (f n)) atTop
        (𝓝 (0 : C(Set.Icc a b, ℝ))) := by
      apply ContinuousMap.tendsto_of_antitone_of_pointwise
      · intro m n hmn x
        exact hanti x hmn
      · exact hlim
    have hn : Tendsto (fun n => ‖Specs.asContinuousMap (f n)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hmaps.norm
    have hb : Tendsto (fun n => (b - a) * ‖Specs.asContinuousMap (f n)‖) atTop (𝓝 0) := by
      simpa only [mul_zero] using hn.const_mul (b - a)
    apply squeeze_zero_norm _ hb
    intro n
    simpa only [Real.norm_eq_abs] using riemann_norm_bound hab (f n)

/-- On [a,a] the classical functional is exactly zero. -/
theorem riemann_degenerate : Specs.RiemannDegenerate := by
  intro a f
  exact realIntegral_degenerate _ a (Specs.interval_continuous_integrable (le_refl a) f)

end D11.Ch23
