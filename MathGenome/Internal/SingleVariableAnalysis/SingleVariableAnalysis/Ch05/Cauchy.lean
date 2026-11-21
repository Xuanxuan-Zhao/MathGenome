import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Rolle
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.LinearRules
import Mathlib.Tactic.Ring

/-!
# Cauchy's real mean value theorem

K03.05.cauchy, paper.tex:824–839. Apply the upstream Rolle theorem to
H(t) = (f(b)-f(a))g(t) - (g(b)-g(a))f(t). Finite derivative linearity
computes H'. A second application of Rolle rules out equal endpoint
values of g when g' never vanishes. Only then divide to obtain the ratio.
-/

namespace SingleVariableAnalysis

open Set

theorem cauchy_mean_value (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x) :
    ∃ c ∈ Ioo a b,
      (f b - f a) * deriv g c = (g b - g a) * deriv f c := by
  let H : ℝ → ℝ := fun t => (f b - f a) * g t - (g b - g a) * f t
  have hH : ContinuousOn H (Icc a b) :=
    (continuousOn_const.mul hg).sub (continuousOn_const.mul hf)
  have hHd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt H ((f b - f a) * deriv g x - (g b - g a) * deriv f x) x :=
    ((hgd x hx).hasDerivAt.const_mul (f b - f a)).sub
      ((hfd x hx).hasDerivAt.const_mul (g b - g a))
  have he : H a = H b := by dsimp [H]; ring
  obtain ⟨c, hc, hzero⟩ := rolle_hasDerivAt H a b hab hH
    (fun x hx => (hHd x hx).differentiableAt) he
  exact ⟨c, hc, sub_eq_zero.mp ((hHd c hc).unique hzero)⟩

theorem cauchy_endpoint_ne (g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hg : ContinuousOn g (Icc a b))
    (hgd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (hn : ∀ x ∈ Ioo a b, deriv g x ≠ 0) : g b ≠ g a := by
  intro he
  obtain ⟨c, hc, hz⟩ := rolle_deriv g a b hab hg hgd he.symm
  exact hn c hc hz

theorem cauchy_mean_value_ratio (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (hn : ∀ x ∈ Ioo a b, deriv g x ≠ 0) :
    g b ≠ g a ∧ ∃ c ∈ Ioo a b, deriv g c ≠ 0 ∧
      (f b - f a) * deriv g c = (g b - g a) * deriv f c ∧
      (f b - f a) / (g b - g a) = deriv f c / deriv g c := by
  have hne := cauchy_endpoint_ne g a b hab hg hgd hn
  obtain ⟨c, hc, he⟩ := cauchy_mean_value f g a b hab hf hg hfd hgd
  refine ⟨hne, c, hc, hn c hc, he, ?_⟩
  apply (div_eq_div_iff (sub_ne_zero.mpr hne) (hn c hc)).mpr
  simpa only [mul_comm] using he

end SingleVariableAnalysis
