import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Lagrange
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Rolle
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.LinearRules

/-!
# The real mean value theorem

K03.05.lagrange, paper.tex:815–823. Apply the upstream Rolle theorem to
`(b - a) * f t - (f b - f a) * t`. This is the manuscript's auxiliary
function multiplied by the nonzero interval length, up to a constant.
Its endpoint values agree; its zero derivative gives the mean value equality.
Only real-valued functions occur, and endpoint differentiability is unnecessary.
-/

namespace SingleVariableAnalysis

open Set
open scoped Topology

theorem lagrange_deriv (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a) := by
  let F : ℝ → ℝ := fun t => (b - a) * f t - (f b - f a) * t
  have hF : ContinuousOn F (Icc a b) :=
    (hf.const_mul (b - a)).sub (continuous_const.mul continuous_id).continuousOn
  have hF' (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt F ((b - a) * deriv f x - (f b - f a)) x := by
    simpa only [F, mul_one] using
      ((hd x hx).hasDerivAt.const_mul (b - a)).fun_sub
        ((hasDerivAt_id' x).const_mul (f b - f a))
  have he : F a = F b := by dsimp only [F]; ring
  obtain ⟨c, hc, hzero⟩ := rolle_hasDerivAt F a b hab hF
    (fun x hx => (hF' x hx).differentiableAt) he
  have hz : (b - a) * deriv f c - (f b - f a) = 0 :=
    (hF' c hc).unique hzero
  refine ⟨c, hc, ?_⟩
  calc
    f b - f a = (b - a) * deriv f c := (sub_eq_zero.mp hz).symm
    _ = deriv f c * (b - a) := mul_comm _ _

theorem lagrange_hasDerivAt (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Ioo a b, HasDerivAt f ((f b - f a) / (b - a)) c := by
  obtain ⟨c, hc, heq⟩ := lagrange_deriv f a b hab hf hd
  have hs : deriv f c = (f b - f a) / (b - a) :=
    (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr heq.symm
  exact ⟨c, hc, hs ▸ (hd c hc).hasDerivAt⟩

theorem lagrange_within (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : RelativeContinuous f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∃ L : ℝ,
      HasRealIncrementDerivativeWithin f L (Icc a b) x) :
    ∃ c ∈ Ioo a b, ∃ L : ℝ,
      HasRealIncrementDerivativeWithin f L (Icc a b) c ∧
      f b - f a = L * (b - a) := by
  have hint (x : ℝ) (hx : x ∈ Ioo a b) : x ∈ interior (Icc a b) := by
    simpa only [interior_Icc] using hx
  have hdiff (x : ℝ) (hx : x ∈ Ioo a b) : DifferentiableAt ℝ f x := by
    obtain ⟨L, hL⟩ := hd x hx
    exact ((withinDerivative_interior_iff f L (Icc a b) x (hint x hx)).mp hL).differentiableAt
  obtain ⟨c, hc, heq⟩ := lagrange_deriv f a b hab
    (relativeContinuous_continuousOn f (Icc a b) hf) hdiff
  exact ⟨c, hc, deriv f c,
    (withinDerivative_interior_iff f (deriv f c) (Icc a b) c (hint c hc)).mpr
      (hdiff c hc).hasDerivAt, heq⟩

end SingleVariableAnalysis
