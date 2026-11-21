import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Rolle
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Fermat
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ExtremeValues
import Mathlib.Topology.Order.Rolle

/-!
# Rolle's theorem

K03.05.rolle, paper.tex:807–814. Mathlib's topological Rolle theorem
uses attainment of the two extreme values on [a,b], including the constant
case. At the resulting interior extremum, the upstream Fermat theorem
makes the existing derivative zero. The relative formulation is transported
through the upstream continuity and interior derivative bridges.
-/

namespace SingleVariableAnalysis

open Set
open scoped Topology

theorem rolle_hasDerivAt (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) (he : f a = f b) :
    ∃ c ∈ Ioo a b, HasDerivAt f 0 c := by
  obtain ⟨c, hc, hextr⟩ := exists_isLocalExtr_Ioo hab hf he
  have hdc := (hd c hc).hasDerivAt
  have hz := fermat_hasDerivAt f c (deriv f c) hextr hdc
  exact ⟨c, hc, hz ▸ hdc⟩

theorem rolle_deriv (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) (he : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  obtain ⟨c, hc, hdc⟩ := rolle_hasDerivAt f a b hab hf hd he
  exact ⟨c, hc, hdc.deriv⟩

theorem rolle_within (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : RelativeContinuous f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∃ L : ℝ,
      HasRealIncrementDerivativeWithin f L (Icc a b) x) (he : f a = f b) :
    ∃ c ∈ Ioo a b, HasRealIncrementDerivativeWithin f 0 (Icc a b) c := by
  have hint : ∀ x ∈ Ioo a b, x ∈ interior (Icc a b) := by
    intro x hx
    simpa only [interior_Icc] using hx
  have hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := by
    intro x hx
    obtain ⟨L, hL⟩ := hd x hx
    exact ((withinDerivative_interior_iff f L (Icc a b) x (hint x hx)).mp hL).differentiableAt
  obtain ⟨c, hc, hdc⟩ := rolle_hasDerivAt f a b hab
    (relativeContinuous_continuousOn f (Icc a b) hf) hdiff he
  exact ⟨c, hc, (withinDerivative_interior_iff f 0 (Icc a b) c (hint c hc)).mpr hdc⟩

/-- Constancy is needed only on the closed interval, with arbitrary values outside. -/
theorem rolle_constant (f : ℝ → ℝ) (a b k : ℝ)
    (hf : ∀ x ∈ Icc a b, f x = k) (c : ℝ) (hc : c ∈ Ioo a b) :
    HasDerivAt f 0 c := by
  have heq : f =ᶠ[𝓝 c] (fun _ : ℝ => k) := by
    filter_upwards [Icc_mem_nhds hc.1 hc.2] with x hx
    exact hf x hx
  exact (hasDerivAt_const c k).congr_of_eventuallyEq heq

end SingleVariableAnalysis
