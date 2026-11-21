import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Chain
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The chain rule for real increments

K03.04.chain, paper.tex:695–707. We use Mathlib's vector-valued chain
rule over ℝ, transported through the proved difference-quotient bridge.
In particular the complex target is a real normed space; the inner function
still has real values. The library rule has no nonvanishing-increment
hypothesis, so it includes repeated occurrences of f(a+h) = f(a).

For functions on I and J, interiority transports their domain derivatives to
ordinary derivatives of any ambient extensions. The retained mapping
hypothesis is redundant by continuity and f(a) ∈ interior J. The upstream
extension/congruence results make this representation independent of values
outside the domains.
-/
namespace SingleVariableAnalysis

open scoped Topology
universe u

theorem incrementDerivative_chain {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → ℝ) (g : ℝ → F) (f' a : ℝ) (g' : F)
    (hf : HasRealIncrementDerivative f f' a)
    (hg : HasRealIncrementDerivative g g' (f a)) :
    HasRealIncrementDerivative (g ∘ f) (f' • g') a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  exact ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hg).scomp a
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hf)

theorem withinDerivative_chain {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → ℝ) (g : ℝ → F) (I J : Set ℝ)
    (f' a : ℝ) (g' : F) (ha : a ∈ interior I) (hb : f a ∈ interior J)
    (_hmap : ∀ᶠ x in 𝓝 a, f x ∈ J)
    (hf : HasRealIncrementDerivativeWithin f f' I a)
    (hg : HasRealIncrementDerivativeWithin g g' J (f a)) :
    HasRealIncrementDerivativeWithin (g ∘ f) (f' • g') I a ∧
      HasDerivAt (g ∘ f) (f' • g') a := by
  have hc : HasDerivAt (g ∘ f) (f' • g') a :=
    ((withinDerivative_interior_iff g g' J (f a) hb).mp hg).scomp a
      ((withinDerivative_interior_iff f f' I a ha).mp hf)
  exact ⟨(withinDerivative_interior_iff _ _ I a ha).mpr hc, hc⟩

theorem real_chain (f g : ℝ → ℝ) (I J : Set ℝ) (f' g' a : ℝ)
    (ha : a ∈ interior I) (hb : f a ∈ interior J)
    (hmap : ∀ᶠ x in 𝓝 a, f x ∈ J)
    (hf : HasRealIncrementDerivativeWithin f f' I a)
    (hg : HasRealIncrementDerivativeWithin g g' J (f a)) :
    HasRealIncrementDerivativeWithin (g ∘ f) (g' * f') I a ∧
      deriv (g ∘ f) a = g' * f' := by
  obtain ⟨hw, hd⟩ := withinDerivative_chain f g I J f' a g' ha hb hmap hf hg
  simpa only [smul_eq_mul, mul_comm] using And.intro hw hd.deriv

theorem complex_chain (f : ℝ → ℝ) (g : ℝ → ℂ) (I J : Set ℝ)
    (f' a : ℝ) (g' : ℂ) (ha : a ∈ interior I) (hb : f a ∈ interior J)
    (hmap : ∀ᶠ x in 𝓝 a, f x ∈ J)
    (hf : HasRealIncrementDerivativeWithin f f' I a)
    (hg : HasRealIncrementDerivativeWithin g g' J (f a)) :
    HasRealIncrementDerivativeWithin (g ∘ f) (g' * (f' : ℂ)) I a ∧
      deriv (g ∘ f) a = g' * (f' : ℂ) := by
  obtain ⟨hw, hd⟩ := withinDerivative_chain f g I J f' a g' ha hb hmap hf hg
  simpa only [Complex.real_smul, mul_comm] using And.intro hw hd.deriv

end SingleVariableAnalysis
