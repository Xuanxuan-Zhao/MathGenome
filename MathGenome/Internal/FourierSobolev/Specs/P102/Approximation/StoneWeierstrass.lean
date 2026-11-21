import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-!
Independent specifications for paper.tex, Theorem 1.11 (lines 475–508).
`Subalgebra 𝕜 C(K, 𝕜)` contains the image of `algebraMap`, hence every
constant function. The norm on continuous maps from compact `K` is the
uniform norm. No nonemptiness of `K` is assumed.
-/

universe u

namespace Specs.P102.Approximation

/-- Real Stone–Weierstrass, in closure and uniform approximation forms. -/
def RealStoneWeierstrass : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℝ C(K, ℝ)),
    A.SeparatesPoints →
      closure (A : Set C(K, ℝ)) = Set.univ ∧
      ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε →
        ∃ a ∈ A, ‖f - a‖ < ε

/-- Complex Stone–Weierstrass. On `C(K, ℂ)`, `star f` is the continuous
function `x ↦ conj (f x)`, so the second hypothesis is conjugation closure. -/
def ComplexStoneWeierstrass : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℂ C(K, ℂ)),
    A.SeparatesPoints →
    (∀ f ∈ A, star f ∈ A) →
      closure (A : Set C(K, ℂ)) = Set.univ ∧
      ∀ (f : C(K, ℂ)) (ε : ℝ), 0 < ε →
        ∃ a ∈ A, ‖f - a‖ < ε

end Specs.P102.Approximation
