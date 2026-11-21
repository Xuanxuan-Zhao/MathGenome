import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Basic

/-!
Independent statements of Stone--Weierstrass (paper.tex:6487--6493).

`Subalgebra` includes every scalar constant. `SeparatesPoints` means that
distinct points have distinct values under some member of the algebra.
On `C(K, ℂ)`, `star` is pointwise complex conjugation. The topology and norm
on continuous maps from compact `K` are the uniform topology and supremum norm.
No nonemptiness assumption is imposed on `K`.
-/

namespace Specs.ExpandedFA.Approximation.StoneWeierstrass

universe u

def RealDensity : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℝ C(K, ℝ)),
    A.SeparatesPoints → Dense (A : Set C(K, ℝ))

def ComplexDensity : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℂ C(K, ℂ)),
    A.SeparatesPoints →
    (∀ f ∈ A, star f ∈ A) → Dense (A : Set C(K, ℂ))

/-- The uniform approximation conclusion expressed directly in supremum norm. -/
def RealUniformApproximation : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℝ C(K, ℝ)),
    A.SeparatesPoints →
    ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε → ∃ g ∈ A, ‖g - f‖ < ε

def ComplexUniformApproximation : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℂ C(K, ℂ)),
    A.SeparatesPoints →
    (∀ f ∈ A, star f ∈ A) →
    ∀ (f : C(K, ℂ)) (ε : ℝ), 0 < ε → ∃ g ∈ A, ‖g - f‖ < ε

end Specs.ExpandedFA.Approximation.StoneWeierstrass
