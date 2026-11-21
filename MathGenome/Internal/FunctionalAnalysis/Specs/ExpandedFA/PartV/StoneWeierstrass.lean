import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Approximation.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
Independent statements for paper.tex, `fa2:p5:stone-weierstrass`.
The compact statements use precisely the earlier canonical `Subalgebra` objects.
For locally compact spaces `NonUnitalSubalgebra` imposes linear and multiplicative
closure without requiring constants. Point separation and nonvanishing are
stated explicitly. `star` on complex functions is pointwise conjugation.
The norm and topology on `C₀` are the supremum norm and uniform topology.
-/
namespace Specs.ExpandedFA.PartV.StoneWeierstrass

open scoped ZeroAtInfty
universe u

def RealDensity : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    (A : Subalgebra ℝ C(K, ℝ)), A.SeparatesPoints → Dense (A : Set C(K, ℝ))

def ComplexDensity : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    (A : Subalgebra ℂ C(K, ℂ)), A.SeparatesPoints →
    (∀ f ∈ A, star f ∈ A) → Dense (A : Set C(K, ℂ))

def RealUniformApproximation : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    (A : Subalgebra ℝ C(K, ℝ)), A.SeparatesPoints →
    ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε → ∃ g ∈ A, ‖g - f‖ < ε

def ComplexUniformApproximation : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    (A : Subalgebra ℂ C(K, ℂ)), A.SeparatesPoints →
    (∀ f ∈ A, star f ∈ A) →
    ∀ (f : C(K, ℂ)) (ε : ℝ), 0 < ε → ∃ g ∈ A, ‖g - f‖ < ε

def RealC0Density : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (A : NonUnitalSubalgebra ℝ C₀(X, ℝ)),
    (∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
    (∀ x : X, ∃ f ∈ A, f x ≠ 0) → Dense (A : Set C₀(X, ℝ))

def ComplexC0Density : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (A : NonUnitalSubalgebra ℂ C₀(X, ℂ)),
    (∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
    (∀ x : X, ∃ f ∈ A, f x ≠ 0) →
    (∀ f ∈ A, star f ∈ A) → Dense (A : Set C₀(X, ℂ))

def RealC0UniformApproximation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (A : NonUnitalSubalgebra ℝ C₀(X, ℝ)),
    (∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
    (∀ x : X, ∃ f ∈ A, f x ≠ 0) →
    ∀ (f : C₀(X, ℝ)) (ε : ℝ), 0 < ε → ∃ g ∈ A, ‖g - f‖ < ε

def ComplexC0UniformApproximation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (A : NonUnitalSubalgebra ℂ C₀(X, ℂ)),
    (∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
    (∀ x : X, ∃ f ∈ A, f x ≠ 0) → (∀ f ∈ A, star f ∈ A) →
    ∀ (f : C₀(X, ℂ)) (ε : ℝ), 0 < ε → ∃ g ∈ A, ‖g - f‖ < ε

end Specs.ExpandedFA.PartV.StoneWeierstrass
