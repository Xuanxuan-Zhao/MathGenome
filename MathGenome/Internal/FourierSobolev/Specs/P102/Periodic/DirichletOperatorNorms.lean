import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! The real functional and its Lebesgue constant, with normalized Haar measure.
These statement types use no candidate implementation. -/
noncomputable section
open MeasureTheory Set

namespace P102.Periodic.Expected.DirichletOperatorNorms

/-- Construction and exact operator norm on the real continuous Banach space.
The complex equality also asserts that the Fourier sum is real. -/
def functionalStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (x : Circle T),
    ∃ Λ : ℕ → (C(Circle T, ℝ) →L[ℝ] ℝ),
      (∀ (N : ℕ) (f : C(Circle T, ℝ)),
        (Λ N f : ℂ) = partialSum T N (fun y => (f y : ℂ)) x) ∧
      (∀ N : ℕ, ‖Λ N‖ = ∫ y, ‖dirichletKernel T N y‖ ∂haar T)

/-- The Lebesgue constants are unbounded, for each positive period. -/
def kernelUnboundedStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)],
    ¬ BddAbove (Set.range (fun N : ℕ => ∫ y, ‖dirichletKernel T N y‖ ∂haar T))

/-- The same family has unbounded operator norms at every prescribed point. -/
def unboundedFunctionalStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (x : Circle T),
    ∃ Λ : ℕ → (C(Circle T, ℝ) →L[ℝ] ℝ),
      (∀ (N : ℕ) (f : C(Circle T, ℝ)),
        (Λ N f : ℂ) = partialSum T N (fun y => (f y : ℂ)) x) ∧
      (∀ N : ℕ, ‖Λ N‖ = ∫ y, ‖dirichletKernel T N y‖ ∂haar T) ∧
      ¬ BddAbove (Set.range (fun N : ℕ => ‖Λ N‖))

end P102.Periodic.Expected.DirichletOperatorNorms
