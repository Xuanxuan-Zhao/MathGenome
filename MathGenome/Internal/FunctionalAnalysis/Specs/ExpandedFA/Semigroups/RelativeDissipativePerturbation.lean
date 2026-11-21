import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LumerPhillips

/-! The Hilbert-space assertion of fa2:p3:semigroup-perturbation,
paper.tex 14847–14850. Partial linear maps carry their exact domains.
The relative-bound constants are arbitrary real numbers, as in the source. -/
noncomputable section
namespace ExpandedFA.Semigroups.RelativeDissipativePerturbationSpec

set_option linter.checkUnivs false

/-- A dissipative relatively A-bounded perturbation with relative bound < 1
preserves contraction generation, on exactly the original domain. -/
def PerturbationExpected : Prop :=
  ∀ {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A B : Unbounded.Operator 𝕜 H H),
    (∃ T : C0Semigroup 𝕜 H,
      C0SemigroupSpec.generatorValue T = A ∧ LumerPhillipsSpec.Contractive T) →
    LumerPhillipsSpec.Dissipative B →
    (hAB : A.domain ≤ B.domain) →
    ∀ a b : ℝ, a < 1 →
    (∀ x : A.domain, ‖B ⟨x, hAB x.2⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖) →
    (A + B).domain = A.domain ∧ (A + B).IsClosed ∧
      ∃ S : C0Semigroup 𝕜 H,
        C0SemigroupSpec.generatorValue S = A + B ∧ LumerPhillipsSpec.Contractive S

end ExpandedFA.Semigroups.RelativeDissipativePerturbationSpec
