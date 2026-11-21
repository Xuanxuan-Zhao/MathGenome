import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator

/-! The bounded-operator clause of `fa2:p3:semigroup-perturbation`,
paper.tex 14843–14846. The relative dissipative clause is separately allocated.
The scalar field is real or complex; no separability or nontriviality is assumed.
The sum below has exactly the original domain, and generator equality is equality
of partial linear maps, hence includes both domain and values. -/

noncomputable section

namespace ExpandedFA.Semigroups.BoundedPerturbationSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A bounded perturbation is added on precisely D(A). -/
def boundedSum (A : Unbounded.Operator 𝕜 X X) (B : X →L[𝕜] X) :
    Unbounded.Operator 𝕜 X X :=
  { domain := A.domain
    toFun := A.toFun + B.toLinearMap.comp A.domain.subtype }

/-- Full original conclusion with the prescribed growth constants. -/
def Generation : Prop :=
  ∀ [CompleteSpace X] (A : Unbounded.Operator 𝕜 X X) (T : C0Semigroup 𝕜 X)
    (B : X →L[𝕜] X) (M ω : ℝ),
    C0SemigroupSpec.generatesValue A T →
    C0SemigroupSpec.exponentialBoundValue T M ω →
    ∃ S : C0Semigroup 𝕜 X,
      C0SemigroupSpec.generatesValue (boundedSum A B) S ∧
      C0SemigroupSpec.exponentialBoundValue S M (ω + M * ‖B‖)

def GenerationExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    Generation (𝕜 := 𝕜) (X := X)

end ExpandedFA.Semigroups.BoundedPerturbationSpec
