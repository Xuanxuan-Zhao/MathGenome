import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SeminormNullQuotient
import Mathlib.Topology.Algebra.Module.Basic

/-!
Independent statements for paper.tex lines 397–400. All quotients retain the
original algebraic cosets. The results hold for every subspace, hence in
particular for nonclosed subspaces. No completeness assumption is made.
-/

noncomputable section

namespace ExpandedFA.P1

namespace QuotientHausdorffization

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The null subspace of the original distance seminorm on `E/M`. -/
abbrev nullSpace (M : Submodule 𝕜 E) : Submodule 𝕜 (E ⧸ M) :=
  SeminormNullQuotient.nullSubspace
    (C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M)

/-- The algebraic quotient by that null space, with its native quotient seminorm.
This is the same algebraic space as the accepted seminorm null-space construction. -/
abbrev Space (M : Submodule 𝕜 E) :=
  SeminormNullQuotient.Space
    (C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M)

namespace Spec

/-- `closure(M)/M` means precisely the image of the closure under the original
coset map, as a linear subspace of the original algebraic quotient. -/
def NullSubspaceIdentification : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E),
    nullSpace M = M.topologicalClosure.map M.mkQ

/-- The native quotient norm is exactly the norm descending from the original
seminorm, including on the representative-based null quotient fixed in Chapter 1.
Definiteness is asserted on every element of the iterated algebraic quotient. -/
def HausdorffNorm : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E),
    (∀ z : E ⧸ M, ‖(nullSpace M).mkQ z‖ = ‖z‖) ∧
    (∀ w : Space M, ‖w‖ = SeminormNullQuotient.quotientValue
      (C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M) w) ∧
    C01Norm.NormAxioms 𝕜 (norm : Space M → ℝ)

/-- A surjective linear isometry to the quotient by the norm closure, explicitly
induced by the original map `x + M ↦ x + closure(M)`. -/
def HausdorffIsometry : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E),
    ∃ e : Space M ≃ₗᵢ[𝕜] E ⧸ M.topologicalClosure,
      ∀ x : E, e ((nullSpace M).mkQ (M.mkQ x)) = M.topologicalClosure.mkQ x

/-- A dense proper subspace has an algebraically nonzero quotient although its
distance seminorm vanishes on every coset. -/
def DenseProperQuotient : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), Dense (M : Set E) → M ≠ ⊤ →
    Nontrivial (E ⧸ M) ∧
      ∀ z : E ⧸ M, C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M z = 0

end Spec
end QuotientHausdorffization
end ExpandedFA.P1
