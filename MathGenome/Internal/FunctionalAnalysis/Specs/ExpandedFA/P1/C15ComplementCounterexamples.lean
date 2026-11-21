import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Basis.Defs

/-! Independent statements for paper.tex 4082–4096. Natural index `n`
represents the manuscript's positive index `n+1`; `e 𝕜 0` is `e₁`.
The space is the shared scalar `ℓ²`, with its native norm and inner product.
Finite sequences enter through the shared canonical `c₀₀ → ℓ²` inclusion. -/

noncomputable section
open scoped ENNReal

universe u
namespace ExpandedFA.P1.C15ComplementCounterexamples

abbrev Space (𝕜 : Type u) [RCLike 𝕜] := C01SequenceSpaces.SequenceLp 𝕜 2

def e (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : Space 𝕜 := lp.single 2 n 1

def c00 (𝕜 : Type u) [RCLike 𝕜] : Submodule 𝕜 (Space 𝕜) :=
  (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 2).range

def firstLine (𝕜 : Type u) [RCLike 𝕜] : Submodule 𝕜 (Space 𝕜) :=
  Submodule.span 𝕜 {e 𝕜 0}

namespace Spec

def FiniteSupportIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : Space 𝕜),
    x ∈ c00 𝕜 ↔ (Function.support (fun n => x n)).Finite

def FiniteSupportObstruction : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Dense (c00 𝕜 : Set (Space 𝕜)) ∧ c00 𝕜 ≠ ⊤ ∧
      ¬ ∃ P : Space 𝕜 →L[𝕜] Space 𝕜, P.comp P = P ∧ P.range = c00 𝕜

/-- The explicit Hamel-basis construction and all its quantitative claims.
The original field may be either real or complex. -/
def UnboundedLineProjection : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ (B : Set (Space 𝕜)) (b : Module.Basis B 𝕜 (Space 𝕜))
      (f : Space 𝕜 →ₗ[𝕜] 𝕜) (P : Space 𝕜 →ₗ[𝕜] Space 𝕜),
      LinearIndependent 𝕜 (e 𝕜) ∧
      (∀ x : B, b x = (x : Space 𝕜)) ∧ Set.range (e 𝕜) ⊆ B ∧
      (∀ n, f (e 𝕜 n) = (n + 1 : ℕ)) ∧
      (∀ x ∈ B, x ∉ Set.range (e 𝕜) → f x = 0) ∧
      (∀ x, P x = f x • e 𝕜 0) ∧
      P.comp P = P ∧ P.range = firstLine 𝕜 ∧
      Module.finrank 𝕜 (firstLine 𝕜) = 1 ∧
      IsClosed (firstLine 𝕜 : Set (Space 𝕜)) ∧
      (∀ n, ‖e 𝕜 n‖ = 1 ∧ ‖P (e 𝕜 n)‖ = (n + 1 : ℕ)) ∧
      (¬ ∃ C : ℝ, ∀ x, ‖P x‖ ≤ C * ‖x‖) ∧ ¬ Continuous P

/-- The very same line also has its usual bounded orthogonal projection. -/
def BoundedOrthogonalProjection : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ Q : Space 𝕜 →L[𝕜] Space 𝕜,
      Q.comp Q = Q ∧ Q.range = firstLine 𝕜 ∧
      Q.ker = (firstLine 𝕜)ᗮ ∧ ‖Q‖ = 1 ∧
      ∀ x, Q x = x 0 • e 𝕜 0

end Spec
end ExpandedFA.P1.C15ComplementCounterexamples
