import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm

/-! Independent formulation of paper.tex:2027–2034. Multiplication is an
arbitrary scalar-bilinear operation on the original Banach space. No norm
bound or joint continuity is assumed. -/

namespace ExpandedFA.P1.TopologicalAlgebraNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The new norm is definite, uniformly equivalent to the given norm, and
complete for its own induced metric. The seminorm bundle preserves the
original addition and scalar multiplication. -/
structure EquivalentCompleteNorm (p : Seminorm 𝕜 E) : Prop where
  definite : ∀ x, p x = 0 → x = 0
  bounds : ∃ c > 0, ∃ C > 0, ∀ x, c * ‖x‖ ≤ p x ∧ p x ≤ C * ‖x‖
  complete : @CompleteSpace E (C01Norm.normedGroup p definite).toUniformSpace

/-- Submultiplicativity concerns precisely the specified multiplication. -/
def AlgebraNorm (B : E →ₗ[𝕜] E →ₗ[𝕜] E) (p : Seminorm 𝕜 E) : Prop :=
  EquivalentCompleteNorm p ∧ ∀ x y, p (B x y) ≤ p x * p y

namespace Spec

/-- The unrestricted conclusion includes the zero algebra and needs no unit. -/
def SubmultiplicativeRenorming : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (B : E →ₗ[𝕜] E →ₗ[𝕜] E),
    (∀ x y z, B (B x y) z = B x (B y z)) →
    (∀ y, Continuous (fun x => B x y)) → (∀ x, Continuous (B x)) →
    ∃ p : Seminorm 𝕜 E, AlgebraNorm B p

/-- Only normalization of the identity requires a nonzero algebra. -/
def NormalizedUnitalRenorming : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [Nontrivial E] (B : E →ₗ[𝕜] E →ₗ[𝕜] E),
    (∀ x y z, B (B x y) z = B x (B y z)) →
    (∀ y, Continuous (fun x => B x y)) → (∀ x, Continuous (B x)) →
    ∀ e : E, (∀ x, B e x = x) → (∀ x, B x e = x) →
    ∃ p : Seminorm 𝕜 E, AlgebraNorm B p ∧ p e = 1

/-- On the zero space every identity is zero and every norm vanishes there;
the algebra still has an equivalent complete submultiplicative norm. -/
def ZeroAlgebraRenorming : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [Subsingleton E] (B : E →ₗ[𝕜] E →ₗ[𝕜] E)
    (e : E), (∀ x, B e x = x) → (∀ x, B x e = x) →
    e = 0 ∧ ∃ p : Seminorm 𝕜 E, AlgebraNorm B p ∧ p e = 0

end Spec
end ExpandedFA.P1.TopologicalAlgebraNorm
