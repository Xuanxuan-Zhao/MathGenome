import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Reflexive
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
Independent statements for `fa2:p1:c14:isomorphism-invariance`,
paper.tex:2754–2759. A continuous linear equivalence is a bounded linear
bijection with bounded inverse, with no isometry requirement. Reflexivity
means surjectivity of the canonical evaluation into the continuous
scalar-linear bidual over either real or complex scalars.
-/

namespace ExpandedFA.P1.C14IsomorphismInvariance.Spec

universe u v w

/-- Banach isomorphisms preserve the canonical reflexivity property. -/
def IsomorphismInvariance : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (T : E ≃L[𝕜] F),
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 F

/-- The canonical reflexivity predicate in precisely the norm p on the
original vector space. Definiteness supplies the metric, and the original
module action supplies scalar multiplication. -/
def ReflexiveForNorm (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [AddCommGroup E] [m : Module 𝕜 E]
    (p : Seminorm 𝕜 E) (hp : ∀ x, p x = 0 → x = 0) : Prop :=
  letI := C01Norm.normedGroup p hp
  letI : NormedSpace 𝕜 E :=
    { m with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }
  C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E

/-- Equivalent norms yield the same reflexivity property. This includes
all equivalent Banach norms; completeness is unnecessary for this result.
The arbitrary finite comparison constants allow non-isometric changes of norm
and include the zero vector space. -/
def EquivalentNormsInvariance : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    (p q : Seminorm 𝕜 E)
    (hp : ∀ x, p x = 0 → x = 0) (hq : ∀ x, q x = 0 → x = 0)
    (C D : ℝ),
    (∀ x, q x ≤ C * p x) → (∀ x, p x ≤ D * q x) →
    (ReflexiveForNorm 𝕜 E p hp ↔ ReflexiveForNorm 𝕜 E q hq)

end ExpandedFA.P1.C14IsomorphismInvariance.Spec
