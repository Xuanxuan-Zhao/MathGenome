import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
Independent specification of Proposition `fa2:p1:c03:resolvent-identity`,
paper.tex lines 692–713. The maps carry their given norm topologies.
No completeness or nontriviality of a vector space is assumed.
-/

namespace ExpandedFA.P1.C03ResolventIdentity.Spec

universe u v w

/-- The inverse difference identity for arbitrary supplied bounded two-sided
inverses, including maps between different spaces. -/
def InverseDifference : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A B : E →L[𝕜] F) (Ai Bi : F →L[𝕜] E),
    Ai.comp A = ContinuousLinearMap.id 𝕜 E →
    A.comp Ai = ContinuousLinearMap.id 𝕜 F →
    Bi.comp B = ContinuousLinearMap.id 𝕜 E →
    B.comp Bi = ContinuousLinearMap.id 𝕜 F →
    Ai - Bi = (Ai.comp (B - A)).comp Bi

def ResolventType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (E →L[𝕜] E) → 𝕜 → (E →L[𝕜] E)

/-- A totalization of `(lam id - T)⁻¹`; identities below are restricted to
parameters at which a bounded two-sided inverse exists. -/
noncomputable def ResolventValue : ResolventType :=
  fun 𝕜 E _ _ _ T lam => Ring.inverse (lam • ContinuousLinearMap.id 𝕜 E - T)

/-- Being a unit of the native operator ring means exactly having a bounded
two-sided inverse, without invoking the Banach bounded inverse theorem. -/
def BoundedInverseIdentification : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →L[𝕜] E),
    IsUnit A ↔ ∃ S : E →L[𝕜] E,
      S.comp A = ContinuousLinearMap.id 𝕜 E ∧
      A.comp S = ContinuousLinearMap.id 𝕜 E

/-- The defined resolvent is indeed the bounded two-sided inverse. -/
def ResolventInverse : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (T : E →L[𝕜] E) (lam : 𝕜),
    IsUnit (lam • ContinuousLinearMap.id 𝕜 E - T) →
    (ResolventValue 𝕜 E T lam).comp (lam • ContinuousLinearMap.id 𝕜 E - T) =
        ContinuousLinearMap.id 𝕜 E ∧
      (lam • ContinuousLinearMap.id 𝕜 E - T).comp (ResolventValue 𝕜 E T lam) =
        ContinuousLinearMap.id 𝕜 E

/-- The sign and order match the manuscript, including `lam = mu`. -/
def ResolventIdentity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (T : E →L[𝕜] E) (lam mu : 𝕜),
    IsUnit (lam • ContinuousLinearMap.id 𝕜 E - T) →
    IsUnit (mu • ContinuousLinearMap.id 𝕜 E - T) →
    ResolventValue 𝕜 E T lam - ResolventValue 𝕜 E T mu =
      (mu - lam) • ((ResolventValue 𝕜 E T lam).comp (ResolventValue 𝕜 E T mu))

def ResolventCommute : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (T : E →L[𝕜] E) (lam mu : 𝕜),
    IsUnit (lam • ContinuousLinearMap.id 𝕜 E - T) →
    IsUnit (mu • ContinuousLinearMap.id 𝕜 E - T) →
    (ResolventValue 𝕜 E T lam).comp (ResolventValue 𝕜 E T mu) =
      (ResolventValue 𝕜 E T mu).comp (ResolventValue 𝕜 E T lam)

end ExpandedFA.P1.C03ResolventIdentity.Spec
