import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Independent conventions interface for paper.tex 7364–7370, 7438–7457,
7552–7570, 7846–7869, and the realification convention at 8696–8707.
The ambient structures are native Mathlib structures. Completeness is used
only to guarantee projection onto every closed subspace. Forms and antiduals
already make sense on normed spaces; two different form domains are allowed.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Hilbert.Conventions.Spec
universe u v w

def ContinuousDualType := ExpandedFA.P1.C04Dual.Spec.ContinuousDualType.{u, v}
abbrev ContinuousDualValue : ContinuousDualType.{u, v} :=
  ExpandedFA.P1.C04Dual.Spec.ContinuousDualValue

def ContinuousAntidualType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H], Type (max u v)
abbrev ContinuousAntidualValue : ContinuousAntidualType.{u, v} :=
  fun 𝕜 H _ _ _ => H →L⋆[𝕜] 𝕜

/-- The first slot is conjugate linear, and the second slot is linear.
The norm is the native iterated operator norm, not a supplied certificate. -/
def BoundedSesquilinearFormType :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K], Type (max u v w)
abbrev BoundedSesquilinearFormValue : BoundedSesquilinearFormType.{u, v, w} :=
  fun 𝕜 H K _ _ _ _ _ => H →L⋆[𝕜] K →L[𝕜] 𝕜

def FormBoundType :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K],
    BoundedSesquilinearFormValue 𝕜 H K → ℝ → Prop
def FormBoundValue : FormBoundType.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ a C => 0 ≤ C ∧ ∀ x y, ‖a x y‖ ≤ C * ‖x‖ * ‖y‖

/-- Coercivity uses the real part and includes strict positivity of α. -/
def FormCoerciveType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H],
    BoundedSesquilinearFormValue 𝕜 H H → ℝ → Prop
def FormCoerciveValue : FormCoerciveType.{u, v} :=
  fun _ _ _ _ _ a α => 0 < α ∧ ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re (a x x)

def FormHermitianType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H],
    BoundedSesquilinearFormValue 𝕜 H H → Prop
def FormHermitianValue : FormHermitianType.{u, v} :=
  fun _ _ _ _ _ a => ∀ x y, a x y = conj (a y x)

def InnerFormType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H],
    BoundedSesquilinearFormValue 𝕜 H H
def InnerFormValue : InnerFormType.{u, v} := fun 𝕜 _ _ _ _ => innerSL 𝕜

/-- Arbitrary sets, including the empty set, have orthogonal complements. -/
def OrthogonalComplementType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], Set H → Submodule 𝕜 H
def OrthogonalComplementValue : OrthogonalComplementType.{u, v} :=
  fun 𝕜 _ _ _ _ A => (Submodule.span 𝕜 A).orthogonal

/-- The ambient-valued native orthogonal projector. The native existence
class includes complete subspaces of incomplete inner-product spaces. -/
def OrthogonalProjectionType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (M : Submodule 𝕜 H) [M.HasOrthogonalProjection], H →L[𝕜] H
def OrthogonalProjectionValue : OrthogonalProjectionType.{u, v} :=
  fun _ _ _ _ _ M _ => M.starProjection

/-- This is the native restriction of scalars on the SAME normed group H,
not a new space, norm, topology, or completeness structure. -/
def RealificationType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], InnerProductSpace ℝ H
abbrev RealificationValue : RealificationType.{u, v} :=
  fun 𝕜 H _ _ _ => InnerProductSpace.rclikeToReal 𝕜 H

/-- All convexity in the complex case is convexity for restricted real scalars. -/
def RealConvexType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], Set H → Prop
def RealConvexValue : RealConvexType.{u, v} :=
  fun 𝕜 H _ _ _ C => letI := RealificationValue 𝕜 H; Convex ℝ C

def InnerConvention : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (c : 𝕜) (x y : H),
    ⟪c • x, y⟫_𝕜 = conj c * ⟪x, y⟫_𝕜 ∧
    ⟪x, c • y⟫_𝕜 = c * ⟪x, y⟫_𝕜 ∧ conj ⟪y, x⟫_𝕜 = ⟪x, y⟫_𝕜

def AntidualIdentification : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] (f : H → 𝕜),
    (∃ F : ContinuousAntidualValue 𝕜 H, (F : H → 𝕜) = f) ↔
    Continuous f ∧ (∀ x y, f (x + y) = f x + f y) ∧
      (∀ (c : 𝕜) x, f (c • x) = conj c * f x)

def AntidualNormSupremum : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] (F : ContinuousAntidualValue 𝕜 H),
    ‖F‖ = sSup ((fun x => ‖F x‖) '' {x : H | ‖x‖ ≤ 1})

/-- An arbitrary function is represented iff it has exactly the four
sesquilinearity laws and a nonnegative global bound. -/
def BoundedFormIdentification : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (a : H → K → 𝕜),
    (∃ A : BoundedSesquilinearFormValue 𝕜 H K, ∀ x y, A x y = a x y) ↔
    (∀ x z y, a (x + z) y = a x y + a z y) ∧
    (∀ (c : 𝕜) x y, a (c • x) y = conj c * a x y) ∧
    (∀ x y z, a x (y + z) = a x y + a x z) ∧
    (∀ (c : 𝕜) x y, a x (c • y) = c * a x y) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖a x y‖ ≤ C * ‖x‖ * ‖y‖)

def FormNormLeastBound : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (a : BoundedSesquilinearFormValue 𝕜 H K),
    IsLeast {C : ℝ | FormBoundValue 𝕜 H K a C} ‖a‖

def FormNormInfimum : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (a : BoundedSesquilinearFormValue 𝕜 H K),
    ‖a‖ = sInf {C : ℝ | FormBoundValue 𝕜 H K a C}

def FormNormZeroSlots : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace 𝕜 H] [NormedSpace 𝕜 K] (a : BoundedSesquilinearFormValue 𝕜 H K),
    (Subsingleton H ∨ Subsingleton K) → ‖a‖ = 0

def RealConventions : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a : BoundedSesquilinearFormValue ℝ H H) (α : ℝ),
    (FormCoerciveValue ℝ H a α ↔ 0 < α ∧ ∀ x, α * ‖x‖ ^ 2 ≤ a x x) ∧
    (FormHermitianValue ℝ H a ↔ ∀ x y, a x y = a y x)

def InnerFormEvaluation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (x y : H),
    InnerFormValue 𝕜 H x y = ⟪x, y⟫_𝕜

def OrthogonalMembership : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : Set H) (y : H),
    y ∈ OrthogonalComplementValue 𝕜 H A ↔ ∀ x ∈ A, ⟪x, y⟫_𝕜 = 0

def OrthogonalClosed : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : Set H),
    IsClosed (OrthogonalComplementValue 𝕜 H A : Set H)

def OrthogonalSubmodule : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (M : Submodule 𝕜 H),
    OrthogonalComplementValue 𝕜 H (M : Set H) = M.orthogonal

/-- The existence class imposes no extra restriction in the source's closed
Hilbert-subspace setting. It is also available for any complete subspace. -/
def ClosedProjectionExists : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : Submodule 𝕜 H), IsClosed (M : Set H) → M.HasOrthogonalProjection

def ProjectionCharacterization : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (M : Submodule 𝕜 H) [M.HasOrthogonalProjection] (x : H),
    OrthogonalProjectionValue 𝕜 H M x ∈ M ∧
      x - OrthogonalProjectionValue 𝕜 H M x ∈ M.orthogonal

/-- Compare all geometry with that saved before real restriction of scalars.
The topological and uniform structures, hence completeness, are unchanged. -/
def RealificationGeometry : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H],
    let innerK : H → H → 𝕜 := inner 𝕜
    let normH : H → ℝ := norm
    let distH : H → H → ℝ := dist
    let topH : TopologicalSpace H := inferInstance
    let uniformH : UniformSpace H := inferInstance
    letI := RealificationValue 𝕜 H
    (∀ x y, ⟪x, y⟫_ℝ = RCLike.re (innerK x y)) ∧
    (∀ x, ‖x‖ = normH x) ∧ (∀ x y, dist x y = distH x y) ∧
    (inferInstance : TopologicalSpace H) = topH ∧
    (inferInstance : UniformSpace H) = uniformH ∧
    (∀ (r : ℝ) (x : H), r • x = (r : 𝕜) • x)

end ExpandedFA.Hilbert.Conventions.Spec
