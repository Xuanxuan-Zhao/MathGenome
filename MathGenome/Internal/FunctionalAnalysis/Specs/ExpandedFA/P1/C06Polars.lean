import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
Independent specifications for fa2:p1:c06:polars, paper.tex 1174–1185.
The zero-inclusive hull convention is specified at 1186–1197 and 1202–1205.
All duals are the original norm-continuous scalar-linear duals. Scalar norm
means absolute value over ℝ and modulus over ℂ. Convexity is real and balance
is over the original scalar field. No completeness or nonemptiness is assumed.
The topology values reuse the canonical upstream pairing and weak-star values;
Lean orders topologies in reverse order of their open sets.
-/

namespace ExpandedFA.P1.C06Polars.Spec

universe u v
open scoped BigOperators

def PolarType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set E → Set (E →L[𝕜] 𝕜)

noncomputable def PolarValue : PolarType :=
  fun 𝕜 E _ _ _ A => {f : E →L[𝕜] 𝕜 | ∀ a ∈ A, ‖f a‖ ≤ 1}

def PrepolarType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set (E →L[𝕜] 𝕜) → Set E

noncomputable def PrepolarValue : PrepolarType :=
  fun _ E _ _ _ B => {x : E | ∀ f ∈ B, ‖f x‖ ≤ 1}

def WeakEquivType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    E ≃ₗ[𝕜] WeakSpace 𝕜 E

noncomputable def WeakEquivValue : WeakEquivType :=
  fun 𝕜 E _ _ _ => toWeakSpace 𝕜 E

def WeakStarEquivType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (E →L[𝕜] 𝕜) ≃ₗ[𝕜] WeakDual 𝕜 E

noncomputable def WeakStarEquivValue : WeakStarEquivType :=
  fun _ _ _ _ _ => StrongDual.toWeakDual

def WeakTopologyType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    TopologicalSpace E

noncomputable def WeakTopologyValue : WeakTopologyType :=
  fun 𝕜 E _ _ _ => C12DualPairSpec.DualPairTopologyValue 𝕜 E
    (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)

def WeakStarTopologyType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    TopologicalSpace (E →L[𝕜] 𝕜)

noncomputable def WeakStarTopologyValue : WeakStarTopologyType :=
  fun 𝕜 E _ _ _ => C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E

def IsAbsolutelyConvexType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set E → Prop

noncomputable def IsAbsolutelyConvexValue : IsAbsolutelyConvexType :=
  fun 𝕜 E _ _ _ A =>
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    Convex ℝ A ∧ Balanced 𝕜 A

def AbsolutelyConvexHullType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set E → Set E

noncomputable def AbsolutelyConvexHullValue : AbsolutelyConvexHullType :=
  fun 𝕜 E _ _ _ A => {y : E | ∃ (n : ℕ) (c : Fin n → 𝕜) (x : Fin n → E),
    (∀ i, x i ∈ A) ∧ (∑ i, ‖c i‖) ≤ 1 ∧ (∑ i, c i • x i) = y}

def ClosedAbsolutelyConvexHullType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set E → Set E

noncomputable def ClosedAbsolutelyConvexHullValue : ClosedAbsolutelyConvexHullType :=
  fun 𝕜 E _ _ _ A => closure (AbsolutelyConvexHullValue 𝕜 E A)

def PolarMembership : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ (A : Set E) (f : E →L[𝕜] 𝕜),
    f ∈ PolarValue 𝕜 E A ↔ ∀ a ∈ A, ‖f a‖ ≤ 1

def PrepolarMembership : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ (B : Set (E →L[𝕜] 𝕜)) (x : E),
    x ∈ PrepolarValue 𝕜 E B ↔ ∀ f ∈ B, ‖f x‖ ≤ 1

def WeakEquivIdentity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ x : E, (WeakEquivValue 𝕜 E x : E) = x

def WeakStarEquivIdentity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ (f : E →L[𝕜] 𝕜) (x : E), WeakStarEquivValue 𝕜 E f x = f x

def WeakTopologyInitial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    WeakTopologyValue 𝕜 E =
    ⨅ (f : E →L[𝕜] 𝕜), TopologicalSpace.induced f inferInstance

def WeakStarTopologyInitial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    WeakStarTopologyValue 𝕜 E =
    ⨅ (x : E), TopologicalSpace.induced (fun f : E →L[𝕜] 𝕜 => f x) inferInstance

/-- Fix the norm-continuous dual before binding an arbitrary competing topology.
In Lean's topology order, `t ≤ weak` means `t` is finer than `weak`. -/
def WeakTopologyCoarsest : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    let D := E →L[𝕜] 𝕜
    ∀ t : TopologicalSpace E,
    (∀ f : D, @Continuous E 𝕜 t inferInstance f) ↔
      t ≤ WeakTopologyValue 𝕜 E

def WeakStarTopologyCoarsest : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    let D := E →L[𝕜] 𝕜
    ∀ t : TopologicalSpace D,
    (∀ x : E, @Continuous D 𝕜 t inferInstance (fun f => f x)) ↔
      t ≤ WeakStarTopologyValue 𝕜 E

def AbsolutelyConvexCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ A : Set E,
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    IsAbsolutelyConvexValue 𝕜 E A ↔ Convex ℝ A ∧
      (∀ (a : 𝕜), ‖a‖ ≤ 1 → ∀ x ∈ A, a • x ∈ A)

def HullZero : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ A : Set E, (0 : E) ∈ AbsolutelyConvexHullValue 𝕜 E A

def HullEmpty : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    AbsolutelyConvexHullValue 𝕜 E (∅ : Set E) = {0}

def SubsetHull : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ A : Set E, A ⊆ AbsolutelyConvexHullValue 𝕜 E A

def HullAbsolutelyConvex : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ A : Set E,
    IsAbsolutelyConvexValue 𝕜 E (AbsolutelyConvexHullValue 𝕜 E A)

def HullMinimal : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∀ A C : Set E, A ⊆ C → (0 : E) ∈ C →
    IsAbsolutelyConvexValue 𝕜 E C → AbsolutelyConvexHullValue 𝕜 E A ⊆ C

end ExpandedFA.P1.C06Polars.Spec
