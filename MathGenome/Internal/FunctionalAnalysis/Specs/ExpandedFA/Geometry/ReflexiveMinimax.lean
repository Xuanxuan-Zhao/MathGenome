import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.CompactConvexMinimax
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14BallCharacterization
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Specializations of `fa2:p2:minimax`, paper.tex 13297–13359.
All semicontinuity hypotheses are relative to the displayed sets and use the
original norm topologies. Reflexivity is surjectivity of canonical evaluation.
The shared conclusion records finite real extrema, all four attainments, and
the saddle inequalities for every pair of outer optimizers. -/
namespace Specs.ExpandedFA.Geometry.ReflexiveMinimax
open Set
open Specs.ExpandedFA.Geometry.CompactConvexMinimax
universe u v

def reflexiveMinimaxType : Prop :=
  ∀ {E : Type u} {G : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (K : Set E) (L : Set G) (F : E → G → ℝ),
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E →
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ G →
    K.Nonempty → IsClosed K → Bornology.IsBounded K → Convex ℝ K →
    L.Nonempty → IsClosed L → Bornology.IsBounded L → Convex ℝ L →
    (∀ y ∈ L, ConvexOn ℝ K (fun x => F x y)) →
    (∀ y ∈ L, LowerSemicontinuousOn (fun x => F x y) K) →
    (∀ x ∈ K, ConcaveOn ℝ L (F x)) →
    (∀ x ∈ K, UpperSemicontinuousOn (F x) L) →
    MinimaxConclusion K L F

/-- A payoff defined only on K × L requires no regularity outside its domain. -/
def restrictedReflexiveMinimaxType : Prop :=
  ∀ {E : Type u} {G : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (K : Set E) (L : Set G) (F : K → L → ℝ),
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E →
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ G →
    K.Nonempty → IsClosed K → Bornology.IsBounded K → Convex ℝ K →
    L.Nonempty → IsClosed L → Bornology.IsBounded L → Convex ℝ L →
    (∀ y : L, ConvexOn ℝ K (fun x => extendPayoff F x y)) →
    (∀ y : L, LowerSemicontinuous (fun x : K => F x y)) →
    (∀ x : K, ConcaveOn ℝ L (extendPayoff F x)) →
    (∀ x : K, UpperSemicontinuous (F x)) →
    MinimaxConclusion K L (extendPayoff F)

/-- Continuous bilinear von Neumann theorem on compact convex sets. -/
def compactBilinearMinimaxType : Prop :=
  ∀ {E : Type u} {G : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [T2Space G]
    (K : Set E) (L : Set G) (B : E →ₗ[ℝ] G →ₗ[ℝ] ℝ),
    K.Nonempty → IsCompact K → Convex ℝ K →
    L.Nonempty → IsCompact L → Convex ℝ L →
    Continuous (fun p : E × G => B p.1 p.2) →
    MinimaxConclusion K L (fun x y => B x y)

/-- Continuous bilinear von Neumann theorem on closed bounded convex sets
of real reflexive Banach spaces. -/
def reflexiveBilinearMinimaxType : Prop :=
  ∀ {E : Type u} {G : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (K : Set E) (L : Set G) (B : E →L[ℝ] G →L[ℝ] ℝ),
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E →
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ G →
    K.Nonempty → IsClosed K → Bornology.IsBounded K → Convex ℝ K →
    L.Nonempty → IsClosed L → Bornology.IsBounded L → Convex ℝ L →
    MinimaxConclusion K L (fun x y => B x y)

end Specs.ExpandedFA.Geometry.ReflexiveMinimax
