import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements of `fa2:p1:c24:compact-map`, paper.tex:5114–5122.

The range closures are in the original ambient normed space, including when
it is incomplete. `RCLike` includes both real and complex scalars. Convexity
is over the underlying reals with the unchanged norm and topology. A compact
map takes bounded subsets of the domain to relatively compact subsets of E;
continuity is a separate hypothesis. No boundedness of D is imposed in the
first assertion, and no nontriviality or positive dimension is assumed.
-/

namespace ExpandedFA.P1.C24CompactMap.Spec

universe u

/-- The normed-space extension, with compact image closure in E itself. -/
def NormedCompactMap : Prop :=
  ∀ (𝕜 : Type) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ D : Set E, D.Nonempty → IsClosed D → Convex ℝ D →
      ∀ T : D → D, Continuous T →
        IsCompact (closure (Set.range (fun x : D => (T x : E)))) →
          ∃ x : D, T x = x

/-- The Banach-space formulation of the first assertion. -/
def BanachCompactMap : Prop :=
  ∀ (𝕜 : Type) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ D : Set E, D.Nonempty → IsClosed D → Convex ℝ D →
      ∀ T : D → D, Continuous T →
        IsCompact (closure (Set.range (fun x : D => (T x : E)))) →
          ∃ x : D, T x = x

/-- Bounded-domain compact self-maps, also valid without completeness. -/
def NormedCompactSelfMap : Prop :=
  ∀ (𝕜 : Type) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ D : Set E, D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D →
      ∀ T : D → D, Continuous T →
        (∀ B : Set D, Bornology.IsBounded (Subtype.val '' B : Set E) →
          IsCompact (closure ((fun x : D => (T x : E)) '' B))) →
            ∃ x : D, T x = x

/-- The stated Banach-space bounded-domain corollary. -/
def BanachCompactSelfMap : Prop :=
  ∀ (𝕜 : Type) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ D : Set E, D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D →
      ∀ T : D → D, Continuous T →
        (∀ B : Set D, Bornology.IsBounded (Subtype.val '' B : Set E) →
          IsCompact (closure ((fun x : D => (T x : E)) '' B))) →
            ∃ x : D, T x = x

end ExpandedFA.P1.C24CompactMap.Spec
