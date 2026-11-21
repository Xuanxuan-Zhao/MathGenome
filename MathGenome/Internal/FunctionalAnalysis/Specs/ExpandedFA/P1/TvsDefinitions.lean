import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
Independent definitions for `fa2:p1:tvs-definitions`, paper.tex:1745–1758.

The scalar field is real or complex (`RCLike`). Convexity and positive
multiples use the underlying real vector space. When both module structures
are supplied, `IsScalarTower ℝ 𝕜 E` requires that they agree. Such a real
structure is always available by restricting scalars.

`TVS` and `LCS` deliberately have no separation premise. In the chapter's
usual setting add `[T2Space E]` separately; the earlier gauge and open
separation results can therefore use precisely the same interfaces.

The uniform space used below is the translation uniformity of the *given*
topology. No independently chosen compatible metric or uniformity is used.
-/

open Set Filter TopologicalSpace
open scoped Topology Pointwise

universe u

namespace ExpandedFA.P1

/-- Native TVS interface, without a separation axiom. Continuous negation in
`IsTopologicalAddGroup` follows from multiplication by `-1`; see the candidate's
joint-continuity identification. -/
abbrev TVS (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] : Prop :=
  IsTopologicalAddGroup E ∧ ContinuousSMul 𝕜 E

/-- Local convexity is real convexity, also for a complex vector space. -/
abbrev LCS (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] : Prop :=
  TVS 𝕜 E ∧ LocallyConvexSpace ℝ E

/-- The manuscript's radial absorption condition. In particular, this is not
Mathlib's stronger `Absorbent` condition on an arbitrary set. -/
def Absorbing {E : Type*} [AddCommGroup E] [Module ℝ E] (A : Set E) : Prop :=
  ∀ x : E, ∃ t : ℝ, 0 < t ∧ x ∈ t • A

/-- The manuscript's boundedness quantifiers, including empty sets. -/
def Bounded {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (A : Set E) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ s : ℝ, 0 < s ∧ ∀ t : ℝ, s ≤ t → A ⊆ t • U

/-- A Cauchy net for the translation uniformity, over any nonempty directed
preorder, not merely a sequence. -/
def CauchyNet {E ι : Type*} [AddCommGroup E] [TopologicalSpace E]
    [Preorder ι] (x : ι → E) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ i : ι, ∀ j ≥ i, ∀ k ≥ i, x j - x k ∈ U

/-- Intrinsic completeness of a topological additive group. The canonical
uniform structure preserves its given topology. -/
abbrev TranslationComplete (E : Type*) [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] : Prop :=
  @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)

/-- F-spaces have no local convexity requirement. Metrizability implies
Hausdorffness. Completeness uses the translation uniformity. -/
def FSpace (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] : Prop :=
  ∃ (_hadd : IsTopologicalAddGroup E), ContinuousSMul 𝕜 E ∧
    MetrizableSpace E ∧ TranslationComplete E

/-- A Frechet space is a locally convex F-space. -/
def FrechetSpace (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] : Prop :=
  FSpace 𝕜 E ∧ LocallyConvexSpace ℝ E

namespace TvsDefinitionsSpec

-- Independent expected types and values for the definition bindings.
def tvsType := ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E], Prop

def tvsValue : tvsType := fun 𝕜 E _ _ _ _ => TVS 𝕜 E

def lcsType := ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E], Prop

def lcsValue : lcsType := fun 𝕜 E _ _ _ _ _ _ => LCS 𝕜 E

def balancedType := ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
  [Module 𝕜 E], Set E → Prop

def balancedValue : balancedType := fun 𝕜 _ _ _ _ A =>
  ∀ a : 𝕜, ‖a‖ ≤ 1 → a • A ⊆ A

def absorbingType := ∀ (E : Type*) [AddCommGroup E] [Module ℝ E], Set E → Prop

def absorbingValue : absorbingType := fun _ _ _ A => Absorbing A

def boundedType := ∀ (E : Type*) [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E], Set E → Prop

def boundedValue : boundedType := fun _ _ _ _ A => Bounded A

def cauchyNetType := ∀ (E ι : Type*) [AddCommGroup E] [TopologicalSpace E]
  [Preorder ι], (ι → E) → Prop

def cauchyNetValue : cauchyNetType := fun _ _ _ _ _ x => CauchyNet x

def completeType := ∀ (E : Type*) [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E], Prop

def completeValue : completeType := fun E _ _ _ => TranslationComplete E

def fSpaceType := tvsType

def fSpaceValue : fSpaceType := fun 𝕜 E _ _ _ _ => FSpace 𝕜 E

def frechetSpaceType := lcsType

def frechetSpaceValue : frechetSpaceType := fun 𝕜 E _ _ _ _ _ _ => FrechetSpace 𝕜 E

/-- Joint continuity, with no Hausdorff assumption. -/
def JointContinuity : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E], TVS 𝕜 E ↔
      Continuous (fun p : E × E => p.1 + p.2) ∧
      Continuous (fun p : 𝕜 × E => p.1 • p.2)

/-- The native real local convexity class is exactly the source's zero
neighborhood basis condition, on every TVS, separated or not. -/
def LocalConvexity : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E], TVS 𝕜 E →
      (LCS 𝕜 E ↔ ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : E), Convex ℝ V ∧ V ⊆ U)

/-- The uniformity is expressed solely by differences and zero neighborhoods. -/
def TranslationUniformity : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E],
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    uniformity E = Filter.comap (fun p : E × E => p.2 - p.1) (𝓝 (0 : E))

/-- Native Cauchy filters express the same differences condition. This also
makes the filter presentation of completeness explicit. -/
def CauchyFilters : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E],
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    ∀ f : Filter E, Cauchy f ↔ f.NeBot ∧
      ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ f, ∀ x ∈ V, ∀ y ∈ V, x - y ∈ U

/-- The source's Cauchy-net criterion over an arbitrary directed preorder. -/
def CauchyNets : Prop :=
  ∀ (E ι : Type*) [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι],
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    ∀ x : ι → E, Cauchy (Filter.map x atTop) ↔ CauchyNet x

/-- Complete translation uniformities make all Cauchy nets converge. -/
def CompleteNets : Prop :=
  ∀ (E ι : Type*) [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι], TranslationComplete E →
    ∀ x : ι → E, CauchyNet x → ∃ a : E, Tendsto x atTop (𝓝 a)

/-- Completeness in terms of arbitrary Cauchy filters, with differences only. -/
def CompleteFilters : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E],
    TranslationComplete E ↔ ∀ f : Filter E, f.NeBot →
      (∀ U ∈ 𝓝 (0 : E), ∃ V ∈ f, ∀ x ∈ V, ∀ y ∈ V, x - y ∈ U) →
      ∃ a : E, f ≤ 𝓝 a

/-- The native filter definition of completeness is equivalent to the source's
convergence of every Cauchy net. Index types in the space's own universe already
suffice for the converse; `CompleteNets` also covers larger index universes. -/
def CompleteNetsIff : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E],
    TranslationComplete E ↔
      ∀ (ι : Type u) [Preorder ι] [IsDirectedOrder ι] [Nonempty ι],
        ∀ x : ι → E, CauchyNet x → ∃ a : E, Tendsto x atTop (𝓝 a)

end TvsDefinitionsSpec
end ExpandedFA.P1
