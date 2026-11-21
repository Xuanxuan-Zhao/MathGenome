import Mathlib.Analysis.Convex.Extreme
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.Compactness.Compact

/-!
Independent interface for `paper.tex`, Definition `fa2:p1:c24:faces` (lines 4935–4943).
All coefficients are real, also when `E` carries additional complex scalars.
The algebraic definitions make sense without a topology or convexity of the
ambient set. In particular they apply to every convex subset of a Hausdorff
locally convex real topological vector space, as required in Chapter 24.
Compactness is always taken in the supplied ambient topology.
-/

universe u

namespace ExpandedFA.P1.C24FacesSpec

/-- The paper's extreme points, using its one-parameter proper combinations. -/
def extremePoints {E : Type u} [AddCommGroup E] [Module ℝ E] (K : Set E) : Set E :=
  {x | x ∈ K ∧ ∀ y ∈ K, ∀ z ∈ K, ∀ t : ℝ, 0 < t → t < 1 →
    x = t • y + (1 - t) • z → y = x ∧ z = x}

/-- Unlike the native `IsExtreme`, a face is nonempty and convex. -/
def IsFace {E : Type u} [AddCommGroup E] [Module ℝ E] (K F : Set E) : Prop :=
  F.Nonempty ∧ Convex ℝ F ∧ F ⊆ K ∧
    ∀ y ∈ K, ∀ z ∈ K, ∀ t : ℝ, 0 < t → t < 1 →
      t • y + (1 - t) • z ∈ F → y ∈ F ∧ z ∈ F

/-- Compact face in the actual given topology, without a metric replacement. -/
def IsCompactFace {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (K F : Set E) : Prop :=
  IsFace K F ∧ IsCompact F

-- Full types for the three required definitions; their expected values are above.
def extremePointsType : Type (u + 1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Set E

def isFaceType : Type (u + 1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Set E → Prop

def isCompactFaceType : Type (u + 1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
    Set E → Set E → Prop

/-- Open real segments are exactly the manuscript's proper combinations. -/
def RealCombination : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] {x y z : E},
    x ∈ openSegment ℝ y z ↔
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = t • y + (1 - t) • z

/-- Compatibility with native real extreme points. -/
def extremePoints_eq_native : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (K : Set E),
    extremePoints K = K.extremePoints ℝ

/-- Compatibility with the native endpoint condition, with the face conventions explicit. -/
def isFace_iff_native : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (K F : Set E),
    IsFace K F ↔ F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ K F

/-- The topology in the native formulation is the very same topology. -/
def isCompactFace_iff_native : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (K F : Set E),
    IsCompactFace K F ↔ F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ K F ∧ IsCompact F

/-- Native extremeness admits the empty convex set; the paper's face does not. -/
def empty_face_conventions : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (K : Set E),
    IsExtreme ℝ K ∅ ∧ Convex ℝ (∅ : Set E) ∧ ¬ IsFace K ∅

def not_isCompactFace_empty : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (K : Set E),
    ¬ IsCompactFace K ∅

end ExpandedFA.P1.C24FacesSpec
