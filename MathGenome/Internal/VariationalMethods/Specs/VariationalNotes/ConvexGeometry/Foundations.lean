import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
Independent specification of paper.tex, §v01-01, Definition (lines 115–129)
and Lemma `lem:hull-descriptions` (lines 131–147). The source's cones
contain zero, so they use `PointedCone`, rather than unrestricted `ConvexCone`.
The relative-interior definition extends to all sets and topologies; in particular
it applies to the nonempty finite-dimensional convex sets specified in the text.
-/

open Set
open scoped Pointwise
noncomputable section
universe u v

namespace VariationalNotes.ConvexGeometry.Specs

def IsAffineType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Prop

def IsAffine {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Prop :=
  ∃ A : AffineSubspace ℝ E, (A : Set E) = s

def affineHullType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Set E

def affineHull {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Set E :=
  (affineSpan ℝ s : Set E)

def IsConeType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Prop

def IsCone {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Prop :=
  (0 : E) ∈ s ∧ (∀ ⦃x y⦄, x ∈ s → y ∈ s → x + y ∈ s) ∧
    (∀ (r : ℝ), 0 ≤ r → ∀ ⦃x⦄, x ∈ s → r • x ∈ s)

def conicHullType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Set E

def conicHull {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) : Set E :=
  (PointedCone.hull ℝ s : Set E)

def IsFaceType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Set E → Prop

def IsFace {E : Type u} [AddCommGroup E] [Module ℝ E] (C F : Set E) : Prop :=
  Convex ℝ F ∧ IsExtreme ℝ C F

def IsExtremePointType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → E → Prop

def IsExtremePoint {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) (x : E) : Prop :=
  x ∈ C.extremePoints ℝ

def relativeInteriorType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set E → Set E

def relativeInterior {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (s : Set E) : Set E :=
  intrinsicInterior ℝ s

def affineHull_description : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), x ∈ affineHull C ↔
  ∃ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C ∧
    (∑ y ∈ s, w y) = 1 ∧ (∑ y ∈ s, w y • y) = x

def convexHull_description : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), x ∈ convexHull ℝ C ↔
  ∃ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C ∧
    (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y) = 1 ∧ (∑ y ∈ s, w y • y) = x

def conicHull_description : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), x ∈ conicHull C ↔
  ∃ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C ∧
    (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y • y) = x

def isAffine_iff_combinations : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, IsAffine C ↔
  ∀ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C →
    (∑ y ∈ s, w y) = 1 → (∑ y ∈ s, w y • y) ∈ C

def convex_iff_combinations : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, Convex ℝ C ↔
  ∀ (s : Finset E) (w : E → ℝ), (↑s : Set E) ⊆ C →
    (∀ y ∈ s, 0 ≤ w y) → (∑ y ∈ s, w y) = 1 → (∑ y ∈ s, w y • y) ∈ C

def isCone_iff_pointedCone : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, IsCone C ↔
  ∃ K : PointedCone ℝ E, (K : Set E) = C

def hull_properties : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E,
  (IsAffine (affineHull C) ∧ C ⊆ affineHull C ∧
    ∀ A, IsAffine A → C ⊆ A → affineHull C ⊆ A) ∧
  (Convex ℝ (convexHull ℝ C) ∧ C ⊆ convexHull ℝ C ∧
    ∀ A, Convex ℝ A → C ⊆ A → convexHull ℝ C ⊆ A) ∧
  (IsCone (conicHull C) ∧ C ⊆ conicHull C ∧
    ∀ A, IsCone A → C ⊆ A → conicHull C ⊆ A)

def empty_hulls : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], affineHull (∅ : Set E) = ∅ ∧ convexHull ℝ (∅ : Set E) = ∅ ∧
  conicHull (∅ : Set E) = {0}

def face_iff_segment : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C F : Set E, IsFace C F ↔
  F ⊆ C ∧ Convex ℝ F ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 < t → t < 1 →
      (1-t) • x + t • y ∈ F → x ∈ F ∧ y ∈ F

def extremePoint_iff_singleton_face : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ (C : Set E) (x : E), IsExtremePoint C x ↔ IsFace C {x}

def convex_intersections : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ S : Set (Set E), (∀ C ∈ S, Convex ℝ C) → Convex ℝ (⋂₀ S)

def convex_affine_image : Prop :=
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (f : E →ᵃ[ℝ] G) (C : Set E),
    Convex ℝ C → Convex ℝ (f '' C)

def convex_affine_preimage : Prop :=
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (f : E →ᵃ[ℝ] G) (C : Set G),
    Convex ℝ C → Convex ℝ (f ⁻¹' C)

def convex_product : Prop :=
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (C : Set E) (D : Set G),
    Convex ℝ C → Convex ℝ D → Convex ℝ (C ×ˢ D)

def convex_minkowski_sum : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C D : Set E,
  Convex ℝ C → Convex ℝ D → Convex ℝ (C + D)

def cone_linear_image : Prop :=
  ∀ {E : Type u} {G : Type v} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup G] [Module ℝ G], ∀ (f : E →ₗ[ℝ] G) (C : Set E),
    IsCone C → IsCone (f '' C)

def cone_convex : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], ∀ C : Set E, IsCone C → Convex ℝ C

def relativeInterior_eq : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (C : Set E), relativeInterior C =
    (Subtype.val : affineSpan ℝ C → E) ''
      interior ((Subtype.val : affineSpan ℝ C → E) ⁻¹' C)

def relativeInterior_empty : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  relativeInterior (∅ : Set E) = ∅

def convex_cartesian_products : Prop :=
  ∀ {ι : Type u} {E : ι → Type v} [∀ i, AddCommGroup (E i)]
    [∀ i, Module ℝ (E i)], ∀ (I : Set ι) (C : ∀ i, Set (E i)),
    (∀ i ∈ I, Convex ℝ (C i)) → Convex ℝ (I.pi C)

end VariationalNotes.ConvexGeometry.Specs
