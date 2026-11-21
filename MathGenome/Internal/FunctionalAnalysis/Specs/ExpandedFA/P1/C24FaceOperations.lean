import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
Independent statements of `paper.tex`, Lemma `fa2:p1:c24:face-operations` (lines 4944–4967).
The algebraic assertions hold in every real module. Compactness refers to
the supplied topology, so the results specialize to the manuscript's
Hausdorff locally convex spaces, including complex spaces regarded as real.
The maximum is represented by its attaining point `x₀`; its value is `ℓ x₀`.
-/

universe u

namespace ExpandedFA.P1.C24FaceOperationsSpec

open ExpandedFA.P1.C24FacesSpec

def isFace_singleton_iff : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (K : Set E) (x : E),
    IsFace K {x} ↔ x ∈ extremePoints K

/-- Ambient intersections of a nonempty family, provided the intersection is nonempty. -/
def isFace_sInter : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (S : Set (Set E)), S.Nonempty →
    (∀ F ∈ S, IsFace K F) → (⋂₀ S).Nonempty → IsFace K (⋂₀ S)

/-- Relative intersections also cover the empty family, whose intersection in `K` is `K`. -/
def isFace_inter_sInter : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (S : Set (Set E)), Convex ℝ K →
    (∀ F ∈ S, IsFace K F) → (K ∩ ⋂₀ S).Nonempty → IsFace K (K ∩ ⋂₀ S)

def isFace_trans : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] {K F G : Set E},
    IsFace K F → IsFace F G → IsFace K G

/-- Maximum attainment and the full compact-face conclusion, in the original topology. -/
def exists_maximizing_compactFace : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ ℓ : E →L[ℝ] ℝ, ∃ x₀ ∈ K,
      (∀ x ∈ K, ℓ x ≤ ℓ x₀) ∧
        IsCompactFace K {x | x ∈ K ∧ ℓ x = ℓ x₀}

end ExpandedFA.P1.C24FaceOperationsSpec
