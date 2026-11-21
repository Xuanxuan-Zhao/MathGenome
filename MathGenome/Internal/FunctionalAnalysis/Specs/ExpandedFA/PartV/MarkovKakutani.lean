import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Compactness.Compact

/-! Independent statements for paper.tex 23220–23238.
Affineness and continuity are required only on K. The real theorem is stated
for Hausdorff topological vector spaces, a stronger result than the locally
convex case. Complex spaces are regarded as real spaces for convexity.
The index type is arbitrary and may be empty.
-/
namespace ExpandedFA.PartV.MarkovKakutaniSpec

universe u v

/-- Preservation of real convex combinations of points of the given set. -/
def AffineOn {E : Type u} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (f : E → E) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) = a • f x + b • f y

def SingleMap : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → AffineOn K f →
      ∃ x ∈ K, f x = x

def CommonFixedPoint : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ (ι : Type v) (f : ι → E → E),
      (∀ i, ContinuousOn (f i) K) → (∀ i, Set.MapsTo (f i) K K) →
      (∀ i, AffineOn K (f i)) →
      (∀ i j, ∀ x ∈ K, f i (f j x) = f j (f i x)) →
      ∃ x ∈ K, ∀ i, f i x = x

/-- An intrinsic version for maps whose domain and codomain are precisely K. -/
def SubtypeCommonFixedPoint : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (K : Set E), K.Nonempty → IsCompact K → ∀ (hconv : Convex ℝ K)
    (ι : Type v) (f : ι → K → K),
      (∀ i, Continuous (f i)) →
      (∀ i (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
        (f i ⟨a • (x : E) + b • (y : E), hconv x.property y.property ha hb hab⟩ : E) =
          a • (f i x : E) + b • (f i y : E)) →
      (∀ i j, Function.Commute (f i) (f j)) →
      ∃ x : K, ∀ i, f i x = x

/-- The complex case uses the induced real module, with no extra real
module or continuity assumption on the input complex topological vector space. -/
def ComplexCommonFixedPoint : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E],
    letI : Module ℝ E := Module.compHom E Complex.ofRealHom
    ∀ (K : Set E), K.Nonempty → IsCompact K → ∀ (hconv : Convex ℝ K)
    (ι : Type v) (f : ι → K → K),
      (∀ i, Continuous (f i)) →
      (∀ i (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
        (f i ⟨a • (x : E) + b • (y : E), hconv x.property y.property ha hb hab⟩ : E) =
          a • (f i x : E) + b • (f i y : E)) →
      (∀ i j, Function.Commute (f i) (f j)) →
      ∃ x : K, ∀ i, f i x = x

end ExpandedFA.PartV.MarkovKakutaniSpec
