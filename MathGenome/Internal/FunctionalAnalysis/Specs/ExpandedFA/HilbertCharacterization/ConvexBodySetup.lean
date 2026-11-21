import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Independent data for paper.tex:9081–9109. The inner product is the
auxiliary Euclidean structure, not a conclusion about the body's gauge.
A body is compact, convex, symmetric about zero, with zero interior.
Projections are endomorphisms with range in L, fixing L, and preserving K.
Normal cones contain zero and consist of continuous real linear functionals.
In finite dimension these are precisely all real linear functionals. -/
namespace Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup

universe u
open Set Metric
open scoped Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SymmetricConvexBody (K : Set E) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (∀ x ∈ K, -x ∈ K) ∧ (0 : E) ∈ interior K

def BodyProjection (K : Set E) (L : Submodule ℝ E) (P : E →L[ℝ] E) : Prop :=
  (∀ x, P x ∈ L) ∧ (∀ x ∈ L, P x = x) ∧ MapsTo P K K

def PlaneProjections (K : Set E) : Prop :=
  ∀ L : Submodule ℝ E, Module.finrank ℝ L = 2 →
    ∃ P : E →L[ℝ] E, BodyProjection K L P

/-- Full geometric hypotheses; no smoothness or strict convexity is included. -/
def ProjectionBody {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (K : Set V) : Prop :=
  Module.finrank ℝ V = 3 ∧ SymmetricConvexBody K ∧ PlaneProjections K

def NormalCone (K : Set E) (p : E) : Set (E →L[ℝ] ℝ) :=
  {f | ∀ x ∈ K, f x ≤ f p}

def PlanarNormalCone (K : Set E) (L : Submodule ℝ E) (p : L) :
    Set (L →L[ℝ] ℝ) :=
  {g | ∀ x : L, (x : E) ∈ K → g x ≤ g p}

def restrictNormal (L : Submodule ℝ E) (f : E →L[ℝ] ℝ) : L →L[ℝ] ℝ :=
  f.comp L.subtypeL

-- Expected values for the implementation's public data definitions.
def bodyType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], Set E → Prop
def bodyValue : bodyType.{u} := @SymmetricConvexBody

def projectionType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  Set E → Submodule ℝ E → (E →L[ℝ] E) → Prop
def projectionValue : projectionType.{u} := @BodyProjection

def planesType := bodyType.{u}
def planesValue : planesType.{u} := @PlaneProjections

def hypothesesType := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E], Set E → Prop
def hypothesesValue : hypothesesType.{u} := @ProjectionBody

def normalConeType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  Set E → E → Set (E →L[ℝ] ℝ)
def normalConeValue : normalConeType.{u} := @NormalCone

def planarNormalConeType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  Set E → (L : Submodule ℝ E) → L → Set (L →L[ℝ] ℝ)
def planarNormalConeValue : planarNormalConeType.{u} := @PlanarNormalCone

def restrictionType := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  (L : Submodule ℝ E) → (E →L[ℝ] ℝ) → (L →L[ℝ] ℝ)
def restrictionValue : restrictionType.{u} := @restrictNormal

/-- The projection's full range and idempotence follow from its defining data. -/
def projectionAlgebraType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (L : Submodule ℝ E) (P : E →L[ℝ] E), BodyProjection K L P →
      LinearMap.range P.toLinearMap = L ∧ P.comp P = P

def projectionImageType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (L : Submodule ℝ E) (P : E →L[ℝ] E), BodyProjection K L P →
      P '' K = K ∩ (L : Set E)

/-- Positive inner and outer radii always exist. Closed balls are r B₂ and R B₂. -/
def radiiType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E), SymmetricConvexBody K →
      ∃ r R : ℝ, 0 < r ∧ 0 < R ∧ closedBall 0 r ⊆ K ∧ K ⊆ closedBall 0 R

/-- This bound applies to every admissible projection with the same radii. -/
def projectionBoundType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (L : Submodule ℝ E) (P : E →L[ℝ] E) (r R : ℝ),
    BodyProjection K L P → 0 < r → 0 ≤ R →
      closedBall 0 r ⊆ K → K ⊆ closedBall 0 R → ‖P‖ ≤ R / r

def uniformBoundType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E), ProjectionBody K →
      ∃ r R : ℝ, 0 < r ∧ 0 < R ∧ closedBall 0 r ⊆ K ∧ K ⊆ closedBall 0 R ∧
        ∀ (L : Submodule ℝ E) (P : E →L[ℝ] E), BodyProjection K L P → ‖P‖ ≤ R / r

/-- Closedness, zero membership, addition and nonnegative scaling of the cone. -/
def normalConePropertiesType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (p : E),
    IsClosed (NormalCone K p) ∧ (0 : E →L[ℝ] ℝ) ∈ NormalCone K p ∧
      (∀ f ∈ NormalCone K p, ∀ g ∈ NormalCone K p, f + g ∈ NormalCone K p) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f ∈ NormalCone K p, t • f ∈ NormalCone K p)

def positiveNormalType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (p : E), (0 : E) ∈ interior K →
      ∀ f ∈ NormalCone K p, f ≠ 0 → 0 < f p

def supportingNormalType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (p : E), SymmetricConvexBody K → p ∈ frontier K →
      ∃ f ∈ NormalCone K p, f ≠ 0

/-- The constructive pullback is stronger than surjectivity alone. -/
def extendNormalType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (L : Submodule ℝ E) (P : E →L[ℝ] E) (hP : BodyProjection K L P),
    ∀ (p : L) (g : L →L[ℝ] ℝ), g ∈ PlanarNormalCone K L p →
      ∃ f ∈ NormalCone K (p : E), restrictNormal L f = g ∧
        ∀ x : E, f x = g ⟨P x, hP.1 x⟩

/-- Any projection onto a central subspace gives the stated equality of cones. -/
def restrictionTypeTheorem : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (L : Submodule ℝ E) (P : E →L[ℝ] E), BodyProjection K L P →
    ∀ p : L, restrictNormal L '' NormalCone K (p : E) = PlanarNormalCone K L p

/-- Original three-dimensional specialization at boundary points in central planes. -/
def planeRestrictionType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E), ProjectionBody K →
    ∀ (L : Submodule ℝ E), Module.finrank ℝ L = 2 →
    ∀ p : L, (p : E) ∈ frontier K →
      restrictNormal L '' NormalCone K (p : E) = PlanarNormalCone K L p

end Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
