import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.CoveringStructure
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.RealProjectiveSpace

/-! The standard structures are identified by their generating atlases. All
quantifiers range over natural dimensions, including zero. The equality with
the maximal lifted atlas records compatibility with the canonical covering
structure, on the fixed original spaces and topologies. -/
namespace SmoothManifolds.StandardCoveringData
open ModelData AtlasData Set

/-- The ordinary global coordinate chart on R^k. -/
def euclideanAtlas (k : ℕ) : Set (ModelChart k .euclidean (Euclidean k)) :=
  { (Homeomorph.Set.univ (Euclidean k)).symm.toOpenPartialHomeomorph }
end SmoothManifolds.StandardCoveringData

namespace Specs.SmoothManifolds.Ch03.StandardCoverings
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.SphereTorusData _root_.SmoothManifolds.ProjectiveData
  _root_.SmoothManifolds.CoveringData _root_.SmoothManifolds.StandardCoveringData

def euclideanManifoldType : Prop :=
  ∀ k : ℕ, ∃ E : SmoothManifold k .euclidean (Euclidean k),
    E.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (euclideanAtlas k)

/-- The exactly identified coordinatewise R/Z version of the angle covering. -/
def quotientSmoothCoveringType : Prop :=
  ∀ (k : ℕ) (E : SmoothManifold k .euclidean (Euclidean k))
    (Q : SmoothManifold k .euclidean (FlatTorus k)),
    E.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (euclideanAtlas k) →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas k) →
    IsSmoothCovering E Q (quotientProjection k) ∧
    E.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (liftedAtlas Q.smoothStructure.val (quotientProjection k))

/-- The literal trigonometric angle map to the product of the shared S^1. -/
def angleSmoothCoveringType : Prop :=
  ∀ (k : ℕ) (E : SmoothManifold k .euclidean (Euclidean k))
    (T : SmoothManifold k .euclidean (Torus k)),
    E.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (euclideanAtlas k) →
    T.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (productHemisphereAtlas k) →
    IsSmoothCovering E T (angleMap k) ∧
    E.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (liftedAtlas T.smoothStructure.val (angleMap k))

/-- The antipodal quotient for the hemisphere sphere and ratio projective
atlases of Chapter 1, including the two-sheeted S^0 → RP^0. -/
def antipodalSmoothCoveringType : Prop :=
  ∀ (n : ℕ) (S : SmoothManifold n .euclidean (Sphere n))
    (P : SmoothManifold n .euclidean (RealProjectiveSpace n)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas n) →
    P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas n) →
    IsSmoothCovering S P (@projectiveProjection n) ∧
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (liftedAtlas P.smoothStructure.val (@projectiveProjection n))
end Specs.SmoothManifolds.Ch03.StandardCoverings
