import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori

/-!
The no-retraction example, paper.tex:2695–2712.

`Sphere n` is the shared, actual sum-of-squares sphere in R^(n+1).
The closed ball below uses that same Euclidean length, not the sup norm on
coordinate tuples. Its boundary inclusion is the literal inclusion.

Nonextension is independent of orientation. The smooth statement is made for
all smooth structures on these spaces, so in particular applies to the standard
ball and its sphere with the induced outward-first orientation. The continuous
statement includes every n, and the zero-dimensional case is also exposed
separately. No extension, collar smoothness, or smoothing certificate is assumed.
-/
namespace SmoothManifolds.SphereNonextensionData
open ModelData SphereTorusData

/-- The closed standard (n+1)-ball with its subspace topology. -/
abbrev ClosedBall (n : ℕ) := {x : Euclidean (n + 1) // squareSum x ≤ 1}

/-- The standard boundary inclusion, with no coordinate changes. -/
def boundaryInclusion {n : ℕ} (x : Sphere n) : ClosedBall n :=
  ⟨x.val, x.property.le⟩

end SmoothManifolds.SphereNonextensionData

namespace Specs.SmoothManifolds.Degree.SphereNonextension
open _root_.SmoothManifolds _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.SphereNonextensionData

/-- In particular this excludes all continuous retractions, in all dimensions. -/
def continuous_nonextensionType : Prop :=
  ∀ n : ℕ, ¬ ∃ F : ClosedBall n → Sphere n,
    Continuous F ∧ ∀ x : Sphere n, F (boundaryInclusion x) = x

/-- The original positive-dimensional smooth nonextension assertion.
Smoothness is the project's all-charts local ambient-extension convention. -/
def smooth_nonextensionType : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (S : SmoothManifold (n + 1) .halfSpace (ClosedBall n))
      (T : SmoothManifold n .euclidean (Sphere n)),
      ¬ ∃ F : ClosedBall n → Sphere n,
        IsSmoothMap S T F ∧ ∀ x : Sphere n, F (boundaryInclusion x) = x

/-- The two-point sphere S⁰ cannot be retracted from the closed interval B¹. -/
def zero_dimensional_nonextensionType : Prop :=
  ¬ ∃ F : ClosedBall 0 → Sphere 0,
    Continuous F ∧ ∀ x : Sphere 0, F (boundaryInclusion x) = x

end Specs.SmoothManifolds.Degree.SphereNonextension
