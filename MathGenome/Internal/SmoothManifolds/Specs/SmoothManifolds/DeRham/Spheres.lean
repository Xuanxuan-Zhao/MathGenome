import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori

/-! The sphere clause of M11.04 (paper.tex 2320–2345).
These are the ordinary intrinsic de Rham quotients of M11.01 on the actual
sum-of-squares spheres. No support or boundary conditions are imposed.
The positive-dimensional statement includes the circle. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.DeRham.Spheres
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.DeRhamData

/-- The base consists of two points; all positive degrees are zero. -/
def zero_sphereType : Prop :=
  ∀ (S : SmoothManifold 0 .euclidean (Sphere 0))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
    Nonempty (K.Cohomology 0 ≃ₗ[ℝ] (ℝ × ℝ)) ∧
      ∀ k : ℕ, 0 < k → Subsingleton (K.Cohomology k)

/-- H⁰ of every positive-dimensional standard sphere. In fact its topology
alone suffices, so this statement permits any smooth structure on it. -/
def h0_positiveType : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (S : SmoothManifold n .euclidean (Sphere n))
      (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      Nonempty (K.Cohomology 0 ≃ₗ[ℝ] ℝ)

/-- Full degree classification for the standard hemisphere smooth structure.
The two displayed isomorphisms express one-dimensionality without presupposing
finite dimensionality of an uncomputed cohomology group. -/
def sphere_cohomologyType : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (S : SmoothManifold n .euclidean (Sphere n)),
      S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas n) →
      ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
        Nonempty (K.Cohomology 0 ≃ₗ[ℝ] ℝ) ∧
        Nonempty (K.Cohomology n ≃ₗ[ℝ] ℝ) ∧
        ∀ k : ℕ, k ≠ 0 → k ≠ n → Subsingleton (K.Cohomology k)

/-- Degrees strictly above the sphere dimension vanish for every smooth structure. -/
def above_dimensionType : Prop :=
  ∀ (n : ℕ) (S : SmoothManifold n .euclidean (Sphere n))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) (k : ℕ),
      n < k → Subsingleton (K.Cohomology k)

/-- The negative-degree convention in the source is included explicitly. -/
def negative_degreesType : Prop :=
  ∀ (n : ℕ) (S : SmoothManifold n .euclidean (Sphere n))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) (j : ℕ),
      Subsingleton (K.CohomologyZ (.negSucc j))

end Specs.SmoothManifolds.DeRham.Spheres
