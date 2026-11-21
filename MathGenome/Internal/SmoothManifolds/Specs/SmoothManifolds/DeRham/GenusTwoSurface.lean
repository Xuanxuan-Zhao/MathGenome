import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.GenusTwoSurface

/-! The genus-two clause of M11.04 (paper.tex 2320–2327, 2378–2422).
The underlying space is the literal reflected connected sum in GenusTwoData,
with its quotient topology and prescribed maximal atlas. We quantify over
realizations of this fixed smooth structure, as in the upstream torus Specs.
The groups are the quotients of all smooth intrinsic closed forms by all exact
forms from M11.01. Linear equivalences assert the dimensions together with
finite dimensionality, avoiding the ambiguity of finrank on infinite spaces.
Orientation is already supplied by the construction and adds no hypothesis.
-/
set_option autoImplicit false
noncomputable section

namespace Specs.SmoothManifolds.DeRham.GenusTwoSurface
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.DeRhamData
  _root_.SmoothManifolds.GenusTwoData

/-- Degree zero of the constructed connected surface has dimension one. -/
def degree_zeroType : Prop :=
  ∀ (S : SmoothManifold 2 .euclidean Surface),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      Nonempty (K.Cohomology 0 ≃ₗ[ℝ] ℝ)

/-- All four independent degree-one classes on the actual connected sum. -/
def degree_oneType : Prop :=
  ∀ (S : SmoothManifold 2 .euclidean Surface),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      Nonempty (K.Cohomology 1 ≃ₗ[ℝ] (Fin 4 → ℝ))

/-- Degree two has dimension one. No integral or connecting class is assumed. -/
def degree_twoType : Prop :=
  ∀ (S : SmoothManifold 2 .euclidean Surface),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      Nonempty (K.Cohomology 2 ≃ₗ[ℝ] ℝ)

/-- Every other degree is zero, including all negative integer degrees. -/
def other_degreesType : Prop :=
  ∀ (S : SmoothManifold 2 .euclidean Surface),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      (∀ k : ℕ, 2 < k → Subsingleton (K.Cohomology k)) ∧
      (∀ j : ℕ, Subsingleton (K.CohomologyZ (.negSucc j)))

end Specs.SmoothManifolds.DeRham.GenusTwoSurface
