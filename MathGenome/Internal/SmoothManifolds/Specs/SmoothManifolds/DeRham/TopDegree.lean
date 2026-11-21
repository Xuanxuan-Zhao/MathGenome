import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.NoncompactTopDegree
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.DoubleCover

/-! Original statements of M11.07 (paper.tex 2503–2510 and 2590–2607).
The complexes are the shared intrinsic complexes of all smooth forms and of
all compactly supported smooth forms. ConnectedSpace includes nonemptiness;
the intrinsic boundary is empty, and either uniform model is permitted.
No covering, descent, properness, or primitive certificate is an assumption.
In degree zero exactness uses the zero submodule, as in the upstream Specs. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.DeRham.TopDegree
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.DeRhamData _root_.SmoothManifolds.CompactSupportData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.BoundaryData
universe u

/-- Every compactly supported top form on a connected nonorientable manifold
is exact in the compact complex; its actual compact quotient vanishes. -/
def nonorientable_compact_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ¬ Nonempty (Orientation S) →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (D : CompactCalculus K ⊤),
      (∀ ω : D.complex.Obj n, ω ∈ D.complex.exact n) ∧
        Subsingleton (D.Cohomology n)

/-- Ordinary vanishing on every connected noncompact manifold, with no
orientability assumption and no support restriction on its primitive. -/
def noncompactType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ¬ IsCompact (Set.univ : Set M) →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      (∀ ω : K.forms n, ω ∈ K.exact n) ∧ Subsingleton (K.Cohomology n)

/-- The remaining compact ordinary case, using equality of the full complexes. -/
def compact_nonorientableType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M] [CompactSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ¬ Nonempty (Orientation S) →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      (∀ ω : K.forms n, ω ∈ K.exact n) ∧ Subsingleton (K.Cohomology n)

/-- All clauses of the original theorem, with the integral representative
formulas, compact comparison, exactness criterion and signed dimension-zero
case retained from the oriented interfaces. -/
def full_top_degreeType : Prop :=
  OrientedTopDegree.top_degreeType.{u} ∧
  OrientedTopDegree.exact_iff_integral_zeroType.{u} ∧
  OrientedTopDegree.compact_comparisonType.{u} ∧
  OrientedTopDegree.compact_top_degreeType.{u} ∧
  OrientedTopDegree.zero_dimensionType.{u} ∧
  noncompactType.{u} ∧ nonorientable_compact_supportType.{u} ∧
  compact_nonorientableType.{u}

end Specs.SmoothManifolds.DeRham.TopDegree
