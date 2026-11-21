import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.OrientedTopDegree

/-! The ordinary oriented noncompact clause of M11.07, paper.tex:2503–2588.
The smooth forms, derivative, and quotient are the shared intrinsic de Rham
objects. ConnectedSpace includes nonemptiness. Both uniform models are allowed;
empty intrinsic boundary is required separately. Noncompactness is a property
of the whole manifold, not a condition on the support of a representative.

Membership in `K.exact n` means existence of an unrestricted smooth primitive
in positive dimension. In dimension zero the exact space is zero; the manifold
hypotheses in this case are inconsistent. The second conclusion records the
vanishing of the actual ordinary quotient. No exhaustion or transfer data is
an additional hypothesis of this statement. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.DeRham.NoncompactTopDegree
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.DeRhamData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.BoundaryData
universe u

def top_degreeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ∀ (o : Orientation S), ¬ IsCompact (Set.univ : Set M) →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B),
      (∀ ω : K.forms n, ω ∈ K.exact n) ∧ Subsingleton (K.Cohomology n)

end Specs.SmoothManifolds.DeRham.NoncompactTopDegree
