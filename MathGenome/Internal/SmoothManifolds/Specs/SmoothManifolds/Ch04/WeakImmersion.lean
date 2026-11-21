import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.GoodProjections

/-! The immersion clause of paper.tex, Theorem M04.03.
The shared Euclidean immersion predicate requires smooth ambient local
extensions and injectivity of their full derivatives in every source chart.
Both ordinary model kinds are allowed, with no compactness, nonemptiness,
connectedness or positive-dimension hypothesis. In dimension zero the target
is a point; injectivity of the map itself is not required. -/
namespace Specs.SmoothManifolds.Ch04.WeakImmersion
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.GoodProjectionData
universe u

def exists_immersionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
    ∃ f : M → Euclidean (2 * n), IsEuclideanImmersion S f

end Specs.SmoothManifolds.Ch04.WeakImmersion
