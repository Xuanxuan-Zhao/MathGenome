import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleGluing

/-! Independent statement of the globalization step in M05.08.
The topology and atlas are those of the supplied bundle, with its prescribed fibers. -/
namespace Specs.SmoothManifolds.Ch05.BundleTubularGlobalization
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.BundleData Bundle Set Topology
universe u v w z

/-- Globalize local smooth inverse data near an embedded zero section, retaining
an open fiberwise star-shaped domain. No closed-image or compactness premise. -/
def bundle_tubular_globalizationType : Prop :=
  ∀ {d r n : ℕ} {P : Type u} {M : Type v}
    [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold d .euclidean P) (S : SmoothManifold n .euclidean M)
    {ι : Type w} {E : P → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle T r ι E) (i : P → M)
    (O : Set (TotalSpace (Euclidean r) E)) (F : TotalSpace (Euclidean r) E → M),
    IsEmbedding i → IsOpen O →
    (∀ p, (⟨p, 0⟩ : TotalSpace (Euclidean r) E) ∈ O) →
    (∀ p, F (⟨p, 0⟩ : TotalSpace (Euclidean r) E) = i p) →
    ManifoldSmoothOn B.totalManifold.smoothStructure.val S.smoothStructure.val F O →
    (∀ x ∈ O, ∃ e : OpenPartialHomeomorph (TotalSpace (Euclidean r) E) M,
      x ∈ e.source ∧ e.source ⊆ O ∧ EqOn e F e.source ∧
      ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
        e.symm e.target) →
    ∃ (V : Set (TotalSpace (Euclidean r) E)) (W : Set M)
      (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W),
      V ⊆ O ∧ (∀ p, (⟨p, 0⟩ : TotalSpace (Euclidean r) E) ∈ V) ∧
      range i ⊆ W ∧ (∀ x : V, (h x).val = F x.val) ∧
      ManifoldSmooth (openSubsetAtlas B.totalManifold.smoothStructure.val V hV)
        (openSubsetAtlas S.smoothStructure.val W hW) h ∧
      ManifoldSmooth (openSubsetAtlas S.smoothStructure.val W hW)
        (openSubsetAtlas B.totalManifold.smoothStructure.val V hV) h.symm ∧
      (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
        (⟨x.proj, t • x.snd⟩ : TotalSpace (Euclidean r) E) ∈ V)

end Specs.SmoothManifolds.Ch05.BundleTubularGlobalization
