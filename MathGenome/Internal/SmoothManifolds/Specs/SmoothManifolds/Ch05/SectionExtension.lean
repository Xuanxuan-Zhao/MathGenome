import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SubmanifoldExtension

/-! M05.02, paper.tex 1277–1284. No neatness or boundarylessness hypothesis
is imposed on the embedded source or ambient manifold. -/
namespace SmoothManifolds.SectionExtensionData
open ModelData AtlasData MapData BundleData Bundle Set
universe u v w z
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- Smoothness is tested on the actual map into the bundle total manifold. -/
def SmoothSection (s : (p : M) → E p) : Prop :=
  ManifoldSmooth S.smoothStructure.val B.totalManifold.smoothStructure.val
    (fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E))

/-- Local sections have their actual open domains; no extension is assumed. -/
def LocallyExtendable (A U : Set M) (s : (p : A) → E p.val) : Prop :=
  ∀ p : A, ∃ (V : Set M) (hV : IsOpen V), p.val ∈ V ∧ V ⊆ U ∧
    ∃ t : (q : V) → E q.val,
      ManifoldSmooth (openSubsetAtlas S.smoothStructure.val V hV)
        B.totalManifold.smoothStructure.val
        (fun q => (⟨q.val, t q⟩ : TotalSpace (Euclidean r) E)) ∧
      ∀ (q : A) (hq : q.val ∈ V), t ⟨q.val, hq⟩ = s q
end SmoothManifolds.SectionExtensionData

namespace Specs.SmoothManifolds.Ch05.SectionExtension
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.BundleData
  _root_.SmoothManifolds.SectionExtensionData _root_.SmoothManifolds.MapClassData Bundle Set
universe u v w z

def closed_extensionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E)
    (A : Set M), IsClosed A → ∀ s : (p : A) → E p.val,
    LocallyExtendable B A univ s →
    ∃ t : (p : M) → E p, SmoothSection B t ∧ ∀ p : A, t p.val = s p

def supported_extensionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E)
    (A U : Set M), IsClosed A → IsOpen U → A ⊆ U →
    ∀ s : (p : A) → E p.val, LocallyExtendable B A U s →
    ∃ t : (p : M) → E p, SmoothSection B t ∧
      (∀ p : A, t p.val = s p) ∧ sectionSupport t ⊆ U

/-- Each frame member can be realized by a global section on a neighborhood
of any chosen point of the frame domain. -/
def frame_member_extensionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E)
    (U : Set M) (hU : IsOpen U) (b : LocalFrame B U hU) (p : U) (j : Fin r),
    ∃ t : (q : M) → E q, SmoothSection B t ∧ sectionSupport t ⊆ U ∧
      ∃ V : Set M, IsOpen V ∧ p.val ∈ V ∧ V ⊆ U ∧
        ∀ (q : U), q.val ∈ V → t q.val = b.section_ j q

/-- Smooth sections along an embedding extend locally, with an actual open
ambient neighborhood cutting out all source points in that neighborhood. -/
def embedded_local_extensionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E)
    {m : ℕ} {b : ModelKind} {N : Type z} [TopologicalSpace N]
    (T : SmoothManifold m b N) (f : N → M), IsSmoothEmbedding T S f →
    ∀ s : (p : N) → E (f p),
    ManifoldSmooth T.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨f p, s p⟩ : TotalSpace (Euclidean r) E)) →
    ∀ p : N, ∃ (V : Set M) (hV : IsOpen V), f p ∈ V ∧
      ∃ t : (q : V) → E q.val,
        ManifoldSmooth (openSubsetAtlas S.smoothStructure.val V hV)
          B.totalManifold.smoothStructure.val
          (fun q => (⟨q.val, t q⟩ : TotalSpace (Euclidean r) E)) ∧
        ∀ (q : N) (hq : f q ∈ V), t ⟨f q, hq⟩ = s q

/-- General embedding formulation includes the inclusion of every closed
embedded submanifold with its given smooth structure. -/
def embedded_supported_extensionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E)
    {m : ℕ} {b : ModelKind} {N : Type z} [TopologicalSpace N]
    (T : SmoothManifold m b N) (f : N → M), IsSmoothEmbedding T S f →
    IsClosed (range f) → ∀ (U : Set M), IsOpen U → range f ⊆ U →
    ∀ s : (p : N) → E (f p),
    ManifoldSmooth T.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨f p, s p⟩ : TotalSpace (Euclidean r) E)) →
    ∃ t : (p : M) → E p, SmoothSection B t ∧
      (∀ p : N, t (f p) = s p) ∧ sectionSupport t ⊆ U

/-- The inclusion formulation for an actual closed embedded submanifold. -/
def submanifold_supported_extensionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) {m : ℕ} {b : ModelKind}
    (A : Set M) (T : SmoothManifold m b A),
    IsSmoothEmbedding T S Subtype.val → IsClosed A →
    ∀ (U : Set M), IsOpen U → A ⊆ U → ∀ s : (p : A) → E p.val,
    ManifoldSmooth T.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p.val, s p⟩ : TotalSpace (Euclidean r) E)) →
    ∃ t : (p : M) → E p, SmoothSection B t ∧
      (∀ p : A, t p.val = s p) ∧ sectionSupport t ⊆ U

end Specs.SmoothManifolds.Ch05.SectionExtension
