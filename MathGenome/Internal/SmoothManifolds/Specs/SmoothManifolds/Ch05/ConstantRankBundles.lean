import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Frames
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Independent definitions and obligations for the kernel/image clauses of
paper.tex, M05.03, lines 1286–1295. The quotient clause is a separate goal.

A smooth subbundle is expressed by adapted smooth local frames of its ambient
bundle. Thus its local trivializations are restrictions of actual smooth
ambient frame maps, not merely unrelated algebraic bases in the fibers.
-/
namespace SmoothManifolds.ConstantRankData
open ModelData AtlasData MapData BundleData FrameData Bundle Set
universe u v w z t

section Bundles
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean s) F)]

/-- A morphism over the identity, with smoothness of its actual total-space map.
There is no rank or local normal-form certificate among the fields. -/
structure SmoothBundleMorphism (B : SmoothVectorBundle S r ι E)
    (D : SmoothVectorBundle S s κ F) where
  linearMap : (p : M) → E p →ₗ[ℝ] F p
  smooth : IsSmoothMap B.totalManifold D.totalManifold
    (fun q => (⟨q.proj, linearMap q.proj q.snd⟩ : TotalSpace (Euclidean s) F))

/-- The first k coordinates in an adapted smooth ambient frame describe K.
This gives local smooth subbundle charts, including k=0 and k=r. -/
def IsSmoothSubbundle (B : SmoothVectorBundle S r ι E) (k : ℕ)
    (K : (p : M) → Submodule ℝ (E p)) : Prop :=
  ∀ p : M, k ≤ r ∧ ∃ U : Set M, ∃ hU : IsOpen U, p ∈ U ∧
    ∃ b : LocalFrame B U hU, ∀ (q : U) (v : E q.val),
      v ∈ K q.val ↔ ∀ j : Fin r, k ≤ j.val → (b.basis q).equivFun v j = 0

end Bundles
end SmoothManifolds.ConstantRankData

namespace Specs.SmoothManifolds.Ch05.ConstantRankBundles
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BundleData _root_.SmoothManifolds.FrameData
  _root_.SmoothManifolds.ConstantRankData Bundle Set Module
universe u v w z t

/-- Public aliases use the same canonical bundle objects as all later Specs. -/
def SmoothBundleMorphismType :=
  {n r s : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → {ι : Type v} → {κ : Type t} →
  {E : M → Type w} → {F : M → Type z} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [∀ p, AddCommGroup (F p)] → [∀ p, Module ℝ (F p)] →
  [TopologicalSpace (TotalSpace (Euclidean r) E)] →
  [TopologicalSpace (TotalSpace (Euclidean s) F)] →
  SmoothVectorBundle S r ι E → SmoothVectorBundle S s κ F → Type (max u w z)

def SmoothBundleMorphismValue : SmoothBundleMorphismType := @ConstantRankData.SmoothBundleMorphism

def IsSmoothSubbundleType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (TotalSpace (Euclidean r) E)] →
  SmoothVectorBundle S r ι E → ℕ → ((p : M) → Submodule ℝ (E p)) → Prop

def IsSmoothSubbundleValue : IsSmoothSubbundleType := @ConstantRankData.IsSmoothSubbundle

/-- No positivity, connectedness or nonemptiness assumption is imposed.
The rank hypothesis concerns every fiber of this morphism. -/
def kernel_image_subbundlesType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)
    (A : SmoothBundleMorphism B D) (k : ℕ),
    (∀ p, finrank ℝ (LinearMap.range (A.linearMap p)) = k) →
    IsSmoothSubbundle B (r - k) (fun p => LinearMap.ker (A.linearMap p)) ∧
    IsSmoothSubbundle D k (fun p => LinearMap.range (A.linearMap p)) ∧
    (∀ p, finrank ℝ (LinearMap.ker (A.linearMap p)) = r - k)

/-- The componentwise version is stated for any family of bases, so in
particular for the open connected components of a manifold. Bundle ranks and
morphism ranks depend on the family index; no uniform bound is assumed.
To specialize, take J to be the distinct connected-component subsets, M j the
subtype of that subset, and S j its inherited open-submanifold structure.
Because the components are open, the adapted charts in this conclusion are
also local charts for the componentwise bundle on the original base. -/
def componentwise_kernel_imageType : Prop :=
  ∀ {J : Type*} {n : J → ℕ} {r s : J → ℕ} {a : J → ModelKind}
    {M : J → Type u} [∀ j, TopologicalSpace (M j)]
    {S : (j : J) → SmoothManifold (n j) (a j) (M j)}
    {ι : J → Type v} {κ : J → Type t}
    {E : (j : J) → M j → Type w} {F : (j : J) → M j → Type z}
    [∀ j p, AddCommGroup (E j p)] [∀ j p, Module ℝ (E j p)]
    [∀ j p, AddCommGroup (F j p)] [∀ j p, Module ℝ (F j p)]
    [∀ j, TopologicalSpace (TotalSpace (Euclidean (r j)) (E j))]
    [∀ j, TopologicalSpace (TotalSpace (Euclidean (s j)) (F j))]
    (B : (j : J) → SmoothVectorBundle (S j) (r j) (ι j) (E j))
    (D : (j : J) → SmoothVectorBundle (S j) (s j) (κ j) (F j))
    (A : (j : J) → SmoothBundleMorphism (B j) (D j)) (k : J → ℕ),
    (∀ j p, finrank ℝ (LinearMap.range ((A j).linearMap p)) = k j) →
    ∀ j, IsSmoothSubbundle (B j) (r j - k j)
        (fun p => LinearMap.ker ((A j).linearMap p)) ∧
      IsSmoothSubbundle (D j) (k j) (fun p => LinearMap.range ((A j).linearMap p)) ∧
      (∀ p, finrank ℝ (LinearMap.ker ((A j).linearMap p)) = r j - k j)

/-- Actual specialization to the distinct connected components of the given
base. Openness and the inherited smooth structures are conclusions, rather
than additional hypotheses. All fiber and morphism ranks may vary with c. -/
def components_kernel_imageType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
  let C := ↥(Set.range (connectedComponent (α := M)))
  ∃ hOpen : ∀ c : C, IsOpen c.val,
    ∃ T : (c : C) → SmoothManifold n a c.val,
      (∀ c, (T c).smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val c.val (hOpen c))) ∧
      ∀ {r s : C → ℕ} {ι : C → Type v} {κ : C → Type t}
        {E : (c : C) → c.val → Type w} {F : (c : C) → c.val → Type z}
        [∀ c p, AddCommGroup (E c p)] [∀ c p, Module ℝ (E c p)]
        [∀ c p, AddCommGroup (F c p)] [∀ c p, Module ℝ (F c p)]
        [∀ c, TopologicalSpace (TotalSpace (Euclidean (r c)) (E c))]
        [∀ c, TopologicalSpace (TotalSpace (Euclidean (s c)) (F c))]
        (B : (c : C) → SmoothVectorBundle (T c) (r c) (ι c) (E c))
        (D : (c : C) → SmoothVectorBundle (T c) (s c) (κ c) (F c))
        (A : (c : C) → SmoothBundleMorphism (B c) (D c)) (k : C → ℕ),
        (∀ c p, finrank ℝ (LinearMap.range ((A c).linearMap p)) = k c) →
        ∀ c, IsSmoothSubbundle (B c) (r c - k c)
            (fun p => LinearMap.ker ((A c).linearMap p)) ∧
          IsSmoothSubbundle (D c) (k c) (fun p => LinearMap.range ((A c).linearMap p)) ∧
          (∀ p, finrank ℝ (LinearMap.ker ((A c).linearMap p)) = r c - k c)

end Specs.SmoothManifolds.Ch05.ConstantRankBundles
