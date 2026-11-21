import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleGluing

/-! M05.02, coefficient test and frame/trivialization equivalence.
The extension part of M05.02 is allocated to SectionExtension. -/
namespace SmoothManifolds.FrameData
open ModelData AtlasData MapData ProductData BundleData Bundle Set Filter
open scoped Topology
universe u v w z

/-- Vector-valued smoothness in an atlas, with actual ambient smooth extensions.
This also applies to scalar functions and to restricted atlases. -/
def VectorSmoothAt {n : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    (A : Set (ModelChart n a X)) {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X → V) (x : X) : Prop :=
  ContinuousAt f x ∧ ∀ c ∈ A, x ∈ c.source →
    ∃ W : Set (Euclidean n), IsOpen W ∧ (c x).val ∈ W ∧
      ∃ F : Euclidean n → V, ContDiffOn ℝ (⊤ : ℕ∞) F W ∧
        (fun y => F (c y).val) =ᶠ[𝓝 x] f

def VectorSmooth {n : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    (A : Set (ModelChart n a X)) {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X → V) : Prop := ∀ x, VectorSmoothAt A f x

section Bundle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- Standard product atlas on the trivial bundle, with the same ambient product
coordinates as B. This uses the ordinary model, including a base boundary. -/
def trivialAtlas := productAtlas B.coordinates S.smoothStructure.val {fiberChart r}

/-- Smooth triviality means a fiberwise linear isomorphism with M × R^r,
whose actual maps in both directions are smooth. -/
structure SmoothTrivialization where
  coordinates : (p : M) → E p ≃ₗ[ℝ] Euclidean r
  smooth_forward : ManifoldSmooth B.totalManifold.smoothStructure.val (trivialAtlas B)
    (fun q : TotalSpace (Euclidean r) E => (q.proj, coordinates q.proj q.snd))
  smooth_inverse : ManifoldSmooth (trivialAtlas B) B.totalManifold.smoothStructure.val
    (fun q : M × Euclidean r => (⟨q.1, (coordinates q.1).symm q.2⟩ : TotalSpace (Euclidean r) E))

def SmoothlyTrivial : Prop := Nonempty (SmoothTrivialization B)

variable {B} {U : Set M} {hU : IsOpen U}

/-- The unique coefficient vector in the given ordered frame. -/
noncomputable def coefficients (b : LocalFrame B U hU) (s : (p : U) → E p.val)
    (p : U) : Euclidean r := (b.basis p).equivFun (s p)

/-- The fiberwise linear synthesis isomorphism associated to a frame. -/
noncomputable def frameLinearEquiv (b : LocalFrame B U hU) (p : U) :
    Euclidean r ≃ₗ[ℝ] E p.val := (b.basis p).equivFun.symm

/-- Junk values outside U do not enter any smoothness assertion. -/
noncomputable def frameSynthesis (b : LocalFrame B U hU) (q : M × Euclidean r) :
    TotalSpace (Euclidean r) E :=
  by
    classical
    exact ⟨q.1, if h : q.1 ∈ U then frameLinearEquiv b ⟨q.1, h⟩ q.2 else 0⟩

noncomputable def frameAnalysis (b : LocalFrame B U hU) (q : TotalSpace (Euclidean r) E) :
    M × Euclidean r :=
  by
    classical
    exact (q.proj, if h : q.proj ∈ U then (frameLinearEquiv b ⟨q.proj, h⟩).symm q.snd else 0)

end Bundle
end SmoothManifolds.FrameData

namespace Specs.SmoothManifolds.Ch05.Frames
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.ProductData _root_.SmoothManifolds.BundleData
  _root_.SmoothManifolds.FrameData Bundle Set
universe u v w

/-- Public names are transparent aliases of these independent canonical objects. -/
def VectorSmoothAtType :=
  {n : ℕ} → {a : ModelKind} → {X : Type u} → [TopologicalSpace X] →
    Set (ModelChart n a X) → {V : Type v} → [NormedAddCommGroup V] → [NormedSpace ℝ V] →
      (X → V) → X → Prop

def VectorSmoothAtValue : VectorSmoothAtType := @FrameData.VectorSmoothAt

def VectorSmoothType :=
  {n : ℕ} → {a : ModelKind} → {X : Type u} → [TopologicalSpace X] →
    Set (ModelChart n a X) → {V : Type v} → [NormedAddCommGroup V] → [NormedSpace ℝ V] →
      (X → V) → Prop

def VectorSmoothValue : VectorSmoothType := @FrameData.VectorSmooth

def trivialAtlasType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
      [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
      [TopologicalSpace (TotalSpace (Euclidean r) E)] → SmoothVectorBundle S r ι E →
        Set (ModelChart (n + r) (productKind n a r .euclidean) (M × Euclidean r))

def trivialAtlasValue : trivialAtlasType := @FrameData.trivialAtlas

def SmoothTrivializationType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
      [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
      [TopologicalSpace (TotalSpace (Euclidean r) E)] → SmoothVectorBundle S r ι E → Type (max u w)

def SmoothTrivializationValue : SmoothTrivializationType := @FrameData.SmoothTrivialization

def SmoothlyTrivialType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
      [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
      [TopologicalSpace (TotalSpace (Euclidean r) E)] → SmoothVectorBundle S r ι E → Prop

def SmoothlyTrivialValue : SmoothlyTrivialType := @FrameData.SmoothlyTrivial

def coefficientsType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
      [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
      [TopologicalSpace (TotalSpace (Euclidean r) E)] → {B : SmoothVectorBundle S r ι E} →
        {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU → ((p : U) → E p.val) →
          U → Euclidean r

noncomputable def coefficientsValue : coefficientsType := @FrameData.coefficients

def frameLinearEquivType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
      [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
      [TopologicalSpace (TotalSpace (Euclidean r) E)] → {B : SmoothVectorBundle S r ι E} →
        {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU →
          (p : U) → Euclidean r ≃ₗ[ℝ] E p.val

noncomputable def frameLinearEquivValue : frameLinearEquivType := @FrameData.frameLinearEquiv

def frameSynthesisType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
      [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
      [TopologicalSpace (TotalSpace (Euclidean r) E)] → {B : SmoothVectorBundle S r ι E} →
        {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU →
          M × Euclidean r → TotalSpace (Euclidean r) E

noncomputable def frameSynthesisValue : frameSynthesisType := @FrameData.frameSynthesis

def frameAnalysisType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
      [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
      [TopologicalSpace (TotalSpace (Euclidean r) E)] → {B : SmoothVectorBundle S r ι E} →
        {U : Set M} → {hU : IsOpen U} → LocalFrame B U hU →
          TotalSpace (Euclidean r) E → M × Euclidean r

noncomputable def frameAnalysisValue : frameAnalysisType := @FrameData.frameAnalysis

section Bundle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]

/-- No continuity of the section is assumed. Coefficients are actual scalar
functions on U, smooth in the restricted atlas. -/
def smooth_section_iff_coefficientsType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (U : Set M) (hU : IsOpen U)
    (b : LocalFrame B U hU) (s : (p : U) → E p.val),
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, s p⟩ : TotalSpace (Euclidean r) E)) ↔
    ∀ j : Fin r, VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (fun p => coefficients b s p j)

/-- The exact finite expansion, including the empty sum at rank zero. -/
def section_expansionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (U : Set M) (hU : IsOpen U)
    (b : LocalFrame B U hU) (s : (p : U) → E p.val) (p : U),
    s p = ∑ j : Fin r, coefficients b s p j • b.section_ j p

/-- Fiberwise linear inverse maps, smooth on their actual open domains. -/
def frame_mapsType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (U : Set M) (hU : IsOpen U)
    (b : LocalFrame B U hU),
    (∀ p : U, ∀ v : Euclidean r,
      frameLinearEquiv b p v = ∑ j : Fin r, v j • b.section_ j p) ∧
    ManifoldSmoothOn B.totalManifold.smoothStructure.val (trivialAtlas B)
      (frameAnalysis b) {q | q.proj ∈ U} ∧
    ManifoldSmoothOn (trivialAtlas B) B.totalManifold.smoothStructure.val
      (frameSynthesis b) (U ×ˢ univ) ∧
    (∀ q : M × Euclidean r, q.1 ∈ U → frameAnalysis b (frameSynthesis b q) = q) ∧
    (∀ q : TotalSpace (Euclidean r) E, q.proj ∈ U →
      frameSynthesis b (frameAnalysis b q) = q)

/-- Both existential directions, with no positive rank or nonempty base premise. -/
def smoothlyTrivial_iff_globalFrameType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ B : SmoothVectorBundle S r ι E,
    SmoothlyTrivial B ↔ Nonempty (LocalFrame B univ isOpen_univ)

/-- A specified frame itself supplies the smooth trivialization, preserving
its actual coefficient and synthesis maps. -/
def globalFrame_trivializationType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (b : LocalFrame B univ isOpen_univ),
    ∃ t : SmoothTrivialization B, ∀ p : M,
      t.coordinates p = (frameLinearEquiv b ⟨p, mem_univ p⟩).symm

/-- Conversely the frame consists of the inverse images of the standard basis. -/
def trivialization_globalFrameType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (t : SmoothTrivialization B),
    ∃ b : LocalFrame B univ isOpen_univ,
      ∀ (p : M) (j : Fin r), b.section_ j ⟨p, mem_univ p⟩ =
        (t.coordinates p).symm (Pi.single j 1)

end Bundle

/-- Rank-zero fibers consist only of zero and the empty frame is smooth.
In particular the rank-zero bundle is smoothly trivial. -/
def rankZeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean 0) E)]
    (B : SmoothVectorBundle S 0 ι E),
    (∀ p (v : E p), v = 0) ∧ Nonempty (LocalFrame B univ isOpen_univ) ∧ SmoothlyTrivial B

end Specs.SmoothManifolds.Ch05.Frames
