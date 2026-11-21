import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.MayerVietoris

/-! M11.05, paper.tex 2426–2457. Compact supports are closed supports in
 the base. An open compact complex is represented by its extension in the
 ambient manifold; `zero_extensionType` supplies the bridge from ALL compactly
 supported smooth restricted sections. No arbitrary-map pullback is asserted. -/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.CompactSupportData
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData
universe u

/-- The full compact-support subcomplex on U, realized inside the original
 global smooth forms. `range` excludes smaller spaces of test forms. -/
structure CompactCalculus {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (U : TopologicalSpace.Opens M) where
  complex : Cochain.{u}
  inclusion : ChainMap complex (globalComplex K)
  injective : ∀ k, Function.Injective (inclusion.map k)
  range : ∀ k (ω : K.forms k),
    (IsCompact (sectionSupport ω.val) ∧ sectionSupport ω.val ⊆ U) ↔
      ∃ x, inclusion.map k x = ω

/-- Cohomology uses the same differential through `inclusion.comm`. -/
abbrev CompactCalculus.Cohomology {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {U : TopologicalSpace.Opens M} (D : CompactCalculus K U)
    (k : ℕ) := D.complex.H k

/-- Extending a compact form from a smaller open set retains its ambient
 section. This formula specifies extension, rather than restriction. -/
def IsExtension {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {U V : TopologicalSpace.Opens M}
    (D : CompactCalculus K U) (E : CompactCalculus K V)
    (f : ChainMap D.complex E.complex) : Prop :=
  ∀ k x, E.inclusion.map k (f.map k x) = D.inclusion.map k x

/-- The geometric short exact sequence with the two prescribed signs. -/
structure CoverSequence {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (O : OpenCover M) where
  global : CompactCalculus K ⊤
  onU : CompactCalculus K O.U
  onV : CompactCalculus K O.V
  overlap : CompactCalculus K (O.U ⊓ O.V)
  sequence : ShortExact overlap.complex (onU.complex.prod onV.complex) global.complex
  first_U : ∀ k x, onU.inclusion.map k (sequence.r.map k x).1 = overlap.inclusion.map k x
  first_V : ∀ k x, onV.inclusion.map k (sequence.r.map k x).2 = -overlap.inclusion.map k x
  sum : ∀ k x, global.inclusion.map k (sequence.q.map k x) =
    onU.inclusion.map k x.1 + onV.inclusion.map k x.2

/-- Actual smooth proper pullback on complexes and on every cohomology
 representative; no natural partition or arbitrary smooth pullback is assumed. -/
structure ProperPullback {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {C : CotangentBundle S} {A : CotangentBundle T}
    {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
    {K : Calculus C B} {J : Calculus A E}
    (D : CompactCalculus K ⊤) (G : CompactCalculus J ⊤) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) where
  chain : ChainMap G.complex D.complex
  field : ∀ k x, (D.inclusion.map k (chain.map k x)).val =
    FormPullbackData.pullbackField S T f L (G.inclusion.map k x).val
  induced : ∀ k, G.Cohomology k →ₗ[ℝ] D.Cohomology k
  representatives : IsInduced chain induced

end SmoothManifolds.CompactSupportData

namespace Specs.SmoothManifolds.DeRham.CompactSupport
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.DeRhamData _root_.SmoothManifolds.MayerVietorisData
  _root_.SmoothManifolds.CompactSupportData
universe u

/-- d does not enlarge the closed support. -/
def differential_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (k : ℕ) (ω : K.forms k),
    sectionSupport (K.d k ω).val ⊆ sectionSupport ω.val

/-- Includes global existence, with the original manifold hypotheses. -/
def complex_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k),
    ∃ K : Calculus C B, Nonempty (CompactCalculus K ⊤)

/-- Every existing intrinsic calculus has the full compact subcomplex on
 every open set, including empty sets and sets meeting the boundary. -/
def open_complex_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (U : TopologicalSpace.Opens M), Nonempty (CompactCalculus K U)

/-- Smooth zero extension, together with its exact closed support and compactness.
 The compact support hypothesis is in the open submanifold's topology. -/
def zero_extensionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {k : ℕ}
    (B : FormBundle C k) (U : TopologicalSpace.Opens M) (ω : RestrictedField S U k),
    IsRestrictedForm B U ω → IsCompact (sectionSupport ω) →
    IsForm B (zeroExtend ω) ∧ IsCompact (sectionSupport (zeroExtend ω)) ∧
      sectionSupport (zeroExtend ω) = Subtype.val '' sectionSupport ω

def extension_derivativeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (U : TopologicalSpace.Opens M) (k : ℕ)
    (ω : RestrictedField S U k) (η : RestrictedField S U (k+1)),
    IsRestrictedForm (B k) U ω → IsCompact (sectionSupport ω) →
    HasRestrictedDerivative C U ω η → K.D k (zeroExtend ω) = zeroExtend η

def extension_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {U V : TopologicalSpace.Opens M}, U ≤ V →
    ∀ (D : CompactCalculus K U) (E : CompactCalculus K V),
      ∃ f : ChainMap D.complex E.complex, IsExtension D E f ∧
        ∀ k, Function.Injective (f.map k)

def proper_pullbackType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (D : CompactCalculus K ⊤) (G : CompactCalculus J ⊤)
    (f : M → N), MapData.IsSmoothMap S T f → IsProperMap f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
      (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
        Nonempty (ProperPullback D G f L)

def cover_sequence_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (O : OpenCover M), Nonempty (CoverSequence K O)

/-- Every segment and the degree-zero endpoint, with the closed-lift formula
 for the connecting map and the canonical middle direct-sum identification. -/
def long_exactType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {O : OpenCover M} (D : CoverSequence K O),
    ∃ R : ∀ k, D.overlap.Cohomology k →ₗ[ℝ] (D.onU.complex.prod D.onV.complex).H k,
    ∃ Q : ∀ k, (D.onU.complex.prod D.onV.complex).H k →ₗ[ℝ] D.global.Cohomology k,
    ∃ δ : ∀ k, D.global.Cohomology k →ₗ[ℝ] D.overlap.Cohomology (k+1),
      IsInduced D.sequence.r R ∧ IsInduced D.sequence.q Q ∧
      IsConnecting D.sequence δ ∧ IsLongExact D.sequence R Q δ ∧
      ∀ k, ∃ e : (D.onU.complex.prod D.onV.complex).H k ≃ₗ[ℝ]
          (D.onU.Cohomology k × D.onV.Cohomology k),
        ∀ x, e ((D.onU.complex.prod D.onV.complex).classOf k x) =
          (D.onU.complex.classOf k ((ChainMap.fst _ _).onClosed k x),
           D.onV.complex.classOf k ((ChainMap.snd _ _).onClosed k x))

/-- The ambient realization is exactly ALL compactly supported smooth forms
 on U, in both directions, with equality of every restricted fiber value. -/
def open_forms_iffType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {U : TopologicalSpace.Opens M} (D : CompactCalculus K U)
    (k : ℕ) (ω : RestrictedField S U k),
    (IsRestrictedForm (B k) U ω ∧ IsCompact (sectionSupport ω)) ↔
      ∃ x : D.complex.Obj k, ∀ p : U, (D.inclusion.map k x).val p.val = ω p

end Specs.SmoothManifolds.DeRham.CompactSupport
