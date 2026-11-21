import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Algebra

/-! M11.03, paper.tex 2274–2318. Independent definitions for the algebraic
connecting construction and its geometric realization on an open cover.
The sign is q(a,b)=b-a. A realization must contain ALL smooth restricted
sections, and its differential must agree locally with the intrinsic d. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SmoothManifolds.MayerVietorisData
universe u

/-- Nonnegative cochain complexes of real vector spaces. -/
structure Cochain where
  Obj : ℕ → Type u
  [group : ∀ k, AddCommGroup (Obj k)]
  [module : ∀ k, Module ℝ (Obj k)]
  d : ∀ k, Obj k →ₗ[ℝ] Obj (k+1)
  square : ∀ k x, d (k+1) (d k x) = 0

attribute [instance] Cochain.group Cochain.module

namespace Cochain
variable (A : Cochain.{u})

def closed (k : ℕ) : Submodule ℝ (A.Obj k) := (A.d k).ker

def exact : (k : ℕ) → Submodule ℝ (A.Obj k)
  | 0 => ⊥
  | k+1 => (A.d k).range

def boundaries (k : ℕ) : Submodule ℝ (A.closed k) :=
  (A.exact k).comap (A.closed k).subtype

def H (k : ℕ) := A.closed k ⧸ A.boundaries k

instance hGroup (k : ℕ) : AddCommGroup (A.H k) :=
  Submodule.Quotient.addCommGroup _
instance hModule (k : ℕ) : Module ℝ (A.H k) := Submodule.Quotient.module _

def classOf (k : ℕ) : A.closed k →ₗ[ℝ] A.H k := (A.boundaries k).mkQ

/-- The direct sum of two complexes (a binary product of vector spaces). -/
def prod (B : Cochain.{u}) : Cochain.{u} where
  Obj k := A.Obj k × B.Obj k
  d k := {
    toFun x := (A.d k x.1, B.d k x.2)
    map_add' _ _ := by simp
    map_smul' _ _ := by simp }
  square k x := Prod.ext (A.square k x.1) (B.square k x.2)

end Cochain

/-- A degree-preserving map commuting with the differentials. -/
structure ChainMap (A B : Cochain.{u}) where
  map : ∀ k, A.Obj k →ₗ[ℝ] B.Obj k
  comm : ∀ k x, B.d k (map k x) = map (k+1) (A.d k x)

namespace ChainMap
variable {A B : Cochain.{u}} (f : ChainMap A B)

def onClosed (k : ℕ) : A.closed k →ₗ[ℝ] B.closed k where
  toFun x := ⟨f.map k x.val, by
    change B.d k (f.map k x.val) = 0
    rw [f.comm, show A.d k x.val = 0 from x.property, map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul _ _ _)

def fst (A B : Cochain.{u}) : ChainMap (A.prod B) A where
  map k := LinearMap.fst ℝ (A.Obj k) (B.Obj k)
  comm _ _ := rfl

def snd (A B : Cochain.{u}) : ChainMap (A.prod B) B where
  map k := LinearMap.snd ℝ (A.Obj k) (B.Obj k)
  comm _ _ := rfl

end ChainMap

/-- Degreewise short exactness, including both end conditions. -/
structure ShortExact (A B C : Cochain.{u}) where
  r : ChainMap A B
  q : ChainMap B C
  injective : ∀ k, Function.Injective (r.map k)
  surjective : ∀ k, Function.Surjective (q.map k)
  exact : ∀ k x, q.map k x = 0 ↔ ∃ y, r.map k y = x

/-- The representative formula fixes the sign and characterizes δ uniquely.
It quantifies over EVERY closed representative, lift, and descending form. -/
def IsConnecting {A B C : Cochain.{u}} (E : ShortExact A B C)
    (δ : ∀ k, C.H k →ₗ[ℝ] A.H (k+1)) : Prop :=
  ∀ k (c : C.closed k) (b : B.Obj k) (a : A.closed (k+1)),
    E.q.map k b = c.val → E.r.map (k+1) a.val = B.d k b →
    δ k (C.classOf k c) = A.classOf (k+1) a

/-- A map on cohomology characterized on every closed representative. -/
def IsInduced {A B : Cochain.{u}} (f : ChainMap A B)
    (F : ∀ k, A.H k →ₗ[ℝ] B.H k) : Prop :=
  ∀ k x, F k (A.classOf k x) = B.classOf k (f.onClosed k x)

/-- Exactness at all three positions of every segment of the long sequence.
The initial injectivity states exactness at H⁰(A), since H⁻¹(C)=0. -/
def IsLongExact {A B C : Cochain.{u}} (E : ShortExact A B C)
    (R : ∀ k, A.H k →ₗ[ℝ] B.H k) (Q : ∀ k, B.H k →ₗ[ℝ] C.H k)
    (δ : ∀ k, C.H k →ₗ[ℝ] A.H (k+1)) : Prop :=
  Function.Injective (R 0) ∧
  (∀ k y, Q k y = 0 ↔ ∃ x, R k x = y) ∧
  (∀ k z, δ k z = 0 ↔ ∃ y, Q k y = z) ∧
  (∀ k x, R (k+1) x = 0 ↔ ∃ z, δ k z = x)

/-- A morphism of short exact sequences, oriented in the direction of
pullbacks. No partition or choice of lift is included. -/
structure SequenceMap {A B C A' B' C' : Cochain.{u}}
    (E : ShortExact A B C) (E' : ShortExact A' B' C') where
  left : ChainMap A A'
  middle : ChainMap B B'
  right : ChainMap C C'
  comm_r : ∀ k x, middle.map k (E.r.map k x) = E'.r.map k (left.map k x)
  comm_q : ∀ k x, right.map k (E.q.map k x) = E'.q.map k (middle.map k x)

open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData

/-- Forms over an open subset retain the ambient cotangent fibers. The
canonical identification T(U)=TM|U is thus built into the representation. -/
abbrev RestrictedField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M) (k : ℕ) :=
  (p : U) → Fiber (TangentSpace S p.val) k

/-- Genuine smooth sections of the restricted exterior bundle. -/
def IsRestrictedForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {k : ℕ}
    (B : FormBundle C k) (U : TopologicalSpace.Opens M) (ω : RestrictedField S U k) : Prop :=
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  MapData.ManifoldSmooth (MapData.openSubsetAtlas S.smoothStructure.val U U.isOpen)
    B.space.bundle.totalManifold.smoothStructure.val
    (fun p : U => (⟨p.val, ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
      (fun q => Fiber (TangentSpace S q) k)))

/-- Used only in a germ at a point INSIDE U. No smoothness at its edge is
assumed or inferred from this unrestricted set-theoretic zero extension. -/
def zeroExtend {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {U : TopologicalSpace.Opens M} {k : ℕ}
    (ω : RestrictedField S U k) : Field S k := by
  classical
  exact fun p => if hp : p ∈ U then ω ⟨p, hp⟩ else 0

/-- The intrinsic derivative on U, characterized by the original coordinate
formula at points of U; artificial nonsmoothness outside U is irrelevant. -/
def HasRestrictedDerivative {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (U : TopologicalSpace.Opens M) {k : ℕ}
    (ω : RestrictedField S U k) (η : RestrictedField S U (k+1)) : Prop :=
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : U)
    (hp : p.val ∈ c.source),
    η p = coordinateDerivative C k c hc (zeroExtend ω) p.val hp

/-- Realization on all smooth forms over an open subset, including empty sets
and open subsets meeting the intrinsic boundary. -/
structure OpenCalculus {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (U : TopologicalSpace.Opens M) where
  complex : Cochain.{u}
  field : ∀ k, complex.Obj k →ₗ[ℝ] RestrictedField S U k
  injective : ∀ k, Function.Injective (field k)
  range_smooth : ∀ k ω, IsRestrictedForm (B k) U ω ↔ ∃ x, field k x = ω
  coordinates : ∀ k ω, HasRestrictedDerivative C U (field k ω)
    (field (k+1) (complex.d k ω))

/-- Reuse of the original de Rham quotient data, not a new differential. -/
def globalComplex {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) : Cochain.{u} where
  Obj k := K.forms k
  d := K.d
  square k ω := Subtype.ext (K.axioms.square k ω.val ((K.mem_forms _ _).mp ω.property))

structure OpenCover (M : Type u) [TopologicalSpace M] where
  U : TopologicalSpace.Opens M
  V : TopologicalSpace.Opens M
  cover : ∀ p : M, p ∈ U ∨ p ∈ V

/-- The actual short exact sequence of the given open cover. The equations
fix the restriction maps, and in particular the requested sign of q. -/
structure CoverComplex {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (O : OpenCover M) where
  onU : OpenCalculus C B O.U
  onV : OpenCalculus C B O.V
  onOverlap : OpenCalculus C B (O.U ⊓ O.V)
  sequence : ShortExact (globalComplex K) (onU.complex.prod onV.complex) onOverlap.complex
  restriction_U : ∀ k (ω : K.forms k) (p : O.U), onU.field k (sequence.r.map k ω).1 p = ω.val p.val
  restriction_V : ∀ k (ω : K.forms k) (p : O.V), onV.field k (sequence.r.map k ω).2 p = ω.val p.val
  difference : ∀ k (ω : onU.complex.Obj k × onV.complex.Obj k) (p : ↥(O.U ⊓ O.V)),
    onOverlap.field k (sequence.q.map k ω) p =
      onV.field k ω.2 ⟨p.val, p.property.2⟩ - onU.field k ω.1 ⟨p.val, p.property.1⟩

/-- Subordinate weights and the actual smooth zero-extended lifts. Membership
in the full smooth-section modules supplies smoothness on their whole domains. -/
def HasPartitionLift {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {O : OpenCover M} (D : CoverComplex K O) : Prop :=
  ∃ ρU ρV : M → ℝ,
    PartitionData.ScalarSmooth S.smoothStructure.val ρU ∧
    PartitionData.ScalarSmooth S.smoothStructure.val ρV ∧
    (∀ p, 0 ≤ ρU p ∧ 0 ≤ ρV p ∧ ρU p + ρV p = 1) ∧
    sectionSupport ρU ⊆ O.U ∧ sectionSupport ρV ⊆ O.V ∧
    ∀ k (γ : D.onOverlap.complex.Obj k),
      ∃ a : D.onU.complex.Obj k, ∃ b : D.onV.complex.Obj k,
        (∀ p : O.U, ∀ hp : p.val ∈ O.V,
          D.onU.field k a p = -(ρV p.val • D.onOverlap.field k γ ⟨p.val, p.property, hp⟩)) ∧
        (∀ p : O.U, p.val ∉ O.V → D.onU.field k a p = 0) ∧
        (∀ p : O.V, ∀ hp : p.val ∈ O.U,
          D.onV.field k b p = ρU p.val • D.onOverlap.field k γ ⟨p.val, hp, p.property⟩) ∧
        (∀ p : O.V, p.val ∉ O.U → D.onV.field k b p = 0) ∧
        D.sequence.q.map k (a,b) = γ

/-- A cover-preserving smooth map induces the ACTUAL pullback on each field,
not merely an arbitrary morphism of short exact sequences. -/
structure CoverPullback {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {C : CotangentBundle S} {A : CotangentBundle T}
    {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
    {K : Calculus C B} {J : Calculus A E} {O : OpenCover M} {P : OpenCover N}
    (D : CoverComplex K O) (G : CoverComplex J P) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hU : Set.MapsTo f O.U P.U) (hV : Set.MapsTo f O.V P.V) where
  morphism : SequenceMap G.sequence D.sequence
  global_field : ∀ k (ω : J.forms k), (morphism.left.map k ω).val =
    FormPullbackData.pullbackField S T f L ω.val
  U_field : ∀ k (ω : G.onU.complex.Obj k × G.onV.complex.Obj k) (p : O.U), D.onU.field k (morphism.middle.map k ω).1 p =
    FormPullbackData.fiberPullback (V := TangentSpace S p.val)
      (W := TangentSpace T (f p.val)) k (L p.val) (G.onU.field k ω.1 ⟨f p.val, hU p.property⟩)
  V_field : ∀ k (ω : G.onU.complex.Obj k × G.onV.complex.Obj k) (p : O.V), D.onV.field k (morphism.middle.map k ω).2 p =
    FormPullbackData.fiberPullback (V := TangentSpace S p.val)
      (W := TangentSpace T (f p.val)) k (L p.val) (G.onV.field k ω.2 ⟨f p.val, hV p.property⟩)
  overlap_field : ∀ k (ω : G.onOverlap.complex.Obj k) (p : ↥(O.U ⊓ O.V)), D.onOverlap.field k (morphism.right.map k ω) p =
    FormPullbackData.fiberPullback (V := TangentSpace S p.val)
      (W := TangentSpace T (f p.val)) k (L p.val)
      (G.onOverlap.field k ω ⟨f p.val, hU p.property.1, hV p.property.2⟩)

end SmoothManifolds.MayerVietorisData

namespace Specs.SmoothManifolds.DeRham.MayerVietoris
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.DeRhamData
  _root_.SmoothManifolds.MayerVietorisData
universe u

/-- The cohomology of the middle complex is canonically the direct sum of
the cohomologies, with the specified maps on every representative. -/
def product_cohomologyType : Prop :=
  ∀ (A B : Cochain.{u}) (k : ℕ),
    ∃ e : (A.prod B).H k ≃ₗ[ℝ] (A.H k × B.H k),
      ∀ x, e ((A.prod B).classOf k x) =
        (A.classOf k ((ChainMap.fst A B).onClosed k x),
         B.classOf k ((ChainMap.snd A B).onClosed k x))

/-- The geometric existence assertion has exactly the original hypotheses.
The global and all three restricted de Rham complexes are conclusions. -/
def cover_sequence_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (O : OpenCover M),
    ∃ K : Calculus C B, ∃ D : CoverComplex K O, HasPartitionLift D

/-- The connecting construction and independence are stated more generally
for every short exact sequence of real cochain complexes. -/
def connecting_existsType : Prop :=
  ∀ (A B C : Cochain.{u}) (E : ShortExact A B C),
    ∃! δ : ∀ k, C.H k →ₗ[ℝ] A.H (k+1), IsConnecting E δ

def induced_existsType : Prop :=
  ∀ (A B : Cochain.{u}) (f : ChainMap A B),
    ∃! F : ∀ k, A.H k →ₗ[ℝ] B.H k, IsInduced f F

/-- All positions, and the left end, in the long exact sequence. -/
def long_exactType : Prop :=
  ∀ (A B C : Cochain.{u}) (E : ShortExact A B C)
    (R : ∀ k, A.H k →ₗ[ℝ] B.H k) (Q : ∀ k, B.H k →ₗ[ℝ] C.H k)
    (δ : ∀ k, C.H k →ₗ[ℝ] A.H (k+1)),
    IsInduced E.r R → IsInduced E.q Q → IsConnecting E δ → IsLongExact E R Q δ

/-- Pullbacks on every open-cover sequence have the specified underlying fields. -/
def cover_pullback_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E) (O : OpenCover M) (P : OpenCover N)
    (D : CoverComplex K O) (G : CoverComplex J P)
    (f : M → N), MapData.IsSmoothMap S T f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    ∀ (hU : Set.MapsTo f O.U P.U) (hV : Set.MapsTo f O.V P.V),
    Nonempty (CoverPullback D G f L hU hV)

/-- Naturality for every morphism of short exact sequences, hence in particular
for every smooth cover-preserving map by cover_pullback_exists. -/
def naturalityType : Prop :=
  ∀ (A B C A' B' C' : Cochain.{u}) (E : ShortExact A B C) (E' : ShortExact A' B' C')
    (F : SequenceMap E E')
    (δ : ∀ k, C.H k →ₗ[ℝ] A.H (k+1))
    (δ' : ∀ k, C'.H k →ₗ[ℝ] A'.H (k+1))
    (FA : ∀ k, A.H k →ₗ[ℝ] A'.H k)
    (FB : ∀ k, B.H k →ₗ[ℝ] B'.H k)
    (FC : ∀ k, C.H k →ₗ[ℝ] C'.H k)
    (R : ∀ k, A.H k →ₗ[ℝ] B.H k) (Q : ∀ k, B.H k →ₗ[ℝ] C.H k)
    (R' : ∀ k, A'.H k →ₗ[ℝ] B'.H k) (Q' : ∀ k, B'.H k →ₗ[ℝ] C'.H k),
    IsConnecting E δ → IsConnecting E' δ' →
    IsInduced F.left FA → IsInduced F.middle FB → IsInduced F.right FC →
    IsInduced E.r R → IsInduced E.q Q → IsInduced E'.r R' → IsInduced E'.q Q' →
    (∀ k x, FB k (R k x) = R' k (FA k x)) ∧
    (∀ k y, FC k (Q k y) = Q' k (FB k y)) ∧
    (∀ k z, FA (k+1) (δ k z) = δ' k (FC k z))

end Specs.SmoothManifolds.DeRham.MayerVietoris
