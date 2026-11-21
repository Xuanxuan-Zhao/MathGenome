import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.CompactSupport
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.MayerVietoris
/-! Conditional M11.05. The ordinary targets remain reserved for later
 closure with the actual Mayer–Vietoris proofs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
noncomputable section

namespace SmoothManifolds.CompactSupportResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData Set Filter
open scoped Topology
universe u

/-- Closed support of a sum is contained in the union of the closed supports. -/
theorem support_add_subset {X : Type*} [TopologicalSpace X] {E : X → Type*}
    [∀ p, AddCommGroup (E p)] (f g : ∀ p, E p) :
    ModelData.sectionSupport (f+g) ⊆ ModelData.sectionSupport f ∪ ModelData.sectionSupport g := by
  apply closure_minimal _ (isClosed_closure.union isClosed_closure)
  intro p hp
  by_cases hf : f p = 0
  · exact Or.inr (subset_closure (by simpa [hf] using hp))
  · exact Or.inl (subset_closure hf)

theorem support_smul_subset {X : Type*} [TopologicalSpace X] {E : X → Type*}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)] (r : ℝ) (f : ∀ p, E p) :
    ModelData.sectionSupport (r • f) ⊆ ModelData.sectionSupport f := by
  apply closure_mono
  intro p hp hf
  exact hp (by simp [hf])

theorem support_function_smul_subset {X : Type*} [TopologicalSpace X] {E : X → Type*}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)] (r : X → ℝ) (f : ∀ p, E p) :
    ModelData.sectionSupport (fun p => r p • f p) ⊆ ModelData.sectionSupport r ∩ ModelData.sectionSupport f := by
  apply closure_minimal _ (isClosed_closure.inter isClosed_closure)
  intro p hp
  exact ⟨subset_closure (fun h => hp (by simp [h])),
    subset_closure (fun h => hp (by simp [h]))⟩

section Supported
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}

/-- Concrete full space of ambient smooth forms with compact support inside U. -/
def supportedForms (K : Calculus C B) (U : TopologicalSpace.Opens M) (k : ℕ) :
    Submodule ℝ (K.forms k) where
  carrier := {ω | IsCompact (ModelData.sectionSupport ω.val) ∧ ModelData.sectionSupport ω.val ⊆ U}
  zero_mem' := by simp [ModelData.sectionSupport]
  add_mem' := by
    rintro α β ⟨hα, sα⟩ ⟨hβ, sβ⟩
    exact ⟨(hα.union hβ).of_isClosed_subset isClosed_closure
      (support_add_subset α.val β.val),
      (support_add_subset α.val β.val).trans (union_subset sα sβ)⟩
  smul_mem' := by
    rintro r α ⟨hα, sα⟩
    exact ⟨hα.of_isClosed_subset isClosed_closure (support_smul_subset r α.val),
      (support_smul_subset r α.val).trans sα⟩

instance supportedGroup (K : Calculus C B) (U : TopologicalSpace.Opens M) (k : ℕ) :
    AddCommGroup (supportedForms K U k) :=
  @Submodule.addCommGroup ℝ (K.forms k) inferInstance
    (Submodule.addCommGroup (K.forms k)) (Submodule.module (K.forms k)) (supportedForms K U k)

instance supportedModule (K : Calculus C B) (U : TopologicalSpace.Opens M) (k : ℕ) :
    Module ℝ (supportedForms K U k) :=
  @Submodule.module ℝ (K.forms k) inferInstance
    (Submodule.addCommMonoid (K.forms k)) (Submodule.module (K.forms k)) (supportedForms K U k)

theorem supported_d (K : Calculus C B) (U : TopologicalSpace.Opens M) (k : ℕ)
    (ω : K.forms k) (hω : ω ∈ supportedForms K U k) :
    K.d k ω ∈ supportedForms K U (k+1) := by
  have hs := ExteriorDerivativeResults.derivative_support C k ω.val (K.d k ω).val
    (K.coordinates k ω.val ((K.mem_forms _ _).mp ω.property))
  exact ⟨hω.1.of_isClosed_subset isClosed_closure hs, hs.trans hω.2⟩

def supportedDifferential (K : Calculus C B) (U : TopologicalSpace.Opens M) (k : ℕ) :
    supportedForms K U k →ₗ[ℝ] supportedForms K U (k+1) :=
  (K.d k).restrict (fun ω hω => supported_d K U k ω hω)

def supportedComplex (K : Calculus C B) (U : TopologicalSpace.Opens M) : Cochain.{u} where
  Obj k := supportedForms K U k
  group k := inferInstance
  module k := inferInstance
  d := supportedDifferential K U
  square k ω := by
    apply Subtype.ext
    exact DeRhamResults.square_zero K k ω.val

def supportedCalculus (K : Calculus C B) (U : TopologicalSpace.Opens M) :
    CompactCalculus K U where
  complex := supportedComplex K U
  inclusion := {
    map k := (supportedForms K U k).subtype
    comm _ _ := rfl }
  injective _ := Subtype.val_injective
  range k ω := by
    constructor
    · intro h; exact ⟨⟨ω,h⟩, rfl⟩
    · rintro ⟨x, rfl⟩; exact x.property

/-- The inclusion's full range gives intrinsic compactness and support control. -/
theorem inclusion_support {K : Calculus C B} {U : TopologicalSpace.Opens M}
    (D : CompactCalculus K U) (k : ℕ) (x : D.complex.Obj k) :
    IsCompact (ModelData.sectionSupport (D.inclusion.map k x).val) ∧
      ModelData.sectionSupport (D.inclusion.map k x).val ⊆ U :=
  (D.range k _).mpr ⟨x,rfl⟩

/-- Lift a linear map through an injective full-range realization. -/
def liftMap {K : Calculus C B} {U : TopologicalSpace.Opens M}
    (D : CompactCalculus K U) {X : Type u} [AddCommGroup X] [Module ℝ X]
    (k : ℕ) (f : X →ₗ[ℝ] K.forms k)
    (h : ∀ x, IsCompact (ModelData.sectionSupport (f x).val) ∧ ModelData.sectionSupport (f x).val ⊆ U) :
    X →ₗ[ℝ] D.complex.Obj k :=
  ((LinearEquiv.ofInjective (D.inclusion.map k) (D.injective k)).symm.toLinearMap).comp
    (f.codRestrict (LinearMap.range (D.inclusion.map k))
      (fun x => (D.range k _).mp (h x)))

end Supported

section ZeroExtension
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {k : ℕ}

/-- Compactness in U prevents new boundary support in M. -/
theorem zeroExtend_support (U : TopologicalSpace.Opens M) (ω : RestrictedField S U k)
    (hω : IsCompact (ModelData.sectionSupport ω)) :
    ModelData.sectionSupport (zeroExtend ω) = Subtype.val '' ModelData.sectionSupport ω := by
  classical
  letI := S.topologicalManifold.hausdorff
  have hn : {p | zeroExtend ω p ≠ 0} = Subtype.val '' {p | ω p ≠ 0} := by
    ext p
    by_cases hp : p ∈ U
    · simp only [Set.mem_ofPred_eq, zeroExtend, dite_eq_left hp, Set.mem_image]
      constructor
      · intro h; exact ⟨⟨p,hp⟩,h,rfl⟩
      · rintro ⟨q,hq,rfl⟩; exact hq
    · simp [zeroExtend, Set.mem_image, hp]
  apply subset_antisymm
  · apply closure_minimal _ (hω.image continuous_subtype_val).isClosed
    rw [hn]
    exact image_mono subset_closure
  · change Subtype.val '' closure {p | ω p ≠ 0} ⊆ closure _
    rw [hn]
    exact image_closure_subset_closure_image continuous_subtype_val

theorem zeroExtend_smooth (B : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm B U ω)
    (hc : IsCompact (ModelData.sectionSupport ω)) : IsForm B (zeroExtend ω) := by
  classical
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  letI := S.topologicalManifold.hausdorff
  let F : M → Bundle.TotalSpace (Euclidean (n.choose k))
      (fun q => Fiber (TangentSpace S q) k) := fun p => ⟨p,zeroExtend ω p⟩
  have hOn : MapData.ManifoldContDiffOn ⊤ S.smoothStructure.val
      B.space.bundle.totalManifold.smoothStructure.val F U := by
    apply (manifoldContDiff_restrict_open ⊤ S.smoothStructure.val
      B.space.bundle.totalManifold.smoothStructure.val F U U.isOpen).mpr
    simpa [F, zeroExtend, IsRestrictedForm, MapData.openSubsetAtlas] using hω
  intro p
  by_cases hp : p ∈ U
  · exact hOn p hp
  · have hclosed : IsClosed (ModelData.sectionSupport (zeroExtend ω)) := isClosed_closure
    have hnot : p ∉ ModelData.sectionSupport (zeroExtend ω) := by
      rw [zeroExtend_support (S := S) U ω hc]
      rintro ⟨q,_,hq⟩
      exact hp (hq ▸ q.property)
    apply manifoldContDiffAt_congr (ExteriorDerivativeResults.zero_form C k B p)
    filter_upwards [hclosed.isOpen_compl.mem_nhds hnot] with q hq
    have hz : zeroExtend ω q = 0 := by
      by_contra hne
      exact hq (subset_closure hne)
    change (⟨q,0⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
      (fun q => Fiber (TangentSpace S q) k)) = ⟨q,zeroExtend ω q⟩
    rw [hz]

private theorem zero_extension_proof :
    Specs.SmoothManifolds.DeRham.CompactSupport.zero_extensionType.{u} := by
  intro n a M _ S C k B U ω hω hc
  have hs := zeroExtend_support (S := S) U ω hc
  exact ⟨zeroExtend_smooth B U ω hω hc, (by rw [hs]; exact hc.image continuous_subtype_val), hs⟩

private theorem extension_derivative_proof :
    Specs.SmoothManifolds.DeRham.CompactSupport.extension_derivativeType.{u} := by
  intro n a M _ S C B K U k ω η hω hc hη
  classical
  have he := zeroExtend_smooth (B k) U ω hω hc
  funext p
  by_cases hp : p ∈ U
  · obtain ⟨c,hc',hpc⟩ := S.smoothStructure.property.1.1 p
    rw [K.coordinates k _ he c hc' p hpc]
    exact (hη c hc' ⟨p,hp⟩ hpc).symm.trans (by simp [zeroExtend, hp])
  · have hs := ExteriorDerivativeResults.derivative_support C k (zeroExtend ω)
      (K.D k (zeroExtend ω)) (K.coordinates k _ he)
    have hz : K.D k (zeroExtend ω) p = 0 := by
      by_contra hne
      have ht := hs (subset_closure hne)
      rw [zeroExtend_support (S := S) U ω hc] at ht
      obtain ⟨q,_,hq⟩ := ht
      exact hp (hq ▸ q.property)
    simp [zeroExtend, hp, hz]

end ZeroExtension

section Extension
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} {U V : TopologicalSpace.Opens M}

theorem liftMap_eq (D : CompactCalculus K V) {X : Type u}
    [AddCommGroup X] [Module ℝ X] (k : ℕ) (f : X →ₗ[ℝ] K.forms k)
    (h : ∀ x, IsCompact (ModelData.sectionSupport (f x).val) ∧ ModelData.sectionSupport (f x).val ⊆ V)
    (x : X) : D.inclusion.map k (liftMap D k f h x) = f x := by
  have hh := (LinearEquiv.ofInjective (D.inclusion.map k) (D.injective k)).apply_symm_apply
    (⟨f x, (D.range k _).mp (h x)⟩ : LinearMap.range (D.inclusion.map k))
  exact congrArg Subtype.val hh

def extension (hUV : U ≤ V) (D : CompactCalculus K U) (E : CompactCalculus K V) :
    ChainMap D.complex E.complex where
  map k := liftMap E k (D.inclusion.map k)
    (fun x => ⟨(inclusion_support D k x).1, (inclusion_support D k x).2.trans hUV⟩)
  comm k x := by
    apply E.injective (k+1)
    erw [← E.inclusion.comm, liftMap_eq, liftMap_eq]
    exact D.inclusion.comm k x

@[simp] theorem extension_field (hUV : U ≤ V) (D : CompactCalculus K U)
    (E : CompactCalculus K V) (k : ℕ) (x : D.complex.Obj k) :
    E.inclusion.map k ((extension hUV D E).map k x) = D.inclusion.map k x :=
  by
    exact liftMap_eq E k (D.inclusion.map k)
      (fun x => ⟨(inclusion_support D k x).1, (inclusion_support D k x).2.trans hUV⟩) x

theorem extension_injective (hUV : U ≤ V) (D : CompactCalculus K U)
    (E : CompactCalculus K V) (k : ℕ) :
    Function.Injective ((extension hUV D E).map k) := by
  intro x y hxy
  apply D.injective k
  simpa using congrArg (E.inclusion.map k) hxy

private theorem extension_exists_proof :
    Specs.SmoothManifolds.DeRham.CompactSupport.extension_existsType.{u} := by
  intro n a M _ S C B K U V hUV D E
  exact ⟨extension hUV D E, extension_field hUV D E, extension_injective hUV D E⟩

end Extension

section Cover
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B) (O : OpenCover M)

def coverFirst : ChainMap (supportedComplex K (O.U ⊓ O.V))
    ((supportedComplex K O.U).prod (supportedComplex K O.V)) where
  map k := {
    toFun ω := (⟨ω.val, ω.property.1, fun p hp => (ω.property.2 hp).1⟩,
      ⟨-ω.val, (by simpa [ModelData.sectionSupport] using ω.property.1), by
          intro p hp
          have hneg : ModelData.sectionSupport (-ω.val.val) = ModelData.sectionSupport ω.val.val := by
            simp [ModelData.sectionSupport]
          exact (ω.property.2 (hneg ▸ hp)).2⟩)
    map_add' α β := by
      apply Prod.ext
      · exact Subtype.ext rfl
      · apply Subtype.ext
        change -(α.val + β.val) = -α.val + -β.val
        exact neg_add α.val β.val
    map_smul' r α := by
      apply Prod.ext
      · exact Subtype.ext rfl
      · apply Subtype.ext
        change -(r • α.val) = r • (-α.val)
        exact (smul_neg r α.val).symm }
  comm k ω := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact map_neg (K.d k) ω.val

def coverSum : ChainMap
    ((supportedComplex K O.U).prod (supportedComplex K O.V)) (supportedComplex K ⊤) where
  map k := {
    toFun ω := ⟨ω.1.val + ω.2.val,
      (ω.1.property.1.union ω.2.property.1).of_isClosed_subset isClosed_closure
        (support_add_subset ω.1.val.val ω.2.val.val), subset_univ _⟩
    map_add' α β := by
      apply Subtype.ext
      change (α.1.val + β.1.val) + (α.2.val + β.2.val) =
        (α.1.val + α.2.val) + (β.1.val + β.2.val)
      abel
    map_smul' r α := by
      apply Subtype.ext
      change r • α.1.val + r • α.2.val = r • (α.1.val + α.2.val)
      exact (smul_add r _ _).symm }
  comm k ω := by
    apply Subtype.ext
    exact map_add (K.d k) _ _

theorem coverFirst_injective (k : ℕ) : Function.Injective ((coverFirst K O).map k) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z => z.1.val) h

theorem cover_exact (k : ℕ) (x : ((supportedComplex K O.U).prod
    (supportedComplex K O.V)).Obj k) :
    (coverSum K O).map k x = 0 ↔ ∃ y, (coverFirst K O).map k y = x := by
  have hneg : ∀ (ω : K.forms k), ModelData.sectionSupport (-ω.val) = ModelData.sectionSupport ω.val := by
    intro ω
    simp [ModelData.sectionSupport]
  constructor
  · intro hx
    have hab : x.1.val + x.2.val = 0 := congrArg Subtype.val hx
    have hb : x.2.val = -x.1.val := eq_neg_of_add_eq_zero_right (a := x.1.val) (b := x.2.val) hab
    have hV : ModelData.sectionSupport x.1.val.val ⊆ O.V := by
      have hh := x.2.property.2
      rw [hb, show (-x.1.val).val = -x.1.val.val from rfl, hneg] at hh
      exact hh
    refine ⟨⟨x.1.val, x.1.property.1, fun p hp => ⟨x.1.property.2 hp,hV hp⟩⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact Subtype.ext hb.symm
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    exact add_neg_cancel y.val

/-- Smooth scalar multiplication, used for the partition splitting. -/
def multiplyForm (k : ℕ) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) (ω : K.forms k) : K.forms k :=
  ⟨fun p => f p • ω.val p, (K.mem_forms _ _).mpr (by
    rw [← ExteriorDerivativeResults.fieldWedge_scalar]
    exact ExteriorAlgebraResults.wedge_smooth C k 0 (B k) (B 0) (B k) ω.val
      (FormPullbackData.scalarField S f) ((K.mem_forms _ _).mp ω.property)
      (ExteriorDerivativeResults.scalarField_form C (B 0) f hf))⟩

theorem coverSum_surjective
    (hcover : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (k : ℕ) : Function.Surjective ((coverSum K O).map k) := by
  obtain ⟨K',D,hD⟩ := hcover S C B O
  obtain ⟨ρU,ρV,hU,hV,hpartition,sU,sV,_⟩ := hD
  intro ω
  let α := multiplyForm K k ρU hU ω.val
  let β := multiplyForm K k ρV hV ω.val
  have hα : α ∈ supportedForms K O.U k := by
    have hs := support_function_smul_subset ρU ω.val.val
    exact ⟨ω.property.1.of_isClosed_subset isClosed_closure
      (hs.trans inter_subset_right), (hs.trans inter_subset_left).trans sU⟩
  have hβ : β ∈ supportedForms K O.V k := by
    have hs := support_function_smul_subset ρV ω.val.val
    exact ⟨ω.property.1.of_isClosed_subset isClosed_closure
      (hs.trans inter_subset_right), (hs.trans inter_subset_left).trans sV⟩
  refine ⟨(⟨α,hα⟩,⟨β,hβ⟩), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext p
  change ρU p • ω.val.val p + ρV p • ω.val.val p = ω.val.val p
  rw [← add_smul, (hpartition p).2.2, one_smul]

def coverSequence
    (hcover : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u}) :
    CoverSequence K O where
  global := supportedCalculus K ⊤
  onU := supportedCalculus K O.U
  onV := supportedCalculus K O.V
  overlap := supportedCalculus K (O.U ⊓ O.V)
  sequence := {
    r := coverFirst K O
    q := coverSum K O
    injective := coverFirst_injective K O
    surjective := coverSum_surjective K O hcover
    exact := cover_exact K O }
  first_U _ _ := rfl
  first_V _ _ := rfl
  sum _ _ := rfl

end Cover

open private smoothPull smoothPull_chain from MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra

section ProperPullback
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {C : CotangentBundle S} {A : CotangentBundle T}
  {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
  {K : Calculus C B} {J : Calculus A E}
  (D : CompactCalculus K ⊤) (G : CompactCalculus J ⊤)
  (f : M → N) (hf : MapData.IsSmoothMap S T f) (hp : IsProperMap f)
  (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
  (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))

def properPullLinear (k : ℕ) : G.complex.Obj k →ₗ[ℝ] K.forms k :=
  (smoothPull K J f hf L hL k).comp (G.inclusion.map k)

include hp in
theorem properPull_support (k : ℕ) (x : G.complex.Obj k) :
    IsCompact (ModelData.sectionSupport (properPullLinear (K := K) G f hf L hL k x).val) ∧
      ModelData.sectionSupport (properPullLinear (K := K) G f hf L hL k x).val ⊆ (⊤ : TopologicalSpace.Opens M) :=
  ⟨ExteriorDerivativeResults.proper_pullback_compact_support S T f hp L k
    (G.inclusion.map k x).val (inclusion_support G k x).1, subset_univ _⟩

def properPullChain : ChainMap G.complex D.complex where
  map k := liftMap D k (properPullLinear (K := K) G f hf L hL k)
    (properPull_support G f hf hp L hL k)
  comm k x := by
    apply D.injective (k+1)
    rw [← D.inclusion.comm, liftMap_eq, liftMap_eq]
    change K.d k (smoothPull K J f hf L hL k (G.inclusion.map k x)) =
      smoothPull K J f hf L hL (k+1) (G.inclusion.map (k+1) (G.complex.d k x))
    rw [← G.inclusion.comm]
    exact (smoothPull_chain K J f hf L hL
      ExteriorDerivativeResults.smooth_naturality k (G.inclusion.map k x)).symm

theorem properPull_field (k : ℕ) (x : G.complex.Obj k) :
    (D.inclusion.map k ((properPullChain D G f hf hp L hL).map k x)).val =
      FormPullbackData.pullbackField S T f L (G.inclusion.map k x).val :=
  congrArg Subtype.val (liftMap_eq D k (properPullLinear (K := K) G f hf L hL k)
    (properPull_support G f hf hp L hL k) x)

end ProperPullback

private theorem proper_pullback_proof
    (hind : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.proper_pullbackType.{u} := by
  intro n m a b M N _ _ S T C A B E K J D G f hf hp L hL
  let P := properPullChain D G f hf hp L hL
  obtain ⟨F,hF,_⟩ := hind _ _ P
  exact ⟨{
    chain := P
    field := properPull_field D G f hf hp L hL
    induced := F
    representatives := hF }⟩

private theorem long_exact_proof
    (hconnecting : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (hinduced : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (hlong : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (hproduct : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.long_exactType.{u} := by
  intro n a M _ S C B K O D
  obtain ⟨R,hR,_⟩ := hinduced _ _ D.sequence.r
  obtain ⟨Q,hQ,_⟩ := hinduced _ _ D.sequence.q
  obtain ⟨δ,hδ,_⟩ := hconnecting _ _ _ D.sequence
  exact ⟨R,Q,δ,hR,hQ,hδ,hlong _ _ _ D.sequence R Q δ hR hQ hδ,
    hproduct D.onU.complex D.onV.complex⟩

private theorem open_forms_iff_proof :
    Specs.SmoothManifolds.DeRham.CompactSupport.open_forms_iffType.{u} := by
  intro n a M _ S C B K U D k ω
  constructor
  · rintro ⟨hω,hc⟩
    obtain ⟨hsmooth,hcompact,hsupp⟩ := zero_extension_proof (B k) U ω hω hc
    let η : K.forms k := ⟨zeroExtend ω, (K.mem_forms k _).mpr hsmooth⟩
    have hsmall : ModelData.sectionSupport η.val ⊆ U := by
      change ModelData.sectionSupport (zeroExtend ω) ⊆ U
      rw [hsupp]
      rintro p ⟨q,hq,rfl⟩
      exact q.property
    obtain ⟨x,hx⟩ := (D.range k η).mp ⟨hcompact,hsmall⟩
    refine ⟨x,fun p => ?_⟩
    have he := congrArg (fun z : K.forms k => z.val p.val) hx
    simpa [η,zeroExtend] using he
  · rintro ⟨x,hx⟩
    let η := (D.inclusion.map k x).val
    have he : (fun p : U => η p.val) = ω := funext hx
    rw [← he]
    have hs : ModelData.sectionSupport (fun p : U => η p.val) =
        Subtype.val ⁻¹' ModelData.sectionSupport η := by
      change closure (Subtype.val ⁻¹' {p | η p ≠ 0}) =
        Subtype.val ⁻¹' closure {p | η p ≠ 0}
      exact (U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val {p | η p ≠ 0}).symm
    refine ⟨?_, ?_⟩
    · letI := (cotangentSpace C).topology
      letI := (B k).space.topology
      apply (manifoldContDiff_restrict_open ⊤ S.smoothStructure.val
        (B k).space.bundle.totalManifold.smoothStructure.val
        (fun p : M => (⟨p,η p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
          (fun q => Fiber (TangentSpace S q) k))) U U.isOpen).mp
      intro p hp
      exact ((K.mem_forms k _).mp (D.inclusion.map k x).property) p
    · rw [hs]
      apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
        (inclusion_support D k x).1
      intro p hp
      exact ⟨⟨p,(inclusion_support D k x).2 hp⟩,rfl⟩

theorem differential_support_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.differential_supportType.{u} := by
  intro n a M _ S C B K k ω
  exact ExteriorDerivativeResults.derivative_support C k ω.val (K.d k ω).val
    (K.coordinates k ω.val ((K.mem_forms _ _).mp ω.property))

theorem complex_exists_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.complex_existsType.{u} := by
  intro n a M _ S C B
  obtain ⟨K⟩ := DeRhamResults.complex_exists C B
  exact ⟨K, ⟨supportedCalculus K ⊤⟩⟩

theorem open_complex_exists_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.open_complex_existsType.{u} := by
  intro n a M _ S C B K U
  exact ⟨supportedCalculus K U⟩

theorem zero_extension_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.zero_extensionType.{u} := zero_extension_proof

theorem extension_derivative_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.extension_derivativeType.{u} := extension_derivative_proof

theorem extension_exists_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.extension_existsType.{u} := extension_exists_proof

theorem proper_pullback_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.proper_pullbackType.{u} := proper_pullback_proof h3

theorem cover_sequence_exists_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.cover_sequence_existsType.{u} := by
  intro n a M _ S C B K O
  exact ⟨coverSequence K O h2⟩

theorem long_exact_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.long_exactType.{u} := long_exact_proof h0 h3 h4 h6

theorem open_forms_iff_conditional
    (h0 : Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u})
    (h5 : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u})
    (h6 : Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u}) :
    Specs.SmoothManifolds.DeRham.CompactSupport.open_forms_iffType.{u} := open_forms_iff_proof

end SmoothManifolds.CompactSupportResults

universe v8_closure_51c6994a61a62221_u0
theorem _root_.«SmoothManifolds».«CompactSupportResults».«complex_exists» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«complex_existsType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«complex_exists_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«cover_sequence_exists» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«cover_sequence_existsType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«cover_sequence_exists_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«differential_support» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«differential_supportType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«differential_support_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«extension_derivative» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«extension_derivativeType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«extension_derivative_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«extension_exists» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«extension_existsType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«extension_exists_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«long_exact» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«long_exactType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«long_exact_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«open_complex_exists» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«open_complex_existsType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«open_complex_exists_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«open_forms_iff» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«open_forms_iffType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«open_forms_iff_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«proper_pullback» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«proper_pullbackType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«proper_pullback_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
theorem _root_.«SmoothManifolds».«CompactSupportResults».«zero_extension» : _root_.«Specs».«SmoothManifolds».«DeRham».«CompactSupport».«zero_extensionType».{v8_closure_51c6994a61a62221_u0} :=
  @_root_.«SmoothManifolds».«CompactSupportResults».«zero_extension_conditional».{v8_closure_51c6994a61a62221_u0} (@_root_.«SmoothManifolds».«MayerVietorisResults».«connecting_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_pullback_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«cover_sequence_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«induced_exists».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«long_exact».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«naturality».{v8_closure_51c6994a61a62221_u0}) (@_root_.«SmoothManifolds».«MayerVietorisResults».«product_cohomology».{v8_closure_51c6994a61a62221_u0})
