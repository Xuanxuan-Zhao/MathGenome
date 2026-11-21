import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Representations
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Exact

/-! Concrete kernels, cokernels and images of quiver representations. -/

open CategoryTheory CategoryTheory.Limits

namespace RM03.QuiverVertexwiseExactnessSpec

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

variable {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}

private def restrict (V : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q)
    (P : ∀ i : Paths Q, Submodule k (V.obj i))
    (h : ∀ {i j : Paths Q} (p : i ⟶ j), P i ≤ (P j).comap (V.map p).hom) :
    QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q where
  obj i := ModuleCat.of k (P i)
  map p := ModuleCat.ofHom (((V.map p).hom.comp (P _).subtype).codRestrict _ fun x => h p x.2)
  map_id i := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => Subtype.ext ?_
    change ((V.map (𝟙 i)).hom x : V.obj i) = x
    rw [V.map_id]
    rfl
  map_comp p q := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (V.map (p ≫ q)).hom x = (V.map q).hom ((V.map p).hom x)
    rw [V.map_comp]
    rfl

private def restrictInclusion (V : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q)
    (P : ∀ i : Paths Q, Submodule k (V.obj i))
    (h : ∀ {i j : Paths Q} (p : i ⟶ j), P i ≤ (P j).comap (V.map p).hom) :
    restrict V P h ⟶ V where
  app i := ModuleCat.ofHom (P i).subtype
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    ext
    rfl

private theorem kernel_stable (f : F ⟶ G) {i j : Paths Q} (p : i ⟶ j) :
    (f.app i).hom.ker ≤ ((f.app j).hom.ker).comap (F.map p).hom := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  have hn := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.naturality p)) x
  change (f.app j).hom ((F.map p).hom x) = (G.map p).hom ((f.app i).hom x) at hn
  rw [hn, LinearMap.mem_ker.mp hx, map_zero]

private theorem range_stable (f : F ⟶ G) {i j : Paths Q} (p : i ⟶ j) :
    (f.app i).hom.range ≤ ((f.app j).hom.range).comap (G.map p).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(F.map p).hom x,
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.naturality p)) x⟩

/-- The representation on the component kernel subspaces. -/
def kernelRepresentation (f : F ⟶ G) : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q :=
  restrict F (fun i => (f.app i).hom.ker) (kernel_stable f)

/-- Inclusions of the component kernel subspaces. -/
def kernelInclusion (f : F ⟶ G) : kernelRepresentation f ⟶ F :=
  restrictInclusion F (fun i => (f.app i).hom.ker) (kernel_stable f)

/-- The representation on the vertex quotients by the component images. -/
def cokernelRepresentation (f : F ⟶ G) : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q where
  obj i := ModuleCat.of k (G.obj i ⧸ (f.app i).hom.range)
  map {i j} p := ModuleCat.ofHom
    ((f.app i).hom.range.mapQ (f.app j).hom.range (G.map p).hom (range_stable f p))
  map_id i := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (f.app i).hom.range.mkQ_surjective x
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.id_apply,
      Submodule.mkQ_apply, Submodule.mapQ_apply, G.map_id]
  map_comp {i j l} p q := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (f.app i).hom.range.mkQ_surjective x
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply,
      Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [G.map_comp]
    rfl

/-- The quotient maps to the component cokernels. -/
def cokernelProjection (f : F ⟶ G) : G ⟶ cokernelRepresentation f where
  app i := ModuleCat.ofHom (f.app i).hom.range.mkQ
  naturality _ _ p := ModuleCat.hom_ext
    (Submodule.mapQ_mkQ _ _ _ (h := range_stable f p)).symm

/-- The representation on the component image subspaces. -/
def imageRepresentation (f : F ⟶ G) : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q :=
  restrict G (fun i => (f.app i).hom.range) (range_stable f)

/-- Inclusions of the component images. -/
def imageInclusion (f : F ⟶ G) : imageRepresentation f ⟶ G :=
  restrictInclusion G (fun i => (f.app i).hom.range) (range_stable f)

/-- Corestrictions of the component linear maps to their images. -/
def toImage (f : F ⟶ G) : F ⟶ imageRepresentation f where
  app i := ModuleCat.ofHom ((f.app i).hom.codRestrict _ fun x => ⟨x, rfl⟩)
  naturality _ _ p := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.naturality p)) x

def kernelFork (f : F ⟶ G) : KernelFork f :=
  KernelFork.ofι (kernelInclusion f) (NatTrans.ext (funext fun i =>
    ModuleCat.hom_ext (LinearMap.comp_ker_subtype (f.app i).hom)))

def cokernelCofork (f : F ⟶ G) : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelProjection f) (NatTrans.ext (funext fun i =>
    ModuleCat.hom_ext (LinearMap.range_mkQ_comp (f.app i).hom)))

def imageFactorisation (f : F ⟶ G) : MonoFactorisation f where
  I := imageRepresentation f
  m := imageInclusion f
  e := toImage f
  m_mono := by
    let (i : Paths Q) : Mono ((imageInclusion f).app i) :=
      (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    exact NatTrans.mono_of_mono_app _
  fac := NatTrans.ext (funext fun _ => ModuleCat.hom_ext rfl)

section Signatures

-- The field, vertex, arrow and vector space universes vary independently.
set_option linter.checkUnivs false

abbrev RepresentationSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q},
    (F ⟶ G) → QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q

abbrev KernelInclusionSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G), kernelRepresentation f ⟶ F

abbrev CokernelProjectionSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G), G ⟶ cokernelRepresentation f

abbrev ImageInclusionSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G), imageRepresentation f ⟶ G

abbrev ToImageSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G), F ⟶ imageRepresentation f

abbrev KernelForkSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q} (f : F ⟶ G), KernelFork f

abbrev CokernelCoforkSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q} (f : F ⟶ G), CokernelCofork f

abbrev ImageFactorisationSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q} (f : F ⟶ G), MonoFactorisation f

end Signatures

def KernelUniversalProperty : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G), Nonempty (IsLimit (kernelFork f))

def CokernelUniversalProperty : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G), Nonempty (IsColimit (cokernelCofork f))

def ImageUniversalProperty : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G), Nonempty (IsImage (imageFactorisation f))

def VertexwiseExactness : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (S : ShortComplex (QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q)),
    S.Exact ↔ ∀ i : Q, (S.f.app i).hom.range = (S.g.app i).hom.ker

def VertexwiseExactPair : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    {F G H : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}
    (f : F ⟶ G) (g : G ⟶ H),
    (∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact) ↔
      ∀ i : Q, (f.app i).hom.range = (g.app i).hom.ker

end RM03.QuiverVertexwiseExactnessSpec
