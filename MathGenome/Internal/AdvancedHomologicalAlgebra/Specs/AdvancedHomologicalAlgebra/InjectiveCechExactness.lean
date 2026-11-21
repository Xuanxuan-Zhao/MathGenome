import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechCochains
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
Independent definitions for the full augmented Čech sheaf chain (HA-H02-Injective,
source 3629–3648). The construction on X resolves the extension by zero of O_U;
its restriction to U is the source's chain. All indices and repetitions are kept.
The index universe is independent of the space and of the original coefficients.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
universe u v

namespace AdvancedHomologicalAlgebra.CechChains
variable {X : TopCat.{u}} (R : RingSheaf X)

/-- Lift only the carrier of each module, leaving the ring sheaf and every
restriction of scalars fixed. -/
def liftPresheaf (F : PresheafOfModules.{u} R.obj) :
    PresheafOfModules.{max u v} R.obj where
  obj W := (ModuleCat.uliftFunctor.{v, u} (R.obj.obj W)).obj (F.obj W)
  map {W V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      ((ModuleCat.uliftFunctor.{v, u} (R.obj.obj V)).obj (F.obj V))) {
    toFun := fun s ↦ ⟨F.map f s.down⟩
    map_add' := by intro s t; apply ULift.ext; exact map_add (F.map f).hom _ _
    map_smul' := by intro r s; apply ULift.ext; exact F.map_smul f r s.down }
  map_id W := by
    ext s
    apply ULift.ext
    exact congr($(F.presheaf.map_id W) (s.down))
  map_comp f g := by
    ext s
    apply ULift.ext
    exact F.map_comp_apply f g s.down

/-- The lift remains a sheaf on the same space, since the lift of groups
preserves the limits expressing sheaf gluing. -/
def liftSheaf (M : Modules R) : SheafOfModules.{max u v} R where
  val := liftPresheaf R M.val
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf _ M.val.presheaf
    AddCommGrpCat.uliftFunctor.{v, u} M.isSheaf

/-- The same lift on sheaf morphisms. -/
def liftSheafMap {M N : Modules R} (f : M ⟶ N) :
    liftSheaf.{u, v} R M ⟶ liftSheaf.{u, v} R N where
  val := {
    app := fun W ↦ (ModuleCat.uliftFunctor.{v, u} (R.obj.obj W)).map (f.val.app W)
    naturality := by
      intro V W j
      ext s
      apply ULift.ext
      exact PresheafOfModules.naturality_apply f.val j s.down }

abbrev largeOpenUnit (V : Opens X) : SheafOfModules.{max u v} R :=
  liftSheaf.{u, v} R (openUnit R V)

/-- The adjunction generator of the open unit, with its carrier lifted. -/
def largeOpenUnitGenerator (V : Opens X) : (largeOpenUnit.{u, v} R V).val.obj (op V) :=
  ⟨openUnitGenerator R V⟩

/-- Underlying additive stalk, computed in the module carrier universe. -/
abbrev largeStalk (x : X) : SheafOfModules.{max u v} R ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf R ⋙ TopCat.Sheaf.forget _ X ⋙
    (Functor.whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op ⋙ colim

/-- Germ of a section in the same large carrier as the stalk. -/
def largeGerm (M : SheafOfModules.{max u v} R) (x : X) (V : Opens X) (hx : x ∈ V) :
    M.val.presheaf.obj (op V) ⟶ (largeStalk.{u, v} R x).obj M :=
  colimit.ι ((OpenNhds.inclusion x).op ⋙ M.val.presheaf) (op ⟨V, hx⟩)

local instance largeSheafification :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} := by
  let e := AsSmall.equiv.{u, u, max u v} (C := Opens X)
  let K := e.inverse.inducedTopology (Opens.grothendieckTopology X)
  let h : HasSheafify K AddCommGrpCat.{max u v} := inferInstance
  exact e.hasSheafify (Opens.grothendieckTopology X) K AddCommGrpCat.{max u v}

local instance largeSheafificationLocalEquivalences :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v} := by
  let e := AsSmall.equiv.{u, u, max u v} (C := Opens X)
  let K := e.inverse.inducedTopology (Opens.grothendieckTopology X)
  let h : K.WEqualsLocallyBijective AddCommGrpCat.{max u v} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport _ K e.inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- Additive corepresentations by evaluation at the adjunction generator. -/
structure SectionPresentation where
  equiv : ∀ (V : Opens X) (M : SheafOfModules.{max u v} R),
    (largeOpenUnit.{u, v} R V ⟶ M) ≃+ M.val.obj (op V)
  naturality : ∀ (V : Opens X) (M N : SheafOfModules.{max u v} R) (f : largeOpenUnit.{u, v} R V ⟶ M) (g : M ⟶ N),
    equiv V N (f ≫ g) = g.val.app (op V) (equiv V M f)
  evaluation : ∀ (V : Opens X) (M : SheafOfModules.{max u v} R)
    (f : largeOpenUnit.{u, v} R V ⟶ M),
    equiv V M f = f.val.app (op V) (largeOpenUnitGenerator.{u, v} R V)

variable {U : Opens X} {I : Type v} (c : Cover U I)

/-- The genuine sheaf coproduct, not the product or the presheaf sum. -/
abbrev term (p : ℕ) : SheafOfModules.{max u v} R := ∐ fun t : Fin (p + 1) → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)


/-- Right multiplication on each open unit, by the scalar restricted from U. -/
def termRightMul (p : ℕ) (r : sectionRing R U) : term R c p ⟶ term R c p :=
  Sigma.desc fun t ↦ liftSheafMap.{u, v} R (openRightMul R (tupleOpen c t)
    (R.obj.map (homOfLE (tupleOpen_le c t)).op r)) ≫
      Sigma.ι (fun t : Fin (p + 1) → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)) t

/-- The original cover regarded as a cover of the actual open subspace. -/
def internalCover : Cover (⊤ : Opens ((Opens.toTopCat X).obj U)) I where
  opens i := (Opens.map U.inclusion').obj (c.opens i)
  le _ := le_top
  covers := by
    change iSup ((Opens.map U.inclusion').obj ∘ c.opens) = ⊤
    rw [← Opens.map_iSup, c.covers, Opens.inclusion'_map_eq_top]

lemma internalCover_tuple (p : ℕ) (t : Fin (p + 1) → I) :
    tupleOpen (internalCover c) t = (Opens.map U.inclusion').obj (tupleOpen c t) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [tupleOpen, ih, tupleOpen]
    rfl


namespace SectionPresentation
variable {R} (e : SectionPresentation.{u, v} R)

/-- The canonical extension-by-zero inclusion, defined by restricting the
universal section. Naturality makes its action on Hom exactly restriction. -/
def inclusion {V W : Opens X} (h : V ≤ W) : largeOpenUnit.{u, v} R V ⟶ largeOpenUnit.{u, v} R W :=
  (e.equiv V _).symm ((largeOpenUnit.{u, v} R W).val.map (homOfLE h).op (e.equiv W _ (𝟙 _)))

lemma inclusion_on_generator {V W : Opens X} (h : V ≤ W) :
    (e.inclusion h).val.app (op V) (largeOpenUnitGenerator.{u, v} R V) =
      (largeOpenUnit.{u, v} R W).val.map (homOfLE h).op (largeOpenUnitGenerator.{u, v} R W) := by
  rw [← e.evaluation, inclusion, AddEquiv.apply_symm_apply, e.evaluation]
  rfl

lemma stalk_inclusion_on_generator {V W : Opens X} (h : V ≤ W) (x : X) (hx : x ∈ V) :
    (largeStalk.{u, v} R x).map (e.inclusion h)
      (largeGerm R (largeOpenUnit.{u, v} R V) x V hx
        (largeOpenUnitGenerator.{u, v} R V)) =
    largeGerm R (largeOpenUnit.{u, v} R W) x W (h hx)
      (largeOpenUnitGenerator.{u, v} R W) := by
  let F : (OpenNhds x)ᵒᵖ ⥤ (Opens X)ᵒᵖ := (OpenNhds.inclusion x).op
  let iV : OpenNhds x := ⟨V, hx⟩
  let iW : OpenNhds x := ⟨W, h hx⟩
  let j : iV ⟶ iW := homOfLE h
  let D := F ⋙ (largeOpenUnit.{u, v} R V).val.presheaf
  let E := F ⋙ (largeOpenUnit.{u, v} R W).val.presheaf
  let f : D ⟶ E :=
    Functor.whiskerLeft F ((PresheafOfModules.toPresheaf R.obj).map (e.inclusion h).val)
  unfold largeGerm
  change colimMap f (colimit.ι D (op iV) (largeOpenUnitGenerator.{u, v} R V)) =
    colimit.ι E (op iW) (largeOpenUnitGenerator.{u, v} R W)
  rw [← ConcreteCategory.comp_apply, ι_colimMap, ConcreteCategory.comp_apply]
  change colimit.ι E (op iV)
    ((e.inclusion h).val.app (op V) (largeOpenUnitGenerator.{u, v} R V)) = _
  rw [inclusion_on_generator]
  change colimit.ι E (op iV) (E.map j.op (largeOpenUnitGenerator.{u, v} R W)) = _
  rw [← ConcreteCategory.comp_apply, colimit.w]

variable {U : Opens X} {I : Type v} (c : Cover U I)

/-- Any reindexing of positions induces a chain map in the reverse direction. -/
def reindex {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    term (R := R) c q ⟶ term (R := R) c p :=
  Sigma.desc fun t ↦ e.inclusion (tupleOpen_reindex_le c f t) ≫
    Sigma.ι (fun t : Fin (p + 1) → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)) (t ∘ f)

/-- Alternating omission maps on each summand. -/
def boundary (p : ℕ) : term (R := R) c (p + 1) ⟶ term (R := R) c p :=
  ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) • e.reindex c a.succAbove

/-- Augmentation to the extension by zero of O_U. -/
def augmentation : term (R := R) c 0 ⟶ largeOpenUnit.{u, v} R U :=
  Sigma.desc fun t ↦ e.inclusion (tupleOpen_le c t)

/-- The full product identification on Hom. -/
def homCochains (M : SheafOfModules.{max u v} R) (p : ℕ) :
    (term (R := R) c p ⟶ M) ≃+ Cochains R M.val c p where
  toFun f t := e.equiv (tupleOpen c t) M (Sigma.ι (fun t : Fin (p + 1) → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)) t ≫ f)
  invFun s := Sigma.desc fun t ↦ (e.equiv _ M).symm (s t)
  left_inv f := by
    apply Sigma.hom_ext
    intro t
    simp only [Sigma.ι_comp_desc, AddEquiv.symm_apply_apply]
  right_inv s := by
    funext t
    simp only [Sigma.ι_comp_desc, AddEquiv.apply_symm_apply]
  map_add' f g := by
    funext t
    simp only [Preadditive.comp_add, map_add, Pi.add_apply]

end SectionPresentation
end AdvancedHomologicalAlgebra.CechChains

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness
open AdvancedHomologicalAlgebra.CechChains
variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {I : Type v} (c : Cover U I)

def presentationExists : Prop := Nonempty (SectionPresentation.{u, v} R)

/-- Complex identities for the explicitly specified alternating maps. -/
def chainIdentities (e : SectionPresentation.{u, v} R) : Prop :=
  e.boundary c 0 ≫ e.augmentation c = 0 ∧
  ∀ p, e.boundary c (p + 1) ≫ e.boundary c p = 0

/-- The Hom identification intertwines both augmentation and every differential. -/
def homIdentification (e : SectionPresentation.{u, v} R) : Prop :=
  (∀ (M : SheafOfModules.{max u v} R) (f : largeOpenUnit.{u, v} R U ⟶ M),
    e.homCochains c M 0 (e.augmentation c ≫ f) =
      AdvancedHomologicalAlgebra.Cech.augmentation R M.val c (e.equiv U M f)) ∧
  ∀ (M : SheafOfModules.{max u v} R) (p : ℕ) (f : term (R := R) c p ⟶ M),
    e.homCochains c M (p + 1) (e.boundary c p ≫ f) =
      differential R M.val c p (e.homCochains c M p f)

/-- Stalkwise exactness, including surjectivity onto the augmented term.
This expresses exactness as equality of image and kernel in actual stalk modules. -/
def stalkExactness (e : SectionPresentation.{u, v} R) : Prop := ∀ x : X,
  Function.Surjective ((largeStalk.{u, v} R x).map (e.augmentation c)) ∧
  (∀ z, (largeStalk.{u, v} R x).map (e.augmentation c) z = 0 →
    ∃ y, (largeStalk.{u, v} R x).map (e.boundary c 0) y = z) ∧
  ∀ p z, (largeStalk.{u, v} R x).map (e.boundary c p) z = 0 →
    ∃ y, (largeStalk.{u, v} R x).map (e.boundary c (p + 1)) y = z

/-- Exactness of the full augmented cochains for an arbitrary injective sheaf.
The maps are the actual R(U)-linear maps in the upstream Čech definition. -/
def injectiveExactness : Prop := ∀ (M : Modules R), Injective M →
  Function.Injective (AdvancedHomologicalAlgebra.Cech.augmentation R M.val c) ∧
  (∀ z, differential R M.val c 0 z = 0 →
    ∃ s, AdvancedHomologicalAlgebra.Cech.augmentation R M.val c s = z) ∧
  ∀ p z, differential R M.val c (p + 1) z = 0 →
    ∃ y, differential R M.val c p y = z

/-- The identification respects the complete section-ring action induced by
right multiplication on every summand. -/
def homLinearIdentification (e : SectionPresentation.{u, v} R) : Prop :=
  ∀ (M : SheafOfModules.{max u v} R) (p : ℕ),
    ∃ inst : Module (sectionRing R U) (term R c p ⟶ M),
      letI := inst
      (∀ (r : sectionRing R U) (f : term R c p ⟶ M),
        r • f = termRightMul R c p r ≫ f) ∧
      ∃ E : (term R c p ⟶ M) ≃ₗ[sectionRing R U] Cochains R M.val c p,
        ∀ f, E f = e.homCochains c M p f

/-- A bundled chain complex, with all its terms and maps identified with the
specified coproducts and alternating extension-by-zero inclusions. -/
def complexConstruction (e : SectionPresentation.{u, v} R) : Prop :=
  ∃ K : ChainComplex (SheafOfModules.{max u v} R) ℕ,
    ∃ iso : ∀ p, K.X p ≅ term R c p,
      ∀ p, K.d (p + 1) p ≫ (iso p).hom = (iso (p + 1)).hom ≫ e.boundary c p

/-- The construction is unconditional: the representing data and all its
properties are supplied, not additional hypotheses on the original objects. -/
def sheafChainProperties (e : SectionPresentation.{u, v} R) : Prop :=
  complexConstruction R c e ∧ chainIdentities R c e ∧
  homIdentification R c e ∧ homLinearIdentification R c e ∧ stalkExactness R c e

def sheafChainConstruction : Prop := ∃ e : SectionPresentation.{u, v} R,
  sheafChainProperties R c e

/-- Transport of the augmentation to the unit on a space covered by d. -/
def unitAugmentationExactness (d : Cover (⊤ : Opens X) I) (e : SectionPresentation.{u, v} R)
    (iso : largeOpenUnit.{u, v} R ⊤ ≅ liftSheaf.{u, v} R (SheafOfModules.unit R)) : Prop :=
  ∀ x : X,
    Function.Surjective ((largeStalk.{u, v} R x).map (e.augmentation d ≫ iso.hom)) ∧
    ∀ z, (largeStalk.{u, v} R x).map (e.augmentation d ≫ iso.hom) z = 0 →
      ∃ y, (largeStalk.{u, v} R x).map (e.boundary d 0) y = z

/-- The full sheaf-chain construction for a cover of the whole space. -/
def topCoverConstruction (d : Cover (⊤ : Opens X) I) : Prop :=
  ∃ e : SectionPresentation.{u, v} R,
    sheafChainProperties R d e ∧
    ∃ iso : largeOpenUnit.{u, v} R ⊤ ≅ liftSheaf.{u, v} R (SheafOfModules.unit R),
      iso.hom.val.app (op ⊤) (largeOpenUnitGenerator.{u, v} R ⊤) =
        ⟨(1 : sectionRing R ⊤)⟩ ∧
      unitAugmentationExactness R d e iso

/-- Source formulation on the actual open subspace, with augmentation to its
actual unit sheaf and exactness checked at every point of that subspace. -/
def onOpenConstruction : Prop :=
  topCoverConstruction (U.sheafRestrict.obj R) (internalCover c)

/-- Closed types for all unconditional public targets. -/
def presentationExistsType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X),
  presentationExists.{u, v} R

def sheafChainConstructionType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {I : Type v} (c : Cover U I), sheafChainConstruction R c

def onOpenConstructionType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {I : Type v} (c : Cover U I), onOpenConstruction R c

def injectiveExactnessType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  {U : Opens X} {I : Type v} (c : Cover U I), injectiveExactness R c

end Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness
