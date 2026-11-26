import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v
noncomputable section

namespace LinearAlgebraicGroups.Specs.OrderedCechComparison

section DerivedCohomology

/-- Schemes over a commutative ring, used also for scalar extension to test algebras. -/
abbrev SchemeOverRing (A : Type u) [CommRing A] := Over (Spec (CommRingCat.of A))

variable {k : Type u} [CommRing k] (X : SchemeOverRing k)

/-- The scalar map from the base ring to global regular functions. -/
def groundRingHom : k →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom

/-- The structure map on the regular functions of an open. -/
def groundRingHomOpen (U : X.left.Opens) : k →+* Γ(X.left, U) :=
  (X.left.presheaf.map U.leTop.op).hom.comp (groundRingHom X)

theorem groundRingHomOpen_top : groundRingHomOpen X ⊤ = groundRingHom X := by
  unfold groundRingHomOpen
  have h : (TopologicalSpace.Opens.leTop (⊤ : X.left.Opens)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [h]
  exact congrArg (fun f : Γ(X.left, ⊤) ⟶ Γ(X.left, ⊤) ↦ f.hom.comp (groundRingHom X))
    (X.left.presheaf.map_id (op ⊤))

variable {X}

/-- The module of sections on an open, regarded as a module over the base ring. -/
abbrev localSections (F : X.left.Modules) (U : X.left.Opens) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (groundRingHomOpen X U)).obj (F.val.obj (op U))

theorem localScalars_comp {U V : X.left.Opens} (i : V ⟶ U) :
    groundRingHomOpen X V =
      (X.left.ringCatSheaf.obj.map i.op).hom.comp (groundRingHomOpen X U) := by
  unfold groundRingHomOpen
  ext r
  change (X.left.presheaf.map V.leTop.op) (groundRingHom X r) =
    (X.left.presheaf.map U.leTop.op ≫ X.left.presheaf.map i.op) (groundRingHom X r)
  rw [← X.left.presheaf.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
def localRestriction (F : X.left.Modules) {U V : X.left.Opens} (i : V ⟶ U) :
    localSections F U ⟶ localSections F V :=
  (ModuleCat.restrictScalars (groundRingHomOpen X U)).map (F.val.map i.op) ≫
    (ModuleCat.restrictScalarsComp' _ _ _ (localScalars_comp i)).inv.app (F.val.obj (op V))

/-- The underlying presheaf of k-modules of a sheaf of O-modules. -/
def coefficientPresheaf (F : X.left.Modules) : X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := localSections F U.unop
  map i := localRestriction F i.unop
  map_id U := by
    apply ModuleCat.hom_ext
    ext x
    change F.val.map (𝟙 U) x = x
    rw [F.val.map_id]
    rfl
  map_comp i j := by
    apply ModuleCat.hom_ext
    ext x
    change F.val.map (i ≫ j).unop.op x =
      F.val.map j.unop.op (F.val.map i.unop.op x)
    simpa only [Quiver.Hom.op_unop] using F.val.map_comp_apply i j x

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of sheaves of modules acts on the presheaves of ground-ring modules. -/
def coefficientPresheafMap {F F' : X.left.Modules} (f : F ⟶ F') :
    coefficientPresheaf (X := X) F ⟶ coefficientPresheaf (X := X) F' where
  app U := (ModuleCat.restrictScalars (groundRingHomOpen X U.unop)).map (f.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    ext x
    exact PresheafOfModules.naturality_apply f.val i (x : F.val.obj U)

variable (X)

/-- Global sections of a sheaf of modules, with scalars restricted to the
ground ring through the structural morphism. -/
def sectionsFunctor : X.left.Modules ⥤ ModuleCat.{u} k :=
  SheafOfModules.evaluation X.left.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars (groundRingHom X)

instance : (sectionsFunctor X).Additive where
  map_add := by intros; ext x; rfl

instance : PreservesFiniteLimits (sectionsFunctor X) := by
  let evalLimits : PreservesFiniteLimits
      (SheafOfModules.evaluation.{u} X.left.ringCatSheaf (op ⊤)) := inferInstance
  let restrictLimits : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u,u,u} (groundRingHom X)) := inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ (SheafOfModules.evaluation.{u} X.left.ringCatSheaf (op ⊤))
    (ModuleCat.restrictScalars.{u,u,u} (groundRingHom X)) evalLimits restrictLimits

/-- Zariski cohomology with coefficients in an actual sheaf of modules. -/
def cohomology (i : ℕ) : X.left.Modules ⥤ ModuleCat.{u} k :=
  (sectionsFunctor X).rightDerived i

def cohomologyZero : cohomology X 0 ≅ sectionsFunctor X :=
  (sectionsFunctor X).rightDerivedZeroIsoSelf

end DerivedCohomology

section CohomologyMaps

variable {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B}

private theorem groundRingHom_over (φ : A →+* B) (f : Y.left ⟶ X.left)
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) :
    f.appTop.hom.comp (groundRingHom X) = (groundRingHom Y).comp φ := by
  have h := congrArg Scheme.Hom.appTop hf
  simp only [Scheme.Hom.comp_appTop] at h
  change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ X.hom.appTop ≫ f.appTop).hom =
    (CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ Y.hom.appTop).hom
  rw [h, Scheme.ΓSpecIso_inv_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Global sections after pushing forward along a morphism over a map of rings. -/
def pushforwardSectionsIso (φ : A →+* B) (f : Y.left ⟶ X.left)
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) :
    Scheme.Modules.pushforward f ⋙ sectionsFunctor X ≅
      sectionsFunctor Y ⋙ ModuleCat.restrictScalars.{u} φ :=
  NatIso.ofComponents (fun M =>
    (ModuleCat.restrictScalarsComp'App (groundRingHom X) f.appTop.hom
      (f.appTop.hom.comp (groundRingHom X)) rfl (M.val.obj (op ⊤))).symm ≪≫
    ModuleCat.restrictScalarsComp'App φ (groundRingHom Y)
      (f.appTop.hom.comp (groundRingHom X)) (groundRingHom_over φ f hf)
      (M.val.obj (op ⊤))) (by
    intro M N g
    apply ModuleCat.hom_ext
    ext x
    rfl)

def restrictCohomologyIso (φ : A →+* B)
    (C : CochainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    (ModuleCat.restrictScalars.{u} φ).obj (C.homology n) ≅
      ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _ |>.obj C).homology n := by
  change (ModuleCat.restrictScalars.{u} φ).obj ((C.sc n).homology) ≅
    ((C.sc n).map (ModuleCat.restrictScalars.{u} φ)).homology
  exact ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars.{u} φ)).symm

/-- A cochain lift into a pushed-forward complex acts on global sections. -/
def sectionsComplexPullback (φ : A →+* B) (f : Y.left ⟶ X.left)
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {K : CochainComplex X.left.Modules ℕ} {L : CochainComplex Y.left.Modules ℕ}
    (l : K ⟶ ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj L) :
    ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (.up ℕ)).obj
        (((sectionsFunctor Y).mapHomologicalComplex (.up ℕ)).obj L) :=
  let ΓX := (sectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)
  let ΓY := (sectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℕ)
  let β : ΓX.obj (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj L) ⟶
      ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj (ΓY.obj L) :=
    HomologicalComplex.Hom.mk
      (fun i => (pushforwardSectionsIso φ f hf).hom.app (L.X i))
      (fun i j _ => (pushforwardSectionsIso φ f hf).hom.naturality (L.d i j))
  ΓX.map l ≫ β

/-- The map computed on the global section complexes of two resolutions. -/
def derivedMapOfLift (φ : A →+* B) (f : Y.left ⟶ X.left)
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : X.left.Modules} {G : Y.left.Modules}
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (l : I.cocomplex ⟶ ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj J.cocomplex)
    (n : ℕ) :
    (cohomology X n).obj F ⟶
      (ModuleCat.restrictScalars.{u} φ).obj ((cohomology Y n).obj G) :=
  let ΓY := (sectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℕ)
  (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
    HomologicalComplex.homologyMap (sectionsComplexPullback φ f hf l) n ≫
    (restrictCohomologyIso φ (ΓY.obj J.cocomplex) n).inv ≫
    (ModuleCat.restrictScalars.{u} φ).map (J.isoRightDerivedObj (sectionsFunctor Y) n).inv

/-- A map of cohomology induced by a coefficient morphism over a map of
schemes. On injective resolutions it is the map on homology of global sections
of a cochain lift of the coefficient morphism. -/
def IsCohomologyMap (φ : A →+* B) (f : Y.left ⟶ X.left)
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : X.left.Modules} {F' : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj F') (n : ℕ)
    (m : (cohomology X n).obj F ⟶
      (ModuleCat.restrictScalars.{u} φ).obj ((cohomology Y n).obj F')) : Prop :=
  ∀ (I : InjectiveResolution F) (J : InjectiveResolution F'),
    let P := Scheme.Modules.pushforward f
    let liftType := I.cocomplex ⟶ (P.mapHomologicalComplex _).obj J.cocomplex
    let lifts := fun l : liftType => I.ι.f 0 ≫ l.f 0 = α ≫ P.map (J.ι.f 0)
    (∃ l : liftType, lifts l) ∧
    ∀ l : liftType, lifts l →
      m = derivedMapOfLift φ f hf I J l n

end CohomologyMaps

section Cech

open CategoryTheory.Preadditive
open scoped Simplicial BigOperators

variable {k : Type u} [CommRing k] {D : Type v} [CompleteLattice D]
    {Idx : Type u} [Preorder Idx] (U : Idx → D) (P : Dᵒᵖ ⥤ ModuleCat.{u} k)

/-- In the ordered Čech complex each intersection is indexed by a strictly
increasing tuple of members of the cover. -/
def tupleOpen {n : ℕ} (e : Fin (n + 1) ↪o Idx) : D := ⨅ j, U (e j)

theorem tupleOpen_le {n m : ℕ} (e : Fin (m + 1) ↪o Idx)
    (f : Fin (n + 1) ↪o Fin (m + 1)) : tupleOpen U e ≤ tupleOpen U (f.trans e) :=
  le_iInf fun j => iInf_le _ (f j)

abbrev term (n : ℕ) : Type u :=
  ∀ e : Fin (n + 1) ↪o Idx, P.obj (op (tupleOpen U e))

def mapTerm {n m : SemiSimplexCategory} (f : n ⟶ m) :
    ModuleCat.of k (term U P n.len) ⟶ ModuleCat.of k (term U P m.len) :=
  ModuleCat.ofHom <| LinearMap.pi fun e =>
    (P.map (homOfLE (tupleOpen_le U e (SemiSimplexCategory.homEquiv f))).op).hom ∘ₗ
      LinearMap.proj ((SemiSimplexCategory.homEquiv f).trans e)

def orderedCochains : SemiSimplexCategory ⥤ ModuleCat.{u} k where
  obj n := ModuleCat.of k (term U P n.len)
  map f := mapTerm U P f
  map_id n := by
    apply ModuleCat.hom_ext
    ext x e
    change (P.map (homOfLE (le_refl (tupleOpen U e))).op) (x e) = x e
    have hid : (homOfLE (le_refl (tupleOpen U e))).op = 𝟙 _ := Subsingleton.elim _ _
    rw [hid, P.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x e
    change (P.map (homOfLE _).op) (x ((SemiSimplexCategory.homEquiv (f ≫ g)).trans e)) =
      (P.map (homOfLE _).op ≫ P.map (homOfLE _).op)
        (x ((SemiSimplexCategory.homEquiv f).trans ((SemiSimplexCategory.homEquiv g).trans e)))
    rw [← P.map_comp]
    simp only [SemiSimplexCategory.homEquiv_comp, RelEmbedding.trans_assoc]
    congr 3

def coface {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ₛ ⟶ ⦋n + 1⦌ₛ :=
  SemiSimplexCategory.homEquiv.symm i.succAboveOrderEmb

private theorem map_coface {n : ℕ} (i : Fin (n + 2)) :
    SemiSimplexCategory.toSimplexCategory.map (coface i) = SimplexCategory.δ i := rfl

def differential (n : ℕ) :
    (orderedCochains U P).obj ⦋n⦌ₛ ⟶ (orderedCochains U P).obj ⦋n + 1⦌ₛ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (orderedCochains U P).map (coface i)

set_option maxHeartbeats 600000 in
private theorem differential_squared (n : ℕ) :
    differential U P n ≫ differential U P (n + 1) = 0 := by
  simp only [differential, comp_sum, sum_comp, ← Finset.sum_product']
  let I := Fin (n + 3) × Fin (n + 2)
  let S : Finset I := {ij : I | (ij.1 : ℕ) ≤ (ij.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let swapTerm : ∀ ij : I, ij ∈ S → I := fun ij hij =>
    (ij.2.succ, Fin.castLT ij.1 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.2.isLt))
  apply Finset.sum_bij swapTerm
  · intro ij hij
    simp_rw [S, swapTerm, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [swapTerm, Fin.castSucc_castLT] using! congr(Fin.castSucc $(h).2),
      by simpa [swapTerm] using! congr($(h).1)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred ?_), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [swapTerm, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [swapTerm, Fin.val_succ, pow_add, pow_one, mul_neg, neg_mul, neg_neg, mul_one,
        Fin.val_castLT]
      apply mul_comm
    · simp only [← (orderedCochains U P).map_comp]
      congr 1
      apply SemiSimplexCategory.toSimplexCategory.map_injective
      simp only [Functor.map_comp, map_coface]
      exact (SimplexCategory.δ_comp_δ'' (by simpa [S, Fin.le_iff_val_le_val] using hij)).symm

/-- Finite-cover Čech complex, with alternating sums of restrictions. -/
def cechComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => (orderedCochains U P).obj ⦋n⦌ₛ) (differential U P)
    (differential_squared U P)

variable {P}

set_option backward.isDefEq.respectTransparency false in
def orderedCochainsMap {P' : Dᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ P') :
    orderedCochains U P ⟶ orderedCochains U P' where
  app n := ModuleCat.ofHom <| LinearMap.pi fun e =>
    (f.app (op (tupleOpen U e))).hom ∘ₗ LinearMap.proj e
  naturality := by
    intro _ _ i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    let j := (homOfLE (tupleOpen_le U e (SemiSimplexCategory.homEquiv i))).op
    let x' := x ((SemiSimplexCategory.homEquiv i).trans e)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.naturality j)) x'

/-- The induced map of ordered Čech complexes, obtained by mapping every section. -/
def cechMap {P' : Dᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ P') :
    cechComplex U P ⟶ cechComplex U P' :=
  let α := orderedCochainsMap U f
  CochainComplex.ofHom (fun n => α.app ⦋n⦌ₛ) fun n => by
    simp only [cechComplex, CochainComplex.of_d, differential, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
    exact Finset.sum_congr rfl fun i _ => congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
      (α.naturality (coface i)).symm

end Cech


section Pullback

variable {A B : Type u} [CommRing A] [CommRing B]
  {X : SchemeOverRing A} {Y : SchemeOverRing B}
  (φ : A →+* B) (f : Y.left ⟶ X.left)
  (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))

include hf in
theorem groundRingHomOpen_over (W : X.left.Opens) :
    (f.app W).hom.comp (groundRingHomOpen X W) =
      (groundRingHomOpen Y (f ⁻¹ᵁ W)).comp φ := by
  have h := f.c.naturality W.leTop.op
  ext r
  have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) (groundRingHom X r)
  change (f.app W) ((X.left.presheaf.map W.leTop.op) (groundRingHom X r)) =
    (Y.left.presheaf.map (f ⁻¹ᵁ W).leTop.op) (groundRingHom Y (φ r))
  change (f.app W) ((X.left.presheaf.map W.leTop.op) (groundRingHom X r)) =
    (Y.left.presheaf.map (f ⁻¹ᵁ W).leTop.op) (f.appTop (groundRingHom X r)) at h'
  rw [h']
  exact congrArg (Y.left.presheaf.map (f ⁻¹ᵁ W).leTop.op)
    (DFunLike.congr_fun (groundRingHom_over φ f hf) r)

set_option backward.isDefEq.respectTransparency false in
/-- A coefficient map into a pushforward on sections of every open. -/
def coefficientPullback {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    coefficientPresheaf F ⟶ (TopologicalSpace.Opens.map f.base).op ⋙
      coefficientPresheaf G ⋙ ModuleCat.restrictScalars φ where
  app W :=
    (ModuleCat.restrictScalars (groundRingHomOpen X W.unop)).map (α.val.app W) ≫
      ((ModuleCat.restrictScalarsComp'App (groundRingHomOpen X W.unop) (f.app W.unop).hom
        ((f.app W.unop).hom.comp (groundRingHomOpen X W.unop)) rfl
        (G.val.obj (op (f ⁻¹ᵁ W.unop)))).symm ≪≫
        ModuleCat.restrictScalarsComp'App φ (groundRingHomOpen Y (f ⁻¹ᵁ W.unop))
          ((f.app W.unop).hom.comp (groundRingHomOpen X W.unop))
          (groundRingHomOpen_over φ f hf W.unop) (G.val.obj (op (f ⁻¹ᵁ W.unop)))).hom
  naturality := by
    intro W V j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact PresheafOfModules.naturality_apply α.val j (x : F.val.obj W)

@[simp]
theorem coefficientPullback_apply {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) (W : X.left.Opens) (x : localSections F W) :
    (coefficientPullback φ f hf α).app (op W) x = α.app W x := rfl

variable {Idx : Type u} [Preorder Idx] (U : Idx → X.left.Opens)

abbrev pullbackCover : Idx → Y.left.Opens := fun i => f ⁻¹ᵁ U i

theorem tupleOpen_pullback {n : ℕ} (e : Fin (n + 1) ↪o Idx) :
    tupleOpen (pullbackCover f U) e = f ⁻¹ᵁ tupleOpen U e := by
  ext y
  change y ∈ ((⨅ j, f ⁻¹ᵁ U (e j)) : Y.left.Opens) ↔
    f y ∈ ((⨅ j, U (e j)) : X.left.Opens)
  simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

def pullbackToIntersection {n : ℕ} (e : Fin (n + 1) ↪o Idx) :
    tupleOpen (pullbackCover f U) e ⟶ f ⁻¹ᵁ tupleOpen U e :=
  eqToHom (tupleOpen_pullback f U e)

set_option backward.isDefEq.respectTransparency false in
private def orderedPullback {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    orderedCochains U (coefficientPresheaf F) ⟶
      orderedCochains (pullbackCover f U) (coefficientPresheaf G) ⋙ ModuleCat.restrictScalars φ where
  app n := by
    letI E := (orderedCochains (pullbackCover f U) (coefficientPresheaf G)).obj n
    letI D := (ModuleCat.restrictScalars φ).obj E
    change _ ⟶ D
    let b := coefficientPullback φ f hf α
    let q := fun e : Fin (n.len + 1) ↪o Idx =>
      (b.app (op (tupleOpen U e))) ≫ (ModuleCat.restrictScalars φ).map
        ((coefficientPresheaf G).map (pullbackToIntersection f U e).op)
    exact ModuleCat.ofHom (Y := D) {
      toFun := fun x e => q e (x e)
      map_add' := fun x y => funext fun e => (q e).hom.map_add (x e) (y e)
      map_smul' := fun r x => funext fun e => (q e).hom.map_smul r (x e) }
  naturality := by
    intro n m i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    let e' := (SemiSimplexCategory.homEquiv i).trans e
    let j : tupleOpen U e ⟶ tupleOpen U e' :=
      homOfLE (tupleOpen_le U e (SemiSimplexCategory.homEquiv i))
    let j' : tupleOpen (pullbackCover f U) e ⟶ tupleOpen (pullbackCover f U) e' :=
      homOfLE (tupleOpen_le (pullbackCover f U) e (SemiSimplexCategory.homEquiv i))
    let g := coefficientPresheaf G
    let b := coefficientPullback φ f hf α
    let D := ModuleCat.restrictScalars.{u} φ
    let m₁ := D.map (g.map (pullbackToIntersection f U e).op)
    let m₂ := D.map (g.map ((Opens.map f.base).map j).op)
    let m₃ := D.map (g.map (pullbackToIntersection f U e').op)
    let m₄ := D.map (g.map j'.op)
    let z := x e'
    change m₁ (b.app (op (tupleOpen U e)) ((coefficientPresheaf F).map j.op z)) =
      m₄ (m₃ (b.app (op (tupleOpen U e')) z))
    have h₁ : b.app (op (tupleOpen U e)) ((coefficientPresheaf F).map j.op z) =
        m₂ (b.app (op (tupleOpen U e')) z) :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (b.naturality j.op)) z
    have h₂ : m₂ ≫ m₁ = m₃ ≫ m₄ := by
      simp only [m₁, m₂, m₃, m₄, ← Functor.map_comp]
      exact congrArg (fun a => D.map (g.map a)) (Subsingleton.elim _ _)
    exact (congrArg (fun a => m₁ a) h₁).trans
      (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h₂) (b.app _ z))

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on the increasing-tuple Čech complexes. Each coordinate is the
map on sections over the corresponding intersection and its inverse image. -/
def cechPullback {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    cechComplex U (coefficientPresheaf F) ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj
        (cechComplex (pullbackCover f U) (coefficientPresheaf G)) :=
  let b := orderedPullback φ f hf U α
  HomologicalComplex.Hom.mk (fun n => b.app (SemiSimplexCategory.mk n)) (by
    intro n m h
    change n + 1 = m at h
    subst m
    change b.app _ ≫ (ModuleCat.restrictScalars φ).map
      ((cechComplex (pullbackCover f U) (coefficientPresheaf G)).d n (n + 1)) =
      (cechComplex U (coefficientPresheaf F)).d n (n + 1) ≫ b.app _
    simp only [cechComplex, CochainComplex.of_d, differential, Functor.map_sum,
      Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    exact Finset.sum_congr rfl fun i _ => congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
      (b.naturality (coface i)).symm)

theorem cechPullback_apply {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) (n : ℕ)
    (x : (cechComplex U (coefficientPresheaf F)).X n) (e : Fin (n + 1) ↪o Idx) :
    (cechPullback φ f hf U α).f n x e =
      G.presheaf.map (pullbackToIntersection f U e).op (α.app (tupleOpen U e) (x e)) := rfl

/-- Pullback on global sections of a coefficient map to the pushforward. -/
def sectionsPullback {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    (sectionsFunctor X).obj F ⟶ (ModuleCat.restrictScalars.{u} φ).obj ((sectionsFunctor Y).obj G) :=
  (sectionsFunctor X).map α ≫ (pushforwardSectionsIso φ f hf).hom.app G

@[simp]
theorem sectionsPullback_apply {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) (x : (sectionsFunctor X).obj F) :
    sectionsPullback φ f hf α x = α.app ⊤ x := rfl

end Pullback

section Comparison

open HomologicalComplex

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {Idx : Type u} [Preorder Idx] (U : Idx → X.left.Opens)

/-- The Čech complex with coefficients in a sheaf of modules. -/
abbrev SheafCech (F : X.left.Modules) := cechComplex U (coefficientPresheaf F)

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf morphism acts on the ordered intersections. -/
def sheafCechFunctor : X.left.Modules ⥤ CochainComplex (ModuleCat.{u} A) ℕ where
  obj F := SheafCech U F
  map α := cechMap U (coefficientPresheafMap α)
  map_id F := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp α β := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance : (sheafCechFunctor U).Additive where
  map_add := by
    intros
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The degree-zero augmentation is restriction of a global section to each
member of the cover. -/
def sectionAugmentation (F : X.left.Modules) :
    (sectionsFunctor X).obj F ⟶ (SheafCech U F).X 0 :=
  (ModuleCat.restrictScalarsCongr (groundRingHomOpen_top X).symm).hom.app (F.val.obj (op ⊤)) ≫
    ModuleCat.ofHom (X := localSections F ⊤) (Y := (SheafCech U F).X 0)
      (LinearMap.pi fun e => ((coefficientPresheaf F).map (tupleOpen U e).leTop.op).hom)

@[simp]
theorem sectionAugmentation_apply (F : X.left.Modules)
    (x : (sectionsFunctor X).obj F) (e : Fin 1 ↪o Idx) :
    sectionAugmentation U F x e = F.presheaf.map (tupleOpen U e).leTop.op x := rfl

theorem sectionAugmentation_naturality {F G : X.left.Modules} (α : F ⟶ G) :
    (sectionsFunctor X).map α ≫ sectionAugmentation U G =
      sectionAugmentation U F ≫ ((sheafCechFunctor U).map α).f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext e
  exact (PresheafOfModules.naturality_apply α.val (tupleOpen U e).leTop.op x).symm

/-- Evaluation with its usual structure-ring coefficients. -/
def openEvaluation {S : Scheme.{u}} (W : S.Opens) :
    S.Modules ⥤ ModuleCat.{u} Γ(S, W) :=
  SheafOfModules.evaluation.{u} S.ringCatSheaf (op W)

instance {S : Scheme.{u}} (W : S.Opens) : (openEvaluation W).Additive where
  map_add := by
    intros
    ext x
    rfl

instance {S : Scheme.{u}} (W : S.Opens) : PreservesFiniteLimits (openEvaluation W) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation.{u} S.ringCatSheaf (op W)))

/-- Acyclicity for evaluation at intersections of nonempty finite families.
The intersection itself is permitted to be the empty open. -/
def IntersectionAcyclic (F : X.left.Modules) : Prop :=
  ∀ (p : ℕ) (e : Fin (p + 1) ↪o Idx) (q : ℕ), 0 < q →
    IsZero (((openEvaluation (tupleOpen U e)).rightDerived q).obj F)

/-- The ordered Čech double complex of a coefficient complex, with the Čech
degree first and the resolution degree second. -/
def resolutionDouble (K : CochainComplex X.left.Modules ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip (((sheafCechFunctor U).mapHomologicalComplex (.up ℕ)).obj K)

abbrev intEmbedding := ComplexShape.embeddingUpIntGE 0

/-- Extend a first-quadrant double complex by zero in both directions. -/
def extendDouble (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ)) :
    HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ) :=
  let L := (((intEmbedding.extendFunctor (ModuleCat.{u} A)).mapHomologicalComplex (.up ℕ))).obj K
  L.extend intEmbedding

def doubleComponentIso (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ))
    (p q : ℕ) :
    (((extendDouble K).X (p : ℤ)).X (q : ℤ)) ≅ (K.X p).X q :=
  let L := (((intEmbedding.extendFunctor (ModuleCat.{u} A)).mapHomologicalComplex (.up ℕ))).obj K
  (HomologicalComplex.eval _ _ (q : ℤ)).mapIso (L.extendXIso intEmbedding (by simp [intEmbedding])) ≪≫
    (K.X p).extendXIso intEmbedding (by simp [intEmbedding])

variable {F : X.left.Modules}

/-- The two canonical augmentations into the total cochain complex of the
resolution. Their components in nonnegative degrees determine both maps. -/
def IsComparisonFromResolution (I : InjectiveResolution F) (n : ℕ)
    (e : (cohomology X n).obj F ≅ (SheafCech U F).homology n) : Prop :=
  let K := resolutionDouble U I.cocomplex
  let D := extendDouble K
  let G := ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let C := SheafCech U F
  let T := D.total (.up ℤ)
  ∃ (a : G.extend intEmbedding ⟶ T) (b : C.extend intEmbedding ⟶ T),
    QuasiIso a ∧ QuasiIso b ∧
    (∀ q : ℕ, a.f (q : ℤ) =
      (G.extendXIso intEmbedding (by simp [intEmbedding])).hom ≫
        sectionAugmentation U (I.cocomplex.X q) ≫
        (doubleComponentIso K 0 q).inv ≫ D.ιTotal (.up ℤ) 0 (q : ℤ) (q : ℤ) (by
          change 0 + (q : ℤ) = q
          simp)) ∧
    (∀ p : ℕ, b.f (p : ℤ) =
      (C.extendXIso intEmbedding (by simp [intEmbedding])).hom ≫
        ((sheafCechFunctor U).map (I.ι.f 0)).f p ≫
        (doubleComponentIso K p 0).inv ≫ D.ιTotal (.up ℤ) (p : ℤ) 0 (p : ℤ) (by
          change (p : ℤ) + 0 = p
          simp)) ∧
    e.hom ≫ (C.extendHomologyIso intEmbedding (by simp [intEmbedding])).inv ≫ homologyMap b (n : ℤ) =
      (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
        (G.extendHomologyIso intEmbedding (by simp [intEmbedding])).inv ≫ homologyMap a (n : ℤ)

/-- Degree zero identifies with gluing actual sections, even without acyclicity. -/
def DegreeZeroComparison : Prop :=
  ∀ {A : Type u} [CommRing A] (X : SchemeOverRing A)
    {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens), (⨆ i, U i) = ⊤ →
    ∃ e : ∀ F : X.left.Modules,
        (cohomology X 0).obj F ≅ (SheafCech U F).homology 0,
      ∀ {F G : X.left.Modules} (α : F ⟶ G),
        (cohomology X 0).map α ≫ (e G).hom =
          (e F).hom ≫ homologyMap ((sheafCechFunctor U).map α) 0

/-- A family of comparisons for all finite ordered covers and acyclic sheaves. -/
def ComparisonFamily :=
  ∀ {A : Type u} [CommRing A] (X : SchemeOverRing A)
    {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens),
    (⨆ i, U i) = ⊤ → ∀ (F : X.left.Modules), IntersectionAcyclic U F → ∀ n : ℕ,
      (cohomology X n).obj F ≅ (SheafCech U F).homology n

/-- The acyclic-cover comparison and its compatibility with coefficient maps
and with the pullback of an ordered cover. A lift is only needed when computing
a pullback as a map of the given injective section complexes. -/
def Comparison : Prop :=
  ∃ e : ComparisonFamily.{u},
    (∀ {A : Type u} [CommRing A] (X : SchemeOverRing A)
      {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens)
      (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) (hF : IntersectionAcyclic U F)
      (I : InjectiveResolution F) (n : ℕ),
        IsComparisonFromResolution U I n (e X U hU F hF n)) ∧
    (∀ {A : Type u} [CommRing A] (X : SchemeOverRing A)
      {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens)
      (hU : (⨆ i, U i) = ⊤) {F G : X.left.Modules} (α : F ⟶ G)
      (hF : IntersectionAcyclic U F) (hG : IntersectionAcyclic U G) (n : ℕ),
        (cohomology X n).map α ≫ (e X U hU G hG n).hom =
          (e X U hU F hF n).hom ≫ homologyMap ((sheafCechFunctor U).map α) n) ∧
    (∀ {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}
      {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens)
      (hU : (⨆ i, U i) = ⊤) (φ : A →+* B) (f : Y.left ⟶ X.left)
      (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
      {F : X.left.Modules} {G : Y.left.Modules}
      (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
      (hF : IntersectionAcyclic U F) (hG : IntersectionAcyclic (pullbackCover f U) G)
      (I : InjectiveResolution F) (J : InjectiveResolution G)
      (l : I.cocomplex ⟶ ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj J.cocomplex),
      I.ι.f 0 ≫ l.f 0 = α ≫ (Scheme.Modules.pushforward f).map (J.ι.f 0) →
      ∀ n : ℕ,
        let R := ModuleCat.restrictScalars.{u} φ
        let V := pullbackCover f U
        let hV : (⨆ i, V i) = ⊤ := f.iSup_preimage_eq_top hU
        derivedMapOfLift φ f hf I J l n ≫ R.map (e Y V hV G hG n).hom =
          (e X U hU F hF n).hom ≫ homologyMap (cechPullback φ f hf U α) n ≫
            (restrictCohomologyIso φ (SheafCech V G) n).inv)

end Comparison

end LinearAlgebraicGroups.Specs.OrderedCechComparison
