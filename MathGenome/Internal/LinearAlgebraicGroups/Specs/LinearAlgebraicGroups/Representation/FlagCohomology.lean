import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.IsogenyFlagComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FormalCharacters
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.LinearAlgebra.TensorProduct.Basis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u v
noncomputable section

namespace LinearAlgebraicGroups.Specs.FlagCohomology

open CentralIsogenies (IsCentralIsogeny characterPullback)
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open FlagLineBundle (OppositeBorelPair BorelProjection AssociatedBundle affineLine linePoint)
open IsogenyFlagComparison (Restrictions)
open QuotientEmbedding (Presentation)

/-- Sections over any family of points of the flag. Restriction along a morphism
of families is precomposition. -/
def SectionsOver {k : Type u} [Field k] {Y E T : SchemeOver k}
    (π : E ⟶ Y) (j : T ⟶ Y) :=
  { s : T ⟶ E // s ≫ π = j }

variable {k : Type u} [Field k] {Y E T S : SchemeOver k}

def SectionsOver.restrict {π : E ⟶ Y} {j : T ⟶ Y} (v : S ⟶ T) (s : SectionsOver π j) :
    SectionsOver π (v ≫ j) :=
  ⟨v ≫ s.val, by rw [Category.assoc, s.property]⟩

/-- A central torus point in the maximal torus fixes each flag and scales the
fiber by the character used in the associated bundle. The formula is on every
test algebra and uses the trivialization over the quotient torsor. -/
def CentralScalarAction : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    (p : BorelProjection P) (χ : Character P.torus.group)
    (L : AssociatedBundle Q a p χ),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀ (R : TestAlgebra k) (t : Points P.torus.group.X R)
      (g : Points G.val.X R) (z : R),
      Centralizes (𝟙 G.val) (t ≫ P.torus.inclusion.hom.hom) →
      lift (t ≫ P.torus.inclusion.hom.hom) (g ≫ Q.projection) ≫ a.smul =
          g ≫ Q.projection ∧
      lift (t ≫ P.torus.inclusion.hom.hom)
          (prod.lift g (linePoint R z) ≫ L.trivialization) ≫ L.action.smul =
        prod.lift g (linePoint R (characterValue χ R t * z)) ≫ L.trivialization

/-- Over a central isogeny, the comparison identifies sections over every
family of flags and commutes with restriction. The maps are induced by the
equivariant bundle isomorphism preserving the torsor fiber coordinate. -/
def CentralSectionComparison : Prop :=
  ∀ {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val), IsCentralIsogeny f → ∀ r : Restrictions f P' P,
    ∀ (p' : BorelProjection P') (p : BorelProjection P)
      (χ : Character P.torus.group)
      (Q' : Presentation P'.negative) (Q : Presentation P.negative)
      (a' : ModObj G'.val.X Q'.scheme) (a : ModObj G.val.X Q.scheme),
      μ[G'.val.X] ≫ Q'.projection = (𝟙 G'.val.X ⊗ₘ Q'.projection) ≫ a'.smul →
      μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
      ∀ (L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ))
        (L : AssociatedBundle Q a p χ),
        ∃ (e : Q'.scheme ≅ Q.scheme) (m : L'.total ≅ L.total),
          Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection ∧
          a'.smul ≫ e.hom = (f.hom.hom ⊗ₘ e.hom) ≫ a.smul ∧
          m.hom ≫ L.projection = L'.projection ≫ e.hom ∧
          L'.trivialization ≫ m.hom =
            prod.map f.hom.hom (𝟙 (affineLine k)) ≫ L.trivialization ∧
          L'.action.smul ≫ m.hom = (f.hom.hom ⊗ₘ m.hom) ≫ L.action.smul ∧
          ∃ E : ∀ {T : SchemeOver k} (j : T ⟶ Q'.scheme),
              SectionsOver L'.projection j ≃ SectionsOver L.projection (j ≫ e.hom),
            (∀ {T : SchemeOver k} (j : T ⟶ Q'.scheme) (s : SectionsOver L'.projection j),
              (E j s).val = s.val ≫ m.hom) ∧
            ∀ {T S : SchemeOver k} (j : T ⟶ Q'.scheme) (v : S ⟶ T)
              (s : SectionsOver L'.projection j),
              (E (v ≫ j) (s.restrict v)).val = v ≫ (E j s).val

section DerivedCohomology

/-- Schemes over a commutative ring, used also for scalar extension to test algebras. -/
abbrev SchemeOverRing (A : Type u) [CommRing A] := Over (Spec (CommRingCat.of A))

variable {k : Type u} [CommRing k] (X : SchemeOverRing k)

/-- The scalar map from the base field to global regular functions. -/
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

/-- The module of sections on an open, regarded as a module over the base field. -/
abbrev localSections (F : X.left.Modules) (U : X.left.Opens) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (groundRingHomOpen X U)).obj (F.val.obj (op U))

private theorem localScalars_comp {U V : X.left.Opens} (i : V ⟶ U) :
    groundRingHomOpen X V =
      (X.left.ringCatSheaf.obj.map i.op).hom.comp (groundRingHomOpen X U) := by
  unfold groundRingHomOpen
  ext r
  change (X.left.presheaf.map V.leTop.op) (groundRingHom X r) =
    (X.left.presheaf.map U.leTop.op ≫ X.left.presheaf.map i.op) (groundRingHom X r)
  rw [← X.left.presheaf.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def localRestriction (F : X.left.Modules) {U V : X.left.Opens} (i : V ⟶ U) :
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
ground field through the structural morphism. -/
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

/-- A finite Zariski cover all of whose nonempty finite intersections are
affine. The intersection indexed by the empty set need not be affine. -/
def HasFiniteAffineCover : Prop :=
  ∃ (Idx : Type u) (_ : Fintype Idx) (U : Idx → X.left.Opens),
    (⨆ i, U i) = ⊤ ∧
    ∀ (s : Finset Idx), s.Nonempty → IsAffineOpen (⨅ i ∈ (s : Set Idx), U i)

/-- Proper flags admit the finite affine covers used for Čech cohomology. -/
def FiniteAffineCover : Prop :=
  ∀ {k : Type u} [Field k] (X : SchemeOver k), IsProper X.hom → HasFiniteAffineCover X

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

private def restrictCohomologyIso (φ : A →+* B)
    (C : CochainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    (ModuleCat.restrictScalars.{u} φ).obj (C.homology n) ≅
      ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _ |>.obj C).homology n := by
  change (ModuleCat.restrictScalars.{u} φ).obj ((C.sc n).homology) ≅
    ((C.sc n).map (ModuleCat.restrictScalars.{u} φ)).homology
  exact ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars.{u} φ)).symm

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
    let ΓX := (sectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)
    let ΓY := (sectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℕ)
    let liftType := I.cocomplex ⟶ (P.mapHomologicalComplex _).obj J.cocomplex
    let lifts := fun l : liftType => I.ι.f 0 ≫ l.f 0 = α ≫ P.map (J.ι.f 0)
    (∃ l : liftType, lifts l) ∧
    ∀ l : liftType, lifts l →
      let β : ΓX.obj ((P.mapHomologicalComplex _).obj J.cocomplex) ⟶
          ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj (ΓY.obj J.cocomplex) :=
        HomologicalComplex.Hom.mk
          (fun i => (pushforwardSectionsIso φ f hf).hom.app (J.cocomplex.X i))
          (fun i j _ => (pushforwardSectionsIso φ f hf).hom.naturality (J.cocomplex.d i j))
      m = (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
        HomologicalComplex.homologyMap (ΓX.map l ≫ β) n ≫
        (restrictCohomologyIso φ (ΓY.obj J.cocomplex) n).inv ≫
        (ModuleCat.restrictScalars.{u} φ).map (J.isoRightDerivedObj (sectionsFunctor Y) n).inv

end CohomologyMaps

section Cech

open CategoryTheory.Preadditive
open scoped Simplicial BigOperators

variable {k : Type u} [CommRing k] {D : Type v} [CompleteLattice D]
    {Idx : Type u} [Preorder Idx] (U : Idx → D) (P : Dᵒᵖ ⥤ ModuleCat.{u} k)

/-- In the ordered Čech complex each intersection is indexed by a strictly
increasing tuple of members of the cover. -/
def tupleOpen {n : ℕ} (e : Fin (n + 1) ↪o Idx) : D := ⨅ j, U (e j)

private theorem tupleOpen_le {n m : ℕ} (e : Fin (m + 1) ↪o Idx)
    (f : Fin (n + 1) ↪o Fin (m + 1)) : tupleOpen U e ≤ tupleOpen U (f.trans e) :=
  le_iInf fun j => iInf_le _ (f j)

private abbrev term (n : ℕ) : Type u :=
  ∀ e : Fin (n + 1) ↪o Idx, P.obj (op (tupleOpen U e))

private def mapTerm {n m : SemiSimplexCategory} (f : n ⟶ m) :
    ModuleCat.of k (term U P n.len) ⟶ ModuleCat.of k (term U P m.len) :=
  ModuleCat.ofHom <| LinearMap.pi fun e =>
    (P.map (homOfLE (tupleOpen_le U e (SemiSimplexCategory.homEquiv f))).op).hom ∘ₗ
      LinearMap.proj ((SemiSimplexCategory.homEquiv f).trans e)

private def orderedCochains : SemiSimplexCategory ⥤ ModuleCat.{u} k where
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

private def coface {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ₛ ⟶ ⦋n + 1⦌ₛ :=
  SemiSimplexCategory.homEquiv.symm i.succAboveOrderEmb

private theorem map_coface {n : ℕ} (i : Fin (n + 2)) :
    SemiSimplexCategory.toSimplexCategory.map (coface i) = SimplexCategory.δ i := rfl

private def differential (n : ℕ) :
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
private def orderedCochainsMap {P' : Dᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ P') :
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

/-- The ordered cochain complex of a finite cover has no terms or cohomology
at or above the number of opens in the cover. -/
def CechBounded : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [CompleteLattice D]
    {Idx : Type u} [Preorder Idx] [Fintype Idx] (U : Idx → D)
    (P : Dᵒᵖ ⥤ ModuleCat.{u} k) (n : ℕ), Fintype.card Idx ≤ n →
    IsZero ((cechComplex U P).homology n)

end Cech

/-- The ordered Čech complex computes cohomology on a finite affine cover
with affine intersections. -/
def AffineCechComparison : Prop :=
  ∀ {A : Type u} [CommRing A] (X : SchemeOverRing A),
    ∀ {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens),
      (⨆ i, U i) = ⊤ →
      (∀ s : Finset I, s.Nonempty → IsAffineOpen (⨅ i ∈ (s : Set I), U i)) →
      ∀ n : ℕ, ∃ e : ∀ (F : X.left.Modules)
          (_ : (F : SheafOfModules X.left.ringCatSheaf).IsQuasicoherent),
          (cohomology X n).obj F ≅ (cechComplex U (coefficientPresheaf (X := X) F)).homology n,
        ∀ {F F' : X.left.Modules}
          (hF : (F : SheafOfModules X.left.ringCatSheaf).IsQuasicoherent)
          (hF' : (F' : SheafOfModules X.left.ringCatSheaf).IsQuasicoherent)
          (f : F ⟶ F'),
          (cohomology X n).map f ≫ (e F' hF').hom = (e F hF).hom ≫
            HomologicalComplex.homologyMap (cechMap U (coefficientPresheafMap (X := X) f)) n

section DescentSheaf

set_option backward.isDefEq.respectTransparency false

/-- The structural sheaf, regarded as a module over itself. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Pullback of regular functions as a map of module sheaves on the target. -/
def pullbackRegular {X Y : Scheme.{u}} (f : X ⟶ Y) :
    structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (structureModule X) := by
  let M := (Scheme.Modules.pushforward f).obj (structureModule X)
  refine M.unitHomEquiv.symm ?_
  refine PresheafOfModules.sectionsMk (M := M.val)
    (fun U => (1 : Γ(X, f ⁻¹ᵁ U.unop))) ?_
  intro U V i
  change X.presheaf.map ((Opens.map f.base).map i.unop).op (1 : Γ(X, f ⁻¹ᵁ U.unop)) = _
  exact map_one (X.presheaf.map ((Opens.map f.base).map i.unop).op).hom

private abbrev restrictedRegular {X : Scheme.{u}} (c : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map U.leTop.op c

/-- Multiplication by a regular function as an endomorphism of the structure module. -/
def multiplyRegular {X : Scheme.{u}} (c : Γ(X, ⊤)) : structureModule X ⟶ structureModule X := by
  refine (structureModule X).unitHomEquiv.symm ?_
  refine PresheafOfModules.sectionsMk (M := (structureModule X).val)
    (fun U => restrictedRegular c U.unop) ?_
  intro U V i
  change (X.presheaf.map U.unop.leTop.op ≫ X.presheaf.map i) c =
    X.presheaf.map V.unop.leTop.op c
  rw [← X.presheaf.map_comp]
  rfl

private def overPullbackRegular {X Y Z : Scheme.{u}} (q : X ⟶ Y) (r : Z ⟶ Y)
    (b : Z ⟶ X) (hb : b ≫ q = r) :
    (Scheme.Modules.pushforward q).obj (structureModule X) ⟶
      (Scheme.Modules.pushforward r).obj (structureModule Z) :=
  (Scheme.Modules.pushforward q).map (pullbackRegular b) ≫
    (Scheme.Modules.pushforwardComp b q).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr hb).hom.app _

/-- Difference of the two descent restrictions, with the twist on the
restriction along the first projection. -/
def covarianceMap {X Y Z : Scheme.{u}} (q : X ⟶ Y) (r : Z ⟶ Y)
    (b₀ b₁ : Z ⟶ X) (hb₀ : b₀ ≫ q = r) (hb₁ : b₁ ≫ q = r) (c : Γ(Z, ⊤)) :
    (Scheme.Modules.pushforward q).obj (structureModule X) ⟶
      (Scheme.Modules.pushforward r).obj (structureModule Z) :=
  overPullbackRegular q r b₁ hb₁ -
    overPullbackRegular q r b₀ hb₀ ≫ (Scheme.Modules.pushforward r).map (multiplyRegular c)

/-- The sheaf of regular functions on X satisfying twisted covariance
along a pair of maps over Y. -/
def covarianceSheaf {X Y Z : Scheme.{u}} (q : X ⟶ Y) (r : Z ⟶ Y)
    (b₀ b₁ : Z ⟶ X) (hb₀ : b₀ ≫ q = r) (hb₁ : b₁ ≫ q = r) (c : Γ(Z, ⊤)) :
    Y.Modules :=
  kernel (covarianceMap q r b₀ b₁ hb₀ hb₁ c)

/-- Sections on an open are the linear kernel of the difference of the two
twisted restrictions on that open. -/
def covarianceSheafSectionsIso {X Y Z : Scheme.{u}} (q : X ⟶ Y) (r : Z ⟶ Y)
    (b₀ b₁ : Z ⟶ X) (hb₀ : b₀ ≫ q = r) (hb₁ : b₁ ≫ q = r) (c : Γ(Z, ⊤))
    (U : Y.Opens) :
    let ev := SheafOfModules.evaluation.{u} Y.ringCatSheaf (op U)
    ev.obj (covarianceSheaf q r b₀ b₁ hb₀ hb₁ c) ≅
      ModuleCat.of _ (ev.map (covarianceMap q r b₀ b₁ hb₀ hb₁ c)).hom.ker := by
  let ev := SheafOfModules.evaluation.{u} Y.ringCatSheaf (op U)
  letI : ev.Additive := ⟨by intros; ext x; rfl⟩
  exact PreservesKernel.iso ev _ ≪≫ ModuleCat.kernelIsoKer _

/-- The regular function χ(b⁻¹) on the double overlap G × B⁻. -/
def flagTransition {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} (p : BorelProjection P) (χ : Character P.torus.group) :
    Γ((G.val.X ⨯ P.negative.group.X).left, ⊤) := by
  let r : (G.val.X ⨯ P.negative.group.X) ⟶ _ :=
    (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X)⁻¹ ≫
      (p.projection ≫ χ).hom.hom
  let M := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
  exact ((Scheme.ΓSpecIso (CommRingCat.of M)).inv ≫ r.left.appTop)
    (MonoidAlgebra.single DiagonalizableGroups.integerGenerator (1 : k))

/-- The torsor and its descent relation, with the transition function on the
double overlap. -/
structure CovarianceData {A : Type u} [CommRing A] (Y : SchemeOverRing A) where
  torsor : SchemeOverRing A
  overlap : SchemeOverRing A
  projection : torsor ⟶ Y
  overlapProjection : overlap ⟶ Y
  first : overlap ⟶ torsor
  second : overlap ⟶ torsor
  fst_w : first ≫ projection = overlapProjection
  snd_w : second ≫ projection = overlapProjection
  multiplier : Γ(overlap.left, ⊤)

namespace CovarianceData

variable {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B}

def covariance (D : CovarianceData X) :=
  covarianceMap D.projection.left D.overlapProjection.left D.first.left D.second.left
    (congrArg Over.Hom.left D.fst_w) (congrArg Over.Hom.left D.snd_w) D.multiplier

abbrev sheaf (D : CovarianceData X) : X.left.Modules :=
  kernel D.covariance

abbrev inclusion (D : CovarianceData X) := kernel.ι D.covariance

/-- The map on the ambient sheaves of regular functions, induced by a map of
torsors over a map of flags. -/
def pullFunctions (D : CovarianceData X) (D' : CovarianceData Y)
    (f : Y.left ⟶ X.left) (g : D'.torsor.left ⟶ D.torsor.left)
    (h : g ≫ D.projection.left = D'.projection.left ≫ f) :
    (Scheme.Modules.pushforward D.projection.left).obj (structureModule D.torsor.left) ⟶
      (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward D'.projection.left).obj (structureModule D'.torsor.left)) :=
  overPullbackRegular D.projection.left (D'.projection.left ≫ f) g h ≫
    (Scheme.Modules.pushforwardComp D'.projection.left f).inv.app _

/-- A coefficient map is induced by pullback of the covariant functions
along the indicated map of torsors. -/
def IsPullbackMap (D : CovarianceData X) (D' : CovarianceData Y)
    (f : Y.left ⟶ X.left) (g : D'.torsor.left ⟶ D.torsor.left)
    (h : g ≫ D.projection.left = D'.projection.left ≫ f)
    (m : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D'.sheaf) : Prop :=
  m ≫ (Scheme.Modules.pushforward f).map D'.inclusion =
    D.inclusion ≫ D.pullFunctions D' f g h

end CovarianceData

/-- The flag torsor and the inverse-character covariance data. -/
def flagLineData {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group)
    (h : IsPullback prod.fst (HomogeneousQuotient.rightMultiplication P.negative)
      Q.projection Q.projection) : CovarianceData Q.scheme where
  torsor := G.val.X
  overlap := G.val.X ⨯ P.negative.group.X
  projection := Q.projection
  overlapProjection := prod.fst ≫ Q.projection
  first := prod.fst
  second := HomogeneousQuotient.rightMultiplication P.negative
  fst_w := rfl
  snd_w := h.w.symm
  multiplier := flagTransition p χ

/-- Descent of the structure module on the quotient torsor with the
inverse-character covariance on its kernel pair. -/
abbrev flagLineSheaf {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group)
    (h : IsPullback prod.fst (HomogeneousQuotient.rightMultiplication P.negative)
      Q.projection Q.projection) : Q.scheme.left.Modules :=
  (flagLineData Q p χ h).sheaf

/-- Derived global sections of the character sheaf, with coefficients in k. -/
def flagCohomology {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group)
    (h : IsPullback prod.fst (HomogeneousQuotient.rightMultiplication P.negative)
      Q.projection Q.projection) (n : ℕ) : ModuleCat.{u} k :=
  (cohomology Q.scheme n).obj (flagLineSheaf Q p χ h)

/-- Restriction of a scheme over the field to an open. -/
abbrev openScheme {k : Type u} [Field k] (X : SchemeOver k) (U : X.left.Opens) :
    SchemeOver k := Over.mk (U.ι ≫ X.hom)

def openInclusion {k : Type u} [Field k] (X : SchemeOver k) (U : X.left.Opens) :
    openScheme X U ⟶ X := Over.homMk U.ι

private def openRestriction {k : Type u} [Field k] (X : SchemeOver k)
    {U V : X.left.Opens} (i : U ⟶ V) : openScheme X U ⟶ openScheme X V :=
  Over.homMk (X.left.homOfLE i.le) (by simp [← Category.assoc])

/-- The function obtained by pulling a local section back to the torsor and
reading its coordinate in the given trivialization. -/
def bundleSectionCoordinate {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {Q : Presentation P.negative}
    {a : ModObj G.val.X Q.scheme} {p : BorelProjection P} {χ : Character P.torus.group}
    (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens)
    (s : SectionsOver L.projection (openInclusion Q.scheme U)) :
    Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U) := by
  let V := Q.projection.left ⁻¹ᵁ U
  let q : openScheme G.val.X V ⟶ openScheme Q.scheme U :=
    Over.homMk (Q.projection.left ∣_ U) (by
      change (Q.projection.left ∣_ U) ≫ (U.ι ≫ Q.scheme.hom) = V.ι ≫ G.val.X.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w Q.projection])
  have w : openInclusion G.val.X V ≫ Q.projection = (q ≫ s.val) ≫ L.projection := by
    rw [Category.assoc, s.property]
    apply Over.OverMorphism.ext
    exact (morphismRestrict_ι Q.projection.left U).symm
  let t := L.trivializes.lift (openInclusion G.val.X V) (q ≫ s.val) w ≫
    (prod.snd : G.val.X ⨯ affineLine k ⟶ affineLine k)
  exact V.topIso.hom (((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
    t.left.appTop) Polynomial.X)

/-- The covariance kernel is the sheaf of sections of the specified
associated line bundle in its torsor coordinates. -/
def FlagLineSheafIdentification : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : IsPullback prod.fst (HomogeneousQuotient.rightMultiplication P.negative)
      Q.projection Q.projection) {a : ModObj G.val.X Q.scheme}
    (L : AssociatedBundle Q a p χ),
    let D := flagLineData Q p χ h
    (D.sheaf : SheafOfModules Q.scheme.left.ringCatSheaf).IsQuasicoherent ∧
    (∀ y : Q.scheme.left, ∃ U : Q.scheme.left.Opens, y ∈ U ∧
      Nonempty (D.sheaf.restrict U.ι ≅ structureModule U.toScheme)) ∧
    ∃ e : ∀ U : Q.scheme.left.Opens,
        Γ(D.sheaf, U) ≃ SectionsOver L.projection (openInclusion Q.scheme U),
      (∀ U x, bundleSectionCoordinate L U (e U x) = D.inclusion.app U x) ∧
      ∀ {U V : Q.scheme.left.Opens} (i : U ⟶ V) (x : Γ(D.sheaf, V)),
        (e U (D.sheaf.presheaf.map i.op x)).val = openRestriction Q.scheme i ≫ (e V x).val

/-- Finite dimensionality and boundedness of the cohomology of the character
line bundle on the projective flag. -/
def FlagCohomologyFinite : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : IsPullback prod.fst (HomogeneousQuotient.rightMultiplication P.negative)
      Q.projection Q.projection),
    (∀ n, FiniteDimensional k (flagCohomology Q p χ h n)) ∧
      ∃ N : ℕ, ∀ n ≥ N, IsZero (flagCohomology Q p χ h n)

end DescentSheaf

section ScalarExtension

variable {k K : Type u} [Field k] [CommRing K] [Algebra k K]

abbrev extendToAlgebra := ModuleCat.extendScalars.{u,u,u} (algebraMap k K)

instance scalarExtension_preservesFiniteLimits : PreservesFiniteLimits (extendToAlgebra (k := k) (K := K)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))

/-- The coefficient-level comparison for a base extension from a field. For a Čech
base-change theorem, the remaining geometric step is to identify the complex
on the extended flag with the scalar extension of the original complex. -/
def extendCohomologyIso (C : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (extendToAlgebra (k := k) (K := K)).obj (C.homology n) ≅
      ((extendToAlgebra (k := k) (K := K)).mapHomologicalComplex _ |>.obj C).homology n := by
  change (extendToAlgebra (k := k) (K := K)).obj ((C.sc n).homology) ≅
    ((C.sc n).map (extendToAlgebra (k := k) (K := K))).homology
  exact ((C.sc n).mapHomologyIso (extendToAlgebra (k := k) (K := K))).symm

end ScalarExtension

section GeometricScalarExtension

variable {k : Type u} [Field k] (R : TestAlgebra k)

/-- The actual scheme fiber product along Spec R → Spec k. For fields this is
the base change functor used for the flag quotient. -/
abbrev extendScheme : SchemeOver k ⥤ SchemeOverRing R :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))

abbrev extensionProjection (X : SchemeOver k) : ((extendScheme R).obj X).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k R)))

theorem extensionProjection_over (X : SchemeOver k) :
    extensionProjection R X ≫ X.hom =
      ((extendScheme R).obj X).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
  pullback.condition

@[reassoc]
theorem extensionProjection_natural {X Y : SchemeOver k} (f : X ⟶ Y) :
    ((extendScheme R).map f).left ≫ extensionProjection R Y =
      extensionProjection R X ≫ f.left :=
  pullback.lift_fst _ _ _

variable {X : SchemeOver k}

/-- Base change of both torsor maps and the transition function. -/
def CovarianceData.extend (D : CovarianceData X) :
    CovarianceData ((extendScheme R).obj X) where
  torsor := (extendScheme R).obj D.torsor
  overlap := (extendScheme R).obj D.overlap
  projection := (extendScheme R).map D.projection
  overlapProjection := (extendScheme R).map D.overlapProjection
  first := (extendScheme R).map D.first
  second := (extendScheme R).map D.second
  fst_w := by rw [← Functor.map_comp, D.fst_w]
  snd_w := by rw [← Functor.map_comp, D.snd_w]
  multiplier := (extensionProjection R D.overlap).appTop D.multiplier

/-- The scalar-extension comparison uses the pullback of sections on the
torsor and the canonical derived map. In particular the target sheaf is
identified with the pullback of the original coefficient sheaf. -/
structure CovarianceData.ScalarExtension (D : CovarianceData X) where
  coefficientMap : D.sheaf ⟶ (Scheme.Modules.pushforward (extensionProjection R X)).obj
    (D.extend R).sheaf
  pullsBack : D.IsPullbackMap (D.extend R) (extensionProjection R X)
    (extensionProjection R D.torsor) (extensionProjection_natural R D.projection).symm
    coefficientMap
  sheafIso : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (extensionProjection R X)).homEquiv
    _ _).symm coefficientMap)
  iso (n : ℕ) : (extendToAlgebra (k := k) (K := R)).obj ((cohomology X n).obj D.sheaf) ≅
    (cohomology ((extendScheme R).obj X) n).obj (D.extend R).sheaf
  induced (n : ℕ) : IsCohomologyMap (algebraMap k R) (extensionProjection R X)
    (extensionProjection_over R X) coefficientMap n
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ (iso n).hom)

end GeometricScalarExtension

section FlagCohomologyAction

open AdjointRepresentation (GroupPoints)
open RootWeightAction (act)
open scoped BigOperators

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}

abbrev FlagKernelPair (Q : Presentation P.negative) :=
  IsPullback prod.fst (HomogeneousQuotient.rightMultiplication P.negative)
    Q.projection Q.projection

/-- Scalar extension of flag cohomology, in particular for every field
extension. Arbitrary commutative test algebras also give the scalars on which
the rational action is evaluated. -/
def FlagCohomologyBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (R : TestAlgebra k),
    Nonempty ((flagLineData Q p χ h).ScalarExtension R)

private abbrev extensionAsSchemeOverField (R : TestAlgebra k) (X : SchemeOver k) : SchemeOver k :=
  (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj ((extendScheme R).obj X)

private def projectionToOriginal (R : TestAlgebra k) (X : SchemeOver k) :
    extensionAsSchemeOverField R X ⟶ X :=
  Over.homMk (extensionProjection R X) (extensionProjection_over R X)

private def projectionToTestScheme (R : TestAlgebra k) (X : SchemeOver k) :
    extensionAsSchemeOverField R X ⟶ (testSpec k).obj (op R) :=
  Over.homMk ((extendScheme R).obj X).hom

/-- Translation by an R-point, on the scheme over R. -/
def pointTranslation {H X : SchemeOver k} (a : H ⊗ X ⟶ X)
    (R : TestAlgebra k) (g : Points H R) :
    ((extendScheme R).obj X).left ⟶ ((extendScheme R).obj X).left :=
  let t := lift (projectionToTestScheme R X ≫ g) (projectionToOriginal R X) ≫ a
  pullback.lift t.left ((extendScheme R).obj X).hom (Over.w t)

theorem pointTranslation_over {H X : SchemeOver k} (a : H ⊗ X ⟶ X)
    (R : TestAlgebra k) (g : Points H R) :
    pointTranslation a R g ≫ ((extendScheme R).obj X).hom =
      ((extendScheme R).obj X).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (CommRingCat.of R)) := by
    exact Spec.map_id _
  rw [hid, Category.comp_id]
  exact pullback.lift_snd _ _ _

abbrev CohomologyIndex (h : FlagKernelPair Q) (n : ℕ) : Type u :=
  ULift.{u} (Fin (Module.finrank k (flagCohomology Q p χ h n)))

abbrev CohomologyBasis (h : FlagKernelPair Q) (n : ℕ) :=
  Module.Basis (CohomologyIndex (p := p) (χ := χ) h n) k (flagCohomology Q p χ h n)

set_option backward.isDefEq.respectTransparency false in
/-- Extend a cohomology basis to a basis over the test algebra. -/
def extendedCoordinates {I : Type u} [Fintype I] (R : TestAlgebra k)
    {V : ModuleCat.{u} k} (b : Module.Basis I k V) :
    (extendToAlgebra (k := k) (K := R)).obj V ≃ₗ[R] (I → R) := by
  letI : Algebra k R := (algebraMap k R).toAlgebra
  exact (b.baseChange R).equivFun

/-- Coordinate description of the action on cohomology induced by left
translation of the torsor. Pullback is along the inverse point, so the
formula is the left action on the associated line bundle. -/
def IsFlagCohomologyAction (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme) (n : ℕ)
    (b : CohomologyBasis (p := p) (χ := χ) h n)
    (ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n)) : Prop :=
  ∀ (R : TestAlgebra k) (g : GroupPoints G.val R)
    (E : (flagLineData Q p χ h).ScalarExtension R),
    let D := (flagLineData Q p χ h).extend R
    let f := pointTranslation a.smul R g⁻¹
    let t := pointTranslation μ[G.val.X] R g⁻¹
    let coord := (extendedCoordinates R b).toLinearMap.comp (E.iso n).inv.hom
    ∃ (w : t ≫ D.projection.left = D.projection.left ≫ f)
      (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D.sheaf)
      (m : (cohomology ((extendScheme R).obj Q.scheme) n).obj D.sheaf ⟶
        (cohomology ((extendScheme R).obj Q.scheme) n).obj D.sheaf),
      D.IsPullbackMap D f t w α ∧
      IsCohomologyMap (RingHom.id R) f (pointTranslation_over a.smul R g⁻¹) α n
        (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv) ∧
      ∀ v, coord (m v) = act ρ R g (coord v)

/-- The rational representations on all cohomology groups, expressed in
finite bases using the same general linear functor as the formal characters. -/
def FlagCohomologyRepresentation : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀ n, ∃ (b : CohomologyBasis (p := p) (χ := χ) h n)
      (ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n)),
      IsFlagCohomologyAction h a n b ρ

/-- The signed sum of the integral characters in degrees below N. -/
def equivariantEulerCharacteristic (h : FlagKernelPair Q)
    (ρ : ∀ n, RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n))
    (N : ℕ) : MonoidAlgebra ℤ (Character P.torus.group) :=
  ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n • FormalCharacters.formalCharacter P.torus (ρ n)

/-- The sum defining the equivariant Euler characteristic stabilizes once
all the remaining cohomology groups vanish. -/
def EulerCharacteristicBound : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q)
    (ρ : ∀ n, RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n))
    (N M : ℕ), N ≤ M → (∀ n ≥ N, IsZero (flagCohomology Q p χ h n)) →
      equivariantEulerCharacteristic h ρ M = equivariantEulerCharacteristic h ρ N

/-- A central torus element acts on every degree by the value of the
linearizing character. This includes the restriction of the pulled-back
character to the central torus factor of a split central cover. -/
def CentralCohomologyScalarAction : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme)
    (n : ℕ) (b : CohomologyBasis (p := p) (χ := χ) h n)
    (ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n)),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    IsFlagCohomologyAction h a n b ρ →
    ∀ (R : TestAlgebra k) (t : GroupPoints P.torus.group R),
      Centralizes (𝟙 G.val) (t ≫ P.torus.inclusion.hom.hom) →
      ∀ v, act ρ R (t ≫ P.torus.inclusion.hom.hom) v = characterValue χ R t • v

/-- The flag isomorphism for a central isogeny induces the cohomology
isomorphism, intertwining the two rational actions through the isogeny. -/
def CentralCohomologyComparison : Prop :=
  ∀ {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val), IsCentralIsogeny f → ∀ r : Restrictions f P' P,
    ∀ (p' : BorelProjection P') (p : BorelProjection P) (χ : Character P.torus.group)
      (Q' : Presentation P'.negative) (Q : Presentation P.negative)
      (h' : FlagKernelPair Q') (h : FlagKernelPair Q)
      (a' : ModObj G'.val.X Q'.scheme) (a : ModObj G.val.X Q.scheme),
    μ[G'.val.X] ≫ Q'.projection = (𝟙 G'.val.X ⊗ₘ Q'.projection) ≫ a'.smul →
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀ (L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ))
      (L : AssociatedBundle Q a p χ),
    let D' := flagLineData Q' p' (characterPullback r.torus χ) h'
    let D := flagLineData Q p χ h
    ∃ (e : Q'.scheme ≅ Q.scheme)
      (w : Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection)
      (m : L'.total ⟶ L.total)
      (α : D.sheaf ⟶ (Scheme.Modules.pushforward e.hom.left).obj D'.sheaf),
      a'.smul ≫ e.hom = (f.hom.hom ⊗ₘ e.hom) ≫ a.smul ∧
      IsPullback m L'.projection L.projection e.hom ∧
      L'.trivialization ≫ m = prod.map f.hom.hom (𝟙 (affineLine k)) ≫ L.trivialization ∧
      L'.action.smul ≫ m = (f.hom.hom ⊗ₘ m) ≫ L.action.smul ∧
      D.IsPullbackMap D' e.hom.left f.hom.hom.left (congrArg Over.Hom.left w.symm) α ∧
      ∀ n, ∃ c : flagCohomology Q p χ h n ≅ flagCohomology Q' p' (characterPullback r.torus χ) h' n,
        IsCohomologyMap (RingHom.id k) e.hom.left
          (by simp) α n
          (c.hom ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).inv) ∧
        ∀ (b : CohomologyBasis (p := p) (χ := χ) h n)
          (b' : CohomologyBasis (p := p') (χ := characterPullback r.torus χ) h' n)
          (ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n))
          (ρ' : RootWeightAction.Representation G'.val
            (CohomologyIndex (p := p') (χ := characterPullback r.torus χ) h' n)),
          IsFlagCohomologyAction h a n b ρ → IsFlagCohomologyAction h' a' n b' ρ' →
          ∀ (R : TestAlgebra k) (g : GroupPoints G'.val R) v,
            let E := extendToAlgebra (k := k) (K := R)
            let C := fun x => extendedCoordinates R b' (E.map c.hom ((extendedCoordinates R b).symm x))
            C (act ρ R (g ≫ f.hom.hom) v) = act ρ' R g (C v)

end FlagCohomologyAction

/-- The degree-zero comparison is the natural comparison with the ordered
Čech complex, for every cover and every sheaf of modules. -/
def CechDegreeZeroComparison : Prop :=
  ∀ {A : Type u} [CommRing A] (X : SchemeOverRing A)
    {I : Type u} [LinearOrder I] (U : I → X.left.Opens), (⨆ i, U i) = ⊤ →
    ∃ e : ∀ (F : X.left.Modules),
        (cohomology X 0).obj F ≅ (cechComplex U (coefficientPresheaf (X := X) F)).homology 0,
      ∀ {F F' : X.left.Modules} (f : F ⟶ F'),
        (cohomology X 0).map f ≫ (e F').hom = (e F).hom ≫
          HomologicalComplex.homologyMap (cechMap U (coefficientPresheafMap (X := X) f)) 0

/-- The base change isomorphism in degree zero is given by pullback on the
quotient torsor under the identification with sections. -/
def FlagCohomologyZeroBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (R : TestAlgebra k),
    let D := flagLineData Q p χ h
    let Y := (extendScheme R).obj Q.scheme
    let f := extensionProjection R Q.scheme
    ∃ (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj (D.extend R).sheaf)
      (e : (extendToAlgebra (k := k) (K := R)).obj (flagCohomology Q p χ h 0) ≅
        (cohomology Y 0).obj (D.extend R).sheaf),
      D.IsPullbackMap (D.extend R) f (extensionProjection R D.torsor)
        (extensionProjection_natural R D.projection).symm α ∧
      (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _
        (e.hom ≫ ((cohomologyZero Y).app (D.extend R).sheaf).hom) =
      ((cohomologyZero Q.scheme).app D.sheaf).hom ≫ (sectionsFunctor Q.scheme).map α ≫
        (pushforwardSectionsIso (algebraMap k R) f (extensionProjection_over R Q.scheme)).hom.app
          (D.extend R).sheaf

/-- The equivariant bundle comparison supplies the coefficient isomorphism
on the flag schemes. Its contravariant map on derived sections is an
isomorphism in every degree. -/
def CentralCohomologyIsomorphism : Prop :=
  ∀ {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val), IsCentralIsogeny f → ∀ r : Restrictions f P' P,
    ∀ (p' : BorelProjection P') (p : BorelProjection P) (χ : Character P.torus.group)
      (Q' : Presentation P'.negative) (Q : Presentation P.negative)
      (h' : FlagKernelPair Q') (h : FlagKernelPair Q)
      (a' : ModObj G'.val.X Q'.scheme) (a : ModObj G.val.X Q.scheme),
    μ[G'.val.X] ≫ Q'.projection = (𝟙 G'.val.X ⊗ₘ Q'.projection) ≫ a'.smul →
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀ (L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ))
      (L : AssociatedBundle Q a p χ),
    let D' := flagLineData Q' p' (characterPullback r.torus χ) h'
    let D := flagLineData Q p χ h
    ∃ (e : Q'.scheme ≅ Q.scheme)
      (w : Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection)
      (m : L'.total ⟶ L.total)
      (α : D.sheaf ⟶ (Scheme.Modules.pushforward e.hom.left).obj D'.sheaf),
      a'.smul ≫ e.hom = (f.hom.hom ⊗ₘ e.hom) ≫ a.smul ∧
      IsPullback m L'.projection L.projection e.hom ∧
      L'.trivialization ≫ m = prod.map f.hom.hom (𝟙 (affineLine k)) ≫ L.trivialization ∧
      L'.action.smul ≫ m = (f.hom.hom ⊗ₘ m) ≫ L.action.smul ∧
      D.IsPullbackMap D' e.hom.left f.hom.hom.left (congrArg Over.Hom.left w.symm) α ∧
      IsIso α ∧
      ∀ n, ∃ c : flagCohomology Q p χ h n ≅ flagCohomology Q' p' (characterPullback r.torus χ) h' n,
        IsCohomologyMap (RingHom.id k) e.hom.left (by simp) α n
          (c.hom ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).inv)

/-- On the flag over any test algebra, the inverse translation by a central
torus point fixes the base and acts on cohomology by the positive character. -/
def CentralTranslationOnCohomology : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀ (R : TestAlgebra k) (t : AdjointRepresentation.GroupPoints P.torus.group R),
      Centralizes (𝟙 G.val) (t ≫ P.torus.inclusion.hom.hom) →
      let Y := (extendScheme R).obj Q.scheme
      let D := (flagLineData Q p χ h).extend R
      let g : AdjointRepresentation.GroupPoints G.val R := t ≫ P.torus.inclusion.hom.hom
      let f := pointTranslation a.smul R g⁻¹
      let b := pointTranslation μ[G.val.X] R g⁻¹
      f = 𝟙 Y.left ∧
      ∃ (w : b ≫ D.projection.left = D.projection.left ≫ f)
        (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D.sheaf),
        D.IsPullbackMap D f b w α ∧
        ∀ n, IsCohomologyMap (RingHom.id R) f
          (pointTranslation_over a.smul R g⁻¹) α n
          ((CharacterPairing.characterValue χ R t • 𝟙 ((cohomology Y n).obj D.sheaf)) ≫
            (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv)

section FlagCechScalarExtension

open scoped TensorProduct ChangeOfRings

/-- Inverse image commutes with the finite intersections in an ordered tuple. -/
theorem preimage_tupleOpen {X Y : Scheme.{u}} (f : Y ⟶ X)
    {I : Type u} [Preorder I] (U : I → X.Opens) {n : ℕ} (e : Fin (n + 1) ↪o I) :
    f ⁻¹ᵁ tupleOpen U e = tupleOpen (fun i => f ⁻¹ᵁ U i) e := by
  apply Opens.ext
  simp only [tupleOpen, Scheme.Hom.coe_preimage, Opens.coe_iInf, Set.preimage_iInter]

/-- Scalar extension on the ordered cochains of the flag cover, using the
pullback of the covariant functions on every tuple intersection. -/
def FlagCechBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (R : TestAlgebra k)
    {I : Type u} [Preorder I] [Finite I] (U : I → Q.scheme.left.Opens),
    (∀ {n : ℕ} (e : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U e)) →
    let D := flagLineData Q p χ h
    let E := extendToAlgebra (k := k) (K := R)
    let f := extensionProjection R Q.scheme
    let U' := fun i => f ⁻¹ᵁ U i
    let F := coefficientPresheaf D.sheaf
    let F' := coefficientPresheaf (D.extend R).sheaf
    ∃ (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj (D.extend R).sheaf)
      (c : (E.mapHomologicalComplex (.up ℕ)).obj (cechComplex U F) ≅ cechComplex U' F'),
      D.IsPullbackMap (D.extend R) f (extensionProjection R D.torsor)
        (extensionProjection_natural R D.projection).symm α ∧
      ∀ (n : ℕ) (e : Fin (n + 1) ↪o I) (x : (cechComplex U F).X n),
        c.hom.f n ((1 : R) ⊗ₜ[k,algebraMap k R] x) e =
          (F'.map (eqToHom (congrArg op (preimage_tupleOpen f U e))))
            (α.app (tupleOpen U e) (x e))

end FlagCechScalarExtension

/-- For each test algebra, inverse translation induces a linear action of its
group of points on the cohomology of the extended flag. -/
def FlagTranslationCohomologyMap : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀ (R : TestAlgebra k) (n : ℕ),
      let D := (flagLineData Q p χ h).extend R
      let Y := (extendScheme R).obj Q.scheme
      let H := (cohomology Y n).obj D.sheaf
      ∃ ρ : AdjointRepresentation.GroupPoints G.val R →* Module.End R H,
        ∀ g,
          let f := pointTranslation a.smul R g⁻¹
          let t := pointTranslation μ[G.val.X] R g⁻¹
          ∃ (w : t ≫ D.projection.left = D.projection.left ≫ f)
            (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D.sheaf),
            D.IsPullbackMap D f t w α ∧
            IsCohomologyMap (RingHom.id R) f (pointTranslation_over a.smul R g⁻¹) α n
              (ModuleCat.ofHom (ρ g) ≫ (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl H).inv)

end LinearAlgebraicGroups.Specs.FlagCohomology
