import Specs.LinearAlgebraicGroups.Representation.FlagCohomology
import LinearAlgebraicGroups.Flag.GrassmannianCharts
import LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
import LinearAlgebraicGroups.Cohomology.FlatPullback
import LinearAlgebraicGroups.Representation.IsogenyFlagComparison
import LinearAlgebraicGroups.Representation.FlagLineBundle
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open scoped BigOperators

namespace LinearAlgebraicGroups.Representation.FlagCohomology

open _root_.LinearAlgebraicGroups.Specs
open Specs.FlagCohomology
open Specs.FlagLineBundle (linePoint affineLine AssociatedBundle OppositeBorelPair BorelProjection)
open Specs.CharacterDescent (Character)
open Specs.QuotientEmbedding (Presentation)
open Specs.IsogenyFlagComparison (FlagBundleComparison)

noncomputable section

/-- The bundle comparison induces restriction-compatible maps on sections. -/
theorem centralSectionComparison_of_bundleComparison.{u}
    (bundle : FlagBundleComparison.{u}) : CentralSectionComparison.{u} := by
  intro k _ G' G P' P f hf r p' p χ Q' Q a' a ha' ha L' L
  obtain ⟨e, m, hq, ha, hp, ht, hm⟩ :=
    bundle f hf r p' p χ Q' Q a' a ha' ha L' L
  let : IsIso m := hp.isIso_fst_of_isIso
  refine ⟨e, asIso m, hq, ha, hp.w, ht, hm, ?_⟩
  have square : m ≫ L.projection = L'.projection ≫ e.hom := hp.w
  have invSquare : inv m ≫ L'.projection = L.projection ≫ e.inv := by
    calc
      inv m ≫ L'.projection =
          inv m ≫ L'.projection ≫ e.hom ≫ e.inv := by simp
      _ = inv m ≫ (L'.projection ≫ e.hom) ≫ e.inv := by simp
      _ = L.projection ≫ e.inv := by rw [← square]; simp
  let E : ∀ {T : SchemeOver k} (j : T ⟶ Q'.scheme),
      SectionsOver L'.projection j ≃ SectionsOver L.projection (j ≫ e.hom) :=
    fun j =>
      { toFun := fun s => ⟨s.val ≫ m, by rw [Category.assoc, square, ← Category.assoc, s.property]⟩
        invFun := fun s => ⟨s.val ≫ inv m, by
          rw [Category.assoc, invSquare, ← Category.assoc, s.property]
          simp⟩
        left_inv := fun s => Subtype.ext (by simp)
        right_inv := fun s => Subtype.ext (by simp) }
  exact ⟨E, fun _ _ => rfl, fun _ _ _ => Category.assoc _ _ _⟩

/-- Pullback along a central isogeny identifies sections of the flag line bundles. -/
theorem centralSectionComparison.{u} : CentralSectionComparison.{u} :=
  centralSectionComparison_of_bundleComparison
    LinearAlgebraicGroups.Representation.IsogenyFlagComparison.flagBundleComparison

set_option backward.isDefEq.respectTransparency false in
theorem centralScalarAction.{u} : CentralScalarAction.{u} := by
  intro k _ G P Q a p χ L ha R t g z hc
  let b : Points P.negative.group.X R := t ≫ p.inclusion.hom.hom
  let c : Points G.val.X R := t ≫ P.torus.inclusion.hom.hom
  let i := P.negative.inclusion.hom.hom
  have hcbi : b ≫ i = c := by
    change (t ≫ p.inclusion.hom.hom) ≫ i = c
    rw [Category.assoc]
    exact congrArg (fun h : P.torus.group ⟶ G.val ↦ t ≫ h.hom.hom) p.inclusion_comp
  have htb : b ≫ (p.projection ≫ χ).hom.hom = t ≫ χ.hom.hom := by
    change (t ≫ p.inclusion.hom.hom) ≫ (p.projection.hom.hom ≫ χ.hom.hom) =
      t ≫ χ.hom.hom
    have hp := congrArg
      (fun h : P.torus.group ⟶ P.torus.group ↦ h.hom.hom) p.section_projection
    change p.inclusion.hom.hom ≫ p.projection.hom.hom = 𝟙 _ at hp
    rw [Category.assoc, ← Category.assoc p.inclusion.hom.hom, hp, Category.id_comp]
  have hχ : CharacterPairing.characterValue (p.projection ≫ χ) R b =
      CharacterPairing.characterValue χ R t := by
    unfold CharacterPairing.characterValue
    rw [htb]
  change Centralizes (𝟙 G.val) c at hc
  have hcomm : c * g = g * c := by
    unfold Centralizes conjugateFamily at hc
    have hid : (𝟙 G.val : G.val ⟶ G.val).hom.hom = 𝟙 G.val.X := rfl
    simp only [hid, Category.comp_id] at hc
    have h := congrArg (fun m ↦ lift g (𝟙 _) ≫ m) hc
    have hg : c * g * c⁻¹ = g := by
      simpa only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_fst_assoc, lift_snd_assoc,
        Category.comp_id, Category.id_comp] using h
    exact mul_inv_eq_iff_eq_mul.mp hg
  have hprod : (g * c) * (b⁻¹ ≫ i) = g := by
    change (g * c) * (b⁻¹ ≫ P.negative.inclusion.hom.hom) = g
    rw [GrpObj.inv_comp, show b ≫ P.negative.inclusion.hom.hom = c from hcbi]
    exact mul_inv_cancel_right _ _
  have htr := L.transition R (g * c) b⁻¹ z
  change prod.lift ((g * c) * (b⁻¹ ≫ i)) (linePoint R
      (CharacterPairing.characterValue (p.projection ≫ χ) R (b⁻¹)⁻¹ * z)) ≫
        L.trivialization = prod.lift (g * c) (linePoint R z) ≫ L.trivialization at htr
  have hinv : ((b : AdjointRepresentation.GroupPoints P.negative.group R)⁻¹)⁻¹ = b :=
    inv_inv (b : AdjointRepresentation.GroupPoints P.negative.group R)
  rw [hprod, hinv, hχ] at htr
  have hbase : (g * c) ≫ Q.projection = g ≫ Q.projection := by
    have h := congrArg (· ≫ L.projection) htr.symm
    simpa only [Category.assoc, ← L.trivializes.w, prod.lift_fst_assoc] using h
  change lift c (g ≫ Q.projection) ≫ a.smul = g ≫ Q.projection ∧
    lift c (prod.lift g (linePoint R z) ≫ L.trivialization) ≫ L.action.smul =
      prod.lift g (linePoint R (CharacterPairing.characterValue χ R t * z)) ≫ L.trivialization
  constructor
  · calc
      _ = (c * g) ≫ Q.projection := by
        have h := lift_map c g (𝟙 G.val.X) Q.projection
        rw [Category.comp_id] at h
        rw [← h, Category.assoc, ← ha]
        rfl
      _ = _ := hcomm ▸ hbase
  · rw [L.leftTranslation, hcomm]
    exact htr.symm

/-- Existence of a finite affine cover of a proper flag. -/
theorem finiteAffineCover.{u} : FiniteAffineCover.{u} := by
  intro k _ X h
  let : IsProper X.hom := h
  let : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  let : X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from X.hom]
    infer_instance⟩
  let 𝒰 := X.left.affineCover.finiteSubcover
  let U := fun i : 𝒰.I₀ => (𝒰.f i).opensRange
  refine ⟨𝒰.I₀, inferInstance, U, 𝒰.isOpenCover_opensRange.iSup_eq_top, ?_⟩
  intro s hs
  apply IsAffineOpen.biInf (s : Set 𝒰.I₀) s.finite_toSet hs
  intro i _
  exact isAffineOpen_opensRange (𝒰.f i)

/-- The cohomology of the finite ordered Čech complex vanishes beyond its length. -/
theorem cechBounded.{u,v} : CechBounded.{u,v} := by
  intro k _ D _ Idx _ _ U P n h
  have : IsEmpty (Fin (n + 1) ↪o Idx) := ⟨fun e => by
    have h' := Fintype.card_le_of_injective e e.injective
    rw [Fintype.card_fin] at h'
    omega⟩
  have hterm : IsZero ((cechComplex U P).X n) := by
    change IsZero (ModuleCat.of k (∀ e : Fin (n + 1) ↪o Idx, P.obj (op (tupleOpen U e))))
    exact ModuleCat.isZero_of_subsingleton _
  exact (HomologicalComplex.ExactAt.of_isZero hterm).isZero_homology

/-- A finite affine comparison transfers the cutoff of the ordered complex
to the derived groups. -/
theorem cohomologyBound_of_affineCech.{u}
    (compare : AffineCechComparison.{u})
    {k : Type u} [Field k] (X : SchemeOver k) (hX : HasFiniteAffineCover X)
    (F : X.left.Modules) (hF : (F : SheafOfModules X.left.ringCatSheaf).IsQuasicoherent) :
    ∃ N : ℕ, ∀ n ≥ N, IsZero ((cohomology X n).obj F) := by
  obtain ⟨I, inst, U, hc, hi⟩ := hX
  let : Fintype I := inst
  let e := Fintype.equivFin I
  let : LinearOrder I := LinearOrder.lift' e e.injective
  refine ⟨Fintype.card I, fun n hn => ?_⟩
  obtain ⟨c, _⟩ := compare X U hc hi n
  exact IsZero.of_iso
    (cechBounded U (coefficientPresheaf F) n hn)
    (c F hF)

section CechScalarExtension

open scoped Simplicial
open CategoryTheory.Preadditive
open private orderedCochains coface differential tupleOpen_le
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]

private abbrev extendScalars := extendToAlgebra (k := k) (K := R)

private def extendProductIso {I : Type u} [Finite I] (Z : I → ModuleCat.{u} k) :
    (extendScalars (k := k) (R := R)).obj (ModuleCat.of k (∀ i, Z i)) ≅
      ModuleCat.of R (∀ i, (extendScalars (k := k) (R := R)).obj (Z i)) :=
  let E := extendScalars (k := k) (R := R)
  E.mapIso (ModuleCat.piIsoPi Z).symm ≪≫ PreservesProduct.iso E Z ≪≫
    ModuleCat.piIsoPi (fun i => E.obj (Z i))

@[reassoc]
private theorem extendProductIso_hom_proj {I : Type u} [Finite I]
    (Z : I → ModuleCat.{u} k) (i : I) :
    (extendProductIso (R := R) Z).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (extendScalars (k := k) (R := R)).map (ModuleCat.ofHom (LinearMap.proj i)) := by
  simp only [extendProductIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom,
    piComparison_comp_π, ← Functor.map_comp, ModuleCat.piIsoPi_inv_kernel_ι, extendScalars]

variable {D : Type v} [CompleteLattice D]
  {I : Type u} [Preorder I] [Finite I] (U : I → D) (P : Dᵒᵖ ⥤ ModuleCat.{u} k)

private instance finiteOrderedTuples (n : ℕ) : Finite (Fin (n + 1) ↪o I) :=
  Finite.of_injective (fun e : Fin (n + 1) ↪o I => (e : Fin (n + 1) → I))
    DFunLike.coe_injective

omit [Finite I] in
private theorem orderedCochains_map_proj {A : Type u} [CommRing A]
    (Q : Dᵒᵖ ⥤ ModuleCat.{u} A) {n m : SemiSimplexCategory} (f : n ⟶ m)
    (e : Fin (m.len + 1) ↪o I) :
    (orderedCochains U Q).map f ≫ ModuleCat.ofHom (LinearMap.proj e) =
      ModuleCat.ofHom (LinearMap.proj ((SemiSimplexCategory.homEquiv f).trans e)) ≫
        Q.map (homOfLE (tupleOpen_le U e (SemiSimplexCategory.homEquiv f))).op := by
  rfl

private def extendOrderedCochainsIso :
    orderedCochains U P ⋙ extendScalars (k := k) (R := R) ≅
      orderedCochains U (P ⋙ extendScalars (k := k) (R := R)) :=
  NatIso.ofComponents (fun n => extendProductIso (fun (e : Fin (n.len + 1) ↪o I) =>
    P.obj (op (tupleOpen U e)))) (by
    intro n m f
    let E := extendScalars (k := k) (R := R)
    apply ModuleCat.hom_ext
    ext x : 1
    funext e
    change ((E.map ((orderedCochains U P).map f) ≫ (extendProductIso (R := R) _).hom) ≫
        ModuleCat.ofHom (LinearMap.proj e)) x =
      (((extendProductIso (R := R) _).hom ≫ (orderedCochains U (P ⋙ E)).map f) ≫
        ModuleCat.ofHom (LinearMap.proj e)) x
    simp only [Category.assoc, extendProductIso_hom_proj, orderedCochains_map_proj,
      Functor.comp_map, extendProductIso_hom_proj_assoc]
    dsimp only [E]
    rw [← Functor.map_comp, orderedCochains_map_proj, Functor.map_comp]
    rfl)

/-- Flat extension of the ground field commutes with the finite ordered Čech
complex, using the canonical maps on its products of sections. -/
def cechExtendScalarsIso :
    ((extendScalars (k := k) (R := R)).mapHomologicalComplex (.up ℕ)).obj (cechComplex U P) ≅
      cechComplex U (P ⋙ extendScalars (k := k) (R := R)) := by
  let E := extendScalars (k := k) (R := R)
  letI : PreservesBinaryBiproducts E := preservesBinaryBiproducts_of_preservesBinaryCoproducts E
  letI : E.Additive := Functor.additive_of_preservesBinaryBiproducts E
  let c := extendOrderedCochainsIso (R := R) U P
  refine HomologicalComplex.Hom.isoOfComponents (fun n => c.app ⦋n⦌ₛ) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  simp only [Functor.mapHomologicalComplex_obj_d, cechComplex, CochainComplex.of_d]
  change c.hom.app ⦋i⦌ₛ ≫ differential U (P ⋙ E) i =
    E.map (differential U P i) ≫ c.hom.app ⦋i + 1⦌ₛ
  unfold differential
  rw [E.map_sum]
  simp only [E.map_zsmul, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  exact Finset.sum_congr rfl fun (s : Fin (i + 2)) _ =>
    congrArg ((-1 : ℤ) ^ (s : ℕ) • ·) (c.hom.naturality (coface s)).symm

/-- Extension of scalars commutes with cohomology of the finite ordered complex. -/
def cechCohomologyExtendScalarsIso (n : ℕ) :
    (extendScalars (k := k) (R := R)).obj ((cechComplex U P).homology n) ≅
      (cechComplex U (P ⋙ extendScalars (k := k) (R := R))).homology n :=
  extendCohomologyIso (cechComplex U P) n ≪≫
    HomologicalComplex.homologyMapIso (cechExtendScalarsIso U P) n

end CechScalarExtension

section CechDegreeZero

open scoped Simplicial
open private orderedCochains coface differential
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] (X : SchemeOverRing A)
  {I : Type u} [LinearOrder I] (U : I → X.left.Opens)

private def singletonTuple (i : I) : Fin 1 ↪o I :=
  OrderEmbedding.ofStrictMono (fun _ => i) (fun a b h => (not_lt_of_ge (Subsingleton.elim a b).ge h).elim)

private theorem singletonTuple_apply (i : I) (j : Fin 1) : singletonTuple i j = i := rfl

private theorem singletonTuple_eq (e : Fin 1 ↪o I) : singletonTuple (e 0) = e :=
  DFunLike.ext _ _ (fun j => by have : j = 0 := Subsingleton.elim _ _; subst j; rfl)

private theorem tupleOpen_singleton (i : I) : tupleOpen U (singletonTuple i) = U i := by
  simp [tupleOpen, singletonTuple_apply]

private theorem tupleOpen_pair (e : Fin 2 ↪o I) :
    tupleOpen U e = U (e 0) ⊓ U (e 1) := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · refine le_iInf fun j => ?_
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right

private abbrev CechOf (F : X.left.Modules) := cechComplex U (coefficientPresheaf (X := X) F)

private def cochainFamily (F : X.left.Modules) (x : (CechOf X U F).X 0) (i : I) :
    Γ(F, U i) :=
  F.presheaf.map (eqToHom (tupleOpen_singleton X U i).symm).op (x (singletonTuple i))

private theorem tupleRestriction_congr (F : X.left.Modules) (x : (CechOf X U F).X 0)
    {V : X.left.Opens} {e e' : Fin 1 ↪o I} (h : e = e')
    (j : V ⟶ tupleOpen U e) (j' : V ⟶ tupleOpen U e') :
    F.presheaf.map j.op (x e) = F.presheaf.map j'.op (x e') := by
  subst e'
  rw [Subsingleton.elim j j']

private theorem cochainFamily_diff (F : X.left.Modules) (x : (CechOf X U F).X 0)
    (e : Fin 2 ↪o I) :
    (CechOf X U F).d 0 1 x e =
      F.presheaf.map (homOfLE (le_trans (le_of_eq (tupleOpen_pair X U e)) inf_le_right)).op
          (cochainFamily X U F x (e 1)) -
        F.presheaf.map (homOfLE (le_trans (le_of_eq (tupleOpen_pair X U e)) inf_le_left)).op
          (cochainFamily X U F x (e 0)) := by
  have h₀ : (SemiSimplexCategory.homEquiv (coface (n := 0) 0)).trans e = singletonTuple (e 1) := by
    apply DFunLike.ext
    intro j
    have : (j : Fin 1) = 0 := @Subsingleton.elim (Fin 1) inferInstance j 0
    subst j
    rfl
  have h₁ : (SemiSimplexCategory.homEquiv (coface (n := 0) 1)).trans e = singletonTuple (e 0) := by
    apply DFunLike.ext
    intro j
    have : (j : Fin 1) = 0 := @Subsingleton.elim (Fin 1) inferInstance j 0
    subst j
    rfl
  have hd : (CechOf X U F).d 0 1 = differential U (coefficientPresheaf (X := X) F) 0 :=
    CochainComplex.of_d (fun n => (orderedCochains U (coefficientPresheaf (X := X) F)).obj ⦋n⦌ₛ)
      (differential U (coefficientPresheaf (X := X) F)) 0
  rw [hd]
  change ((differential U (coefficientPresheaf (X := X) F) 0).hom x) e = _
  unfold differential
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    ModuleCat.hom_add, ModuleCat.hom_neg, LinearMap.add_apply, LinearMap.neg_apply,
    sub_eq_add_neg]
  change (orderedCochains U (coefficientPresheaf (X := X) F)).map (coface 0) x e +
    -(orderedCochains U (coefficientPresheaf (X := X) F)).map (coface 1) x e = _
  apply congrArg₂ (· + -·)
  · unfold cochainFamily
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, ← op_comp]
    change F.presheaf.map (homOfLE _).op (x _) = _
    exact tupleRestriction_congr X U F x h₀ _ _
  · unfold cochainFamily
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, ← op_comp]
    change F.presheaf.map (homOfLE _).op (x _) = _
    exact tupleRestriction_congr X U F x h₁ _ _

private theorem cochainFamily_compatible (F : X.left.Modules)
    (x : (CechOf X U F).X 0) (hx : (CechOf X U F).d 0 1 x = 0) :
    TopCat.Presheaf.IsCompatible F.presheaf U (cochainFamily X U F x) := by
  have h {i j : I} (hij : i < j) :
      F.presheaf.map (Opens.infLELeft (U i) (U j)).op (cochainFamily X U F x i) =
        F.presheaf.map (Opens.infLERight (U i) (U j)).op (cochainFamily X U F x j) := by
    let e : Fin 2 ↪o I := OrderEmbedding.ofStrictMono ![i,j] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro l
      have : l = 0 := Subsingleton.elim _ _
      subst l
      exact hij)
    have hw := congrFun hx e
    rw [cochainFamily_diff, Pi.zero_apply, sub_eq_zero] at hw
    let V := U i ⊓ U j
    have he : tupleOpen U e = V := tupleOpen_pair X U e
    let φ : V ⟶ tupleOpen U e := eqToHom he.symm
    have hh := congrArg (F.presheaf.map φ.op) hw.symm
    simp only [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at hh
    exact hh
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h hij
  · have h : Opens.infLELeft (U i) (U i) = Opens.infLERight (U i) (U i) := Subsingleton.elim _ _
    rw [h]
  · let φ : U i ⊓ U j ⟶ U j ⊓ U i := eqToHom (inf_comm _ _)
    have hh := congrArg (F.presheaf.map φ.op) (h hji).symm
    simp only [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at hh
    exact hh

private def cechZeroAugmentation (F : X.left.Modules) :
    (sectionsFunctor X).obj F ⟶ (CechOf X U F).X 0 :=
  (ModuleCat.restrictScalarsCongr (groundRingHomOpen_top X).symm).hom.app (F.val.obj (op ⊤)) ≫
    ModuleCat.ofHom (X := localSections F ⊤) (Y := (CechOf X U F).X 0)
      (LinearMap.pi fun e => ((coefficientPresheaf (X := X) F).map (tupleOpen U e).leTop.op).hom)

private theorem cechZeroAugmentation_app (F : X.left.Modules)
    (x : (sectionsFunctor X).obj F) (e : Fin 1 ↪o I) :
    cechZeroAugmentation X U F x e = F.presheaf.map (tupleOpen U e).leTop.op x :=
  rfl

private theorem cochainFamily_augmentation (F : X.left.Modules)
    (x : (sectionsFunctor X).obj F) (i : I) :
    cochainFamily X U F (cechZeroAugmentation X U F x) i = F.presheaf.map (U i).leTop.op x := by
  rw [cochainFamily, cechZeroAugmentation_app, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  rfl

private theorem cechZeroAugmentation_closed (F : X.left.Modules) :
    cechZeroAugmentation X U F ≫ (CechOf X U F).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  ext x : 1
  funext e
  change (CechOf X U F).d 0 1 (cechZeroAugmentation X U F x) e =
    (0 : (CechOf X U F).X 1) e
  rw [cochainFamily_diff, Pi.zero_apply, sub_eq_zero, cochainFamily_augmentation,
    cochainFamily_augmentation, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← F.presheaf.map_comp, ← F.presheaf.map_comp]
  rfl

private theorem cochainFamily_eq_iff (F : X.left.Modules)
    (x y : (CechOf X U F).X 0) :
    (∀ i, cochainFamily X U F x i = cochainFamily X U F y i) ↔ x = y := by
  constructor
  · intro h
    funext e
    rw [← singletonTuple_eq e]
    let H := F.presheaf.map (eqToHom (tupleOpen_singleton X U (e 0)).symm).op
    exact (ConcreteCategory.bijective_of_isIso H).injective (h (e 0))
  · intro h i
    rw [h]

private def cechZeroCycleAugmentation (F : X.left.Modules) :
    (sectionsFunctor X).obj F ⟶ (CechOf X U F).cycles 0 :=
  (CechOf X U F).liftCycles' (cechZeroAugmentation X U F) 1 (by decide)
    (cechZeroAugmentation_closed X U F)

private theorem cechZeroCycleAugmentation_isIso (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) :
    IsIso (cechZeroCycleAugmentation X U F) := by
  let K := CechOf X U F
  let aug := cechZeroCycleAugmentation X U F
  let i := K.iCycles 0
  let S : TopCat.Sheaf AddCommGrpCat _ := ⟨F.presheaf, F.isSheaf⟩
  have haug : aug ≫ i = cechZeroAugmentation X U F := K.liftCycles_i _ 1
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 by decide))
    (cechZeroAugmentation_closed X U F)
  have happ (x : (sectionsFunctor X).obj F) :
      i (aug x) = cechZeroAugmentation X U F x :=
    congrArg (fun f => f x) haug
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    let s := cochainFamily X U F (i (aug x))
    have hc : K.d 0 1 (i (aug x)) = 0 :=
      congrArg (fun f => f (aug x)) (K.iCycles_d 0 1)
    obtain ⟨z, _hz, hu⟩ := S.existsUnique_gluing' U ⊤ (fun j => (U j).leTop) hU.ge s
      (cochainFamily_compatible X U F _ hc)
    have h₁ : ∀ j, F.presheaf.map (U j).leTop.op x = s j := by
      intro j
      rw [show s j = cochainFamily X U F (i (aug x)) j from rfl, happ, cochainFamily_augmentation]
    have h₂ : ∀ j, F.presheaf.map (U j).leTop.op y = s j := by
      intro j
      rw [show s j = cochainFamily X U F (i (aug x)) j from rfl, h, happ, cochainFamily_augmentation]
    exact (hu x h₁).trans (hu y h₂).symm
  · intro x
    have hc : K.d 0 1 (i x) = 0 := congrArg (fun f => f x) (K.iCycles_d 0 1)
    obtain ⟨z, hz, _⟩ := S.existsUnique_gluing' U ⊤ (fun j => (U j).leTop) hU.ge
      (cochainFamily X U F (i x)) (cochainFamily_compatible X U F _ hc)
    refine ⟨z, ((ModuleCat.mono_iff_injective i).mp inferInstance) ?_⟩
    rw [happ]
    apply (cochainFamily_eq_iff X U F _ _).mp
    intro j
    rw [cochainFamily_augmentation]
    exact hz j

/-- The degree-zero comparison for any ordered open cover is the gluing
isomorphism, with the canonical augmentation to the Čech complex. -/
def cechDegreeZeroIso (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) :
    (cohomology X 0).obj F ≅ (CechOf X U F).homology 0 := by
  let K := CechOf X U F
  letI := cechZeroCycleAugmentation_isIso X U hU F
  have h : (K.sc 0).f = 0 := K.shape _ _ (by simp)
  exact (cohomologyZero X).app F ≪≫ asIso (cechZeroCycleAugmentation X U F) ≪≫
    (K.sc 0).asIsoHomologyπ h

private theorem cechZeroCycleAugmentation_natural {F F' : X.left.Modules} (f : F ⟶ F') :
    (sectionsFunctor X).map f ≫ cechZeroCycleAugmentation X U F' =
      cechZeroCycleAugmentation X U F ≫
        HomologicalComplex.cyclesMap (cechMap U (coefficientPresheafMap (X := X) f)) 0 := by
  let K := CechOf X U F
  let K' := CechOf X U F'
  let m := cechMap U (coefficientPresheafMap (X := X) f)
  let h : (ComplexShape.up ℕ).next 0 = 1 :=
    (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 by decide)
  have h₁ : cechZeroCycleAugmentation X U F ≫ K.iCycles 0 = cechZeroAugmentation X U F :=
    K.liftCycles_i _ 1 h (cechZeroAugmentation_closed X U F)
  have h₂ : cechZeroCycleAugmentation X U F' ≫ K'.iCycles 0 = cechZeroAugmentation X U F' :=
    K'.liftCycles_i _ 1 h (cechZeroAugmentation_closed X U F')
  apply (cancel_mono (K'.iCycles 0)).mp
  change ((sectionsFunctor X).map f ≫ cechZeroCycleAugmentation X U F') ≫ K'.iCycles 0 =
    (cechZeroCycleAugmentation X U F ≫ HomologicalComplex.cyclesMap m 0) ≫ K'.iCycles 0
  rw [Category.assoc, h₂, Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, h₁]
  apply ModuleCat.hom_ext
  ext x : 1
  funext e
  change cechZeroAugmentation X U F' ((sectionsFunctor X).map f x) e =
    f.app (tupleOpen U e) (cechZeroAugmentation X U F x e)
  rw [cechZeroAugmentation_app, cechZeroAugmentation_app]
  exact (PresheafOfModules.naturality_apply f.val (tupleOpen U e).leTop.op x).symm

/-- The degree-zero Čech comparison is natural in the sheaf of modules. -/
theorem cechDegreeZeroIso_natural (hU : (⨆ i, U i) = ⊤)
    {F F' : X.left.Modules} (f : F ⟶ F') :
    (cohomology X 0).map f ≫ (cechDegreeZeroIso X U hU F').hom =
      (cechDegreeZeroIso X U hU F).hom ≫
        HomologicalComplex.homologyMap (cechMap U (coefficientPresheafMap (X := X) f)) 0 := by
  let m := cechMap U (coefficientPresheafMap (X := X) f)
  change (cohomology X 0).map f ≫ (cohomologyZero X).hom.app F' ≫
        cechZeroCycleAugmentation X U F' ≫ (CechOf X U F').homologyπ 0 =
    ((cohomologyZero X).hom.app F ≫ cechZeroCycleAugmentation X U F ≫
      (CechOf X U F).homologyπ 0) ≫ HomologicalComplex.homologyMap m 0
  rw [NatTrans.naturality_assoc, reassoc_of% cechZeroCycleAugmentation_natural X U f,
    Category.assoc, Category.assoc, HomologicalComplex.homologyπ_naturality]

end CechDegreeZero

section CovarianceOnOpens

open private overPullbackRegular from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false

private theorem pullbackRegular_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : Γ(Y, U)) :
    (Scheme.Modules.Hom.app (pullbackRegular f) U) x = f.app U x := by
  change f.app U x * (1 : Γ(X, f ⁻¹ᵁ U)) = _
  exact mul_one _

private theorem multiplyRegular_app {X : Scheme.{u}} (c : Γ(X, ⊤)) (U : X.Opens)
    (x : Γ(X, U)) :
    (Scheme.Modules.Hom.app (multiplyRegular c) U) x = x * X.presheaf.map U.leTop.op c :=
  rfl

private theorem preimage_le {X Y Z : Scheme.{u}} (q : X ⟶ Y) (r : Z ⟶ Y)
    (b : Z ⟶ X) (hb : b ≫ q = r) (U : Y.Opens) :
    r ⁻¹ᵁ U ≤ b ⁻¹ᵁ (q ⁻¹ᵁ U) := by
  subst r
  rfl

private theorem overPullbackRegular_app {X Y Z : Scheme.{u}} (q : X ⟶ Y) (r : Z ⟶ Y)
    (b : Z ⟶ X) (hb : b ≫ q = r) (U : Y.Opens) (x : Γ(X, q ⁻¹ᵁ U)) :
    (Scheme.Modules.Hom.app (overPullbackRegular q r b hb) U) x =
      b.appLE (q ⁻¹ᵁ U) (r ⁻¹ᵁ U) (preimage_le q r b hb U) x := by
  subst r
  erw [Scheme.Hom.appLE_eq_app]
  unfold overPullbackRegular
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforward_map_app, eqToHom_refl]
  change (Z.presheaf.map (𝟙 (op ((b ≫ q) ⁻¹ᵁ U))))
      ((Scheme.Modules.Hom.app (pullbackRegular b) (q ⁻¹ᵁ U)) x) = _
  erw [Z.presheaf.map_id]
  exact pullbackRegular_app b _ x

/-- On each open the kernel sheaf uses the actual restrictions of functions
along the two maps, with the multiplier restricted from the double overlap. -/
theorem covarianceMap_app {X Y Z : Scheme.{u}} (q : X ⟶ Y) (r : Z ⟶ Y)
    (b₀ b₁ : Z ⟶ X) (hb₀ : b₀ ≫ q = r) (hb₁ : b₁ ≫ q = r) (c : Γ(Z, ⊤))
    (U : Y.Opens) (x : Γ(X, q ⁻¹ᵁ U)) :
    (Scheme.Modules.Hom.app (covarianceMap q r b₀ b₁ hb₀ hb₁ c) U) x =
      b₁.appLE (q ⁻¹ᵁ U) (r ⁻¹ᵁ U) (preimage_le q r b₁ hb₁ U) x -
      (b₀.appLE (q ⁻¹ᵁ U) (r ⁻¹ᵁ U) (preimage_le q r b₀ hb₀ U) x) *
        Z.presheaf.map (r ⁻¹ᵁ U).leTop.op c := by
  unfold covarianceMap
  rw [Scheme.Modules.Hom.sub_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app]
  change Sub.sub (α := Γ(Z, r ⁻¹ᵁ U))
    ((Scheme.Modules.Hom.app (overPullbackRegular q r b₁ hb₁) U) x)
    (Scheme.Modules.Hom.app (multiplyRegular c) (r ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app (overPullbackRegular q r b₀ hb₀) U x)) = _
  erw [multiplyRegular_app, overPullbackRegular_app, overPullbackRegular_app]
  rfl

end CovarianceOnOpens

/-- Restricting a pullback on regular functions to the covariance kernel
determines the map of coefficient sheaves. -/
theorem covariancePullback_unique
    {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}
    (D : CovarianceData X) (D' : CovarianceData Y)
    (f : Y.left ⟶ X.left) (g : D'.torsor.left ⟶ D.torsor.left)
    (w : g ≫ D.projection.left = D'.projection.left ≫ f)
    {α β : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D'.sheaf}
    (hα : D.IsPullbackMap D' f g w α) (hβ : D.IsPullbackMap D' f g w β) : α = β := by
  rw [← cancel_mono ((Scheme.Modules.pushforward f).map D'.inclusion)]
  exact hα.trans hβ.symm

/-- Any two maps induced by the same coefficient map agree, since both
can be computed using the same lift to injective resolutions. -/
theorem inducedCohomologyMap_unique
    {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}
    (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : X.left.Modules} {F' : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj F') (n : ℕ)
    {m m' : (cohomology X n).obj F ⟶
      (ModuleCat.restrictScalars.{u} φ).obj ((cohomology Y n).obj F')}
    (hm : IsCohomologyMap φ f w α n m) (hm' : IsCohomologyMap φ f w α n m') : m = m' := by
  let I := injectiveResolution F
  let J := injectiveResolution F'
  obtain ⟨⟨l, hl⟩, h₁⟩ := hm I J
  exact (h₁ l hl).trans (((hm' I J).2 l hl).symm)

/-- The contribution from each zero cohomology group is the zero character. -/
theorem eulerCharacteristicBound.{u} : EulerCharacteristicBound.{u} := by
  intro k _ G P Q p χ h ρ N M hNM hzero
  classical
  unfold equivariantEulerCharacteristic
  symm
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n hn hnN
  have hn' : N ≤ n := Nat.le_of_not_lt fun hl => hnN (Finset.mem_range.mpr hl)
  let : Subsingleton (flagCohomology Q p χ h n) := ModuleCat.subsingleton_of_isZero (hzero n hn')
  have hdim : Module.finrank k (flagCohomology Q p χ h n) = 0 :=
    Module.finrank_zero_of_subsingleton
  let : IsEmpty (CohomologyIndex (p := p) (χ := χ) h n) :=
    ⟨fun i => Nat.not_lt_zero _ (i.down.isLt.trans_le hdim.le)⟩
  have hm : FormalCharacters.multiplicity P.torus (ρ n) = 0 := by
    funext θ
    let : Subsingleton (CohomologyIndex (p := p) (χ := χ) h n → k) :=
      ⟨fun x y => funext fun i => isEmptyElim i⟩
    simp [FormalCharacters.multiplicity, Module.finrank_zero_of_subsingleton]
  have hc : FormalCharacters.formalCharacter P.torus (ρ n) = 0 := by
    ext θ
    simp [FormalCharacters.formalCharacter, hm]
  rw [hc, smul_zero]


section LineCoordinates

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private abbrev polynomialRing (k : Type u) [Field k] := CommRingCat.of (Polynomial k)

/-- The coordinate of a map to the affine line, for an arbitrary scheme over the field. -/
def lineCoordinate {T : SchemeOver k} (f : T ⟶ affineLine k) : Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (polynomialRing k)).inv ≫ f.left.appTop) Polynomial.X

private theorem lineRingMap_C {T : SchemeOver k} (f : T ⟶ affineLine k) (r : k) :
    ((Scheme.ΓSpecIso (polynomialRing k)).inv ≫ f.left.appTop) (Polynomial.C r) =
      groundRingHom T r := by
  have h := congrArg Scheme.Hom.appTop (Over.w f)
  change (f.left ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))).appTop =
    T.hom.appTop at h
  rw [Scheme.Hom.comp_appTop] at h
  have h' : (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) ≫
      (Scheme.ΓSpecIso (polynomialRing k)).inv ≫ f.left.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.hom.appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, h]
  exact congrArg (fun m : CommRingCat.of k ⟶ Γ(T.left, ⊤) => m r) h'

private theorem lineCoordinate_injective (T : SchemeOver k) :
    Function.Injective (lineCoordinate (T := T)) := by
  intro f g h
  apply Over.OverMorphism.ext
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    exact (lineRingMap_C f r).trans (lineRingMap_C g r).symm
  · exact h

private def lineFromCoordinate (T : SchemeOver k) (z : Γ(T.left, ⊤)) :
    T ⟶ affineLine k := by
  let : Algebra k Γ(T.left, ⊤) := (groundRingHom T).toAlgebra
  let φ : polynomialRing k ⟶ Γ(T.left, ⊤) :=
    CommRingCat.ofHom (Polynomial.aeval z).toRingHom
  let f : T.left ⟶ Spec (polynomialRing k) :=
    ΓSpec.adjunction.homEquiv T.left (op (polynomialRing k)) φ.op
  refine Over.homMk f ?_
  change f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = T.hom
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.hom.appTop
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  dsimp only [f]
  rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  apply CommRingCat.hom_ext
  ext r
  exact Polynomial.aeval_C z r

private theorem lineCoordinate_lineFromCoordinate (T : SchemeOver k) (z : Γ(T.left, ⊤)) :
    lineCoordinate (lineFromCoordinate T z) = z := by
  let : Algebra k Γ(T.left, ⊤) := (groundRingHom T).toAlgebra
  let φ : polynomialRing k ⟶ Γ(T.left, ⊤) :=
    CommRingCat.ofHom (Polynomial.aeval z).toRingHom
  change ((Scheme.ΓSpecIso (polynomialRing k)).inv ≫
    (ΓSpec.adjunction.homEquiv T.left (op (polynomialRing k)) φ.op).appTop) Polynomial.X = _
  rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  exact Polynomial.aeval_X z

/-- Maps to the affine line over the ground field are regular functions. -/
def lineCoordinateEquiv (T : SchemeOver k) :
    (T ⟶ affineLine k) ≃ Γ(T.left, ⊤) where
  toFun := lineCoordinate
  invFun := lineFromCoordinate T
  left_inv f := lineCoordinate_injective T (lineCoordinate_lineFromCoordinate T (lineCoordinate f))
  right_inv := lineCoordinate_lineFromCoordinate T

@[simp]
theorem lineCoordinate_comp {S T : SchemeOver k} (f : S ⟶ T) (g : T ⟶ affineLine k) :
    lineCoordinate (f ≫ g) = f.left.appTop (lineCoordinate g) := by
  unfold lineCoordinate
  rw [Over.comp_left, Scheme.Hom.comp_appTop]
  change ((Scheme.ΓSpecIso (polynomialRing k)).inv ≫ g.left.appTop ≫ f.left.appTop)
      Polynomial.X = (((Scheme.ΓSpecIso (polynomialRing k)).inv ≫ g.left.appTop) ≫ f.left.appTop)
      Polynomial.X
  erw [Category.assoc]

private theorem lineCoordinate_linePoint (R : TestAlgebra k) (z : R) :
    lineCoordinate (linePoint R z) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv z := by
  change ((Scheme.ΓSpecIso (polynomialRing k)).inv ≫
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval z).toRingHom)).appTop) Polynomial.X = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (fun x : R => (Scheme.ΓSpecIso (CommRingCat.of R)).inv x) (Polynomial.aeval_X z)

private theorem lineCoordinate_testPoint {T : SchemeOver k} (R : TestAlgebra k)
    (x : Points T R) (f : T ⟶ affineLine k) :
    x ≫ f = linePoint R ((Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (x.left.appTop (lineCoordinate f))) := by
  apply lineCoordinate_injective
  rw [lineCoordinate_comp, lineCoordinate_linePoint]
  exact (Iso.hom_inv_id_apply (C := CommRingCat) _ _).symm

end LineCoordinates

section BundleDescent

set_option linter.style.haveILetI false

open private openRestriction from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]

private def restrictOver {X Y : SchemeOver k} (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U) :
    openScheme X V ⟶ openScheme Y U :=
  Over.homMk (f.left.resLE U V e) (by
    change f.left.resLE U V e ≫ U.ι ≫ Y.hom = V.ι ≫ X.hom
    rw [Scheme.Hom.resLE_comp_ι_assoc, Over.w f])

@[reassoc (attr := simp)]
private theorem restrictOver_inclusion {X Y : SchemeOver k} (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U) :
    restrictOver f U V e ≫ openInclusion Y U = openInclusion X V ≫ f :=
  Over.OverMorphism.ext (f.left.resLE_comp_ι e)

private instance openInclusion_mono (X : SchemeOver k) (U : X.left.Opens) :
    Mono (openInclusion X U) := by
  let : Mono (openInclusion X U).left := inferInstanceAs (Mono U.ι)
  exact Over.mono_of_mono_left _

private theorem restrictOver_pullback {X Y : SchemeOver k} (f : X ⟶ Y) (U : Y.left.Opens) :
    IsPullback (openInclusion X (f.left ⁻¹ᵁ U)) (restrictOver f U _ le_rfl) f
      (openInclusion Y U) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of k)))
  change IsPullback (f.left ⁻¹ᵁ U).ι (f.left.resLE U (f.left ⁻¹ᵁ U) le_rfl) f.left U.ι
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict f.left U).flip

private theorem topIso_restrictOver {X Y : SchemeOver k} (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U) (z : Γ(Y.left, U)) :
    V.topIso.hom ((restrictOver f U V e).left.appTop (U.topIso.inv z)) =
      f.left.appLE U V e z := by
  change V.topIso.hom ((f.left.resLE U V e).app ⊤ (U.topIso.inv z)) = _
  erw [f.left.resLE_app_top e]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply (C := CommRingCat)]
  exact Iso.inv_hom_id_apply (C := CommRingCat) V.topIso _

private theorem regularSection_mem_covariance {A : Type u} [CommRing A] {Z : SchemeOverRing A}
    (D : CovarianceData Z) (U : Z.left.Opens)
    (x : Γ(D.sheaf, U)) :
    D.covariance.app U (D.inclusion.app U x) = 0 := by
  change (D.inclusion.app U ≫ D.covariance.app U) x = 0
  rw [← Scheme.Modules.Hom.comp_app, kernel.condition, Scheme.Modules.Hom.zero_app]
  rfl

private theorem inclusion_bijective_onto_covariance (D : CovarianceData (A := k) Y)
    (U : Y.left.Opens) :
    Function.Bijective (fun x : Γ(D.sheaf, U) ↦
      (⟨D.inclusion.app U x, regularSection_mem_covariance D U x⟩ :
        {z : Γ(D.torsor.left, D.projection.left ⁻¹ᵁ U) // D.covariance.app U z = 0})) := by
  let ev := SheafOfModules.evaluation.{u} Y.left.ringCatSheaf (op U)
  let : ev.Additive := ⟨by intros; ext x; rfl⟩
  let e := PreservesKernel.iso ev D.covariance ≪≫ ModuleCat.kernelIsoKer _
  have w : e.hom ≫ ModuleCat.ofHom (ModuleCat.Hom.hom (ev.map D.covariance)).ker.subtype =
      ev.map D.inclusion := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  have w' (x : Γ(D.sheaf, U)) : (e.hom x).1 = D.inclusion.app U x :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom w) x
  constructor
  · intro x y h
    have h₁ : (e.hom x).1 = (e.hom y).1 := by rw [w', w']; exact congrArg Subtype.val h
    exact (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance |>.injective
      (Subtype.ext h₁)
  · intro z
    let x : Γ(D.sheaf, U) := e.inv ⟨z.val, z.property⟩
    refine ⟨x, Subtype.ext ?_⟩
    change D.inclusion.app U x = z.val
    rw [← w', show e.hom x = ⟨z.val, z.property⟩ from Iso.inv_hom_id_apply (C := ModuleCat _) e _]

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} {Q : Presentation P.negative}
    {p : BorelProjection P} {χ : Character P.torus.group} {a : ModObj G.val.X Q.scheme}

private abbrev torsorOpen (U : Q.scheme.left.Opens) := Q.projection.left ⁻¹ᵁ U

private abbrev overlapProjection (Q : Presentation P.negative) :
    G.val.X ⨯ P.negative.group.X ⟶ Q.scheme := prod.fst ≫ Q.projection

private abbrev overlapOpen (U : Q.scheme.left.Opens) :=
  (overlapProjection Q).left ⁻¹ᵁ U

private def flagMultiplierAt {T : SchemeOver k} (x : T ⟶ G.val.X ⨯ P.negative.group.X) :
    Γ(T.left, ⊤) :=
  x.left.appTop (flagTransition p χ)

private theorem flagMultiplierAt_testPoint (R : TestAlgebra k)
    (x : Points (G.val.X ⨯ P.negative.group.X) R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (flagMultiplierAt (p := p) (χ := χ) x) =
      CharacterPairing.characterValue (p.projection ≫ χ) R ((x ≫ prod.snd)⁻¹) := by
  let B := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
  let r : G.val.X ⨯ P.negative.group.X ⟶ (specGroup B).X :=
    (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X)⁻¹ ≫ (p.projection ≫ χ).hom.hom
  have h : x ≫ r = (x ≫ prod.snd)⁻¹ ≫ (p.projection ≫ χ).hom.hom := by
    change x ≫ (prod.snd⁻¹ ≫ (p.projection ≫ χ).hom.hom) = _
    rw [← Category.assoc, GrpObj.comp_inv]
  let g := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (x ≫ r)).unop
  have hg : (testSpec k).map g.op = x ≫ r :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hl : Spec.map (CommRingCat.ofHom g.hom.toRingHom) = (x ≫ r).left :=
    congrArg Over.Hom.left hg
  have he : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (x ≫ r).left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom g.hom.toRingHom := by
    rw [← hl, ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Over.comp_left, Scheme.Hom.comp_appTop] at he
  unfold CharacterPairing.characterValue
  rw [← h]
  change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (r.left.appTop ≫ x.left.appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom)
      (MonoidAlgebra.single DiagonalizableGroups.integerGenerator 1) = _
  exact congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of R =>
    φ (MonoidAlgebra.single DiagonalizableGroups.integerGenerator 1)) he

private def bundleGraph (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens)
    (z : openScheme G.val.X (torsorOpen U) ⟶ affineLine k) :
    openScheme G.val.X (torsorOpen U) ⟶ L.total :=
  prod.lift (openInclusion G.val.X (torsorOpen U)) z ≫ L.trivialization

private theorem bundleGraph_projection (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens)
    (z : openScheme G.val.X (torsorOpen U) ⟶ affineLine k) :
    bundleGraph L U z ≫ L.projection =
      openInclusion G.val.X (torsorOpen U) ≫ Q.projection := by
  simp [bundleGraph, ← L.trivializes.w]

private theorem bundleGraph_injective (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens) :
    Function.Injective (bundleGraph L U) := by
  intro f g h
  have he : prod.lift (openInclusion G.val.X (torsorOpen U)) f =
      prod.lift (openInclusion G.val.X (torsorOpen U)) g :=
    L.trivializes.hom_ext (by simp) h
  simpa using congrArg (· ≫ prod.snd) he

private def bundleCoordinateMap (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens)
    (s : SectionsOver L.projection (openInclusion Q.scheme U)) :
    openScheme G.val.X (torsorOpen U) ⟶ affineLine k :=
  L.trivializes.lift (openInclusion G.val.X (torsorOpen U))
    (restrictOver Q.projection U _ le_rfl ≫ s.val)
    (by rw [Category.assoc, s.property, restrictOver_inclusion]) ≫ prod.snd

private theorem bundleCoordinateMap_graph (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens)
    (s : SectionsOver L.projection (openInclusion Q.scheme U)) :
    bundleGraph L U (bundleCoordinateMap L U s) = restrictOver Q.projection U _ le_rfl ≫ s.val := by
  let q := restrictOver Q.projection U (torsorOpen U) le_rfl
  let i := openInclusion G.val.X (torsorOpen U)
  have w : i ≫ Q.projection = (q ≫ s.val) ≫ L.projection := by
    rw [Category.assoc, s.property, restrictOver_inclusion]
  let g := L.trivializes.lift i (q ≫ s.val) w
  have hg : prod.lift i (g ≫ prod.snd) = g := by
    apply prod.hom_ext
    · rw [prod.lift_fst, IsPullback.lift_fst]
    · rw [prod.lift_snd]
  change prod.lift i (g ≫ prod.snd) ≫ L.trivialization = q ≫ s.val
  rw [hg, IsPullback.lift_snd]

private theorem coordinate_agrees (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens)
    (s : SectionsOver L.projection (openInclusion Q.scheme U)) :
    bundleSectionCoordinate L U s =
      (torsorOpen U).topIso.hom (lineCoordinate (bundleCoordinateMap L U s)) := by
  have hres : Q.projection.left.resLE U (torsorOpen U) le_rfl =
      Q.projection.left ∣_ U := Scheme.Hom.resLE_eq_morphismRestrict ..
  let q' : openScheme G.val.X (torsorOpen U) ⟶ openScheme Q.scheme U :=
    Over.homMk (Q.projection.left ∣_ U) (by
      change (Q.projection.left ∣_ U) ≫ (U.ι ≫ Q.scheme.hom) =
        (torsorOpen U).ι ≫ G.val.X.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w Q.projection])
  have hq : q' = restrictOver Q.projection U (torsorOpen U) le_rfl :=
    Over.OverMorphism.ext hres.symm
  let i := openInclusion G.val.X (torsorOpen U)
  let q := restrictOver Q.projection U (torsorOpen U) le_rfl
  have w : i ≫ Q.projection = (q' ≫ s.val) ≫ L.projection := by
    rw [hq, Category.assoc, s.property, restrictOver_inclusion]
  have w' : i ≫ Q.projection = (q ≫ s.val) ≫ L.projection := by
    rw [Category.assoc, s.property, restrictOver_inclusion]
  have he : L.trivializes.lift i (q' ≫ s.val) w = L.trivializes.lift i (q ≫ s.val) w' := by
    apply L.trivializes.hom_ext
    · simp only [IsPullback.lift_fst]
    · simp only [IsPullback.lift_snd, hq, q]
  change (torsorOpen U).topIso.hom
    (lineCoordinate (L.trivializes.lift i (q' ≫ s.val) w ≫ prod.snd)) =
    (torsorOpen U).topIso.hom (lineCoordinate (L.trivializes.lift i (q ≫ s.val) w' ≫ prod.snd))
  rw [he]

private theorem topRegular_ext {T : SchemeOver k} (x y : Γ(T.left, ⊤))
    (h : ∀ (R : TestAlgebra k) (t : Points T R), t.left.appTop x = t.left.appTop y) : x = y := by
  apply (lineCoordinateEquiv T).symm.injective
  apply GrassmannianCharts.hom_ext_on_affines
  intro R t
  apply lineCoordinate_injective
  simpa only [lineCoordinate_comp, show ∀ z, lineCoordinate ((lineCoordinateEquiv T).symm z) = z
    from (lineCoordinateEquiv T).apply_symm_apply] using h R t

variable (h : FlagKernelPair Q) (U : Q.scheme.left.Opens)

private abbrev flagFirstLE (U : Q.scheme.left.Opens) :
    overlapOpen U ≤ (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X).left ⁻¹ᵁ torsorOpen U :=
  preimage_le _ _ _ rfl U

private abbrev flagSecondLE (h : FlagKernelPair Q) (U : Q.scheme.left.Opens) :
    overlapOpen U ≤ (HomogeneousQuotient.rightMultiplication P.negative).left ⁻¹ᵁ torsorOpen U :=
  preimage_le _ _ _ (congrArg Over.Hom.left h.w.symm) U

private def firstOnOpen (U : Q.scheme.left.Opens) :=
  restrictOver (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X)
    (torsorOpen U) (overlapOpen U) (flagFirstLE U)

private def secondOnOpen :=
  restrictOver (HomogeneousQuotient.rightMultiplication P.negative)
    (torsorOpen U) (overlapOpen U) (flagSecondLE h U)

private theorem topIso_inclusion_appTop {X : Scheme.{u}} (V : X.Opens) (c : Γ(X, ⊤)) :
    V.topIso.hom (V.ι.appTop c) = X.presheaf.map V.leTop.op c := by
  change (V.ι.appTop ≫ V.topIso.hom) c = _
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  rfl

private theorem covariance_eq_iff_coordinate (z : openScheme G.val.X (torsorOpen U) ⟶ affineLine k) :
    (flagLineData Q p χ h).covariance.app U ((torsorOpen U).topIso.hom (lineCoordinate z)) = 0 ↔
      lineCoordinate (secondOnOpen h U ≫ z) =
        lineCoordinate (firstOnOpen U ≫ z) *
          flagMultiplierAt (p := p) (χ := χ) (openInclusion _ (overlapOpen U)) := by
  unfold CovarianceData.covariance
  erw [covarianceMap_app]
  rw [sub_eq_zero]
  have hf := topIso_restrictOver
    (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X)
    (torsorOpen U) (overlapOpen U) (flagFirstLE U)
    ((torsorOpen U).topIso.hom (lineCoordinate z))
  have hs := topIso_restrictOver (HomogeneousQuotient.rightMultiplication P.negative)
    (torsorOpen U) (overlapOpen U) (flagSecondLE h U)
    ((torsorOpen U).topIso.hom (lineCoordinate z))
  simp only [Iso.hom_inv_id_apply] at hf hs
  let Z := (G.val.X ⨯ P.negative.group.X).left
  let x := (torsorOpen U).topIso.hom (lineCoordinate z)
  change (HomogeneousQuotient.rightMultiplication P.negative).left.appLE
      (torsorOpen U) (overlapOpen U) (flagSecondLE h U) x =
    (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X).left.appLE
      (torsorOpen U) (overlapOpen U) (flagFirstLE U) x *
      Z.presheaf.map (overlapOpen U).leTop.op (flagTransition p χ) ↔ _
  have ht := topIso_inclusion_appTop (overlapOpen U) (flagTransition p χ)
  rw [← hf, ← hs, ← ht, ← map_mul]
  exact (overlapOpen U).topIso.commRingCatIsoToRingEquiv.injective.eq_iff

private theorem covariance_eq_iff_graph (L : AssociatedBundle Q a p χ)
    (z : openScheme G.val.X (torsorOpen U) ⟶ affineLine k) :
    (flagLineData Q p χ h).covariance.app U ((torsorOpen U).topIso.hom (lineCoordinate z)) = 0 ↔
      firstOnOpen U ≫ bundleGraph L U z = secondOnOpen h U ≫ bundleGraph L U z := by
  rw [covariance_eq_iff_coordinate h U]
  let I := openInclusion (G.val.X ⨯ P.negative.group.X) (overlapOpen U)
  have points (R : TestAlgebra k) (t : Points (openScheme _ (overlapOpen U)) R) :
      let g := t ≫ I ≫ (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X)
      let b := t ≫ I ≫ (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X)
      t ≫ secondOnOpen h U ≫ openInclusion G.val.X (torsorOpen U) =
        g * (b ≫ P.negative.inclusion.hom.hom) := by
    rw [secondOnOpen, restrictOver_inclusion]
    have he : t ≫ I = prod.lift (t ≫ I ≫ (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X))
        (t ≫ I ≫ (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X)) := by
      ext <;> simp
    change (t ≫ I) ≫ HomogeneousQuotient.rightMultiplication P.negative = _
    rw [he]
    simp [HomogeneousQuotient.rightMultiplication, MonObj.comp_mul]
  have first (R : TestAlgebra k) (t : Points (openScheme _ (overlapOpen U)) R) :
      t ≫ firstOnOpen U ≫ openInclusion G.val.X (torsorOpen U) =
        t ≫ I ≫ (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) := by simp [firstOnOpen, I]
  let eval (R : TestAlgebra k) (t : Points (openScheme _
      (overlapOpen U)) R) :=
    (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
  have em (R : TestAlgebra k) (t : Points (openScheme _
      (overlapOpen U)) R) :
    eval R t (flagMultiplierAt (p := p) (χ := χ) I) =
      CharacterPairing.characterValue (p.projection ≫ χ) R
        ((t ≫ I ≫ (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X))⁻¹) := by
    change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (t.left.appTop (I.left.appTop (flagTransition p χ))) = _
    simpa only [flagMultiplierAt, Over.comp_left, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, Category.assoc] using
      flagMultiplierAt_testPoint (p := p) (χ := χ) R (t ≫ I)
  have graph (R : TestAlgebra k) (t : Points (openScheme _
      (overlapOpen U)) R)
      (j : openScheme _ (overlapOpen U) ⟶
        openScheme G.val.X (torsorOpen U)) :
      t ≫ j ≫ bundleGraph L U z =
        prod.lift (t ≫ j ≫ openInclusion G.val.X (torsorOpen U))
          (linePoint R (eval R t (lineCoordinate (j ≫ z)))) ≫ L.trivialization := by
    have w : linePoint R (eval R t (lineCoordinate (j ≫ z))) = t ≫ j ≫ z :=
      (lineCoordinate_testPoint R t (j ≫ z)).symm
    rw [w]
    simp only [bundleGraph, ← Category.assoc, prod.comp_lift]

  constructor
  · intro hc
    apply GrassmannianCharts.hom_ext_on_affines
    intro R t
    rw [graph, graph, first, points]
    rw [hc, map_mul, em, mul_comm]
    exact (L.transition _ _ _ _).symm
  · intro hg
    apply topRegular_ext
    intro R t
    apply (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
    change eval R t _ = eval R t _
    rw [map_mul, em]
    have ht := congrArg (t ≫ ·) hg
    rw [graph, graph, first, points] at ht
    rw [← L.transition R (t ≫ I ≫ prod.fst) (t ≫ I ≫ prod.snd)
      (eval R t (lineCoordinate (firstOnOpen U ≫ z)))] at ht
    have he := L.trivializes.hom_ext (by simp) ht
    have hh := congrArg (· ≫ (prod.snd : G.val.X ⨯ affineLine k ⟶ affineLine k)) he
    simp only [prod.lift_snd] at hh
    apply_fun lineCoordinate at hh
    simp only [lineCoordinate_linePoint] at hh
    exact ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective hh).symm.trans (mul_comm _ _)

private theorem firstOnOpen_projection :
    firstOnOpen U ≫ restrictOver Q.projection U _ le_rfl =
      secondOnOpen h U ≫ restrictOver Q.projection U _ le_rfl := by
  rw [← cancel_mono (openInclusion Q.scheme U)]
  simp only [Category.assoc, restrictOver_inclusion, firstOnOpen, secondOnOpen,
    restrictOver_inclusion_assoc, h.w]

private theorem equalizes_restrictedKernelPair (L : AssociatedBundle Q a p χ)
    (z : openScheme G.val.X (torsorOpen U) ⟶ affineLine k)
    (hz : firstOnOpen U ≫ bundleGraph L U z =
      secondOnOpen h U ≫ bundleGraph L U z) :
    ∀ (T : SchemeOver k) (x y : T ⟶ openScheme G.val.X (torsorOpen U)),
      x ≫ restrictOver Q.projection U _ le_rfl = y ≫ restrictOver Q.projection U _ le_rfl →
      x ≫ bundleGraph L U z = y ≫ bundleGraph L U z := by
  intro T x y w
  let i := openInclusion G.val.X (torsorOpen U)
  let q := restrictOver Q.projection U (torsorOpen U) le_rfl
  have w' : (x ≫ i) ≫ Q.projection = (y ≫ i) ≫ Q.projection := by
    simpa only [Category.assoc, i, restrictOver_inclusion] using
      congrArg (· ≫ openInclusion Q.scheme U) w
  let l := h.lift (x ≫ i) (y ≫ i) w'
  let D := flagLineData Q p χ h
  have hl : l ≫ D.overlapProjection = (x ≫ q) ≫ openInclusion Q.scheme U := by
    simp only [l, D, flagLineData, Category.assoc, IsPullback.lift_fst_assoc, q, i,
      restrictOver_inclusion]
  let t := (restrictOver_pullback D.overlapProjection U).lift l (x ≫ q) hl
  have ht : t ≫ openInclusion (G.val.X ⨯ P.negative.group.X) (overlapOpen U) = l :=
    (restrictOver_pullback D.overlapProjection U).lift_fst l (x ≫ q) hl
  have hx : t ≫ firstOnOpen U = x := by
    rw [← cancel_mono i, Category.assoc, firstOnOpen, restrictOver_inclusion,
      ← Category.assoc, ht]
    exact h.lift_fst _ _ _
  have hy : t ≫ secondOnOpen h U = y := by
    rw [← cancel_mono i, Category.assoc, secondOnOpen, restrictOver_inclusion,
      ← Category.assoc, ht]
    exact h.lift_snd _ _ _
  simpa only [Category.assoc, reassoc_of% hx, reassoc_of% hy] using congrArg (t ≫ ·) hz

private theorem bundleCoordinateMap_covariant (L : AssociatedBundle Q a p χ)
    (s : SectionsOver L.projection (openInclusion Q.scheme U)) :
    (flagLineData Q p χ h).covariance.app U (bundleSectionCoordinate L U s) = 0 := by
  rw [coordinate_agrees, covariance_eq_iff_graph h U L, bundleCoordinateMap_graph,
    ← Category.assoc, ← Category.assoc, firstOnOpen_projection h U]

private theorem bundleCoordinateMap_bijective (L : AssociatedBundle Q a p χ) :
    Function.Bijective (fun s : SectionsOver L.projection (openInclusion Q.scheme U) ↦
      (⟨bundleSectionCoordinate L U s, bundleCoordinateMap_covariant h U L s⟩ :
        {z : Γ(G.val.X.left, torsorOpen U) // (flagLineData Q p χ h).covariance.app U z = 0})) := by
  let q := restrictOver Q.projection U (torsorOpen U) le_rfl
  have eq : q.left = Q.projection.left ∣_ U := Scheme.Hom.resLE_eq_morphismRestrict ..
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  letI : Flat q.left := eq ▸ inferInstanceAs (Flat (Q.projection.left ∣_ U))
  letI : Surjective q.left := MorphismProperty.of_isPullback
    (show IsPullback (torsorOpen U).ι q.left Q.projection.left U.ι from
      eq.symm ▸ (isPullback_morphismRestrict _ _).flip) Q.surjective
  letI : LocallyOfFinitePresentation q.left := eq ▸
    inferInstanceAs (LocallyOfFinitePresentation (Q.projection.left ∣_ U))
  letI : Epi q := by
    haveI : Epi q.left := inferInstance
    exact Over.epi_of_epi_left _
  constructor
  · intro s t hst
    have he := congrArg Subtype.val hst
    simp only [coordinate_agrees] at he
    have hz := lineCoordinate_injective _ ((torsorOpen U).topIso.commRingCatIsoToRingEquiv.injective he)
    apply Subtype.ext
    apply (cancel_epi q).mp
    simpa only [bundleCoordinateMap_graph] using congrArg (bundleGraph L U) hz
  · intro ⟨x, hx⟩
    let e := lineCoordinateEquiv (openScheme G.val.X (torsorOpen U))
    let z := e.symm ((torsorOpen U).topIso.inv x)
    have hz : (torsorOpen U).topIso.hom (lineCoordinate z) = x := by
      change (torsorOpen U).topIso.hom (e (e.symm _)) = _
      rw [e.apply_symm_apply, Iso.inv_hom_id_apply (C := CommRingCat)]
    have hCov := (covariance_eq_iff_graph h U L z).mp (hz.symm ▸ hx)
    let w := bundleGraph L U z
    have he {T : Scheme.{u}} (a b : T ⟶ (openScheme G.val.X (torsorOpen U)).left)
        (hw : a ≫ q.left = b ≫ q.left) : a ≫ w.left = b ≫ w.left := by
      let T' : SchemeOver k := Over.mk (a ≫ (openScheme G.val.X (torsorOpen U)).hom)
      let a' : T' ⟶ _ := Over.homMk a rfl
      let b' : T' ⟶ openScheme G.val.X (torsorOpen U) := Over.homMk b (by
        change b ≫ (openScheme G.val.X (torsorOpen U)).hom =
          a ≫ (openScheme G.val.X (torsorOpen U)).hom
        rw [← Over.w q, ← Category.assoc, ← hw, Category.assoc])
      exact congrArg Over.Hom.left (equalizes_restrictedKernelPair h U L z hCov
        T' a' b' (Over.OverMorphism.ext hw))
    let d := EffectiveEpi.desc q.left w.left he
    have hd : q.left ≫ d = w.left := EffectiveEpi.fac _ _ _
    let s : openScheme Q.scheme U ⟶ L.total := Over.homMk d (by
      apply (cancel_epi q.left).mp
      rw [← Category.assoc, hd, Over.w, Over.w])
    have hs : q ≫ s = w := Over.OverMorphism.ext hd
    have hπ : s ≫ L.projection = openInclusion Q.scheme U := by
      rw [← cancel_epi q, ← Category.assoc, hs, bundleGraph_projection, restrictOver_inclusion]
    let S : SectionsOver L.projection (openInclusion Q.scheme U) := ⟨s, hπ⟩
    have hS : bundleCoordinateMap L U S = z := bundleGraph_injective L U <|
      (bundleCoordinateMap_graph L U S).trans hs
    exact ⟨S, Subtype.ext ((coordinate_agrees L U S).trans (hS ▸ hz))⟩

/-- The covariance equation identifies the kernel on an open with sections of
the associated bundle over that open. -/
def bundleSectionsOnOpen (L : AssociatedBundle Q a p χ) :
    Γ((flagLineData Q p χ h).sheaf, U) ≃ SectionsOver L.projection (openInclusion Q.scheme U) :=
  let D := flagLineData Q p χ h
  (Equiv.ofBijective _ (inclusion_bijective_onto_covariance D U)).trans
    (Equiv.ofBijective _ (bundleCoordinateMap_bijective h U L)).symm

/-- The equivalence uses exactly the coordinate of the given torsor trivialization. -/
theorem bundleSectionsOnOpen_coordinate (L : AssociatedBundle Q a p χ)
    (x : Γ((flagLineData Q p χ h).sheaf, U)) :
    bundleSectionCoordinate L U (bundleSectionsOnOpen h U L x) =
      (flagLineData Q p χ h).inclusion.app U x :=
  congrArg Subtype.val ((Equiv.ofBijective _ (bundleCoordinateMap_bijective h U L)).apply_symm_apply
    ((Equiv.ofBijective _ (inclusion_bijective_onto_covariance (flagLineData Q p χ h) U)) x))

@[reassoc (attr := simp)]
private theorem openRestriction_inclusion (X : SchemeOver k) {V W : X.left.Opens}
    (i : V ⟶ W) :
    openRestriction X i ≫ openInclusion X W = openInclusion X V :=
  Over.OverMorphism.ext (X.left.homOfLE_ι i.le)

private theorem topIso_openRestriction (X : SchemeOver k) {V W : X.left.Opens}
    (i : V ⟶ W) (z : Γ(X.left, W)) :
    V.topIso.hom ((openRestriction X i).left.appTop (W.topIso.inv z)) =
      X.left.presheaf.map i.op z := by
  have w : (openRestriction X i).left = (restrictOver (𝟙 X) W V i.le).left := by
    change X.left.homOfLE i.le = (𝟙 X.left : X.left ⟶ X.left).resLE W V i.le
    rw [Scheme.Hom.resLE_id]
  rw [w, topIso_restrictOver]
  change (𝟙 X.left : X.left ⟶ X.left).appLE W V i.le z = _
  unfold Scheme.Hom.appLE
  rw [Scheme.Hom.id_app, Category.id_comp]
  rfl

private theorem bundleCoordinate_restrict (L : AssociatedBundle Q a p χ)
    {V W : Q.scheme.left.Opens} (i : V ⟶ W)
    (s : SectionsOver L.projection (openInclusion Q.scheme W)) :
    bundleSectionCoordinate L V
      (⟨openRestriction Q.scheme i ≫ s.val,
        by rw [Category.assoc, s.property, openRestriction_inclusion]⟩) =
      G.val.X.left.presheaf.map ((Opens.map Q.projection.left.base).map i).op
        (bundleSectionCoordinate L W s) := by
  let j := (Opens.map Q.projection.left.base).map i
  let s' : SectionsOver L.projection (openInclusion Q.scheme V) :=
    ⟨openRestriction Q.scheme i ≫ s.val,
      by rw [Category.assoc, s.property, openRestriction_inclusion]⟩
  have hq :
      restrictOver Q.projection V _ le_rfl ≫ openRestriction Q.scheme i =
        openRestriction G.val.X j ≫ restrictOver Q.projection W _ le_rfl := by
    rw [← cancel_mono (openInclusion Q.scheme W)]
    simp only [Category.assoc, openRestriction_inclusion, restrictOver_inclusion,
      openRestriction_inclusion_assoc]
  have hz :
      bundleCoordinateMap L V s' = openRestriction G.val.X j ≫ bundleCoordinateMap L W s := by
    apply bundleGraph_injective
    rw [bundleCoordinateMap_graph]
    unfold bundleGraph
    rw [← openRestriction_inclusion G.val.X j, ← prod.comp_lift, Category.assoc]
    change restrictOver Q.projection V _ le_rfl ≫ (openRestriction Q.scheme i ≫ s.val) =
      openRestriction G.val.X j ≫ bundleGraph L W (bundleCoordinateMap L W s)
    rw [bundleCoordinateMap_graph, ← Category.assoc, hq, Category.assoc]
  change bundleSectionCoordinate L V s' = _
  rw [coordinate_agrees, coordinate_agrees, hz, lineCoordinate_comp]
  have h := topIso_openRestriction G.val.X j
    ((torsorOpen W).topIso.hom (lineCoordinate (bundleCoordinateMap L W s)))
  simpa only [Iso.hom_inv_id_apply] using h

/-- The identification of sections is natural under restriction of the base open. -/
theorem bundleSectionsOnOpen_natural (L : AssociatedBundle Q a p χ)
    {V W : Q.scheme.left.Opens} (i : V ⟶ W) (x : Γ((flagLineData Q p χ h).sheaf, W)) :
    (bundleSectionsOnOpen h V L ((flagLineData Q p χ h).sheaf.presheaf.map i.op x)).val =
      openRestriction Q.scheme i ≫ (bundleSectionsOnOpen h W L x).val := by
  let D := flagLineData Q p χ h
  let s := bundleSectionsOnOpen h W L x
  let t : SectionsOver L.projection (openInclusion Q.scheme V) :=
    ⟨openRestriction Q.scheme i ≫ s.val,
      by rw [Category.assoc, s.property, openRestriction_inclusion]⟩
  change _ = t.val
  apply congrArg Subtype.val
  apply (bundleCoordinateMap_bijective h V L).injective
  apply Subtype.ext
  change bundleSectionCoordinate L V _ = bundleSectionCoordinate L V t
  rw [bundleSectionsOnOpen_coordinate, bundleCoordinate_restrict (s := s)]
  unfold s
  rw [bundleSectionsOnOpen_coordinate]
  have w := (D.inclusion.mapPresheaf.naturality i.op)
  exact (congrArg (fun f : Γ(D.sheaf, W) ⟶
      Γ((Scheme.Modules.pushforward D.projection.left).obj (structureModule D.torsor.left), V) =>
    f x) w)

private def openLineCoordinate (X : SchemeOver k) (V : X.left.Opens) :
    (openScheme X V ⟶ affineLine k) ≃ Γ(X.left, V) :=
  (lineCoordinateEquiv (openScheme X V)).trans V.topIso.commRingCatIsoToRingEquiv.toEquiv

private theorem lineCoordinate_openLineCoordinate_symm (X : SchemeOver k) (V : X.left.Opens)
    (z : Γ(X.left, V)) :
    lineCoordinate ((openLineCoordinate X V).symm z) = V.topIso.inv z :=
  (lineCoordinateEquiv (openScheme X V)).apply_symm_apply (V.topIso.inv z)

variable {L : AssociatedBundle Q a p χ} {W : Q.scheme.left.Opens}
    {t : openScheme Q.scheme W ⨯ affineLine k ⟶ L.total}

private def sectionsOfChart
    (ht : IsPullback prod.fst t (openInclusion Q.scheme W) L.projection)
    {V : Q.scheme.left.Opens} (i : V ⟶ W) :
    Γ(Q.scheme.left, V) ≃ SectionsOver L.projection (openInclusion Q.scheme V) := by
  let j := openRestriction Q.scheme i
  let e := openLineCoordinate Q.scheme V
  refine
    { toFun := fun z => ⟨prod.lift j (e.symm z) ≫ t, by
        rw [Category.assoc, ← ht.w, prod.lift_fst_assoc, openRestriction_inclusion]⟩
      invFun := fun s => e (ht.lift j s.val (by rw [openRestriction_inclusion, s.property]) ≫ prod.snd)
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    -- Both graphs have the same projections to the chart and to the bundle.
    have he : ht.lift j (prod.lift j (e.symm z) ≫ t)
          (by rw [Category.assoc, ← ht.w, prod.lift_fst_assoc]) =
          prod.lift j (e.symm z) := by
      apply ht.hom_ext
      · simp
      · simp
    change e (ht.lift j (prod.lift j (e.symm z) ≫ t) _ ≫ prod.snd) = z
    rw [he, prod.lift_snd, e.apply_symm_apply]
  · intro s
    apply Subtype.ext
    let d := ht.lift j s.val (by rw [openRestriction_inclusion, s.property])
    have hd : prod.lift j (d ≫ prod.snd) = d := by
      apply prod.hom_ext
      · rw [prod.lift_fst, IsPullback.lift_fst]
      · rw [prod.lift_snd]
    change prod.lift j (e.symm (e (d ≫ prod.snd))) ≫ t = s.val
    rw [e.symm_apply_apply, hd, IsPullback.lift_snd]

private theorem chartSections_one_restrict
    (ht : IsPullback prod.fst t (openInclusion Q.scheme W) L.projection)
    {V : Q.scheme.left.Opens} (i : V ⟶ W) :
    (sectionsOfChart ht i 1).val =
      openRestriction Q.scheme i ≫ (sectionsOfChart ht (𝟙 W) 1).val := by
  unfold sectionsOfChart
  simp only [Equiv.coe_fn_mk, Subtype.coe_mk]
  change prod.lift (openRestriction Q.scheme i) ((openLineCoordinate Q.scheme V).symm 1) ≫ t =
    openRestriction Q.scheme i ≫ prod.lift (openRestriction Q.scheme (𝟙 W))
      ((openLineCoordinate Q.scheme W).symm 1) ≫ t
  rw [← Category.assoc, prod.comp_lift]
  apply congrArg (· ≫ t)
  apply prod.hom_ext
  · have hi : openRestriction Q.scheme (𝟙 W) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact Q.scheme.left.homOfLE_rfl W
    simp only [prod.lift_fst, hi, Category.comp_id]
  · rw [prod.lift_snd, prod.lift_snd]
    apply lineCoordinate_injective
    simp only [lineCoordinate_comp, lineCoordinate_openLineCoordinate_symm, map_one]

private abbrev ChartLinearity
    (t : openScheme Q.scheme W ⨯ affineLine k ⟶ L.total) : Prop :=
  ∀ (R : TestAlgebra k) (x : Points (openScheme Q.scheme W) R) (g : Points G.val.X R),
    x ≫ openInclusion Q.scheme W = g ≫ Q.projection →
    ∃ c : Rˣ, ∀ z : R, prod.lift x (linePoint R z) ≫ t =
      prod.lift g (linePoint R ((c : R) * z)) ≫ L.trivialization

private theorem bundleChartsOnOpens (L : AssociatedBundle Q a p χ) (y : Q.scheme.left) :
    ∃ (W : Q.scheme.left.Opens) (t : openScheme Q.scheme W ⨯ affineLine k ⟶ L.total),
      y ∈ W ∧ IsPullback prod.fst t (openInclusion Q.scheme W) L.projection ∧ ChartLinearity t := by
  obtain ⟨A, j, t, hOpen, hy, ht, hlinear⟩ := L.charts y
  letI : IsOpenImmersion j.left := hOpen
  let W := j.left.opensRange
  let e : openScheme Q.scheme W ⟶ A :=
    Over.homMk j.left.isoOpensRange.inv (by
      change j.left.isoOpensRange.inv ≫ A.hom = W.ι ≫ Q.scheme.hom
      rw [← Over.w j, ← Category.assoc, j.left.isoOpensRange_inv_comp])
  have he : e ≫ j = openInclusion Q.scheme W :=
    Over.OverMorphism.ext (j.left.isoOpensRange_inv_comp)
  letI : IsIso e := by
    letI : IsIso e.left := inferInstanceAs (IsIso j.left.isoOpensRange.inv)
    exact (isIso_iff_of_reflects_iso e (Over.forget (Spec (CommRingCat.of k)))).1
      (inferInstanceAs (IsIso e.left))
  let l := prod.map e (𝟙 (affineLine k))
  letI : IsIso l := by dsimp [l]; infer_instance
  have hp : IsPullback l prod.fst prod.fst e :=
    IsPullback.of_horiz_isIso ⟨by simp [l]⟩
  refine ⟨W, l ≫ t, hy, ?_, ?_⟩
  · rw [← he]
    exact (hp.paste_horiz ht.flip).flip
  · intro R x g w
    obtain ⟨c, hc⟩ := hlinear R (x ≫ e) g (by simpa only [Category.assoc, he] using w)
    refine ⟨c, fun z => ?_⟩
    rw [← Category.assoc, prod.lift_map, Category.comp_id]
    exact hc z

private def chartToCovariance (h : FlagKernelPair Q)
    (ht : IsPullback prod.fst t (openInclusion Q.scheme W) L.projection)
    {V : Q.scheme.left.Opens} (i : V ⟶ W) :
    Γ(Q.scheme.left, V) ≃ Γ((flagLineData Q p χ h).sheaf, V) :=
  (sectionsOfChart ht i).trans (bundleSectionsOnOpen h V L).symm

private theorem chartToCovariance_smul_one (h : FlagKernelPair Q)
    (ht : IsPullback prod.fst t (openInclusion Q.scheme W) L.projection)
    (hlinear : ChartLinearity t) {V : Q.scheme.left.Opens} (i : V ⟶ W)
    (r : Γ(Q.scheme.left, V)) :
    chartToCovariance h ht i r = r • chartToCovariance h ht i 1 := by
  let D := flagLineData Q p χ h
  let T := openScheme G.val.X (torsorOpen V)
  let q := restrictOver Q.projection V (torsorOpen V) le_rfl
  let e := openLineCoordinate Q.scheme V
  let c (r : Γ(Q.scheme.left, V)) := bundleCoordinateMap L V (sectionsOfChart ht i r)
  have hcoord (r : Γ(Q.scheme.left, V)) :
      D.inclusion.app V (chartToCovariance h ht i r) = (torsorOpen V).topIso.hom (lineCoordinate (c r)) :=
    (bundleSectionsOnOpen_coordinate h V L (chartToCovariance h ht i r)).symm.trans (by
      change bundleSectionCoordinate L V ((bundleSectionsOnOpen h V L)
        ((bundleSectionsOnOpen h V L).symm (sectionsOfChart ht i r))) = _
      rw [Equiv.apply_symm_apply, coordinate_agrees])
  have hlin :
      lineCoordinate (c r) = q.left.appTop (V.topIso.inv r) * lineCoordinate (c 1) := by
    apply topRegular_ext
    intro R x
    let v := x ≫ q
    let g := x ≫ openInclusion G.val.X (torsorOpen V)
    let u := v ≫ openRestriction Q.scheme i
    have w : u ≫ openInclusion Q.scheme W = g ≫ Q.projection := by
      simp only [u, v, g, Category.assoc, openRestriction_inclusion, q, restrictOver_inclusion]
    obtain ⟨c₀, hl⟩ := hlinear R u g w
    let ev (x : Points T R) : Γ(T.left, ⊤) →+* R :=
      (x.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
    let evV : Γ((openScheme Q.scheme V).left, ⊤) →+* R :=
      (v.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
    have hc (z : Γ(Q.scheme.left, V)) : ev x (lineCoordinate (c z)) = (c₀ : R) * evV (V.topIso.inv z) := by
      have h := congrArg (x ≫ ·) (bundleCoordinateMap_graph L V (sectionsOfChart ht i z))
      change x ≫ (prod.lift (openInclusion G.val.X (torsorOpen V)) (c z) ≫ L.trivialization) =
        x ≫ q ≫ (prod.lift (openRestriction Q.scheme i) (e.symm z) ≫ t) at h
      simp only [← Category.assoc, prod.comp_lift] at h
      have h₁ : x ≫ c z = linePoint R (ev x (lineCoordinate (c z))) :=
        lineCoordinate_testPoint R x (c z)
      have h₂ : v ≫ e.symm z = linePoint R (evV (V.topIso.inv z)) := by
        have he := lineCoordinate_testPoint R v (e.symm z)
        rw [lineCoordinate_openLineCoordinate_symm] at he
        exact he
      change prod.lift g (x ≫ c z) ≫ L.trivialization = prod.lift u (v ≫ e.symm z) ≫ t at h
      rw [h₁, h₂, hl] at h
      have hprod := L.trivializes.hom_ext (by simp) h
      have hval := congrArg (· ≫ (prod.snd : G.val.X ⨯ affineLine k ⟶ affineLine k)) hprod
      simp only [prod.lift_snd] at hval
      have hh := congrArg lineCoordinate hval
      rw [lineCoordinate_linePoint, lineCoordinate_linePoint] at hh
      exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective hh
    apply (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
    change ev x (lineCoordinate (c r)) = ev x (q.left.appTop (V.topIso.inv r) * lineCoordinate (c 1))
    have hev : ev x (q.left.appTop (V.topIso.inv r)) = evV (V.topIso.inv r) := by
      change _ = ((v.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom) _
      rw [show v.left.appTop = q.left.appTop ≫ x.left.appTop from rfl]
      rfl
    rw [map_mul, hc, hc, hev, map_one, map_one, mul_one, mul_comm]
  apply (inclusion_bijective_onto_covariance D V).injective
  apply Subtype.ext
  change D.inclusion.app V (chartToCovariance h ht i r) =
    D.inclusion.app V (r • chartToCovariance h ht i 1)
  rw [Scheme.Modules.Hom.app_smul, hcoord, hcoord, hlin, map_mul,
    topIso_restrictOver Q.projection]
  change _ = Q.projection.left.app V r * _
  rw [Scheme.Hom.appLE_eq_app]

private theorem chartToCovariance_one_natural (h : FlagKernelPair Q)
    (ht : IsPullback prod.fst t (openInclusion Q.scheme W) L.projection)
    {V : Q.scheme.left.Opens} (i : V ⟶ W) :
    (flagLineData Q p χ h).sheaf.presheaf.map i.op (chartToCovariance h ht (𝟙 W) 1) =
       chartToCovariance h ht i 1 := by
  apply (bundleSectionsOnOpen h V L).injective
  apply Subtype.ext
  rw [bundleSectionsOnOpen_natural h L]
  have e₁ : bundleSectionsOnOpen h W L (chartToCovariance h ht (𝟙 W) 1) =
      sectionsOfChart ht (𝟙 W) 1 :=
    (bundleSectionsOnOpen h W L).apply_symm_apply _
  have e₂ : bundleSectionsOnOpen h V L (chartToCovariance h ht i 1) =
      sectionsOfChart ht i 1 :=
    (bundleSectionsOnOpen h V L).apply_symm_apply _
  rw [e₁, e₂]
  exact (chartSections_one_restrict ht i).symm

private def chartTrivializationIso (h : FlagKernelPair Q)
    (ht : IsPullback prod.fst t (openInclusion Q.scheme W) L.projection)
    (hlin : ChartLinearity t) :
    SheafOfModules.unit (Q.scheme.left.ringCatSheaf.over W) ≅
      (flagLineData Q p χ h).sheaf.over W := by
  let M := (flagLineData Q p χ h).sheaf
  let S := Q.scheme.left.ringCatSheaf.over W
  let σ : (M.over W).sections := PresheafOfModules.sectionsMk
    (fun V => chartToCovariance h ht V.unop.hom 1) (by
      intro U V j
      change M.presheaf.map j.unop.left.op (chartToCovariance h ht U.unop.hom 1) =
        chartToCovariance h ht V.unop.hom 1
      rw [← chartToCovariance_one_natural h ht U.unop.hom,
        ← chartToCovariance_one_natural h ht V.unop.hom]
      change (M.presheaf.map U.unop.hom.op ≫ M.presheaf.map j.unop.left.op) _ =
        M.presheaf.map V.unop.hom.op _
      rw [← M.presheaf.map_comp, ← op_comp, Over.w j.unop])
  let m := (M.over W).unitHomEquiv.symm σ
  have hIso : IsIso m := by
    let F := SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj
    apply (isIso_iff_of_reflects_iso m F).mp
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun r : Γ(Q.scheme.left, V.unop.left) =>
      r • chartToCovariance h ht V.unop.hom 1)
    have w : (fun r : Γ(Q.scheme.left, V.unop.left) =>
        r • chartToCovariance h ht V.unop.hom 1) = chartToCovariance h ht V.unop.hom := by
      funext r
      exact (chartToCovariance_smul_one h ht hlin V.unop.hom r).symm
    rw [w]
    exact (chartToCovariance h ht V.unop.hom).bijective
  exact asIso m

private def freeSingletonIso
    {C : Type u} [Category* C] {J : GrothendieckTopology C} (S : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    SheafOfModules.free (R := S) (PUnit.{u + 1}) ≅ SheafOfModules.unit S where
  hom := Sigma.desc (fun _ : PUnit.{u + 1} => 𝟙 (SheafOfModules.unit S))
  inv := SheafOfModules.ιFree PUnit.unit
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i
    simp [SheafOfModules.ιFree, SheafOfModules.free]
  inv_hom_id := by simp [SheafOfModules.ιFree, SheafOfModules.free]

private def freeIsoGenerators
    {C : Type u} [Category* C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules S} (e : SheafOfModules.free (PUnit.{u + 1}) ≅ M) :
    M.GeneratingSections where
  I := PUnit.{u + 1}
  s := M.freeHomEquiv e.hom
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

private theorem freeIsoGenerators_iso
    {C : Type u} [Category* C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules S} (e : SheafOfModules.free (PUnit.{u + 1}) ≅ M) :
    IsIso (freeIsoGenerators e).π := by
  change IsIso (M.freeHomEquiv.symm (M.freeHomEquiv e.hom))
  rw [Equiv.symm_apply_apply]
  infer_instance

set_option maxHeartbeats 600000 in
private theorem quasicoherent_of_unit_on_cover {X : Scheme.{u}}
    (M : SheafOfModules X.ringCatSheaf) {I : Type u} (U : I → X.Opens)
    (hU : IsOpenCover U)
    (e : ∀ i, SheafOfModules.unit (X.ringCatSheaf.over (U i)) ≅ M.over (U i)) :
    M.IsQuasicoherent := by
  let e' (i : I) :
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (PUnit.{u + 1}) ≅ M.over (U i) :=
    freeSingletonIso (X.ringCatSheaf.over (U i)) ≪≫ e i
  let gen (i : I) : (M.over (U i)).GeneratingSections := freeIsoGenerators (e' i)
  have hgen (i : I) : IsIso (gen i).π := freeIsoGenerators_iso (e' i)
  let q : M.LocalGeneratorsData :=
    { I := I
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr hU
      generators := gen }
  let : q.IsLocallyFreeData :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.mk (q := q) hgen
  exact q.quasiCoherentData.isQuasicoherent

end BundleDescent

set_option backward.isDefEq.respectTransparency false in
theorem flagLineSheafIdentification.{u} : FlagLineSheafIdentification.{u} := by
  intro k _ G P Q p χ h a L
  classical
  let M := (flagLineData Q p χ h).sheaf
  choose W t hy ht hl using bundleChartsOnOpens L
  let E (y : Q.scheme.left) := chartTrivializationIso h (ht y) (hl y)
  refine ⟨?_, ?_, fun V => bundleSectionsOnOpen h V L,
    fun V => bundleSectionsOnOpen_coordinate h V L, ?_⟩
  · have cov : (⨆ y, W y) = ⊤ := by
      apply top_unique
      intro y _
      exact Opens.mem_iSup.mpr ⟨y, hy y⟩
    exact quasicoherent_of_unit_on_cover M W cov E
  · intro y
    let F := (Scheme.Modules.overEquiv (W y)).functor
    refine ⟨W y, hy y, ⟨((Scheme.Modules.overFunctorEquiv (W y)).app M).symm ≪≫
      F.mapIso (E y).symm ≪≫ (W y).sheafOfModulesEquivOverUnit Q.scheme.left.ringCatSheaf⟩⟩
  · intro V W i x
    exact bundleSectionsOnOpen_natural h L i x

section CovariancePullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B}

private abbrev pullbackOnOpen {T S Z : Scheme.{u}} (q : T ⟶ Z) (r : S ⟶ Z)
    (b : S ⟶ T) (h : b ≫ q = r) (U : Z.Opens) :
    Γ(T, q ⁻¹ᵁ U) ⟶ Γ(S, r ⁻¹ᵁ U) :=
  b.appLE (q ⁻¹ᵁ U) (r ⁻¹ᵁ U) (preimage_le q r b h U)

private theorem pullbackOnOpen_comp {T S W Z : Scheme.{u}}
    (q : T ⟶ Z) (r : S ⟶ Z) (s : W ⟶ Z)
    (b : S ⟶ T) (c : W ⟶ S) (hb : b ≫ q = r) (hc : c ≫ r = s) (U : Z.Opens) :
    pullbackOnOpen q r b hb U ≫ pullbackOnOpen r s c hc U =
      pullbackOnOpen q s (c ≫ b) (by rw [Category.assoc, hb, hc]) U :=
  Scheme.Hom.appLE_comp_appLE c b _ _ _ _ _

private theorem pullbackOnOpen_congr {T S Z : Scheme.{u}} (q : T ⟶ Z) (r : S ⟶ Z)
    {a b : S ⟶ T} (h : a = b) (ha : a ≫ q = r) (hb : b ≫ q = r) (U : Z.Opens) :
    pullbackOnOpen q r a ha U = pullbackOnOpen q r b hb U := by
  subst h
  rfl

private theorem pullbackOnOpen_restrict_global {T S Z : Scheme.{u}}
    (q : T ⟶ Z) (r : S ⟶ Z) (b : S ⟶ T) (h : b ≫ q = r)
    (U : Z.Opens) (z : Γ(T, ⊤)) :
    pullbackOnOpen q r b h U (T.presheaf.map (q ⁻¹ᵁ U).leTop.op z) =
      S.presheaf.map (r ⁻¹ᵁ U).leTop.op (b.appTop z) := by
  change (T.presheaf.map (q ⁻¹ᵁ U).leTop.op ≫ pullbackOnOpen q r b h U) z =
    (b.appTop ≫ S.presheaf.map (r ⁻¹ᵁ U).leTop.op) z
  have w : T.presheaf.map (q ⁻¹ᵁ U).leTop.op ≫ pullbackOnOpen q r b h U =
      b.appTop ≫ S.presheaf.map (r ⁻¹ᵁ U).leTop.op := by
    erw [b.map_appLE]
    rfl
  exact congrArg (fun f : Γ(T, ⊤) ⟶ Γ(S, r ⁻¹ᵁ U) => f z) w

variable (D : CovarianceData X) (D' : CovarianceData Y)
    (f : Y.left ⟶ X.left) (g : D'.torsor.left ⟶ D.torsor.left)
    (w : g ≫ D.projection.left = D'.projection.left ≫ f)

private theorem pullFunctions_app (U : X.left.Opens)
    (x : Γ(D.torsor.left, D.projection.left ⁻¹ᵁ U)) :
    (D.pullFunctions D' f g w).app U x =
      pullbackOnOpen D.projection.left (D'.projection.left ≫ f) g w U x := by
  unfold CovarianceData.pullFunctions
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_inv_app_app, Category.comp_id]
  exact overPullbackRegular_app _ _ _ _ U x

private theorem firstLeft_w (D : CovarianceData X) :
    D.first.left ≫ D.projection.left = D.overlapProjection.left :=
  congrArg Over.Hom.left D.fst_w

private theorem secondLeft_w (D : CovarianceData X) :
    D.second.left ≫ D.projection.left = D.overlapProjection.left :=
  congrArg Over.Hom.left D.snd_w

private theorem firstLeft_over (D' : CovarianceData Y) (f : Y.left ⟶ X.left) :
    D'.first.left ≫ (D'.projection.left ≫ f) = D'.overlapProjection.left ≫ f := by
  rw [← Category.assoc, firstLeft_w]

private theorem secondLeft_over (D' : CovarianceData Y) (f : Y.left ⟶ X.left) :
    D'.second.left ≫ (D'.projection.left ≫ f) = D'.overlapProjection.left ≫ f := by
  rw [← Category.assoc, secondLeft_w]

private theorem covariance_app_eq_zero (D : CovarianceData X) (U : X.left.Opens)
    (a : Γ(D.torsor.left, D.projection.left ⁻¹ᵁ U)) :
    D.covariance.app U a = 0 ↔
      pullbackOnOpen D.projection.left D.overlapProjection.left D.second.left (secondLeft_w D) U a =
        pullbackOnOpen D.projection.left D.overlapProjection.left D.first.left (firstLeft_w D) U a *
          D.overlap.left.presheaf.map (D.overlapProjection.left ⁻¹ᵁ U).leTop.op D.multiplier := by
  unfold CovarianceData.covariance
  rw [covarianceMap_app, sub_eq_zero]

private theorem map_covariance_equation {T T' S S' : CommRingCat.{u}}
    (f₀ f₁ : T ⟶ S) (f₀' f₁' : T' ⟶ S') (q : T ⟶ T') (r : S ⟶ S')
    (h₀ : f₀ ≫ r = q ≫ f₀') (h₁ : f₁ ≫ r = q ≫ f₁')
    (z : T) (c : S) (c' : S') (hc : r c = c') (h : f₁ z = f₀ z * c) :
    f₁' (q z) = f₀' (q z) * c' := by
  have w₀ : r (f₀ z) = f₀' (q z) := congrArg (fun g : T ⟶ S' => g z) h₀
  have w₁ : r (f₁ z) = f₁' (q z) := congrArg (fun g : T ⟶ S' => g z) h₁
  calc
    f₁' (q z) = r (f₁ z) := w₁.symm
    _ = r (f₀ z * c) := congrArg (fun y : S => r y) h
    _ = r (f₀ z) * r c := map_mul r.hom ..
    _ = f₀' (q z) * c' := congrArg₂ (· * ·) w₀ hc

private theorem covarianceMap_pullback (j : D'.overlap.left ⟶ D.overlap.left)
    (h₀ : j ≫ D.first.left = D'.first.left ≫ g)
    (h₁ : j ≫ D.second.left = D'.second.left ≫ g)
    (hc : j.appTop D.multiplier = D'.multiplier)
    (U : X.left.Opens) (x : Γ(D.sheaf, U)) :
    D'.covariance.app (f ⁻¹ᵁ U) ((D.pullFunctions D' f g w).app U (D.inclusion.app U x)) = 0 := by
  let q := D.projection.left
  let r := D.overlapProjection.left
  let q' := D'.projection.left ≫ f
  let r' := D'.overlapProjection.left ≫ f
  have wj : j ≫ r = r' := by
    change j ≫ D.overlapProjection.left = D'.overlapProjection.left ≫ f
    rw [← firstLeft_w D, ← Category.assoc, h₀, Category.assoc, w, firstLeft_over]
  let a : Γ(D.torsor.left, q ⁻¹ᵁ U) := D.inclusion.app U x
  let b := pullbackOnOpen r r' j wj U
  let b₀ := pullbackOnOpen q r D.first.left (firstLeft_w D) U
  let b₁ := pullbackOnOpen q r D.second.left (secondLeft_w D) U
  let gU := pullbackOnOpen q q' g w U
  let b₀' := pullbackOnOpen q' r' D'.first.left (firstLeft_over D' f) U
  let b₁' := pullbackOnOpen q' r' D'.second.left (secondLeft_over D' f) U
  have hb₀ : b₀ ≫ b = gU ≫ b₀' := by
    dsimp only [b₀, b, gU, b₀']
    rw [pullbackOnOpen_comp, pullbackOnOpen_comp]
    exact pullbackOnOpen_congr q r' h₀ _ _ U
  have hb₁ : b₁ ≫ b = gU ≫ b₁' := by
    dsimp only [b₁, b, gU, b₁']
    rw [pullbackOnOpen_comp, pullbackOnOpen_comp]
    exact pullbackOnOpen_congr q r' h₁ _ _ U
  have hmult := pullbackOnOpen_restrict_global r r' j wj U D.multiplier
  rw [hc] at hmult
  have ha : b₁ a = b₀ a * D.overlap.left.presheaf.map (r ⁻¹ᵁ U).leTop.op D.multiplier :=
    (covariance_app_eq_zero D U a).mp (regularSection_mem_covariance D U x)
  have H := map_covariance_equation b₀ b₁ b₀' b₁' gU b hb₀ hb₁ a _ _ hmult ha
  have hresult : D'.covariance.app (f ⁻¹ᵁ U) (gU a) = 0 :=
    (covariance_app_eq_zero D' (f ⁻¹ᵁ U) (gU a)).mpr H
  have hpull : (D.pullFunctions D' f g w).app U a = gU a :=
    pullFunctions_app D D' f g w U a
  change D'.covariance.app (f ⁻¹ᵁ U) ((D.pullFunctions D' f g w).app U a) = 0
  rw [hpull]
  exact hresult

/-- A map of the torsors and overlaps that preserves the multiplier induces
the pullback map on the two covariance kernels. -/
theorem covariancePullback_exists (j : D'.overlap.left ⟶ D.overlap.left)
    (h₀ : j ≫ D.first.left = D'.first.left ≫ g)
    (h₁ : j ≫ D.second.left = D'.second.left ≫ g)
    (hc : j.appTop D.multiplier = D'.multiplier) :
    ∃ α, D.IsPullbackMap D' f g w α := by
  let P := Scheme.Modules.pushforward f
  let a := D.inclusion ≫ D.pullFunctions D' f g w
  have ha : a ≫ P.map D'.covariance = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    exact covarianceMap_pullback D D' f g w j h₀ h₁ hc U x
  let : PreservesLimit (parallelPair D'.covariance 0) P := inferInstance
  refine ⟨kernel.lift (P.map D'.covariance) a ha ≫
    (PreservesKernel.iso P D'.covariance).inv, ?_⟩
  change _ ≫ P.map (kernel.ι D'.covariance) = a
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- Pullback of covariant functions under scalar extension gives the comparison
morphism of coefficient sheaves. -/
theorem scalarExtension_coefficientMap {k : Type u} [Field k] {X : SchemeOver k}
    (R : TestAlgebra k) (D : CovarianceData X) :
    ∃ α, D.IsPullbackMap (D.extend R) (extensionProjection R X)
      (extensionProjection R D.torsor) (extensionProjection_natural R D.projection).symm α :=
  covariancePullback_exists D (D.extend R) (extensionProjection R X) (extensionProjection R D.torsor)
    (extensionProjection_natural R D.projection).symm (extensionProjection R D.overlap)
    (extensionProjection_natural R D.first).symm
    (extensionProjection_natural R D.second).symm rfl

end CovariancePullback

section CovarianceComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} {Z : SchemeOverRing C}
    {D : CovarianceData X} {D' : CovarianceData Y} {D'' : CovarianceData Z}

private theorem covariancePullback_app {f : Y.left ⟶ X.left}
    {t : D'.torsor.left ⟶ D.torsor.left}
    {w : t ≫ D.projection.left = D'.projection.left ≫ f}
    {α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D'.sheaf}
    (hα : D.IsPullbackMap D' f t w α) (U : X.left.Opens) (x : Γ(D.sheaf, U)) :
    D'.inclusion.app (f ⁻¹ᵁ U) (α.app U x) =
      pullbackOnOpen D.projection.left (D'.projection.left ≫ f) t w U (D.inclusion.app U x) := by
  have h := congrArg (fun a => (Scheme.Modules.Hom.app a U) x) hα
  change ((Scheme.Modules.pushforward f).map D'.inclusion).app U (α.app U x) =
    (D.pullFunctions D' f t w).app U (D.inclusion.app U x) at h
  rw [Scheme.Modules.pushforward_map_app, pullFunctions_app] at h
  exact h

/-- Pullback maps on covariance coefficients compose along the original
scheme maps on the base and torsor. -/
theorem covariancePullback_comp
    {f : Y.left ⟶ X.left} {g : Z.left ⟶ Y.left}
    {t : D'.torsor.left ⟶ D.torsor.left} {s : D''.torsor.left ⟶ D'.torsor.left}
    {w : t ≫ D.projection.left = D'.projection.left ≫ f}
    {w' : s ≫ D'.projection.left = D''.projection.left ≫ g}
    {α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D'.sheaf}
    {β : D'.sheaf ⟶ (Scheme.Modules.pushforward g).obj D''.sheaf}
    (hα : D.IsPullbackMap D' f t w α) (hβ : D'.IsPullbackMap D'' g s w' β) :
    D.IsPullbackMap D'' (g ≫ f) (s ≫ t)
      (by rw [Category.assoc, w, ← Category.assoc, w', Category.assoc])
      (α ≫ (Scheme.Modules.pushforward f).map β ≫
        (Scheme.Modules.pushforwardComp g f).hom.app D''.sheaf) := by
  let q := D.projection.left
  let q' := D'.projection.left ≫ f
  let q'' := D''.projection.left ≫ g ≫ f
  have ws : s ≫ q' = q'' := by
    change s ≫ D'.projection.left ≫ f = D''.projection.left ≫ g ≫ f
    rw [← Category.assoc, w', Category.assoc]
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply, pullFunctions_app]
  change D''.inclusion.app (g ⁻¹ᵁ (f ⁻¹ᵁ U)) (β.app (f ⁻¹ᵁ U) (α.app U x)) = _
  rw [covariancePullback_app hβ, covariancePullback_app hα]
  change pullbackOnOpen q' q'' s ws U
      (pullbackOnOpen q q' t w U (D.inclusion.app U x)) = _
  exact congrArg (fun F => F (D.inclusion.app U x)) (pullbackOnOpen_comp q q' q'' t s w ws U)

end CovarianceComposition


section LocalScalarExtension

open private groundRingHom_over from Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}

private theorem groundRingHomOpen_pullback (φ : A →+* B) (f : Y.left ⟶ X.left)
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.left.Opens) :
    (f.app U).hom.comp (groundRingHomOpen X U) =
      (groundRingHomOpen Y (f ⁻¹ᵁ U)).comp φ := by
  ext r
  change (X.left.presheaf.map U.leTop.op ≫ f.app U) (groundRingHom X r) =
    Y.left.presheaf.map (f ⁻¹ᵁ U).leTop.op (groundRingHom Y (φ r))
  rw [f.naturality]
  have h := groundRingHom_over φ f hf
  exact congrArg (Y.left.presheaf.map (f ⁻¹ᵁ U).leTop.op) (DFunLike.congr_fun h r)

private theorem groundRingHomOpen_eq_appLE (U : X.left.Opens) :
    CommRingCat.ofHom (groundRingHomOpen X U) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ X.hom.appLE ⊤ U (by simp) := by
  rfl

/-- On any open, pushforward changes only the open and the restriction of
scalars. This comparison retains the original map of schemes on sections. -/
private def pushforwardLocalSectionsIso (φ : A →+* B) (f : Y.left ⟶ X.left)
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (F : Y.left.Modules) (U : X.left.Opens) :
    localSections ((Scheme.Modules.pushforward f).obj F) U ≅
      (ModuleCat.restrictScalars.{u} φ).obj (localSections F (f ⁻¹ᵁ U)) :=
  (ModuleCat.restrictScalarsComp'App (groundRingHomOpen X U) (f.app U).hom
    ((f.app U).hom.comp (groundRingHomOpen X U)) rfl (F.val.obj (op (f ⁻¹ᵁ U)))).symm ≪≫
  ModuleCat.restrictScalarsComp'App φ (groundRingHomOpen Y (f ⁻¹ᵁ U))
    ((f.app U).hom.comp (groundRingHomOpen X U)) (groundRingHomOpen_pullback φ f hf U)
    (F.val.obj (op (f ⁻¹ᵁ U)))

private def localSectionsMap {F F' : X.left.Modules} (m : F ⟶ F') (U : X.left.Opens) :
    localSections F U ⟶ localSections F' U :=
  (coefficientPresheafMap m).app (op U)

private abbrev regularModuleOpen (X : SchemeOverRing A) (U : X.left.Opens) :=
  localSections (structureModule X.left) U

variable {k : Type u} [Field k] (R : TestAlgebra k) (S : SchemeOver k)

private theorem affineOpenRegularPushout (U : S.left.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (algebraMap k R))
      (CommRingCat.ofHom (groundRingHomOpen S U))
      (CommRingCat.ofHom (groundRingHomOpen ((extendScheme R).obj S) (extensionProjection R S ⁻¹ᵁ U)))
      ((extensionProjection R S).app U) := by
  let Y := (extendScheme R).obj S
  let v := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let e := extensionProjection R S
  have hp : IsPullback e Y.hom S.hom v := IsPullback.of_hasPullback _ _
  have hUY : e ⁻¹ᵁ U = e ⁻¹ᵁ U ⊓ Y.hom ⁻¹ᵁ ⊤ := by simp
  have hUT : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ v ⁻¹ᵁ ⊤ := by simp
  have hUS : U ≤ S.hom ⁻¹ᵁ ⊤ := by simp
  have hTopA : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hTopB : IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens) := isAffineOpen_top _
  have hi := (isIso_pushoutSection_iff hp hUT hUS hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hp hUT hUS hUY hTopA hTopB hU)
  refine hi.flip.of_iso' (Scheme.ΓSpecIso (CommRingCat.of k)).symm
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ v.appLE ⊤ ⊤ hUT =
      CommRingCat.ofHom (algebraMap k R) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv
    change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        v.appLE ⊤ (v ⁻¹ᵁ ⊤) le_rfl = _
    rw [v.appLE_eq_app]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      (groundRingHomOpen_eq_appLE (X := S) U).symm
  · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      (groundRingHomOpen_eq_appLE (X := Y) (e ⁻¹ᵁ U)).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact e.appLE_eq_app

/-- The base change of regular functions on an affine open is its ring of
sections tensored from the field to the test algebra. -/
private def affineOpenRegularExtendIso (U : S.left.Opens) (hU : IsAffineOpen U) :
    (extendToAlgebra (k := k) (K := R)).obj (regularModuleOpen S U) ≅
      regularModuleOpen ((extendScheme R).obj S) (extensionProjection R S ⁻¹ᵁ U) := by
  let Y := (extendScheme R).obj S
  let V := extensionProjection R S ⁻¹ᵁ U
  let M := Γ(S.left, U)
  let N := Γ(Y.left, V)
  let rk := algebraMap k R
  letI : Algebra k R := rk.toAlgebra
  letI : Algebra k M := (groundRingHomOpen S U).toAlgebra
  letI : Algebra R N := (groundRingHomOpen Y V).toAlgebra
  letI : Algebra M N := ((extensionProjection R S).app U).hom.toAlgebra
  letI : Algebra k N := ((groundRingHomOpen Y V).comp rk).toAlgebra
  haveI : IsScalarTower k R N := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k M N := IsScalarTower.of_algebraMap_eq'
    (groundRingHomOpen_pullback rk (extensionProjection R S) (extensionProjection_over R S) U).symm
  haveI : Algebra.IsPushout k R M N :=
    CommRingCat.isPushout_iff_isPushout.mp (affineOpenRegularPushout R S U hU)
  exact (Algebra.IsPushout.equiv k R M N).toLinearEquiv.toModuleIso

private theorem affineOpenRegularExtendIso_tmul (U : S.left.Opens) (hU : IsAffineOpen U)
    (r : R) (x : regularModuleOpen S U) :
    (affineOpenRegularExtendIso R S U hU).hom (r ⊗ₜ[k,algebraMap k R] x) =
      groundRingHomOpen ((extendScheme R).obj S) (extensionProjection R S ⁻¹ᵁ U) r *
        (extensionProjection R S).app U x := by
  let Y := (extendScheme R).obj S
  let V := extensionProjection R S ⁻¹ᵁ U
  let M := Γ(S.left, U)
  let N := Γ(Y.left, V)
  let rk := algebraMap k R
  let : Algebra k R := rk.toAlgebra
  let : Algebra k M := (groundRingHomOpen S U).toAlgebra
  let : Algebra R N := (groundRingHomOpen Y V).toAlgebra
  let : Algebra M N := ((extensionProjection R S).app U).hom.toAlgebra
  let : Algebra k N := ((groundRingHomOpen Y V).comp rk).toAlgebra
  have : IsScalarTower k R N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k M N := IsScalarTower.of_algebraMap_eq'
    (groundRingHomOpen_pullback rk (extensionProjection R S) (extensionProjection_over R S) U).symm
  have : Algebra.IsPushout k R M N :=
    CommRingCat.isPushout_iff_isPushout.mp (affineOpenRegularPushout R S U hU)
  change Algebra.IsPushout.equiv k R M N (r ⊗ₜ[k] (x : M)) = _
  exact Algebra.IsPushout.equiv_tmul k R M N r x

end LocalScalarExtension

section LocalCovarianceExtension

open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private abbrev ambientLocalModule {A : Type u} [CommRing A]
    {X T : SchemeOverRing A} (q : T ⟶ X) (U : X.left.Opens) :=
  localSections ((Scheme.Modules.pushforward q.left).obj (structureModule T.left)) U

private abbrev ambientLocalIso {A : Type u} [CommRing A]
    {X T : SchemeOverRing A} (q : T ⟶ X) (U : X.left.Opens) :
    ambientLocalModule q U ≅ regularModuleOpen T (q.left ⁻¹ᵁ U) :=
  pushforwardLocalSectionsIso (RingHom.id A) q.left (by simp) (structureModule T.left) U ≪≫
    (ModuleCat.restrictScalarsId A).app _

private theorem ambientLocalIso_hom_apply {A : Type u} [CommRing A] {X T : SchemeOverRing A}
    (q : T ⟶ X) (U : X.left.Opens) (x : ambientLocalModule q U) :
    (ambientLocalIso q U).hom x = x := rfl

private theorem ambientLocalIso_inv_apply {A : Type u} [CommRing A] {X T : SchemeOverRing A}
    (q : T ⟶ X) (U : X.left.Opens) (x : regularModuleOpen T (q.left ⁻¹ᵁ U)) :
    (ambientLocalIso q U).inv x = x := rfl

variable {k : Type u} [Field k] (R : TestAlgebra k) {X : SchemeOver k}

private abbrev extFunctor := extendToAlgebra (k := k) (K := R)
private abbrev extendedScheme := (extendScheme R).obj X
private abbrev baseProjection := extensionProjection R X
private abbrev extendedOpen (U : X.left.Opens) : (extendedScheme (X := X) R).left.Opens :=
  baseProjection (X := X) R ⁻¹ᵁ U

private theorem extensionProjection_preimage {T : SchemeOver k} (q : T ⟶ X) (U : X.left.Opens) :
    ((extendScheme R).map q).left ⁻¹ᵁ extendedOpen R U =
      extensionProjection R T ⁻¹ᵁ (q.left ⁻¹ᵁ U) :=
  congrArg (fun f : ((extendScheme R).obj T).left ⟶ X.left => f ⁻¹ᵁ U)
    (extensionProjection_natural R q)

private def affineRegularExtendIsoOn {T : SchemeOver k} (V : T.left.Opens) (hV : IsAffineOpen V)
    (W : ((extendScheme R).obj T).left.Opens) (hW : W = extensionProjection R T ⁻¹ᵁ V) :
    (extFunctor R).obj (regularModuleOpen T V) ≅ regularModuleOpen ((extendScheme R).obj T) W :=
  affineOpenRegularExtendIso R T V hV ≪≫
    eqToIso (congrArg (regularModuleOpen ((extendScheme R).obj T)) hW.symm)

private theorem affineRegularExtendIsoOn_tmul {T : SchemeOver k} (V : T.left.Opens)
    (hV : IsAffineOpen V) (W : ((extendScheme R).obj T).left.Opens)
    (hW : W = extensionProjection R T ⁻¹ᵁ V) (r : R) (x : regularModuleOpen T V) :
    (affineRegularExtendIsoOn R V hV W hW).hom (r ⊗ₜ[k,algebraMap k R] x) =
      groundRingHomOpen ((extendScheme R).obj T) W r *
        (extensionProjection R T).appLE V W hW.le x := by
  subst W
  rw [Scheme.Hom.appLE_eq_app]
  exact affineOpenRegularExtendIso_tmul R T V hV r x

private abbrev extensionOnOpen {T : SchemeOver k} (q : T ⟶ X) (U : X.left.Opens) :
    Γ(T.left, q.left ⁻¹ᵁ U) ⟶
      Γ(((extendScheme R).obj T).left, ((extendScheme R).map q).left ⁻¹ᵁ extendedOpen R U) :=
  pullbackOnOpen q.left (((extendScheme R).map q).left ≫ baseProjection (X := X) R)
    (extensionProjection R T) (extensionProjection_natural R q).symm U

private def localAmbientExtendIso {T : SchemeOver k} (q : T ⟶ X) (U : X.left.Opens)
    (hU : IsAffineOpen (q.left ⁻¹ᵁ U)) :
    (extFunctor R).obj (ambientLocalModule q U) ≅
      ambientLocalModule ((extendScheme R).map q) (extendedOpen R U) :=
  (extFunctor R).mapIso (ambientLocalIso q U) ≪≫
    affineRegularExtendIsoOn R (q.left ⁻¹ᵁ U) hU _ (extensionProjection_preimage R q U) ≪≫
    (ambientLocalIso ((extendScheme R).map q) (extendedOpen R U)).symm

private theorem localAmbientExtendIso_tmul {T : SchemeOver k} (q : T ⟶ X) (U : X.left.Opens)
    (hU : IsAffineOpen (q.left ⁻¹ᵁ U)) (r : R) (x : ambientLocalModule q U) :
    (localAmbientExtendIso R q U hU).hom (r ⊗ₜ[k,algebraMap k R] x) =
      groundRingHomOpen ((extendScheme R).obj T)
        (((extendScheme R).map q).left ⁻¹ᵁ extendedOpen R U) r * extensionOnOpen R q U x := by
  change (ambientLocalIso ((extendScheme R).map q) (extendedOpen R U)).inv
    ((affineRegularExtendIsoOn R (q.left ⁻¹ᵁ U) hU _ (extensionProjection_preimage R q U)).hom
      ((extFunctor R).map (ambientLocalIso q U).hom (r ⊗ₜ[k,algebraMap k R] x))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, ambientLocalIso_inv_apply, affineRegularExtendIsoOn_tmul]
  rfl

private theorem extensionOnOpen_comp {T S : SchemeOver k} (q : T ⟶ X) (r : S ⟶ X)
    (d : S ⟶ T) (w : d ≫ q = r) (U : X.left.Opens) :
    pullbackOnOpen q.left r.left d.left (congrArg Over.Hom.left w) U ≫ extensionOnOpen R r U =
      extensionOnOpen R q U ≫ pullbackOnOpen (((extendScheme R).map q).left ≫ baseProjection (X := X) R)
        (((extendScheme R).map r).left ≫ baseProjection (X := X) R)
        ((extendScheme R).map d).left
        (by rw [← Category.assoc, ← Over.comp_left, ← Functor.map_comp, w]) U := by
  dsimp only [extensionOnOpen]
  rw [pullbackOnOpen_comp, pullbackOnOpen_comp]
  apply pullbackOnOpen_congr
  exact (extensionProjection_natural R d).symm

private abbrev localCovariance {A : Type u} [CommRing A] {Y : SchemeOverRing A}
    (D : CovarianceData Y) (U : Y.left.Opens) := localSectionsMap D.covariance U

private theorem localCovariance_apply {A : Type u} [CommRing A] {Y : SchemeOverRing A}
    (D : CovarianceData Y) (U : Y.left.Opens)
    (x : ambientLocalModule D.projection U) :
    localCovariance D U x =
      pullbackOnOpen D.projection.left D.overlapProjection.left D.second.left (secondLeft_w D) U x -
      pullbackOnOpen D.projection.left D.overlapProjection.left D.first.left (firstLeft_w D) U x *
        D.overlap.left.presheaf.map (D.overlapProjection.left ⁻¹ᵁ U).leTop.op D.multiplier :=
  covarianceMap_app _ _ _ _ _ _ _ _ x

private theorem localAmbientExtendIso_comm (D : CovarianceData X) (U : X.left.Opens)
    (ht : IsAffineOpen (D.projection.left ⁻¹ᵁ U))
    (ho : IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ U)) :
    (extFunctor R).map (localCovariance D U) ≫
        (localAmbientExtendIso R D.overlapProjection U ho).hom =
      (localAmbientExtendIso R D.projection U ht).hom ≫
        localCovariance (D.extend R) (extendedOpen R U) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    localAmbientExtendIso_tmul, localAmbientExtendIso_tmul, map_one, one_mul, map_one, one_mul]
  rw [localCovariance_apply D]
  erw [localCovariance_apply (D.extend R)]
  rw [map_sub, map_mul]
  have h₂ (d : D.overlap ⟶ D.torsor) (hd : d ≫ D.projection = D.overlapProjection) :
      extensionOnOpen R D.overlapProjection U
          (pullbackOnOpen D.projection.left D.overlapProjection.left d.left
            (congrArg Over.Hom.left hd) U x) =
        pullbackOnOpen ((D.extend R).projection.left) ((D.extend R).overlapProjection.left)
          ((extendScheme R).map d).left
          (by change (((extendScheme R).map d) ≫ ((extendScheme R).map D.projection)).left = _
              rw [← Functor.map_comp, hd]
              rfl)
          (extendedOpen R U) (extensionOnOpen R D.projection U x) := by
    have hn := extensionOnOpen_comp R D.projection D.overlapProjection d hd U
    exact congrArg (fun f => f x) hn
  rw [h₂ D.second D.snd_w, h₂ D.first D.fst_w]
  have hmult := pullbackOnOpen_restrict_global D.overlapProjection.left
    (((extendScheme R).map D.overlapProjection).left ≫ baseProjection (X := X) R)
    (extensionProjection R D.overlap)
    (extensionProjection_natural R D.overlapProjection).symm U D.multiplier
  congr 2

private def localEvaluation {A : Type u} [CommRing A] (Y : SchemeOverRing A) (U : Y.left.Opens) :
    Y.left.Modules ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation.{u} Y.left.ringCatSheaf (op U) ⋙
    ModuleCat.restrictScalars (groundRingHomOpen Y U)

private instance {A : Type u} [CommRing A] (Y : SchemeOverRing A) (U : Y.left.Opens) :
    (localEvaluation Y U).Additive := ⟨by intros; apply ModuleCat.hom_ext; ext x : 1; rfl⟩

private instance {A : Type u} [CommRing A] (Y : SchemeOverRing A) (U : Y.left.Opens) :
    PreservesFiniteLimits (localEvaluation Y U) := by
  let ev := SheafOfModules.evaluation.{u} Y.left.ringCatSheaf (op U)
  let E := ModuleCat.restrictScalars.{u,u,u} (groundRingHomOpen Y U)
  exact comp_preservesFiniteLimits ev E

/-- The covariant sections over an open with affine inverse images in the
torsor and its overlap commute with scalar extension. The adjoint map is
pullback on the original covariant functions. -/
theorem covarianceLocalSections_baseChange
    (D : CovarianceData X) (U : X.left.Opens)
    (ht : IsAffineOpen (D.projection.left ⁻¹ᵁ U))
    (ho : IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ U))
    (α : D.sheaf ⟶ (Scheme.Modules.pushforward (baseProjection (X := X) R)).obj (D.extend R).sheaf)
    (hα : D.IsPullbackMap (D.extend R) (baseProjection (X := X) R) (extensionProjection R D.torsor)
      (extensionProjection_natural R D.projection).symm α) :
    ∃ e : (extFunctor R).obj (localSections D.sheaf U) ≅
        localSections (D.extend R).sheaf (extendedOpen R U),
      (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ e.hom =
        localSectionsMap α U ≫
          (pushforwardLocalSectionsIso (algebraMap k R) (baseProjection (X := X) R)
            (extensionProjection_over R X) (D.extend R).sheaf U).hom := by
  let U' := extendedOpen R U
  let Y := extendedScheme (X := X) R
  let D' := D.extend R
  let E := extFunctor R
  let ΓX := localEvaluation X U
  let ΓY := localEvaluation Y U'
  let a := PreservesKernel.iso ΓX D.covariance
  let b := PreservesKernel.iso E (localCovariance D U)
  let c := kernel.mapIso (E.map (localCovariance D U)) (localCovariance D' U')
    (localAmbientExtendIso R D.projection U ht) (localAmbientExtendIso R D.overlapProjection U ho)
    (localAmbientExtendIso_comm R D U ht ho)
  let d := PreservesKernel.iso ΓY D'.covariance
  let e := E.mapIso a ≪≫ b ≪≫ c ≪≫ d.symm
  refine ⟨e, ?_⟩
  have he : e.hom ≫ ΓY.map D'.inclusion =
      E.map (ΓX.map D.inclusion) ≫ (localAmbientExtendIso R D.projection U ht).hom := by
    have ha : a.hom ≫ kernel.ι (localCovariance D U) = ΓX.map D.inclusion := by
      change a.hom ≫ kernel.ι (ΓX.map D.covariance) = ΓX.map (kernel.ι D.covariance)
      rw [show a.hom = kernelComparison D.covariance ΓX from PreservesKernel.iso_hom _ _]
      exact kernelComparison_comp_ι _ _
    have hb : b.hom ≫ kernel.ι (E.map (localCovariance D U)) = E.map (kernel.ι (localCovariance D U)) := by
      simp only [b, PreservesKernel.iso_hom, kernelComparison_comp_ι]
    have hc : c.hom ≫ kernel.ι (localCovariance D' U') =
        kernel.ι (E.map (localCovariance D U)) ≫ (localAmbientExtendIso R D.projection U ht).hom :=
      kernel.lift_ι _ _ _
    have hd : d.inv ≫ ΓY.map D'.inclusion = kernel.ι (localCovariance D' U') :=
      PreservesKernel.iso_inv_ι _ _
    simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc, hd,
      hc, reassoc_of% hb, ← E.map_comp_assoc, ha]
  apply ModuleCat.hom_ext
  ext x : 1
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  apply ((ModuleCat.mono_iff_injective (ΓY.map D'.inclusion)).mp inferInstance)
  have he' := congrArg (fun m => m ((1 : R) ⊗ₜ[k,algebraMap k R] x)) he
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul] at he'
  have hunit := localAmbientExtendIso_tmul R D.projection U ht (1 : R) (ΓX.map D.inclusion x)
  rw [map_one, one_mul] at hunit
  change D'.inclusion.app U' (e.hom ((1 : R) ⊗ₜ[k,algebraMap k R] x)) =
    D'.inclusion.app U' (α.app U x)
  change D'.inclusion.app U' (e.hom ((1 : R) ⊗ₜ[k,algebraMap k R] x)) =
    (localAmbientExtendIso R D.projection U ht).hom ((1 : R) ⊗ₜ[k,algebraMap k R] (ΓX.map D.inclusion x))
    at he'
  exact he'.trans (hunit.trans (covariancePullback_app hα U x).symm)

end LocalCovarianceExtension

section CechGeometricScalarExtension

open CategoryTheory.Preadditive
open scoped Simplicial TensorProduct ChangeOfRings
open private orderedCochains coface differential tupleOpen_le
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] (R : TestAlgebra k) {X : SchemeOver k}
  (D : CovarianceData X)

private abbrev ExtendedCoefficientMap := D.sheaf ⟶
  (Scheme.Modules.pushforward (baseProjection (X := X) R)).obj (D.extend R).sheaf

variable (α : ExtendedCoefficientMap R D)
  (hα : D.IsPullbackMap (D.extend R) (baseProjection (X := X) R) (extensionProjection R D.torsor)
    (extensionProjection_natural R D.projection).symm α)

private abbrev localScalarIso (U : X.left.Opens)
    (ht : IsAffineOpen (D.projection.left ⁻¹ᵁ U))
    (ho : IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ U)) :=
  (covarianceLocalSections_baseChange R D U ht ho α hα).choose

private theorem localScalarIso_one_tmul (U : X.left.Opens)
    (ht : IsAffineOpen (D.projection.left ⁻¹ᵁ U))
    (ho : IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ U)) (x : localSections D.sheaf U) :
    (localScalarIso R D α hα U ht ho).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x) = α.app U x := by
  have h := congrArg (fun f => f x) (covarianceLocalSections_baseChange R D U ht ho α hα).choose_spec
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at h
  exact h

private theorem localScalarIso_natural {U V : X.left.Opens} (i : V ⟶ U)
    (ht : IsAffineOpen (D.projection.left ⁻¹ᵁ U))
    (ho : IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ U))
    (ht' : IsAffineOpen (D.projection.left ⁻¹ᵁ V))
    (ho' : IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ V)) :
    (extFunctor R).map ((coefficientPresheaf D.sheaf).map i.op) ≫
        (localScalarIso R D α hα V ht' ho').hom =
      (localScalarIso R D α hα U ht ho).hom ≫
        (coefficientPresheaf (D.extend R).sheaf).map
          (((Opens.map (baseProjection (X := X) R).base).map i).op) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  erw [localScalarIso_one_tmul, localScalarIso_one_tmul]
  exact PresheafOfModules.naturality_apply α.val i.op x

variable {I : Type u} [Preorder I] (U : I → X.left.Opens)

private abbrev extendedCover (i : I) := extendedOpen R (U i)

private abbrev coverSectionsTransport {n : ℕ} (e : Fin (n + 1) ↪o I) :
    localSections (D.extend R).sheaf (extendedOpen R (tupleOpen U e)) ≅
      localSections (D.extend R).sheaf (tupleOpen (extendedCover R U) e) :=
  (coefficientPresheaf (D.extend R).sheaf).mapIso
    (eqToIso (congrArg op (preimage_tupleOpen (extensionProjection R X) U e)))

private theorem coverSectionsTransport_natural {n m : ℕ}
    (e : Fin (m + 1) ↪o I) (v : Fin (n + 1) ↪o Fin (m + 1)) :
    (coefficientPresheaf (D.extend R).sheaf).map
        (((Opens.map (baseProjection (X := X) R).base).map (homOfLE (tupleOpen_le U e v))).op) ≫
        (coverSectionsTransport R D U e).hom =
      (coverSectionsTransport R D U (v.trans e)).hom ≫
        (coefficientPresheaf (D.extend R).sheaf).map
          (homOfLE (tupleOpen_le (extendedCover R U) e v)).op := by
  change _ ≫ (coefficientPresheaf (D.extend R).sheaf).map _ =
    (coefficientPresheaf (D.extend R).sheaf).map _ ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private def productModuleIso {A : Type u} [CommRing A] {S : Type u}
    {F G : S → ModuleCat.{u} A} (p : ∀ s, F s ≅ G s) :
    ModuleCat.of A (∀ s, F s) ≅ ModuleCat.of A (∀ s, G s) where
  hom := ModuleCat.ofHom <| LinearMap.pi fun s => (p s).hom.hom.comp (LinearMap.proj s)
  inv := ModuleCat.ofHom <| LinearMap.pi fun s => (p s).inv.hom.comp (LinearMap.proj s)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    ext x : 1
    funext i
    change (p i).inv ((p i).hom (x i)) = x i
    exact congrArg (fun f => f (x i)) (p i).hom_inv_id
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x : 1
    funext i
    change (p i).hom ((p i).inv (x i)) = x i
    exact congrArg (fun f => f (x i)) (p i).inv_hom_id

variable
  (ht : ∀ {n : ℕ} (e : Fin (n + 1) ↪o I), IsAffineOpen (D.projection.left ⁻¹ᵁ tupleOpen U e))
  (ho : ∀ {n : ℕ} (e : Fin (n + 1) ↪o I), IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ tupleOpen U e))

private abbrev tupleScalarIso {n : ℕ} (e : Fin (n + 1) ↪o I) :=
  localScalarIso R D α hα (tupleOpen U e) (ht e) (ho e) ≪≫ coverSectionsTransport R D U e

private theorem tupleScalarIso_natural {n m : ℕ}
    (e : Fin (m + 1) ↪o I) (v : Fin (n + 1) ↪o Fin (m + 1)) :
    (extFunctor R).map ((coefficientPresheaf D.sheaf).map (homOfLE (tupleOpen_le U e v)).op) ≫
        (tupleScalarIso R D α hα U ht ho e).hom =
      (tupleScalarIso R D α hα U ht ho (v.trans e)).hom ≫
        (coefficientPresheaf (D.extend R).sheaf).map
          (homOfLE (tupleOpen_le (extendedCover R U) e v)).op := by
  simp only [tupleScalarIso, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, localScalarIso_natural, Category.assoc,
    coverSectionsTransport_natural]

private def extendedOrderedCochainsIso :
    orderedCochains U (coefficientPresheaf D.sheaf ⋙ extFunctor R) ≅
      orderedCochains (extendedCover R U) (coefficientPresheaf (D.extend R).sheaf) :=
  NatIso.ofComponents (fun n => productModuleIso
    (fun (e : Fin (n.len + 1) ↪o I) => tupleScalarIso R D α hα U ht ho e)) (by
    intro n m f
    apply ModuleCat.hom_ext
    ext x : 1
    funext e
    let v := SemiSimplexCategory.homEquiv f
    have hn := tupleScalarIso_natural R D α hα U ht ho e v
    exact congrArg (fun g => g (x (v.trans e))) hn)

variable [Finite I]

/-- Flat extension compares the ordered Čech cochains on a flag cover by
applying the canonical extension of sections on each tuple intersection. -/
def covarianceCechExtendIso :
    ((extFunctor R).mapHomologicalComplex (.up ℕ)).obj
        (cechComplex U (coefficientPresheaf D.sheaf)) ≅
      cechComplex (extendedCover R U) (coefficientPresheaf (D.extend R).sheaf) := by
  refine cechExtendScalarsIso U (coefficientPresheaf D.sheaf) ≪≫ ?_
  let e := extendedOrderedCochainsIso R D α hα U ht ho
  refine HomologicalComplex.Hom.isoOfComponents (fun n => e.app ⦋n⦌ₛ) ?_
  intro n m hnm
  obtain rfl : n + 1 = m := hnm
  simp only [cechComplex, CochainComplex.of_d]
  change e.hom.app ⦋n⦌ₛ ≫ differential (extendedCover R U) (coefficientPresheaf (D.extend R).sheaf) n =
    differential U (coefficientPresheaf D.sheaf ⋙ extFunctor R) n ≫ e.hom.app ⦋n + 1⦌ₛ
  simp only [differential, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  exact Finset.sum_congr rfl fun (i : Fin (n + 2)) _ =>
    congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (e.hom.naturality (coface i)).symm

private theorem covarianceCechExtendIso_one_tmul (n : ℕ) (e : Fin (n + 1) ↪o I)
    (x : (cechComplex U (coefficientPresheaf D.sheaf)).X n) :
    (covarianceCechExtendIso R D α hα U ht ho).hom.f n
        ((1 : R) ⊗ₜ[k,algebraMap k R] x) e =
      (coverSectionsTransport R D U e).hom (α.app (tupleOpen U e) (x e)) := by
  let M (s : Fin (n + 1) ↪o I) := localSections D.sheaf (tupleOpen U s)
  have h₁ := congrArg (fun f => f ((1 : R) ⊗ₜ[k,algebraMap k R] x))
    (extendProductIso_hom_proj (R := R) M e)
  change ((extendProductIso (R := R) M).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x)) e =
    (extFunctor R).map (ModuleCat.ofHom (LinearMap.proj e)) ((1 : R) ⊗ₜ[k,algebraMap k R] x) at h₁
  rw [ModuleCat.ExtendScalars.map_tmul] at h₁
  change (coverSectionsTransport R D U e).hom
    ((localScalarIso R D α hα (tupleOpen U e) (ht e) (ho e)).hom
      (((extendProductIso (R := R) M).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x)) e)) = _
  rw [h₁, localScalarIso_one_tmul]
  rfl

end CechGeometricScalarExtension

section FlagCechBaseChange

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}

private theorem flagStructure_separated (Q : Presentation P.negative) : IsSeparated Q.scheme.hom := by
  obtain ⟨V, _, _, _, j, hj⟩ := Q.quasiProjective
  let : IsImmersion j.left := hj
  let : IsSeparated j.left := inferInstance
  let B := ProjectiveSpaces.projectiveSpace k V
  have : IsSeparated B.hom := by
    let I := ULift.{u} (Fin (Module.finrank k V))
    change IsSeparated (Proj.toSpecZero (ProjectiveSpaces.grading k I) ≫
      Spec.map (CommRingCat.ofHom (ProjectiveSpaces.constants k I)))
    infer_instance
  rw [← Over.w j]
  exact inferInstanceAs (IsSeparated (j.left ≫ B.hom))

private theorem flagTorsor_affine (Q : Presentation P.negative) :
    IsAffineHom Q.projection.left := by
  let : IsAffine G.val.X.left := G.property.1
  let : IsSeparated Q.scheme.hom := flagStructure_separated Q
  have : IsAffineHom (Q.projection.left ≫ Q.scheme.hom) := by
    rw [Over.w Q.projection]
    infer_instance
  exact IsAffineHom.of_comp Q.projection.left Q.scheme.hom

private theorem flagOverlap_affine (Q : Presentation P.negative) :
    IsAffineHom ((prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) ≫ Q.projection).left := by
  let q := (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) ≫ Q.projection
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine P.negative.group.X.left :=
    (Unipotent.closedSubgroupAlgebraicGroup (G := G) P.negative).property.1
  let : IsAffine (G.val.X ⨯ P.negative.group.X).left :=
    IsAffine.of_isPullback (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) prod.snd)
      (prodIsProd G.val.X P.negative.group.X))
  let : IsSeparated Q.scheme.hom := flagStructure_separated Q
  have : IsAffineHom (q.left ≫ Q.scheme.hom) := by
    rw [Over.w q]
    infer_instance
  exact IsAffineHom.of_comp q.left Q.scheme.hom

/-- The ordered cochain comparison for the flag and its extended quotient
torsor over every commutative test algebra. -/
theorem flagCechBaseChange : FlagCechBaseChange.{u} := by
  intro k _ G P Q p χ h R I _ _ U hU
  let D := flagLineData Q p χ h
  let : IsAffineHom D.projection.left := flagTorsor_affine Q
  let : IsAffineHom D.overlapProjection.left := flagOverlap_affine Q
  obtain ⟨α, hα⟩ := scalarExtension_coefficientMap R D
  have ht {n : ℕ} (e : Fin (n + 1) ↪o I) : IsAffineOpen (D.projection.left ⁻¹ᵁ tupleOpen U e) :=
    (hU e).preimage D.projection.left
  have ho {n : ℕ} (e : Fin (n + 1) ↪o I) : IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ tupleOpen U e) :=
    (hU e).preimage D.overlapProjection.left
  refine ⟨α, covarianceCechExtendIso R D α hα U ht ho, hα, ?_⟩
  exact covarianceCechExtendIso_one_tmul R D α hα U ht ho

end FlagCechBaseChange

section AffineScalarExtension

open private groundRingHom_over from Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] (R : TestAlgebra k) (X : SchemeOver k)

private abbrev regularModule {A : Type u} [CommRing A] (S : SchemeOverRing A) :
    ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (groundRingHom S)).obj (ModuleCat.of Γ(S.left, ⊤) Γ(S.left, ⊤))

private theorem affineRegularPushout [IsAffine X.left] :
    IsPushout (CommRingCat.ofHom (algebraMap k R)) (CommRingCat.ofHom (groundRingHom X))
      (CommRingCat.ofHom (groundRingHom ((extendScheme R).obj X)))
      (extensionProjection R X).appTop := by
  let h := (isPushout_appTop_of_isPullback
    (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k R))))).flip
  refine h.of_iso' (Scheme.ΓSpecIso (CommRingCat.of k)).symm
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Scheme.ΓSpecIso_inv_naturality _).symm
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · simp

/-- For an affine scheme over the ground field, scalar extension of global
regular functions is the coordinate ring of the scheme fiber product. -/
def affineRegularExtendIso [IsAffine X.left] :
    (extendToAlgebra (k := k) (K := R)).obj (regularModule X) ≅
      regularModule ((extendScheme R).obj X) := by
  let Y := (extendScheme R).obj X
  let A := Γ(X.left, ⊤)
  let B := Γ(Y.left, ⊤)
  let rk := algebraMap k R
  letI : Algebra k R := rk.toAlgebra
  letI : Algebra k A := (groundRingHom X).toAlgebra
  letI : Algebra R B := (groundRingHom Y).toAlgebra
  letI : Algebra A B := (extensionProjection R X).appTop.hom.toAlgebra
  letI : Algebra k B := ((groundRingHom Y).comp (algebraMap k R)).toAlgebra
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq'
    (groundRingHom_over (algebraMap k R) (extensionProjection R X)
      (extensionProjection_over R X)).symm
  haveI : Algebra.IsPushout k R A B :=
    CommRingCat.isPushout_iff_isPushout.mp (affineRegularPushout R X)
  exact (Algebra.IsPushout.equiv k R A B).toLinearEquiv.toModuleIso

private theorem affineRegularExtendIso_hom_tmul [IsAffine X.left]
    (r : R) (x : regularModule X) :
    (affineRegularExtendIso R X).hom (r ⊗ₜ[k,algebraMap k R] x) =
      groundRingHom ((extendScheme R).obj X) r * (extensionProjection R X).appTop x := by
  let Y := (extendScheme R).obj X
  let A := Γ(X.left, ⊤)
  let B := Γ(Y.left, ⊤)
  let rk := algebraMap k R
  let : Algebra k R := rk.toAlgebra
  let : Algebra k A := (groundRingHom X).toAlgebra
  let : Algebra R B := (groundRingHom Y).toAlgebra
  let : Algebra A B := (extensionProjection R X).appTop.hom.toAlgebra
  let : Algebra k B := ((groundRingHom Y).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq'
    (groundRingHom_over (algebraMap k R) (extensionProjection R X)
      (extensionProjection_over R X)).symm
  have : Algebra.IsPushout k R A B :=
    CommRingCat.isPushout_iff_isPushout.mp (affineRegularPushout R X)
  change Algebra.IsPushout.equiv k R A B (r ⊗ₜ[k] (x : A)) = _
  exact Algebra.IsPushout.equiv_tmul k R A B r x

end AffineScalarExtension

section CovarianceGlobalSections

open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem pullbackOnOpen_top {T S Z : Scheme.{u}}
    (q : T ⟶ Z) (r : S ⟶ Z) (b : S ⟶ T) (w : b ≫ q = r) :
    pullbackOnOpen q r b w ⊤ = b.appTop :=
  b.appLE_eq_app

private abbrev structuralGlobalIso {A : Type u} [CommRing A]
    {X Y : SchemeOverRing A} (f : Y ⟶ X) :
    (sectionsFunctor X).obj ((Scheme.Modules.pushforward f.left).obj (structureModule Y.left)) ≅
      regularModule Y :=
  (pushforwardSectionsIso (RingHom.id A) f.left (by simp)).app (structureModule Y.left) ≪≫
    ModuleCat.restrictScalarsId'App (RingHom.id A) rfl _

private theorem structuralGlobalIso_inv_apply {A : Type u} [CommRing A]
    {X Y : SchemeOverRing A} (f : Y ⟶ X) (x : regularModule Y) :
    (structuralGlobalIso f).inv x = x := rfl

private abbrev globalCovariance {A : Type u} [CommRing A] {X : SchemeOverRing A}
    (D : CovarianceData X) := (sectionsFunctor X).map D.covariance

private theorem globalCovariance_apply {A : Type u} [CommRing A] {X : SchemeOverRing A}
    (D : CovarianceData X)
    (x : (sectionsFunctor X).obj
      ((Scheme.Modules.pushforward D.projection.left).obj (structureModule D.torsor.left))) :
    globalCovariance D x = D.second.left.appTop x - D.first.left.appTop x * D.multiplier := by
  change D.covariance.app ⊤ x = _
  unfold CovarianceData.covariance
  rw [covarianceMap_app]
  have h := pullbackOnOpen_top D.projection.left D.overlapProjection.left D.second.left
    (secondLeft_w D)
  have h' := pullbackOnOpen_top D.projection.left D.overlapProjection.left D.first.left
    (firstLeft_w D)
  have ht : D.overlap.left.presheaf.map
      (D.overlapProjection.left ⁻¹ᵁ (⊤ : X.left.Opens)).leTop.op D.multiplier = D.multiplier := by
    have htop : (TopologicalSpace.Opens.leTop (⊤ : D.overlap.left.Opens)).op = 𝟙 _ :=
      Subsingleton.elim _ _
    change D.overlap.left.presheaf.map (TopologicalSpace.Opens.leTop (⊤ : D.overlap.left.Opens)).op
      D.multiplier = D.multiplier
    rw [htop]
    exact congrArg (fun f : Γ(D.overlap.left, ⊤) ⟶ Γ(D.overlap.left, ⊤) => f D.multiplier)
      (D.overlap.left.presheaf.map_id (op ⊤))
  change pullbackOnOpen _ _ _ (secondLeft_w D) ⊤ x -
      (pullbackOnOpen _ _ _ (firstLeft_w D) ⊤ x) *
        (D.overlap.left.presheaf.map (D.overlapProjection.left ⁻¹ᵁ (⊤ : X.left.Opens)).leTop.op
          D.multiplier) = _
  erw [h, h', ht]
  rfl

variable {k : Type u} [Field k] {X : SchemeOver k} (R : TestAlgebra k) (D : CovarianceData X)

private abbrev ambientExtendIso {T : SchemeOver k} (q : T ⟶ X) [IsAffine T.left] :=
  (extendToAlgebra (k := k) (K := R)).mapIso (structuralGlobalIso q) ≪≫
    affineRegularExtendIso R T ≪≫ (structuralGlobalIso ((extendScheme R).map q)).symm

private theorem ambientExtendIso_tmul {T : SchemeOver k} (q : T ⟶ X) [IsAffine T.left]
    (r : R) (x : (sectionsFunctor X).obj
      ((Scheme.Modules.pushforward q.left).obj (structureModule T.left))) :
    (ambientExtendIso R q).hom (r ⊗ₜ[k,algebraMap k R] x) =
      groundRingHom ((extendScheme R).obj T) r * (extensionProjection R T).appTop x := by
  change (structuralGlobalIso ((extendScheme R).map q)).inv ((affineRegularExtendIso R T).hom
    ((extendToAlgebra (k := k) (K := R)).map (structuralGlobalIso q).hom
      (r ⊗ₜ[k,algebraMap k R] x))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, structuralGlobalIso_inv_apply, affineRegularExtendIso_hom_tmul]
  rfl

private theorem ambientExtendIso_comm [IsAffine D.torsor.left] [IsAffine D.overlap.left] :
    (extendToAlgebra (k := k) (K := R)).map (globalCovariance D) ≫
        (ambientExtendIso R D.overlapProjection).hom =
      (ambientExtendIso R D.projection).hom ≫ globalCovariance (D.extend R) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    ambientExtendIso_tmul, ambientExtendIso_tmul, map_one, one_mul, map_one, one_mul,
    globalCovariance_apply]
  erw [globalCovariance_apply (D.extend R)]
  have h (b : D.overlap ⟶ D.torsor) :
      ((extendScheme R).map b).left.appTop ((extensionProjection R D.torsor).appTop x) =
        (extensionProjection R D.overlap).appTop (b.left.appTop x) := by
    have e := congrArg Scheme.Hom.appTop (extensionProjection_natural R b)
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) x
  change (extensionProjection R D.overlap).appTop
      (D.second.left.appTop x - D.first.left.appTop x * D.multiplier) =
    ((extendScheme R).map D.second).left.appTop ((extensionProjection R D.torsor).appTop x) -
      ((extendScheme R).map D.first).left.appTop ((extensionProjection R D.torsor).appTop x) *
        (extensionProjection R D.overlap).appTop D.multiplier
  rw [h D.second, h D.first]
  exact (map_sub _ _ _).trans (congrArg (_ - ·) (map_mul _ _ _))

/-- For a flat scalar extension from a field, the covariance kernel on global
sections commutes with extension if the torsor and its overlap are affine.
Its map on sections is the pullback of the original regular functions. -/
theorem covarianceGlobalSections_baseChange [IsAffine D.torsor.left] [IsAffine D.overlap.left]
    (α : D.sheaf ⟶ (Scheme.Modules.pushforward (extensionProjection R X)).obj (D.extend R).sheaf)
    (hα : D.IsPullbackMap (D.extend R) (extensionProjection R X) (extensionProjection R D.torsor)
      (extensionProjection_natural R D.projection).symm α) :
    ∃ e : (extendToAlgebra (k := k) (K := R)).obj ((sectionsFunctor X).obj D.sheaf) ≅
        (sectionsFunctor ((extendScheme R).obj X)).obj (D.extend R).sheaf,
      (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ e.hom =
        (sectionsFunctor X).map α ≫
          (pushforwardSectionsIso (algebraMap k R) (extensionProjection R X)
            (extensionProjection_over R X)).hom.app (D.extend R).sheaf := by
  let Y := (extendScheme R).obj X
  let D' := D.extend R
  let E := extendToAlgebra (k := k) (K := R)
  let ΓX := sectionsFunctor X
  let ΓY := sectionsFunctor Y
  let a := PreservesKernel.iso ΓX D.covariance
  let b := PreservesKernel.iso E (globalCovariance D)
  let c := kernel.mapIso (E.map (globalCovariance D)) (globalCovariance D')
    (ambientExtendIso R D.projection) (ambientExtendIso R D.overlapProjection)
    (ambientExtendIso_comm R D)
  let d := PreservesKernel.iso ΓY D'.covariance
  let e := E.mapIso a ≪≫ b ≪≫ c ≪≫ d.symm
  refine ⟨e, ?_⟩
  have he : e.hom ≫ ΓY.map D'.inclusion =
      E.map (ΓX.map D.inclusion) ≫ (ambientExtendIso R D.projection).hom := by
    have ha : a.hom ≫ kernel.ι (globalCovariance D) = ΓX.map D.inclusion := by
      change a.hom ≫ kernel.ι (ΓX.map D.covariance) = ΓX.map (kernel.ι D.covariance)
      rw [show a.hom = kernelComparison D.covariance ΓX from PreservesKernel.iso_hom _ _]
      exact kernelComparison_comp_ι _ _
    have hb : b.hom ≫ kernel.ι (E.map (globalCovariance D)) = E.map (kernel.ι (globalCovariance D)) := by
      simp only [b, PreservesKernel.iso_hom, kernelComparison_comp_ι]
    have hc : c.hom ≫ kernel.ι (globalCovariance D') =
        kernel.ι (E.map (globalCovariance D)) ≫ (ambientExtendIso R D.projection).hom :=
      kernel.lift_ι _ _ _
    have hd : d.inv ≫ ΓY.map D'.inclusion = kernel.ι (globalCovariance D') :=
      PreservesKernel.iso_inv_ι _ _
    simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc, hd,
      hc, reassoc_of% hb, ← E.map_comp_assoc, ha]
  apply ModuleCat.hom_ext
  ext x : 1
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  apply ((ModuleCat.mono_iff_injective (ΓY.map D'.inclusion)).mp inferInstance)
  have he' := congrArg (fun m => m ((1 : R) ⊗ₜ[k,algebraMap k R] x)) he
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul] at he'
  have hunit := ambientExtendIso_tmul R D.projection (1 : R) (ΓX.map D.inclusion x)
  rw [map_one, one_mul] at hunit
  change D'.inclusion.app ⊤ (e.hom ((1 : R) ⊗ₜ[k,algebraMap k R] x)) =
    D'.inclusion.app ⊤ (α.app ⊤ x)
  change D'.inclusion.app ⊤ (e.hom ((1 : R) ⊗ₜ[k,algebraMap k R] x)) =
    (ambientExtendIso R D.projection).hom ((1 : R) ⊗ₜ[k,algebraMap k R] (ΓX.map D.inclusion x))
    at he'
  refine he'.trans (hunit.trans ?_)
  have h := covariancePullback_app hα ⊤ x
  rw [pullbackOnOpen_top] at h
  exact h.symm

/-- Scalar extension of degree-zero flag cohomology is induced by the
projection on the original torsor. The construction works over every
commutative test algebra. -/
theorem flagCohomologyZero_baseChange (R : TestAlgebra k)
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q) :
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
          (D.extend R).sheaf := by
  let D := flagLineData Q p χ h
  let Y := (extendScheme R).obj Q.scheme
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine P.negative.group.X.left :=
    (Unipotent.closedSubgroupAlgebraicGroup (G := G) P.negative).property.1
  let : IsAffine D.torsor.left := G.property.1
  let : IsAffine D.overlap.left := by
    change IsAffine (G.val.X ⨯ P.negative.group.X).left
    exact IsAffine.of_isPullback (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) prod.snd)
      (prodIsProd G.val.X P.negative.group.X))
  obtain ⟨α, hα⟩ := scalarExtension_coefficientMap R D
  obtain ⟨e, he⟩ := covarianceGlobalSections_baseChange R D α hα
  let b := (cohomologyZero Q.scheme).app D.sheaf
  let b' := (cohomologyZero Y).app (D.extend R).sheaf
  refine ⟨α, (extendToAlgebra (k := k) (K := R)).mapIso b ≪≫ e ≪≫ b'.symm, hα, ?_⟩
  change (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _
        (((extendToAlgebra (k := k) (K := R)).map b.hom ≫ e.hom ≫ b'.inv) ≫ b'.hom) =
    b.hom ≫ (sectionsFunctor Q.scheme).map α ≫
      (pushforwardSectionsIso (algebraMap k R) (extensionProjection R Q.scheme)
        (extensionProjection_over R Q.scheme)).hom.app (D.extend R).sheaf
  rw [Category.assoc, Category.assoc, b'.inv_hom_id, Category.comp_id,
    Adjunction.homEquiv_naturality_left, he]

end CovarianceGlobalSections

section CohomologyScalars

open private localScalars_comp from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [CommRing A] (X : SchemeOverRing A)

private def scalarEnd {S : Type u} [CommRing S] (M : ModuleCat.{u} S) (s : S) : M ⟶ M :=
  ModuleCat.ofHom
    { toFun := fun x => s • x
      map_add' := smul_add s
      map_smul' := fun r x => smul_comm s r x }

/-- Multiplication by a ground-ring scalar on a sheaf of modules. -/
def sheafScalarMap (r : A) (F : X.left.Modules) : F ⟶ F where
  val :=
    { app := fun U => scalarEnd (S := Γ(X.left, U.unop)) (F.val.obj U)
        (groundRingHomOpen X U.unop r)
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        ext x : 1
        let m : F.val.obj V := F.val.map i x
        change groundRingHomOpen X V.unop r • m =
          F.val.map i (groundRingHomOpen X U.unop r • x)
        rw [F.val.map_smul]
        have he := congrArg (fun φ : A →+* Γ(X.left, V.unop) => φ r)
          (localScalars_comp (X := X) i.unop)
        exact congrArg (· • m) he }

@[simp]
theorem sheafScalarMap_app (r : A) (F : X.left.Modules) (U : X.left.Opens) (x : Γ(F, U)) :
    (sheafScalarMap X r F).app U x = groundRingHomOpen X U r • x := rfl

private theorem sheafScalarMap_natural (r : A) {F F' : X.left.Modules} (g : F ⟶ F') :
    g ≫ sheafScalarMap X r F' = sheafScalarMap X r F ≫ g := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [sheafScalarMap_app, sheafScalarMap_app]
  exact (g.app_smul _ _).symm

private theorem sectionsFunctor_map_scalar (r : A) (F : X.left.Modules) :
    (sectionsFunctor X).map (sheafScalarMap X r F) = r • 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x : 1
  let y : Γ(F, ⊤) := x
  change (sheafScalarMap X r F).app ⊤ y = groundRingHom X r • y
  rw [sheafScalarMap_app, groundRingHomOpen_top]

/-- Multiplication by a ground-ring scalar on the coefficients induces the
same scalar endomorphism on every cohomology group. -/
theorem cohomology_map_scalar (r : A) (F : X.left.Modules) (n : ℕ) :
    (cohomology X n).map (sheafScalarMap X r F) = r • 𝟙 _ := by
  let I := injectiveResolution F
  let s : I.cocomplex ⟶ I.cocomplex :=
    HomologicalComplex.Hom.mk
      (fun m => sheafScalarMap X r (I.cocomplex.X m))
      (fun i j _ => (sheafScalarMap_natural X r (I.cocomplex.d i j)).symm)
  have hs : I.ι.f 0 ≫ s.f 0 = sheafScalarMap X r F ≫ I.ι.f 0 := by
    have h := sheafScalarMap_natural X r (I.ι.f 0)
    simpa only [s, CochainComplex.single₀_obj_zero] using h
  let H := (sectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)
  let K := H.obj I.cocomplex
  let t := H.map s
  have ht : t.f n = r • 𝟙 _ := sectionsFunctor_map_scalar X r (I.cocomplex.X n)
  have hcyc : HomologicalComplex.cyclesMap t n = r • 𝟙 _ := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [HomologicalComplex.cyclesMap_i, ht, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]
  have hh : HomologicalComplex.homologyMap t n = r • 𝟙 _ := by
    apply (cancel_epi (K.homologyπ n)).mp
    rw [HomologicalComplex.homologyπ_naturality, hcyc, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]
  let e : (cohomology X n).obj F ≅ K.homology n := I.isoRightDerivedObj (sectionsFunctor X) n
  have he : (cohomology X n).map (sheafScalarMap X r F) ≫ e.hom =
      e.hom ≫ HomologicalComplex.homologyMap t n :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality _ I I s hs _ n
  apply (cancel_mono e.hom).mp
  rw [he, hh, Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

end CohomologyScalars

section ExactPushforward

open private restrictCohomologyIso from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def mapInjectiveResolution {C D : Type u} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (P : C ⥤ D) [P.Additive] [P.PreservesHomology]
    [P.PreservesInjectiveObjects] {F : C} (J : InjectiveResolution F) :
    InjectiveResolution (P.obj F) where
  cocomplex := (P.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  injective n := P.injective_obj_of_injective (J.injective n)
  «ι» := (HomologicalComplex.singleMapHomologicalComplex P (.up ℕ) 0).inv.app F ≫
    (P.mapHomologicalComplex (.up ℕ)).map J.ι

private theorem mapInjectiveResolution_ι_zero {C D : Type u} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (P : C ⥤ D) [P.Additive] [P.PreservesHomology]
    [P.PreservesInjectiveObjects] {F : C} (J : InjectiveResolution F) :
    (mapInjectiveResolution P J).ι.f 0 = P.map (J.ι.f 0) := by
  change ((HomologicalComplex.singleMapHomologicalComplex P (.up ℕ) 0).inv.app F).f 0 ≫
    P.map (J.ι.f 0) = _
  simp [HomologicalComplex.singleMapHomologicalComplex]

variable {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}

private def pushforwardComplexSectionsIso (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (J : CochainComplex Y.left.Modules ℕ) :
    ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj J) ≅
      ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (.up ℕ)).obj
        (((sectionsFunctor Y).mapHomologicalComplex (.up ℕ)).obj J) :=
  (Functor.mapHomologicalComplexCompIso (pushforwardSectionsIso φ f w) (.up ℕ)).app J

private theorem complexSections_natural (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {J K : CochainComplex Y.left.Modules ℕ} (m : J ⟶ K) :
    let P := (Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)
    let CX := (sectionsFunctor X).mapHomologicalComplex (.up ℕ)
    let CY := (sectionsFunctor Y).mapHomologicalComplex (.up ℕ)
    let R := (ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (.up ℕ)
    CX.map (P.map m) ≫ (pushforwardComplexSectionsIso φ f w K).hom =
      (pushforwardComplexSectionsIso φ f w J).hom ≫ R.map (CY.map m) := by
  intro P CX CY R
  ext i : 1
  exact (pushforwardSectionsIso φ f w).hom.naturality (m.f i)

private theorem restrictCohomologyIso_natural (φ : A →+* B)
    {J K : CochainComplex (ModuleCat.{u} B) ℕ} (l : J ⟶ K) (n : ℕ) :
    HomologicalComplex.homologyMap (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).map l) n ≫
        (restrictCohomologyIso φ K n).inv =
      (restrictCohomologyIso φ J n).inv ≫
        (ModuleCat.restrictScalars.{u} φ).map (HomologicalComplex.homologyMap l n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map l) (ModuleCat.restrictScalars.{u} φ)

variable (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    [(Scheme.Modules.pushforward f).PreservesHomology]
    [(Scheme.Modules.pushforward f).PreservesInjectiveObjects]

/-- Cohomology of the pushforward computed by a resolution preserved by an
exact pushforward functor. -/
private def exactPushforwardCohomologyIso {F' : Y.left.Modules}
    (J : InjectiveResolution F') (n : ℕ) :
    (cohomology X n).obj ((Scheme.Modules.pushforward f).obj F') ≅
      (ModuleCat.restrictScalars.{u} φ).obj ((cohomology Y n).obj F') :=
  let CY := (sectionsFunctor Y).mapHomologicalComplex (.up ℕ)
  let J' := mapInjectiveResolution (Scheme.Modules.pushforward f) J
  J'.isoRightDerivedObj (sectionsFunctor X) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (pushforwardComplexSectionsIso φ f w J.cocomplex) ≪≫
    (restrictCohomologyIso φ (CY.obj J.cocomplex) n).symm ≪≫
    (ModuleCat.restrictScalars.{u} φ).mapIso (J.isoRightDerivedObj (sectionsFunctor Y) n).symm

private theorem exactPushforwardCohomologyIso_independent {F' : Y.left.Modules}
    (J K : InjectiveResolution F') (n : ℕ) :
    (exactPushforwardCohomologyIso φ f w J n).hom =
      (exactPushforwardCohomologyIso φ f w K n).hom := by
  let P := Scheme.Modules.pushforward f
  let CY := (sectionsFunctor Y).mapHomologicalComplex (.up ℕ)
  let CX := (sectionsFunctor X).mapHomologicalComplex (.up ℕ)
  let R := ModuleCat.restrictScalars.{u} φ
  let J' := mapInjectiveResolution P J
  let K' := mapInjectiveResolution P K
  let d := InjectiveResolution.desc (𝟙 F') K J
  have hd := InjectiveResolution.desc_commutes_zero (𝟙 F') K J
  let d' := (P.mapHomologicalComplex (.up ℕ)).map d
  have hd' : J'.ι.f 0 ≫ d'.f 0 = 𝟙 (P.obj F') ≫ K'.ι.f 0 := by
    change (mapInjectiveResolution P J).ι.f 0 ≫ P.map (d.f 0) =
      𝟙 (P.obj F') ≫ (mapInjectiveResolution P K).ι.f 0
    simp only [mapInjectiveResolution_ι_zero, ← P.map_comp, d, hd, Category.id_comp]
  have hX := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 (P.obj F'))
    J' K' d' hd' (sectionsFunctor X) n
  have hY := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 F') J K d hd
    (sectionsFunctor Y) n
  have idX : ((sectionsFunctor X).rightDerived n).map (𝟙 (P.obj F')) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have idY : ((sectionsFunctor Y).rightDerived n).map (𝟙 F') = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [idX, Category.id_comp] at hX
  rw [idY, Category.comp_id] at hY
  change (K'.isoRightDerivedObj (sectionsFunctor X) n).hom =
    (J'.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
      HomologicalComplex.homologyMap (CX.map d') n at hX
  change (J.isoRightDerivedObj (sectionsFunctor Y) n).inv =
    HomologicalComplex.homologyMap (CY.map d) n ≫ (K.isoRightDerivedObj (sectionsFunctor Y) n).inv at hY
  have hβ := complexSections_natural φ f w d
  dsimp only at hβ
  have hH := congrArg (fun g => HomologicalComplex.homologyMap g n) hβ
  simp only [HomologicalComplex.homologyMap_comp] at hH
  have hR := restrictCohomologyIso_natural φ (CY.map d) n
  simp only [exactPushforwardCohomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map]
  rw [hX, Category.assoc, reassoc_of% hH, reassoc_of% hR, ← R.map_comp, ← hY]

/-- When a pushforward preserves homology and injective objects, the derived
cohomology map is computed using the pushforward of the target resolution. -/
theorem exactPushforward_isCohomologyMap {F : X.left.Modules} {F' : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj F') (n : ℕ) :
    ∃ e : (cohomology X n).obj ((Scheme.Modules.pushforward f).obj F') ≅
        (ModuleCat.restrictScalars.{u} φ).obj ((cohomology Y n).obj F'),
      IsCohomologyMap φ f w α n ((cohomology X n).map α ≫ e.hom) := by
  refine ⟨exactPushforwardCohomologyIso φ f w (injectiveResolution F') n, ?_⟩
  intro I J
  let P := Scheme.Modules.pushforward f
  let J' := mapInjectiveResolution P J
  have hl := InjectiveResolution.desc_commutes_zero α J' I
  refine ⟨⟨InjectiveResolution.desc α J' I, ?_⟩, ?_⟩
  · rw [← mapInjectiveResolution_ι_zero P J]
    exact hl
  · intro l hl
    change I.ι.f 0 ≫ l.f 0 = α ≫ P.map (J.ι.f 0) at hl
    have hc : I.ι.f 0 ≫ l.f 0 = α ≫ J'.ι.f 0 := by
      rwa [mapInjectiveResolution_ι_zero P J]
    have hm := InjectiveResolution.isoRightDerivedObj_hom_naturality α I J' l hc
      (sectionsFunctor X) n
    change (cohomology X n).map α ≫ (J'.isoRightDerivedObj (sectionsFunctor X) n).hom =
      (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫ HomologicalComplex.homologyMap
        (((sectionsFunctor X).mapHomologicalComplex _).map l) n at hm
    rw [exactPushforwardCohomologyIso_independent φ f w (injectiveResolution F') J n]
    let CX := (sectionsFunctor X).mapHomologicalComplex (.up ℕ)
    let CY := (sectionsFunctor Y).mapHomologicalComplex (.up ℕ)
    let β := (pushforwardComplexSectionsIso φ f w J.cocomplex).hom
    let restrictIso := (restrictCohomologyIso φ (CY.obj J.cocomplex) n).inv
    let r := (ModuleCat.restrictScalars.{u} φ).map (J.isoRightDerivedObj (sectionsFunctor Y) n).inv
    let hI := (I.isoRightDerivedObj (sectionsFunctor X) n).hom
    let hJ := (J'.isoRightDerivedObj (sectionsFunctor X) n).hom
    change (cohomology X n).map α ≫
        (hJ ≫ HomologicalComplex.homologyMap β n ≫ restrictIso ≫ r) =
      hI ≫ HomologicalComplex.homologyMap (CX.map l ≫ β) n ≫ restrictIso ≫ r
    rw [reassoc_of% hm, HomologicalComplex.homologyMap_comp_assoc]

end ExactPushforward

section IsomorphicSchemes

variable {A : Type u} [CommRing A] {X Y : SchemeOverRing A}

private def pushforwardEquivalenceOfIso (f : Y.left ⟶ X.left) [IsIso f] :
    Y.left.Modules ≌ X.left.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward (inv f))
    ((Scheme.Modules.pushforwardId Y.left).symm ≪≫
      (Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id f)).symm ≪≫
      (Scheme.Modules.pushforwardComp f (inv f)).symm)
    (Scheme.Modules.pushforwardComp (inv f) f ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pushforwardId X.left)

/-- An isomorphism of schemes and an isomorphism of coefficients induce the
cohomology isomorphism in every degree. -/
theorem isCohomologyMap_of_isIso
    (f : Y.left ⟶ X.left) [IsIso f]
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)))
    {F : X.left.Modules} {F' : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj F') [IsIso α] (n : ℕ) :
    ∃ e : (cohomology X n).obj F ≅ (cohomology Y n).obj F',
      IsCohomologyMap (RingHom.id A) f w α n
        (e.hom ≫ (ModuleCat.restrictScalarsId'App (RingHom.id A) rfl _).inv) := by
  let e := pushforwardEquivalenceOfIso f
  let : (Scheme.Modules.pushforward f).IsEquivalence := by
    change e.functor.IsEquivalence
    exact e.isEquivalence_functor
  obtain ⟨c, hc⟩ := exactPushforward_isCohomologyMap (RingHom.id A) f w α n
  let d := ModuleCat.restrictScalarsId'App (RingHom.id A) rfl ((cohomology Y n).obj F')
  refine ⟨(cohomology X n).mapIso (asIso α) ≪≫ c ≪≫ d, ?_⟩
  simpa only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, d] using hc

end IsomorphicSchemes
section CentralCohomology

open Specs.CentralIsogenies (characterPullback)
open Specs.IsogenyFlagComparison (Restrictions)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
  {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
  {Q' : Presentation P'.negative} {Q : Presentation P.negative}
  {p' : BorelProjection P'} {p : BorelProjection P} {χ : Character P.torus.group}
  {f : G'.val ⟶ G.val} {r : Restrictions f P' P}
  {a' : ModObj G'.val.X Q'.scheme} {a : ModObj G.val.X Q.scheme}

private theorem centralOverlap_second (r : Restrictions f P' P) :
    prod.map f.hom.hom r.borel.hom.hom ≫ HomogeneousQuotient.rightMultiplication P.negative =
      HomogeneousQuotient.rightMultiplication P'.negative ≫ f.hom.hom := by
  have h := congrArg (fun a : P'.negative.group ⟶ G.val ↦ a.hom.hom) r.borel_comm
  change r.borel.hom.hom ≫ P.negative.inclusion.hom.hom =
    P'.negative.inclusion.hom.hom ≫ f.hom.hom at h
  simp only [HomogeneousQuotient.rightMultiplication, MonObj.comp_mul, MonObj.mul_comp,
    prod.map_fst, Category.assoc, prod.map_snd_assoc, h]

open private projection_commutes from LinearAlgebraicGroups.Representation.IsogenyFlagComparison

private theorem centralOverlap_multiplier (r : Restrictions f P' P)
    (p' : BorelProjection P') (p : BorelProjection P) (χ : Character P.torus.group) :
    (prod.map f.hom.hom r.borel.hom.hom).left.appTop (flagTransition p χ) =
      flagTransition p' (characterPullback r.torus χ) := by
  let j := prod.map f.hom.hom r.borel.hom.hom
  let t : (G.val.X ⨯ P.negative.group.X) ⟶ _ :=
    (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X)⁻¹ ≫
      (p.projection ≫ χ).hom.hom
  let t' : (G'.val.X ⨯ P'.negative.group.X) ⟶ _ :=
    (prod.snd : G'.val.X ⨯ P'.negative.group.X ⟶ P'.negative.group.X)⁻¹ ≫
      (p'.projection ≫ characterPullback r.torus χ).hom.hom
  have hw : j ≫ t = t' := by
    have hc : r.borel ≫ (p.projection ≫ χ) = p'.projection ≫ characterPullback r.torus χ := by
      change r.borel ≫ (p.projection ≫ χ) = p'.projection ≫ (r.torus ≫ χ)
      rw [← Category.assoc, projection_commutes r p' p, Category.assoc]
    have he := congrArg (fun a : P'.negative.group ⟶ _ ↦ a.hom.hom) hc
    change r.borel.hom.hom ≫ (p.projection ≫ χ).hom.hom =
      (p'.projection ≫ characterPullback r.torus χ).hom.hom at he
    change j ≫ (prod.snd⁻¹ ≫ (p.projection ≫ χ).hom.hom) = _
    rw [← Category.assoc, GrpObj.comp_inv, show j ≫ prod.snd = prod.snd ≫ r.borel.hom.hom from
      prod.map_snd _ _, ← GrpObj.inv_comp, Category.assoc, he]
  unfold flagTransition
  change (t.left.appTop ≫ j.left.appTop)
      (((Scheme.ΓSpecIso _).inv) (MonoidAlgebra.single _ 1)) =
    t'.left.appTop (((Scheme.ΓSpecIso _).inv) (MonoidAlgebra.single _ 1))
  rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, hw]

private def transportedSection (e : Q'.scheme ≅ Q.scheme)
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ)}
    {m : L'.total ⟶ L.total} (hp : IsPullback m L'.projection L.projection e.hom)
    (U : Q.scheme.left.Opens) :
    SectionsOver L.projection (openInclusion Q.scheme U) ≃
      SectionsOver L'.projection (openInclusion Q'.scheme (e.hom.left ⁻¹ᵁ U)) := by
  let V := e.hom.left ⁻¹ᵁ U
  let j := restrictOver e.hom U V le_rfl
  letI : IsIso j := (restrictOver_pullback e.hom U).isIso_snd_of_isIso
  letI : IsIso m := hp.isIso_fst_of_isIso
  let i := openInclusion Q.scheme U
  let i' := openInclusion Q'.scheme V
  have hj : j ≫ i = i' ≫ e.hom := restrictOver_inclusion _ _ _ _
  have hm : inv m ≫ L'.projection = L.projection ≫ e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, ← hp.w, IsIso.inv_hom_id_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine
    { toFun := fun s => ⟨j ≫ s.val ≫ inv m, by
        rw [Category.assoc, Category.assoc, hm, reassoc_of% s.property, ← Category.assoc, hj]
        change (i' ≫ e.hom) ≫ e.inv = i'
        simp⟩
      invFun := fun s => ⟨inv j ≫ s.val ≫ m, by
        rw [Category.assoc, Category.assoc, hp.w, reassoc_of% s.property, ← hj,
          IsIso.inv_hom_id_assoc]⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }

private theorem transportedSection_comm (e : Q'.scheme ≅ Q.scheme)
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ)}
    {m : L'.total ⟶ L.total} (hp : IsPullback m L'.projection L.projection e.hom)
    (U : Q.scheme.left.Opens) (s : SectionsOver L.projection (openInclusion Q.scheme U)) :
    (transportedSection e hp U s).val ≫ m =
      restrictOver e.hom U (e.hom.left ⁻¹ᵁ U) le_rfl ≫ s.val := by
  let : IsIso m := hp.isIso_fst_of_isIso
  change (restrictOver e.hom U (e.hom.left ⁻¹ᵁ U) le_rfl ≫ s.val ≫ inv m) ≫ m = _
  simp

private theorem transportedSection_coordinate (e : Q'.scheme ≅ Q.scheme)
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ)}
    {m : L'.total ⟶ L.total} (hp : IsPullback m L'.projection L.projection e.hom)
    (w : Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection)
    (ht : L'.trivialization ≫ m = prod.map f.hom.hom (𝟙 (affineLine k)) ≫ L.trivialization)
    (U : Q.scheme.left.Opens) (s : SectionsOver L.projection (openInclusion Q.scheme U)) :
    bundleSectionCoordinate L' (e.hom.left ⁻¹ᵁ U) (transportedSection e hp U s) =
      pullbackOnOpen Q.projection.left (Q'.projection.left ≫ e.hom.left) f.hom.hom.left
        (congrArg Over.Hom.left w.symm) U (bundleSectionCoordinate L U s) := by
  let V := e.hom.left ⁻¹ᵁ U
  let T := Q.projection.left ⁻¹ᵁ U
  let T' := Q'.projection.left ⁻¹ᵁ V
  let j := restrictOver e.hom U V le_rfl
  let q := restrictOver Q.projection U T le_rfl
  let q' := restrictOver Q'.projection V T' le_rfl
  let hw := preimage_le Q.projection.left (Q'.projection.left ≫ e.hom.left)
    f.hom.hom.left (congrArg Over.Hom.left w.symm) U
  let g := restrictOver f.hom.hom T T' hw
  let s' := transportedSection e hp U s
  have hs : s'.val ≫ m = j ≫ s.val := transportedSection_comm e hp U s
  have hg : q' ≫ j = g ≫ q := by
    rw [← cancel_mono (openInclusion Q.scheme U)]
    simp only [Category.assoc, q', j, q, g, restrictOver_inclusion, restrictOver_inclusion_assoc]
    simpa only [Category.assoc] using congrArg (openInclusion G'.val.X T' ≫ ·) w
  let z := bundleCoordinateMap L U s
  let z' := bundleCoordinateMap L' V s'
  have hz : z' = g ≫ z := by
    have hgraph :
        prod.lift (openInclusion G'.val.X T' ≫ f.hom.hom) z' ≫ L.trivialization =
          prod.lift (openInclusion G'.val.X T' ≫ f.hom.hom) (g ≫ z) ≫ L.trivialization := by
      calc
        _ = (prod.lift (openInclusion G'.val.X T') z' ≫ L'.trivialization) ≫ m := by
          rw [Category.assoc, ht, ← Category.assoc, prod.lift_map, Category.comp_id]
        _ = (q' ≫ s'.val) ≫ m := by
          rw [show prod.lift (openInclusion G'.val.X T') z' ≫ L'.trivialization =
              q' ≫ s'.val from bundleCoordinateMap_graph L' V s']
        _ = g ≫ (q ≫ s.val) := by rw [Category.assoc, hs, ← Category.assoc, hg, Category.assoc]
        _ = _ := by
          rw [← bundleCoordinateMap_graph L U s]
          simp only [bundleGraph, ← Category.assoc, prod.comp_lift]
          rw [show g ≫ openInclusion G.val.X T = openInclusion G'.val.X T' ≫ f.hom.hom from
            restrictOver_inclusion _ _ _ _]
    have hl := L.trivializes.hom_ext (by simp) hgraph
    simpa only [prod.lift_snd] using congrArg (· ≫
      (prod.snd : G.val.X ⨯ affineLine k ⟶ affineLine k)) hl
  rw [coordinate_agrees, coordinate_agrees]
  change T'.topIso.hom (lineCoordinate z') =
    pullbackOnOpen Q.projection.left (Q'.projection.left ≫ e.hom.left) f.hom.hom.left
      (congrArg Over.Hom.left w.symm) U (T.topIso.hom (lineCoordinate z))
  rw [hz, lineCoordinate_comp]
  have he := topIso_restrictOver f.hom.hom T T' hw (T.topIso.hom (lineCoordinate z))
  rw [Iso.hom_inv_id_apply (C := CommRingCat)] at he
  exact he

private theorem centralCoefficientComparison
    (h' : FlagKernelPair Q') (h : FlagKernelPair Q)
    (L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ))
    (L : AssociatedBundle Q a p χ)
    (e : Q'.scheme ≅ Q.scheme)
    (w : Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection)
    (m : L'.total ⟶ L.total) (hp : IsPullback m L'.projection L.projection e.hom)
    (ht : L'.trivialization ≫ m = prod.map f.hom.hom (𝟙 (affineLine k)) ≫ L.trivialization) :
    let D := flagLineData Q p χ h
    let D' := flagLineData Q' p' (characterPullback r.torus χ) h'
    ∃ α : D.sheaf ⟶ (Scheme.Modules.pushforward e.hom.left).obj D'.sheaf,
      D.IsPullbackMap D' e.hom.left f.hom.hom.left (congrArg Over.Hom.left w.symm) α ∧ IsIso α := by
  let D := flagLineData Q p χ h
  let D' := flagLineData Q' p' (characterPullback r.torus χ) h'
  let j := prod.map f.hom.hom r.borel.hom.hom
  let w' := congrArg Over.Hom.left w.symm
  obtain ⟨α, hα⟩ := covariancePullback_exists D D' e.hom.left f.hom.hom.left w' j.left
    (congrArg Over.Hom.left (prod.map_fst f.hom.hom r.borel.hom.hom))
    (congrArg Over.Hom.left (centralOverlap_second r))
    (centralOverlap_multiplier r p' p χ)
  refine ⟨α, hα, Scheme.Modules.Hom.isIso_iff_isIso_app.mpr ?_⟩
  intro U
  let V := e.hom.left ⁻¹ᵁ U
  let E := (bundleSectionsOnOpen h U L).trans
    ((transportedSection e hp U).trans (bundleSectionsOnOpen h' V L').symm)
  have he (x : Γ(D.sheaf, U)) : α.app U x = E x := by
    have hker := (inclusion_bijective_onto_covariance D' V).injective
    apply hker
    apply Subtype.ext
    have happ := covariancePullback_app hα U x
    change D'.inclusion.app V (α.app U x) = D'.inclusion.app V (E x)
    change D'.inclusion.app V (α.app U x) = _ at happ
    refine happ.trans ?_
    rw [← bundleSectionsOnOpen_coordinate h' V L' (E x)]
    change pullbackOnOpen _ _ _ w' U (D.inclusion.app U x) =
      bundleSectionCoordinate L' V
        (bundleSectionsOnOpen h' V L' ((bundleSectionsOnOpen h' V L').symm
          (transportedSection e hp U (bundleSectionsOnOpen h U L x))))
    rw [Equiv.apply_symm_apply, transportedSection_coordinate e hp w ht,
      bundleSectionsOnOpen_coordinate h U L]
    rfl
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun x : Γ(D.sheaf, U) => α.app U x)
  rw [show (fun x : Γ(D.sheaf, U) => α.app U x) = E from funext he]
  exact E.bijective

end CentralCohomology

/-- The canonical comparison of an ordered cover in degree zero. -/
theorem cechDegreeZeroComparison.{u} : CechDegreeZeroComparison.{u} := by
  intro A _ X I _ U hU
  exact ⟨cechDegreeZeroIso X U hU, fun f => cechDegreeZeroIso_natural X U hU f⟩

/-- The flag line sheaf satisfies canonical base change on global sections. -/
theorem flagCohomologyZeroBaseChange.{u} : FlagCohomologyZeroBaseChange.{u} := by
  intro k _ G P Q p χ h R
  exact flagCohomologyZero_baseChange R Q p χ h

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of the line bundle under the flag isomorphism gives the derived
cohomology isomorphisms, via the corresponding pullback on coefficients. -/
theorem centralCohomologyIsomorphism.{u} : CentralCohomologyIsomorphism.{u} := by
  intro k _ G' G P' P f hf r p' p χ Q' Q h' h a' a ha' ha L' L
  obtain ⟨e, m, hq, ha, hp, ht, hm⟩ :=
    LinearAlgebraicGroups.Representation.IsogenyFlagComparison.flagBundleComparison
      f hf r p' p χ Q' Q a' a ha' ha L' L
  obtain ⟨α, hα, hIso⟩ := centralCoefficientComparison h' h L' L e hq m hp ht
  let : IsIso α := hIso
  let : IsIso e.hom.left := (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
  refine ⟨e, hq, m, α, ha, hp, ht, hm, hα, hIso, fun n => ?_⟩
  exact isCohomologyMap_of_isIso e.hom.left (by simp) α n


section Translation

open AdjointRepresentation (GroupPoints)
open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] (R : TestAlgebra k)

private abbrev extensionObject (X : SchemeOver k) := (extendScheme R).obj X

private abbrev extensionStructure (X : SchemeOver k) : (extensionObject R X).left ⟶ Spec (CommRingCat.of R) :=
  (extensionObject R X).hom

private theorem extension_hom_ext {T : Scheme.{u}} {Y : SchemeOver k}
    {f g : T ⟶ (extensionObject R Y).left}
    (h₁ : f ≫ extensionProjection R Y = g ≫ extensionProjection R Y)
    (h₂ : f ≫ extensionStructure R Y = g ≫ extensionStructure R Y) : f = g :=
  pullback.hom_ext h₁ h₂

private theorem extensionMap_over {X Y : SchemeOver k} (q : X ⟶ Y) :
    ((extendScheme R).map q).left ≫ extensionStructure R Y = extensionStructure R X :=
  Over.w ((extendScheme R).map q)

private theorem extensionMap_isPullback {X Y : SchemeOver k} (q : X ⟶ Y) :
    IsPullback (extensionProjection R X) ((extendScheme R).map q).left
      q.left (extensionProjection R Y) := by
  let v := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hY : IsPullback (extensionProjection R Y) (extensionStructure R Y) Y.hom v :=
    IsPullback.of_hasPullback _ _
  have hX : IsPullback (extensionProjection R X) (extensionStructure R X)
      (q.left ≫ Y.hom) v := by
    rw [Over.w q]
    exact IsPullback.of_hasPullback _ _
  rw [← extensionMap_over R q] at hX
  exact IsPullback.of_bot hX (extensionProjection_natural R q).symm hY

@[reassoc]
private theorem pointTranslation_fst {H X : SchemeOver k} (a : H ⊗ X ⟶ X)
    (g : Points H R) :
    pointTranslation a R g ≫ extensionProjection R X =
      (lift (projectionToTestScheme R X ≫ g) (projectionToOriginal R X) ≫ a).left :=
  pullback.lift_fst _ _ _

private theorem pointTranslation_structure {H X : SchemeOver k} (a : H ⊗ X ⟶ X)
    (g : Points H R) :
    pointTranslation a R g ≫ extensionStructure R X = extensionStructure R X :=
  pullback.lift_snd _ _ _

private def extensionArrow {X Y : SchemeOver k} (q : X ⟶ Y) :
    extensionAsSchemeOverField R X ⟶ extensionAsSchemeOverField R Y :=
  (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k R)))).map ((extendScheme R).map q)

@[reassoc]
private theorem extensionArrow_original {X Y : SchemeOver k} (q : X ⟶ Y) :
    extensionArrow R q ≫ projectionToOriginal R Y = projectionToOriginal R X ≫ q :=
  Over.OverMorphism.ext (extensionProjection_natural R q)

@[reassoc]
private theorem extensionArrow_testScheme {X Y : SchemeOver k} (q : X ⟶ Y) :
    extensionArrow R q ≫ projectionToTestScheme R Y = projectionToTestScheme R X :=
  Over.OverMorphism.ext (extensionMap_over R q)

private theorem pointTranslation_natural {H' H X' X : SchemeOver k}
    (r : H' ⟶ H) (q : X' ⟶ X)
    (a' : H' ⊗ X' ⟶ X') (a : H ⊗ X ⟶ X)
    (w : a' ≫ q = (r ⊗ₘ q) ≫ a) (g : Points H' R) :
    pointTranslation a' R g ≫ ((extendScheme R).map q).left =
      ((extendScheme R).map q).left ≫ pointTranslation a R (g ≫ r) := by
  apply extension_hom_ext R
  · rw [Category.assoc, extensionProjection_natural, pointTranslation_fst_assoc,
      Category.assoc, pointTranslation_fst]
    change (lift (projectionToTestScheme R X' ≫ g) (projectionToOriginal R X') ≫ a' ≫ q).left =
      (extensionArrow R q ≫
        lift (projectionToTestScheme R X ≫ g ≫ r) (projectionToOriginal R X) ≫ a).left
    congr 1
    rw [w, ← Category.assoc _ (_ ⊗ₘ _) _, lift_map, ← Category.assoc,
      comp_lift, extensionArrow_testScheme_assoc, extensionArrow_original, Category.assoc]
  · simp only [Category.assoc, extensionMap_over, pointTranslation_structure]

private theorem central_point_commutes {G : AffineAlgebraicGroup k} {T S : SchemeOver k}
    {c : T ⟶ G.val.X} (hc : Centralizes (𝟙 G.val) c) (r : S ⟶ T) (g : S ⟶ G.val.X) :
    (r ≫ c) * g = g * (r ≫ c) := by
  unfold Centralizes conjugateFamily at hc
  have hid : (𝟙 G.val : G.val ⟶ G.val).hom.hom = 𝟙 G.val.X := rfl
  simp only [hid, Category.comp_id] at hc
  have h := congrArg (fun b ↦ lift g r ≫ b) hc
  have hg : (r ≫ c) * g * (r ≫ c)⁻¹ = g := by
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_fst_assoc, lift_snd_assoc,
      Category.comp_id, Category.id_comp] using h
  exact mul_inv_eq_iff_eq_mul.mp hg

open HomogeneousQuotient (rightMultiplication)

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
  {p : BorelProjection P} {χ : Character P.torus.group}

private abbrev centralPoint (t : GroupPoints P.torus.group R) : GroupPoints G.val R :=
  t ≫ P.torus.inclusion.hom.hom

private abbrev borelPointInv (p : BorelProjection P) (t : GroupPoints P.torus.group R) :
    GroupPoints P.negative.group R :=
  t⁻¹ ≫ p.inclusion.hom.hom

private theorem borelPointInv_inclusion (p : BorelProjection P)
    (t : GroupPoints P.torus.group R) :
    borelPointInv R p t ≫ P.negative.inclusion.hom.hom = (centralPoint R t)⁻¹ := by
  change (t⁻¹ ≫ p.inclusion.hom.hom) ≫ P.negative.inclusion.hom.hom =
    (t ≫ P.torus.inclusion.hom.hom)⁻¹
  calc
    _ = t⁻¹ ≫ (p.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom) :=
      Category.assoc _ _ _
    _ = t⁻¹ ≫ P.torus.inclusion.hom.hom :=
      congrArg (fun h : P.torus.group ⟶ G.val ↦ t⁻¹ ≫ h.hom.hom) p.inclusion_comp
    _ = _ := GrpObj.inv_comp ..

private def centralOverlapMap (p : BorelProjection P) (t : GroupPoints P.torus.group R) :
    extensionAsSchemeOverField R G.val.X ⟶ G.val.X ⨯ P.negative.group.X :=
  prod.lift (projectionToOriginal R G.val.X)
    (projectionToTestScheme R G.val.X ≫ borelPointInv R p t)

private theorem centralOverlapMap_second (p : BorelProjection P) (t : GroupPoints P.torus.group R)
    (hc : Centralizes (𝟙 G.val) (centralPoint R t)) :
    centralOverlapMap R p t ≫ rightMultiplication P.negative =
      lift (projectionToTestScheme R G.val.X ≫ (centralPoint R t)⁻¹)
        (projectionToOriginal R G.val.X) ≫ μ[G.val.X] := by
  let s := projectionToTestScheme R G.val.X
  let g := projectionToOriginal R G.val.X
  have hcomm := central_point_commutes hc s g
  change centralOverlapMap R p t ≫ rightMultiplication P.negative =
    (s ≫ (centralPoint R t)⁻¹) * g
  simp only [centralOverlapMap, rightMultiplication, MonObj.comp_mul, prod.lift_fst,
    prod.lift_snd_assoc]
  change g * ((s ≫ borelPointInv R p t) ≫ P.negative.inclusion.hom.hom) = _
  rw [Category.assoc s, borelPointInv_inclusion, GrpObj.comp_inv]
  exact (Commute.inv_left hcomm).symm

private def centralOverlapLift (p : BorelProjection P) (t : GroupPoints P.torus.group R) :
    (extensionObject R G.val.X).left ⟶ (extensionObject R (G.val.X ⨯ P.negative.group.X)).left :=
  pullback.lift (centralOverlapMap R p t).left (extensionStructure R G.val.X)
    (Over.w (centralOverlapMap R p t))

@[reassoc]
private theorem centralOverlapLift_fst (p : BorelProjection P) (t : GroupPoints P.torus.group R) :
    centralOverlapLift R p t ≫ extensionProjection R (G.val.X ⨯ P.negative.group.X) =
      (centralOverlapMap R p t).left :=
  pullback.lift_fst _ _ _

private theorem centralOverlapLift_structure (p : BorelProjection P) (t : GroupPoints P.torus.group R) :
    centralOverlapLift R p t ≫ extensionStructure R (G.val.X ⨯ P.negative.group.X) =
      extensionStructure R G.val.X :=
  pullback.lift_snd _ _ _

private theorem centralOverlapLift_first (p : BorelProjection P) (t : GroupPoints P.torus.group R) :
    centralOverlapLift R p t ≫ ((extendScheme R).map
      (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X)).left = 𝟙 _ := by
  apply extension_hom_ext R
  · rw [Category.assoc, extensionProjection_natural, centralOverlapLift_fst_assoc,
      Category.id_comp, ← Over.comp_left]
    simp only [centralOverlapMap, prod.lift_fst]
    rfl
  · simp only [Category.assoc, extensionMap_over, centralOverlapLift_structure, Category.id_comp]

private theorem centralOverlapLift_second (p : BorelProjection P) (t : GroupPoints P.torus.group R)
    (hc : Centralizes (𝟙 G.val) (centralPoint R t)) :
    centralOverlapLift R p t ≫ ((extendScheme R).map (rightMultiplication P.negative)).left =
      pointTranslation μ[G.val.X] R (centralPoint R t)⁻¹ := by
  apply extension_hom_ext R
  · rw [Category.assoc, extensionProjection_natural, centralOverlapLift_fst_assoc,
      ← Over.comp_left, centralOverlapMap_second R p t hc, pointTranslation_fst]
  · simp only [Category.assoc, extensionMap_over, centralOverlapLift_structure,
      pointTranslation_structure]

private theorem centralFlagTranslation_id
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (p : BorelProjection P) (h : FlagKernelPair Q) (t : GroupPoints P.torus.group R)
    (hc : Centralizes (𝟙 G.val) (centralPoint R t)) :
    pointTranslation a.smul R (centralPoint R t)⁻¹ = 𝟙 _ := by
  let q := ((extendScheme R).map Q.projection).left
  let e := centralOverlapLift R p t
  have hq := extensionMap_isPullback R Q.projection
  let : Flat q := MorphismProperty.of_isPullback hq Q.flat
  let : Surjective q := MorphismProperty.of_isPullback hq Q.surjective
  let : Epi q := AlgebraicGeometry.Flat.epi_of_flat_of_surjective q
  apply (cancel_epi q).mp
  have hn := pointTranslation_natural R (𝟙 G.val.X) Q.projection _ _ ha (centralPoint R t)⁻¹
  rw [Category.comp_id] at hn
  rw [Category.comp_id, ← hn, ← centralOverlapLift_second R p t hc]
  have w := congrArg (fun f => ((extendScheme R).map f).left) h.w
  simp only [Functor.map_comp, Over.comp_left] at w
  change (e ≫ _) ≫ q = q
  rw [Category.assoc, ← w, ← Category.assoc, centralOverlapLift_first, Category.id_comp]

end Translation

section CentralMultiplier

open AdjointRepresentation (GroupPoints)
open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] (R : TestAlgebra k)
  {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  (p : BorelProjection P) (χ : Character P.torus.group)
  (t : GroupPoints P.torus.group R)

private theorem centralOverlapLift_multiplier :
    (centralOverlapLift R p t).appTop
        ((extensionProjection R (G.val.X ⨯ P.negative.group.X)).appTop (flagTransition p χ)) =
      groundRingHom (extensionObject R G.val.X) (CharacterPairing.characterValue χ R t) := by
  let s := projectionToTestScheme R G.val.X
  let x : Points (G.val.X ⨯ P.negative.group.X) R :=
    prod.lift (1 : GroupPoints G.val R) (borelPointInv R p t)
  let c : Γ(G.val.X ⨯ P.negative.group.X |>.left, ⊤) := flagTransition p χ
  have hproj : (centralOverlapMap R p t) ≫ prod.snd = (s ≫ x) ≫ prod.snd := by
    simp only [centralOverlapMap, x, prod.lift_snd, Category.assoc, s]
  have hcoord : (centralOverlapMap R p t).left.appTop c = (s ≫ x).left.appTop c := by
    let B := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
    let d : G.val.X ⨯ P.negative.group.X ⟶ (specGroup B).X :=
      (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X)⁻¹ ≫
        (p.projection ≫ χ).hom.hom
    have w : centralOverlapMap R p t ≫ d = (s ≫ x) ≫ d := by
      rw [show d = _ from rfl, ← Category.assoc, ← Category.assoc,
        GrpObj.comp_inv, GrpObj.comp_inv, hproj]
    let coordinate := (Scheme.ΓSpecIso (CommRingCat.of B)).inv
      (MonoidAlgebra.single DiagonalizableGroups.integerGenerator (1 : k))
    change (centralOverlapMap R p t).left.appTop (d.left.appTop coordinate) =
      (s ≫ x).left.appTop (d.left.appTop coordinate)
    have hw := congrArg (fun a => a.left.appTop coordinate) w
    simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hw
  have ht : ((x ≫ prod.snd)⁻¹ ≫ (p.projection ≫ χ).hom.hom) = t ≫ χ.hom.hom := by
    have hsec := congrArg (fun h : P.torus.group ⟶ P.torus.group => h.hom.hom) p.section_projection
    change p.inclusion.hom.hom ≫ p.projection.hom.hom = 𝟙 _ at hsec
    rw [show x ≫ prod.snd = borelPointInv R p t from prod.lift_snd _ _, borelPointInv,
      ← GrpObj.inv_comp, inv_inv]
    change (t ≫ p.inclusion.hom.hom) ≫ p.projection.hom.hom ≫ χ.hom.hom = _
    rw [Category.assoc, ← Category.assoc p.inclusion.hom.hom, hsec, Category.id_comp]
  have he : (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop c) =
      CharacterPairing.characterValue χ R t := by
    refine (flagMultiplierAt_testPoint (p := p) (χ := χ) R x).trans ?_
    unfold CharacterPairing.characterValue
    rw [ht]
  have hval : x.left.appTop c =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv (CharacterPairing.characterValue χ R t) := by
    rw [← he, Iso.hom_inv_id_apply (C := CommRingCat)]
  have hj := congrArg (fun f : (extensionObject R G.val.X).left ⟶
      (G.val.X ⨯ P.negative.group.X).left => f.appTop c)
    (centralOverlapLift_fst R p t)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hj
  change (centralOverlapLift R p t).appTop
      ((extensionProjection R (G.val.X ⨯ P.negative.group.X)).appTop c) = _
  refine hj.trans (hcoord.trans ?_)
  change s.left.appTop (x.left.appTop c) = _
  rw [hval]
  rfl

end CentralMultiplier

section CovarianceScalar

open private groundRingHom_over from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [CommRing A] {X Y : SchemeOverRing A}

private theorem groundRingHomOpen_over (f : X ⟶ Y) (U : Y.left.Opens) (r : A) :
    f.left.app U (groundRingHomOpen Y U r) = groundRingHomOpen X (f.left ⁻¹ᵁ U) r :=
  DFunLike.congr_fun (groundRingHomOpen_pullback (RingHom.id A) f.left (by simp) U) r

private theorem covarianceOverIdentity_scalar (D : CovarianceData Y)
    (t : D.torsor.left ⟶ D.torsor.left)
    (w : t ≫ D.projection.left = D.projection.left ≫ 𝟙 Y.left)
    (j : D.torsor.left ⟶ D.overlap.left)
    (h₀ : j ≫ D.first.left = 𝟙 _)
    (h₁ : j ≫ D.second.left = t)
    (r : A) (hr : j.appTop D.multiplier = groundRingHom D.torsor r) :
    D.IsPullbackMap D (𝟙 Y.left) t w
      (sheafScalarMap Y r D.sheaf ≫ (Scheme.Modules.pushforwardId Y.left).inv.app D.sheaf) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  let q := D.projection.left
  let b := D.overlapProjection.left
  let z : Γ(D.torsor.left, q ⁻¹ᵁ U) := D.inclusion.app U x
  have hj : j ≫ b = q := by
    change j ≫ D.overlapProjection.left = D.projection.left
    rw [← firstLeft_w D, ← Category.assoc, h₀, Category.id_comp]
  let jU := pullbackOnOpen b q j hj U
  let b₀ := pullbackOnOpen q b D.first.left (firstLeft_w D) U
  let b₁ := pullbackOnOpen q b D.second.left (secondLeft_w D) U
  have w' : t ≫ q = q := w.trans (Category.comp_id _)
  have h₁' : b₁ ≫ jU = pullbackOnOpen q q t w' U := by
    dsimp only [b₁, jU]
    rw [pullbackOnOpen_comp]
    exact pullbackOnOpen_congr _ _ h₁ _ _ _
  have h₀' : b₀ ≫ jU = 𝟙 _ := by
    dsimp only [b₀, jU]
    rw [pullbackOnOpen_comp, pullbackOnOpen_congr q q h₀ _ (Category.id_comp q) U]
    simp only [pullbackOnOpen, Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    have hId : (homOfLE (preimage_le q q (𝟙 _) (Category.id_comp q) U)).op =
        𝟙 (op (q ⁻¹ᵁ U)) := Subsingleton.elim _ _
    rw [hId]
    exact D.torsor.left.presheaf.map_id _
  have hz : b₁ z = b₀ z * D.overlap.left.presheaf.map (b ⁻¹ᵁ U).leTop.op D.multiplier :=
    (covariance_app_eq_zero D U z).mp (regularSection_mem_covariance D U x)
  have he : pullbackOnOpen q q t w' U z = z * groundRingHomOpen D.torsor (q ⁻¹ᵁ U) r := by
    have hjz := congrArg (fun y => jU y) hz
    rw [map_mul] at hjz
    change (b₁ ≫ jU) z = (b₀ ≫ jU) z *
      jU (D.overlap.left.presheaf.map (b ⁻¹ᵁ U).leTop.op D.multiplier) at hjz
    rw [h₁', h₀', pullbackOnOpen_restrict_global, hr] at hjz
    exact hjz
  change D.inclusion.app U ((sheafScalarMap Y r D.sheaf).app U x) =
    (D.pullFunctions D (𝟙 Y.left) t w).app U z
  rw [sheafScalarMap_app, D.inclusion.app_smul, pullFunctions_app]
  change q.app U (groundRingHomOpen Y U r) * z = pullbackOnOpen q q t w' U z
  rw [he, mul_comm z]
  exact congrArg (· * z) (groundRingHomOpen_over D.projection U r)

/-- A section of the first projection of the extended kernel pair, with
second projection the inverse central translation, computes scalar
multiplication on the covariant coefficient sheaf. -/
private theorem centralTranslation_coefficient
    {k : Type u} [Field k] (R : TestAlgebra k)
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q)
    (t : AdjointRepresentation.GroupPoints P.torus.group R)
    (hc : Centralizes (𝟙 G.val) (centralPoint R t)) :
    let D := (flagLineData Q p χ h).extend R
    let T := (extendScheme R).obj Q.scheme
    let b := pointTranslation μ[G.val.X] R (centralPoint R t)⁻¹
    let value := CharacterPairing.characterValue χ R t
    ∃ w : b ≫ D.projection.left = D.projection.left ≫ 𝟙 T.left,
      D.IsPullbackMap D (𝟙 T.left) b w
        (sheafScalarMap T value D.sheaf ≫ (Scheme.Modules.pushforwardId T.left).inv.app D.sheaf) := by
  let D := (flagLineData Q p χ h).extend R
  let b := pointTranslation μ[G.val.X] R (centralPoint R t)⁻¹
  let j := centralOverlapLift R p t
  have h₀ : j ≫ D.first.left = 𝟙 _ := centralOverlapLift_first R p t
  have h₁ : j ≫ D.second.left = b := centralOverlapLift_second R p t hc
  have w : b ≫ D.projection.left = D.projection.left ≫ 𝟙 _ := by
    rw [← h₁, Category.assoc, secondLeft_w D, ← firstLeft_w D,
      ← Category.assoc, h₀, Category.id_comp, Category.comp_id]
  exact ⟨w, covarianceOverIdentity_scalar D b w j h₀ h₁ _
    (centralOverlapLift_multiplier R p χ t)⟩

end CovarianceScalar

section IdentityCohomology

open private restrictCohomologyIso from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem shortComplex_mapHomologyIso_id {C : Type*} [Category* C] [Abelian C]
    (S : ShortComplex C) :
    (S.mapHomologyIso (𝟭 C)).hom = 𝟙 S.homology := by
  let h := S.homologyData.left.map (𝟭 C)
  change h.homologyIso.hom = _
  apply (cancel_epi (S.map (𝟭 C)).homologyπ).mp
  change (S.map (𝟭 C)).homologyπ ≫ h.homologyIso.hom =
    (S.map (𝟭 C)).homologyπ ≫ 𝟙 _
  rw [Category.comp_id, h.homologyπ_comp_homologyIso_hom]
  have hi : h.cyclesIso.hom = S.homologyData.left.cyclesIso.hom := by
    apply (cancel_mono h.i).mp
    exact h.cyclesIso_hom_comp_i.trans
      (S.homologyData.left.cyclesIso_hom_comp_i).symm
  rw [hi]
  let h₀ := S.homologyData.left
  change h₀.cyclesIso.hom ≫ h₀.π = S.homologyπ
  have hId : h₀.homologyIso.hom = 𝟙 S.homology := by
    change S.leftHomologyIso.inv ≫ S.leftHomologyIso.hom = _
    exact S.leftHomologyIso.inv_hom_id
  exact h₀.homologyπ_comp_homologyIso_hom.symm.trans (by rw [hId, Category.comp_id])

variable {A : Type u} [CommRing A] (X : SchemeOverRing A)

private abbrev identityRestriction (A : Type u) [CommRing A] :=
  ModuleCat.restrictScalarsId.{u} A

private theorem restrictIdentity_homology
    (C : CochainComplex (ModuleCat.{u} A) ℕ)
    (v : C ⟶ ((ModuleCat.restrictScalars.{u} (RingHom.id A)).mapHomologicalComplex _).obj C)
    (hv : ∀ i, v.f i = (identityRestriction A).inv.app (C.X i)) (n : ℕ) :
    HomologicalComplex.homologyMap v n ≫ (restrictCohomologyIso (RingHom.id A) C n).inv =
      (identityRestriction A).inv.app (C.homology n) := by
  unfold restrictCohomologyIso HomologicalComplex.homologyMap
  have h : (HomologicalComplex.shortComplexFunctor _ _ n).map v =
      (C.sc n).mapNatTrans (identityRestriction A).inv := by
    ext : 1
    all_goals exact hv _
  rw [h, ShortComplex.homologyMap_mapNatTrans]
  let S := C.sc n
  let e := S.mapHomologyIso (ModuleCat.restrictScalars (RingHom.id A))
  change ((S.mapHomologyIso (𝟭 _)).hom ≫ (identityRestriction A).inv.app S.homology ≫ e.inv) ≫
    e.hom = _
  have hId : (S.mapHomologyIso (𝟭 _)).hom = 𝟙 S.homology :=
    shortComplex_mapHomologyIso_id S
  refine congrArg (fun f : S.homology ⟶ S.homology =>
    (f ≫ (identityRestriction A).inv.app S.homology ≫ e.inv) ≫ e.hom) hId |>.trans ?_
  simp only [Category.id_comp, Category.assoc, e.inv_hom_id, Category.comp_id]
  rfl

/-- A lift over the identity of a scheme acts by the usual derived functor
on the underlying coefficient homomorphism. -/
theorem isCohomologyMap_identity
    (w : 𝟙 X.left ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)))
    {F F' : X.left.Modules} (α : F ⟶ F')
    (n : ℕ)
    (m : (cohomology X n).obj F ⟶
      (ModuleCat.restrictScalars.{u} (RingHom.id A)).obj ((cohomology X n).obj F'))
    (hm : IsCohomologyMap (RingHom.id A) (𝟙 X.left) w
      (α ≫ (Scheme.Modules.pushforwardId X.left).inv.app F') n m) :
    m = (cohomology X n).map α ≫ (identityRestriction A).inv.app _ := by
  let I := injectiveResolution F
  let J := injectiveResolution F'
  let P := Scheme.Modules.pushforward (𝟙 X.left)
  let e := Scheme.Modules.pushforwardId X.left
  let Γ := (sectionsFunctor X).mapHomologicalComplex (.up ℕ)
  let r := ModuleCat.restrictScalars.{u} (RingHom.id A)
  let t := InjectiveResolution.desc α J I
  let j : J.cocomplex ⟶ (P.mapHomologicalComplex _).obj J.cocomplex :=
    HomologicalComplex.Hom.mk (fun i => e.inv.app (J.cocomplex.X i))
      (fun i j _ => (e.inv.naturality (J.cocomplex.d i j)).symm)
  have hj : I.ι.f 0 ≫ (t ≫ j).f 0 = (α ≫ e.inv.app F') ≫ P.map (J.ι.f 0) := by
    change I.ι.f 0 ≫ t.f 0 ≫ e.inv.app (J.cocomplex.X 0) =
      (α ≫ e.inv.app F') ≫ P.map (J.ι.f 0)
    rw [← Category.assoc, InjectiveResolution.desc_commutes_zero]
    have hn := e.inv.naturality (J.ι.f 0)
    change J.ι.f 0 ≫ e.inv.app (J.cocomplex.X 0) = e.inv.app F' ≫ P.map (J.ι.f 0) at hn
    rw [Category.assoc, hn, Category.assoc]
  have h := (hm I J).2 (t ≫ j) hj
  let β := (pushforwardComplexSectionsIso (RingHom.id A) (𝟙 X.left) w J.cocomplex).hom
  let C := Γ.obj J.cocomplex
  let j' := Γ.map j ≫ β
  have hj' (i : ℕ) : j'.f i = (identityRestriction A).inv.app (C.X i) := by
    apply ModuleCat.hom_ext
    ext x : 1
    rfl
  change m = (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
    HomologicalComplex.homologyMap (Γ.map (t ≫ j) ≫ β) n ≫
      (restrictCohomologyIso (RingHom.id A) C n).inv ≫
      r.map (J.isoRightDerivedObj (sectionsFunctor X) n).inv at h
  rw [Functor.map_comp, Category.assoc, show Γ.map j ≫ β = j' from rfl,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    reassoc_of% restrictIdentity_homology C j' hj' n] at h
  have hn := InjectiveResolution.isoRightDerivedObj_hom_naturality _ I J t
    (InjectiveResolution.desc_commutes_zero α J I) (sectionsFunctor X) n
  change (cohomology X n).map α ≫ (J.isoRightDerivedObj (sectionsFunctor X) n).hom =
    (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
      HomologicalComplex.homologyMap (Γ.map t) n at hn
  rw [← reassoc_of% hn, ← (identityRestriction A).inv.naturality] at h
  let eJ := J.isoRightDerivedObj (sectionsFunctor X) n
  change m = (cohomology X n).map α ≫ eJ.hom ≫ eJ.inv ≫
    (identityRestriction A).inv.app _ at h
  simpa only [eJ.hom_inv_id_assoc] using h

end IdentityCohomology

section CohomologyComposition

open private restrictCohomologyIso from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [CommRing A] {X Y Z : SchemeOverRing A}

private abbrev sectionsComplex (X : SchemeOverRing A) :=
  (sectionsFunctor X).mapHomologicalComplex (.up ℕ)

private abbrev cohomologyRestriction (X : SchemeOverRing A) (F : X.left.Modules) (n : ℕ) :=
  (identityRestriction A).app ((cohomology X n).obj F)

private def identityRestrictionComplex (C : CochainComplex (ModuleCat.{u} A) ℕ) :
    ((ModuleCat.restrictScalars (RingHom.id A)).mapHomologicalComplex (.up ℕ)).obj C ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (identityRestriction A).app (C.X i))
    (fun i j _ => ((identityRestriction A).hom.naturality (C.d i j)).symm)

private def sectionsPushforwardOverIso (f : Y ⟶ X) (C : CochainComplex Y.left.Modules ℕ) :
    (sectionsComplex X).obj (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℕ)).obj C) ≅
      (sectionsComplex Y).obj C :=
  pushforwardComplexSectionsIso (RingHom.id A) f.left (by simp) C ≪≫
    identityRestrictionComplex ((sectionsComplex Y).obj C)

private def sectionsLiftOver (f : Y ⟶ X) {I : CochainComplex X.left.Modules ℕ}
    {J : CochainComplex Y.left.Modules ℕ}
    (l : I ⟶ ((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℕ)).obj J) :
    (sectionsComplex X).obj I ⟶ (sectionsComplex Y).obj J :=
  (sectionsComplex X).map l ≫ (sectionsPushforwardOverIso f J).hom

private theorem cohomologyMap_over_eq (f : Y ⟶ X)
    {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f.left).obj G) (n : ℕ)
    {m : (cohomology X n).obj F ⟶ (cohomology Y n).obj G}
    (hm : IsCohomologyMap (RingHom.id A) f.left (by simp) α n
      (m ≫ (cohomologyRestriction Y G n).inv))
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (l : I.cocomplex ⟶ ((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℕ)).obj
      J.cocomplex)
    (hl : I.ι.f 0 ≫ l.f 0 = α ≫ (Scheme.Modules.pushforward f.left).map (J.ι.f 0)) :
    m = (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
      HomologicalComplex.homologyMap (sectionsLiftOver f l) n ≫
      (J.isoRightDerivedObj (sectionsFunctor Y) n).inv := by
  let C := (sectionsComplex Y).obj J.cocomplex
  let e := identityRestrictionComplex C
  have h := (hm I J).2 l hl
  change m ≫ (cohomologyRestriction Y G n).inv =
    (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
      HomologicalComplex.homologyMap ((sectionsComplex X).map l ≫
        (pushforwardComplexSectionsIso (RingHom.id A) f.left (by simp) J.cocomplex).hom) n ≫
      (restrictCohomologyIso (RingHom.id A) C n).inv ≫
      (ModuleCat.restrictScalars (RingHom.id A)).map
        (J.isoRightDerivedObj (sectionsFunctor Y) n).inv at h
  have heq : sectionsLiftOver f l ≫ e.inv =
      (sectionsComplex X).map l ≫
        (pushforwardComplexSectionsIso (RingHom.id A) f.left (by simp) J.cocomplex).hom := by
    simp only [sectionsLiftOver, sectionsPushforwardOverIso, Iso.trans_hom, Category.assoc]
    change (sectionsComplex X).map l ≫
      (pushforwardComplexSectionsIso (RingHom.id A) f.left (by simp) J.cocomplex).hom ≫
        e.hom ≫ e.inv = _
    rw [e.hom_inv_id, Category.comp_id]
  rw [← heq, HomologicalComplex.homologyMap_comp, Category.assoc,
    reassoc_of% restrictIdentity_homology C e.inv (fun _ => rfl) n] at h
  have hn := (identityRestriction A).inv.naturality (J.isoRightDerivedObj (sectionsFunctor Y) n).inv
  change (J.isoRightDerivedObj (sectionsFunctor Y) n).inv ≫ (cohomologyRestriction Y G n).inv =
      (identityRestriction A).inv.app (C.homology n) ≫
        (ModuleCat.restrictScalars (RingHom.id A)).map (J.isoRightDerivedObj (sectionsFunctor Y) n).inv
    at hn
  rw [← hn] at h
  apply (cancel_mono (cohomologyRestriction Y G n).inv).mp
  simpa only [Category.assoc] using h

/-- Two cohomology maps over the same ring compose by composing the lifts of
the corresponding coefficient maps. -/
theorem cohomologyMap_over_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : X.left.Modules} {G : Y.left.Modules} {H : Z.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f.left).obj G)
    (β : G ⟶ (Scheme.Modules.pushforward g.left).obj H)
    (n : ℕ)
    {m₁ : (cohomology X n).obj F ⟶ (cohomology Y n).obj G}
    {m₂ : (cohomology Y n).obj G ⟶ (cohomology Z n).obj H}
    {m₃ : (cohomology X n).obj F ⟶ (cohomology Z n).obj H}
    (h₁ : IsCohomologyMap (RingHom.id A) f.left (by simp) α n
      (m₁ ≫ (cohomologyRestriction Y G n).inv))
    (h₂ : IsCohomologyMap (RingHom.id A) g.left (by simp) β n
      (m₂ ≫ (cohomologyRestriction Z H n).inv))
    (h₃ : IsCohomologyMap (RingHom.id A) (g ≫ f).left (by simp)
      (α ≫ (Scheme.Modules.pushforward f.left).map β ≫
        (Scheme.Modules.pushforwardComp g.left f.left).hom.app H) n
      (m₃ ≫ (cohomologyRestriction Z H n).inv)) :
    m₁ ≫ m₂ = m₃ := by
  let I := injectiveResolution F
  let J := injectiveResolution G
  let K := injectiveResolution H
  let P := Scheme.Modules.pushforward f.left
  let Q := Scheme.Modules.pushforward g.left
  let combine := (Scheme.Modules.pushforwardComp g.left f.left).hom
  obtain ⟨⟨l, hl⟩, _⟩ := h₁ I J
  obtain ⟨⟨t, ht⟩, _⟩ := h₂ J K
  let l' : I.cocomplex ⟶ ((Scheme.Modules.pushforward (g ≫ f).left).mapHomologicalComplex
      (.up ℕ)).obj K.cocomplex :=
    l ≫ (P.mapHomologicalComplex (.up ℕ)).map t ≫
      ((Functor.mapHomologicalComplexCompIso (Scheme.Modules.pushforwardComp g.left f.left)
        (.up ℕ)).app K.cocomplex).hom
  have hl' : I.ι.f 0 ≫ l'.f 0 =
      (α ≫ P.map β ≫ combine.app H) ≫ (Scheme.Modules.pushforward (g ≫ f).left).map (K.ι.f 0) := by
    change I.ι.f 0 ≫ l.f 0 ≫ P.map (t.f 0) ≫ combine.app (K.cocomplex.X 0) = _
    change I.ι.f 0 ≫ l.f 0 = α ≫ P.map (J.ι.f 0) at hl
    change J.ι.f 0 ≫ t.f 0 = β ≫ Q.map (K.ι.f 0) at ht
    rw [← Category.assoc (I.ι.f 0), hl, Category.assoc, ← P.map_comp_assoc, ht, P.map_comp,
      Category.assoc]
    have hn := combine.naturality (K.ι.f 0)
    change P.map (Q.map (K.ι.f 0)) ≫ combine.app (K.cocomplex.X 0) =
      combine.app H ≫ (Scheme.Modules.pushforward (g ≫ f).left).map (K.ι.f 0) at hn
    rw [hn]
    simp only [Category.assoc]
  have hw : sectionsLiftOver (g ≫ f) l' = sectionsLiftOver f l ≫ sectionsLiftOver g t := by
    ext i : 1
    apply ModuleCat.hom_ext
    ext x : 1
    rfl
  rw [cohomologyMap_over_eq f α n h₁ I J l hl, cohomologyMap_over_eq g β n h₂ J K t ht,
    cohomologyMap_over_eq (g ≫ f) _ n h₃ I K l' hl', hw]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.homologyMap_comp]

end CohomologyComposition

section CentralDerivedScalar

open AdjointRepresentation (GroupPoints)
open RootWeightAction (act)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem cohomologyMap_of_identity_translation
    {A : Type u} [CommRing A] (X : SchemeOverRing A) (D : CovarianceData X)
    (f : X.left ⟶ X.left) (hf : f = 𝟙 _)
    (hbase : f ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)))
    (b : D.torsor.left ⟶ D.torsor.left) (r : A)
    (h : ∃ (w : b ≫ D.projection.left = D.projection.left ≫ 𝟙 X.left),
      D.IsPullbackMap D (𝟙 X.left) b w
        (sheafScalarMap X r D.sheaf ≫ (Scheme.Modules.pushforwardId X.left).inv.app D.sheaf)) :
    ∃ (w : b ≫ D.projection.left = D.projection.left ≫ f)
      (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D.sheaf),
      D.IsPullbackMap D f b w α ∧ ∀ n,
        IsCohomologyMap (RingHom.id A) f hbase α n
          ((r • 𝟙 _) ≫ (identityRestriction A).inv.app _) := by
  subst f
  obtain ⟨w, hw⟩ := h
  let s := sheafScalarMap X r D.sheaf
  let α := s ≫ (Scheme.Modules.pushforwardId X.left).inv.app D.sheaf
  refine ⟨w, α, hw, fun n => ?_⟩
  let : (Scheme.Modules.pushforward (𝟙 X.left)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Scheme.Modules.pushforwardId X.left).symm
  obtain ⟨e, he⟩ := exactPushforward_isCohomologyMap (RingHom.id A) (𝟙 X.left) hbase α n
  have hmap := isCohomologyMap_identity X hbase s n _ he
  change _ ≫ e.hom = (cohomology X n).map (sheafScalarMap X r D.sheaf) ≫
    (identityRestriction A).inv.app _ at hmap
  rw [cohomology_map_scalar] at hmap
  rwa [hmap] at he

/-- Central inverse translation comes from right multiplication by the
inverse torus point. Covariance evaluates at its inverse, giving the positive
character on every cohomology group after scalar extension of the flag. -/
theorem centralTranslationOnCohomology.{u} : CentralTranslationOnCohomology.{u} := by
  intro k _ G P Q p χ h a ha R t hc
  let Y := (extendScheme R).obj Q.scheme
  let D := (flagLineData Q p χ h).extend R
  let g := centralPoint R t
  let f := pointTranslation a.smul R g⁻¹
  let b := pointTranslation μ[G.val.X] R g⁻¹
  have hf : f = 𝟙 _ := centralFlagTranslation_id R ha p h t hc
  exact ⟨hf, cohomologyMap_of_identity_translation Y D f hf
    (pointTranslation_over a.smul R g⁻¹) b _
    (centralTranslation_coefficient R Q p χ h t hc)⟩

/-- The geometric formula applies to any rational action that is transported
from the extended flag cohomology by the scalar-extension isomorphism. -/
theorem centralCohomologyScalarAction_of_baseChange.{u}
    (baseChange : FlagCohomologyBaseChange.{u}) : CentralCohomologyScalarAction.{u} := by
  intro k _ G P Q p χ h a n basis ρ ha hρ R t hc v
  let D := (flagLineData Q p χ h).extend R
  let Y := (extendScheme R).obj Q.scheme
  let g := centralPoint R t
  let f := pointTranslation a.smul R g⁻¹
  let b := pointTranslation μ[G.val.X] R g⁻¹
  let value := CharacterPairing.characterValue χ R t
  let H := (cohomology Y n).obj D.sheaf
  obtain ⟨E⟩ := baseChange Q p χ h R
  let coord := (extendedCoordinates R basis).toLinearMap.comp (E.iso n).inv.hom
  obtain ⟨w, α, m, hα, hm, hcoord⟩ := hρ R g E
  obtain ⟨_, w', β, hβ, hscalar⟩ := centralTranslationOnCohomology Q p χ h a ha R t hc
  have hβα : α = β := covariancePullback_unique D D f b w hα hβ
  subst β
  let d := (identityRestriction R).app H
  have heq : m ≫ d.inv = (value • 𝟙 H) ≫ d.inv :=
    inducedCohomologyMap_unique (RingHom.id R) f _ α n hm (hscalar n)
  have hmap : m = value • 𝟙 H := (cancel_mono d.inv).mp heq
  let z : H := (E.iso n).hom ((extendedCoordinates R basis).symm v)
  have hz : coord z = v := by
    change extendedCoordinates R basis ((E.iso n).inv ((E.iso n).hom _)) = _
    have he := congrArg (fun j => j ((extendedCoordinates R basis).symm v))
      (E.iso n).hom_inv_id
    change (E.iso n).inv ((E.iso n).hom ((extendedCoordinates R basis).symm v)) =
      (extendedCoordinates R basis).symm v at he
    rw [he, (extendedCoordinates R basis).apply_symm_apply]
  have he : coord (m z) = act ρ R g (coord z) := hcoord z
  rw [hmap] at he
  change coord (value • z) = _ at he
  rw [LinearMap.map_smul, hz] at he
  exact he.symm

end CentralDerivedScalar

section TranslationAction

open AdjointRepresentation (GroupPoints)
open HomogeneousQuotient (rightMultiplication)
open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] (R : TestAlgebra k)

private def translationArrow {H X : SchemeOver k} (a : H ⊗ X ⟶ X) (g : Points H R) :
    extensionAsSchemeOverField R X ⟶ extensionAsSchemeOverField R X :=
  Over.homMk (pointTranslation a R g) (by
    change pointTranslation a R g ≫ extensionStructure R X ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) = _
    rw [← Category.assoc, pointTranslation_structure]
    rfl)

@[reassoc]
private theorem translationArrow_testScheme {H X : SchemeOver k} (a : H ⊗ X ⟶ X) (g : Points H R) :
    translationArrow R a g ≫ projectionToTestScheme R X = projectionToTestScheme R X :=
  Over.OverMorphism.ext (pointTranslation_structure R a g)

@[reassoc]
private theorem translationArrow_original {H X : SchemeOver k} [MonObj H] [ModObj H X]
    (g : Points H R) :
    translationArrow R γ[H, X] g ≫ projectionToOriginal R X =
      (projectionToTestScheme R X ≫ g) • projectionToOriginal R X :=
  Over.OverMorphism.ext (pointTranslation_fst R _ g)

private theorem pointTranslation_one {H X : SchemeOver k} [MonObj H] [ModObj H X] :
    pointTranslation γ[H, X] R (1 : Points H R) = 𝟙 _ := by
  apply extension_hom_ext R
  · rw [pointTranslation_fst, Category.id_comp]
    change (((projectionToTestScheme R X ≫ (1 : Points H R)) • projectionToOriginal R X)).left = _
    rw [MonObj.comp_one, one_smul]
    rfl
  · rw [pointTranslation_structure, Category.id_comp]

private theorem pointTranslation_comp {H X : SchemeOver k} [MonObj H] [ModObj H X]
    (g h : Points H R) :
    pointTranslation γ[H, X] R g ≫
        pointTranslation γ[H, X] R h =
      pointTranslation γ[H, X] R (h * g) := by
  apply extension_hom_ext R
  · rw [Category.assoc, pointTranslation_fst, pointTranslation_fst]
    change (translationArrow R γ[H, X] g ≫
          ((projectionToTestScheme R X ≫ h) • projectionToOriginal R X)).left =
        (((projectionToTestScheme R X ≫ (h * g)) • projectionToOriginal R X)).left
    rw [ModObj.comp_smul, translationArrow_testScheme_assoc,
      translationArrow_original, ← mul_smul, MonObj.comp_mul]
  · simp only [Category.assoc, pointTranslation_structure]

private theorem pointTranslation_isIso {H X : SchemeOver k} [GrpObj H] [ModObj H X] (g : Points H R) :
    IsIso (pointTranslation γ[H, X] R g) := by
  refine ⟨⟨pointTranslation γ[H, X] R g⁻¹, ?_, ?_⟩⟩
  · rw [pointTranslation_comp, inv_mul_cancel, pointTranslation_one]
  · rw [pointTranslation_comp, mul_inv_cancel, pointTranslation_one]

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}

private abbrev Overlap := G.val.X ⨯ P.negative.group.X

private def overlapTranslationToOriginal (g : GroupPoints G.val R) :
    extensionAsSchemeOverField R (Overlap (P := P)) ⟶ Overlap (P := P) :=
  let s := projectionToTestScheme R (Overlap (P := P))
  let v := projectionToOriginal R (Overlap (P := P))
  prod.lift ((s ≫ g) * (v ≫ prod.fst)) (v ≫ prod.snd)

private theorem overlapTranslation_secondProjection (g : GroupPoints G.val R) :
    overlapTranslationToOriginal (P := P) R g ≫ prod.snd =
      projectionToOriginal R (Overlap (P := P)) ≫ prod.snd :=
  prod.lift_snd _ _

private def overlapTranslation (g : GroupPoints G.val R) :
    (extensionObject R (Overlap (P := P))).left ⟶
      (extensionObject R (Overlap (P := P))).left :=
  pullback.lift (overlapTranslationToOriginal (P := P) R g).left
    (extensionStructure R (Overlap (P := P))) (Over.w (overlapTranslationToOriginal (P := P) R g))

@[reassoc]
private theorem overlapTranslation_original (g : GroupPoints G.val R) :
    overlapTranslation (P := P) R g ≫ extensionProjection R (Overlap (P := P)) =
      (overlapTranslationToOriginal (P := P) R g).left :=
  pullback.lift_fst _ _ _

private theorem overlapTranslation_structure (g : GroupPoints G.val R) :
    overlapTranslation (P := P) R g ≫ extensionStructure R (Overlap (P := P)) =
      extensionStructure R (Overlap (P := P)) :=
  pullback.lift_snd _ _ _

private theorem overlapTranslation_commutes (g : GroupPoints G.val R)
    (r : Overlap (P := P) ⟶ G.val.X)
    (hr : overlapTranslationToOriginal (P := P) R g ≫ r =
      (projectionToTestScheme R (Overlap (P := P)) ≫ g) *
        (projectionToOriginal R (Overlap (P := P)) ≫ r)) :
    overlapTranslation (P := P) R g ≫ ((extendScheme R).map r).left =
      ((extendScheme R).map r).left ≫ pointTranslation μ[G.val.X] R g := by
  apply extension_hom_ext R
  · rw [Category.assoc, extensionProjection_natural, overlapTranslation_original_assoc,
      Category.assoc, pointTranslation_fst, ← Over.comp_left, hr]
    change (((projectionToTestScheme R (Overlap (P := P)) ≫ g) *
        (projectionToOriginal R (Overlap (P := P)) ≫ r))).left =
      (extensionArrow R r ≫
        ((projectionToTestScheme R G.val.X ≫ g) * projectionToOriginal R G.val.X)).left
    rw [MonObj.comp_mul, extensionArrow_testScheme_assoc, extensionArrow_original]
  · rw [Category.assoc, extensionMap_over, overlapTranslation_structure, Category.assoc,
      pointTranslation_structure, extensionMap_over]

private theorem overlapTranslation_first (g : GroupPoints G.val R) :
    overlapTranslation (P := P) R g ≫ ((extendScheme R).map
      (prod.fst : Overlap (P := P) ⟶ G.val.X)).left =
      ((extendScheme R).map (prod.fst : Overlap (P := P) ⟶ G.val.X)).left ≫
        pointTranslation μ[G.val.X] R g :=
  overlapTranslation_commutes R g _ (prod.lift_fst _ _)

private theorem overlapTranslation_second (g : GroupPoints G.val R) :
    overlapTranslation (P := P) R g ≫ ((extendScheme R).map (rightMultiplication P.negative)).left =
      ((extendScheme R).map (rightMultiplication P.negative)).left ≫
        pointTranslation μ[G.val.X] R g := by
  apply overlapTranslation_commutes R g
  simp only [rightMultiplication, overlapTranslationToOriginal, MonObj.comp_mul, prod.lift_fst,
    prod.lift_snd_assoc, Category.assoc, mul_assoc]

private theorem overlapTranslation_multiplier (p : BorelProjection P) (χ : Character P.torus.group)
    (g : GroupPoints G.val R) :
    (overlapTranslation (P := P) R g).appTop
      ((extensionProjection R (Overlap (P := P))).appTop (flagTransition p χ)) =
      (extensionProjection R (Overlap (P := P))).appTop (flagTransition p χ) := by
  let B := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
  let d : Overlap (P := P) ⟶ (specGroup B).X :=
    (prod.snd : Overlap (P := P) ⟶ P.negative.group.X)⁻¹ ≫ (p.projection ≫ χ).hom.hom
  have h : overlapTranslationToOriginal (P := P) R g ≫ d =
      projectionToOriginal R (Overlap (P := P)) ≫ d := by
    rw [show d = _ from rfl, ← Category.assoc, ← Category.assoc, GrpObj.comp_inv, GrpObj.comp_inv,
      overlapTranslation_secondProjection]
  have h' : overlapTranslation (P := P) R g ≫ extensionProjection R (Overlap (P := P)) ≫ d.left =
      extensionProjection R (Overlap (P := P)) ≫ d.left := by
    rw [← Category.assoc, overlapTranslation_original, ← Over.comp_left]
    exact congrArg Over.Hom.left h
  let z := (Scheme.ΓSpecIso (CommRingCat.of B)).inv
    (MonoidAlgebra.single DiagonalizableGroups.integerGenerator (1 : k))
  have hz := congrArg (fun f => f.appTop z) h'
  change (overlapTranslation (P := P) R g).appTop
      ((extensionProjection R (Overlap (P := P))).appTop (d.left.appTop z)) =
        (extensionProjection R (Overlap (P := P))).appTop (d.left.appTop z)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hz

/-- The inverse translation by a group point gives a cohomology endomorphism
on the flag over its test algebra via the prescribed covariance pullback. -/
theorem flagTranslationCohomologyMap_at
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (g : GroupPoints G.val R) (n : ℕ) :
    let D := (flagLineData Q p χ h).extend R
    let Y := (extendScheme R).obj Q.scheme
    let f := pointTranslation a.smul R g⁻¹
    let t := pointTranslation μ[G.val.X] R g⁻¹
    ∃ (w : t ≫ D.projection.left = D.projection.left ≫ f)
      (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D.sheaf)
      (m : (cohomology Y n).obj D.sheaf ⟶ (cohomology Y n).obj D.sheaf),
      D.IsPullbackMap D f t w α ∧
      IsCohomologyMap (RingHom.id R) f (pointTranslation_over a.smul R g⁻¹) α n
        (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv) := by
  let D := (flagLineData Q p χ h).extend R
  let Y := (extendScheme R).obj Q.scheme
  let f := pointTranslation a.smul R g⁻¹
  let t := pointTranslation μ[G.val.X] R g⁻¹
  let j := overlapTranslation (P := P) R g⁻¹
  have w : t ≫ D.projection.left = D.projection.left ≫ f := by
    have hn := pointTranslation_natural R (𝟙 G.val.X) Q.projection _ _ ha g⁻¹
    rwa [Category.comp_id] at hn
  obtain ⟨α, hα⟩ := covariancePullback_exists D D f t w j
    (overlapTranslation_first R g⁻¹) (overlapTranslation_second R g⁻¹)
    (overlapTranslation_multiplier R p χ g⁻¹)
  let : IsIso f := @pointTranslation_isIso _ _ R _ _ _ a g⁻¹
  let e := pushforwardEquivalenceOfIso (X := Y) (Y := Y) f
  let : (Scheme.Modules.pushforward f).IsEquivalence := e.isEquivalence_functor
  obtain ⟨c, hc⟩ := exactPushforward_isCohomologyMap (RingHom.id R) f
    (pointTranslation_over a.smul R g⁻¹) α n
  let d := ModuleCat.restrictScalarsId'App (RingHom.id R) rfl ((cohomology Y n).obj D.sheaf)
  refine ⟨w, α, (cohomology Y n).map α ≫ c.hom ≫ d.hom, hα, ?_⟩
  change IsCohomologyMap (RingHom.id R) f _ α n
    (((cohomology Y n).map α ≫ c.hom ≫ d.hom) ≫ d.inv)
  have hid : c.hom ≫ d.hom ≫ d.inv = c.hom := by rw [d.hom_inv_id, Category.comp_id]
  rw [Category.assoc, Category.assoc, hid]
  exact hc

end TranslationAction


section TranslationGroupLaw

open AdjointRepresentation (GroupPoints)
attribute [local instance] ModObj.regular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem covarianceCohomologyMaps_comp {A : Type u} [CommRing A] {Y : SchemeOverRing A}
    (D : CovarianceData Y) (f g : Y ⟶ Y)
    (t s : D.torsor.left ⟶ D.torsor.left)
    (w : t ≫ D.projection.left = D.projection.left ≫ f.left)
    (w' : s ≫ D.projection.left = D.projection.left ≫ g.left)
    (α : D.sheaf ⟶ (Scheme.Modules.pushforward f.left).obj D.sheaf)
    (β : D.sheaf ⟶ (Scheme.Modules.pushforward g.left).obj D.sheaf)
    (n : ℕ)
    {m₁ m₂ m₃ : (cohomology Y n).obj D.sheaf ⟶ (cohomology Y n).obj D.sheaf}
    (hα : D.IsPullbackMap D f.left t w α) (hβ : D.IsPullbackMap D g.left s w' β)
    (h₁ : IsCohomologyMap (RingHom.id A) f.left (by simp) α n
      (m₁ ≫ (cohomologyRestriction Y D.sheaf n).inv))
    (h₂ : IsCohomologyMap (RingHom.id A) g.left (by simp) β n
      (m₂ ≫ (cohomologyRestriction Y D.sheaf n).inv))
    {j : Y.left ⟶ Y.left} {r : D.torsor.left ⟶ D.torsor.left}
    (hj : j = (g ≫ f).left) (hr : r = s ≫ t)
    (hjbase : j ≫ Y.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)))
    (wr : r ≫ D.projection.left = D.projection.left ≫ j)
    (δ : D.sheaf ⟶ (Scheme.Modules.pushforward j).obj D.sheaf)
    (hδ : D.IsPullbackMap D j r wr δ)
    (h₃ : IsCohomologyMap (RingHom.id A) j hjbase δ n
      (m₃ ≫ (cohomologyRestriction Y D.sheaf n).inv)) :
    m₁ ≫ m₂ = m₃ := by
  subst j
  subst r
  have hcomp := covariancePullback_comp hα hβ
  have heq := covariancePullback_unique D D (g ≫ f).left (s ≫ t) wr hcomp hδ
  subst δ
  exact cohomologyMap_over_comp f g α β n h₁ h₂ h₃


private theorem covarianceCohomologyMap_identity
    {A : Type u} [CommRing A] {Y : SchemeOverRing A} (D : CovarianceData Y)
    {f : Y.left ⟶ Y.left} {t : D.torsor.left ⟶ D.torsor.left}
    (hf : f = 𝟙 _) (ht : t = 𝟙 _)
    (hfbase : f ≫ Y.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)))
    (w : t ≫ D.projection.left = D.projection.left ≫ f)
    (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D.sheaf)
    (hα : D.IsPullbackMap D f t w α) (n : ℕ)
    (m : (cohomology Y n).obj D.sheaf ⟶ (cohomology Y n).obj D.sheaf)
    (hm : IsCohomologyMap (RingHom.id A) f hfbase α n
      (m ≫ (cohomologyRestriction Y D.sheaf n).inv)) :
    m = 𝟙 _ := by
  subst f
  subst t
  let β := 𝟙 D.sheaf ≫ (Scheme.Modules.pushforwardId Y.left).inv.app D.sheaf
  have hβ : D.IsPullbackMap D (𝟙 Y.left) (𝟙 D.torsor.left) w β := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    let q := D.projection.left
    let z : Γ(D.torsor.left, q ⁻¹ᵁ U) := D.inclusion.app U x
    change z = (D.pullFunctions D (𝟙 Y.left) (𝟙 D.torsor.left) w).app U z
    rw [pullFunctions_app]
    change z = (𝟙 D.torsor.left : D.torsor.left ⟶ D.torsor.left).appLE
      (q ⁻¹ᵁ U) ((q ≫ 𝟙 Y.left) ⁻¹ᵁ U) _ z
    erw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
    rfl
  have heq := covariancePullback_unique D D (𝟙 Y.left) (𝟙 D.torsor.left) w hβ hα
  subst α
  have he := isCohomologyMap_identity Y hfbase (𝟙 D.sheaf) n _ hm
  rw [CategoryTheory.Functor.map_id (cohomology Y n) D.sheaf] at he
  exact (cancel_mono (cohomologyRestriction Y D.sheaf n).inv).mp he

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
  (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme)
  (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
  (R : TestAlgebra k) (n : ℕ)

private abbrev ExtendedFlagCohomology :=
  (cohomology ((extendScheme R).obj Q.scheme) n).obj ((flagLineData Q p χ h).extend R).sheaf

/-- Geometric translation on the derived cohomology of the flag over a test algebra. -/
def flagCohomologyTranslate (g : GroupPoints G.val R) :
    ExtendedFlagCohomology Q p χ h R n ⟶ ExtendedFlagCohomology Q p χ h R n :=
  (flagTranslationCohomologyMap_at R Q p χ h a ha g n).choose_spec.choose_spec.choose

theorem flagCohomologyTranslate_induced (g : GroupPoints G.val R) :
    let D := (flagLineData Q p χ h).extend R
    let Y := (extendScheme R).obj Q.scheme
    let f := pointTranslation a.smul R g⁻¹
    let t := pointTranslation μ[G.val.X] R g⁻¹
    ∃ (w : t ≫ D.projection.left = D.projection.left ≫ f)
      (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D.sheaf),
      D.IsPullbackMap D f t w α ∧
      IsCohomologyMap (RingHom.id R) f (pointTranslation_over a.smul R g⁻¹) α n
        (flagCohomologyTranslate Q p χ h a ha R n g ≫ (cohomologyRestriction Y D.sheaf n).inv) :=
  let b := flagTranslationCohomologyMap_at R Q p χ h a ha g n
  ⟨b.choose, b.choose_spec.choose, b.choose_spec.choose_spec.choose_spec⟩

/-- Pullback by the inverse translates gives the left-action multiplication
law on cohomology over each test algebra. -/
theorem flagCohomologyTranslate_mul (g g' : GroupPoints G.val R) :
    flagCohomologyTranslate Q p χ h a ha R n (g * g') =
      flagCohomologyTranslate Q p χ h a ha R n g' ≫ flagCohomologyTranslate Q p χ h a ha R n g := by
  let Y := (extendScheme R).obj Q.scheme
  let D := (flagLineData Q p χ h).extend R
  let F (b : GroupPoints G.val R) : Y ⟶ Y :=
    Over.homMk (pointTranslation a.smul R b⁻¹) (pointTranslation_structure R a.smul b⁻¹)
  let T (b : GroupPoints G.val R) := pointTranslation μ[G.val.X] R b⁻¹
  let M := flagCohomologyTranslate Q p χ h a ha R n
  have hf : (F (g * g')).left = (F g ≫ F g').left := by
    let : ModObj G.val.X Q.scheme := a
    change pointTranslation γ[G.val.X, Q.scheme] R (g * g')⁻¹ =
      pointTranslation γ[G.val.X, Q.scheme] R g⁻¹ ≫
        pointTranslation γ[G.val.X, Q.scheme] R g'⁻¹
    rw [pointTranslation_comp, mul_inv_rev]
  have ht : T (g * g') = T g ≫ T g' := by
    change pointTranslation γ[G.val.X, G.val.X] R (g * g')⁻¹ =
      pointTranslation γ[G.val.X, G.val.X] R g⁻¹ ≫ pointTranslation γ[G.val.X, G.val.X] R g'⁻¹
    rw [pointTranslation_comp, mul_inv_rev]
  obtain ⟨w, α, hα, hg⟩ := flagCohomologyTranslate_induced Q p χ h a ha R n g
  obtain ⟨w', β, hβ, hg'⟩ := flagCohomologyTranslate_induced Q p χ h a ha R n g'
  obtain ⟨wg, δ, hδ, hgprod⟩ := flagCohomologyTranslate_induced Q p χ h a ha R n (g * g')
  change M (g * g') = M g' ≫ M g
  symm
  exact covarianceCohomologyMaps_comp D (F g') (F g) (T g') (T g)
    w' w β α n hβ hα hg' hg hf ht _ wg δ hδ hgprod

set_option maxHeartbeats 600000 in
/-- The identity point induces the identity cohomology endomorphism. -/
theorem flagCohomologyTranslate_one :
    flagCohomologyTranslate Q p χ h a ha R n (1 : GroupPoints G.val R) = 𝟙 _ := by
  let b : GroupPoints G.val R := 1
  let Y := (extendScheme R).obj Q.scheme
  let D := (flagLineData Q p χ h).extend R
  obtain ⟨w, α, hα, hm⟩ := flagCohomologyTranslate_induced Q p χ h a ha R n b
  let : ModObj G.val.X Q.scheme := a
  have hf : pointTranslation a.smul R b⁻¹ = 𝟙 _ := by
    rw [show b⁻¹ = (1 : GroupPoints G.val R) from inv_one]
    exact pointTranslation_one (H := G.val.X) (X := Q.scheme) R
  have ht : pointTranslation μ[G.val.X] R b⁻¹ = 𝟙 _ := by
    rw [show b⁻¹ = (1 : GroupPoints G.val R) from inv_one]
    exact pointTranslation_one (H := G.val.X) (X := G.val.X) R
  exact covarianceCohomologyMap_identity (Y := Y) D hf ht
    (pointTranslation_over a.smul R b⁻¹) w α hα n
    (flagCohomologyTranslate Q p χ h a ha R n b) hm

/-- Each test algebra has a linear action on its flag cohomology, given by
the cohomology endomorphisms of inverse translation. -/
def flagCohomologyPointAction :
    GroupPoints G.val R →* Module.End R (ExtendedFlagCohomology Q p χ h R n) where
  toFun g := (flagCohomologyTranslate Q p χ h a ha R n g).hom
  map_one' := congrArg ModuleCat.Hom.hom (flagCohomologyTranslate_one Q p χ h a ha R n)
  map_mul' g g' := congrArg ModuleCat.Hom.hom (flagCohomologyTranslate_mul Q p χ h a ha R n g g')

end TranslationGroupLaw

/-- Inverse translations give the prescribed action over each test algebra. -/
theorem flagTranslationCohomologyMap.{u} : FlagTranslationCohomologyMap.{u} := by
  intro k _ G P Q p χ h a ha R n
  refine ⟨flagCohomologyPointAction Q p χ h a ha R n, fun g => ?_⟩
  exact flagCohomologyTranslate_induced Q p χ h a ha R n g

section DerivedFlagCohomology

open scoped ChangeOfRings TensorProduct

private theorem tupleOpen_isAffine_of_finite_intersections
    {X : Scheme.{u}} {I : Type u} [Preorder I] (U : I → X.Opens)
    (hU : ∀ s : Finset I, s.Nonempty → IsAffineOpen (⨅ i ∈ (s : Set I), U i))
    {n : ℕ} (e : Fin (n + 1) ↪o I) : IsAffineOpen (tupleOpen U e) := by
  classical
  let s := Finset.univ.image e
  have hs : s.Nonempty := ⟨e 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have he : tupleOpen U e = ⨅ i ∈ (s : Set I), U i := by
    apply le_antisymm
    · refine le_iInf fun i => le_iInf fun hi => ?_
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact iInf_le _ j
    · refine le_iInf fun j => ?_
      exact iInf_le_of_le (e j) (iInf_le _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  rw [he]
  exact hU s hs

private theorem intersectionAcyclic_of_isAffine
    {A : Type u} [CommRing A] {X : SchemeOverRing A}
    {I : Type u} [Preorder I] (U : I → X.left.Opens)
    (hU : ∀ {n : ℕ} (e : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U e))
    (F : X.left.Modules) (hF : F.IsQuasicoherent) :
    LinearAlgebraicGroups.Specs.OrderedCechComparison.IntersectionAcyclic U F := by
  letI : F.IsQuasicoherent := hF
  intro n e q hq
  exact LinearAlgebraicGroups.Cohomology.isZero_rightDerived_evaluation_of_isAffineOpen
    (hU e) F q hq

/-- Affine intersections are acyclic for quasi-coherent coefficients, so the
ordered Čech comparison applies to every finite affine cover. -/
theorem affineCechComparison.{u} : AffineCechComparison.{u} := by
  intro A _ X I _ _ U hU hUi n
  obtain ⟨e, _, natural, _⟩ := LinearAlgebraicGroups.OrderedCechComparison.orderedCechComparison.{u}
  let h (F : X.left.Modules) (hF : F.IsQuasicoherent) :=
    intersectionAcyclic_of_isAffine U (tupleOpen_isAffine_of_finite_intersections U hUi) F hF
  refine ⟨fun F hF => e X U hU F (h F hF) n, ?_⟩
  intro F F' hF hF' f
  exact natural X U hU f (h F hF) (h F' hF') n

private theorem exists_associatedBundle
    {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul) :
    Nonempty (AssociatedBundle Q a p χ) := by
  obtain ⟨D, d, φ, _, _, hφ, _, _⟩ :=
    LinearAlgebraicGroups.FlagLineBundle.borelCharacterLine p χ
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_hopfSpec.mpr G.property.1
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let q := (ff.preimage (d.hom ≫ P.negative.inclusion ≫ e.inv)).unop
  have hq : (specGroupMap q) ≫ e.hom =
      d.hom ≫ P.negative.inclusion := by
    have h : specGroupMap q =
        d.hom ≫ P.negative.inclusion ≫ e.inv := ff.map_preimage _
    simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨_, _, L, _⟩ :=
    LinearAlgebraicGroups.FlagLineBundle.flagLineBundleAndSections
      k G P p χ Q a ha A.unop D e d q φ hq hφ
  exact ⟨L⟩

/-- Every cohomology group of the character line bundle is finite dimensional,
and the finite affine cover gives a common upper bound on its degrees. -/
theorem flagCohomologyFinite.{u} : FlagCohomologyFinite.{u} := by
  intro k _ G P Q p χ h
  obtain ⟨_, hproper, _, V, hv, hm, hf, a, j, hj, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  letI : AddCommGroup V := hv
  letI : Module k V := hm
  letI : Module.Finite k V := hf
  letI : IsClosedImmersion j.left := hj
  obtain ⟨L⟩ := exists_associatedBundle Q p χ a ha
  obtain ⟨hqc, hl, _⟩ := flagLineSheafIdentification Q p χ h L
  choose U hU e using hl
  have cover : IsOpenCover U := by
    apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hU y⟩
  refine ⟨fun n => ?_, cohomologyBound_of_affineCech affineCechComparison Q.scheme
    (finiteAffineCover Q.scheme hproper) (flagLineSheaf Q p χ h) hqc⟩
  exact LinearAlgebraicGroups.ProjectiveFiniteness.projectiveCohomologyFiniteness_of_local_rank_one
    j (flagLineSheaf Q p χ h) U cover (fun y => (e y).some.symm) n

end DerivedFlagCohomology

section DerivedBaseChange

open scoped TensorProduct ChangeOfRings
open private restrictCohomologyIso from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 1000000 in
private theorem cech_homology_adjunction {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    {C : CochainComplex (ModuleCat.{u} k) ℕ} {D : CochainComplex (ModuleCat.{u} R) ℕ}
    (e : ((extendToAlgebra (k := k) (K := R)).mapHomologicalComplex (.up ℕ)).obj C ⟶ D)
    (t : C ⟶ ((ModuleCat.restrictScalars.{u} (algebraMap k R)).mapHomologicalComplex (.up ℕ)).obj D)
    (ht : ∀ i, t.f i = (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ (e.f i))
    (n : ℕ) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _
        ((extendCohomologyIso C n).hom ≫ HomologicalComplex.homologyMap e n) =
      HomologicalComplex.homologyMap t n ≫ (restrictCohomologyIso (algebraMap k R) D n).inv := by
  let E := extendToAlgebra (k := k) (K := R)
  let S := ModuleCat.restrictScalars.{u} (algebraMap k R)
  let A := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  let T := C.sc n
  let U := D.sc n
  let e' := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map e
  let t' := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℕ) n).map t
  have hm : (T.mapNatTrans A.unit) ≫ (S.mapShortComplex).map e' = t' := by
    ext : 1
    all_goals exact (A.homEquiv_unit _ _ _).symm.trans (ht _).symm
  change A.homEquiv _ _ ((T.mapHomologyIso E).inv ≫ ShortComplex.homologyMap e') =
    ShortComplex.homologyMap t' ≫ (U.mapHomologyIso S).hom
  rw [← hm, ShortComplex.homologyMap_comp, Category.assoc,
    ShortComplex.mapHomologyIso_hom_naturality, ShortComplex.homologyMap_mapNatTrans]
  rw [A.homEquiv_unit, Functor.map_comp]
  let L := T.homologyData.left
  let M := (L.map E).map S
  let N := L.map (E ⋙ S)
  have hMN : M.homologyIso.hom = N.homologyIso.hom := by
    apply (cancel_epi (T.map (E ⋙ S)).homologyπ).mp
    erw [M.homologyπ_comp_homologyIso_hom, N.homologyπ_comp_homologyIso_hom]
    have hc : M.cyclesIso.hom = N.cyclesIso.hom := by
      apply (cancel_mono N.i).mp
      exact M.cyclesIso_hom_comp_i.trans N.cyclesIso_hom_comp_i.symm
    rw [hc]
    rfl
  have h := congrArg Iso.hom ((L.map E).mapHomologyIso_eq S)
  change ((T.map E).mapHomologyIso S).hom = M.homologyIso.hom ≫ S.map (T.mapHomologyIso E).inv at h
  rw [hMN] at h
  rw [shortComplex_mapHomologyIso_id]
  simp only [Category.assoc]
  erw [h]
  change A.unit.app T.homology ≫ S.map (T.mapHomologyIso E).inv ≫
      S.map (ShortComplex.homologyMap e') =
    A.unit.app T.homology ≫ (T.mapHomologyIso (E ⋙ S)).inv ≫
      (T.mapHomologyIso (E ⋙ S)).hom ≫ S.map (T.mapHomologyIso E).inv ≫
      S.map (ShortComplex.homologyMap e')
  rw [Iso.inv_hom_id_assoc]

private theorem flatCohomologyMap_bridge
    {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}
    (φ : A →+* B) (f : Y.left ⟶ X.left) [Flat f]
    (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : X.left.Modules} {F' : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj F') (n : ℕ) :
    ∃ m, IsCohomologyMap (X := X) (Y := Y) φ f hf α n m := by
  obtain ⟨m, hm, _⟩ := LinearAlgebraicGroups.FlatCohomology.flatCohomologyMap φ f hf α n
  refine ⟨m, fun I J => ⟨(hm I J).1, ?_⟩⟩
  intro l hl
  exact (hm I J).2 l hl


private theorem cechScalarComparison
    {k : Type u} [Field k] {X : SchemeOver k} (R : TestAlgebra k) (D : CovarianceData X)
    (α : D.sheaf ⟶ (Scheme.Modules.pushforward (extensionProjection R X)).obj (D.extend R).sheaf)
    (hα : D.IsPullbackMap (D.extend R) (extensionProjection R X) (extensionProjection R D.torsor)
      (extensionProjection_natural R D.projection).symm α)
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)
    (ht : ∀ {n : ℕ} (e : Fin (n + 1) ↪o I), IsAffineOpen (D.projection.left ⁻¹ᵁ tupleOpen U e))
    (ho : ∀ {n : ℕ} (e : Fin (n + 1) ↪o I), IsAffineOpen (D.overlapProjection.left ⁻¹ᵁ tupleOpen U e))
    (n : ℕ) :
    let C := Specs.OrderedCechComparison.SheafCech U D.sheaf
    let D' := Specs.OrderedCechComparison.SheafCech (Specs.OrderedCechComparison.pullbackCover (extensionProjection R X) U) (D.extend R).sheaf
    let iso := extendCohomologyIso C n ≪≫
      HomologicalComplex.homologyMapIso (covarianceCechExtendIso R D α hα U ht ho) n
    (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ iso.hom =
      HomologicalComplex.homologyMap
          (Specs.OrderedCechComparison.cechPullback (algebraMap k R) (extensionProjection R X) (extensionProjection_over R X) U α) n ≫
        (Specs.OrderedCechComparison.restrictCohomologyIso (algebraMap k R) D' n).inv := by
  dsimp only [Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  refine cech_homology_adjunction _ _ (fun i => ?_) n
  apply ModuleCat.hom_ext
  ext x : 1
  funext e
  change (Specs.OrderedCechComparison.cechPullback (algebraMap k R) (extensionProjection R X)
      (extensionProjection_over R X) U α).f i x e =
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _
      ((covarianceCechExtendIso R D α hα U ht ho).hom.f i) x) e
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, Specs.OrderedCechComparison.cechPullback_apply]
  refine Eq.trans ?_ (covarianceCechExtendIso_one_tmul R D α hα U ht ho i e x).symm
  let F := (D.extend R).sheaf
  let a := (Specs.OrderedCechComparison.pullbackToIntersection (extensionProjection R X) U e).op
  let b := eqToHom (congrArg op (preimage_tupleOpen (extensionProjection R X) U e))
  have hab : a = b := Subsingleton.elim _ _
  change F.presheaf.map a _ = F.presheaf.map b _
  rw [hab]
  rfl

/-- The affine computation on each Čech intersection induces the derived
scalar extension on covariant coefficients. -/
private theorem covarianceDerivedBaseChange
    {k : Type u} [Field k] {X : SchemeOver k} (R : TestAlgebra k) (D : CovarianceData X)
    [IsAffineHom D.projection.left] [IsAffineHom D.overlapProjection.left]
    (hD : D.sheaf.IsQuasicoherent) (hD' : (D.extend R).sheaf.IsQuasicoherent)
    (hX : HasFiniteAffineCover X)
    (α : D.sheaf ⟶ (Scheme.Modules.pushforward (extensionProjection R X)).obj (D.extend R).sheaf)
    (hα : D.IsPullbackMap (D.extend R) (extensionProjection R X) (extensionProjection R D.torsor)
      (extensionProjection_natural R D.projection).symm α) (n : ℕ) :
    ∃ b : (extendToAlgebra (k := k) (K := R)).obj ((cohomology X n).obj D.sheaf) ≅
          (cohomology ((extendScheme R).obj X) n).obj (D.extend R).sheaf,
      IsCohomologyMap (algebraMap k R) (extensionProjection R X) (extensionProjection_over R X)
        α n ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ b.hom) := by
  classical
  let Y := (extendScheme R).obj X
  let f := extensionProjection R X
  let hf := extensionProjection_over R X
  let E := extendToAlgebra (k := k) (K := R)
  let S := ModuleCat.restrictScalars.{u} (algebraMap k R)
  let A := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  let : Flat f := LinearAlgebraicGroups.FlatCohomology.flatScalarExtension k R X
  let : IsAffineHom f := MorphismProperty.pullback_fst _ _ inferInstance
  obtain ⟨Idx, inst, W, hW, hAff⟩ := hX
  let : Fintype Idx := inst
  let : LinearOrder Idx := LinearOrder.lift' (Fintype.equivFin Idx) (Fintype.equivFin Idx).injective
  let V := Specs.OrderedCechComparison.pullbackCover f W
  have hV : (⨆ i, V i) = ⊤ := f.iSup_preimage_eq_top hW
  have hAW {n : ℕ} (e : Fin (n + 1) ↪o Idx) : IsAffineOpen (tupleOpen W e) :=
    tupleOpen_isAffine_of_finite_intersections W hAff e
  have hAV {n : ℕ} (e : Fin (n + 1) ↪o Idx) : IsAffineOpen (tupleOpen V e) := by
    rw [← preimage_tupleOpen f W e]
    exact (hAW e).preimage f
  let p := intersectionAcyclic_of_isAffine W hAW D.sheaf hD
  let q := intersectionAcyclic_of_isAffine V hAV (D.extend R).sheaf hD'
  obtain ⟨c, _, _, natural⟩ := LinearAlgebraicGroups.OrderedCechComparison.orderedCechComparison.{u}
  let ht {n : ℕ} (e : Fin (n + 1) ↪o Idx) := (hAW e).preimage D.projection.left
  let ho {n : ℕ} (e : Fin (n + 1) ↪o Idx) := (hAW e).preimage D.overlapProjection.left
  let cX := c X W hW D.sheaf p n
  let cY := c Y V hV (D.extend R).sheaf q n
  let cH := extendCohomologyIso (Specs.OrderedCechComparison.SheafCech W D.sheaf) n ≪≫
    HomologicalComplex.homologyMapIso (covarianceCechExtendIso R D α hα W ht ho) n
  let b := E.mapIso cX ≪≫ cH ≪≫ cY.symm
  obtain ⟨m, hm⟩ := flatCohomologyMap_bridge (algebraMap k R) f hf α n
  let JX := injectiveResolution D.sheaf
  let JY := injectiveResolution (D.extend R).sheaf
  obtain ⟨l, hl⟩ := (hm JX JY).1
  have h := natural (X := X) (Y := Y) W hW (algebraMap k R) f hf α p q JX JY l hl n
  have hmap : m = Specs.OrderedCechComparison.derivedMapOfLift (algebraMap k R) f hf JX JY l n :=
    (hm JX JY).2 l hl
  change Specs.OrderedCechComparison.derivedMapOfLift (algebraMap k R) f hf JX JY l n ≫ S.map cY.hom = _ at h
  rw [← hmap] at h
  refine ⟨b, ?_⟩
  change IsCohomologyMap (algebraMap k R) f hf α n (A.homEquiv _ _ b.hom)
  suffices H : A.homEquiv _ _ b.hom = m by
    exact H.symm ▸ hm
  apply (cancel_mono (S.map cY.hom)).mp
  rw [h]
  change A.homEquiv _ _ (E.map cX.hom ≫ cH.hom ≫ cY.inv) ≫ S.map cY.hom = _
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right, Category.assoc, Category.assoc,
    ← S.map_comp, cY.inv_hom_id]
  erw [S.map_id, Category.comp_id]
  exact congrArg (cX.hom ≫ ·) (cechScalarComparison R D α hα W ht ho n)

end DerivedBaseChange

section ScalarExtensionCoefficients

universe u

open scoped TensorProduct ChangeOfRings
open private affineSectionRestriction affineSections restrictRing
  from LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

section CoefficientGenerators

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private def sectionGenerator {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    Γ(X, U) →ₗ[Γ(X, U)] Γ(M, U) := LinearMap.toSpanSingleton _ _ s

private abbrev restrictSection {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (s : Γ(M, U)) : Γ(M, V) := M.presheaf.map (homOfLE h).op s

private theorem sectionGenerator_restrict {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (s : Γ(M, U)) (a : Γ(X, U)) :
    restrictSection M h (sectionGenerator M U s a) =
      sectionGenerator M V (restrictSection M h s) (restrictRing h a) :=
  M.val.map_smul (homOfLE h).op a s

private def equivKernelOnOpen {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    (kernel f).val.obj (op U) ≅ ModuleCat.of (Γ(X, U)) (LinearMap.ker (f.val.app (op U)).hom) := by
  let ev := SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)
  let : ev.Additive := ⟨by intros; ext x; rfl⟩
  exact PreservesKernel.iso ev f ≪≫ ModuleCat.kernelIsoKer _

private theorem equivKernelOnOpen_apply {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (s : Γ((kernel f), U)) :
    ((equivKernelOnOpen f U).hom s).1 = (kernel.ι f).app U s := by
  let ev := SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)
  let : ev.Additive := ⟨by intros; ext x; rfl⟩
  have w : (equivKernelOnOpen f U).hom ≫
      ModuleCat.ofHom (R := Γ(X, U)) ((f.val.app (op U)).hom.ker.subtype) =
      ev.map (kernel.ι f) := by
    dsimp only [equivKernelOnOpen, Iso.trans_hom]
    rw [Category.assoc]
    change (PreservesKernel.iso ev f).hom ≫ (ModuleCat.kernelIsoKer (ev.map f)).hom ≫
      ModuleCat.ofHom (ev.map f).hom.ker.subtype = ev.map (kernel.ι f)
    rw [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom w) s

/-- If two coefficient modules localize on a principal open, then the
sections of their sheaf kernel localize on that open as well. -/
private theorem isLocalizedModule_kernel_restrict {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    (hM : IsLocalizedModule.Away r (affineSectionRestriction M (X.basicOpen_le r)))
    (hN : IsLocalizedModule.Away r (affineSectionRestriction N (X.basicOpen_le r))) :
    IsLocalizedModule.Away r (affineSectionRestriction (kernel f) (X.basicOpen_le r)) := by
  let V := X.basicOpen r
  let h : V ≤ U := X.basicOpen_le r
  let S := Submonoid.powers r
  let A := Γ(X, U)
  let B := Γ(X, V)
  letI : Algebra A B := (restrictRing h).toAlgebra
  letI : IsLocalization S B := by
    exact hU.isLocalization_basicOpen r
  let m := affineSectionRestriction M h
  let n := affineSectionRestriction N h
  let K := kernel f
  let i := kernel.ι f
  let φ : Γ(M, U) →ₗ[A] Γ(N, U) := (f.val.app (op U)).hom
  let ψ : affineSections M h →ₗ[A] affineSections N h := (ModuleCat.restrictScalars (restrictRing h)).map (f.val.app (op V)) |>.hom
  have w : IsLocalizedModule.map S m n φ = ψ := by
    apply IsLocalizedModule.ext S m (IsLocalizedModule.map_units n)
    ext x : 1
    rw [LinearMap.comp_apply, IsLocalizedModule.map_apply, LinearMap.comp_apply]
    exact (PresheafOfModules.naturality_apply f.val (homOfLE h).op x).symm
  let e := (equivKernelOnOpen f U).toLinearEquiv
  let eq : ψ.ker = (IsLocalizedModule.map S m n φ).ker := congrArg LinearMap.ker w.symm
  letI : Module B (affineSections M h) := (M.val.obj (op V)).isModule
  letI : IsScalarTower A B (affineSections M h) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module B (affineSections N h) := (N.val.obj (op V)).isModule
  letI : IsScalarTower A B (affineSections N h) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e' := ((ModuleCat.restrictScalars (restrictRing h)).mapIso (equivKernelOnOpen f V)).toLinearEquiv
  let eV : affineSections K h ≃ₗ[A] (IsLocalizedModule.map S m n φ).ker :=
    e'.trans (LinearEquiv.ofEq _ _ eq)
  have loc := LinearMap.toKerLocalized_isLocalizedModule B S m n φ
  have hh := IsLocalizedModule.of_linearEquiv_right S (LinearMap.toKerIsLocalized S m n φ) e
  have hh' := IsLocalizedModule.of_linearEquiv S
    ((LinearMap.toKerIsLocalized S m n φ).comp e.toLinearMap) eV.symm
  have he : affineSectionRestriction K h = eV.symm.toLinearMap.comp
      ((LinearMap.toKerIsLocalized S m n φ).comp e.toLinearMap) := by
    apply LinearMap.ext
    intro x
    apply eV.injective
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    change ((equivKernelOnOpen f V).hom (restrictSection K h x)).1 =
      m (((equivKernelOnOpen f U).hom x).1)
    rw [equivKernelOnOpen_apply, equivKernelOnOpen_apply]
    exact PresheafOfModules.naturality_apply i.val (homOfLE h).op x
  exact he.symm ▸ hh'

private theorem structureModule_isQuasicoherent (X : Scheme.{u}) : (structureModule X).IsQuasicoherent :=
  quasicoherent_of_unit_on_cover (structureModule X) (fun _ : PUnit.{u + 1} => ⊤)
    (by simp [IsOpenCover]) (fun _ => Iso.refl _)

private theorem covarianceGenerator_basicOpen {A : Type u} [CommRing A] {X : SchemeOverRing A}
    (D : CovarianceData X) [IsAffineHom D.projection.left] [IsAffineHom D.overlapProjection.left]
    {U : X.left.Opens} (hU : IsAffineOpen U) (s : Γ(D.sheaf, U))
    (hs : Function.Bijective (sectionGenerator D.sheaf U s)) (r : Γ(X.left, U)) :
    Function.Bijective (sectionGenerator D.sheaf (X.left.basicOpen r)
      (restrictSection D.sheaf (X.left.basicOpen_le r) s)) := by
  let V := X.left.basicOpen r
  let h : V ≤ U := X.left.basicOpen_le r
  let S := Submonoid.powers r
  let A := Γ(X.left, U)
  let B := Γ(X.left, V)
  letI : Algebra A B := (restrictRing h).toAlgebra
  letI : IsLocalization S B := by
    exact hU.isLocalization_basicOpen r
  let : (structureModule D.torsor.left).IsQuasicoherent := structureModule_isQuasicoherent _
  let : (structureModule D.overlap.left).IsQuasicoherent := structureModule_isQuasicoherent _
  have kLoc : IsLocalizedModule S (affineSectionRestriction D.sheaf h) :=
    isLocalizedModule_kernel_restrict D.covariance hU r
      (LinearAlgebraicGroups.ProjectiveFiniteness.isLocalizedModule_pushforward_affineSectionRestriction
        D.projection.left (structureModule D.torsor.left) hU r)
      (LinearAlgebraicGroups.ProjectiveFiniteness.isLocalizedModule_pushforward_affineSectionRestriction
        D.overlapProjection.left (structureModule D.overlap.left) hU r)
  let e := LinearEquiv.ofBijective (sectionGenerator D.sheaf U s) hs
  have kLoc' := IsLocalizedModule.of_linearEquiv_right S (affineSectionRestriction D.sheaf h) e
  let ringLoc : IsLocalizedModule S (Algebra.linearMap A B) := inferInstance
  let b := IsLocalizedModule.linearEquiv S (Algebra.linearMap A B)
    ((affineSectionRestriction D.sheaf h).comp e.toLinearMap)
  let g : B →ₗ[A] affineSections D.sheaf h := {
    toFun := sectionGenerator D.sheaf V (restrictSection D.sheaf h s)
    map_add' := fun a b => map_add (sectionGenerator D.sheaf V (restrictSection D.sheaf h s)) a b
    map_smul' := fun a b => by
      change ((restrictRing h a * b) • restrictSection D.sheaf h s : Γ(D.sheaf, V)) =
        restrictRing h a • (b • restrictSection D.sheaf h s)
      exact mul_smul _ _ _ }
  have hb : g = b.toLinearMap := by
    apply IsLocalizedModule.ext S (Algebra.linearMap A B) (IsLocalizedModule.map_units
      ((affineSectionRestriction D.sheaf h).comp e.toLinearMap))
    apply LinearMap.ext
    intro t
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      IsLocalizedModule.linearEquiv_apply]
    exact (sectionGenerator_restrict D.sheaf h s t).symm
  have hfun : (fun t : B => sectionGenerator D.sheaf V (restrictSection D.sheaf h s) t) = ⇑b := by
    funext t
    exact DFunLike.congr_fun hb t
  change Function.Bijective (fun t : B => sectionGenerator D.sheaf V (restrictSection D.sheaf h s) t)
  rw [hfun]
  exact b.bijective

private def sectionGeneratorOver {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ F.over U :=
  (F.over U).unitHomEquiv.symm <| PresheafOfModules.sectionsMk
    (fun V => F.presheaf.map V.unop.hom.op s) (by
      intro V W j
      change (F.presheaf.map V.unop.hom.op ≫ F.presheaf.map j.unop.left.op) s =
        F.presheaf.map W.unop.hom.op s
      rw [← F.presheaf.map_comp, ← op_comp, Over.w j.unop])

private theorem moduleSheaf_isIso_of_underlying {X : Scheme.{u}} {F G : X.Modules}
    (m : F ⟶ G) (hm : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map m)) : IsIso m := by
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app).mpr
  intro U
  exact Functor.map_isIso (TopCat.Sheaf.forget Ab X ⋙ (evaluation _ _).obj (op U))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map m)

private theorem sectionGeneratorOver_isIso {A : Type u} [CommRing A] {X : SchemeOverRing A}
    (D : CovarianceData X) [IsAffineHom D.projection.left] [IsAffineHom D.overlapProjection.left]
    {U : X.left.Opens} (hU : IsAffineOpen U) (s : Γ(D.sheaf, U))
    (hs : Function.Bijective (sectionGenerator D.sheaf U s)) :
    IsIso (sectionGeneratorOver D.sheaf U s) := by
  let E := (Scheme.Modules.overEquiv U).functor
  let S := SheafOfModules.toSheaf U.toScheme.ringCatSheaf
  let m := (E ⋙ S).map (sectionGeneratorOver D.sheaf U s)
  have hm : IsIso m := by
    let : IsAffine U.toScheme := hU
    apply TopCat.Sheaf.isIso_iff_isIso_basis (φ := m) (isBasis_basicOpen U.toScheme)
    intro r
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    let V := U.toScheme.basicOpen r
    let W := U.ι ''ᵁ V
    have eTop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U :=
      U.ι.image_top_eq_opensRange.trans (Scheme.Opens.opensRange_ι U)
    let h : W ≤ U := (U.ι.image_mono le_top).trans eTop.le
    let r₀ := (U.ι.appIso (⊤ : U.toScheme.Opens)).inv r
    let i := (eqToHom eTop.symm).op
    let r₁ := X.left.presheaf.map i r₀
    have hW : W = X.left.basicOpen r₁ := by
      change U.ι ''ᵁ U.toScheme.basicOpen r = X.left.basicOpen (X.left.presheaf.map i r₀)
      rw [Scheme.image_basicOpen]
      exact (X.left.basicOpen_res_eq r₀ i).symm
    have hgen (W' : X.left.Opens) (h' : W' ≤ U) (eq : W' = X.left.basicOpen r₁) :
        Function.Bijective (sectionGenerator D.sheaf W' (restrictSection D.sheaf h' s)) := by
      subst W'
      exact covarianceGenerator_basicOpen D hU s hs _
    change Function.Bijective (sectionGenerator D.sheaf W (restrictSection D.sheaf h s))
    exact hgen W h hW
  have hE : IsIso (E.map (sectionGeneratorOver D.sheaf U s)) :=
    moduleSheaf_isIso_of_underlying _ hm
  exact isIso_of_reflects_iso (sectionGeneratorOver D.sheaf U s) E

private theorem extendedSectionGenerator {k : Type u} [Field k] {X : SchemeOver k}
    (R : TestAlgebra k) (D : CovarianceData X)
    [IsAffineHom D.projection.left] [IsAffineHom D.overlapProjection.left]
    (α : D.sheaf ⟶ (Scheme.Modules.pushforward (extensionProjection R X)).obj (D.extend R).sheaf)
    (hα : D.IsPullbackMap (D.extend R) (extensionProjection R X) (extensionProjection R D.torsor)
      (extensionProjection_natural R D.projection).symm α)
    {U : X.left.Opens} (hU : IsAffineOpen U) (s : Γ(D.sheaf, U))
    (hs : Function.Bijective (sectionGenerator D.sheaf U s)) :
    Function.Bijective (sectionGenerator (D.extend R).sheaf (extensionProjection R X ⁻¹ᵁ U) (α.app U s)) := by
  let f := extensionProjection R X
  let V := f ⁻¹ᵁ U
  let h : localSections (structureModule X.left) U ⟶ localSections D.sheaf U :=
    (ModuleCat.restrictScalars (groundRingHomOpen X U)).map
      (ModuleCat.ofHom (sectionGenerator D.sheaf U s))
  have hh : IsIso h := (ConcreteCategory.isIso_iff_bijective _).mpr hs
  let E := extendToAlgebra (k := k) (K := R)
  let a := affineOpenRegularExtendIso R X U hU
  let b := localScalarIso R D α hα U (hU.preimage D.projection.left) (hU.preimage D.overlapProjection.left)
  let g : localSections (structureModule ((extendScheme R).obj X).left) V ⟶
      localSections (D.extend R).sheaf V :=
    (ModuleCat.restrictScalars (groundRingHomOpen ((extendScheme R).obj X) V)).map
      (ModuleCat.ofHom (sectionGenerator (D.extend R).sheaf V (α.app U s)))
  have w : a.hom ≫ g = E.map h ≫ b.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul]
    erw [affineOpenRegularExtendIso_tmul, localScalarIso_one_tmul]
    rw [map_one, one_mul]
    exact (Scheme.Modules.Hom.app_smul α (show Γ(X.left, U) from x) s).symm
  have hg : IsIso g := by
    rw [← isIso_comp_left_iff a.hom, w]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective g).mp hg

end CoefficientGenerators

section CoefficientStalks

open private moduleStalk moduleStalk_germ_smul moduleStalkAdjunction moduleStalk_map_forget
  pullbackStalk pushSky skyIso skyTo_stalk skyscraperModuleFunctor stalkSkyscraperHomEquiv
  from LinearAlgebraicGroups.Cohomology.FlatPullback
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem localGenerator_bijective {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (s : Γ(F, U)) (hs : IsIso (sectionGeneratorOver F U s))
    {V : X.Opens} (h : V ≤ U) :
    Function.Bijective (sectionGenerator F V (restrictSection F h s)) := by
  let ev := SheafOfModules.evaluation.{u} (X.ringCatSheaf.over U) (op (Over.mk (homOfLE h)))
  let f := ev.map (sectionGeneratorOver F U s)
  have hf : IsIso f := Functor.map_isIso ev _
  exact (ConcreteCategory.isIso_iff_bijective f).mp hf

private theorem stalkGenerator_bijective {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (s : Γ(F, U)) (hs : IsIso (sectionGeneratorOver F U s)) (x : X) (hx : x ∈ U) :
    letI := ((moduleStalk x).obj F).isModule
    Function.Bijective (LinearMap.toSpanSingleton (X.presheaf.stalk x) ((moduleStalk x).obj F)
      (F.presheaf.germ U x hx s)) := by
  letI := ((moduleStalk x).obj F).isModule
  let z : (moduleStalk x).obj F := F.presheaf.germ U x hx s
  have hmul (V : X.Opens) (hxV : x ∈ V) (le : V ≤ U) (a : Γ(X, V)) :
      X.presheaf.germ V x hxV a • z =
        F.presheaf.germ V x hxV (sectionGenerator F V (restrictSection F le s) a) := by
    have e : F.presheaf.germ V x hxV (restrictSection F le s) = z :=
      F.presheaf.germ_res_apply (homOfLE le) x hxV s
    rw [← e]
    exact (moduleStalk_germ_smul x F V hxV a _).symm
  constructor
  · intro r t he
    obtain ⟨V, hv, m, a, rfl⟩ := X.presheaf.exists_le_germ_eq r hx
    obtain ⟨W, hw, n, b, rfl⟩ := X.presheaf.exists_le_germ_eq t hx
    change (X.presheaf.germ V x m a : X.presheaf.stalk x) • z =
      (X.presheaf.germ W x n b : X.presheaf.stalk x) • z at he
    rw [hmul V m hv, hmul W n hw] at he
    obtain ⟨T, hxT, hTV, hTW, hT⟩ := F.presheaf.germ_eq x m n _ _ he
    let e : T ≤ U := hTV.le.trans hv
    have hV : restrictSection F hTV.le (restrictSection F hv s) = restrictSection F e s := by
      change (F.presheaf.map (homOfLE _).op ≫ F.presheaf.map (homOfLE _).op) s = _
      rw [← Functor.map_comp]
      rfl
    have hW : restrictSection F hTW.le (restrictSection F hw s) = restrictSection F e s := by
      change (F.presheaf.map (homOfLE _).op ≫ F.presheaf.map (homOfLE _).op) s = _
      rw [← Functor.map_comp]
      rfl
    have h₀ : restrictSection F hTV.le (sectionGenerator F V (restrictSection F hv s) a) =
        restrictSection F hTW.le (sectionGenerator F W (restrictSection F hw s) b) := hT
    rw [sectionGenerator_restrict, sectionGenerator_restrict, hV, hW] at h₀
    have hab := (localGenerator_bijective F U s hs e).1 h₀
    change X.presheaf.map hTV.op a = X.presheaf.map hTW.op b at hab
    have h' := congrArg (X.presheaf.germ T x hxT) hab
    simpa only [X.presheaf.germ_res_apply] using h'
  · intro t
    obtain ⟨V, hV, m, z, rfl⟩ := F.presheaf.exists_le_germ_eq t hx
    obtain ⟨a, ha⟩ := (localGenerator_bijective F U s hs hV).2 z
    exact ⟨X.presheaf.germ V x m a, (hmul V m hV a).trans (congrArg _ ha)⟩

private def stalkAdjointMap {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    {F : X.Modules} {G : Y.Modules} (α : F ⟶ (Scheme.Modules.pushforward f).obj G) :=
  (pullbackStalk f y).inv.app F ≫ (moduleStalk y).map
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm α)

private theorem stalkAdjointMap_tmul_germ {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    {F : X.Modules} {G : Y.Modules} (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (U : X.Opens) (hy : f y ∈ U) (s : Γ(F, U)) :
    stalkAdjointMap f y α ((1 : Y.presheaf.stalk y) ⊗ₜ[X.presheaf.stalk (f y),(f.stalkMap y).hom]
      (F.presheaf.germ U (f y) hy s)) = G.presheaf.germ (f ⁻¹ᵁ U) y hy (α.app U s) := by
  let f₁ := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := moduleStalkAdjunction y
  let c := moduleStalkAdjunction (f y)
  let d := ModuleCat.extendRestrictScalarsAdj (f.stalkMap y).hom
  let e := pushSky f y
  let L := f₁.comp b
  let R := (c.comp d).ofNatIsoRight e.symm
  let β := ((f₁.homEquiv F G).symm α)
  let x := (moduleStalk y).obj G
  let gm := (moduleStalk y).map β
  have hL : L.homEquiv F x gm = α ≫ (Scheme.Modules.pushforward f).map (b.unit.app G) := by
    dsimp only [L]
    rw [Adjunction.comp_homEquiv]
    change f₁.homEquiv F _ (b.homEquiv _ _ ((moduleStalk y).map β)) = _
    have hb := b.homEquiv_naturality_left β (𝟙 x)
    rw [Category.comp_id, b.homEquiv_id] at hb
    rw [hb, ← f₁.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  have hR : R.homEquiv F x (stalkAdjointMap f y α) = L.homEquiv F x gm := by
    change R.homEquiv F x ((L.leftAdjointUniq R).inv.app F ≫ gm) = _
    rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_unit,
      Functor.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app,
      ← Adjunction.homEquiv_unit]
  rw [hL] at hR
  have h : c.homEquiv F _ (d.homEquiv _ _ (stalkAdjointMap f y α)) =
      α ≫ (Scheme.Modules.pushforward f).map (b.unit.app G) ≫ e.hom.app x := by
    dsimp only [R] at hR
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hR
    change c.homEquiv F _ (d.homEquiv _ _ (stalkAdjointMap f y α)) ≫ e.inv.app x = _ at hR
    apply (cancel_mono (e.inv.app x)).mp
    refine hR.trans ?_
    simp only [Category.assoc, e.hom_inv_id_app]
    exact congrArg (α ≫ ·) (Category.comp_id ((Scheme.Modules.pushforward f).map (b.unit.app G))).symm
  have hh := congrArg (fun m => (skyIso (f y) _ U hy).hom (m.app U s)) h
  have hhom {Z : Scheme.{u}} (x : Z) : (moduleStalkAdjunction x).homEquiv = stalkSkyscraperHomEquiv x :=
    Adjunction.mkOfHomEquiv_homEquiv _
  have hx : (skyIso (f y) _ U hy).hom ((c.homEquiv F _
      (d.homEquiv _ _ (stalkAdjointMap f y α))).app U s) =
      d.homEquiv _ _ (stalkAdjointMap f y α) (F.presheaf.germ U (f y) hy s) :=
    by
      dsimp only [c]
      rw [hhom]
      exact skyTo_stalk (f y) F _ (d.homEquiv _ _ (stalkAdjointMap f y α)) U hy s
  rw [hx, ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at hh
  refine hh.trans ?_
  change (skyIso (f y) _ U hy).hom ((e.hom.app x).app U ((b.unit.app G).app (f ⁻¹ᵁ U) (α.app U s))) = _
  have he (z : Γ((skyscraperModuleFunctor y).obj x, f ⁻¹ᵁ U)) :
      (skyIso (f y) _ U hy).hom ((e.hom.app x).app U z) =
        (skyIso y x (f ⁻¹ᵁ U) hy).hom z := rfl
  rw [he, ← b.homEquiv_id]
  dsimp only [b]
  rw [hhom]
  exact skyTo_stalk y G x (𝟙 _) (f ⁻¹ᵁ U) hy (α.app U s)

private theorem isIso_adjoint_of_local_generators {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (h : ∀ y : Y, ∃ (U : X.Opens) (_ : f y ∈ U) (s : Γ(F, U)),
      IsIso (sectionGeneratorOver F U s) ∧
      IsIso (sectionGeneratorOver G (f ⁻¹ᵁ U) (α.app U s))) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm α) := by
  let m := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm α
  let S := SheafOfModules.toSheaf Y.ringCatSheaf
  apply moduleSheaf_isIso_of_underlying m
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (S.map m)).mpr
  intro y
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map m.mapPresheaf)
  rw [← moduleStalk_map_forget y]
  suffices hm : IsIso ((moduleStalk y).map m) by infer_instance
  have hm : IsIso (stalkAdjointMap f y α) := by
    obtain ⟨U, hx, s, hs, ht⟩ := h y
    let A := X.presheaf.stalk (f y)
    let B := Y.presheaf.stalk y
    let φ := (f.stalkMap y).hom
    let L := ModuleCat.extendScalars.{u,u,u} φ
    let F₀ : ModuleCat.{u} A := (moduleStalk (f y)).obj F
    let G₀ : ModuleCat.{u} B := (moduleStalk y).obj G
    let a : F₀ := F.presheaf.germ U (f y) hx s
    let z : G₀ := G.presheaf.germ (f ⁻¹ᵁ U) y hx (α.app U s)
    let e : ModuleCat.of A A ⟶ F₀ := ModuleCat.ofHom (Y := F₀) (LinearMap.toSpanSingleton A F₀ a)
    let d : ModuleCat.of B B ⟶ G₀ := ModuleCat.ofHom (Y := G₀) (LinearMap.toSpanSingleton B G₀ z)
    have he : IsIso e := (ConcreteCategory.isIso_iff_bijective _).mpr (stalkGenerator_bijective F U s hs _ hx)
    have hd : IsIso d := (ConcreteCategory.isIso_iff_bijective _).mpr (stalkGenerator_bijective G _ _ ht _ hx)
    letI : Algebra A B := φ.toAlgebra
    let q := (Algebra.TensorProduct.rid A B B).toLinearEquiv.toModuleIso
    let m := stalkAdjointMap f y α
    have w : L.map e ≫ m = q.hom ≫ d := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro r
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul]
      change m ((1 : B) ⊗ₜ[A,φ] (r • a)) =
        ((Algebra.TensorProduct.rid A B B) ((1 : B) ⊗ₜ[A] r)) • z
      rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
      have ht : (1 : B) ⊗ₜ[A] (r • a) = (φ r) • ((1 : B) ⊗ₜ[A] a) := by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rfl
      erw [ht]
      exact (m.hom.map_smul _ _).trans
        (congrArg (φ r • ·) (stalkAdjointMap_tmul_germ f y α U hx s))
    rw [← isIso_comp_left_iff (L.map e), w]
    infer_instance
  let : IsIso ((pullbackStalk f y).inv.app F ≫ (moduleStalk y).map m) := hm
  exact IsIso.of_isIso_comp_left ((pullbackStalk f y).inv.app F) ((moduleStalk y).map m)

end CoefficientStalks

section ExtendedFlagCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem extendedFlagCoefficientComparison
    {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) {a : ModObj G.val.X Q.scheme} (L : AssociatedBundle Q a p χ)
    (R : TestAlgebra k) :
    let X := Q.scheme
    let D := flagLineData Q p χ h
    let f := extensionProjection R X
    ∀ (α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj (D.extend R).sheaf),
      D.IsPullbackMap (D.extend R) f (extensionProjection R D.torsor)
        (extensionProjection_natural R D.projection).symm α →
      (D.extend R).sheaf.IsQuasicoherent ∧
      IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm α) := by
  intro X D f α hα
  classical
  let : IsAffineHom D.projection.left := flagTorsor_affine Q
  let : IsAffineHom D.overlapProjection.left := flagOverlap_affine Q
  let : IsAffineHom (D.extend R).projection.left := MorphismProperty.of_isPullback
    (extensionMap_isPullback R D.projection) inferInstance
  let : IsAffineHom (D.extend R).overlapProjection.left := MorphismProperty.of_isPullback
    (extensionMap_isPullback R D.overlapProjection) inferInstance
  let : IsAffineHom f := MorphismProperty.pullback_fst _ _ inferInstance
  have localData (x : X.left) : ∃ (U : X.left.Opens) (_ : x ∈ U)
      (s : Γ(D.sheaf, U)), IsIso (sectionGeneratorOver D.sheaf U s) ∧
        IsIso (sectionGeneratorOver (D.extend R).sheaf (f ⁻¹ᵁ U) (α.app U s)) := by
    obtain ⟨W, t, hx, ht, hlin⟩ := bundleChartsOnOpens L x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    let s : Γ(D.sheaf, U) := chartToCovariance h ht (homOfLE hUW) 1
    have hs : Function.Bijective (sectionGenerator D.sheaf U s) := by
      have e (r : Γ(X.left, U)) : sectionGenerator D.sheaf U s r =
          chartToCovariance h ht (homOfLE hUW) r :=
        (chartToCovariance_smul_one h ht hlin _ r).symm
      exact (funext e).symm ▸ (chartToCovariance h ht (homOfLE hUW)).bijective
    have hs' := extendedSectionGenerator R D α hα hU s hs
    exact ⟨U, hxU, s, sectionGeneratorOver_isIso D hU s hs,
      sectionGeneratorOver_isIso (D.extend R) (hU.preimage f) (α.app U s) hs'⟩
  have H (y : ((extendScheme R).obj X).left) := localData (f y)
  refine ⟨?_, isIso_adjoint_of_local_generators f α H⟩
  choose U hU s _ hIso using H
  let V y := f ⁻¹ᵁ U y
  have hV : IsOpenCover V := by
    apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hU y⟩
  exact quasicoherent_of_unit_on_cover (D.extend R).sheaf V hV
    (fun y => @asIso _ _ _ _ _ (hIso y))

end ExtendedFlagCoefficients

/-- Every extension from the ground field compares the actual coefficient
sheaves and all degrees of their derived global sections. -/
theorem flagCohomologyBaseChange : FlagCohomologyBaseChange.{u} := by
  intro k _ G P Q p χ h R
  obtain ⟨_, hproper, _, _, _, _, _, a, _, _, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  obtain ⟨L⟩ := exists_associatedBundle Q p χ a ha
  let D := flagLineData Q p χ h
  let : IsAffineHom D.projection.left := flagTorsor_affine Q
  let : IsAffineHom D.overlapProjection.left := flagOverlap_affine Q
  obtain ⟨α, hα⟩ := scalarExtension_coefficientMap R D
  have hF : D.sheaf.IsQuasicoherent := (flagLineSheafIdentification Q p χ h L).1
  obtain ⟨hF', hIso⟩ := extendedFlagCoefficientComparison Q p χ h L R α hα
  have hcover := finiteAffineCover Q.scheme hproper
  choose c hc using fun n => covarianceDerivedBaseChange R D hF hF' hcover α hα n
  exact ⟨⟨α, hα, hIso, c, hc⟩⟩

/-- In every degree the central torus acts by the original character. -/
theorem centralCohomologyScalarAction : CentralCohomologyScalarAction.{u} :=
  centralCohomologyScalarAction_of_baseChange flagCohomologyBaseChange

end ScalarExtensionCoefficients

section RationalCohomology

universe u

open AdjointRepresentation (GroupPoints)
open scoped TensorProduct ChangeOfRings

section FlatCovarianceComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private structure FlatCovariancePullback {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B}
    (D : CovarianceData X) (D' : CovarianceData Y) (φ : A →+* B) where
  base : Y.left ⟶ X.left
  torsor : D'.torsor.left ⟶ D.torsor.left
  overBase : base ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ)
  square : torsor ≫ D.projection.left = D'.projection.left ≫ base
  flat : Flat base
  coefficients : D.sheaf ⟶ (Scheme.Modules.pushforward base).obj D'.sheaf
  pullsBack : D.IsPullbackMap D' base torsor square coefficients

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  {X : SchemeOverRing A} {Y : SchemeOverRing B} {Z : SchemeOverRing C}
  {D : CovarianceData X} {D' : CovarianceData Y} {D'' : CovarianceData Z}
  {φ : A →+* B} {ψ : B →+* C}

private def FlatCovariancePullback.cohomologyMap (F : FlatCovariancePullback D D' φ) (n : ℕ) :
    (cohomology X n).obj D.sheaf ⟶
      (ModuleCat.restrictScalars.{u} φ).obj ((cohomology Y n).obj D'.sheaf) :=
  let : Flat F.base := F.flat
  (LinearAlgebraicGroups.FlatCohomology.flatCohomologyMap φ F.base F.overBase F.coefficients n).choose

private theorem FlatCovariancePullback.cohomologyMap_induced
    (F : FlatCovariancePullback D D' φ) (n : ℕ) :
    IsCohomologyMap φ F.base F.overBase F.coefficients n (F.cohomologyMap n) := by
  let : Flat F.base := F.flat
  exact (LinearAlgebraicGroups.FlatCohomology.flatCohomologyMap φ F.base F.overBase
    F.coefficients n).choose_spec.1

private def FlatCovariancePullback.comp (F : FlatCovariancePullback D D' φ)
    (G : FlatCovariancePullback D' D'' ψ) : FlatCovariancePullback D D'' (ψ.comp φ) where
  base := G.base ≫ F.base
  torsor := G.torsor ≫ F.torsor
  overBase := LinearAlgebraicGroups.FlatCohomology.comp_over φ ψ F.base G.base F.overBase G.overBase
  square := by rw [Category.assoc, F.square, ← Category.assoc, G.square, Category.assoc]
  flat := by
    let : Flat F.base := F.flat
    let : Flat G.base := G.flat
    infer_instance
  coefficients := F.coefficients ≫ (Scheme.Modules.pushforward F.base).map G.coefficients ≫
    (Scheme.Modules.pushforwardComp G.base F.base).hom.app D''.sheaf
  pullsBack := covariancePullback_comp F.pullsBack G.pullsBack

private theorem FlatCovariancePullback.comp_apply (F : FlatCovariancePullback D D' φ)
    (G : FlatCovariancePullback D' D'' ψ) (n : ℕ) (x : (cohomology X n).obj D.sheaf) :
    (F.comp G).cohomologyMap n x = G.cohomologyMap n (F.cohomologyMap n x) := by
  let : Flat F.base := F.flat
  let : Flat G.base := G.flat
  have h₁ : LinearAlgebraicGroups.FlatCohomology.IsCohomologyMap
      φ F.base F.overBase F.coefficients n (F.cohomologyMap n) := F.cohomologyMap_induced n
  have h₂ : LinearAlgebraicGroups.FlatCohomology.IsCohomologyMap
      ψ G.base G.overBase G.coefficients n (G.cohomologyMap n) := G.cohomologyMap_induced n
  have h := LinearAlgebraicGroups.FlatCohomology.cohomologyMapComp φ ψ F.base G.base
    F.overBase G.overBase F.coefficients G.coefficients n h₁ h₂
  have hcomp := inducedCohomologyMap_unique (ψ.comp φ) (F.comp G).base (F.comp G).overBase
    (F.comp G).coefficients n ((F.comp G).cohomologyMap_induced n) h
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcomp) x

private theorem FlatCovariancePullback.coefficients_eq
    {φ φ' : A →+* B} (F : FlatCovariancePullback D D' φ) (G : FlatCovariancePullback D D' φ')
    (hf : F.base = G.base) (ht : F.torsor = G.torsor) :
    F.coefficients ≫ (Scheme.Modules.pushforwardCongr hf).hom.app D'.sheaf = G.coefficients := by
  have h : ∀ (f g : Y.left ⟶ X.left) (hfg : f = g)
      (t s : D'.torsor.left ⟶ D.torsor.left) (hts : t = s)
      (wt : t ≫ D.projection.left = D'.projection.left ≫ f)
      (ws : s ≫ D.projection.left = D'.projection.left ≫ g)
      (a : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D'.sheaf)
      (b : D.sheaf ⟶ (Scheme.Modules.pushforward g).obj D'.sheaf),
      D.IsPullbackMap D' f t wt a → D.IsPullbackMap D' g s ws b →
        a ≫ (Scheme.Modules.pushforwardCongr hfg).hom.app D'.sheaf = b := by
    intro f g hfg t s hts wt ws a b ha hb
    subst g
    subst s
    have e : (Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app D'.sheaf = 𝟙 _ := by
      apply Scheme.Modules.hom_ext
      intro U
      rw [Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.Hom.id_app]
      simp
    rw [e, Category.comp_id]
    exact covariancePullback_unique D D' f t wt ha hb
  exact h _ _ hf _ _ ht F.square G.square _ _ F.pullsBack G.pullsBack

private theorem FlatCovariancePullback.cohomologyMap_congr {φ φ' : A →+* B}
    (F : FlatCovariancePullback D D' φ) (G : FlatCovariancePullback D D' φ')
    (hφ : φ = φ') (hf : F.base = G.base) (ht : F.torsor = G.torsor)
    (n : ℕ) (x : (cohomology X n).obj D.sheaf) :
    F.cohomologyMap n x = G.cohomologyMap n x := by
  subst φ'
  let b := G.coefficients
  have h := F.coefficients_eq G hf ht
  have transport : ∀ (f g : Y.left ⟶ X.left) (hf : f = g)
      (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
      (wg : g ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
      (a : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj D'.sheaf)
      (b : D.sheaf ⟶ (Scheme.Modules.pushforward g).obj D'.sheaf),
      a ≫ (Scheme.Modules.pushforwardCongr hf).hom.app D'.sheaf = b →
      ∀ m, IsCohomologyMap φ f wf a n m → IsCohomologyMap φ g wg b n m := by
    intro f g hfg wf wg a b hab m hm
    subst g
    have e : (Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app D'.sheaf = 𝟙 _ := by
      apply Scheme.Modules.hom_ext
      intro U
      rw [Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.Hom.id_app]
      simp
    rw [e, Category.comp_id] at hab
    subst b
    exact hm
  have hF := transport _ _ hf F.overBase G.overBase _ _ h _ (F.cohomologyMap_induced n)
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (inducedCohomologyMap_unique φ G.base G.overBase b n hF (G.cohomologyMap_induced n))) x

end FlatCovarianceComposition

section ScalarTower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] {R S : TestAlgebra k} (j : R ⟶ S)

private def scalarTowerMap (X : SchemeOver k) :
    ((extendScheme S).obj X).left ⟶ ((extendScheme R).obj X).left :=
  pullback.lift (extensionProjection S X)
    (extensionStructure S X ≫ Spec.map (CommRingCat.ofHom j.hom.toRingHom)) (by
      rw [extensionProjection_over S X, Category.assoc, ← Spec.map_comp]
      congr 2
      exact (CommRingCat.hom_ext j.hom.comp_algebraMap).symm)

@[reassoc, simp]
private theorem scalarTowerMap_original (X : SchemeOver k) :
    scalarTowerMap j X ≫ extensionProjection R X = extensionProjection S X :=
  pullback.lift_fst _ _ _

@[reassoc, simp]
private theorem scalarTowerMap_over (X : SchemeOver k) :
    scalarTowerMap j X ≫ extensionStructure R X =
      extensionStructure S X ≫ Spec.map (CommRingCat.ofHom j.hom.toRingHom) :=
  pullback.lift_snd _ _ _

private theorem scalarTowerMap_isPullback (X : SchemeOver k) :
    IsPullback (scalarTowerMap j X) (extensionStructure S X) (extensionStructure R X)
      (Spec.map (CommRingCat.ofHom j.hom.toRingHom)) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k S))
  let r := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let b := Spec.map (CommRingCat.ofHom j.hom.toRingHom)
  have h : s = b ≫ r := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact j.hom.comp_algebraMap.symm
  have outer : IsPullback (extensionProjection S X) (extensionStructure S X) X.hom (b ≫ r) := by
    rw [← h]
    exact IsPullback.of_hasPullback _ _
  rw [← scalarTowerMap_original j X] at outer
  exact IsPullback.of_right outer (scalarTowerMap_over j X) (IsPullback.of_hasPullback X.hom r)

private theorem scalarTowerMap_naturality {X Y : SchemeOver k} (q : X ⟶ Y) :
    scalarTowerMap j X ≫ ((extendScheme R).map q).left =
      ((extendScheme S).map q).left ≫ scalarTowerMap j Y := by
  apply extension_hom_ext R <;>
    simp only [Category.assoc, extensionProjection_natural, scalarTowerMap_original_assoc,
      scalarTowerMap_original, extensionMap_over, reassoc_of% extensionMap_over, scalarTowerMap_over]

private def scalarTowerArrow (X : SchemeOver k) :
    extensionAsSchemeOverField S X ⟶ extensionAsSchemeOverField R X :=
  Over.homMk (scalarTowerMap j X) (by
    change scalarTowerMap j X ≫ (extensionStructure R X ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      extensionStructure S X ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))
    rw [← Category.assoc, scalarTowerMap_over j X, Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext j.hom.comp_algebraMap)

private theorem scalarTowerArrow_test (X : SchemeOver k) :
    scalarTowerArrow j X ≫ projectionToTestScheme R X =
      projectionToTestScheme S X ≫ (testSpec k).map j.op :=
  Over.OverMorphism.ext (scalarTowerMap_over j X)

private theorem scalarTowerArrow_original (X : SchemeOver k) :
    scalarTowerArrow j X ≫ projectionToOriginal R X = projectionToOriginal S X :=
  Over.OverMorphism.ext (scalarTowerMap_original j X)

private theorem pointTranslation_scalarTowerMap {H X : SchemeOver k} (a : H ⊗ X ⟶ X)
    (g : Points H R) :
    scalarTowerMap j X ≫ pointTranslation a R g =
      pointTranslation a S (mapPoints j g) ≫ scalarTowerMap j X := by
  apply extension_hom_ext R
  · simp only [Category.assoc, scalarTowerMap_original, pointTranslation_fst]
    change (scalarTowerArrow j X ≫ (lift (projectionToTestScheme R X ≫ g) (projectionToOriginal R X) ≫ a)).left = _
    rw [← Category.assoc, comp_lift, ← Category.assoc (scalarTowerArrow j X),
      scalarTowerArrow_test j X, Category.assoc, scalarTowerArrow_original j X]
  · simp only [Category.assoc, pointTranslation_structure, scalarTowerMap_over, reassoc_of% pointTranslation_structure]

private def flatScalarTowerPullback {X : SchemeOver k} (D : CovarianceData X)
    (hj : Flat (Spec.map (CommRingCat.ofHom j.hom.toRingHom))) :
    FlatCovariancePullback (D.extend R) (D.extend S) j.hom.toRingHom := by
  let f := scalarTowerMap j X
  let t := scalarTowerMap j D.torsor
  let b := scalarTowerMap j D.overlap
  have w : t ≫ (D.extend R).projection.left = (D.extend S).projection.left ≫ f :=
    scalarTowerMap_naturality j D.projection
  have hm : b.appTop (D.extend R).multiplier = (D.extend S).multiplier := by
    change b.appTop ((extensionProjection R D.overlap).appTop D.multiplier) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, scalarTowerMap_original j D.overlap]
    rfl
  let hex := covariancePullback_exists (D.extend R) (D.extend S) f t w b
    (scalarTowerMap_naturality j D.first) (scalarTowerMap_naturality j D.second) hm
  exact ⟨f, t, scalarTowerMap_over j X, w, MorphismProperty.of_isPullback
    (scalarTowerMap_isPullback j X).flip hj, hex.choose, hex.choose_spec⟩

end ScalarTower

section TranslationScalarNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] ModObj.regular

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (n : ℕ)

private def flatTranslationPullback (R : TestAlgebra k) (g : GroupPoints G.val R) :
    FlatCovariancePullback ((flagLineData Q p χ h).extend R) ((flagLineData Q p χ h).extend R) (RingHom.id R) :=
  let α := flagCohomologyTranslate_induced Q p χ h a ha R n g
  let : ModObj G.val.X Q.scheme := a
  let : IsIso (pointTranslation a.smul R g⁻¹) := pointTranslation_isIso R g⁻¹
  ⟨pointTranslation a.smul R g⁻¹, pointTranslation μ[G.val.X] R g⁻¹,
    pointTranslation_over a.smul R g⁻¹, α.choose, inferInstance, α.choose_spec.choose,
    α.choose_spec.choose_spec.1⟩

private theorem flatTranslationPullback_apply (R : TestAlgebra k) (g : GroupPoints G.val R)
    (x : (cohomology ((extendScheme R).obj Q.scheme) n).obj ((flagLineData Q p χ h).extend R).sheaf) :
    (flatTranslationPullback Q p χ h a ha n R g).cohomologyMap n x =
      flagCohomologyTranslate Q p χ h a ha R n g x := by
  let b := flatTranslationPullback Q p χ h a ha n R g
  have hm := (flagCohomologyTranslate_induced Q p χ h a ha R n g).choose_spec.choose_spec.2
  have eq := inducedCohomologyMap_unique (RingHom.id R) b.base b.overBase b.coefficients n
    (b.cohomologyMap_induced n) hm
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom eq) x

private theorem flatScalarTower_translation {R S : TestAlgebra k} (j : R ⟶ S)
    (hj : Flat (Spec.map (CommRingCat.ofHom j.hom.toRingHom))) (g : GroupPoints G.val R)
    (x : (cohomology ((extendScheme R).obj Q.scheme) n).obj ((flagLineData Q p χ h).extend R).sheaf) :
    (flatScalarTowerPullback j (flagLineData Q p χ h) hj).cohomologyMap n
        (flagCohomologyTranslate Q p χ h a ha R n g x) =
      flagCohomologyTranslate Q p χ h a ha S n (mapPoints j g)
        ((flatScalarTowerPullback j (flagLineData Q p χ h) hj).cohomologyMap n x) := by
  let A := flatTranslationPullback Q p χ h a ha n R g
  let B := flatTranslationPullback Q p χ h a ha n S (mapPoints j g)
  let C := flatScalarTowerPullback j (flagLineData Q p χ h) hj
  have hinv : mapPoints j (g⁻¹) = (mapPoints j g : GroupPoints G.val S)⁻¹ := GrpObj.comp_inv _ _
  have hb : (A.comp C).base = (C.comp B).base := by
    change scalarTowerMap j Q.scheme ≫ pointTranslation a.smul R g⁻¹ =
      pointTranslation a.smul S (mapPoints j g : GroupPoints G.val S)⁻¹ ≫ scalarTowerMap j Q.scheme
    rw [pointTranslation_scalarTowerMap, hinv]
  have ht : (A.comp C).torsor = (C.comp B).torsor := by
    change scalarTowerMap j G.val.X ≫ pointTranslation μ[G.val.X] R g⁻¹ =
      pointTranslation μ[G.val.X] S (mapPoints j g : GroupPoints G.val S)⁻¹ ≫ scalarTowerMap j G.val.X
    rw [pointTranslation_scalarTowerMap, hinv]
  have hm := (A.comp C).cohomologyMap_congr (C.comp B) (RingHom.ext fun _ => rfl) hb ht n x
  rw [FlatCovariancePullback.comp_apply, FlatCovariancePullback.comp_apply] at hm
  change C.cohomologyMap n ((flatTranslationPullback Q p χ h a ha n R g).cohomologyMap n x) =
    (flatTranslationPullback Q p χ h a ha n S (mapPoints j g)).cohomologyMap n (C.cohomologyMap n x) at hm
  rw [flatTranslationPullback_apply, flatTranslationPullback_apply] at hm
  exact hm

end TranslationScalarNaturality

section BaseExtensionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {X : SchemeOver k} (D : CovarianceData X)

private def comparisonPullback (R : TestAlgebra k) (E : D.ScalarExtension R) :
    FlatCovariancePullback D (D.extend R) (algebraMap k R) where
  base := extensionProjection R X
  torsor := extensionProjection R D.torsor
  overBase := extensionProjection_over R X
  square := (extensionProjection_natural R D.projection).symm
  flat := LinearAlgebraicGroups.FlatCohomology.flatScalarExtension k R X
  coefficients := E.coefficientMap
  pullsBack := E.pullsBack

private theorem comparisonPullback_apply (R : TestAlgebra k) (E : D.ScalarExtension R) (n : ℕ)
    (x : (cohomology X n).obj D.sheaf) :
    (comparisonPullback D R E).cohomologyMap n x = (E.iso n).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x) := by
  let M := comparisonPullback D R E
  have he := inducedCohomologyMap_unique (algebraMap k R) M.base M.overBase M.coefficients n
    (M.cohomologyMap_induced n) (E.induced n)
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) x

private theorem flatScalarTower_baseChange {R S : TestAlgebra k} (j : R ⟶ S)
    (hj : Flat (Spec.map (CommRingCat.ofHom j.hom.toRingHom)))
    (ER : D.ScalarExtension R) (ES : D.ScalarExtension S) (n : ℕ)
    (x : (cohomology X n).obj D.sheaf) :
    (flatScalarTowerPullback j D hj).cohomologyMap n ((ER.iso n).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x)) =
      (ES.iso n).hom ((1 : S) ⊗ₜ[k,algebraMap k S] x) := by
  let A := comparisonPullback D R ER
  let B := comparisonPullback D S ES
  let C := flatScalarTowerPullback j D hj
  have h := (A.comp C).cohomologyMap_congr B j.hom.comp_algebraMap
    (scalarTowerMap_original j X) (scalarTowerMap_original j D.torsor) n x
  rw [FlatCovariancePullback.comp_apply] at h
  change C.cohomologyMap n ((comparisonPullback D R ER).cohomologyMap n x) =
    (comparisonPullback D S ES).cohomologyMap n x at h
  rw [comparisonPullback_apply, comparisonPullback_apply] at h
  exact h

end BaseExtensionComposition

section Coordinates

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {X : SchemeOver k} (D : CovarianceData X)
    {I : Type u} [Fintype I] [DecidableEq I] (n : ℕ)
    (b : Module.Basis I k ((cohomology X n).obj D.sheaf))

private def cohomologyCoordinates (R : TestAlgebra k) (E : D.ScalarExtension R) :
    (cohomology ((extendScheme R).obj X) n).obj (D.extend R).sheaf ≃ₗ[R] (I → R) :=
  (E.iso n).toLinearEquiv.symm.trans (extendedCoordinates R b)

private theorem cohomologyCoordinates_basis (R : TestAlgebra k) (E : D.ScalarExtension R) (i : I) :
    cohomologyCoordinates D n b R E ((E.iso n).hom ((1 : R) ⊗ₜ[k,algebraMap k R] b i)) =
      Pi.single i 1 := by
  change extendedCoordinates R b ((E.iso n).toLinearEquiv.symm ((E.iso n).toLinearEquiv _)) = _
  rw [LinearEquiv.symm_apply_apply]
  letI : Algebra k R := (algebraMap k R).toAlgebra
  change ((b.baseChange R).equivFun (1 ⊗ₜ[k] b i)) = _
  rw [← Module.Basis.baseChange_apply]
  funext j
  simpa only [Pi.single_apply, eq_comm] using Module.Basis.equivFun_self (b.baseChange R) i j

private theorem flatScalarTower_coordinates {R S : TestAlgebra k} (j : R ⟶ S)
    (hj : Flat (Spec.map (CommRingCat.ofHom j.hom.toRingHom)))
    (ER : D.ScalarExtension R) (ES : D.ScalarExtension S)
    (x : (cohomology ((extendScheme R).obj X) n).obj (D.extend R).sheaf) :
    cohomologyCoordinates D n b S ES ((flatScalarTowerPullback j D hj).cohomologyMap n x) =
      fun i => j.hom ((cohomologyCoordinates D n b R ER x) i) := by
  let xR := cohomologyCoordinates D n b R ER
  let xS := cohomologyCoordinates D n b S ES
  let h := (flatScalarTowerPullback j D hj).cohomologyMap n
  let M := (cohomology ((extendScheme R).obj X) n).obj (D.extend R).sheaf
  let J := ModuleCat.restrictScalars.{u} j.hom.toRingHom
  let L := ModuleCat.of S (I → S)
  let post : M ⟶ J.obj L := h ≫ J.map (ModuleCat.ofHom xS.toLinearMap)
  let j₀ : ModuleCat.of R (I → R) ⟶ J.obj L := ModuleCat.ofHom (Y := J.obj L) {
    toFun := fun v i => j.hom (v i)
    map_add' := fun a b => funext fun i => map_add j.hom (a i) (b i)
    map_smul' := fun r v => funext fun i => map_mul j.hom r (v i) }
  let pre : M ⟶ J.obj L := ModuleCat.ofHom xR.toLinearMap ≫ j₀
  let bR : Module.Basis I R M := (Pi.basisFun R I).map xR.symm
  have eq : post = pre := by
    apply ModuleCat.hom_ext
    apply bR.ext
    intro i
    have hr : bR i = (ER.iso n).hom ((1 : R) ⊗ₜ[k,algebraMap k R] b i) := by
      apply xR.injective
      rw [show xR (bR i) = Pi.single i 1 by
        simp only [bR, Module.Basis.map_apply, Pi.basisFun_apply]
        exact xR.apply_symm_apply _]
      exact (cohomologyCoordinates_basis D n b R ER i).symm
    change xS (h (bR i)) = fun r => j.hom (xR (bR i) r)
    rw [hr, flatScalarTower_baseChange, cohomologyCoordinates_basis, cohomologyCoordinates_basis]
    ext t : 1
    by_cases hti : t = i <;> simp [Pi.single_apply, hti]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom eq) x

end Coordinates

section PointActionInCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open RootWeightAction (act)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (n : ℕ)
    (b : CohomologyBasis (p := p) (χ := χ) h n)

private def translationMatrices (R : TestAlgebra k) (E : (flagLineData Q p χ h).ScalarExtension R) :
    GroupPoints G.val R →* Matrix.GeneralLinearGroup (CohomologyIndex (p := p) (χ := χ) h n) R :=
  let coord := cohomologyCoordinates (flagLineData Q p χ h) n b R E
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
    ((Units.map coord.conjRingEquiv.toMonoidHom).comp
      (flagCohomologyPointAction Q p χ h a ha R n).toHomUnits)

private theorem translationMatrices_apply (R : TestAlgebra k)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (g : GroupPoints G.val R)
    (x : (cohomology ((extendScheme R).obj Q.scheme) n).obj ((flagLineData Q p χ h).extend R).sheaf) :
    let coord := cohomologyCoordinates (flagLineData Q p χ h) n b R E
    (translationMatrices Q p χ h a ha n b R E g).val.mulVec (coord x) =
      coord (flagCohomologyTranslate Q p χ h a ha R n g x) := by
  dsimp only
  let coord := cohomologyCoordinates (flagLineData Q p χ h) n b R E
  let u := Units.map coord.conjRingEquiv.toMonoidHom
    ((flagCohomologyPointAction Q p χ h a ha R n).toHomUnits g)
  have he := congrArg Units.val (Matrix.GeneralLinearGroup.toLin.apply_symm_apply u)
  change Matrix.toLinAlgEquiv' (translationMatrices Q p χ h a ha n b R E g).val = u.val at he
  have ht := DFunLike.congr_fun he (coord x)
  rw [Matrix.toLinAlgEquiv'_apply] at ht
  refine ht.trans ?_
  change coord (flagCohomologyTranslate Q p χ h a ha R n g (coord.symm (coord x))) = _
  rw [coord.symm_apply_apply]

private theorem translationMatrices_flat_naturality {R S : TestAlgebra k} (j : R ⟶ S)
    (hj : Flat (Spec.map (CommRingCat.ofHom j.hom.toRingHom)))
    (ER : (flagLineData Q p χ h).ScalarExtension R) (ES : (flagLineData Q p χ h).ScalarExtension S)
    (g : GroupPoints G.val R) :
    translationMatrices Q p χ h a ha n b S ES (mapPoints j g) =
      Matrix.GeneralLinearGroup.map j.hom.toRingHom (translationMatrices Q p χ h a ha n b R ER g) := by
  let D := flagLineData Q p χ h
  let zR := cohomologyCoordinates D n b R ER
  let zS := cohomologyCoordinates D n b S ES
  let C := (flatScalarTowerPullback j D hj).cohomologyMap n
  let tR := flagCohomologyTranslate Q p χ h a ha R n g
  let tS := flagCohomologyTranslate Q p χ h a ha S n (mapPoints j g)
  let AR := translationMatrices Q p χ h a ha n b R ER g
  let AS := translationMatrices Q p χ h a ha n b S ES (mapPoints j g)
  apply Units.ext
  ext i l
  let x := zR.symm (Pi.single l 1)
  have hx : zR x = Pi.single l 1 := zR.apply_symm_apply _
  have hCx : zS (C x) = Pi.single l 1 := by
    rw [flatScalarTower_coordinates D n b j hj ER ES x, hx]
    ext m
    by_cases hm : m = l <;> simp [Pi.single_apply, hm]
  have hcomm := congrArg zS (flatScalarTower_translation Q p χ h a ha n j hj g x)
  change zS (C (tR x)) = zS (tS (C x)) at hcomm
  rw [flatScalarTower_coordinates D n b j hj ER ES (tR x),
    ← translationMatrices_apply Q p χ h a ha n b R ER g x,
    ← translationMatrices_apply Q p χ h a ha n b S ES (mapPoints j g) (C x)] at hcomm
  have hm := congrFun hcomm i
  change j.hom ((AR.val.mulVec (zR x)) i) = (AS.val.mulVec (zS (C x))) i at hm
  rw [hx, hCx, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hm
  exact hm.symm

end PointActionInCoordinates

section CentralScalarExtension

open CentralIsogenies (characterPullback)
open IsogenyFlagComparison (Restrictions)
attribute [local instance] ModObj.regular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    {Q' : Presentation P'.negative} {Q : Presentation P.negative}
    (f : G'.val ⟶ G.val) (r : Restrictions f P' P)
    (p' : BorelProjection P') (p : BorelProjection P) (χ : Character P.torus.group)
    (h' : FlagKernelPair Q') (h : FlagKernelPair Q)
    (e : Q'.scheme ≅ Q.scheme)
    (w : Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection)

private def centralExtendedPullback (R : TestAlgebra k) :
    FlatCovariancePullback ((flagLineData Q p χ h).extend R)
      ((flagLineData Q' p' (characterPullback r.torus χ) h').extend R) (RingHom.id R) := by
  let F := extendScheme R
  let D := flagLineData Q p χ h
  let D' := flagLineData Q' p' (characterPullback r.torus χ) h'
  let j : D'.overlap ⟶ D.overlap := prod.map f.hom.hom r.borel.hom.hom
  have w₁ : j ≫ D.first = D'.first ≫ f.hom.hom := prod.map_fst _ _
  have w₂ : j ≫ D.second = D'.second ≫ f.hom.hom := centralOverlap_second r
  have w' : (F.map f.hom.hom).left ≫ (D.extend R).projection.left =
      (D'.extend R).projection.left ≫ (F.map e.hom).left := by
    change (F.map f.hom.hom ≫ F.map Q.projection).left = (F.map Q'.projection ≫ F.map e.hom).left
    rw [← F.map_comp, ← F.map_comp, w]
  have map_w (q : D.overlap ⟶ D.torsor) (q' : D'.overlap ⟶ D'.torsor)
      (eq : j ≫ q = q' ≫ f.hom.hom) :
      (F.map j).left ≫ (F.map q).left = (F.map q').left ≫ (F.map f.hom.hom).left := by
    change (F.map j ≫ F.map q).left = (F.map q' ≫ F.map f.hom.hom).left
    rw [← F.map_comp, ← F.map_comp, eq]
  have hm : (F.map j).left.appTop (D.extend R).multiplier = (D'.extend R).multiplier := by
    change ((extensionProjection R D.overlap).appTop ≫ (F.map j).left.appTop) D.multiplier = _
    rw [← Scheme.Hom.comp_appTop, extensionProjection_natural,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [show j.left.appTop D.multiplier = D'.multiplier from centralOverlap_multiplier r p' p χ]
    rfl
  have a := covariancePullback_exists (D.extend R) (D'.extend R) (F.map e.hom).left
    (F.map f.hom.hom).left w' (F.map j).left (map_w D.first D'.first w₁) (map_w D.second D'.second w₂) hm
  let : IsIso (F.map e.hom).left :=
    ((Over.forget _ : SchemeOverRing R ⥤ Scheme).map_isIso (F.map e.hom))
  exact ⟨(F.map e.hom).left, (F.map f.hom.hom).left,
    (extensionMap_over R e.hom).trans (by simp), w', inferInstance, a.choose, a.choose_spec⟩

private theorem centralExtendedPullback_translate
    (a' : ModObj G'.val.X Q'.scheme) (a : ModObj G.val.X Q.scheme)
    (ha' : μ[G'.val.X] ≫ Q'.projection = (𝟙 G'.val.X ⊗ₘ Q'.projection) ≫ a'.smul)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (wa : a'.smul ≫ e.hom = (f.hom.hom ⊗ₘ e.hom) ≫ a.smul)
    (R : TestAlgebra k) (n : ℕ) (g : GroupPoints G'.val R)
    (x : (cohomology ((extendScheme R).obj Q.scheme) n).obj ((flagLineData Q p χ h).extend R).sheaf) :
    let F := centralExtendedPullback f r p' p χ h' h e w R
    F.cohomologyMap n (flagCohomologyTranslate Q p χ h a ha R n (g ≫ f.hom.hom) x) =
      flagCohomologyTranslate Q' p' (characterPullback r.torus χ) h' a' ha' R n g
        (F.cohomologyMap n x) := by
  let A := flatTranslationPullback Q p χ h a ha n R (g ≫ f.hom.hom)
  let B := flatTranslationPullback Q' p' (characterPullback r.torus χ) h' a' ha' n R g
  let F := centralExtendedPullback f r p' p χ h' h e w R
  have hi : (g ≫ f.hom.hom : GroupPoints G.val R)⁻¹ = g⁻¹ ≫ f.hom.hom := (GrpObj.inv_comp _ _).symm
  have hb : (A.comp F).base = (F.comp B).base := by
    change ((extendScheme R).map e.hom).left ≫ pointTranslation a.smul R (g ≫ f.hom.hom)⁻¹ =
      pointTranslation a'.smul R g⁻¹ ≫ ((extendScheme R).map e.hom).left
    rw [hi]
    exact (pointTranslation_natural R f.hom.hom e.hom a'.smul a.smul wa g⁻¹).symm
  have ht : (A.comp F).torsor = (F.comp B).torsor := by
    change ((extendScheme R).map f.hom.hom).left ≫ pointTranslation μ[G.val.X] R (g ≫ f.hom.hom)⁻¹ =
      pointTranslation μ[G'.val.X] R g⁻¹ ≫ ((extendScheme R).map f.hom.hom).left
    rw [hi]
    exact (pointTranslation_natural R f.hom.hom f.hom.hom μ[G'.val.X] μ[G.val.X]
      (IsMonHom.mul_hom _) g⁻¹).symm
  have hm := (A.comp F).cohomologyMap_congr (F.comp B) rfl hb ht n x
  rw [FlatCovariancePullback.comp_apply, FlatCovariancePullback.comp_apply] at hm
  change F.cohomologyMap n ((flatTranslationPullback Q p χ h a ha n R (g ≫ f.hom.hom)).cohomologyMap n x) =
    (flatTranslationPullback Q' p' (characterPullback r.torus χ) h' a' ha' n R g).cohomologyMap n
      (F.cohomologyMap n x) at hm
  rw [flatTranslationPullback_apply, flatTranslationPullback_apply] at hm
  exact hm

private theorem centralExtendedPullback_baseChange
    (R : TestAlgebra k) (n : ℕ)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (E' : (flagLineData Q' p' (characterPullback r.torus χ) h').ScalarExtension R)
    (α : (flagLineData Q p χ h).sheaf ⟶ (Scheme.Modules.pushforward e.hom.left).obj
      (flagLineData Q' p' (characterPullback r.torus χ) h').sheaf)
    (hα : (flagLineData Q p χ h).IsPullbackMap (flagLineData Q' p' (characterPullback r.torus χ) h')
      e.hom.left f.hom.hom.left (congrArg Over.Hom.left w.symm) α)
    (c : flagCohomology Q p χ h n ≅ flagCohomology Q' p' (characterPullback r.torus χ) h' n)
    (hc : IsCohomologyMap (RingHom.id k) e.hom.left (by simp) α n
      (c.hom ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).inv))
    (x : (extendToAlgebra (k := k) (K := R)).obj (flagCohomology Q p χ h n)) :
    (centralExtendedPullback f r p' p χ h' h e w R).cohomologyMap n ((E.iso n).hom x) =
      (E'.iso n).hom ((extendToAlgebra (k := k) (K := R)).map c.hom x) := by
  let D := flagLineData Q p χ h
  let D' := flagLineData Q' p' (characterPullback r.torus χ) h'
  let F := centralExtendedPullback f r p' p χ h' h e w R
  let A := comparisonPullback D R E
  let B := comparisonPullback D' R E'
  let : IsIso e.hom.left := (Over.forget _ : SchemeOver k ⥤ Scheme).map_isIso e.hom
  let U : FlatCovariancePullback D D' (RingHom.id k) :=
    ⟨e.hom.left, f.hom.hom.left, by simp, congrArg Over.Hom.left w.symm, inferInstance, α, hα⟩
  let I := ModuleCat.restrictScalarsId'App (RingHom.id R) rfl
    ((cohomology ((extendScheme R).obj Q'.scheme) n).obj (D'.extend R).sheaf)
  let s := F.cohomologyMap n ≫ I.hom
  let lhs := (E.iso n).hom ≫ s
  let rhs := (extendToAlgebra (k := k) (K := R)).map c.hom ≫ (E'.iso n).hom
  have hs : lhs = rhs := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro z
    have eq := (A.comp F).cohomologyMap_congr (U.comp B) (RingHom.ext fun _ => rfl)
      (extensionProjection_natural R e.hom) (extensionProjection_natural R f.hom.hom) n z
    rw [FlatCovariancePullback.comp_apply, FlatCovariancePullback.comp_apply] at eq
    change F.cohomologyMap n ((comparisonPullback D R E).cohomologyMap n z) =
      (comparisonPullback D' R E').cohomologyMap n (U.cohomologyMap n z) at eq
    have hu : U.cohomologyMap n z = c.hom z := by
      have hm := inducedCohomologyMap_unique (RingHom.id k) e.hom.left (by simp) α n
        (U.cohomologyMap_induced n) hc
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hm) z
    rw [comparisonPullback_apply, hu, comparisonPullback_apply] at eq
    change F.cohomologyMap n ((E.iso n).hom ((1 : R) ⊗ₜ[k,algebraMap k R] z)) =
      (E'.iso n).hom ((extendToAlgebra (k := k) (K := R)).map c.hom ((1 : R) ⊗ₜ[k,algebraMap k R] z))
    rw [ModuleCat.ExtendScalars.map_tmul]
    exact eq
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hs) x

end CentralScalarExtension

section UniversalPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]
  {I : Type u} [Fintype I] [DecidableEq I] {G : GroupScheme k}

private def pointRingMap {R S : TestAlgebra k} (p : Points ((testSpec k).obj (op R)) S) : R ⟶ S :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p).unop

private theorem pointRingMap_spec {R S : TestAlgebra k}
    (p : Points ((testSpec k).obj (op R)) S) : (testSpec k).map (pointRingMap p).op = p :=
  (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage p

private theorem pointRingMap_comp {R S T : TestAlgebra k}
    (a : Points ((testSpec k).obj (op R)) S) (b : Points ((testSpec k).obj (op S)) T) :
    pointRingMap (b ≫ a) = pointRingMap a ≫ pointRingMap b := by
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [op_comp, (testSpec k).map_comp, pointRingMap_spec, pointRingMap_spec, pointRingMap_spec]

/-- For an affine group scheme, each point can be tested after a split
scalar extension. There the universal point and its translate come from
flat maps out of the representing algebra. -/
private theorem compareOnUniversalPoint (affine : IsAffine G.X.left)
    (ρ : ∀ R : TestAlgebra k, GroupPoints G R →* Matrix.GeneralLinearGroup I R)
    (hρ : ∀ {R S : TestAlgebra k} (j : R ⟶ S), Flat (Spec.map (CommRingCat.ofHom j.hom.toRingHom)) →
      ∀ (g : GroupPoints G R), ρ S (mapPoints j g) = Matrix.GeneralLinearGroup.map j.hom.toRingHom (ρ R g)) :
    ∀ {R S : TestAlgebra k} (j : R ⟶ S) (g : GroupPoints G R),
      ρ S (mapPoints j g) = Matrix.GeneralLinearGroup.map j.hom.toRingHom (ρ R g) := by
  obtain ⟨Aop, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr affine
  let A : TestAlgebra k := Aop.unop
  let u : GroupPoints G A := e.hom
  let eval {R : TestAlgebra k} (g : GroupPoints G R) : A ⟶ R := pointRingMap (g ≫ e.inv)
  have compare (R : TestAlgebra k) (g : GroupPoints G R) :
      ρ R g = (Matrix.GeneralLinearGroup.map (eval (1 : GroupPoints G R)).hom.toRingHom (ρ A u))⁻¹ *
        Matrix.GeneralLinearGroup.map (eval g).hom.toRingHom (ρ A u) := by
    let Rsp := (testSpec k).obj (op R)
    let P := G.X ⨯ Rsp
    let p : P ⟶ G.X := prod.fst
    let q : P ⟶ Rsp := prod.snd
    have hP := Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk p q) (prodIsProd G.X Rsp)
    let : IsAffine Rsp.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
    let : IsAffine G.X.left := affine
    have hAff : IsAffine P.left := IsAffine.of_isPullback hP
    obtain ⟨Bop, ⟨d⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hAff
    let B : TestAlgebra k := Bop.unop
    have hR : Flat Rsp.hom := by
      change Flat (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      exact Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) _)
    let : Flat p.left := MorphismProperty.of_isPullback hP.flip hR
    let τ : P ⟶ P := prod.lift (p * (q ≫ g)) q
    let σ : P ⟶ P := prod.lift (p * (q ≫ g)⁻¹) q
    have htq : τ ≫ q = q := prod.lift_snd _ _
    have hsq : σ ≫ q = q := prod.lift_snd _ _
    have htp : τ ≫ p = p * (q ≫ g) := prod.lift_fst _ _
    have hsp : σ ≫ p = p * (q ≫ g)⁻¹ := prod.lift_fst _ _
    let : IsIso τ := ⟨⟨σ, by
      apply prod.hom_ext (X := G.X) (Y := Rsp)
      · change (τ ≫ σ) ≫ p = 𝟙 _ ≫ p
        rw [Category.assoc, hsp, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
          htq, htp, mul_inv_cancel_right, Category.id_comp]
      · simp only [Category.assoc, show prod.snd = q from rfl, hsq, htq, Category.id_comp], by
      apply prod.hom_ext (X := G.X) (Y := Rsp)
      · change (σ ≫ τ) ≫ p = 𝟙 _ ≫ p
        rw [Category.assoc, htp, MonObj.comp_mul, ← Category.assoc,
          hsq, hsp, inv_mul_cancel_right, Category.id_comp]
      · simp only [Category.assoc, show prod.snd = q from rfl, hsq, htq, Category.id_comp]⟩⟩
    let a : A ⟶ B := pointRingMap (d.hom ≫ p ≫ e.inv)
    let a' : A ⟶ B := pointRingMap (d.hom ≫ τ ≫ p ≫ e.inv)
    let b : R ⟶ B := pointRingMap (d.hom ≫ q)
    let c : B ⟶ R := pointRingMap (prod.lift (1 : Rsp ⟶ G.X) (𝟙 Rsp) ≫ d.inv)
    have h₁ : Flat (Spec.map (CommRingCat.ofHom a.hom.toRingHom)) := by
      change Flat ((testSpec k).map a.op).left
      rw [pointRingMap_spec]
      simp only [Over.comp_left]
      infer_instance
    have h₂ : Flat (Spec.map (CommRingCat.ofHom a'.hom.toRingHom)) := by
      change Flat ((testSpec k).map a'.op).left
      rw [pointRingMap_spec]
      simp only [Over.comp_left]
      infer_instance
    have hG : Flat G.X.hom := by
      have h : Flat ((testSpec k).obj (op A)).hom := by
        change Flat (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        exact Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) _)
      have ht : Flat (e.hom.left ≫ G.X.hom) := (Over.w e.hom).symm ▸ h
      exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat) e.hom.left G.X.hom).mp ht
    let : Flat q.left := MorphismProperty.of_isPullback hP hG
    have h₃ : Flat (Spec.map (CommRingCat.ofHom b.hom.toRingHom)) := by
      change Flat ((testSpec k).map b.op).left
      rw [pointRingMap_spec]
      simp only [Over.comp_left]
      infer_instance
    have hb : b ≫ c = 𝟙 R := by
      apply Quiver.Hom.op_inj
      apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
      rw [op_comp, (testSpec k).map_comp, pointRingMap_spec, pointRingMap_spec]
      simp [q]
      rfl
    have ha₁ : mapPoints a u = d.hom ≫ p := by
      change (testSpec k).map (pointRingMap _).op ≫ e.hom = _
      rw [pointRingMap_spec]
      simp
    have ha₂ : mapPoints a' u = mapPoints a u * mapPoints b g := by
      change (testSpec k).map (pointRingMap _).op ≫ e.hom = _
      rw [pointRingMap_spec, ha₁]
      change _ = (d.hom ≫ p) * ((testSpec k).map (pointRingMap _).op ≫ g)
      rw [pointRingMap_spec]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ← MonObj.comp_mul, htp]
    let v := prod.lift (1 : Rsp ⟶ G.X) (𝟙 Rsp)
    have hvp : v ≫ p = 1 := prod.lift_fst _ _
    have hvq : v ≫ q = 𝟙 _ := prod.lift_snd _ _
    have hac : a ≫ c = eval (1 : GroupPoints G R) := by
      dsimp only [a, c, eval]
      rw [← pointRingMap_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, p, prod.lift_fst_assoc]
    have ha'c : a' ≫ c = eval g := by
      dsimp only [a', c, eval]
      rw [← pointRingMap_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply congrArg pointRingMap
      rw [reassoc_of% htp, ← Category.assoc v, MonObj.comp_mul, hvp, ← Category.assoc,
        hvq, Category.id_comp, one_mul]
    have h := hρ a' h₂ u
    rw [ha₂, map_mul, hρ a h₁ u, hρ b h₃ g] at h
    have h := congrArg (Matrix.GeneralLinearGroup.map c.hom.toRingHom) h
    rw [map_mul] at h
    change Matrix.GeneralLinearGroup.map ((a ≫ c).hom.toRingHom) (ρ A u) *
      Matrix.GeneralLinearGroup.map ((b ≫ c).hom.toRingHom) (ρ R g) =
      Matrix.GeneralLinearGroup.map ((a' ≫ c).hom.toRingHom) (ρ A u) at h
    rw [hac, hb, ha'c] at h
    change _ * ρ R g = _ at h
    exact eq_inv_mul_of_mul_eq h
  intro R S j g
  rw [compare S (mapPoints j g), compare R g]
  have hEval (q : GroupPoints G R) : eval (mapPoints j q) = eval q ≫ j := by
    apply Quiver.Hom.op_inj
    apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    rw [op_comp, (testSpec k).map_comp]
    change (testSpec k).map (pointRingMap _).op = (testSpec k).map j.op ≫
      (testSpec k).map (pointRingMap _).op
    simp only [pointRingMap_spec, Category.assoc]
  have hone : (1 : GroupPoints G S) = mapPoints j (1 : GroupPoints G R) :=
    (MonObj.comp_one ((testSpec k).map j.op)).symm
  rw [hone, hEval, hEval, map_mul, map_inv]
  rfl

end UniversalPoint

section RationalFlagAction

open RootWeightAction (act)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem scalarExtension_iso_eq {k : Type u} [Field k] {X : SchemeOver k}
    (D : CovarianceData X) (R : TestAlgebra k) (E E' : D.ScalarExtension R) (n : ℕ) :
    E.iso n = E'.iso n := by
  have h := covariancePullback_unique D (D.extend R) (extensionProjection R X)
    (extensionProjection R D.torsor) (extensionProjection_natural R D.projection).symm
    E.pullsBack E'.pullsBack
  apply Iso.ext
  apply ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _).injective
  exact inducedCohomologyMap_unique (algebraMap k R) (extensionProjection R X)
    (extensionProjection_over R X) E.coefficientMap n (E.induced n) (h.symm ▸ E'.induced n)

private theorem flagCohomologyRepresentation_of_baseChange
    (baseChange : FlagCohomologyBaseChange.{u}) : FlagCohomologyRepresentation.{u} := by
  intro k _ G P Q p χ h a ha n
  classical
  let : FiniteDimensional k (flagCohomology Q p χ h n) := (flagCohomologyFinite Q p χ h).1 n
  let b : CohomologyBasis (p := p) (χ := χ) h n :=
    (Module.finBasis k (flagCohomology Q p χ h n)).reindex Equiv.ulift.symm
  let E (R : TestAlgebra k) := (baseChange Q p χ h R).some
  let m (R : TestAlgebra k) := translationMatrices Q p χ h a ha n b R (E R)
  have nat {R S : TestAlgebra k} (j : R ⟶ S) (g : GroupPoints G.val R) :
      m S (mapPoints j g) = Matrix.GeneralLinearGroup.map j.hom.toRingHom (m R g) :=
    compareOnUniversalPoint G.property.1 m (fun {A B} i hi x =>
      translationMatrices_flat_naturality Q p χ h a ha n b i hi (E A) (E B) x) j g
  let ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n) := {
    app R := GrpCat.ofHom (m R)
    naturality := by
      intro R S j
      apply GrpCat.ext
      intro g
      exact nat j g }
  refine ⟨b, ρ, fun R g E' => ?_⟩
  obtain ⟨w, α, hα, hm⟩ := flagCohomologyTranslate_induced Q p χ h a ha R n g
  refine ⟨w, α, flagCohomologyTranslate Q p χ h a ha R n g, hα, hm, fun x => ?_⟩
  have he := scalarExtension_iso_eq (flagLineData Q p χ h) R E' (E R) n
  have hcoord (y : (cohomology ((extendScheme R).obj Q.scheme) n).obj ((flagLineData Q p χ h).extend R).sheaf) :
      extendedCoordinates R b ((E'.iso n).inv y) = cohomologyCoordinates (flagLineData Q p χ h) n b R (E R) y := by
    rw [he]
    rfl
  change extendedCoordinates R b ((E'.iso n).inv (flagCohomologyTranslate Q p χ h a ha R n g x)) =
    (m R g).val.mulVec (extendedCoordinates R b ((E'.iso n).inv x))
  rw [hcoord, hcoord]
  exact (translationMatrices_apply Q p χ h a ha n b R (E R) g x).symm

private theorem flagAction_coordinates
    {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
    {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    {n : ℕ} {b : CohomologyBasis (p := p) (χ := χ) h n}
    {ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n)}
    (hρ : IsFlagCohomologyAction h a n b ρ) (R : TestAlgebra k) (g : GroupPoints G.val R)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (x : (cohomology ((extendScheme R).obj Q.scheme) n).obj ((flagLineData Q p χ h).extend R).sheaf) :
    let c := cohomologyCoordinates (flagLineData Q p χ h) n b R E
    c (flagCohomologyTranslate Q p χ h a ha R n g x) = act ρ R g (c x) := by
  let D := (flagLineData Q p χ h).extend R
  let f := pointTranslation a.smul R g⁻¹
  let t := pointTranslation μ[G.val.X] R g⁻¹
  obtain ⟨w, α, m, hα, hm, hcoord⟩ := hρ R g E
  obtain ⟨w', α', hα', hm'⟩ := flagCohomologyTranslate_induced Q p χ h a ha R n g
  have e := covariancePullback_unique D D f t w hα hα'
  subst α'
  have hm₀ := inducedCohomologyMap_unique (RingHom.id R) f (pointTranslation_over a.smul R g⁻¹) α n hm hm'
  let d := ModuleCat.restrictScalarsId'App (RingHom.id R) rfl
    ((cohomology ((extendScheme R).obj Q.scheme) n).obj D.sheaf)
  have eq : m = flagCohomologyTranslate Q p χ h a ha R n g := (cancel_mono d.inv).mp hm₀
  exact eq ▸ hcoord x

set_option maxRecDepth 1600 in
private theorem centralCohomologyComparison_of_baseChange
    (baseChange : FlagCohomologyBaseChange.{u}) : CentralCohomologyComparison.{u} := by
  intro k _ G' G P' P f hf r p' p χ Q' Q h' h a' a ha' ha L' L
  obtain ⟨e, w, m, α, wa, hp, ht, hm, hα, _, cdata⟩ :=
    centralCohomologyIsomorphism f hf r p' p χ Q' Q h' h a' a ha' ha L' L
  refine ⟨e, w, m, α, wa, hp, ht, hm, hα, fun n => ?_⟩
  obtain ⟨c, hc⟩ := cdata n
  refine ⟨c, hc, fun b b' ρ ρ' hρ hρ' R g v => ?_⟩
  let D := flagLineData Q p χ h
  let D' := flagLineData Q' p' (CentralIsogenies.characterPullback r.torus χ) h'
  let E := (baseChange Q p χ h R).some
  let E' := (baseChange Q' p' (CentralIsogenies.characterPullback r.torus χ) h' R).some
  let F := centralExtendedPullback f r p' p χ h' h e w R
  let d := cohomologyCoordinates D n b R E
  let d' := cohomologyCoordinates D' n b' R E'
  let J := extendToAlgebra (k := k) (K := R)
  let C := fun z => extendedCoordinates R b' (J.map c.hom ((extendedCoordinates R b).symm z))
  have hC (x : (cohomology ((extendScheme R).obj Q.scheme) n).obj (D.extend R).sheaf) :
      C (d x) = d' (F.cohomologyMap n x) := by
    let z := (E.iso n).inv x
    have hz : (E.iso n).hom z = x := Iso.inv_hom_id_apply (C := ModuleCat _) _ _
    have hc₀ := centralExtendedPullback_baseChange f r p' p χ h' h e w R n E E' α hα c hc z
    change F.cohomologyMap n ((E.iso n).hom z) = (E'.iso n).hom (J.map c.hom z) at hc₀
    rw [hz] at hc₀
    have hleft : (extendedCoordinates R b).symm (d x) = z :=
      (extendedCoordinates R b).symm_apply_apply z
    have hright : (E'.iso n).inv (F.cohomologyMap n x) = J.map c.hom z := by
      rw [hc₀]
      exact Iso.hom_inv_id_apply (C := ModuleCat _) _ _
    exact congrArg (fun y => extendedCoordinates R b' (J.map c.hom y)) hleft |>.trans
      (congrArg (extendedCoordinates R b') hright.symm)
  let x := d.symm v
  let T := flagCohomologyTranslate Q p χ h a ha R n (g ≫ f.hom.hom)
  let T' := flagCohomologyTranslate Q' p' (CentralIsogenies.characterPullback r.torus χ) h' a' ha' R n g
  have hx : d x = v := d.apply_symm_apply v
  have equiv := centralExtendedPullback_translate f r p' p χ h' h e w a' a ha' ha wa R n g x
  change C (act ρ R (g ≫ f.hom.hom) v) = act ρ' R g (C v)
  calc
    C (act ρ R (g ≫ f.hom.hom) v) = C (d (T x)) := by
      rw [← hx]
      exact congrArg C (flagAction_coordinates ha hρ R (g ≫ f.hom.hom) E x).symm
    _ = d' (F.cohomologyMap n (T x)) := hC _
    _ = d' (T' (F.cohomologyMap n x)) := congrArg d' equiv
    _ = act ρ' R g (C v) := by
      rw [← hx, hC]
      exact flagAction_coordinates ha' hρ' R g E' (F.cohomologyMap n x)

end RationalFlagAction

/-- The geometric translations induce a finite-dimensional rational action in
any degree, with the coefficient sheaf and scalar extension described above. -/
theorem flagCohomologyRepresentation : FlagCohomologyRepresentation.{u} :=
  flagCohomologyRepresentation_of_baseChange flagCohomologyBaseChange

/-- The pullback on cohomology under the central isogeny intertwines the
rational representations on all test algebras. -/
theorem centralCohomologyComparison : CentralCohomologyComparison.{u} :=
  centralCohomologyComparison_of_baseChange flagCohomologyBaseChange

end RationalCohomology

end

end LinearAlgebraicGroups.Representation.FlagCohomology
