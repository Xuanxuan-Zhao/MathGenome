import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! HA-H05, source 3708–3729. All sections in the two-open sequence carry
scalars from R(V ⊔ W). The order of the opens is fixed: the difference is
restriction from V minus restriction from W. The cochain construction is
made for arbitrary complexes; exactness uses only injectivity of the terms. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
universe u

namespace AdvancedHomologicalAlgebra.MayerVietorisData

variable {X : TopCat.{u}} (R : RingSheaf X)

/-- Sections on T, viewed as R(U)-modules by the actual restriction of rings. -/
def sectionsFunctor (U T : Opens X) (h : T ≤ U) :
    Modules R ⥤ ModuleCat.{u} (sectionRing R U) :=
  SheafOfModules.evaluation R (op T) ⋙
    ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom

instance (U T : Opens X) (h : T ≤ U) : (sectionsFunctor R U T h).Additive := by
  dsimp [sectionsFunctor]; infer_instance

/-- Linear restriction after both source and target are viewed over R(U). -/
def res (U T S : Opens X) (hT : T ≤ U) (hS : S ≤ U) (h : S ≤ T) :
    sectionsFunctor R U T hT ⟶ sectionsFunctor R U S hS where
  app M := ModuleCat.ofHom
    (X := (sectionsFunctor R U T hT).obj M)
    (Y := (sectionsFunctor R U S hS).obj M)
    { toFun := M.val.map (homOfLE h).op
      map_add' := map_add _
      map_smul' r s := by
        change M.val.map (homOfLE h).op ((R.obj.map (homOfLE hT).op r) • (show M.val.obj (op T) from s)) =
          (R.obj.map (homOfLE hS).op r) • (show M.val.obj (op S) from M.val.map (homOfLE h).op s)
        rw [M.val.map_smul]
        congr 1
        rw [← RingCat.comp_apply, ← R.obj.map_comp]
        rfl }
  naturality M N f := by
    ext s
    exact (PresheafOfModules.naturality_apply f.val (homOfLE h).op s).symm

@[simp] lemma res_comp (U T S P : Opens X) (hT : T ≤ U) (hS : S ≤ U)
    (hP : P ≤ U) (h : S ≤ T) (k : P ≤ S) (M : Modules R) :
    (res R U T S hT hS h).app M ≫ (res R U S P hS hP k).app M =
      (res R U T P hT hP (k.trans h)).app M := by
  ext s
  exact (M.val.map_comp_apply (homOfLE h).op (homOfLE k).op s).symm

variable (V W : Opens X)

abbrev base := V ⊔ W
abbrev meet := V ⊓ W

/-- The section short complex, even for nonflasque coefficients. Its middle
term uses the concrete product model of the binary biproduct. -/
def sectionRow (M : Modules R) : ShortComplex (ModuleCat.{u} (sectionRing R (V ⊔ W))) := by
  let A := (sectionsFunctor R (V ⊔ W) V le_sup_left).obj M
  let B := (sectionsFunctor R (V ⊔ W) W le_sup_right).obj M
  let fV := (res R (V ⊔ W) (V ⊔ W) V le_rfl le_sup_left le_sup_left).app M
  let fW := (res R (V ⊔ W) (V ⊔ W) W le_rfl le_sup_right le_sup_right).app M
  let gV := (res R (V ⊔ W) V (V ⊓ W) le_sup_left (inf_le_left.trans le_sup_left) inf_le_left).app M
  let gW := (res R (V ⊔ W) W (V ⊓ W) le_sup_right (inf_le_left.trans le_sup_left) inf_le_right).app M
  exact {
    X₁ := (sectionsFunctor R (V ⊔ W) (V ⊔ W) le_rfl).obj M
    X₂ := ModuleCat.of (sectionRing R (V ⊔ W)) (A × B)
    X₃ := (sectionsFunctor R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left)).obj M
    f := ModuleCat.ofHom
      (X := (sectionsFunctor R (V ⊔ W) (V ⊔ W) le_rfl).obj M)
      (Y := ModuleCat.of (sectionRing R (V ⊔ W)) (A × B)) (fV.hom.prod fW.hom)
    g := ModuleCat.ofHom (X := ModuleCat.of (sectionRing R (V ⊔ W)) (A × B))
      (Y := (sectionsFunctor R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left)).obj M)
      (gV.hom.comp (LinearMap.fst _ A B) -
      gW.hom.comp (LinearMap.snd _ A B))
    zero := by
      ext s
      change ((fV ≫ gV) s - (fW ≫ gW) s) = 0
      rw [show fV ≫ gV = fW ≫ gW by dsimp [fV, fW, gV, gW]; simp]
      exact sub_self _ }

/-- Sections applied termwise. -/
abbrev sectionComplex (U T : Opens X) (h : T ≤ U) (I : CochainComplex (Modules R) ℤ) :=
  ((sectionsFunctor R U T h).mapHomologicalComplex (.up ℤ)).obj I

/-- The two-open short complex of cochain complexes. -/
def complexRow (I : CochainComplex (Modules R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} (sectionRing R (V ⊔ W))) ℤ) where
  X₁ := sectionComplex R (V ⊔ W) (V ⊔ W) le_rfl I
  X₂ := sectionComplex R (V ⊔ W) V le_sup_left I ⊞
    sectionComplex R (V ⊔ W) W le_sup_right I
  X₃ := sectionComplex R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) I
  f := biprod.lift
    (((res R _ _ V le_rfl le_sup_left le_sup_left).mapHomologicalComplex (.up ℤ)).app I)
    (((res R _ _ W le_rfl le_sup_right le_sup_right).mapHomologicalComplex (.up ℤ)).app I)
  g := biprod.desc
    (((res R _ V _ le_sup_left (inf_le_left.trans le_sup_left) inf_le_left).mapHomologicalComplex (.up ℤ)).app I)
    (-(((res R _ W _ le_sup_right (inf_le_left.trans le_sup_left) inf_le_right).mapHomologicalComplex (.up ℤ)).app I))
  zero := by
    rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero]
    apply HomologicalComplex.Hom.ext
    funext n
    change (res R _ _ V _ _ _).app (I.X n) ≫
      (res R _ V _ _ _ _).app (I.X n) =
      (res R _ _ W _ _ _).app (I.X n) ≫ (res R _ W _ _ _ _).app (I.X n)
    simp

end AdvancedHomologicalAlgebra.MayerVietorisData

namespace Specs.AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData

/-- Gluing and flasqueness yield a short exact sequence over the section ring. -/
def sectionsExactType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  (V W : Opens X) (M : Modules R), IsFlasque R M → (sectionRow R V W M).ShortExact

/-- Every termwise injective complex gives the two-open short exact sequence. -/
def complexesExactType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
  (V W : Opens X) (I : CochainComplex (Modules R) ℤ),
  (∀ q : ℤ, Injective (I.X q)) → (complexRow R V W I).ShortExact

end Specs.AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietorisData
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)

/-- A cochain map induces a map of the two-open section rows. -/
def complexRowMap {I J : CochainComplex (Modules R) ℤ} (φ : I ⟶ J) :
    complexRow R V W I ⟶ complexRow R V W J where
  τ₁ := ((sectionsFunctor R (V ⊔ W) (V ⊔ W) le_rfl).mapHomologicalComplex (.up ℤ)).map φ
  τ₂ := biprod.map
    (((sectionsFunctor R (V ⊔ W) V le_sup_left).mapHomologicalComplex (.up ℤ)).map φ)
    (((sectionsFunctor R (V ⊔ W) W le_sup_right).mapHomologicalComplex (.up ℤ)).map φ)
  τ₃ := ((sectionsFunctor R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left)).mapHomologicalComplex (.up ℤ)).map φ
  comm₁₂ := by
    apply biprod.hom_ext <;> simp only [complexRow, Category.assoc, biprod.lift_fst, biprod.lift_snd,
      biprod.map_fst, biprod.map_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc]
    all_goals exact NatTrans.naturality _ φ
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp only [complexRow, biprod.inl_desc, biprod.inr_desc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.inl_map_assoc, biprod.inr_map_assoc, Preadditive.neg_comp,
      Preadditive.comp_neg]
    · exact NatTrans.naturality _ φ
    · exact congrArg Neg.neg (NatTrans.naturality _ φ)

end AdvancedHomologicalAlgebra.MayerVietorisData

namespace Specs.AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData

/-- Every degree of the ordinary cohomology sequence is exact. With the
canonical homology/biproduct isomorphism this has precisely the two-open shape. -/
def longExactType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (V W : Opens X) (I : CochainComplex (Modules R) ℤ)
    (hI : ∀ q : ℤ, Injective (I.X q)),
  ∃ hS : (complexRow R V W I).ShortExact, ∀ n : ℤ,
    (HomologicalComplex.HomologySequence.composableArrows₅ hS n (n + 1) rfl).Exact

/-- Naturality of the connecting homomorphism for every map of resolutions. -/
def naturalityType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (V W : Opens X) (I J : CochainComplex (Modules R) ℤ)
    (hI : ∀ q : ℤ, Injective (I.X q)) (hJ : ∀ q : ℤ, Injective (J.X q))
    (hS : (complexRow R V W I).ShortExact) (hT : (complexRow R V W J).ShortExact)
    (φ : I ⟶ J) (n : ℤ),
  hS.δ n (n + 1) rfl ≫ HomologicalComplex.homologyMap (complexRowMap R V W φ).τ₁ (n + 1) =
    HomologicalComplex.homologyMap (complexRowMap R V W φ).τ₃ n ≫ hT.δ n (n + 1) rfl

/-- Identification of the model cohomology with HA-H01, after restricting
scalars along R(U) → R(T). This is required for every injective resolution. -/
def resolutionModelType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (U T : Opens X) (h : T ≤ U) (M : Modules R)
    (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I),
  QuasiIso ι → (∀ q : ℤ, Injective (I.X q)) → ∀ n : ℕ,
  Nonempty (((ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom).obj
    ((sectionCohomology R T n).obj M)) ≅
      (sectionComplex R U T h I).homology (n : ℤ))

/-- The boundary is the one of HA-D04, with its fixed cone sign. -/
def derivedBoundaryType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (V W : Opens X) (I : CochainComplex (Modules R) ℤ)
    (hS : (complexRow R V W I).ShortExact),
  let A := ModuleCat.{u} (sectionRing R (V ⊔ W))
  letI := HasDerivedCategory.standard A
  ∀ n : ℤ,
  _root_.DerivedCategory.HomologySequence.δ
      (Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.row hS) n (n + 1) rfl ≫
      (_root_.DerivedCategory.homologyFunctorFactors A (n + 1)).hom.app (complexRow R V W I).X₁ =
    (_root_.DerivedCategory.homologyFunctorFactors A n).hom.app (complexRow R V W I).X₃ ≫
      hS.δ n (n + 1) rfl

end Specs.AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietorisData
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)

instance homologyPreservesBinary (U : Opens X) (n : ℤ) :
    PreservesBinaryBiproducts
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} (sectionRing R U)) (.up ℤ) n) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

/-- The canonical homology isomorphism for the middle biproduct. -/
def middleIso (I : CochainComplex (Modules R) ℤ) (n : ℤ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} (sectionRing R (V ⊔ W))) (.up ℤ) n).mapBiprod
    (sectionComplex R (V ⊔ W) V le_sup_left I)
    (sectionComplex R (V ⊔ W) W le_sup_right I)

/-- The long sequence written with the actual biproduct of the two local
cohomology modules, rather than homology of a biproduct of complexes. -/
def modelSequence (I : CochainComplex (Modules R) ℤ)
    (hS : (complexRow R V W I).ShortExact) (n : ℤ) :
    ComposableArrows (ModuleCat.{u} (sectionRing R (V ⊔ W))) 5 :=
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} (sectionRing R (V ⊔ W))) (.up ℤ)
  let a := fun n => biprod.lift
    ((H n).map (((res R _ _ V le_rfl le_sup_left le_sup_left).mapHomologicalComplex (.up ℤ)).app I))
    ((H n).map (((res R _ _ W le_rfl le_sup_right le_sup_right).mapHomologicalComplex (.up ℤ)).app I))
  let b := fun n => biprod.desc
    ((H n).map (((res R _ V _ le_sup_left (inf_le_left.trans le_sup_left) inf_le_left).mapHomologicalComplex (.up ℤ)).app I))
    (-((H n).map (((res R _ W _ le_sup_right (inf_le_left.trans le_sup_left) inf_le_right).mapHomologicalComplex (.up ℤ)).app I)))
  ComposableArrows.mk₅ (a n) (b n) (hS.δ n (n + 1) rfl) (a (n + 1)) (b (n + 1))

end AdvancedHomologicalAlgebra.MayerVietorisData

namespace Specs.AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData

/-- Exactness in the displayed two-open shape, in R(V ⊔ W)-modules. -/
def modelExactType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (V W : Opens X) (I : CochainComplex (Modules R) ℤ)
    (hI : ∀ q : ℤ, Injective (I.X q)),
  ∃ hS : (complexRow R V W I).ShortExact, ∀ n : ℤ, (modelSequence R V W I hS n).Exact

/-- Lift a cocycle on the intersection to a pair on V,W, differentiate,
and descend the resulting compatible pair to the union. This is the boundary
class, with the positive lift-and-differential convention of HA-D04. -/
def liftDifferentialType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (V W : Opens X) (I : CochainComplex (Modules R) ℤ)
    (hS : (complexRow R V W I).ShortExact) (n : ℤ)
    (P : ModuleCat.{u} (sectionRing R (V ⊔ W)))
    (c : P ⟶ (complexRow R V W I).X₃.X n)
    (hc : c ≫ (complexRow R V W I).X₃.d n (n + 1) = 0)
    (b : P ⟶ (complexRow R V W I).X₂.X n)
    (hb : b ≫ (complexRow R V W I).g.f n = c)
    (a : P ⟶ (complexRow R V W I).X₁.X (n + 1))
    (ha : a ≫ (complexRow R V W I).f.f (n + 1) =
      b ≫ (complexRow R V W I).X₂.d n (n + 1)),
  (complexRow R V W I).X₃.liftCycles c (n + 1) (by simp) hc ≫
      (complexRow R V W I).X₃.homologyπ n ≫ hS.δ n (n + 1) rfl =
    (complexRow R V W I).X₁.liftCycles a (n + 2) (by apply (ComplexShape.up ℤ).next_eq'; change (n + 1) + 1 = n + 2; omega) (by
      have := hS.mono_f
      rw [← cancel_mono ((complexRow R V W I).f.f (n + 2)), Category.assoc,
        ← (complexRow R V W I).f.comm, reassoc_of% ha,
        HomologicalComplex.d_comp_d, comp_zero, zero_comp]) ≫
      (complexRow R V W I).X₁.homologyπ (n + 1)

end Specs.AdvancedHomologicalAlgebra.MayerVietoris

namespace Specs.AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData

/-- For every coefficient sheaf there is an injective resolution whose
section cohomology realizes the two-open sequence, with HA-H01 comparisons
on every subopen. No vanishing condition is imposed on the opens. -/
def mayerVietorisType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (V W : Opens X) (M : Modules R),
  ∃ (I : CochainComplex (Modules R) ℤ) (hb : I.IsStrictlyGE 0)
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I),
    QuasiIso ι ∧ (∀ q : ℤ, Injective (I.X q)) ∧
    ∃ hS : (complexRow R V W I).ShortExact,
      (∀ n : ℤ, (modelSequence R V W I hS n).Exact) ∧
      ∀ (T : Opens X) (h : T ≤ V ⊔ W) (n : ℕ),
        Nonempty (((ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom).obj
          ((sectionCohomology R T n).obj M)) ≅
          (sectionComplex R (V ⊔ W) T h I).homology (n : ℤ))

/-- Homotopic comparison maps give identical maps on every local cohomology
module. Together with naturality this makes the sequence independent of lifts. -/
def homotopyIndependenceType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (U T : Opens X) (h : T ≤ U) (I J : CochainComplex (Modules R) ℤ)
    (f g : I ⟶ J), Homotopy f g → ∀ n : ℤ,
  HomologicalComplex.homologyMap (((sectionsFunctor R U T h).mapHomologicalComplex (.up ℤ)).map f) n =
    HomologicalComplex.homologyMap (((sectionsFunctor R U T h).mapHomologicalComplex (.up ℤ)).map g) n

end Specs.AdvancedHomologicalAlgebra.MayerVietoris

namespace Specs.AdvancedHomologicalAlgebra.MayerVietoris

/-- Every map of coefficient sheaves lifts to the injective resolutions,
and such lifts are unique up to cochain homotopy. The augmentation is allowed
to commute up to homotopy, which is sufficient for induced cohomology maps. -/
def resolutionLiftsType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (M N : Modules R) (I J : CochainComplex (Modules R) ℤ)
    [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
    (κ : (CochainComplex.singleFunctor (Modules R) 0).obj N ⟶ J),
  QuasiIso ι → QuasiIso κ → (∀ q : ℤ, Injective (J.X q)) → ∀ f : M ⟶ N,
  ∃ φ : I ⟶ J,
    Nonempty (Homotopy (ι ≫ φ) ((CochainComplex.singleFunctor (Modules R) 0).map f ≫ κ)) ∧
    ∀ ψ : I ⟶ J,
      Nonempty (Homotopy (ι ≫ ψ) ((CochainComplex.singleFunctor (Modules R) 0).map f ≫ κ)) →
      Nonempty (Homotopy φ ψ)

end Specs.AdvancedHomologicalAlgebra.MayerVietoris

namespace Specs.AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData

/-- A simultaneous natural identification with the fixed HA-H01 functors,
not merely a separate isomorphism of objects. Naturality holds for all
comparison maps commuting with the augmentations up to homotopy. -/
def naturalModelsType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X)
    (U T : Opens X) (h : T ≤ U),
  ∃ e : ∀ (M : Modules R) (I : CochainComplex (Modules R) ℤ) (hb : I.IsStrictlyGE 0)
      (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
      (hi : QuasiIso ι) (hI : ∀ q : ℤ, Injective (I.X q)) (n : ℕ),
      ((ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom).obj
        ((sectionCohomology R T n).obj M)) ≅ (sectionComplex R U T h I).homology (n : ℤ),
    ∀ (M N : Modules R) (I J : CochainComplex (Modules R) ℤ)
      (hbI : I.IsStrictlyGE 0) (hbJ : J.IsStrictlyGE 0)
      (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
      (κ : (CochainComplex.singleFunctor (Modules R) 0).obj N ⟶ J)
      (hi : QuasiIso ι) (hj : QuasiIso κ)
      (hI : ∀ q : ℤ, Injective (I.X q)) (hJ : ∀ q : ℤ, Injective (J.X q))
      (f : M ⟶ N) (φ : I ⟶ J),
    Homotopy (ι ≫ φ) ((CochainComplex.singleFunctor (Modules R) 0).map f ≫ κ) → ∀ n : ℕ,
      (ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom).map
          ((sectionCohomology R T n).map f) ≫ (e N J hbJ κ hj hJ n).hom =
        (e M I hbI ι hi hI n).hom ≫
          HomologicalComplex.homologyMap
            (((sectionsFunctor R U T h).mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ)

end Specs.AdvancedHomologicalAlgebra.MayerVietoris

/-! Canonical comparisons are defined independently of the candidate proofs.
They are the derived-functor unit comparison, followed by exact restriction
of scalars, and fix the meaning of all transported cohomology maps. -/
universe v u' v'
open CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData
section CanonicalComparison
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [EnoughInjectives A]

/-- The derived comparison unit is invertible on a termwise injective model. -/
theorem resolutionUnitIsIso (F : A ⥤ B) [F.Additive] (I : CochainComplex.Plus A)
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app I) := by
  letI := hI
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

def replacementIso (F : A ⥤ B) [F.Additive] (X I : CochainComplex.Plus A)
    (i : X ⟶ I) (hi : QuasiIso i.hom)
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) :
    F.rightDerivedFunctorPlus.obj (_root_.DerivedCategory.Plus.Q.obj X) ≅
      _root_.DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I) := by
  letI := resolutionUnitIsIso F I hI
  letI : IsIso (_root_.DerivedCategory.Plus.Q.map i) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso A) i ((CochainComplex.Plus.quasiIso_iff A i).mpr hi)
  exact F.rightDerivedFunctorPlus.mapIso (asIso (_root_.DerivedCategory.Plus.Q.map i)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app I)).symm

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

def resolutionComparison (F : A ⥤ B) [F.Additive] (M : A)
    (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I)
    (hi : QuasiIso i) (hI : ∀ q : ℤ, Injective (I.X q)) (n : ℕ) :
    (rightValue F n).obj M ≅ ((F.mapHomologicalComplex (.up ℤ)).obj I).homology (n : ℤ) := by
  let XI : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let II : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let ii : XI ⟶ II := (CochainComplex.plus A).homMk i
  exact (_root_.DerivedCategory.Plus.homologyFunctor B (n : ℤ)).mapIso
    (replacementIso F XI II ii hi hI) ≪≫
    (_root_.DerivedCategory.homologyFunctorFactors B (n : ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj I)

end CanonicalComparison

def canonicalModelIso {X : TopCat.{u}} (R : RingSheaf X) (U T : Opens X) (h : T ≤ U)
    (M : Modules R) (I : CochainComplex (Modules R) ℤ) (hb : I.IsStrictlyGE 0)
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
    (hi : QuasiIso ι) (hI : ∀ q : ℤ, Injective (I.X q)) (n : ℕ) :
    ((ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom).obj
      ((sectionCohomology R T n).obj M)) ≅ (sectionComplex R U T h I).homology (n : ℤ) := by
  letI := hb
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R T))
  let E := SheafOfModules.evaluation R (op T)
  let G := ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom
  exact G.mapIso (resolutionComparison E M I ι hi hI n) ≪≫
    ((((E.mapHomologicalComplex (.up ℤ)).obj I).sc (n : ℤ)).mapHomologyIso G).symm

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietorisData
/-- Restricting H^n(U,-) along the identity restriction of rings changes no module. -/
def sameOpenCohomologyIso {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) (n : ℕ) :
    sectionCohomology R U n ⋙ ModuleCat.restrictScalars
      (R.obj.map (homOfLE (show U ≤ U from le_rfl)).op).hom ≅ sectionCohomology R U n := by
  have hh : (R.obj.map (homOfLE (show U ≤ U from le_rfl)).op).hom =
      RingHom.id (sectionRing R U) := by
    change (R.obj.map (𝟙 (op U))).hom = _
    rw [R.obj.map_id]
    rfl
  exact isoWhiskerLeft _ (ModuleCat.restrictScalarsId' _ hh) ≪≫ Functor.rightUnitor _
end AdvancedHomologicalAlgebra.MayerVietorisData

namespace AdvancedHomologicalAlgebra.MayerVietorisData

variable {X : TopCat.{u}} (R : RingSheaf X)

/-- An augmented injective cochain resolution with its nonnegative bound. -/
structure ResolutionModel (M : Modules R) where
  complex : CochainComplex (Modules R) ℤ
  bounded : complex.IsStrictlyGE 0
  augmentation : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ complex
  quasiIso : QuasiIso augmentation
  injective : ∀ q : ℤ, Injective (complex.X q)

/-- Fixed HA-H01 cohomology, viewed over the ring of the ambient open. -/
def localCohomology (U T : Opens X) (h : T ≤ U) (n : ℕ) :
    Modules R ⥤ ModuleCat.{u} (sectionRing R U) :=
  sectionCohomology R T n ⋙ ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom

variable (V W : Opens X) (m : ∀ M : Modules R, ResolutionModel R M)

/-- The fixed canonical comparison, simultaneously for every subopen. -/
def cohomologyComparison (T : Opens X) (h : T ≤ V ⊔ W) (M : Modules R) (n : ℕ) :
    (localCohomology R (V ⊔ W) T h n).obj M ≅
      (sectionComplex R (V ⊔ W) T h (m M).complex).homology (n : ℤ) :=
  AdvancedHomologicalAlgebra.MayerVietoris.canonicalModelIso R (V ⊔ W) T h M
    (m M).complex (m M).bounded (m M).augmentation (m M).quasiIso (m M).injective n

/-- Restriction on the fixed derived cohomology modules. -/
def cohomologyRestriction (T S : Opens X) (hT : T ≤ V ⊔ W) (hS : S ≤ V ⊔ W)
    (h : S ≤ T) (M : Modules R) (n : ℕ) :
    (localCohomology R (V ⊔ W) T hT n).obj M ⟶
      (localCohomology R (V ⊔ W) S hS n).obj M :=
  (cohomologyComparison R V W m T hT M n).hom ≫
    HomologicalComplex.homologyMap
      (((res R (V ⊔ W) T S hT hS h).mapHomologicalComplex (.up ℤ)).app (m M).complex)
      (n : ℤ) ≫
    (cohomologyComparison R V W m S hS M n).inv

/-- The pair of restrictions from the union. -/
def cohomologyAlpha (M : Modules R) (n : ℕ) :=
  biprod.lift
    (cohomologyRestriction R V W m (V ⊔ W) V le_rfl le_sup_left le_sup_left M n)
    (cohomologyRestriction R V W m (V ⊔ W) W le_rfl le_sup_right le_sup_right M n)

/-- Restriction from V minus restriction from W. -/
def cohomologyBeta (M : Modules R) (n : ℕ) :=
  biprod.desc
    (cohomologyRestriction R V W m V (V ⊓ W) le_sup_left
      (inf_le_left.trans le_sup_left) inf_le_left M n)
    (-(cohomologyRestriction R V W m W (V ⊓ W) le_sup_right
      (inf_le_left.trans le_sup_left) inf_le_right M n))

variable (hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact)

/-- The connecting morphism, with the lift-and-differential convention. -/
def cohomologyDelta (M : Modules R) (n : ℕ) :=
  (cohomologyComparison R V W m (V ⊓ W) (inf_le_left.trans le_sup_left) M n).hom ≫
    (hS M).δ (n : ℤ) ((n : ℤ) + 1) rfl ≫
    (cohomologyComparison R V W m (V ⊔ W) le_rfl M (n + 1)).inv

/-- Each consecutive five-arrow window of the two-open sequence. -/
def cohomologySequence (M : Modules R) (n : ℕ) :
    ComposableArrows (ModuleCat.{u} (sectionRing R (V ⊔ W))) 5 :=
  ComposableArrows.mk₅ (cohomologyAlpha R V W m M n) (cohomologyBeta R V W m M n)
    (cohomologyDelta R V W m hS M n) (cohomologyAlpha R V W m M (n + 1))
    (cohomologyBeta R V W m M (n + 1))

end AdvancedHomologicalAlgebra.MayerVietorisData

namespace AdvancedHomologicalAlgebra.MayerVietorisData
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)
  (m : ∀ M : Modules R, ResolutionModel R M)
  (hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact)

/-- The pair of restrictions with the usual cohomology module at the union. -/
def directAlpha (M : Modules R) (n : ℕ) :=
  (sameOpenCohomologyIso R (V ⊔ W) n).inv.app M ≫ cohomologyAlpha R V W m M n

/-- The connecting morphism with the usual cohomology module at the union. -/
def directDelta (M : Modules R) (n : ℕ) :=
  cohomologyDelta R V W m hS M n ≫ (sameOpenCohomologyIso R (V ⊔ W) (n + 1)).hom.app M

/-- The two-open sequence on the usual union cohomology modules. -/
def directSequence (M : Modules R) (n : ℕ) :
    ComposableArrows (ModuleCat.{u} (sectionRing R (V ⊔ W))) 5 :=
  ComposableArrows.mk₅ (directAlpha R V W m M n) (cohomologyBeta R V W m M n)
    (directDelta R V W m hS M n) (directAlpha R V W m M (n + 1))
    (cohomologyBeta R V W m M (n + 1))

end AdvancedHomologicalAlgebra.MayerVietorisData


namespace Specs.AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData

/-- HA-H05 on the fixed HA-H01 cohomology modules: the sequence starts at
H⁰ of the union, is exact in every degree, and is natural in the sheaf.
The definitions of the arrows fix the two restrictions, their difference,
and the positive lift-and-differential boundary. -/
def naturalLongExactType : Prop := ∀ {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X),
  ∃ (m : ∀ M : Modules R, ResolutionModel R M)
    (hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact),
    (∀ M : Modules R, Mono (directAlpha R V W m M 0)) ∧
    (∀ (M : Modules R) (n : ℕ), (directSequence R V W m hS M n).Exact) ∧
    (∀ (M N : Modules R) (f : M ⟶ N) (n : ℕ),
      (sectionCohomology R (V ⊔ W) n).map f ≫ directAlpha R V W m N n =
        directAlpha R V W m M n ≫
          biprod.map ((localCohomology R (V ⊔ W) V le_sup_left n).map f)
            ((localCohomology R (V ⊔ W) W le_sup_right n).map f) ∧
      biprod.map ((localCohomology R (V ⊔ W) V le_sup_left n).map f)
          ((localCohomology R (V ⊔ W) W le_sup_right n).map f) ≫
        cohomologyBeta R V W m N n =
        cohomologyBeta R V W m M n ≫
          (localCohomology R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f ∧
      (localCohomology R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f ≫
        directDelta R V W m hS N n =
        directDelta R V W m hS M n ≫ (sectionCohomology R (V ⊔ W) (n + 1)).map f)

end Specs.AdvancedHomologicalAlgebra.MayerVietoris
