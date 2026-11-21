import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MayerVietoris

/-! The two-open construction over the original section rings (HA-H05). -/

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)

universe a u r

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentData

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- The opens are labeled by those of the common-universe site, using the
order isomorphism. Thus the original two opens range independently over all opens. -/
abbrev Open := Opens (liftedSpace.{max a u r} X)

abbrev originalOpen (T : Open.{a,u,r} (X := X)) : Opens X := opensEquiv X T

abbrev Sections (U : Open.{a,u,r} (X := X)) :=
  SectionModules.{a} R (originalOpen.{a,u,r} U)

abbrev Sc (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) : Sections.{a,u,r} R T ⥤ Sections.{a,u,r} R U :=
  restrictSectionScalars.{a} X R (homOfLE ((opensEquiv X).monotone h))

abbrev E (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) :
    AmbientSheaves.{a} R ⥤ Sections.{a,u,r} R U :=
  sectionsValue.{a} R (originalOpen.{a,u,r} T) ⋙ Sc.{a,u,r} R U T h

/-- Actual restrictions of sections, linear over the original union ring. -/
def res (U T S : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hS : S ≤ U) (h : S ≤ T) :
    E.{a,u,r} R U T hT ⟶ E.{a,u,r} R U S hS where
  app M := ModuleCat.ofHom
    (X := (E.{a,u,r} R U T hT).obj M) (Y := (E.{a,u,r} R U S hS).obj M)
    { toFun := M.val.map (homOfLE ((opensEquiv X).monotone h)).op
      map_add' := map_add _
      map_smul' c s := by
        change M.val.map (homOfLE ((opensEquiv X).monotone h)).op
          (R.obj.map (homOfLE ((opensEquiv X).monotone hT)).op c •
            (show M.val.obj (op (originalOpen.{a,u,r} T)) from s)) =
          R.obj.map (homOfLE ((opensEquiv X).monotone hS)).op c • _
        rw [M.val.map_smul]
        congr 1
        rw [← RingCat.comp_apply, ← R.obj.map_comp]
        rfl }
  naturality M N f := by
    ext s
    exact (PresheafOfModules.naturality_apply f.val (homOfLE ((opensEquiv X).monotone h)).op s).symm

@[simp] theorem res_comp (U T S P : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hS : S ≤ U)
    (hP : P ≤ U) (h : S ≤ T) (k : P ≤ S) (M : AmbientSheaves.{a} R) :
    (res.{a,u,r} R U T S hT hS h).app M ≫ (res.{a,u,r} R U S P hS hP k).app M =
      (res.{a,u,r} R U T P hT hP (k.trans h)).app M := by
  ext s
  exact (M.val.map_comp_apply (homOfLE ((opensEquiv X).monotone h)).op
    (homOfLE ((opensEquiv X).monotone k)).op s).symm

abbrev K (U T : Open.{a,u,r} (X := X)) (h : T ≤ U)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) :=
  ((E.{a,u,r} R U T h).mapHomologicalComplex (.up ℤ)).obj I

abbrev kRes (U T S : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hS : S ≤ U) (h : S ≤ T)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) : K.{a,u,r} R U T hT I ⟶ K.{a,u,r} R U S hS I :=
  ((res.{a,u,r} R U T S hT hS h).mapHomologicalComplex (.up ℤ)).app I

variable (V W : Open.{a,u,r} (X := X))

abbrev A (I : CochainComplex (AmbientSheaves.{a} R) ℤ) := K.{a,u,r} R (V ⊔ W) (V ⊔ W) le_rfl I
abbrev B (I : CochainComplex (AmbientSheaves.{a} R) ℤ) := K.{a,u,r} R (V ⊔ W) V le_sup_left I
abbrev C (I : CochainComplex (AmbientSheaves.{a} R) ℤ) := K.{a,u,r} R (V ⊔ W) W le_sup_right I
abbrev D (I : CochainComplex (AmbientSheaves.{a} R) ℤ) :=
  K.{a,u,r} R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) I

abbrev fV (I : CochainComplex (AmbientSheaves.{a} R) ℤ) : A.{a,u,r} R V W I ⟶ B.{a,u,r} R V W I :=
  kRes.{a,u,r} R _ _ _ le_rfl le_sup_left le_sup_left I
abbrev fW (I : CochainComplex (AmbientSheaves.{a} R) ℤ) : A.{a,u,r} R V W I ⟶ C.{a,u,r} R V W I :=
  kRes.{a,u,r} R _ _ _ le_rfl le_sup_right le_sup_right I
abbrev gV (I : CochainComplex (AmbientSheaves.{a} R) ℤ) : B.{a,u,r} R V W I ⟶ D.{a,u,r} R V W I :=
  kRes.{a,u,r} R _ _ _ le_sup_left (inf_le_left.trans le_sup_left) inf_le_left I
abbrev gW (I : CochainComplex (AmbientSheaves.{a} R) ℤ) : C.{a,u,r} R V W I ⟶ D.{a,u,r} R V W I :=
  kRes.{a,u,r} R _ _ _ le_sup_right (inf_le_left.trans le_sup_left) inf_le_right I

/-- The row of the actual section complexes, with the difference in the
specified order. -/
def row (I : CochainComplex (AmbientSheaves.{a} R) ℤ) :
    ShortComplex (CochainComplex (Sections.{a,u,r} R (V ⊔ W)) ℤ) where
  X₁ := A.{a,u,r} R V W I
  X₂ := B.{a,u,r} R V W I ⊞ C.{a,u,r} R V W I
  X₃ := D.{a,u,r} R V W I
  f := biprod.lift (fV.{a,u,r} R V W I) (fW.{a,u,r} R V W I)
  g := biprod.desc (gV.{a,u,r} R V W I) (-gW.{a,u,r} R V W I)
  zero := by
    rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero]
    apply HomologicalComplex.Hom.ext
    funext n
    change (res.{a,u,r} R _ _ V le_rfl le_sup_left le_sup_left).app (I.X n) ≫
      (res.{a,u,r} R _ V (V ⊓ W) le_sup_left (inf_le_left.trans le_sup_left) inf_le_left).app (I.X n) =
      (res.{a,u,r} R _ _ W le_rfl le_sup_right le_sup_right).app (I.X n) ≫
      (res.{a,u,r} R _ W (V ⊓ W) le_sup_right (inf_le_left.trans le_sup_left) inf_le_right).app (I.X n)
    simp

/-- Every map of ambient complexes induces a map of the two-open rows. -/
def rowMap {I J : CochainComplex (AmbientSheaves.{a} R) ℤ} (φ : I ⟶ J) :
    row.{a,u,r} R V W I ⟶ row.{a,u,r} R V W J where
  τ₁ := ((E.{a,u,r} R (V ⊔ W) (V ⊔ W) le_rfl).mapHomologicalComplex (.up ℤ)).map φ
  τ₂ := biprod.map
    (((E.{a,u,r} R (V ⊔ W) V le_sup_left).mapHomologicalComplex (.up ℤ)).map φ)
    (((E.{a,u,r} R (V ⊔ W) W le_sup_right).mapHomologicalComplex (.up ℤ)).map φ)
  τ₃ := ((E.{a,u,r} R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left)).mapHomologicalComplex (.up ℤ)).map φ
  comm₁₂ := by
    apply biprod.hom_ext <;> simp only [row, Category.assoc, biprod.lift_fst, biprod.lift_snd,
      biprod.map_fst, biprod.map_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc]
    all_goals exact NatTrans.naturality _ φ
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp only [row, biprod.inl_desc, biprod.inr_desc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.inl_map_assoc, biprod.inr_map_assoc,
      Preadditive.neg_comp, Preadditive.comp_neg]
    · exact NatTrans.naturality _ φ
    · exact congrArg Neg.neg (NatTrans.naturality _ φ)

structure Resolution (M : AmbientSheaves.{a} R) where
  I : CochainComplex (AmbientSheaves.{a} R) ℤ
  bounded : I.IsStrictlyGE 0
  i : (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).obj M ⟶ I
  quasiIso : QuasiIso i
  injective : ∀ q : ℤ, Injective (I.X q)

variable [EnoughInjectives (AmbientSheaves.{a} R)]

abbrev H (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) (n : ℕ) :
    AmbientSheaves.{a} R ⥤ Sections.{a,u,r} R U :=
  cohomologyValue.{a} R (originalOpen.{a,u,r} T) n ⋙ Sc.{a,u,r} R U T h

/-- The canonical comparison from model cohomology to the HA-H01-Carrier
cohomology, viewed over the union's section ring. -/
def modelMap (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) {M : AmbientSheaves.{a} R}
    (m : Resolution.{a,u,r} R M) (n : ℕ) : (K.{a,u,r} R U T h m.I).homology (n : ℤ) ⟶ (H.{a,u,r} R U T h n).obj M := by
  letI := m.bounded
  let F := sectionsValue.{a} R (originalOpen.{a,u,r} T)
  exact ((((F.mapHomologicalComplex (.up ℤ)).obj m.I).sc (n : ℤ)).mapHomologyIso
    (Sc.{a,u,r} R U T h)).hom ≫ (Sc.{a,u,r} R U T h).map (resolutionModelMap F m.i m.quasiIso n)

abbrev kLift (I : CochainComplex (AmbientSheaves.{a} R) ℤ) :=
  ((transport.{a} R).mapHomologicalComplex (.up ℤ)).obj I

abbrev scalars (U : Open.{a,u,r} (X := X)) := liftedScalars.{a} R U

instance (U : Open.{a,u,r} (X := X)) :
    PreservesBinaryBiproducts (scalars.{a,u,r} R U) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

open AdvancedHomologicalAlgebra.MayerVietorisData in
/-- The original and raised section functors agree after the change of
scalars at the base open. -/
def sectionTransport (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) :
    E.{a,u,r} R U T h ⋙ scalars.{a,u,r} R U ≅ transport.{a} R ⋙ sectionsFunctor (liftedRing.{a} R) U T h :=
  NatIso.ofComponents (fun M ↦ by
    let P := (E.{a,u,r} R U T h ⋙ scalars.{a,u,r} R U).obj M
    exact (LinearEquiv.refl _ P).toModuleIso)
    (by intros; ext x; rfl)

open AdvancedHomologicalAlgebra.MayerVietorisData in
def complexTransport (U T : Open.{a,u,r} (X := X)) (h : T ≤ U)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) :
    (((scalars.{a,u,r} R U).mapHomologicalComplex (.up ℤ)).obj (K.{a,u,r} R U T h I)) ≅
      sectionComplex (liftedRing.{a} R) U T h (kLift.{a,u,r} R I) :=
  (NatIso.mapHomologicalComplex (sectionTransport.{a,u,r} R U T h) (.up ℤ)).app I

end AdvancedHomologicalAlgebra.MayerVietorisIndependentData

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentData

open HomologicalComplex

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))

variable [EnoughInjectives (AmbientSheaves.{a} R)]

/-- The canonical identification for restriction of scalars along the
identity ring map at the union. -/
def unionIso (n : ℕ) :
    H.{a,u,r} R (V ⊔ W) (V ⊔ W) le_rfl n ≅ cohomologyValue.{a} R (originalOpen.{a,u,r} (V ⊔ W)) n := by
  let U := originalOpen.{a,u,r} (V ⊔ W)
  have h : (R.obj.map (𝟙 (op U))).hom = RingHom.id (R.obj.obj (op U)) := by
    rw [R.obj.map_id]
    rfl
  exact isoWhiskerLeft _ (ModuleCat.restrictScalarsId' _ h) ≪≫ Functor.rightUnitor _

variable {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)

abbrev Comparison :=
  ∀ (T : Open.{a,u,r} (X := X)) (h : T ≤ V ⊔ W) (n : ℕ),
    (K.{a,u,r} R (V ⊔ W) T h m.I).homology (n : ℤ) ≅ (H.{a,u,r} R (V ⊔ W) T h n).obj M

variable (e : Comparison.{a,u,r} R V W m)

abbrev eA (n : ℕ) := e (V ⊔ W) le_rfl n ≪≫ (unionIso.{a,u,r} R V W n).app M
abbrev eB (n : ℕ) := e V le_sup_left n
abbrev eC (n : ℕ) := e W le_sup_right n
abbrev eD (n : ℕ) := e (V ⊓ W) (inf_le_left.trans le_sup_left) n

/-- Pair of actual restrictions, computed in the original model. -/
def alpha (n : ℕ) :=
  biprod.lift
    ((eA.{a,u,r} R V W m e n).inv ≫ homologyMap (fV.{a,u,r} R V W m.I) (n : ℤ) ≫ (eB.{a,u,r} R V W m e n).hom)
    ((eA.{a,u,r} R V W m e n).inv ≫ homologyMap (fW.{a,u,r} R V W m.I) (n : ℤ) ≫ (eC.{a,u,r} R V W m e n).hom)

/-- Restriction from the first open minus restriction from the second. -/
def beta (n : ℕ) :=
  biprod.desc
    ((eB.{a,u,r} R V W m e n).inv ≫ homologyMap (gV.{a,u,r} R V W m.I) (n : ℤ) ≫ (eD.{a,u,r} R V W m e n).hom)
    (-((eC.{a,u,r} R V W m e n).inv ≫ homologyMap (gW.{a,u,r} R V W m.I) (n : ℤ) ≫ (eD.{a,u,r} R V W m e n).hom))

/-- The ordinary cohomology connector of the original row, transferred
through the canonical resolution comparisons. -/
def delta (h : (row.{a,u,r} R V W m.I).ShortExact) (n : ℕ) :=
  (eD.{a,u,r} R V W m e n).inv ≫ h.δ (n : ℤ) ((n : ℤ) + 1) rfl ≫ (eA.{a,u,r} R V W m e (n + 1)).hom

def cohomologySequence (h : (row.{a,u,r} R V W m.I).ShortExact) (n : ℕ) :
    ComposableArrows (Sections.{a,u,r} R (V ⊔ W)) 5 :=
  ComposableArrows.mk₅ (alpha.{a,u,r} R V W m e n) (beta.{a,u,r} R V W m e n) (delta.{a,u,r} R V W m e h n)
    (alpha.{a,u,r} R V W m e (n + 1)) (beta.{a,u,r} R V W m e (n + 1))

end AdvancedHomologicalAlgebra.MayerVietorisIndependentData

namespace Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open AdvancedHomologicalAlgebra.MayerVietorisIndependentData

/-- The independent-level section row is short exact for flasque terms. -/
def flasqueRowType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ),
    (∀ q : ℤ, IsFlasque R (I.X q)) → (row.{a,u,r} R V W I).ShortExact

/-- Positive lift-and-differentiate formula, in the original section
complexes and over the original ring. -/
def liftDifferentialType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ)
    (h : (row.{a,u,r} R V W I).ShortExact) (n : ℤ)
    (P : Sections.{a,u,r} R (V ⊔ W))
    (c : P ⟶ (row.{a,u,r} R V W I).X₃.X n)
    (hc : c ≫ (row.{a,u,r} R V W I).X₃.d n (n + 1) = 0)
    (b : P ⟶ (row.{a,u,r} R V W I).X₂.X n)
    (hb : b ≫ (row.{a,u,r} R V W I).g.f n = c)
    (z : P ⟶ (row.{a,u,r} R V W I).X₁.X (n + 1))
    (hz : z ≫ (row.{a,u,r} R V W I).f.f (n + 1) = b ≫ (row.{a,u,r} R V W I).X₂.d n (n + 1)),
  (row.{a,u,r} R V W I).X₃.liftCycles c (n + 1) (by simp) hc ≫
      (row.{a,u,r} R V W I).X₃.homologyπ n ≫ h.δ n (n + 1) rfl =
    (row.{a,u,r} R V W I).X₁.liftCycles z (n + 2)
      (by apply (ComplexShape.up ℤ).next_eq'; change (n + 1) + 1 = n + 2; omega) (by
      have := h.mono_f
      rw [← cancel_mono ((row.{a,u,r} R V W I).f.f (n + 2)), Category.assoc,
        ← (row.{a,u,r} R V W I).f.comm, reassoc_of% hz,
        HomologicalComplex.d_comp_d, comp_zero, zero_comp]) ≫
      (row.{a,u,r} R V W I).X₁.homologyπ (n + 1)

/-- The section models have zero cohomology in every negative degree. -/
def negativeModelType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U T : Open.{a,u,r} (X := X)) (h : T ≤ U)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) [I.IsStrictlyGE 0] (n : ℤ),
    n < 0 → IsZero ((K.{a,u,r} R U T h I).homology n)

/-- The original cohomologies, and their maps, on any ambient injective
resolution. -/
def sequenceType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    [EnoughInjectives (AmbientSheaves.{a} R)]
    (M : AmbientSheaves.{a} R) (m : Resolution.{a,u,r} R M),
  ∃ (h : (row.{a,u,r} R V W m.I).ShortExact) (e : Comparison.{a,u,r} R V W m),
    (∀ T hT n, (e T hT n).hom = modelMap.{a,u,r} R (V ⊔ W) T hT m n) ∧
    Mono (alpha.{a,u,r} R V W m e 0) ∧
    ∀ n : ℕ, (cohomologySequence.{a,u,r} R V W m e h n).Exact

end Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open AdvancedHomologicalAlgebra.MayerVietorisIndependentData

/-- The original sequence is functorial in the coefficient sheaf, with
the maps on each term given by the fixed HA-H01-Carrier functors. -/
def naturalSequenceType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
  ∃ (m : ∀ M : AmbientSheaves.{a} R, Resolution.{a,u,r} R M)
    (h : ∀ M, (row.{a,u,r} R V W (m M).I).ShortExact)
    (e : ∀ M, Comparison.{a,u,r} R V W (m M)),
    (∀ M T hT n, (e M T hT n).hom = modelMap.{a,u,r} R (V ⊔ W) T hT (m M) n) ∧
    (∀ M, Mono (alpha.{a,u,r} R V W (m M) (e M) 0)) ∧
    (∀ M n, (cohomologySequence.{a,u,r} R V W (m M) (e M) (h M) n).Exact) ∧
    ∀ (M N : AmbientSheaves.{a} R) (f : M ⟶ N) (n : ℕ),
      let U := V ⊔ W
      let fA := (cohomologyValue.{a} R (originalOpen.{a,u,r} U) n).map f
      let fA' := (cohomologyValue.{a} R (originalOpen.{a,u,r} U) (n + 1)).map f
      let fB := (H.{a,u,r} R U V le_sup_left n).map f
      let fC := (H.{a,u,r} R U W le_sup_right n).map f
      let fD := (H.{a,u,r} R U (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f
      fA ≫ alpha.{a,u,r} R V W (m N) (e N) n =
        alpha.{a,u,r} R V W (m M) (e M) n ≫ biprod.map fB fC ∧
      biprod.map fB fC ≫ beta.{a,u,r} R V W (m N) (e N) n =
        beta.{a,u,r} R V W (m M) (e M) n ≫ fD ∧
      fD ≫ delta.{a,u,r} R V W (m N) (e N) (h N) n =
        delta.{a,u,r} R V W (m M) (e M) (h M) n ≫ fA'

end Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentData

open AdvancedHomologicalAlgebra.SheafTheory (sectionCohomology)
open AdvancedHomologicalAlgebra.MayerVietorisData (sectionsFunctor ResolutionModel)

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

abbrev raisedRestriction (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) :=
  ModuleCat.restrictScalars.{max a u r} ((liftedRing.{a} R).obj.map (homOfLE h).op).hom

variable [EnoughInjectives (AmbientSheaves.{a} R)]

/-- The comparison from HA-H01-Carrier, in the raised scalar coordinates. -/
abbrev SiteComparison (T : Open.{a,u,r} (X := X)) :=
  ∀ n : ℕ, cohomologyValue.{a} R (originalOpen.{a,u,r} T) n ⋙ scalars.{a,u,r} R T ≅
    transport.{a} R ⋙ sectionCohomology (liftedRing.{a} R) T n

/-- The same comparison over the union ring, with the two ways to restrict
scalars identified via the actual section-ring equivalences. -/
def localSiteComparison (U T : Open.{a,u,r} (X := X)) (h : T ≤ U)
    (s : SiteComparison.{a,u,r} R T) (n : ℕ) :
    H.{a,u,r} R U T h n ⋙ scalars.{a,u,r} R U ≅
      transport.{a} R ⋙ MayerVietorisData.localCohomology (liftedRing.{a} R) U T h n :=
  isoWhiskerRight (s n) (raisedRestriction.{a,u,r} R U T h)

variable {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)

abbrev raisedAugmentation :=
  mapAugmentation (transport.{a} R) m.i

/-- The raised resolution uses the transported complex and augmentation. -/
def raisedResolution (hi : QuasiIso (raisedAugmentation.{a,u,r} R m))
    (hI : ∀ q : ℤ, Injective ((kLift.{a,u,r} R m.I).X q)) :
    ResolutionModel (liftedRing.{a} R) ((transport.{a} R).obj M) := by
  letI := m.bounded
  exact ⟨kLift.{a,u,r} R m.I, inferInstance, raisedAugmentation.{a,u,r} R m, hi, hI⟩


open AdvancedHomologicalAlgebra.SheafTheory (Modules)
open HomologicalComplex

section CommonSequence

variable (V W : Open.{a,u,r} (X := X))
  {N : Modules (liftedRing.{a} R)} (l : ResolutionModel (liftedRing.{a} R) N)

/-- The comparison used in HA-H05, written for an individual resolution. -/
abbrev commonModelIso (T : Open.{a,u,r} (X := X)) (h : T ≤ V ⊔ W) (n : ℕ) :=
  (MayerVietoris.canonicalModelIso (liftedRing.{a} R) (V ⊔ W) T h
    N l.complex l.bounded l.augmentation l.quasiIso l.injective n).symm

abbrev commonUnionIso (n : ℕ) :=
  commonModelIso.{a,u,r} R V W l (V ⊔ W) le_rfl n ≪≫
    (MayerVietorisData.sameOpenCohomologyIso (liftedRing.{a} R) (V ⊔ W) n).app N

abbrev commonRes (T S : Open.{a,u,r} (X := X)) (hT : T ≤ V ⊔ W) (hS : S ≤ V ⊔ W)
    (h : S ≤ T) :=
  ((MayerVietorisData.res (liftedRing.{a} R) (V ⊔ W) T S hT hS h).mapHomologicalComplex
    (.up ℤ)).app l.complex

def commonAlpha (n : ℕ) :=
  biprod.lift
    ((commonUnionIso.{a,u,r} R V W l n).inv ≫
      homologyMap (commonRes.{a,u,r} R V W l (V ⊔ W) V le_rfl le_sup_left le_sup_left) (n : ℤ) ≫
      (commonModelIso.{a,u,r} R V W l V le_sup_left n).hom)
    ((commonUnionIso.{a,u,r} R V W l n).inv ≫
      homologyMap (commonRes.{a,u,r} R V W l (V ⊔ W) W le_rfl le_sup_right le_sup_right) (n : ℤ) ≫
      (commonModelIso.{a,u,r} R V W l W le_sup_right n).hom)

def commonBeta (n : ℕ) :=
  let e := commonModelIso.{a,u,r} R V W l (V ⊓ W) (inf_le_left.trans le_sup_left) n
  biprod.desc
    ((commonModelIso.{a,u,r} R V W l V le_sup_left n).inv ≫
      homologyMap (commonRes.{a,u,r} R V W l V (V ⊓ W) le_sup_left
        (inf_le_left.trans le_sup_left) inf_le_left) (n : ℤ) ≫ e.hom)
    (-((commonModelIso.{a,u,r} R V W l W le_sup_right n).inv ≫
      homologyMap (commonRes.{a,u,r} R V W l W (V ⊓ W) le_sup_right
        (inf_le_left.trans le_sup_left) inf_le_right) (n : ℤ) ≫ e.hom))

def commonDelta (h : (MayerVietorisData.complexRow (liftedRing.{a} R) V W l.complex).ShortExact) (n : ℕ) :=
  (commonModelIso.{a,u,r} R V W l (V ⊓ W) (inf_le_left.trans le_sup_left) n).inv ≫
    h.δ (n : ℤ) ((n : ℤ) + 1) rfl ≫ (commonUnionIso.{a,u,r} R V W l (n + 1)).hom

end CommonSequence

end AdvancedHomologicalAlgebra.MayerVietorisIndependentData

namespace Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open AdvancedHomologicalAlgebra.MayerVietorisIndependentData
open AdvancedHomologicalAlgebra.MayerVietorisData
  (complexRow directAlpha cohomologyBeta directDelta ResolutionModel)
open AdvancedHomologicalAlgebra.SheafTheory (Modules)

/-- The lifted labels reach every original pair, and send their union and
intersection to the actual original union and intersection. -/
def originalOpensType : Prop :=
  ∀ (X : TopCat.{u}) (V W : Opens X),
    ∃ V' W' : Open.{a,u,r} (X := X),
      originalOpen.{a,u,r} V' = V ∧ originalOpen.{a,u,r} W' = W ∧
      originalOpen.{a,u,r} (V' ⊔ W') = V ⊔ W ∧ originalOpen.{a,u,r} (V' ⊓ W') = V ⊓ W

/-- Comparison of short complexes induced by termwise section transport,
including the actual projections of the middle biproduct. -/
def sectionTransportType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ),
    let L := (scalars.{a,u,r} R (V ⊔ W)).mapHomologicalComplex (.up ℤ)
    ∃ e : (row.{a,u,r} R V W I).map L ≅ complexRow (liftedRing.{a} R) V W (kLift.{a,u,r} R I),
      e.hom.τ₁ = (complexTransport.{a,u,r} R (V ⊔ W) (V ⊔ W) le_rfl I).hom ∧
      e.hom.τ₃ = (complexTransport.{a,u,r} R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) I).hom ∧
      e.hom.τ₂ ≫ biprod.fst = L.map biprod.fst ≫
        (complexTransport.{a,u,r} R (V ⊔ W) V le_sup_left I).hom ∧
      e.hom.τ₂ ≫ biprod.snd = L.map biprod.snd ≫
        (complexTransport.{a,u,r} R (V ⊔ W) W le_sup_right I).hom

/-- The section transport and exact scalar change identify the positive
connectors in the original and common-universe cochain rows. -/
def modelBoundaryTransportType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ)
    (h : (row.{a,u,r} R V W I).ShortExact)
    (h' : (complexRow (liftedRing.{a} R) V W (kLift.{a,u,r} R I)).ShortExact)
    (n : ℤ),
    let S := scalars.{a,u,r} R (V ⊔ W)
    let eA := (A.{a,u,r} R V W I).sc (n + 1)
    let eD := (D.{a,u,r} R V W I).sc n
    h'.δ n (n + 1) rfl ≫ (eA.mapHomologyIso S).hom =
      (eD.mapHomologyIso S).hom ≫ S.map (h.δ n (n + 1) rfl)

/-- Comparison of the actual cohomology sequence with HA-H05. The source
and raised resolutions are related by the given site and ring transport.
The vertical isomorphisms are the augmented-model comparisons of
HA-H01-Carrier. -/
def cohomologyTransportType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    [EnoughInjectives (AmbientSheaves.{a} R)],
    ∃ s : ∀ T : Open.{a,u,r} (X := X), SiteComparison.{a,u,r} R T,
      (∀ T, IsResolutionComparison (sectionsValue.{a} R (originalOpen.{a,u,r} T))
        (sectionsValue.{0} (liftedRing.{a} R) T) (transport.{a} R)
        (scalars.{a,u,r} R T) (siteSectionsIso.{a} R T) (s T)) ∧
      ∀ (M : AmbientSheaves.{a} R) (m : Resolution.{a,u,r} R M),
        ∃ (q : QuasiIso (raisedAugmentation.{a,u,r} R m))
          (j : ∀ k : ℤ, Injective ((kLift.{a,u,r} R m.I).X k))
          (h' : (complexRow (liftedRing.{a} R) V W (kLift.{a,u,r} R m.I)).ShortExact)
          (h : (row.{a,u,r} R V W m.I).ShortExact)
          (e : Comparison.{a,u,r} R V W m),
          let U := V ⊔ W
          let S := scalars.{a,u,r} R U
          let l := raisedResolution.{a,u,r} R m q j
          (∀ T hT n, (e T hT n).hom = modelMap.{a,u,r} R U T hT m n) ∧
          ∀ n : ℕ,
            let a := (s U n).app M
            let a' := (s U (n + 1)).app M
            let b := (localSiteComparison.{a,u,r} R U V le_sup_left (s V) n).app M
            let c := (localSiteComparison.{a,u,r} R U W le_sup_right (s W) n).app M
            let d := (localSiteComparison.{a,u,r} R U (V ⊓ W)
              (inf_le_left.trans le_sup_left) (s (V ⊓ W)) n).app M
            let p := S.mapBiprod ((H.{a,u,r} R U V le_sup_left n).obj M)
              ((H.{a,u,r} R U W le_sup_right n).obj M) ≪≫ biprod.mapIso b c
            (S.map (alpha.{a,u,r} R V W m e n) ≫ p.hom =
              a.hom ≫ commonAlpha.{a,u,r} R V W l n) ∧
            (S.map (beta.{a,u,r} R V W m e n) ≫ d.hom =
              p.hom ≫ commonBeta.{a,u,r} R V W l n) ∧
            S.map (delta.{a,u,r} R V W m e h n) ≫ a'.hom =
              d.hom ≫ commonDelta.{a,u,r} R V W l h' n

/-- These individual-model formulas are the arrows of HA-H05 on the
same model. -/
def commonMapsType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    (l : ∀ N : Modules (liftedRing.{a} R), ResolutionModel (liftedRing.{a} R) N)
    (h' : ∀ N, (complexRow (liftedRing.{a} R) V W (l N).complex).ShortExact)
    (N : Modules (liftedRing.{a} R)) (n : ℕ),
    commonAlpha.{a,u,r} R V W (l N) n = directAlpha (liftedRing.{a} R) V W l N n ∧
    commonBeta.{a,u,r} R V W (l N) n = cohomologyBeta (liftedRing.{a} R) V W l N n ∧
    commonDelta.{a,u,r} R V W (l N) (h' N) n = directDelta (liftedRing.{a} R) V W l h' N n

end Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentData

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- The given coefficient sheaf, regarded in the adequate ambient category
over the same site and ring. -/
abbrev coefficientLift : SheafOfModules.{a} R ⥤ AmbientSheaves.{a} R :=
  liftSheafCoefficients.{max u r,u,r,a} R

variable [EnoughInjectives (AmbientSheaves.{a} R)]

/-- The actual cohomology functor on the given coefficients, with the action
of the union's section ring via its restriction map. -/
abbrev coefficientH (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) (n : ℕ) :
    SheafOfModules.{a} R ⥤ Sections.{a,u,r} R U :=
  coefficientCohomologyValue.{a,u,r} X R (originalOpen.{a,u,r} T) n ⋙ Sc.{a,u,r} R U T h

end AdvancedHomologicalAlgebra.MayerVietorisIndependentData

namespace Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open AdvancedHomologicalAlgebra.MayerVietorisIndependentData

/-- The sequence applies to every original carrier universe. The existence of
ambient injectives, used to construct the sequence, is part of the conclusion. -/
def coefficientNaturalSequenceType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X)),
  ∃ hInj : EnoughInjectives (AmbientSheaves.{a} R),
    letI := hInj
    let U := V ⊔ W
    let L := coefficientLift.{a,u,r} R
    ∃ (m : ∀ M : SheafOfModules.{a} R, Resolution.{a,u,r} R (L.obj M))
      (h : ∀ M, (row.{a,u,r} R V W (m M).I).ShortExact)
      (e : ∀ M, Comparison.{a,u,r} R V W (m M)),
      (∀ M T hT n, (e M T hT n).hom = modelMap.{a,u,r} R U T hT (m M) n) ∧
      (∀ M, Mono (alpha.{a,u,r} R V W (m M) (e M) 0)) ∧
      (∀ M n, (cohomologySequence.{a,u,r} R V W (m M) (e M) (h M) n).Exact) ∧
      ∀ (M N : SheafOfModules.{a} R) (f : M ⟶ N) (n : ℕ),
        let fA := (coefficientCohomologyValue.{a,u,r} X R (originalOpen.{a,u,r} U) n).map f
        let fA' := (coefficientCohomologyValue.{a,u,r} X R (originalOpen.{a,u,r} U) (n + 1)).map f
        let fB := (coefficientH.{a,u,r} R U V le_sup_left n).map f
        let fC := (coefficientH.{a,u,r} R U W le_sup_right n).map f
        let fD := (coefficientH.{a,u,r} R U (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f
        fA ≫ alpha.{a,u,r} R V W (m N) (e N) n =
          alpha.{a,u,r} R V W (m M) (e M) n ≫ biprod.map fB fC ∧
        biprod.map fB fC ≫ beta.{a,u,r} R V W (m N) (e N) n =
          beta.{a,u,r} R V W (m M) (e M) n ≫ fD ∧
        fD ≫ delta.{a,u,r} R V W (m N) (e N) (h N) n =
          delta.{a,u,r} R V W (m M) (e M) (h M) n ≫ fA'

end Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open AdvancedHomologicalAlgebra.MayerVietorisIndependentData

/-- The arrows computed on any two injective resolutions of the same
coefficient agree under the normalized identifications with derived cohomology. -/
def modelIndependenceType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))
    [EnoughInjectives (AmbientSheaves.{a} R)] (M : AmbientSheaves.{a} R)
    (m l : Resolution.{a,u,r} R M)
    (h : (row.{a,u,r} R V W m.I).ShortExact) (h' : (row.{a,u,r} R V W l.I).ShortExact)
    (e : Comparison.{a,u,r} R V W m) (e' : Comparison.{a,u,r} R V W l),
    (∀ T hT n, (e T hT n).hom = modelMap.{a,u,r} R (V ⊔ W) T hT m n) →
    (∀ T hT n, (e' T hT n).hom = modelMap.{a,u,r} R (V ⊔ W) T hT l n) →
    ∀ n : ℕ,
      alpha.{a,u,r} R V W m e n = alpha.{a,u,r} R V W l e' n ∧
      beta.{a,u,r} R V W m e n = beta.{a,u,r} R V W l e' n ∧
      delta.{a,u,r} R V W m e h n = delta.{a,u,r} R V W l e' h' n

end Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

/-! Coefficient enlargement on the original site and mixed-level naturality. -/

universe b c

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentData

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- Only the coefficient universe changes, leaving the site and section rings fixed. -/
abbrev enlargeCoefficients : AmbientSheaves.{b} R ⥤ AmbientSheaves.{max a b} R :=
  liftSheafCoefficients.{a,u,r,max b u r} R

abbrev commonCoefficientLift : SheafOfModules.{b} R ⥤ AmbientSheaves.{max a b} R :=
  liftSheafCoefficients.{max a b u r,u,r,b} R

abbrev enlargeSection (U : Opens X) : SectionModules.{b} R U ⥤ SectionModules.{max a b} R U :=
  ModuleCat.uliftFunctor.{a,max b u r} (R.obj.obj (op U))

abbrev enlargeComplex (I : CochainComplex (AmbientSheaves.{b} R) ℤ) :=
  ((enlargeCoefficients.{a,u,r,b} R).mapHomologicalComplex (.up ℤ)).obj I

/-- The identification of the section complexes is the identity on the actual
lifted sections. In particular the scalar ring is the original ring of U. -/
def enlargeSectionComplexIso (U T : Opens X) (h : T ≤ U)
    (I : CochainComplex (AmbientSheaves.{b} R) ℤ) :
    let L := (enlargeSection.{a,u,r,b} R U).mapHomologicalComplex (.up ℤ)
    let U₁ := liftedOpen.{b,u,r} U
    let T₁ := liftedOpen.{b,u,r} T
    let U₂ := liftedOpen.{max a b,u,r} U
    let T₂ := liftedOpen.{max a b,u,r} T
    L.obj (K.{b,u,r} R U₁ T₁ ((opensEquiv X).symm.monotone h) I) ≅
      K.{max a b,u,r} R U₂ T₂ ((opensEquiv X).symm.monotone h) (enlargeComplex.{a,u,r,b} R I) :=
  Iso.refl _

variable (V W : Opens X)

/-- The biproduct of the two maps of individual section groups, on the
section cohomology carriers. -/
def pairMap {S : Type r} [Ring S]
    {B C : ModuleCat.{b} S} {B' C' : ModuleCat.{c} S}
    (p : B → B') (q : C → C') (x : ↥(B ⊞ C)) : ↥(B' ⊞ C') :=
  (biprod.inl : B' ⟶ B' ⊞ C') (p ((biprod.fst : B ⊞ C ⟶ B) x)) +
    (biprod.inr : C' ⟶ B' ⊞ C') (q ((biprod.snd : B ⊞ C ⟶ C) x))

variable [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
    {M : AmbientSheaves.{b} R} {N : AmbientSheaves.{c} R}

/-- The three squares of the two-open sequence, with each row computed
from its own model. The maps on the four opens may have different source and
target carrier universes. -/
def arrowsCommute
    (m : Resolution.{b,u,r} R M) (l : Resolution.{c,u,r} R N)
    (hm : (row.{b,u,r} R (liftedOpen.{b,u,r} V) (liftedOpen.{b,u,r} W) m.I).ShortExact)
    (hl : (row.{c,u,r} R (liftedOpen.{c,u,r} V) (liftedOpen.{c,u,r} W) l.I).ShortExact)
    (em : Comparison.{b,u,r} R (liftedOpen.{b,u,r} V) (liftedOpen.{b,u,r} W) m)
    (el : Comparison.{c,u,r} R (liftedOpen.{c,u,r} V) (liftedOpen.{c,u,r} W) l)
    (p : ∀ (T : Opens X) (n : ℕ),
      (cohomologyValue.{b} R T n).obj M → (cohomologyValue.{c} R T n).obj N) : Prop :=
  ∀ n : ℕ,
    let V₁ := liftedOpen.{b,u,r} V
    let W₁ := liftedOpen.{b,u,r} W
    let V₂ := liftedOpen.{c,u,r} V
    let W₂ := liftedOpen.{c,u,r} W
    let q := pairMap
      (B := (H.{b,u,r} R (V₁ ⊔ W₁) V₁ le_sup_left n).obj M)
      (C := (H.{b,u,r} R (V₁ ⊔ W₁) W₁ le_sup_right n).obj M)
      (B' := (H.{c,u,r} R (V₂ ⊔ W₂) V₂ le_sup_left n).obj N)
      (C' := (H.{c,u,r} R (V₂ ⊔ W₂) W₂ le_sup_right n).obj N)
      (p V n) (p W n)
    (∀ x, q (alpha.{b,u,r} R V₁ W₁ m em n x) =
      alpha.{c,u,r} R V₂ W₂ l el n (p (V ⊔ W) n x)) ∧
    (∀ x, p (V ⊓ W) n (beta.{b,u,r} R V₁ W₁ m em n x) =
      beta.{c,u,r} R V₂ W₂ l el n (q x)) ∧
    (∀ x, p (V ⊔ W) (n + 1) (delta.{b,u,r} R V₁ W₁ m em hm n x) =
      delta.{c,u,r} R V₂ W₂ l el hl n (p (V ⊓ W) n x))

end AdvancedHomologicalAlgebra.MayerVietorisIndependentData

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentData

open HomologicalComplex

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- The same lift on the homology of a section complex. -/
def enlargeSectionHomologyIso (U T : Opens X) (h : T ≤ U)
    (I : CochainComplex (AmbientSheaves.{b} R) ℤ) (n : ℤ) :
    let U₁ := liftedOpen.{b,u,r} U
    let T₁ := liftedOpen.{b,u,r} T
    let U₂ := liftedOpen.{max a b,u,r} U
    let T₂ := liftedOpen.{max a b,u,r} T
    let K₁ := K.{b,u,r} R U₁ T₁ ((opensEquiv X).symm.monotone h) I
    let K₂ := K.{max a b,u,r} R U₂ T₂ ((opensEquiv X).symm.monotone h)
      (enlargeComplex.{a,u,r,b} R I)
    (enlargeSection.{a,u,r,b} R U).obj (K₁.homology n) ≅ K₂.homology n :=
  (((K.{b,u,r} R (liftedOpen.{b,u,r} U) (liftedOpen.{b,u,r} T)
    ((opensEquiv X).symm.monotone h) I).sc n).mapHomologyIso _).symm ≪≫
    (homologyFunctor _ (.up ℤ) n).mapIso (enlargeSectionComplexIso.{a,u,r,b} R U T h I)

/-- A native two-open sequence expressed by the comparison on any augmented
injective model, with its section computations fixed. -/
structure SequenceModel (V W : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] (M : AmbientSheaves.{b} R) where
  resolution : Resolution.{b,u,r} R M
  exactRow : (row.{b,u,r} R (liftedOpen.{b,u,r} V) (liftedOpen.{b,u,r} W) resolution.I).ShortExact
  comparison : Comparison.{b,u,r} R (liftedOpen.{b,u,r} V) (liftedOpen.{b,u,r} W) resolution
  normalized : ∀ T hT n, (comparison T hT n).hom =
    modelMap.{b,u,r} R (liftedOpen.{b,u,r} V ⊔ liftedOpen.{b,u,r} W) T hT resolution n

end AdvancedHomologicalAlgebra.MayerVietorisIndependentData

namespace Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open AdvancedHomologicalAlgebra.MayerVietorisIndependentData HomologicalComplex

set_option maxHeartbeats 2400000 in
/-- Raising only the coefficient carriers identifies each native Mayer--Vietoris
sequence with the sequence in the larger category. The comparison passes through
the exact row of the enlarged flasque model and preserves its augmentation. -/
def coefficientModelEnlargementType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]
    (s : ∀ T : Opens X, IndividualCohomologyComparison.{a,u,r,b} X R T),
    (∀ T, IsIndividualCohomologyComparison X R T (s T)) →
    ∀ (M : SheafOfModules.{b} R)
      (m : SequenceModel.{u,r,b} R V W ((coefficientLift.{b,u,r} R).obj M))
      (l : SequenceModel.{u,r,max a b} R V W ((commonCoefficientLift.{a,u,r,b} R).obj M)),
      let U := V ⊔ W
      let V₁ := liftedOpen.{b,u,r} V
      let W₁ := liftedOpen.{b,u,r} W
      let V₂ := liftedOpen.{max a b,u,r} V
      let W₂ := liftedOpen.{max a b,u,r} W
      let J := enlargeCoefficients.{a,u,r,b} R
      let I := m.resolution.I
      let I' := enlargeComplex.{a,u,r,b} R I
      let S := enlargeSection.{a,u,r,b} R U
      let L := S.mapHomologicalComplex (.up ℤ)
      let row₁ := row.{b,u,r} R V₁ W₁ I
      let row₂ := row.{max a b,u,r} R V₂ W₂ I'
      let row₃ := row.{max a b,u,r} R V₂ W₂ l.resolution.I
      ∃ (k : J.obj ((coefficientLift.{b,u,r} R).obj M) ≅
          (commonCoefficientLift.{a,u,r,b} R).obj M)
        (e : row₁.map L ≅ row₂) (φ : I' ⟶ l.resolution.I) (h : row₂.ShortExact),
        (∀ (T : (Opens X)ᵒᵖ) (x : (J.obj ((coefficientLift.{b,u,r} R).obj M)).val.obj T),
          k.hom.val.app T x = ULift.up x.down.down) ∧
        (let i := (CochainComplex.singleFunctor (AmbientSheaves.{max a b} R) 0).map k.inv ≫
            mapAugmentation J m.resolution.i
         QuasiIso i ∧ i ≫ φ = l.resolution.i) ∧
        (∀ q : ℤ, IsFlasque R (I'.X q)) ∧
        (e.hom.τ₁ = (enlargeSectionComplexIso.{a,u,r,b} R U U le_rfl I).hom) ∧
        (e.hom.τ₃ = (enlargeSectionComplexIso.{a,u,r,b} R U (V ⊓ W)
          (inf_le_left.trans le_sup_left) I).hom) ∧
        (e.hom.τ₂ ≫ biprod.fst = L.map biprod.fst ≫
          (enlargeSectionComplexIso.{a,u,r,b} R U V le_sup_left I).hom) ∧
        (e.hom.τ₂ ≫ biprod.snd = L.map biprod.snd ≫
          (enlargeSectionComplexIso.{a,u,r,b} R U W le_sup_right I).hom) ∧
        (∀ n : ℤ, S.map (m.exactRow.δ n (n + 1) rfl) ≫
            (enlargeSectionHomologyIso.{a,u,r,b} R U U le_rfl I (n + 1)).hom =
          (enlargeSectionHomologyIso.{a,u,r,b} R U (V ⊓ W) (inf_le_left.trans le_sup_left) I n).hom ≫
            h.δ n (n + 1) rfl) ∧
        (∀ n : ℤ,
          let f : row₂ ⟶ row₃ := rowMap.{max a b,u,r} R V₂ W₂ φ
          h.δ n (n + 1) rfl ≫ homologyMap f.τ₁ (n + 1) =
            homologyMap f.τ₃ n ≫ l.exactRow.δ n (n + 1) rfl) ∧
        (∀ (T : Opens X) (hT : T ≤ U) (n : ℕ),
          let T₁ := liftedOpen.{b,u,r} T
          let T₂ := liftedOpen.{max a b,u,r} T
          let h₁ : T₁ ≤ V₁ ⊔ W₁ := (opensEquiv X).symm.monotone hT
          let h₂ : T₂ ≤ V₂ ⊔ W₂ := (opensEquiv X).symm.monotone hT
          ∀ x : (K.{b,u,r} R (V₁ ⊔ W₁) T₁ h₁ I).homology (n : ℤ),
            (s T n).hom.app M (ULift.up ((m.comparison T₁ h₁ n).hom x)) =
              (l.comparison T₂ h₂ n).hom
                (homologyMap (((E.{max a b,u,r} R (V₂ ⊔ W₂) T₂ h₂).mapHomologicalComplex
                  (.up ℤ)).map φ) (n : ℤ)
                  ((enlargeSectionHomologyIso.{a,u,r,b} R U T hT I (n : ℤ)).hom (ULift.up x)))) ∧
        arrowsCommute R V W m.resolution l.resolution m.exactRow l.exactRow m.comparison l.comparison
          (fun T n x ↦ (s T n).hom.app M (ULift.up x))

set_option maxHeartbeats 2400000 in
/-- All three arrows commute with the map of the given coefficients even
when their carriers are independently sized. The vertical arrows are the
actual lifted map conjugated by the normalized HA-H01-Carrier comparisons. -/
def sectionwiseNaturalityType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Opens X)
    [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
    [EnoughInjectives (AmbientSheaves.{max a b c} R)]
    (M : SheafOfModules.{b} R) (N : SheafOfModules.{c} R) (f : SectionwiseHom M N)
    (m : SequenceModel.{u,r,b} R V W ((coefficientLift.{b,u,r} R).obj M))
    (l : SequenceModel.{u,r,c} R V W ((coefficientLift.{c,u,r} R).obj N)),
    let f' : (commonCoefficientLift.{max a c,u,r,b} R).obj M ⟶
        (commonCoefficientLift.{max a b,u,r,c} R).obj N := f.lift.{max a u r}
    ∃ (s : ∀ T : Opens X, IndividualCohomologyComparison.{max a c,u,r,b} X R T)
      (t : ∀ T : Opens X, IndividualCohomologyComparison.{max a b,u,r,c} X R T)
      (p : ∀ (T : Opens X) (n : ℕ), (coefficientCohomologyValue.{b} X R T n).obj M →ₗ[R.obj.obj (op T)]
        (coefficientCohomologyValue.{c} X R T n).obj N),
      (∀ T, IsIndividualCohomologyComparison X R T (s T) ∧
        IsIndividualCohomologyComparison X R T (t T)) ∧
      (∀ (T : Opens X) (n : ℕ) (x : (coefficientCohomologyValue.{b} X R T n).obj M),
        (cohomologyValue.{max a b c} R T n).map f' ((s T n).hom.app M (ULift.up x)) =
          (t T n).hom.app N (ULift.up (p T n x))) ∧
      arrowsCommute R V W m.resolution l.resolution m.exactRow l.exactRow m.comparison l.comparison
        (fun T n ↦ p T n)

end Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
