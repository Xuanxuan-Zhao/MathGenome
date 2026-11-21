import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtShiftedHom
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveComplexReplacement

noncomputable section
set_option linter.checkUnivs false
set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u uG v
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra

namespace AdvancedHomologicalAlgebra.GroupDerivedInvariants

open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants
variable {k : Type u} {G : Type uG} [CommRing k] [Group G]

lemma trivial_single_smul (g : G) (b a : k) :
    (MonoidAlgebra.single g b) • trivialElement.{u,uG,v} k G a =
      trivialElement k G (b * a) := by
  apply (Representation.trivial k G (ULift.{max uG v} k)).asModuleEquiv.injective
  change (Representation.trivial k G (ULift.{max uG v} k)).asAlgebraHom
    (MonoidAlgebra.single g b) (ULift.up a) = ULift.up (b*a)
  simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply,
    Representation.trivial_apply]
  rfl

lemma trivial_base_smul (a b : k) :
    a • trivialElement.{u,uG,v} k G b = trivialElement k G (a*b) := by
  change (algebraMap k k[G] a) • trivialElement k G b = _
  simpa [MonoidAlgebra.coe_algebraMap] using trivial_single_smul.{u,uG,v} (1 : G) a b

/-- The inverse to evaluation sends m to a ↦ a m. -/
def fromInvariant (M : GroupModule.{u,uG,v} k G) (m : invariants k G M) :
    trivialModule k G ⟶ M := ModuleCat.ofHom
  { toFun := fun a => ((Representation.trivial k G (ULift.{max uG v} k)).asModuleEquiv a).down • m.val
    map_add' := by intro a b; simp only [map_add]; exact add_smul _ _ _
    map_smul' := by
      intro r a
      simp only [RingHom.id_apply]
      induction r using MonoidAlgebra.induction_on with
      | of g =>
          simp only [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of,
            Representation.trivial_apply]
          rw [smul_comm, MonoidAlgebra.of_apply, m.property g]
      | add r s hr hs =>
          simp only [add_smul, map_add] at *
          exact (add_smul _ _ _).trans (congrArg₂ (· + ·) hr hs)
      | smul b r hr =>
          simp only [Representation.asModuleEquiv_map_smul, map_smul, LinearMap.smul_apply] at *
          change (b * _ ) • m.val = _
          rw [mul_smul, hr, smul_assoc] }

/-- Evaluation at 1 lands in the actual fixed submodule. -/
def evaluationMap (M : GroupModule.{u,uG,v} k G) :
    (trivialModule k G ⟶ M) →ₗ[k] invariants k G M where
  toFun f := ⟨f.hom (trivialElement k G 1), fun g => by
    rw [← f.hom.map_smul, trivial_single_smul, one_mul]⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma fromInvariant_evaluation (M : GroupModule.{u,uG,v} k G) (f : trivialModule k G ⟶ M) :
    fromInvariant M (evaluationMap M f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  obtain ⟨⟨a⟩, rfl⟩ := (Representation.trivial k G (ULift.{max uG v} k)).asModuleEquiv.symm.surjective a
  change a • f.hom (trivialElement k G 1) = f.hom (trivialElement k G a)
  rw [← f.hom.map_smul_of_tower, trivial_base_smul, mul_one]

lemma evaluation_fromInvariant (M : GroupModule.{u,uG,v} k G) (m : invariants k G M) :
    evaluationMap M (fromInvariant M m) = m := by
  apply Subtype.ext
  change (1 : k) • m.val = m.val
  exact one_smul k m.val

def evaluationEquiv (M : GroupModule.{u,uG,v} k G) :
    (trivialModule k G ⟶ M) ≃ₗ[k] invariants k G M :=
  { evaluationMap M with
    invFun := fromInvariant M
    left_inv := fromInvariant_evaluation M
    right_inv := evaluation_fromInvariant M }

def evaluationIso : homFunctor.{u,uG,v} k G ≅ invariantsFunctor k G :=
  NatIso.ofComponents (fun M => (evaluationEquiv M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    rfl)

theorem evaluation : evaluationType.{u,uG,v} := by
  intro k G _ _
  exact ⟨evaluationIso, fun _ _ => rfl⟩

open CochainComplex HomComplex

private lemma fromInvariant_naturality {M N : GroupModule.{u,uG,v} k G}
    (f : M ⟶ N) (m : invariants k G M) :
    fromInvariant M m ≫ f = fromInvariant N (((invariantsFunctor k G).map f).hom m) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact f.hom.map_smul_of_tower _ _

/-- Evaluation identifies invariant cochains with Hom cochains, including
all differentials. -/
def invariantComplexIso (I : CochainComplex (GroupModule.{u,uG,v} k G) ℤ) :
    ((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj I ≅
      linearHomComplex k ((CochainComplex.singleFunctor _ 0).obj (trivialModule k G)) I := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => ((evaluationEquiv (I.X n)).symm.trans
      (Cochain.fromSingleLinearEquiv (R := k) (zero_add n)).symm).toModuleIso) ?_
  intro i j hij
  have hj : i+1=j := hij
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change δ i (i+1) (Cochain.fromSingleMk (fromInvariant (I.X i) m) (zero_add i)) =
    Cochain.fromSingleMk (fromInvariant (I.X (i+1))
      (((invariantsFunctor k G).map (I.d i (i+1))).hom m)) (zero_add (i+1))
  rw [Cochain.δ_fromSingleMk _ _ _ (i+1) (zero_add (i+1))]
  rw [fromInvariant_naturality]

private def homComplexPostcomp (K : CochainComplex (GroupModule.{u,uG,v} k G) ℤ)
    {I J : CochainComplex (GroupModule.{u,uG,v} k G) ℤ} (f : I ⟶ J) :
    linearHomComplex k K I ⟶ linearHomComplex k K J where
  f n := ModuleCat.ofHom
    { toFun := fun z => z.comp (Cochain.ofHom f) (add_zero n)
      map_add' := fun x y => Cochain.add_comp x y _ _
      map_smul' := fun r z => Cochain.smul_comp r z _ _ }
  comm' i j _ := by
    ext z
    exact δ_comp_ofHom z f j

private lemma invariantComplexIso_naturality
    {I J : CochainComplex (GroupModule.{u,uG,v} k G) ℤ} (f : I ⟶ J) :
    ((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map f ≫ (invariantComplexIso J).hom =
      (invariantComplexIso I).hom ≫
        homComplexPostcomp ((CochainComplex.singleFunctor _ 0).obj (trivialModule k G)) f := by
  ext n m
  change Cochain.fromSingleMk
      (fromInvariant (J.X n) (((invariantsFunctor k G).map (f.f n)).hom m)) (zero_add n) =
    (Cochain.fromSingleMk (fromInvariant (I.X n) m) (zero_add n)).comp
      (Cochain.ofHom f) (add_zero n)
  rw [← Cochain.fromSingleMk_postcomp, fromInvariant_naturality]

private def invariantClassEquiv (I : CochainComplex (GroupModule.{u,uG,v} k G) ℤ) (n : ℤ) :
    ((((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj I).homology n) ≃ₗ[k]
      CohomologyClass ((CochainComplex.singleFunctor _ 0).obj (trivialModule k G)) I n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) n).mapIso
    (invariantComplexIso I)).toLinearEquiv.trans (homologyLinearEquiv k _ I n)

private lemma homologyLinearEquiv_postcomp
    {K I J : CochainComplex (GroupModule.{u,uG,v} k G) ℤ} (f : I ⟶ J) (n : ℤ)
    (z : Cocycle K I n) :
    homologyLinearEquiv k K J n
      ((HomologicalComplex.homologyMap (homComplexPostcomp K f) n).hom
        ((homologyLinearEquiv k K I n).symm (CohomologyClass.mk z))) =
    CohomologyClass.mk (z.postcomp f) := by
  let hI := linearLeftHomologyData k K I n
  let hJ := linearLeftHomologyData k K J n
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat k) (.up ℤ) n).map
    (homComplexPostcomp K f)
  let γ := ShortComplex.leftHomologyMapData φ hI hJ
  have hz : γ.φK.hom z = z.postcomp f := by
    apply Subtype.ext
    exact congrArg (fun a => a.hom z) γ.commi
  have hπ : γ.φH.hom (CohomologyClass.mk z) = CohomologyClass.mk (z.postcomp f) := by
    have h := congrArg (fun a => a.hom z) γ.commπ
    change γ.φH.hom (CohomologyClass.mk z) = CohomologyClass.mk (γ.φK.hom z) at h
    simpa only [hz] using h
  change (((hI.homologyIso.inv ≫ ShortComplex.homologyMap φ) ≫ hJ.homologyIso.hom).hom
    (CohomologyClass.mk z)) = _
  rw [Category.assoc, γ.homologyMap_comm, Iso.inv_hom_id_assoc]
  exact hπ

private lemma invariantClassEquiv_naturality
    {I J : CochainComplex (GroupModule.{u,uG,v} k G) ℤ} (f : I ⟶ J) (n : ℤ)
    (z : Cocycle ((CochainComplex.singleFunctor _ 0).obj (trivialModule k G)) I n) :
    invariantClassEquiv J n
      ((HomologicalComplex.homologyMap
        (((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map f) n).hom
          ((invariantClassEquiv I n).symm (CohomologyClass.mk z))) =
    CohomologyClass.mk (z.postcomp f) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) n
  let F := (invariantsFunctor k G).mapHomologicalComplex (.up ℤ)
  let g := homComplexPostcomp ((CochainComplex.singleFunctor _ 0).obj (trivialModule k G)) f
  have h := congrArg H.map (invariantComplexIso_naturality f)
  simp only [Functor.map_comp] at h
  change H.map (F.map f) ≫ (H.mapIso (invariantComplexIso J)).hom =
    (H.mapIso (invariantComplexIso I)).hom ≫ H.map g at h
  have h' : (H.mapIso (invariantComplexIso I)).inv ≫ H.map (F.map f) ≫
      (H.mapIso (invariantComplexIso J)).hom = H.map g := by
    rw [h, Iso.inv_hom_id_assoc]
  change (homologyLinearEquiv k _ J n)
    (((H.mapIso (invariantComplexIso I)).inv ≫ H.map (F.map f) ≫
      (H.mapIso (invariantComplexIso J)).hom).hom
      ((homologyLinearEquiv k _ I n).symm (CohomologyClass.mk z))) = _
  rw [h']
  exact homologyLinearEquiv_postcomp f n z

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

theorem leftExact : leftExactType.{u,uG,v} := by
  intro k G _ _
  let : PreservesFiniteLimits
      (homFunctor.{u,uG,v} k G ⋙ forget (ModuleCat.{max u uG v} k)) := by
    change PreservesFiniteLimits (coyoneda.obj (Opposite.op (trivialModule k G)))
    infer_instance
  let : PreservesFiniteLimits (homFunctor.{u,uG,v} k G) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (forget (ModuleCat k))
  exact preservesFiniteLimits_of_natIso evaluationIso

theorem degreeZero : degreeZeroType.{u,uG,v} := by
  intro k G _ _
  let := leftExact k G
  let := ClassicalDerivedValues.rightZero _ _ (invariantsFunctor k G)
  exact ⟨(asIso (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightDegreeZeroUnit
    (invariantsFunctor k G))).symm⟩

open CategoryTheory.Functor

private abbrev boundedModel (I : CochainComplex (GroupModule.{u,uG,v} k G) ℤ)
    [I.IsStrictlyGE 0] : CochainComplex.Plus (GroupModule k G) := ⟨I, 0, inferInstance⟩

private abbrev localizedAugmentation {M : GroupModule.{u,uG,v} k G}
    {I : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) :
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M ⟶
      _root_.DerivedCategory.Plus.Q.obj (boundedModel I) :=
  _root_.DerivedCategory.Plus.ι.preimage (_root_.DerivedCategory.Q.map i)

private lemma localizedAugmentation_isIso {M : GroupModule.{u,uG,v} k G}
    {I : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) [QuasiIso i] :
    IsIso (localizedAugmentation i) := by
  have : IsIso (_root_.DerivedCategory.Plus.ι.map (localizedAugmentation i)) := by
    rw [Functor.map_preimage]
    infer_instance
  exact isIso_of_reflects_iso _ _root_.DerivedCategory.Plus.ι

private lemma injectiveUnit_isIso (I : CochainComplex (GroupModule.{u,uG,v} k G) ℤ)
    [I.IsStrictlyGE 0] (hI : ∀ q, Injective (I.X q)) :
    IsIso ((invariantsFunctor k G).rightDerivedFunctorPlusUnit.app (boundedModel I)) := by
  let := hI
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

private abbrev homologyFactors (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B]
    (n : ℤ) :
    (_root_.DerivedCategory.Plus.Q ⋙
      _root_.DerivedCategory.Plus.homologyFunctor B n) ≅
    CochainComplex.Plus.ι B ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (_root_.DerivedCategory.Plus.QCompιIso B) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (_root_.DerivedCategory.homologyFunctorFactors B n)

/-- Comparison with an injective resolution using the localized augmentation
and the canonical unit of the bounded-below derived functor. -/
def injectiveValueIso {M : GroupModule.{u,uG,v} k G}
    {I : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
    (cohomology k G n).obj M ≅
      (((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj I).homology (n : ℤ) := by
  let := hi
  let := localizedAugmentation_isIso i
  let := injectiveUnit_isIso I hI
  let F := invariantsFunctor k G
  let H := _root_.DerivedCategory.Plus.homologyFunctor (ModuleCat k) (n : ℤ)
  exact H.mapIso ((F.rightDerivedFunctorPlus.mapIso (asIso (localizedAugmentation i))) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (boundedModel I))).symm) ≪≫
    (homologyFactors (ModuleCat k) (n : ℤ)).app (F.mapCochainComplexPlus.obj (boundedModel I))

theorem injectiveValueIso_naturality {M N : GroupModule.{u,uG,v} k G}
    {I J : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (j : (CochainComplex.singleFunctor _ 0).obj N ⟶ J) (hj : QuasiIso j)
    (hI : ∀ q, Injective (I.X q)) (hJ : ∀ q, Injective (J.X q))
    (b : M ⟶ N) (g : I ⟶ J)
    (h : Homotopy (i ≫ g) ((CochainComplex.singleFunctor _ 0).map b ≫ j))
    (n : ℕ) :
    (cohomology k G n).map b ≫ (injectiveValueIso j hj hJ n).hom =
      (injectiveValueIso i hi hI n).hom ≫
        HomologicalComplex.homologyMap
          (((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map g) (n : ℤ) := by
  let F := invariantsFunctor k G
  let Q := _root_.DerivedCategory.Plus.Q (C := GroupModule k G)
  let R := F.rightDerivedFunctorPlus
  let H := _root_.DerivedCategory.Plus.homologyFunctor (ModuleCat k) (n : ℤ)
  let gb : boundedModel I ⟶ boundedModel J := ObjectProperty.homMk g
  have hs : (_root_.DerivedCategory.Plus.singleFunctor _ 0).map b ≫ localizedAugmentation j =
      localizedAugmentation i ≫ Q.map gb := by
    apply _root_.DerivedCategory.Plus.ι.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    change _root_.DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map b) ≫
        _root_.DerivedCategory.Q.map j =
      _root_.DerivedCategory.Q.map i ≫ _root_.DerivedCategory.Q.map g
    simpa only [Functor.map_comp] using
      (_root_.DerivedCategory.Q_map_eq_of_homotopy _ h).symm
  let := injectiveUnit_isIso I hI
  let := injectiveUnit_isIso J hJ
  have hu := F.rightDerivedFunctorPlusUnit.naturality gb
  change _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map gb) ≫
      F.rightDerivedFunctorPlusUnit.app (boundedModel J) =
    F.rightDerivedFunctorPlusUnit.app (boundedModel I) ≫ R.map (Q.map gb) at hu
  have hu' : R.map (Q.map gb) ≫ inv (F.rightDerivedFunctorPlusUnit.app (boundedModel J)) =
      inv (F.rightDerivedFunctorPlusUnit.app (boundedModel I)) ≫
        _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map gb) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hu, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  let e := homologyFactors (ModuleCat.{max u uG v} k) (n : ℤ)
  have hf := e.hom.naturality (F.mapCochainComplexPlus.map gb)
  change H.map (_root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map gb)) ≫
      e.hom.app (F.mapCochainComplexPlus.obj (boundedModel J)) =
    e.hom.app (F.mapCochainComplexPlus.obj (boundedModel I)) ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ) at hf
  have hcomp :
      R.map ((_root_.DerivedCategory.Plus.singleFunctor _ 0).map b) ≫
        R.map (localizedAugmentation j) ≫
          inv (F.rightDerivedFunctorPlusUnit.app (boundedModel J)) =
      R.map (localizedAugmentation i) ≫
        inv (F.rightDerivedFunctorPlusUnit.app (boundedModel I)) ≫
          _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map gb) := by
    rw [← R.map_comp_assoc, hs, R.map_comp, Category.assoc, hu']
  change H.map (R.map ((_root_.DerivedCategory.Plus.singleFunctor _ 0).map b)) ≫
      H.map (R.map (localizedAugmentation j) ≫
        inv (F.rightDerivedFunctorPlusUnit.app (boundedModel J))) ≫
      e.hom.app (F.mapCochainComplexPlus.obj (boundedModel J)) =
    (H.map (R.map (localizedAugmentation i) ≫
        inv (F.rightDerivedFunctorPlusUnit.app (boundedModel I))) ≫
      e.hom.app (F.mapCochainComplexPlus.obj (boundedModel I))) ≫
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)
  rw [← H.map_comp_assoc, hcomp]
  simp only [Functor.map_comp, Category.assoc, hf]

theorem injectiveComputation : injectiveComputationType.{u,uG,v} := by
  intro k G _ _ M I hb i hi hI n
  exact ⟨injectiveValueIso i hi hI n⟩

private theorem exists_injectiveExtEquiv {M : GroupModule.{u,uG,v} k G}
    {I : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
    ∃ e : CohomologyClass ((CochainComplex.singleFunctor _ 0).obj (trivialModule k G)) I
        (n : ℤ) ≃+ groupExt k G M n,
      ∀ x, e x = Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.injectiveClassMap
        (trivialModule k G) M I i hi (n : ℤ) x := by
  obtain ⟨e, he⟩ := ExtShiftedHom.injective_comparison (GroupModule k G)
    (trivialModule k G) M I i hi ⟨0, fun q hq => I.isZero_of_isStrictlyGE 0 q hq⟩ hI (n : ℤ)
  exact ⟨(homologyAddEquiv _ _ _).symm.trans e, he⟩

/-- The derived-invariants comparison computed on any supplied injective
resolution, using evaluation and the shifted derived class map. -/
def derivedExtVia {M : GroupModule.{u,uG,v} k G}
    {I : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
    ((cohomology k G n).obj M) ≃+ groupExt k G M n :=
  (injectiveValueIso i hi hI n).toLinearEquiv.toAddEquiv.trans
    ((invariantClassEquiv I (n : ℤ)).toAddEquiv.trans (exists_injectiveExtEquiv i hi hI n).choose)

theorem derivedExtVia_naturality {M N : GroupModule.{u,uG,v} k G}
    {I J : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (j : (CochainComplex.singleFunctor _ 0).obj N ⟶ J) (hj : QuasiIso j)
    (hI : ∀ q, Injective (I.X q)) (hJ : ∀ q, Injective (J.X q))
    (b : M ⟶ N) (g : I ⟶ J)
    (h : Homotopy (i ≫ g) ((CochainComplex.singleFunctor _ 0).map b ≫ j))
    (n : ℕ) (x : (cohomology k G n).obj M) :
    derivedExtVia j hj hJ n (((cohomology k G n).map b).hom x) =
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap (𝟙 (trivialModule k G)) b
        (n : ℤ) (derivedExtVia i hi hI n x) := by
  let y := (injectiveValueIso i hi hI n).hom.hom x
  obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (invariantClassEquiv I (n : ℤ) y)
  have hy : y = (invariantClassEquiv I (n : ℤ)).symm (CohomologyClass.mk z) :=
    (LinearEquiv.eq_symm_apply _).mpr hz.symm
  have hmap := congrArg (fun f => f.hom x) (injectiveValueIso_naturality i hi j hj hI hJ b g h n)
  change (injectiveValueIso j hj hJ n).hom.hom (((cohomology k G n).map b).hom x) =
    (HomologicalComplex.homologyMap
      (((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)).hom y at hmap
  change (exists_injectiveExtEquiv j hj hJ n).choose
      (invariantClassEquiv J (n : ℤ)
        ((injectiveValueIso j hj hJ n).hom.hom (((cohomology k G n).map b).hom x))) =
    Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap _ b (n : ℤ)
      ((exists_injectiveExtEquiv i hi hI n).choose (invariantClassEquiv I (n : ℤ) y))
  rw [hmap, ← hz, hy, invariantClassEquiv_naturality,
    (exists_injectiveExtEquiv j hj hJ n).choose_spec,
    (exists_injectiveExtEquiv i hi hI n).choose_spec]
  have hzid : z.precomp (𝟙 _) = z := by
    apply Subtype.ext
    exact Cochain.id_comp z.1
  have hh :=
    ExtShiftedHom.injective_natural (GroupModule k G) (trivialModule k G) (trivialModule k G)
      M N I J i j hi hj (𝟙 _) b g ⟨h⟩ (n : ℤ) z
  rw [CategoryTheory.Functor.map_id, hzid] at hh
  exact hh

private lemma derivedExtVia_map {M N : GroupModule.{u,uG,v} k G}
    {I J : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (j : (CochainComplex.singleFunctor _ 0).obj N ⟶ J) (hj : QuasiIso j)
    (hI : ∀ q, Injective (I.X q)) (hJ : ∀ q, Injective (J.X q))
    (b : M ⟶ N) (n : ℕ) (x : (cohomology k G n).obj M) :
    derivedExtVia j hj hJ n (((cohomology k G n).map b).hom x) =
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap (𝟙 (trivialModule k G)) b
        (n : ℤ) (derivedExtVia i hi hI n x) := by
  let := hi
  let : J.IsKInjective := (BoundedKModels.kInjective_iff _ _).mp
    (BoundedKModels.boundedBelow_injective _ J 0
      (fun q hq => J.isZero_of_isStrictlyGE 0 q hq) hJ)
  obtain ⟨g, ⟨hg⟩⟩ := ExtShiftedHom.injective_lift M N I J i j b
  exact derivedExtVia_naturality i hi j hj hI hJ b g hg n x

private structure InjectiveModel (M : GroupModule.{u,uG,v} k G) where
  complex : CochainComplex (GroupModule k G) ℤ
  bounded : complex.IsStrictlyGE 0
  augmentation : (CochainComplex.singleFunctor _ 0).obj M ⟶ complex
  quasiIso : QuasiIso augmentation
  injective : ∀ q, Injective (complex.X q)

private theorem injectiveModel_exists (M : GroupModule.{u,uG,v} k G) :
    Nonempty (InjectiveModel M) := by
  obtain ⟨I, i, _, hi, hI, hb⟩ := InjectiveComplexReplacement.replacement (GroupModule k G)
    ((CochainComplex.singleFunctor _ 0).obj M) 0 (by infer_instance)
  exact ⟨⟨I, hb, i, hi, hI⟩⟩

private def chooseInjectiveModel (M : GroupModule.{u,uG,v} k G) : InjectiveModel M :=
  (injectiveModel_exists M).some

/-- Comparison with Ext through an injective resolution of the coefficient. -/
def derivedExtEquiv (M : GroupModule.{u,uG,v} k G) (n : ℕ) :
    (cohomology k G n).obj M ≃+ groupExt k G M n := by
  let I := chooseInjectiveModel M
  let := I.bounded
  exact derivedExtVia I.augmentation I.quasiIso I.injective n

theorem derivedExtEquiv_naturality {M N : GroupModule.{u,uG,v} k G}
    (b : M ⟶ N) (n : ℕ) (x : (cohomology k G n).obj M) :
    derivedExtEquiv N n (((cohomology k G n).map b).hom x) =
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap (𝟙 (trivialModule k G)) b
        (n : ℤ) (derivedExtEquiv M n x) := by
  let I := chooseInjectiveModel M
  let J := chooseInjectiveModel N
  let := I.bounded
  let := J.bounded
  exact derivedExtVia_map I.augmentation I.quasiIso J.augmentation J.quasiIso
    I.injective J.injective b n x

/-- Every supplied injective resolution induces the same comparison with Ext. -/
theorem derivedExtVia_eq {M : GroupModule.{u,uG,v} k G}
    {I : CochainComplex (GroupModule k G) ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor _ 0).obj M ⟶ I) (hi : QuasiIso i)
    (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
    derivedExtVia i hi hI n = derivedExtEquiv M n := by
  let J := chooseInjectiveModel M
  let := J.bounded
  ext x
  change derivedExtVia i hi hI n x = derivedExtVia J.augmentation J.quasiIso J.injective n x
  simpa [Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap] using
    (derivedExtVia_map i hi J.augmentation J.quasiIso hI J.injective (𝟙 M) n x).symm

/-- The additive comparison with Ext is natural in the coefficient module. -/
theorem derivedExtNatural (k : Type u) (G : Type uG) [CommRing k] [Group G] (n : ℕ) :
    ∃ e : ∀ M : GroupModule.{u,uG,v} k G, (cohomology k G n).obj M ≃+ groupExt k G M n,
      ∀ (M N : GroupModule k G) (b : M ⟶ N) (x : (cohomology k G n).obj M),
        e N (((cohomology k G n).map b).hom x) =
          Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap (𝟙 (trivialModule k G)) b
            (n : ℤ) (e M x) :=
  ⟨fun M => derivedExtEquiv M n, fun _ _ b x => derivedExtEquiv_naturality b n x⟩

theorem derivedExt : derivedExtType.{u,uG,v} := by
  intro k G _ _ M n
  exact ⟨derivedExtEquiv M n⟩

private theorem exists_projectiveExtEquiv {M : GroupModule.{u,uG,v} k G}
    {P : CochainComplex (GroupModule k G) ℤ} [P.IsStrictlyLE 0]
    (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj (trivialModule k G))
    (hp : QuasiIso p) (hP : ∀ q, Projective (P.X q)) (n : ℕ) :
    ∃ e : (HomComplex P ((CochainComplex.singleFunctor _ 0).obj M)).homology (n : ℤ) ≃+
        groupExt k G M n,
      ∀ x, e ((homologyAddEquiv _ _ (n : ℤ)).symm x) =
        Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.projectiveClassMap
          (trivialModule k G) M P p hp (n : ℤ) x :=
  ExtShiftedHom.projective_comparison (GroupModule k G) (trivialModule k G) M P p hp
    ⟨0, fun q hq => P.isZero_of_isStrictlyLE 0 q hq⟩ hP (n : ℤ)

/-- The comparison from projective Hom cohomology to derived invariants. -/
def projectiveValueEquiv {M : GroupModule.{u,uG,v} k G}
    {P : CochainComplex (GroupModule k G) ℤ} [P.IsStrictlyLE 0]
    (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj (trivialModule k G))
    (hp : QuasiIso p) (hP : ∀ q, Projective (P.X q)) (n : ℕ) :
    (HomComplex P ((CochainComplex.singleFunctor _ 0).obj M)).homology (n : ℤ) ≃+
      (cohomology k G n).obj M :=
  (exists_projectiveExtEquiv (M := M) p hp hP n).choose.trans (derivedExtEquiv M n).symm

theorem projectiveValueEquiv_class {M : GroupModule.{u,uG,v} k G}
    {P : CochainComplex (GroupModule k G) ℤ} [P.IsStrictlyLE 0]
    (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj (trivialModule k G))
    (hp : QuasiIso p) (hP : ∀ q, Projective (P.X q)) (n : ℕ)
    (x : CohomologyClass P ((CochainComplex.singleFunctor _ 0).obj M) (n : ℤ)) :
    derivedExtEquiv M n (projectiveValueEquiv p hp hP n ((homologyAddEquiv _ _ (n : ℤ)).symm x)) =
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.projectiveClassMap
        (trivialModule k G) M P p hp (n : ℤ) x := by
  simpa only [projectiveValueEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply] using
    (exists_projectiveExtEquiv (M := M) p hp hP n).choose_spec x

/-- The comparison commutes with coefficient maps and every augmented lift
of the identity between projective resolutions. -/
theorem projectiveValueEquiv_naturality {M N : GroupModule.{u,uG,v} k G}
    {P P' : CochainComplex (GroupModule k G) ℤ} [P.IsStrictlyLE 0] [P'.IsStrictlyLE 0]
    (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj (trivialModule k G))
    (p' : P' ⟶ (CochainComplex.singleFunctor _ 0).obj (trivialModule k G))
    (hp : QuasiIso p) (hp' : QuasiIso p')
    (hP : ∀ q, Projective (P.X q)) (hP' : ∀ q, Projective (P'.X q))
    (n : ℕ) (b : M ⟶ N) (g : P' ⟶ P) (h : Homotopy (g ≫ p) p')
    (z : Cocycle P ((CochainComplex.singleFunctor _ 0).obj M) (n : ℤ)) :
    projectiveValueEquiv p' hp' hP' n ((homologyAddEquiv _ _ (n : ℤ)).symm
        (CohomologyClass.mk ((z.precomp g).postcomp ((CochainComplex.singleFunctor _ 0).map b)))) =
      ((cohomology k G n).map b).hom
        (projectiveValueEquiv p hp hP n ((homologyAddEquiv _ _ (n : ℤ)).symm
          (CohomologyClass.mk z))) := by
  apply (derivedExtEquiv N n).injective
  rw [projectiveValueEquiv_class, derivedExtEquiv_naturality, projectiveValueEquiv_class]
  have hg : Nonempty (Homotopy (g ≫ p)
      (p' ≫ (CochainComplex.singleFunctor _ 0).map (𝟙 (trivialModule k G)))) := by
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact ⟨h⟩
  exact ExtShiftedHom.projective_natural (GroupModule k G) (trivialModule k G)
    (trivialModule k G) M N P P' p p' hp hp' (𝟙 _) b g hg (n : ℤ) z

theorem projectiveComputation : projectiveComputationType.{u,uG,v} := by
  intro k G _ _ M P hb p hp hP n
  exact ⟨(projectiveValueEquiv (M := M) p hp hP n).symm⟩

end AdvancedHomologicalAlgebra.GroupDerivedInvariants

