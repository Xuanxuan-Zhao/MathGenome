import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupBarResolution
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupDerivedInvariants
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

noncomputable section
set_option linter.checkUnivs false
set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped ModuleCat.Algebra MonoidAlgebra TensorProduct
universe u uG uM
namespace AdvancedHomologicalAlgebra.GroupCochainComparison

section EqualUniverseCoordinates
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
variable (k G : Type u) [CommRing k] [Group G]

/-- The inverse homogeneous-to-free map on an arbitrary free generator. -/
lemma diagonal_inv_single (n : ℕ) (g : Fin n → G) (a : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom
      (Finsupp.single g (MonoidAlgebra.single a r)) =
      MonoidAlgebra.single (a • Fin.partialProd g) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step₁ : (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv.hom
      (Finsupp.single g (MonoidAlgebra.single a r)) =
      MonoidAlgebra.single a (1 : k) ⊗ₜ[k] MonoidAlgebra.single g r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single g a r
  rw [step₁]
  simp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso,
    Representation.Equiv.mk_symm, LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom,
    Action.tensorObj_V, Action.trivial_V, Functor.mapIso_inv, Rep.tensor_V, Rep.tensor_ρ,
    Iso.symm_inv, Functor.Monoidal.μIso_hom, Rep.μ_hom, MonoidalCategory.tensorIso_inv,
    Representation.linearizeTrivialIso, Rep.hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have h₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (a, g) ((1 : k) * r)
  have h₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) a g 1 r
  exact ((congrArg (fun z => Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv z) h₂).trans h₁).trans (by simp)

lemma basis_vertices (n : ℕ) (g : Fin n → G) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom
      (Finsupp.single g (MonoidAlgebra.single 1 1)) =
      MonoidAlgebra.single (vertices G g) 1 := by
  simpa [vertices] using diagonal_inv_single k G n g 1 1

def coordinates (M : Coeff k G) (n : ℕ) :=
  Rep.diagonalHomEquiv k G n (representation k G M)

lemma coordinates_apply (M : Coeff k G) (n : ℕ)
    (φ : GroupBar.B k G n ⟶ representation k G M) (g : Fin n → G) :
    coordinates k G M n φ g = φ.hom (MonoidAlgebra.single (vertices G g) 1) := by
  change φ.hom ((Rep.diagonalSuccIsoFree k G n).inv.hom
    (Finsupp.single g (MonoidAlgebra.single 1 1))) = _
  rw [basis_vertices]

theorem coordinates_spec : coordinatesType k G := by
  intro M n
  exact ⟨coordinates k G M n, coordinates_apply k G M n⟩

def moduleEvaluation (M : Coeff k G) (n : ℕ) :
    (Rep.toModuleMonoidAlgebra.obj (GroupBar.B k G n) ⟶ M) →ₗ[k]
      ((Fin n → G) → representation k G M) where
  toFun φ g := φ.hom ((GroupBar.B k G n).ρ.asModuleEquiv.symm
    (MonoidAlgebra.single (vertices G g) 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma moduleEvaluation_bijective (M : Coeff k G) (n : ℕ) :
    Function.Bijective (moduleEvaluation k G M n) := by
  let e := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
    (GroupBar.B k G n) M
  have h : (moduleEvaluation k G M n : _ → _) =
      (coordinates k G M n) ∘ e := by
    funext φ g
    rw [Function.comp_apply, coordinates_apply]
    rfl
  rw [h]
  exact (coordinates k G M n).bijective.comp e.bijective

def moduleCoordinates (M : Coeff k G) (n : ℕ) :=
  LinearEquiv.ofBijective (moduleEvaluation k G M n) (moduleEvaluation_bijective k G M n)

theorem moduleCoordinates_spec : moduleCoordinatesType k G := by
  intro M n
  exact ⟨moduleCoordinates k G M n, fun _ _ => rfl⟩

def homogeneousHomIso (M : Coeff k G) :
    homCochains k G M ≅ (Rep.barComplex k G).linearYonedaObj k (representation k G M) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (Linear.homCongr k (Rep.diagonalSuccIsoFree k G n) (Iso.refl _)).toModuleIso) ?_
  intro i j hij
  have hj : i+1=j := hij
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (Rep.barComplex k G).d (i+1) i ≫
      ((Rep.diagonalSuccIsoFree k G i).inv ≫ φ ≫ 𝟙 _) =
    (Rep.diagonalSuccIsoFree k G (i+1)).inv ≫
      ((Rep.standardComplex k G).d (i+1) i ≫ φ) ≫ 𝟙 _
  have h := Rep.barComplex.d_comp_diagonalSuccIsoFree_inv_eq k G i
  have hh := congrArg (fun t : Rep.free k G (Fin (i+1) → G) ⟶
      Rep.diagonal k G (i+1) => t ≫ φ) h
  simpa [Category.assoc, Rep.barComplex.d_def, ChainComplex.of.d] using hh

def complexIso (M : Coeff k G) : homCochains k G M ≅ cochains k G M :=
  homogeneousHomIso k G M ≪≫ (groupCohomology.inhomogeneousCochainsIso _).symm

lemma complexIso_components (M : Coeff k G) (n : ℕ) :
    (complexIso k G M).hom.f n = (coordinates k G M n).toModuleIso.hom := rfl

def naturalComplexIso : homogeneousCochainsFunctor k G ≅ cochainsFunctor k G :=
  NatIso.ofComponents (complexIso k G) (by
    intro M N b
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    funext g
    change coordinates k G N n (φ ≫ Rep.ofModuleMonoidAlgebra.map b) g =
      (Rep.ofModuleMonoidAlgebra.map b).hom (coordinates k G M n φ g)
    rw [coordinates_apply, coordinates_apply]
    rfl)

theorem complexComparison : complexType k G := by
  refine ⟨naturalComplexIso k G, ?_⟩
  intro M n φ g
  exact coordinates_apply k G M n φ g

theorem resolutionComparison : resolutionComparisonType k G :=
  ⟨GroupBar.resolution k G, complexComparison k G⟩

theorem differential : differentialType k G := by
  intro M n f g
  rw [groupCohomology.inhomogeneousCochains.d_def]
  change (representation k G M).ρ (g 0) (f (fun i => g i.succ)) +
    (∑ j : Fin (n+1), (-1 : k) ^ (j.val+1) • f (Fin.contractNth j (· * ·) g)) = _
  rw [Fin.sum_univ_castSucc]
  have hlast : Fin.contractNth (Fin.last n) (· * ·) g = fun i => g i.castSucc := by
    funext i
    simp [Fin.contractNth]
  simp only [differentialFormula, hlast, add_assoc, Fin.val_last, Fin.val_castSucc]

theorem degreeZero : zeroType k G := by
  intro M
  refine ⟨LinearEquiv.funUnique (Fin 0 → G) k (representation k G M), ?_⟩
  intro f
  rfl

theorem naturalCoordinates : naturalCoordinatesType k G := by
  intro M N b n φ g
  rfl


end EqualUniverseCoordinates

/-! The comparison with derived invariants is constructed from actual
injective models, so that its coefficient naturality is retained. -/
section DerivedComparison
open CochainComplex HomComplex
open CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
variable (k : Type u) [CommRing k]

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

lemma classToDerived_smul {A : Type*} [Category A] [Abelian A]
    [Linear k A] (K L : CochainComplex A ℤ) (n : ℤ) (r : k)
    (x : CohomologyClass K L n) :
    classToDerived K L n (r • x) = r • classToDerived K L n x := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_smul]
  simp [AdvancedHomologicalAlgebra.ExtShiftedHom.classToDerived_mk,
    Cocycle.equivHomShift_symm_smul]

def injectiveClassLinearEquiv {A : Type*} [Category A] [Abelian A] [Linear k A]
    (X Y : A) (I : CochainComplex A ℤ) [I.IsKInjective]
    (ι : (CochainComplex.singleFunctor A 0).obj Y ⟶ I) [QuasiIso ι] (n : ℤ) :
    CohomologyClass ((CochainComplex.singleFunctor A 0).obj X) I n ≃ₗ[k]
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj X) ⟶
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj Y))⟦n⟧) :=
  { toAddEquiv := (AdvancedHomologicalAlgebra.ExtShiftedHom.classDerivedEquivInjective
        ((CochainComplex.singleFunctor A 0).obj X) I n).trans
      { toEquiv := ((CategoryTheory.shiftFunctor _ n).mapIso
          (asIso (DerivedCategory.Q.map ι))).symm.homToEquiv
        map_add' := by intros; simp [Preadditive.add_comp] }
    map_smul' r x := by
      change classToDerived _ _ n (r • x) ≫ _ = r • (classToDerived _ _ n x ≫ _)
      rw [classToDerived_smul, Linear.smul_comp] }


section HomFunctoriality
variable {A : Type*} [Category A] [Abelian A] [Linear k A]
  (K : CochainComplex A ℤ) {I J : CochainComplex A ℤ} (b : I ⟶ J)

def linearHomPostcomp : linearHomComplex k K I ⟶ linearHomComplex k K J where
  f n := ModuleCat.ofHom
    { toFun z := z.comp (Cochain.ofHom b) (add_zero n)
      map_add' z t := by simp
      map_smul' r z := by simp [Cochain.smul_comp] }
  comm' i j _ := by ext z; exact δ_comp_ofHom z b j

def cocyclePostcomp (n : ℤ) : Cocycle K I n →ₗ[k] Cocycle K J n where
  toFun z := z.postcomp b
  map_add' z t := by ext : 1; simp [Cocycle.postcomp]
  map_smul' r z := by ext : 1; simp [Cocycle.postcomp, Cochain.smul_comp]

def classPostcomp (n : ℤ) : CohomologyClass K I n →ₗ[k] CohomologyClass K J n :=
  { __ := CohomologyClass.descAddMonoidHom
      ((CohomologyClass.mkAddMonoidHom K J n).comp (cocyclePostcomp k K b n).toAddMonoidHom)
      (by
        intro z hz
        obtain ⟨m, hm, y, hy⟩ := hz
        change CohomologyClass.mk (z.postcomp b) = 0
        rw [CohomologyClass.mk_eq_zero_iff]
        refine ⟨m, hm, y.comp (Cochain.ofHom b) (add_zero m), ?_⟩
        simp [← hy])
    map_smul' r x := by
      obtain ⟨z, rfl⟩ := x.mk_surjective
      change CohomologyClass.mk ((r • z).postcomp b) =
        r • CohomologyClass.mk (z.postcomp b)
      rw [← CohomologyClass.mk_smul]
      congr 1
      exact (cocyclePostcomp k K b n).map_smul r z }

lemma homologyClass_postcomp (n : ℤ) :
    (HomologicalComplex.homologyMap (linearHomPostcomp k K b) n) ≫
      (HomComplex.linearLeftHomologyData k K J n).homologyIso.hom =
    (HomComplex.linearLeftHomologyData k K I n).homologyIso.hom ≫
      ModuleCat.ofHom (classPostcomp k K b n) := by
  let γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat k) (.up ℤ) n).map
        (linearHomPostcomp k K b))
      (HomComplex.linearLeftHomologyData k K I n)
      (HomComplex.linearLeftHomologyData k K J n) :=
    { φK := ModuleCat.ofHom (cocyclePostcomp k K b n)
      φH := ModuleCat.ofHom (classPostcomp k K b n)
      commi := by ext z; rfl
      commf' := by
        apply (cancel_mono (HomComplex.linearLeftHomologyData k K J n).i).mp
        have hi : ModuleCat.ofHom (cocyclePostcomp k K b n) ≫
            (HomComplex.linearLeftHomologyData k K J n).i =
          (HomComplex.linearLeftHomologyData k K I n).i ≫
            (linearHomPostcomp k K b).f n := rfl
        rw [Category.assoc, hi, ← Category.assoc,
          ShortComplex.LeftHomologyData.f'_i,
          Category.assoc, ShortComplex.LeftHomologyData.f'_i]
        exact ((HomologicalComplex.shortComplexFunctor (ModuleCat k) (.up ℤ) n).map
          (linearHomPostcomp k K b)).comm₁₂.symm
      commπ := by ext z; rfl }
  exact γ.homologyMap_comm

lemma injectiveClassLinearEquiv_natural (X Y Y' : A)
    (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective]
    (ι : (CochainComplex.singleFunctor A 0).obj Y ⟶ I)
    (ι' : (CochainComplex.singleFunctor A 0).obj Y' ⟶ J)
    [QuasiIso ι] [QuasiIso ι'] (b : Y ⟶ Y') (g : I ⟶ J)
    (hg : ι ≫ g = (CochainComplex.singleFunctor A 0).map b ≫ ι')
    (n : ℤ) (x : CohomologyClass ((CochainComplex.singleFunctor A 0).obj X) I n) :
    injectiveClassLinearEquiv k X Y' J ι' n
        (classPostcomp k ((CochainComplex.singleFunctor A 0).obj X) g n x) =
      injectiveClassLinearEquiv k X Y I ι n x ≫
        (CategoryTheory.shiftFunctor _ n).map ((DerivedCategory.singleFunctor A 0).map b) := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  have h := AdvancedHomologicalAlgebra.ExtShiftedHom.injective_natural A X X Y Y'
    I J ι ι' (inferInstance) (inferInstance) (𝟙 X) b g
    ⟨Homotopy.ofEq hg⟩ n z
  have hz : z.precomp ((CochainComplex.singleFunctor A 0).map (𝟙 X)) = z := by
    ext : 1
    simp [Cocycle.precomp]
  rw [hz] at h
  change injectiveClassMap X Y' J ι' (inferInstance) n
      (CohomologyClass.mk (z.postcomp g)) =
    injectiveClassMap X Y I ι (inferInstance) n (CohomologyClass.mk z) ≫ _
  dsimp only [extMap] at h
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

end HomFunctoriality

section GroupExt
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants
variable (G : Type uG) [Group G]

local instance groupHasExt : HasExt.{max u uG uM} (GroupModule.{u,uG,uM} k G) :=
  CategoryTheory.hasExt_of_enoughInjectives.{max u uG uM} (GroupModule.{u,uG,uM} k G)

def invariantModelExtIso (M : GroupModule.{u,uG,uM} k G) (R : InjectiveResolution M) (n : ℕ) :
    (((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj
      R.cochainComplex).homology (n : ℤ) ≅
    ModuleCat.of k (Abelian.Ext.{max u uG uM} (trivialModule.{u,uG,uM} k G) M n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) (n : ℤ)).mapIso
    (AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantComplexIso
      R.cochainComplex)) ≪≫
    (HomComplex.homologyLinearEquiv k _ _ (n : ℤ)).toModuleIso ≪≫
    ((injectiveClassLinearEquiv k (trivialModule k G) M R.cochainComplex R.ι' (n : ℤ)).trans
      (Abelian.Ext.homLinearEquiv (R := k)).symm).toModuleIso

lemma invariantComplexIso_natural {M N : GroupModule.{u,uG,uM} k G}
    (R : InjectiveResolution M) (S : InjectiveResolution N) (g : R.cochainComplex ⟶ S.cochainComplex) :
    ((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map g ≫
        (AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantComplexIso S.cochainComplex).hom =
      (AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantComplexIso R.cochainComplex).hom ≫
        linearHomPostcomp k ((CochainComplex.singleFunctor (GroupModule.{u,uG,uM} k G) 0).obj
          (trivialModule k G)) g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change Cochain.fromSingleMk
      (AdvancedHomologicalAlgebra.GroupDerivedInvariants.fromInvariant (S.cochainComplex.X n)
        (((invariantsFunctor k G).map (g.f n)).hom m)) (zero_add n) =
    (Cochain.fromSingleMk
      (AdvancedHomologicalAlgebra.GroupDerivedInvariants.fromInvariant (R.cochainComplex.X n) m)
      (zero_add n)).comp (Cochain.ofHom g) (add_zero n)
  rw [← Cochain.fromSingleMk_postcomp]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (((Representation.trivial k G (ULift.{max uG uM} k)).asModuleEquiv a).down : k) •
      ((g.f n).hom m.val) = (g.f n).hom
      ((((Representation.trivial k G (ULift.{max uG uM} k)).asModuleEquiv a).down : k) • m.val)
  exact ((g.f n).hom.map_smul_of_tower (R := k) _ _).symm

lemma invariantModelExtIso_natural {M N : GroupModule.{u,uG,uM} k G}
    (R : InjectiveResolution M) (S : InjectiveResolution N) (b : M ⟶ N)
    (φ : InjectiveResolution.Hom R S b) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((invariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫
        (invariantModelExtIso k G N S n).hom =
      (invariantModelExtIso k G M R n).hom ≫
        (Abelian.linearExtFunctorObj k (trivialModule k G) n).map b := by
  have h₁ := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) (n : ℤ)).map
    (invariantComplexIso_natural k G R S φ.hom')
  simp only [CategoryTheory.Functor.map_comp] at h₁
  have h₂ := homologyClass_postcomp k
    ((CochainComplex.singleFunctor (GroupModule.{u,uG,uM} k G) 0).obj (trivialModule k G)) φ.hom' (n : ℤ)
  dsimp only [invariantModelExtIso, Iso.trans_hom]
  simp only [Category.assoc]
  erw [reassoc_of% h₁]
  erw [reassoc_of% h₂]
  congr 1
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (Abelian.Ext.homLinearEquiv (R := k)).injective
  change (Abelian.Ext.homLinearEquiv (R := k))
      ((Abelian.Ext.homLinearEquiv (R := k)).symm
        (injectiveClassLinearEquiv k _ N S.cochainComplex S.ι' (n : ℤ)
          (classPostcomp k _ φ.hom' (n : ℤ) x))) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [injectiveClassLinearEquiv_natural k _ M N R.cochainComplex S.cochainComplex
    R.ι' S.ι' b φ.hom' φ.ι'_comp_hom']
  have he :
      (((injectiveClassLinearEquiv k (trivialModule k G) M R.cochainComplex R.ι' (n : ℤ)).trans
        (Abelian.Ext.homLinearEquiv (R := k)).symm) x).hom =
      injectiveClassLinearEquiv k (trivialModule k G) M R.cochainComplex R.ι' (n : ℤ) x := by
    change (Abelian.Ext.homLinearEquiv (R := k))
      ((Abelian.Ext.homLinearEquiv (R := k)).symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  change _ = ((((injectiveClassLinearEquiv k (trivialModule k G) M
      R.cochainComplex R.ι' (n : ℤ)).trans
      (Abelian.Ext.homLinearEquiv (R := k)).symm) x).comp
        (Abelian.Ext.mk₀ b) (add_zero n)).hom
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  exact congrArg (fun f => f ≫ (CategoryTheory.shiftFunctor _ (n : ℤ)).map
    ((DerivedCategory.singleFunctor (GroupModule.{u,uG,uM} k G) 0).map b)) he.symm

/-- The canonical linear comparison from derived invariants to shifted Hom. -/
def derivedExtLinearIso (n : ℕ) :
    Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.cohomology.{u,uG,uM} k G n ≅
      Abelian.linearExtFunctorObj k (trivialModule.{u,uG,uM} k G) n := by
  let model (M : GroupModule.{u,uG,uM} k G) := injectiveResolution M
  let hI (M : GroupModule.{u,uG,uM} k G) (q : ℤ) :
      Injective ((model M).cochainComplex.X q) := inferInstance
  let e (M : GroupModule.{u,uG,uM} k G) :=
    AdvancedHomologicalAlgebra.GroupDerivedInvariants.injectiveValueIso
      (model M).ι' inferInstance (hI M) n
  refine NatIso.ofComponents
    (fun M => e M ≪≫ invariantModelExtIso k G M (model M) n) ?_
  intro M N b
  let φ : InjectiveResolution.Hom (model M) (model N) b :=
    ⟨InjectiveResolution.desc b _ _, InjectiveResolution.desc_commutes_zero b _ _⟩
  have h := AdvancedHomologicalAlgebra.GroupDerivedInvariants.injectiveValueIso_naturality
    (model M).ι' (by infer_instance) (model N).ι' (by infer_instance)
    (hI M) (hI N) b φ.hom' (Homotopy.ofEq φ.ι'_comp_hom') n
  change _ ≫ (e N).hom ≫ _ = ((e M).hom ≫ _) ≫ _
  erw [← Category.assoc, h, Category.assoc,
    invariantModelExtIso_natural k G _ _ b φ n, ← Category.assoc]

end GroupExt

end DerivedComparison

universe uC vC uR

namespace ResolutionBridge
open CochainComplex HomComplex
open AdvancedHomologicalAlgebra.ExtShiftedHom.LiftedP103 (resolutionSign)
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{vC} C]
  (k : Type uR) [CommRing k] [Linear k C] {X Y : C} (R : ProjectiveResolution X)

def homShortComplex (n : ℕ) : ShortComplex (ModuleCat.{vC} k) :=
  (R.complex.linearYonedaObj k Y).sc' (n-1) n (n+1)

private lemma resolutionSign_smul_cancel {A : Type*} [AddCommGroup A] (n : ℕ) (a : A) :
    resolutionSign n • (resolutionSign n • a) = a := by
  rw [← mul_smul, resolutionSign, ← mul_pow]
  simp

private lemma resolutionSign_smul_eq_zero_iff {A : Type*} [AddCommGroup A] (n : ℕ) (a : A) :
    resolutionSign n • a = 0 ↔ a = 0 := by
  constructor
  · intro h
    simpa only [resolutionSign_smul_cancel, smul_zero] using congrArg (resolutionSign n • ·) h
  · rintro rfl
    exact smul_zero _

/-- The HA-R11 sign converts unsigned bar cocycles to the signed Hom convention
used by `ProjectiveResolution.extMk`. -/
def cyclesExtMap (n : ℕ) :
    (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.K →ₗ[k] Abelian.Ext X Y n :=
  resolutionSign n •
    { toFun := fun f => R.extMk f.1 (n+1) rfl f.2
      map_add' := fun f g => (R.add_extMk _ _ _ _ _ _).symm
      map_smul' := fun r f => by simp [R.smul_extMk] }

lemma cyclesExtMap_apply (n : ℕ)
    (f : (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.K) :
    cyclesExtMap k R n f = resolutionSign n • R.extMk f.1 (n+1) rfl f.2 :=
  rfl

lemma cyclesExtMap_surjective (n : ℕ) : Function.Surjective (cyclesExtMap k (Y := Y) R n) := by
  intro x
  obtain ⟨f, hf, hx⟩ := R.extMk_surjective (resolutionSign n • x) (n+1) rfl
  refine ⟨⟨f, hf⟩, ?_⟩
  rw [cyclesExtMap_apply, hx, resolutionSign_smul_cancel]

lemma extMk_zero_iff (f : R.complex.X 0 ⟶ Y) (hf : R.complex.d 1 0 ≫ f = 0) :
    R.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  rw [← R.extEquivCohomologyClass.apply_eq_iff_eq]
  simp only [ProjectiveResolution.extEquivCohomologyClass_extMk,
    ProjectiveResolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by simp)]
  constructor
  · rintro ⟨g, hg⟩
    have hgzero : g = 0 :=
      (CochainComplex.isZero_of_isStrictlyLE R.cochainComplex 0 1).eq_of_src _ _
    simpa [hgzero] using hg.symm
  · intro hfzero
    subst f
    exact ⟨0, by simp⟩


lemma cyclesExtMap_exact (n : ℕ) :
    Function.Exact (homShortComplex k (Y := Y) R n).moduleCatToCycles (cyclesExtMap k (Y := Y) R n) := by
  intro f
  rw [cyclesExtMap_apply, resolutionSign_smul_eq_zero_iff]
  cases n with
  | zero =>
      rw [extMk_zero_iff]
      constructor
      · intro hf
        refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa using hf.symm
      · rintro ⟨g, hg⟩
        have hg' := congrArg Subtype.val hg
        change ((R.complex.linearYonedaObj k Y).d 0 0).hom g = f.1 at hg'
        rw [HomologicalComplex.shape _ _ _ (by simp)] at hg'
        change f.1 = 0
        exact hg'.symm.trans rfl
  | succ n =>
      rw [R.extMk_eq_zero_iff _ _ _ _ n rfl]
      simp only [homShortComplex, Nat.succ_sub_one]
      constructor
      · rintro ⟨g, hg⟩
        refine ⟨g, ?_⟩
        exact Subtype.ext hg
      · rintro ⟨g, hg⟩
        exact ⟨g, congrArg Subtype.val hg⟩


def extLeftHomologyData (n : ℕ) : (homShortComplex k (Y := Y) R n).LeftHomologyData where
  K := (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.K
  H := ModuleCat.of k (Abelian.Ext X Y n)
  i := (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.i
  π := ModuleCat.ofHom (cyclesExtMap k R n)
  wi := (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.wi
  hi := (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.hi
  wπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (cyclesExtMap_exact k R n _).mpr ⟨f, rfl⟩
  hπ := ModuleCat.isColimitCokernelCofork _ _ (cyclesExtMap_exact k R n)
    (cyclesExtMap_surjective k R n)

lemma prev_up_nat (n : ℕ) : (ComplexShape.up ℕ).prev n = n-1 := by
  cases n with
  | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by intro j; simp)
  | succ n => simp

def homologyExtIso (Y : C) (n : ℕ) :
    (R.complex.linearYonedaObj k Y).homology n ≅ ModuleCat.of k (Abelian.Ext X Y n) :=
  (ShortComplex.homologyFunctor (ModuleCat k)).mapIso
    ((R.complex.linearYonedaObj k Y).isoSc' (n-1) n (n+1) (prev_up_nat n)
      ((ComplexShape.up ℕ).next_eq' rfl)) ≪≫
    (extLeftHomologyData k R n).homologyIso


def homPostcomp {Y Z : C} (b : Y ⟶ Z) :
    R.complex.linearYonedaObj k Y ⟶ R.complex.linearYonedaObj k Z where
  f n := ((linearYoneda k C).map b).app (Opposite.op (R.complex.X n))
  comm' i j hij := by ext f; simp [Category.assoc]

def cyclesPostcomp {Y Z : C} (b : Y ⟶ Z) (n : ℕ) :
    (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.K →ₗ[k]
      (homShortComplex k (Y := Z) R n).moduleCatLeftHomologyData.K where
  toFun f := ⟨f.1 ≫ b, by
    change R.complex.d (n+1) n ≫ (f.1 ≫ b) = 0
    have hf := f.2
    change R.complex.d (n+1) n ≫ f.1 = 0 at hf
    simp [← Category.assoc, hf]⟩
  map_add' f g := by
    apply Subtype.ext
    change (f.1 + g.1) ≫ b = f.1 ≫ b + g.1 ≫ b
    exact Preadditive.add_comp _ _ _ f.1 g.1 b
  map_smul' r f := by
    apply Subtype.ext
    change (r • f.1) ≫ b = r • (f.1 ≫ b)
    exact Linear.smul_comp _ _ _ r f.1 b

def homologyMapData {Y Z : C} (b : Y ⟶ Z) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat k) (.up ℕ) (n-1) n (n+1)).map
        (homPostcomp k R b)) (extLeftHomologyData k R n) (extLeftHomologyData k R n) where
  φK := ModuleCat.ofHom (cyclesPostcomp k R b n)
  φH := (Abelian.linearExtFunctorObj k X n).map b
  commi := by ext f; rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact Category.assoc _ _ _
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change ((Abelian.linearExtFunctorObj k X n).map b).hom (cyclesExtMap k R n f) =
      cyclesExtMap k R n (cyclesPostcomp k R b n f)
    rw [cyclesExtMap_apply, cyclesExtMap_apply, map_zsmul]
    exact congrArg (resolutionSign n • ·) (R.extMk_comp_mk₀ f.1 (n+1) rfl f.2 b)

lemma homologyExtIso_natural {Y Z : C} (b : Y ⟶ Z) (n : ℕ) :
    HomologicalComplex.homologyMap (homPostcomp k R b) n ≫
      (homologyExtIso k R Z n).hom =
      (homologyExtIso k R Y n).hom ≫ (Abelian.linearExtFunctorObj k X n).map b := by
  have hnat := (HomologicalComplex.natIsoSc' (ModuleCat k) (.up ℕ) (n-1) n (n+1)
    (prev_up_nat n) ((ComplexShape.up ℕ).next_eq' rfl)).hom.naturality (homPostcomp k R b)
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat k)).map hnat
  simp only [Functor.map_comp] at h
  dsimp only [homologyExtIso, Iso.trans_hom, Functor.mapIso_hom]
  change HomologicalComplex.homologyMap (homPostcomp k R b) n ≫
      (ShortComplex.homologyFunctor (ModuleCat k)).map
        ((R.complex.linearYonedaObj k Z).isoSc' (n-1) n (n+1) _ _).hom = _ at h
  erw [← Category.assoc, h, Category.assoc]
  erw [(homologyMapData k R b n).homologyMap_comm]
  simp only [Category.assoc]
  rfl


def homCochainsFunctor : C ⥤ CochainComplex (ModuleCat.{vC} k) ℕ where
  obj Y := R.complex.linearYonedaObj k Y
  map b := homPostcomp k R b
  map_id Y := by ext n f; simp [homPostcomp]
  map_comp b c := by
    ext n f
    exact (Category.assoc f b c).symm

def homologyExtNatIso (n : ℕ) :
    homCochainsFunctor k R ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n ≅
      Abelian.linearExtFunctorObj k X n :=
  NatIso.ofComponents (fun Y => homologyExtIso k R Y n)
    (fun b => homologyExtIso_natural k R b n)
end ResolutionBridge


namespace ModuleBarBridge
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants
variable (k G : Type u) [CommRing k] [Group G]

def trivialRepresentationLiftIso : Rep.trivial k G k ≅ Rep.trivial k G (ULift.{u} k) :=
  Rep.mkIso (.mk (ULift.moduleEquiv.symm : k ≃ₗ[k] ULift.{u} k) (by intro g; rfl))

def trivialModuleIso : Rep.toModuleMonoidAlgebra.obj (Rep.trivial k G k) ≅
    trivialModule.{u,u,0} k G :=
  Rep.toModuleMonoidAlgebra.mapIso (trivialRepresentationLiftIso k G)

instance toModuleAdditive :
    (Rep.toModuleMonoidAlgebra (k := k) (G := G)).Additive where
  map_add := by intros; rfl

def mappedStandardResolution :=
  Rep.toModuleMonoidAlgebra.mapProjectiveResolution (Rep.standardResolution k G)

def moduleBarResolution : ProjectiveResolution (trivialModule.{u,u,0} k G) where
  complex := (mappedStandardResolution k G).complex
  projective n := (mappedStandardResolution k G).projective n
  π := (mappedStandardResolution k G).π ≫
    (ChainComplex.single₀ (Coeff k G)).map (trivialModuleIso k G).hom
  quasiIso := by infer_instance

def moduleRepHomMap (M : Coeff k G) (n : ℕ) :
    ((moduleBarResolution k G).complex.X n ⟶ M) →ₗ[k]
      (GroupBar.B k G n ⟶ representation k G M) where
  toFun := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
    (GroupBar.B k G n) M
  map_add' f g := by rfl
  map_smul' r f := by rfl

def moduleRepHomEquiv (M : Coeff k G) (n : ℕ) :
    ((moduleBarResolution k G).complex.X n ⟶ M) ≃ₗ[k]
      (GroupBar.B k G n ⟶ representation k G M) :=
  LinearEquiv.ofBijective (moduleRepHomMap k G M n)
    ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
      (GroupBar.B k G n) M).bijective

def moduleHomComplexIso (M : Coeff k G) :
    ((moduleBarResolution k G).complex.linearYonedaObj k M) ≅ homCochains k G M := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleRepHomEquiv k G M n).toModuleIso) ?_
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Rep.hom_ext
  ext x
  rfl

def moduleHomCochainsFunctor : Coeff k G ⥤ CochainComplex (ModuleCat.{u} k) ℕ where
  obj M := (moduleBarResolution k G).complex.linearYonedaObj k M
  map b :=
    { f n := ((linearYoneda k (Coeff k G)).map b).app
        (Opposite.op ((moduleBarResolution k G).complex.X n))
      comm' i j _ := by ext φ; rfl }
  map_id M := by ext n φ; rfl
  map_comp b c := by ext n φ; rfl

lemma moduleHomComplexIso_natural {M N : Coeff k G} (b : M ⟶ N) :
    (moduleHomCochainsFunctor k G).map b ≫ (moduleHomComplexIso k G N).hom =
      (moduleHomComplexIso k G M).hom ≫ (homogeneousCochainsFunctor k G).map b := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Rep.hom_ext
  ext x
  rfl

def moduleHomFunctorIso : moduleHomCochainsFunctor k G ≅ homogeneousCochainsFunctor k G :=
  NatIso.ofComponents (moduleHomComplexIso k G) (fun b => moduleHomComplexIso_natural k G b)

end ModuleBarBridge


section EqualUniverseCohomology
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
variable (k G : Type u) [CommRing k] [Group G]

attribute [local instance] groupHasExt

/-- The full bar resolution computes the same linear Ext functor as
injective models of the actual derived invariants. -/
def barExtIso (n : ℕ) :
    ModuleBarBridge.moduleHomCochainsFunctor k G ⋙
      HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n ≅
    Abelian.linearExtFunctorObj k
      (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.trivialModule.{u,u,0} k G) n := by
  exact ResolutionBridge.homologyExtNatIso k (ModuleBarBridge.moduleBarResolution k G) n

/-- HA-A02: cohomology of the displayed unsigned cochains is naturally
isomorphic to the actual derived invariants of HA-A01. -/
theorem cohomology : cohomologyType k G := by
  intro n
  exact ⟨derivedExtLinearIso.{u,u,0} k G n ≪≫ (barExtIso k G n).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight (ModuleBarBridge.moduleHomFunctorIso k G ≪≫ naturalComplexIso k G)
      (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n)⟩

end EqualUniverseCohomology

universe v w

namespace LargeCoordinates

open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large
  renaming coordinates → tupleCochains, differential → tupleDifferential

variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- A homogeneous tuple has these successive quotients. -/
private def increments {n : ℕ} (c : Fin (n + 1) → G) : Fin n → G :=
  fun i => (c i.castSucc)⁻¹ * c i.succ

private lemma increments_partialProd {n : ℕ} (g : Fin n → G) :
    increments G (Fin.partialProd g) = g :=
  funext (Fin.partialProd_right_inv g)

private lemma increments_translate {n : ℕ} (a : G) (c : Fin (n + 1) → G) :
    increments G (fun i => a * c i) = increments G c := by
  funext i
  simp [increments, mul_inv_rev, mul_assoc]

/-- Extend inhomogeneous coordinates by equivariance and linearity on the full tuple basis. -/
private def extendLinear (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : tupleCochains k G M n) : GroupBar.Large.B.{u,v,w} k G n →ₗ[k] representation k G M :=
  (Finsupp.linearCombination k
    (fun c : ULift.{w} (Fin (n + 1) → G) =>
      (representation k G M).ρ (c.down 0) (f (increments G c.down)))).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private lemma extendLinear_single (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : tupleCochains k G M n) (c : Fin (n + 1) → G) (r : k) :
    extendLinear k G M n f (GroupBar.Large.single k G c r) =
      r • (representation k G M).ρ (c 0) (f (increments G c)) :=
  Finsupp.linearCombination_single _ _ _

private def extend (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : tupleCochains k G M n) : GroupBar.Large.B.{u,v,w} k G n ⟶ representation k G M :=
  Rep.ofHom ⟨extendLinear k G M n f, fun a => by
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change extendLinear k G M n f
      ((GroupBar.Large.B.{u,v,w} k G n).ρ a (GroupBar.Large.single k G c 1)) =
      (representation k G M).ρ a (extendLinear k G M n f (GroupBar.Large.single k G c 1))
    rw [GroupBar.Large.diagonal_action, extendLinear_single, extendLinear_single,
      increments_translate]
    simp only [one_smul, map_mul]
    rfl⟩

/-- Evaluation on the cumulative-product tuples is a linear equivalence. -/
def coordinatesEquiv (M : Coeff.{u,v,w} k G) (n : ℕ) :
    ((Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.homogeneousFunctor
      k G).obj M).X n ≃ₗ[k] tupleCochains k G M n where
  toFun φ g := φ.hom (GroupBar.Large.single k G (Fin.partialProd g) 1)
  invFun f := extend k G M n f
  left_inv φ := by
    change GroupBar.Large.B.{u,v,w} k G n ⟶ representation k G M at φ
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change extendLinear k G M n
      (fun g => φ.hom (GroupBar.Large.single k G (Fin.partialProd g) 1))
      (GroupBar.Large.single k G c 1) = φ.hom (GroupBar.Large.single k G c 1)
    rw [extendLinear_single, one_smul, ← φ.hom.isIntertwining,
      GroupBar.Large.diagonal_action]
    have h := Fin.partialProd_left_inv c
    exact congrArg (fun t => φ.hom (GroupBar.Large.single k G t 1)) h
  right_inv f := by
    funext g
    change extendLinear k G M n f (GroupBar.Large.single k G (Fin.partialProd g) 1) = f g
    rw [extendLinear_single, one_smul, increments_partialProd, Fin.partialProd_zero, map_one]
    rfl
  map_add' φ ψ := rfl
  map_smul' r φ := rfl

/-- The first face is the translated tail, while all other faces contract an increment. -/
private lemma differential_coordinates (M : Coeff.{u,v,w} k G) (n : ℕ)
    (φ : GroupBar.Large.B.{u,v,w} k G n ⟶ representation k G M) (g : Fin (n + 1) → G) :
    coordinatesEquiv k G M (n+1) ((((homogeneousFunctor k G).obj M).d n (n+1)).hom φ) g =
      tupleDifferential k G M n (coordinatesEquiv k G M n φ) g := by
  change φ.hom (GroupBar.Large.d.{u,v,w} k G n
    (GroupBar.Large.single k G (Fin.partialProd g) 1)) = _
  rw [GroupBar.Large.boundary_single, map_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ]
  have hfirst : Fin.partialProd g ∘ Fin.succ =
      fun i => g 0 * Fin.partialProd (fun j => g j.succ) i := by
    funext i
    exact Fin.partialProd_succ' g i
  rw [hfirst, ← GroupBar.Large.diagonal_action, φ.hom.isIntertwining]
  simp_rw [← Fin.partialProd_contractNth]
  have hscalar (i : Fin (n + 1)) :
      GroupBar.Large.single.{u,v,w} k G (Fin.partialProd (Fin.contractNth i (· * ·) g))
          ((-1 : k) ^ (i.val + 1)) =
        ((-1 : k) ^ (i.val + 1)) •
          GroupBar.Large.single.{u,v,w} k G (Fin.partialProd (Fin.contractNth i (· * ·) g)) 1 := by
    simp [GroupBar.Large.single, MonoidAlgebra.smul_single]
  simp_rw [hscalar, map_smul]
  rw [Fin.sum_univ_castSucc]
  have hlast : Fin.contractNth (Fin.last n) (· * ·) g = fun i => g i.castSucc := by
    funext i
    simp [Fin.contractNth]
  simp only [tupleDifferential, hlast, add_assoc, Fin.val_last, Fin.val_castSucc]
  rfl

private def moduleEvaluation (M : Coeff.{u,v,w} k G) (n : ℕ) :
    (Rep.toModuleMonoidAlgebra.obj (GroupBar.Large.B.{u,v,w} k G n) ⟶ M) →ₗ[k]
      tupleCochains k G M n where
  toFun φ g := φ.hom ((GroupBar.Large.B.{u,v,w} k G n).ρ.asModuleEquiv.symm
    (GroupBar.Large.single k G (Fin.partialProd g) 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma moduleEvaluation_bijective (M : Coeff.{u,v,w} k G) (n : ℕ) :
    Function.Bijective (moduleEvaluation k G M n) := by
  let e := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
    (GroupBar.Large.B.{u,v,w} k G n) M
  have h : (moduleEvaluation k G M n : _ → _) = (coordinatesEquiv k G M n) ∘ e := rfl
  rw [h]
  exact (coordinatesEquiv k G M n).bijective.comp e.bijective

theorem comparison : comparisonType.{u,v,w} k G := by
  refine ⟨coordinatesEquiv k G, ?_, differential_coordinates k G, ?_, ?_, ?_⟩
  · intro M n φ g
    rfl
  · intro M N a n φ g
    rfl
  · intro M
    exact ⟨LinearEquiv.funUnique (Fin 0 → G) k (representation k G M), fun _ => rfl⟩
  · intro M n
    exact ⟨LinearEquiv.ofBijective (moduleEvaluation k G M n)
      (moduleEvaluation_bijective k G M n), fun _ _ => rfl⟩

end LargeCoordinates

theorem largeComparison :
    Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.comparisonExpected.{u,v,w} :=
  fun k G _ _ => LargeCoordinates.comparison k G

namespace Large
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large (homogeneousFunctor)
open Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants

variable (k : Type u) (G : Type uG) [CommRing k] [Group G]

local instance largeToModuleAdditive :
    (Rep.toModuleMonoidAlgebra (k := k) (G := G) :
      Rep.{max u uG uM} k G ⥤ GroupModule.{u,uG,uM} k G).Additive where
  map_add := by intros; rfl

private abbrev moduleBarComplex : ChainComplex (GroupModule.{u,uG,uM} k G) ℕ :=
  (Rep.toModuleMonoidAlgebra.mapHomologicalComplex _).obj
    (GroupBar.Large.complex.{u,uG,uM} k G)

private abbrev moduleAugmentation :
    (moduleBarComplex.{u,uG,uM} k G).X 0 ⟶ trivialModule.{u,uG,uM} k G :=
  Rep.toModuleMonoidAlgebra.map (GroupBar.Large.augmentation.{u,uG,uM} k G)

private lemma moduleAugmentation_comp :
    (moduleBarComplex.{u,uG,uM} k G).d 1 0 ≫ moduleAugmentation k G = 0 := by
  change Rep.toModuleMonoidAlgebra.map (GroupBar.Large.boundary.{u,uG,uM} k G 0) ≫
    Rep.toModuleMonoidAlgebra.map (GroupBar.Large.augmentation.{u,uG,uM} k G) = 0
  rw [← Functor.map_comp, GroupBar.Large.boundary_augmentation, Functor.map_zero]

private lemma moduleAugmentation_exact :
    (ShortComplex.mk _ _ (moduleAugmentation_comp.{u,uG,uM} k G)).Exact := by
  apply ModuleCat.shortComplex_exact
  intro x
  change (ULift.up (GroupBar.Large.ε.{u,uG,uM} k G x) : ULift.{max uG uM} k) = ULift.up (0 : k) ↔
    ∃ y, GroupBar.Large.d.{u,uG,uM} k G 0 y = x
  simpa only [ULift.up_inj] using GroupBar.Large.exact_zero.{u,uG,uM} k G x

private lemma moduleAugmentation_epi : Epi (moduleAugmentation.{u,uG,uM} k G) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y, hy⟩ := GroupBar.Large.augmentation_surjective.{u,uG,uM} k G x.down
  exact ⟨y, ULift.ext hy⟩

private def moduleAugmentationChainMap :
    moduleBarComplex.{u,uG,uM} k G ⟶ (ChainComplex.single₀ _).obj (trivialModule.{u,uG,uM} k G) :=
  ((moduleBarComplex k G).toSingle₀Equiv _).symm
    ⟨moduleAugmentation k G, moduleAugmentation_comp k G⟩

private lemma moduleAugmentation_quasiIso :
    QuasiIso (moduleAugmentationChainMap.{u,uG,uM} k G) := by
  constructor
  intro n
  cases n with
  | zero =>
      simp only [moduleAugmentationChainMap]
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂,
        ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
      exact ⟨moduleAugmentation_exact.{u,uG,uM} k G, moduleAugmentation_epi.{u,uG,uM} k G⟩
  | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      apply ModuleCat.shortComplex_exact
      exact GroupBar.Large.exact_succ.{u,uG,uM} k G n

/-- The actual augmented homogeneous bar complex as a projective resolution
in the coefficient category used by the derived invariants. -/
def moduleBarResolution : ProjectiveResolution (trivialModule.{u,uG,uM} k G) where
  complex := moduleBarComplex k G
  projective n := by
    let := GroupBar.Large.degree_free.{u,uG,uM} k G n
    let : Module.Projective k[G] (GroupBar.Large.B.{u,uG,uM} k G n).ρ.asModule :=
      Module.Projective.of_free
    exact ModuleCat.projective_of_categoryTheory_projective
      (ModuleCat.of k[G] (GroupBar.Large.B.{u,uG,uM} k G n).ρ.asModule)
  π := moduleAugmentationChainMap k G
  quasiIso := moduleAugmentation_quasiIso k G

private def moduleRepHomMap (M : GroupModule.{u,uG,uM} k G) (n : ℕ) :
    ((moduleBarResolution k G).complex.X n ⟶ M) →ₗ[k]
      (GroupBar.Large.B.{u,uG,uM} k G n ⟶ Rep.ofModuleMonoidAlgebra.obj M) where
  toFun := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
    (GroupBar.Large.B k G n) M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def moduleRepHomEquiv (M : GroupModule.{u,uG,uM} k G) (n : ℕ) :
    ((moduleBarResolution k G).complex.X n ⟶ M) ≃ₗ[k]
      (GroupBar.Large.B.{u,uG,uM} k G n ⟶ Rep.ofModuleMonoidAlgebra.obj M) :=
  LinearEquiv.ofBijective (moduleRepHomMap k G M n)
    ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
      (GroupBar.Large.B k G n) M).bijective

private def moduleHomComplexIso (M : GroupModule.{u,uG,uM} k G) :
    ((moduleBarResolution k G).complex.linearYonedaObj k M) ≅
      (homogeneousFunctor.{u,uG,uM} k G).obj M := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleRepHomEquiv k G M n).toModuleIso) ?_
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Rep.hom_ext
  ext x
  rfl

private def moduleHomFunctorIso :
    ResolutionBridge.homCochainsFunctor k (moduleBarResolution.{u,uG,uM} k G) ≅
      homogeneousFunctor.{u,uG,uM} k G :=
  NatIso.ofComponents (moduleHomComplexIso k G) (by
    intro M N b
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply Rep.hom_ext
    ext x
    rfl)

attribute [local instance] groupHasExt

/-- The comparison with actual derived invariants through the augmented bar resolution. -/
def cohomologyIso (n : ℕ) :
    Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.cohomology.{u,uG,uM} k G n ≅
      homogeneousFunctor.{u,uG,uM} k G ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u uG uM} k) (.up ℕ) n :=
  derivedExtLinearIso.{u,uG,uM} k G n ≪≫
    (ResolutionBridge.homologyExtNatIso k (moduleBarResolution.{u,uG,uM} k G) n).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight (moduleHomFunctorIso k G)
      (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n)

end Large

theorem largeCohomology :
    Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.cohomologyExpected.{u,uG,uM} :=
  fun k G _ _ n => ⟨Large.cohomologyIso k G n⟩

end AdvancedHomologicalAlgebra.GroupCochainComparison
