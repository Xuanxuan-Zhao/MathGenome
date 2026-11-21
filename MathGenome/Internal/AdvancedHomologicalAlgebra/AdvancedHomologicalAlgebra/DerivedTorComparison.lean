import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.Splitting
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import MathGenome.Internal.AlgebraCore.P103.Ch10.Horseshoe
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorExactSequences

/-! HA-R14: derived tensor and classical Tor over arbitrary rings.
The normalized comparison retains the actual quotient maps on every projective
resolution, together with naturality, degree zero, balance, and connecting maps. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits
universe u v w t x y
namespace AdvancedHomologicalAlgebra.DerivedTorComparison

open P103.Specs.Ch10.Complexes

section Quotient
variable {S : Type u} [Ring S] {ι : Type t} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} S) c) (n : ι)

lemma range_toCycles :
    (K.sc n).moduleCatToCycles.range = cycleBoundaries K n := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- The categorical homology object is the original P103 quotient, with
its inherited scalar structure. -/
def quotientHomologyIso : K.homology n ≅ ModuleCat.of S (Homology K n) :=
  (K.sc n).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (range_toCycles K n)).toModuleIso

/-- The comparison sends the categorical quotient of a cycle to its
ordinary quotient class. -/
@[reassoc]
lemma quotientHomologyIso_projection :
    K.homologyπ n ≫ (quotientHomologyIso K n).hom =
      (K.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (homologyClass K n) := by
  change (K.sc n).homologyπ ≫ ((K.sc n).moduleCatHomologyIso.hom ≫ _) = _
  rw [← Category.assoc, ShortComplex.π_moduleCatCyclesIso_hom, Category.assoc]
  congr 1

variable {K n} {L : HomologicalComplex (ModuleCat.{v} S) c}

@[reassoc]
lemma quotientCyclesIso_naturality (f : K ⟶ L) (n : ι) :
    HomologicalComplex.cyclesMap f n ≫ (L.sc n).moduleCatCyclesIso.hom =
      (K.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (cyclesMap f n) := by
  rw [← cancel_mono (L.sc n).moduleCatLeftHomologyData.i]
  simp only [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i]
  change _ = (K.sc n).moduleCatCyclesIso.hom ≫
    (K.sc n).moduleCatLeftHomologyData.i ≫ f.f n
  rw [← Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i]
  exact HomologicalComplex.cyclesMap_i f n

lemma quotientHomologyIso_naturality (f : K ⟶ L) (n : ι) :
    HomologicalComplex.homologyMap f n ≫ (quotientHomologyIso L n).hom =
      (quotientHomologyIso K n).hom ≫ ModuleCat.ofHom (homologyMap f n) := by
  rw [← cancel_epi (K.homologyπ n), HomologicalComplex.homologyπ_naturality_assoc]
  erw [quotientHomologyIso_projection, quotientHomologyIso_projection_assoc]
  erw [quotientCyclesIso_naturality_assoc]
  rfl

end Quotient

section Resolutions
open P103.Specs.Ch10.Comparison
variable {S : Type u} [Ring S] {A : ModuleCat.{max u v} S}
    (P : LeftResolution S A)

def augmentation : P.complex ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} S)).obj A :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom P.ε, by
    apply ModuleCat.hom_ext
    apply LinearMap.range_le_ker_iff.mp
    exact le_of_eq P.exact_zero⟩

lemma augmentation_quasiIso : QuasiIso (augmentation P) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_of_zeros' _
      (by change P.complex.d 0 0 = 0; simp) (by rfl) (by rfl)).mpr
    constructor
    · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      simpa [augmentation] using P.exact_zero
    · apply (ModuleCat.epi_iff_surjective _).mpr
      simpa [augmentation] using P.surjective
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      exact P.exact_succ n
    · apply ChainComplex.exactAt_succ_single_obj

/-- An ordinary P103 projective resolution is a categorical projective
resolution with the same chain complex and augmentation. -/
def categoricalResolution (hP : P.IsProjective) : ProjectiveResolution A where
  complex := P.complex
  π := augmentation P
  projective n := by
    letI := hP n
    infer_instance
  quasiIso := augmentation_quasiIso P

/-- Put Pₙ in degree −n, with precisely the original differential. -/
def cochainResolution : CochainComplex (ModuleCat.{max u v} S) ℤ :=
  P.complex.extend ComplexShape.embeddingDownNat

def cochainAugmentation : cochainResolution P ⟶
    (CochainComplex.singleFunctor (ModuleCat.{max u v} S) 0).obj A :=
  HomologicalComplex.extendMap (augmentation P) ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat A 0 0 rfl).hom

lemma cochainAugmentation_quasiIso : QuasiIso (cochainAugmentation P) := by
  letI := augmentation_quasiIso P
  dsimp only [cochainAugmentation]
  infer_instance

instance cochainResolution_strictlyLE : (cochainResolution P).IsStrictlyLE 0 := by
  dsimp [cochainResolution]
  infer_instance

lemma cochainResolution_projective (hP : P.IsProjective) (n : ℤ) :
    Projective ((cochainResolution P).X n) := by
  letI (i : ℕ) : Projective (P.complex.X i) := by
    letI := hP i
    infer_instance
  dsimp only [cochainResolution]
  infer_instance

variable {P} {B : ModuleCat.{max u v} S} (Q : LeftResolution S B)
    (f : A ⟶ B) (l : P.complex ⟶ Q.complex) (hl : ChainLift P Q f.hom l)

include hl in
lemma augmentation_naturality :
    l ≫ augmentation Q = augmentation P ≫ (ChainComplex.single₀ _).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
    apply ModuleCat.hom_ext
    simpa [augmentation, ChainLift] using hl
  | succ i =>
    exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)).eq_of_tgt _ _

include hl in
lemma cochainAugmentation_naturality :
    HomologicalComplex.extendMap l ComplexShape.embeddingDownNat ≫ cochainAugmentation Q =
      cochainAugmentation P ≫ (CochainComplex.singleFunctor _ 0).map f := by
  have he :
      HomologicalComplex.extendMap ((ChainComplex.single₀ _).map f)
          ComplexShape.embeddingDownNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat B 0 0 rfl).hom =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat A 0 0 rfl).hom ≫
        (CochainComplex.singleFunctor _ 0).map f := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_hom_f,
        HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl),
        ChainComplex.single₀_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc,
        ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.id_comp]
      erw [HomologicalComplex.single_map_f_self]
      simp
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _
  dsimp only [cochainAugmentation]
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    augmentation_naturality Q f l hl, HomologicalComplex.extendMap_comp,
    Category.assoc, he, Category.assoc]

end Resolutions
section Extension
variable {C : Type*} {D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] {ι ι' : Type*} {c : ComplexShape ι}
  {c' : ComplexShape ι'} (K : HomologicalComplex C c) (e : c.Embedding c')

private def mapExtendTerm (i : Option ι) :
    F.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => F.mapZeroObject

/-- Extension by zero commutes with an additive functor, including the
chosen zero terms. No exactness of the functor is used. -/
def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i => mapExtendTerm F K (e.r i)) (by
    intro i j hij
    change (mapExtendTerm F K (e.r i)).hom ≫
      HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) (e.r i) (e.r j) =
        F.map (HomologicalComplex.extend.d K (e.r i) (e.r j)) ≫
          (mapExtendTerm F K (e.r j)).hom
    cases e.r i <;> cases e.r j <;>
      simp [mapExtendTerm, HomologicalComplex.extend.d])
variable {K} {L : HomologicalComplex C c}

@[reassoc]
lemma mapExtendIso_naturality (f : K ⟶ L) :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap f e) ≫
      (mapExtendIso F L e).hom =
    (mapExtendIso F K e).hom ≫
      HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map f) e := by
  ext i : 1
  change F.map (HomologicalComplex.extend.mapX f (e.r i)) ≫
    (mapExtendTerm F L (e.r i)).hom =
      (mapExtendTerm F K (e.r i)).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map f) (e.r i)
  cases e.r i <;> simp [mapExtendTerm, HomologicalComplex.extend.mapX]

@[reassoc]
lemma mapExtendIso_coefficient (G : C ⥤ D) [G.Additive] (τ : F ⟶ G) :
    ((NatTrans.mapHomologicalComplex τ c').app (K.extend e)) ≫
      (mapExtendIso G K e).hom =
    (mapExtendIso F K e).hom ≫
      HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex τ c).app K) e := by
  ext i : 1
  change τ.app (HomologicalComplex.extend.X K (e.r i)) ≫
    (mapExtendTerm G K (e.r i)).hom =
      (mapExtendTerm F K (e.r i)).hom ≫
        HomologicalComplex.extend.mapX ((NatTrans.mapHomologicalComplex τ c).app K) (e.r i)
  cases e.r i with
  | none => exact (isZero_zero D).eq_of_tgt _ _
  | some i => simp [mapExtendTerm, HomologicalComplex.extend.mapX, HomologicalComplex.extend.X]

end Extension
section Models
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
universe u₁ v₁ u₂ v₂ w₁ w₂
variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Abelian C]
  [Category.{v₂} E] [Abelian E]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  (F : C ⥤ E) [F.Additive] (D : ExactLeftData.{u₁,v₁,u₂,v₂,w₁,w₂} F)
  {P X : KMinus C} (p : P ⟶ X)
  (hP : ∀ i : ℤ, Projective (P.obj.as.X i)) (hp : WMinus C p)

/-- The model comparison is fixed by the counit at the projective model.
This normalization is retained before taking homology. -/
def modelIso : D.functor.obj ((QMinus C).obj X) ≅ (minusUValue F).obj P := by
  letI : IsIso ((QMinus C).map p) := Localization.inverts (QMinus C) (WMinus C) p hp
  letI := D.model_iso P hP
  exact (D.functor.mapIso (asIso ((QMinus C).map p))).symm ≪≫
    asIso (D.counit.app P)

@[reassoc]
lemma modelIso_normalization :
    D.functor.map ((QMinus C).map p) ≫ (modelIso F D p hP hp).hom =
      D.counit.app P := by
  letI : IsIso ((QMinus C).map p) := Localization.inverts (QMinus C) (WMinus C) p hp
  simp [modelIso]

@[reassoc]
lemma modelIso_counit :
    (modelIso F D p hP hp).hom ≫ (minusUValue F).map p = D.counit.app X := by
  letI : IsIso ((QMinus C).map p) := Localization.inverts (QMinus C) (WMinus C) p hp
  rw [← cancel_epi (D.functor.map ((QMinus C).map p)),
    modelIso_normalization_assoc]
  exact (D.counit.naturality p).symm

/-- Comparison of any two projective models over a base morphism.
Taking the base morphism to be the identity gives resolution independence. -/
@[reassoc]
lemma modelIso_naturality {Q Y : KMinus C} (q : Q ⟶ Y)
    (hQ : ∀ i : ℤ, Projective (Q.obj.as.X i)) (hq : WMinus C q)
    (l : P ⟶ Q) (f : X ⟶ Y) (hl : l ≫ q = p ≫ f) :
    D.functor.map ((QMinus C).map f) ≫ (modelIso F D q hQ hq).hom =
      (modelIso F D p hP hp).hom ≫ (minusUValue F).map l := by
  letI : IsIso ((QMinus C).map p) := Localization.inverts (QMinus C) (WMinus C) p hp
  rw [← cancel_epi (D.functor.map ((QMinus C).map p)),
    modelIso_normalization_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp, ← hl, Functor.map_comp, Functor.map_comp,
    Category.assoc, modelIso_normalization]
  exact D.counit.naturality l

/-- The same normalized comparison respects any derived transformation
satisfying the original counit square. -/
@[reassoc]
lemma modelIso_transformation (G : C ⥤ E) [G.Additive]
    (D' : ExactLeftData.{u₁,v₁,u₂,v₂,w₁,w₂} G) (τ : F ⟶ G)
    (α : D.functor ⟶ D'.functor)
    (hα : Functor.whiskerLeft (QMinus C) α ≫ D'.counit =
      D.counit ≫ minusUMapValue F G τ) :
    α.app ((QMinus C).obj X) ≫ (modelIso G D' p hP hp).hom =
      (modelIso F D p hP hp).hom ≫ (minusUMapValue F G τ).app P := by
  letI : IsIso ((QMinus C).map p) := Localization.inverts (QMinus C) (WMinus C) p hp
  rw [← cancel_epi (D.functor.map ((QMinus C).map p)),
    modelIso_normalization_assoc, α.naturality_assoc,
    modelIso_normalization]
  exact congr_app hα P

open CategoryTheory.Pretriangulated CategoryTheory.Functor

/-- The counit is an isomorphism of triangles on projective models,
including the third (shifted) arrow. -/
def counitTriangleIso (T : Triangle (KMinus C))
    (h₁ : ∀ i : ℤ, Projective (T.obj₁.obj.as.X i))
    (h₂ : ∀ i : ℤ, Projective (T.obj₂.obj.as.X i))
    (h₃ : ∀ i : ℤ, Projective (T.obj₃.obj.as.X i)) :
    letI := D.commShift
    letI : (QMinus C).CommShift ℤ := quotientShift
    letI : (minusUValue F).CommShift ℤ := inputShift F
    (QMinus C ⋙ D.functor).mapTriangle.obj T ≅ (minusUValue F).mapTriangle.obj T := by
  letI := D.commShift
  letI : (QMinus C).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  letI : NatTrans.CommShift D.counit ℤ := D.counit_shift
  letI := D.model_iso T.obj₁ h₁
  letI := D.model_iso T.obj₂ h₂
  letI := D.model_iso T.obj₃ h₃
  refine Triangle.isoMk _ _ (asIso (D.counit.app T.obj₁))
    (asIso (D.counit.app T.obj₂)) (asIso (D.counit.app T.obj₃))
    (by exact D.counit.naturality T.mor₁) (by exact D.counit.naturality T.mor₂) ?_
  dsimp
  simp only [Category.assoc, NatTrans.shift_app_comm D.counit (1 : ℤ) T.obj₁]
  exact D.counit.naturality_assoc T.mor₃ _


/-- A triangle of projective models identified with a target triangle computes
its image under the derived functor by one normalized triangle isomorphism. -/
def replacementTriangleIso (T : Triangle (KMinus C))
    (X : Triangle (DerivedCategory.Minus C))
    (e : letI : (QMinus C).CommShift ℤ := quotientShift
      (QMinus C).mapTriangle.obj T ≅ X)
    (h₁ : ∀ i : ℤ, Projective (T.obj₁.obj.as.X i))
    (h₂ : ∀ i : ℤ, Projective (T.obj₂.obj.as.X i))
    (h₃ : ∀ i : ℤ, Projective (T.obj₃.obj.as.X i)) :
    letI := D.commShift
    letI : (QMinus C).CommShift ℤ := quotientShift
    letI : (minusUValue F).CommShift ℤ := inputShift F
    D.functor.mapTriangle.obj X ≅ (minusUValue F).mapTriangle.obj T := by
  letI := D.commShift
  letI : (QMinus C).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  exact D.functor.mapTriangle.mapIso e.symm ≪≫
    (Functor.mapTriangleCompIso (QMinus C) D.functor).symm.app T ≪≫
    counitTriangleIso F D T h₁ h₂ h₃

@[simp]
lemma replacementTriangleIso_hom₁ (T : Triangle (KMinus C))
    (X : Triangle (DerivedCategory.Minus C))
    (e : letI : (QMinus C).CommShift ℤ := quotientShift
      (QMinus C).mapTriangle.obj T ≅ X)
    (h₁ : ∀ i : ℤ, Projective (T.obj₁.obj.as.X i))
    (h₂ : ∀ i : ℤ, Projective (T.obj₂.obj.as.X i))
    (h₃ : ∀ i : ℤ, Projective (T.obj₃.obj.as.X i)) :
    (replacementTriangleIso F D T X e h₁ h₂ h₃).hom.hom₁ =
      D.functor.map e.inv.hom₁ ≫ D.counit.app T.obj₁ := by
  simp [replacementTriangleIso, counitTriangleIso]

@[simp]
lemma replacementTriangleIso_hom₃ (T : Triangle (KMinus C))
    (X : Triangle (DerivedCategory.Minus C))
    (e : letI : (QMinus C).CommShift ℤ := quotientShift
      (QMinus C).mapTriangle.obj T ≅ X)
    (h₁ : ∀ i : ℤ, Projective (T.obj₁.obj.as.X i))
    (h₂ : ∀ i : ℤ, Projective (T.obj₂.obj.as.X i))
    (h₃ : ∀ i : ℤ, Projective (T.obj₃.obj.as.X i)) :
    (replacementTriangleIso F D T X e h₁ h₂ h₃).hom.hom₃ =
      D.functor.map e.inv.hom₃ ≫ D.counit.app T.obj₃ := by
  simp [replacementTriangleIso, counitTriangleIso]


/-- The normalized projective-model triangle comparison commutes with the
connecting arrows of the derived homology sequence. -/
lemma replacementTriangleIso_boundary (T : Triangle (KMinus C))
    (X : Triangle (DerivedCategory.Minus C))
    (e : letI : (QMinus C).CommShift ℤ := quotientShift
      (QMinus C).mapTriangle.obj T ≅ X)
    (h₁ : ∀ i : ℤ, Projective (T.obj₁.obj.as.X i))
    (h₂ : ∀ i : ℤ, Projective (T.obj₂.obj.as.X i))
    (h₃ : ∀ i : ℤ, Projective (T.obj₃.obj.as.X i))
    (n m : ℤ) (hnm : n + 1 = m) :
    letI := D.commShift
    letI : (QMinus C).CommShift ℤ := quotientShift
    letI : (minusUValue F).CommShift ℤ := inputShift F
    (DerivedCategory.homologyFunctor E n).map (DerivedCategory.Minus.ι.map
        (replacementTriangleIso F D T X e h₁ h₂ h₃).hom.hom₃) ≫
      (DerivedCategory.homologyFunctor E 0).homologySequenceδ
        (DerivedCategory.Minus.ι.mapTriangle.obj ((minusUValue F).mapTriangle.obj T)) n m hnm =
    (DerivedCategory.homologyFunctor E 0).homologySequenceδ
        (DerivedCategory.Minus.ι.mapTriangle.obj (D.functor.mapTriangle.obj X)) n m hnm ≫
      (DerivedCategory.homologyFunctor E m).map (DerivedCategory.Minus.ι.map
        (replacementTriangleIso F D T X e h₁ h₂ h₃).hom.hom₁) := by
  letI := D.commShift
  letI : (QMinus C).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  exact (DerivedCategory.homologyFunctor E 0).homologySequenceδ_naturality
    (DerivedCategory.Minus.ι.mapTriangle.map
      (replacementTriangleIso F D T X e h₁ h₂ h₃).hom) n m hnm


end Models

section CochainModels
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u₁ v₁ u₂ v₂ w₁ w₂
variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Abelian C]
  [Category.{v₂} E] [Abelian E]

/-- The degree-zero stalk in the bounded-above homotopy category. -/
def minusSingleHomotopy (C : Type u₁) [Category.{v₁} C] [Abelian C] : C ⥤ KMinus C :=
  (minus C).lift (HomotopyCategory.singleFunctor C 0)
    (fun X => (minusStalkValue X).property)

/-- Localization sends the bounded homotopy stalk to the derived stalk. -/
def minusSingleIso {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C] :
    minusSingle C ≅ minusSingleHomotopy C ⋙ QMinus C :=
  ((Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ DerivedCategory C)).whiskeringRight C).preimageIso
      (DerivedCategory.singleFunctorIsoCompQh C 0)

/-- A nonpositive cochain complex, retaining its actual homotopy object. -/
def cochainModel (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] : KMinus C :=
  ⟨(HomotopyCategory.quotient C (.up ℤ)).obj K, 0, by
    change K.IsStrictlyLE 0
    infer_instance⟩

def cochainModelMap {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) : cochainModel K ⟶ cochainModel L :=
  (minus C).homMk ((HomotopyCategory.quotient C (.up ℤ)).map f)

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  (F : C ⥤ E) [F.Additive] (D : ExactLeftData.{u₁,v₁,u₂,v₂,w₁,w₂} F)
  (X : C) (K : CochainComplex C ℤ) [K.IsStrictlyLE 0]
  (p : K ⟶ (CochainComplex.singleFunctor C 0).obj X) (hp : QuasiIso p)
  (hK : ∀ i : ℤ, Projective (K.X i))

include hp in
lemma cochainModelMap_quasiIso : WMinus C (cochainModelMap p) :=
  (HomotopyCategory.quotient_map_mem_quasiIso_iff p).mpr hp

/-- A normalized comparison on the derived object, before applying homology.
The stalk identification is the natural one from the quotient functor. -/
def stalkModelIso :
    D.functor.obj ((minusSingle C).obj X) ≅ (minusUValue F).obj (cochainModel K) :=
  D.functor.mapIso ((minusSingleIso (C := C)).app X) ≪≫
    modelIso F D (cochainModelMap p) hK (cochainModelMap_quasiIso X K p hp)

/-- Homology factors through the actual homotopy and derived quotient functors. -/
def modelHomologyIso (i : ℤ) :
    (DerivedCategory.homologyFunctor E i).obj
      ((minusUValue F).obj (cochainModel K)).obj ≅
        ((F.mapHomologicalComplex (.up ℤ)).obj K).homology i :=
  (DerivedCategory.homologyFunctorFactorsh E i).app
      ((F.mapHomotopyCategory (.up ℤ)).obj (cochainModel K).obj) ≪≫
    (HomotopyCategory.homologyFunctorFactors E (.up ℤ) i).app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)

/-- The canonical computation on an ordinary cochain resolution, retaining
its counit normalization instead of forgetting it in an existential. -/
def cochainComputationIso (n : ℕ) :
    (leftValue F D n).obj X ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology (-(n : ℤ)) :=
  (DerivedCategory.homologyFunctor E (-(n : ℤ))).mapIso
      (DerivedCategory.Minus.ι.mapIso (stalkModelIso F D X K p hp hK)) ≪≫
    modelHomologyIso F K (-(n : ℤ))

variable {X K}

@[reassoc]
lemma stalkModelIso_naturality {Y : C} {L : CochainComplex C ℤ} [L.IsStrictlyLE 0]
    (q : L ⟶ (CochainComplex.singleFunctor C 0).obj Y) (hq : QuasiIso q)
    (hL : ∀ i : ℤ, Projective (L.X i)) (l : K ⟶ L) (f : X ⟶ Y)
    (hl : l ≫ q = p ≫ (CochainComplex.singleFunctor C 0).map f) :
    D.functor.map ((minusSingle C).map f) ≫ (stalkModelIso F D Y L q hq hL).hom =
      (stalkModelIso F D X K p hp hK).hom ≫ (minusUValue F).map (cochainModelMap l) := by
  have hs : cochainModelMap l ≫ cochainModelMap q =
      cochainModelMap p ≫ (minusSingleHomotopy C).map f := by
    apply (minusInclusion C).map_injective
    change (HomotopyCategory.quotient C (.up ℤ)).map l ≫
        (HomotopyCategory.quotient C (.up ℤ)).map q =
      (HomotopyCategory.quotient C (.up ℤ)).map p ≫
        (HomotopyCategory.quotient C (.up ℤ)).map ((CochainComplex.singleFunctor C 0).map f)
    simpa only [← Functor.map_comp] using
      congrArg (HomotopyCategory.quotient C (.up ℤ)).map hl
  have h := modelIso_naturality F D (cochainModelMap p) hK
    (cochainModelMap_quasiIso X K p hp) (cochainModelMap q) hL
    (cochainModelMap_quasiIso Y L q hq) (cochainModelMap l)
    ((minusSingleHomotopy C).map f) hs
  dsimp only [stalkModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc]
  erw [(minusSingleIso (C := C)).hom.naturality]
  rw [Functor.map_comp, Category.assoc]
  erw [h]
  rw [Category.assoc]
  rfl

variable {p hp hK}

@[reassoc]
lemma modelHomologyIso_naturality {L : CochainComplex C ℤ} [L.IsStrictlyLE 0]
    (l : K ⟶ L) (i : ℤ) :
    (DerivedCategory.homologyFunctor E i).map
        (DerivedCategory.Minus.ι.map ((minusUValue F).map (cochainModelMap l))) ≫
      (modelHomologyIso F L i).hom =
    (modelHomologyIso F K i).hom ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map l) i := by
  have h₁ := (DerivedCategory.homologyFunctorFactorsh E i).hom.naturality
    ((F.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient C (.up ℤ)).map l))
  have h₂ := (HomotopyCategory.homologyFunctorFactors E (.up ℤ) i).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map l)
  dsimp only [modelHomologyIso, Iso.trans_hom]
  rw [← Category.assoc]
  erw [h₁]
  rw [Category.assoc]
  erw [h₂]
  simp only [Category.assoc]
  rfl

@[reassoc]
lemma cochainComputationIso_naturality {Y : C} {L : CochainComplex C ℤ} [L.IsStrictlyLE 0]
    (q : L ⟶ (CochainComplex.singleFunctor C 0).obj Y) (hq : QuasiIso q)
    (hL : ∀ i : ℤ, Projective (L.X i)) (l : K ⟶ L) (f : X ⟶ Y)
    (hl : l ≫ q = p ≫ (CochainComplex.singleFunctor C 0).map f) (n : ℕ) :
    (leftValue F D n).map f ≫ (cochainComputationIso F D Y L q hq hL n).hom =
      (cochainComputationIso F D X K p hp hK n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map l) (-(n : ℤ)) := by
  have h := stalkModelIso_naturality F D p hp hK q hq hL l f hl
  have hh := congrArg
    (fun a => (DerivedCategory.homologyFunctor E (-(n : ℤ))).map
      (DerivedCategory.Minus.ι.map a)) h
  dsimp only [cochainComputationIso, Iso.trans_hom, Functor.mapIso_hom]
  dsimp only [leftValue, Functor.comp_map]
  simp only [Functor.map_comp] at hh
  rw [← Category.assoc, hh, Category.assoc]
  erw [modelHomologyIso_naturality]
  rw [Category.assoc]


end CochainModels

section Tensor
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} [Ring R] {A : ModuleCat.{max u v} Rᵐᵒᵖ}
  (P : LeftResolution Rᵐᵒᵖ A) (M : ModuleCat.{w} R)

/-- H⁻ⁿ of the tensor of the reindexed resolution is exactly the original
right-left Tor quotient. -/
def tensorResolutionHomologyIso (n : ℕ) :
    (((tensorFunctor M).mapHomologicalComplex (.up ℤ)).obj
      (cochainResolution P)).homology (-(n : ℤ)) ≅
        ModuleCat.of ℤ (TorWith P M n) :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (-(n : ℤ))).mapIso
      (mapExtendIso (tensorFunctor M) P.complex ComplexShape.embeddingDownNat) ≪≫
    (tensorComplex P.complex M).extendHomologyIso ComplexShape.embeddingDownNat rfl ≪≫
      quotientHomologyIso (tensorComplex P.complex M) n

variable {P} {B : ModuleCat.{max u v} Rᵐᵒᵖ} (Q : LeftResolution Rᵐᵒᵖ B)

@[reassoc]
lemma tensorResolutionHomologyIso_naturality (l : P.complex ⟶ Q.complex) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((tensorFunctor M).mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap l ComplexShape.embeddingDownNat)) (-(n : ℤ)) ≫
      (tensorResolutionHomologyIso Q M n).hom =
    (tensorResolutionHomologyIso P M n).hom ≫
      ModuleCat.ofHom (homologyMap (tensorFirstMap l M) n) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} ℤ) (.up ℤ) (-(n : ℤ))
  have h := congrArg H.map
    (mapExtendIso_naturality (tensorFunctor M) ComplexShape.embeddingDownNat l)
  simp only [Functor.map_comp] at h
  dsimp only [tensorResolutionHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc]
  erw [h]
  simp only [Category.assoc]
  erw [HomologicalComplex.extendHomologyIso_hom_naturality_assoc]
  erw [quotientHomologyIso_naturality]

variable (P)

open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
variable [HasDerivedCategory.{x} (ModuleCat.{max u v} Rᵐᵒᵖ)]
  [HasDerivedCategory.{y} (ModuleCat.{max u v w} ℤ)]
  [(minus (ModuleCat.{max u v} Rᵐᵒᵖ)).IsTriangulated]
  [(minus (ModuleCat.{max u v w} ℤ)).IsTriangulated]
  (D : ExactLeftData (tensorFunctor M :
    ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ))

/-- A single normalized family, on all resolutions and in all degrees. -/
def derivedTensorIso (hP : P.IsProjective) (n : ℕ) :
    (leftValue (tensorFunctor M) D n).obj A ≅ ModuleCat.of ℤ (TorWith P M n) :=
  cochainComputationIso (tensorFunctor M) D A (cochainResolution P)
      (cochainAugmentation P) (cochainAugmentation_quasiIso P)
      (cochainResolution_projective P hP) n ≪≫
    tensorResolutionHomologyIso P M n

/-- Every ordinary projective right resolution computes the actual total
left derived value, without flatness or commutativity hypotheses. -/
theorem derivedValue_iso (hP : P.IsProjective) (n : ℕ) :
    Nonempty ((leftValue (tensorFunctor M) D n).obj A ≅
      ModuleCat.of ℤ (TorWith P M n)) := by
  exact ⟨derivedTensorIso P M D hP n⟩


variable {P}

/-- The normalized derived comparison respects every lift between ordinary
projective resolutions over any right-module map. -/
@[reassoc]
lemma derivedTensorIso_naturality {B : ModuleCat.{max u v} Rᵐᵒᵖ}
    (Q : LeftResolution Rᵐᵒᵖ B) (hP : P.IsProjective) (hQ : Q.IsProjective)
    (f : A ⟶ B) (l : P.complex ⟶ Q.complex) (hl : ChainLift P Q f.hom l) (n : ℕ) :
    (leftValue (tensorFunctor M) D n).map f ≫ (derivedTensorIso Q M D hQ n).hom =
      (derivedTensorIso P M D hP n).hom ≫
        ModuleCat.ofHom (homologyMap (tensorFirstMap l M) n) := by
  have hc := cochainComputationIso_naturality (tensorFunctor M) D
    (p := cochainAugmentation P) (hp := cochainAugmentation_quasiIso P)
    (hK := cochainResolution_projective P hP)
    (cochainAugmentation Q) (cochainAugmentation_quasiIso Q)
    (cochainResolution_projective Q hQ)
    (HomologicalComplex.extendMap l ComplexShape.embeddingDownNat) f
    (cochainAugmentation_naturality Q f l hl) n
  dsimp only [derivedTensorIso, Iso.trans_hom]
  rw [← Category.assoc, hc, Category.assoc]
  erw [tensorResolutionHomologyIso_naturality]
  rw [Category.assoc]

/-- The right naturality square uses the original classical Tor map from
any canonical theory, independently of the selected resolutions. -/
@[reassoc]
lemma derivedTensorIso_right_naturality (n : ℕ) (E : TorMaps.{u,max u v,w} R n)
    {B : ModuleCat.{max u v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ B) (f : A ⟶ B) :
    (leftValue (tensorFunctor M) D n).map f ≫
        (derivedTensorIso Q.val M D Q.property n).hom =
      (derivedTensorIso P.val M D P.property n).hom ≫
        ModuleCat.ofHom (E.map P Q f (𝟙 M)) := by
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists Rᵐᵒᵖ A B
    P.val Q.val P.property f.hom
  have hi : tensorSecondMap Q.val.complex (𝟙 M : M ⟶ M).hom = 𝟙 (tensorComplex Q.val.complex M) := by
    ext i : 1
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  rw [E.formula P Q f (𝟙 M) l hl, hi, Category.comp_id]
  exact derivedTensorIso_naturality M D Q.val P.property Q.property f l hl n

end Tensor

section CochainCoefficient

open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u₁ v₁ u₂ v₂ w₁ w₂
variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Abelian C]
  [Category.{v₂} E] [Abelian E]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  (F G : C ⥤ E) [F.Additive] [G.Additive]
  (D : ExactLeftData.{u₁,v₁,u₂,v₂,w₁,w₂} F)
  (D' : ExactLeftData.{u₁,v₁,u₂,v₂,w₁,w₂} G)
  (τ : F ⟶ G) (α : D.functor ⟶ D'.functor)
  (hα : Functor.whiskerLeft (QMinus C) α ≫ D'.counit =
      D.counit ≫ minusUMapValue F G τ)
  (X : C) (K : CochainComplex C ℤ) [K.IsStrictlyLE 0]
  (p : K ⟶ (CochainComplex.singleFunctor C 0).obj X) (hp : QuasiIso p)
  (hK : ∀ i : ℤ, Projective (K.X i))

include hα in
@[reassoc]
lemma stalkModelIso_transformation :
    α.app ((minusSingle C).obj X) ≫ (stalkModelIso G D' X K p hp hK).hom =
      (stalkModelIso F D X K p hp hK).hom ≫
        (minusUMapValue F G τ).app (cochainModel K) := by
  dsimp only [stalkModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← α.naturality_assoc, Category.assoc]
  erw [modelIso_transformation F D (cochainModelMap p) hK
    (cochainModelMap_quasiIso X K p hp) G D' τ α hα]

@[reassoc]
lemma modelHomologyIso_transformation (i : ℤ) :
    (DerivedCategory.homologyFunctor E i).map
        (DerivedCategory.Minus.ι.map ((minusUMapValue F G τ).app (cochainModel K))) ≫
      (modelHomologyIso G K i).hom =
    (modelHomologyIso F K i).hom ≫
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) i := by
  have h₁ := (DerivedCategory.homologyFunctorFactorsh E i).hom.naturality
    ((τ.mapHomotopyCategory (.up ℤ)).app ((HomotopyCategory.quotient C (.up ℤ)).obj K))
  have h₂ := (HomotopyCategory.homologyFunctorFactors E (.up ℤ) i).hom.naturality
    ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)
  dsimp only [modelHomologyIso, Iso.trans_hom]
  rw [← Category.assoc]
  erw [h₁]
  rw [Category.assoc]
  erw [h₂]
  simp only [Category.assoc]
  rfl

include hα in
@[reassoc]
lemma cochainComputationIso_transformation (n : ℕ) :
    (DerivedCategory.homologyFunctor E (-(n : ℤ))).map
        (DerivedCategory.Minus.ι.map (α.app ((minusSingle C).obj X))) ≫
      (cochainComputationIso G D' X K p hp hK n).hom =
      (cochainComputationIso F D X K p hp hK n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) (-(n : ℤ)) := by
  have h := stalkModelIso_transformation F G D D' τ α hα X K p hp hK
  have hh := congrArg
    (fun a => (DerivedCategory.homologyFunctor E (-(n : ℤ))).map
      (DerivedCategory.Minus.ι.map a)) h
  dsimp only [cochainComputationIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp] at hh
  rw [← Category.assoc, hh, Category.assoc]
  erw [modelHomologyIso_transformation]
  rw [Category.assoc]

end CochainCoefficient
section TensorCoefficient

open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} [Ring R] {A : ModuleCat.{max u v} Rᵐᵒᵖ}
  (P : LeftResolution Rᵐᵒᵖ A) {M N : ModuleCat.{w} R} (g : M ⟶ N)

@[reassoc]
lemma tensorResolutionHomologyIso_coefficient (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (AdvancedHomologicalAlgebra.TorBalance.tensorCoefficientMap g.hom) (.up ℤ)).app
            (cochainResolution P)) (-(n : ℤ)) ≫
      (tensorResolutionHomologyIso P N n).hom =
    (tensorResolutionHomologyIso P M n).hom ≫
      ModuleCat.ofHom (homologyMap (tensorSecondMap P.complex g.hom) n) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} ℤ) (.up ℤ) (-(n : ℤ))
  have h := congrArg H.map
    (mapExtendIso_coefficient (tensorFunctor M) (K := P.complex) ComplexShape.embeddingDownNat
      (tensorFunctor N) (AdvancedHomologicalAlgebra.TorBalance.tensorCoefficientMap g.hom))
  simp only [Functor.map_comp] at h
  dsimp only [tensorResolutionHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc]
  erw [h]
  simp only [Category.assoc]
  erw [HomologicalComplex.extendHomologyIso_hom_naturality_assoc]
  erw [quotientHomologyIso_naturality]
  rfl

variable [HasDerivedCategory.{x} (ModuleCat.{max u v} Rᵐᵒᵖ)]
  [HasDerivedCategory.{y} (ModuleCat.{max u v w} ℤ)]
  [(minus (ModuleCat.{max u v} Rᵐᵒᵖ)).IsTriangulated]
  [(minus (ModuleCat.{max u v w} ℤ)).IsTriangulated]
  (D : ExactLeftData (tensorFunctor M :
    ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ))
  (D' : ExactLeftData (tensorFunctor N :
    ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ))
  (α : D.functor ⟶ D'.functor)
  (hα : Functor.whiskerLeft (QMinus (ModuleCat.{max u v} Rᵐᵒᵖ)) α ≫ D'.counit =
    D.counit ≫ minusUMapValue (tensorFunctor M) (tensorFunctor N)
      (AdvancedHomologicalAlgebra.TorBalance.tensorCoefficientMap g.hom))

include hα in
@[reassoc]
lemma derivedTensorIso_coefficient (hP : P.IsProjective) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} ℤ) (-(n : ℤ))).map
        (DerivedCategory.Minus.ι.map (α.app ((minusSingle (ModuleCat.{max u v} Rᵐᵒᵖ)).obj A))) ≫
      (derivedTensorIso P N D' hP n).hom =
    (derivedTensorIso P M D hP n).hom ≫
      ModuleCat.ofHom (homologyMap (tensorSecondMap P.complex g.hom) n) := by
  have hc := cochainComputationIso_transformation (tensorFunctor M) (tensorFunctor N) D D'
    (AdvancedHomologicalAlgebra.TorBalance.tensorCoefficientMap g.hom) α hα A
    (cochainResolution P) (cochainAugmentation P) (cochainAugmentation_quasiIso P)
    (cochainResolution_projective P hP) n
  dsimp only [derivedTensorIso, Iso.trans_hom]
  rw [← Category.assoc, hc, Category.assoc]
  erw [tensorResolutionHomologyIso_coefficient]
  rw [Category.assoc]

variable {P}
include hα in
@[reassoc]
lemma derivedTensorIso_coefficient_naturality (n : ℕ) (E : TorMaps.{u,max u v,w} R n)
    (P : ProjectiveChoice Rᵐᵒᵖ A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} ℤ) (-(n : ℤ))).map
        (DerivedCategory.Minus.ι.map (α.app ((minusSingle (ModuleCat.{max u v} Rᵐᵒᵖ)).obj A))) ≫
      (derivedTensorIso P.val N D' P.property n).hom =
    (derivedTensorIso P.val M D P.property n).hom ≫ ModuleCat.ofHom (E.map P P (𝟙 A) g) := by
  have hl : ChainLift P.val P.val (𝟙 A : A ⟶ A).hom (𝟙 P.val.complex) := by
    dsimp [ChainLift]
  rw [E.formula P P (𝟙 A) g (𝟙 P.val.complex) hl]
  have hi : tensorFirstMap (𝟙 P.val.complex) M = 𝟙 (tensorComplex P.val.complex M) :=
    (tensorFunctor M).mapHomologicalComplex (.down ℕ) |>.map_id _
  rw [hi, Category.id_comp]
  exact derivedTensorIso_coefficient P.val g D D' α hα P.property n
end TensorCoefficient

section ClassicalComparisons
open Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]

lemma horseshoe_exists (S : ShortComplex (RightModules.{u,v} R))
    (hS : S.ShortExact) (P : ProjectiveChoice Rᵐᵒᵖ S.X₁)
    (Q : ProjectiveChoice Rᵐᵒᵖ S.X₃) :
    Nonempty (P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P.val Q.val) := by
  apply P103.Ch10.Horseshoe.projective_horseshoe Rᵐᵒᵖ S.X₁ S.X₂ S.X₃
    S.f.hom S.g.hom hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g P.val Q.val P.property Q.property

variable [HasDerivedCategory.{x} (RightModules.{u,v} R)]
  [HasDerivedCategory.{y} (Groups.{u,v,w})]
  [(Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels.minus (RightModules.{u,v} R)).IsTriangulated]
  [(Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels.minus (Groups.{u,v,w})).IsTriangulated]

lemma comparison_balance (D : DerivedFamily.{u,v,w,x,y} R)
    (iso : ∀ (M : Coefficients.{u,w} R) (A : RightModules.{u,v} R)
      (P : ProjectiveChoice Rᵐᵒᵖ A) (n : ℕ),
      (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.leftValue (tensor R M) (D M) n).obj A ≅
        ModuleCat.of ℤ (TorWith P.val M n))
    (M : Coefficients.{u,w} R) (A : RightModules.{u,v} R)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (Q : LeftResolution R M) (hQ : Q.IsProjective) :
    ∃ (a : Augmentations P.val Q) (hL : QuasiIsomorphism a.left)
      (hR : QuasiIsomorphism a.right), ∀ n : ℕ,
      ∃ e : (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.leftValue (tensor R M) (D M) n).obj A ≃ₗ[ℤ]
        Homology (leftOrdinaryTensorComplex A Q.complex) n,
        ∀ z, e z = balanceEquiv a hL hR n ((iso M A P n).hom z) := by
  obtain ⟨a, hL, hR⟩ := AdvancedHomologicalAlgebra.TorBalance.balance R A M P.val Q P.property hQ
  refine ⟨a, hL, hR, ?_⟩
  intro n
  exact ⟨(iso M A P n).toLinearEquiv.trans (balanceEquiv a hL hR n), fun z => rfl⟩

section Zero
variable (T : CanonicalTheory.{u,max u v,w} R) (M : Coefficients.{u,w} R)
variable {A B : RightModules.{u,v} R}

def torZeroIso (P : LeftResolution Rᵐᵒᵖ A) :
    ModuleCat.of ℤ (TorWith P M 0) ≅ (tensor R M).obj A :=
  (P103.Ch11.ExtTorDefinitions.torZero P M).toIntLinearEquiv.toModuleIso

lemma torZeroIso_naturality (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ B) (f : A ⟶ B) :
    ModuleCat.ofHom ((T.torMaps 0).map P Q f (𝟙 M)) ≫ (torZeroIso M Q.val).hom =
      (torZeroIso M P.val).hom ≫ (tensor R M).map f := by
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists Rᵐᵒᵖ A B P.val Q.val P.property f.hom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change P103.Ch11.ExtTorDefinitions.torZero Q.val M ((T.torMaps 0).map P Q f (𝟙 M) x) =
    tensorMap f.hom LinearMap.id (P103.Ch11.ExtTorDefinitions.torZero P.val M x)
  rw [(T.torMaps 0).formula P Q f (𝟙 M) l hl]
  exact P103.Ch11.ExtTorDefinitions.tor_zero_natural R A B P.val Q.val M M f.hom LinearMap.id l hl
    (P103.Ch11.ExtTorDefinitions.torZero P.val M) (P103.Ch11.ExtTorDefinitions.torZero Q.val M)
    (P103.Ch11.ExtTorDefinitions.torZero_class P.val M)
    (P103.Ch11.ExtTorDefinitions.torZero_class Q.val M) x

variable (F : RightModules.{u,v} R ⥤ Groups.{u,v,w})
    (e : ∀ (A : RightModules.{u,v} R) (P : ProjectiveChoice Rᵐᵒᵖ A),
      F.obj A ≅ ModuleCat.of ℤ (TorWith P.val M 0))
    (he : ∀ {A B : RightModules.{u,v} R} (P : ProjectiveChoice Rᵐᵒᵖ A)
      (Q : ProjectiveChoice Rᵐᵒᵖ B) (f : A ⟶ B),
      F.map f ≫ (e B Q).hom = (e A P).hom ≫ ModuleCat.ofHom ((T.torMaps 0).map P Q f (𝟙 M)))

def zeroIso : F ≅ tensor R M :=
  NatIso.ofComponents (fun A => e A (T.rightResolutions A) ≪≫ torZeroIso M (T.rightResolutions A).val)
    (by
      intro A B f
      change F.map f ≫ ((e B (T.rightResolutions B)).hom ≫ (torZeroIso M (T.rightResolutions B).val).hom) =
        ((e A (T.rightResolutions A)).hom ≫ (torZeroIso M (T.rightResolutions A).val).hom) ≫ (tensor R M).map f
      rw [← Category.assoc, he (T.rightResolutions A) (T.rightResolutions B) f, Category.assoc, torZeroIso_naturality T M (T.rightResolutions A) (T.rightResolutions B) f]
      simp only [Category.assoc])

lemma zeroIso_formula (A : RightModules.{u,v} R) (P : ProjectiveChoice Rᵐᵒᵖ A)
    (z : cycles (tensorComplex P.val.complex M) 0) :
    (zeroIso T M F e he).hom.app A ((e A P).inv (homologyClass _ 0 z)) =
      tensorMap P.val.ε LinearMap.id z.val := by
  have h := he P (T.rightResolutions A) (𝟙 A)
  simp only [F.map_id, Category.id_comp] at h
  have hcomp : (zeroIso T M F e he).hom.app A = (e A P).hom ≫ (torZeroIso M P.val).hom := by
    change (e A (T.rightResolutions A)).hom ≫ (torZeroIso M (T.rightResolutions A).val).hom = _
    rw [h, Category.assoc, torZeroIso_naturality T M P (T.rightResolutions A) (𝟙 A)]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hh : (e A P).inv ≫ (zeroIso T M F e he).hom.app A = (torZeroIso M P.val).hom := by
    rw [hcomp, Iso.inv_hom_id_assoc]
  calc
    _ = (torZeroIso M P.val).hom (homologyClass _ 0 z) := ConcreteCategory.congr_hom hh _
    _ = _ := P103.Ch11.ExtTorDefinitions.torZero_class P.val M z

end Zero

end ClassicalComparisons

section TensorZeroAugmentation
set_option maxHeartbeats 1600000
set_option quotPrecheck false
set_option hygiene false
open HomologicalComplex P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions

private lemma homologyMap_single_eq_of_f
    {ι : Type*} {ι' : Type*} [DecidableEq ι'] {d : ComplexShape ι} {d' : ComplexShape ι'}
    {C : Type*} [Category* C] [Abelian C]
    (K : HomologicalComplex C d') (T : HomologicalComplex C d) (e : d.Embedding d')
    {i : ι} {j : ι'} (h : e.f i = j) (X : C)
    (f : K ⟶ (single C d' j).obj X) (g : K ⟶ T.extend e)
    (p : T.homology i ⟶ X) (a : T.X i ⟶ X)
    (hp : T.homologyπ i ≫ p = T.iCycles i ≫ a)
    (hf : f.f j ≫ (singleObjXSelf d' j X).hom = g.f j ≫ (T.extendXIso e h).hom ≫ a) :
    homologyMap f j ≫ (singleObjHomologySelfIso d' j X).hom =
      homologyMap g j ≫ (T.extendHomologyIso e h).hom ≫ p := by
  simp only [← cancel_epi (K.homologyπ j),
    homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, cyclesMap_i_assoc, homologyπ_extendHomologyIso_hom_assoc,
    hp, extendCyclesIso_hom_iCycles_assoc, hf]

variable {R : Type u} [Ring R] {A : ModuleCat.{max u v} Rᵐᵒᵖ}
  (P : LeftResolution Rᵐᵒᵖ A) (M : ModuleCat.{w} R)

local notation "F" => (tensorFunctor M : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ)
local notation "c" => ComplexShape.down ℕ
local notation "c'" => ComplexShape.up ℤ
local notation "e" => ComplexShape.embeddingDownNat

private lemma torZeroIso_projection :
    (tensorComplex P.complex M).homologyπ 0 ≫
      (quotientHomologyIso (tensorComplex P.complex M) 0).hom ≫ (torZeroIso M P).hom =
    (tensorComplex P.complex M).iCycles 0 ≫ (F).map (ModuleCat.ofHom P.ε) := by
  rw [quotientHomologyIso_projection_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (torZeroIso M P).hom (homologyClass _ 0
      (((tensorComplex P.complex M).sc 0).moduleCatCyclesIso.hom z)) =
    tensorMap P.ε LinearMap.id ((tensorComplex P.complex M).iCycles 0 z)
  change P103.Ch11.ExtTorDefinitions.torZero P M (homologyClass _ 0
      (((tensorComplex P.complex M).sc 0).moduleCatCyclesIso.hom z)) = _
  rw [P103.Ch11.ExtTorDefinitions.torZero_class]
  congr 1

private lemma mapExtendTerm_XIso {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (G : C ⥤ D) [G.Additive] {ι : Type*} {d : ComplexShape ι}
    (K : HomologicalComplex C d) {i : Option ι} {j : ι} (h : i = some j) :
    (mapExtendTerm G K i).hom ≫ (extend.XIso ((G.mapHomologicalComplex d).obj K) h).hom =
        G.map (extend.XIso K h).hom := by
  subst i
  change 𝟙 _ ≫ 𝟙 _ = G.map (𝟙 _)
  rw [Category.comp_id, G.map_id]

private lemma mapExtendIso_f_zero :
    (mapExtendIso F P.complex e).hom.f 0 ≫
      ((tensorComplex P.complex M).extendXIso e (show (e).f 0 = 0 from rfl)).hom =
    (F).map (P.complex.extendXIso e (show (e).f 0 = 0 from rfl)).hom := by
  exact mapExtendTerm_XIso (F) P.complex ((e).r_eq_some (show (e).f 0 = 0 from rfl))

private lemma tensorCochainAugmentation_f_zero :
    (((F).mapHomologicalComplex c').map (cochainAugmentation P) ≫
      ((F).mapCochainComplexSingleFunctor 0).hom.app A).f 0 ≫
        (singleObjXSelf c' 0 ((F).obj A)).hom =
     (F).map (P.complex.extendXIso e (show (e).f 0 = 0 from rfl)).hom ≫
       (F).map (ModuleCat.ofHom P.ε) := by
  rw [HomologicalComplex.comp_f]
  change (F).map ((cochainAugmentation P).f 0) ≫
    ((singleMapHomologicalComplex F c' 0).hom.app A).f 0 ≫
      (singleObjXSelf c' 0 ((F).obj A)).hom = _
  rw [singleMapHomologicalComplex_hom_app_self, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, ← (F).map_comp, ← (F).map_comp]
  congr 1
  simp only [cochainAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendMap_f _ _
      (show (e).f 0 = 0 from rfl), Category.assoc, Iso.inv_hom_id_assoc,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id, augmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]

lemma tensorResolutionHomologyIso_zero :
    homologyMap (((F).mapHomologicalComplex c').map (cochainAugmentation P) ≫
      ((F).mapCochainComplexSingleFunctor 0).hom.app A) 0 ≫
        (singleObjHomologySelfIso c' 0 ((F).obj A)).hom =
    (tensorResolutionHomologyIso P M 0).hom ≫ (torZeroIso M P).hom := by
  let K := ((F).mapHomologicalComplex c').obj (cochainResolution P)
  let L := (single (ModuleCat.{max u v w} ℤ) c' 0).obj ((F).obj A)
  let q : K ⟶ L := ((F).mapHomologicalComplex c').map (cochainAugmentation P) ≫
    ((F).mapCochainComplexSingleFunctor 0).hom.app A
  let T := tensorComplex P.complex M
  let J := T.extend e
  let g : K ⟶ J := (mapExtendIso F P.complex e).hom
  let h : (e).f 0 = 0 := rfl
  let p := (quotientHomologyIso T 0).hom ≫ (torZeroIso M P).hom
  let a : T.X 0 ⟶ (F).obj A := (F).map (ModuleCat.ofHom P.ε)
  have hp : T.homologyπ 0 ≫ p = T.iCycles 0 ≫ a := by
    exact torZeroIso_projection.{u,v,w} P M
  have hf : q.f 0 ≫ (singleObjXSelf c' 0 ((F).obj A)).hom =
      g.f 0 ≫ (T.extendXIso e h).hom ≫ a := by
    calc
      _ = (F).map (P.complex.extendXIso e h).hom ≫ a :=
        tensorCochainAugmentation_f_zero.{u,v,w} P M
      _ = _ := by
        rw [← Category.assoc]
        exact congrArg (fun k => k ≫ a) (mapExtendIso_f_zero.{u,v,w} P M).symm
  calc
    _ = homologyMap g 0 ≫ (T.extendHomologyIso e h).hom ≫ p :=
      homologyMap_single_eq_of_f K T e h ((F).obj A) q g p a hp hf
    _ = _ := by
      change homologyMap g 0 ≫ (T.extendHomologyIso e h).hom ≫ p =
        (homologyMap g 0 ≫ (T.extendHomologyIso e h).hom ≫ (quotientHomologyIso T 0).hom) ≫
          (torZeroIso M P).hom
      simp only [p, Category.assoc]

end TensorZeroAugmentation


section BoundaryReindexing
section Abstract
variable {ι : Type w} {ι' : Type t} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {C : Type*} [Category* C] [Abelian C]
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {n m : ι} {n' m' : ι'} (hn : e.f n = n')
    (hm : c.next n = m) (hm' : c'.next n' = m') {A : C}
    (f : A ⟶ K.X n) (hf : f ≫ K.d n m = 0)

@[reassoc] lemma liftCycles_extendHomology :
    (K.extend e).liftCycles (f ≫ (K.extendXIso e hn).inv) m' hm'
      (by simpa only [Category.assoc] using
        (HomologicalComplex.extend.comp_d_eq_zero_iff K e hn hm hm' f).mp hf) ≫
        (K.extend e).homologyπ n' ≫ (K.extendHomologyIso e hn).hom =
      K.liftCycles f m hm hf ≫ K.homologyπ n := by
  rw [HomologicalComplex.homologyπ_extendHomologyIso_hom, ← Category.assoc]
  congr 1
  apply (cancel_mono (K.iCycles n)).mp
  simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
    HomologicalComplex.liftCycles_i_assoc, Iso.inv_hom_id, Category.comp_id,
    HomologicalComplex.liftCycles_i]
end Abstract
section Modules
variable {S : Type u} [Ring S] {ι : Type w} {ι' : Type t}
  {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex (ModuleCat.{max u v} S) c) (n : ι)
def elementMap (x : K.X n) : ModuleCat.of S (ULift.{v} S) ⟶ K.X n :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton S (K.X n) x).comp
    (ULift.moduleEquiv.toLinearMap))

@[simp] lemma elementMap_one (x : K.X n) : elementMap K n x ⟨1⟩ = x := by
  simp [elementMap, LinearMap.toSpanSingleton_apply]

lemma liftCycles_quotient {m : ι} (h : c.next n = m) (x : cycles K n)
    (hx : elementMap K n x.val ≫ K.d n m = 0) :
    (K.liftCycles (elementMap K n x.val) m h hx ≫ K.homologyπ n ≫
      (quotientHomologyIso K n).hom) ⟨1⟩ = homologyClass K n x := by
  rw [quotientHomologyIso_projection]
  change homologyClass K n ((K.sc n).moduleCatCyclesIso.hom
    (K.liftCycles (elementMap K n x.val) m h hx ⟨1⟩)) = _
  congr 1
  apply Subtype.ext
  change ((K.sc n).moduleCatLeftHomologyData.i
    ((K.sc n).moduleCatCyclesIso.hom
      (K.liftCycles (elementMap K n x.val) m h hx ⟨1⟩))) = _
  rw [ShortComplex.moduleCatCyclesIso_hom_i_apply]
  change (K.liftCycles (elementMap K n x.val) m h hx ≫ K.iCycles n) ⟨1⟩ = _
  rw [HomologicalComplex.liftCycles_i]
  exact elementMap_one K n x.val


variable (e : c.Embedding c') {m : ι} {n' m' : ι'} (hn : e.f n = n')
    (hm : c.next n = m) (hm' : c'.next n' = m')

def extendedQuotientHomologyIso :
    (K.extend e).homology n' ≅ ModuleCat.of S (Homology K n) :=
  K.extendHomologyIso e hn ≪≫ quotientHomologyIso K n

lemma extendedClass (z : cycles K n)
    (hz : elementMap K n z.val ≫ K.d n m = 0) :
    ((K.extend e).liftCycles
      (elementMap K n z.val ≫ (K.extendXIso e hn).inv) m' hm'
      (by
        rw [Category.assoc]
        exact (HomologicalComplex.extend.comp_d_eq_zero_iff K e hn hm hm'
          (elementMap K n z.val)).mp hz) ≫
        (K.extend e).homologyπ n' ≫
          (extendedQuotientHomologyIso K n e hn).hom) ⟨1⟩ = homologyClass K n z := by
  dsimp only [extendedQuotientHomologyIso, Iso.trans_hom]
  rw [liftCycles_extendHomology_assoc K e hn hm hm']
  exact liftCycles_quotient K n hm z hz

lemma extendedBoundaryConnecting
    (S₀ : ShortComplex (HomologicalComplex (ModuleCat.{max u v} S) c))
    (e : c.Embedding c')
    (hE : (S₀.map (e.extendFunctor (ModuleCat.{max u v} S))).ShortExact)
    (n m : ι) (hnm : c.Rel n m) :
    P103.Specs.Ch10.HomologySequence.Connecting S₀.f S₀.g n m
      ((extendedQuotientHomologyIso S₀.X₁ m e rfl).hom.hom.comp
        ((hE.δ (e.f n) (e.f m) (e.rel hnm)).hom.comp
          (extendedQuotientHomologyIso S₀.X₃ n e rfl).inv.hom)) := by
  intro z b a hb ha
  have hz : elementMap S₀.X₃ n z.val ≫ S₀.X₃.d n m = 0 := by
    ext r
    change (S₀.X₃.d n m).hom (r.down • z.val) = 0
    rw [map_smul]
    have hz₀ := z.property
    change (S₀.X₃.d n (c.next n)).hom z.val = 0 at hz₀
    rw [c.next_eq' hnm] at hz₀
    rw [hz₀, smul_zero]
  have hb' : elementMap S₀.X₂ n b ≫ S₀.g.f n = elementMap S₀.X₃ n z.val := by
    ext r
    change (S₀.g.f n).hom (r.down • b) = r.down • z.val
    rw [map_smul, hb]
  have ha' : elementMap S₀.X₁ m a.val ≫ S₀.f.f m =
      elementMap S₀.X₂ n b ≫ S₀.X₂.d n m := by
    ext r
    change (S₀.f.f m).hom (r.down • a.val) = (S₀.X₂.d n m).hom (r.down • b)
    rw [map_smul, map_smul, ha]
  have hze :
      (elementMap S₀.X₃ n z.val ≫ (S₀.X₃.extendXIso e rfl).inv) ≫
        (S₀.X₃.extend e).d (e.f n) (e.f m) = 0 := by
    rw [S₀.X₃.extend_d_eq e rfl rfl, Category.assoc, Iso.inv_hom_id_assoc,
      ← Category.assoc, hz, zero_comp]
  have hbe : (elementMap S₀.X₂ n b ≫ (S₀.X₂.extendXIso e rfl).inv) ≫
      (HomologicalComplex.extendMap S₀.g e).f (e.f n) =
        elementMap S₀.X₃ n z.val ≫ (S₀.X₃.extendXIso e rfl).inv := by
    rw [HomologicalComplex.extendMap_f _ _ rfl, Category.assoc,
      Iso.inv_hom_id_assoc, ← Category.assoc, hb']
  have hae : (elementMap S₀.X₁ m a.val ≫ (S₀.X₁.extendXIso e rfl).inv) ≫
      (HomologicalComplex.extendMap S₀.f e).f (e.f m) =
        (elementMap S₀.X₂ n b ≫ (S₀.X₂.extendXIso e rfl).inv) ≫
          (S₀.X₂.extend e).d (e.f n) (e.f m) := by
    rw [HomologicalComplex.extendMap_f _ _ rfl, S₀.X₂.extend_d_eq e rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← Category.assoc, ha']
  have E := hE.δ_eq (e.f n) (e.f m) (e.rel hnm)
    (elementMap S₀.X₃ n z.val ≫ (S₀.X₃.extendXIso e rfl).inv) hze
    (elementMap S₀.X₂ n b ≫ (S₀.X₂.extendXIso e rfl).inv) hbe
    (elementMap S₀.X₁ m a.val ≫ (S₀.X₁.extendXIso e rfl).inv) hae
    (c'.next (e.f m)) rfl
  have EE := congrArg (fun f : ModuleCat.of S (ULift.{v} S) ⟶
      (S₀.X₁.extend e).homology (e.f m) =>
        (f ≫ (extendedQuotientHomologyIso S₀.X₁ m e rfl).hom) ⟨1⟩) E
  have hzq := extendedClass S₀.X₃ n e rfl (c.next_eq' hnm)
    (c'.next_eq' (e.rel hnm)) z hz
  have ha0 : elementMap S₀.X₁ m a.val ≫ S₀.X₁.d m (c.next m) = 0 := by
    ext r
    change (S₀.X₁.d m (c.next m)).hom (r.down • a.val) = 0
    rw [map_smul, a.property, smul_zero]
  have haq := extendedClass S₀.X₁ m e rfl rfl rfl a ha0
  change (extendedQuotientHomologyIso S₀.X₁ m e rfl).hom
    ((hE.δ (e.f n) (e.f m) (e.rel hnm))
      ((extendedQuotientHomologyIso S₀.X₃ n e rfl).inv
        (homologyClass S₀.X₃ n z))) = _
  rw [← hzq]
  have hinv : (extendedQuotientHomologyIso S₀.X₃ n e rfl).inv
      (((S₀.X₃.extend e).liftCycles
        (elementMap S₀.X₃ n z.val ≫ (S₀.X₃.extendXIso e rfl).inv)
        (e.f m) (c'.next_eq' (e.rel hnm)) hze ≫
        (S₀.X₃.extend e).homologyπ (e.f n) ≫
        (extendedQuotientHomologyIso S₀.X₃ n e rfl).hom) ⟨1⟩) =
      (((S₀.X₃.extend e).liftCycles
        (elementMap S₀.X₃ n z.val ≫ (S₀.X₃.extendXIso e rfl).inv)
        (e.f m) (c'.next_eq' (e.rel hnm)) hze ≫
        (S₀.X₃.extend e).homologyπ (e.f n)) ⟨1⟩) := by
    exact CategoryTheory.Iso.hom_inv_id_apply
      (extendedQuotientHomologyIso S₀.X₃ n e rfl) _
  rw [hinv]
  exact EE.trans haq
end Modules

end BoundaryReindexing

section OrdinaryHorseshoe
open P103.Specs.Ch10.Comparison
variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{max u v} R))
  (P : LeftResolution R S.X₁) (Q : LeftResolution R S.X₃)
  (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P Q)

def horseshoeChain : ShortComplex (ChainComplex (ModuleCat.{max u v} R) ℕ) :=
  ShortComplex.mk H.inclusion H.projection (by
    ext n x
    change (H.projection.f n).hom ((H.inclusion.f n).hom x) = 0
    rw [H.projection_apply, H.inclusion_apply])

def horseshoeChainSplitting (n : ℕ) :
    ((horseshoeChain S P Q H).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := ModuleCat.ofHom ((LinearMap.fst R (P.complex.X n) (Q.complex.X n)).comp
    (H.term n).toLinearMap)
  s := ModuleCat.ofHom ((H.term n).symm.toLinearMap.comp
    (LinearMap.inr R (P.complex.X n) (Q.complex.X n)))
  f_r := by
    ext x
    change ((H.term n) ((H.inclusion.f n).hom x)).1 = x
    rw [H.inclusion_apply]
  s_g := by
    ext x
    change (H.projection.f n).hom ((H.term n).symm (0, x)) = x
    rw [H.projection_apply, (H.term n).apply_symm_apply]
  id := by
    ext x
    change (H.inclusion.f n).hom ((H.term n x).1) +
      (H.term n).symm (0, (H.projection.f n).hom x) = x
    apply (H.term n).injective
    rw [map_add, H.inclusion_apply, (H.term n).apply_symm_apply, H.projection_apply]
    ext <;> simp

def horseshoeCochain : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  (horseshoeChain S P Q H).map
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{max u v} R))

def horseshoeCochainSplitting (n : ℤ) :
    ((horseshoeCochain S P Q H).map (HomologicalComplex.eval _ _ n)).Splitting :=
  ComplexShape.embeddingDownNat.splittingExtend (horseshoeChainSplitting S P Q H) n

def horseshoeAugmentation : horseshoeCochain S P Q H ⟶
    S.map (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0) where
  τ₁ := cochainAugmentation P
  τ₂ := cochainAugmentation H.middle
  τ₃ := cochainAugmentation Q
  comm₁₂ := by
    exact (cochainAugmentation_naturality H.middle S.f H.inclusion H.augmentation_inclusion).symm
  comm₂₃ := by
    exact (cochainAugmentation_naturality Q S.g H.projection H.augmentation_projection).symm

lemma horseshoeCochain_shortExact : (horseshoeCochain S P Q H).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (horseshoeCochainSplitting S P Q H n).shortExact)

variable {E : Type*} [Category* E] [Abelian E] (F : ModuleCat.{max u v} R ⥤ E)
    [F.Additive]

def horseshoeImageSplitting (n : ℤ) :
    (((horseshoeCochain S P Q H).map (F.mapHomologicalComplex (.up ℤ))).map
      (HomologicalComplex.eval _ _ n)).Splitting :=
  (horseshoeCochainSplitting S P Q H n).map F

lemma horseshoeImage_shortExact :
    ((horseshoeCochain S P Q H).map (F.mapHomologicalComplex (.up ℤ))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (horseshoeImageSplitting S P Q H F n).shortExact)


end OrdinaryHorseshoe

section SplitTriangles
open CategoryTheory.Preadditive CochainComplex CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting)

noncomputable def splittingConeHomotopy :
    Homotopy (mappingCone.descShortComplex S ≫ homOfDegreewiseSplit S σ)
      (mappingCone.triangle S.f).mor₃ := by
  refine mappingCone.descHomotopy S.f _ _ 0
    ((Cochain.ofHoms (fun p => (σ p).r)).rightShift 1 (-1) (by omega)) ?_ ?_
  · ext p q hpq
    simp only [Cochain.add_v, Cochain.zero_v, δ_zero, zero_add,
      Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc,
      mappingCone.inl_v_descShortComplex_f_assoc,
      zero_comp, mappingCone.inl_v_triangle_mor₃_f]
    simp only [Cochain.rightShift_v (Cochain.ofHoms (fun p => (σ p).r)) 1 (-1) (by omega) p q hpq p (by omega),
      Cochain.ofHoms_v]
    have h := (σ p).f_r
    dsimp at h
    rw [← Category.assoc, h, Category.id_comp, add_neg_cancel]
  · apply Cochain.ext
    intro p q hpq
    obtain rfl : q = p := by omega
    simp only [Cochain.ofHom_v, HomologicalComplex.comp_f,
      Category.assoc, mappingCone.inr_f_descShortComplex_f_assoc,
      mappingCone.inr_f_triangle_mor₃_f, Cochain.add_v, add_zero]
    simp [δ_v, Cochain.rightShift_v, Cochain.ofHoms_v]
    simp only [cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.mk_v]
    have hgs := (σ q).g_s
    have hfr := (σ (q + 1)).f_r
    dsimp at hgs hfr
    rw [← Category.assoc, hgs, sub_comp, Category.id_comp,
      Category.assoc, S.f.comm_assoc, hfr, Category.comp_id]
    exact sub_eq_neg_add _ _

variable [HasDerivedCategory.{w} C]

@[reassoc]
lemma splittingDerivedBoundary (hS : S.ShortExact) :
    DerivedCategory.Q.map (homOfDegreewiseSplit S σ) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ =
        DerivedCategory.triangleOfSESδ hS := by
  have := mappingCone.quasiIso_descShortComplex hS
  rw [← cancel_epi (DerivedCategory.Q.map (mappingCone.descShortComplex S)),
    ← DerivedCategory.Q.map_comp_assoc,
    DerivedCategory.Q_map_eq_of_homotopy C (splittingConeHomotopy S σ),
    DerivedCategory.descShortComplex_triangleOfSESδ]

noncomputable def splittingDerivedTriangleIso (hS : S.ShortExact) :
    DerivedCategory.Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ) ≅
      DerivedCategory.triangleOfSES hS :=
  CategoryTheory.Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by
      dsimp
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      exact splittingDerivedBoundary S σ hS)


end SplitTriangles


open CategoryTheory.Pretriangulated CategoryTheory.Functor
open HomologicalComplex CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

section BoundedSplitTriangles
variable {C : Type u} [Category.{v} C] [Abelian C]
  [(minus C).IsTriangulated]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting)
  [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0]

def cochainModelTriangle : Triangle (KMinus C) :=
  Triangle.mk (cochainModelMap S.f) (cochainModelMap S.g)
    ((minus C).homMk (ShiftedHom.map (homOfDegreewiseSplit S σ)
      (HomotopyCategory.quotient C (.up ℤ)) ≫
        ((minusInclusion C).commShiftIso (1 : ℤ)).inv.app (cochainModel S.X₁)))

def cochainModelTriangleInclusionIso :
    (minusInclusion C).mapTriangle.obj (cochainModelTriangle S σ) ≅
      (HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj (triangleOfDegreewiseSplit S σ) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [cochainModelTriangle, triangleOfDegreewiseSplit, cochainModelMap]) (by simp [cochainModelTriangle, triangleOfDegreewiseSplit, cochainModelMap]) ?_
  dsimp [cochainModelTriangle, triangleOfDegreewiseSplit, ShiftedHom.map]
  simp
  erw [Category.comp_id]

variable [HasDerivedCategory.{w} C]

omit [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0] in
def cochainQuotientIso (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    ((QMinus C).obj (cochainModel K)).obj ≅ DerivedCategory.Q.obj K :=
  (DerivedCategory.quotientCompQhIso C).app K

omit [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0] in
@[reassoc]
lemma cochainQuotientIso_naturality {K L : CochainComplex C ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L) :
    DerivedCategory.Minus.ι.map ((QMinus C).map (cochainModelMap f)) ≫
      (cochainQuotientIso L).hom =
    (cochainQuotientIso K).hom ≫ DerivedCategory.Q.map f := by
  exact (DerivedCategory.quotientCompQhIso C).hom.naturality f

omit [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0] in
def minusQuotientTriangleIso (T : Triangle (KMinus C)) :
    letI : (QMinus C).CommShift ℤ := quotientShift
    DerivedCategory.Minus.ι.mapTriangle.obj ((QMinus C).mapTriangle.obj T) ≅
      DerivedCategory.Qh.mapTriangle.obj ((minusInclusion C).mapTriangle.obj T) := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  let e : QMinus C ⋙ DerivedCategory.Minus.ι ≅ minusInclusion C ⋙ DerivedCategory.Qh :=
    ObjectProperty.liftCompιIso _ _ _
  letI : NatTrans.CommShift e.hom ℤ := by
    dsimp [e, QMinus]
    infer_instance
  exact (Functor.mapTriangleCompIso (QMinus C) DerivedCategory.Minus.ι).symm.app T ≪≫
    (Functor.mapTriangleIso e).app T ≪≫
    (Functor.mapTriangleCompIso (minusInclusion C) DerivedCategory.Qh).app T

def cochainModelDerivedTriangleIso :
    letI : (QMinus C).CommShift ℤ := quotientShift
    DerivedCategory.Minus.ι.mapTriangle.obj ((QMinus C).mapTriangle.obj (cochainModelTriangle S σ)) ≅
      DerivedCategory.Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ) := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  exact minusQuotientTriangleIso (cochainModelTriangle S σ) ≪≫
    DerivedCategory.Qh.mapTriangle.mapIso (cochainModelTriangleInclusionIso S σ) ≪≫
    (Functor.mapTriangleCompIso (HomotopyCategory.quotient C (.up ℤ)) DerivedCategory.Qh).symm.app _ ≪≫
    (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).app _

end BoundedSplitTriangles
open CochainComplex CochainComplex.HomComplex CategoryTheory.Pretriangulated CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

section AugmentationTriangles
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{x} C]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting)
section Augmentation
variable {T : ShortComplex C} (hT : T.ShortExact)
  (a : S ⟶ T.map (CochainComplex.singleFunctor C 0))
  [QuasiIso a.τ₁] [QuasiIso a.τ₂] [QuasiIso a.τ₃]

def augmentationDerivedTriangleMap (hS : S.ShortExact) :
    DerivedCategory.triangleOfSES hS ⟶
      DerivedCategory.triangleOfSES (hT.map_of_exact (CochainComplex.singleFunctor C 0)) :=
  DerivedCategory.triangleOfSES.map hS _ a

noncomputable def augmentationDerivedTriangleIso (hS : S.ShortExact) :
    DerivedCategory.Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ) ≅ hT.singleTriangle := by
  let f := augmentationDerivedTriangleMap S hT a hS
  letI : IsIso f.hom₁ := inferInstanceAs (IsIso (DerivedCategory.Q.map a.τ₁))
  letI : IsIso f.hom₂ := inferInstanceAs (IsIso (DerivedCategory.Q.map a.τ₂))
  letI : IsIso f.hom₃ := inferInstanceAs (IsIso (DerivedCategory.Q.map a.τ₃))
  letI : IsIso f := CategoryTheory.Pretriangulated.Triangle.isIso_of_isIsos f inferInstance inferInstance inferInstance
  exact splittingDerivedTriangleIso S σ hS ≪≫ asIso f ≪≫ hT.singleTriangleIso.symm

@[simp]
lemma augmentationDerivedTriangleIso_hom₁ (hS : S.ShortExact) :
    (augmentationDerivedTriangleIso S σ hT a hS).hom.hom₁ = DerivedCategory.Q.map a.τ₁ := by
  simp [augmentationDerivedTriangleIso, splittingDerivedTriangleIso, augmentationDerivedTriangleMap]
  erw [Category.comp_id]

@[simp]
lemma augmentationDerivedTriangleIso_hom₂ (hS : S.ShortExact) :
    (augmentationDerivedTriangleIso S σ hT a hS).hom.hom₂ = DerivedCategory.Q.map a.τ₂ := by
  simp [augmentationDerivedTriangleIso, splittingDerivedTriangleIso, augmentationDerivedTriangleMap]
  erw [Category.comp_id]

@[simp]
lemma augmentationDerivedTriangleIso_hom₃ (hS : S.ShortExact) :
    (augmentationDerivedTriangleIso S σ hT a hS).hom.hom₃ = DerivedCategory.Q.map a.τ₃ := by
  simp [augmentationDerivedTriangleIso, splittingDerivedTriangleIso, augmentationDerivedTriangleMap]
  erw [Category.comp_id]

end Augmentation

end AugmentationTriangles

section BoundedAugmentationTriangles
variable {C : Type u} [Category.{v} C] [Abelian C]
  [(minus C).IsTriangulated]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting)
  [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0]
  [HasDerivedCategory.{x} C]
@[simp]
lemma cochainModelDerivedTriangleIso_hom₁ :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (cochainModelDerivedTriangleIso S σ).hom.hom₁ = (cochainQuotientIso S.X₁).hom := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  simp [cochainModelDerivedTriangleIso, minusQuotientTriangleIso,
    cochainModelTriangleInclusionIso, cochainQuotientIso, ObjectProperty.liftCompιIso]
  erw [Category.id_comp]

@[simp]
lemma cochainModelDerivedTriangleIso_hom₂ :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (cochainModelDerivedTriangleIso S σ).hom.hom₂ = (cochainQuotientIso S.X₂).hom := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  simp [cochainModelDerivedTriangleIso, minusQuotientTriangleIso,
    cochainModelTriangleInclusionIso, cochainQuotientIso, ObjectProperty.liftCompιIso]
  erw [Category.id_comp]

@[simp]
lemma cochainModelDerivedTriangleIso_hom₃ :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (cochainModelDerivedTriangleIso S σ).hom.hom₃ = (cochainQuotientIso S.X₃).hom := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  simp [cochainModelDerivedTriangleIso, minusQuotientTriangleIso,
    cochainModelTriangleInclusionIso, cochainQuotientIso, ObjectProperty.liftCompιIso]
  erw [Category.id_comp]

omit [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0] in
lemma minusSingleIso_inv_app (X : C) :
    DerivedCategory.Minus.ι.map ((minusSingleIso (C := C)).app X).inv =
      (cochainQuotientIso ((CochainComplex.singleFunctor C 0).obj X)).hom := by
  calc
    _ = (DerivedCategory.singleFunctorIsoCompQh C 0).inv.app X := by
      exact congr_app (((FullyFaithful.ofFullyFaithful
          (DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ DerivedCategory C)).whiskeringRight C).map_preimage
        (X := minusSingleHomotopy C ⋙ QMinus C)
        (Y := minusSingle C) (DerivedCategory.singleFunctorIsoCompQh C 0).inv) X
    _ = _ := by
      simp [DerivedCategory.singleFunctorIsoCompQh, DerivedCategory.singleFunctorsPostcompQhIso,
        SingleFunctors.postcompIsoOfIso, SingleFunctors.postcompPostcompIso, cochainQuotientIso]
      erw [Category.id_comp]

section Augmentation
variable {T : ShortComplex C} (hT : T.ShortExact)
  (hS : S.ShortExact)
  (a : S ⟶ T.map (CochainComplex.singleFunctor C 0))
  [QuasiIso a.τ₁] [QuasiIso a.τ₂] [QuasiIso a.τ₃]

def minusSingleTriangleInclusionIso :
    DerivedCategory.Minus.ι.mapTriangle.obj (minusTriangle C hT) ≅ hT.singleTriangle :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [minusTriangle, minusSingle, ObjectProperty.lift])
    (by simp [minusTriangle, minusSingle, ObjectProperty.lift])
    (by simp [minusTriangle, Category.assoc, minusSingle, ObjectProperty.lift])

def boundedAugmentationDerivedTriangleIso :
    letI : (QMinus C).CommShift ℤ := quotientShift
    DerivedCategory.Minus.ι.mapTriangle.obj ((QMinus C).mapTriangle.obj (cochainModelTriangle S σ)) ≅
      DerivedCategory.Minus.ι.mapTriangle.obj (minusTriangle C hT) := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  exact cochainModelDerivedTriangleIso S σ ≪≫
    augmentationDerivedTriangleIso S σ hT a hS ≪≫
    (minusSingleTriangleInclusionIso hT).symm

@[simp]
lemma boundedAugmentationDerivedTriangleIso_hom₁ :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (boundedAugmentationDerivedTriangleIso S σ hT hS a).hom.hom₁ =
      (cochainQuotientIso S.X₁).hom ≫ DerivedCategory.Q.map a.τ₁ := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  simp [boundedAugmentationDerivedTriangleIso, minusSingleTriangleInclusionIso]
  erw [Category.comp_id]

@[simp]
lemma boundedAugmentationDerivedTriangleIso_hom₃ :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (boundedAugmentationDerivedTriangleIso S σ hT hS a).hom.hom₃ =
      (cochainQuotientIso S.X₃).hom ≫ DerivedCategory.Q.map a.τ₃ := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  simp [boundedAugmentationDerivedTriangleIso, minusSingleTriangleInclusionIso]
  erw [Category.comp_id]

def boundedAugmentationTriangleIso :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (QMinus C).mapTriangle.obj (cochainModelTriangle S σ) ≅ minusTriangle C hT := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  exact (DerivedCategory.Minus.ι.mapTriangle).preimageIso
    (boundedAugmentationDerivedTriangleIso S σ hT hS a)

local instance mapSingleX1Bound : (T.map (CochainComplex.singleFunctor C 0)).X₁.IsStrictlyLE 0 := by
  change ((CochainComplex.singleFunctor C 0).obj T.X₁).IsStrictlyLE 0
  infer_instance

local instance mapSingleX3Bound : (T.map (CochainComplex.singleFunctor C 0)).X₃.IsStrictlyLE 0 := by
  change ((CochainComplex.singleFunctor C 0).obj T.X₃).IsStrictlyLE 0
  infer_instance

@[simp]
lemma boundedAugmentationTriangleIso_hom₁ :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (boundedAugmentationTriangleIso S σ hT hS a).hom.hom₁ =
      (QMinus C).map (cochainModelMap a.τ₁) ≫
        ((minusSingleIso (C := C)).app T.X₁).inv := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  apply DerivedCategory.Minus.ι.map_injective
  have hm : DerivedCategory.Minus.ι.map (boundedAugmentationTriangleIso S σ hT hS a).hom.hom₁ =
      (boundedAugmentationDerivedTriangleIso S σ hT hS a).hom.hom₁ := by
    exact congrArg (fun f => f.hom₁)
      ((DerivedCategory.Minus.ι.mapTriangle).map_preimage
        (boundedAugmentationDerivedTriangleIso S σ hT hS a).hom)
  rw [hm, boundedAugmentationDerivedTriangleIso_hom₁, CategoryTheory.Functor.map_comp,
    minusSingleIso_inv_app]
  exact (cochainQuotientIso_naturality a.τ₁).symm

@[simp]
lemma boundedAugmentationTriangleIso_hom₃ :
    letI : (QMinus C).CommShift ℤ := quotientShift
    (boundedAugmentationTriangleIso S σ hT hS a).hom.hom₃ =
      (QMinus C).map (cochainModelMap a.τ₃) ≫
        ((minusSingleIso (C := C)).app T.X₃).inv := by
  letI : (QMinus C).CommShift ℤ := quotientShift
  apply DerivedCategory.Minus.ι.map_injective
  have hm : DerivedCategory.Minus.ι.map (boundedAugmentationTriangleIso S σ hT hS a).hom.hom₃ =
      (boundedAugmentationDerivedTriangleIso S σ hT hS a).hom.hom₃ := by
    exact congrArg (fun f => f.hom₃)
      ((DerivedCategory.Minus.ι.mapTriangle).map_preimage
        (boundedAugmentationDerivedTriangleIso S σ hT hS a).hom)
  rw [hm, boundedAugmentationDerivedTriangleIso_hom₃, CategoryTheory.Functor.map_comp,
    minusSingleIso_inv_app]
  exact (cochainQuotientIso_naturality a.τ₃).symm

end Augmentation

end BoundedAugmentationTriangles


section AugmentationModelNormalization
universe u' v' w'
variable {C : Type u} {E : Type u'} [Category.{v} C] [Abelian C]
  [Category.{v'} E] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  (F : C ⥤ E) [F.Additive] (D : ExactLeftData.{u,v,u',v',w,w'} F)
  (X : C) (K : CochainComplex C ℤ) [K.IsStrictlyLE 0]
  (p : K ⟶ (CochainComplex.singleFunctor C 0).obj X) (hp : QuasiIso p)
  (hK : ∀ i : ℤ, Projective (K.X i))
  (e : (QMinus C).obj (cochainModel K) ≅ (minusSingle C).obj X)
  (he : e.hom = (QMinus C).map (cochainModelMap p) ≫
    ((minusSingleIso (C := C)).app X).inv)

include he in
lemma augmentationModelIso_normalization :
    D.functor.map e.inv ≫ D.counit.app (cochainModel K) =
      (stalkModelIso F D X K p hp hK).hom := by
  have hm : D.functor.map e.hom ≫
      D.functor.map ((minusSingleIso (C := C)).app X).hom =
        D.functor.map ((QMinus C).map (cochainModelMap p)) := by
    rw [← D.functor.map_comp, he, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← cancel_epi (D.functor.map e.hom), ← D.functor.map_comp_assoc,
    e.hom_inv_id, D.functor.map_id, Category.id_comp]
  dsimp only [stalkModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hm]
  exact (modelIso_normalization F D (cochainModelMap p) hK
    (cochainModelMap_quasiIso X K p hp)).symm

end AugmentationModelNormalization

section SplitTriangleImages
universe u' v'
variable {C : Type u} {E : Type u'} [Category.{v} C] [Abelian C]
  [Category.{v'} E] [Abelian E] (F : C ⥤ E) [F.Additive]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C (.up ℤ) n)).Splitting)

/-- An additive functor preserves a specified degreewise splitting. -/
def mapDegreewiseSplitting (n : ℤ) :
    ((S.map (F.mapHomologicalComplex (.up ℤ))).map (eval E (.up ℤ) n)).Splitting :=
  (σ n).map F

/-- The positive connecting cochain of a split short exact sequence is
preserved by an additive functor, with its standard cochain shift. -/
lemma map_homOfDegreewiseSplit :
    (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.homOfDegreewiseSplit S σ) ≫
      ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ =
    CochainComplex.homOfDegreewiseSplit (S.map (F.mapHomologicalComplex (.up ℤ)))
      (mapDegreewiseSplitting F S σ) := by
  ext n : 1
  simp [CochainComplex.homOfDegreewiseSplit_f,
    CochainComplex.cocycleOfDegreewiseSplit, mapDegreewiseSplitting, Functor.map_comp]

/-- Consequently the entire split triangle is preserved with identity
comparisons on each of its three vertices. -/
def mapTriangleOfDegreewiseSplitIso :
    (F.mapHomologicalComplex (.up ℤ)).mapTriangle.obj
      (CochainComplex.triangleOfDegreewiseSplit S σ) ≅
    CochainComplex.triangleOfDegreewiseSplit (S.map (F.mapHomologicalComplex (.up ℤ)))
      (mapDegreewiseSplitting F S σ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by
      simpa using map_homOfDegreewiseSplit F S σ)

end SplitTriangleImages

section QuotientModelHomology
universe u' v' w'
variable {C : Type u} {E : Type u'} [Category.{v} C] [Abelian C]
  [Category.{v'} E] [Abelian E] (F : C ⥤ E) [F.Additive]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]

/-- The two quotient-factor comparisons used for models agree with the
ordinary derived-category comparison, including its specified quotient iso. -/
lemma modelHomologyIso_eq_quotient (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (i : ℤ) :
    (modelHomologyIso F K i).hom =
      (DerivedCategory.homologyFunctor E i).map
        ((DerivedCategory.quotientCompQhIso E).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        (DerivedCategory.homologyFunctorFactors E i).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  change (DerivedCategory.homologyFunctorFactorsh E i).hom.app
      ((HomotopyCategory.quotient E (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      (HomotopyCategory.homologyFunctorFactors E (.up ℤ) i).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) = _
  rw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  simp

/-- The homology comparison from the homotopy quotient respects every
connecting map attached to a triangle, with its standard shift. -/
lemma homologySequenceδ_Qh (T : Triangle (HomotopyCategory E (.up ℤ)))
    (n m : ℤ) (hnm : n + 1 = m) :
    (DerivedCategory.homologyFunctor E 0).homologySequenceδ
        (DerivedCategory.Qh.mapTriangle.obj T) n m hnm ≫
      (DerivedCategory.homologyFunctorFactorsh E m).hom.app T.obj₁ =
    (DerivedCategory.homologyFunctorFactorsh E n).hom.app T.obj₃ ≫
      (HomotopyCategory.homologyFunctor E (.up ℤ) 0).homologySequenceδ T n m hnm := by
  dsimp only [Functor.homologySequenceδ, Functor.mapTriangle_obj]
  change (DerivedCategory.homologyFunctor E 0).shiftMap
      (ShiftedHom.map T.mor₃ DerivedCategory.Qh) n m _ ≫ _ = _
  rw [DerivedCategory.shiftMap_homologyFunctor_map_Qh T.mor₃ n m (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- On a cochain triangle the composite quotient comparisons respect the
triangle's connecting map, in every integer degree. -/
lemma quotientModelHomology_boundary (T : Triangle (CochainComplex E ℤ))
    (n m : ℤ) (hnm : n + 1 = m) :
    (DerivedCategory.homologyFunctor E 0).homologySequenceδ
        (DerivedCategory.Qh.mapTriangle.obj
          ((HomotopyCategory.quotient E (.up ℤ)).mapTriangle.obj T)) n m hnm ≫
      ((DerivedCategory.homologyFunctorFactorsh E m).hom.app
          ((HomotopyCategory.quotient E (.up ℤ)).obj T.obj₁) ≫
        (HomotopyCategory.homologyFunctorFactors E (.up ℤ) m).hom.app T.obj₁) =
    ((DerivedCategory.homologyFunctorFactorsh E n).hom.app
          ((HomotopyCategory.quotient E (.up ℤ)).obj T.obj₃) ≫
        (HomotopyCategory.homologyFunctorFactors E (.up ℤ) n).hom.app T.obj₃) ≫
      (HomologicalComplex.homologyFunctor E (.up ℤ) 0).shiftMap T.mor₃ n m (by omega) := by
  rw [← Category.assoc]
  erw [homologySequenceδ_Qh ((HomotopyCategory.quotient E (.up ℤ)).mapTriangle.obj T) n m hnm]
  erw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj T n m hnm]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rfl


end QuotientModelHomology

section InputTriangleModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
universe u₁ v₁ u₂ v₂ w₁ w₂
variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Abelian C]
  [Category.{v₂} E] [Abelian E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  (F : C ⥤ E) [F.Additive]

def termwiseTriangleInclusionIso (T : Triangle (KMinus C)) :
    letI : (termwiseMinusValue F).CommShift ℤ := termwiseShift F
    (minusInclusion E).mapTriangle.obj ((termwiseMinusValue F).mapTriangle.obj T) ≅
      (F.mapHomotopyCategory (.up ℤ)).mapTriangle.obj ((minusInclusion C).mapTriangle.obj T) := by
  letI : (termwiseMinusValue F).CommShift ℤ := termwiseShift F
  let e : termwiseMinusValue F ⋙ minusInclusion E ≅
      minusInclusion C ⋙ F.mapHomotopyCategory (.up ℤ) :=
    ObjectProperty.liftCompιIso _ _ _
  letI : NatTrans.CommShift e.hom ℤ := by
    dsimp [e, termwiseMinusValue]
    infer_instance
  exact (Functor.mapTriangleCompIso (termwiseMinusValue F) (minusInclusion E)).symm.app T ≪≫
    (Functor.mapTriangleIso e).app T ≪≫
    (Functor.mapTriangleCompIso (minusInclusion C) (F.mapHomotopyCategory (.up ℤ))).app T

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} E]

def inputTriangleInclusionIso (T : Triangle (KMinus C)) :
    letI : (minusUValue F).CommShift ℤ := inputShift F
    DerivedCategory.Minus.ι.mapTriangle.obj ((minusUValue F).mapTriangle.obj T) ≅
      DerivedCategory.Qh.mapTriangle.obj
        ((F.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
          ((minusInclusion C).mapTriangle.obj T)) := by
  letI : (termwiseMinusValue F).CommShift ℤ := termwiseShift F
  letI : (QMinus E).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  exact DerivedCategory.Minus.ι.mapTriangle.mapIso
      ((Functor.mapTriangleCompIso (termwiseMinusValue F) (QMinus E)).app T) ≪≫
    minusQuotientTriangleIso ((termwiseMinusValue F).mapTriangle.obj T) ≪≫
    DerivedCategory.Qh.mapTriangle.mapIso (termwiseTriangleInclusionIso F T)

@[simp]
lemma inputTriangleInclusionIso_hom₁ (T : Triangle (KMinus C)) :
    (inputTriangleInclusionIso F T).hom.hom₁ = 𝟙 _ := by
  simp [inputTriangleInclusionIso, termwiseTriangleInclusionIso,
    minusQuotientTriangleIso, ObjectProperty.liftCompιIso]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

@[simp]
lemma inputTriangleInclusionIso_hom₃ (T : Triangle (KMinus C)) :
    (inputTriangleInclusionIso F T).hom.hom₃ = 𝟙 _ := by
  simp [inputTriangleInclusionIso, termwiseTriangleInclusionIso,
    minusQuotientTriangleIso, ObjectProperty.liftCompιIso]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl


end InputTriangleModels

section SplitTriangleHomology
variable {E : Type u} [Category.{v} E] [Abelian E]
lemma homOfDegreewiseSplit_shiftMap (S : ShortComplex (CochainComplex E ℤ))
    (σ : ∀ n, (S.map (eval E (.up ℤ) n)).Splitting) (hS : S.ShortExact)
    (n : ℤ) :
    (HomologicalComplex.homologyFunctor E (.up ℤ) 0).shiftMap
      (homOfDegreewiseSplit S σ) n (n + 1) (by omega) = hS.δ n (n + 1) rfl := by
  let c := S.X₃.iCycles n
  let b := c ≫ (σ n).s
  let a := b ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r
  have hsg : (σ n).s ≫ S.g.f n = 𝟙 _ := (σ n).s_g
  have hrf : (σ (n + 1)).r ≫ S.f.f (n + 1) =
      𝟙 _ - S.g.f (n + 1) ≫ (σ (n + 1)).s := (σ (n + 1)).r_f
  have hb : b ≫ S.g.f n = c := by simp [b, hsg]
  have ha : a ≫ S.f.f (n + 1) = b ≫ S.X₂.d n (n + 1) := by
    dsimp only [a]
    simp only [Category.assoc]
    rw [hrf]
    simp only [CategoryTheory.Preadditive.comp_sub, Category.comp_id,
      Category.assoc, sub_eq_self]
    rw [← S.g.comm_assoc, reassoc_of% hb]
    simp [c]
  have hs := hS.δ_eq n (n + 1) rfl c (by simp [c]) b hb a ha (n + 2) (by simp; omega)
  have hid : S.X₃.liftCycles c (n + 1) (by simp) (by simp [c]) = 𝟙 _ := by
    rw [← cancel_mono (S.X₃.iCycles n), liftCycles_i]
    simp [c]
  rw [hid, Category.id_comp] at hs
  apply (cancel_epi (S.X₃.homologyπ n)).mp
  rw [hs]
  dsimp only [Functor.shiftMap, CochainComplex.homologyFunctor_shift]
  erw [HomologicalComplex.homologyπ_naturality_assoc]
  erw [← Category.id_comp (cyclesMap (homOfDegreewiseSplit S σ) n), ← hid,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  erw [S.X₁.liftCycles_shift_homologyπ_assoc _ _ _ _ (n + 1) (by omega) (n + 2) (by simp; omega)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change _ ≫ (S.X₁.homologyπ (n + 1) ≫ 𝟙 (S.X₁.homology (n + 1))) = _
  rw [Category.comp_id]
  congr 1
  rw [← cancel_mono (S.X₁.iCycles (n + 1)), liftCycles_i, liftCycles_i]
  simp [a, b, c, CochainComplex.homOfDegreewiseSplit_f,
    CochainComplex.cocycleOfDegreewiseSplit]

end SplitTriangleHomology

section SplitModelHomology
universe u' v' w'
variable {C : Type u} {E : Type u'} [Category.{v} C] [Abelian C]
  [Category.{v'} E] [Abelian E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} E]
  (F : C ⥤ E) [F.Additive]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C (.up ℤ) n)).Splitting)
  [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0]

/-- The termwise image of a bounded split-model triangle is the quotient
of the split triangle of the termwise image, with identity vertex maps. -/
def modelImageSplitTriangleIso :
    letI : (minusUValue F).CommShift ℤ := inputShift F
    DerivedCategory.Minus.ι.mapTriangle.obj
      ((minusUValue F).mapTriangle.obj (cochainModelTriangle S σ)) ≅
    DerivedCategory.Qh.mapTriangle.obj ((HomotopyCategory.quotient E (.up ℤ)).mapTriangle.obj
      (triangleOfDegreewiseSplit (S.map (F.mapHomologicalComplex (.up ℤ)))
        (mapDegreewiseSplitting F S σ))) := by
  letI : (minusUValue F).CommShift ℤ := inputShift F
  let e : (F.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
      ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj
        (triangleOfDegreewiseSplit S σ)) ≅
    (HomotopyCategory.quotient E (.up ℤ)).mapTriangle.obj
      ((F.mapHomologicalComplex (.up ℤ)).mapTriangle.obj (triangleOfDegreewiseSplit S σ)) :=
    (Functor.mapTriangleCompIso (HomotopyCategory.quotient C (.up ℤ))
      (F.mapHomotopyCategory (.up ℤ))).symm.app _ ≪≫
      (Functor.mapTriangleIso (F.mapHomotopyCategoryFactors (.up ℤ))).app _ ≪≫
      (Functor.mapTriangleCompIso (F.mapHomologicalComplex (.up ℤ))
        (HomotopyCategory.quotient E (.up ℤ))).app _
  exact inputTriangleInclusionIso F (cochainModelTriangle S σ) ≪≫
    DerivedCategory.Qh.mapTriangle.mapIso
      ((F.mapHomotopyCategory (.up ℤ)).mapTriangle.mapIso
        (cochainModelTriangleInclusionIso S σ) ≪≫ e ≪≫
        (HomotopyCategory.quotient E (.up ℤ)).mapTriangle.mapIso
          (mapTriangleOfDegreewiseSplitIso F S σ))

@[simp]
lemma modelImageSplitTriangleIso_hom₁ : (modelImageSplitTriangleIso F S σ).hom.hom₁ = 𝟙 _ := by
  simp [modelImageSplitTriangleIso, inputTriangleInclusionIso_hom₁,
    cochainModelTriangleInclusionIso, mapTriangleOfDegreewiseSplitIso]
  erw [CategoryTheory.Functor.mapHomotopyCategoryFactors_hom_app,
    CategoryTheory.Functor.map_id]
  rfl

@[simp]
lemma modelImageSplitTriangleIso_hom₃ : (modelImageSplitTriangleIso F S σ).hom.hom₃ = 𝟙 _ := by
  simp [modelImageSplitTriangleIso, inputTriangleInclusionIso_hom₃,
    cochainModelTriangleInclusionIso, mapTriangleOfDegreewiseSplitIso]
  erw [CategoryTheory.Functor.mapHomotopyCategoryFactors_hom_app,
    CategoryTheory.Functor.map_id]
  rfl

lemma modelSplitBoundary (hFS : (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact)
    (n : ℤ) :
    letI : (minusUValue F).CommShift ℤ := inputShift F
    (DerivedCategory.homologyFunctor E 0).homologySequenceδ
        (DerivedCategory.Minus.ι.mapTriangle.obj
          ((minusUValue F).mapTriangle.obj (cochainModelTriangle S σ))) n (n + 1) rfl ≫
      (modelHomologyIso F S.X₁ (n + 1)).hom =
    (modelHomologyIso F S.X₃ n).hom ≫ hFS.δ n (n + 1) rfl := by
  letI : (minusUValue F).CommShift ℤ := inputShift F
  have he := (DerivedCategory.homologyFunctor E 0).homologySequenceδ_naturality
    (modelImageSplitTriangleIso F S σ).hom n (n + 1) rfl
  simp only [modelImageSplitTriangleIso_hom₁, modelImageSplitTriangleIso_hom₃,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at he
  rw [← he]
  have hb := quotientModelHomology_boundary
    (triangleOfDegreewiseSplit (S.map (F.mapHomologicalComplex (.up ℤ)))
      (mapDegreewiseSplitting F S σ)) n (n + 1) rfl
  erw [homOfDegreewiseSplit_shiftMap _ _ hFS n] at hb
  exact hb

lemma modelSplitBoundary_adjacent
    (hFS : (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact)
    (n m : ℤ) (hnm : n + 1 = m) :
    letI : (minusUValue F).CommShift ℤ := inputShift F
    (DerivedCategory.homologyFunctor E 0).homologySequenceδ
        (DerivedCategory.Minus.ι.mapTriangle.obj
          ((minusUValue F).mapTriangle.obj (cochainModelTriangle S σ))) n m hnm ≫
      (modelHomologyIso F S.X₁ m).hom =
    (modelHomologyIso F S.X₃ n).hom ≫ hFS.δ n m hnm := by
  subst m
  exact modelSplitBoundary F S σ hFS n


end SplitModelHomology

section CompositeHomologyBoundary
variable {C₁ C₂ E : Type*} [Category* C₁] [Category* C₂] [Category* E]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [Abelian E] [HasDerivedCategory E]
  (F : C₁ ⥤ C₂) [F.CommShift ℤ] (G : C₂ ⥤ DerivedCategory E) [G.CommShift ℤ]
lemma derivedHomologyBoundary_comp (T : Triangle C₁) (n m : ℤ) (hnm : n + 1 = m) :
    (DerivedCategory.homologyFunctor E 0).homologySequenceδ
      ((F ⋙ G).mapTriangle.obj T) n m hnm =
    (DerivedCategory.homologyFunctor E 0).homologySequenceδ
      (G.mapTriangle.obj (F.mapTriangle.obj T)) n m hnm := by
  have h := (DerivedCategory.homologyFunctor E 0).homologySequenceδ_naturality
    ((Functor.mapTriangleCompIso F G).hom.app T) n m hnm
  simpa using h.symm

end CompositeHomologyBoundary

section CochainResolutionBoundary
universe u' v' w'
variable {C : Type u} {E : Type u'} [Category.{v} C] [Abelian C]
  [Category.{v'} E] [Abelian E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} E]
  (F : C ⥤ E) [F.Additive] (D : ExactLeftData.{u,v,u',v',w,w'} F)
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C (.up ℤ) n)).Splitting)
  [S.X₁.IsStrictlyLE 0] [S.X₂.IsStrictlyLE 0] [S.X₃.IsStrictlyLE 0]
  {T : ShortComplex C} (hT : T.ShortExact)
  (a : S ⟶ T.map (CochainComplex.singleFunctor C 0))
  [QuasiIso a.τ₁] [QuasiIso a.τ₂] [QuasiIso a.τ₃]
  (h₁ : ∀ i : ℤ, Projective (S.X₁.X i))
  (h₂ : ∀ i : ℤ, Projective (S.X₂.X i))
  (h₃ : ∀ i : ℤ, Projective (S.X₃.X i))

local instance cochainBoundarySingleX1Bound : (T.map (CochainComplex.singleFunctor C 0)).X₁.IsStrictlyLE 0 := by
  change ((CochainComplex.singleFunctor C 0).obj T.X₁).IsStrictlyLE 0
  infer_instance
local instance cochainBoundarySingleX3Bound : (T.map (CochainComplex.singleFunctor C 0)).X₃.IsStrictlyLE 0 := by
  change ((CochainComplex.singleFunctor C 0).obj T.X₃).IsStrictlyLE 0
  infer_instance

include h₂ in
lemma cochainComputationIso_boundary_of_triangleIso
    (e : letI : (QMinus C).CommShift ℤ := quotientShift
      (QMinus C).mapTriangle.obj (cochainModelTriangle S σ) ≅ minusTriangle C hT)
    (he₁ : e.hom.hom₁ = (QMinus C).map (cochainModelMap a.τ₁) ≫
      ((minusSingleIso (C := C)).app T.X₁).inv)
    (he₃ : e.hom.hom₃ = (QMinus C).map (cochainModelMap a.τ₃) ≫
      ((minusSingleIso (C := C)).app T.X₃).inv)
    (hFS : (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact) (n : ℕ) :
    leftBoundary F D hT n ≫
        (cochainComputationIso F D T.X₁ S.X₁ a.τ₁ inferInstance h₁ n).hom =
      (cochainComputationIso F D T.X₃ S.X₃ a.τ₃ inferInstance h₃ (n + 1)).hom ≫
        hFS.δ (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by dsimp; omega) := by
  letI := D.commShift
  letI : (QMinus C).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  have hn₁ := augmentationModelIso_normalization F D T.X₁ S.X₁ a.τ₁ inferInstance h₁
    (Triangle.π₁.mapIso e) he₁
  have hn₃ := augmentationModelIso_normalization F D T.X₃ S.X₃ a.τ₃ inferInstance h₃
    (Triangle.π₃.mapIso e) he₃
  change D.functor.map e.inv.hom₁ ≫ D.counit.app (cochainModel S.X₁) = _ at hn₁
  change D.functor.map e.inv.hom₃ ≫ D.counit.app (cochainModel S.X₃) = _ at hn₃
  have hr := replacementTriangleIso_boundary F D (cochainModelTriangle S σ)
    (minusTriangle C hT) e h₁ h₂ h₃ (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)
  rw [replacementTriangleIso_hom₁, replacementTriangleIso_hom₃] at hr
  erw [hn₁, hn₃] at hr
  have hr' := congrArg (fun f => f ≫ (modelHomologyIso F S.X₁ (-(n : ℤ))).hom) hr
  rw [Category.assoc, modelSplitBoundary_adjacent F S σ hFS
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)] at hr'
  dsimp only [cochainComputationIso, Iso.trans_hom, Functor.mapIso_hom]
  dsimp only [leftBoundary]
  rw [derivedHomologyBoundary_comp D.functor DerivedCategory.Minus.ι]
  simpa only [Category.assoc] using hr'.symm

include h₂ σ in
lemma cochainComputationIso_boundary (hS : S.ShortExact)
    (hFS : (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact) (n : ℕ) :
    leftBoundary F D hT n ≫
        (cochainComputationIso F D T.X₁ S.X₁ a.τ₁ inferInstance h₁ n).hom =
      (cochainComputationIso F D T.X₃ S.X₃ a.τ₃ inferInstance h₃ (n + 1)).hom ≫
        hFS.δ (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by dsimp; omega) := by
  exact cochainComputationIso_boundary_of_triangleIso F D S σ hT a h₁ h₂ h₃
    (boundedAugmentationTriangleIso S σ hT hS a)
    (boundedAugmentationTriangleIso_hom₁ S σ hT hS a)
    (boundedAugmentationTriangleIso_hom₃ S σ hT hS a) hFS n


end CochainResolutionBoundary

open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions

section MapExtensionBoundary
variable {C : Type*} {D : Type*} [Category* C] [Category* D]
  [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {ι ι' : Type*} {c : ComplexShape ι}
  {c' : ComplexShape ι'} (S : ShortComplex (HomologicalComplex C c)) (e : c.Embedding c')

def mapExtendShortComplexIso :
    (S.map (e.extendFunctor C)).map (F.mapHomologicalComplex c') ≅
      (S.map (F.mapHomologicalComplex c)).map (e.extendFunctor D) :=
  ShortComplex.isoMk (mapExtendIso F S.X₁ e) (mapExtendIso F S.X₂ e)
    (mapExtendIso F S.X₃ e)
    (mapExtendIso_naturality F e S.f).symm
    (mapExtendIso_naturality F e S.g).symm

section Abelian
variable (hF : ((S.map (e.extendFunctor C)).map (F.mapHomologicalComplex c')).ShortExact)

include hF in
lemma mapExtend_shortExact :
    ((S.map (F.mapHomologicalComplex c)).map (e.extendFunctor D)).ShortExact :=
  ShortComplex.shortExact_of_iso (mapExtendShortComplexIso F S e) hF

@[reassoc] lemma mapExtend_boundary (n m : ι') (hnm : c'.Rel n m) :
    hF.δ n m hnm ≫ HomologicalComplex.homologyMap (mapExtendIso F S.X₁ e).hom m =
      HomologicalComplex.homologyMap (mapExtendIso F S.X₃ e).hom n ≫
        (mapExtend_shortExact F S e hF).δ n m hnm :=
  HomologicalComplex.HomologySequence.δ_naturality
    (mapExtendShortComplexIso F S e).hom hF (mapExtend_shortExact F S e hF) n m hnm
end Abelian
end MapExtensionBoundary


section TensorHorseshoeBoundary
variable {R : Type u} [Ring R]
  (S : ShortComplex (ModuleCat.{max u v} Rᵐᵒᵖ))
  (P : LeftResolution Rᵐᵒᵖ S.X₁) (Q : LeftResolution Rᵐᵒᵖ S.X₃)
  (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P Q)
  (M : ModuleCat.{w} R)

@[instance_reducible] def explicitHomologyModule {R₀ : Type*} [Ring R₀] {I : Type*} {d : ComplexShape I}
    (K : HomologicalComplex (ModuleCat R₀) d) (i : I) : Module R₀ (Homology K i) :=
  inferInstance

def tensorHorseshoeBoundary (n : ℕ) :
    ModuleCat.of ℤ (TorWith Q M (n+1)) ⟶ ModuleCat.of ℤ (TorWith P M n) :=
  (tensorResolutionHomologyIso Q M (n + 1)).inv ≫
    (horseshoeImage_shortExact S P Q H
      ((tensorFunctor M) : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ)).δ
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
      (by change -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ); omega) ≫
    (tensorResolutionHomologyIso P M n).hom

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] P103.Specs.Ch11.ExtTorDefinitions.tensorFunctor
attribute [local irreducible] P103.BalancedTensor.relations
attribute [local irreducible] P103.Specs.Ch11.ExtTorDefinitions.tensorMap

set_option maxHeartbeats 1200000 in
lemma tensorHorseshoeConnecting (n : ℕ)
    (δ : letI : Module ℤ (TorWith Q M (n+1)) :=
        explicitHomologyModule (tensorComplex Q.complex M) (n+1)
      letI : Module ℤ (TorWith P M n) :=
        explicitHomologyModule (tensorComplex P.complex M) n
      TorWith Q M (n+1) →ₗ[ℤ] TorWith P M n)
    (hδ : ∀ z : TorWith Q M (n+1), δ z = tensorHorseshoeBoundary S P Q H M n z) :
    P103.Specs.Ch10.HomologySequence.Connecting (R := ℤ) (c := .down ℕ)
      (A := tensorComplex P.complex M) (B := tensorComplex H.middle.complex M)
      (C := tensorComplex Q.complex M)
      (tensorFirstMap H.inclusion M) (tensorFirstMap H.projection M) (n + 1) n δ := by
  let F : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ := tensorFunctor M
  let C := horseshoeChain S P Q H
  let e := ComplexShape.embeddingDownNat
  let hF := horseshoeImage_shortExact S P Q H F
  let hE := mapExtend_shortExact F C e hF
  have h := extendedBoundaryConnecting (C.map (F.mapHomologicalComplex (.down ℕ)))
    e hE (n+1) n (by simp)
  have hn : (ComplexShape.up ℤ).Rel (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) := by
    change -((n+1 : ℕ) : ℤ) + 1 = -(n : ℤ)
    omega
  have hb := mapExtend_boundary F C e hF
    (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn
  let EQ := (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} ℤ) (.up ℤ)
      (-((n+1 : ℕ) : ℤ))).mapIso (mapExtendIso F Q.complex e)
  let EP := (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} ℤ) (.up ℤ)
      (-(n : ℤ))).mapIso (mapExtendIso F P.complex e)
  have hb' (x : ((tensorComplex Q.complex M).extend e).homology (-((n+1 : ℕ) : ℤ))) :
      EP.hom (hF.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn (EQ.inv x)) =
        hE.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn x := by
    have hv := congrArg (fun f :
        (((F.mapHomologicalComplex (.up ℤ)).obj (cochainResolution Q)).homology
          (-((n+1 : ℕ) : ℤ))) ⟶
        (((tensorComplex P.complex M).extend e).homology (-(n : ℤ))) =>
          f (EQ.inv x)) hb
    change EP.hom (hF.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn (EQ.inv x)) =
      hE.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn (EQ.hom (EQ.inv x)) at hv
    exact hv.trans (congrArg (fun z => hE.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn z)
      (CategoryTheory.Iso.inv_hom_id_apply EQ x))
  have heq (z : TorWith Q M (n+1)) :
      tensorHorseshoeBoundary S P Q H M n z =
      (extendedQuotientHomologyIso (tensorComplex P.complex M) n e (show e.f n = -(n : ℤ) from rfl)).hom
        (hE.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn
          ((extendedQuotientHomologyIso (tensorComplex Q.complex M) (n+1) e (show e.f (n+1) = -((n+1 : ℕ) : ℤ) from rfl)).inv z)) := by
    dsimp only [tensorHorseshoeBoundary, tensorResolutionHomologyIso,
      cochainResolution, extendedQuotientHomologyIso, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv]
    change (quotientHomologyIso (tensorComplex P.complex M) n).hom
      (((tensorComplex P.complex M).extendHomologyIso e (show e.f n = -(n : ℤ) from rfl)).hom
        (EP.hom (hF.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn
          (EQ.inv (((tensorComplex Q.complex M).extendHomologyIso e (show e.f (n+1) = -((n+1 : ℕ) : ℤ) from rfl)).inv
            ((quotientHomologyIso (tensorComplex Q.complex M) (n+1)).inv z)))))) = _
    rw [hb']
    rfl
  intro z b a hb ha
  calc
    δ (homologyClass _ _ z) =
        tensorHorseshoeBoundary S P Q H M n (homologyClass _ _ z) := hδ _
    _ = (extendedQuotientHomologyIso (tensorComplex P.complex M) n e (show e.f n = -(n : ℤ) from rfl)).hom
        (hE.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) hn
          ((extendedQuotientHomologyIso (tensorComplex Q.complex M) (n+1) e (show e.f (n+1) = -((n+1 : ℕ) : ℤ) from rfl)).inv
            (homologyClass _ _ z))) := heq _
    _ = homologyClass _ _ a := h z b a hb ha
end TensorHorseshoeBoundary


section TensorHorseshoeBoundary
variable {R : Type u} [Ring R]
  (S : ShortComplex (ModuleCat.{max u v} Rᵐᵒᵖ)) (hS : S.ShortExact)
  (P : LeftResolution Rᵐᵒᵖ S.X₁) (Q : LeftResolution Rᵐᵒᵖ S.X₃)
  (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P Q)
  (M : ModuleCat.{w} R)
  [HasDerivedCategory.{x} (ModuleCat.{max u v} Rᵐᵒᵖ)]
  [HasDerivedCategory.{y} (ModuleCat.{max u v w} ℤ)]
  [(minus (ModuleCat.{max u v} Rᵐᵒᵖ)).IsTriangulated]
  [(minus (ModuleCat.{max u v w} ℤ)).IsTriangulated]
  (D : ExactLeftData (tensorFunctor M : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ))
  (hP : P.IsProjective) (hQ : Q.IsProjective)

theorem derivedTensorIso_boundary (n : ℕ) :
    leftBoundary (tensorFunctor M) D hS n ≫ (derivedTensorIso P M D hP n).hom =
      (derivedTensorIso Q M D hQ (n + 1)).hom ≫
        ((tensorResolutionHomologyIso Q M (n + 1)).inv ≫
          (horseshoeImage_shortExact S P Q H
            (tensorFunctor M : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ)).δ
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by change -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ); omega) ≫
          (tensorResolutionHomologyIso P M n).hom) := by
  let F : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ := tensorFunctor M
  let C := horseshoeCochain S P Q H
  let a := horseshoeAugmentation S P Q H
  letI : C.X₁.IsStrictlyLE 0 := by
    change (cochainResolution P).IsStrictlyLE 0
    infer_instance
  letI : C.X₂.IsStrictlyLE 0 := by
    change (cochainResolution H.middle).IsStrictlyLE 0
    infer_instance
  letI : C.X₃.IsStrictlyLE 0 := by
    change (cochainResolution Q).IsStrictlyLE 0
    infer_instance
  letI : QuasiIso a.τ₁ := cochainAugmentation_quasiIso P
  letI : QuasiIso a.τ₂ := cochainAugmentation_quasiIso H.middle
  letI : QuasiIso a.τ₃ := cochainAugmentation_quasiIso Q
  have hb := cochainComputationIso_boundary F D C (horseshoeCochainSplitting S P Q H)
    hS a (cochainResolution_projective P hP)
    (cochainResolution_projective H.middle H.projective) (cochainResolution_projective Q hQ)
    (horseshoeCochain_shortExact S P Q H) (horseshoeImage_shortExact S P Q H F) n
  dsimp only [derivedTensorIso, Iso.trans_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ (tensorResolutionHomologyIso P M n).hom) hb

end TensorHorseshoeBoundary

section DerivedTensorConnecting
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [Ring R]
  (S : ShortComplex (ModuleCat.{max u v} Rᵐᵒᵖ)) (hS : S.ShortExact)
  (P : LeftResolution Rᵐᵒᵖ S.X₁) (Q : LeftResolution Rᵐᵒᵖ S.X₃)
  (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P Q)
  (M : ModuleCat.{w} R)
  [HasDerivedCategory.{x} (ModuleCat.{max u v} Rᵐᵒᵖ)]
  [HasDerivedCategory.{y} (ModuleCat.{max u v w} ℤ)]
  [(minus (ModuleCat.{max u v} Rᵐᵒᵖ)).IsTriangulated]
  [(minus (ModuleCat.{max u v w} ℤ)).IsTriangulated]
  (D : ExactLeftData (tensorFunctor M : ModuleCat.{max u v} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w} ℤ))
  (hP : P.IsProjective) (hQ : Q.IsProjective)

theorem derivedTensorIso_connecting (n : ℕ) :
    P103.Specs.Ch10.HomologySequence.Connecting
      (tensorFirstMap H.inclusion M) (tensorFirstMap H.projection M) (n + 1) n
      ((derivedTensorIso P M D hP n).hom.hom.comp
        ((leftBoundary (tensorFunctor M) D hS n).hom.comp
          (derivedTensorIso Q M D hQ (n + 1)).inv.hom)) := by
  apply tensorHorseshoeConnecting.{u,v,w} S P Q H M n
  intro z
  have hb := derivedTensorIso_boundary.{u,v,w,x,y} S hS P Q H M D hP hQ n
  have hv := ConcreteCategory.congr_hom hb ((derivedTensorIso Q M D hQ (n + 1)).inv z)
  simpa only [tensorHorseshoeBoundary, CategoryTheory.comp_apply, ConcreteCategory.comp_apply,
    LinearMap.comp_apply, ModuleCat.comp_apply,
    CategoryTheory.Iso.inv_hom_id_apply] using hv

end DerivedTensorConnecting

section Counit
open CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u₁ v₁ u₂ v₂ w₁ w₂

variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Abelian C]
  [Category.{v₂} E] [Abelian E]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} E]
  [(minus C).IsTriangulated] [(minus E).IsTriangulated]
  (F : C ⥤ E) [F.Additive] (D : ExactLeftData.{u₁,v₁,u₂,v₂,w₁,w₂} F)
  (X : C) (K : CochainComplex C ℤ) [K.IsStrictlyLE 0]
  (p : K ⟶ (CochainComplex.singleFunctor C 0).obj X) (hp : QuasiIso p)
  (hK : ∀ i : ℤ, Projective (K.X i))

private def mappedCochainAugmentation :
    (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (CochainComplex.singleFunctor E 0).obj (F.obj X) :=
  (F.mapHomologicalComplex (.up ℤ)).map p ≫ (F.mapCochainComplexSingleFunctor 0).hom.app X

omit [(minus E).IsTriangulated] in
private lemma quotientCompQhIso_inv_eq_hom (L : CochainComplex E ℤ) :
    (DerivedCategory.quotientCompQhIso E).inv.app L =
      (DerivedCategory.quotientCompQhIso E).hom.app L := by
  rfl

omit [(minus E).IsTriangulated] in
private lemma singleStalkHomology (Y : E) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso E 0).hom.app Y =
      (DerivedCategory.homologyFunctorFactors E 0).hom.app
        ((CochainComplex.singleFunctor E 0).obj Y) ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 Y).hom := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso]

private lemma cochainComputationIso_counit :
    let L := (CochainComplex.singleFunctor C 0).obj X
    let S := cochainModel L
    let FL := (F.mapHomologicalComplex (.up ℤ)).obj L
    let sourceStalk : (minusSingle C).obj X ≅ (QMinus C).obj S :=
      DerivedCategory.Minus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQh C 0).app X)
    let tensorStalk : ((minusUValue F).obj S).obj ≅
        (DerivedCategory.singleFunctor E 0).obj (F.obj X) :=
      DerivedCategory.Qh.mapIso
        ((F.mapHomotopyCategory (.up ℤ)).mapIso
          ((HomotopyCategory.singleFunctorPostcompQuotientIso C 0).app X) ≪≫
          (F.mapHomotopyCategoryFactors (.up ℤ)).app L) ≪≫
      (DerivedCategory.quotientCompQhIso E).symm.app FL ≪≫
      DerivedCategory.Q.mapIso ((F.mapCochainComplexSingleFunctor 0).app X)
    (DerivedCategory.homologyFunctor E 0).map
      (DerivedCategory.Minus.ι.map (D.functor.map sourceStalk.hom ≫ D.counit.app S) ≫
        tensorStalk.hom) ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso E 0).hom.app (F.obj X)
      =
    (cochainComputationIso F D X K p hp hK 0).hom ≫
      HomologicalComplex.homologyMap (mappedCochainAugmentation F X K p) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj X)).hom := by
  intro L S FL sourceStalk tensorStalk
  have hSrc : sourceStalk.hom = ((minusSingleIso (C := C)).app X).hom := by
    apply DerivedCategory.Minus.ι.map_injective
    change DerivedCategory.Minus.ι.map (DerivedCategory.Minus.ι.preimage
      (X := (minusSingle C).obj X) (Y := (QMinus C).obj S)
      ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X)) = _
    rw [Functor.map_preimage]
    exact (congr_app (((FullyFaithful.ofFullyFaithful
          (DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ DerivedCategory C)).whiskeringRight C).map_preimage
        (X := minusSingle C)
        (Y := minusSingleHomotopy C ⋙ QMinus C)
        (DerivedCategory.singleFunctorIsoCompQh C 0).hom) X).symm
  have hStalk : tensorStalk.hom =
      (DerivedCategory.quotientCompQhIso E).hom.app FL ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
    have hSingle : (HomotopyCategory.singleFunctorPostcompQuotientIso C 0).hom.app X = 𝟙 _ := by
      rfl
    dsimp only [tensorStalk, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
    simp only [CategoryTheory.Functor.map_comp, hSingle,
      Functor.mapHomotopyCategoryFactors_hom_app, quotientCompQhIso_inv_eq_hom]
    have hF := (F.mapHomotopyCategory (.up ℤ)).map_id
      ((HomotopyCategory.singleFunctor C 0).obj X)
    have hQ := (DerivedCategory.Qh (C := E)).map_id
      ((HomotopyCategory.quotient E (.up ℤ)).obj FL)
    erw [hF, hQ]
    erw [Category.id_comp]
    erw [Category.id_comp]
  have hpD :
      (stalkModelIso F D X K p hp hK).hom ≫ (minusUValue F).map (cochainModelMap p) =
        D.functor.map sourceStalk.hom ≫ D.counit.app S := by
    dsimp only [stalkModelIso, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, modelIso_counit, hSrc]
    rfl
  have hHom := modelHomologyIso_naturality F (K := K) (L := L) p 0
  have hChain : (modelHomologyIso F L 0).hom ≫
        HomologicalComplex.homologyMap ((F.mapCochainComplexSingleFunctor 0).hom.app X) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj X)).hom =
      (DerivedCategory.homologyFunctor E 0).map tensorStalk.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso E 0).hom.app (F.obj X) := by
    rw [hStalk, CategoryTheory.Functor.map_comp, singleStalkHomology, modelHomologyIso_eq_quotient]
    have hn := (DerivedCategory.homologyFunctorFactors E 0).hom.naturality_assoc
      ((F.mapCochainComplexSingleFunctor 0).hom.app X)
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj X)).hom
    simp only [Category.assoc]
    exact congrArg (_ ≫ ·) hn.symm
  rw [← hpD]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← hChain, ← Category.assoc _ (modelHomologyIso F L 0).hom, hHom]
  change _ = ((DerivedCategory.homologyFunctor E 0).map
      (DerivedCategory.Minus.ι.map (stalkModelIso F D X K p hp hK).hom) ≫
      (modelHomologyIso F K 0).hom) ≫
      HomologicalComplex.homologyMap (mappedCochainAugmentation F X K p) 0 ≫ _
  rw [mappedCochainAugmentation, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]

end Counit

section TensorCounit

open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open P103.Specs.Ch10.Comparison

variable {R : Type u} [Ring R]
  [HasDerivedCategory.{x} (RightModules.{u,v} R)]
  [HasDerivedCategory.{y} (Groups.{u,v,w})]
  [(minus (RightModules.{u,v} R)).IsTriangulated]
  [(minus (Groups.{u,v,w})).IsTriangulated]
  (M : Coefficients.{u,w} R) (D : ExactLeftData (tensor.{u,v,w} R M))
  {A : RightModules.{u,v} R} (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)

/-- The same projective-model comparison that computes the higher values
identifies the ordinary augmentation in degree zero with the derived counit. -/
lemma derivedTensorIso_zero_counit :
    (derivedTensorIso P M D hP 0).hom ≫ (torZeroIso M P).hom =
      counitOnTensorStalk R M D A := by
  let F := tensor.{u,v,w} R M
  let K := cochainResolution P
  let p := cochainAugmentation P
  let hp := cochainAugmentation_quasiIso P
  let hK := cochainResolution_projective P hP
  let eC := cochainComputationIso F D A K p hp hK 0
  let eT := tensorResolutionHomologyIso.{u,v,w} P M 0
  let q := HomologicalComplex.homologyMap (mappedCochainAugmentation F A K p) 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj A)).hom
  have hc : counitOnTensorStalk R M D A = eC.hom ≫ q :=
    cochainComputationIso_counit.{max ((max u v) + 1) u,max u v,(max u v w) + 1,max u v w,x,y} F D A K p hp hK
  have ht : q = eT.hom ≫ (torZeroIso M P).hom :=
    tensorResolutionHomologyIso_zero.{u,v,w} P M
  change (eC.hom ≫ eT.hom) ≫ (torZeroIso M P).hom = _
  exact (Category.assoc ..).trans
    ((congrArg (fun f => eC.hom ≫ f) ht.symm).trans hc.symm)

end TensorCounit

/-- Every ordinary projective right resolution computes the derived tensor values. -/
theorem values :
    Specs.AdvancedHomologicalAlgebra.DerivedTorComparison.ValuesType.{u,v,w,x,y} := by
  intro R _ _ _ hA hB M D A P hP n
  exact derivedValue_iso P M D hP n

/-- The coherent HA-R14 comparison, including both naturalities, degree zero,
balance, and the classical connecting maps after reversal of indices. -/
theorem comparison :
    Specs.AdvancedHomologicalAlgebra.DerivedTorComparison.FullType.{u,v,w,x,y} := by
  intro R _ _ _ hA hB T D
  let e : ∀ (M : Specs.AdvancedHomologicalAlgebra.DerivedTorComparison.Coefficients.{u,w} R)
      (A : Specs.AdvancedHomologicalAlgebra.DerivedTorComparison.RightModules.{u,v} R)
      (P : P103.Specs.Ch10.Comparison.ProjectiveChoice Rᵐᵒᵖ A) (n : ℕ),
      (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.leftValue
        (Specs.AdvancedHomologicalAlgebra.DerivedTorComparison.tensor R M) (D M) n).obj A ≅
      ModuleCat.of ℤ (P103.Specs.Ch11.ExtTorDefinitions.TorWith P.val M n) :=
    fun M A P n => derivedTensorIso P.val M (D M) P.property n
  have hn : ∀ M n {A B} P Q (f : A ⟶ B),
      (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.leftValue
        (Specs.AdvancedHomologicalAlgebra.DerivedTorComparison.tensor R M) (D M) n).map f ≫
        (e M B Q n).hom = (e M A P n).hom ≫
          ModuleCat.ofHom ((T.torMaps n).map P Q f (𝟙 M)) :=
    fun M n _ _ P Q f => derivedTensorIso_right_naturality M (D M) n (T.torMaps n) P Q f
  refine ⟨{
    iso := e
    right_naturality := hn
    coefficient_naturality := ?_
    zero := fun M => zeroIso T M _ (fun A P => e M A P 0) (hn M 0)
    zero_counit := ?_
    zero_formula := ?_
    balance := comparison_balance D e
    connecting := ?_ }⟩
  · intro M N g α hα A P n
    change _ ≫ (derivedTensorIso P.val N (D N) P.property n).hom =
      (derivedTensorIso P.val M (D M) P.property n).hom ≫ _
    exact derivedTensorIso_coefficient_naturality.{u,v,w,x,y} (R := R) (M := M) (N := N) g (D M) (D N) α hα n (T.torMaps n) P
  · intro M A
    dsimp only [zeroIso, NatIso.ofComponents_hom_app, Iso.trans_hom, e]
    exact derivedTensorIso_zero_counit.{u,v,w,x,y} (A := A) M (D M)
      (T.rightResolutions A).val (T.rightResolutions A).property
  · intro M A P z
    exact zeroIso_formula T M _ (fun A P => e M A P 0) (hn M 0) A P z
  · intro M S hS P Q
    refine ⟨horseshoe_exists S hS P Q, ?_⟩
    intro H n
    dsimp only [e]
    exact derivedTensorIso_connecting.{u,v,w,x,y} S hS P.val Q.val H M (D M)
      P.property Q.property n

section Uniqueness
open CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions

variable {R : Type u} [Ring R]
  [HasDerivedCategory.{x} (RightModules.{u,v} R)]
  [HasDerivedCategory.{y} (Groups.{u,v,w})]
  [hA : (minus (RightModules.{u,v} R)).IsTriangulated]
  [hB : (minus (Groups.{u,v,w})).IsTriangulated]

variable (D : DerivedFamily.{u,v,w,x,y} R) (M : Coefficients.{u,w} R)

lemma mono_leftBoundary_of_projective
    {S : ShortComplex (RightModules.{u,v} R)} (hS : S.ShortExact)
    [Projective S.X₂] (n : ℕ) :
    Mono (leftBoundary (tensor.{u,v,w} R M) (D M) hS n) := by
  let E := D M
  letI := E.commShift
  letI : E.functor.IsTriangulated := E.triangulated
  let F := E.functor ⋙ DerivedCategory.Minus.ι
  let E₀ := DerivedCategory.homologyFunctor (Groups.{u,v,w}) 0
  let L := F.mapTriangle.obj (minusTriangle _ hS)
  have hL : L ∈ distTriang _ :=
    F.map_distinguished _ (ClassicalDerivedValues.minusTriangle_distinguished hS)
  let k : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
  have hz : IsZero ((leftValue (tensor.{u,v,w} R M) E (n + 1)).obj S.X₂) :=
    ClassicalDerivedValues.leftProjectiveVanishing _ _ hA hB (tensor.{u,v,w} R M) E S.X₂ n
  exact (E₀.homologySequence_exact₃ L hL _ _ k).mono_g (hz.eq_of_src _ _)

variable {T : CanonicalTheory.{u,max u v,w} R}
    (c₁ c₂ : Comparison.{u,v,w,x,y} R T D)

lemma comparisonIso_zero_unique
    (A : RightModules.{u,v} R) (P : ProjectiveChoice Rᵐᵒᵖ A) :
    c₁.iso M A P 0 = c₂.iso M A P 0 := by
  have hzer : (c₁.zero M).hom.app A = (c₂.zero M).hom.app A :=
    (c₁.zero_counit M A).trans (c₂.zero_counit M A).symm
  have hcomp : (c₁.iso M A P 0).inv ≫ (c₁.zero M).hom.app A =
      (c₂.iso M A P 0).inv ≫ (c₂.zero M).hom.app A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := (cycleBoundaries (tensorComplex P.val.complex M) 0).mkQ_surjective z
    exact (c₁.zero_formula M A P z).trans (c₂.zero_formula M A P z).symm
  rw [hzer, cancel_mono] at hcomp
  exact congrArg Iso.symm ((Iso.ext hcomp) :
    (c₁.iso M A P 0).symm = (c₂.iso M A P 0).symm)


variable (S : ShortComplex (RightModules.{u,v} R)) (hS : S.ShortExact)
    [Projective S.X₂]
    (P : ProjectiveChoice Rᵐᵒᵖ S.X₁) (Q : ProjectiveChoice Rᵐᵒᵖ S.X₃)
    (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P.val Q.val)

include hS H in
open P103.Specs.Ch10.HomologySequence in
lemma comparisonIso_succ_unique (n : ℕ)
    (hn : c₁.iso M S.X₁ P n = c₂.iso M S.X₁ P n) :
    c₁.iso M S.X₃ Q (n + 1) = c₂.iso M S.X₃ Q (n + 1) := by
  let B := leftBoundary (tensor.{u,v,w} R M) (D M) hS n
  let δ (e : Comparison.{u,v,w,x,y} R T D) :
      ModuleCat.of ℤ (TorWith Q.val M (n + 1)) ⟶ ModuleCat.of ℤ (TorWith P.val M n) :=
    (e.iso M S.X₃ Q (n + 1)).inv ≫ B ≫ (e.iso M S.X₁ P n).hom
  have hδ (e : Comparison.{u,v,w,x,y} R T D) :
      Connecting (tensorFirstMap H.inclusion M) (tensorFirstMap H.projection M) (n + 1) n (δ e).hom :=
    (e.connecting M S hS P Q).2 H n
  have hExact := P103.Ch11.TorExactSequences.first_degreewise_exact H M
  have hd : δ c₂ = δ c₁ := by
    apply ModuleCat.hom_ext
    exact P103.Ch10.HomologySequence.connecting_unique _ _ hExact rfl
      (δ c₁).hom (hδ c₁) (δ c₂).hom (hδ c₂)
  haveI : Mono B := mono_leftBoundary_of_projective.{u,v,w,x,y} D M hS n
  haveI : Mono (δ c₁) := by dsimp only [δ]; infer_instance
  apply Iso.ext
  rw [← cancel_mono (δ c₁)]
  have hc (e : Comparison.{u,v,w,x,y} R T D) :
      (e.iso M S.X₃ Q (n+1)).hom ≫ δ e = B ≫ (e.iso M S.X₁ P n).hom := by
    dsimp only [δ]
    simp
  rw [hc, ← hd, hc, hn]

end Uniqueness

section ComparisonIsos
open CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} [Ring R]
  [HasDerivedCategory.{x} (RightModules.{u,v} R)]
  [HasDerivedCategory.{y} (Groups.{u,v,w})]
  [(minus (RightModules.{u,v} R)).IsTriangulated]
  [(minus (Groups.{u,v,w})).IsTriangulated]
  {T : CanonicalTheory.{u,max u v,w} R}
  {D : DerivedFamily.{u,v,w,x,y} R}

/-- The degree-zero counit and classical connecting equations determine
the comparison in all degrees by effacement using projective presentations. -/
theorem comparisonIso_unique (c₁ c₂ : Comparison.{u,v,w,x,y} R T D)
    (M : Coefficients.{u,w} R) (A : RightModules.{u,v} R)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (n : ℕ) :
    c₁.iso M A P n = c₂.iso M A P n := by
  induction n generalizing A with
  | zero => exact comparisonIso_zero_unique D M c₁ c₂ A P
  | succ n hn =>
    let S := ShortComplex.kernelSequence (Projective.π A)
    have hS : S.ShortExact :=
      { exact := ShortComplex.kernelSequence_exact _
        mono_f := inferInstance
        epi_g := inferInstanceAs (Epi (Projective.π A)) }
    haveI : Projective S.X₂ := inferInstanceAs (Projective (Projective.over A))
    let Q := T.rightResolutions S.X₁
    obtain ⟨H⟩ := (c₁.connecting M S hS Q P).1
    exact comparisonIso_succ_unique.{u,v,w,x,y} D M c₁ c₂ S hS Q P H n (hn S.X₁ Q)

end ComparisonIsos

end AdvancedHomologicalAlgebra.DerivedTorComparison
