import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveComplexReplacement
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! HA-R08. Acyclic terms compute the total derived functor.
Finite complexes are handled by degreewise split brutal truncation triangles;
the general one-sided bounded case follows degree by degree using same-bound
replacements. Exactness of F is needed only for the vanishing criteria. -/
noncomputable section
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

open scoped ZeroObject

namespace AdvancedHomologicalAlgebra.AcyclicTermComparison

section Stalks
variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable def plusStalk : plusStalkType (A := A) := plusStalkValue
noncomputable def minusStalk : minusStalkType (A := A) := minusStalkValue
end Stalks

section NaturalComparisons
variable {C D : Type*} [Category C] [Category D]
  {G H : C ⥤ D} (τ : G ⟶ H)

lemma comparison_iso_of_iso {X Y : C} (e : X ≅ Y) [IsIso (τ.app X)] :
    IsIso (τ.app Y) := by
  have h : τ.app Y = inv (G.map e.hom) ≫ τ.app X ≫ H.map e.hom := by
    rw [← τ.naturality, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

variable [HasShift C ℤ] [HasShift D ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
  [NatTrans.CommShift τ ℤ]

lemma comparison_iso_shift (X : C) (n : ℤ) [IsIso (τ.app X)] :
    IsIso (τ.app (X⟦n⟧)) := by
  rw [τ.app_shift]
  infer_instance

variable [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [G.IsTriangulated] [H.IsTriangulated]

lemma comparison_iso_extension (T : Triangle C) (hT : T ∈ distTriang C)
    [IsIso (τ.app T.obj₁)] [IsIso (τ.app T.obj₃)] : IsIso (τ.app T.obj₂) := by
  let f : G.mapTriangle.obj T ⟶ H.mapTriangle.obj T :=
    { hom₁ := τ.app T.obj₁
      hom₂ := τ.app T.obj₂
      hom₃ := τ.app T.obj₃
      comm₁ := τ.naturality _
      comm₂ := τ.naturality _
      comm₃ := by
        dsimp
        simp only [Category.assoc, τ.shift_app_comm, τ.naturality_assoc] }
  exact Pretriangulated.isIso₂_of_isIso₁₃ f
    (G.map_distinguished T hT) (H.map_distinguished T hT) inferInstance inferInstance
end NaturalComparisons

/-! The following cuts retain the original terms. In particular they introduce
no kernels or cokernels whose acyclicity would require an extra hypothesis. -/
section BrutalCuts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (K : CochainComplex A ℤ) (P : ℤ → Prop) [DecidablePred P]

private def cutX (i : ℤ) : A := if P i then K.X i else 0
private def cutIn (i : ℤ) : cutX K P i ⟶ K.X i := by
  unfold cutX
  split_ifs
  · exact 𝟙 _
  · exact 0
private def cutOut (i : ℤ) : K.X i ⟶ cutX K P i := by
  unfold cutX
  split_ifs
  · exact 𝟙 _
  · exact 0

private lemma cutIn_cutOut (i : ℤ) : cutIn K P i ≫ cutOut K P i = 𝟙 _ := by
  by_cases h : P i
  · simp [cutIn, cutOut, cutX, h]
  · have hz : IsZero (cutX K P i) := by
      simpa only [cutX, ite_eq_right h] using (isZero_zero A)
    exact hz.eq_of_src _ _
private lemma cutOut_cutIn (i : ℤ) :
    cutOut K P i ≫ cutIn K P i = if P i then 𝟙 (K.X i) else 0 := by
  by_cases h : P i <;> simp [cutIn, cutOut, cutX, h]

/-- Retain exactly the terms satisfying P, with all other terms zero. -/
def brutalCut : CochainComplex A ℤ where
  X := cutX K P
  d i j := cutIn K P i ≫ K.d i j ≫ cutOut K P j
  shape i j h := by simp [K.shape i j h]
  d_comp_d' i j k _ _ := by
    simp only [Category.assoc]
    rw [← Category.assoc (cutOut K P j), cutOut_cutIn]
    by_cases h : P j
    · simp only [ite_eq_left h, Category.id_comp]
      rw [← Category.assoc (K.d i j), K.d_comp_d]
      simp
    · simp [h]

/-- Inclusion of an upper cut. -/
def brutalCutIncl (a : ℤ) : brutalCut K (fun i => a ≤ i) ⟶ K where
  f i := cutIn K (fun i => a ≤ i) i
  comm' i j hij := by
    dsimp [brutalCut]
    rw [Category.assoc, Category.assoc, cutOut_cutIn]
    by_cases h : a ≤ j
    · simp [h]
    · have hi : ¬ a ≤ i := by simpa using (show ¬ a ≤ i by
        have : i + 1 = j := hij
        omega)
      have hz : cutIn K (fun i => a ≤ i) i = 0 := by simp [cutIn, hi]
      simp [h, hz]

/-- Projection onto the complementary lower cut. -/
def brutalCutProj (a : ℤ) : K ⟶ brutalCut K (fun i => i < a) where
  f i := cutOut K (fun i => i < a) i
  comm' i j hij := by
    dsimp [brutalCut]
    rw [← Category.assoc, cutOut_cutIn]
    by_cases h : i < a
    · simp [h]
    · have hj : ¬ j < a := by
        have : i + 1 = j := hij
        omega
      have hz : cutOut K (fun i => i < a) j = 0 := by simp [cutOut, hj]
      simp [h, hz]

/-- The brutal truncation short complex, split in each degree. -/
def brutalCutSequence (a : ℤ) : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (brutalCutIncl K a) (brutalCutProj K a) (by
    ext i
    dsimp [brutalCutIncl, brutalCutProj]
    by_cases h : a ≤ i
    · simp [cutIn, cutOut, h, show ¬ i < a by omega]
    · simp [cutIn, cutOut, h])

def brutalCutSplitting (a i : ℤ) :
    ((brutalCutSequence K a).map (HomologicalComplex.eval A (.up ℤ) i)).Splitting where
  r := cutOut K (fun i => a ≤ i) i
  s := cutIn K (fun i => i < a) i
  f_r := cutIn_cutOut K _ i
  s_g := cutIn_cutOut K _ i
  id := by
    dsimp [brutalCutSequence, brutalCutIncl, brutalCutProj]
    rw [cutOut_cutIn, cutOut_cutIn]
    by_cases h : a ≤ i <;> simp [h, show (i < a) ↔ ¬ a ≤ i by omega]

lemma brutalCut_isZero_X (i : ℤ) (hi : ¬ P i) : IsZero ((brutalCut K P).X i) := by
  change IsZero (cutX K P i)
  simpa only [cutX, ite_eq_right hi] using (isZero_zero A)

/-- A retained term is the original term, by a canonical isomorphism. -/
def brutalCutXIso (i : ℤ) (hi : P i) : (brutalCut K P).X i ≅ K.X i where
  hom := cutIn K P i
  inv := cutOut K P i
  hom_inv_id := cutIn_cutOut K P i
  inv_hom_id := by rw [cutOut_cutIn, ite_eq_left hi]

instance brutalCut_inheritsGE (a : ℤ) [K.IsStrictlyGE a] :
    (brutalCut K P).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  by_cases h : P i
  · exact (K.isZero_of_isStrictlyGE a i hi).of_iso (brutalCutXIso K P i h)
  · exact brutalCut_isZero_X K P i h

instance brutalCut_inheritsLE (b : ℤ) [K.IsStrictlyLE b] :
    (brutalCut K P).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases h : P i
  · exact (K.isZero_of_isStrictlyLE b i hi).of_iso (brutalCutXIso K P i h)
  · exact brutalCut_isZero_X K P i h

instance brutalCut_upperGE (a : ℤ) :
    (brutalCut K (fun i => a ≤ i)).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact brutalCut_isZero_X K _ i (by omega)

instance brutalCut_lowerLE (a : ℤ) :
    (brutalCut K (fun i => i < a)).IsStrictlyLE (a - 1) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact brutalCut_isZero_X K _ i (by omega)

end BrutalCuts

section TriangleRestriction
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated]

/-- Restrict a triangle whose three vertices belong to a full subcategory. -/
def restrictTriangle (T : Triangle C) (h₁ : P T.obj₁) (h₂ : P T.obj₂) (h₃ : P T.obj₃) :
    Triangle P.FullSubcategory :=
  Triangle.mk (P.homMk (X := ⟨T.obj₁, h₁⟩) (Y := ⟨T.obj₂, h₂⟩) T.mor₁)
    (P.homMk (X := ⟨T.obj₂, h₂⟩) (Y := ⟨T.obj₃, h₃⟩) T.mor₂)
    (P.homMk (T.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app ⟨T.obj₁, h₁⟩))

lemma restrictTriangle_distinguished (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) (h₃ : P T.obj₃) :
    restrictTriangle P T h₁ h₂ h₃ ∈ distTriang P.FullSubcategory := by
  change P.ι.mapTriangle.obj (restrictTriangle P T h₁ h₂ h₃) ∈ distTriang C
  apply isomorphic_distinguished _ hT
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [restrictTriangle]) (by simp [restrictTriangle]) (by simp [restrictTriangle])
end TriangleRestriction

section BoundaryHomology
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

/-- At the first term degree, preservation of kernels suffices to preserve
quasi-isomorphisms. It does not assert preservation of all quasi-isomorphisms. -/
lemma quasiIsoAt_map_of_strictlyGE (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (a : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE a] [QuasiIsoAt f a] :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map f) a := by
  let : F.PreservesLeftHomologyOf (K.sc a) := F.preservesLeftHomology_of_zero_f _ (by
    change K.d ((ComplexShape.up ℤ).prev a) a = 0
    rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (a - 1) a by simp)]
    exact (K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)
  let : F.PreservesLeftHomologyOf (L.sc a) := F.preservesLeftHomology_of_zero_f _ (by
    change L.d ((ComplexShape.up ℤ).prev a) a = 0
    rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (a - 1) a by simp)]
    exact (L.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)
  have : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor A (.up ℤ) a).map f) :=
    (quasiIsoAt_iff f a).mp inferInstance
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor A (.up ℤ) a).map f)

/-- The dual assertion uses preservation of cokernels at the last term degree. -/
lemma quasiIsoAt_map_of_strictlyLE (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] [QuasiIsoAt f b] :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map f) b := by
  let : F.PreservesRightHomologyOf (K.sc b) := F.preservesRightHomology_of_zero_g _ (by
    change K.d b ((ComplexShape.up ℤ).next b) = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel b (b + 1) by simp)]
    exact (K.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_of_tgt _ _)
  let : F.PreservesRightHomologyOf (L.sc b) := F.preservesRightHomology_of_zero_g _ (by
    change L.d b ((ComplexShape.up ℤ).next b) = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel b (b + 1) by simp)]
    exact (L.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_of_tgt _ _)
  have : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor A (.up ℤ) b).map f) :=
    (quasiIsoAt_iff f b).mp inferInstance
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_of_preservesRightHomology F
    ((HomologicalComplex.shortComplexFunctor A (.up ℤ) b).map f)
end BoundaryHomology

section Right
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]

noncomputable def rightAcyclic : rightAcyclicType (A := A) (B := B) := rightAcyclicValue
noncomputable def rightDerivedObject : rightDerivedObjectType (A := A) (B := B) :=
  rightDerivedObjectValue

/-- Every injective object is acyclic, without exactness of F. -/
lemma rightAcyclic_of_injective (F : A ⥤ B) [F.Additive] (X : A) [Injective X] :
    rightAcyclic F X := by
  apply TotalRightDerivedFunctor.modelComparison A B F (plusStalkValue X)
  intro n
  change Injective (((HomologicalComplex.single A (.up ℤ) 0).obj X).X n)
  infer_instance

/-- The right derived image preserves a specified lower term bound. This is
why the tail above i+1 has no effect on the comparison in degree i. -/
lemma rightDerived_isGE (F : A ⥤ B) [F.Additive]
    (C : CochainComplex.Plus A) (a : ℤ) [C.obj.IsStrictlyGE a] :
    (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj C)).IsGE a := by
  obtain ⟨I, f, _, hf, hI, hIa⟩ :=
    InjectiveComplexReplacement.replacement A C.obj a inferInstance
  let I' : CochainComplex.Plus A := ⟨I, a, hIa⟩
  let f' : C ⟶ I' := (CochainComplex.plus A).homMk f
  obtain ⟨e, _⟩ := TotalRightDerivedFunctor.computesReplacement A B F C I' f' hf hI
  have := hIa
  have h : (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I')).IsGE a := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I)).IsGE a
    infer_instance
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso e.symm a

/-- The same bound assertion on the bounded homotopy category. -/
lemma rightDerived_isGE_homotopy (F : A ⥤ B) [F.Additive]
    (C : HomotopyCategory.Plus A) (a : ℤ) [hC : CochainComplex.IsStrictlyGE C.obj.as a] :
    (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj C)).IsGE a := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective C
  have : C.obj.IsStrictlyGE a := hC
  have := rightDerived_isGE F C a
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (F.rightDerivedFunctorPlus.mapIso ((DerivedCategory.Plus.quotientCompQhIso A).app C)).symm a

/-- Termwise application of any additive functor preserves upper term bounds. -/
lemma termwisePlus_isLE (F : A ⥤ B) [F.Additive]
    (C : HomotopyCategory.Plus A) (b : ℤ) [hC : CochainComplex.IsStrictlyLE C.obj.as b] :
    ((plusUValue F).obj C).IsLE b := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective C
  have : C.obj.IsStrictlyLE b := hC
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff]
  change (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj))).IsLE b
  have : (DerivedCategory.Q.obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj)).IsLE b := by infer_instance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C.obj)).symm b

/-- The necessary vanishing direction does not require left exactness. -/
lemma rightAcyclic_positive_vanishing (F : A ⥤ B) [F.Additive] (X : A)
    (hX : rightAcyclic F X) (n : ℕ) : IsZero (rightDerivedObject F (n + 1) X) := by
  let : IsIso (F.rightDerivedFunctorPlusUnith.app (plusStalkValue X)) := hX
  have : CochainComplex.IsStrictlyLE (plusStalkValue X).obj.as 0 := by
    change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyLE 0
    infer_instance
  have : ((plusUValue F).obj (plusStalkValue X)).IsLE 0 :=
    termwisePlus_isLE F (plusStalkValue X) 0
  exact (DerivedCategory.Plus.isZero_homology_of_isLE
    ((plusUValue F).obj (plusStalkValue X)) 0 ((n + 1 : ℕ) : ℤ) (by omega)).of_iso
      ((DerivedCategory.Plus.homologyFunctor B ((n + 1 : ℕ) : ℤ)).mapIso
        (asIso (F.rightDerivedFunctorPlusUnith.app (plusStalkValue X)))).symm

/-- The cochain comparison is invertible on the first possible cohomology
for a left exact F. -/
lemma rightComparison_lowest_degree (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (C : CochainComplex.Plus A) (a : ℤ) [C.obj.IsStrictlyGE a] :
    IsIso ((DerivedCategory.Plus.homologyFunctor B a).map
      (F.rightDerivedFunctorPlusUnit.app C)) := by
  obtain ⟨I, f, _, hf, hI, hIa⟩ :=
    InjectiveComplexReplacement.replacement A C.obj a inferInstance
  let I' : CochainComplex.Plus A := ⟨I, a, hIa⟩
  let f' : C ⟶ I' := (CochainComplex.plus A).homMk f
  obtain ⟨e, he⟩ := TotalRightDerivedFunctor.computesReplacement A B F C I' f' hf hI
  let := hf
  let := hIa
  have := quasiIsoAt_map_of_strictlyGE F f a
  have hmap : IsIso ((DerivedCategory.Plus.homologyFunctor B a).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f'))) := by
    change IsIso ((DerivedCategory.homologyFunctor B a).map
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f)))
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors B a)
      ((F.mapHomologicalComplex (.up ℤ)).map f)).mpr
      ((quasiIsoAt_iff_isIso_homologyMap _ a).mp inferInstance)
  have hcomp := congrArg ((DerivedCategory.Plus.homologyFunctor B a).map) he
  simp only [Functor.map_comp] at hcomp
  have : IsIso (((DerivedCategory.Plus.homologyFunctor B a).map
      (F.rightDerivedFunctorPlusUnit.app C)) ≫
      (DerivedCategory.Plus.homologyFunctor B a).map e.hom) := by
    rw [hcomp]
    exact hmap
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.homologyFunctor B a).map e.hom)

/-- The homotopy comparison has the same lowest-degree property; the cochain
and homotopy units differ by the canonical quotient isomorphisms. -/
lemma rightComparison_lowest_degree_homotopy (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (C : HomotopyCategory.Plus A) (a : ℤ)
    [hC : CochainComplex.IsStrictlyGE C.obj.as a] :
    IsIso ((DerivedCategory.Plus.homologyFunctor B a).map
      (F.rightDerivedFunctorPlusUnith.app C)) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective C
  have : C.obj.IsStrictlyGE a := hC
  have h := rightComparison_lowest_degree F C a
  simp only [Functor.rightDerivedFunctorPlusUnit_app, Functor.map_comp] at h
  have h := (isIso_comp_left_iff _ _).mp h
  have h := (isIso_comp_left_iff _ _).mp h
  exact (isIso_comp_right_iff _ _).mp h

/-- Invertibility of the stalk comparison is detected by its degree zero map
and positive target cohomology, even before imposing left exactness. -/
lemma rightAcyclic_iff_cohomology (F : A ⥤ B) [F.Additive] (X : A) :
    rightAcyclic F X ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
        (F.rightDerivedFunctorPlusUnith.app (plusStalkValue X))) ∧
      ∀ n : ℕ, IsZero (rightDerivedObject F (n + 1) X) := by
  constructor
  · intro h
    let : IsIso (F.rightDerivedFunctorPlusUnith.app (plusStalkValue X)) := h
    exact ⟨inferInstance, rightAcyclic_positive_vanishing F X h⟩
  · rintro ⟨h0, hpos⟩
    change IsIso (F.rightDerivedFunctorPlusUnith.app (plusStalkValue X))
    rw [DerivedCategory.Plus.isIso_iff]
    intro i
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · have : CochainComplex.IsStrictlyGE (plusStalkValue X).obj.as 0 := by
        change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyGE 0
        infer_instance
      have := rightDerived_isGE_homotopy F (plusStalkValue X) 0
      have htarget := DerivedCategory.Plus.isZero_homology_of_isGE
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj (plusStalkValue X))) 0 i hi
      have hsource : IsZero ((DerivedCategory.Plus.homologyFunctor B i).obj
          ((plusUValue F).obj (plusStalkValue X))) := by
        change IsZero ((DerivedCategory.homologyFunctor B i).obj
          ((minusUValue F).obj (minusStalkValue X)).obj)
        have hge : ((minusUValue F).obj (minusStalkValue X)).obj.IsGE 0 := by
          change (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj
              ((CochainComplex.singleFunctor A 0).obj X)))).IsGE 0
          have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
              ((CochainComplex.singleFunctor A 0).obj X))).IsGE 0 := by infer_instance
          exact DerivedCategory.TStructure.t.isGE_of_iso
            ((DerivedCategory.quotientCompQhIso B).app _).symm 0
        exact DerivedCategory.isZero_of_isGE _ 0 i hi
      exact hsource.isIso htarget _
    · exact h0
    · have : CochainComplex.IsStrictlyLE (plusStalkValue X).obj.as 0 := by
        change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyLE 0
        infer_instance
      have := termwisePlus_isLE F (plusStalkValue X) 0
      have hsource := DerivedCategory.Plus.isZero_homology_of_isLE
        ((plusUValue F).obj (plusStalkValue X)) 0 i hi
      have htarget : IsZero ((DerivedCategory.Plus.homologyFunctor B i).obj
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj (plusStalkValue X)))) := by
        have hn : ((i.toNat - 1 : ℕ) : ℤ) + 1 = i := by omega
        have h := hpos (i.toNat - 1)
        dsimp [rightDerivedObject, rightDerivedObjectValue] at h
        rwa [hn] at h
      exact hsource.isIso htarget _

/-- HA-R08: for a left exact functor, right acyclicity is exactly positive
right-derived vanishing. The degree zero comparison has just been proved. -/
theorem rightVanishing : rightVanishingType := by
  intro A B _ _ _ _ _ _ _ F _ _ X
  change rightAcyclic F X ↔ ∀ n : ℕ, IsZero (rightDerivedObject F (n + 1) X)
  rw [rightAcyclic_iff_cohomology]
  have : CochainComplex.IsStrictlyGE (plusStalkValue X).obj.as 0 := by
    change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyGE 0
    infer_instance
  exact and_iff_right (rightComparison_lowest_degree_homotopy F (plusStalkValue X) 0)

end Right

section Left
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated]

noncomputable def leftAcyclic : leftAcyclicType (A := A) (B := B) := leftAcyclicValue
noncomputable def leftDerivedObject : leftDerivedObjectType (A := A) (B := B) :=
  leftDerivedObjectValue

/-- Every projective object is acyclic for every choice of the left derived data. -/
lemma leftAcyclic_of_projective (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) (X : A) [Projective X] :
    leftAcyclic F R X := by
  apply R.model_iso (minusStalkValue X)
  intro n
  change Projective (((HomologicalComplex.single A (.up ℤ) 0).obj X).X n)
  infer_instance

/-- Termwise application also preserves lower term bounds on K⁻. -/
lemma termwiseMinus_isGE (F : A ⥤ B) [F.Additive]
    (C : KMinus A) (a : ℤ) [CochainComplex.IsStrictlyGE C.obj.as a] :
    ((minusUValue F).obj C).obj.IsGE a := by
  change (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as))).IsGE a
  have : (DerivedCategory.Q.obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as)).IsGE a := by infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as)).symm a

/-- The necessary left vanishing direction does not require right exactness. -/
lemma leftAcyclic_positive_vanishing (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) (X : A)
    (hX : leftAcyclic F R X) (n : ℕ) : IsZero (leftDerivedObject F R (n + 1) X) := by
  let : IsIso (R.counit.app (minusStalkValue X)) := hX
  have : CochainComplex.IsStrictlyGE (minusStalkValue X).obj.as 0 := by
    change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyGE 0
    infer_instance
  have : ((minusUValue F).obj (minusStalkValue X)).obj.IsGE 0 :=
    termwiseMinus_isGE F (minusStalkValue X) 0
  exact (DerivedCategory.isZero_of_isGE
    ((minusUValue F).obj (minusStalkValue X)).obj 0 (-((n + 1 : ℕ) : ℤ))
    (by omega)).of_iso
      ((DerivedCategory.homologyFunctor B (-((n + 1 : ℕ) : ℤ))).mapIso
        (DerivedCategory.Minus.ι.mapIso (asIso (R.counit.app (minusStalkValue X)))))

/-- The left derived image preserves the specified upper term bound. -/
lemma leftDerived_isLE [EnoughProjectives A] (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (C : KMinus A) (b : ℤ) [CochainComplex.IsStrictlyLE C.obj.as b] :
    (R.functor.obj ((QMinus A).obj C)).obj.IsLE b := by
  obtain ⟨P, p, hPb, hP, _, hp⟩ :=
    ProjectiveComplexReplacement.replacement A C.obj.as b inferInstance
  let P' : KMinus A := ⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, b, hPb⟩
  let p' : P' ⟶ C := (minus A).homMk ((HomotopyCategory.quotient A (.up ℤ)).map p)
  have hp' : WMinus A p' :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff p).mpr hp
  obtain ⟨e, _, _⟩ := TotalLeftDerivedFunctor.computation A B
    (inferInstance : (minus A).IsTriangulated) (inferInstance : (minus B).IsTriangulated)
    F R P' C p' hP hp'
  have := hPb
  have hBound : ((minusUValue F).obj P').obj.IsLE b := by
    change (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P))).IsLE b
    have : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)).IsLE b := by infer_instance
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((DerivedCategory.quotientCompQhIso B).app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).symm b
  let : DerivedCategory.TStructure.t.IsLE
      (DerivedCategory.Minus.ι.obj ((minusUValue F).obj P')) b := hBound
  exact DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Minus.ι.mapIso e).symm b

/-- A right exact functor preserves the last possibly nonzero cohomology
of a projective replacement, hence of the left comparison. -/
lemma leftComparison_highest_degree [EnoughProjectives A] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteColimits F] (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (C : KMinus A) (b : ℤ) [CochainComplex.IsStrictlyLE C.obj.as b] :
    IsIso ((DerivedCategory.homologyFunctor B b).map
      (DerivedCategory.Minus.ι.map (R.counit.app C))) := by
  obtain ⟨P, p, hPb, hP, _, hp⟩ :=
    ProjectiveComplexReplacement.replacement A C.obj.as b inferInstance
  let P' : KMinus A := ⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, b, hPb⟩
  let p' : P' ⟶ C := (minus A).homMk ((HomotopyCategory.quotient A (.up ℤ)).map p)
  have hp' : WMinus A p' :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff p).mpr hp
  obtain ⟨e, he, _⟩ := TotalLeftDerivedFunctor.computation A B
    (inferInstance : (minus A).IsTriangulated) (inferInstance : (minus B).IsTriangulated)
    F R P' C p' hP hp'
  let := hp
  let := hPb
  have := quasiIsoAt_map_of_strictlyLE F p b
  have hmap : IsIso ((DerivedCategory.homologyFunctor B b).map
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map p))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors B b)
      ((F.mapHomologicalComplex (.up ℤ)).map p)).mpr
        ((quasiIsoAt_iff_isIso_homologyMap _ b).mp inferInstance)
  have hmap' : IsIso ((DerivedCategory.homologyFunctor B b).map
      (DerivedCategory.Minus.ι.map ((minusUValue F).map p'))) := by
    change IsIso ((DerivedCategory.homologyFunctor B b).map
      (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient A (.up ℤ)).map p))))
    rw [Functor.mapHomotopyCategory_map]
    exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (DerivedCategory.quotientCompQhIso B) (DerivedCategory.homologyFunctor B b))
        ((F.mapHomologicalComplex (.up ℤ)).map p)).mpr hmap
  rw [← he, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Acyclicity for the left comparison is detected by degree zero and the
negative target cohomology. -/
lemma leftAcyclic_iff_cohomology [EnoughProjectives A] (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) (X : A) :
    leftAcyclic F R X ↔
      IsIso ((DerivedCategory.homologyFunctor B 0).map
        (DerivedCategory.Minus.ι.map (R.counit.app (minusStalkValue X)))) ∧
      ∀ n : ℕ, IsZero (leftDerivedObject F R (n + 1) X) := by
  constructor
  · intro h
    let : IsIso (R.counit.app (minusStalkValue X)) := h
    exact ⟨inferInstance, leftAcyclic_positive_vanishing F R X h⟩
  · rintro ⟨h0, hneg⟩
    change IsIso (R.counit.app (minusStalkValue X))
    apply (ObjectProperty.isIso_hom_iff (R.counit.app (minusStalkValue X))).mp
    rw [DerivedCategory.isIso_iff]
    intro i
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · have : CochainComplex.IsStrictlyGE (minusStalkValue X).obj.as 0 := by
        change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyGE 0
        infer_instance
      have := termwiseMinus_isGE F (minusStalkValue X) 0
      have hsource : IsZero ((DerivedCategory.homologyFunctor B i).obj
          (R.functor.obj ((QMinus A).obj (minusStalkValue X))).obj) := by
        have hn : -((((-i).toNat - 1 : ℕ) : ℤ) + 1) = i := by omega
        have h := hneg ((-i).toNat - 1)
        dsimp [leftDerivedObject, leftDerivedObjectValue] at h
        rwa [hn] at h
      have htarget := DerivedCategory.isZero_of_isGE
        ((minusUValue F).obj (minusStalkValue X)).obj 0 i hi
      exact hsource.isIso htarget _
    · exact h0
    · have : CochainComplex.IsStrictlyLE (minusStalkValue X).obj.as 0 := by
        change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyLE 0
        infer_instance
      have := leftDerived_isLE F R (minusStalkValue X) 0
      have hsource := DerivedCategory.isZero_of_isLE
        (R.functor.obj ((QMinus A).obj (minusStalkValue X))).obj 0 i hi
      have ht : ((minusUValue F).obj (minusStalkValue X)).obj.IsLE 0 := by
        change (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor A 0).obj X)))).IsLE 0
        have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor A 0).obj X))).IsLE 0 := by infer_instance
        exact DerivedCategory.TStructure.t.isLE_of_iso
          ((DerivedCategory.quotientCompQhIso B).app _).symm 0
      have htarget := DerivedCategory.isZero_of_isLE
        ((minusUValue F).obj (minusStalkValue X)).obj 0 i hi
      exact hsource.isIso htarget _

/-- HA-R08: for a right exact functor, left acyclicity is exactly positive
left-derived vanishing. -/
theorem leftVanishing : leftVanishingType := by
  intro A B _ _ _ _ _ _ _ hA hB F _ _ R X
  let := hA
  let := hB
  change leftAcyclic F R X ↔ ∀ n : ℕ, IsZero (leftDerivedObject F R (n + 1) X)
  rw [leftAcyclic_iff_cohomology]
  have : CochainComplex.IsStrictlyLE (minusStalkValue X).obj.as 0 := by
    change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyLE 0
    infer_instance
  exact and_iff_right (leftComparison_highest_degree F R (minusStalkValue X) 0)

end Left
section HomologicalCut
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category D] [Abelian D]
  (H : C ⥤ D) [H.IsHomological] [H.ShiftSequence ℤ]
lemma homology_map_mor₂_isIso (T : Triangle C) (hT : T ∈ distTriang C) (i : ℤ)
    (hi : IsZero ((H.shift i).obj T.obj₁))
    (hi' : IsZero ((H.shift (i+1)).obj T.obj₁)) :
    IsIso ((H.shift i).map T.mor₂) := by
  have : Mono ((H.shift i).map T.mor₂) :=
    (H.homologySequence_mono_shift_map_mor₂_iff T hT i).mpr (hi.eq_of_src _ _)
  have : Epi ((H.shift i).map T.mor₂) :=
    (H.homologySequence_epi_shift_map_mor₂_iff T hT i (i+1) rfl).mpr
      (hi'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _
lemma homology_map_mor₁_isIso (T : Triangle C) (hT : T ∈ distTriang C) (i : ℤ)
    (hi : IsZero ((H.shift i).obj T.obj₃))
    (hi' : IsZero ((H.shift (i-1)).obj T.obj₃)) :
    IsIso ((H.shift i).map T.mor₁) := by
  have : Epi ((H.shift i).map T.mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff T hT i).mpr (hi.eq_of_tgt _ _)
  have : Mono ((H.shift i).map T.mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff T hT (i-1) i (by omega)).mpr
      (hi'.eq_of_src _ _)
  exact isIso_of_mono_of_epi _
end HomologicalCut
section RightMore
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]
lemma rightAcyclic_of_iso (F : A ⥤ B) [F.Additive] {X Y : A} (e : X ≅ Y)
    (hX : rightAcyclic F X) : rightAcyclic F Y := by
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := hX
  change IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj Y))
  exact comparison_iso_of_iso F.rightDerivedFunctorPlusUnith
    ((HomotopyCategory.Plus.singleFunctor A 0).mapIso e)
lemma rightAcyclic_of_isZero (F : A ⥤ B) [F.Additive] (X : A) (hX : IsZero X) :
    rightAcyclic F X := by
  have : Injective X := hX.injective
  exact rightAcyclic_of_injective F X
end RightMore
section LeftMore
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [(minus A).IsTriangulated] [(minus B).IsTriangulated]
lemma leftAcyclic_of_iso (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) {X Y : A} (e : X ≅ Y)
    (hX : leftAcyclic F R X) : leftAcyclic F R Y := by
  have : IsIso (R.counit.app (minusStalkValue X)) := hX
  exact comparison_iso_of_iso R.counit
    ((minus A).isoMk (X := minusStalkValue X) (Y := minusStalkValue Y)
      ((HomotopyCategory.singleFunctor A 0).mapIso e))
lemma leftAcyclic_of_isZero (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) (X : A) (hX : IsZero X) :
    leftAcyclic F R X := by
  have : Projective X := hX.projective
  exact leftAcyclic_of_projective F R X
end LeftMore
section CutTriangle
variable {A : Type u} [Category.{v} A] [Abelian A]

def plusUpperCut (C : HomotopyCategory.Plus A) (a : ℤ) : HomotopyCategory.Plus A :=
  ⟨(HomotopyCategory.quotient A (.up ℤ)).obj (brutalCut C.obj.as (fun i => a ≤ i)), by
    rw [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨a, inferInstance⟩⟩

def plusLowerCut (C : HomotopyCategory.Plus A) (a : ℤ) : HomotopyCategory.Plus A :=
  ⟨(HomotopyCategory.quotient A (.up ℤ)).obj (brutalCut C.obj.as (fun i => i < a)), by
    rw [HomotopyCategory.plus_quotient_obj_iff]
    obtain ⟨b, hb⟩ : CochainComplex.plus A C.obj.as :=
      (HomotopyCategory.plus_quotient_obj_iff C.obj.as).mp C.property
    letI := hb
    exact ⟨b, inferInstance⟩⟩

def plusCutTriangle (C : HomotopyCategory.Plus A) (a : ℤ) :
    Triangle (HomotopyCategory.Plus A) :=
  restrictTriangle (HomotopyCategory.plus A)
    (CochainComplex.trianglehOfDegreewiseSplit (brutalCutSequence C.obj.as a)
      (brutalCutSplitting C.obj.as a))
    (plusUpperCut C a).property C.property (plusLowerCut C a).property

@[simp] lemma plusCutTriangle_obj₁ (C : HomotopyCategory.Plus A) (a : ℤ) :
    (plusCutTriangle C a).obj₁ = plusUpperCut C a := rfl
@[simp] lemma plusCutTriangle_obj₂ (C : HomotopyCategory.Plus A) (a : ℤ) :
    (plusCutTriangle C a).obj₂ = C := rfl
@[simp] lemma plusCutTriangle_obj₃ (C : HomotopyCategory.Plus A) (a : ℤ) :
    (plusCutTriangle C a).obj₃ = plusLowerCut C a := rfl
@[simp] lemma plusCutTriangle_mor₁_hom (C : HomotopyCategory.Plus A) (a : ℤ) :
    (plusCutTriangle C a).mor₁.hom =
      (HomotopyCategory.quotient A (.up ℤ)).map (brutalCutIncl C.obj.as a) := rfl
@[simp] lemma plusCutTriangle_mor₂_hom (C : HomotopyCategory.Plus A) (a : ℤ) :
    (plusCutTriangle C a).mor₂.hom =
      (HomotopyCategory.quotient A (.up ℤ)).map (brutalCutProj C.obj.as a) := rfl

lemma plusCutTriangle_distinguished (C : HomotopyCategory.Plus A) (a : ℤ) :
    plusCutTriangle C a ∈ distTriang _ :=
  restrictTriangle_distinguished _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished
      (brutalCutSequence C.obj.as a) (brutalCutSplitting C.obj.as a)) _ _ _

def minusUpperCut (C : KMinus A) (a : ℤ) : KMinus A :=
  ⟨(HomotopyCategory.quotient A (.up ℤ)).obj (brutalCut C.obj.as (fun i => a ≤ i)), by
    obtain ⟨b, hb⟩ := C.property
    letI := hb
    refine ⟨b, ?_⟩
    change (brutalCut C.obj.as (fun i => a ≤ i)).IsStrictlyLE b
    infer_instance⟩

def minusLowerCut (C : KMinus A) (a : ℤ) : KMinus A :=
  ⟨(HomotopyCategory.quotient A (.up ℤ)).obj (brutalCut C.obj.as (fun i => i < a)),
    a - 1, by
      change (brutalCut C.obj.as (fun i => i < a)).IsStrictlyLE (a - 1)
      infer_instance⟩

variable [(minus A).IsTriangulated]

def minusCutTriangle (C : KMinus A) (a : ℤ) : Triangle (KMinus A) :=
  restrictTriangle (minus A)
    (CochainComplex.trianglehOfDegreewiseSplit (brutalCutSequence C.obj.as a)
      (brutalCutSplitting C.obj.as a))
    (minusUpperCut C a).property C.property (minusLowerCut C a).property

@[simp] lemma minusCutTriangle_obj₁ (C : KMinus A) (a : ℤ) :
    (minusCutTriangle C a).obj₁ = minusUpperCut C a := rfl
@[simp] lemma minusCutTriangle_obj₂ (C : KMinus A) (a : ℤ) :
    (minusCutTriangle C a).obj₂ = C := rfl
@[simp] lemma minusCutTriangle_obj₃ (C : KMinus A) (a : ℤ) :
    (minusCutTriangle C a).obj₃ = minusLowerCut C a := rfl
@[simp] lemma minusCutTriangle_mor₁_hom (C : KMinus A) (a : ℤ) :
    (minusCutTriangle C a).mor₁.hom =
      (HomotopyCategory.quotient A (.up ℤ)).map (brutalCutIncl C.obj.as a) := rfl
@[simp] lemma minusCutTriangle_mor₂_hom (C : KMinus A) (a : ℤ) :
    (minusCutTriangle C a).mor₂.hom =
      (HomotopyCategory.quotient A (.up ℤ)).map (brutalCutProj C.obj.as a) := rfl

lemma minusCutTriangle_distinguished (C : KMinus A) (a : ℤ) :
    minusCutTriangle C a ∈ distTriang _ :=
  restrictTriangle_distinguished _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished
      (brutalCutSequence C.obj.as a) (brutalCutSplitting C.obj.as a)) _ _ _
end CutTriangle
section SingletonIso
variable {A : Type u} [Category.{v} A] [Abelian A]

lemma isZero_X_of_singleton_support (K : CochainComplex A ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE a] (i : ℤ) (hi : i ≠ a) : IsZero (K.X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact K.isZero_of_isStrictlyGE a i h
  · exact K.isZero_of_isStrictlyLE a i h

noncomputable def singletonIso (K : CochainComplex A ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE a] :
    K ≅ (CochainComplex.singleFunctor A a).obj (K.X a) := by
  let f : K ⟶ (CochainComplex.singleFunctor A a).obj (K.X a) :=
    HomologicalComplex.mkHomToSingle (𝟙 (K.X a)) (fun i hi => by
      have hi' : i < a := by change i + 1 = a at hi; omega
      exact (K.isZero_of_isStrictlyGE a i hi').eq_of_src _ _)
  have : ∀ i, IsIso (f.f i) := by
    intro i
    by_cases hi : i = a
    · subst hi
      dsimp [f]
      rw [HomologicalComplex.mkHomToSingle_f]
      infer_instance
    · exact (isZero_X_of_singleton_support K a i hi).isIso
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) a (K.X a) i hi) _
  letI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

noncomputable def plusSingletonIso (C : HomotopyCategory.Plus A) (a : ℤ)
    [CochainComplex.IsStrictlyGE C.obj.as a] [CochainComplex.IsStrictlyLE C.obj.as a] :
    C ≅ (HomotopyCategory.Plus.singleFunctor A a).obj (C.obj.as.X a) :=
  (HomotopyCategory.plus A).isoMk
    ((HomotopyCategory.quotient A (.up ℤ)).mapIso (singletonIso C.obj.as a))

noncomputable def plusSingletonShiftIso (C : HomotopyCategory.Plus A) (a : ℤ)
    [CochainComplex.IsStrictlyGE C.obj.as a] [CochainComplex.IsStrictlyLE C.obj.as a] :
    C ≅ (plusStalkValue (C.obj.as.X a))⟦-a⟧ :=
  plusSingletonIso C a ≪≫
    ((HomotopyCategory.Plus.singleFunctors A).shiftIso (-a) a 0 (by omega)).symm.app _

noncomputable def minusSingletonShiftIso (C : KMinus A) (a : ℤ)
    [(minus A).IsTriangulated]
    [CochainComplex.IsStrictlyGE C.obj.as a] [CochainComplex.IsStrictlyLE C.obj.as a] :
    C ≅ (minusStalkValue (C.obj.as.X a))⟦-a⟧ :=
  (minus A).isoMk
    ((HomotopyCategory.quotient A (.up ℤ)).mapIso (singletonIso C.obj.as a) ≪≫
      ((HomotopyCategory.singleFunctors A).shiftIso (-a) a 0 (by omega)).symm.app _ ≪≫
      ((minus A).ι.commShiftIso (-a)).symm.app (minusStalkValue (C.obj.as.X a)))
end SingletonIso
section RightAux
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]
lemma termwisePlus_isGE (F : A ⥤ B) [F.Additive]
    (C : HomotopyCategory.Plus A) (a : ℤ) [hC : CochainComplex.IsStrictlyGE C.obj.as a] :
    ((plusUValue F).obj C).IsGE a := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  change (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as))).IsGE a
  have : (DerivedCategory.Q.obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as)).IsGE a := by infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as)).symm a
lemma rightComparison_single (F : A ⥤ B) [F.Additive] (X : A) (a : ℤ)
    (hX : rightAcyclic F X) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A a).obj X)) := by
  let : IsIso (F.rightDerivedFunctorPlusUnith.app (plusStalkValue X)) := hX
  let e : (plusStalkValue X)⟦-a⟧ ≅
      (HomotopyCategory.Plus.singleFunctor A a).obj X :=
    ((HomotopyCategory.Plus.singleFunctors A).shiftIso (-a) a 0 (by omega)).app X
  have := comparison_iso_shift F.rightDerivedFunctorPlusUnith (plusStalkValue X) (-a)
  exact comparison_iso_of_iso F.rightDerivedFunctorPlusUnith e
lemma rightAcyclic_brutalCut (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (P : ℤ → Prop) [DecidablePred P]
    (hK : ∀ i, rightAcyclic F (K.X i)) (i : ℤ) :
    rightAcyclic F ((brutalCut K P).X i) := by
  by_cases hi : P i
  · exact rightAcyclic_of_iso F (brutalCutXIso K P i hi).symm (hK i)
  · exact rightAcyclic_of_isZero F _ (brutalCut_isZero_X K P i hi)

lemma rightComparison_singleton (F : A ⥤ B) [F.Additive]
    (C : HomotopyCategory.Plus A) (a : ℤ)
    [CochainComplex.IsStrictlyGE C.obj.as a] [CochainComplex.IsStrictlyLE C.obj.as a]
    (hC : ∀ i, rightAcyclic F (C.obj.as.X i)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app C) := by
  have : IsIso (F.rightDerivedFunctorPlusUnith.app (plusStalkValue (C.obj.as.X a))) := hC a
  have := comparison_iso_shift F.rightDerivedFunctorPlusUnith
    (plusStalkValue (C.obj.as.X a)) (-a)
  exact comparison_iso_of_iso F.rightDerivedFunctorPlusUnith (plusSingletonShiftIso C a).symm

lemma rightComparison_bounded (F : A ⥤ B) [F.Additive]
    (n : ℕ) (a : ℤ) (C : HomotopyCategory.Plus A)
    [CochainComplex.IsStrictlyGE C.obj.as a]
    [CochainComplex.IsStrictlyLE C.obj.as (a+n)]
    (hC : ∀ i, rightAcyclic F (C.obj.as.X i)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app C) := by
  induction n generalizing a C with
  | zero =>
    have : CochainComplex.IsStrictlyLE C.obj.as a := by simpa using
      (inferInstance : CochainComplex.IsStrictlyLE C.obj.as (a+(0:ℕ)))
    exact rightComparison_singleton F C a hC
  | succ n ih =>
    let U := plusUpperCut C (a+1)
    let L := plusLowerCut C (a+1)
    have hUge : CochainComplex.IsStrictlyGE U.obj.as (a+1) := by
      change (brutalCut C.obj.as (fun i => a+1 ≤ i)).IsStrictlyGE (a+1)
      infer_instance
    have hUle : CochainComplex.IsStrictlyLE U.obj.as ((a+1)+n) := by
      have hle : CochainComplex.IsStrictlyLE C.obj.as ((a+1)+n) := by
        convert (inferInstance : CochainComplex.IsStrictlyLE C.obj.as (a+(n+1:ℕ))) using 1 <;> omega
      change (brutalCut C.obj.as (fun i => a+1 ≤ i)).IsStrictlyLE ((a+1)+n)
      infer_instance
    have hLge : CochainComplex.IsStrictlyGE L.obj.as a := by
      change (brutalCut C.obj.as (fun i => i < a+1)).IsStrictlyGE a
      infer_instance
    have hLle : CochainComplex.IsStrictlyLE L.obj.as a := by
      have : a = (a+1)-1 := by omega
      rw [this]
      change (brutalCut C.obj.as (fun i => i < a+1)).IsStrictlyLE ((a+1)-1)
      infer_instance
    have hU : IsIso (F.rightDerivedFunctorPlusUnith.app U) :=
      ih (a+1) U (rightAcyclic_brutalCut F C.obj.as _ hC)
    have hL : IsIso (F.rightDerivedFunctorPlusUnith.app L) :=
      rightComparison_singleton F L a (rightAcyclic_brutalCut F C.obj.as _ hC)
    letI : IsIso (F.rightDerivedFunctorPlusUnith.app (plusCutTriangle C (a+1)).obj₁) := hU
    letI : IsIso (F.rightDerivedFunctorPlusUnith.app (plusCutTriangle C (a+1)).obj₃) := hL
    exact comparison_iso_extension F.rightDerivedFunctorPlusUnith
      (plusCutTriangle C (a+1)) (plusCutTriangle_distinguished C (a+1))
lemma plus_homology_map_mor₂_isIso
    (T : Triangle (DerivedCategory.Plus B)) (hT : T ∈ distTriang _)
    (a : ℤ) [T.obj₁.IsGE a] (i : ℤ) (hi : i+1 < a) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B i).map T.mor₂) := by
  exact homology_map_mor₂_isIso (DerivedCategory.homologyFunctor B 0)
    (DerivedCategory.Plus.ι.mapTriangle.obj T)
    (DerivedCategory.Plus.ι.map_distinguished T hT) i
    (DerivedCategory.Plus.isZero_homology_of_isGE T.obj₁ a i (by omega))
    (DerivedCategory.Plus.isZero_homology_of_isGE T.obj₁ a (i+1) hi)

lemma rightComparison_homotopy (F : A ⥤ B) [F.Additive]
    (C : HomotopyCategory.Plus A) (hC : ∀ i, rightAcyclic F (C.obj.as.X i)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app C) := by
  obtain ⟨a, ha⟩ : CochainComplex.plus A C.obj.as :=
    (HomotopyCategory.plus_quotient_obj_iff C.obj.as).mp C.property
  letI := ha
  rw [DerivedCategory.Plus.isIso_iff]
  intro i
  let b : ℤ := max a (i+1)
  let U := plusUpperCut C (b+1)
  let L := plusLowerCut C (b+1)
  let T := plusCutTriangle C (b+1)
  have hT : T ∈ distTriang _ := plusCutTriangle_distinguished C (b+1)
  have hUge : CochainComplex.IsStrictlyGE U.obj.as (b+1) := by
    change (brutalCut C.obj.as (fun j => b+1 ≤ j)).IsStrictlyGE (b+1)
    infer_instance
  have hLge : CochainComplex.IsStrictlyGE L.obj.as a := by
    change (brutalCut C.obj.as (fun j => j < b+1)).IsStrictlyGE a
    infer_instance
  have hLle : CochainComplex.IsStrictlyLE L.obj.as (a+(b-a).toNat) := by
    have hb : a+(b-a).toNat = (b+1)-1 := by dsimp [b]; omega
    rw [hb]
    change (brutalCut C.obj.as (fun j => j < b+1)).IsStrictlyLE ((b+1)-1)
    infer_instance
  have hL : IsIso (F.rightDerivedFunctorPlusUnith.app L) :=
    rightComparison_bounded F (b-a).toNat a L (rightAcyclic_brutalCut F C.obj.as _ hC)
  let G := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let H := DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus
  have hGge : (G.obj T.obj₁).IsGE (b+1) := termwisePlus_isGE F U (b+1)
  have hHge : (H.obj T.obj₁).IsGE (b+1) := rightDerived_isGE_homotopy F U (b+1)
  letI : (G.mapTriangle.obj T).obj₁.IsGE (b+1) := hGge
  letI : (H.mapTriangle.obj T).obj₁.IsGE (b+1) := hHge
  have hG : IsIso ((DerivedCategory.Plus.homologyFunctor B i).map (G.map T.mor₂)) := by
    exact plus_homology_map_mor₂_isIso (G.mapTriangle.obj T)
      (G.map_distinguished T hT) (b+1) i (by dsimp [b]; omega)
  have hH : IsIso ((DerivedCategory.Plus.homologyFunctor B i).map (H.map T.mor₂)) := by
    exact plus_homology_map_mor₂_isIso (H.mapTriangle.obj T)
      (H.map_distinguished T hT) (b+1) i (by dsimp [b]; omega)
  have hn := congrArg ((DerivedCategory.Plus.homologyFunctor B i).map)
    (F.rightDerivedFunctorPlusUnith.naturality T.mor₂)
  simp only [Functor.map_comp] at hn
  change IsIso ((DerivedCategory.Plus.homologyFunctor B i).map
    (F.rightDerivedFunctorPlusUnith.app T.obj₂))
  have : IsIso (F.rightDerivedFunctorPlusUnith.app T.obj₃) := hL
  have : IsIso (((DerivedCategory.Plus.homologyFunctor B i).map
      (F.rightDerivedFunctorPlusUnith.app T.obj₂)) ≫
      (DerivedCategory.Plus.homologyFunctor B i).map (H.map T.mor₂)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Plus.homologyFunctor B i).map (H.map T.mor₂))
end RightAux

/-- HA-R08: a bounded-below complex of right F-acyclic terms computes its
right derived image, for every additive F. -/
theorem rightComparison : rightComparisonType := by
  intro A B _ _ _ _ _ _ _ F _ C hC
  exact rightComparison_homotopy F C hC

lemma homology_mor₁_isIso_of_isZero
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (T : Triangle (DerivedCategory B)) (hT : T ∈ distTriang _)
    (i : ℤ) (hz₀ : IsZero ((DerivedCategory.homologyFunctor B (i-1)).obj T.obj₃))
    (hz₁ : IsZero ((DerivedCategory.homologyFunctor B i).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor B i).map T.mor₁) := by
  have : Epi ((DerivedCategory.homologyFunctor B i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
      (hz₁.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor B i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i-1) i (by omega)).mpr
      (hz₀.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

section Left
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughProjectives A]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]

lemma termwiseMinus_isLE (F : A ⥤ B) [F.Additive]
    (C : KMinus A) (b : ℤ) [CochainComplex.IsStrictlyLE C.obj.as b] :
    ((minusUValue F).obj C).obj.IsLE b := by
  change (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as))).IsLE b
  have : (DerivedCategory.Q.obj
    ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as)).IsLE b := by infer_instance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C.obj.as)).symm b

lemma leftAcyclic_brutalCut (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (K : CochainComplex A ℤ) (P : ℤ → Prop) [DecidablePred P]
    (hK : ∀ i, leftAcyclic F R (K.X i)) (i : ℤ) :
    leftAcyclic F R ((brutalCut K P).X i) := by
  by_cases hi : P i
  · exact leftAcyclic_of_iso F R (brutalCutXIso K P i hi).symm (hK i)
  · exact leftAcyclic_of_isZero F R _ (brutalCut_isZero_X K P i hi)

lemma leftComparison_singleton (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F) (C : KMinus A) (a : ℤ)
    [CochainComplex.IsStrictlyGE C.obj.as a] [CochainComplex.IsStrictlyLE C.obj.as a]
    (hC : ∀ i, leftAcyclic F R (C.obj.as.X i)) : IsIso (R.counit.app C) := by
  letI : R.functor.CommShift ℤ := R.commShift
  letI : (QMinus A).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  letI : NatTrans.CommShift R.counit ℤ := R.counit_shift
  have : IsIso (R.counit.app (minusStalkValue (C.obj.as.X a))) := hC a
  have := comparison_iso_shift R.counit (minusStalkValue (C.obj.as.X a)) (-a)
  exact comparison_iso_of_iso R.counit (minusSingletonShiftIso C a).symm

lemma leftComparison_bounded_of_singleton (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (hsingle : ∀ (C : KMinus A) (a : ℤ)
      [CochainComplex.IsStrictlyGE C.obj.as a] [CochainComplex.IsStrictlyLE C.obj.as a],
      (∀ i, leftAcyclic F R (C.obj.as.X i)) →
      IsIso (R.counit.app C))
    (n : ℕ) (a : ℤ) (C : KMinus A)
    [CochainComplex.IsStrictlyGE C.obj.as a]
    [CochainComplex.IsStrictlyLE C.obj.as (a+n)]
    (hC : ∀ i, leftAcyclic F R (C.obj.as.X i)) :
    IsIso (R.counit.app C) := by
  letI : R.functor.CommShift ℤ := R.commShift
  letI : R.functor.IsTriangulated := R.triangulated
  letI : (QMinus A).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  letI : NatTrans.CommShift R.counit ℤ := R.counit_shift
  haveI : (minusUValue F).IsTriangulated := by dsimp [minusUValue]; infer_instance
  induction n generalizing a C with
  | zero =>
    have : CochainComplex.IsStrictlyLE C.obj.as a := by simpa using
      (inferInstance : CochainComplex.IsStrictlyLE C.obj.as (a+(0:ℕ)))
    exact hsingle C a hC
  | succ n ih =>
    let U := minusUpperCut C (a+1)
    let L := minusLowerCut C (a+1)
    have hUge : CochainComplex.IsStrictlyGE U.obj.as (a+1) := by
      change (brutalCut C.obj.as (fun i => a+1 ≤ i)).IsStrictlyGE (a+1)
      infer_instance
    have hUle : CochainComplex.IsStrictlyLE U.obj.as ((a+1)+n) := by
      have hle : CochainComplex.IsStrictlyLE C.obj.as ((a+1)+n) := by
        convert (inferInstance : CochainComplex.IsStrictlyLE C.obj.as (a+(n+1:ℕ))) using 1 <;> omega
      change (brutalCut C.obj.as (fun i => a+1 ≤ i)).IsStrictlyLE ((a+1)+n)
      infer_instance
    have hLge : CochainComplex.IsStrictlyGE L.obj.as a := by
      change (brutalCut C.obj.as (fun i => i < a+1)).IsStrictlyGE a
      infer_instance
    have hLle : CochainComplex.IsStrictlyLE L.obj.as a := by
      have : a = (a+1)-1 := by omega
      rw [this]
      change (brutalCut C.obj.as (fun i => i < a+1)).IsStrictlyLE ((a+1)-1)
      infer_instance
    have hU : IsIso (R.counit.app U) :=
      ih (a+1) U (leftAcyclic_brutalCut F R C.obj.as _ hC)
    have hL : IsIso (R.counit.app L) :=
      hsingle L a (leftAcyclic_brutalCut F R C.obj.as _ hC)
    letI : IsIso (R.counit.app (minusCutTriangle C (a+1)).obj₁) := hU
    letI : IsIso (R.counit.app (minusCutTriangle C (a+1)).obj₃) := hL
    exact comparison_iso_extension R.counit
      (minusCutTriangle C (a+1)) (minusCutTriangle_distinguished C (a+1))
lemma leftComparison_finite (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (C : KMinus A) (a : ℤ) [CochainComplex.IsStrictlyGE C.obj.as a]
    (hC : ∀ n : ℤ, leftAcyclic F R (C.obj.as.X n)) : IsIso (R.counit.app C) := by
  obtain ⟨b, hb⟩ := C.property
  have : CochainComplex.IsStrictlyLE C.obj.as b := hb
  have : CochainComplex.IsStrictlyLE C.obj.as (a+(b-a).toNat) :=
    CochainComplex.isStrictlyLE_of_le C.obj.as b _ (by omega)
  exact leftComparison_bounded_of_singleton F R (leftComparison_singleton F R)
    (b-a).toNat a C hC

lemma leftComparison_of_finite (F : A ⥤ B) [F.Additive]
    (R : ExactLeftData.{u, v, u', v', w, w'} F)
    (hfinite : ∀ (K : KMinus A) (a : ℤ), CochainComplex.IsStrictlyGE K.obj.as a →
      (∀ n : ℤ, leftAcyclicValue F R (K.obj.as.X n)) → IsIso (R.counit.app K))
    (C : KMinus A) (hC : ∀ n : ℤ, leftAcyclicValue F R (C.obj.as.X n)) :
    IsIso (R.counit.app C) := by
  letI : R.functor.CommShift ℤ := R.commShift
  letI : R.functor.IsTriangulated := R.triangulated
  letI : (QMinus A).CommShift ℤ := quotientShift
  letI : (minusUValue F).CommShift ℤ := inputShift F
  let G : KMinus A ⥤ DerivedCategory B := QMinus A ⋙ R.functor ⋙ DerivedCategory.Minus.ι
  let H : KMinus A ⥤ DerivedCategory B := minusUValue F ⋙ DerivedCategory.Minus.ι
  haveI : G.IsTriangulated := by dsimp [G]; infer_instance
  haveI : H.IsTriangulated := by dsimp [H, minusUValue]; infer_instance
  apply (ObjectProperty.isIso_hom_iff (R.counit.app C)).mp
  rw [DerivedCategory.isIso_iff]
  intro i
  change IsIso ((DerivedCategory.homologyFunctor B i).map
      (DerivedCategory.Minus.ι.map (R.counit.app C)))
  let U := minusUpperCut C (i-1)
  let L := minusLowerCut C (i-1)
  let T := minusCutTriangle C (i-1)
  have hT : T ∈ distTriang _ := minusCutTriangle_distinguished C (i-1)
  have hU : IsIso (R.counit.app U) := by
    apply hfinite U (i-1) (by
      change CochainComplex.IsStrictlyGE (brutalCut C.obj.as (fun j => i-1 ≤ j)) (i-1)
      infer_instance)
    intro n
    by_cases hn : i-1 ≤ n
    · have e := brutalCutXIso C.obj.as (fun j => i-1 ≤ j) n hn
      -- acyclicity is invariant under isomorphisms of original objects.
      exact leftAcyclic_of_iso F R e.symm (hC n)
    · have hz := brutalCut_isZero_X C.obj.as (fun j => i-1 ≤ j) n hn
      exact leftAcyclic_of_isZero F R _ hz
  haveI : CochainComplex.IsStrictlyLE L.obj.as (i-2) := by
    change CochainComplex.IsStrictlyLE (brutalCut C.obj.as (fun j => j < i-1)) (i-2)
    convert brutalCut_lowerLE C.obj.as (i-1) using 1 <;> omega
  have hGL : (G.obj L).IsLE (i-2) := leftDerived_isLE F R L (i-2)
  have hHL : (H.obj L).IsLE (i-2) := by
    exact termwiseMinus_isLE F L (i-2)
  have hG : IsIso ((DerivedCategory.homologyFunctor B i).map (G.map T.mor₁)) := by
    exact homology_mor₁_isIso_of_isZero _ (G.map_distinguished T hT) i
      (DerivedCategory.isZero_of_isLE (G.obj L) (i-2) (i-1) (by omega))
      (DerivedCategory.isZero_of_isLE (G.obj L) (i-2) i (by omega))
  have hH : IsIso ((DerivedCategory.homologyFunctor B i).map (H.map T.mor₁)) := by
    exact homology_mor₁_isIso_of_isZero _ (H.map_distinguished T hT) i
      (DerivedCategory.isZero_of_isLE (H.obj L) (i-2) (i-1) (by omega))
      (DerivedCategory.isZero_of_isLE (H.obj L) (i-2) i (by omega))
  have hn := congrArg (fun f => (DerivedCategory.homologyFunctor B i).map
      (DerivedCategory.Minus.ι.map f)) (R.counit.naturality T.mor₁)
  simp only [Functor.map_comp] at hn
  have hi : IsIso ((DerivedCategory.homologyFunctor B i).map
      (DerivedCategory.Minus.ι.map (R.counit.app U))) := by infer_instance
  change (DerivedCategory.homologyFunctor B i).map (G.map T.mor₁) ≫
    (DerivedCategory.homologyFunctor B i).map (DerivedCategory.Minus.ι.map (R.counit.app C)) =
      (DerivedCategory.homologyFunctor B i).map (DerivedCategory.Minus.ι.map (R.counit.app U)) ≫
      (DerivedCategory.homologyFunctor B i).map (H.map T.mor₁) at hn
  exact (isIso_comp_left_iff ((DerivedCategory.homologyFunctor B i).map
    (G.map T.mor₁)) _).mp (by rw [hn]; infer_instance)
end Left

theorem leftComparison : leftComparisonType := by
  intro A B _ _ _ _ _ _ _ hA hB F _ R C hC
  let := hA
  let := hB
  exact leftComparison_of_finite F R
    (fun K a ha hK => by
      let := ha
      exact leftComparison_finite F R K a hK) C hC
end AdvancedHomologicalAlgebra.AcyclicTermComparison
