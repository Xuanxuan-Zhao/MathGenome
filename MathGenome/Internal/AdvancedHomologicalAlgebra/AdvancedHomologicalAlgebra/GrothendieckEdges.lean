import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.EdgesAndFiveTerms
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckEdges
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveComplexReplacement

noncomputable section Base
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

/-- A derived lower bound can be represented by a termwise injective model
with that same bound, so an additive functor cannot create lower terms. -/
theorem preservesLowerBounds : Specs.PreservesLowerBounds.{u₁,v₁,u₂,v₂,w₁,w₂} := by
  intro A B _ _ _ _ _ _ _ F _ Y a hY
  letI := hY
  obtain ⟨I, hI, hb, ⟨e⟩⟩ := InjectiveComplexReplacement.derivedRepresentative A Y.obj a
    (fun n hn => DerivedCategory.Plus.isZero_homology_of_isGE Y a n hn)
  letI := hb
  let II : CochainComplex.Plus A := ⟨I, a, hb⟩
  let ee : Y ≅ DerivedCategory.Plus.Q.obj II :=
    ObjectProperty.isoMk _ e
  obtain ⟨ei, _⟩ := TotalRightDerivedFunctor.computesReplacement A B F II II (𝟙 II)
    (by change QuasiIso (𝟙 I); infer_instance) hI
  let ef := F.rightDerivedFunctorPlus.mapIso ee ≪≫ ei
  haveI : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up ℤ)).obj I) a := by
    infer_instance
  haveI : (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj II)).IsGE a := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I)).IsGE a
    infer_instance
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso ef.symm a

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The second page calculation includes its action on every object map. -/
def objectSecondIso (P : Package F G) (p q : ℕ) :
    objectSequence F G P ⋙ pageEval 0 (p : ℤ) ((p : ℤ)+(q : ℤ)) ≅
      rightValue F q ⋙ rightValue G p :=
  isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0) (P.secondIso p (q : ℤ))

lemma objectSecondIso_eq (P : Package F G) (p q : ℕ) :
    objectSecondIso F G P p q =
      associator _ _ _ ≪≫
        isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0) (P.secondIso p (q : ℤ)) ≪≫
        (associator (DerivedCategory.Plus.singleFunctor A 0)
          (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B (q : ℤ))
          (rightValue G p)).symm := by
  ext X
  simp [objectSecondIso]

def objectTargetIso (P : Package F G) (n : ℕ) :
    objectSequence F G P ⋙ targetEval (n : ℤ) ≅ rightValue (F ⋙ G) n :=
  isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0) (P.targetIso (n : ℤ))

/-- Additivity sends a zero cohomology object to zero; no exactness of the
classical derived-value functor is used. -/
theorem object_quadrant (P : Package F G) (X : A) (p n : ℤ)
    (h : p < 0 ∨ n < p) :
    IsZero (((objectSequence F G P).obj X).page 0 p n) := by
  rcases h with hp | hn
  · convert P.negative ((DerivedCategory.Plus.singleFunctor A 0).obj X) p (n-p) hp using 1 <;>
      congr 1 <;> omega
  · by_cases hp : p < 0
    · convert P.negative ((DerivedCategory.Plus.singleFunctor A 0).obj X) p (n-p) hp using 1 <;>
        congr 1 <;> omega
    · let Y := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
      haveI : Y.IsGE 0 := preservesLowerBounds A B F _ 0 (by infer_instance)
      have hz := DerivedCategory.Plus.isZero_homology_of_isGE Y 0 (n-p) (by omega)
      let e := (P.secondIso p.toNat (n-p)).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)
      have he : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega)
      haveI : (rightValue G p.toNat).Additive := by
        dsimp [rightValue]
        infer_instance
      have hz' := (rightValue G p.toNat).map_isZero hz
      exact IsZero.of_iso hz' (by simpa [he, pageEval, Y] using e)

theorem objectCase : Specs.ObjectStatement.{u₁,v₁,u₂,v₂,u₃,v₃,w₁,w₂,w₃} := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ F G _ _ P
  exact ⟨{
    secondIso := objectSecondIso F G P
    secondIso_eq := objectSecondIso_eq F G P
    targetIso := objectTargetIso F G P
    targetIso_eq := fun _ => rfl
    quadrant := object_quadrant F G P }⟩

end AdvancedHomologicalAlgebra.GrothendieckEdges

end Base

noncomputable section G05DerivedRow

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open AdvancedHomologicalAlgebra.ClassicalDerivedValues
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

omit [EnoughInjectives B] in
lemma stalkToDerived_homology_zero_isIso [PreservesFiniteLimits F] (X : A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map ((stalkToDerived F).app X)) := by
  let K := (stalkComplex A).obj X
  haveI : K.obj.IsStrictlyGE 0 := by
    change ((CochainComplex.singleFunctor A 0).obj X).IsStrictlyGE 0
    infer_instance
  haveI := AcyclicTermComparison.rightComparison_lowest_degree F K 0
  simp only [stalkToDerived, NatTrans.comp_app, whiskerLeft_app, Functor.map_comp]
  infer_instance

/-- The actual derived unit induces the canonical degree-zero isomorphism. -/
def degreeZeroIso [PreservesFiniteLimits F] : F ≅ rightValue F 0 := by
  haveI (X : A) : IsIso ((degreeZeroUnit F).app X) := by
    dsimp only [degreeZeroUnit, NatTrans.comp_app, isoWhiskerLeft_inv,
      whiskerLeft_app, whiskerRight_app]
    haveI := stalkToDerived_homology_zero_isIso F X
    infer_instance
  letI : IsIso (degreeZeroUnit F) := NatIso.isIso_of_isIso_app _
  exact asIso (degreeZeroUnit F)

/-- The zero truncation of a degree-zero stalk is canonically that stalk. -/
def stalkTruncIso : (F ⋙ DerivedCategory.Plus.singleFunctor B 0) ⋙
    DerivedCategory.Plus.TStructure.t.truncLE 0 ≅ F ⋙ DerivedCategory.Plus.singleFunctor B 0 := by
  let η : (F ⋙ DerivedCategory.Plus.singleFunctor B 0) ⋙
      DerivedCategory.Plus.TStructure.t.truncLE 0 ⟶ F ⋙ DerivedCategory.Plus.singleFunctor B 0 :=
    whiskerLeft (F ⋙ DerivedCategory.Plus.singleFunctor B 0)
      (DerivedCategory.Plus.TStructure.t.truncLEι 0)
  haveI (X : A) : IsIso (η.app X) := by
    change IsIso ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app
      ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)))
    infer_instance
  haveI : IsIso η := NatIso.isIso_of_isIso_app _
  exact asIso η

/-- The canonical factor of the derived unit through the zero truncation. -/
def stalkToTruncDerived : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ⟶
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.TStructure.t.truncLE 0 :=
  (stalkTruncIso F).inv ≫
    whiskerRight (stalkToDerived F) (DerivedCategory.Plus.TStructure.t.truncLE 0)

@[reassoc]
lemma stalkToTruncDerived_ι (X : A) :
    (stalkToTruncDerived F).app X ≫
      (DerivedCategory.Plus.TStructure.t.truncLEι 0).app
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) =
    (stalkToDerived F).app X := by
  dsimp only [stalkToTruncDerived, NatTrans.comp_app, whiskerRight_app]
  have hh := (DerivedCategory.Plus.TStructure.t.truncLEι 0).naturality ((stalkToDerived F).app X)
  dsimp only [Functor.comp_obj, Functor.id_map] at hh
  rw [Category.assoc, hh, ← Category.assoc]
  have h := (stalkTruncIso F).inv_hom_id_app X
  change (stalkTruncIso F).inv.app X ≫
    (DerivedCategory.Plus.TStructure.t.truncLEι 0).app
      ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)) = 𝟙 _ at h
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun z => z ≫ (stalkToDerived F).app X) h

lemma homology_truncLEι_isIso (Y : DerivedCategory.Plus B) (a q : ℤ) (hq : q ≤ a) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B q).map
      ((DerivedCategory.Plus.TStructure.t.truncLEι a).app Y)) := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let T := (t.triangleLEGE a (a+1) rfl).obj Y
  have ht : T ∈ distTriang (DerivedCategory.Plus B) := t.triangleLEGE_distinguished a (a+1) rfl Y
  have hz : IsZero ((H.shift q).obj T.obj₃) := by
    change IsZero ((DerivedCategory.Plus.homologyFunctor B q).obj ((t.truncGE (a+1)).obj Y))
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ (a+1) _ (by omega)
  have hz' : IsZero ((H.shift (q-1)).obj T.obj₃) := by
    change IsZero ((DerivedCategory.Plus.homologyFunctor B (q-1)).obj ((t.truncGE (a+1)).obj Y))
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ (a+1) _ (by omega)
  haveI : Epi ((H.shift q).map T.mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff T ht q).2 (hz.eq_of_tgt _ _)
  haveI : Mono ((H.shift q).map T.mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff T ht (q-1) q (by omega)).2
      (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((H.shift q).map T.mor₁)

lemma isIso_of_homology_zero {X Y : DerivedCategory.Plus B}
    [X.IsGE 0] [X.IsLE 0] [Y.IsGE 0] [Y.IsLE 0] (f : X ⟶ Y)
    (hf : IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map f)) : IsIso f := by
  apply (DerivedCategory.Plus.isIso_iff f).mpr
  intro q
  by_cases hq : q = 0
  · subst q; exact hf
  · rcases lt_or_gt_of_ne hq with hq | hq
    · exact (DerivedCategory.Plus.isZero_homology_of_isGE X 0 q hq).isIso
        (DerivedCategory.Plus.isZero_homology_of_isGE Y 0 q hq) _
    · exact (DerivedCategory.Plus.isZero_homology_of_isLE X 0 q hq).isIso
        (DerivedCategory.Plus.isZero_homology_of_isLE Y 0 q hq) _

lemma stalkToTruncDerived_app_isIso [PreservesFiniteLimits F] (X : A) :
    IsIso ((stalkToTruncDerived F).app X) := by
  let S := (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)
  let Y := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  haveI : Y.IsGE 0 := preservesLowerBounds A B F _ 0 (by infer_instance)
  haveI : ((DerivedCategory.Plus.TStructure.t.truncLE 0).obj Y).IsGE 0 := by infer_instance
  haveI : ((DerivedCategory.Plus.TStructure.t.truncLE 0).obj Y).IsLE 0 := by infer_instance
  haveI : S.IsGE 0 := by dsimp [S]; infer_instance
  haveI : S.IsLE 0 := by dsimp [S]; infer_instance
  change IsIso (show S ⟶ (DerivedCategory.Plus.TStructure.t.truncLE 0).obj Y from
    (stalkToTruncDerived F).app X)
  apply isIso_of_homology_zero
  let H := DerivedCategory.Plus.homologyFunctor B 0
  haveI := stalkToDerived_homology_zero_isIso F X
  haveI := homology_truncLEι_isIso Y 0 0 (by omega)
  have h := congrArg H.map (stalkToTruncDerived_ι F X)
  rw [Functor.map_comp] at h
  haveI : IsIso (H.map ((stalkToTruncDerived F).app X) ≫
      H.map ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app Y)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (H.map ((DerivedCategory.Plus.TStructure.t.truncLEι 0).app Y))

/-- The canonical F(X)[0] ≅ τ≤0 RF(X[0]), naturally in X. -/
def stalkToTruncDerivedIso [PreservesFiniteLimits F] :
    F ⋙ DerivedCategory.Plus.singleFunctor B 0 ≅
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.TStructure.t.truncLE 0 := by
  haveI (X : A) := stalkToTruncDerived_app_isIso F X
  haveI : IsIso (stalkToTruncDerived F) := NatIso.isIso_of_isIso_app _
  exact asIso (stalkToTruncDerived F)

lemma stalkToDerived_eq_trunc [PreservesFiniteLimits F] :
    stalkToDerived F = (stalkToTruncDerivedIso F).hom ≫
      whiskerLeft (DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus)
        (DerivedCategory.Plus.TStructure.t.truncLEι 0) := by
  apply NatTrans.ext
  funext X
  exact (stalkToTruncDerived_ι F X).symm

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05DerivedRow

noncomputable section G05Truncation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w w' uA vA wA
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges

variable {B : Type u} {C : Type u'} [Category.{v} B] [Abelian B]
  [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w'} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive]

theorem isIso_homology_rightDerived_truncLEι
    (Y : DerivedCategory.Plus B) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor C n).map
      (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLEι n).app Y))) := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let R := G.rightDerivedFunctorPlus
  let T := (t.triangleLEGE n (n+1) rfl).obj Y
  have hT : R.mapTriangle.obj T ∈ distTriang (DerivedCategory.Plus C) :=
    R.map_distinguished _ (t.triangleLEGE_distinguished n (n+1) rfl Y)
  have hGE : (R.obj ((t.truncGE (n+1)).obj Y)).IsGE (n+1) :=
    preservesLowerBounds B C G _ (n+1) (by infer_instance)
  letI := hGE
  have hn := DerivedCategory.Plus.isZero_homology_of_isGE
    (R.obj ((t.truncGE (n+1)).obj Y)) (n+1) n (by omega)
  have hprev := DerivedCategory.Plus.isZero_homology_of_isGE
    (R.obj ((t.truncGE (n+1)).obj Y)) (n+1) (n-1) (by omega)
  let H := DerivedCategory.Plus.homologyFunctor C 0
  haveI : Epi ((H.shift n).map (R.mapTriangle.obj T).mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff _ hT n).mpr
      (hn.eq_of_tgt _ _)
  haveI : Mono ((H.shift n).map (R.mapTriangle.obj T).mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff _ hT (n-1) n (by omega)).mpr
      (hprev.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((H.shift n).map (R.mapTriangle.obj T).mor₁)

/-- Right derivation followed by degree `n` cohomology only depends on `τ≤n`. -/
def homology_rightDerived_truncLEIso (n : ℤ) :
    DerivedCategory.Plus.TStructure.t.truncLE n ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor C n ≅
    G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n := by
  let α := whiskerRight (DerivedCategory.Plus.TStructure.t.truncLEι n)
    (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n)
  haveI : ∀ Y, IsIso (α.app Y) := fun Y =>
    isIso_homology_rightDerived_truncLEι G Y n
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

def singlePlusHomologyIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor B n ⋙ DerivedCategory.Plus.homologyFunctor B n ≅ 𝟭 B :=
  DerivedCategory.singleFunctorCompHomologyFunctorIso B n

lemma pure_homology_map_injective (n : ℤ) {X Y : DerivedCategory B}
    [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    {f g : X ⟶ Y}
    (h : (DerivedCategory.homologyFunctor B n).map f =
      (DerivedCategory.homologyFunctor B n).map g) : f = g := by
  obtain ⟨U, ⟨eU⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  obtain ⟨V, ⟨eV⟩⟩ := Y.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let eX := eU
  let eY := eV
  let S := DerivedCategory.singleFunctor B n
  let H := DerivedCategory.homologyFunctor B n
  change H.map f = H.map g at h
  let φ := S.preimage (eX.inv ≫ f ≫ eY.hom)
  let ψ := S.preimage (eX.inv ≫ g ≫ eY.hom)
  have hh : (S ⋙ H).map φ = (S ⋙ H).map ψ := by
    simp only [Functor.comp_map, φ, ψ, Functor.map_preimage]
    simp only [Functor.map_comp, h]
  have hφ : φ = ψ := by
    letI : (S ⋙ H).Faithful := Functor.Faithful.of_iso (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).symm
    exact (S ⋙ H).map_injective hh
  have hh' := congrArg S.map hφ
  dsimp only [φ, ψ] at hh'
  simpa only [Functor.map_preimage, Category.assoc, cancel_epi, cancel_mono] using hh'

lemma exists_pureHomologyIso (X : DerivedCategory B) (n : ℤ)
    [X.IsGE n] [X.IsLE n] :
    ∃ e : X ≅ (DerivedCategory.singleFunctor B n).obj
      ((DerivedCategory.homologyFunctor B n).obj X),
      (DerivedCategory.homologyFunctor B n).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app
          ((DerivedCategory.homologyFunctor B n).obj X) = 𝟙 _ := by
  obtain ⟨U, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let S := DerivedCategory.singleFunctor B n
  let H := DerivedCategory.homologyFunctor B n
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso B n
  let k : H.obj X ≅ U := H.mapIso e ≪≫ ε.app U
  refine ⟨e ≪≫ S.mapIso k.symm, ?_⟩
  change H.map (e.hom ≫ S.map k.inv) ≫ ε.hom.app (H.obj X) = _
  rw [Functor.map_comp, Category.assoc]
  change H.map e.hom ≫ (S ⋙ H).map k.inv ≫ ε.hom.app (H.obj X) = _
  rw [ε.hom.naturality k.inv]
  dsimp only [Functor.id_map]
  rw [← Category.assoc]
  exact k.hom_inv_id

def pureHomologyIso (X : DerivedCategory B) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor B n).obj ((DerivedCategory.homologyFunctor B n).obj X) :=
  Classical.choose (exists_pureHomologyIso X n)

@[reassoc]
lemma pureHomologyIso_normalization (X : DerivedCategory B) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    (DerivedCategory.homologyFunctor B n).map (pureHomologyIso X n).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app
        ((DerivedCategory.homologyFunctor B n).obj X) = 𝟙 _ :=
  Classical.choose_spec (exists_pureHomologyIso X n)

variable {D : Type*} [Category* D]
def pureFunctorIso (T : D ⥤ DerivedCategory B) (n : ℤ)
    [∀ X, (T.obj X).IsGE n] [∀ X, (T.obj X).IsLE n] :
    T ≅ T ⋙ DerivedCategory.homologyFunctor B n ⋙ DerivedCategory.singleFunctor B n :=
  NatIso.ofComponents (fun X => pureHomologyIso (T.obj X) n) (by
    intro X Y f
    apply pure_homology_map_injective n
      (X := T.obj X) (Y := (DerivedCategory.singleFunctor B n).obj _)
    let H := DerivedCategory.homologyFunctor B n
    let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso B n
    change H.map (T.map f ≫ _) = H.map (_ ≫ _)
    apply (cancel_mono (ε.hom.app (H.obj (T.obj Y)))).mp
    simp only [Functor.map_comp, Category.assoc]
    have hX : H.map (pureHomologyIso (T.obj X) n).hom ≫
        ε.hom.app (H.obj (T.obj X)) = 𝟙 _ := pureHomologyIso_normalization _ _
    have hY : H.map (pureHomologyIso (T.obj Y) n).hom ≫
        ε.hom.app (H.obj (T.obj Y)) = 𝟙 _ := pureHomologyIso_normalization _ _
    rw [hY, Category.comp_id]
    change H.map (T.map f) = H.map (pureHomologyIso (T.obj X) n).hom ≫
      (DerivedCategory.singleFunctor B n ⋙ H).map (H.map (T.map f)) ≫
        ε.hom.app (H.obj (T.obj Y))
    rw [ε.hom.naturality, Functor.id_map, ← Category.assoc, hX, Category.id_comp])



lemma homology_truncGEπ_isIso (Y : DerivedCategory.Plus B) (a q : ℤ) (hq : a ≤ q) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B q).map
      ((DerivedCategory.Plus.TStructure.t.truncGEπ a).app Y)) := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let T := (t.triangleLEGE (a-1) a (by omega)).obj Y
  have ht : T ∈ distTriang (DerivedCategory.Plus B) :=
    t.triangleLEGE_distinguished (a-1) a (by omega) Y
  have hz : IsZero ((H.shift q).obj T.obj₁) := by
    change IsZero ((DerivedCategory.Plus.homologyFunctor B q).obj ((t.truncLE (a-1)).obj Y))
    exact DerivedCategory.Plus.isZero_homology_of_isLE _ (a-1) _ (by omega)
  have hz' : IsZero ((H.shift (q+1)).obj T.obj₁) := by
    change IsZero ((DerivedCategory.Plus.homologyFunctor B (q+1)).obj ((t.truncLE (a-1)).obj Y))
    exact DerivedCategory.Plus.isZero_homology_of_isLE _ (a-1) _ (by omega)
  haveI : Mono ((H.shift q).map T.mor₂) :=
    (H.homologySequence_mono_shift_map_mor₂_iff T ht q).2 (hz.eq_of_src _ _)
  haveI : Epi ((H.shift q).map T.mor₂) :=
    (H.homologySequence_epi_shift_map_mor₂_iff T ht q (q+1) rfl).2
      (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift q).map T.mor₂)

lemma point_homology_truncLEι_isIso (Y : DerivedCategory.Plus B) (a q : ℤ) (hq : q ≤ a) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B q).map
      ((DerivedCategory.Plus.TStructure.t.truncLEι a).app Y)) := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let T := (t.triangleLEGE a (a+1) rfl).obj Y
  have ht : T ∈ distTriang (DerivedCategory.Plus B) := t.triangleLEGE_distinguished a (a+1) rfl Y
  have hz : IsZero ((H.shift q).obj T.obj₃) := by
    change IsZero ((DerivedCategory.Plus.homologyFunctor B q).obj ((t.truncGE (a+1)).obj Y))
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ (a+1) _ (by omega)
  have hz' : IsZero ((H.shift (q-1)).obj T.obj₃) := by
    change IsZero ((DerivedCategory.Plus.homologyFunctor B (q-1)).obj ((t.truncGE (a+1)).obj Y))
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ (a+1) _ (by omega)
  haveI : Epi ((H.shift q).map T.mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff T ht q).2 (hz.eq_of_tgt _ _)
  haveI : Mono ((H.shift q).map T.mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff T ht (q-1) q (by omega)).2
      (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((H.shift q).map T.mor₁)


def pointTruncation (n : ℤ) : DerivedCategory.Plus B ⥤ DerivedCategory.Plus B :=
  DerivedCategory.Plus.TStructure.t.truncLE n ⋙ DerivedCategory.Plus.TStructure.t.truncGE n

def pointTruncationPureIso (n : ℤ) :
    pointTruncation (B := B) n ≅ pointTruncation (B := B) n ⋙
      DerivedCategory.Plus.homologyFunctor B n ⋙ DerivedCategory.Plus.singleFunctor B n := by
  let T := pointTruncation (B := B) n
  let T' := T ⋙ DerivedCategory.Plus.ι
  haveI (Y : DerivedCategory.Plus B) : (T'.obj Y).IsGE n := by
    change (DerivedCategory.Plus.ι.obj (T.obj Y)).IsGE n
    haveI : (T.obj Y).IsGE n := by dsimp [T, pointTruncation]; infer_instance
    infer_instance
  haveI (Y : DerivedCategory.Plus B) : (T'.obj Y).IsLE n := by
    change (DerivedCategory.Plus.ι.obj (T.obj Y)).IsLE n
    haveI : (T.obj Y).IsLE n := by dsimp [T, pointTruncation]; infer_instance
    infer_instance
  apply ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight
    (DerivedCategory.Plus B)).preimageIso
  exact pureFunctorIso T' n

lemma pointTruncationPureIso_normalization (n : ℤ) (Y : DerivedCategory.Plus B) :
    (DerivedCategory.Plus.homologyFunctor B n).map
      ((pointTruncationPureIso (B := B) n).hom.app Y) ≫
      (singlePlusHomologyIso (B := B) n).hom.app
        ((DerivedCategory.Plus.homologyFunctor B n).obj ((pointTruncation n).obj Y)) = 𝟙 _ := by
  let T := pointTruncation (B := B) n
  let T' := T ⋙ DerivedCategory.Plus.ι
  haveI (Y : DerivedCategory.Plus B) : (T'.obj Y).IsGE n := by
    change (DerivedCategory.Plus.ι.obj (T.obj Y)).IsGE n
    haveI : (T.obj Y).IsGE n := by dsimp [T, pointTruncation]; infer_instance
    infer_instance
  haveI (Y : DerivedCategory.Plus B) : (T'.obj Y).IsLE n := by
    change (DerivedCategory.Plus.ι.obj (T.obj Y)).IsLE n
    haveI : (T.obj Y).IsLE n := by dsimp [T, pointTruncation]; infer_instance
    infer_instance
  have he : whiskerRight (pointTruncationPureIso (B := B) n).hom DerivedCategory.Plus.ι =
      (pureFunctorIso T' n).hom :=
    ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight
      (DerivedCategory.Plus B)).map_preimage _
  have heY := congrArg (fun α => α.app Y) he
  change (DerivedCategory.homologyFunctor B n).map
    (DerivedCategory.Plus.ι.map ((pointTruncationPureIso (B := B) n).hom.app Y)) ≫ _ = _
  change DerivedCategory.Plus.ι.map ((pointTruncationPureIso (B := B) n).hom.app Y) =
    (pureHomologyIso (T'.obj Y) n).hom at heY
  rw [heY]
  exact pureHomologyIso_normalization (T'.obj Y) n

def pointTruncationHomologyIso (n : ℤ) :
    pointTruncation (B := B) n ⋙ DerivedCategory.Plus.homologyFunctor B n ≅
      DerivedCategory.Plus.homologyFunctor B n := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let H := DerivedCategory.Plus.homologyFunctor B n
  let α := whiskerRight (whiskerLeft (t.truncLE n) (t.truncGEπ n)) H
  let β := whiskerRight (t.truncLEι n) H
  haveI (Y : DerivedCategory.Plus B) : IsIso (α.app Y) :=
    homology_truncGEπ_isIso _ n n (by omega)
  haveI (Y : DerivedCategory.Plus B) : IsIso (β.app Y) :=
    point_homology_truncLEι_isIso _ n n (by omega)
  haveI : IsIso α := NatIso.isIso_of_isIso_app _
  haveI : IsIso β := NatIso.isIso_of_isIso_app _
  exact (asIso α).symm ≪≫ asIso β

def pointTruncationIso (n : ℤ) :
    pointTruncation (B := B) n ≅
      DerivedCategory.Plus.homologyFunctor B n ⋙ DerivedCategory.Plus.singleFunctor B n :=
  pointTruncationPureIso n ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (pointTruncationHomologyIso (B := B) n)
      (DerivedCategory.Plus.singleFunctor B n)

lemma pointTruncationIso_normalization (n : ℤ) (Y : DerivedCategory.Plus B) :
    (DerivedCategory.Plus.homologyFunctor B n).map
      ((pointTruncationIso (B := B) n).hom.app Y) ≫
      (singlePlusHomologyIso (B := B) n).hom.app
        ((DerivedCategory.Plus.homologyFunctor B n).obj Y) =
      (pointTruncationHomologyIso (B := B) n).hom.app Y := by
  let H := DerivedCategory.Plus.homologyFunctor B n
  let S := DerivedCategory.Plus.singleFunctor B n
  let ε := singlePlusHomologyIso (B := B) n
  let θ := (pointTruncationPureIso (B := B) n).app Y
  let k := (pointTruncationHomologyIso (B := B) n).app Y
  have hθ : H.map θ.hom ≫ ε.hom.app (H.obj ((pointTruncation n).obj Y)) = 𝟙 _ :=
    pointTruncationPureIso_normalization n Y
  simp only [pointTruncationIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, associator_inv_app, Category.id_comp, Category.comp_id]
  change H.map (θ.hom ≫ S.map k.hom) ≫ ε.hom.app (H.obj Y) = k.hom
  rw [Functor.map_comp, Category.assoc]
  change H.map θ.hom ≫ (S ⋙ H).map k.hom ≫ ε.hom.app (H.obj Y) = _
  rw [ε.hom.naturality, Functor.id_map, ← Category.assoc, hθ, Category.id_comp]


def truncationToSingle (n : ℤ) :
    DerivedCategory.Plus.TStructure.t.truncLE n ⟶
      DerivedCategory.Plus.homologyFunctor B n ⋙ DerivedCategory.Plus.singleFunctor B n :=
  whiskerLeft (DerivedCategory.Plus.TStructure.t.truncLE n)
    (DerivedCategory.Plus.TStructure.t.truncGEπ n) ≫ (pointTruncationIso n).hom


lemma truncationToSingle_normalization (n : ℤ) (Y : DerivedCategory.Plus B) :
    (DerivedCategory.Plus.homologyFunctor B n).map
      ((truncationToSingle (B := B) n).app Y) ≫
      (singlePlusHomologyIso (B := B) n).hom.app
        ((DerivedCategory.Plus.homologyFunctor B n).obj Y) =
      (DerivedCategory.Plus.homologyFunctor B n).map
        ((DerivedCategory.Plus.TStructure.t.truncLEι n).app Y) := by
  let H := DerivedCategory.Plus.homologyFunctor B n
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  change H.map ((t.truncGEπ n).app ((t.truncLE n).obj Y) ≫
      (pointTruncationIso n).hom.app Y) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, pointTruncationIso_normalization]
  haveI := homology_truncGEπ_isIso ((t.truncLE n).obj Y) n n (by omega)
  simp only [pointTruncationHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, NatTrans.comp_app, NatIso.isIso_inv_app, whiskerRight_app, whiskerLeft_app]
  change H.map ((t.truncGEπ n).app ((t.truncLE n).obj Y)) ≫
    (inv (H.map ((t.truncGEπ n).app ((t.truncLE n).obj Y))) ≫
      H.map ((t.truncLEι n).app Y)) = _
  simp
  rfl


open AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
def canonicalRightZeroIso [PreservesFiniteLimits G] : rightValue G 0 ≅ G :=
  (degreeZeroIso G).symm

def rightDerivedStalkHomologyIso [PreservesFiniteLimits G] (n : ℤ) :
    DerivedCategory.Plus.singleFunctor B n ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor C n ≅ G :=
  shiftedStalkValueIso G n ≪≫ canonicalRightZeroIso G

/-- The degree-`n` truncation span, with its canonical cohomology normalizations. -/
def columnTruncation (n : ℤ) : ColumnTruncation G n where
  lower := homology_rightDerived_truncLEIso G n
  lower_hom := rfl
  point := pointTruncationIso n
  point_normalization := truncationToSingle_normalization n

/-- The natural second derived edge, obtained from the canonical truncation span. -/
def derivedTruncationEdge [PreservesFiniteLimits G] (n : ℤ) :
    G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n ⟶
      DerivedCategory.Plus.homologyFunctor B n ⋙ G :=
  (homology_rightDerived_truncLEIso G n).inv ≫
    whiskerRight (truncationToSingle n)
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n) ≫
    (associator _ _ _).hom ≫
    (isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor B n)
      (rightDerivedStalkHomologyIso G n)).hom


variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]
open GrothendieckSpectralSequence

/-- The object-case second edge, using the canonical composition comparison. -/
def derivedSecondEdge [PreservesFiniteLimits G] (n : ℕ) :
    rightValue (F ⋙ G) n ⟶ rightValue F n ⋙ G :=
  classicalColumn F G (columnTruncation G (n : ℤ)) (canonicalRightZeroIso G)

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05Truncation

noncomputable section G05FilteredEdges

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.G05FilteredEdges
open HypercohomologyDerivedNaturality GrothendieckSpectralSequence
open FiniteFiltrationConvergence CartanEilenbergData

variable {C : Type u'} [Category.{v'} C] [Abelian C]

lemma exact_conjugate {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (hfg : f ≫ g = 0)
    (he : (ShortComplex.mk f g hfg).Exact) :
    ∀ hzero : (e₁.hom ≫ f ≫ e₂.inv) ≫ (e₂.hom ≫ g ≫ e₃.inv) = 0,
      (ShortComplex.mk (e₁.hom ≫ f ≫ e₂.inv) (e₂.hom ≫ g ≫ e₃.inv) hzero).Exact := by
  intro hzero
  let e : ShortComplex.mk (e₁.hom ≫ f ≫ e₂.inv) (e₂.hom ≫ g ≫ e₃.inv) hzero ≅
      ShortComplex.mk f g hfg :=
    ShortComplex.isoMk e₁ e₂ e₃ (by simp) (by simp)
  exact (ShortComplex.exact_iff_of_iso e).mpr he

def transport {X Y : RowDiagram C} (e : X ≅ Y) (E : EdgeData Y) : EdgeData X where
  row n := e.hom.page 0 n n ≫ E.row n ≫ e.inv.target n
  column n := e.hom.target n ≫ E.column n ≫ e.inv.page 0 0 n

lemma differential_conjugate {X Y : RowDiagram C} (e : X ≅ Y) :
    transgression X = e.hom.page 0 0 1 ≫ transgression Y ≫ e.inv.page 0 2 2 := by
  have h := e.hom.differential_comm 0 0 1
  change e.hom.page 0 0 1 ≫ transgression Y = transgression X ≫ e.hom.page 0 2 2 at h
  rw [← Category.assoc, h, Category.assoc]
  have hi : e.hom.page 0 2 2 ≫ e.inv.page 0 2 2 = 𝟙 _ :=
    congrArg (fun f : X ⟶ X => f.page 0 2 2) e.hom_inv_id
  rw [hi, Category.comp_id]

theorem transport_fiveTerms {X Y : RowDiagram C} (e : X ≅ Y) (E : EdgeData Y)
    (hE : FiveTermData E) : FiveTermData (transport e E) := by
  let ep (p n : ℤ) := (pageEval 0 p n).mapIso e
  let et (n : ℤ) := (targetEval n).mapIso e
  have hd : transgression X = (ep 0 1).hom ≫ transgression Y ≫ (ep 2 2).inv :=
    differential_conjugate e
  change FiveTermData (⟨(fun n => (ep n n).hom ≫ E.row n ≫ (et n).inv),
    (fun n => (et n).hom ≫ E.column n ≫ (ep 0 n).inv)⟩ : EdgeData X)
  haveI := hE.row_mono
  have hrc : ((ep 1 1).hom ≫ E.row 1 ≫ (et 1).inv) ≫
      ((et 1).hom ≫ E.column 1 ≫ (ep 0 1).inv) = 0 := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (E.row 1) (E.column 1), hE.row_column, zero_comp, comp_zero]
  have hcd : ((et 1).hom ≫ E.column 1 ≫ (ep 0 1).inv) ≫ transgression X = 0 := by
    rw [hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (E.column 1) (transgression Y), hE.column_d, zero_comp, comp_zero]
  have hdr : transgression X ≫ ((ep 2 2).hom ≫ E.row 2 ≫ (et 2).inv) = 0 := by
    rw [hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (transgression Y) (E.row 2), hE.d_row, zero_comp, comp_zero]
  refine {
    row_mono := ?_
    row_column := hrc
    column_d := hcd
    d_row := hdr
    exact_H1 := ?_
    exact_E01 := ?_
    exact_E20 := ?_ }
  · change Mono (_ ≫ E.row 1 ≫ _)
    infer_instance
  · exact exact_conjugate (ep 1 1) (et 1) (ep 0 1) _ _ hE.row_column hE.exact_H1 hrc
  · change (ShortComplex.mk ((et 1).hom ≫ E.column 1 ≫ (ep 0 1).inv) (transgression X) hcd).Exact
    have hz := hcd
    rw [hd] at hz
    simpa only [hd] using exact_conjugate (et 1) (ep 0 1) (ep 2 2) _ _ hE.column_d hE.exact_E01 hz
  · change (ShortComplex.mk (transgression X) ((ep 2 2).hom ≫ E.row 2 ≫ (et 2).inv) hdr).Exact
    have hz := hdr
    rw [hd] at hz
    simpa only [hd] using exact_conjugate (ep 0 1) (ep 2 2) (et 2) _ _ hE.d_row hE.exact_E20 hz

lemma EdgeMap.comp {X Y Z : RowDiagram C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {E : EdgeData X} {E' : EdgeData Y} {E'' : EdgeData Z}
    (hf : EdgeMap f E E') (hg : EdgeMap g E' E'') : EdgeMap (f ≫ g) E E'' := by
  constructor
  · intro n
    change (f.page 0 n n ≫ g.page 0 n n) ≫ E''.row n = E.row n ≫ (f.target n ≫ g.target n)
    rw [Category.assoc, hg.row n, ← Category.assoc, hf.row n, Category.assoc]
  · intro n
    change (f.target n ≫ g.target n) ≫ E''.column n = E.column n ≫ (f.page 0 0 n ≫ g.page 0 0 n)
    rw [Category.assoc, hg.column n, ← Category.assoc, hf.column n, Category.assoc]

lemma EdgeMap.inv {X Y : RowDiagram C} (e : X ≅ Y) {E : EdgeData X} {E' : EdgeData Y}
    (h : EdgeMap e.hom E E') : EdgeMap e.inv E' E := by
  constructor
  · intro n
    let ep := (pageEval 0 n n).mapIso e
    let et := (targetEval n).mapIso e
    have hn := congrArg (fun k => ep.inv ≫ k ≫ et.inv) (h.row n)
    change ep.inv ≫ E.row n = E'.row n ≫ et.inv
    change ep.inv ≫ (ep.hom ≫ E'.row n) ≫ et.inv = ep.inv ≫ (E.row n ≫ et.hom) ≫ et.inv at hn
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using hn.symm
  · intro n
    let ep := (pageEval 0 0 n).mapIso e
    let et := (targetEval n).mapIso e
    have hn := congrArg (fun k => et.inv ≫ k ≫ ep.inv) (h.column n)
    change et.inv ≫ E.column n = E'.column n ≫ ep.inv
    change et.inv ≫ (et.hom ≫ E'.column n) ≫ ep.inv = et.inv ≫ (E.column n ≫ ep.hom) ≫ ep.inv at hn
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using hn.symm

/-- Transport preserves naturality whenever the conjugated map preserves the original edges. -/
lemma EdgeMap.transport {X Y X' Y' : RowDiagram C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) {E : EdgeData X'} {E' : EdgeData Y'}
    (h : EdgeMap (eX.inv ≫ f ≫ eY.hom) E E') :
    EdgeMap f (transport eX E) (transport eY E') := by
  constructor
  · intro n
    let epX := (pageEval 0 n n).mapIso eX
    let etX := (targetEval n).mapIso eX
    let epY := (pageEval 0 n n).mapIso eY
    let etY := (targetEval n).mapIso eY
    have hn := congrArg (fun k => epX.hom ≫ k ≫ etY.inv) (h.row n)
    change epX.hom ≫ ((epX.inv ≫ f.page 0 n n ≫ epY.hom) ≫ E'.row n) ≫ etY.inv =
      epX.hom ≫ (E.row n ≫ (etX.inv ≫ f.target n ≫ etY.hom)) ≫ etY.inv at hn
    change f.page 0 n n ≫ (epY.hom ≫ E'.row n ≫ etY.inv) =
      (epX.hom ≫ E.row n ≫ etX.inv) ≫ f.target n
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hn
  · intro n
    let epX := (pageEval 0 0 n).mapIso eX
    let etX := (targetEval n).mapIso eX
    let epY := (pageEval 0 0 n).mapIso eY
    let etY := (targetEval n).mapIso eY
    have hn := congrArg (fun k => etX.hom ≫ k ≫ epY.inv) (h.column n)
    change etX.hom ≫ ((etX.inv ≫ f.target n ≫ etY.hom) ≫ E'.column n) ≫ epY.inv =
      etX.hom ≫ (E.column n ≫ (epX.inv ≫ f.page 0 0 n ≫ epY.hom)) ≫ epY.inv at hn
    change f.target n ≫ (etY.hom ≫ E'.column n ≫ epY.inv) =
      (etX.hom ≫ E.column n ≫ epX.inv) ≫ f.page 0 0 n
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hn

lemma transport_trans {X Y Z : RowDiagram C} (e : X ≅ Y) (e' : Y ≅ Z) (E : EdgeData Z) :
    transport (e ≪≫ e') E = transport e (transport e' E) := by
  apply EdgeData.ext
  · funext n
    change (e.hom.page 0 n n ≫ e'.hom.page 0 n n) ≫ E.row n ≫
      (e'.inv.target n ≫ e.inv.target n) =
      e.hom.page 0 n n ≫ (e'.hom.page 0 n n ≫ E.row n ≫ e'.inv.target n) ≫ e.inv.target n
    simp only [Category.assoc]
  · funext n
    change (e.hom.target n ≫ e'.hom.target n) ≫ E.column n ≫
      (e'.inv.page 0 0 n ≫ e.inv.page 0 0 n) =
      e.hom.target n ≫ (e'.hom.target n ≫ E.column n ≫ e'.inv.page 0 0 n) ≫ e.inv.page 0 0 n
    simp only [Category.assoc]

lemma conjugate_eq_of_heq {X Y X' Y' : RowDiagram C} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    (eqToIso hX).inv ≫ f ≫ (eqToIso hY).hom = g := by
  subst X'; subst Y'
  cases h
  simp

section Models
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C] [EnoughInjectives A]
  (G : A ⥤ C) [G.Additive]
  {K : CochainComplex.Plus A} {R : ResolutionData K.obj} (M : Data G K R)

abbrev modelEdges (hQ : EdgesAndFiveTerms.FirstQuadrant M.filtration M.pages) :
    EdgesAndFiveTerms.EdgeData M.filtration M.pages :=
  EdgesAndFiveTerms.edgeData M.filtration M.pages M.convergence.finite hQ

def modelDiagramEdges (hQ : EdgesAndFiveTerms.FirstQuadrant M.filtration M.pages) :
    EdgeData (diagram G M) where
  row n := (modelEdges G M hQ).row n (by omega) ≫ (M.targetIso n).hom
  column n := (M.targetIso n).inv ≫ (modelEdges G M hQ).column n (by omega)

theorem modelDiagram_fiveTerms
    (hQ : EdgesAndFiveTerms.FirstQuadrant M.filtration M.pages) :
    FiveTermData (modelDiagramEdges G M hQ) := by
  let E := modelEdges G M hQ
  have hE := EdgesAndFiveTerms.fiveTermData M.filtration M.pages M.convergence.finite hQ E
  haveI := hE.row_mono
  have hrc : (E.row 1 (by omega) ≫ (M.targetIso 1).hom) ≫
      ((M.targetIso 1).inv ≫ E.column 1 (by omega)) = 0 := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hE.row_column]
  have hcd : ((M.targetIso 1).inv ≫ E.column 1 (by omega)) ≫
      EdgesAndFiveTerms.transgression M.filtration M.pages = 0 := by
    rw [Category.assoc, hE.column_d, comp_zero]
  have hdr : EdgesAndFiveTerms.transgression M.filtration M.pages ≫
      (E.row 2 (by omega) ≫ (M.targetIso 2).hom) = 0 := by
    rw [← Category.assoc, hE.d_row, zero_comp]
  refine {
    row_mono := ?_
    row_column := hrc
    column_d := hcd
    d_row := hdr
    exact_H1 := ?_
    exact_E01 := ?_
    exact_E20 := ?_ }
  · change Mono (E.row 1 (by omega) ≫ _)
    infer_instance
  · change (ShortComplex.mk (E.row 1 (by omega) ≫ (M.targetIso 1).hom)
        ((M.targetIso 1).inv ≫ E.column 1 (by omega)) hrc).Exact
    simpa only [Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv, Category.id_comp, Category.comp_id] using
      exact_conjugate (Iso.refl _) (M.targetIso 1).symm (Iso.refl _)
        _ _ hE.row_column hE.exact_H1 (by simpa using hrc)
  · change (ShortComplex.mk ((M.targetIso 1).inv ≫ E.column 1 (by omega))
        (EdgesAndFiveTerms.transgression M.filtration M.pages) hcd).Exact
    simpa only [Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv, Category.id_comp, Category.comp_id] using
      exact_conjugate (M.targetIso 1).symm (Iso.refl _) (Iso.refl _)
        _ _ hE.column_d hE.exact_E01 (by simpa using hcd)
  · change (ShortComplex.mk (EdgesAndFiveTerms.transgression M.filtration M.pages)
        (E.row 2 (by omega) ≫ (M.targetIso 2).hom) hdr).Exact
    simpa only [Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv, Category.id_comp, Category.comp_id] using
      exact_conjugate (Iso.refl _) (Iso.refl _) (M.targetIso 2).symm
        _ _ hE.d_row hE.exact_E20 (by simpa using hdr)


lemma firstQuadrant_of_iso {X Y : RowDiagram C} (e : X ≅ Y) (h : FirstQuadrant X) : FirstQuadrant Y := by
  intro p n hp
  exact IsZero.of_iso (h p n hp) ((pageEval 0 p n).mapIso e).symm

def realizedQuadrant {X : RowDiagram C} (e : X ≅ diagram G M) (hQ : FirstQuadrant X) :
    EdgesAndFiveTerms.FirstQuadrant M.filtration M.pages := by
  intro p n hp
  change IsZero ((diagram G M).page 0 p n)
  exact IsZero.of_iso (hQ p n hp) ((pageEval 0 p n).mapIso e).symm

/-- Edges transported from the actual filtration using a simultaneous diagram realization. -/
def realizedEdges {X : RowDiagram C} (e : X ≅ diagram G M) (hQ : FirstQuadrant X) :
    EdgeData X :=
  transport e (modelDiagramEdges G M (realizedQuadrant G M e hQ))

theorem realized_fiveTerms {X : RowDiagram C} (e : X ≅ diagram G M) (hQ : FirstQuadrant X) :
    FiveTermData (realizedEdges G M e hQ) :=
  transport_fiveTerms e _ (modelDiagram_fiveTerms G M (realizedQuadrant G M e hQ))


/-- The row-edge representative equation after simultaneous diagram transport. -/
theorem realized_row_formula {X : RowDiagram C} (e : X ≅ diagram G M)
    (hQ : FirstQuadrant X) (n : ℕ) :
    (closedToPage M.filtration M.pages 2 (n : ℤ) (n : ℤ) ≫ e.inv.page 0 n n) ≫
        (realizedEdges G M e hQ).row n =
      EdgesAndFiveTerms.ambientClass M.filtration n n ≫ (M.targetIso n).hom ≫ e.inv.target n := by
  let ep := (pageEval 0 n n).mapIso e
  dsimp only [realizedEdges, transport, modelDiagramEdges]
  simp only [Category.assoc]
  change closedToPage M.filtration M.pages 2 n n ≫ ep.inv ≫ ep.hom ≫
      (modelEdges G M (realizedQuadrant G M e hQ)).row n (by omega) ≫
        (M.targetIso n).hom ≫ e.inv.target n = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (closedToPage M.filtration M.pages 2 n n)
    ((modelEdges G M (realizedQuadrant G M e hQ)).row n (by omega)),
    (modelEdges G M (realizedQuadrant G M e hQ)).row_formula]
  simp only [EdgesAndFiveTerms.ambientClass, Category.assoc]

/-- The column-edge representative equation after simultaneous diagram transport. -/
theorem realized_column_formula {X : RowDiagram C} (e : X ≅ diagram G M)
    (hQ : FirstQuadrant X) (n : ℕ) :
    ((EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom) ≫
        e.inv.target n) ≫ (realizedEdges G M e hQ).column n =
      closedToPage M.filtration M.pages 2 0 n ≫ e.inv.page 0 0 n := by
  let et := (targetEval n).mapIso e
  dsimp only [realizedEdges, transport, modelDiagramEdges]
  simp only [Category.assoc]
  change closedClass M.filtration 0 n ≫ (cohomologyPiece M.filtration 0 n).arrow ≫
      (M.targetIso n).hom ≫ et.inv ≫
      et.hom ≫ (M.targetIso n).inv ≫
        (modelEdges G M (realizedQuadrant G M e hQ)).column n (by omega) ≫ e.inv.page 0 0 n = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (closedClass M.filtration 0 n) (cohomologyPiece M.filtration 0 n).arrow]
  rw [← Category.assoc (EdgesAndFiveTerms.ambientClass M.filtration 0 n)
    ((modelEdges G M (realizedQuadrant G M e hQ)).column n (by omega)),
    (modelEdges G M (realizedQuadrant G M e hQ)).column_formula]


section ModelNaturality
variable (S : System G) {L : CochainComplex.Plus A}
  {U : ResolutionData L.obj} (f : K ⟶ L) (a : R.bicomplex ⟶ U.bicomplex)
  (ha : CartanEilenbergComparison.IsLift R U f.hom a)
  (hK : EdgesAndFiveTerms.FirstQuadrant (S.data K R).filtration (S.data K R).pages)
  (hL : EdgesAndFiveTerms.FirstQuadrant (S.data L U).filtration (S.data L U).pages)

lemma modelDiagram_row_naturality (n : ℕ) :
    (diagramMap G S f a ha).page 0 n n ≫ (modelDiagramEdges G (S.data L U) hL).row n =
      (modelDiagramEdges G (S.data K R) hK).row n ≫ (diagramMap G S f a ha).target n := by
  let E := modelEdges G (S.data K R) hK
  let E' := modelEdges G (S.data L U) hL
  have hp := EdgesAndFiveTerms.row_naturality (S.lift R U a).filtered
    (S.data K R).pages (S.data L U).pages (S.lift R U a).maps
    (S.data K R).convergence.finite hK E E' (n : ℤ) (by omega)
  change (S.lift R U a).maps.map 2 n n ≫ (E'.row n (by omega) ≫ ((S.data L U).targetIso n).hom) =
    (E.row n (by omega) ≫ ((S.data K R).targetIso n).hom) ≫ targetMap G f n
  rw [← Category.assoc, hp, Category.assoc, S.target_naturality R U f a ha n, Category.assoc]

lemma modelDiagram_column_naturality (n : ℕ) :
    (diagramMap G S f a ha).target n ≫ (modelDiagramEdges G (S.data L U) hL).column n =
      (modelDiagramEdges G (S.data K R) hK).column n ≫ (diagramMap G S f a ha).page 0 0 n := by
  let E := modelEdges G (S.data K R) hK
  let E' := modelEdges G (S.data L U) hL
  have hp := EdgesAndFiveTerms.column_naturality (S.lift R U a).filtered
    (S.data K R).pages (S.data L U).pages (S.lift R U a).maps
    (S.data K R).convergence.finite hK E E' (n : ℤ) (by omega)
  have ht : targetMap G f n ≫ ((S.data L U).targetIso n).inv =
      ((S.data K R).targetIso n).inv ≫ HomologicalComplex.homologyMap (S.lift R U a).filtered.hom n := by
    apply (cancel_epi ((S.data K R).targetIso n).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id_assoc]
    rw [← S.target_naturality R U f a ha n]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  change targetMap G f n ≫ (((S.data L U).targetIso n).inv ≫ E'.column n (by omega)) =
    (((S.data K R).targetIso n).inv ≫ E.column n (by omega)) ≫ (S.lift R U a).maps.map 2 0 n
  rw [← Category.assoc, ht, Category.assoc, hp, Category.assoc]

end ModelNaturality

end Models

section Derived
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C] [EnoughInjectives A]
  (G : A ⥤ C) [G.Additive] (R : DerivedRow G)

/-- The complex-level edges, with the supplied equality to the actual diagram. -/
def complexEdges (K : CochainComplex.Plus A) (hQ : FirstQuadrant (R.complexes.obj K)) :
    EdgeData (R.complexes.obj K) :=
  realizedEdges G (R.system.data K (R.resolution K)) (eqToIso (R.obj_eq K)) hQ

lemma complex_edges_naturality {K L : CochainComplex.Plus A} (f : K ⟶ L)
    (hK : FirstQuadrant (R.complexes.obj K)) (hL : FirstQuadrant (R.complexes.obj L)) :
    EdgeMap (R.complexes.map f) (complexEdges G R K hK) (complexEdges G R L hL) := by
  obtain ⟨a,ha,heq⟩ := R.map_eq f
  change EdgeMap (R.complexes.map f)
    (transport (eqToIso (R.obj_eq K)) _)
    (transport (eqToIso (R.obj_eq L)) _)
  apply EdgeMap.transport
  rw [conjugate_eq_of_heq (R.obj_eq K) (R.obj_eq L) _ _ heq]
  exact ⟨modelDiagram_row_naturality G R.system f a ha _ _,
    modelDiagram_column_naturality G R.system f a ha _ _⟩

/-- Complex-level edges transferred across the localization factorization. -/
def qEdges (K : CochainComplex.Plus A)
    (hQ : FirstQuadrant (R.derived.obj (DerivedCategory.Plus.Q.obj K))) :
    EdgeData (R.derived.obj (DerivedCategory.Plus.Q.obj K)) :=
  transport (R.factors.app K)
    (complexEdges G R K (firstQuadrant_of_iso (R.factors.app K) hQ))

lemma q_edges_map_naturality {K L : CochainComplex.Plus A} (f : K ⟶ L)
    (hK : FirstQuadrant (R.derived.obj (DerivedCategory.Plus.Q.obj K)))
    (hL : FirstQuadrant (R.derived.obj (DerivedCategory.Plus.Q.obj L))) :
    EdgeMap (R.derived.map (DerivedCategory.Plus.Q.map f))
      (qEdges G R K hK) (qEdges G R L hL) := by
  change EdgeMap _ (transport (R.factors.app K) _) (transport (R.factors.app L) _)
  apply EdgeMap.transport
  have hnat := R.factors.hom.naturality f
  change R.derived.map (DerivedCategory.Plus.Q.map f) ≫ (R.factors.app L).hom =
    (R.factors.app K).hom ≫ R.complexes.map f at hnat
  have hc : (R.factors.app K).inv ≫ R.derived.map (DerivedCategory.Plus.Q.map f) ≫
      (R.factors.app L).hom = R.complexes.map f := by
    rw [hnat, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hc]
  exact complex_edges_naturality G R f _ _

/-- Fractions between bounded-below complex presentations remain bounded below. -/
lemma plus_left_fac {K L : CochainComplex.Plus A}
    (f : DerivedCategory.Plus.Q.obj K ⟶ DerivedCategory.Plus.Q.obj L) :
    ∃ (T : CochainComplex.Plus A) (g : K ⟶ T) (s : L ⟶ T)
      (_ : IsIso (DerivedCategory.Plus.Q.map s)),
      f = DerivedCategory.Plus.Q.map g ≫ inv (DerivedCategory.Plus.Q.map s) := by
  obtain ⟨b,hb⟩ := L.property
  haveI : L.obj.IsStrictlyGE b := hb
  obtain ⟨T,hT,g,s,hs,hfac⟩ := DerivedCategory.left_fac_of_isStrictlyGE (X := K.obj) (Y := L.obj) f.hom b
  letI := hT
  letI := hs
  let TT : CochainComplex.Plus A := ⟨T,b,hT⟩
  let gg : K ⟶ TT := (CochainComplex.plus A).homMk g
  let ss : L ⟶ TT := (CochainComplex.plus A).homMk s
  haveI : IsIso ((DerivedCategory.Plus.ι (C := A)).map (DerivedCategory.Plus.Q.map ss)) := by
    change IsIso (DerivedCategory.Q.map s)
    exact hs
  have hiso : IsIso (DerivedCategory.Plus.Q.map ss) :=
    isIso_of_fully_faithful (DerivedCategory.Plus.ι (C := A)) _
  letI := hiso
  refine ⟨TT,gg,ss,hiso,?_⟩
  apply (DerivedCategory.Plus.ι (C := A)).map_injective
  rw [Functor.map_comp, Functor.map_inv]
  change f.hom = DerivedCategory.Q.map g ≫ inv (DerivedCategory.Q.map s)
  exact hfac

lemma q_edges_naturality {K L : CochainComplex.Plus A}
    (f : DerivedCategory.Plus.Q.obj K ⟶ DerivedCategory.Plus.Q.obj L)
    (hK : FirstQuadrant (R.derived.obj (DerivedCategory.Plus.Q.obj K)))
    (hL : FirstQuadrant (R.derived.obj (DerivedCategory.Plus.Q.obj L))) :
    EdgeMap (R.derived.map f) (qEdges G R K hK) (qEdges G R L hL) := by
  obtain ⟨T,g,s,hs,hfac⟩ := plus_left_fac f
  letI := hs
  let es := R.derived.mapIso (asIso (DerivedCategory.Plus.Q.map s))
  have hT : FirstQuadrant (R.derived.obj (DerivedCategory.Plus.Q.obj T)) :=
    firstQuadrant_of_iso es hL
  have hg := q_edges_map_naturality G R g hK hT
  have hss := q_edges_map_naturality G R s hL hT
  have hi := EdgeMap.inv es hss
  have hc := hg.comp hi
  rw [hfac, Functor.map_comp, Functor.map_inv]
  simpa only [es, Functor.mapIso_inv, asIso_inv, Functor.map_inv] using hc

/-- The actual S05 edges of a descended row sequence. -/
def derivedEdges (Y : DerivedCategory.Plus A) (hQ : FirstQuadrant (R.derived.obj Y)) :
    EdgeData (R.derived.obj Y) :=
  realizedEdges G _ (realization G R Y) hQ

theorem derived_fiveTerms (Y : DerivedCategory.Plus A) (hQ : FirstQuadrant (R.derived.obj Y)) :
    FiveTermData (derivedEdges G R Y hQ) :=
  realized_fiveTerms G _ (realization G R Y) hQ

local instance : (DerivedCategory.Plus.Q (C := A)).EssSurj :=
  Localization.essSurj _ (CochainComplex.Plus.quasiIso A)

lemma derivedEdges_eq (Y : DerivedCategory.Plus A) (hQ : FirstQuadrant (R.derived.obj Y)) :
    derivedEdges G R Y hQ =
      transport (R.derived.mapIso (DerivedCategory.Plus.Q.objObjPreimageIso Y).symm)
        (qEdges G R (DerivedCategory.Plus.Q.objPreimage Y)
          (firstQuadrant_of_iso
            (R.derived.mapIso (DerivedCategory.Plus.Q.objObjPreimageIso Y).symm) hQ)) := by
  simp only [derivedEdges, realizedEdges, realization, qEdges, complexEdges,
    DerivedRow.complexIso, transport_trans]

/-- Both actual filtered edges are natural for every derived morphism. -/
theorem derived_edges_naturality {Y Z : DerivedCategory.Plus A} (f : Y ⟶ Z)
    (hY : FirstQuadrant (R.derived.obj Y)) (hZ : FirstQuadrant (R.derived.obj Z)) :
    EdgeMap (R.derived.map f) (derivedEdges G R Y hY) (derivedEdges G R Z hZ) := by
  rw [derivedEdges_eq G R Y hY, derivedEdges_eq G R Z hZ]
  apply EdgeMap.transport
  let eY := DerivedCategory.Plus.Q.objObjPreimageIso Y
  let eZ := DerivedCategory.Plus.Q.objObjPreimageIso Z
  have hc : (R.derived.mapIso eY.symm).inv ≫ R.derived.map f ≫
      (R.derived.mapIso eZ.symm).hom = R.derived.map (eY.hom ≫ f ≫ eZ.inv) := by
    simp only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom,
      Functor.map_comp]
  rw [hc]
  exact q_edges_naturality G R (eY.hom ≫ f ≫ eZ.inv) _ _

/-- On a specified complex, the localization of the edges may be computed
using that complex's presentation of the row diagram. -/
lemma derivedEdges_q (K : CochainComplex.Plus A)
    (hQ : FirstQuadrant (R.derived.obj (DerivedCategory.Plus.Q.obj K))) :
    derivedEdges G R (DerivedCategory.Plus.Q.obj K) hQ =
      realizedEdges G _ (R.complexIso G K) hQ := by
  let Y := DerivedCategory.Plus.Q.obj K
  let e := DerivedCategory.Plus.Q.objObjPreimageIso Y
  have h := q_edges_naturality G R e.inv hQ
    (firstQuadrant_of_iso (R.derived.mapIso e.symm) hQ)
  rw [derivedEdges_eq]
  have hh : transport (R.derived.mapIso e.symm)
      (qEdges G R (DerivedCategory.Plus.Q.objPreimage Y)
        (firstQuadrant_of_iso (R.derived.mapIso e.symm) hQ)) =
      qEdges G R K hQ := by
    apply EdgeData.ext
    · funext n
      have hn := h.row n
      dsimp only [transport, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv]
      rw [reassoc_of% hn]
      change (qEdges G R K hQ).row n ≫
        ((targetEval (C := C) (n : ℤ)).map ((R.derived).map e.inv) ≫
          (targetEval (n : ℤ)).map ((R.derived).map e.hom)) = _
      simp [← Functor.map_comp]
      exact Category.comp_id _
    · funext n
      have hn := h.column n
      dsimp only [transport, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv]
      rw [reassoc_of% hn]
      change (qEdges G R K hQ).column n ≫
        ((pageEval (C := C) 0 0 (n : ℤ)).map ((R.derived).map e.inv) ≫
          (pageEval 0 0 (n : ℤ)).map ((R.derived).map e.hom)) = _
      simp [← Functor.map_comp]
      exact Category.comp_id _
  rw [hh]
  exact (transport_trans _ _ _).symm

end Derived

end AdvancedHomologicalAlgebra.G05FilteredEdges
end G05FilteredEdges

noncomputable section G05Collapse

set_option maxHeartbeats 300000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra.EdgesAndFiveTerms
open FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)

/-- Any vanishing E₂ term stays zero on all later pages. -/
theorem later_isZero_of_E2 (p n : ℤ) (h : IsZero (PageCohomology.object F D 2 p n))
    (r : ℤ) (hr : 2 ≤ r) : IsZero (PageCohomology.object F D r p n) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = 2+k := ⟨(r-2).toNat, by omega⟩
  clear hr
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
      next_isZero F D (2+(k : ℤ)) (by omega) p n ih

/-- An E₂ vanishing term has a zero limiting graded cohomology piece. -/
theorem gradedCohomology_isZero_of_E2 (hF : DegreewiseFinite F) (p n : ℤ)
    (h : IsZero (PageCohomology.object F D 2 p n)) :
    IsZero (gradedCohomology F p n) := by
  obtain ⟨R, hR, hs⟩ := uniform_stabilization F hF n
  let r := max 2 R
  exact (later_isZero_of_E2 F D p n h r (le_max_left _ _)).of_iso
    (limitIso F D r p n (hs r (le_max_right _ _) p)).iso.symm

/-- If every graded term below p is zero, Fᵖ is the full cohomology object. -/
theorem cohomologyPiece_eq_top_of_E2_zero_below (hF : DegreewiseFinite F) (p n : ℤ)
    (hZ : ∀ i : ℤ, i < p → IsZero (PageCohomology.object F D 2 i n)) :
    cohomologyPiece F p n = ⊤ := by
  obtain ⟨a, b, ha, hb⟩ := (cohomology_filtration F hF).finite n
  let a' := min a p
  have hbase : cohomologyPiece F a' n = ⊤ := ha a' (min_le_left _ _)
  have heq : ∀ k : ℕ, a'+k ≤ p →
      cohomologyPiece F (a'+k) n = cohomologyPiece F a' n := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hz := gradedCohomology_isZero_of_E2 F D hF (a'+k) n (hZ _ (by omega))
      have hh := cohomologyPiece_eq_of_graded_isZero F (a'+k) n hz
      rw [show (a'+(↑(k+1) : ℤ)) = (a'+k)+1 by omega, hh, ih (by omega)]
  have he : a'+(↑((p-a').toNat) : ℤ) = p := by dsimp [a']; omega
  have h := heq (p-a').toNat (by omega)
  rw [he, hbase] at h
  exact h

/-- If every graded term at or above p is zero, Fᵖ is zero. -/
theorem cohomologyPiece_eq_bot_of_E2_zero_above (hF : DegreewiseFinite F) (p n : ℤ)
    (hZ : ∀ i : ℤ, p ≤ i → IsZero (PageCohomology.object F D 2 i n)) :
    cohomologyPiece F p n = ⊥ := by
  obtain ⟨a, b, ha, hb⟩ := (cohomology_filtration F hF).finite n
  let b' := max b p
  have hbase : cohomologyPiece F b' n = ⊥ := hb b' (le_max_left _ _)
  have heq : ∀ k : ℕ, cohomologyPiece F (p+k) n = cohomologyPiece F p n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hz := gradedCohomology_isZero_of_E2 F D hF (p+k) n (hZ _ (by omega))
      have hh := cohomologyPiece_eq_of_graded_isZero F (p+k) n hz
      rw [show (p+(↑(k+1) : ℤ)) = (p+k)+1 by omega, hh, ih]
  have he : p+(↑((b'-p).toNat) : ℤ) = b' := by dsimp [b']; omega
  have h := heq (b'-p).toNat
  rw [he, hbase] at h
  exact h.symm

/-- The row edge is an isomorphism when E₂ is concentrated in row zero. -/
theorem row_edge_isIso_of_single_row_zero (hF : DegreewiseFinite F)
    (hQ : FirstQuadrant F D) (E : EdgeData F D)
    (hZ : ∀ p m : ℤ, m ≠ p → IsZero (PageCohomology.object F D 2 p m))
    (n : ℤ) (hn : 0 ≤ n) : IsIso (E.row n hn) := by
  let L := stationaryLimit F D hF 2 (by omega) n n
    (fun r hr => (later_isZero_of_E2 F D (n-r) (n-1)
      (hZ _ _ (by omega)) r hr).eq_of_src _ _)
    (fun r hr => row_differential_zero F D hQ r hr n)
  let π := cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F n n))
  haveI : IsIso π := cokernel.π_of_zero
    (ofLE_zero_of_eq_bot _ (cohomologyPiece_above_eq_bot F D hF hQ n))
  haveI : IsIso (cohomologyPiece F n n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2
      (cohomologyPiece_eq_top_of_E2_zero_below F D hF n n
        (fun p hp => hZ _ _ (by omega)))
  have hrow : E.row n hn = (L.iso.hom ≫ inv π) ≫ (cohomologyPiece F n n).arrow := by
    haveI := row_closedToPage_epi F D hF hQ n
    apply (cancel_epi (closedToPage F D 2 n n)).1
    rw [E.row_formula]
    symm
    simp only [Category.assoc]
    rw [reassoc_of% L.representative_formula]
    simp only [gradedClass, π, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [hrow]
  infer_instance

/-- At the degree of its only row, the column edge is an isomorphism. -/
theorem column_edge_isIso_of_single_row (hF : DegreewiseFinite F)
    (hQ : FirstQuadrant F D) (E : EdgeData F D) (n : ℤ) (hn : 0 ≤ n)
    (hZ : ∀ p m : ℤ, m ≠ p+n → IsZero (PageCohomology.object F D 2 p m)) :
    IsIso (E.column n hn) := by
  let L := stationaryLimit F D hF 2 (by omega) 0 n
    (fun r hr => by rw [zero_sub]; exact column_incoming_zero F D hQ r hr n)
    (fun r hr => (later_isZero_of_E2 F D (0+r) (n+1)
      (hZ _ _ (by omega)) r hr).eq_of_tgt _ _)
  haveI : IsIso (cohomologyPiece F 0 n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (cohomologyPiece_zero_eq_top F D hF hQ n)
  let π := cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F 0 n))
  haveI : IsIso π := cokernel.π_of_zero
    (ofLE_zero_of_eq_bot _
      (cohomologyPiece_eq_bot_of_E2_zero_above F D hF 1 n
        (fun p hp => hZ _ _ (by omega))))
  have hcolumn : E.column n hn = inv (cohomologyPiece F 0 n).arrow ≫ π ≫ L.iso.inv := by
    haveI : Epi (ambientClass F 0 n) := by dsimp only [ambientClass]; infer_instance
    apply (cancel_epi (ambientClass F 0 n)).1
    rw [E.column_formula]
    dsimp only [ambientClass]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc]
    change closedToPage F D 2 0 n = gradedClass F 0 n ≫ L.iso.inv
    rw [← L.representative_formula]
    simp
  rw [hcolumn]
  infer_instance

end AdvancedHomologicalAlgebra.EdgesAndFiveTerms
end G05Collapse

noncomputable section G05Quadrant

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
variable {B : Type u} {C : Type u'}
  [Category.{v} B] [Abelian B] [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive] (S : System G)

/-- Negative derived-functor columns vanish in the canonical descended row. -/
lemma descended_negative (Y : DerivedCategory.Plus B) (p m : ℤ) (hp : p < 0) :
    IsZero (((descendedRow G S).derived.obj Y).page 0 p m) := by
  letI : (DerivedCategory.Plus.Q (C := B)).EssSurj :=
    Localization.essSurj _ (CochainComplex.Plus.quasiIso B)
  let e := (pageEval 0 p m).mapIso (realization G (descendedRow G S) Y)
  let K := DerivedCategory.Plus.Q.objPreimage Y
  have hz := (S.data K ((descendedRow G S).resolution K)).negative p (m-p) hp
  change IsZero ((diagram G (S.data K ((descendedRow G S).resolution K))).page 0 p (p+(m-p))) at hz
  have hm : p+(m-p)=m := by omega
  rw [hm] at hz
  exact IsZero.of_iso hz e

/-- A zero cohomology input gives a zero E₂ term, for any integer column. -/
lemma descended_page_zero_of_homology_zero (Y : DerivedCategory.Plus B) (p m : ℤ)
    (hz : IsZero ((DerivedCategory.Plus.homologyFunctor B (m-p)).obj Y)) :
    IsZero (((descendedRow G S).derived.obj Y).page 0 p m) := by
  by_cases hp : p < 0
  · exact descended_negative G S Y p m hp
  · let e := (derivedSecondIso G S p.toNat (m-p)).app Y
    have he : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega)
    haveI : (rightValue G p.toNat).Additive := by dsimp [rightValue]; infer_instance
    have hz' := (rightValue G p.toNat).map_isZero hz
    exact IsZero.of_iso hz' (by simpa [he, pageEval] using e)

/-- Nonnegative cohomology gives the actual first quadrant of the row sequence. -/
lemma descended_quadrant (Y : DerivedCategory.Plus B) [Y.IsGE 0] :
    ∀ p m : ℤ, p < 0 ∨ m < p →
      IsZero (((descendedRow G S).derived.obj Y).page 0 p m) := by
  intro p m h
  rcases h with hp | hm
  · exact descended_negative G S Y p m hp
  · exact descended_page_zero_of_homology_zero G S Y p m
      (DerivedCategory.Plus.isZero_homology_of_isGE Y 0 (m-p) (by omega))

/-- A stalk in degree q has only the q-th row on E₂. -/
lemma descended_stalk_support (U : B) (q p m : ℤ) (hm : m ≠ p+q) :
    IsZero (((descendedRow G S).derived.obj
      ((DerivedCategory.Plus.singleFunctor B q).obj U)).page 0 p m) := by
  apply descended_page_zero_of_homology_zero G S
  have hne : m-p ≠ q := by omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact DerivedCategory.Plus.isZero_homology_of_isGE _ q (m-p) hlt
  · exact DerivedCategory.Plus.isZero_homology_of_isLE _ q (m-p) hgt

/-- Every nonnegative stalk row is first quadrant. -/
lemma descended_stalk_quadrant (U : B) (q : ℤ) (hq : 0 ≤ q) :
    ∀ p m : ℤ, p < 0 ∨ m < p →
      IsZero (((descendedRow G S).derived.obj
        ((DerivedCategory.Plus.singleFunctor B q).obj U)).page 0 p m) := by
  haveI : ((DerivedCategory.Plus.singleFunctor B q).obj U).IsGE 0 :=
    DerivedCategory.Plus.TStructure.t.isGE_of_ge _ 0 q hq
  exact descended_quadrant G S _

/-- The good upper truncation of a nonnegative object remains first quadrant. -/
lemma descended_trunc_quadrant (Y : DerivedCategory.Plus B) [Y.IsGE 0] (n : ℤ) :
    ∀ p m : ℤ, p < 0 ∨ m < p →
      IsZero (((descendedRow G S).derived.obj
        ((DerivedCategory.Plus.TStructure.t.truncLE n).obj Y)).page 0 p m) :=
  descended_quadrant G S _

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05Quadrant

noncomputable section G05CollapseTransport
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.G05FilteredEdges
open HypercohomologyDerivedNaturality GrothendieckSpectralSequence
open FiniteFiltrationConvergence CartanEilenbergData
universe uu vv uu' vv' ww ww'
variable {B : Type uu} {C : Type uu'} [Category.{vv} B] [Abelian B]
  [Category.{vv'} C] [Abelian C]
  [HasDerivedCategory.{ww} B] [HasDerivedCategory.{ww'} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive]

lemma transport_row_isIso {X Y : RowDiagram C} (e : X ≅ Y) (E : EdgeData Y)
    (n : ℕ) [IsIso (E.row n)] : IsIso ((transport e E).row n) := by
  haveI : IsIso (e.hom.page 0 n n) := ((pageEval 0 n n).mapIso e).isIso_hom
  haveI : IsIso (e.inv.target n) := ((targetEval n).mapIso e).isIso_inv
  change IsIso (e.hom.page 0 n n ≫ E.row n ≫ e.inv.target n)
  infer_instance

lemma transport_column_isIso {X Y : RowDiagram C} (e : X ≅ Y) (E : EdgeData Y)
    (n : ℕ) [IsIso (E.column n)] : IsIso ((transport e E).column n) := by
  haveI : IsIso (e.hom.target n) := ((targetEval n).mapIso e).isIso_hom
  haveI : IsIso (e.inv.page 0 0 n) := ((pageEval 0 0 n).mapIso e).isIso_inv
  change IsIso (e.hom.target n ≫ E.column n ≫ e.inv.page 0 0 n)
  infer_instance

lemma modelDiagram_row_isIso_of_support
    {K : CochainComplex.Plus B} {U : ResolutionData K.obj} (M : Data G K U)
    (hQ : EdgesAndFiveTerms.FirstQuadrant M.filtration M.pages)
    (hZ : ∀ p m : ℤ, m ≠ p → IsZero ((diagram G M).page 0 p m)) (n : ℕ) :
    IsIso ((modelDiagramEdges G M hQ).row n) := by
  haveI := EdgesAndFiveTerms.row_edge_isIso_of_single_row_zero M.filtration M.pages
    M.convergence.finite hQ (modelEdges G M hQ) hZ (n : ℤ) (by omega)
  change IsIso ((modelEdges G M hQ).row n (by omega) ≫ (M.targetIso n).hom)
  infer_instance

lemma modelDiagram_column_isIso_of_support
    {K : CochainComplex.Plus B} {U : ResolutionData K.obj} (M : Data G K U)
    (hQ : EdgesAndFiveTerms.FirstQuadrant M.filtration M.pages) (n : ℕ)
    (hZ : ∀ p m : ℤ, m ≠ p+(n : ℤ) → IsZero ((diagram G M).page 0 p m)) :
    IsIso ((modelDiagramEdges G M hQ).column n) := by
  haveI := EdgesAndFiveTerms.column_edge_isIso_of_single_row M.filtration M.pages
    M.convergence.finite hQ (modelEdges G M hQ) (n : ℤ) (by omega) hZ
  change IsIso ((M.targetIso n).inv ≫ (modelEdges G M hQ).column n (by omega))
  infer_instance

lemma realized_row_isIso_of_support
    {K : CochainComplex.Plus B} {U : ResolutionData K.obj} (M : Data G K U)
    {X : RowDiagram C} (e : X ≅ diagram G M) (hQ : FirstQuadrant X)
    (hZ : ∀ p m : ℤ, m ≠ p → IsZero (X.page 0 p m)) (n : ℕ) :
    IsIso ((realizedEdges G M e hQ).row n) := by
  have hz : ∀ p m : ℤ, m ≠ p → IsZero ((diagram G M).page 0 p m) := by
    intro p m hm
    exact IsZero.of_iso (hZ p m hm) ((pageEval 0 p m).mapIso e).symm
  haveI := modelDiagram_row_isIso_of_support G M (realizedQuadrant G M e hQ) hz n
  exact transport_row_isIso e _ n

lemma realized_column_isIso_of_support
    {K : CochainComplex.Plus B} {U : ResolutionData K.obj} (M : Data G K U)
    {X : RowDiagram C} (e : X ≅ diagram G M) (hQ : FirstQuadrant X) (n : ℕ)
    (hZ : ∀ p m : ℤ, m ≠ p+(n : ℤ) → IsZero (X.page 0 p m)) :
    IsIso ((realizedEdges G M e hQ).column n) := by
  have hz : ∀ p m : ℤ, m ≠ p+(n : ℤ) → IsZero ((diagram G M).page 0 p m) := by
    intro p m hm
    exact IsZero.of_iso (hZ p m hm) ((pageEval 0 p m).mapIso e).symm
  haveI := modelDiagram_column_isIso_of_support G M (realizedQuadrant G M e hQ) n hz
  exact transport_column_isIso e _ n

/-- The actual descended row edge is invertible for a row-zero input sequence. -/
lemma derived_row_isIso_of_support (R : DerivedRow G) (Y : DerivedCategory.Plus B)
    (hQ : FirstQuadrant (R.derived.obj Y))
    (hZ : ∀ p m : ℤ, m ≠ p → IsZero ((R.derived.obj Y).page 0 p m)) (n : ℕ) :
    IsIso ((derivedEdges G R Y hQ).row n) :=
  realized_row_isIso_of_support G _ (realization G R Y) hQ hZ n

/-- In the total degree of its only row, the descended column edge is invertible. -/
lemma derived_column_isIso_of_support (R : DerivedRow G) (Y : DerivedCategory.Plus B)
    (hQ : FirstQuadrant (R.derived.obj Y)) (n : ℕ)
    (hZ : ∀ p m : ℤ, m ≠ p+(n : ℤ) → IsZero ((R.derived.obj Y).page 0 p m)) :
    IsIso ((derivedEdges G R Y hQ).column n) :=
  realized_column_isIso_of_support G _ (realization G R Y) hQ n hZ

end AdvancedHomologicalAlgebra.G05FilteredEdges
end G05CollapseTransport

noncomputable section G05StalkCollapse
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u v u' v' w w'
variable {B : Type u} {C : Type u'}
  [Category.{v} B] [Abelian B] [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive] (S : System G)

lemma descended_stalk_row_isIso (U : B) (n : ℕ) :
    IsIso ((G05FilteredEdges.derivedEdges G (descendedRow G S)
      ((DerivedCategory.Plus.singleFunctor B 0).obj U)
      (descended_stalk_quadrant G S U 0 (by omega))).row n) := by
  apply G05FilteredEdges.derived_row_isIso_of_support
  intro p m hm
  exact descended_stalk_support G S U 0 p m (by simpa using hm)

lemma descended_stalk_column_isIso (U : B) (n : ℕ) :
    IsIso ((G05FilteredEdges.derivedEdges G (descendedRow G S)
      ((DerivedCategory.Plus.singleFunctor B (n : ℤ)).obj U)
      (descended_stalk_quadrant G S U (n : ℤ) (by omega))).column n) := by
  apply G05FilteredEdges.derived_column_isIso_of_support
  intro p m hm
  exact descended_stalk_support G S U (n : ℤ) p m hm

/-- Reindex the computed second page by a specified total degree. -/
def secondCoordinatesAt (p : ℕ) (q m : ℤ) (h : (p : ℤ) + q = m) :
    (descendedRow G S).derived ⋙ pageEval 0 (p : ℤ) m ≅
      DerivedCategory.Plus.homologyFunctor B q ⋙ rightValue G p :=
  by
    subst m
    exact derivedSecondIso G S p q

/-- The bottom-row coordinates of the descended second page, in total degree. -/
def bottomCoordinates (n : ℕ) :
    (descendedRow G S).derived ⋙ pageEval 0 (n : ℤ) (n : ℤ) ≅
      DerivedCategory.Plus.homologyFunctor B 0 ⋙ rightValue G n :=
  secondCoordinatesAt G S n 0 n (add_zero _)

/-- The left-column coordinates of the descended second page, in total degree. -/
def leftCoordinates (n : ℕ) :
    (descendedRow G S).derived ⋙ pageEval 0 0 (n : ℤ) ≅
      DerivedCategory.Plus.homologyFunctor B (n : ℤ) ⋙ rightValue G 0 :=
  secondCoordinatesAt G S 0 n n (zero_add _)

open CartanEilenbergData FiniteFiltrationConvergence

/-- The cochain model for a stalk in an arbitrary degree. -/
abbrev ordinaryStalk (U : B) (n : ℤ) : CochainComplex.Plus B :=
  ⟨(CochainComplex.singleFunctor B n).obj U, n, inferInstance⟩

lemma plusSingleHomology_app (U : B) (n : ℤ) :
    (singlePlusHomologyIso (B := B) n).hom.app U =
      (DerivedCategory.homologyFunctorFactors B n).hom.app (ordinaryStalk U n).obj ≫
        (HomologicalComplex.homologyFunctorSingleIso B (.up ℤ) n).hom.app U := by
  simp [singlePlusHomologyIso, DerivedCategory.singleFunctorCompHomologyFunctorIso]
  rfl

/-- Complex-level coordinates with the same total-degree indexing. -/
def modelSecondCoordinates {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    (M : Data G K R) (p : ℕ) (q m : ℤ) (h : (p : ℤ) + q = m) :
    (diagram G M).page 0 p m ≅ (rightValue G p).obj (K.obj.homology q) :=
  by
    subst m
    exact M.secondIso p q

lemma modelSecondCoordinates_hom {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    (M : Data G K R) (p : ℕ) (q m : ℤ) (h : (p : ℤ) + q = m) :
    (modelSecondCoordinates G M p q m h).hom =
      eqToHom (congrArg ((diagram G M).page 0 (p : ℤ)) h.symm) ≫
        (M.secondIso p q).hom := by
  subst m
  exact (Category.id_comp _).symm

lemma secondCoordinatesAt_app (K : CochainComplex.Plus B) (p : ℕ) (q m : ℤ)
    (h : (p : ℤ) + q = m) :
    (secondCoordinatesAt G S p q m h).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((descendedRow G S).complexIso G K).hom.page 0 p m ≫
        (modelSecondCoordinates G (S.data K ((descendedRow G S).resolution K)) p q m h).hom ≫
        (rightValue G p).map ((DerivedCategory.homologyFunctorFactors B q).inv.app K.obj) := by
  subst m
  exact (rowCoordinates G S).second_eq K p q

lemma modelSecondCoordinates_naturality {K L : CochainComplex.Plus B}
    {R : ResolutionData K.obj} {U : ResolutionData L.obj}
    (f : K ⟶ L) (a : R.bicomplex ⟶ U.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R U f.hom a) (p : ℕ) (q m : ℤ)
    (h : (p : ℤ) + q = m) :
    (diagramMap G S f a ha).page 0 p m ≫
        (modelSecondCoordinates G (S.data L U) p q m h).hom =
      (modelSecondCoordinates G (S.data K R) p q m h).hom ≫
        (rightValue G p).map (HomologicalComplex.homologyMap f.hom q) := by
  subst m
  exact S.second_naturality R U f a ha p q

lemma model_firstQuadrant (K : CochainComplex.Plus B) (R : ResolutionData K.obj)
    (hQ : G05FilteredEdges.FirstQuadrant ((descendedRow G S).derived.obj
      (DerivedCategory.Plus.Q.obj K))) :
    EdgesAndFiveTerms.FirstQuadrant (S.data K R).filtration (S.data K R).pages := by
  intro p n hpn
  by_cases hp : p < 0
  · have hneg := (S.data K R).negative p (n-p) hp
    have hdeg : p+(n-p)=n := by omega
    simpa only [term, DoubleComplexFirstPages.page, hdeg] using hneg
  · let e := (descendedRow G S).complexIso G K
    let U := (descendedRow G S).resolution K
    let hU := G05FilteredEdges.realizedQuadrant G (S.data K U) e hQ
    let q := n-p
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = p := ⟨p.toNat, Int.toNat_of_nonneg (by omega)⟩
    let hsum : (k : ℤ)+q=n := by dsimp [q]; omega
    exact IsZero.of_iso (hU k n hpn)
      (modelSecondCoordinates G (S.data K R) k q n hsum ≪≫
        (modelSecondCoordinates G (S.data K U) k q n hsum).symm)

set_option maxHeartbeats 1000000 in
/-- Check the comparison of the bottom edge on any one Cartan–Eilenberg
resolution of the complex. A lift of the identity transfers the calculation
to the chosen resolution before localization. -/
lemma bottomEdge_of_model (K : CochainComplex.Plus B) (R : ResolutionData K.obj) (n : ℕ)
    (hQ : G05FilteredEdges.FirstQuadrant ((descendedRow G S).derived.obj
      (DerivedCategory.Plus.Q.obj K)))
    (hM : EdgesAndFiveTerms.FirstQuadrant (S.data K R).filtration (S.data K R).pages)
    (v : (rightValue G n).obj (K.obj.homology 0) ⟶ target G K n)
    (h : let M := S.data K R
      ∃ (T : C) (c : T ⟶ (closed M.filtration n n : C)),
        Epi (c ≫ closedToPage M.filtration M.pages 2 n n) ∧
        c ≫ EdgesAndFiveTerms.ambientClass M.filtration n n ≫ (M.targetIso n).hom =
          c ≫ closedToPage M.filtration M.pages 2 n n ≫
            (modelSecondCoordinates G M n 0 n (add_zero _)).hom ≫ v) :
    (G05FilteredEdges.derivedEdges G (descendedRow G S) (DerivedCategory.Plus.Q.obj K) hQ).row n ≫
      (derivedTargetIso G S (n : ℤ)).hom.app (DerivedCategory.Plus.Q.obj K) =
        (bottomCoordinates G S n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
          (rightValue G n).map ((DerivedCategory.homologyFunctorFactors B 0).hom.app K.obj) ≫ v := by
  let D := descendedRow G S
  let U := D.resolution K
  let e := D.complexIso G K
  let hU := G05FilteredEdges.realizedQuadrant G (S.data K U) e hQ
  let ER := G05FilteredEdges.modelDiagramEdges G (S.data K R) hM
  let EU := G05FilteredEdges.modelDiagramEdges G (S.data K U) hU
  have hR : ER.row n = (modelSecondCoordinates G (S.data K R) n 0 n (add_zero _)).hom ≫ v := by
    let M := S.data K R
    obtain ⟨T,c,hc,hrep⟩ := h
    letI := hc
    apply (cancel_epi (c ≫ closedToPage M.filtration M.pages 2 n n)).1
    change (c ≫ closedToPage M.filtration M.pages 2 n n) ≫
      ((G05FilteredEdges.modelEdges G M hM).row n (by omega) ≫ (M.targetIso n).hom) =
        (c ≫ closedToPage M.filtration M.pages 2 n n) ≫ _ ≫ v
    erw [Category.assoc c, Category.assoc c, ← Category.assoc (closedToPage M.filtration M.pages 2 n n),
      (G05FilteredEdges.modelEdges G M hM).row_formula]
    exact hrep
  obtain ⟨a, ha⟩ := S.comparison R U (𝟙 K)
  let f := diagramMap G S (𝟙 K) a ha
  have hf := modelSecondCoordinates_naturality G S (𝟙 K) a ha n 0 n (add_zero _)
  simp only [ObjectProperty.FullSubcategory.id_hom, HomologicalComplex.homologyMap_id,
    (rightValue G n).map_id, Category.comp_id] at hf
  change f.page 0 n n ≫ _ = _ at hf
  have ht : f.target n = 𝟙 (target G K n) :=
    (DerivedCategory.Plus.Q ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor C n).map_id K
  haveI : IsIso (f.page 0 n n) := by
    have hi : IsIso (f.page 0 n n ≫
        (modelSecondCoordinates G (S.data K U) n 0 n (add_zero _)).hom) :=
      hf.symm ▸ (modelSecondCoordinates G (S.data K R) n 0 n (add_zero _)).isIso_hom
    exact IsIso.of_isIso_comp_right _ (modelSecondCoordinates G (S.data K U) n 0 n (add_zero _)).hom
  have hU' : EU.row n = (modelSecondCoordinates G (S.data K U) n 0 n (add_zero _)).hom ≫ v := by
    apply (cancel_epi (f.page 0 n n)).1
    have hn : f.page 0 n n ≫ EU.row n = ER.row n ≫ f.target n :=
      G05FilteredEdges.modelDiagram_row_naturality G S (𝟙 K) a ha hM hU n
    erw [hn, hR, ht, Category.comp_id, reassoc_of% hf]
    rfl
  have htarget : (derivedTargetIso G S (n : ℤ)).hom.app (DerivedCategory.Plus.Q.obj K) =
    e.hom.target n := (rowCoordinates G S).target_eq K n
  rw [G05FilteredEdges.derivedEdges_q]
  erw [htarget]
  rw [show (bottomCoordinates G S n).hom.app (DerivedCategory.Plus.Q.obj K) = _ from
    secondCoordinatesAt_app G S K n 0 n (add_zero _)]
  let t := (targetEval (C := C) n).mapIso e
  let p := ((pageEval 0 n n).mapIso e).hom
  let k := (modelSecondCoordinates G (S.data K U) n 0 n (add_zero _)).hom
  let a := (rightValue G n).mapIso ((DerivedCategory.homologyFunctorFactors B 0).app K.obj)
  change (p ≫ EU.row n ≫ t.inv) ≫ t.hom = (p ≫ k ≫ a.inv) ≫ a.hom ≫ v
  have cancelModelTarget {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (j : Z ≅ Y) :
      (f ≫ g ≫ j.inv) ≫ j.hom = f ≫ g := by
    simp only [Category.assoc, j.inv_hom_id, Category.comp_id]
  have cancelHomologyFactors {W X Y Z L : C} (f : W ⟶ X) (g : X ⟶ Y)
      (j : Z ≅ Y) (u : Y ⟶ L) :
      (f ≫ g ≫ j.inv) ≫ j.hom ≫ u = f ≫ g ≫ u := by
    simp only [Category.assoc, j.inv_hom_id_assoc]
  have hleft : (p ≫ EU.row n ≫ t.inv) ≫ t.hom = p ≫ EU.row n :=
    cancelModelTarget p (EU.row n) t
  have hright : (p ≫ k ≫ a.inv) ≫ a.hom ≫ v = p ≫ k ≫ v :=
    cancelHomologyFactors p k a v
  rw [hleft, hright]
  exact congrArg (fun u => p ≫ u) hU'

set_option maxHeartbeats 1000000 in
/-- The left-edge comparison transfers from any Cartan–Eilenberg
resolution by its map over the identity of the complex. -/
lemma leftEdge_of_model (K : CochainComplex.Plus B) (R : ResolutionData K.obj) (n : ℕ)
    (hQ : G05FilteredEdges.FirstQuadrant ((descendedRow G S).derived.obj
      (DerivedCategory.Plus.Q.obj K)))
    (hM : EdgesAndFiveTerms.FirstQuadrant (S.data K R).filtration (S.data K R).pages)
    {L : C} (v : (rightValue G 0).obj (K.obj.homology n) ⟶ L)
    (w : target G K n ⟶ L)
    (h : let M := S.data K R
      ∃ (T : C) (c : T ⟶ (closed M.filtration 0 n : C)),
        Epi (c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n) ∧
        c ≫ closedToPage M.filtration M.pages 2 0 n ≫
            (modelSecondCoordinates G M 0 n n (zero_add _)).hom ≫ v =
          c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom ≫ w) :
    (G05FilteredEdges.derivedEdges G (descendedRow G S) (DerivedCategory.Plus.Q.obj K) hQ).column n ≫
      (leftCoordinates G S n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        (rightValue G 0).map ((DerivedCategory.homologyFunctorFactors B n).hom.app K.obj) ≫ v =
          (derivedTargetIso G S (n : ℤ)).hom.app (DerivedCategory.Plus.Q.obj K) ≫ w := by
  let D := descendedRow G S
  let U := D.resolution K
  let e := D.complexIso G K
  let hU := G05FilteredEdges.realizedQuadrant G (S.data K U) e hQ
  let ER := G05FilteredEdges.modelDiagramEdges G (S.data K R) hM
  let EU := G05FilteredEdges.modelDiagramEdges G (S.data K U) hU
  have hR : ER.column n ≫ (modelSecondCoordinates G (S.data K R) 0 n n (zero_add _)).hom ≫ v = w := by
    let M := S.data K R
    obtain ⟨T,d,hd,hrep⟩ := h
    letI := hd
    let b := EdgesAndFiveTerms.ambientClass M.filtration 0 n
    let c := (G05FilteredEdges.modelEdges G M hM).column n (by omega)
    let k := (modelSecondCoordinates G M 0 n n (zero_add _)).hom
    let t := M.targetIso n
    apply (cancel_epi ((d ≫ b) ≫ t.hom)).1
    change ((d ≫ b) ≫ t.hom) ≫ (t.inv ≫ c) ≫ k ≫ v = ((d ≫ b) ≫ t.hom) ≫ w
    have hb : b ≫ c = closedToPage M.filtration M.pages 2 0 n :=
      (G05FilteredEdges.modelEdges G M hM).column_formula n (by omega)
    calc
      ((d ≫ b) ≫ t.hom) ≫ (t.inv ≫ c) ≫ k ≫ v =
          d ≫ (b ≫ c) ≫ k ≫ v := by simp only [Category.assoc, t.hom_inv_id_assoc]
      _ = d ≫ b ≫ t.hom ≫ w := by rw [hb]; exact hrep
      _ = ((d ≫ b) ≫ t.hom) ≫ w := by simp only [Category.assoc]
  obtain ⟨a, ha⟩ := S.comparison R U (𝟙 K)
  let f := diagramMap G S (𝟙 K) a ha
  have hf := modelSecondCoordinates_naturality G S (𝟙 K) a ha 0 n n (zero_add _)
  simp only [ObjectProperty.FullSubcategory.id_hom, HomologicalComplex.homologyMap_id,
    (rightValue G 0).map_id, Category.comp_id] at hf
  change f.page 0 0 n ≫ _ = _ at hf
  have ht : f.target n = 𝟙 (target G K n) :=
    (DerivedCategory.Plus.Q ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor C n).map_id K
  have hU' : EU.column n ≫ (modelSecondCoordinates G (S.data K U) 0 n n (zero_add _)).hom ≫ v = w := by
    have hn : f.target n ≫ EU.column n = ER.column n ≫ f.page 0 0 n :=
      G05FilteredEdges.modelDiagram_column_naturality G S (𝟙 K) a ha hM hU n
    erw [ht, Category.id_comp] at hn
    erw [hn, Category.assoc, reassoc_of% hf, hR]
  have htarget : (derivedTargetIso G S (n : ℤ)).hom.app (DerivedCategory.Plus.Q.obj K) =
    e.hom.target n := (rowCoordinates G S).target_eq K n
  rw [G05FilteredEdges.derivedEdges_q]
  erw [htarget]
  rw [show (leftCoordinates G S n).hom.app (DerivedCategory.Plus.Q.obj K) = _ from
    secondCoordinatesAt_app G S K 0 n n (zero_add _)]
  let t := ((targetEval (C := C) n).mapIso e).hom
  let p := (pageEval 0 0 n).mapIso e
  let k := (modelSecondCoordinates G (S.data K U) 0 n n (zero_add _)).hom
  let a := (rightValue G 0).mapIso ((DerivedCategory.homologyFunctorFactors B n).app K.obj)
  change (t ≫ EU.column n ≫ p.inv) ≫ (p.hom ≫ k ≫ a.inv) ≫ a.hom ≫ v = t ≫ w
  have hleft : (t ≫ EU.column n ≫ p.inv) ≫ (p.hom ≫ k ≫ a.inv) ≫ a.hom ≫ v =
      t ≫ EU.column n ≫ k ≫ v := by
    calc
      _ = t ≫ (EU.column n ≫ p.inv) ≫ (p.hom ≫ k ≫ a.inv) ≫ a.hom ≫ v :=
        Category.assoc _ _ _
      _ = t ≫ EU.column n ≫ p.inv ≫ (p.hom ≫ k ≫ a.inv) ≫ a.hom ≫ v :=
        congrArg (fun f => t ≫ f) (Category.assoc _ _ _)
      _ = t ≫ EU.column n ≫ p.inv ≫ p.hom ≫ (k ≫ a.inv) ≫ a.hom ≫ v :=
        congrArg (fun f => t ≫ EU.column n ≫ p.inv ≫ f) (Category.assoc _ _ _)
      _ = t ≫ EU.column n ≫ (k ≫ a.inv) ≫ a.hom ≫ v :=
        congrArg (fun f => t ≫ EU.column n ≫ f) (p.inv_hom_id_assoc _)
      _ = t ≫ EU.column n ≫ k ≫ a.inv ≫ a.hom ≫ v :=
        congrArg (fun f => t ≫ EU.column n ≫ f) (Category.assoc _ _ _)
      _ = _ := congrArg (fun f => t ≫ EU.column n ≫ k ≫ f) (a.inv_hom_id_assoc v)
  rw [hleft]
  exact congrArg (fun u => t ≫ u) hU'

/-- Pass the closed-representative calculation on an ordinary stalk to the
degree-zero stalk in the derived category. -/
lemma bottomStalk_of_model (U : B) (n : ℕ)
    (R : ResolutionData (ordinaryStalk U 0).obj)
    (h : let M := S.data (ordinaryStalk U 0) R
      ∃ (T : C) (c : T ⟶ (closed M.filtration n n : C)),
        Epi (c ≫ closedToPage M.filtration M.pages 2 n n) ∧
        c ≫ EdgesAndFiveTerms.ambientClass M.filtration n n ≫ (M.targetIso n).hom =
          c ≫ closedToPage M.filtration M.pages 2 n n ≫
            (modelSecondCoordinates G M n 0 n (add_zero _)).hom ≫
            (rightValue G n).map ((HomologicalComplex.homologyFunctorSingleIso B (.up ℤ) 0).hom.app U)) :
    let Y := (DerivedCategory.Plus.singleFunctor B 0).obj U
    (G05FilteredEdges.derivedEdges G (descendedRow G S) Y
      (descended_stalk_quadrant G S U 0 (by omega))).row n ≫
        (derivedTargetIso G S (n : ℤ)).hom.app Y =
      (bottomCoordinates G S n).hom.app Y ≫
        (rightValue G n).map ((singlePlusHomologyIso (B := B) 0).hom.app U) := by
  let Q := descended_stalk_quadrant G S U 0 (by omega)
  have e := bottomEdge_of_model G S (ordinaryStalk U 0) R n Q
    (model_firstQuadrant G S (ordinaryStalk U 0) R Q) _ h
  dsimp only
  erw [plusSingleHomology_app, (rightValue G n).map_comp]
  exact e

/-- Pass the closed-representative calculation on an ordinary stalk to the
stalk in the same degree in the derived category. -/
lemma leftStalk_of_model [PreservesFiniteLimits G] (U : B) (n : ℕ)
    (R : ResolutionData (ordinaryStalk U (n : ℤ)).obj)
    (h : let M := S.data (ordinaryStalk U (n : ℤ)) R
      ∃ (T : C) (c : T ⟶ (closed M.filtration 0 n : C)),
        Epi (c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n) ∧
        c ≫ closedToPage M.filtration M.pages 2 0 n ≫
            (modelSecondCoordinates G M 0 n n (zero_add _)).hom ≫
            (rightValue G 0).map ((HomologicalComplex.homologyFunctorSingleIso B (.up ℤ) n).hom.app U) ≫
            (canonicalRightZeroIso G).hom.app U =
          c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom ≫
            (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app U) :
    let Y := (DerivedCategory.Plus.singleFunctor B (n : ℤ)).obj U
    (G05FilteredEdges.derivedEdges G (descendedRow G S) Y
      (descended_stalk_quadrant G S U (n : ℤ) (by omega))).column n ≫
        (leftCoordinates G S n).hom.app Y ≫
        (rightValue G 0).map ((singlePlusHomologyIso (B := B) (n : ℤ)).hom.app U) ≫
        (canonicalRightZeroIso G).hom.app U =
      (derivedTargetIso G S (n : ℤ)).hom.app Y ≫
        (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app U := by
  let Q := descended_stalk_quadrant G S U (n : ℤ) (by omega)
  let v := (rightValue G 0).map
    ((HomologicalComplex.homologyFunctorSingleIso B (.up ℤ) n).hom.app U) ≫
      (canonicalRightZeroIso G).hom.app U
  have e := leftEdge_of_model G S (ordinaryStalk U (n : ℤ)) R n Q
    (model_firstQuadrant G S (ordinaryStalk U (n : ℤ)) R Q) v _ h
  dsimp only
  erw [plusSingleHomology_app, (rightValue G 0).map_comp]
  erw [Category.assoc ((rightValue G 0).map
    ((DerivedCategory.homologyFunctorFactors B n).hom.app (ordinaryStalk U n).obj))]
  exact e

end AdvancedHomologicalAlgebra.GrothendieckEdges

end G05StalkCollapse

noncomputable section G05IdentifyFirstEdge
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  (S : System G)

private lemma stalkToDerived_page_isIso [PreservesFiniteLimits F] (X : A) (n : ℕ) :
    IsIso (((descendedRow G S).derived.map ((stalkToDerived F).app X)).page 0 n n) := by
  let D := (descendedRow G S).derived
  let P := pageEval (C := C) 0 (n : ℤ) (n : ℤ)
  let R := DerivedCategory.Plus.homologyFunctor B 0 ⋙ rightValue G n
  let e : D ⋙ P ≅ R := by
    simpa only [add_zero] using derivedSecondIso G S n 0
  let f := (stalkToDerived F).app X
  haveI : IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map f) :=
    stalkToDerived_homology_zero_isIso F X
  haveI : IsIso (R.map f) := by
    change IsIso ((rightValue G n).map ((DerivedCategory.Plus.homologyFunctor B 0).map f))
    infer_instance
  change IsIso ((D ⋙ P).map f)
  haveI : IsIso ((D ⋙ P).map f ≫ e.hom.app _) := by
    rw [e.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

/-- The row edge on a degree-zero stalk compares its surviving
second-page term with the entire degree-n target. -/
private def stalkRowIso (n : ℕ) :
    ((F ⋙ DerivedCategory.Plus.singleFunctor B 0) ⋙ (descendedRow G S).derived) ⋙
      pageEval 0 (n : ℤ) (n : ℤ) ≅
    ((F ⋙ DerivedCategory.Plus.singleFunctor B 0) ⋙ (descendedRow G S).derived) ⋙
      targetEval (n : ℤ) := by
  let Q (X : A) := descended_stalk_quadrant G S (F.obj X) 0 (by omega)
  let E (X : A) := G05FilteredEdges.derivedEdges G (descendedRow G S)
    ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)) (Q X)
  letI (X : A) : IsIso ((E X).row n) :=
    descended_stalk_row_isIso G S (F.obj X) n
  refine NatIso.ofComponents (fun X => asIso ((E X).row n)) ?_
  intro X Y f
  exact (G05FilteredEdges.derived_edges_naturality G (descendedRow G S)
    ((DerivedCategory.Plus.singleFunctor B 0).map (F.map f)) (Q X) (Q Y)).row n

/-- Use the collapse comparison on F(X)[0] and carry that identification to
the bottom row along the derived unit. -/
def normalizedFirstPageIso [PreservesFiniteLimits F] (n : ℕ) :
    ((DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus) ⋙
      (descendedRow G S).derived) ⋙ pageEval 0 (n : ℤ) (n : ℤ) ≅ F ⋙ rightValue G n := by
  let M := (descendedRow G S).derived
  let T := pageEval (C := C) 0 (n : ℤ) (n : ℤ)
  let α := whiskerRight (whiskerRight (stalkToDerived F) M) T
  haveI (X : A) : IsIso (α.app X) := stalkToDerived_page_isIso F G S X n
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  exact (asIso α).symm ≪≫ stalkRowIso F G S n ≪≫
    (associator _ _ _) ≪≫
    isoWhiskerLeft (F ⋙ DerivedCategory.Plus.singleFunctor B 0) (derivedTargetIso G S (n : ℤ))

set_option maxHeartbeats 800000 in
/-- The actual filtered bottom edge is the one induced by the derived unit. -/
theorem normalizedFirstPageIso_row [PreservesFiniteLimits F] (X : A) (n : ℕ)
    (hQ : G05FilteredEdges.FirstQuadrant
      ((descendedRow G S).derived.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) :
    (normalizedFirstPageIso F G S n).hom.app X ≫
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (n : ℤ)).map
        ((stalkToDerived F).app X) =
    (G05FilteredEdges.derivedEdges G (descendedRow G S)
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))
      hQ).row n ≫
      (derivedTargetIso G S (n : ℤ)).hom.app
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  let D := (descendedRow G S).derived
  let H := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let f := (stalkToDerived F).app X
  let U := (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)
  let Y := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let hU := descended_stalk_quadrant G S (F.obj X) 0 (by omega)
  let e := derivedTargetIso G S (n : ℤ)
  let rU := (G05FilteredEdges.derivedEdges G (descendedRow G S) U hU).row n
  let rY := (G05FilteredEdges.derivedEdges G (descendedRow G S) Y hQ).row n
  letI : IsIso ((D.map f).page 0 n n) := stalkToDerived_page_isIso F G S X n
  have ht : (D.map f).target n ≫ e.hom.app Y = e.hom.app U ≫ H.map f :=
    e.hom.naturality f
  have hr : (D.map f).page 0 n n ≫ rY = rU ≫ (D.map f).target n :=
    (G05FilteredEdges.derived_edges_naturality G (descendedRow G S) f hU hQ).row n
  dsimp only [normalizedFirstPageIso, stalkRowIso, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, NatTrans.comp_app, NatIso.ofComponents_hom_app, asIso_hom,
    associator_hom_app, isoWhiskerLeft_hom, whiskerLeft_app]
  rw [NatIso.isIso_inv_app]
  dsimp only [whiskerRight_app]
  change (inv ((D.map f).page 0 n n) ≫ (rU ≫ 𝟙 _ ≫ e.hom.app U)) ≫ H.map f =
    rY ≫ e.hom.app Y
  rw [Category.id_comp]
  calc
    (inv ((D.map f).page 0 n n) ≫ rU ≫ e.hom.app U) ≫ H.map f =
        inv ((D.map f).page 0 n n) ≫ rU ≫ ((D.map f).target n ≫ e.hom.app Y) := by
      simp only [Category.assoc, ← ht]
    _ = rY ≫ e.hom.app Y := by
      rw [← Category.assoc rU, ← hr, ← Category.assoc (inv _), IsIso.inv_hom_id_assoc]

/-- The compatibility on stalks determines the same compatibility after applying
the derived unit, since that unit is invertible on the bottom second page. -/
lemma bottomCoordinates_naturality [PreservesFiniteLimits F] (n : ℕ)
    (hStalk : ∀ U : B,
      let Y := (DerivedCategory.Plus.singleFunctor B 0).obj U
      (G05FilteredEdges.derivedEdges G (descendedRow G S) Y
        (descended_stalk_quadrant G S U 0 (by omega))).row n ≫
          (derivedTargetIso G S (n : ℤ)).hom.app Y =
        (bottomCoordinates G S n).hom.app Y ≫
          (rightValue G n).map ((singlePlusHomologyIso (B := B) 0).hom.app U))
    (X : A) :
    (normalizedFirstPageIso F G S n).hom.app X ≫
        (rightValue G n).map ((degreeZeroIso F).hom.app X) =
      (bottomCoordinates G S n).hom.app
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  let D := (descendedRow G S).derived
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let U := (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)
  let Y := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let f := (stalkToDerived F).app X
  let c := (bottomCoordinates G S n).hom
  let a := (singlePlusHomologyIso (B := B) 0).app (F.obj X)
  haveI : IsIso ((D.map f).page 0 n n) := stalkToDerived_page_isIso F G S X n
  have hnat : (D.map f).page 0 n n ≫ c.app Y =
      c.app U ≫ (rightValue G n).map (H.map f) := c.naturality f
  have hdeg : (degreeZeroIso F).hom.app X = a.inv ≫ H.map f := rfl
  simp only [normalizedFirstPageIso, stalkRowIso, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, NatTrans.comp_app, NatIso.ofComponents_hom_app, asIso_hom,
    associator_hom_app, isoWhiskerLeft_hom, whiskerLeft_app, NatIso.isIso_inv_app,
    whiskerRight_app, Category.id_comp]
  apply (cancel_epi ((D.map f).page 0 n n)).1
  change (D.map f).page 0 n n ≫
      (inv ((D.map f).page 0 n n) ≫ _ ≫ _) ≫ _ = _
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  let E := (G05FilteredEdges.derivedEdges G (descendedRow G S) U
    (descended_stalk_quadrant G S (F.obj X) 0 (by omega))).row n
  let t := (derivedTargetIso G S (n : ℤ)).hom.app U
  let R := rightValue G n
  change E ≫ t ≫ R.map ((degreeZeroIso F).hom.app X) =
    (D.map f).page 0 n n ≫ c.app Y
  have hs : E ≫ t = c.app U ≫ R.map a.hom := hStalk (F.obj X)
  rw [← Category.assoc, hs, hnat, hdeg]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc]
  rfl

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05IdentifyFirstEdge

noncomputable section G05ColumnIdentification
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open HypercohomologyDerivedNaturality GrothendieckSpectralSequence G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u v u' v' w w'
variable {B : Type u} {C : Type u'}
  [Category.{v} B] [Abelian B] [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive] (S : System G)

private abbrev columnPage (n : ℕ) :=
  (descendedRow G S).derived ⋙ pageEval 0 0 (n : ℤ)

local notation "tB" => (DerivedCategory.Plus.TStructure.t (C := B))

private abbrev columnStalk (n : ℕ) := DerivedCategory.Plus.singleFunctor B (n : ℤ)

/-- For a degree-`n` stalk there is only one nonzero graded piece in total
degree `n`. Its identification with the second page is the column edge. -/
def stalkColumnIso (n : ℕ) :
    columnStalk n ⋙ (descendedRow G S).derived ⋙ targetEval (n : ℤ) ≅
      columnStalk n ⋙ columnPage G S n := by
  refine NatIso.ofComponents (fun U => ?_) ?_
  · haveI := descended_stalk_column_isIso G S U n
    exact asIso ((derivedEdges G (descendedRow G S) ((columnStalk n).obj U)
      (descended_stalk_quadrant G S U _ (by omega))).column n)
  · intro U V f
    exact (derived_edges_naturality G (descendedRow G S) ((columnStalk n).map f)
      (descended_stalk_quadrant G S U _ (by omega))
      (descended_stalk_quadrant G S V _ (by omega))).column n

private lemma columnPage_map_isIso (n : ℕ) {X Y : DerivedCategory.Plus B} (f : X ⟶ Y)
    (h : IsIso ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map f)) :
    IsIso ((columnPage G S n).map f) := by
  let e : columnPage G S n ≅
      DerivedCategory.Plus.homologyFunctor B (n : ℤ) ⋙ rightValue G 0 := by
    simpa only [Int.natCast_zero, zero_add] using derivedSecondIso G S 0 (n : ℤ)
  haveI : IsIso (((DerivedCategory.Plus.homologyFunctor B (n : ℤ)) ⋙ rightValue G 0).map f) := by
    change IsIso ((rightValue G 0).map ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map f))
    infer_instance
  exact (NatIso.isIso_map_iff e f).2 inferInstance

private lemma truncationToSingle_homology_isIso (n : ℕ) (Y : DerivedCategory.Plus B) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      ((truncationToSingle (n : ℤ)).app Y)) := by
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let e := (singlePlusHomologyIso (B := B) (n : ℤ)).app (H.obj Y)
  haveI : IsIso (H.map ((truncationToSingle (B := B) (n : ℤ)).app Y) ≫ e.hom) := by
    rw [show H.map ((truncationToSingle (B := B) (n : ℤ)).app Y) ≫ e.hom =
        H.map (((tB).truncLEι (n : ℤ)).app Y) from truncationToSingle_normalization _ _]
    exact homology_truncLEι_isIso Y _ _ (le_refl _)
  exact IsIso.of_isIso_comp_right _ e.hom

private def columnPageTruncLEIso (n : ℕ) :
    (tB).truncLE (n : ℤ) ⋙ columnPage G S n ≅ columnPage G S n := by
  let α := whiskerRight ((tB).truncLEι (n : ℤ)) (columnPage G S n)
  haveI (Y : DerivedCategory.Plus B) : IsIso (α.app Y) :=
    columnPage_map_isIso G S n _ (homology_truncLEι_isIso Y _ _ (le_refl _))
  letI : IsIso α := NatIso.isIso_of_isIso_app _
  exact asIso α

private def columnPageTruncToStalkIso (n : ℕ) :
    (tB).truncLE (n : ℤ) ⋙ columnPage G S n ≅
      DerivedCategory.Plus.homologyFunctor B (n : ℤ) ⋙ columnStalk n ⋙ columnPage G S n := by
  let α := whiskerRight (truncationToSingle (B := B) (n : ℤ)) (columnPage G S n)
  haveI (Y : DerivedCategory.Plus B) : IsIso (α.app Y) :=
    columnPage_map_isIso G S n _ (truncationToSingle_homology_isIso n Y)
  letI : IsIso α := NatIso.isIso_of_isIso_app _
  exact asIso α

/-- Identify the zero column using the stalk identification in the exact
degree of the page term. The two truncation maps preserve this page term. -/
def columnPageIso [PreservesFiniteLimits G] (n : ℕ) :
    columnPage G S n ≅ DerivedCategory.Plus.homologyFunctor B (n : ℤ) ⋙ G :=
  (columnPageTruncLEIso G S n).symm ≪≫ columnPageTruncToStalkIso G S n ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor B (n : ℤ))
      ((stalkColumnIso G S n).symm ≪≫
        isoWhiskerLeft (columnStalk n) (derivedTargetIso G S (n : ℤ)) ≪≫
        rightDerivedStalkHomologyIso G (n : ℤ))

/-- The filtered column edge agrees with the right-derived map from the
canonical good-truncation span. -/
theorem column_edge_comparison [PreservesFiniteLimits G]
    (Y : DerivedCategory.Plus B) [Y.IsGE 0] (n : ℕ) :
    (derivedEdges G (descendedRow G S) Y (descended_quadrant G S Y)).column n ≫
        (columnPageIso G S n).hom.app Y =
      (derivedTargetIso G S (n : ℤ)).hom.app Y ≫ (derivedTruncationEdge G (n : ℤ)).app Y := by
  let R := (descendedRow G S).derived
  let P := columnPage G S n
  let L := R ⋙ targetEval (n : ℤ)
  let H := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let T := ((tB).truncLE (n : ℤ)).obj Y
  let V := (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj Y
  let U := (columnStalk n).obj V
  let i : T ⟶ Y := ((tB).truncLEι (n : ℤ)).app Y
  let j : T ⟶ U := (truncationToSingle (n : ℤ)).app Y
  let e := (derivedTargetIso G S (n : ℤ)).hom
  let E := (derivedEdges G (descendedRow G S) Y (descended_quadrant G S Y)).column n
  let Eₜ := (derivedEdges G (descendedRow G S) T (descended_trunc_quadrant G S Y _)).column n
  let Eᵤ := (derivedEdges G (descendedRow G S) U
    (descended_stalk_quadrant G S V _ (by omega))).column n
  let k := (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app V
  haveI : IsIso (P.map i) :=
    columnPage_map_isIso G S n i (homology_truncLEι_isIso Y _ _ (le_refl _))
  haveI : IsIso (H.map i) := isIso_homology_rightDerived_truncLEι G Y (n : ℤ)
  haveI : IsIso Eᵤ := descended_stalk_column_isIso G S V n
  have hEi : L.map i ≫ E = Eₜ ≫ P.map i :=
    (derived_edges_naturality G (descendedRow G S) i
      (descended_trunc_quadrant G S Y _) (descended_quadrant G S Y)).column n
  have hEj : L.map j ≫ Eᵤ = Eₜ ≫ P.map j :=
    (derived_edges_naturality G (descendedRow G S) j
      (descended_trunc_quadrant G S Y _) (descended_stalk_quadrant G S V _ (by omega))).column n
  have hti : L.map i ≫ e.app Y = e.app T ≫ H.map i := e.naturality i
  have htj : L.map j ≫ e.app U = e.app T ≫ H.map j := e.naturality j
  haveI : IsIso (L.map i) := (NatIso.isIso_map_iff (derivedTargetIso G S (n : ℤ)) i).2 inferInstance
  simp only [columnPageIso, columnPageTruncLEIso, columnPageTruncToStalkIso,
    derivedTruncationEdge, homology_rightDerived_truncLEIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, asIso_hom, asIso_inv, NatIso.isIso_inv_app, whiskerRight_app,
    whiskerLeft_app, isoWhiskerLeft_hom, associator_hom_app, Category.id_comp]
  change E ≫ inv (P.map i) ≫ P.map j ≫ inv Eᵤ ≫ e.app U ≫ k =
    e.app Y ≫ inv (H.map i) ≫ H.map j ≫ k
  apply (cancel_epi (L.map i)).1
  simp only [reassoc_of% hEi, reassoc_of% hti,
    IsIso.hom_inv_id_assoc, ← reassoc_of% hEj, ← reassoc_of% htj]

private def stalkColumnCoordinates [PreservesFiniteLimits G] (n : ℕ) :
    columnStalk n ⋙ columnPage G S n ≅ G :=
  isoWhiskerLeft (columnStalk n) (leftCoordinates G S n) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (singlePlusHomologyIso (B := B) (n : ℤ)) (rightValue G 0) ≪≫
    leftUnitor _ ≪≫ canonicalRightZeroIso G

set_option maxHeartbeats 1000000 in
/-- It suffices to compare the stalk column edge on injective objects.
Both comparisons are natural, and the left exact functor preserves the
monomorphism from any object into an injective. -/
lemma stalkColumn_comparison_of_injective [PreservesFiniteLimits G] (n : ℕ)
    (hI : ∀ U : B, Injective U →
      let Y := (columnStalk n).obj U
      (derivedEdges G (descendedRow G S) Y
        (descended_stalk_quadrant G S U (n : ℤ) (by omega))).column n ≫
          (leftCoordinates G S n).hom.app Y ≫
          (rightValue G 0).map ((singlePlusHomologyIso (B := B) (n : ℤ)).hom.app U) ≫
          (canonicalRightZeroIso G).hom.app U =
        (derivedTargetIso G S (n : ℤ)).hom.app Y ≫
          (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app U)
    (U : B) :
    let Y := (columnStalk n).obj U
    (derivedEdges G (descendedRow G S) Y
      (descended_stalk_quadrant G S U (n : ℤ) (by omega))).column n ≫
        (leftCoordinates G S n).hom.app Y ≫
        (rightValue G 0).map ((singlePlusHomologyIso (B := B) (n : ℤ)).hom.app U) ≫
        (canonicalRightZeroIso G).hom.app U =
      (derivedTargetIso G S (n : ℤ)).hom.app Y ≫
        (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app U := by
  let L := (stalkColumnIso G S n).hom ≫ (stalkColumnCoordinates G S n).hom
  let R := (isoWhiskerLeft (columnStalk n) (derivedTargetIso G S n)).hom ≫
    (rightDerivedStalkHomologyIso G n).hom
  have hL (V : B) :
      L.app V =
        (derivedEdges G (descendedRow G S) ((columnStalk n).obj V)
          (descended_stalk_quadrant G S V (n : ℤ) (by omega))).column n ≫
          (leftCoordinates G S n).hom.app ((columnStalk n).obj V) ≫
          (rightValue G 0).map ((singlePlusHomologyIso (B := B) (n : ℤ)).hom.app V) ≫
          (canonicalRightZeroIso G).hom.app V := by
    simp only [L, stalkColumnIso, stalkColumnCoordinates, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, NatIso.ofComponents_hom_app, asIso_hom, isoWhiskerLeft_hom,
      whiskerLeft_app, associator_inv_app, isoWhiskerRight_hom, whiskerRight_app,
      leftUnitor_hom_app, Category.id_comp]
    congr 1
    exact congrArg (fun f => (leftCoordinates G S n).hom.app ((columnStalk n).obj V) ≫
      (rightValue G 0).map ((singlePlusHomologyIso (B := B) (n : ℤ)).hom.app V) ≫ f)
      (Category.id_comp ((canonicalRightZeroIso G).hom.app V))
  dsimp only
  rw [← hL]
  change L.app U = R.app U
  let i := Injective.ι U
  have hU : L.app (Injective.under U) = R.app (Injective.under U) := by
    rw [hL]
    exact hI _ inferInstance
  haveI : Mono (G.map i) := by dsimp [i]; infer_instance
  apply (cancel_mono (G.map i)).1
  rw [← L.naturality i, ← R.naturality i, hU]

set_option maxHeartbeats 1000000 in
/-- Both good-truncation maps preserve the relevant cohomology, so the comparison
on the zero column is determined by the one on a stalk in that same degree. -/
lemma leftCoordinates_naturality [PreservesFiniteLimits G] (n : ℕ)
    (hStalk : ∀ U : B,
      let Y := (columnStalk n).obj U
      (derivedEdges G (descendedRow G S) Y
        (descended_stalk_quadrant G S U (n : ℤ) (by omega))).column n ≫
          (leftCoordinates G S n).hom.app Y ≫
          (rightValue G 0).map ((singlePlusHomologyIso (B := B) (n : ℤ)).hom.app U) ≫
          (canonicalRightZeroIso G).hom.app U =
        (derivedTargetIso G S (n : ℤ)).hom.app Y ≫
          (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app U)
    (Y : DerivedCategory.Plus B) :
    (columnPageIso G S n).hom.app Y =
      (leftCoordinates G S n).hom.app Y ≫
        (canonicalRightZeroIso G).hom.app ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj Y) := by
  let P := columnPage G S n
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let T := ((tB).truncLE (n : ℤ)).obj Y
  let V := H.obj Y
  let U := (columnStalk n).obj V
  let i : T ⟶ Y := ((tB).truncLEι (n : ℤ)).app Y
  let j : T ⟶ U := (truncationToSingle (n : ℤ)).app Y
  let a := (singlePlusHomologyIso (B := B) (n : ℤ)).app V
  let c := (leftCoordinates G S n).hom
  let z := (canonicalRightZeroIso G).hom.app V
  let b := (derivedEdges G (descendedRow G S) U
    (descended_stalk_quadrant G S V _ (by omega))).column n
  let e := (derivedTargetIso G S (n : ℤ)).hom.app U
  let k := (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app V
  haveI : IsIso (P.map i) :=
    columnPage_map_isIso G S n i (homology_truncLEι_isIso Y _ _ (le_refl _))
  haveI : IsIso b := descended_stalk_column_isIso G S V n
  have hi : P.map i ≫ c.app Y = c.app T ≫ (rightValue G 0).map (H.map i) :=
    c.naturality i
  have hj : P.map j ≫ c.app U = c.app T ≫ (rightValue G 0).map (H.map j) :=
    c.naturality j
  have hji : H.map j ≫ a.hom = H.map i := truncationToSingle_normalization (n : ℤ) Y
  have hb : b ≫ c.app U ≫ (rightValue G 0).map a.hom ≫ z = e ≫ k := hStalk V
  simp only [columnPageIso, columnPageTruncLEIso, columnPageTruncToStalkIso,
    stalkColumnIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, asIso_hom, asIso_inv,
    NatIso.isIso_inv_app, whiskerRight_app, whiskerLeft_app, isoWhiskerLeft_hom,
    NatIso.ofComponents_inv_app]
  change inv (P.map i) ≫ P.map j ≫ inv b ≫ e ≫ k = c.app Y ≫ z
  apply (cancel_epi (P.map i)).1
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← hb, IsIso.inv_hom_id_assoc, reassoc_of% hj, ← Functor.map_comp_assoc, hji,
    reassoc_of% hi]

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05ColumnIdentification


noncomputable section G05ZeroEdges
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.G05FilteredEdges
open HypercohomologyDerivedNaturality GrothendieckSpectralSequence CartanEilenbergData
open FiniteFiltrationConvergence
universe u v u' v' w w'
variable {B : Type u} {C : Type u'}
  [Category.{v} B] [Abelian B] [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive]

/-- The two edges at total degree zero are mutually inverse. -/
theorem derived_zero_row_column (R : DerivedRow G) (Y : DerivedCategory.Plus B)
    (hQ : FirstQuadrant (R.derived.obj Y)) :
    (derivedEdges G R Y hQ).row 0 ≫ (derivedEdges G R Y hQ).column 0 = 𝟙 _ := by
  letI := Localization.essSurj (DerivedCategory.Plus.Q (C := B)) (CochainComplex.Plus.quasiIso B)
  let e := realization G R Y
  let M := R.system.data (DerivedCategory.Plus.Q.objPreimage Y) (R.resolution _)
  let k := closedToPage M.filtration M.pages 2 (↑(0 : ℕ) : ℤ) (↑(0 : ℕ) : ℤ) ≫
    e.inv.page 0 (↑(0 : ℕ) : ℤ) (↑(0 : ℕ) : ℤ)
  let hq := realizedQuadrant G M e hQ
  haveI : Epi (closedToPage M.filtration M.pages 2 0 0) :=
    EdgesAndFiveTerms.row_closedToPage_epi M.filtration M.pages M.convergence.finite hq 0
  haveI : IsIso (e.inv.page 0 0 0) := ((pageEval 0 0 0).mapIso e).isIso_inv
  haveI : Epi k := by dsimp only [k]; infer_instance
  have hr := realized_row_formula G M e hQ 0
  have hc := realized_column_formula G M e hQ 0
  apply (cancel_epi k).1
  change k ≫ (derivedEdges G R Y hQ).row 0 ≫ (derivedEdges G R Y hQ).column 0 =
    k ≫ 𝟙 ((R.derived.obj Y).page 0 (↑(0 : ℕ) : ℤ) (↑(0 : ℕ) : ℤ))
  rw [Category.comp_id, ← Category.assoc]
  change (k ≫ (realizedEdges G M e hQ).row 0) ≫ (realizedEdges G M e hQ).column 0 = k
  rw [show k ≫ (realizedEdges G M e hQ).row 0 =
      EdgesAndFiveTerms.ambientClass M.filtration 0 0 ≫ (M.targetIso 0).hom ≫ e.inv.target 0
    from hr]
  simpa only [k, Category.assoc, Int.natCast_zero] using hc

end AdvancedHomologicalAlgebra.G05FilteredEdges
end G05ZeroEdges

noncomputable section G05ColumnStalk
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
universe u v u' v' w w'
variable {B : Type u} {C : Type u'}
  [Category.{v} B] [Abelian B] [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive]

lemma truncationToSingle_app_stalk (n : ℤ) (U : B) :
    (truncationToSingle (B := B) n).app ((DerivedCategory.Plus.singleFunctor B n).obj U) =
      (DerivedCategory.Plus.TStructure.t.truncLEι n).app ((DerivedCategory.Plus.singleFunctor B n).obj U) ≫
        (DerivedCategory.Plus.singleFunctor B n).map ((singlePlusHomologyIso (B := B) n).app U).inv := by
  let S := DerivedCategory.Plus.singleFunctor B n
  let H := DerivedCategory.Plus.homologyFunctor B n
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let Y := S.obj U
  let X := (t.truncLE n).obj Y
  let Z := S.obj (H.obj Y)
  let ε := singlePlusHomologyIso (B := B) n
  let f : X ⟶ Z := (truncationToSingle (B := B) n).app Y
  let g : X ⟶ Z := (t.truncLEι n).app Y ≫ S.map (ε.app U).inv
  change f = g
  have h : H.map f = H.map g := by
    apply (cancel_mono (ε.app (H.obj Y)).hom).1
    rw [show H.map f ≫ (ε.app (H.obj Y)).hom = H.map ((t.truncLEι n).app Y)
      from truncationToSingle_normalization n Y]
    change H.map ((t.truncLEι n).app Y) =
      H.map ((t.truncLEι n).app Y ≫ S.map (ε.app U).inv) ≫ (ε.app (H.obj Y)).hom
    rw [Functor.map_comp, Category.assoc]
    have hε := ε.hom.naturality (ε.app U).inv
    change H.map (S.map (ε.app U).inv) ≫ (ε.app (H.obj Y)).hom =
      (ε.app U).hom ≫ (ε.app U).inv at hε
    rw [hε, Iso.hom_inv_id]
    exact (Category.comp_id _).symm
  haveI : Y.IsGE n := by dsimp only [Y, S]; infer_instance
  haveI : X.IsGE n := by dsimp only [X]; infer_instance
  haveI : X.IsLE n := by dsimp only [X]; infer_instance
  haveI : Z.IsGE n := by dsimp only [Z, S]; infer_instance
  haveI : Z.IsLE n := by dsimp only [Z, S]; infer_instance
  apply DerivedCategory.Plus.ι.map_injective
  apply pure_homology_map_injective n
  exact h

lemma derivedTruncationEdge_app_stalk [PreservesFiniteLimits G] (n : ℤ) (U : B) :
    (derivedTruncationEdge G n).app ((DerivedCategory.Plus.singleFunctor B n).obj U) =
      (rightDerivedStalkHomologyIso G n).hom.app U ≫
        G.map ((singlePlusHomologyIso (B := B) n).app U).inv := by
  let S := DerivedCategory.Plus.singleFunctor B n
  let H := DerivedCategory.Plus.homologyFunctor B n
  let L := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let Y := S.obj U
  let ε := singlePlusHomologyIso (B := B) n
  let k := rightDerivedStalkHomologyIso G n
  let i := (t.truncLEι n).app Y
  haveI : IsIso (L.map i) := isIso_homology_rightDerived_truncLEι G Y n
  simp only [derivedTruncationEdge, homology_rightDerived_truncLEIso,
    NatTrans.comp_app, asIso_inv, NatIso.isIso_inv_app, whiskerRight_app,
    whiskerLeft_app, associator_hom_app, isoWhiskerLeft_hom, Category.id_comp]
  change inv (L.map i) ≫ L.map ((truncationToSingle n).app Y) ≫
    k.hom.app (H.obj Y) = k.hom.app U ≫ G.map (ε.app U).inv
  rw [show (truncationToSingle n).app Y = i ≫ S.map (ε.app U).inv
      from truncationToSingle_app_stalk n U,
    Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc]
  exact k.hom.naturality (ε.app U).inv

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05ColumnStalk


noncomputable section G05CornerComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits G] (S : System G)

theorem normalizedCorner (X : A)
    (hF : ((singlePlusHomologyIso (B := B) 0).app (F.obj X)).inv ≫
      (DerivedCategory.Plus.homologyFunctor B 0).map ((stalkToDerived F).app X) =
        (canonicalRightZeroIso F).inv.app X)
    (hG : rightDerivedStalkHomologyIso G 0 = canonicalRightZeroIso G)
    (hQ : G05FilteredEdges.FirstQuadrant
      ((descendedRow G S).derived.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) :
    (normalizedFirstPageIso F G S 0).hom.app X ≫
      (rightValue G 0).map ((canonicalRightZeroIso F).inv.app X) ≫
        (canonicalRightZeroIso G).hom.app ((rightValue F 0).obj X) =
    (columnPageIso G S 0).hom.app
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  let S₀ := DerivedCategory.Plus.singleFunctor B 0
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let L := G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C 0
  let U := S₀.obj (F.obj X)
  let Y := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let f : U ⟶ Y := (stalkToDerived F).app X
  let χ := derivedTruncationEdge G 0
  let ε := (singlePlusHomologyIso (B := B) 0).app (F.obj X)
  let eF := (canonicalRightZeroIso F).inv.app X
  let eG := canonicalRightZeroIso G
  let μ := (normalizedFirstPageIso F G S 0).hom.app X
  let ν := (columnPageIso G S 0).hom.app Y
  let e := (derivedTargetIso G S 0).hom.app Y
  let E := derivedEdges G (descendedRow G S) Y hQ
  haveI : Y.IsGE 0 := preservesLowerBounds A B F _ 0 (by infer_instance)
  have hi : L.map f ≫ χ.app Y = eG.hom.app (F.obj X) ≫ G.map eF := by
    have h := χ.naturality f
    change L.map f ≫ χ.app Y = χ.app U ≫ G.map (H.map f) at h
    rw [h, show χ.app U = (rightDerivedStalkHomologyIso G 0).hom.app (F.obj X) ≫ G.map ε.inv
        from derivedTruncationEdge_app_stalk G 0 (F.obj X), hG,
      Category.assoc, ← Functor.map_comp, show ε.inv ≫ H.map f = eF from hF]
  have hr : μ ≫ L.map f = E.row 0 ≫ e := normalizedFirstPageIso_row F G S X 0 hQ
  have hc : E.column 0 ≫ ν = e ≫ χ.app Y := column_edge_comparison G S Y 0
  calc
    μ ≫ (rightValue G 0).map eF ≫ eG.hom.app (H.obj Y) =
        μ ≫ eG.hom.app (F.obj X) ≫ G.map eF := by
      rw [show (rightValue G 0).map eF ≫ eG.hom.app (H.obj Y) =
          eG.hom.app (F.obj X) ≫ G.map eF from eG.hom.naturality eF]
    _ = (μ ≫ L.map f) ≫ χ.app Y := by rw [Category.assoc, hi]
    _ = E.row 0 ≫ E.column 0 ≫ ν := by
      rw [hr, Category.assoc, ← hc]
    _ = ν := by
      rw [← Category.assoc, show E.row 0 ≫ E.column 0 = 𝟙 _
          from derived_zero_row_column G (descendedRow G S) Y hQ, Category.id_comp]

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05CornerComparison

noncomputable section G05StalkRepresentatives
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open HomologicalComplex
universe u v
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open PageCohomology FilteredPage

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} (Fr : Filtration K) (D : F03Specs.PageData Fr)
  (N : PageCohomology.Data Fr D)

/-- Compute the page two comparison on an actual representative in a given row. -/
lemma secondPageIso_representative (J : CochainComplex C ℤ) (a n : ℤ)
    (e : PageCohomology.shortComplex Fr D 1 (by omega) a n ≅ J.sc' a (a+1) (a+1+1))
    {T : C} (x : T ⟶ J.X (a+1)) (hx : x ≫ J.d (a+1) (a+1+1) = 0)
    (b : T ⟶ (FilteredPage.almost Fr 2 (a+1) (n+1) : C))
    (hb : b ≫ PageCohomology.nextRepresentative Fr D 1 (a+1) (n+1) ≫
        e.hom.τ₂ = x) :
    (b ≫ FilteredPage.toPage Fr 2 (a+1) (n+1) (D.containment 2 (a+1) (n+1))) ≫
      (N.nextIso 1 (by omega) a n).hom ≫ (ShortComplex.homologyMapIso e).hom ≫
        (J.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).inv =
      J.liftCycles x (a+1+1) (by simp) hx ≫ J.homologyπ (a+1) := by
  have hn : FilteredPage.toPage Fr 2 (a+1) (n+1) (D.containment 2 (a+1) (n+1)) ≫
        (N.nextIso 1 (by omega) a n).hom = _ := N.nextIso_formula 1 (by omega) a n
  let S := PageCohomology.shortComplex Fr D 1 (by omega) a n
  let h := (J.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).inv
  have he := congrArg (fun f : (FilteredPage.almost Fr 2 (a+1) (n+1) : C) ⟶ S.homology =>
    b ≫ f ≫ (ShortComplex.homologyMapIso e).hom ≫ h) hn
  simp only [Category.assoc] at he ⊢
  rw [he]
  simp only [ShortComplex.homologyMapIso_hom, ShortComplex.homologyπ_naturality_assoc,
    ]
  dsimp only [h]
  simp only [HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono (J.iCycles (a+1))).1
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    ShortComplex.cyclesMap_i, ShortComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
  simpa only [PageCohomology.nextRepresentative, FilteredPage.toPage, Category.assoc] using hb

open CartanEilenbergData CartanEilenbergTotalization DoubleTotalization
open DoubleComplexFirstPages FiniteDiagonalFiltrations FiniteFiltrationConvergence

section SecondPageRepresentative
open RowHypercohomology

universe u' v'
variable {B : Type u'} [Category.{v'} B] [Abelian B]
  (G : B ⥤ C) [G.Additive] {L : CochainComplex B ℤ} (R : ResolutionData L)
  [((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ)]
  (F : Filtration (sumTotal ((mapDouble G).obj R.bicomplex)))
  (hF : HasFiltrationFormula ((mapDouble G).obj R.bicomplex) Prod.snd F)
  (E : F03Specs.PageData F) (P : PageCohomology.Data F E)
  (M : FirstPageComputation G R F hF E)

private lemma transported_closedToPage (r p n n' : ℤ) (h : n = n') :
    eqToHom (congrArg (fun i => (closed F p i : C)) h) ≫
      closedToPage F E r p n' ≫ eqToHom (congrArg (PageCohomology.object F E r p) h.symm) =
    closedToPage F E r p n := by
  subst n'
  simp

private lemma transported_closedToPage_forward (r p n n' : ℤ) (h : n = n') :
    eqToHom (congrArg (fun i => (closed F p i : C)) h) ≫
      closedToPage F E r p n' =
    closedToPage F E r p n ≫ eqToHom (congrArg (PageCohomology.object F E r p) h) := by
  subst n'
  simp

private lemma closedToPage_nextRepresentative (r p n : ℤ) :
    Subobject.ofLE _ _ (closed_le_almost F (r+1) p n) ≫
      PageCohomology.nextRepresentative F E r p n =
    closedToPage F E r p n := by
  simp [PageCohomology.nextRepresentative, closedToPage, ← Category.assoc]

/-- Compute the signed first-page homology comparison on closed representatives. -/
lemma signedSecondPageIso_closedRepresentative (p q : ℤ) {T : C}
    (x : T ⟶ (mappedOriginalColumn G R q).X p)
    (hx : x ≫ (mappedOriginalColumn G R q).d p (p+1) = 0)
    (c : T ⟶ (closed F p (p+q) : C))
    (hc : c ≫ closedToPage F E 1 p (p+q) ≫
      (signedFirstIso G R F hF E M.row M.split p q).hom = x) :
    c ≫ closedToPage F E 2 p (p+q) ≫
      (M.secondPageIso G R F hF E P p q).hom =
        (mappedOriginalColumn G R q).liftCycles x (p+1) (by simp) hx ≫
          (mappedOriginalColumn G R q).homologyπ p := by
  suffices h : ∀ a : ℤ, ∀ {T : C} (x : T ⟶ (mappedOriginalColumn G R q).X (a+1)),
      ∀ (hx : x ≫ (mappedOriginalColumn G R q).d (a+1) (a+1+1) = 0)
      (c : T ⟶ (closed F (a+1) ((a+1)+q) : C)),
      c ≫ closedToPage F E 1 (a+1) ((a+1)+q) ≫
        (signedFirstIso G R F hF E M.row M.split (a+1) q).hom = x →
      c ≫ closedToPage F E 2 (a+1) ((a+1)+q) ≫
        (M.secondPageIso G R F hF E P (a+1) q).hom =
          (mappedOriginalColumn G R q).liftCycles x (a+1+1) (by simp) hx ≫
            (mappedOriginalColumn G R q).homologyπ (a+1) by
    obtain ⟨a, rfl⟩ : ∃ a : ℤ, p = a+1 := ⟨p-1, by omega⟩
    exact h a x hx c hc
  intro a T x hx c hc
  let J := mappedOriginalColumn G R q
  let j := a+1
  have hj : j - 1 = a := by dsimp [j]; omega
  have hi : j+q = a+q+1 := by dsimp [j]; omega
  let c' := c ≫ eqToHom (congrArg (fun i => (closed F j i : C)) hi)
  let b := c' ≫ Subobject.ofLE _ _ (closed_le_almost F 2 j (a+q+1))
  have hb : b ≫ PageCohomology.nextRepresentative F E 1 j (a+q+1) ≫
       (M.signedShortComplex a q).hom.τ₂ = x := by
    rw [M.signedShortComplex_middle]
    change ((c ≫ eqToHom (congrArg (fun i => (closed F j i : C)) hi)) ≫
      Subobject.ofLE _ _ (closed_le_almost F 2 j (a+q+1))) ≫
      PageCohomology.nextRepresentative F E 1 j (a+q+1) ≫
      eqToHom (congrArg (PageCohomology.object F E 1 j) hi.symm) ≫ _ = _
    calc
      _ = c ≫ eqToHom (congrArg (fun i => (closed F j i : C)) hi) ≫
          closedToPage F E 1 j (a+q+1) ≫
          eqToHom (congrArg (PageCohomology.object F E 1 j) hi.symm) ≫
          (signedFirstIso G R F hF E M.row M.split j q).hom := by
        have h := congrArg (fun f => c ≫ eqToHom (congrArg (fun i => (closed F j i : C)) hi) ≫ f ≫
            eqToHom (congrArg (PageCohomology.object F E 1 j) hi.symm) ≫
              (signedFirstIso G R F hF E M.row M.split j q).hom)
            (closedToPage_nextRepresentative G R F E 1 j (a+q+1))
        simp only [Category.assoc] at h ⊢
        exact h
      _ = x := by
        have h := congrArg (fun f => c ≫ f ≫ (signedFirstIso G R F hF E M.row M.split j q).hom)
          (transported_closedToPage G R F E 1 j (j+q) (a+q+1) hi)
        simp only [Category.assoc] at h
        exact h.trans hc
  have hrep := secondPageIso_representative F E P J a (a+q)
    (M.signedShortComplex a q) x hx b hb
  have htransport : (b ≫ FilteredPage.toPage F 2 j (a+q+1) (E.containment 2 j (a+q+1))) =
      c ≫ closedToPage F E 2 j (j+q) ≫
        eqToHom (congrArg (PageCohomology.object F E 2 j) hi) := by
    dsimp only [b, c']
    rw [Category.assoc, Category.assoc]
    change c ≫ eqToHom (congrArg (fun i => (closed F j i : C)) hi) ≫
      closedToPage F E 2 j (a+q+1) = _
    simpa only [Category.assoc] using
      congrArg (fun f => c ≫ f) (transported_closedToPage_forward G R F E 2 j (j+q) (a+q+1) hi)
  rw [htransport] at hrep
  -- Unfold the index transport in the definition at p = a+1.
  have haux (a' : ℤ) (h : a'+1 = a+1) :
      c ≫ closedToPage F E 2 (a+1) ((a+1)+q) ≫
        eqToHom (congrArg₂ (PageCohomology.object F E 2) h.symm
          (show (a+1)+q = a'+q+1 by omega)) ≫
        (P.nextIso 1 (by omega) a' (a'+q)).hom ≫
        (ShortComplex.homologyMapIso (M.signedShortComplex a' q)).hom ≫
        (J.homologyIsoSc' a' (a'+1) (a'+1+1) (by simp) (by simp)).inv ≫
        eqToHom (congrArg (fun i => J.homology i) h) =
      J.liftCycles x (a+1+1) (by simp) hx ≫ J.homologyπ (a+1) := by
    have he : a' = a := by omega
    subst a'
    simp only [eqToHom_refl, Category.comp_id, Category.assoc] at hrep ⊢
    exact hrep
  simp only [FirstPageComputation.secondPageIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  exact haux (a + 1 - 1) (by omega)


end SecondPageRepresentative

section Bottom
variable (I : DoubleComplex C)
  (hI : ∀ p : ℤ, IsZero ((I.X (-1)).X p))

include hI in
private lemma row_homologyπ_iso (p : ℤ) : IsIso ((I.flip.X p).homologyπ 0) :=
  (I.flip.X p).isIso_homologyπ (-1) 0 (by simp) ((hI p).eq_of_src _ _)

private def horizontalHomologyInclusion (p : ℤ) :
    ((I.flip.X p).homology 0) ⟶ (I.X 0).X p := by
  letI := row_homologyπ_iso I hI p
  exact inv ((I.flip.X p).homologyπ 0) ≫ (I.flip.X p).iCycles 0

@[reassoc]
private lemma horizontalHomologyInclusion_comp_homologyπ (p : ℤ) :
    (I.flip.X p).homologyπ 0 ≫ horizontalHomologyInclusion I hI p = (I.flip.X p).iCycles 0 := by
  haveI := row_homologyπ_iso I hI p
  simp [horizontalHomologyInclusion]

private lemma horizontalHomologyInclusion_d (p : ℤ) :
    horizontalHomologyInclusion I hI p ≫ (I.d 0 1).f p = 0 := by
  haveI := row_homologyπ_iso I hI p
  change (inv ((I.flip.X p).homologyπ 0) ≫ (I.flip.X p).iCycles 0) ≫
    (I.flip.X p).d 0 1 = 0
  simp only [Category.assoc, iCycles_d, comp_zero]

private def horizontalHomologyColumnInclusion :
    invariantColumn I (HomologicalComplex.homologyFunctor C (.up ℤ) 0) ⟶ I.X 0 where
  f := horizontalHomologyInclusion I hI
  comm' p p' _ := by
    apply (cancel_epi ((I.flip.X p).homologyπ 0)).1
    change (I.flip.X p).homologyπ 0 ≫
        horizontalHomologyInclusion I hI p ≫ ((I.flip.d p p').f 0) =
      (I.flip.X p).homologyπ 0 ≫ homologyMap (I.flip.d p p') 0 ≫
        horizontalHomologyInclusion I hI p'
    rw [← Category.assoc, horizontalHomologyInclusion_comp_homologyπ,
      homologyπ_naturality_assoc, horizontalHomologyInclusion_comp_homologyπ]
    exact (cyclesMap_i (I.flip.d p p') 0).symm

variable [I.HasTotal (.up ℤ)]

private def bottomCohomologyToTotal :
    invariantColumn I (HomologicalComplex.homologyFunctor C (.up ℤ) 0) ⟶ sumTotal I where
  f p := horizontalHomologyInclusion I hI p ≫ sumInjection I 0 p p (zero_add p)
  comm' p p' hp := by
    have hh : p' = p+1 := by simpa using hp.symm
    subst p'
    have hD : sumInjection I 0 p p (zero_add p) ≫ (sumTotal I).d p (p+1) =
        (I.d 0 1).f p ≫ sumInjection I 1 p (p+1) (by omega) +
        (I.X 0).d p (p+1) ≫ sumInjection I 0 (p+1) (p+1) (zero_add _) := by
      change _ ≫ (HomologicalComplex₂.D₁ I (.up ℤ) p (p+1) +
          HomologicalComplex₂.D₂ I (.up ℤ) p (p+1)) = _
      rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
      rw [HomologicalComplex₂.d₁_eq _ _ (i₁' := 1) (by simp), 
        HomologicalComplex₂.d₂_eq _ _ _ (i₂' := p+1) (by simp)]
      · simp
      · change 0 + (p+1) = p+1
        omega
      · change 1 + p = p+1
        omega
    simp only [Category.assoc, hD, Preadditive.comp_add,
      reassoc_of% (horizontalHomologyInclusion_d I hI p), zero_comp, zero_add]
    have hc := (horizontalHomologyColumnInclusion I hI).comm p (p+1)
    change horizontalHomologyInclusion I hI p ≫ (I.X 0).d p (p+1) = _ at hc
    rw [← Category.assoc, hc, Category.assoc]
    rfl

end Bottom

section StalkModel
open HypercohomologyDerivedNaturality RowHypercohomology
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u' v' w w'
variable {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} B] [EnoughInjectives C]
  (G : C ⥤ B) [G.Additive]
  (X : C)
local notation "Stk" => CochainComplex.singleFunctor C 0
local notation "K₀" U => (cohomologyStalk U)
variable (R : ResolutionData (K₀ X).obj) (M : HypercohomologyDerivedNaturality.Data G (K₀ X) R)
  (hR : ∀ p : ℤ, IsZero ((R.bicomplex.X (-1)).X p))

include hR in
private def bottomStalkColumnMap :
    letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    (⟨cohomologyColumn R 0, (M.secondComparison.column 0).bounded⟩ :
      CochainComplex.Plus C) ⟶ ⟨sumTotal R.bicomplex, M.targetComparison.totalBound⟩ :=
  (CochainComplex.plus C).homMk (@bottomCohomologyToTotal _ _ _ R.bicomplex hR M.sourceTotal)

private lemma bottomStalkColumnMap_aug :
    letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    (M.secondComparison.column 0).augmentation ≫ bottomStalkColumnMap G X R M hR =
      (CochainComplex.plus C).homMk (X := cohomologyStalk ((K₀ X).obj.homology 0)) (Y := K₀ X)
        ((Stk).map (singleObjHomologySelfIso (.up ℤ) 0 X).hom) ≫
      M.targetComparison.augmentation := by
  letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
  letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
  dsimp only
  apply (CochainComplex.plus C).hom_ext
  apply HomologicalComplex.from_single_hom_ext
  change (M.secondComparison.column 0).augmentation.hom.f 0 ≫
      (bottomStalkColumnMap G X R M hR).hom.f 0 =
    ((Stk).map (singleObjHomologySelfIso (.up ℤ) 0 X).hom).f 0 ≫
      M.targetComparison.augmentation.hom.f 0
  rw [(M.secondComparison.column 0).augmentation_eq, M.targetComparison.augmentation_eq]
  change (_ ≫ homologyMap R.augmentation 0) ≫
      (horizontalHomologyInclusion R.bicomplex hR 0 ≫ sumInjection R.bicomplex 0 0 0 rfl) =
    ((Stk).map (singleObjHomologySelfIso (.up ℤ) 0 X).hom).f 0 ≫ _
  rw [HomologicalComplex.single_map_f_self]
  apply (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((K₀ X).obj.homology 0)).inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi ((K₀ X).obj.homologyπ 0)).1
  rw [homologyπ_naturality_assoc, horizontalHomologyInclusion_comp_homologyπ_assoc,
    cyclesMap_i_assoc]
  change _ = ((HomologicalComplex.single C (.up ℤ) 0).obj X).homologyπ 0 ≫
    (singleObjHomologySelfIso (.up ℤ) 0 X).hom ≫ _
  simp only [homologyπ_singleObjHomologySelfIso_hom_assoc, singleObjCyclesSelfIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

private def bottomMappedColumnMap :
    letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    mappedOriginalColumn G R 0 ⟶ sumTotal ((mapDouble G).obj R.bicomplex) :=
  by
    letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    exact (G.mapHomologicalComplex (.up ℤ)).map (bottomStalkColumnMap G X R M hR).hom ≫
      M.targetComparison.additivity.hom

private lemma bottomMappedColumnMap_f (p : ℤ) :
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    (bottomMappedColumnMap G X R M hR).f p =
      G.map (horizontalHomologyInclusion R.bicomplex hR p) ≫
        sumInjection ((mapDouble G).obj R.bicomplex) 0 p p (zero_add p) := by
  letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
  letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
  change G.map (horizontalHomologyInclusion R.bicomplex hR p ≫
         sumInjection R.bicomplex 0 p p (zero_add p)) ≫
      M.targetComparison.additivity.hom.f p = _
  rw [Functor.map_comp, Category.assoc, M.targetComparison.summands]

private lemma bottomClosedRepresentative_factors (p : ℤ) :
    (closed M.filtration p p).Factors
      ((mappedOriginalColumn G R 0).iCycles p ≫ (bottomMappedColumnMap G X R M hR).f p) := by
  letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
  let J := mappedOriginalColumn G R 0
  let b := bottomMappedColumnMap G X R M hR
  let x := J.iCycles p ≫ b.f p
  apply (Subobject.inf_factors x).2
  constructor
  · apply (Subobject.factors_iff _ _).2
    refine ⟨J.iCycles p ≫ G.map (horizontalHomologyInclusion R.bicomplex hR p) ≫
      summandToStep _ Prod.snd M.filtration M.formula p 0 p p (zero_add p) le_rfl, ?_⟩
    change (J.iCycles p ≫ G.map (horizontalHomologyInclusion R.bicomplex hR p) ≫
      summandToStep _ Prod.snd M.filtration M.formula p 0 p p (zero_add p) le_rfl) ≫
      (M.filtration.piece p p).arrow = x
    simp only [Category.assoc, summandToStep_arrow, x, b, bottomMappedColumnMap_f]
  · apply kernelSubobject_factors
    change (J.iCycles p ≫ b.f p) ≫ _ = _
    rw [Category.assoc, b.comm, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

private def bottomClosedRepresentative (p : ℤ) :
    (mappedOriginalColumn G R 0).cycles p ⟶ (closed M.filtration p p : B) :=
  (closed M.filtration p p).factorThru _
    (bottomClosedRepresentative_factors G X R M hR p)

@[reassoc]
private lemma bottomClosedRepresentative_arrow (p : ℤ) :
    bottomClosedRepresentative G X R M hR p ≫ (closed M.filtration p p).arrow =
      (mappedOriginalColumn G R 0).iCycles p ≫ (bottomMappedColumnMap G X R M hR).f p :=
  Subobject.factorThru_arrow _ _ _

private lemma ambientClass_bottomClosedRepresentative (p : ℤ) :
    bottomClosedRepresentative G X R M hR p ≫ EdgesAndFiveTerms.ambientClass M.filtration p p =
      (mappedOriginalColumn G R 0).homologyπ p ≫ homologyMap (bottomMappedColumnMap G X R M hR) p := by
  let J := mappedOriginalColumn G R 0
  let b := bottomMappedColumnMap G X R M hR
  let c := bottomClosedRepresentative G X R M hR p
  let F := M.filtration
  change c ≫ EdgesAndFiveTerms.ambientClass F p p = J.homologyπ p ≫ homologyMap b p
  change c ≫ (closedClass F p p ≫ (cohomologyPiece F p p).arrow) = _
  rw [closedClass_arrow, homologyπ_naturality]
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono ((HypercohomologyDerivedNaturality.modelComplex G M.toRowModel).iCycles p)).1
  simp only [Category.assoc, liftCycles_i, cyclesMap_i]
  change c ≫ (closed F p p).arrow = _
  exact bottomClosedRepresentative_arrow G X R M hR p

private def bottomClosedRepresentativeReindexed (p : ℤ) :
    (mappedOriginalColumn G R 0).cycles p ⟶ (closed M.filtration p (p+0) : B) :=
  bottomClosedRepresentative G X R M hR p ≫
    eqToHom (congrArg (fun n => (closed M.filtration p n : B)) (add_zero p).symm)

private lemma bottomClosedRepresentative_first (p : ℤ) :
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    bottomClosedRepresentativeReindexed G X R M hR p ≫ closedToPage M.filtration M.pages 1 p (p+0) ≫
      (signedFirstIso G R M.filtration M.formula M.pages
        M.secondComparison.first.row M.secondComparison.first.split p 0).hom =
      (mappedOriginalColumn G R 0).iCycles p := by
  letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
  let F := M.filtration
  let E := M.pages
  let A := M.secondComparison.first
  let J := mappedOriginalColumn G R 0
  let I := R.bicomplex.flip.X p
  let GI := ((mapDouble G).obj R.bicomplex).flip.X p
  let c := bottomClosedRepresentativeReindexed G X R M hR p
  let z := J.iCycles p ≫ G.map (horizontalHomologyInclusion R.bicomplex hR p)
  let a := c ≫ Subobject.ofLE _ _ (closed_le_almost F 1 p (p+0))
  have hz : z ≫ GI.d 0 1 = 0 := by
    change (J.iCycles p ≫ G.map (horizontalHomologyInclusion R.bicomplex hR p)) ≫
      G.map ((R.bicomplex.d 0 1).f p) = 0
    rw [Category.assoc, ← Functor.map_comp, horizontalHomologyInclusion_d, Functor.map_zero, comp_zero]
  have ha : a ≫ (FilteredPage.almost F 1 p (p+0)).arrow =
      z ≫ sumInjection ((mapDouble G).obj R.bicomplex) 0 p (p+0) (by omega) := by
    have ht (m : ℤ) (hm : p = m) :
        (bottomClosedRepresentative G X R M hR p ≫
          eqToHom (congrArg (fun n => (closed F p n : B)) hm)) ≫ (closed F p m).arrow =
            z ≫ sumInjection ((mapDouble G).obj R.bicomplex) 0 p m (by omega) := by
      subst m
      rw [eqToHom_refl, Category.comp_id]
      change bottomClosedRepresentative G X R M hR p ≫ (closed M.filtration p p).arrow = _
      rw [bottomClosedRepresentative_arrow, bottomMappedColumnMap_f]
      exact (Category.assoc _ _ _).symm
    dsimp only [a]
    rw [Category.assoc, Subobject.ofLE_arrow]
    exact ht _ (add_zero p).symm
  have hfirst := A.row.first_formula p 0 (T := J.cycles p) z hz a ha
  haveI := row_homologyπ_iso R.bicomplex hR p
  let w := J.iCycles p ≫ G.map (inv (I.homologyπ 0))
  have hw : GI.liftCycles z 1 (by simp) hz = w ≫
      GI.liftCycles (G.map (I.iCycles 0)) 1 (by simp) (by
        change G.map (I.iCycles 0) ≫ G.map (I.d 0 1) = 0
        rw [← G.map_comp, I.iCycles_d, G.map_zero]) := by
    apply (cancel_mono (GI.iCycles 0)).1
    simp only [Category.assoc, HomologicalComplex.liftCycles_i, w, z]
    rw [← G.map_comp]
    rfl
  have hsplit := A.split.on_cycles (R := R) p 0
  change _ ≫ _ ≫ _ = G.map (I.homologyπ 0) at hsplit
  change c ≫ closedToPage F E 1 p (p+0) ≫ (signedFirstIso G R F M.formula E A.row A.split p 0).hom =
      J.iCycles p
  simp only [signedFirstIso, Preadditive.smul_iso_hom, rawFirstIso, mul_zero, Int.negOnePow_zero,
    one_smul, Iso.trans_hom]
  change c ≫ (Subobject.ofLE _ _ (closed_le_almost F 1 p (p+0)) ≫
      FilteredPage.toPage F 1 p (p+0) (E.containment 1 p (p+0))) ≫
    (A.row.firstIso p 0).hom ≫ (A.split.iso R p 0).hom = _
  rw [← Category.assoc c, ← Category.assoc c]
  change (a ≫ FilteredPage.toPage F 1 p (p+0) (E.containment 1 p (p+0))) ≫
    (A.row.firstIso p 0).hom ≫ (A.split.iso R p 0).hom = _
  rw [Category.assoc a]
  have hfirst' := congrArg (fun t => t ≫ (A.split.iso R p 0).hom) hfirst
  simp only [Category.assoc] at hfirst'
  have hpost : GI.liftCycles z 1 (by simp) hz ≫ GI.homologyπ 0 ≫ (A.split.iso R p 0).hom =
      J.iCycles p := by
    rw [hw]
    simp only [Category.assoc]
    erw [hsplit]
    dsimp only [w]
    erw [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, G.map_id, Category.comp_id]
  simpa only [FilteredPage.toPage, Category.assoc] using hfirst'.trans hpost

private lemma bottomMappedColumnMap_homology (p : ℕ) :
    letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    ((M.secondComparison.column 0).homologyIso G R p).hom ≫
      homologyMap (bottomMappedColumnMap G X R M hR) (p : ℤ) =
    (rightValue G p).map (singleObjHomologySelfIso (.up ℤ) 0 X).hom ≫
      (M.targetComparison.homologyIso (p : ℤ)).hom := by
  letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
  letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
  let W := M.secondComparison.column 0
  let T := M.targetComparison
  let b := bottomStalkColumnMap G X R M hR
  let f : (cohomologyStalk ((K₀ X).obj.homology 0)) ⟶ (K₀ X) :=
    (CochainComplex.plus C).homMk ((Stk).map (singleObjHomologySelfIso (.up ℤ) 0 X).hom)
  let H := DerivedCategory.Plus.homologyFunctor B (p : ℤ)
  have hf : DerivedCategory.Plus.Q.map f =
      (DerivedCategory.Plus.singleFunctor C 0).map
        (singleObjHomologySelfIso (.up ℤ) 0 X).hom := by
    apply DerivedCategory.Plus.ι.map_injective
    rfl
  have hn := ColumnHypercohomology.replacementComparison_naturality G W.model T.model f b
    (bottomStalkColumnMap_aug G X R M hR)
  have h := congrArg H.map hn
  simp only [Functor.map_comp, hf] at h
  change (W.homologyIso G R p).hom ≫
    homologyMap ((G.mapHomologicalComplex (.up ℤ)).map b.hom ≫ T.additivity.hom) (p : ℤ) = _
  simp only [homologyMap_comp, CohomologyColumnComputation.homologyIso, DerivedTotalComparison.homologyIso,
    ReplacementComparison.homologyIso, Iso.trans_hom, Functor.mapIso_hom, homologyFunctor_map]
  change (H.map W.model.iso.hom ≫ _) ≫ _ =
    (H.map (G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map
      (singleObjHomologySelfIso (.up ℤ) 0 X).hom))) ≫ _
  simp only [Category.assoc]
  have hfac := (DerivedCategory.homologyFunctorFactors B (p : ℤ)).hom.naturality
    ((G.mapHomologicalComplex (.up ℤ)).map b.hom)
  change H.map (DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map b)) ≫
    (DerivedCategory.homologyFunctorFactors B (p : ℤ)).hom.app _ =
      (DerivedCategory.homologyFunctorFactors B (p : ℤ)).hom.app _ ≫
        homologyMap ((G.mapHomologicalComplex (.up ℤ)).map b.hom) (p : ℤ) at hfac
  erw [← reassoc_of% hfac, ← reassoc_of% h]
  rfl

include hR in
/-- On a stalk, the filtered bottom edge in the modeled second-page
coordinates is the augmented total computation of the same derived value. -/
lemma bottomStalkModel_formula (p : ℕ) :
    ∃ (T : B) (c : T ⟶ (closed M.filtration p p : B)),
      Epi (c ≫ closedToPage M.filtration M.pages 2 p p) ∧
      c ≫ EdgesAndFiveTerms.ambientClass M.filtration p p ≫ (M.targetIso p).hom =
        c ≫ closedToPage M.filtration M.pages 2 p p ≫
          eqToHom (congrArg (PageCohomology.object M.filtration M.pages 2 (p : ℤ))
            (add_zero (p : ℤ)).symm) ≫ (M.secondIso p 0).hom ≫
          (rightValue G p).map (singleObjHomologySelfIso (.up ℤ) 0 X).hom := by
  letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
  letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
  let J := mappedOriginalColumn G R 0
  let b := bottomMappedColumnMap G X R M hR
  let c := bottomClosedRepresentative G X R M hR (p : ℤ)
  let d := closedToPage M.filtration M.pages 2 (p : ℤ) (p : ℤ)
  let e := eqToIso (congrArg (PageCohomology.object M.filtration M.pages 2 (p : ℤ))
    (add_zero (p : ℤ)).symm)
  let s := M.secondComparison.first.secondPageIso G R M.filtration M.formula M.pages M.next (p : ℤ) 0
  let a := (M.secondComparison.column 0).homologyIso G R (p : ℤ)
  let v := (rightValue G p).map (singleObjHomologySelfIso (.up ℤ) 0 X).hom
  let t := M.targetComparison.homologyIso (p : ℤ)
  have ht : bottomClosedRepresentativeReindexed G X R M hR (p : ℤ) ≫
      closedToPage M.filtration M.pages 2 (p : ℤ) ((p : ℤ)+0) = c ≫ d ≫ e.hom := by
    change (c ≫ _) ≫ _ = _
    rw [Category.assoc]
    exact congrArg (fun f => c ≫ f)
      (transported_closedToPage_forward G R M.filtration M.pages 2 (p : ℤ) (p : ℤ)
        ((p : ℤ)+0) (add_zero (p : ℤ)).symm)
  have hS := signedSecondPageIso_closedRepresentative G R M.filtration M.formula M.pages M.next
    M.secondComparison.first (p : ℤ) 0 (J.iCycles (p : ℤ)) (J.iCycles_d _ _)
      (bottomClosedRepresentativeReindexed G X R M hR (p : ℤ))
      (bottomClosedRepresentative_first G X R M hR (p : ℤ))
  have h1 : c ≫ d ≫ e.hom ≫ s.hom = J.homologyπ (p : ℤ) := by
    have hl := J.liftCycles_i (J.iCycles (p : ℤ)) ((p : ℤ)+1) (by simp) (J.iCycles_d _ _)
    have hId : J.liftCycles (J.iCycles (p : ℤ)) ((p : ℤ)+1) (by simp) (J.iCycles_d _ _) =
        𝟙 _ := by
      apply (cancel_mono (J.iCycles (p : ℤ))).1
      simpa only [Category.id_comp] using hl
    have hA := congrArg (fun f => f ≫ s.hom) ht
    simp only [Category.assoc] at hA
    rw [← hA]
    exact hS.trans (by rw [hId, Category.id_comp])
  have hepi : Epi ((c ≫ d) ≫ (e.hom ≫ s.hom)) := by
    rw [Category.assoc, h1]
    infer_instance
  haveI : Epi (c ≫ d) := (epi_comp_iff_of_isIso (c ≫ d) (e.hom ≫ s.hom)).mp hepi
  refine ⟨J.cycles (p : ℤ), c, inferInstance, ?_⟩
  change c ≫ EdgesAndFiveTerms.ambientClass M.filtration p p ≫ (M.targetIso p).hom =
    c ≫ d ≫ e.hom ≫ (M.secondIso p 0).hom ≫ v
  rw [M.targetIso_eq, M.secondIso_eq]
  change c ≫ EdgesAndFiveTerms.ambientClass M.filtration p p ≫ t.inv =
    c ≫ d ≫ e.hom ≫ (s.hom ≫ a.inv) ≫ v
  have hn : a.hom ≫ homologyMap b (p : ℤ) = v ≫ t.hom :=
    bottomMappedColumnMap_homology G X R M hR p
  have hz : homologyMap b (p : ℤ) ≫ t.inv = a.inv ≫ v := by
    apply (cancel_epi a.hom).1
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hLeft := congrArg (fun f => f ≫ t.inv)
    (ambientClass_bottomClosedRepresentative G X R M hR (p : ℤ))
  have hRight := congrArg (fun f => f ≫ a.inv ≫ v) h1
  simp only [Category.assoc] at hLeft hRight ⊢
  exact hLeft.trans ((congrArg (fun f => J.homologyπ (p : ℤ) ≫ f) hz).trans hRight.symm)

end StalkModel

end AdvancedHomologicalAlgebra.GrothendieckEdges

end G05StalkRepresentatives

noncomputable section G05StalkShift
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open HomologicalComplex
namespace AdvancedHomologicalAlgebra.GrothendieckEdges

universe u v u' v' w w'
variable {B : Type u} [Category.{v} B] [Abelian B]
  {C : Type u'} [Category.{v'} C] [Abelian C]

/-- Shifted comparison of actual single cochain complexes to degree zero. -/
private abbrev singleShift (n : ℤ) (X : B) :
    ShiftedHom ((CochainComplex.singleFunctor B 0).obj X)
      ((CochainComplex.singleFunctor B n).obj X) n :=
  ((CochainComplex.singleFunctors B).shiftIso n 0 n (by simp)).inv.app X

lemma singleShift_homology (n : ℤ) (U : B) :
    (homologyFunctor B (.up ℤ) 0).shiftMap (singleShift n U) 0 n (by simp) ≫
      (singleObjHomologySelfIso (.up ℤ) n U).hom =
    (singleObjHomologySelfIso (.up ℤ) 0 U).hom := by
  let K := (CochainComplex.singleFunctor B 0).obj U
  let L := (CochainComplex.singleFunctor B n).obj U
  let f := singleShift n U
  let e := (shortComplexFunctor B (.up ℤ) 0).map f ≫
    (CochainComplex.shiftShortComplexFunctorIso B n 0 n (by simp)).hom.app L
  have hshift :
      (homologyFunctor B (.up ℤ) 0).shiftMap f 0 n (by simp) =
      ShortComplex.homologyMap e := by
    change HomologicalComplex.homologyMap f 0 ≫
      (CochainComplex.ShiftSequence.shiftIso B n 0 n (by simp)).hom.app L = _
    rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
    exact (ShortComplex.homologyMap_comp _ _).symm
  rw [hshift]
  apply (cancel_epi (K.homologyπ 0)).1
  change (K.sc 0).homologyπ ≫ ShortComplex.homologyMap e ≫ _ = _
  rw [ShortComplex.homologyπ_naturality_assoc]
  change ShortComplex.cyclesMap e ≫ L.homologyπ n ≫ (singleObjHomologySelfIso (.up ℤ) n U).hom =
    K.homologyπ 0 ≫ (singleObjHomologySelfIso (.up ℤ) 0 U).hom
  have hL := homologyπ_singleObjHomologySelfIso_hom (.up ℤ) n U
  have hK := homologyπ_singleObjHomologySelfIso_hom (.up ℤ) 0 U
  change (L.sc n).homologyπ ≫ _ = _ at hL
  change (K.sc 0).homologyπ ≫ _ = _ at hK
  change ShortComplex.cyclesMap e ≫ (L.sc n).homologyπ ≫ _ = (K.sc 0).homologyπ ≫ _
  rw [hL, hK]
  simp only [singleObjCyclesSelfIso_hom]
  change ShortComplex.cyclesMap e ≫ (L.sc n).iCycles ≫ _ = (K.sc 0).iCycles ≫ _
  rw [ShortComplex.cyclesMap_i_assoc]
  congr 1
  change (f.f 0 ≫ (CochainComplex.shiftEval B n 0 n (by simp)).hom.app L) ≫
    (singleObjXSelf (.up ℤ) n U).hom = (singleObjXSelf (.up ℤ) 0 U).hom
  simp [f, singleShift, CochainComplex.singleFunctors, CochainComplex.shiftEval, singleObjXSelf, XIsoOfEq, singleObjXIsoOfEq, eqToHom_trans]
  
section Functor
variable (G : B ⥤ C) [G.Additive]

private abbrev mappedSingleInv (n : ℤ) (U : B) :=
  (singleMapHomologicalComplex G (.up ℤ) n).inv.app U

private lemma map_singleShift (n : ℤ) (U : B) :
    mappedSingleInv G 0 U ≫ (singleShift n U).map (G.mapHomologicalComplex (.up ℤ)) =
      singleShift n (G.obj U) ≫ (mappedSingleInv G n U)⟦n⟧' := by
  ext i
  by_cases h : i = 0
  · subst i
    simp only [ShiftedHom.map, HomologicalComplex.comp_f, mapHomologicalComplex_map_f,
      mapHomologicalComplex_commShiftIso_hom_app_f, Category.comp_id, mappedSingleInv,
      singleMapHomologicalComplex_inv_app_self, CochainComplex.shiftFunctor_map_f']
    simp [singleShift, CochainComplex.singleFunctors, singleObjXSelf,
      singleObjXIsoOfEq, singleMapHomologicalComplex, eqToHom_map, eqToHom_trans]
    change G.map (𝟙 U) ≫ eqToHom _ = eqToHom _
    rw [G.map_id, Category.id_comp]
  · exact (isZero_single_obj_X (.up ℤ) 0 (G.obj U) i h).eq_of_src _ _

private abbrev literalStalk (n : ℤ) (U : B) : CochainComplex.Plus B :=
  ⟨(CochainComplex.singleFunctor B n).obj U, ⟨n, inferInstance⟩⟩

private abbrev literalStalkShift (n : ℤ) (U : B) :
    ShiftedHom (literalStalk 0 U) (literalStalk n U) n :=
  (CochainComplex.Plus.fullyFaithfulι B).preimage
    (singleShift n U ≫ ((CochainComplex.Plus.ι B).commShiftIso n).inv.app (literalStalk n U))

private lemma literalStalkShift_map_ι (n : ℤ) (U : B) :
    (literalStalkShift n U).map (CochainComplex.Plus.ι B) = singleShift n U := by
  rw [ShiftedHom.map, literalStalkShift, Functor.FullyFaithful.map_preimage,
    Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private lemma shiftedMap_naturality {D E : Type*} [Category D] [Category E]
    [HasShift D ℤ] [HasShift E ℤ] {X Y : D} {n : ℤ} (f : ShiftedHom X Y n)
    {L R : D ⥤ E} [L.CommShift ℤ] [R.CommShift ℤ] (τ : L ⟶ R)
    [NatTrans.CommShift τ ℤ] :
    f.map L ≫ (τ.app Y)⟦n⟧' = τ.app X ≫ f.map R := by
  simpa only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using ShiftedHom.map_naturality f τ

private abbrev literalMappedStalkInv (n : ℤ) (U : B) :
    literalStalk n (G.obj U) ⟶ G.mapCochainComplexPlus.obj (literalStalk n U) :=
  (CochainComplex.plus C).homMk (mappedSingleInv G n U)

private lemma map_literalStalkShift (n : ℤ) (U : B) :
    literalMappedStalkInv G 0 U ≫ (literalStalkShift n U).map G.mapCochainComplexPlus =
      literalStalkShift n (G.obj U) ≫ (literalMappedStalkInv G n U)⟦n⟧' := by
  let I := CochainComplex.Plus.ι C
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app _)).1
  let f := literalStalkShift n U
  let y := literalMappedStalkInv G n U
  let g := literalStalkShift n (G.obj U)
  have h := shiftedMap_naturality f G.mapCochainComplexPlusCompι.hom
  simp only [Functor.mapCochainComplexPlusCompι_hom_app, ShiftedHom.comp_map] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  have h' := h.trans (congrArg (fun k => ShiftedHom.map k (G.mapHomologicalComplex (.up ℤ)))
    (literalStalkShift_map_ι n U))
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]
  change I.map (literalMappedStalkInv G 0 U) ≫ (f.map G.mapCochainComplexPlus).map I =
    I.map g ≫ ((I.commShiftIso n).hom.app _) ≫ (I.map y)⟦n⟧'
  rw [← Category.assoc (I.map g)]
  change I.map (literalMappedStalkInv G 0 U) ≫ (f.map G.mapCochainComplexPlus).map I =
    g.map I ≫ (I.map y)⟦n⟧'
  erw [h']
  rw [show g.map I = singleShift n (G.obj U) from literalStalkShift_map_ι _ _]
  exact map_singleShift G n U

section Derived
variable [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C] [EnoughInjectives B]

omit [EnoughInjectives B] in
private lemma literalStalkShift_map_Q (n : ℤ) (U : B) :
    (literalStalkShift n U).map (DerivedCategory.Plus.Q (C := B)) =
      ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (by simp)).inv.app U := by
  let I := DerivedCategory.Plus.ι (C := B)
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app _)).1
  let Q := DerivedCategory.Q (C := B)
  let H := DerivedCategory.Plus.Q (C := B)
  let D := DerivedCategory.Plus.singleFunctors B
  let e := DerivedCategory.Plus.QCompιIso B
  let f := literalStalkShift n U
  change (f.map H).map I = ShiftedHom.map ((D.shiftIso n 0 n (by simp)).inv.app U) I
  have hn := shiftedMap_naturality f e.hom
  simp only [e, DerivedCategory.Plus.QCompιIso_hom_app, ShiftedHom.comp_map] at hn
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hn
  have h' := hn.trans (congrArg (fun k => ShiftedHom.map k Q)
    (literalStalkShift_map_ι n U))
  erw [h']
  let e' := SingleFunctors.liftPostcompIso (DerivedCategory.singleFunctors B)
    I (fun a => D.functor a) (fun _ => Iso.refl _)
  have hs := congr_app (e'.hom.comm n 0 n (by simp)) U
  have hh : (D.postcomp I).shiftIso n 0 n (by simp) =
      (DerivedCategory.singleFunctors B).shiftIso n 0 n (by simp) := by
    apply Iso.ext
    ext V
    have hh := congr_app (e'.hom.comm n 0 n (by simp)) V
    simp only [e', SingleFunctors.liftPostcompIso_hom_hom, Iso.refl_hom,
      NatTrans.comp_app, NatTrans.id_app, whiskerRight_app] at hh
    erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp] at hh
    exact hh
  have h := congrArg (fun t => t.inv.app U) hh
  simp only [SingleFunctors.postcomp, Iso.trans_inv, NatTrans.comp_app, isoWhiskerRight_inv,
    isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app, Iso.symm_inv,
    associator_inv_app, associator_hom_app, Category.comp_id, Category.id_comp] at h
  have hL : (singleShift n U).map Q = ((DerivedCategory.singleFunctors B).shiftIso n 0 n
      (by simp)).inv.app U := by
    simp [Q, ShiftedHom.map, singleShift, DerivedCategory.singleFunctors, SingleFunctors.postcomp]
  exact hL.trans h.symm

private lemma shiftMap_leftComp {D E M : Type*} [Category D] [Category E] [Category M]
    [HasShift D ℤ] [HasShift E ℤ] (L : D ⥤ E) [L.CommShift ℤ] (H : E ⥤ M)
    [H.ShiftSequence ℤ] {X Y : D} {n : ℤ} (f : ShiftedHom X Y n) :
    (L ⋙ H).shiftMap f 0 n (by simp) = H.shiftMap (f.map L) 0 n (by simp) := by
  simp [Functor.shiftMap, Functor.shiftIso, Functor.ShiftSequence.leftComp, Functor.shift,
    ShiftedHom.map, CategoryTheory.Functor.map_comp]

omit [EnoughInjectives B] in
private lemma plus_homology_shiftMap_Q {K L : CochainComplex.Plus C} (n : ℤ)
    (f : ShiftedHom K L n) :
    (DerivedCategory.Plus.homologyFunctor C 0).shiftMap
      (f.map (DerivedCategory.Plus.Q (C := C))) 0 n (by simp) =
      (DerivedCategory.homologyFunctorFactors C 0).hom.app K.obj ≫
      (homologyFunctor C (.up ℤ) 0).shiftMap
        (f.map (CochainComplex.Plus.ι C)) 0 n (by simp) ≫
        (DerivedCategory.homologyFunctorFactors C n).inv.app L.obj := by
  let Q := DerivedCategory.Plus.Q (C := C)
  let I := DerivedCategory.Plus.ι (C := C)
  let e := DerivedCategory.Plus.QCompιIso C
  have hl := shiftedMap_naturality f e.hom
  simp only [e, DerivedCategory.Plus.QCompιIso_hom_app, ShiftedHom.comp_map] at hl
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hl
  change (I ⋙ DerivedCategory.homologyFunctor C 0).shiftMap (f.map Q) 0 n (by simp) = _
  rw [shiftMap_leftComp, hl]
  exact DerivedCategory.shiftMap_homologyFunctor_map_Q _ _ _ _

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

private abbrev derivedStalkShift (n : ℤ) (U : B) :
    ShiftedHom ((DerivedCategory.Plus.singleFunctor B 0).obj U)
      ((DerivedCategory.Plus.singleFunctor B n).obj U) n :=
  ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (by simp)).inv.app U

omit [EnoughInjectives B] in
private lemma derivedStalkShift_homology (n : ℤ) (U : B) :
    (DerivedCategory.Plus.homologyFunctor B 0).shiftMap (derivedStalkShift n U) 0 n (by simp) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app U =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app U := by
  have h := plus_homology_shiftMap_Q n (literalStalkShift n U)
  rw [literalStalkShift_map_Q, literalStalkShift_map_ι] at h
  let e (d : ℤ) := (DerivedCategory.homologyFunctorFactors B d).app
    ((CochainComplex.singleFunctor B d).obj U)
  let f (d : ℤ) := singleObjHomologySelfIso (.up ℤ) d U
  simp only [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    associator_hom_app, whiskerRight_app, whiskerLeft_app,
    DerivedCategory.singleFunctorsPostcompQIso, Functor.mapIso_refl, Iso.refl_hom,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp, Category.id_comp, Category.id_comp]
  change (DerivedCategory.Plus.homologyFunctor B 0).shiftMap (derivedStalkShift n U) 0 n
    (by simp) ≫ (e n).hom ≫ (f n).hom = (e 0).hom ≫ (f 0).hom
  change (DerivedCategory.Plus.homologyFunctor B 0).shiftMap (derivedStalkShift n U) 0 n
    (by simp) = (e 0).hom ≫
      (homologyFunctor B (.up ℤ) 0).shiftMap (singleShift n U) 0 n (by simp) ≫ (e n).inv at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun z => (e 0).hom ≫ z) (singleShift_homology n U)

private lemma homotopyHomology_shiftZero :
    (HomotopyCategory.homologyFunctor C (.up ℤ) 0).isoShiftZero ℤ = Iso.refl _ := by
  apply Iso.ext
  ext K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Functor.ShiftSequence.induced_isoShiftZero_hom_app_obj]
  change _ ≫ 𝟙 _ ≫ _ = _
  simp
  rfl

private lemma derivedHomology_shiftZero :
    (DerivedCategory.homologyFunctor C 0).isoShiftZero ℤ = Iso.refl _ := by
  apply Iso.ext
  apply Localization.natTrans_ext (DerivedCategory.Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  rw [Functor.ShiftSequence.induced_isoShiftZero_hom_app_obj,
    homotopyHomology_shiftZero]
  simp
  rfl

private lemma plusHomology_shiftZero :
    (DerivedCategory.Plus.homologyFunctor C 0).isoShiftZero ℤ = Iso.refl _ := by
  change isoWhiskerLeft (DerivedCategory.Plus.ι (C := C))
    ((DerivedCategory.homologyFunctor C 0).isoShiftZero ℤ) ≪≫ Iso.refl _ = _
  rw [derivedHomology_shiftZero]
  ext
  simp
  rfl

private lemma shiftedStalkValueIso_inv_app (n : ℤ) (U : B) (hn : n ≠ 0) :
    (shiftedStalkValueIso G n).inv.app U =
      (DerivedCategory.Plus.homologyFunctor C 0).shiftMap
        ((derivedStalkShift n U).map G.rightDerivedFunctorPlus) 0 n (by simp) := by
  unfold shiftedStalkValueIso
  simp only [dite_eq_right hn, id_eq, Iso.trans_inv, NatTrans.comp_app,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app, Iso.symm_inv]
  simp only [derivedStalkShift, Functor.shiftMap, ShiftedHom.map, Functor.isoShift,
    plusHomology_shiftZero, Iso.refl_inv, Iso.refl_hom,
    NatTrans.comp_app, NatTrans.id_app, isoWhiskerLeft_hom, whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.comp_id, Category.id_comp]
  dsimp only [Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom, Iso.refl_inv,
    NatTrans.comp_app, whiskerLeft_app, NatTrans.id_app]
  erw [Category.id_comp]
  rfl

lemma mappedStalkIso_hom_app_literal (U : B) :
    (mappedStalkIso G).hom.app U =
      DerivedCategory.Plus.Q.map (literalMappedStalkInv G 0 U) := by
  let I := DerivedCategory.Plus.ι (C := C)
  let H := (FullyFaithful.ofFullyFaithful I).whiskeringRight B
  apply I.map_injective
  have hh := congrArg (fun t => NatTrans.app t U)
    (H.map_preimage (X := G ⋙ DerivedCategory.Plus.singleFunctor C 0)
      (Y := stalkComplex B ⋙ G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q)
      (isoWhiskerLeft G (DerivedCategory.singleFunctorIsoCompQ C 0) ≪≫
       (associator _ _ _).symm ≪≫
       isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).symm _ ≪≫
       associator _ _ _).hom)
  change I.map ((mappedStalkIso G).hom.app U) = _ at hh
  rw [hh]
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, associator_inv_app, associator_hom_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id, DerivedCategory.singleFunctorIsoCompQ_hom_app]
  erw [Category.id_comp]
  rfl

lemma stalkToDerived_app_literal (U : B) :
    (stalkToDerived G).app U =
      DerivedCategory.Plus.Q.map (literalMappedStalkInv G 0 U) ≫
        G.rightDerivedFunctorPlusUnit.app (literalStalk 0 U) := by
  change (mappedStalkIso G).hom.app U ≫ _ = _
  rw [mappedStalkIso_hom_app_literal]
  rfl
  
private lemma map_comp_shifted {D E : Type*} [Category D] [Category E]
    [HasShift D ℤ] [HasShift E ℤ] {X Y Z : D} {n : ℤ} (L : D ⥤ E)
    [L.CommShift ℤ] (f : X ⟶ Y) (g : ShiftedHom Y Z n) :
    ShiftedHom.map (f ≫ g) L = L.map f ≫ g.map L := by
  simp [ShiftedHom.map, CategoryTheory.Functor.map_comp]

private lemma map_shifted_comp {D E : Type*} [Category D] [Category E]
    [HasShift D ℤ] [HasShift E ℤ] {X Y Z : D} {n : ℤ} (L : D ⥤ E)
    [L.CommShift ℤ] (f : ShiftedHom X Y n) (g : Y ⟶ Z) :
    ShiftedHom.map (f ≫ g⟦n⟧') L = f.map L ≫ (L.map g)⟦n⟧' := by
  simp [ShiftedHom.map, CategoryTheory.Functor.map_comp]

private abbrev mappedStalkUnitAt (n : ℤ) (U : B) :
    (DerivedCategory.Plus.singleFunctor C n).obj (G.obj U) ⟶
      G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B n).obj U) :=
  DerivedCategory.Plus.Q.map (literalMappedStalkInv G n U) ≫
    G.rightDerivedFunctorPlusUnit.app (literalStalk n U)

private lemma mappedStalkUnit_shift (n : ℤ) (U : B) :
    derivedStalkShift n (G.obj U) ≫ (mappedStalkUnitAt G n U)⟦n⟧' =
      mappedStalkUnitAt G 0 U ≫ (derivedStalkShift n U).map G.rightDerivedFunctorPlus := by
  let Q := DerivedCategory.Plus.Q (C := C)
  let f := literalStalkShift n U
  have hn := shiftedMap_naturality f G.rightDerivedFunctorPlusUnit
  simp only [ShiftedHom.comp_map] at hn
  rw [show f.map (DerivedCategory.Plus.Q (C := B)) = derivedStalkShift n U
    from literalStalkShift_map_Q n U] at hn
  have hm := congrArg (fun k => ShiftedHom.map k Q) (map_literalStalkShift G n U)
  have hL := map_comp_shifted Q (literalMappedStalkInv G 0 U) (f.map G.mapCochainComplexPlus)
  have hR := map_shifted_comp Q (literalStalkShift n (G.obj U)) (literalMappedStalkInv G n U)
  have h := hL.symm.trans (hm.trans hR)
  rw [literalStalkShift_map_Q] at h
  dsimp only [mappedStalkUnitAt]
  erw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← h, Category.assoc, hn]
  change Q.map (literalMappedStalkInv G 0 U) ≫
    (G.rightDerivedFunctorPlusUnit.app (literalStalk 0 U) ≫
      (derivedStalkShift n U).map G.rightDerivedFunctorPlus) = _
  exact (Category.assoc _ _ _).symm

/-- The actual right-derived unit on a literal stalk uses the normalized
degree-zero unit after the canonical shift, with no sign on that cohomology. -/
lemma shiftedStalkUnit_normalization (n : ℤ) (U : B) :
    (DerivedCategory.Plus.homologyFunctor C n).map (mappedStalkUnitAt G n U) ≫
      (shiftedStalkValueIso G n).hom.app U =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app (G.obj U) ≫
        (degreeZeroUnit G).app U := by
  by_cases hn : n = 0
  · subst n
    have hu := stalkToDerived_app_literal G U
    change (stalkToDerived G).app U = mappedStalkUnitAt G 0 U at hu
    rw [← hu]
    simp only [shiftedStalkValueIso, dite_eq_left rfl, id_eq, Iso.refl_hom, NatTrans.id_app]
    change _ ≫ 𝟙 _ = _ ≫ _ ≫ (DerivedCategory.Plus.homologyFunctor C 0).map
      ((stalkToDerived G).app U)
    erw [Category.comp_id, Iso.hom_inv_id_app_assoc]
  · let H := DerivedCategory.Plus.homologyFunctor C 0
    let s := derivedStalkShift n (G.obj U)
    let f := mappedStalkUnitAt G n U
    let g := mappedStalkUnitAt G 0 U
    let e (i : ℤ) := (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app (G.obj U)
    let t := (shiftedStalkValueIso G n).app U
    have he : H.shiftMap s 0 n (by simp) ≫ (e n).hom = (e 0).hom :=
      derivedStalkShift_homology n (G.obj U)
    have hs := congrArg (fun k => H.shiftMap k 0 n (by simp)) (mappedStalkUnit_shift G n U)
    rw [Functor.shiftMap_comp, Functor.shiftMap_comp'] at hs
    have ht : t.inv = H.shiftMap ((derivedStalkShift n U).map G.rightDerivedFunctorPlus) 0 n
        (by simp) := shiftedStalkValueIso_inv_app G n U hn
    change H.shiftMap s 0 n (by simp) ≫ (DerivedCategory.Plus.homologyFunctor C n).map f =
      H.map g ≫ _ at hs
    rw [← ht] at hs
    haveI : IsIso (H.shiftMap s 0 n (by simp) ≫ (e n).hom) := by
      rw [he]
      infer_instance
    haveI : IsIso (H.shiftMap s 0 n (by simp)) :=
      IsIso.of_isIso_comp_right _ (e n).hom
    apply (cancel_epi (H.shiftMap s 0 n (by simp))).1
    change H.shiftMap s 0 n (by simp) ≫ (DerivedCategory.Plus.homologyFunctor C n).map f ≫
      t.hom = H.shiftMap s 0 n (by simp) ≫ (e n).hom ≫ (degreeZeroUnit G).app U
    erw [← Category.assoc, hs, Category.assoc, t.inv_hom_id, Category.comp_id,
      ← Category.assoc (H.shiftMap s 0 n (by simp)), he]
    have hu := stalkToDerived_app_literal G U
    change (stalkToDerived G).app U = g at hu
    rw [← hu]
    change _ = (e 0).hom ≫ (e 0).inv ≫ H.map ((stalkToDerived G).app U)
    exact ((e 0).hom_inv_id_assoc _).symm

/-- The shifted unit normalization in ordinary single-complex coordinates. -/
lemma shiftedStalkUnit_cochain_normalization (e₀ : rightValue G 0 ≅ G)
    (he₀ : e₀.inv = degreeZeroUnit G) (n : ℤ) (U : B) :
    (singleObjHomologySelfIso (.up ℤ) n (G.obj U)).inv ≫
      homologyMap ((singleMapHomologicalComplex G (.up ℤ) n).inv.app U) n ≫
      (DerivedCategory.homologyFunctorFactors C n).inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor B n).obj U)) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        (G.rightDerivedFunctorPlusUnit.app (literalStalk n U)) ≫
      (shiftedStalkValueIso G n).hom.app U ≫ e₀.hom.app U = 𝟙 (G.obj U) := by
  let K := (CochainComplex.singleFunctor C n).obj (G.obj U)
  let L := (G.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor B n).obj U)
  let f : K ⟶ L := (singleMapHomologicalComplex G (.up ℤ) n).inv.app U
  let H := DerivedCategory.Plus.homologyFunctor C n
  let h := DerivedCategory.homologyFunctorFactors C n
  let u := G.rightDerivedFunctorPlusUnit.app (literalStalk n U)
  let d := (shiftedStalkValueIso G n).hom.app U
  let k := (singleObjHomologySelfIso (.up ℤ) n (G.obj U))
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app (G.obj U)
  have he : e.hom = h.hom.app K ≫ k.hom := by
    simp only [e, DerivedCategory.singleFunctorCompHomologyFunctorIso, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, associator_hom_app,
      whiskerRight_app, whiskerLeft_app, DerivedCategory.singleFunctorsPostcompQIso,
      Functor.mapIso_refl, Iso.refl_hom, NatTrans.id_app, Iso.app_hom]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    rfl
  have hEi : e.inv = k.inv ≫ h.inv.app K := by
    apply (cancel_mono e.hom).1
    rw [e.inv_hom_id, he]
    erw [Category.assoc, Iso.inv_hom_id_app_assoc, k.inv_hom_id]
    rfl
  have hf := h.inv.naturality f
  change homologyMap f n ≫ h.inv.app L =
    h.inv.app K ≫ H.map (DerivedCategory.Plus.Q.map (literalMappedStalkInv G n U)) at hf
  change k.inv ≫ homologyMap f n ≫ h.inv.app L ≫ H.map u ≫ d ≫ e₀.hom.app U = _
  rw [reassoc_of% hf]
  erw [← Category.assoc k.inv, ← hEi, ← CategoryTheory.Functor.map_comp_assoc]
  change e.inv ≫ H.map (mappedStalkUnitAt G n U) ≫ d ≫ e₀.hom.app U = _
  have hh := shiftedStalkUnit_normalization G n U
  change H.map (mappedStalkUnitAt G n U) ≫ d = e.hom ≫ (degreeZeroUnit G).app U at hh
  rw [reassoc_of% hh, e.inv_hom_id_assoc, ← he₀, Iso.inv_hom_id_app]

end Derived

end Functor

end AdvancedHomologicalAlgebra.GrothendieckEdges

end G05StalkShift

noncomputable section G05StalkClasses
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
variable {B : Type u} {C : Type u'} [Category.{v} B] [Abelian B]
  [Category.{v'} C] [Abelian C] (G : B ⥤ C) [G.Additive]

/-- The class of the cycles of a mapped one-term complex agrees with its
canonical stalk cohomology class. -/
lemma mappedStalk_cycle_class (n : ℤ) (U : B) :
    let K := (CochainComplex.singleFunctor B n).obj U
    let A := (G.mapHomologicalComplex (.up ℤ)).obj K
    G.map (singleObjCyclesSelfIso (.up ℤ) n U).inv ≫
      A.liftCycles (G.map (K.iCycles n)) (n+1) (by simp) (by
        change G.map (K.iCycles n) ≫ G.map (K.d n (n+1)) = 0
        rw [← G.map_comp, K.iCycles_d, G.map_zero]) ≫ A.homologyπ n =
      (singleObjHomologySelfIso (.up ℤ) n (G.obj U)).inv ≫
        homologyMap ((singleMapHomologicalComplex G (.up ℤ) n).inv.app U) n := by
  let K := (CochainComplex.singleFunctor B n).obj U
  let A := (G.mapHomologicalComplex (.up ℤ)).obj K
  let J := (CochainComplex.singleFunctor C n).obj (G.obj U)
  let f : J ⟶ A := (singleMapHomologicalComplex G (.up ℤ) n).inv.app U
  let j := singleObjCyclesSelfIso (.up ℤ) n (G.obj U)
  let k := singleObjCyclesSelfIso (.up ℤ) n U
  let h : G.map (K.iCycles n) ≫ A.d n (n+1) = 0 := by
    change G.map (K.iCycles n) ≫ G.map (K.d n (n+1)) = 0
    rw [← G.map_comp, K.iCycles_d, G.map_zero]
  change G.map k.inv ≫ A.liftCycles (G.map (K.iCycles n)) (n+1) (by simp) h ≫ A.homologyπ n =
      (singleObjHomologySelfIso (.up ℤ) n (G.obj U)).inv ≫ homologyMap f n
  have hb : G.map k.inv ≫ A.liftCycles (G.map (K.iCycles n)) (n+1) (by simp) h =
      j.inv ≫ cyclesMap f n := by
    apply (cancel_mono (A.iCycles n)).1
    simp only [Category.assoc, HomologicalComplex.liftCycles_i, cyclesMap_i,
      ← G.map_comp, f, singleMapHomologicalComplex_inv_app_self]
    change G.map (k.inv ≫ K.iCycles n) =
      j.inv ≫ J.iCycles n ≫ _ ≫ G.map (singleObjXSelf (.up ℤ) n U).inv
    erw [singleObjCyclesSelfIso_inv_iCycles, ← Category.assoc j.inv,
      singleObjCyclesSelfIso_inv_iCycles, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (G.map k.inv), hb, Category.assoc,
    ← HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  exact congrArg (fun x => x ≫ homologyMap f n)
    (singleObjCyclesSelfIso_inv_homologyπ (.up ℤ) n (G.obj U))


end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05StalkClasses

noncomputable section G05AugmentedComparisons
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open CartanEilenbergData CartanEilenbergTotalization DoubleTotalization
open FiniteFiltrationConvergence

universe u v u' v' w w'
variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
  [EnoughInjectives B]
  {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w'} C]
  (G : B ⥤ C) [G.Additive]

open private CartanEilenbergTotalization.isIso_unit_on_injectives from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CartanEilenbergTotalization

/-- The actual unit and actual replacement comparison give back the mapped
augmentation in cohomology. -/
lemma replacement_homologyIso_comp_unit {K J : CochainComplex.Plus B} {a : K ⟶ J}
    (M : ReplacementComparison G K J a) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlusUnit.app K) ≫
      (M.homologyIso n).hom =
    (DerivedCategory.homologyFunctorFactors C n).hom.app ((G.mapCochainComplexPlus.obj K).obj) ≫
      homologyMap ((G.mapCochainComplexPlus.map a).hom) n := by
  let H := DerivedCategory.Plus.homologyFunctor C n
  let Q := DerivedCategory.Plus.Q (C := B)
  let Q' := DerivedCategory.Plus.Q (C := C)
  let Gc := G.mapCochainComplexPlus
  let α := G.rightDerivedFunctorPlusUnit
  haveI : IsIso (α.app J) := by
    exact CartanEilenbergTotalization.isIso_unit_on_injectives G J M.injective
  have h : α.app K ≫ M.iso.hom = Q'.map (Gc.map a) := by
    apply (cancel_mono (α.app J)).1
    rw [Category.assoc, M.unit_eq]
    exact (α.naturality a).symm
  change H.map (α.app K) ≫ H.map M.iso.hom ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp, h]
  exact (DerivedCategory.homologyFunctorFactors C n).hom.naturality
    (G.mapCochainComplexPlus.map a).hom

/-- The total comparison, after the actual unit, is the map on cohomology of
the augmented total cochain complex. -/
lemma total_homologyIso_comp_unit {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    [R.bicomplex.HasTotal (.up ℤ)] [((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ)]
    (M : DerivedTotalComparison G K R) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlusUnit.app K) ≫
      (M.homologyIso n).hom =
    (DerivedCategory.homologyFunctorFactors C n).hom.app ((G.mapCochainComplexPlus.obj K).obj) ≫
      homologyMap ((G.mapCochainComplexPlus.map M.augmentation).hom ≫ M.additivity.hom) n := by
  dsimp only [DerivedTotalComparison.homologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, replacement_homologyIso_comp_unit G M.model n, Category.assoc,
    homologyMap_comp]
  rfl

@[reassoc]
lemma total_comparison_augmentation_f {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    [R.bicomplex.HasTotal (.up ℤ)] [((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ)]
    (M : DerivedTotalComparison G K R) (n : ℤ) :
    ((G.mapCochainComplexPlus.map M.augmentation).hom ≫ M.additivity.hom).f n =
      G.map (R.augmentation.f n) ≫ sumInjection ((mapDouble G).obj R.bicomplex) n 0 n (add_zero n) := by
  change G.map (M.augmentation.hom.f n) ≫ M.additivity.hom.f n = _
  rw [M.augmentation_eq, Functor.map_comp, Category.assoc, M.summands]

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05AugmentedComparisons

noncomputable section G05LeftRepresentatives
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open DoubleTotalization CartanEilenbergData CartanEilenbergTotalization
open FiniteFiltrationConvergence RowHypercohomology HypercohomologyDerivedNaturality
open DoubleComplexFirstPages FilteredPage PageCohomology

universe u v u' v' w w'
variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
  [EnoughInjectives B]
  {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w'} C]
  (G : B ⥤ C) [G.Additive]
  {K : CochainComplex.Plus B} {R : ResolutionData K.obj} (M : Data G K R)

set_option quotPrecheck false in
local notation "I" => ((mapDouble G).obj R.bicomplex)
local notation "TG" => (sumTotal I)

/-- A cycle of the original stalk defines a closed representative in the
filtration step of vertical degree zero. -/
lemma leftColumnRepresentative (n : ℤ)
    (c : G.obj (K.obj.cycles n) ⟶ (closed M.filtration 0 (0+n) : C))
    (hc : letI : (I).HasTotal (.up ℤ) := M.toRowModel.total
      c ≫ (closed M.filtration 0 (0+n)).arrow =
        G.map (K.obj.iCycles n ≫ R.augmentation.f n) ≫ sumInjection I n 0 (0+n) (by omega)) :
    letI : (I).HasTotal (.up ℤ) := M.toRowModel.total
    c ≫ closedToPage M.filtration M.pages 1 0 (0+n) ≫
      (signedFirstIso G R M.filtration M.formula M.pages
        M.secondComparison.first.row M.secondComparison.first.split 0 n).hom =
      G.map (K.obj.homologyπ n ≫ homologyMap R.augmentation n) := by
  letI : (I).HasTotal (.up ℤ) := M.toRowModel.total
  let x : G.obj (K.obj.cycles n) ⟶ ((I).X n).X 0 :=
    G.map (K.obj.iCycles n ≫ R.augmentation.f n)
  let A := FilteredPage.almost M.filtration 1 0 (0+n)
  let a : G.obj (K.obj.cycles n) ⟶ (A : C) :=
    c ≫ Subobject.ofLE _ _ (closed_le_almost M.filtration 1 0 (0+n))
  have ha : a ≫ A.arrow = x ≫ sumInjection I n 0 (0+n) (by omega) := by
    simp only [a, A, Category.assoc, Subobject.ofLE_arrow]
    exact hc
  have hx' : x ≫ ((I).d n (n+1)).f 0 = 0 := by
    change G.map (K.obj.iCycles n ≫ R.augmentation.f n) ≫
      G.map ((R.bicomplex.flip.X 0).d n (n+1)) = 0
    rw [← Functor.map_comp, Category.assoc, R.augmentation.comm, ← Category.assoc,
      K.obj.iCycles_d, zero_comp, G.map_zero]
  have hr := M.secondComparison.first.row.first_formula 0 n x hx' a ha
  let J := R.bicomplex.flip.X 0
  let J' := (I).flip.X 0
  let u := cyclesMap R.augmentation n
  have hu : u ≫ J.iCycles n = K.obj.iCycles n ≫ R.augmentation.f n :=
    cyclesMap_i R.augmentation n
  have hv : J'.liftCycles x (n+1) (by simp) hx' =
      G.map u ≫ J'.liftCycles (G.map (J.iCycles n)) (n+1) (by simp) (by
        change G.map (J.iCycles n) ≫ G.map (J.d n (n+1)) = 0
        rw [← G.map_comp, J.iCycles_d, G.map_zero]) := by
    apply (cancel_mono (J'.iCycles n)).1
    simp only [Category.assoc, HomologicalComplex.liftCycles_i, ← G.map_comp, hu, x]
  have hs := M.secondComparison.first.split.on_cycles R 0 n
  change J'.liftCycles _ (n+1) (by simp) _ ≫ J'.homologyπ n ≫
      (M.secondComparison.first.split.iso R 0 n).hom = G.map (J.homologyπ n) at hs
  have hraw : (a ≫ toPage M.filtration 1 0 (0+n) (M.pages.containment 1 0 (0+n)) ≫
    (M.secondComparison.first.row.firstIso 0 n).hom) ≫
      (M.secondComparison.first.split.iso R 0 n).hom =
    G.map (K.obj.homologyπ n ≫ homologyMap R.augmentation n) := by
    rw [hr, Category.assoc, hv, Category.assoc, hs, ← G.map_comp, homologyπ_naturality]
  simpa only [signedFirstIso, rawFirstIso, closedToPage, a, zero_mul, Int.negOnePow_zero,
    Preadditive.smul_iso_hom, one_smul, Iso.trans_hom, Category.assoc] using hraw

/-- The representative formed from an original cycle has the ambient
cohomology class determined by the actual derived unit. -/
lemma leftColumnRepresentative_target (n : ℤ)
    [hclosed : IsIso (closed M.filtration 0 n).arrow] :
    letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
    letI : (I).HasTotal (.up ℤ) := M.toRowModel.total
    let c := (G.map (K.obj.iCycles n ≫ R.augmentation.f n) ≫ sumInjection I n 0 n (add_zero n)) ≫
      inv (closed M.filtration 0 n).arrow
    let A := (G.mapCochainComplexPlus.obj K).obj
    c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom =
      A.liftCycles (G.map (K.obj.iCycles n)) (n+1) (by simp) (by
        change G.map (K.obj.iCycles n) ≫ G.map (K.obj.d n (n+1)) = 0
        rw [← G.map_comp, K.obj.iCycles_d, G.map_zero]) ≫
      A.homologyπ n ≫ (DerivedCategory.homologyFunctorFactors C n).inv.app A ≫
        (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlusUnit.app K) := by
  letI : R.bicomplex.HasTotal (.up ℤ) := M.sourceTotal
  letI : (I).HasTotal (.up ℤ) := M.toRowModel.total
  let e := M.targetComparison
  let t := (G.mapCochainComplexPlus.map e.augmentation).hom ≫ e.additivity.hom
  let c := (G.map (K.obj.iCycles n ≫ R.augmentation.f n) ≫ sumInjection I n 0 n (add_zero n)) ≫
      inv (closed M.filtration 0 n).arrow
  let A := (G.mapCochainComplexPlus.obj K).obj
  have hc : c ≫ (closed M.filtration 0 n).arrow = G.map (K.obj.iCycles n) ≫ t.f n := by
    simp only [c, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [total_comparison_augmentation_f G e n, ← G.map_comp_assoc]
  let b := A.liftCycles (G.map (K.obj.iCycles n)) (n+1) (by simp) (by
    change G.map (K.obj.iCycles n) ≫ G.map (K.obj.d n (n+1)) = 0
    rw [← G.map_comp, K.obj.iCycles_d, G.map_zero])
  have hb : c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n =
      b ≫ A.homologyπ n ≫ homologyMap t n := by
    rw [EdgesAndFiveTerms.ambientClass, closedClass_arrow, homologyπ_naturality,
      ← Category.assoc, ← Category.assoc]
    congr 1
    apply (cancel_mono ((TG).iCycles n)).1
    simp only [Category.assoc, liftCycles_i, liftCycles_i_assoc, cyclesMap_i, b]
    exact hc
  change c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom =
    b ≫ A.homologyπ n ≫ (DerivedCategory.homologyFunctorFactors C n).inv.app A ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlusUnit.app K)
  rw [← Category.assoc, hb, M.targetIso_eq]
  have hr := total_homologyIso_comp_unit G e n
  change _ ≫ (e.homologyIso n).hom =
    (DerivedCategory.homologyFunctorFactors C n).hom.app A ≫ homologyMap t n at hr
  have hi : homologyMap t n ≫ (e.homologyIso n).inv =
      (DerivedCategory.homologyFunctorFactors C n).inv.app A ≫
        (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlusUnit.app K) := by
    apply (cancel_mono (e.homologyIso n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hr,
      Iso.inv_hom_id_app_assoc]
  simp only [Category.assoc, Iso.symm_hom]
  change b ≫ A.homologyπ n ≫ homologyMap t n ≫ (e.homologyIso n).inv = _
  rw [hi]

/-- The degree zero column coordinates send the represented class to the
degree zero derived unit on the original cohomology object. -/
lemma leftColumnRepresentative_page (n : ℤ)
    (c : G.obj (K.obj.cycles n) ⟶ (closed M.filtration 0 (0+n) : C))
    (hc : letI : (I).HasTotal (.up ℤ) := M.toRowModel.total
      c ≫ (closed M.filtration 0 (0+n)).arrow =
        G.map (K.obj.iCycles n ≫ R.augmentation.f n) ≫ sumInjection I n 0 (0+n) (by omega)) :
    let L := cohomologyStalk (K.obj.homology n)
    let A := (G.mapCochainComplexPlus.obj L).obj
    let z : G.obj (K.obj.cycles n) ⟶ A.X 0 := G.map (K.obj.homologyπ n ≫ (singleObjXSelf (.up ℤ) 0 (K.obj.homology n)).inv)
    c ≫ closedToPage M.filtration M.pages 2 0 (0+n) ≫ (M.secondIso 0 n).hom =
      A.liftCycles z 1 (by simp) (by
          have hd : A.d 0 1 = 0 := by
            change G.map (0 : L.obj.X 0 ⟶ L.obj.X 1) = 0
            exact G.map_zero _ _
          rw [hd, comp_zero]) ≫
        A.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app A ≫
          (DerivedCategory.Plus.homologyFunctor C 0).map (G.rightDerivedFunctorPlusUnit.app L) := by
  letI : (I).HasTotal (.up ℤ) := M.toRowModel.total
  let L := cohomologyStalk (K.obj.homology n)
  let A := (G.mapCochainComplexPlus.obj L).obj
  let z := G.map (K.obj.homologyπ n ≫ (singleObjXSelf (.up ℤ) 0 (K.obj.homology n)).inv)
  let e := M.secondComparison.column n
  let J := mappedOriginalColumn G R n
  let φ : A ⟶ J := (G.mapCochainComplexPlus.map e.augmentation).hom
  let x : G.obj (K.obj.cycles n) ⟶ J.X 0 := G.map (K.obj.homologyπ n ≫ homologyMap R.augmentation n)
  have hz : z ≫ φ.f 0 = x := by
    change G.map (K.obj.homologyπ n ≫ (singleObjXSelf (.up ℤ) 0 _).inv) ≫
      G.map (e.augmentation.hom.f 0) = _
    rw [← G.map_comp, e.augmentation_eq, Category.assoc, Iso.inv_hom_id_assoc]
  have hz₀ : z ≫ A.d 0 1 = 0 := by
    have hd : A.d 0 1 = 0 := by
      change G.map (0 : L.obj.X 0 ⟶ L.obj.X 1) = 0
      exact G.map_zero _ _
    rw [hd, comp_zero]
  have hxd : x ≫ J.d 0 1 = 0 := by
    rw [← hz, Category.assoc, φ.comm, ← Category.assoc, hz₀, zero_comp]
  have hfirst : c ≫ closedToPage M.filtration M.pages 1 0 (0+n) ≫
      (signedFirstIso G R M.filtration M.formula M.pages
        M.secondComparison.first.row M.secondComparison.first.split 0 n).hom = x :=
    leftColumnRepresentative G M n c hc
  have hrep := signedSecondPageIso_closedRepresentative G R M.filtration M.formula
    M.pages M.next M.secondComparison.first 0 n x hxd c hfirst
  have hh : J.liftCycles x 1 (by simp) hxd ≫ J.homologyπ 0 =
      A.liftCycles z 1 (by simp) hz₀ ≫ A.homologyπ 0 ≫ homologyMap φ 0 := by
    rw [homologyπ_naturality, ← Category.assoc, liftCycles_comp_cyclesMap]
    congr 1
    apply (cancel_mono (J.iCycles 0)).1
    simpa only [liftCycles_i] using hz.symm
  have hcol : homologyMap φ 0 ≫ ((e.homologyIso G R 0).inv) =
      (DerivedCategory.homologyFunctorFactors C 0).inv.app A ≫
        (DerivedCategory.Plus.homologyFunctor C 0).map (G.rightDerivedFunctorPlusUnit.app L) := by
    have h := replacement_homologyIso_comp_unit G e.model 0
    apply (cancel_mono (e.homologyIso G R 0).hom).1
    simp only [Category.assoc]
    change _ ≫ (e.model.homologyIso 0).inv ≫ (e.model.homologyIso 0).hom =
      _ ≫ _ ≫ (e.model.homologyIso 0).hom
    simp only [Iso.inv_hom_id, Category.comp_id]
    change (DerivedCategory.Plus.homologyFunctor C 0).map (G.rightDerivedFunctorPlusUnit.app L) ≫
      (e.model.homologyIso 0).hom = (DerivedCategory.homologyFunctorFactors C 0).hom.app A ≫
        homologyMap φ 0 at h
    rw [h, Iso.inv_hom_id_app_assoc]
  rw [M.secondIso_eq]
  simp only [SecondPageComputation.iso, Iso.trans_hom, Iso.symm_hom]
  erw [reassoc_of% hrep]
  rw [← Category.assoc]
  change (J.liftCycles x 1 (by simp) hxd ≫ J.homologyπ 0) ≫ (e.homologyIso G R 0).inv = _
  rw [hh]
  simpa only [Category.assoc] using
    congrArg (fun f => A.liftCycles z 1 (by simp) hz₀ ≫ A.homologyπ 0 ≫ f) hcol

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05LeftRepresentatives

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open CartanEilenbergData HomologicalComplex

universe u v
variable {B : Type u} [Category.{v} B] [Abelian B]

private abbrev stalkRows (K : CochainComplex B ℤ) :=
  (CochainComplex.singleFunctor (CochainComplex B ℤ) 0).obj K

private abbrev stalkAugmentation (K : CochainComplex B ℤ) :
    K ⟶ (stalkRows K).X 0 :=
  (singleObjXSelf (.up ℤ) 0 K).inv

private lemma stalkInvariantResolution (K : CochainComplex B ℤ)
    (P : CochainComplex B ℤ ⥤ B) [P.PreservesZeroMorphisms] (h : Injective (P.obj K)) :
    IsInjectiveResolution (P.obj K)
      ((P.mapHomologicalComplex (.up ℤ)).obj (stalkRows K)) (P.map (stalkAugmentation K)) := by
  let J := (P.mapHomologicalComplex (.up ℤ)).obj (stalkRows K)
  let a := P.map (stalkAugmentation K)
  have hz (q : ℤ) (hq : q ≠ 0) : IsZero (J.X q) :=
    P.map_isZero (isZero_single_obj_X (.up ℤ) 0 K q hq)
  have hd (q r : ℤ) : J.d q r = 0 := by
    change P.map ((stalkRows K).d q r) = 0
    rw [CochainComplex.singleFunctor_obj_d, P.map_zero]
  haveI : IsIso a := inferInstanceAs (IsIso (P.map (stalkAugmentation K)))
  refine { zero_neg := fun q hq => hz q (by omega)
           injective := ?_
           mono := inferInstanceAs (Mono a)
           augmentation_d := ?_
           exact_zero := ?_
           exact_pos := ?_ }
  · intro q hq
    by_cases he : q = 0
    · subst q
      exact Injective.of_iso (asIso a) h
    · exact (hz q he).injective
  · change a ≫ J.d 0 1 = 0
    rw [hd, comp_zero]
  · apply ShortComplex.exact_of_f_is_kernel
    apply KernelFork.IsLimit.ofι'
    intro A f _
    refine ⟨f ≫ inv a, ?_⟩
    change (f ≫ inv a) ≫ a = f
    simp
  · intro q hq
    exact HomologicalComplex.ExactAt.of_isZero (K := J) (i := q) (hz q (by omega))

private lemma injectiveStalkTerm (U : B) [Injective U] (n p : ℤ) :
    Injective (((CochainComplex.singleFunctor B n).obj U).X p) := by
  by_cases h : p = n
  · subst p
    exact Injective.of_iso (singleObjXSelf (.up ℤ) n U).symm (inferInstanceAs (Injective U))
  · exact (isZero_single_obj_X (.up ℤ) n U p h).injective

private lemma injectiveStalkBoundary (U : B) (n p : ℤ) :
    Injective ((boundariesFunctor p).obj ((CochainComplex.singleFunctor B n).obj U)) := by
  let f := ((CochainComplex.singleFunctor B n).obj U).d (p - 1) p
  have hf : f = 0 := rfl
  have hfac : factorThruImage f = 0 := by
    apply (cancel_mono (image.ι f)).1
    rw [image.fac, hf, zero_comp]
  have hz : IsZero (image f) := by
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (factorThruImage f), Category.comp_id, hfac,
      zero_comp]
  exact hz.injective

private lemma injectiveStalkCycles (U : B) [Injective U] (n p : ℤ) :
    Injective (((CochainComplex.singleFunctor B n).obj U).cycles p) := by
  let K := (CochainComplex.singleFunctor B n).obj U
  let e := K.iCyclesIso p (p + 1) (by simp) (by rfl)
  exact Injective.of_iso e.symm (injectiveStalkTerm U n p)

private lemma injectiveStalkHomology (U : B) [Injective U] (n p : ℤ) :
    Injective (((CochainComplex.singleFunctor B n).obj U).homology p) := by
  by_cases h : p = n
  · subst p
    exact Injective.of_iso ((homologyFunctorSingleIso B (.up ℤ) n).app U).symm (inferInstanceAs (Injective U))
  · exact (isZero_single_obj_homology (.up ℤ) n U p h).injective

/-- The Cartan–Eilenberg resolution of an injective stalk in one cell. -/
def injectiveStalkResolution (U : B) [Injective U] (n : ℤ) :
    ResolutionData ((CochainComplex.singleFunctor B n).obj U) := by
  let K := (CochainComplex.singleFunctor B n).obj U
  refine {
    bicomplex := HomologicalComplex₂.flip (stalkRows K)
    boundedBelow := ⟨n, ?_⟩
    nonnegative := ?_
    augmentation := stalkAugmentation K
    augmentation_d := ?_
    terms := fun p =>
      stalkInvariantResolution K (eval B (.up ℤ) p) (injectiveStalkTerm U n p)
    boundaries := fun p =>
      stalkInvariantResolution K (boundariesFunctor p) (injectiveStalkBoundary U n p)
    cycles := fun p =>
      stalkInvariantResolution K (cyclesFunctor B (.up ℤ) p) (injectiveStalkCycles U n p)
    cohomology := fun p =>
      stalkInvariantResolution K (homologyFunctor B (.up ℤ) p) (injectiveStalkHomology U n p) }
  · intro p q hp
    change IsZero (((stalkRows K).X q).X p)
    by_cases hq : q = 0
    · subst q
      exact IsZero.of_iso (isZero_single_obj_X (.up ℤ) n U p (ne_of_lt hp))
        ((eval B (.up ℤ) p).mapIso (singleObjXSelf (.up ℤ) 0 K))
    · exact (eval B (.up ℤ) p).map_isZero (isZero_single_obj_X (.up ℤ) 0 K q hq)
  · intro p q hq
    exact (eval B (.up ℤ) p).map_isZero (isZero_single_obj_X (.up ℤ) 0 K q (ne_of_lt hq))
  · intro p
    change (stalkAugmentation K).f p ≫ ((stalkRows K).d 0 1).f p = 0
    rw [CochainComplex.singleFunctor_obj_d, zero_f, comp_zero]

lemma injectiveStalkResolution_support (U : B) [Injective U] (n p q : ℤ) :
    (p ≠ n ∨ q ≠ 0) →
      IsZero (((injectiveStalkResolution U n).bicomplex.X p).X q) := by
  let K := (CochainComplex.singleFunctor B n).obj U
  change (p ≠ n ∨ q ≠ 0) → IsZero (((stalkRows K).X q).X p)
  intro hpq
  by_cases hq : q = 0
  · subst q
    exact IsZero.of_iso (isZero_single_obj_X (.up ℤ) n U p (hpq.resolve_right (by simp)))
      ((eval B (.up ℤ) p).mapIso (singleObjXSelf (.up ℤ) 0 K))
  · exact (eval B (.up ℤ) p).map_isZero (isZero_single_obj_X (.up ℤ) 0 K q hq)

lemma injectiveStalkResolution_augmentation_isIso (U : B) [Injective U] (n p : ℤ) :
    IsIso ((injectiveStalkResolution U n).augmentation.f p) := by
  change IsIso ((eval B (.up ℤ) p).map (stalkAugmentation ((CochainComplex.singleFunctor B n).obj U)))
  infer_instance

end AdvancedHomologicalAlgebra.GrothendieckEdges

end

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open FiniteFiltrationConvergence

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : CochainComplex C ℤ} (F : Filtration K)

/-- If the closed representatives exhaust the degree, their ambient class
surjects onto the cohomology. -/
lemma ambientClass_epi_of_closed (p n : ℤ) [IsIso (closed F p n).arrow] :
    Epi (EdgesAndFiveTerms.ambientClass F p n) := by
  rw [EdgesAndFiveTerms.ambientClass, closedClass_arrow]
  have hd : K.d n (n+1) = 0 := by
    apply (cancel_epi (closed F p n).arrow).1
    rw [closed_d, comp_zero]
  let z := K.liftCycles (closed F p n).arrow (n+1) (by simp) (closed_d F p n)
  have : IsIso (K.iCycles n) := K.isIso_iCycles n (n+1) (by simp) hd
  have : IsIso (z ≫ K.iCycles n) := by
    rw [show z ≫ K.iCycles n = (closed F p n).arrow from liftCycles_i _ _ _ _ _]
    infer_instance
  have : IsIso z := IsIso.of_isIso_comp_right _ (K.iCycles n)
  change Epi (z ≫ K.homologyπ n)
  infer_instance

end AdvancedHomologicalAlgebra.GrothendieckEdges

end
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open DoubleTotalization FiniteDiagonalFiltrations FiniteFiltrationConvergence

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (I : Bicomplex C) [I.HasTotal (ComplexShape.up ℤ)]

/-- A diagonal injection is invertible when all other summands are zero. -/
lemma sumInjection_isIso_of_support (p q n : ℤ) (h : p + q = n)
    (hz : ∀ a b, a + b = n → a ≠ p → IsZero ((I.X a).X b)) :
    IsIso (sumInjection I p q n h) := by
  let f (a b : ℤ) (hb : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (a,b) = n) :
      (I.X a).X b ⟶ (I.X p).X q :=
    if ha : a = p then eqToHom (by
      have hb' : a + b = n := hb
      have hh : b = q := by omega
      rw [ha, hh])
    else 0
  let r : (sumTotal I).X n ⟶ (I.X p).X q := I.totalDesc f
  have hr : sumInjection I p q n h ≫ r = 𝟙 _ := by
    change I.ιTotal (.up ℤ) p q n h ≫ I.totalDesc f = _
    rw [I.ι_totalDesc]
    simp [f]
  refine ⟨⟨r, hr, ?_⟩⟩
  apply HomologicalComplex₂.total.hom_ext
  intro a b hb
  change a + b = n at hb
  by_cases ha : a = p
  · have hh : b = q := by omega
    subst a
    subst b
    change sumInjection I p q n h ≫ (r ≫ sumInjection I p q n h) =
      sumInjection I p q n h ≫ 𝟙 _
    simp [← Category.assoc, hr]
  · exact (hz a b hb ha).eq_of_src _ _

/-- A diagonal without supported terms is zero. -/
lemma sumTotal_X_isZero_of_support (n : ℤ)
    (hz : ∀ a b, a + b = n → IsZero ((I.X a).X b)) : IsZero ((sumTotal I).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  exact (hz a b hab).eq_of_src _ _

/-- The indicated filtration step contains the entire diagonal. -/
lemma filtration_piece_eq_top_of_injection (F : Filtration (sumTotal I))
    (hF : HasFiltrationFormula I Prod.snd F) (a p q n : ℤ) (h : p + q = n)
    (ha : a ≤ q) [IsIso (sumInjection I p q n h)] :
    F.piece a n = ⊤ := by
  let f := DoubleComplexFirstPages.summandToStep I Prod.snd F hF a p q n h ha
  have hf : f ≫ (F.piece a n).arrow = sumInjection I p q n h :=
    DoubleComplexFirstPages.summandToStep_arrow I Prod.snd F hF a p q n h ha
  haveI : IsIso (f ≫ (F.piece a n).arrow) := by rw [hf]; infer_instance
  haveI : Epi (F.piece a n).arrow := epi_of_epi f _
  haveI : IsIso (F.piece a n).arrow := isIso_of_mono_of_epi _
  exact (Subobject.isIso_arrow_iff_eq_top _).1 inferInstance

/-- Over a fully supported filtration step and a zero outgoing target,
every middle term is a closed representative. -/
lemma closed_arrow_isIso_of_support (F : Filtration (sumTotal I))
    (hF : HasFiltrationFormula I Prod.snd F) (a p q n : ℤ) (h : p + q = n)
    (ha : a ≤ q) [IsIso (sumInjection I p q n h)] (hzero : IsZero ((sumTotal I).X (n+1))) :
    IsIso (closed F a n).arrow := by
  apply (Subobject.isIso_arrow_iff_eq_top _).2
  have hd : (sumTotal I).d n (n+1) = 0 := hzero.eq_of_tgt _ _
  change F.piece a n ⊓ kernelSubobject ((sumTotal I).d n (n+1)) = ⊤
  rw [filtration_piece_eq_top_of_injection I F hF a p q n h ha, hd, kernelSubobject_zero, inf_top_eq]

end AdvancedHomologicalAlgebra.GrothendieckEdges

end

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open CartanEilenbergTotalization DoubleTotalization HypercohomologyDerivedNaturality
open FiniteFiltrationConvergence
universe u v u' v' w w'
variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
  [EnoughInjectives B]
  {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w'} C]
  (G : B ⥤ C) [G.Additive]

lemma injectiveStalk_sumInjection_isIso (U : B) [Injective U] (n : ℤ)
    (M : Data G (ordinaryStalk U n) (injectiveStalkResolution U n)) :
    letI := M.toRowModel.total
    IsIso (sumInjection ((mapDouble G).obj (injectiveStalkResolution U n).bicomplex)
      n 0 n (add_zero n)) := by
  letI := M.toRowModel.total
  let R := injectiveStalkResolution U n
  let I := (mapDouble G).obj R.bicomplex
  apply sumInjection_isIso_of_support I
  intro p q hpq hp
  exact G.map_isZero (injectiveStalkResolution_support U n p q (.inl hp))

lemma injectiveStalk_closed_isIso (U : B) [Injective U] (n : ℤ)
    (M : Data G (ordinaryStalk U n) (injectiveStalkResolution U n)) :
    IsIso (closed M.filtration 0 n).arrow := by
  letI := M.toRowModel.total
  let R := injectiveStalkResolution U n
  let I := (mapDouble G).obj R.bicomplex
  letI : IsIso (sumInjection I n 0 n (add_zero n)) :=
    injectiveStalk_sumInjection_isIso G U n M
  apply closed_arrow_isIso_of_support I M.filtration M.formula 0 n 0 n (add_zero n) le_rfl
  apply sumTotal_X_isZero_of_support I
  intro p q hpq
  exact G.map_isZero (injectiveStalkResolution_support U n p q (by omega))

lemma injective_left_representative_epi (U : B) [Injective U] (n : ℤ)
    (M : Data G (ordinaryStalk U n) (injectiveStalkResolution U n))
    [IsIso (closed M.filtration 0 n).arrow]
    (hinj : letI := M.toRowModel.total
      IsIso (sumInjection ((mapDouble G).obj (injectiveStalkResolution U n).bicomplex)
        n 0 n (add_zero n))) :
    letI := M.toRowModel.total
    let K := (ordinaryStalk U n).obj
    let R := injectiveStalkResolution U n
    let c := (G.map (K.iCycles n ≫ R.augmentation.f n) ≫
        sumInjection ((mapDouble G).obj R.bicomplex) n 0 n (add_zero n)) ≫
      inv (closed M.filtration 0 n).arrow
    Epi (c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n) := by
  letI := M.toRowModel.total
  let K := (ordinaryStalk U n).obj
  let R := injectiveStalkResolution U n
  haveI : IsIso (K.iCycles n) := K.isIso_iCycles n (n+1) (by simp) (by rfl)
  haveI : IsIso (R.augmentation.f n) := injectiveStalkResolution_augmentation_isIso U n n
  haveI : IsIso (sumInjection ((mapDouble G).obj R.bicomplex) n 0 n (add_zero n)) := hinj
  haveI : Epi (EdgesAndFiveTerms.ambientClass M.filtration 0 n) :=
    ambientClass_epi_of_closed M.filtration 0 n
  change Epi (((G.map (K.iCycles n ≫ R.augmentation.f n) ≫
    sumInjection ((mapDouble G).obj R.bicomplex) n 0 n (add_zero n)) ≫
      inv (closed M.filtration 0 n).arrow) ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n)
  infer_instance

end AdvancedHomologicalAlgebra.GrothendieckEdges
end

noncomputable section G05ColumnComplete
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open CartanEilenbergData CartanEilenbergTotalization DoubleTotalization
open FiniteFiltrationConvergence FiniteDiagonalFiltrations HypercohomologyDerivedNaturality
open GrothendieckSpectralSequence G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
universe u v u' v' w w'
variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B] [EnoughInjectives B]
  {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w'} C]
  (G : B ⥤ C) [G.Additive]

private lemma mappedStalk_derivedUnit_class (e₀ : rightValue G 0 ≅ G)
    (he₀ : e₀.inv = degreeZeroUnit G) (n : ℤ) (U : B) :
    let K := (ordinaryStalk U n)
    let A := (G.mapCochainComplexPlus.obj K).obj
    A.liftCycles (G.map (K.obj.iCycles n)) (n+1) (by simp) (by
      change G.map (K.obj.iCycles n) ≫ G.map (K.obj.d n (n+1)) = 0
      rw [← G.map_comp, K.obj.iCycles_d, G.map_zero]) ≫ A.homologyπ n ≫
      (DerivedCategory.homologyFunctorFactors C n).inv.app A ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlusUnit.app K) ≫
      (shiftedStalkValueIso G n).hom.app U ≫ e₀.hom.app U =
      G.map (singleObjCyclesSelfIso (.up ℤ) n U).hom := by
  let K := (ordinaryStalk U n)
  let A := (G.mapCochainComplexPlus.obj K).obj
  let H := DerivedCategory.Plus.homologyFunctor C n
  let e := G.mapIso (singleObjCyclesSelfIso (.up ℤ) n U)
  let d := DerivedCategory.homologyFunctorFactors C n
  let us := G.rightDerivedFunctorPlusUnit.app K
  let ss := (shiftedStalkValueIso G n).hom.app U
  let g := A.liftCycles (G.map (K.obj.iCycles n)) (n+1) (by simp) (by
      change G.map (K.obj.iCycles n) ≫ G.map (K.obj.d n (n+1)) = 0
      rw [← G.map_comp, K.obj.iCycles_d, G.map_zero])
  change g ≫ A.homologyπ n ≫ d.inv.app A ≫ H.map us ≫ ss ≫ e₀.hom.app U = e.hom
  apply (cancel_epi e.inv).1
  have hc := mappedStalk_cycle_class G n U
  rw [e.inv_hom_id]
  have hc' := congrArg (fun z => z ≫ d.inv.app A ≫ H.map us ≫ ss ≫ e₀.hom.app U) hc
  simp only [Category.assoc] at hc'
  exact hc'.trans (shiftedStalkUnit_cochain_normalization G e₀ he₀ n U)

set_option maxHeartbeats 1000000 in
private lemma mappedZeroStalk_derivedUnit_class (e₀ : rightValue G 0 ≅ G)
    (he₀ : e₀.inv = degreeZeroUnit G) {U V : B} (f : V ⟶ U) :
    let K := (ordinaryStalk U 0)
    let A := (G.mapCochainComplexPlus.obj K).obj
    let z := G.map (f ≫ (singleObjXSelf (.up ℤ) 0 U).inv)
    A.liftCycles z 1 (by simp) (by
      change _ ≫ G.map (K.obj.d 0 1) = 0
      rw [CochainComplex.singleFunctor_obj_d, G.map_zero, comp_zero]) ≫ A.homologyπ 0 ≫
      (DerivedCategory.homologyFunctorFactors C 0).inv.app A ≫
      (DerivedCategory.Plus.homologyFunctor C 0).map (G.rightDerivedFunctorPlusUnit.app K) ≫
      e₀.hom.app U = G.map f := by
  let K := (ordinaryStalk U 0)
  let A := (G.mapCochainComplexPlus.obj K).obj
  let z := G.map (f ≫ (singleObjXSelf (.up ℤ) 0 U).inv)
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let d := DerivedCategory.homologyFunctorFactors C 0
  let us := G.rightDerivedFunctorPlusUnit.app K
  let e := singleObjCyclesSelfIso (.up ℤ) 0 U
  have hz : z ≫ A.d 0 1 = 0 := by
    change _ ≫ G.map (K.obj.d 0 1) = 0
    rw [CochainComplex.singleFunctor_obj_d, G.map_zero, comp_zero]
  let g := A.liftCycles (G.map (K.obj.iCycles 0)) 1 (by simp) (by
      change G.map (K.obj.iCycles 0) ≫ G.map (K.obj.d 0 1) = 0
      rw [← G.map_comp, K.obj.iCycles_d, G.map_zero])
  have hf : A.liftCycles z 1 (by simp) hz = G.map (f ≫ e.inv) ≫ g := by
    have hi : e.inv ≫ K.obj.iCycles 0 = (singleObjXSelf (.up ℤ) 0 U).inv :=
      singleObjCyclesSelfIso_inv_iCycles (.up ℤ) 0 U
    apply (cancel_mono (A.iCycles 0)).1
    dsimp only [g]
    simp only [Category.assoc, liftCycles_i, ← G.map_comp]
    exact congrArg G.map (congrArg (fun x => f ≫ x) hi).symm
  have hg := mappedStalk_derivedUnit_class G e₀ he₀ 0 U
  have hz0 : (shiftedStalkValueIso G 0).hom.app U = 𝟙 _ := by
    simp [shiftedStalkValueIso]
  have hzero : (shiftedStalkValueIso G 0).hom.app U ≫ e₀.hom.app U = e₀.hom.app U := by
    rw [hz0]
    exact Category.id_comp _
  change g ≫ A.homologyπ 0 ≫ d.inv.app A ≫ H.map us ≫
    (shiftedStalkValueIso G 0).hom.app U ≫ e₀.hom.app U = _ at hg
  have hg' := congrArg (fun t => g ≫ A.homologyπ 0 ≫ d.inv.app A ≫ H.map us ≫ t) hzero
  have hg₀ := hg'.symm.trans hg
  change A.liftCycles z 1 (by simp) hz ≫ A.homologyπ 0 ≫ d.inv.app A ≫ H.map us ≫ e₀.hom.app U = _
  rw [hf]
  have hh := congrArg (fun k => G.map (f ≫ e.inv) ≫ k) hg₀
  simp only [Category.assoc] at hh ⊢
  erw [hh, ← G.map_comp, Category.assoc, e.inv_hom_id, Category.comp_id]


private lemma transportLeftRepresentative {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    (M : Data G K R) (n m : ℤ) (h : n = m)
    {T : C} (c : T ⟶ (closed M.filtration 0 n : C)) :
    (c ≫ eqToHom (congrArg (fun i => (closed M.filtration 0 i : C)) h)) ≫
      closedToPage M.filtration M.pages 2 0 m =
      c ≫ closedToPage M.filtration M.pages 2 0 n ≫
        eqToHom (congrArg (PageCohomology.object M.filtration M.pages 2 0) h) := by
  subst m
  simp

private lemma transportLeftRepresentative_arrow {K : CochainComplex.Plus B} {R : ResolutionData K.obj}
    (M : Data G K R) (n m : ℤ) (h : n = m)
    (c : G.obj (K.obj.cycles n) ⟶ (closed M.filtration 0 n : C))
    (hc : letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
      let I := (mapDouble G).obj R.bicomplex
      let x := G.map (K.obj.iCycles n ≫ R.augmentation.f n)
      c ≫ (closed M.filtration 0 n).arrow = x ≫ sumInjection I n 0 n (add_zero n)) :
    letI : ((mapDouble G).obj R.bicomplex).HasTotal (.up ℤ) := M.toRowModel.total
    let I := (mapDouble G).obj R.bicomplex
    let x := G.map (K.obj.iCycles n ≫ R.augmentation.f n)
    (c ≫ eqToHom (congrArg (fun i => (closed M.filtration 0 i : C)) h)) ≫
      (closed M.filtration 0 m).arrow = x ≫ sumInjection I n 0 m ((add_zero n).trans h) := by
  subst m
  simpa only [eqToHom_refl, Category.comp_id] using hc

-- The single-cell support and augmented computation provide the closed representation.
set_option maxHeartbeats 1900000 in
lemma leftStalkModel_formula [PreservesFiniteLimits G] (U : B) (n : ℕ)
    {R : ResolutionData (ordinaryStalk U (n : ℤ)).obj}
    (M : Data G (ordinaryStalk U (n : ℤ)) R)
    (hclosed : IsIso (closed M.filtration 0 (n : ℤ)).arrow)
    (hepi :
      letI := M.toRowModel.total
      letI := hclosed
      let c := (G.map ((ordinaryStalk U (n : ℤ)).obj.iCycles n ≫ R.augmentation.f n) ≫
        sumInjection ((mapDouble G).obj R.bicomplex) n 0 n (add_zero _)) ≫
          inv (closed M.filtration 0 (n : ℤ)).arrow
      Epi (c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 (n : ℤ))) :
    ∃ (T : C) (c : T ⟶ (closed M.filtration 0 n : C)),
      Epi (c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n) ∧
      c ≫ closedToPage M.filtration M.pages 2 0 n ≫
          (modelSecondCoordinates G M 0 n n (zero_add _)).hom ≫
          (rightValue G 0).map ((homologyFunctorSingleIso B (.up ℤ) n).hom.app U) ≫
          (canonicalRightZeroIso G).hom.app U =
        c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom ≫
          (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app U := by
  letI := M.toRowModel.total
  letI := hclosed
  let K := ordinaryStalk U (n : ℤ)
  let I := (mapDouble G).obj R.bicomplex
  let x := G.map (K.obj.iCycles n ≫ R.augmentation.f n)
  let c := (x ≫ sumInjection I n 0 n (add_zero _)) ≫ inv (closed M.filtration 0 (n : ℤ)).arrow
  let c' := c ≫ eqToHom (congrArg (fun i => (closed M.filtration 0 i : C)) (zero_add (n : ℤ)).symm)
  let e₀ := canonicalRightZeroIso G
  let d := (singleObjHomologySelfIso (.up ℤ) (n : ℤ) U).hom
  let w := (rightDerivedStalkHomologyIso G (n : ℤ)).hom.app U
  have hc : c ≫ (closed M.filtration 0 (n : ℤ)).arrow = x ≫ sumInjection I n 0 n (add_zero _) := by
    dsimp only [c]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hc' := transportLeftRepresentative_arrow G M (n : ℤ) (0+(n : ℤ)) (zero_add _).symm c hc
  have hp := leftColumnRepresentative_page G M (n : ℤ) c' hc'
  have ht := leftColumnRepresentative_target G M (n : ℤ)
  have hrel : c' ≫ closedToPage M.filtration M.pages 2 0 (0+(n : ℤ)) =
      c ≫ closedToPage M.filtration M.pages 2 0 n ≫
        eqToHom (congrArg (PageCohomology.object M.filtration M.pages 2 0) (zero_add (n : ℤ)).symm) :=
    transportLeftRepresentative G M _ _ (zero_add _).symm c
  refine ⟨G.obj (K.obj.cycles (n : ℤ)), c, hepi, ?_⟩
  have htarget : c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom ≫ w =
      G.map (singleObjCyclesSelfIso (.up ℤ) (n : ℤ) U).hom := by
    let A := (G.mapCochainComplexPlus.obj K).obj
    let b := A.liftCycles (G.map (K.obj.iCycles (n : ℤ))) ((n : ℤ)+1) (by simp) (by
      change G.map (K.obj.iCycles (n : ℤ)) ≫ G.map (K.obj.d (n : ℤ) ((n : ℤ)+1)) = 0
      rw [← G.map_comp, K.obj.iCycles_d, G.map_zero])
    let f := (DerivedCategory.homologyFunctorFactors C (n : ℤ)).inv.app A
    let g := (DerivedCategory.Plus.homologyFunctor C (n : ℤ)).map
      (G.rightDerivedFunctorPlusUnit.app K)
    have hNorm : b ≫ A.homologyπ (n : ℤ) ≫ f ≫ g ≫ w =
        G.map (singleObjCyclesSelfIso (.up ℤ) (n : ℤ) U).hom := by
      dsimp only [w, rightDerivedStalkHomologyIso, Iso.trans_hom, NatTrans.comp_app]
      exact mappedStalk_derivedUnit_class G e₀ rfl (n : ℤ) U
    have hT : c ≫ EdgesAndFiveTerms.ambientClass M.filtration 0 n ≫ (M.targetIso n).hom =
        b ≫ A.homologyπ (n : ℤ) ≫ f ≫ g := ht
    have ht' := congrArg (fun k => k ≫ w) hT
    simp only [Category.assoc] at ht' ⊢
    exact ht'.trans hNorm
  have hpage : c' ≫ closedToPage M.filtration M.pages 2 0 (0+(n : ℤ)) ≫ (M.secondIso 0 (n : ℤ)).hom ≫
      e₀.hom.app (K.obj.homology (n : ℤ)) = G.map (K.obj.homologyπ (n : ℤ)) := by
    have hp' := congrArg (fun f => f ≫ e₀.hom.app (K.obj.homology (n : ℤ))) hp
    simp only [Category.assoc] at hp'
    exact hp'.trans (mappedZeroStalk_derivedUnit_class G e₀ rfl (K.obj.homologyπ (n : ℤ)))
  have hd := e₀.hom.naturality d
  have hg : G.map (K.obj.homologyπ (n : ℤ)) ≫ G.map d =
      G.map (singleObjCyclesSelfIso (.up ℤ) (n : ℤ) U).hom := by
    rw [← G.map_comp]
    exact congrArg G.map (homologyπ_singleObjHomologySelfIso_hom (.up ℤ) (n : ℤ) U)
  have hpage' := congrArg (fun f => f ≫ G.map d) hpage
  have hrel' := congrArg (fun f => f ≫ (M.secondIso 0 (n : ℤ)).hom ≫
    (rightValue G 0).map d ≫ e₀.hom.app U) hrel
  simp only [Category.assoc] at hpage' hrel'
  rw [modelSecondCoordinates_hom, homologyFunctorSingleIso_hom_app]
  calc
    _ = c' ≫ closedToPage M.filtration M.pages 2 0 (0+(n : ℤ)) ≫
      (M.secondIso 0 (n : ℤ)).hom ≫ (rightValue G 0).map d ≫ e₀.hom.app U := by
        simpa only [Category.assoc] using hrel'.symm
    _ = c' ≫ closedToPage M.filtration M.pages 2 0 (0+(n : ℤ)) ≫
      (M.secondIso 0 (n : ℤ)).hom ≫ e₀.hom.app (K.obj.homology (n : ℤ)) ≫ G.map d := by
        exact congrArg (fun f => c' ≫ closedToPage M.filtration M.pages 2 0 (0+(n : ℤ)) ≫
          (M.secondIso 0 (n : ℤ)).hom ≫ f) hd
    _ = G.map (singleObjCyclesSelfIso (.up ℤ) (n : ℤ) U).hom := by
      simpa only [Category.assoc] using hpage'.trans hg
    _ = _ := htarget.symm

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05ColumnComplete

noncomputable section G05Assembly
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.GrothendieckEdges
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality G05FilteredEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
variable {C : Type u₃} [Category.{v₃} C] [Abelian C]

private theorem transferFiveTerms {D : RowDiagram C} (E : EdgeData D)
    (hE : FiveTermData E) {X₁ X₂ X₃ X₄ X₅ : C}
    (e₁ : X₁ ≅ D.page 0 1 1) (e₂ : X₂ ≅ D.target 1)
    (e₃ : X₃ ≅ D.page 0 0 1) (e₄ : X₄ ≅ D.page 0 2 2)
    (e₅ : X₅ ≅ D.target 2) :
    ClassicalFiveTerms (e₁.hom ≫ E.row 1 ≫ e₂.inv) (e₂.hom ≫ E.column 1 ≫ e₃.inv)
      (e₃.hom ≫ transgression D ≫ e₄.inv) (e₄.hom ≫ E.row 2 ≫ e₅.inv) := by
  let f := e₁.hom ≫ E.row 1 ≫ e₂.inv
  let g := e₂.hom ≫ E.column 1 ≫ e₃.inv
  let d := e₃.hom ≫ transgression D ≫ e₄.inv
  let h := e₄.hom ≫ E.row 2 ≫ e₅.inv
  haveI := hE.row_mono
  have hfg : f ≫ g = 0 := by
    dsimp only [f, g]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hE.row_column, zero_comp, comp_zero]
  have hgd : g ≫ d = 0 := by
    dsimp only [g, d]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hE.column_d, zero_comp, comp_zero]
  have hdh : d ≫ h = 0 := by
    dsimp only [d, h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hE.d_row, zero_comp, comp_zero]
  exact {
    mono := inferInstanceAs (Mono (e₁.hom ≫ E.row 1 ≫ e₂.inv))
    fg := hfg
    gd := hgd
    dh := hdh
    exact_f_g := exact_conjugate e₁ e₂ e₃ _ _ _ hE.exact_H1 hfg
    exact_g_d := exact_conjugate e₂ e₃ e₄ _ _ _ hE.exact_E01 hgd
    exact_d_h := exact_conjugate e₃ e₄ e₅ _ _ _ hE.exact_E20 hdh }

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (S : System G)

private abbrev Comp := _root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F G

/-- Use the row construction of HA-G04 with the given resolution system. -/
private abbrev compositionPackage
    (hc : ∀ X, IsIso ((Comp F G).app X)) : Package F G := by
  let R := descendedRow G S
  letI := hc
  letI : IsIso (Comp F G) := NatIso.isIso_of_isIso_app _
  refine {
    row := R
    secondIso := fun p q => isoWhiskerLeft F.rightDerivedFunctorPlus (derivedSecondIso G S p q)
    coordinates := rowCoordinates G S
    second_eq := ?_
    negative := ?_
    comparison_isIso := hc
    iteratedIso := fun n => isoWhiskerLeft F.rightDerivedFunctorPlus (derivedTargetIso G S n)
    iterated_eq := ?_
    targetIso := fun n => isoWhiskerLeft F.rightDerivedFunctorPlus (derivedTargetIso G S n) ≪≫
      isoWhiskerRight (asIso (Comp F G)).symm (DerivedCategory.Plus.homologyFunctor C n)
    canonical := fun _ => rfl
    convergence := ?_
    down_inclusion := fun X => derived_down_inclusion G R (F.rightDerivedFunctorPlus.obj X)
    inclusion_mono := ?_
    finite := ?_ }
  · intro p q
    ext X
    simp [rowCoordinates]
    exact (Category.id_comp _).symm
  · intro X p q h
    exact descended_negative G S (F.rightDerivedFunctorPlus.obj X) p (p+q) h
  · intro n
    ext X
    simp [rowCoordinates]
    exact (Category.id_comp _).symm
  · intro X
    exact converges_of_iso (realization G R _) (diagram_converges G _)
  · intro X
    exact mono_of_iso (realization G R _) (fun _ _ => diagram_inclusion_mono G _ _ _)
  · intro X
    exact finite_of_iso (realization G R _) (diagram_finite G _)

variable (hc : ∀ X, IsIso ((Comp F G).app X))
local notation "P" => compositionPackage F G S hc
local notation "S₀" => DerivedCategory.Plus.singleFunctor A 0
local notation "R" => descendedRow G S
local notation "T" => (S₀ ⋙ F.rightDerivedFunctorPlus)
local notation "Y" X => Functor.obj T X

private def objectFilteredEdges (X : A) : EdgeData ((objectSequence F G P).obj X) :=
  derivedEdges G R (Y X) (object_quadrant F G P X)

private lemma objectFilteredEdges_formulas (X : A) :
    FilteredEdgesOn G (P).row (Y X) (objectFilteredEdges F G S hc X) := by
  constructor
  · intro n
    exact realized_row_formula G (modelData G R (Y X)) (modelIso G R (Y X)) (object_quadrant F G P X) n
  · intro n
    exact realized_column_formula G (modelData G R (Y X)) (modelIso G R (Y X)) (object_quadrant F G P X) n

variable [PreservesFiniteLimits F] [PreservesFiniteLimits G]

private def rowPageIso (n : ℕ) :
    objectSequence F G P ⋙ pageEval 0 (n : ℤ) (n : ℤ) ≅ F ⋙ rightValue G n :=
  normalizedFirstPageIso F G S n

private def columnPageIsoAtObjects (n : ℕ) :
    objectSequence F G P ⋙ pageEval 0 0 (n : ℤ) ≅ rightValue F n ⋙ G :=
  isoWhiskerLeft T (columnPageIso G S n)

private lemma objectSecondIso_at (p q : ℕ) (m : ℤ) (h : (p : ℤ)+(q : ℤ)=m) :
    objectSecondIso F G P p q =
      eqToIso (congrArg (fun k => objectSequence F G P ⋙ pageEval 0 (p : ℤ) k) h) ≪≫
        isoWhiskerLeft T (secondCoordinatesAt G S p q m h) := by
  subst m
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [objectSecondIso, secondCoordinatesAt]

private lemma objectRow_coordinates (n : ℕ)
    (h : ∀ X : A, (normalizedFirstPageIso F G S n).hom.app X ≫
      (rightValue G n).map ((degreeZeroIso F).hom.app X) =
        (bottomCoordinates G S n).hom.app (Y X)) :
    objectSecondIso F G P n 0 =
      rowIndexIso F G P n ≪≫ rowPageIso F G S hc n ≪≫
        isoWhiskerRight (degreeZeroIso F) (rightValue G n) := by
  rw [objectSecondIso_at F G S hc n 0 n (add_zero _)]
  congr 1
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact (h X).symm

private lemma objectColumn_coordinates (n : ℕ)
    (h : ∀ Z : DerivedCategory.Plus B, (columnPageIso G S n).hom.app Z =
      (leftCoordinates G S n).hom.app Z ≫
        (canonicalRightZeroIso G).hom.app ((DerivedCategory.Plus.homologyFunctor B n).obj Z)) :
    objectSecondIso F G P 0 n =
      columnIndexIso F G P n ≪≫ columnPageIsoAtObjects F G S hc n ≪≫
        isoWhiskerLeft (rightValue F n) (canonicalRightZeroIso G).symm := by
  rw [objectSecondIso_at F G S hc 0 n n (zero_add _)]
  congr 1
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let e := (canonicalRightZeroIso G).app ((rightValue F n).obj X)
  change (leftCoordinates G S n).hom.app (Y X) =
    (columnPageIso G S n).hom.app (Y X) ≫ e.inv
  rw [h]
  change _ = ((leftCoordinates G S n).hom.app (Y X) ≫ e.hom) ≫ e.inv
  let a := (leftCoordinates G S n).hom.app (Y X)
  exact ((Category.assoc a e.hom e.inv).trans
    ((congrArg (fun f => a ≫ f) e.hom_inv_id).trans (Category.comp_id a))).symm

private lemma object_first_comparison (X : A) (n : ℕ) :
    (rowPageIso F G S hc n).hom.app X ≫ (derivedFirstEdge F G P n).app X =
      (objectFilteredEdges F G S hc X).row n ≫ (objectTargetIso F G P n).hom.app X := by
  letI := hc
  letI : IsIso (Comp F G) := NatIso.isIso_of_isIso_app _
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let α := H.map ((asIso (Comp F G)).inv.app ((S₀).obj X))
  change (normalizedFirstPageIso F G S n).hom.app X ≫
      ((G.rightDerivedFunctorPlus ⋙ H).map ((stalkToDerived F).app X) ≫ α) =
    (objectFilteredEdges F G S hc X).row n ≫
      ((derivedTargetIso G S (n : ℤ)).hom.app (Y X) ≫ α)
  simp only [← Category.assoc]
  rw [normalizedFirstPageIso_row F G S X n (object_quadrant F G P X)]
  rfl

private lemma object_second_comparison (X : A) (n : ℕ) :
    (objectTargetIso F G P n).hom.app X ≫ (derivedSecondEdge G F n).app X =
      (objectFilteredEdges F G S hc X).column n ≫
        (columnPageIsoAtObjects F G S hc n).hom.app X := by
  letI := hc
  letI : IsIso (Comp F G) := NatIso.isIso_of_isIso_app _
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let cmp := (asIso (Comp F G)).app ((S₀).obj X)
  haveI : (Y X).IsGE 0 := preservesLowerBounds A B F _ 0 (by infer_instance)
  have heq := column_edge_comparison G S (Y X) n
  change ((derivedTargetIso G S (n : ℤ)).hom.app (Y X) ≫ H.map cmp.inv) ≫
      (H.map cmp.hom ≫ (derivedTruncationEdge G (n : ℤ)).app (Y X)) =
      (objectFilteredEdges F G S hc X).column n ≫
        (columnPageIsoAtObjects F G S hc n).hom.app X
  rw [Category.assoc]
  have hh := (H.mapIso cmp).inv_hom_id_assoc ((derivedTruncationEdge G (n : ℤ)).app (Y X))
  change H.map cmp.inv ≫ H.map cmp.hom ≫ (derivedTruncationEdge G (n : ℤ)).app (Y X) = _ at hh
  rw [hh]
  exact heq.symm

private lemma object_five_terms (X : A) :
    ClassicalFiveTerms ((derivedFirstEdge F G P 1).app X) ((derivedSecondEdge G F 1).app X)
      ((columnPageIsoAtObjects F G S hc 1).inv.app X ≫
        transgression ((objectSequence F G P).obj X) ≫ (rowPageIso F G S hc 2).hom.app X)
      ((derivedFirstEdge F G P 2).app X) := by
  let E := objectFilteredEdges F G S hc X
  have hE : FiveTermData E :=
    derived_fiveTerms G R (Y X) (object_quadrant F G P X)
  let e₁ := (rowPageIso F G S hc 1).app X
  let e₂ := (objectTargetIso F G P 1).app X
  let e₃ := (columnPageIsoAtObjects F G S hc 1).app X
  let e₄ := (rowPageIso F G S hc 2).app X
  let e₅ := (objectTargetIso F G P 2).app X
  have hFirst (n : ℕ) :
      (derivedFirstEdge F G P n).app X = (rowPageIso F G S hc n).inv.app X ≫
        E.row n ≫ (objectTargetIso F G P n).hom.app X := by
    have h := object_first_comparison F G S hc X n
    rw [← h]
    exact (((rowPageIso F G S hc n).app X).inv_hom_id_assoc _).symm
  have hSecond : (derivedSecondEdge G F 1).app X =
      e₂.inv ≫ E.column 1 ≫ e₃.hom := by
    have h := object_second_comparison F G S hc X 1
    change e₂.hom ≫ (derivedSecondEdge G F 1).app X = E.column 1 ≫ e₃.hom at h
    rw [← h, Iso.inv_hom_id_assoc]
  rw [hFirst 1, hSecond, hFirst 2]
  exact transferFiveTerms E hE e₁.symm e₂.symm e₃.symm e₄.symm e₅.symm

private def objectEdgePackage
    (hBottom : ∀ (n : ℕ) (X : A), (normalizedFirstPageIso F G S n).hom.app X ≫
      (rightValue G n).map ((degreeZeroIso F).hom.app X) =
        (bottomCoordinates G S n).hom.app (Y X))
    (hLeft : ∀ (n : ℕ) (Z : DerivedCategory.Plus B), (columnPageIso G S n).hom.app Z =
      (leftCoordinates G S n).hom.app Z ≫
        (canonicalRightZeroIso G).hom.app ((DerivedCategory.Plus.homologyFunctor B n).obj Z)) :
    ObjectEdges F G P where
  objectCase := {
    secondIso := objectSecondIso F G P
    secondIso_eq := objectSecondIso_eq F G P
    targetIso := objectTargetIso F G P
    targetIso_eq := fun _ => rfl
    quadrant := object_quadrant F G P }
  target_identification _ := rfl
  degreeZeroF := degreeZeroIso F
  degreeZeroF_hom := rfl
  degreeZero := canonicalRightZeroIso G
  degreeZero_hom := rfl
  zeroTruncation := stalkToTruncDerivedIso F
  zeroTruncation_hom := stalkToDerived_eq_trunc F
  truncation n := columnTruncation G (n : ℤ)
  rowPage := rowPageIso F G S hc
  columnPage := columnPageIsoAtObjects F G S hc
  row_identification n := objectRow_coordinates F G S hc n (hBottom n)
  column_identification n := objectColumn_coordinates F G S hc n (hLeft n)
  filtered := objectFilteredEdges F G S hc
  filtered_formulas := objectFilteredEdges_formulas F G S hc
  first_comparison := fun n X => object_first_comparison F G S hc X n
  second_comparison := fun n X => object_second_comparison F G S hc X n
  fiveTerms := object_five_terms F G S hc

/-- HA-G05 for left exact functors and the injective acyclicity hypothesis of HA-G04. -/
theorem grothendieck_edges : Specs.FullStatement.{u₁,v₁,u₂,v₂,u₃,v₃,w₁,w₂,w₃} := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ F G _ _ _ _ hacyc
  obtain ⟨S, _⟩ := (HypercohomologyDerivedNaturality.hypercohomology).2 B C G
  have hc := (RightDerivedComposition.comparisonIsoIff A B C F G).mpr hacyc
  refine ⟨compositionPackage F G S hc, ⟨objectEdgePackage F G S hc ?_ ?_⟩⟩
  · intro n
    apply bottomCoordinates_naturality
    intro U
    obtain ⟨I, hI⟩ := CartanEilenbergExistence.existsResolutionAtBound (ordinaryStalk U 0).obj 0
      (fun p hp => HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U p (by omega))
    apply bottomStalk_of_model G S U n I
    simp only [modelSecondCoordinates_hom]
    simpa only [Category.assoc, HomologicalComplex.homologyFunctorSingleIso_hom_app] using
      bottomStalkModel_formula G U I (S.data (ordinaryStalk U 0) I)
        (fun p => hI (-1) p (by omega)) n
  · intro n
    apply leftCoordinates_naturality
    apply stalkColumn_comparison_of_injective
    intro U hU
    letI := hU
    let I := injectiveStalkResolution U (n : ℤ)
    let M := S.data (ordinaryStalk U (n : ℤ)) I
    letI hClosed := injectiveStalk_closed_isIso G U (n : ℤ) M
    have hInjection := injectiveStalk_sumInjection_isIso G U (n : ℤ) M
    exact leftStalk_of_model G S U n I (leftStalkModel_formula G U n M hClosed
      (injective_left_representative_epi G U (n : ℤ) M hInjection))

end AdvancedHomologicalAlgebra.GrothendieckEdges
end G05Assembly
