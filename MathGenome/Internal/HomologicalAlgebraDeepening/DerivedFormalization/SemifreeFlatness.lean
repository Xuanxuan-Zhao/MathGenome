import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeFiltration
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-! K-flatness of semifree complexes, via exact direct sums and filtered colimits. -/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
open HomologicalComplex (ιTensorObj)

namespace DerivedFormalization

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]

local notation "M" => ModuleCat R
local notation "up" => ComplexShape.up ℤ

private abbrev leftTensor (A : Comp.{u} R) : Comp.{u} R ⥤ Comp.{u} R where
  obj X := tensorComplex A X
  map f := tensorMap (𝟙 A) f
  map_id X := tensorMap_id A X
  map_comp f g := by rw [tensorMap_comp, Category.id_comp]

@[reassoc]
private lemma ι_leftTensor_map (A : Comp.{u} R) {X Y : Comp.{u} R} (f : X ⟶ Y)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj A X i j n h ≫ ((leftTensor A).map f).f n =
      (A.X i ◁ f.f j) ≫ ιTensorObj A Y i j n h := by
  change ιTensorObj A X i j n h ≫ (tensorMap (𝟙 A) f).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

private instance (A : Comp.{u} R) : (leftTensor A).PreservesZeroMorphisms where
  map_zero X Y := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := A) (K₂ := X) (F := curriedTensor M) (c := up)
    intro i j h
    change ιTensorObj A X i j n h ≫ ((leftTensor A).map (0 : X ⟶ Y)).f n =
      ιTensorObj A X i j n h ≫ (0 : tensorComplex A X ⟶ tensorComplex A Y).f n
    rw [ι_leftTensor_map]
    simp

private lemma leftTensor_mono (A : Comp.{u} R) {X Y : Comp.{u} R} (f : X ⟶ Y)
    (hf : ∀ j, ∃ r : Y.X j ⟶ X.X j, f.f j ≫ r = 𝟙 _) :
    Mono ((leftTensor A).map f) := by
  choose r hr using hf
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let retraction : (tensorComplex A Y).X n ⟶ (tensorComplex A X).X n :=
    HomologicalComplex.mapBifunctorDesc
      (K₁ := A) (K₂ := Y) (F := curriedTensor M) (c := up)
      (fun i j h => (A.X i ◁ r j) ≫ ιTensorObj A X i j n h)
  have fac : ((leftTensor A).map f).f n ≫ retraction = 𝟙 _ := by
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := A) (K₂ := X) (F := curriedTensor M) (c := up)
    intro i j h
    change ιTensorObj A X i j n h ≫ _ = ιTensorObj A X i j n h ≫ _
    dsimp only [retraction]
    rw [ι_leftTensor_map_assoc, HomologicalComplex.ι_mapBifunctorDesc, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, hr, MonoidalCategory.whiskerLeft_id]
    simp
  exact mono_of_mono_fac fac

/-- Tensoring on the left commutes with colimits. Degreewise this follows by
taking the colimit of each summand in the total tensor. -/
private def leftTensor_isColimit {J : Type v} [Category.{w} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)] (A : Comp.{u} R) {D : J ⥤ Comp.{u} R} {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((leftTensor A).mapCocone c) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  let E := (leftTensor A) ⋙ HomologicalComplex.eval M up n
  let T (i j : ℤ) := HomologicalComplex.eval M up j ⋙ tensorLeft (A.X i)
  let hT (i j : ℤ) : IsColimit ((T i j).mapCocone c) :=
    isColimitOfPreserves (tensorLeft (A.X i))
      (isColimitOfPreserves (HomologicalComplex.eval M up j) hc)
  let restrict (t : Cocone (D ⋙ E)) (i j : ℤ) (h : i + j = n) :
      Cocone (D ⋙ T i j) :=
    { pt := t.pt
      ι :=
        { app := fun k => ιTensorObj A (D.obj k) i j n h ≫ t.ι.app k
          naturality := by
            intro k l f
            change (A.X i ◁ (D.map f).f j) ≫
              ιTensorObj A (D.obj l) i j n h ≫ t.ι.app l =
                (ιTensorObj A (D.obj k) i j n h ≫ t.ι.app k) ≫ 𝟙 _
            rw [Category.comp_id]
            rw [← ι_leftTensor_map_assoc A (D.map f) i j n h]
            congr 1
            exact t.w f } }
  refine
    { desc := fun t => HomologicalComplex.mapBifunctorDesc
        (K₁ := A) (K₂ := c.pt) (F := curriedTensor M) (c := up)
        (fun i j h => (hT i j).desc (restrict t i j h))
      fac := ?_
      uniq := ?_ }
  · intro t k
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := A) (K₂ := D.obj k) (F := curriedTensor M) (c := up)
    intro i j h
    change ιTensorObj A (D.obj k) i j n h ≫
      ((leftTensor A).map (c.ι.app k)).f n ≫ _ = _
    erw [ι_leftTensor_map_assoc, HomologicalComplex.ι_mapBifunctorDesc]
    exact (hT i j).fac (restrict t i j h) k
  · intro t m hm
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := A) (K₂ := c.pt) (F := curriedTensor M) (c := up)
    intro i j h
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    apply (hT i j).uniq (restrict t i j h)
    intro k
    let leg : D.obj k ⟶ c.pt := c.ι.app k
    change (A.X i ◁ leg.f j) ≫ ιTensorObj A c.pt i j n h ≫ m = _
    erw [← ι_leftTensor_map_assoc A leg i j n h]
    have hk : ((leftTensor A).map leg).f n ≫ m = t.ι.app k := hm k
    rw [hk]

private instance {J : Type v} [Category.{w} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)] (A : Comp.{u} R) :
    PreservesColimitsOfShape J (leftTensor A) where
  preservesColimit {D} := ⟨fun hc => ⟨leftTensor_isColimit (D := D) A hc⟩⟩

private lemma tensor_cokernel_shortExact (A : Comp.{u} R) {X Y : Comp.{u} R} (f : X ⟶ Y)
    (hf : ∀ j, ∃ r : Y.X j ⟶ X.X j, f.f j ≫ r = 𝟙 _) :
    ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
      (leftTensor A)).ShortExact := by
  let S := (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map (leftTensor A)
  obtain ⟨he, hg⟩ := S.exact_and_epi_g_iff_g_is_cokernel.mpr
    ⟨isColimitOfHasCokernelOfPreservesColimit (leftTensor A) f⟩
  exact { exact := he, mono_f := leftTensor_mono A f hf, epi_g := hg }

private lemma tensor_shiftedStalk_acyclic (A : Comp.{u} R) (hA : A.Acyclic) (s : ℤ) :
    (tensorComplex A ((cochainShift R s).obj ((stalk R).obj (ModuleCat.of R R)))).Acyclic := by
  let U := HomologicalComplex.tensorUnit M up
  let e : tensorComplex A ((cochainShift R s).obj ((stalk R).obj (ModuleCat.of R R))) ≅
      (cochainShift R s).obj A :=
    CochainComplex.mapBifunctorShift₂Iso A U (curriedTensor M) s ≪≫
      (cochainShift R s).mapIso (HomologicalComplex.rightUnitor A)
  intro i
  apply HomologicalComplex.ExactAt.of_iso _ e.symm
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hA (i + s)).isZero_homology.of_iso ((cohomologyShiftIso R s i).app A)

/-- A degreewise colimit of acyclic complexes is acyclic when the
indexing shape has exact colimits in the category of modules. -/
private lemma acyclic_of_isColimit {J : Type v} [Category.{w} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)] [HasExactColimitsOfShape J (ModuleCat.{u} R)]
    {D : J ⥤ Comp.{u} R} {c : Cocone D} (hc : IsColimit c) (hD : ∀ j, (D.obj j).Acyclic) :
    c.pt.Acyclic := by
  intro n
  let S := (ShortComplex.functorEquivalence J M).inverse.obj
    (D ⋙ HomologicalComplex.shortComplexFunctor M up n)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext j
    let E := (CategoryTheory.evaluation J M).obj j
    have hz : IsZero ((S.map E).homology) :=
      (ShortComplex.exact_iff_isZero_homology _).mp (hD j n)
    exact (hz.of_iso (S.mapHomologyIso E).symm).eq_of_src _ _
  let c₁ := (HomologicalComplex.eval M up ((up).prev n)).mapCocone c
  let c₂ := (HomologicalComplex.eval M up n).mapCocone c
  let c₃ := (HomologicalComplex.eval M up ((up).next n)).mapCocone c
  have hc₁ : IsColimit (c₁ : Cocone S.X₁) := isColimitOfPreserves _ hc
  have hc₂ : IsColimit (c₂ : Cocone S.X₂) := isColimitOfPreserves _ hc
  have hc₃ : IsColimit (c₃ : Cocone S.X₃) := isColimitOfPreserves _ hc
  exact colim.exact_mapShortComplex hS hc₁ hc₂ hc₃
    (c.pt.d ((up).prev n) n) (c.pt.d n ((up).next n))
    (fun j => (c.ι.app j).comm _ _) (fun j => (c.ι.app j).comm _ _)

private lemma tensor_shiftedStalkSum_acyclic (A : Comp.{u} R) (hA : A.Acyclic) {I : Type u}
    (s : I → ℤ) : (tensorComplex A (shiftedStalkSum s)).Acyclic := by
  let cells := Discrete.functor (fun i : I =>
    (cochainShift R (s i)).obj ((stalk R).obj (ModuleCat.of R R)))
  exact acyclic_of_isColimit (leftTensor_isColimit A (colimit.isColimit cells))
    (fun i => tensor_shiftedStalk_acyclic A hA (s i.as))

namespace SemifreeFiltration

/-- An exhaustive semifree filtration makes its ambient complex K-flat. -/
theorem isKFlat {F : Comp.{u} R} (P : SemifreeFiltration F) : IsKFlat F := by
  intro A hA
  have stages_acyclic (n : ℕ) : (tensorComplex A (P.stages.obj n)).Acyclic := by
    induction n with
    | zero =>
      obtain ⟨I, s, ⟨e⟩⟩ := P.initial
      let e₀ := P.initialQuotientIso.symm ≪≫ e
      intro i
      exact (tensor_shiftedStalkSum_acyclic A hA s i).of_iso ((leftTensor A).mapIso e₀.symm)
    | succ n ih =>
      obtain ⟨I, s, ⟨e⟩⟩ := P.successive n
      have hQ : (tensorComplex A (cokernel (P.step n))).Acyclic :=
        fun i => (tensor_shiftedStalkSum_acyclic A hA s i).of_iso
          ((leftTensor A).mapIso e.symm)
      exact (tensor_cokernel_shortExact A (P.step n) (P.split n)).acyclic_X₂ ih hQ
  let : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE (ModuleCat.{u} R)
  exact acyclic_of_isColimit (leftTensor_isColimit A P.isColimit) stages_acyclic

end SemifreeFiltration

end

end DerivedFormalization
