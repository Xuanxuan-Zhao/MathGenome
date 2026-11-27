import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentModelProperties
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.FlatFiltration
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective

open CategoryTheory

universe u v

namespace DerivedFormalization.Affine.CotangentModelProperties

open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular dgCat)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit ShiftedFree)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom)
open Specs.DerivedFormalization.DG.IndexedSemiFree
  (Attachment CellFamily Presentation StrictSum cells)
open CochainComplex.HomComplex (Cochain)
open DG.IndexedCellAttachment (projection sectionDegree sectionDegree_act projection_section
  inclusion_projection)
open private preceding_add_section from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedCellAttachment

noncomputable section

/-- The scalar extension of the given model of relative differentials. -/
abbrev cotangentModel {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A P B : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} (p : P ⟶ B)
    (O : Kahler.DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)) : B.Module :=
  Specs.DerivedFormalization.Affine.CotangentModelProperties.cotangentModel T p O

/-- The cotangent representative formed using the concrete balanced tensor
and relative differentials of the affine construction. -/
abbrev concreteModel {k : Type u} [Field k] [CharZero k]
    {A P B : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) (p : P ⟶ B) : B.Module :=
  cotangentModel (Tensor.moduleTensorModel k) p (Kahler.model f)

section Filtration

variable {k : Type u} [Field k] [CharZero k] {B : CommDGAlgebra.{u,v} k}
variable {L M S : B.Module} {I : Type v} {C : CellFamily L I}

private def gradedMapOfComponents (f : ∀ a n,
    (M.complex a).X n →ₗ[k] (S.complex a).X n)
    (hf : ∀ (a b : (dgCat B).Obj) i j n (h : i+j=n)
      (x : (M.complex b).X i) (z : ((dgCat B).hom a b).X j),
      f a n (M.act i j n h x z) = S.act i j n h (f b i x) z) :
    gradedHom M S 0 :=
  ⟨fun a => Cochain.mk (fun i q h => by
    obtain rfl : i = q := (add_zero i).symm.trans h
    exact ModuleCat.ofHom (f a i)), by
    intro a b i j n ir nr h hi hn x z
    obtain rfl : i = ir := (add_zero i).symm.trans hi
    obtain rfl : n = nr := (add_zero n).symm.trans hn
    exact hf a b i j n h x z⟩

private def attachmentSplit (E : Attachment C M) (s : StrictSum (cells C) S) :
    GradedSplit E.inclusion (projection E s) where
  zero := inclusion_projection E s
  retraction := gradedMapOfComponents
    (fun a n => (LinearMap.fst k _ _).comp (E.coordinates a n).toLinearMap)
    (fun _ _ i j n h x z => (E.coordinate_act i j n h x z).1)
  sectionMap := gradedMapOfComponents (sectionDegree E s)
    (fun _ _ i j n h x z => sectionDegree_act E s i j n h x z)
  retract n x := by
    change (E.coordinates () n ((E.inclusion.app ()).f n x)).1 = x
    rw [E.coordinate_inclusion]
  section_id n z := projection_section E s () n z
  decompose n y := preceding_add_section E s () n y

private theorem cells_shiftedFree (s : StrictSum (cells C) S) : ShiftedFree.{u,v,v} S := by
  classical
  refine ⟨I, fun i => -C.degree i, ⟨?_⟩⟩
  refine ⟨s.inclusion, fun n => ?_⟩
  have h : (s.coordinates () n).toLinearMap.comp
      (DirectSum.toModule k I _ (fun i => ((s.inclusion i).app ()).f n |>.hom)) =
      LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change s.coordinates () n
      (DirectSum.toModule k I _ (fun i => ((s.inclusion i).app ()).f n |>.hom)
        (DirectSum.lof k I _ i x)) = DirectSum.lof k I _ i x
    rw [DirectSum.toModule_lof]
    exact s.coordinate_inclusion i () n x
  have h' := congrArg (fun g => (s.coordinates () n).symm.toLinearMap.comp g) h
  rw [← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp,
    LinearMap.comp_id] at h'
  exact h' ▸ (s.coordinates () n).symm.bijective

private theorem bottom_shiftedFree (F : Presentation.{u,v,0,v} M) :
    ShiftedFree.{u,v,v} (F.stage 0) := by
  classical
  refine ⟨PEmpty, fun i => isEmptyElim i, ⟨⟨fun i => isEmptyElim i, fun n => ?_⟩⟩⟩
  constructor
  · intro x y _
    exact DFinsupp.ext fun i => isEmptyElim i
  · intro x
    refine ⟨0, ?_⟩
    rw [map_zero, F.bottom () n x]

private def stageDiagram (F : Presentation.{u,v,0,v} M) : ℕ ⥤ B.Module :=
  Functor.ofSequence (fun n => (F.extension n).inclusion)

private def stageUnion (F : Presentation.{u,v,0,v} M) :
    Specs.DerivedFormalization.Affine.FlatFiltration.Union (stageDiagram F) M where
  incl := F.into
  comm {i j} h := by
    let inclusion : stageDiagram F ⟶ (Functor.const ℕ).obj M :=
      NatTrans.ofSequence F.into (fun n => by
        simp only [stageDiagram, Functor.ofSequence_map_homOfLE_succ,
          Functor.const_obj_map]
        exact F.compatible n)
    have naturality := inclusion.naturality (homOfLE h)
    change (stageDiagram F).map (homOfLE h) ≫ F.into j = F.into i ≫ 𝟙 M at naturality
    simpa only [Category.comp_id] using naturality
  injective n q := F.injective n () q
  exhaustive n x := F.exhaustive () n x

/-- A cell presentation in the one-object category of a commutative dg
algebra gives K-flatness for its signed tensor product. -/
theorem isKFlat_of_presentation (T : ModuleTensor.{u,v} k)
    (formulas : ∀ N : B.Module, T.Formulas (𝟙 B) N)
    (F : Presentation.{u,v,0,v} M) : T.KFlat M := by
  apply FlatFiltration.semifreeFlatness T formulas (stageDiagram F) (stageUnion F)
  · intro n hn
    exact (Order.not_isSuccLimit_natCast (α := ℕ) n hn).elim
  · intro n hn
    have hn' : n = 0 := Nat.eq_zero_of_le_zero (hn (Nat.zero_le n))
    subst n
    exact bottom_shiftedFree F
  · intro i j hij
    have hj : j = i+1 := by
      by_contra h
      exact hij.2 (show i < i+1 by omega) (show i+1 < j by have := hij.lt; omega)
    subst j
    let s := DG.IndexedSums.nativeSum (cells (F.family i))
    refine ⟨_, projection (F.extension i) s, ⟨?_⟩, cells_shiftedFree s⟩
    unfold stageDiagram
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact attachmentSplit (F.extension i) s

end Filtration

theorem cotangentModelProperties :
    Specs.DerivedFormalization.Affine.CotangentModelProperties.ModelProperties.{u,v} := by
  intro k _ _ T A P B _ f p O _ hf _ _ hp hB
  obtain ⟨V, ⟨E⟩⟩ := hf
  obtain ⟨_, _, ⟨F, _⟩, _, _⟩ :=
    SemifreeDifferentials.semifreeAfterBaseChange T E O p hp
  exact ⟨RightDGModule.SemiFreePresentation.isKProjective F, isKFlat_of_presentation T hB F⟩

/-- The concrete cotangent representative is K-projective and K-flat. -/
theorem concreteModel_properties {k : Type u} [Field k] [CharZero k]
    {A P B : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) (p : P ⟶ B)
    (hf : Semifree.IsSemifree A f) (hp : NonpositiveCDGA.DegreewiseSurjective p)
    (hq : NonpositiveCDGA.IsQuasiIso p) :
    RightDGModule.IsKProjective (concreteModel f p) ∧ Tensor.KFlat (concreteModel f p) :=
  cotangentModelProperties (Tensor.moduleTensorModel k) (f ≫ p) f p (Kahler.model f)
    rfl hf hp hq (Tensor.moduleTensor_formulas p (regular B.toCommDGAlgebra))
    (Tensor.moduleTensor_formulas (𝟙 B.toCommDGAlgebra))

end
end DerivedFormalization.Affine.CotangentModelProperties
