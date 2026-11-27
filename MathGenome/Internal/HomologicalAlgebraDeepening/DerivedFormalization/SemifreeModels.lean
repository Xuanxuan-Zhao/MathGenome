import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.OrdinaryComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeFiltrationTransport

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace DerivedFormalization.SemifreeModels

open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels (isKProjectiveValue)
open Specs.DerivedFormalization.CochainRingTransport
  (complexEquivalenceValue shrinkRingEquivValue uliftRingEquivValue)
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.OrdinaryComplex
  (CellPresentation degreeZeroCategory fromComplexFunctor DGMod)
open Specs.DerivedFormalization.SemifreeModels

open private toComplex counit strictPreimage map_strictPreimage
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.OrdinaryComplex

universe u v t

noncomputable section

variable {R : Type v} [CommRing R]

private def cellQuotientIso
    {F : compValue.{v} R} {I : ℕ → Type v} {d : ∀ n, I n → ℤ}
    (C : CellPresentation F I d) (n : ℕ) :
    cokernel (C.incl n) ≅ Specs.DerivedFormalization.SemifreeFiltration.stalkSum
      (fun i => -d n i) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (C.shortExact n).gIsCokernel

/-- The ordinary cell presentation numbers the zero stage by zero. The
exhaustive filtration starts at the first attachment. -/
private def filtrationOfCellPresentation
    {F : compValue.{v} R} {I : ℕ → Type v} {d : ∀ n, I n → ℤ}
    (C : CellPresentation F I d) :
    Specs.DerivedFormalization.SemifreeFiltration.Filtration F where
  stages := Functor.ofSequence (fun n => C.incl (n + 1))
  inclusions := NatTrans.ofSequence (fun n => C.into (n + 1)) (fun n => by
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    change C.incl (n + 1) ≫ C.into (n + 1 + 1) = C.into (n + 1) ≫ 𝟙 F
    rw [Category.comp_id, C.compatible])
  injective n i := C.injective (n + 1) i
  exhaustive i x := by
    obtain ⟨n, y, hy⟩ := C.exhaustive i x
    cases n with
    | zero =>
        refine ⟨0, (C.incl 0).f i y, ?_⟩
        change (C.into 1).f i ((C.incl 0).f i y) = x
        rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, C.compatible]
        exact hy
    | succ n => exact ⟨n, y, hy⟩
  split n i := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact C.split (n + 1) i
  initial := by
    have hz : C.incl 0 = 0 := by
      ext i x
      rw [C.bottom i x]
      simp
    refine ⟨I 0, fun i => -d 0 i, ⟨?_⟩⟩
    exact cokernelZeroIsoTarget ≪≫ cokernelZeroIsoTarget.symm ≪≫
      cokernelIsoOfEq hz.symm ≪≫ cellQuotientIso C 0
  successive n := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact ⟨I (n + 1), fun i => -d (n + 1) i, ⟨cellQuotientIso C (n + 1)⟩⟩

theorem diagonalResolution : DiagonalResolution.{v} := by
  intro R _ X
  let T := fromComplexFunctor (k := R) (R := R)
  obtain ⟨P, q, ⟨D⟩, hsurj, hq⟩ :=
    RightDGModule.unboundedSemiFreeResolutionInUniverse.{v,v,0}
      R (degreeZeroCategory R R) (T.obj X)
  let F := toComplex P
  let e : T.obj F ≅ P := counit P
  let p : F ⟶ X := strictPreimage (e.hom ≫ q)
  have hp : T.map p = e.hom ≫ q := map_strictPreimage _
  let D' : IndexedSemiFree.Presentation (T.obj F) :=
    { stage := D.stage
      bottom := D.bottom
      index := D.index
      family := D.family
      extension := D.extension
      into := fun n => D.into n ≫ e.inv
      compatible := fun n => by rw [← Category.assoc, D.compatible]
      injective := fun n a i => by
        let α := ((RightDGModuleModel.eval a).mapIso e).symm
        exact (ConcreteCategory.bijective_of_isIso (α.hom.f i)).injective.comp (D.injective n a i)
      exhaustive := fun a i x => by
        obtain ⟨n, y, hy⟩ := D.exhaustive a i ((e.hom.app a).f i x)
        refine ⟨n, y, ?_⟩
        change (e.inv.app a).f i ((D.into n).app a |>.f i y) = x
        rw [hy, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
        exact congrArg (fun f : T.obj F ⟶ T.obj F => (f.app a).f i x) e.hom_inv_id }
  obtain ⟨_, _, C, _⟩ := OrdinaryComplex.indexedFiltrationComparison R R F D'
  refine ⟨F, p, ?_, ?_, ⟨filtrationOfCellPresentation C⟩,
    (OrdinaryComplex.kProjectivityComparison R R F).2
      (RightDGModule.SemiFreePresentation.isKProjective D')⟩
  · apply (OrdinaryComplex.quasiIsoComparison R R p).2
    change ∀ a, QuasiIso (((RightDGModuleModel.eval a).map (T.map p)))
    intro a
    rw [hp, Functor.map_comp]
    exact (quasiIso_iff_comp_left
      ((RightDGModuleModel.eval a).map e.hom) ((RightDGModuleModel.eval a).map q)).2 (hq a)
  · apply (OrdinaryComplex.surjectivityComparison R R p).2
    rw [hp]
    intro a i
    let α := (RightDGModuleModel.eval a).mapIso e
    exact (hsurj a i).comp (ConcreteCategory.bijective_of_isIso (α.hom.f i)).surjective

/-- A ring representative at the given module level gives the resolution
over the original ring via the exact equivalence of cochain categories. -/
private theorem representedResolution {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (e : R ≃+* A) (X : compValue.{v} R) :
    ∃ (F : compValue.{v} R) (p : F ⟶ X), QuasiIso p ∧
      (∀ i, Function.Surjective (p.f i)) ∧
      Nonempty (Specs.DerivedFormalization.SemifreeFiltrationTransport.Filtration e F) ∧
      isKProjectiveValue F := by
  let E := complexEquivalenceValue e
  obtain ⟨G, q, hq, hsurj, ⟨C⟩, hK⟩ := diagonalResolution A (E.functor.obj X)
  let F := E.inverse.obj G
  let φ : E.functor.obj F ≅ G := E.counitIso.app G
  let p : F ⟶ X := E.functor.preimage (φ.hom ≫ q)
  have hp : E.functor.map p = φ.hom ≫ q := E.functor.map_preimage _
  obtain ⟨P, _⟩ := (SemifreeFiltrationTransport.transportFiltration e φ).2 C
  obtain ⟨comparison⟩ := CochainTensorTransport.ringComparison e
  have properties := CochainRingTransport.complexProperties e F X p
  refine ⟨F, p, properties.2.1.1 ?_, fun i => (properties.2.2.2 i).1 ?_, ⟨P⟩,
    (comparison.kProjective F).1 ((CochainComplex.isKProjective_iff_of_iso φ).2 hK)⟩
  · change QuasiIso (E.functor.map p)
    rw [hp]
    infer_instance
  · change Function.Surjective ((E.functor.map p).f i)
    rw [hp, HomologicalComplex.comp_f]
    exact (hsurj i).comp (ConcreteCategory.bijective_of_isIso (φ.hom.f i)).surjective

theorem nativeResolution : NativeResolution.{u,v} := by
  intro R _ _ X
  exact representedResolution (shrinkRingEquivValue.{v} R) X

theorem adequateResolution : AdequateResolution.{u,v,t} := by
  intro R _ X
  let e := uliftRingEquivValue.{max u v t} R
  let jX := (Specs.DerivedFormalization.CochainCoefficientLift.lift.{max u t, v} R).obj X
  obtain ⟨F, p, hq, hsurj, hF, hK⟩ := representedResolution e jX
  exact ⟨F, p, hq, hsurj, hF, hK,
    fun i => (CochainCoefficientLift.toOriginal_surjective p i).2 (hsurj i),
    (CochainCoefficientLift.toOriginal_quasiIso_iff p).1 hq⟩

end

end DerivedFormalization.SemifreeModels
