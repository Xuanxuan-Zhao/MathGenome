import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechToCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.EdgesAndFiveTerms

/-! HA-H04, notes/002/advanced-homological-algebra.tex:3687–3706. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.CechToCohomology
open AdvancedHomologicalAlgebra.DoubleTotalization
open HomologicalComplex
universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AdvancedHomologicalAlgebra.AcyclicCoverComparison

abbrev natEmbedding := ComplexShape.embeddingUpIntGE 0

variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v} (c : Cover U A)

abbrev SectionModule := ModuleCat.{max u v} (sectionRing R U)

abbrev cechComplexInt (M : Modules R) :=
  (cechComplex R c M.val).extend natEmbedding

abbrev cechCohomology (n : ℕ) : Modules R ⥤ SectionModule (U := U) R :=
  SheafOfModules.forget R ⋙ cochainFunctor R c ⋙
    homologyFunctor (SectionModule (U := U) R) (.up ℕ) n

/-- The vanishing condition on intersections indexed by nonempty ordered tuples. -/
def AcyclicOnIntersections (M : Modules R) : Prop :=
  ∀ (p : ℕ) (t : Fin (p + 1) → A) (q : ℕ), 0 < q →
    IsZero ((sectionCohomology R (tupleOpen c t) q).obj M)

/-- The nonnegative column of the extended Čech-resolution bicomplex. -/
abbrev columnIso (M : Modules R) (I : InjectiveResolution M) (p : ℕ) :
    (resolutionDoubleComplexInt R c M I).X (p : ℤ) ≅
      ((resolutionDoubleComplex R c M I).X p).extend natEmbedding :=
  resolutionColumnIso R c M I p

/-- Transport from the integer-indexed bidegree to the original term. -/
abbrev entryIso (M : Modules R) (I : InjectiveResolution M) (p q : ℕ) :
    ((resolutionDoubleComplexInt R c M I).X (p : ℤ)).X (q : ℤ) ≅
      ((resolutionDoubleComplex R c M I).X p).X q :=
  (eval (SectionModule (U := U) R) (.up ℤ) (q : ℤ)).mapIso (columnIso R c M I p) ≪≫
    ((resolutionDoubleComplex R c M I).X p).extendXIso natEmbedding (by simp [natEmbedding])

/-- The comparison uses the exact carrier lift of the original HA-H01 cohomology. -/
def sectionResolutionIso (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    (liftedSectionCohomology R c n).obj M ≅ (sectionComplexInt R c M I).homology (n : ℤ) :=
  (sectionLift R c).mapIso (sectionResolutionIsoNat R U M I n) ≪≫
    (liftedSectionHomologyIso R c M I n).symm

end AdvancedHomologicalAlgebra.AcyclicCoverComparison

namespace Specs.AdvancedHomologicalAlgebra.AcyclicCoverComparison

open _root_.AdvancedHomologicalAlgebra.AcyclicCoverComparison
open _root_.AdvancedHomologicalAlgebra.EdgesAndFiveTerms

/-- The comparison is the bottom edge of this very spectral sequence
after the degree-zero comparison from the underived coefficient presheaf. -/
def agreesWithRowEdge {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X}
    {A : Type v} (c : Cover U A)
    (η : ∀ n, cechCohomology R c n ⟶ liftedSectionCohomology R c n) : Prop :=
  ∀ (S : CechSpectralSequence R c) (M : Modules R) (I : InjectiveResolution M)
    (E : EdgeData (S.data M I).filtration (S.data M I).pages) (n : ℕ),
    let D := S.data M I
    let toLocal := (cochainFunctor R c).map ((SheafOfModules.forget R).toRightDerivedZero.app M)
    homologyMap toLocal n ≫ (S.second M I n 0).inv ≫
      eqToHom (congrArg (_root_.AdvancedHomologicalAlgebra.PageCohomology.object D.filtration D.pages 2 (n : ℤ)) (add_zero _)) ≫
      E.row (n : ℤ) (by omega) ≫ (S.abutment M I n).hom = (η n).app M

/-- The natural comparison is induced by the two specified augmentations of the
HA-H03 resolution bicomplex, for every injective resolution. -/
def acyclicCoverComparison : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v} (c : Cover U A),
    ∃ η : ∀ n, cechCohomology R c n ⟶ liftedSectionCohomology R c n,
      (∀ (M : Modules R) (n : ℕ), AcyclicOnIntersections R c M → IsIso ((η n).app M)) ∧
      agreesWithRowEdge R c η ∧
      ∀ (M : Modules R) (I : InjectiveResolution M),
        ∃ (v : cechComplexInt R c M ⟶ sumTotal (resolutionDoubleComplexInt R c M I))
          (h : sectionComplexInt R c M I ⟶ sumTotal (resolutionDoubleComplexInt R c M I)),
          (∀ p : ℕ, v.f (p : ℤ) =
            ((cechComplex R c M.val).extendXIso natEmbedding (by simp [natEmbedding])).hom ≫
              ((cochainFunctor R c).map ((SheafOfModules.forget R).map (I.ι.f 0))).f p ≫
              (entryIso R c M I p 0).inv ≫
              sumInjection (resolutionDoubleComplexInt R c M I) (p : ℤ) 0 (p : ℤ) (add_zero _)) ∧
          (∀ n : ℤ, h.f n =
            (resolutionAugmentation R c M I).f n ≫
              sumInjection (resolutionDoubleComplexInt R c M I) 0 n n (zero_add n)) ∧
          QuasiIso h ∧
          ∀ n : ℕ,
            (η n).app M ≫ (sectionResolutionIso R c M I n).hom ≫ homologyMap h (n : ℤ) =
              ((cechComplex R c M.val).extendHomologyIso natEmbedding
                (j := n) (j' := (n : ℤ)) (by simp [natEmbedding])).inv ≫ homologyMap v (n : ℤ)

end Specs.AdvancedHomologicalAlgebra.AcyclicCoverComparison
