import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LerayAndDegenerations
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GrothendieckEdges
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CollapseAndExtensions

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
open TopologicalSpace

namespace AdvancedHomologicalAlgebra.LerayAndDegenerations
open SheafTheory HigherDirectImageLocalTheory DerivedSectionsTheory
open GrothendieckSpectralSequence GrothendieckEdges G05FilteredEdges
open FiniteFiltrationConvergence CollapseAndExtensions
open _root_.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- When only column zero survives, the column edge is the canonical
comparison through the sole graded piece of the abutment. -/
private theorem columnEdge_isIso {A : Type u} [Category.{v} A] [Abelian A]
    {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)
    (hF : DegreewiseFinite F) (E : EdgesAndFiveTerms.EdgeData F D)
    (hZ : ∀ p n : ℤ, p ≠ 0 → IsZero (PageCohomology.object F D 2 p n))
    (n : ℤ) (hn : 0 ≤ n) : IsIso (E.column n hn) := by
  obtain ⟨collapse⟩ := filtered_column_collapse F hF D 2 0 (by omega) hZ
  obtain ⟨L⟩ := collapse.limit 0 n
  obtain ⟨t⟩ := collapse.target n
  haveI : IsIso (cohomologyPiece F 0 n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (collapse.steps_top 0 n le_rfl)
  haveI : Epi (EdgesAndFiveTerms.ambientClass F 0 n) := by
    dsimp only [EdgesAndFiveTerms.ambientClass]
    infer_instance
  have he : E.column n hn = t.iso.hom ≫ L.iso.inv := by
    apply (cancel_epi (EdgesAndFiveTerms.ambientClass F 0 n)).1
    rw [E.column_formula]
    dsimp only [EdgesAndFiveTerms.ambientClass]
    simp only [Category.assoc, reassoc_of% t.inclusion_quotient]
    rw [← Category.assoc]
    change closedToPage F D 2 0 n = gradedClass F 0 n ≫ L.iso.inv
    rw [← L.representative_formula, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

section Global
variable {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
  (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)

local notation "D" => directImage R S f φ
local notation "ΓY" => globalSections S
local notation "stalk" => DerivedCategory.Plus.singleFunctor (Modules R) 0

variable {R S f φ} (L : LerayData R S f φ) (M : Modules R)

local notation "Seq" => Functor.obj (objectSequence D ΓY (L.package)) M
local notation "Y₀" => Functor.obj (Functor.rightDerivedFunctorPlus D) (Functor.obj stalk M)
local notation "ModData" => modelData ΓY L.package.row Y₀
local notation "ModIso" => modelIso ΓY L.package.row Y₀

/-- Transfer a support condition stated in nonnegative bidegrees to all
integer filtration and total degrees of the actual sheaf sequence. -/
private lemma sheafPage_isZero (P : ℤ → ℤ → Prop)
    (h : ∀ p q : ℕ, P p ((p : ℤ) + (q : ℤ)) →
      IsZero (((higherDirectImage R S f φ q ⋙ sectionCohomology S ⊤ p).obj M))) :
    ∀ p n : ℤ, P p n → IsZero ((Seq).page 0 p n) := by
  intro p n hpn
  by_cases hQ : p < 0 ∨ n < p
  · exact L.edges.objectCase.quadrant M p n hQ
  · let a := p.toNat
    let b := (n - p).toNat
    have ha : (a : ℤ) = p := Int.toNat_of_nonneg (by omega)
    have hab : (a : ℤ) + (b : ℤ) = n := by dsimp [a, b]; omega
    rw [← ha, ← hab] at hpn ⊢
    exact (h a b hpn).of_iso ((L.sheafSecondIso a b).app M)

private lemma filtered_eq_realized :
    L.edges.filtered M =
      realizedEdges ΓY ModData ModIso (L.edges.objectCase.quadrant M) := by
  let Q := L.edges.objectCase.quadrant M
  let A := ModData
  let e := ModIso
  let Q' := realizedQuadrant ΓY A e Q
  have hE := L.edges.filtered_formulas M
  apply EdgeData.ext
  · funext n
    haveI := EdgesAndFiveTerms.row_closedToPage_epi A.filtration A.pages A.convergence.finite Q' (n : ℤ)
    haveI : IsIso (e.inv.page 0 n n) := ((pageEval 0 n n).mapIso e).isIso_inv
    apply (cancel_epi (closedToPage A.filtration A.pages 2 (n : ℤ) (n : ℤ) ≫ e.inv.page 0 n n)).1
    exact (hE.row n).trans (realized_row_formula ΓY A e Q n).symm
  · funext n
    haveI : IsIso (cohomologyPiece A.filtration 0 n).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2
        (EdgesAndFiveTerms.cohomologyPiece_zero_eq_top A.filtration A.pages
          A.convergence.finite Q' n)
    haveI : Epi (EdgesAndFiveTerms.ambientClass A.filtration 0 n) := by
      dsimp only [EdgesAndFiveTerms.ambientClass]
      infer_instance
    haveI : IsIso (e.inv.target n) := ((targetEval n).mapIso e).isIso_inv
    apply (cancel_epi ((EdgesAndFiveTerms.ambientClass A.filtration 0 n ≫
      (A.targetIso n).hom) ≫ e.inv.target n)).1
    exact (hE.column n).trans (realized_column_formula ΓY A e Q n).symm

private lemma rowDegeneration
    (h : ∀ q : ℕ, 0 < q → IsZero ((higherDirectImage R S f φ q).obj M))
    (n : ℕ) : IsIso ((L.rowEdge n).app M) := by
  have hZ : ∀ p m : ℤ, m ≠ p → IsZero ((Seq).page 0 p m) :=
    sheafPage_isZero L M (fun p m => m ≠ p) fun p q hq => by
      haveI : (sectionCohomology S ⊤ p).Additive := by
        dsimp [sectionCohomology, rightValue]
        infer_instance
      exact (sectionCohomology S ⊤ p).map_isZero (h q (by omega))
  haveI : IsIso ((L.edges.filtered M).row n) := by
    rw [filtered_eq_realized L M]
    exact realized_row_isIso_of_support ΓY ModData ModIso
      (L.edges.objectCase.quadrant M) hZ n
  haveI : IsIso ((derivedFirstEdge D ΓY L.package n).app M) :=
    IsIso.of_isIso_fac_left (L.edges.first_comparison n M)
  change IsIso ((derivedFirstEdge D ΓY L.package n).app M ≫ (L.comparison n).hom.app ((stalk).obj M))
  infer_instance

private lemma columnDegeneration
    (h : ∀ p q : ℕ, 0 < p →
      IsZero (((higherDirectImage R S f φ q ⋙ sectionCohomology S ⊤ p).obj M)))
    (n : ℕ) : IsIso ((L.columnEdge n).app M) := by
  let Q := L.edges.objectCase.quadrant M
  let A := ModData
  let e := ModIso
  let Q' := realizedQuadrant ΓY A e Q
  have hZ : ∀ p m : ℤ, p ≠ 0 → IsZero (PageCohomology.object A.filtration A.pages 2 p m) := by
    intro p m hp
    have hz := sheafPage_isZero L M (fun p _ => p ≠ 0) (fun a b ha => h a b (by omega)) p m hp
    exact hz.of_iso ((pageEval 0 p m).mapIso e).symm
  haveI : IsIso ((modelEdges ΓY A Q').column (n : ℤ) (by omega)) :=
    columnEdge_isIso A.filtration A.pages A.convergence.finite (modelEdges ΓY A Q') hZ n (by omega)
  haveI : IsIso ((modelDiagramEdges ΓY A Q').column n) := by
    change IsIso ((A.targetIso n).inv ≫ (modelEdges ΓY A Q').column n (by omega))
    infer_instance
  haveI : IsIso ((L.edges.filtered M).column n) := by
    rw [filtered_eq_realized L M]
    exact transport_column_isIso e _ n
  haveI : IsIso ((classicalColumn D ΓY (L.edges.truncation n) L.edges.degreeZero).app M) :=
    IsIso.of_isIso_fac_left (L.edges.second_comparison n M)
  change IsIso ((L.comparison n).inv.app ((stalk).obj M) ≫
    (classicalColumn D ΓY (L.edges.truncation n) L.edges.degreeZero).app M)
  infer_instance

end Global

/-- Leray on bounded-below derived inputs and its first-quadrant sheaf
specialization, with the two natural degeneration isomorphisms. -/
theorem leray : GlobalStatement.{u} := by
  intro X Y R S f φ
  let D := directImage R S f φ
  let G := globalSections S
  have hExact := DerivedSectionsComposition.leftExact R S f φ
  letI := hExact.1
  letI := hExact.2
  obtain ⟨P, ⟨E⟩⟩ := grothendieck_edges (Modules R) (Modules S)
    (ModuleCat.{u} (sectionRing S ⊤)) D G (DerivedSectionsComposition.compositionHypothesis R S f φ)
  obtain ⟨sections⟩ := DerivedSectionsComposition.derivedComposition R S f φ
  let L : LerayData R S f φ :=
    { package := P
      edges := E
      sections := sections }
  exact ⟨L, rowDegeneration L, columnDegeneration L⟩

end AdvancedHomologicalAlgebra.LerayAndDegenerations
