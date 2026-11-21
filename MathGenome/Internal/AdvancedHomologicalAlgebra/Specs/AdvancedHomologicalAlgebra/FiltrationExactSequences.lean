import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredComplexes
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.Refinements

/-! Independent statements and canonical quotient objects for HA-F02.
The middle quotient is a cokernel in the abelian category of cochain complexes;
evaluation preserves this cokernel, so its terms are the stated quotients.
`p + 1 + 1` is the integer index `p + 2`.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
variable {A : Type u} [Category.{v} A] [Abelian A]
namespace Filtration
variable {K : CochainComplex A ℤ}

def doubleTransition (F : Filtration K) (p : ℤ) : F.step (p + 1 + 1) ⟶ F.step p :=
  F.transition (p + 1) ≫ F.transition p

def twoStepQuotient (F : Filtration K) (p : ℤ) : CochainComplex A ℤ :=
  cokernel (F.doubleTransition p)

def twoStepProjection (F : Filtration K) (p : ℤ) : F.step p ⟶ F.twoStepQuotient p :=
  cokernel.π (F.doubleTransition p)

def gradedToTwoStep (F : Filtration K) (p : ℤ) : F.graded (p + 1) ⟶ F.twoStepQuotient p :=
  F.quotientDesc (p + 1) (F.transition p ≫ F.twoStepProjection p) (by
    change F.transition (p + 1) ≫ F.transition p ≫ cokernel.π (F.doubleTransition p) = 0
    simpa only [doubleTransition, Category.assoc] using cokernel.condition (F.doubleTransition p))

def twoStepToGraded (F : Filtration K) (p : ℤ) : F.twoStepQuotient p ⟶ F.graded p :=
  cokernel.desc _ (F.projection p) (by
    ext n
    change ((F.transition (p + 1)).f n ≫ (F.transition p).f n) ≫
      cokernel.π ((F.transition p).f n) = 0
    simp only [Category.assoc, cokernel.condition, comp_zero])

def firstSequence (F : Filtration K) (p : ℤ) : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (F.transition p) (F.projection p) (by ext n; exact cokernel.condition _)

private theorem projection_gradedToTwoStep (F : Filtration K) (p : ℤ) :
    F.projection (p + 1) ≫ F.gradedToTwoStep p = F.transition p ≫ F.twoStepProjection p := by
  ext n
  exact cokernel.π_desc _ _ _

private theorem twoStepProjection_toGraded (F : Filtration K) (p : ℤ) :
    F.twoStepProjection p ≫ F.twoStepToGraded p = F.projection p :=
  cokernel.π_desc _ _ _

def secondSequence (F : Filtration K) (p : ℤ) : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (F.gradedToTwoStep p) (F.twoStepToGraded p) (by
    have : Epi (F.projection (p + 1)) :=
      HomologicalComplex.epi_of_epi_f _ (fun _ => inferInstanceAs (Epi (cokernel.π _)))
    apply (cancel_epi (F.projection (p + 1))).1
    rw [← Category.assoc, projection_gradedToTwoStep, Category.assoc,
      twoStepProjection_toGraded, comp_zero]
    ext n
    exact cokernel.condition _)
end Filtration

namespace FilteredMap
variable {X Y : FilteredComplex A}
def twoStepMap (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.twoStepQuotient p ⟶ Y.filtration.twoStepQuotient p :=
  cokernel.map _ _ (f.stepMap (p + 1 + 1)) (f.stepMap p) (by
    dsimp [Filtration.doubleTransition]
    rw [Category.assoc, f.transition_naturality p, ← Category.assoc,
      f.transition_naturality (p + 1), Category.assoc])
end FilteredMap

namespace F02Specs
/-- In every degree the middle complex is the quotient of the stated two
filtration steps, as a cokernel of their inclusion. -/
def DegreewiseQuotient : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p n : ℤ),
  Nonempty (IsColimit (CokernelCofork.ofπ ((F.twoStepProjection p).f n)
    (HomologicalComplex.congr_hom (cokernel.condition (F.doubleTransition p)) n)))

/-- Both sequences have the original objects and canonical arrows. -/
def ExactSequences : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p : ℤ),
  (F.firstSequence p).ShortExact ∧ (F.secondSequence p).ShortExact

/-- The canonical middle quotient is functorial for filtered maps. -/
def QuotientFunctoriality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A],
  (∀ (X : FilteredComplex A) (p : ℤ),
    (FilteredMap.id X).twoStepMap p = 𝟙 (X.filtration.twoStepQuotient p)) ∧
  (∀ {X Y Z : FilteredComplex A} (f : FilteredMap X Y) (g : FilteredMap Y Z) (p : ℤ),
    (f.comp g).twoStepMap p = f.twoStepMap p ≫ g.twoStepMap p)

/-- Naturality of all arrows of the two sequences. -/
def Naturality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A} (f : FilteredMap X Y) (p : ℤ),
  (X.filtration.transition p ≫ f.stepMap p =
    f.stepMap (p + 1) ≫ Y.filtration.transition p) ∧
  (X.filtration.projection p ≫ f.gradedMap p =
    f.stepMap p ≫ Y.filtration.projection p) ∧
  (X.filtration.gradedToTwoStep p ≫ f.twoStepMap p =
    f.gradedMap (p + 1) ≫ Y.filtration.gradedToTwoStep p) ∧
  (X.filtration.twoStepToGraded p ≫ f.gradedMap p =
    f.twoStepMap p ≫ Y.filtration.twoStepToGraded p)

/-- The usual connecting map sends the class of `x` to the class of `dx`.
Here `y` is precisely `dx` factored through the next filtration step.
All representatives are maps from any test object, with no projectivity assumption.
-/
def ConnectingFormula : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p n : ℤ)
  (h : (F.secondSequence p).ShortExact) {T : A}
  (x : T ⟶ (F.step p).X n)
  (hx : (x ≫ (F.projection p).f n) ≫ (F.graded p).d n (n + 1) = 0)
  (y : T ⟶ (F.step (p + 1)).X (n + 1))
  (hy : y ≫ (F.transition p).f (n + 1) = x ≫ (F.step p).d n (n + 1)),
  ∃ (hz : (y ≫ (F.projection (p + 1)).f (n + 1)) ≫
      (F.graded (p + 1)).d (n + 1) (n + 1 + 1) = 0),
    (F.graded p).liftCycles (x ≫ (F.projection p).f n) (n + 1) (by simp) hx ≫
        (F.graded p).homologyπ n ≫ h.δ n (n + 1) (by simp) =
      (F.graded (p + 1)).liftCycles (y ≫ (F.projection (p + 1)).f (n + 1))
        (n + 1 + 1) (by simp) hz ≫ (F.graded (p + 1)).homologyπ (n + 1)

/-- Every quotient cycle has a representative and a factored differential after
an epic cover. This supplies the lifts used in `ConnectingFormula` for arbitrary
abelian categories rather than assuming global lifts from the test object. -/
def RepresentativeLifts : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (p n : ℤ) {T : A}
  (z : T ⟶ (F.graded p).X n) (_hz : z ≫ (F.graded p).d n (n + 1) = 0),
  ∃ (T' : A) (e : T' ⟶ T) (_ : Epi e)
    (x : T' ⟶ (F.step p).X n) (y : T' ⟶ (F.step (p + 1)).X (n + 1)),
    x ≫ (F.projection p).f n = e ≫ z ∧
    y ≫ (F.transition p).f (n + 1) = x ≫ (F.step p).d n (n + 1)

/-- The connecting morphism is natural under filtered maps. -/
def ConnectingNaturality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A} (f : FilteredMap X Y) (p n : ℤ)
  (hX : (X.filtration.secondSequence p).ShortExact)
  (hY : (Y.filtration.secondSequence p).ShortExact),
  hX.δ n (n + 1) (by simp) ≫ HomologicalComplex.homologyMap (f.gradedMap (p + 1)) (n + 1) =
    HomologicalComplex.homologyMap (f.gradedMap p) n ≫ hY.δ n (n + 1) (by simp)
end F02Specs
end AdvancedHomologicalAlgebra
