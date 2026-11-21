import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredPages
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiltrationExactSequences

/-! Independent contract for HA-F04, source lines 263–309. All pages below
are the actual `FilteredPage.page` quotients of HA-F03. Total degree is `n`;
thus `(p+r,n+1)` has complementary degree `q-r+1` when `n=p+q`.
The short complex is indexed by its left term `(p,n)`, so its middle term
is `(p+r,n+1)`. As `p,n` range over the integers this covers every bidegree.
The representative equations specify the canonical isomorphisms, not just
abstract isomorphism of the underlying objects. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace PageCohomology
open FilteredPage
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

/-- Inclusion of the next almost-cycle subobject. -/
theorem almost_succ_le (r p n : ℤ) : almost F (r+1) p n ≤ almost F r p n := by
  apply inf_le_inf_left
  apply (Subobject.pullback (K.d n (n+1))).monotone
  simpa only [add_assoc] using F.decreasing (p+r) (n+1)

/-- The differential of an almost 1-cycle, in the next filtration step. -/
def firstLift (p n : ℤ) : (almost F 1 p n : A) ⟶ (F.piece (p+1) (n+1) : A) :=
  Subobject.ofLE _ _ inf_le_right ≫
    Subobject.pullbackπ (K.d n (n+1)) (F.piece (p+1) (n+1))

@[reassoc (attr := simp)]
theorem firstLift_arrow (p n : ℤ) :
    firstLift F p n ≫ (F.piece (p+1) (n+1)).arrow =
      (almost F 1 p n).arrow ≫ K.d n (n+1) := by
  dsimp only [firstLift]
  rw [Category.assoc, (Subobject.isPullback (K.d n (n+1))
    (F.piece (p+1) (n+1))).w, ← Category.assoc, Subobject.ofLE_arrow]

/-- An almost 1-cycle gives a cycle of the associated graded complex. -/
theorem firstRepresentative_cycle (p n : ℤ) :
    gradedRepresentative F p n (almost F 1 p n) inf_le_left ≫
      (F.graded p).d n (n+1) = 0 := by
  have hw : Subobject.ofLE _ _ (inf_le_left : almost F 1 p n ≤ F.piece p n) ≫
      (F.step p).d n (n+1) = firstLift F p n ≫ (F.transition p).f (n+1) := by
    apply (cancel_mono (F.piece p (n+1)).arrow).1
    simp [Filtration.step, Filtration.transition, Category.assoc]
  dsimp only [gradedRepresentative]
  rw [Category.assoc, (F.projection p).comm n (n+1), ← Category.assoc, hw,
    Category.assoc]
  change firstLift F p n ≫ ((F.transition p).f (n+1) ≫ cokernel.π _) = 0
  rw [cokernel.condition, comp_zero]

/-- The canonical homology class of an almost 1-cycle. -/
abbrev firstClass (p n : ℤ) :
    (almost F 1 p n : A) ⟶ (F.graded p).homology n :=
  (F.graded p).liftCycles (gradedRepresentative F p n (almost F 1 p n) inf_le_left)
    (n+1) (by simp) (firstRepresentative_cycle F p n) ≫ (F.graded p).homologyπ n

variable (D : F03Specs.PageData F)

abbrev object (r p n : ℤ) : A := page F r p n (D.containment r p n)

/-- Incoming and outgoing page differentials, centered at `(p+r,n+1)`. -/
def shortComplex (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) : ShortComplex A :=
  ShortComplex.mk (D.differential r hr p n)
    (D.differential r hr (p+r) (n+1)) (D.square_zero r hr p n)

/-- A representative on the next page gives an element of the current page. -/
abbrev nextRepresentative (r p n : ℤ) :
    (almost F (r+1) p n : A) ⟶ object F D r p n :=
  Subobject.ofLE _ _ (almost_succ_le F r p n) ≫ toPage F r p n (D.containment r p n)

/-- The zeroth page, including its differential, is the associated graded. -/
structure ZeroData where
  zeroIso : ∀ p n, object F D 0 p n ≅ (F.graded p).X n
  zeroIso_formula : ∀ p n,
    toPage F 0 p n (D.containment 0 p n) ≫ (zeroIso p n).hom =
      gradedRepresentative F p n (almost F 0 p n) inf_le_left
  zero_differential : ∀ p n,
    D.differential 0 (by omega) p n ≫
      (eqToIso (by simp only [add_zero] :
        object F D 0 (p+0) (n+1) = object F D 0 p (n+1))).hom ≫
          (zeroIso p (n+1)).hom =
      (zeroIso p n).hom ≫ (F.graded p).d n (n+1)

/-- The first page and its connecting differential, with representative formulas. -/
structure FirstData where
  firstIso : ∀ p n, object F D 1 p n ≅ (F.graded p).homology n
  firstIso_formula : ∀ p n,
    toPage F 1 p n (D.containment 1 p n) ≫ (firstIso p n).hom = firstClass F p n
  first_differential : ∀ p n (h : (F.secondSequence p).ShortExact),
    D.differential 1 (by omega) p n ≫ (firstIso (p+1) (n+1)).hom =
      (firstIso p n).hom ≫ h.δ n (n+1) (by simp)

/-- The entire sequence of canonical page-cohomology identifications. -/
structure Data extends ZeroData F D, FirstData F D where
  next_cycle : ∀ r (hr : 0 ≤ r) p n,
    nextRepresentative F D r (p+r) (n+1) ≫ D.differential r hr (p+r) (n+1) = 0
  nextIso : ∀ r (hr : 0 ≤ r) p n,
    object F D (r+1) (p+r) (n+1) ≅ (shortComplex F D r hr p n).homology
  nextIso_formula : ∀ r (hr : 0 ≤ r) p n,
    toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) ≫
        (nextIso r hr p n).hom =
      (shortComplex F D r hr p n).liftCycles
        (nextRepresentative F D r (p+r) (n+1)) (next_cycle r hr p n) ≫
          (shortComplex F D r hr p n).homologyπ
end PageCohomology

namespace F04Specs
open PageCohomology FilteredPage

/-- The zero page and its differential are the associated graded complex. -/
def ZeroPage : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F),
  Nonempty (ZeroData F D)

/-- The first-page identification includes the comparison of `d₁` with `δ`. -/
def FirstPages : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F),
  Nonempty (FirstData F D)

/-- Every next-page representative defines a cycle on the current page. -/
def NextCycles : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)
  (r : ℤ) (hr : 0 ≤ r) (p n : ℤ),
  nextRepresentative F D r p n ≫ D.differential r hr p n = 0

/-- Existence of the entire spectral sequence, under only the original
abelian-category and filtered-complex hypotheses. The witnessed page data has
exactly the fixed HA-F03 quotient objects and representative differential. -/
def FullStatement : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K),
  ∃ D : F03Specs.PageData F, Nonempty (Data F D)
end F04Specs
end AdvancedHomologicalAlgebra
