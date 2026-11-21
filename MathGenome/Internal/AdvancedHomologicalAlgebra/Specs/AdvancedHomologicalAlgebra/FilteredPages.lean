import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredComplexes
import Mathlib.CategoryTheory.Abelian.Subobject

/-! Independent objects and full expected statement for HA-F03.
Indices are `(p,n)` with total degree `n`; replacing `n` by `p+q` makes
`(p+r,n+1)` precisely the bidegree `(p+r,q-r+1)` of the source.
Images under the projection to the associated graded are the categorical
meaning of `(S + F^(p+1))/F^(p+1)`. No element or lifting assumptions occur.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace FilteredPage
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

/-- The almost cycles, as an actual subobject of the ambient term. -/
abbrev almost (r p n : ℤ) : Subobject (K.X n) :=
  F.piece p n ⊓ (Subobject.pullback (K.d n (n+1))).obj (F.piece (p+r) (n+1))

/-- Boundaries in the filtration step, before projecting to the graded piece. -/
abbrev boundarySource (r p n : ℤ) : Subobject (K.X n) :=
  F.piece p n ⊓ imageSubobject ((F.piece (p-r+1) (n-1)).arrow ≫ K.d (n-1) n)

/-- Projection of any subobject contained in the filtration step. -/
abbrev gradedRepresentative (p n : ℤ) (S : Subobject (K.X n)) (h : S ≤ F.piece p n) :
    (S : A) ⟶ (F.graded p).X n :=
  Subobject.ofLE _ _ h ≫ (F.projection p).f n

abbrev cycles (r p n : ℤ) : Subobject ((F.graded p).X n) :=
  imageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left)

abbrev boundaries (r p n : ℤ) : Subobject ((F.graded p).X n) :=
  imageSubobject (gradedRepresentative F p n (boundarySource F r p n) inf_le_left)

/-- The page is literally `Z_r/B_r`, once the required containment is proved. -/
abbrev page (r p n : ℤ) (h : boundaries F r p n ≤ cycles F r p n) : A :=
  cokernel (Subobject.ofLE _ _ h)

/-- The canonical epimorphism from almost cycles to the page. -/
abbrev toPage (r p n : ℤ) (h : boundaries F r p n ≤ cycles F r p n) :
    (almost F r p n : A) ⟶ page F r p n h :=
  factorThruImageSubobject (gradedRepresentative F p n (almost F r p n) inf_le_left) ≫
    cokernel.π (Subobject.ofLE _ _ h)

/-- The denominator in the source's equivalent quotient presentation, as an
ambient subobject. The quotient requires a proof that it lies in `almost`. -/
abbrev denominator (r p n : ℤ) : Subobject (K.X n) :=
  almost F (r-1) (p+1) n ⊔
    imageSubobject ((almost F (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n)

end FilteredPage

namespace F03Specs
open FilteredPage

-- Use an explicit dependent type for the exposed definition bindings.
def AlmostSubobjectType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (r p n : ℤ), Subobject (K.X n)
def AlmostValue : AlmostSubobjectType.{v,u} := fun F r p n => almost F r p n

def BoundarySourceValue : AlmostSubobjectType.{v,u} := fun F r p n => boundarySource F r p n

def GradedSubobjectType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (r p n : ℤ), Subobject ((F.graded p).X n)
def CyclesValue : GradedSubobjectType.{v,u} := fun F r p n => cycles F r p n
def BoundariesValue : GradedSubobjectType.{v,u} := fun F r p n => boundaries F r p n

def PageType := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (r p n : ℤ),
  boundaries F r p n ≤ cycles F r p n → A
def PageValue : PageType.{v,u} := fun F r p n h => page F r p n h

def BoundaryContainment : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K) (r p n : ℤ),
  boundaries F r p n ≤ cycles F r p n

/-- All constructions and conclusions of HA-F03, including the boundary page
and the representative-compatible quotient identification. The subobjects above
are fixed, so the witnesses cannot change the original page objects. -/
structure PageData {A : Type u} [Category.{v} A] [Abelian A]
    {K : CochainComplex A ℤ} (F : Filtration K) where
  containment : ∀ r p n, boundaries F r p n ≤ cycles F r p n
  differential : ∀ (r : ℤ), 0 ≤ r → ∀ p n,
    page F r p n (containment r p n) ⟶ page F r (p+r) (n+1) (containment r (p+r) (n+1))
  restriction : ∀ (r : ℤ), 0 ≤ r → ∀ p n,
    (almost F r p n : A) ⟶ (almost F r (p+r) (n+1) : A)
  restriction_arrow : ∀ r hr p n,
    restriction r hr p n ≫ (almost F r (p+r) (n+1)).arrow =
      (almost F r p n).arrow ≫ K.d n (n+1)
  representative_formula : ∀ r hr p n,
    toPage F r p n (containment r p n) ≫ differential r hr p n =
      restriction r hr p n ≫ toPage F r (p+r) (n+1) (containment r (p+r) (n+1))
  square_zero : ∀ r hr p n,
    differential r hr p n ≫ differential r hr (p+r) (n+1) = 0
  almost_zero : ∀ p n, almost F 0 p n = F.piece p n
  boundaries_zero : ∀ p n, boundaries F 0 p n = ⊥
  cycles_zero : ∀ p n, cycles F 0 p n = ⊤
  zeroPageIso : ∀ p n, page F 0 p n (containment 0 p n) ≅ (F.graded p).X n
  zeroPageIso_formula : ∀ p n,
    toPage F 0 p n (containment 0 p n) ≫ (zeroPageIso p n).hom =
      gradedRepresentative F p n (almost F 0 p n) inf_le_left
  zero_differential : ∀ p n,
    differential 0 (by omega) p n ≫
      (eqToIso (by simp only [add_zero] :
        page F 0 (p+0) (n+1) (containment 0 (p+0) (n+1)) =
        page F 0 p (n+1) (containment 0 p (n+1)))).hom ≫ (zeroPageIso p (n+1)).hom =
      (zeroPageIso p n).hom ≫ (F.graded p).d n (n+1)
  denominator_le : ∀ r, 1 ≤ r → ∀ p n, denominator F r p n ≤ almost F r p n
  quotientIso : ∀ r (hr : 1 ≤ r) p n,
    cokernel (Subobject.ofLE _ _ (denominator_le r hr p n)) ≅
      page F r p n (containment r p n)
  quotientIso_formula : ∀ r (hr : 1 ≤ r) p n,
    cokernel.π (Subobject.ofLE _ _ (denominator_le r hr p n)) ≫
      (quotientIso r hr p n).hom = toPage F r p n (containment r p n)

def FullStatement : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), Nonempty (PageData F)
end F03Specs
end AdvancedHomologicalAlgebra
