import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence

/-! HA-S05, source lines 568–614. Indices `(p,n)` denote filtration and total
cochain degree. In particular row zero is `(n,n)` and column zero is `(0,n)`.
The representative equations below fix the edge maps canonically, using the
same closed representatives and cohomology image filtration as HA-S01.
They are equations of morphisms in an arbitrary abelian category.
No surjectivity at the final H² term is asserted. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace EdgesAndFiveTerms
open FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)

/-- Only E₂, not the original graded complex, is assumed first quadrant. -/
def FirstQuadrant : Prop := ∀ p n : ℤ, p < 0 ∨ n < p →
  IsZero (PageCohomology.object F D 2 p n)

/-- The ambient cohomology class of a closed filtered representative. -/
abbrev ambientClass (p n : ℤ) : (closed F p n : A) ⟶ K.homology n :=
  closedClass F p n ≫ (cohomologyPiece F p n).arrow

/-- The genuine page-two differential from (0,1) to (2,0). -/
abbrev transgression : PageCohomology.object F D 2 0 1 ⟶
    PageCohomology.object F D 2 2 2 :=
  D.differential 2 (by omega) 0 1

/-- Edge maps in every nonnegative degree, fixed by their closed-representative
formulas. The image and kernel identify the edges with the extreme pieces of
the actual induced cohomology filtration, rather than unrelated morphisms. -/
structure EdgeData where
  row : ∀ n : ℤ, 0 ≤ n → (PageCohomology.object F D 2 n n ⟶ K.homology n)
  column : ∀ n : ℤ, 0 ≤ n → (K.homology n ⟶ PageCohomology.object F D 2 0 n)
  row_formula : ∀ n hn,
    closedToPage F D 2 n n ≫ row n hn = ambientClass F n n
  column_formula : ∀ n hn,
    ambientClass F 0 n ≫ column n hn = closedToPage F D 2 0 n
  row_image : ∀ n hn, imageSubobject (row n hn) = cohomologyPiece F n n
  column_kernel : ∀ n hn, kernelSubobject (column n hn) = cohomologyPiece F 1 n

/-- Exactness at the four internal terms, including the initial injection.
This expresses precisely 0 → E₂¹⁰ → H¹ → E₂⁰¹ → E₂²⁰ → H². -/
structure FiveTermData (E : EdgeData F D) : Prop where
  row_mono : Mono (E.row 1 (by omega))
  row_column : E.row 1 (by omega) ≫ E.column 1 (by omega) = 0
  column_d : E.column 1 (by omega) ≫ transgression F D = 0
  d_row : transgression F D ≫ E.row 2 (by omega) = 0
  exact_H1 : (ShortComplex.mk (E.row 1 (by omega)) (E.column 1 (by omega)) row_column).Exact
  exact_E01 : (ShortComplex.mk (E.column 1 (by omega)) (transgression F D) column_d).Exact
  exact_E20 : (ShortComplex.mk (transgression F D) (E.row 2 (by omega)) d_row).Exact

/-- Simultaneous natural edges, with the source hypotheses on each complex.
Naturality holds for every page-map system satisfying the HA-F06 formulas. -/
structure System (A : Type u) [Category.{v} A] [Abelian A] where
  edges : ∀ (X : FilteredComplex A) (D : F03Specs.PageData X.filtration),
    DegreewiseFinite X.filtration → FirstQuadrant X.filtration D → EdgeData X.filtration D
  five_terms : ∀ (X : FilteredComplex A) (D : F03Specs.PageData X.filtration)
    (hF : DegreewiseFinite X.filtration) (hQ : FirstQuadrant X.filtration D),
    FiveTermData X.filtration D (edges X D hF hQ)
  row_naturality : ∀ {X Y : FilteredComplex A} (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (D' : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D D')
    (hX : DegreewiseFinite X.filtration) (hY : DegreewiseFinite Y.filtration)
    (hQX : FirstQuadrant X.filtration D) (hQY : FirstQuadrant Y.filtration D') n hn,
    M.map 2 n n ≫ (edges Y D' hY hQY).row n hn =
      (edges X D hX hQX).row n hn ≫ HomologicalComplex.homologyMap f.hom n
  column_naturality : ∀ {X Y : FilteredComplex A} (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (D' : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D D')
    (hX : DegreewiseFinite X.filtration) (hY : DegreewiseFinite Y.filtration)
    (hQX : FirstQuadrant X.filtration D) (hQY : FirstQuadrant Y.filtration D') n hn,
    HomologicalComplex.homologyMap f.hom n ≫ (edges Y D' hY hQY).column n hn =
      (edges X D hX hQX).column n hn ≫ M.map 2 0 n
end EdgesAndFiveTerms
namespace S05Specs
/-- HA-S05 with no bounds on the complex and no element-lifting assumptions. -/
def FullStatement : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A],
  Nonempty (EdgesAndFiveTerms.System A)
end S05Specs
end AdvancedHomologicalAlgebra
