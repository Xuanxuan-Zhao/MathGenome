import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredPageFunctoriality
import Mathlib.Algebra.Homology.Additive

/-! HA-B03, source lines 822–885. Indices are filtration degree and
complementary degree. All page objects below are the fixed HA-F03 quotients.
The bicomplex convention is commuting and the total differential is
`d_h + (-1)^p d_v`. For `ComplexShape.up ℤ`, its sign character `ε p`
is definitionally `p.negOnePow`. -/
noncomputable section
open scoped Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra.DoubleComplexFirstPages
open DoubleTotalization FiniteDiagonalFiltrations
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]

/-- Each included summand factors through the prescribed filtration step. -/
theorem summand_factors (axis : ℤ × ℤ → ℤ) (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K axis F) (a p q n : ℤ) (h : p+q=n)
    (ha : a ≤ axis (p,q)) : (F.piece a n).Factors (sumInjection K p q n h) := by
  obtain ⟨b, hb, ι, hι, eι, hbi⟩ := hF a n
  rw [← eι]
  apply (Subobject.factors_iff _ _).2
  refine ⟨b.ι ⟨⟨(p,q),h⟩,ha⟩ ≫ (Subobject.underlyingIso ι).inv, ?_⟩
  change (b.ι _ ≫ (Subobject.underlyingIso ι).inv) ≫ (Subobject.mk ι).arrow = _
  rw [Category.assoc, Subobject.underlyingIso_arrow]
  exact hbi ⟨⟨(p,q),h⟩,ha⟩

/-- The unique lift of a diagonal summand to an appropriate filtration step. -/
def summandToStep (axis : ℤ × ℤ → ℤ) (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K axis F) (a p q n : ℤ) (h : p+q=n)
    (ha : a ≤ axis (p,q)) : (K.X p).X q ⟶ (F.piece a n : A) :=
  (F.piece a n).factorThru _ (summand_factors K axis F hF a p q n h ha)

@[reassoc (attr := simp)]
theorem summandToStep_arrow (axis : ℤ × ℤ → ℤ) (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K axis F) (a p q n : ℤ) (h : p+q=n)
    (ha : a ≤ axis (p,q)) :
    summandToStep K axis F hF a p q n h ha ≫ (F.piece a n).arrow =
      sumInjection K p q n h := Subobject.factorThru_arrow _ _ _

/-- The distinguished column summand in the column associated graded. -/
def columnGradedInclusion (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K Prod.fst F) (p q : ℤ) :
    (K.X p).X q ⟶ (F.graded p).X (p+q) :=
  summandToStep K Prod.fst F hF p p q (p+q) rfl le_rfl ≫ (F.projection p).f (p+q)

/-- Unsigned vertical cohomology, with its horizontal differential induced by `d_h`. -/
def verticalHomology (q : ℤ) : CochainComplex A ℤ :=
  ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The map of horizontal complexes induced by a map of bicomplexes. -/
def verticalHomologyMap {L : Bicomplex A} (f : K ⟶ L) (q : ℤ) :
    verticalHomology K q ⟶ verticalHomology L q :=
  ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).mapHomologicalComplex
    (ComplexShape.up ℤ)).map f

variable {K}
/-- Actual filtered page, in the `(p,q)` convention. -/
abbrev page (F : Filtration (sumTotal K)) (D : F03Specs.PageData F) (r p q : ℤ) : A :=
  PageCohomology.object F D r p (p+q)

/-- Zeroth differential, with its target reindexed to complementary degree `q+1`. -/
def zeroDifferential (F : Filtration (sumTotal K)) (D : F03Specs.PageData F) (p q : ℤ) :
    page F D 0 p q ⟶ page F D 0 p (q+1) :=
  D.differential 0 (by omega) p (p+q) ≫ eqToHom (by
    congr 1 <;> omega)

/-- First differential, with its target reindexed to filtration degree `p+1`. -/
def firstDifferential (F : Filtration (sumTotal K)) (D : F03Specs.PageData F) (p q : ℤ) :
    page F D 1 p q ⟶ page F D 1 (p+1) q :=
  D.differential 1 (by omega) p (p+q) ≫ eqToHom (by
    congr 1 <;> omega)

/-- Express the three terms of the first-page differential in the coordinates
of an ordinary cochain complex, using the specified first-page maps. -/
def firstPageShortIso (F : Filtration (sumTotal K)) (D : F03Specs.PageData F)
    (L : CochainComplex A ℤ) (q : ℤ)
    (e : ∀ p, page F D 1 p q ≅ L.X p)
    (comm : ∀ p, firstDifferential F D p q ≫ (e (p+1)).hom =
      (e p).hom ≫ L.d p (p+1)) (p : ℤ) :
    PageCohomology.shortComplex F D 1 (by omega) p (p+q) ≅
      L.sc' p (p+1) (p+1+1) := by
  let e₂ : PageCohomology.object F D 1 (p+1) (p+q+1) ≅ page F D 1 (p+1) q :=
    eqToIso (congrArg (PageCohomology.object F D 1 (p+1)) (by omega))
  let e₃ : PageCohomology.object F D 1 (p+1+1) (p+q+1+1) ≅ page F D 1 (p+1+1) q :=
    eqToIso (congrArg (PageCohomology.object F D 1 (p+1+1)) (by omega))
  refine ShortComplex.isoMk (e p) (e₂ ≪≫ e (p+1)) (e₃ ≪≫ e (p+1+1)) ?_ ?_
  · change (e p).hom ≫ L.d p (p+1) =
      D.differential 1 (by omega) p (p+q) ≫ e₂.hom ≫ (e (p+1)).hom
    simpa only [firstDifferential, e₂, eqToIso.hom, Category.assoc] using (comm p).symm
  · change (e₂.hom ≫ (e (p+1)).hom) ≫ L.d (p+1) (p+1+1) =
      D.differential 1 (by omega) (p+1) (p+q+1) ≫ e₃.hom ≫ (e (p+1+1)).hom
    rw [Category.assoc, ← comm (p+1)]
    have transport (n n' : ℤ) (h : n = n') :
        eqToHom (congrArg (PageCohomology.object F D 1 (p+1)) h) ≫
            D.differential 1 (by omega) (p+1) n' =
          D.differential 1 (by omega) (p+1) n ≫
            eqToHom (congrArg (PageCohomology.object F D 1 (p+1+1))
              (congrArg (fun s => s+1) h)) := by
      subst n'
      simp
    simp only [firstDifferential, e₂, e₃, eqToIso.hom, ← Category.assoc,
      transport (p+q+1) ((p+1)+q) (by omega)]
    simp only [Category.assoc, eqToHom_trans]

/-- The second page is obtained from the actual next-page comparison and
the homology of the three first-page coordinate maps. -/
def SecondPageFormula (F : Filtration (sumTotal K)) (D : F03Specs.PageData F)
    (L : CochainComplex A ℤ) (q : ℤ)
    (e : ∀ p, page F D 1 p q ≅ L.X p)
    (comm : ∀ p, firstDifferential F D p q ≫ (e (p+1)).hom =
      (e p).hom ≫ L.d p (p+1))
    (second : ∀ p, page F D 2 p q ≅ L.homology p) : Prop :=
  ∃ C : PageCohomology.Data F D, ∀ p : ℤ,
    eqToIso (congrArg (PageCohomology.object F D 2 (p+1)) (show (p+1)+q = p+q+1 by omega))
        ≪≫ C.nextIso 1 (by omega) p (p+q)
        ≪≫ ShortComplex.homologyMapIso (firstPageShortIso F D L q e comm p)
        ≪≫ (L.homologyIsoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm =
      second (p+1)

variable (K)
/-- The distinguished row summand, with the filtration index written first. -/
def rowGradedInclusion (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K Prod.snd F) (p q : ℤ) :
    (K.X q).X p ⟶ (F.graded p).X (p+q) :=
  summandToStep K Prod.snd F hF p q p (p+q) (by omega) le_rfl ≫
    (F.projection p).f (p+q)

/-- Zeroth column page, including the associated graded and the differential. -/
structure ColumnZeroData (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K Prod.fst F) (D : F03Specs.PageData F) where
  gradedIso : ∀ p q, (F.graded p).X (p+q) ≅ (K.X p).X q
  graded_inv : ∀ p q, (gradedIso p q).inv = columnGradedInclusion K F hF p q
  graded_d : ∀ p q,
    (F.graded p).d (p+q) (p+(q+1)) ≫ (gradedIso p (q+1)).hom =
      (gradedIso p q).hom ≫ ((ComplexShape.up ℤ).ε p • (K.X p).d q (q+1))
  zeroIso : ∀ p q, page F D 0 p q ≅ (K.X p).X q
  zeroIso_eq : ∀ p q, zeroIso p q = D.zeroPageIso p (p+q) ≪≫ gradedIso p q
  zero_d : ∀ p q,
    zeroDifferential F D p q ≫ (zeroIso p (q+1)).hom =
      (zeroIso p q).hom ≫ ((ComplexShape.up ℤ).ε p • (K.X p).d q (q+1))

/-- The canonical column `E₁` objects. Representatives are
maps from arbitrary test objects. No lift from a projective object is assumed. -/
structure ColumnFirstData (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K Prod.fst F) (D : F03Specs.PageData F)
    extends ColumnZeroData K F hF D where
  firstIso : ∀ p q, page F D 1 p q ≅ (K.X p).homology q
  first_formula : ∀ p q {T : A} (x : T ⟶ (K.X p).X q)
    (hx : x ≫ (K.X p).d q (q+1) = 0)
    (a : T ⟶ (FilteredPage.almost F 1 p (p+q) : A))
    (_ha : a ≫ (FilteredPage.almost F 1 p (p+q)).arrow =
      x ≫ sumInjection K p q (p+q) rfl),
    a ≫ FilteredPage.toPage F 1 p (p+q) (D.containment 1 p (p+q)) ≫
      (firstIso p q).hom = (K.X p).liftCycles x (q+1) (by simp) hx ≫
        (K.X p).homologyπ q
/-- The first differential and its cohomology are the unsigned horizontal
cohomology differential and the second page. -/
structure ColumnData (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K Prod.fst F) (D : F03Specs.PageData F)
    extends ColumnFirstData K F hF D where
  first_d : ∀ p q,
    firstDifferential F D p q ≫ (firstIso (p+1) q).hom =
      (firstIso p q).hom ≫ HomologicalComplex.homologyMap (K.d p (p+1)) q
  secondIso : ∀ p q, page F D 2 p q ≅ (verticalHomology K q).homology p
  second_formula : ∀ q, SecondPageFormula F D (verticalHomology K q) q
    (fun p => firstIso p q) (fun p => first_d p q) (fun p => secondIso p q)

/-- Raw row pages: `d₀=d_h`, `d₁=(-1)^q H_h^q(d_v)`. -/
structure RowData (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K Prod.snd F) (D : F03Specs.PageData F) where
  gradedIso : ∀ p q, (F.graded p).X (p+q) ≅ (K.X q).X p
  graded_inv : ∀ p q, (gradedIso p q).inv = rowGradedInclusion K F hF p q
  graded_d : ∀ p q,
    (F.graded p).d (p+q) (p+(q+1)) ≫ (gradedIso p (q+1)).hom =
      (gradedIso p q).hom ≫ (K.d q (q+1)).f p
  zeroIso : ∀ p q, page F D 0 p q ≅ (K.X q).X p
  zeroIso_eq : ∀ p q, zeroIso p q = D.zeroPageIso p (p+q) ≪≫ gradedIso p q
  zero_d : ∀ p q,
    zeroDifferential F D p q ≫ (zeroIso p (q+1)).hom =
      (zeroIso p q).hom ≫ (K.d q (q+1)).f p
  firstIso : ∀ p q, page F D 1 p q ≅ (K.flip.X p).homology q
  first_formula : ∀ p q {T : A} (x : T ⟶ (K.X q).X p)
    (hx : x ≫ (K.d q (q+1)).f p = 0)
    (a : T ⟶ (FilteredPage.almost F 1 p (p+q) : A))
    (_ha : a ≫ (FilteredPage.almost F 1 p (p+q)).arrow =
      x ≫ sumInjection K q p (p+q) (by omega)),
    a ≫ FilteredPage.toPage F 1 p (p+q) (D.containment 1 p (p+q)) ≫
      (firstIso p q).hom = (K.flip.X p).liftCycles x (q+1) (by simp) hx ≫
        (K.flip.X p).homologyπ q
  first_d : ∀ p q,
    firstDifferential F D p q ≫ (firstIso (p+1) q).hom =
      (firstIso p q).hom ≫ ((ComplexShape.up ℤ).ε q •
        HomologicalComplex.homologyMap (K.flip.d p (p+1)) q)
  signed_first_d : ∀ p q,
    firstDifferential F D p q ≫ (((p+1)*q).negOnePow • (firstIso (p+1) q).hom) =
      ((p*q).negOnePow • (firstIso p q).hom) ≫ (verticalHomology K.flip q).d p (p+1)
  secondIso : ∀ p q, page F D 2 p q ≅ (verticalHomology K.flip q).homology p
  second_formula : ∀ q, SecondPageFormula F D (verticalHomology K.flip q) q
    (fun p => (p*q).negOnePow • firstIso p q) (fun p => signed_first_d p q)
    (fun p => secondIso p q)

/-- The signed total interchange induces actual isomorphisms on every page.
The representative equation fixes them as the induced filtered maps. -/
structure InterchangeData [K.flip.HasTotal (ComplexShape.up ℤ)]
    (Fr : Filtration (sumTotal K)) (G : Filtration (sumTotal K.flip))
    (Dr : F03Specs.PageData Fr) (Dt : F03Specs.PageData G) where
  forward : FilteredMap ⟨sumTotal K, Fr⟩ ⟨sumTotal K.flip, G⟩
  backward : FilteredMap ⟨sumTotal K.flip, G⟩ ⟨sumTotal K, Fr⟩
  forward_hom : forward.hom = (K.totalFlipIso (ComplexShape.up ℤ)).inv
  backward_hom : backward.hom = (K.totalFlipIso (ComplexShape.up ℤ)).hom
  pageIso : ∀ r p n, PageCohomology.object Fr Dr r p n ≅ PageCohomology.object G Dt r p n
  representative_formula : ∀ r p n,
    FilteredPage.toPage Fr r p n (Dr.containment r p n) ≫ (pageIso r p n).hom =
      FilteredPageFunctoriality.almostMap forward r p n ≫
        FilteredPage.toPage G r p n (Dt.containment r p n)
  differential_comm : ∀ r (hr : 0 ≤ r) p n,
    (pageIso r p n).hom ≫ Dt.differential r hr p n =
      Dr.differential r hr p n ≫ (pageIso r (p+r) (n+1)).hom

/-- Simultaneous natural identifications for all finite-diagonal bicomplexes,
all realizations of their prescribed filtrations, and the fixed page quotients. -/
structure System (A : Type u) [Category.{v} A] [Abelian A] where
  column : ∀ (K : Bicomplex A), FiniteDiagonals K →
    ∀ [K.HasTotal (ComplexShape.up ℤ)] (F : Filtration (sumTotal K))
      (hF : HasFiltrationFormula K Prod.fst F) (D : F03Specs.PageData F), ColumnData K F hF D
  row : ∀ (K : Bicomplex A), FiniteDiagonals K →
    ∀ [K.HasTotal (ComplexShape.up ℤ)] (F : Filtration (sumTotal K))
      (hF : HasFiltrationFormula K Prod.snd F) (D : F03Specs.PageData F), RowData K F hF D
  column_naturality : ∀ (K L : Bicomplex A) (hK : FiniteDiagonals K) (hL : FiniteDiagonals L)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (G : Filtration (sumTotal L))
    (hF : HasFiltrationFormula K Prod.fst F) (hG : HasFiltrationFormula L Prod.fst G)
    (D : F03Specs.PageData F) (E : F03Specs.PageData G) (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K,F⟩ ⟨sumTotal L,G⟩)
    (_hg : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E) (p q : ℤ),
    M.map 0 p (p+q) ≫ ((column L hL G hG E).zeroIso p q).hom =
      ((column K hK F hF D).zeroIso p q).hom ≫ (f.f p).f q ∧
    M.map 1 p (p+q) ≫ ((column L hL G hG E).firstIso p q).hom =
      ((column K hK F hF D).firstIso p q).hom ≫ HomologicalComplex.homologyMap (f.f p) q ∧
    M.map 2 p (p+q) ≫ ((column L hL G hG E).secondIso p q).hom =
      ((column K hK F hF D).secondIso p q).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K f q) p
  row_naturality : ∀ (K L : Bicomplex A) (hK : FiniteDiagonals K) (hL : FiniteDiagonals L)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (G : Filtration (sumTotal L))
    (hF : HasFiltrationFormula K Prod.snd F) (hG : HasFiltrationFormula L Prod.snd G)
    (D : F03Specs.PageData F) (E : F03Specs.PageData G) (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K,F⟩ ⟨sumTotal L,G⟩)
    (_hg : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E) (p q : ℤ),
    M.map 0 p (p+q) ≫ ((row L hL G hG E).zeroIso p q).hom =
      ((row K hK F hF D).zeroIso p q).hom ≫ (f.f q).f p ∧
    M.map 1 p (p+q) ≫ ((row L hL G hG E).firstIso p q).hom =
      ((row K hK F hF D).firstIso p q).hom ≫ HomologicalComplex.homologyMap
        (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f p) q ∧
    M.map 2 p (p+q) ≫ ((row L hL G hG E).secondIso p q).hom =
      ((row K hK F hF D).secondIso p q).hom ≫ HomologicalComplex.homologyMap
        (verticalHomologyMap K.flip
          ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) p
  interchange : ∀ (K : Bicomplex A) (hK : FiniteDiagonals K)
    [K.HasTotal (ComplexShape.up ℤ)] [K.flip.HasTotal (ComplexShape.up ℤ)]
    (hKt : FiniteDiagonals K.flip)
    (Fr : Filtration (sumTotal K)) (G : Filtration (sumTotal K.flip))
    (hr : HasFiltrationFormula K Prod.snd Fr) (hg : HasFiltrationFormula K.flip Prod.fst G)
    (Dr : F03Specs.PageData Fr) (Dt : F03Specs.PageData G),
    ∃ I : InterchangeData K Fr G Dr Dt, ∀ p q,
      (I.pageIso 1 p (p+q)).hom ≫ ((column K.flip hKt G hg Dt).firstIso p q).hom =
        (p*q).negOnePow • ((row K hK Fr hr Dr).firstIso p q).hom ∧
      (I.pageIso 2 p (p+q)).hom ≫ ((column K.flip hKt G hg Dt).secondIso p q).hom =
        ((row K hK Fr hr Dr).secondIso p q).hom

namespace Specs
/-- A separate incremental target for the completely specified zeroth column page. -/
def ColumnZero : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
  (F : Filtration (sumTotal K)) (hF : HasFiltrationFormula K Prod.fst F)
  (D : F03Specs.PageData F), Nonempty (ColumnZeroData K F hF D)

/-- Incremental first-page object identification, with its canonical class formula. -/
def ColumnFirstObjects : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
  (F : Filtration (sumTotal K)) (hF : HasFiltrationFormula K Prod.fst F)
  (D : F03Specs.PageData F), Nonempty (ColumnFirstData K F hF D)

/-- Column pages through the second page, with both specified differentials. -/
def ColumnPages : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
  (F : Filtration (sumTotal K)) (hF : HasFiltrationFormula K Prod.fst F)
  (D : F03Specs.PageData F), Nonempty (ColumnData K F hF D)

/-- HA-B03 with the original finite-diagonal hypothesis and full naturality,
including the signed row interchange and the raw row first differential. -/
def FullStatement : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A], Nonempty (System A)
end Specs
end AdvancedHomologicalAlgebra.DoubleComplexFirstPages
