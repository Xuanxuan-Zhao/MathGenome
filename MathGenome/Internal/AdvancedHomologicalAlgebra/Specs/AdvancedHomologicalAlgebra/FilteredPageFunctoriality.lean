import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PageCohomology

/-! HA-F06, source Proposition F06 and its proof. The indices `(p,n)` mean
filtration degree and total degree, so maps below have bidegree zero.
The page objects, differentials, and canonical next-page identifications
are precisely those of HA-F03 and HA-F04. No boundedness is assumed. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace FilteredPageFunctoriality
open FilteredPage
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y Z : FilteredComplex A}

/-- A filtered cochain map takes almost cycles to almost cycles. -/
theorem almost_factors (f : FilteredMap X Y) (r p n : ℤ) :
    (almost Y.filtration r p n).Factors
      ((almost X.filtration r p n).arrow ≫ f.hom.f n) := by
  apply (Subobject.inf_factors _).2
  constructor
  · apply (Subobject.factors_iff _ _).2
    refine ⟨Subobject.ofLE _ _ inf_le_left ≫ f.component p n, ?_⟩
    simp [Category.assoc]
  · apply pullback_factors
    apply (Subobject.factors_iff _ _).2
    refine ⟨Subobject.ofLE _ _ inf_le_right ≫
      Subobject.pullbackπ (X.complex.d n (n+1)) (X.filtration.piece (p+r) (n+1)) ≫
        f.component (p+r) (n+1), ?_⟩
    change (Subobject.ofLE _ _ inf_le_right ≫
      Subobject.pullbackπ (X.complex.d n (n+1)) (X.filtration.piece (p+r) (n+1)) ≫
      f.component (p+r) (n+1)) ≫ (Y.filtration.piece (p+r) (n+1)).arrow =
        ((almost X.filtration r p n).arrow ≫ f.hom.f n) ≫ Y.complex.d n (n+1)
    simp only [Category.assoc, FilteredMap.component_arrow]
    rw [← Category.assoc (Subobject.pullbackπ _ _) _ _,
      (Subobject.isPullback (X.complex.d n (n+1))
        (X.filtration.piece (p+r) (n+1))).w]
    simp only [Category.assoc, Subobject.ofLE_arrow_assoc, f.hom.comm]

/-- The restriction of the ambient map to almost cycles. -/
def almostMap (f : FilteredMap X Y) (r p n : ℤ) :
    (almost X.filtration r p n : A) ⟶ (almost Y.filtration r p n : A) :=
  (almost Y.filtration r p n).factorThru _ (almost_factors f r p n)

@[reassoc (attr := simp)]
theorem almostMap_arrow (f : FilteredMap X Y) (r p n : ℤ) :
    almostMap f r p n ≫ (almost Y.filtration r p n).arrow =
      (almost X.filtration r p n).arrow ≫ f.hom.f n :=
  Subobject.factorThru_arrow _ _ _

/-- The induced maps on the actual page quotients, including their canonical
representative formula and their compatibility with every page differential. -/
structure MapData (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration) where
  map : ∀ r p n : ℤ, PageCohomology.object X.filtration D r p n ⟶
    PageCohomology.object Y.filtration E r p n
  representative_formula : ∀ r p n,
    toPage X.filtration r p n (D.containment r p n) ≫ map r p n =
      almostMap f r p n ≫ toPage Y.filtration r p n (E.containment r p n)
  differential_comm : ∀ r (hr : 0 ≤ r) p n,
    map r p n ≫ E.differential r hr p n =
      D.differential r hr p n ≫ map r (p+r) (n+1)

/-- The morphism of three-term page complexes, centered at `(p+r,n+1)`. -/
def shortComplexMap {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : MapData f D E) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    PageCohomology.shortComplex X.filtration D r hr p n ⟶
      PageCohomology.shortComplex Y.filtration E r hr p n where
  τ₁ := M.map r p n
  τ₂ := M.map r (p+r) (n+1)
  τ₃ := M.map r (p+r+r) (n+1+1)
  comm₁₂ := M.differential_comm r hr p n
  comm₂₃ := M.differential_comm r hr (p+r) (n+1)

/-- One simultaneous system on all filtered complexes. Identity/composition
hold for the actual induced maps. Naturality holds for every choice of the
canonical HA-F04 identifications (specified by their representative formulas).
An isomorphism on one entire page propagates to every later page. -/
structure System (A : Type u) [Category.{v} A] [Abelian A] where
  maps : ∀ {X Y : FilteredComplex A} (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration), MapData f D E
  map_id : ∀ (X : FilteredComplex A) (D : F03Specs.PageData X.filtration) r p n,
    (maps (FilteredMap.id X) D D).map r p n = 𝟙 _
  map_comp : ∀ {X Y Z : FilteredComplex A} (f : FilteredMap X Y) (g : FilteredMap Y Z)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (G : F03Specs.PageData Z.filtration) r p n,
    (maps (f.comp g) D G).map r p n =
      (maps f D E).map r p n ≫ (maps g E G).map r p n
  next_naturality : ∀ {X Y : FilteredComplex A} (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (C : PageCohomology.Data X.filtration D) (C' : PageCohomology.Data Y.filtration E)
    r (hr : 0 ≤ r) p n,
    (maps f D E).map (r+1) (p+r) (n+1) ≫ (C'.nextIso r hr p n).hom =
      (C.nextIso r hr p n).hom ≫ ShortComplex.homologyMap
        (shortComplexMap (maps f D E) r hr p n)
  comparison : ∀ {X Y : FilteredComplex A} (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    r (hr : 0 ≤ r), (∀ p n, IsIso ((maps f D E).map r p n)) →
      ∀ s, r ≤ s → ∀ p n, IsIso ((maps f D E).map s p n)
end FilteredPageFunctoriality

namespace F06Specs
/-- Full functoriality and comparison of all pages, for arbitrary abelian
categories and all decreasing filtered cochain complexes. -/
def FullStatement : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A],
  Nonempty (FilteredPageFunctoriality.System A)
end F06Specs
end AdvancedHomologicalAlgebra
