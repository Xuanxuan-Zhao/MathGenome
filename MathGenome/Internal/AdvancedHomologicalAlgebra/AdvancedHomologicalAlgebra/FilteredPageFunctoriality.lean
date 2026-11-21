import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.PageCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredPageFunctoriality

/-! HA-F06: canonical functoriality and comparison of the actual filtered pages. -/
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

@[simp]
theorem almostMap_id (X : FilteredComplex A) (r p n : ℤ) :
    almostMap (FilteredMap.id X) r p n = 𝟙 _ := by
  apply (cancel_mono (almost X.filtration r p n).arrow).1
  simp [FilteredMap.id]

@[simp]
theorem almostMap_comp (f : FilteredMap X Y) (g : FilteredMap Y Z) (r p n : ℤ) :
    almostMap (f.comp g) r p n = almostMap f r p n ≫ almostMap g r p n := by
  apply (cancel_mono (almost Z.filtration r p n).arrow).1
  simp [FilteredMap.comp, Category.assoc]

/-- A quotient relation stays a quotient relation. The decomposition is made
on an epic cover, and equality descends along that cover. This also handles r=0. -/
theorem map_relation (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (r p n : ℤ) {T : A} (x : T ⟶ (almost X.filtration r p n : A))
    (hx : x ≫ toPage X.filtration r p n (D.containment r p n) = 0) :
    x ≫ almostMap f r p n ≫ toPage Y.filtration r p n (E.containment r p n) = 0 := by
  obtain ⟨T', e, he, u, v, huv⟩ :=
    PageCohomology.decompose_page_zero X.filtration r p n _ x hx
  have hu : (denominator Y.filtration r p n).Factors
      ((u ≫ almostMap f (r-1) (p+1) n) ≫
        (almost Y.filtration (r-1) (p+1) n).arrow) :=
    Subobject.factors_of_le _ le_sup_left (Subobject.factors_comp_arrow _)
  have hv : (denominator Y.filtration r p n).Factors
      ((v ≫ almostMap f (r-1) (p-r+1) (n-1)) ≫
        ((almost Y.filtration (r-1) (p-r+1) (n-1)).arrow ≫ Y.complex.d (n-1) n)) :=
    Subobject.factors_of_le _ le_sup_right (imageSubobject_factors_comp_self _ _)
  apply (cancel_epi e).1
  rw [comp_zero]
  suffices (e ≫ x ≫ almostMap f r p n) ≫
      toPage Y.filtration r p n (E.containment r p n) = 0 by
    simpa only [Category.assoc] using this
  apply (PageCohomology.toPage_zero_iff_denominator Y.filtration r p n _ _).2
  have hsum : (e ≫ x ≫ almostMap f r p n) ≫ (almost Y.filtration r p n).arrow =
      (u ≫ almostMap f (r-1) (p+1) n) ≫
        (almost Y.filtration (r-1) (p+1) n).arrow +
      (v ≫ almostMap f (r-1) (p-r+1) (n-1)) ≫
        ((almost Y.filtration (r-1) (p-r+1) (n-1)).arrow ≫ Y.complex.d (n-1) n) := by
    simpa only [Preadditive.add_comp, Category.assoc, almostMap_arrow, almostMap_arrow_assoc, f.hom.comm]
      using congrArg (fun a => a ≫ f.hom.f n) huv
  rw [hsum]
  exact Subobject.factors_add _ _ hu hv

/-- Descend the filtered map along the canonical epic representative map. -/
def pageMap (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (r p n : ℤ) : PageCohomology.object X.filtration D r p n ⟶
      PageCohomology.object Y.filtration E r p n :=
  Abelian.epiDesc (toPage X.filtration r p n (D.containment r p n))
    (almostMap f r p n ≫ toPage Y.filtration r p n (E.containment r p n))
    (map_relation f D E r p n _ (kernel.condition _))

@[reassoc (attr := simp)]
theorem toPage_pageMap (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (r p n : ℤ) :
    toPage X.filtration r p n (D.containment r p n) ≫ pageMap f D E r p n =
      almostMap f r p n ≫ toPage Y.filtration r p n (E.containment r p n) :=
  Abelian.comp_epiDesc _ _ _

/-- Uniqueness of induced maps, determined on all representatives. -/
theorem pageMap_unique (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (r p n : ℤ) (g : PageCohomology.object X.filtration D r p n ⟶
      PageCohomology.object Y.filtration E r p n)
    (hg : toPage X.filtration r p n (D.containment r p n) ≫ g =
      almostMap f r p n ≫ toPage Y.filtration r p n (E.containment r p n)) :
    g = pageMap f D E r p n := by
  apply (cancel_epi (toPage X.filtration r p n (D.containment r p n))).1
  rw [hg, toPage_pageMap]

@[simp]
theorem pageMap_id (X : FilteredComplex A) (D : F03Specs.PageData X.filtration)
    (r p n : ℤ) : pageMap (FilteredMap.id X) D D r p n = 𝟙 _ := by
  apply (cancel_epi (toPage X.filtration r p n (D.containment r p n))).1
  rw [toPage_pageMap, almostMap_id, Category.id_comp, Category.comp_id]

@[simp]
theorem pageMap_comp (f : FilteredMap X Y) (g : FilteredMap Y Z)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (G : F03Specs.PageData Z.filtration) (r p n : ℤ) :
    pageMap (f.comp g) D G r p n = pageMap f D E r p n ≫ pageMap g E G r p n := by
  apply (cancel_epi (toPage X.filtration r p n (D.containment r p n))).1
  rw [toPage_pageMap, almostMap_comp]
  symm
  rw [← Category.assoc, toPage_pageMap, Category.assoc, toPage_pageMap, Category.assoc]

/-- Naturality of the representative differential holds for all the allowed
choices of page data, by monicity of the almost-cycle inclusion. -/
theorem restriction_naturality (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    almostMap f r p n ≫ E.restriction r hr p n =
      D.restriction r hr p n ≫ almostMap f r (p+r) (n+1) := by
  apply (cancel_mono (almost Y.filtration r (p+r) (n+1)).arrow).1
  simp only [Category.assoc, E.restriction_arrow, almostMap_arrow,
    almostMap_arrow_assoc, f.hom.comm]
  simp only [← Category.assoc, D.restriction_arrow]

/-- Commutation with d_r in bidegree (r,1-r). -/
theorem pageMap_differential (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    pageMap f D E r p n ≫ E.differential r hr p n =
      D.differential r hr p n ≫ pageMap f D E r (p+r) (n+1) := by
  apply (cancel_epi (toPage X.filtration r p n (D.containment r p n))).1
  calc
    _ = almostMap f r p n ≫ E.restriction r hr p n ≫
        toPage Y.filtration r (p+r) (n+1) (E.containment r (p+r) (n+1)) := by
      rw [← Category.assoc, toPage_pageMap, Category.assoc, E.representative_formula]
    _ = D.restriction r hr p n ≫ almostMap f r (p+r) (n+1) ≫
        toPage Y.filtration r (p+r) (n+1) (E.containment r (p+r) (n+1)) := by
      rw [← Category.assoc, restriction_naturality f D E, Category.assoc]
    _ = _ := by
      symm
      rw [← Category.assoc, D.representative_formula, Category.assoc, toPage_pageMap]

/-- All maps for a fixed filtered morphism. -/
def mapData (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration) :
    MapData f D E where
  map := pageMap f D E
  representative_formula := toPage_pageMap f D E
  differential_comm := pageMap_differential f D E

/-- Restriction to the next almost-cycle subobject is natural. -/
theorem almostMap_succ (f : FilteredMap X Y) (r p n : ℤ) :
    almostMap f (r+1) p n ≫ Subobject.ofLE _ _
      (PageCohomology.almost_succ_le Y.filtration r p n) =
    Subobject.ofLE _ _ (PageCohomology.almost_succ_le X.filtration r p n) ≫
      almostMap f r p n := by
  apply (cancel_mono (almost Y.filtration r p n).arrow).1
  simp only [Category.assoc, Subobject.ofLE_arrow, almostMap_arrow,
    Subobject.ofLE_arrow_assoc]

/-- The representative inclusion used to construct the next page commutes
with the induced maps. -/
theorem nextRepresentative_naturality {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : MapData f D E) (r p n : ℤ) :
    PageCohomology.nextRepresentative X.filtration D r p n ≫ M.map r p n =
      almostMap f (r+1) p n ≫ PageCohomology.nextRepresentative Y.filtration E r p n := by
  dsimp only [PageCohomology.nextRepresentative]
  rw [Category.assoc, M.representative_formula, ← Category.assoc, ← almostMap_succ,
    Category.assoc]

/-- Naturality of the canonical next-page identification follows by checking
its defining formula on almost-cycle representatives and then on cycles. -/
theorem next_naturality {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : MapData f D E)
    (C : PageCohomology.Data X.filtration D) (C' : PageCohomology.Data Y.filtration E)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    M.map (r+1) (p+r) (n+1) ≫ (C'.nextIso r hr p n).hom =
      (C.nextIso r hr p n).hom ≫ ShortComplex.homologyMap (shortComplexMap M r hr p n) := by
  apply (cancel_epi (toPage X.filtration (r+1) (p+r) (n+1)
    (D.containment (r+1) (p+r) (n+1)))).1
  rw [← Category.assoc, M.representative_formula, Category.assoc, C'.nextIso_formula,
    ← Category.assoc _ (C.nextIso r hr p n).hom, C.nextIso_formula,
    Category.assoc, ShortComplex.homologyπ_naturality]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun a => a ≫ (PageCohomology.shortComplex Y.filtration E r hr p n).homologyπ)
  apply (cancel_mono (PageCohomology.shortComplex Y.filtration E r hr p n).iCycles).1
  simp only [Category.assoc, ShortComplex.liftCycles_i,
    ShortComplex.cyclesMap_i, ShortComplex.liftCycles_i_assoc]
  simpa only [PageCohomology.nextRepresentative, toPage, Category.assoc, shortComplexMap]
    using (nextRepresentative_naturality M r (p+r) (n+1)).symm

/-- A componentwise isomorphism of the current page induces an isomorphism
on the next page, by functoriality of three-term homology. -/
theorem isIso_succ_center {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : MapData f D E) (r : ℤ) (hr : 0 ≤ r)
    (h : ∀ p n, IsIso (M.map r p n)) (p n : ℤ) :
    IsIso (M.map (r+1) (p+r) (n+1)) := by
  let C := PageCohomology.data X.filtration D
  let C' := PageCohomology.data Y.filtration E
  let φ := shortComplexMap M r hr p n
  have : IsIso φ.τ₁ := h p n
  have : IsIso φ.τ₂ := h (p+r) (n+1)
  have : IsIso φ.τ₃ := h (p+r+r) (n+1+1)
  have : IsIso φ := ShortComplex.isIso_of_isIso φ
  have heq : M.map (r+1) (p+r) (n+1) =
      (C.nextIso r hr p n).hom ≫ ShortComplex.homologyMap φ ≫
        (C'.nextIso r hr p n).inv := by
    rw [← Category.assoc, ← next_naturality M C C' r hr p n, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- Comparison needs no convergence hypothesis and starts at any r ≥ 0,
including the zeroth and first pages. -/
theorem comparison {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : MapData f D E) (r : ℤ) (hr : 0 ≤ r)
    (h : ∀ p n, IsIso (M.map r p n)) (s : ℤ) (hs : r ≤ s) :
    ∀ p n, IsIso (M.map s p n) := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hs
  clear hs
  induction k with
  | zero =>
    rw [Int.natCast_zero, add_zero]
    exact h
  | succ k ih =>
    intro p n
    have hk : 0 ≤ r + (k : ℤ) := by omega
    have hh := isIso_succ_center M (r + (k : ℤ)) hk ih (p-(r+(k : ℤ))) (n-1)
    rw [sub_add_cancel, sub_add_cancel] at hh
    rw [show r + (↑(k+1) : ℤ) = r + (k : ℤ) + 1 by omega]
    exact hh

/-- The simultaneous functorial system, on every page and every filtered complex. -/
def system (A : Type u) [Category.{v} A] [Abelian A] : System A where
  maps := mapData
  map_id := pageMap_id
  map_comp := pageMap_comp
  next_naturality f D E C C' r hr p n := next_naturality (mapData f D E) C C' r hr p n
  comparison f D E r hr h s hs := comparison (mapData f D E) r hr h s hs

end FilteredPageFunctoriality

/-- HA-F06: functoriality and comparison of the actual filtered-complex pages. -/
theorem filtered_page_functoriality : F06Specs.FullStatement.{v,u} := by
  intro A _ _
  exact ⟨FilteredPageFunctoriality.system A⟩
end AdvancedHomologicalAlgebra
