import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexFirstPages
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.PageCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FilteredPageFunctoriality

/-! HA-B03: column and row pages of a finite-diagonal commuting bicomplex.
The constructions use the fixed filtered-page quotients, preserve generalized
cycle classes, and are natural for all double-complex maps. The signed total
interchange acts on every page and has multiplier `(-1)^(p*q)` on `E₁`. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra.DoubleComplexFirstPages
open DoubleTotalization FiniteDiagonalFiltrations
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
variable (axis : ℤ × ℤ → ℤ) (F : Filtration (sumTotal K))
variable (hF : HasFiltrationFormula K axis F)

/-- Summand lifts jointly detect maps out of a filtration step. -/
theorem step_hom_ext {a n : ℤ} {T : A} {f g : (F.piece a n : A) ⟶ T}
    (h : ∀ p q (hpq : p+q=n) (ha : a ≤ axis (p,q)),
      summandToStep K axis F hF a p q n hpq ha ≫ f =
        summandToStep K axis F hF a p q n hpq ha ≫ g) : f = g := by
  obtain ⟨b, hb, ι, hι, eι, hbi⟩ := hF a n
  let e := Subobject.isoOfMkEq ι (F.piece a n) eι
  apply (cancel_epi e.hom).1
  apply hb.isColimit.hom_ext
  rintro ⟨i⟩
  have hi : b.ι i ≫ e.hom = summandToStep K axis F hF a i.val.val.1 i.val.val.2 n
      i.val.property i.property := by
    apply (cancel_mono (F.piece a n).arrow).1
    simp only [Category.assoc, summandToStep_arrow, e, Subobject.isoOfMkEq_hom,
      Subobject.ofMkLE_arrow]
    exact hbi i
  change b.ι i ≫ (e.hom ≫ f) = b.ι i ≫ (e.hom ≫ g)
  simpa only [← Category.assoc, hi] using h i.val.val.1 i.val.val.2 i.val.property i.property

/-- The universal map specified on all summands of a filtration step. -/
def stepDesc (a n : ℤ) {T : A}
    (f : ∀ p q, p+q=n → a ≤ axis (p,q) → ((K.X p).X q ⟶ T)) :
    (F.piece a n : A) ⟶ T := by
  let b := (hF a n).choose
  let hb := (hF a n).choose_spec.choose
  let ι := (hF a n).choose_spec.choose_spec.choose
  let hι := (hF a n).choose_spec.choose_spec.choose_spec.choose
  let : Mono ι := hι
  let eι := (hF a n).choose_spec.choose_spec.choose_spec.choose_spec.1
  exact (Subobject.isoOfMkEq ι (F.piece a n) eι).inv ≫
    hb.isColimit.desc (Cofan.mk T (fun i => f i.val.val.1 i.val.val.2 i.val.property i.property))

@[reassoc (attr := simp)]
theorem summandToStep_stepDesc (a p q n : ℤ) (hpq : p+q=n) (ha : a ≤ axis (p,q))
    {T : A} (f : ∀ p q, p+q=n → a ≤ axis (p,q) → ((K.X p).X q ⟶ T)) :
    summandToStep K axis F hF a p q n hpq ha ≫ stepDesc K axis F hF a n f =
      f p q hpq ha := by
  let b := (hF a n).choose
  let hb := (hF a n).choose_spec.choose
  let ι := (hF a n).choose_spec.choose_spec.choose
  let hι := (hF a n).choose_spec.choose_spec.choose_spec.choose
  let : Mono ι := hι
  let eι := (hF a n).choose_spec.choose_spec.choose_spec.choose_spec.1
  let e := Subobject.isoOfMkEq ι (F.piece a n) eι
  have hi : summandToStep K axis F hF a p q n hpq ha ≫ e.inv =
        b.ι ⟨⟨(p,q),hpq⟩,ha⟩ := by
    apply (cancel_mono ι).1
    simp only [Category.assoc, e, Subobject.isoOfMkEq_inv, Subobject.ofLEMk_comp,
      summandToStep_arrow]
    exact ((hF a n).choose_spec.choose_spec.choose_spec.choose_spec.2 ⟨⟨(p,q),hpq⟩,ha⟩).symm
  change summandToStep K axis F hF a p q n hpq ha ≫
    (e.inv ≫ hb.isColimit.desc _) = _
  rw [← Category.assoc, hi]
  exact hb.isColimit.fac _ ⟨⟨⟨(p,q),hpq⟩,ha⟩⟩

/-- A summand lifts compatibly through consecutive filtration steps. -/
@[reassoc]
theorem summandToStep_transition (a p q n : ℤ) (hpq : p+q=n)
    (ha : a+1 ≤ axis (p,q)) :
    summandToStep K axis F hF (a+1) p q n hpq ha ≫ (F.transition a).f n =
      summandToStep K axis F hF a p q n hpq (by omega) := by
  apply (cancel_mono (F.piece a n).arrow).1
  simp [Filtration.transition, Category.assoc]

/-- Higher-threshold summands vanish in the associated graded. -/
@[reassoc (attr := simp)]
theorem summandToStep_projection_zero (a p q n : ℤ) (hpq : p+q=n)
    (ha : a+1 ≤ axis (p,q)) (ha' : a ≤ axis (p,q)) :
    summandToStep K axis F hF a p q n hpq ha' ≫ (F.projection a).f n = 0 := by
  rw [← summandToStep_transition K axis F hF a p q n hpq ha, Category.assoc]
  change _ ≫ ((F.transition a).f n ≫ cokernel.π _) = 0
  simp only [cokernel.condition, comp_zero]

/-- The total differential on a lifted summand, before taking quotients. -/
theorem summandToStep_d (a p q n m : ℤ) (hpq : p+q=n) (hnm : n+1=m)
    (ha : a ≤ axis (p,q)) (hh : a ≤ axis (p+1,q)) (hv : a ≤ axis (p,q+1)) :
    summandToStep K axis F hF a p q n hpq ha ≫ (F.step a).d n m =
      (K.d p (p+1)).f q ≫
          summandToStep K axis F hF a (p+1) q m (by omega) hh +
        (ComplexShape.up ℤ).ε p • ((K.X p).d q (q+1) ≫
          summandToStep K axis F hF a p (q+1) m (by omega) hv) := by
  apply (cancel_mono (F.piece a m).arrow).1
  simp only [Category.assoc, Filtration.step, Filtration.differential_arrow,
    summandToStep_arrow_assoc, Preadditive.add_comp, Linear.units_smul_comp,
    summandToStep_arrow]
  exact sumDifferential K p (p+1) q (q+1) n m rfl rfl hpq (by omega) (by omega)

/-- The coordinate map between equal diagonal positions, and zero otherwise. -/
def coordinateLeg (p q r s : ℤ) : (K.X r).X s ⟶ (K.X p).X q :=
  if h : (r,s) = (p,q) then
    eqToHom (congrArg (fun i : ℤ × ℤ => (K.X i.1).X i.2) h) else 0

omit [K.HasTotal (ComplexShape.up ℤ)] in
@[simp] theorem coordinateLeg_self (p q : ℤ) : coordinateLeg K p q p q = 𝟙 _ := by
  simp [coordinateLeg]

omit [K.HasTotal (ComplexShape.up ℤ)] in
@[simp] theorem coordinateLeg_ne (p q r s : ℤ) (h : (r,s) ≠ (p,q)) :
    coordinateLeg K p q r s = 0 := by simp [coordinateLeg, h]

variable (Fc : Filtration (sumTotal K)) (hc : HasFiltrationFormula K Prod.fst Fc)

/-- The surviving coordinate on a column filtration step. -/
def columnCoordinate (p q : ℤ) : (Fc.piece p (p+q) : A) ⟶ (K.X p).X q :=
  stepDesc K Prod.fst Fc hc p (p+q) (fun r s _ _ => coordinateLeg K p q r s)

@[reassoc (attr := simp)]
theorem summandToStep_columnCoordinate (p q r s : ℤ) (hrs : r+s=p+q) (hr : p ≤ r) :
    summandToStep K Prod.fst Fc hc p r s (p+q) hrs hr ≫ columnCoordinate K Fc hc p q =
      coordinateLeg K p q r s := summandToStep_stepDesc _ _ _ _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem transition_columnCoordinate (p q : ℤ) :
    (Fc.transition p).f (p+q) ≫ columnCoordinate K Fc hc p q = 0 := by
  apply step_hom_ext K Prod.fst Fc hc
  intro r s hrs hr
  rw [← Category.assoc, summandToStep_transition, summandToStep_columnCoordinate]
  rw [comp_zero]
  exact coordinateLeg_ne K p q r s (by
    intro h; have := congrArg Prod.fst h; dsimp at this hr; omega)

/-- The quotient coordinate, inverse to the distinguished graded summand. -/
def columnGradedProjection (p q : ℤ) : (Fc.graded p).X (p+q) ⟶ (K.X p).X q :=
  cokernel.desc _ (columnCoordinate K Fc hc p q) (transition_columnCoordinate K Fc hc p q)

@[reassoc (attr := simp)]
theorem projection_columnGradedProjection (p q : ℤ) :
    (Fc.projection p).f (p+q) ≫ columnGradedProjection K Fc hc p q =
      columnCoordinate K Fc hc p q := cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
theorem columnGradedInclusion_projection (p q : ℤ) :
    columnGradedInclusion K Fc hc p q ≫ columnGradedProjection K Fc hc p q = 𝟙 _ := by
  simp [columnGradedInclusion, Category.assoc]

@[reassoc (attr := simp)]
theorem columnGradedProjection_inclusion (p q : ℤ) :
    columnGradedProjection K Fc hc p q ≫ columnGradedInclusion K Fc hc p q = 𝟙 _ := by
  apply (cancel_epi ((Fc.projection p).f (p+q))).1
  rw [← Category.assoc, projection_columnGradedProjection, Category.comp_id]
  apply step_hom_ext K Prod.fst Fc hc
  intro r s hrs hr
  rw [← Category.assoc, summandToStep_columnCoordinate]
  by_cases h : (r,s)=(p,q)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simp only [coordinateLeg_self, Category.id_comp]
    rfl
  · rw [coordinateLeg_ne K p q r s h, zero_comp]
    symm
    apply summandToStep_projection_zero K Prod.fst Fc hc
    dsimp at hr ⊢
    have hne : r ≠ p := by
      intro he
      apply h
      apply Prod.ext he
      omega
    omega

/-- The actual associated graded term is canonically its diagonal factor. -/
def columnGradedIso (p q : ℤ) : (Fc.graded p).X (p+q) ≅ (K.X p).X q where
  hom := columnGradedProjection K Fc hc p q
  inv := columnGradedInclusion K Fc hc p q
  hom_inv_id := columnGradedProjection_inclusion K Fc hc p q
  inv_hom_id := columnGradedInclusion_projection K Fc hc p q

/-- On the associated graded the horizontal term disappears. -/
@[reassoc]
theorem columnGradedInclusion_d (p q : ℤ) :
    columnGradedInclusion K Fc hc p q ≫ (Fc.graded p).d (p+q) (p+(q+1)) =
      (ComplexShape.up ℤ).ε p •
        ((K.X p).d q (q+1) ≫ columnGradedInclusion K Fc hc p (q+1)) := by
  unfold columnGradedInclusion
  rw [Category.assoc, (Fc.projection p).comm, ← Category.assoc,
    summandToStep_d K Prod.fst Fc hc p p q (p+q) (p+(q+1)) rfl (by omega)
      le_rfl (by dsimp; omega) le_rfl]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    summandToStep_projection_zero K Prod.fst Fc hc p (p+1) q (p+(q+1))
      (by omega) le_rfl (by dsimp; omega), comp_zero, zero_add]

/-- The quotient isomorphisms also identify the associated graded differential. -/
theorem columnGradedIso_d (p q : ℤ) :
    (Fc.graded p).d (p+q) (p+(q+1)) ≫ (columnGradedIso K Fc hc p (q+1)).hom =
      (columnGradedIso K Fc hc p q).hom ≫
        ((ComplexShape.up ℤ).ε p • (K.X p).d q (q+1)) := by
  apply (cancel_epi (columnGradedIso K Fc hc p q).inv).1
  change columnGradedInclusion K Fc hc p q ≫
    ((Fc.graded p).d (p+q) (p+(q+1)) ≫ columnGradedProjection K Fc hc p (q+1)) =
      columnGradedInclusion K Fc hc p q ≫
        (columnGradedProjection K Fc hc p q ≫ _)
  rw [← Category.assoc, columnGradedInclusion_d]
  simp only [Linear.units_smul_comp, Category.assoc, columnGradedInclusion_projection,
    Category.comp_id]
  rw [← Category.assoc, columnGradedInclusion_projection, Category.id_comp]

/-- Reindex the target of the zeroth-page differential along any degree equality. -/
theorem zeroDifferential_at (D : F03Specs.PageData Fc) (p n m : ℤ) (h : n+1=m) :
    D.differential 0 (by omega) p n ≫
        eqToHom (by congr 1 <;> omega :
          PageCohomology.object Fc D 0 (p+0) (n+1) = PageCohomology.object Fc D 0 p m) ≫
          (D.zeroPageIso p m).hom =
      (D.zeroPageIso p n).hom ≫ (Fc.graded p).d n m := by
  subst m
  exact D.zero_differential p n

/-- The zeroth-page differential formula, in complementary degree notation. -/
theorem zeroDifferential_zeroPageIso (D : F03Specs.PageData Fc) (p q : ℤ) :
    zeroDifferential Fc D p q ≫ (D.zeroPageIso p (p+(q+1))).hom =
      (D.zeroPageIso p (p+q)).hom ≫ (Fc.graded p).d (p+q) (p+(q+1)) := by
  exact (Category.assoc _ _ _).trans (zeroDifferential_at K Fc D p (p+q) (p+(q+1)) (by omega))

/-- Complete zeroth column page in the original, arbitrary abelian category. -/
def columnZeroData (D : F03Specs.PageData Fc) : ColumnZeroData K Fc hc D where
  gradedIso := columnGradedIso K Fc hc
  graded_inv _ _ := rfl
  graded_d := columnGradedIso_d K Fc hc
  zeroIso p q := D.zeroPageIso p (p+q) ≪≫ columnGradedIso K Fc hc p q
  zeroIso_eq _ _ := rfl
  zero_d p q := by
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc, zeroDifferential_zeroPageIso,
      Category.assoc, columnGradedIso_d, ← Category.assoc]

theorem column_zero_page : Specs.ColumnZero.{v,u} := by
  intro A _ _ K _ F hF D
  exact ⟨columnZeroData K F hF D⟩

/-- The graded coordinate isomorphism with an independently named total degree. -/
def columnGradedIsoAt (p q n : ℤ) (h : p+q=n) :
    (Fc.graded p).X n ≅ (K.X p).X q :=
  eqToIso (congrArg (Fc.graded p).X h.symm) ≪≫ columnGradedIso K Fc hc p q

@[simp] theorem columnGradedIsoAt_self (p q : ℤ) :
    columnGradedIsoAt K Fc hc p q (p+q) rfl = columnGradedIso K Fc hc p q := by
  simp only [columnGradedIsoAt, eqToIso_refl, Iso.refl_trans]

@[reassoc]
theorem columnGradedIsoAt_d (p q n m : ℤ) (h : p+q=n) (h' : p+(q+1)=m) :
    (Fc.graded p).d n m ≫ (columnGradedIsoAt K Fc hc p (q+1) m h').hom =
      (columnGradedIsoAt K Fc hc p q n h).hom ≫
        ((ComplexShape.up ℤ).ε p • (K.X p).d q (q+1)) := by
  subst n m
  simpa only [columnGradedIsoAt, eqToIso_refl, Iso.refl_trans] using
    columnGradedIso_d K Fc hc p q

/-- A version with an independently named next vertical degree. -/
theorem columnGradedIsoAt_d' (p q q' n m : ℤ) (hq : q+1=q')
    (h : p+q=n) (h' : p+q'=m) :
    (Fc.graded p).d n m ≫ (columnGradedIsoAt K Fc hc p q' m h').hom =
      (columnGradedIsoAt K Fc hc p q n h).hom ≫
        ((ComplexShape.up ℤ).ε p • (K.X p).d q q') := by
  subst q'
  exact columnGradedIsoAt_d K Fc hc p q n m h h'

/-- Endpoint signs remove the constant sign of a vertical differential while
leaving the middle coordinate, and hence the cohomology class, unchanged. -/
def columnShortIso (p q : ℤ) :
    (Fc.graded p).sc' (p+q-1) (p+q) (p+q+1) ≅
      (K.X p).sc' (q-1) q (q+1) := by
  refine ShortComplex.isoMk
    ((ComplexShape.up ℤ).ε p • columnGradedIsoAt K Fc hc p (q-1) (p+q-1) (by omega))
    (columnGradedIso K Fc hc p q)
    ((ComplexShape.up ℤ).ε p • columnGradedIsoAt K Fc hc p (q+1) (p+q+1) (by omega)) ?_ ?_
  · change ((ComplexShape.up ℤ).ε p • _ ) ≫ (K.X p).d (q-1) q =
      (Fc.graded p).d (p+q-1) (p+q) ≫ _
    have h : (Fc.graded p).d (p+q-1) (p+q) ≫ (columnGradedIso K Fc hc p q).hom =
        (columnGradedIsoAt K Fc hc p (q-1) (p+q-1) (by omega)).hom ≫
          ((ComplexShape.up ℤ).ε p • (K.X p).d (q-1) q) :=
      by simpa only [columnGradedIsoAt_self] using
        columnGradedIsoAt_d' K Fc hc p (q-1) q (p+q-1) (p+q) (by omega) (by omega) rfl
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul] using h.symm
  · change _ ≫ (K.X p).d q (q+1) =
      (Fc.graded p).d (p+q) (p+q+1) ≫ ((ComplexShape.up ℤ).ε p • _)
    have h : (Fc.graded p).d (p+q) (p+q+1) ≫
        (columnGradedIsoAt K Fc hc p (q+1) (p+q+1) (by omega)).hom =
          (columnGradedIso K Fc hc p q).hom ≫
            ((ComplexShape.up ℤ).ε p • (K.X p).d q (q+1)) :=
      by simpa only [columnGradedIsoAt_self] using
        columnGradedIsoAt_d K Fc hc p q (p+q) (p+q+1) rfl (by omega)
    rw [Linear.comp_units_smul, h, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul]

/-- Short-complex comparison with the unsigned vertical complex. -/
def columnCohomologyShortIso (p q : ℤ) : (Fc.graded p).sc (p+q) ≅ (K.X p).sc q :=
  (Fc.graded p).isoSc' (p+q-1) (p+q) (p+q+1) (by simp) (by simp) ≪≫
    columnShortIso K Fc hc p q ≪≫
      ((K.X p).isoSc' (q-1) q (q+1) (by simp) (by simp)).symm

@[simp] theorem columnCohomologyShortIso_middle (p q : ℤ) :
    (columnCohomologyShortIso K Fc hc p q).hom.τ₂ = (columnGradedIso K Fc hc p q).hom := by
  simp [columnCohomologyShortIso, columnShortIso, HomologicalComplex.isoSc',
    HomologicalComplex.natIsoSc']

/-- Cohomology of the graded column is unsigned vertical cohomology. -/
def columnHomologyIso (p q : ℤ) : (Fc.graded p).homology (p+q) ≅ (K.X p).homology q :=
  ShortComplex.homologyMapIso (columnCohomologyShortIso K Fc hc p q)

/-- The cohomology isomorphism sends the class of a graded cycle to the class
of its unsigned vertical coordinate. -/
theorem columnHomologyIso_class (p q : ℤ) {T : A}
    (x : T ⟶ (Fc.graded p).X (p+q))
    (hx : x ≫ (Fc.graded p).d (p+q) (p+q+1) = 0)
    (y : T ⟶ (K.X p).X q) (hy : y ≫ (K.X p).d q (q+1) = 0)
    (hxy : x ≫ (columnGradedIso K Fc hc p q).hom = y) :
    (Fc.graded p).liftCycles x (p+q+1) (by simp) hx ≫
        (Fc.graded p).homologyπ (p+q) ≫ (columnHomologyIso K Fc hc p q).hom =
      (K.X p).liftCycles y (q+1) (by simp) hy ≫ (K.X p).homologyπ q := by
  let e := columnCohomologyShortIso K Fc hc p q
  have he : e.hom.τ₂ = (columnGradedIso K Fc hc p q).hom :=
    columnCohomologyShortIso_middle K Fc hc p q
  have hz : (Fc.graded p).liftCycles x (p+q+1) (by simp) hx ≫
      ShortComplex.cyclesMap e.hom = (K.X p).liftCycles y (q+1) (by simp) hy := by
    apply (cancel_mono ((K.X p).iCycles q)).1
    change _ ≫ ((K.X p).sc q).iCycles = _
    rw [Category.assoc, ShortComplex.cyclesMap_i]
    change _ ≫ ((Fc.graded p).iCycles (p+q) ≫ e.hom.τ₂) = _
    rw [← Category.assoc, HomologicalComplex.liftCycles_i, he, hxy,
      HomologicalComplex.liftCycles_i]
  change (Fc.graded p).liftCycles x (p+q+1) (by simp) hx ≫
    ((Fc.graded p).sc (p+q)).homologyπ ≫ ShortComplex.homologyMap e.hom = _
  rw [ShortComplex.homologyπ_naturality, ← Category.assoc, hz]
  rfl

/-- The first-page object identification, on the fixed HA-F03 page. -/
def columnFirstIso (D : F03Specs.PageData Fc) (p q : ℤ) :
    page Fc D 1 p q ≅ (K.X p).homology q :=
  PageCohomology.firstIso Fc p (p+q) (D.containment 1 p (p+q)) ≪≫
    columnHomologyIso K Fc hc p q

/-- The `E₁` comparison preserves the class of each pure-column cycle. -/
theorem columnFirstIso_formula (D : F03Specs.PageData Fc) (p q : ℤ) {T : A}
    (x : T ⟶ (K.X p).X q) (hx : x ≫ (K.X p).d q (q+1) = 0)
    (a : T ⟶ (FilteredPage.almost Fc 1 p (p+q) : A))
    (ha : a ≫ (FilteredPage.almost Fc 1 p (p+q)).arrow =
      x ≫ sumInjection K p q (p+q) rfl) :
    a ≫ FilteredPage.toPage Fc 1 p (p+q) (D.containment 1 p (p+q)) ≫
        (columnFirstIso K Fc hc D p q).hom =
      (K.X p).liftCycles x (q+1) (by simp) hx ≫ (K.X p).homologyπ q := by
  have ha' : a ≫ Subobject.ofLE _ _
      (inf_le_left : FilteredPage.almost Fc 1 p (p+q) ≤ Fc.piece p (p+q)) =
      x ≫ summandToStep K Prod.fst Fc hc p p q (p+q) rfl le_rfl := by
    apply (cancel_mono (Fc.piece p (p+q)).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, summandToStep_arrow]
    exact ha
  have hg : a ≫ FilteredPage.gradedRepresentative Fc p (p+q)
      (FilteredPage.almost Fc 1 p (p+q)) inf_le_left =
      x ≫ columnGradedInclusion K Fc hc p q := by
    dsimp only [FilteredPage.gradedRepresentative, columnGradedInclusion]
    rw [← Category.assoc, ha', Category.assoc]
  have hcoord : (a ≫ FilteredPage.gradedRepresentative Fc p (p+q)
      (FilteredPage.almost Fc 1 p (p+q)) inf_le_left) ≫
        (columnGradedIso K Fc hc p q).hom = x := by
    rw [hg, Category.assoc]
    change x ≫ (columnGradedInclusion K Fc hc p q ≫ columnGradedProjection K Fc hc p q) = x
    rw [columnGradedInclusion_projection, Category.comp_id]
  dsimp only [columnFirstIso, Iso.trans_hom]
  rw [← Category.assoc (FilteredPage.toPage _ _ _ _ _) _ _,
    PageCohomology.toPage_firstIso]
  dsimp only [PageCohomology.firstClass]
  rw [← Category.assoc a, ← Category.assoc a,
    HomologicalComplex.comp_liftCycles]
  rw [Category.assoc]
  exact columnHomologyIso_class K Fc hc p q _ _ x hx hcoord

/-- The canonical first-page objects, including their zeroth-page data. -/
def columnFirstData (D : F03Specs.PageData Fc) : ColumnFirstData K Fc hc D where
  toColumnZeroData := columnZeroData K Fc hc D
  firstIso := columnFirstIso K Fc hc D
  first_formula := columnFirstIso_formula K Fc hc D

theorem column_first_objects : Specs.ColumnFirstObjects.{v,u} := by
  intro A _ _ K _ F hF D
  exact ⟨columnFirstData K F hF D⟩

/-- A vertically closed pure-column representative has only a horizontal
component in its total differential. -/
theorem columnCycle_total_d (p q n m : ℤ) (hpq : p+q=n) (hnm : n+1=m)
    {T : A} (x : T ⟶ (K.X p).X q) (hx : x ≫ (K.X p).d q (q+1) = 0) :
    x ≫ sumInjection K p q n hpq ≫ (sumTotal K).d n m =
      x ≫ (K.d p (p+1)).f q ≫ sumInjection K (p+1) q m (by omega) := by
  rw [sumDifferential K p (p+1) q (q+1) n m rfl rfl hpq (by omega) (by omega),
    Preadditive.comp_add]
  simp only [Linear.comp_units_smul, ← Category.assoc, hx, zero_comp, smul_zero, add_zero]

/-- A pure-column cycle is an almost cycle of filtration order one. -/
def columnAlmostCycle (p q : ℤ) {T : A} (x : T ⟶ (K.X p).X q)
    (hx : x ≫ (K.X p).d q (q+1) = 0) :
    T ⟶ (FilteredPage.almost Fc 1 p (p+q) : A) :=
  (FilteredPage.almost Fc 1 p (p+q)).factorThru
    (x ≫ sumInjection K p q (p+q) rfl) (by
      apply (Subobject.inf_factors _).2
      constructor
      · apply (Subobject.factors_iff _ _).2
        exact ⟨x ≫ summandToStep K Prod.fst Fc hc p p q (p+q) rfl le_rfl,
          by
            change (_ ≫ _) ≫ (Fc.piece p (p+q)).arrow = _
            simp only [Category.assoc, summandToStep_arrow]⟩
      · apply pullback_factors
        apply (Subobject.factors_iff _ _).2
        refine ⟨x ≫ (K.d p (p+1)).f q ≫
          summandToStep K Prod.fst Fc hc (p+1) (p+1) q (p+q+1) (by omega) le_rfl, ?_⟩
        change (_ ≫ _ ≫ _) ≫ (Fc.piece (p+1) (p+q+1)).arrow = _
        simp only [Category.assoc, summandToStep_arrow]
        simpa only [Category.assoc] using
          (columnCycle_total_d K p q (p+q) (p+q+1) rfl rfl x hx).symm)

@[reassoc (attr := simp)]
theorem columnAlmostCycle_arrow (p q : ℤ) {T : A} (x : T ⟶ (K.X p).X q)
    (hx : x ≫ (K.X p).d q (q+1) = 0) :
    columnAlmostCycle K Fc hc p q x hx ≫ (FilteredPage.almost Fc 1 p (p+q)).arrow =
      x ≫ sumInjection K p q (p+q) rfl := Subobject.factorThru_arrow _ _ _

/-- Pure vertical cycles generate the actual first page. -/
def columnCyclesToPage (D : F03Specs.PageData Fc) (p q : ℤ) :
    (K.X p).cycles q ⟶ page Fc D 1 p q :=
  columnAlmostCycle K Fc hc p q ((K.X p).iCycles q)
      ((K.X p).iCycles_d q (q+1)) ≫
    FilteredPage.toPage Fc 1 p (p+q) (D.containment 1 p (p+q))

@[reassoc (attr := simp)]
theorem columnCyclesToPage_firstIso (D : F03Specs.PageData Fc) (p q : ℤ) :
    columnCyclesToPage K Fc hc D p q ≫ (columnFirstIso K Fc hc D p q).hom =
      (K.X p).homologyπ q := by
  unfold columnCyclesToPage
  rw [Category.assoc, columnFirstIso_formula K Fc hc D p q ((K.X p).iCycles q)
    ((K.X p).iCycles_d q (q+1)) _
    (columnAlmostCycle_arrow K Fc hc p q _ _)]
  have h : (K.X p).liftCycles ((K.X p).iCycles q) (q+1) (by simp)
      ((K.X p).iCycles_d q (q+1)) = 𝟙 _ := by
    apply (cancel_mono ((K.X p).iCycles q)).1
    simp
  rw [h, Category.id_comp]

instance columnCyclesToPage_epi (D : F03Specs.PageData Fc) (p q : ℤ) :
    Epi (columnCyclesToPage K Fc hc D p q) := by
  have : Epi (columnCyclesToPage K Fc hc D p q ≫
      (columnFirstIso K Fc hc D p q).hom) := by
    rw [columnCyclesToPage_firstIso]; infer_instance
  exact (epi_comp_iff_of_isIso (columnCyclesToPage K Fc hc D p q)
    (columnFirstIso K Fc hc D p q).hom).1 this

/-- The first-page isomorphism with the total degree named independently. -/
def columnFirstIsoAt (D : F03Specs.PageData Fc) (p q n : ℤ) (h : p+q=n) :
    PageCohomology.object Fc D 1 p n ≅ (K.X p).homology q :=
  eqToIso (congrArg (PageCohomology.object Fc D 1 p) h.symm) ≪≫
    columnFirstIso K Fc hc D p q

@[simp] theorem columnFirstIsoAt_self (D : F03Specs.PageData Fc) (p q : ℤ) :
    columnFirstIsoAt K Fc hc D p q (p+q) rfl = columnFirstIso K Fc hc D p q := by
  simp only [columnFirstIsoAt, eqToIso_refl, Iso.refl_trans]

theorem columnFirstIsoAt_formula (D : F03Specs.PageData Fc) (p q n : ℤ) (h : p+q=n)
    {T : A} (x : T ⟶ (K.X p).X q) (hx : x ≫ (K.X p).d q (q+1) = 0)
    (a : T ⟶ (FilteredPage.almost Fc 1 p n : A))
    (ha : a ≫ (FilteredPage.almost Fc 1 p n).arrow = x ≫ sumInjection K p q n h) :
    a ≫ FilteredPage.toPage Fc 1 p n (D.containment 1 p n) ≫
        (columnFirstIsoAt K Fc hc D p q n h).hom =
      (K.X p).liftCycles x (q+1) (by simp) hx ≫ (K.X p).homologyπ q := by
  subst n
  simpa only [columnFirstIsoAt_self] using columnFirstIso_formula K Fc hc D p q x hx a ha

/-- The horizontal image of a vertical cycle remains a vertical cycle. -/
theorem columnCycle_horizontal (p q : ℤ) {T : A} (x : T ⟶ (K.X p).X q)
    (hx : x ≫ (K.X p).d q (q+1) = 0) :
    (x ≫ (K.d p (p+1)).f q) ≫ (K.X (p+1)).d q (q+1) = 0 := by
  rw [Category.assoc, (K.d p (p+1)).comm, ← Category.assoc, hx, zero_comp]

/-- On pure cycles the first filtered differential is induced by `d_h`. -/
theorem columnFirstIso_d_at (D : F03Specs.PageData Fc) (p q : ℤ) :
    D.differential 1 (by omega) p (p+q) ≫
        (columnFirstIsoAt K Fc hc D (p+1) q (p+q+1) (by omega)).hom =
      (columnFirstIso K Fc hc D p q).hom ≫ HomologicalComplex.homologyMap (K.d p (p+1)) q := by
  apply (cancel_epi (columnCyclesToPage K Fc hc D p q)).1
  let x := (K.X p).iCycles q
  have hx : x ≫ (K.X p).d q (q+1) = 0 := (K.X p).iCycles_d q (q+1)
  let a := columnAlmostCycle K Fc hc p q x hx
  have ha : (a ≫ D.restriction 1 (by omega) p (p+q)) ≫
      (FilteredPage.almost Fc 1 (p+1) (p+q+1)).arrow =
        (x ≫ (K.d p (p+1)).f q) ≫ sumInjection K (p+1) q (p+q+1) (by omega) := by
    rw [Category.assoc, D.restriction_arrow, ← Category.assoc,
      columnAlmostCycle_arrow, Category.assoc, columnCycle_total_d K p q (p+q) (p+q+1) rfl rfl x hx]
    rw [Category.assoc]
  change (a ≫ FilteredPage.toPage Fc 1 p (p+q) (D.containment 1 p (p+q))) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (FilteredPage.toPage _ _ _ _ _),
    D.representative_formula, Category.assoc, ← Category.assoc a,
    columnFirstIsoAt_formula K Fc hc D (p+1) q (p+q+1) (by omega)
      (x ≫ (K.d p (p+1)).f q) (columnCycle_horizontal K p q x hx) _ ha]
  rw [← Category.assoc, columnCyclesToPage_firstIso]
  rw [HomologicalComplex.homologyπ_naturality]
  congr 1

/-- The column first-page differential is the unsigned horizontal map. -/
theorem columnFirstIso_d (D : F03Specs.PageData Fc) (p q : ℤ) :
    firstDifferential Fc D p q ≫ (columnFirstIso K Fc hc D (p+1) q).hom =
      (columnFirstIso K Fc hc D p q).hom ≫ HomologicalComplex.homologyMap (K.d p (p+1)) q := by
  convert columnFirstIso_d_at K Fc hc D p q using 1
  dsimp only [firstDifferential, columnFirstIsoAt, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc]

/-- The differential formula with independent source and target total degrees. -/
theorem columnFirstIsoAt_d (D : F03Specs.PageData Fc) (p q n m : ℤ)
    (h : p+q=n) (h' : p+1+q=m) (hm : n+1=m) :
    D.differential 1 (by omega) p n ≫
        (columnFirstIsoAt K Fc hc D (p+1) q (n+1) (by omega)).hom =
      (columnFirstIsoAt K Fc hc D p q n h).hom ≫
        HomologicalComplex.homologyMap (K.d p (p+1)) q := by
  subst n
  simpa only [columnFirstIsoAt_self] using columnFirstIso_d_at K Fc hc D p q

/-- The three consecutive column first pages are the horizontal complex of
unsigned vertical cohomology. -/
def columnFirstShortIso (D : F03Specs.PageData Fc) (p q : ℤ) :
    PageCohomology.shortComplex Fc D 1 (by omega) p (p+q) ≅
      (verticalHomology K q).sc' p (p+1) (p+1+1) := by
  refine ShortComplex.isoMk
    (columnFirstIsoAt K Fc hc D p q (p+q) rfl)
    (columnFirstIsoAt K Fc hc D (p+1) q (p+q+1) (by omega))
    (columnFirstIsoAt K Fc hc D (p+1+1) q (p+q+1+1) (by omega)) ?_ ?_
  · exact (columnFirstIsoAt_d K Fc hc D p q (p+q) (p+q+1) rfl (by omega) rfl).symm
  · exact (columnFirstIsoAt_d K Fc hc D (p+1) q (p+q+1) (p+q+1+1)
      (by omega) (by omega) rfl).symm

private def secondIsoOfShortIso {K : Bicomplex A} [K.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (D : F03Specs.PageData F)
    (L : CochainComplex A ℤ) (q : ℤ)
    (e : ∀ t : ℤ, PageCohomology.shortComplex F D 1 (by omega) t (t+q) ≅
      L.sc' t (t+1) (t+1+1)) (p t : ℤ) (ht : t+1 = p) :
    page F D 2 p q ≅ L.homology p :=
  eqToIso (congrArg₂ (PageCohomology.object F D 2) ht.symm
      (show p+q = t+q+1 by omega)) ≪≫
    PageCohomology.nextIso F D 1 (by omega) t (t+q) ≪≫
      ShortComplex.homologyMapIso
        (e t ≪≫ (L.isoSc' t (t+1) (t+1+1) (by simp) (by simp)).symm) ≪≫
      eqToIso (congrArg (fun i : ℤ => L.homology i) ht)

private theorem secondPageFormula_of_shortIso {K : Bicomplex A} [K.HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (sumTotal K)) (D : F03Specs.PageData F)
    (L : CochainComplex A ℤ) (q : ℤ) (e : ∀ p, page F D 1 p q ≅ L.X p)
    (comm : ∀ p, firstDifferential F D p q ≫ (e (p+1)).hom =
      (e p).hom ≫ L.d p (p+1))
    (s : ∀ t : ℤ, PageCohomology.shortComplex F D 1 (by omega) t (t+q) ≅
      L.sc' t (t+1) (t+1+1))
    (hs : ∀ t, firstPageShortIso F D L q e comm t = s t) :
    SecondPageFormula F D L q e comm
      (fun p => secondIsoOfShortIso F D L q s p (p-1) (by omega)) := by
  refine ⟨PageCohomology.data F D, fun p => ?_⟩
  rw [hs]
  suffices ∀ t (ht : t = p), _ = secondIsoOfShortIso F D L q s (p+1) t (by omega) from
    this (p+1-1) (by omega)
  intro t ht
  subst t
  apply Iso.ext
  simp only [secondIsoOfShortIso, Iso.trans_hom, ShortComplex.homologyMapIso_hom, Iso.symm_hom,
    HomologicalComplex.homologyIsoSc', ShortComplex.homologyMap_comp,
    ShortComplex.homologyMapIso_inv, eqToIso.hom, eqToHom_refl, Category.comp_id]
  rfl

private theorem columnFirstShortIso_eq (D : F03Specs.PageData Fc) (p q : ℤ) :
    firstPageShortIso Fc D (verticalHomology K q) q
      (fun s => columnFirstIso K Fc hc D s q) (fun s => columnFirstIso_d K Fc hc D s q) p =
    columnFirstShortIso K Fc hc D p q := by
  apply Iso.ext
  ext
  · exact congrArg (fun e => e.hom) (columnFirstIsoAt_self K Fc hc D p q).symm
  · rfl
  · rfl

/-- Second column page: horizontal cohomology after unsigned vertical cohomology. -/
def columnSecondIso (D : F03Specs.PageData Fc) (p q : ℤ) :
    page Fc D 2 p q ≅ (verticalHomology K q).homology p :=
  secondIsoOfShortIso Fc D (verticalHomology K q) q
    (fun t => columnFirstShortIso K Fc hc D t q) p (p-1) (by omega)

/-- All column identifications through `E₂`, including both differentials. -/
def columnData (D : F03Specs.PageData Fc) : ColumnData K Fc hc D where
  toColumnFirstData := columnFirstData K Fc hc D
  first_d := columnFirstIso_d K Fc hc D
  secondIso := columnSecondIso K Fc hc D
  second_formula q := secondPageFormula_of_shortIso Fc D (verticalHomology K q) q
    (fun p => columnFirstIso K Fc hc D p q) (fun p => columnFirstIso_d K Fc hc D p q)
    (fun p => columnFirstShortIso K Fc hc D p q) (fun p => columnFirstShortIso_eq K Fc hc D p q)

/-- The entire column calculation through its second page. -/
theorem column_first_pages : Specs.ColumnPages.{v,u} := by
  intro A _ _ K _ F hF D
  exact ⟨columnData K F hF D⟩

section PageNaturality
variable {X Y : FilteredComplex A} (g : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData g D E)

/-- Restriction and projection of an almost cycle commute with filtered maps. -/
theorem almostMap_gradedRepresentative (r p n : ℤ) :
    FilteredPageFunctoriality.almostMap g r p n ≫
        FilteredPage.gradedRepresentative Y.filtration p n
          (FilteredPage.almost Y.filtration r p n) inf_le_left =
      FilteredPage.gradedRepresentative X.filtration p n
        (FilteredPage.almost X.filtration r p n) inf_le_left ≫ (g.gradedMap p).f n := by
  have h : FilteredPageFunctoriality.almostMap g r p n ≫ Subobject.ofLE _ _
      (inf_le_left : FilteredPage.almost Y.filtration r p n ≤ Y.filtration.piece p n) =
      Subobject.ofLE _ _ (inf_le_left : FilteredPage.almost X.filtration r p n ≤ X.filtration.piece p n) ≫
        g.component p n := by
    apply (cancel_mono (Y.filtration.piece p n).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, FilteredPageFunctoriality.almostMap_arrow,
      FilteredMap.component_arrow, Subobject.ofLE_arrow_assoc]
  dsimp only [FilteredPage.gradedRepresentative]
  rw [← Category.assoc, h, Category.assoc]
  simpa only [HomologicalComplex.comp_f, FilteredMap.stepMap, Category.assoc] using
    congrArg (fun t => Subobject.ofLE _ _
      (inf_le_left : FilteredPage.almost X.filtration r p n ≤ X.filtration.piece p n) ≫ t)
      (HomologicalComplex.congr_hom (g.projection_naturality p) n).symm

/-- The canonical zeroth-page comparison is natural for every induced page map. -/
theorem zeroPageIso_naturality (p n : ℤ) :
    M.map 0 p n ≫ (E.zeroPageIso p n).hom =
      (D.zeroPageIso p n).hom ≫ (g.gradedMap p).f n := by
  apply (cancel_epi (FilteredPage.toPage X.filtration 0 p n (D.containment 0 p n))).1
  rw [← Category.assoc, M.representative_formula, Category.assoc, E.zeroPageIso_formula,
    ← Category.assoc _ (D.zeroPageIso p n).hom, D.zeroPageIso_formula]
  exact almostMap_gradedRepresentative g 0 p n
end PageNaturality

section ColumnNaturality
variable {L : Bicomplex A} [L.HasTotal (ComplexShape.up ℤ)]
    (Gc : Filtration (sumTotal L)) (hgc : HasFiltrationFormula L Prod.fst Gc)
    (D : F03Specs.PageData Fc) (E : F03Specs.PageData Gc) (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K,Fc⟩ ⟨sumTotal L,Gc⟩)
    (hg : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E)

include hg

/-- A map of double complexes preserves the distinguished filtration summand. -/
theorem summandToStep_naturality (p q : ℤ) :
    summandToStep K Prod.fst Fc hc p p q (p+q) rfl le_rfl ≫ g.component p (p+q) =
      (f.f p).f q ≫ summandToStep L Prod.fst Gc hgc p p q (p+q) rfl le_rfl := by
  apply (cancel_mono (Gc.piece p (p+q)).arrow).1
  change (summandToStep K Prod.fst Fc hc p p q (p+q) rfl le_rfl ≫
      g.component p (p+q)) ≫ (Gc.piece p (p+q)).arrow =
    ((f.f p).f q ≫ summandToStep L Prod.fst Gc hgc p p q (p+q) rfl le_rfl) ≫
      (Gc.piece p (p+q)).arrow
  rw [Category.assoc, FilteredMap.component_arrow, ← Category.assoc, summandToStep_arrow,
    Category.assoc, summandToStep_arrow, hg]
  exact HomologicalComplex₂.ιTotal_map K L f (ComplexShape.up ℤ) p q (p+q) rfl

/-- The associated-graded coordinate comparison is natural. -/
theorem columnGradedIso_naturality (p q : ℤ) :
    (g.gradedMap p).f (p+q) ≫ (columnGradedIso L Gc hgc p q).hom =
      (columnGradedIso K Fc hc p q).hom ≫ (f.f p).f q := by
  apply (cancel_epi (columnGradedIso K Fc hc p q).inv).1
  change columnGradedInclusion K Fc hc p q ≫ _ = _
  rw [← Category.assoc, Iso.inv_hom_id_assoc]
  unfold columnGradedInclusion
  have hproj : (Fc.projection p).f (p+q) ≫ (g.gradedMap p).f (p+q) =
      g.component p (p+q) ≫ (Gc.projection p).f (p+q) := by
    exact HomologicalComplex.congr_hom (g.projection_naturality p) (p+q)
  calc
    ((summandToStep K Prod.fst Fc hc p p q (p+q) rfl le_rfl ≫ (Fc.projection p).f (p+q)) ≫
        (g.gradedMap p).f (p+q)) ≫ (columnGradedIso L Gc hgc p q).hom =
      summandToStep K Prod.fst Fc hc p p q (p+q) rfl le_rfl ≫
        ((Fc.projection p).f (p+q) ≫ (g.gradedMap p).f (p+q)) ≫
          (columnGradedIso L Gc hgc p q).hom := by simp only [Category.assoc]
    _ = (summandToStep K Prod.fst Fc hc p p q (p+q) rfl le_rfl ≫ g.component p (p+q)) ≫
        (Gc.projection p).f (p+q) ≫ (columnGradedIso L Gc hgc p q).hom := by
      rw [hproj]; simp only [Category.assoc]
    _ = ((f.f p).f q ≫ summandToStep L Prod.fst Gc hgc p p q (p+q) rfl le_rfl) ≫
        (Gc.projection p).f (p+q) ≫ (columnGradedIso L Gc hgc p q).hom := by
      rw [summandToStep_naturality K Fc hc Gc hgc f g hg]
    _ = (f.f p).f q := by
      simpa only [columnGradedIso, columnGradedInclusion, Category.assoc, Category.comp_id]
        using congrArg (fun z => (f.f p).f q ≫ z)
          (columnGradedInclusion_projection L Gc hgc p q)

/-- Naturality of the column zeroth page. -/
theorem columnZeroIso_naturality (p q : ℤ) :
    M.map 0 p (p+q) ≫ ((columnZeroData L Gc hgc E).zeroIso p q).hom =
      ((columnZeroData K Fc hc D).zeroIso p q).hom ≫ (f.f p).f q := by
  dsimp only [columnZeroData, Iso.trans_hom]
  rw [← Category.assoc, zeroPageIso_naturality g D E M, Category.assoc,
    columnGradedIso_naturality K Fc hc Gc hgc f g hg, ← Category.assoc]

/-- Naturality of the column first page, tested on its epic pure-cycle classes. -/
theorem columnFirstIso_naturality (p q : ℤ) :
    M.map 1 p (p+q) ≫ (columnFirstIso L Gc hgc E p q).hom =
      (columnFirstIso K Fc hc D p q).hom ≫ HomologicalComplex.homologyMap (f.f p) q := by
  apply (cancel_epi (columnCyclesToPage K Fc hc D p q)).1
  let x := (K.X p).iCycles q
  have hx : x ≫ (K.X p).d q (q+1) = 0 := (K.X p).iCycles_d q (q+1)
  let a := columnAlmostCycle K Fc hc p q x hx
  have hy : (x ≫ (f.f p).f q) ≫ (L.X p).d q (q+1) = 0 := by
    rw [Category.assoc, (f.f p).comm, ← Category.assoc, hx, zero_comp]
  have ha : (a ≫ FilteredPageFunctoriality.almostMap g 1 p (p+q)) ≫
      (FilteredPage.almost Gc 1 p (p+q)).arrow =
        (x ≫ (f.f p).f q) ≫ sumInjection L p q (p+q) rfl := by
    rw [Category.assoc, FilteredPageFunctoriality.almostMap_arrow, ← Category.assoc,
      columnAlmostCycle_arrow, Category.assoc, hg]
    simpa only [sumInjection, Category.assoc] using
      congrArg (fun z => x ≫ z) (HomologicalComplex₂.ιTotal_map K L f _ p q (p+q) rfl)
  change (a ≫ FilteredPage.toPage Fc 1 p (p+q) (D.containment 1 p (p+q))) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (FilteredPage.toPage _ _ _ _ _),
    M.representative_formula, Category.assoc, ← Category.assoc a,
    columnFirstIso_formula L Gc hgc E p q (x ≫ (f.f p).f q) hy _ ha,
    ← Category.assoc, columnCyclesToPage_firstIso, HomologicalComplex.homologyπ_naturality]
  congr 1
/-- First-page naturality with total degree specified independently. -/
theorem columnFirstIsoAt_naturality (p q n : ℤ) (h : p+q=n) :
    M.map 1 p n ≫ (columnFirstIsoAt L Gc hgc E p q n h).hom =
      (columnFirstIsoAt K Fc hc D p q n h).hom ≫ HomologicalComplex.homologyMap (f.f p) q := by
  subst n
  simpa only [columnFirstIsoAt_self] using
    columnFirstIso_naturality K Fc hc Gc hgc D E f g hg M p q

/-- The three-term comparison on the first column page is natural. -/
theorem columnFirstShortIso_naturality (p q : ℤ) :
    FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q) ≫
        (columnFirstShortIso L Gc hgc E p q).hom =
      (columnFirstShortIso K Fc hc D p q).hom ≫
        (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) p (p+1) (p+1+1)).map
          (verticalHomologyMap K f q) := by
  ext
  · exact columnFirstIsoAt_naturality K Fc hc Gc hgc D E f g hg M p q (p+q) rfl
  · exact columnFirstIsoAt_naturality K Fc hc Gc hgc D E f g hg M
      (p+1) q (p+q+1) (by omega)
  · exact columnFirstIsoAt_naturality K Fc hc Gc hgc D E f g hg M
      (p+1+1) q (p+q+1+1) (by omega)

/-- Naturality after identifying the three-term model with the standard short complex. -/
theorem columnFirstCohomologyShortIso_naturality (p q : ℤ) :
    FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q) ≫
        (columnFirstShortIso L Gc hgc E p q ≪≫
          ((verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm).hom =
      (columnFirstShortIso K Fc hc D p q ≪≫
          ((verticalHomology K q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm).hom ≫
        (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) (p+1)).map
          (verticalHomologyMap K f q) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, columnFirstShortIso_naturality K Fc hc Gc hgc D E f g hg M,
    Category.assoc]
  have h := (HomologicalComplex.natIsoSc' A (ComplexShape.up ℤ) p (p+1) (p+1+1)
    (by simp) (by simp)).inv.naturality (verticalHomologyMap K f q)
  simpa only [HomologicalComplex.isoSc', Iso.app_inv, Category.assoc] using
    congrArg (fun t => (columnFirstShortIso K Fc hc D p q).hom ≫ t) h

/-- Naturality of the homology induced by the first-page three-term comparison. -/
theorem columnFirstShortHomologyIso_naturality (p q : ℤ) :
    ShortComplex.homologyMap (FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q)) ≫
        (ShortComplex.homologyMapIso (columnFirstShortIso L Gc hgc E p q ≪≫
          ((verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom =
      (ShortComplex.homologyMapIso (columnFirstShortIso K Fc hc D p q ≪≫
          ((verticalHomology K q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K f q) (p+1) := by
  have h := congrArg (fun t => ShortComplex.homologyMap t)
    (columnFirstCohomologyShortIso_naturality K Fc hc Gc hgc D E f g hg M p q)
  simpa only [ShortComplex.homologyMap_comp, ShortComplex.homologyMapIso_hom, HomologicalComplex.homologyMap] using h

/-- The second-page comparison before reindexing its center is natural. -/
theorem columnSecondCoreIso_naturality (p q : ℤ) :
    M.map 2 (p+1) (p+q+1) ≫
        ((PageCohomology.nextIso Gc E 1 (by omega) p (p+q)).hom ≫
          (ShortComplex.homologyMapIso (columnFirstShortIso L Gc hgc E p q ≪≫
            ((verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom) =
      ((PageCohomology.nextIso Fc D 1 (by omega) p (p+q)).hom ≫
          (ShortComplex.homologyMapIso (columnFirstShortIso K Fc hc D p q ≪≫
            ((verticalHomology K q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom) ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K f q) (p+1) := by
  have hnext := FilteredPageFunctoriality.next_naturality M
    (PageCohomology.data Fc D) (PageCohomology.data Gc E) 1 (by omega) p (p+q)
  change M.map 2 (p+1) (p+q+1) ≫ (PageCohomology.nextIso Gc E 1 (by omega) p (p+q)).hom =
    (PageCohomology.nextIso Fc D 1 (by omega) p (p+q)).hom ≫
      ShortComplex.homologyMap (FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q)) at hnext
  rw [← Category.assoc, hnext, Category.assoc,
    columnFirstShortHomologyIso_naturality K Fc hc Gc hgc D E f g hg M, ← Category.assoc]

/-- Naturality commutes with equalities of filtration and total degree. -/
theorem pageMap_transport (r p p' n n' : ℤ) (hp : p=p') (hn : n=n') :
    M.map r p n ≫ eqToHom (congrArg₂ (PageCohomology.object Gc E r) hp hn) =
      eqToHom (congrArg₂ (PageCohomology.object Fc D r) hp hn) ≫ M.map r p' n' := by
  subst p' n'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The map on iterated homology commutes with an equality of its degree. -/
theorem verticalHomologyMap_transport (q p p' : ℤ) (hp : p=p') :
    HomologicalComplex.homologyMap (verticalHomologyMap K f q) p ≫
        eqToHom (congrArg (fun t => (verticalHomology L q).homology t) hp) =
      eqToHom (congrArg (fun t => (verticalHomology K q).homology t) hp) ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K f q) p' := by
  subst p'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Naturality of the column second page. -/
theorem columnSecondIso_naturality (p q : ℤ) :
    M.map 2 p (p+q) ≫ (columnSecondIso L Gc hgc E p q).hom =
      (columnSecondIso K Fc hc D p q).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K f q) p := by
  dsimp only [columnSecondIso, secondIsoOfShortIso, Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, pageMap_transport K Fc Gc D E f g hg M 2 p (p-1+1) (p+q) (p-1+q+1)
      (by omega) (by omega), Category.assoc]
  rw [← Category.assoc _ _ (eqToHom _)]
  rw [← Category.assoc (M.map 2 (p-1+1) (p-1+q+1)) _ (eqToHom _),
    columnSecondCoreIso_naturality K Fc hc Gc hgc D E f g hg M (p-1) q]
  rw [Category.assoc, verticalHomologyMap_transport K Fc Gc f g hg q (p-1+1) p (by omega)]
  simp only [Category.assoc]


end ColumnNaturality

omit [K.HasTotal (ComplexShape.up ℤ)] in
/-- Transposing the axes preserves finite diagonal support. -/
theorem finiteDiagonals_flip (hK : FiniteDiagonals K) : FiniteDiagonals K.flip := by
  intro n
  let e : Diagonal n ≃ Diagonal n :=
    { toFun := fun i => ⟨(i.val.2, i.val.1), by simpa only [add_comm] using i.property⟩
      invFun := fun i => ⟨(i.val.2, i.val.1), by simpa only [add_comm] using i.property⟩
      left_inv := fun i => by cases i; rfl
      right_inv := fun i => by cases i; rfl }
  have h := Set.Finite.preimage e.injective.injOn (hK n)
  exact h


variable (Fr : Filtration (sumTotal K)) (hr : HasFiltrationFormula K Prod.snd Fr)

/-- The surviving coordinate on a row filtration step. -/
def rowCoordinate (p q : ℤ) : (Fr.piece p (p+q) : A) ⟶ (K.X q).X p :=
  stepDesc K Prod.snd Fr hr p (p+q) (fun r s _ _ => coordinateLeg K q p r s)

@[reassoc (attr := simp)]
theorem summandToStep_rowCoordinate (p q r s : ℤ) (hrs : r+s=p+q) (hr' : p ≤ s) :
    summandToStep K Prod.snd Fr hr p r s (p+q) hrs hr' ≫ rowCoordinate K Fr hr p q =
      coordinateLeg K q p r s := summandToStep_stepDesc _ _ _ _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem transition_rowCoordinate (p q : ℤ) :
    (Fr.transition p).f (p+q) ≫ rowCoordinate K Fr hr p q = 0 := by
  apply step_hom_ext K Prod.snd Fr hr
  intro r s hrs hs
  rw [← Category.assoc, summandToStep_transition, summandToStep_rowCoordinate]
  rw [comp_zero]
  exact coordinateLeg_ne K q p r s (by
    intro h; have := congrArg Prod.snd h; dsimp at this hs; omega)

/-- The quotient coordinate, inverse to the distinguished graded summand. -/
def rowGradedProjection (p q : ℤ) : (Fr.graded p).X (p+q) ⟶ (K.X q).X p :=
  cokernel.desc _ (rowCoordinate K Fr hr p q) (transition_rowCoordinate K Fr hr p q)

@[reassoc (attr := simp)]
theorem projection_rowGradedProjection (p q : ℤ) :
    (Fr.projection p).f (p+q) ≫ rowGradedProjection K Fr hr p q =
      rowCoordinate K Fr hr p q := cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
theorem rowGradedInclusion_projection (p q : ℤ) :
    rowGradedInclusion K Fr hr p q ≫ rowGradedProjection K Fr hr p q = 𝟙 _ := by
  simp [rowGradedInclusion, Category.assoc]

@[reassoc (attr := simp)]
theorem rowGradedProjection_inclusion (p q : ℤ) :
    rowGradedProjection K Fr hr p q ≫ rowGradedInclusion K Fr hr p q = 𝟙 _ := by
  apply (cancel_epi ((Fr.projection p).f (p+q))).1
  rw [← Category.assoc, projection_rowGradedProjection, Category.comp_id]
  apply step_hom_ext K Prod.snd Fr hr
  intro r s hrs hs
  rw [← Category.assoc, summandToStep_rowCoordinate]
  by_cases h : (r,s)=(q,p)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simp only [coordinateLeg_self, Category.id_comp]
    rfl
  · rw [coordinateLeg_ne K q p r s h, zero_comp]
    symm
    apply summandToStep_projection_zero K Prod.snd Fr hr
    dsimp at hs ⊢
    have hne : s ≠ p := by
      intro he
      apply h
      apply Prod.ext (by omega) he
    omega

/-- The actual associated graded term is canonically its diagonal factor. -/
def rowGradedIso (p q : ℤ) : (Fr.graded p).X (p+q) ≅ (K.X q).X p where
  hom := rowGradedProjection K Fr hr p q
  inv := rowGradedInclusion K Fr hr p q
  hom_inv_id := rowGradedProjection_inclusion K Fr hr p q
  inv_hom_id := rowGradedInclusion_projection K Fr hr p q

/-- On the row associated graded, the vertical term disappears. -/
@[reassoc]
theorem rowGradedInclusion_d (p q : ℤ) :
    rowGradedInclusion K Fr hr p q ≫ (Fr.graded p).d (p+q) (p+(q+1)) =
      (K.d q (q+1)).f p ≫ rowGradedInclusion K Fr hr p (q+1) := by
  unfold rowGradedInclusion
  rw [Category.assoc, (Fr.projection p).comm, ← Category.assoc,
    summandToStep_d K Prod.snd Fr hr p q p (p+q) (p+(q+1)) (by omega) (by omega)
      le_rfl le_rfl (by dsimp; omega)]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    summandToStep_projection_zero K Prod.snd Fr hr p q (p+1) (p+(q+1))
      (by omega) le_rfl (by dsimp; omega), comp_zero, smul_zero, add_zero]

theorem rowGradedIso_d (p q : ℤ) :
    (Fr.graded p).d (p+q) (p+(q+1)) ≫ (rowGradedIso K Fr hr p (q+1)).hom =
      (rowGradedIso K Fr hr p q).hom ≫ (K.d q (q+1)).f p := by
  apply (cancel_epi (rowGradedIso K Fr hr p q).inv).1
  change rowGradedInclusion K Fr hr p q ≫
    ((Fr.graded p).d (p+q) (p+(q+1)) ≫ rowGradedProjection K Fr hr p (q+1)) =
      rowGradedInclusion K Fr hr p q ≫ (rowGradedProjection K Fr hr p q ≫ _)
  rw [← Category.assoc, rowGradedInclusion_d]
  simp only [Category.assoc, rowGradedInclusion_projection, Category.comp_id]
  rw [← Category.assoc, rowGradedInclusion_projection, Category.id_comp]

def rowGradedIsoAt (p q n : ℤ) (h : p+q=n) :
    (Fr.graded p).X n ≅ (K.X q).X p :=
  eqToIso (congrArg (Fr.graded p).X h.symm) ≪≫ rowGradedIso K Fr hr p q

@[simp] theorem rowGradedIsoAt_self (p q : ℤ) :
    rowGradedIsoAt K Fr hr p q (p+q) rfl = rowGradedIso K Fr hr p q := by
  simp only [rowGradedIsoAt, eqToIso_refl, Iso.refl_trans]

theorem rowGradedIsoAt_d (p q q' n m : ℤ) (hq : q+1=q')
    (h : p+q=n) (h' : p+q'=m) :
    (Fr.graded p).d n m ≫ (rowGradedIsoAt K Fr hr p q' m h').hom =
      (rowGradedIsoAt K Fr hr p q n h).hom ≫ (K.d q q').f p := by
  subst q' n m
  simpa only [rowGradedIsoAt_self] using rowGradedIso_d K Fr hr p q

def rowShortIso (p q : ℤ) :
    (Fr.graded p).sc' (p+q-1) (p+q) (p+q+1) ≅
      (K.flip.X p).sc' (q-1) q (q+1) := by
  refine ShortComplex.isoMk
    (rowGradedIsoAt K Fr hr p (q-1) (p+q-1) (by omega))
    (rowGradedIso K Fr hr p q)
    (rowGradedIsoAt K Fr hr p (q+1) (p+q+1) (by omega)) ?_ ?_
  · change (rowGradedIsoAt K Fr hr p (q-1) (p+q-1) (by omega)).hom ≫
      (K.d (q-1) q).f p = (Fr.graded p).d (p+q-1) (p+q) ≫ (rowGradedIso K Fr hr p q).hom
    simpa only [rowGradedIsoAt_self] using (rowGradedIsoAt_d K Fr hr p (q-1) q (p+q-1) (p+q) (by omega) (by omega) rfl).symm
  · change (rowGradedIso K Fr hr p q).hom ≫ (K.d q (q+1)).f p =
      (Fr.graded p).d (p+q) (p+q+1) ≫
        (rowGradedIsoAt K Fr hr p (q+1) (p+q+1) (by omega)).hom
    simpa only [rowGradedIsoAt_self] using (rowGradedIsoAt_d K Fr hr p q (q+1) (p+q) (p+q+1) rfl rfl (by omega)).symm

def rowCohomologyShortIso (p q : ℤ) : (Fr.graded p).sc (p+q) ≅ (K.flip.X p).sc q :=
  (Fr.graded p).isoSc' (p+q-1) (p+q) (p+q+1) (by simp) (by simp) ≪≫
    rowShortIso K Fr hr p q ≪≫
      ((K.flip.X p).isoSc' (q-1) q (q+1) (by simp) (by simp)).symm

@[simp] theorem rowCohomologyShortIso_middle (p q : ℤ) :
    (rowCohomologyShortIso K Fr hr p q).hom.τ₂ = (rowGradedIso K Fr hr p q).hom := by
  simp [rowCohomologyShortIso, rowShortIso, HomologicalComplex.isoSc',
    HomologicalComplex.natIsoSc']

def rowHomologyIso (p q : ℤ) : (Fr.graded p).homology (p+q) ≅ (K.flip.X p).homology q :=
  ShortComplex.homologyMapIso (rowCohomologyShortIso K Fr hr p q)
/-- The cohomology isomorphism sends the class of a graded cycle to the class
of its unsigned horizontal coordinate. -/
theorem rowHomologyIso_class (p q : ℤ) {T : A}
    (x : T ⟶ (Fr.graded p).X (p+q))
    (hx : x ≫ (Fr.graded p).d (p+q) (p+q+1) = 0)
    (y : T ⟶ (K.flip.X p).X q) (hy : y ≫ (K.flip.X p).d q (q+1) = 0)
    (hxy : x ≫ (rowGradedIso K Fr hr p q).hom = y) :
    (Fr.graded p).liftCycles x (p+q+1) (by simp) hx ≫
        (Fr.graded p).homologyπ (p+q) ≫ (rowHomologyIso K Fr hr p q).hom =
      (K.flip.X p).liftCycles y (q+1) (by simp) hy ≫ (K.flip.X p).homologyπ q := by
  let e := rowCohomologyShortIso K Fr hr p q
  have he : e.hom.τ₂ = (rowGradedIso K Fr hr p q).hom :=
    rowCohomologyShortIso_middle K Fr hr p q
  have hz : (Fr.graded p).liftCycles x (p+q+1) (by simp) hx ≫
      ShortComplex.cyclesMap e.hom = (K.flip.X p).liftCycles y (q+1) (by simp) hy := by
    apply (cancel_mono ((K.flip.X p).iCycles q)).1
    change _ ≫ ((K.flip.X p).sc q).iCycles = _
    rw [Category.assoc, ShortComplex.cyclesMap_i]
    change _ ≫ ((Fr.graded p).iCycles (p+q) ≫ e.hom.τ₂) = _
    rw [← Category.assoc, HomologicalComplex.liftCycles_i, he, hxy,
      HomologicalComplex.liftCycles_i]
  change (Fr.graded p).liftCycles x (p+q+1) (by simp) hx ≫
    ((Fr.graded p).sc (p+q)).homologyπ ≫ ShortComplex.homologyMap e.hom = _
  rw [ShortComplex.homologyπ_naturality, ← Category.assoc, hz]
  rfl

/-- The first-page object identification, on the fixed HA-F03 page. -/
def rowFirstIso (D : F03Specs.PageData Fr) (p q : ℤ) :
    page Fr D 1 p q ≅ (K.flip.X p).homology q :=
  PageCohomology.firstIso Fr p (p+q) (D.containment 1 p (p+q)) ≪≫
    rowHomologyIso K Fr hr p q

/-- The `E₁` comparison preserves the class of each pure-row cycle. -/
theorem rowFirstIso_formula (D : F03Specs.PageData Fr) (p q : ℤ) {T : A}
    (x : T ⟶ (K.flip.X p).X q) (hx : x ≫ (K.flip.X p).d q (q+1) = 0)
    (a : T ⟶ (FilteredPage.almost Fr 1 p (p+q) : A))
    (ha : a ≫ (FilteredPage.almost Fr 1 p (p+q)).arrow =
      x ≫ sumInjection K q p (p+q) (by omega)) :
    a ≫ FilteredPage.toPage Fr 1 p (p+q) (D.containment 1 p (p+q)) ≫
        (rowFirstIso K Fr hr D p q).hom =
      (K.flip.X p).liftCycles x (q+1) (by simp) hx ≫ (K.flip.X p).homologyπ q := by
  have ha' : a ≫ Subobject.ofLE _ _
      (inf_le_left : FilteredPage.almost Fr 1 p (p+q) ≤ Fr.piece p (p+q)) =
      x ≫ summandToStep K Prod.snd Fr hr p q p (p+q) (by omega) le_rfl := by
    apply (cancel_mono (Fr.piece p (p+q)).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, summandToStep_arrow]
    exact ha
  have hg : a ≫ FilteredPage.gradedRepresentative Fr p (p+q)
      (FilteredPage.almost Fr 1 p (p+q)) inf_le_left =
      x ≫ rowGradedInclusion K Fr hr p q := by
    dsimp only [FilteredPage.gradedRepresentative, rowGradedInclusion]
    rw [← Category.assoc, ha', Category.assoc]
  have hcoord : (a ≫ FilteredPage.gradedRepresentative Fr p (p+q)
      (FilteredPage.almost Fr 1 p (p+q)) inf_le_left) ≫
        (rowGradedIso K Fr hr p q).hom = x := by
    rw [hg, Category.assoc]
    change x ≫ (rowGradedInclusion K Fr hr p q ≫ rowGradedProjection K Fr hr p q) = x
    rw [rowGradedInclusion_projection]
    dsimp only [HomologicalComplex₂.flip_X_X] at x ⊢
    exact Category.comp_id x
  dsimp only [rowFirstIso, Iso.trans_hom]
  rw [← Category.assoc (FilteredPage.toPage _ _ _ _ _) _ _,
    PageCohomology.toPage_firstIso]
  dsimp only [PageCohomology.firstClass]
  rw [← Category.assoc a, ← Category.assoc a,
    HomologicalComplex.comp_liftCycles]
  rw [Category.assoc]
  exact rowHomologyIso_class K Fr hr p q _ _ x hx hcoord

def rowZeroIso (D : F03Specs.PageData Fr) (p q : ℤ) :
    page Fr D 0 p q ≅ (K.X q).X p :=
  D.zeroPageIso p (p+q) ≪≫ rowGradedIso K Fr hr p q

theorem rowZeroIso_d (D : F03Specs.PageData Fr) (p q : ℤ) :
    zeroDifferential Fr D p q ≫ (rowZeroIso K Fr hr D p (q+1)).hom =
      (rowZeroIso K Fr hr D p q).hom ≫ (K.d q (q+1)).f p := by
  dsimp only [rowZeroIso, Iso.trans_hom]
  rw [← Category.assoc, zeroDifferential_zeroPageIso,
    Category.assoc, rowGradedIso_d, ← Category.assoc]

/-- A horizontally closed pure-row representative has only a vertical component. -/
theorem rowCycle_total_d (p q n m : ℤ) (hpq : p+q=n) (hnm : n+1=m)
    {T : A} (x : T ⟶ (K.X q).X p) (hx : x ≫ (K.d q (q+1)).f p = 0) :
    x ≫ sumInjection K q p n (by omega) ≫ (sumTotal K).d n m =
      (ComplexShape.up ℤ).ε q •
        (x ≫ (K.X q).d p (p+1) ≫ sumInjection K q (p+1) m (by omega)) := by
  rw [sumDifferential K q (q+1) p (p+1) n m rfl rfl (by omega) (by omega) (by omega),
    Preadditive.comp_add]
  simp only [Linear.comp_units_smul, ← Category.assoc, hx, zero_comp, zero_add]

def rowAlmostCycle (p q : ℤ) {T : A} (x : T ⟶ (K.X q).X p)
    (hx : x ≫ (K.d q (q+1)).f p = 0) :
    T ⟶ (FilteredPage.almost Fr 1 p (p+q) : A) :=
  (FilteredPage.almost Fr 1 p (p+q)).factorThru
    (x ≫ sumInjection K q p (p+q) (by omega)) (by
      apply (Subobject.inf_factors _).2
      constructor
      · apply (Subobject.factors_iff _ _).2
        exact ⟨x ≫ summandToStep K Prod.snd Fr hr p q p (p+q) (by omega) le_rfl,
          by
            change (_ ≫ _) ≫ (Fr.piece p (p+q)).arrow = _
            simp only [Category.assoc, summandToStep_arrow]⟩
      · apply pullback_factors
        apply (Subobject.factors_iff _ _).2
        refine ⟨(ComplexShape.up ℤ).ε q • (x ≫ (K.X q).d p (p+1) ≫
          summandToStep K Prod.snd Fr hr (p+1) q (p+1) (p+q+1) (by omega) le_rfl), ?_⟩
        change ((ComplexShape.up ℤ).ε q • (_ ≫ _ ≫ _)) ≫
          (Fr.piece (p+1) (p+q+1)).arrow = _
        simp only [Linear.units_smul_comp, Category.assoc, summandToStep_arrow]
        simpa only [Category.assoc] using
          (rowCycle_total_d K p q (p+q) (p+q+1) rfl rfl x hx).symm)

@[reassoc (attr := simp)]
theorem rowAlmostCycle_arrow (p q : ℤ) {T : A} (x : T ⟶ (K.X q).X p)
    (hx : x ≫ (K.d q (q+1)).f p = 0) :
    rowAlmostCycle K Fr hr p q x hx ≫ (FilteredPage.almost Fr 1 p (p+q)).arrow =
      x ≫ sumInjection K q p (p+q) (by omega) := Subobject.factorThru_arrow _ _ _

def rowCyclesToPage (D : F03Specs.PageData Fr) (p q : ℤ) :
    (K.flip.X p).cycles q ⟶ page Fr D 1 p q :=
  rowAlmostCycle K Fr hr p q ((K.flip.X p).iCycles q)
      ((K.flip.X p).iCycles_d q (q+1)) ≫
    FilteredPage.toPage Fr 1 p (p+q) (D.containment 1 p (p+q))

@[reassoc (attr := simp)]
theorem rowCyclesToPage_firstIso (D : F03Specs.PageData Fr) (p q : ℤ) :
    rowCyclesToPage K Fr hr D p q ≫ (rowFirstIso K Fr hr D p q).hom =
      (K.flip.X p).homologyπ q := by
  unfold rowCyclesToPage
  rw [Category.assoc, rowFirstIso_formula K Fr hr D p q ((K.flip.X p).iCycles q)
    ((K.flip.X p).iCycles_d q (q+1)) _
    (rowAlmostCycle_arrow K Fr hr p q _ _)]
  have h : (K.flip.X p).liftCycles ((K.flip.X p).iCycles q) (q+1) (by simp)
      ((K.flip.X p).iCycles_d q (q+1)) = 𝟙 _ := by
    apply (cancel_mono ((K.flip.X p).iCycles q)).1
    simp
  rw [h, Category.id_comp]

instance rowCyclesToPage_epi (D : F03Specs.PageData Fr) (p q : ℤ) :
    Epi (rowCyclesToPage K Fr hr D p q) := by
  have : Epi (rowCyclesToPage K Fr hr D p q ≫
      (rowFirstIso K Fr hr D p q).hom) := by
    rw [rowCyclesToPage_firstIso]; infer_instance
  exact (epi_comp_iff_of_isIso (rowCyclesToPage K Fr hr D p q)
    (rowFirstIso K Fr hr D p q).hom).1 this

def rowFirstIsoAt (D : F03Specs.PageData Fr) (p q n : ℤ) (h : p+q=n) :
    PageCohomology.object Fr D 1 p n ≅ (K.flip.X p).homology q :=
  eqToIso (congrArg (PageCohomology.object Fr D 1 p) h.symm) ≪≫
    rowFirstIso K Fr hr D p q

@[simp] theorem rowFirstIsoAt_self (D : F03Specs.PageData Fr) (p q : ℤ) :
    rowFirstIsoAt K Fr hr D p q (p+q) rfl = rowFirstIso K Fr hr D p q := by
  simp only [rowFirstIsoAt, eqToIso_refl, Iso.refl_trans]

theorem rowFirstIsoAt_formula (D : F03Specs.PageData Fr) (p q n : ℤ) (h : p+q=n)
    {T : A} (x : T ⟶ (K.X q).X p) (hx : x ≫ (K.d q (q+1)).f p = 0)
    (a : T ⟶ (FilteredPage.almost Fr 1 p n : A))
    (ha : a ≫ (FilteredPage.almost Fr 1 p n).arrow = x ≫ sumInjection K q p n (by omega)) :
    a ≫ FilteredPage.toPage Fr 1 p n (D.containment 1 p n) ≫
        (rowFirstIsoAt K Fr hr D p q n h).hom =
      (K.flip.X p).liftCycles x (q+1) (by simp) hx ≫ (K.flip.X p).homologyπ q := by
  subst n
  simpa only [rowFirstIsoAt_self] using rowFirstIso_formula K Fr hr D p q x hx a ha

/-- The unsigned vertical image of a horizontal cycle remains a horizontal cycle. -/
theorem rowCycle_vertical (p q : ℤ) {T : A} (x : T ⟶ (K.X q).X p)
    (hx : x ≫ (K.d q (q+1)).f p = 0) :
    (x ≫ (K.X q).d p (p+1)) ≫ (K.d q (q+1)).f (p+1) = 0 := by
  rw [Category.assoc, ← (K.d q (q+1)).comm, ← Category.assoc, hx, zero_comp]

theorem rowFirstIso_d_at (D : F03Specs.PageData Fr) (p q : ℤ) :
    D.differential 1 (by omega) p (p+q) ≫
        (rowFirstIsoAt K Fr hr D (p+1) q (p+q+1) (by omega)).hom =
      (rowFirstIso K Fr hr D p q).hom ≫ ((ComplexShape.up ℤ).ε q •
        HomologicalComplex.homologyMap (K.flip.d p (p+1)) q) := by
  apply (cancel_epi (rowCyclesToPage K Fr hr D p q)).1
  let x := (K.flip.X p).iCycles q
  have hx : x ≫ (K.d q (q+1)).f p = 0 := (K.flip.X p).iCycles_d q (q+1)
  let a := rowAlmostCycle K Fr hr p q x hx
  let y := (ComplexShape.up ℤ).ε q • (x ≫ (K.X q).d p (p+1))
  have hy : y ≫ (K.d q (q+1)).f (p+1) = 0 := by
    dsimp only [y]
    rw [Linear.units_smul_comp, rowCycle_vertical K p q x hx, smul_zero]
  have ha : (a ≫ D.restriction 1 (by omega) p (p+q)) ≫
      (FilteredPage.almost Fr 1 (p+1) (p+q+1)).arrow =
        y ≫ sumInjection K q (p+1) (p+q+1) (by omega) := by
    rw [Category.assoc, D.restriction_arrow, ← Category.assoc,
      rowAlmostCycle_arrow, Category.assoc,
      rowCycle_total_d K p q (p+q) (p+q+1) rfl rfl x hx]
    dsimp only [y]
    rw [Linear.units_smul_comp, Category.assoc]
  change (a ≫ FilteredPage.toPage Fr 1 p (p+q) (D.containment 1 p (p+q))) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (FilteredPage.toPage _ _ _ _ _),
    D.representative_formula, Category.assoc, ← Category.assoc a,
    rowFirstIsoAt_formula K Fr hr D (p+1) q (p+q+1) (by omega) y hy _ ha]
  have hz : (K.flip.X (p+1)).liftCycles y (q+1) (by simp) hy =
      (ComplexShape.up ℤ).ε q • HomologicalComplex.cyclesMap (K.flip.d p (p+1)) q := by
    apply (cancel_mono ((K.flip.X (p+1)).iCycles q)).1
    rw [HomologicalComplex.liftCycles_i, Linear.units_smul_comp,
      HomologicalComplex.cyclesMap_i]
    rfl
  rw [hz, Linear.units_smul_comp]
  change _ = rowCyclesToPage K Fr hr D p q ≫ _
  rw [← Category.assoc, rowCyclesToPage_firstIso, Linear.comp_units_smul,
    HomologicalComplex.homologyπ_naturality]

theorem rowFirstIso_d (D : F03Specs.PageData Fr) (p q : ℤ) :
    firstDifferential Fr D p q ≫ (rowFirstIso K Fr hr D (p+1) q).hom =
      (rowFirstIso K Fr hr D p q).hom ≫ ((ComplexShape.up ℤ).ε q •
        HomologicalComplex.homologyMap (K.flip.d p (p+1)) q) := by
  convert rowFirstIso_d_at K Fr hr D p q using 1
  dsimp only [firstDifferential, rowFirstIsoAt, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc]

theorem rowFirstIsoAt_d (D : F03Specs.PageData Fr) (p q n : ℤ) (h : p+q=n) :
    D.differential 1 (by omega) p n ≫
        (rowFirstIsoAt K Fr hr D (p+1) q (n+1) (by omega)).hom =
      (rowFirstIsoAt K Fr hr D p q n h).hom ≫ ((ComplexShape.up ℤ).ε q •
        HomologicalComplex.homologyMap (K.flip.d p (p+1)) q) := by
  subst n
  simpa only [rowFirstIsoAt_self] using rowFirstIso_d_at K Fr hr D p q

private theorem rowSign_succ (p q : ℤ) :
    ((p+1)*q).negOnePow = (p*q).negOnePow * (ComplexShape.up ℤ).ε q := by
  change ((p+1)*q).negOnePow = (p*q).negOnePow * q.negOnePow
  rw [add_mul, one_mul, Int.negOnePow_add]

private theorem rowFirstIsoAt_signed_d (D : F03Specs.PageData Fr) (p q n : ℤ)
    (h : p+q=n) :
    D.differential 1 (by omega) p n ≫
        (((p+1)*q).negOnePow • (rowFirstIsoAt K Fr hr D (p+1) q (n+1) (by omega)).hom) =
      ((p*q).negOnePow • (rowFirstIsoAt K Fr hr D p q n h).hom) ≫
        (verticalHomology K.flip q).d p (p+1) := by
  change _ = _ ≫ HomologicalComplex.homologyMap (K.flip.d p (p+1)) q
  rw [Linear.comp_units_smul, rowFirstIsoAt_d K Fr hr D p q n h, Linear.comp_units_smul,
    Linear.units_smul_comp, smul_smul, rowSign_succ, mul_assoc, Int.units_mul_self, mul_one]

/-- The signed row coordinates carry the raw first differential to the unsigned one. -/
theorem rowFirstIso_signed_d (D : F03Specs.PageData Fr) (p q : ℤ) :
    firstDifferential Fr D p q ≫ (((p+1)*q).negOnePow • (rowFirstIso K Fr hr D (p+1) q).hom) =
      ((p*q).negOnePow • (rowFirstIso K Fr hr D p q).hom) ≫
        (verticalHomology K.flip q).d p (p+1) := by
  simpa only [firstDifferential, rowFirstIsoAt, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.assoc, Linear.comp_units_smul] using
    rowFirstIsoAt_signed_d K Fr hr D p q (p+q) rfl

/-- The three row comparisons use the signed interchange at each filtration degree. -/
def rowFirstShortIso (D : F03Specs.PageData Fr) (p q : ℤ) :
    PageCohomology.shortComplex Fr D 1 (by omega) p (p+q) ≅
      (verticalHomology K.flip q).sc' p (p+1) (p+1+1) := by
  refine ShortComplex.isoMk
    ((p*q).negOnePow • rowFirstIsoAt K Fr hr D p q (p+q) rfl)
    (((p+1)*q).negOnePow • rowFirstIsoAt K Fr hr D (p+1) q (p+q+1) (by omega))
    (((p+1+1)*q).negOnePow • rowFirstIsoAt K Fr hr D (p+1+1) q (p+q+1+1) (by omega))
    (rowFirstIsoAt_signed_d K Fr hr D p q (p+q) rfl).symm
    (rowFirstIsoAt_signed_d K Fr hr D (p+1) q (p+q+1) (by omega)).symm

private theorem rowFirstShortIso_eq (D : F03Specs.PageData Fr) (p q : ℤ) :
    firstPageShortIso Fr D (verticalHomology K.flip q) q
      (fun s => (s*q).negOnePow • rowFirstIso K Fr hr D s q)
      (fun s => rowFirstIso_signed_d K Fr hr D s q) p =
    rowFirstShortIso K Fr hr D p q := by
  apply Iso.ext
  ext
  · exact congrArg (fun e => (p*q).negOnePow • e.hom)
      (rowFirstIsoAt_self K Fr hr D p q).symm
  · simp only [rowFirstShortIso, firstPageShortIso, rowFirstIsoAt, ShortComplex.isoMk_hom_τ₂,
      Preadditive.smul_iso_hom, Iso.trans_hom, eqToIso.hom, Linear.comp_units_smul]
  · simp only [rowFirstShortIso, firstPageShortIso, rowFirstIsoAt, ShortComplex.isoMk_hom_τ₃,
      Preadditive.smul_iso_hom, Iso.trans_hom, eqToIso.hom, Linear.comp_units_smul]

def rowSecondIso (D : F03Specs.PageData Fr) (p q : ℤ) :
    page Fr D 2 p q ≅ (verticalHomology K.flip q).homology p :=
  secondIsoOfShortIso Fr D (verticalHomology K.flip q) q
    (fun t => rowFirstShortIso K Fr hr D t q) p (p-1) (by omega)

def rowData (D : F03Specs.PageData Fr) : RowData K Fr hr D where
  gradedIso := rowGradedIso K Fr hr
  graded_inv _ _ := rfl
  graded_d := rowGradedIso_d K Fr hr
  zeroIso := rowZeroIso K Fr hr D
  zeroIso_eq _ _ := rfl
  zero_d := rowZeroIso_d K Fr hr D
  firstIso := rowFirstIso K Fr hr D
  first_formula := rowFirstIso_formula K Fr hr D
  first_d := rowFirstIso_d K Fr hr D
  signed_first_d := rowFirstIso_signed_d K Fr hr D
  secondIso := rowSecondIso K Fr hr D
  second_formula q := secondPageFormula_of_shortIso Fr D (verticalHomology K.flip q) q
    (fun p => (p*q).negOnePow • rowFirstIso K Fr hr D p q)
    (fun p => rowFirstIso_signed_d K Fr hr D p q)
    (fun p => rowFirstShortIso K Fr hr D p q) (fun p => rowFirstShortIso_eq K Fr hr D p q)


section RowNaturality
variable {L : Bicomplex A} [L.HasTotal (ComplexShape.up ℤ)]
    (Gr : Filtration (sumTotal L)) (hgr : HasFiltrationFormula L Prod.snd Gr)
    (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr) (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K,Fr⟩ ⟨sumTotal L,Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E)

include hg

/-- A map of double complexes preserves the distinguished filtration summand. -/
theorem rowSummandToStep_naturality (p q : ℤ) :
    summandToStep K Prod.snd Fr hr p q p (p+q) (by change q+p=p+q; omega) le_rfl ≫ g.component p (p+q) =
      (f.f q).f p ≫ summandToStep L Prod.snd Gr hgr p q p (p+q) (by change q+p=p+q; omega) le_rfl := by
  apply (cancel_mono (Gr.piece p (p+q)).arrow).1
  change (summandToStep K Prod.snd Fr hr p q p (p+q) (by change q+p=p+q; omega) le_rfl ≫
      g.component p (p+q)) ≫ (Gr.piece p (p+q)).arrow =
    ((f.f q).f p ≫ summandToStep L Prod.snd Gr hgr p q p (p+q) (by change q+p=p+q; omega) le_rfl) ≫
      (Gr.piece p (p+q)).arrow
  rw [Category.assoc, FilteredMap.component_arrow, ← Category.assoc, summandToStep_arrow,
    Category.assoc, summandToStep_arrow, hg]
  exact HomologicalComplex₂.ιTotal_map K L f (ComplexShape.up ℤ) q p (p+q) (by change q+p=p+q; omega)

/-- The associated-graded coordinate comparison is natural. -/
theorem rowGradedIso_naturality (p q : ℤ) :
    (g.gradedMap p).f (p+q) ≫ (rowGradedIso L Gr hgr p q).hom =
      (rowGradedIso K Fr hr p q).hom ≫ (f.f q).f p := by
  apply (cancel_epi (rowGradedIso K Fr hr p q).inv).1
  change rowGradedInclusion K Fr hr p q ≫ _ = _
  rw [← Category.assoc, Iso.inv_hom_id_assoc]
  unfold rowGradedInclusion
  have hproj : (Fr.projection p).f (p+q) ≫ (g.gradedMap p).f (p+q) =
      g.component p (p+q) ≫ (Gr.projection p).f (p+q) := by
    exact HomologicalComplex.congr_hom (g.projection_naturality p) (p+q)
  calc
    ((summandToStep K Prod.snd Fr hr p q p (p+q) (by change q+p=p+q; omega) le_rfl ≫ (Fr.projection p).f (p+q)) ≫
        (g.gradedMap p).f (p+q)) ≫ (rowGradedIso L Gr hgr p q).hom =
      summandToStep K Prod.snd Fr hr p q p (p+q) (by change q+p=p+q; omega) le_rfl ≫
        ((Fr.projection p).f (p+q) ≫ (g.gradedMap p).f (p+q)) ≫
          (rowGradedIso L Gr hgr p q).hom := by simp only [Category.assoc]
    _ = (summandToStep K Prod.snd Fr hr p q p (p+q) (by change q+p=p+q; omega) le_rfl ≫ g.component p (p+q)) ≫
        (Gr.projection p).f (p+q) ≫ (rowGradedIso L Gr hgr p q).hom := by
      rw [hproj]; simp only [Category.assoc]
    _ = ((f.f q).f p ≫ summandToStep L Prod.snd Gr hgr p q p (p+q) (by change q+p=p+q; omega) le_rfl) ≫
        (Gr.projection p).f (p+q) ≫ (rowGradedIso L Gr hgr p q).hom := by
      rw [rowSummandToStep_naturality K Fr hr Gr hgr f g hg]
    _ = (f.f q).f p := by
      simpa only [rowGradedIso, rowGradedInclusion, Category.assoc, Category.comp_id]
        using congrArg (fun z => (f.f q).f p ≫ z)
          (rowGradedInclusion_projection L Gr hgr p q)

/-- Naturality of the row zeroth page. -/
theorem rowZeroIso_naturality (p q : ℤ) :
    M.map 0 p (p+q) ≫ (rowZeroIso L Gr hgr E p q).hom =
      (rowZeroIso K Fr hr D p q).hom ≫ (f.f q).f p := by
  dsimp only [rowZeroIso, Iso.trans_hom]
  rw [← Category.assoc, zeroPageIso_naturality g D E M, Category.assoc,
    rowGradedIso_naturality K Fr hr Gr hgr f g hg, ← Category.assoc]

/-- Naturality of the row first page, tested on its epic pure-cycle classes. -/
theorem rowFirstIso_naturality (p q : ℤ) :
    M.map 1 p (p+q) ≫ (rowFirstIso L Gr hgr E p q).hom =
      (rowFirstIso K Fr hr D p q).hom ≫ HomologicalComplex.homologyMap (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f p) q := by
  apply (cancel_epi (rowCyclesToPage K Fr hr D p q)).1
  let x := (K.flip.X p).iCycles q
  have hx : x ≫ (K.flip.X p).d q (q+1) = 0 := (K.flip.X p).iCycles_d q (q+1)
  let a := rowAlmostCycle K Fr hr p q x hx
  have hy : (x ≫ (f.f q).f p) ≫ (L.flip.X p).d q (q+1) = 0 := by
    have hw : (f.f q).f p ≫ (L.d q (q+1)).f p =
        (K.d q (q+1)).f p ≫ (f.f (q+1)).f p :=
      HomologicalComplex.congr_hom (f.comm q (q+1)) p
    dsimp only [HomologicalComplex₂.flip_X_X, HomologicalComplex₂.flip_X_d] at x hx ⊢
    rw [Category.assoc, hw, ← Category.assoc, hx, zero_comp]
  have ha : (a ≫ FilteredPageFunctoriality.almostMap g 1 p (p+q)) ≫
      (FilteredPage.almost Gr 1 p (p+q)).arrow =
        (x ≫ (f.f q).f p) ≫ sumInjection L q p (p+q) (by change q+p=p+q; omega) := by
    rw [Category.assoc, FilteredPageFunctoriality.almostMap_arrow, ← Category.assoc,
      rowAlmostCycle_arrow, Category.assoc, hg]
    simpa only [sumInjection, Category.assoc] using
      congrArg (fun z => x ≫ z) (HomologicalComplex₂.ιTotal_map K L f _ q p (p+q) (by change q+p=p+q; omega))
  change (a ≫ FilteredPage.toPage Fr 1 p (p+q) (D.containment 1 p (p+q))) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (FilteredPage.toPage _ _ _ _ _),
    M.representative_formula, Category.assoc, ← Category.assoc a,
    rowFirstIso_formula L Gr hgr E p q (x ≫ (f.f q).f p) hy _ ha,
    ← Category.assoc, rowCyclesToPage_firstIso, HomologicalComplex.homologyπ_naturality]
  congr 1
/-- First-page naturality with total degree specified independently. -/
theorem rowFirstIsoAt_naturality (p q n : ℤ) (h : p+q=n) :
    M.map 1 p n ≫ (rowFirstIsoAt L Gr hgr E p q n h).hom =
      (rowFirstIsoAt K Fr hr D p q n h).hom ≫ HomologicalComplex.homologyMap (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f p) q := by
  subst n
  simpa only [rowFirstIsoAt_self] using
    rowFirstIso_naturality K Fr hr Gr hgr D E f g hg M p q

/-- The three-term comparison on the first row page is natural. -/
theorem rowFirstShortIso_naturality (p q : ℤ) :
    FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q) ≫
        (rowFirstShortIso L Gr hgr E p q).hom =
      (rowFirstShortIso K Fr hr D p q).hom ≫
        (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) p (p+1) (p+1+1)).map
          (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) := by
  ext
  · change M.map 1 p (p+q) ≫ ((p*q).negOnePow •
        (rowFirstIsoAt L Gr hgr E p q (p+q) rfl).hom) =
      ((p*q).negOnePow • (rowFirstIsoAt K Fr hr D p q (p+q) rfl).hom) ≫
        HomologicalComplex.homologyMap (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f p) q
    simpa only [Linear.comp_units_smul, Linear.units_smul_comp] using
      congrArg (fun t => (p*q).negOnePow • t)
        (rowFirstIsoAt_naturality K Fr hr Gr hgr D E f g hg M p q (p+q) rfl)
  · change M.map 1 (p+1) (p+q+1) ≫ (((p+1)*q).negOnePow •
        (rowFirstIsoAt L Gr hgr E (p+1) q (p+q+1) (by omega)).hom) =
      (((p+1)*q).negOnePow • (rowFirstIsoAt K Fr hr D (p+1) q (p+q+1) (by omega)).hom) ≫
        HomologicalComplex.homologyMap (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f (p+1)) q
    simpa only [Linear.comp_units_smul, Linear.units_smul_comp] using
      congrArg (fun t => ((p+1)*q).negOnePow • t)
        (rowFirstIsoAt_naturality K Fr hr Gr hgr D E f g hg M
          (p+1) q (p+q+1) (by omega))
  · change M.map 1 (p+1+1) (p+q+1+1) ≫ (((p+1+1)*q).negOnePow •
        (rowFirstIsoAt L Gr hgr E (p+1+1) q (p+q+1+1) (by omega)).hom) =
      (((p+1+1)*q).negOnePow • (rowFirstIsoAt K Fr hr D (p+1+1) q (p+q+1+1) (by omega)).hom) ≫
        HomologicalComplex.homologyMap (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f (p+1+1)) q
    simpa only [Linear.comp_units_smul, Linear.units_smul_comp] using
      congrArg (fun t => ((p+1+1)*q).negOnePow • t)
        (rowFirstIsoAt_naturality K Fr hr Gr hgr D E f g hg M
          (p+1+1) q (p+q+1+1) (by omega))

/-- Naturality after identifying the three-term model with the standard short complex. -/
theorem rowFirstCohomologyShortIso_naturality (p q : ℤ) :
    FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q) ≫
        (rowFirstShortIso L Gr hgr E p q ≪≫
          ((verticalHomology L.flip q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm).hom =
      (rowFirstShortIso K Fr hr D p q ≪≫
          ((verticalHomology K.flip q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm).hom ≫
        (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) (p+1)).map
          (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, rowFirstShortIso_naturality K Fr hr Gr hgr D E f g hg M,
    Category.assoc]
  have h := (HomologicalComplex.natIsoSc' A (ComplexShape.up ℤ) p (p+1) (p+1+1)
    (by simp) (by simp)).inv.naturality (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q)
  simpa only [HomologicalComplex.isoSc', Iso.app_inv, Category.assoc, HomologicalComplex₂.flipFunctor_obj] using
    congrArg (fun t => (rowFirstShortIso K Fr hr D p q).hom ≫ t) h

/-- Naturality of the homology induced by the first-page three-term comparison. -/
theorem rowFirstShortHomologyIso_naturality (p q : ℤ) :
    ShortComplex.homologyMap (FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q)) ≫
        (ShortComplex.homologyMapIso (rowFirstShortIso L Gr hgr E p q ≪≫
          ((verticalHomology L.flip q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom =
      (ShortComplex.homologyMapIso (rowFirstShortIso K Fr hr D p q ≪≫
          ((verticalHomology K.flip q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) (p+1) := by
  have h := congrArg (fun t => ShortComplex.homologyMap t)
    (rowFirstCohomologyShortIso_naturality K Fr hr Gr hgr D E f g hg M p q)
  simpa only [ShortComplex.homologyMap_comp, ShortComplex.homologyMapIso_hom, HomologicalComplex.homologyMap] using h

/-- The second-page comparison before reindexing its center is natural. -/
theorem rowSecondCoreIso_naturality (p q : ℤ) :
    M.map 2 (p+1) (p+q+1) ≫
        ((PageCohomology.nextIso Gr E 1 (by omega) p (p+q)).hom ≫
          (ShortComplex.homologyMapIso (rowFirstShortIso L Gr hgr E p q ≪≫
            ((verticalHomology L.flip q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom) =
      ((PageCohomology.nextIso Fr D 1 (by omega) p (p+q)).hom ≫
          (ShortComplex.homologyMapIso (rowFirstShortIso K Fr hr D p q ≪≫
            ((verticalHomology K.flip q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom) ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) (p+1) := by
  have hnext := FilteredPageFunctoriality.next_naturality M
    (PageCohomology.data Fr D) (PageCohomology.data Gr E) 1 (by omega) p (p+q)
  change M.map 2 (p+1) (p+q+1) ≫ (PageCohomology.nextIso Gr E 1 (by omega) p (p+q)).hom =
    (PageCohomology.nextIso Fr D 1 (by omega) p (p+q)).hom ≫
      ShortComplex.homologyMap (FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q)) at hnext
  rw [← Category.assoc, hnext, Category.assoc,
    rowFirstShortHomologyIso_naturality K Fr hr Gr hgr D E f g hg M, ← Category.assoc]

/-- Naturality commutes with equalities of filtration and total degree. -/
theorem rowPageMap_transport (r p p' n n' : ℤ) (hp : p=p') (hn : n=n') :
    M.map r p n ≫ eqToHom (congrArg₂ (PageCohomology.object Gr E r) hp hn) =
      eqToHom (congrArg₂ (PageCohomology.object Fr D r) hp hn) ≫ M.map r p' n' := by
  subst p' n'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The map on iterated homology commutes with an equality of its degree. -/
theorem rowVerticalHomologyMap_transport (q p p' : ℤ) (hp : p=p') :
    HomologicalComplex.homologyMap (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) p ≫
        eqToHom (congrArg (fun t => (verticalHomology L.flip q).homology t) hp) =
      eqToHom (congrArg (fun t => (verticalHomology K.flip q).homology t) hp) ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) p' := by
  subst p'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Naturality of the row second page. -/
theorem rowSecondIso_naturality (p q : ℤ) :
    M.map 2 p (p+q) ≫ (rowSecondIso L Gr hgr E p q).hom =
      (rowSecondIso K Fr hr D p q).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyMap K.flip ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) q) p := by
  dsimp only [rowSecondIso, secondIsoOfShortIso, Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, rowPageMap_transport K Fr Gr D E f g hg M 2 p (p-1+1) (p+q) (p-1+q+1)
      (by omega) (by omega), Category.assoc]
  rw [← Category.assoc _ _ (eqToHom _)]
  rw [← Category.assoc (M.map 2 (p-1+1) (p-1+q+1)) _ (eqToHom _),
    rowSecondCoreIso_naturality K Fr hr Gr hgr D E f g hg M (p-1) q]
  rw [Category.assoc, rowVerticalHomologyMap_transport K Fr Gr f g hg q (p-1+1) p (by omega)]
  simp only [Category.assoc]


end RowNaturality

section Interchange
set_option maxHeartbeats 1200000

private theorem firstPageShortIso_naturality_of_coordinates
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : Bicomplex A}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    {F : Filtration (sumTotal K)} {G : Filtration (sumTotal L)}
    {D : F03Specs.PageData F} {E : F03Specs.PageData G}
    {f : FilteredMap ⟨sumTotal K, F⟩ ⟨sumTotal L, G⟩}
    (M : FilteredPageFunctoriality.MapData f D E)
    (T : CochainComplex A ℤ) (q : ℤ)
    (a : ∀ p, page F D 1 p q ≅ T.X p) (b : ∀ p, page G E 1 p q ≅ T.X p)
    (ha : ∀ p, firstDifferential F D p q ≫ (a (p+1)).hom =
      (a p).hom ≫ T.d p (p+1))
    (hb : ∀ p, firstDifferential G E p q ≫ (b (p+1)).hom =
      (b p).hom ≫ T.d p (p+1))
    (h : ∀ p, M.map 1 p (p+q) ≫ (b p).hom = (a p).hom) (p : ℤ) :
    FilteredPageFunctoriality.shortComplexMap M 1 (by omega) p (p+q) ≫
      (firstPageShortIso G E T q b hb p).hom =
        (firstPageShortIso F D T q a ha p).hom := by
  have transport (s n n' : ℤ) (eq : n = n') :
      M.map 1 s n ≫ eqToHom (congrArg (PageCohomology.object G E 1 s) eq) =
        eqToHom (congrArg (PageCohomology.object F D 1 s) eq) ≫ M.map 1 s n' := by
    subst n'
    simp
  ext
  · exact h p
  · change M.map 1 (p+1) (p+q+1) ≫
          (eqToHom (congrArg (PageCohomology.object G E 1 (p+1))
            (show p+q+1 = (p+1)+q by omega)) ≫ (b (p+1)).hom) =
        eqToHom (congrArg (PageCohomology.object F D 1 (p+1))
          (show p+q+1 = (p+1)+q by omega)) ≫ (a (p+1)).hom
    rw [← Category.assoc, transport _ _ _ (by omega), Category.assoc, h]
  · change M.map 1 (p+1+1) (p+q+1+1) ≫
          (eqToHom (congrArg (PageCohomology.object G E 1 (p+1+1))
            (show p+q+1+1 = (p+1+1)+q by omega)) ≫ (b (p+1+1)).hom) =
        eqToHom (congrArg (PageCohomology.object F D 1 (p+1+1))
          (show p+q+1+1 = (p+1+1)+q by omega)) ≫ (a (p+1+1)).hom
    rw [← Category.assoc, transport _ _ _ (by omega), Category.assoc, h]

/-- Compatibility with first-page coordinates gives compatibility with the
induced second-page comparison. -/
private theorem secondPageFormula_naturality_of_coordinates
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L : Bicomplex A}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    {F : Filtration (sumTotal K)} {G : Filtration (sumTotal L)}
    {D : F03Specs.PageData F} {E : F03Specs.PageData G}
    {f : FilteredMap ⟨sumTotal K, F⟩ ⟨sumTotal L, G⟩}
    (M : FilteredPageFunctoriality.MapData f D E)
    (T : CochainComplex A ℤ) (q : ℤ)
    (a : ∀ p, page F D 1 p q ≅ T.X p) (b : ∀ p, page G E 1 p q ≅ T.X p)
    (ha : ∀ p, firstDifferential F D p q ≫ (a (p+1)).hom =
      (a p).hom ≫ T.d p (p+1))
    (hb : ∀ p, firstDifferential G E p q ≫ (b (p+1)).hom =
      (b p).hom ≫ T.d p (p+1))
    (a₂ : ∀ p, page F D 2 p q ≅ T.homology p)
    (b₂ : ∀ p, page G E 2 p q ≅ T.homology p)
    (hA : SecondPageFormula F D T q a ha a₂) (hB : SecondPageFormula G E T q b hb b₂)
    (h : ∀ p, M.map 1 p (p+q) ≫ (b p).hom = (a p).hom) (p : ℤ) :
    M.map 2 p (p+q) ≫ (b₂ p).hom = (a₂ p).hom := by
  obtain ⟨R, hR⟩ := hA
  obtain ⟨C, hC⟩ := hB
  have aux (s : ℤ) :
      M.map 2 (s+1) ((s+1)+q) ≫ (b₂ (s+1)).hom = (a₂ (s+1)).hom := by
    have transport (n n' : ℤ) (eq : n = n') :
        M.map 2 (s+1) n ≫ eqToHom (congrArg (PageCohomology.object G E 2 (s+1)) eq) =
          eqToHom (congrArg (PageCohomology.object F D 2 (s+1)) eq) ≫ M.map 2 (s+1) n' := by
      subst n'
      simp
    have hn := FilteredPageFunctoriality.next_naturality M R C 1 (by omega) s (s+q)
    have hs := congrArg ShortComplex.homologyMap
      (firstPageShortIso_naturality_of_coordinates M T q a b ha hb h s)
    change M.map 2 (s+1) (s+q+1) ≫ (C.nextIso 1 (by omega) s (s+q)).hom =
      (R.nextIso 1 (by omega) s (s+q)).hom ≫
        ShortComplex.homologyMap (FilteredPageFunctoriality.shortComplexMap M 1 (by omega) s (s+q)) at hn
    simp only [← hR s, ← hC s, Iso.trans_hom, eqToIso.hom]
    rw [← Category.assoc (M.map 2 (s+1) ((s+1)+q)), transport _ _ (by omega), Category.assoc,
      ← Category.assoc (M.map 2 (s+1) (s+q+1)), hn]
    simp only [Category.assoc, ShortComplex.homologyMapIso_hom]
    rw [← Category.assoc (ShortComplex.homologyMap
      (FilteredPageFunctoriality.shortComplexMap M 1 (by omega) s (s+q))),
      ← ShortComplex.homologyMap_comp, hs]
  have e : p-1+1 = p := by omega
  exact (congrArg (fun t => M.map 2 t (t+q) ≫ (b₂ t).hom = (a₂ t).hom) e).mp (aux (p-1))

variable [K.flip.HasTotal (ComplexShape.up ℤ)]
variable (Fr : Filtration (sumTotal K)) (G : Filtration (sumTotal K.flip))
variable (hr : HasFiltrationFormula K Prod.snd Fr)
variable (hg : HasFiltrationFormula K.flip Prod.fst G)

/-- The signed total interchange respects the row and transposed-column filtrations. -/
def interchangeForward : FilteredMap ⟨sumTotal K, Fr⟩ ⟨sumTotal K.flip, G⟩ where
  hom := (K.totalFlipIso (ComplexShape.up ℤ)).inv
  preserves a n := by
    refine ⟨stepDesc K Prod.snd Fr hr a n (fun p q hpq ha =>
      (p*q).negOnePow • summandToStep K.flip Prod.fst G hg a q p n (by omega) ha), ?_⟩
    apply step_hom_ext K Prod.snd Fr hr
    intro p q hpq ha
    rw [← Category.assoc, summandToStep_stepDesc]
    simp only [Linear.units_smul_comp, summandToStep_arrow, summandToStep_arrow_assoc]
    exact (sumSymmetryFormula K p q n hpq).symm

/-- The inverse signed interchange is filtered as well. -/
def interchangeBackward : FilteredMap ⟨sumTotal K.flip, G⟩ ⟨sumTotal K, Fr⟩ where
  hom := (K.totalFlipIso (ComplexShape.up ℤ)).hom
  preserves a n := by
    refine ⟨stepDesc K.flip Prod.fst G hg a n (fun p q hpq ha =>
      (q*p).negOnePow • summandToStep K Prod.snd Fr hr a q p n (by omega) ha), ?_⟩
    apply step_hom_ext K.flip Prod.fst G hg
    intro p q hpq ha
    rw [← Category.assoc, summandToStep_stepDesc]
    simp only [Linear.units_smul_comp, summandToStep_arrow, summandToStep_arrow_assoc]
    exact (HomologicalComplex₂.ιTotal_totalFlipIso_f_hom K (ComplexShape.up ℤ) q p n hpq).symm

variable (Dr : F03Specs.PageData Fr) (Dt : F03Specs.PageData G)

/-- The signed interchange gives isomorphisms on all actual filtered pages. -/
def interchangePageIso (r p n : ℤ) :
    PageCohomology.object Fr Dr r p n ≅ PageCohomology.object G Dt r p n where
  hom := FilteredPageFunctoriality.pageMap (interchangeForward K Fr G hr hg) Dr Dt r p n
  inv := FilteredPageFunctoriality.pageMap (interchangeBackward K Fr G hr hg) Dt Dr r p n
  hom_inv_id := by
    apply (cancel_epi (FilteredPage.toPage Fr r p n (Dr.containment r p n))).1
    rw [← Category.assoc, FilteredPageFunctoriality.toPage_pageMap (interchangeForward K Fr G hr hg) Dr Dt, Category.assoc,
      FilteredPageFunctoriality.toPage_pageMap (interchangeBackward K Fr G hr hg) Dt Dr]
    have h : FilteredPageFunctoriality.almostMap (interchangeForward K Fr G hr hg) r p n ≫
        FilteredPageFunctoriality.almostMap (interchangeBackward K Fr G hr hg) r p n = 𝟙 _ := by
      apply (cancel_mono (FilteredPage.almost Fr r p n).arrow).1
      rw [Category.assoc,
        FilteredPageFunctoriality.almostMap_arrow (interchangeBackward K Fr G hr hg),
        ← Category.assoc, FilteredPageFunctoriality.almostMap_arrow (interchangeForward K Fr G hr hg)]
      change ((FilteredPage.almost Fr r p n).arrow ≫
        (K.totalFlipIso (ComplexShape.up ℤ)).inv.f n) ≫
        (K.totalFlipIso (ComplexShape.up ℤ)).hom.f n = _
      simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
        HomologicalComplex.id_f, Category.comp_id, Category.id_comp]
    rw [← Category.assoc, h, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (FilteredPage.toPage G r p n (Dt.containment r p n))).1
    rw [← Category.assoc, FilteredPageFunctoriality.toPage_pageMap (interchangeBackward K Fr G hr hg) Dt Dr, Category.assoc,
      FilteredPageFunctoriality.toPage_pageMap (interchangeForward K Fr G hr hg) Dr Dt]
    have h : FilteredPageFunctoriality.almostMap (interchangeBackward K Fr G hr hg) r p n ≫
        FilteredPageFunctoriality.almostMap (interchangeForward K Fr G hr hg) r p n = 𝟙 _ := by
      apply (cancel_mono (FilteredPage.almost G r p n).arrow).1
      rw [Category.assoc,
        FilteredPageFunctoriality.almostMap_arrow (interchangeForward K Fr G hr hg),
        ← Category.assoc, FilteredPageFunctoriality.almostMap_arrow (interchangeBackward K Fr G hr hg)]
      change ((FilteredPage.almost G r p n).arrow ≫
        (K.totalFlipIso (ComplexShape.up ℤ)).hom.f n) ≫
        (K.totalFlipIso (ComplexShape.up ℤ)).inv.f n = _
      simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
        HomologicalComplex.id_f, Category.comp_id, Category.id_comp]
    rw [← Category.assoc, h, Category.id_comp, Category.comp_id]

/-- All-page interchange, fixed on generalized representatives. -/
def interchangeData : InterchangeData K Fr G Dr Dt where
  forward := interchangeForward K Fr G hr hg
  backward := interchangeBackward K Fr G hr hg
  forward_hom := rfl
  backward_hom := rfl
  pageIso := interchangePageIso K Fr G hr hg Dr Dt
  representative_formula := FilteredPageFunctoriality.toPage_pageMap (interchangeForward K Fr G hr hg) Dr Dt
  differential_comm := FilteredPageFunctoriality.pageMap_differential (interchangeForward K Fr G hr hg) Dr Dt

/-- The signed interchange on `E₁` has multiplier `(-1)^(pq)` under
any raw-row identification that preserves pure cycle classes. -/
theorem interchange_firstIso (R : RowData K Fr hr Dr) (p q : ℤ) :
    (interchangePageIso K Fr G hr hg Dr Dt 1 p (p+q)).hom ≫
        (columnFirstIso K.flip G hg Dt p q).hom =
      (p*q).negOnePow • (R.firstIso p q).hom := by
  let e := interchangePageIso K Fr G hr hg Dr Dt 1 p (p+q)
  let x := (K.flip.X p).iCycles q
  have hx : x ≫ (K.flip.X p).d q (q+1) = 0 := (K.flip.X p).iCycles_d q (q+1)
  let a := columnAlmostCycle K.flip G hg p q x hx
  have hsx : ((p*q).negOnePow • x) ≫ (K.d q (q+1)).f p = 0 := by
    change ((p*q).negOnePow • x) ≫ (K.flip.X p).d q (q+1) = 0
    rw [Linear.units_smul_comp, hx, smul_zero]
  have ha : (a ≫ FilteredPageFunctoriality.almostMap
      (interchangeBackward K Fr G hr hg) 1 p (p+q)) ≫
        (FilteredPage.almost Fr 1 p (p+q)).arrow =
      ((p*q).negOnePow • x) ≫ sumInjection K q p (p+q) (by omega) := by
    rw [Category.assoc, FilteredPageFunctoriality.almostMap_arrow
      (interchangeBackward K Fr G hr hg), ← Category.assoc,
      columnAlmostCycle_arrow]
    change (x ≫ sumInjection K.flip p q (p+q) rfl) ≫
      (K.totalFlipIso (ComplexShape.up ℤ)).hom.f (p+q) = _
    rw [Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom K
      (ComplexShape.up ℤ) q p (p+q) rfl]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp]
    change (q*p).negOnePow • (x ≫ sumInjection K q p (p+q) (by omega)) =
      (p*q).negOnePow • (x ≫ sumInjection K q p (p+q) (by omega))
    rw [mul_comm q p]
  have hcyc : (K.flip.X p).liftCycles ((p*q).negOnePow • x) (q+1) (by simp) hsx =
      (p*q).negOnePow • 𝟙 _ := by
    apply (cancel_mono ((K.flip.X p).iCycles q)).1
    rw [HomologicalComplex.liftCycles_i, Linear.units_smul_comp, Category.id_comp]
  have hb : columnCyclesToPage K.flip G hg Dt p q ≫ e.inv ≫ (R.firstIso p q).hom =
      (p*q).negOnePow • (K.flip.X p).homologyπ q := by
    change (a ≫ FilteredPage.toPage G 1 p (p+q) (Dt.containment 1 p (p+q))) ≫
      FilteredPageFunctoriality.pageMap (interchangeBackward K Fr G hr hg) Dt Dr 1 p (p+q) ≫
      (R.firstIso p q).hom = _
    rw [Category.assoc, ← Category.assoc (FilteredPage.toPage G 1 p (p+q) _),
      FilteredPageFunctoriality.toPage_pageMap (interchangeBackward K Fr G hr hg) Dt Dr,
      Category.assoc, ← Category.assoc a,
      R.first_formula p q ((p*q).negOnePow • x) hsx _ ha,
      hcyc, Linear.units_smul_comp, Category.id_comp]
  apply (cancel_epi (columnCyclesToPage K.flip G hg Dt p q ≫ e.inv)).1
  change (columnCyclesToPage K.flip G hg Dt p q ≫ e.inv) ≫
    (e.hom ≫ (columnFirstIso K.flip G hg Dt p q).hom) = _
  rw [Category.assoc, e.inv_hom_id_assoc, columnCyclesToPage_firstIso,
    Linear.comp_units_smul, Category.assoc, hb,
    smul_smul, Int.units_mul_self, one_smul]

end Interchange


section InterchangeNaturality
set_option maxHeartbeats 1200000

/-- A commuting square of filtered cochain maps commutes on every page,
for every choice of its representative-compatible map data. -/
theorem pageMap_square {X Y X' Y' : FilteredComplex A}
    (f : FilteredMap X Y) (g : FilteredMap X' Y')
    (u : FilteredMap X X') (v : FilteredMap Y Y')
    (h : f.hom ≫ v.hom = u.hom ≫ g.hom)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (D' : F03Specs.PageData X'.filtration) (E' : F03Specs.PageData Y'.filtration)
    (M : FilteredPageFunctoriality.MapData f D E)
    (N : FilteredPageFunctoriality.MapData g D' E') (r p n : ℤ) :
    M.map r p n ≫ FilteredPageFunctoriality.pageMap v E E' r p n =
      FilteredPageFunctoriality.pageMap u D D' r p n ≫ N.map r p n := by
  have hmaps : FilteredPageFunctoriality.almostMap f r p n ≫
      FilteredPageFunctoriality.almostMap v r p n =
    FilteredPageFunctoriality.almostMap u r p n ≫
      FilteredPageFunctoriality.almostMap g r p n := by
    apply (cancel_mono (FilteredPage.almost Y'.filtration r p n).arrow).1
    simp only [Category.assoc, FilteredPageFunctoriality.almostMap_arrow v r p n,
      FilteredPageFunctoriality.almostMap_arrow_assoc f r p n,
      FilteredPageFunctoriality.almostMap_arrow g r p n,
      FilteredPageFunctoriality.almostMap_arrow_assoc u r p n]
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun z => (FilteredPage.almost X.filtration r p n).arrow ≫ z.f n) h
  apply (cancel_epi (FilteredPage.toPage X.filtration r p n (D.containment r p n))).1
  calc
    _ = FilteredPageFunctoriality.almostMap f r p n ≫
        FilteredPageFunctoriality.almostMap v r p n ≫
        FilteredPage.toPage Y'.filtration r p n (E'.containment r p n) := by
      rw [← Category.assoc, M.representative_formula, Category.assoc,
        FilteredPageFunctoriality.toPage_pageMap v E E']
    _ = FilteredPageFunctoriality.almostMap u r p n ≫
        FilteredPageFunctoriality.almostMap g r p n ≫
        FilteredPage.toPage Y'.filtration r p n (E'.containment r p n) := by
      rw [← Category.assoc, hmaps, Category.assoc]
    _ = _ := by
      symm
      rw [← Category.assoc, FilteredPageFunctoriality.toPage_pageMap u D D',
        Category.assoc, N.representative_formula]

variable {K} (L : Bicomplex A) [L.HasTotal (ComplexShape.up ℤ)]
  [K.flip.HasTotal (ComplexShape.up ℤ)] [L.flip.HasTotal (ComplexShape.up ℤ)]
variable (Fr : Filtration (sumTotal K)) (G : Filtration (sumTotal K.flip))
  (Fr' : Filtration (sumTotal L)) (G' : Filtration (sumTotal L.flip))
  (hr : HasFiltrationFormula K Prod.snd Fr) (hg : HasFiltrationFormula K.flip Prod.fst G)
  (hr' : HasFiltrationFormula L Prod.snd Fr') (hg' : HasFiltrationFormula L.flip Prod.fst G')
  (Dr : F03Specs.PageData Fr) (Dt : F03Specs.PageData G)
  (Dr' : F03Specs.PageData Fr') (Dt' : F03Specs.PageData G')

/-- Signed interchange is natural on every page. -/
theorem interchangePageIso_naturality
    (f : K ⟶ L)
    (g : FilteredMap ⟨sumTotal K, Fr⟩ ⟨sumTotal L, Fr'⟩)
    (h : FilteredMap ⟨sumTotal K.flip, G⟩ ⟨sumTotal L.flip, G'⟩)
    (hgf : g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))
    (hhf : h.hom = HomologicalComplex₂.total.map
      (show K.flip ⟶ L.flip from
        (HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f)
        (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData g Dr Dr')
    (N : FilteredPageFunctoriality.MapData h Dt Dt') (r p n : ℤ) :
    M.map r p n ≫ (interchangePageIso L Fr' G' hr' hg' Dr' Dt' r p n).hom =
      (interchangePageIso K Fr G hr hg Dr Dt r p n).hom ≫ N.map r p n := by
  apply pageMap_square g h (interchangeForward K Fr G hr hg)
    (interchangeForward L Fr' G' hr' hg') _ Dr Dr' Dt Dt' M N r p n
  change g.hom ≫ (L.totalFlipIso (ComplexShape.up ℤ)).inv =
    (K.totalFlipIso (ComplexShape.up ℤ)).inv ≫ h.hom
  rw [hgf, hhf]
  exact sumNaturality K L f

end InterchangeNaturality


/-- The natural column and row page identifications and their signed interchange. -/
def system (A : Type u) [Category.{v} A] [Abelian A] : System A where
  column := by
    intro K hK inst F hF D
    exact columnData K F hF D
  row := by
    intro K hK inst F hF D
    exact rowData K F hF D
  column_naturality := by
    intro K L hK hL instK instL F G hF hG D E f g hg M p q
    exact ⟨columnZeroIso_naturality K F hF G hG D E f g hg M p q,
      columnFirstIso_naturality K F hF G hG D E f g hg M p q,
      columnSecondIso_naturality K F hF G hG D E f g hg M p q⟩
  row_naturality := by
    intro K L hK hL instK instL F G hF hG D E f g hg M p q
    exact ⟨rowZeroIso_naturality K F hF G hG D E f g hg M p q,
      rowFirstIso_naturality K F hF G hG D E f g hg M p q,
      rowSecondIso_naturality K F hF G hG D E f g hg M p q⟩
  interchange := by
    intro K hK instK instKt hKt Fr G hr hg Dr Dt
    let R := rowData K Fr hr Dr
    let C := columnData K.flip G hg Dt
    let M := FilteredPageFunctoriality.mapData (interchangeForward K Fr G hr hg) Dr Dt
    refine ⟨interchangeData K Fr G hr hg Dr Dt, fun p q => ⟨?_, ?_⟩⟩
    · exact interchange_firstIso K Fr G hr hg Dr Dt R p q
    · exact secondPageFormula_naturality_of_coordinates M (verticalHomology K.flip q) q
        (fun s => (s*q).negOnePow • R.firstIso s q) (fun s => C.firstIso s q)
        (fun s => R.signed_first_d s q) (fun s => C.first_d s q)
        (fun s => R.secondIso s q) (fun s => C.secondIso s q)
        (R.second_formula q) (C.second_formula q)
        (fun s => interchange_firstIso K Fr G hr hg Dr Dt R s q) p

/-- HA-B03: the first column and row pages, their signs, and naturality. -/
theorem double_complex_first_pages : Specs.FullStatement.{v,u} := by
  intro A _ _
  exact ⟨system A⟩

end AdvancedHomologicalAlgebra.DoubleComplexFirstPages
