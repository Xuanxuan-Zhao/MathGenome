import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FilteredPages
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiltrationExactSequences
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PageCohomology
import Mathlib.Algebra.Homology.Refinements

/-! HA-F04: comparison of the actual filtered pages with cohomology.
All representative arguments take place over test objects and epic covers. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra

/-- The zeroth page is the associated graded object, with its canonical
representative map, for every choice of HA-F03 page data. -/
theorem filtered_zero_page : F04Specs.ZeroPage.{v,u} := by
  intro A _ _ K F D
  exact ⟨{
    zeroIso := D.zeroPageIso
    zeroIso_formula := D.zeroPageIso_formula
    zero_differential := D.zero_differential }⟩

namespace PageCohomology
open FilteredPage
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

/-- A first-page almost cycle obtained from a representative and its
factored differential. No lift on the original test object is assumed. -/
def liftAlmostOne {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X n)
    (y : T ⟶ (F.step (p+1)).X (n+1))
    (hy : y ≫ (F.transition p).f (n+1) = x ≫ (F.step p).d n (n+1)) :
    T ⟶ (almost F 1 p n : A) :=
  (almost F 1 p n).factorThru (x ≫ (F.piece p n).arrow) (by
    apply (Subobject.inf_factors _).2
    refine ⟨Subobject.factors_comp_arrow x, ?_⟩
    apply pullback_factors
    apply (Subobject.factors_iff _ _).2
    refine ⟨y, ?_⟩
    calc
      y ≫ (F.piece (p+1) (n+1)).arrow =
          (y ≫ (F.transition p).f (n+1)) ≫ (F.piece p (n+1)).arrow := by
        simp [Filtration.transition, Category.assoc]
      _ = (x ≫ (F.step p).d n (n+1)) ≫ (F.piece p (n+1)).arrow := by rw [hy]
      _ = (x ≫ (F.piece p n).arrow) ≫ K.d n (n+1) := by
        simp [Filtration.step, Category.assoc])

@[reassoc (attr := simp)]
theorem liftAlmostOne_arrow {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X n)
    (y : T ⟶ (F.step (p+1)).X (n+1))
    (hy : y ≫ (F.transition p).f (n+1) = x ≫ (F.step p).d n (n+1)) :
    liftAlmostOne F p n x y hy ≫ (almost F 1 p n).arrow = x ≫ (F.piece p n).arrow :=
  Subobject.factorThru_arrow _ _ _

@[reassoc (attr := simp)]
theorem liftAlmostOne_graded {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X n)
    (y : T ⟶ (F.step (p+1)).X (n+1))
    (hy : y ≫ (F.transition p).f (n+1) = x ≫ (F.step p).d n (n+1)) :
    liftAlmostOne F p n x y hy ≫ gradedRepresentative F p n (almost F 1 p n) inf_le_left =
      x ≫ (F.projection p).f n := by
  dsimp only [gradedRepresentative]
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (F.piece p n).arrow).1
  simp [Category.assoc]

/-- The cycle subobject defining page one maps to the usual cycles. -/
def firstCyclesMap (p n : ℤ) : (cycles F 1 p n : A) ⟶ (F.graded p).cycles n :=
  (F.graded p).liftCycles (cycles F 1 p n).arrow (n+1) (by simp) (by
    apply (cancel_epi (factorThruImageSubobject
      (gradedRepresentative F p n (almost F 1 p n) inf_le_left))).1
    rw [← Category.assoc, imageSubobject_arrow_comp, comp_zero]
    exact firstRepresentative_cycle F p n)

@[reassoc (attr := simp)]
theorem firstCyclesMap_iCycles (p n : ℤ) :
    firstCyclesMap F p n ≫ (F.graded p).iCycles n = (cycles F 1 p n).arrow :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

@[reassoc (attr := simp)]
theorem toCycles_firstCyclesMap (p n : ℤ) :
    factorThruImageSubobject (gradedRepresentative F p n (almost F 1 p n) inf_le_left) ≫
      firstCyclesMap F p n =
    (F.graded p).liftCycles (gradedRepresentative F p n (almost F 1 p n) inf_le_left)
      (n+1) (by simp) (firstRepresentative_cycle F p n) := by
  apply (cancel_mono ((F.graded p).iCycles n)).1
  simp [Category.assoc]

instance firstCyclesMap_mono (p n : ℤ) : Mono (firstCyclesMap F p n) :=
  mono_of_mono_fac (firstCyclesMap_iCycles F p n)

instance firstCyclesMap_epi (p n : ℤ) : Epi (firstCyclesMap F p n) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T z
  obtain ⟨T', e, he, x, y, hx, hy⟩ := filtration_representative_lifts F p n
    (z ≫ (F.graded p).iCycles n) (by simp)
  refine ⟨T', e, he, liftAlmostOne F p n x y hy ≫ factorThruImageSubobject
    (gradedRepresentative F p n (almost F 1 p n) inf_le_left), ?_⟩
  apply (cancel_mono ((F.graded p).iCycles n)).1
  simp only [Category.assoc, firstCyclesMap_iCycles, imageSubobject_arrow_comp,
    liftAlmostOne_graded]
  exact hx.symm

/-- The defining first-page cycle subobject is exactly the usual cycles. -/
def firstCyclesIso (p n : ℤ) : (cycles F 1 p n : A) ≅ (F.graded p).cycles n :=
  have : IsIso (firstCyclesMap F p n) := isIso_of_mono_of_epi _
  asIso (firstCyclesMap F p n)

/-- Any boundary in the filtration step gives a boundary in the associated graded. -/
theorem boundaryClass_zero (p n : ℤ) :
    Subobject.ofLE _ _ (boundaries_le_cycles F 1 p n) ≫ firstCyclesMap F p n ≫
      (F.graded p).homologyπ n = 0 := by
  apply (cancel_epi (factorThruImageSubobject
    (gradedRepresentative F p n (boundarySource F 1 p n) inf_le_left))).1
  rw [comp_zero]
  have hb : boundarySource F 1 p n ≤
      imageSubobject ((F.piece p (n-1)).arrow ≫ K.d (n-1) n) := by
    change F.piece p n ⊓ imageSubobject ((F.piece (p-1+1) (n-1)).arrow ≫ K.d (n-1) n) ≤ _
    rw [show p-1+1=p by omega]
    exact inf_le_right
  let b := Subobject.ofLE _ _ hb
  obtain ⟨T, e, he, x, hx⟩ := surjective_up_to_refinements_of_epi
    (factorThruImageSubobject ((F.piece p (n-1)).arrow ≫ K.d (n-1) n)) b
  apply (cancel_epi e).1
  rw [comp_zero]
  have hx' : x ≫ (F.piece p (n-1)).arrow ≫ K.d (n-1) n =
      e ≫ (boundarySource F 1 p n).arrow := by
    have hh := hx =≫ (imageSubobject ((F.piece p (n-1)).arrow ≫ K.d (n-1) n)).arrow
    simpa [b, Category.assoc] using hh.symm
  let z := e ≫ gradedRepresentative F p n (boundarySource F 1 p n) inf_le_left
  have hz : z = (x ≫ (F.projection p).f (n-1)) ≫ (F.graded p).d (n-1) n := by
    calc
      z = (e ≫ Subobject.ofLE _ _ (inf_le_left : boundarySource F 1 p n ≤ F.piece p n)) ≫
          (F.projection p).f n := (Category.assoc _ _ _).symm
      _ = (x ≫ (F.step p).d (n-1) n) ≫ (F.projection p).f n := by
        apply congrArg (fun t : T ⟶ (F.step p).X n => t ≫ (F.projection p).f n)
        apply (cancel_mono (F.piece p n).arrow).1
        simpa only [Category.assoc, Subobject.ofLE_arrow, Filtration.step,
          Filtration.differential_arrow] using hx'.symm
      _ = (x ≫ (F.projection p).f (n-1)) ≫ (F.graded p).d (n-1) n := by
        rw [Category.assoc, ← (F.projection p).comm (n-1) n, ← Category.assoc]
  have hzcycle : z ≫ (F.graded p).d n (n+1) = 0 := by
    rw [hz, Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
  trans (F.graded p).liftCycles z (n+1) (by simp) hzcycle ≫ (F.graded p).homologyπ n
  · simp only [← Category.assoc]
    apply congrArg (fun t : T ⟶ (F.graded p).cycles n => t ≫ (F.graded p).homologyπ n)
    apply (cancel_mono ((F.graded p).iCycles n)).1
    simp [z, Category.assoc]
  · exact (F.graded p).liftCycles_homologyπ_eq_zero_of_boundary z (n+1) (by simp)
      (x ≫ (F.projection p).f (n-1)) hz

/-- The canonical first-page comparison, before proving it is an isomorphism. -/
def firstMap (p n : ℤ) (h : boundaries F 1 p n ≤ cycles F 1 p n) :
    page F 1 p n h ⟶ (F.graded p).homology n :=
  cokernel.desc _ (firstCyclesMap F p n ≫ (F.graded p).homologyπ n) (boundaryClass_zero F p n)

@[reassoc (attr := simp)]
theorem toPage_firstMap (p n : ℤ) (h : boundaries F 1 p n ≤ cycles F 1 p n) :
    toPage F 1 p n h ≫ firstMap F p n h = firstClass F p n := by
  dsimp only [toPage, firstMap, firstClass]
  rw [Category.assoc, cokernel.π_desc, ← Category.assoc, toCycles_firstCyclesMap]

instance firstMap_epi (p n : ℤ) (h : boundaries F 1 p n ≤ cycles F 1 p n) :
    Epi (firstMap F p n h) := by
  have hh : cokernel.π (Subobject.ofLE _ _ h) ≫ firstMap F p n h =
      firstCyclesMap F p n ≫ (F.graded p).homologyπ n := cokernel.π_desc _ _ _
  exact epi_of_epi_fac hh

/-- A differential from `F^p` is a first-page boundary, before projection. -/
def firstBoundary {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X (n-1)) :
    T ⟶ (boundarySource F 1 p n : A) :=
  (boundarySource F 1 p n).factorThru
    (x ≫ (F.piece p (n-1)).arrow ≫ K.d (n-1) n) (by
      apply (Subobject.inf_factors _).2
      constructor
      · apply (Subobject.factors_iff _ _).2
        exact ⟨x ≫ (F.step p).d (n-1) n, by simp [Category.assoc, Filtration.step]⟩
      · change (imageSubobject ((F.piece (p-1+1) (n-1)).arrow ≫ K.d (n-1) n)).Factors _
        rw [show p-1+1=p by omega]
        exact imageSubobject_factors_comp_self _ x)

@[reassoc (attr := simp)]
theorem firstBoundary_arrow {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X (n-1)) :
    firstBoundary F p n x ≫ (boundarySource F 1 p n).arrow =
      x ≫ (F.piece p (n-1)).arrow ≫ K.d (n-1) n :=
  Subobject.factorThru_arrow _ _ _

@[reassoc (attr := simp)]
theorem firstBoundary_graded {T : A} (p n : ℤ) (x : T ⟶ (F.step p).X (n-1)) :
    firstBoundary F p n x ≫ gradedRepresentative F p n (boundarySource F 1 p n) inf_le_left =
      x ≫ (F.projection p).f (n-1) ≫ (F.graded p).d (n-1) n := by
  dsimp only [gradedRepresentative]
  rw [(F.projection p).comm (n-1) n, ← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_mono (F.piece p n).arrow).1
  simp [Category.assoc, Filtration.step]

/-- Equal graded representatives have equal classes on the page. -/
theorem toPage_eq_of_graded_eq (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) {T : A}
    (x y : T ⟶ (almost F r p n : A))
    (hxy : x ≫ gradedRepresentative F p n (almost F r p n) inf_le_left =
      y ≫ gradedRepresentative F p n (almost F r p n) inf_le_left) :
    x ≫ toPage F r p n h = y ≫ toPage F r p n h := by
  have hh : x ≫ factorThruImageSubobject
      (gradedRepresentative F p n (almost F r p n) inf_le_left) =
      y ≫ factorThruImageSubobject
      (gradedRepresentative F p n (almost F r p n) inf_le_left) := by
    apply (cancel_mono (cycles F r p n).arrow).1
    simpa only [Category.assoc, imageSubobject_arrow_comp] using hxy
  simpa only [toPage, Category.assoc] using
    congrArg (fun z => z ≫ cokernel.π (Subobject.ofLE _ _ h)) hh

/-- Vanishing in graded cohomology implies vanishing on the first page.
Two epic refinements suffice: one for a graded boundary and one for its lift. -/
theorem toPage_zero_of_firstClass_zero (p n : ℤ)
    (h : boundaries F 1 p n ≤ cycles F 1 p n) {T : A}
    (x : T ⟶ (almost F 1 p n : A)) (hx : x ≫ firstClass F p n = 0) :
    x ≫ toPage F 1 p n h = 0 := by
  have hxcycle : (x ≫ gradedRepresentative F p n (almost F 1 p n) inf_le_left) ≫
      (F.graded p).d n (n+1) = 0 := by
    rw [Category.assoc, firstRepresentative_cycle, comp_zero]
  have hxclass : (F.graded p).liftCycles
      (x ≫ gradedRepresentative F p n (almost F 1 p n) inf_le_left)
      (n+1) (by simp) hxcycle ≫ (F.graded p).homologyπ n = 0 := by
    dsimp only [firstClass] at hx
    rw [HomologicalComplex.comp_liftCycles_assoc] at hx
    exact hx
  obtain ⟨T₁, e₁, he₁, y, hy⟩ :=
    ((F.graded p).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
      (n-1) n (n+1) (by simp) (by simp) _ hxcycle).1 hxclass
  obtain ⟨T₂, e₂, he₂, z, hz⟩ :=
    surjective_up_to_refinements_of_epi ((F.projection p).f (n-1)) y
  apply (cancel_epi (e₂ ≫ e₁)).1
  rw [comp_zero]
  let b := firstBoundary F p n z ≫ Subobject.ofLE _ _ (boundarySource_le_almost F 1 p n)
  trans b ≫ toPage F 1 p n h
  · have hh : ((e₂ ≫ e₁) ≫ x) ≫ gradedRepresentative F p n (almost F 1 p n) inf_le_left =
        b ≫ gradedRepresentative F p n (almost F 1 p n) inf_le_left := by
      dsimp only [b]
      rw [Category.assoc (firstBoundary F p n z), gradedRepresentative_naturality,
        firstBoundary_graded]
      rw [← Category.assoc z, ← hz]
      simp only [Category.assoc]
      rw [← hy]
    simpa only [Category.assoc] using toPage_eq_of_graded_eq F 1 p n h _ _ hh
  · apply toPage_zero_of_boundary
    simp only [b, Category.assoc, Subobject.ofLE_arrow]
    exact Subobject.factors_comp_arrow _

instance firstMap_mono (p n : ℤ) (h : boundaries F 1 p n ≤ cycles F 1 p n) :
    Mono (firstMap F p n h) := by
  apply Preadditive.mono_of_cancel_zero
  intro T z hz
  obtain ⟨T', e, he, x, hx⟩ := surjective_up_to_refinements_of_epi (toPage F 1 p n h) z
  apply (cancel_epi e).1
  rw [hx, comp_zero]
  apply toPage_zero_of_firstClass_zero
  rw [← toPage_firstMap F p n h, ← Category.assoc, ← hx, Category.assoc, hz, comp_zero]

/-- The canonical `E₁ ≅ H(gr)` identification. -/
def firstIso (p n : ℤ) (h : boundaries F 1 p n ≤ cycles F 1 p n) :
    page F 1 p n h ≅ (F.graded p).homology n :=
  have : IsIso (firstMap F p n h) := isIso_of_mono_of_epi _
  asIso (firstMap F p n h)

@[reassoc (attr := simp)]
theorem toPage_firstIso (p n : ℤ) (h : boundaries F 1 p n ≤ cycles F 1 p n) :
    toPage F 1 p n h ≫ (firstIso F p n h).hom = firstClass F p n :=
  toPage_firstMap F p n h

/-- The chosen differential of an almost 1-cycle factors through `F^(p+1)`. -/
theorem firstLift_transition (p n : ℤ) :
    firstLift F p n ≫ (F.transition p).f (n+1) =
      Subobject.ofLE _ _ (inf_le_left : almost F 1 p n ≤ F.piece p n) ≫
        (F.step p).d n (n+1) := by
  apply (cancel_mono (F.piece p (n+1)).arrow).1
  simp [Category.assoc, Filtration.transition, Filtration.step]

/-- With the first-page identification, the first differential is precisely
the connecting morphism of the second short exact filtration sequence. -/
theorem first_differential (D : F03Specs.PageData F) (p n : ℤ)
    (h : (F.secondSequence p).ShortExact) :
    D.differential 1 (by omega) p n ≫
        (firstIso F (p+1) (n+1) (D.containment 1 (p+1) (n+1))).hom =
      (firstIso F p n (D.containment 1 p n)).hom ≫ h.δ n (n+1) (by simp) := by
  apply (cancel_epi (toPage F 1 p n (D.containment 1 p n))).1
  rw [← Category.assoc, D.representative_formula, Category.assoc, toPage_firstIso,
    ← Category.assoc (toPage F 1 p n _) _ _, toPage_firstIso]
  let x := Subobject.ofLE _ _ (inf_le_left : almost F 1 p n ≤ F.piece p n)
  have hx : (x ≫ (F.projection p).f n) ≫ (F.graded p).d n (n+1) = 0 :=
    firstRepresentative_cycle F p n
  obtain ⟨hz, hh⟩ := filtration_connecting_formula F p n h x hx (firstLift F p n)
    (firstLift_transition F p n)
  have hw : D.restriction 1 (by omega) p n ≫
      gradedRepresentative F (p+1) (n+1) (almost F 1 (p+1) (n+1)) inf_le_left =
      firstLift F p n ≫ (F.projection (p+1)).f (n+1) := by
    dsimp only [gradedRepresentative]
    rw [← Category.assoc]
    apply congrArg (fun t : (almost F 1 p n : A) ⟶ (F.step (p+1)).X (n+1) =>
      t ≫ (F.projection (p+1)).f (n+1))
    apply (cancel_mono (F.piece (p+1) (n+1)).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, D.restriction_arrow, firstLift_arrow]
  dsimp only [firstClass]
  rw [HomologicalComplex.comp_liftCycles_assoc]
  simpa only [hw, Category.assoc, firstClass, gradedRepresentative, x] using hh.symm

/-- A page representative supported in the next filtration step is zero. -/
theorem toPage_zero_of_next (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) {T : A}
    (x : T ⟶ (almost F r p n : A))
    (hx : (F.piece (p+1) n).Factors (x ≫ (almost F r p n).arrow)) :
    x ≫ toPage F r p n h = 0 := by
  apply toPage_zero_of_graded_zero
  let y := (F.piece (p+1) n).factorThru _ hx
  have hw : x ≫ Subobject.ofLE _ _ (inf_le_left : almost F r p n ≤ F.piece p n) =
      y ≫ (F.transition p).f n := by
    apply (cancel_mono (F.piece p n).arrow).1
    simp [y, Category.assoc, Filtration.transition]
  dsimp only [gradedRepresentative, Filtration.projection]
  rw [← Category.assoc, hw, Category.assoc, cokernel.condition, comp_zero]

/-- Almost `(r+1)`-cycles give cycles for the `r`th page differential. -/
theorem next_cycle_at (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    nextRepresentative F D r p n ≫ D.differential r hr p n = 0 := by
  dsimp only [nextRepresentative]
  rw [Category.assoc, D.representative_formula, ← Category.assoc]
  apply toPage_zero_of_next
  rw [Category.assoc, D.restriction_arrow, ← Category.assoc, Subobject.ofLE_arrow]
  apply (pullback_factors_iff (K.d n (n+1)) (F.piece (p+r+1) (n+1))
    (almost F (r+1) p n).arrow).1
  apply Subobject.factors_of_le _ _ (Subobject.factors_self (almost F (r+1) p n))
  simpa only [add_assoc] using
    (inf_le_right : almost F (r+1) p n ≤
      (Subobject.pullback (K.d n (n+1))).obj (F.piece (p+(r+1)) (n+1)))


/-- The alternate quotient presentation detects precisely the denominator
relations, for morphisms from every test object. -/
theorem toPage_zero_iff_denominator (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) {T : A}
    (x : T ⟶ (almost F r p n : A)) :
    x ≫ toPage F r p n h = 0 ↔
      (denominator F r p n).Factors (x ≫ (almost F r p n).arrow) := by
  constructor
  · intro hx
    have hx' : x ≫ cokernel.π (Subobject.ofLE _ _ (denominator_le F r p n)) = 0 := by
      apply (cancel_mono (quotientIso F r p n h).hom).1
      simpa only [Category.assoc, toAlternate_quotientIso, zero_comp] using hx
    let y := Abelian.monoLift (Subobject.ofLE _ _ (denominator_le F r p n)) x hx'
    apply (Subobject.factors_iff _ _).2
    refine ⟨y, ?_⟩
    change y ≫ (denominator F r p n).arrow = _
    rw [← Subobject.ofLE_arrow (denominator_le F r p n), ← Category.assoc]
    rw [Abelian.monoLift_comp]
  · intro hx
    rw [← toAlternate_quotientIso F r p n h, ← Category.assoc,
      toAlternate_zero_of_factors F r p n x hx, zero_comp]

/-- Representatives in a sum of two subobjects can be decomposed over an
epic cover. This uses only a binary coproduct. -/
theorem decompose_sum {X T : A} (U V : Subobject X) (z : T ⟶ X)
    (hz : (U ⊔ V).Factors z) :
    ∃ (T' : A) (e : T' ⟶ T) (_ : Epi e) (u : T' ⟶ (U : A)) (v : T' ⟶ (V : A)),
      e ≫ z = u ≫ U.arrow + v ≫ V.arrow := by
  have : StrongEpi (Subobject.supMonoFactorisation U V).e :=
    strongEpi_of_strongEpiMonoFactorisation
      (Abelian.imageStrongEpiMonoFactorisation _) (Subobject.supIsImage U V)
  let t := (U ⊔ V).factorThru z hz
  obtain ⟨T', e, he, w, hw⟩ := surjective_up_to_refinements_of_epi
    (Subobject.supMonoFactorisation U V).e t
  refine ⟨T', e, he, w ≫ coprod.desc (𝟙 _) 0, w ≫ coprod.desc 0 (𝟙 _), ?_⟩
  have hh : coprod.desc U.arrow V.arrow =
      coprod.desc (𝟙 _) 0 ≫ U.arrow + coprod.desc 0 (𝟙 _) ≫ V.arrow := by
    apply coprod.hom_ext <;> simp [Preadditive.comp_add]
  calc
    e ≫ z = (e ≫ t) ≫ (U ⊔ V).arrow := by simp [t, Category.assoc]
    _ = (w ≫ (Subobject.supMonoFactorisation U V).e) ≫ (U ⊔ V).arrow := by rw [hw]
    _ = w ≫ coprod.desc U.arrow V.arrow := by
      rw [Category.assoc]
      change w ≫ ((Subobject.supMonoFactorisation U V).e ≫
        (Subobject.supMonoFactorisation U V).m) = _
      rw [(Subobject.supMonoFactorisation U V).fac]
    _ = _ := by rw [hh, Preadditive.comp_add]; simp only [Category.assoc]

/-- A vanishing page representative is, over an epic cover, a next-filtration
representative plus a differential of an almost cycle. -/
theorem decompose_page_zero (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) {T : A}
    (x : T ⟶ (almost F r p n : A)) (hx : x ≫ toPage F r p n h = 0) :
    ∃ (T' : A) (e : T' ⟶ T) (_ : Epi e)
      (u : T' ⟶ (almost F (r-1) (p+1) n : A))
      (v : T' ⟶ (almost F (r-1) (p-r+1) (n-1) : A)),
      e ≫ x ≫ (almost F r p n).arrow =
        u ≫ (almost F (r-1) (p+1) n).arrow +
          v ≫ (almost F (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n := by
  have hx' := (toPage_zero_iff_denominator F r p n h x).1 hx
  obtain ⟨T₁, e₁, he₁, u, v, huv⟩ := decompose_sum
    (almost F (r-1) (p+1) n)
    (imageSubobject ((almost F (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n))
    (x ≫ (almost F r p n).arrow) hx'
  obtain ⟨T₂, e₂, he₂, w, hw⟩ := surjective_up_to_refinements_of_epi
    (factorThruImageSubobject ((almost F (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n)) v
  refine ⟨T₂, e₂ ≫ e₁, inferInstance, e₂ ≫ u, w, ?_⟩
  calc
    (e₂ ≫ e₁) ≫ x ≫ (almost F r p n).arrow =
        e₂ ≫ (u ≫ (almost F (r-1) (p+1) n).arrow +
          v ≫ (imageSubobject ((almost F (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n)).arrow) := by
      simpa only [Category.assoc] using congrArg (fun z => e₂ ≫ z) huv
    _ = _ := by
      rw [Preadditive.comp_add, ← Category.assoc e₂ v, hw, Category.assoc,
        imageSubobject_arrow_comp]
      simp only [Category.assoc]



/-- Reindex an almost-cycle object by equal integers. -/
def almostIsoOfEq {r r' p p' n n' : ℤ} (hr : r=r') (hp : p=p') (hn : n=n') :
    (almost F r p n : A) ≅ (almost F r' p' n' : A) :=
  eqToIso (by subst r'; subst p'; subst n'; rfl)

@[reassoc (attr := simp)]
theorem almostIsoOfEq_d {r r' p p' n n' : ℤ} (hr : r=r') (hp : p=p') (hn : n=n') (m : ℤ) :
    (almostIsoOfEq F hr hp hn).hom ≫ (almost F r' p' n').arrow ≫ K.d n' m =
      (almost F r p n).arrow ≫ K.d n m := by
  subst r'; subst p'; subst n'
  simp [almostIsoOfEq]

@[reassoc (attr := simp)]
theorem almostIsoOfEq_arrow {r r' p p' n : ℤ} (hr : r=r') (hp : p=p') :
    (almostIsoOfEq F hr hp (rfl : n=n)).hom ≫ (almost F r' p' n).arrow =
      (almost F r p n).arrow := by
  subst r'; subst p'
  simp [almostIsoOfEq]

@[reassoc (attr := simp)]
theorem almostIsoOfEq_inv_d {r r' p p' n n' : ℤ} (hr : r=r') (hp : p=p') (hn : n=n') (m : ℤ) :
    (almostIsoOfEq F hr hp hn).inv ≫ (almost F r p n).arrow ≫ K.d n m =
      (almost F r' p' n').arrow ≫ K.d n' m := by
  subst r'; subst p'; subst n'
  simp [almostIsoOfEq]

/-- Every cycle on page `r` can, after an epic cover, be represented by an
almost `(r+1)`-cycle. The correction is the `v` in `dx = u + dv`. -/
theorem lift_next_cycle (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    {T : A} (z : T ⟶ object F D r p n) (hz : z ≫ D.differential r hr p n = 0) :
    ∃ (T' : A) (e : T' ⟶ T) (_ : Epi e) (w : T' ⟶ (almost F (r+1) p n : A)),
      e ≫ z = w ≫ nextRepresentative F D r p n := by
  obtain ⟨T₁, e₁, he₁, x, hx⟩ := surjective_up_to_refinements_of_epi
    (toPage F r p n (D.containment r p n)) z
  have hdx : (x ≫ D.restriction r hr p n) ≫
      toPage F r (p+r) (n+1) (D.containment r (p+r) (n+1)) = 0 := by
    rw [Category.assoc, ← D.representative_formula, ← Category.assoc, ← hx,
      Category.assoc, hz, comp_zero]
  obtain ⟨T₂, e₂, he₂, u, v, huv⟩ :=
    decompose_page_zero F r (p+r) (n+1) _ (x ≫ D.restriction r hr p n) hdx
  have hp : p+r-r+1=p+1 := by omega
  have hn : n+1-1=n := by omega
  let v' := v ≫ (almostIsoOfEq F (rfl : r-1=r-1) hp hn).hom
  have hvd : v' ≫ (almost F (r-1) (p+1) n).arrow ≫ K.d n (n+1) =
      v ≫ (almost F (r-1) (p+r-r+1) (n+1-1)).arrow ≫ K.d (n+1-1) (n+1) := by
    simp [v', Category.assoc]
  have hv : almost F (r-1) (p+1) n ≤ almost F r p n := by
    rw [almost_inter_next]
    exact inf_le_left
  have hdecomp : e₂ ≫ x ≫ (almost F r p n).arrow ≫ K.d n (n+1) =
      u ≫ (almost F (r-1) (p+r+1) (n+1)).arrow +
        v' ≫ (almost F (r-1) (p+1) n).arrow ≫ K.d n (n+1) := by
    rw [hvd]
    simpa only [Category.assoc, D.restriction_arrow] using huv
  let a := e₂ ≫ x - v' ≫ Subobject.ofLE _ _ hv
  have ha : a ≫ (almost F r p n).arrow ≫ K.d n (n+1) =
      u ≫ (almost F (r-1) (p+r+1) (n+1)).arrow := by
    dsimp only [a]
    simp only [Preadditive.sub_comp, Category.assoc, Subobject.ofLE_arrow_assoc]
    rw [hdecomp, add_sub_cancel_right]
  have haf : (almost F (r+1) p n).Factors (a ≫ (almost F r p n).arrow) := by
    apply (Subobject.inf_factors _).2
    constructor
    · exact Subobject.factors_of_le _ inf_le_left (Subobject.factors_comp_arrow a)
    · apply pullback_factors
      rw [show p+(r+1)=p+r+1 by omega, Category.assoc, ha]
      exact Subobject.factors_of_le _ inf_le_left (Subobject.factors_comp_arrow u)
  let w := (almost F (r+1) p n).factorThru _ haf
  have hw : w ≫ Subobject.ofLE _ _ (almost_succ_le F r p n) = a := by
    apply (cancel_mono (almost F r p n).arrow).1
    simp [w, Category.assoc]
  have hvzero : (v' ≫ Subobject.ofLE _ _ hv) ≫ toPage F r p n (D.containment r p n) = 0 := by
    apply toPage_zero_of_next
    rw [Category.assoc, Subobject.ofLE_arrow]
    exact Subobject.factors_of_le _ inf_le_left (Subobject.factors_comp_arrow v')
  refine ⟨T₂, e₂ ≫ e₁, inferInstance, w, ?_⟩
  dsimp only [nextRepresentative]
  rw [← Category.assoc w, hw]
  dsimp only [a]
  rw [Preadditive.sub_comp, hvzero, sub_zero]
  simpa only [Category.assoc] using congrArg (fun t => e₂ ≫ t) hx

/-- The cohomology class of a next-page almost cycle, centered at the middle
term of the page short complex. -/
abbrev nextClass (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    (almost F (r+1) (p+r) (n+1) : A) ⟶ (shortComplex F D r hr p n).homology :=
  (shortComplex F D r hr p n).liftCycles
    (nextRepresentative F D r (p+r) (n+1)) (next_cycle_at F D r hr (p+r) (n+1)) ≫
      (shortComplex F D r hr p n).homologyπ


/-- The next almost cycles cover the cohomology of the current page. -/
instance nextClass_epi (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    Epi (nextClass F D r hr p n) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T z
  obtain ⟨T₁, e₁, he₁, x, hx, hclass⟩ :=
    (shortComplex F D r hr p n).eq_liftCycles_homologyπ_up_to_refinements z
  obtain ⟨T₂, e₂, he₂, w, hw⟩ := lift_next_cycle F D r hr (p+r) (n+1) x hx
  refine ⟨T₂, e₂ ≫ e₁, inferInstance, w, ?_⟩
  dsimp only [nextClass]
  rw [Category.assoc, hclass, ShortComplex.comp_liftCycles_assoc,
    ShortComplex.comp_liftCycles_assoc]
  apply congrArg (fun t : T₂ ⟶ (shortComplex F D r hr p n).cycles =>
    t ≫ (shortComplex F D r hr p n).homologyπ)
  apply (cancel_mono (shortComplex F D r hr p n).iCycles).1
  simpa only [ShortComplex.liftCycles_i] using hw


@[reassoc]
theorem comp_nextClass (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    {T : A} (x : T ⟶ (almost F (r+1) (p+r) (n+1) : A)) :
    x ≫ nextClass F D r hr p n =
      (shortComplex F D r hr p n).liftCycles
        (x ≫ nextRepresentative F D r (p+r) (n+1))
        (by
          change (x ≫ nextRepresentative F D r (p+r) (n+1)) ≫
            D.differential r hr (p+r) (n+1) = 0
          rw [Category.assoc, next_cycle_at, comp_zero]) ≫
          (shortComplex F D r hr p n).homologyπ := by
  dsimp only [nextClass]
  rw [ShortComplex.comp_liftCycles_assoc]

/-- A next representative that is an incoming page boundary has zero class. -/
theorem nextClass_zero_of_boundary (D : F03Specs.PageData F)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) {T : A}
    (x : T ⟶ (almost F (r+1) (p+r) (n+1) : A))
    (y : T ⟶ object F D r p n)
    (hxy : x ≫ nextRepresentative F D r (p+r) (n+1) = y ≫ D.differential r hr p n) :
    x ≫ nextClass F D r hr p n = 0 := by
  rw [comp_nextClass]
  exact (shortComplex F D r hr p n).liftCycles_homologyπ_eq_zero_of_boundary _ y hxy

/-- Every relation in the next-page denominator vanishes in current-page
cohomology. -/
theorem nextClass_zero_of_toPage_zero (D : F03Specs.PageData F)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) {T : A}
    (x : T ⟶ (almost F (r+1) (p+r) (n+1) : A))
    (hx : x ≫ toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) = 0) :
    x ≫ nextClass F D r hr p n = 0 := by
  obtain ⟨T', e, he, u, v, huv⟩ := decompose_page_zero F (r+1) (p+r) (n+1) _ x hx
  have hrr : r+1-1=r := by omega
  have hpp : p+r-(r+1)+1=p := by omega
  have hnn : n+1-1=n := by omega
  let u' := u ≫ (almostIsoOfEq F hrr (rfl : p+r+1=p+r+1) (rfl : n+1=n+1)).hom
  let v' := v ≫ (almostIsoOfEq F hrr hpp hnn).hom
  have hsum : e ≫ x ≫ (almost F (r+1) (p+r) (n+1)).arrow =
      u' ≫ (almost F r (p+r+1) (n+1)).arrow +
        v' ≫ (almost F r p n).arrow ≫ K.d n (n+1) := by
    simpa only [u', v', Category.assoc, almostIsoOfEq_arrow, almostIsoOfEq_d] using huv
  let a := e ≫ x ≫ Subobject.ofLE _ _ (almost_succ_le F r (p+r) (n+1)) -
    v' ≫ D.restriction r hr p n
  have ha : a ≫ (almost F r (p+r) (n+1)).arrow =
      u' ≫ (almost F r (p+r+1) (n+1)).arrow := by
    dsimp only [a]
    simp only [Preadditive.sub_comp, Category.assoc, Subobject.ofLE_arrow,
      D.restriction_arrow]
    rw [hsum, add_sub_cancel_right]
  have hazero : a ≫ toPage F r (p+r) (n+1) (D.containment r (p+r) (n+1)) = 0 := by
    apply toPage_zero_of_next
    rw [ha]
    exact Subobject.factors_of_le _ inf_le_left (Subobject.factors_comp_arrow u')
  dsimp only [a] at hazero
  rw [Preadditive.sub_comp, sub_eq_zero] at hazero
  have hj : (e ≫ x) ≫ nextRepresentative F D r (p+r) (n+1) =
      (v' ≫ toPage F r p n (D.containment r p n)) ≫ D.differential r hr p n := by
    simpa only [nextRepresentative, Category.assoc, D.representative_formula] using hazero
  apply (cancel_epi e).1
  rw [comp_zero, ← Category.assoc]
  exact nextClass_zero_of_boundary F D r hr p n (e ≫ x) _ hj


/-- Incoming representative differentials lie in the next-page denominator. -/
theorem differential_factors_next_denominator (r p n : ℤ) {T : A}
    (x : T ⟶ (almost F r p n : A)) :
    (denominator F (r+1) (p+r) (n+1)).Factors
      (x ≫ (almost F r p n).arrow ≫ K.d n (n+1)) := by
  let y := x ≫ (almostIsoOfEq F (show r+1-1=r by omega)
    (show p+r-(r+1)+1=p by omega) (show n+1-1=n by omega)).inv
  have h : (denominator F (r+1) (p+r) (n+1)).Factors
      (y ≫ (almost F (r+1-1) (p+r-(r+1)+1) (n+1-1)).arrow ≫ K.d (n+1-1) (n+1)) := by
    apply Subobject.factors_of_le _
      (show imageSubobject ((almost F (r+1-1) (p+r-(r+1)+1) (n+1-1)).arrow ≫
        K.d (n+1-1) (n+1)) ≤ denominator F (r+1) (p+r) (n+1) from le_sup_right)
    exact imageSubobject_factors_comp_self _ y
  simpa only [y, Category.assoc, almostIsoOfEq_inv_d] using h

/-- Vanishing in current-page cohomology gives precisely a next-page
quotient relation. All refinements are finite epic pullbacks. -/
theorem toPage_zero_of_nextClass_zero (D : F03Specs.PageData F)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) {T : A}
    (x : T ⟶ (almost F (r+1) (p+r) (n+1) : A))
    (hx : x ≫ nextClass F D r hr p n = 0) :
    x ≫ toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) = 0 := by
  rw [comp_nextClass] at hx
  obtain ⟨T₁, e₁, he₁, y, hy⟩ :=
    ((shortComplex F D r hr p n).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _).1 hx
  obtain ⟨T₂, e₂, he₂, z, hz⟩ := surjective_up_to_refinements_of_epi
    (toPage F r p n (D.containment r p n)) y
  have hrel : (e₂ ≫ e₁) ≫ x ≫ nextRepresentative F D r (p+r) (n+1) =
      z ≫ D.restriction r hr p n ≫ toPage F r (p+r) (n+1) (D.containment r (p+r) (n+1)) := by
    calc
      _ = (e₂ ≫ y) ≫ D.differential r hr p n := by
        simpa only [shortComplex, Category.assoc] using congrArg (fun t => e₂ ≫ t) hy
      _ = _ := by rw [hz, Category.assoc, D.representative_formula]
  let a := (e₂ ≫ e₁) ≫ x ≫ Subobject.ofLE _ _ (almost_succ_le F r (p+r) (n+1)) -
    z ≫ D.restriction r hr p n
  have ha : a ≫ toPage F r (p+r) (n+1) (D.containment r (p+r) (n+1)) = 0 := by
    dsimp only [a]
    rw [Preadditive.sub_comp, sub_eq_zero]
    simpa only [nextRepresentative, Category.assoc] using hrel
  obtain ⟨T₃, e₃, he₃, u, v, huv⟩ := decompose_page_zero F r (p+r) (n+1) _ a ha
  let v' := v ≫ (almostIsoOfEq F (rfl : r-1=r-1)
    (show p+r-r+1=p+1 by omega) (show n+1-1=n by omega)).hom
  have huv' :
      ((e₃ ≫ e₂ ≫ e₁) ≫ x ≫ (almost F (r+1) (p+r) (n+1)).arrow) -
        ((e₃ ≫ z) ≫ (almost F r p n).arrow ≫ K.d n (n+1)) =
      u ≫ (almost F (r-1) (p+r+1) (n+1)).arrow +
        v' ≫ (almost F (r-1) (p+1) n).arrow ≫ K.d n (n+1) := by
    simpa only [a, v', Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      Subobject.ofLE_arrow, D.restriction_arrow, almostIsoOfEq_d] using huv
  have hsum := sub_eq_iff_eq_add.mp huv'
  have hud : u ≫ (almost F (r-1) (p+r+1) (n+1)).arrow ≫ K.d (n+1) (n+1+1) =
      (e₃ ≫ e₂ ≫ e₁) ≫ x ≫ (almost F (r+1) (p+r) (n+1)).arrow ≫
        K.d (n+1) (n+1+1) := by
    have hh := congrArg (fun t => t ≫ K.d (n+1) (n+1+1)) hsum
    simpa only [Preadditive.add_comp, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, add_zero] using hh.symm
  have hu : (almost F r (p+r+1) (n+1)).Factors
      (u ≫ (almost F (r-1) (p+r+1) (n+1)).arrow) := by
    apply (Subobject.inf_factors _).2
    constructor
    · exact Subobject.factors_of_le _ inf_le_left (Subobject.factors_comp_arrow u)
    · apply pullback_factors
      rw [Category.assoc, hud, show p+r+1+r=(p+r)+(r+1) by omega]
      apply Subobject.factors_of_factors_right (e₃ ≫ e₂ ≫ e₁)
      rw [← Category.assoc x]
      apply (pullback_factors_iff (K.d (n+1) (n+1+1))
        (F.piece ((p+r)+(r+1)) (n+1+1)) _).1
      exact Subobject.factors_of_le _ inf_le_right (Subobject.factors_comp_arrow x)
  have huD : (denominator F (r+1) (p+r) (n+1)).Factors
      (u ≫ (almost F (r-1) (p+r+1) (n+1)).arrow) := by
    have hu' : (almost F (r+1-1) (p+r+1) (n+1)).Factors
        (u ≫ (almost F (r-1) (p+r+1) (n+1)).arrow) := by
      simpa only [show r+1-1=r by omega] using hu
    exact Subobject.factors_of_le _
      (show almost F (r+1-1) (p+r+1) (n+1) ≤ denominator F (r+1) (p+r) (n+1)
        from le_sup_left) hu' 
  have hv : almost F (r-1) (p+1) n ≤ almost F r p n := by
    rw [almost_inter_next]
    exact inf_le_left
  have hvD : (denominator F (r+1) (p+r) (n+1)).Factors
      (v' ≫ (almost F (r-1) (p+1) n).arrow ≫ K.d n (n+1)) := by
    simpa only [Category.assoc, Subobject.ofLE_arrow_assoc] using
      differential_factors_next_denominator F r p n (v' ≫ Subobject.ofLE _ _ hv)
  have hzD := differential_factors_next_denominator F r p n (e₃ ≫ z)
  have hD := Subobject.factors_add _ _ (Subobject.factors_add _ _ huD hvD) hzD
  apply (cancel_epi (e₃ ≫ e₂ ≫ e₁)).1
  rw [comp_zero, ← Category.assoc]
  apply (toPage_zero_iff_denominator F (r+1) (p+r) (n+1) _ _).2
  rw [Category.assoc, hsum]
  exact hD

/-- Assembly of the next-page isomorphism from the two substantive comparison
claims: surjectivity on cohomology and equality of the representative relations.
The two comparison claims are proved above for the actual page objects. -/
def nextIsoOfCriteria (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (he : Epi (nextClass F D r hr p n))
    (hk : ∀ {T : A} (x : T ⟶ (almost F (r+1) (p+r) (n+1) : A)),
      x ≫ nextClass F D r hr p n = 0 ↔
        x ≫ toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) = 0) :
    object F D (r+1) (p+r) (n+1) ≅ (shortComplex F D r hr p n).homology := by
  let q := toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1))
  let g := Abelian.epiDesc q (nextClass F D r hr p n)
    ((hk (kernel.ι q)).2 (kernel.condition q))
  have hq : q ≫ g = nextClass F D r hr p n := Abelian.comp_epiDesc _ _ _
  have : Epi g := epi_of_epi_fac hq
  have : Mono g := by
    apply Preadditive.mono_of_cancel_zero
    intro T z hz
    obtain ⟨T', e, he', x, hx⟩ := surjective_up_to_refinements_of_epi q z
    apply (cancel_epi e).1
    rw [comp_zero, hx]
    apply (hk x).1
    rw [← hq, ← Category.assoc, ← hx, Category.assoc, hz, comp_zero]
  have : IsIso g := isIso_of_mono_of_epi g
  exact asIso g

@[reassoc (attr := simp)]
theorem toPage_nextIsoOfCriteria (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (he : Epi (nextClass F D r hr p n))
    (hk : ∀ {T : A} (x : T ⟶ (almost F (r+1) (p+r) (n+1) : A)),
      x ≫ nextClass F D r hr p n = 0 ↔
        x ≫ toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) = 0) :
    toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) ≫
        (nextIsoOfCriteria F D r hr p n he hk).hom = nextClass F D r hr p n :=
  Abelian.comp_epiDesc _ _ _

/-- Equality of the next-page quotient relations and the relations in
current-page cohomology, tested on arbitrary generalized representatives. -/
theorem nextClass_zero_iff (D : F03Specs.PageData F)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) {T : A}
    (x : T ⟶ (almost F (r+1) (p+r) (n+1) : A)) :
    x ≫ nextClass F D r hr p n = 0 ↔
      x ≫ toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) = 0 :=
  ⟨toPage_zero_of_nextClass_zero F D r hr p n x,
    nextClass_zero_of_toPage_zero F D r hr p n x⟩

/-- The canonical next-page isomorphism, valid also for `r = 0`. -/
def nextIso (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    object F D (r+1) (p+r) (n+1) ≅ (shortComplex F D r hr p n).homology :=
  nextIsoOfCriteria F D r hr p n inferInstance (nextClass_zero_iff F D r hr p n)

@[reassoc (attr := simp)]
theorem toPage_nextIso (D : F03Specs.PageData F) (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) ≫
      (nextIso F D r hr p n).hom = nextClass F D r hr p n :=
  toPage_nextIsoOfCriteria F D r hr p n _ _

/-- All page-cohomology identifications with their canonical formulas. -/
def data (D : F03Specs.PageData F) : Data F D where
  zeroIso := D.zeroPageIso
  zeroIso_formula := D.zeroPageIso_formula
  zero_differential := D.zero_differential
  firstIso p n := firstIso F p n _
  firstIso_formula p n := toPage_firstIso F p n _
  first_differential := first_differential F D
  next_cycle r hr p n := next_cycle_at F D r hr (p+r) (n+1)
  nextIso := nextIso F D
  nextIso_formula := toPage_nextIso F D

end PageCohomology
/-- HA-F04's first-page identification and connecting-differential formula. -/
theorem filtered_first_pages : F04Specs.FirstPages.{v,u} := by
  intro A _ _ K F D
  exact ⟨{
    firstIso := fun p n => PageCohomology.firstIso F p n _
    firstIso_formula := fun p n => PageCohomology.toPage_firstIso F p n _
    first_differential := PageCohomology.first_differential F D }⟩

/-- The next almost cycles are cycles for the current page differential. -/
theorem filtered_next_cycles : F04Specs.NextCycles.{v,u} := by
  intro A _ _ K F D r hr p n
  exact PageCohomology.next_cycle_at F D r hr p n

/-- HA-F04: the actual filtered pages form a cohomological spectral sequence,
with the first-page and connecting-map identifications. -/
theorem filtered_page_cohomology : F04Specs.FullStatement.{v,u} := by
  intro A _ _ K F
  exact ⟨FilteredPage.pageData F, ⟨PageCohomology.data F (FilteredPage.pageData F)⟩⟩

end AdvancedHomologicalAlgebra
