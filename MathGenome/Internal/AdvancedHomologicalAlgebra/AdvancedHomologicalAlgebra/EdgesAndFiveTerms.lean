import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.EdgesAndFiveTerms
import Mathlib.CategoryTheory.Abelian.Exact

set_option maxHeartbeats 2000000
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

/-- A zero term remains zero on the next page. -/
theorem next_isZero (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (h : IsZero (PageCohomology.object F D r p n)) :
    IsZero (PageCohomology.object F D (r+1) p n) := by
  let S := PageCohomology.shortComplex F D r hr (p-r) (n-1)
  have hm : IsZero S.X₂ := by simpa [S, PageCohomology.shortComplex] using h
  have hz := S.isZero_homology_of_isZero_X₂ hm
  have e := (PageCohomology.data F D).nextIso r hr (p-r) (n-1)
  have he : IsZero (PageCohomology.object F D (r+1) ((p-r)+r) ((n-1)+1)) :=
    hz.of_iso e
  simpa using he

/-- The first-quadrant hypothesis propagates from E₂ to every later page. -/
theorem firstQuadrant_later (hQ : FirstQuadrant F D) (r : ℤ) (hr : 2 ≤ r)
    (p n : ℤ) (hpn : p < 0 ∨ n < p) :
    IsZero (PageCohomology.object F D r p n) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = 2 + k := by
    exact ⟨(r-2).toNat, by omega⟩
  induction k with
  | zero => simpa using hQ p n hpn
  | succ k ih =>
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
      next_isZero F D (2 + (k : ℤ)) (by omega) p n (ih (by omega))

/-- No differential on or after E₂ leaves row zero. -/
theorem row_differential_zero (hQ : FirstQuadrant F D) (r : ℤ) (hr : 2 ≤ r) (n : ℤ) :
    D.differential r (by omega) n n = 0 := by
  exact (firstQuadrant_later F D hQ r hr (n+r) (n+1) (Or.inr (by omega))).eq_of_tgt _ _

/-- No differential on or after E₂ enters column zero. -/
theorem column_incoming_zero (hQ : FirstQuadrant F D) (r : ℤ) (hr : 2 ≤ r) (n : ℤ) :
    D.differential r (by omega) (-r) (n-1) = 0 := by
  exact (firstQuadrant_later F D hQ r hr (-r) (n-1) (Or.inl (by omega))).eq_of_src _ _

/-- The only possible incoming map at (1,0) already vanishes on E₂. -/
theorem E10_incoming_zero (hQ : FirstQuadrant F D) (r : ℤ) (hr : 2 ≤ r) :
    D.differential r (by omega) (1-r) 0 = 0 := by
  exact (firstQuadrant_later F D hQ r hr (1-r) 0 (Or.inl (by omega))).eq_of_src _ _

/-- After d₂, nothing leaves (0,1). -/
theorem E01_outgoing_zero (hQ : FirstQuadrant F D) (r : ℤ) (hr : 3 ≤ r) :
    D.differential r (by omega) 0 1 = 0 := by
  simpa only [zero_add] using
    (firstQuadrant_later F D hQ r (by omega) (0+r) (1+1)
      (Or.inr (by omega))).eq_of_tgt (D.differential r (by omega) 0 1) 0

/-- After d₂, nothing enters (2,0). -/
theorem E20_incoming_zero (hQ : FirstQuadrant F D) (r : ℤ) (hr : 3 ≤ r) :
    D.differential r (by omega) (2-r) 1 = 0 := by
  exact (firstQuadrant_later F D hQ r (by omega) (2-r) 1 (Or.inl (by omega))).eq_of_src _ _

/-- Outside the first quadrant the limiting cohomology quotient is zero. -/
theorem gradedCohomology_isZero (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D)
    (p n : ℤ) (hpn : p < 0 ∨ n < p) : IsZero (gradedCohomology F p n) := by
  obtain ⟨R, hR, hs⟩ := uniform_stabilization F hF n
  let r := max 2 R
  have hr : R ≤ r := le_max_right _ _
  have h2 : 2 ≤ r := le_max_left _ _
  exact (firstQuadrant_later F D hQ r h2 p n hpn).of_iso
    (limitIso F D r p n (hs r hr p)).iso.symm

/-- A vanishing associated graded quotient identifies adjacent subobjects. -/
theorem cohomologyPiece_eq_of_graded_isZero (p n : ℤ)
    (hz : IsZero (gradedCohomology F p n)) :
    cohomologyPiece F (p+1) n = cohomologyPiece F p n := by
  let i := Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)
  have : Epi i := Preadditive.epi_of_isZero_cokernel i hz
  have : IsIso i := isIso_of_mono_of_epi i
  exact Subobject.eq_of_comm (asIso i) (Subobject.ofLE_arrow _)

/-- In a first-quadrant abutment, the cohomology filtration is the entire
cohomology object at step zero. This uses finiteness, not any assertion about
F⁰ of the original complex. -/
theorem cohomologyPiece_zero_eq_top (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D)
    (n : ℤ) : cohomologyPiece F 0 n = ⊤ := by
  obtain ⟨a, b, ha, hb⟩ := (cohomology_filtration F hF).finite n
  let a' := min a 0
  have hbase : cohomologyPiece F a' n = ⊤ := ha a' (min_le_left _ _)
  have heq : ∀ k : ℕ, (a' + k : ℤ) ≤ 0 →
      cohomologyPiece F (a'+k) n = cohomologyPiece F a' n := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hz := gradedCohomology_isZero F D hF hQ (a'+k) n (Or.inl (by omega))
      have hh := cohomologyPiece_eq_of_graded_isZero F (a'+k) n hz
      rw [show (a' + (↑(k+1) : ℤ)) = (a'+k)+1 by omega, hh, ih (by omega)]
  have h0 := heq (-a').toNat (by dsimp [a']; omega)
  have he : a' + (↑((-a').toNat) : ℤ) = 0 := by dsimp [a']; omega
  rw [he, hbase] at h0
  exact h0

/-- There are no nonzero cohomology filtration steps past total degree n. -/
theorem cohomologyPiece_above_eq_bot (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D)
    (n : ℤ) : cohomologyPiece F (n+1) n = ⊥ := by
  obtain ⟨a, b, ha, hb⟩ := (cohomology_filtration F hF).finite n
  let b' := max b (n+1)
  have hbase : cohomologyPiece F b' n = ⊥ := hb b' (le_max_left _ _)
  have heq : ∀ k : ℕ, cohomologyPiece F (n+1+k) n = cohomologyPiece F (n+1) n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hz := gradedCohomology_isZero F D hF hQ (n+1+k) n (Or.inr (by omega))
      have hh := cohomologyPiece_eq_of_graded_isZero F (n+1+k) n hz
      rw [show (n+1 + (↑(k+1) : ℤ)) = (n+1+k)+1 by omega, hh, ih]
  have he : n+1 + (↑((b'-(n+1)).toNat) : ℤ) = b' := by dsimp [b']; omega
  have hh := heq (b'-(n+1)).toNat
  rw [he, hbase] at hh
  exact hh.symm

/-- The next-page quotient when the outgoing differential vanishes. The
indices here are those of the upstream short complex's left term. -/
def nextQuotient (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hg : D.differential r hr (p+r) (n+1) = 0) :
    PageCohomology.object F D r (p+r) (n+1) ⟶
      PageCohomology.object F D (r+1) (p+r) (n+1) := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.iCycles := S.isIso_iCycles hg
  exact inv S.iCycles ≫ S.homologyπ ≫ ((PageCohomology.data F D).nextIso r hr p n).inv

instance nextQuotient_epi (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hg : D.differential r hr (p+r) (n+1) = 0) : Epi (nextQuotient F D r hr p n hg) := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.iCycles := S.isIso_iCycles hg
  dsimp only [nextQuotient]
  infer_instance

/-- The quotient is induced by inclusion of the next almost cycles. -/
theorem nextRepresentative_nextQuotient (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hg : D.differential r hr (p+r) (n+1) = 0) :
    PageCohomology.nextRepresentative F D r (p+r) (n+1) ≫ nextQuotient F D r hr p n hg =
      FilteredPage.toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.iCycles := S.isIso_iCycles hg
  apply (cancel_mono ((PageCohomology.data F D).nextIso r hr p n).hom).1
  rw [(PageCohomology.data F D).nextIso_formula]
  dsimp only [nextQuotient]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hw : PageCohomology.nextRepresentative F D r (p+r) (n+1) ≫ inv S.iCycles =
      S.liftCycles (PageCohomology.nextRepresentative F D r (p+r) (n+1))
        ((PageCohomology.data F D).next_cycle r hr p n) := by
    apply (cancel_mono S.iCycles).1
    simp
  simpa only [Category.assoc] using congrArg (fun z => z ≫ S.homologyπ) hw

/-- The next-page inclusion when the incoming differential vanishes. -/
def nextInclusion (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr p n = 0) :
    PageCohomology.object F D (r+1) (p+r) (n+1) ⟶
      PageCohomology.object F D r (p+r) (n+1) := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.homologyπ := S.isIso_homologyπ hf
  exact ((PageCohomology.data F D).nextIso r hr p n).hom ≫ inv S.homologyπ ≫ S.iCycles

instance nextInclusion_mono (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr p n = 0) : Mono (nextInclusion F D r hr p n hf) := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.homologyπ := S.isIso_homologyπ hf
  dsimp only [nextInclusion]
  infer_instance

/-- The inclusion has the canonical representative formula. -/
theorem toPage_nextInclusion (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr p n = 0) :
    FilteredPage.toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)) ≫
        nextInclusion F D r hr p n hf =
      PageCohomology.nextRepresentative F D r (p+r) (n+1) := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.homologyπ := S.isIso_homologyπ hf
  dsimp only [nextInclusion]
  rw [← Category.assoc, ← Category.assoc, (PageCohomology.data F D).nextIso_formula]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, ShortComplex.liftCycles_i]

/-- Closed representatives commute with the next-page quotient. -/
theorem closedToPage_nextQuotient (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hg : D.differential r hr (p+r) (n+1) = 0) :
    closedToPage F D r (p+r) (n+1) ≫ nextQuotient F D r hr p n hg =
      closedToPage F D (r+1) (p+r) (n+1) := by
  have hw : closedToPage F D r (p+r) (n+1) =
      Subobject.ofLE _ _ (closed_le_almost F (r+1) (p+r) (n+1)) ≫
        PageCohomology.nextRepresentative F D r (p+r) (n+1) := by
    simp only [closedToPage, PageCohomology.nextRepresentative, ← Category.assoc,
      Subobject.ofLE_comp_ofLE]
  rw [hw, Category.assoc, nextRepresentative_nextQuotient]
  rfl

/-- Closed representatives commute with the next-page inclusion. -/
theorem closedToPage_nextInclusion (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr p n = 0) :
    closedToPage F D (r+1) (p+r) (n+1) ≫ nextInclusion F D r hr p n hf =
      closedToPage F D r (p+r) (n+1) := by
  dsimp only [closedToPage]
  rw [Category.assoc, toPage_nextInclusion]
  simp only [PageCohomology.nextRepresentative, ← Category.assoc, Subobject.ofLE_comp_ofLE]

/-- Centered version of the quotient, convenient for iteration. -/
theorem quotient_step (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hg : D.differential r hr p n = 0) :
    ∃ q : PageCohomology.object F D r p n ⟶ PageCohomology.object F D (r+1) p n,
      Epi q ∧ closedToPage F D r p n ≫ q = closedToPage F D (r+1) p n := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, p = a+r := ⟨p-r, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b+1 := ⟨n-1, by omega⟩
  subst p; subst n
  exact ⟨nextQuotient F D r hr a b hg, inferInstance,
    closedToPage_nextQuotient F D r hr a b hg⟩

/-- Centered version of the inclusion, convenient for iteration. -/
theorem inclusion_step (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr (p-r) (n-1) = 0) :
    ∃ i : PageCohomology.object F D (r+1) p n ⟶ PageCohomology.object F D r p n,
      Mono i ∧ closedToPage F D (r+1) p n ≫ i = closedToPage F D r p n := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, p = a+r := ⟨p-r, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b+1 := ⟨n-1, by omega⟩
  subst p; subst n
  have hf' : D.differential r hr a b = 0 := by
    rw [show a+r-r=a by omega, show b+1-1=b by omega] at hf
    exact hf
  exact ⟨nextInclusion F D r hr a b hf', inferInstance,
    closedToPage_nextInclusion F D r hr a b hf'⟩

/-- Every page boundary is represented by an actual closed element. -/
theorem boundaries_le_stableCycles (r p n : ℤ) :
    FilteredPage.boundaries F r p n ≤ stableCycles F p n := by
  have hb : FilteredPage.boundarySource F r p n ≤ closed F p n :=
    le_inf inf_le_left (le_kernelSubobject _ _ (FilteredPage.boundarySource_d F r p n))
  dsimp only [FilteredPage.boundaries, stableCycles]
  simpa only [FilteredPage.gradedRepresentative_naturality] using
    imageSubobject_comp_le (Subobject.ofLE _ _ hb)
      (FilteredPage.gradedRepresentative F p n (closed F p n) inf_le_left)

/-- The next cycle subobject lies in the current one, before quotienting. -/
theorem cycles_succ_le (r p n : ℤ) :
    FilteredPage.cycles F (r+1) p n ≤ FilteredPage.cycles F r p n := by
  dsimp only [FilteredPage.cycles]
  simpa only [FilteredPage.gradedRepresentative_naturality] using
    imageSubobject_comp_le (Subobject.ofLE _ _ (PageCohomology.almost_succ_le F r p n))
      (FilteredPage.gradedRepresentative F p n (FilteredPage.almost F r p n) inf_le_left)

theorem stableCycles_le_cycles (r p n : ℤ) : stableCycles F p n ≤ FilteredPage.cycles F r p n := by
  dsimp only [stableCycles, FilteredPage.cycles]
  simpa only [FilteredPage.gradedRepresentative_naturality] using
    imageSubobject_comp_le (Subobject.ofLE _ _ (closed_le_almost F r p n))
      (FilteredPage.gradedRepresentative F p n (FilteredPage.almost F r p n) inf_le_left)

/-- Quotienting by a subobject of S cannot make a proper inclusion S ⊆ T
surjective. This uses only cokernels and the abelian mono/epi criterion. -/
theorem subobject_eq_of_quotient_epi {X : A} (B S T : Subobject X)
    (hBS : B ≤ S) (hST : S ≤ T)
    (he : Epi (Subobject.ofLE _ _ hST ≫ cokernel.π (Subobject.ofLE _ _ (hBS.trans hST)))) :
    S = T := by
  let i := Subobject.ofLE B T (hBS.trans hST)
  let j := Subobject.ofLE S T hST
  have hi : i ≫ cokernel.π j = 0 := by
    rw [show i = Subobject.ofLE B S hBS ≫ j by simp [i, j], Category.assoc,
      cokernel.condition, comp_zero]
  let z := cokernel.desc i (cokernel.π j) hi
  have hz : z = 0 := by
    apply (cancel_epi (j ≫ cokernel.π i)).1
    simp [z, Category.assoc]
  have hj : cokernel.π j = 0 := by
    rw [← cokernel.π_desc i (cokernel.π j) hi]
    change cokernel.π i ≫ z = 0
    rw [hz, comp_zero]
  have : Epi j := Preadditive.epi_of_cokernel_zero hj
  have : IsIso j := isIso_of_mono_of_epi j
  exact Subobject.eq_of_comm (asIso j) (Subobject.ofLE_arrow _)

/-- If the outgoing differential is zero, the cycle subobject itself does
not shrink on the next page, since every boundary is already closed. -/
theorem cycles_eq_of_differential_zero (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hg : D.differential r hr p n = 0) :
    FilteredPage.cycles F (r+1) p n = FilteredPage.cycles F r p n := by
  let j := Subobject.ofLE _ _ (cycles_succ_le F r p n)
  let a := factorThruImageSubobject
    (FilteredPage.gradedRepresentative F p n (FilteredPage.almost F (r+1) p n) inf_le_left)
  let b := Subobject.ofLE _ _ (PageCohomology.almost_succ_le F r p n) ≫
    factorThruImageSubobject
      (FilteredPage.gradedRepresentative F p n (FilteredPage.almost F r p n) inf_le_left)
  have hab : a ≫ j = b := by
    apply (cancel_mono (FilteredPage.cycles F r p n).arrow).1
    simp only [a, j, b, Category.assoc, Subobject.ofLE_arrow,
      imageSubobject_arrow_comp, FilteredPage.gradedRepresentative_naturality]
  have he : Epi (PageCohomology.nextRepresentative F D r p n) := by
    rw [epi_iff_surjective_up_to_refinements]
    intro T z
    exact PageCohomology.lift_next_cycle F D r hr p n z (by rw [hg, comp_zero])
  have hw : a ≫ (j ≫ cokernel.π (Subobject.ofLE _ _ (D.containment r p n))) =
      PageCohomology.nextRepresentative F D r p n := by
    rw [← Category.assoc, hab]
    simp only [b, PageCohomology.nextRepresentative, FilteredPage.toPage, Category.assoc]
  have he' : Epi (j ≫ cokernel.π (Subobject.ofLE _ _ (D.containment r p n))) :=
    epi_of_epi_fac hw
  exact subobject_eq_of_quotient_epi _ _ _
    ((boundaries_le_stableCycles F r p n).trans (stableCycles_le_cycles F (r+1) p n))
    (cycles_succ_le F r p n) he'

/-- Along row zero the cycle subobject has already reached its limiting
value on E₂; later changes can only add boundaries. -/
theorem row_cycles_stable (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) (n : ℤ) :
    FilteredPage.cycles F 2 n n = stableCycles F n n := by
  have heq : ∀ k : ℕ, FilteredPage.cycles F (2+k) n n = FilteredPage.cycles F 2 n n := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show (2+(↑(k+1):ℤ))=(2+k)+1 by omega,
        cycles_eq_of_differential_zero F D (2+k) (by omega) n n
          (row_differential_zero F D hQ (2+k) (by omega) n), ih]
  obtain ⟨R, hR, hs⟩ := uniform_stabilization F hF n
  let r := max 2 R
  have hk : 2 + (↑((r-2).toNat) : ℤ) = r := by dsimp [r]; omega
  have hh := heq (r-2).toNat
  rw [hk, (hs r (le_max_right _ _) n).1] at hh
  exact hh.symm

theorem row_closedToPage_epi (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) (n : ℤ) :
    Epi (closedToPage F D 2 n n) :=
  closedToPage_epi F D 2 n n (row_cycles_stable F D hF hQ n)

/-- Every later row-zero term is a canonical quotient of E₂. -/
theorem row_comparison (hQ : FirstQuadrant F D) (r : ℤ) (hr : 2 ≤ r) (n : ℤ) :
    ∃ q : PageCohomology.object F D 2 n n ⟶ PageCohomology.object F D r n n,
      Epi q ∧ closedToPage F D 2 n n ≫ q = closedToPage F D r n n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = 2 + k := ⟨(r-2).toNat, by omega⟩
  clear hr
  induction k with
  | zero => exact ⟨𝟙 _, inferInstance, by simp⟩
  | succ k ih =>
    obtain ⟨q, hq, hqf⟩ := ih
    obtain ⟨s, hs, hsf⟩ := quotient_step F D (2+k) (by omega) n n
      (row_differential_zero F D hQ (2+k) (by omega) n)
    have h : ∃ z : PageCohomology.object F D 2 n n ⟶
        PageCohomology.object F D ((2+k)+1) n n,
        Epi z ∧ closedToPage F D 2 n n ≫ z = closedToPage F D ((2+k)+1) n n :=
      ⟨q ≫ s, inferInstance, by rw [← Category.assoc, hqf, hsf]⟩
    rw [show (2 + (↑(k+1) : ℤ)) = (2+k)+1 by omega]
    exact h

/-- Every later column-zero term is a canonical subobject of E₂. -/
theorem column_comparison (hQ : FirstQuadrant F D) (r : ℤ) (hr : 2 ≤ r) (n : ℤ) :
    ∃ i : PageCohomology.object F D r 0 n ⟶ PageCohomology.object F D 2 0 n,
      Mono i ∧ closedToPage F D r 0 n ≫ i = closedToPage F D 2 0 n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = 2 + k := ⟨(r-2).toNat, by omega⟩
  clear hr
  induction k with
  | zero => exact ⟨𝟙 _, inferInstance, by simp⟩
  | succ k ih =>
    obtain ⟨i, hi, hif⟩ := ih
    obtain ⟨s, hs, hsf⟩ := inclusion_step F D (2+k) (by omega) 0 n
      (by rw [zero_sub]; exact column_incoming_zero F D hQ (2+k) (by omega) n)
    have h : ∃ z : PageCohomology.object F D ((2+k)+1) 0 n ⟶
        PageCohomology.object F D 2 0 n,
        Mono z ∧ closedToPage F D ((2+k)+1) 0 n ≫ z = closedToPage F D 2 0 n :=
      ⟨s ≫ i, inferInstance, by rw [← Category.assoc, hsf, hif]⟩
    rw [show (2 + (↑(k+1) : ℤ)) = (2+k)+1 by omega]
    exact h

/-- A bottom subobject has zero inclusion into any larger subobject. -/
theorem ofLE_zero_of_eq_bot {H : A} {S T : Subobject H} (h : S ≤ T) (hS : S = ⊥) :
    Subobject.ofLE S T h = 0 := by
  apply (cancel_mono T.arrow).1
  rw [Subobject.ofLE_arrow, zero_comp]
  exact Subobject.mk_eq_bot_iff_zero.mp (by simpa only [Subobject.mk_arrow] using hS)

/-- The kernel of the quotient by S, expressed using an isomorphic ambient
step T, is precisely S as a subobject of the original ambient object. -/
theorem kernel_inverse_quotient {H : A} (S T : Subobject H) (h : S ≤ T) [IsIso T.arrow] :
    kernelSubobject (inv T.arrow ≫ cokernel.π (Subobject.ofLE S T h)) = S := by
  let i := Subobject.ofLE S T h
  apply le_antisymm
  · let x := (kernelSubobject (inv T.arrow ≫ cokernel.π i)).arrow ≫ inv T.arrow
    have hx : x ≫ cokernel.π i = 0 := by
      simpa only [x, Category.assoc] using kernelSubobject_arrow_comp
        (inv T.arrow ≫ cokernel.π i)
    apply Subobject.le_of_comm (Abelian.monoLift i x hx)
    rw [← Subobject.ofLE_arrow h, ← Category.assoc, Abelian.monoLift_comp]
    simp only [x, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · apply le_kernelSubobject
    rw [← Subobject.ofLE_arrow h]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, cokernel.condition]

/-- Construct the row edge by quotienting onto a stable row term, then
using HA-S01 and the vanishing of the next cohomology filtration step. -/
theorem exists_row_edge (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) (n : ℤ) :
    ∃ e : PageCohomology.object F D 2 n n ⟶ K.homology n,
      closedToPage F D 2 n n ≫ e = ambientClass F n n ∧
      imageSubobject e = cohomologyPiece F n n := by
  obtain ⟨R, hR, hs⟩ := uniform_stabilization F hF n
  let r := max 2 R
  let L := limitIso F D r n n (hs r (le_max_right _ _) n)
  obtain ⟨q, hq, hqf⟩ := row_comparison F D hQ r (le_max_left _ _) n
  let π := cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F n n))
  have hπ : IsIso π := cokernel.π_of_zero
    (ofLE_zero_of_eq_bot _ (cohomologyPiece_above_eq_bot F D hF hQ n))
  let e := (q ≫ L.iso.hom ≫ inv π) ≫ (cohomologyPiece F n n).arrow
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e]
    simp only [Category.assoc]
    rw [reassoc_of% hqf, reassoc_of% L.representative_formula]
    simp only [gradedClass, π, Category.assoc, IsIso.hom_inv_id_assoc]
  · have : StrongEpi (q ≫ L.iso.hom ≫ inv π) := strongEpi_of_epi _
    dsimp only [e]
    rw [imageSubobject_comp_of_strongEpi, imageSubobject_mono, Subobject.mk_arrow]

/-- Construct the column edge by the quotient of cohomology by F¹, followed
by the stable column term's inclusion into E₂. -/
theorem exists_column_edge (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) (n : ℤ) :
    ∃ e : K.homology n ⟶ PageCohomology.object F D 2 0 n,
      ambientClass F 0 n ≫ e = closedToPage F D 2 0 n ∧
      kernelSubobject e = cohomologyPiece F 1 n := by
  obtain ⟨R, hR, hs⟩ := uniform_stabilization F hF n
  let r := max 2 R
  let L := limitIso F D r 0 n (hs r (le_max_right _ _) 0)
  obtain ⟨i, hi, hif⟩ := column_comparison F D hQ r (le_max_left _ _) n
  have h0 : IsIso (cohomologyPiece F 0 n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (cohomologyPiece_zero_eq_top F D hF hQ n)
  let π := cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F 0 n))
  let e := (inv (cohomologyPiece F 0 n).arrow ≫ π) ≫ (L.iso.inv ≫ i)
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e, ambientClass]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← Category.assoc]
    change (gradedClass F 0 n ≫ L.iso.inv) ≫ i = _
    rw [← L.representative_formula]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hif]
  · dsimp only [e]
    rw [kernelSubobject_comp_mono]
    exact kernel_inverse_quotient _ _ _

/-- Edge maps in all nonnegative degrees. Their choices are constrained by
the representative formulas, and hence are unique. -/
def edgeData (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) : EdgeData F D where
  row n _ := (exists_row_edge F D hF hQ n).choose
  column n _ := (exists_column_edge F D hF hQ n).choose
  row_formula n _ := (exists_row_edge F D hF hQ n).choose_spec.1
  column_formula n _ := (exists_column_edge F D hF hQ n).choose_spec.1
  row_image n _ := (exists_row_edge F D hF hQ n).choose_spec.2
  column_kernel n _ := (exists_column_edge F D hF hQ n).choose_spec.2

/-- Ambient closed classes commute with filtered cochain maps. -/
@[reassoc]
theorem ambientClass_naturality {X Y : FilteredComplex A} (f : FilteredMap X Y) (p n : ℤ) :
    ambientClass X.filtration p n ≫ HomologicalComplex.homologyMap f.hom n =
      closedMap f p n ≫ ambientClass Y.filtration p n := by
  dsimp only [ambientClass]
  rw [Category.assoc, ← cohomologyStepMap_arrow, ← Category.assoc,
    closedClass_naturality, Category.assoc]

theorem row_naturality {X Y : FilteredComplex A} (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (D' : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D D')
    (hF : DegreewiseFinite X.filtration) (hQ : FirstQuadrant X.filtration D)
    (E : EdgeData X.filtration D) (E' : EdgeData Y.filtration D') (n : ℤ) (hn : 0 ≤ n) :
    M.map 2 n n ≫ E'.row n hn = E.row n hn ≫ HomologicalComplex.homologyMap f.hom n := by
  have := row_closedToPage_epi X.filtration D hF hQ n
  apply (cancel_epi (closedToPage X.filtration D 2 n n)).1
  rw [← Category.assoc, closedToPage_naturality, Category.assoc, E'.row_formula]
  rw [← Category.assoc (closedToPage X.filtration D 2 n n) (E.row n hn)
    (HomologicalComplex.homologyMap f.hom n), E.row_formula, ambientClass_naturality]

theorem column_naturality {X Y : FilteredComplex A} (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (D' : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D D')
    (hF : DegreewiseFinite X.filtration) (hQ : FirstQuadrant X.filtration D)
    (E : EdgeData X.filtration D) (E' : EdgeData Y.filtration D') (n : ℤ) (hn : 0 ≤ n) :
    HomologicalComplex.homologyMap f.hom n ≫ E'.column n hn = E.column n hn ≫ M.map 2 0 n := by
  have : IsIso (cohomologyPiece X.filtration 0 n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (cohomologyPiece_zero_eq_top X.filtration D hF hQ n)
  have : Epi (ambientClass X.filtration 0 n) := by dsimp only [ambientClass]; infer_instance
  apply (cancel_epi (ambientClass X.filtration 0 n)).1
  rw [← Category.assoc, ambientClass_naturality, Category.assoc, E'.column_formula,
    ← Category.assoc, E.column_formula, closedToPage_naturality]

/-- If both adjacent differentials vanish, passage to the next page is an
isomorphism, with the same closed-representative formula. -/
theorem iso_step (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr (p-r) (n-1) = 0)
    (hg : D.differential r hr p n = 0) :
    ∃ e : PageCohomology.object F D r p n ≅ PageCohomology.object F D (r+1) p n,
      closedToPage F D r p n ≫ e.hom = closedToPage F D (r+1) p n := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, p = a+r := ⟨p-r, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b+1 := ⟨n-1, by omega⟩
  subst p; subst n
  rw [show a+r-r=a by omega, show b+1-1=b by omega] at hf
  let S := PageCohomology.shortComplex F D r hr a b
  have : IsIso S.iCycles := S.isIso_iCycles hg
  have : IsIso S.homologyπ := S.isIso_homologyπ hf
  have : IsIso (nextQuotient F D r hr a b hg) := by dsimp only [nextQuotient]; infer_instance
  exact ⟨asIso (nextQuotient F D r hr a b hg), closedToPage_nextQuotient F D r hr a b hg⟩

/-- Iteration of the canonical stationary page identifications. -/
theorem iso_comparison (s : ℤ) (hs : 0 ≤ s) (p n : ℤ)
    (hf : ∀ t (ht : s ≤ t), D.differential t (by omega) (p-t) (n-1) = 0)
    (hg : ∀ t (ht : s ≤ t), D.differential t (by omega) p n = 0)
    (r : ℤ) (hr : s ≤ r) :
    ∃ e : PageCohomology.object F D s p n ≅ PageCohomology.object F D r p n,
      closedToPage F D s p n ≫ e.hom = closedToPage F D r p n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = s+k := ⟨(r-s).toNat, by omega⟩
  clear hr
  induction k with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    exact ⟨Iso.refl _, by simp⟩
  | succ k ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := iso_step F D (s+k) (by omega) p n (hf _ (by omega)) (hg _ (by omega))
    rw [show (s+(↑(k+1):ℤ))=(s+k)+1 by omega]
    exact ⟨e.trans e', by simp only [Iso.trans_hom, ← Category.assoc, he, he']⟩

/-- When all subsequent incoming and outgoing maps vanish, this page itself
has the canonical limiting identification with graded cohomology. -/
def stationaryLimit (hF : DegreewiseFinite F) (s : ℤ) (hs : 0 ≤ s) (p n : ℤ)
    (hf : ∀ t (ht : s ≤ t), D.differential t (by omega) (p-t) (n-1) = 0)
    (hg : ∀ t (ht : s ≤ t), D.differential t (by omega) p n = 0) : LimitIso F D s p n := by
  classical
  apply Classical.choice
  obtain ⟨R, hR, hstab⟩ := uniform_stabilization F hF n
  let r := max s R
  obtain ⟨e, he⟩ := iso_comparison F D s hs p n hf hg r (le_max_left _ _)
  let L := limitIso F D r p n (hstab r (le_max_right _ _) p)
  exact ⟨⟨e.trans L.iso, by rw [Iso.trans_hom, ← Category.assoc, he, L.representative_formula]⟩⟩

/-- The (1,0) term is stable already on E₂. -/
def E10_limit (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) : LimitIso F D 2 1 1 :=
  stationaryLimit F D hF 2 (by omega) 1 1
    (fun t ht => E10_incoming_zero F D hQ t ht)
    (fun t ht => row_differential_zero F D hQ t ht 1)

/-- The (0,1) term is stable after d₂. -/
def E01_limit (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) : LimitIso F D 3 0 1 :=
  stationaryLimit F D hF 3 (by omega) 0 1
    (fun t ht => by rw [zero_sub]; exact column_incoming_zero F D hQ t (by omega) 1)
    (fun t ht => E01_outgoing_zero F D hQ t ht)

/-- The (2,0) term is stable after d₂. -/
def E20_limit (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) : LimitIso F D 3 2 2 :=
  stationaryLimit F D hF 3 (by omega) 2 2
    (fun t ht => E20_incoming_zero F D hQ t ht)
    (fun t ht => row_differential_zero F D hQ t (by omega) 2)

/-- The next-page inclusion has image equal to the outgoing kernel when
there are no incoming boundaries. -/
theorem nextInclusion_exact (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr p n = 0) :
    ∃ h : nextInclusion F D r hr p n hf ≫ D.differential r hr (p+r) (n+1) = 0,
      (ShortComplex.mk (nextInclusion F D r hr p n hf)
        (D.differential r hr (p+r) (n+1)) h).Exact := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.homologyπ := S.isIso_homologyπ hf
  let a := ((PageCohomology.data F D).nextIso r hr p n).hom ≫ inv S.homologyπ
  have ha : IsIso a := by dsimp only [a]; infer_instance
  have hz : nextInclusion F D r hr p n hf ≫ S.g = 0 := by
    dsimp only [nextInclusion]
    simp [S, Category.assoc]
  refine ⟨hz, ?_⟩
  let T := ShortComplex.mk (nextInclusion F D r hr p n hf) S.g hz
  let U := ShortComplex.mk S.iCycles S.g S.iCycles_g
  let φ : T ⟶ U := { τ₁ := a, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp [T, U, a, nextInclusion, S, Category.assoc] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (U.exact_of_f_is_kernel S.cyclesIsKernel)

/-- The next-page quotient has kernel equal to the incoming image when
there is no outgoing differential. -/
theorem nextQuotient_exact (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hg : D.differential r hr (p+r) (n+1) = 0) :
    ∃ h : D.differential r hr p n ≫ nextQuotient F D r hr p n hg = 0,
      (ShortComplex.mk (D.differential r hr p n)
        (nextQuotient F D r hr p n hg) h).Exact := by
  let S := PageCohomology.shortComplex F D r hr p n
  have : IsIso S.iCycles := S.isIso_iCycles hg
  have hfi : S.f ≫ inv S.iCycles = S.toCycles := by
    apply (cancel_mono S.iCycles).1
    simp
  have hz : S.f ≫ nextQuotient F D r hr p n hg = 0 := by
    dsimp only [nextQuotient]
    rw [← Category.assoc, ← Category.assoc, hfi]
    simp [S, Category.assoc]
  refine ⟨hz, ?_⟩
  let T := ShortComplex.mk S.f (nextQuotient F D r hr p n hg) hz
  let U := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  let φ : T ⟶ U := {
    τ₁ := 𝟙 _, τ₂ := inv S.iCycles,
    τ₃ := ((PageCohomology.data F D).nextIso r hr p n).hom,
    comm₁₂ := by simp [T, U],
    comm₂₃ := by simp [T, U, nextQuotient, S, Category.assoc] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (U.exact_of_g_is_cokernel S.homologyIsCokernel)

/-- Centered next-page inclusions, including their exactness property. -/
theorem inclusion_step_exact (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hf : D.differential r hr (p-r) (n-1) = 0) :
    ∃ i : PageCohomology.object F D (r+1) p n ⟶ PageCohomology.object F D r p n,
      Mono i ∧ (closedToPage F D (r+1) p n ≫ i = closedToPage F D r p n) ∧
      ∃ h : i ≫ D.differential r hr p n = 0,
        (ShortComplex.mk i (D.differential r hr p n) h).Exact := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, p = a+r := ⟨p-r, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b+1 := ⟨n-1, by omega⟩
  subst p; subst n
  rw [show a+r-r=a by omega, show b+1-1=b by omega] at hf
  obtain ⟨hz, hex⟩ := nextInclusion_exact F D r hr a b hf
  exact ⟨nextInclusion F D r hr a b hf, inferInstance,
    closedToPage_nextInclusion F D r hr a b hf, hz, hex⟩

/-- The first row edge is the inclusion of F¹H¹ under its limiting
isomorphism, so it is monic. -/
theorem first_row_mono (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D)
    (E : EdgeData F D) : Mono (E.row 1 (by omega)) := by
  let L := E10_limit F D hF hQ
  let π := cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F 1 1))
  have hπ : IsIso π := cokernel.π_of_zero
    (ofLE_zero_of_eq_bot _ (cohomologyPiece_above_eq_bot F D hF hQ 1))
  have hrow : E.row 1 (by omega) = (L.iso.hom ≫ inv π) ≫ (cohomologyPiece F 1 1).arrow := by
    have := row_closedToPage_epi F D hF hQ 1
    apply (cancel_epi (closedToPage F D 2 1 1)).1
    rw [E.row_formula]
    symm
    simp only [Category.assoc]
    rw [reassoc_of% L.representative_formula]
    simp only [gradedClass, π, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [hrow]
  infer_instance

/-- The degree-one column edge surjects onto E₃⁰¹ and then includes it in E₂⁰¹. -/
theorem column_one_factor (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D)
    (E : EdgeData F D)
    (i : PageCohomology.object F D 3 0 1 ⟶ PageCohomology.object F D 2 0 1)
    (hif : closedToPage F D 3 0 1 ≫ i = closedToPage F D 2 0 1) :
    ∃ m : K.homology 1 ⟶ PageCohomology.object F D 3 0 1,
      Epi m ∧ E.column 1 (by omega) = m ≫ i := by
  let L := E01_limit F D hF hQ
  let π := cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F 0 1))
  have h0 : IsIso (cohomologyPiece F 0 1).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (cohomologyPiece_zero_eq_top F D hF hQ 1)
  let m := inv (cohomologyPiece F 0 1).arrow ≫ π ≫ L.iso.inv
  have hm : Epi m := by dsimp only [m]; infer_instance
  have hmf : ambientClass F 0 1 ≫ m = closedToPage F D 3 0 1 := by
    dsimp only [m, ambientClass]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    change closedClass F 0 1 ≫ π ≫ L.iso.inv = _
    rw [← Category.assoc]
    change gradedClass F 0 1 ≫ L.iso.inv = _
    rw [← L.representative_formula]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨m, hm, ?_⟩
  have : Epi (ambientClass F 0 1) := by dsimp only [ambientClass]; infer_instance
  apply (cancel_epi (ambientClass F 0 1)).1
  rw [E.column_formula, ← Category.assoc, hmf]
  exact hif.symm

/-- The degree-two row edge is the quotient onto E₃²⁰ followed by the
inclusion of F²H² under its limiting identification. -/
theorem row_two_factor (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D)
    (E : EdgeData F D)
    (q : PageCohomology.object F D 2 2 2 ⟶ PageCohomology.object F D 3 2 2)
    (hqf : closedToPage F D 2 2 2 ≫ q = closedToPage F D 3 2 2) :
    ∃ m : PageCohomology.object F D 3 2 2 ⟶ K.homology 2,
      Mono m ∧ E.row 2 (by omega) = q ≫ m := by
  let L := E20_limit F D hF hQ
  let π := cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F 2 2))
  have hπ : IsIso π := cokernel.π_of_zero
    (ofLE_zero_of_eq_bot _ (cohomologyPiece_above_eq_bot F D hF hQ 2))
  let m := (L.iso.hom ≫ inv π) ≫ (cohomologyPiece F 2 2).arrow
  have hm : Mono m := by dsimp only [m]; infer_instance
  have hmf : closedToPage F D 3 2 2 ≫ m = ambientClass F 2 2 := by
    dsimp only [m]
    simp only [Category.assoc]
    rw [reassoc_of% L.representative_formula]
    simp only [gradedClass, π, Category.assoc, IsIso.hom_inv_id_assoc]
  refine ⟨m, hm, ?_⟩
  have := row_closedToPage_epi F D hF hQ 2
  apply (cancel_epi (closedToPage F D 2 2 2)).1
  rw [E.row_formula, ← Category.assoc, hqf, hmf]

/-- Exactness at E₂⁰¹ is the kernel description of the next-page inclusion. -/
theorem exact_at_E01 (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) (E : EdgeData F D) :
    ∃ h : E.column 1 (by omega) ≫ transgression F D = 0,
      (ShortComplex.mk (E.column 1 (by omega)) (transgression F D) h).Exact := by
  have hf : D.differential 2 (by omega) (0-2) (1-1) = 0 := by
    rw [show (0-2:ℤ) = -2 by decide, show (1-1:ℤ) = 0 by decide]
    exact column_incoming_zero F D hQ 2 (by omega) 1
  have hi := inclusion_step_exact F D 2 (by omega) 0 1 hf
  rw [show (2+1:ℤ) = 3 by decide] at hi
  obtain ⟨i, hi, hif, hz, hex⟩ := hi
  obtain ⟨m, hm, hcf⟩ := column_one_factor F D hF hQ E i hif
  have hcd : E.column 1 (by omega) ≫ transgression F D = 0 := by
    rw [hcf, Category.assoc, hz, comp_zero]
  refine ⟨hcd, ?_⟩
  let T := ShortComplex.mk (E.column 1 (by omega)) (transgression F D) hcd
  let U := ShortComplex.mk i (transgression F D) hz
  let φ : T ⟶ U := {
    τ₁ := m
    τ₂ := 𝟙 _
    τ₃ := 𝟙 _
    comm₁₂ := by simpa only [T, U, Category.id_comp, Category.comp_id] using hcf.symm }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex

/-- Exactness at E₂²⁰ is the cokernel description of the next-page quotient. -/
theorem exact_at_E20 (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) (E : EdgeData F D) :
    ∃ h : transgression F D ≫ E.row 2 (by omega) = 0,
      (ShortComplex.mk (transgression F D) (E.row 2 (by omega)) h).Exact := by
  have hg : D.differential 2 (by omega) (0+2) (1+1) = 0 :=
    row_differential_zero F D hQ 2 (by omega) 2
  obtain ⟨hz, hex⟩ := nextQuotient_exact F D 2 (by omega) 0 1 hg
  have hq : ∃ q : PageCohomology.object F D 2 2 2 ⟶ PageCohomology.object F D 3 2 2,
      Epi q ∧ (closedToPage F D 2 2 2 ≫ q = closedToPage F D 3 2 2) ∧
      ∃ h : transgression F D ≫ q = 0,
        (ShortComplex.mk (transgression F D) q h).Exact :=
    ⟨nextQuotient F D 2 (by omega) 0 1 hg, inferInstance,
      closedToPage_nextQuotient F D 2 (by omega) 0 1 hg, hz, hex⟩
  obtain ⟨q, hq, hqf, hz, hex⟩ := hq
  obtain ⟨m, hm, hrf⟩ := row_two_factor F D hF hQ E q hqf
  have hdr : transgression F D ≫ E.row 2 (by omega) = 0 := by
    rw [hrf, ← Category.assoc, hz, zero_comp]
  refine ⟨hdr, ?_⟩
  let T := ShortComplex.mk (transgression F D) q hz
  let U := ShortComplex.mk (transgression F D) (E.row 2 (by omega)) hdr
  let φ : T ⟶ U := {
    τ₁ := 𝟙 _
    τ₂ := 𝟙 _
    τ₃ := m
    comm₂₃ := by simpa only [T, U, Category.id_comp] using hrf }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex

/-- All exactness statements, with the original row and column edge maps. -/
theorem fiveTermData (hF : DegreewiseFinite F) (hQ : FirstQuadrant F D) (E : EdgeData F D) :
    FiveTermData F D E := by
  have h : imageSubobject (E.row 1 (by omega)) = kernelSubobject (E.column 1 (by omega)) := by
    rw [E.row_image, E.column_kernel]
  have hrc : E.row 1 (by omega) ≫ E.column 1 (by omega) = 0 := by
    rw [← imageSubobject_arrow_comp (E.row 1 (by omega)),
      ← Subobject.ofLE_arrow h.le]
    simp only [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  obtain ⟨hcd, hE01⟩ := exact_at_E01 F D hF hQ E
  obtain ⟨hdr, hE20⟩ := exact_at_E20 F D hF hQ E
  exact {
    row_mono := first_row_mono F D hF hQ E
    row_column := hrc
    column_d := hcd
    d_row := hdr
    exact_H1 := (ShortComplex.exact_iff_image_eq_kernel _).2 h
    exact_E01 := hE01
    exact_E20 := hE20 }

/-- A simultaneous system of canonical natural edges and five-term exact sequences. -/
def system (A : Type u) [Category.{v} A] [Abelian A] : System A where
  edges X D hF hQ := edgeData X.filtration D hF hQ
  five_terms X D hF hQ := fiveTermData X.filtration D hF hQ (edgeData X.filtration D hF hQ)
  row_naturality f D D' M hX _hY hQX _hQY n hn :=
    row_naturality f D D' M hX hQX _ _ n hn
  column_naturality f D D' M hX _hY hQX _hQY n hn :=
    column_naturality f D D' M hX hQX _ _ n hn

end EdgesAndFiveTerms

/-- HA-S05: natural first-quadrant edge maps and the five-term exact sequence,
under exactly the degreewise finite filtration and E₂ quadrant hypotheses. -/
theorem filtered_edges_and_five_terms : S05Specs.FullStatement.{v,u} := by
  intro A _ _
  exact ⟨EdgesAndFiveTerms.system A⟩

end AdvancedHomologicalAlgebra
