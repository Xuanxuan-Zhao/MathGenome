import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.NonzeroSecondDifferential
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.PageCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence

set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace AdvancedHomologicalAlgebra.SecondDifferentialExample
open FilteredPage
universe u
variable (k : Type u) [Field k]

/-- The two basis identifications are isomorphisms. -/
instance basis_isIso (n : ℤ) (hn : n = 1 ∨ n = 2) : IsIso (basis k n hn) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro x y h
    exact congrArg Subtype.val h
  · intro x
    exact ⟨x.val, Subtype.ext rfl⟩

theorem term_zero (n : ℤ) (hn : ¬ (n = 1 ∨ n = 2)) : IsZero ((complex k).X n) := by
  change IsZero (ModuleCat.of k (term k n))
  unfold term
  rw [ite_eq_right hn]
  exact ModuleCat.isZero_of_subsingleton _

theorem differential_other (i j : ℤ) (h : ¬ (i = 1 ∧ j = 2)) :
    (complex k).d i j = 0 := by
  change differential k i j = 0
  exact dite_eq_right h

@[reassoc]
theorem basis_d : basis k 1 (by simp) ≫ (complex k).d 1 2 = basis k 2 (by simp) := by
  ext x
  rfl

instance main_d_isIso : IsIso ((complex k).d 1 2) := by
  have := basis_d k
  exact IsIso.of_isIso_fac_left this

/-- Away from the two jumps, adjacent filtration steps agree. -/
theorem adjacent_eq (p n : ℤ)
    (h : ¬ ((p = 0 ∧ n = 1) ∨ (p = 2 ∧ n = 2))) :
    (filtration k).piece (p+1) n = (filtration k).piece p n := by
  by_cases hn : n = 1 ∨ n = 2
  · rcases hn with rfl | rfl
    all_goals
      change piece k (p+1) _ = piece k p _
      unfold piece weight
      norm_num
      split_ifs <;> first | rfl | omega
  · have hz := term_zero k n hn
    haveI := Subobject.subsingleton_of_isZero hz
    exact Subsingleton.elim _ _

section General
variable {A : Type*} [Category A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

private theorem toPage_iso (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n)
    (ha : almost F r p n = F.piece p n)
    (hn : F.piece (p+1) n = ⊥)
    (hb : boundaries F r p n = ⊥) : IsIso (toPage F r p n h) := by
  have ht : (F.transition p).f n = 0 := by
    dsimp [Filtration.transition]
    apply IsZero.eq_zero_of_src
    rw [hn]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  have hp : IsIso ((F.projection p).f n) := by
    change IsIso (cokernel.π ((F.transition p).f n))
    rw [ht]
    infer_instance
  have hi : IsIso (Subobject.ofLE _ _ (inf_le_left : almost F r p n ≤ F.piece p n)) :=
    (Subobject.isoOfEq _ _ ha).isIso_hom
  have hg : IsIso (gradedRepresentative F p n (almost F r p n) inf_le_left) := by
    dsimp [gradedRepresentative]
    infer_instance
  have hm : Mono (factorThruImageSubobject
      (gradedRepresentative F p n (almost F r p n) inf_le_left)) :=
    mono_of_mono_fac (imageSubobject_arrow_comp _)
  have hf : IsIso (factorThruImageSubobject
      (gradedRepresentative F p n (almost F r p n) inf_le_left)) :=
    isIso_of_mono_of_epi _
  have hz : Subobject.ofLE _ _ h = 0 := by
    apply IsZero.eq_zero_of_src
    rw [hb]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  dsimp only [toPage]
  have : IsIso (cokernel.π (Subobject.ofLE _ _ h)) := by rw [hz]; infer_instance
  infer_instance

private theorem page_zero_of_almost_bot (r p n : ℤ)
    (h : boundaries F r p n ≤ cycles F r p n) (ha : almost F r p n = ⊥) :
    IsZero (page F r p n h) := by
  apply IsZero.of_epi (toPage F r p n h)
  rw [ha]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

end General

/-- The almost-cycle subobject at `a` is the whole term through page 2. -/
theorem almost_a (r : ℤ) (hr : r ≤ 2) : almost (filtration k) r 0 1 = ⊤ := by
  dsimp only [almost]
  rw [show (filtration k).piece 0 1 = ⊤ by rfl,
    show (filtration k).piece (0+r) (1+1) = ⊤ by
      change piece k (0+r) 2 = ⊤
      apply ite_eq_left
      simpa [weight] using hr,
    Subobject.pullback_top, inf_top_eq]

/-- The differential out of degree 2 is zero, so `b` is always an almost cycle. -/
theorem almost_b (r : ℤ) : almost (filtration k) r 2 2 = ⊤ := by
  dsimp only [almost]
  rw [show (filtration k).piece 2 2 = ⊤ by rfl, top_inf_eq]
  apply top_unique
  apply Subobject.le_of_factors
  apply pullback_factors
  rw [differential_other k 2 (2+1) (by omega), comp_zero]
  exact Subobject.factors_zero

private theorem boundaries_of_source_zero (r p n : ℤ)
    (hz : (boundarySource (filtration k) r p n).arrow = 0) :
    boundaries (filtration k) r p n = ⊥ := by
  have hi := IsZero.of_mono_eq_zero _ hz
  have h : gradedRepresentative (filtration k) p n
      (boundarySource (filtration k) r p n) inf_le_left = 0 := hi.eq_zero_of_src _
  simp only [boundaries, h, imageSubobject_zero]

theorem boundaries_a (r : ℤ) : boundaries (filtration k) r 0 1 = ⊥ := by
  apply boundaries_of_source_zero
  have h : boundarySource (filtration k) r 0 1 = ⊥ := by
    dsimp only [boundarySource]
    simp only [differential_other k (1-1) 1 (by omega), comp_zero, imageSubobject_zero, inf_bot_eq]
  rw [h, Subobject.bot_arrow]

theorem boundaries_b (r : ℤ) (hr : r ≤ 2) : boundaries (filtration k) r 2 2 = ⊥ := by
  apply boundaries_of_source_zero
  have h : boundarySource (filtration k) r 2 2 = ⊥ := by
    dsimp only [boundarySource]
    have hp : (filtration k).piece (2-r+1) (2-1) = ⊥ := by
      change piece k (2-r+1) 1 = ⊥
      apply ite_eq_right
      simp only [weight]
      norm_num
      omega
    have hz : ((filtration k).piece (2-r+1) (2-1)).arrow = 0 := by
      rw [hp, Subobject.bot_arrow]
    simp only [hz, zero_comp, imageSubobject_zero, inf_bot_eq]
  rw [h, Subobject.bot_arrow]

private def basisLift (r p n : ℤ) (hn : n = 1 ∨ n = 2)
    (ha : almost (filtration k) r p n = ⊤) :
    ModuleCat.of k k ⟶ (almost (filtration k) r p n : ModuleCat k) :=
  haveI : IsIso (almost (filtration k) r p n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 ha
  basis k n hn ≫ inv (almost (filtration k) r p n).arrow

@[reassoc (attr := simp)]
private theorem basisLift_arrow (r p n : ℤ) (hn : n = 1 ∨ n = 2)
    (ha : almost (filtration k) r p n = ⊤) :
    basisLift k r p n hn ha ≫ (almost (filtration k) r p n).arrow = basis k n hn := by
  haveI : IsIso (almost (filtration k) r p n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 ha
  simp [basisLift]

private instance basisLift_isIso (r p n : ℤ) (hn : n = 1 ∨ n = 2)
    (ha : almost (filtration k) r p n = ⊤) : IsIso (basisLift k r p n hn ha) := by
  haveI : IsIso (almost (filtration k) r p n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 ha
  dsimp only [basisLift]
  infer_instance


variable (D : F03Specs.PageData (filtration k))

private def aIso (r : ℤ) (hr : r ≤ 2) :
    ModuleCat.of k k ≅ PageCohomology.object (filtration k) D r 0 1 := by
  haveI : IsIso (toPage (filtration k) r 0 1 (D.containment r 0 1)) := by
    apply toPage_iso
    · simpa only [show (filtration k).piece 0 1 = ⊤ by rfl] using almost_a k r hr
    · rfl
    · exact boundaries_a k r
  exact asIso (basisLift k r 0 1 (by simp) (almost_a k r hr) ≫
    toPage (filtration k) r 0 1 (D.containment r 0 1))

private def bIso (r : ℤ) (hr : r ≤ 2) :
    ModuleCat.of k k ≅ PageCohomology.object (filtration k) D r 2 2 := by
  haveI : IsIso (toPage (filtration k) r 2 2 (D.containment r 2 2)) := by
    apply toPage_iso
    · simpa only [show (filtration k).piece 2 2 = ⊤ by rfl] using almost_b k r
    · rfl
    · exact boundaries_b k r hr
  exact asIso (basisLift k r 2 2 (by simp) (almost_b k r) ≫
    toPage (filtration k) r 2 2 (D.containment r 2 2))

/-- In every page, a position without a jump in the filtration vanishes. -/
theorem page_zero_off_support (r p n : ℤ)
    (h : ¬ ((p = 0 ∧ n = 1) ∨ (p = 2 ∧ n = 2))) :
    IsZero (PageCohomology.object (filtration k) D r p n) := by
  apply IsZero.of_epi_eq_zero (toPage (filtration k) r p n (D.containment r p n))
  have hg := FiniteFiltrationConvergence.gradedRepresentative_eq_zero_of_eq
    (filtration k) p n (adjacent_eq k p n h) (almost (filtration k) r p n) inf_le_left
  simpa only [Category.id_comp] using
    toPage_zero_of_graded_zero (filtration k) r p n (D.containment r p n) (𝟙 _)
      (by simpa only [Category.id_comp] using hg)

/-- Degree reasons kill both early differentials. -/
theorem early_differentials (r : ℤ) (hr : 0 ≤ r) (hs : r ≤ 1) (p n : ℤ) :
    D.differential r hr p n = 0 := by
  by_cases h : (p = 0 ∧ n = 1) ∨ (p = 2 ∧ n = 2)
  · apply IsZero.eq_zero_of_tgt (page_zero_off_support k D r (p+r) (n+1) (by omega))
  · exact (page_zero_off_support k D r p n h).eq_zero_of_src _

section
-- Keep chosen categorical limits opaque while matching numeric indices.
set_option allowUnsafeReducibility true
attribute [local irreducible] toPage basisLift page cycles boundaries almost
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem second_formula :
    (aIso k D 2 (by omega)).hom ≫ D.differential 2 (by omega) 0 1 =
      (bIso k D 2 (by omega)).hom := by
  have hb : basisLift k 2 0 1 (by simp) (almost_a k 2 (by omega)) ≫
      D.restriction 2 (by omega) 0 1 =
        basisLift k 2 2 2 (by simp) (almost_b k 2) := by
    apply (cancel_mono (almost (filtration k) 2 2 2).arrow).1
    have hd : D.restriction 2 (by omega) 0 1 ≫ (almost (filtration k) 2 2 2).arrow =
        (almost (filtration k) 2 0 1).arrow ≫ (complex k).d 1 2 :=
      D.restriction_arrow 2 (by omega) 0 1
    rw [Category.assoc, hd, basisLift_arrow_assoc, basisLift_arrow]
    exact basis_d k
  dsimp only [aIso, bIso, asIso_hom]
  rw [Category.assoc, D.representative_formula, ← Category.assoc, hb]
  rfl
end

private theorem third_a : IsZero (PageCohomology.object (filtration k) D 3 0 1) := by
  apply page_zero_of_almost_bot
  rw [← Subobject.mk_arrow (almost (filtration k) 3 0 1)]
  apply Subobject.mk_eq_bot_iff_zero.mpr
  have h : (almost (filtration k) 3 0 1).arrow ≫ (complex k).d 1 2 = 0 := by
    have hh := (Subobject.isPullback ((complex k).d 1 (1+1))
      ((filtration k).piece (0+3) (1+1))).w
    have hq : (filtration k).piece (0+3) (1+1) = ⊥ := by rfl
    have hz : ((filtration k).piece (0+3) (1+1)).arrow = 0 := by
      rw [hq, Subobject.bot_arrow]
    have hh' : ((Subobject.pullback ((complex k).d 1 (1+1))).obj
      ((filtration k).piece (0+3) (1+1))).arrow ≫ (complex k).d 1 (1+1) = 0 := by
      rw [← hh, hz, comp_zero]
    change (almost (filtration k) 3 0 1).arrow ≫ (complex k).d 1 (1+1) = 0
    rw [← Subobject.ofLE_arrow (inf_le_right : almost (filtration k) 3 0 1 ≤
      (Subobject.pullback ((complex k).d 1 (1+1))).obj ((filtration k).piece (0+3) (1+1))),
      Category.assoc, hh', comp_zero]
  exact (cancel_mono ((complex k).d 1 2)).1 (by simpa using h)

private theorem third_b : IsZero (PageCohomology.object (filtration k) D 3 2 2) := by
  have h : boundarySource (filtration k) 3 2 2 = ⊤ := by
    have hi : IsIso ((filtration k).piece (2-3+1) (2-1)).arrow := by
      apply (Subobject.isIso_arrow_iff_eq_top _).2
      rfl
    haveI : IsIso ((complex k).d (2-1) 2) := main_d_isIso k
    have hm : imageSubobject (((filtration k).piece (2-3+1) (2-1)).arrow ≫
        (complex k).d (2-1) 2) = ⊤ := by
      rw [imageSubobject_mono]
      exact Subobject.mk_eq_top_of_isIso _
    dsimp only [boundarySource]
    rw [hm, inf_top_eq]
    rfl
  apply IsZero.of_epi_eq_zero (toPage (filtration k) 3 2 2 (D.containment 3 2 2))
  simpa only [Category.id_comp] using
    toPage_zero_of_boundary (filtration k) 3 2 2 (D.containment 3 2 2) (𝟙 _)
      (by rw [h]; exact Subobject.top_factors _)

/-- The entire third page vanishes. -/
theorem third_page (p n : ℤ) : IsZero (PageCohomology.object (filtration k) D 3 p n) := by
  by_cases h : (p = 0 ∧ n = 1) ∨ (p = 2 ∧ n = 2)
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact third_a k D
    · exact third_b k D
  · exact page_zero_off_support k D 3 p n h

/-- The identity differential makes the original two-term complex acyclic. -/
theorem acyclic (n : ℤ) : IsZero ((complex k).homology n) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  by_cases h : n = 1 ∨ n = 2
  · rcases h with rfl | rfl
    · rw [(complex k).exactAt_iff' 0 1 2 (by norm_num) (by norm_num)]
      apply (ShortComplex.exact_iff_mono _ ?_).2
      · change Mono ((complex k).d 1 2)
        infer_instance
      · exact differential_other k 0 1 (by omega)
    · rw [(complex k).exactAt_iff' 1 2 3 (by norm_num) (by norm_num)]
      apply (ShortComplex.exact_iff_epi _ ?_).2
      · change Epi ((complex k).d 1 2)
        infer_instance
      · exact differential_other k 2 3 (by omega)
  · exact HomologicalComplex.ExactAt.of_isZero (term_zero k n h)

/-- The example has a globally bounded filtration, hence the required degreewise finiteness. -/
theorem finite : FiniteFiltrationConvergence.DegreewiseFinite (filtration k) := by
  intro n
  refine ⟨0, 3, ?_, ?_⟩
  · intro p hp
    change piece k p n = ⊤
    apply ite_eq_left
    unfold weight
    split_ifs <;> omega
  · intro p hp
    change piece k p n = ⊥
    apply ite_eq_right
    unfold weight
    split_ifs <;> omega


/-- The complete page calculation, with its canonical representatives. -/
def calculation : Calculation k D where
  aLift r _ hs := basisLift k r 0 1 (by simp) (almost_a k r hs)
  aLift_arrow r _ hs := basisLift_arrow k r 0 1 (by simp) (almost_a k r hs)
  bLift r _ _ := basisLift k r 2 2 (by simp) (almost_b k r)
  bLift_arrow r _ _ := basisLift_arrow k r 2 2 (by simp) (almost_b k r)
  aIso r _ hs := aIso k D r hs
  aIso_hom _ _ _ := rfl
  bIso r _ hs := bIso k D r hs
  bIso_hom _ _ _ := rfl
  support r _ _ p n h := page_zero_off_support k D r p n h
  early_differentials := early_differentials k D
  second_formula := second_formula k D
  second_isIso := IsIso.of_isIso_fac_left (second_formula k D)
  third_page := third_page k D
  acyclic := acyclic k
  finite := finite k

end AdvancedHomologicalAlgebra.SecondDifferentialExample

namespace AdvancedHomologicalAlgebra
/-- HA-S05's explicit nonzero `d₂`, on the actual pages of the filtered complex. -/
theorem nonzero_second_differential : S05ExampleSpecs.FullStatement.{u} := by
  intro k _ D
  exact ⟨SecondDifferentialExample.calculation k D⟩
end AdvancedHomologicalAlgebra

