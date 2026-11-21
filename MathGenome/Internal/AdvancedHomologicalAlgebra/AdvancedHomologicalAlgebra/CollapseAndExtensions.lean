import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CollapseAndExtensions

/-! HA-S04: collapse, canonical target identifications, and extensions. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace CollapseAndExtensions
open FilteredPage PageCohomology FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)

/-- Vanishing in a bidegree persists on every later page. -/
theorem support_later (C : PageCohomology.Data F D) (s : ℤ) (hs : 0 ≤ s)
    (index : ℤ → ℤ)
    (h : ∀ p n, p ≠ index n → IsZero (object F D s p n)) :
    ∀ r, s ≤ r → ∀ p n, p ≠ index n → IsZero (object F D r p n) := by
  intro r hr
  induction r, hr using Int.leInduction with
  | base => exact h
  | succ r hr ih =>
    intro p n hp
    have hr0 : 0 ≤ r := hs.trans hr
    have hz := (shortComplex F D r hr0 (p-r) (n-1)).isZero_homology_of_isZero_X₂
      (by simpa only [shortComplex, sub_add_cancel] using ih p n hp)
    have hi := C.nextIso r hr0 (p-r) (n-1)
    have hz' := IsZero.of_iso hz hi
    simpa only [sub_add_cancel] using hz'

/-- The bidegree shift cannot join two terms on the same supported line. -/
theorem differential_zero_of_support (r : ℤ) (hr : 0 ≤ r) (index : ℤ → ℤ)
    (h : ∀ p n, p ≠ index n → IsZero (object F D r p n))
    (shift : ∀ n, index n + r ≠ index (n+1)) (p n : ℤ) :
    D.differential r hr p n = 0 := by
  by_cases hp : p = index n
  · exact (h (p+r) (n+1) (by simpa only [hp] using shift n)).eq_of_tgt _ _
  · exact (h p n hp).eq_of_src _ _

/-- With both differentials zero, the next-page identification is an
isomorphism to the current page, specified by inclusion of representatives. -/
theorem stationary_of_zero (C : PageCohomology.Data F D) (r : ℤ) (hr : 0 ≤ r)
    (hd : ∀ p n, D.differential r hr p n = 0) :
    ∀ p n, Nonempty (StationaryStep F D r p n) := by
  suffices h : ∀ p n, Nonempty (StationaryStep F D r (p+r) (n+1)) by
    intro p n
    simpa only [sub_add_cancel] using h (p-r) (n-1)
  intro p n
  let S := shortComplex F D r hr p n
  have hf : S.f = 0 := hd p n
  have hg : S.g = 0 := hd (p+r) (n+1)
  let e := C.nextIso r hr p n ≪≫ (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoX₂ hg
  refine ⟨⟨e, ?_⟩⟩
  dsimp only [e, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, C.nextIso_formula]
  simp only [Category.assoc]
  change S.liftCycles _ _ ≫ S.homologyπ ≫ (S.asIsoHomologyπ hf).inv ≫ S.iCycles = _
  rw [← Category.assoc S.homologyπ, S.homologyπ_comp_asIsoHomologyπ_inv,
    Category.id_comp]
  exact S.liftCycles_i _ _

/-- Every inclusion of closed representatives is compatible with a stationary
transition. This equation will fix the limiting identification. -/
theorem closed_stationary (r p n : ℤ) (T : StationaryStep F D r p n) :
    closedToPage F D (r+1) p n ≫ T.iso.hom = closedToPage F D r p n := by
  dsimp only [closedToPage]
  rw [Category.assoc, T.representative_formula]
  dsimp only [nextRepresentative]
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE]

/-- Iterate stationary transitions from a late page back to the given page. -/
theorem stationary_comparison (s : ℤ)
    (h : ∀ r, s ≤ r → ∀ p n, Nonempty (StationaryStep F D r p n)) :
    ∀ r, s ≤ r → ∀ p n, ∃ e : object F D r p n ≅ object F D s p n,
      closedToPage F D r p n ≫ e.hom = closedToPage F D s p n := by
  intro r hr
  induction r, hr using Int.leInduction with
  | base => intro p n; exact ⟨Iso.refl _, Category.comp_id _⟩
  | succ r hr ih =>
    intro p n
    obtain ⟨T⟩ := h r hr p n
    obtain ⟨e, he⟩ := ih p n
    refine ⟨T.iso ≪≫ e, ?_⟩
    simp only [Iso.trans_hom, ← Category.assoc, closed_stationary, he]

/-- The stationary initial page is canonically the associated graded target.
Degreewise finiteness is used only to compare to one sufficiently late page. -/
theorem collapsed_limit (hF : DegreewiseFinite F) (s : ℤ)
    (h : ∀ r, s ≤ r → ∀ p n, Nonempty (StationaryStep F D r p n)) (p n : ℤ) :
    Nonempty (LimitIso F D s p n) := by
  obtain ⟨R, hR, hstab⟩ := uniform_stabilization F hF n
  let r := max s R
  have hsr : s ≤ r := le_max_left _ _
  have hRr : R ≤ r := le_max_right _ _
  let L := limitIso F D r p n (hstab r hRr p)
  obtain ⟨e, he⟩ := stationary_comparison F D s h r hsr p n
  refine ⟨⟨e.symm ≪≫ L.iso, ?_⟩⟩
  have hh : closedToPage F D s p n ≫ e.inv = closedToPage F D r p n := by
    rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  simpa only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hh] using L.representative_formula

/-- The ordinary step/quotient short exact sequence of the actual cohomology
filtration. -/
def gradedSequence (p n : ℤ) : ShortComplex A :=
  ShortComplex.mk (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))
    (cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)))
    (cokernel.condition _)

theorem gradedSequence_shortExact (p n : ℤ) : (gradedSequence F p n).ShortExact := by
  dsimp only [gradedSequence]
  exact ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)⟩

/-- A zero graded quotient makes the two actual filtration subobjects equal. -/
theorem step_eq_of_graded_zero (p n : ℤ) (hz : IsZero (gradedCohomology F p n)) :
    cohomologyPiece F (p+1) n = cohomologyPiece F p n := by
  have hi : IsIso (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)) :=
    ((gradedSequence_shortExact F p n).isIso_f_iff).2 hz
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)))
    (Subobject.ofLE_arrow _)

/-- A finite filtration with only one possible nonzero quotient has full
steps below that quotient and zero steps above it. -/
theorem single_piece_bounds (hF : DegreewiseFinite F) (n t : ℤ)
    (hz : ∀ p, p ≠ t → IsZero (gradedCohomology F p n)) :
    (∀ p, p ≤ t → cohomologyPiece F p n = ⊤) ∧
    (∀ p, t < p → cohomologyPiece F p n = ⊥) := by
  obtain ⟨a, b, ha, hb⟩ := (cohomology_filtration F hF).finite n
  constructor
  · intro p hp
    by_cases hpa : p ≤ a
    · exact ha p hpa
    have ht : ∀ q, a ≤ q → q ≤ t → cohomologyPiece F q n = ⊤ := by
      intro q hq
      induction q, hq using Int.leInduction with
      | base => intro _; exact ha a le_rfl
      | succ q hq ih =>
        intro hqt
        rw [step_eq_of_graded_zero F q n (hz q (by omega))]
        exact ih (by omega)
    exact ht p (by omega) hp
  · intro p hp
    by_cases hbp : b ≤ p
    · exact hb p hbp
    have ht : ∀ q, q ≤ b → t < q → cohomologyPiece F q n = ⊥ := by
      intro q hq
      induction q, hq using Int.leInductionDown with
      | base => intro _; exact hb b le_rfl
      | pred q hq ih =>
        intro htq
        have he := step_eq_of_graded_zero F (q-1) n (hz (q-1) (by omega))
        rw [sub_add_cancel] at he
        rw [← he]
        exact ih (by omega)
    exact ht p (by omega) hp

/-- The quotient and inclusion are isomorphisms when they are the only
remaining filtration step. -/
def targetIso (p n : ℤ) (ht : cohomologyPiece F p n = ⊤)
    (hb : cohomologyPiece F (p+1) n = ⊥) : TargetIso F p n := by
  have hi : IsIso (cohomologyPiece F p n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 ht
  have hz : IsZero (cohomologyPiece F (p+1) n : A) := by
    rw [hb]
    exact IsZero.of_iso (isZero_zero A) Subobject.botCoeIsoZero
  have hq : IsIso (cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))) :=
    ((gradedSequence_shortExact F p n).isIso_g_iff).2 hz
  let e := (asIso (cohomologyPiece F p n).arrow).symm ≪≫
    asIso (cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)))
  exact ⟨e, by simp [e]⟩

/-- A generic line-support argument, specialized below to rows and columns. -/
theorem collapse_of_line (hF : DegreewiseFinite F) (s : ℤ) (hs : 0 ≤ s)
    (index : ℤ → ℤ)
    (support : ∀ p n, p ≠ index n → IsZero (object F D s p n))
    (shift : ∀ r, s ≤ r → ∀ n, index n + r ≠ index (n+1)) :
    Nonempty (CollapseData F D s index) := by
  let C := PageCohomology.data F D
  have supp := support_later F D C s hs index support
  have hd : ∀ r (hr : 0 ≤ r), s ≤ r → ∀ p n, D.differential r hr p n = 0 := by
    intro r hr hsr
    exact differential_zero_of_support F D r hr index (supp r hsr) (shift r hsr)
  have stat : ∀ r, s ≤ r → ∀ p n, Nonempty (StationaryStep F D r p n) := by
    intro r hsr
    exact stationary_of_zero F D C r (hs.trans hsr) (hd r (hs.trans hsr) hsr)
  have lim := collapsed_limit F D hF s stat
  have bounds : ∀ n, (∀ p, p ≤ index n → cohomologyPiece F p n = ⊤) ∧
      (∀ p, index n < p → cohomologyPiece F p n = ⊥) := by
    intro n
    apply single_piece_bounds F hF n (index n)
    intro p hp
    obtain ⟨L⟩ := lim p n
    exact IsZero.of_iso (support p n hp) L.iso.symm
  exact ⟨⟨supp, hd, stat, lim, fun p n hp => (bounds n).1 p hp,
    fun p n hp => (bounds n).2 p hp,
    fun n => ⟨targetIso F (index n) n ((bounds n).1 _ le_rfl)
      ((bounds n).2 _ (by omega))⟩⟩⟩

end CollapseAndExtensions

/-- HA-S04 for a single row, with the necessary s ≥ 2 threshold. -/
theorem filtered_row_collapse : S04Specs.RowCollapse.{v,u} := by
  intro A _ _ K F hF D s q hs h
  apply CollapseAndExtensions.collapse_of_line F D hF s (by omega) (fun n => n-q)
  · intro p n hp
    exact h p n (by omega)
  · intro r hr n
    omega

/-- HA-S04 for a single column, including collapse starting at E₁. -/
theorem filtered_column_collapse : S04Specs.ColumnCollapse.{v,u} := by
  intro A _ _ K F hF D s p hs h
  apply CollapseAndExtensions.collapse_of_line F D hF s (by omega) (fun _ => p) h
  intro r hr n
  omega


/-- The stable diagonal pieces are the actual successive quotient extensions. -/
theorem filtered_successive_extensions : S04Specs.Extensions.{v,u} := by
  intro A _ _ K F hF D r p n hr hstab
  let L := FiniteFiltrationConvergence.limitIso F D r p n hstab
  refine ⟨L, ?_⟩
  let e : CollapseAndExtensions.gradedSequence F p n ≅
      CollapseAndExtensions.limitSequence F D r p n L :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) L.iso.symm
      (by simp [CollapseAndExtensions.gradedSequence, CollapseAndExtensions.limitSequence])
      (by simp [CollapseAndExtensions.gradedSequence, CollapseAndExtensions.limitSequence])
  exact ShortComplex.shortExact_of_iso e (CollapseAndExtensions.gradedSequence_shortExact F p n)

/-- Naturality holds for every comparison satisfying the closed-representative
formula; this includes the early collapsed page. -/
theorem collapsed_limit_naturality : S04Specs.LimitNaturality.{v,u} := by
  intro A _ _ X Y f D E M s p n L L'
  have hq : FiniteFiltrationConvergence.closedToPage X.filtration D s p n =
      FiniteFiltrationConvergence.gradedClass X.filtration p n ≫ L.iso.inv := by
    rw [← L.representative_formula, Category.assoc, L.iso.hom_inv_id, Category.comp_id]
  have : Epi (FiniteFiltrationConvergence.closedToPage X.filtration D s p n) := by
    rw [hq]
    infer_instance
  apply (cancel_epi (FiniteFiltrationConvergence.closedToPage X.filtration D s p n)).1
  rw [← Category.assoc, FiniteFiltrationConvergence.closedToPage_naturality,
    Category.assoc, L'.representative_formula, ← Category.assoc,
    L.representative_formula, FiniteFiltrationConvergence.gradedClass_naturality]

/-- The target identification is natural because its quotient and inclusion
square is the defining square for the associated graded cohomology map. -/
theorem collapsed_target_naturality : S04Specs.TargetNaturality.{v,u} := by
  intro A _ _ X Y f p n ht T T'
  have : IsIso (FiniteFiltrationConvergence.cohomologyPiece X.filtration p n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 ht
  apply (cancel_epi (FiniteFiltrationConvergence.cohomologyPiece X.filtration p n).arrow).1
  rw [← Category.assoc, ← FiniteFiltrationConvergence.cohomologyStepMap_arrow,
    Category.assoc, T'.inclusion_quotient, ← Category.assoc, T.inclusion_quotient]
  simp [FiniteFiltrationConvergence.gradedCohomologyMap]

namespace CollapseExample

lemma cyclic_injective : Function.Injective cyclicInjection := by decide
lemma cyclic_surjective : Function.Surjective cyclicProjection := by decide
lemma cyclic_exact : Function.Exact cyclicInjection cyclicProjection := by
  unfold Function.Exact
  decide
lemma split_injective : Function.Injective splitInjection := by decide
lemma split_surjective : Function.Surjective splitProjection := by decide
lemma split_exact : Function.Exact splitInjection splitProjection := by
  unfold Function.Exact
  decide

/-- Every odd residue has order four, whereas twice any element of Z/2 is zero. -/
lemma cyclic_outside_order : ∀ x : ZMod 4, x ∉ cyclicInjection.range → addOrderOf x = 4 := by
  intro x hx
  have hcases : x = 1 ∨ x = 3 := by
    revert hx
    revert x
    decide
  rcases hcases with rfl | rfl
  · exact ZMod.addOrderOf_one 4
  · have h : (3 : ZMod 4) = -1 := by decide
    rw [h, addOrderOf_neg, ZMod.addOrderOf_one]

lemma cyclic_nonsplit : ¬ ∃ t : ZMod 2 →+ ZMod 4,
    cyclicProjection.comp t = AddMonoidHom.id _ := by
  rintro ⟨t, ht⟩
  have hproj : cyclicProjection (t 1) = 1 := DFunLike.congr_fun ht 1
  have hodd : ∀ x : ZMod 4, cyclicProjection x = 1 → 2 • x ≠ 0 := by decide
  apply hodd (t 1) hproj
  have he : (2 : ℕ) • (1 : ZMod 2) = 0 := by decide
  rw [← map_nsmul, he, map_zero]

lemma same_graded_pieces : SameGradedPieces := by
  have hc : cyclicInjection.range = cyclicProjection.ker := by
    ext x
    exact (cyclic_exact x).symm
  have hs : splitInjection.range = splitProjection.ker := by
    ext x
    exact (split_exact x).symm
  refine ⟨⟨AddEquiv.ofBijective cyclicInjection.rangeRestrict
      ⟨(AddMonoidHom.rangeRestrict_injective_iff).2 cyclic_injective,
        AddMonoidHom.rangeRestrict_surjective _⟩⟩,
    ?_, ⟨AddEquiv.ofBijective splitInjection.rangeRestrict
      ⟨(AddMonoidHom.rangeRestrict_injective_iff).2 split_injective,
        AddMonoidHom.rangeRestrict_surjective _⟩⟩, ?_⟩
  · rw [hc]
    exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective cyclicProjection cyclic_surjective⟩
  · rw [hs]
    exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective splitProjection split_surjective⟩

end CollapseExample

/-- The source's two filtrations have the same graded groups and respectively
nonsplit and split quotient extensions. -/
theorem collapse_extension_example : CollapseExample.Statement := by
  open CollapseExample in
    refine ⟨cyclic_injective, cyclic_surjective, cyclic_exact, ?_, cyclic_outside_order,
      cyclic_nonsplit, split_injective, split_surjective, split_exact, ?_, ?_,
      same_graded_pieces⟩
  · decide
  · decide
  · ext x
    rfl

/-- HA-S04, with the full finite-convergence scope, canonical identifications,
successive extension sequences, and the split/nonsplit example. -/
theorem filtered_collapse_and_extensions : S04Specs.FullStatement.{v,u} :=
  ⟨filtered_row_collapse, filtered_column_collapse, filtered_successive_extensions,
    collapsed_limit_naturality, collapsed_target_naturality, collapse_extension_example⟩

end AdvancedHomologicalAlgebra
