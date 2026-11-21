import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BanachSumDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02HilbertSum

/-! Arbitrary normed sums from paper.tex:6234–6269. The native dependent `lp`
construction is identified with bounded finite power subsums and the displayed
root norm. The c₀ carrier has exactly the source finite-level-set condition.
Coordinate maps and truncations are defined for all index sets, including empty
ones. Completeness, density and contractivity are allocated to BanachSums. -/

open scoped ENNReal Classical
noncomputable section
universe u v w
namespace ExpandedFA.Supplements.BanachSumDefinitions

abbrev Space := @Spec.Space
abbrev BoundedProduct := @Spec.BoundedProduct
abbrev PowerSummable := @Spec.PowerSummable
abbrev powerSum := @Spec.powerSum
abbrev VanishesAtInfinity := @Spec.VanishesAtInfinity
abbrev finiteSupport := @Spec.finiteSupport
abbrev ofFiniteSupport := @Spec.ofFiniteSupport
abbrev truncate := @Spec.truncate
abbrev c0Submodule := @Spec.c0Submodule
abbrev C0Space := @Spec.C0Space
abbrev coordinate := @Spec.coordinate
abbrev inclusion := @Spec.inclusion
abbrev c0ToBounded := @Spec.c0ToBounded
abbrev c0Coordinate := @Spec.c0Coordinate
abbrev c0OfFiniteSupport := @Spec.c0OfFiniteSupport
abbrev c0Inclusion := @Spec.c0Inclusion
abbrev c0Truncate := @Spec.c0Truncate
abbrev hilbertIdentification := @Spec.hilbertIdentification

/-- The positivity needed by Mathlib's finite-exponent formulas. -/
private theorem exponent_pos {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    0 < p.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt

theorem memℓp_iff_powerSummable : Spec.memℓp_iff_powerSummable_type := by
  intro I E _ p hp hpt x
  rw [memℓp_gen_iff'' (exponent_pos hp hpt)]
  constructor
  · rintro ⟨C, _, hC⟩
    exact ⟨C, by rintro _ ⟨A, rfl⟩; exact hC A⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_, fun A => hC ⟨A, rfl⟩⟩
    simpa using hC ⟨∅, by simp⟩

theorem exists_coordinates_iff : Spec.exists_coordinates_iff_type := by
  intro I E _ p hp hpt x
  constructor
  · rintro ⟨y, rfl⟩
    exact (memℓp_iff_powerSummable E p hp hpt _).mp (lp.memℓp y)
  · intro hx
    exact ⟨⟨x, (memℓp_iff_powerSummable E p hp hpt x).mpr hx⟩, rfl⟩

theorem norm_rpow_eq_sup : Spec.norm_rpow_eq_sup_type := by
  intro I E _ p _ hpt x
  have hp := exponent_pos (Fact.out : 1 ≤ p) hpt
  exact (isLUB_hasSum (fun i => Real.rpow_nonneg (norm_nonneg _) _)
    (lp.hasSum_norm hp x)).csSup_eq (Set.range_nonempty _)|>.symm

theorem norm_eq_root_sup : Spec.norm_eq_root_sup_type := by
  intro I E _ p _ hpt x
  rw [← norm_rpow_eq_sup E p hpt x, ← Real.rpow_mul (norm_nonneg x)]
  have hp := exponent_pos (Fact.out : 1 ≤ p) hpt
  rw [mul_one_div_cancel hp.ne', Real.rpow_one]

theorem bounded_exists_coordinates_iff : Spec.bounded_exists_coordinates_iff_type := by
  intro I E _ x
  constructor
  · rintro ⟨y, rfl⟩
    exact (memℓp_infty_iff).mp (lp.memℓp y)
  · intro hx
    exact ⟨⟨x, memℓp_infty hx⟩, rfl⟩

theorem bounded_norm_eq_sup : Spec.bounded_norm_eq_sup_type := by
  intro I E _ x
  exact lp.norm_eq_ciSup x

/-- Finite positive level sets themselves imply boundedness. This ensures
that c₀ membership does not acquire an extra hidden boundedness hypothesis. -/
theorem bounded_of_vanishes {I : Type u} {E : I → Type v}
    [∀ i, NormedAddCommGroup (E i)] {x : ∀ i, E i}
    (hx : VanishesAtInfinity E x) : BddAbove (Set.range fun i => ‖x i‖) := by
  obtain ⟨C, hC⟩ := ((hx 1 zero_lt_one).image (fun i => ‖x i‖)).bddAbove
  refine ⟨max C 1, ?_⟩
  rintro _ ⟨i, rfl⟩
  by_cases hi : 1 ≤ ‖x i‖
  · exact (hC ⟨i, hi, rfl⟩).trans (le_max_left _ _)
  · exact (le_of_lt (lt_of_not_ge hi)).trans (le_max_right _ _)

theorem c0_exists_coordinates_iff : Spec.c0_exists_coordinates_iff_type := by
  intro I E _ 𝕜 _ _ x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨⟨x, memℓp_infty (bounded_of_vanishes hx)⟩, hx⟩, rfl⟩

theorem c0_norm_eq_sup : Spec.c0_norm_eq_sup_type := by
  intro I E _ 𝕜 _ _ x
  exact lp.norm_eq_ciSup x.val

theorem ofFiniteSupport_apply : Spec.ofFiniteSupport_apply_type := by
  intro I E _ p x hx i
  rfl

theorem truncate_apply : Spec.truncate_apply_type := by
  intro I E _ p A x j
  simp only [Spec.truncate, lp.coeFn_sum, Finset.sum_apply,
    lp.single_apply, Finset.sum_pi_single]

theorem truncate_finiteSupport : Spec.truncate_finiteSupport_type := by
  intro I E _ p A x
  apply A.finite_toSet.subset
  intro i hi
  by_contra h
  change i ∉ A at h
  exact hi (by rw [truncate_apply E p A x i, ite_eq_right h])

theorem coordinate_apply : Spec.coordinate_apply_type := by
  intro I E _ 𝕜 _ _ p _ i x
  rfl

theorem inclusion_apply : Spec.inclusion_apply_type := by
  intro I E _ 𝕜 _ _ p _ i a j
  exact congrFun (lp.coeFn_single p i a) j

theorem c0Coordinate_apply : Spec.c0Coordinate_apply_type := by
  intro I E _ 𝕜 _ _ i x
  rfl

theorem c0Inclusion_apply : Spec.c0Inclusion_apply_type := by
  intro I E _ 𝕜 _ _ i a j
  exact congrFun (lp.coeFn_single ∞ i a) j

theorem c0Truncate_apply : Spec.c0Truncate_apply_type := by
  intro I E _ 𝕜 _ _ A x j
  change (∑ i ∈ A, c0Inclusion (𝕜 := 𝕜) E i (x i)).val j = _
  simp only [Submodule.coe_sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ i ∈ A, Pi.single i (x i) j) = _
  simp only [Finset.sum_pi_single]

theorem c0Truncate_finiteSupport : Spec.c0Truncate_finiteSupport_type := by
  intro I E _ 𝕜 _ _ A x
  apply A.finite_toSet.subset
  intro i hi
  by_contra h
  change i ∉ A at h
  exact hi (by rw [c0Truncate_apply E A x i, ite_eq_right h])

theorem c0OfFiniteSupport_apply : Spec.c0OfFiniteSupport_apply_type := by
  intro I E _ 𝕜 _ _ x hx i
  rfl

theorem hilbertIdentification_apply : Spec.hilbertIdentification_apply_type := by
  intro I E _ 𝕜 _ _ x
  rfl

theorem empty_index : Spec.empty_index_type := by
  intro I E _ 𝕜 _ _ _
  constructor
  · intro p _ x
    have hx : x = 0 := lp.eq_zero' x
    exact ⟨hx, by rw [hx, norm_zero]⟩
  · intro x
    have hx : x = 0 := Subtype.ext (lp.eq_zero' x.val)
    exact ⟨hx, by rw [hx, norm_zero]⟩

end ExpandedFA.Supplements.BanachSumDefinitions
