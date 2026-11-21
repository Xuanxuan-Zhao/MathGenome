import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02HilbertSum

/-!
The arbitrary-index Hilbert direct sum from paper.tex 484–496, realized as
Mathlib's native `lp H 2`. Bounded finite squared sums are equivalent to its
membership condition. Its existing norm squared equals the finite-sum supremum,
and its existing inner product is the unconditional coordinate sum.

The definitions and supporting coordinate/truncation formulas are available
without countability, nonemptiness, or nonzero-summand hypotheses. Completeness
and finite-support density are assigned to subsequent goals.
-/

open scoped ENNReal Classical

noncomputable section
universe u v
namespace ExpandedFA.P1.C02HilbertSum

variable {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)]

abbrev Space : Type (max u v) := Spec.Space H
abbrev SquareSummable := Spec.SquareSummable H
abbrev squaredSum := Spec.squaredSum H
abbrev finiteSupport := Spec.finiteSupport H
abbrev ofFiniteSupport := Spec.ofFiniteSupport H
abbrev truncate := Spec.truncate H

variable {H}

theorem memℓp_iff_squareSummable (x : ∀ i, H i) :
    Memℓp x 2 ↔ SquareSummable H x := by
  rw [memℓp_gen_iff'' (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  constructor
  · rintro ⟨C, _, hC⟩
    exact ⟨C, by rintro _ ⟨A, rfl⟩; exact hC A⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_, fun A => hC ⟨A, rfl⟩⟩
    simpa using hC ⟨∅, by simp⟩

/-- Every and only the families in the displayed source definition occur. -/
theorem exists_coordinates_iff (x : ∀ i, H i) :
    (∃ y : Space H, (fun i => y i) = x) ↔ SquareSummable H x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (memℓp_iff_squareSummable _).mp (lp.memℓp y)
  · intro hx
    exact ⟨⟨x, (memℓp_iff_squareSummable x).mpr hx⟩, rfl⟩

theorem norm_sq_eq_tsum (x : Space H) : ‖x‖ ^ 2 = ∑' i, ‖x i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

theorem norm_sq_eq_sup (x : Space H) : ‖x‖ ^ 2 = squaredSum H (fun i => x i) := by
  exact (isLUB_hasSum (fun i => sq_nonneg ‖x i‖)
    (by simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x)).csSup_eq (Set.range_nonempty _)|>.symm

theorem ofFiniteSupport_apply (x : ∀ i, H i) (hx : Set.Finite {i | x i ≠ 0}) (i : I) :
    ofFiniteSupport H x hx i = x i := rfl

theorem truncate_apply (A : Finset I) (x : ∀ i, H i) (j : I) :
    truncate H A x j = (if j ∈ A then x j else 0) := by
  classical
  simp only [truncate, Spec.truncate,
    lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

theorem norm_sq_truncate (A : Finset I) (x : ∀ i, H i) :
    ‖truncate H A x‖ ^ 2 = ∑ i ∈ A, ‖x i‖ ^ 2 := by
  classical
  simpa [truncate, Spec.truncate] using
    lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x A

theorem truncate_finiteSupport (A : Finset I) (x : ∀ i, H i) :
    truncate H A x ∈ finiteSupport H := by
  classical
  apply A.finite_toSet.subset
  intro i hi
  by_contra h
  change i ∉ A at h
  exact hi (by simp [truncate_apply, h])

theorem ofFiniteSupport_mem (x : ∀ i, H i) (hx : Set.Finite {i | x i ≠ 0}) :
    ofFiniteSupport H x hx ∈ finiteSupport H := hx

/-- The set of finite-support vectors is precisely the set of finite truncations. -/
theorem mem_finiteSupport_iff (x : Space H) :
    x ∈ finiteSupport H ↔ ∃ A : Finset I, truncate H A (fun i => x i) = x := by
  classical
  constructor
  · intro hx
    change Set.Finite {i | x i ≠ 0} at hx
    refine ⟨hx.toFinset, lp.ext (funext fun i => ?_)⟩
    by_cases hi : x i = 0
    · simp [truncate_apply, hi]
    · simp [truncate_apply, Set.Finite.mem_toFinset, hi]
  · rintro ⟨A, hA⟩
    rw [← hA]
    exact truncate_finiteSupport _ _

variable (H) {𝕜 : Type*} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)]

abbrev coordinate := Spec.coordinate (𝕜 := 𝕜) H
abbrev inclusion := Spec.inclusion (𝕜 := 𝕜) H

variable {H}

theorem coordinate_apply (i : I) (x : Space H) : coordinate (𝕜 := 𝕜) H i x = x i := rfl

theorem inclusion_apply_self (i : I) (a : H i) :
    inclusion (𝕜 := 𝕜) H i a i = a := by
  classical
  exact lp.single_apply_self 2 i a

theorem inclusion_apply_ne (i j : I) (a : H i) (h : j ≠ i) :
    inclusion (𝕜 := 𝕜) H i a j = 0 := by
  classical
  exact lp.single_apply_ne 2 i a h

theorem norm_inclusion (i : I) (a : H i) : ‖inclusion (𝕜 := 𝕜) H i a‖ = ‖a‖ := by
  classical
  exact lp.norm_single (by norm_num) i a

theorem inner_eq_tsum (x y : Space H) :
    inner 𝕜 x y = ∑' i, inner 𝕜 (x i) (y i) := lp.inner_eq_tsum x y

theorem hasSum_inner (x y : Space H) :
    HasSum (fun i => inner 𝕜 (x i) (y i)) (inner 𝕜 x y) := lp.hasSum_inner x y

end ExpandedFA.P1.C02HilbertSum
