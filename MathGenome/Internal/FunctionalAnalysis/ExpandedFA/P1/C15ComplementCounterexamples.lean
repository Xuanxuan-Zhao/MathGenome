import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15ComplementCounterexamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DiscontinuousAlgebraicFunctional
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02Projections
import Mathlib.Analysis.SpecificLimits.Normed

/-! Elementary failures of algebraic intuition, paper.tex 4082–4096. -/

noncomputable section
open scoped ENNReal
universe u
namespace ExpandedFA.P1.C15ComplementCounterexamples

theorem finite_support_identification : Spec.FiniteSupportIdentification.{u} := by
  intro 𝕜 _ x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.hasFiniteSupport
  · intro hx
    exact ⟨Finsupp.ofSupportFinite (fun n => x n) hx, lp.ext rfl⟩

theorem unit_vector_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : ‖e 𝕜 n‖ = 1 := by
  simp [e, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

theorem unit_vector_ne_zero (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : e 𝕜 n ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [unit_vector_norm]; exact one_ne_zero)

theorem finite_support_dense (𝕜 : Type u) [RCLike 𝕜] :
    Dense (c00 𝕜 : Set (Space 𝕜)) := by
  intro x
  apply (c00 𝕜).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro n hn
  apply (c00 𝕜).le_topologicalClosure
  rw [finite_support_identification]
  exact (Set.finite_singleton n).subset (by
    intro j hj
    by_contra h
    exact hj (lp.single_apply_ne _ _ _ h))

/-- The everywhere nonzero geometric sequence belongs to `ℓ²`, but not `c₀₀`. -/
theorem finite_support_proper (𝕜 : Type u) [RCLike 𝕜] : c00 𝕜 ≠ ⊤ := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hm : Memℓp (fun n : ℕ => (1 / 2 : 𝕜) ^ n) 1 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, norm_pow, norm_div, norm_one,
      RCLike.norm_ofNat] using hg
  let x : Space 𝕜 := ⟨_, hm.of_exponent_ge (by norm_num)⟩
  intro h
  have hx : x ∈ c00 𝕜 := h ▸ Submodule.mem_top
  have hf := (finite_support_identification 𝕜 x).mp hx
  have hsupport : Function.support (fun n => x n) = Set.univ := by
    ext n
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact pow_ne_zero _ (by norm_num : (1 / 2 : 𝕜) ≠ 0)
  rw [hsupport] at hf
  exact Set.infinite_univ hf

theorem finite_support_obstruction : Spec.FiniteSupportObstruction.{u} := by
  intro 𝕜 _
  have hd := finite_support_dense 𝕜
  refine ⟨hd, finite_support_proper 𝕜, ?_⟩
  rintro ⟨P, hP, hr⟩
  obtain ⟨_, hc, _⟩ := C02Projections.bounded_projection_direct_sum 𝕜 (Space 𝕜) P hP
  rw [hr] at hc
  have he : (c00 𝕜 : Set (Space 𝕜)) = Set.univ := by
    rw [← hc.closure_eq, hd.closure_eq]
  exact finite_support_proper 𝕜 (SetLike.coe_injective he)

/-- The standard coordinate vectors remain independent in `ℓ²`. -/
theorem unit_vectors_independent (𝕜 : Type u) [RCLike 𝕜] :
    LinearIndependent 𝕜 (e 𝕜) := by
  let T := lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜)
    (show (0 : ℝ≥0∞) ≤ 2 by positivity)
  have hT : Function.Injective T := by
    intro x y h
    apply lp.ext
    exact congrArg (fun z : Space 𝕜 => (fun n => z n)) h
  convert (lp.zeroBasis (𝕜 := 𝕜) (α := ℕ)).linearIndependent.map' T
    (LinearMap.ker_eq_bot.mpr hT) using 1
  funext n
  change e 𝕜 n = T (lp.zeroBasis n)
  rw [lp.zeroBasis_apply]
  apply lp.ext
  rfl

theorem unbounded_line_projection : Spec.UnboundedLineProjection.{u} := by
  intro 𝕜 _
  have hi := unit_vectors_independent 𝕜
  obtain ⟨B, b, f, hb, hsub, hf, hzero⟩ :=
    DiscontinuousAlgebraicFunctional.exists_basis_functional hi
      (fun n => (n + 1 : ℕ))
  let P := f.smulRight (e 𝕜 0)
  have hf0 : f (e 𝕜 0) = 1 := by simpa using hf 0
  have hfn : f ≠ 0 := by
    intro h
    have := hf0
    simp [h] at this
  have hP (x : Space 𝕜) : P x = f x • e 𝕜 0 := rfl
  have hn (n : ℕ) : ‖P (e 𝕜 n)‖ = (n + 1 : ℕ) := by
    rw [hP, hf, norm_smul, unit_vector_norm, mul_one, RCLike.norm_natCast]
  have hunbounded : ¬ ∃ C : ℝ, ∀ x, ‖P x‖ ≤ C * ‖x‖ := by
    rintro ⟨C, hC⟩
    obtain ⟨n, hnC⟩ := exists_nat_gt C
    have hh := hC (e 𝕜 n)
    rw [hn, unit_vector_norm, mul_one] at hh
    have hle : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    exact (not_lt_of_ge (hle.trans hh)) hnC
  refine ⟨B, b, f, P, hi, hb, hsub, hf, hzero, hP, ?_, ?_, ?_, ?_,
    (fun n => ⟨unit_vector_norm 𝕜 n, hn n⟩), hunbounded, ?_⟩
  · apply LinearMap.ext
    intro x
    change P (P x) = P x
    simp only [hP, map_smul, hf0, smul_eq_mul, mul_one]
  · exact LinearMap.range_smulRight_apply hfn _
  · exact finrank_span_singleton (unit_vector_ne_zero 𝕜 0)
  · exact (Submodule.span 𝕜 {e 𝕜 0}).closed_of_finiteDimensional
  · intro hc
    obtain ⟨C, _, hC⟩ := SemilinearMapClass.bound_of_continuous P hc
    exact hunbounded ⟨C, hC⟩

theorem bounded_orthogonal_projection : Spec.BoundedOrthogonalProjection.{u} := by
  intro 𝕜 _
  let M := firstLine 𝕜
  let : FiniteDimensional 𝕜 M := FiniteDimensional.span_singleton 𝕜 (e 𝕜 0)
  have hne : M ≠ ⊥ := by
    intro h
    have he : e 𝕜 0 ∈ M := Submodule.subset_span (Set.mem_singleton _)
    rw [h] at he
    exact unit_vector_ne_zero 𝕜 0 he
  refine ⟨M.starProjection, M.isIdempotentElem_starProjection,
    M.range_starProjection, M.ker_starProjection, M.norm_starProjection hne, ?_⟩
  intro x
  change (𝕜 ∙ e 𝕜 0).starProjection x = _
  rw [Submodule.starProjection_singleton, unit_vector_norm]
  simp [e, lp.inner_single_left, RCLike.inner_apply]

end ExpandedFA.P1.C15ComplementCounterexamples
