import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ProximalCharacterization
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ProximalExistence
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.DifferentiabilityMonotonicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.VariationalFirmness

noncomputable section
open scoped InnerProductSpace
universe u
namespace VariationalNotes.ConvexAnalysis
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Identify the finite-value supporting functional with its Riesz vector. -/
lemma mem_subdifferential_toDual_iff_mathGenome [CompleteSpace H]
    (f : H → WithTop ℝ) (p w : H) :
    InnerProductSpace.toDual ℝ H w ∈ subdifferential f p ↔
      w ∈ ExpandedFA.Proximal.hilbertSubdifferential H f p := by
  change (∃ r : ℝ, f p = (r : WithTop ℝ) ∧
    ∀ z, ((r + ⟪w, z - p⟫_ℝ : ℝ) : WithTop ℝ) ≤ f z) ↔
    (f p ≠ ⊤ ∧ ∀ z, f p + (⟪w, z - p⟫_ℝ : WithTop ℝ) ≤ f z)
  constructor
  · rintro ⟨r, hr, hs⟩
    refine ⟨by rw [hr]; exact WithTop.coe_ne_top, ?_⟩
    intro z
    simpa only [hr, WithTop.coe_add] using hs z
  · rintro ⟨hp, hs⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hp
    refine ⟨r, hr.symm, ?_⟩
    intro z
    simpa only [← hr, WithTop.coe_add] using hs z

theorem proximalMap_characterization : Specs.proximalMap_characterization.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x p
  have hc' : ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H f :=
    (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph H f).mpr hc
  exact (minimizer_iff_eq_proximalMap f hp hc hl μ hμ x p).symm.trans
    ((isProximalMinimizer_iff_mathGenome f μ x p).trans
      ((ExpandedFA.Proximal.minimizer_iff_variational H f hc' μ hμ x p).trans
        ((ExpandedFA.Proximal.variational_iff_subgradient H f μ hμ x p).trans
          (mem_subdifferential_toDual_iff_mathGenome f p (μ⁻¹ • (x - p))).symm)))

theorem proximalMap_firm : Specs.proximalMap_firm.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x y
  let p := proximalMap f μ x
  let q := proximalMap f μ y
  have hps := (proximalMap_characterization f hp hc hl μ hμ x p).mp rfl
  have hqs := (proximalMap_characterization f hp hc hl μ hμ y q).mp rfl
  have hm := subdifferential_monotone f p q _ _ hps hqs
  change 0 ≤ ⟪μ⁻¹ • (x - p), p - q⟫_ℝ - ⟪μ⁻¹ • (y - q), p - q⟫_ℝ at hm
  rw [real_inner_smul_left, real_inner_smul_left, ← mul_sub] at hm
  have hm' := nonneg_of_mul_nonneg_right hm (inv_pos.mpr hμ)
  have he : ⟪x - p, p - q⟫_ℝ - ⟪y - q, p - q⟫_ℝ =
      ⟪p - q, x - y⟫_ℝ - ‖p - q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, real_inner_comm (x - y) (p - q)]
    simp only [inner_sub_left]
    ring
  change ‖p - q‖ ^ 2 ≤ ⟪p - q, x - y⟫_ℝ
  linarith [he]

theorem proximalMap_nonexpansive : Specs.proximalMap_nonexpansive.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x y
  have hf := proximalMap_firm f hp hc hl μ hμ x y
  change ‖proximalMap f μ x - proximalMap f μ y‖ ^ 2 ≤
    ⟪proximalMap f μ x - proximalMap f μ y, x - y⟫_ℝ at hf
  change ‖proximalMap f μ x - proximalMap f μ y‖ ≤ ‖x - y‖
  have hcs := real_inner_le_norm (proximalMap f μ x - proximalMap f μ y) (x - y)
  nlinarith [norm_nonneg (proximalMap f μ x - proximalMap f μ y), norm_nonneg (x - y)]

theorem proximalResidual_nonexpansive : Specs.proximalResidual_nonexpansive.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x y
  let p := proximalMap f μ x
  let q := proximalMap f μ y
  have hf := proximalMap_firm f hp hc hl μ hμ x y
  have he : (x - p) - (y - q) = (x - y) - (p - q) := by abel
  change ‖(x - p) - (y - q)‖ ≤ ‖x - y‖
  rw [he]
  have hn := norm_sub_sq_real (x - y) (p - q)
  rw [real_inner_comm (p - q) (x - y)] at hn
  change ‖p - q‖ ^ 2 ≤ ⟪p - q, x - y⟫_ℝ at hf
  nlinarith [sq_nonneg ‖p - q‖, norm_nonneg ((x - y) - (p - q)), norm_nonneg (x - y)]

theorem proximal_finite_and_attained : Specs.proximal_finite_and_attained.{u} := by
  intro H _ _ _ f hp hc hl μ hμ x
  exact ⟨moreauEnvelope_finite f hp hc hl μ hμ x,
    exists_unique_proximalMinimizer f hp hc hl μ hμ x,
    proximalMap_minimizes f hp hc hl μ hμ x,
    moreauEnvelope_eq_objective f hp hc hl μ hμ x⟩

end VariationalNotes.ConvexAnalysis
