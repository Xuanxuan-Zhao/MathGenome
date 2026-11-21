import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.CoercivePotentialVariationalInequality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.ProximalMap
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Geometry.CoercivePotentialVariationalInequality
open P1.ExtendedConvexFunctions
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A small step works even on the zero space, without division by ‖A‖. -/
lemma exists_contraction_step (A : H →L[ℝ] H) (α : ℝ) (hα : 0 < α)
    (hA : ∀ x, α * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ) :
    ∃ (ρ q : ℝ), 0 < ρ ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ x y, ‖(x - ρ • A x) - (y - ρ • A y)‖ ≤ q * ‖x - y‖ := by
  let ρ := min (1 / (4 * α)) (α / (‖A‖ ^ 2 + 1))
  have hd : 0 < ‖A‖ ^ 2 + 1 := by positivity
  have hρ : 0 < ρ := lt_min (by positivity) (div_pos hα hd)
  have hb : ρ * (4 * α) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * α)).mp (min_le_left _ _)
  have hc : ρ * (‖A‖ ^ 2 + 1) ≤ α :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  let c := 1 - 2 * ρ * α + ρ ^ 2 * ‖A‖ ^ 2
  have hc0 : 0 ≤ c := by dsimp [c]; nlinarith [sq_nonneg (ρ * ‖A‖)]
  have hc1 : c < 1 := by
    have hh : ρ * ‖A‖ ^ 2 < α := by nlinarith
    have hm := mul_lt_mul_of_pos_left hh hρ
    dsimp [c]
    nlinarith [mul_pos hρ hα]
  refine ⟨ρ, Real.sqrt c, hρ, Real.sqrt_nonneg _, ?_, ?_⟩
  · exact (Real.sqrt_lt hc0 (by norm_num)).mpr (by simpa using hc1)
  · intro x y
    have heq : (x - ρ • A x) - (y - ρ • A y) =
        (x - y) - ρ • A (x - y) := by rw [map_sub, smul_sub]; abel
    have hn := A.le_opNorm (x - y)
    have hn2 : ‖A (x - y)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖x - y‖ ^ 2 := by
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg (A (x - y)))
          (mul_nonneg (norm_nonneg A) (norm_nonneg (x - y)))).mpr hn
    have hco := hA (x - y)
    have hi : ⟪x - y, A (x - y)⟫_ℝ = ⟪A (x - y), x - y⟫_ℝ := real_inner_comm _ _
    have hs : ‖(x - ρ • A x) - (y - ρ • A y)‖ ^ 2 ≤ c * ‖x - y‖ ^ 2 := by
      rw [heq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs, hi]
      have hm1 := mul_le_mul_of_nonneg_left hn2 (sq_nonneg ρ)
      have hm2 := mul_le_mul_of_nonneg_left hco hρ.le
      dsimp [c]
      nlinarith
    have hnq : 0 ≤ Real.sqrt c * ‖x - y‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) hnq).mp
    simpa only [mul_pow, Real.sq_sqrt hc0] using hs

lemma solution_iff_subgradient (A : H →L[ℝ] H) (φ : ExtendedFunction H) (u : H) :
    Spec.IsSolution A φ u ↔ -A u ∈ Proximal.Spec.HilbertSubdifferentialValue H φ u := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, ?_⟩
    intro v
    by_cases hv : φ v = ⊤
    · simp [hv]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hv
      have hh := h v r s hr.symm hs.symm
      rw [← hr, ← hs, inner_neg_left, ← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr (by linarith)
  · rintro ⟨hu, h⟩
    refine ⟨hu, ?_⟩
    intro v r s hr hs
    have hh := h v
    rw [hr, hs, inner_neg_left, ← WithTop.coe_add] at hh
    have := WithTop.coe_le_coe.mp hh
    linarith

theorem potential_vi : Spec.PotentialVI.{u} := by
  intro H _ _ _ A α hα hA φ hp hc hl
  obtain ⟨ρ, q, hρ, hq, hq1, hstep⟩ := exists_contraction_step A α hα hA
  let T : H → H := fun u => Proximal.proximalMap H φ ρ (u - ρ • A u)
  have hT : ContractingWith ⟨q, hq⟩ T := by
    refine ⟨hq1, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simp only [dist_eq_norm]
    exact (Proximal.proximalMap_nonexpansive H φ hp hc hl ρ hρ _ _).trans (hstep x y)
  have hiff (u : H) : Spec.IsSolution A φ u ↔ T u = u := by
    rw [solution_iff_subgradient]
    have hchar := (Proximal.proximalMap_characterization H φ hp hc hl ρ hρ
      (u - ρ • A u) u).2
    have heq : ρ⁻¹ • ((u - ρ • A u) - u) = -A u := by
      rw [sub_sub_cancel_left, smul_neg, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    rw [heq] at hchar
    exact hchar.symm.trans eq_comm
  refine ⟨hT.fixedPoint T, (hiff _).mpr hT.fixedPoint_isFixedPt, ?_⟩
  intro u hu
  exact hT.fixedPoint_unique ((hiff u).mp hu)

theorem forcing_properties : Spec.ForcingProperties.{u} := by
  classical
  intro H _ _ K hne hclosed hc f
  refine ⟨?_, ?_, ?_⟩
  · change ∃ x, Spec.ForcingPotential K f x ≠ ⊤
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [Spec.ForcingPotential, hx]⟩
  · intro x y r s a b hx hy ha hb hab
    have hxK : x ∈ K := by
      by_contra hn
      simp [Spec.ForcingPotential, hn] at hx
    have hyK : y ∈ K := by
      by_contra hn
      simp [Spec.ForcingPotential, hn] at hy
    have hr : -⟪f, x⟫_ℝ = r := by
      apply WithTop.coe_injective
      simpa only [Spec.ForcingPotential, ite_eq_left hxK] using hx
    have hs : -⟪f, y⟫_ℝ = s := by
      apply WithTop.coe_injective
      simpa only [Spec.ForcingPotential, ite_eq_left hyK] using hy
    rw [Spec.ForcingPotential, ite_eq_left (hc hxK hyK ha hb hab)]
    apply WithTop.coe_le_coe.mpr
    rw [← hr, ← hs, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact le_of_eq (by ring)
  · intro r
    have heq : {x | Spec.ForcingPotential K f x ≤ (r : WithTop ℝ)} =
        K ∩ {x : H | -⟪f, x⟫_ℝ ≤ r} := by
      ext x
      by_cases hx : x ∈ K
      · simp only [Set.mem_ofPred_eq, Spec.ForcingPotential,
          Set.mem_inter_iff, hx, ite_true, true_and, WithTop.coe_le_coe]
      · simp [Spec.ForcingPotential, hx]
    rw [heq]
    exact hclosed.inter (isClosed_le (continuous_const.inner continuous_id |>.neg) continuous_const)

theorem forcing_solution_iff : Spec.ForcingSolutionIff.{u} := by
  classical
  intro H _ _ A K f u
  constructor
  · rintro ⟨hu, h⟩
    have huK : u ∈ K := by
      by_contra hn
      simp [Spec.ForcingPotential, hn] at hu
    refine ⟨huK, ?_⟩
    intro v hv
    have hh := h v (-⟪f, u⟫_ℝ) (-⟪f, v⟫_ℝ)
      (by simp [Spec.ForcingPotential, huK]) (by simp [Spec.ForcingPotential, hv])
    simp only [inner_sub_left, inner_sub_right] at hh ⊢
    linarith
  · rintro ⟨hu, h⟩
    refine ⟨by simp [Spec.ForcingPotential, hu], ?_⟩
    intro v r s hr hs
    have hv : v ∈ K := by
      by_contra hn
      simp [Spec.ForcingPotential, hn] at hs
    have hr' : -⟪f, u⟫_ℝ = r := by
      apply WithTop.coe_injective
      simpa only [Spec.ForcingPotential, ite_eq_left hu] using hr
    have hs' : -⟪f, v⟫_ℝ = s := by
      apply WithTop.coe_injective
      simpa only [Spec.ForcingPotential, ite_eq_left hv] using hs
    have hh := h v hv
    simp only [inner_sub_left, inner_sub_right] at hh ⊢
    linarith

theorem stampacchia : Spec.Stampacchia.{u} := by
  intro H _ _ _ A α hα hA K hne hclosed hc f
  obtain ⟨hp, hconv, hl⟩ := forcing_properties H K hne hclosed hc f
  obtain ⟨u, hu, hunique⟩ := potential_vi H A α hα hA (Spec.ForcingPotential K f) hp hconv hl
  refine ⟨u, (forcing_solution_iff H A K f u).mp hu, ?_⟩
  intro v hv
  exact hunique v ((forcing_solution_iff H A K f v).mpr hv)

end ExpandedFA.Geometry.CoercivePotentialVariationalInequality
