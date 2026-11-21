import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.PolynomialHull
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.PoleMovement
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.BoundaryModulus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set

namespace D12Complex.PolynomialHull

/-- The planar polynomial hull, defined by all polynomial norm inequalities. -/
def polynomialHull (K : Set ℂ) : Set ℂ := Definitions.polynomialHull K

theorem subset_polynomialHull :
    Specs.D12Complex.Ch15.PolynomialHull.subset_polynomialHull_type := by
  intro K hK a ha p
  exact le_csSup (hK.bddAbove_image p.differentiable.continuous.norm.continuousOn)
    (mem_image_of_mem _ ha)

/-- Components of an open complement have boundary in the removed closed set. -/
theorem frontier_complementary_component_subset {K : Set ℂ} (hK : IsClosed K)
    (a : ℂ) : frontier (connectedComponentIn Kᶜ a) ⊆ K := by
  let C := connectedComponentIn Kᶜ a
  have hC : IsOpen C := hK.isOpen_compl.connectedComponentIn
  have hrest : IsOpen (Kᶜ \ C) := PoleMovement.isOpen_compl_component hK.isOpen_compl a
  have hdis : Disjoint C (Kᶜ \ C) := disjoint_sdiff_right
  intro z hz
  by_contra hzK
  have hzC : z ∉ C := by
    change z ∈ frontier C at hz
    rw [hC.frontier_eq] at hz
    exact hz.2
  exact Set.disjoint_left.mp (hdis.closure_left hrest)
    (frontier_subset_closure hz) ⟨hzK, hzC⟩

theorem bounded_component_subset_polynomialHull :
    Specs.D12Complex.Ch15.PolynomialHull.bounded_component_subset_polynomialHull_type := by
  intro K hK _ a ha hb z hz p
  let C := connectedComponentIn Kᶜ a
  have hopen : IsOpen C := hK.isClosed.isOpen_compl.connectedComponentIn
  have hdomain : IsDomain C :=
    ⟨⟨a, mem_connectedComponentIn ha⟩, hopen,
      isPreconnected_connectedComponentIn⟩
  have hhol : HolomorphicOn C (fun w => p.eval w) :=
    ⟨hopen, fun _ _ => p.differentiableAt⟩
  obtain ⟨ξ, hξ, hmax⟩ := BoundaryModulus.exists_boundary_maximum C
    (fun w => p.eval w) hdomain hb hhol p.differentiable.continuous.continuousOn
  exact (hmax (subset_closure hz)).trans
    (le_csSup (hK.bddAbove_image p.differentiable.continuous.norm.continuousOn)
      (mem_image_of_mem _ (frontier_complementary_component_subset hK.isClosed a hξ)))

theorem polynomial_separation :
    Specs.D12Complex.Ch15.PolynomialHull.polynomial_separation_type := by
  intro K hK hne a ha hun
  obtain ⟨M, hM⟩ := hK.bddAbove_image
    ((continuous_id.sub continuous_const).norm.continuousOn :
      ContinuousOn (fun z : ℂ => ‖z - a‖) K)
  let B : ℝ := max 1 M
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨p, hp⟩ := PoleMovement.resolvent_polynomial_approximation
    ⟨K, hK⟩ a ha hun (1 / (2 * B)) (by positivity)
  let q : Polynomial ℂ := 1 - (Polynomial.X - Polynomial.C a) * p
  have hqa : q.eval a = 1 := by simp [q]
  refine ⟨q, hqa, csSup_le (hne.image _) ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (fun h => ha (h ▸ hz))
  have heq : q.eval z = (z - a) * ((z - a)⁻¹ - p.eval z) := by
    simp only [q, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [mul_sub, mul_inv_cancel₀ hza]
  have hzB : ‖z - a‖ ≤ B := (hM (mem_image_of_mem _ hz)).trans (le_max_right _ _)
  change ‖q.eval z‖ ≤ (1 / 2 : ℝ)
  rw [heq, norm_mul]
  calc
    ‖z - a‖ * ‖(z - a)⁻¹ - p.eval z‖ ≤ B * (1 / (2 * B)) :=
      mul_le_mul hzB (hp z hz).le (norm_nonneg _) hB.le
    _ = 1 / 2 := by field_simp

theorem polynomialHull_eq_filledHoles :
    Specs.D12Complex.Ch15.PolynomialHull.polynomialHull_eq_filledHoles_type := by
  intro K hK hne
  ext a
  constructor
  · intro ha
    by_cases haK : a ∈ K
    · exact Or.inl haK
    · right
      refine ⟨haK, ?_⟩
      by_contra hun
      obtain ⟨q, hqa, hq⟩ := polynomial_separation K hK hne a haK hun
      have hh := ha q
      rw [hqa, norm_one] at hh
      linarith
  · rintro (ha | ⟨ha, hb⟩)
    · exact subset_polynomialHull K hK ha
    · exact bounded_component_subset_polynomialHull K hK hne a ha hb
        (mem_connectedComponentIn ha)

theorem polynomialHull_empty :
    Specs.D12Complex.Ch15.PolynomialHull.polynomialHull_empty_type := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hh := ha (1 : Polynomial ℂ)
  have : (1 : ℝ) ≤ 0 := by simpa using hh
  exact (not_le.mpr zero_lt_one) this

end D12Complex.PolynomialHull
