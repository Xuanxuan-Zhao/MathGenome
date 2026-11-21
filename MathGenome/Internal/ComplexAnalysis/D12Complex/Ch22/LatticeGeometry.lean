import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.LatticeGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section

namespace D12Complex.Ch22.LatticeGeometry

abbrev lattice := Specs.D12Complex.Ch22.LatticeGeometry.lattice

theorem mem_lattice : Specs.D12Complex.Ch22.LatticeGeometry.Membership := by
  intro ω₁ ω₂ z
  simp only [Specs.D12Complex.Ch22.LatticeGeometry.lattice,
    Submodule.mem_span_pair, zsmul_eq_mul]

/-- Positive imaginary period ratio gives a real basis, without additional assumptions. -/
theorem periods_linearIndependent {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) : LinearIndependent ℝ ![ω₁, ω₂] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have hd : (a : ℂ) + (b : ℂ) * (ω₂ / ω₁) = 0 := by
    apply (mul_left_injective₀ h₁)
    simpa [add_mul, mul_assoc, div_mul_cancel₀ _ h₁, Complex.real_smul] using h
  have hi := congrArg Complex.im hd
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, add_zero, zero_add, Complex.zero_im] at hi
  have hb : b = 0 := (mul_eq_zero.mp hi).resolve_right (ne_of_gt h₂)
  subst b
  simp only [zero_smul, add_zero] at h
  exact ⟨(smul_eq_zero.mp h).resolve_right h₁, rfl⟩

private def periodBasis {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    Module.Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank (periods_linearIndependent h₁ h₂) (by simp)

private theorem periodBasis_zero {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) : periodBasis h₁ h₂ 0 = ω₁ := by
  simp [periodBasis]

private theorem periodBasis_one {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) : periodBasis h₁ h₂ 1 = ω₂ := by
  simp [periodBasis]

private theorem lattice_eq_span_basis {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) :
    lattice ω₁ ω₂ = Submodule.span ℤ (Set.range (periodBasis h₁ h₂)) := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
  rw [← Set.image_univ, ← Finset.coe_univ, hu]
  simp [periodBasis_zero, periodBasis_one, lattice,
    Specs.D12Complex.Ch22.LatticeGeometry.lattice]

theorem discrete : Specs.D12Complex.Ch22.LatticeGeometry.Discrete := by
  intro ω₁ ω₂ h₁ h₂
  change DiscreteTopology (lattice ω₁ ω₂)
  rw [lattice_eq_span_basis h₁ h₂]
  infer_instance

theorem bounded_finite : Specs.D12Complex.Ch22.LatticeGeometry.BoundedFinite := by
  intro ω₁ ω₂ h₁ h₂ a R
  change Set.Finite ((lattice ω₁ ω₂ : Set ℂ) ∩ Metric.closedBall a R)
  rw [lattice_eq_span_basis h₁ h₂, Set.inter_comm]
  exact ZSpan.setFinite_inter (periodBasis h₁ h₂) Metric.isBounded_closedBall

theorem power_summable : Specs.D12Complex.Ch22.LatticeGeometry.PowerSummable := by
  intro ω₁ ω₂ h₁ h₂ s hs
  let _ := discrete ω₁ ω₂ h₁ h₂
  have : IsZLattice ℝ (lattice ω₁ ω₂) := ⟨by
    rw [lattice_eq_span_basis h₁ h₂]
    exact ZSpan.span_top _⟩
  have hrank : Module.finrank ℤ (lattice ω₁ ω₂) = 2 := by
    rw [ZLattice.rank ℝ (lattice ω₁ ω₂), Complex.finrank_real_complex]
  have hs' : -s < -(Module.finrank ℤ (lattice ω₁ ω₂) : ℝ) := by
    rw [hrank]
    norm_num
    linarith
  exact (ZLattice.summable_norm_rpow (lattice ω₁ ω₂) (-s) hs').subtype (· ≠ 0)

/-- Norm comparison for the real coordinate map, specialized to integer coefficients. -/
theorem lower_bound : Specs.D12Complex.Ch22.LatticeGeometry.LowerBound := by
  intro ω₁ ω₂ h₁ h₂
  let b := periodBasis h₁ h₂
  let e := b.equivFunL
  let C : ℝ := 2 * ‖e.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C⁻¹, inv_pos.mpr hC, fun m n => ?_⟩
  let z := (m : ℂ) * ω₁ + (n : ℂ) * ω₂
  have hm : e z 0 = (m : ℝ) := by
    change b.repr z 0 = (m : ℝ)
    have hz : z = (m : ℝ) • b 0 + (n : ℝ) • b 1 := by
      simp [z, b, periodBasis_zero, periodBasis_one, Complex.real_smul]
    rw [hz, map_add, map_smul, map_smul]
    simp
  have hn : e z 1 = (n : ℝ) := by
    change b.repr z 1 = (n : ℝ)
    have hz : z = (m : ℝ) • b 0 + (n : ℝ) • b 1 := by
      simp [z, b, periodBasis_zero, periodBasis_one, Complex.real_smul]
    rw [hz, map_add, map_smul, map_smul]
    simp
  have hnorm := e.toContinuousLinearMap.le_opNorm z
  have hm' : |(m : ℝ)| ≤ ‖e.toContinuousLinearMap‖ * ‖z‖ := by
    rw [← hm, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm (e z) 0).trans hnorm
  have hn' : |(n : ℝ)| ≤ ‖e.toContinuousLinearMap‖ * ‖z‖ := by
    rw [← hn, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm (e z) 1).trans hnorm
  have hsum : |(m : ℝ)| + |(n : ℝ)| ≤ C * ‖z‖ := by
    dsimp [C]
    nlinarith [norm_nonneg z]
  exact (inv_mul_le_iff₀ hC).mpr hsum

/-- Minimize the norm over the finite set of nonzero periods no longer than ω₁. -/
theorem minimum_distance : Specs.D12Complex.Ch22.LatticeGeometry.MinimumDistance := by
  intro ω₁ ω₂ h₁ h₂
  let S : Set ℂ := {z | z ∈ lattice ω₁ ω₂ ∧ z ≠ 0 ∧ ‖z‖ ≤ ‖ω₁‖}
  have hω : ω₁ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hS : S.Finite := (bounded_finite ω₁ ω₂ h₁ h₂ 0 ‖ω₁‖).subset (by
    intro z hz
    exact ⟨hz.1, by simpa using hz.2.2⟩)
  obtain ⟨z, hz, hmin⟩ := Set.exists_min_image S (fun z : ℂ => ‖z‖) hS
    ⟨ω₁, hω, h₁, le_rfl⟩
  refine ⟨‖z‖, norm_pos_iff.mpr hz.2.1, z, hz.1, hz.2.1, rfl, ?_⟩
  intro x hx y hy hxy
  rw [dist_eq_norm]
  by_cases hsmall : ‖x - y‖ ≤ ‖ω₁‖
  · exact hmin (x - y) ⟨sub_mem hx hy, sub_ne_zero.mpr hxy, hsmall⟩
  · exact hz.2.2.trans (not_le.mp hsmall).le

theorem orientation : Specs.D12Complex.Ch22.LatticeGeometry.Orientation := by
  intro ω₁ ω₂
  constructor
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact Submodule.subset_span (by simp)
      · have hz : z = -ω₂ := Set.mem_singleton_iff.mp hz
        subst z
        exact neg_mem (Submodule.subset_span (by simp))
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact Submodule.subset_span (by simp)
      · have hz : z = ω₂ := Set.mem_singleton_iff.mp hz
        subst z
        have hh : -ω₂ ∈ lattice ω₁ (-ω₂) := Submodule.subset_span (by simp)
        simpa using neg_mem hh
  · intro h
    simpa only [neg_div, Complex.neg_im] using neg_pos.mpr h

end D12Complex.Ch22.LatticeGeometry
