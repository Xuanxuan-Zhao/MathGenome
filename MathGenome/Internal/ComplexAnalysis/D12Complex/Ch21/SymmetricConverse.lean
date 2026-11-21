import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.SymmetricConverse
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.SymmetricCoefficients
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Algebra.Polynomial

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace D12Complex.SymmetricConverse
open SymmetricCoefficientData
open Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects

/-- Clearing a rational representative gives a pointwise identity even at its
cancellable denominator zeros. Continuity supplies these values. -/
theorem cleared_coefficient {E : Finset RiemannSphere} {d : ℕ}
    {B : RiemannSphere → Multiset ℂ} (hB : AnalyticMultiset E d B)
    (k : ℕ) (P R : Polynomial ℂ) (hR : R ≠ 0)
    (he : ∀ a : ℂ, sphereFinite a ∉ E →
      sphereFinite (coefficient B k (sphereFinite a)) =
        fill (fun z => P.eval z / R.eval z) a)
    (a : ℂ) (ha : sphereFinite a ∉ E) :
    R.eval a * coefficient B k (sphereFinite a) = P.eval a := by
  have hreg : ∀ᶠ z in 𝓝 a, sphereFinite z ∉ E := by
    apply (E.finite_toSet.isClosed.preimage continuous_sphereFinite).isOpen_compl.mem_nhds
    exact ha
  have hne := (Polynomial.eventually_eval_ne_zero_cofinite hR).filter_mono
    (nhdsNE_le_cofinite a)
  have heq : (fun z => R.eval z * coefficient B k (sphereFinite z)) =ᶠ[𝓝[≠] a]
      (fun z => P.eval z) := by
    filter_upwards [hreg.filter_mono nhdsWithin_le_nhds, hne] with z hz hn
    have han : AnalyticAt ℂ (fun z => P.eval z / R.eval z) z :=
      ((AnalyticOnNhd.eval_polynomial P) z (mem_univ z)).div
        ((AnalyticOnNhd.eval_polynomial R) z (mem_univ z)) hn
    have hv := sphereFinite_injective ((he z hz).trans
      (LocalQuotientsArithmetic.fill_of_analyticAt han))
    rw [hv]
    exact mul_div_cancel₀ _ hn
  exact tendsto_nhds_unique
    (((R.continuous.continuousAt).mul
      (SymmetricCoefficients.differentiable_finite hB k ha).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds)
    ((P.continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds |>.congr' heq.symm)

/-- Clear finitely many rational coefficient denominators simultaneously. -/
theorem symmetric_converse :
    Specs.D12Complex.Ch21.SymmetricConverse.symmetric_converse_type := by
  classical
  intro E d B hB hg
  have hr (k : ℕ) := SymmetricCoefficients.rational_values E d B hB hg k
  choose P R hR he hInfinity using hr
  let s := Finset.range (d + 1)
  let D : Polynomial ℂ := ∏ k ∈ s, R k
  let A (k : ℕ) : Polynomial ℂ :=
    if k = 0 then D else P k * ∏ j ∈ s.erase k, R j
  let Q : Polynomial (Polynomial ℂ) :=
    ∑ k ∈ s, Polynomial.C (A k) * Polynomial.X ^ (d-k)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hR k)
  have hA (k : ℕ) (hk : k ∈ s) (a : ℂ) (ha : sphereFinite a ∉ E) :
      (A k).eval a = D.eval a * coefficient B k (sphereFinite a) := by
    by_cases hk0 : k = 0
    · subst k
      simp [A, SymmetricCoefficientData.coefficient]
    · have hc := cleared_coefficient hB k (P k) (R k) (hR k) (he k) a ha
      have hd : D = R k * ∏ j ∈ s.erase k, R j :=
        (Finset.mul_prod_erase s R hk).symm
      simp only [A, ite_eq_right hk0, Polynomial.eval_mul, hd]
      rw [← hc]
      ring
  have hlead : Q.coeff d = D := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single 0]
    · simp [A]
    · intro k hk hk0
      have hk' : k < d+1 := Finset.mem_range.mp hk
      have hkd : d-k ≠ d := by omega
      simp [Ne.symm hkd]
    · intro h0
      exact (h0 (Finset.mem_range.mpr (Nat.zero_lt_succ d))).elim
  have hQ : Q ≠ 0 := by
    intro hz
    apply hD
    rw [← hlead, hz, Polynomial.coeff_zero]
  have hidentity (a : ℂ) (ha : sphereFinite a ∉ E) :
      Q.map (Polynomial.evalRingHom a) =
        Polynomial.C (D.eval a) *
          ((B (sphereFinite a)).map (fun v => Polynomial.X - Polynomial.C v)).prod := by
    rw [SymmetricCoefficients.product_expansion, (hB.2 _ ha).1]
    simp only [Q, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.coe_evalRingHom,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hA k hk a ha, Polynomial.C_mul, mul_assoc]
  have hdegree : Q.natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le d k)
    · simpa only [hlead] using hD
  refine ⟨D, Q, hD, hQ, hlead, hdegree, hidentity, ?_⟩
  intro a ha v hv
  rw [hidentity a ha, Polynomial.eval_mul, Polynomial.eval_C]
  have hzero : (((B (sphereFinite a)).map
      (fun x => Polynomial.X - Polynomial.C x)).prod).eval v = 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨v, hv, by simp⟩
  rw [hzero, mul_zero]

end D12Complex.SymmetricConverse
