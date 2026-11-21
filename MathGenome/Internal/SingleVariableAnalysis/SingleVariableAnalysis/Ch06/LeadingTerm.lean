import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Peano
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Equivalence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.LeadingTerm

/-! The first nonzero derivative (K03.06.leading_term).
The finite Taylor sum reduces to its constant and nth terms. Peano's
remainder and the nonzero leading coefficient give the ratio limit.
For real values that ratio is positive close to zero, so the increment
has precisely the sign of the leading monomial. -/
noncomputable section
namespace SingleVariableAnalysis
open Filter Set Asymptotics
open scoped Topology
universe u

variable {K : Type u} [RCLike K]

/-- Collapsing the finite sum uses only the vanishing lower coefficients. -/
theorem taylor_sum_first_nonzero (f : ℝ → K) (n : ℕ) (a h : ℝ) (hn : 1 ≤ n)
    (hz : ∀ j, 1 ≤ j → j < n → RealIteratedDerivative j f a = 0) :
    (∑ k ∈ Finset.range (n+1),
      (RealIteratedDerivative k f a / (k.factorial : K)) * (algebraMap ℝ K h)^k) =
      f a + (RealIteratedDerivative n f a / (n.factorial : K)) *
        (algebraMap ℝ K h)^n := by
  rw [Finset.sum_range_succ]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [hz j (by omega) (Finset.mem_range.mp hj)]
    simp
  · intro h0
    exact (h0 (Finset.mem_range.mpr hn)).elim

theorem leadingTerm_peano : Specs.SingleVariableAnalysis.Ch06.LeadingTerm.leadingTermPeano := by
  intro K _ f n a c hn hnear htop hz hc _hc0
  change c = RealIteratedDerivative n f a / (n.factorial : K) at hc
  have h := taylor_peano f n a hn hnear htop
  have heq (h : ℝ) := taylor_sum_first_nonzero f n a h hn hz
  simp_rw [heq, ← hc] at h
  convert h using 1
  ext h
  ring

theorem leadingTerm_equivalent :
    Specs.SingleVariableAnalysis.Ch06.LeadingTerm.leadingTermEquivalent := by
  intro K _ f n a c hn hnear htop hz hc hc0
  have h := leadingTerm_peano f n a c hn hnear htop hz hc hc0
  have hK : IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => (f (a+h) - f a) - c * (algebraMap ℝ K h)^n)
      (fun h => (algebraMap ℝ K h)^n) := by
    apply IsLittleO.of_norm_right
    simpa only [norm_pow, RCLike.algebraMap_eq_ofReal, RCLike.norm_ofReal, Real.norm_eq_abs] using h.norm_right
  have hmul := (isLittleO_const_mul_right_iff hc0).mpr hK
  have hne : ∀ᶠ h in 𝓝[≠] (0 : ℝ), c * (algebraMap ℝ K h)^n ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero hc0 (pow_ne_zero _ ((map_ne_zero (algebraMap ℝ K)).mpr (by simpa using hh)))
  exact (scalarEquivalent_iff_isEquivalent _ _ _).mpr ⟨hne, hmul⟩

/-- Translate the ratio statement from increments to a punctured neighborhood
of the center. -/
theorem leadingTerm_equivalent_at (f : ℝ → K) (n : ℕ) (a : ℝ) (c : K)
    (hn : 1 ≤ n) (hnear : ∃ U ∈ 𝓝 a, KTimesDifferentiableOn (n-1) f U)
    (htop : DifferentiableAt ℝ (RealIteratedDerivative (n-1) f) a)
    (hz : ∀ j, 1 ≤ j → j < n → RealIteratedDerivative j f a = 0)
    (hc : c = RealIteratedDerivative n f a / (n.factorial : K)) (hc0 : c ≠ 0) :
    ScalarEquivalent (𝓝[≠] a) (fun x => f x - f a)
      (fun x => c * (algebraMap ℝ K (x-a))^n) := by
  have hs : Tendsto (fun x : ℝ => x-a) (𝓝[≠] a) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using! (continuousAt_id.sub continuousAt_const :
        ContinuousAt (fun x : ℝ => x-a) a).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa only [mem_compl_iff, mem_singleton_iff, sub_ne_zero] using hx
  have he := leadingTerm_equivalent f n a c hn hnear htop hz hc hc0
  exact ⟨hs.eventually he.1, by
    simpa only [Function.comp_def, add_sub_cancel] using he.2.comp hs⟩

theorem leadingTerm_strictMin :
    Specs.SingleVariableAnalysis.Ch06.LeadingTerm.leadingTermStrictMin := by
  intro f n a c hn hnear htop hz hc heven hcpos
  have he := ((scalarEquivalent_iff_isEquivalent _ _ _).mp
    (leadingTerm_equivalent_at f n a c hn hnear htop hz hc (ne_of_gt hcpos))).2
  have hp : ∀ᶠ x in 𝓝[≠] a, 0 < c * (algebraMap ℝ ℝ (x-a))^n := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos hcpos (heven.pow_pos (sub_ne_zero.mpr (by simpa using hx)))
  exact (he.eventually_pos hp).mono (fun x hx => sub_pos.mp hx)

theorem leadingTerm_strictMax :
    Specs.SingleVariableAnalysis.Ch06.LeadingTerm.leadingTermStrictMax := by
  intro f n a c hn hnear htop hz hc heven hcneg
  have he := ((scalarEquivalent_iff_isEquivalent _ _ _).mp
    (leadingTerm_equivalent_at f n a c hn hnear htop hz hc (ne_of_lt hcneg))).2
  have hp : ∀ᶠ x in 𝓝[≠] a, c * (algebraMap ℝ ℝ (x-a))^n < 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_neg_of_neg_of_pos hcneg (heven.pow_pos (sub_ne_zero.mpr (by simpa using hx)))
  exact (he.eventually_neg hp).mono (fun x hx => sub_neg.mp hx)

/-- An odd leading monomial takes opposite signs on the two sides. The
contradiction excludes non-strict local extrema as well. -/
theorem leadingTerm_odd : Specs.SingleVariableAnalysis.Ch06.LeadingTerm.leadingTermOdd := by
  intro f n a c hn hnear htop hz hc hodd hc0
  have he := ((scalarEquivalent_iff_isEquivalent _ _ _).mp
    (leadingTerm_equivalent_at f n a c hn hnear htop hz hc hc0)).2
  have hleft := he.mono (nhdsLT_le_nhdsNE a)
  have hright := he.mono (show 𝓝[>] a ≤ 𝓝[≠] a from
    nhdsWithin_mono a (fun x hx => ne_of_gt hx))
  have hLP : ∀ᶠ x in 𝓝[<] a, (algebraMap ℝ ℝ (x-a))^n < 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hodd.pow_neg_iff.mpr (sub_neg.mpr hx)
  have hRP : ∀ᶠ x in 𝓝[>] a, 0 < (algebraMap ℝ ℝ (x-a))^n := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.mpr hx) n
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · have hlpos := hleft.eventually_pos
      (hLP.mono fun x hx => mul_pos_of_neg_of_neg hcneg hx)
    have hrneg := hright.eventually_neg
      (hRP.mono fun x hx => mul_neg_of_neg_of_pos hcneg hx)
    constructor
    · intro hm
      obtain ⟨x, hx, hm⟩ := (hrneg.and (hm.filter_mono nhdsWithin_le_nhds)).exists
      linarith
    · intro hm
      obtain ⟨x, hx, hm⟩ := (hlpos.and (hm.filter_mono nhdsWithin_le_nhds)).exists
      linarith
  · have hlneg := hleft.eventually_neg
      (hLP.mono fun x hx => mul_neg_of_pos_of_neg hcpos hx)
    have hrpos := hright.eventually_pos
      (hRP.mono fun x hx => mul_pos hcpos hx)
    constructor
    · intro hm
      obtain ⟨x, hx, hm⟩ := (hlneg.and (hm.filter_mono nhdsWithin_le_nhds)).exists
      linarith
    · intro hm
      obtain ⟨x, hx, hm⟩ := (hrpos.and (hm.filter_mono nhdsWithin_le_nhds)).exists
      linarith

end SingleVariableAnalysis
