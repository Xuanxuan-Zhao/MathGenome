import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.StrictAdjointSumDomain
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.MultiplierTranspose
import Mathlib.Analysis.PSeries

/-! The maximal real counting-measure multiplier gives A and -A, including
closedness and their exact self-adjoint domains. The reciprocal sequence is
square summable by the p-series test, while its weighted sequence is constant
one. The last two theorems transport the full graphs and domains through the
conjugate-linear Riesz equivalence; the Banach dual itself stays scalar-linear. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate ENNReal
namespace ExpandedFA.Unbounded.StrictAdjointSumDomain
open Multiplication

theorem coordinates : Spec.Coordinates := by
  refine ⟨fun _ => Iff.rfl, ?_, rfl, fun _ => rfl⟩
  intro x n
  exact Measure.ae_count_iff.mp (maximalLpMultiplier_apply Measure.count 2 weight x) n

private theorem neg_multiplier : B = maximalMultiplier Measure.count 2 (fun n => -weight n) := by
  apply LinearPMap.ext
  · ext x
    change MemLp (fun n => weight n * x n) 2 Measure.count ↔
      MemLp (fun n => -weight n * x n) 2 Measure.count
    rw [show (fun n => -weight n * x n) = -(fun n => weight n * x n) by
      funext n; exact neg_mul _ _]
    exact memLp_neg_iff.symm
  · intro x hx hy
    change x ∈ A.domain at hx
    apply Lp.ext
    filter_upwards [Lp.coeFn_neg (A ⟨x, hx⟩),
      maximalLpMultiplier_apply Measure.count 2 weight ⟨x, hx⟩,
      maximalLpMultiplier_apply Measure.count 2 (fun n => -weight n) ⟨x, hy⟩]
      with n hn ha hb
    change (-A ⟨x, hx⟩ : H) n = _
    rw [hn, Pi.neg_apply]
    change -(maximalMultiplier Measure.count 2 weight ⟨x, hx⟩) n = _
    rw [ha, hb, neg_mul]

theorem closed_selfAdjoint : Spec.ClosedSelfAdjoint := by
  have hd : Dense (A.domain : Set H) :=
    maximalLpMultiplier_denselyDefined Measure.count 2 (by norm_num) weight (measurable_of_countable _)
  have hA : IsSelfAdjoint A := multiplier_real_selfAdjoint Measure.count weight
    (measurable_of_countable _) (Filter.Eventually.of_forall fun n => by simp [weight])
  have hB : IsSelfAdjoint B := by
    rw [neg_multiplier]
    apply multiplier_real_selfAdjoint Measure.count _ (measurable_of_countable _)
    exact Filter.Eventually.of_forall fun n => by simp [weight]
  refine ⟨hd, hd, ?_, ?_, hA, hB⟩
  · exact maximalLpMultiplier_isClosed Measure.count 2 weight
  · rw [neg_multiplier]
    exact maximalLpMultiplier_isClosed Measure.count 2 _

theorem sum_zero : Spec.Sum := by
  refine ⟨?_, ?_⟩
  · change A.domain ⊓ A.domain = A.domain
    simp
  · intro x
    change A ⟨x, x.2.1⟩ + -A ⟨x, x.2.2⟩ = 0
    simp

private theorem weight_ne_zero (n : ℕ) : weight n ≠ 0 := by
  change ((n + 1 : ℕ) : ℂ) ≠ 0
  exact_mod_cast Nat.succ_ne_zero n

private theorem reciprocal_memLp :
    MemLp (fun n => (weight n)⁻¹) 2 (Measure.count : Measure ℕ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_of_countable _).aestronglyMeasurable).mpr
  apply integrable_count_iff.mpr
  have hs : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
  convert hs using 1
  funext n
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_inv, weight, Complex.norm_natCast, inv_pow]

theorem reciprocal_excluded : Spec.ReciprocalExcluded := by
  let v : H := reciprocal_memLp.toLp _
  have hv : ∀ n, v n = (weight n)⁻¹ :=
    Measure.ae_count_iff.mp reciprocal_memLp.coeFn_toLp
  refine ⟨v, hv, ?_⟩
  intro hmem
  have hone : MemLp (fun _ : ℕ => (1 : ℂ)) 2 Measure.count := by
    apply hmem.ae_eq
    exact Filter.Eventually.of_forall fun n => by
      change weight n * v n = 1
      rw [hv n, mul_inv_cancel₀ (weight_ne_zero n)]
  have hfin := (memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hone
  simp [Measure.count_apply_infinite Set.infinite_univ] at hfin

private theorem sum_dense : Dense ((A + B).domain : Set H) := by
  rw [sum_zero.1]
  exact closed_selfAdjoint.1

private theorem adjoint_A : HilbertAdjointSpec.adjointValue A = A := by
  rcases closed_selfAdjoint with ⟨_, _, _, _, h, _⟩
  exact LinearPMap.isSelfAdjoint_def.mp h

private theorem adjoint_B : HilbertAdjointSpec.adjointValue B = B := by
  rcases closed_selfAdjoint with ⟨_, _, _, _, _, h⟩
  exact LinearPMap.isSelfAdjoint_def.mp h

theorem hilbert_domains : Spec.HilbertDomains := by
  have htop : (hilbertAdjoint (A + B)).domain = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro y
    apply (mem_hilbertAdjoint_domain_iff (A + B) sum_dense y).mpr
    refine ⟨0, fun x => ?_⟩
    rw [sum_zero.2 x]
    simp
  have hzero : ∀ x : (hilbertAdjoint (A + B)).domain,
      hilbertAdjoint (A + B) x = 0 := by
    intro x
    apply hilbertAdjoint_apply_eq (A + B) sum_dense x 0
    intro y
    rw [sum_zero.2 y]
    simp
  refine ⟨htop, hzero, ?_, ?_, ?_⟩
  · rw [adjoint_A, adjoint_B]
    exact sum_zero.1
  · rw [adjoint_A, adjoint_B]
    exact sum_zero.2
  · rw [adjoint_A, adjoint_B, sum_zero.1]
    change A.domain < (hilbertAdjoint (A + B)).domain
    rw [htop]
    apply lt_top_iff_ne_top.mpr
    obtain ⟨v, _, hv⟩ := reciprocal_excluded
    intro heq
    exact hv (heq ▸ Submodule.mem_top)

theorem riesz_transport : Spec.RieszTransport := by
  intro T hd
  have htest (y z : H) :
      (∀ x : T.domain, inner ℂ z (x : H) = inner ℂ y (T x)) ↔
      (∀ x : T.domain, inner ℂ (T x) y = inner ℂ (x : H) z) := by
    constructor <;> intro h x
    · simpa only [inner_conj_symm] using congrArg conj (h x).symm
    · simpa only [inner_conj_symm] using congrArg conj (h x).symm
  constructor
  · intro y z
    change (J y, J z) ∈ (banachAdjoint T).graph ↔ (y, z) ∈ (hilbertAdjoint T).graph
    rw [banachAdjoint_graph T hd, mem_hilbertAdjoint_graph_iff T hd]
    exact htest y z
  · intro y
    change J y ∈ (banachAdjoint T).domain ↔ y ∈ (hilbertAdjoint T).domain
    rw [mem_banachAdjoint_domain_iff, mem_hilbertAdjoint_domain_iff T hd]
    constructor
    · rintro ⟨f, hf⟩
      obtain ⟨z, rfl⟩ := J.surjective f
      exact ⟨z, (htest y z).mp hf⟩
    · rintro ⟨z, hz⟩
      exact ⟨J z, (htest y z).mpr hz⟩

theorem banach_domains : Spec.BanachDomains := by
  have hdA := closed_selfAdjoint.1
  have hdB := closed_selfAdjoint.2.1
  have htop : (banachAdjoint (A + B)).domain = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro q
    obtain ⟨y, rfl⟩ := J.surjective q
    rw [(riesz_transport (A + B) sum_dense).2]
    rw [hilbert_domains.1]
    exact Submodule.mem_top
  have hzero : ∀ x : (banachAdjoint (A + B)).domain,
      banachAdjoint (A + B) x = 0 := by
    intro x
    apply (banachAdjoint_unique_extension (A + B) sum_dense x 0 ?_).symm
    intro y
    rw [sum_zero.2 y]
    simp
  have hDA : ∀ y : H, J y ∈ (banachAdjoint A).domain ↔ y ∈ A.domain := by
    intro y
    rw [(riesz_transport A hdA).2, adjoint_A]
  have hDB : ∀ y : H, J y ∈ (banachAdjoint B).domain ↔ y ∈ A.domain := by
    intro y
    rw [(riesz_transport B hdB).2, adjoint_B]
    rfl
  have hsumzero : ∀ x : (banachAdjoint A + banachAdjoint B).domain,
      (banachAdjoint A + banachAdjoint B) x = 0 := by
    intro x
    apply dual_eq_of_eq_on_domain A hdA
    intro y
    rw [LinearPMap.add_apply]
    change (banachAdjoint A ⟨x, x.2.1⟩) (y : H) +
      (banachAdjoint B ⟨x, x.2.2⟩) (y : H) = 0
    rw [banachAdjoint_apply A hdA ⟨x, x.2.1⟩ y,
      banachAdjoint_apply B hdB ⟨x, x.2.2⟩ (⟨y, y.2⟩ : B.domain)]
    change (x : H →L[ℂ] ℂ) (A y) + (x : H →L[ℂ] ℂ) (-A y) = 0
    simp
  obtain ⟨v, hv, hvnot⟩ := reciprocal_excluded
  have hnot : J v ∉ (banachAdjoint A + banachAdjoint B).domain := by
    intro h
    exact hvnot ((hDA v).mp h.1)
  have hproper : (banachAdjoint A + banachAdjoint B).domain <
      (banachAdjoint (A + B)).domain := by
    rw [htop]
    apply lt_top_iff_ne_top.mpr
    intro heq
    exact hnot (heq ▸ Submodule.mem_top)
  exact ⟨htop, hzero, hDA, hDB, hsumzero, hproper,
    v, hv, htop ▸ Submodule.mem_top, hnot⟩

end ExpandedFA.Unbounded.StrictAdjointSumDomain
