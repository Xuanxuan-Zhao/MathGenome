import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.HadamardFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.HadamardFixedRank
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.HadamardFactorization
open OrderDivisorDefinitions ExponentCountingRank CanonicalLowerCircles CanonicalFactors

/-- Polynomial converting the canonical product at rank q to rank p. -/
def rankCorrection : Specs.D12Complex.Ch17.HadamardFactorization.rankCorrection_type :=
  Specs.D12Complex.Ch17.HadamardFactorization.rankCorrection_value

theorem rank_change_coefficients :
    Specs.D12Complex.Ch17.HadamardFactorization.rank_change_coefficients_type := by
  intro ι a hloc q hs l hl
  have hsum := summable_exponent_mono a hloc
    (show (q : ℝ) + 1 ≤ (l : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hl)) hs
  convert hsum using 1
  funext i
  rw [norm_pow, norm_inv, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]

theorem rankCorrection_eval :
    Specs.D12Complex.Ch17.HadamardFactorization.rankCorrection_eval_type := by
  intro ι a q p z
  simp only [Specs.D12Complex.Ch17.HadamardFactorization.rankCorrection_value,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem rankCorrection_degree :
    Specs.D12Complex.Ch17.HadamardFactorization.rankCorrection_degree_type := by
  intro ι a q p
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l hl
  exact (Polynomial.natDegree_monomial_le _).trans (Finset.mem_Ioc.mp hl).2

/-- A finite elementary-factor comparison, valid also at their zeros. -/
lemma factor_rank_change (q p : ℕ) (hqp : q ≤ p) (w : ℂ) :
    factor p w = factor q w *
      Complex.exp (∑ l ∈ Finset.Ioc q p, w ^ l / (l : ℂ)) := by
  have hc : (∑ k ∈ Finset.range p, w ^ (k+1) / (k+1 : ℂ)) =
      (∑ k ∈ Finset.range q, w ^ (k+1) / (k+1 : ℂ)) +
        ∑ l ∈ Finset.Ioc q p, w ^ l / (l : ℂ) := by
    induction p, hqp using Nat.le_induction with
    | base => simp
    | succ p hp ih =>
      rw [Finset.sum_range_succ, Finset.sum_Ioc_succ_top hp, ih]
      push_cast
      ring
  simp only [factor, Specs.D12Complex.Ch16.CanonicalFactors.factor_value, hc,
    Complex.exp_add]
  ring

/-- Finite summation of the absolutely convergent coefficient series. -/
lemma correction_hasSum {ι : Type} (a : ι → ℂ) (hloc : LocallyFiniteDivisor a)
    (q p : ℕ) (hs : RankSummable a q) (z : ℂ) :
    HasSum (fun i => ∑ l ∈ Finset.Ioc q p, (z / a i) ^ l / (l : ℂ))
      ((rankCorrection a q p).eval z) := by
  rw [show (rankCorrection a q p).eval z = _ from rankCorrection_eval a q p z]
  have hh (l : ℕ) (hl : l ∈ Finset.Ioc q p) :
      HasSum (fun i => z ^ l / (l : ℂ) * (a i)⁻¹ ^ l)
        (z ^ l / (l : ℂ) * ∑' i, (a i)⁻¹ ^ l) :=
    ((rank_change_coefficients a hloc q hs l (Finset.mem_Ioc.mp hl).1).of_norm.hasSum).mul_left _
  convert hasSum_sum hh using 1
  funext i
  apply Finset.sum_congr rfl
  intro l _
  simp only [div_eq_mul_inv, mul_pow]
  ring

theorem canonical_product_rank_change :
    Specs.D12Complex.Ch17.HadamardFactorization.canonical_product_rank_change_type := by
  intro ι a hloc q p hqp hs
  have hsp : RankSummable a p := summable_exponent_mono a hloc
    (show (q : ℝ) + 1 ≤ (p : ℝ) + 1 by exact_mod_cast (Nat.add_le_add_right hqp 1)) hs
  have hq := hasProdLocallyUniformlyOn_of_summable a q hloc hs
  have hp := hasProdLocallyUniformlyOn_of_summable a p hloc hsp
  refine ⟨hq, hp, fun z => ?_⟩
  have hh := (hq.hasProd (mem_univ z)).mul (correction_hasSum a hloc q p hs z).cexp
  have heq : (fun i => factor q (z / a i) *
      Complex.exp (∑ l ∈ Finset.Ioc q p, (z / a i) ^ l / (l : ℂ))) =
      (fun i => factor p (z / a i)) := by
    funext i
    exact (factor_rank_change q p hqp _).symm
  dsimp only [Function.comp_def] at hh
  rw [heq] at hh
  exact hh.tprod_eq

/-- Complete Hadamard theorem, retaining the least canonical rank. -/
theorem hadamard_factorization :
    Specs.D12Complex.Ch17.HadamardFactorization.hadamard_factorization_type := by
  refine ⟨HadamardFixedRank.hadamard_fixed_rank, ?_⟩
  intro f hfin
  dsimp only
  let p := ⌊(order f).toReal⌋₊
  let m := (analyticOrderAt f.toFun 0).toNat
  let a := zeroLocation f
  have hrank := FiniteOrderDivisorGrowth.canonicalRank_le_floor f hfin
  have hrankfin : canonicalRank a ≠ ⊤ := ne_top_of_le_ne_top (by simp) hrank
  let q := (canonicalRank a).toNat
  have hq : canonicalRank a = (q : ℕ∞) := (ENat.natCast_toNat hrankfin).symm
  have hqp : q ≤ p := ENat.toNat_le_of_le_natCast hrank
  have hs : RankSummable a q := (canonicalRank_eq_nat_iff a q).mp hq |>.1
  obtain ⟨Qp, hQp, _, _, _, he⟩ := HadamardFixedRank.hadamard_fixed_rank f hfin
  let Q := Qp + rankCorrection a q p
  have hQ : Q.natDegree ≤ p := Polynomial.natDegree_add_le_of_degree_le hQp
    (rankCorrection_degree a q p)
  obtain ⟨hconv, _, hchange⟩ := canonical_product_rank_change a (zeros_locallyFinite f) q p hqp hs
  have hfactor (z : ℂ) : f.toFun z = z ^ m * canonicalProduct q a z *
      Complex.exp (Q.eval z) := by
    rw [he z, hchange z]
    simp only [Q, m, rankCorrection, Polynomial.eval_add, Complex.exp_add]
    ring
  have hm : analyticOrderAt f.toFun 0 = (m : ℕ∞) :=
    (ENat.natCast_toNat (zero_multiplicity_finite f 0)).symm
  refine ⟨q, Q, hq, hqp, hQ, hconv, ?_, ?_⟩
  · change Specs.D12Complex.Ch17.OrderDivisorDefinitions.IsCanonicalFactorization_value f m q Q
    refine ⟨hm, hq, canonicalProduct q a, fun z => hconv.hasProd (mem_univ z), hfactor⟩
  · have hgenus : genus q Q ≤ p := max_le hqp hQ
    exact (show (genus q Q : ℝ) ≤ (p : ℝ) by exact_mod_cast hgenus).trans
      (Nat.floor_le ENNReal.toReal_nonneg)

end D12Complex.HadamardFactorization
