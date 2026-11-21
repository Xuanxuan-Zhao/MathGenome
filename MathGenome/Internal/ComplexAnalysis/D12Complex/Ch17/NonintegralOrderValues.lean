import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.NonintegralOrderValues
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.HadamardFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.ElementaryOrderOperations
import Mathlib.Data.Fintype.Sigma

noncomputable section
open Set
open scoped ENNReal
namespace D12Complex.NonintegralOrderValues
open OrderDivisorDefinitions

/-- Finitely many distinct zeros give a finite repeated divisor. Each fibre
is finite because its index is a Fin of the analytic zero multiplicity. -/
lemma finite_repeatedZero (f : NonzeroEntireFunction)
    (hz : Set.Finite {z : ℂ | f.toFun z = 0}) : Finite (RepeatedZero f) := by
  have hbase : Set.Finite {z : ℂ | z ≠ 0 ∧ f.toFun z = 0} :=
    hz.subset (fun _ h => h.2)
  let : Fintype {z : ℂ // z ≠ 0 ∧ f.toFun z = 0} := hbase.fintype
  unfold RepeatedZero
  infer_instance

theorem finite_zeros_polynomial_exp :
    Specs.D12Complex.Ch17.NonintegralOrderValues.finite_zeros_polynomial_exp_type := by
  classical
  intro f hfin hz
  let : Finite (RepeatedZero f) := finite_repeatedZero f hz
  let : Fintype (RepeatedZero f) := Fintype.ofFinite _
  obtain ⟨q, Q, hq, _, _, _, hfac, _⟩ :=
    HadamardFactorization.hadamard_factorization.2 f hfin
  have hq0 : q = 0 := by
    have hzero := canonicalRank_finite (zeroLocation f)
    change canonicalRank (zeroLocation f) = 0 at hzero
    rw [hq] at hzero
    exact_mod_cast hzero
  subst q
  obtain ⟨_, _, P, hP, he⟩ := hfac
  let m := (analyticOrderAt f.toFun 0).toNat
  let A : Polynomial ℂ := Polynomial.X ^ m *
    ∏ i : RepeatedZero f, (1 - Polynomial.C (zeroLocation f i)⁻¹ * Polynomial.X)
  have hPe (z : ℂ) : P z = ∏ i : RepeatedZero f, (1 - z / zeroLocation f i) := by
    have ht := (hP z).tprod_eq
    simpa [zeroLocation, tprod_fintype, Specs.D12Complex.Ch16.CanonicalFactors.factor_value] using ht.symm
  have hAe (z : ℂ) : A.eval z = z ^ m * P z := by
    rw [hPe]
    simp only [A, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [div_eq_mul_inv, mul_comm]
  have heq : f.toFun = (fun z => A.eval z * Complex.exp (Q.eval z)) := by
    funext z
    rw [hAe]
    exact he z
  refine ⟨A, Q, ?_, heq⟩
  intro hA
  obtain ⟨z, hz⟩ := f.nonzero
  apply hz
  rw [heq, hA]
  simp

theorem finite_zeros_integral_order :
    Specs.D12Complex.Ch17.NonintegralOrderValues.finite_zeros_integral_order_type := by
  intro f hfin hz
  obtain ⟨A, Q, hA, he⟩ := finite_zeros_polynomial_exp f hfin hz
  exact ⟨Q.natDegree, ElementaryOrderOperations.polynomial_exp_order A Q f hA he⟩

theorem nonintegral_order_infinite_preimages :
    Specs.D12Complex.Ch17.NonintegralOrderValues.nonintegral_order_infinite_preimages_type := by
  intro f hnc hfin hnonint b hfinite
  obtain ⟨g, hg, horder⟩ := ElementaryOrderOperations.translated_order f b hnc
  change order g = order f at horder
  change order f ≠ ⊤ at hfin
  have hgfin : order g ≠ ⊤ := by simpa only [horder] using hfin
  have hgzeros : Set.Finite {z : ℂ | g.toFun z = 0} := by
    simpa only [hg, sub_eq_zero] using hfinite
  obtain ⟨n, hn⟩ := finite_zeros_integral_order g hgfin hgzeros
  exact hnonint n (horder.symm.trans hn)

end D12Complex.NonintegralOrderValues
