import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpConstruction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.SinCos
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.LogArctanSeries
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Binomial
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.StandardSeries

/-!
# Standard elementary series with their exact real domains

K03.13.standard_series, paper.tex:1514–1536. This collects the established
series constructions and endpoint results. The factorial identities also
identify the canonical real functions by the proved construction bridges.
Logarithm and arctangent retain ordinary, potentially conditional convergence.
The binomial cases retain the root-limsup radius and distinguish natural
exponents, including the constant polynomial when the exponent is zero.
-/
noncomputable section
namespace SingleVariableAnalysis.StandardSeries
open Specs.SingleVariableAnalysis.Ch07.SinCos

theorem exp_identity : Specs.SingleVariableAnalysis.Ch13.StandardSeries.expIdentity := by
  intro x
  refine ⟨real_expSeries_hasSum x, ?_⟩
  rw [← expSeries_eq_realExp x]
  exact real_expSeries_hasSum x

theorem sin_identity : Specs.SingleVariableAnalysis.Ch13.StandardSeries.sinIdentity := by
  intro x
  have hs := (real_sinCosSeries_hasSum x).1
  refine ⟨hs, ?_⟩
  rw [← (sinCosSeries_eq_real x).1]
  exact hs

theorem cos_identity : Specs.SingleVariableAnalysis.Ch13.StandardSeries.cosIdentity := by
  intro x
  have hc := (real_sinCosSeries_hasSum x).2
  refine ⟨hc, ?_⟩
  rw [← (sinCosSeries_eq_real x).2]
  exact hc

theorem factorial_absolute : Specs.SingleVariableAnalysis.Ch13.StandardSeries.factorialAbsolute := by
  intro x
  refine ⟨?_, (real_sinCosSeries_absolute x).1, ?_⟩
  · have hs := (Real.summable_pow_div_factorial |x|).hasSum
    have ha : HasSum (fun n => |x^n / (n.factorial : ℝ)|)
        (∑' n, |x|^n / (n.factorial : ℝ)) := by
      simpa only [abs_div, abs_pow, Nat.abs_cast] using hs
    exact ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum ha⟩
  · exact (real_sinCosSeries_absolute x).2

theorem log_identity : Specs.SingleVariableAnalysis.Ch13.StandardSeries.logIdentity :=
  LogArctanSeries.log_identity

theorem arctan_identity : Specs.SingleVariableAnalysis.Ch13.StandardSeries.arctanIdentity :=
  LogArctanSeries.arctan_identity

theorem log_domain : Specs.SingleVariableAnalysis.Ch13.StandardSeries.logDomain :=
  LogArctanSeries.log_domain

theorem arctan_domain : Specs.SingleVariableAnalysis.Ch13.StandardSeries.arctanDomain :=
  LogArctanSeries.arctan_domain

theorem log_endpoint : Specs.SingleVariableAnalysis.Ch13.StandardSeries.logEndpoint :=
  LogArctanSeries.log_endpoint

theorem arctan_endpoints : Specs.SingleVariableAnalysis.Ch13.StandardSeries.arctanEndpoints :=
  LogArctanSeries.arctan_endpoints

theorem log_negative_endpoint : Specs.SingleVariableAnalysis.Ch13.StandardSeries.logNegativeEndpoint :=
  LogArctanSeries.log_negative_endpoint

theorem exterior_divergence : Specs.SingleVariableAnalysis.Ch13.StandardSeries.exteriorDivergence :=
  LogArctanSeries.exterior_divergence

theorem binomial_interior : Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialInterior :=
  SingleVariableAnalysis.binomial_interior_and_radius.1

theorem binomial_radius : Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialRadius :=
  SingleVariableAnalysis.binomial_interior_and_radius.2

theorem binomial_one_converges : Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialOneConverges :=
  SingleVariableAnalysis.binomial_endpoint_one_converges

theorem binomial_one_sum : Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialOneSum :=
  SingleVariableAnalysis.binomial_endpoint_one_sum

theorem binomial_neg_one_converges :
    Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialNegOneConverges :=
  SingleVariableAnalysis.binomial_endpoint_neg_one_converges

theorem binomial_neg_one_sum : Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialNegOneSum :=
  SingleVariableAnalysis.binomial_endpoint_neg_one_sum

theorem binomial_endpoints_absolute :
    Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialEndpointsAbsolute :=
  SingleVariableAnalysis.binomial_endpoints_absolute

theorem binomial_one_conditional : Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialOneConditional :=
  SingleVariableAnalysis.binomial_endpoint_one_conditional

theorem binomial_natural_all_arguments :
    Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialNaturalAllArguments :=
  SingleVariableAnalysis.binomial_natural_all_arguments

theorem binomial_natural_endpoints :
    Specs.SingleVariableAnalysis.Ch13.StandardSeries.binomialNaturalEndpoints :=
  SingleVariableAnalysis.binomial_natural_endpoints

end SingleVariableAnalysis.StandardSeries
