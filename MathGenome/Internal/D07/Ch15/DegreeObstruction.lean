import MathGenome.Internal.Specs.D07.Ch15.DegreeObstruction
import MathGenome.Internal.D07.Ch15.NormalClosureCriterion
import MathGenome.Internal.D07.Ch15.DegreeObstructionQuarticS4Counterexample

/-! Necessary degree and its failed converse (paper.tex:4524–4553).
The normal closure has power-of-two degree by the accepted exact criterion.
Embed the simple real field in that closure: the tower law makes its degree
a divisor, hence again a power of two. The explicit quartic computations
are reused from the separately assigned counterexample obligation.
-/
namespace D07.Ch15.DegreeObstruction
open IntermediateField StraightedgeCompass
open Specs.D07.Ch15.DegreeObstruction

/-- A simple extension embeds in its normal closure in the chosen algebraic
closure, so its degree divides the degree of that normal closure. -/
lemma simple_degree_dvd_normal_closure
    (K : IntermediateField ℚ ℝ) (a : ℝ) (ha : IsIntegral K a) :
    Module.finrank K K⟮a⟯ ∣
      Module.finrank K (normalClosure K K⟮a⟯ (AlgebraicClosure K)) := by
  let E := (K⟮a⟯ : IntermediateField K ℝ)
  let : FiniteDimensional K E := adjoin.finiteDimensional ha
  let f : E →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  rw [f.equivFieldRange.toLinearEquiv.finrank_eq]
  exact IntermediateField.finrank_dvd_of_le_right f.fieldRange_le_normalClosure

/-- Constructibility forces power-of-two simple degree; no normality of
the simple real extension or finite generation of the base is imposed. -/
theorem necessary_degree : NecessaryDegree := by
  intro K a ha hconstructible
  obtain ⟨n, hn⟩ :=
    (NormalClosureCriterion.normal_closure_criterion K a ha (AlgebraicClosure K)).mp
      hconstructible
  have hd : Module.finrank K K⟮a⟯ ∣ 2 ^ n := by
    rw [← hn]
    exact simple_degree_dvd_normal_closure K a ha
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨m, hm⟩

/-- Actual geometric constructions satisfy the same necessary condition. -/
theorem geometric_necessary_degree : GeometricNecessaryDegree := by
  intro P a ha hconstructible
  exact necessary_degree (coordinateField P) a ha
    ((QuadraticTowerIff.real_criterion P a).mp hconstructible)

/-- Degree four alone does not imply constructibility: all real roots of
X⁴-X-1 give counterexamples. Their nonconstructibility is the independently
proved normal-closure obstruction, rather than an inference from degree four. -/
theorem quartic_root_counterexample : QuarticRootCounterexample := by
  intro a ha
  exact ⟨DegreeObstructionQuarticS4Counterexample.root_integral a ha,
    DegreeObstructionQuarticS4Counterexample.real_root_degree a ha,
    DegreeObstructionQuarticS4Counterexample.real_root_not_constructible a ha⟩

/-- The explicit real root between -1 and 0 makes the failed converse
an existential assertion, not merely a conditional statement about roots. -/
theorem converse_fails_degree_four : ConverseFailsDegreeFour := by
  obtain ⟨a, b, ha, _, hroots⟩ :=
    DegreeObstructionQuarticS4Counterexample.exactly_two_real_roots
  have hroot := (hroots a).mpr (Or.inl rfl)
  exact ⟨a, ha, hroot, quartic_root_counterexample a hroot⟩

end D07.Ch15.DegreeObstruction
