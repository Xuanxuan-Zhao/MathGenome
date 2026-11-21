import MathGenome.Internal.Specs.D07.Ch11.FieldPolynomialPid
import MathGenome.Internal.D07.Ch10.EuclideanPid
import MathGenome.Internal.D07.Ch10.PidUfd
import MathGenome.Internal.D07.Ch11.FieldDivision
import Mathlib.RingTheory.Polynomial.Quotient

/-!
Polynomial rings over fields, K07.11.field_polynomial_pid.

The upstream division theorem supplies degree-decreasing remainders.
Well-foundedness of polynomial degree gives the exact Euclidean relation
of the source; the upstream Euclidean-to-PID and PID-to-UFD theorems give
the consequences. For the converse, injective constants pull the domain
property back to R. The library quotient theorem then uses maximality of
(X) and the evaluation isomorphism R[X]/(X) ≃ R to prove IsField R.
-/

universe u

namespace D07.Ch11.FieldPolynomialPid

open Polynomial
open Specs.D07.Ch11.FieldPolynomialPid

theorem degreeEuclideanData : DegreeEuclideanData.{u} := by
  intro F _
  classical
  have hdiv : ∀ f g : Polynomial F, ∃ q r : Polynomial F,
      g ≠ 0 → f = q * g + r ∧ (r = 0 ∨ r.degree < g.degree) := by
    intro f g
    by_cases hg : g = 0
    · exact ⟨0, 0, fun h => (h hg).elim⟩
    · obtain ⟨qr, hqr, _⟩ := FieldDivision.uniqueFieldDivision F f g hg
      exact ⟨qr.1, qr.2, fun _ => hqr⟩
  exact ⟨{
    smaller := fun p q => p.degree < q.degree
    wellFounded := Polynomial.degree_lt_wf
    quotient := fun f g => (hdiv f g).choose
    remainder := fun f g => (hdiv f g).choose_spec.choose
    division := fun f g hg => ((hdiv f g).choose_spec.choose_spec hg).1
    decrease := fun f g hg => ((hdiv f g).choose_spec.choose_spec hg).2 }, rfl⟩

theorem fieldPolynomialEuclidean : FieldPolynomialEuclidean.{u} := by
  intro F _
  obtain ⟨d, _⟩ := degreeEuclideanData F
  exact (Ch10.EuclideanDefinition.divisionDataCharacterization (Polynomial F)).mp ⟨d⟩

theorem fieldPolynomialPID : FieldPolynomialPID.{u} := by
  intro F _
  exact Ch10.EuclideanPid.euclidean_implies_pid (Polynomial F)
    (fieldPolynomialEuclidean F)

theorem fieldPolynomialUFD : FieldPolynomialUFD.{u} := by
  intro F _
  exact Ch10.PidUfd.pid_is_ufd (Polynomial F) (fieldPolynomialPID F)

theorem fieldOfPolynomialPID : FieldOfPolynomialPID.{u} := by
  intro R _ hPID
  obtain ⟨hDomain, hPrincipal⟩ := (Ch10.PidDefinition.pid_iff (Polynomial R)).mp hPID
  let : IsDomain (Polynomial R) := hDomain
  let : IsPrincipalIdealRing (Polynomial R) := hPrincipal
  let : IsDomain R := Function.Injective.isDomain
    (Polynomial.C : R →+* Polynomial R) Polynomial.C_injective
  exact Ideal.IsField.of_isPrincipalIdealRing_polynomial

end D07.Ch11.FieldPolynomialPid
