import MathGenome.Internal.Specs.D07.Ch11.MultivariateBoundaryBivariateNonprincipalIdeal
import MathGenome.Internal.D07.Ch11.PolynomialUfd
import Mathlib.Algebra.MvPolynomial.Division

/-!
The ideal (X,Y) in F[X,Y] is proper, since its elements have zero constant
coefficient. Distinct variables are nonassociate primes. Any generator of
(X,Y) would divide both variables; irreducibility of X then forces it to be
a unit, contradicting properness. The accepted finite-variable polynomial
UFD theorem supplies the UFD half of the final example.
-/

universe u

namespace D07.Ch11.MultivariateBoundaryBivariateNonprincipalIdeal

open MvPolynomial
open Specs.D07.Ch11.MultivariateBoundaryBivariateNonprincipalIdeal

theorem variables_prime : VariablesPrime.{u} := by
  intro F _
  exact ⟨X_prime, X_prime⟩

theorem x_not_dvd_y : XNotDvdY.{u} := by
  intro F _
  simp only [X_dvd_X]
  decide

theorem variables_not_associated : VariablesNotAssociated.{u} := by
  intro F _ h
  exact x_not_dvd_y F h.dvd

theorem origin_ideal_proper : OriginIdealProper.{u} := by
  intro F _
  rw [Ideal.ne_top_iff_one]
  intro h
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  have hcoeff := congrArg (constantCoeff : MvPolynomial (Fin 2) F →+* F) hab
  simp at hcoeff

theorem origin_ideal_not_principal : OriginIdealNotPrincipal.{u} := by
  intro F _ h
  obtain ⟨g, hg⟩ := h.principal
  change originIdeal F = Ideal.span {g} at hg
  have hx : g ∣ (X 0 : MvPolynomial (Fin 2) F) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hg]
    exact Ideal.subset_span (by simp)
  have hy : g ∣ (X 1 : MvPolynomial (Fin 2) F) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hg]
    exact Ideal.subset_span (by simp)
  have hunit : IsUnit g :=
    ((variables_prime F).1.irreducible.isRelPrime_iff_not_dvd.mpr (x_not_dvd_y F)) hx hy
  apply origin_ideal_proper F
  rw [hg]
  exact Ideal.span_singleton_eq_top.mpr hunit

theorem ufd_not_pid : UfdNotPid.{u} := by
  intro F _
  refine ⟨inferInstance, PolynomialUfd.finiteVariablePolynomialUfd F (Fin 2), ?_⟩
  intro h
  exact origin_ideal_not_principal F (@IsPrincipalIdealRing.principal _ _ h (originIdeal F))

end D07.Ch11.MultivariateBoundaryBivariateNonprincipalIdeal
