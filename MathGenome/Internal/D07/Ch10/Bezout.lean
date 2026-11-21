import MathGenome.Internal.Specs.D07.Ch10.Bezout
import MathGenome.Internal.D07.Ch10.GcdLcm
import MathGenome.Internal.D07.Ch10.PidDefinition
import MathGenome.Internal.D07.Ch08.IdealGeneration
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import Mathlib.Algebra.Polynomial.Degree.Domain

/-! Bezout identities from principal pairs, including the limitation in ℤ[X]. -/

universe u

namespace D07.Ch10.Bezout

open Polynomial
open Specs.D07.Ch10.GcdLcm
open Specs.D07.Ch10.Bezout

theorem pairMembership : PairMembership.{u} := by
  intro R _ _ a b d
  simpa only [eq_comm] using (Ideal.mem_span_pair (x := a) (y := b) (z := d))

theorem commonDivisorInclusion : CommonDivisorInclusion.{u} := by
  intro R _ _ a b c hca hcb
  apply Ideal.span_le.mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact Ideal.mem_span_singleton.mpr hca
  · have hz' : z = b := Set.mem_singleton_iff.mp hz
    subst z
    exact Ideal.mem_span_singleton.mpr hcb

theorem principalPairGcd : PrincipalPairGcd.{u} := by
  intro R _ _ a b d h
  have ha : a ∈ Ideal.span ({a, b} : Set R) := Ideal.subset_span (by simp)
  have hb : b ∈ Ideal.span ({a, b} : Set R) := Ideal.subset_span (by simp)
  refine ⟨Ideal.mem_span_singleton.mp (h ▸ ha),
    Ideal.mem_span_singleton.mp (h ▸ hb), ?_⟩
  intro c hca hcb
  have hd : d ∈ Ideal.span ({a, b} : Set R) := by
    rw [h]
    exact Ideal.mem_span_singleton_self d
  exact Ideal.mem_span_singleton.mp (commonDivisorInclusion R a b c hca hcb hd)

theorem principalPairBezout : PrincipalPairBezout.{u} := by
  intro R _ _ a b d h
  apply (pairMembership R a b d).mp
  rw [h]
  exact Ideal.mem_span_singleton_self d

theorem pidGcdBezout : PIDGcdBezout.{u} := by
  intro R _ _ _ a b
  obtain ⟨d, hd⟩ := Submodule.IsPrincipal.principal (Ideal.span ({a, b} : Set R))
  exact ⟨d, hd, principalPairGcd R a b d hd, principalPairBezout R a b d hd⟩

theorem pidEveryGcdBezout : PIDEveryGcdBezout.{u} := by
  intro R _ _ _ a b d hd
  obtain ⟨e, he, hge, _⟩ := pidGcdBezout R a b
  have hed : e ∣ d := hd.2.2 e hge.1 hge.2.1
  have heq : Ideal.span ({a, b} : Set R) = Ideal.span {d} := by
    apply le_antisymm
    · exact commonDivisorInclusion R a b d hd.1 hd.2.1
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [he]
      exact Ideal.mem_span_singleton.mpr hed
  exact ⟨heq, principalPairBezout R a b d heq⟩

theorem allZeroCase : AllZeroCase.{u} := by
  intro R _ _
  have h : Ideal.span ({0, 0} : Set R) = Ideal.span {(0 : R)} := by simp
  exact ⟨h, principalPairGcd R 0 0 0 h, ⟨0, 0, by simp⟩⟩

theorem divisorTwoConstant : DivisorTwoConstant := by
  intro p hp
  have htwo : C (2 : ℤ) ≠ 0 := by simp
  have hdeg : p.natDegree = 0 := by
    have h := Polynomial.natDegree_le_of_dvd hp htwo
    simpa using h
  exact ⟨p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩

theorem commonDivisorTwoXUnit : CommonDivisorTwoXUnit := by
  intro p hp2 hpX
  obtain ⟨n, rfl⟩ := divisorTwoConstant p hp2
  apply Polynomial.isUnit_C.mpr
  apply isUnit_iff_dvd_one.mpr
  have hn := (Polynomial.C_dvd_iff_dvd_coeff n X).mp hpX 1
  simpa using hn

theorem twoXGcdOne : TwoXGcdOne := by
  refine ⟨one_dvd _, one_dvd _, ?_⟩
  intro p hp2 hpX
  exact (commonDivisorTwoXUnit p hp2 hpX).dvd

theorem evenConstantCoefficient : EvenConstantCoefficient := by
  intro f g
  exact ⟨f.coeff 0, by simp⟩

theorem twoXNoBezout : TwoXNoBezout := by
  rintro ⟨f, g, h⟩
  have hdiv := evenConstantCoefficient f g
  rw [h] at hdiv
  norm_num at hdiv

end D07.Ch10.Bezout
