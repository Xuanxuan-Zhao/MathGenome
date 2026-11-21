import MathGenome.Internal.Specs.D07.Ch09.Comaximal
import MathGenome.Internal.D07.Ch08.IdealSumIntersection
import MathGenome.Internal.D07.Ch09.MaximalIdeal
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.NormNum

/-! K07.09.comaximal: sums, witnesses, maximal ideals, and Bezout identities. -/

universe u

namespace D07.Ch09.Comaximal

open Specs.D07.Ch09.Comaximal

/-- Two ideals are comaximal when their sum is the entire ring. -/
def isComaximal {R : Type u} [CommRing R] (I J : Ideal R) : Prop :=
  I ⊔ J = ⊤

theorem witnessCharacterization : WitnessCharacterization.{u} := by
  intro R _ I J
  change I ⊔ J = ⊤ ↔ _
  rw [Ideal.eq_top_iff_one]
  exact (D07.Ch08.IdealSumIntersection.sumDescription R I J
    inferInstance inferInstance).2 1

theorem distinctMaximalIdeals : DistinctMaximalIdeals.{u} := by
  intro R _ I J hI hJ hne
  have hImax := (MaximalIdeal.containingIdealCharacterization R I).mp hI
  have hJmax := (MaximalIdeal.containingIdealCharacterization R J).mp hJ
  change I ⊔ J = ⊤
  rcases hImax.2 (I ⊔ J) le_sup_left with heq | htop
  · have hJI : J ≤ I := heq ▸ le_sup_right
    rcases hJmax.2 I hJI with hIJ | hItop
    · exact (hne hIJ).elim
    · exact (hImax.1 hItop).elim
  · exact htop

theorem principalBezout : PrincipalBezout.{u} := by
  intro R _ a b
  rw [witnessCharacterization R]
  constructor
  · rintro ⟨i, hi, j, hj, hij⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hi
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hj
    exact ⟨r, s, hij⟩
  · rintro ⟨r, s, hrs⟩
    exact ⟨r * a, Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩,
      s * b, Ideal.mem_span_singleton'.mpr ⟨s, rfl⟩, hrs⟩

theorem bezoutImpliesGcdOne : BezoutImpliesGcdOne.{u} := by
  intro R _ _ a b h d
  obtain ⟨r, s, hrs⟩ := h
  constructor
  · rintro ⟨hda, hdb⟩
    rw [← hrs]
    exact dvd_add (dvd_mul_of_dvd_right hda r) (dvd_mul_of_dvd_right hdb s)
  · intro hd
    exact ⟨hd.trans (one_dvd a), hd.trans (one_dvd b)⟩

theorem gcdOneNotSufficient : GcdOneNotSufficient := by
  have hrel : IsRelPrime (2 : Polynomial ℤ) Polynomial.X := by
    apply IsRelPrime.symm
    apply Polynomial.irreducible_X.isRelPrime_iff_not_dvd.mpr
    norm_num [Polynomial.X_dvd_iff]
  have hbez : ¬ ∃ f g : Polynomial ℤ, f * 2 + g * Polynomial.X = 1 := by
    rintro ⟨f, g, hfg⟩
    have heval := congrArg (Polynomial.eval (0 : ℤ)) hfg
    have heq : f.eval 0 * 2 = 1 := by simpa using heval
    have hdiv : (2 : ℤ) ∣ 1 := heq ▸ dvd_mul_left 2 (f.eval 0)
    norm_num at hdiv
  refine ⟨?_, hbez, ?_⟩
  · intro d
    constructor
    · rintro ⟨hd2, hdX⟩
      exact (hrel hd2 hdX).dvd
    · intro hd
      exact ⟨hd.trans (one_dvd _), hd.trans (one_dvd _)⟩
  · exact fun h => hbez ((principalBezout (Polynomial ℤ) 2 Polynomial.X).mp h)

end D07.Ch09.Comaximal
