import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimaryDecomposition
import MathGenome.Internal.AlgebraCore.P103.Ch05.IrreducibleIntersections
import MathGenome.Internal.AlgebraCore.P103.Ch05.IrreduciblePrimary
import Mathlib.RingTheory.Lasker

namespace P103.Ch05.PrimaryDecomposition

universe u v
open P103.Specs.Ch05.PrimaryDecomposition
open P103.Specs.Ch05.PrimarySubmodules
open P103.Specs.Ch05.AssociatedPrimesInterface

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem radical_eq_colon (Q : Submodule R M) :
    radicalValue R M Q = (Q.colon Set.univ).radical := by
  exact congrArg Ideal.radical (Submodule.annihilator_quotient (N := Q))

/-- Removing a necessary component strictly enlarges the intersection;
this is exactly the source's deletion formulation of irredundancy. -/
theorem decomposition_of_minimal {N : Submodule R M} {s : Finset (Submodule R M)}
    (h : N.IsMinimalPrimaryDecomposition s) (hN : N ≠ ⊤) : IsDecomposition N s := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro hs
    apply hN
    simpa [hs] using h.inf_eq.symm
  · intro Q hQ
    exact (IrreduciblePrimary.primary_iff_mathlib R M Q).mpr (h.primary hQ)
  · simpa only [Finset.inf_eq_iInf, id_eq] using h.inf_eq
  · intro Q hQ P hP hQP
    simpa only [radical_eq_colon] using h.distinct hQ hP hQP
  · intro Q hQ heq
    apply h.minimal hQ
    have hi : (s.erase Q).inf id = N := by
      simpa only [Finset.inf_eq_iInf, id_eq] using heq
    rw [hi, ← h.inf_eq]
    exact Finset.inf_le hQ

/-- The converse bridge makes the uniqueness theorem apply to any family
satisfying the source conditions. -/
theorem minimal_of_decomposition {N : Submodule R M} {s : Finset (Submodule R M)}
    (h : IsDecomposition N s) : N.IsMinimalPrimaryDecomposition s := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Finset.inf_eq_iInf, id_eq] using h.intersection
  · intro Q hQ
    exact (IrreduciblePrimary.primary_iff_mathlib R M Q).mp (h.primary Q hQ)
  · intro Q hQ P hP hQP
    simpa only [radical_eq_colon] using h.distinct hQ hP hQP
  · intro Q hQ hle
    apply h.irredundant Q hQ
    have heq : (s.erase Q).inf id = s.inf id := by
      conv_rhs => rw [← Finset.insert_erase hQ, Finset.inf_insert]
      exact (inf_eq_right.mpr hle).symm
    simpa only [Finset.inf_eq_iInf, id_eq, h.intersection] using heq

theorem exists_decomposition : exists_decompositionType.{u,v} := by
  intro R _ _ M _ _ _ N hN
  obtain ⟨s, hs, hprim, hEq⟩ := IrreducibleIntersections.proper_finite_intersection R M N hN
  have hprimary : ∀ ⦃Q⦄, Q ∈ s → Q.IsPrimary := by
    intro Q hQ
    exact (IrreduciblePrimary.primary_iff_mathlib R M Q).mp
      (IrreduciblePrimary.irreducible_primary R M Q (hprim Q hQ))
  have hinf : s.inf id = N := by
    simpa only [Finset.inf_eq_iInf, id_eq] using hEq.symm
  obtain ⟨t, ht, hp, hd, hm⟩ :=
    Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hinf hprimary
  exact ⟨t, decomposition_of_minimal ⟨ht, hp, hd, hm⟩ hN⟩

/-- Cyclic annihilators in the quotient are the colon ideals upstairs. -/
theorem quotient_elementAnnihilator (N : Submodule R M) (x : M) :
    elementAnnihilatorValue R (M ⧸ N) (N.mkQ x) = N.colon {x} := by
  ext r
  simp only [elementAnnihilatorValue, Submodule.mem_colon_singleton, Submodule.mem_bot]
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem associatedPrimes_quotient [IsNoetherianRing R] (N : Submodule R M) :
    associatedPrimesValue R (M ⧸ N) = N.associatedPrimes := by
  ext p
  rw [Submodule.AssociatePrimes.mem_iff, Submodule.isAssociatedPrime_iff]
  change (p.IsPrime ∧ ∃ x : M ⧸ N, p = elementAnnihilatorValue R (M ⧸ N) x) ↔ _
  constructor
  · rintro ⟨hp, x, hx⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    exact ⟨hp, y, hx.trans (quotient_elementAnnihilator N y)⟩
  · rintro ⟨hp, y, hy⟩
    exact ⟨hp, N.mkQ y, hy.trans (quotient_elementAnnihilator N y).symm⟩

theorem associatedPrimes_eq_radicals : associatedPrimes_eq_radicalsType.{u,v} := by
  intro R _ _ M _ _ _ N s h
  rw [associatedPrimes_quotient, ← (minimal_of_decomposition h).image_radical_eq_associated_primes]
  simp only [radical_eq_colon]

end P103.Ch05.PrimaryDecomposition
