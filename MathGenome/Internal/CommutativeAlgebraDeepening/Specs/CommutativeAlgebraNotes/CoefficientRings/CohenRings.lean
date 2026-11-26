import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RingHom.Smooth

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

universe u

open IsLocalRing

/-- A complete DVR with uniformizer `p` and prescribed residue field whose
positive truncations are formally smooth over the corresponding integer quotients. -/
def cohenRingWithSmoothTruncations : Prop :=
  ∀ (p : ℕ) (_ : p.Prime) (k : Type u) [Field k] [CharP k p],
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ),
      CharZero Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧
        maximalIdeal Λ = Ideal.span {(p : Λ)} ∧ Nonempty (ResidueField Λ ≃+* k) ∧
        ∀ (n : ℕ), 1 ≤ n →
          let I : Ideal Λ := Ideal.span {(p : Λ) ^ n}
          let f : ZMod (p ^ n) →+* Λ ⧸ I :=
            ZMod.castHom (ringChar.dvd (R := Λ ⧸ I) (by
              rw [Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk I), ← map_pow]
              exact Ideal.Quotient.eq_zero_iff_mem.mpr
                (Ideal.subset_span (Set.mem_singleton _)))) _
          f.FormallySmooth

end Specs.CommutativeAlgebraNotes.CoefficientRings
