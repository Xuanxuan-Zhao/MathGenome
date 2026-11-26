import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RingHom.Smooth

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

universe u

/-- The canonical map from the integers modulo `p ^ n` to the `n`-th
truncation of a complete DVR with uniformizer `p` is formally smooth. -/
def cohenRingTruncationSmoothness : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    (p : ℕ) [Fact p.Prime], Ideal.span {(p : Λ)} = IsLocalRing.maximalIdeal Λ →
    ∀ (n : ℕ), 1 ≤ n →
    let I : Ideal Λ := Ideal.span {(p : Λ) ^ n}
    let f : ZMod (p ^ n) →+* Λ ⧸ I :=
      ZMod.castHom (ringChar.dvd (R := Λ ⧸ I) (by
        rw [Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk I), ← map_pow]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))) _
    f.FormallySmooth

end Specs.CommutativeAlgebraNotes.CoefficientRings
