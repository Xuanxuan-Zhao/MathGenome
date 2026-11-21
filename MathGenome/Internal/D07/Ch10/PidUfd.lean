import MathGenome.Internal.Specs.D07.Ch10.PidUfd
import MathGenome.Internal.D07.Ch10.PidAscendingChain
import MathGenome.Internal.D07.Ch10.PidPrimeMaximal
import MathGenome.Internal.D07.Ch10.PrimeFactorizationUnique
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
PID implies UFD (K07.10.pid_ufd).
The ascending-chain prerequisite supplies Noetherianity and hence
well-founded strict divisibility. The PID prime/irreducible equivalence
then gives the UFD structure. We also extract the full factorization
statement and apply the upstream prime-factorization uniqueness theorem.

For the Euclidean consequence we use the paper's weaker, explicit division
hypothesis: a minimal nonzero element of any nonzero ideal generates it.
This avoids assuming the extra relation axiom in Mathlib's EuclideanDomain.
-/

universe u

namespace D07.Ch10.PidUfd

open Specs.D07.Ch10.PidUfd

theorem pid_is_ufd : PIDIsUFD.{u} := by
  intro R _ hPID
  let : IsDomain R := hPID.1
  let : IsNoetherianRing R := PidAscendingChain.noetherian_of_pid R hPID
  have hprime (p : R) : Irreducible p ↔ Prime p := by
    constructor
    · intro hp
      exact (PidPrimeMaximal.irreducible_iff_prime R hPID p hp.ne_zero).mp hp
    · exact Prime.irreducible
  let : UniqueFactorizationMonoid R := {
    irreducible_iff_prime := hprime _ }
  refine ⟨inferInstance, ?_, ?_⟩
  · intro a ha
    exact WfDvdMonoid.exists_factors a ha
  · intro f g hf hg hfg
    exact PrimeFactorizationUnique.primeProductsUnique R f g
      (fun p hp => (hprime p).mp (hf p hp))
      (fun q hq => (hprime q).mp (hg q hq)) hfg

theorem euclidean_is_ufd : EuclideanIsUFD.{u} := by
  intro R _ _ r hr hdiv
  apply pid_is_ufd R
  refine ⟨inferInstance, ?_⟩
  intro I
  classical
  by_cases hI : ∃ a : R, a ∈ I ∧ a ≠ 0
  · obtain ⟨d, hd, hmin⟩ := hr.has_min {a : R | a ∈ I ∧ a ≠ 0} hI
    refine ⟨d, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hd.1)⟩
    intro a ha
    obtain ⟨q, t, heq, ht⟩ := hdiv a d hd.2
    have htI : t ∈ I := by
      have : a - q * d ∈ I := I.sub_mem ha (I.mul_mem_left q hd.1)
      simpa only [heq, add_sub_cancel_left] using this
    have ht0 : t = 0 := by
      rcases ht with ht | ht
      · exact ht
      · by_contra hne
        exact hmin t ⟨htI, hne⟩ ht
    rw [Ideal.mem_span_singleton]
    exact ⟨q, by simpa only [ht0, add_zero, mul_comm] using heq⟩
  · refine ⟨0, ?_⟩
    rw [Ideal.span_singleton_eq_bot.mpr rfl]
    apply le_antisymm _ bot_le
    intro a ha
    exact not_ne_iff.mp (fun hne => hI ⟨a, ha, hne⟩)

end D07.Ch10.PidUfd
