import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.ArtinianProduct
import MathGenome.Internal.AlgebraCore.P103.Ch03.ArtinianRadical
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalRing.Basic

/-!
The commutative conclusion of paper.tex, Theorem 3.3.

Artinianity makes the maximal spectrum finite and identifies the nilradical
with the Jacobson radical. The intersection of the Nth powers of the maximal
ideals is therefore J^N. Distinct maximal ideals, and hence their powers, are
coprime, so the Chinese remainder equivalence has exactly the required map.
For locality, an element outside m is a unit modulo m^N; if x is in m, then
1 - x is outside m. Positive N ensures the quotient is nonzero. Quotients
inherit Artinianity. The upstream nilpotence theorem supplies a positive
exponent (increase any nilpotence exponent by one), also for the zero ring.
-/

universe u

namespace P103.Ch03.ArtinianProduct

open P103.Specs.Ch03.ArtinianProduct
open P103.Specs.Ch03.JacobsonRadical (radical)

theorem finite_maximalIdeals : finite_maximalIdealsType.{u} := by
  intro R _ _
  infer_instance

theorem factors_local_artinian : factors_local_artinianType.{u} := by
  intro R _ _ N hN m
  have hn : N ≠ 0 := Nat.ne_of_gt hN
  have hproper : m.asIdeal ^ N ≠ ⊤ := by
    intro h
    exact (Ideal.pow_eq_top_iff.mp h).elim m.isMaximal.ne_top hn
  have : Nontrivial (R ⧸ m.asIdeal ^ N) := Submodule.Quotient.nontrivial_iff.mpr hproper
  refine ⟨?_, inferInstance⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  by_cases hx : x ∈ m.asIdeal
  · right
    rw [← map_one (Ideal.Quotient.mk (m.asIdeal ^ N)), ← map_sub]
    apply Ideal.Quotient.isUnit_mk_pow_of_notMem
    intro h
    exact m.isMaximal.ne_top (m.asIdeal.eq_top_iff_one.mpr
      (by simpa using m.asIdeal.add_mem h hx))
  · exact Or.inl (Ideal.Quotient.isUnit_mk_pow_of_notMem m.asIdeal hx)

theorem chinese_remainder : chinese_remainderType.{u} := by
  intro R _ _ N hN
  have hrad : nilradical R = radical R := by
    calc
      nilradical R = (⊥ : Ideal R).jacobson :=
        (IsArtinianRing.jacobson_eq_radical (⊥ : Ideal R)).symm
      _ = radical R := Ideal.jacobson_bot
  have hinf : (⨅ m : MaximalSpectrum R, m.asIdeal ^ N) = ⊥ := by
    rw [← IsArtinianRing.nilradical_pow_eq_iInf R N, hrad, hN]
  let e : R ≃+* ((m : MaximalSpectrum R) → R ⧸ m.asIdeal ^ N) :=
    (RingEquiv.quotientBot R).symm.trans
      ((Ideal.quotEquivOfEq hinf.symm).trans
        (Ideal.quotientInfRingEquivPiQuotient _
          (fun m n h => (m.isCoprime_of_ne h).pow)))
  exact ⟨e, fun x m => rfl⟩

theorem decomposition : decompositionType.{u} := by
  intro R _ _
  obtain ⟨n, hn⟩ := P103.Ch03.ArtinianRadical.nilpotent R
  have hn' : radical R ^ (n + 1) = ⊥ := by
    rw [pow_succ, hn]
    exact zero_mul _
  exact ⟨finite_maximalIdeals R, n + 1, Nat.zero_lt_succ n, hn',
    factors_local_artinian R (n + 1) (Nat.zero_lt_succ n),
    chinese_remainder R (n + 1) hn'⟩

theorem zero_ring : zero_ringType.{u} := by
  intro R _ _
  refine ⟨⟨fun m => m.isMaximal.ne_top (Subsingleton.elim _ _)⟩, ?_⟩
  exact ⟨RingEquiv.ofBijective (RingHom.pi fun _ : Fin 0 => RingHom.id R)
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩⟩

end P103.Ch03.ArtinianProduct
