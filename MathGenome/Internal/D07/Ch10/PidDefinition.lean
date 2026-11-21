import MathGenome.Internal.Specs.D07.Ch10.PidDefinition
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.ZMod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Principal ideal domains and the principal ideal ring ℤ/4ℤ.
K07.10.pid_definition, paper.tex:1912–1917.
-/

universe u

namespace D07.Ch10.PidDefinition

open Specs.D07.Ch10.PidDefinition

/-- A PID is a nontrivial domain in which every ideal has one generator. -/
def IsPID (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ ∀ I : Ideal R, ∃ a : R, I = Ideal.span {a}

theorem principalIdealRing_iff : PrincipalIdealRingIff.{u} := by
  intro R _
  constructor
  · intro h I
    let := h
    exact Submodule.IsPrincipal.principal I
  · intro h
    exact ⟨fun I => ⟨h I⟩⟩

theorem pid_iff : PIDIff.{u} := by
  intro R _
  exact and_congr_right (fun _ => (principalIdealRing_iff R).symm)

theorem integer_ideals_above_four : IntegerIdealsAboveFour := by
  intro J
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal J
    have hJ : J = Ideal.span {(a.natAbs : ℤ)} :=
      ha.trans (Int.span_natAbs a).symm
    refine ⟨a.natAbs, ?_, hJ⟩
    have hfour : (4 : ℤ) ∈ J := (Ideal.span_singleton_le_iff_mem J).mp h
    rw [hJ, Ideal.mem_span_singleton] at hfour
    exact Int.natCast_dvd_natCast.mp hfour
  · rintro ⟨n, hn, rfl⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact Int.natCast_dvd_natCast.mpr hn

theorem divisors_four : DivisorsFour := by
  intro n
  constructor
  · intro hn
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hn
    interval_cases n <;> norm_num at *
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem zmod_four_ideal_correspondence : ZModFourIdealCorrespondence := by
  let f := Int.castRingHom (ZMod 4)
  have hf : Function.Surjective f := ZMod.intCast_surjective
  have hk : Ideal.comap f ⊥ = Ideal.span {(4 : ℤ)} := by
    rw [← RingHom.ker_eq_comap_bot]
    simpa [f] using ZMod.ker_intCastRingHom 4
  let e : Ideal (ZMod 4) ≃o {J : Ideal ℤ // Ideal.span {(4 : ℤ)} ≤ J} := {
    toFun := fun I => ⟨I.comap f, by
      rw [← hk]
      exact Ideal.comap_mono bot_le⟩
    invFun := fun J => J.val.map f
    left_inv := fun I => Ideal.map_comap_of_surjective f hf I
    right_inv := fun J => by
      apply Subtype.ext
      change (J.val.map f).comap f = J.val
      rw [Ideal.comap_map_of_surjective f hf, hk]
      exact sup_eq_left.mpr J.property
    map_rel_iff' := by
      intro I J
      exact Ideal.comap_le_comap_iff_of_surjective f hf I J }
  refine ⟨e, ?_, ?_⟩
  · intro I
    rfl
  · intro J
    exact Ideal.map_eq_image_of_surjective f hf

theorem zmod_four_ideal_generators : ZModFourIdealGenerators := by
  intro I
  let f := Int.castRingHom (ZMod 4)
  have hf : Function.Surjective f := ZMod.intCast_surjective
  have hk : Ideal.span {(4 : ℤ)} ≤ I.comap f := by
    have hker : RingHom.ker f = Ideal.span {(4 : ℤ)} := by
      simpa using ZMod.ker_intCastRingHom 4
    rw [← hker]
    exact Ideal.comap_mono bot_le
  obtain ⟨n, hn, hI⟩ := (integer_ideals_above_four (I.comap f)).mp hk
  refine ⟨n, hn, hI, ?_⟩
  calc
    I = (I.comap f).map f := (Ideal.map_comap_of_surjective f hf I).symm
    _ = Ideal.span {(n : ZMod 4)} := by
      rw [hI, Ideal.map_span]
      simp [f]

theorem zmod_four_zero_divisor : ZModFourZeroDivisor := by
  constructor <;> decide

theorem zmod_four_ideals : ZModFourIdeals := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I
    obtain ⟨n, hn, _, hI⟩ := zmod_four_ideal_generators I
    rcases (divisors_four n).mp hn with rfl | rfl | rfl
    · exact Or.inr (Or.inr (hI.trans Ideal.span_singleton_one))
    · exact Or.inr (Or.inl hI)
    · exact Or.inl (hI.trans (Ideal.span_singleton_eq_bot.mpr (by decide)))
  · intro h
    have htwo := Ideal.mem_span_singleton_self (2 : ZMod 4)
    rw [← h] at htwo
    exact zmod_four_zero_divisor.1 htwo
  · intro h
    have h1 : (1 : ZMod 4) ∈ Ideal.span {(2 : ZMod 4)} := by
      rw [h]
      trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have hzero : (2 : ZMod 4) = 0 := by
      calc
        (2 : ZMod 4) = 1 * 2 := (one_mul _).symm
        _ = (a * 2) * 2 := by rw [ha]
        _ = 0 := by rw [mul_assoc, zmod_four_zero_divisor.2, mul_zero]
    exact zmod_four_zero_divisor.1 hzero
  · intro h
    have h1 : (1 : ZMod 4) ∈ (⊥ : Ideal (ZMod 4)) := by rw [h]; trivial
    exact (by decide : (1 : ZMod 4) ≠ 0) h1

theorem zmod_four_principal_not_domain : ZModFourPrincipalNotDomain := by
  have hprincipal : IsPrincipalIdealRing (ZMod 4) := by
    apply (principalIdealRing_iff (ZMod 4)).mpr
    intro I
    obtain ⟨n, _, _, hn⟩ := zmod_four_ideal_generators I
    exact ⟨n, hn⟩
  have hdomain : ¬ IsDomain (ZMod 4) := by
    intro h
    let := h
    rcases mul_eq_zero.mp zmod_four_zero_divisor.2 with hz | hz <;>
      exact zmod_four_zero_divisor.1 hz
  exact ⟨hprincipal, hdomain, fun h => hdomain h.1⟩

end D07.Ch10.PidDefinition
