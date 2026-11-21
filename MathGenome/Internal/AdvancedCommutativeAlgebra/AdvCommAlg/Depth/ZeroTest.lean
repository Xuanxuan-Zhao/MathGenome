import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ZeroTest
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! The zero-grade and zero-depth tests in DP-01, paper.tex:2636–2658. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R]

/-- If `IM ≠ M`, grade zero means that no element of `I` acts injectively. -/
theorem grade_zero_iff_no_regular (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    grade I M = 0 ↔ ∀ a ∈ I, ¬ IsSMulRegular M a := by
  constructor
  · intro hg a ha hreg
    have hs : RegularSequence.Regular M [a] := by
      refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff M a).mpr hreg, ?_⟩
      exact (ne_top_of_le_ne_top hI (Submodule.smul_mono_left
        (Ideal.span_le.mpr (by simpa using ha)))).symm
    have hlen : (1 : ℕ∞) ≤ grade I M := by
      rw [grade_of_smul_ne_top I M hI]
      exact le_sSup ⟨[a], hs, by simpa using ha, rfl⟩
    simp [hg] at hlen
  · intro h
    rw [grade_of_smul_ne_top I M hI]
    apply le_antisymm _ bot_le
    apply sSup_le
    rintro _ ⟨x, hx, hIx, rfl⟩
    cases x with
    | nil => simp
    | cons a xs =>
      exact False.elim (h a (hIx a (by simp))
        ((RingTheory.Sequence.isWeaklyRegular_cons_iff M a xs).mp
          hx.toIsWeaklyRegular).1)

/-- Finite prime avoidance converts the zero-divisor test to an associated prime. -/
theorem grade_zero_iff_exists_associatedPrime [IsNoetherianRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    grade I M = 0 ↔ ∃ p ∈ associatedPrimes R M, I ≤ p := by
  rw [grade_zero_iff_no_regular I M hI]
  have hav := Ideal.subset_union_prime_finite (associatedPrimes.finite R M)
    (f := id) (⊥ : Ideal R) ⊥ (fun _ hp _ _ => hp.isPrime) (I := I)
  simp only [id_eq] at hav
  rw [biUnion_associatedPrimes_eq_compl_regular R M] at hav
  exact hav

/-- The annihilator `0 :_M I` is nonzero exactly at grade zero. -/
theorem grade_zero_iff_annihilator_ne_bot [IsNoetherianRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    grade I M = 0 ↔ Submodule.torsionBySet R M (I : Set R) ≠ ⊥ := by
  constructor
  · intro hg
    obtain ⟨p, hp, hIp⟩ := (grade_zero_iff_exists_associatedPrime I M hI).mp hg
    obtain ⟨hprime, x, rfl⟩ := isAssociatedPrime_iff.mp hp
    have hx : x ≠ 0 := by
      intro hx
      apply hprime.ne_top
      simp [hx]
    have hxmem : x ∈ Submodule.torsionBySet R M (I : Set R) := by
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using hIp a.property
    intro hbot
    exact hx (by simpa only [hbot, Submodule.mem_bot] using hxmem)
  · intro hAnn
    apply (grade_zero_iff_no_regular I M hI).mpr
    intro a ha hreg
    apply hAnn
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    exact hreg.right_eq_zero_of_smul
      ((Submodule.mem_torsionBySet_iff _ _).mp hx ⟨a, ha⟩)

/-- Nakayama gives the local hypothesis `mM ≠ M`; its annihilator is the socle. -/
theorem depth_zero_iff_socle_ne_bot (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M] :
    depth R M = 0 ↔
      Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R) ≠ ⊥ := by
  apply grade_zero_iff_annihilator_ne_bot
  exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm

end AdvCommAlg.Depth
