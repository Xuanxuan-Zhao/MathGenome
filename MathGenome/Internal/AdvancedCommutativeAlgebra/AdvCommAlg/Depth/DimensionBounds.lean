import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.DimensionBounds
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! Dimension drop, local depth bound, and bounded regular lengths (DP-02). -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

section Local
variable [IsLocalRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

theorem supportDim_quotSMulTop_add_one (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : Function.Injective (fun m : M => x • m)) :
    Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M :=
  Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hx

theorem regular_length_le_supportDim (x : List R) (hx : RegularSequence.Regular M x) :
    (x.length : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have hq : Nontrivial (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) :=
    Submodule.Quotient.nontrivial_iff.mpr hx.top_ne_smul.symm
  have hd := Module.supportDim_ne_bot_of_nontrivial R
    (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M))
  have hn : (0 : WithBot ℕ∞) ≤
      Module.supportDim R (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) := by
    rw [← WithBot.coe_unbot _ hd]
    exact WithBot.coe_le_coe.mpr zero_le
  calc
    (x.length : WithBot ℕ∞) ≤
        Module.supportDim R (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) + x.length :=
      le_add_of_nonneg_left hn
    _ = Module.supportDim R M := Module.supportDim_add_length_eq_supportDim_of_isRegular x hx

theorem depth_le_supportDim : (depth R M : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  rw [depth_eq_grade, grade_of_smul_ne_top _ _ hproper]
  rw [← WithBot.coe_unbot _ (Module.supportDim_ne_bot_of_nontrivial R M)]
  apply WithBot.coe_le_coe.mpr
  apply sSup_le
  rintro _ ⟨x, hx, _, rfl⟩
  have h := regular_length_le_supportDim M x hx
  rw [← WithBot.coe_unbot _ (Module.supportDim_ne_bot_of_nontrivial R M)] at h
  exact WithBot.coe_le_coe.mp h

end Local

/-- Localize at one prime in the support of `M/IM`.  This prime is fixed
before choosing the regular list, so the local dimension gives a uniform bound. -/
theorem regular_lengths_bounded (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    ∃ n : ℕ, ∀ x : List R, RegularSequence.Regular M x →
      (∀ a ∈ x, a ∈ I) → x.length ≤ n := by
  have : Nontrivial (M ⧸ (I • ⊤ : Submodule R M)) :=
    Submodule.Quotient.nontrivial_iff.mpr hI
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R)
    (M := M ⧸ (I • ⊤ : Submodule R M))
  rw [Module.support_quotient] at hp
  have : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp.1
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  let m := IsLocalRing.maximalIdeal S
  refine ⟨m.spanFinrank, ?_⟩
  intro x hx hxI
  have hxp : Ideal.ofList x ≤ p.asIdeal :=
    Ideal.span_le.mpr fun a ha => hp.2 (hxI a ha)
  have hreg := RegularSequence.regular_localizedModule M p.asIdeal x hxp hx
  have hdim := (regular_length_le_supportDim N _ hreg).trans
    (Module.supportDim_le_ringKrullDim S N)
  have hbound : ringKrullDim S ≤ (m.spanFinrank : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr (m.height_le_spanFinrank Ideal.IsPrime.ne_top')
  have hlen : (x.length : WithBot ℕ∞) ≤ (m.spanFinrank : WithBot ℕ∞) := by
    simpa only [List.length_map] using hdim.trans hbound
  exact_mod_cast hlen

end AdvCommAlg.Depth
