import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.DegreeDividesOrder
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterValueIntegrality
import MathGenome.Internal.AlgebraCore.P103.Ch08.ClassSumIntegrality
import MathGenome.Internal.AlgebraCore.P103.Ch08.UnitarityPairing
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.RingTheory.Polynomial.RationalRoot
import Batteries.Tactic.OpenPrivate

noncomputable section
universe u v
namespace P103.Ch08

open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur

namespace DegreeDividesOrder
open ClassSumIntegrality

variable {G : Type u} {V : Type v} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

local instance : Fintype (ConjClasses G) := Fintype.ofFinite _
local instance : DecidableEq (ConjClasses G) := Classical.typeDecidableEq _

/-- Row orthogonality with the source's first-variable-linear convention. -/
theorem sum_character_mul_conjugate (ρ : Representation ℂ G V)
    (hρ : Irreducible ℂ G V ρ) :
    ∑ g : G, CharacterSpecs.characterValue ρ g *
      star (CharacterSpecs.characterValue ρ g) = (Fintype.card G : ℂ) := by
  have := libraryIrreducible ρ hρ
  have h := (character_pairing ρ ρ).1
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self] at h
  simp only [UnitaritySpecs.functionPairingValue, Nat.cast_one] at h
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh := congrArg (fun z : ℂ => (Fintype.card G : ℂ) * z) h
  simpa only [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_one] using hh

/-- Grouping row orthogonality by conjugacy class yields the quotient of
order by degree as a sum of products of algebraic integers. -/
theorem sum_classScalar_mul_conjugate (ρ : Representation ℂ G V)
    (hρ : Irreducible ℂ G V ρ)
    (r : ConjClasses G → G) (hr : ∀ D, ConjClasses.mk (r D) = D) :
    ∑ D : ConjClasses G, classScalar ρ D (r D) *
      star (CharacterSpecs.characterValue ρ (r D)) =
      (Fintype.card G : ℂ) / Module.finrank ℂ V := by
  classical
  have hclass (D : ConjClasses G) (g : G) (hg : g ∈ classMembers D) :
      CharacterSpecs.characterValue ρ g = CharacterSpecs.characterValue ρ (r D) := by
    have hc : IsConj (r D) g := ConjClasses.mk_eq_mk_iff_isConj.mp
      ((hr D).trans ((mem_classMembers D g).mp hg).symm)
    obtain ⟨h, rfl⟩ := isConj_iff.mp hc
    exact character_conjugate ρ (r D) h
  calc
    _ = ∑ D : ConjClasses G, ∑ g ∈ classMembers D,
        CharacterSpecs.characterValue ρ g * star (CharacterSpecs.characterValue ρ g) /
          Module.finrank ℂ V := by
      apply Finset.sum_congr rfl
      intro D _
      calc
        _ = (classMembers D).card *
            (CharacterSpecs.characterValue ρ (r D) *
              star (CharacterSpecs.characterValue ρ (r D)) / Module.finrank ℂ V) := by
          unfold classScalar
          ring
        _ = _ := by
          symm
          calc
            _ = ∑ _g ∈ classMembers D, CharacterSpecs.characterValue ρ (r D) *
                star (CharacterSpecs.characterValue ρ (r D)) / Module.finrank ℂ V := by
              exact Finset.sum_congr rfl (fun g hg => by rw [hclass D g hg])
            _ = _ := by simp
    _ = ∑ g : G, CharacterSpecs.characterValue ρ g *
        star (CharacterSpecs.characterValue ρ g) / Module.finrank ℂ V := by
      have hm (D : ConjClasses G) : classMembers D =
          Finset.univ.filter (fun g : G => ConjClasses.mk g = D) := by
        ext g
        simp
      simp_rw [hm]
      exact Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ) (t := (Finset.univ : Finset (ConjClasses G)))
          (g := ConjClasses.mk) (fun _ _ => Finset.mem_univ _)
          (fun g : G => CharacterSpecs.characterValue ρ g *
            star (CharacterSpecs.characterValue ρ g) / Module.finrank ℂ V)
    _ = (∑ g : G, CharacterSpecs.characterValue ρ g *
        star (CharacterSpecs.characterValue ρ g)) / Module.finrank ℂ V := by
      rw [Finset.sum_div]
    _ = _ := by rw [sum_character_mul_conjugate ρ hρ]

/-- The quotient is integral before using its rationality. -/
theorem order_div_degree_integral (ρ : Representation ℂ G V)
    (hρ : Irreducible ℂ G V ρ) :
    IsIntegral ℤ ((Fintype.card G : ℂ) / Module.finrank ℂ V) := by
  classical
  let r : ConjClasses G → G := fun D => (ConjClasses.exists_rep D).choose
  have hr : ∀ D, ConjClasses.mk (r D) = D := fun D =>
    (ConjClasses.exists_rep D).choose_spec
  rw [← sum_classScalar_mul_conjugate ρ hρ r hr]
  apply IsIntegral.sum
  intro D _
  apply (scalarIntegral ρ hρ D (r D) (hr D)).mul
  rw [← character_inverse_conjugate ρ]
  exact character_integral ρ _

/-- A rational algebraic integer is an integer; clearing the nonzero
natural denominator gives divisibility in ℕ. -/
theorem dvd_of_integral_quotient (n d : ℕ) (hd : d ≠ 0)
    (hi : IsIntegral ℤ ((n : ℂ) / (d : ℂ))) : d ∣ n := by
  have hrat : (n : ℂ) / (d : ℂ) ∈ Set.range Rat.cast := by
    refine ⟨(n : ℚ) / (d : ℚ), ?_⟩
    push_cast
    rfl
  obtain ⟨z, hz⟩ := hi.mem_range_ratCast_iff.mp hrat
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have he : (n : ℂ) = (d : ℂ) * (z : ℂ) := by
    rw [hz, mul_div_cancel₀ _ hd']
  apply Int.natCast_dvd_natCast.mp
  refine ⟨z, ?_⟩
  exact_mod_cast he

end DegreeDividesOrder

/-- Every nonzero irreducible complex representation of a finite group has
degree dividing the group order. No dimension bound is assumed. -/
theorem degree_divides_order : DegreeDividesOrderSpecs.degree_divides_orderType := by
  intro G V _ _ _ _ ρ hρ
  let := Fintype.ofFinite G
  have := ClassSumIntegrality.finiteDimensional_of_irreducible ρ hρ
  have : Nontrivial V := hρ.1
  apply DegreeDividesOrder.dvd_of_integral_quotient
  · exact (Module.finrank_pos (R := ℂ) (M := V)).ne'
  · simpa only [Fintype.card_eq_nat_card] using
      DegreeDividesOrder.order_div_degree_integral ρ hρ

end P103.Ch08
