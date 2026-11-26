import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Tactic.Abel

noncomputable section

namespace Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations

open OrderedValuationGroups (valueGroup value)
open ValuationPrimesAndConvexSubgroups (convexAddSubgroup PrimeValues ringValue)
open Additive (ofMul)

section OrderedQuotient

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  (H : convexAddSubgroup Γ)

/-- The additive quotient by a convex subgroup, with its quotient order. -/
def OrderedQuotient := Γ ⧸ H.1

instance : AddCommGroup (OrderedQuotient H) :=
  inferInstanceAs (AddCommGroup (Γ ⧸ H.1))

def quotientMap : Γ →+ OrderedQuotient H := QuotientAddGroup.mk' H.1

omit [IsOrderedAddMonoid Γ] in
theorem quotientMap_surjective : Function.Surjective (quotientMap H) :=
  QuotientAddGroup.mk'_surjective H.1

omit [IsOrderedAddMonoid Γ] in
theorem quotientMap_eq_iff (a b : Γ) :
    quotientMap H a = quotientMap H b ↔ a - b ∈ H.1 :=
  QuotientAddGroup.eq_iff_sub_mem

instance : LE (OrderedQuotient H) where
  le x y := ∃ a b : Γ, quotientMap H a = x ∧ quotientMap H b = y ∧ a ≤ b

theorem quotientMap_le_iff (a b : Γ) :
    quotientMap H a ≤ quotientMap H b ↔ ∃ h ∈ H.1, a ≤ b + h := by
  constructor
  · rintro ⟨a', b', ha', hb', hab⟩
    have ha := (quotientMap_eq_iff H a a').mp ha'.symm
    have hb := (quotientMap_eq_iff H b' b).mp hb'
    refine ⟨(a - a') + (b' - b), H.1.add_mem ha hb, ?_⟩
    calc
      a = a' + (a - a') := by abel
      _ ≤ b' + (a - a') := add_le_add_left hab _
      _ = b + ((a - a') + (b' - b)) := by abel
  · rintro ⟨h, hh, hab⟩
    refine ⟨a, b + h, rfl, (quotientMap_eq_iff H _ _).mpr ?_, hab⟩
    rwa [add_sub_cancel_left]

instance : LinearOrder (OrderedQuotient H) where
  le_refl := by
    intro x
    obtain ⟨a, rfl⟩ := quotientMap_surjective H x
    exact ⟨a, a, rfl, rfl, le_rfl⟩
  le_trans := by
    intro x y z hxy hyz
    obtain ⟨a, rfl⟩ := quotientMap_surjective H x
    obtain ⟨b, rfl⟩ := quotientMap_surjective H y
    obtain ⟨c, rfl⟩ := quotientMap_surjective H z
    obtain ⟨h, hh, hab⟩ := (quotientMap_le_iff H a b).mp hxy
    obtain ⟨k, hk, hbc⟩ := (quotientMap_le_iff H b c).mp hyz
    have hbc' : b + h ≤ c + (k + h) := by
      simpa only [add_assoc] using add_le_add_left hbc h
    exact (quotientMap_le_iff H a c).mpr ⟨k + h, H.1.add_mem hk hh, hab.trans hbc'⟩
  le_antisymm := by
    intro x y hxy hyx
    obtain ⟨a, rfl⟩ := quotientMap_surjective H x
    obtain ⟨b, rfl⟩ := quotientMap_surjective H y
    obtain ⟨h, hh, hab⟩ := (quotientMap_le_iff H a b).mp hxy
    obtain ⟨k, hk, hba⟩ := (quotientMap_le_iff H b a).mp hyx
    apply (quotientMap_eq_iff H a b).mpr
    have hu : a - b ≤ h := sub_le_iff_le_add.mpr (by simpa only [add_comm] using hab)
    have hl : b - a ≤ k := sub_le_iff_le_add.mpr (by simpa only [add_comm] using hba)
    exact H.2 (H.1.neg_mem hk) hh
      (by simpa only [neg_sub] using neg_le_neg hl) hu
  le_total := by
    intro x y
    obtain ⟨a, rfl⟩ := quotientMap_surjective H x
    obtain ⟨b, rfl⟩ := quotientMap_surjective H y
    exact (le_total a b).imp (fun h ↦ ⟨a, b, rfl, rfl, h⟩) (fun h ↦ ⟨b, a, rfl, rfl, h⟩)
  toDecidableLE := Classical.decRel _

instance : IsOrderedAddMonoid (OrderedQuotient H) where
  add_le_add_left := by
    rintro x y ⟨a, b, rfl, rfl, h⟩ z
    obtain ⟨c, rfl⟩ := quotientMap_surjective H z
    exact ⟨a + c, b + c, map_add _ _ _, map_add _ _ _, add_le_add_left h c⟩

end OrderedQuotient

universe u

variable {K : Type u} [Field K] (V : ValuationSubring K) (P : PrimeSpectrum V)

/-- The nonnegative part of the subgroup consists of the values outside the prime. -/
def Associated (H : convexAddSubgroup (valueGroup V)) : Prop :=
  ∀ g : valueGroup V, 0 ≤ g → (g ∈ H.1 ↔ PrimeValues V P g)

/-- The localization inside the original fraction field has the ordered quotient valuation. -/
def IsCoarsening (H : convexAddSubgroup (valueGroup V)) : Prop :=
  ∃ e : valueGroup (V.ofPrime P.asIdeal) ≃+o OrderedQuotient H,
    ∀ a : Additive Kˣ, e (value (V.ofPrime P.asIdeal) a) = quotientMap H (value V a)

/-- The canonical composite from the valuation ring to the fraction field of its prime quotient. -/
def residueMap : V →+* P.asIdeal.ResidueField :=
  (algebraMap (V ⧸ P.asIdeal) P.asIdeal.ResidueField).comp (Ideal.Quotient.mk P.asIdeal)

theorem residueMap_ne_zero {x : V} (hx : x ∉ P.asIdeal) : residueMap V P x ≠ 0 := by
  change algebraMap (V ⧸ P.asIdeal) P.asIdeal.ResidueField
    (Ideal.Quotient.mk P.asIdeal x) ≠ 0
  exact fun h ↦ hx (Ideal.Quotient.eq_zero_iff_mem.mp
    (IsFractionRing.injective (V ⧸ P.asIdeal) P.asIdeal.ResidueField (h.trans (map_zero _).symm)))

theorem notMem_ne_zero {x : V} (hx : x ∉ P.asIdeal) : x ≠ 0 :=
  fun h ↦ hx (h.symm ▸ P.asIdeal.zero_mem)

/-- The image in the fraction field of an element outside the prime, as a unit. -/
def residueUnit (x : V) (hx : x ∉ P.asIdeal) : P.asIdeal.ResidueFieldˣ :=
  Units.mk0 (residueMap V P x) (residueMap_ne_zero V P hx)

/-- The prime quotient, embedded in its fraction field, has value group the convex subgroup. -/
def HasResidueValuation (H : convexAddSubgroup (valueGroup V)) : Prop :=
  ∃ W : ValuationSubring P.asIdeal.ResidueField,
    (∀ x, x ∈ W ↔ x ∈ (residueMap V P).range) ∧
    ∃ e : valueGroup W ≃+o H.1,
      (∀ (a : V) (ha : a ∉ P.asIdeal),
        (e (value W (ofMul (residueUnit V P a ha))) : valueGroup V) =
          ringValue V a (notMem_ne_zero V P ha)) ∧
      (∀ (a b : V) (ha : a ∉ P.asIdeal) (hb : b ∉ P.asIdeal),
        (e (value W (ofMul (residueUnit V P a ha / residueUnit V P b hb))) : valueGroup V) =
          ringValue V a (notMem_ne_zero V P ha) - ringValue V b (notMem_ne_zero V P hb))

def Coarsening : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K) (P : PrimeSpectrum V)
    (H : convexAddSubgroup (valueGroup V)), Associated V P H → IsCoarsening V P H

def ResidueValuation : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K) (P : PrimeSpectrum V)
    (H : convexAddSubgroup (valueGroup V)), Associated V P H → HasResidueValuation V P H

def CoarseningAndResidue : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K) (P : PrimeSpectrum V),
    ∃ H : convexAddSubgroup (valueGroup V),
      Associated V P H ∧ IsCoarsening V P H ∧ HasResidueValuation V P H

/-- At zero the coarsening is the fraction field. At the maximal ideal the coarsening
is the original ring and the residue quotient already fills its fraction field. -/
def ExtremePrimes : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    let O : PrimeSpectrum V := ⊥
    let M : PrimeSpectrum V := ⟨IsLocalRing.maximalIdeal V, inferInstance⟩
    (V.ofPrime O.asIdeal = ⊤ ∧
      ∃ H : convexAddSubgroup (valueGroup V),
        Associated V O H ∧ H.1 = ⊤ ∧ IsCoarsening V O H ∧ HasResidueValuation V O H) ∧
    (V.ofPrime M.asIdeal = V ∧ Function.Surjective (residueMap V M) ∧
      ∃ H : convexAddSubgroup (valueGroup V),
        Associated V M H ∧ H.1 = ⊥ ∧ IsCoarsening V M H ∧ HasResidueValuation V M H)

end Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations
