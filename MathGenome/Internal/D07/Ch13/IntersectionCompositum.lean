import MathGenome.Internal.Specs.D07.Ch13.IntersectionCompositum
import MathGenome.Internal.D07.Ch13.SubfieldLattice

/-! Intersections and composita of the actual embedded root fields. -/

universe u v

namespace D07.Ch13.IntersectionCompositum

open Specs.D07.Ch13.IntersectionCompositum

/-- The tower law proves the necessary divisibility; iterating the root
equation proves sufficiency. -/
theorem inclusion_iff_divides : InclusionIffDivides.{u, v} := by
  intro K Ω _ _ _ _ _ _ q a b hq ha hb
  constructor
  · intro h
    have hA := Existence.embedded_existence K Ω q a hq ha
    have hB := Existence.embedded_existence K Ω q b hq hb
    let : FiniteDimensional K (Existence.rootField K Ω q b) := hB.2.2.1
    rw [← hA.2.2.2.1, ← hB.2.2.2.1]
    exact IntermediateField.finrank_dvd_of_le_right h
  · exact SubfieldLattice.root_field_le_of_dvd K Ω q a b hq

/-- Classify the intersection inside the degree-a field and use both
divisibilities to identify its positive index with gcd(a,b). -/
theorem intersection_eq : IntersectionEquality.{u, v} := by
  intro K Ω _ _ _ _ _ _ q a b hq ha hb
  let A := Existence.rootField K Ω q a
  let B := Existence.rootField K Ω q b
  obtain ⟨d, ⟨hd, hda, hD⟩, _⟩ :=
    (SubfieldLattice.embedded_classification K Ω q a hq ha (A ⊓ B)).mp inf_le_left
  have hdb : d ∣ b := (inclusion_iff_divides K Ω q d b hq hd hb).mp (by
    rw [← hD]
    exact inf_le_right)
  have hg : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hga := (inclusion_iff_divides K Ω q (Nat.gcd a b) a hq hg ha).mpr
    (Nat.gcd_dvd_left a b)
  have hgb := (inclusion_iff_divides K Ω q (Nat.gcd a b) b hq hg hb).mpr
    (Nat.gcd_dvd_right a b)
  have hgd : Nat.gcd a b ∣ d :=
    (inclusion_iff_divides K Ω q (Nat.gcd a b) d hq hg hd).mp (by
      rw [← hD]
      exact le_inf hga hgb)
  have heq : d = Nat.gcd a b := Nat.dvd_antisymm (Nat.dvd_gcd hda hdb) hgd
  exact hD.trans (congrArg (Existence.rootField K Ω q) heq)

/-- Both fields lie in the degree-lcm field, so their supremum does too.
Classification and the least-common-multiple property identify its index. -/
theorem compositum_eq : CompositumEquality.{u, v} := by
  intro K Ω _ _ _ _ _ _ q a b hq ha hb
  let A := Existence.rootField K Ω q a
  let B := Existence.rootField K Ω q b
  have hl : 1 ≤ Nat.lcm a b := Nat.lcm_pos ha hb
  have hal := (inclusion_iff_divides K Ω q a (Nat.lcm a b) hq ha hl).mpr
    (Nat.dvd_lcm_left a b)
  have hbl := (inclusion_iff_divides K Ω q b (Nat.lcm a b) hq hb hl).mpr
    (Nat.dvd_lcm_right a b)
  obtain ⟨c, ⟨hc, hcl, hC⟩, _⟩ :=
    (SubfieldLattice.embedded_classification K Ω q (Nat.lcm a b) hq hl (A ⊔ B)).mp
      (sup_le hal hbl)
  have hac : a ∣ c := (inclusion_iff_divides K Ω q a c hq ha hc).mp (by
    rw [← hC]
    exact le_sup_left)
  have hbc : b ∣ c := (inclusion_iff_divides K Ω q b c hq hb hc).mp (by
    rw [← hC]
    exact le_sup_right)
  have heq : c = Nat.lcm a b := Nat.dvd_antisymm hcl (Nat.lcm_dvd hac hbc)
  change IntermediateField.adjoin K ((A : Set Ω) ∪ (B : Set Ω)) = _
  rw [← IntermediateField.sup_def]
  exact hC.trans (congrArg (Existence.rootField K Ω q) heq)

end D07.Ch13.IntersectionCompositum
