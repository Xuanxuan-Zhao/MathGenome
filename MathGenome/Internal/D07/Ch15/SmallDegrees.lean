import MathGenome.Internal.Specs.D07.Ch15.SmallDegrees
import MathGenome.Internal.D07.Ch15.RadicalEquivalenceCharZero
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
Polynomials of degree at most four are solvable by radicals.
The splitting-field automorphism group acts faithfully on the distinct
roots, even for a polynomial with repeated factors. The number of these
roots is bounded by the degree. Thus its group embeds in a solvable
symmetric group; the characteristic-zero radical equivalence finishes.
Using the distinct root set directly also covers constants and avoids
requiring the original polynomial to be separable.
-/

universe u v

namespace D07.Ch15.SmallDegrees

open Polynomial

/-- The group-theoretic part does not require characteristic zero. -/
theorem galois_group_solvable_of_natDegree_le_four
    {K : Type u} [Field K] (f : K[X]) (hf : f.natDegree ≤ 4) :
    Group.IsSolvable f.Gal := by
  classical
  have : Fact ((f.map (algebraMap K f.SplittingField)).Splits) :=
    ⟨SplittingField.splits f⟩
  have hcard : Nat.card (f.rootSet f.SplittingField) ≤ 4 :=
    (f.ncard_rootSet_le f.SplittingField).trans hf
  have : Group.IsSolvable (Equiv.Perm (f.rootSet f.SplittingField)) :=
    Equiv.Perm.isSolvable hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := Gal.galActionHom f f.SplittingField)
    (Gal.galActionHom_injective f f.SplittingField)

theorem degree_le_four_solvable_by_radicals :
    Specs.D07.Ch15.SmallDegrees.DegreeAtMostFourSolvable.{u, v} := by
  intro K Ω _ _ _ _ _ _ f hf hdegree
  exact (RadicalEquivalenceCharZero.radical_equivalence K Ω f hf).mpr
    (galois_group_solvable_of_natDegree_le_four f hdegree)

end D07.Ch15.SmallDegrees
