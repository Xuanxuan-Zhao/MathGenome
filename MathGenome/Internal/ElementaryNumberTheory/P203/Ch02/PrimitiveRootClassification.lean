import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.PrimitiveRootClassification
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.MultiplicativeCyclicity
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! Classification and count of primitive-root classes, Theorem 2.5.
The positive-modulus classification specializes Mathlib's theorem. The count
uses the shared finite cyclic generator count, transported from units to their
underlying residue classes; no unit is presumed to be a generator.
-/

namespace P203.Ch02

open P203Specs.Ch02

theorem primitiveRootClassification : PrimitiveRootClassification := by
  intro m hm
  simpa only [hm.ne', false_or] using ZMod.isCyclic_units_iff m

/-- Forgetting the unit structure identifies generating units with exactly
the primitive-root residue classes. A unit is determined by its residue value. -/
private noncomputable def primitiveRootClassEquiv (m : ℕ) :
    {g : ResidueUnits m // Subgroup.zpowers g = ⊤} ≃
      {x : ZMod m // IsPrimitiveRootClass m x} :=
  Equiv.ofBijective
    (fun g => ⟨(g.val : ZMod m), g.val, rfl, g.property⟩)
    ⟨by
      intro g h heq
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val heq,
    by
      rintro ⟨x, g, hg, hgen⟩
      exact ⟨⟨g, hgen⟩, Subtype.ext hg⟩⟩

theorem primitiveRootCount : PrimitiveRootCount := by
  intro m hm hc
  let : NeZero m := ⟨hm.ne'⟩
  let : IsCyclic (ResidueUnits m) := hc
  have hd : 0 < totient m := Nat.card_pos (α := ResidueUnits m)
  calc
    Nat.card {x : ZMod m // IsPrimitiveRootClass m x} =
        Nat.card {g : ResidueUnits m // Subgroup.zpowers g = ⊤} :=
      (Nat.card_congr (primitiveRootClassEquiv m)).symm
    _ = totient (totient m) :=
      cyclicGeneratorCount (ResidueUnits m) (totient m) hd rfl

theorem primitiveRootRepresentatives : PrimitiveRootRepresentatives := by
  intro m hm x
  let : NeZero m := ⟨hm.ne'⟩
  have hx : ((x.val : ℤ) : ZMod m) = x := by
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val x
  exact ⟨(x.val : ℤ), hx, by rw [IsPrimitiveRootMod, hx]⟩

end P203.Ch02
