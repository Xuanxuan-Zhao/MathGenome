import MathGenome.Internal.Specs.D07.Ch08.ZeroRing
import MathGenome.Internal.D07.Ch08.RingDefinition
import Mathlib.Algebra.Ring.PUnit

/-!
The zero ring, K07.08.zero_ring (paper.tex:1179–1190).
No nontriviality or commutativity hypothesis is imposed on the arbitrary
unital rings in these results. The existence statement uses the canonical
commutative ring on `PUnit`.
-/

universe u

namespace D07.Ch08.ZeroRing

open Specs.D07.Ch08.ZeroRing

/-- If zero equals one, multiplication by the identity makes every element zero. -/
theorem zeroEqOneIffSubsingleton : ZeroEqOneIffSubsingleton.{u} := by
  intro R _
  constructor
  · intro h
    have hz (a : R) : a = 0 := by
      calc
        a = a * 1 := (mul_one a).symm
        _ = a * 0 := congrArg (fun x : R => a * x) h.symm
        _ = 0 := D07.Ch08.RingDefinition.mulZero R a
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩
  · intro h
    exact h.elim 0 1

/-- An explicit formulation of having exactly one element. -/
theorem zeroEqOneIffUniqueElement : ZeroEqOneIffUniqueElement.{u} := by
  intro R _
  constructor
  · intro h
    have hs : Subsingleton R := (zeroEqOneIffSubsingleton R).mp h
    exact ⟨0, True.intro, fun a _ => hs.elim a 0⟩
  · rintro ⟨a, _, ha⟩
    exact (ha 0 True.intro).trans (ha 1 True.intro).symm

/-- The standard one-element type supplies an actual commutative unital ring. -/
theorem oneElementRingExists : OneElementRingExists.{u} := by
  refine ⟨PUnit.{u + 1}, inferInstance, PUnit.unit, True.intro, ?_⟩
  intro a _
  exact Subsingleton.elim a PUnit.unit

/-- A one-element ring fails the nontriviality required of a domain. -/
theorem notDomain : NotDomain.{u} := by
  intro R _ _ h
  obtain ⟨a, b, hab⟩ := h.toNontrivial.exists_pair_ne
  exact hab (Subsingleton.elim a b)

/-- A one-element ring fails the nontriviality required of a field. -/
theorem notField : NotField.{u} := by
  intro R _ _ h
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact hab (Subsingleton.elim a b)

/-- In the one-element ring, zero is self-inverse and every element is a unit. -/
theorem unitsOfOneElementRing : UnitsOfOneElementRing.{u} := by
  intro R _ _
  have h : (0 : R) * 0 = 1 := Subsingleton.elim _ _
  refine ⟨h, ?_⟩
  intro a
  exact ⟨⟨a, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩

end D07.Ch08.ZeroRing
