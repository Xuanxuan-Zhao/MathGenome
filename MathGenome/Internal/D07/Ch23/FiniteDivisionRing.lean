import MathGenome.Internal.Specs.D07.Ch23.FiniteDivisionRing
import Mathlib.RingTheory.LittleWedderburn

/-!
Wedderburn's finite-division-ring theorem (K07.23.finite_division_ring).
The library theorem takes only a division ring and finiteness of its
underlying type. Its field structure extends the given division-ring
structure; no commutativity assumption is added to the inputs.
-/

universe u

namespace D07.Ch23.FiniteDivisionRing

open Specs.D07.Ch23.FiniteDivisionRing

theorem commutative : Commutative.{u} := by
  intro D _ _ a b
  let _ : Field D := littleWedderburn D
  exact mul_comm a b

theorem finite_field : FiniteField.{u} := by
  intro D d _
  exact ⟨littleWedderburn D, rfl⟩

end D07.Ch23.FiniteDivisionRing
