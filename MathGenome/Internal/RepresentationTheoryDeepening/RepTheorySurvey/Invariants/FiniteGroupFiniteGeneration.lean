import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.Actions
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Basic

universe u v w

namespace RepTheorySurvey.Invariants.GroupAlgebraAction

/-- In any characteristic, a finite group acting on a finite-type commutative algebra
has a finite-type fixed subalgebra over which the ambient algebra is module-finite. -/
theorem finiteType_fixedSubalgebra_and_moduleFinite
    {k : Type u} {G : Type v} {A : Type w}
    [Field k] [Group G] [Finite G] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ρ : GroupAlgebraAction k G A) :
    Algebra.FiniteType k ρ.fixedSubalgebra ∧ Module.Finite ρ.fixedSubalgebra A := by
  let : MulSemiringAction G A := MulSemiringAction.compHom A ρ
  let : Algebra.IsInvariant ρ.fixedSubalgebra A G :=
    ⟨fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩
  -- Orbit polynomials give integrality over the fixed subalgebra.
  let : Algebra.IsIntegral ρ.fixedSubalgebra A := Algebra.IsInvariant.isIntegral _ _ G
  let : Algebra.FiniteType ρ.fixedSubalgebra A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k ρ.fixedSubalgebra A
  have hFinite : Module.Finite ρ.fixedSubalgebra A := Algebra.IsIntegral.finite
  -- Apply Artin–Tate to the tower through the fixed subalgebra.
  exact ⟨⟨fg_of_fg_of_fg k ρ.fixedSubalgebra A
    (Algebra.FiniteType.out (R := k) (A := A)) hFinite.fg_top Subtype.val_injective⟩, hFinite⟩

end RepTheorySurvey.Invariants.GroupAlgebraAction
