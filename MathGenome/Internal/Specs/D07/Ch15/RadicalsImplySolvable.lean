import MathGenome.Internal.Specs.D07.Ch15.RadicalDefinition
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
The three conclusions of K07.15.radicals_imply_solvable (paper.tex:4412–4435).
Radical membership is membership in an actual finite tower, using the shared
predicate. `Polynomial.Gal f` is the automorphism group over K of f's splitting
field, without a separability assumption. There is no characteristic restriction.

For the all-roots assertion Ω is the specified algebraic closure. For the
single-element and irreducible assertions any algebraic overfield suffices.
-/

universe u v
namespace Specs.D07.Ch15.RadicalsImplySolvable
open Polynomial Specs.D07.Ch15.RadicalDefinition

def RadicalMinpolyGroup : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (a : Ω),
    solvableByRadicalsValue K Ω a → Group.IsSolvable (minpoly K a).Gal

def IrreducibleRadicalRootGroup : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (f : K[X]) (a : Ω),
    Irreducible f → aeval a f = 0 → solvableByRadicalsValue K Ω a →
      Group.IsSolvable f.Gal

/-- Repeated factors and constants are allowed. The harmless zero-polynomial
case is included as well, since its splitting-field automorphism group is trivial. -/
def AllRadicalRootsGroup : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (f : K[X]),
    (∀ a : Ω, aeval a f = 0 → solvableByRadicalsValue K Ω a) →
      Group.IsSolvable f.Gal

end Specs.D07.Ch15.RadicalsImplySolvable
