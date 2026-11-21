import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootStrings
import Mathlib.Algebra.Lie.Subalgebra

/-! LA-F02-Relations, source res:F02, lines 2542–2576.
Only the assertion in an existing semisimple algebra belongs to this goal.
A positive system is specified by a real linear functional regular on the
roots; on the real root space this is the source's pairing with a regular
vector. Simple roots are precisely its indecomposable positive roots.
The indexing subtype includes every simple root exactly once, including the
empty system. The chosen vectors are arbitrary nonzero normalized root vectors.
Cartan entries are integers whose complex values are α_j(h_i); thus the
orientation and the exponent `1 - a_ij` agree with (6.1). -/

open scoped Classical
universe u
namespace Specs.LieAlgebrasAndRepresentations.SerreRelations
open RootDecomposition RootForm

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

def positive (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :
    Set (Module.Dual ℂ H) := {α | α ∈ rootSet_value H ∧ 0 < φ α}

def simple (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :
    Set (Module.Dual ℂ H) :=
  {α | α ∈ positive H φ ∧
    ∀ β ∈ positive H φ, ∀ γ ∈ positive H φ, α ≠ β + γ}

/-- The original, unconditional target. No root-string theorem is assumed here. -/
def serre_relations_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ),
      (∀ α ∈ rootSet_value H, φ α ≠ 0) →
    ∀ e f : simple H φ → L,
      (∀ i, e i ∈ rootSpace_value H i.val ∧
        f i ∈ rootSpace_value H (-i.val) ∧ e i ≠ 0 ∧ f i ≠ 0 ∧
        ⁅e i, f i⁆ = (coroot_value H i.val : L)) →
    ∃ A : simple H φ → simple H φ → ℤ,
      (∀ i j, j.val (coroot_value H i.val) = (A i j : ℂ)) ∧
      (∀ i j,
        ⁅(coroot_value H i.val : L), (coroot_value H j.val : L)⁆ = 0 ∧
        ⁅(coroot_value H i.val : L), e j⁆ = (A i j : ℂ) • e j ∧
        ⁅(coroot_value H i.val : L), f j⁆ = -(A i j : ℂ) • f j ∧
        ⁅e i, f j⁆ = if i = j then (coroot_value H i.val : L) else 0) ∧
      (∀ i j, i ≠ j → A i j ≤ 0 ∧
        ((LieAlgebra.ad ℂ L (e i)) ^ (1 - A i j).toNat) (e j) = 0 ∧
        ((LieAlgebra.ad ℂ L (f i)) ^ (1 - A i j).toNat) (f j) = 0) ∧
      LieSubalgebra.lieSpan ℂ L
        (Set.range e ∪ Set.range f ∪
          Set.range (fun i : simple H φ => (coroot_value H i.val : L))) = ⊤

end Specs.LieAlgebrasAndRepresentations.SerreRelations
