import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootStrings
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RepresentationJordan
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Algebra.Group.Subgroup.Basic

/-! LA-E08 (finite module assertions), source lines 2421–2426 and 2435–2446.
The Cartan is the fixed maximal toral subalgebra of the complex semisimple
algebra. Weight spaces are ordinary simultaneous eigenspaces; zero is allowed.
The Weyl group acts on the complex dual by the usual coroot reflections.
The total definition below uses the identity away from normalized coroots;
for every root the coroot pairing is two, so this branch is immaterial. -/

noncomputable section
universe u v
namespace Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
attribute [local instance 100] LieRing.ofAssociativeRing
open RootDecomposition RootForm
open _root_.LieAlgebrasAndRepresentations.RepresentationJordan

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

def corootEvaluation (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) :
    Module.Dual ℂ (Module.Dual ℂ H) where
  toFun μ := μ (coroot_value H α)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def weightReflection (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) :
    Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H :=
  if h : α (coroot_value H α) = 2 then
    Module.reflection (x := α) (f := corootEvaluation H α) h
  else LinearEquiv.refl ℂ _

def weightWeylGroup (H : LieSubalgebra ℂ L) :
    Subgroup (Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) :=
  Subgroup.closure (weightReflection H '' rootSet_value H)

def integral_weights_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H →
    ∀ μ : Module.Dual ℂ H, weightSpace ρ H μ ≠ ⊥ →
    ∀ α : Module.Dual ℂ H, α ∈ rootSet_value H →
      ∃ z : ℤ, μ (coroot_value H α) = (z : ℂ)

def multiplicities_weyl_invariant_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H →
    ∀ (w : weightWeylGroup H) (μ : Module.Dual ℂ H),
      Module.finrank ℂ (weightSpace ρ H (w.val μ)) =
        Module.finrank ℂ (weightSpace ρ H μ)

def saturated_weights_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H →
    ∀ μ : Module.Dual ℂ H, weightSpace ρ H μ ≠ ⊥ →
    ∀ α : Module.Dual ℂ H, α ∈ rootSet_value H →
    ∀ n : ℤ, μ (coroot_value H α) = (n : ℂ) → 0 ≤ n →
    ∀ j : ℤ, 0 ≤ j → j ≤ n → weightSpace ρ H (μ - j • α) ≠ ⊥

/-- The real Weyl group acts on the Killing-induced root space. Its action
on the Cartan dual is given by complexification via the canonical extension. -/
def weyl_complexification_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
  ∀ (H : LieSubalgebra ℂ L) (d : RealRootSpace.Realization H),
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    (∀ α ∈ rootSet_value H, ∀ x : RealRootSpace.E H,
      d.j (_root_.LieAlgebrasAndRepresentations.rootReflectionEquiv
        (RealRootSpace.rootRestriction H α) x) = weightReflection H α (d.j x)) ∧
    ∃ e : _root_.LieAlgebrasAndRepresentations.rootWeylGroup (RealRootSpace.realRoots H) ≃*
        weightWeylGroup H,
      ∀ w x, d.j (w.val x) = (e w).val (d.j x)

/-- The source's weights and multiplicities refer to the same real root space
as its Weyl group. Every occurring weight has a real preimage, including zero. -/
def real_weight_multiplicities_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L),
    MaximalTori.IsMaximalToral_value H →
    ∀ d : RealRootSpace.Realization H,
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      (∀ μ : Module.Dual ℂ H, weightSpace ρ H μ ≠ ⊥ → ∃ x, d.j x = μ) ∧
      ∀ (w : _root_.LieAlgebrasAndRepresentations.rootWeylGroup (RealRootSpace.realRoots H))
        (x : RealRootSpace.E H),
        Module.finrank ℂ (weightSpace ρ H (d.j (w.val x))) =
          Module.finrank ℂ (weightSpace ρ H (d.j x))

end Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
