import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Order.Atoms

/-! LA-G03. The Verma module and its distinguished vector are those of
LA-G01–G02. Simplicity means that the lattice of Lie submodules has
exactly two elements. Module universes are independent of the Lie
algebra universe, and there is no nonzero assumption on the Lie algebra. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient

open VermaModules VermaWeightsUniversal
open SerreRelations (simple)
open SolvableRadical (IsSemisimple_value)

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

abbrev RaisingVectors (H : LieSubalgebra ℂ L) (φ : Direction H) (e : simple H φ → L) : Prop :=
  ∀ i, e i ∈ RootDecomposition.rootSpace_value H i.val ∧ e i ≠ 0

/-- A nonzero vector of weight `lam` killed by the simple positive-root
vectors and generating the whole module. -/
def IsHighestWeight {H : LieSubalgebra ℂ L} {φ : Direction H}
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    (e : simple H φ → L) (lam : Module.Dual ℂ H) (x : V) : Prop :=
  x ≠ 0 ∧ (∀ h : H, ⁅(h : L), x⁆ = lam h • x) ∧ (∀ i, ⁅e i, x⁆ = 0) ∧
    LieSubmodule.lieSpan ℂ L ({x} : Set V) = ⊤

/-- The simple-root equations in the universal property agree with the
Chapter 7 convention that the entire positive nilpotent subalgebra kills
a highest-weight vector. -/
def highest_weight_iff_positive_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H) (e : simple H φ → L), RaisingVectors H φ e →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      (lam : Module.Dual ℂ H) (x : V),
    IsHighestWeight e lam x ↔
      x ≠ 0 ∧ (∀ h : H, ⁅(h : L), x⁆ = lam h • x) ∧
        (∀ z : positive_value H φ, ⁅(z : L), x⁆ = 0) ∧
        LieSubmodule.lieSpan ℂ L ({x} : Set V) = ⊤

variable (H : LieSubalgebra ℂ L) (φ : Direction H)
  (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)

local instance : LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance : LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

/-- The sum of all proper Lie submodules of the Verma module. -/
def maximalSubmodule_value : LieSubmodule ℂ L (induced_value H φ χ) :=
  sSup {N | N ≠ ⊤}

def maximalSubmodule_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    LieSubmodule ℂ L (induced_value H φ χ)

/-- The module `L(lam)` with `χ` the character of weight `lam`. -/
abbrev simpleQuotient_value := induced_value H φ χ ⧸ maximalSubmodule_value H φ χ

def simpleQuotient_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H)
    (_ : U (borel_value H φ) →ₐ[ℂ] ℂ), Type u

abbrev quotientMap := LieSubmodule.Quotient.mk' (maximalSubmodule_value H φ χ)

abbrev quotientHighestVector := quotientMap H φ χ (highestVector_value H φ χ)

def maximal_submodule_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    IsGreatest {N : LieSubmodule ℂ L (induced_value H φ χ) | N ≠ ⊤}
      (maximalSubmodule_value H φ χ)

/-- The actual quotient is simple and the image of the Verma generator
is a highest-weight generator. -/
def simple_quotient_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ∀ e : simple H φ → L, RaisingVectors H φ e →
    IsSimpleOrder (LieSubmodule ℂ L (simpleQuotient_value H φ χ)) ∧
      IsHighestWeight e lam (quotientHighestVector H φ χ)

/-- For each weight the inducing character exists, and its Verma module
has a greatest proper submodule and a simple highest-weight quotient. -/
def exists_simple_quotient_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (e : simple H φ → L), RaisingVectors H φ e →
    ∃ χ : U (borel_value H φ) →ₐ[ℂ] ℂ, IsWeightCharacter H φ lam χ ∧
      IsGreatest {N : LieSubmodule ℂ L (induced_value H φ χ) | N ≠ ⊤}
        (maximalSubmodule_value H φ χ) ∧
      IsSimpleOrder (LieSubmodule ℂ L (simpleQuotient_value H φ χ)) ∧
      IsHighestWeight e lam (quotientHighestVector H φ χ)

/-- Every nonzero highest-weight module of this weight surjects onto the
simple quotient by a map sending its specified generator to the canonical one. -/
def highest_weight_surjects_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ∀ e : simple H φ → L, RaisingVectors H φ e →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      (x : V), IsHighestWeight e lam x →
    ∃! f : V →ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ,
      f x = quotientHighestVector H φ χ ∧ Function.Surjective f

/-- Uniqueness of the simple quotient as a module with its specified
generator, for any simple quotient map out of the Verma module. -/
def unique_simple_quotient_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      [IsSimpleOrder (LieSubmodule ℂ L V)]
      (p : induced_value H φ χ →ₗ⁅ℂ,L⁆ V), Function.Surjective p →
    ∃! i : V ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ,
      i (p (highestVector_value H φ χ)) = quotientHighestVector H φ χ

/-- Every finite-dimensional simple module has a highest-weight
generator and is the corresponding simple quotient. -/
def finite_simple_quotient_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ e : simple H φ → L, RaisingVectors H φ e →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      [FiniteDimensional ℂ V] [IsSimpleOrder (LieSubmodule ℂ L V)],
    ∃ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) (x : V),
      IsWeightCharacter H φ lam χ ∧ IsHighestWeight e lam x ∧
      ∃ i : V ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ, i x = quotientHighestVector H φ χ

/-- The weight is determined by the module even if the isomorphism does
not carry one chosen generator to the other. -/
def highest_weight_eq_of_equiv_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ e : simple H φ → L, RaisingVectors H φ e →
    ∀ (V : Type v) (W : Type w)
      [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
      (lam mu : Module.Dual ℂ H) (x : V) (y : W),
    IsHighestWeight e lam x → IsHighestWeight e mu y → (V ≃ₗ⁅ℂ,L⁆ W) → lam = mu

end Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
