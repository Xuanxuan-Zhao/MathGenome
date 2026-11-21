import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestRoot
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootForm
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card

/-! The principal triple and its exponents, LA-E09, source lines 2448–2498.
The positive system, the simple roots and the dominance order are those of the
highest-root specification. Heights count simple roots with repetition. -/

noncomputable section
open scoped Classical

universe u v
namespace LieAlgebrasAndRepresentations.PrincipalTriple

open HighestRoot
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
open Specs.LieAlgebrasAndRepresentations.RootForm
open Specs.LieAlgebrasAndRepresentations.Sl2Model
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Module.Dual ℝ (Module.Dual ℂ H))

/-- On positive roots this is the sum of the nonnegative simple-root coefficients. -/
def positiveHeight (α : Module.Dual ℂ H) : ℕ :=
  sInf {n | ∃ l : List (_root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ),
    l.length = n ∧ (l.map Subtype.val).sum = α}

/-- The root count at positive heights, with the Cartan dimension at height zero. -/
def heightCount (m : ℕ) : ℕ :=
  if m = 0 then Module.finrank ℂ H
  else {α ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ | positiveHeight H φ α = m}.ncard

/-- The volume's convention for the Coxeter number at the highest root. -/
def coxeterNumber (θ : Module.Dual ℂ H) : ℕ := 1 + positiveHeight H φ θ

variable [FiniteDimensional ℂ L]

/-- Twice the half-sum of positive coroots, in the actual Cartan subalgebra. -/
def twiceCorootRho : H := ∑ᶠ α ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ, coroot_value H α

/-- Choices of simple root triples and coordinates of twice the coroot half-sum. -/
structure SimpleTripleData where
  e : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ → L
  f : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ → L
  c : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ → ℂ
  e_mem (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) : e a ∈ rootSpace_value H a
  f_mem (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) : f a ∈ rootSpace_value H (-a.val)
  triple (a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ) : IsSl2Triple (coroot_value H a : L) (e a) (f a)
  coroot_sum : (∑ᶠ a : _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ, c a • coroot_value H a) = twiceCorootRho H φ

def principalE (d : SimpleTripleData H φ) : L := ∑ᶠ a, d.e a

def principalF (d : SimpleTripleData H φ) : L := ∑ᶠ a, d.c a • d.f a

/-- Internal direct sum on the adjoint module pulled back along the embedding
of the matrix `sl₂` with the stated principal generators. -/
def HasExponentDecomposition (j : Model ℂ →ₗ⁅ℂ⁆ L)
    (θ : Module.Dual ℂ H) : Prop :=
  letI : LieRingModule (Model ℂ) L := LieRingModule.compLieHom L j
  letI : LieModule ℂ (Model ℂ) L := LieModule.compLieHom L j
  ∃ S : Set (LieSubmodule ℂ (Model ℂ) L), S.Finite ∧
    DirectSum.IsInternal (fun W : S => W.val.toSubmodule) ∧
    ∃ m : S → ℕ,
      Nat.card S = Module.finrank ℂ H ∧
      (∀ W : S, 0 < m W ∧
        ∃ b : Module.Basis (Fin (2 * m W + 1)) ℂ W.val, IsStandardBasis b) ∧
      (∀ n : ℕ, heightCount H φ (n + 1) ≤ heightCount H φ n ∧
        Nat.card {W : S | m W = n} = heightCount H φ n - heightCount H φ (n + 1)) ∧
      (∑ᶠ W : S, m W) = (_root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ).ncard ∧
      IsGreatest (Set.range m) (positiveHeight H φ θ) ∧
      coxeterNumber H φ θ = 1 + sSup (Set.range m)

end LieAlgebrasAndRepresentations.PrincipalTriple

namespace Specs.LieAlgebrasAndRepresentations.PrincipalTriple

open RootDecomposition MaximalTori Sl2Model
open _root_.LieAlgebrasAndRepresentations.HighestRoot
open _root_.LieAlgebrasAndRepresentations.PrincipalTriple

/-- The principal triple and exponent conclusions for a specified positive system. -/
def PrincipalTripleFor {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Module.Dual ℝ (Module.Dual ℂ H)) : Prop :=
  Nonempty (SimpleTripleData H φ) ∧
  ∀ d : SimpleTripleData H φ,
    IsSl2Triple (twiceCorootRho H φ : L) (principalE H φ d) (principalF H φ d) ∧
    ∃ j : Model ℂ →ₗ⁅ℂ⁆ L, Function.Injective j ∧
      j (E ℂ) = principalE H φ d ∧
      j (Sl2Model.H ℂ) = (twiceCorootRho H φ : L) ∧
      j (F ℂ) = principalF H φ d ∧
      ∃ θ ∈ _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ,
        (∀ β ∈ rootSet_value H, θ - β ∈ positiveRootMonoid H φ) ∧
        HasExponentDecomposition H φ j θ

def principal_triple_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [Nontrivial L] [LieAlgebra.IsSimple ℂ L],
    ∀ (H : LieSubalgebra ℂ L), IsMaximalToral_value H →
    ∀ (φ : Module.Dual ℝ (Module.Dual ℂ H)),
      (∀ α ∈ rootSet_value H, φ α ≠ 0) →
      PrincipalTripleFor H φ

/-- The same conclusions for the positive system chosen by a regular vector in
a real Euclidean model of the adjoint roots. -/
def principal_triple_regular_vector_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [Nontrivial L] [LieAlgebra.IsSimple ℂ L],
    ∀ (H : LieSubalgebra ℂ L), IsMaximalToral_value H →
    ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      (ι : V →ₗ[ℝ] Module.Dual ℂ H), Function.Injective ι →
      rootSet_value H ⊆ Set.range ι →
      let R := ι ⁻¹' rootSet_value H
      ∀ w : V, _root_.LieAlgebrasAndRepresentations.RootRegular R w →
        ∃ φ : Module.Dual ℝ (Module.Dual ℂ H),
          (∀ a : V, φ (ι a) = inner ℝ w a) ∧
          ι '' _root_.LieAlgebrasAndRepresentations.positiveRoots R w =
            _root_.LieAlgebrasAndRepresentations.HighestRoot.positiveRoots H φ ∧
          ι '' _root_.LieAlgebrasAndRepresentations.simpleRoots R w =
            _root_.LieAlgebrasAndRepresentations.HighestRoot.simpleRoots H φ ∧
          PrincipalTripleFor H φ

end Specs.LieAlgebrasAndRepresentations.PrincipalTriple
