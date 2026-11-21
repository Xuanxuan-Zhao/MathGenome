import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWOrdered
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Independent specification for LA-I08, source lines 4324–4360.
The field is arbitrary, and the zero Lie algebra is included. All quotients
below are quotients of the actual enveloping algebra. The weighted subspace is
fixed by PBW monomials; its multiplicativity and stability are conclusions.
-/
namespace LieAlgebrasAndRepresentations.NilpotentTruncation
open _root_.Shared.Lie _root_.Shared.Lie.PBW
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]

/-- A basis and positive weights describing every positive lower-central term. -/
def IsAdapted {d : ℕ} (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ) : Prop :=
  (∀ i, 0 < w i) ∧ ∀ j : ℕ, 0 < j →
    (Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries.lowerCentralSeries_value k L j).toSubmodule = Submodule.span k (b '' {i | j ≤ w i})

def wordWeight {ι : Type w} (w : ι → ℕ) (l : List ι) : ℕ := (l.map w).sum

/-- Decreasing filtration by the total lower-central weight of ordered PBW words. -/
noncomputable def weightedSpan {d : ℕ} (b : Module.Basis (Fin d) k L)
    (w : Fin d → ℕ) (N : ℕ) : Submodule k (U k L) :=
  Submodule.span k {a | ∃ l : OrderedWord (Fin d),
    N ≤ wordWeight w l.val ∧ orderedMonomial b l = a}

/-- The carrier is fixed even before ideal closure has been proved. -/
abbrev QuotientSpace {d : ℕ} (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ) (N : ℕ) :=
  U k L ⧸ weightedSpan b w N

/-- The associative Leibniz rule on the noncommutative enveloping algebra. -/
def IsEnvelopingDerivation (D : Module.End k (U k L)) : Prop :=
  D 1 = 0 ∧ ∀ a b, D (a * b) = a * D b + D a * b

/-- A derivation is uniquely determined by its values on the Lie generators. -/
def Extends (D : Module.End k (U k L)) (δ : LieDerivation k L L) : Prop :=
  IsEnvelopingDerivation D ∧ ∀ x, D (inclusion k L x) = inclusion k L (δ x)

end LieAlgebrasAndRepresentations.NilpotentTruncation

namespace Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation
open _root_.Shared.Lie _root_.Shared.Lie.PBW
open _root_.LieAlgebrasAndRepresentations.NilpotentTruncation
universe u v
attribute [local instance 100] LieRing.ofAssociativeRing

/-- No nilpotence, finite dimension or characteristic assumption is needed to
extend a derivation to the actual enveloping quotient. -/
def derivationExtensionExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L],
    ∃ E : LieDerivation k L L →ₗ⁅k⁆ Module.End k (U k L),
      ∀ δ, Extends (E δ) δ ∧ ∀ D, Extends D δ → D = E δ

/-- Each lower-central term is characteristic under all derivations. -/
def lowerCentralStableExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    (δ : LieDerivation k L L) (j : ℕ) (x : L),
    x ∈ DerivedLowerSeries.lowerCentralSeries_value k L j →
      δ x ∈ DerivedLowerSeries.lowerCentralSeries_value k L j

/-- Existence of a finite lower-central adapted basis. -/
def adaptedBasisExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [LieRing.IsNilpotent L],
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ), IsAdapted b w

/-- Multiplicativity of the decreasing weighted filtration. -/
def weightedMultiplicativeExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    (d : ℕ) (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ), IsAdapted b w →
    ∀ i j (a z : U k L), a ∈ weightedSpan b w i → z ∈ weightedSpan b w j →
      a * z ∈ weightedSpan b w (i + j)

/-- Every extended derivation preserves the specified PBW subspace. -/
def weightedStableExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    (d : ℕ) (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ), IsAdapted b w →
    ∀ (δ : LieDerivation k L L) (D : Module.End k (U k L)), Extends D δ →
      ∀ N z, z ∈ weightedSpan b w N → D z ∈ weightedSpan b w N

/-- Finite dimension of the exact PBW quotient (including N = 0). -/
def quotientFiniteExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    (d : ℕ) (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ), (∀ i, 0 < w i) →
      ∀ N, FiniteDimensional k (QuotientSpace b w N)

/-- Separation of the generators once every basis weight is below the cutoff. -/
def pbwSeparationExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    (d : ℕ) (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ) (N : ℕ),
      (∀ i, w i < N) →
        Function.Injective ((weightedSpan b w N).mkQ.comp (inclusion k L).toLinearMap)

/-- Complete weighted PBW construction, with no exclusion of dimension zero.
The actions are required to be the actions induced by left multiplication and
by the enveloping derivations, on the specified quotient carrier. -/
def truncationExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [LieRing.IsNilpotent L],
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ),
      IsAdapted b w ∧
      ∃ E : LieDerivation k L L →ₗ⁅k⁆ Module.End k (U k L),
        (∀ δ, Extends (E δ) δ) ∧
        ∀ N : ℕ,
          (∀ (a z : U k L), z ∈ weightedSpan b w N →
            a * z ∈ weightedSpan b w N ∧ z * a ∈ weightedSpan b w N) ∧
          (∀ (δ : LieDerivation k L L) z, z ∈ weightedSpan b w N →
            E δ z ∈ weightedSpan b w N) ∧
          FiniteDimensional k (QuotientSpace b w N) ∧
          ∃ (ρ : L →ₗ⁅k⁆ Module.End k (QuotientSpace b w N))
            (D : LieDerivation k L L →ₗ⁅k⁆ Module.End k (QuotientSpace b w N)),
            (∀ x a, ρ x ((weightedSpan b w N).mkQ a) =
              (weightedSpan b w N).mkQ (inclusion k L x * a)) ∧
            (∀ δ a, D δ ((weightedSpan b w N).mkQ a) =
              (weightedSpan b w N).mkQ (E δ a)) ∧
            (∀ δ, D δ ((weightedSpan b w N).mkQ 1) = 0) ∧
            (∀ δ x, ⁅D δ, ρ x⁆ = ρ (δ x)) ∧
            (∀ (c : ℕ),
              DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥ →
              c < N → Function.Injective ρ ∧ ∀ x, (ρ x) ^ N = 0)

/-- The stated faithful nilpotent representation, with a positive cutoff
chosen from nilpotence and simultaneous compatibility with all derivations. -/
def faithfulExpected : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [LieRing.IsNilpotent L],
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k L) (w : Fin d → ℕ) (N : ℕ),
      0 < N ∧ IsAdapted b w ∧ FiniteDimensional k (QuotientSpace b w N) ∧
      ∃ (ρ : L →ₗ⁅k⁆ Module.End k (QuotientSpace b w N))
        (D : LieDerivation k L L →ₗ⁅k⁆ Module.End k (QuotientSpace b w N)),
        Function.Injective ρ ∧ (∀ x, (ρ x) ^ N = 0) ∧
        (∀ x a, ρ x ((weightedSpan b w N).mkQ a) =
          (weightedSpan b w N).mkQ (inclusion k L x * a)) ∧
        (∀ δ, D δ ((weightedSpan b w N).mkQ 1) = 0) ∧
        (∀ δ x, ⁅D δ, ρ x⁆ = ρ (δ x))

end Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation
