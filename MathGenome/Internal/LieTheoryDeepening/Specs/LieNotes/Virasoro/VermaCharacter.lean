import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VermaModules
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.Int

/-! The graded character and unique simple quotient in KM13. -/

noncomputable section

namespace LieNotes.Virasoro.VermaCharacterSpec

open VermaSpec PowerSeries
open scoped PowerSeries.WithPiTopology

universe u

/-- The factor with exponent (i+1) in the formal Euler product. -/
def eulerFactor (i : ℕ) : PowerSeries ℤ :=
  ∑' j : ℕ, (X ^ (i + 1) : PowerSeries ℤ) ^ j

def EulerFactorInverse : Prop :=
  ∀ i : ℕ, (1 - X ^ (i + 1)) * eulerFactor i = 1

section
variable [LieRing V] [LieAlgebra ℂ V]

/-- Formal series of the complex dimensions of the spaces of (L_0)-weight (h+d). -/
def gradedDimension (D : InducingData) (c h : ℂ) : PowerSeries ℤ :=
  PowerSeries.mk fun d : ℕ => (Module.finrank ℂ (D.degree c h d) : ℤ)

/-- Degree (d) has the ordered monomial basis indexed by the partitions of (d). -/
def HasCharacter (D : InducingData) (c h : ℂ) : Prop :=
  (∀ d : ℕ, ∃ e : {w : Word // wordDegree w = d} ≃ Nat.Partition d,
    (∀ w, (e w).parts = ↑(w.val.val.map Nat.succ)) ∧
    ∃ b : Module.Basis (Nat.Partition d) ℂ (D.degree c h d),
      ∀ p, (b p : D.Verma c h) = D.applyWord c h (e.symm p).val.val) ∧
  (∀ d : ℕ, FiniteDimensional ℂ (D.degree c h d)) ∧
  HasProd eulerFactor (gradedDimension D c h) ∧
  (∀ (d : ℕ) (s : Finset ℕ), Finset.range d ⊆ s →
    coeff d (gradedDimension D c h) = coeff d (∏ i ∈ s, eulerFactor i))

/-- The largest proper submodule gives a simple quotient and is the kernel
of every surjection onto a simple Lie module, which factors through the quotient
by a unique Lie module equivalence. -/
def HasUniqueSimpleQuotient (D : InducingData) (c h : ℂ) : Prop :=
  ∃ N : LieSubmodule ℂ V (D.Verma c h), N ≠ ⊤ ∧
    (∀ P : LieSubmodule ℂ V (D.Verma c h), P ≠ ⊤ → P ≤ N) ∧
    IsSimpleOrder (LieSubmodule ℂ V (D.Verma c h ⧸ N)) ∧
    (∀ {Q : Type u} [AddCommGroup Q] [Module ℂ Q] [LieRingModule V Q] [LieModule ℂ V Q],
      IsSimpleOrder (LieSubmodule ℂ V Q) →
      ∀ f : D.Verma c h →ₗ⁅ℂ,V⁆ Q, Function.Surjective f → f.ker = N ∧
        ∃! e : (D.Verma c h ⧸ N) ≃ₗ⁅ℂ,V⁆ Q,
          ∀ x, e (LieSubmodule.Quotient.mk' N x) = f x)

end

/-- The full statement uses one induced model with the canonical Virasoro bracket. -/
def CharacterModelExists : Prop :=
  ∃ r : LieRing V, ∃ a : @LieAlgebra ℂ V _ r,
    r.toAddCommGroup = (inferInstance : AddCommGroup V) ∧
    HEq a.toModule (inferInstance : Module ℂ V) ∧
    letI : LieRing V := r
    letI : LieAlgebra ℂ V := a
    (∀ x y : V, ⁅x, y⁆ = VirasoroSpec.bracket x y) ∧
    ∃ D : InducingData, ModelProperties.{u} D ∧
      ∀ c h, HasCharacter D c h ∧ HasUniqueSimpleQuotient.{u} D c h

end LieNotes.Virasoro.VermaCharacterSpec
