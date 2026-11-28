import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.Basic
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AbelianExtensions
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Proposition LD01, with adjoint coefficients in the exterior CE complex. -/

noncomputable section

namespace Specs.LieNotes.Heisenberg.AdjointCohomology

open _root_.AdvancedHomologicalAlgebra.CE
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions

universe u v

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]

abbrev Cochains (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (n : ℕ) := W k L n →ₗ[k] L

/-- The adjoint differential selected by the full canonical CE formula. -/
def d (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L] :
    ∀ n, Cochains k L n →ₗ[k] Cochains k L (n + 1) :=
  Classical.choose (canonicalCEExists_spec (k := k) (g := L) (M := L))

abbrev Cycles (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (n : ℕ) := LinearMap.ker (d k L n)

/-- The image of the preceding differential, inside the space of cycles. -/
def boundaries (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (n : ℕ) : Submodule k (Cycles k L (n + 1)) :=
  (LinearMap.range (d k L n)).comap (Cycles k L (n + 1)).subtype

abbrev H2 (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L] :=
  Cycles k L 2 ⧸ boundaries k L 1

abbrev H3 (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L] :=
  Cycles k L 3 ⧸ boundaries k L 2

/-- The bracket table in the given ordered basis. -/
def HeisenbergBasis (b : Module.Basis (Fin 3) k L) : Prop :=
  ⁅b 0, b 1⁆ = b 2 ∧ ⁅b 0, b 2⁆ = 0 ∧ ⁅b 1, b 2⁆ = 0

/-- The three prescribed evaluations for the parameter vector (a,b,c,d,e). -/
def HasNormalValues (b : Module.Basis (Fin 3) k L) (p : Fin 5 → k)
    (f : Cochains k L 2) : Prop :=
  f (wedge k L 2 ![b 0, b 1]) = 0 ∧
  f (wedge k L 2 ![b 0, b 2]) = p 0 • b 0 + p 1 • b 1 + p 2 • b 2 ∧
  f (wedge k L 2 ![b 1, b 2]) = p 3 • b 0 - p 0 • b 1 + p 4 • b 2

def DifferentialTwoType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L), HeisenbergBasis b →
    ∀ f : Cochains k L 2,
      d k L 2 f (wedge k L 3 ![b 0, b 1, b 2]) =
        (b.repr (f (wedge k L 2 ![b 1, b 2])) 1 +
          b.repr (f (wedge k L 2 ![b 0, b 2])) 0) • b 2

def DifferentialTwoImageType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L), HeisenbergBasis b →
    ∀ v : L, (∃ f : Cochains k L 2, d k L 2 f (wedge k L 3 ![b 0, b 1, b 2]) = v) ↔
      v ∈ k ∙ b 2

def BoundariesTwoType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L), HeisenbergBasis b →
    ∀ v : L, ∃! f : Cochains k L 2,
      f ∈ LinearMap.range (d k L 1) ∧ f (wedge k L 2 ![b 0, b 1]) = v

def CochainsFourType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (_ : Module.Basis (Fin 3) k L), Subsingleton (Cochains k L 4)

def NormalFormType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L), HeisenbergBasis b →
    ∃ e : (Fin 5 → k) ≃ₗ[k] H2 k L,
      (∀ p : Fin 5 → k,
        ∃! f : Cycles k L 2, HasNormalValues b p f.1 ∧ Submodule.Quotient.mk f = e p) ∧
      ∀ c : H2 k L,
        ∃! f : Cycles k L 2, (∃ p, HasNormalValues b p f.1) ∧ Submodule.Quotient.mk f = c

def ModelNormalFormType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ e : (Fin 5 → k) ≃ₗ[k] H2 k (ModelValue k), ∀ p : Fin 5 → k,
      ∃ f : Cycles k (ModelValue k) 2,
        f.1 = phiExteriorValue k (p 0) (p 1) (p 2) (p 3) (p 4) ∧
          Submodule.Quotient.mk f = e p

def EvaluationThreeType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L), HeisenbergBasis b →
    ∃ e : H3 k L ≃ₗ[k] (L ⧸ (k ∙ b 2 : Submodule k L)),
      ∀ f : Cycles k L 3, e (Submodule.Quotient.mk f) =
        Submodule.Quotient.mk (f.1 (wedge k L 3 ![b 0, b 1, b 2]))

def DimensionsType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L), HeisenbergBasis b →
    Module.finrank k (H2 k L) = 5 ∧ Module.finrank k (H3 k L) = 2

end Specs.LieNotes.Heisenberg.AdjointCohomology
