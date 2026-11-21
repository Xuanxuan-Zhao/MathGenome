import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RegularMultiplicity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Independent statements for the coefficient and completeness assertions of
paper.tex 1526–1538 and 1550–1559. Forms are linear in the first variable.
The spaces below are the original spaces with arbitrary chosen orthonormal
bases, rather than spaces carrying a preassigned analytic structure.
-/
noncomputable section
universe u v w
namespace P103.Ch08.MatrixCoefficientSpecs
open Module

/-- An irreducible unitary representation with a chosen orthonormal basis.
The basis cardinality is its dimension, and nonzeroness is included in
`irreducible`, through the shared Chapter 8 convention. -/
structure Model (G : Type u) [Group G] where
  space : Type v
  [addCommGroup : AddCommGroup space]
  [module : Module ℂ space]
  ρ : Representation ℂ G space
  irreducible : Irreducible ℂ G space ρ
  d : ℕ
  basis : Basis (Fin d) ℂ space
  form : PositiveHermitianForm space
  invariant : ∀ g x y, form.toFun (ρ g x) (ρ g y) = form.toFun x y
  orthonormal : ∀ a b, form.toFun (basis a) (basis b) = if a = b then 1 else 0

attribute [instance] Model.addCommGroup Model.module

/-- The actual (row a, column b) coordinate of the group operator. -/
def coefficient {G : Type u} [Group G] (M : Model.{u,v} G)
    (a b : Fin M.d) (g : G) : ℂ := M.basis.repr (M.ρ g (M.basis b)) a

/-- Orthogonality in a single irreducible block, with both matrix deltas. -/
def selfOrthogonalityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (M : Model.{u,v} G)
    (a b c d : Fin M.d),
    UnitaritySpecs.functionPairingValue (coefficient M a b) (coefficient M c d) =
      if a = c ∧ b = d then (M.d : ℂ)⁻¹ else 0

/-- Different irreducible types give zero, even on different original spaces. -/
def inequivalentOrthogonalityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (M : Model.{u,v} G) (N : Model.{u,w} G),
    ¬ Nonempty (N.ρ.Equiv M.ρ) →
    ∀ (a b : Fin M.d) (c d : Fin N.d),
      UnitaritySpecs.functionPairingValue (coefficient M a b) (coefficient N c d) = 0

/-- Any chosen finite enumeration, with no prescribed relation to a regular
module decomposition. -/
structure UnitaryFamily (G : Type u) [Group G] where
  n : ℕ
  model : Fin n → Model.{u,v} G

def Distinct {G : Type u} [Group G] (F : UnitaryFamily.{u,v} G) : Prop :=
  ∀ i j, Nonempty ((F.model i).ρ.Equiv (F.model j).ρ) → i = j

def Exhaustive {G : Type u} [Group G] (F : UnitaryFamily.{u,v} G) : Prop :=
  ∀ {V : Type w} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Irreducible ℂ G V ρ → ∃ i, Nonempty ((F.model i).ρ.Equiv ρ)

abbrev FamilyIndex {G : Type u} [Group G] (F : UnitaryFamily.{u,v} G) :=
  Σ i : Fin F.n, Fin (F.model i).d × Fin (F.model i).d

def familyNormalized {G : Type u} [Group G] (F : UnitaryFamily.{u,v} G)
    (p : FamilyIndex F) : G → ℂ :=
  (Real.sqrt ((F.model p.1).d : ℝ) : ℂ) • coefficient (F.model p.1) p.2.1 p.2.2

def familyOrthogonalityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (F : UnitaryFamily.{u,v} G), Distinct F →
    ∀ p q : FamilyIndex F,
    UnitaritySpecs.functionPairingValue
      (coefficient (F.model p.1) p.2.1 p.2.2)
      (coefficient (F.model q.1) q.2.1 q.2.2) =
      if p = q then ((F.model p.1).d : ℂ)⁻¹ else 0

/-- Completeness for any list containing exactly one representative of every
irreducible type. Testing exhaustiveness on spaces in the group algebra's
universe suffices, since every irreducible embeds in that algebra. -/
def familyBasisType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (F : UnitaryFamily.{u,v} G),
    Distinct F → Exhaustive.{u,v,u} F →
    ∃ B : Basis (FamilyIndex F) ℂ (G → ℂ),
      (∀ p, B p = familyNormalized F p) ∧
      ∀ p q, UnitaritySpecs.functionPairingValue (B p) (B q) = if p = q then 1 else 0

end P103.Ch08.MatrixCoefficientSpecs
