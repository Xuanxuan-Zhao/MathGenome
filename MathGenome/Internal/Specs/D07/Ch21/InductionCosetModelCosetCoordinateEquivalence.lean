import MathGenome.Internal.Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
The left-coset coordinates of paper.tex:6520–6543. A transversal is indexed
by the actual left-coset type, with no normality assumption. The finitely
supported functions are the direct sum of copies of V. No finite dimension
or nonzero-vector hypothesis is imposed on the coordinate construction.
The model structure packages the conclusions to be constructed, rather than
postulating an induced representation or a coordinate isomorphism.
-/
namespace Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence

universe u v
noncomputable section
open Representation
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge

variable {G : Type u} [Group G] (H : Subgroup G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

/-- A chosen representative of each left coset. -/
def IsTransversal (r : G ⧸ H → G) : Prop :=
  ∀ q, (QuotientGroup.mk (r q) : G ⧸ H) = q

/-- The direct sum indexed by the left cosets. -/
abbrev Coordinates := (G ⧸ H) →₀ V

/-- The sum map specified in the paper, independent of its invertibility. -/
def coordinateSum (r : G ⧸ H → G) : Coordinates H (V := V) →ₗ[ℂ] NotesInd H ρ :=
  Finsupp.lsum ℂ (fun q => notesMk H ρ (r q))

/-- A coordinate model, including compatibility with the quotient's left action.
`left_action` states this compatibility on all spanning quotient generators. -/
structure CoordinateModel (r : G ⧸ H → G) where
  toQuotient : Coordinates H (V := V) ≃ₗ[ℂ] NotesInd H ρ
  action : Representation ℂ G (Coordinates H (V := V))
  sum_map : toQuotient.toLinearMap = coordinateSum H ρ r
  left_action : ∀ k g v,
    toQuotient (action k (toQuotient.symm (notesMk H ρ g v))) =
      notesMk H ρ (k * g) v

/-- Sections exist, and the decomposition g = r(q)h is unique. -/
def TransversalDecomposition : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G),
    (∃ r : G ⧸ H → G, IsTransversal H r) ∧
    ∀ r : G ⧸ H → G, IsTransversal H r →
      ∀ g : G, ∃! p : (G ⧸ H) × H, g = r p.1 * (p.2 : G)

/-- The two inverse linear maps, their explicit formulas, and the block action. -/
def CoordinateConstruction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (r : G ⧸ H → G), IsTransversal H r →
    ∃ m : CoordinateModel H ρ r,
      (∀ x, m.toQuotient x = x.sum (fun q v => notesMk H ρ (r q) v)) ∧
      (∀ q (h : H) v, m.toQuotient.symm (notesMk H ρ (r q * (h : G)) v) =
        Finsupp.single q (ρ h v)) ∧
      (∀ k q q' (h : H), k * r q = r q' * (h : G) → ∀ v,
        m.action k (Finsupp.single q v) = Finsupp.single q' (ρ h v))

/-- Finite dimension is a conclusion for induction, not an extra premise. -/
def InductionDimension : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    FiniteDimensional ℂ (NotesInd H ρ) ∧
    Module.finrank ℂ (NotesInd H ρ) = H.index * Module.finrank ℂ V

/-- Changing representatives intertwines the coordinate actions, with the
explicit coefficient r(q) = s(q)h, and identifies the same quotient vector. -/
def RepresentativeChange : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (r s : G ⧸ H → G), IsTransversal H r → IsTransversal H s →
    ∀ (m : CoordinateModel H ρ r) (n : CoordinateModel H ρ s),
    ∃ e : m.action.Equiv n.action,
      (∀ x, n.toQuotient (e x) = m.toQuotient x) ∧
      (∀ q (h : H), r q = s q * (h : G) → ∀ v,
        e (Finsupp.single q v) = Finsupp.single q (ρ h v))

end
end Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
