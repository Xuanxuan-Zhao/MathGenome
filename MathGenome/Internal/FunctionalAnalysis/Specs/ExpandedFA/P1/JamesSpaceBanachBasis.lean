import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceDefinition
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import Mathlib.Analysis.Normed.Module.Basic

/-!
Independent specification of the Banach and normalized monotone basis stages of
`fa2:p1:james-space`, paper.tex:4512–4540. Coordinates start at zero here.

The underlying type is precisely the upstream null finite-variation subtype.
The fields below fix the norm and all vector operations on that subtype. Thus
the existence statements cannot be satisfied by renorming or by transporting an
unrelated Banach space onto the subtype. Completeness and convergence refer to
the topology induced by this same norm.
-/
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal

namespace ExpandedFA.P1.JamesBanachBasisSpec

abbrev Sequence : Type := JamesSpec.spaceValue

/-- A normed-space structure with the prescribed sequence operations and norm. -/
structure NormedModel where
  group : NormedAddCommGroup Sequence
  scalars : @NormedSpace ℝ Sequence _ group.toSeminormedAddCommGroup
  norm_eq : letI : NormedAddCommGroup Sequence := group; ∀ a : Sequence, ‖a‖ = JamesSpec.normValue a
  zero_eq : letI : NormedAddCommGroup Sequence := group; (0 : Sequence).val = fun _ => 0
  add_eq : letI : NormedAddCommGroup Sequence := group; ∀ a b : Sequence, (a + b).val = fun n => a.val n + b.val n
  neg_eq : letI : NormedAddCommGroup Sequence := group; ∀ a : Sequence, (-a).val = fun n => -a.val n
  smul_eq : letI : NormedAddCommGroup Sequence := group; letI : NormedSpace ℝ Sequence := scalars;
    ∀ (c : ℝ) (a : Sequence), (c • a).val = fun n => c * a.val n

/-- In particular, completeness is for the displayed cyclic James norm. -/
structure BanachModel extends NormedModel where
  complete : letI : NormedAddCommGroup Sequence := toNormedModel.group; CompleteSpace Sequence

/-- The coordinate unit vectors, with unique ordered norm-convergent expansions.
The stated partial-sum bound says that their basis is monotone with constant one;
normalization also makes this constant optimal. -/
structure BanachBasisModel extends BanachModel where
  e : ℕ → Sequence
  unit_eq : ∀ n, (e n).val = Pi.single n (1 : ℝ)
  normalized : letI : NormedAddCommGroup Sequence := toBanachModel.toNormedModel.group; ∀ n, ‖e n‖ = 1
  schauder : letI : NormedAddCommGroup Sequence := toBanachModel.toNormedModel.group;
    letI : NormedSpace ℝ Sequence := toBanachModel.toNormedModel.scalars;
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := ℝ) e
  coordinates : letI : NormedAddCommGroup Sequence := toBanachModel.toNormedModel.group;
    letI : NormedSpace ℝ Sequence := toBanachModel.toNormedModel.scalars;
    ∀ x : Sequence, C15Basis.Spec.rawCoordinates schauder x = x.val
  monotone : letI : NormedAddCommGroup Sequence := toBanachModel.toNormedModel.group;
    letI : NormedSpace ℝ Sequence := toBanachModel.toNormedModel.scalars;
    ∀ (N : ℕ) (x : Sequence), ‖C15Basis.Spec.orderedPartialSum e x.val N‖ ≤ ‖x‖

def BanachSpaceConclusion : Prop := Nonempty BanachModel

def BanachBasisConclusion : Prop := Nonempty BanachBasisModel

/-- Source-level finite-truncation inequality, including N = 0. -/
def TruncationBound : Prop :=
  ∀ (a : ℕ → ℝ), JamesSpec.membershipValue a → ∀ N : ℕ,
    JamesSpec.extendedNormValue (fun n => if n < N then a n else 0) ≤
      JamesSpec.extendedNormValue a

/-- The normalized coordinate units have exactly the source norm one. -/
def UnitNorm : Prop :=
  ∀ n : ℕ, JamesSpec.extendedNormValue (Pi.single n (1 : ℝ)) = 1

/-- Tails tend to zero in the actual cyclic variation, with its fixed factor.
This is stronger than coordinatewise convergence and is the density step. -/
def TailConvergence : Prop :=
  ∀ (a : ℕ → ℝ), JamesSpec.membershipValue a →
    Tendsto (fun N : ℕ => JamesSpec.extendedNormValue
      (fun n => if n < N then 0 else a n)) atTop (𝓝 0)

/-- A reduction target, distinct from the unconditional original conclusion. -/
def BasisFromTailConvergence : Prop := TailConvergence → BanachBasisConclusion

end ExpandedFA.P1.JamesBanachBasisSpec
