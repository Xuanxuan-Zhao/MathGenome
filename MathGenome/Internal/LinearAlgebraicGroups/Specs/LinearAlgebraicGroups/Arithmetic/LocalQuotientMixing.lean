import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeALocalModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
import Mathlib.Topology.Algebra.Group.Matrix

open AlgebraicGeometry CategoryTheory Filter MeasureTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj InnerProductSpace Topology

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalQuotientMixing

open _root_.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
  (IsUniformizingUnit RationalPoints pointTopology)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
  (L2 RightInvariant rightOperator)
open _root_.LinearAlgebraicGroups.Arithmetic
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open ExceptionalLocalRadicalGeneration (HasAbsoluteTypeE IsInnerTypeE)
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsSplitReductive IsSplitTorus IsTorus baseChangedSubgroup)
open RankOneFlag (IsGeometricallyMaximal)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (IsRegular relativeRoots)
open RelativeRayGeneration (unipotentGenerated)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple RealRootSpan realRoot)
open RootGroups (HasScalarAction Proportional)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)
open UnitaryRankOne (quadraticConjugation splitUpper)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition cocharacterPoint)
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

noncomputable section

/-- A strongly continuous unitary action of `SL₂(F)` fixes an upper-root
fixed vector under the whole group. -/
def UpperRootFixedVector : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* (V ≃ₗᵢ[ℂ] V)),
    (∀ w : V, Continuous (fun g => ρ g w)) →
    ∀ w : V, (∀ x : F, ρ (splitUpper x) w = w) → ∀ g, ρ g w = w

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

private abbrev Gm (K : Type u) [Field K] := specGroup (groupAlgebra K IntegerCharacters)

/-- Restriction from the absolute roots of a maximal torus through the split
torus. The fibre is defined using the actual base-change morphisms. -/
def HasSingleAbsoluteRoot (S : ClosedSubgroup G.val) (a : Character S.group) : Prop :=
  ∃ (T : ClosedSubgroup G.val) (i : S.group ⟶ T.group),
    IsTorus T.group ∧ IsGeometricallyMaximal T ∧ i ≫ T.inclusion = S.inclusion ∧
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (_ : IsGalois F K)
      (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
      (e : Gm K ≅ (groupBaseChange F K).obj (Gm F)),
      IsSplitReductive (baseChangedAlgebraicGroup K G) ∧
      IsSplitTorus ((groupBaseChange F K).obj T.group) ∧
      QuasiSplitOrbitLevis.PreservesUnits (F := F) (K := K) e ∧
      ∃! b : Character ((groupBaseChange F K).obj T.group),
        b ∈ absoluteRoots (baseChangedSubgroup K T hT) ∧
          (groupBaseChange F K).map i ≫ b = (groupBaseChange F K).map a ≫ e.inv

/-- Maximal root length in a Euclidean realization compatible with the
relative Cartan integers. The realization is on the span of the actual roots. -/
def IsLongest (S : ClosedSubgroup G.val) (a : relativeRoots S) : Prop :=
  ∃ (D : Relative.RelativeWeylScheme.QuotientData S)
    (comm : IsCommMonObj S.group.X),
    letI := comm
    ∃ (d : Relative.RelativeReflections.Datum D)
        (form : InnerProductSpace.Core ℝ (RealRootSpan S)),
      letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
      letI := InnerProductSpace.ofCore form.toCore
      (∀ b c : relativeRoots S,
        2 * inner ℝ (realRoot b) (realRoot c) / inner ℝ (realRoot c) (realRoot c) =
          (pairing S.group b.val (d.reflection c).coroot : ℝ)) ∧
      ∀ b : relativeRoots S, ‖realRoot b‖ ≤ ‖realRoot a‖

/-- A longest relative root with exactly one absolute root above it. -/
def HasLongestSingleRoot (S : ClosedSubgroup G.val) : Prop :=
  ∃ a : relativeRoots S, IsLongest S a ∧ HasSingleAbsoluteRoot S a.val

/-- Reducedness of the relative root system. -/
def HasReducedRoots (S : ClosedSubgroup G.val) : Prop :=
  ∀ a b : relativeRoots S, Proportional a.val b.val → b.val = a.val ∨ b.val = a.val⁻¹

/-- The highest root in the positive system selected by a regular cocharacter.
The monoid generated by the positive roots gives the usual root order. -/
def IsHighest (S : ClosedSubgroup G.val) (c : Cocharacter S.group)
    (a : relativeRoots S) : Prop :=
  let positive := {b ∈ relativeRoots S | 0 < pairing S.group b c}
  a.val ∈ positive ∧
    ∀ b ∈ positive, a.val * b⁻¹ ∈ Submonoid.closure positive

/-- The two elementary subgroups of the split rank-one group have the
prescribed opposite weights on the original torus. -/
def IsRankOneAt (S : ClosedSubgroup G.val) (a : relativeRoots S)
    (L : TrialitarianFixedRootSL2.RankOne S) : Prop :=
  HasScalarAction S a.val (L.upper.hom ≫ L.positive.inclusion) ∧
  HasScalarAction S a.val⁻¹ (L.lower.hom ≫ L.negative.inclusion) ∧
  TrialitarianRelativeRoots.RankOne.HasOppositeRadicals L

/-- The split rank-one group at the highest root and the centrality of its
upper subgroup in the radical of a maximal standard parabolic. -/
def HasHighestSplitRankOne (S : ClosedSubgroup G.val) : Prop :=
  ∃ (c : Cocharacter S.group) (a : relativeRoots S)
    (L : TrialitarianFixedRootSL2.RankOne S) (P : LimitDecomposition (c ≫ S.inclusion)),
    IsRegular S c ∧ IsHighest S c a ∧ HasSingleAbsoluteRoot S a.val ∧ IsRankOneAt S a L ∧
    TrialitarianRelativeRoots.RankOne.HasCentralUpper L P.parabolic

/-- The split subgroup at a longest root with singleton absolute fibre,
and its highest-root version in a reduced relative system. -/
def LongRootRankOne : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∀ a : relativeRoots S, IsLongest S a → HasSingleAbsoluteRoot S a.val →
        (∃ L : TrialitarianFixedRootSL2.RankOne S, IsRankOneAt S a L) ∧
        (HasReducedRoots S → HasHighestSplitRankOne S)

/-- The nonsplit inner exceptional indices and the outer `E₆` index used
in the highest-root argument. -/
def IsExceptionalCase (G : AffineAlgebraicGroup F) : Prop :=
  (HasAbsoluteTypeE G 6 ∧ IsInnerTypeE G 6 ∧ ¬ IsSplitReductive G) ∨
  (HasAbsoluteTypeE G 7 ∧ IsInnerTypeE G 7 ∧ ¬ IsSplitReductive G) ∨
  (HasAbsoluteTypeE G 6 ∧ ¬ IsInnerTypeE G 6)

/-- The quasi-split case with transitive action on the outer vertices of `D₄`. -/
def IsTrialitarianCase (G : AffineAlgebraicGroup F) : Prop :=
  TrialitarianLocalForms.IsTrialitarian G ∧ IsQuasiSplit G

/-- The reduced relative systems for the indicated exceptional and trialitarian
groups supply the requisite split subgroup at the highest root. -/
def ExceptionalAndTrialitarianRankOne : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    IsExceptionalCase G ∨ IsTrialitarianCase G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      HasReducedRoots S ∧ HasLongestSingleRoot S ∧ HasHighestSplitRankOne S

/-- The determinant-one isometry group of an isotropic nondegenerate
Hermitian form over a separable quadratic field extension. -/
def IsIsotropicSpecialUnitary (G : AffineAlgebraicGroup F) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra F E)
    (_ : Algebra.IsQuadraticExtension F E) (_ : Algebra.IsSeparable F E)
    (n : ℕ) (H : (Matrix (Fin n) (Fin n) E)ˣ),
    let σ := quadraticConjugation F E
    (H.val.map σ).transpose = H.val ∧
    (∃ x : Fin n → E, x ≠ 0 ∧ dotProduct (σ ∘ x) (Matrix.mulVec H.val x) = 0) ∧
    OuterTypeALocalModels.RepresentsHermitian σ H.val G

/-- The spin group of the original regular isotropic quadratic space, with
the even Clifford point functor over all test algebras. -/
def IsIsotropicQuadraticSpin (G : AffineAlgebraicGroup F) : Prop :=
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module F V) (_ : FiniteDimensional F V)
    (q : QuadraticForm F V)
    (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →*
      (LinearAlgebraicGroups.Albert.SpinSpecification.ScalarClifford q R)ˣ),
    5 ≤ Module.finrank F V ∧
    IsotropicSpinGeneration.IsRegular q ∧ IsotropicSpinGeneration.IsIsotropic q ∧
    LinearAlgebraicGroups.Albert.SpinSpecification.IsSpinPointRepresentation q G.val ρ

/-- The spin double cover in the quaternion division case with a hyperbolic
pair. The pair presentation includes the semitrace in characteristic two. -/
def IsIsotropicQuaternionicSpin (G : AffineAlgebraicGroup F) : Prop :=
  ∃ (K I B : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
    (_ : IsGalois F K) (_ : Fintype I) (_ : DecidableEq I)
    (_ : DivisionRing B) (_ : Algebra F B)
    (ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K))
    (D : NontrialitarianSpinModels.DescendedQuadraticPair ρ) (hB : isCentralSimple F B)
    (d : ℕ),
    4 ≤ Fintype.card I ∧ degree F B = 2 ∧ ((2 : F) ≠ 0 → 0 < d) ∧
    Nonempty (NontrialitarianSpinModels.SpinModel G D) ∧
    Nonempty (QuaternionSpinScaleCover.QuaternionHyperbolicPresentation D hB d)

variable [TopologicalSpace F]

/-- Density of the subgroup generated by the ground-field parabolic
radicals, in the coordinate topology on the original local group. -/
def HasDenseRadicals (G : AffineAlgebraicGroup F) : Prop :=
  letI := pointTopology G.val.X
  Dense {g : RationalPoints G.val.X |
    ∃ x ∈ unipotentGenerated G, toUnit ((testSpec F).obj (.op (CommAlgCat.of F F))) ≫ x = g}

/-- The local groups in the mixing assertion. -/
def MixingCases (G : AffineAlgebraicGroup F) : Prop :=
  (IsSplitReductive G ∧ GeometricallySimplyConnected G) ∨
    IsIsotropicSpecialUnitary G ∨ IsIsotropicQuadraticSpin G ∨ IsIsotropicQuaternionicSpin G ∨
    (GeometricallySimplyConnected G ∧
      (IsExceptionalCase G ∨ IsTrialitarianCase G ∨
        (HasDenseRadicals G ∧ ∃ S : ClosedSubgroup G.val,
          IsMaximalSplitTorus S ∧ HasLongestSingleRoot S)))

/-- Mixing on the quotient by left multiplication of a closed subgroup.
The order of the arguments to Lean's inner product conjugates `g`. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → MixingCases G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∀ c : Cocharacter S.group, IsRegular S c →
      ∀ π : Fˣ, IsUniformizingUnit π →
        letI := pointTopology G.val.X
        let a : RationalPoints G.val.X := cocharacterPoint (c ≫ S.inclusion) (CommAlgCat.of F F) π
        ∀ (H : Subgroup (RationalPoints G.val.X)), IsClosed (H : Set (RationalPoints G.val.X)) →
          ∀ (ν : Measure (LocalQuotientTransport.RightCosets H)) [IsFiniteMeasure ν],
            ν ≠ 0 → ∀ (hν : RightInvariant ν) (f g : L2 ν),
              Tendsto (fun m : ℕ => ⟪g, rightOperator hν (a ^ m) f⟫_ℂ) atTop
                (𝓝 (((∫ x, (f : LocalQuotientTransport.RightCosets H → ℂ) x ∂ν) *
                  (∫ x, star ((g : LocalQuotientTransport.RightCosets H → ℂ) x) ∂ν)) /
                    ((ν Set.univ).toReal : ℂ)))

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalQuotientMixing
