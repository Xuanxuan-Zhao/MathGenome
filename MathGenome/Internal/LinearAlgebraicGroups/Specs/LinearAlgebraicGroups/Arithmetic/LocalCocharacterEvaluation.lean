import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.SplitContractingRadical
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank
import Mathlib.RingTheory.AlgebraTower
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

open AlgebraicGeometry CategoryTheory Filter IsDedekindDomain Topology
open scoped NumberField

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalCocharacterEvaluation

open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open LinearAlgebraicGroups.CocharacterDynamics
open AdjointRepresentation (conjugate GroupPoints)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open IntegralModels (MatrixRealization)
open RankOneFlag (SameSubgroup)
open StandardParabolicLevi (IsContractingRadical)
open Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

noncomputable section

/-- The matrix topology of the original local point group is carried by a
closed matrix realization of the base-changed group over the local field. -/
def CompletionPointTopology : Prop :=
  ∀ {k F : Type u} [Field k] [Field F] [Algebra k F] [TopologicalSpace F]
    (G : AffineAlgebraicGroup k) (i : MatrixRealization G),
      ∃ j : MatrixRealization (baseChangedAlgebraicGroup F G),
        @IsHomeomorph (PointsIn j F) (PointsIn i F) _ _
          (baseChangePoint k F G.val.X (CommAlgCat.of F F))

/-- The given finite completion of a number field is a finite extension of
the p-adic field at the prime below the place, with continuous scalar map. -/
def PadicCompletionScalars : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)),
    ∃ v : HeightOneSpectrum (𝓞 ℚ), w.asIdeal.LiesOver v.asIdeal ∧
      let p := Rat.HeightOneSpectrum.primesEquiv v
      letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
      ∃ a : Algebra (Padic p) (w.adicCompletion K),
        letI := a
        FiniteDimensional (Padic p) (w.adicCompletion K) ∧
          Continuous (algebraMap (Padic p) (w.adicCompletion K))

/-- Every archimedean completion has its continuous real scalar structure
inherited from its real or complex model. -/
def ArchimedeanCompletionScalars : Prop :=
  ∀ {K : Type u} [Field K] (w : NumberField.InfinitePlace K),
    ∃ a : Algebra ℝ w.Completion,
      letI := a
      FiniteDimensional ℝ w.Completion ∧ Continuous (algebraMap ℝ w.Completion)

/-- The scheme adjoint action in a cocharacter weight basis. The tower basis
repeats each weight across the scalar restriction, including from complex to
real and from a finite extension of the p-adics to the p-adics. -/
def AdjointEvaluation : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (c : Cocharacter G.val) (s : IdentityLieStructure G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (W : AdjointWeightBasis c s) (ρ : PointsIn i F →* (Lie F G.val ≃ₗ[F] Lie F G.val)),
      (∀ g v, (ρ g v).toMul.val =
        conjugate (R := CommAlgCat.of F F) g v) ∧
      (∀ v j, Continuous (fun g ↦ W.basis.coord j (ρ g v))) ∧
      (∀ (t : Fˣ) j, ρ (cocharacterPoint c (CommAlgCat.of F F) t) (W.basis j) =
        ((t : F) ^ W.weight j) • W.basis j) ∧
      ∀ {E : Type v} [NontriviallyNormedField E] [CompleteSpace E] [Algebra E F] [T2Space F]
        {ι : Type v} [Fintype ι] (d : Module.Basis ι E F), Continuous (algebraMap E F) →
        letI : Module E (Lie F G.val) := Module.compHom (Lie F G.val) (algebraMap E F)
        letI : IsScalarTower E F (Lie F G.val) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let b := d.smulTower W.basis
        ∃ σ : PointsIn i F →* (Lie F G.val ≃ₗ[E] Lie F G.val),
          (∀ g v, σ g v = ρ g v) ∧
          (∀ v j, Continuous (fun g ↦ b.coord j (σ g v))) ∧
          ∀ (t : Eˣ) (j : ι × ULift.{u} (Fin W.dimension)),
            σ (cocharacterPoint c (CommAlgCat.of F F) (Units.map (algebraMap E F).toMonoidHom t)) (b j) =
              ((t : E) ^ W.weight j.2) • b j

/-- Distinct integer weights give distinct absolute values for a non-unit-norm
scalar from the field used for restriction of scalars. -/
def NormSeparatesWeights : Prop :=
  ∀ {E : Type v} [NormedField E] (t : Eˣ), ‖(t : E)‖ ≠ 1 →
    Function.Injective (fun m : ℤ ↦ ‖(t : E) ^ m‖)

/-- A scalar of strictly positive norm less than one is available in each
nontrivially normed scalar field. -/
def ContractingScalarExists : Prop :=
  ∀ {E : Type v} [NontriviallyNormedField E], ∃ t : Eˣ, ‖(t : E)‖ < 1

/-- The image in the local point group of every contracting subgroup is
contracted by positive powers of the same evaluated cocharacter. -/
def ContractingEvaluation : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (c : Cocharacter G.val) (D : LimitDecomposition c)
    {E : Type v} [NormedField E] [Algebra E F],
    Continuous (algebraMap E F) → ∀ (t : Eˣ), ‖(t : E)‖ < 1 →
    ∀ g : PointsIn i F,
      g ∈ ((((groupPointsFunctor F).map D.contracting.inclusion).app
        (CommAlgCat.of F F)).hom).range →
      let a : PointsIn i F :=
        cocharacterPoint c (CommAlgCat.of F F) (Units.map (algebraMap E F).toMonoidHom t)
      Tendsto (fun n : ℕ ↦ a ^ n * g * (a ^ n)⁻¹) atTop (𝓝 1)

/-- Every rational parabolic has a cocharacter realization whose unipotent
radical is contracted by the indicated local evaluation. -/
def ParabolicRadicalEvaluation : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (P : ClosedSubgroup G.val), BorelProper.IsParabolic G P →
    ∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      SameSubgroup P D.parabolic ∧ IsContractingRadical D ∧
      (∀ U : ClosedSubgroup P.group, IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U →
        ∃ e : U.group ≅ D.contracting.group,
          e.hom ≫ D.contracting.inclusion = U.inclusion ≫ P.inclusion) ∧
      ∀ {E : Type v} [NormedField E] [Algebra E F],
        Continuous (algebraMap E F) → ∀ (t : Eˣ), ‖(t : E)‖ < 1 →
        ∀ g : PointsIn i F,
          g ∈ ((((groupPointsFunctor F).map D.contracting.inclusion).app
            (CommAlgCat.of F F)).hom).range →
          let a : PointsIn i F :=
            cocharacterPoint c (CommAlgCat.of F F) (Units.map (algebraMap E F).toMonoidHom t)
          Tendsto (fun n : ℕ ↦ a ^ n * g * (a ^ n)⁻¹) atTop (𝓝 1)

/-- An open cocompact subgroup contains the points of every rational
parabolic unipotent radical. A continuous embedding of the given scalar
field supplies the contracting parameter. -/
def OpenCocompactContainsRadicals : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    {E : Type v} [NontriviallyNormedField E] [Algebra E F],
    Continuous (algebraMap E F) → ∀ (H : Subgroup (PointsIn i F))
      [CompactSpace (PointsIn i F ⧸ H)], IsOpen (H : Set (PointsIn i F)) →
    H.FiniteIndex ∧
      ∀ (P : ClosedSubgroup G.val), BorelProper.IsParabolic G P →
        ∀ (U : ClosedSubgroup P.group), IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U →
          ((((groupPointsFunctor F).map (U.inclusion ≫ P.inclusion)).app
            (CommAlgCat.of F F)).hom).range ≤ H

/-- A noncentral split torus has a cocharacter, with sign chosen inside that
torus, whose contracting subgroup has a nonzero tangent direction in G. -/
def NonzeroContractingLie : Prop :=
  ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F), IsReductive G →
    ∀ (S : ClosedSubgroup G.val), IsSplitTorus S.group →
      ¬ CentralFrobeniusDescent.IsCentral S.inclusion →
      ∃ (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)),
        ∃ v : Lie F G.val, v ∈ lieImage D.contracting ∧ v ≠ 0

/-- Isotropic semisimple groups, including the absolutely almost simple
case, have a nonzero contracting Lie direction from a maximal split torus. -/
def IsotropicContractingLie : Prop :=
  ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F),
    GeometricRadicals.IsSemisimple G → 0 < RelativeRank.relativeRank G →
    ∃ (S : ClosedSubgroup G.val),
      Relative.MaximalSplitTori.IsMaximalSplitTorus S ∧
      ∃ (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)),
        ∃ v : Lie F G.val, v ∈ lieImage D.contracting ∧ v ≠ 0

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalCocharacterEvaluation
