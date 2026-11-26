import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalLocalRadicalGeneration

open AdjointCocharacters (coordinateHopf)
open Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open BorelProper (IsParabolic)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open ExceptionalAffineRootSystems (exceptionalCartan IsRootCoordinate restrictedRoot)
open ExceptionalFormsOverUnramifiedFields (HasTypeE)
open ExceptionalInnerIndices (e6Black e7Black)
open ExceptionalIwahoriCongruence (affinePointTopology)
open ExceptionalMarkedRootDescent (coordinatePointEquiv)
open GeneralLinearStructure (SpecialMatrixPoints)
open GeometricBorelConjugacy (ConjugatesSubgroups)
open GeometricRadicals (IsSplitReductive IsMaximalTorus)
open OuterTypeAModels (RepresentsNormOne)
open Pinning (AttachedDatum PinnedGroup SplitBorelPair)
open QuasiSplitInnerForms (AreInnerForms)
open QuasiSplitOrbitAmbientWords (groundPointIso)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Relative.RelativeChambers (relativeRoots)
open RelativeRank (relativeRank)
open RootGroups (AdditiveLine IsRootSubgroup Proportional)
open SchemeDerivedGroup (IsDerivedSubgroup IsSubgroupOf RepresentsQuotient)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup Index)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition cocharacterPoint unitPoint)
open _root_.Specs.RM03.CSA (degree isCentralSimple)

noncomputable section

variable {F : Type u} [Field F]

local notation "Fsep" => SeparableClosure F

private abbrev Gm (K : Type u) [Field K] := specGroup (groupAlgebra K IntegerCharacters)

/-- Absolute type, measured on the actual simple roots over the separable closure.
The numbering of `exceptionalCartan` is Bourbaki's, starting at zero. -/
def HasAbsoluteTypeE (G : AffineAlgebraicGroup F) (n : ℕ) : Prop :=
  ∃ (P : SplitBorelPair Fsep) (D : AttachedDatum P)
    (b : Fin n ≃ D.toBased.base.support),
    Nonempty (P.G.val ≅ (groupBaseChange F Fsep).obj G.val) ∧
    ∀ i j, D.toBased.datum.pairing (b i) (b j) = exceptionalCartan n i j

/-- An inner form of a split pinned group of the indicated absolute E type. -/
def IsInnerTypeE (G : AffineAlgebraicGroup F) (n : ℕ) : Prop :=
  ∃ (A : AdditiveLine F) (P : PinnedGroup A) (D : AttachedDatum P.pair),
    HasTypeE D n ∧ AreInnerForms (S := Fsep) P.pair.G G

/-- Evaluation on the coordinate algebra gives the usual local topology on
the ground-field sections of the actual affine group scheme. -/
abbrev localPointTopology [TopologicalSpace F] (G : AffineAlgebraicGroup F) :
    TopologicalSpace (𝟙_ (SchemeOver F) ⟶ G.val.X) :=
  letI := affinePointTopology F (coordinateHopf G) F
  TopologicalSpace.induced
    (fun g => ((coordinatePointEquiv G _).symm ((groundPointIso F).inv ≫ g)).ofConv)
    inferInstance

/-- Over a nonarchimedean local field, every simply connected absolutely almost
simple E₆, E₇ or E₈ has positive split rank and dense `G(F)⁺`. -/
def LocalRadicalGeneration : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    (HasAbsoluteTypeE G 6 ∨ HasAbsoluteTypeE G 7 ∨ HasAbsoluteTypeE G 8) →
    letI := localPointTopology G
    0 < relativeRank G ∧ Dense (unipotentGenerated G : Set (𝟙_ (SchemeOver F) ⟶ G.val.X))

/-- A geometric Borel pair adapted to a minimal rational parabolic and to
maximal tori over the ground field. The comparisons are of subgroup schemes. -/
structure AdaptedBorel (G : AffineAlgebraicGroup F) (n : ℕ) where
  S : ClosedSubgroup G.val
  maximalSplit : IsMaximalSplitTorus S
  T : ClosedSubgroup G.val
  maximalTorus : IsMaximalTorus T
  intoTorus : S.group ⟶ T.group
  intoTorus_eq : intoTorus ≫ T.inclusion = S.inclusion
  J : ClosedSubgroup G.val
  minimalParabolic : IsMinimalParabolic G J
  torusInParabolic : IsSubgroupOf T J
  P : SplitBorelPair Fsep
  D : AttachedDatum P
  numbering : Fin n ≃ D.toBased.base.support
  cartan_eq : ∀ i j, D.toBased.datum.pairing (numbering i) (numbering j) = exceptionalCartan n i j
  ambient : P.G.val ≅ (groupBaseChange F Fsep).obj G.val
  torus : (groupBaseChange F Fsep).obj T.group ≅ P.T.group
  torus_eq : torus.hom ≫ P.T.inclusion ≫ ambient.hom =
    (groupBaseChange F Fsep).map T.inclusion
  borel : P.B.group ⟶ (groupBaseChange F Fsep).obj J.group
  borel_eq : borel ≫ (groupBaseChange F Fsep).map J.inclusion =
    P.B.inclusion ≫ ambient.hom
  multiplicative : Gm Fsep ≅ (groupBaseChange F Fsep).obj (Gm F)
  multiplicative_eq : ∀ (R : TestAlgebra Fsep) (t : Rˣ),
    baseChangePoint F Fsep (Gm F).X R (unitPoint R t ≫ multiplicative.hom.hom.hom) =
      unitPoint ((restrictTestAlgebra F Fsep).obj R) t

variable {G : AffineAlgebraicGroup F} {n : ℕ}

abbrev AdaptedBorel.splitInAbsolute (A : AdaptedBorel G n) :
    (groupBaseChange F Fsep).obj A.S.group ⟶ A.P.T.group :=
  (groupBaseChange F Fsep).map A.intoTorus ≫ A.torus.hom

abbrev AdaptedBorel.restrictAbsolute (A : AdaptedBorel G n)
    (α : Character A.P.T.group) : Character ((groupBaseChange F Fsep).obj A.S.group) :=
  A.splitInAbsolute ≫ α

abbrev AdaptedBorel.extendRelative (A : AdaptedBorel G n) (β : Character A.S.group) :
    Character ((groupBaseChange F Fsep).obj A.S.group) :=
  (groupBaseChange F Fsep).map β ≫ A.multiplicative.inv

/-- A split rank-one subgroup with the indicated absolute root groups as its
upper and lower unipotent subgroups. The diagonal is the descended coroot. -/
structure SplitRootSL2 (A : AdaptedBorel G n) (α : AbstractPairing.Root A.P.T) where
  subgroup : ClosedSubgroup G.val
  matrix : SpecialMatrixPoints (closedSubgroupAlgebraicGroup subgroup) 2
  positive : ClosedSubgroup subgroup.group
  negative : ClosedSubgroup subgroup.group
  positive_eq : ∀ (R : TestAlgebra F) (g : AdjointRepresentation.GroupPoints subgroup.group R),
    g ∈ SubgroupSections positive ((testSpec F).obj (op R)) ↔
      let m := (matrix.hom.app R g).val
      m (⟨0⟩ : Index.{u} 2) ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨1⟩ ⟨0⟩ = 0
  negative_eq : ∀ (R : TestAlgebra F) (g : AdjointRepresentation.GroupPoints subgroup.group R),
    g ∈ SubgroupSections negative ((testSpec F).obj (op R)) ↔
      let m := (matrix.hom.app R g).val
      m (⟨0⟩ : Index.{u} 2) ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨0⟩ ⟨1⟩ = 0
  positiveAbsolute : ClosedSubgroup A.P.G.val
  negativeAbsolute : ClosedSubgroup A.P.G.val
  positiveIso : (groupBaseChange F Fsep).obj positive.group ≅ positiveAbsolute.group
  negativeIso : (groupBaseChange F Fsep).obj negative.group ≅ negativeAbsolute.group
  positiveInclusion : positiveIso.hom ≫ positiveAbsolute.inclusion ≫ A.ambient.hom =
    (groupBaseChange F Fsep).map (positive.inclusion ≫ subgroup.inclusion)
  negativeInclusion : negativeIso.hom ≫ negativeAbsolute.inclusion ≫ A.ambient.hom =
    (groupBaseChange F Fsep).map (negative.inclusion ≫ subgroup.inclusion)
  positiveRoot : IsRootSubgroup A.P.T positiveAbsolute α.val
  negativeRoot : IsRootSubgroup A.P.T negativeAbsolute α.val⁻¹
  diagonal : Cocharacter subgroup.group
  diagonal_eq : ∀ (R : TestAlgebra F) (t : Rˣ),
    (matrix.hom.app R (cocharacterPoint diagonal R t)).val =
      Matrix.diagonal (fun i : Index.{u} 2 => if i.down = 0 then (t : R) else (t⁻¹ : Rˣ))
  coroot : Cocharacter A.S.group
  diagonalInAmbient : diagonal ≫ subgroup.inclusion = coroot ≫ A.S.inclusion
  coroot_eq : A.multiplicative.hom ≫ (groupBaseChange F Fsep).map coroot ≫ A.splitInAbsolute =
    Additive.toMul (A.D.toBased.datum.coroot α)

/-- The maps on simple-root coefficients for the two inner indices. The
outer E₆ case uses `restrictedRoot`, which adds coefficients on each orbit. -/
def e6InnerProjection (v : Fin 6 → ℤ) : Fin 2 → ℤ := ![v 1, v 3]
def e7InnerProjection (v : Fin 7 → ℤ) : Fin 4 → ℤ := ![v 0, v 2, v 3, v 5]

def projectedRoots {r : ℕ} (project : (Fin n → ℤ) → (Fin r → ℤ)) : Set (Fin r → ℤ) :=
  (project '' {v | IsRootCoordinate (exceptionalCartan n) v}) \ {0}

/-- Orthogonality to the kernel of restriction, for the absolute root form
with square length two. It means the lift retains full length under
orthogonal projection and hence its restriction is a longest root. -/
def KeepsFullLength {r : ℕ} (project : (Fin n → ℤ) → (Fin r → ℤ))
    (v : Fin n → ℤ) : Prop :=
  ∀ c, project c = 0 → dotProduct v ((exceptionalCartan n).mulVec c) = 0

/-- The actual relative roots in the marked simple-root coordinates.
Both the chosen simple root and the highest root have singleton absolute
fibres and split SL₂ subgroups, conjugate by a rational normalizer point. -/
def HasProjectedRootSystem {r : ℕ} (A : AdaptedBorel G n)
    (project : (Fin n → ℤ) → (Fin r → ℤ))
    (cardinality : ℕ) (node : Fin n)
    (selected : SplitRootSL2 A (A.numbering node).val) : Prop :=
  ∃ (coeff : AbstractPairing.Root A.P.T ≃ {v // IsRootCoordinate (exceptionalCartan n) v})
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group),
    Function.Injective encode ∧
    (∀ α, A.D.toBased.datum.root α =
      ∑ j, (coeff α).val j • A.D.toBased.datum.root (A.numbering j)) ∧
    (∀ i, (coeff (A.numbering i).val).val = Pi.single i 1) ∧
    (∀ α, A.restrictAbsolute α.val = A.extendRelative
      (encode (Multiplicative.ofAdd (project (coeff α).val)))) ∧
    relativeRoots A.S = (fun v => encode (Multiplicative.ofAdd v)) '' projectedRoots project ∧
    Nat.card (relativeRoots A.S) = cardinality ∧
    (∀ a b : relativeRoots A.S, Proportional a.val b.val →
      b.val = a.val ∨ b.val = a.val⁻¹) ∧
    ∃ (simple highest : relativeRoots A.S) (α : AbstractPairing.Root A.P.T),
      simple.val = encode (Multiplicative.ofAdd (project (Pi.single node 1))) ∧
      highest.val = encode (Multiplicative.ofAdd (project (coeff α).val)) ∧
      (∀ v ∈ projectedRoots project, ∀ j, v j ≤ project (coeff α).val j) ∧
      KeepsFullLength project (Pi.single node 1) ∧ KeepsFullLength project (coeff α).val ∧
      (∀ a : AbstractPairing.Root A.P.T,
        (A.restrictAbsolute a.val = A.extendRelative simple.val ↔ a = (A.numbering node).val) ∧
        (A.restrictAbsolute a.val = A.extendRelative highest.val ↔ a = α)) ∧
      ∃ (highestSL2 : SplitRootSL2 A α) (w : 𝟙_ (SchemeOver F) ⟶ G.val.X)
        (τ : A.S.group ≅ A.S.group),
        (τ.hom ≫ A.S.inclusion).hom.hom =
          (toUnit _ ≫ w) * A.S.inclusion.hom.hom * (toUnit _ ≫ w)⁻¹ ∧
        τ.hom ≫ highest.val = simple.val ∧
        ConjugatesSubgroups w selected.subgroup highestSL2.subgroup

/-- The norm-one form of an `m` by `m` matrix algebra over a central division
algebra of degree `d`, as a group scheme on all test algebras. -/
def IsDivisionMatrixGroup (H : AffineAlgebraicGroup F) (m d : ℕ) : Prop :=
  ∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B),
    isCentralSimple F B ∧ degree F B = d ∧
    ∃ (h : isCentralSimple F (Matrix (Fin m) (Fin m) B))
      (b : Module.Basis (ULift.{u} (Fin (Module.finrank F (Matrix (Fin m) (Fin m) B)))) F
        (Matrix (Fin m) (Fin m) B)),
      RepresentsNormOne h b H

/-- The Levi of the rational maximal parabolic omitting `node`, with the
coroot section of its one-dimensional split torus quotient. -/
def HasOmittedNodeLevi (A : AdaptedBorel G n) (node : Fin n)
    (selected : SplitRootSL2 A (A.numbering node).val)
    (model : AffineAlgebraicGroup F → Prop) : Prop :=
  ∃ (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion)),
    (∀ i, let p := pairing A.P.T.group (A.numbering i).val.val
                (A.multiplicative.hom ≫ (groupBaseChange F Fsep).map c ≫ A.splitInAbsolute)
          if i = node then 0 < p else p = 0) ∧
    IsParabolic G L.parabolic ∧ ¬ IsIso L.parabolic.inclusion ∧
    IsSubgroupOf A.J L.parabolic ∧
    (∀ Q : ClosedSubgroup G.val, IsParabolic G Q → IsSubgroupOf L.parabolic Q →
      IsIso Q.inclusion ∨ IsSubgroupOf Q L.parabolic) ∧
    ∃ (H : ClosedSubgroup L.centralizer.group) (q : L.centralizer.group ⟶ Gm F)
      (s : Cocharacter L.centralizer.group),
      let derived := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H
      IsDerivedSubgroup H ∧ GeometricallySimplyConnected derived ∧
      IsSchemeKernel q H ∧ RepresentsQuotient H q ∧
      s ≫ q = 𝟙 _ ∧ s ≫ L.centralizer.inclusion = selected.coroot ≫ A.S.inclusion ∧
      model derived

/-- The nonsplit inner forms have the indicated actual derived Levis and
reduced relative root systems. The outer E₆ form has the orbit projection
and the corresponding split rank-one subgroups. -/
def ExceptionalRootSystemsAndLevis : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    (HasAbsoluteTypeE G 6 → IsInnerTypeE G 6 → ¬ IsSplitReductive G →
      ∃ (A : AdaptedBorel G 6) (selected : SplitRootSL2 A (A.numbering 1).val),
        relativeRank G = 2 ∧
        (∀ i, A.restrictAbsolute (A.numbering i).val.val = 1 ↔ i ∈ e6Black) ∧
        HasProjectedRootSystem A e6InnerProjection 12 1 selected ∧
        HasOmittedNodeLevi A 1 selected (fun H => IsDivisionMatrixGroup H 2 3)) ∧
    (HasAbsoluteTypeE G 7 → IsInnerTypeE G 7 → ¬ IsSplitReductive G →
      ∃ (A : AdaptedBorel G 7) (selected : SplitRootSL2 A (A.numbering 2).val),
        relativeRank G = 4 ∧
        (∀ i, A.restrictAbsolute (A.numbering i).val.val = 1 ↔ i ∈ e7Black) ∧
        HasProjectedRootSystem A e7InnerProjection 48 2 selected ∧
        HasOmittedNodeLevi A 2 selected (fun H =>
          ∃ (H₁ H₂ : AffineAlgebraicGroup F) (_ : SpecialMatrixPoints H₁ 2),
            IsDivisionMatrixGroup H₂ 3 2 ∧ Nonempty (H.val ≅ Limits.prod H₁.val H₂.val))) ∧
    (HasAbsoluteTypeE G 6 → ¬ IsInnerTypeE G 6 →
      ∃ (A : AdaptedBorel G 6) (selected : SplitRootSL2 A (A.numbering 1).val),
        HasProjectedRootSystem A restrictedRoot 48 1 selected)

end
end LinearAlgebraicGroups.Specs.ExceptionalLocalRadicalGeneration
