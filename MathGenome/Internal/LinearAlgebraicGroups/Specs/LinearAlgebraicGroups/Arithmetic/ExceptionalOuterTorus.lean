import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import Mathlib.Analysis.Complex.Circle

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Topology
open scoped BigOperators CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterTorus

open AbsoluteDynkinTypes (CartanRoots E6Reflection PreservesCartan)
open AdjointRepresentation (GroupPoints)
open Arithmetic.AdelicGroups (PointsIn)
open CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open ExceptionalCompactInner (ActsOnComplexPoints HasCompactDifferential HasExceptionalType
  fixedSubgroup realConjugation)
open IntegralModels (MatrixRealization)
open Pinning (AttachedDatum PinnedGroup PinnedIso)
open RootGroups (AdditiveLine CorootReflection HasScalarAction rootPoint)
open SimplyConnectedLattice (GeometricallySimplyConnected)

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The identity component of a subgroup in the ambient point group. -/
def identityComponent (J : Subgroup H) : Set H :=
  Subtype.val '' connectedComponent (1 : J)

def fixedCompact (ω θ : MulAut H) : Subgroup H :=
  fixedSubgroup ω ⊓ fixedSubgroup θ

/-- A torus with the topology it inherits from the given point group. -/
def IsCompactTorus (T : Subgroup H) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → Circle) ≃* T), Continuous e ∧ Continuous e.symm

def IsMaximalCompactTorus (J : Set H) (T : Subgroup H) : Prop :=
  IsCompactTorus T ∧ (T : Set H) ⊆ J ∧
    ∀ V : Subgroup H, IsCompactTorus V → (V : Set H) ⊆ J → T ≤ V → V = T

/-- A conjugating element of the specified subgroup or component. -/
def Conjugates (g : H) (S U : Subgroup H) : Prop :=
  (MulAut.conj g) '' (S : Set H) = (U : Set H)

abbrev E6Space := Fin 6 → ℝ

def e6Diagram (x : E6Space) : E6Space := fun j => x (E6Reflection j)

def foldedSpace : Set E6Space := {x | e6Diagram x = x}

def e6Lattice : Set E6Space :=
  Set.range (fun z : Fin 6 → ℤ => fun j => (z j : ℝ))

def e6Inner (x y : E6Space) : ℝ :=
  ∑ i, ∑ j, x i * (CartanMatrix.E 6 i j : ℝ) * y j

def e6Roots : Set E6Space :=
  {v | ∃ p : (Fin 6 → ℤ) × (Fin 6 → ℤ),
    CartanRoots (CartanMatrix.E 6) p ∧ v = fun j => (p.2 j : ℝ)}

abbrev complexGroup (G : AffineAlgebraicGroup ℝ) := (groupBaseChange ℝ ℂ).obj G.val

abbrev complexTest := CommAlgCat.of ℂ ℂ

/-- A pinned pair on the actual complexification and a numbering of its based datum. -/
structure MarkedPair (G : AffineAlgebraicGroup ℝ) (A : AdditiveLine ℂ) where
  P : PinnedGroup A
  comparison : P.pair.G.val ≅ complexGroup G
  datum : AttachedDatum P.pair
  numbering :
    letI := datum.comm
    datum.base.support ≃ Fin 6

variable {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
variable {A : AdditiveLine ℂ}

def MarkedPair.onPoints (M : MarkedPair G A) {Q : GroupScheme ℂ}
    (f : Q ⟶ M.P.pair.G.val) (x : GroupPoints Q complexTest) : PointsIn i ℂ :=
  baseChangePoint ℝ ℂ G.val.X complexTest
    (((groupPointsFunctor ℂ).map (f ≫ M.comparison.hom)).app complexTest x)

abbrev MarkedPair.simple (M : MarkedPair G A) (j : Fin 6) : Pinning.SimpleRoot M.P.pair :=
  letI := M.datum.comm
  ⟨(M.numbering.symm j).val, (M.datum.simple_iff _).mp (M.numbering.symm j).property⟩

def MarkedPair.coroot (M : MarkedPair G A) (j : Fin 6) : Cocharacter M.P.pair.T.group :=
  letI := M.datum.comm
  Additive.toMul (M.datum.datum.rootDatum.coroot (M.simple j).val)

def MarkedPair.simpleCoordinate (M : MarkedPair G A) (j : Fin 6) : A.group ⟶ M.P.pair.G.val :=
  (M.P.pin (M.simple j)).val.hom ≫ (M.P.roots (M.simple j).val).val.inclusion

/-- Compact conjugation relates the positive and coroot-normalized negative coordinates. -/
def MarkedPair.IsCompactCompatible (M : MarkedPair G A) (ω : MulAut (PointsIn i ℂ)) : Prop :=
  ∀ j, ∃ (xneg : A.group ⟶ M.P.pair.G.val)
      (r : CorootReflection M.P.pair.T (M.simple j).val.val (M.simpleCoordinate j) xneg),
    HasScalarAction M.P.pair.T (M.simple j).val.val⁻¹ xneg ∧ r.coroot = M.coroot j ∧
    ∀ z : ℂ,
      ω (M.onPoints (i := i) (𝟙 _) (rootPoint (M.simpleCoordinate j) complexTest z)) =
        M.onPoints (𝟙 _) (rootPoint xneg complexTest (-Complex.conjAe z))

/-- The actual torus point obtained from the six simple-coroot circles. -/
def MarkedPair.torusPoint (M : MarkedPair G A) (x : E6Space) :
    GroupPoints M.P.pair.T.group complexTest :=
  (List.ofFn (fun j : Fin 6 =>
    cocharacterPoint (M.coroot j) complexTest (Circle.toUnits (Circle.exp (2 * Real.pi * x j))))).prod

def MarkedPair.exp (M : MarkedPair G A) (x : E6Space) : PointsIn i ℂ :=
  M.onPoints M.P.pair.T.inclusion (M.torusPoint x)

/-- The six values of a root character on the simple coroots. -/
def MarkedPair.rootValues (M : MarkedPair G A) (α : AbstractPairing.Root M.P.pair.T) : E6Space :=
  fun j => (CharacterPairing.pairing M.P.pair.T.group α.val (M.coroot j) : ℝ)

def MarkedPair.IsRegularChamber (M : MarkedPair G A) (z : E6Space) : Prop :=
  ∀ α : AbstractPairing.Root M.P.pair.T,
    let r := ∑ j, M.rootValues α j * z j
    r ≠ 0 ∧ (0 < r ↔ α ∈ BorelsAndChambers.subgroupRoots M.P.pair.T M.P.pair.B)

/-- Stability of the Borel and torus under an algebraic lift of the point action. -/
def MarkedPair.IsStable (M : MarkedPair G A) (θ : MulAut (PointsIn i ℂ)) : Prop :=
  ∃ (a : Aut (complexGroup G))
    (aT : Aut M.P.pair.T.group) (aB : Aut M.P.pair.B.group),
    ActsOnComplexPoints (i := i) a θ ∧
    M.P.pair.T.inclusion ≫ M.comparison.hom ≫ a.asIso.hom =
      aT.asIso.hom ≫ M.P.pair.T.inclusion ≫ M.comparison.hom ∧
    M.P.pair.B.inclusion ≫ M.comparison.hom ≫ a.asIso.hom =
      aB.asIso.hom ≫ M.P.pair.B.inclusion ≫ M.comparison.hom

/-- The outer branch of the compact comparison, on the matrix-topologized points of G. -/
structure OuterInvolutions (ω θ : MulAut (PointsIn i ℂ)) : Prop where
  continuous_compact : Continuous ω
  continuous_outer : Continuous θ
  compact_differential :
    ∃ a, ActsOnComplexPoints (i := i) a (fun x => ω (realConjugation G i x)) ∧
      HasCompactDifferential a
  algebraic_outer : ∃ a, ActsOnComplexPoints (i := i) a θ
  compact_involutive : Function.Involutive ω
  outer_involutive : Function.Involutive θ
  commute : Function.Commute θ ω
  compact_fixed : CompactSpace (fixedSubgroup ω)
  connected_fixed : ConnectedSpace (fixedSubgroup ω)
  outer : ¬ ∃ t : PointsIn i ℂ, θ = MulAut.conj t

/-- A maximal compact torus exists in the identity component of the fixed group. -/
def MaximalFixedTorusExistence : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∃ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S

/-- The maximal compact tori of the connected fixed group are conjugate there. -/
def FixedTorusConjugacy : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∀ S U : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S →
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) U →
        ∃ g ∈ identityComponent (fixedCompact ω θ), Conjugates g S U

/-- Each component of the compact fixed group meets the normalizer of its chosen torus. -/
def FixedNormalizerRepresentatives : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∀ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S →
        ∀ g ∈ fixedCompact ω θ,
          ∃ n ∈ fixedCompact ω θ, n ∈ Subgroup.normalizer (S : Set _) ∧
            g * n⁻¹ ∈ identityComponent (fixedCompact ω θ)

/-- The centralizer and the pinned torus coordinates for every choice of fixed maximal torus. -/
def OuterTorusComparison : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∀ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S →
        ∃ (T : Subgroup (PointsIn i ℂ)) (A : AdditiveLine ℂ) (M : MarkedPair G A)
          (d : PinnedIso M.P M.P) (δ : MulAut (PointsIn i ℂ)),
          (T : Set (PointsIn i ℂ)) =
            identityComponent (fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _)) ∧
          T = fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _) ∧
          IsMaximalCompactTorus (fixedSubgroup ω : Set _) T ∧
          (T : Set (PointsIn i ℂ)) = (fixedSubgroup ω : Set _) ∩
            Set.range (M.onPoints (i := i) M.P.pair.T.inclusion) ∧
          M.IsStable (i := i) θ ∧
          M.IsCompactCompatible (i := i) ω ∧
          (letI := M.datum.comm
           PreservesCartan (RootData.integralCartan M.datum.datum.rootDatum M.datum.base)
             (CartanMatrix.E 6) M.numbering) ∧
          (letI := M.datum.comm
           ∃ b : Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)),
             ∀ j, b j = Additive.ofMul (M.coroot j)) ∧
          Set.range M.rootValues =
            (fun α j => e6Inner (Pi.single j 1) α) '' e6Roots ∧
          (∀ (α : AbstractPairing.Root M.P.pair.T) x,
            CharacterPairing.characterValue α.val complexTest (M.torusPoint x) =
            (Circle.exp (2 * Real.pi * ∑ j, M.rootValues α j * x j) : ℂ)) ∧
          (∃ z ∈ foldedSpace, M.IsRegularChamber z) ∧
          Continuous (M.exp (i := i)) ∧
          (∀ y z, M.exp (i := i) (y + z) = M.exp y * M.exp z) ∧
          (T : Set (PointsIn i ℂ)) = Set.range (M.exp (i := i)) ∧
          (∀ y, M.exp (i := i) y = 1 ↔ y ∈ e6Lattice) ∧
          (∀ j, M.simpleCoordinate j ≫ d.group.hom = M.simpleCoordinate (E6Reflection j)) ∧
          (∀ j, M.coroot j ≫ d.torus.hom = M.coroot (E6Reflection j)) ∧
          ActsOnComplexPoints (i := i) (Aut.of (M.comparison.symm ≪≫ d.group ≪≫ M.comparison)) δ ∧
          Function.Involutive δ ∧ Continuous δ ∧ Function.Commute δ ω ∧
          (∀ y, δ (M.exp (i := i) y) = M.exp (e6Diagram y)) ∧
          (∃ t₀ : T, θ = MulAut.conj t₀.val * δ) ∧
          S = T ⊓ fixedSubgroup δ ∧
          (S : Set (PointsIn i ℂ)) = M.exp (i := i) '' foldedSpace

end LinearAlgebraicGroups.Specs.ExceptionalOuterTorus
