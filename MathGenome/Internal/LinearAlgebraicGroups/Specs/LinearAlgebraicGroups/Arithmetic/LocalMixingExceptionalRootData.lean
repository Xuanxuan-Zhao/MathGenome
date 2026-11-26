import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import Mathlib.NumberTheory.LocalField.Basic

open AlgebraicGeometry CategoryTheory
open scoped BigOperators CategoryTheory.MonObj InnerProductSpace Matrix

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingExceptionalRootData

open CharacterDescent (Character)
open CharacterPairing (absoluteRoots pairing)
open ExceptionalAffineRootSystems (IsRootCoordinate exceptionalCartan restrictedRoot)
open GeometricRadicals (IsSplitReductive IsSplitTorus IsTorus baseChangedSubgroup)
open Pinning (AttachedDatum SplitBorelPair)
open QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open RankOneFlag (IsGeometricallyMaximal)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (relativeRoots)
open Relative.RelativeReflections (Datum)
open Relative.RelativeWeylScheme (QuotientData)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple RealRootSpan realRoot)
open RootGroups (Proportional)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

noncomputable section

/-- The three projections in the marked exceptional cases. The indices give
the absolute and projected ranks. -/
inductive Projection : ℕ → ℕ → Type
  | innerE6 : Projection 6 2
  | innerE7 : Projection 7 4
  | outerE6 : Projection 6 4

/-- Restriction on integral simple-root coefficients, in the numbering of
`exceptionalCartan`. -/
def Projection.project : Projection n m → (Fin n → ℤ) → (Fin m → ℤ)
  | .innerE6, v => ![v 1, v 3]
  | .innerE7, v => ![v 0, v 2, v 3, v 5]
  | .outerE6, v => restrictedRoot v

/-- The same projection on real simple-root coefficients. -/
def Projection.projectReal : Projection n m → (Fin n → ℝ) → (Fin m → ℝ)
  | .innerE6, v => ![v 1, v 3]
  | .innerE7, v => ![v 0, v 2, v 3, v 5]
  | .outerE6, v => ![v 1, v 3, v 2 + v 4, v 0 + v 5]

/-- The zero-based index of the distinguished simple root. -/
def Projection.selectedIndex : Projection n m → Fin n
  | .innerE6 => 1
  | .innerE7 => 2
  | .outerE6 => 1

/-- The absolute simply laced form in simple-root coordinates. -/
def cartanForm (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * (exceptionalCartan n i j : ℝ) * y j

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

local notation "Fsep" => SeparableClosure F
local notation "Esep" => groupBaseChange F Fsep

/-- A maximal torus above the marked split torus, with its actual pinned-pair
comparison and its absolute and relative root coordinates. -/
structure MarkedTorus (S₀ : ClosedSubgroup G.val) (p : Projection n m) where
  maximalSplit : IsMaximalSplitTorus S₀
  torus : ClosedSubgroup G.val
  isTorus : IsTorus torus.group
  isMaximal : IsGeometricallyMaximal torus
  inclusion : S₀.group ⟶ torus.group
  inclusion_comp : inclusion ≫ torus.inclusion = S₀.inclusion
  pair : SplitBorelPair Fsep
  datum : AttachedDatum pair
  groupIso : pair.G.val ≅ (Esep).obj G.val
  torusIso : pair.T.group ≅ (Esep).obj torus.group
  inclusions_commute :
    pair.T.inclusion ≫ groupIso.hom = torusIso.hom ≫ (Esep).map torus.inclusion
  multiplicative : MultiplicativeComparison F Fsep
  preservesUnits : PreservesUnits multiplicative
  numbering :
    letI := datum.comm
    Fin n ≃ datum.base.support
  cartan_eq :
    letI := datum.comm
    ∀ i j, exceptionalCartan n i j = datum.datum.rootDatum.pairing (numbering i) (numbering j)
  coordinates : AbstractPairing.Root pair.T ≃
    {v : Fin n → ℤ // IsRootCoordinate (exceptionalCartan n) v}
  coordinates_eq :
    letI := datum.comm
    ∀ b, datum.datum.rootDatum.root b =
      ∑ j, (coordinates b).val j • datum.datum.rootDatum.root (numbering j)
  encode : Multiplicative (Fin m → ℤ) →* Character S₀.group
  encode_injective : Function.Injective encode
  restriction_eq : ∀ b : AbstractPairing.Root pair.T,
    (Esep).map inclusion ≫ torusIso.inv ≫ b.val =
      (Esep).map (encode (Multiplicative.ofAdd (p.project (coordinates b).val))) ≫ multiplicative.inv
  relativeRoots_eq : relativeRoots S₀ =
    {a | ∃ v : {v : Fin n → ℤ // IsRootCoordinate (exceptionalCartan n) v},
      p.project v.val ≠ 0 ∧ encode (Multiplicative.ofAdd (p.project v.val)) = a}
  selected : relativeRoots S₀
  selected_eq : selected.val = encode (Multiplicative.ofAdd (p.project
    (Pi.single p.selectedIndex (1 : ℤ))))
  orthogonal : ∀ x : Fin n → ℝ, p.projectReal x = 0 →
    cartanForm n (Pi.single p.selectedIndex (1 : ℝ)) x = 0
  singleton : ∃! b : AbstractPairing.Root pair.T,
    (Esep).map inclusion ≫ torusIso.inv ≫ b.val = (Esep).map selected.val ≫ multiplicative.inv

/-- The absolute-root restriction fibre of `a` is a singleton over a
finite Galois field splitting the ambient group and the chosen maximal torus. -/
def HasSingleAbsoluteRoot (S : ClosedSubgroup G.val) (a : Character S.group) : Prop :=
  ∃ (T : ClosedSubgroup G.val) (i : S.group ⟶ T.group),
    IsTorus T.group ∧ IsGeometricallyMaximal T ∧ i ≫ T.inclusion = S.inclusion ∧
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (_ : IsGalois F K)
      (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
      (e : MultiplicativeComparison F K),
      IsSplitReductive (baseChangedAlgebraicGroup K G) ∧
      IsSplitTorus ((groupBaseChange F K).obj T.group) ∧
      PreservesUnits e ∧
      ∃! b : Character ((groupBaseChange F K).obj T.group),
        b ∈ absoluteRoots (baseChangedSubgroup K T hT) ∧
          (groupBaseChange F K).map i ≫ b = (groupBaseChange F K).map a ≫ e.inv

/-- Maximal length in a real inner product realizing the relative Cartan
integers of the actual torus. -/
def IsLongest (S : ClosedSubgroup G.val) (a : relativeRoots S) : Prop :=
  ∃ (D : QuotientData S) (comm : IsCommMonObj S.group.X),
    letI := comm
    ∃ (d : Datum D) (form : InnerProductSpace.Core ℝ (RealRootSpan S)),
      letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
      letI := InnerProductSpace.ofCore form.toCore
      (∀ b r : relativeRoots S,
        2 * inner ℝ (realRoot b) (realRoot r) / inner ℝ (realRoot r) (realRoot r) =
          (pairing S.group b.val (d.reflection r).coroot : ℝ)) ∧
      ∀ b : relativeRoots S, ‖realRoot b‖ ≤ ‖realRoot a‖

/-- The relative roots on each rational maximal split torus are reduced and
one of maximum length has a single absolute root above it. -/
def ExceptionalRootData : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ (S : ClosedSubgroup G.val), IsMaximalSplitTorus S →
    ∀ (S₀ : ClosedSubgroup G.val) {n m : ℕ} (p : Projection n m), MarkedTorus S₀ p →
      (∀ a b : relativeRoots S, Proportional a.val b.val →
        b.val = a.val ∨ b.val = a.val⁻¹) ∧
      ∃ a : relativeRoots S, IsLongest S a ∧ HasSingleAbsoluteRoot S a.val

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingExceptionalRootData
