import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj InnerProductSpace

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingTrialitarianRootData

open CharacterDescent (Character)
open CharacterPairing (absoluteRoots pairing)
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsSplitReductive IsSplitTorus IsTorus baseChangedSubgroup)
open QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open RankOneFlag (IsGeometricallyMaximal)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (relativeRoots)
open Relative.RelativeReflections (Datum)
open Relative.RelativeWeylScheme (QuotientData)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple RealRootSpan realRoot)
open RootGroups (Proportional)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open TrialitarianLocalForms (IsTrialitarian)
open Unipotent (baseChangedAlgebraicGroup)

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

/-- The relative roots on each rational line are equal or opposite. -/
def HasReducedRoots (S : ClosedSubgroup G.val) : Prop :=
  ∀ a b : relativeRoots S, Proportional a.val b.val → b.val = a.val ∨ b.val = a.val⁻¹

/-- The length comparison on the real span of the actual relative roots,
with the relative Cartan integers computed by the scheme pairing. -/
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

/-- The fibre of restriction on the actual absolute roots is a singleton
in a finite Galois splitting of the group and of the indicated maximal torus. -/
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

/-- For a quasi-split trialitarian group with transitive outer-vertex action,
the supplied maximal split torus has reduced relative roots and a longest
relative root with a singleton absolute fibre. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    IsTrialitarian G → IsQuasiSplit G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      HasReducedRoots S ∧ ∃ a : relativeRoots S, IsLongest S a ∧ HasSingleAbsoluteRoot S a.val

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingTrialitarianRootData
