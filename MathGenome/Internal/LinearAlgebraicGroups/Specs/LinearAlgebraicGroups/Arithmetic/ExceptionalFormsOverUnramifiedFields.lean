import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalFormsOverUnramifiedFields

open Arithmetic.MaximalUnramifiedBrauer (maximalUnramified)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open GeometricRadicals (IsSemisimple)
open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open QuasiSplitInnerForms (AreInnerForms PinnedRepresentative trivialOuterAction
  basedAutTopology fieldGalTopology)
attribute [local instance] basedAutTopology fieldGalTopology
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology
  (Cocycle groupH1 groupBasepoint)

/-- The actual Cartan matrix of the pinned simple roots has type E of rank n. -/
def HasTypeE {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (n : ℕ) : Prop :=
  ∃ e : Fin n ≃ SimpleRoot P.pair,
    ∀ i j, letI := D.comm
      D.datum.rootDatum.pairing (e i).val (e j).val = CartanMatrix.E n i j

/-- The split pinned datum of the reference has one of the three simply
connected exceptional types in the statement. The outer cocycle is arbitrary. -/
def IsExceptionalReference {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) : Prop :=
  IsSemisimple P.pair.G ∧ GeometricallySimplyConnected P.pair.G ∧
    (HasTypeE D 6 ∨ HasTypeE D 7 ∨ HasTypeE D 8)

/-- First Galois cohomology of the simply connected quasi-split reference is trivial. -/
def SimplyConnectedVanishing : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    let K := maximalUnramified F
    ∀ (S : Type u) [Field S] [Algebra K S] [IsSepClosure K S]
      {A : AdditiveLine K} {P : PinnedGroup A} {D : AttachedDatum P.pair}
      {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
      {E : SplitSequence P D l Q}
      {ω : Cocycle (trivialOuterAction (k := K) (S := S) D.toBased)}
      (V : PinnedRepresentative (S := S) E ω),
      IsExceptionalReference D →
      ∀ x : groupH1 K V.model.val.val.X S, x = groupBasepoint K V.model.val.val.X S

/-- First Galois cohomology of the adjoint quotient by the full scheme centre is trivial. -/
def AdjointVanishing : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    let K := maximalUnramified F
    ∀ (S : Type u) [Field S] [Algebra K S] [IsSepClosure K S]
      {A : AdditiveLine K} {P : PinnedGroup A} {D : AttachedDatum P.pair}
      {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
      {E : SplitSequence P D l Q}
      {ω : Cocycle (trivialOuterAction (k := K) (S := S) D.toBased)}
      (V : PinnedRepresentative (S := S) E ω),
      IsExceptionalReference D →
      ∀ (Q₀ : AdjointQuotient V.model.val)
        (x : groupH1 K Q₀.quotient.val.X S),
        x = groupBasepoint K Q₀.quotient.val.X S

/-- Every inner form of the specified reference is isomorphic to it over the ground field. -/
def InnerFormsAreReference : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    let K := maximalUnramified F
    ∀ (S : Type u) [Field S] [Algebra K S] [IsSepClosure K S]
      {A : AdditiveLine K} {P : PinnedGroup A} {D : AttachedDatum P.pair}
      {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
      {E : SplitSequence P D l Q}
      {ω : Cocycle (trivialOuterAction (k := K) (S := S) D.toBased)}
      (V : PinnedRepresentative (S := S) E ω),
      IsExceptionalReference D →
      ∀ H : AffineAlgebraicGroup K, AreInnerForms (S := S) V.model.val H →
        Nonempty (V.model.val.val ≅ H.val)


end LinearAlgebraicGroups.Specs.ExceptionalFormsOverUnramifiedFields
