import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.BracketFromFlow
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! The commuting-flow and simultaneous-coordinate clauses of M06.07.
All flow families are the actual maximal integral-curve families, and all
local compositions below have their four required domain conditions.
-/
namespace SmoothManifolds.CommutingFieldsData
open ModelData AtlasData TangentBundleData VectorFieldData LieBracketData
  MaximalFlowData Set
universe u

/-- Both orders of the two time maps are defined at this initial state. -/
def CompositionsDefined {M : Type u} (F G : CurveFamily M)
    (p : M) (s t : ℝ) : Prop :=
  s ∈ (F.interval p).carrier ∧ t ∈ (G.interval p).carrier ∧
  t ∈ (G.interval (F.curve p s)).carrier ∧
  s ∈ (F.interval (G.curve p t)).carrier

/-- A common time width and open initial-state neighborhood for commutation.
This asserts no global existence for arbitrary partial compositions. -/
def CommuteNear {M : Type u} [TopologicalSpace M]
    (F G : CurveFamily M) (p : M) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
    ∀ q ∈ U, ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
      CompositionsDefined F G q s t ∧
        G.curve (F.curve q s) t = F.curve (G.curve q t) s

/-- Completeness expressed on a maximal family, independent of off-domain
representatives: every maximal time interval is all of the real line. -/
def CompleteFamily {M : Type u} (F : CurveFamily M) : Prop :=
  ∀ p, (F.interval p).carrier = univ

/-- The first k coordinate fields of an actual chart in the maximal atlas.
In dimension zero, and for k=0, the field equations have no indices. -/
def SimultaneousCoordinates {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B) (p : M) (hk : k ≤ n) : Prop :=
  ∃ e : ModelChart n .euclidean M, ∃ he : e ∈ S.smoothStructure.val,
    p ∈ e.source ∧ ∀ q (hq : q ∈ e.source) (i : Fin k),
      B.fiberCoordinates.equiv e he q hq ((X i).val q) =
        Pi.single (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin n) 1

end SmoothManifolds.CommutingFieldsData

namespace Specs.SmoothManifolds.Ch06.CommutingFields
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.VectorFieldData _root_.SmoothManifolds.LieBracketData
  _root_.SmoothManifolds.MaximalFlowData _root_.SmoothManifolds.CommutingFieldsData Set
universe u

/-- No completeness or nonvanishing assumption enters local commutation. -/
def local_commutationType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B), (∀ q, (b X Y).val q = 0) →
    ∀ (F G : CurveFamily M), IsMaximalFamily X F → IsMaximalFamily Y G →
    ∀ p : M, CommuteNear F G p

/-- Completeness supplies the full domain for both orders and all real times. -/
def complete_commutationType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B), (∀ q, (b X Y).val q = 0) →
    ∀ (F G : CurveFamily M), IsMaximalFamily X F → IsMaximalFamily Y G →
    CompleteFamily F → CompleteFamily G →
    ∀ (p : M) (s t : ℝ), CompositionsDefined F G p s t ∧
      G.curve (F.curve p s) t = F.curve (G.curve p t) s

/-- Pairwise brackets need only vanish on one open neighborhood of p.
The values are independent only at p. There is no completeness premise. -/
def simultaneous_coordinatesType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X : Fin k → SmoothField B) (p : M) (hk : k ≤ n),
    LinearIndependent ℝ (fun i => (X i).val p) →
    (∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ (i j : Fin k) (q : M), q ∈ U → (b (X i) (X j)).val q = 0) →
    SimultaneousCoordinates B X p hk

end Specs.SmoothManifolds.Ch06.CommutingFields
