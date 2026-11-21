import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition
import Mathlib.RingTheory.AlgebraTower

/-!
Independent specification for K07.12.tower_law (paper.tex:3631–3640).
The three Algebra structures specify the embeddings, and IsScalarTower asserts
their compatibility. The product family uses the specified map E → L.
The basis indices and the three fields may lie in different universes.
Cardinal lifts only put the degrees in a common universe; no finiteness or
algebraicity is imposed on the basis or cardinal statements.
-/

universe u v w s t

namespace Specs.D07.Ch12.TowerLaw

noncomputable section

/-- The particular product family is a basis, with index set I × J. -/
def ProductBasis : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (I : Type s) (J : Type t) (e : Module.Basis I K E) (b : Module.Basis J E L),
    ∃ c : Module.Basis (I × J) K L,
      ∀ ij, c ij = algebraMap E L (e ij.1) * b ij.2

/-- [L:K] = [L:E][E:K] for cardinal-valued degree, including infinite degree. -/
def CardinalDegreeTower : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L],
    Cardinal.lift.{v} (Module.rank K L) =
      Cardinal.lift.{v} (Module.rank E L) * Cardinal.lift.{w} (Module.rank K E)

/-- If the two degrees are natural numbers m and n, the total degree is n*m;
all three natural degrees are positive. Finiteness is a hypothesis about
cardinal dimension, not finiteness of the underlying fields. -/
def NaturalDegreeTower : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (m n : ℕ),
    Module.rank K E = (m : Cardinal.{v}) →
    Module.rank E L = (n : Cardinal.{w}) →
    Module.rank K L = ((n * m : ℕ) : Cardinal.{w}) ∧
      0 < m ∧ 0 < n ∧ 0 < n * m

end

end Specs.D07.Ch12.TowerLaw
