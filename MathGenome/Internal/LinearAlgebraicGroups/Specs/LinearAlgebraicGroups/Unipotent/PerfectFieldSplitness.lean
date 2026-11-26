import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect
import Mathlib.Topology.KrullDimension

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

/-- A closed subgroup scheme of the additive group in characteristic zero is
either the trivial group or the entire additive group. -/
def AdditiveSubgroupCharZero : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (H A : AffineAlgebraicGroup k)
    (f : H.val ⟶ A.val),
    Nonempty ((groupPointsFunctor k).obj A.val ≅ StandardGroups.additivePoints k) →
    IsClosedImmersion f.hom.hom.left →
    Nonempty (H.val ≅ Grp.trivial (SchemeOver k)) ∨ IsIso f

/-- Over a perfect field a smooth connected unipotent group has a central series
with every successive fppf quotient isomorphic to the additive group. Its
dimension-zero case admits a series of length zero. -/
def PerfectFieldSplitness : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsUnipotent G →
    ∃ (length : ℕ) (S : ClosedSeries G length), S.IsCentral ∧
      (topologicalKrullDim G.val.X.left ≤ 0 → length = 0) ∧
      ∀ i < length, ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
        IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
        Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k)

/-- Splitness of smooth connected unipotent groups over perfect fields in the
shared subnormal-series predicate. -/
def PerfectFieldIsSplitUnipotent : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsUnipotent G → IsSplitUnipotent G

end LinearAlgebraicGroups.Specs.Unipotent
