import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CanonicalSplitSubgroup

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

/-- The subnormal-series definition with every successive quotient isomorphic to Ga. -/
def HasAdditiveSeries {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (n : ℕ) (S : ClosedSeries G n), ∀ i < n,
    ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
        Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k)

def AdditiveSeriesCharacterization : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsSplitUnipotent G ↔ IsUnipotent G ∧ HasAdditiveSeries G

/-- A smooth connected unipotent group splits over some finite purely inseparable extension. -/
def FinitePurelyInseparableSplitness : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsUnipotent G →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ IsPurelyInseparable k K ∧
        IsSplitUnipotent (baseChangedAlgebraicGroup K G)

/-- Splitness descends along separable extensions, including transcendental ones. -/
def SeparableSplitnessDescent : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsUnipotent G →
    ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K],
      IsSplitUnipotent (baseChangedAlgebraicGroup K G) → IsSplitUnipotent G

end LinearAlgebraicGroups.Specs.Unipotent
