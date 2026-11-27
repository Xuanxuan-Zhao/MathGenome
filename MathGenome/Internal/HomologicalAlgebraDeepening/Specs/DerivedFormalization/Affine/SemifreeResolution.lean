import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeAlgebras

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.SemifreeResolution

open _root_.DerivedFormalization.Affine

/-- A specified map of nonpositive cdgas over a characteristic-zero field
factors through a semifree extension of its domain. -/
def Factorization : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B),
    ∃ (P : NonpositiveCDGA.{u,v} k) (i : A ⟶ P) (p : P ⟶ B),
      i ≫ p = f ∧ Semifree.IsSemifree A i ∧
        NonpositiveCDGA.DegreewiseSurjective p ∧ NonpositiveCDGA.IsQuasiIso p

end Specs.DerivedFormalization.Affine.SemifreeResolution
