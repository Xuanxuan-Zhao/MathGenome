import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeAlgebras

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.SemifreeLifting

open _root_.DerivedFormalization.Affine

/-- The lifting assertion of Theorem 7.2. Both triangles commute as cdga maps. -/
def Lifting : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {A P C D : NonpositiveCDGA.{u,v} k}
    (aP : A ⟶ P) (aC : A ⟶ C) (aD : A ⟶ D)
    (f : P ⟶ D) (q : C ⟶ D),
    Semifree.IsSemifree A aP →
    aP ≫ f = aD → aC ≫ q = aD →
    NonpositiveCDGA.DegreewiseSurjective q → NonpositiveCDGA.IsQuasiIso q →
    ∃ g : P ⟶ C, aP ≫ g = aC ∧ g ≫ q = f

end Specs.DerivedFormalization.Affine.SemifreeLifting
