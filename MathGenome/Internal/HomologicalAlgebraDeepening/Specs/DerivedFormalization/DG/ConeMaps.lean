import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone

open CategoryTheory

universe u v w

namespace Specs.DerivedFormalization.DG.ConeMaps

open _root_.DerivedFormalization
open HomComplex (gradedHom component HomotopyEquation)
open ShiftCone (cone coneTerm coneInclusion coneProjection shiftMap)

/-- A specified right-linear homotopy of a square induces a strict map of cones. -/
def ConeSquareComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N M' N' : RightDGModuleModel A}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : gradedHom M N' (-1)), HomotopyEquation (f ≫ b) (a ≫ g) h →
    ∃ c : cone f ⟶ cone g,
      coneInclusion f ≫ c = b ≫ coneInclusion g ∧
      c ≫ coneProjection g = coneProjection f ≫ shiftMap 1 a ∧
      ∀ (o : A.Obj) (i : ℤ) (p : coneTerm M N o i),
        (c.app o).f i p =
          ((b.app o).f i p.1 + component h o (i+1) i (by omega) p.2,
            (a.app o).f (i+1) p.2)

/-- For composable strict maps the two outer comparisons and the deformation
retraction of the iterated cone are given by the indicated coordinate maps. -/
def OctahedronConeComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N P : RightDGModuleModel A} (f : M ⟶ N) (g : N ⟶ P),
    ∃ (α : cone f ⟶ cone (f ≫ g)) (β : cone (f ≫ g) ⟶ cone g)
      (r : cone α ⟶ cone g) (s : cone g ⟶ cone α)
      (H : gradedHom (cone α) (cone α) (-1)),
      (∀ (o : A.Obj) (i : ℤ) (p : coneTerm M N o i),
        (α.app o).f i p = ((g.app o).f i p.1, p.2)) ∧
      (∀ (o : A.Obj) (i : ℤ) (p : coneTerm M P o i),
        (β.app o).f i p = (p.1, (f.app o).f (i+1) p.2)) ∧
      coneInclusion f ≫ α = g ≫ coneInclusion (f ≫ g) ∧
      α ≫ coneProjection (f ≫ g) = coneProjection f ∧
      coneInclusion (f ≫ g) ≫ β = coneInclusion g ∧
      β ≫ coneProjection g = coneProjection (f ≫ g) ≫ shiftMap 1 f ∧
      (∀ (o : A.Obj) (i : ℤ) (p : coneTerm (cone f) (cone (f ≫ g)) o i),
        (r.app o).f i p = (p.1.1, (f.app o).f (i+1) p.1.2 + p.2.1)) ∧
      (∀ (o : A.Obj) (i : ℤ) (p : coneTerm N P o i),
        (s.app o).f i p = ((p.1, 0), (p.2, 0))) ∧
      (∀ (o : A.Obj) (i : ℤ) (p : coneTerm (cone f) (cone (f ≫ g)) o (i+1)),
        component H o (i+1) i (by omega) p = ((0, 0), (0, -p.1.2))) ∧
      s ≫ r = 𝟙 (cone g) ∧ HomotopyEquation (r ≫ s) (𝟙 (cone α)) H ∧
      coneInclusion α ≫ r = β ∧
      s ≫ coneProjection α = coneProjection g ≫ shiftMap 1 (coneInclusion f)

end Specs.DerivedFormalization.DG.ConeMaps
