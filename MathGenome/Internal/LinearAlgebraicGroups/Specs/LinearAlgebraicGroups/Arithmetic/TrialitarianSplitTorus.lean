import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntegralSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorusSpecification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs
open Albert.IntegralSmoothnessSpecification (SplitGroup geometricFiber)
open Albert.ShortDirectionSpecification (IntegralPresentation)
open Albert.FrameSpecification (frameAxis)
open Albert.SpinSpecification (SchemePoints)
open scoped CategoryTheory.MonObj

noncomputable section

/-- View a test point of the split fibre as a point of the integral group
over the same test algebra, with its canonical integer algebra structure. -/
def integralPoint {k : Type} [Field k] {P : IntegralPresentation} {G : SplitGroup P}
    {R : TestAlgebra k} (x : Points (geometricFiber G k).X R) :
    SchemePoints G.group (CommAlgCat.of ℤ R) :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℤ k))
  let a : Spec (CommRingCat.of R) ⟶ pullback G.group.X.hom f := x.left
  Over.homMk (a ≫ pullback.fst _ _) (by
    change (a ≫ pullback.fst _ _) ≫ G.group.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
    have h : a ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
      Over.w x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap ℤ k))
      (CommRingCat.ofHom (algebraMap k R))).symm.trans (by
        congr 1
        exact CommRingCat.hom_ext (RingHom.ext_int _ _)))

/-- Geometric conjugacy to the ordered-frame stabilizer, tested as an
equality of subgroup functors with a single conjugating point. -/
def IsGeometricFrameConjugate {k : Type} [Field k] {P : IntegralPresentation}
    {G : SplitGroup P} (H : ClosedSubgroup (geometricFiber G k)) : Prop :=
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  ∃ g : Points (F.obj (geometricFiber G k)).X (CommAlgCat.of K K),
    ∀ (R : TestAlgebra K) (x : Points (F.obj (geometricFiber G k)).X R),
      let gR := mapPoints (CommAlgCat.ofHom (Algebra.ofId K R)) g
      let y := baseChangePoint k K (geometricFiber G k).X R (gR * x * gR⁻¹)
      (∃ h : Points (F.obj H.group).X R, h ≫ (F.map H.inclusion).hom.hom = x) ↔
        ∀ i, G.action (CommAlgCat.of ℤ R)
          (integralPoint (k := k) (G := G) (R := (restrictTestAlgebra k K).obj R) y)
          (frameAxis i) = frameAxis i

/-- A nonarchimedean local form of the ordered-frame stabilizer inside the
split Albert group contains a closed split torus of positive dimension.
Mathlib's local-field hypothesis implies finiteness of the residue field. -/
def Statement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (P : IntegralPresentation) (G : SplitGroup P) (H : ClosedSubgroup (geometricFiber G k)),
    IsGeometricFrameConjugate H →
      ∃ (T : ClosedSubgroup H.group) (r : ℕ), 0 < r ∧
        Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift (Fin r))).val)

end
end LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorusSpecification
