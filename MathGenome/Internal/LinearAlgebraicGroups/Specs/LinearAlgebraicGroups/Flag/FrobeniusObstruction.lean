import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.TorsorObstruction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.SeparableClosure

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.FrobeniusObstruction

open DiagonalizableGroups Fppf TorsorObstruction

noncomputable section

/-- The rational function field with indeterminate `RatFunc.X` over the prime field. -/
abbrev BaseField (p : ℕ) := RatFunc (ZMod p)

/-- The rank-one split multiplicative group, in its integer character presentation. -/
abbrev Gm (p : ℕ) [Fact p.Prime] : GroupScheme (BaseField p) :=
  specGroup (groupAlgebra (BaseField p) IntegerCharacters.{0})

/-- The `t`-adic valuation excludes a rational `p`-th root of `t`. -/
def NoRationalRoot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ b : BaseField p, b ^ p ≠ RatFunc.X

/-- The failure of lifting persists over every separable extension. -/
def NoSeparableRoot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra (BaseField p) L]
    [Algebra.IsSeparable (BaseField p) L], ∀ b : L,
      b ^ p ≠ algebraMap (BaseField p) L RatFunc.X

/-- The fppf power quotient and the obstruction at the point `t`.
The kernel is the group scheme of `p`-th roots of unity on all test algebras.
The final clause implies that every continuous Galois cocycle in the kernel's
separable-closure points is trivial. -/
def PowerQuotientObstruction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    let k := BaseField p
    let G := Gm p
    ∃ (c : (groupPointsFunctor k).obj G ≅ StandardGroups.multiplicativePoints k)
      (q : G ⟶ G) (H : ClosedSubgroup G),
      (∀ (R : TestAlgebra k) (g : Points G.X R),
        (c.hom.app R (g ≫ q.hom.hom) : Rˣ) = (c.hom.app R g : Rˣ) ^ p) ∧
      IsSchemeKernel q H ∧
      (∀ (R : TestAlgebra k) (g : Points G.X R),
        (∃ a : Points H.group.X R, a ≫ H.inclusion.hom.hom = g) ↔
          (c.hom.app R g : Rˣ) ^ p = 1) ∧
      (¬ Smooth H.group.X.hom) ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      LocallyOfFinitePresentation q.hom.hom.left ∧
      ∃ (e : rightQuotientSheaf H ≅ schemeFppfSheaf G.X),
        rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.map q.hom.hom ∧
        ∃ (t : fieldBase k ⟶ G.X) (x : RationalPoints H),
          (c.hom.app (CommAlgCat.of k k) (Over.mkIdTerminal.from _ ≫ t) : kˣ).val = RatFunc.X ∧
          (e.hom.hom.app (op (fieldBase k)) x).down = t ∧
          (∀ (R : TestAlgebra k) (g : Points G.X R),
            projectSection H g = (rightQuotientSheaf H).obj.map
                (Over.mkIdTerminal.from ((testSpec k).obj (op R))).op x ↔
              ((c.hom.app R g : Rˣ).val) ^ p = algebraMap k R RatFunc.X) ∧
          (¬ ∃ g : fieldBase k ⟶ G.X, g ≫ q.hom.hom = t) ∧
          (∃ h : IsTorsor (quotientFibreAction H x),
            (Quotient.mk _ (⟨quotientFibreAction H x, h⟩ : FppfTorsor (fieldBase k) H.group) :
              H1fppf k H.group) ≠ fieldNeutralClass H.group) ∧
          IsEmpty ((quotientFibreAction H x).Section
            (Over.mk (Over.mkIdTerminal.from
              ((testSpec k).obj (op (CommAlgCat.of k (SeparableClosure k))))))) ∧
          (∀ cocycle : (SeparableClosure k ≃ₐ[k] SeparableClosure k) →
              Points H.group.X (CommAlgCat.of k (SeparableClosure k)),
            cocycle = fun _ ↦ 1)

end

end LinearAlgebraicGroups.Specs.FrobeniusObstruction
