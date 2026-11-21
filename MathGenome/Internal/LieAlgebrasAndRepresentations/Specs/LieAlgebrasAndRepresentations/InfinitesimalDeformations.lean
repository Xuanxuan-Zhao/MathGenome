import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AbelianExtensions
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! LA-I02, source expanded lines 4101–4122. Coordinates `(x,u)` mean
`x + εu` in `g ⊗ k[ε]`. Alternation, rather than only skew symmetry,
is required over arbitrary fields. The coefficient action is adjoint. -/
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.InfinitesimalDeformations
open LieModule.Cohomology
variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]

/-- The scalar action of `r + εs` on `x + εu`. -/
def dualSMul (r : DualNumber k) (p : g × g) : g × g :=
  (r.fst • p.1, r.fst • p.2 + r.snd • p.1)

/-- Multiplication on the scalar factor of the actual scalar extension. -/
def tensorScalar (r : DualNumber k) :
    (g ⊗[k] DualNumber k) →ₗ[k] (g ⊗[k] DualNumber k) :=
  TensorProduct.map LinearMap.id
    { toFun := fun s => r * s
      map_add' := mul_add r
      map_smul' := by
        intro a s
        ext <;> simp [mul_add, mul_assoc, mul_comm, mul_left_comm] }

/-- All alternating dual-number-bilinear brackets reducing to the fixed bracket.
The underlying bilinearity is over k; the two further equations impose precisely
linearity over the dual numbers. -/
structure Deformation where
  bracket : (g × g) →ₗ[k] (g × g) →ₗ[k] (g × g)
  alternating : ∀ p, bracket p p = 0
  scalar_left : ∀ r p q, bracket (dualSMul k g r p) q = dualSMul k g r (bracket p q)
  scalar_right : ∀ r p q, bracket p (dualSMul k g r q) = dualSMul k g r (bracket p q)
  reduction : ∀ p q, (bracket p q).1 = ⁅p.1,q.1⁆
  jacobi : ∀ p q r, bracket p (bracket q r) + bracket q (bracket r p) +
    bracket r (bracket p q) = 0

/-- Every allowed change of coordinates is dual-number-linear and is identity
modulo ε. Invertibility is part of the definition, not an assumption on `a`. -/
structure CoordinateChange where
  equiv : (g × g) ≃ₗ[k] (g × g)
  scalar : ∀ r p, equiv (dualSMul k g r p) = dualSMul k g r (equiv p)
  reduction : ∀ p, (equiv p).1 = p.1

variable {k g}
def Equivalent (B C : Deformation k g) : Prop :=
  ∃ T : CoordinateChange k g, ∀ p q,
    T.equiv (C.bracket p q) = B.bracket (T.equiv p) (T.equiv q)

/-- The source bracket μ+εc in coordinates; the cross terms use the adjoint action. -/
def bracketFormula (c : twoCochain k g g) (p q : g × g) : g × g :=
  LieAlgebrasAndRepresentations.AbelianExtensions.twistedBracket c p q

def shear (a : g →ₗ[k] g) (p : g × g) : g × g := (p.1,p.2 + a p.1)

end LieAlgebrasAndRepresentations.InfinitesimalDeformations

namespace Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations
open _root_.LieAlgebrasAndRepresentations.InfinitesimalDeformations
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions
open LieModule.Cohomology _root_.AdvancedHomologicalAlgebra.CE
variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]

/-- The coordinate model is the actual scalar extension, with its dual action. -/
def tensorModelStatement : Prop :=
  ∃ e : (g ⊗[k] DualNumber k) ≃ₗ[k] (g × g),
    (∀ x r, e (x ⊗ₜ[k] r) = (r.fst • x,r.snd • x)) ∧
    ∀ r z, e (tensorScalar k g r z) = dualSMul k g r (e z)

def jacobiStatement : Prop :=
  ∀ c : twoCochain k g g,
    (∀ p q r, bracketFormula c p (bracketFormula c q r) +
      bracketFormula c q (bracketFormula c r p) +
      bracketFormula c r (bracketFormula c p q) = 0) ↔ d₂₃ k g g c = 0

/-- Explicit coefficient with the left-nested source sign `-dc`. -/
def linearJacobiStatement : Prop :=
  ∀ (c : twoCochain k g g) (x y z : g),
    (⁅c x y,z⁆ + c ⁅x,y⁆ z) + (⁅c y z,x⁆ + c ⁅y,z⁆ x) +
      (⁅c z x,y⁆ + c ⁅z,x⁆ y) = -(d₂₃ k g g c x y z)

def normalFormStatement : Prop :=
  ∀ B : Deformation k g, ∃! c : twoCocycle k g g,
    ∀ p q, B.bracket p q = bracketFormula c.1 p q

def modelsStatement : Prop :=
  ∀ c : twoCocycle k g g, ∃ B : Deformation k g,
    ∀ p q, B.bracket p q = bracketFormula c.1 p q

def coordinatesStatement : Prop :=
  (∀ T : CoordinateChange k g, ∃! a : g →ₗ[k] g, ∀ p, T.equiv p = shear a p) ∧
  (∀ a : g →ₗ[k] g, ∃ T : CoordinateChange k g, ∀ p, T.equiv p = shear a p)

def pullbackStatement : Prop :=
  ∀ (c : twoCochain k g g) (a : g →ₗ[k] g) (p q : g × g),
    shear a (bracketFormula (c + d₁₂ k g g a) p q) =
      bracketFormula c (shear a p) (shear a q)

/-- Surjectivity and the exact coordinate-equivalence relation establish the
bijection of orbits with the ordinary H² of the canonical exterior complex.
The final clause fixes the parametrization on every displayed coefficient. -/
def classificationStatement : Prop :=
  ∀ (δ : ∀ n, (W k g n →ₗ[k] g) →ₗ[k] (W k g (n+1) →ₗ[k] g)),
    (∀ n, (δ (n+1)).comp (δ n) = 0) → HasLieCEFormula δ →
    ∃ C : Deformation k g → CEH2 δ,
      Function.Surjective C ∧
      (∀ B D, C B = C D ↔ Equivalent B D) ∧
      ∀ B (c : twoCocycle k g g),
        (∀ p q, B.bracket p q = bracketFormula c.1 p q) →
        ∃ h : LinearMap.ker (δ 2),
          (∀ x y, h.1 (wedge k g 2 ![x,y]) = c.1 x y) ∧
          C B = Submodule.Quotient.mk h

def tensorModelExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    tensorModelStatement k g

def jacobiExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    jacobiStatement k g

def linearJacobiExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    linearJacobiStatement k g

def normalFormExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    normalFormStatement k g

def modelsExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    modelsStatement k g

def coordinatesExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    coordinatesStatement k g

def pullbackExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    pullbackStatement k g

def classificationExpected : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g],
    classificationStatement k g

end Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations
