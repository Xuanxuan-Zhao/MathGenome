import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Connected.PathConnected
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace LinearAlgebraicGroups.Arithmetic.RealDefiniteSpinSpec

open CliffordAlgebra
open LinearAlgebraicGroups.Albert.SpinSpecification

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def IsDefinite (q : QuadraticForm ℝ V) : Prop :=
  (∀ x ≠ 0, 0 < q x) ∨ (∀ x ≠ 0, q x < 0)

/-- The real spin points inside the units of the actual Clifford algebra. -/
def spinPoints (q : QuadraticForm ℝ V) : Set (CliffordAlgebra q)ˣ :=
  {a | (a : CliffordAlgebra q) ∈ evenOdd q 0 ∧ reverse (a : CliffordAlgebra q) * a = 1 ∧
    Set.MapsTo (fun x => (a : CliffordAlgebra q) * x * ↑a⁻¹) (LinearMap.range (ι q))
      (LinearMap.range (ι q)) ∧
    Set.MapsTo (fun x => (↑a⁻¹ : CliffordAlgebra q) * x * a) (LinearMap.range (ι q))
      (LinearMap.range (ι q))}

/-- The embedded real point set with the subspace topology of the Clifford algebra. -/
def cliffordPoints (q : QuadraticForm ℝ V) : Set (CliffordAlgebra q) :=
  Units.val '' spinPoints q

def PointComparison : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] (q : QuadraticForm ℝ V)
    (a : (ScalarClifford q ℝ)ˣ),
    a ∈ spinUnits q ℝ ↔
      Units.map (Algebra.TensorProduct.lid ℝ (CliffordAlgebra q)).toMonoidHom a ∈ spinPoints q

/-- The action is restriction of conjugation to the Clifford vector subspace. -/
def Acts (q : QuadraticForm ℝ V) (a : (CliffordAlgebra q)ˣ) (g : V ≃ₗ[ℝ] V) : Prop :=
  ∀ x, ι q (g x) = (a : CliffordAlgebra q) * ι q x * ↑a⁻¹

def VectorAction : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (q : QuadraticForm ℝ V), IsDefinite q →
    (∀ a ∈ spinPoints q, (∃! g, Acts q a g) ∧
      ∀ g, Acts q a g → (∀ x, q (g x) = q x) ∧ LinearMap.det g.toLinearMap = 1 ∧
        (g = 1 ↔ (a : CliffordAlgebra q) = 1 ∨ (a : CliffordAlgebra q) = -1)) ∧
    ∀ g : V ≃ₗ[ℝ] V, (∀ x, q (g x) = q x) → LinearMap.det g.toLinearMap = 1 →
      ∃ a ∈ spinPoints q, Acts q a g

def PathConnected : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (q : QuadraticForm ℝ V), IsDefinite q → 2 ≤ Module.finrank ℝ V →
    @IsPathConnected _ (moduleTopology ℝ (CliffordAlgebra q)) (cliffordPoints q)

/-- The half-angle circle for any normalized orthogonal pair, with the Clifford sign convention. -/
def PlaneLift : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (q : QuadraticForm ℝ V), IsDefinite q →
    ∀ (s : ℝ) (e f : V), s * s = 1 → q e = s → q f = s → q.polarBilin e f = 0 →
    let B := ι q e * ι q f
    B * B = -1 ∧
    ∃ p : ℝ → (CliffordAlgebra q)ˣ,
      @Continuous ℝ (CliffordAlgebra q) _ (moduleTopology ℝ (CliffordAlgebra q))
        (fun θ => (p θ : CliffordAlgebra q)) ∧
      (p 0 : CliffordAlgebra q) = 1 ∧ (p (2 * Real.pi) : CliffordAlgebra q) = -1 ∧
      ∀ θ,
        p θ ∈ spinPoints q ∧
        (p θ : CliffordAlgebra q) = Real.cos (θ / 2) • (1 : CliffordAlgebra q) +
          Real.sin (θ / 2) • B ∧
        ∃ g : V ≃ₗ[ℝ] V, Acts q (p θ) g ∧
          g e = Real.cos θ • e - (s * Real.sin θ) • f ∧
          g f = (s * Real.sin θ) • e + Real.cos θ • f ∧
          ∀ x, q.polarBilin e x = 0 → q.polarBilin f x = 0 → g x = x

end
end LinearAlgebraicGroups.Arithmetic.RealDefiniteSpinSpec
