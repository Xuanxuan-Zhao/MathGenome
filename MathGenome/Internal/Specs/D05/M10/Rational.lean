import MathGenome.Internal.Specs.D05.M10.Rational.Presentation
import MathGenome.Internal.Specs.D05.M10.InvariantFactorComputation
import MathGenome.Internal.Specs.D05.M10.Companion
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Data.Matrix.Block

/-! Independent full statement of K05.10.rational, paper.tex:1483–1501.
The scalar field is arbitrary. The polynomial action on V is evaluation at T.
Residues are actual quotients by principal ideals, so the module isomorphism
expresses a direct sum of cyclic operators with exactly the stated annihilators.
The basis and matrix conclusion record the companion convention explicitly.
Finite products here are finite external direct sums. Empty indices are allowed.
-/
noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace Specs.D05.M10.Rational

abbrev Residue {K : Type*} [Field K] (d : K[X]) :=
  K[X] ⧸ (Ideal.span {d} : Submodule K[X] K[X])

abbrev Cokernel {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K[X]) :=
  (Fin n → K[X]) ⧸ LinearMap.range (Matrix.toLin' M)

/-- Polynomial elementary operations preserve the presented module. -/
def smith_cokernel : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K[X]) (ops : List (D05.M10.Smith.Operation K n n)),
    Nonempty (Cokernel M ≃ₗ[K[X]] Cokernel (D05.M10.Smith.run ops M))

/-- Full rational decomposition and its companion-block matrix over K.
No cyclic decomposition or splitting assumption occurs among the hypotheses. -/
def rational_form : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
  ∃ (r : ℕ) (d : Fin r → K[X]) (_hm : ∀ i, (d i).Monic),
    (∀ i, 0 < (d i).natDegree) ∧
    (∀ i j, i ≤ j → d i ∣ d j) ∧
    Nonempty (Module.AEval' T ≃ₗ[K[X]] (∀ i, Residue (d i))) ∧
    ∃ b : Module.Basis (Σ i, Fin (d i).natDegree) K V,
      LinearMap.toMatrix b b T =
        Matrix.blockDiagonal' (fun i => Specs.D05.M10.Companion.companionMatrix_value K (d i)) ∧
      (∑ i, (d i).natDegree) = Module.finrank K V

/-- The zero-dimensional case has no nonconstant blocks. -/
def zero_blocks : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (_hV : Module.finrank K V = 0) (T : Module.End K V),
    ∃ b : Module.Basis (Σ _i : Fin 0, Fin (0 : K[X]).natDegree) K V,
      LinearMap.toMatrix b b T = Matrix.blockDiagonal'
        (fun _ : Fin 0 => Specs.D05.M10.Companion.companionMatrix_value K (0 : K[X]))

end Specs.D05.M10.Rational
