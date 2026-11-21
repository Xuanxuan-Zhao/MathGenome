import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
Independent specification of `K07.01.dihedral_quaternion_models`,
`paper.tex:363–375`. The geometric group consists of ALL Euclidean
isometries preserving the polygon. Its source name is `D_{2n}`: the
library parameter `DihedralGroup n` counts vertices, not group elements.
The quaternion matrices and their GL subgroup use the upstream canonical
objects verbatim. No classification, finiteness, or normal form is assumed.
-/

noncomputable section
namespace Specs.D07.Ch01.DihedralQuaternionModels

open Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
open scoped ComplexConjugate

/-- The actual geometric generators, their relations, unique normal forms,
generation, and noncommutativity, for every center, size and first vertex.
`Fin n × Bool` indexes exactly the source's `2n` distinct motions. -/
def DihedralModels : Prop :=
  ∀ (n : ℕ) (c a : ℂ), 3 ≤ n → a ≠ 0 →
    Finite (symmetryGroup (vertices n c a)) ∧
    Nat.card (symmetryGroup (vertices n c a)) = 2 * n ∧
    ∃ e : DihedralGroup n ≃* symmetryGroup (vertices n c a),
      let r := e (DihedralGroup.r 1)
      let s := e (DihedralGroup.sr 0)
      (∀ z : ℂ, (r : ℂ ≃ᵢ ℂ) z = c + root n * (z - c)) ∧
      (∀ z : ℂ, (s : ℂ ≃ᵢ ℂ) z = c + a * conj ((z - c) / a)) ∧
      r ^ n = 1 ∧ s ^ 2 = 1 ∧ s * r * s = r⁻¹ ∧
      s * r = r⁻¹ * s ∧
      (∀ f : symmetryGroup (vertices n c a),
        ∃! p : Fin n × Bool, f = if p.2 then r ^ p.1.val * s else r ^ p.1.val) ∧
      Subgroup.closure ({r, s} : Set (symmetryGroup (vertices n c a))) = ⊤ ∧
      r * s ≠ s * r

/-- The original exact matrix identities (including `IJ ≠ JI`), all eight
matrices distinct, their multiplication/inverse closure, and their faithful
identification with a subgroup of GL₂(ℂ) of cardinality eight. -/
def QuaternionModels : Prop :=
  DihedralQuaternionModelsQuaternionMatrices.MatrixIdentities ∧
  DihedralQuaternionModelsQuaternionMatrices.EightDistinct ∧
  DihedralQuaternionModelsQuaternionMatrices.MatrixClosure ∧
  DihedralQuaternionModelsQuaternionMatrices.QuaternionMatrixModel

/-- Both concrete families, with the order statement also expressed for
an arbitrary set satisfying the upstream regular-polygon predicate. -/
def ConcreteNonabelianFamilies : Prop :=
  DihedralModels ∧
  DihedralQuaternionModelsPolygonSymmetries.GeometricOrder ∧
  QuaternionModels

end Specs.D07.Ch01.DihedralQuaternionModels
