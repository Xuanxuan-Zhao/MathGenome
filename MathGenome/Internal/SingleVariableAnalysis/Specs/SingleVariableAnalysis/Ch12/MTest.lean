import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of `K03.12.m_test`, paper.tex:1277–1285.
The domain is an arbitrary type; a set E is represented by its subtype.
No topology, boundedness or nonemptiness is required of the domain.
In particular the empty set is included. Terms start at zero and the
partial sum through N includes terms 0,…,N, as in Ch11.PartialSums.
The majorant hypothesis is ordinary convergence of the nonnegative real
series, not an assumed uniform convergence or absolute convergence of u.
The three conclusions separately record uniform convergence of the scalar
series, uniform convergence of its modulus series, and absolute convergence
at every point. All limits are finite scalars in the canonical ℝ or ℂ.
-/

namespace Specs.SingleVariableAnalysis.Ch12.MTest

open Specs.SingleVariableAnalysis.Ch11.PartialSums

universe u

def realMTest : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℝ) (M : ℕ → ℝ),
    (∀ n, 0 ≤ M n) → (∀ n x, |u n x| ≤ M n) →
    realSeriesConvergesValue M →
      (∃ f : E → ℝ, Uniform.realUniformConvergesValue
        (fun N x => realPartialSumValue (fun n => u n x) N) f) ∧
      (∃ g : E → ℝ, Uniform.realUniformConvergesValue
        (fun N x => realPartialSumValue (fun n => |u n x|) N) g) ∧
      ∀ x, realSeriesConvergesValue (fun n => |u n x|)

def complexMTest : Prop :=
  ∀ {E : Type u} (u : ℕ → E → ℂ) (M : ℕ → ℝ),
    (∀ n, 0 ≤ M n) → (∀ n x, ‖u n x‖ ≤ M n) →
    realSeriesConvergesValue M →
      (∃ f : E → ℂ, Uniform.complexUniformConvergesValue
        (fun N x => complexPartialSumValue (fun n => u n x) N) f) ∧
      (∃ g : E → ℝ, Uniform.realUniformConvergesValue
        (fun N x => realPartialSumValue (fun n => ‖u n x‖) N) g) ∧
      ∀ x, realSeriesConvergesValue (fun n => ‖u n x‖)

end Specs.SingleVariableAnalysis.Ch12.MTest
