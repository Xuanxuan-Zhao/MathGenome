import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ProperDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.FactorialBridge

/-! Finite repeated differentiation of the shared bounded-region Riemann
integral. The fields T are continuous extensions of the actual derivatives
on S; existence is asserted separately, through the shared pointwise predicate.
No derivatives in the spatial variable, or beyond the finite order r, are assumed. -/
noncomputable section
open Set
namespace Specs.D04.C08.FiniteRepeated
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C06.JordanRegions.Model

def finite_repeatedType : Prop :=
  ∀ {n m k : ℕ} {S : Set (E n)} {P : Set (E m)}, Jordan S → IsOpen P →
  ∀ (r : ℕ) (f : S → E m → E k)
    (T : (j : ℕ) → closure S → E m → Differential (E m) (E k) j),
  (∀ x p, p ∈ P → TimesDifferentiableAt r P (f x) p) →
  (∀ j, j ≤ r → Continuous (fun z : closure S × P => T j z.1 z.2)) →
  (∀ j, j ≤ r → ∀ (x : S) p, p ∈ P →
    T j ⟨x, subset_closure x.property⟩ p = higherDifferential j (f x) p) →
  let F := fun p => vectorRegionIntegral (fun x => f x p)
  (∀ p ∈ P, VectorRegionIntegrable (fun x => f x p)) ∧
  CrOn r P F ∧
  (∀ j, j ≤ r → ∀ p ∈ P, ∀ v : Fin j → E m,
    VectorRegionIntegrable (fun x => higherDifferential j (f x) p v) ∧
    higherDifferential j F p v =
      vectorRegionIntegral (fun x => higherDifferential j (f x) p v)) ∧
  (∀ α : MultiIndex m, multiIndexDegree α ≤ r → ∀ p ∈ P,
    VectorRegionIntegrable (fun x => multiIndexPartial α (f x) p) ∧
    multiIndexPartial α F p = vectorRegionIntegral (fun x => multiIndexPartial α (f x) p))
end Specs.D04.C08.FiniteRepeated
