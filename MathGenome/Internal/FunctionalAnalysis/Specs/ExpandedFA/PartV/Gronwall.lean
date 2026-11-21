import Specs.ExpandedFA.PartV.VolterraResolvent
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! Independent specification of paper.tex, `fa2:p5:gronwall`, 21926–21944.
Order is pointwise real order, and for systems it is componentwise order.
The canonical Volterra operator and its native ring inverse are reused.
All statements include the singleton interval and systems with zero components.
-/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV

/-- A scalar kernel acts by multiplication, rather than quadratic positivity. -/
def scalarVolterraKernel {a b : ℝ} (k : C(volterraTriangle a b, ℝ)) :
    C(volterraTriangle a b, ℝ →L[ℝ] ℝ) :=
  ⟨fun p => k p • (1 : ℝ →L[ℝ] ℝ), k.continuous.smul continuous_const⟩

/-- The matrix with its sole nonzero entry, equal to one, at `(i,j)`. -/
def matrixCoordinateOperator {n : ℕ} (i j : Fin n) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (Pi.single i 1)

/-- An arbitrary matrix of continuous real entries, acting on column vectors.
Each entry is independently continuous on the closed Volterra triangle. -/
def matrixVolterraKernel {a b : ℝ} {n : ℕ}
    (k : Fin n → Fin n → C(volterraTriangle a b, ℝ)) :
    C(volterraTriangle a b, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  ⟨fun p => ∑ i, ∑ j, k i j p • matrixCoordinateOperator i j,
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => (k i j).continuous.smul continuous_const))⟩

namespace GronwallSpec

/-- The scalar integral inequality on the actual compact interval. The
projection only extends the integrand and fixes every point of `[0,t]`. -/
def Gronwall : Prop := ∀ (T : ℝ) (hT : 0 ≤ T) (a M : ℝ),
  0 ≤ a → 0 ≤ M → ∀ z : C(VolterraInterval 0 T, ℝ),
  (∀ t, 0 ≤ z t) →
  (∀ t, z t ≤ a + M * ∫ s in 0..(t : ℝ), z (Set.projIcc 0 T hT s)) →
  ∀ t, z t ≤ a * Real.exp (M * (t : ℝ))

section Ordered
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [PartialOrder E]

/-- All inequalities between continuous maps below use pointwise order.
The last two clauses compare arbitrary subsolutions and supersolutions with
the unique solution furnished by the two-sided inverse. -/
def OrderConclusions {a b : ℝ} (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[ℝ] E)) (lam : ℝ) : Prop :=
  let V := VolterraOperatorSpec.OperatorValue ℝ E a b hab k
  let S := Ring.inverse (1 - lam • V)
  (∀ f : C(VolterraInterval a b, E), 0 ≤ f → 0 ≤ V f) ∧
  Monotone V ∧
  (∀ f g u₀ v₀ : C(VolterraInterval a b, E), f ≤ g → u₀ ≤ v₀ → ∀ n : ℕ,
    (fun u => f + lam • V u)^[n] u₀ ≤ (fun v => g + lam • V v)^[n] v₀) ∧
  (∀ f : C(VolterraInterval a b, E), 0 ≤ f → 0 ≤ S f) ∧
  Monotone S ∧
  (∀ u f : C(VolterraInterval a b, E), u - lam • V u ≤ f → u ≤ S f) ∧
  (∀ u f : C(VolterraInterval a b, E), f ≤ u - lam • V u → S f ≤ u)
end Ordered

/-- The scalar statement retains arbitrary continuous nonnegative kernels,
nonnegative parameters, and signed comparison data. -/
def ScalarComparison : Prop := ∀ (a b : ℝ) (hab : a ≤ b)
  (k : C(volterraTriangle a b, ℝ)), (∀ p, 0 ≤ k p) →
  ∀ lam : ℝ, 0 ≤ lam → OrderConclusions hab (scalarVolterraKernel k) lam

/-- Finite systems: the hypotheses concern the individual matrix entries,
and the conclusions use componentwise order throughout. -/
def SystemComparison : Prop := ∀ (a b : ℝ) (hab : a ≤ b) (n : ℕ)
  (k : Fin n → Fin n → C(volterraTriangle a b, ℝ)),
  (∀ i j p, 0 ≤ k i j p) → ∀ lam : ℝ, 0 ≤ lam →
  OrderConclusions hab (matrixVolterraKernel k) lam

/-- Explicit bridges to ordinary scalar multiplication and matrix-vector
multiplication, with integrals of those original expressions. -/
def ScalarIntegralFormula : Prop := ∀ (a b : ℝ) (hab : a ≤ b)
  (k : C(volterraTriangle a b, ℝ)) (f : C(VolterraInterval a b, ℝ)) t,
  VolterraOperatorSpec.OperatorValue ℝ ℝ a b hab (scalarVolterraKernel k) f t =
    ∫ s in a..(t : ℝ), k (volterraRetraction t s) * f (Set.projIcc a b hab s)

def SystemIntegralFormula : Prop := ∀ (a b : ℝ) (hab : a ≤ b) (n : ℕ)
  (k : Fin n → Fin n → C(volterraTriangle a b, ℝ))
  (f : C(VolterraInterval a b, Fin n → ℝ)) t i,
  VolterraOperatorSpec.OperatorValue ℝ (Fin n → ℝ) a b hab (matrixVolterraKernel k) f t i =
    ∫ s in a..(t : ℝ), ∑ j, k i j (volterraRetraction t s) *
      f (Set.projIcc a b hab s) j

end GronwallSpec
end ExpandedFA.PartV
