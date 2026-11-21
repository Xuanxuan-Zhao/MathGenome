import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! The geometry used in both d04:05:active-constraints and d04:05:critical-cone.
Ambient functions represent maps on U. Finite function spaces are the canonical
coordinate representation of the Euclidean constraint blocks. No nonemptiness
of any block is imposed. The remaining block has its actual dimension k. -/
noncomputable section
open Set
namespace Specs.D04.C05.ActiveConstraintCoordinates
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

/-- All and only the inequalities vanishing at the basepoint. -/
abbrev Active {n s : ℕ} (h : E n → E s) (a : E n) :=
  {i : Fin s // h a i = 0}

/-- Equality rows followed by active inequality rows, as algebraic covectors.
The regularity hypotheses below guarantee that these derivative selectors are
actual derivatives. -/
def constraintRows {n q s : ℕ} (g : E n → E q) (h : E n → E s) (a : E n) :
    (Fin q ⊕ Active h a) → Module.Dual ℝ (E n) :=
  Sum.elim (fun j => (totalDerivative (fun x => g x j) a).toLinearMap)
    (fun i => (totalDerivative (fun x => h x i.val) a).toLinearMap)

/-- The forward map is prescribed, apart from its final linear block. -/
def coordinateMap {n q s k : ℕ} (g : E n → E q) (h : E n → E s)
    (c : E q) (a : E n) (w : E n →ₗ[ℝ] E k) (x : E n) :
    (Fin q → ℝ) × ((Active h a → ℝ) × E k) :=
  (fun j => g x j - c j, (fun i => h x i.val, w x))

/-- The original feasible set retains its ambient domain. -/
def Feasible {n q s : ℕ} (U : Set (E n)) (g : E n → E q)
    (h : E n → E s) (c : E q) : Set (E n) :=
  {x | x ∈ U ∧ g x = c ∧ ∀ i, 0 ≤ h x i}

/-- All compatible domains, inverse identities, regularity, and the precise
normal form, on a genuine open product neighborhood. -/
def Chart {n q s k : ℕ} (r : ℕ) (U : Set (E n))
    (g : E n → E q) (h : E n → E s) (c : E q) (a : E n)
    (w : E n →ₗ[ℝ] E k) (X : Set (E n))
    (A : Set (Fin q → ℝ)) (B : Set (Active h a → ℝ)) (C : Set (E k))
    (inverse : ((Fin q → ℝ) × ((Active h a → ℝ) × E k)) → E n) : Prop :=
  q + Fintype.card (Active h a) + k = n ∧
  IsOpen X ∧ IsOpen A ∧ IsOpen B ∧ IsOpen C ∧
  a ∈ X ∧ (0 : Fin q → ℝ) ∈ A ∧ (0 : Active h a → ℝ) ∈ B ∧ w a ∈ C ∧
  X ⊆ U ∧
  coordinateMap g h c a w a = (0, (0, w a)) ∧
  BijOn (coordinateMap g h c a w) X (A ×ˢ (B ×ˢ C)) ∧
  MapsTo inverse (A ×ˢ (B ×ˢ C)) X ∧
  LeftInvOn inverse (coordinateMap g h c a w) X ∧
  RightInvOn inverse (coordinateMap g h c a w) (A ×ˢ (B ×ˢ C)) ∧
  CrOn r X (coordinateMap g h c a w) ∧ CrOn r (A ×ˢ (B ×ˢ C)) inverse ∧
  (∀ x ∈ X, ∀ i : Fin s, h a i ≠ 0 → 0 < h x i) ∧
  (∀ x ∈ X, x ∈ Feasible U g h c ↔
    (coordinateMap g h c a w x).1 = 0 ∧
    ∀ i : Active h a, 0 ≤ (coordinateMap g h c a w x).2.1 i) ∧
  (∀ y ∈ A ×ˢ (B ×ˢ C), inverse y ∈ Feasible U g h c ↔
    y.1 = 0 ∧ ∀ i : Active h a, 0 ≤ y.2.1 i)

/-- In particular the theorem supplies both the C¹ and C² constructions.
The stronger finite-r statement uses precisely the same hypotheses. -/
def active_constraint_coordinatesType : Prop :=
  ∀ {n q s : ℕ} (r : ℕ) (U : Set (E n)) (g : E n → E q)
    (h : E n → E s) (c : E q) (a : E n),
    1 ≤ r → IsOpen U → CrOn r U g → CrOn r U h →
    a ∈ U → g a = c → (∀ i, 0 ≤ h a i) →
    LinearIndependent ℝ (constraintRows g h a) →
    ∃ (k : ℕ) (w : E n →ₗ[ℝ] E k), ∃ X A B C inverse,
      Chart r U g h c a w X A B C inverse

end Specs.D04.C05.ActiveConstraintCoordinates
