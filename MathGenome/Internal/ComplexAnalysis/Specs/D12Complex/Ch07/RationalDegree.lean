import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.RationalInfinity
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.AlgebraicClosure

/-! Degree and fibers in paper.tex:1818–1851. Multiplicity is defined from the
actual sphere map in a source coordinate. At a finite target it is the zero
order of F-c; at infinity it is the pole order. `untopD` is used only to make
the definition total; the nonconstant rational theorems prove finite orders. -/
noncomputable section
open scoped Classical
-- Shared objects have Spec-owned names; candidate targets are declared separately.
namespace Specs.D12Complex.Ch07.RationalDegree.Objects
open _root_.D12Complex

/-- The scalar expression of a sphere map in the appropriate source chart. -/
def sourceFunction (F : RiemannSphere → RiemannSphere) (p : RiemannSphere) : ℂ → ℂ :=
  if p = sphereInfty then scalarFinitePart (F ∘ infinityParametrization)
  else scalarFinitePart (F ∘ sphereFinite)

def sourceCenter (p : RiemannSphere) : ℂ :=
  if p = sphereInfty then 0 else finiteCoordinate p

/-- Zero order of F-c, or pole order of F when the target is infinity.
The positive part is zero away from the fiber. -/
def localMultiplicity (F : RiemannSphere → RiemannSphere)
    (c p : RiemannSphere) : ℕ :=
  if c = sphereInfty then
    (-(meromorphicOrderAt (sourceFunction F p) (sourceCenter p)).untopD 0).toNat
  else
    ((meromorphicOrderAt (fun z => sourceFunction F p z - finiteCoordinate c)
      (sourceCenter p)).untopD 0).toNat

/-- The usual algebraic nonconstancy condition for P/Q with Q nonzero. -/
def Nonconstant (P Q : Polynomial ℂ) : Prop := ∀ c : ℂ, P ≠ Polynomial.C c * Q

end Specs.D12Complex.Ch07.RationalDegree.Objects

namespace Specs.D12Complex.Ch07.RationalDegree
open _root_.D12Complex
open Objects
open Specs.D12Complex.Ch07.RationalInfinity.Objects

def sourceFunction_type := (RiemannSphere → RiemannSphere) → RiemannSphere → ℂ → ℂ
def sourceFunction_value : sourceFunction_type := fun F p =>
  if p = sphereInfty then scalarFinitePart (F ∘ infinityParametrization)
  else scalarFinitePart (F ∘ sphereFinite)

def sourceCenter_type := RiemannSphere → ℂ
def sourceCenter_value : sourceCenter_type := fun p =>
  if p = sphereInfty then 0 else finiteCoordinate p

def localMultiplicity_type := (RiemannSphere → RiemannSphere) → RiemannSphere → RiemannSphere → ℕ
def localMultiplicity_value : localMultiplicity_type := fun F c p =>
  if c = sphereInfty then
    (-(meromorphicOrderAt (sourceFunction F p) (sourceCenter p)).untopD 0).toNat
  else
    ((meromorphicOrderAt (fun z => sourceFunction F p z - finiteCoordinate c)
      (sourceCenter p)).untopD 0).toNat

def Nonconstant_type := Polynomial ℂ → Polynomial ℂ → Prop
def Nonconstant_value : Nonconstant_type := fun P Q => ∀ c : ℂ, P ≠ Polynomial.C c * Q

/-- Neither the original function nor its translates is a zero germ. Thus the
integer extraction in localMultiplicity never discards an infinite order here. -/
def local_orders_finite_type : Prop := ∀ (P Q : Polynomial ℂ), Q ≠ 0 →
  IsRelPrime P Q → Nonconstant P Q → ∀ p : RiemannSphere,
    meromorphicOrderAt (sourceFunction (extension P Q) p) (sourceCenter p) ≠ ⊤ ∧
    ∀ c : ℂ, meromorphicOrderAt (fun z => sourceFunction (extension P Q) p z - c)
      (sourceCenter p) ≠ ⊤

/-- A multiset lists every preimage exactly its analytic local number of times. -/
def fiber_count_type : Prop := ∀ (P Q : Polynomial ℂ), Q ≠ 0 →
  IsRelPrime P Q → Nonconstant P Q → ∀ c : RiemannSphere,
  ∃ A : Multiset RiemannSphere,
    A.card = max P.natDegree Q.natDegree ∧
    (∀ p, p ∈ A ↔ extension P Q p = c) ∧
    (∀ p, A.count p = localMultiplicity (extension P Q) c p)

def fibers_finite_type : Prop := ∀ (P Q : Polynomial ℂ), Q ≠ 0 →
  IsRelPrime P Q → Nonconstant P Q → ∀ c : RiemannSphere,
    {p | extension P Q p = c}.Finite

/-- Explicit sum over the finite fiber. -/
def fiber_total_type : Prop := ∀ (P Q : Polynomial ℂ), Q ≠ 0 →
  IsRelPrime P Q → Nonconstant P Q → ∀ c : RiemannSphere,
  ∃ S : Finset RiemannSphere,
    (∀ p, p ∈ S ↔ extension P Q p = c) ∧
    ∑ p ∈ S, localMultiplicity (extension P Q) c p = max P.natDegree Q.natDegree

def zeros_poles_count_type : Prop := ∀ (P Q : Polynomial ℂ), Q ≠ 0 →
  IsRelPrime P Q → Nonconstant P Q →
  (∃ Z : Multiset RiemannSphere,
    Z.card = max P.natDegree Q.natDegree ∧
    (∀ p, p ∈ Z ↔ extension P Q p = sphereFinite 0) ∧
    (∀ p, Z.count p = localMultiplicity (extension P Q) (sphereFinite 0) p)) ∧
  (∃ B : Multiset RiemannSphere,
    B.card = max P.natDegree Q.natDegree ∧
    (∀ p, p ∈ B ↔ extension P Q p = sphereInfty) ∧
    (∀ p, B.count p = localMultiplicity (extension P Q) sphereInfty p))

def nonzero_constant_type : Prop := ∀ c : ℂ, c ≠ 0 →
  (∀ p : RiemannSphere, (fun _ => sphereFinite c) p ≠ sphereFinite 0 ∧
    (fun _ => sphereFinite c) p ≠ sphereInfty) ∧
  (∀ p : RiemannSphere,
    localMultiplicity (fun _ => sphereFinite c) (sphereFinite 0) p = 0 ∧
    localMultiplicity (fun _ => sphereFinite c) sphereInfty p = 0)

/-- Nonconstancy really is that of the filled sphere function. -/
def nonconstant_iff_type : Prop := ∀ (P Q : Polynomial ℂ), Q ≠ 0 →
  IsRelPrime P Q → (Nonconstant P Q ↔
    ¬ ∃ c : RiemannSphere, extension P Q = fun _ => c)

end Specs.D12Complex.Ch07.RationalDegree
