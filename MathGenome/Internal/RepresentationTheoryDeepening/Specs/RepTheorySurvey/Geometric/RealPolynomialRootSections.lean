import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Connected.Basic

namespace RepTheorySurvey.Geometric.RealPolynomialRootSectionsSpecs

universe u v

open Set

def DerivativeFamilyType : Type (u + 1) :=
  ∀ {σ : Type u}, Finset (Polynomial (MvPolynomial σ ℝ)) →
    ℝ → ℝ → Finset (Polynomial (MvPolynomial σ ℝ))

/-- The nonzero vertical derivatives, including order zero, and the two cutoff polynomials. -/
noncomputable def derivativeFamily : DerivativeFamilyType.{u} := by
  classical
  intro σ P a b
  exact insert (Polynomial.X - Polynomial.C (MvPolynomial.C a))
    (insert (Polynomial.X - Polynomial.C (MvPolynomial.C b))
      (P.biUnion fun p =>
        ((Finset.range (p.natDegree + 1)).image fun k =>
          Polynomial.derivative^[k] p).filter (fun q => q ≠ 0)))

def DerivativeProductType : Type (u + 1) :=
  ∀ {σ : Type u}, Finset (Polynomial (MvPolynomial σ ℝ)) →
    ℝ → ℝ → Polynomial (MvPolynomial σ ℝ)

/-- The product with each distinct member of the derivative family appearing once. -/
noncomputable def derivativeProduct : DerivativeProductType.{u} :=
  fun P a b => (derivativeFamily P a b).prod id

/-- The derivative product has a nonzero real constant leading coefficient. -/
def DerivativeProductLeadingCoeff : Prop :=
  ∀ (σ : Type u) [Finite σ] (P : Finset (Polynomial (MvPolynomial σ ℝ))) (a b : ℝ),
    a < b →
    (∀ p ∈ P, ∃ c : ℝ, c ≠ 0 ∧ p.leadingCoeff = MvPolynomial.C c) →
    ∃ c : ℝ, c ≠ 0 ∧ (derivativeProduct P a b).leadingCoeff = MvPolynomial.C c

/-- Ordered root sections on the ambient closures of the pieces, with signs on graphs
and bands and compatible restrictions to pieces in those closures. -/
def RealPolynomialRootSections : Prop :=
  ∀ (σ : Type u) [Finite σ] (α : Type v) [Finite α]
    (P : Finset (Polynomial (MvPolynomial σ ℝ))) (a b : ℝ) (C : α → Set (σ → ℝ)),
    a < b →
    (∀ p ∈ P, ∃ c : ℝ, c ≠ 0 ∧ p.leadingCoeff = MvPolynomial.C c) →
    (∀ i, (C i).Nonempty) →
    (∀ i, IsPreconnected (C i)) →
    let F := derivativeProduct P a b
    (∀ i, ∀ x y : C i,
      ((F.map (MvPolynomial.eval x.val)).rootSet ℂ).ncard =
        ((F.map (MvPolynomial.eval y.val)).rootSet ℂ).ncard) →
    let signConstantOn := fun (s : Set ((σ → ℝ) × ℝ)) =>
      ∀ p ∈ P, ∀ z ∈ s, ∀ w ∈ s,
        let r := (p.map (MvPolynomial.eval z.1)).eval z.2
        let t := (p.map (MvPolynomial.eval w.1)).eval w.2
        (0 ≤ r ↔ 0 ≤ t) ∧ (r ≤ 0 ↔ t ≤ 0)
    ∃ (m : α → ℕ) (h : (i : α) → Fin (m i + 2) → closure (C i) → Icc a b),
      let level := fun (i : α) (k : Fin (m i + 2)) (x : C i) =>
        h i k ⟨x.val, subset_closure x.property⟩
      (∀ i k, Continuous (h i k)) ∧
      (∀ i (x : closure (C i)), Monotone fun k => h i k x) ∧
      (∀ i (x : C i), StrictMono fun k => level i k x) ∧
      (∀ i (x : closure (C i)), (h i 0 x).val = a ∧ (h i (Fin.last (m i + 1)) x).val = b) ∧
      (∀ i (x : C i) (t : ℝ), (∃ k, (level i k x).val = t) ↔
        t ∈ Icc a b ∧ t ∈ (F.map (MvPolynomial.eval x.val)).rootSet ℝ) ∧
      (∀ i k, signConstantOn (range fun x : C i => (x.val, (level i k x).val))) ∧
      (∀ i (k : Fin (m i + 1)), signConstantOn
        {z | ∃ x : C i, x.val = z.1 ∧
          (level i k.castSucc x).val < z.2 ∧ z.2 < (level i k.succ x).val}) ∧
      (∀ i j (hji : C j ⊆ closure (C i)),
        ∃ q : Fin (m i + 2) → Fin (m j + 2), Monotone q ∧ Function.Surjective q ∧
          ∀ k (x : closure (C j)),
            h i k ⟨x.val, closure_minimal hji isClosed_closure x.property⟩ = h j (q k) x)

end RepTheorySurvey.Geometric.RealPolynomialRootSectionsSpecs
