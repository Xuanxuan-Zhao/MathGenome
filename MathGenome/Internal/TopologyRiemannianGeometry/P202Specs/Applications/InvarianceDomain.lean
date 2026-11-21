import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Lemmas

/-! Invariance of domain, paper.tex 2854–2861 and 2886–2897 (T34).
The domain carries its ordinary subspace topology. There is no nonemptiness
or connectedness assumption, and the homeomorphism agrees with the given map. -/
noncomputable section
open Set Topology

namespace P202Specs.InvarianceDomain.Expected

/-- A continuous injection on any open subset of real n-space is open and
is a homeomorphism onto its open image. -/
def invarianceDomain : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (U : Set (EuclideanSpace ℝ (Fin n))), IsOpen U →
    ∀ (f : U → EuclideanSpace ℝ (Fin n)), Continuous f → Function.Injective f →
      IsOpenMap f ∧ IsOpen (range f) ∧
        ∃ h : U ≃ₜ range f, ∀ x : U, (h x).val = f x

end P202Specs.InvarianceDomain.Expected
