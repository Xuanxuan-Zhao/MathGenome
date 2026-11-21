import Mathlib.Topology.Closure

/-!
Independent statement of `paper.tex`, d10:01:kuratowski.
The operator is arbitrary and the only hypotheses are its four displayed
Kuratowski axioms. The topology and its closure are the canonical Mathlib
objects. In particular, no topology on X, monotonicity, separation, or
nonemptiness is assumed.
-/

open Set
universe u

namespace Specs.D10Topology.Ch01.KuratowskiReconstruction

def kuratowski_reconstruction : Prop :=
  ∀ {X : Type u} (c : Set X → Set X),
    (∀ A : Set X, A ⊆ c A) →
    (∀ A : Set X, c (c A) = c A) →
    (∀ A B : Set X, c (A ∪ B) = c A ∪ c B) →
    c ∅ = ∅ →
    ∃! t : TopologicalSpace X, ∀ A : Set X, @closure X t A = c A

end Specs.D10Topology.Ch01.KuratowskiReconstruction
