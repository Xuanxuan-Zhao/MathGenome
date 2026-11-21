import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.DerivedTensorAction
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurWeylDuality

/-! FR-D10, source lines 1683–1740. The field is ℂ and V is finite-dimensional.
The enveloping map and the actions on the actual equivariant Hom spaces are
specified by their generator/postcomposition formulas. Irreducibility is
expressed as the invariant-subspace criterion, and nonisomorphism as absence
of a linear equivalence intertwining the Lie actions. No image equality,
stability, semisimplicity or analytic factorization is assumed. -/
noncomputable section
attribute [local instance] LieRing.ofAssociativeRing
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Lie Schur–Weyl duality, including the scalar unital image in degree zero
and the zero endomorphism algebra when dim(V)=0<n. All multiplicity spaces
are the canonical Hom_{S_n}(S^p,V^{⊗n}) of the upstream evaluation interface. -/
def lieSchurWeylType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    ∃ Φ : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
        Module.End ℂ (TensorPower V n),
    ∃ τ : ∀ p : Partition n,
        Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (TensorMultiplicity V p),
      (∀ T, Φ (UniversalEnvelopingAlgebra.ι ℂ T) = derivedTensorOperator V n T) ∧
      Φ.range = tensorB V n ∧
      Subalgebra.centralizer ℂ (Φ.range : Set (Module.End ℂ (TensorPower V n))) =
        tensorA V n ∧
      (∀ (p : Partition n) T (f : TensorMultiplicity V p) (v : SpechtModule p),
        (τ p T f).val v = derivedTensorOperator V n T (f.val v)) ∧
      (∀ p : Partition n, Nontrivial (TensorMultiplicity V p) →
        ∀ W : Submodule ℂ (TensorMultiplicity V p),
          (∀ T f, f ∈ W → τ p T f ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      (∀ p q : Partition n, p ≠ q →
        ∀ k : TensorMultiplicity V p →ₗ[ℂ] TensorMultiplicity V q,
          (∀ T f, k (τ p T f) = τ q T (k f)) → k = 0) ∧
      (∀ p q : Partition n, Nontrivial (TensorMultiplicity V p) →
        Nontrivial (TensorMultiplicity V q) → p ≠ q →
        ¬ ∃ e : TensorMultiplicity V p ≃ₗ[ℂ] TensorMultiplicity V q,
          ∀ T f, e (τ p T f) = τ q T (e f)) ∧
      (n = 0 → Φ.range = ⊥) ∧
      (0 < n → Module.finrank ℂ V = 0 →
        Φ.range = ⊥ ∧ (0 : Module.End ℂ (TensorPower V n)) = 1)

end Specs.AdvancedFiniteGroupRepresentations
