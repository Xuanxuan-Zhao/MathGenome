import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal

/-! KD-14: a split quotient of arbitrary commutative algebras. The conormal
module and both arrows are exactly those of KD-11. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w
noncomputable section
open TensorProduct

/-- Both splittings, left injectivity and right exactness, together with the
specified derivation and its universal/scalar-extension factorization. -/
def splitQuotient : Prop :=
  ∀ (A : Type u) (P : Type v) (B : Type w)
    [CommRing A] [CommRing P] [CommRing B]
    [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
    (h : Function.Surjective (algebraMap P B))
    (s : B →ₐ[A] P) (hs : Function.RightInverse s (algebraMap P B)),
    ∃ D : Derivation A P (Conormal A P B h),
      (∀ p : P, D p = Algebra.Extension.Cotangent.mk
        ⟨p - s (algebraMap P B p), by
          change algebraMap P B (p - s (algebraMap P B p)) = 0
          rw [map_sub, hs, sub_self]⟩) ∧
      ∃ r : B ⊗[P] KaehlerDifferential A P →ₗ[B] Conormal A P B h,
        r = D.liftKaehlerDifferential.liftBaseChange B ∧
        Function.LeftInverse r (conormalMapValue A P B h) ∧
        Function.Injective (conormalMapValue A P B h) ∧
        Function.Exact (conormalMapValue A P B h) (conormalProjectionValue A P B) ∧
        Function.Surjective (conormalProjectionValue A P B) ∧
        ∃ t : KaehlerDifferential A B →ₗ[B] B ⊗[P] KaehlerDifferential A P,
          Function.RightInverse t (conormalProjectionValue A P B)

end
end Specs.AdvCommAlg.Differentials
