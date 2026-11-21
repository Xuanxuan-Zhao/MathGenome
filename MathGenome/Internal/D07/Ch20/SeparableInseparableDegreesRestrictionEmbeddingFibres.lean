import MathGenome.Internal.Specs.D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres

/-!
Restriction fibres for an arbitrary finite field tower, without separability.
An embedding of M extends to the algebraic closure Ω, and any K-endomorphism
of an algebraic extension of K is bijective. Composition with its inverse
then identifies the actual restriction fibre with the embeddings fixing M.
Finally, a sigma decomposition counts these fibres.
-/

noncomputable section

universe u v w z

namespace D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres

open Specs.D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres

variable {K : Type u} {M : Type v} {L : Type w} {Ω : Type z}
  [Field K] [Field M] [Field L] [Field Ω]
  [Algebra K M] [Algebra M L] [Algebra K L]
  [Algebra L Ω] [Algebra M Ω] [Algebra K Ω]
  [IsScalarTower K M L] [IsScalarTower M L Ω]
  [IsScalarTower K L Ω] [IsScalarTower K M Ω]

/-- Composition with a closure automorphism transports precisely the given fibre. -/
def fibreEquivOfAutomorphism (τ : M →ₐ[K] Ω) (e : Ω ≃ₐ[K] Ω)
    (he : ∀ x : M, e (algebraMap M Ω x) = τ x) :
    {σ : L →ₐ[K] Ω // σ.domRestrict M = τ} ≃ (L →ₐ[M] Ω) where
  toFun σ :=
    { __ := e.symm.toAlgHom.toRingHom.comp σ.1.toRingHom
      commutes' := fun x => by
        change e.symm (σ.1 (algebraMap M L x)) = algebraMap M Ω x
        have h := congrArg (fun f : M →ₐ[K] Ω => f x) σ.2
        change σ.1 (algebraMap M L x) = τ x at h
        rw [h, ← he x, e.symm_apply_apply] }
  invFun ρ :=
    ⟨e.toAlgHom.comp (ρ.restrictScalars K), by
      ext x
      change e (ρ (algebraMap M L x)) = τ x
      rw [ρ.commutes, he]⟩
  left_inv σ := by
    apply Subtype.ext
    ext x
    exact e.apply_symm_apply (σ.1 x)
  right_inv ρ := by
    ext x
    exact e.symm_apply_apply (ρ x)

theorem automorphism_extension : AutomorphismExtension.{u, v, w, z} := by
  intro K M L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  let : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.trans M L Ω
  let : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K M Ω
  intro τ
  obtain ⟨f, hf⟩ :=
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := K) (L := M) (M := Ω) (E := Ω)) τ
  exact ⟨AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f),
    fun x => congrArg (fun g : M →ₐ[K] Ω => g x) hf⟩

theorem restriction_surjective : RestrictionSurjective.{u, v, w, z} := by
  intro K M L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact IsAlgClosed.surjective_domRestrict_of_isAlgebraic

theorem fibre_equivalence : FibreEquivalence.{u, v, w, z} := by
  intro K M L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ
  obtain ⟨e, he⟩ := automorphism_extension K M L Ω τ
  exact ⟨fibreEquivOfAutomorphism τ e he⟩

theorem fibre_card : FibreCard.{u, v, w, z} := by
  intro K M L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ
  obtain ⟨e⟩ := fibre_equivalence K M L Ω τ
  exact (Nat.card_congr e).trans (Field.finSepDegree_eq_of_isAlgClosed M L Ω).symm

theorem embedding_count_product : EmbeddingCountProduct.{u, v, w, z} := by
  intro K M L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  let e : (L →ₐ[K] Ω) ≃ ((M →ₐ[K] Ω) × (L →ₐ[M] Ω)) :=
    (Equiv.sigmaFiberEquiv (fun σ : L →ₐ[K] Ω => σ.domRestrict M)).symm.trans
      (Equiv.sigmaEquivProdOfEquiv
        (fun τ => Classical.choice (fibre_equivalence K M L Ω τ)))
  rw [Nat.card_congr e, Nat.card_prod,
    ← Field.finSepDegree_eq_of_isAlgClosed M L Ω, Nat.mul_comm]

theorem finSepDegree_tower : FinSepDegreeTower.{u, v, w} := by
  intro K M L _ _ _ _ _ _ _ _ _
  let Ω := AlgebraicClosure L
  let : FiniteDimensional K L := Module.Finite.trans M L
  rw [Field.finSepDegree_eq_of_isAlgClosed K L Ω,
    Field.finSepDegree_eq_of_isAlgClosed K M Ω]
  exact embedding_count_product K M L Ω

end D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres
