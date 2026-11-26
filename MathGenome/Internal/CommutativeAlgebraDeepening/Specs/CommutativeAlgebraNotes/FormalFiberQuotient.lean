import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions

/-! The formal fibre as the generic fibre of the completed quotient. -/

universe u

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence.Specs

open IsLocalRing (maximalIdeal)

variable {A : Type u} [CommRing A] [IsLocalRing A] (q : Ideal A) [q.IsPrime]

/-- The ideal `m/q` determining the completion of the quotient. -/
abbrev quotientMaximalIdeal : Ideal (A ⧸ q) :=
  (maximalIdeal A).map (Ideal.Quotient.mk q)

/-- Reduction modulo `q` on the quotients defining the two completions. -/
def formalFiberQuotientCoordinate (n : ℕ) :
    (A ⧸ maximalIdeal A ^ n) →+* (A ⧸ q) ⧸ quotientMaximalIdeal q ^ n :=
  Ideal.quotientMap _ (Ideal.Quotient.mk q)
    (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]))

/-- The scalar identification obtained from the two fraction rings of `A/q`. -/
noncomputable abbrev residueFieldToFractionRing :
    q.ResidueField ≃ₐ[A ⧸ q] FractionRing (A ⧸ q) :=
  (FractionRing.algEquiv (A ⧸ q) q.ResidueField).symm

/-- The `κ(q)`-algebra structure through the fraction field in the right factor. -/
noncomputable abbrev formalFiberQuotientAlgebra :
    Algebra q.ResidueField
      (AdicCompletion (quotientMaximalIdeal q) (A ⧸ q) ⊗[A ⧸ q] FractionRing (A ⧸ q)) :=
  ((Algebra.TensorProduct.includeRight : FractionRing (A ⧸ q) →ₐ[A ⧸ q]
      AdicCompletion (quotientMaximalIdeal q) (A ⧸ q) ⊗[A ⧸ q] FractionRing (A ⧸ q)).toRingHom.comp
    (residueFieldToFractionRing q).toRingEquiv.toRingHom).toAlgebra

def formalFiberQuotientType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (q : Ideal A) [q.IsPrime],
    letI := formalFiberQuotientAlgebra q
    ∃ (f : AdicCompletion (maximalIdeal A) A →ₐ[A]
        AdicCompletion (quotientMaximalIdeal q) (A ⧸ q))
      (e : FormalFiberValue A q ≃ₐ[q.ResidueField]
        AdicCompletion (quotientMaximalIdeal q) (A ⧸ q) ⊗[A ⧸ q] FractionRing (A ⧸ q)),
      (∀ (x : AdicCompletion (maximalIdeal A) A) (n : ℕ),
        AdicCompletion.evalₐ (quotientMaximalIdeal q) n (f x) =
          formalFiberQuotientCoordinate q n (AdicCompletion.evalₐ (maximalIdeal A) n x)) ∧
      (∀ (k : q.ResidueField) (x : AdicCompletion (maximalIdeal A) A),
        e (k ⊗ₜ[A] x) = f x ⊗ₜ[A ⧸ q] residueFieldToFractionRing q k)

end CommutativeAlgebraNotes.Excellence.Specs
