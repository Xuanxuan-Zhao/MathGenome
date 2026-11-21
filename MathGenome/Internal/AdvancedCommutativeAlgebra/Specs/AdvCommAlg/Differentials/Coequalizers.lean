import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Naturality
import Mathlib.LinearAlgebra.Isomorphisms

/-! KD-19, second assertion. The coefficient actions are the displayed compatible
algebra structures. Both arrows use the *same* P-action on C. -/
namespace Specs.AdvCommAlg.Differentials.Coequalizers

universe a p q c d
noncomputable section
open scoped TensorProduct

variable {A : Type a} {P : Type p} {Q : Type q} {C : Type c}
variable [CommRing A] [CommRing P] [CommRing Q] [CommRing C]
variable [Algebra A P] [Algebra A Q] [Algebra A C]

/-- The usual algebra coequalizer universal property, with test algebras in
universe d. The theorem tests it in the universes of Q and C, so that no
universe equality or size hypothesis on the rings is needed. -/
def CoequalizerUniversal (u v : P →ₐ[A] Q) (π : Q →ₐ[A] C) : Prop :=
  π.comp u = π.comp v ∧
  ∀ (D : Type d) [CommRing D] [Algebra A D] (f : Q →ₐ[A] D),
    f.comp u = f.comp v → ∃! g : C →ₐ[A] D, g.comp π = f

def differenceIdeal (u v : P →ₐ[A] Q) : Ideal Q :=
  Ideal.span (Set.range (fun x : P => u x - v x))

variable [Algebra Q C] [IsScalarTower A Q C]
variable [Algebra P C] [IsScalarTower A P C]

abbrev extendedDifferentials := C ⊗[Q] KaehlerDifferential A Q

/-- d of Q with its coefficients extended to C. -/
def extendedDerivation : Derivation A Q (extendedDifferentials (A := A) (Q := Q) (C := C)) :=
  (TensorProduct.mk Q C (KaehlerDifferential A Q) 1).compDer
    (KaehlerDifferential.D A Q)

/-- Restrict the derivation along either arrow, using the common P-action. -/
def arrowDerivation (f : P →ₐ[A] Q)
    (hf : ∀ x, algebraMap Q C (f x) = algebraMap P C x) :
    Derivation A P (extendedDifferentials (A := A) (Q := Q) (C := C)) :=
  Derivation.mk'
    { toFun := fun x => extendedDerivation (A := A) (Q := Q) (C := C) (f x)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    (by
      intro x y
      change extendedDerivation (A := A) (Q := Q) (C := C) (f (x * y)) =
        x • extendedDerivation (A := A) (Q := Q) (C := C) (f y) +
        y • extendedDerivation (A := A) (Q := Q) (C := C) (f x)
      rw [map_mul, Derivation.leibniz]
      rw [← IsScalarTower.algebraMap_smul C (f x),
        ← IsScalarTower.algebraMap_smul C (f y), hf x, hf y,
        IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul])

/-- The canonical C-linear arrow C ⊗_P Ω(P/A) → C ⊗_Q Ω(Q/A). -/
def arrowMap (f : P →ₐ[A] Q)
    (hf : ∀ x, algebraMap Q C (f x) = algebraMap P C x) :
    (C ⊗[P] KaehlerDifferential A P) →ₗ[C]
      extendedDifferentials (A := A) (Q := Q) (C := C) :=
  (TensorProduct.isBaseChange P (KaehlerDifferential A P) C).lift
    (arrowDerivation f hf).liftKaehlerDifferential

/-- The final canonical map, c ⊗ dq ↦ c d(π(q)). -/
abbrev finalMap : extendedDifferentials (A := A) (Q := Q) (C := C) →ₗ[C]
    KaehlerDifferential A C := KaehlerDifferential.mapBaseChange A Q C

/-- A full presentation of Ω(C/A), including both induced maps and the formula
for the quotient map on the differentials of Q. No finite generation or
nontriviality assumptions are made. -/
def coequalizerCokernel : Prop :=
  ∀ (A : Type a) (P : Type p) (Q : Type q) (C : Type c)
  [CommRing A] [CommRing P] [CommRing Q] [CommRing C]
  [Algebra A P] [Algebra A Q] [Algebra A C]
  [Algebra Q C] [IsScalarTower A Q C]
  [Algebra P C] [IsScalarTower A P C]
  (u v : P →ₐ[A] Q)
  (hu : ∀ x, algebraMap Q C (u x) = algebraMap P C x)
  (hv : ∀ x, algebraMap Q C (v x) = algebraMap P C x),
  CoequalizerUniversal.{a,p,q,c,q} u v (IsScalarTower.toAlgHom A Q C) →
  CoequalizerUniversal.{a,p,q,c,c} u v (IsScalarTower.toAlgHom A Q C) →
  let α := arrowMap u hu
  let β := arrowMap v hv
  (∀ (r : C) (x : P), α (r ⊗ₜ[P] KaehlerDifferential.D A P x) =
    r • (1 ⊗ₜ[Q] KaehlerDifferential.D A Q (u x))) ∧
  (∀ (r : C) (x : P), β (r ⊗ₜ[P] KaehlerDifferential.D A P x) =
    r • (1 ⊗ₜ[Q] KaehlerDifferential.D A Q (v x))) ∧
  ∃ e : (extendedDifferentials (A := A) (Q := Q) (C := C) ⧸
      LinearMap.range (α - β)) ≃ₗ[C] KaehlerDifferential A C,
    (∀ z, e ((LinearMap.range (α - β)).mkQ z) = finalMap z) ∧
    (∀ (r : C) (x : Q),
      e ((LinearMap.range (α - β)).mkQ (r ⊗ₜ[Q] KaehlerDifferential.D A Q x)) =
        r • KaehlerDifferential.D A C (algebraMap Q C x))

end
end Specs.AdvCommAlg.Differentials.Coequalizers
