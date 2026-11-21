import MathGenome.Internal.Specs.D05.M15.Contraction

/-!
K05.15.contraction, equivariance paragraph (paper.tex:3063–3064).
Use the existing mixed tensor space, contraction, and slotwise action.
Here `p,q` in a contraction count the remaining slots; thus `p=q=0`
is allowed. Linear equivalences represent GL(V), without a finite-dimension
assumption. Composition `h.trans g` means first h, then g.
-/
namespace Specs.D05.M15.Contraction.Equivariance

open Specs.D05.M15.Contraction
open scoped BigOperators

/-- The action uses g on vectors and precomposition by g⁻¹ on covectors. -/
def action_on_elementary : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) {p q : ℕ} (f : Fin p → Module.Dual K V) (v : Fin q → V),
    mixedAction g p q (elementary f v) =
      elementary (fun i => (f i).comp g.symm.toLinearMap) (fun j => g (v j))

def action_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (p q : ℕ),
    mixedAction (LinearEquiv.refl K V) p q = LinearMap.id

def action_composition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g h : V ≃ₗ[K] V) (p q : ℕ),
    mixedAction (h.trans g) p q = (mixedAction g p q).comp (mixedAction h p q)

/-- These are actual linear automorphisms, with the stated inverse. -/
def action_automorphism : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) (p q : ℕ),
    ∃ e : Mixed K V p q ≃ₗ[K] Mixed K V p q,
      e.toLinearMap = mixedAction g p q ∧
        e.symm.toLinearMap = mixedAction g.symm p q

/-- Invariance of the algebraic evaluation pairing; no conjugation is used. -/
def evaluation_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) (f : Module.Dual K V) (v : V),
    (f.comp g.symm.toLinearMap) (g v) = f v

/-- Equality of linear maps on the entire mixed tensor space. -/
def contraction_equivariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) {p q : ℕ} (r : Fin (p+1)) (s : Fin (q+1)),
    (contract r s).comp (mixedAction g (p+1) (q+1)) =
      (mixedAction g p q).comp (contract r s)

/-- The scalar degree is fixed, under the canonical nullary identification. -/
def scalar_action : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) (t : Mixed K V 0 0),
    zeroEquiv (mixedAction g 0 0 t) = zeroEquiv t

/-- In any finite dual product basis, contracting transformed coordinates
is exactly transforming the contracted tensor. This is a consequence of
invariant evaluation and the established diagonal-sum coordinate formula. -/
def contracted_coordinate_transformation : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) (g : V ≃ₗ[K] V) {p q : ℕ}
    (r : Fin (p+1)) (s : Fin (q+1)) (t : Mixed K V (p+1) (q+1))
    (i : Fin p → I) (j : Fin q → I),
    (∑ k : I, (mixedBasis b (p+1) (q+1)).repr
      (mixedAction g (p+1) (q+1) t) (r.insertNth k i, s.insertNth k j)) =
      (mixedBasis b p q).repr (mixedAction g p q (contract r s t)) (i,j)

end Specs.D05.M15.Contraction.Equivariance
