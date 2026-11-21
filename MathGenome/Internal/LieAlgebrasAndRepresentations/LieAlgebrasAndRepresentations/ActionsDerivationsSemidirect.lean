import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Quotients
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Commutator

/-!
Actions, derivations and semidirect products (LA-A03, source lines 259–301).
All constructions use an arbitrary field, with no finite dimension assumption.
For the semidirect product, transport preserves the original addition and scalar
multiplication on G × N. The converse in the abelian case is proved by testing
cyclic Jacobi on (x,0), (y,0), (0,a).
-/

universe u v w

namespace LieAlgebrasAndRepresentations

open Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k]
variable {G : Type v} [LieRing G] [LieAlgebra k G]
variable {N : Type w} [LieRing N] [LieAlgebra k N]
variable {M : Type w} [AddCommGroup M] [Module k M]

theorem representation_iff (ρ : G →ₗ[k] Module.End k M) :
    (∃ f : G →ₗ⁅k⁆ Module.End k M, f.toLinearMap = ρ) ↔ IsRepresentation ρ :=
  homomorphism_iff ρ

theorem representation_action (ρ : G →ₗ⁅k⁆ Module.End k M) (x y : G) (a : M) :
    ρ ⁅x, y⁆ a = ρ x (ρ y a) - ρ y (ρ x a) := by
  rw [ρ.map_lie]
  rfl

def derivations_subalgebra (k : Type u) [Field k]
    (N : Type w) [LieRing N] [LieAlgebra k N] : LieSubalgebra k (Module.End k N) :=
  (LieDerivation.toLinearMapLieHom k N).range

theorem derivation_membership (d : Module.End k N) :
    d ∈ derivations_subalgebra k N ↔
      ∀ a b, d ⁅a, b⁆ = ⁅d a, b⁆ + ⁅a, d b⁆ := by
  change (∃ D : LieDerivation k N N, D.toLinearMap = d) ↔ _
  constructor
  · rintro ⟨D, rfl⟩ a b
    exact (D.apply_lie_eq_add a b).trans (add_comm _ _)
  · intro h
    refine ⟨⟨d, ?_⟩, rfl⟩
    intro a b
    rw [h, ← lie_skew (d a) b]
    abel

theorem derivation_commutator (d e : LieDerivation k N N) (a : N) :
    ⁅d, e⁆ a = d (e a) - e (d a) :=
  LieDerivation.commutator_apply a

def adjoint (k : Type u) [Field k]
    (G : Type v) [LieRing G] [LieAlgebra k G] : G →ₗ⁅k⁆ LieDerivation k G G :=
  LieDerivation.ad k G

theorem adjoint_apply (x y : G) : adjoint k G x y = ⁅x, y⁆ := by
  simp [adjoint]

theorem adjoint_kernel (k : Type u) [Field k]
    (G : Type v) [LieRing G] [LieAlgebra k G] :
    (adjoint k G).ker = LieAlgebra.center k G :=
  LieDerivation.ad_ker_eq_center k G

theorem adjoint_endomorphism_kernel (k : Type u) [Field k]
    (G : Type v) [LieRing G] [LieAlgebra k G] :
    ((LieDerivation.toLinearMapLieHom k G).comp (adjoint k G)).ker =
      LieAlgebra.center k G := by
  have hc : (LieDerivation.toLinearMapLieHom k G).comp (adjoint k G) =
      LieAlgebra.ad k G := by
    ext x y
    change adjoint k G x y = ⁅x, y⁆
    exact adjoint_apply x y
  rw [hc, LieAlgebra.ad_ker_eq_self_module_ker, LieAlgebra.self_module_ker_eq_center]

theorem adjoint_representation :
    IsRepresentation ((LieDerivation.toLinearMapLieHom k G).comp
      (adjoint k G)).toLinearMap :=
  (representation_iff _).mp ⟨_, rfl⟩

def semidirect_lie_ring (θ : G →ₗ⁅k⁆ LieDerivation k N N) : LieRing (G × N) :=
  semidirect_lie_ring_value θ

def semidirect_lie_algebra (θ : G →ₗ⁅k⁆ LieDerivation k N N) :
    letI := semidirect_lie_ring θ
    LieAlgebra k (G × N) :=
  semidirect_lie_algebra_value θ

theorem semidirect_bracket (θ : G →ₗ⁅k⁆ LieDerivation k N N)
    (x y : G) (a b : N) :
    letI := semidirect_lie_ring θ
    ⁅(x, a), (y, b)⁆ = (⁅x, y⁆, θ x b - θ y a + ⁅a, b⁆) := by
  change (⁅x, y⁆, ⁅a, b⁆ + θ x b - θ y a) = _
  congr 1
  abel

theorem abelian_jacobi_iff_representation (ρ : G →ₗ[k] Module.End k M) :
    (∀ p q r : G × M,
      abelianBracket ρ p (abelianBracket ρ q r) +
        abelianBracket ρ q (abelianBracket ρ r p) +
        abelianBracket ρ r (abelianBracket ρ p q) = 0) ↔ IsRepresentation ρ := by
  constructor
  · intro h x y
    ext a
    have hh := congrArg Prod.snd (h (x, 0) (y, 0) (0, a))
    simp only [abelianBracket, Prod.snd_add, Prod.snd_zero,
      lie_zero, zero_lie, map_zero, sub_zero, zero_sub] at hh
    change ρ ⁅x, y⁆ a = ρ x (ρ y a) - ρ y (ρ x a)
    apply sub_eq_zero.mp
    calc
      ρ ⁅x, y⁆ a - (ρ x (ρ y a) - ρ y (ρ x a)) =
          -(ρ x (ρ y a) + ρ y (-ρ x a) - ρ ⁅x, y⁆ a) := by
            rw [map_neg]
            abel
      _ = 0 := by simpa only [sub_eq_add_neg, neg_zero] using congrArg Neg.neg hh
  · intro h p q r
    change ∀ x y, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x at h
    apply Prod.ext
    · exact lie_jacobi p.1 q.1 r.1
    · change
        (ρ p.1 (ρ q.1 r.2 - ρ r.1 q.2) - ρ ⁅q.1, r.1⁆ p.2) +
          (ρ q.1 (ρ r.1 p.2 - ρ p.1 r.2) - ρ ⁅r.1, p.1⁆ q.2) +
          (ρ r.1 (ρ p.1 q.2 - ρ q.1 p.2) - ρ ⁅p.1, q.1⁆ r.2) = 0
      simp only [map_sub, h, LinearMap.sub_apply, Module.End.mul_apply]
      abel

end LieAlgebrasAndRepresentations
