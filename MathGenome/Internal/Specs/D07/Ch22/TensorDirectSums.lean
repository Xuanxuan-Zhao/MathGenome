import MathGenome.Internal.Specs.D07.Ch22.FreeDirectSums
import MathGenome.Internal.Specs.D07.Ch22.TensorFunctor
import MathGenome.Internal.Specs.D07.Ch09.MaximalExistence
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
Independent specification of K07.22.tensor_direct_sums, paper.tex:6796–6822.
`DirectSum` and `Finsupp` retain finite support even for infinite index types.
All equivalences are linear over the original commutative unital ring.
Only the intrinsic-rank assertions assume a nonzero ring. Neither the
distribution theorem nor the chosen finite-free presentations do so.
No assertion about arbitrary infinite products is made here.
-/

universe u v w t
namespace Specs.D07.Ch22.TensorDirectSums
open scoped TensorProduct BigOperators

/-- The canonical isomorphism, uniquely specified on elementary tensors;
the inverse includes a summand by tensoring its coordinate inclusion. -/
def Distribution : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (N : Type t) [AddCommGroup N] [Module R N],
    ∃! e : ((DirectSum E M) ⊗[R] N) ≃ₗ[R] DirectSum E (fun i => M i ⊗[R] N),
      (∀ m n i, e (m ⊗ₜ[R] n) i = m i ⊗ₜ[R] n) ∧
      (∀ i x n, e.symm (DirectSum.lof R E _ i (x ⊗ₜ[R] n)) =
        DirectSum.lof R E M i x ⊗ₜ[R] n)

/-- The tuple formula for Mathlib's canonical equivalence, with no finite-index premise. -/
def ForwardCoordinates : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (N : Type t) [AddCommGroup N] [Module R N]
    (m : DirectSum E M) (n : N) (i : E),
    TensorProduct.directSumLeft R R M N (m ⊗ₜ[R] n) i = m i ⊗ₜ[R] n

/-- The elementary tuple has support contained in that of its first input. -/
def FiniteSupport : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (N : Type t) [AddCommGroup N] [Module R N]
    (m : DirectSum E M) (n : N),
    (TensorProduct.directSumLeft R R M N (m ⊗ₜ[R] n)).support ⊆ m.support

/-- On arbitrary tensors in each summand, the inverse is the extension of
the maps inclusion tensor identity by the direct-sum universal property. -/
def InverseMap : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (N : Type t) [AddCommGroup N] [Module R N],
    (TensorProduct.directSumLeft R R M N).symm.toLinearMap =
      DirectSum.toModule R E ((DirectSum E M) ⊗[R] N)
        (fun i => TensorProduct.map (DirectSum.lof R E M i) (LinearMap.id : N →ₗ[R] N))

/-- Its value on an arbitrary tuple is a finite sum, including for infinite E. -/
def InverseFiniteSum : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (N : Type t) [AddCommGroup N] [Module R N]
    (z : DirectSum E (fun i => M i ⊗[R] N)),
    (TensorProduct.directSumLeft R R M N).symm z =
      ∑ i ∈ z.support,
        TensorProduct.map (DirectSum.lof R E M i) (LinearMap.id : N →ₗ[R] N) (z i)

/-- Both composites are identities on the whole modules. -/
def InverseIdentities : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v) (M : E → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (N : Type t) [AddCommGroup N] [Module R N],
    let e := TensorProduct.directSumLeft R R M N
    (∀ x, e.symm (e x) = x) ∧ (∀ z, e (e.symm z) = z)

/-- Arbitrary free-module specialization, with both generator formulas. -/
def FreeTensor : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] (E : Type v)
    (N : Type t) [AddCommGroup N] [Module R N],
    ∃ e : ((E →₀ R) ⊗[R] N) ≃ₗ[R] (E →₀ N),
      (∀ f n i, e (f ⊗ₜ[R] n) i = f i • n) ∧
      (∀ i n, e.symm (Finsupp.single i n) = Finsupp.single i (1 : R) ⊗ₜ[R] n)

/-- Chosen finite free models, including a=0, b=0, and the zero ring.
The product coordinates are indexed explicitly by `finProdFinEquiv`. -/
def FiniteFreeTensor : Prop :=
  ∀ (R : Type u) [CommRing R] (a b : ℕ),
    ∃ e : ((Fin a → R) ⊗[R] (Fin b → R)) ≃ₗ[R] (Fin (a * b) → R),
      ∀ f g (i : Fin a) (j : Fin b),
        e (f ⊗ₜ[R] g) (finProdFinEquiv (i, j)) = f i * g j

/-- The tensor products of two given bases form the product-indexed basis.
This assertion concerns a chosen basis and also applies over the zero ring. -/
def ProductBasis : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type t) [AddCommGroup N] [Module R N]
    (a b : ℕ) (bm : Module.Basis (Fin a) R M) (bn : Module.Basis (Fin b) R N),
    ∃ c : Module.Basis (Fin a × Fin b) R (M ⊗[R] N),
      ∀ i j, c (i, j) = bm i ⊗ₜ[R] bn j

/-- Any two finite free presentations have the same size over a nonzero ring. -/
def FiniteRankInvariant : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] (a b : ℕ),
    ((Fin a → R) ≃ₗ[R] (Fin b → R)) → a = b

/-- Finite-free ranks multiply, for arbitrary finite free modules. -/
def RankMultiplication : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (N : Type t) [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N],
    Module.finrank R (M ⊗[R] N) = Module.finrank R M * Module.finrank R N

/-- The size of any finite basis agrees with the intrinsic rank when R is nonzero. -/
def FiniteBasisRank : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R]
    (M : Type w) [AddCommGroup M] [Module R M]
    (a : ℕ) (b : Module.Basis (Fin a) R M), Module.finrank R M = a

/-- Every unital module over the zero ring is zero. -/
def ZeroRingModules : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R]
    (M : Type w) [AddCommGroup M] [Module R M] (x : M), x = 0

/-- All displayed finite sizes give isomorphic modules over the zero ring;
in particular the distinct sizes zero and one do not define intrinsic rank. -/
def ZeroRingSizes : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R] (a b : ℕ),
    Nonempty ((Fin a → R) ≃ₗ[R] (Fin b → R))

end Specs.D07.Ch22.TensorDirectSums
