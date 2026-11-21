import MathGenome.Internal.Specs.D05.M13.AdjointLaws
import MathGenome.Internal.Specs.D05.M12.Orthonormal

/-! Independent statements for the paired-vector stage of K05.14.svd,
paper.tex:2441–2459. The supplied eigenbasis is arbitrary; ordering among the
positive values is immaterial. Fin r selects the first r vectors and hr embeds
these indices in Fin n. Every inverse below has a strictly positive real input.
There is no nonzero-dimension assumption. -/

noncomputable section
namespace Specs.D05.M14.Svd.PairedVectors
universe u v w
def image_inner : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ i j, _root_.D05.firstInner (F := F) (T (e i)) (T (e j)) =
      ((s j ^ 2 : ℝ) : F) * (if i = j then 1 else 0)


def zero_image : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ i, s i = 0 → T (e i) = 0


def paired_orthonormal : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ {r : ℕ} (hr : r ≤ n)
    (hp : ∀ i : Fin r, 0 < s (Fin.castLE hr i)),
    _root_.D05.orthonormalFamily (F := F)
      (fun i : Fin r => ((s (Fin.castLE hr i) : F)⁻¹) • T (e (Fin.castLE hr i)))


def image_independent : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ {r : ℕ} (hr : r ≤ n)
    (hp : ∀ i : Fin r, 0 < s (Fin.castLE hr i)),
    LinearIndependent F (fun i : Fin r => T (e (Fin.castLE hr i)))


def image_span : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ {r : ℕ} (hr : r ≤ n)
    (hp : ∀ i : Fin r, 0 < s (Fin.castLE hr i)),
    (∀ i : Fin n, r ≤ i.val → s i = 0) →
    Submodule.span F (Set.range (fun i : Fin r => T (e (Fin.castLE hr i)))) = LinearMap.range T


def image_basis : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ {r : ℕ} (hr : r ≤ n)
    (hp : ∀ i : Fin r, 0 < s (Fin.castLE hr i)),
    (∀ i : Fin n, r ≤ i.val → s i = 0) →
    ∃ b : Module.Basis (Fin r) F (LinearMap.range T),
      ∀ i, (b i : W) = T (e (Fin.castLE hr i))


def rank_eq : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ {r : ℕ} (hr : r ≤ n)
    (hp : ∀ i : Fin r, 0 < s (Fin.castLE hr i)),
    (∀ i : Fin n, r ≤ i.val → s i = 0) →
    r = Module.finrank F (LinearMap.range T)


def rank_bound : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    ∀ {r : ℕ} (hr : r ≤ n)
    (hp : ∀ i : Fin r, 0 < s (Fin.castLE hr i)),
    (∀ i : Fin n, r ≤ i.val → s i = 0) →
    r ≤ min (Module.finrank F V) (Module.finrank F W)


def zero_rank : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) {n : ℕ} (e : OrthonormalBasis (Fin n) F V)
    (s : Fin n → ℝ)
    (he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i),
    (∀ i, s i = 0) → T = 0


end Specs.D05.M14.Svd.PairedVectors
