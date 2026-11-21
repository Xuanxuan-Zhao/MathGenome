import MathGenome.Internal.Specs.D05.M14.SingularValues

/-! K05.14.svd, paper.tex:2441–2459. The two bases are full bases, including
when either dimension is zero. Positive entries use the first rank(T) indices
of the already specified singular-value list. The record is data to be
constructed, not a hypothesis imposed on T in the existence theorem. -/

noncomputable section

namespace D05

variable {F V W : Type*} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- Full orthonormal singular bases, with the actual range dimension as rank. -/
structure SingularValueDecomposition (T : V →ₗ[F] W) where
  domainBasis : OrthonormalBasis (Fin (Module.finrank F V)) F V
  codomainBasis : OrthonormalBasis (Fin (Module.finrank F W)) F W
  positive_action : ∀ i : Fin (Module.finrank F (LinearMap.range T)),
    T (domainBasis (Fin.castLE T.finrank_range_le i)) =
      (T.singularValues i : F) •
        codomainBasis (Fin.castLE (Submodule.finrank_le _) i)
  zero_action : ∀ i : Fin (Module.finrank F V),
    Module.finrank F (LinearMap.range T) ≤ i.val → T (domainBasis i) = 0

end D05

namespace Specs.D05.M14.Svd
universe u v w

/-- Existence has no decomposition/eigenbasis premise and no positive dimension
or injectivity premise. -/
def exists_svd : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    Nonempty (_root_.D05.SingularValueDecomposition T)

/-- Fourier expansion in the paper's first-slot-linear convention. -/
def expansion : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (v : V),
    T v = ∑ i : Fin (Module.finrank F (LinearMap.range T)),
      ((T.singularValues i : F) *
        _root_.D05.firstInner v (d.domainBasis (Fin.castLE T.finrank_range_le i))) •
          d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)

/-- The actual matrix in these bases: all off-diagonal entries vanish and the
remaining entries are the ordered nonnegative real singular values. -/
def rectangular_diagonal : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T),
    ∀ (i : Fin (Module.finrank F W)) (j : Fin (Module.finrank F V)),
      LinearMap.toMatrix d.domainBasis.toBasis d.codomainBasis.toBasis T i j =
        if i.val = j.val then (T.singularValues j : F) else 0

/-- The diagonal coefficients are nonnegative; the positive block has size the
rank, and all later coefficients are zero. -/
def diagonal_signs : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (∀ i : Fin (Module.finrank F V), 0 ≤ T.singularValues i) ∧
    (∀ i : Fin (Module.finrank F (LinearMap.range T)), 0 < T.singularValues i) ∧
    (∀ i : Fin (Module.finrank F V),
      Module.finrank F (LinearMap.range T) ≤ i.val → T.singularValues i = 0)

/-- If the map is zero, its two full bases may be chosen independently. -/
def zero_map_bases : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (e : OrthonormalBasis (Fin (Module.finrank F V)) F V)
    (f : OrthonormalBasis (Fin (Module.finrank F W)) F W),
    ∃ d : _root_.D05.SingularValueDecomposition (0 : V →ₗ[F] W),
      d.domainBasis = e ∧ d.codomainBasis = f

end Specs.D05.M14.Svd
