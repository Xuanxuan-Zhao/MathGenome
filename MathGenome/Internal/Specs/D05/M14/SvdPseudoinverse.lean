import MathGenome.Internal.Specs.D05.M14.Svd
import MathGenome.Internal.Specs.D05.M14.Pseudoinverse
import MathGenome.Internal.Specs.D05.M13.Adjoint

/-! K05.14.svd_pseudoinverse, paper.tex:2528–2545.
The formulas hold for every singular value decomposition, whose existence is
the upstream SVD theorem. The index set contains precisely the positive singular
values; it is empty at rank zero. `firstInner w f = inner F f w`.
-/

noncomputable section

namespace Specs.D05.M14.SvdPseudoinverse

universe u v w

/-- Adjoint expansion in the full singular bases, summed over the positive block. -/
def adjoint_formula : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (w : W),
    LinearMap.adjoint T w =
      ∑ i : Fin (Module.finrank F (LinearMap.range T)),
        ((T.singularValues i : F) *
          _root_.D05.firstInner w
            (d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i))) •
          d.domainBasis (Fin.castLE T.finrank_range_le i)

/-- Pseudoinverse expansion: only strictly positive singular values are inverted. -/
def pseudoinverse_formula : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (w : W),
    _root_.D05.pseudoinverse T w =
      ∑ i : Fin (Module.finrank F (LinearMap.range T)),
        ((T.singularValues i : F)⁻¹ *
          _root_.D05.firstInner w
            (d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i))) •
          d.domainBasis (Fin.castLE T.finrank_range_le i)

end Specs.D05.M14.SvdPseudoinverse
