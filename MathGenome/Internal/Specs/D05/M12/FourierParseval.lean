import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M12.Orthonormal
import MathGenome.Internal.Specs.D05.M12.NormLaws

/-!
Independent statements for K05.12.fourier_parseval, paper.tex:1989–2000.
The paper's coefficient is `D05.firstInner (F := F) v (e j) = inner F (e j) v`.
All sums are finite. Bessel and the residual identities require no spanning,
finite-dimensionality, completeness, or nonemptiness hypothesis.
The basis is the shared canonical algebraic `Module.Basis`.
-/

namespace Specs.D05.M12.FourierParseval

/-- Squaring the norm of an orthonormal finite linear combination leaves
exactly the diagonal terms. -/
def norm_sq_finite_sum : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : I → V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ (s : Finset I) (a : I → F),
      ‖∑ j ∈ s, a j • e j‖ ^ 2 = ∑ j ∈ s, ‖a j‖ ^ 2

/-- Coordinates in an orthonormal algebraic basis are the Fourier coefficients. -/
def fourier_coefficient : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (b : Module.Basis I F V), _root_.D05.orthonormalFamily (F := F) b →
    ∀ (v : V) (j : I), b.repr v j = _root_.D05.firstInner (F := F) v (b j)

/-- The finite orthonormal basis expansion in the source's linearity convention. -/
def fourier_expansion : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] (b : Module.Basis I F V),
    _root_.D05.orthonormalFamily (F := F) b → ∀ v : V,
      v = ∑ j, _root_.D05.firstInner (F := F) v (b j) • b j

def parseval : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] (b : Module.Basis I F V),
    _root_.D05.orthonormalFamily (F := F) b → ∀ v : V,
      ‖v‖ ^ 2 = ∑ j, ‖_root_.D05.firstInner (F := F) v (b j)‖ ^ 2

/-- The residual is orthogonal to each selected vector. -/
def residual_orthogonal : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : I → V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ (s : Finset I) (v : V) (k : I), k ∈ s →
      _root_.D05.firstInner (F := F)
        (v - ∑ j ∈ s, _root_.D05.firstInner (F := F) v (e j) • e j) (e k) = 0

/-- In particular the residual is orthogonal to the partial Fourier sum. -/
def residual_orthogonal_sum : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : I → V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ (s : Finset I) (v : V),
      let p := ∑ j ∈ s, _root_.D05.firstInner (F := F) v (e j) • e j
      _root_.D05.firstInner (F := F) (v - p) p = 0

/-- Pythagoras with its full nonnegative residual term. -/
def bessel_identity : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : I → V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ (s : Finset I) (v : V),
      let p := ∑ j ∈ s, _root_.D05.firstInner (F := F) v (e j) • e j
      ‖v‖ ^ 2 = (∑ j ∈ s, ‖_root_.D05.firstInner (F := F) v (e j)‖ ^ 2) + ‖v - p‖ ^ 2

def bessel : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : I → V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ (s : Finset I) (v : V),
      (∑ j ∈ s, ‖_root_.D05.firstInner (F := F) v (e j)‖ ^ 2) ≤ ‖v‖ ^ 2

/-- Taking `I = Fin m` gives the exact list statement, including `m = 0`. -/
def bessel_finite_family : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] (e : I → V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ v : V, (∑ j, ‖_root_.D05.firstInner (F := F) v (e j)‖ ^ 2) ≤ ‖v‖ ^ 2

end Specs.D05.M12.FourierParseval
