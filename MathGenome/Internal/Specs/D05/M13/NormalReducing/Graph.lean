import MathGenome.Internal.Specs.D05.M13.NormalReducing.Subspace
import MathGenome.Internal.Specs.D05.M06.ExternalSum
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Independent statements for the graph argument in K05.13.normal_reducing,
paper.tex:2193–2207. The product has its L² norm and sum inner product,
not the maximum norm on the ordinary product. `WithLp.linearEquiv` only
transports the componentwise linear operations. The adjoint and normality
are the canonical upstream objects, with firstInner x y = inner F y x.
No hypothesis is imposed on S beyond linearity and ST = TS. -/

noncomputable section
namespace Specs.D05.M13.NormalReducing.Graph
universe u v

variable {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V]

/-- The finite external direct sum V ⊕ V with its direct-sum inner product. -/
abbrev SumSpace (V : Type v) := WithLp 2 (V × V)

/-- Comparison with the upstream external finitely supported sum. Its two
components are unchanged; only the product norm is replaced by the L² norm. -/
def externalSumComparison :
    (_root_.DirectSum (Fin 2) (fun _ => V)) ≃ₗ[F] SumSpace V :=
  ((Specs.D05.M06.ExternalSum.finiteProductMap F (Fin 2) (fun _ => V)).trans
    (LinearEquiv.finTwoArrow F V)).trans (WithLp.linearEquiv 2 F (V × V)).symm

/-- The comparison is the actual component identification of the external sum. -/
def external_sum_components : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (z : _root_.DirectSum (Fin 2) (fun _ => V)),
    WithLp.ofLp (externalSumComparison (F := F) z) = (z 0, z 1)

/-- The actual diagonal map (x,y) ↦ (Tx,Ty). -/
def diagonalMap (T : V →ₗ[F] V) : SumSpace V →ₗ[F] SumSpace V :=
  (WithLp.linearEquiv 2 F (V × V)).symm.toLinearMap.comp
    ((T.prodMap T).comp (WithLp.linearEquiv 2 F (V × V)).toLinearMap)

/-- The graph is the preimage of the canonical linear graph under the
identity-on-components comparison with the ordinary product. -/
def graphSubspace (S : V →ₗ[F] V) : Submodule F (SumSpace V) :=
  S.graph.comap (WithLp.linearEquiv 2 F (V × V)).toLinearMap

/-- The inner product is the sum in precisely the paper's slot convention. -/
def direct_sum_inner : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (x y : SumSpace V),
    _root_.D05.firstInner (F := F) x y =
      _root_.D05.firstInner (F := F) (WithLp.ofLp x).1 (WithLp.ofLp y).1 +
      _root_.D05.firstInner (F := F) (WithLp.ofLp x).2 (WithLp.ofLp y).2

def diagonal_apply : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (T : V →ₗ[F] V) (x y : V),
    diagonalMap T (WithLp.toLp 2 (x, y)) = WithLp.toLp 2 (T x, T y)

def mem_graph : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (S : V →ₗ[F] V) (z : SumSpace V),
    z ∈ graphSubspace S ↔ (WithLp.ofLp z).2 = S (WithLp.ofLp z).1

def diagonal_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    (diagonalMap T).adjoint = diagonalMap T.adjoint

def diagonal_normal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T → _root_.D05.normalOperator (diagonalMap T)

/-- Graph invariance only uses the original commutation identity. -/
def graph_invariant : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (T S : V →ₗ[F] V),
    S.comp T = T.comp S →
      Specs.D05.M06.Invariant.invariant_value F (SumSpace V)
        (graphSubspace S) (diagonalMap T)

/-- The reducing-subspace theorem applied to the actual graph. -/
def graph_adjoint_invariant : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T S : V →ₗ[F] V),
    _root_.D05.normalOperator T → S.comp T = T.comp S →
      Specs.D05.M06.Invariant.invariant_value F (SumSpace V)
        (graphSubspace S) ((diagonalMap T).adjoint)

/-- Finite-dimensional real/complex commutant assertion, including the zero space. -/
def commutes_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T S : V →ₗ[F] V),
    _root_.D05.normalOperator T → S.comp T = T.comp S →
      S.comp T.adjoint = T.adjoint.comp S

end Specs.D05.M13.NormalReducing.Graph
