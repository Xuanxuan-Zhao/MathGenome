import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExactSequence

/-! CM-12, first assertion (paper.tex:3649–3655, 3670–3673).
A tower records successive finite free surjections, with their kernels.
There is no minimality or finite projective dimension assumption. Zero free
modules and zero kernels are allowed, in particular after termination.
-/
universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay

/-- `K 0` is the original module and `K n` its nth syzygy.
Each step is the short exact sequence `0 → K (n+1) → F n → K n → 0`.
Finiteness of the kernels is automatic over a Noetherian ring; recording it
here lets the tower be defined over any commutative ring. -/
structure FiniteFreeSyzygies (R : Type u) [CommRing R] where
  K : ℕ → ModuleCat.{u} R
  F : ℕ → ModuleCat.{u} R
  finiteK : ∀ n, Module.Finite R (K n)
  finiteF : ∀ n, Module.Finite R (F n)
  freeF : ∀ n, Module.Free R (F n)
  i : ∀ n, K (n + 1) ⟶ F n
  p : ∀ n, F n ⟶ K n
  w : ∀ n, i n ≫ p n = 0
  shortExact : ∀ n, (ShortComplex.mk (i n) (p n) (w n)).ShortExact

attribute [instance] FiniteFreeSyzygies.finiteK FiniteFreeSyzygies.finiteF
  FiniteFreeSyzygies.freeF

/-- A finite chain of successive finite free surjections. This formulation
requires only the steps up to the specified syzygy, and no choice of later
free covers. The zeroth syzygy is the original module. -/
inductive FiniteFreeSyzygy (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ℕ → ModuleCat.{u} R → Prop where
  | zero : FiniteFreeSyzygy R M 0 M
  | succ {n : ℕ} {N F K : ModuleCat.{u} R}
      [Module.Finite R N] [Module.Finite R F] [Module.Free R F] [Module.Finite R K]
      (previous : FiniteFreeSyzygy R M n N)
      (i : K ⟶ F) (p : F ⟶ N) (w : i ≫ p = 0)
      (shortExact : (ShortComplex.mk i p w).ShortExact) :
      FiniteFreeSyzygy R M (n + 1) K

namespace Specs

/-- A terminated chain may be continued by zero free modules and zero kernels. -/
def finiteFreeSyzygy_zero_tailType : Prop :=
  ∀ {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    [Module.Finite R N] [Subsingleton N] {n : ℕ},
    FiniteFreeSyzygy R M n N → ∀ k : ℕ, FiniteFreeSyzygy R M (n + k) N

def finiteFreeSyzygy_depth_lower_boundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (d e n : ℕ), LocalCohenMacaulayValue R R →
    ringKrullDim R = (d : WithBot ℕ∞) →
    Depth.Specs.depthValue R M = (e : ℕ∞) → FiniteFreeSyzygy R M n N →
    ((min d (e + n) : ℕ) : ℕ∞) ≤ Depth.Specs.depthValue R N

/-- The source conclusion for an arbitrary finite chain of covers, including
chains that end with zero modules. No further covers are required. -/
def finiteFreeSyzygy_boundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] [Nontrivial M]
    (d e : ℕ), LocalCohenMacaulayValue R R →
    ringKrullDim R = (d : WithBot ℕ∞) → Depth.Specs.depthValue R M = (e : ℕ∞) →
    FiniteFreeSyzygy R M (d - e) N →
    e ≤ d ∧ e + (d - e) = d ∧ MaximalCohenMacaulayValue R N

def syzygy_depth_lower_boundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (T : FiniteFreeSyzygies R) (d e : ℕ),
    LocalCohenMacaulayValue R R → ringKrullDim R = (d : WithBot ℕ∞) →
    Depth.Specs.depthValue R (T.K 0) = (e : ℕ∞) →
    ∀ n : ℕ, ((min d (e + n) : ℕ) : ℕ∞) ≤ Depth.Specs.depthValue R (T.K n)

def syzygy_maximalCohenMacaulayType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (T : FiniteFreeSyzygies R) (d e n : ℕ),
    LocalCohenMacaulayValue R R → ringKrullDim R = (d : WithBot ℕ∞) →
    Depth.Specs.depthValue R (T.K 0) = (e : ℕ∞) → d ≤ e + n →
    MaximalCohenMacaulayValue R (T.K n)

/-- The untruncated numerical assertion accompanies the `d-e` conclusion.
At `e=d`, the syzygy is `K 0`. The MCM predicate includes zero by CM-01. -/
def syzygy_boundType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (T : FiniteFreeSyzygies R) [Nontrivial (T.K 0)] (d e : ℕ),
    LocalCohenMacaulayValue R R → ringKrullDim R = (d : WithBot ℕ∞) →
    Depth.Specs.depthValue R (T.K 0) = (e : ℕ∞) →
    e ≤ d ∧ e + (d - e) = d ∧ MaximalCohenMacaulayValue R (T.K (d - e))

end Specs
end AdvCommAlg.CohenMacaulay
