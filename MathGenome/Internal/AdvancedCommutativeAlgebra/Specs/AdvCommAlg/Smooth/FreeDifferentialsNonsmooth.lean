import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Hypersurfaces
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import Mathlib.Algebra.CharP.Defs

/-! SM-17, paper.tex:1480–1493. `AdjoinRoot (X^n)` is literally the
polynomial quotient k[X]/(X^n), with its quotient k-algebra structure. -/
namespace Specs.AdvCommAlg.Smooth.FreeDifferentialsNonsmooth
universe u
noncomputable section

abbrev Truncated (K : Type u) [CommRing K] (n : ℕ) :=
  AdjoinRoot (Polynomial.X ^ n : Polynomial K)

abbrev coordinate (K : Type u) [CommRing K] (n : ℕ) : Truncated K n :=
  AdjoinRoot.root (Polynomial.X ^ n : Polynomial K)

/-- The canonical reduction k[X]/(X^(p+1)) → k[X]/(X^p). -/
def reduction (K : Type u) [CommRing K] (p : ℕ) :
    Truncated K (p+1) →ₐ[K] Truncated K p :=
  AdjoinRoot.algHomOfDvd K _ _ (pow_dvd_pow _ (Nat.le_succ p))

def differentialBasis : Prop := ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p],
  0 < p → ∃ b : Module.Basis Unit (Truncated K p)
      (KaehlerDifferential K (Truncated K p)),
    b () = KaehlerDifferential.D K (Truncated K p) (coordinate K p)

def candidateImages : Prop := ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p],
  0 < p → ∀ z : Truncated K (p+1), reduction K p z = coordinate K p →
    ∃ c : K, z = coordinate K (p+1) +
      algebraMap K (Truncated K (p+1)) c * coordinate K (p+1) ^ p

def candidatePowers : Prop := ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p],
  0 < p → ∀ z : Truncated K (p+1), reduction K p z = coordinate K p →
    z ^ p = coordinate K (p+1) ^ p ∧ coordinate K (p+1) ^ p ≠ 0

/-- Surjectivity and square-zero kernel, together with failure to lift the identity. -/
def failureTest : Prop := ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p],
  0 < p → Function.Surjective (reduction K p) ∧
    (RingHom.ker (reduction K p)) ^ 2 = ⊥ ∧
    ¬ ∃ f : Truncated K p →ₐ[K] Truncated K (p+1),
      (reduction K p).comp f = AlgHom.id K (Truncated K p)

def nonsmooth : Prop := ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p],
  0 < p → ¬ FormalLifting.formallySmoothValue K (Truncated K p) ∧
    ¬ Algebra.Smooth K (Truncated K p)

end
end Specs.AdvCommAlg.Smooth.FreeDifferentialsNonsmooth
