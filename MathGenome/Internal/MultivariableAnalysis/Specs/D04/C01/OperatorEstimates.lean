import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! Independent propositions for `d04:01:operator-estimates`.
The topology of a family of algebraic maps is specified directly by convergence
of the shared operator norm of differences. The arbitrary topological source
includes all relative Euclidean domains. The Pi norm over pairs of indices is
the finite maximum of absolute real entries, with value zero on an empty set.
All dimensions and orders include zero. No continuity hypothesis on the maps
or any assumed boundedness certificate is introduced.
-/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C01.OperatorEstimates
open EuclideanInterfaces.Model

def linear_continuousType : Prop :=
  ∀ {n m : ℕ} (A : E n →ₗ[ℝ] E m),
    Continuous A

def linear_norm_finiteType : Prop :=
  ∀ {n m : ℕ} (A : E n →ₗ[ℝ] E m),
    BddAbove ((fun v => ‖A v‖) '' {v | ‖v‖ ≤ 1}) ∧ 0 ≤ linearOperatorNorm A

def linear_apply_boundType : Prop :=
  ∀ {n m : ℕ} (A : E n →ₗ[ℝ] E m) (v : E n),
    ‖A v‖ ≤ linearOperatorNorm A * ‖v‖

def linear_comp_boundType : Prop :=
  ∀ {n m p : ℕ} (A : E n →ₗ[ℝ] E m) (B : E m →ₗ[ℝ] E p),
    linearOperatorNorm (B.comp A) ≤ linearOperatorNorm B * linearOperatorNorm A

def multilinear_continuousType : Prop :=
  ∀ {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)),
    Continuous T

def multilinear_norm_finiteType : Prop :=
  ∀ {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)),
    BddAbove ((fun v => ‖T v‖) '' {v | ∀ i, ‖v i‖ ≤ 1}) ∧
      0 ≤ multilinearOperatorNorm T

def multilinear_apply_boundType : Prop :=
  ∀ {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) (v : Fin k → E n),
    ‖T v‖ ≤ multilinearOperatorNorm T * ∏ i, ‖v i‖

def linear_operator_tendstoType : Prop :=
  ∀ {ι : Type*} {n m : ℕ} (l : Filter ι)
    (f : ι → E n →ₗ[ℝ] E m) (A : E n →ₗ[ℝ] E m),
    Tendsto (fun x => linearOperatorNorm (f x - A)) l (𝓝 0) ↔
      ∀ i j, Tendsto (fun x => matrixOfLinearMap (f x) i j) l
        (𝓝 (matrixOfLinearMap A i j))

def multilinear_operator_tendstoType : Prop :=
  ∀ {ι : Type*} {n m k : ℕ} (l : Filter ι)
    (f : ι → MultilinearMap ℝ (fun _ : Fin k => E n) (E m))
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)),
    Tendsto (fun x => multilinearOperatorNorm (f x - T)) l (𝓝 0) ↔
      ∀ (j : Fin k → Fin n) (i : Fin m),
        Tendsto (fun x => f x (fun r => standardBasis n (j r)) i) l
          (𝓝 (T (fun r => standardBasis n (j r)) i))

def linear_operator_continuousType : Prop :=
  ∀ {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (f : X → E n →ₗ[ℝ] E m),
    (∀ a, Tendsto (fun x => linearOperatorNorm (f x - f a)) (𝓝 a) (𝓝 0)) ↔
      ∀ i j, Continuous (fun x => matrixOfLinearMap (f x) i j)

def multilinear_operator_continuousType : Prop :=
  ∀ {X : Type*} [TopologicalSpace X] {n m k : ℕ}
    (f : X → MultilinearMap ℝ (fun _ : Fin k => E n) (E m)),
    (∀ a, Tendsto (fun x => multilinearOperatorNorm (f x - f a)) (𝓝 a) (𝓝 0)) ↔
      ∀ (j : Fin k → Fin n) (i : Fin m),
        Continuous (fun x => f x (fun r => standardBasis n (j r)) i)

def matrix_entry_boundType : Prop :=
  ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n),
    |M i j| ≤ linearOperatorNorm (matrixLinearEquiv m n M)

def matrix_max_le_operatorType : Prop :=
  ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ),
    ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖ ≤
      linearOperatorNorm (matrixLinearEquiv m n M)

def matrix_operator_le_frobeniusType : Prop :=
  ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ),
    linearOperatorNorm (matrixLinearEquiv m n M) ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2)

def matrix_frobenius_le_maxType : Prop :=
  ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ),
    Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤
      Real.sqrt ((m : ℝ) * (n : ℝ)) * ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖

def matrix_operator_boundsType : Prop :=
  ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ),
    ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖ ≤
        linearOperatorNorm (matrixLinearEquiv m n M) ∧
      linearOperatorNorm (matrixLinearEquiv m n M) ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) ∧
      Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤
        Real.sqrt ((m : ℝ) * (n : ℝ)) * ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖

def linear_operator_zero_dimensionsType : Prop :=
  ∀ {n m : ℕ} (A : E n →ₗ[ℝ] E m)
    (h : n = 0 ∨ m = 0),
    linearOperatorNorm A = 0

def multilinear_operator_zero_codomainType : Prop :=
  ∀ {n k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E 0)),
    multilinearOperatorNorm T = 0

def multilinear_operator_zero_domainType : Prop :=
  ∀ {m k : ℕ} (hk : 0 < k)
    (T : MultilinearMap ℝ (fun _ : Fin k => E 0) (E m)),
    multilinearOperatorNorm T = 0

def multilinear_order_zero_equalityType : Prop :=
  ∀ {n m : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin 0 => E n) (E m)) (v : Fin 0 → E n),
    ‖T v‖ = multilinearOperatorNorm T * ∏ i, ‖v i‖

end Specs.D04.C01.OperatorEstimates
