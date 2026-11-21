import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.BilinearRules
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

noncomputable section
open Set
open scoped BigOperators Matrix.Norms.Frobenius
namespace D04

/-- The standard ordered cross product on the shared Euclidean space. -/
def cross : Specs.D04.C02.BilinearRules.crossType :=
  Specs.D04.C02.BilinearRules.crossValue

section Generic
variable {X Y Z W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem linear_hasTotalDerivative [FiniteDimensional ℝ X]
    (U : Set X) (A : X →ₗ[ℝ] Y) (a : X) (hU : IsOpen U) (ha : a ∈ U) :
    HasTotalDerivative U A A.toContinuousLinearMap a ∧
      totalDerivative A a = A.toContinuousLinearMap := by
  have hd := (hasTotalDerivative_iff_hasFDerivAt U A _ a hU ha).mpr
    (A.toContinuousLinearMap.hasFDerivAt)
  exact ⟨hd, totalDerivative_eq U A _ a hd⟩

theorem sum_hasTotalDerivative {ι : Type} (s : Finset ι) (U : Set X)
    (f : ι → X → Y) (A : ι → X →L[ℝ] Y) (a : X) (hU : IsOpen U) (ha : a ∈ U)
    (hf : ∀ i ∈ s, HasTotalDerivative U (f i) (A i) a) :
    HasTotalDerivative U (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, A i) a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U _ _ a hU ha).mpr
  exact HasFDerivAt.fun_sum fun i hi =>
    (hasTotalDerivative_iff_hasFDerivAt U (f i) (A i) a hU ha).mp (hf i hi)

theorem sum_totalDerivative {ι : Type} (s : Finset ι) (U : Set X)
    (f : ι → X → Y) (a : X) (hU : IsOpen U) (ha : a ∈ U)
    (hf : ∀ i ∈ s, TotalDifferentiableAt U (f i) a) :
    TotalDifferentiableAt U (fun x => ∑ i ∈ s, f i x) a ∧
      totalDerivative (fun x => ∑ i ∈ s, f i x) a = ∑ i ∈ s, totalDerivative (f i) a := by
  have hd : HasTotalDerivative U (fun x => ∑ i ∈ s, f i x)
      (∑ i ∈ s, totalDerivative (f i) a) a := by
    apply sum_hasTotalDerivative s U f _ a hU ha
    intro i hi
    obtain ⟨A, hA⟩ := hf i hi
    rw [totalDerivative_eq U (f i) A a hA]
    exact hA
  exact ⟨⟨_, hd⟩, totalDerivative_eq U _ _ a hd⟩

theorem const_smul_hasTotalDerivative (U : Set X) (f : X → Y)
    (A : X →L[ℝ] Y) (a : X) (c : ℝ) (hf : HasTotalDerivative U f A a) :
    HasTotalDerivative U (fun x => c • f x) (c • A) a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U _ _ a hf.1 hf.2.1).mpr
  exact ((hasTotalDerivative_iff_hasFDerivAt U f A a hf.1 hf.2.1).mp hf).const_smul c

theorem const_smul_totalDerivative (U : Set X) (f : X → Y) (a : X) (c : ℝ)
    (hf : TotalDifferentiableAt U f a) :
    TotalDifferentiableAt U (fun x => c • f x) a ∧
      totalDerivative (fun x => c • f x) a = c • totalDerivative f a := by
  obtain ⟨A, hA⟩ := hf
  have hd := const_smul_hasTotalDerivative U f A a c hA
  exact ⟨⟨_, hd⟩, by rw [totalDerivative_eq U _ _ a hd, totalDerivative_eq U f A a hA]⟩

/-- Continuity of B is derived from finite dimension, never assumed. -/
theorem bilinear_hasTotalDerivative [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
    (B : Y →ₗ[ℝ] Z →ₗ[ℝ] W) (U : Set X) (u : X → Y) (v : X → Z)
    (A : X →L[ℝ] Y) (C : X →L[ℝ] Z) (a : X)
    (hu : HasTotalDerivative U u A a) (hv : HasTotalDerivative U v C a) :
    ∃ L : X →L[ℝ] W, HasTotalDerivative U (fun x => B (u x) (v x)) L a ∧
      ∀ h, L h = B (A h) (v a) + B (u a) (C h) := by
  have hu' := (hasTotalDerivative_iff_hasFDerivAt U u A a hu.1 hu.2.1).mp hu
  have hv' := (hasTotalDerivative_iff_hasFDerivAt U v C a hv.1 hv.2.1).mp hv
  have hd := B.toContinuousBilinearMap.hasFDerivAt_of_bilinear hu' hv'
  refine ⟨_, (hasTotalDerivative_iff_hasFDerivAt U _ _ a hu.1 hu.2.1).mpr hd, ?_⟩
  intro h
  simp [add_comm]

theorem bilinear_totalDerivative [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
    (B : Y →ₗ[ℝ] Z →ₗ[ℝ] W) (U : Set X) (u : X → Y) (v : X → Z) (a : X)
    (hu : TotalDifferentiableAt U u a) (hv : TotalDifferentiableAt U v a) :
    TotalDifferentiableAt U (fun x => B (u x) (v x)) a ∧
      ∀ h, totalDerivative (fun x => B (u x) (v x)) a h =
        B (totalDerivative u a h) (v a) + B (u a) (totalDerivative v a h) := by
  obtain ⟨A, hA⟩ := hu
  obtain ⟨C, hC⟩ := hv
  obtain ⟨L, hL, he⟩ := bilinear_hasTotalDerivative B U u v A C a hA hC
  refine ⟨⟨L, hL⟩, ?_⟩
  rw [totalDerivative_eq U _ L a hL, totalDerivative_eq U u A a hA,
    totalDerivative_eq U v C a hC]
  exact he

theorem scalar_mul_totalDerivative (U : Set X) (u v : X → ℝ) (a : X)
    (hu : TotalDifferentiableAt U u a) (hv : TotalDifferentiableAt U v a) :
    TotalDifferentiableAt U (fun x => u x * v x) a ∧
      ∀ h, totalDerivative (fun x => u x * v x) a h =
        totalDerivative u a h * v a + u a * totalDerivative v a h :=
  bilinear_totalDerivative (LinearMap.mul ℝ ℝ) U u v a hu hv

theorem smul_totalDerivative [FiniteDimensional ℝ Y]
    (U : Set X) (u : X → ℝ) (v : X → Y) (a : X)
    (hu : TotalDifferentiableAt U u a) (hv : TotalDifferentiableAt U v a) :
    TotalDifferentiableAt U (fun x => u x • v x) a ∧
      ∀ h, totalDerivative (fun x => u x • v x) a h =
        totalDerivative u a h • v a + u a • totalDerivative v a h :=
  bilinear_totalDerivative (LinearMap.lsmul ℝ Y) U u v a hu hv

set_option maxHeartbeats 800000 in
theorem matrix_mul_totalDerivative {r s t : ℕ} (U : Set X)
    (u : X → Matrix (Fin r) (Fin s) ℝ) (v : X → Matrix (Fin s) (Fin t) ℝ) (a : X)
    (hu : TotalDifferentiableAt U u a) (hv : TotalDifferentiableAt U v a) :
    TotalDifferentiableAt U (fun x => u x * v x) a ∧
      ∀ h, totalDerivative (fun x => u x * v x) a h =
        totalDerivative u a h * v a + u a * totalDerivative v a h :=
  bilinear_totalDerivative (X := X)
    (Y := Matrix (Fin r) (Fin s) ℝ) (Z := Matrix (Fin s) (Fin t) ℝ)
    (W := Matrix (Fin r) (Fin t) ℝ)
    (_root_.mulLinearMap (l := Fin r) (m := Fin s) (n := Fin t) (A := ℝ) ℝ) U u v a hu hv

theorem inner_totalDerivative {n : ℕ} (U : Set X) (u v : X → E n) (a : X)
    (hu : TotalDifferentiableAt U u a) (hv : TotalDifferentiableAt U v a) :
    TotalDifferentiableAt U (fun x => inner ℝ (u x) (v x)) a ∧
      ∀ h, totalDerivative (fun x => inner ℝ (u x) (v x)) a h =
        inner ℝ (totalDerivative u a h) (v a) + inner ℝ (u a) (totalDerivative v a h) :=
  bilinear_totalDerivative (innerₗ (E n)) U u v a hu hv

private def crossBilinear : E 3 →ₗ[ℝ] E 3 →ₗ[ℝ] E 3 :=
  ((crossProduct.compl₁₂ (coordinates 3).toLinearMap (coordinates 3).toLinearMap).compr₂
    (coordinates 3).symm.toLinearMap)

theorem cross_totalDerivative (U : Set X) (u v : X → E 3) (a : X)
    (hu : TotalDifferentiableAt U u a) (hv : TotalDifferentiableAt U v a) :
    TotalDifferentiableAt U (fun x => cross (u x) (v x)) a ∧
      ∀ h, totalDerivative (fun x => cross (u x) (v x)) a h =
        cross (totalDerivative u a h) (v a) + cross (u a) (totalDerivative v a h) :=
  bilinear_totalDerivative crossBilinear U u v a hu hv

end Generic
end D04
