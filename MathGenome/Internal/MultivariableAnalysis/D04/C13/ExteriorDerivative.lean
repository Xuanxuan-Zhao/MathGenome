import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C13.NormalizedFormsAndWedge
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04

abbrev exteriorDerivative := @Specs.D04.C13.ExteriorDerivative.Model.exteriorDerivative

/-- The coordinate expression uses the already fixed normalized wedge. -/
theorem exteriorDerivative_formula {n k : ℕ} (ω : FormField n k) (x : E n) :
    exteriorDerivative ω x = ∑ I : MultiIndex n k, ∑ j : Fin n,
      scalarPartialDerivative (fun y => coefficient (standardBasis n) (ω y) I) x j •
        castCovector (Nat.add_comm 1 k)
          (wedge (linearCovector ((standardBasis n).coord j)) (dx (standardBasis n) I)) := rfl

/-- A coordinate derivative of a C^(r+1) scalar function is C^r, on its
original open domain, even if its ambient representative is irregular elsewhere. -/
theorem crOn_scalarPartialDerivative {n : ℕ} (r : ℕ) (U : Set (E n))
    (f : E n → ℝ) (hU : IsOpen U) (hf : CrOn (r + 1) U f) (j : Fin n) :
    CrOn r U (fun x => scalarPartialDerivative f x j) := by
  change TotalDifferentiableOn U f ∧ CrOn r U (totalDerivative f) at hf
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  have hc := ((crOn_iff_contDiffOn r U _ hU).mp hf.2).clm_apply
    (contDiffOn_const (c := standardBasis n j))
  apply hc.congr
  intro x hx
  obtain ⟨A, hA⟩ := hf.1 x hx
  rw [totalDerivative_eq U f A x hA]
  exact scalarPartialDerivative_eq U f x A hA j

private theorem coefficient_exteriorDerivative {n k : ℕ} (ω : FormField n k)
    (x : E n) (J : MultiIndex n (k + 1)) :
    coefficient (standardBasis n) (exteriorDerivative ω x) J =
      ∑ I : MultiIndex n k, ∑ j : Fin n,
        scalarPartialDerivative (fun y => coefficient (standardBasis n) (ω y) I) x j *
          coefficient (standardBasis n)
            (Specs.D04.C13.ExteriorDerivative.Model.coordinateExteriorTerm j I) J := by
  simp only [exteriorDerivative, Specs.D04.C13.ExteriorDerivative.Model.exteriorDerivative,
    coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient,
    sum_apply, smul_apply, smul_eq_mul]
  rfl

private theorem exteriorDerivative_isCr_succ {n k : ℕ} (r : ℕ)
    (U : Set (E n)) (ω : FormField n k) (hω : IsCrForm (some (r + 1)) U ω) :
    IsCrForm (some r) U (exteriorDerivative ω) := by
  obtain ⟨hU, hcoeff⟩ := hω
  refine ⟨hU, ?_⟩
  intro J
  change CrOn r U (fun x => coefficient (standardBasis n) (exteriorDerivative ω x) J)
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  simp_rw [coefficient_exteriorDerivative]
  apply ContDiffOn.sum
  intro I _
  apply ContDiffOn.sum
  intro j _
  exact ((crOn_iff_contDiffOn r U _ hU).mp
    (crOn_scalarPartialDerivative r U _ hU (hcoeff I) j)).mul contDiffOn_const

theorem exteriorDerivative_isCr {n k : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (U : Set (E n)) (ω : FormField n k) (hω : IsCrForm (some r) U ω) :
    IsCrForm (some (r - 1)) U (exteriorDerivative ω) := by
  cases r with
  | zero => exact (Nat.not_succ_le_zero 0 hr).elim
  | succ r => exact exteriorDerivative_isCr_succ r U ω hω

theorem exteriorDerivative_continuous {n k : ℕ} (U : Set (E n))
    (ω : FormField n k) (hω : IsCrForm (some 1) U ω) :
    IsCrForm (some 0) U (exteriorDerivative ω) :=
  exteriorDerivative_isCr_succ 0 U ω hω

theorem exteriorDerivative_smooth {n k : ℕ} (U : Set (E n))
    (ω : FormField n k) (hω : IsCrForm none U ω) :
    IsCrForm none U (exteriorDerivative ω) := by
  refine ⟨hω.1, ?_⟩
  intro J r
  exact (exteriorDerivative_isCr_succ r U ω ⟨hω.1, fun I => hω.2 I (r + 1)⟩).2 J

theorem exteriorDerivative_top {n : ℕ} (ω : FormField n n) :
    exteriorDerivative ω = 0 := by
  funext x
  apply covector_eq_zero_above_dimension
  simpa only [E, Specs.D04.C01.EuclideanInterfaces.Model.E, finrank_euclideanSpace, Fintype.card_fin] using
    Nat.lt_succ_self n

theorem exteriorDerivative_above {n k : ℕ} (hk : n < k) (ω : FormField n k) :
    exteriorDerivative ω = 0 := by
  funext x
  apply covector_eq_zero_above_dimension
  simpa only [E, Specs.D04.C01.EuclideanInterfaces.Model.E, finrank_euclideanSpace, Fintype.card_fin] using
    hk.trans (Nat.lt_succ_self k)

/-- On scalar functions the coordinate construction evaluates to the genuine
linear differential, including the empty sum in dimension zero. -/
theorem exteriorDerivative_scalar {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (x : E n) (A : E n →L[ℝ] ℝ) (hA : HasTotalDerivative U f A x) :
    exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x =
      linearCovector A.toLinearMap := by
  let I₀ : MultiIndex n 0 := ⟨∅, Finset.card_empty⟩
  let : Unique (MultiIndex n 0) :=
    { default := I₀
      uniq := fun I => Subtype.ext (Finset.card_eq_zero.mp I.property) }
  have hz (I : MultiIndex n 0) : dx (standardBasis n) I = scalarCovector 1 := by
    ext v
    exact dx_degree_zero (standardBasis n) I v
  have hc (I : MultiIndex n 0) :
      (fun y => coefficient (standardBasis n) (scalarCovector (V := E n) (f y)) I) = f := rfl
  rw [exteriorDerivative_formula]
  simp_rw [hc, scalarPartialDerivative_eq U f x A hA, hz, wedge_scalar_right, one_smul]
  simp only [Fintype.sum_unique]
  ext v
  simp only [sum_apply, smul_apply, smul_eq_mul]
  change ∑ j : Fin n, A (standardBasis n j) * (standardBasis n).repr (v 0) j = A (v 0)
  conv_rhs => rw [← (standardBasis n).sum_repr (v 0)]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem exteriorDerivative_function {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (_hU : IsOpen U) (hf : CrOn 1 U f) (x : E n) (hx : x ∈ U) :
    exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x =
      linearCovector (totalDerivative f x).toLinearMap := by
  obtain ⟨A, hA⟩ := hf.1 x hx
  rw [totalDerivative_eq U f A x hA]
  exact exteriorDerivative_scalar U f x A hA

end D04
