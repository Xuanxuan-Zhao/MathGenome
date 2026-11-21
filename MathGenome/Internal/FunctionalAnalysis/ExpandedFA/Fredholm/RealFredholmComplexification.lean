import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RealFredholmComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.RealComplexification
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.Fredholm.RealFredholmComplexification
universe v w
open TraceIdeals.RealComplexification hiding Space
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification
open DefinitionsSpec
open Spec (complexSubspace)
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]

@[simp] lemma mem_complexSubspace (S : Submodule ℝ H) (p : Space H) :
    p ∈ complexSubspace S ↔ p.1 ∈ S ∧ p.2 ∈ S := Iff.rfl

lemma ker_operator (T : H →L[ℝ] K) : (operator T).ker = complexSubspace T.ker := by
  ext p
  change complexPair K (T p.1) (T p.2) = 0 ↔ T p.1 = 0 ∧ T p.2 = 0
  exact Prod.ext_iff

lemma range_operator (T : H →L[ℝ] K) : (operator T).range = complexSubspace T.range := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨q.1, rfl⟩, ⟨q.2, rfl⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨complexPair H x y, Prod.ext hx hy⟩

lemma range_formula (T : H →L[ℝ] K) (p : Space K) :
    p ∈ (operator T).range ↔ ∃ x y : H, p = complexPair K (T x) (T y) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, rfl⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨complexPair H x y, rfl⟩

lemma complexSubspace_closed_iff (S : Submodule ℝ H) :
    IsClosed (complexSubspace S : Set (Space H)) ↔ IsClosed (S : Set H) := by
  constructor
  · intro h
    have hh := h.preimage inclusion.continuous
    convert hh using 1
    ext x
    change x ∈ S ↔ x ∈ S ∧ (0 : H) ∈ S
    simp
  · intro h
    exact (h.preimage realPart.continuous).inter (h.preimage imagPart.continuous)

theorem kernel_range : Spec.KernelRange.{v,w} := by
  intro H K _ _ _ _ _ _ T
  exact ⟨ker_operator T, range_operator T, range_formula T⟩

theorem closed_range : Spec.ClosedRange.{v,w} := by
  intro H K _ _ _ _ _ _ T
  rw [range_operator]
  exact (complexSubspace_closed_iff T.range).symm

/-- The canonical complexification of a real subspace maps isometrically onto
its componentwise complex subspace, with no completeness or dimension assumption. -/
def subspaceEquiv (S : Submodule ℝ H) : Space S ≃ₗᵢ[ℂ] complexSubspace S where
  toFun p := ⟨complexPair H p.1.val p.2.val, p.1.property, p.2.property⟩
  invFun p := complexPair S ⟨p.val.1, p.property.1⟩ ⟨p.val.2, p.property.2⟩
  left_inv p := rfl
  right_inv p := rfl
  map_add' p q := rfl
  map_smul' a p := by
    apply Subtype.ext
    change complexPair H ((a • p).1.val) ((a • p).2.val) =
      a • complexPair H p.1.val p.2.val
    rw [csmul, csmul]
    rfl
  norm_map' p := by
    have h₁ := TraceIdeals.RealComplexification.Spec.norm_sq p
    change ‖p‖ ^ 2 = ‖p.1.val‖ ^ 2 + ‖p.2.val‖ ^ 2 at h₁
    have h₂ := TraceIdeals.RealComplexification.Spec.norm_sq (complexPair H p.1.val p.2.val)
    change ‖complexPair H p.1.val p.2.val‖ = ‖p‖
    change ‖complexPair H p.1.val p.2.val‖ ^ 2 = ‖p.1.val‖ ^ 2 + ‖p.2.val‖ ^ 2 at h₂
    nlinarith [norm_nonneg p, norm_nonneg (complexPair H p.1.val p.2.val)]

lemma complexSubspace_orthogonal (S : Submodule ℝ H) :
    (complexSubspace S).orthogonal = complexSubspace S.orthogonal := by
  ext p
  constructor
  · intro hp
    have hh (x : S) := (Submodule.mem_orthogonal _ _).mp hp
      (complexPair H x.val 0) (show complexPair H x.val 0 ∈ complexSubspace S from
        ⟨x.property, S.zero_mem⟩)
    constructor
    · apply (Submodule.mem_orthogonal _ _).mpr
      intro x hx
      have h := congrArg Complex.re (hh ⟨x, hx⟩)
      change (ip H (complexPair H x 0) p).re = 0 at h
      simpa [ip, complexPair] using h
    · apply (Submodule.mem_orthogonal _ _).mpr
      intro x hx
      have h := congrArg Complex.im (hh ⟨x, hx⟩)
      change (ip H (complexPair H x 0) p).im = 0 at h
      simpa [ip, complexPair] using h
  · rintro ⟨hp₁, hp₂⟩
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro q ⟨hq₁, hq₂⟩
    have h₁ := (Submodule.mem_orthogonal _ _).mp hp₁
    have h₂ := (Submodule.mem_orthogonal _ _).mp hp₂
    change ip H q p = 0
    apply Complex.ext <;> simp [ip, h₁ _ hq₁, h₁ _ hq₂, h₂ _ hq₁, h₂ _ hq₂]

theorem kernel_identification : Spec.KernelIdentification.{v,w} := by
  intro H K _ _ _ _ _ _ T
  exact ⟨(subspaceEquiv T.ker).trans (LinearIsometryEquiv.ofEq _ _ (ker_operator T).symm),
    fun _ => rfl⟩

theorem cokernel_identification : Spec.CokernelIdentification.{v,w} := by
  intro H K _ _ _ _ _ _ T _
  have h : complexSubspace T.range.orthogonal = (operator T).range.orthogonal := by
    rw [range_operator, complexSubspace_orthogonal]
  exact ⟨(subspaceEquiv T.range.orthogonal).trans (LinearIsometryEquiv.ofEq _ _ h),
    fun _ => rfl⟩


/-- Restriction to real scalars of the complex subspace is exactly S × S. -/
def realSubspaceEquiv (S : Submodule ℝ H) : complexSubspace S ≃ₗ[ℝ] S × S :=
  ((subspaceEquiv S).symm.toLinearEquiv.restrictScalars ℝ).trans
    (Hilbert.PreHilbertCompactSpectral.Complexification.toPair S)

/-- Dimension comparison uses the two real coordinates on both sides of the
tower law, so there is no factor of two in the final complex dimension. -/
lemma finite_pair_iff {V : Type*} {W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℂ W]
    [Module ℝ W] [IsScalarTower ℝ ℂ W] (e : W ≃ₗ[ℝ] V × V) :
    FiniteDimensional ℂ W ↔ FiniteDimensional ℝ V := by
  constructor
  · intro h
    let := h
    let : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
    let : FiniteDimensional ℝ (V × V) := Module.Finite.equiv e
    exact Module.Finite.of_surjective (LinearMap.fst ℝ V V) (fun x => ⟨(x, 0), rfl⟩)
  · intro h
    let := h
    let : FiniteDimensional ℝ W := Module.Finite.equiv e.symm
    exact Module.Finite.of_restrictScalars_finite ℝ ℂ W

lemma finrank_pair {V : Type*} {W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℂ W]
    [Module ℝ W] [IsScalarTower ℝ ℂ W] (e : W ≃ₗ[ℝ] V × V)
    [FiniteDimensional ℝ V] : Module.finrank ℂ W = Module.finrank ℝ V := by
  have h := Module.finrank_mul_finrank ℝ ℂ W
  rw [Complex.finrank_real_complex, e.finrank_eq, Module.finrank_prod] at h
  omega

/-- The real coordinate quotient map, valid even when S is not closed. -/
def quotientPairMap (S : Submodule ℝ H) : Space H →ₗ[ℝ] (H ⧸ S) × (H ⧸ S) :=
  (S.mkQ.comp realPart.toLinearMap).prod (S.mkQ.comp imagPart.toLinearMap)

lemma quotientPairMap_ker (S : Submodule ℝ H) :
    (quotientPairMap S).ker = (complexSubspace S).restrictScalars ℝ := by
  ext p
  change (S.mkQ p.1, S.mkQ p.2) = 0 ↔ p.1 ∈ S ∧ p.2 ∈ S
  simp

lemma quotientPairMap_surjective (S : Submodule ℝ H) :
    Function.Surjective (quotientPairMap S) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := S.mkQ_surjective x
  obtain ⟨b, rfl⟩ := S.mkQ_surjective y
  exact ⟨complexPair H a b, rfl⟩

/-- Actual algebraic cokernel coordinates, with the scalar restriction explicit. -/
def quotientPairEquiv (S : Submodule ℝ H) :
    (Space H ⧸ complexSubspace S) ≃ₗ[ℝ] (H ⧸ S) × (H ⧸ S) :=
  (Submodule.Quotient.restrictScalarsEquiv ℝ (complexSubspace S)).symm |>.trans
    ((Submodule.quotEquivOfEq _ _ (quotientPairMap_ker S).symm).trans
      ((quotientPairMap S).quotKerEquivOfSurjective (quotientPairMap_surjective S)))

lemma kernel_finite_iff (T : H →L[ℝ] K) :
    FiniteDimensional ℝ T.ker ↔ FiniteDimensional ℂ (operator T).ker := by
  rw [ker_operator]
  exact (finite_pair_iff (realSubspaceEquiv T.ker)).symm

lemma cokernel_finite_iff (T : H →L[ℝ] K) :
    FiniteDimensional ℝ (K ⧸ T.range) ↔
      FiniteDimensional ℂ (Space K ⧸ (operator T).range) := by
  rw [range_operator]
  exact (finite_pair_iff (quotientPairEquiv T.range)).symm

lemma kernel_finrank (T : H →L[ℝ] K) [FiniteDimensional ℝ T.ker] :
    Module.finrank ℝ T.ker = Module.finrank ℂ (operator T).ker := by
  rw [ker_operator]
  exact (finrank_pair (realSubspaceEquiv T.ker)).symm

lemma cokernel_finrank (T : H →L[ℝ] K) [FiniteDimensional ℝ (K ⧸ T.range)] :
    Module.finrank ℝ (K ⧸ T.range) = Module.finrank ℂ (Space K ⧸ (operator T).range) := by
  rw [range_operator]
  exact (finrank_pair (quotientPairEquiv T.range)).symm

theorem dimensions : Spec.Dimensions.{v,w} := by
  intro H K _ _ _ _ _ _ T
  exact ⟨kernel_finite_iff T, cokernel_finite_iff T,
    fun h => @kernel_finrank _ _ _ _ _ _ T h,
    fun h => @cokernel_finrank _ _ _ _ _ _ T h⟩

lemma fredholm_operator_iff (T : H →L[ℝ] K) :
    IsFredholmValue T ↔ IsFredholmValue (operator T) := by
  simp only [IsFredholmValue, range_operator, complexSubspace_closed_iff,
    ← kernel_finite_iff T, ← cokernel_finite_iff T]

theorem fredholm : Spec.Fredholm.{v,w} := by
  intro H K _ _ _ _ _ _ T
  exact fredholm_operator_iff T

lemma index_operator (T : H →L[ℝ] K) (h : IsFredholmValue T)
    (hC : IsFredholmValue (operator T)) :
    fredholmIndexValue T h = fredholmIndexValue (operator T) hC := by
  let := h.2.1
  let := h.2.2
  simp only [fredholmIndexValue, kernel_finrank T, cokernel_finrank T]

theorem index : Spec.Index.{v,w} := by
  intro H K _ _ _ _ _ _ T h hC
  exact index_operator T h hC

@[simp] lemma operator_sub (S T : H →L[ℝ] K) :
    operator (S - T) = operator S - operator T := by ext p; rfl

lemma operator_injective : Function.Injective (operator (H := H) (K := K)) := by
  intro S T h
  ext x
  exact congrArg (fun A : Space H →L[ℂ] Space K => (A (inclusion x)).1) h

lemma operator_shift (T : H →L[ℝ] H) (r : ℝ) :
    operator (T - r • ContinuousLinearMap.id ℝ H) =
      operator T - (r : ℂ) • ContinuousLinearMap.id ℂ (Space H) := by
  rw [operator_sub, operator_real_smul, operator_id]

section Spectral
variable [CompleteSpace H]

/-- Units are actual two-sided bounded inverses; use the owner's inverse
transport in both directions, including its real-coordinate descent. -/
lemma isUnit_operator_iff (A : H →L[ℝ] H) : IsUnit (operator A) ↔ IsUnit A := by
  simpa only [isUnit_iff_exists, ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
    using (TraceIdeals.RealComplexification.invertibility H A).1.symm

theorem spectrum_comparison : Spec.Spectrum.{v} := by
  intro H _ _ _ T r
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have h : operator (algebraMap ℝ (H →L[ℝ] H) r - T) =
      algebraMap ℂ (Space H →L[ℂ] Space H) (r : ℂ) - operator T := by
    simp only [Algebra.algebraMap_eq_smul_one, operator_sub, operator_real_smul,
      ContinuousLinearMap.one_def, operator_id]
  rw [← h, isUnit_operator_iff]

theorem shift_comparison : Spec.Shift.{v} := by
  intro H _ _ _ T r
  have hs := operator_shift T r
  refine ⟨hs, ?_, ?_⟩
  · rw [← hs]
    exact not_congr (fredholm_operator_iff _)
  · intro h hC
    have hi := index_operator (T - r • ContinuousLinearMap.id ℝ H) h
      ((fredholm_operator_iff _).mp h)
    simpa only [hs] using hi

theorem normality : Spec.Normality.{v} := by
  intro H _ _ _ T
  simp only [isStarNormal_iff, Commute, SemiconjBy, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def]
  rw [operator_adjoint, ← operator_comp, ← operator_comp]
  exact ⟨congrArg operator, fun h => operator_injective h⟩
end Spectral

end ExpandedFA.Fredholm.RealFredholmComplexification
