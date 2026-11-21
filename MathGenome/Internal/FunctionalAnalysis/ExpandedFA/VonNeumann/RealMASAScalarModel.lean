import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealMASAScalarModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.RealAbelianComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.ScalarMultiplicationCommutant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.SeparableMASA
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.VonNeumann.RealMASAScalarModel
open TraceIdeals.RealComplexification
open RealAbelianComplexification.Spec.NativeLp
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- Restriction first lands in the fixed subspace as a real linear isometry. -/
def restrictionEmbedding (D : InvolutionData μ) (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hV : ∀ z, V (conjugation z) = conjugatePullback D (V z)) :
    H →ₗᵢ[ℝ] Fixed D 2 where
  toFun x := ⟨V (inclusion x), by
    change conjugatePullback D (V (inclusion x)) = V (inclusion x)
    rw [← hV]
    congr 1
    exact ((TraceIdeals.RealComplexification.coordinates H).2.1 _).mpr ⟨x, rfl⟩⟩
  map_add' x y := by apply Subtype.ext; simp only [map_add]; rfl
  map_smul' a x := by
    apply Subtype.ext
    change V (inclusion (a • x)) = a • V (inclusion x)
    rw [map_smul]
    exact (V.toLinearEquiv.restrictScalars ℝ).map_smul a (inclusion x)
  norm_map' x := by
    change ‖V (inclusion x)‖ = ‖x‖
    rw [V.norm_map, inclusion.norm_map]

theorem restrictionEmbedding_surjective (D : InvolutionData μ)
    (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hV : ∀ z, V (conjugation z) = conjugatePullback D (V z)) :
    Function.Surjective (restrictionEmbedding D V hV) := by
  intro f
  obtain ⟨z, hz⟩ := V.surjective f.val
  have hfix : conjugation z = z := by
    apply V.injective
    rw [hV, hz]
    exact f.property
  obtain ⟨x, hx⟩ := ((TraceIdeals.RealComplexification.coordinates H).2.1 z).mp hfix
  change inclusion x = z at hx
  exact ⟨x, Subtype.ext (by change V (inclusion x) = f.val; rw [hx, hz])⟩

/-- The restriction, with its inverse obtained by fixed-point surjectivity. -/
def equivariantRestriction (D : InvolutionData μ) (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hV : ∀ z, V (conjugation z) = conjugatePullback D (V z)) :
    H ≃ₗᵢ[ℝ] Fixed D 2 :=
  LinearIsometryEquiv.ofSurjective (restrictionEmbedding D V hV)
    (restrictionEmbedding_surjective D V hV)

theorem equivariant_restriction : Spec.EquivariantRestriction.{u} := by
  intro H _ _ X _ μ D V hV
  exact ⟨equivariantRestriction D V hV, fun _ => rfl⟩

/-- A real intertwining identity extends over the canonical complexification. -/
theorem complex_intertwining (D : InvolutionData μ)
    (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (U : H ≃ₗᵢ[ℝ] Fixed D 2)
    (hUV : ∀ x, (U x).val = V (inclusion x))
    (T : H →L[ℝ] H) (f : Fixed D ∞)
    (hT : ∀ x, U (T x) = restrictedMultiplier D f (U x)) :
    ∀ z, V (operator T z) = ScalarMultiplicationCommutant.Spec.multiplier μ f.val (V z) := by
  let M := ScalarMultiplicationCommutant.Spec.multiplier μ f.val
  have hj (x : H) : V (operator T (inclusion x)) = M (V (inclusion x)) := by
    rw [operator_inclusion]
    calc
      V (inclusion (T x)) = (U (T x)).val := (hUV _).symm
      _ = (restrictedMultiplier D f (U x)).val := congrArg Subtype.val (hT x)
      _ = M ((U x).val) := rfl
      _ = M (V (inclusion x)) := congrArg M (hUV x)
  intro z
  calc
    V (operator T z) = V (operator T (inclusion z.1 + Complex.I • inclusion z.2)) :=
      congrArg (fun w => V (operator T w)) (decomposition z)
    _ = M (V (inclusion z.1 + Complex.I • inclusion z.2)) := by
      simp only [map_add, map_smul, hj]
    _ = M (V z) := congrArg (fun w => M (V w)) (decomposition z).symm

/-- Surjective isometric intertwining preserves the operator norm. -/
theorem norm_of_unitary_intertwining
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (S : F →L[ℂ] F)
    (h : ∀ x, V (T x) = S (V x)) : ‖T‖ = ‖S‖ := by
  apply le_antisymm
  · apply T.opNorm_le_bound (norm_nonneg S)
    intro x
    calc
      ‖T x‖ = ‖V (T x)‖ := (V.norm_map _).symm
      _ = ‖S (V x)‖ := congrArg norm (h x)
      _ ≤ ‖S‖ * ‖V x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [V.norm_map]
  · apply S.opNorm_le_bound (norm_nonneg T)
    intro y
    obtain ⟨x, rfl⟩ := V.surjective y
    calc
      ‖S (V x)‖ = ‖V (T x)‖ := congrArg norm (h x).symm
      _ = ‖T x‖ := V.norm_map _
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖V x‖ := by rw [V.norm_map]

/-- Uniqueness is equality of native L∞ classes, with no positivity of mass. -/
theorem symbol_unique [IsFiniteMeasure μ] (D : InvolutionData μ)
    (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (U : H ≃ₗᵢ[ℝ] Fixed D 2)
    (hUV : ∀ x, (U x).val = V (inclusion x))
    (T : H →L[ℝ] H) (f g : Fixed D ∞)
    (hf : ∀ x, U (T x) = restrictedMultiplier D f (U x))
    (hg : ∀ x, U (T x) = restrictedMultiplier D g (U x)) : f = g := by
  apply Subtype.ext
  apply ScalarMultiplicationCommutant.multiplier_injective μ
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := V.surjective y
  exact (complex_intertwining D V U hUV T f hf z).symm.trans
    (complex_intertwining D V U hUV T g hg z)

/-- Exact symbol norm, obtained by complexification and native multiplication. -/
theorem symbol_norm [IsFiniteMeasure μ] (D : InvolutionData μ)
    (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (U : H ≃ₗᵢ[ℝ] Fixed D 2)
    (hUV : ∀ x, (U x).val = V (inclusion x))
    (T : H →L[ℝ] H) (f : Fixed D ∞)
    (hf : ∀ x, U (T x) = restrictedMultiplier D f (U x)) : ‖T‖ = ‖f‖ := by
  calc
    ‖T‖ = ‖operator T‖ := (operator_norm T).symm
    _ = ‖ScalarMultiplicationCommutant.Spec.multiplier μ f.val‖ :=
      norm_of_unitary_intertwining V _ _ (complex_intertwining D V U hUV T f hf)
    _ = ‖f.val‖ := ScalarMultiplicationCommutant.multiplier_norm μ f.val
    _ = ‖f‖ := rfl

theorem multiplier_covariance (D : InvolutionData μ) (f : Lp ℂ ∞ μ)
    (v : Lp ℂ 2 μ) :
    conjugatePullback D (ScalarMultiplicationCommutant.Spec.multiplier μ f v) =
      ScalarMultiplicationCommutant.Spec.multiplier μ (conjugatePullback D f)
        (conjugatePullback D v) :=
  conjugatePullback_holder D f v

/-- The native restricted multiplication action preserves adjoints. -/
theorem restrictedMultiplier_star (D : InvolutionData μ) (f : Fixed D ∞) :
    restrictedMultiplier D (star f) = star (restrictedMultiplier D f) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  change inner ℝ (restrictedMultiplier D (star f) v).val w.val =
    inner ℝ v.val (restrictedMultiplier D f w).val
  rw [RealAbelianComplexification.NativeLp.l2_inner_real_formula,
    RealAbelianComplexification.NativeLp.l2_inner_real_formula]
  congr 1
  apply integral_congr_ae
  filter_upwards [coeFn_restrictedMultiplier D (star f) v,
    coeFn_fixedStar D f, coeFn_restrictedMultiplier D f w] with x h1 h2 h3
  rw [h1, h2, h3, star_mul, star_star]
  ring

/-- Equivariance forces the coefficient of an actual real operator to be fixed. -/
theorem symbol_fixed_of_equivariant [IsFiniteMeasure μ] (D : InvolutionData μ)
    (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hV : ∀ z, V (conjugation z) = conjugatePullback D (V z))
    (T : H →L[ℝ] H) (f : Lp ℂ ∞ μ)
    (hf : ∀ z, V (operator T z) = ScalarMultiplicationCommutant.Spec.multiplier μ f (V z)) :
    conjugatePullback D f = f := by
  apply ScalarMultiplicationCommutant.multiplier_injective μ
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := V.surjective y
  have hJ : conjugation (operator T (conjugation z)) = operator T z := by
    apply Prod.ext
    · rfl
    · change -(T (-z.2)) = T z.2
      simp only [map_neg, neg_neg]
  have hc := congrArg (conjugatePullback D) (hf (conjugation z))
  rw [← hV, hJ, multiplier_covariance, ← hV,
    (TraceIdeals.RealComplexification.coordinates H).2.2.1 z] at hc
  exact hc.symm.trans (hf z)

section Descent
variable [CompleteSpace H]
local instance : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

/-- The actual fixed-real unitary associated to a normalized complex model. -/
def realUnitary {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) :
    H ≃ₗᵢ[ℝ] Fixed C.geometry.involution 2 :=
  equivariantRestriction C.geometry.involution C.Uc C.equivariant

theorem realUnitary_all_multipliers {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) (T : H →L[ℝ] H) :
    T ∈ A ↔ ∃ f : Fixed C.geometry.involution ∞,
      ∀ x, realUnitary C (T x) = restrictedMultiplier C.geometry.involution f (realUnitary C x) := by
  constructor
  · intro hT
    have hTC : operator T ∈ RealAbelianComplexification.Spec.complexAlgebra A := by
      apply StarAlgebra.subset_adjoin
      exact ⟨T, hT, rfl⟩
    obtain ⟨f, hf⟩ := (C.all_multipliers (operator T)).mp hTC
    let g : Fixed C.geometry.involution ∞ :=
      ⟨f, symbol_fixed_of_equivariant _ C.Uc C.equivariant T f hf⟩
    refine ⟨g, fun x => ?_⟩
    apply Subtype.ext
    change C.Uc (inclusion (T x)) =
      ScalarMultiplicationCommutant.Spec.multiplier C.geometry.μ f (C.Uc (inclusion x))
    simpa only [operator_inclusion] using hf (inclusion x)
  · rintro ⟨f, hf⟩
    have hTC := (C.all_multipliers (operator T)).mpr
      ⟨f.val, complex_intertwining _ C.Uc (realUnitary C) (fun _ => rfl) T f hf⟩
    have hr := (RealAbelianComplexification.mem_complexAlgebra A (operator T)).mp hTC
    simpa only [RealAbelianComplexification.realPart_operator] using hr.1

/-- Inverse unitary transport of the native multiplication representation. -/
def transportedMultipliers (D : InvolutionData μ) (U : H ≃ₗᵢ[ℝ] Fixed D 2) :
    Fixed D ∞ →⋆ₐ[ℝ] (H →L[ℝ] H) where
  toAlgHom := U.symm.conjStarAlgEquiv.toAlgEquiv.toAlgHom.comp (multiplierAlgebraHom D)
  map_star' f := by
    change U.symm.conjStarAlgEquiv (restrictedMultiplier D (star f)) =
      star (U.symm.conjStarAlgEquiv (restrictedMultiplier D f))
    rw [restrictedMultiplier_star, map_star]

theorem transportedMultipliers_intertwining (D : InvolutionData μ)
    (U : H ≃ₗᵢ[ℝ] Fixed D 2) (f : Fixed D ∞) (x : H) :
    U (transportedMultipliers D U f x) = restrictedMultiplier D f (U x) := by
  change U (U.symm (restrictedMultiplier D f (U x))) = _
  exact U.apply_symm_apply _

def modelHom {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) : Fixed C.geometry.involution ∞ →⋆ₐ[ℝ] A :=
  (transportedMultipliers C.geometry.involution (realUnitary C)).codRestrict A (fun f =>
    (realUnitary_all_multipliers C _).mpr
      ⟨f, transportedMultipliers_intertwining _ _ f⟩)

theorem modelHom_intertwining {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) (f : Fixed C.geometry.involution ∞) (x : H) :
    realUnitary C ((modelHom C f : H →L[ℝ] H) x) =
      restrictedMultiplier C.geometry.involution f (realUnitary C x) :=
  transportedMultipliers_intertwining _ _ f x

theorem modelHom_isometry {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) : Isometry (modelHom C) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro f
  exact symbol_norm _ C.Uc (realUnitary C) (fun _ => rfl) _ f
    (modelHom_intertwining C f)

theorem modelHom_surjective {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) : Function.Surjective (modelHom C) := by
  intro T
  obtain ⟨f, hf⟩ := (realUnitary_all_multipliers C T.val).mp T.property
  refine ⟨f, Subtype.ext ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply (realUnitary C).injective
  exact (modelHom_intertwining C f x).trans (hf x).symm

/-- The bijection is induced by multiplication and inverse unitary transport. -/
def modelEquiv {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) : Fixed C.geometry.involution ∞ ≃⋆ₐ[ℝ] A :=
  StarAlgEquiv.ofBijective (modelHom C)
    ⟨(modelHom_isometry C).injective, modelHom_surjective C⟩

/-- Full native real descent, including symbol norm and the star-algebra bijection. -/
def scalarModelOfNormalized {A : StarSubalgebra ℝ (H →L[ℝ] H)} {e : H}
    (C : Spec.NormalizedComplexModel A e) : Spec.ScalarModel A e where
  complexModel := C
  U := realUnitary C
  restriction _ := rfl
  all_multipliers := realUnitary_all_multipliers C
  symbol_unique := symbol_unique _ C.Uc (realUnitary C) (fun _ => rfl)
  symbol_norm := symbol_norm _ C.Uc (realUnitary C) (fun _ => rfl)
  symbolEquiv := modelEquiv C
  symbolIsometry := modelHom_isometry C
  symbolIntertwining := modelHom_intertwining C

theorem normalized_descent : Spec.NormalizedDescent.{u} := by
  intro H _ _ _ A e C
  exact ⟨scalarModelOfNormalized C⟩

end Descent

section SeparableCore
open Set Filter Topology TopologicalSpace
open scoped Topology
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

/-- A norm-bounded sequence converging on a dense set converges strongly.
The bound is essential: convergence on a dense set alone does not suffice. -/
theorem strong_convergence_of_dense_tests (T : E →L[ℂ] E)
    (S : ℕ → E →L[ℂ] E) (hbound : ∀ n, ‖S n‖ ≤ 1)
    (h : ∀ k, Tendsto (fun n => S n (denseSeq E k)) atTop
      (𝓝 (T (denseSeq E k)))) :
    Tendsto S atTop (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E) T) := by
  apply (OperatorTopology.strong_tendsto_iff ℂ E E _ _ _ _).mpr
  have heq : Equicontinuous (fun n x => S n x) :=
    (LipschitzWith.uniformEquicontinuous (fun n x => S n x) 1 (fun n =>
      (S n).lipschitzWith.weaken (by exact_mod_cast hbound n))).equicontinuous
  have hc := heq.isClosed_setOfPred_tendsto (l := atTop) T.continuous
  have hs : Set.range (denseSeq E) ⊆ {x | Tendsto (fun n => S n x) atTop (𝓝 (T x))} := by
    rintro _ ⟨k, rfl⟩
    exact h k
  exact fun x => hc.closure_subset_iff.mpr hs ((denseRange_denseSeq E) x)

/-- Select countably many elements of the unit ball. Their tests on a fixed
countable dense family are dense among all unit-ball tests. -/
theorem countable_unitBall_tests (M : StarSubalgebra ℂ (E →L[ℂ] E)) :
    ∃ s : Set (E →L[ℂ] E), s.Countable ∧
      (∀ S ∈ s, S ∈ M ∧ ‖S‖ ≤ 1) ∧
      ∀ T ∈ M, ‖T‖ ≤ 1 → ∃ S : ℕ → E →L[ℂ] E,
        (∀ n, S n ∈ s) ∧
        Tendsto S atTop (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E) T) := by
  classical
  let L := {T : E →L[ℂ] E // T ∈ M ∧ ‖T‖ ≤ 1}
  let f : L → ℕ → E := fun T k => T.val (denseSeq E k)
  let Y := Set.range f
  let q : Y → L := fun y => Classical.choose y.property
  have hq (y : Y) : f (q y) = y.val := Classical.choose_spec y.property
  obtain ⟨t, ht, hd⟩ := TopologicalSpace.exists_countable_dense Y
  let s : Set (E →L[ℂ] E) := (fun y : Y => (q y).val) '' t
  refine ⟨s, ht.image _, ?_, ?_⟩
  · rintro S ⟨y, _, rfl⟩
    exact (q y).property
  · intro T hT hb
    let y : Y := ⟨f ⟨T, hT, hb⟩, ⟨⟨T, hT, hb⟩, rfl⟩⟩
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hd y)
    refine ⟨fun n => (q (v n)).val, fun n => ⟨v n, hv n, rfl⟩, ?_⟩
    apply strong_convergence_of_dense_tests T _ (fun n => (q (v n)).property.2)
    intro k
    have hl := (continuous_apply k).tendsto y.val |>.comp
      (continuous_subtype_val.tendsto y |>.comp hlim)
    convert hl using 1
    ext n
    exact congrFun (hq (v n)) k

/-- The norm-closed star algebra generated by a countable set is norm separable.
This uses countably many finite words followed by complex linear span. -/
theorem separable_generated_closure (s : Set (E →L[ℂ] E)) (hs : s.Countable) :
    TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set (E →L[ℂ] E)) := by
  have hss : (s ∪ star s).Countable := hs.union (by simpa only [Set.image_star] using hs.image star)
  letI : Countable ↥(s ∪ star s) := hss.to_subtype
  letI : Countable (FreeMonoid ↥(s ∪ star s)) :=
    inferInstanceAs (Countable (List ↥(s ∪ star s)))
  have hm : (Submonoid.closure (s ∪ star s) : Set (E →L[ℂ] E)).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  have ha : TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set (E →L[ℂ] E)) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set (E →L[ℂ] E))
    rw [StarAlgebra.adjoin_eq_span]
    exact hm.isSeparable.span
  exact ha.closure

/-- A complex linear algebra containing the countable tests is strongly
 dense in the original algebra. Scaling the tests covers unbounded operators. -/
theorem strong_density_from_unitBall (M B : StarSubalgebra ℂ (E →L[ℂ] E))
    (s : Set (E →L[ℂ] E)) (hsB : s ⊆ B)
    (hd : ∀ T ∈ M, ‖T‖ ≤ 1 → ∃ S : ℕ → E →L[ℂ] E,
      (∀ n, S n ∈ s) ∧
      Tendsto S atTop (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E) T)) :
    (M : Set _) ⊆ @closure _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E) (B : Set _) := by
  intro T hT
  by_cases hzero : T = 0
  · subst T
    exact @subset_closure _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E)
      (B : Set _) 0 B.zero_mem
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  let c : ℂ := ‖T‖
  let R : E →L[ℂ] E := c⁻¹ • T
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast hn
  have hR : R ∈ M := M.smul_mem hT _
  have hb : ‖R‖ ≤ 1 := by
    dsimp [R, c]
    simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn, le_refl]
  have hscale : c • R = T := by simp [R, smul_smul, hc]
  obtain ⟨S, hS, hlim⟩ := hd R hR hb
  have hlim' : Tendsto (fun n => c • S n) atTop
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E) T) := by
    apply (OperatorTopology.strong_tendsto_iff ℂ E E _ _ _ _).mpr
    intro x
    have h := (tendsto_const_nhds (x := c) (f := atTop)).smul
      ((OperatorTopology.strong_tendsto_iff ℂ E E _ _ _ _).mp hlim x)
    simpa only [← smul_apply, hscale] using h
  letI : TopologicalSpace (E →L[ℂ] E) := OperatorTopology.Spec.StrongTopologyValue ℂ E E
  exact mem_closure_of_tendsto hlim' (Eventually.of_forall (fun n => B.smul_mem (hsB (hS n)) c))

end SeparableCore

section CanonicalCore
open Set Filter Topology TopologicalSpace
open scoped Topology
open RealAbelianComplexification
variable [CompleteSpace H]
local instance : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

/-- Operator conjugation is isometric in the existing operator norm. -/
theorem gamma_norm (R : Space H →L[ℂ] Space H) : ‖gamma R‖ = ‖R‖ := by
  have hle (S : Space H →L[ℂ] Space H) : ‖gamma S‖ ≤ ‖S‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    rw [gamma_apply, conjugation.norm_map]
    simpa only [conjugation.norm_map] using S.le_opNorm (conjugation z)
  exact le_antisymm (hle R) (by simpa only [gamma_gamma] using hle (gamma R))

/-- The continuous real-linear conjugation map on complex operators. -/
def gammaIsometry : (Space H →L[ℂ] Space H) →ₗᵢ[ℝ] (Space H →L[ℂ] Space H) where
  toFun := gamma
  map_add' := gamma_add
  map_smul' a R := by
    change gamma ((a : ℂ) • R) = (a : ℂ) • gamma R
    rw [gamma_smul]
    simp
  norm_map' := gamma_norm

/-- Symmetrizing the generators and then taking norm closure preserves
conjugation stability. All scalar constants are retained. -/
theorem generated_core_stable (s : Set (Space H →L[ℂ] Space H)) :
    ∀ R ∈ (StarAlgebra.adjoin ℂ (s ∪ gamma '' s)).topologicalClosure,
      gamma R ∈ (StarAlgebra.adjoin ℂ (s ∪ gamma '' s)).topologicalClosure := by
  let D := StarAlgebra.adjoin ℂ (s ∪ gamma '' s)
  let B := D.topologicalClosure
  have hg : ∀ R ∈ s ∪ gamma '' s, gamma R ∈ D := by
    intro R hR
    rcases hR with hR | ⟨S, hS, rfl⟩
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨R, hR, rfl⟩)
    · rw [gamma_gamma]
      exact StarAlgebra.subset_adjoin ℂ _ (Or.inl hS)

  have hD : ∀ R ∈ D, gamma R ∈ B := by
    intro R hR
    induction hR using StarAlgebra.adjoin_induction with
    | mem R hR => exact D.le_topologicalClosure (hg R hR)
    | algebraMap a =>
      rw [Algebra.algebraMap_eq_smul_one, gamma_smul, gamma_one]
      exact B.smul_mem B.one_mem _
    | add R S _ _ hR hS => rw [gamma_add]; exact B.add_mem hR hS
    | mul R S _ _ hR hS => rw [gamma_mul]; exact B.mul_mem hR hS
    | star R _ hR => rw [gamma_star]; exact star_mem hR
  have hclosure : closure (D : Set (Space H →L[ℂ] Space H)) ⊆
      (gamma (H := H)) ⁻¹' (B : Set (Space H →L[ℂ] Space H)) :=
    closure_minimal (fun R hR => hD R hR)
      (D.isClosed_topologicalClosure.preimage gammaIsometry.continuous)
  exact hclosure

/-- Construct a countably generated C* core, proving rather than assuming
its norm separability, conjugation stability and strong density. -/
theorem separable_core : Spec.SeparableCoreConstruction.{u} := by
  intro H _ _ _ _ A hA e he
  letI : SeparableSpace (Space H) := RealAbelianComplexification.separability H
  let M := RealAbelianComplexification.Spec.complexAlgebra A
  have hM : SeparableMASA.Spec.IsMASA M := masa_transport H A hA
  obtain ⟨s, hs, hsm, hd⟩ := countable_unitBall_tests M
  let t := s ∪ gamma '' s
  let D := StarAlgebra.adjoin ℂ t
  let B := D.topologicalClosure
  have htM : t ⊆ M := by
    rintro R (hR | ⟨S, hS, rfl⟩)
    · exact (hsm R hR).1
    · exact (algebra_fixed_points H A).1 S (hsm S hS).1
  have hBM : B ≤ M :=
    StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le htM)
      (SeparableMASA.maximalAbelian_normClosed M hM.1)
  have hsB : s ⊆ B := fun R hR => D.le_topologicalClosure
    (StarAlgebra.subset_adjoin ℂ t (Or.inl hR))
  have hstrong : @closure _ (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
      (B : Set _) = (M : Set _) := by
    apply Set.Subset.antisymm
    · exact @closure_minimal _ (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
        _ _ hBM (hM.2.mono (OperatorTopology.topology_comparison ℂ (Space H) (Space H)).2)
    · exact strong_density_from_unitBall M B s hsB hd
  have hcyclic : SeparableMASA.Spec.IsCyclic B (inclusion e) := by
    have hmcyclic := (cyclic_separating_transport H A e).1 he
    intro z
    have hsub : Set.range (fun R : M => R.val (inclusion e)) ⊆
        closure (Set.range (fun R : B => R.val (inclusion e))) := by
      rintro _ ⟨R, rfl⟩
      have hR : R.val ∈ @closure _
          (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)) (B : Set _) := by
        rw [hstrong]
        exact R.property
      have hEval : R.val (inclusion e) ∈ closure
          ((fun S : Space H →L[ℂ] Space H => S (inclusion e)) '' (B : Set _)) := by
        letI : TopologicalSpace (Space H →L[ℂ] Space H) :=
          OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)
        have hcont : Continuous (fun S : Space H →L[ℂ] Space H => S (inclusion e)) :=
          (continuous_apply (inclusion e)).comp continuous_induced_dom
        exact image_closure_subset_closure_image hcont ⟨R.val, hR, rfl⟩
      apply closure_mono ?_ hEval
      rintro _ ⟨S, hS, rfl⟩
      exact ⟨⟨S, hS⟩, rfl⟩
    exact closure_minimal hsub isClosed_closure (hmcyclic z)
  exact ⟨{ algebra := B
           included := hBM
           closed := D.isClosed_topologicalClosure
           separable := separable_generated_closure t (hs.union (hs.image gamma))
           stable := generated_core_stable s
           cyclic := hcyclic
           strongClosure := hstrong }⟩

end CanonicalCore

namespace CharacterGeometry
variable {B : Type u} [CommCStarAlgebra B]

structure RealStructure (B : Type u) [CommCStarAlgebra B] where
  toFun : B → B
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_smul : ∀ (z : ℂ) a, toFun (z • a) = star z • toFun a
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_one : toFun 1 = 1
  involutive : Function.Involutive toFun

variable (D : RealStructure B)

def twistAlgHom (χ : WeakDual.characterSpace ℂ B) : B →ₐ[ℂ] ℂ where
  toFun b := star (χ (D.toFun b))
  map_one' := by simp [D.map_one]
  map_mul' a b := by simp [D.map_mul]
  map_zero' := by
    have hz : D.toFun 0 = 0 := by simpa using D.map_smul (0 : ℂ) (0 : B)
    simp [hz]
  map_add' a b := by simp [D.map_add]
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, D.map_smul, D.map_one]
    simp

def twist (χ : WeakDual.characterSpace ℂ B) : WeakDual.characterSpace ℂ B :=
  WeakDual.CharacterSpace.equivAlgHom.symm (twistAlgHom D χ)

@[simp] theorem twist_apply (χ : WeakDual.characterSpace ℂ B) (b : B) :
    twist D χ b = star (χ (D.toFun b)) := rfl

theorem twist_involutive : Function.Involutive (twist D) := by
  intro χ
  apply WeakDual.CharacterSpace.ext
  intro b
  simp only [twist_apply, D.involutive b, star_star]

theorem twist_continuous : Continuous (twist D) := by
  apply continuous_induced_rng.mpr
  apply WeakDual.continuous_of_continuous_eval
  intro b
  exact continuous_star.comp ((WeakDual.eval_continuous (D.toFun b)).comp continuous_subtype_val)

def tau : WeakDual.characterSpace ℂ B ≃ₜ WeakDual.characterSpace ℂ B where
  toEquiv := Function.Involutive.toPerm (twist D) (twist_involutive D)
  continuous_toFun := twist_continuous D
  continuous_invFun := twist_continuous D

@[simp] theorem tau_apply (χ : WeakDual.characterSpace ℂ B) (b : B) :
    tau D χ b = star (χ (D.toFun b)) := rfl

theorem character_metrizable [TopologicalSpace.SeparableSpace B] :
    TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ B) := by
  apply WeakDual.metrizable_of_isCompact ℂ B
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem gelfand_covariance (D : RealStructure B) (b : B) :
    gelfandStarTransform B (D.toFun b) =
      ⟨fun χ => star (gelfandStarTransform B b (tau D χ)),
        continuous_star.comp ((gelfandStarTransform B b).continuous.comp (tau D).continuous)⟩ := by
  ext χ
  change χ (D.toFun b) = star (star (χ (D.toFun b)))
  simp

end CharacterGeometry

namespace CharacterGeometry
section MeasureInvariance
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

def theta (τ : X ≃ₜ X) (f : C(X, ℂ)) : C(X, ℂ) :=
  ⟨fun x => star (f (τ x)), continuous_star.comp (f.continuous.comp τ.continuous)⟩

@[simp] theorem theta_apply (τ : X ≃ₜ X) (f : C(X, ℂ)) (x : X) :
    theta τ f x = star (f (τ x)) := rfl

theorem measurePreserving_of_covariant_functional (τ : X ≃ₜ X)
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (F : C(X, ℂ) → ℂ)
    (hrep : ∀ f : C(X, ℂ), F f = ∫ x, f x ∂μ)
    (hcov : ∀ f, F (theta τ f) = star (F f)) :
    MeasurePreserving τ μ μ := by
  refine ⟨τ.measurable, ?_⟩
  haveI : (Measure.map τ μ).Regular := Measure.Regular.map τ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(X, ℂ) := ⟨fun x => (f x : ℂ),
    Complex.continuous_ofReal.comp f.continuous⟩
  have hh := hcov fc
  rw [hrep, hrep] at hh
  have heq : (∫ x, (f (τ x) : ℂ) ∂μ) = star (∫ x, (f x : ℂ) ∂μ) := by
    simpa [theta, fc] using hh
  have hr := congrArg Complex.re heq
  simp only [integral_complex_ofReal, Complex.ofReal_re, Complex.star_def, Complex.conj_re] at hr
  rw [τ.isClosedEmbedding.integral_map]
  exact hr
end MeasureInvariance
end CharacterGeometry

namespace CharacterGeometry
open ExpandedFA
open scoped IsMulCommutative
open ExpandedFA.TraceIdeals.RealComplexification
open ExpandedFA.VonNeumann.RealAbelianComplexification
open ExpandedFA.VonNeumann.CyclicAbelianScalarRepresentation
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := ExpandedFA.TraceIdeals.RealComplexification.Spec.completeSpace

def coreStructure (B : StarSubalgebra ℂ (Space H →L[ℂ] Space H))
    [IsClosed (B : Set (Space H →L[ℂ] Space H))] [IsMulCommutative B]
    (stable : ∀ R ∈ B, gamma R ∈ B) : RealStructure B where
  toFun b := ⟨gamma b.val, stable b.val b.property⟩
  map_add a b := Subtype.ext (gamma_add a.val b.val)
  map_smul z a := Subtype.ext (gamma_smul z a.val)
  map_mul a b := Subtype.ext (gamma_mul a.val b.val)
  map_one := Subtype.ext gamma_one
  involutive a := Subtype.ext (gamma_gamma a.val)

def corePi (B : StarSubalgebra ℂ (Space H →L[ℂ] Space H))
    [IsClosed (B : Set (Space H →L[ℂ] Space H))] [IsMulCommutative B] :
    C(WeakDual.characterSpace ℂ B, ℂ) →⋆ₐ[ℂ] (Space H →L[ℂ] Space H) :=
  B.subtype.comp (gelfandStarTransform B).symm.toStarAlgHom

lemma corePi_gamma (B : StarSubalgebra ℂ (Space H →L[ℂ] Space H))
    [IsClosed (B : Set (Space H →L[ℂ] Space H))] [IsMulCommutative B]
    (stable : ∀ R ∈ B, gamma R ∈ B)
    (f : C(WeakDual.characterSpace ℂ B, ℂ)) :
    gamma (corePi B f) = corePi B (theta (tau (coreStructure B stable)) f) := by
  let D := coreStructure B stable
  let E := gelfandStarTransform B
  change ((D.toFun (E.symm f) : B) : Space H →L[ℂ] Space H) =
    ((E.symm (theta (tau D) f) : B) : Space H →L[ℂ] Space H)
  congr 1
  apply E.injective
  change E (D.toFun (E.symm f)) = E (E.symm (theta (tau D) f))
  rw [E.apply_symm_apply]
  change gelfandStarTransform B (D.toFun (E.symm f)) = _
  rw [gelfand_covariance]
  ext χ
  change star (E (E.symm f) (tau D χ)) = _
  rw [E.apply_symm_apply]
  rfl

lemma corePi_orbit_covariance (B : StarSubalgebra ℂ (Space H →L[ℂ] Space H))
    [IsClosed (B : Set (Space H →L[ℂ] Space H))] [IsMulCommutative B]
    (stable : ∀ R ∈ B, gamma R ∈ B) (e : H)
    (f : C(WeakDual.characterSpace ℂ B, ℂ)) :
    conjugation (corePi B f (inclusion e)) =
      corePi B (theta (tau (coreStructure B stable)) f) (inclusion e) := by
  rw [← corePi_gamma B stable f, gamma_inclusion]

lemma vectorFunctional_covariance {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (π : C(X, ℂ) →⋆ₐ[ℂ] (Space H →L[ℂ] Space H)) (e : H) (τ : X ≃ₜ X)
    (hcov : ∀ f, conjugation (π f (inclusion e)) = π (theta τ f) (inclusion e)) :
    ∀ f, vectorFunctional π (inclusion e) (theta τ f) = star (vectorFunctional π (inclusion e) f) := by
  intro f
  change inner ℂ (inclusion e) (π (theta τ f) (inclusion e)) =
    star (inner ℂ (inclusion e) (π f (inclusion e)))
  rw [← hcov]
  have hfixed : conjugation (inclusion e) = inclusion e := by
    change (e, -(0 : H)) = (e, 0)
    simp
  simpa only [hfixed] using inner_conjugation (inclusion e) (π f (inclusion e))

end CharacterGeometry

section WholeMultiplierAlgebra
universe v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {X : Type v} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- A multiplication representation of a strongly dense core identifies the
entire maximal abelian algebra, while preserving the prescribed unitary. -/
theorem all_multipliers_of_strongClosure
    (M B : StarSubalgebra ℂ (E →L[ℂ] E))
    (hM : SeparableMASA.Spec.IsMaximalAbelian M)
    (hclosure : @closure _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E)
      (B : Set (E →L[ℂ] E)) = (M : Set _))
    (V : E ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hV : ∀ S ∈ B, ∃ f : Lp ℂ ∞ μ, ∀ x,
      V (S x) = ScalarMultiplicationCommutant.Spec.multiplier μ f (V x)) :
    ∀ T : E →L[ℂ] E, T ∈ M ↔ ∃ f : Lp ℂ ∞ μ, ∀ x,
      V (T x) = ScalarMultiplicationCommutant.Spec.multiplier μ f (V x) := by
  let Q (f : Lp ℂ ∞ μ) : E →L[ℂ] E :=
    V.symm.conjStarAlgEquiv (ScalarMultiplicationCommutant.Spec.multiplier μ f)
  have hQ (f : Lp ℂ ∞ μ) (x : E) :
      V (Q f x) = ScalarMultiplicationCommutant.Spec.multiplier μ f (V x) := by
    exact V.apply_symm_apply _
  have hcomm (f : Lp ℂ ∞ μ) (S : E →L[ℂ] E) (hS : S ∈ B) :
      S * Q f = Q f * S := by
    obtain ⟨g, hg⟩ := hV S hS
    apply ContinuousLinearMap.ext
    intro x
    apply V.injective
    change V (S (Q f x)) = V (Q f (S x))
    rw [hg, hQ, hQ, hg]
    exact congrArg (fun R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => R (V x))
      (ScalarMultiplicationCommutant.multipliers_commute μ g f)
  have hQmem (f : Lp ℂ ∞ μ) : Q f ∈ M := by
    rw [← SeparableMASA.maximalAbelian_eq_commutant M hM,
      ← SetLike.mem_coe, SeparableMASA.coe_commutant]
    have hclosed : @IsClosed _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E)
        (Set.centralizer ({Q f} : Set (E →L[ℂ] E))) :=
      (OperatorTopology.weak_closed_centralizer _).mono
        (OperatorTopology.topology_comparison ℂ E E).2
    have hsub : (B : Set (E →L[ℂ] E)) ⊆
        Set.centralizer ({Q f} : Set (E →L[ℂ] E)) := by
      intro S hS R hR
      have hR' : R = Q f := Set.mem_singleton_iff.mp hR
      rw [hR']
      exact (hcomm f S hS).symm
    have hc : (M : Set (E →L[ℂ] E)) ⊆
        Set.centralizer ({Q f} : Set (E →L[ℂ] E)) := by
      rw [← hclosure]
      exact @closure_minimal _ (OperatorTopology.Spec.StrongTopologyValue ℂ E E)
        _ _ hsub hclosed
    intro S hS
    exact (hc hS (Q f) (Set.mem_singleton _)).symm
  intro T
  constructor
  · intro hT
    have hc : ScalarMultiplicationCommutant.Spec.CommutesWithMultipliers μ
        (V.conjStarAlgEquiv T) := by
      intro f
      apply ContinuousLinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := V.surjective y
      have ht := congrArg (fun R : E →L[ℂ] E => V (R x))
        (hM.1 T hT (Q f) (hQmem f))
      change V (T (V.symm (ScalarMultiplicationCommutant.Spec.multiplier μ f (V x)))) =
        ScalarMultiplicationCommutant.Spec.multiplier μ f (V (T (V.symm (V x))))
      simpa only [mul_apply_eq_comp, hQ, Q,
        LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
        V.apply_symm_apply, V.symm_apply_apply] using ht
    obtain ⟨f, ⟨hf, _⟩, _⟩ :=
      ScalarMultiplicationCommutant.finite_commutant ℂ X μ (V.conjStarAlgEquiv T) hc
    refine ⟨f, fun x => ?_⟩
    have hx := congrArg (fun R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => R (V x)) hf
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, V.symm_apply_apply] using hx
  · rintro ⟨f, hf⟩
    have hT : T = Q f := by
      apply ContinuousLinearMap.ext
      intro x
      apply V.injective
      exact (hf x).trans (hQ f x).symm
    rw [hT]
    exact hQmem f

end WholeMultiplierAlgebra

section NormalizedCyclic
open Set Filter CyclicAbelianScalarRepresentation
open scoped InnerProductSpace ZeroAtInfty CStarAlgebra
universe v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
local instance : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace
variable {X : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable (π : C(X, ℂ) →⋆ₐ[ℂ] (Space H →L[ℂ] Space H)) (e : H)
variable (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
variable (hμ : ∀ f : C(X, ℂ), Integrable f μ ∧
  vectorFunctional π (inclusion e) f = ∫ x, f x ∂μ)

omit [T2Space X] [μ.Regular] in
lemma toLp_theta (D : InvolutionData μ) (θ : C(X, ℂ) → C(X, ℂ))
    (hθ : ∀ f x, θ f x = star (f (D.tau x))) (f : C(X, ℂ)) :
    ContinuousMap.toLp 2 μ ℂ (θ f) =
      conjugatePullback D (ContinuousMap.toLp 2 μ ℂ f) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (θ f),
    coeFn_conjugatePullback D (ContinuousMap.toLp 2 μ ℂ f),
    D.measurePreserving.quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f)] with x h1 h2 h3
  rw [h1, h2, h3, hθ]

include hμ in
/-- Conditional normalized equivariant orbit completion for a prescribed measure. -/
theorem compact_normalized_equivariant
    (he : DenseRange (continuousOrbit π (inclusion e)))
    (D : InvolutionData μ) (θ : C(X, ℂ) → C(X, ℂ))
    (hθ : ∀ f x, θ f x = star (f (D.tau x)))
    (hcov : ∀ f, conjugation (π f (inclusion e)) = π (θ f) (inclusion e)) :
    ∃ U : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      (∀ f : C(X, ℂ), U (π f (inclusion e)) = ContinuousMap.toLp 2 μ ℂ f) ∧
      U (inclusion e) = (memLp_const (1 : ℂ)).toLp (fun _ : X => (1 : ℂ)) ∧
      (∀ z, U (conjugation z) = conjugatePullback D (U z)) ∧
      (∀ f : C(X, ℂ), ∀ z : Space H,
        U (π f z) = ScalarMultiplicationCommutant.Spec.multiplier μ
          (ContinuousMap.toLp ∞ μ ℂ f) (U z)) := by
  let j := (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap
  let v := (continuousOrbit π (inclusion e)).toLinearMap
  have hj : DenseRange j := ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)
  have hv : DenseRange v := he
  have hn : ∀ f, ‖j f‖ = ‖v f‖ := fun f =>
    (continuousOrbit_norm π (inclusion e) μ hμ f).symm
  let U : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
    (LinearEquiv.refl ℂ C(X, ℂ)).extendOfIsometry v j hv hj hn
  have hU (f : C(X, ℂ)) : U (π f (inclusion e)) = ContinuousMap.toLp 2 μ ℂ f := by
    change U (v f) = j f
    exact LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ C(X, ℂ)) v j hv hj hn f
  have hnorm : U (inclusion e) = (memLp_const (1 : ℂ)).toLp (fun _ : X => (1 : ℂ)) := by
    have hone : π (1 : C(X, ℂ)) (inclusion e) = inclusion e := by rw [map_one]; rfl
    rw [← hone, hU]
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (1 : C(X, ℂ)),
      (memLp_const (1 : ℂ) (μ := μ) (p := 2)).coeFn_toLp] with x h1 h2
    rw [h1, h2]
    rfl
  have hequiv (z : Space H) :
      U (conjugation z) = conjugatePullback D (U z) := by
    apply congrFun (hv.equalizer (U.continuous.comp conjugation.continuous)
      ((isometry_conjugatePullback D).continuous.comp U.continuous) ?_) z
    funext f
    change U (conjugation (π f (inclusion e))) =
      conjugatePullback D (U (π f (inclusion e)))
    rw [hcov, hU, hU, ← toLp_theta μ D θ hθ f]
  refine ⟨U, hU, hnorm, hequiv, ?_⟩
  intro g z
  apply congrFun (hv.equalizer (U.continuous.comp (π g).continuous)
    ((ScalarMultiplicationCommutant.Spec.multiplier μ
      (ContinuousMap.toLp ∞ μ ℂ g)).continuous.comp U.continuous) ?_) z
  funext f
  change U (π g (π f (inclusion e))) =
    ScalarMultiplicationCommutant.Spec.multiplier μ
      (ContinuousMap.toLp ∞ μ ℂ g) (U (π f (inclusion e)))
  rw [← mul_apply_eq_comp, ← map_mul, hU, hU]
  exact (SpectralMeasure.CyclicModel.multiplier_toLp μ g f).symm
end NormalizedCyclic

open scoped IsMulCommutative in
set_option maxHeartbeats 800000 in
/-- Construct the normalized equivariant compact model from a countably
 generated conjugation-stable core and its unnormalized cyclic vector measure. -/
theorem normalized_complex_construction : Spec.NormalizedConstruction.{u} := by
  intro H _ _ _ _ A hA e he
  letI : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace
  obtain ⟨K⟩ := separable_core H A hA e he
  let B := K.algebra
  have hM := RealAbelianComplexification.masa_transport H A hA
  letI : IsClosed (B : Set (Space H →L[ℂ] Space H)) := K.closed
  letI : IsMulCommutative B :=
    ⟨⟨fun a b => Subtype.ext (hM.1.1 a.val (K.included a.property)
      b.val (K.included b.property))⟩⟩
  letI : TopologicalSpace.SeparableSpace B := K.separable.separableSpace
  let X := WeakDual.characterSpace ℂ B
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : TopologicalSpace.MetrizableSpace X := CharacterGeometry.character_metrizable (B := B)
  let D := CharacterGeometry.coreStructure B K.stable
  let τ := CharacterGeometry.tau D
  let π := CharacterGeometry.corePi B
  let g := gelfandStarTransform B
  have hπ (b : B) : π (g b) = b.val := by
    change (g.symm (g b)).val = b.val
    rw [g.symm_apply_apply]
  have hdense : DenseRange (CyclicAbelianScalarRepresentation.continuousOrbit π (inclusion e)) := by
    apply K.cyclic.mono
    rintro _ ⟨b, rfl⟩
    exact ⟨g b, congrArg (fun T : Space H →L[ℂ] Space H => T (inclusion e)) (hπ b)⟩
  have hcov (f : C(X, ℂ)) :
      conjugation (π f (inclusion e)) = π (CharacterGeometry.theta τ f) (inclusion e) :=
    CharacterGeometry.corePi_orbit_covariance B K.stable e f
  obtain ⟨μ, hreg, hfinite, hrep⟩ :=
    CyclicAbelianScalarRepresentation.exists_vectorMeasure π (inclusion e)
  letI : μ.Regular := hreg
  letI : IsFiniteMeasure μ := ⟨hfinite⟩
  have hpres : MeasurePreserving τ μ μ :=
    CharacterGeometry.measurePreserving_of_covariant_functional τ μ
      (CyclicAbelianScalarRepresentation.vectorFunctional π (inclusion e))
      (fun f => (hrep f).2) (CharacterGeometry.vectorFunctional_covariance π e τ hcov)
  let G : Spec.Geometry.{u} :=
    { X := X
      μ := μ
      tau := τ
      preserving := hpres
      involutive := CharacterGeometry.twist_involutive D }
  obtain ⟨U, _, hnorm, hequiv, hinter⟩ :=
    compact_normalized_equivariant π e μ hrep hdense G.involution
      (CharacterGeometry.theta τ) (fun _ _ => rfl) hcov
  refine ⟨{ geometry := G
            Uc := U
            normalized := hnorm
            equivariant := hequiv
            all_multipliers := ?_ }⟩
  apply all_multipliers_of_strongClosure μ
    (RealAbelianComplexification.Spec.complexAlgebra A) B hM.1 K.strongClosure U
  intro S hS
  refine ⟨ContinuousMap.toLp ∞ μ ℂ (g ⟨S, hS⟩), ?_⟩
  intro z
  simpa only [hπ] using hinter (g ⟨S, hS⟩) z

/-- Assembly uses genuine real MASA cyclicity, with no extra input on A. -/
theorem full_representation : Spec.FullRepresentation.{u} := by
  intro H _ _ _ _ A hA
  obtain ⟨e, he⟩ := SeparableMASA.real_masa_cyclic H A hA
  obtain ⟨C⟩ := normalized_complex_construction H A hA e he
  exact ⟨e, he, ⟨scalarModelOfNormalized C⟩⟩

end ExpandedFA.VonNeumann.RealMASAScalarModel
