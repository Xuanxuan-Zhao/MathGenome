import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ReproducingKernels

noncomputable section
open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace ExpandedFA.PartV.ReproducingKernels
universe u v w w'
open Spec

/-- Hilbert functions with a scalar-linear injective realization and continuous
individual evaluations, using the independent canonical interface. -/
abbrev FunctionSpace : Spec.FunctionSpaceType.{u, v, w} := Spec.FunctionSpaceValue

/-- The product topology requires continuity of each evaluation separately. -/
@[instance_reducible] def toRKHS {𝕜 : Type u} {X : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (F : FunctionSpace 𝕜 X H) : RKHS 𝕜 H X 𝕜 where
  coeCLM := { F.functions with cont := continuous_pi F.continuous_eval }
  coeCLM_injective := F.injective

/-- Read a native scalar RKHS as an injectively realized function space. -/
def functionSpace {𝕜 : Type u} {X : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [RKHS 𝕜 H X 𝕜] :
    FunctionSpace 𝕜 X H where
  functions := (RKHS.coeCLM 𝕜).toLinearMap
  injective := RKHS.coeCLM_injective
  continuous_eval := RKHS.continuous_eval_const

lemma positiveKernel_iff_matrix {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
    (K : X → X → 𝕜) : PositiveKernel K ↔ (Matrix.of K).PosSemidef := by
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨?_, fun c => ?_⟩
    · ext x y
      simpa using congrArg conj (hs x y)
    · rcases hp c with ⟨r, hr, h⟩
      have he : (c.sum fun x a => c.sum fun y b => star a * Matrix.of K x y * b) =
          (c.sum fun x a => c.sum fun y b => conj a * b * K x y) := by
        simp only [Matrix.of_apply, RCLike.star_def, mul_right_comm]
      rw [he, h]
      exact RCLike.ofReal_nonneg.mpr hr
  · rintro ⟨hs, hp⟩
    refine ⟨fun x y => ?_, fun c => ?_⟩
    · simpa only [Matrix.of_apply, RCLike.star_def] using (hs.apply y x).symm
    · have h := hp c
      simp only [Matrix.of_apply, RCLike.star_def, mul_right_comm] at h
      rcases RCLike.nonneg_iff_exists_ofReal.mp h with ⟨r, hr, he⟩
      exact ⟨r, hr, he.symm⟩

/-- Scalar multiplication operators allow use of the vector-valued native construction. -/
def scalarOperators {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
    (K : X → X → 𝕜) : Matrix X X (𝕜 →L[𝕜] 𝕜) :=
  Matrix.of fun x y => K x y • ContinuousLinearMap.id 𝕜 𝕜

lemma scalarOperators_posSemidef {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
    (K : X → X → 𝕜) (hK : PositiveKernel K) : (scalarOperators K).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun c => ?_⟩
  · ext x y
    simp [scalarOperators, Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint,
      hK.1 x y, ContinuousLinearMap.adjoint_id]
  · rcases hK.2 c with ⟨r, hr, he⟩
    have heq : (c.sum fun x a => c.sum fun y b =>
        ⟪scalarOperators K y x a, b⟫_𝕜) =
        (c.sum fun x a => c.sum fun y b => conj a * b * K x y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp [scalarOperators, RCLike.inner_apply, hK.1 x y]
      ring
    rw [heq, he]
    simpa using hr

lemma native_reproduces {𝕜 : Type u} {X : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [RKHS 𝕜 H X 𝕜] : Reproduces (functionSpace (𝕜 := 𝕜) (X := X) (H := H))
      (fun x => RKHS.kerFun H x 1) := by
  intro f x
  simp [functionSpace, RCLike.inner_apply]

lemma gram_positive {𝕜 : Type u} {X : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (k : X → H) :
    PositiveKernel (fun x y => ⟪k x, k y⟫_𝕜) := by
  refine ⟨fun x y => (inner_conj_symm (k y) (k x)).symm, fun c => ?_⟩
  refine ⟨‖c.sum (fun x a => a • k x)‖ ^ 2, sq_nonneg _, ?_⟩
  rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K (𝕜 := 𝕜)]
  simp only [Finsupp.sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

lemma native_kernel_apply_one {𝕜 : Type u} {X : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [RKHS 𝕜 H X 𝕜] (x y : X) :
    RKHS.kernel H x y 1 = ⟪RKHS.kerFun H x 1, RKHS.kerFun H y 1⟫_𝕜 := by
  simp only [RKHS.kerFun_inner, RCLike.inner_apply, map_one, mul_one, RKHS.kerFun_apply]

theorem evaluation_representation : Spec.EvaluationRepresentation.{u, v, w} := by
  intro 𝕜 X H _ _ _ _ F
  let := toRKHS F
  let k : X → H := fun x => RKHS.kerFun H x 1
  have hk : Reproduces F k := by
    intro f x
    exact native_reproduces f x
  refine ⟨k, hk, ?_, gram_positive k⟩
  intro l hl
  funext x
  apply ext_inner_right 𝕜
  intro f
  exact (hl f x).symm.trans (hk f x)

theorem kernel_existence : Spec.KernelExistence.{u, v} := by
  intro 𝕜 X _ K hK
  let L := scalarOperators K
  let : Fact L.PosSemidef := ⟨scalarOperators_posSemidef K hK⟩
  let H := RKHS.OfKernel L
  refine ⟨H, inferInstance, inferInstance, inferInstance, functionSpace,
    (fun x => RKHS.kerFun H x 1), native_reproduces, ?_⟩
  intro x y
  rw [← native_kernel_apply_one, RKHS.OfKernel.kernel_ofKernel]
  simp [L, scalarOperators]

lemma kerFun_eq_of_reproduces {𝕜 : Type u} {X : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (F : FunctionSpace 𝕜 X H) (k : X → H) (hk : Reproduces F k) (x : X) :
    let := toRKHS F
    RKHS.kerFun H x 1 = k x := by
  let := toRKHS F
  apply ext_inner_right 𝕜
  intro f
  exact (native_reproduces f x).symm.trans (hk f x)

theorem kernel_uniqueness : Spec.KernelUniqueness.{u, v, w, w'} := by
  intro 𝕜 X H G _ _ _ _ _ _ _ F D k l hk hl heq
  let := toRKHS F
  let := toRKHS D
  have hnative : RKHS.kernel H = RKHS.kernel G := by
    ext x y
    rw [native_kernel_apply_one, native_kernel_apply_one,
      kerFun_eq_of_reproduces F k hk, kerFun_eq_of_reproduces F k hk,
      kerFun_eq_of_reproduces D l hl, kerFun_eq_of_reproduces D l hl, heq]
  refine ⟨RKHS.equiv hnative, ?_⟩
  intro f x
  exact congrFun (RKHS.coe_equiv hnative f) x

theorem finite_gram : Spec.FiniteGram.{u, v} := by
  intro 𝕜 X _ K hK n x c
  rcases kernel_existence 𝕜 X K hK with ⟨H, ng, ip, cp, F, k, hk, hkernel⟩
  let := ng
  let := ip
  let := cp
  refine ⟨‖∑ i, c i • k (x i)‖ ^ 2, sq_nonneg _, ?_⟩
  simp_rw [← hkernel]
  rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K (𝕜 := 𝕜)]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finite_kernel_characterization : Spec.FiniteKernelCharacterization.{u, v} := by
  intro 𝕜 X _ K
  constructor
  · intro hK
    exact ⟨hK.1, finite_gram 𝕜 X K hK⟩
  · rintro ⟨hs, hp⟩
    refine ⟨hs, fun c => ?_⟩
    let e : Fin c.support.card ≃ c.support := c.support.equivFin.symm
    rcases hp c.support.card (fun i => (e i).val) (fun i => c (e i)) with ⟨r, hr, he⟩
    refine ⟨r, hr, ?_⟩
    have hsum : (∑ i : Fin c.support.card, ∑ j : Fin c.support.card,
        conj (c (e i)) * c (e j) * K (e i) (e j)) =
        (c.sum fun x a => c.sum fun y b => conj a * b * K x y) := by
      simp only [Finsupp.sum]
      simp_rw [← Finset.sum_coe_sort c.support]
      apply Fintype.sum_equiv e
      intro i
      exact Fintype.sum_equiv e _ _ (fun j => rfl)
    exact hsum.symm.trans he

end ExpandedFA.PartV.ReproducingKernels
