import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealAbelianComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OperatorTopology.Definitions

noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.VonNeumann.RealAbelianComplexification
open TraceIdeals.RealComplexification
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification (complexPair csmul ip)
universe u
abbrev operatorRealPart := @Spec.operatorRealPart
abbrev operatorImagPart := @Spec.operatorImagPart
abbrev gamma := @Spec.gamma
abbrev complexifiedSet := @Spec.complexifiedSet
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

@[simp] lemma operatorRealPart_apply (R : Space H →L[ℂ] Space H) (x : H) :
    operatorRealPart R x = (R (inclusion x)).1 := rfl

@[simp] lemma operatorImagPart_apply (R : Space H →L[ℂ] Space H) (x : H) :
    operatorImagPart R x = (R (inclusion x)).2 := rfl

lemma assemble_inclusion (S T : H →L[ℝ] H) (x : H) :
    (operator S + Complex.I • operator T) (inclusion x) = complexPair H (S x) (T x) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    operator_inclusion]
  rw [csmul]
  change (S x + (Complex.I.re • T x - Complex.I.im • (0 : H)),
    (0 : H) + (Complex.I.im • T x + Complex.I.re • (0 : H))) = (S x, T x)
  simp

@[simp] lemma realPart_assemble (S T : H →L[ℝ] H) :
    operatorRealPart (operator S + Complex.I • operator T) = S := by
  ext x
  exact congrArg Prod.fst (assemble_inclusion S T x)

@[simp] lemma imagPart_assemble (S T : H →L[ℝ] H) :
    operatorImagPart (operator S + Complex.I • operator T) = T := by
  ext x
  exact congrArg Prod.snd (assemble_inclusion S T x)

lemma operator_decompose (R : Space H →L[ℂ] Space H) :
    R = operator (operatorRealPart R) + Complex.I • operator (operatorImagPart R) := by
  have h : ∀ x : H, R (inclusion x) =
      (operator (operatorRealPart R) + Complex.I • operator (operatorImagPart R))
        (inclusion x) := by
    intro x
    rw [assemble_inclusion]
    rfl
  ext p
  rw [decomposition p]
  simp only [map_add, map_smul, h]

lemma assemble_unique (R : Space H →L[ℂ] Space H) (S T : H →L[ℝ] H) :
    R = operator S + Complex.I • operator T ↔
      operatorRealPart R = S ∧ operatorImagPart R = T := by
  constructor
  · rintro rfl
    exact ⟨realPart_assemble S T, imagPart_assemble S T⟩
  · rintro ⟨hS, hT⟩
    simpa only [hS, hT] using operator_decompose R

theorem operator_decomposition : Spec.OperatorDecomposition.{u} := by
  intro H _ _ R
  exact ⟨operator_decompose R, assemble_unique R⟩

lemma operator_injective : Function.Injective (operator (H := H) (K := H)) := by
  intro S T h
  ext x
  exact congrArg (fun R : Space H →L[ℂ] Space H => (R (inclusion x)).1) h

@[simp] lemma realPart_operator (T : H →L[ℝ] H) : operatorRealPart (operator T) = T := by
  ext x
  rfl

@[simp] lemma imagPart_operator (T : H →L[ℝ] H) : operatorImagPart (operator T) = 0 := by
  ext x
  change T 0 = 0
  simp

@[simp] lemma operator_zero : operator (0 : H →L[ℝ] H) = 0 := by
  ext p
  change ((0 : H), 0) = (0, 0)
  rfl

lemma conjugation_involutive (p : Space H) : conjugation (conjugation p) = p :=
  (coordinates H).2.2.1 p

lemma conjugation_smul (a : ℂ) (p : Space H) :
    conjugation (a • p) = star a • conjugation p := (coordinates H).2.2.2.1 a p

lemma gamma_inclusion (R : Space H →L[ℂ] Space H) (x : H) :
    gamma R (inclusion x) = conjugation (R (inclusion x)) := by
  change (operator (operatorRealPart R) - Complex.I • operator (operatorImagPart R))
    (inclusion x) = _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    operator_inclusion]
  rw [csmul, conjugation_apply]
  change ((R (complexPair H x 0)).1 -
      (Complex.I.re • (R (complexPair H x 0)).2 - Complex.I.im • (0 : H)),
    (0 : H) - (Complex.I.im • (R (complexPair H x 0)).2 +
      Complex.I.re • (0 : H))) = _
  simp [complexPair]

lemma gamma_apply (R : Space H →L[ℂ] Space H) (p : Space H) :
    gamma R p = conjugation (R (conjugation p)) := by
  have hp := decomposition p
  rw [hp]
  simp only [map_add, map_smul, conjugation_smul, gamma_inclusion]
  simp only [conjugation_involutive, conjugation_smul, map_add, map_smul,
    star_star]
  have hx (x : H) : conjugation (inclusion x) = inclusion x := by
    change (x, -(0 : H)) = (x, 0)
    simp
  simp only [hx]

@[simp] lemma gamma_gamma (R : Space H →L[ℂ] Space H) : gamma (gamma R) = R := by
  ext p
  simp only [gamma_apply, conjugation_involutive]

@[simp] lemma gamma_add (R S : Space H →L[ℂ] Space H) :
    gamma (R + S) = gamma R + gamma S := by
  ext p
  simp only [gamma_apply, ContinuousLinearMap.add_apply, map_add]

@[simp] lemma gamma_smul (a : ℂ) (R : Space H →L[ℂ] Space H) :
    gamma (a • R) = star a • gamma R := by
  ext p
  simp only [gamma_apply, ContinuousLinearMap.smul_apply, conjugation_smul]

@[simp] lemma gamma_mul (R S : Space H →L[ℂ] Space H) :
    gamma (R * S) = gamma R * gamma S := by
  ext p
  simp only [gamma_apply, ContinuousLinearMap.mul_apply, conjugation_involutive]

@[simp] lemma gamma_one : gamma (1 : Space H →L[ℂ] Space H) = 1 := by
  ext p
  simp only [gamma_apply, ContinuousLinearMap.one_apply, conjugation_involutive]

theorem conjugation_laws : Spec.ConjugationLaws.{u} := by
  intro H _ _
  exact ⟨gamma_apply, gamma_gamma, gamma_add, gamma_smul, gamma_mul, gamma_one⟩

@[simp] lemma gamma_operator (T : H →L[ℝ] H) : gamma (operator T) = operator T := by
  ext p
  rw [gamma_apply]
  simp only [operator_apply, conjugation_apply]
  change (T p.1, -(T (-p.2))) = (T p.1, T p.2)
  simp

lemma fixed_iff (R : Space H →L[ℂ] Space H) :
    gamma R = R ↔ ∃! T : H →L[ℝ] H, R = operator T := by
  constructor
  · intro h
    have hi : operatorImagPart R = 0 := by
      ext x
      have hx := congrArg (fun Q : Space H →L[ℂ] Space H => (Q (inclusion x)).2) h
      rw [gamma_inclusion] at hx
      change -(R (inclusion x)).2 = (R (inclusion x)).2 at hx
      change (R (inclusion x)).2 = 0
      have hz : (2 : ℝ) • (R (inclusion x)).2 = 0 := by
        rw [two_smul]
        exact add_eq_zero_iff_eq_neg.mpr hx.symm
      exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
    refine ⟨operatorRealPart R, ?_, ?_⟩
    · calc R = operator (operatorRealPart R) + Complex.I • operator (operatorImagPart R) :=
              operator_decompose R
           _ = operator (operatorRealPart R) := by
             rw [hi, operator_zero]
             ext p
             simp only [add_apply, smul_apply, zero_apply, smul_zero, add_zero]
    · intro T hT
      simpa only [realPart_operator] using (congrArg operatorRealPart hT).symm
  · rintro ⟨T, rfl, _⟩
    exact gamma_operator T

theorem fixed_operators : Spec.FixedOperators.{u} := by
  intro H _ _ R
  exact fixed_iff R

lemma inner_conjugation (p q : Space H) :
    inner ℂ (conjugation p) (conjugation q) = star (inner ℂ p q) := by
  change ip H (complexPair H p.1 (-p.2)) (complexPair H q.1 (-q.2)) = star (ip H p q)
  apply Complex.ext <;> simp [ip, complexPair, sub_eq_add_neg, add_comm]

lemma inner_conjugation_left (p q : Space H) :
    inner ℂ (conjugation p) q = star (inner ℂ p (conjugation q)) := by
  simpa only [conjugation_involutive] using inner_conjugation p (conjugation q)

lemma gamma_star [CompleteSpace H] (R : Space H →L[ℂ] Space H) :
    gamma (star R) = star (gamma R) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro p q
  rw [gamma_apply, inner_conjugation_left]
  change star (inner ℂ (R.adjoint (conjugation p)) (conjugation q)) = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [gamma_apply]
  simpa only [conjugation_involutive] using
    (inner_conjugation (conjugation p) (R (conjugation q))).symm

theorem conjugation_star : Spec.ConjugationStar.{u} := by
  intro H _ _ _ R
  exact gamma_star R


theorem separability : Spec.Separability.{u} := by
  intro H _ _ _
  let e := Hilbert.PreHilbertCompactSpectral.Complexification.pairEquiv H
  exact e.symm.surjective.denseRange.separableSpace e.symm.continuous

lemma strong_extension_iff {ι : Type*} (l : Filter ι)
    (f : ι → H →L[ℝ] H) (T : H →L[ℝ] H) :
    Filter.Tendsto f l (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℝ H H) T) ↔
    Filter.Tendsto (fun i => operator (f i)) l
      (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)) (operator T)) := by
  rw [OperatorTopology.strong_tendsto_iff ℝ H H,
    OperatorTopology.strong_tendsto_iff ℂ (Space H) (Space H)]
  constructor
  · intro hf p
    let e := Hilbert.PreHilbertCompactSpectral.Complexification.pairEquiv H
    exact (e.symm.continuous.tendsto (T p.1, T p.2)).comp
      ((hf p.1).prodMk_nhds (hf p.2))
  · intro hf x
    exact (realPart.continuous.tendsto (operator T (inclusion x))).comp (hf (inclusion x))

theorem strong_extension : Spec.StrongExtension.{u} := by
  intro H _ _ ι l f T
  exact strong_extension_iff l f T

lemma weak_extension_iff [CompleteSpace H] {ι : Type*} (l : Filter ι)
    (f : ι → H →L[ℝ] H) (T : H →L[ℝ] H) :
    Filter.Tendsto f l (@nhds _ (OperatorTopology.Spec.WeakTopologyValue ℝ H H) T) ↔
    Filter.Tendsto (fun i => operator (f i)) l
      (@nhds _ (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H)) (operator T)) := by
  rw [OperatorTopology.hilbert_tendsto_iff ℝ H H,
    OperatorTopology.hilbert_tendsto_iff ℂ (Space H) (Space H)]
  constructor
  · intro hf p q
    have hre := (hf p.1 q.1).add (hf p.2 q.2)
    have him := (hf p.2 q.1).sub (hf p.1 q.2)
    have hc := (Complex.continuous_ofReal.tendsto _).comp hre
    have hd := ((Complex.continuous_ofReal.tendsto _).comp him).const_mul Complex.I
    have hformula (S : H →L[ℝ] H) : inner ℂ q (operator S p) =
        ((inner ℝ q.1 (S p.1) + inner ℝ q.2 (S p.2) : ℝ) : ℂ) +
          Complex.I * ((inner ℝ q.1 (S p.2) - inner ℝ q.2 (S p.1) : ℝ) : ℂ) := by
      change ip H q (complexPair H (S p.1) (S p.2)) = _
      apply Complex.ext <;> simp [ip, complexPair]
    simpa only [Function.comp_def, hformula] using hc.add hd
  · intro hf x y
    have hr := (Complex.continuous_re.tendsto _).comp (hf (inclusion x) (inclusion y))
    simpa only [Function.comp_def, operator_inclusion, inner_inclusion, Complex.ofReal_re] using hr

theorem weak_extension : Spec.WeakExtension.{u} := by
  intro H _ _ _ ι l f T
  exact weak_extension_iff l f T

lemma strong_realPart_continuous :
    @Continuous _ _
      (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.StrongTopologyValue ℝ H H) operatorRealPart := by
  letI := OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  exact realPart.continuous.comp ((continuous_apply (inclusion x)).comp continuous_induced_dom)

lemma strong_imagPart_continuous :
    @Continuous _ _
      (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.StrongTopologyValue ℝ H H) operatorImagPart := by
  letI := OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  exact imagPart.continuous.comp ((continuous_apply (inclusion x)).comp continuous_induced_dom)

lemma weak_realPart_continuous [CompleteSpace H] :
    @Continuous _ _
      (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.WeakTopologyValue ℝ H H) operatorRealPart := by
  rw [OperatorTopology.hilbert_weak_eq_coefficients ℝ H H,
    OperatorTopology.hilbert_weak_eq_coefficients ℂ (Space H) (Space H)]
  letI := OperatorTopology.Spec.HilbertCoefficientTopologyValue ℂ (Space H) (Space H)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  rintro ⟨x, y⟩
  have hc : Continuous (fun R : Space H →L[ℂ] Space H =>
      inner ℂ (inclusion y) (R (inclusion x))) :=
    by
      have hind : Continuous (fun R : Space H →L[ℂ] Space H =>
          fun p : Space H × Space H => inner ℂ p.2 (R p.1)) := continuous_induced_dom
      exact (continuous_apply (inclusion x, inclusion y)).comp hind
  have h := Complex.continuous_re.comp hc
  simpa only [Function.comp_def, inner_inclusion_left, operatorRealPart_apply, operatorImagPart_apply] using h

lemma weak_imagPart_continuous [CompleteSpace H] :
    @Continuous _ _
      (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H))
      (OperatorTopology.Spec.WeakTopologyValue ℝ H H) operatorImagPart := by
  rw [OperatorTopology.hilbert_weak_eq_coefficients ℝ H H,
    OperatorTopology.hilbert_weak_eq_coefficients ℂ (Space H) (Space H)]
  letI := OperatorTopology.Spec.HilbertCoefficientTopologyValue ℂ (Space H) (Space H)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  rintro ⟨x, y⟩
  have hc : Continuous (fun R : Space H →L[ℂ] Space H =>
      inner ℂ (inclusion y) (R (inclusion x))) :=
    by
      have hind : Continuous (fun R : Space H →L[ℂ] Space H =>
          fun p : Space H × Space H => inner ℂ p.2 (R p.1)) := continuous_induced_dom
      exact (continuous_apply (inclusion x, inclusion y)).comp hind
  have h := Complex.continuous_im.comp hc
  simpa only [Function.comp_def, inner_inclusion_left, operatorRealPart_apply, operatorImagPart_apply] using h

theorem extraction_continuous : Spec.ExtractionContinuous.{u} := by
  intro H _ _ _
  exact ⟨strong_realPart_continuous, strong_imagPart_continuous,
    weak_realPart_continuous, weak_imagPart_continuous⟩


abbrev complexAlgebra := @Spec.complexAlgebra
abbrev complexSpanSet := @Spec.complexSpanSet

lemma map_coordinates (R : Space H →L[ℂ] Space H) (p : Space H) :
    R p = complexPair H
      (operatorRealPart R p.1 - operatorImagPart R p.2)
      (operatorImagPart R p.1 + operatorRealPart R p.2) := by
  conv_lhs => rw [decomposition p, map_add, map_smul, csmul]
  change ((R (inclusion p.1)).1 +
    (Complex.I.re • (R (inclusion p.2)).1 - Complex.I.im • (R (inclusion p.2)).2),
    (R (inclusion p.1)).2 +
    (Complex.I.im • (R (inclusion p.2)).1 + Complex.I.re • (R (inclusion p.2)).2)) = _
  simp only [Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_sub, add_zero]
  simp only [operatorRealPart_apply, operatorImagPart_apply, sub_eq_add_neg, complexPair]

@[simp] lemma realPart_add (R S : Space H →L[ℂ] Space H) :
    operatorRealPart (R + S) = operatorRealPart R + operatorRealPart S := rfl

@[simp] lemma imagPart_add (R S : Space H →L[ℂ] Space H) :
    operatorImagPart (R + S) = operatorImagPart R + operatorImagPart S := rfl

lemma realPart_smul (a : ℂ) (R : Space H →L[ℂ] Space H) :
    operatorRealPart (a • R) = a.re • operatorRealPart R - a.im • operatorImagPart R := by
  ext x
  exact congrArg Prod.fst (csmul H a (R (inclusion x)))

lemma imagPart_smul (a : ℂ) (R : Space H →L[ℂ] Space H) :
    operatorImagPart (a • R) = a.im • operatorRealPart R + a.re • operatorImagPart R := by
  ext x
  exact congrArg Prod.snd (csmul H a (R (inclusion x)))

lemma realPart_mul (R S : Space H →L[ℂ] Space H) :
    operatorRealPart (R * S) =
      operatorRealPart R * operatorRealPart S - operatorImagPart R * operatorImagPart S := by
  ext x
  exact congrArg Prod.fst (map_coordinates R (S (inclusion x)))

lemma imagPart_mul (R S : Space H →L[ℂ] Space H) :
    operatorImagPart (R * S) =
      operatorImagPart R * operatorRealPart S + operatorRealPart R * operatorImagPart S := by
  ext x
  exact congrArg Prod.snd (map_coordinates R (S (inclusion x)))

@[simp] lemma operator_neg (T : H →L[ℝ] H) : operator (-T) = -operator T := by
  ext p
  rfl

@[simp] lemma operator_star [CompleteSpace H] (T : H →L[ℝ] H) :
    star (operator T) = operator (star T) := operator_adjoint T

lemma neg_smul_operator (a : ℂ) (R : Space H →L[ℂ] Space H) :
    (-a) • R = a • (-R) := by
  ext p
  change (-a) • (R p) = a • (-(R p))
  exact (neg_smul a (R p)).trans (smul_neg a (R p)).symm

lemma star_coordinates [CompleteSpace H] (R : Space H →L[ℂ] Space H) :
    operatorRealPart (star R) = star (operatorRealPart R) ∧
    operatorImagPart (star R) = -star (operatorImagPart R) := by
  apply (assemble_unique _ _ _).mp
  conv_lhs => rw [operator_decompose R]
  rw [star_add, star_smul, operator_star, operator_star, operator_neg]
  simp only [Complex.star_def, Complex.conj_I]
  rw [neg_smul_operator]

@[simp] lemma realPart_zero : operatorRealPart (0 : Space H →L[ℂ] Space H) = 0 := rfl
@[simp] lemma imagPart_zero : operatorImagPart (0 : Space H →L[ℂ] Space H) = 0 := rfl
@[simp] lemma realPart_one : operatorRealPart (1 : Space H →L[ℂ] Space H) = 1 := rfl
@[simp] lemma imagPart_one : operatorImagPart (1 : Space H →L[ℂ] Space H) = 0 := rfl

private def coordinateAlgebra [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)) :
    StarSubalgebra ℂ (Space H →L[ℂ] Space H) where
  carrier := {R | operatorRealPart R ∈ A ∧ operatorImagPart R ∈ A}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro R S ⟨hr, hi⟩ ⟨hs, hj⟩
    exact ⟨by rw [realPart_add]; exact A.add_mem hr hs,
      by rw [imagPart_add]; exact A.add_mem hi hj⟩
  mul_mem' := by
    rintro R S ⟨hr, hi⟩ ⟨hs, hj⟩
    exact ⟨by rw [realPart_mul]; exact A.sub_mem (A.mul_mem hr hs) (A.mul_mem hi hj),
      by rw [imagPart_mul]; exact A.add_mem (A.mul_mem hi hs) (A.mul_mem hr hj)⟩
  algebraMap_mem' a := by
    change operatorRealPart (a • (1 : Space H →L[ℂ] Space H)) ∈ A ∧
      operatorImagPart (a • (1 : Space H →L[ℂ] Space H)) ∈ A
    rw [realPart_smul, imagPart_smul, realPart_one, imagPart_one]
    simp only [smul_zero, sub_zero, add_zero]
    exact ⟨A.smul_mem A.one_mem _, A.smul_mem A.one_mem _⟩
  star_mem' := by
    rintro R ⟨hr, hi⟩
    change operatorRealPart (star R) ∈ A ∧ operatorImagPart (star R) ∈ A
    rw [(star_coordinates R).1, (star_coordinates R).2]
    have hs : star (operatorImagPart R) ∈ A := star_mem hi
    exact ⟨star_mem hr, A.neg_mem hs⟩

lemma mem_complexAlgebra [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H))
    (R : Space H →L[ℂ] Space H) :
    R ∈ complexAlgebra A ↔ operatorRealPart R ∈ A ∧ operatorImagPart R ∈ A := by
  constructor
  · intro hR
    apply (StarAlgebra.adjoin_le (S := coordinateAlgebra A) ?_) hR
    rintro _ ⟨T, hT, rfl⟩
    change operatorRealPart (operator T) ∈ A ∧ operatorImagPart (operator T) ∈ A
    simp only [realPart_operator, imagPart_operator]
    exact ⟨hT, A.zero_mem⟩
  · rintro ⟨hr, hi⟩
    rw [operator_decompose R]
    exact (complexAlgebra A).add_mem
      (StarAlgebra.subset_adjoin ℂ _ ⟨_, hr, rfl⟩)
      ((complexAlgebra A).smul_mem (StarAlgebra.subset_adjoin ℂ _ ⟨_, hi, rfl⟩) _)

lemma complexAlgebra_carrier [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)) :
    (complexAlgebra A : Set (Space H →L[ℂ] Space H)) = complexifiedSet A := by
  ext R
  change R ∈ complexAlgebra A ↔ R ∈ complexifiedSet A
  rw [mem_complexAlgebra]
  constructor
  · rintro ⟨hr, hi⟩
    exact ⟨_, hr, _, hi, operator_decompose R⟩
  · rintro ⟨S, hS, T, hT, hR⟩
    rcases (assemble_unique R S T).mp hR with ⟨rfl, rfl⟩
    exact ⟨hS, hT⟩

theorem algebra_carrier : Spec.AlgebraCarrier.{u} := by
  intro H _ _ _ A
  exact complexAlgebra_carrier A

lemma gamma_assemble (S T : H →L[ℝ] H) :
    gamma (operator S + Complex.I • operator T) = operator S + Complex.I • operator (-T) := by
  rw [gamma_add, gamma_smul, gamma_operator, gamma_operator, operator_neg]
  simp only [Complex.star_def, Complex.conj_I]
  rw [neg_smul_operator]

theorem algebra_fixed_points : Spec.AlgebraFixedPoints.{u} := by
  intro H _ _ _ A
  constructor
  · intro R hR
    change R ∈ (complexAlgebra A : Set (Space H →L[ℂ] Space H)) at hR
    change gamma R ∈ (complexAlgebra A : Set (Space H →L[ℂ] Space H))
    rw [complexAlgebra_carrier] at hR ⊢
    rcases hR with ⟨S, hS, T, hT, rfl⟩
    exact ⟨S, hS, -T, A.neg_mem hT, gamma_assemble S T⟩
  · intro R
    constructor
    · rintro ⟨hR, hfix⟩
      rcases (fixed_iff R).mp hfix with ⟨T, hT, _⟩
      refine ⟨T, ?_, hT⟩
      simpa only [hT, realPart_operator] using ((mem_complexAlgebra A R).mp hR).1
    · rintro ⟨T, hT, rfl⟩
      exact ⟨(mem_complexAlgebra A _).mpr ⟨realPart_operator T ▸ hT,
        by simp only [imagPart_operator]; exact A.zero_mem⟩, gamma_operator T⟩


lemma operator_eq_iff (R S : Space H →L[ℂ] Space H) :
    R = S ↔ operatorRealPart R = operatorRealPart S ∧
      operatorImagPart R = operatorImagPart S := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hr, hi⟩
    calc R = operator (operatorRealPart R) + Complex.I • operator (operatorImagPart R) :=
          operator_decompose R
         _ = operator (operatorRealPart S) + Complex.I • operator (operatorImagPart S) := by
          rw [hr, hi]
         _ = S := (operator_decompose S).symm

lemma mem_complexSpanSet_iff (s : Set (H →L[ℝ] H)) (R : Space H →L[ℂ] Space H) :
    R ∈ complexSpanSet s ↔ operatorRealPart R ∈ s ∧ operatorImagPart R ∈ s := by
  constructor
  · rintro ⟨S, hS, T, hT, hR⟩
    rcases (assemble_unique R S T).mp hR with ⟨rfl, rfl⟩
    exact ⟨hS, hT⟩
  · rintro ⟨hr, hi⟩
    exact ⟨_, hr, _, hi, operator_decompose R⟩

lemma commutes_extension_iff (T : H →L[ℝ] H) (R : Space H →L[ℂ] Space H) :
    operator T * R = R * operator T ↔
      T * operatorRealPart R = operatorRealPart R * T ∧
      T * operatorImagPart R = operatorImagPart R * T := by
  rw [operator_eq_iff]
  simp only [realPart_mul, imagPart_mul, realPart_operator, imagPart_operator,
    zero_mul, mul_zero, sub_zero, zero_add, add_zero]

lemma smul_mul_operator (a : ℂ) (R S : Space H →L[ℂ] Space H) :
    (a • R) * S = a • (R * S) := by ext p; rfl

lemma mul_smul_operator (a : ℂ) (R S : Space H →L[ℂ] Space H) :
    R * (a • S) = a • (R * S) := by
  ext p
  exact R.map_smul a (S p)

lemma centralizer_complexSpanSet (s : Set (H →L[ℝ] H)) :
    Set.centralizer (complexSpanSet s) = complexSpanSet (Set.centralizer s) := by
  ext R
  rw [mem_complexSpanSet_iff]
  simp only [Set.mem_centralizer_iff]
  constructor
  · intro h
    have hcomm (T : H →L[ℝ] H) (hT : T ∈ s) : operator T * R = R * operator T := by
      have hh := h (operator T + Complex.I • operator T) ⟨T, hT, T, hT, rfl⟩
      have hform : operator T + Complex.I • operator T =
          (1 + Complex.I) • operator T := by
        ext p
        change operator T p + Complex.I • operator T p = (1 + Complex.I) • operator T p
        simpa only [one_smul] using (add_smul (1 : ℂ) Complex.I (operator T p)).symm
      rw [hform, smul_mul_operator, mul_smul_operator] at hh
      have hn : (1 + Complex.I : ℂ) ≠ 0 := by
        intro hz
        have := congrArg Complex.re hz
        norm_num at this
      ext p
      have hp := congrArg (fun Q : Space H →L[ℂ] Space H => Q p) hh
      exact (smul_right_inj hn).mp hp
    exact ⟨fun T hT => ((commutes_extension_iff T R).mp (hcomm T hT)).1,
      fun T hT => ((commutes_extension_iff T R).mp (hcomm T hT)).2⟩
  · rintro ⟨hr, hi⟩ Q ⟨S, hS, T, hT, rfl⟩
    have hs := (commutes_extension_iff S R).mpr ⟨hr S hS, hi S hS⟩
    have ht := (commutes_extension_iff T R).mpr ⟨hr T hT, hi T hT⟩
    simp only [add_mul, mul_add, smul_mul_operator, mul_smul_operator, hs, ht]

theorem commutants : Spec.Commutants.{u} := by
  intro H _ _ s
  refine ⟨centralizer_complexSpanSet s, ?_⟩
  rw [centralizer_complexSpanSet, centralizer_complexSpanSet]

@[simp] lemma operator_mul (S T : H →L[ℝ] H) :
    operator (S * T) = operator S * operator T := rfl

@[simp] lemma operator_one : operator (1 : H →L[ℝ] H) = 1 := rfl

lemma generated_algebra [CompleteSpace H] (N : H →L[ℝ] H) :
    complexAlgebra (StarAlgebra.adjoin ℝ {N}) = StarAlgebra.adjoin ℂ {operator N} := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨T, hT, rfl⟩
    induction hT using StarAlgebra.adjoin_induction with
    | mem T hT =>
      have ht : T = N := Set.mem_singleton_iff.mp hT
      subst T
      exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _)
    | algebraMap r =>
      change operator (algebraMap ℝ (H →L[ℝ] H) r) ∈ StarAlgebra.adjoin ℂ {operator N}
      have hr : operator (algebraMap ℝ (H →L[ℝ] H) r) =
          algebraMap ℂ (Space H →L[ℂ] Space H) (r : ℂ) := by
        change operator (r • (1 : H →L[ℝ] H)) = (r : ℂ) • 1
        rw [operator_real_smul, operator_one]
      rw [hr]
      exact StarSubalgebra.algebraMap_mem _ _
    | add S T _ _ hS hT =>
      change operator (S + T) ∈ StarAlgebra.adjoin ℂ {operator N}
      rw [operator_add]
      exact add_mem hS hT
    | mul S T _ _ hS hT =>
      change operator (S * T) ∈ StarAlgebra.adjoin ℂ {operator N}
      rw [operator_mul]
      exact mul_mem hS hT
    | star S _ hS =>
      change operator (star S) ∈ StarAlgebra.adjoin ℂ {operator N}
      rw [← operator_star]
      exact star_mem hS
  · apply StarAlgebra.adjoin_le
    rintro _ (rfl : _ = operator N)
    exact (mem_complexAlgebra _ _).mpr ⟨by simp [StarAlgebra.subset_adjoin ℝ _ (Set.mem_singleton N)],
      by simp⟩

theorem generated_double_commutants : Spec.GeneratedDoubleCommutants.{u} := by
  intro H _ _ _ N
  have hc : complexSpanSet (StarAlgebra.adjoin ℝ {N} : Set (H →L[ℝ] H)) =
      (StarAlgebra.adjoin ℂ {operator N} : Set (Space H →L[ℂ] Space H)) := by
    rw [← generated_algebra N, complexAlgebra_carrier]
    rfl
  change complexSpanSet (Set.centralizer (Set.centralizer
    (StarAlgebra.adjoin ℝ {N} : Set (H →L[ℝ] H)))) = _
  rw [← centralizer_complexSpanSet, ← centralizer_complexSpanSet, hc]


lemma strong_operator_continuous :
    @Continuous _ _ (OperatorTopology.Spec.StrongTopologyValue ℝ H H)
      (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)) operator := by
  letI := OperatorTopology.Spec.StrongTopologyValue ℝ H H
  letI := OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H)
  apply continuous_iff_continuousAt.mpr
  intro T
  exact (strong_extension_iff
    (@nhds _ (OperatorTopology.Spec.StrongTopologyValue ℝ H H) T) id T).mp Filter.tendsto_id

lemma weak_operator_continuous [CompleteSpace H] :
    @Continuous _ _ (OperatorTopology.Spec.WeakTopologyValue ℝ H H)
      (OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H)) operator := by
  letI := OperatorTopology.Spec.WeakTopologyValue ℝ H H
  letI := OperatorTopology.Spec.WeakTopologyValue ℂ (Space H) (Space H)
  apply continuous_iff_continuousAt.mpr
  intro T
  exact (weak_extension_iff
    (@nhds _ (OperatorTopology.Spec.WeakTopologyValue ℝ H H) T) id T).mp Filter.tendsto_id

lemma closed_algebra_iff [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H))
    (tR : TopologicalSpace (H →L[ℝ] H))
    (tC : TopologicalSpace (Space H →L[ℂ] Space H))
    (hr : @Continuous _ _ tC tR operatorRealPart)
    (hi : @Continuous _ _ tC tR operatorImagPart)
    (he : @Continuous _ _ tR tC operator) :
    @IsClosed _ tR (A : Set _) ↔ @IsClosed _ tC (complexAlgebra A : Set _) := by
  letI := tR
  letI := tC
  constructor
  · intro h
    have hh := (h.preimage hr).inter (h.preimage hi)
    have hs : (complexAlgebra A : Set (Space H →L[ℂ] Space H)) =
        operatorRealPart ⁻¹' (A : Set _) ∩ operatorImagPart ⁻¹' (A : Set _) := by
      ext R
      exact mem_complexAlgebra A R
    rw [hs]
    exact hh
  · intro h
    have hh := h.preimage he
    have hs : operator ⁻¹' (complexAlgebra A : Set (Space H →L[ℂ] Space H)) =
        (A : Set (H →L[ℝ] H)) := by
      ext T
      change operator T ∈ complexAlgebra A ↔ T ∈ A
      simp only [mem_complexAlgebra, realPart_operator, imagPart_operator]
      exact and_iff_left A.zero_mem
    rw [hs] at hh
    exact hh

theorem closed_algebras : Spec.ClosedAlgebras.{u} := by
  intro H _ _ _ A
  exact ⟨closed_algebra_iff A _ _ weak_realPart_continuous weak_imagPart_continuous
    weak_operator_continuous,
    closed_algebra_iff A _ _ strong_realPart_continuous strong_imagPart_continuous
      strong_operator_continuous⟩

lemma cyclic_transport [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)) (e : H)
    (he : SeparableMASA.Spec.RealIsCyclic A e) :
    SeparableMASA.Spec.IsCyclic (complexAlgebra A) (inclusion e) := by
  let d := Hilbert.PreHilbertCompactSpectral.Complexification.pairEquiv H
  have hd : DenseRange (fun p : A × A => complexPair H (p.1.val e) (p.2.val e)) :=
    d.symm.surjective.denseRange.comp (he.prodMap he) d.symm.continuous
  apply hd.mono
  rintro _ ⟨⟨S, T⟩, rfl⟩
  have hmem : operator S.val + Complex.I • operator T.val ∈ complexAlgebra A :=
    (mem_complexAlgebra A _).mpr (by simpa only [realPart_assemble, imagPart_assemble] using
      (And.intro S.property T.property))
  exact ⟨⟨_, hmem⟩, assemble_inclusion S.val T.val e⟩

lemma separating_transport [CompleteSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)) (e : H)
    (he : SeparableMASA.Spec.RealIsSeparating A e) :
    SeparableMASA.Spec.IsSeparating (complexAlgebra A) (inclusion e) := by
  intro R hR hzero
  have hm := (mem_complexAlgebra A R).mp hR
  have hr : operatorRealPart R e = 0 := congrArg Prod.fst hzero
  have hi : operatorImagPart R e = 0 := congrArg Prod.snd hzero
  have hreal := he _ hm.1 hr
  have himag := he _ hm.2 hi
  apply (operator_eq_iff R 0).mpr
  exact ⟨hreal, himag⟩

theorem cyclic_separating_transport : Spec.CyclicSeparatingTransport.{u} := by
  intro H _ _ _ A e
  exact ⟨cyclic_transport A e, separating_transport A e⟩


lemma normal_mem_of_real_maximal [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)) (hA : SeparableMASA.Spec.RealIsMaximalAbelian A)
    (T : H →L[ℝ] H) (hn : IsStarNormal T)
    (hc : T ∈ Set.centralizer (A : Set (H →L[ℝ] H))) : T ∈ A := by
  let C := StarSubalgebra.centralizer ℝ (A : Set (H →L[ℝ] H))
  have hC (R : H →L[ℝ] H) : R ∈ C ↔ R ∈ Set.centralizer (A : Set (H →L[ℝ] H)) := by
    change R ∈ (C : Set (H →L[ℝ] H)) ↔ _
    simp only [C, StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]
  have hct : T ∈ C := (hC T).mpr hc
  have hctstar : star T ∈ C := star_mem hct
  have hstar := (hC (star T)).mp hctstar
  let s : Set (H →L[ℝ] H) := (A : Set (H →L[ℝ] H)) ∪ {T}
  have hnorm (x : H →L[ℝ] H) (hx : x ∈ s) : IsStarNormal x := by
    rcases hx with hx | hx
    · exact ⟨hA.1 _ (star_mem hx) _ hx⟩
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hn
  have hpair : s.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA.1 x hx y hy
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact hc x hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact (hc y hy).symm
    · rcases Set.mem_singleton_iff.mp hx with rfl
      rcases Set.mem_singleton_iff.mp hy with rfl
      rfl
  have hpairStar : s.Pairwise (fun x y => Commute x (star y)) := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA.1 x hx _ (star_mem hy)
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact hstar x hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact (hc _ (star_mem hy)).symm
    · rcases Set.mem_singleton_iff.mp hx with rfl
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hn.star_comm_self.symm
  let B := StarAlgebra.adjoin ℝ s
  letI : IsMulCommutative B := StarAlgebra.isMulCommutative_adjoin ℝ hnorm hpair hpairStar
  have hB : SeparableMASA.Spec.RealIsAbelian B := fun x hx y hy => setLike_mul_comm hx hy
  have hAB : A ≤ B := fun x hx => StarAlgebra.subset_adjoin ℝ s (Or.inl hx)
  have hBA := hA.2 B hB hAB
  rw [← hBA]
  exact StarAlgebra.subset_adjoin ℝ s (Or.inr (Set.mem_singleton T))

lemma real_maximal_commutant [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)) (hA : SeparableMASA.Spec.RealIsMaximalAbelian A) :
    Set.centralizer (A : Set (H →L[ℝ] H)) = (A : Set (H →L[ℝ] H)) := by
  ext T
  constructor
  · intro hc
    let C := StarSubalgebra.centralizer ℝ (A : Set (H →L[ℝ] H))
    have hC : (C : Set (H →L[ℝ] H)) = Set.centralizer (A : Set (H →L[ℝ] H)) := by
      simp only [C, StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]
    have hct : T ∈ C := by change T ∈ (C : Set _); rwa [hC]
    have hstar : star T ∈ C := star_mem hct
    let S := (1 / 2 : ℝ) • (T + star T)
    let U := (1 / 2 : ℝ) • (T - star T)
    have hS : IsSelfAdjoint S := by
      simp [S, IsSelfAdjoint, star_smul, add_comm]
    have hU : U ∈ skewAdjoint (H →L[ℝ] H) := by
      rw [skewAdjoint.mem_iff]
      dsimp [U]
      rw [star_smul, star_trivial, star_sub, star_star, ← smul_neg]
      congr 1
      abel
    have hSC : S ∈ Set.centralizer (A : Set (H →L[ℝ] H)) := by
      rw [← hC]
      exact C.smul_mem (C.add_mem hct hstar) _
    have hUC : U ∈ Set.centralizer (A : Set (H →L[ℝ] H)) := by
      rw [← hC]
      exact C.smul_mem (C.sub_mem hct hstar) _
    have hSA := normal_mem_of_real_maximal A hA S hS.isStarNormal hSC
    have hUA := normal_mem_of_real_maximal A hA U (skewAdjoint.isStarNormal_of_mem hU) hUC
    have heq : T = S + U := by
      dsimp [S, U]
      rw [← smul_add]
      have h : (T + star T) + (T - star T) = T + T := by abel
      rw [h, ← two_smul ℝ T, smul_smul]
      norm_num
    rw [heq]
    exact A.add_mem hSA hUA
  · intro hT S hS
    exact hA.1 S hS T hT

theorem masa_transport : Spec.MASATransport.{u} := by
  intro H _ _ _ A hA
  have hcomm : Set.centralizer (complexAlgebra A : Set (Space H →L[ℂ] Space H)) =
      (complexAlgebra A : Set (Space H →L[ℂ] Space H)) := by
    rw [complexAlgebra_carrier]
    change Set.centralizer (complexSpanSet (A : Set (H →L[ℝ] H))) = complexSpanSet (A : Set _)
    rw [centralizer_complexSpanSet, real_maximal_commutant A hA.1]
  have hab : SeparableMASA.Spec.IsAbelian (complexAlgebra A) := by
    intro R hR S hS
    have hc : S ∈ Set.centralizer (complexAlgebra A : Set (Space H →L[ℂ] Space H)) := by
      rwa [hcomm]
    exact hc R hR
  refine ⟨⟨hab, ?_⟩, (closed_algebras H A).1.mp hA.2⟩
  intro B hB hAB
  apply le_antisymm _ hAB
  intro R hR
  have hc : R ∈ Set.centralizer (complexAlgebra A : Set (Space H →L[ℂ] Space H)) :=
    fun S hS => hB S (hAB hS) R hR
  rwa [hcomm] at hc

end ExpandedFA.VonNeumann.RealAbelianComplexification



namespace ExpandedFA.VonNeumann.RealAbelianComplexification
open MeasureTheory
open scoped ENNReal
open Spec.NativeLp
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

theorem nativeLp_foundation : Spec.NativeLpFoundation.{u} := by
  intro X _ μ D p
  refine ⟨coeFn_conjugatePullback D, conjugatePullback_add D,
    conjugatePullback_smul D, norm_conjugatePullback D,
    conjugatePullback_involutive D, mem_fixedSubmodule_iff_ae D, ?_⟩
  intro hp
  exact ⟨fun _ ↦ rfl, isometry_conjugatePullback D, isClosed_fixedSubmodule D, inferInstance⟩

end ExpandedFA.VonNeumann.RealAbelianComplexification


namespace ExpandedFA.VonNeumann.RealAbelianComplexification
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexConjugate
universe u
abbrev lpConjugation := @Spec.NativeLp.conjugatePullback
abbrev lpFixedSubmodule := @Spec.NativeLp.fixedSubmodule
abbrev lpPairing := @Spec.NativeLp.pairing
namespace NativeLp
open Spec.NativeLp
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma integral_real_of_covariance (τ : X → X) (hm : MeasurePreserving τ μ μ)
    (hi : Function.Involutive τ) (f : X → ℂ)
    (hf : ∀ᵐ x ∂μ, f (τ x) = star (f x)) :
    (∫ x, f x ∂μ).im = 0 := by
  have he := (MeasurableEquiv.ofInvolutive τ hi hm.measurable).measurableEmbedding
  have hc : (∫ x, f x ∂μ) = star (∫ x, f x ∂μ) := by
    calc
      (∫ x, f x ∂μ) = ∫ x, f (τ x) ∂μ := (hm.integral_comp he f).symm
      _ = ∫ x, star (f x) ∂μ := integral_congr_ae hf
      _ = star (∫ x, f x ∂μ) := integral_conj
  have hh := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hh
  linarith

lemma pair_integral_real (τ : X → X) (hm : MeasurePreserving τ μ μ)
    (hi : Function.Involutive τ) {f g : X → ℂ}
    (hf : ∀ᵐ x ∂μ, f (τ x) = star (f x))
    (hg : ∀ᵐ x ∂μ, g (τ x) = star (g x)) :
    (∫ x, f x * g x ∂μ).im = 0 := by
  apply integral_real_of_covariance τ hm hi
  filter_upwards [hf, hg] with x hx hy
  simp [hx, hy, star_mul, mul_comm]

lemma inner_integral_real (τ : X → X) (hm : MeasurePreserving τ μ μ)
    (hi : Function.Involutive τ) {f g : X → ℂ}
    (hf : ∀ᵐ x ∂μ, f (τ x) = star (f x))
    (hg : ∀ᵐ x ∂μ, g (τ x) = star (g x)) :
    (∫ x, star (f x) * g x ∂μ).im = 0 := by
  apply integral_real_of_covariance τ hm hi
  filter_upwards [hf, hg] with x hx hy
  simp [hx, hy, star_mul, mul_comm]

lemma l2_inner_real_formula (f g : Lp ℂ 2 μ) :
    inner ℝ f g = (∫ x, star (f x) * g x ∂μ).re := by
  rw [L2.inner_def]
  have hi : Integrable (fun x => star (f x) * g x) μ := by
    simpa [RCLike.inner_apply, mul_comm] using L2.integrable_inner (𝕜 := ℂ) f g
  calc
    (∫ x, inner ℝ (f x) (g x) ∂μ) = ∫ x, (star (f x) * g x).re ∂μ := by
      congr 1
      ext x
      simp [Complex.inner, mul_comm]
    _ = _ := Complex.reCLM.integral_comp_comm hi

lemma product_integrable (f : Lp ℂ ∞ μ) (g : Lp ℂ 1 μ) :
    Integrable (fun x => f x * g x) μ := by
  exact memLp_one_iff_integrable.mp ((ContinuousLinearMap.mul ℂ ℂ).memLp_of_bilin 1
    (Lp.memLp f) (Lp.memLp g))

lemma pairing_eq_integral (D : InvolutionData μ) (f : Fixed D ∞) (g : Fixed D 1) :
    pairing D f g = (∫ x, f.val x * g.val x ∂μ).re := by
  change ((ContinuousLinearMap.mul ℝ ℂ).lpPairing μ ∞ 1 f.val g.val).re = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rfl

lemma fixed_pairing_integral_real (D : InvolutionData μ) (f : Fixed D ∞) (g : Fixed D 1) :
    (∫ x, f.val x * g.val x ∂μ).im = 0 :=
  pair_integral_real D.tau D.measurePreserving D.involutive (fixed_ae D f) (fixed_ae D g)

lemma fixed_inner_integral_real (D : InvolutionData μ) (f g : Fixed D 2) :
    (∫ x, star (f.val x) * g.val x ∂μ).im = 0 :=
  inner_integral_real D.tau D.measurePreserving D.involutive (fixed_ae D f) (fixed_ae D g)

lemma fixed_inner_eq_integral (D : InvolutionData μ) (f g : Fixed D 2) :
    (inner ℝ f g : ℂ) = ∫ x, star (f.val x) * g.val x ∂μ := by
  apply Complex.ext
  · change inner ℝ f.val g.val = _
    exact l2_inner_real_formula f.val g.val
  · simpa using (fixed_inner_integral_real D f g).symm

end NativeLp

theorem nativeLp_hilbert_pairing : Spec.NativeLpHilbertPairing.{u} := by
  intro X _ μ D
  constructor
  · intro f g
    refine ⟨?_, NativeLp.fixed_inner_integral_real D f g,
      NativeLp.fixed_inner_eq_integral D f g⟩
    simpa [RCLike.inner_apply, mul_comm] using
      MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f.val g.val
  · intro f g
    exact ⟨NativeLp.product_integrable f.val g.val,
      NativeLp.pairing_eq_integral D f g, NativeLp.fixed_pairing_integral_real D f g⟩
end ExpandedFA.VonNeumann.RealAbelianComplexification

namespace ExpandedFA.VonNeumann.RealAbelianComplexification
open MeasureTheory
open scoped ENNReal
universe u v
abbrev lpProduct := @Spec.NativeLp.fixedProduct
abbrev lpStar := @Spec.NativeLp.fixedStar
abbrev lpMultiplier := @Spec.NativeLp.restrictedMultiplier
abbrev lpMultiplierRepresentation := @Spec.NativeLp.multiplierAlgebraHom

theorem nativeLp_algebra_multiplier : Spec.NativeLpAlgebraMultiplier.{u} := by
  constructor
  · intro X _ μ D
    exact ⟨fun _ _ ↦ rfl, fun _ ↦ rfl, rfl, Spec.NativeLp.fixed_algebraMap D,
      fun f g ↦ norm_mul_le f g, fun f ↦ norm_star f⟩
  · intro X _ μ D
    exact ⟨Spec.NativeLp.multiplier_preserves D, Spec.NativeLp.restrictedMultiplier_val D,
      Spec.NativeLp.restrictedMultiplier_one D, Spec.NativeLp.restrictedMultiplier_product D,
      Spec.NativeLp.restrictedMultiplier_add D, Spec.NativeLp.restrictedMultiplier_real_smul D⟩

theorem complete_result : Spec.CompleteResult.{u, v} :=
  ⟨operator_decomposition, conjugation_laws, fixed_operators, conjugation_star,
    algebra_carrier, algebra_fixed_points, commutants, generated_double_commutants,
    strong_extension, weak_extension, extraction_continuous, closed_algebras,
    masa_transport, cyclic_separating_transport, separability, nativeLp_foundation,
    nativeLp_hilbert_pairing, nativeLp_algebra_multiplier⟩
end ExpandedFA.VonNeumann.RealAbelianComplexification
