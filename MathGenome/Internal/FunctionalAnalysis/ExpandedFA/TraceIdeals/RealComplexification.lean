import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.PreHilbertCompactSpectral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceClassDefinitions

noncomputable section
open scoped InnerProductSpace Topology
namespace ExpandedFA.TraceIdeals.RealComplexification
universe v w z
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification
/-- Reuse the real isometric embedding constructed by the model's owner. -/
abbrev inclusion {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    H →ₗᵢ[ℝ] Space H :=
  Hilbert.PreHilbertCompactSpectral.Complexification.realEmbedding H
abbrev realPart := @Spec.realPart
abbrev imagPart := @Spec.imagPart
abbrev conjugation := @Spec.conjugation
abbrev operator := @Spec.operator
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]

@[simp] lemma inclusion_apply (x : H) : inclusion x = complexPair H x 0 := rfl
@[simp] lemma realPart_apply (p : Space H) : realPart p = p.1 := rfl
@[simp] lemma imagPart_apply (p : Space H) : imagPart p = p.2 := rfl
@[simp] lemma conjugation_apply (p : Space H) : conjugation p = complexPair H p.1 (-p.2) := rfl
@[simp] lemma operator_apply (T : H →L[ℝ] K) (p : Space H) :
    operator T p = complexPair K (T p.1) (T p.2) := rfl

lemma decomposition (p : Space H) : p = inclusion p.1 + Complex.I • inclusion p.2 := by
  rw [csmul]
  change (p.1, p.2) = (p.1 + (Complex.I.re • p.2 - Complex.I.im • (0:H)),
    (0:H) + (Complex.I.im • p.2 + Complex.I.re • (0:H)))
  simp

@[simp] lemma inner_inclusion (x y : H) :
    inner ℂ (inclusion x) (inclusion y) = (inner ℝ x y : ℂ) := by
  change ip H (complexPair H x 0) (complexPair H y 0) = _
  apply Complex.ext <;> simp [ip, complexPair]

lemma inner_inclusion_left (x : H) (p : Space H) :
    inner ℂ (inclusion x) p = ⟨inner ℝ x p.1, inner ℝ x p.2⟩ := by
  change ip H (complexPair H x 0) p = _
  apply Complex.ext <;> simp [ip, complexPair]

theorem coordinates : Spec.Coordinates.{v} := by
  intro H _ _
  refine ⟨decomposition, ?_, ?_, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      have h : -p.2 = p.2 := congrArg Prod.snd hp
      have hz : p.2 = 0 := by
        let y : H := p.2
        change -y = y at h
        have hh : (2:ℝ) • y = 0 := by
          rw [two_smul]
          calc y + y = y + -y := congrArg (y + ·) h.symm
               _ = 0 := add_neg_cancel y
        exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
      exact ⟨p.1, Prod.ext rfl hz.symm⟩
    · rintro ⟨x, rfl⟩
      change (x, -(0:H)) = (x, 0)
      simp
  · intro p
    change (p.1, -(-p.2)) = (p.1, p.2)
    simp
  · intro a p
    rw [conjugation_apply, csmul, conjugation_apply, csmul]
    change (a.re • p.1 - a.im • p.2, -(a.im • p.1 + a.re • p.2)) =
      ((star a).re • p.1 - (star a).im • (-p.2),
        (star a).im • p.1 + (star a).re • (-p.2))
    ext <;> simp [sub_eq_add_neg, add_comm]
  · intro p x y
    rw [csmul]
    change p = (x + (Complex.I.re • y - Complex.I.im • (0:H)),
      (0:H) + (Complex.I.im • y + Complex.I.re • (0:H))) ↔ p.1 = x ∧ p.2 = y
    simp only [Complex.I_re, Complex.I_im, zero_smul, one_smul, sub_zero,
      add_zero, zero_add]
    exact Prod.ext_iff

lemma operator_inclusion (T : H →L[ℝ] K) (x : H) :
    operator T (inclusion x) = inclusion (T x) := by
  change (T x, T 0) = (T x, 0)
  simp

lemma operator_unique (T : H →L[ℝ] K) (S : Space H →L[ℂ] Space K)
    (hS : ∀ x, S (inclusion x) = inclusion (T x)) : S = operator T := by
  ext p
  calc
    S p = S (inclusion p.1 + Complex.I • inclusion p.2) := congrArg S (decomposition p)
    _ = operator T (inclusion p.1 + Complex.I • inclusion p.2) := by
      simp only [map_add, map_smul, hS, operator_inclusion]
    _ = operator T p := congrArg (operator T) (decomposition p).symm

lemma operator_norm (T : H →L[ℝ] K) : ‖operator T‖ = ‖T‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _
  · apply T.opNorm_le_bound (norm_nonneg (operator T))
    intro x
    calc ‖T x‖ = ‖inclusion (T x)‖ := (inclusion.norm_map (T x)).symm
         _ = ‖operator T (inclusion x)‖ := congrArg norm (operator_inclusion T x).symm
         _ ≤ ‖operator T‖ * ‖inclusion x‖ := (operator T).le_opNorm _
         _ = ‖operator T‖ * ‖x‖ := by rw [inclusion.norm_map]

theorem operator_formula : Spec.OperatorFormula.{v,w} := by
  intro H K _ _ _ _ T
  exact ⟨fun _ => rfl, operator_unique T, operator_norm T⟩

@[simp] lemma operator_id : operator (ContinuousLinearMap.id ℝ H) =
    ContinuousLinearMap.id ℂ (Space H) := by ext p; rfl
@[simp] lemma operator_add (S T : H →L[ℝ] K) : operator (S + T) = operator S + operator T := by
  ext p; rfl
@[simp] lemma operator_real_smul (r : ℝ) (T : H →L[ℝ] K) :
    operator (r • T) = (r : ℂ) • operator T := by
  ext p
  rw [smul_apply, csmul]
  change (r • T p.1, r • T p.2) = _
  simp [complexPair]
@[simp] lemma operator_comp {G : Type z} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (S : K →L[ℝ] G) (T : H →L[ℝ] K) :
    operator (S.comp T) = (operator S).comp (operator T) := by ext p; rfl

theorem operator_algebra : Spec.OperatorAlgebra.{v,w,z} := by
  exact ⟨fun _ _ _ => operator_id, fun _ _ _ _ _ _ S T r =>
    ⟨operator_add S T, operator_real_smul r T⟩,
    fun _ _ _ _ _ _ _ _ _ T S => operator_comp S T⟩

lemma operator_adjoint [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K) :
    (operator T).adjoint = operator T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro q p
  change ip H (complexPair H (T.adjoint q.1) (T.adjoint q.2)) p =
    ip K q (complexPair K (T p.1) (T p.2))
  apply Complex.ext <;> simp only [ip, complexPair, ContinuousLinearMap.adjoint_inner_left]

theorem adjoint : Spec.Adjoint.{v,w} := by
  intro H K _ _ _ _ _ _ T
  exact operator_adjoint T

lemma operator_compact_iff (T : H →L[ℝ] K) :
    IsCompactOperator (operator T) ↔ IsCompactOperator T := by
  constructor
  · intro h
    have hh := (h.comp_clm inclusion.toContinuousLinearMap).clm_comp (realPart (H := K))
    exact hh
  · intro hc
    obtain ⟨C, hC, hTC⟩ := hc.image_closedBall_subset_compact (f := T.toLinearMap) 1
    apply (isCompactOperator_iff_image_closedBall_subset_compact
      (operator T).toLinearMap (by norm_num : (0:ℝ) < 1)).mpr
    let e := Hilbert.PreHilbertCompactSpectral.Complexification.pairEquiv K
    refine ⟨e.symm '' (C ×ˢ C), (hC.prod hC).image e.symm.continuous, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have hp' : ‖p‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
    refine ⟨(T p.1, T p.2), ⟨?_, ?_⟩, rfl⟩
    · exact hTC ⟨p.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using
        (Hilbert.PreHilbertCompactSpectral.Complexification.norm_fst_le H p).trans hp', rfl⟩
    · exact hTC ⟨p.2, by simpa only [Metric.mem_closedBall, dist_zero_right] using
        (Hilbert.PreHilbertCompactSpectral.Complexification.norm_snd_le H p).trans hp', rfl⟩

theorem compactness : Spec.Compactness.{v,w} := by
  intro H K _ _ _ _ T
  rw [ExpandedFA.Compactness.compact_iff_isCompactOperator,
    ExpandedFA.Compactness.compact_iff_isCompactOperator]
  exact (operator_compact_iff T).symm

lemma operator_eq_original (T : H →L[ℝ] H) :
    operator T = Hilbert.PreHilbertCompactSpectral.Complexification.op H T := by
  ext p
  rfl

theorem earlier_witness : Spec.EarlierWitness.{v} := by
  intro H _ _ T S hS
  ext p
  exact hS p

lemma inclusion_orthonormal {ι : Type z} (e : ι → H) (he : Orthonormal ℝ e) :
    Orthonormal ℂ (fun i => inclusion (e i)) := by
  constructor
  · intro i
    rw [inclusion.norm_map]
    exact he.norm_eq_one i
  · intro i j hij
    rw [inner_inclusion, he.inner_eq_zero hij, Complex.ofReal_zero]

lemma basis_total [CompleteSpace H] {ι : Type z} (b : HilbertBasis ι ℝ H) :
    (Submodule.span ℂ (Set.range (fun i => inclusion (b i)))).orthogonal = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  have hh := (CompactSpectral.CompactNormalClassification.orthogonal_span_range_iff
    (fun i => inclusion (b i)) p).mp hp
  have hre : p.1 = 0 := by
    apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply, inner_zero_right]
    change inner ℝ (b i) p.1 = 0
    have h := congrArg Complex.re (hh i)
    simpa only [inner_inclusion_left, Complex.zero_re] using h
  have him : p.2 = 0 := by
    apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply, inner_zero_right]
    change inner ℝ (b i) p.2 = 0
    have h := congrArg Complex.im (hh i)
    simpa only [inner_inclusion_left, Complex.zero_im] using h
  exact Prod.ext hre him

def basis [CompleteSpace H] {ι : Type z} (b : HilbertBasis ι ℝ H) :
    HilbertBasis ι ℂ (Space H) :=
  HilbertBasis.mkOfOrthogonalEqBot (inclusion_orthonormal b b.orthonormal) (basis_total b)

@[simp] lemma basis_apply [CompleteSpace H] {ι : Type z} (b : HilbertBasis ι ℝ H) (i : ι) :
    basis b i = inclusion (b i) := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

theorem basis_extension : Spec.BasisExtension.{v,z} := by
  intro H _ _ _ ι b
  exact ⟨basis b, basis_apply b⟩

lemma inverse_transport (A B : H →L[ℝ] H)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ H)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ H) :
    (operator A).comp (operator B) = ContinuousLinearMap.id ℂ (Space H) ∧
    (operator B).comp (operator A) = ContinuousLinearMap.id ℂ (Space H) := by
  constructor
  · rw [← operator_comp, hAB, operator_id]
  · rw [← operator_comp, hBA, operator_id]

/-- The inverse descends by its real coordinate on real vectors. -/
def realInverse (C : Space H →L[ℂ] Space H) : H →L[ℝ] H :=
  realPart.comp ((C.restrictScalars ℝ).comp inclusion.toContinuousLinearMap)

lemma inverse_descends (A : H →L[ℝ] H) (C : Space H →L[ℂ] Space H)
    (hAC : (operator A).comp C = ContinuousLinearMap.id ℂ (Space H))
    (hCA : C.comp (operator A) = ContinuousLinearMap.id ℂ (Space H)) :
    A.comp (realInverse C) = ContinuousLinearMap.id ℝ H ∧
    (realInverse C).comp A = ContinuousLinearMap.id ℝ H := by
  constructor
  · ext x
    exact congrArg (fun F : Space H →L[ℂ] Space H => (F (inclusion x)).1) hAC
  · ext x
    have h := congrArg (fun F : Space H →L[ℂ] Space H => (F (inclusion x)).1) hCA
    change (C (inclusion (A x))).1 = x
    simpa only [ContinuousLinearMap.comp_apply, operator_inclusion,
      ContinuousLinearMap.id_apply] using (show (C (operator A (inclusion x))).1 = x from h)

/-- Every bounded complex inverse is the complexification of its descended
real inverse; in particular it preserves the fixed real subspace. -/
lemma inverse_identification (A : H →L[ℝ] H) (C : Space H →L[ℂ] Space H)
    (hAC : (operator A).comp C = ContinuousLinearMap.id ℂ (Space H))
    (hCA : C.comp (operator A) = ContinuousLinearMap.id ℂ (Space H)) :
    C = operator (realInverse C) := by
  have h := inverse_descends A C hAC hCA
  have hh := (inverse_transport A (realInverse C) h.1 h.2).1
  calc C = C.comp (ContinuousLinearMap.id ℂ (Space H)) := (ContinuousLinearMap.comp_id C).symm
       _ = C.comp ((operator A).comp (operator (realInverse C))) := congrArg C.comp hh.symm
       _ = (C.comp (operator A)).comp (operator (realInverse C)) := (ContinuousLinearMap.comp_assoc _ _ _).symm
       _ = operator (realInverse C) := by rw [hCA, ContinuousLinearMap.id_comp]

theorem invertibility : Spec.Invertibility.{v} := by
  intro H _ _ _ A
  refine ⟨⟨?_, ?_⟩, inverse_transport A⟩
  · rintro ⟨B, hAB, hBA⟩
    exact ⟨operator B, inverse_transport A B hAB hBA⟩
  · rintro ⟨C, hAC, hCA⟩
    exact ⟨realInverse C, inverse_descends A C hAC hCA⟩

section Spectral
variable [CompleteSpace H] [CompleteSpace K]
open CompactSpectral
open TraceClassDefinitions.Spec

omit [CompleteSpace H] in
lemma span_inclusion_orthogonal {ι : Type*} (e : ι → H) (p : Space H) :
    p ∈ (Submodule.span ℂ (Set.range (fun i => inclusion (e i)))).orthogonal ↔
      p.1 ∈ (Submodule.span ℝ (Set.range e)).orthogonal ∧
      p.2 ∈ (Submodule.span ℝ (Set.range e)).orthogonal := by
  simp only [CompactNormalClassification.orthogonal_span_range_iff, inner_inclusion_left,
    Complex.ext_iff, Complex.zero_re, Complex.zero_im]
  exact forall_and

omit [CompleteSpace H] [CompleteSpace K] in
lemma operator_hasSum {ι : Type*} (T : H →L[ℝ] K) (a : ι → ℝ) (e : ι → H) (f : ι → K)
    (hs : ∀ x, HasSum (fun j => (a j * inner ℝ (e j) x) • f j) (T x)) (p : Space H) :
    HasSum (fun j => ((a j : ℂ) * inner ℂ (inclusion (e j)) p) • inclusion (f j)) (operator T p) := by
  have h₁ := (hs p.1).mapL inclusion.toContinuousLinearMap
  have h₂ := ((hs p.2).mapL inclusion.toContinuousLinearMap).const_smul Complex.I
  convert h₁.add h₂ using 1
  · ext j
    change ((a j : ℂ) * inner ℂ (inclusion (e j)) p) • inclusion (f j) =
      inclusion ((a j * inner ℝ (e j) p.1) • f j) +
      Complex.I • inclusion ((a j * inner ℝ (e j) p.2) • f j)
    rw [inner_inclusion_left]
    simp only [inclusion_apply]
    rw [csmul, csmul]
    apply Prod.ext
    · simp [complexPair, mul_smul]
      change a j • inner ℝ (e j) p.1 • f j = a j • inner ℝ (e j) p.1 • f j + 0
      exact (add_zero _).symm
    · simp [complexPair, mul_smul]
      change a j • inner ℝ (e j) p.2 • f j = 0 + a j • inner ℝ (e j) p.2 • f j
      exact (zero_add _).symm
  · exact decomposition (operator T p)

/-- A singular system is extended with exactly its original index and weights. -/
def singularSystem (T : H →L[ℝ] K) (S : SingularExpansion.Spec.SingularSystem ℝ H K T) :
    SingularExpansion.Spec.SingularSystem ℂ (Space H) (Space K) (operator T) := by
  have hr : (Submodule.span ℝ (Set.range S.rightVector)).orthogonal = T.ker := by
    rw [← Submodule.orthogonal_closure, S.right_closedSpan, Submodule.orthogonal_orthogonal]
  have hl : (Submodule.span ℝ (Set.range S.leftVector)).orthogonal = T.adjoint.ker := by
    rw [← Submodule.orthogonal_closure, S.left_closedSpan, Submodule.orthogonal_orthogonal]
  have hrC : (Submodule.span ℂ (Set.range (fun j => inclusion (S.rightVector j)))).orthogonal =
      (operator T).ker := by
    ext p
    rw [span_inclusion_orthogonal, hr]
    change T p.1 = 0 ∧ T p.2 = 0 ↔ complexPair K (T p.1) (T p.2) = 0
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  have hlC : (Submodule.span ℂ (Set.range (fun j => inclusion (S.leftVector j)))).orthogonal =
      (operator T).adjoint.ker := by
    rw [operator_adjoint]
    ext p
    rw [span_inclusion_orthogonal, hl]
    change T.adjoint p.1 = 0 ∧ T.adjoint p.2 = 0 ↔
      complexPair H (T.adjoint p.1) (T.adjoint p.2) = 0
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  have hright : (Submodule.span ℂ (Set.range (fun j => inclusion (S.rightVector j)))).topologicalClosure =
      (operator T).ker.orthogonal := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hrC]
  have hleft : (Submodule.span ℂ (Set.range (fun j => inclusion (S.leftVector j)))).topologicalClosure =
      (operator T).adjoint.ker.orthogonal := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hlC]
  have hmap (j : S.Index) : operator T (inclusion (S.rightVector j)) =
      (S.sigma j : ℂ) • inclusion (S.leftVector j) := by
    rw [operator_inclusion, S.map_right]
    rw [csmul]
    change (S.sigma j • S.leftVector j, (0:K)) = _
    simp [complexPair]
  letI : CompleteSpace (operator T).ker := (operator T).isClosed_ker.completeSpace_coe
  letI : CompleteSpace (operator T).adjoint.ker := (operator T).adjoint.isClosed_ker.completeSpace_coe
  refine {
    Index := S.Index
    countable := S.countable
    sigma := S.sigma
    rightVector := fun j => inclusion (S.rightVector j)
    leftVector := fun j => inclusion (S.leftVector j)
    positive := S.positive
    right_orthonormal := inclusion_orthonormal _ S.right_orthonormal
    left_orthonormal := inclusion_orthonormal _ S.left_orthonormal
    map_right := hmap
    adjoint_left := ?_
    right_closedSpan := hright
    right_complement := ?_
    left_closedSpan := hleft
    left_complement := ?_
    expansion := operator_hasSum T S.sigma S.rightVector S.leftVector S.expansion
    adjoint_expansion := ?_
    finite_multiplicity := S.finite_multiplicity
    finite_away := S.finite_away
    finite_rank := ?_
    zero_empty := ?_ }
  · intro j
    rw [operator_adjoint, operator_inclusion, S.adjoint_left, csmul]
    change (S.sigma j • S.rightVector j, (0:H)) = _
    simp [complexPair]
  · rw [hright]
    exact (operator T).ker.isCompl_orthogonal
  · rw [hleft]
    exact (operator T).adjoint.ker.isCompl_orthogonal
  · intro p
    rw [operator_adjoint]
    exact operator_hasSum T.adjoint S.sigma S.leftVector S.rightVector S.adjoint_expansion p
  · intro hfinite
    let := hfinite
    let g : S.Index → (operator T).range := fun j =>
      ⟨inclusion (S.leftVector j), by
        refine ⟨(S.sigma j : ℂ)⁻¹ • inclusion (S.rightVector j), ?_⟩
        change operator T ((S.sigma j : ℂ)⁻¹ • inclusion (S.rightVector j)) = _
        rw [map_smul, hmap, inv_smul_smul₀ (by exact_mod_cast (S.positive j).ne')]⟩
    have hli : LinearIndependent ℂ ((operator T).range.subtype ∘ g) :=
      (inclusion_orthonormal S.leftVector S.left_orthonormal).linearIndependent
    exact (hli.of_comp (operator T).range.subtype).finite
  · intro hz
    apply S.zero_empty
    ext x
    apply inclusion.injective
    rw [← operator_inclusion, hz]
    rfl

lemma singularValue_operator (T : H →L[ℝ] K)
    (hT : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap) (n : ℕ) :
    SingularApproximation.Spec.SingularValueValue (operator T) n =
      SingularApproximation.Spec.SingularValueValue T n := by
  by_cases hn : 0 < n
  · obtain ⟨S⟩ := SingularExpansion.compact_singular_system ℝ H K T hT
    have hTC := (compactness H K T).mp hT
    have hR := (SingularApproximation.singular_spectral_counting ℝ H K T hT S).1
    have hC := (SingularApproximation.singular_spectral_counting ℂ (Space H) (Space K)
      (operator T) hTC (singularSystem T S)).1
    have hRn := (SingularApproximation.singular_sequence_properties ℝ H K T hT).1 n hn
    have hCn := (SingularApproximation.singular_sequence_properties ℂ (Space H) (Space K)
      (operator T) hTC).1 n hn
    apply le_antisymm
    · apply le_of_forall_gt_imp_ge_of_dense
      intro c hc
      exact (hC c (lt_of_le_of_lt hRn hc) n hn).mpr
        ((hR c (lt_of_le_of_lt hRn hc) n hn).mp hc.le)
    · apply le_of_forall_gt_imp_ge_of_dense
      intro c hc
      exact (hR c (lt_of_le_of_lt hCn hc) n hn).mpr
        ((hC c (lt_of_le_of_lt hCn hc) n hn).mp hc.le)
  · have hn0 : n = 0 := by omega
    subst n
    simp [SingularApproximation.Spec.SingularValueValue]

theorem singular_values : Spec.SingularValues.{v,w} := by
  intro H K _ _ _ _ _ _ T hT n
  exact singularValue_operator T hT n

lemma traceClass_operator_iff (T : H →L[ℝ] K) :
    IsTraceClassValue (operator T) ↔ IsTraceClassValue T := by
  constructor
  · intro h
    have hc := (compactness H K T).mpr h.1
    exact ⟨hc, h.2.congr (fun n => singularValue_operator T hc (n+1))⟩
  · intro h
    exact ⟨(compactness H K T).mp h.1,
      h.2.congr (fun n => (singularValue_operator T h.1 (n+1)).symm)⟩

theorem trace_ideal : Spec.TraceIdeal.{v,w} := by
  intro H K _ _ _ _ _ _ T
  refine ⟨(traceClass_operator_iff T).symm, fun hT => ?_⟩
  exact tsum_congr (fun n => singularValue_operator T hT.1 (n+1))

theorem trace : Spec.Trace.{v} := by
  intro H _ _ _ T hT
  let b := TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℝ) (H := H)
  have hR := (TraceClassDefinitions.diagonal_trace ℝ H T hT _ b).2
  have hC := (TraceClassDefinitions.diagonal_trace ℂ (Space H) (operator T)
    ((traceClass_operator_iff T).mpr hT) _ (basis b)).2
  have he := hR.mapL Complex.ofRealCLM
  apply HasSum.unique hC
  convert he using 1
  · ext i
    rw [basis_apply, operator_inclusion, inner_inclusion]
    rfl
  · rfl

end Spectral

end ExpandedFA.TraceIdeals.RealComplexification
