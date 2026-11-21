import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.CompactNormalClassification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.NormalExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.HilbertCardinalityClassification
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
Compact normal spectral expansion and classification on arbitrary complex and
real Hilbert spaces. The real proof constructs reducing eigenvalue lines and
positive-speed rotation planes directly on the original space, through the
finite-dimensional eigenspaces of N†N. The whole kernel is retained in both
classifications.
-/
noncomputable section
open scoped InnerProductSpace
open Filter
set_option maxHeartbeats 2000000

namespace ExpandedFA.CompactSpectral.CompactNormalClassification
universe u v w t
open Spec (basisSet chosenBasis hilbertDimension eigenMultiplicity)

lemma chosenBasis_maximal (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] :
    Hilbert.OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H (basisSet 𝕜 H)
      (chosenBasis 𝕜 H) :=
  (Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 H _ _
    (chosenBasis 𝕜 H).orthonormal).mpr (chosenBasis 𝕜 H).dense_span

theorem dimension_classification : Spec.DimensionClassification.{u,v,w} := by
  intro 𝕜 H K _ _ _ _ _ _ _
  exact Hilbert.HilbertCardinalityClassification.unitary_classification 𝕜 H K _ _
    (chosenBasis 𝕜 H) (chosenBasis 𝕜 K)
    (chosenBasis_maximal 𝕜 H) (chosenBasis_maximal 𝕜 K)

theorem complex_expansion : Spec.ComplexExpansion.{v} :=
  ⟨NormalEigenspaces.normal_orthogonal_eigenspaces,
    NormalEigenspaces.compact_finite_dimensional_eigenspaces,
    NormalEigenspaces.compact_nonzero_eigenvalues_countable,
    NormalEigenspaces.compact_eigenvalues_finite_away_from_zero,
    NormalExpansion.decomposition, NormalExpansion.vector_expansion,
    NormalExpansion.operator_expansion, NormalExpansion.ordered_expansion,
    NormalExpansion.tail_norm⟩

section Intertwiners
variable {𝕜 : Type u} {H : Type v} {K : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- A unitary intertwiner restricts to an isometry of each full eigenspace.
Neither compactness nor normality is needed in this direction. -/
def eigenspaceIsometry (N : H →L[𝕜] H) (M : K →L[𝕜] K)
    (U : H ≃ₗᵢ[𝕜] K) (hU : ∀ x, U (N x) = M (U x)) (α : 𝕜) :
    Module.End.eigenspace N.toLinearMap α ≃ₗᵢ[𝕜]
      Module.End.eigenspace M.toLinearMap α := by
  let f : Module.End.eigenspace N.toLinearMap α →ₗᵢ[𝕜]
      Module.End.eigenspace M.toLinearMap α :=
    { toFun := fun x => ⟨U x, Module.End.mem_eigenspace_iff.mpr (by
        change M (U (x : H)) = α • U (x : H)
        have hx : N (x : H) = α • (x : H) := Module.End.mem_eigenspace_iff.mp x.property
        rw [← hU, hx, map_smul])⟩
      map_add' := fun _ _ => Subtype.ext (U.map_add _ _)
      map_smul' := fun _ _ => Subtype.ext (U.map_smul _ _)
      norm_map' := fun _ => U.norm_map _ }
  apply LinearIsometryEquiv.ofSurjective f
  intro y
  refine ⟨⟨U.symm y, Module.End.mem_eigenspace_iff.mpr ?_⟩, ?_⟩
  · change N (U.symm (y : K)) = α • U.symm (y : K)
    apply U.injective
    have hy : M (y : K) = α • (y : K) := Module.End.mem_eigenspace_iff.mp y.property
    rw [hU, U.apply_symm_apply, hy, map_smul, U.apply_symm_apply]
  · exact Subtype.ext (U.apply_symm_apply y)
end Intertwiners

section Complex
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance eigenspaceComplete (N : H →L[ℂ] H) (α : ℂ) :
    CompleteSpace (Module.End.eigenspace N.toLinearMap α) :=
  (N.isClosed_eigenspace α).completeSpace_coe

/-- All eigenspace basis vectors, including an arbitrary-dimensional kernel. -/
abbrev EigenbasisIndex (N : H →L[ℂ] H) :=
  (α : ℂ) × basisSet ℂ (Module.End.eigenspace N.toLinearMap α)

def eigenbasisVectors (N : H →L[ℂ] H) (j : EigenbasisIndex N) : H :=
  chosenBasis ℂ (Module.End.eigenspace N.toLinearMap j.1) j.2

lemma eigenbasisVectors_apply (N : H →L[ℂ] H) (j : EigenbasisIndex N) :
    N (eigenbasisVectors N j) = j.1 • eigenbasisVectors N j :=
  Module.End.mem_eigenspace_iff.mp
    (chosenBasis ℂ (Module.End.eigenspace N.toLinearMap j.1) j.2).property

lemma eigenbasisVectors_orthonormal (N : H →L[ℂ] H) (hN : IsStarNormal N) :
    Orthonormal ℂ (eigenbasisVectors N) :=
  (NormalEigenspaces.normal_orthogonal_eigenspaces H N hN).orthonormal_sigma_orthonormal
    (fun α => (chosenBasis ℂ (Module.End.eigenspace N.toLinearMap α)).orthonormal)

/-- Vanishing of a continuous functional on a Hilbert basis implies it
vanishes everywhere; the basis need not be countable. -/
lemma functional_zero_of_basis {𝕜 : Type u} {E : Type w} {ι : Type t} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (b : HilbertBasis ι 𝕜 E) (L : E →L[𝕜] 𝕜) (h : ∀ i, L (b i) = 0) (x : E) :
    L x = 0 := by
  have hs := L.hasSum (b.hasSum_repr x)
  have hz : (fun i => L (b.repr x i • b i)) = 0 := by
    funext i
    simp [h]
  change HasSum (fun i => L (b.repr x i • b i)) (L x) at hs
  rw [hz] at hs
  exact hs.unique hasSum_zero

lemma eigenbasisVectors_total (N : H →L[ℂ] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap)
    (hN : IsStarNormal N) :
    (Submodule.span ℂ (Set.range (eigenbasisVectors N))).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply bot_unique
  intro x hx
  have hinner (α : ℂ) (y : Module.End.eigenspace N.toLinearMap α) :
      inner ℂ x (y : H) = 0 := by
    apply functional_zero_of_basis (chosenBasis ℂ _) ((innerSL ℂ x).comp
      (Module.End.eigenspace N.toLinearMap α).subtypeL)
    intro i
    exact inner_eq_zero_symm.mp
      (hx _ (Submodule.subset_span ⟨⟨α, i⟩, rfl⟩))
  have hperp : x ∈ (NormalExpansion.Spec.nonzeroSpan N).orthogonal := by
    rw [NormalExpansion.Spec.nonzeroSpan, Submodule.orthogonal_closure]
    apply (Submodule.mem_orthogonal _ _).mpr
    have hle : (⨆ α : {α : ℂ // α ≠ 0},
        Module.End.eigenspace N.toLinearMap α.val) ≤
        (Submodule.span ℂ {x}).orthogonal := by
      apply iSup_le
      intro α y hy
      apply (Submodule.mem_orthogonal _ _).mpr
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        have hzx : z = x := Set.mem_singleton_iff.mp hz
        subst z
        exact hinner α.val ⟨y, hy⟩
      | zero => simp
      | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
      | smul a y _ hy => simp [inner_smul_left, hy]
    intro y hy
    exact inner_eq_zero_symm.mp
      (hle hy x (Submodule.subset_span (Set.mem_singleton x)))
  have hxker : x ∈ N.ker := by
    rwa [NormalExpansion.nonzeroSpan_orthogonal N hc hN] at hperp
  have hxE : x ∈ Module.End.eigenspace N.toLinearMap 0 :=
    Module.End.mem_eigenspace_iff.mpr (by simpa using hxker)
  exact (Submodule.mem_bot ℂ).mpr (inner_self_eq_zero.mp (hinner 0 ⟨x, hxE⟩))

lemma eigenbasisVectors_maximal (N : H →L[ℂ] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap)
    (hN : IsStarNormal N) :
    Hilbert.OrthonormalExpansion.IsMaximalOrthonormal ℂ H _ (eigenbasisVectors N) :=
  (Hilbert.OrthonormalExpansion.maximal_iff_total ℂ H _ _
    (eigenbasisVectors_orthonormal N hN)).mpr (eigenbasisVectors_total N hc hN)

end Complex

theorem complex_classification : Spec.ComplexClassification.{v,w} := by
  intro H K _ _ _ _ _ _ N M hcN hnN hcM hnM
  constructor
  · rintro ⟨U, hU⟩ α
    letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) :=
      (N.isClosed_eigenspace α).completeSpace_coe
    letI : CompleteSpace (Module.End.eigenspace M.toLinearMap α) :=
      (M.isClosed_eigenspace α).completeSpace_coe
    exact (dimension_classification ℂ _ _).mp ⟨eigenspaceIsometry N M U hU α⟩
  · intro h
    classical
    have heq (α : ℂ) : Nonempty
        (basisSet ℂ (Module.End.eigenspace N.toLinearMap α) ≃
          basisSet ℂ (Module.End.eigenspace M.toLinearMap α)) :=
      Cardinal.lift_mk_eq'.mp (h α)
    let p (α : ℂ) := Classical.choice (heq α)
    let q : EigenbasisIndex N ≃ EigenbasisIndex M := Equiv.sigmaCongrRight p
    obtain ⟨U, hU⟩ := Hilbert.HilbertCardinalityClassification.basis_bijection_extends
      ℂ H K _ _ (eigenbasisVectors N) (eigenbasisVectors M)
      (eigenbasisVectors_maximal N hcN hnN) (eigenbasisVectors_maximal M hcM hnM) q
    refine ⟨U, ?_⟩
    have heq : U.toContinuousLinearEquiv.toContinuousLinearMap.comp N =
        M.comp U.toContinuousLinearEquiv.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr
        (eigenbasisVectors_total N hcN hnN))
      rintro _ ⟨j, rfl⟩
      change U (N (eigenbasisVectors N j)) = M (U (eigenbasisVectors N j))
      rw [eigenbasisVectors_apply, map_smul, hU, eigenbasisVectors_apply]
      rfl
    intro x
    exact congrArg (fun L : H →L[ℂ] K => L x) heq

theorem selfAdjoint_eigenvalues_real : Spec.SelfAdjointEigenvaluesReal.{v} := by
  intro H _ _ _ N hN α x hx hα
  have he : Module.End.HasEigenvalue N.toLinearMap α :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hα, hx⟩
  have h := hN.isSymmetric.conj_eigenvalue_eq_self he
  have hh := congrArg Complex.im h
  change -α.im = α.im at hh
  linarith

theorem no_selfAdjoint_rotation_plane : Spec.NoSelfAdjointRotationPlane.{v} := by
  intro H _ _ _ N hN a b e f he hf hef hNe hNf
  have h : inner ℝ (N e) f = inner ℝ e (N f) := hN.isSymmetric e f
  rw [hNe, hNf, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_left, inner_smul_right, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he, hf, hef] at h
  norm_num at h
  linarith

section SelfAdjoint
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Nonzero eigenvalues over the original scalar field. -/
abbrev SelfAdjointNonzeroEigenvalues (T : H →L[𝕜] H) :=
  {μ : 𝕜 // Module.End.HasEigenvalue T.toLinearMap μ ∧ μ ≠ 0}

/-- Each eigenvalue is repeated according to its finite eigenspace dimension. -/
abbrev SelfAdjointEigenvectorIndex (T : H →L[𝕜] H) :=
  (μ : SelfAdjointNonzeroEigenvalues T) × Fin (Module.finrank 𝕜 (Module.End.eigenspace T.toLinearMap μ.val))

/-- A finite orthonormal basis of each nonzero eigenspace. -/
def nonzeroEigenspaceBasis (T : H →L[𝕜] H) (hc : IsCompactOperator T)
    (μ : SelfAdjointNonzeroEigenvalues T) :
    OrthonormalBasis (Fin (Module.finrank 𝕜 (Module.End.eigenspace T.toLinearMap μ.val)))
      𝕜 (Module.End.eigenspace T.toLinearMap μ.val) := by
  letI := T.finite_dimensional_eigenspace hc μ.val μ.property.2
  exact stdOrthonormalBasis 𝕜 _

/-- The collected nonzero unit eigenvectors in the original Hilbert space. -/
def nonzeroEigenvectors (T : H →L[𝕜] H) (hc : IsCompactOperator T) :
    SelfAdjointEigenvectorIndex T → H :=
  fun j => (nonzeroEigenspaceBasis T hc j.1 j.2 : H)

lemma nonzeroEigenvectors_orthonormal (T : H →L[𝕜] H)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    Orthonormal 𝕜 (nonzeroEigenvectors T hc) := by
  exact (hT.orthogonalFamily_eigenspaces.comp Subtype.val_injective).orthonormal_sigma_orthonormal
    (fun μ => (nonzeroEigenspaceBasis T hc μ).orthonormal)

lemma nonzeroEigenvectors_apply (T : H →L[𝕜] H)
    (hc : IsCompactOperator T) (j : SelfAdjointEigenvectorIndex T) :
    T (nonzeroEigenvectors T hc j) = j.1.val • nonzeroEigenvectors T hc j := by
  exact Module.End.mem_eigenspace_iff.mp (nonzeroEigenspaceBasis T hc j.1 j.2).property

omit [CompleteSpace H] in
lemma orthogonal_span_range_iff {I : Type w} (e : I → H) (x : H) :
    x ∈ (Submodule.span 𝕜 (Set.range e)).orthogonal ↔ ∀ i, inner 𝕜 (e i) x = 0 := by
  constructor
  · intro hx i
    exact hx _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hx i
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
    | smul a y _ hy => simp [inner_smul_left, hy]

lemma orthonormal_hasSum_projection {I : Type w} (e : I → H) (he : Orthonormal 𝕜 e) (x : H) :
    HasSum (fun i => inner 𝕜 (e i) x • e i)
      ((Submodule.span 𝕜 (Set.range e)).topologicalClosure.starProjection x) := by
  let M := (Submodule.span 𝕜 (Set.range e)).topologicalClosure
  let v : I → M := fun i => ⟨e i, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hv : Orthonormal 𝕜 v :=
    (M.subtypeₗᵢ.orthonormal_comp_iff).mp he
  have hperp : (Submodule.span 𝕜 (Set.range v)).orthogonal = ⊥ := by
    apply bot_unique
    intro y hy
    have hz : (y : H) ∈ (Submodule.span 𝕜 (Set.range e)).orthogonal := by
      apply (orthogonal_span_range_iff e y).mpr
      exact (orthogonal_span_range_iff v y).mp hy
    have hzM : (y : H) ∈ M.orthogonal := by
      rwa [Submodule.orthogonal_closure]
    have hy0 : (y : H) = 0 := inner_self_eq_zero.mp (hzM y y.property)
    exact (Submodule.mem_bot 𝕜).mpr (Subtype.ext hy0)
  let b := HilbertBasis.mkOfOrthogonalEqBot hv hperp
  have hs := (b.hasSum_orthogonalProjectionOnto x).map M.subtypeL M.subtypeL.continuous
  simpa only [b, Function.comp_def, map_smul, Submodule.subtypeL_apply,
    HilbertBasis.coe_mkOfOrthogonalEqBot, v, Submodule.coe_smul, Submodule.starProjection_apply] using hs

/-- The countability is in the nonzero spectral part, never the kernel. -/
lemma selfAdjointNonzeroEigenvalues_countable (T : H →L[𝕜] H)
    (hcompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap) :
    Countable (SelfAdjointNonzeroEigenvalues T) := by
  let S (n : ℕ) : Set 𝕜 :=
    {μ | (∃ x : H, x ≠ 0 ∧ T x = μ • x) ∧ 1 / (n + 1 : ℝ) ≤ ‖μ‖}
  have hS (n : ℕ) : (S n).Finite :=
    Fredholm.compact_eigenvalues_finite_away_from_zero T hcompact _ (by positivity)
  apply Set.countable_coe_iff.mpr
  apply (Set.countable_iUnion (fun n => (hS n).countable)).mono
  intro μ hμ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hμ.2)
  obtain ⟨x, hx, hx0⟩ := hμ.1.exists_hasEigenvector
  exact Set.mem_iUnion.mpr ⟨n, ⟨x, hx0, Module.End.mem_eigenspace_iff.mp hx⟩, hn.le⟩

lemma selfAdjointEigenvectorIndex_finite_away (T : H →L[𝕜] H)
    (hcompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (ε : ℝ) (hε : 0 < ε) :
    {j : SelfAdjointEigenvectorIndex T | ε ≤ ‖j.1.val‖}.Finite := by
  let S : Set (SelfAdjointNonzeroEigenvalues T) := {μ | ε ≤ ‖μ.val‖}
  have hfin := Fredholm.compact_eigenvalues_finite_away_from_zero T hcompact ε hε
  have hS : S.Finite := by
    apply (hfin.preimage Subtype.val_injective.injOn).subset
    intro μ hμ
    obtain ⟨x, hx, hx0⟩ := μ.property.1.exists_hasEigenvector
    exact ⟨⟨x, hx0, Module.End.mem_eigenspace_iff.mp hx⟩, hμ⟩
  apply (hS.sigma (fun _ _ => Set.finite_univ)).subset
  intro j hj
  exact ⟨hj, Set.mem_univ _⟩

/-- Every vector of a nonzero eigenspace is a finite combination of the
collected eigenvectors, with its actual eigenspace multiplicity. -/
lemma eigenspace_le_span_nonzeroEigenvectors (T : H →L[𝕜] H)
    (hc : IsCompactOperator T) (μ : SelfAdjointNonzeroEigenvalues T) :
    Module.End.eigenspace T.toLinearMap μ.val ≤
      Submodule.span 𝕜 (Set.range (nonzeroEigenvectors T hc)) := by
  intro x hx
  let b := nonzeroEigenspaceBasis T hc μ
  have hsum := congrArg (fun y : Module.End.eigenspace T.toLinearMap μ.val => (y : H))
    (b.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  rw [← hsum]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩

/-- The common orthogonal complement of the nonzero eigenvectors is the
entire kernel, with no separability assumption on that kernel. -/
lemma span_nonzeroEigenvectors_orthogonal (T : H →L[𝕜] H)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    (Submodule.span 𝕜 (Set.range (nonzeroEigenvectors T hc))).orthogonal = T.ker := by
  apply le_antisymm
  · intro x hx
    have hTx : T x ∈ (⨆ μ, Module.End.eigenspace T.toLinearMap μ).orthogonal := by
      rw [← Submodule.iInf_orthogonal]
      apply (Submodule.mem_iInf _).mpr
      intro μ y hy
      have hsym : inner 𝕜 (T y) x = inner 𝕜 y (T x) := hT y x
      rw [← hsym]
      have hTy : T y = μ • y := Module.End.mem_eigenspace_iff.mp hy
      by_cases hμ : μ = 0
      · rw [hTy, hμ, zero_smul, inner_zero_left]
      · by_cases hy0 : y = 0
        · simp [hy0]
        · let ν : SelfAdjointNonzeroEigenvalues T :=
            ⟨μ, Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩, hμ⟩
          have hxy := hx y (eigenspace_le_span_nonzeroEigenvectors T hc ν hy)
          rw [hTy, inner_smul_left, hxy, mul_zero]
    rw [T.orthogonalComplement_iSup_eigenspaces_eq_bot hc hT] at hTx
    exact (Submodule.mem_bot 𝕜).mp hTx
  · intro x hx
    apply (orthogonal_span_range_iff (nonzeroEigenvectors T hc) x).mpr
    intro j
    have h : inner 𝕜 (T (nonzeroEigenvectors T hc j)) x =
        inner 𝕜 (nonzeroEigenvectors T hc j) (T x) :=
      hT (nonzeroEigenvectors T hc j) x
    rw [nonzeroEigenvectors_apply T hc j, show T x = 0 from hx,
      inner_smul_left, inner_zero_right] at h
    exact (mul_eq_zero.mp h).resolve_left (by simpa using j.1.property.2)

/-- The nonzero spectral subspace is exactly the orthogonal complement of
`ker T`; this also identifies the first summand in a nonseparable space. -/
lemma closedSpan_nonzeroEigenvectors (T : H →L[𝕜] H)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    (Submodule.span 𝕜 (Set.range (nonzeroEigenvectors T hc))).topologicalClosure =
      T.ker.orthogonal := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    span_nonzeroEigenvectors_orthogonal T hc hT]

set_option maxHeartbeats 800000 in
/-- The self-adjoint theorem is proved over the original field. In particular,
the real conclusion is obtained without assuming a complex eigenbasis. -/
theorem selfAdjoint_expansion : Spec.SelfAdjointExpansion.{u,v} := by
  intro 𝕜 H _ _ _ _ T hT hcompact
  have hc : IsCompactOperator T :=
    (Compactness.compact_iff_isCompactOperator T.toLinearMap).mp hcompact
  let : Countable (SelfAdjointNonzeroEigenvalues T) :=
    selfAdjointNonzeroEigenvalues_countable T hcompact
  let : Countable (SelfAdjointEigenvectorIndex T) := inferInstance
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let e := nonzeroEigenvectors T hc
  let a : SelfAdjointEigenvectorIndex T → ℝ := fun j => RCLike.re j.1.val
  have har (j : SelfAdjointEigenvectorIndex T) : (a j : 𝕜) = j.1.val :=
    RCLike.conj_eq_iff_re.mp (hT.isSymmetric.conj_eigenvalue_eq_self j.1.property.1)
  have he : Orthonormal 𝕜 e := nonzeroEigenvectors_orthonormal T hc hT.isSymmetric
  have heig (j : SelfAdjointEigenvectorIndex T) : T (e j) = (a j : 𝕜) • e j := by
    rw [har j]
    exact nonzeroEigenvectors_apply T hc j
  let M := (Submodule.span 𝕜 (Set.range e)).topologicalClosure
  have hM : M = T.ker.orthogonal := closedSpan_nonzeroEigenvectors T hc hT.isSymmetric
  refine ⟨SelfAdjointEigenvectorIndex T, inferInstance, e, a, he, ?_, hM, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, heig j⟩
    intro hj
    apply j.1.property.2
    rw [← har j, hj, RCLike.ofReal_zero]
  · change IsCompl T.ker M
    rw [hM]
    exact T.ker.isCompl_orthogonal
  · intro x
    have hs := orthonormal_hasSum_projection e he x
    change HasSum (fun j => inner 𝕜 (e j) x • e j) (M.starProjection x) at hs
    have hMorth : M.orthogonal = T.ker := by
      dsimp [M]
      rw [Submodule.orthogonal_closure, span_nonzeroEigenvectors_orthogonal T hc hT.isSymmetric]
    have hproj : M.starProjection x = x - T.ker.starProjection x := by
      apply M.eq_starProjection_of_mem_orthogonal
      · rw [hM]
        exact T.ker.sub_starProjection_mem_orthogonal x
      · have hab : x - (x - T.ker.starProjection x) = T.ker.starProjection x := by abel
        rw [hab, hMorth]
        exact T.ker.starProjection_apply_mem x
    rw [hproj] at hs
    have hp : T (T.ker.starProjection x) = 0 := T.ker.starProjection_apply_mem x
    have ht := hs.map T T.continuous
    have ht' : HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) (T x) := by
      simpa only [Function.comp_def, map_smul, heig, smul_smul, mul_comm,
        map_sub, hp, sub_zero] using ht
    exact ⟨hs, ht'⟩
  · intro μ hμ
    exact T.finite_dimensional_eigenspace hc μ hμ
  · intro ε hε
    have hfin := selfAdjointEigenvectorIndex_finite_away T hcompact ε hε
    convert hfin using 1
    ext j
    change (ε ≤ |a j|) ↔ (ε ≤ ‖j.1.val‖)
    rw [← har j, RCLike.norm_ofReal]
end SelfAdjoint

section RealModulus
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev gramOperator (N : H →L[ℝ] H) : H →L[ℝ] H := Spec.gramOperator N

lemma gramOperator_selfAdjoint (N : H →L[ℝ] H) : IsSelfAdjoint (gramOperator N) :=
  IsSelfAdjoint.star_mul_self N

lemma gramOperator_compact (N : H →L[ℝ] H) (hc : IsCompactOperator N) :
    IsCompactOperator (gramOperator N) := hc.clm_comp N.adjoint

lemma gramOperator_ker (N : H →L[ℝ] H) : (gramOperator N).ker = N.ker :=
  N.ker_adjoint_comp_self

lemma gramOperator_commute (N : H →L[ℝ] H) (hn : IsStarNormal N) :
    Commute (gramOperator N) N :=
  hn.star_comm_self.mul_left (Commute.refl N)

lemma gramOperator_adjoint_commute (N : H →L[ℝ] H) (hn : IsStarNormal N) :
    Commute (gramOperator N) N.adjoint :=
  (Commute.refl N.adjoint).mul_left hn.star_comm_self.symm

lemma maps_eigenspace_of_commute (A B : H →L[ℝ] H) (h : Commute A B)
    (r : ℝ) (x : H) (hx : x ∈ Module.End.eigenspace A.toLinearMap r) :
    B x ∈ Module.End.eigenspace A.toLinearMap r := by
  apply Module.End.mem_eigenspace_iff.mpr
  change A (B x) = r • B x
  have hh : A (B x) = B (A x) := congrArg (fun L : H →L[ℝ] H => L x) h.eq
  have hx' : A x = r • x := Module.End.mem_eigenspace_iff.mp hx
  rw [hh, hx', map_smul]

lemma gramOperator_eigenspace_reducing (N : H →L[ℝ] H) (hn : IsStarNormal N) (r : ℝ) :
    Hilbert.Adjoint.Spec.ReducingSubspaceValue ℝ H
      (Module.End.eigenspace (gramOperator N).toLinearMap r) N := by
  apply (Hilbert.Adjoint.reducing_iff_invariant_adjoint ℝ H _
    ((gramOperator N).isClosed_eigenspace r) N).mpr
  exact ⟨fun x hx => maps_eigenspace_of_commute _ _ (gramOperator_commute N hn) r x hx,
    fun x hx => maps_eigenspace_of_commute _ _ (gramOperator_adjoint_commute N hn) r x hx⟩

lemma gramOperator_eigenvector_norm_sq (N : H →L[ℝ] H) (r : ℝ) (x : H)
    (hx : x ∈ Module.End.eigenspace (gramOperator N).toLinearMap r) :
    ‖N x‖ ^ 2 = r * ‖x‖ ^ 2 := by
  have hh := N.adjoint_inner_left x (N x)
  rw [show N.adjoint (N x) = r • x from Module.End.mem_eigenspace_iff.mp hx,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hh
  exact hh.symm

lemma gramOperator_eigenvalue_pos (N : H →L[ℝ] H) (r : ℝ)
    (hr : Module.End.HasEigenvalue (gramOperator N).toLinearMap r) (hr0 : r ≠ 0) :
    0 < r := by
  obtain ⟨x, hx, hx0⟩ := hr.exists_hasEigenvector
  have hh := gramOperator_eigenvector_norm_sq N r x hx
  have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hnonneg : 0 ≤ r := (mul_nonneg_iff_of_pos_right hxpos).mp (hh ▸ sq_nonneg ‖N x‖)
  exact lt_of_le_of_ne hnonneg (Ne.symm hr0)

lemma closedSpan_nonzeroEigenspaces (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    (⨆ r : {r : ℝ // r ≠ 0}, Module.End.eigenspace T.toLinearMap r.val).topologicalClosure =
      T.ker.orthogonal := by
  have heq : (⨆ r : {r : ℝ // r ≠ 0}, Module.End.eigenspace T.toLinearMap r.val) =
      Submodule.span ℝ (Set.range (nonzeroEigenvectors T hc)) := by
    apply le_antisymm
    · apply iSup_le
      intro r x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · let μ : SelfAdjointNonzeroEigenvalues T :=
          ⟨r.val, Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩, r.property⟩
        exact eigenspace_le_span_nonzeroEigenvectors T hc μ hx
    · apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact (le_iSup (fun r : {r : ℝ // r ≠ 0} => Module.End.eigenspace T.toLinearMap r.val)
        ⟨j.1.val, j.1.property.2⟩) (Module.End.mem_eigenspace_iff.mpr
          (nonzeroEigenvectors_apply T hc j))
  rw [heq]
  exact closedSpan_nonzeroEigenvectors T hc hT

lemma gramOperator_closedSpan (N : H →L[ℝ] H) (hc : IsCompactOperator N) :
    (⨆ r : {r : ℝ // r ≠ 0},
      Module.End.eigenspace (gramOperator N).toLinearMap r.val).topologicalClosure =
        N.ker.orthogonal := by
  rw [closedSpan_nonzeroEigenspaces (gramOperator N) (gramOperator_compact N hc)
    (gramOperator_selfAdjoint N).isSymmetric, gramOperator_ker]

lemma gramOperator_finite_away (N : H →L[ℝ] H)
    (hcompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap)
    (ε : ℝ) (hε : 0 < ε) :
    {r : ℝ | Module.End.HasEigenvalue (gramOperator N).toLinearMap r ∧
      ε ≤ Real.sqrt r}.Finite := by
  have hc := (Compactness.compact_iff_isCompactOperator N.toLinearMap).mp hcompact
  have hcG : Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (gramOperator N).toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr (gramOperator_compact N hc)
  have hfin := Fredholm.compact_eigenvalues_finite_away_from_zero (gramOperator N)
    hcG (ε ^ 2) (sq_pos_of_pos hε)
  apply hfin.subset
  intro r hr
  obtain ⟨x, hx, hx0⟩ := hr.1.exists_hasEigenvector
  refine ⟨⟨x, hx0, Module.End.mem_eigenspace_iff.mp hx⟩, ?_⟩
  have hsqrt : ε ^ 2 ≤ (Real.sqrt r) ^ 2 := sq_le_sq₀ hε.le (Real.sqrt_nonneg r) |>.mpr hr.2
  calc
    ε ^ 2 ≤ (Real.sqrt r) ^ 2 := hsqrt
    _ = max r 0 := Real.sq_sqrt'
    _ ≤ ‖r‖ := max_le (le_abs_self r) (abs_nonneg r)

theorem real_modulus_decomposition : Spec.RealModulusDecomposition.{v} := by
  intro H _ _ _ N hcompact hn
  have hc := (Compactness.compact_iff_isCompactOperator N.toLinearMap).mp hcompact
  have hcG := gramOperator_compact N hc
  have hcompactG : Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (gramOperator N).toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr hcG
  change IsSelfAdjoint (gramOperator N) ∧ _
  refine ⟨gramOperator_selfAdjoint N, hcompactG, gramOperator_ker N,
    (gramOperator_selfAdjoint N).isSymmetric.orthogonalFamily_eigenspaces,
    (fun r hr => (gramOperator N).finite_dimensional_eigenspace hcG r hr),
    gramOperator_eigenvalue_pos N,
    gramOperator_eigenspace_reducing N hn, gramOperator_eigenvector_norm_sq N,
    gramOperator_closedSpan N hc, ?_, gramOperator_finite_away N hcompact⟩
  exact Set.countable_coe_iff.mp (selfAdjointNonzeroEigenvalues_countable (gramOperator N) hcompactG)


end RealModulus

namespace RealBlock
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma symmetricPart_isSelfAdjoint (T : E →L[ℝ] E) :
    IsSelfAdjoint ((2 : ℝ)⁻¹ • (T + T.adjoint)) := by
  simp [IsSelfAdjoint, star_smul, star_eq_adjoint, add_comm]

lemma exists_symmetricPart_unit_eigenvector [FiniteDimensional ℝ E] [Nontrivial E]
    (T : E →L[ℝ] E) :
    ∃ (a : ℝ) (e : E), ‖e‖ = 1 ∧ T e + T.adjoint e = (2 * a) • e := by
  let A := (2 : ℝ)⁻¹ • (T + T.adjoint)
  have hA : A.IsSymmetric := (symmetricPart_isSelfAdjoint T).isSymmetric
  obtain ⟨v, hv, hv0⟩ := hA.hasEigenvalue_iSup_of_finiteDimensional.exists_hasEigenvector
  let a : ℝ := ⨆ x : {x : E // x ≠ 0}, inner ℝ (A x) x / ‖(x : E)‖ ^ 2
  have hAv : A v = a • v := by
    exact Module.End.mem_eigenspace_iff.mp hv
  let e := ‖v‖⁻¹ • v
  refine ⟨a, e, norm_smul_inv_norm hv0, ?_⟩
  have hAe : A e = a • e := by
    dsimp [e]
    rw [map_smul, hAv, smul_smul, smul_smul, mul_comm]
  have hh := congrArg (fun x : E => (2 : ℝ) • x) hAe
  simpa [A, smul_smul, mul_assoc] using hh

lemma normal_gram_apply (T : E →L[ℝ] E) (hT : IsStarNormal T) (x : E) :
    T (T.adjoint x) = T.adjoint (T x) := by
  have hh := congrArg (fun S : E →L[ℝ] E => S x) ((isStarNormal_iff T).mp hT).eq
  exact hh.symm

lemma rotation_plane_of_gram_scalar (T : E →L[ℝ] E) (hT : IsStarNormal T)
    (μ a : ℝ) (e : E) (he : ‖e‖ = 1)
    (hgram : ∀ x, T.adjoint (T x) = μ • x)
    (hsym : T e + T.adjoint e = (2 * a) • e)
    (hne : T e - a • e ≠ 0) :
    ∃ (b : ℝ) (f : E), 0 < b ∧ ‖f‖ = 1 ∧ inner ℝ e f = 0 ∧
      T e = a • e + b • f ∧ T f = (-b) • e + a • f ∧
      T.adjoint e = a • e - b • f ∧ T.adjoint f = b • e + a • f ∧
      a ^ 2 + b ^ 2 = μ := by
  let u := T e - a • e
  let b := ‖u‖
  let f := b⁻¹ • u
  have hb : 0 < b := norm_pos_iff.mpr hne
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hadj : T.adjoint e = (2 * a) • e - T e := eq_sub_of_add_eq' hsym
  have hinner : inner ℝ e (T e) = a := by
    have hh := congrArg (fun x : E => inner ℝ e x) hsym
    rw [inner_add_right, inner_smul_right, hee, T.adjoint_inner_right] at hh
    rw [real_inner_comm e (T e)] at hh
    linarith
  have heu : inner ℝ e u = 0 := by
    dsimp [u]
    rw [inner_sub_right, inner_smul_right, hinner, hee]
    ring
  have hTTe : T (T e) = (2 * a) • T e - μ • e := by
    have hh := congrArg T hsym
    rw [map_add, map_smul, normal_gram_apply T hT, hgram] at hh
    exact eq_sub_of_add_eq hh
  have hTu : T u = a • u - (μ - a ^ 2) • e := by
    dsimp [u]
    rw [map_sub, map_smul, hTTe]
    module
  have hunn : ‖u‖ ^ 2 = μ - a ^ 2 := by
    have hh : inner ℝ (T e) (T e) = μ := by
      rw [← T.adjoint_inner_right, hgram, inner_smul_right, hee, mul_one]
    rw [real_inner_self_eq_norm_sq] at hh
    dsimp [u]
    rw [norm_sub_sq_real, hh, norm_smul, he, mul_one, inner_smul_right,
      real_inner_comm e (T e), hinner, Real.norm_eq_abs, sq_abs]
    ring
  have hinv : b⁻¹ * b ^ 2 = b := by field_simp
  refine ⟨b, f, hb, norm_smul_inv_norm hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [f]
    rw [inner_smul_right, heu, mul_zero]
  · have hu : b • f = u := by dsimp [f]; rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
    rw [hu]
    dsimp [u]
    abel
  · dsimp [f]
    rw [map_smul, hTu, ← hunn]
    change b⁻¹ • (a • u - b ^ 2 • e) = (-b) • e + a • (b⁻¹ • u)
    rw [smul_sub, smul_smul, smul_smul, hinv]
    module
  · have hu : b • f = u := by dsimp [f]; rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
    rw [hu, hadj]
    dsimp [u]
    module
  · have hSu : T.adjoint u = (μ - a ^ 2) • e + a • u := by
      dsimp [u]
      rw [map_sub, map_smul, hgram, hadj]
      module
    dsimp [f]
    rw [map_smul, hSu, ← hunn]
    change b⁻¹ • (b ^ 2 • e + a • u) = b • e + a • (b⁻¹ • u)
    rw [smul_add, smul_smul, smul_smul, hinv]
    module
  · dsimp [b]
    linarith [hunn]

/-- An oriented real spectral line (`b=0`, `f=0`) or positive-speed plane. -/
structure Frame (T : E →L[ℝ] E) (μ : ℝ) where
  a : ℝ
  b : ℝ
  e : E
  f : E
  norm_e : ‖e‖ = 1
  line_or_plane : (b = 0 ∧ f = 0) ∨ (0 < b ∧ ‖f‖ = 1)
  orthogonal : inner ℝ e f = 0
  apply_e : T e = a • e + b • f
  apply_f : T f = (-b) • e + a • f
  adjoint_e : T.adjoint e = a • e - b • f
  adjoint_f : T.adjoint f = b • e + a • f
  modulus : a ^ 2 + b ^ 2 = μ

lemma exists_frame [FiniteDimensional ℝ E] [Nontrivial E]
    (T : E →L[ℝ] E) (hT : IsStarNormal T) (μ : ℝ)
    (hgram : ∀ x, T.adjoint (T x) = μ • x) : Nonempty (Frame T μ) := by
  obtain ⟨a, e, he, hsym⟩ := exists_symmetricPart_unit_eigenvector T
  by_cases hu : T e - a • e = 0
  · have hTe : T e = a • e := sub_eq_zero.mp hu
    have hSe : T.adjoint e = a • e := by
      rw [eq_sub_of_add_eq' hsym, hTe]
      module
    have he0 : e ≠ 0 := by intro h; simp [h] at he
    have hmod : a ^ 2 = μ := by
      have hh := hgram e
      rw [hTe, map_smul, hSe, smul_smul] at hh
      have hh' : a * a = μ := (smul_left_injective ℝ he0) hh
      nlinarith
    exact ⟨⟨a, 0, e, 0, he, Or.inl ⟨rfl, rfl⟩, by simp,
      by simpa using hTe, by simp, by simpa using hSe, by simp, by simpa using hmod⟩⟩
  · obtain ⟨b, f, hb, hf, hef, hTe, hTf, hSe, hSf, hm⟩ :=
      rotation_plane_of_gram_scalar T hT μ a e he hgram hsym hu
    exact ⟨⟨a, b, e, f, he, Or.inr ⟨hb, hf⟩, hef, hTe, hTf, hSe, hSf, hm⟩⟩

namespace Frame
variable {T : E →L[ℝ] E} {μ : ℝ}

def space (F : Frame T μ) : Submodule ℝ E :=
  Submodule.span ℝ {F.e, F.f}

lemma e_mem_space (F : Frame T μ) : F.e ∈ F.space :=
  Submodule.subset_span (by simp)

lemma f_mem_space (F : Frame T μ) : F.f ∈ F.space :=
  Submodule.subset_span (by simp)

lemma space_ne_bot (F : Frame T μ) : F.space ≠ ⊥ := by
  intro hh
  have he0 : F.e = 0 := by simpa [hh] using F.e_mem_space
  have := F.norm_e
  simp [he0] at this

lemma invariant (F : Frame T μ) ⦃x : E⦄ (hx : x ∈ F.space) : T x ∈ F.space := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · rw [F.apply_e]
      exact F.space.add_mem (F.space.smul_mem _ F.e_mem_space) (F.space.smul_mem _ F.f_mem_space)
    · have hx' : x = F.f := Set.mem_singleton_iff.mp hx
      subst x
      rw [F.apply_f]
      exact F.space.add_mem (F.space.smul_mem _ F.e_mem_space) (F.space.smul_mem _ F.f_mem_space)
  | zero => simp
  | add x y _ _ hx hy => simpa using F.space.add_mem hx hy
  | smul a x _ hx => simpa using F.space.smul_mem a hx

lemma adjoint_invariant (F : Frame T μ) ⦃x : E⦄ (hx : x ∈ F.space) :
    T.adjoint x ∈ F.space := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · rw [F.adjoint_e]
      exact F.space.sub_mem (F.space.smul_mem _ F.e_mem_space) (F.space.smul_mem _ F.f_mem_space)
    · have hx' : x = F.f := Set.mem_singleton_iff.mp hx
      subst x
      rw [F.adjoint_f]
      exact F.space.add_mem (F.space.smul_mem _ F.e_mem_space) (F.space.smul_mem _ F.f_mem_space)
  | zero => simp
  | add x y _ _ hx hy => simpa using F.space.add_mem hx hy
  | smul a x _ hx => simpa using F.space.smul_mem a hx

lemma orthogonal_invariant (F : Frame T μ) ⦃x : E⦄ (hx : x ∈ F.space.orthogonal) :
    T x ∈ F.space.orthogonal := by
  intro y hy
  rw [← T.adjoint_inner_left]
  exact hx _ (F.adjoint_invariant hy)

lemma orthogonal_adjoint_invariant (F : Frame T μ) ⦃x : E⦄ (hx : x ∈ F.space.orthogonal) :
    T.adjoint x ∈ F.space.orthogonal := by
  intro y hy
  rw [T.adjoint_inner_right]
  exact hx _ (F.invariant hy)

end Frame

lemma adjoint_restrict_of_reducing (T : E →L[ℝ] E) (V : Submodule ℝ E)
    [CompleteSpace V] (hV : ∀ ⦃x⦄, x ∈ V → T x ∈ V)
    (hVstar : ∀ ⦃x⦄, x ∈ V → T.adjoint x ∈ V) :
    (T.restrict hV).adjoint = T.adjoint.restrict hVstar := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact T.adjoint_inner_left y x

lemma normal_restrict_of_reducing (T : E →L[ℝ] E) (hT : IsStarNormal T)
    (V : Submodule ℝ E) [CompleteSpace V]
    (hV : ∀ ⦃x⦄, x ∈ V → T x ∈ V)
    (hVstar : ∀ ⦃x⦄, x ∈ V → T.adjoint x ∈ V) :
    IsStarNormal (T.restrict hV) := by
  apply (isStarNormal_iff_norm_eq_adjoint).mpr
  intro x
  rw [adjoint_restrict_of_reducing T V hV hVstar]
  exact (isStarNormal_iff_norm_eq_adjoint.mp hT) x

lemma gram_restrict_of_reducing (T : E →L[ℝ] E) (μ : ℝ)
    (hgram : ∀ x, T.adjoint (T x) = μ • x)
    (V : Submodule ℝ E) [CompleteSpace V]
    (hV : ∀ ⦃x⦄, x ∈ V → T x ∈ V)
    (hVstar : ∀ ⦃x⦄, x ∈ V → T.adjoint x ∈ V) :
    ∀ x, (T.restrict hV).adjoint ((T.restrict hV) x) = μ • x := by
  intro x
  rw [adjoint_restrict_of_reducing T V hV hVstar]
  exact Subtype.ext (hgram x)

namespace Frame
variable {T : E →L[ℝ] E} {μ : ℝ}

/-- Transport a block of a reducing restriction back to the original real space. -/
def lift (V : Submodule ℝ E) [CompleteSpace V]
    (hV : ∀ ⦃x⦄, x ∈ V → T x ∈ V)
    (hVstar : ∀ ⦃x⦄, x ∈ V → T.adjoint x ∈ V)
    (F : Frame (T.restrict hV) μ) : Frame T μ where
  a := F.a
  b := F.b
  e := F.e
  f := F.f
  norm_e := F.norm_e
  line_or_plane := F.line_or_plane.imp (fun h => ⟨h.1, congrArg Subtype.val h.2⟩) id
  orthogonal := F.orthogonal
  apply_e := congrArg Subtype.val F.apply_e
  apply_f := congrArg Subtype.val F.apply_f
  adjoint_e := by
    have hh := F.adjoint_e
    rw [adjoint_restrict_of_reducing T V hV hVstar] at hh
    exact congrArg Subtype.val hh
  adjoint_f := by
    have hh := F.adjoint_f
    rw [adjoint_restrict_of_reducing T V hV hVstar] at hh
    exact congrArg Subtype.val hh
  modulus := F.modulus

lemma lift_space_le (V : Submodule ℝ E) [CompleteSpace V]
    (hV : ∀ ⦃x⦄, x ∈ V → T x ∈ V)
    (hVstar : ∀ ⦃x⦄, x ∈ V → T.adjoint x ∈ V)
    (F : Frame (T.restrict hV) μ) : (F.lift V hV hVstar).space ≤ V := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact F.e.property
  · have hh : x = (F.f : E) := Set.mem_singleton_iff.mp hx
    rw [hh]
    exact F.f.property

end Frame

/-- The sum of a family of actual one- or two-dimensional reducing blocks. -/
def sumSpaces {T : E →L[ℝ] E} {μ : ℝ} (s : Set (Frame T μ)) : Submodule ℝ E :=
  ⨆ F : s, F.val.space

lemma space_le_sumSpaces {T : E →L[ℝ] E} {μ : ℝ} {s : Set (Frame T μ)}
    {F : Frame T μ} (hF : F ∈ s) : F.space ≤ sumSpaces s :=
  le_iSup (fun F : s => F.val.space) ⟨F, hF⟩

lemma sumSpaces_invariant {T : E →L[ℝ] E} {μ : ℝ} (s : Set (Frame T μ))
    ⦃x : E⦄ (hx : x ∈ sumSpaces s) : T x ∈ sumSpaces s := by
  refine Submodule.iSup_induction (fun F : s => F.val.space) (motive := fun x => T x ∈ sumSpaces s) hx ?_ ?_ ?_
  · intro F x hx
    exact (space_le_sumSpaces F.property) (F.val.invariant hx)
  · simp
  · intro x y hx hy
    simpa using (sumSpaces s).add_mem hx hy

lemma sumSpaces_adjoint_invariant {T : E →L[ℝ] E} {μ : ℝ} (s : Set (Frame T μ))
    ⦃x : E⦄ (hx : x ∈ sumSpaces s) : T.adjoint x ∈ sumSpaces s := by
  refine Submodule.iSup_induction (fun F : s => F.val.space) (motive := fun x => T.adjoint x ∈ sumSpaces s) hx ?_ ?_ ?_
  · intro F x hx
    exact (space_le_sumSpaces F.property) (F.val.adjoint_invariant hx)
  · simp
  · intro x y hx hy
    simpa using (sumSpaces s).add_mem hx hy

lemma sumSpaces_orthogonal_invariant {T : E →L[ℝ] E} {μ : ℝ} (s : Set (Frame T μ))
    ⦃x : E⦄ (hx : x ∈ (sumSpaces s).orthogonal) : T x ∈ (sumSpaces s).orthogonal := by
  intro y hy
  rw [← T.adjoint_inner_left]
  exact hx _ (sumSpaces_adjoint_invariant s hy)

lemma sumSpaces_orthogonal_adjoint_invariant {T : E →L[ℝ] E} {μ : ℝ} (s : Set (Frame T μ))
    ⦃x : E⦄ (hx : x ∈ (sumSpaces s).orthogonal) : T.adjoint x ∈ (sumSpaces s).orthogonal := by
  intro y hy
  rw [T.adjoint_inner_right]
  exact hx _ (sumSpaces_invariant s hy)

lemma sumSpaces_insert {T : E →L[ℝ] E} {μ : ℝ} (s : Set (Frame T μ)) (F : Frame T μ) :
    sumSpaces (insert F s) = F.space ⊔ sumSpaces s := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨G, hG⟩
    rcases Set.mem_insert_iff.mp hG with hh | hh
    · subst G
      exact le_sup_left
    · exact (space_le_sumSpaces hh).trans le_sup_right
  · apply sup_le
    · exact space_le_sumSpaces (Set.mem_insert F s)
    · apply iSup_le
      intro G
      exact space_le_sumSpaces (Set.mem_insert_of_mem F G.property)

/-- The finite real spectral theorem on a fixed singular-value eigenspace.
The blocks are actual reducing lines or positive-speed oriented planes in E. -/
theorem finite_frames_of_gram_scalar [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : IsStarNormal T) (μ : ℝ)
    (hgram : ∀ x, T.adjoint (T x) = μ • x) :
    ∃ s : Set (Frame T μ), s.Finite ∧
      s.Pairwise (fun F G => F.space ⟂ G.space) ∧ sumSpaces s = ⊤ := by
  classical
  let S : Set (Submodule ℝ E) := {W | ∃ s : Set (Frame T μ), s.Finite ∧
    s.Pairwise (fun F G => F.space ⟂ G.space) ∧ sumSpaces s = W}
  have hSne : S.Nonempty := by
    refine ⟨⊥, ∅, Set.finite_empty, by simp, ?_⟩
    simp [sumSpaces]
  obtain ⟨W, hW⟩ := (inferInstance : WellFoundedGT (Submodule ℝ E)).exists_maximal S hSne
  obtain ⟨s, hsfinite, hspair, rfl⟩ := hW.prop
  refine ⟨s, hsfinite, hspair, ?_⟩
  by_contra htop
  let V := (sumSpaces s).orthogonal
  have hVne : V ≠ ⊥ := by
    intro hh
    exact htop (Submodule.orthogonal_eq_bot_iff.mp hh)
  letI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hVne
  let hV := sumSpaces_orthogonal_invariant s
  let hVstar := sumSpaces_orthogonal_adjoint_invariant s
  let R := T.restrict hV
  have hRnormal : IsStarNormal R := normal_restrict_of_reducing T hT V hV hVstar
  have hRgram : ∀ x, R.adjoint (R x) = μ • x :=
    gram_restrict_of_reducing T μ hgram V hV hVstar
  let F0 : Frame R μ := Classical.choice (exists_frame R hRnormal μ hRgram)
  let F : Frame T μ := F0.lift V hV hVstar
  have hFle : F.space ≤ (sumSpaces s).orthogonal := F0.lift_space_le V hV hVstar
  have hpair : (insert F s).Pairwise (fun F G => F.space ⟂ G.space) := by
    apply hspair.insert
    intro G hG _
    have hh : G.space ⟂ F.space :=
      ((Submodule.isOrtho_orthogonal_right (sumSpaces s)).mono_left
        (space_le_sumSpaces hG)).mono_right hFle
    exact ⟨hh.symm, hh⟩
  have hnew : F.space ⊔ sumSpaces s ∈ S :=
    ⟨insert F s, hsfinite.insert F, hpair, sumSpaces_insert s F⟩
  have heq : sumSpaces s = F.space ⊔ sumSpaces s := hW.eq_of_le hnew le_sup_right
  have hFsum : F.space ≤ sumSpaces s := le_sup_left.trans heq.ge
  apply F.space_ne_bot
  apply le_bot_iff.mp
  exact (le_inf hFsum hFle).trans (Submodule.inf_orthogonal_eq_bot _).le


end RealBlock

theorem real_rotation_plane_extraction : Spec.RealRotationPlaneExtraction.{v} := by
  intro H _ _ _ N hn μ a e he hg hs hne
  exact RealBlock.rotation_plane_of_gram_scalar N hn μ a e he hg hs hne

section RealMultiplicity
open Spec (pairOperator pairMultiplicity realEigenMultiplicity)
variable {H : Type v} {K : Type w}
 [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
 [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

lemma pair_intertwine (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (U : H ≃ₗᵢ[ℝ] K) (hU : ∀ x, U (N x) = M (U x)) (a b : ℝ) (x : H) :
 U (pairOperator N a b x) = pairOperator M a b (U x) := by
 simp only [pairOperator, add_apply, sub_apply,
  smul_apply, mul_apply_eq_comp, one_apply_eq_self,
  map_add, map_sub, map_smul, hU]

def pairKernelIsometry (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (U : H ≃ₗᵢ[ℝ] K) (hU : ∀ x, U (N x) = M (U x)) (a b : ℝ) :
 (pairOperator N a b).ker ≃ₗᵢ[ℝ] (pairOperator M a b).ker := by
 let f : (pairOperator N a b).ker →ₗᵢ[ℝ] (pairOperator M a b).ker :=
  { toFun := fun x => ⟨U x, by
      change pairOperator M a b (U (x : H)) = 0
      rw [← pair_intertwine N M U hU a b]
      rw [show pairOperator N a b (x : H) = 0 from x.property, map_zero]⟩
    map_add' := fun _ _ => Subtype.ext (U.map_add _ _)
    map_smul' := fun _ _ => Subtype.ext (U.map_smul _ _)
    norm_map' := fun _ => U.norm_map _ }
 apply LinearIsometryEquiv.ofSurjective f
 intro y
 refine ⟨⟨U.symm y, ?_⟩, ?_⟩
 · change pairOperator N a b (U.symm (y : K)) = 0
   apply U.injective
   rw [pair_intertwine N M U hU a b, U.apply_symm_apply]
   exact (show pairOperator M a b (y : K) = 0 from y.property).trans (map_zero U).symm
 · exact Subtype.ext (U.apply_symm_apply y)

lemma pairMultiplicity_intertwine (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (U : H ≃ₗᵢ[ℝ] K) (hU : ∀ x, U (N x) = M (U x)) (a b : ℝ) :
 pairMultiplicity N a b = pairMultiplicity M a b := by
 unfold pairMultiplicity
 rw [(pairKernelIsometry N M U hU a b).toLinearEquiv.finrank_eq]

lemma pairKernel_eq_eigenspace (N : H →L[ℝ] H) (a b : ℝ) :
 (pairOperator N a b).ker = Module.End.eigenspace
  (((2*a) • N - N*N).toLinearMap) (a*a+b*b) := by
 ext x
 rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
 change N (N x) - (2*a) • N x + (a*a+b*b) • x = 0 ↔
   (2*a) • N x - N (N x) = (a*a+b*b) • x
 constructor
 · intro h
   have hh := add_eq_zero_iff_eq_neg.mp h
   calc
    (2*a) • N x - N (N x) = -(N (N x) - (2*a) • N x) := by abel
    _ = (a*a+b*b) • x := by rw [hh, neg_neg]
 · intro h
   calc
    N (N x) - (2*a) • N x + (a*a+b*b) • x =
      -((2*a) • N x - N (N x)) + (a*a+b*b) • x := by abel
    _ = 0 := by rw [h]; abel

lemma pairKernel_finiteDimensional (N : H →L[ℝ] H) (hc : IsCompactOperator N)
 (a b : ℝ) (hb : 0 < b) : FiniteDimensional ℝ (pairOperator N a b).ker := by
 rw [pairKernel_eq_eigenspace]
 have hcc : IsCompactOperator ((2*a) • N - N*N : H →L[ℝ] H) := by
  exact (hc.smul (2*a)).sub (hc.comp_clm N)
 exact ContinuousLinearMap.finite_dimensional_eigenspace hcc (a*a+b*b) (by nlinarith [sq_nonneg a, sq_pos_of_pos hb])

lemma pairOperator_on_realEigenvector (N : H →L[ℝ] H) (a b μ : ℝ) (e : H)
 (he : N e = μ • e) :
 pairOperator N a b e = ((μ-a)^2+b^2) • e := by
 change N (N e) - (2*a) • N e + (a*a+b*b) • e = _
 rw [he, map_smul, he]
 module

lemma realEigenvector_not_mem_pairKernel (N : H →L[ℝ] H) (a b μ : ℝ) (hb : 0 < b)
 (e : H) (he : N e = μ • e) (hne : e ≠ 0) : e ∉ (pairOperator N a b).ker := by
 intro hx
 have hh : pairOperator N a b e = 0 := hx
 rw [pairOperator_on_realEigenvector N a b μ e he] at hh
 rcases smul_eq_zero.mp hh with h | h
 · nlinarith [sq_nonneg (μ-a), sq_pos_of_pos hb]
 · exact hne h

lemma pairOperator_on_plane_first (N : H →L[ℝ] H) (a b c d : ℝ) (e f : H)
 (he : N e = c • e + d • f) (hf : N f = (-d) • e + c • f) :
 pairOperator N a b e = ((c-a)^2+b^2-d^2) • e + (2*d*(c-a)) • f := by
 change N (N e) - (2*a) • N e + (a*a+b*b) • e = _
 rw [he, map_add, map_smul, map_smul, he, hf]
 module

lemma pairOperator_on_plane_second (N : H →L[ℝ] H) (a b c d : ℝ) (e f : H)
 (he : N e = c • e + d • f) (hf : N f = (-d) • e + c • f) :
 pairOperator N a b f = (-2*d*(c-a)) • e + ((c-a)^2+b^2-d^2) • f := by
 change N (N f) - (2*a) • N f + (a*a+b*b) • f = _
 rw [hf, map_add, map_smul, map_smul, he, hf]
 module

lemma plane_first_mem_pairKernel_iff (N : H →L[ℝ] H) (a b c d : ℝ) (hb : 0 < b)
 (hd : 0 < d) (e f : H) (he : N e = c • e + d • f)
 (hf : N f = (-d) • e + c • f) (he1 : ‖e‖ = 1) (hf1 : ‖f‖ = 1)
 (hef : ⟪e, f⟫_ℝ = 0) : e ∈ (pairOperator N a b).ker ↔ a = c ∧ b = d := by
 constructor
 · intro hx
   have hh : pairOperator N a b e = 0 := hx
   rw [pairOperator_on_plane_first N a b c d e f he hf] at hh
   have hp := congrArg (fun x : H => ⟪e, x⟫_ℝ) hh
   have ht := congrArg (fun x : H => ⟪f, x⟫_ℝ) hh
   simp only [inner_add_right, inner_smul_right, inner_zero_right,
    real_inner_self_eq_norm_sq, he1, hf1, hef, real_inner_comm e f] at hp ht
   have ht0 : 2*d*(c-a) = 0 := by simpa only [real_inner_comm e f, hef, mul_zero,
     zero_add, one_pow, mul_one] using ht
   have hca : c-a = 0 := (mul_eq_zero.mp ht0).resolve_left (by positivity)
   have hac : a = c := by linarith
   refine ⟨hac, ?_⟩
   subst c
   nlinarith
 · rintro ⟨rfl, rfl⟩
   change pairOperator N a b e = 0
   rw [pairOperator_on_plane_first N a b a b e f he hf]
   simp

lemma pairKernel_eq_bot_of_selfAdjoint (N : H →L[ℝ] H) (hN : IsSelfAdjoint N)
 (a b : ℝ) (hb : 0 < b) : (pairOperator N a b).ker = ⊥ := by
 apply bot_unique
 intro x hx
 have hqx : pairOperator N a b x = 0 := hx
 have hi := congrArg (fun y : H => ⟪x, y⟫_ℝ) hqx
 change ⟪x, N (N x) - (2*a) • N x + (a*a+b*b) • x⟫_ℝ = _ at hi
 have hsym : ⟪x, N (N x)⟫_ℝ = ‖N x‖^2 := by
   have hs := hN.isSymmetric x (N x)
   change ⟪N x, N x⟫_ℝ = ⟪x, N (N x)⟫_ℝ at hs
   rw [← hs, real_inner_self_eq_norm_sq]
 simp only [inner_add_right, inner_sub_right, inner_smul_right,
   inner_zero_right, real_inner_self_eq_norm_sq, hsym] at hi
 have hs := norm_sub_sq_real (N x) (a • x)
 rw [inner_smul_right, real_inner_comm x (N x), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hs
 have hle : b^2 * ‖x‖^2 ≤ 0 := by
   nlinarith [sq_nonneg ‖N x - a • x‖]
 have hx0 : ‖x‖^2 ≤ 0 := nonpos_of_mul_nonpos_right hle (sq_pos_of_pos hb)
 have hzero : ‖x‖ = 0 := by nlinarith
 exact (Submodule.mem_bot ℝ).mpr (norm_eq_zero.mp hzero)


open ExpandedFA.CompactSpectral.CompactNormalClassification

lemma realEigenMultiplicity_intertwine (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (U : H ≃ₗᵢ[ℝ] K) (hU : ∀ x, U (N x) = M (U x)) (r : ℝ) :
 Cardinal.lift.{w} (realEigenMultiplicity N r) =
 Cardinal.lift.{v} (realEigenMultiplicity M r) := by
 letI : CompleteSpace (Module.End.eigenspace N.toLinearMap r) :=
   (N.isClosed_eigenspace r).completeSpace_coe
 letI : CompleteSpace (Module.End.eigenspace M.toLinearMap r) :=
   (M.isClosed_eigenspace r).completeSpace_coe
 exact (dimension_classification ℝ _ _).mp ⟨eigenspaceIsometry N M U hU r⟩

lemma realClassification_necessary (N : H →L[ℝ] H) (M : K →L[ℝ] K) :
 (∃ U : H ≃ₗᵢ[ℝ] K, ∀ x, U (N x) = M (U x)) →
 (∀ r : ℝ, Cardinal.lift.{w} (realEigenMultiplicity N r) =
   Cardinal.lift.{v} (realEigenMultiplicity M r)) ∧
 (∀ a b : ℝ, 0 < b → pairMultiplicity N a b = pairMultiplicity M a b) := by
 rintro ⟨U, hU⟩
 exact ⟨realEigenMultiplicity_intertwine N M U hU,
   fun a b _ => pairMultiplicity_intertwine N M U hU a b⟩


end RealMultiplicity

namespace RealBlockTails
open scoped Topology


variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : I → Submodule ℝ H) [∀ i, (V i).HasOrthogonalProjection]

lemma projection_bessel (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (x : H) (s : Finset I) :
    ∑ i ∈ s, ‖(V i).orthogonalProjectionOnto x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let p : ∀ i, V i := fun i => (V i).orthogonalProjectionOnto x
  have hn := ho.norm_sum p s
  have hi : inner ℝ x (∑ i ∈ s, (V i).subtypeₗᵢ (p i)) =
      ∑ i ∈ s, ‖(V i).orthogonalProjectionOnto x‖ ^ 2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hp := (V i).inner_orthogonalProjectionOnto_eq_of_mem_left (p i) x
    change inner ℝ x (p i : H) = ‖(V i).orthogonalProjectionOnto x‖ ^ 2
    rw [real_inner_comm, ← hp]
    exact real_inner_self_eq_norm_sq _
  have hnon := sq_nonneg ‖x - ∑ i ∈ s, (V i).subtypeₗᵢ (p i)‖
  rw [norm_sub_sq_real, hn, hi] at hnon
  change 0 ≤ ‖x‖ ^ 2 - 2 * (∑ i ∈ s, ‖(V i).orthogonalProjectionOnto x‖ ^ 2) +
    (∑ i ∈ s, ‖(V i).orthogonalProjectionOnto x‖ ^ 2) at hnon
  linarith

lemma norm_block_sum_le (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (T : H →L[ℝ] H) (hinv : ∀ i, ∀ y ∈ V i, T y ∈ V i)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hscale : ∀ i, ∀ y ∈ V i, ‖T y‖ = r i * ‖y‖)
    (c : ℝ) (hc : 0 ≤ c) (x : H) (s : Finset I) (hbound : ∀ i ∈ s, r i ≤ c) :
    ‖∑ i ∈ s, T ((V i).starProjection x)‖ ≤ c * ‖x‖ := by
  let p : ∀ i, V i := fun i => (V i).orthogonalProjectionOnto x
  let q : ∀ i, V i := fun i => ⟨T (p i), hinv i (p i) (p i).property⟩
  have hn := ho.norm_sum q s
  have hnorm : ‖∑ i ∈ s, T ((V i).starProjection x)‖ ^ 2 =
      ∑ i ∈ s, (r i * ‖(V i).orthogonalProjectionOnto x‖) ^ 2 := by
    calc
      _ = ∑ i ∈ s, ‖q i‖ ^ 2 := by
        change ‖∑ i ∈ s, T ((V i).starProjection x)‖ ^ 2 = ∑ i ∈ s, ‖q i‖ ^ 2 at hn
        exact hn
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        change ‖T (p i : H)‖ ^ 2 = (r i * ‖(V i).orthogonalProjectionOnto x‖) ^ 2
        rw [hscale i (p i) (p i).property]
        rfl
  have hle : (∑ i ∈ s, (r i * ‖(V i).orthogonalProjectionOnto x‖) ^ 2) ≤
      c ^ 2 * (∑ i ∈ s, ‖(V i).orthogonalProjectionOnto x‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (sq_le_sq₀ (hr i) hc |>.mpr (hbound i hi)) (sq_nonneg _)
  have hb := projection_bessel V ho x s
  have hle' := hle.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg c))
  rw [← hnorm] at hle'
  have hprod : 0 ≤ c * ‖x‖ := mul_nonneg hc (norm_nonneg x)
  nlinarith [norm_nonneg (∑ i ∈ s, T ((V i).starProjection x))]

lemma hasSum_omitted {E J : Type*} [NormedAddCommGroup E] [DecidableEq J]
    {f : J → E} {a : E} (hf : HasSum f a) (s : Finset J) :
    HasSum (fun i => if i ∈ s then 0 else f i) (a - ∑ i ∈ s, f i) := by
  classical
  have hfinite : HasSum (fun i => if i ∈ s then f i else 0) (∑ i ∈ s, f i) := by
    convert (hasSum_sum (fun j (_ : j ∈ s) => hasSum_ite_eq j (f j))) using 1
    funext i
    simp
  convert hf.sub hfinite using 1
  funext i
  split_ifs <;> simp

lemma norm_block_remainder_le
    (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (T : H →L[ℝ] H) (hinv : ∀ i, ∀ y ∈ V i, T y ∈ V i)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hscale : ∀ i, ∀ y ∈ V i, ‖T y‖ = r i * ‖y‖)
    (hexpand : ∀ x, HasSum (fun i => T ((V i).starProjection x)) (T x))
    (c : ℝ) (hc : 0 ≤ c) (s : Finset I) (hbound : ∀ i ∉ s, r i ≤ c) :
    ‖T - ∑ i ∈ s, T.comp (V i).starProjection‖ ≤ c := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hs := hasSum_omitted (hexpand x) s
  have hs' := hs.norm
  change Tendsto (fun t : Finset I => ‖∑ i ∈ t, if i ∈ s then 0 else T ((V i).starProjection x)‖)
    atTop (𝓝 ‖T x - ∑ i ∈ s, T ((V i).starProjection x)‖) at hs'
  have hbound' (t : Finset I) :
      ‖∑ i ∈ t, if i ∈ s then 0 else T ((V i).starProjection x)‖ ≤ c * ‖x‖ := by
    have he : (∑ i ∈ t, if i ∈ s then 0 else T ((V i).starProjection x)) =
        ∑ i ∈ t \ s, T ((V i).starProjection x) := by
      calc
        _ = ∑ i ∈ t \ s, if i ∈ s then 0 else T ((V i).starProjection x) := by
          symm
          apply Finset.sum_subset Finset.sdiff_subset
          intro i hi hnot
          have his : i ∈ s := by simpa [Finset.mem_sdiff, hi] using hnot
          simp [his]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [Finset.mem_sdiff.mp hi |>.2]
    rw [he]
    exact norm_block_sum_le V ho T hinv r hr hscale c hc x (t \ s)
      (fun i hi => hbound i (Finset.mem_sdiff.mp hi).2)
  have hnorm := le_of_tendsto hs' (Filter.Eventually.of_forall hbound')
  simpa only [sub_apply, sum_apply,
    ContinuousLinearMap.comp_apply] using hnorm

omit [∀ i, (V i).HasOrthogonalProjection] in
lemma modulus_le_opNorm (T : H →L[ℝ] H) (r : I → ℝ)
    (hne : ∀ i, V i ≠ ⊥) (hscale : ∀ i, ∀ y ∈ V i, ‖T y‖ = r i * ‖y‖) (i : I) :
    r i ≤ ‖T‖ := by
  obtain ⟨y, hy, hy0⟩ := (V i).ne_bot_iff.mp (hne i)
  have he := T.le_opNorm y
  rw [hscale i y hy] at he
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hy0)).mp he

lemma omitted_modulus_le_remainder_norm
    (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (T : H →L[ℝ] H) (r : I → ℝ) (hne : ∀ i, V i ≠ ⊥)
    (hscale : ∀ i, ∀ y ∈ V i, ‖T y‖ = r i * ‖y‖)
    (s : Finset I) (i : I) (hi : i ∉ s) :
    r i ≤ ‖T - ∑ j ∈ s, T.comp (V j).starProjection‖ := by
  classical
  obtain ⟨y, hy, hy0⟩ := (V i).ne_bot_iff.mp (hne i)
  have hp (j : I) (hj : j ∈ s) : (V j).starProjection y = 0 := by
    apply ((V j).starProjection_apply_eq_zero_iff).mpr
    intro z hz
    have hji : j ≠ i := by rintro rfl; exact hi hj
    exact ho hji ⟨z, hz⟩ ⟨y, hy⟩
  have hsum : (∑ j ∈ s, T.comp (V j).starProjection) y = 0 := by
    simp only [sum_apply, ContinuousLinearMap.comp_apply]
    exact Finset.sum_eq_zero (fun j hj => by rw [hp j hj, map_zero])
  have hle := (T - ∑ j ∈ s, T.comp (V j).starProjection).le_opNorm y
  rw [sub_apply, hsum, sub_zero, hscale i y hy] at hle
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hy0)).mp hle

lemma real_sSup_le_of_nonneg {S : Set ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ r ∈ S, r ≤ c) : sSup S ≤ c := by
  rcases S.eq_empty_or_nonempty with hs | hs
  · simpa [hs] using hc
  · exact csSup_le hs hbound

lemma norm_block_remainder_eq_sSup
    (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (T : H →L[ℝ] H) (hinv : ∀ i, ∀ y ∈ V i, T y ∈ V i)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (hne : ∀ i, V i ≠ ⊥)
    (hscale : ∀ i, ∀ y ∈ V i, ‖T y‖ = r i * ‖y‖)
    (hexpand : ∀ x, HasSum (fun i => T ((V i).starProjection x)) (T x))
    (s : Finset I) :
    ‖T - ∑ i ∈ s, T.comp (V i).starProjection‖ = sSup (r '' {i | i ∉ s}) := by
  have hbdd : BddAbove (r '' {i | i ∉ s}) := by
    refine ⟨‖T‖, ?_⟩
    rintro _ ⟨i, hi, rfl⟩
    exact modulus_le_opNorm V T r hne hscale i
  have hnonneg : 0 ≤ sSup (r '' {i | i ∉ s}) := by
    rcases (r '' {i | i ∉ s}).eq_empty_or_nonempty with hs | ⟨c, hc⟩
    · simp [hs]
    · obtain ⟨i, hi, rfl⟩ := hc
      exact (hr i).trans (le_csSup hbdd ⟨i, hi, rfl⟩)
  apply le_antisymm
  · exact norm_block_remainder_le V ho T hinv r hr hscale hexpand _ hnonneg s
      (fun i hi => le_csSup hbdd ⟨i, hi, rfl⟩)
  · apply real_sSup_le_of_nonneg (norm_nonneg _)
    rintro _ ⟨i, hi, rfl⟩
    exact omitted_modulus_le_remainder_norm V ho T r hne hscale s i hi

lemma operator_block_expansion
    (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (T : H →L[ℝ] H) (hinv : ∀ i, ∀ y ∈ V i, T y ∈ V i)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hscale : ∀ i, ∀ y ∈ V i, ‖T y‖ = r i * ‖y‖)
    (hexpand : ∀ x, HasSum (fun i => T ((V i).starProjection x)) (T x))
    (hfinite : ∀ ε : ℝ, 0 < ε → {i | ε ≤ r i}.Finite) :
    HasSum (fun i => T.comp (V i).starProjection) T := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hfin := hfinite (ε / 2) (by positivity)
  refine ⟨hfin.toFinset, ?_⟩
  intro s hs
  rw [dist_eq_norm, norm_sub_rev]
  apply lt_of_le_of_lt (norm_block_remainder_le V ho T hinv r hr hscale hexpand
    (ε / 2) (by positivity) s ?_) (half_lt_self hε)
  intro i hi
  apply le_of_lt
  by_contra! hge
  exact hi (hs (hfin.mem_toFinset.mpr hge))

lemma block_vector_expansion_of_total [CompleteSpace H]
    (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (T : H →L[ℝ] H)
    (htotal : ((⨆ i, V i).topologicalClosure).orthogonal ≤ T.ker) (x : H) :
    HasSum (fun i => T ((V i).starProjection x)) (T x) := by
  classical
  let p : ∀ i, V i := fun i => (V i).orthogonalProjectionOnto x
  have hs : Summable (fun i => (V i).subtypeₗᵢ (p i)) := by
    apply (ho.summable_iff_norm_sq_summable p).mpr
    refine summable_of_sum_le (c := ‖x‖ ^ 2) (fun i => sq_nonneg _) ?_
    intro s
    exact projection_bessel V ho x s
  obtain ⟨y, hy⟩ := hs
  have hinner (i : I) (z : V i) : inner ℝ (z : H) y = inner ℝ (z : H) x := by
    have hs' := (innerSL ℝ (z : H)).hasSum hy
    have hs'' : HasSum (fun j => inner ℝ (z : H) ((V j).subtypeₗᵢ (p j)))
        (inner ℝ (z : H) x) := by
      convert hasSum_ite_eq i (inner ℝ (z : H) x) using 1
      funext j
      by_cases hj : j = i
      · subst j
        simp only [ite_true]
        change inner ℝ (z : H) ((V i).starProjection x) = inner ℝ (z : H) x
        rw [Submodule.starProjection_apply]
        exact (V i).inner_orthogonalProjectionOnto_eq_of_mem_left z x
      · simp only [ite_eq_right hj]
        exact ho (Ne.symm hj) z (p j)
    exact hs'.unique hs''
  have hxy : x - y ∈ ((⨆ i, V i).topologicalClosure).orthogonal := by
    rw [Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal]
    apply (Submodule.mem_iInf _).mpr
    intro i z hz
    rw [inner_sub_right, hinner i ⟨z, hz⟩, sub_self]
  have hker : T (x - y) = 0 := htotal hxy
  have hTy : T y = T x := by
    rw [map_sub, sub_eq_zero] at hker
    exact hker.symm
  have ht := hy.map T T.continuous
  change HasSum (fun i => T ((V i).starProjection x)) (T y) at ht
  rwa [hTy] at ht

lemma orthonormal_pair_combination_norm_sq (e f : H) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (u v : ℝ) : ‖u • e + v • f‖ ^ 2 = u ^ 2 + v ^ 2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, he, hf, inner_smul_left, inner_smul_right, hef, Real.norm_eq_abs]

lemma rotation_plane_norm_scale (T : H →L[ℝ] H) (e f : H) (a b : ℝ)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    (hTe : T e = a • e + b • f) (hTf : T f = (-b) • e + a • f) (u v : ℝ) :
    ‖T (u • e + v • f)‖ = Real.sqrt (a ^ 2 + b ^ 2) * ‖u • e + v • f‖ := by
  have hcombine : T (u • e + v • f) = (a * u - b * v) • e + (b * u + a * v) • f := by
    rw [map_add, map_smul, map_smul, hTe, hTf]
    simp only [smul_add, smul_smul]
    module
  have hsq : ‖T (u • e + v • f)‖ ^ 2 =
      (a ^ 2 + b ^ 2) * ‖u • e + v • f‖ ^ 2 := by
    rw [hcombine, orthonormal_pair_combination_norm_sq e f he hf hef,
      orthonormal_pair_combination_norm_sq e f he hf hef]
    ring
  have hsqrt : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hnon : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) * ‖u • e + v • f‖ := by positivity
  nlinarith [norm_nonneg (T (u • e + v • f))]

lemma block_projection_expansion [CompleteSpace H]
    (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ)) (x : H) :
    HasSum (fun i => (V i).starProjection x)
      ((⨆ i, V i).topologicalClosure.starProjection x) := by
  classical
  let M := (⨆ i, V i).topologicalClosure
  let p : ∀ i, V i := fun i => (V i).orthogonalProjectionOnto x
  have hs : Summable (fun i => (V i).subtypeₗᵢ (p i)) := by
    apply (ho.summable_iff_norm_sq_summable p).mpr
    refine summable_of_sum_le (c := ‖x‖ ^ 2) (fun i => sq_nonneg _) ?_
    intro s
    exact projection_bessel V ho x s
  obtain ⟨y, hy⟩ := hs
  have hinner (i : I) (z : V i) : inner ℝ (z : H) y = inner ℝ (z : H) x := by
    have hs' := (innerSL ℝ (z : H)).hasSum hy
    have hs'' : HasSum (fun j => inner ℝ (z : H) ((V j).subtypeₗᵢ (p j)))
        (inner ℝ (z : H) x) := by
      convert hasSum_ite_eq i (inner ℝ (z : H) x) using 1
      funext j
      by_cases hj : j = i
      · subst j
        simp only [ite_true]
        change inner ℝ (z : H) ((V i).starProjection x) = inner ℝ (z : H) x
        rw [Submodule.starProjection_apply]
        exact (V i).inner_orthogonalProjectionOnto_eq_of_mem_left z x
      · simp only [ite_eq_right hj]
        exact ho (Ne.symm hj) z (p j)
    exact hs'.unique hs''
  have hxy : x - y ∈ M.orthogonal := by
    dsimp [M]
    rw [Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal]
    apply (Submodule.mem_iInf _).mpr
    intro i z hz
    rw [inner_sub_right, hinner i ⟨z, hz⟩, sub_self]
  have hym : y ∈ M := by
    apply (Submodule.isClosed_topologicalClosure (⨆ i, V i)).mem_of_tendsto hy
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.le_topologicalClosure _ (le_iSup V i (p i).property)
  have hyproj : y = M.starProjection x := (M.eq_starProjection_of_mem_orthogonal hym hxy).symm
  change HasSum (fun i => (V i).starProjection x) y at hy
  rwa [hyproj] at hy

lemma ordered_operator_block_expansion
    (ho : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (T : H →L[ℝ] H) (hinv : ∀ i, ∀ y ∈ V i, T y ∈ V i)
    (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (hscale : ∀ i, ∀ y ∈ V i, ‖T y‖ = r i * ‖y‖)
    (hexpand : ∀ x, HasSum (fun i => T ((V i).starProjection x)) (T x))
    (hfinite : ∀ ε : ℝ, 0 < ε → {i | ε ≤ r i}.Finite) :
    ∃ s : ℕ → Finset I, Monotone s ∧ (∀ i, ∃ n, i ∈ s n) ∧
      (∀ n i, i ∈ s n → ∀ j, j ∉ s n → r j ≤ r i) ∧
      Tendsto (fun n => ∑ i ∈ s n, T.comp (V i).starProjection) atTop (𝓝 T) := by
  classical
  let A (n : ℕ) : Set I := {i | 1 / (n + 1 : ℝ) ≤ r i}
  have hA (n : ℕ) : (A n).Finite := hfinite _ (by positivity)
  let s (n : ℕ) : Finset I := (hA n).toFinset
  have hmem (n : ℕ) (i : I) : i ∈ s n ↔ 1 / (n + 1 : ℝ) ≤ r i := (hA n).mem_toFinset
  have hmono : Monotone s := by
    intro n m hnm i hi
    apply (hmem m i).mpr
    apply le_trans ?_ ((hmem n i).mp hi)
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have homitted (n : ℕ) (j : I) (hj : j ∉ s n) : r j < 1 / (n + 1 : ℝ) := by
    by_contra! hh
    exact hj ((hmem n j).mpr hh)
  refine ⟨s, hmono, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hr i)
    exact ⟨n, (hmem n i).mpr hn.le⟩
  · intro n i hi j hj
    exact (homitted n j hj).le.trans ((hmem n i).mp hi)
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, ?_⟩
    intro m hnm
    rw [dist_eq_norm, norm_sub_rev]
    apply lt_of_le_of_lt (norm_block_remainder_le V ho T hinv r (fun i => (hr i).le)
      hscale hexpand (1 / (n + 1 : ℝ)) (by positivity) (s m) ?_) hn
    intro j hj
    have hj' : j ∉ s n := fun h => hj (hmono hnm h)
    exact (homitted n j hj').le


end RealBlockTails


theorem real_classification_necessary : Spec.RealClassificationNecessary.{v,w} := by
  intro H K _ _ _ _ _ _ N M
  exact realClassification_necessary N M

theorem real_pairKernel_finite : Spec.RealPairKernelFinite.{v} := by
  intro H _ _ _ N hc a b hb
  exact pairKernel_finiteDimensional N
    ((Compactness.compact_iff_isCompactOperator _).mp hc) a b hb

theorem selfAdjoint_pairKernel_zero : Spec.SelfAdjointPairKernelZero.{v} := by
  intro H _ _ _ N hn a b hb
  exact pairKernel_eq_bot_of_selfAdjoint N hn a b hb

theorem real_orthogonal_block_expansion : Spec.RealOrthogonalBlockExpansion.{v,w} := by
  intro H ι _ _ _ V _ ho N hinv r hr hne hscale htotal hfinite
  have hexpand := RealBlockTails.block_vector_expansion_of_total V ho N htotal
  exact ⟨hexpand,
    RealBlockTails.norm_block_remainder_eq_sSup V ho N hinv r (fun i => (hr i).le)
      hne hscale hexpand,
    RealBlockTails.operator_block_expansion V ho N hinv r (fun i => (hr i).le)
      hscale hexpand hfinite,
    RealBlockTails.ordered_operator_block_expansion V ho N hinv r hr
      hscale hexpand hfinite⟩

namespace GlobalReal
open ContinuousLinearMap
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev GramEigenvalues (N : H →L[ℝ] H) := SelfAdjointNonzeroEigenvalues (gramOperator N)
abbrev GramSpace (N : H →L[ℝ] H) (r : GramEigenvalues N) :=
  Module.End.eigenspace (gramOperator N).toLinearMap r.val

instance gramSpaceComplete (N : H →L[ℝ] H) (r : GramEigenvalues N) :
    CompleteSpace (GramSpace N r) :=
  ((gramOperator N).isClosed_eigenspace r.val).completeSpace_coe

lemma gramInvariant (N : H →L[ℝ] H) (hn : IsStarNormal N) (r : GramEigenvalues N)
    ⦃x : H⦄ (hx : x ∈ GramSpace N r) : N x ∈ GramSpace N r :=
  maps_eigenspace_of_commute _ _ (gramOperator_commute N hn) r.val x hx

lemma gramAdjointInvariant (N : H →L[ℝ] H) (hn : IsStarNormal N) (r : GramEigenvalues N)
    ⦃x : H⦄ (hx : x ∈ GramSpace N r) : N.adjoint x ∈ GramSpace N r :=
  maps_eigenspace_of_commute _ _ (gramOperator_adjoint_commute N hn) r.val x hx

def gramRestrict (N : H →L[ℝ] H) (hn : IsStarNormal N) (r : GramEigenvalues N) :
    GramSpace N r →L[ℝ] GramSpace N r := N.restrict (gramInvariant N hn r)

lemma gramRestrict_normal (N : H →L[ℝ] H) (hn : IsStarNormal N) (r : GramEigenvalues N) :
    IsStarNormal (gramRestrict N hn r) :=
  RealBlock.normal_restrict_of_reducing N hn _ (gramInvariant N hn r) (gramAdjointInvariant N hn r)

lemma gramRestrict_gram (N : H →L[ℝ] H) (hn : IsStarNormal N) (r : GramEigenvalues N) :
    ∀ x, (gramRestrict N hn r).adjoint (gramRestrict N hn r x) = r.val • x := by
  intro x
  rw [gramRestrict, RealBlock.adjoint_restrict_of_reducing N _
    (gramInvariant N hn r) (gramAdjointInvariant N hn r)]
  exact Subtype.ext (Module.End.mem_eigenspace_iff.mp x.property)

lemma finiteGramFrames_exists (N : H →L[ℝ] H) (hc : IsCompactOperator N)
    (hn : IsStarNormal N) (r : GramEigenvalues N) :
    ∃ s : Set (RealBlock.Frame (gramRestrict N hn r) r.val), s.Finite ∧
      s.Pairwise (fun F G => F.space ⟂ G.space) ∧ RealBlock.sumSpaces s = ⊤ := by
  letI := (gramOperator N).finite_dimensional_eigenspace (gramOperator_compact N hc) r.val r.property.2
  exact RealBlock.finite_frames_of_gram_scalar _ (gramRestrict_normal N hn r) _
    (gramRestrict_gram N hn r)

def finiteGramFrames (N : H →L[ℝ] H) (hc : IsCompactOperator N)
    (hn : IsStarNormal N) (r : GramEigenvalues N) :
    Set (RealBlock.Frame (gramRestrict N hn r) r.val) :=
  Classical.choose (finiteGramFrames_exists N hc hn r)

lemma finiteGramFrames_finite (N : H →L[ℝ] H) (hc : IsCompactOperator N)
    (hn : IsStarNormal N) (r : GramEigenvalues N) :
    (finiteGramFrames N hc hn r).Finite :=
  (Classical.choose_spec (finiteGramFrames_exists N hc hn r)).1

lemma finiteGramFrames_pairwise (N : H →L[ℝ] H) (hc : IsCompactOperator N)
    (hn : IsStarNormal N) (r : GramEigenvalues N) :
    (finiteGramFrames N hc hn r).Pairwise (fun F G => F.space ⟂ G.space) :=
  (Classical.choose_spec (finiteGramFrames_exists N hc hn r)).2.1

lemma finiteGramFrames_total (N : H →L[ℝ] H) (hc : IsCompactOperator N)
    (hn : IsStarNormal N) (r : GramEigenvalues N) :
    RealBlock.sumSpaces (finiteGramFrames N hc hn r) = ⊤ :=
  (Classical.choose_spec (finiteGramFrames_exists N hc hn r)).2.2

abbrev FrameIndex (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N) :=
  (r : GramEigenvalues N) × finiteGramFrames N hc hn r

def globalFrame (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N)
    (i : FrameIndex N hc hn) : RealBlock.Frame N i.1.val :=
  i.2.val.lift (GramSpace N i.1) (gramInvariant N hn i.1) (gramAdjointInvariant N hn i.1)

lemma globalFrame_le_gramSpace (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N)
    (i : FrameIndex N hc hn) : (globalFrame N hc hn i).space ≤ GramSpace N i.1 :=
  i.2.val.lift_space_le _ _ _

lemma frameIndex_countable (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N) :
    Countable (FrameIndex N hc hn) := by
  letI : Countable (GramEigenvalues N) := selfAdjointNonzeroEigenvalues_countable (gramOperator N)
    ((Compactness.compact_iff_isCompactOperator _).mpr (gramOperator_compact N hc))
  letI : ∀ r : GramEigenvalues N, Finite (finiteGramFrames N hc hn r) :=
    fun r => (finiteGramFrames_finite N hc hn r).to_subtype
  exact inferInstance

lemma lift_space_eq_map {T : H →L[ℝ] H} {μ : ℝ} (V : Submodule ℝ H) [CompleteSpace V]
    (hV : ∀ ⦃x⦄, x ∈ V → T x ∈ V)
    (hVstar : ∀ ⦃x⦄, x ∈ V → T.adjoint x ∈ V)
    (F : RealBlock.Frame (T.restrict hV) μ) :
    (F.lift V hV hVstar).space = F.space.map V.subtype := by
  simp [RealBlock.Frame.space, RealBlock.Frame.lift, Submodule.map_span, Set.image_insert_eq]

lemma globalFrame_total_per_eigenvalue (N : H →L[ℝ] H) (hc : IsCompactOperator N)
    (hn : IsStarNormal N) (r : GramEigenvalues N) :
    (⨆ F : finiteGramFrames N hc hn r, (globalFrame N hc hn ⟨r, F⟩).space) = GramSpace N r := by
  simp only [globalFrame, gramRestrict]
  simp_rw [lift_space_eq_map, ← Submodule.map_iSup]
  change (RealBlock.sumSpaces (finiteGramFrames N hc hn r)).map (GramSpace N r).subtype = _
  rw [finiteGramFrames_total, Submodule.map_subtype_top]

lemma globalFrame_pairwise (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N) :
    Pairwise (fun i j : FrameIndex N hc hn =>
      (globalFrame N hc hn i).space ⟂ (globalFrame N hc hn j).space) := by
  intro i j hij
  by_cases hr : i.1 = j.1
  · rcases i with ⟨r, F⟩
    rcases j with ⟨q, G⟩
    dsimp only at hr
    subst q
    have hFG : F.val ≠ G.val := by
      intro hh
      apply hij
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hh))
    have hh := (finiteGramFrames_pairwise N hc hn r) F.property G.property hFG
    have hcoe : ((GramSpace N r).subtypeₗᵢ : GramSpace N r →ₗ[ℝ] H) = (GramSpace N r).subtype := by
      ext x
      rfl
    simpa only [globalFrame, gramRestrict, lift_space_eq_map, hcoe] using
      hh.map (GramSpace N r).subtypeₗᵢ
  · have hval : i.1.val ≠ j.1.val := by exact fun hh => hr (Subtype.ext hh)
    have hh := (gramOperator_selfAdjoint N).isSymmetric.orthogonalFamily_eigenspaces.isOrtho hval
    exact (hh.mono_left (globalFrame_le_gramSpace N hc hn i)).mono_right
      (globalFrame_le_gramSpace N hc hn j)

lemma globalFrame_iSup (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N) :
    (⨆ i : FrameIndex N hc hn, (globalFrame N hc hn i).space) =
      ⨆ r : {r : ℝ // r ≠ 0}, Module.End.eigenspace (gramOperator N).toLinearMap r.val := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact (globalFrame_le_gramSpace N hc hn i).trans
      (le_iSup (fun r : {r : ℝ // r ≠ 0} =>
        Module.End.eigenspace (gramOperator N).toLinearMap r.val) ⟨i.1.val, i.1.property.2⟩)
  · apply iSup_le
    intro r
    by_cases hr : Module.End.HasEigenvalue (gramOperator N).toLinearMap r.val
    · let q : GramEigenvalues N := ⟨r.val, hr, r.property⟩
      change GramSpace N q ≤ _
      rw [← globalFrame_total_per_eigenvalue N hc hn q]
      apply iSup_le
      intro F
      exact le_iSup (fun i : FrameIndex N hc hn => (globalFrame N hc hn i).space) ⟨q, F⟩
    · have hbot : Module.End.eigenspace (gramOperator N).toLinearMap r.val = ⊥ :=
        not_not.mp (fun hh => hr (Module.End.hasEigenvalue_iff.mpr hh))
      rw [hbot]
      exact bot_le

lemma globalFrame_closedSpan (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N) :
    (⨆ i : FrameIndex N hc hn, (globalFrame N hc hn i).space).topologicalClosure = N.ker.orthogonal := by
  rw [globalFrame_iSup]
  exact gramOperator_closedSpan N hc

lemma globalFrame_positive (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N)
    (i : FrameIndex N hc hn) : 0 < i.1.val :=
  gramOperator_eigenvalue_pos N _ i.1.property.1 i.1.property.2

lemma globalFrame_finite_away (N : H →L[ℝ] H)
    (hcompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap)
    (hc : IsCompactOperator N) (hn : IsStarNormal N) (ε : ℝ) (hε : 0 < ε) :
    {i : FrameIndex N hc hn | ε ≤ Real.sqrt i.1.val}.Finite := by
  let S : Set (GramEigenvalues N) := {r | ε ≤ Real.sqrt r.val}
  have hfin := gramOperator_finite_away N hcompact ε hε
  have hS : S.Finite := by
    apply (hfin.preimage Subtype.val_injective.injOn).subset
    intro r hr
    exact ⟨r.property.1, hr⟩
  have hF (r : GramEigenvalues N) : (Set.univ : Set (finiteGramFrames N hc hn r)).Finite := by
    letI : Finite (finiteGramFrames N hc hn r) := (finiteGramFrames_finite N hc hn r).to_subtype
    exact Set.toFinite _
  apply (hS.sigma (fun r _ => hF r)).subset
  intro i hi
  exact ⟨hi, Set.mem_univ _⟩


end GlobalReal

namespace RealBlockDataAnalysis
open scoped Topology
open ExpandedFA.CompactSpectral.CompactNormalClassification.Spec
open ExpandedFA.CompactSpectral.CompactNormalClassification.RealBlockTails
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {N : H →L[ℝ] H} (D : RealBlockData N)

abbrev BlockIndex := D.LineIndex ⊕ D.PlaneIndex
abbrev CoordinateIndex := D.LineIndex ⊕ (D.PlaneIndex × Bool)
def vectors : CoordinateIndex D → H :=
  Sum.elim D.line (fun q => if q.2 then D.second q.1 else D.first q.1)
def coordinateBlock : CoordinateIndex D → BlockIndex D := Sum.elim Sum.inl (fun q => Sum.inr q.1)
def generators : BlockIndex D → Set H :=
  Sum.elim (fun i => {D.line i}) (fun j => {D.first j, D.second j})
def blockSpace (i : BlockIndex D) : Submodule ℝ H := Submodule.span ℝ (generators D i)

lemma mem_generators_iff (i : BlockIndex D) (x : H) :
    x ∈ generators D i ↔ ∃ p : CoordinateIndex D, coordinateBlock D p = i ∧ vectors D p = x := by
  cases i with
  | inl i =>
    constructor
    · intro hx
      refine ⟨Sum.inl i, rfl, ?_⟩
      exact (Set.mem_singleton_iff.mp hx).symm
    · rintro ⟨p, hp, rfl⟩
      cases p with
      | inl j =>
        have hji : j = i := Sum.inl.inj hp
        subst j
        exact Set.mem_singleton _
      | inr q => cases hp
  | inr j =>
    constructor
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · exact ⟨Sum.inr (j, false), rfl, hx.symm⟩
      · exact ⟨Sum.inr (j, true), rfl, (Set.mem_singleton_iff.mp hx).symm⟩
    · rintro ⟨p, hp, rfl⟩
      cases p with
      | inl i => cases hp
      | inr q =>
        have hq : q.1 = j := Sum.inr.inj hp
        rcases q with ⟨k, b⟩
        dsimp at hq
        subst k
        cases b <;> simp [generators, vectors]

lemma blockSpace_orthogonal : OrthogonalFamily ℝ (fun i => blockSpace D i)
    (fun i => (blockSpace D i).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  apply Submodule.isOrtho_span.mpr
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := (mem_generators_iff D i x).mp hx
  obtain ⟨q, hq, rfl⟩ := (mem_generators_iff D j y).mp hy
  apply D.orthonormal.2
  intro hpq
  apply hij
  rw [← hp, ← hq, hpq]

instance blockSpace_finiteDimensional (i : BlockIndex D) : FiniteDimensional ℝ (blockSpace D i) := by
  apply FiniteDimensional.span_of_finite
  cases i <;> simp [generators]

lemma line_norm (i : D.LineIndex) : ‖D.line i‖ = 1 := D.orthonormal.1 (Sum.inl i)
lemma first_norm (j : D.PlaneIndex) : ‖D.first j‖ = 1 := D.orthonormal.1 (Sum.inr (j, false))
lemma second_norm (j : D.PlaneIndex) : ‖D.second j‖ = 1 := D.orthonormal.1 (Sum.inr (j, true))
lemma first_inner_second (j : D.PlaneIndex) : inner ℝ (D.first j) (D.second j) = 0 :=
  D.orthonormal.2 (by simp : Sum.inr (j, false) ≠ Sum.inr (j, true))

lemma second_inner_first (j : D.PlaneIndex) : inner ℝ (D.second j) (D.first j) = 0 := by
  rw [real_inner_comm]
  exact first_inner_second D j

lemma blockSpace_projection (i : BlockIndex D) :
    (blockSpace D i).starProjection = D.projection i := by
  cases i with
  | inl i =>
    ext x
    change (ℝ ∙ D.line i).starProjection x = inner ℝ (D.line i) x • D.line i
    exact Submodule.starProjection_unit_singleton ℝ (line_norm D i) x
  | inr j =>
    let : FiniteDimensional ℝ (Submodule.span ℝ {D.first j, D.second j}) :=
      blockSpace_finiteDimensional D (Sum.inr j)
    ext x
    change (Submodule.span ℝ {D.first j, D.second j}).starProjection x =
      inner ℝ (D.first j) x • D.first j + inner ℝ (D.second j) x • D.second j
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · apply Submodule.add_mem
      · apply Submodule.smul_mem
        exact Submodule.subset_span (by simp)
      · apply Submodule.smul_mem
        exact Submodule.subset_span (by simp)
    · rw [Submodule.mem_orthogonal]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        rcases Set.mem_insert_iff.mp hy with hy | hy
        · subst y
          simp [inner_sub_right, inner_add_right, inner_smul_right,
            first_norm D j, first_inner_second D j]
        · have hy' := Set.mem_singleton_iff.mp hy
          subst y
          simp [inner_sub_right, inner_add_right, inner_smul_right,
            second_norm D j, second_inner_first D j]
      | zero => simp
      | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
      | smul a y _ hy => simp [inner_smul_left, hy]

lemma blockSpace_invariant (i : BlockIndex D) : ∀ y ∈ blockSpace D i, N y ∈ blockSpace D i := by
  cases i with
  | inl i => exact (D.line_reducing i).1
  | inr j => exact (D.plane_reducing j).1

lemma blockSpace_norm_scale (i : BlockIndex D) :
    ∀ y ∈ blockSpace D i, ‖N y‖ = D.modulus i * ‖y‖ := by
  cases i with
  | inl i =>
    intro y hy
    obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.mp hy
    change ‖N (u • D.line i)‖ = |D.eigenvalue i| * ‖u • D.line i‖
    have he : N (u • D.line i) = D.eigenvalue i • (u • D.line i) := by
      rw [map_smul, D.line_action, smul_smul, smul_smul, mul_comm]
    rw [he, norm_smul, Real.norm_eq_abs]
  | inr j =>
    intro y hy
    obtain ⟨u, v, rfl⟩ := Submodule.mem_span_pair.mp hy
    exact rotation_plane_norm_scale N (D.first j) (D.second j) (D.realPart j) (D.speed j)
      (first_norm D j) (second_norm D j) (first_inner_second D j)
      (D.first_action j) (D.second_action j) u v

lemma blockSpace_ne_bot (i : BlockIndex D) : blockSpace D i ≠ ⊥ := by
  apply (blockSpace D i).ne_bot_iff.mpr
  cases i with
  | inl i =>
    refine ⟨D.line i, Submodule.subset_span (Set.mem_singleton _), ?_⟩
    exact norm_ne_zero_iff.mp (by rw [line_norm D i]; exact one_ne_zero)
  | inr j =>
    refine ⟨D.first j, Submodule.subset_span (by simp [generators]), ?_⟩
    exact norm_ne_zero_iff.mp (by rw [first_norm D j]; exact one_ne_zero)

lemma modulus_pos (i : BlockIndex D) : 0 < D.modulus i := by
  cases i with
  | inl i => exact abs_pos.mpr (D.eigenvalue_ne_zero i)
  | inr j =>
    change 0 < Real.sqrt (D.realPart j ^ 2 + D.speed j ^ 2)
    have hb := D.speed_pos j
    positivity

lemma iSup_blockSpace_eq_span : (⨆ i, blockSpace D i) = Submodule.span ℝ (Set.range (vectors D)) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (mem_generators_iff D i x).mp hx
    exact Submodule.subset_span ⟨p, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply le_iSup (blockSpace D) (coordinateBlock D p)
    apply Submodule.subset_span
    exact (mem_generators_iff D _ _).mpr ⟨p, rfl, rfl⟩

lemma closed_iSup_blockSpace : (⨆ i, blockSpace D i).topologicalClosure = N.ker.orthogonal := by
  rw [iSup_blockSpace_eq_span D]
  exact D.closed_span

lemma projection_vector_expansion (x : H) :
    HasSum (fun i => D.projection i x)
      (x - (letI : CompleteSpace N.ker := N.isClosed_ker.completeSpace_coe;
        N.ker.starProjection x)) := by
  have hs := block_projection_expansion (blockSpace D) (blockSpace_orthogonal D) x
  simp_rw [blockSpace_projection D] at hs
  simp only [closed_iSup_blockSpace D] at hs
  let : CompleteSpace N.ker := N.isClosed_ker.completeSpace_coe
  have hproj : N.ker.orthogonal.starProjection x = x - N.ker.starProjection x := by
    have h := N.ker.starProjection_add_starProjection_orthogonal x
    exact eq_sub_of_add_eq' h
  rwa [hproj] at hs

lemma operator_vector_expansion (x : H) :
    HasSum (fun i => N (D.projection i x)) (N x) := by
  let : CompleteSpace N.ker := N.isClosed_ker.completeSpace_coe
  have hp : N (N.ker.starProjection x) = 0 := N.ker.starProjection_apply_mem x
  have hs := (projection_vector_expansion D x).map N N.continuous
  simpa only [Function.comp_def, map_sub, hp, sub_zero] using hs

theorem real_expansion_of_data
    (hfinite : ∀ ε : ℝ, 0 < ε → {i | ε ≤ D.modulus i}.Finite) :
    (∀ x, HasSum (fun i => D.projection i x)
        (x - (letI : CompleteSpace N.ker := N.isClosed_ker.completeSpace_coe;
          N.ker.starProjection x)) ∧ HasSum (fun i => N (D.projection i x)) (N x)) ∧
      HasSum (fun i => N.comp (D.projection i)) N ∧
      (∀ s, ‖N - D.truncation s‖ = sSup (D.tailModuli s)) ∧
      ∃ s : ℕ → Finset (D.LineIndex ⊕ D.PlaneIndex), Monotone s ∧
        (∀ i, ∃ n, i ∈ s n) ∧
        (∀ n i, i ∈ s n → ∀ j, j ∉ s n → D.modulus j ≤ D.modulus i) ∧
        Filter.Tendsto (fun n => D.truncation (s n)) Filter.atTop (nhds N) := by
  have hexpand : ∀ x, HasSum (fun i => N ((blockSpace D i).starProjection x)) (N x) := by
    intro x
    simpa only [blockSpace_projection D] using operator_vector_expansion D x
  have hop := operator_block_expansion (blockSpace D) (blockSpace_orthogonal D) N
    (blockSpace_invariant D) D.modulus (fun i => (modulus_pos D i).le)
    (blockSpace_norm_scale D) hexpand hfinite
  have htail := norm_block_remainder_eq_sSup (blockSpace D) (blockSpace_orthogonal D) N
    (blockSpace_invariant D) D.modulus (fun i => (modulus_pos D i).le)
    (blockSpace_ne_bot D) (blockSpace_norm_scale D) hexpand
  have hordered := ordered_operator_block_expansion (blockSpace D) (blockSpace_orthogonal D) N
    (blockSpace_invariant D) D.modulus (modulus_pos D) (blockSpace_norm_scale D) hexpand hfinite
  simp_rw [blockSpace_projection D] at hop htail hordered
  exact ⟨fun x => ⟨projection_vector_expansion D x, operator_vector_expansion D x⟩, hop, htail, hordered⟩


end RealBlockDataAnalysis

section RealNormalPolynomial
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
open Spec (pairOperator)
open ContinuousLinearMap

lemma real_normal_scalar_shift (N : H →L[ℝ] H) (hN : IsStarNormal N) (r : ℝ) :
    IsStarNormal (N - r • 1) := by
  letI := hN
  apply Commute.isStarNormal_sub
  simp only [star_smul, star_one, star_trivial]
  exact (Commute.one_right N).smul_right _

lemma real_normal_adjoint_eigenvector (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (r : ℝ) (x : H) : N.adjoint x = r • x ↔ N x = r • x := by
  have hh := (real_normal_scalar_shift N hN r).adjoint_apply_eq_zero_iff x
  simpa only [map_sub, map_smulₛₗ, ContinuousLinearMap.adjoint_one,
    starRingEnd_apply, star_trivial, sub_apply, smul_apply,
    one_apply_eq_self, sub_eq_zero] using hh

lemma real_normal_pairOperator (N : H →L[ℝ] H) (hN : IsStarNormal N) (a b : ℝ) :
    IsStarNormal (pairOperator N a b) := by
  letI := hN
  haveI : IsStarNormal (N * N) := by
    simpa only [pow_two] using (inferInstance : IsStarNormal (N ^ 2))
  have hcomm : Commute (N * N) (star ((2*a) • N)) := by
    simpa only [star_smul, star_trivial, pow_two] using
      ((hN.star_comm_self.symm.pow_left 2).smul_right (2*a))
  letI : IsStarNormal (N * N - (2*a) • N) := hcomm.isStarNormal_sub
  unfold pairOperator
  apply Commute.isStarNormal_add
  simp only [star_smul, star_one, star_trivial]
  exact (Commute.one_right _).smul_right _

lemma real_pair_adjoint_kernel (N : H →L[ℝ] H) (hN : IsStarNormal N) (a b : ℝ)
    (x : H) (hx : x ∈ (pairOperator N a b).ker) :
    (pairOperator N a b).adjoint x = 0 :=
  (real_normal_pairOperator N hN a b).adjoint_apply_eq_zero_iff x |>.mpr hx

end RealNormalPolynomial

lemma hilbertDimension_eq_finrank (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E] : Spec.hilbertDimension 𝕜 E = (Module.finrank 𝕜 E : Cardinal) := by
  classical
  letI : Finite (Spec.basisSet 𝕜 E) := (Spec.chosenBasis 𝕜 E).orthonormal.linearIndependent.finite
  letI := Fintype.ofFinite (Spec.basisSet 𝕜 E)
  unfold Spec.hilbertDimension
  rw [Cardinal.mk_fintype, Module.finrank_eq_card_basis (Spec.chosenBasis 𝕜 E).toOrthonormalBasis.toBasis]

namespace RealLineMultiplicity
open ExpandedFA.CompactSpectral.CompactNormalClassification
open ExpandedFA.CompactSpectral.CompactNormalClassification.Spec
open ExpandedFA.CompactSpectral.CompactNormalClassification.RealBlockDataAnalysis
variable {H : Type v} {K : Type w}
 [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
 [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

abbrev LineFiber {N : H →L[ℝ] H} (D : RealBlockData N) (r : ℝ) := {i : D.LineIndex // D.eigenvalue i = r}

lemma nonmatching_line_inner_eq_zero {N : H →L[ℝ] H} (D : RealBlockData N) (hn : IsStarNormal N)
    {r : ℝ} {x : H} (hx : N x = r • x) (i : D.LineIndex) (hi : D.eigenvalue i ≠ r) :
    inner ℝ (D.line i) x = 0 := by
  have hax := (real_normal_adjoint_eigenvector N hn r x).mpr hx
  have h := ContinuousLinearMap.adjoint_inner_right N (D.line i) x
  rw [hax, D.line_action, inner_smul_left, inner_smul_right] at h
  simp only [starRingEnd_apply, star_trivial] at h
  have he : (D.eigenvalue i - r) * inner ℝ (D.line i) x = 0 := by nlinarith [h]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hi)

lemma plane_inner_eq_zero {N : H →L[ℝ] H} (D : RealBlockData N) (hn : IsStarNormal N)
    {r : ℝ} {x : H} (hx : N x = r • x) (j : D.PlaneIndex) :
    inner ℝ (D.first j) x = 0 ∧ inner ℝ (D.second j) x = 0 := by
  have hax := (real_normal_adjoint_eigenvector N hn r x).mpr hx
  have h1 := ContinuousLinearMap.adjoint_inner_right N (D.first j) x
  have h2 := ContinuousLinearMap.adjoint_inner_right N (D.second j) x
  rw [hax, D.first_action, inner_smul_right, inner_add_left, inner_smul_left, inner_smul_left] at h1
  rw [hax, D.second_action, inner_smul_right, inner_add_left, inner_smul_left, inner_smul_left] at h2
  simp only [starRingEnd_apply, star_trivial] at h1 h2
  have hb := D.speed_pos j
  have hu : (D.realPart j - r) * inner ℝ (D.first j) x + D.speed j * inner ℝ (D.second j) x = 0 := by
    nlinarith [h1]
  have hv : -D.speed j * inner ℝ (D.first j) x + (D.realPart j - r) * inner ℝ (D.second j) x = 0 := by
    nlinarith [h2]
  have hsq : ((D.realPart j - r) ^ 2 + D.speed j ^ 2) *
      (inner ℝ (D.first j) x ^ 2 + inner ℝ (D.second j) x ^ 2) = 0 := by
    nlinarith [sq_nonneg ((D.realPart j - r) * inner ℝ (D.first j) x + D.speed j * inner ℝ (D.second j) x),
      sq_nonneg (-D.speed j * inner ℝ (D.first j) x + (D.realPart j - r) * inner ℝ (D.second j) x)]
  have hcoeff : 0 < (D.realPart j - r) ^ 2 + D.speed j ^ 2 := by positivity
  have hzero := (mul_eq_zero.mp hsq).resolve_left (ne_of_gt hcoeff)
  constructor <;> nlinarith [sq_nonneg (inner ℝ (D.first j) x), sq_nonneg (inner ℝ (D.second j) x)]

def lineFiberVectors {N : H →L[ℝ] H} (D : RealBlockData N) (r : ℝ) :
    LineFiber D r → Module.End.eigenspace N.toLinearMap r := fun j =>
  ⟨D.line j.val, Module.End.mem_eigenspace_iff.mpr (by
    change N (D.line j.val) = r • D.line j.val
    rw [D.line_action, j.property])⟩

lemma lineFiberVectors_orthonormal {N : H →L[ℝ] H} (D : RealBlockData N) (r : ℝ) :
    Orthonormal ℝ (lineFiberVectors D r) := by
  have hline : Orthonormal ℝ (fun j : LineFiber D r => D.line j.val) :=
    D.orthonormal.comp (fun j : LineFiber D r => Sum.inl j.val) (by
      intro i j hij
      exact Subtype.ext (Sum.inl.inj hij))
  exact ((Module.End.eigenspace N.toLinearMap r).subtypeₗᵢ.orthonormal_comp_iff).mp hline

lemma lineFiberVectors_orthogonal_eq_bot {N : H →L[ℝ] H} (D : RealBlockData N)
    (hn : IsStarNormal N) (r : ℝ) (hr : r ≠ 0) :
    (Submodule.span ℝ (Set.range (lineFiberVectors D r))).orthogonal = ⊥ := by
  apply bot_unique
  intro x hx
  have hxEig : N (x : H) = r • (x : H) := Module.End.mem_eigenspace_iff.mp x.property
  have hline (i : D.LineIndex) : inner ℝ (D.line i) (x : H) = 0 := by
    by_cases hi : D.eigenvalue i = r
    · have h := hx (lineFiberVectors D r ⟨i, hi⟩) (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      exact h
    · exact nonmatching_line_inner_eq_zero D hn hxEig i hi
  have hprojection (i : D.LineIndex ⊕ D.PlaneIndex) : D.projection i (x : H) = 0 := by
    cases i with
    | inl i => simp [RealBlockData.projection, hline i]
    | inr j =>
      have hj := plane_inner_eq_zero D hn hxEig j
      simp [RealBlockData.projection, hj.1, hj.2]
  have hs := operator_vector_expansion D (x : H)
  have hz : (fun i => N (D.projection i (x : H))) = 0 := by
    funext i
    rw [hprojection i, map_zero]
    rfl
  rw [hz] at hs
  have hNx : N (x : H) = 0 := hs.unique hasSum_zero
  have hx0 : (x : H) = 0 := (smul_eq_zero.mp (hxEig.symm.trans hNx)).resolve_left hr
  exact (Submodule.mem_bot ℝ).mpr (Subtype.ext hx0)

lemma lineFiberVectors_maximal {N : H →L[ℝ] H} (D : RealBlockData N)
    (hn : IsStarNormal N) (r : ℝ) (hr : r ≠ 0) :
    ExpandedFA.Hilbert.OrthonormalExpansion.IsMaximalOrthonormal ℝ
      (Module.End.eigenspace N.toLinearMap r) _ (lineFiberVectors D r) := by
  apply (ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total ℝ _ _ _
    (lineFiberVectors_orthonormal D r)).mpr
  exact Submodule.topologicalClosure_eq_top_iff.mpr (lineFiberVectors_orthogonal_eq_bot D hn r hr)

lemma lineFiber_cardinality {N : H →L[ℝ] H} (D : RealBlockData N)
    (hn : IsStarNormal N) (r : ℝ) (hr : r ≠ 0) :
    Cardinal.lift.{v} (Cardinal.mk (LineFiber D r)) = realEigenMultiplicity N r := by
  let : CompleteSpace (Module.End.eigenspace N.toLinearMap r) :=
    (N.isClosed_eigenspace r).completeSpace_coe
  have hc := ExpandedFA.Hilbert.HilbertCardinalityClassification.basis_cardinality_invariant
    ℝ (Module.End.eigenspace N.toLinearMap r) (LineFiber D r)
    (basisSet ℝ (Module.End.eigenspace N.toLinearMap r))
    (lineFiberVectors D r) (chosenBasis ℝ (Module.End.eigenspace N.toLinearMap r))
    (lineFiberVectors_maximal D hn r hr) (chosenBasis_maximal ℝ _)
  simpa only [realEigenMultiplicity, hilbertDimension, Cardinal.lift_id, Cardinal.lift_umax, Cardinal.lift_uzero] using hc

lemma line_index_matching {N : H →L[ℝ] H} {M : K →L[ℝ] K}
    (D : RealBlockData N) (E : RealBlockData M) (hnN : IsStarNormal N) (hnM : IsStarNormal M)
    (hmul : ∀ r : ℝ, Cardinal.lift.{w} (realEigenMultiplicity N r) =
      Cardinal.lift.{v} (realEigenMultiplicity M r)) :
    ∃ p : D.LineIndex ≃ E.LineIndex, ∀ i, D.eigenvalue i = E.eigenvalue (p i) := by
  classical
  have hequiv (r : ℝ) : Nonempty (LineFiber D r ≃ LineFiber E r) := by
    by_cases hr : r = 0
    · subst r
      let : IsEmpty (LineFiber D 0) := ⟨fun i => D.eigenvalue_ne_zero i.val i.property⟩
      let : IsEmpty (LineFiber E 0) := ⟨fun i => E.eigenvalue_ne_zero i.val i.property⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
    · have hc := hmul r
      rw [← lineFiber_cardinality D hnN r hr, ← lineFiber_cardinality E hnM r hr] at hc
      apply Cardinal.eq.mp
      apply Cardinal.lift_inj.{0, max v w}.mp
      simpa only [Cardinal.lift_lift] using hc
  let q (r : ℝ) : LineFiber D r ≃ LineFiber E r := Classical.choice (hequiv r)
  refine ⟨Equiv.ofFiberEquiv q, ?_⟩
  intro i
  exact (Equiv.ofFiberEquiv_map q i).symm


end RealLineMultiplicity

section RealBlockDataConstruction
open ContinuousLinearMap
namespace RealBlock.Frame
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {N : H →L[ℝ] H} {μ : ℝ}

def Component (F : RealBlock.Frame N μ) := {b : Bool // b = false ∨ F.b ≠ 0}

def componentVector (F : RealBlock.Frame N μ) (b : F.Component) : H :=
  if b.val then F.f else F.e

lemma componentVector_mem (F : RealBlock.Frame N μ) (b : F.Component) :
    F.componentVector b ∈ F.space := by
  rcases b with ⟨b, hb⟩
  cases b
  · exact F.e_mem_space
  · exact F.f_mem_space

lemma norm_f_of_b_ne_zero (F : RealBlock.Frame N μ) (hb : F.b ≠ 0) : ‖F.f‖ = 1 := by
  rcases F.line_or_plane with h | h
  · exact (hb h.1).elim
  · exact h.2

lemma speed_pos_of_ne_zero (F : RealBlock.Frame N μ) (hb : F.b ≠ 0) : 0 < F.b := by
  rcases F.line_or_plane with h | h
  · exact (hb h.1).elim
  · exact h.1

lemma f_eq_zero_of_b_eq_zero (F : RealBlock.Frame N μ) (hb : F.b = 0) : F.f = 0 := by
  rcases F.line_or_plane with h | h
  · exact h.2
  · exact (h.1.ne' hb).elim

lemma componentVector_orthonormal (F : RealBlock.Frame N μ) :
    Orthonormal ℝ F.componentVector := by
  classical
  apply orthonormal_iff_ite.mpr
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  cases a <;> cases b
  · simp [Component, componentVector, real_inner_self_eq_norm_sq, F.norm_e]
  · simp only [Bool.true_eq_false, false_or] at hb
    simp [Component, componentVector, F.orthogonal]
  · simp only [Bool.true_eq_false, false_or] at ha
    simp [Component, componentVector, real_inner_comm F.e F.f, F.orthogonal]
  · simp only [Bool.true_eq_false, false_or] at ha hb
    simp [Component, componentVector, real_inner_self_eq_norm_sq, F.norm_f_of_b_ne_zero ha]

lemma componentVector_span (F : RealBlock.Frame N μ) :
    Submodule.span ℝ (Set.range F.componentVector) = F.space := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨b, rfl⟩
    exact F.componentVector_mem b
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Submodule.subset_span ⟨⟨false, Or.inl rfl⟩, rfl⟩
    · have hh : x = F.f := Set.mem_singleton_iff.mp hx
      rw [hh]
      by_cases hb : F.b = 0
      · rw [F.f_eq_zero_of_b_eq_zero hb]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨true, Or.inr hb⟩, rfl⟩

end RealBlock.Frame
namespace GlobalReal
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {N : H →L[ℝ] H}
variable {I : Type w} {μ : I → ℝ} (F : ∀ i, RealBlock.Frame N (μ i))

abbrev LineIndex := {i : I // (F i).b = 0}
abbrev PlaneIndex := {i : I // (F i).b ≠ 0}
abbrev CombinedIndex := LineIndex F ⊕ (PlaneIndex F × Bool)

def combinedVector : CombinedIndex F → H :=
  Sum.elim (fun i => (F i.val).e) (fun q => if q.2 then (F q.1.val).f else (F q.1.val).e)

def combinedToAtom : CombinedIndex F → (i : I) × (F i).Component
  | Sum.inl i => ⟨i.val, ⟨false, Or.inl rfl⟩⟩
  | Sum.inr (i, b) => ⟨i.val, ⟨b, Or.inr i.property⟩⟩

lemma combinedToAtom_injective : Function.Injective (combinedToAtom F) := by
  intro x y h
  have hi := congrArg (fun q : (i : I) × (F i).Component => q.1) h
  have hb := congrArg (fun q : (i : I) × (F i).Component => q.2.val) h
  rcases x with i | ⟨i, b⟩ <;> rcases y with j | ⟨j, c⟩
  · congr 1
    exact Subtype.ext hi
  · exact (j.property ((congrArg (fun i => (F i).b) hi) ▸ i.property)).elim
  · exact (i.property ((congrArg (fun i => (F i).b) hi).symm ▸ j.property)).elim
  · congr 1
    exact Prod.ext (Subtype.ext hi) hb

lemma combinedToAtom_surjective : Function.Surjective (combinedToAtom F) := by
  rintro ⟨i, b, hb⟩
  by_cases hFi : (F i).b = 0
  · have hbfalse : b = false := hb.resolve_right (not_not_intro hFi)
    subst b
    exact ⟨Sum.inl ⟨i, hFi⟩, rfl⟩
  · exact ⟨Sum.inr (⟨i, hFi⟩, b), rfl⟩

lemma combinedVector_eq_atoms : combinedVector F =
    (fun q : (i : I) × (F i).Component => (F q.1).componentVector q.2) ∘ combinedToAtom F := by
  funext x
  rcases x with i | ⟨i, b⟩ <;> rfl

lemma combinedVector_orthonormal
    (hpair : Pairwise (fun i j => (F i).space ⟂ (F j).space)) :
    Orthonormal ℝ (combinedVector F) := by
  let c (i : I) (b : (F i).Component) : (F i).space := ⟨(F i).componentVector b,
    (F i).componentVector_mem b⟩
  have hc (i : I) : Orthonormal ℝ (c i) :=
    ((F i).space.subtypeₗᵢ.orthonormal_comp_iff).mp (F i).componentVector_orthonormal
  have hfam : OrthogonalFamily ℝ (fun i => (F i).space) (fun i => (F i).space.subtypeₗᵢ) := by
    intro i j hij x y
    exact (hpair hij).inner_eq x.property y.property
  have hall : Orthonormal ℝ
      (fun q : (i : I) × (F i).Component => (F q.1).componentVector q.2) :=
    hfam.orthonormal_sigma_orthonormal hc
  rw [combinedVector_eq_atoms]
  exact hall.comp _ (combinedToAtom_injective F)

lemma combinedVector_span : Submodule.span ℝ (Set.range (combinedVector F)) =
    ⨆ i : I, (F i).space := by
  have heq : Set.range (combinedVector F) =
      Set.range (fun q : (i : I) × (F i).Component => (F q.1).componentVector q.2) := by
    rw [combinedVector_eq_atoms, Set.range_comp, (combinedToAtom_surjective F).range_eq, Set.image_univ]
  rw [heq]
  have hrange : Set.range (fun q : (i : I) × (F i).Component => (F q.1).componentVector q.2) =
      ⋃ i, Set.range (F i).componentVector := by
    ext x
    simp only [Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, b⟩, hx⟩
      exact ⟨i, b, hx⟩
    · rintro ⟨i, b, hx⟩
      exact ⟨⟨i, b⟩, hx⟩
  rw [hrange, Submodule.span_iUnion]
  simp_rw [RealBlock.Frame.componentVector_span]

lemma frame_space_eq_line {i : I} (hi : (F i).b = 0) :
    (F i).space = Submodule.span ℝ {(F i).e} := by
  rw [RealBlock.Frame.space, (F i).f_eq_zero_of_b_eq_zero hi, Set.pair_comm,
    Submodule.span_insert_zero]

variable {I₀ : Type} {ν : I₀ → ℝ} (B : ∀ i, RealBlock.Frame N (ν i))

def blockDataOfFrames [Countable I₀] (hpos : ∀ i, 0 < ν i)
    (hpair : Pairwise (fun i j => (B i).space ⟂ (B j).space))
    (hclosed : (⨆ i, (B i).space).topologicalClosure = N.ker.orthogonal) :
    Spec.RealBlockData N := by
  classical
  refine {
    LineIndex := LineIndex B
    PlaneIndex := PlaneIndex B
    line_countable := inferInstance
    plane_countable := inferInstance
    line := fun i => (B i.val).e
    first := fun i => (B i.val).e
    second := fun i => (B i.val).f
    eigenvalue := fun i => (B i.val).a
    realPart := fun i => (B i.val).a
    speed := fun i => (B i.val).b
    eigenvalue_ne_zero := ?_
    speed_pos := fun i => (B i.val).speed_pos_of_ne_zero i.property
    orthonormal := combinedVector_orthonormal B hpair
    line_action := ?_
    first_action := fun i => (B i.val).apply_e
    second_action := fun i => (B i.val).apply_f
    closed_span := ?_
    line_reducing := ?_
    plane_reducing := ?_ }
  · intro i ha
    have hm := (B i.val).modulus
    rw [ha, i.property] at hm
    have hh := hpos i.val
    nlinarith
  · intro i
    simpa only [i.property, zero_smul, add_zero] using (B i.val).apply_e
  · change (Submodule.span ℝ (Set.range (combinedVector B))).topologicalClosure = _
    rw [combinedVector_span]
    exact hclosed
  · intro i
    rw [← frame_space_eq_line B i.property]
    exact ⟨fun _ hx => (B i.val).invariant hx, fun _ hx => (B i.val).orthogonal_invariant hx⟩
  · intro i
    exact ⟨fun _ hx => (B i.val).invariant hx, fun _ hx => (B i.val).orthogonal_invariant hx⟩

def constructedData (N : H →L[ℝ] H) (hc : IsCompactOperator N) (hn : IsStarNormal N) :
    Spec.RealBlockData N := by
  classical
  letI : Countable (FrameIndex N hc hn) := frameIndex_countable N hc hn
  let I₀ := Shrink.{0} (FrameIndex N hc hn)
  let q : I₀ ≃ FrameIndex N hc hn := (equivShrink.{0} (FrameIndex N hc hn)).symm
  letI : Countable I₀ := Countable.of_equiv _ q.symm
  let ν : I₀ → ℝ := fun i => (q i).1.val
  let B : ∀ i : I₀, RealBlock.Frame N (ν i) := fun i => globalFrame N hc hn (q i)
  refine blockDataOfFrames B (fun i => globalFrame_positive N hc hn (q i)) ?_ ?_
  · intro i j hij
    exact globalFrame_pairwise N hc hn (q.injective.ne hij)
  · have hh : (⨆ i : I₀, (B i).space) = ⨆ i, (globalFrame N hc hn i).space := q.iSup_comp (g := fun i : FrameIndex N hc hn => (globalFrame N hc hn i).space)
    rw [hh]
    exact globalFrame_closedSpan N hc hn

lemma blockDataOfFrames_modulus [Countable I₀] (hpos : ∀ i, 0 < ν i)
    (hpair : Pairwise (fun i j => (B i).space ⟂ (B j).space))
    (hclosed : (⨆ i, (B i).space).topologicalClosure = N.ker.orthogonal)
    (i : LineIndex B ⊕ PlaneIndex B) :
    (blockDataOfFrames B hpos hpair hclosed).modulus i =
      Real.sqrt (ν (Equiv.sumCompl (fun i => (B i).b = 0) i)) := by
  classical
  rcases i with i | i
  · change |(B i.val).a| = Real.sqrt (ν i.val)
    have hm : (B i.val).a ^ 2 = ν i.val := by simpa only [i.property, zero_pow (by decide : 2 ≠ 0), add_zero] using (B i.val).modulus
    calc
      |(B i.val).a| = Real.sqrt ((B i.val).a ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ = Real.sqrt (ν i.val) := congrArg Real.sqrt hm
  · change Real.sqrt ((B i.val).a ^ 2 + (B i.val).b ^ 2) = Real.sqrt (ν i.val)
    rw [(B i.val).modulus]

lemma blockDataOfFrames_finite_away [Countable I₀] (hpos : ∀ i, 0 < ν i)
    (hpair : Pairwise (fun i j => (B i).space ⟂ (B j).space))
    (hclosed : (⨆ i, (B i).space).topologicalClosure = N.ker.orthogonal)
    (ε : ℝ) (hfin : {i : I₀ | ε ≤ Real.sqrt (ν i)}.Finite) :
    {i | ε ≤ (blockDataOfFrames B hpos hpair hclosed).modulus i}.Finite := by
  classical
  change {i : LineIndex B ⊕ PlaneIndex B | ε ≤ (blockDataOfFrames B hpos hpair hclosed).modulus i}.Finite
  have heq : {i : LineIndex B ⊕ PlaneIndex B | ε ≤ (blockDataOfFrames B hpos hpair hclosed).modulus i} =
      (Equiv.sumCompl (fun i => (B i).b = 0)) ⁻¹' {i | ε ≤ Real.sqrt (ν i)} := by
    ext i
    change (ε ≤ (blockDataOfFrames B hpos hpair hclosed).modulus i) ↔
      (ε ≤ Real.sqrt (ν (Equiv.sumCompl (fun i => (B i).b = 0) i)))
    rw [blockDataOfFrames_modulus B hpos hpair hclosed i]
  rw [heq]
  exact hfin.preimage (Equiv.sumCompl (fun i => (B i).b = 0)).injective.injOn

lemma constructedData_finite_away (N : H →L[ℝ] H)
    (hcompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap)
    (hc : IsCompactOperator N) (hn : IsStarNormal N) (ε : ℝ) (hε : 0 < ε) :
    {i | ε ≤ (constructedData N hc hn).modulus i}.Finite := by
  classical
  letI : Countable (FrameIndex N hc hn) := frameIndex_countable N hc hn
  letI : Countable (Shrink.{0} (FrameIndex N hc hn)) :=
    Countable.of_equiv _ (equivShrink.{0} (FrameIndex N hc hn))
  unfold constructedData
  apply blockDataOfFrames_finite_away
  have hfin := globalFrame_finite_away N hcompact hc hn ε hε
  exact hfin.preimage (f := (equivShrink.{0} (FrameIndex N hc hn)).symm)
    (equivShrink.{0} (FrameIndex N hc hn)).symm.injective.injOn

end GlobalReal

end RealBlockDataConstruction

theorem real_normal_expansion : Spec.RealNormalExpansion.{v} := by
  intro H _ _ _ N hcompact hn
  have hc := (Compactness.compact_iff_isCompactOperator _).mp hcompact
  let D := GlobalReal.constructedData N hc hn
  have hfinite : ∀ ε : ℝ, 0 < ε → {i | ε ≤ D.modulus i}.Finite :=
    GlobalReal.constructedData_finite_away N hcompact hc hn
  exact ⟨D, hfinite, RealBlockDataAnalysis.real_expansion_of_data D hfinite⟩

namespace RealBlockClassification
open ExpandedFA.CompactSpectral.CompactNormalClassification
open ExpandedFA.CompactSpectral.CompactNormalClassification.Spec
variable {H : Type v} {K : Type w}
 [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
 [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

local instance kernelComplete (N : H →L[ℝ] H) : CompleteSpace N.ker :=
 N.isClosed_ker.completeSpace_coe

abbrev BlockIndex {N : H →L[ℝ] H} (D : RealBlockData N) :=
 D.LineIndex ⊕ (D.PlaneIndex × Bool)

def blockVectors {N : H →L[ℝ] H} (D : RealBlockData N) : BlockIndex D → H :=
 Sum.elim D.line (fun q => if q.2 then D.second q.1 else D.first q.1)

abbrev WholeIndex {N : H →L[ℝ] H} (D : RealBlockData N) :=
 basisSet ℝ N.ker ⊕ BlockIndex D

def wholeVectors {N : H →L[ℝ] H} (D : RealBlockData N) : WholeIndex D → H :=
 Sum.elim (fun j => (chosenBasis ℝ N.ker j : H)) (blockVectors D)

lemma blockVectors_mem_kerOrth {N : H →L[ℝ] H} (D : RealBlockData N) (i : BlockIndex D) :
 blockVectors D i ∈ N.ker.orthogonal := by
 rw [← D.closed_span]
 exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

lemma wholeVectors_orthonormal {N : H →L[ℝ] H} (D : RealBlockData N) :
 Orthonormal ℝ (wholeVectors D) := by
 constructor
 · rintro (i|i)
   · exact (chosenBasis ℝ N.ker).orthonormal.norm_eq_one i
   · exact D.orthonormal.norm_eq_one i
 · rintro (i|i) (j|j) hij
   · exact (chosenBasis ℝ N.ker).orthonormal.inner_eq_zero (by simpa using hij)
   · exact blockVectors_mem_kerOrth D j (chosenBasis ℝ N.ker i)
      (chosenBasis ℝ N.ker i).property
   · exact inner_eq_zero_symm.mp (blockVectors_mem_kerOrth D i
      (chosenBasis ℝ N.ker j) (chosenBasis ℝ N.ker j).property)
   · exact D.orthonormal.inner_eq_zero (by simpa using hij)

lemma wholeVectors_total {N : H →L[ℝ] H} (D : RealBlockData N) :
 (Submodule.span ℝ (Set.range (wholeVectors D))).topologicalClosure = ⊤ := by
 apply Submodule.topologicalClosure_eq_top_iff.mpr
 apply bot_unique
 intro x hx
 have hi := (orthogonal_span_range_iff (wholeVectors D) x).mp hx
 have hxb : x ∈ (Submodule.span ℝ (Set.range (blockVectors D))).orthogonal := by
   apply (orthogonal_span_range_iff (blockVectors D) x).mpr
   intro i
   exact hi (Sum.inr i)
 have hxker : x ∈ N.ker := by
   rw [← Submodule.orthogonal_closure, show
     (Submodule.span ℝ (Set.range (blockVectors D))).topologicalClosure =
       N.ker.orthogonal from D.closed_span, Submodule.orthogonal_orthogonal] at hxb
   exact hxb
 have hinner (y : N.ker) : inner ℝ x (y : H) = 0 := by
   apply functional_zero_of_basis (chosenBasis ℝ N.ker)
     ((innerSL ℝ x).comp N.ker.subtypeL)
   intro i
   exact inner_eq_zero_symm.mp (hi (Sum.inl i))
 exact (Submodule.mem_bot ℝ).mpr (inner_self_eq_zero.mp (hinner ⟨x, hxker⟩))

lemma wholeVectors_maximal {N : H →L[ℝ] H} (D : RealBlockData N) :
 ExpandedFA.Hilbert.OrthonormalExpansion.IsMaximalOrthonormal ℝ H _ (wholeVectors D) :=
 (ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total ℝ H _ _
   (wholeVectors_orthonormal D)).mpr (wholeVectors_total D)

lemma block_matching_sufficient (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (D : RealBlockData N) (E : RealBlockData M)
 (p0 : basisSet ℝ N.ker ≃ basisSet ℝ M.ker)
 (p1 : D.LineIndex ≃ E.LineIndex) (p2 : D.PlaneIndex ≃ E.PlaneIndex)
 (h1 : ∀ i, D.eigenvalue i = E.eigenvalue (p1 i))
 (h2 : ∀ j, D.realPart j = E.realPart (p2 j))
 (h3 : ∀ j, D.speed j = E.speed (p2 j)) :
 ∃ U : H ≃ₗᵢ[ℝ] K, ∀ x, U (N x) = M (U x) := by
 let p : WholeIndex D ≃ WholeIndex E :=
   Equiv.sumCongr p0 (Equiv.sumCongr p1 (Equiv.prodCongr p2 (Equiv.refl Bool)))
 obtain ⟨U, hU⟩ := ExpandedFA.Hilbert.HilbertCardinalityClassification.basis_bijection_extends
   ℝ H K _ _ (wholeVectors D) (wholeVectors E)
   (wholeVectors_maximal D) (wholeVectors_maximal E) p
 refine ⟨U, ?_⟩
 have heq : U.toContinuousLinearEquiv.toContinuousLinearMap.comp N =
     M.comp U.toContinuousLinearEquiv.toContinuousLinearMap := by
   apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr
     (wholeVectors_total D))
   rintro _ ⟨i, rfl⟩
   change U (N (wholeVectors D i)) = M (U (wholeVectors D i))
   cases i with
   | inl i =>
     have hNi : N (wholeVectors D (Sum.inl i)) = 0 := (chosenBasis ℝ N.ker i).property
     have hMi : M (wholeVectors E (p (Sum.inl i))) = 0 :=
       (chosenBasis ℝ M.ker (p0 i)).property
     rw [hNi, map_zero, hU, hMi]
   | inr i =>
     cases i with
     | inl i =>
       change U (N (D.line i)) = M (U (D.line i))
       have hline : U (D.line i) = E.line (p1 i) := hU (Sum.inr (Sum.inl i))
       rw [D.line_action, map_smul, hline, E.line_action, h1]
     | inr i =>
       rcases i with ⟨j, b⟩
       have hfirst : U (D.first j) = E.first (p2 j) :=
         hU (Sum.inr (Sum.inr (j, false)))
       have hsecond : U (D.second j) = E.second (p2 j) :=
         hU (Sum.inr (Sum.inr (j, true)))
       cases b
       · change U (N (D.first j)) = M (U (D.first j))
         rw [D.first_action, map_add, map_smul, map_smul, hfirst, hsecond,
           E.first_action, h2, h3]
       · change U (N (D.second j)) = M (U (D.second j))
         rw [D.second_action, map_add, map_smul, map_smul, hfirst, hsecond,
           E.second_action, h2, h3]
 intro x
 exact congrArg (fun L : H →L[ℝ] K => L x) heq

lemma block_matching_sufficient_of_kernel_dimension (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (D : RealBlockData N) (E : RealBlockData M)
 (h0 : Cardinal.lift.{w} (hilbertDimension ℝ N.ker) =
   Cardinal.lift.{v} (hilbertDimension ℝ M.ker))
 (p1 : D.LineIndex ≃ E.LineIndex) (p2 : D.PlaneIndex ≃ E.PlaneIndex)
 (h1 : ∀ i, D.eigenvalue i = E.eigenvalue (p1 i))
 (h2 : ∀ j, D.realPart j = E.realPart (p2 j))
 (h3 : ∀ j, D.speed j = E.speed (p2 j)) :
 ∃ U : H ≃ₗᵢ[ℝ] K, ∀ x, U (N x) = M (U x) := by
 obtain ⟨p0⟩ := Cardinal.lift_mk_eq'.mp h0
 exact block_matching_sufficient N M D E p0 p1 p2 h1 h2 h3

lemma inner_apply_eq_zero_of_mem_ker_normal (T : H →L[ℝ] H) (hn : IsStarNormal T)
 (x : H) (hx : x ∈ T.ker) (y : H) : ⟪T y, x⟫_ℝ = 0 := by
 have hadj : T.adjoint x = 0 := ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff hn x |>.mpr hx
 rw [← T.adjoint_inner_right, hadj, inner_zero_right]


abbrev PlaneFiber {N : H →L[ℝ] H} (D : RealBlockData N) (a b : ℝ) :=
 {j : D.PlaneIndex // D.realPart j = a ∧ D.speed j = b}

lemma pairKernel_inner_line_zero {N : H →L[ℝ] H} (D : RealBlockData N)
 (hn : IsStarNormal N) (a b : ℝ) (hb : 0 < b) (x : H)
 (hx : x ∈ (pairOperator N a b).ker) (i : D.LineIndex) : ⟪D.line i, x⟫_ℝ = 0 := by
 have hi := inner_apply_eq_zero_of_mem_ker_normal (pairOperator N a b)
   (real_normal_pairOperator N hn a b) x hx (D.line i)
 rw [pairOperator_on_realEigenvector N a b (D.eigenvalue i) (D.line i) (D.line_action i),
   inner_smul_left, starRingEnd_apply, star_trivial] at hi
 exact (mul_eq_zero.mp hi).resolve_left (by nlinarith [sq_nonneg (D.eigenvalue i-a), sq_pos_of_pos hb])

lemma pairKernel_inner_kernel_zero {N : H →L[ℝ] H} (hn : IsStarNormal N)
 (a b : ℝ) (hb : 0 < b) (x : H) (hx : x ∈ (pairOperator N a b).ker)
 (y : N.ker) : ⟪(y : H), x⟫_ℝ = 0 := by
 have hi := inner_apply_eq_zero_of_mem_ker_normal (pairOperator N a b)
   (real_normal_pairOperator N hn a b) x hx y
 have hy : N (y : H) = (0 : ℝ) • (y : H) := by simpa using y.property
 rw [pairOperator_on_realEigenvector N a b 0 (y : H) hy,
   inner_smul_left, starRingEnd_apply, star_trivial] at hi
 exact (mul_eq_zero.mp hi).resolve_left (by nlinarith [sq_nonneg a, sq_pos_of_pos hb])

lemma pairKernel_inner_other_plane_zero {N : H →L[ℝ] H} (D : RealBlockData N)
 (hn : IsStarNormal N) (a b : ℝ) (hb : 0 < b) (x : H)
 (hx : x ∈ (pairOperator N a b).ker) (j : D.PlaneIndex)
 (hj : ¬ (D.realPart j = a ∧ D.speed j = b)) :
 ⟪D.first j, x⟫_ℝ = 0 ∧ ⟪D.second j, x⟫_ℝ = 0 := by
 let A := (D.realPart j-a)^2+b^2-D.speed j^2
 let B := 2*D.speed j*(D.realPart j-a)
 have h1 := inner_apply_eq_zero_of_mem_ker_normal (pairOperator N a b)
   (real_normal_pairOperator N hn a b) x hx (D.first j)
 have h2 := inner_apply_eq_zero_of_mem_ker_normal (pairOperator N a b)
   (real_normal_pairOperator N hn a b) x hx (D.second j)
 rw [pairOperator_on_plane_first N a b (D.realPart j) (D.speed j)
   (D.first j) (D.second j) (D.first_action j) (D.second_action j),
   inner_add_left, inner_smul_left, inner_smul_left, starRingEnd_apply, star_trivial, starRingEnd_apply, star_trivial] at h1
 rw [pairOperator_on_plane_second N a b (D.realPart j) (D.speed j)
   (D.first j) (D.second j) (D.first_action j) (D.second_action j),
   inner_add_left, inner_smul_left, inner_smul_left, starRingEnd_apply, star_trivial, starRingEnd_apply, star_trivial] at h2
 change A * ⟪D.first j, x⟫_ℝ + B * ⟪D.second j, x⟫_ℝ = 0 at h1
 have h2' : -B * ⟪D.first j, x⟫_ℝ + A * ⟪D.second j, x⟫_ℝ = 0 := by
   simpa only [B, neg_mul] using h2
 have hdet : A^2+B^2 ≠ 0 := by
   intro hz
   have hA : A = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
   have hB : B = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
   have hca : D.realPart j-a = 0 := (mul_eq_zero.mp hB).resolve_left
     (mul_ne_zero (by norm_num) (ne_of_gt (D.speed_pos j)))
   have hc : D.realPart j = a := by linarith
   have hd : D.speed j = b := by
     dsimp [A] at hA
     rw [hc] at hA
     nlinarith [D.speed_pos j]
   exact hj ⟨hc, hd⟩
 constructor
 · have hu : (A^2+B^2) * ⟪D.first j, x⟫_ℝ = 0 := by linear_combination A*h1 - B*h2'
   exact (mul_eq_zero.mp hu).resolve_left hdet
 · have hu : (A^2+B^2) * ⟪D.second j, x⟫_ℝ = 0 := by linear_combination B*h1 + A*h2'
   exact (mul_eq_zero.mp hu).resolve_left hdet

local instance pairKernelComplete (N : H →L[ℝ] H) (a b : ℝ) :
 CompleteSpace (pairOperator N a b).ker := (pairOperator N a b).isClosed_ker.completeSpace_coe

def pairFiberVectors {N : H →L[ℝ] H} (D : RealBlockData N) (a b : ℝ) :
 PlaneFiber D a b × Bool → (pairOperator N a b).ker :=
 fun q => ⟨if q.2 then D.second q.1 else D.first q.1, by
   rcases q with ⟨j, t⟩
   rcases j with ⟨j, hj⟩
   cases t
   · change pairOperator N a b (D.first j) = 0
     rw [pairOperator_on_plane_first N a b (D.realPart j) (D.speed j)
       (D.first j) (D.second j) (D.first_action j) (D.second_action j), hj.1, hj.2]
     simp
   · change pairOperator N a b (D.second j) = 0
     rw [pairOperator_on_plane_second N a b (D.realPart j) (D.speed j)
       (D.first j) (D.second j) (D.first_action j) (D.second_action j), hj.1, hj.2]
     simp⟩

lemma pairFiberVectors_orthonormal {N : H →L[ℝ] H} (D : RealBlockData N) (a b : ℝ) :
 Orthonormal ℝ (pairFiberVectors D a b) := by
 apply ((pairOperator N a b).ker.subtypeₗᵢ.orthonormal_comp_iff).mp
 exact D.orthonormal.comp (fun q : PlaneFiber D a b × Bool => Sum.inr (q.1.val, q.2))
   (by
    intro i j h
    have hh := Sum.inr.inj h
    exact Prod.ext (Subtype.ext (congrArg (fun q : D.PlaneIndex × Bool => q.1) hh)) (congrArg (fun q : D.PlaneIndex × Bool => q.2) hh))

lemma pairFiberVectors_orthogonal_eq_bot {N : H →L[ℝ] H} (D : RealBlockData N)
 (hn : IsStarNormal N) (a b : ℝ) (hb : 0 < b) :
 (Submodule.span ℝ (Set.range (pairFiberVectors D a b))).orthogonal = ⊥ := by
 apply bot_unique
 intro x hx
 have hi := (orthogonal_span_range_iff (pairFiberVectors D a b) x).mp hx
 have hall : (x : H) ∈ (Submodule.span ℝ (Set.range (wholeVectors D))).orthogonal := by
   apply (orthogonal_span_range_iff (wholeVectors D) x).mpr
   rintro (i|i)
   · exact pairKernel_inner_kernel_zero hn a b hb x x.property (chosenBasis ℝ N.ker i)
   · cases i with
     | inl i => exact pairKernel_inner_line_zero D hn a b hb x x.property i
     | inr i =>
       rcases i with ⟨j,t⟩
       by_cases hj : D.realPart j = a ∧ D.speed j = b
       · exact hi (⟨j,hj⟩,t)
       · have hz := pairKernel_inner_other_plane_zero D hn a b hb x x.property j hj
         cases t
         · exact hz.1
         · exact hz.2
 rw [Submodule.topologicalClosure_eq_top_iff.mp (wholeVectors_total D)] at hall
 exact (Submodule.mem_bot ℝ).mpr (Subtype.ext ((Submodule.mem_bot ℝ).mp hall))

def pairFiberBasis {N : H →L[ℝ] H} (D : RealBlockData N)
 (hn : IsStarNormal N) (a b : ℝ) (hb : 0 < b) :
 HilbertBasis (PlaneFiber D a b × Bool) ℝ (pairOperator N a b).ker :=
 HilbertBasis.mkOfOrthogonalEqBot (pairFiberVectors_orthonormal D a b)
   (pairFiberVectors_orthogonal_eq_bot D hn a b hb)


lemma planeFiber_finite {N : H →L[ℝ] H} (D : RealBlockData N) (hc : IsCompactOperator N)
 (hn : IsStarNormal N) (a b : ℝ) (hb : 0 < b) : Finite (PlaneFiber D a b) := by
 letI : FiniteDimensional ℝ (pairOperator N a b).ker := pairKernel_finiteDimensional N hc a b hb
 haveI : Finite (PlaneFiber D a b × Bool) := (pairFiberVectors_orthonormal D a b).linearIndependent.finite
 exact Finite.of_injective (fun j : PlaneFiber D a b => (j,false)) (fun _ _ h => congrArg Prod.fst h)

lemma pairMultiplicity_eq_card_planeFiber {N : H →L[ℝ] H} (D : RealBlockData N)
 (hc : IsCompactOperator N) (hn : IsStarNormal N) (a b : ℝ) (hb : 0 < b) :
 pairMultiplicity N a b = Nat.card (PlaneFiber D a b) := by
 letI : Finite (PlaneFiber D a b) := planeFiber_finite D hc hn a b hb
 letI := Fintype.ofFinite (PlaneFiber D a b)
 have hdim : Module.finrank ℝ (pairOperator N a b).ker =
     Fintype.card (PlaneFiber D a b × Bool) :=
   Module.finrank_eq_card_basis (pairFiberBasis D hn a b hb).toOrthonormalBasis.toBasis
 unfold pairMultiplicity
 rw [hdim, Fintype.card_prod, Fintype.card_bool, Nat.mul_div_left]
 · exact Nat.card_eq_fintype_card.symm
 · norm_num

lemma planeFiber_equiv {N : H →L[ℝ] H} {M : K →L[ℝ] K} (D : RealBlockData N)
 (E : RealBlockData M) (hcN : IsCompactOperator N) (hnN : IsStarNormal N)
 (hcM : IsCompactOperator M) (hnM : IsStarNormal M)
 (hmul : ∀ a b : ℝ, 0 < b → pairMultiplicity N a b = pairMultiplicity M a b)
 (a b : ℝ) : Nonempty (PlaneFiber D a b ≃ PlaneFiber E a b) := by
 classical
 by_cases hb : 0 < b
 · letI : Finite (PlaneFiber D a b) := planeFiber_finite D hcN hnN a b hb
   letI : Finite (PlaneFiber E a b) := planeFiber_finite E hcM hnM a b hb
   letI := Fintype.ofFinite (PlaneFiber D a b)
   letI := Fintype.ofFinite (PlaneFiber E a b)
   apply Fintype.card_eq.mp
   have hh : Nat.card (PlaneFiber D a b) = Nat.card (PlaneFiber E a b) := by
     rw [← pairMultiplicity_eq_card_planeFiber D hcN hnN a b hb,
       ← pairMultiplicity_eq_card_planeFiber E hcM hnM a b hb]
     exact hmul a b hb
   simpa only [Nat.card_eq_fintype_card] using hh
 · haveI : IsEmpty (PlaneFiber D a b) := ⟨fun j => hb (j.property.2 ▸ D.speed_pos j)⟩
   haveI : IsEmpty (PlaneFiber E a b) := ⟨fun j => hb (j.property.2 ▸ E.speed_pos j)⟩
   exact ⟨Equiv.equivOfIsEmpty _ _⟩

def planeLabel {N : H →L[ℝ] H} (D : RealBlockData N) (j : D.PlaneIndex) : ℝ × ℝ :=
 (D.realPart j, D.speed j)

def planeLabelFiberEquiv {N : H →L[ℝ] H} (D : RealBlockData N) (q : ℝ × ℝ) :
 {j : D.PlaneIndex // planeLabel D j = q} ≃ PlaneFiber D q.1 q.2 :=
 Equiv.subtypeEquivRight (fun j => Prod.ext_iff)

lemma plane_index_matching {N : H →L[ℝ] H} {M : K →L[ℝ] K} (D : RealBlockData N)
 (E : RealBlockData M) (hcN : IsCompactOperator N) (hnN : IsStarNormal N)
 (hcM : IsCompactOperator M) (hnM : IsStarNormal M)
 (hmul : ∀ a b : ℝ, 0 < b → pairMultiplicity N a b = pairMultiplicity M a b) :
 ∃ p : D.PlaneIndex ≃ E.PlaneIndex,
   (∀ j, D.realPart j = E.realPart (p j)) ∧ (∀ j, D.speed j = E.speed (p j)) := by
 classical
 let e : ∀ q : ℝ × ℝ, {j : D.PlaneIndex // planeLabel D j = q} ≃
     {j : E.PlaneIndex // planeLabel E j = q} := fun q =>
   (planeLabelFiberEquiv D q).trans
     ((Classical.choice (planeFiber_equiv D E hcN hnN hcM hnM hmul q.1 q.2)).trans
       (planeLabelFiberEquiv E q).symm)
 refine ⟨Equiv.ofFiberEquiv e, ?_, ?_⟩
 · intro j
   exact (congrArg Prod.fst (Equiv.ofFiberEquiv_map e j)).symm
 · intro j
   exact (congrArg Prod.snd (Equiv.ofFiberEquiv_map e j)).symm


lemma submodule_hilbertDimension_congr (S T : Submodule ℝ H)
 [CompleteSpace S] [CompleteSpace T] (h : S = T) :
 hilbertDimension ℝ S = hilbertDimension ℝ T := by
 subst T
 rfl

lemma kernel_dimension_eq_of_realEigenMultiplicity (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (hreal : ∀ r : ℝ, Cardinal.lift.{w} (realEigenMultiplicity N r) =
   Cardinal.lift.{v} (realEigenMultiplicity M r)) :
 Cardinal.lift.{w} (hilbertDimension ℝ N.ker) =
   Cardinal.lift.{v} (hilbertDimension ℝ M.ker) := by
 have hN0 : realEigenMultiplicity N 0 = hilbertDimension ℝ N.ker := by
   letI : CompleteSpace (Module.End.eigenspace N.toLinearMap 0) :=
     (N.isClosed_eigenspace 0).completeSpace_coe
   exact submodule_hilbertDimension_congr _ _ (Module.End.eigenspace_zero N.toLinearMap)
 have hM0 : realEigenMultiplicity M 0 = hilbertDimension ℝ M.ker := by
   letI : CompleteSpace (Module.End.eigenspace M.toLinearMap 0) :=
     (M.isClosed_eigenspace 0).completeSpace_coe
   exact submodule_hilbertDimension_congr _ _ (Module.End.eigenspace_zero M.toLinearMap)
 simpa only [hN0, hM0] using hreal 0

lemma classification_of_data (N : H →L[ℝ] H) (M : K →L[ℝ] K)
 (D : RealBlockData N) (E : RealBlockData M)
 (hcN : IsCompactOperator N) (hnN : IsStarNormal N)
 (hcM : IsCompactOperator M) (hnM : IsStarNormal M)
 (hreal : ∀ r : ℝ, Cardinal.lift.{w} (realEigenMultiplicity N r) =
   Cardinal.lift.{v} (realEigenMultiplicity M r))
 (hpair : ∀ a b : ℝ, 0 < b → pairMultiplicity N a b = pairMultiplicity M a b) :
 ∃ U : H ≃ₗᵢ[ℝ] K, ∀ x, U (N x) = M (U x) := by
 obtain ⟨p1, h1⟩ := RealLineMultiplicity.line_index_matching D E hnN hnM hreal
 obtain ⟨p2, h2, h3⟩ := plane_index_matching D E hcN hnN hcM hnM hpair
 exact block_matching_sufficient_of_kernel_dimension N M D E
   (kernel_dimension_eq_of_realEigenMultiplicity N M hreal) p1 p2 h1 h2 h3

end RealBlockClassification


theorem real_normal_classification : Spec.RealNormalClassification.{v,w} := by
  intro H K _ _ _ _ _ _ N M hcN hnN hcM hnM
  have hcN' := (Compactness.compact_iff_isCompactOperator _).mp hcN
  have hcM' := (Compactness.compact_iff_isCompactOperator _).mp hcM
  constructor
  · exact realClassification_necessary N M
  · rintro ⟨hreal, hpair⟩
    exact RealBlockClassification.classification_of_data N M
      (GlobalReal.constructedData N hcN' hnN) (GlobalReal.constructedData M hcM' hnM)
      hcN' hnN hcM' hnM hreal hpair

end ExpandedFA.CompactSpectral.CompactNormalClassification
