import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.FriedrichsExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosedNonnegativeForms
import Mathlib.Tactic.FunProp

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexConjugate InnerProductSpace Topology
open Filter UniformSpace
universe u v
namespace ExpandedFA.Unbounded.FriedrichsExtension
open ClosedNonnegativeForms
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp] theorem realShift_apply (A : Operator 𝕜 H H) (c : ℝ) (x : A.domain) :
    realShift A c x = A x + (c : 𝕜) • (x : H) := rfl

@[simp] theorem realShift_cancel (A : Operator 𝕜 H H) (c : ℝ) :
    realShift (realShift A c) (-c) = A := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  simp only [LinearPMap.mem_graph_iff]
  constructor <;> rintro ⟨x, hx, hAx⟩ <;> refine ⟨x, hx, ?_⟩
  · change A x + (c : 𝕜) • (x : H) + ((-c : ℝ) : 𝕜) • (x : H) = p.2 at hAx
    simpa using hAx
  · change A x + (c : 𝕜) • (x : H) + ((-c : ℝ) : 𝕜) • (x : H) = p.2
    simpa using hAx

@[simp] theorem operatorForm_apply (S : Operator 𝕜 H H) (c : ℝ)
    (h : SemiboundedSymmetric S c) (v u : S.domain) :
    (operatorForm S c h).form v u = inner 𝕜 (v : H) (S u) -
      (c : 𝕜) * inner 𝕜 (v : H) (u : H) := by
  change inner 𝕜 (v : H) (S u + ((-c : ℝ) : 𝕜) • (u : H)) = _
  simp [inner_add_right, inner_smul_right, sub_eq_add_neg]

section Complete
variable [CompleteSpace H]

/-- The inclusion extends to the abstract form completion. -/
def completionMap (q : NonnegativeForm 𝕜 H) : Completion q.EnergySpace →L[𝕜] H :=
  q.inclusion.fromCompletion

@[simp] theorem completionMap_coe (q : NonnegativeForm 𝕜 H) (x : q.EnergySpace) :
    completionMap q (x : Completion q.EnergySpace) = (q.toDomain x : H) := by
  exact q.inclusion.fromCompletion_apply_coe x

theorem completionMap_contractive (q : NonnegativeForm 𝕜 H) (x : Completion q.EnergySpace) :
    ‖completionMap q x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x => simpa using q.inclusion_bound x

/-- Symmetry identifies every original form test with an ambient continuous
functional, even when the operator is unbounded. -/
theorem completion_test (S : Operator 𝕜 H H) (c : ℝ) (h : SemiboundedSymmetric S c)
    (v : (operatorForm S c h).EnergySpace) (x : Completion (operatorForm S c h).EnergySpace) :
    inner 𝕜 (v : Completion (operatorForm S c h).EnergySpace) x =
    inner 𝕜 (S ((operatorForm S c h).toDomain v) +
      ((1 - c : ℝ) : 𝕜) • ((operatorForm S c h).toDomain v : H)) (completionMap (operatorForm S c h) x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [Completion.inner_coe, completionMap_coe, NonnegativeForm.energy_inner]
    rw [operatorForm_apply, inner_add_left, inner_smul_left, RCLike.conj_ofReal,
      h.symmetric ((operatorForm S c h).toDomain v) ((operatorForm S c h).toDomain x)]
    push_cast
    ring

/-- A form-completion vector mapped to zero is orthogonal to the dense core. -/
theorem completionMap_injective (S : Operator 𝕜 H H) (c : ℝ)
    (h : SemiboundedSymmetric S c) : Function.Injective (completionMap (operatorForm S c h)) := by
  have hzero : ∀ x, completionMap (operatorForm S c h) x = 0 → x = 0 := by
    intro x hx
    have ho : ∀ z : Completion (operatorForm S c h).EnergySpace, inner 𝕜 z x = 0 := by
      intro z
      induction z using Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) continuous_const
      | ih v => rw [completion_test S c h v, hx, inner_zero_right]
    exact (inner_self_eq_zero).mp (ho x)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

/-- Transport the completed inner product to the range, subtracting the ambient
inner product. Contractivity is exactly the nonnegativity of this form. -/
def rangeForm (q : NonnegativeForm 𝕜 H)
    (hj : Function.Injective (completionMap q)) : NonnegativeForm 𝕜 H := by
  let J := completionMap q
  let e := LinearEquiv.ofInjective J.toLinearMap hj
  refine
    { domain := J.toLinearMap.range
      dense := q.dense.mono ?_
      form := ((innerₛₗ 𝕜).compl₂ e.symm.toLinearMap).comp e.symm.toLinearMap -
        ((innerₛₗ 𝕜).compl₂ J.toLinearMap.range.subtype).comp J.toLinearMap.range.subtype
      hermitian := ?_
      nonneg := ?_ }
  · intro x hx
    exact ⟨((show q.EnergySpace from ⟨x, hx⟩) : Completion q.EnergySpace), completionMap_coe q _⟩
  · intro x y
    change conj (inner 𝕜 (e.symm y) (e.symm x) - inner 𝕜 (y : H) (x : H)) = _
    simp only [map_sub, inner_conj_symm]
    rfl
  · intro x
    change 0 ≤ RCLike.re (inner 𝕜 (e.symm x) (e.symm x) - inner 𝕜 (x : H) (x : H))
    rw [map_sub, ← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner]
    have hb := completionMap_contractive q (e.symm x)
    have he : J (e.symm x) = (x : H) := LinearEquiv.ofInjective_symm_apply _ _
    change ‖J (e.symm x)‖ ≤ _ at hb
    rw [he] at hb
    nlinarith [norm_nonneg (x : H), norm_nonneg (e.symm x)]

def rangeEquiv (q : NonnegativeForm 𝕜 H)
    (hj : Function.Injective (completionMap q)) :
    Completion q.EnergySpace ≃ₗ[𝕜] (rangeForm q hj).domain :=
  LinearEquiv.ofInjective (completionMap q).toLinearMap hj

@[simp] theorem rangeEquiv_inclusion (q : NonnegativeForm 𝕜 H)
    (hj : Function.Injective (completionMap q)) (x : Completion q.EnergySpace) :
    (rangeEquiv q hj x : H) = completionMap q x := rfl

theorem rangeForm_energy (q : NonnegativeForm 𝕜 H)
    (hj : Function.Injective (completionMap q)) (x y : Completion q.EnergySpace) :
    (rangeForm q hj).form (rangeEquiv q hj x) (rangeEquiv q hj y) +
      inner 𝕜 (completionMap q x) (completionMap q y) = inner 𝕜 x y := by
  change (inner 𝕜 ((rangeEquiv q hj).symm (rangeEquiv q hj x))
      ((rangeEquiv q hj).symm (rangeEquiv q hj y)) -
      inner 𝕜 (completionMap q x) (completionMap q y)) + _ = _
  simp only [LinearEquiv.symm_apply_apply, sub_add_cancel]

/-- The range with its energy norm is isometric to the full Hilbert completion. -/
def rangeEnergyEquiv (q : NonnegativeForm 𝕜 H)
    (hj : Function.Injective (completionMap q)) :
    Completion q.EnergySpace ≃ₗᵢ[𝕜] (rangeForm q hj).EnergySpace := by
  let e : Completion q.EnergySpace ≃ₗ[𝕜] (rangeForm q hj).EnergySpace := rangeEquiv q hj
  apply e.isometryOfInner
  intro x y
  change (rangeForm q hj).form (rangeEquiv q hj x) (rangeEquiv q hj y) +
    inner 𝕜 (rangeEquiv q hj x : H) (rangeEquiv q hj y : H) = _
  exact rangeForm_energy q hj x y

theorem rangeForm_closed (q : NonnegativeForm 𝕜 H)
    (hj : Function.Injective (completionMap q)) : (rangeForm q hj).IsClosed :=
  (rangeEnergyEquiv q hj).symm.toIsometryEquiv.completeSpace

/-- The entire closed form, with its injectively embedded completion. -/
def formClosure (S : Operator 𝕜 H H) (c : ℝ) (h : SemiboundedSymmetric S c) :
    FormClosure (operatorForm S c h) where
  embedding := completionMap _
  injective := completionMap_injective S c h
  on_core := completionMap_coe _
  contractive := completionMap_contractive _
  closedForm := rangeForm _ (completionMap_injective S c h)
  closed := rangeForm_closed _ _
  equivalence := rangeEquiv _ _
  inclusion := rangeEquiv_inclusion _ _
  energy_identity := rangeForm_energy _ _

omit [CompleteSpace H] in
/-- Any such embedded completion satisfies the usual sequential closability test. -/
theorem FormClosure.closable (q : NonnegativeForm 𝕜 H) (F : FormClosure q) :
    FormClosable q := by
  intro x hx hzero
  have hc : CauchySeq (fun n => (x n : Completion q.EnergySpace)) :=
    (Completion.uniformContinuous_coe _).comp_cauchySeq hx
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  have hjz : F.embedding z = 0 := by
    apply tendsto_nhds_unique (F.embedding.continuous.tendsto z |>.comp hz)
    change Tendsto (fun n => F.embedding (x n : Completion q.EnergySpace)) atTop (𝓝 0)
    simpa only [F.on_core] using hzero
  have heq : z = 0 := F.injective (hjz.trans F.embedding.map_zero.symm)
  subst z
  apply (Completion.coe_isometry.tendsto_nhds_iff).mpr
  change Tendsto (fun n => (x n : Completion q.EnergySpace)) atTop
    (𝓝 ((0 : q.EnergySpace) : Completion q.EnergySpace))
  simpa only [Completion.coe_zero] using hz

omit [CompleteSpace H] in
/-- The specified closure really extends the form on the original domain. -/
theorem FormClosure.core_test (S : Operator 𝕜 H H) (c : ℝ)
    (h : SemiboundedSymmetric S c) (F : FormClosure (operatorForm S c h))
    (u : (operatorForm S c h).EnergySpace)
    (x : Completion (operatorForm S c h).EnergySpace) :
    inner 𝕜 x (u : Completion (operatorForm S c h).EnergySpace) =
      inner 𝕜 (F.embedding x)
        (S ((operatorForm S c h).toDomain u) +
          ((1 - c : ℝ) : 𝕜) • ((operatorForm S c h).toDomain u : H)) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    rw [Completion.inner_coe, F.on_core, NonnegativeForm.energy_inner]
    rw [operatorForm_apply, inner_add_right, inner_smul_right]
    push_cast
    ring

omit [CompleteSpace H] in
theorem FormClosure.core_graph (S : Operator 𝕜 H H) (c : ℝ)
    (h : SemiboundedSymmetric S c) (F : FormClosure (operatorForm S c h)) (u : S.domain) :
    ((u : H), realShift S (-c) u) ∈ F.closedForm.associatedOperator.graph := by
  let u₀ : (operatorForm S c h).EnergySpace := u
  let U := F.equivalence (u₀ : Completion (operatorForm S c h).EnergySpace)
  have hU : (U : H) = (u : H) := (F.inclusion _).trans (F.on_core u₀)
  apply (F.closedForm.associated _ _).mpr
  refine ⟨hU ▸ U.property, fun v => ?_⟩
  have hev : F.embedding (F.equivalence.symm v) = (v : H) := by
    rw [← F.inclusion, LinearEquiv.apply_symm_apply]
  have he := F.energy_identity (F.equivalence.symm v)
    (u₀ : Completion (operatorForm S c h).EnergySpace)
  rw [LinearEquiv.apply_symm_apply, F.on_core, F.core_test S c h u₀, hev] at he
  have hsub : (⟨(u : H), hU ▸ U.property⟩ : F.closedForm.domain) = U :=
    Subtype.ext hU.symm
  rw [hsub]
  change F.closedForm.form v U = inner 𝕜 (v : H) (S u + ((-c : ℝ) : 𝕜) • (u : H))
  change F.closedForm.form v U + inner 𝕜 (v : H) (u : H) =
    inner 𝕜 (v : H) (S u + ((1 - c : ℝ) : 𝕜) • (u : H)) at he
  simp only [inner_add_right, inner_smul_right] at he ⊢
  push_cast at he ⊢
  linear_combination he

/-- Real shifts preserve self-adjointness, with the domain unchanged. -/
theorem realShift_selfAdjoint (A : Operator 𝕜 H H) (hd : Dense (A.domain : Set H))
    (hA : A = HilbertAdjointSpec.adjointValue A) (c : ℝ) :
    realShift A c = HilbertAdjointSpec.adjointValue (realShift A c) := by
  let B := realShift A c
  have hdB : Dense (B.domain : Set H) := hd
  have hsym : A.IsFormalAdjoint A := by
    have hh := LinearPMap.adjoint_isFormalAdjoint hd
    change A = A.adjoint at hA
    rw [← hA] at hh
    exact hh
  have hsB : B.IsFormalAdjoint B := by
    intro x y
    change inner 𝕜 (A x + (c : 𝕜) • (x : H)) (y : H) =
      inner 𝕜 (x : H) (A y + (c : 𝕜) • (y : H))
    rw [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal, hsym]
  apply le_antisymm (LinearPMap.IsFormalAdjoint.le_adjoint hdB hsB)
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨y, hy, hyp⟩ := B.adjoint.mem_graph_iff.mp hp
  have ha : ((y : H), B.adjoint y - (c : 𝕜) • (y : H)) ∈ A.adjoint.graph := by
    apply (mem_hilbertAdjoint_graph_iff A hd _ _).mpr
    intro x
    have hh := (LinearPMap.adjoint_isFormalAdjoint hdB).symm x y
    change inner 𝕜 (A x + (c : 𝕜) • (x : H)) (y : H) =
      inner 𝕜 (x : H) (B.adjoint y) at hh
    rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal] at hh
    rw [inner_sub_right, inner_smul_right]
    exact eq_sub_of_add_eq hh
  change A = A.adjoint at hA
  rw [← hA] at ha
  obtain ⟨x, hxy, hx⟩ := A.mem_graph_iff.mp ha
  apply B.mem_graph_iff.mpr
  refine ⟨x, hxy.trans hy, ?_⟩
  change A x + (c : 𝕜) • (x : H) = p.2
  rw [hx, hxy, sub_add_cancel, hyp]

omit [CompleteSpace H] in
/-- Injectivity of shifting includes equality of exact domains. -/
theorem realShift_injective (c : ℝ) : Function.Injective (realShift (𝕜 := 𝕜) (H := H) · c) := by
  intro A B h
  have hh := congrArg (fun T => realShift T (-c)) h
  simpa only [realShift_cancel] using hh

omit [CompleteSpace H] in
/-- The continuous embedding is fixed uniquely by the original core. -/
theorem FormClosure.embedding_unique (q : NonnegativeForm 𝕜 H) (F G : FormClosure q) :
    F.embedding = G.embedding := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v => rw [F.on_core, G.on_core]

omit [CompleteSpace H] in
/-- The full graph of the associated operator can be read in the abstract
completion, without any choice of range coordinates. -/
theorem FormClosure.graph_iff (q : NonnegativeForm 𝕜 H) (F : FormClosure q) (u f : H) :
    (u, f) ∈ F.closedForm.associatedOperator.graph ↔
      ∃ x : Completion q.EnergySpace, F.embedding x = u ∧
        ∀ z : Completion q.EnergySpace,
          inner 𝕜 z x - inner 𝕜 (F.embedding z) u = inner 𝕜 (F.embedding z) f := by
  rw [F.closedForm.associated]
  constructor
  · rintro ⟨hu, hf⟩
    let x := F.equivalence.symm ⟨u, hu⟩
    have hx : F.embedding x = u := by
      rw [← F.inclusion, LinearEquiv.apply_symm_apply]
    refine ⟨x, hx, fun z => ?_⟩
    have he := F.energy_identity z x
    rw [LinearEquiv.apply_symm_apply, hf, F.inclusion, hx] at he
    exact (eq_sub_of_add_eq he).symm
  · rintro ⟨x, hx, hf⟩
    have hxu : (F.equivalence x : H) = u := (F.inclusion x).trans hx
    refine ⟨hxu ▸ (F.equivalence x).property, fun v => ?_⟩
    have he := F.energy_identity (F.equivalence.symm v) x
    have hz : F.embedding (F.equivalence.symm v) = (v : H) := by
      rw [← F.inclusion, LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.apply_symm_apply, hz, hx] at he
    have ht := hf (F.equivalence.symm v)
    rw [hz] at ht
    have hsub : (⟨u, hxu ▸ (F.equivalence x).property⟩ : F.closedForm.domain) =
        F.equivalence x := Subtype.ext hxu.symm
    rw [hsub]
    exact (eq_sub_of_add_eq he).trans ht

/-- Friedrichs completion and its injective ambient embedding. -/
theorem completion_embedding : Spec.CompletionEmbedding.{u, v} := by
  intro 𝕜 H _ _ _ _ S c h
  exact ⟨formClosure S c h⟩

/-- Closability after the scalar shift, including the zero-space case. -/
theorem closability : Spec.Closability.{u, v} := by
  intro 𝕜 H _ _ _ _ S c h
  exact (formClosure S c h).closable _

/-- The unique operator selected by the closed form extends S and retains c. -/
theorem extension : Spec.Extension.{u, v} := by
  intro 𝕜 H _ _ _ _ S c h F
  let T := F.closedForm.associatedOperator
  let A := realShift T c
  have hT : F.closedForm.Associated T := F.closedForm.associated
  have hd : Dense (T.domain : Set H) := F.closedForm.associated_dense F.closed
  refine ⟨A, ⟨?_, ?_, hd, ?_, ?_⟩, ?_⟩
  · simpa only [A, realShift_cancel] using hT
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨u, hu, hSu⟩ := S.mem_graph_iff.mp hp
    have hg := F.core_graph S c h u
    obtain ⟨x, hx, hTx⟩ := T.mem_graph_iff.mp hg
    exact A.mem_graph_iff.mpr ⟨x, hx.trans hu, by
      change T x + (c : 𝕜) • (x : H) = p.2
      rw [hTx, realShift_apply, hx]
      simpa using hSu⟩
  · exact realShift_selfAdjoint T hd (F.closedForm.associated_selfAdjoint F.closed) c
  · intro x
    have hn := F.closedForm.associated_nonnegative x
    change c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (x : H) (T x + (c : 𝕜) • (x : H)))
    rw [inner_add_right, inner_smul_right, map_add, RCLike.re_ofReal_mul,
      ← norm_sq_eq_re_inner]
    linarith
  · intro B hB
    apply realShift_injective (-c)
    exact F.closedForm.associated_unique hB.1 (by simpa only [A, realShift_cancel] using hT)

/-- The full Friedrichs theorem, with no assumed form-closure witness. -/
theorem friedrichs_extension : Spec.Friedrichs.{u, v} := by
  intro 𝕜 H _ _ _ _ S c h
  exact ⟨formClosure S c h, extension S c h (formClosure S c h)⟩

/-- Canonicity holds for any two realizations of the same completed form. -/
theorem canonical : Spec.Canonical.{u, v} := by
  intro 𝕜 H _ _ _ q F G A
  have he : F.closedForm.associatedOperator = G.closedForm.associatedOperator := by
    apply LinearPMap.eq_of_eq_graph
    ext ⟨u, f⟩
    rw [F.graph_iff, G.graph_iff, F.embedding_unique q G]
  constructor
  · intro hA
    have ha := F.closedForm.associated_unique hA F.closedForm.associated
    rw [ha, he]
    exact G.closedForm.associated
  · intro hA
    have ha := G.closedForm.associated_unique hA G.closedForm.associated
    rw [ha, ← he]
    exact F.closedForm.associated

end Complete
end ExpandedFA.Unbounded.FriedrichsExtension
