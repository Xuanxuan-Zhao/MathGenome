import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.ClosedNonnegativeForms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith

noncomputable section
open scoped InnerProductSpace ComplexConjugate
universe u v
namespace ExpandedFA.Unbounded.ClosedNonnegativeForms
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Closedness for a densely defined nonnegative form, in its form norm. -/
def IsClosedForm (q : NonnegativeForm 𝕜 H) : Prop := q.IsClosed

namespace NonnegativeForm
variable (q : NonnegativeForm 𝕜 H)

theorem energy_inner (x y : q.EnergySpace) :
    inner 𝕜 x y = q.form (q.toDomain x) (q.toDomain y) +
      inner 𝕜 (q.toDomain x : H) (q.toDomain y : H) := rfl

theorem energy_norm (x : q.EnergySpace) :
    ‖x‖ ^ 2 = RCLike.re (q.form (q.toDomain x) (q.toDomain x)) + ‖(q.toDomain x : H)‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), energy_inner, map_add, ← norm_sq_eq_re_inner]

theorem inclusion_bound (x : q.EnergySpace) : ‖(q.toDomain x : H)‖ ≤ ‖x‖ := by
  have hn := q.energy_norm x
  have hp := q.nonneg (q.toDomain x)
  nlinarith [norm_nonneg x, norm_nonneg (q.toDomain x : H)]

/-- The continuous, injective inclusion of the form Hilbert space into H. -/
def inclusion : q.EnergySpace →L[𝕜] H :=
  LinearMap.mkContinuous
    { toFun := fun x => (q.toDomain x : H)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (by intro x; change ‖(q.toDomain x : H)‖ ≤ 1 * ‖x‖; simpa using q.inclusion_bound x)

/-- The representation relation, before extracting its single-valued operator. -/
def relation : Submodule 𝕜 (H × H) where
  carrier := {p | ∃ hu : p.1 ∈ q.domain,
    ∀ v : q.domain, q.form v ⟨p.1, hu⟩ = inner 𝕜 (v : H) p.2}
  zero_mem' := ⟨q.domain.zero_mem, by intro v; change q.form v 0 = inner 𝕜 (v : H) 0; simp⟩
  add_mem' := by
    rintro ⟨x, f⟩ ⟨y, g⟩ ⟨hx, hfx⟩ ⟨hy, hgy⟩
    refine ⟨q.domain.add_mem hx hy, fun v => ?_⟩
    change q.form v (⟨x, hx⟩ + ⟨y, hy⟩) = inner 𝕜 (v : H) (f + g)
    rw [map_add, hfx, hgy, inner_add_right]
  smul_mem' := by
    rintro c ⟨x, f⟩ ⟨hx, hfx⟩
    refine ⟨q.domain.smul_mem c hx, fun v => ?_⟩
    change q.form v (c • ⟨x, hx⟩) = inner 𝕜 (v : H) (c • f)
    rw [map_smul, inner_smul_right, hfx]
    rfl

theorem relation_single_valued (p : H × H) (hp : p ∈ q.relation) (hzero : p.1 = 0) :
    p.2 = 0 := by
  obtain ⟨hu, hf⟩ := hp
  apply Dense.eq_of_inner_right (𝕜 := 𝕜) q.dense
  intro v hv
  have hz : (⟨p.1, hu⟩ : q.domain) = 0 := Subtype.ext hzero
  simpa only [hz, map_zero, inner_zero_right] using (hf ⟨v, hv⟩).symm

/-- Canonical associated operator; its exact graph is proved below. -/
def associatedOperator : Operator 𝕜 H H := q.relation.toLinearPMap

theorem associated_graph : q.associatedOperator.graph = q.relation :=
  Submodule.toLinearPMap_graph_eq _ q.relation_single_valued

theorem associated : q.Associated q.associatedOperator := by
  intro u f
  rw [q.associated_graph]
  rfl

theorem associated_unique {A B : Operator 𝕜 H H}
    (hA : q.Associated A) (hB : q.Associated B) : A = B := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨u, f⟩
  exact (hA u f).trans (hB u f).symm

theorem exact_domain {A : Operator 𝕜 H H} (hA : q.Associated A) (u : H) :
    u ∈ A.domain ↔ ∃ hu : u ∈ q.domain, ∃ f : H,
      ∀ v : q.domain, q.form v ⟨u, hu⟩ = inner 𝕜 (v : H) f := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨hu, huf⟩ := (hA u f).mp hf
    exact ⟨hu, f, huf⟩
  · rintro ⟨hu, f, huf⟩
    exact ⟨f, (hA u f).mpr ⟨hu, huf⟩⟩

section Complete
variable [CompleteSpace H]

/-- Riesz representation in the form Hilbert space solves the shifted equation. -/
theorem shifted_solution (hc : q.IsClosed) (f : H) :
    ∃ u : q.domain, ∀ v : q.domain,
      q.form v u + inner 𝕜 (v : H) (u : H) = inner 𝕜 (v : H) f := by
  let : CompleteSpace q.EnergySpace := hc
  let u := q.inclusion.adjoint f
  refine ⟨q.toDomain u, fun v => ?_⟩
  exact (q.energy_inner (show q.EnergySpace from v) u).symm.trans
    (q.inclusion.adjoint_inner_right (show q.EnergySpace from v) f)

/-- I+A maps its exact domain onto the whole ambient space. -/
theorem shifted_surjective (hc : q.IsClosed) (f : H) :
    ∃ u : q.associatedOperator.domain, q.associatedOperator u + (u : H) = f := by
  obtain ⟨u, hu⟩ := q.shifted_solution hc f
  have hg : ((u : H), f - (u : H)) ∈ q.associatedOperator.graph := by
    apply (q.associated _ _).mpr
    refine ⟨u.property, fun v => ?_⟩
    rw [inner_sub_right]
    exact eq_sub_iff_add_eq.mpr (hu v)
  obtain ⟨x, hx, hAx⟩ := q.associatedOperator.mem_graph_iff.mp hg
  exact ⟨x, by rw [hAx, hx]; exact sub_add_cancel f (u : H)⟩

omit [CompleteSpace H] in
theorem associated_nonnegative (x : q.associatedOperator.domain) :
    0 ≤ RCLike.re (inner 𝕜 (x : H) (q.associatedOperator x)) := by
  obtain ⟨hx, hf⟩ := (q.associated _ _).mp (q.associatedOperator.mem_graph x)
  rw [← hf ⟨x, hx⟩]
  exact q.nonneg _

omit [CompleteSpace H] in
theorem associated_formalAdjoint :
    q.associatedOperator.IsFormalAdjoint q.associatedOperator := by
  intro x y
  obtain ⟨hx, hf⟩ := (q.associated _ _).mp (q.associatedOperator.mem_graph x)
  obtain ⟨hy, hg⟩ := (q.associated _ _).mp (q.associatedOperator.mem_graph y)
  rw [← inner_conj_symm, ← hf ⟨y, hy⟩, q.hermitian, hg ⟨x, hx⟩]

theorem associated_dense (hc : q.IsClosed) : Dense (q.associatedOperator.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨u, hu⟩ := q.shifted_surjective hc f
  have ho : inner 𝕜 (u : H) f = 0 := hf u u.property
  rw [← hu, inner_add_right] at ho
  have hr := congrArg RCLike.re ho
  rw [map_add, map_zero, ← norm_sq_eq_re_inner] at hr
  have hp := q.associated_nonnegative u
  have hn : ‖(u : H)‖ = 0 := by nlinarith [sq_nonneg ‖(u : H)‖]
  have hz : u = 0 := Subtype.ext (norm_eq_zero.mp hn)
  have hfzero : f = 0 := by simpa [hz] using hu.symm
  exact hfzero

/-- A symmetric operator with a real shifted range equal to H is self-adjoint.
The proof uses the adjoint identity on the full original domain. -/
theorem associated_selfAdjoint (hc : q.IsClosed) :
    q.associatedOperator = HilbertAdjointSpec.adjointValue q.associatedOperator := by
  let A := q.associatedOperator
  have hd : Dense (A.domain : Set H) := q.associated_dense hc
  have hs : A.IsFormalAdjoint A := q.associated_formalAdjoint
  have hle : A ≤ A.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hd hs
  apply le_antisymm hle
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨y, hy, hyp⟩ := A.adjoint.mem_graph_iff.mp hp
  obtain ⟨u, hu⟩ := q.shifted_surjective hc (A.adjoint y + (y : H))
  have heq : (y : H) = (u : H) := by
    apply ext_inner_left 𝕜
    intro f
    obtain ⟨v, hv⟩ := q.shifted_surjective hc f
    rw [← hv, inner_add_left, inner_add_left]
    rw [(LinearPMap.adjoint_isFormalAdjoint hd).symm v y, hs v u]
    rw [← inner_add_right, ← inner_add_right, hu]
  have hvalue : A.adjoint y = A u := by
    apply add_right_cancel (b := (y : H))
    rw [← hu, heq]
  exact A.mem_graph_iff.mpr ⟨u, heq.symm.trans hy, hvalue.symm.trans hyp⟩

end Complete

end NonnegativeForm
/-- The energy norm has exactly the square prescribed in the manuscript. -/
theorem energy_norm_identity : Spec.EnergyNormIdentity.{u, v} := by
  intro 𝕜 H _ _ _ q x
  exact q.energy_norm x

/-- Exact domain, including the existential representation condition. -/
theorem exact_domain : Spec.ExactDomain.{u, v} := by
  intro 𝕜 H _ _ _ q A hA u
  exact q.exact_domain hA u

/-- Every densely defined closed nonnegative form has a unique nonnegative
self-adjoint associated operator, with the stipulated exact domain and action. -/
theorem representation : Spec.Representation.{u, v} := by
  intro 𝕜 H _ _ _ _ q hc
  refine ⟨q.associatedOperator,
    ⟨q.associated, q.associated_dense hc, q.associated_selfAdjoint hc,
      q.associated_nonnegative⟩, ?_⟩
  intro B hB
  exact q.associated_unique hB.1 q.associated

end ExpandedFA.Unbounded.ClosedNonnegativeForms
