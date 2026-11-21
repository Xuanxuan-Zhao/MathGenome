import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ClosedForm

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexConjugate InnerProductSpace
universe u v
namespace P201.Elliptic
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace DenseForm
variable (a : DenseForm 𝕜 H)

/-- Density, rather than symmetry or positivity, gives uniqueness. -/
theorem representer_unique (u : a.domain) (f g : H)
    (hf : ∀ w : a.domain, a.form u w = paperInner (𝕜 := 𝕜) f (w : H))
    (hg : ∀ w : a.domain, a.form u w = paperInner (𝕜 := 𝕜) g (w : H)) : f = g := by
  apply Dense.eq_of_inner_right (𝕜 := 𝕜) a.dense
  intro w hw
  exact (hf ⟨w, hw⟩).symm.trans (hg ⟨w, hw⟩)

/-- The relation has no vertical part, so conversion to a partial map loses nothing. -/
theorem graph_single_valued (p : H × H) (hp : p ∈ a.graph) (hzero : p.1 = 0) :
    p.2 = 0 := by
  obtain ⟨hu, hf⟩ := hp
  apply a.representer_unique ⟨p.1, hu⟩ p.2 0 hf
  have hz : (⟨p.1, hu⟩ : a.domain) = 0 := Subtype.ext hzero
  intro w
  simp [hz, paperInner]

theorem associated_graph : a.associatedOperator.graph = a.graph :=
  Submodule.toLinearPMap_graph_eq _ a.graph_single_valued

theorem mem_associated_graph (u f : H) :
    (u, f) ∈ a.associatedOperator.graph ↔
      ∃ hu : u ∈ a.domain, ∀ w : a.domain,
        a.form ⟨u, hu⟩ w = paperInner (𝕜 := 𝕜) f (w : H) := by
  rw [a.associated_graph]
  rfl

theorem associated_domain (u : H) :
    u ∈ a.associatedOperator.domain ↔
      ∃ hu : u ∈ a.domain, ∃ f : H, ∀ w : a.domain,
        a.form ⟨u, hu⟩ w = paperInner (𝕜 := 𝕜) f (w : H) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨hu, huf⟩ := (a.mem_associated_graph u f).mp hf
    exact ⟨hu, f, huf⟩
  · rintro ⟨hu, f, hf⟩
    exact ⟨f, (a.mem_associated_graph u f).mpr ⟨hu, hf⟩⟩

/-- Equality of the full operators, including their exact domains and actions. -/
theorem toNonnegative_operator (hs : a.IsHermitian) (hn : a.IsNonnegative) :
    a.associatedOperator = (a.toNonnegative hs hn).associatedOperator := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨u, f⟩
  rw [a.mem_associated_graph, (a.toNonnegative hs hn).associated]
  rfl

end DenseForm

/-- The concrete slot and scalar bridges, over either R or C. -/
theorem form_conventions : ClosedFormExpected.Conventions.{u, v} := by
  intro 𝕜 H _ _ _ a hs hn
  exact ⟨fun _ _ => rfl, fun x => RCLike.conj_eq_iff_re.mp (hs x x),
    fun _ _ => rfl,
    fun _ _ _ => inner_smul_right _ _ _, fun _ _ _ => inner_smul_left _ _ _⟩

/-- Canonical associated operator for every densely defined sesquilinear form. -/
theorem canonical_operator : ClosedFormExpected.CanonicalOperator.{u, v} := by
  intro 𝕜 H _ _ _ a
  refine ⟨a.mem_associated_graph, a.associated_domain, a.representer_unique, ?_⟩
  intro u
  exact (a.mem_associated_graph _ _).mp (a.associatedOperator.mem_graph u)

/-- Closed nonnegative Hermitian forms, with the canonical operator and actual
shifted inverse on the form energy space. -/
theorem closed_form : ClosedFormExpected.ClosedForm.{u, v} := by
  intro 𝕜 H _ _ _ _ a hs hn q hc
  let : CompleteSpace q.EnergySpace := hc
  let S : H →L[𝕜] q.EnergySpace := q.inclusion.adjoint
  have hA : a.associatedOperator = q.associatedOperator := a.toNonnegative_operator hs hn
  have hsol (f : H) (w : a.domain) :
      a.form (q.toDomain (S f)) w + inner 𝕜 (w : H) (q.inclusion (S f)) =
        inner 𝕜 (w : H) f := by
    exact (q.energy_inner (show q.EnergySpace from w) (S f)).symm.trans
      (q.inclusion.adjoint_inner_right (show q.EnergySpace from w) f)
  refine ⟨?_, ?_, ?_, ?_, S, ?_, ?_, ?_, ?_⟩
  · exact q.energy_norm
  · rw [hA]
    exact q.associated_dense hc
  · rw [hA]
    exact q.associated_selfAdjoint hc
  · rw [hA]
    exact q.associated_nonnegative
  · intro f
    have he : ‖S f‖ ^ 2 = RCLike.re (inner 𝕜 (q.inclusion (S f)) f) := by
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜)]
      exact congrArg RCLike.re (q.inclusion.adjoint_inner_right (S f) f)
    have hi := q.inclusion_bound (S f)
    have hb := re_inner_le_norm (𝕜 := 𝕜) (q.inclusion (S f)) f
    have hm := mul_le_mul_of_nonneg_right hi (norm_nonneg f)
    change ‖q.inclusion (S f)‖ * ‖f‖ ≤ ‖S f‖ * ‖f‖ at hm
    nlinarith [norm_nonneg (S f), norm_nonneg f]
  · intro f u
    constructor
    · intro hu
      have he (w : q.EnergySpace) : inner 𝕜 w (show q.EnergySpace from u) = inner 𝕜 w (S f) := by
        rw [q.energy_inner, q.energy_inner]
        exact (hu (q.toDomain w)).trans (hsol f (q.toDomain w)).symm
      exact congrArg q.toDomain (ext_inner_left 𝕜 he)
    · rintro rfl
      exact hsol f
  · intro u f
    rw [a.mem_associated_graph]
    constructor
    · rintro ⟨hu, huf⟩
      have he (w : q.EnergySpace) :
          inner 𝕜 w (show q.EnergySpace from ⟨u, hu⟩) = inner 𝕜 w (S f) := by
        rw [q.energy_inner, q.energy_inner]
        change a.form ⟨u, hu⟩ (q.toDomain w) + inner 𝕜 (q.toDomain w : H) u =
          a.form (q.toDomain (S f)) (q.toDomain w) +
            inner 𝕜 (q.toDomain w : H) (q.inclusion (S f))
        rw [huf, hsol, paperInner, inner_sub_right, sub_add_cancel]
      exact congrArg (fun x => q.inclusion x) (ext_inner_left 𝕜 he).symm
    · intro hu
      refine ⟨hu ▸ (q.toDomain (S f)).property, fun w => ?_⟩
      have hsub : (⟨u, hu ▸ (q.toDomain (S f)).property⟩ : a.domain) = q.toDomain (S f) :=
        Subtype.ext hu.symm
      rw [hsub]
      change a.form (q.toDomain (S f)) w = inner 𝕜 (w : H) (f - u)
      rw [inner_sub_right, ← hu]
      exact eq_sub_iff_add_eq.mpr (hsol f w)
  · intro hj
    exact hj.comp_clm S

end P201.Elliptic
