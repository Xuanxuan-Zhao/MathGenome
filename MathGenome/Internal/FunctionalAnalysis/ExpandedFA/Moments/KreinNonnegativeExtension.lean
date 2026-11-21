import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.KreinNonnegativeExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosedNonnegativeForms
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.FunProp

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexConjugate InnerProductSpace Topology
open UniformSpace Filter
universe u
namespace ExpandedFA.Moments.KreinNonnegativeExtension
open ExpandedFA.Unbounded ExpandedFA.Unbounded.FriedrichsExtension
open ExpandedFA.Unbounded.ClosedNonnegativeForms
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0)

@[simp] theorem classMap_inner (x y : S.domain) :
    inner ℂ (classMap S h x) (classMap S h y) = inner ℂ (x : H) (S y) :=
  Completion.inner_coe (show EnergyCore S h from x) (show EnergyCore S h from y)

theorem classMap_dense : DenseRange (classMap S h) := by
  change DenseRange ((↑) : EnergyCore S h → Completion (EnergyCore S h))
  exact Completion.denseRange_coe

@[simp] theorem classMap_norm (y : S.domain) :
    ‖classMap S h y‖ = ‖(show EnergyCore S h from y)‖ :=
  Completion.norm_coe _

/-- The completion identifies exactly the null vectors of the original form. -/
theorem classMap_eq_zero_iff (y : S.domain) :
    classMap S h y = 0 ↔ inner ℂ (y : H) (S y) = 0 := by
  rw [← classMap_inner S h y y, inner_self_eq_zero]

theorem classMap_ext {v w : W S h}
    (hw : ∀ y : S.domain, inner ℂ v (classMap S h y) = inner ℂ w (classMap S h y)) : v = w := by
  apply ext_inner_right ℂ
  intro z
  have hc1 : Continuous (fun z : W S h => inner ℂ v z) := by fun_prop
  have hc2 : Continuous (fun z : W S h => inner ℂ w z) := by fun_prop
  exact congrFun ((classMap_dense S h).equalizer hc1 hc2 (funext hw)) z

/-- The testing relation is linear, including its precise domain. -/
def testingGraph : Submodule ℂ (H × W S h) where
  carrier := {p | ∀ y : S.domain, inner ℂ p.2 (classMap S h y) = inner ℂ p.1 (S y)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq y
    simp only [Prod.fst_add, Prod.snd_add, inner_add_left, hp y, hq y]
  smul_mem' := by
    intro c p hp y
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, hp y]

theorem testingGraph_single (p : H × W S h) (hp : p ∈ testingGraph S h)
    (hz : p.1 = 0) : p.2 = 0 := by
  apply classMap_ext S h
  intro y
  simpa only [hz, inner_zero_left] using hp y

def energyOperator : Operator ℂ H (W S h) := (testingGraph S h).toLinearPMap

theorem energyOperator_graph : (energyOperator S h).graph = testingGraph S h :=
  Submodule.toLinearPMap_graph_eq _ (testingGraph_single S h)

theorem energyOperator_graph_iff (x : H) (w : W S h) :
    (x, w) ∈ (energyOperator S h).graph ↔
      ∀ y : S.domain, inner ℂ w (classMap S h y) = inner ℂ x (S y) := by
  rw [energyOperator_graph]
  rfl

theorem core_graph (y : S.domain) :
    ((y : H), classMap S h y) ∈ (energyOperator S h).graph := by
  rw [energyOperator_graph_iff]
  exact classMap_inner S h y

theorem core_domain : S.domain ≤ (energyOperator S h).domain := by
  intro y hy
  rw [LinearPMap.mem_domain_iff]
  exact ⟨classMap S h ⟨y, hy⟩, core_graph S h ⟨y, hy⟩⟩

theorem energyOperator_on_core (y : S.domain) :
    energyOperator S h ⟨y, core_domain S h y.property⟩ = classMap S h y := by
  have hg := core_graph S h y
  rw [LinearPMap.mem_graph_iff] at hg
  obtain ⟨z, hz, hw⟩ := hg
  have he : z = ⟨y, core_domain S h y.property⟩ := Subtype.ext hz
  simpa only [he] using hw

theorem energyOperator_dense : Dense ((energyOperator S h).domain : Set H) :=
  h.dense.mono (core_domain S h)

theorem energyOperator_closed : (energyOperator S h).IsClosed := by
  rw [LinearPMap.IsClosed, energyOperator_graph]
  have he : (testingGraph S h : Set (H × W S h)) =
      ⋂ y : S.domain, {p | inner ℂ p.2 (classMap S h y) = inner ℂ p.1 (S y)} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun y => isClosed_eq (by fun_prop) (by fun_prop)

/-- Riesz representation after extension from the energy seminormed core. -/
theorem energyOperator_bounded_domain (x : H) :
    x ∈ (energyOperator S h).domain ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : S.domain, ‖inner ℂ x (S y)‖ ≤ C * ‖classMap S h y‖ := by
  constructor
  · intro hx
    let w := energyOperator S h ⟨x, hx⟩
    have hw := (energyOperator_graph_iff S h x w).mp
      ((energyOperator S h).mem_graph ⟨x, hx⟩)
    exact ⟨‖w‖, norm_nonneg _, fun y => (hw y) ▸ norm_inner_le_norm w (classMap S h y)⟩
  · rintro ⟨C, _hC, hb⟩
    let f : EnergyCore S h →ₗ[ℂ] ℂ :=
      (innerₛₗ ℂ x).comp S.toFun
    have hf : ∀ y : EnergyCore S h, ‖f y‖ ≤ C * ‖y‖ := by
      intro y
      change ‖inner ℂ x (S (show S.domain from y))‖ ≤ C * ‖y‖
      simpa only [classMap_norm] using hb (show S.domain from y)
    let F : W S h →L[ℂ] ℂ := (f.mkContinuous C hf).fromCompletion
    let w := (InnerProductSpace.toDual ℂ (W S h)).symm F
    have hw : ∀ y : S.domain, inner ℂ w (classMap S h y) = inner ℂ x (S y) := by
      intro y
      change (InnerProductSpace.toDual ℂ (W S h)) w (classMap S h y) = _
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact (f.mkContinuous C hf).fromCompletion_apply_coe (show EnergyCore S h from y)
    rw [LinearPMap.mem_domain_iff]
    exact ⟨w, (energyOperator_graph_iff S h x w).mpr hw⟩

section Pullback
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (R : Operator ℂ H V) (hd : Dense (R.domain : Set H))

/-- The form norm is the Hilbert product norm on the graph. -/
def pullbackGraphIsometry : (pullbackForm R hd).EnergySpace →ₗᵢ[ℂ] WithLp 2 (H × V) := by
  let f : (pullbackForm R hd).EnergySpace →ₗ[ℂ] WithLp 2 (H × V) :=
    ((WithLp.linearEquiv 2 ℂ (H × V)).symm.toLinearMap).comp
      ({ toFun := fun x => (((pullbackForm R hd).toDomain x : H), R ((pullbackForm R hd).toDomain x))
         map_add' := by intro x y; exact Prod.ext rfl (R.map_add _ _)
         map_smul' := by intro c x; exact Prod.ext rfl (R.map_smul _ _) } :
        (pullbackForm R hd).EnergySpace →ₗ[ℂ] H × V)
  apply f.isometryOfInner
  intro x y
  change inner ℂ ((pullbackForm R hd).toDomain x : H) ((pullbackForm R hd).toDomain y : H) +
      inner ℂ (R ((pullbackForm R hd).toDomain x)) (R ((pullbackForm R hd).toDomain y)) =
    inner ℂ (R ((pullbackForm R hd).toDomain x)) (R ((pullbackForm R hd).toDomain y)) +
      inner ℂ ((pullbackForm R hd).toDomain x : H) ((pullbackForm R hd).toDomain y : H)
  exact add_comm _ _

theorem pullbackGraphIsometry_range :
    Set.range (pullbackGraphIsometry R hd) =
      WithLp.ofLp ⁻¹' (R.graph : Set (H × V)) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact R.mem_graph _
  · intro hp
    obtain ⟨x, hx, hRx⟩ := R.mem_graph_iff.mp hp
    refine ⟨(show (pullbackForm R hd).EnergySpace from x), ?_⟩
    apply (WithLp.linearEquiv 2 ℂ (H × V)).injective
    exact Prod.ext hx hRx

/-- Closedness of R makes the graph, and hence the form space, complete. -/
theorem pullbackForm_closed [CompleteSpace H] [CompleteSpace V]
    (hc : R.IsClosed) : (pullbackForm R hd).IsClosed := by
  apply (completeSpace_iff_isComplete_range (pullbackGraphIsometry R hd).isometry.isUniformInducing).mpr
  rw [pullbackGraphIsometry_range]
  exact (hc.preimage (WithLp.prod_continuous_ofLp 2 H V)).isComplete
end Pullback

section Extension
variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- The associated operator contains every original pair (y,Sy). -/
theorem krein_extends :
    S ≤ (pullbackForm (energyOperator S h) (energyOperator_dense S h)).associatedOperator := by
  let R := energyOperator S h
  let q := pullbackForm R (energyOperator_dense S h)
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨y, hy, hSy⟩ := S.mem_graph_iff.mp hp
  apply (q.associated _ _).mpr
  have hyr : (y : H) ∈ R.domain := core_domain S h y.property
  have hpr : p.1 ∈ R.domain := hy ▸ hyr
  refine ⟨hpr, fun v => ?_⟩
  have he : (⟨p.1, hpr⟩ : R.domain) = ⟨y, hyr⟩ := Subtype.ext hy.symm
  change inner ℂ (R v) (R ⟨p.1, hpr⟩) = inner ℂ (v : H) p.2
  rw [he, energyOperator_on_core]
  have hv := (energyOperator_graph_iff S h (v : H) (R v)).mp (R.mem_graph v) y
  exact hv.trans (congrArg (inner ℂ (v : H)) hSy)

/-- The full unshifted construction. In fact this construction only uses density,
symmetry and nonnegativity, so it also applies before closing S. -/
def construction : Construction S h where
  R := energyOperator S h
  graph_iff := energyOperator_graph_iff S h
  bounded_domain := energyOperator_bounded_domain S h
  core_domain := core_domain S h
  on_core := energyOperator_on_core S h
  dense := energyOperator_dense S h
  closed := energyOperator_closed S h
  closed_form := pullbackForm_closed _ _ (energyOperator_closed S h)
  extension := (pullbackForm (energyOperator S h) (energyOperator_dense S h)).associatedOperator
  associated := NonnegativeForm.associated _
  extends_operator := krein_extends S h
  extension_dense := NonnegativeForm.associated_dense _
    (pullbackForm_closed _ _ (energyOperator_closed S h))
  selfAdjoint := NonnegativeForm.associated_selfAdjoint _
    (pullbackForm_closed _ _ (energyOperator_closed S h))
  nonnegative := NonnegativeForm.associated_nonnegative _

end Extension

/-- Existence of the Krein nonnegative extension with its full form construction,
without a strictly positive lower bound. -/
theorem krein_construction : Spec.KreinConstruction.{u} := by
  intro H _ _ _ S h _hclosed
  exact ⟨construction S h⟩

end ExpandedFA.Moments.KreinNonnegativeExtension
