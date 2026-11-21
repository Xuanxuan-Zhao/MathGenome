import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.DirichletWave
import MathGenome.Internal.LinearPDE.P201.Heat.FormDomain
import MathGenome.Internal.LinearPDE.P201.Elliptic.DirichletResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.AbstractWaveEnergy
import Mathlib.Analysis.InnerProductSpace.LinearMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTriple
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTripleTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.InhomogeneousEvolution

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Matrix.Norms.Elementwise
universe u v
open private test_smul_integrable from
  MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTriple

namespace P201.Wave
open ExpandedFA ExpandedFA.Unbounded
open ClosedNonnegativeForms Models.AbstractWaveEnergy

namespace FormData
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (d : FormData 𝕜 V H)

@[simp] theorem rangeEquiv_coe (x : V) : (d.rangeEquiv x : H) = d.j x := rfl

@[simp] theorem energy_form (x y : V) :
    d.denseForm.form (d.rangeEquiv x) (d.rangeEquiv y) = d.a x y := by
  change d.a (d.rangeEquiv.symm (d.rangeEquiv x))
    (d.rangeEquiv.symm (d.rangeEquiv y)) = _
  simp only [LinearEquiv.symm_apply_apply]

/-- Algebraic identification with the actual full energy-norm space. -/
def toEnergy : V ≃ₗ[𝕜] d.energyForm.EnergySpace := d.rangeEquiv

@[simp] theorem toEnergy_inclusion (x : V) :
    d.energyForm.inclusion (d.toEnergy x) = d.j x := rfl

theorem energy_norm (x : V) :
    ‖d.toEnergy x‖ ^ 2 = RCLike.re (d.a x x) + ‖d.j x‖ ^ 2 := by
  have h := d.energyForm.energy_norm (d.toEnergy x)
  change ‖d.toEnergy x‖ ^ 2 =
    RCLike.re (d.denseForm.form (d.rangeEquiv x) (d.rangeEquiv x)) + ‖d.j x‖ ^ 2 at h
  simpa only [d.energy_form] using h

/-- Boundedness and coercivity imply equivalence of the original full V norm
and the energy norm; no completeness assumption is hidden in FormData. -/
theorem energy_bounds :
    (∃ C : ℝ, ∀ x, ‖d.toEnergy x‖ ≤ C * ‖x‖) ∧
    (∃ C : ℝ, ∀ y, ‖d.toEnergy.symm y‖ ≤ C * ‖y‖) := by
  constructor
  · refine ⟨Real.sqrt (‖d.a‖ + ‖d.j‖ ^ 2), fun x => ?_⟩
    have ha : RCLike.re (d.a x x) ≤ ‖d.a‖ * ‖x‖ * ‖x‖ :=
      (RCLike.re_le_norm _).trans ((d.a x).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (d.a.le_opNorm x) (norm_nonneg x)))
    have hj := d.j.le_opNorm x
    have hs := Real.sq_sqrt (show 0 ≤ ‖d.a‖ + ‖d.j‖ ^ 2 by positivity)
    have hn := d.energy_norm x
    have hjj : ‖d.j x‖ ^ 2 ≤ ‖d.j‖ ^ 2 * ‖x‖ ^ 2 := by
      nlinarith [norm_nonneg (d.j x), norm_nonneg d.j, norm_nonneg x]
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith
  · obtain ⟨c, hc, hb⟩ := d.coercive
    refine ⟨(Real.sqrt c)⁻¹, fun y => ?_⟩
    let x := d.toEnergy.symm y
    have he : d.toEnergy x = y := d.toEnergy.apply_symm_apply y
    have hn := d.energy_norm x
    rw [he] at hn
    have hs := Real.sq_sqrt hc.le
    have hp : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hmul : Real.sqrt c * ‖x‖ ≤ ‖y‖ := by
      have hb' := hb x
      nlinarith [sq_nonneg ‖d.j x‖, norm_nonneg y, norm_nonneg x]
    have hh : ‖x‖ ≤ ‖y‖ / Real.sqrt c :=
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hmul)
    simpa only [div_eq_mul_inv, mul_comm] using hh

def energyEquiv : V ≃L[𝕜] d.energyForm.EnergySpace :=
  d.toEnergy.toContinuousLinearEquivOfBounds
    (Classical.choose d.energy_bounds.1) (Classical.choose d.energy_bounds.2)
    (Classical.choose_spec d.energy_bounds.1) (Classical.choose_spec d.energy_bounds.2)

theorem energy_closed [CompleteSpace V] : d.energyForm.IsClosed := by
  let e := d.energyEquiv
  let f : V ≃ᵤ d.energyForm.EnergySpace :=
    ⟨e.toEquiv, e.toContinuousLinearMap.uniformContinuous,
      e.symm.toContinuousLinearMap.uniformContinuous⟩
  exact f.completeSpace_iff.mp inferInstance

theorem operator_eq : d.operator = d.energyForm.associatedOperator :=
  d.denseForm.toNonnegative_operator _ _

/-- Both directions of the representation relation in the original form space. -/
theorem mem_graph (x h : H) :
    (x, h) ∈ d.operator.graph ↔
      ∃ v : V, d.j v = x ∧ ∀ w : V, d.a v w = inner 𝕜 (d.j w) h := by
  rw [operator, d.denseForm.mem_associated_graph]
  constructor
  · rintro ⟨hx, hf⟩
    let v := d.rangeEquiv.symm ⟨x, hx⟩
    have hv : d.rangeEquiv v = ⟨x, hx⟩ := d.rangeEquiv.apply_symm_apply _
    refine ⟨v, congrArg Subtype.val hv, fun w => ?_⟩
    simpa only [← hv, d.energy_form, P201.Elliptic.paperInner, d.rangeEquiv_coe] using
      hf (d.rangeEquiv w)
  · rintro ⟨v, rfl, hf⟩
    refine ⟨(d.rangeEquiv v).property, fun w => ?_⟩
    change d.denseForm.form (d.rangeEquiv v) w = _
    rw [← d.rangeEquiv.apply_symm_apply w]
    simpa only [d.energy_form, P201.Elliptic.paperInner, d.rangeEquiv_coe] using
      hf (d.rangeEquiv.symm w)


/-- The pivot map is conjugate-linear, as required for the scalar-linear dual. -/
def pivotMap : H →L⋆[𝕜] (V →L[𝕜] 𝕜) :=
  ((ContinuousLinearMap.compL 𝕜 V H 𝕜).flip d.j).comp (innerSL 𝕜)

@[simp] theorem pivotMap_apply (x : H) : d.pivotMap x = d.pivot x := rfl

@[simp] theorem dualForm_flip (x : V) : d.a.flip x = d.dualForm x := by
  ext w
  rfl

/-- Once u is continuous in V, the claimed acceleration is genuinely L¹(V′)
for arbitrary L¹(H) forcing. This does not presume the weak equation. -/
theorem acceleration_integrable {T : ℝ} {f : ℝ → H} {u : ℝ → V}
    (hf : IntegrableOn f (Ioo 0 T)) (hu : ContinuousOn u (Icc 0 T)) :
    IntegrableOn (d.acceleration f u) (Ioo 0 T) := by
  have hp : IntegrableOn (fun t => d.pivot (f t)) (Ioo 0 T) :=
    d.pivotMap.integrable_comp hf
  have huI : IntegrableOn u (Ioo 0 T) :=
    (hu.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have ha : IntegrableOn (fun t => d.dualForm (u t)) (Ioo 0 T) :=
    d.a.flip.integrable_comp huI
  refine ⟨?_, ?_⟩
  · exact hp.aestronglyMeasurable.sub ha.aestronglyMeasurable
  · exact (hp.sub ha).hasFiniteIntegral

/-- Scalar testing determines the actual distributional acceleration in V′.
This holds for every weak energy solution with L¹ forcing, without any
spectral representation assumption on that solution. -/
theorem IsSolution.acceleration_derivative
    [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    {T : ℝ} {g : V} {h : H} {f : ℝ → H} {u : ℝ → V} {vel : ℝ → H}
    (huv : d.IsSolution T g h f u vel) (hf : IntegrableOn f (Ioo 0 T)) :
    Evolution.HilbertTripleSpec.derivativeValue T
      (fun t => d.pivot (vel t)) (d.acceleration f u) := by
  have hv : IntegrableOn (fun t => d.pivot (vel t)) (Ioo 0 T) :=
    d.pivotMap.integrable_comp
      ((huv.continuous_velocity.integrableOn_compact isCompact_Icc).mono_set
        Ioo_subset_Icc_self)
  have ha := d.acceleration_integrable hf huv.continuous_position
  refine ⟨hv.locallyIntegrableOn, ha.locallyIntegrableOn, ?_⟩
  intro φ hφ
  have hdφ : Evolution.IsTimeTest T (deriv φ) :=
    ⟨hφ.1.deriv', hφ.2.1.deriv, tsupport_deriv_subset.trans hφ.2.2⟩
  have hi₁ := (test_smul_integrable hv.locallyIntegrableOn hdφ).restrict
    (s := Ioo 0 T)
  have hi₂ := (test_smul_integrable ha.locallyIntegrableOn hφ).restrict
    (s := Ioo 0 T)
  ext w
  simp only [Evolution.HilbertTripleSpec.timeMeasureValue]
  rw [ContinuousLinearMap.integral_apply hi₁, neg_apply,
    ContinuousLinearMap.integral_apply hi₂]
  have he := congrArg (starRingEnd 𝕜) ((huv.equation w).2.2 φ hφ)
  change conj (∫ t, deriv φ t • inner 𝕜 (d.j w) (vel t)
      ∂Evolution.HilbertTripleSpec.timeMeasureValue T) =
    conj (-(∫ t, φ t • (inner 𝕜 (d.j w) (f t) - d.a (u t) w)
      ∂Evolution.HilbertTripleSpec.timeMeasureValue T)) at he
  rw [map_neg, ← integral_conj, ← integral_conj] at he
  simp only [starRingEnd_apply, star_smul, star_trivial] at he
  simp only [← starRingEnd_apply, map_sub, inner_conj_symm, d.hermitian,
    Evolution.HilbertTripleSpec.timeMeasureValue] at he
  simpa only [FormData.pivot, FormData.acceleration,
    FormData.dualForm, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    smul_apply, sub_apply] using he

/-- Coercivity makes the energy positive definite on exactly V × H. -/
theorem energy_eq_zero_iff (x : V) (y : H) :
    d.energy x y = 0 ↔ x = 0 ∧ y = 0 := by
  obtain ⟨c, hc, hb⟩ := d.coercive
  constructor
  · intro he
    have hx := hb x
    have hy := sq_nonneg ‖y‖
    unfold energy at he
    have hcx : c * ‖x‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (mul_nonneg hc.le (sq_nonneg _))
    have hx2 : ‖x‖ ^ 2 = 0 := (mul_eq_zero.mp hcx).resolve_left hc.ne'
    have hnx : ‖x‖ = 0 := by
      nlinarith [norm_nonneg x]
    have hny : ‖y‖ = 0 := by
      nlinarith [norm_nonneg y, sq_nonneg ‖x‖]
    exact ⟨norm_eq_zero.mp hnx, norm_eq_zero.mp hny⟩
  · rintro ⟨rfl, rfl⟩
    simp [energy]

/-- Differences retain the full weak solution class, including endpoints. -/
theorem IsSolution.sub [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    {T : ℝ} {g g' : V} {h h' : H} {f f' : ℝ → H}
    {u z : ℝ → V} {vel w : ℝ → H}
    (huv : d.IsSolution T g h f u vel) (hzw : d.IsSolution T g' h' f' z w) :
    d.IsSolution T (g - g') (h - h') (f - f') (u - z) (vel - w) where
  continuous_position := huv.continuous_position.sub hzw.continuous_position
  continuous_velocity := huv.continuous_velocity.sub hzw.continuous_velocity
  derivative t ht := by
    simpa only [Pi.sub_apply, Pi.sub_def, map_sub] using
      (huv.derivative t ht).sub (hzw.derivative t ht)
  initial_position := by simp only [Pi.sub_apply, huv.initial_position, hzw.initial_position]
  initial_velocity := by simp only [Pi.sub_apply, huv.initial_velocity, hzw.initial_velocity]
  equation v := by
    have hu := huv.equation v
    have hz := hzw.equation v
    have hd : Evolution.HilbertTripleSpec.derivativeValue T
        (fun t => inner 𝕜 (d.j v) (vel t) - inner 𝕜 (d.j v) (w t))
        (fun t => (inner 𝕜 (d.j v) (f t) - d.a (u t) v) -
          (inner 𝕜 (d.j v) (f' t) - d.a (z t) v)) := by
      refine ⟨hu.1.sub hz.1, hu.2.1.sub hz.2.1, ?_⟩
      intro φ hφ
      have hiu := Evolution.hasTimeDerivative_test_integrable T _ _ hu φ hφ
      have hiz := Evolution.hasTimeDerivative_test_integrable T _ _ hz φ hφ
      simp only [Evolution.timeMeasure] at hiu hiz
      calc
        _ = (∫ t, deriv φ t • inner 𝕜 (d.j v) (vel t)
            ∂Evolution.HilbertTripleSpec.timeMeasureValue T) -
            (∫ t, deriv φ t • inner 𝕜 (d.j v) (w t)
            ∂Evolution.HilbertTripleSpec.timeMeasureValue T) := by
          simpa only [smul_sub] using integral_sub hiu.1 hiz.1
        _ = -((∫ t, φ t • (inner 𝕜 (d.j v) (f t) - d.a (u t) v)
            ∂Evolution.HilbertTripleSpec.timeMeasureValue T) -
            (∫ t, φ t • (inner 𝕜 (d.j v) (f' t) - d.a (z t) v)
            ∂Evolution.HilbertTripleSpec.timeMeasureValue T)) := by
          rw [hu.2.2 φ hφ, hz.2.2 φ hφ]
          abel
        _ = _ := by
          rw [← integral_sub hiu.2 hiz.2]
          simp only [smul_sub]
    have hrhs : (fun t => (inner 𝕜 (d.j v) (f t) - d.a (u t) v) -
          (inner 𝕜 (d.j v) (f' t) - d.a (z t) v)) =
        (fun t => inner 𝕜 (d.j v) ((f - f') t) - d.a ((u - z) t) v) := by
      funext t
      simp only [Pi.sub_apply, map_sub, sub_apply, inner_sub_right]
      abel
    rw [hrhs] at hd
    simpa only [Pi.sub_apply, inner_sub_right] using hd

/-- Vanishing difference energy gives uniqueness in both original norms. -/
theorem eqOn_of_difference_energy {T : ℝ} {u z : ℝ → V} {vel w : ℝ → H}
    (he : ∀ t ∈ Icc 0 T, d.energy (u t - z t) (vel t - w t) = 0) :
    EqOn u z (Icc 0 T) ∧ EqOn vel w (Icc 0 T) := by
  constructor
  · intro t ht
    exact sub_eq_zero.mp ((d.energy_eq_zero_iff _ _).mp (he t ht)).1
  · intro t ht
    exact sub_eq_zero.mp ((d.energy_eq_zero_iff _ _).mp (he t ht)).2

end FormData

namespace RootTransport
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (q : NonnegativeForm 𝕜 H) (S : Operator 𝕜 H H)
  (hdom : S.domain = q.domain)
  (hnorm : ∀ (x : q.domain) (hx : (x : H) ∈ S.domain),
    RCLike.re (q.form x x) = ‖S ⟨x, hx⟩‖ ^ 2)

/-- The sum graph norm is equivalent to the original full energy norm. -/
def linearEquiv : q.EnergySpace ≃ₗ[𝕜] GraphDomain S where
  toFun x := (⟨(q.toDomain x : H), hdom.symm ▸ (q.toDomain x).property⟩ : S.domain)
  invFun x := (show q.EnergySpace from
    ⟨(GraphDomain.toDomain S x : H), hdom ▸ (GraphDomain.toDomain S x).property⟩)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem position_linearEquiv (x : q.EnergySpace) :
    position S (linearEquiv q S hdom x) = q.inclusion x := rfl

include hnorm in
theorem norm_identity (x : q.EnergySpace) :
    ‖x‖ ^ 2 = ‖position S (linearEquiv q S hdom x)‖ ^ 2 +
      ‖Models.AbstractWaveEnergy.gradient S (linearEquiv q S hdom x)‖ ^ 2 := by
  rw [q.energy_norm]
  rw [hnorm (q.toDomain x)]
  exact add_comm _ _

def equiv : q.EnergySpace ≃L[𝕜] GraphDomain S :=
  (linearEquiv q S hdom).toContinuousLinearEquivOfBounds 2 1
    (by
      intro x
      have he := norm_identity q S hdom hnorm x
      change ‖position S (linearEquiv q S hdom x)‖ +
        ‖Models.AbstractWaveEnergy.gradient S (linearEquiv q S hdom x)‖ ≤ 2 * ‖x‖
      nlinarith [norm_nonneg x, norm_nonneg (position S (linearEquiv q S hdom x)),
        norm_nonneg (Models.AbstractWaveEnergy.gradient S (linearEquiv q S hdom x)),
        sq_nonneg (‖position S (linearEquiv q S hdom x)‖ -
          ‖Models.AbstractWaveEnergy.gradient S (linearEquiv q S hdom x)‖)])
    (by
      intro y
      have he := norm_identity q S hdom hnorm ((linearEquiv q S hdom).symm y)
      rw [(linearEquiv q S hdom).apply_symm_apply] at he
      change ‖(linearEquiv q S hdom).symm y‖ ≤
        1 * (‖position S y‖ + ‖Models.AbstractWaveEnergy.gradient S y‖)
      nlinarith [norm_nonneg ((linearEquiv q S hdom).symm y),
        norm_nonneg (position S y), norm_nonneg (Models.AbstractWaveEnergy.gradient S y)])


/-- Polarization of the square-root energy, proved on the operator core and
extended in the energy topology. This fixes both complex slots. -/
theorem form_identity [CompleteSpace H] (hc : q.IsClosed)
    (hd : Dense (S.domain : Set H)) (hsa : S.adjoint = S)
    (hsq : OperatorDomainsSpec.productValue S S = q.associatedOperator)
    (x y : q.EnergySpace) :
    q.form (q.toDomain y) (q.toDomain x) =
      inner 𝕜 (Models.AbstractWaveEnergy.gradient S (equiv q S hdom hnorm y))
        (Models.AbstractWaveEnergy.gradient S (equiv q S hdom hnorm x)) := by
  have hS : S.IsFormalAdjoint S := by
    have h := LinearPMap.adjoint_isFormalAdjoint hd
    rwa [hsa] at h
  let e := equiv q S hdom hnorm
  have hcont : Continuous (fun z : q.EnergySpace => q.form (q.toDomain y) (q.toDomain z)) := by
    have he (z : q.EnergySpace) :
        q.form (q.toDomain y) (q.toDomain z) =
          inner 𝕜 y z - inner 𝕜 (q.inclusion y) (q.inclusion z) := by
      rw [q.energy_inner]
      change q.form (q.toDomain y) (q.toDomain z) =
        (q.form (q.toDomain y) (q.toDomain z) + inner 𝕜 (q.inclusion y) (q.inclusion z)) -
          inner 𝕜 (q.inclusion y) (q.inclusion z)
      abel
    simp_rw [he]
    fun_prop
  apply (P201.Heat.FormDomain.operatorCore_dense q hc).induction
    (P := fun z => q.form (q.toDomain y) (q.toDomain z) =
      inner 𝕜 (Models.AbstractWaveEnergy.gradient S (e y))
        (Models.AbstractWaveEnergy.gradient S (e z))) ?_ ?_ x
  · intro z hz
    let zc : P201.Heat.FormDomain.operatorCore q := ⟨z, hz⟩
    obtain ⟨hSz, hval⟩ := P201.Heat.FormDomain.core_square_eval q S hsq zc
    obtain ⟨hzdom, ha⟩ := (q.associated _ _).mp
      (q.associatedOperator.mem_graph ⟨q.inclusion z, hz⟩)
    change q.form (q.toDomain y) (q.toDomain z) =
      inner 𝕜 (S (GraphDomain.toDomain S (e y)))
        (S (P201.Heat.FormDomain.coreToRoot q S hsq zc))
    rw [hS (GraphDomain.toDomain S (e y))
      ⟨S (P201.Heat.FormDomain.coreToRoot q S hsq zc), hSz⟩, hval]
    exact ha (q.toDomain y)
  · apply isClosed_eq hcont
    exact continuous_const.inner
      ((Models.AbstractWaveEnergy.gradient S).continuous.comp e.continuous)

end RootTransport

namespace FormData
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (d : FormData 𝕜 V H) (F : WaveFamily (𝕜 := 𝕜) (H := H))
  (hr : d.RootClaims F)

/-- The original V is precisely the graph-norm displacement domain used by
the library's wave evolution, with no operator-domain regularity on the data. -/
def graphEquiv : V ≃L[𝕜] GraphDomain F.S :=
  d.energyEquiv.trans (RootTransport.equiv d.energyForm F.S hr.2.1
    (by
      intro x hx
      obtain ⟨v, hv⟩ := x.property
      have he : d.rangeEquiv v = x := Subtype.ext hv
      subst x
      simpa only [FormData.energyForm, P201.Elliptic.DenseForm.toNonnegative,
        LinearMap.flip_apply, d.energy_form, d.rangeEquiv_coe] using hr.2.2 v hx))

@[simp] theorem graphEquiv_position (x : V) :
    position F.S (d.graphEquiv F hr x) = d.j x := rfl

theorem graphEquiv_energy (x : V) :
    ‖Models.AbstractWaveEnergy.gradient F.S (d.graphEquiv F hr x)‖ ^ 2 = RCLike.re (d.a x x) :=
  (hr.2.2 x (GraphDomain.toDomain F.S (d.graphEquiv F hr x)).property).symm


/-- Equality of the full sesquilinear form, not just its real diagonal. -/
theorem graphEquiv_form [CompleteSpace V] [CompleteSpace H]
    (hd : Dense (F.S.domain : Set H)) (hsa : F.S.adjoint = F.S) (x y : V) :
    d.a x y = inner 𝕜
      (Models.AbstractWaveEnergy.gradient F.S (d.graphEquiv F hr y))
      (Models.AbstractWaveEnergy.gradient F.S (d.graphEquiv F hr x)) := by
  have h := RootTransport.form_identity d.energyForm F.S hr.2.1
    (by
      intro z hz
      obtain ⟨v, hv⟩ := z.property
      have he : d.rangeEquiv v = z := Subtype.ext hv
      subst z
      simpa only [FormData.energyForm, P201.Elliptic.DenseForm.toNonnegative,
        LinearMap.flip_apply, d.energy_form, d.rangeEquiv_coe] using hr.2.2 v hz)
    d.energy_closed hd hsa (hr.1.trans d.operator_eq) (d.toEnergy x) (d.toEnergy y)
  have hh : d.energyForm.form (d.energyForm.toDomain (d.toEnergy y))
      (d.energyForm.toDomain (d.toEnergy x)) = d.a x y := d.energy_form x y
  rw [hh] at h
  exact h

end FormData

/-- The acceleration part of W05 for the entire stated weak solution class. -/
theorem weak_acceleration : DirichletWaveExpected.AccelerationTheorem.{u, v} := by
  intro 𝕜 _ V H _ _ _ _ _ _ d T g h f u vel hf huv
  exact ⟨d.acceleration_integrable hf huv.continuous_position,
    FormData.IsSolution.acceleration_derivative d huv hf⟩

/-- Canonical real spectral wave family and exact root-domain bridge. -/
theorem real_spectral_bridge {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : FormData ℝ V H) :
    ∃ C : RealNonnegativeSpectralCalculus.Calculus (H := H),
      C.integral RealNonnegativeSpectralCalculus.coordinate = d.operator ∧
      d.RootClaims (realFamily C) ∧ WaveTheorem d.operator (realFamily C) := by
  have hd := d.energyForm.associated_dense d.energy_closed
  have hs := (d.energyForm.associated_selfAdjoint d.energy_closed).symm
  have hn := d.energyForm.associated_nonnegative
  rw [← d.operator_eq] at hd hs hn
  obtain ⟨C, hC, hW⟩ := real_abstract_wave_energy H d.operator ⟨hd, hs, hn⟩
  have hsq := hW.1.2.1
  have hsa := hW.1.1.2.1
  obtain ⟨hdom, hnorm⟩ := P201.Heat.FormDomain.root_identification d.energyForm
    (realFamily C).S (hsq.trans d.operator_eq) d.energy_closed hW.1.1.1 hsa
  refine ⟨C, hC, ⟨hsq, hdom, ?_⟩, hW⟩
  intro x hx
  simpa only [FormData.energyForm, P201.Elliptic.DenseForm.toNonnegative,
    LinearMap.flip_apply, d.energy_form, d.rangeEquiv_coe] using hnorm (d.rangeEquiv x) hx

/-- Canonical complex spectral wave family, including slot and domain conventions. -/
theorem complex_spectral_bridge {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : FormData ℂ V H) :
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H)
      (C : MeasurableSpectralCalculus.BoundedRealization E),
      MeasurableSpectralCalculus.measurableIntegral C (complexSymbol RealSymbols.coordinate) =
        d.operator ∧ d.RootClaims (complexFamily C) ∧ WaveTheorem d.operator (complexFamily C) := by
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  have hd := d.energyForm.associated_dense d.energy_closed
  have hs := (d.energyForm.associated_selfAdjoint d.energy_closed).symm
  have hn := d.energyForm.associated_nonnegative
  rw [← d.operator_eq] at hd hs hn
  obtain ⟨E, C, hC, hW⟩ := complex_abstract_wave_energy H d.operator ⟨hd, hs, hn⟩
  have hsq := hW.1.2.1
  have hsa := hW.1.1.2.1
  obtain ⟨hdom, hnorm⟩ := P201.Heat.FormDomain.root_identification d.energyForm
    (complexFamily C).S (hsq.trans d.operator_eq) d.energy_closed hW.1.1.1 hsa
  refine ⟨E, C, hC, ⟨hsq, hdom, ?_⟩, hW⟩
  intro x hx
  simpa only [FormData.energyForm, P201.Elliptic.DenseForm.toNonnegative,
    LinearMap.flip_apply, d.energy_form, d.rangeEquiv_coe] using hnorm (d.rangeEquiv x) hx


/-- Transfer the pinned homogeneous theorem to the original coercive form
space, including the full complex weak equation. -/
theorem homogeneous_of_spectral {𝕜 : Type*} [RCLike 𝕜]
    {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
    (d : FormData 𝕜 V H) (F : WaveFamily (𝕜 := 𝕜) (H := H))
    (hr : d.RootClaims F) (hW : WaveTheorem d.operator F) : d.HomogeneousClaims F := by
  intro g h
  let e := d.graphEquiv F hr
  obtain ⟨z, hpos, hz, hz0, hv0, huniq, hen⟩ := hW.2.1 (e g) h
  let u : ℝ → V := fun t => e.symm (z t)
  have hu (t : ℝ) : e (u t) = z t := e.apply_symm_apply (z t)
  have hju (t : ℝ) : d.j (u t) = position F.S (z t) := by
    rw [← hu t]
    rfl
  have hweak := weak_derivative_conjugate F.S hz.weak_derivative
  refine ⟨u, F.velocity (e g) h, e.symm.continuous.comp hz.continuous_graph,
    hz.continuous_velocity, ?_, ?_, ?_, hv0, ?_, ?_⟩
  · intro t
    simpa only [hju] using hz.derivative t
  · intro w t
    have he := hweak (e w) t
    have hf := d.graphEquiv_form F hr hW.1.1.1 hW.1.1.2.1 (u t) w
    rw [hu t] at hf
    change HasDerivAt (fun s => inner 𝕜 (d.j w) (F.velocity (e g) h s))
      (-inner 𝕜 (Models.AbstractWaveEnergy.gradient F.S (e w))
        (Models.AbstractWaveEnergy.gradient F.S (z t))) t at he
    rw [← hf] at he
    exact he
  · change e.symm (z 0) = g
    rw [hz0, e.symm_apply_apply]
  · intro t
    have hene := hen t
    have hg := d.graphEquiv_energy F hr g
    have hut := d.graphEquiv_energy F hr (u t)
    rw [hu t] at hut
    change ‖Models.AbstractWaveEnergy.gradient F.S (z t)‖ ^ 2 +
      ‖F.velocity (e g) h t‖ ^ 2 =
      ‖Models.AbstractWaveEnergy.gradient F.S (e g)‖ ^ 2 + ‖h‖ ^ 2 at hene
    unfold FormData.energy
    rw [← hg, ← hut]
    linarith
  · intro t
    rw [hju, hpos]
    rfl

/-- The full homogeneous real stage of W05, with data in exactly V × H. -/
theorem homogeneous_wave_real : DirichletWaveExpected.RealHomogeneousTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  obtain ⟨C, hC, hr, hW⟩ := real_spectral_bridge d
  exact ⟨C, hC, hr, homogeneous_of_spectral d (realFamily C) hr hW⟩

/-- The full homogeneous complex stage, using the manuscript's form slots. -/
theorem homogeneous_wave_complex : DirichletWaveExpected.ComplexHomogeneousTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  obtain ⟨E, C, hC, hr, hW⟩ := complex_spectral_bridge d
  exact ⟨E, C, hC, hr, homogeneous_of_spectral d (complexFamily C) hr hW⟩


/-- The actual real Dirichlet injection works for every open set. -/
def realDirichletData {n : ℕ} (Ω : P201Specs.Domain n)
    (a : P201Specs.H10 ℝ Ω →L[ℝ] P201Specs.H10 ℝ Ω →L[ℝ] ℝ)
    (hs : ∀ x y, a x y = a y x)
    (hc : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ a x x) :
    FormData ℝ (P201Specs.H10 ℝ Ω) (P201Specs.Lp ℝ Ω 2) where
  j := P201Specs.hZeroUnderlying Ω
  injective := P201.DirichletResolvent.inclusion_injective Ω
  dense := P201.DirichletResolvent.inclusion_dense Ω
  a := a
  hermitian := hs
  coercive := hc

/-- The complex injection has the same actual full-H¹ closure as H07. -/
def complexDirichletData {n : ℕ} (Ω : P201Specs.Domain n)
    (a : P201Specs.H10 ℂ Ω →L[ℂ] P201Specs.H10 ℂ Ω →L⋆[ℂ] ℂ)
    (hs : ∀ x y, conj (a x y) = a y x)
    (hc : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ (a x x).re) :
    FormData ℂ (P201Specs.H10 ℂ Ω) (P201Specs.Lp ℂ Ω 2) where
  j := P201Specs.hZeroUnderlying Ω
  injective := P201.Heat.FormDomain.dirichlet_injective Ω
  dense := P201.Heat.FormDomain.dirichlet_dense Ω
  a := a
  hermitian := hs
  coercive := hc

/-- A reduction, not an assumed proof of the abstract L¹ theorem. -/
theorem real_dirichlet_of_abstract (hreal : DirichletWaveExpected.RealTheorem.{0, 0}) :
    DirichletWaveExpected.RealDirichletTheorem := by
  intro m Ω hΩ hne a hs hc
  let d := realDirichletData Ω a hs hc
  exact ⟨d, rfl, fun _ _ => rfl, hreal d⟩

theorem complex_dirichlet_of_abstract (hcomplex : DirichletWaveExpected.ComplexTheorem.{0, 0}) :
    DirichletWaveExpected.ComplexDirichletTheorem := by
  intro m Ω hΩ hne a hs hc
  let d := complexDirichletData Ω a hs hc
  exact ⟨d, rfl, rfl, hcomplex d⟩

/-- The matrix realization and the physical homogeneous trace reduce to the
same abstract form theorem. No coefficient-specific assumption enters it. -/
theorem elliptic_of_abstract (hreal : DirichletWaveExpected.RealTheorem.{0, 0}) :
    DirichletWaveExpected.EllipticTheorem := by
  intro m Ω hΩ hne A hA lam hlam hell hsym
  obtain ⟨C, hC, hnorm, hforms⟩ := P201.Dirichlet.form_bridge
    (by omega : 1 ≤ m + 1) Ω
    (P102.Sobolev.Rellich.bounded_domain (P201Specs.graphFrame m) Ω hΩ)
  obtain ⟨B, hB, hbound, hcoerc⟩ := hforms A hA
  let a := B.bilinearComp (P201Specs.Dirichlet.zeroInclusion Ω)
    (P201Specs.Dirichlet.zeroInclusion Ω)
  have ha (x y : P201Specs.H10 ℝ Ω) :
      a x y = P201Specs.ellipticEnergyForm Ω A x.val y.val := hB _ _
  have hs (x y : P201Specs.H10 ℝ Ω) : a x y = a y x := by
    rw [ha, ha]
    exact (P201.Dirichlet.form_apply Ω A hA x.val y.val).symm.trans
      ((P201.Dirichlet.form_symmetric Ω A hA hsym x.val y.val).trans
        (P201.Dirichlet.form_apply Ω A hA y.val x.val))
  have hc : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ a x x :=
    ⟨lam / C ^ 2, by positivity, hcoerc lam hlam hell⟩
  let d := realDirichletData Ω a hs hc
  refine ⟨d, rfl, ha, ?_, hreal d, ?_⟩
  · intro x h
    rw [d.mem_graph]
    constructor
    · rintro ⟨v, hv, hform⟩
      refine ⟨v, hv, fun w => ?_⟩
      rw [← ha]
      exact (hform w).trans (real_inner_comm _ _)
    · rintro ⟨v, hv, hsol⟩
      refine ⟨v, hv, fun w => ?_⟩
      change a v w = inner ℝ (P201Specs.hZeroUnderlying Ω w) h
      rw [ha, hsol w]
      change inner ℝ h (P201Specs.hZeroUnderlying Ω w) =
        inner ℝ (P201Specs.hZeroUnderlying Ω w) h
      exact real_inner_comm _ _
  · obtain ⟨trace, lift, hagree, hsurj, hlift, hker⟩ := P201.Trace.exact_trace m Ω hΩ
    refine ⟨trace, hagree, hker, fun x => ?_⟩
    change x.val ∈ trace.ker
    rw [hker]
    exact x.property

end P201.Wave

open Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate
open ExpandedFA
namespace P201.Wave

/-- Distribution derivative plus continuity yields exact endpoint increments. -/
theorem continuous_derivative_increments {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 < T) (x g : ℝ → E)
    (hx : ContinuousOn x (Icc 0 T)) (hg : IntegrableOn g (Ioo 0 T))
    (hd : Evolution.HilbertTripleSpec.derivativeValue T x g) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, x t - x s = ∫ r in s..t, g r := by
  have hxi : IntegrableOn x (Ioo 0 T) :=
    (hx.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  obtain ⟨P, hPc, hPae, hPinc⟩ :=
    Evolution.hasTimeDerivative_continuous_primitive T x g hxi hg hd
  have ho : EqOn x P (Ioo 0 T) :=
    Measure.eqOn_open_of_ae_eq hPae isOpen_Ioo (hx.mono Ioo_subset_Icc_self)
      (hPc.continuousOn)
  have hc : EqOn x P (Icc 0 T) := by
    apply ho.of_subset_closure hx hPc.continuousOn Ioo_subset_Icc_self
    rw [closure_Ioo (ne_of_lt hT)]
  intro s hs t ht
  rw [hc ht, hc hs]
  exact hPinc ⟨s, hs⟩ ⟨t, ht⟩

end P201.Wave

open P201.Wave ExpandedFA
namespace P201.Wave.FormData
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type u} {H : Type v}
 [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
 [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (d : FormData 𝕜 V H)
 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
 [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

def realForm : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => RCLike.re (d.a x y))
      (by intros; simp) (by intros; simp [RCLike.smul_re])
      (by intros; simp) (by
        intro c x y
        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smulₛₗ]
        simp))
    ‖d.a‖ (by intro x y; exact (RCLike.norm_re_le_norm _).trans (d.a.le_opNorm₂ x y))

omit [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
@[simp] theorem realForm_apply (x y : V) : d.realForm x y = RCLike.re (d.a x y) := rfl

omit [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem realForm_symm (x y : V) : d.realForm x y = d.realForm y x := by
  change RCLike.re (d.a x y) = RCLike.re (d.a y x)
  rw [← d.hermitian x y, RCLike.conj_re]

variable [CompleteSpace V]

theorem homogeneous_zero
    {T : ℝ} (hT : 0 < T) {u : ℝ → V} {vel : ℝ → H}
    (huv : d.IsSolution T 0 0 (fun _ => 0) u vel) :
    ∀ t ∈ Icc 0 T, u t = 0 ∧ vel t = 0 := by
  let U : ℝ → V := fun t => ∫ r in 0..t, u r
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hui : IntegrableOn u (Icc 0 T) :=
    huv.continuous_position.integrableOn_compact isCompact_Icc
  have hUi (t : ℝ) (ht : t ∈ Icc 0 T) : IntervalIntegrable u volume 0 t :=
    (hui.mono_set (uIcc_subset_Icc h0 ht)).intervalIntegrable
  have hUc : ContinuousOn U (Icc 0 T) := by
    simpa only [U, uIcc_of_le hT.le] using
      intervalIntegral.continuousOn_primitive_interval
        (show IntegrableOn u (uIcc 0 T) by simpa only [uIcc_of_le hT.le] using hui)
  have hEq (t : ℝ) (ht : t ∈ Icc 0 T) (w : V) :
      inner 𝕜 (d.j w) (vel t) = -d.a (U t) w := by
    have hsc : ContinuousOn (fun t => inner 𝕜 (d.j w) (vel t)) (Icc 0 T) :=
      continuousOn_const.inner huv.continuous_velocity
    have hgc : ContinuousOn (fun t => -d.a (u t) w) (Icc 0 T) := (d.a.flip w).continuous.comp_continuousOn huv.continuous_position |>.neg
    have hgi : IntegrableOn (fun t => -d.a (u t) w) (Ioo 0 T) :=
      (hgc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hd := huv.equation w
    simp only [inner_zero_right, zero_sub] at hd
    have he := continuous_derivative_increments hT _ _ hsc hgi hd 0 h0 t ht
    simp only [huv.initial_velocity, inner_zero_right, sub_zero] at he
    rw [intervalIntegral.integral_neg] at he
    change inner 𝕜 (d.j w) (vel t) = -(∫ x in 0..t, (d.a.flip w) (u x)) at he
    rw [(d.a.flip w).intervalIntegral_comp_comm (hUi t ht)] at he
    exact he
  let E : ℝ → ℝ := fun t => d.realForm (U t) (U t) + ‖d.j (u t)‖ ^ 2
  have hEc : ContinuousOn E (Icc 0 T) := by
    apply ContinuousOn.add
    · exact d.realForm.continuous.comp_continuousOn hUc |>.clm_apply hUc
    · exact (d.j.continuous.comp_continuousOn huv.continuous_position).norm.pow 2
  have hEd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt E 0 t := by
    have hut : ContinuousAt u t :=
      huv.continuous_position.continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hUm : StronglyMeasurableAtFilter u (nhds t) volume :=
      ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun r hr => huv.continuous_position.continuousAt (Icc_mem_nhds hr.1 hr.2)) t ht
    have hUd : HasDerivAt U (u t) t :=
      intervalIntegral.integral_hasDerivAt_right (hUi t (Ioo_subset_Icc_self ht)) hUm hut
    have hud : HasDerivAt (fun r => d.j (u r)) (vel t) t :=
      (huv.derivative t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have ha : HasDerivAt (fun r => d.realForm (U r) (U r))
        (d.realForm (U t) (u t) + d.realForm (u t) (U t)) t :=
      d.realForm.hasDerivAt_of_bilinear (fun _ => hUd) (fun _ => hUd)
    have hn := RCLike.reCLM.hasFDerivAt.comp_hasDerivAt t (hud.inner 𝕜 hud)
    have hn' : HasDerivAt (fun r => ‖d.j (u r)‖ ^ 2)
        (RCLike.re (inner 𝕜 (d.j (u t)) (vel t)) +
          RCLike.re (inner 𝕜 (vel t) (d.j (u t)))) t := by
      simpa only [Function.comp_def, ← norm_sq_eq_re_inner, map_add,
        RCLike.reCLM_apply] using hn
    have hh : RCLike.re (inner 𝕜 (vel t) (d.j (u t))) =
        RCLike.re (inner 𝕜 (d.j (u t)) (vel t)) := by
      rw [← inner_conj_symm, RCLike.conj_re]
    have hs := congrArg RCLike.re (hEq t (Ioo_subset_Icc_self ht) (u t))
    have hsum : d.realForm (U t) (u t) + d.realForm (u t) (U t) +
        (RCLike.re (inner 𝕜 (d.j (u t)) (vel t)) +
          RCLike.re (inner 𝕜 (vel t) (d.j (u t)))) = 0 := by
      rw [hh, d.realForm_symm (u t) (U t), realForm_apply]
      simp only [map_neg] at hs
      linarith
    convert ha.add hn' using 1
    simp only [hsum]
  have hE0 : E 0 = 0 := by simp [E, U, huv.initial_position]
  have hEz (t : ℝ) (ht : t ∈ Icc 0 T) : E t = 0 := by
    by_cases ht0 : t = 0
    · simpa only [ht0] using hE0
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    obtain ⟨r, hr, he⟩ := exists_hasDerivAt_eq_slope E (fun _ => 0) htpos
      (hEc.mono (Icc_subset_Icc_right ht.2))
      (fun r hr => hEd r ⟨hr.1, hr.2.trans_le ht.2⟩)
    simp only [hE0, sub_zero] at he
    exact (div_eq_zero_iff.mp he.symm).resolve_right (by simpa using htpos.ne')
  intro t ht
  have he := hEz t ht
  obtain ⟨c, hc, hb⟩ := d.coercive
  have hu : u t = 0 := by
    apply d.injective
    rw [map_zero]
    apply norm_eq_zero.mp
    have hp := hb (U t)
    change RCLike.re (d.a (U t) (U t)) + ‖d.j (u t)‖ ^ 2 = 0 at he
    nlinarith [mul_nonneg hc.le (sq_nonneg ‖U t‖), norm_nonneg (d.j (u t))]
  have hU : U t = 0 := by
    apply norm_eq_zero.mp
    have hp := hb (U t)
    change RCLike.re (d.a (U t) (U t)) + ‖d.j (u t)‖ ^ 2 = 0 at he
    have hcx : c * ‖U t‖ ^ 2 = 0 := le_antisymm
      (by linarith [sq_nonneg ‖d.j (u t)‖]) (mul_nonneg hc.le (sq_nonneg _))
    have hx := (mul_eq_zero.mp hcx).resolve_left hc.ne'
    nlinarith [norm_nonneg (U t)]
  refine ⟨hu, d.dense.eq_zero_of_inner_right (𝕜 := 𝕜) ?_⟩
  intro w
  simpa only [hU, map_zero, zero_apply, neg_zero] using hEq t ht w

theorem IsSolution.eqOn
    {T : ℝ} (hT : 0 < T) {g : V} {h : H} {f : ℝ → H}
    {u z : ℝ → V} {vel w : ℝ → H}
    (huv : d.IsSolution T g h f u vel) (hzw : d.IsSolution T g h f z w) :
    EqOn u z (Icc 0 T) ∧ EqOn vel w (Icc 0 T) := by
  have hd : d.IsSolution T 0 0 (fun _ => 0) (u - z) (vel - w) := by
    simpa only [sub_self, Pi.zero_def] using huv.sub d hzw
  have hz := d.homogeneous_zero hT hd
  constructor
  · intro t ht
    exact sub_eq_zero.mp (hz t ht).1
  · intro t ht
    exact sub_eq_zero.mp (hz t ht).2

end P201.Wave.FormData

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
namespace P201.Wave
open ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

/-- The norm-square chain rule for an arbitrary Bochner-integrable primitive.
The primitive may be given by any representative with the exact increments. -/
theorem real_primitive_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) (Y G : ℝ → E)
    (hG : IntervalIntegrable G volume a b)
    (hY : ∀ t ∈ Icc a b, Y t - Y a = ∫ s in a..t, G s) :
    IntervalIntegrable (fun s => inner ℝ (Y s) (G s)) volume a b ∧
    (‖Y b‖ ^ 2 - ‖Y a‖ ^ 2) / 2 = ∫ s in a..b, inner ℝ (Y s) (G s) := by
  have hYac : AbsolutelyContinuousOnInterval Y a b :=
    FiniteEnergy.primitive_increment_ac hG (by simpa only [uIcc_of_le hab] using hY)
  have hYd := FiniteEnergy.primitive_increment_ae_deriv hab hG hY
  obtain ⟨hi, he⟩ := bilinear_integral_derivative
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) hab hYac hYac hYd hYd
  have hfun : (fun s => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) (Y s) (G s) +
      (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) (G s) (Y s)) =
      fun s => 2 * inner ℝ (Y s) (G s) := by
    funext s
    change inner ℝ (Y s) (G s) + inner ℝ (G s) (Y s) = _
    rw [real_inner_comm (G s) (Y s)]
    ring
  rw [hfun] at hi he
  have hwork : IntervalIntegrable (fun s => inner ℝ (Y s) (G s)) volume a b := by
    convert hi.const_mul (2⁻¹ : ℝ) using 1
    ext s
    ring
  refine ⟨hwork, ?_⟩
  change (∫ s in a..b, 2 * inner ℝ (Y s) (G s)) =
    inner ℝ (Y b) (Y b) - inner ℝ (Y a) (Y a) at he
  rw [intervalIntegral.integral_const_mul, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at he
  linarith

/-- All-pairs primitive energy identity, with only L¹ forcing and original endpoints. -/
theorem real_L1_primitive_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 ≤ T) (x₀ : E) (G : ℝ → E)
    (hG : IntegrableOn G (Ioo 0 T)) :
    let Y : ℝ → E := fun t => x₀ + ∫ s in (0 : ℝ)..t, G s
    ∀ r ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      IntervalIntegrable (fun s => inner ℝ (Y s) (G s)) volume r t ∧
      (‖Y t‖ ^ 2 - ‖Y r‖ ^ 2) / 2 = ∫ s in r..t, inner ℝ (Y s) (G s) := by
  intro Y
  have hGIcc : IntegrableOn G (Icc 0 T) := by
    change Integrable G (volume.restrict (Icc 0 T))
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hG
  have hGI : IntervalIntegrable G volume 0 T :=
    (show IntegrableOn G (uIcc 0 T) from by simpa [uIcc_of_le hT] using hGIcc).intervalIntegrable
  have hYi (b : ℝ) (hb : b ∈ Icc 0 T) :
      IntervalIntegrable (fun s => inner ℝ (Y s) (G s)) volume 0 b ∧
      (‖Y b‖ ^ 2 - ‖Y 0‖ ^ 2) / 2 = ∫ s in (0 : ℝ)..b, inner ℝ (Y s) (G s) := by
    have hbU : b ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using hb
    apply real_primitive_energy hb.1 Y G
      (hGI.mono_set (uIcc_subset_uIcc left_mem_uIcc hbU))
    intro s hs
    simp [Y]
  intro r hr t ht
  have hrE := hYi r hr
  have htE := hYi t ht
  refine ⟨hrE.1.symm.trans htE.1, ?_⟩
  rw [← intervalIntegral.integral_interval_sub_left htE.1 hrE.1]
  linarith [htE.2, hrE.2]

/-- Scalar-field independent form of the primitive identity.
The real Hilbert structure is derived, rather than supplied. -/
theorem L1_primitive_energy {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : ℝ} (hT : 0 ≤ T) (x₀ : E) (G : ℝ → E)
    (hG : IntegrableOn G (Ioo 0 T)) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    let Y : ℝ → E := fun t => x₀ + ∫ s in (0 : ℝ)..t, G s
    ∀ r ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      IntervalIntegrable (fun s => RCLike.re (inner 𝕜 (Y s) (G s))) volume r t ∧
      (‖Y t‖ ^ 2 - ‖Y r‖ ^ 2) / 2 = ∫ s in r..t, RCLike.re (inner 𝕜 (Y s) (G s)) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  simpa only [real_inner_eq_re_inner] using real_L1_primitive_energy hT x₀ G hG

/-- Energy work for a Duhamel orbit of an isometric group. Only the
integrability of the interaction-picture source is needed here. -/
theorem group_L1_energy {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : ℝ → E ≃ₗᵢ[𝕜] E)
    (hU0 : ∀ x, U 0 x = x)
    (hUadd : ∀ s t x, U (s + t) x = U s (U t x))
    {T : ℝ} (hT : 0 ≤ T) (x₀ : E) (F : ℝ → E)
    (hG : IntegrableOn (fun s => U (-s) (F s)) (Ioo 0 T)) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    let Z : ℝ → E := fun t => U t (x₀ + ∫ s in (0 : ℝ)..t, U (-s) (F s))
    ∀ r ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      IntervalIntegrable (fun s => RCLike.re (inner 𝕜 (Z s) (F s))) volume r t ∧
      (‖Z t‖ ^ 2 - ‖Z r‖ ^ 2) / 2 =
        ∫ s in r..t, RCLike.re (inner 𝕜 (Z s) (F s)) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let Y : ℝ → E := fun t => x₀ + ∫ s in (0 : ℝ)..t, U (-s) (F s)
  let Z : ℝ → E := fun t => U t (Y t)
  have hinner (s : ℝ) : inner 𝕜 (Z s) (F s) = inner 𝕜 (Y s) (U (-s) (F s)) := by
    have hinv : U s (U (-s) (F s)) = F s := by
      rw [← hUadd, add_neg_cancel, hU0]
    calc
      inner 𝕜 (Z s) (F s) = inner 𝕜 (U s (Y s)) (U s (U (-s) (F s))) := by rw [hinv]
      _ = _ := (U s).inner_map_map _ _
  change ∀ r ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
    IntervalIntegrable (fun s => RCLike.re (inner 𝕜 (Z s) (F s))) volume r t ∧
    (‖Z t‖ ^ 2 - ‖Z r‖ ^ 2) / 2 = ∫ s in r..t, RCLike.re (inner 𝕜 (Z s) (F s))
  intro r hr t ht
  have he := L1_primitive_energy (𝕜 := 𝕜) hT x₀ (fun s => U (-s) (F s)) hG r hr t ht
  simpa only [Y, Z, hinner, LinearIsometryEquiv.norm_map] using he
end P201.Wave

open Set
open scoped NNReal
namespace P201.Wave

/-- Uniformly bounded strong derivatives give operator norm Lipschitz bounds. -/
theorem lipschitzWith_of_strong_derivative {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A D : ℝ → X →L[ℝ] E) (K : ℝ≥0)
    (hd : ∀ (x : X) (t : ℝ), HasDerivAt (fun s => A s x) (D t x) t)
    (hD : ∀ t : ℝ, ‖D t‖ ≤ K) :
    LipschitzWith K A := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro s t
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hb : ∀ r ∈ (univ : Set ℝ), ‖D r x‖ ≤ (K : ℝ) * ‖x‖ := by
    intro r _
    exact (D r).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hD r) (norm_nonneg x))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (univ : Set ℝ)) => (hd x r).hasDerivWithinAt)
    hb convex_univ (mem_univ t) (mem_univ s)
  simpa only [sub_apply, mul_right_comm] using hh

/-- Strong differentiation with a uniform bound gives continuous action on varying vectors. -/
theorem continuous_apply_of_strong_derivative {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A D : ℝ → X →L[ℝ] E) (K : ℝ≥0)
    (hd : ∀ (x : X) (t : ℝ), HasDerivAt (fun s => A s x) (D t x) t)
    (hD : ∀ t : ℝ, ‖D t‖ ≤ K) :
    Continuous (fun p : ℝ × X => A p.1 p.2) := by
  exact ((lipschitzWith_of_strong_derivative A D K hd hD).continuous.comp
    continuous_fst).clm_apply continuous_snd

end P201.Wave

open Set Filter Topology
namespace P201.Wave

/-- A strong operator derivative suffices for the product rule; the time
family need only act jointly continuously, including on varying vectors. -/
theorem hasDerivAt_strong_apply {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → X →L[ℝ] E) (hA : Continuous (fun p : ℝ × X => A p.1 p.2))
    {Y : ℝ → X} {Y' : X} {t : ℝ} {d : E}
    (hd : HasDerivAt (fun s => A s (Y t)) d t) (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun s => A s (Y s)) (d + A t Y') t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hpair : Tendsto (fun s : ℝ => (s, slope Y t s)) (𝓝[≠] t) (𝓝 (t, Y')) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hY.tendsto_slope
  have hlim := hd.tendsto_slope.add ((hA.continuousAt (x := (t, Y'))).tendsto.comp hpair)
  convert hlim using 1
  funext s
  simp only [slope, Function.comp_def, vsub_eq_sub, map_sub, map_smul]
  rw [← smul_add]
  congr 1
  abel

end P201.Wave

open MeasureTheory Set
namespace P201.Wave

/-- Banach-valued AC fundamental theorem with a derivative integrable only
on the interval. Zero extension discharges the upstream global L¹-local condition. -/
theorem vector_ac_ftc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} {Z G : ℝ → E}
    (hZ : AbsolutelyContinuousOnInterval Z a b)
    (hG : IntervalIntegrable G volume a b)
    (hd : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt Z (G t) t) :
    (∫ s in a..b, G s) = Z b - Z a := by
  let G₀ : ℝ → E := (uIcc a b).indicator G
  have hGI : Integrable G₀ volume :=
    (integrable_indicator_iff measurableSet_uIcc).mpr ((intervalIntegrable_iff' (by finiteness)).mp hG)
  have hd₀ : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt Z (G₀ t) t := by
    filter_upwards [hd] with t ht hmem
    simpa only [G₀, indicator_of_mem hmem] using ht hmem
  have he := ExpandedFA.Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
    hZ hGI.locallyIntegrable hd₀
  rw [← he]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (indicator_of_mem ht G).symm

/-- Every pair of times has the exact primitive increment, in either order. -/
theorem vector_ac_increments {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} {Z G : ℝ → E}
    (hZ : AbsolutelyContinuousOnInterval Z a b)
    (hG : IntervalIntegrable G volume a b)
    (hd : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt Z (G t) t) :
    ∀ r ∈ uIcc a b, ∀ t ∈ uIcc a b, Z t - Z r = ∫ s in r..t, G s := by
  intro r hr t ht
  have hsub : uIcc r t ⊆ uIcc a b := uIcc_subset_uIcc hr ht
  apply (vector_ac_ftc (hZ.mono hsub) (hG.mono_set hsub) ?_).symm
  filter_upwards [hd] with s hs hst
  exact hs (hsub hst)


/-- An AC trajectory with an integrable a.e. derivative satisfies the actual
vector-valued time-distribution equation. -/
theorem vector_ac_derivativeValue {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T) {Z G : ℝ → E}
    (hZ : AbsolutelyContinuousOnInterval Z 0 T)
    (hG : IntegrableOn G (Ioo 0 T))
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt Z (G t) t) :
    ExpandedFA.Evolution.HilbertTripleSpec.derivativeValue T Z G := by
  have hZc : ContinuousOn Z (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using hZ.continuousOn
  have hZi : IntegrableOn Z (Ioo 0 T) :=
    (hZc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hGI : IntervalIntegrable G volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hG
  have hdU : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → HasDerivAt Z (G t) t := by
    simpa only [uIcc_of_le hT] using hd
  apply ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.GalerkinNet.derivativeValue_of_integral_increments
    T hT Z G hZi hG
  intro s t
  exact vector_ac_increments hZ hGI hdU s.val
    (by simpa only [uIcc_of_le hT] using s.property) t.val
    (by simpa only [uIcc_of_le hT] using t.property)
end P201.Wave

open Set MeasureTheory Filter
open scoped NNReal
namespace P201.Wave
open ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
open ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

/-- Strongly differentiable bounded observations of an L¹ primitive satisfy
the product rule as a genuine Banach-valued distribution derivative. -/
theorem observation_derivativeValue {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A D : ℝ → X →L[ℝ] E) (K : ℝ≥0)
    (hd : ∀ (x : X) (t : ℝ), HasDerivAt (fun s => A s x) (D t x) t)
    (hD : ∀ t : ℝ, ‖D t‖ ≤ K)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : X) (G : ℝ → X)
    (hG : IntegrableOn G (Ioo 0 T))
    (hJ : IntegrableOn (fun t => D t (x₀ + ∫ s in (0 : ℝ)..t, G s) + A t (G t))
      (Ioo 0 T)) :
    ExpandedFA.Evolution.HilbertTripleSpec.derivativeValue T
      (fun t => A t (x₀ + ∫ s in (0 : ℝ)..t, G s))
      (fun t => D t (x₀ + ∫ s in (0 : ℝ)..t, G s) + A t (G t)) := by
  let Y : ℝ → X := fun t => x₀ + ∫ s in (0 : ℝ)..t, G s
  have hGI : IntervalIntegrable G volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hG
  have hYinc : ∀ t ∈ Icc 0 T, Y t - Y 0 = ∫ s in (0 : ℝ)..t, G s := by
    intro t _
    simp [Y]
  have hYAc : AbsolutelyContinuousOnInterval Y 0 T :=
    FiniteEnergy.primitive_increment_ac hGI (by simpa only [uIcc_of_le hT] using hYinc)
  have hYAe := FiniteEnergy.primitive_increment_ae_deriv hT hGI hYinc
  have hAlip := lipschitzWith_of_strong_derivative A D K hd hD
  have hAAc : AbsolutelyContinuousOnInterval A 0 T :=
    hAlip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hZAc : AbsolutelyContinuousOnInterval (fun t => A t (Y t)) 0 T :=
    bilinear_absolutelyContinuousOnInterval
      ((ContinuousLinearMap.apply ℝ E : X →L[ℝ] (X →L[ℝ] E) →L[ℝ] E).flip) hAAc hYAc
  apply vector_ac_derivativeValue hT hZAc hJ
  filter_upwards [hYAe] with t ht hmem
  exact hasDerivAt_strong_apply A
    ((hAlip.continuous.comp continuous_fst).clm_apply continuous_snd)
    (hd (Y t) t) (ht hmem)
end P201.Wave

open MeasureTheory Set Filter
namespace P201.Wave

/-- A continuous derivative field and exact increments give the prescribed
within derivative at every point of the closed slab, including endpoints.
Continuity of x follows from the increments and is not needed as a premise. -/
theorem hasDerivWithinAt_of_continuous_increments {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 ≤ T) (x g : ℝ → E)
    (hg : ContinuousOn g (Icc 0 T))
    (hinc : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, x t - x s = ∫ r in s..t, g r) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt x (g t) (Icc 0 T) t := by
  let G : ℝ → E := fun s => g (projIcc 0 T hT s)
  have hGc : Continuous G := hg.domRestrict.comp continuous_projIcc
  have hG (s : ℝ) (hs : s ∈ Icc 0 T) : G s = g s := by
    simp only [G, projIcc_of_mem hT hs]
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have he (s : ℝ) (hs : s ∈ Icc 0 T) :
      x s = (∫ r in (0 : ℝ)..s, G r) + x 0 := by
    have hGs : (∫ r in (0 : ℝ)..s, G r) = ∫ r in (0 : ℝ)..s, g r := by
      apply intervalIntegral.integral_congr
      intro r hr
      apply hG
      exact uIcc_subset_Icc h0 hs hr
    rw [hGs]
    exact sub_eq_iff_eq_add.mp (hinc 0 h0 s hs)
  intro t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 t)
    hGc.stronglyMeasurable.stronglyMeasurableAtFilter hGc.continuousAt).add_const (x 0)
  rw [hG t ht] at hd
  exact hd.hasDerivWithinAt.congr he (he t ht)
end P201.Wave

open Set
open scoped InnerProductSpace ComplexConjugate
namespace P201.Wave
open ExpandedFA ExpandedFA.Unbounded
open ClosedNonnegativeForms Models.AbstractWaveEnergy

namespace PhaseObservation
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
  {F : WaveFamily (𝕜 := 𝕜) (H := H)}
  (M : EnergyHilbertModel F.S)

def graphPosition : M.Space →L[𝕜] GraphDomain F.S :=
  (ContinuousLinearMap.fst 𝕜 (GraphDomain F.S) H).comp
    M.coordinates.symm.toContinuousLinearMap

def positionMap : M.Space →L[𝕜] H := (position F.S).comp (graphPosition M)

def velocityMap : M.Space →L[𝕜] H :=
  (ContinuousLinearMap.snd 𝕜 (GraphDomain F.S) H).comp
    M.coordinates.symm.toContinuousLinearMap

variable [CompleteSpace H]
  (U : ℝ → M.Space ≃ₗᵢ[𝕜] M.Space)
  (hcoord : ∀ (x : GraphDomain F.S × H) t,
    position F.S (M.coordinates.symm (U t (M.coordinates x))).1 =
      F.displacement x.1 x.2 t ∧
    (M.coordinates.symm (U t (M.coordinates x))).2 = F.velocity x.1 x.2 t)

include hcoord in
/-- The coordinate group has the original energy-solution derivative interfaces. -/
theorem isEnergySolution (hsol : SolutionClaims F) (x : M.Space) :
    IsEnergySolution F.S (fun t => graphPosition M (U t x))
      (fun t => velocityMap M (U t x)) := by
  let p := M.coordinates.symm x
  obtain ⟨z, hpos, hz, _⟩ := hsol p.1 p.2
  have hco (t : ℝ) : position F.S (graphPosition M (U t x)) =
      F.displacement p.1 p.2 t ∧ velocityMap M (U t x) = F.velocity p.1 p.2 t := by
    change position F.S (M.coordinates.symm (U t x)).1 = F.displacement p.1 p.2 t ∧
      (M.coordinates.symm (U t x)).2 = F.velocity p.1 p.2 t
    simpa only [p, M.coordinates.apply_symm_apply] using hcoord p t
  have he (t : ℝ) : graphPosition M (U t x) = z t := by
    apply Subtype.ext
    change position F.S (graphPosition M (U t x)) = position F.S (z t)
    exact (hco t).1.trans (hpos t).symm
  have hu : (fun t => graphPosition M (U t x)) = z := funext he
  have hv : (fun t => velocityMap M (U t x)) = F.velocity p.1 p.2 :=
    funext (fun t => (hco t).2)
  rw [hu, hv]
  exact hz

include hcoord in
theorem position_derivative (hsol : SolutionClaims F) (x : M.Space) (t : ℝ) :
    HasDerivAt (fun s => positionMap M (U s x)) (velocityMap M (U t x)) t :=
  (isEnergySolution M U hcoord hsol x).derivative t

include hcoord in
theorem weak_velocity_derivative (hsol : SolutionClaims F)
    (w : GraphDomain F.S) (x : M.Space) (t : ℝ) :
    HasDerivAt (fun s => inner 𝕜 (position F.S w) (velocityMap M (U s x)))
      (-inner 𝕜 (Models.AbstractWaveEnergy.gradient F.S w)
        (Models.AbstractWaveEnergy.gradient F.S (graphPosition M (U t x)))) t :=
  weak_derivative_conjugate F.S
    (isEnergySolution M U hcoord hsol x).weak_derivative w t

variable {V : Type u}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  (d : FormData 𝕜 V H) (hr : d.RootClaims F)

def originalPosition : M.Space →L[𝕜] V :=
  (d.graphEquiv F hr).symm.toContinuousLinearMap.comp (graphPosition M)

def weakVelocityMap (w : V) : M.Space →L[𝕜] 𝕜 :=
  (innerSL 𝕜 (d.j w)).comp (velocityMap M)

def formMap (w : V) : M.Space →L[𝕜] 𝕜 :=
  -((d.a.flip w).comp (originalPosition M d hr))

variable [CompleteSpace V]
include hcoord in
theorem form_velocity_derivative (hW : WaveTheorem d.operator F)
    (w : V) (x : M.Space) (t : ℝ) :
    HasDerivAt (fun s => weakVelocityMap M d w (U s x))
      (formMap M d hr w (U t x)) t := by
  let e := d.graphEquiv F hr
  have he : e (originalPosition M d hr (U t x)) = graphPosition M (U t x) :=
    e.apply_symm_apply _
  have hf := d.graphEquiv_form F hr hW.1.1.1 hW.1.1.2.1
    (originalPosition M d hr (U t x)) w
  rw [he] at hf
  have hd := weak_velocity_derivative M U hcoord hW.2.1 (e w) x t
  change HasDerivAt (fun s => inner 𝕜 (d.j w) (velocityMap M (U s x)))
    (-inner 𝕜 (Models.AbstractWaveEnergy.gradient F.S (e w))
      (Models.AbstractWaveEnergy.gradient F.S (graphPosition M (U t x)))) t at hd
  rw [← hf] at hd
  exact hd

end PhaseObservation

/-- Composition with a unitary phase map retains the same operator norm bound. -/
theorem norm_observation_comp_unitary {𝕜 : Type*} [RCLike 𝕜]
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (R : X →L[𝕜] E) (U : X ≃ₗᵢ[𝕜] X) :
    ‖R.comp U.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro x
  change ‖R (U x)‖ ≤ ‖R‖ * ‖x‖
  simpa only [U.norm_map] using R.le_opNorm (U x)

end P201.Wave

open Set MeasureTheory Filter Topology
open scoped NNReal
namespace P201.Wave
open ExpandedFA ExpandedFA.Unbounded
open ClosedNonnegativeForms Models.AbstractWaveEnergy

namespace FormData
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (d : FormData 𝕜 V H)

theorem operator_positive_gap : ∃ c : ℝ, 0 < c ∧
    ∀ x : d.operator.domain, c * ‖(x : H)‖ ^ 2 ≤
      RCLike.re (inner 𝕜 (x : H) (d.operator x)) := by
  obtain ⟨c, hc, hb⟩ := d.coercive
  refine ⟨c / (‖d.j‖ ^ 2 + 1), by positivity, fun x => ?_⟩
  obtain ⟨v, hv, ha⟩ := (d.mem_graph (x : H) (d.operator x)).mp (d.operator.mem_graph x)
  have hvb := d.j.le_opNorm v
  have hvb2 : ‖(x : H)‖ ^ 2 ≤ (‖d.j‖ ^ 2 + 1) * ‖v‖ ^ 2 := by
    rw [← hv]
    nlinarith [norm_nonneg (d.j v), norm_nonneg d.j, norm_nonneg v, sq_nonneg ‖v‖]
  have he := ha v
  rw [hv] at he
  rw [← he]
  apply le_trans _ (hb v)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < ‖d.j‖ ^ 2 + 1 by positivity)).mpr
  calc
    c * ‖(x : H)‖ ^ 2 ≤ c * ((‖d.j‖ ^ 2 + 1) * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hvb2 hc.le
    _ = c * ‖v‖ ^ 2 * (‖d.j‖ ^ 2 + 1) := by ring

end FormData

namespace UnitaryDuhamel
variable {𝕜 : Type*} [RCLike 𝕜] {X : Type u}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (U : ℝ → X ≃ₗᵢ[𝕜] X)
  (hzero : ∀ x, U 0 x = x)
  (hadd : ∀ s t x, U (s + t) x = U s (U t x))
  (hcont : ∀ x, Continuous (fun t => U t x))

def semigroup : ExpandedFA.Semigroups.C0Semigroup 𝕜 X where
  operators := fun t => (U t).toContinuousLinearEquiv.toContinuousLinearMap
  at_zero := by ext x; exact hzero x
  add_time := by intro t s; ext x; exact hadd t s x
  strong_zero := by
    intro x
    change Tendsto (fun h : ℝ => U (h.toNNReal : ℝ) x) (𝓝[>] 0) (𝓝 x)
    have hc : Continuous (fun t : ℝ => U (t.toNNReal : ℝ) x) :=
      (hcont x).comp (continuous_subtype_val.comp continuous_real_toNNReal)
    simpa only [Real.toNNReal_zero, NNReal.coe_zero, hzero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

include hcont in
theorem continuous_action : Continuous (fun p : ℝ × X => U p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hc : Tendsto (fun q : ℝ × X => U q.1 p.2) (𝓝 p) (𝓝 (U p.1 p.2)) :=
    ((hcont p.2).comp continuous_fst).continuousAt
  apply hc.congr_dist
  have hd : (fun q : ℝ × X => dist (U q.1 p.2) (U q.1 q.2)) =
      fun q : ℝ × X => dist p.2 q.2 := by
    funext q
    exact (U q.1).dist_map _ _
  rw [hd]
  simpa only [dist_self] using ((continuous_const : Continuous (fun _ : ℝ × X => p.2)).dist continuous_snd).continuousAt.tendsto (x := p)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Distributional product rule specialized to a unitary group. -/
theorem observation (R Q : X →L[𝕜] E)
    (hd : ∀ x t, HasDerivAt (fun s => R (U s x)) (Q (U t x)) t)
    {T : ℝ} (hT : 0 ≤ T) (x : X) (G : ℝ → X)
    (hG : IntegrableOn G (Ioo 0 T))
    (hJ : IntegrableOn (fun t => Q (U t (x + ∫ s in (0 : ℝ)..t, G s)) + R (U t (G t))) (Ioo 0 T)) :
    Evolution.HilbertTripleSpec.derivativeValue T
      (fun t => R (U t (x + ∫ s in (0 : ℝ)..t, G s)))
      (fun t => Q (U t (x + ∫ s in (0 : ℝ)..t, G s)) + R (U t (G t))) := by
  let A : ℝ → X →L[ℝ] E := fun t =>
    (R.comp (U t).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  let D : ℝ → X →L[ℝ] E := fun t =>
    (Q.comp (U t).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hd' : ∀ x t, HasDerivAt (fun s => A s x) (D t x) t := hd
  have hD : ∀ t, ‖D t‖ ≤ ‖Q‖₊ := by
    intro t
    change ‖(Q.comp (U t).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ‖ ≤ ‖Q‖
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact norm_observation_comp_unitary Q (U t)
  exact observation_derivativeValue A D ‖Q‖₊ hd' hD hT x G hG hJ

end UnitaryDuhamel

namespace FormData
variable {𝕜 : Type*} [RCLike 𝕜] {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
  (d : FormData 𝕜 V H) (F : WaveFamily (𝕜 := 𝕜) (H := H))
  (hr : d.RootClaims F) (hW : WaveTheorem d.operator F)

include hr hW in
/-- Full L¹ forced wave evolution from the canonical spectral family. -/
theorem forced_of_spectral : d.ForcedClaims F := by
  intro T hT g h f hf
  obtain ⟨c, hc, hgap⟩ := d.operator_positive_gap
  obtain ⟨M, U, hzero, hadd, hcont, hcoord⟩ := hW.2.2.2.2 c hc hgap
  letI : NormedSpace ℝ M.Space := NormedSpace.restrictScalars ℝ 𝕜 M.Space
  letI : IsScalarTower ℝ 𝕜 M.Space := IsScalarTower.restrictScalars ℝ 𝕜 M.Space
  letI : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  letI : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  let e := d.graphEquiv F hr
  let S := UnitaryDuhamel.semigroup U hzero hadd hcont
  let B : H →L[𝕜] M.Space := M.coordinates.toContinuousLinearMap.comp
    ((0 : H →L[𝕜] GraphDomain F.S).prod (ContinuousLinearMap.id 𝕜 H))
  let x : M.Space := M.coordinates (e g, h)
  let y := Semigroups.InhomogeneousEvolutionSpec.solution S x (fun s => B (f s))
  have hfcc : IntegrableOn f (Icc 0 T) := (integrableOn_Icc_iff_integrableOn_Ioo).mpr hf
  have hB : IntegrableOn (fun s => B (f s)) (Icc 0 T) := B.integrable_comp hfcc
  let τ : ℝ≥0 := ⟨T, hT.le⟩
  have hBτ : IntegrableOn (fun s => B (f s)) (Icc 0 (τ : ℝ)) := hB
  have hY := Semigroups.InhomogeneousEvolution.solution_continuousOn S τ x hBτ
  let P : M.Space →L[𝕜] H := (position F.S).comp
    ((ContinuousLinearMap.fst 𝕜 (GraphDomain F.S) H).comp
      M.coordinates.symm.toContinuousLinearMap)
  let Q : M.Space →L[𝕜] H := (ContinuousLinearMap.snd 𝕜 (GraphDomain F.S) H).comp
      M.coordinates.symm.toContinuousLinearMap
  let u : ℝ → V := fun t => e.symm (M.coordinates.symm (y t)).1
  let vel : ℝ → H := fun t => Q (y t)
  have hju (t : ℝ) : d.j (u t) = P (y t) := by
    change d.j (e.symm _) = position F.S _
    rw [← d.graphEquiv_position F hr, e.apply_symm_apply]
    rfl
  have hK (t s : ℝ) (hs : 0 ≤ t - s) :
      P (S.operators (t - s).toNNReal (B (f s))) = F.quotient (t - s) (f s) := by
    change position F.S (M.coordinates.symm
      (U ((t - s).toNNReal : ℝ) (M.coordinates (0, f s)))).1 = _
    rw [Real.coe_toNNReal _ hs, (hcoord (0, f s) (t - s)).1]
    simp [WaveFamily.displacement]
  let G : ℝ → M.Space := fun s => U (-s) (B (f s))
  let Z : ℝ → M.Space := fun t => U t (x + ∫ s in (0 : ℝ)..t, G s)
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Ioo 0 T)) :=
    (UnitaryDuhamel.continuous_action U hcont).comp_aestronglyMeasurable
      (continuous_neg.aestronglyMeasurable.prodMk (B.integrable_comp hf).aestronglyMeasurable)
  have hG : IntegrableOn G (Ioo 0 T) := by
    apply ((B.integrable_comp hf).norm).mono' hGmeas
    exact Eventually.of_forall (fun s => le_of_eq ((U (-s)).norm_map (B (f s))))
  have hZ (t : ℝ) (ht : t ∈ Icc 0 T) : Z t = y t := by
    have hGI : IntervalIntegrable G volume 0 t := by
      have hGcc : IntegrableOn G (Icc 0 T) := (integrableOn_Icc_iff_integrableOn_Ioo).mpr hG
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
        (hGcc.mono_set (Icc_subset_Icc le_rfl ht.2))
    let L : M.Space →L[𝕜] M.Space := (U t).toContinuousLinearEquiv.toContinuousLinearMap
    change L (x + ∫ s in (0 : ℝ)..t, G s) = _
    rw [map_add, ← L.intervalIntegral_comp_comm hGI]
    change U t x + (∫ s in (0 : ℝ)..t, U t (U (-s) (B (f s)))) =
      S.operators t.toNNReal x + ∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal (B (f s))
    congr 1
    · change U t x = U (t.toNNReal : ℝ) x
      rw [Real.coe_toNNReal _ ht.1]
    · apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      change U t (U (-s) (B (f s))) = U ((t-s).toNNReal : ℝ) (B (f s))
      rw [← hadd, Real.coe_toNNReal _ (by linarith [hs.2])]
      rfl

  have henergy (t : ℝ) : ‖y t‖ ^ 2 / 2 = d.energy (u t) (vel t) := by
    let z := M.coordinates.symm (y t)
    have hz : e (u t) = z.1 := e.apply_symm_apply z.1
    have hi := M.inner_eq z z
    have hn := norm_sq_eq_re_inner (𝕜 := 𝕜) (y t)
    have hco : M.coordinates z = y t := M.coordinates.apply_symm_apply _
    rw [hco] at hi
    rw [hi] at hn
    change ‖y t‖ ^ 2 = RCLike.re
      (inner 𝕜 (Models.AbstractWaveEnergy.gradient F.S z.1)
        (Models.AbstractWaveEnergy.gradient F.S z.1) + inner 𝕜 z.2 z.2) at hn
    rw [map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← hz,
      d.graphEquiv_energy F hr (u t)] at hn
    change ‖y t‖ ^ 2 / 2 = (‖z.2‖ ^ 2 + RCLike.re (d.a (u t) (u t))) / 2
    linarith
  have hwork (s : ℝ) : inner 𝕜 (y s) (B (f s)) = inner 𝕜 (vel s) (f s) := by
    have hi := M.inner_eq (M.coordinates.symm (y s)) (0, f s)
    rw [M.coordinates.apply_symm_apply] at hi
    change inner 𝕜 (y s) (B (f s)) =
      inner 𝕜 (Models.AbstractWaveEnergy.gradient F.S (M.coordinates.symm (y s)).1)
        (Models.AbstractWaveEnergy.gradient F.S 0) +
      inner 𝕜 (M.coordinates.symm (y s)).2 (f s) at hi
    change inner 𝕜 (y s) (B (f s)) = inner 𝕜 (M.coordinates.symm (y s)).2 (f s)
    simpa only [map_zero, inner_zero_right, zero_add] using hi
  have huc : ContinuousOn u (Icc 0 T) := e.symm.continuous.comp_continuousOn
      (continuous_fst.comp_continuousOn (M.coordinates.symm.continuous.comp_continuousOn hY))
  have hvc : ContinuousOn vel (Icc 0 T) := Q.continuous.comp_continuousOn hY
  have hu0 : u 0 = g := by
    change e.symm (M.coordinates.symm (y 0)).1 = g
    have hy0 : y 0 = x := Semigroups.InhomogeneousEvolution.solution_zero S x _
    rw [hy0, M.coordinates.symm_apply_apply]
    exact e.symm_apply_apply g
  have hv0 : vel 0 = h := by
    change Q (y 0) = h
    rw [show y 0 = x from Semigroups.InhomogeneousEvolution.solution_zero S x _]
    change (M.coordinates.symm (M.coordinates (e g, h))).2 = h
    rw [M.coordinates.symm_apply_apply]
  have hUG (t : ℝ) : U t (G t) = B (f t) := by
    change U t (U (-t) (B (f t))) = _
    rw [← hadd, add_neg_cancel, hzero]
  have hPB (t : ℝ) : P (B (f t)) = 0 := by
    change position F.S (M.coordinates.symm (M.coordinates (0, f t))).1 = 0
    rw [M.coordinates.symm_apply_apply, map_zero]
  have hPJ (t : ℝ) (ht : t ∈ Icc 0 T) :
      Q (Z t) + P (U t (G t)) = vel t := by
    rw [hUG, hPB, add_zero, hZ t ht]
  have hPX (t : ℝ) (ht : t ∈ Icc 0 T) : P (Z t) = d.j (u t) := by
    rw [hZ t ht, hju]
  have hvi : IntegrableOn vel (Ioo 0 T) :=
    (hvc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hPJint : IntegrableOn (fun t => Q (Z t) + P (U t (G t))) (Ioo 0 T) :=
    hvi.congr_fun (fun t ht => (hPJ t (Ioo_subset_Icc_self ht)).symm) measurableSet_Ioo
  have hPd : ∀ x t, HasDerivAt (fun s => P (U s x)) (Q (U t x)) t :=
    PhaseObservation.position_derivative M U hcoord hW.2.1
  have hpobs := UnitaryDuhamel.observation U P Q hPd hT.le x G hG hPJint
  have hPXae : (fun t => P (Z t)) =ᵐ[Evolution.timeMeasure T] (fun t => d.j (u t)) := by
    change _ =ᵐ[volume.restrict (Ioo 0 T)] _
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hPX t (Ioo_subset_Icc_self ht)
  have hPJae : (fun t => Q (Z t) + P (U t (G t))) =ᵐ[Evolution.timeMeasure T] vel := by
    change _ =ᵐ[volume.restrict (Ioo 0 T)] _
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hPJ t (Ioo_subset_Icc_self ht)
  have hposder := (Evolution.hasTimeDerivative_congr T _ _ _ _ hPXae hPJae).mp hpobs
  have hposinc := continuous_derivative_increments hT _ _
    (d.j.continuous.comp_continuousOn huc) hvi hposder
  have hpointe := hasDerivWithinAt_of_continuous_increments hT.le _ _ hvc hposinc
  have hequation (w : V) : Evolution.HilbertTripleSpec.derivativeValue T
      (fun t => inner 𝕜 (d.j w) (vel t))
      (fun t => inner 𝕜 (d.j w) (f t) - d.a (u t) w) := by
    let R := PhaseObservation.weakVelocityMap M d w
    let D := PhaseObservation.formMap M d hr w
    have hDJ (t : ℝ) (ht : t ∈ Icc 0 T) :
        D (Z t) + R (U t (G t)) = inner 𝕜 (d.j w) (f t) - d.a (u t) w := by
      rw [hUG, hZ t ht]
      change -d.a (u t) w + inner 𝕜 (d.j w)
        (M.coordinates.symm (M.coordinates (0, f t))).2 = _
      rw [M.coordinates.symm_apply_apply]
      abel
    have hDX (t : ℝ) (ht : t ∈ Icc 0 T) :
        R (Z t) = inner 𝕜 (d.j w) (vel t) := by
      rw [hZ t ht]
      rfl
    have hsc : IntegrableOn (fun t => inner 𝕜 (d.j w) (f t) - d.a (u t) w) (Ioo 0 T) :=
      ((innerSL 𝕜 (d.j w)).integrable_comp hf).sub
        ((d.a.flip w).integrable_comp ((huc.integrableOn_compact isCompact_Icc).mono_set
          Ioo_subset_Icc_self))
    have hDJint : IntegrableOn (fun t => D (Z t) + R (U t (G t))) (Ioo 0 T) :=
      hsc.congr_fun (fun t ht => (hDJ t (Ioo_subset_Icc_self ht)).symm) measurableSet_Ioo
    have hDd : ∀ x t, HasDerivAt (fun s => R (U s x)) (D (U t x)) t :=
      PhaseObservation.form_velocity_derivative M U hcoord d hr hW w
    have hdobs := UnitaryDuhamel.observation U R D hDd hT.le x G hG hDJint
    apply (Evolution.hasTimeDerivative_congr T _ _ _ _ ?_ ?_).mp hdobs
    · change _ =ᵐ[volume.restrict (Ioo 0 T)] _
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hDX t (Ioo_subset_Icc_self ht)
    · change _ =ᵐ[volume.restrict (Ioo 0 T)] _
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hDJ t (Ioo_subset_Icc_self ht)
  have huv : d.IsSolution T g h f u vel :=
    ⟨huc, hvc, hpointe, hu0, hv0, hequation⟩
  refine ⟨u, vel, huv, ?_, d.acceleration_integrable hf huc,
    FormData.IsSolution.acceleration_derivative d huv hf, ?_, ?_⟩
  · intro z w hzw
    exact hzw.eqOn d hT huv
  · intro r hr' t ht
    have he := group_L1_energy U hzero hadd hT.le x (fun s => B (f s)) hG r hr' t ht
    change _ ∧ (‖Z t‖ ^ 2 - ‖Z r‖ ^ 2) / 2 =
      ∫ s in r..t, RCLike.re (inner 𝕜 (Z s) (B (f s))) at he
    rw [hZ t ht, hZ r hr'] at he
    have hIt : (∫ s in r..t, RCLike.re (inner 𝕜 (Z s) (B (f s)))) =
        ∫ s in r..t, RCLike.re (inner 𝕜 (vel s) (f s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc 0 T := (uIcc_subset_Icc hr' ht) hs
      dsimp only
      rw [hZ s hs', hwork s]
    rw [hIt] at he
    have he' := he.2
    rw [sub_div, henergy t, henergy r] at he'
    exact he'
  · intro t ht
    have hKI := Semigroups.InhomogeneousEvolution.kernel_intervalIntegrable S τ hBτ ht
    have hEq : (fun s => P (S.operators (t - s).toNNReal (B (f s)))) =ᶠ[
        ae (volume.restrict (Ioc 0 t))] (fun s => F.quotient (t - s) (f s)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hK t s (by linarith [hs.2])
    have hPI : IntervalIntegrable (fun s => P (S.operators (t - s).toNNReal (B (f s)))) volume 0 t :=
      ⟨P.integrable_comp hKI.1, P.integrable_comp hKI.2⟩
    have hIq : IntervalIntegrable (fun s => F.quotient (t - s) (f s)) volume 0 t := by
      apply hPI.congr_ae
      simpa only [uIoc_of_le ht.1] using hEq
    refine ⟨hIq, ?_⟩
    rw [hju]
    change P (S.operators t.toNNReal x + ∫ s in (0 : ℝ)..t,
      S.operators (t - s).toNNReal (B (f s))) = _
    rw [map_add, ← P.intervalIntegral_comp_comm hKI]
    have hfree : P (S.operators t.toNNReal x) = F.cosine t (d.j g) + F.quotient t h := by
      change position F.S (M.coordinates.symm
        (U (t.toNNReal : ℝ) (M.coordinates (e g, h)))).1 = _
      rw [Real.coe_toNNReal _ ht.1, (hcoord (e g, h) t).1]
      rfl
    rw [hfree]
    congr 1
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le ht.1]
    exact (ae_restrict_iff' measurableSet_Ioc).mp hEq

end FormData
end P201.Wave


namespace P201.Wave
open ExpandedFA.Models.AbstractWaveEnergy

/-- The full real finite-energy wave theorem, with arbitrary Bochner L¹ forcing. -/
theorem dirichlet_wave_real : DirichletWaveExpected.RealTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  obtain ⟨C, hC, hr, hW⟩ := real_spectral_bridge d
  exact ⟨C, hC, hr, d.forced_of_spectral (realFamily C) hr hW⟩

/-- The full complex theorem for every original Hermitian coercive form. -/
theorem dirichlet_wave_complex : DirichletWaveExpected.ComplexTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  obtain ⟨E, C, hC, hr, hW⟩ := complex_spectral_bridge d
  exact ⟨E, C, hC, hr, d.forced_of_spectral (complexFamily C) hr hW⟩

/-- Original real spatial statement on the actual full-H¹ zero-trace closure. -/
theorem real_dirichlet_wave : DirichletWaveExpected.RealDirichletTheorem :=
  real_dirichlet_of_abstract dirichlet_wave_real

/-- Original complex spatial statement, retaining every Hermitian coercive form. -/
theorem complex_dirichlet_wave : DirichletWaveExpected.ComplexDirichletTheorem :=
  complex_dirichlet_of_abstract dirichlet_wave_complex

/-- E10's canonical elliptic realization, with homogeneous physical boundary trace. -/
theorem elliptic_dirichlet_wave : DirichletWaveExpected.EllipticTheorem :=
  elliptic_of_abstract dirichlet_wave_real

end P201.Wave
