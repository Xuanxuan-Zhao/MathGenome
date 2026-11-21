import MathGenome.Internal.LinearPDE.P201Specs.Heat.FormDomain
import MathGenome.Internal.LinearPDE.P201.Heat.FormOperator
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
import Mathlib.Analysis.Normed.Operator.Extend

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexConjugate NNReal
universe u v
namespace P201.Heat
open ExpandedFA ExpandedFA.Unbounded
open ClosedNonnegativeForms

namespace FormDomain
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (q : NonnegativeForm 𝕜 H)

/-- The shifted Riesz map takes values in the original operator domain. -/
theorem adjoint_inclusion_domain (hc : q.IsClosed) (f : H) :
    q.inclusion (by let : CompleteSpace q.EnergySpace := hc; exact q.inclusion.adjoint f)
      ∈ q.associatedOperator.domain := by
  let : CompleteSpace q.EnergySpace := hc
  let x := q.inclusion.adjoint f
  apply LinearPMap.mem_domain_iff.mpr
  refine ⟨f - q.inclusion x, (q.associated _ _).mpr ⟨(q.toDomain x).property, ?_⟩⟩
  intro w
  have hh := q.inclusion.adjoint_inner_right (show q.EnergySpace from w) f
  rw [q.energy_inner] at hh
  change q.form w (q.toDomain x) = inner 𝕜 (w : H) (f - q.inclusion x)
  rw [inner_sub_right]
  exact eq_sub_iff_add_eq.mpr hh

/-- The operator domain inside the form Hilbert space. -/
def operatorCore : Submodule 𝕜 q.EnergySpace :=
  q.associatedOperator.domain.comap q.inclusion.toLinearMap

/-- The operator domain is dense for the full energy norm, without compactness. -/
theorem operatorCore_dense (hc : q.IsClosed) : Dense ((operatorCore q) : Set q.EnergySpace) := by
  let : CompleteSpace q.EnergySpace := hc
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro x hx
  have hf (f : H) : inner 𝕜 (q.inclusion.adjoint f) x = 0 :=
    hx _ ((adjoint_inclusion_domain q) hc f)
  have hz : q.inclusion x = 0 := by
    apply ext_inner_left 𝕜
    intro f
    rw [inner_zero_right, ← q.inclusion.adjoint_inner_left x f]
    exact hf f
  exact Subtype.ext hz


variable (S : Operator 𝕜 H H)
  (hsq : OperatorDomainsSpec.productValue S S = q.associatedOperator)

include hsq

/-- The square identity includes membership in both successive domains. -/
theorem core_root_mem (x : (operatorCore q)) : q.inclusion x ∈ S.domain := by
  have hx : q.inclusion x ∈ q.associatedOperator.domain := x.property
  rw [← hsq] at hx
  exact (mem_product_domain_iff S S _).mp hx |>.1

def coreToRoot : (operatorCore q) →ₗ[𝕜] S.domain :=
  (q.inclusion.toLinearMap.comp (operatorCore q).subtype).codRestrict
    S.domain ((core_root_mem q) S hsq)

def rootOnCore : (operatorCore q) →ₗ[𝕜] H := S.toFun.comp ((coreToRoot q) S hsq)

theorem core_square_eval (x : (operatorCore q)) :
    ∃ hy : S ((coreToRoot q) S hsq x) ∈ S.domain,
      S ⟨S ((coreToRoot q) S hsq x), hy⟩ =
        q.associatedOperator ⟨q.inclusion x, x.property⟩ := by
  have hx : q.inclusion x ∈ q.associatedOperator.domain := x.property
  rw [← hsq] at hx
  have hy := (mem_product_domain_iff S S _).mp hx |>.2
  refine ⟨hy, ?_⟩
  rw [← product_apply S S ((coreToRoot q) S hsq x) hy]
  exact (LinearPMap.ext_iff.mp hsq).2 (hg := x.property)

theorem rootOnCore_norm (hS : S.IsFormalAdjoint S) (x : (operatorCore q)) :
    ‖(rootOnCore q) S hsq x‖ ^ 2 =
      RCLike.re (q.form (q.toDomain x) (q.toDomain x)) := by
  obtain ⟨hy, he⟩ := (core_square_eval q) S hsq x
  obtain ⟨hx, ha⟩ := (q.associated _ _).mp
    (q.associatedOperator.mem_graph ⟨q.inclusion x, x.property⟩)
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜)]
  change RCLike.re (inner 𝕜 (S ((coreToRoot q) S hsq x))
    (S ((coreToRoot q) S hsq x))) = _
  rw [hS ((coreToRoot q) S hsq x) ⟨S ((coreToRoot q) S hsq x), hy⟩, he]
  exact congrArg RCLike.re (ha (q.toDomain x)).symm

theorem rootOnCore_bound (hS : S.IsFormalAdjoint S) (x : (operatorCore q)) :
    ‖(rootOnCore q) S hsq x‖ ≤ 1 * ‖(x : q.EnergySpace)‖ := by
  have he := q.energy_norm x
  have hr := (rootOnCore_norm q) S hsq hS x
  nlinarith [norm_nonneg ((rootOnCore q) S hsq x), norm_nonneg (x : q.EnergySpace),
    sq_nonneg ‖q.inclusion x‖]


def rootExtension : q.EnergySpace →L[𝕜] H :=
  (rootOnCore q S hsq).extendOfNorm (operatorCore q).subtype

theorem rootExtension_core (hc : q.IsClosed) (hS : S.IsFormalAdjoint S)
    (x : operatorCore q) : rootExtension q S hsq x = rootOnCore q S hsq x := by
  apply LinearMap.extendOfNorm_eq
  · simpa [DenseRange] using operatorCore_dense q hc
  · exact ⟨1, rootOnCore_bound q S hsq hS⟩

theorem rootExtension_graph (hc : q.IsClosed) (hS : S.IsFormalAdjoint S)
    (hclosed : S.IsClosed) (x : q.EnergySpace) :
    (q.inclusion x, rootExtension q S hsq x) ∈ S.graph := by
  apply (operatorCore_dense q hc).induction
    (P := fun x => (q.inclusion x, rootExtension q S hsq x) ∈ S.graph) ?_ ?_ x
  · intro y hy
    rw [rootExtension_core q S hsq hc hS ⟨y, hy⟩]
    exact S.mem_graph (coreToRoot q S hsq ⟨y, hy⟩)
  · exact hclosed.preimage (q.inclusion.continuous.prodMk (rootExtension q S hsq).continuous)

theorem rootExtension_energy (hc : q.IsClosed) (hS : S.IsFormalAdjoint S)
    (x : q.EnergySpace) :
    ‖rootExtension q S hsq x‖ ^ 2 + ‖q.inclusion x‖ ^ 2 = ‖x‖ ^ 2 := by
  apply (operatorCore_dense q hc).induction
    (P := fun x => ‖rootExtension q S hsq x‖ ^ 2 + ‖q.inclusion x‖ ^ 2 = ‖x‖ ^ 2) ?_ ?_ x
  · intro y hy
    rw [rootExtension_core q S hsq hc hS ⟨y, hy⟩]
    have hr := rootOnCore_norm q S hsq hS ⟨y, hy⟩
    have he := q.energy_norm y
    change ‖y‖ ^ 2 = _ + ‖q.inclusion y‖ ^ 2 at he
    simpa only [hr] using he.symm
  · exact isClosed_eq (by fun_prop) (by fun_prop)

omit hsq in
theorem energy_inner_operator_left (u : operatorCore q) (v : q.EnergySpace) :
    inner 𝕜 (u : q.EnergySpace) v =
      inner 𝕜 (q.associatedOperator ⟨q.inclusion u, u.property⟩ + q.inclusion u)
        (q.inclusion v) := by
  obtain ⟨hx, ha⟩ := (q.associated _ _).mp
    (q.associatedOperator.mem_graph ⟨q.inclusion u, u.property⟩)
  have hf := ha (q.toDomain v)
  change q.form (q.toDomain v) (q.toDomain u) = _ at hf
  rw [q.energy_inner, inner_add_left,
    ← q.hermitian (q.toDomain u) (q.toDomain v), hf, inner_conj_symm]
  rfl

/-- Closedness gives one inclusion; Riesz representation and surjectivity of
I+B give the other. This proof works equally over the reals and complexes. -/
theorem root_identification (hc : q.IsClosed) (hd : Dense (S.domain : Set H))
    (hsa : S.adjoint = S) :
    S.domain = q.domain ∧
    ∀ (x : q.domain) (hx : (x : H) ∈ S.domain),
      RCLike.re (q.form x x) = ‖S ⟨x, hx⟩‖ ^ 2 := by
  let : CompleteSpace q.EnergySpace := hc
  have hS : S.IsFormalAdjoint S := by
    have h := LinearPMap.adjoint_isFormalAdjoint hd
    rwa [hsa] at h
  have hclosed : S.IsClosed := by
    rw [← hsa]
    exact LinearPMap.adjoint_isClosed hd
  let T := rootExtension q S hsq
  have hgraph := rootExtension_graph q S hsq hc hS hclosed
  have hle : q.domain ≤ S.domain := by
    intro x hx
    exact LinearPMap.mem_domain_iff.mpr ⟨T (show q.EnergySpace from ⟨x, hx⟩),
      hgraph (show q.EnergySpace from ⟨x, hx⟩)⟩
  have hrev : S.domain ≤ q.domain := by
    intro x hx
    let y : q.EnergySpace := q.inclusion.adjoint x + T.adjoint (S ⟨x, hx⟩)
    have hy (u : operatorCore q) :
        inner 𝕜 (q.associatedOperator ⟨q.inclusion u, u.property⟩ + q.inclusion u)
          (q.inclusion y) =
        inner 𝕜 (q.associatedOperator ⟨q.inclusion u, u.property⟩ + q.inclusion u) x := by
      rw [← energy_inner_operator_left q u y]
      change inner 𝕜 (u : q.EnergySpace)
        (q.inclusion.adjoint x + T.adjoint (S ⟨x, hx⟩)) = _
      rw [inner_add_right, q.inclusion.adjoint_inner_right, T.adjoint_inner_right]
      have ht : T u = rootOnCore q S hsq u := rootExtension_core q S hsq hc hS u
      obtain ⟨hu, he⟩ := core_square_eval q S hsq u
      rw [ht]
      change inner 𝕜 (q.inclusion u) x +
        inner 𝕜 (S (coreToRoot q S hsq u)) (S ⟨x, hx⟩) = _
      rw [← hS ⟨S (coreToRoot q S hsq u), hu⟩ ⟨x, hx⟩, he, inner_add_left]
      exact add_comm _ _
    have he : q.inclusion y = x := by
      apply ext_inner_left 𝕜
      intro f
      obtain ⟨z, hz⟩ := q.shifted_surjective hc f
      obtain ⟨hzdom, _⟩ := (q.associated _ _).mp (q.associatedOperator.mem_graph z)
      let u : operatorCore q := ⟨(show q.EnergySpace from ⟨(z : H), hzdom⟩), z.property⟩
      exact hz ▸ hy u
    exact he ▸ (q.toDomain y).property
  refine ⟨le_antisymm hrev hle, ?_⟩
  intro x hx
  let z : q.EnergySpace := x
  have hg := hgraph z
  have hv : S ⟨(x : H), hx⟩ = T z := by
    obtain ⟨w, hw, hv⟩ := S.mem_graph_iff.mp hg
    have hw' : w = ⟨(x : H), hx⟩ := Subtype.ext hw
    simpa only [hw'] using hv
  have he := rootExtension_energy q S hsq hc hS z
  have hn := q.energy_norm z
  rw [hv]
  change ‖T z‖ ^ 2 + ‖q.inclusion z‖ ^ 2 = ‖z‖ ^ 2 at he
  change ‖z‖ ^ 2 = RCLike.re (q.form x x) + ‖q.inclusion z‖ ^ 2 at hn
  linarith

end FormDomain

theorem form_domain_root_identification : FormDomainExpected.RootIdentification.{u, v} := by
  intro 𝕜 H _ _ _ _ q hc S hd hs hsq
  exact FormDomain.root_identification q S hsq hc hd hs


/-- Real spectral calculus and the full form-domain theorem for the canonical B. -/
theorem form_domain_real : FormDomainExpected.RealTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  have hrep := d.representation
  refine ⟨hrep, ?_⟩
  obtain ⟨C, hC⟩ := RealNonnegativeSpectralCalculus.spectral_existence H d.operator
    ⟨hrep.1, hrep.2.1.symm, hrep.2.2.1⟩
  have heq : d.operator = d.energyForm.associatedOperator :=
    d.denseForm.toNonnegative_operator _ _
  have hs := RealNonnegativeSpectralCalculus.squareRoot_square C
  rw [hC, heq] at hs
  obtain ⟨hdom, hnorm⟩ := FormDomain.root_identification d.energyForm
    (RealNonnegativeSpectralCalculus.squareRoot C) hs d.energy_closed
    (C.dense _ RealNonnegativeSpectralCalculus.continuous_root.measurable)
    (C.selfAdjoint _ RealNonnegativeSpectralCalculus.continuous_root.measurable)
  refine ⟨C, hC, hdom, ?_⟩
  intro v hv
  simpa only [CoerciveForm.energyForm, P201.Elliptic.DenseForm.toNonnegative,
    LinearMap.flip_apply, d.energy_form, RCLike.re_to_real, d.rangeEquiv_coe] using hnorm (d.rangeEquiv v) hv


namespace FormDomain
open FormDomainExpected MeasurableSpectralCalculus

/-- Exact square, including the domain, for the nonnegative complex symbol. -/
theorem complexRoot_square {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H} (C : BoundedRealization E) :
    OperatorDomainsSpec.productValue (measurableIntegral C complexRoot)
      (measurableIntegral C complexRoot) = measurableIntegral C complexCoordinate := by
  have hr : Measurable complexRoot := by unfold complexRoot; fun_prop
  have ht : Measurable complexCoordinate := by unfold complexCoordinate; fun_prop
  have hmul : complexRoot * complexRoot = complexCoordinate := by
    funext s
    change (Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (s : ℝ) : ℂ) = ((s : ℝ) : ℂ)
    rw [← Complex.ofReal_mul, ← pow_two]
    exact congrArg Complex.ofReal (Real.sq_sqrt s.2)
  have hdom : (measurableIntegral C complexCoordinate).domain ≤
      (measurableIntegral C complexRoot).domain := by
    apply RealNonnegativeSpectralCalculus.ComplexCalculus.domain_growth C hr ht
    refine ⟨1, 1, zero_le_one, zero_le_one, fun s => ?_⟩
    simp only [complexRoot, complexCoordinate, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, one_mul]
    have hs := Real.sq_sqrt (show 0 ≤ (s : ℝ) from s.2)
    nlinarith [sq_nonneg ((s : ℝ) - 1 / 2)]
  obtain ⟨hd, hl⟩ := SpectralProductAndSumDomains.product_rule C _ _ hr hr
  rw [hmul, inf_eq_right.mpr hdom] at hd
  rw [hmul] at hl
  exact LinearPMap.eq_of_le_of_domain_eq hl hd

end FormDomain

/-- The complex spectral square root has exactly the closed form domain. -/
theorem form_domain_complex_closed : FormDomainExpected.ComplexClosedTheorem.{v} := by
  intro H _ _ _ q hc
  have hd := q.associated_dense hc
  have hs := (q.associated_selfAdjoint hc).symm
  have hcl : q.associatedOperator.IsClosed := by
    rw [← hs]
    exact LinearPMap.adjoint_isClosed hd
  obtain ⟨E, hE⟩ := (UnboundedNormalSpectralTheorem.selfadjoint_spectral H
    q.associatedOperator hd hcl hs).1
  obtain ⟨C, hC, _⟩ := RealNonnegativeSpectralCalculus.SupportWork.realResolves_nonnegative_rebase
    q.associatedOperator E hE q.associated_nonnegative
  refine ⟨_, C, hC, ?_⟩
  apply FormDomain.root_identification q _ (by
    rw [FormDomain.complexRoot_square]
    exact hC) hc
  · apply MeasurableSpectralCalculus.measurableIntegral_dense
    unfold FormDomainExpected.complexRoot
    fun_prop
  · apply MeasurableSpectralCalculus.measurableIntegral_selfAdjoint
    · unfold FormDomainExpected.complexRoot
      fun_prop
    · intro s
      rfl


namespace FormDomain
open MeasureTheory P201Specs

/-- The shared full-H¹ model has an injective zero-order coordinate. -/
theorem dirichlet_injective {n : ℕ} (Ω : P201Specs.Domain n) :
    Function.Injective (P201Specs.hZeroUnderlying (𝕜 := ℂ) Ω) := by
  intro u v h
  apply Subtype.ext
  exact P201.hilbertUnderlyingInjective Ω 1 h

/-- Smooth tests belong to the actual full-H¹ closure used in C00. -/
theorem test_in_dirichlet {n : ℕ} (Ω : P201Specs.Domain n)
    (φ : P102.U4.TestSpace ℂ Ω) :
    ∃ v : P201Specs.H10 ℂ Ω,
      P201Specs.hZeroUnderlying Ω v = P102.U4.testToDomainLp Ω 2 φ := by
  obtain ⟨u, hu⟩ := P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ
  let v := (P201Specs.hToW ℂ Ω 1).symm u
  have hv : v ∈ P201Specs.hZeroSubmodule ℂ Ω := by
    apply Submodule.le_topologicalClosure _
    change ∃ ψ, P102.U4.testToDomainLp Ω 2 ψ =
      P102.U4.sobolevUnderlying ((P201Specs.hToW ℂ Ω 1) v)
    exact ⟨φ, by simpa [v] using hu.symm⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  change P102.U4.sobolevUnderlying ((P201Specs.hToW ℂ Ω 1) v) = _
  simpa [v] using hu

/-- Density holds on every open set; no boundary regularity is required. -/
theorem dirichlet_dense {n : ℕ} (Ω : P201Specs.Domain n) :
    DenseRange (P201Specs.hZeroUnderlying (𝕜 := ℂ) Ω) := by
  change Dense (LinearMap.range (P201Specs.hZeroUnderlying (𝕜 := ℂ) Ω).toLinearMap :
    Set (P201Specs.Lp ℂ Ω 2))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro f hf
  have hz : star f = 0 := by
    apply P102.U4.regularLp_injective Ω 2
    ext φ
    obtain ⟨v, hv⟩ := test_in_dirichlet Ω φ
    have hi : inner ℂ f (P102.U4.testToDomainLp Ω 2 φ) = 0 := by
      rw [← hv]
      exact inner_eq_zero_symm.mp (hf _ ⟨v, rfl⟩)
    rw [P102.U4.regularLp_pairing, P102.U4.regularLp_pairing, map_zero]
    rw [P102.U4.lpTestPairing_eq_integral]
    rw [L2.inner_def] at hi
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star f, P102.U4.testToDomainLp_ae Ω 2 φ] with x hx hφ
    simp only [hx, hφ, RCLike.inner_apply, RCLike.star_def, Pi.star_apply]
    exact mul_comm _ _
  change f = 0
  apply Lp.ext
  filter_upwards [Lp.coeFn_star f, Lp.ext_iff.mp hz,
    Lp.coeFn_zero ℂ 2 (P201Specs.domainMeasure Ω)] with x hx he h0
  rw [h0]
  exact star_eq_zero.mp (hx.symm.trans (he.trans h0))

end FormDomain

/-- Bounded Hermitian coercive forms on a complex Hilbert embedding. The
convention is linear in the first slot, as in the manuscript. -/
structure HermitianEmbedding (V : Type u) (H : Type v)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  j : V →L[ℂ] H
  injective : Function.Injective j
  dense : DenseRange j
  a : V →L[ℂ] V →L⋆[ℂ] ℂ
  hermitian : ∀ x y, conj (a x y) = a y x
  coercive : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ (a x x).re

namespace HermitianEmbedding
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (d : HermitianEmbedding V H)

def rangeEquiv : V ≃ₗ[ℂ] LinearMap.range d.j.toLinearMap :=
  LinearEquiv.ofInjective d.j.toLinearMap d.injective

def denseForm : P201.Elliptic.DenseForm ℂ H where
  domain := LinearMap.range d.j.toLinearMap
  dense := d.dense
  form :=
    { toFun := fun x =>
        { toFun := fun y => d.a (d.rangeEquiv.symm x) (d.rangeEquiv.symm y)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

theorem denseForm_hermitian : d.denseForm.IsHermitian := by
  intro x y
  exact d.hermitian _ _

theorem denseForm_nonnegative : d.denseForm.IsNonnegative := by
  intro x
  obtain ⟨c, hc, hb⟩ := d.coercive
  exact le_trans (mul_nonneg hc.le (sq_nonneg _)) (hb _)

def energyForm := d.denseForm.toNonnegative d.denseForm_hermitian d.denseForm_nonnegative

def toEnergy : V ≃ₗ[ℂ] d.energyForm.EnergySpace := d.rangeEquiv

@[simp] theorem rangeEquiv_coe (x : V) : (d.rangeEquiv x : H) = d.j x := rfl

@[simp] theorem toEnergy_inclusion (x : V) :
    d.energyForm.inclusion (d.toEnergy x) = d.j x := rfl

@[simp] theorem energy_form (x y : V) :
    d.denseForm.form (d.rangeEquiv x) (d.rangeEquiv y) = d.a x y := by
  change d.a (d.rangeEquiv.symm (d.rangeEquiv x))
    (d.rangeEquiv.symm (d.rangeEquiv y)) = _
  simp only [LinearEquiv.symm_apply_apply]

theorem energy_norm (x : V) :
    ‖d.toEnergy x‖ ^ 2 = (d.a x x).re + ‖d.j x‖ ^ 2 := by
  have h := d.energyForm.energy_norm (d.toEnergy x)
  change ‖d.toEnergy x‖ ^ 2 =
    (d.denseForm.form (d.rangeEquiv x) (d.rangeEquiv x)).re + ‖d.j x‖ ^ 2 at h
  simpa only [d.energy_form] using h

/-- The original norm and full energy norm are equivalent by boundedness and
coercivity. This is a conclusion, not a completeness certificate in the data. -/
theorem energy_bounds :
    (∃ C : ℝ, ∀ x, ‖d.toEnergy x‖ ≤ C * ‖x‖) ∧
    (∃ C : ℝ, ∀ y, ‖d.toEnergy.symm y‖ ≤ C * ‖y‖) := by
  constructor
  · refine ⟨Real.sqrt (‖d.a‖ + ‖d.j‖ ^ 2), fun x => ?_⟩
    have ha : (d.a x x).re ≤ ‖d.a‖ * ‖x‖ * ‖x‖ :=
      (Complex.re_le_norm _).trans ((d.a x).le_opNorm x |>.trans
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

theorem energy_closed [CompleteSpace V] : d.energyForm.IsClosed := by
  obtain ⟨⟨C, hC⟩, ⟨D, hD⟩⟩ := d.energy_bounds
  let e := d.toEnergy.toContinuousLinearEquivOfBounds C D hC hD
  let f : V ≃ᵤ d.energyForm.EnergySpace :=
    ⟨e.toEquiv, e.toContinuousLinearMap.uniformContinuous,
      e.symm.toContinuousLinearMap.uniformContinuous⟩
  exact f.completeSpace_iff.mp inferInstance

/-- Both directions of the representation relation in the original form space. -/
theorem mem_graph (x h : H) :
    (x, h) ∈ d.denseForm.associatedOperator.graph ↔
      ∃ v : V, d.j v = x ∧ ∀ w : V, d.a v w = inner ℂ (d.j w) h := by
  rw [d.denseForm.mem_associated_graph]
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

end HermitianEmbedding

/-- Arbitrary Hermitian coercive forms on the shared complex H¹₀ model have
exactly that square-root domain, with equality of the complex energy value.
The proof works on every open set, including the source's bounded Lipschitz case. -/
theorem form_domain_complex_dirichlet : FormDomainExpected.ComplexDirichletTheorem := by
  intro n Ω a hs hc
  let d : HermitianEmbedding (P201Specs.H10 ℂ Ω) (P201Specs.Lp ℂ Ω 2) :=
    { j := P201Specs.hZeroUnderlying Ω
      injective := FormDomain.dirichlet_injective Ω
      dense := FormDomain.dirichlet_dense Ω
      a := a
      hermitian := hs
      coercive := hc }
  have hA : d.denseForm.associatedOperator = d.energyForm.associatedOperator :=
    d.denseForm.toNonnegative_operator _ _
  obtain ⟨E, C, hC, hdom, hnorm⟩ := form_domain_complex_closed d.energyForm d.energy_closed
  refine ⟨d.denseForm, d.mem_graph, ?_, ?_, ?_, E, C, hC.trans hA.symm, hdom, ?_⟩
  · rw [hA]
    exact d.energyForm.associated_dense d.energy_closed
  · rw [hA]
    exact (d.energyForm.associated_selfAdjoint d.energy_closed).symm
  · rw [hA]
    exact d.energyForm.associated_nonnegative
  · intro v hv
    have hn := hnorm (d.rangeEquiv v) hv
    have hr : ((a v v).re : ℂ) = a v v := RCLike.conj_eq_iff_re.mp (hs v v)
    have he : (a v v).re =
        ‖MeasurableSpectralCalculus.measurableIntegral C FormDomainExpected.complexRoot
          ⟨P201Specs.hZeroUnderlying Ω v, hv⟩‖ ^ 2 := by
      simpa only [HermitianEmbedding.energyForm, P201.Elliptic.DenseForm.toNonnegative,
        LinearMap.flip_apply, d.energy_form, d.rangeEquiv_coe] using hn
    rw [← hr, he]

end P201.Heat
