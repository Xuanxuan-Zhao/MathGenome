import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set
open scoped ENNReal InnerProductSpace
namespace VariationalNotes.Sobolev

variable {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)

/-- The coordinates of a vector-valued Lp representative, almost everywhere. -/
theorem coordinateLp_ae {ι : Type*} [Fintype ι] (i : ι)
    (u : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)) :
    coordinateLp Ω p i u =ᵐ[domainMeasure Ω] fun x => u x i := by
  simpa only [coordinateLp, PiLp.proj_apply] using
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).coeFn_compLpL
      (p := p.ennreal) (μ := domainMeasure Ω) u

/-- Finite coordinate projections jointly determine an Lp class. -/
theorem coordinateLp_ext {ι : Type*} [Fintype ι]
    {u v : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)}
    (h : ∀ i, coordinateLp Ω p i u = coordinateLp Ω p i v) : u = v := by
  apply Lp.ext
  have hu := (Filter.eventually_all).mpr (fun i => coordinateLp_ae Ω p i u)
  have hv := (Filter.eventually_all).mpr (fun i => coordinateLp_ae Ω p i v)
  filter_upwards [hu, hv] with x hx hy
  apply PiLp.ext
  intro i
  exact (hx i).symm.trans ((congrArg (fun f : P102.U4.DomainLp ℝ Ω p.ennreal => f x)
    (h i)).trans (hy i))

/-- Assemble a finite family of scalar Lp classes by the Euclidean basis. -/
def assembleLp {ι : Type*} [Fintype ι] :
    (ι → P102.U4.DomainLp ℝ Ω p.ennreal) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω) := by
  classical
  exact ∑ i : ι, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single i (1 : ℝ))).compLpL p.ennreal (domainMeasure Ω)).comp
      (ContinuousLinearMap.proj i)

/-- Exact coordinate recovery, independent of representatives. -/
theorem coordinate_assemble {ι : Type*} [Fintype ι] (i : ι)
    (u : ι → P102.U4.DomainLp ℝ Ω p.ennreal) :
    coordinateLp Ω p i (assembleLp Ω p u) = u i := by
  classical
  simp only [assembleLp, ContinuousLinearMap.sum_apply, map_sum,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · apply Lp.ext
    filter_upwards [coordinateLp_ae Ω p i
      ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).compLpL
        p.ennreal (domainMeasure Ω) (u i)),
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).coeFn_compLpL
        (u i)] with x hx hy
    simp [hx, hy]
  · intro j _ hj
    apply Lp.ext
    filter_upwards [coordinateLp_ae Ω p i
      ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).compLpL
        p.ennreal (domainMeasure Ω) (u j)),
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).coeFn_compLpL
        (u j), Lp.coeFn_zero ℝ p.ennreal (domainMeasure Ω)] with x hx hy hz
    rw [hx, hy]
    simpa [Ne.symm hj] using hz.symm
  · simp

/-- Euclidean-valued Lp and its finite scalar coordinate product have the same topology. -/
def coordinateLpEquiv {ι : Type*} [Fintype ι] :
    Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω) ≃L[ℝ]
      (ι → P102.U4.DomainLp ℝ Ω p.ennreal) where
  toLinearEquiv :=
    { toFun := fun u i => coordinateLp Ω p i u
      invFun := assembleLp Ω p
      map_add' := by intro u v; funext i; exact (coordinateLp Ω p i).map_add u v
      map_smul' := by intro c u; funext i; exact (coordinateLp Ω p i).map_smul c u
      left_inv := fun u => coordinateLp_ext Ω p fun i => coordinate_assemble Ω p i _
      right_inv := fun u => funext fun i => coordinate_assemble Ω p i u }
  continuous_toFun := continuous_pi fun i => (coordinateLp Ω p i).continuous
  continuous_invFun := (assembleLp Ω p).continuous

/-- The graph equations as the usual scalar distribution equations. -/
theorem mem_weakDerivativeGraph_iff (z : GraphAmbient Ω m p) :
    z ∈ weakDerivativeGraph Ω m p ↔
      ∀ (i : Fin m) (j : Fin d),
        P102.U4.distributionPartial {j}
          (P102.U4.regularDistribution Ω (coordinateLp Ω p i (graphValue Ω m p z))) =
        P102.U4.regularDistribution Ω (coordinateLp Ω p (i,j) (graphGradient Ω m p z)) := by
  simp only [weakDerivativeGraph, Submodule.mem_iInf, LinearMap.mem_ker,
    derivativeEquation, ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, add_eq_zero_iff_eq_neg]
  constructor
  · intro h i j
    apply (P102.U4.distributionPartial_eq_regularLp_iff Ω p.ennreal _ _ _).mpr
    simpa using h i j
  · intro h i j
    have hi := (P102.U4.distributionPartial_eq_regularLp_iff Ω p.ennreal _ _ _).mp (h i j)
    simpa using hi

/-- The full norm has precisely the prescribed Euclidean p-sum formula. -/
theorem norm_eq (u : W1p Ω m p) :
    ‖u‖ = (‖value Ω m p u‖ ^ p.real + ‖gradient Ω m p u‖ ^ p.real) ^ (1 / p.real) := by
  change ‖u.val‖ = _
  have h := WithLp.prod_norm_eq_add (by simpa using p.pos) u.val
  simpa only [Exponent.toReal, value, gradient, graphValue, graphGradient,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, WithLp.fstL_apply,
    WithLp.sndL_apply] using h

/-- No extra gradient choices are present in a Sobolev equivalence class. -/
theorem value_injective : Function.Injective (value Ω m p) := by
  intro u v huv
  have hu := (mem_weakDerivativeGraph_iff Ω p u.val).mp u.property
  have hv := (mem_weakDerivativeGraph_iff Ω p v.val).mp v.property
  have hg : gradient Ω m p u = gradient Ω m p v := by
    apply coordinateLp_ext Ω p
    intro ij
    apply P102.U4.regularLp_injective Ω p.ennreal
    rcases ij with ⟨i,j⟩
    exact (hu i j).symm.trans ((congrArg (fun f => P102.U4.distributionPartial {j}
      (P102.U4.regularDistribution Ω (coordinateLp Ω p i f))) huv).trans (hv i j))
  apply Subtype.ext
  apply (WithLp.equiv p.ennreal _).injective
  exact Prod.ext huv hg

/-- The graph model contains exactly the distribution-defined value classes. -/
theorem value_range : Set.range (value Ω m p) = {u | HasWeakGradient Ω m p u} := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨gradient Ω m p v, (mem_weakDerivativeGraph_iff Ω p v.val).mp v.property⟩
  · rintro ⟨V, hV⟩
    exact ⟨⟨WithLp.toLp p.ennreal (u,V),
      (mem_weakDerivativeGraph_iff Ω p _).mpr hV⟩, rfl⟩


/-- First-order multi-indices are exactly zero and the coordinate singletons. -/
def firstIndex (d : ℕ) : Option (Fin d) → P102.U4.SobolevIndex d 1
  | none => P102.U4.zeroSobolevIndex d 1
  | some j => ⟨{j}, by simp⟩

theorem firstIndex_bijective (d : ℕ) : Function.Bijective (firstIndex d) := by
  constructor
  · intro a b h
    cases a with
    | none => cases b with
      | none => rfl
      | some j => have := congrArg (fun α : P102.U4.SobolevIndex d 1 => α.val.card) h
                  simp [firstIndex, P102.U4.zeroSobolevIndex] at this
    | some i => cases b with
      | none => have := congrArg (fun α : P102.U4.SobolevIndex d 1 => α.val.card) h
                simp [firstIndex, P102.U4.zeroSobolevIndex] at this
      | some j => exact congrArg some ((Multiset.singleton_inj.mp (congrArg Subtype.val h)))
  · intro α
    by_cases h : α.val.card = 0
    · exact ⟨none, Subtype.ext (Multiset.card_eq_zero.mp h).symm⟩
    · have hc : α.val.card = 1 := by have := α.property; omega
      obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hc
      exact ⟨some j, Subtype.ext hj.symm⟩

def firstIndexEquiv (d : ℕ) : Option (Fin d) ≃ P102.U4.SobolevIndex d 1 :=
  Equiv.ofBijective (firstIndex d) (firstIndex_bijective d)

@[simp] theorem firstIndexEquiv_apply (d : ℕ) (j : Option (Fin d)) :
    firstIndexEquiv d j = firstIndex d j := rfl

/-- A target coordinate's value and first derivatives in the scalar tuple model. -/
def coordinateTuple (i : Fin m) :
    GraphAmbient Ω m p →L[ℝ] P102.U4.SobolevTuple ℝ Ω 1 p.ennreal where
  toFun z := WithLp.toLp 1 fun α => match (firstIndexEquiv d).symm α with
    | none => coordinateLp Ω p i (graphValue Ω m p z)
    | some j => coordinateLp Ω p (i,j) (graphGradient Ω m p z)
  map_add' u v := by
    apply PiLp.ext
    intro α
    simp only [PiLp.add_apply]
    cases h : (firstIndexEquiv d).symm α with
    | none => simpa only [h, ContinuousLinearMap.comp_apply] using ((coordinateLp Ω p i).comp (graphValue Ω m p)).map_add u v
    | some j => simpa only [h, ContinuousLinearMap.comp_apply] using ((coordinateLp Ω p (i,j)).comp (graphGradient Ω m p)).map_add u v
  map_smul' c u := by
    apply PiLp.ext
    intro α
    simp only [PiLp.smul_apply, RingHom.id_apply]
    cases h : (firstIndexEquiv d).symm α with
    | none => simpa only [h, ContinuousLinearMap.comp_apply] using ((coordinateLp Ω p i).comp (graphValue Ω m p)).map_smul c u
    | some j => simpa only [h, ContinuousLinearMap.comp_apply] using ((coordinateLp Ω p (i,j)).comp (graphGradient Ω m p)).map_smul c u
  cont := (PiLp.continuous_toLp 1 _).comp (continuous_pi fun α => by
    cases h : (firstIndexEquiv d).symm α with
    | none => exact ((coordinateLp Ω p i).comp (graphValue Ω m p)).continuous
    | some j => exact ((coordinateLp Ω p (i,j)).comp (graphGradient Ω m p)).continuous)

@[simp] theorem coordinateTuple_zero (i : Fin m) (z : GraphAmbient Ω m p) :
    coordinateTuple Ω p i z (P102.U4.zeroSobolevIndex d 1) =
      coordinateLp Ω p i (graphValue Ω m p z) := by
  change (match (firstIndexEquiv d).symm (firstIndexEquiv d none) with | none => _ | some j => _) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem coordinateTuple_single (i : Fin m) (j : Fin d) (z : GraphAmbient Ω m p) :
    coordinateTuple Ω p i z ⟨{j}, by simp⟩ =
      coordinateLp Ω p (i,j) (graphGradient Ω m p z) := by
  change (match (firstIndexEquiv d).symm (firstIndexEquiv d (some j)) with | none => _ | some j => _) = _
  rw [Equiv.symm_apply_apply]

theorem coordinateTuple_mem (i : Fin m) (u : W1p Ω m p) :
    coordinateTuple Ω p i u.val ∈ P102.U4.sobolevSubmodule ℝ Ω 1 p.ennreal := by
  apply (P102.U4.mem_sobolevSubmodule_iff Ω 1 p.ennreal _).mpr
  intro α φ
  obtain ⟨a, rfl⟩ := (firstIndexEquiv d).surjective α
  cases a with
  | none => simp [firstIndex, P102.U4.zeroSobolevIndex, P102.U4.testPartialWord]
  | some j =>
    have h := (mem_weakDerivativeGraph_iff Ω p u.val).mp u.property i j
    have he := (P102.U4.distributionPartial_eq_regularLp_iff Ω p.ennreal _ _ _).mp h φ
    simpa [firstIndex] using he

/-- The coordinate map, with continuity for the actual Euclidean Sobolev norm. -/
def toCoordinates : W1p Ω m p →L[ℝ] (Fin m → P102.U4.Sobolev ℝ Ω 1 p.ennreal) :=
  ContinuousLinearMap.pi fun i =>
    { toFun := fun u => ⟨coordinateTuple Ω p i u.val, coordinateTuple_mem Ω p i u⟩
      map_add' := fun _ _ => Subtype.ext ((coordinateTuple Ω p i).map_add _ _)
      map_smul' := fun _ _ => Subtype.ext ((coordinateTuple Ω p i).map_smul _ _)
      cont := ((coordinateTuple Ω p i).continuous.comp continuous_subtype_val).subtype_mk _ }

@[simp] theorem toCoordinates_value (u : W1p Ω m p) (i : Fin m) :
    P102.U4.sobolevUnderlying (toCoordinates Ω p u i) = coordinateLp Ω p i (value Ω m p u) :=
  coordinateTuple_zero Ω p i u.val

@[simp] theorem toCoordinates_derivative (u : W1p Ω m p) (i : Fin m) (j : Fin d) :
    P102.U4.sobolevDerivative (toCoordinates Ω p u i) ⟨{j}, by simp⟩ =
      coordinateLp Ω p (i,j) (gradient Ω m p u) :=
  coordinateTuple_single Ω p i j u.val

/-- The weak-derivative graph is a closed subspace of its Euclidean Lp product. -/
theorem weakDerivativeGraph_closed :
    IsClosed (weakDerivativeGraph Ω m p : Set (GraphAmbient Ω m p)) := by
  simp only [weakDerivativeGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun φ =>
    (derivativeEquation Ω m p i j φ).isClosed_ker

instance w1pCompleteSpace : CompleteSpace (W1p Ω m p) :=
  (weakDerivativeGraph_closed Ω p).completeSpace_coe

theorem toCoordinates_bijective : Function.Bijective (toCoordinates (m := m) Ω p) := by
  constructor
  · intro u v h
    apply value_injective Ω p
    apply coordinateLp_ext Ω p
    intro i
    simpa only [toCoordinates_value] using
      congrArg (fun f : Fin m → P102.U4.Sobolev ℝ Ω 1 p.ennreal => P102.U4.sobolevUnderlying (f i)) h
  · intro v
    let U := assembleLp Ω p (fun i => P102.U4.sobolevUnderlying (v i))
    let V := assembleLp Ω p (fun ij : Fin m × Fin d =>
      P102.U4.sobolevDerivative (v ij.1) ⟨{ij.2}, by simp⟩)
    have hUV : WithLp.toLp p.ennreal (U,V) ∈ weakDerivativeGraph Ω m p := by
      apply (mem_weakDerivativeGraph_iff Ω p _).mpr
      intro i j
      change P102.U4.distributionPartial {j} (P102.U4.regularDistribution Ω (coordinateLp Ω p i U)) =
        P102.U4.regularDistribution Ω (coordinateLp Ω p (i,j) V)
      simp only [U, V, coordinate_assemble]
      exact P102.U4.sobolev_derivative_distribution Ω 1 p.ennreal (v i) ⟨{j}, by simp⟩
    let u : W1p Ω m p := ⟨WithLp.toLp p.ennreal (U,V), hUV⟩
    refine ⟨u, funext fun i => ?_⟩
    apply P102.U4.sobolevUnderlying_injective Ω 1 p.ennreal
    rw [toCoordinates_value]
    exact coordinate_assemble Ω p i _

/-- Canonical coordinate identification. Its inverse is continuous by the Banach
open mapping theorem; no equality of the distinct norms is asserted. -/
def coordinateEquiv : W1p Ω m p ≃L[ℝ] (Fin m → P102.U4.Sobolev ℝ Ω 1 p.ennreal) :=
  ContinuousLinearEquiv.ofBijective (E := W1p Ω m p)
    (F := Fin m → P102.U4.Sobolev ℝ Ω 1 p.ennreal) (toCoordinates (m := m) Ω p)
    (LinearMap.ker_eq_bot.mpr (toCoordinates_bijective (m := m) Ω p).1)
    (LinearMap.range_eq_top.mpr (toCoordinates_bijective (m := m) Ω p).2)

@[simp] theorem coordinateEquiv_apply (u : W1p Ω m p) :
    coordinateEquiv Ω p u = toCoordinates Ω p u := rfl


/-- The source closure of smooth vector functions. -/
theorem zeroSubmodule_eq_closure :
    (zeroSubmodule Ω m p : Set (W1p Ω m p)) =
      closure {u | ∃ φ : Fin m → P102.U4.TestSpace ℝ Ω,
        ∀ i, coordinateLp Ω p i (value Ω m p u) = P102.U4.testToDomainLp Ω p.ennreal (φ i)} := by
  have hs : (smoothSubmodule Ω m p : Set (W1p Ω m p)) =
      {u | ∃ φ : Fin m → P102.U4.TestSpace ℝ Ω,
        ∀ i, coordinateLp Ω p i (value Ω m p u) = P102.U4.testToDomainLp Ω p.ennreal (φ i)} := by
    apply Set.ext
    intro u
    change u ∈ smoothSubmodule Ω m p ↔ _
    simp only [smoothSubmodule, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.mem_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      choose φ hφ using h
      exact ⟨φ, fun i => (hφ i).symm⟩
    · rintro ⟨φ, hφ⟩ i
      exact ⟨φ i, (hφ i).symm⟩
  exact congrArg closure hs

/-- Closure in the Euclidean full norm transports to the scalar sum-norm closures. -/
theorem zero_mem_iff_coordinates (u : W1p Ω m p) :
    u ∈ zeroSubmodule Ω m p ↔
      ∀ i, coordinateEquiv Ω p u i ∈ P102.U4.sobolevZeroSubmodule ℝ Ω 1 p.ennreal := by
  have hs : (smoothSubmodule Ω m p : Set (W1p Ω m p)) =
      (coordinateEquiv Ω p) ⁻¹' (Set.univ.pi fun _ : Fin m =>
        (P102.U4.smoothSobolevSubmodule ℝ Ω 1 p.ennreal : Set _)) := by
    ext v
    simp [smoothSubmodule, P102.U4.smoothSobolevSubmodule, Set.mem_pi,
      P102.U4.sobolevUnderlyingCLM, coordinateTuple_zero, toCoordinates, value]
  change u ∈ closure (smoothSubmodule Ω m p : Set (W1p Ω m p)) ↔ _
  rw [hs]
  change u ∈ closure ((coordinateEquiv (m := m) Ω p).toHomeomorph ⁻¹'
    (Set.univ.pi fun _ : Fin m => (P102.U4.smoothSobolevSubmodule ℝ Ω 1 p.ennreal : Set _))) ↔ _
  rw [← (coordinateEquiv (m := m) Ω p).toHomeomorph.preimage_closure, closure_pi_set]
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
  rfl

/-- The matrix pairing is the Frobenius sum, with target index first. -/
theorem frobenius_eq_sum (A B : Gradient m d) :
    frobenius A B = ∑ i : Fin m, ∑ j : Fin d, A (i,j) * B (i,j) := by
  simp [frobenius, PiLp.inner_apply, Fintype.sum_prod_type, mul_comm]

/-- The matrix fiber norm is the Frobenius norm. -/
theorem gradient_norm_eq (A : Gradient m d) :
    ‖A‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin d, (A (i,j)) ^ 2) := by
  simpa [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq A

/-- Changing either field on a null set never changes its integrand class. -/
theorem composition_ae_eq (F : Domain d → Vector m → Gradient m d → ℝ)
    {u v : Domain d → Vector m} {U V : Domain d → Gradient m d}
    (hu : u =ᵐ[domainMeasure Ω] v) (hV : U =ᵐ[domainMeasure Ω] V) :
    (fun x => F x (u x) (U x)) =ᵐ[domainMeasure Ω] fun x => F x (v x) (V x) := by
  filter_upwards [hu, hV] with x hx hy
  rw [hx, hy]

/-- Signed extended energy is independent of both representatives. -/
theorem energyOnFields_congr (F : Domain d → Vector m → Gradient m d → ℝ)
    {u v : Domain d → Vector m} {U V : Domain d → Gradient m d}
    (hu : u =ᵐ[domainMeasure Ω] v) (hV : U =ᵐ[domainMeasure Ω] V) :
    energyOnFields Ω F u U = energyOnFields Ω F v V := by
  have h := composition_ae_eq Ω F hu hV
  unfold energyOnFields
  congr 1 <;> congr 1 <;> apply lintegral_congr_ae <;>
    filter_upwards [h] with x hx <;> rw [hx]

/-- Finite measurable partitions allow a.e. measurable parameter sections. -/
theorem simpleFunc_composition_aemeasurable {Y : Type*}
    (F : Domain d → Y → ℝ)
    (hF : ∀ y, AEMeasurable (fun x => F x y) (domainMeasure Ω))
    (s : SimpleFunc (Domain d) Y) :
    AEMeasurable (fun x => F x (s x)) (domainMeasure Ω) := by
  classical
  have he : (fun x => F x (s x)) =
      fun x => ∑ y ∈ s.range, (s ⁻¹' {y}).indicator (fun x => F x y) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (s x)]
    · simp
    · intro y _ hy
      simp [Set.indicator, Ne.symm hy]
    · simp
  rw [he]
  simpa only [Finset.sum_fn] using
    (Finset.aemeasurable_sum s.range fun y _ => (hF y).indicator (s.measurableSet_fiber y))

/-- The Carathéodory composition theorem, allowing a common exceptional null
set for fiber continuity and a.e. measurable base-point sections. -/
theorem caratheodory_composition {Y : Type*} [NormedAddCommGroup Y]
    (F : Domain d → Y → ℝ)
    (hF : ∀ y, AEMeasurable (fun x => F x y) (domainMeasure Ω))
    (hcont : ∀ᵐ x ∂domainMeasure Ω, Continuous (F x))
    {w : Domain d → Y} (hw : StronglyMeasurable w) :
    AEMeasurable (fun x => F x (w x)) (domainMeasure Ω) := by
  apply aemeasurable_of_tendsto_metrizable_ae' (fun n =>
    simpleFunc_composition_aemeasurable Ω F hF (hw.approx n))
  filter_upwards [hcont] with x hx
  exact (hx.tendsto (w x)).comp (hw.tendsto_approx x)

/-- Evaluation on the selected measurable Lp representatives is measurable. -/
theorem energy_integrand_aemeasurable
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (hF : ∀ s Z, AEMeasurable (fun x => F x s Z) (domainMeasure Ω))
    (hcont : ∀ᵐ x ∂domainMeasure Ω, Continuous (fun y : Vector m × Gradient m d => F x y.1 y.2))
    (u : W1p Ω m p) :
    AEMeasurable (fun x => F x (value Ω m p u x) (gradient Ω m p u x)) (domainMeasure Ω) :=
  caratheodory_composition Ω (fun x (y : Vector m × Gradient m d) => F x y.1 y.2)
    (fun y => hF y.1 y.2) hcont
    ((Lp.stronglyMeasurable (value Ω m p u)).prodMk (Lp.stronglyMeasurable (gradient Ω m p u)))


/-- Every compactly supported smooth vector function gives a class in the graph. -/
theorem smooth_inclusion (φ : Fin m → P102.U4.TestSpace ℝ Ω) :
    ∃ u : W1p Ω m p, ∀ i,
      coordinateLp Ω p i (value Ω m p u) = P102.U4.testToDomainLp Ω p.ennreal (φ i) := by
  have h (i : Fin m) := P102.U4.zeroExtension_smoothInclusion Ω 1 p.ennreal (φ i)
  choose v hv using h
  let u := (coordinateEquiv Ω p).symm v
  refine ⟨u, fun i => ?_⟩
  calc
    coordinateLp Ω p i (value Ω m p u) =
        P102.U4.sobolevUnderlying (coordinateEquiv Ω p u i) := (toCoordinates_value Ω p u i).symm
    _ = P102.U4.sobolevUnderlying (v i) := congrArg P102.U4.sobolevUnderlying
      (congrFun ((coordinateEquiv Ω p).apply_symm_apply v) i)
    _ = P102.U4.testToDomainLp Ω p.ennreal (φ i) := hv i

/-- Weak convergence is unchanged under the finite scalar coordinate model. -/
theorem weaklyConverges_iff_coordinates (u : ℕ → W1p Ω m p) (v : W1p Ω m p) :
    WeaklyConverges u v ↔ ∀ (i : Fin m) (ℓ : P102.U4.Sobolev ℝ Ω 1 p.ennreal →L[ℝ] ℝ),
      Filter.Tendsto (fun n => ℓ (coordinateEquiv Ω p (u n) i)) Filter.atTop
        (nhds (ℓ (coordinateEquiv Ω p v i))) := by
  constructor
  · intro h i ℓ
    exact h (ℓ.comp ((ContinuousLinearMap.proj i).comp (coordinateEquiv Ω p).toContinuousLinearMap))
  · intro h ℓ
    let L := ℓ.comp (coordinateEquiv Ω p).symm.toContinuousLinearMap
    have he (w : W1p Ω m p) :
        (∑ i : Fin m, (L.comp (ContinuousLinearMap.single ℝ
          (fun _ : Fin m => P102.U4.Sobolev ℝ Ω 1 p.ennreal) i)) (coordinateEquiv Ω p w i)) = ℓ w := by
      rw [ContinuousLinearMap.sum_comp_single]
      exact congrArg ℓ ((coordinateEquiv Ω p).symm_apply_apply w)
    have ht := tendsto_finsetSum Finset.univ (fun i _ =>
      h i (L.comp (ContinuousLinearMap.single ℝ
        (fun _ : Fin m => P102.U4.Sobolev ℝ Ω 1 p.ennreal) i)))
    simpa only [he] using ht


/-- Coordinate projection of a genuine vector test. -/
def vectorTestCoordinate (φ : VectorTest Ω m) (i : Fin m) : P102.U4.TestSpace ℝ Ω :=
  TestFunction.postcompCLM (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i) φ

/-- Finite sums of basis injections assemble scalar tests into a vector test. -/
def vectorTestAssemble (φ : Fin m → P102.U4.TestSpace ℝ Ω) : VectorTest Ω m :=
  ∑ i : Fin m, TestFunction.postcompCLM
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))) (φ i)

@[simp] theorem vectorTestCoordinate_assemble (φ : Fin m → P102.U4.TestSpace ℝ Ω) (i : Fin m) :
    vectorTestCoordinate Ω (vectorTestAssemble Ω φ) i = φ i := by
  ext x
  simp [vectorTestCoordinate, vectorTestAssemble, Function.comp_apply]

/-- Projection of a smooth vector class is exactly its smooth scalar class. -/
theorem coordinate_testToValueLp (φ : VectorTest Ω m) (i : Fin m) :
    coordinateLp Ω p i (testToValueLp Ω m p φ) =
      P102.U4.testToDomainLp Ω p.ennreal (vectorTestCoordinate Ω φ i) := by
  apply Lp.ext
  have hφ := (φ.continuous.memLp_of_hasCompactSupport (p := p.ennreal)
    (μ := domainMeasure Ω) φ.hasCompactSupport).coeFn_toLp
  filter_upwards [coordinateLp_ae Ω p i (testToValueLp Ω m p φ), hφ,
    P102.U4.testToDomainLp_ae Ω p.ennreal (vectorTestCoordinate Ω φ i)] with x hx hy hz
  exact hx.trans ((congrArg (fun v : Vector m => v i) hy).trans hz.symm)

/-- The coordinate definition of smooth classes equals the actual vector-test image. -/
theorem smoothSubmodule_eq_vector_tests :
    (smoothSubmodule Ω m p : Set (W1p Ω m p)) =
      {u | ∃ φ : VectorTest Ω m, value Ω m p u = testToValueLp Ω m p φ} := by
  apply Set.ext
  intro u
  change u ∈ smoothSubmodule Ω m p ↔ _
  simp only [smoothSubmodule, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mem_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    Set.mem_ofPred_eq]
  constructor
  · intro h
    choose φ hφ using h
    refine ⟨vectorTestAssemble Ω φ, coordinateLp_ext Ω p fun i => ?_⟩
    rw [coordinate_testToValueLp, vectorTestCoordinate_assemble]
    exact (hφ i).symm
  · rintro ⟨φ, hφ⟩ i
    refine ⟨vectorTestCoordinate Ω φ i, ?_⟩
    rw [hφ, coordinate_testToValueLp]

namespace Definitions

abbrev space : Expected.SpaceType := @W1p
abbrev zeroSpace : Expected.ZeroSpaceType := @W1pZero
abbrev h1Space : Expected.H1SpaceType := @H1
abbrev h1ZeroSpace : Expected.H1ZeroSpaceType := @H1Zero
abbrev valueMap : Expected.ValueMapType := @value
abbrev gradientMap : Expected.GradientMapType := @gradient
abbrev zeroBoundarySubmodule : Expected.ZeroBoundarySubmoduleType := @zeroSubmodule
abbrev admissibleClass : Expected.AffineClassType := @affineClass
abbrev weakConvergence : Expected.WeakConvergenceType := @WeaklyConverges
abbrev evaluateEnergy : Expected.EnergyType := @energy
abbrev matrixPairing : Expected.MatrixPairingType := @frobenius

end Definitions


theorem source_norm : Expected.NormFormula := by
  intro d m Ω p u
  exact norm_eq Ω p u

theorem class_injective : Expected.ValueInjective := by
  intro d m Ω p
  exact value_injective Ω p

theorem class_range : Expected.ValueRange := by
  intro d m Ω p
  exact value_range Ω p

theorem distribution_derivative : Expected.DerivativeDistribution := by
  intro d m Ω p u i j
  exact (mem_weakDerivativeGraph_iff Ω p u.val).mp u.property i j

theorem coordinate_bridge : Expected.CoordinateBridge := by
  intro d m Ω p
  refine ⟨coordinateEquiv Ω p, ?_, ?_, ?_, ?_, ?_⟩
  · exact toCoordinates_value Ω p
  · exact toCoordinates_derivative Ω p
  · intro A
    exact (coordinateEquiv Ω p).toHomeomorph.image_closure A
  · exact zero_mem_iff_coordinates Ω p
  · exact weaklyConverges_iff_coordinates Ω p

theorem frobenius_formulas : Expected.FrobeniusFormula :=
  ⟨fun A B => frobenius_eq_sum A B, fun A => gradient_norm_eq A⟩

theorem measurable_representatives : Expected.MeasurableRepresentatives := by
  intro d m Ω p u
  exact ⟨Lp.stronglyMeasurable _, Lp.stronglyMeasurable _⟩

theorem composition_congr : Expected.CompositionCongr := by
  intro d m Ω F u v U V hu hV
  exact composition_ae_eq Ω F hu hV

theorem energy_congr : Expected.EnergyCongr := by
  intro d m Ω F u v U V hu hV
  exact energyOnFields_congr Ω F hu hV

theorem composition_measurable : Expected.CompositionMeasurable := by
  intro d m Ω F hF hcont u V hu hV
  let hw : AEStronglyMeasurable (fun x => (u x, V x)) (domainMeasure Ω) :=
    hu.aestronglyMeasurable.prodMk hV.aestronglyMeasurable
  have hm := caratheodory_composition Ω (fun x (y : Vector m × Gradient m d) => F x y.1 y.2)
    (fun y => hF y.1 y.2) hcont hw.stronglyMeasurable_mk
  apply hm.congr
  filter_upwards [hw.ae_eq_mk] with x hx
  exact congrArg (fun y : Vector m × Gradient m d => F x y.1 y.2) hx.symm


theorem zero_closure : Expected.ZeroClosure := by
  intro d m Ω p
  exact congrArg closure (smoothSubmodule_eq_vector_tests Ω p)

theorem smooth_vector_inclusion : Expected.SmoothInclusion := by
  intro d m Ω p φ
  obtain ⟨u, hu⟩ := smooth_inclusion Ω p (vectorTestCoordinate Ω φ)
  refine ⟨u, coordinateLp_ext Ω p fun i => ?_⟩
  rw [coordinate_testToValueLp]
  exact hu i

end VariationalNotes.Sobolev
