import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GeodesicCriticalityCorners
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.FirstVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialNormalCoordinates
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Hom.Set
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.Frobenius

/-! The criticality and corners portion of Theorem 6.8.
The original intrinsic tangent fibers and actual maximal exponential domains
are used throughout. Energy includes constant curves. Arc-length parameters
and all corner variations are constructed, and no completeness is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData
  P202.GeodesicData P202.ExponentialData
open Set Filter MeasureTheory
open scoped Topology
universe u

variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- Smooth scalar test functions suffice to detect a continuous function on a
closed nondegenerate interval, including its endpoint values. -/
theorem scalar_fundamental_lemma :
    P202Specs.Geometry.GeodesicCriticalityCorners.scalar_fundamental_lemmaType := by
  intro a b hab f hf htest
  have hf' : ContinuousOn f (Ioo a b) := hf.mono Ioo_subset_Icc_self
  have hae : ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf'.locallyIntegrableOn measurableSet_Ioo)
    intro φ hφ hc hsupp
    have hs : Function.support (fun t => φ t * f t) ⊆ Ioc a b := by
      intro t ht
      apply Ioo_subset_Ioc_self
      apply hsupp
      apply subset_closure
      exact Function.mem_support.mpr (fun hh => ht (by simp [hh]))
    simp only [smul_eq_mul]
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
    exact htest φ hφ hc hsupp
  have heq : EqOn f (fun _ => 0) (Ioo a b) :=
    Measure.eqOn_open_of_ae_eq
      ((ae_restrict_iff' measurableSet_Ioo).mpr hae) isOpen_Ioo hf' continuousOn_const
  exact heq.of_subset_closure hf continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])

/-- A fixed parameter trace has zero actual variation velocity. -/
theorem variationField_zero_of_fixed {F : ℝ × ℝ → M} {ε t : ℝ}
    (hε : 0 < ε) (hfix : ∀ s ∈ Ioo (-ε) ε, F (s,t) = F (0,t)) :
    variationField S F t = 0 := by
  have heq : (fun s : ℝ => F (s,t)) =ᶠ[𝓝 0] (fun _ => F (0,t)) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hε) hε] with s hs
    exact hfix s hs
  have hv : HasVelocityAt S (fun s => F (s,t)) 0 0 := by
    simpa using PiecewiseCurves.HasVelocityAt.congr
      (PiecewiseCurves.hasVelocityAt_const (S := S) (F (0,t)) 0) heq.symm
  exact PiecewiseCurves.velocity_eq hv

theorem fixed_endpoint_fields :
    P202Specs.Geometry.GeodesicCriticalityCorners.fixed_endpoint_fieldsType.{u} := by
  intro n kind M _ S F ε a b hε hfix
  exact ⟨variationField_zero_of_fixed hε (fun s hs => (hfix s hs).1),
    variationField_zero_of_fixed hε (fun s hs => (hfix s hs).2)⟩

theorem fixed_endpoint_energy :
    P202Specs.Geometry.GeodesicCriticalityCorners.fixed_endpoint_energyType.{u} := by
  intro n kind M _ S g C hC F ε a b hε hab hF hfix
  obtain ⟨ha, hb⟩ := fixed_endpoint_fields F ε a b hε hfix (S := S)
  have hd := FirstVariation.first_variation_energy g C hC F ε a b hε hab hF
  simpa only [energyFirstVariation, variationPairing, ha, hb, map_zero,
    LinearMap.zero_apply, sub_self, zero_sub] using hd

theorem fixed_endpoint_length :
    P202Specs.Geometry.GeodesicCriticalityCorners.fixed_endpoint_lengthType.{u} := by
  intro n kind M _ S g C hC F ε a b hε hab hF hfix hpos
  obtain ⟨ha, hb⟩ := fixed_endpoint_fields F ε a b hε hfix (S := S)
  have hd := FirstVariation.first_variation_length g C hC F ε a b hε hab hF hpos
  simpa only [lengthFirstVariation, variationPairing, ha, hb, map_zero,
    LinearMap.zero_apply, sub_self, zero_sub] using hd

/-- A covariantly constant field makes the fixed-endpoint interior term zero. -/
theorem integral_variationPairing_zero_of_parallel (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) {F : ℝ × ℝ → M} {a b : ℝ}
    (hab : a < b) {W : (t : ℝ) → TangentSpace S (F (0,t))}
    (hW : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
      W (Icc a b) t 0) :
    (∫ t in a..b, variationPairing g F
      (covariantDerivativeWithin C (fun r => F (0,r)) W (Icc a b)) t) = 0 := by
  calc
    _ = ∫ _t in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using ht
      have hD := CurveCovariantDerivative.covariantDerivativeWithin_eq C ht'
        (uniqueDiffOn_Icc hab t ht') (hW t ht')
      simp only [variationPairing, hD, map_zero]
    _ = 0 := by simp

theorem geodesic_energy_stationary :
    P202Specs.Geometry.GeodesicCriticalityCorners.geodesic_energy_stationaryType.{u} := by
  intro n kind M _ S g C hC F ε a b hε hab hF hfix hgeo
  have hd := fixed_endpoint_energy g C hC F ε a b hε hab.le hF hfix
  simpa only [integral_variationPairing_zero_of_parallel g C hab hgeo, neg_zero] using hd

theorem parallel_unit_length_stationary :
    P202Specs.Geometry.GeodesicCriticalityCorners.parallel_unit_length_stationaryType.{u} := by
  intro n kind M _ S g C hC F ε a b hε hab hF hfix hpos hgeo
  have hd := fixed_endpoint_length g C hC F ε a b hε hab.le hF hfix hpos
  simpa only [integral_variationPairing_zero_of_parallel g C hab hgeo, neg_zero] using hd

/-- The fixed-endpoint energy criticality problem reduces exactly to testing
the acceleration integral against all realizable variation fields. -/
theorem energy_stationary_iff_integral_zero
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hε : 0 < ε) (hab : a ≤ b) (hF : SmoothVariationOn S F ε a b)
    (hfix : EndpointFixed F ε a b) :
    HasDerivAt (variedEnergy g F a b) 0 0 ↔
      (∫ t in a..b, variationPairing g F
        (covariantDerivativeWithin C (fun r => F (0,r))
          (segmentVelocity S F a b) (Icc a b)) t) = 0 := by
  have hd := fixed_endpoint_energy g C hC F ε a b hε hab hF hfix
  constructor
  · intro hzero
    exact neg_eq_zero.mp (hd.unique hzero)
  · intro hint
    simpa only [hint, neg_zero] using hd

theorem length_stationary_iff_integral_zero
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hε : 0 < ε) (hab : a ≤ b) (hF : SmoothVariationOn S F ε a b)
    (hfix : EndpointFixed F ε a b)
    (hpos : ∀ t ∈ Icc a b,
      0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) :
    HasDerivAt (variedLength g F a b) 0 0 ↔
      (∫ t in a..b, variationPairing g F
        (covariantDerivativeWithin C (fun r => F (0,r))
          (unitVelocity g F a b) (Icc a b)) t) = 0 := by
  have hd := fixed_endpoint_length g C hC F ε a b hε hab hF hfix hpos
  constructor
  · intro hzero
    exact neg_eq_zero.mp (hd.unique hzero)
  · intro hint
    simpa only [hint, neg_zero] using hd

/-- For parallel unit velocities on each piece and fixed outer endpoints,
the entire length derivative is the sum of the genuine corner terms. -/
theorem piecewise_parallel_length_derivative
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hF : ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ))
    (hfix : EndpointFixed F ε (node 0) (node (Fin.last (k+1))))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (F (0,t)) (segmentVelocity S F (node i.castSucc) (node i.succ) t))
    (hpar : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      HasCovariantDerivativeWithinAt C (fun r => F (0,r))
        (unitVelocity g F (node i.castSucc) (node i.succ))
        (Icc (node i.castSucc) (node i.succ)) t 0) :
    HasDerivAt (variedLength g F (node 0) (node (Fin.last (k+1))))
      (∑ j : Fin k, lengthCorner g F node j) 0 := by
  have hd := FirstVariation.piecewise_length g C hC F ε hε node hnode hF hpos
  obtain ⟨ha, hb⟩ := fixed_endpoint_fields F ε _ _ hε hfix (S := S)
  have hint : (∑ i : Fin (k+1), ∫ t in node i.castSucc..node i.succ,
      variationPairing g F
        (covariantDerivativeWithin C (fun r => F (0,r))
          (unitVelocity g F (node i.castSucc) (node i.succ))
          (Icc (node i.castSucc) (node i.succ))) t) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact integral_variationPairing_zero_of_parallel g C
      (hnode (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) (hpar i)
  rw [hint] at hd
  simpa only [variationPairing, ha, hb, map_zero, LinearMap.zero_apply,
    sub_self, zero_add, sub_zero] using hd

/-- Once a genuine variation moves just one join, minimality kills its
individual unit-velocity corner pairing. Constructing such variations with
arbitrary join value is still required for the unconditional no-corner theorem. -/
theorem isolated_corner_zero_of_minimum
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hF : ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ))
    (hfix : EndpointFixed F ε (node 0) (node (Fin.last (k+1))))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (F (0,t)) (segmentVelocity S F (node i.castSucc) (node i.succ) t))
    (hpar : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      HasCovariantDerivativeWithinAt C (fun r => F (0,r))
        (unitVelocity g F (node i.castSucc) (node i.succ))
        (Icc (node i.castSucc) (node i.succ)) t 0)
    (hmin : IsLocalMin (variedLength g F (node 0) (node (Fin.last (k+1)))) 0)
    (j₀ : Fin k)
    (hother : ∀ j : Fin k, j ≠ j₀ → variationField S F (node j.succ.castSucc) = 0) :
    lengthCorner g F node j₀ = 0 := by
  have hsum := hmin.hasDerivAt_eq_zero
    (piecewise_parallel_length_derivative g C hC hε node hnode hF hfix hpos hpar)
  have heq : (∑ j : Fin k, lengthCorner g F node j) = lengthCorner g F node j₀ := by
    apply Finset.sum_eq_single j₀
    · intro j _ hj
      simp only [lengthCorner, variationPairing, hother j hj,
        map_zero, LinearMap.zero_apply]
    · simp
  rwa [heq] at hsum

/-- Positive definiteness turns arbitrary corner test pairings into equality
of the two unit velocities in their common intrinsic tangent fiber. -/
theorem eq_of_all_pairings_sub_zero (g : RiemannianMetric S) (p : M)
    (v w : TangentSpace S p)
    (htest : ∀ z : TangentSpace S p, pairing g p z (v - w) = 0) : v = w := by
  apply sub_eq_zero.mp
  by_contra hne
  exact (ne_of_gt (g.positive p (v - w) hne)) (htest (v - w))

/-- Uniform definition of exp(γ(t),sV(t)) on the compact parameter interval.
This is only the domain step, not a smoothness or realization certificate. -/
theorem uniform_exponential_domain :
    P202Specs.Geometry.GeodesicCriticalityCorners.uniform_exponential_domainType.{u} := by
  intro n M _ S C F hF γ V a b hV
  let H : ℝ × Icc a b → Phase S := fun z => ⟨γ z.2.val, z.1 • V z.2.val⟩
  have hH : Continuous H := by
    apply continuousOn_univ.mp
    exact hV.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun z _ => ⟨mem_univ _, z.2.property⟩)
  let O := H ⁻¹' exponentialDomain F
  have hO : IsOpen O := (ExponentialNormalCoordinates.domain_open S C F hF).preimage hH
  have hKO : ({(0 : ℝ)} : Set ℝ) ×ˢ (univ : Set (Icc a b)) ⊆ O := by
    rintro ⟨s,t⟩ ⟨hs, _⟩
    have hs0 : s = 0 := hs
    subst s
    simpa only [O, mem_preimage, H, zero_smul] using
      (ExponentialNormalCoordinates.zero_section S C F hF (γ t.val)).1
  obtain ⟨U, W, hU, _, h0U, hW, hUW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hO hKO
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro s hs t ht
  have hsU : s ∈ U := by
    apply hdU
    change dist s 0 < d
    rw [Real.dist_eq, sub_zero]
    exact (abs_le.mpr hs).trans_lt (half_lt_self hd)
  exact hUW (show (s, (⟨t,ht⟩ : Icc a b)) ∈ U ×ˢ W from
    ⟨hsU, hW (mem_univ _)⟩)

/-- The radial identity proves the prescribed variation velocity without any
choice of coordinate extensions or complete-geodesic assumption. -/
theorem exponential_ray_velocity :
    P202Specs.Geometry.GeodesicCriticalityCorners.exponential_ray_velocityType.{u} := by
  intro n M _ S C F hF p v
  let q := F.curve ⟨p,v⟩
  have h0 := (hF ⟨p,v⟩).1
  have hi : q 0 = (⟨p,v⟩ : Phase S) := (hF ⟨p,v⟩).2.1
  obtain ⟨hc, e, he, hp, hd⟩ := ((hF ⟨p,v⟩).2.2.1 0 h0).1
  have hv : HasVelocityAt S (fun s => (q s).1) 0 (q 0).2 :=
    ⟨hc.continuousAt univ_mem, e, he, hp, hasDerivWithinAt_univ.mp hd⟩
  have heq : (fun s => (q s).1) =ᶠ[𝓝 0]
      (fun s : ℝ => fiberExponential F p (s • v)) := by
    filter_upwards [(F.interval ⟨p,v⟩).isOpen.mem_nhds h0] with s hs
    exact (ExponentialNormalCoordinates.radial_identity_at C F hF p v s hs).2.symm
  have hvel := PiecewiseCurves.velocity_eq (PiecewiseCurves.HasVelocityAt.congr hv heq)
  apply (heq_of_eq hvel).trans
  apply (cast_heq _ _).trans
  have : HEq (q 0).2 v := by rw [hi]
  exact this

section Realization
variable {S : SmoothManifold n .euclidean M}
open SmoothManifolds.TangentBundleData SmoothManifolds.MapData

/-- Scalar multiplication of the vector part of canonical tangent coordinates. -/
private noncomputable def scalePhaseCoordinates (s : ℝ) (x : Euclidean (n+n)) :
    Euclidean (n+n) :=
  let L := (tangentStructure S).productCoordinates.linearEquiv
  L ((L.symm x).1, s • (L.symm x).2)

private theorem scalePhaseCoordinates_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Euclidean (n+n) =>
      scalePhaseCoordinates (S := S) z.1 z.2) := by
  let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
  exact L.contDiff.comp ((L.symm.contDiff.comp contDiff_snd).fst.prodMk
    (contDiff_fst.smul (L.symm.contDiff.comp contDiff_snd).snd))

private theorem scaled_chart (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (v : TangentSpace S p) (s : ℝ) :
    (((tangentStructure S).chart e he) ⟨p, s • v⟩).val =
      scalePhaseCoordinates (S := S) s
        ((((tangentStructure S).chart e he) ⟨p,v⟩).val) := by
  rw [(tangentStructure S).chart_apply e he _ hp,
    (tangentStructure S).chart_apply e he _ hp]
  simp [scalePhaseCoordinates]

/-- Scaling a smooth field gives smooth coordinate germs jointly in its scale
and curve parameter. The proof uses the original tangent-bundle topology. -/
theorem scaled_field_germ {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) {z : ℝ × ℝ} (hz : z.2 ∈ J) :
    ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val),
      γ z.2 ∈ e.source ∧ ∃ x : ℝ × ℝ → Euclidean (n+n),
        ContDiffAt ℝ (⊤ : ℕ∞) x z ∧
        x z = (((tangentStructure S).chart e he) ⟨γ z.2, z.1 • V z.2⟩).val ∧
        (fun w : ℝ × ℝ => (((tangentStructure S).chart e he)
          ⟨γ w.2, w.1 • V w.2⟩).val) =ᶠ[𝓝[univ ×ˢ J] z] x := by
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hV.2 z.2 hz
  let d := (tangentStructure S).chart e he
  have hsource : (⟨γ z.2, V z.2⟩ : Phase S) ∈ d.source := by
    simpa only [d, (tangentStructure S).chart_source, projection, mem_preimage] using hp
  have hnear : ∀ᶠ t in 𝓝[J] z.2, (⟨γ t,V t⟩ : Phase S) ∈ d.source :=
    (hV.1 z.2 hz).preimage_mem_nhdsWithin (d.open_source.mem_nhds hsource)
  have hsnd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) (𝓝[univ ×ˢ J] z) (𝓝[J] z.2) :=
    continuous_snd.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun w hw => hw.2)
  refine ⟨e, he, hp, fun w => scalePhaseCoordinates (S := S) w.1 (x w.2),
    scalePhaseCoordinates_smooth.contDiffAt.comp z
      (contDiffAt_fst.prodMk (hx.comp z contDiffAt_snd)), ?_, ?_⟩
  · change scalePhaseCoordinates (S := S) z.1 (x z.2) = _
    rw [hxt, scaled_chart e he _ hp]
  · filter_upwards [hsnd.eventually hnear, heq.comp_tendsto hsnd] with w hw hxe
    have hpw : γ w.2 ∈ e.source := by
      simpa only [d, (tangentStructure S).chart_source, projection, mem_preimage] using hw
    simp only [Function.comp_apply] at hxe
    rw [scaled_chart e he _ hpw, hxe]

/-- The same local calculation supplies the continuity needed for compactness. -/
theorem scaled_field_continuous {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) :
    ContinuousOn (fun z : ℝ × ℝ => (⟨γ z.2, z.1 • V z.2⟩ : Phase S))
      (univ ×ˢ J) := by
  intro z hz
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := scaled_field_germ hV hz.2
  let d := (tangentStructure S).chart e he
  let H : ℝ × ℝ → Phase S := fun w => ⟨γ w.2, w.1 • V w.2⟩
  have hsource : H z ∈ d.source := by
    simpa only [d, H, (tangentStructure S).chart_source, projection, mem_preimage] using hp
  have hcoord : ContinuousWithinAt (fun w => (d (H w)).val) (univ ×ˢ J) z := by
    apply hx.continuousAt.continuousWithinAt.congr_of_eventuallyEq heq
    exact hxt.symm
  have hmodel : ContinuousWithinAt (fun w => d (H w)) (univ ×ˢ J) z :=
    tendsto_subtype_rng.mpr hcoord
  have hback := (d.continuousAt_symm (d.map_source hsource)).tendsto.comp hmodel
  have hsnd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) (𝓝[univ ×ˢ J] z) (𝓝[J] z.2) :=
    continuous_snd.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun w hw => hw.2)
  have hnear : ∀ᶠ t in 𝓝[J] z.2, (⟨γ t,V t⟩ : Phase S) ∈ d.source :=
    (hV.1 z.2 hz.2).preimage_mem_nhdsWithin (d.open_source.mem_nhds (by
      simpa only [d, (tangentStructure S).chart_source, projection, mem_preimage] using hp))
  rw [d.left_inv hsource] at hback
  apply hback.congr'
  filter_upwards [hsnd.eventually hnear] with w hw
  have hpw : γ w.2 ∈ e.source := by
    simpa only [d, (tangentStructure S).chart_source, projection, mem_preimage] using hw
  exact d.left_inv (by
    simpa only [d, H, (tangentStructure S).chart_source, projection, mem_preimage] using hpw)

/-- Multiplication by a smooth scalar preserves smooth intrinsic fields on
closed parameter sets, without an extension of the base curve. -/
theorem smooth_field_smul {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    SmoothFieldAlongOn S γ (fun t => φ t • V t) J := by
  refine ⟨(scaled_field_continuous hV).comp
    (hφ.continuous.continuousOn.prodMk continuousOn_id)
    (fun t ht => ⟨mem_univ _, ht⟩), ?_⟩
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ :=
    scaled_field_germ hV (z := (φ t,t)) ht
  have hmap : Tendsto (fun r : ℝ => (φ r,r)) (𝓝[J] t)
      (𝓝[univ ×ˢ J] (φ t,t)) :=
    (hφ.continuous.continuousAt.prodMk continuousAt_id).continuousWithinAt.tendsto_nhdsWithin
      (fun r hr => ⟨mem_univ _, hr⟩)
  have harg : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => (φ r,r)) t :=
    hφ.contDiffAt.prodMk contDiffAt_id
  have hcomp := hx.comp t (f := fun r : ℝ => (φ r,r)) harg
  exact ⟨e, he, hp, fun r => x (φ r,r), hcomp, hxt, heq.comp_tendsto hmap⟩

/-- The base curve of a smooth intrinsic field is continuous on the same set. -/
theorem smooth_field_base_continuous {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) : ContinuousOn γ J := by
  intro t ht
  have hc : ContinuousAt (projection S) (⟨γ t,V t⟩ : Phase S) :=
    (SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S)
      ⟨γ t,V t⟩).1
  have hcomp : ContinuousWithinAt ((projection S) ∘
      (fun r => (⟨γ r,V r⟩ : Phase S))) J t :=
    hc.comp_continuousWithinAt (f := fun r => (⟨γ r,V r⟩ : Phase S)) (hV.1 t ht)
  exact hcomp

/-- Tangent-chart smooth germs contain the base curve's coordinate germs. -/
theorem smooth_field_base_c1 {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) : CoordinateC1On S γ J := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hV.2 t ht
  let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
  let y : ℝ → Euclidean n := fun r => (L.symm (x r)).1
  have hnear : ∀ᶠ r in 𝓝[J] t, γ r ∈ e.source :=
    (smooth_field_base_continuous hV t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp)
  have hcoords : (fun r => (e (γ r)).val) =ᶠ[𝓝[J] t] y := by
    filter_upwards [hnear, heq] with r hr hxr
    dsimp only [y]
    rw [← hxr, (tangentStructure S).chart_apply e he _ hr]
    simp [L]
  exact ⟨e, he, hp, y,
    ((L.symm.contDiff.contDiffAt.comp t hx).fst).of_le (by simp),
    (hcoords.self_of_nhdsWithin ht).symm, hcoords⟩

/-- Smooth intrinsic tangent germs give the actual frame-based C¹ regularity
used in the covariant derivative interface. -/
theorem smooth_field_c1 {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) :
    C1FieldOn (B := tangentBundle S) γ V J := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hV.2 t ht
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
  let y : ℝ → Euclidean n := fun r => (L.symm (x r)).2
  have hU : IsOpen ((tangentBundle S).baseSet i) :=
    (tangentBundle S).trivialization_baseSet i ▸
      ((tangentBundle S).trivialization i).open_baseSet
  have hi : γ t ∈ (tangentBundle S).baseSet i :=
    (tangentRealization S).baseSet i ▸ hp
  have hnear : ∀ᶠ r in 𝓝[J] t, γ r ∈ e.source :=
    (smooth_field_base_continuous hV t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp)
  have hcoords : coefficientsAlong b γ V =ᶠ[𝓝[J] t] y := by
    filter_upwards [hnear, heq] with r hr hxr
    have hir : γ r ∈ (tangentBundle S).baseSet i :=
      (tangentRealization S).baseSet i ▸ hr
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hir,
      FirstVariation.tangentFrame_coordinates e he (γ r) hr]
    dsimp only [y]
    rw [← hxr, (tangentStructure S).chart_apply e he _ hr]
    simp [L]
  exact ⟨_, hU, b, hi, y,
    ((L.symm.contDiff.contDiffAt.comp t hx).snd).of_le (by simp),
    hcoords.self_of_nhdsWithin ht, hcoords⟩

/-- Metric pairings of smooth intrinsic fields are continuous up to the
endpoints, with no claim about their off-set representatives. -/
theorem smooth_fields_pairing_continuous (g : RiemannianMetric S) {γ : ℝ → M}
    {V W : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) (hW : SmoothFieldAlongOn S γ W J) :
    ContinuousOn (fun t => pairing g (γ t) (V t) (W t)) J := by
  intro t ht
  obtain ⟨y, hy, heq⟩ := FirstVariation.metric_pairing_c1_extension (tangentBundle S) g
    (smooth_field_base_c1 hV) (smooth_field_base_continuous hV) ht
    (smooth_field_c1 hV) (smooth_field_c1 hW)
  exact hy.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem heq ht

/-- Testing a smooth field against all smooth scalar multiples of itself
detects zero in every original tangent fiber, including at the endpoints. -/
theorem smooth_field_fundamental_lemma (g : RiemannianMetric S) {γ : ℝ → M}
    {A : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ} (hab : a < b)
    (hA : SmoothFieldAlongOn S γ A (Icc a b))
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t in a..b, pairing g (γ t) (φ t • A t) (A t)) = 0) :
    ∀ t ∈ Icc a b, A t = 0 := by
  have hzero : ∀ t ∈ Icc a b, pairing g (γ t) (A t) (A t) = 0 := by
    apply scalar_fundamental_lemma hab (smooth_fields_pairing_continuous g hA hA)
    intro φ hφ hc hs
    simpa only [pairing, map_smul, LinearMap.smul_apply, smul_eq_mul] using
      htest φ hφ hc hs
  intro t ht
  by_contra hne
  exact (ne_of_gt (g.positive (γ t) (A t) hne)) (hzero t ht)

/-- Compose scaled tangent-coordinate germs with the actual smooth exponential map. -/
theorem exponential_field_smooth
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace S (γ t)} {a b ε : ℝ}
    (hV : SmoothFieldAlongOn S γ V (Icc a b))
    (hdom : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Icc a b,
      (⟨γ t, s • V t⟩ : Phase S) ∈ exponentialDomain F) :
    SmoothVariationOn S (fun z : ℝ × ℝ => fiberExponential F (γ z.2) (z.1 • V z.2))
      ε a b := by
  let A : ℝ × ℝ → Phase S := fun z => ⟨γ z.2, z.1 • V z.2⟩
  let D : Set (ℝ × ℝ) := Ioo (-ε) ε ×ˢ Icc a b
  have hAc : ContinuousOn A D :=
    (scaled_field_continuous hV).mono (by intro z hz; exact ⟨mem_univ _, hz.2⟩)
  have hE := ExponentialNormalCoordinates.exponential_smooth C F hF
  have hDc (z : ℝ × ℝ) (hz : z ∈ D) : A z ∈ exponentialDomain F :=
    hdom z.1 hz.1 z.2 hz.2
  refine ⟨?_, ?_⟩
  · intro z hz
    exact (hE (A z) (hDc z hz)).1.comp_continuousWithinAt (hAc z hz)
  · intro z hz
    obtain ⟨e, he, hp, x, hx, hxz, hxeq⟩ := scaled_field_germ hV hz.2
    let d := (tangentStructure S).chart e he
    have hd := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
    have hsrc : A z ∈ d.source := by
      simpa only [d, A, (tangentStructure S).chart_source, projection, mem_preimage] using hp
    obtain ⟨c, hc, hcs⟩ := S.smoothStructure.property.1.1 (exponential F (A z))
    obtain ⟨U, hU, hzU, G, hG, hrep⟩ :=
      (hE (A z) (hDc z hz)).2 d hd c hc hsrc hcs
    refine ⟨c, hc, hcs, fun w => G (x w), ?_, ?_, ?_⟩
    · exact (hG.contDiffAt (hU.mem_nhds (by simpa only [hxz] using hzU))).comp z hx
    · have hrepz := hrep.self_of_nhds
      simpa only [hxz, A, d, Function.comp_def, fiberExponential] using hrepz
    · have hxeqD := hxeq.filter_mono (nhdsWithin_mono z
        (show D ⊆ univ ×ˢ Icc a b from fun w hw => ⟨mem_univ _, hw.2⟩))
      filter_upwards [hrep.comp_tendsto (hAc z hz), hxeqD] with w hw hwx
      simpa only [← hwx, A, d, Function.comp_def, fiberExponential] using hw.symm

/-- Every prescribed smooth intrinsic field is realized on a compact parameter strip. -/
theorem realize_smooth_field :
    P202Specs.Geometry.GeodesicCriticalityCorners.realize_smooth_fieldType.{u} := by
  intro n M _ S C γ V a b hV
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨δ, hδ, hdom⟩ := uniform_exponential_domain C F hF γ V a b
    (scaled_field_continuous hV)
  let H : ℝ × ℝ → M := fun z => fiberExponential F (γ z.2) (z.1 • V z.2)
  have hbase (t : ℝ) : H (0,t) = γ t := by
    simpa only [H, zero_smul] using
      (ExponentialNormalCoordinates.zero_section S C F hF (γ t)).2
  refine ⟨δ, hδ, H, ?_, ?_, ?_⟩
  · exact exponential_field_smooth C F hF hV
      (fun s hs t ht => hdom s ⟨le_of_lt hs.1, le_of_lt hs.2⟩ t ht)
  · intro t
    exact ⟨hbase t, exponential_ray_velocity C F hF (γ t) (V t)⟩
  · intro hVa hVb s hs
    constructor
    · rw [hbase]
      simpa only [H, hVa, smul_zero] using
        (ExponentialNormalCoordinates.zero_section S C F hF (γ a)).2
    · rw [hbase]
      simpa only [H, hVb, smul_zero] using
        (ExponentialNormalCoordinates.zero_section S C F hF (γ b)).2

/-- A single exponential variation simultaneously realizes a field smooth on
finitely many compact pieces, including at their joins. -/
theorem realize_finite_piecewise_field
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : Connection (tangentBundle S))
    (γ : ℝ → M) (V : (t : ℝ) → TangentSpace S (γ t))
    (left right : ι → ℝ)
    (hV : ∀ i, SmoothFieldAlongOn S γ V (Icc (left i) (right i))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : ℝ × ℝ → M,
      (∀ i, SmoothVariationOn S H ε (left i) (right i)) ∧
      (∀ t : ℝ, H (0,t) = γ t ∧ HEq (variationField S H t) (V t)) ∧
      (∀ a b : ℝ, V a = 0 → V b = 0 → EndpointFixed H ε a b) := by
  classical
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  have hδ (i : ι) : ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc (-δ) δ, ∀ t ∈ Icc (left i) (right i),
        (⟨γ t, s • V t⟩ : Phase S) ∈ exponentialDomain F :=
    uniform_exponential_domain C F hF γ V (left i) (right i)
      (scaled_field_continuous (hV i))
  choose δ hδpos hδdom using hδ
  let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hε : 0 < ε := (Finset.lt_inf'_iff _).mpr (fun i _ => hδpos i)
  have hεδ (i : ι) : ε ≤ δ i := Finset.inf'_le _ (Finset.mem_univ i)
  let H : ℝ × ℝ → M := fun z => fiberExponential F (γ z.2) (z.1 • V z.2)
  have hbase (t : ℝ) : H (0,t) = γ t := by
    simpa only [H, zero_smul] using
      (ExponentialNormalCoordinates.zero_section S C F hF (γ t)).2
  refine ⟨ε, hε, H, ?_, ?_, ?_⟩
  · intro i
    exact exponential_field_smooth C F hF (hV i) (fun s hs t ht =>
      hδdom i s ⟨(neg_le_neg (hεδ i)).trans (le_of_lt hs.1),
        (le_of_lt hs.2).trans (hεδ i)⟩ t ht)
  · intro t
    exact ⟨hbase t, exponential_ray_velocity C F hF (γ t) (V t)⟩
  · intro a b hVa hVb s hs
    constructor
    · rw [hbase]
      simpa only [H, hVa, smul_zero] using
        (ExponentialNormalCoordinates.zero_section S C F hF (γ a)).2
    · rw [hbase]
      simpa only [H, hVb, smul_zero] using
        (ExponentialNormalCoordinates.zero_section S C F hF (γ b)).2

end Realization

end P202.Geometry.GeodesicCriticalityCorners

open Set Filter MeasureTheory
open scoped Topology
namespace P202.Geometry.GeodesicCriticalityCorners
open P202.CriticalityData
theorem strictMono_arcParameter {v : ℝ → ℝ} {a b : ℝ}
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t) :
    StrictMonoOn (arcParameter v a) (Icc a b) := by
  intro x hx y hy hxy
  have hxyc : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have haix := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hx.1 (hv.mono (Icc_subset_Icc le_rfl hx.2))
  have haiy := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hy.1 (hv.mono (Icc_subset_Icc le_rfl hy.2))
  have hp : 0 < ∫ r in x..y, v r := intervalIntegral.integral_pos hxy
    (hv.mono hxyc) (fun r hr => le_of_lt (hpos r (hxyc (Ioc_subset_Icc_self hr))))
    ⟨x, left_mem_Icc.mpr hxy.le, hpos x hx⟩
  dsimp [arcParameter]
  linarith [intervalIntegral.integral_interval_sub_left haiy haix]

theorem continuousOn_arcParameter {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) : ContinuousOn (arcParameter v a) (Icc a b) := by
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hv
  change ContinuousOn (fun t => ∫ r in a..t, v r) (Icc a b)
  simpa only [uIcc_of_le hab] using
    intervalIntegral.continuousOn_primitive_interval' hi (show a ∈ uIcc a b from left_mem_uIcc)

theorem hasDerivWithinAt_arcParameter {v : ℝ → ℝ} {a b t : ℝ}
    (hv : ContinuousOn v (Icc a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (arcParameter v a) (v t) (Icc a b) t := by
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  apply intervalIntegral.integral_hasDerivWithinAt_right
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ht.1 (hv.mono (Icc_subset_Icc le_rfl ht.2)))
    (hv.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hv t ht)

theorem HasDerivWithinAt.of_local_inverse {f g : ℝ → ℝ} {d x : ℝ} {J I : Set ℝ}
    (hg : Tendsto g (𝓝[I] x) (𝓝[J] g x))
    (hf : HasDerivWithinAt f d J (g x)) (hd : d ≠ 0) (hx : x ∈ I)
    (hfg : ∀ᶠ y in 𝓝[I] x, f (g y) = y) :
    HasDerivWithinAt g d⁻¹ I x := by
  have H := hf.hasFDerivWithinAt.of_comp_of_leftInverse
    (f'symm := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹) hg
    (hasFDerivWithinAt_id x I) hfg (by intro z; simp [hd]) hx
  convert H.hasDerivWithinAt using 1
  simp

/-- The genuine accumulated-speed integral has a continuous inverse, including
one-sided endpoint derivative rules. -/
theorem arcParameter_inverse {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t) :
    ∃ τ : ℝ → ℝ,
      Continuous τ ∧
      MapsTo τ (Icc 0 (arcParameter v a b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (arcParameter v a t) = t) ∧
      (∀ s ∈ Icc 0 (arcParameter v a b), arcParameter v a (τ s) = s) ∧
      (∀ s ∈ Icc 0 (arcParameter v a b),
        HasDerivWithinAt τ (v (τ s))⁻¹ (Icc 0 (arcParameter v a b)) s) := by
  let σ := arcParameter v a
  have hmono : StrictMonoOn σ (Icc a b) := strictMono_arcParameter hv hpos
  have hσ : ContinuousOn σ (Icc a b) := continuousOn_arcParameter hab.le hv
  have hσa : σ a = 0 := by simp [σ, arcParameter]
  have hL : 0 < σ b := by
    simpa only [hσa] using hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have himage : σ '' Icc a b = Icc 0 (σ b) := by
    simpa only [hσa] using hσ.image_Icc_of_monotoneOn hab.le hmono.monotoneOn
  let e : Icc a b ≃o Icc 0 (σ b) :=
    (hmono.orderIso σ (Icc a b)).trans (Set.orderIsoOfEq _ _ himage)
  have he : ∀ t : Icc a b, (e t).val = σ t.val := by intro t; rfl
  let τ : ℝ → ℝ := fun s => (e.symm (projIcc 0 (σ b) hL.le s)).val
  have hτ : Continuous τ := continuous_subtype_val.comp
    (e.symm.toHomeomorph.continuous.comp continuous_projIcc)
  have hτmap : MapsTo τ (Icc 0 (σ b)) (Icc a b) := by
    intro s hs; exact (e.symm _).property
  have hτσ : ∀ t ∈ Icc a b, τ (σ t) = t := by
    intro t ht
    have hst : σ t ∈ Icc 0 (σ b) := by rw [← himage]; exact mem_image_of_mem σ ht
    change (e.symm (projIcc 0 (σ b) hL.le (σ t))).val = t
    rw [projIcc_of_mem hL.le hst]
    change (e.symm (e ⟨t,ht⟩)).val = t
    rw [e.symm_apply_apply]
  have hστ : ∀ s ∈ Icc 0 (σ b), σ (τ s) = s := by
    intro s hs
    change σ (e.symm (projIcc 0 (σ b) hL.le s)).val = s
    rw [← he, e.apply_symm_apply, projIcc_of_mem hL.le hs]
  refine ⟨τ, hτ, hτmap, hτσ, hστ, ?_⟩
  intro s hs
  apply HasDerivWithinAt.of_local_inverse
    (hτ.continuousAt.continuousWithinAt.tendsto_nhdsWithin hτmap)
    (hasDerivWithinAt_arcParameter hv (hτmap hs)) (ne_of_gt (hpos _ (hτmap hs))) hs
  exact eventually_nhdsWithin_of_forall hστ
end P202.Geometry.GeodesicCriticalityCorners

open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveData P202.CurveConnectionData
open Set Filter
open scoped Topology
namespace P202.Geometry.GeodesicCriticalityCorners
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

theorem normalized_velocity_reparam (g : RiemannianMetric S)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace S (γ t)}
    {τ : ℝ → ℝ} {I J : Set ℝ} {s : ℝ}
    (hV : HasVelocityWithinAt S γ J (τ s) (V (τ s)))
    (hτ : HasDerivWithinAt τ (tangentNorm g (γ (τ s)) (V (τ s)))⁻¹ I s)
    (hmap : MapsTo τ I J) :
    HasVelocityWithinAt S (γ ∘ τ) I s
      ((tangentNorm g (γ (τ s)) (V (τ s)))⁻¹ • V (τ s)) :=
  P202.Geometry.CurveCovariantDerivative.velocity_reparam hV hτ hmap

theorem normalized_norm (g : RiemannianMetric S) (p : M) (V : TangentSpace S p)
    (hpos : 0 < tangentNorm g p V) :
    tangentNorm g p ((tangentNorm g p V)⁻¹ • V) = 1 := by
  rw [P202.Geometry.SmoothMetrics.tangentNorm_smul, abs_of_pos (inv_pos.mpr hpos),
    inv_mul_cancel₀ (ne_of_gt hpos)]

theorem derivative_zero_reparam_iff
    (C : Connection (tangentBundle S))
    {γ : ℝ → M} {U : (t : ℝ) → TangentSpace S (γ t)}
    {τ : ℝ → ℝ} {I J : Set ℝ} {s k : ℝ}
    (hs : s ∈ I) (hI : UniqueDiffWithinAt ℝ I s)
    (hτ : HasDerivWithinAt τ k I s) (hmap : MapsTo τ I J) (hk : k ≠ 0)
    (hex : ∃ D, HasCovariantDerivativeWithinAt C γ U J (τ s) D) :
    HasCovariantDerivativeWithinAt C γ U J (τ s) 0 ↔
      HasCovariantDerivativeWithinAt C (γ ∘ τ) (fun s => U (τ s)) I s 0 := by
  constructor
  · intro h
    simpa only [smul_zero] using
      P202.Geometry.CurveCovariantDerivative.derivative_reparam C h hτ hmap
  · intro h
    obtain ⟨D, hD⟩ := hex
    have hd := P202.Geometry.CurveCovariantDerivative.derivative_reparam C hD hτ hmap
    have heq := P202.Geometry.CurveCovariantDerivative.covariantDerivative_unique C hs hI hd h
    have hD0 : D = 0 := (smul_eq_zero.mp heq).resolve_left hk
    simpa only [hD0] using hD

theorem HasVelocityWithinAt.ordinary_of_mem_nhds
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {V : TangentSpace S (γ t)}
    (hV : HasVelocityWithinAt S γ J t V) (hJ : J ∈ 𝓝 t) :
    HasVelocityWithinAt S γ univ t V := by
  obtain ⟨hc,e,he,hp,hd⟩ := hV
  exact ⟨(hc.continuousAt hJ).continuousWithinAt,e,he,hp,
    (hd.hasDerivAt hJ).hasDerivWithinAt⟩

theorem HasCovariantDerivativeWithinAt.ordinary_of_mem_nhds
    (C : Connection (tangentBundle S))
    {γ : ℝ → M} {U : (t : ℝ) → TangentSpace S (γ t)}
    {J : Set ℝ} {t : ℝ} {D : TangentSpace S (γ t)}
    (hD : HasCovariantDerivativeWithinAt C γ U J t D) (hJ : J ∈ 𝓝 t) :
    HasCovariantDerivativeAt C γ U t D := by
  obtain ⟨V,hV,W,hW,b,hp,v',hd,hDeq⟩ := hD
  exact ⟨V,HasVelocityWithinAt.ordinary_of_mem_nhds hV hJ,W,hW,b,hp,v',
    (hd.hasDerivAt hJ).hasDerivWithinAt,hDeq⟩
end P202.Geometry.GeodesicCriticalityCorners
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveData P202.CurveConnectionData
  P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

theorem segmentSpeed_continuousOn (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b) :
    ContinuousOn (fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) (Icc a b) := by
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε,hε⟩
  have hf := FirstVariation.segmentVelocity_c1 hF hε hab
  intro t ht
  obtain ⟨y,hy,heq⟩ := FirstVariation.metric_pairing_c1_extension
    (tangentBundle S) g (FirstVariation.variation_coordinateC1On_slice hF h0)
    (FirstVariation.variation_continuousOn_slice hF h0) ht hf hf
  have hc : ContinuousWithinAt (fun t => Real.sqrt (y t)) (Icc a b) t :=
    hy.continuousAt.sqrt.continuousWithinAt
  apply hc.congr_of_eventuallyEq
  · filter_upwards [heq] with s hs
    simp only [tangentNorm, pairing, hs]
  · simp only [tangentNorm, pairing, heq.self_of_nhdsWithin ht]

theorem regular_arc_length_parameterization (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) :
    let v := fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)
    let σ := arcParameter v a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), HasDerivWithinAt τ (v (τ s))⁻¹ (Icc 0 (σ b)) s) ∧
      (∀ s ∈ Icc 0 (σ b), HasVelocityWithinAt S (fun r => F (0,τ r))
        (Icc 0 (σ b)) s (unitVelocity g F a b (τ s))) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (F (0,τ s)) (unitVelocity g F a b (τ s)) = 1) ∧
      (∀ C : Connection (tangentBundle S),
        (∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
          (unitVelocity g F a b) (Icc a b) t 0) ↔
        (∀ s ∈ Icc 0 (σ b), HasCovariantDerivativeWithinAt C (fun r => F (0,τ r))
          (fun r => unitVelocity g F a b (τ r)) (Icc 0 (σ b)) s 0)) := by
  dsimp only
  let v := fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)
  let σ := arcParameter v a
  have hv := segmentSpeed_continuousOn g hF hε hab
  have hmono : StrictMonoOn σ (Icc a b) := strictMono_arcParameter hv hpos
  have hσa : σ a = 0 := by simp [σ,arcParameter]
  have hL : 0 < σ b := by
    simpa only [hσa] using hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  obtain ⟨τ,hτ,hτmap,hτσ,hστ,hdτ⟩ := arcParameter_inverse hab hv hpos
  have hσmap : MapsTo σ (Icc a b) (Icc 0 (σ b)) := by
    intro t ht
    exact ⟨by simpa only [hσa] using hmono.monotoneOn (left_mem_Icc.mpr hab.le) ht ht.1,
      hmono.monotoneOn ht (right_mem_Icc.mpr hab.le) ht.2⟩
  refine ⟨τ,hτ,hτmap,hτσ,hστ,hdτ,?_,?_,?_⟩
  · intro s hs
    exact normalized_velocity_reparam g (FirstVariation.segmentVelocity_spec hF hε (hτmap hs))
      (hdτ s hs) hτmap
  · intro s hs
    exact normalized_norm g _ _ (hpos _ (hτmap hs))
  · intro C
    have hequiv : ∀ s ∈ Icc 0 (σ b),
        HasCovariantDerivativeWithinAt C (fun r => F (0,r)) (unitVelocity g F a b)
          (Icc a b) (τ s) 0 ↔
        HasCovariantDerivativeWithinAt C (fun r => F (0,τ r))
          (fun r => unitVelocity g F a b (τ r)) (Icc 0 (σ b)) s 0 := by
      intro s hs
      apply derivative_zero_reparam_iff C hs (uniqueDiffOn_Icc hL s hs)
        (hdτ s hs) hτmap (inv_ne_zero (ne_of_gt (hpos _ (hτmap hs))))
      exact CurveCovariantDerivative.exists_covariantDerivative C (hτmap hs)
        (FirstVariation.variation_coordinateC1On_slice hF ⟨neg_lt_zero.mpr hε,hε⟩)
        (FirstVariation.variation_continuousOn_slice hF ⟨neg_lt_zero.mpr hε,hε⟩)
        (FirstVariation.unitVelocity_c1 g hF hε hab hpos)
    constructor
    · intro h s hs
      exact (hequiv s hs).mp (h _ (hτmap hs))
    · intro h t ht
      have hh := (hequiv (σ t) (hσmap ht)).mpr (h (σ t) (hσmap ht))
      exact Eq.mp (congrArg (fun r => HasCovariantDerivativeWithinAt C
        (fun r => F (0,r)) (unitVelocity g F a b) (Icc a b) r 0) (hτσ t ht)) hh
end P202.Geometry.GeodesicCriticalityCorners
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveData P202.CurveConnectionData
  P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

theorem segment_arcLength_eq_variedLength (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a ≤ b) :
    arcParameter (fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) a b =
      variedLength g F a b 0 := by
  unfold arcParameter variedLength
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  dsimp only
  rw [FirstVariation.segmentVelocity_eq_velocity hF hε ht]
  rfl

theorem geodesicOn_of_closed_interval
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {a b : ℝ}
    (hV : ∀ t ∈ Icc a b, HasVelocityWithinAt S (fun r => (q r).1)
      (Icc a b) t (q t).2)
    (hD : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => (q r).1)
      (fun r => (q r).2) (Icc a b) t 0) :
    IsGeodesicOn S C (Ioo a b) q := by
  intro t ht
  exact ⟨HasVelocityWithinAt.ordinary_of_mem_nhds (hV t (Ioo_subset_Icc_self ht))
    (Icc_mem_nhds ht.1 ht.2),
    HasCovariantDerivativeWithinAt.ordinary_of_mem_nhds C (hD t (Ioo_subset_Icc_self ht))
      (Icc_mem_nhds ht.1 ht.2)⟩

theorem regular_arc_length_geodesic
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t))
    (hpar : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
      (unitVelocity g F a b) (Icc a b) t 0) :
    let σ := arcParameter (fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (F (0,τ s)) (unitVelocity g F a b (τ s)) = 1) ∧
      IsGeodesicOn S C (Ioo 0 (σ b))
        (fun s => (⟨F (0,τ s), unitVelocity g F a b (τ s)⟩ : Phase S)) := by
  obtain ⟨τ,hτ,hmap,hτσ,hστ,hd,hvel,hnorm,hequiv⟩ :=
    regular_arc_length_parameterization g hF hε hab hpos
  refine ⟨τ,hτ,hmap,hτσ,hστ,hnorm,?_⟩
  apply geodesicOn_of_closed_interval C hvel
  exact (hequiv C).mp hpar
end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.GeodesicData P202.CriticalityData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

theorem length_nonneg (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) : 0 ≤ length g c :=
  intervalIntegral.integral_nonneg_of_forall c.ordered
    (fun t => P202.Geometry.SmoothMetrics.tangentNorm_nonneg g (c t) _)

theorem endpointLengths_bddBelow (g : RiemannianMetric S) (p q : M) :
    BddBelow (endpointLengths g p q) := by
  refine ⟨0, ?_⟩
  rintro L ⟨a,b,c,_hp,_hq,rfl⟩
  exact length_nonneg g c

theorem endpointDistance_le_length (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) :
    endpointDistance g (c a) (c b) ≤ length g c :=
  csInf_le (endpointLengths_bddBelow g _ _) ⟨a,b,c,rfl,rfl,rfl⟩

/-- Equality to the source length infimum implies minimum among all actual
piecewise C1 competitors, even with different compact parameter intervals. -/
theorem minimizing_of_length_eq_distance (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (hmin : length g c = endpointDistance g (c a) (c b))
    {l r : ℝ} (d : PiecewiseC1Curve S l r)
    (hp : d l = c a) (hq : d r = c b) : length g c ≤ length g d := by
  rw [hmin, ← hp, ← hq]
  exact endpointDistance_le_length g d

/-- Every finite piecewise smooth variation slice is an admissible original
curve competitor with exactly the varied length and exactly the endpoints. -/
theorem piecewise_variation_competitor
    (g : RiemannianMetric S) {F : ℝ × ℝ → M} {ε s : ℝ}
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : Monotone node)
    (hF : ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ))
    (hs : s ∈ Ioo (-ε) ε) :
    ∃ c : PiecewiseC1Curve S (node 0) (node (Fin.last (k+1))),
      c (node 0) = F (s,node 0) ∧
      c (node (Fin.last (k+1))) = F (s,node (Fin.last (k+1))) ∧
      length g c = variedLength g F (node 0) (node (Fin.last (k+1))) s := by
  let pieces := fun i : Fin (k+1) => P202.Geometry.FirstVariation.variationSlice
    (hF i) hs (hnode (Fin.castSucc_le_succ i))
  obtain ⟨c,hp,hq,_hpieces,hL⟩ :=
    P202.Geometry.LengthLaws.finiteConcatenation_length g node
      (fun j => F (s,node j)) pieces (fun _ => rfl) (fun _ => rfl)
  refine ⟨c,hp,hq,?_⟩
  rw [hL, (P202.Geometry.FirstVariation.varied_functionals_subdivision g node hnode hF hs).2]
  rfl

/-- Source distance equality automatically gives the local minimum used by
first variation. There is no separately assumed variation-minimum certificate. -/
theorem piecewise_variation_localMin_of_distance
    (g : RiemannianMetric S) {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : Monotone node)
    (hF : ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ))
    (hfix : ∀ s ∈ Ioo (-ε) ε,
      F (s,node 0) = F (0,node 0) ∧
      F (s,node (Fin.last (k+1))) = F (0,node (Fin.last (k+1))))
    (hmin : variedLength g F (node 0) (node (Fin.last (k+1))) 0 =
      endpointDistance g (F (0,node 0)) (F (0,node (Fin.last (k+1))))) :
    IsLocalMin (variedLength g F (node 0) (node (Fin.last (k+1)))) 0 := by
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hε) hε] with s hs
  obtain ⟨c,hp,hq,hL⟩ := piecewise_variation_competitor g node hnode hF hs
  rw [hmin, ← hL, ← (hfix s hs).1, ← (hfix s hs).2, ← hp, ← hq]
  exact endpointDistance_le_length g c

section Gluing
variable {S : SmoothManifold n .euclidean M}

/-- Equal positions and tangent vectors at a join glue two intrinsic geodesics
into one smooth geodesic on an open interval containing both original domains.
The pieces are only constrained on their actual open domains. -/
theorem geodesic_gluing
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C)
    (I J : D13Unified.OpenTimeInterval) (q r : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (hr : IsGeodesicOn S C J.carrier r)
    (c : ℝ) (hc : c ∈ I.carrier ∩ J.carrier) (hjoin : q c = r c) :
    ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      I.carrier ∪ J.carrier ⊆ K.carrier ∧
      IsGeodesicOn S C K.carrier z ∧
      EqOn z q I.carrier ∧ EqOn z r J.carrier ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source →
        ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (z s)).val) t := by
  obtain ⟨A,Q,hQ⟩ := P202.Geometry.GeodesicIVP.maximal_exists S g C hC (q c)
  let I' := P202.Geometry.GeodesicIVP.affineInterval I 1 c one_ne_zero
  let J' := P202.Geometry.GeodesicIVP.affineInterval J 1 c one_ne_zero
  have hI0 : 0 ∈ I'.carrier := by simpa [I', P202.Geometry.GeodesicIVP.affineInterval, affineDomain] using hc.1
  have hJ0 : 0 ∈ J'.carrier := by simpa [J', P202.Geometry.GeodesicIVP.affineInterval, affineDomain] using hc.2
  have hq0 : affineCurve S q 1 c 0 = q c := by simp [affineCurve]
  have hr0 : affineCurve S r 1 c 0 = q c := by simpa [affineCurve] using hjoin.symm
  have hq' := hQ.2.2.2 I' (affineCurve S q 1 c) hI0 hq0
    (P202.Geometry.GeodesicIVP.geodesic_affine C 1 c hq)
  have hr' := hQ.2.2.2 J' (affineCurve S r 1 c) hJ0 hr0
    (P202.Geometry.GeodesicIVP.geodesic_affine C 1 c hr)
  let K := P202.Geometry.GeodesicIVP.affineInterval A 1 (-c) one_ne_zero
  let z := affineCurve S Q 1 (-c)
  have hqtime {t : ℝ} (ht : t ∈ I.carrier) : t - c ∈ I'.carrier := by
    simpa [I', P202.Geometry.GeodesicIVP.affineInterval, affineDomain] using ht
  have hrtime {t : ℝ} (ht : t ∈ J.carrier) : t - c ∈ J'.carrier := by
    simpa [J', P202.Geometry.GeodesicIVP.affineInterval, affineDomain] using ht
  have hz : IsGeodesicOn S C K.carrier z :=
    P202.Geometry.GeodesicIVP.geodesic_affine C 1 (-c) hQ.2.2.1
  refine ⟨K,z,?_,hz,?_,?_,?_⟩
  · intro t ht
    change 1 * t + -c ∈ A.carrier
    rcases ht with ht | ht
    · simpa [sub_eq_add_neg] using hq'.1 (hqtime ht)
    · simpa [sub_eq_add_neg] using hr'.1 (hrtime ht)
  · intro t ht
    simpa [z, affineCurve, sub_eq_add_neg, add_assoc] using hq'.2 (hqtime ht)
  · intro t ht
    simpa [z, affineCurve, sub_eq_add_neg, add_assoc] using hr'.2 (hrtime ht)
  · obtain ⟨G,_hG,hbridge⟩ := P202.Geometry.GeodesicIVP.spray_exists S C
    intro t ht e he hp
    exact (((hbridge K z).mpr hz).2 t ht e he hp).1

end Gluing
end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.VectorFieldData
  SmoothManifolds.MapData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.FirstVariationData P202.CriticalityData P202.GeodesicData P202.ExponentialData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}
/-- Genuine global smooth vectorfields restrict to smooth fields along an
arbitrary smooth curve with only one-sided coordinate germs at endpoints. -/
theorem smoothField_along_curve
    (X : SmoothField (tangentStructure S)) {γ : ℝ → M} {J : Set ℝ}
    (hγ : SmoothCurveOn (S := S) γ J) :
    SmoothFieldAlongOn S γ (fun t => X.val (γ t)) J := by
  constructor
  · intro t ht
    exact (X.smooth (γ t)).1.comp_continuousWithinAt (f := γ) (hγ.1 t ht)
  · intro t ht
    obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hγ.2 t ht
    let d := (tangentStructure S).chart e he
    have hd : d ∈ (tangentStructure S).manifold.smoothStructure.val :=
      SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
    have hsource : (⟨γ t,X.val (γ t)⟩ : Phase S) ∈ d.source := by
      simpa only [d,(tangentStructure S).chart_source,projection,mem_preimage] using hp
    obtain ⟨U,hU,hpU,G,hG,hrep⟩ :=
      (X.smooth (γ t)).2 e he d hd hp hsource
    have hpU' : x t ∈ U := by rwa [hxt]
    have hrep' := hrep.comp_tendsto (hγ.1 t ht)
    refine ⟨e,he,hp,fun r => G (x r),
      (hG.contDiffAt (hU.mem_nhds hpU')).comp t hx,?_,?_⟩
    · change G (x t) = (d ⟨γ t,X.val (γ t)⟩).val
      rw [hxt]
      exact hrep.self_of_nhds
    · filter_upwards [heq,hrep'] with r hyr hrepr
      change G (e (γ r)).val = (d ⟨γ r,X.val (γ r)⟩).val at hrepr
      rw [← hyr]
      exact hrepr.symm


theorem exists_smoothField_value (p : M) (v : TangentSpace S p) :
    ∃ X : SmoothField (tangentStructure S), X.val p = v := by
  obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 p
  let L := (tangentStructure S).fiberCoordinates.equiv e he p hp
  obtain ⟨X,hX⟩ := SmoothManifolds.Frobenius.exists_field_with_coordinate_germ
    S (tangentStructure S) e he p hp univ isOpen_univ (mem_univ _)
    (fun _ => L v) contDiffOn_const
  refine ⟨X,?_⟩
  apply L.injective
  have hpX := hX.self_of_nhds
  simpa only [SmoothManifolds.LieBracketData.coefficients, hp, dite_true] using hpX

theorem maximal_position_smoothCurveOn
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (w : Phase S) {J : Set ℝ}
    (hJ : J ⊆ (F.interval w).carrier) :
    SmoothCurveOn S (fun t => (F.curve w t).1) J := by
  have hP (t : ℝ) (ht : t ∈ J) : PositionSmoothAt S F (t,w) :=
    ((GeodesicIVP.domain_open_smooth S C F hF).2 (t,w) (hJ ht)).2
  have hj (t : ℝ) : ContinuousAt (fun r : ℝ => (r,w)) t :=
    (continuous_id.prodMk continuous_const).continuousAt
  refine ⟨?_, ?_⟩
  · intro t ht
    exact ((hP t ht).1.comp (f := fun r : ℝ => (r,w)) (hj t)).continuousWithinAt
  · intro t ht
    obtain ⟨e, he, hw⟩ := (phaseManifold S).smoothStructure.property.1.1 w
    obtain ⟨d, hd, hp⟩ := S.smoothStructure.property.1.1 (F.curve w t).1
    obtain ⟨U, hU, hzU, H, hH, hrep⟩ := (hP t ht).2 e he d hd hw hp
    refine ⟨d, hd, hp, fun r => H (r, (e w).val), ?_, ?_, ?_⟩
    · exact (hH.contDiffAt (hU.mem_nhds hzU)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)
    · exact hrep.self_of_nhds
    · exact (hrep.comp_tendsto (hj t)).symm.filter_mono nhdsWithin_le_nhds

/-- The actual velocity field of a maximal geodesic is smooth in the original
tangent bundle, simultaneously with its base position. -/
theorem maximal_velocity_smoothFieldAlongOn
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (w : Phase S) {J : Set ℝ}
    (hJ : J ⊆ (F.interval w).carrier) :
    SmoothFieldAlongOn S (fun t => (F.curve w t).1)
      (fun t => (F.curve w t).2) J := by
  have hP (t : ℝ) (ht : t ∈ J) : FlowSmoothAt (phaseManifold S) F (t,w) :=
    ((GeodesicIVP.domain_open_smooth S C F hF).2 (t,w) (hJ ht)).1
  have hj (t : ℝ) : ContinuousAt (fun r : ℝ => (r,w)) t :=
    (continuous_id.prodMk continuous_const).continuousAt
  refine ⟨?_, ?_⟩
  · intro t ht
    exact ((hP t ht).1.comp (f := fun r : ℝ => (r,w)) (hj t)).continuousWithinAt
  · intro t ht
    obtain ⟨e, he, hw⟩ := (phaseManifold S).smoothStructure.property.1.1 w
    obtain ⟨d, hd, hp⟩ := S.smoothStructure.property.1.1 (F.curve w t).1
    let c := (tangentStructure S).chart d hd
    have hc := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) d hd
    have hpc : flow F (t,w) ∈ c.source := by
      simpa only [c, flow, (tangentStructure S).chart_source, projection,
        mem_preimage] using hp
    obtain ⟨U, hU, hzU, H, hH, hrep⟩ := (hP t ht).2 e he c hc hw hpc
    refine ⟨d, hd, hp, fun r => H (r, (e w).val), ?_, ?_, ?_⟩
    · exact (hH.contDiffAt (hU.mem_nhds hzU)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)
    · exact hrep.self_of_nhds
    · exact (hrep.comp_tendsto (hj t)).symm.filter_mono nhdsWithin_le_nhds

end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}
/-- An actual smooth scalar function can isolate one node of any finite
injectively placed collection. In particular it vanishes at the outer endpoints. -/
theorem exists_smooth_node_selector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hnode : Function.Injective node) (j : ι) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      ∀ i : ι, φ (node i) = if i = j then 1 else 0 := by
  classical
  let φ : ℝ → ℝ := fun t => ∏ i ∈ Finset.univ.erase j,
    ((t - node i) / (node j - node i))
  refine ⟨φ,?_,?_⟩
  · apply contDiff_prod
    intro i _hi
    exact (contDiff_id.sub contDiff_const).div_const _
  · intro i
    by_cases hij : i = j
    · subst i
      rw [ite_eq_left rfl]
      apply Finset.prod_eq_one
      intro i hi
      apply div_self
      exact sub_ne_zero.mpr (fun heq => (Finset.ne_of_mem_erase hi) (hnode heq).symm)
    · rw [ite_eq_right hij]
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ _⟩)
      simp

/-- Every prescribed join value is attained by an actual intrinsic field,
smooth on each piece and zero at all other nodes. -/
theorem exists_join_field
    {γ : ℝ → M} {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn (S := S) γ (Icc (node i.castSucc) (node i.succ)))
    (j : Fin (k+2)) (v : TangentSpace S (γ (node j))) :
    ∃ V : (t : ℝ) → TangentSpace S (γ t),
      (∀ i : Fin (k+1), SmoothFieldAlongOn S γ V (Icc (node i.castSucc) (node i.succ))) ∧
      V (node j) = v ∧ ∀ i : Fin (k+2), i ≠ j → V (node i) = 0 := by
  obtain ⟨X,hX⟩ := exists_smoothField_value (γ (node j)) v
  obtain ⟨φ,hφ,hφnode⟩ := exists_smooth_node_selector node hnode.injective j
  refine ⟨fun t => φ t • X.val (γ t),?_,?_,?_⟩
  · intro i
    exact smooth_field_smul (smoothField_along_curve X (hγ i)) hφ
  · dsimp only
    rw [hφnode j,ite_eq_left rfl,one_smul,hX]
  · intro i hij
    dsimp only
    rw [hφnode i,ite_eq_right hij,zero_smul]



/-- A distance-minimizing regular piecewise smooth curve whose actual unit
velocity is covariantly parallel on every piece has no corner. Arbitrary join
values are constructed and realized by genuine variations in the proof. -/
theorem minimizing_parallel_curve_no_corner
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (γ t)
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ) t))
    (hpar : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      HasCovariantDerivativeWithinAt C γ
        (unitVelocity g (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ))
        (Icc (node i.castSucc) (node i.succ)) t 0)
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))) :
    ∀ j : Fin k,
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.castSucc.castSucc) (node j.castSucc.succ) (node j.succ.castSucc) =
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.succ.castSucc) (node j.succ.succ) (node j.succ.castSucc) := by
  intro j
  let v := unitVelocity g (fun z : ℝ × ℝ => γ z.2)
      (node j.castSucc.castSucc) (node j.castSucc.succ) (node j.succ.castSucc) -
    unitVelocity g (fun z : ℝ × ℝ => γ z.2)
      (node j.succ.castSucc) (node j.succ.succ) (node j.succ.castSucc)
  obtain ⟨V,hV,hVj,hVother⟩ := exists_join_field node hnode hγ j.succ.castSucc v
  obtain ⟨ε,hε,H,hH,hHV,hfixed⟩ := realize_finite_piecewise_field C γ V
    (fun i : Fin (k+1) => node i.castSucc) (fun i => node i.succ) hV
  have hbasefun : (fun t => H (0,t)) = γ := funext (fun t => (hHV t).1)
  subst γ
  have hj0 : (0 : Fin (k+2)) ≠ j.succ.castSucc := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_zero,Fin.val_castSucc,Fin.val_succ] at hv
    omega
  have hjlast : Fin.last (k+1) ≠ j.succ.castSucc := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_last,Fin.val_castSucc,Fin.val_succ] at hv
    omega
  have hfix : EndpointFixed H ε (node 0) (node (Fin.last (k+1))) :=
    hfixed _ _ (hVother _ hj0) (hVother _ hjlast)
  have hlocal := piecewise_variation_localMin_of_distance g hε node hnode.monotone hH hfix hmin
  have hother : ∀ j' : Fin k, j' ≠ j → variationField S H (node j'.succ.castSucc) = 0 := by
    intro j' hne
    have hindices : j'.succ.castSucc ≠ j.succ.castSucc := by
      intro heq
      apply hne
      apply Fin.ext
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc,Fin.val_succ] at hv
      omega
    exact (eq_of_heq (hHV _).2).trans (hVother _ hindices)
  have hzero := isolated_corner_zero_of_minimum g C hC hε node hnode hH hfix
    hpos hpar hlocal j hother
  change pairing g (H (0,node j.succ.castSucc))
    (variationField S H (node j.succ.castSucc)) v = 0 at hzero
  rw [eq_of_heq (hHV _).2,hVj] at hzero
  apply sub_eq_zero.mp
  by_contra hne
  exact (ne_of_gt (g.positive _ _ hne)) hzero

end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MapData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData
  P202.GeodesicData P202.ExponentialData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The original covariant geodesic equations imply smoothness of the actual
velocity field; the spray bridge proves all smoothness obligations. -/
theorem geodesic_velocity_smoothFieldAlongOn
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {J : Set ℝ} (hJ : J ⊆ I.carrier) :
    SmoothFieldAlongOn S (fun t => (q t).1) (fun t => (q t).2) J := by
  obtain ⟨G, _, hbridge⟩ := GeodesicIVP.spray_exists S C
  have hq' := (hbridge I q).mpr hq
  refine ⟨hq'.1.mono hJ, ?_⟩
  intro t ht
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (q t).1
  let d := (tangentStructure S).chart e he
  have hd := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
  have hpd : q t ∈ d.source := by
    simpa only [d, (tangentStructure S).chart_source, projection, mem_preimage] using hp
  exact ⟨e, he, hp, fun r => (d (q r)).val, (hq'.2 t (hJ ht) d hd hpd).1,
    rfl, Filter.EventuallyEq.rfl⟩

/-- Genuine geodesic position curves have smooth ambient coordinate germs,
including at endpoints of compact subintervals of their open domain. -/
theorem geodesic_position_smoothCurveOn
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {J : Set ℝ} (hJ : J ⊆ I.carrier) :
    SmoothCurveOn S (fun t => (q t).1) J := by
  obtain ⟨G, _, hbridge⟩ := GeodesicIVP.spray_exists S C
  have hq' := (hbridge I q).mpr hq
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (hq t (hJ ht)).1.1.mono (subset_univ J)
  · intro t ht
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (q t).1
    let d := (tangentStructure S).chart e he
    have hd := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
    have hpd : q t ∈ d.source := by
      simpa only [d, (tangentStructure S).chart_source, projection, mem_preimage] using hp
    let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
    let x : ℝ → Euclidean n := fun r => (L.symm (d (q r)).val).1
    have hx : ContDiffAt ℝ (⊤ : ℕ∞) x t :=
      (L.symm.contDiff.contDiffAt.comp t (hq'.2 t (hJ ht) d hd hpd).1).fst
    have hsource : ∀ᶠ r in 𝓝 t, q r ∈ d.source :=
      (hq'.1.continuousAt (I.isOpen.mem_nhds (hJ ht))).preimage_mem_nhds
        (d.open_source.mem_nhds hpd)
    have hxcoord {r : ℝ} (hr : q r ∈ d.source) : x r = (e (q r).1).val := by
      have hp' : (q r).1 ∈ e.source := by
        simpa only [d, (tangentStructure S).chart_source, projection, mem_preimage] using hr
      dsimp only [x, d]
      rw [(tangentStructure S).chart_apply e he _ hp']
      simp [L]
    refine ⟨e, he, hp, x, hx, hxcoord hpd, ?_⟩
    exact (hsource.mono (fun r hr => (hxcoord hr).symm)).filter_mono nhdsWithin_le_nhds
end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MapData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData
  P202.GeodesicData P202.ExponentialData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Constant geodesic speed makes its actual normalized velocity parallel on
all parameter subsets; the derivative is one-sided at closed endpoints. -/
theorem geodesic_unit_parallel
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {J : Set ℝ} (hJ : J ⊆ I.carrier) {t : ℝ} (ht : t ∈ J) :
    HasCovariantDerivativeWithinAt C (fun r => (q r).1)
      (fun r => (tangentNorm g (q r).1 (q r).2)⁻¹ • (q r).2) J t 0 := by
  obtain ⟨W, hW, U, hU, b, hp, v', hv, hEq⟩ := (hq t (hJ ht)).2
  have hWJ : HasVelocityWithinAt S (fun r => (q r).1) J t W := by
    refine ⟨hW.1.mono (subset_univ J), ?_⟩
    obtain ⟨e, he, hp', hd⟩ := hW.2
    exact ⟨e, he, hp', hd.mono (subset_univ J)⟩
  have hDJ : HasCovariantDerivativeWithinAt C (fun r => (q r).1)
      (fun r => (q r).2) J t 0 :=
    ⟨W, hWJ, U, hU, b, hp, v', hv.mono (subset_univ J), hEq⟩
  let k := (tangentNorm g (q t).1 (q t).2)⁻¹
  have hscaled := CurveCovariantDerivative.derivative_const_smul C hDJ k
  simp only [smul_zero] at hscaled
  apply InducedConnections.curve_derivative_congr C ht hscaled
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [GeodesicIVP.constant_speed S g C hC I q hq r (hJ hr) t (hJ ht)]


/-- On a nondegenerate closed subinterval, the chosen one-sided velocity is
exactly the actual velocity recorded by the geodesic phase. -/
theorem geodesic_withinVelocity_eq
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ I.carrier)
    {t : ℝ} (ht : t ∈ Icc a b) :
    PiecewiseCurves.withinVelocity S (fun r => (q r).1) (Icc a b) t = (q t).2 := by
  have hvel := (hq t (hJ ht)).1
  have hvelJ : HasVelocityWithinAt S (fun r => (q r).1) (Icc a b) t (q t).2 := by
    refine ⟨hvel.1.mono (subset_univ _), ?_⟩
    obtain ⟨e, he, hp, hd⟩ := hvel.2
    exact ⟨e, he, hp, hd.mono (subset_univ _)⟩
  have hex : ∃ v, PiecewiseCurves.HasVelocityWithinAt S (fun r => (q r).1) (Icc a b) t v :=
    ⟨(q t).2, hvelJ⟩
  unfold PiecewiseCurves.withinVelocity
  rw [dite_eq_left hex]
  exact CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hab t ht)
    (Classical.choose_spec hex) hvelJ

/-- The unit field computed from actual one-sided segment velocities is
parallel for every nondegenerate compact geodesic segment. -/
theorem geodesic_withinUnit_parallel
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ I.carrier)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasCovariantDerivativeWithinAt C (fun r => (q r).1)
      (fun r => (tangentNorm g (q r).1
        (PiecewiseCurves.withinVelocity S (fun z => (q z).1) (Icc a b) r))⁻¹ •
          PiecewiseCurves.withinVelocity S (fun z => (q z).1) (Icc a b) r)
      (Icc a b) t 0 := by
  apply InducedConnections.curve_derivative_congr C ht
    (geodesic_unit_parallel g C hC I q hq hJ ht)
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [geodesic_withinVelocity_eq C I q hq hab hJ hr]

/-- The preceding intrinsic assertion applies to the actual first-variation
unitVelocity of any variation with the given geodesic base. -/
theorem geodesic_base_unitVelocity_parallel
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    (H : ℝ × ℝ → M) (hbase : (fun t => H (0,t)) = (fun t => (q t).1))
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ I.carrier)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasCovariantDerivativeWithinAt C (fun r => H (0,r))
      (unitVelocity g H a b) (Icc a b) t 0 := by
  let P : (ℝ → M) → Prop := fun γ =>
    HasCovariantDerivativeWithinAt C γ
      (fun r => (tangentNorm g (γ r)
        (PiecewiseCurves.withinVelocity S γ (Icc a b) r))⁻¹ •
          PiecewiseCurves.withinVelocity S γ (Icc a b) r) (Icc a b) t 0
  change P (fun r => H (0,r))
  exact Eq.mpr (congrArg P hbase)
    (geodesic_withinUnit_parallel g C hC I q hq hab hJ ht)


/-- A geodesic with zero velocity at one point is constant on its full open
interval, by actual geodesic initial-value uniqueness. -/
theorem geodesic_constant_of_velocity_zero
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {r : ℝ} (hr : r ∈ I.carrier) (hv : (q r).2 = 0) :
    ∀ s ∈ I.carrier, (q s).1 = (q r).1 := by
  have hmeet : q r = constantCurve S (q r).1 r := by
    simpa only [constantCurve, ← hv, Sigma.eta]
  have hEq := GeodesicIVP.overlap_unique S C I D13Unified.OpenTimeInterval.whole
    q (constantCurve S (q r).1) hq (GeodesicIVP.constant_is_geodesic C (q r).1)
    r ⟨hr, mem_univ r⟩ hmeet
  intro s hs
  simpa only [constantCurve] using
    congrArg (fun z : Phase S => z.1) (hEq ⟨hs, mem_univ s⟩)

/-- A geodesic nonconstant on a subinterval has positive speed everywhere
in its open domain. Neither completeness nor a chosen positive speed is assumed. -/
theorem geodesic_speed_pos_of_nonconstant
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {J : Set ℝ} (hJ : J ⊆ I.carrier)
    (hne : ∃ s ∈ J, ∃ t ∈ J, (q s).1 ≠ (q t).1)
    {r : ℝ} (hr : r ∈ I.carrier) :
    0 < tangentNorm g (q r).1 (q r).2 := by
  by_contra hpos
  have hzero : tangentNorm g (q r).1 (q r).2 = 0 :=
    le_antisymm (le_of_not_gt hpos) (SmoothMetrics.tangentNorm_nonneg g _ _)
  have hv : (q r).2 = 0 := (SmoothMetrics.tangentNorm_eq_zero_iff g _ _).mp hzero
  have hconst := geodesic_constant_of_velocity_zero C I q hq hr hv
  obtain ⟨s, hs, t, ht, hst⟩ := hne
  exact hst ((hconst s (hJ hs)).trans (hconst t (hJ ht)).symm)

/-- Positive speed for the actual first-variation segment velocity follows
from nonconstancy of the original geodesic segment. -/
theorem geodesic_base_segmentVelocity_pos
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    (H : ℝ × ℝ → M) (hbase : (fun t => H (0,t)) = (fun t => (q t).1))
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ I.carrier)
    (hne : ∃ s ∈ Icc a b, ∃ t ∈ Icc a b, (q s).1 ≠ (q t).1)
    {t : ℝ} (ht : t ∈ Icc a b) :
    0 < tangentNorm g (H (0,t)) (segmentVelocity S H a b t) := by
  let P : (ℝ → M) → Prop := fun γ =>
    0 < tangentNorm g (γ t) (PiecewiseCurves.withinVelocity S γ (Icc a b) t)
  change P (fun r => H (0,r))
  rw [hbase]
  change 0 < tangentNorm g (q t).1
    (PiecewiseCurves.withinVelocity S (fun z => (q z).1) (Icc a b) t)
  rw [geodesic_withinVelocity_eq C I q hq hab hJ ht]
  exact geodesic_speed_pos_of_nonconstant g C I q hq hJ hne (hJ ht)

end P202.Geometry.GeodesicCriticalityCorners

open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FrameData SmoothManifolds.VectorFieldData
  P202.ConnectionData P202.MetricData P202.CurveData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.GeodesicCriticalityCorners
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem smooth_field_base_smooth {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) : SmoothCurveOn S γ J := by
  refine ⟨smooth_field_base_continuous hV, ?_⟩
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hV.2 t ht
  let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
  let y : ℝ → Euclidean n := fun r => (L.symm (x r)).1
  have hnear : ∀ᶠ r in 𝓝[J] t, γ r ∈ e.source :=
    (smooth_field_base_continuous hV t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp)
  have hcoords : (fun r => (e (γ r)).val) =ᶠ[𝓝[J] t] y := by
    filter_upwards [hnear, heq] with r hr hxr
    dsimp only [y]
    rw [← hxr, (tangentStructure S).chart_apply e he _ hr]
    simp [L]
  exact ⟨e, he, hp, y, (L.symm.contDiff.contDiffAt.comp t hx).fst,
    (hcoords.self_of_nhdsWithin ht).symm, hcoords⟩

theorem scalar_smooth_extension {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hγ : SmoothCurveOn S γ J) (ht : t ∈ J)
    {f : M → ℝ} (hf : VectorSmoothAt S.smoothStructure.val f (γ t)) :
    ∃ y : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) y t ∧ (f ∘ γ) =ᶠ[𝓝[J] t] y := by
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hγ.2 t ht
  obtain ⟨U, hU, hu, G, hG, heqG⟩ := hf.2 e he hp
  refine ⟨G ∘ x, ?_, ?_⟩
  · have hGc : ContDiffAt ℝ (⊤ : ℕ∞) G (x t) := by
      rw [hxt]
      exact hG.contDiffAt (hU.mem_nhds hu)
    exact hGc.comp t hx
  · filter_upwards [heq, heqG.comp_tendsto (hγ.1 t ht)] with s hs hsG
    simpa only [Function.comp_apply, ← hs] using hsG.symm

theorem smooth_field_of_coordinate_germs {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hγ : ContinuousOn γ J)
    (hgerm : ∀ t ∈ J, ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val),
      γ t ∈ e.source ∧
      ∃ x : ℝ → Euclidean (n+n), ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
        x t = (((tangentStructure S).chart e he) ⟨γ t, V t⟩).val ∧
        (fun r => (((tangentStructure S).chart e he) ⟨γ r, V r⟩).val) =ᶠ[𝓝[J] t] x) :
    SmoothFieldAlongOn S γ V J := by
  refine ⟨?_, hgerm⟩
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hgerm t ht
  let d := (tangentStructure S).chart e he
  let H : ℝ → Phase S := fun r => ⟨γ r, V r⟩
  have hsource : H t ∈ d.source := by
    simpa only [d,H,(tangentStructure S).chart_source,projection,mem_preimage] using hp
  have hcoord : ContinuousWithinAt (fun r => (d (H r)).val) J t := by
    exact hx.continuousAt.continuousWithinAt.congr_of_eventuallyEq heq hxt.symm
  have hmodel : ContinuousWithinAt (fun r => d (H r)) J t := tendsto_subtype_rng.mpr hcoord
  have hback := (d.continuousAt_symm (d.map_source hsource)).tendsto.comp hmodel
  rw [d.left_inv hsource] at hback
  apply hback.congr'
  filter_upwards [(hγ t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp)] with r hr
  exact d.left_inv (by
    simpa only [d,H,(tangentStructure S).chart_source,projection,mem_preimage] using hr)

theorem connectionMatrix_mulVec_coordinates
    (C : Connection (tangentBundle S)) (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (X : TangentSpace S p.val) (z : Euclidean n) (k : Fin n) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    (connectionMatrix C b p X).mulVec z k =
      ∑ i : Fin n, ∑ j : Fin n, christoffel C c p k i j * (b.basis p).equivFun X i * z j := by
  classical
  dsimp only
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hlinear (j : Fin n) : connectionForm C b p k j X =
      ∑ i : Fin n, (b.basis p).equivFun X i * christoffel C c p k i j := by
    conv_lhs => rw [← (b.basis p).sum_equivFun X]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rw [← GeodesicIVP.coordinateVector_eq_frame]
    rfl
  change (connectionMatrix C b p X).mulVec z k = _
  simp only [Matrix.mulVec, dotProduct, connectionMatrix, hlinear, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end P202.Geometry.GeodesicCriticalityCorners
namespace P202.Geometry.GeodesicCriticalityCorners
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem smooth_field_covariantDerivative
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ} (hab : a < b)
    (hV : SmoothFieldAlongOn S γ V (Icc a b)) :
    SmoothFieldAlongOn S γ (covariantDerivativeWithin C γ V (Icc a b)) (Icc a b) := by
  classical
  let J := Icc a b
  let A := covariantDerivativeWithin C γ V J
  have hγ := smooth_field_base_smooth hV
  have hγ1 := smooth_field_base_c1 hV
  have hV1 := smooth_field_c1 hV
  have hAsp (r : ℝ) (hr : r ∈ J) : HasCovariantDerivativeWithinAt C γ V J r (A r) :=
    CurveCovariantDerivative.covariantDerivativeWithin_spec C
      (CurveCovariantDerivative.exists_covariantDerivative C hr hγ1 hγ.1 hV1)
  apply smooth_field_of_coordinate_germs hγ.1
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hV.2 t ht
  let c : TangentIndex S := ⟨e,he⟩
  let bf := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
  let y : ℝ → Euclidean n := fun r => (L.symm (x r)).1
  let z : ℝ → Euclidean n := fun r => (L.symm (x r)).2
  have hy : ContDiffAt ℝ (⊤ : ℕ∞) y t := (L.symm.contDiff.contDiffAt.comp t hx).fst
  have hz : ContDiffAt ℝ (⊤ : ℕ∞) z t := (L.symm.contDiff.contDiffAt.comp t hx).snd
  have hdy : ContDiffAt ℝ (⊤ : ℕ∞) (deriv y) t := by simpa using hy.derivWithin (by simp)
  have hdz : ContDiffAt ℝ (⊤ : ℕ∞) (deriv z) t := by simpa using hz.derivWithin (by simp)
  have hnear : ∀ᶠ r in 𝓝[J] t, γ r ∈ e.source :=
    (hγ.1 t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp)
  have hycoords : (fun r => (e (γ r)).val) =ᶠ[𝓝[J] t] y := by
    filter_upwards [hnear,heq] with r hr hxr
    dsimp only [y]
    rw [← hxr,(tangentStructure S).chart_apply e he _ hr]
    simp [L]
  have hzcoords : coefficientsAlong bf γ V =ᶠ[𝓝[J] t] z := by
    filter_upwards [hnear,heq] with r hr hxr
    have hpB : γ r ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hr
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpB,
      FirstVariation.tangentFrame_coordinates e he (γ r) hr]
    dsimp only [z]
    rw [← hxr,(tangentStructure S).chart_apply e he _ hr]
    simp [L]
  have hpB : γ t ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hgamma (k i j : Fin n) : ∃ g : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) g t ∧
      ((fun p => totalize (fun q => christoffel C c q k i j) p) ∘ γ) =ᶠ[𝓝[J] t] g := by
    apply scalar_smooth_extension hγ ht
    exact VectorSmoothAt.totalize (GeodesicIVP.tangent_baseSet_isOpen c)
      (GeodesicIVP.christoffel_smooth C c k i j ⟨γ t,hpB⟩)
  choose g hg heqg using hgamma
  let u : ℝ → Euclidean n := fun r k => deriv z r k +
    ∑ i : Fin n, ∑ j : Fin n, g k i j r * deriv y r i * z r j
  have hu : ContDiffAt ℝ (⊤ : ℕ∞) u t := by
    apply contDiffAt_pi.mpr
    intro k
    exact (contDiffAt_pi.mp hdz k).add (ContDiffAt.sum fun i _ =>
      ContDiffAt.sum fun j _ => ((hg k i j).mul (contDiffAt_pi.mp hdy i)).mul (contDiffAt_pi.mp hz j))
  have hy1 : ContDiffAt ℝ 1 y t := hy.of_le (by simp)
  have hz1 : ContDiffAt ℝ 1 z t := hz.of_le (by simp)
  have hcoeffA : coefficientsAlong bf γ A =ᶠ[𝓝[J] t] u := by
    have hgall : ∀ᶠ r in 𝓝[J] t, ∀ k i j : Fin n,
        totalize (fun q => christoffel C c q k i j) (γ r) = g k i j r :=
      Filter.eventually_all.mpr (fun k => Filter.eventually_all.mpr (fun i =>
        Filter.eventually_all.mpr (fun j => heqg k i j)))
    filter_upwards [hnear,hycoords.derivWithin,hzcoords,hzcoords.derivWithin,hgall,
      (hy1.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
      (hz1.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hpr hdyEq hzEq hdzEq hgr hyr hzr hr
    have hpBr : γ r ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hpr
    have hud : UniqueDiffWithinAt ℝ J r := uniqueDiffOn_Icc hab r hr
    obtain ⟨W,hW⟩ := PiecewiseCurves.CoordinateC1On.exists_withinVelocity hγ1 hγ.1 hr
    obtain ⟨d,hd⟩ := CurveCovariantDerivative.exists_coefficients_deriv C hr (hAsp r hr) bf hpBr
    have hdval : d = deriv z r := by
      rw [← hd.derivWithin hud,hdzEq]
      exact (hzr.differentiableAt (by simp)).derivWithin hud
    have hWval : (bf.basis ⟨γ r,hpBr⟩).equivFun W = deriv y r := by
      rw [FirstVariation.tangentFrame_coordinates e he (γ r) hpr]
      rw [← (CurveCovariantDerivative.velocity_coordinates hW hr e he hpr).derivWithin hud,hdyEq]
      exact (hyr.differentiableAt (by simp)).derivWithin hud
    have hform := CurveCovariantDerivative.local_formula C hr hud (hAsp r hr) bf hpBr hW hd
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpBr,hform]
    simp only [frameDerivative,LinearEquiv.apply_symm_apply]
    rw [hdval,hzEq]
    ext k
    change deriv z r k + (connectionMatrix C bf ⟨γ r,hpBr⟩ W).mulVec (z r) k = _
    rw [GeodesicCriticalityCorners.connectionMatrix_mulVec_coordinates C c ⟨γ r,hpBr⟩ W (z r) k]
    change deriv z r k + (∑ i, ∑ j, christoffel C c ⟨γ r,hpBr⟩ k i j *
      (bf.basis ⟨γ r,hpBr⟩).equivFun W i * z r j) = _
    rw [hWval]
    dsimp only [u]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hgij := hgr k i j
    rw [totalize_of_mem _ (γ r) hpBr] at hgij
    rw [hgij]
  have hcoordsA : (fun r => (((tangentStructure S).chart e he) ⟨γ r,A r⟩).val)
      =ᶠ[𝓝[J] t] fun r => L (y r,u r) := by
    filter_upwards [hnear,hycoords,hcoeffA] with r hpr hyr hur
    have hpBr : γ r ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hpr
    rw [(tangentStructure S).chart_apply e he _ hpr, hyr]
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpBr,
      FirstVariation.tangentFrame_coordinates e he (γ r) hpr] at hur
    rw [hur]
    rfl
  refine ⟨e,he,hp,fun r => L (y r,u r),L.contDiff.contDiffAt.comp t (hy.prodMk hu),
    (hcoordsA.self_of_nhdsWithin ht).symm,hcoordsA⟩
end P202.Geometry.GeodesicCriticalityCorners
namespace P202.Geometry.GeodesicCriticalityCorners
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem smooth_segmentVelocity {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b) :
    SmoothFieldAlongOn S (fun r => F (0,r)) (segmentVelocity S F a b) (Icc a b) := by
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε,hε⟩
  have hγ := FirstVariation.variation_continuousOn_slice hF h0
  apply smooth_field_of_coordinate_germs hγ
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hF.2 (0,t) ⟨h0,ht⟩
  let y : ℝ → Euclidean n := fun r => x (0,r)
  let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
  have hy : ContDiffAt ℝ (⊤ : ℕ∞) y t :=
    hx.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have hdy : ContDiffAt ℝ (⊤ : ℕ∞) (deriv y) t := by simpa using hy.derivWithin (by simp)
  have hy1 : ContDiffAt ℝ 1 y t := hy.of_le (by simp)
  have hmap : Tendsto (fun r : ℝ => (0,r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun r hr => ⟨h0,hr⟩)
  have hycoords : (fun r => (e (F (0,r))).val) =ᶠ[𝓝[Icc a b] t] y := heq.comp_tendsto hmap
  have hcoords : (fun r => (((tangentStructure S).chart e he)
      ⟨F (0,r),segmentVelocity S F a b r⟩).val) =ᶠ[𝓝[Icc a b] t]
        fun r => L (y r,deriv y r) := by
    filter_upwards [hycoords,hycoords.derivWithin,
      (hγ t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp),
      (hy1.eventually (by simp)).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
        with r hyr hdyr hpr hyr1 hr
    rw [(tangentStructure S).chart_apply e he
      (⟨F (0,r),segmentVelocity S F a b r⟩ : Phase S) hpr,hyr]
    rw [FirstVariation.segmentVelocity_coordinates hF hε hab hr e he hpr,hdyr,
      (hyr1.differentiableAt (by simp)).derivWithin (uniqueDiffOn_Icc hab r hr)]
    rfl
  exact ⟨e,he,hp,fun r => L (y r,deriv y r),L.contDiff.contDiffAt.comp t (hy.prodMk hdy),
    (hcoords.self_of_nhdsWithin ht).symm,hcoords⟩
end P202.Geometry.GeodesicCriticalityCorners

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.VectorFieldData
  SmoothManifolds.MapData SmoothManifolds.FrameData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem metric_square_phase_smooth (g : RiemannianMetric S) (z : Phase S) :
    VectorSmoothAt (phaseManifold S).smoothStructure.val
      (fun q : Phase S => pairing g q.1 q.2 q.2) z := by
  exact SmoothMetrics.metric_pairing_smoothAt (phaseManifold S) (tangentBundle S) g
    (projection S) (fun q => q.2) (fun q => q.2) z
    (SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S) z)
    ((tangentRealization S).smooth_from_original z)
    ((tangentRealization S).smooth_from_original z)

/-- Smooth scalar functions on the actual tangent manifold have smooth
ambient germs along any smooth intrinsic field on a closed parameter set. -/
theorem scalar_smooth_field_germ {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) {f : Phase S → ℝ} {t : ℝ} (ht : t ∈ J)
    (hf : VectorSmoothAt (phaseManifold S).smoothStructure.val f ⟨γ t,V t⟩) :
    ∃ y : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) y t ∧
      (fun r => f ⟨γ r,V r⟩) =ᶠ[𝓝[J] t] y := by
  obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hV.2 t ht
  let d := (tangentStructure S).chart e he
  have hd := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
  have hsrc : (⟨γ t,V t⟩ : Phase S) ∈ d.source := by
    simpa only [d,(tangentStructure S).chart_source,projection,mem_preimage] using hp
  obtain ⟨U,hU,hpU,G,hG,hrep⟩ := hf.2 d hd hsrc
  refine ⟨fun r => G (x r), (hG.contDiffAt (hU.mem_nhds (by rwa [hxt]))).comp t hx, ?_⟩
  filter_upwards [heq,hrep.comp_tendsto (hV.1 t ht)] with r hxr hr
  rw [← hxr]
  exact hr.symm

/-- A smooth scalar germ on the parameter set may multiply a smooth field;
only its trace on that set matters. -/
theorem smooth_field_smul_of_local {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J) {φ : ℝ → ℝ}
    (hcφ : ContinuousOn φ J)
    (hφ : ∀ t ∈ J, ∃ y : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) y t ∧
      y t = φ t ∧ φ =ᶠ[𝓝[J] t] y) :
    SmoothFieldAlongOn S γ (fun t => φ t • V t) J := by
  refine ⟨(scaled_field_continuous hV).comp (hcφ.prodMk continuousOn_id)
    (fun r hr => ⟨mem_univ _,hr⟩), ?_⟩
  intro t ht
  obtain ⟨y,hy,hyt,hyeq⟩ := hφ t ht
  obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := scaled_field_germ hV (z := (φ t,t)) ht
  have harg : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => (y r,r)) t := hy.prodMk contDiffAt_id
  rw [← hyt] at hx
  have hc := hx.comp t (f := fun r : ℝ => (y r,r)) harg
  have hmap : Tendsto (fun r : ℝ => (φ r,r)) (𝓝[J] t) (𝓝[univ ×ˢ J] (φ t,t)) :=
    ((hcφ t ht).prodMk continuousWithinAt_id).tendsto_nhdsWithin
      (fun r hr => ⟨mem_univ _,hr⟩)
  refine ⟨e,he,hp,fun r => x (y r,r),hc,?_,?_⟩
  · simpa only [hyt] using hxt
  · filter_upwards [heq.comp_tendsto hmap,hyeq] with r hr hyr
    change (((tangentStructure S).chart e he) ⟨γ r, φ r • V r⟩).val = x (φ r,r) at hr
    rw [hr,hyr]

theorem normalize_smooth_field (g : RiemannianMetric S) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J)
    (hpos : ∀ t ∈ J, 0 < tangentNorm g (γ t) (V t)) :
    SmoothFieldAlongOn S γ
      (fun t => (tangentNorm g (γ t) (V t))⁻¹ • V t) J := by
  apply smooth_field_smul_of_local hV
  · intro t ht
    exact ((smooth_fields_pairing_continuous g hV hV t ht).sqrt).inv₀
      (ne_of_gt (hpos t ht))
  · intro t ht
    obtain ⟨y,hy,heq⟩ := scalar_smooth_field_germ hV ht (metric_square_phase_smooth g _)
    have heqt : pairing g (γ t) (V t) (V t) = y t := heq.self_of_nhdsWithin ht
    have hynz : y t ≠ 0 := by
      rw [← heqt, ← SmoothMetrics.tangentNorm_sq g (γ t) (V t)]
      exact pow_ne_zero _ (ne_of_gt (hpos t ht))
    have hsqrt : Real.sqrt (y t) ≠ 0 := by
      rw [← heqt]
      exact ne_of_gt (hpos t ht)
    refine ⟨fun r => (Real.sqrt (y r))⁻¹, (hy.sqrt hynz).inv hsqrt, ?_, ?_⟩
    · change (Real.sqrt (y t))⁻¹ = _
      rw [← heqt]
      rfl
    · filter_upwards [heq] with r hr
      change (Real.sqrt (pairing g (γ r) (V r) (V r)))⁻¹ = (Real.sqrt (y r))⁻¹
      rw [hr]
end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem smooth_curve_constant_variation {γ : ℝ → M} {J : Set ℝ}
    (hγ : SmoothCurveOn S γ J) {ε a b : ℝ} (hJ : Icc a b ⊆ J) :
    SmoothVariationOn S (fun z : ℝ × ℝ => γ z.2) ε a b := by
  have hmap (z : ℝ × ℝ) : Tendsto (Prod.snd : ℝ × ℝ → ℝ)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] z) (𝓝[J] z.2) :=
    continuous_snd.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun w hw => hJ hw.2)
  refine ⟨?_,?_⟩
  · intro z hz
    exact (hγ.1 z.2 (hJ hz.2)).comp (continuous_snd.continuousWithinAt) (fun w hw => hJ hw.2)
  · intro z hz
    obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hγ.2 z.2 (hJ hz.2)
    exact ⟨e,he,hp,fun w => x w.2,hx.comp z contDiffAt_snd,hxt,heq.comp_tendsto (hmap z)⟩

theorem smooth_test_endpoint_zero {φ : ℝ → ℝ} {a b : ℝ}
    (hs : tsupport φ ⊆ Ioo a b) : φ a = 0 ∧ φ b = 0 := by
  constructor
  · by_contra hne
    exact (lt_irrefl a) (hs (subset_closure (Function.mem_support.mpr hne))).1
  · by_contra hne
    exact (lt_irrefl b) (hs (subset_closure (Function.mem_support.mpr hne))).2

theorem energy_critical_implies_geodesic
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : SmoothCurveOn S γ (Icc a b))
    (hcrit : EnergyCriticalOn g γ a b) :
    ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b) (Icc a b) t 0 := by
  let T := segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b
  let A := covariantDerivativeWithin C γ T (Icc a b)
  have hF : SmoothVariationOn S (fun z : ℝ × ℝ => γ z.2) 1 a b :=
    smooth_curve_constant_variation hγ Subset.rfl
  have hT : SmoothFieldAlongOn S γ T (Icc a b) := smooth_segmentVelocity hF zero_lt_one hab
  have hA : SmoothFieldAlongOn S γ A (Icc a b) := smooth_field_covariantDerivative C hab hT
  have hAz : ∀ t ∈ Icc a b, A t = 0 := by
    apply smooth_field_fundamental_lemma g hab hA
    intro φ hφ hc hs
    have hW := smooth_field_smul hA hφ
    obtain ⟨ε,hε,H,hH,hHV,hfixed⟩ := realize_smooth_field C γ (fun t => φ t • A t) a b hW
    obtain ⟨hφa,hφb⟩ := smooth_test_endpoint_zero hs
    have hfix : EndpointFixed H ε a b := hfixed (by simp [hφa]) (by simp [hφb])
    have hd := hcrit H ε hε hH hfix (fun t _ => (hHV t).1)
    have hint := (energy_stationary_iff_integral_zero g C hC hε hab.le hH hfix).mp hd
    have hbasefun : (fun t => H (0,t)) = γ := funext (fun t => (hHV t).1)
    subst γ
    change (∫ t in a..b, pairing g (H (0,t)) (φ t • A t) (A t)) = 0
    change (∫ t in a..b, pairing g (H (0,t)) (variationField S H t) (A t)) = 0 at hint
    convert hint using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [eq_of_heq (hHV t).2]
  intro t ht
  have hspec := CurveCovariantDerivative.covariantDerivativeWithin_spec C
    (CurveCovariantDerivative.exists_covariantDerivative C ht
      (smooth_field_base_c1 hT) hγ.1 (smooth_field_c1 hT))
  change HasCovariantDerivativeWithinAt C _ _ _ t (A t) at hspec
  simpa only [hAz t ht] using hspec

theorem length_critical_implies_parallel_unit
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : SmoothCurveOn S γ (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (γ t)
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t))
    (hcrit : LengthCriticalOn g γ a b) :
    ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
      (unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b) (Icc a b) t 0 := by
  let U := unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b
  let A := covariantDerivativeWithin C γ U (Icc a b)
  have hF : SmoothVariationOn S (fun z : ℝ × ℝ => γ z.2) 1 a b :=
    smooth_curve_constant_variation hγ Subset.rfl
  have hU : SmoothFieldAlongOn S γ U (Icc a b) :=
    normalize_smooth_field g (smooth_segmentVelocity hF zero_lt_one hab) hpos
  have hA : SmoothFieldAlongOn S γ A (Icc a b) := smooth_field_covariantDerivative C hab hU
  have hAz : ∀ t ∈ Icc a b, A t = 0 := by
    apply smooth_field_fundamental_lemma g hab hA
    intro φ hφ hc hs
    have hW := smooth_field_smul hA hφ
    obtain ⟨ε,hε,H,hH,hHV,hfixed⟩ := realize_smooth_field C γ (fun t => φ t • A t) a b hW
    obtain ⟨hφa,hφb⟩ := smooth_test_endpoint_zero hs
    have hfix : EndpointFixed H ε a b := hfixed (by simp [hφa]) (by simp [hφb])
    have hd := hcrit H ε hε hH hfix (fun t _ => (hHV t).1)
    have hbasefun : (fun t => H (0,t)) = γ := funext (fun t => (hHV t).1)
    subst γ
    have hint := (length_stationary_iff_integral_zero g C hC hε hab.le hH hfix hpos).mp hd
    change (∫ t in a..b, pairing g (H (0,t)) (φ t • A t) (A t)) = 0
    change (∫ t in a..b, pairing g (H (0,t)) (variationField S H t) (A t)) = 0 at hint
    convert hint using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [eq_of_heq (hHV t).2]
  intro t ht
  have hspec := CurveCovariantDerivative.covariantDerivativeWithin_spec C
    (CurveCovariantDerivative.exists_covariantDerivative C ht
      (smooth_field_base_c1 hU) hγ.1 (smooth_field_c1 hU))
  change HasCovariantDerivativeWithinAt C _ _ _ t (A t) at hspec
  simpa only [hAz t ht] using hspec
end P202.Geometry.GeodesicCriticalityCorners

open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FrameData SmoothManifolds.VectorFieldData
  P202.ConnectionData P202.MetricData P202.CurveData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.GeodesicCriticalityCorners
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem covariantDerivativeWithin_of_at (C : Connection (tangentBundle S))
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ} {t : ℝ}
    {D : TangentSpace S (γ t)} (hD : HasCovariantDerivativeAt C γ V t D) :
    HasCovariantDerivativeWithinAt C γ V J t D := by
  obtain ⟨W,⟨hc,e,he,hp,hv⟩,U,hU,b,hpU,v',hd,hDeq⟩ := hD
  exact ⟨W,⟨hc.mono (subset_univ _),e,he,hp,hv.mono (subset_univ _)⟩,
    U,hU,b,hpU,v',hd.mono (subset_univ _),hDeq⟩

theorem smooth_field_zero_of_interior_zero (g : RiemannianMetric S)
    {γ : ℝ → M} {A : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ} (hab : a < b)
    (hA : SmoothFieldAlongOn S γ A (Icc a b))
    (hzero : ∀ t ∈ Ioo a b, A t = 0) : ∀ t ∈ Icc a b, A t = 0 := by
  have heq : EqOn (fun t => pairing g (γ t) (A t) (A t)) (fun _ => 0) (Ioo a b) := by
    intro t ht
    simp only [hzero t ht,pairing,map_zero]
  have heq' := heq.of_subset_closure (smooth_fields_pairing_continuous g hA hA)
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  intro t ht
  by_contra hne
  exact (ne_of_gt (g.positive (γ t) (A t) hne)) (heq' ht)

theorem regular_arc_length_geodesic_iff (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) :
    let σ := arcParameter (fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (F (0,τ s)) (unitVelocity g F a b (τ s)) = 1) ∧
      ((∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
        (unitVelocity g F a b) (Icc a b) t 0) ↔
      IsGeodesicOn S C (Ioo 0 (σ b))
        (fun s => (⟨F (0,τ s), unitVelocity g F a b (τ s)⟩ : Phase S))) := by
  let v := fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)
  let σ := arcParameter v a
  have hmono : StrictMonoOn σ (Icc a b) := strictMono_arcParameter
    (segmentSpeed_continuousOn g hF hε hab) hpos
  have hσa : σ a = 0 := by simp [σ,arcParameter]
  have hL : 0 < σ b := by
    simpa only [hσa] using hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  obtain ⟨τ,hτ,hmap,hτσ,hστ,hd,hvel,hnorm,hequiv⟩ :=
    regular_arc_length_parameterization g hF hε hab hpos
  refine ⟨τ,hτ,hmap,hτσ,hστ,hnorm,?_⟩
  constructor
  · intro hpar
    exact geodesicOn_of_closed_interval C hvel ((hequiv C).mp hpar)
  · intro hgeo
    let γ := fun r => F (0,r)
    let U := unitVelocity g F a b
    let A := covariantDerivativeWithin C γ U (Icc a b)
    have hU : SmoothFieldAlongOn S γ U (Icc a b) :=
      normalize_smooth_field g (smooth_segmentVelocity hF hε hab) hpos
    have hA : SmoothFieldAlongOn S γ A (Icc a b) := smooth_field_covariantDerivative C hab hU
    have hDexists (t : ℝ) (ht : t ∈ Icc a b) : ∃ D, HasCovariantDerivativeWithinAt C γ U (Icc a b) t D :=
      CurveCovariantDerivative.exists_covariantDerivative C ht (smooth_field_base_c1 hU)
        (smooth_field_base_continuous hU) (smooth_field_c1 hU)
    have hAzero : ∀ t ∈ Icc a b, A t = 0 := by
      apply smooth_field_zero_of_interior_zero g hab hA
      intro t ht
      have hst : σ t ∈ Ioo 0 (σ b) := ⟨by
        simpa only [hσa] using hmono (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self ht) ht.1,
        hmono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hab.le) ht.2⟩
      have hst' : σ t ∈ Icc 0 (σ b) := Ioo_subset_Icc_self hst
      have hnew : HasCovariantDerivativeWithinAt C (γ ∘ τ) (fun r => U (τ r))
          (Icc 0 (σ b)) (σ t) 0 := covariantDerivativeWithin_of_at C (hgeo (σ t) hst).2
      have horig := (derivative_zero_reparam_iff C hst' (uniqueDiffOn_Icc hL _ hst')
        (hd (σ t) hst') hmap (inv_ne_zero (ne_of_gt (hpos _ (hmap hst'))))
        (hDexists _ (hmap hst'))).mpr hnew
      have horig' : HasCovariantDerivativeWithinAt C γ U (Icc a b) t 0 :=
        Eq.mp (congrArg (fun r => HasCovariantDerivativeWithinAt C γ U (Icc a b) r 0)
          (hτσ t (Ioo_subset_Icc_self ht))) horig
      exact CurveCovariantDerivative.covariantDerivativeWithin_eq C (Ioo_subset_Icc_self ht)
        (uniqueDiffOn_Icc hab t (Ioo_subset_Icc_self ht)) horig'
    intro t ht
    have hD := CurveCovariantDerivative.covariantDerivativeWithin_spec C (hDexists t ht)
    exact Eq.mp (congrArg (fun D => HasCovariantDerivativeWithinAt C γ U (Icc a b) t D)
      (hAzero t ht)) hD
end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 800000
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.BundleData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- Intrinsic one-sided velocities depend only on the curve trace on the set. -/
theorem hasVelocityWithinAt_congr_eqOn
    {c d : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (heq : EqOn c d J) {v : TangentSpace S (c t)}
    (hv : P202.CurveConnectionData.HasVelocityWithinAt S c J t v) :
    P202.CurveConnectionData.HasVelocityWithinAt S d J t
      (cast (congrArg (TangentSpace S) (heq ht)) v) := by
  have hnear : c =ᶠ[𝓝[J] t] d := mem_of_superset self_mem_nhdsWithin (fun s hs => heq hs)
  obtain ⟨hc,e,he,hp,hd⟩ := hv
  have hp' : d t ∈ e.source := heq ht ▸ hp
  refine ⟨hc.congr_of_eventuallyEq_of_mem hnear.symm ht,e,he,hp',?_⟩
  rw [PiecewiseCurves.fiberCoordinates_cast e he (c t) (d t) hp hp' (heq ht)]
  exact hd.congr_of_eventuallyEq_of_mem (hnear.fun_comp (fun p => (e p).val)).symm ht

/-- Actual tangent-frame coefficients respect equality of base traces and
heterogeneous equality in their original intrinsic tangent fibers. -/
theorem coefficientsAlong_congr_eqOn
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c d : ℝ → M} {J : Set ℝ}
    {V : (t : ℝ) → TangentSpace S (c t)} {W : (t : ℝ) → TangentSpace S (d t)}
    (heq : EqOn c d J) (hVW : ∀ t ∈ J, HEq (V t) (W t)) :
    EqOn (coefficientsAlong b c V) (coefficientsAlong b d W) J := by
  classical
  intro t ht
  have hc : ∀ (p q : M) (v : TangentSpace S p) (w : TangentSpace S q),
      p = q → HEq v w →
      (if hp : p ∈ U then (b.basis ⟨p,hp⟩).equivFun v else 0) =
      (if hq : q ∈ U then (b.basis ⟨q,hq⟩).equivFun w else 0) := by
    intro p q v w hpq hvw
    cases hpq
    cases hvw
    rfl
  simpa only [coefficientsAlong] using hc (c t) (d t) (V t) (W t) (heq ht) (hVW t ht)

/-- The local frame formula itself respects transport at the base point. -/
theorem frameDerivative_heq_of_eqOn
    (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c d : ℝ → M} {t : ℝ}
    {V : (t : ℝ) → TangentSpace S (c t)} {W : (t : ℝ) → TangentSpace S (d t)}
    (hcd : c t = d t) (hVW : HEq (V t) (W t))
    (hc : c t ∈ U) (hd : d t ∈ U)
    (v : TangentSpace S (c t)) (v' : Euclidean n) :
    HEq (frameDerivative C b c V t hc v v')
      (frameDerivative C b d W t hd (cast (congrArg (TangentSpace S) hcd) v) v') := by
  have hformula : ∀ (p q : M) (hp : p ∈ U) (hq : q ∈ U)
      (v : TangentSpace S p) (w : TangentSpace S q)
      (f : TangentSpace S p) (g : TangentSpace S q), p = q → HEq v w → HEq f g →
      HEq ((b.basis ⟨p,hp⟩).equivFun.symm
        (v' + (connectionMatrix C b ⟨p,hp⟩ v).mulVec ((b.basis ⟨p,hp⟩).equivFun f)))
      ((b.basis ⟨q,hq⟩).equivFun.symm
        (v' + (connectionMatrix C b ⟨q,hq⟩ w).mulVec ((b.basis ⟨q,hq⟩).equivFun g))) := by
    intro p q hp hq v w f g hpq hv hf
    cases hpq
    cases hv
    cases hf
    rfl
  simpa only [frameDerivative,coefficientsAlong,dite_eq_left hc,dite_eq_left hd] using
    hformula (c t) (d t) hc hd v (cast (congrArg (TangentSpace S) hcd) v)
      (V t) (W t) hcd (cast_heq _ v).symm hVW


/-- The intrinsic covariant derivative on a closed parameter set depends only
on its actual curve and tangent-field trace, with the required base transport. -/
theorem hasCovariantDerivativeWithinAt_congr_eqOn
    (C : Connection (tangentBundle S))
    {c d : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {V : (t : ℝ) → TangentSpace S (c t)} {W : (t : ℝ) → TangentSpace S (d t)}
    (heq : EqOn c d J) (hVW : ∀ t ∈ J, HEq (V t) (W t))
    {D : TangentSpace S (c t)}
    (hD : HasCovariantDerivativeWithinAt C c V J t D) :
    HasCovariantDerivativeWithinAt C d W J t
      (cast (congrArg (TangentSpace S) (heq ht)) D) := by
  obtain ⟨A,hA,U,hU,b,hp,v',hd,hformula⟩ := hD
  have hp' : d t ∈ U := heq ht ▸ hp
  have hcoeff := coefficientsAlong_congr_eqOn b heq hVW
  have hnear : coefficientsAlong b c V =ᶠ[𝓝[J] t] coefficientsAlong b d W :=
    mem_of_superset self_mem_nhdsWithin (fun s hs => hcoeff hs)
  refine ⟨_,hasVelocityWithinAt_congr_eqOn ht heq hA,U,hU,b,hp',v',
    hd.congr_of_eventuallyEq_of_mem hnear.symm ht,?_⟩
  apply eq_of_heq
  exact (cast_heq _ D).trans ((heq_of_eq hformula).trans
    (frameDerivative_heq_of_eqOn C b (heq ht) (hVW t ht) hp hp' A v'))

theorem cast_tangent_zero {p q : M} (h : p = q) :
    cast (congrArg (TangentSpace S) h) (0 : TangentSpace S p) = 0 := by
  cases h
  rfl

/-- Parallelism is preserved by equality of the traces on the parameter set. -/
theorem parallelWithinAt_congr_eqOn
    (C : Connection (tangentBundle S))
    {c d : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {V : (t : ℝ) → TangentSpace S (c t)} {W : (t : ℝ) → TangentSpace S (d t)}
    (heq : EqOn c d J) (hVW : ∀ t ∈ J, HEq (V t) (W t))
    (hD : HasCovariantDerivativeWithinAt C c V J t 0) :
    HasCovariantDerivativeWithinAt C d W J t 0 := by
  have hd := hasCovariantDerivativeWithinAt_congr_eqOn C ht heq hVW hD
  have hz : cast (congrArg (TangentSpace S) (heq ht)) (0 : TangentSpace S (c t)) = 0 :=
    cast_tangent_zero (S := S) (heq ht)
  rw [hz] at hd
  exact hd


/-- Actual selected one-sided segment velocities agree under equality of the
base traces on the entire closed segment. No off-segment smoothness is needed. -/
theorem segmentVelocity_heq_of_eqOn
    {F G : ℝ × ℝ → M} {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (heq : EqOn (fun r => F (0,r)) (fun r => G (0,r)) (Icc a b)) :
    HEq (segmentVelocity S F a b t) (segmentVelocity S G a b t) := by
  classical
  let Hf := ∃ v, P202.CurveConnectionData.HasVelocityWithinAt S (fun r => F (0,r)) (Icc a b) t v
  let Hg := ∃ v, P202.CurveConnectionData.HasVelocityWithinAt S (fun r => G (0,r)) (Icc a b) t v
  by_cases hf : Hf
  · have hg : Hg := ⟨_,hasVelocityWithinAt_congr_eqOn ht heq (Classical.choose_spec hf)⟩
    unfold segmentVelocity
    rw [dite_eq_left hf,dite_eq_left hg]
    have hu := CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hab t ht)
      (hasVelocityWithinAt_congr_eqOn ht heq (Classical.choose_spec hf)) (Classical.choose_spec hg)
    exact (cast_heq _ (Classical.choose hf)).symm.trans (heq_of_eq hu)
  · have hg : ¬ Hg := by
      rintro ⟨v,hv⟩
      exact hf ⟨_,hasVelocityWithinAt_congr_eqOn ht heq.symm hv⟩
    unfold segmentVelocity
    rw [dite_eq_right hf,dite_eq_right hg]
    exact (cast_heq (congrArg (TangentSpace S) (heq ht)) (0 : TangentSpace S (F (0,t)))).symm.trans
      (heq_of_eq (cast_tangent_zero (S := S) (heq ht)))

theorem normalizedVelocity_heq (g : RiemannianMetric S)
    {p q : M} (hpq : p = q) (v : TangentSpace S p) (w : TangentSpace S q)
    (hvw : HEq v w) :
    HEq ((tangentNorm g p v)⁻¹ • v) ((tangentNorm g q w)⁻¹ • w) := by
  cases hpq
  cases hvw
  rfl

/-- Normalization of the actual one-sided velocities respects the same closed
trace equivalence, with equality in the original tangent fibers. -/
theorem unitVelocity_heq_of_eqOn
    (g : RiemannianMetric S) {F G : ℝ × ℝ → M} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (heq : EqOn (fun r => F (0,r)) (fun r => G (0,r)) (Icc a b)) :
    HEq (unitVelocity g F a b t) (unitVelocity g G a b t) :=
  normalizedVelocity_heq g (heq ht) _ _ (segmentVelocity_heq_of_eqOn hab ht heq)

end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 800000
namespace P202.Geometry.GeodesicCriticalityCorners
open P202.Geometry P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.BundleData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

section Euclidean
variable {S : SmoothManifold n .euclidean M}

theorem smoothCurveOn_congr {γ η : ℝ → M} {J : Set ℝ}
    (hγ : SmoothCurveOn S γ J) (hEq : EqOn η γ J) :
    SmoothCurveOn S η J := by
  refine ⟨hγ.1.congr (fun t ht => hEq ht), ?_⟩
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hγ.2 t ht
  refine ⟨e, he, ?_, x, hx, ?_, ?_⟩
  · rw [hEq ht]
    exact hp
  · rw [hEq ht]
    exact hxt
  · filter_upwards [self_mem_nhdsWithin, heq] with r hr hxr
    rw [hEq hr]
    exact hxr

theorem tangentNorm_eq_of_heq (g : RiemannianMetric S)
    {p q : M} (hpq : p = q) (v : TangentSpace S p) (w : TangentSpace S q)
    (hvw : HEq v w) : tangentNorm g p v = tangentNorm g q w := by
  cases hpq
  cases hvw
  rfl

/-- A finite concatenation of genuine nonconstant intrinsic geodesic segments
whose actual length equals the source endpoint-distance infimum has matching
one-sided unit velocities at every join. No corner tests or parallelism are
assumed: both are derived from the actual geodesic pieces. -/
theorem minimizing_broken_geodesic_no_corner
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (I : Fin (k+1) → D13Unified.OpenTimeInterval)
    (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (hdom : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ (I i).carrier)
    (hpiece : ∀ i, EqOn γ (fun t => (q i t).1) (Icc (node i.castSucc) (node i.succ)))
    (hne : ∀ i, ∃ s ∈ Icc (node i.castSucc) (node i.succ),
      ∃ t ∈ Icc (node i.castSucc) (node i.succ), (q i s).1 ≠ (q i t).1)
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))) :
    ∀ j : Fin k,
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.castSucc.castSucc) (node j.castSucc.succ) (node j.succ.castSucc) =
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.succ.castSucc) (node j.succ.succ) (node j.succ.castSucc) := by
  apply minimizing_parallel_curve_no_corner g C hC γ node hnode ?_ ?_ ?_ hmin
  · intro i
    exact smoothCurveOn_congr
      (geodesic_position_smoothCurveOn C (I i) (q i) (hq i) (hdom i)) (hpiece i)
  · intro i t ht
    have hab : node i.castSucc < node i.succ := hnode Fin.castSucc_lt_succ
    have hp := geodesic_base_segmentVelocity_pos g C (I i) (q i) (hq i)
      (fun z : ℝ × ℝ => (q i z.2).1) rfl hab (hdom i) (hne i) ht
    have hvel := segmentVelocity_heq_of_eqOn (S := S) (F := fun z : ℝ × ℝ => γ z.2)
      (G := fun z : ℝ × ℝ => (q i z.2).1) hab ht (hpiece i)
    rw [tangentNorm_eq_of_heq g (hpiece i ht) _ _ hvel]
    exact hp
  · intro i t ht
    have hab : node i.castSucc < node i.succ := hnode Fin.castSucc_lt_succ
    have hpar := geodesic_base_unitVelocity_parallel g C hC (I i) (q i) (hq i)
      (fun z : ℝ × ℝ => (q i z.2).1) rfl hab (hdom i) ht
    apply parallelWithinAt_congr_eqOn C ht (hpiece i).symm ?_ hpar
    intro r hr
    exact (unitVelocity_heq_of_eqOn g (F := fun z : ℝ × ℝ => γ z.2)
      (G := fun z : ℝ × ℝ => (q i z.2).1) hab hr (hpiece i)).symm

end Euclidean
end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 800000
namespace P202.Geometry.GeodesicCriticalityCorners
open P202.Geometry P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.BundleData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- Energy stationarity for every actual variation agreeing with the original
curve only on the compact segment. All velocities remain one-sided at endpoints. -/
theorem geodesic_energy_stationary_of_base_eqOn
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M) {a b : ℝ} (hab : a < b)
    (hgeo : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b) (Icc a b) t 0)
    (H : ℝ × ℝ → M) {ε : ℝ} (hε : 0 < ε)
    (hH : SmoothVariationOn S H ε a b) (hfix : EndpointFixed H ε a b)
    (hbase : EqOn (fun t => H (0,t)) γ (Icc a b)) :
    HasDerivAt (variedEnergy g H a b) 0 0 := by
  apply geodesic_energy_stationary g C hC H ε a b hε hab hH hfix
  intro t ht
  apply parallelWithinAt_congr_eqOn C ht hbase.symm ?_ (hgeo t ht)
  intro r hr
  exact segmentVelocity_heq_of_eqOn (S := S)
    (F := fun z : ℝ × ℝ => γ z.2) (G := H) hab hr hbase.symm

/-- Length stationarity for every actual endpoint-fixed variation with the
same closed base trace follows from parallelism of the actual canonical unit
velocity. This statement does not constrain off-segment representatives. -/
theorem parallel_unit_length_stationary_of_base_eqOn
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M) {a b : ℝ} (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (γ t)
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t))
    (hpar : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
      (unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b) (Icc a b) t 0)
    (H : ℝ × ℝ → M) {ε : ℝ} (hε : 0 < ε)
    (hH : SmoothVariationOn S H ε a b) (hfix : EndpointFixed H ε a b)
    (hbase : EqOn (fun t => H (0,t)) γ (Icc a b)) :
    HasDerivAt (variedLength g H a b) 0 0 := by
  apply parallel_unit_length_stationary g C hC H ε a b hε hab hH hfix
  · intro t ht
    have hvel := segmentVelocity_heq_of_eqOn (S := S)
      (F := H) (G := fun z : ℝ × ℝ => γ z.2) hab ht hbase
    have hnorm : tangentNorm g (H (0,t)) (segmentVelocity S H a b t) =
        tangentNorm g (γ t) (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t) := by
      have hlemma : ∀ (p q : M) (v : TangentSpace S p) (w : TangentSpace S q),
          p = q → HEq v w → tangentNorm g p v = tangentNorm g q w := by
        intro p q v w hpq hvw
        cases hpq
        cases hvw
        rfl
      exact hlemma _ _ _ _ (hbase ht) hvel
    rw [hnorm]
    exact hpos t ht
  · intro t ht
    apply parallelWithinAt_congr_eqOn C ht hbase.symm ?_ (hpar t ht)
    intro r hr
    exact unitVelocity_heq_of_eqOn g
      (F := fun z : ℝ × ℝ => γ z.2) (G := H) hab hr hbase.symm


end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Universal fixed-endpoint energy criticality is exactly the original
covariant geodesic equation. Constant curves and dimension zero are included. -/
theorem energy_criticality_iff
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : SmoothCurveOn S γ (Icc a b)) :
    EnergyCriticalOn g γ a b ↔
      ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b) (Icc a b) t 0 := by
  constructor
  · exact energy_critical_implies_geodesic g C hC hab hγ
  · intro hgeo H ε hε hH hfix hbase
    exact geodesic_energy_stationary_of_base_eqOn g C hC γ hab hgeo H hε hH hfix
      hbase

/-- Universal fixed-endpoint length criticality is exactly parallelism of the
actual unit tangent. Regularity is required on the entire compact interval. -/
theorem length_criticality_iff_parallel_unit
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : SmoothCurveOn S γ (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (γ t)
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t)) :
    LengthCriticalOn g γ a b ↔
      ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
        (unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b) (Icc a b) t 0 := by
  constructor
  · exact length_critical_implies_parallel_unit g C hC hab hγ hpos
  · intro hpar H ε hε hH hfix hbase
    exact parallel_unit_length_stationary_of_base_eqOn g C hC γ hab hpos hpar H hε hH hfix
      hbase

/-- The source length-criticality statement, with its actual accumulated-speed
parameter and inverse, and the intrinsic geodesic equation after arc length. -/
theorem length_criticality_iff_arclength_geodesic
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : SmoothCurveOn S γ (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (γ t)
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t)) :
    let σ := arcParameter (fun t => tangentNorm g (γ t)
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t)) a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (γ (τ s))
        (unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b (τ s)) = 1) ∧
      (LengthCriticalOn g γ a b ↔ IsGeodesicOn S C (Ioo 0 (σ b))
        (fun s => (⟨γ (τ s),unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b (τ s)⟩ : Phase S))) := by
  have hF : SmoothVariationOn S (fun z : ℝ × ℝ => γ z.2) 1 a b :=
    smooth_curve_constant_variation hγ Subset.rfl
  obtain ⟨τ,hτ,hmap,hτσ,hστ,hnorm,hequiv⟩ :=
    regular_arc_length_geodesic_iff g C hF zero_lt_one hab hpos
  exact ⟨τ,hτ,hmap,hτσ,hστ,hnorm,
    (length_criticality_iff_parallel_unit g C hC hab hγ hpos).trans hequiv⟩
end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 800000
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Matching unit velocities at a join of genuine geodesic pieces give one
actual smooth unit-speed geodesic containing both arc-length normalizations.
Each original open time domain is transformed explicitly, so no completeness
or unproved endpoint extension is assumed. -/
theorem unit_speed_geodesic_gluing
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C)
    (I J : D13Unified.OpenTimeInterval) (q r : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (hr : IsGeodesicOn S C J.carrier r)
    (c : ℝ) (hc : c ∈ I.carrier ∩ J.carrier)
    (hp : (q c).1 = (r c).1)
    (hqpos : 0 < tangentNorm g (q c).1 (q c).2)
    (hrpos : 0 < tangentNorm g (r c).1 (r c).2)
    (hunit : HEq ((tangentNorm g (q c).1 (q c).2)⁻¹ • (q c).2)
      ((tangentNorm g (r c).1 (r c).2)⁻¹ • (r c).2)) :
    ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      affineDomain I.carrier (tangentNorm g (q c).1 (q c).2)⁻¹ c ∪
        affineDomain J.carrier (tangentNorm g (r c).1 (r c).2)⁻¹ c ⊆ K.carrier ∧
      IsGeodesicOn S C K.carrier z ∧
      EqOn z (affineCurve S q (tangentNorm g (q c).1 (q c).2)⁻¹ c)
        (affineDomain I.carrier (tangentNorm g (q c).1 (q c).2)⁻¹ c) ∧
      EqOn z (affineCurve S r (tangentNorm g (r c).1 (r c).2)⁻¹ c)
        (affineDomain J.carrier (tangentNorm g (r c).1 (r c).2)⁻¹ c) ∧
      (∀ t ∈ K.carrier, tangentNorm g (z t).1 (z t).2 = 1) ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source → ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (z s)).val) t := by
  let a := tangentNorm g (q c).1 (q c).2
  let b := tangentNorm g (r c).1 (r c).2
  let I' := GeodesicIVP.affineInterval I a⁻¹ c (inv_ne_zero (ne_of_gt hqpos))
  let J' := GeodesicIVP.affineInterval J b⁻¹ c (inv_ne_zero (ne_of_gt hrpos))
  let Q := affineCurve S q a⁻¹ c
  let R := affineCurve S r b⁻¹ c
  have hI0 : (0:ℝ) ∈ I'.carrier := by
    simpa [I',GeodesicIVP.affineInterval,affineDomain] using hc.1
  have hJ0 : (0:ℝ) ∈ J'.carrier := by
    simpa [J',GeodesicIVP.affineInterval,affineDomain] using hc.2
  have hQ : IsGeodesicOn S C I'.carrier Q := GeodesicIVP.geodesic_affine C a⁻¹ c hq
  have hR : IsGeodesicOn S C J'.carrier R := GeodesicIVP.geodesic_affine C b⁻¹ c hr
  have hmeet : Q 0 = R 0 := by
    have hnormphase : (⟨(q c).1,a⁻¹ • (q c).2⟩ : Phase S) = ⟨(r c).1,b⁻¹ • (r c).2⟩ :=
      Sigma.ext hp hunit
    change (⟨(q (a⁻¹ * 0 + c)).1,a⁻¹ • (q (a⁻¹ * 0 + c)).2⟩ : Phase S) =
      ⟨(r (b⁻¹ * 0 + c)).1,b⁻¹ • (r (b⁻¹ * 0 + c)).2⟩
    rw [show a⁻¹ * 0 + c = c by ring,show b⁻¹ * 0 + c = c by ring]
    exact hnormphase
  obtain ⟨K,z,hK,hz,hzQ,hzR,hsmooth⟩ :=
    geodesic_gluing g C hC I' J' Q R hQ hR 0 ⟨hI0,hJ0⟩ hmeet
  refine ⟨K,z,hK,hz,hzQ,hzR,?_,hsmooth⟩
  have h0K : (0:ℝ) ∈ K.carrier := hK (Or.inl hI0)
  have hunit0 : tangentNorm g (Q 0).1 (Q 0).2 = 1 := by
    change tangentNorm g (q (a⁻¹ * 0 + c)).1 (a⁻¹ • (q (a⁻¹ * 0 + c)).2) = 1
    rw [show a⁻¹ * 0 + c = c by ring]
    rw [SmoothMetrics.tangentNorm_smul,abs_of_pos (inv_pos.mpr hqpos)]
    exact inv_mul_cancel₀ (ne_of_gt hqpos)
  intro t ht
  rw [GeodesicIVP.constant_speed S g C hC K z hz t ht 0 h0K]
  have hnorm := congrArg (fun w : Phase S => tangentNorm g w.1 w.2) (hzQ hI0)
  exact hnorm.trans hunit0

end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A maximal geodesic absorbs every genuine geodesic meeting it with the
same phase. The candidate union is constructed before maximality is used. -/
theorem maximal_absorbs_meeting_geodesic
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {w : Phase S} {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (hq : IsMaximalThrough S C w I q)
    (J : D13Unified.OpenTimeInterval) (r : ℝ → Phase S)
    (hr : IsGeodesicOn S C J.carrier r) (c : ℝ)
    (hc : c ∈ I.carrier ∩ J.carrier) (hmeet : q c = r c) :
    J.carrier ⊆ I.carrier ∧ EqOn q r J.carrier := by
  obtain ⟨K,z,hK,hz,hzq,hzr,_⟩ :=
    geodesic_gluing g C hC I J q r hq.2.2.1 hr c hc hmeet
  have h0 : (0:ℝ) ∈ K.carrier := hK (Or.inl hq.1)
  have hz0 : z 0 = w := (hzq hq.1).trans hq.2.1
  have hmax := hq.2.2.2 K z h0 hz0 hz
  refine ⟨fun t ht => hmax.1 (hK (Or.inr ht)), ?_⟩
  intro t ht
  exact (hmax.2 (hK (Or.inr ht))).trans (hzr ht)

/-- Finitely many intrinsic geodesics whose successive phase values match
are restrictions of one genuine smooth geodesic on an actual open domain. -/
theorem finite_geodesic_gluing
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {k : ℕ} (I : Fin (k+1) → D13Unified.OpenTimeInterval)
    (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (h0 : (0:ℝ) ∈ (I 0).carrier)
    (join : Fin k → ℝ)
    (hjoin : ∀ j : Fin k, join j ∈ (I j.castSucc).carrier ∩ (I j.succ).carrier ∧
      q j.castSucc (join j) = q j.succ (join j)) :
    ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      IsGeodesicOn S C K.carrier z ∧
      (∀ i, (I i).carrier ⊆ K.carrier ∧ EqOn z (q i) (I i).carrier) ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source → ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (z s)).val) t := by
  obtain ⟨K,z,hz⟩ := GeodesicIVP.maximal_exists S g C hC (q 0 0)
  have hall : ∀ i, (I i).carrier ⊆ K.carrier ∧ EqOn z (q i) (I i).carrier := by
    intro i
    induction i using Fin.induction with
    | zero => exact hz.2.2.2 (I 0) (q 0) h0 rfl (hq 0)
    | succ i hi =>
      have hc : join i ∈ K.carrier ∩ (I i.succ).carrier :=
        ⟨hi.1 (hjoin i).1.1,(hjoin i).1.2⟩
      have hmeet : z (join i) = q i.succ (join i) :=
        (hi.2 (hjoin i).1.1).trans (hjoin i).2
      exact maximal_absorbs_meeting_geodesic g C hC hz (I i.succ) (q i.succ)
        (hq i.succ) (join i) hc hmeet
  refine ⟨K,z,hz.2.2.1,hall,?_⟩
  obtain ⟨G,_hG,hbridge⟩ := GeodesicIVP.spray_exists S C
  intro t ht e he hp
  exact (((hbridge K z).mpr hz.2.2.1).2 t ht e he hp).1
end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 800000
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.GeodesicCriticalityCorners
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem minimizing_piece_length_le
    (g : RiemannianMetric S) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1)))))
    (i₀ : Fin (k+1)) (d : PiecewiseC1Curve S (node i₀.castSucc) (node i₀.succ))
    (hdstart : d (node i₀.castSucc) = γ (node i₀.castSucc))
    (hdend : d (node i₀.succ) = γ (node i₀.succ)) :
    (∫ t in node i₀.castSucc..node i₀.succ, speed g γ t) ≤ length g d := by
  classical
  have hF (i : Fin (k+1)) : SmoothVariationOn S (fun z : ℝ × ℝ => γ z.2) 1
      (node i.castSucc) (node i.succ) := smooth_curve_constant_variation (hγ i) Subset.rfl
  let base : (i : Fin (k+1)) → PiecewiseC1Curve S (node i.castSucc) (node i.succ) :=
    fun i => FirstVariation.variationSlice (s := 0) (hF i) (by simp) (hnode.monotone (Fin.castSucc_le_succ i))
  let curves : (i : Fin (k+1)) → PiecewiseC1Curve S (node i.castSucc) (node i.succ) :=
    Function.update base i₀ d
  have hstart : ∀ i, curves i (node i.castSucc) = γ (node i.castSucc) := by
    intro i
    by_cases hi : i = i₀
    · subst i
      simpa only [curves,Function.update_self] using hdstart
    · simp only [curves,Function.update_of_ne hi]
      rfl
  have hend : ∀ i, curves i (node i.succ) = γ (node i.succ) := by
    intro i
    by_cases hi : i = i₀
    · subst i
      simpa only [curves,Function.update_self] using hdend
    · simp only [curves,Function.update_of_ne hi]
      rfl
  obtain ⟨c,hc0,hcend,_hpieces,hclength⟩ := LengthLaws.finiteConcatenation_length g node
    (fun j => γ (node j)) curves hstart hend
  have hbaseLength : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      ∑ i : Fin (k+1), length g (base i) := by
    exact (FirstVariation.varied_functionals_subdivision (s := 0) g node hnode.monotone hF (by simp)).2
  have hsumle : (∑ i : Fin (k+1), length g (base i)) ≤ ∑ i : Fin (k+1), length g (curves i) := by
    rw [← hbaseLength,hmin,← hclength,← hc0,← hcend]
    exact endpointDistance_le_length g c
  have hdiff : (∑ i : Fin (k+1), length g (curves i)) - ∑ i : Fin (k+1), length g (base i) =
      length g d - length g (base i₀) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i : Fin (k+1), if i = i₀ then length g d - length g (base i₀) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = i₀
        · subst i
          simp only [curves,Function.update_self,ite_true]
        · simp only [curves,Function.update_of_ne hi,hi,ite_false,sub_self]
      _ = _ := by simp
  change length g (base i₀) ≤ length g d
  linarith
end P202.Geometry.GeodesicCriticalityCorners
namespace P202.Geometry.GeodesicCriticalityCorners
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem minimizing_piece_variation_localMin
    (g : RiemannianMetric S) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1)))))
    (i₀ : Fin (k+1)) (H : ℝ × ℝ → M) {ε : ℝ} (hε : 0 < ε)
    (hH : SmoothVariationOn S H ε (node i₀.castSucc) (node i₀.succ))
    (hfix : EndpointFixed H ε (node i₀.castSucc) (node i₀.succ))
    (hbase : EqOn (fun t => H (0,t)) γ (Icc (node i₀.castSucc) (node i₀.succ))) :
    IsLocalMin (variedLength g H (node i₀.castSucc) (node i₀.succ)) 0 := by
  have hab : node i₀.castSucc < node i₀.succ := hnode (show i₀.castSucc < i₀.succ from Fin.castSucc_lt_succ)
  have h0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε,hε⟩
  have hFγ : SmoothVariationOn S (fun z : ℝ × ℝ => γ z.2) 1
      (node i₀.castSucc) (node i₀.succ) := smooth_curve_constant_variation (hγ i₀) Subset.rfl
  have hL0 : variedLength g H (node i₀.castSucc) (node i₀.succ) 0 =
      ∫ t in node i₀.castSucc..node i₀.succ, speed g γ t :=
    PiecewiseCurves.length_eq_of_eqOn g (FirstVariation.variationSlice hH h0 hab.le)
      (FirstVariation.variationSlice (s := 0) hFγ (by simp) hab.le) hbase
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hε) hε] with s hs
  have hstart : (FirstVariation.variationSlice hH hs hab.le) (node i₀.castSucc) =
      γ (node i₀.castSucc) :=
    ((hfix s hs).1).trans (hbase (left_mem_Icc.mpr hab.le))
  have hend : (FirstVariation.variationSlice hH hs hab.le) (node i₀.succ) =
      γ (node i₀.succ) :=
    ((hfix s hs).2).trans (hbase (right_mem_Icc.mpr hab.le))
  have hle := minimizing_piece_length_le g γ node hnode hγ hmin i₀
    (FirstVariation.variationSlice hH hs hab.le) hstart hend
  rw [← hL0] at hle
  exact hle

theorem minimizing_piece_length_critical
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (γ : ℝ → M) {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (γ t)
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ) t))
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))) :
    ∀ i : Fin (k+1), LengthCriticalOn g γ (node i.castSucc) (node i.succ) := by
  intro i H ε hε hH hfix hbase
  have hab : node i.castSucc < node i.succ := hnode (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  have hposH : ∀ t ∈ Icc (node i.castSucc) (node i.succ),
      0 < tangentNorm g (H (0,t)) (segmentVelocity S H (node i.castSucc) (node i.succ) t) := by
    intro t ht
    have hvel := segmentVelocity_heq_of_eqOn (S := S) (F := H)
      (G := fun z : ℝ × ℝ => γ z.2) hab ht hbase
    rw [tangentNorm_eq_of_heq g (hbase t ht) _ _ hvel]
    exact hpos i t ht
  have hd := FirstVariation.first_variation_length g C hC H ε _ _ hε hab.le hH hposH
  exact hd.congr_deriv ((minimizing_piece_variation_localMin g γ node hnode hγ hmin
    i H hε hH hfix hbase).hasDerivAt_eq_zero hd)

theorem minimizing_regular_curve_parallel_unit
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (γ : ℝ → M) {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (γ t)
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ) t))
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))) :
    ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      HasCovariantDerivativeWithinAt C γ
        (unitVelocity g (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ))
        (Icc (node i.castSucc) (node i.succ)) t 0 := by
  intro i
  exact length_critical_implies_parallel_unit g C hC (hnode (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
    (hγ i) (hpos i) (minimizing_piece_length_critical g C hC γ node hnode hγ hpos hmin i)

theorem minimizing_regular_curve_no_corner
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (γ : ℝ → M) {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (γ t)
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ) t))
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))) :
    ∀ j : Fin k,
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.castSucc.castSucc) (node j.castSucc.succ) (node j.succ.castSucc) =
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.succ.castSucc) (node j.succ.succ) (node j.succ.castSucc) :=
  minimizing_parallel_curve_no_corner g C hC γ node hnode hγ hpos
    (minimizing_regular_curve_parallel_unit g C hC γ node hnode hγ hpos hmin) hmin
end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 800000
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}
/-- The source first-variation unit velocity of a compact geodesic piece is
its intrinsic normalized phase velocity, including both endpoints. -/
theorem geodesic_segment_unitVelocity_eq
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ I.carrier) {t : ℝ} (ht : t ∈ Icc a b) :
    unitVelocity g (fun z : ℝ × ℝ => (q z.2).1) a b t =
      (tangentNorm g (q t).1 (q t).2)⁻¹ • (q t).2 := by
  change (tangentNorm g (q t).1
    (PiecewiseCurves.withinVelocity S (fun r => (q r).1) (Icc a b) t))⁻¹ •
      PiecewiseCurves.withinVelocity S (fun r => (q r).1) (Icc a b) t = _
  rw [geodesic_withinVelocity_eq C I q hq hab hJ ht]


/-- Every finite minimizing concatenation of nonconstant intrinsic geodesic
pieces has a single actual smooth unit-speed geodesic containing all of its
arc-length normalized pieces. The common parameter nodes are the actual
cumulative segment lengths, and all transformed open domains are explicit. -/
theorem minimizing_broken_geodesic_global_gluing
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (I : Fin (k+1) → D13Unified.OpenTimeInterval)
    (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (hdom : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ (I i).carrier)
    (hpiece : ∀ i, EqOn γ (fun t => (q i t).1) (Icc (node i.castSucc) (node i.succ)))
    (hne : ∀ i, ∃ s ∈ Icc (node i.castSucc) (node i.succ),
      ∃ t ∈ Icc (node i.castSucc) (node i.succ), (q i s).1 ≠ (q i t).1)
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))) :
    let c := fun i : Fin (k+1) => tangentNorm g (q i (node i.castSucc)).1 (q i (node i.castSucc)).2
    let s := Fin.partialSum (fun i : Fin (k+1) => c i * (node i.succ - node i.castSucc))
    ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      StrictMono s ∧ IsGeodesicOn S C K.carrier z ∧
      (∀ i, affineDomain (I i).carrier (c i)⁻¹ (node i.castSucc - (c i)⁻¹ * s i.castSucc) ⊆ K.carrier ∧
        EqOn z (affineCurve S (q i) (c i)⁻¹ (node i.castSucc - (c i)⁻¹ * s i.castSucc))
          (affineDomain (I i).carrier (c i)⁻¹ (node i.castSucc - (c i)⁻¹ * s i.castSucc))) ∧
      (∀ t ∈ K.carrier, tangentNorm g (z t).1 (z t).2 = 1) ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source → ContDiffAt ℝ (⊤ : ℕ∞) (fun r => (e (z r)).val) t := by
  dsimp only
  let c := fun i : Fin (k+1) => tangentNorm g (q i (node i.castSucc)).1 (q i (node i.castSucc)).2
  let s := Fin.partialSum (fun i : Fin (k+1) => c i * (node i.succ - node i.castSucc))
  have hab (i : Fin (k+1)) : node i.castSucc < node i.succ := hnode Fin.castSucc_lt_succ
  have hleft (i : Fin (k+1)) : node i.castSucc ∈ Icc (node i.castSucc) (node i.succ) :=
    ⟨le_rfl,(hab i).le⟩
  have hright (i : Fin (k+1)) : node i.succ ∈ Icc (node i.castSucc) (node i.succ) :=
    ⟨(hab i).le,le_rfl⟩
  have hc (i : Fin (k+1)) : 0 < c i :=
    geodesic_speed_pos_of_nonconstant g C (I i) (q i) (hq i) (hdom i) (hne i) (hdom i (hleft i))
  have hs (i : Fin (k+1)) : s i.succ = s i.castSucc + c i * (node i.succ - node i.castSucc) :=
    Fin.partialSum_succ _ i
  have hsmono : StrictMono s := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    rw [hs]
    exact lt_add_of_pos_right _ (mul_pos (hc i) (sub_pos.mpr (hab i)))
  let b := fun i : Fin (k+1) => node i.castSucc - (c i)⁻¹ * s i.castSucc
  let N := fun i : Fin (k+1) => GeodesicIVP.affineInterval (I i) (c i)⁻¹ (b i)
    (inv_ne_zero (ne_of_gt (hc i)))
  let Q := fun i : Fin (k+1) => affineCurve S (q i) (c i)⁻¹ (b i)
  have hQ (i : Fin (k+1)) : IsGeodesicOn S C (N i).carrier (Q i) :=
    GeodesicIVP.geodesic_affine C (c i)⁻¹ (b i) (hq i)
  have htimeL (i : Fin (k+1)) : (c i)⁻¹ * s i.castSucc + b i = node i.castSucc := by
    dsimp [b]
    ring
  have htimeR (i : Fin (k+1)) : (c i)⁻¹ * s i.succ + b i = node i.succ := by
    rw [hs]
    calc
      _ = ((c i)⁻¹ * c i) * (node i.succ - node i.castSucc) + node i.castSucc := by dsimp [b]; ring
      _ = node i.succ := by rw [inv_mul_cancel₀ (ne_of_gt (hc i))]; ring
  have hNL (i : Fin (k+1)) : s i.castSucc ∈ (N i).carrier := by
    change (c i)⁻¹ * s i.castSucc + b i ∈ (I i).carrier
    rw [htimeL]
    exact hdom i (hleft i)
  have hNR (i : Fin (k+1)) : s i.succ ∈ (N i).carrier := by
    change (c i)⁻¹ * s i.succ + b i ∈ (I i).carrier
    rw [htimeR]
    exact hdom i (hright i)
  have hs0 : s ((0 : Fin (k+1)).castSucc) = 0 := by
    change s 0 = 0
    exact Fin.partialSum_zero _
  have h0 : (0:ℝ) ∈ (N 0).carrier := by
    have hmem := hNL 0
    rw [hs0] at hmem
    exact hmem
  have hno := minimizing_broken_geodesic_no_corner g C hC γ node hnode I q hq hdom hpiece hne hmin
  have hjoins (j : Fin k) : s j.succ.castSucc ∈ (N j.castSucc).carrier ∩ (N j.succ).carrier ∧
      Q j.castSucc (s j.succ.castSucc) = Q j.succ (s j.succ.castSucc) := by
    refine ⟨⟨hNR j.castSucc,hNL j.succ⟩,?_⟩
    let t := node j.succ.castSucc
    have htL : t ∈ Icc (node j.castSucc.castSucc) (node j.castSucc.succ) := hright j.castSucc
    have htR : t ∈ Icc (node j.succ.castSucc) (node j.succ.succ) := hleft j.succ
    have hp : (q j.castSucc t).1 = (q j.succ t).1 :=
      (hpiece j.castSucc htL).symm.trans (hpiece j.succ htR)
    have hL := (unitVelocity_heq_of_eqOn g (F := fun z : ℝ × ℝ => γ z.2)
      (G := fun z : ℝ × ℝ => (q j.castSucc z.2).1) (hab j.castSucc) htL (hpiece j.castSucc)).trans
        (heq_of_eq (geodesic_segment_unitVelocity_eq g C (I j.castSucc) (q j.castSucc)
          (hq j.castSucc) (hab j.castSucc) (hdom j.castSucc) htL))
    have hR := (unitVelocity_heq_of_eqOn g (F := fun z : ℝ × ℝ => γ z.2)
      (G := fun z : ℝ × ℝ => (q j.succ z.2).1) (hab j.succ) htR (hpiece j.succ)).trans
        (heq_of_eq (geodesic_segment_unitVelocity_eq g C (I j.succ) (q j.succ)
          (hq j.succ) (hab j.succ) (hdom j.succ) htR))
    have hunit := hL.symm.trans ((heq_of_eq (hno j)).trans hR)
    have hconstL : c j.castSucc = tangentNorm g (q j.castSucc t).1 (q j.castSucc t).2 :=
      GeodesicIVP.constant_speed S g C hC (I j.castSucc) (q j.castSucc) (hq j.castSucc)
        _ (hdom j.castSucc (hleft j.castSucc)) t (hdom j.castSucc htL)
    change (⟨(q j.castSucc ((c j.castSucc)⁻¹ * s j.succ.castSucc + b j.castSucc)).1,
      (c j.castSucc)⁻¹ • (q j.castSucc ((c j.castSucc)⁻¹ * s j.succ.castSucc + b j.castSucc)).2⟩ : Phase S) =
      ⟨(q j.succ ((c j.succ)⁻¹ * s j.succ.castSucc + b j.succ)).1,
        (c j.succ)⁻¹ • (q j.succ ((c j.succ)⁻¹ * s j.succ.castSucc + b j.succ)).2⟩
    have htimeRL : (c j.castSucc)⁻¹ * s j.succ.castSucc + b j.castSucc = t := htimeR j.castSucc
    have htimeLR : (c j.succ)⁻¹ * s j.succ.castSucc + b j.succ = t := htimeL j.succ
    rw [htimeRL,htimeLR]
    apply Sigma.ext
    · exact hp
    · rw [hconstL]
      exact hunit
  obtain ⟨K,z,hz,hall,hsmooth⟩ := finite_geodesic_gluing g C hC N Q hQ h0
    (fun j => s j.succ.castSucc) hjoins
  refine ⟨K,z,hsmono,hz,hall,?_,hsmooth⟩
  have h0K : (0:ℝ) ∈ K.carrier := (hall 0).1 h0
  have hz0 : z 0 = Q 0 0 := (hall 0).2 h0
  have htime0 : (c 0)⁻¹ * 0 + b 0 = node 0 := by
    have heq := htimeL 0
    rw [hs0] at heq
    exact heq
  have hunit0 : tangentNorm g (Q 0 0).1 (Q 0 0).2 = 1 := by
    change tangentNorm g (q 0 ((c 0)⁻¹ * 0 + b 0)).1
      ((c 0)⁻¹ • (q 0 ((c 0)⁻¹ * 0 + b 0)).2) = 1
    rw [htime0,SmoothMetrics.tangentNorm_smul,abs_of_pos (inv_pos.mpr (hc 0))]
    exact inv_mul_cancel₀ (ne_of_gt (hc 0))
  intro t ht
  rw [GeodesicIVP.constant_speed S g C hC K z hz t ht 0 h0K]
  exact (congrArg (fun w : Phase S => tangentNorm g w.1 w.2) hz0).trans hunit0

end P202.Geometry.GeodesicCriticalityCorners

set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology
namespace P202.Geometry.GeodesicCriticalityCorners

/-- A smooth scalar germ has an actual integral primitive with the same
ambient smoothness at its center. Values away from the germ are irrelevant. -/
theorem primitive_contDiffAt {x : ℝ → ℝ} {t : ℝ}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x t) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun r => ∫ y in t..r, x y) t ∧
      HasDerivAt (fun r => ∫ y in t..r, x y) (x t) t := by
  have hx1 : ContDiffAt ℝ 1 x t := hx.of_le (by simp)
  have hnear : ∀ᶠ r in 𝓝 t, ContinuousAt x r :=
    (hx1.eventually (by simp)).mono
      (fun r hr => hr.continuousAt)
  obtain ⟨l, u, ht, hcont⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  have hc : ContinuousOn x (Ioo l u) := fun r hr => (hcont hr).continuousWithinAt
  have hd (r : ℝ) (hr : r ∈ Ioo l u) :
      HasDerivAt (fun r => ∫ y in t..r, x y) (x r) r :=
    intervalIntegral.integral_hasDerivAt_right
      (hc.mono (ordConnected_Ioo.uIcc_subset ht hr)).intervalIntegrable
      (hc.stronglyMeasurableAtFilter isOpen_Ioo r hr) (hcont hr)
  refine ⟨?_, hd t ht⟩
  apply contDiffAt_infty.mpr
  intro n
  cases n with
  | zero => exact contDiffAt_zero.mpr ⟨Ioo l u, Ioo_mem_nhds ht.1 ht.2,
      fun r hr => (hd r hr).continuousAt.continuousWithinAt⟩
  | succ n =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun r => (x r) • ContinuousLinearMap.id ℝ ℝ,
      ⟨Ioo l u, Ioo_mem_nhds ht.1 ht.2, ?_⟩, ?_⟩
    · intro r hr
      convert (hd r hr).hasFDerivAt using 1
      ext z
      simp [mul_comm]
    · have hxn : ContDiffAt ℝ n x t := hx.of_le (by simp)
      exact hxn.smul contDiffAt_const


/-- The actual accumulated-speed integral has smooth ambient primitive germs
at closed endpoints whenever its integrand has such germs. -/
theorem arcParameter_smooth_germ {v : ℝ → ℝ} {a b t : ℝ}
    (hv : ContinuousOn v (Icc a b)) (ht : t ∈ Icc a b)
    (hvgerm : ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      x t = v t ∧ v =ᶠ[𝓝[Icc a b] t] x) :
    ∃ P : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) P t ∧
      P t = P202.CriticalityData.arcParameter v a t ∧
      P202.CriticalityData.arcParameter v a =ᶠ[𝓝[Icc a b] t] P ∧
      HasDerivAt P (v t) t := by
  obtain ⟨x, hx, hxt, hxeq⟩ := hvgerm
  let P : ℝ → ℝ := fun r => P202.CriticalityData.arcParameter v a t + ∫ y in t..r, x y
  obtain ⟨hPsmooth, hPderiv⟩ := primitive_contDiffAt hx
  refine ⟨P, contDiffAt_const.add hPsmooth, ?_, ?_, ?_⟩
  · simp [P]
  · obtain ⟨U, hUt, hUeq⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hxeq
    obtain ⟨l, u, htl, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hUt
    have hloc' : ∀ᶠ r in 𝓝 t, r ∈ Ioo l u := Ioo_mem_nhds htl.1 htl.2
    have hloc : ∀ᶠ r in 𝓝[Icc a b] t, r ∈ Ioo l u :=
      hloc'.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hloc] with r hr hrloc
    have hInt : (∫ y in t..r, v y) = ∫ y in t..r, x y := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact hUeq ⟨hlu (ordConnected_Ioo.uIcc_subset htl hrloc hy),
        uIcc_subset_Icc ht hr hy⟩
    have hai := (hv.mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc (μ := volume) hr.1
    have hat := (hv.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hadd := intervalIntegral.integral_interval_sub_left hai hat
    change (∫ y in a..r, v y) = (∫ y in a..t, v y) + ∫ y in t..r, x y
    linarith
  · simpa only [P, hxt] using hPderiv.const_add
      (P202.CriticalityData.arcParameter v a t)

/-- A genuine continuous inverse inherits ambient smooth germs on a closed
parameter subset from positive-derivative ambient germs of the original map. -/
theorem inverse_smooth_germ
    {σ τ v : ℝ → ℝ} {J K : Set ℝ}
    (hτ : ContinuousOn τ K) (hτmap : MapsTo τ K J)
    (hστ : ∀ s ∈ K, σ (τ s) = s)
    (hσ : ∀ t ∈ J, ∃ P : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) P t ∧
      P t = σ t ∧ σ =ᶠ[𝓝[J] t] P ∧ HasDerivAt P (v t) t)
    (hpos : ∀ t ∈ J, 0 < v t) {s : ℝ} (hs : s ∈ K) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) ψ s ∧
      τ s = ψ s ∧ τ =ᶠ[𝓝[K] s] ψ ∧ 0 < deriv ψ s := by
  obtain ⟨P, hP, hPt, hσP, hdP⟩ := hσ (τ s) (hτmap hs)
  have hPn : v (τ s) ≠ 0 := ne_of_gt (hpos _ (hτmap hs))
  let e := hP.toOpenPartialHomeomorph P (hdP.hasFDerivAt_equiv hPn) (by simp)
  have he : (e : ℝ → ℝ) = P := hP.toOpenPartialHomeomorph_coe _ _
  have hsrc : τ s ∈ e.source := hP.mem_toOpenPartialHomeomorph_source _ _
  have hPs : P (τ s) = s := hPt.trans (hστ s hs)
  have htar : s ∈ e.target := by
    rw [← hPs]
    exact e.map_source hsrc
  have hinv : e.symm s = τ s := by
    have h := e.left_inv hsrc
    rw [he, hPs] at h
    exact h
  have hdPe : HasDerivAt e (v (τ s)) (e.symm s) := by
    simpa only [hinv, he] using hdP
  have hPe : ContDiffAt ℝ (⊤ : ℕ∞) e (e.symm s) := by
    simpa only [hinv, he] using hP
  refine ⟨e.symm, e.contDiffAt_symm_deriv hPn htar hdPe hPe, hinv.symm, ?_, ?_⟩
  · have hτJ := (hτ s hs).tendsto_nhdsWithin hτmap
    have hnear : ∀ᶠ r in 𝓝[K] s, τ r ∈ e.source :=
      (hτ s hs).preimage_mem_nhdsWithin (e.open_source.mem_nhds hsrc)
    filter_upwards [self_mem_nhdsWithin, hnear, hσP.comp_tendsto hτJ]
      with r hr hsr hPr
    have her : e (τ r) = r := by
      change P (τ r) = r
      exact hPr.symm.trans (hστ r hr)
    exact (e.left_inv hsr).symm.trans (congrArg e.symm her)
  · rw [(e.hasDerivAt_symm htar hPn hdPe).deriv]
    exact inv_pos.mpr (hpos _ (hτmap hs))


/-- Positive smooth speed germs give an actual regular smooth arc-length inverse. -/
theorem arcParameter_inverse_smooth {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t)
    (hvgerm : ∀ t ∈ Icc a b, ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      x t = v t ∧ v =ᶠ[𝓝[Icc a b] t] x) :
    ∃ τ : ℝ → ℝ, Continuous τ ∧
      MapsTo τ (Icc 0 (P202.CriticalityData.arcParameter v a b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (P202.CriticalityData.arcParameter v a t) = t) ∧
      (∀ s ∈ Icc 0 (P202.CriticalityData.arcParameter v a b),
        P202.CriticalityData.arcParameter v a (τ s) = s) ∧
      (∀ s ∈ Icc 0 (P202.CriticalityData.arcParameter v a b),
        ∃ ψ : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) ψ s ∧
          τ s = ψ s ∧ τ =ᶠ[𝓝[Icc 0 (P202.CriticalityData.arcParameter v a b)] s] ψ ∧
            0 < deriv ψ s) ∧
      P202.CurveData.RegularRealC1On τ
        (Icc 0 (P202.CriticalityData.arcParameter v a b)) := by
  obtain ⟨τ, hτ, hmap, hτσ, hστ, _⟩ := arcParameter_inverse hab hv hpos
  have hgerm (s : ℝ) (hs : s ∈ Icc 0 (P202.CriticalityData.arcParameter v a b)) :=
    inverse_smooth_germ hτ.continuousOn hmap hστ
      (fun t ht => arcParameter_smooth_germ hv ht (hvgerm t ht)) hpos hs
  refine ⟨τ, hτ, hmap, hτσ, hστ, hgerm, ?_⟩
  intro s hs
  obtain ⟨ψ, hψ, hψs, hψeq, hψpos⟩ := hgerm s hs
  exact ⟨ψ, hψ.of_le (by simp), hψs, hψeq, hψpos⟩


open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.CurveConnectionData P202.FirstVariationData
  P202.CriticalityData P202.GeodesicData

/-- Positive norm of a smooth intrinsic field has actual ambient smooth germs. -/
theorem smooth_field_norm_germ {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : SmoothFieldAlongOn S γ V J)
    (hpos : ∀ t ∈ J, 0 < tangentNorm g (γ t) (V t)) {t : ℝ} (ht : t ∈ J) :
    ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      x t = tangentNorm g (γ t) (V t) ∧
      (fun r => tangentNorm g (γ r) (V r)) =ᶠ[𝓝[J] t] x := by
  obtain ⟨y, hy, heq⟩ := scalar_smooth_field_germ hV ht (metric_square_phase_smooth g _)
  have heqt : pairing g (γ t) (V t) (V t) = y t := heq.self_of_nhdsWithin ht
  have hynz : y t ≠ 0 := by
    rw [← heqt, ← SmoothMetrics.tangentNorm_sq g (γ t) (V t)]
    exact pow_ne_zero _ (ne_of_gt (hpos t ht))
  refine ⟨fun r => Real.sqrt (y r), hy.sqrt hynz, ?_, ?_⟩
  · change Real.sqrt (y t) = _
    rw [← heqt]
    rfl
  · filter_upwards [heq] with r hr
    change Real.sqrt (pairing g (γ r) (V r) (V r)) = Real.sqrt (y r)
    rw [hr]


/-- The actual accumulated-speed inverse is an accepted regular increasing
change of compact parameter, rather than merely an inverse certificate. -/
theorem arcParameter_piecewiseRegularIncreasing {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t)
    (hvgerm : ∀ t ∈ Icc a b, ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      x t = v t ∧ v =ᶠ[𝓝[Icc a b] t] x) :
    ∃ φ : PiecewiseRegularIncreasing a b 0 (arcParameter v a b),
      ∀ t ∈ Icc a b, φ (arcParameter v a t) = t := by
  obtain ⟨τ, hτ, hmap, hτσ, hστ, hgerm, hregular⟩ :=
    arcParameter_inverse_smooth hab hv hpos hvgerm
  let σ := arcParameter v a
  have hmono : StrictMonoOn σ (Icc a b) := strictMono_arcParameter hv hpos
  have hσa : σ a = 0 := by simp [σ, arcParameter]
  have hL : 0 < σ b := by
    simpa only [hσa] using hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have hσmap : MapsTo σ (Icc a b) (Icc 0 (σ b)) := by
    intro t ht
    exact ⟨by simpa only [hσa] using hmono.monotoneOn (left_mem_Icc.mpr hab.le) ht ht.1,
      hmono.monotoneOn ht (right_mem_Icc.mpr hab.le) ht.2⟩
  have hτmono : StrictMonoOn τ (Icc 0 (σ b)) := by
    intro s hs t ht hst
    by_contra hnot
    have hle := hmono.monotoneOn (hmap ht) (hmap hs) (le_of_not_gt hnot)
    change arcParameter v a (τ t) ≤ arcParameter v a (τ s) at hle
    rw [hστ t ht, hστ s hs] at hle
    exact (not_le_of_gt hst) hle
  have hτonto : SurjOn τ (Icc 0 (σ b)) (Icc a b) := by
    intro t ht
    exact ⟨σ t, hσmap ht, hτσ t ht⟩
  let node : Fin 2 → ℝ := fun i => i.val * σ b
  have hnode : Monotone node := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hL.le
  have hnfirst : node 0 = 0 := by simp [node]
  have hnlast : node (Fin.last 1) = σ b := by simp [node]
  have hnregular : ∀ i : Fin 1, RegularRealC1On τ (Icc (node i.castSucc) (node i.succ)) := by
    intro i
    fin_cases i
    simpa [node, σ] using hregular
  obtain ⟨φ, hφ⟩ := PiecewiseCurves.parameter_representation hab.le hL.le τ hmap hτmono
    hτonto 1 node hnode hnfirst hnlast hnregular
  refine ⟨φ, ?_⟩
  intro t ht
  exact (hφ (hσmap ht)).trans (hτσ t ht)

end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 800000
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The actual source length integral of a closed geodesic piece is its
constant intrinsic speed times duration, even when the total representative
has corners or unrelated values outside this closed segment. -/
theorem geodesic_piece_length_of_eqOn
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hdom : Icc a b ⊆ I.carrier)
    (γ : ℝ → M) (htrace : EqOn γ (fun t => (q t).1) (Icc a b)) :
    (∫ t in a..b, speed g γ t) = tangentNorm g (q a).1 (q a).2 * (b-a) := by
  have hconst : ∀ t ∈ Ioo a b, speed g γ t = tangentNorm g (q a).1 (q a).2 := by
    intro t ht
    have htI := hdom (Ioo_subset_Icc_self ht)
    obtain ⟨hc,e,he,hp,hd⟩ := (hq t htI).1
    have hv : P202.CurveData.HasVelocityAt S (fun r => (q r).1) t (q t).2 :=
      ⟨hc.continuousAt univ_mem,e,he,hp,hasDerivWithinAt_univ.mp hd⟩
    have hnear : (fun r => (q r).1) =ᶠ[𝓝 t] γ :=
      mem_of_superset (Icc_mem_nhds ht.1 ht.2) (fun r hr => (htrace hr).symm)
    have hvel := PiecewiseCurves.velocity_eq (PiecewiseCurves.HasVelocityAt.congr hv hnear)
    unfold speed
    rw [hvel,PiecewiseCurves.tangentNorm_cast g (q t).1 (γ t) hnear.eq_of_nhds (q t).2]
    exact GeodesicIVP.constant_speed S g C hC I q hq t htI a (hdom ⟨le_rfl,hab.le⟩)
  calc
    _ = ∫ _t in a..b, tangentNorm g (q a).1 (q a).2 :=
      intervalIntegral.integral_congr_Ioo_of_le hab.le hconst
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring


/-- The common nodes used by the finite gluing theorem are literally the
cumulative integrals of the source speed on its original closed pieces. -/
theorem geodesic_cumulative_arclength_nodes
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (I : Fin (k+1) → D13Unified.OpenTimeInterval) (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (hdom : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ (I i).carrier)
    (hpiece : ∀ i, EqOn γ (fun t => (q i t).1) (Icc (node i.castSucc) (node i.succ))) :
    let c := fun i : Fin (k+1) => tangentNorm g (q i (node i.castSucc)).1 (q i (node i.castSucc)).2
    let s := Fin.partialSum (fun i : Fin (k+1) => c i * (node i.succ - node i.castSucc))
    s 0 = 0 ∧
    (∀ i : Fin (k+1), s i.succ = s i.castSucc +
      ∫ t in node i.castSucc..node i.succ, speed g γ t) ∧
    s = Fin.partialSum (fun i : Fin (k+1) =>
      ∫ t in node i.castSucc..node i.succ, speed g γ t) := by
  dsimp only
  have hlen (i : Fin (k+1)) := geodesic_piece_length_of_eqOn g C hC (I i) (q i) (hq i)
    (hnode Fin.castSucc_lt_succ) (hdom i) γ (hpiece i)
  refine ⟨Fin.partialSum_zero _,?_,?_⟩
  · intro i
    rw [Fin.partialSum_succ,hlen i]
  · congr 1
    funext i
    exact (hlen i).symm

end P202.Geometry.GeodesicCriticalityCorners

set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology
namespace P202.Geometry.GeodesicCriticalityCorners
open P202.CriticalityData

/-- Integrable positive-almost-everywhere speed is enough for a strictly
increasing accumulated-length parameter; isolated corner values do not matter. -/
theorem strictMono_arcParameter_of_ae_pos {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable v volume a b)
    (hpos : ∀ᵐ t ∂volume, t ∈ Icc a b → 0 < v t) :
    StrictMonoOn (arcParameter v a) (Icc a b) := by
  intro x hx y hy hxy
  have hxyc : uIcc x y ⊆ uIcc a b := by
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc hx hy
  have hxyc' : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
  have hixy := hi.mono_set hxyc
  have hnn : 0 ≤ᵐ[volume.restrict (uIoc x y)] v := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hpos] with t ht hty
    exact (ht (hxyc' (uIoc_subset_uIcc hty))).le
  have hset : (Function.support v ∩ Ioc x y : Set ℝ) =ᵐ[volume] Ioc x y := by
    filter_upwards [hpos] with t ht
    apply propext
    constructor
    · exact fun h => h.2
    · intro hty
      exact ⟨ne_of_gt (ht (hxyc' (by simpa only [uIcc_of_le hxy.le] using Ioc_subset_Icc_self hty))), hty⟩
  have hp : 0 < ∫ t in x..y, v t := by
    apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnn hixy).mpr
    refine ⟨hxy, ?_⟩
    rw [measure_congr hset, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)
  have hax : IntervalIntegrable v volume a x := hi.mono_set (by
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc (left_mem_Icc.mpr hab) hx)
  have hay : IntervalIntegrable v volume a y := hi.mono_set (by
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc (left_mem_Icc.mpr hab) hy)
  have hadd := intervalIntegral.integral_interval_sub_left hay hax
  dsimp only [arcParameter]
  linarith


/-- A genuine global inverse exists for an integrable a.e.-positive speed,
including when its representative jumps or vanishes at finitely many corners. -/
theorem arcParameter_inverse_of_ae_pos {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hi : IntervalIntegrable v volume a b)
    (hpos : ∀ᵐ t ∂volume, t ∈ Icc a b → 0 < v t) :
    ∃ τ : ℝ → ℝ, Continuous τ ∧
      MapsTo τ (Icc 0 (arcParameter v a b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (arcParameter v a t) = t) ∧
      (∀ s ∈ Icc 0 (arcParameter v a b), arcParameter v a (τ s) = s) := by
  let σ := arcParameter v a
  have hmono : StrictMonoOn σ (Icc a b) := strictMono_arcParameter_of_ae_pos hab.le hi hpos
  have hσ : ContinuousOn σ (Icc a b) := by
    change ContinuousOn (fun t => ∫ r in a..t, v r) (Icc a b)
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hi (show a ∈ uIcc a b from left_mem_uIcc)
  have hσa : σ a = 0 := by simp [σ, arcParameter]
  have hL : 0 < σ b := by
    simpa only [hσa] using hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have himage : σ '' Icc a b = Icc 0 (σ b) := by
    simpa only [hσa] using hσ.image_Icc_of_monotoneOn hab.le hmono.monotoneOn
  let e : Icc a b ≃o Icc 0 (σ b) :=
    (hmono.orderIso σ (Icc a b)).trans (Set.orderIsoOfEq _ _ himage)
  have he : ∀ t : Icc a b, (e t).val = σ t.val := by intro t; rfl
  let τ : ℝ → ℝ := fun s => (e.symm (projIcc 0 (σ b) hL.le s)).val
  have hτ : Continuous τ := continuous_subtype_val.comp
    (e.symm.toHomeomorph.continuous.comp continuous_projIcc)
  have hτmap : MapsTo τ (Icc 0 (σ b)) (Icc a b) := by
    intro s hs; exact (e.symm _).property
  have hτσ : ∀ t ∈ Icc a b, τ (σ t) = t := by
    intro t ht
    have hst : σ t ∈ Icc 0 (σ b) := by rw [← himage]; exact mem_image_of_mem σ ht
    change (e.symm (projIcc 0 (σ b) hL.le (σ t))).val = t
    rw [projIcc_of_mem hL.le hst]
    change (e.symm (e ⟨t,ht⟩)).val = t
    rw [e.symm_apply_apply]
  have hστ : ∀ s ∈ Icc 0 (σ b), σ (τ s) = s := by
    intro s hs
    change σ (e.symm (projIcc 0 (σ b) hL.le s)).val = s
    rw [← he, e.apply_symm_apply, projIcc_of_mem hL.le hs]
  exact ⟨τ,hτ,hτmap,hτσ,hστ⟩


/-- On each regular smooth piece, the actual global length integral has
smooth germs with the piece's one-sided speed, ignoring representative values
at corner points. -/
theorem arcParameter_piece_smooth_germ {v w : ℝ → ℝ} {a b l u t : ℝ}
    (hi : IntervalIntegrable v volume a b) (hab : a ≤ b)
    (hsub : Icc l u ⊆ Icc a b)
    (heq : v =ᵐ[volume.restrict (Icc l u)] w) (ht : t ∈ Icc l u)
    (hwgerm : ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      x t = w t ∧ w =ᶠ[𝓝[Icc l u] t] x) :
    ∃ P : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) P t ∧
      P t = arcParameter v a t ∧ arcParameter v a =ᶠ[𝓝[Icc l u] t] P ∧
      HasDerivAt P (w t) t := by
  obtain ⟨x, hx, hxt, hxeq⟩ := hwgerm
  let P : ℝ → ℝ := fun r => arcParameter v a t + ∫ y in t..r, x y
  obtain ⟨hPsmooth, hPderiv⟩ := primitive_contDiffAt hx
  refine ⟨P, contDiffAt_const.add hPsmooth, ?_, ?_, ?_⟩
  · simp [P]
  · obtain ⟨U, hUt, hUeq⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hxeq
    obtain ⟨l', u', htl, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hUt
    have hloc' : ∀ᶠ r in 𝓝 t, r ∈ Ioo l' u' := Ioo_mem_nhds htl.1 htl.2
    have hloc : ∀ᶠ r in 𝓝[Icc l u] t, r ∈ Ioo l' u' :=
      hloc'.filter_mono nhdsWithin_le_nhds
    have hae : ∀ᵐ y ∂volume, y ∈ Icc l u → v y = w y :=
      (ae_restrict_iff' measurableSet_Icc).mp heq
    filter_upwards [self_mem_nhdsWithin, hloc] with r hr hrloc
    have hIntvw : (∫ y in t..r, v y) = ∫ y in t..r, w y := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hae] with y hy hyt
      exact hy (uIcc_subset_Icc ht hr (uIoc_subset_uIcc hyt))
    have hIntwx : (∫ y in t..r, w y) = ∫ y in t..r, x y := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact hUeq ⟨hlu (ordConnected_Ioo.uIcc_subset htl hrloc hy),
        uIcc_subset_Icc ht hr hy⟩
    have hai : IntervalIntegrable v volume a r := hi.mono_set (by
      rw [uIcc_of_le hab]
      exact uIcc_subset_Icc (left_mem_Icc.mpr hab) (hsub hr))
    have hat : IntervalIntegrable v volume a t := hi.mono_set (by
      rw [uIcc_of_le hab]
      exact uIcc_subset_Icc (left_mem_Icc.mpr hab) (hsub ht))
    have hadd := intervalIntegral.integral_interval_sub_left hai hat
    change (∫ y in a..r, v y) = (∫ y in a..t, v y) + ∫ y in t..r, x y
    linarith
  · simpa only [P, hxt] using hPderiv.const_add (arcParameter v a t)


/-- Finite regular speed pieces determine one actual global arc-length
parameter, with an accepted piecewise regular inverse and exact inverse
one-sided derivatives on every arc-length piece. -/
theorem finite_arcParameter_inverse
    {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hi : IntervalIntegrable v volume a b)
    (hpos : ∀ᵐ t ∂volume, t ∈ Icc a b → 0 < v t)
    (k : ℕ) (node : Fin (k+1) → ℝ) (hnode : Monotone node)
    (hfirst : node 0 = a) (hlast : node (Fin.last k) = b)
    (w : Fin k → ℝ → ℝ)
    (hwp : ∀ i t, t ∈ Icc (node i.castSucc) (node i.succ) → 0 < w i t)
    (hweq : ∀ i, v =ᵐ[volume.restrict (Icc (node i.castSucc) (node i.succ))] w i)
    (hwgerm : ∀ i t, t ∈ Icc (node i.castSucc) (node i.succ) →
      ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧ x t = w i t ∧
        w i =ᶠ[𝓝[Icc (node i.castSucc) (node i.succ)] t] x) :
    ∃ φ : P202.CurveData.PiecewiseRegularIncreasing a b 0 (arcParameter v a b),
      (∀ t ∈ Icc a b, φ (arcParameter v a t) = t) ∧
      (∀ i s, s ∈ Icc (arcParameter v a (node i.castSucc))
          (arcParameter v a (node i.succ)) →
        HasDerivWithinAt φ (w i (φ s))⁻¹
          (Icc (arcParameter v a (node i.castSucc))
            (arcParameter v a (node i.succ))) s) := by
  let σ := arcParameter v a
  have hmono : StrictMonoOn σ (Icc a b) := strictMono_arcParameter_of_ae_pos hab.le hi hpos
  have hσa : σ a = 0 := by simp [σ, arcParameter]
  have hL : 0 < σ b := by
    simpa only [hσa] using hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have hσmap : MapsTo σ (Icc a b) (Icc 0 (σ b)) := by
    intro t ht
    exact ⟨by simpa only [hσa] using hmono.monotoneOn (left_mem_Icc.mpr hab.le) ht ht.1,
      hmono.monotoneOn ht (right_mem_Icc.mpr hab.le) ht.2⟩
  obtain ⟨τ,hτ,hτmap,hτσ,hστ⟩ := arcParameter_inverse_of_ae_pos hab hi hpos
  have hnmem (j : Fin (k+1)) : node j ∈ Icc a b := by
    constructor
    · rw [← hfirst]
      exact hnode (Fin.zero_le j)
    · rw [← hlast]
      exact hnode (Fin.le_last j)
  have hsub (i : Fin k) : Icc (node i.castSucc) (node i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hnmem i.castSucc).1 (hnmem i.succ).2
  let K (i : Fin k) := Icc (σ (node i.castSucc)) (σ (node i.succ))
  have hKsub (i : Fin k) : K i ⊆ Icc 0 (σ b) :=
    Icc_subset_Icc (hσmap (hnmem i.castSucc)).1 (hσmap (hnmem i.succ)).2
  have hτpiece (i : Fin k) : MapsTo τ (K i) (Icc (node i.castSucc) (node i.succ)) := by
    intro s hs
    have hsfull := hKsub i hs
    have hτs := hτmap hsfull
    constructor
    · by_contra hnot
      have hlt := hmono hτs (hnmem i.castSucc) (lt_of_not_ge hnot)
      change arcParameter v a (τ s) < σ (node i.castSucc) at hlt
      rw [hστ s hsfull] at hlt
      exact (not_lt_of_ge hs.1) hlt
    · by_contra hnot
      have hlt := hmono (hnmem i.succ) hτs (lt_of_not_ge hnot)
      change σ (node i.succ) < arcParameter v a (τ s) at hlt
      rw [hστ s hsfull] at hlt
      exact (not_lt_of_ge hs.2) hlt
  have hσgerm (i : Fin k) (t : ℝ) (ht : t ∈ Icc (node i.castSucc) (node i.succ)) :=
    arcParameter_piece_smooth_germ hi hab.le (hsub i) (hweq i) ht (hwgerm i t ht)
  have hτregular (i : Fin k) : P202.CurveData.RegularRealC1On τ (K i) := by
    intro s hs
    obtain ⟨ψ,hψ,hψs,hψeq,hψpos⟩ := inverse_smooth_germ hτ.continuousOn (hτpiece i)
      (fun s hs => hστ s (hKsub i hs)) (hσgerm i) (hwp i) hs
    exact ⟨ψ,hψ.of_le (by simp),hψs,hψeq,hψpos⟩
  have hτderiv (i : Fin k) (s : ℝ) (hs : s ∈ K i) :
      HasDerivWithinAt τ (w i (τ s))⁻¹ (K i) s := by
    obtain ⟨P,hP,hPt,hσP,hdP⟩ := hσgerm i (τ s) (hτpiece i hs)
    have hσder : HasDerivWithinAt σ (w i (τ s))
        (Icc (node i.castSucc) (node i.succ)) (τ s) :=
      hdP.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hσP (hτpiece i hs)
    apply HasDerivWithinAt.of_local_inverse
      (hτ.continuousAt.continuousWithinAt.tendsto_nhdsWithin (hτpiece i)) hσder
      (ne_of_gt (hwp i (τ s) (hτpiece i hs))) hs
    exact eventually_nhdsWithin_of_forall (fun r hr => hστ r (hKsub i hr))
  have hτmono : StrictMonoOn τ (Icc 0 (σ b)) := by
    intro s hs t ht hst
    by_contra hnot
    have hle := hmono.monotoneOn (hτmap ht) (hτmap hs) (le_of_not_gt hnot)
    change arcParameter v a (τ t) ≤ arcParameter v a (τ s) at hle
    rw [hστ t ht, hστ s hs] at hle
    exact (not_le_of_gt hst) hle
  have hτonto : SurjOn τ (Icc 0 (σ b)) (Icc a b) :=
    fun t ht => ⟨σ t,hσmap ht,hτσ t ht⟩
  have hσnode : Monotone (σ ∘ node) := by
    intro i j hij
    exact hmono.monotoneOn (hnmem i) (hnmem j) (hnode hij)
  have hσfirst : (σ ∘ node) 0 = 0 := by simp only [Function.comp_apply,hfirst,hσa]
  have hσlast : (σ ∘ node) (Fin.last k) = σ b := by simp only [Function.comp_apply,hlast]
  obtain ⟨φ,hφ⟩ := PiecewiseCurves.parameter_representation hab.le hL.le τ hτmap hτmono
    hτonto k (σ ∘ node) hσnode hσfirst hσlast hτregular
  refine ⟨φ, fun t ht => (hφ (hσmap ht)).trans (hτσ t ht), ?_⟩
  intro i s hs
  have hφs : φ s = τ s := hφ (hKsub i hs)
  rw [hφs]
  apply (hτderiv i s hs).congr_of_eventuallyEq_of_mem _ hs
  exact eventually_nhdsWithin_of_forall (fun r hr => hφ (hKsub i hr))

end P202.Geometry.GeodesicCriticalityCorners

set_option maxHeartbeats 1000000
namespace P202.Geometry.GeodesicCriticalityCorners
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Every finite regular piecewise smooth intrinsic curve has an actual
arc-length reparametrization in the accepted compact-parameter interface.
Its actual one-sided velocities are the original normalized piece velocities,
and have norm one on every closed arc-length piece, including both ends. -/
theorem regular_piecewise_arc_length_parameterization
    (g : RiemannianMetric S) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (γ t)
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ) t)) :
    let σ := arcParameter (speed g γ) (node 0)
    ∃ φ : PiecewiseRegularIncreasing (node 0) (node (Fin.last (k+1))) 0
        (σ (node (Fin.last (k+1)))),
      (∀ t ∈ Icc (node 0) (node (Fin.last (k+1))), φ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ (node (Fin.last (k+1)))), σ (φ s) = s) ∧
      ∀ (i : Fin (k+1)) (s : ℝ), s ∈ Icc (σ (node i.castSucc)) (σ (node i.succ)) →
        HasVelocityWithinAt S (γ ∘ φ) (Icc (σ (node i.castSucc)) (σ (node i.succ))) s
          (unitVelocity g (fun z : ℝ × ℝ => γ z.2)
            (node i.castSucc) (node i.succ) (φ s)) ∧
        tangentNorm g (γ (φ s))
          (unitVelocity g (fun z : ℝ × ℝ => γ z.2)
            (node i.castSucc) (node i.succ) (φ s)) = 1 := by
  dsimp only
  let σ := arcParameter (speed g γ) (node 0)
  let V := fun i : Fin (k+1) => segmentVelocity S (fun z : ℝ × ℝ => γ z.2)
    (node i.castSucc) (node i.succ)
  let w := fun (i : Fin (k+1)) (t : ℝ) => tangentNorm g (γ t) (V i t)
  have hab : node 0 < node (Fin.last (k+1)) := hnode (by change 0 < k+1; omega)
  have hpiece (i : Fin (k+1)) : node i.castSucc < node i.succ := hnode Fin.castSucc_lt_succ
  have hF (i : Fin (k+1)) : SmoothVariationOn S (fun z : ℝ × ℝ => γ z.2) 1
      (node i.castSucc) (node i.succ) := smooth_curve_constant_variation (hγ i) Subset.rfl
  have hi : IntervalIntegrable (speed g γ) volume (node 0) (node (Fin.last (k+1))) := by
    apply PiecewiseCurves.intervalIntegrable_of_partition node
    intro i
    exact PiecewiseCurves.speed_integrable g
      (FirstVariation.variationSlice (s := 0) (hF i) (by simp) (hpiece i).le)
  have hspeed (i : Fin (k+1)) {t : ℝ} (ht : t ∈ Ioo (node i.castSucc) (node i.succ)) :
      speed g γ t = w i t := by
    dsimp only [w, V, speed]
    rw [FirstVariation.segmentVelocity_eq_velocity (hF i) zero_lt_one ht]
  have hnotnode : ∀ᵐ t ∂volume, ∀ j : Fin (k+2), t ≠ node j := by
    filter_upwards [(Set.finite_range node).countable.ae_notMem volume] with t ht j heq
    exact ht ⟨j,heq.symm⟩
  have hposae : ∀ᵐ t ∂volume,
      t ∈ Icc (node 0) (node (Fin.last (k+1))) → 0 < speed g γ t := by
    filter_upwards [hnotnode] with t htn ht
    obtain ⟨i, hi⟩ := PiecewiseCurves.exists_piece_between_nodes node
      (lt_of_le_of_ne ht.1 (htn 0).symm) (lt_of_le_of_ne ht.2 (htn (Fin.last (k+1)))) htn
    rw [hspeed i hi]
    exact hpos i t (Ioo_subset_Icc_self hi)
  have hweq (i : Fin (k+1)) : speed g γ =ᵐ[volume.restrict
      (Icc (node i.castSucc) (node i.succ))] w i := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [volume.ae_ne (node i.castSucc),volume.ae_ne (node i.succ)]
      with t htl htr ht
    exact hspeed i ⟨lt_of_le_of_ne ht.1 htl.symm,lt_of_le_of_ne ht.2 htr⟩
  have hwgerm (i : Fin (k+1)) (t : ℝ) (ht : t ∈ Icc (node i.castSucc) (node i.succ)) :
      ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧ x t = w i t ∧
        w i =ᶠ[𝓝[Icc (node i.castSucc) (node i.succ)] t] x :=
    smooth_field_norm_germ g (smooth_segmentVelocity (hF i) zero_lt_one (hpiece i)) (hpos i) ht
  obtain ⟨φ,hφinv,hφderiv⟩ := finite_arcParameter_inverse hab hi hposae (k+1) node
    hnode.monotone rfl rfl w hpos hweq hwgerm
  have hmono : StrictMonoOn σ (Icc (node 0) (node (Fin.last (k+1)))) :=
    strictMono_arcParameter_of_ae_pos hab.le hi hposae
  have hσa : σ (node 0) = 0 := by simp [σ,arcParameter]
  have hσmap : MapsTo σ (Icc (node 0) (node (Fin.last (k+1))))
      (Icc 0 (σ (node (Fin.last (k+1))))) := by
    intro t ht
    exact ⟨by simpa only [hσa] using hmono.monotoneOn (left_mem_Icc.mpr hab.le) ht ht.1,
      hmono.monotoneOn ht (right_mem_Icc.mpr hab.le) ht.2⟩
  have hnmem (j : Fin (k+2)) : node j ∈ Icc (node 0) (node (Fin.last (k+1))) :=
    ⟨hnode.monotone (Fin.zero_le j),hnode.monotone (Fin.le_last j)⟩
  have hφmap := PiecewiseCurves.parameter_mapsTo φ
  have hφmono := PiecewiseCurves.parameter_strictMonoOn φ
  have hright (s : ℝ) (hs : s ∈ Icc 0 (σ (node (Fin.last (k+1))))) : σ (φ s) = s := by
    apply hφmono.injOn (hσmap (hφmap hs)) hs
    exact hφinv (φ s) (hφmap hs)
  have hφpiece (i : Fin (k+1)) : MapsTo φ (Icc (σ (node i.castSucc)) (σ (node i.succ)))
      (Icc (node i.castSucc) (node i.succ)) := by
    intro s hs
    have hsfull : s ∈ Icc 0 (σ (node (Fin.last (k+1)))) :=
      ⟨(hσmap (hnmem i.castSucc)).1.trans hs.1,hs.2.trans (hσmap (hnmem i.succ)).2⟩
    constructor
    · have hle := hφmono.monotoneOn (hσmap (hnmem i.castSucc)) hsfull hs.1
      rw [hφinv _ (hnmem i.castSucc)] at hle
      exact hle
    · have hle := hφmono.monotoneOn hsfull (hσmap (hnmem i.succ)) hs.2
      rw [hφinv _ (hnmem i.succ)] at hle
      exact hle
  refine ⟨φ,hφinv,hright,?_⟩
  intro i s hs
  refine ⟨?_,?_⟩
  · exact normalized_velocity_reparam g
      (FirstVariation.segmentVelocity_spec (hF i) zero_lt_one (hφpiece i hs))
      (hφderiv i s hs) (hφpiece i)
  · exact normalized_norm g _ _ (hpos i (φ s) (hφpiece i hs))

end P202.Geometry.GeodesicCriticalityCorners

namespace P202.Geometry.GeodesicCriticalityCorners
universe u

/-- The full source theorem, retaining its general endpoint/corner formulas
and all criticality, arc-length and minimizer conclusions. -/
theorem complete_first_variation :
    P202Specs.Geometry.GeodesicCriticalityCorners.complete_first_variationType.{u} :=
  ⟨FirstVariation.first_variation_energy,
    FirstVariation.first_variation_length,
    FirstVariation.piecewise_energy,
    FirstVariation.piecewise_length,
    FirstVariation.length_sq_le_energy,
    FirstVariation.constant_speed_equality,
    FirstVariation.equality_iff_constant_speed,
    FirstVariation.degenerate,
    realize_smooth_field,
    energy_criticality_iff,
    length_criticality_iff_arclength_geodesic,
    minimizing_broken_geodesic_no_corner,
    minimizing_broken_geodesic_global_gluing,
    geodesic_cumulative_arclength_nodes,
    regular_piecewise_arc_length_parameterization,
    minimizing_regular_curve_no_corner⟩
end P202.Geometry.GeodesicCriticalityCorners
