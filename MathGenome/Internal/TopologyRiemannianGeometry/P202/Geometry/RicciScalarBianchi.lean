import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RicciScalarBianchi
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SecondBianchi
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.Geometry.RicciScalarBianchi
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.SectionExtensionData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.CurvatureData P202.SecondBianchiData P202.RicciData
open Filter
open scoped Topology
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable abbrev ricci := @P202.RicciData.ricci
noncomputable abbrev scalarCurvature := @P202.RicciData.scalarCurvature
noncomputable abbrev ricciDerivative := @P202.RicciData.ricciDerivative
noncomputable abbrev divergenceRicci := @P202.RicciData.divergenceRicci

theorem trace_basis {V : Type v} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (A : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ V A = ∑ i, b.repr (A (b i)) i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

theorem ricci_basis (T : CurvatureTensor S) (p : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace S p)) (Y Z : TangentSpace S p) :
    ricci T p Y Z = ∑ i, b.repr (T.val p (b i) Y Z) i :=
  trace_basis b _

theorem orthonormal_repr (g : RiemannianMetric S) (p : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace S p))
    (hb : IsOrthonormalBasis g p b) (v : TangentSpace S p) (i : Fin n) :
    b.repr v i = pairing g p (b i) v := by
  classical
  change ∀ i j, pairing g p (b i) (b j) = if i = j then 1 else 0 at hb
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem metricTrace_orthonormal (g : RiemannianMetric S) (p : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace S p))
    (hb : IsOrthonormalBasis g p b) (B : LinearMap.BilinForm ℝ (TangentSpace S p)) :
    metricTrace g p B = ∑ i, B (b i) (b i) := by
  unfold metricTrace
  rw [trace_basis b]
  apply Finset.sum_congr rfl
  intro i _
  rw [orthonormal_repr g p b hb]
  change pairing g p (b i)
    ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm
      (B (b i))) = _
  calc
    _ = pairing g p ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm
      (B (b i))) (b i) := g.symmetric p _ _
    _ = _ := ?_
  change (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p)
    ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm
      (B (b i))) (b i) = _
  rw [LinearEquiv.apply_symm_apply]

theorem orthonormal_contractions :
    P202Specs.Geometry.RicciScalarBianchi.orthonormal_contractionsType.{u} := by
  intro n a M _ S g T p b hb
  refine ⟨?_, metricTrace_orthonormal g p b hb (ricci T p)⟩
  intro Y Z
  rw [ricci_basis T p b]
  apply Finset.sum_congr rfl
  intro i _
  rw [orthonormal_repr g p b hb]
  exact g.symmetric p _ _

/-- Existence of an orthonormal basis uses positive definiteness only, and
also applies to the zero-dimensional tangent space. -/
theorem exists_orthonormal_basis (g : RiemannianMetric S) (p : M) :
    ∃ b : Module.Basis (Fin n) ℝ (TangentSpace S p), IsOrthonormalBasis g p b := by
  classical
  letI : AddCommGroup (TangentSpace S p) := Module.addCommMonoidToAddCommGroup ℝ
  letI : InnerProductSpace.Core ℝ (TangentSpace S p) := {
    inner := fun x y => pairing g p x y
    conj_inner_symm := fun x y => g.symmetric p y x
    re_inner_nonneg := fun x => by
      change 0 ≤ pairing g p x x
      by_cases hx : x = 0
      · subst x; simp [pairing]
      · exact le_of_lt (g.positive p x hx)
    add_left := fun x y z => (g.form p).map_add₂ x y z
    smul_left := fun x y c => (g.form p).map_smul₂ c x y
    definite := fun x hx => by
      by_contra h
      exact (ne_of_gt (g.positive p x h)) hx }
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := TangentSpace S p)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (TangentSpace S p))
  letI := SmoothManifolds.ConstantRankBundles.finite_fiber (tangentBundle S) p
  let b := (stdOrthonormalBasis ℝ (TangentSpace S p)).reindex
    (finCongr (SmoothManifolds.ConstantRankBundles.finrank_fiber (tangentBundle S) p))
  refine ⟨b.toBasis, ?_⟩
  intro i j
  exact b.inner_eq_ite i j

theorem ricci_symmetric : P202Specs.Geometry.RicciScalarBianchi.ricci_symmetricType.{u} := by
  intro n a M _ S g C hC T hT p Y Z
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g p
  rw [(orthonormal_contractions g T p b hb).1,
    (orthonormal_contractions g T p b hb).1]
  apply Finset.sum_congr rfl
  intro i _
  have h₁ := (CurvatureAlgebra.symmetries g C hC T hT p (b i) Y Z (b i)).2.2
  have h₂ := (CurvatureAlgebra.symmetries g C hC T hT p Z (b i) (b i) Y).1
  have h₃ := (CurvatureAlgebra.symmetries g C hC T hT p (b i) Z (b i) Y).2.1
  linarith

/-- Smoothness of the trace of a smooth family of endomorphisms, tested on
smooth sections. A local trivialization is used only inside the proof. -/
theorem trace_smooth (A : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p)
    (hA : ∀ X : Field S, SmoothSection (tangentBundle S) (fun p => A p (X.val p))) :
    (fun p => LinearMap.trace ℝ (TangentSpace S p) (A p)) ∈
      SmoothManifolds.globalSmoothAlgebra S := by
  classical
  apply (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr
  intro p
  apply (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
  let B := tangentBundle S
  obtain ⟨i, hi⟩ := B.covers p
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hi⟩
  have hs : VectorSmoothAt S.smoothStructure.val
      (fun q => ∑ j : Fin n, ((B.trivialization i) ⟨q, A q ((e j).val q)⟩).2 j) p := by
    apply VectorSmoothAt.sum
    intro j
    exact (SmoothManifolds.SectionExtension.coordinates_smoothAt B i hi
      (hA (e j) p)).postcomp (ContinuousLinearMap.proj j).contDiff
  apply hs.congr
  filter_upwards [ho.mem_nhds hi, Filter.eventually_all.mpr he] with q hq heq
  rw [trace_basis (b.basis ⟨q, hq⟩)]
  apply Finset.sum_congr rfl
  intro j _
  rw [heq j, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
  change ((B.trivialization i) ⟨q, A q (b.section_ j ⟨q, hq⟩)⟩).2 j =
    (b.basis ⟨q, hq⟩).equivFun (A q ((b.basis ⟨q, hq⟩) j)) j
  rw [LeviCivita.trivializationFrame_coordinates]
  rfl

theorem ricci_smooth : P202Specs.Geometry.RicciScalarBianchi.ricci_smoothType.{u} := by
  intro n a M _ S T Y Z
  exact trace_smooth (fun p => {
    toFun := fun x => T.val p x (Y.val p) (Z.val p)
    map_add' := by intros; simp only [map_add, LinearMap.add_apply]
    map_smul' := by intros; simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] })
      (fun X => T.smooth X Y Z)

theorem scalar_smooth : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u} := by
  intro n a M _ S g T
  apply trace_smooth
  intro X
  let lam := fun p => ricci T p (X.val p)
  have hl : SmoothSection (cotangentBundle S) lam := by
    apply InducedConnections.dual_smooth_of_evaluations (tangentBundle S) (cotangentDual S)
    intro Z p
    exact (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
      ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp (ricci_smooth T X Z) p)
  let I := SmoothManifolds.MetricSplittings.metricIso (tangentBundle S) g (cotangentDual S)
  intro p
  exact SmoothManifolds.manifoldContDiffAt_comp
    (cotangentBundle S).totalManifold.smoothStructure.property.1.1
    (hl p) (I.inverse_smooth ⟨p, lam p⟩)

theorem metricTrace_coordinates (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (p : M)
    (hp : p ∈ (tangentBundle S).baseSet c)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p)) :
    metricTrace g p B = ∑ i, ∑ j, (metricMatrix g c p)⁻¹ i j *
      B (coordinateVector c i p) (coordinateVector c j p) := by
  classical
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let sharp := (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm
  unfold metricTrace
  rw [trace_basis (b.basis ⟨p, hp⟩)]
  apply Finset.sum_congr rfl
  intro i _
  have hb (j : Fin n) : (b.basis ⟨p, hp⟩) j = coordinateVector c j p := by
    change (b.section_ j ⟨p, hp⟩) = _
    exact LeviCivita.trivializationFrame_section c j ⟨p, hp⟩
  change (b.basis ⟨p, hp⟩).equivFun (sharp (B ((b.basis ⟨p, hp⟩) i))) i = _
  rw [LeviCivita.trivializationFrame_coordinates, hb,
    LeviCivita.coordinates_from_metric g c p hp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p)
    (sharp (B (coordinateVector c i p))) (coordinateVector c j p) = _
  rw [LinearEquiv.apply_symm_apply]

theorem coordinate_contractions :
    P202Specs.Geometry.RicciScalarBianchi.coordinate_contractionsType.{u} := by
  intro n a M _ S g C T c p hp
  refine ⟨metricTrace_coordinates g c p hp (ricci T p), ?_⟩
  intro Z
  exact metricTrace_coordinates g c p hp _

@[simp] theorem globalSmooth_sum_apply {ι : Type*} [Fintype ι]
    (f : ι → GlobalSmooth S) (p : M) : (∑ i, f i).val p = ∑ i, (f i).val p :=
  map_sum (SmoothManifolds.TangentData.globalEvaluation S p) _ _

set_option maxHeartbeats 3000000 in
/-- Covariant differentiation commutes with the ordinary endomorphism trace.
The two connection-matrix terms cancel after interchanging the finite indices. -/
theorem trace_derivative (C : Connection (tangentBundle S)) (X : Field S)
    (A : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace S q)
    (hA : ∀ Y : Field S, SmoothSection (tangentBundle S) (fun q => A q (Y.val q)))
    (K : (q : M) → TangentSpace S q →ₗ[ℝ] TangentSpace S q)
    (hK : ∀ (Y : Field S) (q : M), K q (Y.val q) =
      (C.cov X ⟨fun q => A q (Y.val q), hA Y⟩).val q - A q ((C.cov X Y).val q))
    (p : M) :
    scalarDerivative S (fun q => LinearMap.trace ℝ (TangentSpace S q) (A q)) p (X.val p) =
      LinearMap.trace ℝ (TangentSpace S p) (K p) := by
  classical
  let B := tangentBundle S
  obtain ⟨i, hi⟩ := B.covers p
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hi⟩
  let Ae (j : Fin n) : Field S := ⟨fun q => A q ((e j).val q), hA (e j)⟩
  have hf (j k : Fin n) : ∃ f : GlobalSmooth S, f.val =ᶠ[𝓝 p]
      (fun q => ((B.trivialization i) ⟨q, (Ae j).val q⟩).2 k) := by
    have h := (SmoothManifolds.SectionExtension.coordinates_smoothAt B i hi
      ((Ae j).property p)).postcomp (ContinuousLinearMap.proj k).contDiff
    obtain ⟨f, hf, heq⟩ := SmoothManifolds.exists_global_representative S p _
      ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr h)
    exact ⟨⟨f, (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr hf⟩, heq⟩
  choose f hf using hf
  let bp := b.basis ⟨p, hi⟩
  have hep (j : Fin n) : (e j).val p = bp j := by
    rw [(he j).self_of_nhds, SmoothManifolds.SectionExtension.totalSection_of_mem _ p hi]
    exact (b.basis_eq _ _).symm
  have hfp (j k : Fin n) : (f j k).val p = bp.equivFun ((Ae j).val p) k := by
    rw [(hf j k).eq_of_nhds]
    change _ = bp.equivFun ((Ae j).val p) k
    rw [LeviCivita.trivializationFrame_coordinates]
    rfl
  have hrep (j : Fin n) : ∀ᶠ q in 𝓝 p, (Ae j).val q =
      (∑ k, mulSection (f j k) (e k)).val q := by
    filter_upwards [ho.mem_nhds hi, Filter.eventually_all.mpr he,
      Filter.eventually_all.mpr (hf j)] with q hq heq hfq
    simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply]
    simp_rw [hfq, heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    have hh := (b.basis ⟨q, hq⟩).sum_repr ((Ae j).val q)
    conv_lhs => rw [← hh]
    apply Finset.sum_congr rfl
    intro k _
    rw [b.basis_eq]
    congr 1
  have htr : (∑ j, f j j).val =ᶠ[𝓝 p]
      (fun q => LinearMap.trace ℝ (TangentSpace S q) (A q)) := by
    filter_upwards [ho.mem_nhds hi, Filter.eventually_all.mpr he,
      Filter.eventually_all.mpr (fun j => Filter.eventually_all.mpr (hf j))]
      with q hq heq hfq
    simp only [globalSmooth_sum_apply]
    rw [trace_basis (b.basis ⟨q, hq⟩)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hfq j j]
    change _ = (b.basis ⟨q, hq⟩).equivFun (A q ((b.basis ⟨q, hq⟩) j)) j
    rw [LeviCivita.trivializationFrame_coordinates]
    change (B.fiberCoordinates i q hq) (A q ((e j).val q)) j =
      (B.fiberCoordinates i q hq) (A q ((b.basis ⟨q, hq⟩) j)) j
    rw [heq j, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq, b.basis_eq]
  have hd (j : Fin n) : bp.equivFun ((C.cov X (Ae j)).val p) j =
      (act S X (f j j)).val p + ∑ k, (f j k).val p *
        bp.equivFun ((C.cov X (e k)).val p) j := by
    rw [ConnectionForms.locality_section B C X _ _ p (hrep j),
      ConnectionForms.finite_expansion B C]
    simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.section_add_apply,
      ConnectionForms.mulSection_apply, map_sum, map_add, map_smul, Finset.sum_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, hep,
      Module.Basis.equivFun_self]
    simp [mul_ite]
    rfl
  have hka (j : Fin n) : bp.equivFun (A p ((C.cov X (e j)).val p)) j =
      ∑ k, bp.equivFun ((C.cov X (e j)).val p) k * (f k j).val p := by
    conv_lhs => rw [← bp.sum_repr ((C.cov X (e j)).val p)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [hfp]
    simp only [Ae, hep]
    rfl
  rw [ConnectionForms.scalarDerivative_representative _ (∑ j, f j j) p htr,
    ← ConnectionForms.act_apply, map_sum, globalSmooth_sum_apply,
    trace_basis bp]
  have hc : (∑ j, ∑ k, (f j k).val p * bp.equivFun ((C.cov X (e k)).val p) j) =
      ∑ j, ∑ k, bp.equivFun ((C.cov X (e j)).val p) k * (f k j).val p := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  have hk (j : Fin n) : bp.equivFun (K p (bp j)) j =
      (act S X (f j j)).val p +
        (∑ k, (f j k).val p * bp.equivFun ((C.cov X (e k)).val p) j) -
        (∑ k, bp.equivFun ((C.cov X (e j)).val p) k * (f k j).val p) := by
    rw [← hep j, hK]
    change bp.equivFun ((C.cov X (Ae j)).val p - A p ((C.cov X (e j)).val p)) j = _
    rw [LeviCivita.tangent_sub_as_add]
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hd, hka]
    ring
  change (∑ j, (act S X (f j j)).val p) = ∑ j, bp.equivFun (K p (bp j)) j
  simp_rw [hk]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hc]
  ring

noncomputable def curvatureEndomorphism {V : Type v} [AddCommMonoid V] [Module ℝ V]
    (A : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) (Y Z : V) : V →ₗ[ℝ] V :=
  (A.flip Y).flip Z

theorem ricci_derivative_rule :
    P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u} := by
  intro n a M _ S C T X Y Z p
  let A := fun q => curvatureEndomorphism (T.val q) (Y.val q) (Z.val q)
  let K := fun q =>
    curvatureEndomorphism (covariantDerivative C T q (X.val q)) (Y.val q) (Z.val q) +
    curvatureEndomorphism (T.val q) ((C.cov X Y).val q) (Z.val q) +
    curvatureEndomorphism (T.val q) (Y.val q) ((C.cov X Z).val q)
  have hA : ∀ U : Field S, SmoothSection (tangentBundle S) (fun q => A q (U.val q)) :=
    fun U => T.smooth U Y Z
  have hK (U : Field S) (q : M) : K q (U.val q) =
      (C.cov X ⟨fun q => A q (U.val q), hA U⟩).val q - A q ((C.cov X U).val q) := by
    have hd := (SecondBianchi.derivative_rule C T q).1 X U Y Z
    change _ = (tensorDerivativeField C T X U Y Z).val q at hd
    simp only [tensorDerivativeField, ConnectionForms.section_add_apply,
      ConnectionForms.section_smul_apply, SecondBianchi.tensorSection_apply] at hd
    change covariantDerivative C T q (X.val q) (U.val q) (Y.val q) (Z.val q) +
      T.val q (U.val q) ((C.cov X Y).val q) (Z.val q) +
      T.val q (U.val q) (Y.val q) ((C.cov X Z).val q) = _
    rw [hd]
    change _ = (C.cov X (tensorSection T U Y Z)).val q -
      T.val q ((C.cov X U).val q) (Y.val q) (Z.val q)
    module
  have h := trace_derivative C X A hA K hK p
  change scalarDerivative S (fun q => ricci T q (Y.val q) (Z.val q)) p (X.val p) =
    LinearMap.trace ℝ (TangentSpace S p) (_ + _ + _) at h
  rw [map_add, map_add] at h
  change _ = ricciDerivative C T p (X.val p) (Y.val p) (Z.val p) +
    ricci T p ((C.cov X Y).val p) (Z.val p) +
    ricci T p (Y.val p) ((C.cov X Z).val p) at h
  linarith

@[simp] theorem sharp_pairing (g : RiemannianMetric S) (p : M)
    (lam : Module.Dual ℝ (TangentSpace S p)) (v : TangentSpace S p) :
    pairing g p
      ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm lam) v =
        lam v := by
  change (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p)
    ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm lam) v = _
  rw [LinearEquiv.apply_symm_apply]

noncomputable def raisedRicci (g : RiemannianMetric S) (T : CurvatureTensor S) (p : M) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S p :=
  ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm.toLinearMap).comp
    (ricci T p)

theorem raisedRicci_smooth (g : RiemannianMetric S) (T : CurvatureTensor S)
    (Y : Field S) : SmoothSection (tangentBundle S) (fun p => raisedRicci g T p (Y.val p)) := by
  let lam := fun p => ricci T p (Y.val p)
  have hl : SmoothSection (cotangentBundle S) lam := by
    apply InducedConnections.dual_smooth_of_evaluations (tangentBundle S) (cotangentDual S)
    intro Z p
    exact (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
      ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp (ricci_smooth T Y Z) p)
  let I := SmoothManifolds.MetricSplittings.metricIso (tangentBundle S) g (cotangentDual S)
  intro p
  exact SmoothManifolds.manifoldContDiffAt_comp
    (cotangentBundle S).totalManifold.smoothStructure.property.1.1
    (hl p) (I.inverse_smooth ⟨p, lam p⟩)

theorem scalar_derivative_rule :
    P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u} := by
  intro n a M _ S g C hC T p x
  obtain ⟨X, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p x
  let A := raisedRicci g T
  let hA := raisedRicci_smooth g T
  let K := fun q =>
    ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g q).symm.toLinearMap).comp
      (ricciDerivative C T q (X.val q))
  have hK (Y : Field S) (q : M) : K q (Y.val q) =
      (C.cov X ⟨fun q => A q (Y.val q), hA Y⟩).val q - A q ((C.cov X Y).val q) := by
    apply LeviCivita.pairing_ext g q
    intro Z
    let AY : Field S := ⟨fun q => A q (Y.val q), hA Y⟩
    have hp (r : M) (v : TangentSpace S r) :
        pairing g r (A r (Y.val r)) v = ricci T r (Y.val r) v := sharp_pairing g r _ v
    have he : (fun r => pairing g r (AY.val r) (Z.val r)) =
        (fun r => ricci T r (Y.val r) (Z.val r)) := funext (fun r => hp r _)
    have hm := hC.2 X AY Z q
    rw [he] at hm
    have hr := ricci_derivative_rule C T X Y Z q
    change pairing g q ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g q).symm
      (ricciDerivative C T q (X.val q) (Y.val q))) (Z.val q) = _
    rw [sharp_pairing, LeviCivita.tangent_sub_as_add]
    simp only [pairing, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    have hpa : pairing g q (A q ((C.cov X Y).val q)) (Z.val q) =
        ricci T q ((C.cov X Y).val q) (Z.val q) := sharp_pairing g q _ _
    change ricciDerivative C T q (X.val q) (Y.val q) (Z.val q) =
      pairing g q ((C.cov X AY).val q) (Z.val q) +
        (-1 : ℝ) * pairing g q (A q ((C.cov X Y).val q)) (Z.val q)
    rw [hpa]
    change _ = pairing g q ((C.cov X AY).val q) (Z.val q) +
      pairing g q (A q (Y.val q)) ((C.cov X Z).val q) at hm
    rw [hp] at hm
    linarith
  exact trace_derivative C X A hA K hK p

noncomputable def curvatureFunction (g : RiemannianMetric S) (T : CurvatureTensor S)
    (Y Z W U : Field S) : GlobalSmooth S :=
  LeviCivita.fieldPairing g (tensorSection T Y Z W) U

noncomputable def derivativeForm (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (T : CurvatureTensor S) (p : M)
    (X Y Z W U : TangentSpace S p) : ℝ :=
  pairing g p (covariantDerivative C T p X Y Z W) U

theorem derivativeForm_rule (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (T : CurvatureTensor S)
    (X Y Z W U : Field S) (p : M) :
    derivativeForm g C T p (X.val p) (Y.val p) (Z.val p) (W.val p) (U.val p) =
      (act S X (curvatureFunction g T Y Z W U)).val p -
      curvatureForm g T p ((C.cov X Y).val p) (Z.val p) (W.val p) (U.val p) -
      curvatureForm g T p (Y.val p) ((C.cov X Z).val p) (W.val p) (U.val p) -
      curvatureForm g T p (Y.val p) (Z.val p) ((C.cov X W).val p) (U.val p) -
      curvatureForm g T p (Y.val p) (Z.val p) (W.val p) ((C.cov X U).val p) := by
  have hd := (SecondBianchi.derivative_rule C T p).1 X Y Z W
  have hm := hC.2 X (tensorSection T Y Z W) U p
  change scalarDerivative S (curvatureFunction g T Y Z W U).val p (X.val p) = _ at hm
  rw [ConnectionForms.scalarDerivative_global] at hm
  unfold derivativeForm
  rw [hd]
  simp only [tensorDerivativeField, ConnectionForms.section_add_apply,
    ConnectionForms.section_smul_apply, SecondBianchi.tensorSection_apply,
    pairing, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  change _ = _ - _ - _ - _ - _
  change _ = pairing g p ((C.cov X (tensorSection T Y Z W)).val p) (U.val p) +
    curvatureForm g T p (Y.val p) (Z.val p) (W.val p) ((C.cov X U).val p) at hm
  simp only [curvatureForm, pairing] at hm ⊢
  linarith

theorem derivativeForm_pair_exchange (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)
    (x y z w u : TangentSpace S p) :
    derivativeForm g C T p x y z w u = derivativeForm g C T p x w u y z := by
  obtain ⟨X, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p x
  obtain ⟨Y, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p y
  obtain ⟨Z, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p z
  obtain ⟨W, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p w
  obtain ⟨U, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p u
  have hf : curvatureFunction g T Y Z W U = curvatureFunction g T W U Y Z := by
    apply Subtype.ext
    funext q
    exact (CurvatureAlgebra.symmetries g C hC T hT q _ _ _ _).2.2
  rw [derivativeForm_rule g C hC, derivativeForm_rule g C hC, hf]
  have hp := fun A B D E => (CurvatureAlgebra.symmetries g C hC T hT p A B D E).2.2
  rw [hp ((C.cov X Y).val p) (Z.val p) (W.val p) (U.val p),
    hp (Y.val p) ((C.cov X Z).val p) (W.val p) (U.val p),
    hp (Y.val p) (Z.val p) ((C.cov X W).val p) (U.val p),
    hp (Y.val p) (Z.val p) (W.val p) ((C.cov X U).val p)]
  ring

theorem derivativeForm_skew_last (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)
    (x y z w u : TangentSpace S p) :
    derivativeForm g C T p x y z w u = -derivativeForm g C T p x y z u w := by
  obtain ⟨X, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p x
  obtain ⟨Y, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p y
  obtain ⟨Z, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p z
  obtain ⟨W, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p w
  obtain ⟨U, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p u
  have hf : curvatureFunction g T Y Z W U = -curvatureFunction g T Y Z U W := by
    apply Subtype.ext
    funext q
    exact (CurvatureAlgebra.symmetries g C hC T hT q _ _ _ _).2.1
  rw [derivativeForm_rule g C hC, derivativeForm_rule g C hC, hf, map_neg]
  change -(act S X (curvatureFunction g T Y Z U W)).val p - _ - _ - _ - _ = _
  have hp := fun A B D E => (CurvatureAlgebra.symmetries g C hC T hT p A B D E).2.1
  rw [hp ((C.cov X Y).val p) (Z.val p) (W.val p) (U.val p),
    hp (Y.val p) ((C.cov X Z).val p) (W.val p) (U.val p),
    hp (Y.val p) (Z.val p) ((C.cov X W).val p) (U.val p),
    hp (Y.val p) (Z.val p) (W.val p) ((C.cov X U).val p)]
  ring

theorem derivativeForm_skew_first (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)
    (x y z w u : TangentSpace S p) :
    derivativeForm g C T p x y z w u = -derivativeForm g C T p x z y w u := by
  rw [derivativeForm_pair_exchange g C hC T hT p x y z w u,
    derivativeForm_skew_last g C hC T hT p x w u y z,
    derivativeForm_pair_exchange g C hC T hT p x w u z y]

/-- The finite-dimensional algebraic contraction of differential Bianchi. -/
theorem contracted_bianchi_algebra (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (p : M)
    (Z : TangentSpace S p) :
    2 * divergenceRicci g C T p Z = metricTrace g p (ricciDerivative C T p Z) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g p
  have hrc (x y z : TangentSpace S p) : ricciDerivative C T p x y z =
      ∑ i, derivativeForm g C T p x (b i) y z (b i) := by
    rw [ricciDerivative, P202.RicciData.ricciDerivative, curvatureContraction,
      LinearMap.mk₂_apply, trace_basis b]
    apply Finset.sum_congr rfl
    intro i _
    rw [orthonormal_repr g p b hb]
    exact g.symmetric p _ _
  have hdiv : divergenceRicci g C T p Z =
      ∑ m, ∑ i, derivativeForm g C T p (b m) (b i) (b m) Z (b i) := by
    rw [divergenceRicci, P202.RicciData.divergenceRicci, metricTrace_orthonormal g p b hb]
    simp only [LinearMap.mk₂_apply, hrc]
  have hsc : metricTrace g p (ricciDerivative C T p Z) =
      ∑ m, ∑ i, derivativeForm g C T p Z (b i) (b m) (b m) (b i) := by
    rw [metricTrace_orthonormal g p b hb]
    simp_rw [hrc]
  have hsum (m i : Fin n) :
      derivativeForm g C T p (b m) (b i) Z (b m) (b i) +
      derivativeForm g C T p (b i) Z (b m) (b m) (b i) +
      derivativeForm g C T p Z (b m) (b i) (b m) (b i) = 0 := by
    have h := congrArg (fun A : TangentSpace S p →ₗ[ℝ] TangentSpace S p =>
      pairing g p (A (b m)) (b i)) (SecondBianchi.second_bianchi g C hC T hT p (b m) (b i) Z)
    simpa only [derivativeForm, LinearMap.add_apply, LinearMap.zero_apply,
      pairing, map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] using h
  have hfirst (m i : Fin n) : derivativeForm g C T p (b m) (b i) Z (b m) (b i) =
      derivativeForm g C T p (b m) (b i) (b m) Z (b i) := by
    rw [derivativeForm_pair_exchange g C hC T hT p (b m) (b i) Z (b m) (b i),
      derivativeForm_skew_first g C hC T hT p (b m) (b m) (b i) (b i) Z,
      derivativeForm_skew_last g C hC T hT p (b m) (b i) (b m) (b i) Z,
      neg_neg]
  have hsecond (m i : Fin n) : derivativeForm g C T p (b i) Z (b m) (b m) (b i) =
      derivativeForm g C T p (b i) (b m) (b i) Z (b m) :=
    derivativeForm_pair_exchange g C hC T hT p (b i) Z (b m) (b m) (b i)
  have hthird (m i : Fin n) : derivativeForm g C T p Z (b m) (b i) (b m) (b i) =
      -derivativeForm g C T p Z (b m) (b i) (b i) (b m) :=
    derivativeForm_skew_last g C hC T hT p Z (b m) (b i) (b m) (b i)
  have hs : (∑ m : Fin n, ∑ i : Fin n,
      (derivativeForm g C T p (b m) (b i) Z (b m) (b i) +
      derivativeForm g C T p (b i) Z (b m) (b m) (b i) +
      derivativeForm g C T p Z (b m) (b i) (b m) (b i))) = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro i _
    exact hsum m i
  simp_rw [hfirst, hsecond, hthird] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hs
  rw [Finset.sum_comm (f := fun m i => derivativeForm g C T p (b i) (b m) (b i) Z (b m)),
    Finset.sum_comm (f := fun m i => derivativeForm g C T p Z (b m) (b i) (b i) (b m))] at hs
  rw [hdiv, hsc]
  linarith

theorem contracted_bianchi : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u} := by
  intro n a M _ S g C hC T hT p Z
  rw [scalar_derivative_rule g C hC T p Z]
  linarith [contracted_bianchi_algebra g C hC T hT p Z]

theorem frame_independence :
    P202Specs.Geometry.RicciScalarBianchi.frame_independenceType.{u} := by
  intro n a M _ S g T p b c hb hc
  refine ⟨?_, ?_⟩
  · intro Y Z
    exact ((orthonormal_contractions g T p b hb).1 Y Z).symm.trans
      ((orthonormal_contractions g T p c hc).1 Y Z)
  · exact (orthonormal_contractions g T p b hb).2.symm.trans
      (orthonormal_contractions g T p c hc).2

theorem contracted_bianchi_coordinates :
    P202Specs.Geometry.RicciScalarBianchi.contracted_bianchi_coordinatesType.{u} := by
  intro n a M _ S g C hC T hT c p hp k
  rw [← (coordinate_contractions g C T c p hp).2]
  exact contracted_bianchi g C hC T hT p (coordinateVector c k p)

end P202.Geometry.RicciScalarBianchi
