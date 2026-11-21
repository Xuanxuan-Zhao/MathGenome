import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.Schur
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SectionalRecovery
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.PeriodCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RicciScalarBianchi
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.Schur
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.CurvatureData P202.RicciData P202.SchurData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

private theorem metricTrace_multiple (g : RiemannianMetric S) (p : M) (c : ℝ) :
    metricTrace g p (c • pairing g p) = (n : ℝ) * c := by
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Module.Free ℝ (TangentSpace S p) := @Module.Free.of_divisionRing ℝ (TangentSpace S p) _ _ _
  have he : ((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm.toLinearMap).comp
      (c • pairing g p) = c • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm
      (c • (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p) x) = c • x
    rw [map_smul, LinearEquiv.symm_apply_apply]
  unfold metricTrace
  rw [he, map_smul, (LinearMap.trace_id (R := ℝ) (M := TangentSpace S p)), (SmoothManifolds.tangent_dimension S p).2]
  simp [mul_comm]

private theorem ricci_of_form (g : RiemannianMetric S) (T : CurvatureTensor S)
    (p : M) (k : ℝ)
    (hf : ∀ x y z w, curvatureForm g T p x y z w =
      k * (pairing g p y z * pairing g p x w - pairing g p x z * pairing g p y w)) :
    ∀ y z, ricci T p y z = ((n : ℝ) - 1) * k * pairing g p y z := by
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Module.Free ℝ (TangentSpace S p) := @Module.Free.of_divisionRing ℝ (TangentSpace S p) _ _ _
  have hv (x y z : TangentSpace S p) : T.val p x y z =
      (k * pairing g p y z) • x + (-k * pairing g p x z) • y := by
    apply (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).injective
    apply LinearMap.ext
    intro w
    change pairing g p (T.val p x y z) w =
      pairing g p ((k * pairing g p y z) • x + (-k * pairing g p x z) • y) w
    have h := hf x y z w
    change pairing g p (T.val p x y z) w = _ at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [h]
    ring
  intro y z
  change LinearMap.trace ℝ (TangentSpace S p) _ = _
  calc
    _ = LinearMap.trace ℝ (TangentSpace S p)
        ((k * pairing g p y z) • LinearMap.id +
          (-k) • ((pairing g p).flip z).smulRight y) := by
      congr 1
      apply LinearMap.ext
      intro x
      change T.val p x y z =
        (k * pairing g p y z) • x + (-k) • (pairing g p x z • y)
      simp only [hv, mul_smul]
    _ = _ := by
      rw [map_add, map_smul, map_smul,
        (LinearMap.trace_id (R := ℝ) (M := TangentSpace S p)),
        (LinearMap.trace_smulRight (R := ℝ) (M := TangentSpace S p) ((pairing g p).flip z) y),
        (SmoothManifolds.tangent_dimension S p).2]
      simp only [smul_eq_mul]
      change (k * pairing g p y z) * (n : ℝ) + (-k) * pairing g p y z = _
      ring

private theorem pointwise_formulas_proof : P202Specs.Geometry.Schur.pointwise_formulasType.{u} := by
  intro n a M _ S g C hc T hT κ hk p
  have hf := SectionalRecovery.curvature_constant g C hc T hT p (κ p) (hk p)
  have hr := ricci_of_form g T p (κ p) hf
  refine ⟨hf, hr, ?_⟩
  have hb : ricci T p = (((n : ℝ) - 1) * κ p) • pairing g p := by
    ext y z
    exact hr y z
  change metricTrace g p (ricci T p) = _
  rw [hb, metricTrace_multiple]
  ring

private theorem common_value_smooth_proof
    (hs : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.common_value_smoothType.{u} := by
  intro n a M _ S g C hc T hT hn κ hk
  have hf := pointwise_formulas_proof g C hc T hT κ hk
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := by nlinarith
  have he : κ = fun p => ((n : ℝ) * ((n : ℝ) - 1))⁻¹ * scalarCurvature g T p := by
    funext p
    rw [(hf p).2.2]
    rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  rw [he]
  exact (SmoothManifolds.globalSmoothAlgebra S).mul_mem
    ((SmoothManifolds.globalSmoothAlgebra S).algebraMap_mem _) (hs g T)

private theorem derivative_scale_product (f h : GlobalSmooth S) (c : ℝ)
    (X : Field S) (p : M) :
    scalarDerivative S (fun q => c * (f.val q * h.val q)) p (X.val p) =
      c * (f.val p * scalarDerivative S h.val p (X.val p) +
        h.val p * scalarDerivative S f.val p (X.val p)) := by
  change scalarDerivative S (c • (f * h)).val p (X.val p) = _
  rw [ConnectionForms.scalarDerivative_global, Derivation.map_smul, Derivation.leibniz]
  change c * (f.val p * (act S X h).val p + h.val p * (act S X f).val p) = _
  rw [ConnectionForms.scalarDerivative_global, ConnectionForms.scalarDerivative_global]

private theorem ricciDerivative_of_isotropic
    (hs : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u})
    (hrule : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hc : IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T) (hn : 3 ≤ n)
    (κ : M → ℝ) (hk : PointwiseSectional g T κ) (p : M)
    (x y z : TangentSpace S p) :
    ricciDerivative C T p x y z =
      ((n : ℝ) - 1) * scalarDerivative S κ p x * pairing g p y z := by
  let X := CurvatureAlgebra.fieldLift p x
  let Y := CurvatureAlgebra.fieldLift p y
  let Z := CurvatureAlgebra.fieldLift p z
  have hX : X.val p = x := CurvatureAlgebra.fieldLift_value p x
  have hY : Y.val p = y := CurvatureAlgebra.fieldLift_value p y
  have hZ : Z.val p = z := CurvatureAlgebra.fieldLift_value p z
  let k : GlobalSmooth S := ⟨κ, common_value_smooth_proof hs g C hc T hT hn κ hk⟩
  have hf := pointwise_formulas_proof g C hc T hT κ hk
  have hr (q : M) (v w : TangentSpace S q) :
      ricci T q v w = ((n : ℝ) - 1) * κ q * pairing g q v w := (hf q).2.1 v w
  have e := hrule C T X Y Z p
  simp_rw [hr] at e
  have hd := derivative_scale_product k (LeviCivita.fieldPairing g Y Z) ((n : ℝ) - 1) X p
  have hfun : (fun q => ((n : ℝ) - 1) * (k.val q * (LeviCivita.fieldPairing g Y Z).val q)) =
      (fun q => ((n : ℝ) - 1) * κ q * pairing g q (Y.val q) (Z.val q)) := by
    funext q
    change ((n : ℝ) - 1) * (κ q * pairing g q (Y.val q) (Z.val q)) = _
    ring
  rw [hfun] at hd
  change scalarDerivative S (fun q => ((n : ℝ) - 1) * κ q * pairing g q (Y.val q) (Z.val q))
    p (X.val p) = ((n : ℝ) - 1) * (κ p * scalarDerivative S
      (fun q => pairing g q (Y.val q) (Z.val q)) p (X.val p) +
        pairing g p (Y.val p) (Z.val p) * scalarDerivative S κ p (X.val p)) at hd
  rw [hc.2 X Y Z p] at hd
  rw [hd] at e
  rw [hX, hY, hZ] at e
  linear_combination e

private theorem metricTrace_rankone (g : RiemannianMetric S) (p : M)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p))
    (α : TangentSpace S p →ₗ[ℝ] ℝ) (z : TangentSpace S p)
    (hB : ∀ x y, B x y = α x * pairing g p y z) :
    metricTrace g p B = α z := by
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Module.Free ℝ (TangentSpace S p) :=
    @Module.Free.of_divisionRing ℝ (TangentSpace S p) _ _ _
  let e := SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p
  have he : e.symm.toLinearMap.comp B = α.smulRight z := by
    apply LinearMap.ext
    intro x
    apply e.injective
    apply LinearMap.ext
    intro y
    change e (e.symm (B x)) y = pairing g p (α x • z) y
    rw [e.apply_symm_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hB]
    exact congrArg (fun t : ℝ => α x * t) (g.symmetric p y z)
  unfold metricTrace
  rw [he]
  exact LinearMap.trace_smulRight (R := ℝ) (M := TangentSpace S p) α z

private theorem common_value_differential_proof
    (hb : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u})
    (hr : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (hsd : P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u})
    (hs : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.common_value_differentialType.{u} := by
  intro n a M _ S g C hc T hT hn κ hk p z
  have hD := ricciDerivative_of_isotropic hs hr g C hc T hT hn κ hk p
  have hdiv : divergenceRicci g C T p z = ((n : ℝ) - 1) * scalarDerivative S κ p z := by
    apply metricTrace_rankone g p _ (((n : ℝ) - 1) • scalarDerivative S κ p) z
    intro x y
    exact hD x y z
  have hscal : scalarDerivative S (scalarCurvature g T) p z =
      (n : ℝ) * (((n : ℝ) - 1) * scalarDerivative S κ p z) := by
    rw [hsd g C hc T p z]
    have he : ricciDerivative C T p z =
        (((n : ℝ) - 1) * scalarDerivative S κ p z) • pairing g p := by
      ext x y
      exact hD z x y
    rw [he, metricTrace_multiple]
  have he := hb g C hc T hT p z
  rw [hdiv, hscal] at he
  have hz : (((n : ℝ) - 1) * ((n : ℝ) - 2)) * scalarDerivative S κ p z = 0 := by
    linear_combination -2 * he
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hn1 hn2)

private theorem common_value_locally_constant
    (κ : M → ℝ) (hk : κ ∈ SmoothManifolds.globalSmoothAlgebra S)
    (hd : ∀ (p : M) (v : TangentSpace S p), scalarDerivative S κ p v = 0) :
    IsLocallyConstant κ := by
  let K : GlobalSmooth S := ⟨κ, hk⟩
  let C := Classical.choice (SmoothManifolds.BundleOperations.exists_cotangent S)
  have hκ := (SmoothManifolds.mem_globalSmoothAlgebra_iff S κ).mp hk
  apply SmoothManifolds.PeriodCriterion.locally_constant_of_dFunction_zero S C κ hκ
  funext p
  apply LinearMap.ext
  intro v
  change v.val (SmoothManifolds.CovectorData.functionGerm S κ hκ p) = 0
  have he : SmoothManifolds.CovectorData.functionGerm S κ hκ p =
      SmoothManifolds.globalToGerm S p K := by rfl
  rw [he, ← ConnectionForms.scalarDerivative_representative κ K p Filter.EventuallyEq.rfl v]
  exact hd p v

private theorem schur_proof
    (hb : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u})
    (hr : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (hsd : P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u})
    (hs : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.schurType.{u} := by
  intro n a M _ _ S g C hc T hT hn hk
  rcases isEmpty_or_nonempty M with hM | hM
  · letI := hM
    exact ⟨0, fun p => isEmptyElim p⟩
  letI := hM
  choose κ hκ using hk
  have hpoint : PointwiseSectional g T κ := hκ
  have hsm := common_value_smooth_proof hs g C hc T hT hn κ hpoint
  have hd := common_value_differential_proof hb hr hsd hs g C hc T hT hn κ hpoint
  have hlc := common_value_locally_constant κ hsm hd
  let p₀ : M := Classical.choice (inferInstance : Nonempty M)
  refine ⟨κ p₀, ?_⟩
  intro p x y h
  rw [hκ p x y h]
  exact hlc.apply_eq_of_preconnectedSpace p p₀

theorem pointwise_formulas_conditional
    (h1 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u})
    (h2 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchi_coordinatesType.{u})
    (h3 : P202Specs.Geometry.RicciScalarBianchi.coordinate_contractionsType.{u})
    (h4 : P202Specs.Geometry.RicciScalarBianchi.frame_independenceType.{u})
    (h5 : P202Specs.Geometry.RicciScalarBianchi.orthonormal_contractionsType.{u})
    (h6 : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (h7 : P202Specs.Geometry.RicciScalarBianchi.ricci_smoothType.{u})
    (h8 : P202Specs.Geometry.RicciScalarBianchi.ricci_symmetricType.{u})
    (h9 : P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u})
    (h10 : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.pointwise_formulasType.{u} := pointwise_formulas_proof

theorem common_value_smooth_conditional
    (h1 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u})
    (h2 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchi_coordinatesType.{u})
    (h3 : P202Specs.Geometry.RicciScalarBianchi.coordinate_contractionsType.{u})
    (h4 : P202Specs.Geometry.RicciScalarBianchi.frame_independenceType.{u})
    (h5 : P202Specs.Geometry.RicciScalarBianchi.orthonormal_contractionsType.{u})
    (h6 : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (h7 : P202Specs.Geometry.RicciScalarBianchi.ricci_smoothType.{u})
    (h8 : P202Specs.Geometry.RicciScalarBianchi.ricci_symmetricType.{u})
    (h9 : P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u})
    (h10 : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.common_value_smoothType.{u} := common_value_smooth_proof h10

theorem common_value_differential_conditional
    (h1 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u})
    (h2 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchi_coordinatesType.{u})
    (h3 : P202Specs.Geometry.RicciScalarBianchi.coordinate_contractionsType.{u})
    (h4 : P202Specs.Geometry.RicciScalarBianchi.frame_independenceType.{u})
    (h5 : P202Specs.Geometry.RicciScalarBianchi.orthonormal_contractionsType.{u})
    (h6 : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (h7 : P202Specs.Geometry.RicciScalarBianchi.ricci_smoothType.{u})
    (h8 : P202Specs.Geometry.RicciScalarBianchi.ricci_symmetricType.{u})
    (h9 : P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u})
    (h10 : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.common_value_differentialType.{u} := common_value_differential_proof h1 h6 h9 h10

theorem schur_conditional
    (h1 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u})
    (h2 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchi_coordinatesType.{u})
    (h3 : P202Specs.Geometry.RicciScalarBianchi.coordinate_contractionsType.{u})
    (h4 : P202Specs.Geometry.RicciScalarBianchi.frame_independenceType.{u})
    (h5 : P202Specs.Geometry.RicciScalarBianchi.orthonormal_contractionsType.{u})
    (h6 : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (h7 : P202Specs.Geometry.RicciScalarBianchi.ricci_smoothType.{u})
    (h8 : P202Specs.Geometry.RicciScalarBianchi.ricci_symmetricType.{u})
    (h9 : P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u})
    (h10 : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.schurType.{u} := schur_proof h1 h6 h9 h10

theorem complete_theorem_conditional
    (h1 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u})
    (h2 : P202Specs.Geometry.RicciScalarBianchi.contracted_bianchi_coordinatesType.{u})
    (h3 : P202Specs.Geometry.RicciScalarBianchi.coordinate_contractionsType.{u})
    (h4 : P202Specs.Geometry.RicciScalarBianchi.frame_independenceType.{u})
    (h5 : P202Specs.Geometry.RicciScalarBianchi.orthonormal_contractionsType.{u})
    (h6 : P202Specs.Geometry.RicciScalarBianchi.ricci_derivative_ruleType.{u})
    (h7 : P202Specs.Geometry.RicciScalarBianchi.ricci_smoothType.{u})
    (h8 : P202Specs.Geometry.RicciScalarBianchi.ricci_symmetricType.{u})
    (h9 : P202Specs.Geometry.RicciScalarBianchi.scalar_derivative_ruleType.{u})
    (h10 : P202Specs.Geometry.RicciScalarBianchi.scalar_smoothType.{u}) :
    P202Specs.Geometry.Schur.complete_theoremType.{u} := ⟨SectionalRecovery.recovery, h8, h1, h2, pointwise_formulas_proof, common_value_smooth_proof h10, common_value_differential_proof h1 h6 h9 h10, schur_proof h1 h6 h9 h10⟩

end P202.Geometry.Schur

universe v8_closure_0a10c52bb29aa9e8_u0
theorem _root_.«P202».«Geometry».«Schur».«common_value_differential» : _root_.«P202Specs».«Geometry».«Schur».«common_value_differentialType».{v8_closure_0a10c52bb29aa9e8_u0} :=
  @_root_.«P202».«Geometry».«Schur».«common_value_differential_conditional».{v8_closure_0a10c52bb29aa9e8_u0} (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi_coordinates».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«coordinate_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«frame_independence».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«orthonormal_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_smooth».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_symmetric».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_smooth».{v8_closure_0a10c52bb29aa9e8_u0})
theorem _root_.«P202».«Geometry».«Schur».«common_value_smooth» : _root_.«P202Specs».«Geometry».«Schur».«common_value_smoothType».{v8_closure_0a10c52bb29aa9e8_u0} :=
  @_root_.«P202».«Geometry».«Schur».«common_value_smooth_conditional».{v8_closure_0a10c52bb29aa9e8_u0} (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi_coordinates».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«coordinate_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«frame_independence».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«orthonormal_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_smooth».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_symmetric».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_smooth».{v8_closure_0a10c52bb29aa9e8_u0})
theorem _root_.«P202».«Geometry».«Schur».«complete_theorem» : _root_.«P202Specs».«Geometry».«Schur».«complete_theoremType».{v8_closure_0a10c52bb29aa9e8_u0} :=
  @_root_.«P202».«Geometry».«Schur».«complete_theorem_conditional».{v8_closure_0a10c52bb29aa9e8_u0} (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi_coordinates».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«coordinate_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«frame_independence».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«orthonormal_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_smooth».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_symmetric».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_smooth».{v8_closure_0a10c52bb29aa9e8_u0})
theorem _root_.«P202».«Geometry».«Schur».«pointwise_formulas» : _root_.«P202Specs».«Geometry».«Schur».«pointwise_formulasType».{v8_closure_0a10c52bb29aa9e8_u0} :=
  @_root_.«P202».«Geometry».«Schur».«pointwise_formulas_conditional».{v8_closure_0a10c52bb29aa9e8_u0} (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi_coordinates».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«coordinate_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«frame_independence».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«orthonormal_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_smooth».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_symmetric».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_smooth».{v8_closure_0a10c52bb29aa9e8_u0})
theorem _root_.«P202».«Geometry».«Schur».«schur» : _root_.«P202Specs».«Geometry».«Schur».«schurType».{v8_closure_0a10c52bb29aa9e8_u0} :=
  @_root_.«P202».«Geometry».«Schur».«schur_conditional».{v8_closure_0a10c52bb29aa9e8_u0} (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«contracted_bianchi_coordinates».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«coordinate_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«frame_independence».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«orthonormal_contractions».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_smooth».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«ricci_symmetric».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_derivative_rule».{v8_closure_0a10c52bb29aa9e8_u0}) (@_root_.«P202».«Geometry».«RicciScalarBianchi».«scalar_smooth».{v8_closure_0a10c52bb29aa9e8_u0})
