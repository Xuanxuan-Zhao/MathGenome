import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussCodazziRicci
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussWeingarten
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.Geometry.GaussCodazziRicci
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GaussWeingartenData
  P202.CurvatureEquationsData P202.TorsionMetricData
open Filter
open scoped Topology
open ConnectionForms (section_ext section_add_apply section_smul_apply section_zero_apply)
universe u v w z t q

/-- Specify the ambient dependent function module explicitly, avoiding the
upstream realization's expensive reverse typeclass inference. -/
noncomputable local instance sectionAddCommGroup
    {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) : AddCommGroup (Section B) :=
  @Submodule.addCommGroup ℝ ((p : M) → E p) _ _ _ (sectionModule B)

/-- A smooth fiberwise bilinear tensor induces a bilinear operation on smooth
sections. This is the reverse direction of the upstream tensor descent. -/
noncomputable def bilinearSections
    {n r k l : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t} {τ : Type q}
    {E : M → Type w} {J : M → Type z} {H : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (J p)] [∀ p, Module ℝ (J p)]
    [∀ p, AddCommGroup (H p)] [∀ p, Module ℝ (H p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) J)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean l) H)]
    (B : SmoothVectorBundle S r ι E) (A : SmoothVectorBundle S k κ J)
    (L : SmoothVectorBundle S l τ H)
    (f : (p : M) → E p →ₗ[ℝ] J p →ₗ[ℝ] H p)
    (hf : ∀ (s : Section B) (v : Section A),
      SmoothManifolds.SectionExtensionData.SmoothSection L
        (fun p => f p (s.val p) (v.val p))) :
    Section B →ₗ[ℝ] Section A →ₗ[ℝ] Section L where
  toFun s := {
    toFun := fun v => ⟨_, hf s v⟩
    map_add' := by intros; apply section_ext; intro p; exact map_add (f p (s.val p)) _ _
    map_smul' := by intros; apply section_ext; intro p; exact map_smul (f p (s.val p)) _ _ }
  map_add' := by
    intros; apply LinearMap.ext; intro v; apply section_ext; intro p
    exact LinearMap.congr_fun (map_add (f p) _ _) (v.val p)
  map_smul' := by
    intros; apply LinearMap.ext; intro v; apply section_ext; intro p
    exact LinearMap.congr_fun (map_smul (f p) _ _) (v.val p)

section BundleCurvature
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (D : Connection B)

@[simp] theorem bundleCurvature_apply (X Y : Field S) (s : Section B) (p : M) :
    (bundleCurvature D X Y s).val p =
      (D.cov X (D.cov Y s)).val p - (D.cov Y (D.cov X s)).val p -
        (D.cov (bracket X Y) s).val p := rfl

theorem bundleCurvature_add (X Y : Field S) (s t : Section B) :
    bundleCurvature D X Y (s + t) = bundleCurvature D X Y s + bundleCurvature D X Y t := by
  simp only [bundleCurvature, map_add]
  abel

theorem bundleCurvature_smul (X Y : Field S) (c : ℝ) (s : Section B) :
    bundleCurvature D X Y (c • s) = c • bundleCurvature D X Y s := by
  simp only [bundleCurvature, map_smul]
  module

theorem bundleCurvature_mul (X Y : Field S) (f : GlobalSmooth S) (s : Section B) :
    bundleCurvature D X Y (mulSection f s) = mulSection f (bundleCurvature D X Y s) := by
  apply section_ext; intro p
  have hb := TorsionAndMetric.bracket_act X Y f p
  rw [ConnectionForms.scalarDerivative_global] at hb
  simp only [bundleCurvature_apply, D.leibniz, map_add, section_add_apply,
    ConnectionForms.mulSection_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [hb]
  module

theorem bundleCurvature_locality (X Y : Field S) (s t : Section B) (p : M)
    (h : ∀ᶠ z in nhds p, s.val z = t.val z) :
    (bundleCurvature D X Y s).val p = (bundleCurvature D X Y t).val p := by
  have hd (Z : Field S) : ∀ᶠ q in nhds p, (D.cov Z s).val q = (D.cov Z t).val q :=
    h.eventually_nhds.mono (fun q hq => ConnectionForms.locality_section B D Z s t q hq)
  rw [bundleCurvature_apply, bundleCurvature_apply,
    ConnectionForms.locality_section B D X _ _ p (hd Y),
    ConnectionForms.locality_section B D Y _ _ p (hd X),
    ConnectionForms.locality_section B D (bracket X Y) s t p h]

end BundleCurvature

/-- Finite bilinear contraction, retaining both possibly zero ranks. -/
noncomputable def weighted {k l : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Fin k → ℝ) (g : Fin l → ℝ) (z : Fin k → Fin l → V) : V :=
  ∑ i, f i • ∑ j, g j • z i j

theorem weighted_swap {k l : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Fin k → ℝ) (g : Fin l → ℝ) (z : Fin k → Fin l → V) :
    weighted g f (fun j i => z i j) = weighted f g z := by
  simp only [weighted, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

theorem weighted_sub {k l : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Fin k → ℝ) (g : Fin l → ℝ) (z t : Fin k → Fin l → V) :
    weighted f g (fun i j => z i j - t i j) = weighted f g z - weighted f g t := by
  simp only [weighted, smul_sub, Finset.sum_sub_distrib]

theorem weighted_map {k l : ℕ} {V H : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup H] [Module ℝ H]
    (L : V →ₗ[ℝ] H) (f : Fin k → ℝ) (g : Fin l → ℝ)
    (z : Fin k → Fin l → V) :
    L (weighted f g z) = weighted f g (fun i j => L (z i j)) := by
  simp only [weighted, map_sum, map_smul]

section PullbackCurvature
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  (F : M → N) (hF : IsSmoothMap S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (K : Connection (tangentBundle T))
  (D : letI := P.space.topology; Connection P.space.bundle)
  (hD : letI := P.space.topology;
    P202.PullbackData.IsPullback (tangentBundle T) K F hF P D)
include hD

/-- Differentiate any germ expansion in pulled-back ambient fields. -/
theorem cov_pull_expansion (X : Field S)
    (V : letI := P.space.topology; Section P.space.bundle)
    {k : ℕ} (f : Fin k → GlobalSmooth S) (e : Fin k → Field T) (p : M)
    (hV : letI := P.space.topology;
      ∀ᶠ q in nhds p, V.val q =
        (∑ j, mulSection (f j) (PullbackConnections.pullSection (tangentBundle T) F hF P (e j))).val q) :
    letI := P.space.topology
    (D.cov X V).val p = ∑ j,
      ((act S X (f j)).val p • (e j).val (F p) +
        (f j).val p • pointDerivative K (e j).val (F p)
          (SmoothManifolds.differential S T F hF p (X.val p))) := by
  letI := P.space.topology
  rw [ConnectionForms.locality_section P.space.bundle D X _ _ p hV,
    ConnectionForms.finite_expansion P.space.bundle D]
  simp only [Submodule.coe_sum, Finset.sum_apply, section_add_apply,
    ConnectionForms.mulSection_apply, PullbackConnections.pullSection_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hD X (e j) _ (fun _ => rfl) p]

/-- A prescribed expansion of dF(X) gives the derivative of every pulled-back
ambient field on the same neighborhood. -/
theorem derivative_pull_expansion (X : Field S) (s : Field T)
    {k : ℕ} (f : Fin k → GlobalSmooth S) (e : Fin k → Field T) (p : M)
    (hX : ∀ᶠ q in nhds p,
      SmoothManifolds.differential S T F hF q (X.val q) =
        ∑ j, (f j).val q • (e j).val (F q)) :
    letI := P.space.topology
    ∀ᶠ q in nhds p,
      (D.cov X (PullbackConnections.pullSection (tangentBundle T) F hF P s)).val q =
        (∑ j, mulSection (f j) (PullbackConnections.pullSection (tangentBundle T) F hF P
          (K.cov (e j) s))).val q := by
  letI := P.space.topology
  filter_upwards [hX] with q hq
  rw [hD X s _ (fun _ => rfl) q, hq, map_sum]
  simp only [map_smul, ConnectionForms.pointDerivative_global, Submodule.coe_sum,
    Finset.sum_apply, ConnectionForms.mulSection_apply, PullbackConnections.pullSection_apply]

/-- Mixed derivatives of a pulled-back section, with finite germs for dF(X)
and dF(Y). Coefficient derivatives are the intrinsic action of source fields. -/
theorem second_pull_expansion (X Y : Field S) (s : Field T)
    {k l : ℕ} (f : Fin k → GlobalSmooth S) (e : Fin k → Field T)
    (g : Fin l → GlobalSmooth S) (v : Fin l → Field T) (p : M)
    (hX : ∀ᶠ q in nhds p,
      SmoothManifolds.differential S T F hF q (X.val q) = ∑ j, (f j).val q • (e j).val (F q))
    (hY : ∀ᶠ q in nhds p,
      SmoothManifolds.differential S T F hF q (Y.val q) = ∑ j, (g j).val q • (v j).val (F q)) :
    letI := P.space.topology
    (D.cov X (D.cov Y (PullbackConnections.pullSection (tangentBundle T) F hF P s))).val p =
      ∑ j, ((act S X (g j)).val p • (K.cov (v j) s).val (F p) +
        (g j).val p • ∑ i, (f i).val p • (K.cov (e i) (K.cov (v j) s)).val (F p)) := by
  letI := P.space.topology
  rw [cov_pull_expansion F hF P K D hD X _ g (fun j => K.cov (v j) s) p
    (derivative_pull_expansion F hF P K D hD Y s g v p hY)]
  rw [hX.self_of_nhds]
  simp only [map_sum, map_smul, ConnectionForms.pointDerivative_global]

theorem cov_differential_expansion (X Y : Field S)
    {k l : ℕ} (f : Fin k → GlobalSmooth S) (e : Fin k → Field T)
    (g : Fin l → GlobalSmooth S) (v : Fin l → Field T) (p : M)
    (hX : ∀ᶠ q in nhds p,
      SmoothManifolds.differential S T F hF q (X.val q) = ∑ j, (f j).val q • (e j).val (F q))
    (hY : ∀ᶠ q in nhds p,
      SmoothManifolds.differential S T F hF q (Y.val q) = ∑ j, (g j).val q • (v j).val (F q)) :
    letI := P.space.topology
    (D.cov X (TorsionAndMetric.differentialAlong F hF P Y)).val p =
      (∑ j, (act S X (g j)).val p • (v j).val (F p)) +
        weighted (fun i => (f i).val p) (fun j => (g j).val p)
          (fun i j => (K.cov (e i) (v j)).val (F p)) := by
  letI := P.space.topology
  have hV : ∀ᶠ q in nhds p,
      (TorsionAndMetric.differentialAlong F hF P Y).val q =
        (∑ j, mulSection (g j) (PullbackConnections.pullSection (tangentBundle T) F hF P (v j))).val q := by
    simpa only [TorsionAndMetric.differentialAlong_apply, Submodule.coe_sum,
      Finset.sum_apply, ConnectionForms.mulSection_apply, PullbackConnections.pullSection_apply] using hY
  rw [cov_pull_expansion F hF P K D hD X _ g v p hV, hX.self_of_nhds]
  simp only [map_sum, map_smul, ConnectionForms.pointDerivative_global, Finset.sum_add_distrib]
  exact congrArg (fun z => (∑ j, (act S X (g j)).val p • (v j).val (F p)) + z)
    (weighted_swap (fun i => (f i).val p) (fun j => (g j).val p)
      (fun i j => (K.cov (e i) (v j)).val (F p)))

/-- Naturality on pulled-back ambient fields. The finite expansions are germs,
so this does not require a frame on either entire manifold. -/
theorem curvature_pullSection (hK : IsTorsionFree K)
    (R : P202.CurvatureData.CurvatureTensor T)
    (hR : P202.CurvatureData.RepresentsCurvature K R)
    (X Y : Field S) (s : Field T) (p : M) :
    letI := P.space.topology
    (bundleCurvature D X Y (PullbackConnections.pullSection (tangentBundle T) F hF P s)).val p =
      R.val (F p) (SmoothManifolds.differential S T F hF p (X.val p))
        (SmoothManifolds.differential S T F hF p (Y.val p)) (s.val (F p)) := by
  letI := P.space.topology
  let VX := TorsionAndMetric.differentialAlong F hF P X
  let VY := TorsionAndMetric.differentialAlong F hF P Y
  obtain ⟨f, e, hf⟩ := PullbackConnections.section_germ_expansion (tangentBundle T) F hF P VX p
  obtain ⟨g, v, hg⟩ := PullbackConnections.section_germ_expansion (tangentBundle T) F hF P VY p
  have hX : ∀ᶠ q in nhds p,
      SmoothManifolds.differential S T F hF q (X.val q) = ∑ j, (f j).val q • (e j).val (F q) := by
    simpa only [VX, TorsionAndMetric.differentialAlong_apply, Submodule.coe_sum,
      Finset.sum_apply, ConnectionForms.mulSection_apply, PullbackConnections.pullSection_apply] using hf
  have hY : ∀ᶠ q in nhds p,
      SmoothManifolds.differential S T F hF q (Y.val q) = ∑ j, (g j).val q • (v j).val (F q) := by
    simpa only [VY, TorsionAndMetric.differentialAlong_apply, Submodule.coe_sum,
      Finset.sum_apply, ConnectionForms.mulSection_apply, PullbackConnections.pullSection_apply] using hg
  let f₀ := fun i => (f i).val p
  let g₀ := fun j => (g j).val p
  have ht := TorsionAndMetric.differential_naturality_fiber F hF P K D hD X Y VX VY
    (fun _ => rfl) (fun _ => rfl) p
  have hz : TorsionAndMetric.torsionFiber K (F p) (VX.val p) (VY.val p) = 0 := by
    change (torsion K (TorsionAndMetric.liftField (F p) (VX.val p))
      (TorsionAndMetric.liftField (F p) (VY.val p))).val (F p) = 0
    rw [hK]
    rfl
  rw [hz] at ht
  have hbr : SmoothManifolds.differential S T F hF p ((bracket X Y).val p) =
      (D.cov X VY).val p - (D.cov Y VX).val p := by
    exact (sub_eq_zero.mp ht).symm
  rw [cov_differential_expansion F hF P K D hD X Y f e g v p hX hY,
    cov_differential_expansion F hF P K D hD Y X g v f e p hY hX,
    weighted_swap (V := TangentSpace T (F p)) f₀ g₀ (fun i j => (K.cov (v j) (e i)).val (F p))] at hbr
  have hbf (i j : Fin m) : (bracket (e i) (v j)).val (F p) =
      (K.cov (e i) (v j)).val (F p) - (K.cov (v j) (e i)).val (F p) := by
    rw [LeviCivita.tangent_sub_as_add]
    have h := congrArg (fun Z : Field T => Z.val (F p)) (CurvatureAlgebra.bracket_cov K hK (e i) (v j))
    simpa only [section_add_apply, section_smul_apply] using h
  have hbr' : SmoothManifolds.differential S T F hF p ((bracket X Y).val p) =
      (∑ j, (act S X (g j)).val p • (v j).val (F p)) -
      (∑ i, (act S Y (f i)).val p • (e i).val (F p)) +
      weighted f₀ g₀ (fun i j => (bracket (e i) (v j)).val (F p)) := by
    simp_rw [hbf]
    rw [weighted_sub (V := TangentSpace T (F p)), hbr]
    abel
  have hbrs := congrArg (pointDerivative K s.val (F p)) hbr'
  simp only [
    map_add (pointDerivative K s.val (F p)),
    map_sub (pointDerivative K s.val (F p)),
    map_sum (pointDerivative K s.val (F p)),
    map_smul (pointDerivative K s.val (F p)),
    weighted_map (V := TangentSpace T (F p)) (H := TangentSpace T (F p))
      (pointDerivative K s.val (F p)),
    ConnectionForms.pointDerivative_global (tangentBundle T) K s (F p)
  ] at hbrs
  have hXY := second_pull_expansion F hF P K D hD X Y s f e g v p hX hY
  have hYX := second_pull_expansion F hF P K D hD Y X s g v f e p hY hX
  simp only [Finset.sum_add_distrib] at hXY hYX
  change _ = _ + weighted (V := TangentSpace T (F p)) g₀ f₀ (fun j i => (K.cov (e i) (K.cov (v j) s)).val (F p)) at hXY
  change _ = _ + weighted (V := TangentSpace T (F p)) f₀ g₀ (fun i j => (K.cov (v j) (K.cov (e i) s)).val (F p)) at hYX
  rw [weighted_swap (V := TangentSpace T (F p)) f₀ g₀ (fun i j => (K.cov (e i) (K.cov (v j) s)).val (F p))] at hXY
  have hRsum : R.val (F p)
      (SmoothManifolds.differential S T F hF p (X.val p))
      (SmoothManifolds.differential S T F hF p (Y.val p)) (s.val (F p)) =
      weighted f₀ g₀ (fun i j => (P202.CurvatureData.curvature K (e i) (v j) s).val (F p)) := by
    rw [hX.self_of_nhds, hY.self_of_nhds]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, weighted,
      f₀, g₀]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [smul_comm, hR]
  rw [bundleCurvature_apply, hXY, hYX, hD (bracket X Y) s _ (fun _ => rfl) p,
    hbrs, hRsum]
  simp_rw [CurvatureAlgebra.curvature_apply]
  rw [weighted_sub (V := TangentSpace T (F p)), weighted_sub (V := TangentSpace T (F p))]
  abel

theorem curvature_pullback (hK : IsTorsionFree K)
    (R : P202.CurvatureData.CurvatureTensor T)
    (hR : P202.CurvatureData.RepresentsCurvature K R)
    (X Y : Field S) (s : letI := P.space.topology; Section P.space.bundle) (p : M) :
    letI := P.space.topology
    (bundleCurvature D X Y s).val p =
      R.val (F p) (SmoothManifolds.differential S T F hF p (X.val p))
        (SmoothManifolds.differential S T F hF p (Y.val p)) (s.val p) := by
  letI := P.space.topology
  obtain ⟨f, e, he⟩ := PullbackConnections.section_germ_expansion (tangentBundle T) F hF P s p
  let L : Section P.space.bundle →ₗ[ℝ] Section P.space.bundle := {
    toFun := bundleCurvature D X Y
    map_add' := bundleCurvature_add P.space.bundle D X Y
    map_smul' := bundleCurvature_smul P.space.bundle D X Y }
  rw [bundleCurvature_locality P.space.bundle D X Y s _ p he, he.self_of_nhds]
  change (L (∑ j, mulSection (f j) (PullbackConnections.pullSection (tangentBundle T) F hF P (e j)))).val p = _
  rw [map_sum]
  simp only [Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  change (bundleCurvature D X Y (mulSection (f j) (PullbackConnections.pullSection (tangentBundle T) F hF P (e j)))).val p = _
  rw [bundleCurvature_mul, ConnectionForms.mulSection_apply,
    curvature_pullSection F hF P K D hD hK R hR]
  rfl

end PullbackCurvature

section Immersion
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)
variable {g : RiemannianMetric S} {C : Connection (tangentBundle S)}
  {D : letI := P.space.topology; Connection P.space.bundle} (G : Geometry i P hP W g C D)

/-- Tangential and normal components before using torsion freeness. -/
theorem tangent_curvature_expansion (X Y Z : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    bundleCurvature D X Y (G.tangentLift Z) =
      G.tangentLift (bundleCurvature C X Y Z -
        G.shape (G.second Y Z) X + G.shape (G.second X Z) Y) +
      G.normalLift (G.second X (C.cov Y Z) + G.CN.cov X (G.second Y Z) -
        G.second Y (C.cov X Z) - G.CN.cov Y (G.second X Z) -
        G.second (bracket X Y) Z) := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  simp only [bundleCurvature, G.gauss, map_add, G.weingarten, map_sub, map_neg, map_smul, neg_one_smul]
  abel

/-- The normal component of the curvature acting on a normal field. -/
theorem normal_curvature_expansion (X Y : Field S)
    (xi : letI := P.space.topology; letI := W.orthogonal.right.topology;
      Section W.orthogonal.right.bundle) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    bundleCurvature D X Y (G.normalLift xi) =
      G.tangentLift (-C.cov X (G.shape xi Y) - G.shape (G.CN.cov Y xi) X +
        C.cov Y (G.shape xi X) + G.shape (G.CN.cov X xi) Y +
        G.shape xi (bracket X Y)) +
      G.normalLift (normalCurvature G X Y xi - G.second X (G.shape xi Y) +
        G.second Y (G.shape xi X)) := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  simp only [normalCurvature, bundleCurvature, G.weingarten, map_add, map_neg,
    G.gauss, map_sub, map_smul, neg_one_smul]
  abel

/-- Torsion freeness is precisely the cancellation needed in Codazzi. -/
theorem codazzi_grouping (hC : IsTorsionFree C) (X Y Z : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    G.second X (C.cov Y Z) + G.CN.cov X (G.second Y Z) -
      G.second Y (C.cov X Z) - G.CN.cov Y (G.second X Z) -
      G.second (bracket X Y) Z = covariantB G X Y Z - covariantB G Y X Z := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  rw [CurvatureAlgebra.bracket_cov C hC]
  simp only [covariantB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  module

theorem gauss_equation
    (hiP : letI := P.space.topology; ∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w)
    (X Y Z V : Field S) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    pairing g p ((bundleCurvature C X Y Z).val p) (V.val p) =
      hP.form p ((bundleCurvature D X Y (G.tangentLift Z)).val p)
        (i.differential p (V.val p)) +
      hP.form p (G.B p (X.val p) (V.val p)).val (G.B p (Y.val p) (Z.val p)).val -
      hP.form p (G.B p (Y.val p) (V.val p)).val (G.B p (X.val p) (Z.val p)).val := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  have he := congrArg (fun s : Section P.space.bundle => s.val p)
    (tangent_curvature_expansion i P hP W G X Y Z)
  simp only [section_add_apply, G.tangentLift_val, G.normalLift_val, Submodule.subtype_apply] at he
  have hn (z : (hP.form p).orthogonal (tangentImage i p)) :
      hP.form p z.val (i.differential p (V.val p)) = 0 :=
    (hP.symmetric p z.val (i.differential p (V.val p))).trans
      (GaussWeingarten.tangent_normal_orthogonal i P hP p (V.val p) z)
  have hp := congrArg (fun z : TangentSpace T (F p) =>
    hP.form p z (i.differential p (V.val p))) he
  rw [map_add, LinearMap.add_apply] at hp
  have hm := hiP p ((bundleCurvature C X Y Z - G.shape (G.second Y Z) X +
    G.shape (G.second X Z) Y).val p) (V.val p)
  have hz := hn ((G.second X (C.cov Y Z) + G.CN.cov X (G.second Y Z) -
    G.second Y (C.cov X Z) - G.CN.cov Y (G.second X Z) -
    G.second (bracket X Y) Z).val p)
  have hpair : hP.form p ((bundleCurvature D X Y (G.tangentLift Z)).val p)
      (i.differential p (V.val p)) = pairing g p
        ((bundleCurvature C X Y Z - G.shape (G.second Y Z) X +
          G.shape (G.second X Z) Y).val p) (V.val p) :=
    hp.trans ((congrArg₂ (fun x y : ℝ => x + y) hm hz).trans (add_zero _))
  rw [hpair]
  have hs (s t : Field S) : (s - t).val p = s.val p - t.val p := rfl
  simp only [section_add_apply, hs, G.shape_val, G.second_val,
    LeviCivita.tangent_sub_as_add, map_add, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
  rw [G.adjoint, G.adjoint]
  simp only [Submodule.subtype_apply]
  ring

theorem codazzi_equation (hC : IsTorsionFree C) (X Y Z : Field S) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    letI := W.sum.space.topology
    ((W.iso.equiv p).symm ((bundleCurvature D X Y (G.tangentLift Z)).val p)).2 =
      (covariantB G X Y Z - covariantB G Y X Z).val p := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  have he := congrArg (fun s : Section P.space.bundle => s.val p)
    (tangent_curvature_expansion i P hP W G X Y Z)
  rw [codazzi_grouping i P hP W G hC] at he
  simp only [section_add_apply, G.tangentLift_val, G.normalLift_val, Submodule.subtype_apply] at he
  rw [he]
  exact congrArg Prod.snd (GaussWeingarten.inverse_on_sum i P hP W p
    ((bundleCurvature C X Y Z - G.shape (G.second Y Z) X + G.shape (G.second X Z) Y).val p)
    ((covariantB G X Y Z - covariantB G Y X Z).val p))

set_option maxHeartbeats 2000000 in
theorem ricci_equation (X Y : Field S)
    (xi eta : letI := P.space.topology; letI := W.orthogonal.right.topology;
      Section W.orthogonal.right.bundle) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    hP.form p ((normalCurvature G X Y xi).val p).val (eta.val p).val =
      hP.form p ((bundleCurvature D X Y (G.normalLift xi)).val p) (eta.val p).val +
      pairing g p
        (G.A p (xi.val p) (G.A p (eta.val p) (X.val p)) -
         G.A p (eta.val p) (G.A p (xi.val p) (X.val p))) (Y.val p) := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  have he := congrArg (fun s : Section P.space.bundle => s.val p)
    (normal_curvature_expansion i P hP W G X Y xi)
  simp only [section_add_apply, G.tangentLift_val, G.normalLift_val, Submodule.subtype_apply] at he
  rw [he, map_add, LinearMap.add_apply,
    GaussWeingarten.tangent_normal_orthogonal i P hP, zero_add]
  simp only [Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply,
    G.second_val, G.shape_val]
  simp only [Submodule.coe_sub, Submodule.coe_add, map_sub, map_add,
    LinearMap.sub_apply, LinearMap.add_apply]
  have hadj (z : (hP.form p).orthogonal (tangentImage i p)) (v w : TangentSpace S p) :
      pairing g p (G.A p z v) w = hP.form p (G.B p v w).val z.val :=
    G.adjoint p z v w
  rw [LeviCivita.tangent_sub_as_add p
    (G.A p (xi.val p) (G.A p (eta.val p) (X.val p)))
    (G.A p (eta.val p) (G.A p (xi.val p) (X.val p)))]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul]
  have hsym : pairing g p (G.A p (eta.val p) (Y.val p))
      (G.A p (xi.val p) (X.val p)) =
      pairing g p (G.A p (xi.val p) (X.val p))
        (G.A p (eta.val p) (Y.val p)) :=
    g.symmetric p (G.A p (eta.val p) (Y.val p)) (G.A p (xi.val p) (X.val p))
  rw [← hadj (eta.val p) (X.val p) (G.A p (xi.val p) (Y.val p)),
    ← hadj (eta.val p) (Y.val p) (G.A p (xi.val p) (X.val p)),
    G.selfAdjoint p (xi.val p) (G.A p (eta.val p) (X.val p)) (Y.val p),
    G.selfAdjoint p (eta.val p) (G.A p (xi.val p) (X.val p)) (Y.val p),
    hsym]
  ring

/-- Adapter from the accepted Gauss–Weingarten conclusion. In particular,
none of the first-order geometric data is an additional existence assumption. -/
noncomputable def geometryOfConclusion
    (hG : GaussWeingartenConclusion i P hP g C D W) :
    Nonempty (Geometry i P hP W g C D) := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  obtain ⟨CT, CN, hN, B, A, hCT, _, _, hgauss, hwein, hBs, hAs, hsym, hadj, hself⟩ := hG
  subst CT
  let L := GaussWeingarten.mapSections (tangentBundle S) P.space.bundle
    (GaussWeingarten.differentialMorphism i P)
  let J := GaussWeingarten.mapSections W.orthogonal.right.bundle P.space.bundle
    (GaussWeingarten.normalInclusionMorphism i P hP W)
  let bOp := bilinearSections (tangentBundle S) (tangentBundle S)
    W.orthogonal.right.bundle B hBs
  let aOp := bilinearSections W.orthogonal.right.bundle (tangentBundle S)
    (tangentBundle S) A hAs
  refine ⟨{
    CN := CN
    second := bOp
    shape := aOp
    tangentLift := L
    normalLift := J
    tangentLift_val := fun _ _ => rfl
    normalLift_val := fun _ _ => rfl
    B := B
    A := A
    second_val := fun _ _ _ => rfl
    shape_val := fun _ _ _ => rfl
    gauss := ?_
    weingarten := ?_
    symmetric := hsym
    adjoint := hadj
    selfAdjoint := hself }⟩
  · intro X Y
    obtain ⟨V, hV, _, _, hv⟩ := hgauss X Y
    have hVL : V = L Y := section_ext hV
    rw [hVL] at hv
    apply section_ext
    intro p
    exact hv p
  · intro X xi
    obtain ⟨U, hU, _, _, hu⟩ := hwein X xi
    have hUJ : U = J xi := section_ext hU
    rw [hUJ] at hu
    apply section_ext
    intro p
    simp only [section_add_apply, neg_one_smul, ConnectionForms.section_neg_apply]
    change (D.cov X (J xi)).val p =
      -i.differential p (A p (xi.val p) (X.val p)) + ((CN.cov X xi).val p).val
    exact hu p

end Immersion

theorem equations : P202Specs.Geometry.GaussCodazziRicci.equationsType.{u} := by
  intro n m a b M N _ _ S T F i P
  letI := P.space.topology
  intro hP W g C D hC hiP G
  exact ⟨gauss_equation i P hP W G hiP,
    codazzi_equation i P hP W G hC.1,
    ricci_equation i P hP W G⟩

theorem geometry_exists : P202Specs.Geometry.GaussCodazziRicci.geometry_existsType.{u} := by
  intro n m a b M N _ _ S T g h F i hi C K hC hK P
  letI := P.space.topology
  obtain ⟨hP, D, W, hhP, hDP, hG⟩ :=
    GaussWeingarten.exists_geometry g h F i hi C K hC hK P
  exact ⟨hP, D, W, hhP, hDP, geometryOfConclusion i P hP W hG⟩

theorem pullback_curvature : P202Specs.Geometry.GaussCodazziRicci.pullback_curvatureType.{u} := by
  intro n m a b M N _ _ S T F i K R hK hR P
  letI := P.space.topology
  intro D hD X Y s p
  simpa only [← GaussWeingarten.immersion_differential_eq i p] using
    curvature_pullback F i.smooth P K D hD hK R hR X Y s p

theorem bundleCurvature_tangent
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)) (X Y Z : Field S) :
    bundleCurvature C X Y Z = P202.CurvatureData.curvature C X Y Z := by
  apply section_ext; intro p
  rw [bundleCurvature_apply, CurvatureAlgebra.curvature_apply]

section AmbientAssembly
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)
  (g : RiemannianMetric S) (C : Connection (tangentBundle S))
  (K : Connection (tangentBundle T))
  (D : letI := P.space.topology; Connection P.space.bundle)

theorem ambient_equations (hC : IsLeviCivita g C) (hK : IsTorsionFree K)
    (hiP : letI := P.space.topology;
      ∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w)
    (hD : letI := P.space.topology;
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D)
    (R₀ : P202.CurvatureData.CurvatureTensor S) (R : P202.CurvatureData.CurvatureTensor T)
    (hR₀ : P202.CurvatureData.RepresentsCurvature C R₀)
    (hR : P202.CurvatureData.RepresentsCurvature K R)
    (G : Geometry i P hP W g C D) : AmbientEquations G R₀ R := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  obtain ⟨hgauss, hcodazzi, hricci⟩ := equations i P hP W g C D hC hiP G
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z V p
    have he := hgauss X Y Z V p
    rw [bundleCurvature_tangent,
      pullback_curvature i K R hK hR P D hD, G.tangentLift_val] at he
    change pairing g p (R₀.val p (X.val p) (Y.val p) (Z.val p)) (V.val p) = _
    rw [hR₀ X Y Z p]
    exact he
  · intro X Y Z p
    have he := hcodazzi X Y Z p
    rw [pullback_curvature i K R hK hR P D hD, G.tangentLift_val] at he
    exact he
  · intro X Y xi eta p
    have he := hricci X Y xi eta p
    rw [pullback_curvature i K R hK hR P D hD, G.normalLift_val] at he
    exact he

end AmbientAssembly

/-- Theorem 7.5, including construction of the normal geometry and evaluation
of every ambient curvature slot in the actual pullback fiber. -/
theorem curvature_equations : P202Specs.Geometry.GaussCodazziRicci.curvature_equationsType.{u} := by
  intro n m a b M N _ _ S T g h F i hi C K hC hK R₀ R hR₀ hR P
  letI := P.space.topology
  obtain ⟨hP, D, W, hhP, hDP, ⟨G⟩⟩ := geometry_exists g h F i hi C K hC hK P
  have hiP : ∀ p v w,
      hP.form p (i.differential p v) (i.differential p w) = pairing g p v w := by
    intro p v w
    rw [hhP]
    exact hi p v w
  exact ⟨hP, D, W, G, hhP, hDP,
    ambient_equations i P hP W g C K D hC hK.1 hiP hDP R₀ R hR₀ hR G⟩

end P202.Geometry.GaussCodazziRicci
