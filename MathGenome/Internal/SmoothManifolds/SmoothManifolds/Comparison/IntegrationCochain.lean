import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.IntegrationCochain
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.SimplexPullbackIntegral
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.SmoothSingularComplex
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.AmbientSimplexStokes

/-! The natural integration map on the full de Rham and smooth singular
complexes, using the literal simplex pullback integrals and corner Stokes. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped Classical
namespace SmoothManifolds.IntegrationCochain
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  SmoothSingularData CornerData DeRhamData IntegrationCochainData Set MeasureTheory
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B}

/-- Outward-first orientation of every ordered face, including endpoint faces. -/
theorem face_orientation :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.face_orientationType :=
  AmbientSimplexStokes.face_orientation

theorem face_outward :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.face_outwardType :=
  AmbientSimplexStokes.face_outward

theorem simplex_isCompact (q : ℕ) : IsCompact (simplexSet q) :=
  SimplexPullbackIntegral.simplex_isCompact q

theorem simplexIntegral_add {q : ℕ} (α β : Field S q) (σ : SingularSimplex S q)
    (hα : IntegrableOn (ambientPullbackCoefficient S C α σ) (simplexSet q))
    (hβ : IntegrableOn (ambientPullbackCoefficient S C β σ) (simplexSet q)) :
    simplexIntegral S C (α+β) σ = simplexIntegral S C α σ + simplexIntegral S C β σ :=
  SimplexPullbackIntegral.simplexIntegral_add α β σ hα hβ

theorem simplexIntegral_smul {q : ℕ} (r : ℝ) (α : Field S q) (σ : SingularSimplex S q) :
    simplexIntegral S C (r • α) σ = r • simplexIntegral S C α σ :=
  SimplexPullbackIntegral.simplexIntegral_smul r α σ

/-- The empty-product integral is evaluation on the unique zero-simplex point. -/
theorem simplexIntegral_zero (ω : Field S 0) (σ : SingularSimplex S 0)
    (x : SmoothSingularData.Simplex 0) :
    simplexIntegral S C ω σ =
      exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S (σ.val x))) (ω (σ.val x)) :=
  SimplexPullbackIntegral.simplexIntegral_zero ω σ x

/-- Compactness gives integrability for all smooth forms, with no support restriction. -/
theorem integrability :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.integrabilityType := by
  intro n q a M _ S C B ω σ
  exact ⟨simplex_isCompact q, SimplexPullbackIntegral.integrability S C B ω σ⟩

theorem simplexStokes (q : ℕ) (ω : K.forms q) (σ : SingularSimplex S (q+1)) :
    ∃ τ : Fin (q+2) → SingularSimplex S q,
      (∀ j, (τ j).val = σ.val ∘ face j) ∧
      simplexIntegral S C (K.d q ω).val σ =
        ∑ j, (-1 : ℝ)^j.val * simplexIntegral S C ω.val (τ j) := by
  let α := SimplexPullbackIntegral.coordinatePullback (C := C) ω.val σ
  have hω : IsForm (B q) ω.val := (K.mem_forms q ω.val).mp ω.property
  have hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val) := by
    intro x
    obtain ⟨U,hU,hxU,F,hF,hEq⟩ :=
      SimplexPullbackIntegral.coordinatePullback_smooth (B q) ω.val hω σ x
    exact ⟨U,hU,hxU,F,hF.of_le (by simp),hEq⟩
  have hstokes := (AmbientSimplexStokes.stokes q α hα).2.2
  let τ : Fin (q+2) → SingularSimplex S q := fun j =>
    ⟨σ.val ∘ face j, SmoothSingular.smooth_face σ.property j⟩
  refine ⟨τ, fun _ => rfl, ?_⟩
  have hbulk : simplexIntegral S C (K.d q ω).val σ =
      ∫ x in simplexSet (q+1), AmbientSimplexData.bulkCoefficient α x := by
    apply setIntegral_congr_fun (SimplexPullbackIntegral.simplex_isCompact _).measurableSet
    intro x hx
    simp only [ambientPullbackCoefficient, hx, dite_true]
    unfold AmbientSimplexData.bulkCoefficient α
    rw [SimplexPullbackIntegral.coordinatePullback_derivative B K ω.val hω σ ⟨x,hx⟩]
    exact (SimplexPullbackIntegral.coordinatePullback_top (K.D q ω.val) σ ⟨x,hx⟩).symm
  rw [hbulk, hstokes]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold simplexIntegral
  apply setIntegral_congr_fun (SimplexPullbackIntegral.simplex_isCompact _).measurableSet
  intro y hy
  simp only [ambientPullbackCoefficient, hy, dite_true]
  have hface := SimplexPullbackIntegral.coordinatePullback_precompose (C := C)
    ω.val σ (face j) (faceAmbient j) (SmoothSingular.faceAmbient_smooth j)
    (SmoothSingular.face_val j) (SmoothSingular.smooth_face σ.property j) ⟨y,hy⟩
  rw [← SimplexPullbackIntegral.coordinatePullback_top ω.val (τ j) ⟨y,hy⟩]
  rw [show SimplexPullbackIntegral.coordinatePullback (C := C) ω.val (τ j) y =
      (α (face j ⟨y,hy⟩).val).compContinuousLinearMap (fderiv ℝ (faceAmbient j) y) from hface]
  rfl

/-- The linear extension in the chain variable uses the free real chain space. -/
def integrationCochain {q : ℕ} (ω : Field S q) : Cochains S q :=
  Finsupp.linearCombination ℝ (fun σ => simplexIntegral S C ω σ)

@[simp] theorem integrationCochain_single {q : ℕ} (ω : Field S q)
    (σ : SingularSimplex S q) :
    integrationCochain (C := C) ω (Finsupp.single σ 1) = simplexIntegral S C ω σ := by
  simp [integrationCochain]

/-- Assembly lemma: analytic integrability supplies linearity in the form. -/
def linearIntegration
    (hi : ∀ q (ω : K.forms q) (σ : SingularSimplex S q),
      IntegrableOn (ambientPullbackCoefficient S C ω.val σ) (simplexSet q))
    (q : ℕ) : K.forms q →ₗ[ℝ] Cochains S q where
  toFun ω := integrationCochain ω.val
  map_add' α β := by
    apply Finsupp.lhom_ext
    intro σ r
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul]
    congr 1
    simp only [integrationCochain_single, LinearMap.add_apply]
    exact simplexIntegral_add α.val β.val σ (hi q α σ) (hi q β σ)
  map_smul' r α := by
    apply Finsupp.lhom_ext
    intro σ t
    have ht : Finsupp.single σ t = t • Finsupp.single σ 1 := by simp
    rw [ht, map_smul, map_smul]
    congr 1
    simp only [integrationCochain_single, LinearMap.smul_apply, RingHom.id_apply]
    exact simplexIntegral_smul r α.val σ

/-- Algebraic assembly from literal-integral integrability and simplex Stokes. -/
def integrationMapOfStokes
    (hi : ∀ q (ω : K.forms q) (σ : SingularSimplex S q),
      IntegrableOn (ambientPullbackCoefficient S C ω.val σ) (simplexSet q))
    (hs : ∀ q (ω : K.forms q) (σ : SingularSimplex S (q+1)),
      ∃ τ : Fin (q+2) → SingularSimplex S q,
        (∀ j, (τ j).val = σ.val ∘ face j) ∧
        simplexIntegral S C (K.d q ω).val σ =
          ∑ j, (-1 : ℝ)^j.val * simplexIntegral S C ω.val (τ j)) :
    IntegrationMap S K where
  map := linearIntegration hi
  evaluation q ω σ := integrationCochain_single ω.val σ
  commutes q ω := by
    apply Finsupp.lhom_ext
    intro σ r
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul]
    congr 1
    obtain ⟨τ,hτ,hs⟩ := hs q ω σ
    have hg (j : Fin (q+2)) : generate S (σ.val ∘ face j) = Finsupp.single (τ j) 1 := by
      rw [← hτ j]
      simp [generate, (τ j).property]
    change integrationCochain (K.d q ω).val (Finsupp.single σ 1) =
      integrationCochain ω.val (boundary S q (Finsupp.single σ 1))
    rw [integrationCochain_single, hs]
    simp only [boundary, Finsupp.linearCombination_single, one_smul, map_sum, map_smul, hg,
      integrationCochain_single, smul_eq_mul]

theorem integrable_stokes_suffice :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.integrable_stokes_sufficeType.{u} := by
  intro n a M _ S C B K hi hs
  exact ⟨integrationMapOfStokes hi hs⟩

/-- Simplex Stokes applies to every smooth form and every closed simplex. -/
theorem simplex_stokes :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.simplex_stokesType.{u} := by
  intro n q a M _ S C B K ω σ
  exact simplexStokes q ω σ

/-- The literal integral defines a real linear cochain map in all degrees. -/
theorem integration_exists :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.integration_existsType.{u} := by
  intro n a M _ S C B K
  exact ⟨integrationMapOfStokes
    (fun q ω σ => SimplexPullbackIntegral.simplexIntegral_integrable
      (B q) ω.val ((K.mem_forms q ω.val).mp ω.property) σ)
    (fun q ω σ => simplex_stokes S C B K ω σ)⟩

/-- Evaluation determines the integration cochain map uniquely. -/
theorem integrationMap_unique (I J : IntegrationMap S K) : I = J := by
  have hm : I.map = J.map := by
    funext q
    apply LinearMap.ext
    intro ω
    apply Finsupp.lhom_ext
    intro σ r
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul, I.evaluation, J.evaluation]
  cases I
  cases J
  cases hm
  rfl

namespace IntegrationMap
variable (I : IntegrationCochainData.IntegrationMap S K)

/-- Closed forms map into the actual smooth singular cocycles. -/
def closedMap (q : ℕ) : K.closed q →ₗ[ℝ] cocycles S q :=
  LinearMap.codRestrict (cocycles S q) ((I.map q).comp (K.closed q).subtype) (by
    intro ω
    change coboundary S q (I.map q ω.val) = 0
    rw [← I.commutes q ω.val]
    have hω : K.d q ω.val = 0 := ω.property
    rw [hω, map_zero])

/-- Exact forms map into incoming singular coboundaries, including degree zero. -/
theorem maps_boundaries (q : ℕ) (ω : K.closed q) (hω : ω ∈ K.boundaries q) :
    closedMap I q ω ∈ coboundaries S q := by
  change (closedMap I q ω).val ∈ LinearMap.range (previousCoboundary S q)
  change ω.val ∈ K.exact q at hω
  cases q with
  | zero =>
      have hw : ω.val = 0 := hω
      refine ⟨0, ?_⟩
      change previousCoboundary S 0 0 = I.map 0 ω.val
      simp [hw]
  | succ q =>
      obtain ⟨η,hη⟩ := hω
      refine ⟨I.map q η, ?_⟩
      change coboundary S q (I.map q η) = I.map (q+1) ω.val
      rw [← I.commutes, hη]

/-- Descent to the original quotients, using the exact and coboundary submodules. -/
def cohomologyMap (q : ℕ) : K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q :=
  (K.boundaries q).liftQ ((singularClass S q).comp (closedMap I q)) (by
    intro ω hω
    change singularClass S q (closedMap I q ω) = 0
    change closedMap I q ω ∈ LinearMap.ker (coboundaries S q).mkQ
    rw [Submodule.ker_mkQ]
    exact maps_boundaries I q ω hω)

@[simp] theorem cohomologyMap_class (q : ℕ) (ω : K.closed q) :
    cohomologyMap I q (K.classOf q ω) = singularClass S q (closedMap I q ω) := rfl

/-- The induced map is the unique linear map with its values on closed representatives. -/
theorem cohomologyMap_unique (q : ℕ)
    (F : K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q)
    (hF : ∀ ω : K.closed q,
      F (K.classOf q ω) = singularClass S q (closedMap I q ω)) :
    F = cohomologyMap I q := by
  apply LinearMap.ext
  intro x
  obtain ⟨ω,rfl⟩ := (K.boundaries q).mkQ_surjective x
  exact hF ω

end IntegrationMap
/-- Every realization induces unique real-linear maps on the original cohomology quotients. -/
theorem cohomology_exists :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.cohomology_existsType.{u} := by
  intro n a M _ S C B K I
  refine ⟨fun q => IntegrationMap.cohomologyMap I q, ?_, ?_⟩
  · intro q ω
    exact ⟨IntegrationMap.closedMap I q ω, rfl, rfl⟩
  · intro F hF
    funext q
    apply IntegrationMap.cohomologyMap_unique I q
    intro ω
    obtain ⟨c,hc,he⟩ := hF q ω
    have hc' : c = IntegrationMap.closedMap I q ω := Subtype.ext hc
    rw [he, hc']

/-- Literal integration commutes with actual smooth pullback. -/
theorem naturality :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.naturalityType.{u} := by
  intro n m q a b M N _ _ S T C A f hf L hL ω B hω σ hσ
  obtain ⟨τ,hτ,hint⟩ := SimplexPullbackIntegral.integral_naturality T A σ f hf L hL
  have heq : τ = ⟨f ∘ σ.val,hσ⟩ := Subtype.ext hτ
  simpa only [heq] using hint ω

namespace SingularPullback
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : SmoothManifold n a M) (T : SmoothManifold m b N)
  (f : M → N) (hf : MapData.IsSmoothMap S T f)

/-- The actual cochain pullback takes cocycles to cocycles. -/
def closedMap (q : ℕ) : cocycles T q →ₗ[ℝ] cocycles S q :=
  LinearMap.codRestrict (cocycles S q)
    ((cochainMap S T f q).comp (cocycles T q).subtype) (by
      intro c
      change coboundary S q (cochainMap S T f q c.val) = 0
      have hcomm := LinearMap.congr_fun (SmoothSingular.cochainMap_coboundary S T hf q) c.val
      change coboundary S q (cochainMap S T f q c.val) =
        cochainMap S T f (q+1) (coboundary T q c.val) at hcomm
      rw [hcomm]
      have hc : coboundary T q c.val = 0 := c.property
      rw [hc,map_zero])

/-- Pullback preserves the full incoming coboundaries, including zero degree. -/
theorem maps_boundaries (q : ℕ) (c : cocycles T q) (hc : c ∈ coboundaries T q) :
    closedMap S T f hf q c ∈ coboundaries S q := by
  change (closedMap S T f hf q c).val ∈ LinearMap.range (previousCoboundary S q)
  change c.val ∈ LinearMap.range (previousCoboundary T q) at hc
  obtain ⟨b,hb⟩ := hc
  cases q with
  | zero =>
      have hc0 : c.val = 0 := by simpa only [previousCoboundary,LinearMap.zero_apply] using hb.symm
      refine ⟨0, ?_⟩
      change previousCoboundary S 0 0 = cochainMap S T f 0 c.val
      simp [hc0,previousCoboundary]
  | succ q =>
      refine ⟨cochainMap S T f q b, ?_⟩
      change coboundary S q (cochainMap S T f q b) = cochainMap S T f (q+1) c.val
      have hcomm := LinearMap.congr_fun (SmoothSingular.cochainMap_coboundary S T hf q) b
      change coboundary S q (cochainMap S T f q b) =
        cochainMap S T f (q+1) (coboundary T q b) at hcomm
      exact hcomm.trans (congrArg (cochainMap S T f (q+1)) hb)

/-- Pullback on the already defined smooth singular cohomology quotients. -/
def cohomologyMap (q : ℕ) : SmoothSingularData.Cohomology T q →ₗ[ℝ]
    SmoothSingularData.Cohomology S q :=
  (coboundaries T q).liftQ ((singularClass S q).comp (closedMap S T f hf q)) (by
    intro c hc
    change singularClass S q (closedMap S T f hf q c) = 0
    change closedMap S T f hf q c ∈ LinearMap.ker (coboundaries S q).mkQ
    rw [Submodule.ker_mkQ]
    exact maps_boundaries S T f hf q c hc)

@[simp] theorem cohomologyMap_class (q : ℕ) (c : cocycles T q) :
    cohomologyMap S T f hf q (singularClass T q c) =
      singularClass S q (closedMap S T f hf q c) := rfl
end SingularPullback

/-- Smooth pullback descends to smooth singular cohomology. -/
theorem singular_pullback_exists :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.singular_pullback_existsType.{u} := by
  intro n m a b M N _ _ S T f hf
  refine ⟨SingularPullback.cohomologyMap S T f hf, ?_⟩
  intro q c
  exact ⟨SingularPullback.closedMap S T f hf q c,rfl,rfl⟩

/-- The whole cochain agrees, since equality holds on every smooth simplex. -/
theorem integrationMap_pullback
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (I : IntegrationMap S K) (H : IntegrationMap T J)
    (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (q : ℕ) (α : J.forms q) (β : K.forms q)
    (hβ : β.val = FormPullbackData.pullbackField S T f L α.val) :
    I.map q β = cochainMap S T f q (H.map q α) := by
  apply Finsupp.lhom_ext
  intro σ r
  have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  rw [I.evaluation]
  change simplexIntegral S C β.val σ =
    H.map q α (chainMap S T f q (Finsupp.single σ 1))
  have hσ := SmoothSingular.smooth_postcompose hf σ.property
  rw [SmoothSingular.chainMap_single,one_smul,SmoothSingular.generate_smooth T hσ,H.evaluation]
  rw [hβ]
  exact naturality S T C A f hf L hL α.val (E q)
    ((J.mem_forms q α.val).mp α.property) σ hσ


section CohomologyNaturality
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
/-- Naturality on the original quotients, proved on every closed representative. -/
theorem cohomology_naturality :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.cohomology_naturalityType.{u} := by
  intro n m a b M N _ _ S T C A B E K J I H F G hF hG f hf L hL P Q hP hQ q x
  refine Submodule.Quotient.induction_on _ x ?_
  intro α
  have hpα := hP q α
  let β : K.closed q := hpα.choose
  have hβ := hpα.choose_spec.1
  have hPβ := hpα.choose_spec.2
  have hdex := hF q β
  let d : cocycles S q := hdex.choose
  have hd := hdex.choose_spec.1
  have hFβ := hdex.choose_spec.2
  have hcex := hG q α
  let c : cocycles T q := hcex.choose
  have hc := hcex.choose_spec.1
  have hGα := hcex.choose_spec.2
  have heex := hQ q c
  let e : cocycles S q := heex.choose
  have he := heex.choose_spec.1
  have hQe := heex.choose_spec.2
  have hde : d = e := Subtype.ext (hd.trans (
    (integrationMap_pullback S T C A B E K J I H f hf L hL q α.val β.val hβ).trans
      (he.trans (congrArg (cochainMap S T f q) hc)).symm))
  change F q (P q (J.classOf q α)) = Q q (G q (J.classOf q α))
  calc F q (P q (J.classOf q α)) = F q (K.classOf q β) := congrArg (F q) hPβ
    _ = singularClass S q d := hFβ
    _ = singularClass S q e := congrArg (singularClass S q) hde
    _ = Q q (singularClass T q c) := hQe.symm
    _ = Q q (G q (J.classOf q α)) := congrArg (Q q) hGα.symm
end CohomologyNaturality

/-- Simultaneous existence of integration and its real-linear quotient maps. -/
theorem integration_cohomology_exists :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.integration_cohomology_existsType.{u} := by
  intro n a M _ S C B K
  obtain ⟨I⟩ := integration_exists S C B K
  exact ⟨I, cohomology_exists S C B K I⟩

/-- The boundary integral in dimension one has the signed endpoint convention. -/
theorem endpoint_sum :
    Specs.SmoothManifolds.Comparison.IntegrationCochain.endpoint_sumType :=
  AmbientSimplexStokes.endpoint_sum

end SmoothManifolds.IntegrationCochain
