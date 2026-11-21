import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.StatementInterface
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.SmoothSingularComplex

/-! Continuous singular chains, restriction, and the statement-only comparison
interface. Neither comparison isomorphism is proved or postulated here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical

namespace SmoothManifolds.ContinuousSingular
open ContinuousSingularData
open SmoothSingularData (Simplex face)
universe u v w
variable {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

abbrev SingularSimplex := @ContinuousSingularData.SingularSimplex
abbrev Chains := @ContinuousSingularData.Chains
abbrev Cochains := @ContinuousSingularData.Cochains
abbrev generate := @ContinuousSingularData.generate
abbrev boundary := @ContinuousSingularData.boundary
abbrev boundaryZero := @ContinuousSingularData.boundaryZero
abbrev coboundary := @ContinuousSingularData.coboundary
abbrev cocycles := @ContinuousSingularData.cocycles
abbrev previousCoboundary := @ContinuousSingularData.previousCoboundary
abbrev coboundaries := @ContinuousSingularData.coboundaries
abbrev Cohomology := @ContinuousSingularData.Cohomology
abbrev classOf := @ContinuousSingularData.classOf
abbrev chainMap := @ContinuousSingularData.chainMap
abbrev cochainMap := @ContinuousSingularData.cochainMap
abbrev cohomologyPullback := @ContinuousSingularData.cohomologyPullback

@[simp] theorem generate_continuous {q : ℕ} {f : Simplex q → M} (hf : Continuous f) :
    generate M f = Finsupp.single ⟨f,hf⟩ 1 := by
  simp [generate, ContinuousSingularData.generate, hf]

@[simp] theorem generate_simplex {q : ℕ} (σ : SingularSimplex M q) :
    generate M σ.val = Finsupp.single σ 1 := generate_continuous σ.property

@[simp] theorem boundary_generate {q : ℕ} {f : Simplex (q+1) → M} (hf : Continuous f) :
    boundary M q (generate M f) =
      ∑ j : Fin (q+2), (-1 : ℝ)^j.val • generate M (f ∘ face j) := by
  rw [generate_continuous hf]
  simp [boundary, ContinuousSingularData.boundary]

@[simp] theorem boundary_single {q : ℕ} (σ : SingularSimplex M (q+1)) (r : ℝ) :
    boundary M q (Finsupp.single σ r) =
      r • ∑ j : Fin (q+2), (-1 : ℝ)^j.val • generate M (σ.val ∘ face j) := by
  simp [boundary, ContinuousSingularData.boundary]

/-- The face cancellation uses the same ordered geometric face identity. -/
theorem boundary_squared (q : ℕ) :
    (boundary M q).comp (boundary M (q+1)) = 0 := by
  apply Finsupp.lhom_ext
  intro σ r
  change boundary M q (boundary M (q+1) (Finsupp.single σ r)) = 0
  rw [boundary_single, map_smul]
  suffices h : boundary M q (∑ j : Fin (q+3),
      (-1 : ℝ)^j.val • generate M (σ.val ∘ face j)) = 0 by rw [h, smul_zero]
  rw [map_sum]
  simp only [map_smul]
  have he (j : Fin (q+3)) : boundary M q (generate M (σ.val ∘ face j)) =
      ∑ i : Fin (q+2), (-1 : ℝ)^i.val • generate M ((σ.val ∘ face j) ∘ face i) :=
    boundary_generate (σ.property.comp (SmoothSingular.face_continuous j))
  simp_rw [he, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]
  apply SmoothSingular.alternating_double_sum q
  intro i j hij
  congr 1
  rw [Function.comp_assoc, SmoothSingular.face_comp_face i j hij, ← Function.comp_assoc]

theorem coboundary_squared (q : ℕ) :
    (coboundary M (q+1)).comp (coboundary M q) = 0 := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro z
  change c (boundary M q (boundary M (q+1) z)) = 0
  have hz := LinearMap.congr_fun (boundary_squared (M := M) q) z
  change boundary M q (boundary M (q+1) z) = 0 at hz
  rw [hz, map_zero]

theorem coboundaries_are_cocycles (q : ℕ) :
    LinearMap.range (previousCoboundary M q) ≤ cocycles M q := by
  cases q with
  | zero =>
    rintro c ⟨b,rfl⟩
    exact (cocycles M 0).zero_mem
  | succ q =>
    rintro c ⟨b,rfl⟩
    exact LinearMap.congr_fun (coboundary_squared (M := M) q) b

@[simp] theorem zero_incoming : coboundaries M 0 = ⊥ := by
  ext c
  change (∃ x, (0 : Cochains M 0 →ₗ[ℝ] Cochains M 0) x = c.val) ↔ c = 0
  simp only [LinearMap.zero_apply, exists_const]
  exact ⟨fun h => Subtype.ext h.symm, fun h => by simp [h]⟩

@[simp] theorem chainMap_single (f : M → N) (q : ℕ) (σ : SingularSimplex M q) (r : ℝ) :
    chainMap f q (Finsupp.single σ r) = r • generate N (f ∘ σ.val) := by
  simp [chainMap, ContinuousSingularData.chainMap]

@[simp] theorem chainMap_generate (f : M → N) {q : ℕ} {σ : Simplex q → M}
    (hσ : Continuous σ) : chainMap f q (generate M σ) = generate N (f ∘ σ) := by
  rw [generate_continuous hσ, chainMap_single, one_smul]

theorem chainMap_id (q : ℕ) : chainMap (id : M → M) q = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ r
  simp

theorem chainMap_comp {f : M → N} {g : N → P} (hf : Continuous f) (q : ℕ) :
    chainMap (g ∘ f) q = (chainMap g q).comp (chainMap f q) := by
  apply Finsupp.lhom_ext
  intro σ r
  simp only [LinearMap.comp_apply, chainMap_single, map_smul]
  rw [chainMap_generate g (hf.comp σ.property)]
  rfl

theorem chainMap_boundary {f : M → N} (hf : Continuous f) (q : ℕ) :
    (boundary N q).comp (chainMap f (q+1)) = (chainMap f q).comp (boundary M q) := by
  apply Finsupp.lhom_ext
  intro σ r
  simp only [LinearMap.comp_apply, chainMap_single, map_smul, boundary_single]
  rw [boundary_generate (hf.comp σ.property), map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, chainMap_generate f (σ.property.comp (SmoothSingular.face_continuous j))]
  rfl

theorem cochainMap_coboundary {f : M → N} (hf : Continuous f) (q : ℕ) :
    (coboundary M q).comp (cochainMap f q) =
      (cochainMap f (q+1)).comp (coboundary N q) := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro z
  change c (chainMap f q (boundary M q z)) = c (boundary N q (chainMap f (q+1) z))
  exact congrArg c (LinearMap.congr_fun (chainMap_boundary hf q) z).symm

/-- Descent of continuous pullback, with uniqueness on every quotient representative. -/
theorem cohomologyPullback_exists {f : M → N} (hf : Continuous f) (q : ℕ) :
    ∃! F : Cohomology N q →ₗ[ℝ] Cohomology M q,
      ContinuousSingularData.IsPullback f q F := by
  have hz (c : cocycles N q) : cochainMap f q c.val ∈ cocycles M q := by
    change coboundary M q (cochainMap f q c.val) = 0
    have hc : coboundary N q c.val = 0 := c.property
    have he := LinearMap.congr_fun (cochainMap_coboundary hf q) c.val
    change coboundary M q (cochainMap f q c.val) =
      cochainMap f (q+1) (coboundary N q c.val) at he
    rw [he, hc, map_zero]
  let Z : cocycles N q →ₗ[ℝ] cocycles M q :=
    LinearMap.codRestrict _ ((cochainMap f q).comp (cocycles N q).subtype) hz
  have hb : coboundaries N q ≤ (coboundaries M q).comap Z := by
    intro c hc
    obtain ⟨b,hb⟩ := hc
    change ∃ b, previousCoboundary M q b = cochainMap f q c.val
    cases q with
    | zero =>
      have hc0 : c.val = 0 := hb.symm
      exact ⟨0, by simp [hc0, previousCoboundary, ContinuousSingularData.previousCoboundary]⟩
    | succ q =>
      refine ⟨cochainMap f q b, ?_⟩
      have he := LinearMap.congr_fun (cochainMap_coboundary hf q) b
      change coboundary M q (cochainMap f q b) =
        cochainMap f (q+1) (coboundary N q b) at he
      exact he.trans (congrArg (cochainMap f (q+1)) hb)
  let F := (coboundaries N q).mapQ (coboundaries M q) Z hb
  refine ⟨F, fun c => ⟨Z c, rfl, rfl⟩, ?_⟩
  intro G hG
  apply LinearMap.ext
  intro x
  obtain ⟨c,rfl⟩ := (coboundaries N q).mkQ_surjective x
  obtain ⟨d,hd,he⟩ := hG c
  have hdZ : d = Z c := Subtype.ext hd
  exact he.trans (congrArg (classOf M q) hdZ)

theorem cohomologyPullback_spec {f : M → N} (hf : Continuous f) (q : ℕ) :
    ContinuousSingularData.IsPullback f q (cohomologyPullback f q) :=
  Classical.epsilon_spec (cohomologyPullback_exists hf q).exists

end SmoothManifolds.ContinuousSingular

namespace SmoothManifolds.Comparison
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData IntegrationCochainData ComparisonData
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : SmoothManifold n a M) (T : SmoothManifold m b N)

abbrev forgetSimplex := @ComparisonData.forgetSimplex
abbrev inclusion := @ComparisonData.inclusion
abbrev restriction := @ComparisonData.restriction
abbrev restrictionCohomology := @ComparisonData.restrictionCohomology
/-- The later comparison unit is to prove this proposition. This declaration is
only its full statement, with neither an axiom nor a witness of either isomorphism. -/
def comparisonStatement : Prop := ComparisonData.ComparisonStatement.{u}

@[simp] theorem inclusion_single {q : ℕ} (σ : SmoothSingularData.SingularSimplex S q) (r : ℝ) :
    inclusion S q (Finsupp.single σ r) = r • Finsupp.single (forgetSimplex S σ) 1 := by
  simp [inclusion, ComparisonData.inclusion]

@[simp] theorem inclusion_generate {q : ℕ} {σ : SmoothSingularData.Simplex q → M}
    (hσ : SmoothSingularData.SimplexSmooth S σ) :
    inclusion S q (SmoothSingularData.generate S σ) = ContinuousSingularData.generate M σ := by
  simp only [SmoothSingularData.generate, dite_eq_left hσ]
  rw [inclusion_single, one_smul]
  simp only [ContinuousSingularData.generate, dite_eq_left hσ.1]
  rfl

theorem inclusion_boundary (q : ℕ) :
    (ContinuousSingularData.boundary M q).comp (inclusion S (q+1)) =
      (inclusion S q).comp (SmoothSingularData.boundary S q) := by
  apply Finsupp.lhom_ext
  intro σ r
  simp only [LinearMap.comp_apply, inclusion_single, map_smul,
    ContinuousSingular.boundary_single, SmoothSingular.boundary_single, one_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change ContinuousSingularData.generate M (σ.val ∘ SmoothSingularData.face j) = _
  have hj : Continuous (σ.val ∘ SmoothSingularData.face j) :=
    σ.property.1.comp (SmoothSingular.face_continuous j)
  simp only [ContinuousSingularData.generate, dite_eq_left hj]
  rfl

/-- Restriction is an actual cochain map in every degree. -/
theorem restriction_coboundary (q : ℕ) :
    (SmoothSingularData.coboundary S q).comp (restriction S q) =
      (restriction S (q+1)).comp (ContinuousSingularData.coboundary M q) := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro z
  change c (inclusion S q (SmoothSingularData.boundary S q z)) =
    c (ContinuousSingularData.boundary M q (inclusion S (q+1) z))
  exact congrArg c (LinearMap.congr_fun (inclusion_boundary S q) z).symm

/-- The induced r* is constructed without asserting it is bijective. -/
theorem restrictionCohomology_exists (q : ℕ) :
    ∃! F : ContinuousSingularData.Cohomology M q →ₗ[ℝ] SmoothSingularData.Cohomology S q,
      IsRestriction S q F := by
  have hz (c : ContinuousSingularData.cocycles M q) :
      restriction S q c.val ∈ SmoothSingularData.cocycles S q := by
    change SmoothSingularData.coboundary S q (restriction S q c.val) = 0
    have hc : ContinuousSingularData.coboundary M q c.val = 0 := c.property
    have he := LinearMap.congr_fun (restriction_coboundary S q) c.val
    change SmoothSingularData.coboundary S q (restriction S q c.val) =
      restriction S (q+1) (ContinuousSingularData.coboundary M q c.val) at he
    rw [he, hc, map_zero]
  let Z : ContinuousSingularData.cocycles M q →ₗ[ℝ] SmoothSingularData.cocycles S q :=
    LinearMap.codRestrict _ ((restriction S q).comp (ContinuousSingularData.cocycles M q).subtype) hz
  have hb : ContinuousSingularData.coboundaries M q ≤
      (SmoothSingularData.coboundaries S q).comap Z := by
    intro c hc
    obtain ⟨b,hb⟩ := hc
    change ∃ b, SmoothSingularData.previousCoboundary S q b = restriction S q c.val
    cases q with
    | zero =>
      have hc0 : c.val = 0 := hb.symm
      exact ⟨0, by simp [hc0, SmoothSingularData.previousCoboundary]⟩
    | succ q =>
      refine ⟨restriction S q b, ?_⟩
      have he := LinearMap.congr_fun (restriction_coboundary S q) b
      change SmoothSingularData.coboundary S q (restriction S q b) =
        restriction S (q+1) (ContinuousSingularData.coboundary M q b) at he
      exact he.trans (congrArg (restriction S (q+1)) hb)
  let F := (ContinuousSingularData.coboundaries M q).mapQ (SmoothSingularData.coboundaries S q) Z hb
  refine ⟨F, fun c => ⟨Z c, rfl, rfl⟩, ?_⟩
  intro G hG
  apply LinearMap.ext
  intro x
  obtain ⟨c,rfl⟩ := (ContinuousSingularData.coboundaries M q).mkQ_surjective x
  obtain ⟨d,hd,he⟩ := hG c
  have hdZ : d = Z c := Subtype.ext hd
  exact he.trans (congrArg (singularClass S q) hdZ)

theorem restrictionCohomology_spec (q : ℕ) :
    IsRestriction S q (restrictionCohomology S q) :=
  Classical.epsilon_spec (restrictionCohomology_exists S q).exists

/-- Naturality compares only smooth pushforwards on the smooth chain complex. -/
theorem inclusion_naturality {f : M → N} (hf : MapData.IsSmoothMap S T f) (q : ℕ) :
    (ContinuousSingularData.chainMap f q).comp (inclusion S q) =
      (inclusion T q).comp (SmoothSingularData.chainMap S T f q) := by
  apply Finsupp.lhom_ext
  intro σ r
  simp only [LinearMap.comp_apply, inclusion_single, map_smul,
    ContinuousSingular.chainMap_single, SmoothSingular.chainMap_single]
  rw [inclusion_generate T (SmoothSingular.smooth_postcompose hf σ.property)]
  simp only [one_smul]
  rfl

theorem restriction_naturality {f : M → N} (hf : MapData.IsSmoothMap S T f) (q : ℕ) :
    (SmoothSingularData.cochainMap S T f q).comp (restriction T q) =
      (restriction S q).comp (ContinuousSingularData.cochainMap f q) := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro z
  change c (inclusion T q (SmoothSingularData.chainMap S T f q z)) =
    c (ContinuousSingularData.chainMap f q (inclusion S q z))
  exact congrArg c (LinearMap.congr_fun (inclusion_naturality S T hf q) z).symm

/-- Actual naturality of r*, proved without any comparison isomorphism. -/
theorem restrictionCohomology_naturality {f : M → N} (hf : MapData.IsSmoothMap S T f)
    (Q : ∀ q, SmoothSingularData.Cohomology T q →ₗ[ℝ] SmoothSingularData.Cohomology S q)
    (hQ : IsSingularCohomologyPullback S T f Q) (q : ℕ)
    (x : ContinuousSingularData.Cohomology N q) :
    restrictionCohomology S q (ContinuousSingularData.cohomologyPullback f q x) =
      Q q (restrictionCohomology T q x) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf p).1)
  obtain ⟨c,rfl⟩ := (ContinuousSingularData.coboundaries N q).mkQ_surjective x
  obtain ⟨d,hd,hpd⟩ := ContinuousSingular.cohomologyPullback_spec hfc q c
  obtain ⟨e,he,hre⟩ := restrictionCohomology_spec T q c
  obtain ⟨v,hv,hrv⟩ := restrictionCohomology_spec S q d
  obtain ⟨w,hw,hQw⟩ := hQ q e
  have hvw : v = w := by
    apply Subtype.ext
    calc v.val = restriction S q d.val := hv
         _ = restriction S q (ContinuousSingularData.cochainMap f q c.val) := congrArg _ hd
         _ = SmoothSingularData.cochainMap S T f q (restriction T q c.val) :=
           (LinearMap.congr_fun (restriction_naturality S T hf q) c.val).symm
         _ = SmoothSingularData.cochainMap S T f q e.val := congrArg _ he.symm
         _ = w.val := hw.symm
  change restrictionCohomology S q
    (ContinuousSingularData.cohomologyPullback f q (ContinuousSingularData.classOf N q c)) =
      Q q (restrictionCohomology T q (ContinuousSingularData.classOf N q c))
  rw [hpd, hrv, hre, hQw, hvw]

theorem continuousComplex :
    Specs.SmoothManifolds.Comparison.StatementInterface.continuousComplexType.{u} := by
  intro M _
  exact ⟨ContinuousSingular.boundary_squared, rfl, ContinuousSingular.coboundary_squared,
    ContinuousSingular.coboundaries_are_cocycles, ContinuousSingular.zero_incoming⟩

theorem continuousPullback :
    Specs.SmoothManifolds.Comparison.StatementInterface.continuousPullbackType := by
  intro M N _ _ f hf q
  exact ⟨ContinuousSingular.chainMap_boundary hf q,
    ContinuousSingular.cohomologyPullback_exists hf q,
    ContinuousSingular.cohomologyPullback_spec hf q⟩

theorem restrictionConstruction :
    Specs.SmoothManifolds.Comparison.StatementInterface.restrictionConstructionType.{u} := by
  intro n a M _ S q
  exact ⟨restriction_coboundary S q, restrictionCohomology_exists S q, restrictionCohomology_spec S q⟩

theorem restrictionNaturality :
    Specs.SmoothManifolds.Comparison.StatementInterface.restrictionNaturalityType.{u} := by
  intro n m a b M N _ _ S T f hf Q hQ q x
  exact restrictionCohomology_naturality S T hf Q hQ q x

end SmoothManifolds.Comparison
