import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GreenBoundaryFlux
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.TorsionAndMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.Cartan
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Boundary

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Topology CompactlySupported BigOperators

namespace P202.Geometry.GreenBoundaryFlux
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.DifferentialData SmoothManifolds.BoundaryData
  SmoothManifolds.BoundaryRegularLevelData SmoothManifolds.OrientationData
  SmoothManifolds.LocalIntegrationData SmoothManifolds.GlobalIntegrationData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData P202.GreenData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Pointwise metric construction, valid on the actual tangent fiber. The
covector will be the last boundary-chart coordinate differential. -/
theorem unit_normal_of_covector (g : RiemannianMetric S) (p : M)
    (φ : Module.Dual ℝ (TangentSpace S p)) (hφ : φ ≠ 0) :
    ∃ ν : TangentSpace S p,
      pairing g p ν ν = 1 ∧ φ ν < 0 ∧
        ∀ z, φ z = 0 → pairing g p ν z = 0 := by
  let w := (musical g p).symm φ
  have hw : w ≠ 0 := by
    intro hw
    apply hφ
    have he := (musical g p).apply_symm_apply φ
    change musical g p w = φ at he
    rw [hw, map_zero] at he
    exact he.symm
  have hg : 0 < pairing g p w w := g.positive p w hw
  let r := tangentNorm g p w
  have hr : 0 < r := Real.sqrt_pos.mpr hg
  have hr2 : r ^ 2 = pairing g p w w := SmoothMetrics.tangentNorm_sq g p w
  have hφw : φ w = pairing g p w w := by
    change φ w = musical g p w w
    rw [show musical g p w = φ from (musical g p).apply_symm_apply φ]
  refine ⟨(-r⁻¹) • w, ?_, ?_, ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← hr2]
    field_simp
  · rw [map_smul, smul_eq_mul, hφw]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr hr)) hg
  · intro z hz
    have hwz : pairing g p w z = φ z := by
      change musical g p w z = φ z
      rw [(musical g p).apply_symm_apply φ]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hwz, hz, mul_zero]

/-- The outward sign distinguishes the two unit normals to a hyperplane. -/
theorem unit_normal_unique (g : RiemannianMetric S) (p : M)
    (φ : Module.Dual ℝ (TangentSpace S p)) (ν μ : TangentSpace S p)
    (hνunit : pairing g p ν ν = 1) (hμunit : pairing g p μ μ = 1)
    (hνnegative : φ ν < 0) (hμnegative : φ μ < 0)
    (hνorth : ∀ z, φ z = 0 → pairing g p ν z = 0)
    (hμorth : ∀ z, φ z = 0 → pairing g p μ z = 0) : ν = μ := by
  let t := φ μ / φ ν
  have hνne : φ ν ≠ 0 := ne_of_lt hνnegative
  have ht : 0 < t := div_pos_of_neg_of_neg hμnegative hνnegative
  let z := μ - t • ν
  have hzφ : φ z = 0 := by
    calc
      φ z = φ μ - φ (t • ν) := φ.map_sub μ (t • ν)
      _ = φ μ - t * φ ν := by rw [φ.map_smul]; rfl
      _ = 0 := by dsimp only [t]; field_simp; ring
  have hνz := hνorth z hzφ
  have hμz := hμorth z hzφ
  have hzz : pairing g p z z = 0 := by
    change pairing g p (μ - t • ν) z = 0
    have hsub := congrArg (fun ψ : Module.Dual ℝ (TangentSpace S p) => ψ z)
      ((pairing g p).map_sub μ (t • ν))
    calc
      pairing g p (μ - t • ν) z = pairing g p μ z - pairing g p (t • ν) z := hsub
      _ = 0 := by
        rw [show pairing g p (t • ν) z = t * pairing g p ν z from
          congrArg (fun ψ : Module.Dual ℝ (TangentSpace S p) => ψ z)
            ((pairing g p).map_smul t ν), hμz, hνz, mul_zero, sub_self]
  have hz : z = 0 := by
    by_contra hne
    have hh : 0 < pairing g p z z := g.positive p z hne
    exact (ne_of_gt hh) hzz
  have hμ : μ = t • ν := sub_eq_zero.mp hz
  have hunit := hμunit
  rw [hμ] at hunit
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hνunit, mul_one] at hunit
  have htone : t = 1 := by nlinarith
  rw [htone, one_smul] at hμ
  exact hμ.symm

/-- An empty boundary has an empty normal field; no unit vector is selected
in any ambient tangent space. -/
theorem boundary_geometry_of_empty (g : RiemannianMetric S)
    (hB : intrinsicBoundary S = ∅) : Nonempty (BoundaryGeometry g) := by
  letI : IsEmpty (intrinsicBoundary S) := ⟨fun p => by
    simpa only [hB, Set.mem_empty_iff_false] using p.property⟩
  obtain ⟨B, hnatural, gB, _, hinduced, _, _, _⟩ :=
    RiemannianVolume.boundaryDensity_exists S g
  exact ⟨{ manifold := B
           natural := hnatural
           metric := gB
           induced := hinduced
           normal := fun p => isEmptyElim p
           unit := fun p => isEmptyElim p
           orthogonal := fun p => isEmptyElim p
           outward := fun p => isEmptyElim p
           normal_smooth := fun p => isEmptyElim p }⟩


theorem boundary_geometry_zero_dimension {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold 0 a M} (g : RiemannianMetric S) :
    Nonempty (BoundaryGeometry g) :=
  boundary_geometry_of_empty g (SmoothManifolds.intrinsicBoundary_zero S)



/-- Normalize the negative metric dual of the last chart-coordinate covector.
Its kernel is exactly the range of the genuine inclusion differential. -/
theorem boundary_normal_pointwise :
    P202Specs.Geometry.GreenBoundaryFlux.boundary_normal_pointwiseType.{u} := by
  intro n a M _ S g B hB p
  cases a with
  | euclidean =>
    have hp := p.property
    change p.val ∈ SmoothManifolds.intrinsicBoundary S at hp
    rw [SmoothManifolds.intrinsicBoundary_euclidean S] at hp
    exact hp.elim
  | halfSpace =>
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    let E := SmoothManifolds.coordinateDerivationEquiv S p.val c hc hp
    have hE : IsChartCoordinates S p.val c E :=
      SmoothManifolds.coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
    let φ : Module.Dual ℝ (TangentSpace S p.val) :=
      (LinearMap.proj (Fin.last n)).comp E.toLinearMap
    have hφ : φ ≠ 0 := by
      intro hz
      have h := congrArg (fun L : Module.Dual ℝ (TangentSpace S p.val) =>
        L (E.symm (fun _ => 1))) hz
      change E (E.symm (fun _ => 1)) (Fin.last n) = 0 at h
      exact one_ne_zero (by simpa only [E.apply_symm_apply] using h)
    obtain ⟨ν, hunit, hneg, horth⟩ := unit_normal_of_covector g p.val φ hφ
    let L := SmoothManifolds.differential B S Subtype.val hB.1 p
    have hL : IsDifferential B S Subtype.val p L :=
      SmoothManifolds.differential_spec B S Subtype.val hB.1 p
    refine ⟨ν, hunit, ?_, ?_⟩
    · intro v
      apply horth
      exact ((SmoothManifolds.boundary_inclusion_image S B hB p c hc hp L hL E hE).2
        (L v)).mp ⟨v, rfl⟩
    · exact (SmoothManifolds.BoundaryOrientations.outward_iff_coordinate
        S p c hc hp E hE ν).mpr hneg

theorem boundary_normal_unique :
    P202Specs.Geometry.GreenBoundaryFlux.boundary_normal_uniqueType.{u} := by
  intro n a M _ S g B hB p ν μ hν hμ hνorth hμorth hνout hμout
  cases a with
  | euclidean =>
    have hp := p.property
    change p.val ∈ SmoothManifolds.intrinsicBoundary S at hp
    rw [SmoothManifolds.intrinsicBoundary_euclidean S] at hp
    exact hp.elim
  | halfSpace =>
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    let E := SmoothManifolds.coordinateDerivationEquiv S p.val c hc hp
    have hE := SmoothManifolds.coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
    let φ : Module.Dual ℝ (TangentSpace S p.val) :=
      (LinearMap.proj (Fin.last n)).comp E.toLinearMap
    let L := SmoothManifolds.differential B S Subtype.val hB.1 p
    have hL := SmoothManifolds.differential_spec B S Subtype.val hB.1 p
    have hker := (SmoothManifolds.boundary_inclusion_image S B hB p c hc hp L hL E hE).2
    apply unit_normal_unique g p.val φ ν μ hν hμ
    · exact (SmoothManifolds.BoundaryOrientations.outward_iff_coordinate
        S p c hc hp E hE ν).mp hνout
    · exact (SmoothManifolds.BoundaryOrientations.outward_iff_coordinate
        S p c hc hp E hE μ).mp hμout
    · intro z hz
      obtain ⟨v, rfl⟩ := (hker z).mpr hz
      exact hνorth v
    · intro z hz
      obtain ⟨v, rfl⟩ := (hker z).mpr hz
      exact hμorth v

/-- Local chart heights have globally smooth representatives near each point. -/
theorem boundary_height_representative {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (p : M)
    (c : ModelChart (n+1) .halfSpace M) (hc : c ∈ S.smoothStructure.val)
    (hp : p ∈ c.source) :
    ∃ (f : GlobalSmooth S) (U : Set M), IsOpen U ∧ p ∈ U ∧ U ⊆ c.source ∧
      ∀ q ∈ U, f.val q = (c q).val (Fin.last n) := by
  have hheight : SmoothManifolds.ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun q => (c q).val (Fin.last n)) p :=
    SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1 hc hp
      ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun z => z (Fin.last n),
        (contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) (Fin.last n)).contDiffOn,
        Filter.EventuallyEq.rfl⟩
  obtain ⟨f, hf, heq⟩ := SmoothManifolds.exists_global_representative S p _ hheight
  obtain ⟨U, hUeq, hUopen, hpU⟩ := eventually_nhds_iff.mp heq
  exact ⟨⟨f, (SmoothManifolds.mem_globalSmoothAlgebra_iff S f).mpr hf⟩,
    U ∩ c.source, hUopen.inter c.open_source, ⟨hpU, hp⟩, Set.inter_subset_right,
    fun q hq => hUeq q hq.1⟩

/-- A local height gradient is exactly the inverse-metric boundary conormal. -/
theorem gradient_height_pairing {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (g : RiemannianMetric S)
    (f : GlobalSmooth S) (c : ModelChart (n+1) .halfSpace M)
    (hc : c ∈ S.smoothStructure.val) (q : M) (hq : q ∈ c.source)
    (heq : f.val =ᶠ[𝓝 q] (fun x => (c x).val (Fin.last n)))
    (v : TangentSpace S q) :
    pairing g q ((gradient g f).val q) v =
      SmoothManifolds.coordinateDerivationEquiv S q c hc hq v (Fin.last n) := by
  let hf := (SmoothManifolds.mem_globalSmoothAlgebra_iff S f.val).mp f.property
  change musical g q ((musical g q).symm
    (SmoothManifolds.CovectorData.dFunction S f.val hf q)) v = _
  rw [LinearEquiv.apply_symm_apply]
  have hG : SmoothManifolds.CovectorData.functionGerm S f.val hf q =
      SmoothManifolds.coordinateGerm S q c hc hq (Fin.last n) :=
    Subtype.ext (Filter.Germ.coe_eq.mpr heq)
  change v.val (SmoothManifolds.CovectorData.functionGerm S f.val hf q) = _
  rw [hG]
  rfl

/-- Each boundary point has a global smooth ambient field which is the unit
outward normal at all boundary points in a neighborhood. -/
theorem local_unit_normal {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) .halfSpace M) (g : RiemannianMetric S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (p : intrinsicBoundary S) :
    ∃ (U : Set M), IsOpen U ∧ p.val ∈ U ∧ ∃ X : Field S,
      ∀ q : intrinsicBoundary S, q.val ∈ U →
        pairing g q.val (X.val q.val) (X.val q.val) = 1 ∧
        (∀ v, pairing g q.val (X.val q.val)
          (SmoothManifolds.differential B S Subtype.val hB.1 q v) = 0) ∧
        Outward S q (X.val q.val) := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  obtain ⟨f, U, hU, hpU, hUc, hfU⟩ := boundary_height_representative S p.val c hc hp
  let w : Field S := gradient g f
  let A : M → ℝ := fun q => pairing g q (w.val q) (w.val q)
  have hpair (q : M) (hq : q ∈ U) (v : TangentSpace S q) :
      pairing g q (w.val q) v =
        SmoothManifolds.coordinateDerivationEquiv S q c hc (hUc hq) v (Fin.last n) :=
    gradient_height_pairing S g f c hc q (hUc hq)
      (Filter.eventually_of_mem (hU.mem_nhds hq) (fun z hz => hfU z hz)) v
  have hpos (q : M) (hq : q ∈ U) : 0 < A q := by
    apply g.positive q (w.val q)
    intro hz
    let E := SmoothManifolds.coordinateDerivationEquiv S q c hc (hUc hq)
    have he := hpair q hq (E.symm (fun _ => 1))
    rw [hz, map_zero, LinearMap.zero_apply] at he
    change (0 : ℝ) = E (E.symm (fun _ => 1)) (Fin.last n) at he
    have he' : (0 : ℝ) = 1 := by simpa only [E.apply_symm_apply] using he
    exact zero_ne_one he'
  have hA : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val A p.val :=
    TorsionAndMetric.metricPairing_smooth (tangentBundle S) g w w p.val
  have hnorm : ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => -(Real.sqrt r)⁻¹) (Set.Ioi 0) := by
    intro r hr
    exact ((Real.contDiffAt_sqrt (ne_of_gt hr)).inv
      (ne_of_gt (Real.sqrt_pos.mpr hr))).neg.contDiffWithinAt
  have hN := hA.postcompOn isOpen_Ioi (hpos p.val hpU) hnorm
  obtain ⟨h, hh, heq⟩ := SmoothManifolds.exists_global_representative S p.val _
    ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hN)
  let hglobal : GlobalSmooth S := ⟨h, (SmoothManifolds.mem_globalSmoothAlgebra_iff S h).mpr hh⟩
  obtain ⟨V, hVeq, hV, hpV⟩ := eventually_nhds_iff.mp heq
  let X : Field S := mulSection hglobal w
  refine ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, X, ?_⟩
  intro q hq
  let E := SmoothManifolds.coordinateDerivationEquiv S q.val c hc (hUc hq.1)
  have hE := SmoothManifolds.coordinateDerivationEquiv_isChartCoordinates
    S q.val c hc (hUc hq.1)
  let r := Real.sqrt (A q.val)
  have hr : 0 < r := Real.sqrt_pos.mpr (hpos q.val hq.1)
  have hr2 : r ^ 2 = A q.val := Real.sq_sqrt (hpos q.val hq.1).le
  have hX : X.val q.val = (-r⁻¹) • w.val q.val := by
    change h q.val • w.val q.val = _
    rw [hVeq q.val hq.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    change -r⁻¹ * (-r⁻¹ * A q.val) = 1
    rw [← hr2]
    field_simp
  · intro v
    rw [hX]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hpair q.val hq.1]
    have hzero := ((SmoothManifolds.boundary_inclusion_image S B hB q c hc
      (hUc hq.1) (SmoothManifolds.differential B S Subtype.val hB.1 q)
      (SmoothManifolds.differential_spec B S Subtype.val hB.1 q) E hE).2
      (SmoothManifolds.differential B S Subtype.val hB.1 q v)).mp ⟨v, rfl⟩
    rw [hzero, mul_zero]
  · apply (SmoothManifolds.BoundaryOrientations.outward_iff_coordinate
      S q c hc (hUc hq.1) E hE _).mpr
    rw [hX, map_smul]
    change -r⁻¹ * E (w.val q.val) (Fin.last n) < 0
    rw [← hpair q.val hq.1]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr hr)) (hpos q.val hq.1)

/-- The locally constructed normals agree by geometric uniqueness. -/
theorem boundary_geometry_exists :
    P202Specs.Geometry.GreenBoundaryFlux.boundary_geometry_existsType.{u} := by
  intro n a M _ S g
  cases n with
  | zero => exact boundary_geometry_zero_dimension g
  | succ n =>
    cases a with
    | euclidean =>
      exact boundary_geometry_of_empty g (SmoothManifolds.intrinsicBoundary_euclidean S)
    | halfSpace =>
      obtain ⟨B, hB, gB, _, hinduced, _, _, _⟩ :=
        RiemannianVolume.boundaryDensity_exists S g
      have hnormal := boundary_normal_pointwise g B hB
      choose ν hunit horth hout using hnormal
      refine ⟨{ manifold := B
                natural := hB
                metric := gB
                induced := hinduced
                normal := ν
                unit := hunit
                orthogonal := horth
                outward := hout
                normal_smooth := ?_ }⟩
      intro p
      obtain ⟨U, hU, hpU, X, hX⟩ := local_unit_normal S g B hB p
      refine ⟨U, hU, hpU, X, ?_⟩
      intro q hq
      obtain ⟨hXunit, hXorth, hXout⟩ := hX q hq
      exact boundary_normal_unique g B hB q (X.val q.val) (ν q)
        hXunit (hunit q) hXorth (horth q) hXout (hout q)

open SmoothManifolds.FormPullbackData SmoothManifolds.MetricVolumeData

open SmoothManifolds.BoundaryOrientationData

/-- First-slot insertion on decomposable determinant vectors. -/
theorem normalWedge_tuple {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {n : ℕ} (L : W →ₗ[ℝ] V)
    (ν : V) (v : Fin n → W) :
    normalWedge L ν (exteriorPower.ιMulti ℝ n v) =
      exteriorPower.ιMulti ℝ (n+1) (Fin.cons ν (fun i => L (v i))) := by
  apply Subtype.ext
  simp [SmoothManifolds.BoundaryOrientations.coe_normalWedge,
    ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, Function.comp_def]

/-- Appending a unit vector orthogonal to all tangential vectors preserves
Gram determinants. The boundary metric is the actual pullback metric. -/
theorem normalWedge_norm_tuple {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g) (p : intrinsicBoundary S)
    (v : Fin n → TangentSpace b.manifold p) :
    determinantNorm (P202.VolumeData.libraryMetric g) p.val
      (normalWedge (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p)
        (b.normal p) (exteriorPower.ιMulti ℝ n v)) =
    determinantNorm (P202.VolumeData.libraryMetric b.metric) p
      (exteriorPower.ιMulti ℝ n v) := by
  let L := SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p
  let w : Fin (n+1) → TangentSpace S p.val := Fin.cons (b.normal p) (fun i => L (v i))
  rw [normalWedge_tuple]
  unfold determinantNorm determinantMetric
  change Real.sqrt ((pairing g p.val).exteriorPower (n+1)
      (exteriorPower.ιMulti ℝ (n+1) w) (exteriorPower.ιMulti ℝ (n+1) w)) =
    Real.sqrt ((pairing b.metric p).exteriorPower n
      (exteriorPower.ιMulti ℝ n v) (exteriorPower.ιMulti ℝ n v))
  simp only [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  congr 1
  change (Matrix.of (fun i j : Fin (n+1) => pairing g p.val
    (Fin.cons (α := fun _ => TangentSpace S p.val) (b.normal p) (fun k => L (v k)) j)
    (Fin.cons (α := fun _ => TangentSpace S p.val) (b.normal p) (fun k => L (v k)) i))).det =
      (Matrix.of (fun i j : Fin n => pairing b.metric p (v j) (v i))).det
  have hzero (i : Fin n) : pairing g p.val (b.normal p) (L (v i)) = 0 :=
    b.orthogonal p (v i)
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Matrix.of_apply, Fin.cons_zero,
    b.unit p, one_mul, Fin.succAbove_zero, Fin.cons_succ, hzero, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  ext i j
  exact (b.induced p (v j) (v i)).symm

/-- Normal insertion is an isometry of the determinant norms. -/
theorem normalWedge_norm {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g) (p : intrinsicBoundary S)
    (η : DeterminantLine b.manifold p) :
    determinantNorm (P202.VolumeData.libraryMetric g) p.val
      (normalWedge (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p)
        (b.normal p) η) =
    determinantNorm (P202.VolumeData.libraryMetric b.metric) p η := by
  let K := (P202.VolumeData.cotangentBundle b.manifold).tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := b.manifold.smoothStructure.property.1.1 p
  rw [SmoothManifolds.MetricVolumeResults.coordinate_expansion K c hc ⟨p, hp⟩ η,
    SmoothManifolds.BoundaryOrientations.normalWedge_smul_right,
    SmoothManifolds.MetricVolumeResults.determinantNorm_smul,
    SmoothManifolds.MetricVolumeResults.determinantNorm_smul]
  congr 1
  exact normalWedge_norm_tuple g b p
    (fun i => (K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) i))

/-- Every vector splits into its normal component and a tangential vector. -/
theorem boundary_normal_decomposition {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g) (p : intrinsicBoundary S)
    (x : TangentSpace S p.val) :
    ∃ z : TangentSpace b.manifold p,
      x = pairing g p.val x (b.normal p) • b.normal p +
        SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p z := by
  cases a with
  | euclidean =>
    have hp := p.property
    change p.val ∈ SmoothManifolds.intrinsicBoundary S at hp
    rw [SmoothManifolds.intrinsicBoundary_euclidean S] at hp
    exact hp.elim
  | halfSpace =>
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    let E := SmoothManifolds.coordinateDerivationEquiv S p.val c hc hp
    have hE := SmoothManifolds.coordinateDerivationEquiv_isChartCoordinates S p.val c hc hp
    let L := SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p
    have hL := SmoothManifolds.differential_spec b.manifold S Subtype.val b.natural.1 p
    have hneg : E (b.normal p) (Fin.last n) < 0 :=
      (SmoothManifolds.BoundaryOrientations.outward_iff_coordinate S p c hc hp E hE _).mp
        (b.outward p)
    let t := E x (Fin.last n) / E (b.normal p) (Fin.last n)
    let φ : Module.Dual ℝ (TangentSpace S p.val) :=
      (LinearMap.proj (Fin.last n)).comp E.toLinearMap
    have hz : φ (x + (-t) • b.normal p) = 0 := by
      calc
        φ (x + (-t) • b.normal p) = φ x + φ ((-t) • b.normal p) := φ.map_add _ _
        _ = φ x + (-t) * φ (b.normal p) := by rw [φ.map_smul]; rfl
        _ = 0 := by
          change E x (Fin.last n) + (-t) * E (b.normal p) (Fin.last n) = 0
          rw [neg_mul, ← sub_eq_add_neg]
          dsimp only [t]
          rw [div_mul_cancel₀ _ (ne_of_lt hneg), sub_self]
    obtain ⟨z, hzeq⟩ := ((SmoothManifolds.boundary_inclusion_image S b.manifold b.natural
      p c hc hp L hL E hE).2 _).mpr hz
    have hx : x = t • b.normal p + L z := by
      rw [hzeq, add_left_comm, ← add_smul, add_neg_cancel, zero_smul, add_zero]
    have ht : pairing g p.val x (b.normal p) = t := by
      have hsym : pairing g p.val x (b.normal p) = pairing g p.val (b.normal p) x :=
        g.symmetric p.val x (b.normal p)
      rw [hsym, hx]
      have horth : pairing g p.val (b.normal p) (L z) = 0 := b.orthogonal p z
      simp only [map_add, map_smul, smul_eq_mul, b.unit p, horth, mul_one, add_zero]
    exact ⟨z, ht.symm ▸ hx⟩


/-- The metric volume coefficient retains the orientation sign. -/
theorem volume_topCoefficient (g : RiemannianMetric S) (o : Orientation S)
    (s : SignedCharts S) (hs : RepresentsSignedCharts o.val s)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) :
    topCoefficient K c hc p.val p.property (P202.VolumeData.volumeForm g o).field =
      signValue (s.sign c hc p) *
        densityCoefficient K c hc p (P202.VolumeData.density g p.val) := by
  rw [(RiemannianVolume.density_coordinates g K c hc p).1]
  have hω := RiemannianVolume.volumeForm_coordinates g o s hs K c hc p
  have hp : SmoothManifolds.OrientationData.pairing p.val
      ((P202.VolumeData.volumeForm g o).field p.val)
      (SmoothManifolds.OrientationData.coordinateVector K c hc p) =
      signValue (s.sign c hc p) * Real.sqrt (P202.VolumeData.gramMatrix g K c hc p).det := by
    rw [hω]
    simp only [SmoothManifolds.OrientationData.pairing, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [show exteriorPower.pairingDual ℝ (TangentSpace S p.val) n
      (coordinateTopForm K c hc p) (SmoothManifolds.OrientationData.coordinateVector K c hc p) = 1
      from SmoothManifolds.MetricVolumeResults.coordinateTopForm_pairing K c hc p]
    exact mul_one _
  unfold topCoefficient
  rw [SmoothManifolds.FormPullbackResults.evaluate_eq_pairing]
  unfold SmoothManifolds.CovectorData.coordinateVector
  simpa only [SmoothManifolds.OrientationData.pairing,
    SmoothManifolds.OrientationData.coordinateVector, Pi.basisFun_apply] using hp

/-- The actual smooth metric volume field is continuous in the top-form atlas. -/
theorem volume_topForm_continuous (g : RiemannianMetric S) (o : Orientation S) :
    IsContinuousTopForm (P202.VolumeData.volumeForm g o).field := by
  obtain ⟨s, hs, _⟩ := SmoothManifolds.LocalIntegrationResults.orientation_signs S o
  intro K c hc
  have h := ((s.locallyConstant c hc).comp signValue).continuous.mul
    ((RiemannianVolume.density_properties g).2.2.1 K c hc)
  exact h.congr (fun p => (volume_topCoefficient g o s hs K c hc p).symm)

/-- Multiplication by a compact continuous scalar needs no compactness or
orientation assumptions on the underlying manifold beyond the displayed o. -/
def compactMetricForm (g : RiemannianMetric S) (o : Orientation S) (f : C_c(M, ℝ)) :
    CompactTopForm S where
  field := fun p => f p • (P202.VolumeData.volumeForm g o).field p
  continuous := by
    intro K c hc
    exact ((f.continuous.comp continuous_subtype_val).mul
      (volume_topForm_continuous g o K c hc)).congr
        (fun p => (SmoothManifolds.GlobalIntegrationResults.topCoefficient_weight
          K c hc p.val p.property (fun q => f q) _).symm)
  compact_support := f.hasCompactSupport.of_isClosed_subset isClosed_closure
    (fun p hp => (SmoothManifolds.GlobalIntegrationResults.weight_support S n
      (P202.VolumeData.volumeForm g o).field (fun q => f q) hp).1)

/-- The sign from the integral cancels the sign of the metric volume form.
No absolute value is taken on the scalar f. -/
theorem metric_signed_coefficient (g : RiemannianMetric S) (o : Orientation S)
    (s : SignedCharts S) (hs : RepresentsSignedCharts o.val s)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (f : M → ℝ) :
    signedCoordinateCoefficient s K c hc
      (fun p => f p • (P202.VolumeData.volumeForm g o).field p) =
    SmoothManifolds.DensityIntegrationData.coordinateDensity K c hc
      (fun p => f p • P202.VolumeData.density g p) := by
  funext x
  by_cases hx : x ∈ modelSet n a
  · by_cases hy : (⟨x, hx⟩ : ModelSpace n a) ∈ c.target
    · let p : c.source := ⟨c.symm ⟨x, hx⟩, c.map_target hy⟩
      have htop := SmoothManifolds.GlobalIntegrationResults.topCoefficient_weight
        K c hc p.val p.property f (P202.VolumeData.volumeForm g o).field
      have hvol := volume_topCoefficient g o s hs K c hc p
      have hden := map_smul (densityCoefficient K c hc p) (f p.val)
        (P202.VolumeData.density g p.val)
      simp only [signedCoordinateCoefficient, extendModel, modelSignedCoefficient,
        SmoothManifolds.DensityIntegrationData.coordinateDensity, hx, hy, dite_true]
      change signValue (s.sign c hc p) *
        topCoefficient K c hc p.val p.property
          (fun q => f q • (P202.VolumeData.volumeForm g o).field q) =
        densityCoefficient K c hc p (f p.val • P202.VolumeData.density g p.val)
      rw [htop, hvol, hden]
      change signValue (s.sign c hc p) *
        (f p.val * (signValue (s.sign c hc p) * _)) = f p.val * _
      have halg (e : Bool) (r t : ℝ) : signValue e * (r * (signValue e * t)) = r * t := by
        cases e <;> simp only [signValue, Bool.false_eq_true, ↓reduceIte,
          neg_mul, mul_neg, neg_neg, one_mul]
      exact halg _ _ _
    · simp only [signedCoordinateCoefficient, extendModel, modelSignedCoefficient,
        SmoothManifolds.DensityIntegrationData.coordinateDensity, hx, hy, dite_true, dite_false]
  · simp only [signedCoordinateCoefficient, extendModel,
      SmoothManifolds.DensityIntegrationData.coordinateDensity, hx, dite_false]

/-- The bridge for every compact top-form representative, hence independent of
which proofs of continuity and compactness were used to bundle it. -/
theorem metric_integral_eq (g : RiemannianMetric S) (o : Orientation S)
    (f : C_c(M, ℝ)) (η : CompactTopForm S)
    (hη : η.field = fun p => f p • (P202.VolumeData.volumeForm g o).field p)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) :
    I η = P202.VolumeData.integral g f := by
  obtain ⟨s, hs, _⟩ := SmoothManifolds.LocalIntegrationResults.orientation_signs S o
  obtain ⟨K⟩ := SmoothManifolds.TangentBundle.fiberCoordinates_exists S
  let U : {c : ModelChart n a M // c ∈ S.smoothStructure.val} → Set M :=
    fun c => c.val.source
  obtain ⟨ρ, hρcont, hρlf, hρsub, hρsum⟩ :=
    SmoothManifolds.GlobalIntegrationResults.continuous_partition S U
      (fun c => c.val.open_source) (by
        intro p
        obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
        exact ⟨⟨c, hc⟩, hp⟩)
  have hloc : IsLocalization (fun c => c.val) ρ η :=
    ⟨hρcont, hρlf, hρsub, Set.univ, isOpen_univ, Set.subset_univ _, fun p _ => hρsum p⟩
  rw [SmoothManifolds.GlobalIntegrationResults.localization S o I hI s hs K
    (fun c => c.val) (fun c => c.property) ρ η hloc]
  obtain ⟨σ, t, hσ, _, _, _, _, hD⟩ :=
    SmoothManifolds.DensityIntegralResults.locally_finite_localization S
      (P202.VolumeData.densityIntegral S)
      (RiemannianVolume.densityIntegral_properties S).1
      (P202.VolumeData.compactMetricDensity g f) ρ K
      (fun c => c.val) (fun c => c.property) hρcont hρlf hρsub
      ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun p _ => hρsum p⟩
  change _ = P202.VolumeData.densityIntegral S (P202.VolumeData.compactMetricDensity g f)
  rw [hD]
  apply finsum_congr
  intro c
  unfold SmoothManifolds.LocalIntegrationData.coordinateIntegral
    SmoothManifolds.DensityIntegrationData.coordinateIntegral
  congr 1
  rw [hη, hσ c]
  change signedCoordinateCoefficient s K c.val c.property
    (fun p => ρ c p • (f p • (P202.VolumeData.volumeForm g o).field p)) =
    SmoothManifolds.DensityIntegrationData.coordinateDensity K c.val c.property
      (fun p => ρ c p • (f p • P202.VolumeData.density g p))
  simp_rw [smul_smul]
  exact metric_signed_coefficient g o s hs K c.val c.property (fun p => ρ c p * f p)

theorem metric_integral_bridge :
    P202Specs.Geometry.GreenBoundaryFlux.metric_integral_bridgeType.{u} := by
  intro n a M _ S g o f
  exact ⟨compactMetricForm g o f, rfl,
    fun I hI => metric_integral_eq g o f (compactMetricForm g o f) rfl I hI⟩

/-- The normal-first metric volume restricts to the metric boundary volume. -/
theorem normal_volume_pairing {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g) (o : Orientation S)
    (q : Orientation b.manifold) (hq : IsInducedOrientation o q)
    (p : intrinsicBoundary S) (η : DeterminantLine b.manifold p) :
    SmoothManifolds.OrientationData.pairing p.val ((P202.VolumeData.volumeForm g o).field p.val)
      (normalWedge (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p)
        (b.normal p) η) =
    SmoothManifolds.OrientationData.pairing p ((P202.VolumeData.volumeForm b.metric q).field p) η := by
  let L := SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p
  let K := (P202.VolumeData.cotangentBundle b.manifold).tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := b.manifold.smoothStructure.property.1.1 p
  obtain ⟨s, hs, _⟩ := SmoothManifolds.LocalIntegrationResults.orientation_signs b.manifold q
  let ζ := SmoothManifolds.OrientationData.coordinateVector K c hc ⟨p, hp⟩
  let ε := signValue (s.sign c hc ⟨p, hp⟩)
  have hζ : IsPositive (q.val p) (ε • ζ) := hs K c hc ⟨p, hp⟩
  have hout : IsPositive (o.val p.val) (normalWedge L (b.normal p) (ε • ζ)) :=
    (hq p L (SmoothManifolds.differential_spec b.manifold S Subtype.val b.natural.1 p)
      (b.normal p) (b.outward p) (ε • ζ)).mp hζ
  have hamb := SmoothManifolds.MetricVolumeResults.metricVolume_evaluate_positive
    (P202.VolumeData.libraryMetric g) o (P202.VolumeData.volumeForm g o)
    (RiemannianVolume.volumeForm_normalization g o) p.val _ hout
  have hbdy := SmoothManifolds.MetricVolumeResults.metricVolume_evaluate_positive
    (P202.VolumeData.libraryMetric b.metric) q (P202.VolumeData.volumeForm b.metric q)
    (RiemannianVolume.volumeForm_normalization b.metric q) p _ hζ
  have he : SmoothManifolds.OrientationData.pairing p.val
      ((P202.VolumeData.volumeForm g o).field p.val)
      (normalWedge L (b.normal p) (ε • ζ)) =
      SmoothManifolds.OrientationData.pairing p
        ((P202.VolumeData.volumeForm b.metric q).field p) (ε • ζ) :=
    hamb.trans ((normalWedge_norm g b p (ε • ζ)).trans hbdy.symm)
  have hbase : SmoothManifolds.OrientationData.pairing p.val
      ((P202.VolumeData.volumeForm g o).field p.val) (normalWedge L (b.normal p) ζ) =
      SmoothManifolds.OrientationData.pairing p
        ((P202.VolumeData.volumeForm b.metric q).field p) ζ := by
    apply mul_left_cancel₀ (SmoothManifolds.OrientationResults.signValue_ne_zero
      (s.sign c hc ⟨p, hp⟩))
    simpa only [SmoothManifolds.BoundaryOrientations.normalWedge_smul_right,
      SmoothManifolds.OrientationData.pairing, map_smul, smul_eq_mul] using he
  rw [SmoothManifolds.MetricVolumeResults.coordinate_expansion K c hc ⟨p, hp⟩ η,
    SmoothManifolds.BoundaryOrientations.normalWedge_smul_right]
  simpa only [SmoothManifolds.OrientationData.pairing, map_smul, smul_eq_mul] using
    congrArg (fun r : ℝ => determinantCoefficient K c hc ⟨p, hp⟩ η * r) hbase

/-- The pullback of Cartan contraction is evaluation after normal-first wedge. -/
theorem contraction_pullback_evaluate {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold (n+1) a M}
    (g : RiemannianMetric S) (b : BoundaryGeometry g) (o : Orientation S)
    (X : Field S) (p : intrinsicBoundary S) (v : Fin n → TangentSpace b.manifold p) :
    SmoothManifolds.ExteriorData.evaluate (TangentSpace b.manifold p) n
      (SmoothManifolds.FormPullbackData.pullbackField b.manifold S Subtype.val
        (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1)
        (SmoothManifolds.CartanData.contraction (P202.VolumeData.cotangentBundle S)
          X.val (n+1) (P202.VolumeData.volumeForm g o).field) p) v =
      SmoothManifolds.OrientationData.pairing p.val
        ((P202.VolumeData.volumeForm g o).field p.val)
        (normalWedge (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p)
          (X.val p.val) (exteriorPower.ιMulti ℝ n v)) := by
  rw [SmoothManifolds.FormPullbackResults.pullback_apply,
    SmoothManifolds.CartanResults.contraction_apply,
    SmoothManifolds.FormPullbackResults.evaluate_eq_pairing, normalWedge_tuple]
  rfl

set_option maxHeartbeats 8000000 in
theorem boundary_flux : P202Specs.Geometry.GreenBoundaryFlux.boundary_fluxType.{u} := by
  intro n a M _ S g b o
  obtain ⟨q, ⟨hq, _⟩, _⟩ :=
    (SmoothManifolds.BoundaryOrientations.boundary_orientation S o).2 b.manifold b.natural
  refine ⟨q, hq, ?_⟩
  intro X
  funext p
  let L := SmoothManifolds.differential b.manifold S Subtype.val b.natural.1 p
  letI := (SmoothManifolds.tangent_dimension b.manifold p).1
  obtain ⟨z, hz⟩ := boundary_normal_decomposition g b p (X.val p.val)
  apply (SmoothManifolds.CartanData.evaluationEquiv
    (P202.VolumeData.cotangentBundle b.manifold).tangent.fiberCoordinates p n).injective
  rw [SmoothManifolds.CartanResults.evaluationEquiv_apply,
    SmoothManifolds.CartanResults.evaluationEquiv_apply]
  apply AlternatingMap.ext
  intro v
  rw [contraction_pullback_evaluate]
  rw [hz, SmoothManifolds.BoundaryOrientations.normalWedge_add,
    SmoothManifolds.BoundaryOrientations.normalWedge_smul,
    SmoothManifolds.BoundaryOrientations.normalWedge_tangent
      (SmoothManifolds.tangent_dimension b.manifold p).2,
    add_zero]
  change SmoothManifolds.OrientationData.pairing p.val
      ((P202.VolumeData.volumeForm g o).field p.val)
      (pairing g p.val (X.val p.val) (b.normal p) •
        normalWedge L (b.normal p) (exteriorPower.ιMulti ℝ n v)) = _
  rw [show SmoothManifolds.OrientationData.pairing p.val
      ((P202.VolumeData.volumeForm g o).field p.val)
      (pairing g p.val (X.val p.val) (b.normal p) •
        normalWedge L (b.normal p) (exteriorPower.ιMulti ℝ n v)) =
      pairing g p.val (X.val p.val) (b.normal p) *
      SmoothManifolds.OrientationData.pairing p.val
        ((P202.VolumeData.volumeForm g o).field p.val)
        (normalWedge L (b.normal p) (exteriorPower.ιMulti ℝ n v)) from
        map_smul (exteriorPower.pairingDual ℝ (TangentSpace S p.val) (n+1)
          ((P202.VolumeData.volumeForm g o).field p.val)) _ _]
  rw [normal_volume_pairing g b o q hq p]
  rw [SmoothManifolds.FormPullbackResults.evaluate_eq_pairing]
  simp only [SmoothManifolds.OrientationData.pairing, map_smul, LinearMap.smul_apply,
    smul_eq_mul, flux]
  rfl

end P202.Geometry.GreenBoundaryFlux
