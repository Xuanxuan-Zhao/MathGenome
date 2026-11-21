import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetBoundaryGluing
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RegionalBoundaryDensities
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RegionalBoundaryRefinement

/-! Boundary gluing for paper.tex 5107–5117. The actual geometric density
comparison and common refinement are proved in the upstream child modules.
Here unsigned substitution, finite interval subdivision, and the exact mate
involution assemble them into the unconditional equality of literal integrals.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.PlanarRegionTopology P202Specs.SurfaceRegionsEuler
open P202Specs.RegionalBoundaryRefinement P202Specs.RegionalBoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryGluing
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The empty case of the full gluing equality uses the original arbitrary
decomposition and boundary presentation. -/
theorem regional_boundary_gluing_of_isEmpty [IsEmpty M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (D : RegionDecomposition S)
    (G : ∀ j : Fin D.regionCount, RegionalChartGeometry g D j)
    (A : ∀ (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount),
      P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (s : ∀ j : Fin D.regionCount, Fin (D.region j).boundaryCount → ℝ)
    (B : BoundaryPresentation g) :
    (∑ j : Fin D.regionCount, P202Specs.LocalGaussBonnet.geodesicIntegral
      (G j).metric (G j).connection (G j).orientation
      (G j).ambientChart (G j).ambientChart_mem (D.region j) (A j) (s j)) =
      B.curvatureIntegral C := by
  have hz := (D.empty_case inferInstance).2.2
  haveI : IsEmpty (Fin D.regionCount) := by rw [hz]; infer_instance
  rw [Finset.sum_of_isEmpty]
  exact (boundaryCurvatureIntegral_eq_zero g B C (Subsingleton.elim _ _)).symm

/-- A closed change of parameter with nonzero derivative of one sign transports
an unsigned density to the increasing target interval. Endpoints need only
continuity, not differentiability. -/
theorem integral_abs_deriv_of_closed_image (f φ : ℝ → ℝ)
    {l r a b : ℝ} (hlr : l < r) (hab : a < b)
    (hc : ContinuousOn φ (Icc l r))
    (hd : ∀ t ∈ Ioo l r, HasDerivAt φ (deriv φ t) t)
    (hs : (∀ t ∈ Ioo l r, 0 < deriv φ t) ∨
      (∀ t ∈ Ioo l r, deriv φ t < 0))
    (hi : φ '' Icc l r = Icc a b) :
    (∫ t in l..r, f (φ t) * |deriv φ t|) = ∫ t in a..b, f t := by
  have hcu : ContinuousOn φ (uIcc l r) := by
    simpa only [uIcc_of_le hlr.le] using hc
  have hdu : ∀ t ∈ Ioo (min l r) (max l r), HasDerivAt φ (deriv φ t) t := by
    simpa only [min_eq_left hlr.le, max_eq_right hlr.le] using hd
  rcases hs with hpos | hneg
  · have hm : StrictMonoOn φ (Icc l r) := strictMonoOn_of_deriv_pos (convex_Icc l r) hc (by
      simpa only [interior_Icc] using hpos)
    have he := (Icc_eq_Icc_iff hab.le).mp
      (hi.symm.trans (hc.image_Icc_of_monotoneOn hlr.le hm.monotoneOn))
    have hz := intervalIntegral_density_reparam_nonneg f φ (deriv φ) l r hcu hdu (by
      simpa only [min_eq_left hlr.le, max_eq_right hlr.le] using
        fun t ht => (hpos t ht).le)
    simpa only [← he.1, ← he.2] using hz
  · have hm : StrictAntiOn φ (Icc l r) := strictAntiOn_of_deriv_neg (convex_Icc l r) hc (by
      simpa only [interior_Icc] using hneg)
    have he := (Icc_eq_Icc_iff hab.le).mp
      (hi.symm.trans (hc.image_Icc_of_antitoneOn hlr.le hm.antitoneOn))
    have hz := intervalIntegral_density_reparam_nonpos f φ (deriv φ) l r hcu hdu (by
      simpa only [min_eq_left hlr.le, max_eq_right hlr.le] using
        fun t ht => (hneg t ht).le)
    simpa only [← he.1, ← he.2] using hz

/-- Densities cancelling almost everywhere along one matched geometric piece
have opposite literal interval integrals. -/
theorem integral_pair_cancel_of_ae (f g φ : ℝ → ℝ)
    {l r a b : ℝ} (hlr : l < r) (hab : a < b)
    (hc : ContinuousOn φ (Icc l r))
    (hd : ∀ t ∈ Ioo l r, HasDerivAt φ (deriv φ t) t)
    (hs : (∀ t ∈ Ioo l r, 0 < deriv φ t) ∨
      (∀ t ∈ Ioo l r, deriv φ t < 0))
    (hi : φ '' Icc l r = Icc a b)
    (he : ∀ᵐ t ∂volume, t ∈ Ioo l r →
      f t + g (φ t) * |deriv φ t| = 0) :
    (∫ t in l..r, f t) + (∫ t in a..b, g t) = 0 := by
  have heq : (∫ t in l..r, f t) =
      -(∫ t in l..r, g (φ t) * |deriv φ t|) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [he, volume.ae_ne r] with t ht htr hmem
    have htIoc : t ∈ Ioc l r := by
      simpa only [uIoc_of_le hlr.le] using hmem
    have hz := ht ⟨htIoc.1, lt_of_le_of_ne htIoc.2 htr⟩
    linarith
  rw [integral_abs_deriv_of_closed_image g φ hlr hab hc hd hs hi] at heq
  linarith

/-- One original occurrence is exactly the disjoint finite sum of its subdivision intervals. -/
theorem subdivision_integral_eq_sum_fiber {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    {R : RegionalRepresentatives g D A} {B : BoundaryPresentation g}
    (F : FiniteSubdivision R B) (o : Occurrence A B) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (occurrenceArc R B o).left
      (occurrenceArc R B o).right) :
    (∫ t in (occurrenceArc R B o).left..(occurrenceArc R B o).right, f t) =
      ∑ h : {h : Fin F.count // F.occurrence h = o},
        ∫ t in F.left h.val..F.right h.val, f t := by
  let K := {h : Fin F.count // F.occurrence h = o}
  apply intervalIntegral_eq_sum_of_finite_cover f (occurrenceArc R B o).ordered.le
    (fun h : K => F.left h.val) (fun h : K => F.right h.val)
    (fun h => (F.ordered h.val).le) ?_ ?_ (F.cuts o : Set ℝ)
    (Finset.finite_toSet _) ?_ hf
  · intro h t ht
    have hlo := F.cuts_bounds _ (F.left_cut h.val)
    have hhi := F.cuts_bounds _ (F.right_cut h.val)
    rw [h.property] at hlo hhi
    exact ⟨hlo.1.trans_lt ht.1, ht.2.trans_le hhi.2⟩
  · intro h k hne
    apply F.disjoint h.val k.val (fun he => hne (Subtype.ext he))
    exact h.property.trans k.property.symm
  · intro t ht
    obtain ⟨h, ho, hth⟩ := F.covers o t ht.1 ht.2
    exact mem_iUnion.mpr ⟨⟨h, ho⟩, hth⟩

/-- Reindex the sum of all original occurrence integrals by the finite subdivision. -/
theorem subdivision_sum_integral_eq {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    {R : RegionalRepresentatives g D A} {B : BoundaryPresentation g}
    (F : FiniteSubdivision R B) (f : Occurrence A B → ℝ → ℝ)
    (hf : ∀ o, IntervalIntegrable (f o) volume (occurrenceArc R B o).left
      (occurrenceArc R B o).right) :
    (∑ o : Occurrence A B,
      ∫ t in (occurrenceArc R B o).left..(occurrenceArc R B o).right, f o t) =
      ∑ h : Fin F.count, ∫ t in F.left h..F.right h, f (F.occurrence h) t := by
  classical
  let I : Fin F.count → ℝ := fun h =>
    ∫ t in F.left h..F.right h, f (F.occurrence h) t
  calc
    _ = ∑ o : Occurrence A B, ∑ h : {h : Fin F.count // F.occurrence h = o}, I h.val := by
      apply Finset.sum_congr rfl
      intro o _
      rw [subdivision_integral_eq_sum_fiber F o (f o) (hf o)]
      apply Finset.sum_congr rfl
      intro h _
      simp only [I, h.property]
    _ = ∑ h : Fin F.count, I h := by
      rw [← Fintype.sum_sigma' (fun o (h : {h : Fin F.count // F.occurrence h = o}) => I h.val)]
      exact (Equiv.sigmaFiberEquiv F.occurrence).sum_comp I

/-- Pairwise cancellation on the finite geometric refinement kills the full signed sum. -/
theorem commonRefinement_sum_integral_zero {g : RiemannianMetric S}
    {D : RegionDecomposition S} {A : Presentations D}
    {R : RegionalRepresentatives g D A} {B : BoundaryPresentation g}
    (F : CommonRefinement R B) (f : Occurrence A B → ℝ → ℝ)
    (hf : ∀ o, IntervalIntegrable (f o) volume (occurrenceArc R B o).left
      (occurrenceArc R B o).right)
    (hcancel : ∀ h : Fin F.count,
      (∫ t in F.left h..F.right h, f (F.occurrence h) t) +
        (∫ t in F.left (F.mate h)..F.right (F.mate h),
          f (F.occurrence (F.mate h)) t) = 0) :
    (∑ o : Occurrence A B,
      ∫ t in (occurrenceArc R B o).left..(occurrenceArc R B o).right, f o t) = 0 := by
  rw [subdivision_sum_integral_eq F.toFiniteSubdivision f hf]
  apply Finset.sum_ninvolution F.mate hcancel
  · intro h _
    exact F.fixed_point_free h
  · intro h
    exact Finset.mem_univ _
  · exact F.involutive

/-- Regional curvature densities, with the original boundary density subtracted. -/
def occurrenceDensity (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (D : RegionDecomposition S) (G : ∀ j, RegionalChartGeometry g D j)
    (A : Presentations D) (s : ∀ j, Fin (D.region j).boundaryCount → ℝ)
    (_R : RegionalRepresentatives g D A) (B : BoundaryPresentation g) :
    Occurrence A B → ℝ → ℝ
  | .inl ⟨j,i,k⟩ => fun t => s j i * P202Specs.LocalGaussBonnet.geodesicIntegrand
      (G j).metric (G j).connection (G j).orientation
      (G j).ambientChart (G j).ambientChart_mem (A j i) k t
  | .inr b => fun t => -B.curvatureIntegrand C b t

lemma representative_represents {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount) (k : Fin (A j i).count) :
    RepresentsRegionalArc D j i (A j i) k (R.arc j i k) :=
  ⟨R.left j i k, R.right j i k, fun t ht => (R.literal j i k t ht).2⟩

def occurrenceExceptions {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (B : BoundaryPresentation g) : Occurrence A B → Set ℝ
  | .inl ⟨j,i,k⟩ => exceptionalParameters D j i (A j i) k
  | .inr _ => ∅

lemma occurrenceExceptions_finite {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (B : BoundaryPresentation g) (o : Occurrence A B) :
    (occurrenceExceptions B o).Finite := by
  rcases o with ⟨j,i,k⟩ | b
  · exact BoundaryDensities.exceptionalParameters_finite D j i (A j i) k
  · exact finite_empty

lemma occurrenceDensity_mate_add_of_good
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (D : RegionDecomposition S) (G : ∀ j, RegionalChartGeometry g D j)
    (A : Presentations D) (s : ∀ j, Fin (D.region j).boundaryCount → ℝ)
    (hs : ∀ j, IsInducedBoundaryOrientation (D.region j) (s j))
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : CommonRefinement R B) (h : Fin F.count) {t : ℝ}
    (ht : t ∈ Ioo (F.left h) (F.right h))
    (hg : t ∉ occurrenceExceptions B (F.occurrence h))
    (hgm : F.transition h t ∉ occurrenceExceptions B (F.occurrence (F.mate h))) :
    occurrenceDensity g C D G A s R B (F.occurrence h) t +
      occurrenceDensity g C D G A s R B (F.occurrence (F.mate h)) (F.transition h t) *
        |deriv (F.transition h) t| = 0 := by
  let φ := F.transition h
  have hsub := subdivision_piece_open_bounds F.toFiniteSubdivision h
  have htm : φ t ∈ Ioo (F.left (F.mate h)) (F.right (F.mate h)) := by
    rw [← F.image_open h]
    exact mem_image_of_mem _ ht
  have hsubm := subdivision_piece_open_bounds F.toFiniteSubdivision (F.mate h)
  have hmaps : MapsTo φ (Ioo (F.left h) (F.right h))
      (Ioo (occurrenceArc R B (F.occurrence (F.mate h))).left
        (occurrenceArc R B (F.occurrence (F.mate h))).right) := by
    intro x hx
    apply hsubm
    rw [← F.image_open h]
    exact mem_image_of_mem _ hx
  have hi : InjOn φ (Ioo (F.left h) (F.right h)) := by
    rcases F.monotone h with hh | hh
    · exact hh.injOn.mono Ioo_subset_Icc_self
    · exact hh.injOn.mono Ioo_subset_Icc_self
  have hder := F.hasDerivAt h
  have hcurve : ∀ x ∈ Ioo (F.left h) (F.right h),
      (occurrenceArc R B (F.occurrence (F.mate h))).curve (φ x) =
        (occurrenceArc R B (F.occurrence h)).curve x :=
    fun x hx => (F.point_eq h x (Ioo_subset_Icc_self hx)).symm
  rcases ho : F.occurrence h with ⟨j,i,k⟩ | b
  · rcases hm : F.occurrence (F.mate h) with ⟨j',i',k'⟩ | b'
    · simp only [ho,hm,occurrenceArc] at hsub hsubm hmaps hcurve
      have ht0 : t ∈ Ioo (0 : ℝ) 1 := by
        simpa only [R.left, R.right] using hsub ht
      have htm0 : φ t ∈ Ioo (0 : ℝ) 1 := by
        simpa only [R.left, R.right] using hsubm htm
      simp only [ho, occurrenceExceptions] at hg
      simp only [hm, occurrenceExceptions] at hgm
      obtain ⟨a⟩ := BoundaryDensities.regionalSide_exists g D j (s j) (hs j)
        i (A j i) k (R.arc j i k) (representative_represents R j i k) t ht0 hg
      obtain ⟨a'⟩ := BoundaryDensities.regionalSide_exists g D j' (s j') (hs j')
        i' (A j' i') k' (R.arc j' i' k') (representative_represents R j' i' k')
        (φ t) htm0 hgm
      have he := F.interior_incidence h j i k j' i' k' ho hm
      have hpint := (he.2 ((R.arc j i k).curve t) (by
        refine ⟨t,ht,?_⟩
        simp only [ho, occurrenceArc])).1
      have hz := BoundaryDensities.regularArc_inwardDensity_cancel C
        (R.arc j i k) (R.arc j' i' k') φ ht hsub hmaps hi hder hcurve
        a a' (D.disjoint_interiors he.1) hpint
      have hd := BoundaryDensities.regional_density_eq g C hC D j (G j) (s j) (hs j)
        i (A j i) k (R.arc j i k) (representative_represents R j i k) t ht0 hg a
      have hd' := BoundaryDensities.regional_density_eq g C hC D j' (G j') (s j') (hs j')
        i' (A j' i') k' (R.arc j' i' k') (representative_represents R j' i' k')
        (φ t) htm0 hgm a'
      simp only [ho,hm,occurrenceDensity]
      rw [hd, hd']
      exact hz
    · simp only [ho,hm,occurrenceArc] at hsub hsubm hmaps hcurve
      have ht0 : t ∈ Ioo (0 : ℝ) 1 := by
        simpa only [R.left, R.right] using hsub ht
      simp only [ho, occurrenceExceptions] at hg
      obtain ⟨a⟩ := BoundaryDensities.regionalSide_exists g D j (s j) (hs j)
        i (A j i) k (R.arc j i k) (representative_represents R j i k) t ht0 hg
      have he := F.boundary_incidence h j i k b' ho hm ((R.arc j i k).curve t) (by
        refine ⟨t,ht,?_⟩
        simp only [ho, occurrenceArc])
      have hreg : regionClosure D j =ᶠ[𝓝 ((R.arc j i k).curve t)] (univ : Set M) := by
        filter_upwards [he.2.2] with p hp
        exact propext (iff_of_true hp (mem_univ p))
      have hz := BoundaryDensities.regularArc_inwardDensity_reparam C
        (R.arc j i k) (B.arc b') φ ht hsub hmaps hi hder hcurve
        (BoundaryDensities.boundarySideOfGerm a hreg) (B.side b' (φ t) (hsubm htm))
      have hd := BoundaryDensities.regional_density_eq g C hC D j (G j) (s j) (hs j)
        i (A j i) k (R.arc j i k) (representative_represents R j i k) t ht0 hg a
      have hbt : F.transition h t ∈ Ioo (B.arc b').left (B.arc b').right := hsubm htm
      simp only [ho,hm,occurrenceDensity, BoundaryPresentation.curvatureIntegrand,
        dif_pos hbt]
      rw [hd]
      rw [BoundaryDensities.boundarySideOfGerm_normal] at hz
      linarith
  · rcases hm : F.occurrence (F.mate h) with ⟨j,i,k⟩ | b'
    · simp only [ho,hm,occurrenceArc] at hsub hsubm hmaps hcurve
      have htm0 : φ t ∈ Ioo (0 : ℝ) 1 := by
        simpa only [R.left, R.right] using hsubm htm
      simp only [hm, occurrenceExceptions] at hgm
      obtain ⟨a⟩ := BoundaryDensities.regionalSide_exists g D j (s j) (hs j)
        i (A j i) k (R.arc j i k) (representative_represents R j i k) (φ t) htm0 hgm
      have hback : F.occurrence (F.mate (F.mate h)) = .inr b := by
        rw [F.involutive h, ho]
      have he := F.boundary_incidence (F.mate h) j i k b hm hback
        ((R.arc j i k).curve (φ t)) (by
          refine ⟨φ t,htm,?_⟩
          simp only [hm, occurrenceArc])
      have hreg : regionClosure D j =ᶠ[𝓝 ((R.arc j i k).curve (φ t))] (univ : Set M) := by
        filter_upwards [he.2.2] with p hp
        exact propext (iff_of_true hp (mem_univ p))
      have hz := BoundaryDensities.regularArc_inwardDensity_reparam C
        (B.arc b) (R.arc j i k) φ ht hsub hmaps hi hder hcurve
        (B.side b t (hsub ht)) (BoundaryDensities.boundarySideOfGerm a hreg)
      have hd := BoundaryDensities.regional_density_eq g C hC D j (G j) (s j) (hs j)
        i (A j i) k (R.arc j i k) (representative_represents R j i k) (φ t) htm0 hgm a
      simp only [ho,hm,occurrenceDensity, BoundaryPresentation.curvatureIntegrand,
        dif_pos (hsub ht)]
      rw [hd]
      rw [BoundaryDensities.boundarySideOfGerm_normal] at hz
      linarith
    · exact False.elim (F.no_boundary_boundary h b b' ho hm)

lemma occurrenceDensity_mate_add_ae
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (D : RegionDecomposition S) (G : ∀ j, RegionalChartGeometry g D j)
    (A : Presentations D) (s : ∀ j, Fin (D.region j).boundaryCount → ℝ)
    (hs : ∀ j, IsInducedBoundaryOrientation (D.region j) (s j))
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (F : CommonRefinement R B) (h : Fin F.count) :
    ∀ᵐ t ∂volume, t ∈ Ioo (F.left h) (F.right h) →
      occurrenceDensity g C D G A s R B (F.occurrence h) t +
        occurrenceDensity g C D G A s R B (F.occurrence (F.mate h)) (F.transition h t) *
          |deriv (F.transition h) t| = 0 := by
  have hi : InjOn (F.transition h) (Ioo (F.left h) (F.right h)) := by
    rcases F.monotone h with hh | hh
    · exact hh.injOn.mono Ioo_subset_Icc_self
    · exact hh.injOn.mono Ioo_subset_Icc_self
  have hf : (Ioo (F.left h) (F.right h) ∩
      (F.transition h) ⁻¹' occurrenceExceptions B (F.occurrence (F.mate h))).Finite :=
    Set.Finite.of_injOn (t := occurrenceExceptions B (F.occurrence (F.mate h)))
      (fun x hx => hx.2) (hi.mono inter_subset_left)
      (occurrenceExceptions_finite B _)
  filter_upwards [(occurrenceExceptions_finite B (F.occurrence h)).countable.ae_notMem volume,
    hf.countable.ae_notMem volume] with t hgood hgoodm
  intro ht
  exact occurrenceDensity_mate_add_of_good g C hC D G A s hs R B F h ht hgood
    (fun hbad => hgoodm ⟨ht,hbad⟩)

/-- The literal signed regional integrand is integrable for every supplied
regional chart geometry and every induced boundary presentation. -/
theorem signed_regional_integrand_integrable {g : RiemannianMetric S}
    {D : RegionDecomposition S} {j : Fin D.regionCount}
    (G : RegionalChartGeometry g D j)
    (A : ∀ i : Fin (D.region j).boundaryCount,
      P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (s : Fin (D.region j).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region j) s)
    (i : Fin (D.region j).boundaryCount) (k : Fin (A i).count) :
    IntervalIntegrable
      (fun t => s i * P202Specs.LocalGaussBonnet.geodesicIntegrand
        G.metric G.connection G.orientation G.ambientChart G.ambientChart_mem (A i) k t)
      volume 0 1 := by
  obtain ⟨_, hlocal⟩ := P202.LocalGaussBonnet.localGaussBonnet
    G.ambientSurface G.metric G.connection G.connection_LC
    G.curvature G.curvature_represents G.orientation G.ambientChart
    G.ambientChart_mem G.orientation_positive (D.region j)
    (regionalChartGeometry_carrier_subset G)
  exact ((hlocal A s hs).2.1 i k).const_mul (s i)


/-- Every literal occurrence density is integrable on its own original
parameter interval. -/
theorem occurrenceDensity_integrable
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (D : RegionDecomposition S) (G : ∀ j, RegionalChartGeometry g D j)
    (A : Presentations D) (s : ∀ j, Fin (D.region j).boundaryCount → ℝ)
    (hs : ∀ j, IsInducedBoundaryOrientation (D.region j) (s j))
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g)
    (o : Occurrence A B) :
    IntervalIntegrable (occurrenceDensity g C D G A s R B o) volume
      (occurrenceArc R B o).left (occurrenceArc R B o).right := by
  rcases o with ⟨j, i, k⟩ | b
  · simpa only [occurrenceDensity, occurrenceArc, R.left, R.right] using
      signed_regional_integrand_integrable (G j) (A j) (s j) (hs j) i k
  · simpa only [occurrenceDensity, occurrenceArc, neg_one_mul] using
      (boundary_curvatureIntegrand_integrable g C B b).const_mul (-1 : ℝ)

/-- Summing the original occurrence integrals is exactly the regional signed
geodesic integral sum minus the original surface's literal boundary integral. -/
theorem occurrenceDensity_sum_integral_eq
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (D : RegionDecomposition S) (G : ∀ j, RegionalChartGeometry g D j)
    (A : Presentations D) (s : ∀ j, Fin (D.region j).boundaryCount → ℝ)
    (R : RegionalRepresentatives g D A) (B : BoundaryPresentation g) :
    (∑ o : Occurrence A B,
      ∫ t in (occurrenceArc R B o).left..(occurrenceArc R B o).right,
        occurrenceDensity g C D G A s R B o t) =
    (∑ j : Fin D.regionCount,
      P202Specs.LocalGaussBonnet.geodesicIntegral
        (G j).metric (G j).connection (G j).orientation
        (G j).ambientChart (G j).ambientChart_mem (D.region j) (A j) (s j)) -
      B.curvatureIntegral C := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma,
    occurrenceDensity, occurrenceArc, R.left, R.right,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
    Finset.sum_neg_distrib, P202Specs.LocalGaussBonnet.geodesicIntegral,
    BoundaryPresentation.curvatureIntegral, Finset.mul_sum, sub_eq_add_neg]

end P202.GlobalGaussBonnet.BoundaryGluing

namespace P202.GlobalGaussBonnet
universe u

/-- Summing the literal regional boundary integrals cancels every interior
piece and leaves exactly the prescribed original surface boundary integral. -/
theorem regional_boundary_gluing :
    P202Specs.GlobalGaussBonnet.BoundaryGluingExpected.regional_boundary_gluing.{u} := by
  intro kind M hM S hcompact g C hC D G A s hs B
  obtain ⟨R, ⟨F⟩⟩ := BoundaryGluing.regional_boundary_refinement S g D A B
  let f := BoundaryGluing.occurrenceDensity g C D G A s R B
  have hcancel : ∀ h : Fin F.count,
      (∫ t in F.left h..F.right h, f (F.occurrence h) t) +
        (∫ t in F.left (F.mate h)..F.right (F.mate h),
          f (F.occurrence (F.mate h)) t) = 0 := by
    intro h
    exact BoundaryGluing.integral_pair_cancel_of_ae _ _ _
      (F.ordered h) (F.ordered (F.mate h)) (F.continuous h)
      (F.hasDerivAt h) (F.derivative_sign h) (F.image_closed h)
      (BoundaryGluing.occurrenceDensity_mate_add_ae g C hC D G A s hs R B F h)
  have hz := BoundaryGluing.commonRefinement_sum_integral_zero F f
    (BoundaryGluing.occurrenceDensity_integrable g C D G A s hs R B) hcancel
  rw [BoundaryGluing.occurrenceDensity_sum_integral_eq g C D G A s R B] at hz
  exact sub_eq_zero.mp hz

end P202.GlobalGaussBonnet
