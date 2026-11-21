import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalPrimitiveHomotopy
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.PeriodCriterion

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SmoothManifolds.LocalPrimitiveHomotopy
open ModelData AtlasData MapData PartitionData TangentData CovectorData
  BundleOperationsData PathIntegrationData PeriodData Set Filter
open scoped Topology
universe u
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]

/-- Changing a covector field off the path image has no effect on its integral. -/
theorem integral_congr_field (S : SmoothManifold n k M) (α β : CovectorField S)
    (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, α (γ t) = β (γ t)) :
    pathIntegral S α γ a b = pathIntegral S β γ a b := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  change α (γ t) _ = β (γ t) _
  rw [h t ⟨ht.1.le, ht.2.le⟩]

theorem integral_local_potential :
    Specs.SmoothManifolds.Integration.LocalPrimitiveHomotopy.integral_local_potentialType.{u} := by
  intro n k M _ S α f hf γ a b hγ hdf
  rw [← integral_congr_field S (dFunction S f hf) α γ hγ.1 hdf]
  exact PathIntegration.integral_dFunction S f hf γ a b hγ

/-- Restrict a smooth piece; the endpoint velocities may become one-sided. -/
theorem smoothOnInterval_mono (S : SmoothManifold n k M) (γ : ℝ → M)
    {a b c d : ℝ} (hγ : SmoothOnInterval S γ a b)
    (hcd : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b) : SmoothOnInterval S γ c d := by
  have hid : ScalarSmoothOnInterval (id : ℝ → ℝ) c d :=
    ⟨hcd, fun t _ => ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id,
      fun _ _ => rfl⟩⟩
  exact PathIntegration.smoothOnInterval_comp S γ id hγ hid
    (fun t ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩)

/-- The finite-piece class is closed under arbitrary closed subintervals. -/
theorem piecewiseSmoothOn_mono (S : SmoothManifold n k M) (γ : ℝ → M)
    {a b c d : ℝ} (hγ : PiecewiseSmoothOn S γ a b)
    (hcd : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b) : PiecewiseSmoothOn S γ c d := by
  classical
  obtain ⟨s, hs⟩ := hγ.2.2
  let F : Finset ℝ := insert c (insert d
    (((Finset.range (s.count+1)).image s.point).filter (fun x => x ∈ Icc c d)))
  have hc : c ∈ F := Finset.mem_insert_self _ _
  have hd : d ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hF : ∀ x ∈ F, x ∈ Icc c d := by
    intro x hx
    simp only [F, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨_, hx⟩
    · exact ⟨le_rfl, hcd⟩
    · exact ⟨hcd, le_rfl⟩
    · exact hx
  let r := PathIntegration.Subdivision.ofFinset F hc hd hF
  refine ⟨hcd, hγ.2.1.mono (Icc_subset_Icc hac hdb), r, ?_⟩
  intro i hi
  have hxy := PathIntegration.Subdivision.start_lt_end r hi
  have hx := PathIntegration.Subdivision.point_mem r hi.le
  have hy := PathIntegration.Subdivision.point_mem r hi
  obtain ⟨j, hj, hjx, hyj⟩ := PathIntegration.Subdivision.exists_piece_containing s hxy
    (hac.trans hx.1) (hy.2.trans hdb) (fun j hj hint => by
      apply PathIntegration.Subdivision.ofFinset_avoids F hc hd hF hi (s.point j) _ hint
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨j, Finset.mem_range.mpr (by omega), rfl⟩,
        ⟨hx.1.trans hint.1.le, hint.2.le.trans hy.2⟩⟩)
  exact smoothOnInterval_mono S γ (hs j hj) hxy.le hjx hyj

/-- Vanishing differential on an open set gives local constancy on that set.
This uses the actual restricted manifold and pullback differential. -/
theorem locallyConstantOn_of_dFunction_zero (S : SmoothManifold n k M)
    (f : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f)
    (U : Set M) (hU : IsOpen U) (hdf : ∀ p ∈ U, dFunction S f hf p = 0) :
    IsLocallyConstant (fun p : U => f p.val) := by
  obtain ⟨R, _, _, hι⟩ := exists_openSubset_smoothManifold S U hU
  classical
  choose L hL huniq using differential_exists R S Subtype.val hι
  obtain ⟨hfr, hderiv⟩ := Covectors.pullback_differential S R Subtype.val hι L hL f hf
  obtain ⟨C⟩ := BundleOperations.exists_cotangent R
  apply PeriodCriterion.locally_constant_of_dFunction_zero R C (f ∘ Subtype.val) hfr
  rw [hderiv]
  funext p
  apply LinearMap.ext
  intro v
  change dFunction S f hf p.val (L p v) = 0
  rw [hdf p.val p.property, LinearMap.zero_apply]

/-- Potentials with the same differential differ locally by a constant on
an open overlap. No connectedness assumption on that overlap is needed. -/
theorem potential_difference_locallyConstant (S : SmoothManifold n k M)
    (f g : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f)
    (hg : ScalarSmooth S.smoothStructure.val g) (U : Set M) (hU : IsOpen U)
    (hdf : ∀ p ∈ U, dFunction S f hf p = dFunction S g hg p) :
    IsLocallyConstant (fun p : U => f p.val - g p.val) := by
  have hfg : ScalarSmooth S.smoothStructure.val (fun p => f p - g p) :=
    fun p => ScalarContDiffAt.add (hf p) (ScalarContDiffAt.neg (hg p))
  apply locallyConstantOn_of_dFunction_zero S _ hfg U hU
  intro p hp
  rw [PeriodCriterion.dFunction_sub S f g hf hg hfg]
  change dFunction S f hf p - dFunction S g hg p = 0
  exact sub_eq_zero.mpr (hdf p hp)

/-- Exact coefficients are integrable on every finite-piece smooth path. -/
theorem exactCoefficient_integrable (S : SmoothManifold n k M) (f : M → ℝ)
    (hf : ScalarSmooth S.smoothStructure.val f) (γ : ℝ → M) {a b : ℝ}
    (hγ : PiecewiseSmoothOn S γ a b) :
    IntervalIntegrable (coefficient S (dFunction S f hf) γ) MeasureTheory.volume a b := by
  obtain ⟨s, hs⟩ := hγ.2.2
  have hi (i : ℕ) (hi : i < s.count) :=
    PathIntegration.exactCoefficient_integrable_smoothPiece S f hf γ (hs i hi)
  simpa only [s.first, s.last] using IntervalIntegrable.trans_iterate hi

/-- Local FTC on a monotone subdivision; repeated subdivision points are allowed. -/
theorem integral_eq_sum_potentials (S : SmoothManifold n k M) (α : CovectorField S)
    (γ : ℝ → M) {a b : ℝ} (hγ : PiecewiseSmoothOn S γ a b)
    (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) (ht0 : t 0 = a) (htN : t N = b)
    (f : ℕ → M → ℝ) (hf : ∀ j, ScalarSmooth S.smoothStructure.val (f j))
    (hdf : ∀ j < N, ∀ x ∈ Icc (t j) (t (j+1)),
      dFunction S (f j) (hf j) (γ x) = α (γ x)) :
    pathIntegral S α γ a b =
      ∑ j ∈ Finset.range N, (f j (γ (t (j+1))) - f j (γ (t j))) := by
  have hpiece (j : ℕ) (hj : j < N) : PiecewiseSmoothOn S γ (t j) (t (j+1)) := by
    apply piecewiseSmoothOn_mono S γ hγ (ht j.le_succ)
    · rw [← ht0]; exact ht (Nat.zero_le _)
    · rw [← htN]; exact ht hj
  have hi (j : ℕ) (hj : j < N) :
      IntervalIntegrable (coefficient S α γ) MeasureTheory.volume (t j) (t (j+1)) := by
    apply (exactCoefficient_integrable S (f j) (hf j) γ (hpiece j hj)).congr_uIoo
    rw [uIoo_of_le (ht j.le_succ)]
    intro x hx
    change dFunction S (f j) (hf j) (γ x) _ = α (γ x) _
    rw [hdf j hj x ⟨hx.1.le, hx.2.le⟩]
  calc
    _ = ∑ j ∈ Finset.range N, pathIntegral S α γ (t j) (t (j+1)) := by
      simpa only [pathIntegral, ht0, htN] using
        (intervalIntegral.sum_integral_adjacent_intervals hi).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_local_potential S α (f j) (hf j) γ _ _
        (hpiece j (Finset.mem_range.mp hj)) (hdf j (Finset.mem_range.mp hj))

/-- Endpoint increments computed in two potential neighborhoods agree along
any continuous edge in their overlap. The edge need not be differentiable. -/
theorem potential_increment_eq (S : SmoothManifold n k M) (α : CovectorField S)
    (f g : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f)
    (hg : ScalarSmooth S.smoothStructure.val g)
    (U V : Set M) (hU : IsOpen U) (hV : IsOpen V)
    (hdf : ∀ p ∈ U, dFunction S f hf p = α p)
    (hdg : ∀ p ∈ V, dFunction S g hg p = α p)
    (e : unitInterval → M) {a b : unitInterval} (hab : a ≤ b)
    (he : ContinuousOn e (Icc a b)) (heU : MapsTo e (Icc a b) (U ∩ V)) :
    f (e b) - f (e a) = g (e b) - g (e a) := by
  have hlc := potential_difference_locallyConstant S f g hf hg (U ∩ V) (hU.inter hV)
    (fun p hp => (hdf p hp.1).trans (hdg p hp.2).symm)
  let eU : Icc a b → {p : M // p ∈ U ∩ V} := fun s => ⟨e s, heU s.property⟩
  have heUc : Continuous eU :=
    (he.domRestrict).subtype_mk (fun s => heU s.property)
  let : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hc := (hlc.comp_continuous heUc).apply_eq_of_preconnectedSpace
    (⟨b, ⟨hab, le_rfl⟩⟩ : Icc a b) ⟨a, ⟨le_rfl, hab⟩⟩
  change f (e b) - g (e b) = f (e a) - g (e a) at hc
  linarith

/-- Cancellation on a rectangular grid. This statement uses only the
continuity of H and its constant endpoint sides. -/
theorem grid_sum_eq (S : SmoothManifold n k M) (α : CovectorField S)
    (H : unitInterval × unitInterval → M) (hH : Continuous H)
    (t : ℕ → unitInterval) (ht : Monotone t) (N : ℕ)
    (hside0 : ∀ i, H (t i, t 0) = H (t 0, t 0))
    (hsideN : ∀ i, H (t i, t N) = H (t 0, t N))
    (U : ℕ → ℕ → Set M) (hU : ∀ i j, IsOpen (U i j))
    (f : ℕ → ℕ → M → ℝ)
    (hf : ∀ i j, ScalarSmooth S.smoothStructure.val (f i j))
    (hdf : ∀ i j p, p ∈ U i j → dFunction S (f i j) (hf i j) p = α p)
    (hcell : ∀ i j, MapsTo H (Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1))) (U i j)) :
    (∑ j ∈ Finset.range N, (f 0 j (H (t 0, t (j+1))) - f 0 j (H (t 0, t j)))) =
      ∑ j ∈ Finset.range N, (f N j (H (t N, t (j+1))) - f N j (H (t N, t j))) := by
  let R (i : ℕ) : ℝ :=
    ∑ j ∈ Finset.range N, (f i j (H (t i, t (j+1))) - f i j (H (t i, t j)))
  let V (i j : ℕ) : ℝ := f i j (H (t (i+1), t j)) - f i j (H (t i, t j))
  have hhor (i j : ℕ) :
      f (i+1) j (H (t (i+1), t (j+1))) - f (i+1) j (H (t (i+1), t j)) =
      f i j (H (t (i+1), t (j+1))) - f i j (H (t (i+1), t j)) := by
    apply potential_increment_eq S α _ _ (hf (i+1) j) (hf i j)
      (U (i+1) j) (U i j) (hU (i+1) j) (hU i j)
      (hdf (i+1) j) (hdf i j) (fun s => H (t (i+1), s)) (ht j.le_succ)
      (hH.comp (Continuous.prodMk_right _)).continuousOn
    intro s hs
    exact ⟨hcell (i+1) j ⟨⟨le_rfl, ht (i+1).le_succ⟩, hs⟩,
      hcell i j ⟨⟨ht i.le_succ, le_rfl⟩, hs⟩⟩
  have hver (i j : ℕ) :
      f i j (H (t (i+1), t (j+1))) - f i j (H (t i, t (j+1))) = V i (j+1) := by
    apply potential_increment_eq S α _ _ (hf i j) (hf i (j+1))
      (U i j) (U i (j+1)) (hU i j) (hU i (j+1))
      (hdf i j) (hdf i (j+1)) (fun s => H (s, t (j+1))) (ht i.le_succ)
      (hH.comp (Continuous.prodMk_left _)).continuousOn
    intro s hs
    exact ⟨hcell i j ⟨hs, ⟨ht j.le_succ, le_rfl⟩⟩,
      hcell i (j+1) ⟨hs, ⟨le_rfl, ht (j+1).le_succ⟩⟩⟩
  have hstep (i : ℕ) : R (i+1) = R i := by
    have hsum : R (i+1) - R i = V i N - V i 0 := by
      calc
        _ = ∑ j ∈ Finset.range N, (V i (j+1) - V i j) := by
          dsimp only [R]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [hhor i j]
          have hh := hver i j
          dsimp only [V] at *
          linarith
        _ = _ := Finset.sum_range_sub (V i) N
    have hv0 : V i 0 = 0 := by simp [V, hside0]
    have hvN : V i N = 0 := by simp [V, hsideN]
    rw [hv0, hvN] at hsum
    linarith
  have hR (i : ℕ) : R i = R 0 := by
    induction i with
    | zero => rfl
    | succ i hi => exact (hstep i).trans hi
  exact (hR N).symm

/-- Compute the original integral using a partition of its affine unit-interval
parameter. This also works when the affine map is constant. -/
theorem integral_eq_sum_affine_potentials (S : SmoothManifold n k M)
    (α : CovectorField S) (γ : ℝ → M) {a b : ℝ}
    (hγ : PiecewiseSmoothOn S γ a b)
    (t : ℕ → unitInterval) (ht : Monotone t) (N : ℕ)
    (ht0 : t 0 = 0) (htN : t N = 1)
    (f : ℕ → M → ℝ) (hf : ∀ j, ScalarSmooth S.smoothStructure.val (f j))
    (hdf : ∀ j < N, ∀ s ∈ Icc (t j) (t (j+1)),
      dFunction S (f j) (hf j) (γ (a + (b-a)*s.val)) = α (γ (a + (b-a)*s.val))) :
    pathIntegral S α γ a b = ∑ j ∈ Finset.range N,
      (f j (γ (a + (b-a)*(t (j+1)).val)) - f j (γ (a + (b-a)*(t j).val))) := by
  let A : unitInterval → ℝ := fun s => a + (b-a)*s.val
  have hAc : Continuous A :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  have hAm : Monotone A := by
    intro x y hxy
    exact add_le_add (le_refl a) (mul_le_mul_of_nonneg_left
      (show (x : ℝ) ≤ (y : ℝ) from hxy) (sub_nonneg.mpr hγ.1))
  have hA0 : A (t 0) = a := by simp [A, ht0]
  have hAN : A (t N) = b := by simp [A, htN]
  apply integral_eq_sum_potentials S α γ hγ (fun j => A (t j)) (hAm.comp ht) N
    hA0 hAN f hf
  intro j hj x hx
  have himage := hAc.continuousOn.image_Icc_of_monotoneOn
    (ht j.le_succ) (hAm.monotoneOn (Icc (t j) (t (j+1))))
  rw [← himage] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  exact hdf j hj s hs

/-- A locally exact intrinsic covector field has the same actual integral
along continuously homotopic piecewise smooth paths with fixed endpoints. -/
theorem homotopy_invariance :
    Specs.SmoothManifolds.Integration.LocalPrimitiveHomotopy.homotopy_invarianceType.{u} := by
  intro n k M _ S α hlocal γ η a b c d hab hcd hγ hη H hH h0 h1 hs0 hs1
  classical
  choose U hU hp f hf hdf using hlocal
  obtain ⟨t, ht0, ht, ⟨N, hN⟩, hcells⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (c := fun p => H ⁻¹' U p) (fun p => (hU p).preimage hH)
      (fun z _ => mem_iUnion.mpr ⟨H z, hp (H z)⟩)
  choose p hcell using hcells
  have htN : t N = 1 := hN N le_rfl
  let W (i j : ℕ) : Set M := U (p i j)
  let F (i j : ℕ) : M → ℝ := f (p i j)
  have hF (i j : ℕ) : ScalarSmooth S.smoothStructure.val (F i j) := hf (p i j)
  have hDF (i j : ℕ) (q : M) (hq : q ∈ W i j) :
      dFunction S (F i j) (hF i j) q = α q := hdf (p i j) q hq
  have hW (i j : ℕ) : IsOpen (W i j) := hU (p i j)
  have hgrid := grid_sum_eq S α H hH t ht N
    (by intro i; rw [ht0, hs0, hs0])
    (by intro i; rw [htN, hs1, hs1]) W hW F hF hDF hcell
  calc
    pathIntegral S α γ a b =
        ∑ j ∈ Finset.range N, (F 0 j (H (t 0, t (j+1))) - F 0 j (H (t 0, t j))) := by
      have hsum := integral_eq_sum_affine_potentials S α γ hγ t ht N ht0 htN
        (F 0) (hF 0) (fun j _ s hs => by
          have hmem := hcell 0 j (show (t 0, s) ∈
              Icc (t 0) (t (0+1)) ×ˢ Icc (t j) (t (j+1)) from
            ⟨⟨le_rfl, ht (Nat.zero_le 1)⟩, hs⟩)
          have hd := hDF 0 j (H (t 0, s)) hmem
          have heq : H (t 0, s) = γ (a + (b-a)*s.val) := by rw [ht0, h0]
          exact heq ▸ hd)
      simpa only [ht0, h0] using hsum
    _ = ∑ j ∈ Finset.range N,
        (F N j (H (t N, t (j+1))) - F N j (H (t N, t j))) := hgrid
    _ = pathIntegral S α η c d := by
      have hsum := integral_eq_sum_affine_potentials S α η hη t ht N ht0 htN
        (F N) (hF N) (fun j _ s hs => by
          have hmem := hcell N j (show (t N, s) ∈
              Icc (t N) (t (N+1)) ×ˢ Icc (t j) (t (j+1)) from
            ⟨⟨le_rfl, ht N.le_succ⟩, hs⟩)
          have hd := hDF N j (H (t N, s)) hmem
          have heq : H (t N, s) = η (c + (d-c)*s.val) := by rw [htN, h1]
          exact heq ▸ hd)
      simpa only [htN, h1] using hsum.symm

end SmoothManifolds.LocalPrimitiveHomotopy
