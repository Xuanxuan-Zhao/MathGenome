import MathGenome.Internal.FourierSobolev.Specs.P102.U4.Rademacher
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ACL
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.AbsoluteContinuityOnLines

import MathGenome.Internal.FourierSobolev.P102.U4.ACL
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace P102.U4

/-- A Lipschitz neighborhood can be chosen open and inside the domain. -/
theorem exists_open_lipschitz_neighborhood {m k : ℕ} {U : Opens (Space m)}
    {f : Space m → Space k} (hf : LocallyLipschitzOn (U : Set (Space m)) f)
    {x : Space m} (hx : x ∈ U) :
    ∃ (V : Opens (Space m)) (L : ℝ≥0), x ∈ V ∧ V ≤ U ∧
      LipschitzOnWith L f (V : Set (Space m)) := by
  obtain ⟨L, s, hs, hL⟩ := hf hx
  rw [U.isOpen.nhdsWithin_eq hx] at hs
  obtain ⟨v, hvs, hv, hxv⟩ := mem_nhds_iff.mp (inter_mem hs (U.isOpen.mem_nhds hx))
  exact ⟨⟨v, hv⟩, L, hxv, fun y hy => (hvs hy).2,
    hL.mono fun y hy => (hvs hy).1⟩

/-- Local applicability of the finite-dimensional Rademacher theorem. -/
theorem ae_differentiableAt_of_locallyLipschitzOn {m k : ℕ} {U : Opens (Space m)}
    {f : Space m → Space k} (hf : LocallyLipschitzOn (U : Set (Space m)) f) :
    ∀ᵐ x ∂volume.restrict (U : Set (Space m)), DifferentiableAt ℝ f x := by
  apply ExpandedFA.Sobolev.Lines.ae_on_set_of_locally_ae
  intro x hx
  obtain ⟨V, L, hxV, hVU, hL⟩ := exists_open_lipschitz_neighborhood hf hx
  refine ⟨V, hxV, ?_⟩
  filter_upwards [hL.ae_differentiableWithinAt V.isOpen.measurableSet,
    ae_restrict_mem V.isOpen.measurableSet] with y hy hyV
  exact hy.differentiableAt (V.isOpen.mem_nhds hyV)

/-- The canonical derivative is essentially bounded on each local Lipschitz set. -/
theorem fderiv_memLp_top_on_open {m k : ℕ} {f : Space m → Space k}
    (V : Opens (Space m)) {L : ℝ≥0}
    (hL : LipschitzOnWith L f (V : Set (Space m))) :
    MemLp (fderiv ℝ f) ∞ (volume.restrict (V : Set (Space m))) := by
  apply memLp_top_of_bound (measurable_fderiv ℝ f).aestronglyMeasurable L
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
  exact norm_fderiv_le_of_lipschitzOn ℝ (V.isOpen.mem_nhds hx) hL

/-- Local essential boundedness implies the required local L¹ property. -/
theorem fderiv_locallyIntegrableOn {m k : ℕ} {U : Opens (Space m)}
    {f : Space m → Space k} (hf : LocallyLipschitzOn (U : Set (Space m)) f) :
    LocallyIntegrableOn (fderiv ℝ f) U volume := by
  intro x hx
  obtain ⟨V, L, hxV, hVU, hL⟩ := exists_open_lipschitz_neighborhood hf hx
  have h := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((fderiv_memLp_top_on_open V hL).locallyIntegrable le_top)
  have hxI := h x hxV
  rw [V.isOpen.nhdsWithin_eq hxV] at hxI
  exact hxI.filter_mono nhdsWithin_le_nhds

/-- Scalar components preserve local Lipschitz regularity. -/
theorem locallyLipschitzOn_component {m k : ℕ} {U : Opens (Space m)}
    {f : Space m → Space k} (hf : LocallyLipschitzOn (U : Set (Space m)) f)
    (i : Fin k) : LocallyLipschitzOn (U : Set (Space m)) (fun x => f x i) := by
  intro x hx
  obtain ⟨L, s, hs, hL⟩ := hf hx
  let p : Space k →L[ℝ] ℝ := EuclideanSpace.proj i
  exact ⟨‖p‖₊ * L, s, hs, p.lipschitzWith.comp_lipschitzOnWith hL⟩

/-- Coordinate lines in the Euclidean norm have their usual affine form. -/
theorem acl_line_eq_affine {m : ℕ} (j : Fin m) (z : ACL.Transverse j) (t : ℝ) :
    ACL.line j z t = ACL.line j z 0 + t • coordinateVector m j := by
  ext i
  by_cases hi : i = j
  · subst i
    simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, coordinateVector,
      EuclideanSpace.basisFun_apply]
  · simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, coordinateVector,
      EuclideanSpace.basisFun_apply, hi]

/-- The parametrization has derivative the standard unit coordinate vector. -/
theorem acl_line_hasDerivAt {m : ℕ} (j : Fin m) (z : ACL.Transverse j) (t : ℝ) :
    HasDerivAt (ACL.line j z) (coordinateVector m j) t := by
  have h := ((hasDerivAt_id t).smul_const (coordinateVector m j)).const_add (ACL.line j z 0)
  simpa only [one_smul, id_eq, ← acl_line_eq_affine] using h

/-- Coordinate line parametrizations preserve Euclidean distance. -/
theorem acl_line_lipschitz {m : ℕ} (j : Fin m) (z : ACL.Transverse j) :
    LipschitzWith 1 (ACL.line j z) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [acl_line_eq_affine j z s, acl_line_eq_affine j z t, dist_eq_norm,
    add_sub_add_left_eq_sub, ← sub_smul, norm_smul]
  simp [coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    PiLp.norm_single, Real.dist_eq]

/-- Locally Lipschitz components are AC on every compact interior fiber interval. -/
theorem locallyAC_on_coordinate_fiber {m k : ℕ} {U : Opens (Space m)}
    {f : Space m → Space k} (hf : LocallyLipschitzOn (U : Set (Space m)) f)
    (i : Fin k) (j : Fin m) (z : ACL.Transverse j) :
    ACL.LocallyAC (fun t => f (ACL.line j z t) i) (ACL.fiber U j z) := by
  intro a b hab
  have hcompact := (isCompact_uIcc (a := a) (b := b)).image (acl_line_lipschitz j z).continuous
  have hsub : ACL.line j z '' uIcc a b ⊆ (U : Set (Space m)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hab ht
  obtain ⟨C, hC⟩ := ((locallyLipschitzOn_component hf i).mono hsub).exists_lipschitzOnWith_of_compact hcompact
  exact (hC.comp (acl_line_lipschitz j z).lipschitzOnWith
    (mapsTo_image (ACL.line j z) (uIcc a b))).absolutelyContinuousOnInterval

/-- Completed Fubini, transported from product coordinates to Euclidean volume. -/
theorem ae_on_acl_fibers {m : ℕ} (U : Opens (Space m)) (j : Fin m)
    {P : Space m → Prop} (hP : ∀ᵐ x ∂volume.restrict (U : Set (Space m)), P x) :
    ∀ᵐ z : ACL.Transverse j ∂volume,
      ∀ᵐ t ∂volume.restrict (ACL.fiber U j z), P (ACL.line j z t) := by
  let W : Opens (Fin m → ℝ) :=
    ⟨WithLp.toLp 2 ⁻¹' (U : Set (Space m)),
      U.isOpen.preimage (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ))⟩
  have h := (PiLp.volume_preserving_toLp (Fin m)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' U.isOpen.measurableSet).mp hP)
  have hW : ∀ᵐ x ∂volume.restrict (W : Set (Fin m → ℝ)), P (WithLp.toLp 2 x) :=
    (ae_restrict_iff' W.isOpen.measurableSet).mpr h
  exact ExpandedFA.Sobolev.Lines.ae_on_fibers (Ω := W)
    (P := fun x => P (WithLp.toLp 2 x)) j hW

/-- The original continuous scalar component itself is the ACL representative;
Fubini transfers the a.e. Fréchet identity to almost every entire fiber. -/
theorem component_has_acl_representative {m k : ℕ} {U : Opens (Space m)}
    {f : Space m → Space k} (hf : LocallyLipschitzOn (U : Set (Space m)) f)
    (i : Fin k) (j : Fin m) :
    ACL.HasRepresentative U j (fun x => f x i)
      (fun x => (fderiv ℝ f x (coordinateVector m j)) i) := by
  refine ⟨fun x => f x i, Filter.EventuallyEq.rfl, ?_⟩
  filter_upwards [ae_on_acl_fibers U j (ae_differentiableAt_of_locallyLipschitzOn hf)] with z hz
  refine ⟨locallyAC_on_coordinate_fiber hf i j z, ?_⟩
  filter_upwards [hz] with t ht
  have hd := (EuclideanSpace.proj i : Space k →L[ℝ] ℝ).hasFDerivAt.comp
    (ACL.line j z t) ht.hasFDerivAt
  exact hd.comp_hasDerivAt t (acl_line_hasDerivAt j z t)

/-- Conditional derivation of the full Rademacher statement. The three exact
ACL interfaces are explicit premises, in their contracted order. No closed
`rademacher` theorem is defined until the owner supplies the upstream proofs. -/
theorem rademacher_conditional
    (_hcharacterization : ACLExpected.Characterization)
    (hconverse : ACLExpected.Converse)
    (_hdimensionOne : ACLExpected.DimensionOne) : RademacherExpected.Theorem := by
  intro m hm k U f hf
  refine ⟨fderiv ℝ f, measurable_fderiv ℝ f, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_differentiableAt_of_locallyLipschitzOn hf] with x hx
    exact hx.hasFDerivAt
  · intro i j
    let entry : (Space m →L[ℝ] Space k) →L[ℝ] ℝ :=
      (EuclideanSpace.proj i : Space k →L[ℝ] ℝ).comp
        (ContinuousLinearMap.apply ℝ (Space k) (coordinateVector m j))
    have hentry : LocallyIntegrableOn
        (fun x => (fderiv ℝ f x (coordinateVector m j)) i) U volume :=
      entry.locallyIntegrableOn_comp (fderiv_locallyIntegrableOn hf)
    refine ⟨hentry, ?_⟩
    exact hconverse m hm ℝ U j (fun x => f x i)
      (fun x => (fderiv ℝ f x (coordinateVector m j)) i)
      ((locallyLipschitzOn_component hf i).continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      hentry (component_has_acl_representative hf i j)
  · intro x hx
    obtain ⟨V, L, hxV, hVU, hL⟩ := exists_open_lipschitz_neighborhood hf hx
    exact ⟨V, hxV, hVU, fderiv_memLp_top_on_open V hL⟩
  · intro V hVU L hL
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact norm_fderiv_le_of_lipschitzOn ℝ (V.isOpen.mem_nhds hx) hL

end P102.U4

theorem _root_.«P102».«U4».«rademacher» : _root_.«P102».«U4».«RademacherExpected».«Theorem» :=
  @_root_.«P102».«U4».«rademacher_conditional» (@_root_.«P102».«U4».«acl_characterization») (@_root_.«P102».«U4».«acl_converse») (@_root_.«P102».«U4».«acl_dimensionOne»)
