import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.RegularDomainGeometryAndJordanMeasurability
import MathGenome.Internal.MultivariableAnalysis.D04.C12.ClassicalRegularDomains
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OutwardFirstBoundaryOrientation
import MathGenome.Internal.MultivariableAnalysis.D04.C15.LowerDimensionalImagesHaveZeroContent
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04.RegularDomainGeometry
open ClassicalRegularDomains NullCovers
open Specs.D04.C12.RegularDomainGeometryAndJordanMeasurability
open private inverse_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction

lemma regularity_one : ManifoldRegularity 1 := ⟨le_rfl, by simp⟩

/-- The closure of an open set is its disjoint interior part and ambient boundary. -/
theorem closure_difference : closure_differenceType := by
  intro n D hD
  rw [frontier, hD.isOpen.interior_eq]

/-- In a defining neighborhood the closure is exactly the nonpositive side. -/
lemma closure_iff_nonpos {n : ℕ} {D U : Set (E n)} {ρ : E n → ℝ}
    (hD : IsOpen D) (hρ : IsDefiningFunction D U ρ) {x : E n} (hx : x ∈ U) :
    x ∈ closure D ↔ ρ x ≤ 0 := by
  have hcl : closure D = D ∪ frontier D := by
    rw [frontier, hD.interior_eq]
    exact (union_sdiff_cancel subset_closure).symm
  rw [hcl, mem_union, hρ.negative x hx, hρ.zero_level x hx]
  exact le_iff_lt_or_eq.symm

/-- A compact restriction of a chart has zero ambient content in higher dimension. -/
lemma chart_local_contentZero {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (hkn : k < n) {u : E k}
    (hu : u ∈ c.source) (hc : c.half = false) :
    ∃ O : Set (E n), IsOpen O ∧ c.toFun u ∈ O ∧ ContentZero (M ∩ O) := by
  obtain ⟨W, hW, heq⟩ := c.source_open
  have hs : IsOpen c.source := by
    rw [heq, Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, hc]
    simpa using hW
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hu)
  let K := Metric.closedBall u (r / 2)
  have hKs : K ⊆ c.source :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact K := isCompact_closedBall _ _
  have him : ContentZero (c.toFun '' K) :=
    (LowerDimensionalImages.compact_local_C1_image hkn K c.toFun hK (by
      intro v hv
      obtain ⟨T, g, hT, hvT, hg, hreg, _⟩ := c.regular v (hKs hv)
      exact ⟨T, g, hT.mem_nhds hvT, hreg.contDiffAt (hT.mem_nhds hvT),
        hg.mono (inter_subset_inter_left _ hKs)⟩)).2
  obtain ⟨T, hT, hTeq⟩ := continuousOn_iff'.mp c.continuous_invFun
    (Metric.ball u (r / 2)) Metric.isOpen_ball
  have hcenter : c.toFun u ∈ T := by
    have hh : c.toFun u ∈ c.invFun ⁻¹' Metric.ball u (r / 2) ∩ (M ∩ c.ambient) :=
      ⟨by rw [mem_preimage, c.left_inv u hu]; exact Metric.mem_ball_self (half_pos hr),
        c.map_source hu⟩
    rw [hTeq] at hh
    exact hh.1
  refine ⟨c.ambient ∩ T, c.ambient_open.inter hT,
    ⟨(c.map_source hu).2, hcenter⟩, contentZero_mono ?_ him⟩
  intro x hx
  have hxm : x ∈ M ∩ c.ambient := ⟨hx.1, hx.2.1⟩
  have hxi : x ∈ T ∩ (M ∩ c.ambient) := ⟨hx.2.2, hxm⟩
  rw [← hTeq] at hxi
  exact ⟨c.invFun x, Metric.ball_subset_closedBall hxi.1, c.right_inv x hxm⟩

/-- Compact lower-dimensional boundaryless embedded manifolds have content zero.
Only compactly restricted C¹ charts enter this argument. -/
lemma compact_manifold_contentZero {k n : ℕ} {M : Set (E n)}
    (hM : IsBoundarylessEmbeddedManifold 1 k M) (hK : IsCompact M) (hkn : k < n) :
    ContentZero M := by
  classical
  have hlocal : ∀ x : M, ∃ O : Set (E n), IsOpen O ∧ (x : E n) ∈ O ∧ ContentZero (M ∩ O) := by
    intro x
    obtain ⟨c, u, hc, hu, hcu⟩ := hM.2.2 x x.property
    simpa only [hcu] using chart_local_contentZero c hkn hu hc
  choose O hO hxO hnull using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hO (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩)
  apply compact_null_contentZero M hK
  apply null_mono (T := ⋃ i : s, M ∩ O i.val)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx, hxi⟩
  · exact null_iUnion_countable _ (fun i => contentZero_null (hnull i.val))

/-- Scalar values as one-dimensional Euclidean coordinates. -/
def scalarCoordinate : E 1 ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

@[simp] lemma scalarCoordinate_apply (x : E 1) : scalarCoordinate x = x 0 := rfl

lemma scalar_differential_surjective {n : ℕ} (A : E n →L[ℝ] ℝ) (hA : A ≠ 0) :
    Function.Surjective (scalarCoordinate.symm.toContinuousLinearMap.comp (-A)) := by
  have hex : ∃ v, A v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hA (ContinuousLinearMap.ext hh)
  obtain ⟨v, hv⟩ := hex
  intro y
  refine ⟨(-(scalarCoordinate y) / A v) • v, ?_⟩
  apply scalarCoordinate.injective
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.neg_apply, map_smul, smul_eq_mul, map_neg,
    ContinuousLinearEquiv.apply_symm_apply]
  field_simp

/-- An ambient inverse-function neighborhood with the prescribed final coordinate. -/
structure BoundaryCoordinates {d : ℕ} (D U : Set (E (d+1)))
    (ρ : E (d+1) → ℝ) (p : E (d+1)) where
  X : Set (E (d+1))
  Y : Set (E (d+1))
  F : E (d+1) → E (d+1)
  g : E (d+1) → E (d+1)
  inverse : Specs.D04.C04.InverseFunction.InverseNeighborhood U F p X Y g
  backward_regular : ContDiffOn ℝ 1 g Y
  forward_regular : ContDiffOn ℝ 1 F X
  final_coordinate : ∀ x, F x (Fin.last d) = -ρ x

lemma boundary_coordinates {d : ℕ} {D U : Set (E (d+1))} {ρ : E (d+1) → ℝ}
    (hρ : IsDefiningFunction D U ρ) {p : E (d+1)} (hp : p ∈ frontier D ∩ U) :
    Nonempty (BoundaryCoordinates D U ρ p) := by
  let A := scalarCoordinate.symm.toContinuousLinearMap.comp (-fderiv ℝ ρ p)
  have hA : Function.Surjective A := scalar_differential_surjective _
    (hρ.nonzero p hp.2 ((hρ.zero_level p hp.2).mp hp.1))
  obtain ⟨e, he⟩ := RegularLevels.surjective_splitting (k := d) A hA rfl
  let L : E (d+1) ≃L[ℝ] E d × E 1 := EuclideanSpace.finAddEquivProd
  let P := (ContinuousLinearMap.fst ℝ (E d) (E 1)).comp e.toContinuousLinearMap
  let F : E (d+1) → E (d+1) := fun x => L.symm (P x, scalarCoordinate.symm (-ρ x))
  have hF : ContDiffOn ℝ 1 F U := L.symm.contDiff.comp_contDiffOn
    (P.contDiff.contDiffOn.prodMk
      (scalarCoordinate.symm.contDiff.comp_contDiffOn hρ.regular.neg))
  have hdρ := (hρ.regular.contDiffAt (hρ.isOpen.mem_nhds hp.2)).differentiableAt one_ne_zero
  have hd : HasFDerivAt F (e.trans L.symm).toContinuousLinearMap p := by
    have hh : HasFDerivAt F (L.symm.toContinuousLinearMap.comp
        (P.prod (scalarCoordinate.symm.toContinuousLinearMap.comp (-fderiv ℝ ρ p)))) p :=
      L.symm.hasFDerivAt.comp p (P.hasFDerivAt.prodMk
        (scalarCoordinate.symm.hasFDerivAt.comp p hdρ.hasFDerivAt.neg))
    have heder : L.symm.toContinuousLinearMap.comp
        (P.prod (scalarCoordinate.symm.toContinuousLinearMap.comp (-fderiv ℝ ρ p))) =
        (e.trans L.symm).toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro v
      change L.symm (P v, A v) = L.symm (e v)
      congr 1
      exact Prod.ext rfl (he v).symm
    rwa [heder] at hh
  obtain ⟨X, Y, g, hI, hg⟩ := inverse_neighborhood U F p (e.trans L.symm)
    le_rfl hρ.isOpen hF hp.2 hd.fderiv.symm
  refine ⟨⟨X, Y, F, g, hI, hg, hF.mono hI.2.2.2.2.1, ?_⟩⟩
  intro x
  change (L.symm (P x, scalarCoordinate.symm (-ρ x))) (Fin.last d) = -ρ x
  have hlast : finSumFinEquiv.symm (Fin.last d : Fin (d+1)) = Sum.inr (0 : Fin 1) := by
    apply (Equiv.symm_apply_eq _).mpr
    rfl
  simp [L, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    scalarCoordinate, hlast]

/-- The inverse coordinates restricted to the nonnegative final coordinate. -/
def BoundaryCoordinates.chart {d : ℕ} {D U : Set (E (d+1))}
    {ρ : E (d+1) → ℝ} {p : E (d+1)} (C : BoundaryCoordinates D U ρ p)
    (hD : IsOpen D) (hρ : IsDefiningFunction D U ρ) :
    EmbeddedChart 1 (d+1) (d+1) (closure D) := by
  obtain ⟨hX, hY, hpX, hFpY, hXU, hbij, hgmap, hleft, hright, hDF, hDg, hLip, huniq⟩ := C.inverse
  have hside (x : E (d+1)) (hx : x ∈ C.X) :
      x ∈ closure D ↔ 0 ≤ C.F x (Fin.last d) := by
    rw [C.final_coordinate, neg_nonneg]
    exact closure_iff_nonpos hD hρ (hXU hx)
  have hgdiff (y : E (d+1)) (hy : y ∈ C.Y) :
      ∃ B : E (d+1) ≃L[ℝ] E (d+1),
        HasFDerivAt C.g B.toContinuousLinearMap y := by
    obtain ⟨B, _, hB, _⟩ := hDg y hy
    exact ⟨B.symm, (hasTotalDerivative_iff_hasFDerivAt C.Y _ _ y hY hy).mp hB⟩
  exact {
    half := true
    half_pos := by omega
    source := halfSpace (d+1) ∩ C.Y
    source_open := ⟨C.Y, hY, rfl⟩
    ambient := C.X
    ambient_open := hX
    toFun := C.g
    invFun := C.F
    map_source := by
      intro y hy
      refine ⟨(hside _ (hgmap hy.2)).mpr ?_, hgmap hy.2⟩
      rw [hright hy.2]
      exact hy.1
    map_target := by
      intro x hx
      exact ⟨(hside x hx.2).mp hx.1, hbij.mapsTo hx.2⟩
    left_inv := fun y hy => hright hy.2
    right_inv := fun x hx => hleft hx.2
    continuous_toFun := C.backward_regular.continuousOn.mono inter_subset_right
    continuous_invFun := C.forward_regular.continuousOn.mono inter_subset_right
    regular := by
      intro y hy
      exact ⟨C.Y, C.g, hY, hy.2, fun _ _ => rfl, C.backward_regular,
        fun z hz => by
          obtain ⟨B, hB⟩ := hgdiff z hz
          rw [hB.fderiv]
          exact B.injective⟩
  }

/-- Every interior point has the ordinary identity chart. -/
def interiorChart {n : ℕ} {D : Set (E n)} (hD : IsOpen D) :
    EmbeddedChart 1 n n (closure D) where
  half := false
  half_pos := by simp
  source := D
  source_open := ⟨D, hD, by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := D
  ambient_open := hD
  toFun := id
  invFun := id
  map_source := fun _ hx => ⟨subset_closure hx, hx⟩
  map_target := fun _ hx => hx.2
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  continuous_toFun := continuous_id.continuousOn
  continuous_invFun := continuous_id.continuousOn
  regular := by
    intro u _
    exact ⟨univ, id, isOpen_univ, mem_univ _, fun _ _ => rfl,
      contDiff_id.contDiffOn, fun _ _ => by simpa using Function.injective_id⟩

lemma boundary_chart_center {d : ℕ} {D U : Set (E (d+1))}
    {ρ : E (d+1) → ℝ} {p : E (d+1)}
    (C : BoundaryCoordinates D U ρ p) (hD : IsOpen D)
    (hρ : IsDefiningFunction D U ρ) (hp : p ∈ frontier D ∩ U) :
    CenteredAt (C.chart hD hρ) (C.F p) ∧ C.g (C.F p) = p := by
  have hz : C.F p (Fin.last d) = 0 := by
    rw [C.final_coordinate, (hρ.zero_level p hp.2).mp hp.1, neg_zero]
  refine ⟨⟨⟨hz.ge, C.inverse.2.2.2.1⟩, fun _ => hz⟩, ?_⟩
  exact C.inverse.2.2.2.2.2.2.2.1 C.inverse.2.2.1

theorem closure_manifold : closure_manifoldType := by
  intro n D hD
  refine ⟨ClassicalRegularDomains.closure_compact hD, regularity_one, le_rfl, ?_⟩
  intro x hx
  by_cases hxi : x ∈ D
  · exact ⟨interiorChart hD.isOpen, x, ⟨hxi, by simp [interiorChart]⟩, rfl⟩
  · have hxb : x ∈ frontier D := by
      rw [frontier, hD.isOpen.interior_eq]
      exact ⟨hx, hxi⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by have := hD.dimension; omega)
    obtain ⟨U, ρ, hxU, hρ⟩ := hD.defining x hxb
    obtain ⟨C⟩ := boundary_coordinates hρ ⟨hxb, hxU⟩
    exact ⟨C.chart hD.isOpen hρ, C.F x, (boundary_chart_center C hD.isOpen hρ ⟨hxb, hxU⟩).1,
      (boundary_chart_center C hD.isOpen hρ ⟨hxb, hxU⟩).2⟩

theorem intrinsic_boundary : intrinsic_boundaryType := by
  intro n D hD
  ext x
  constructor
  · intro hx
    have hxK := hx.1
    by_contra hxb
    have hxD : x ∈ D := by
      by_contra hxD
      exact hxb (by rw [frontier, hD.isOpen.interior_eq]; exact ⟨hxK, hxD⟩)
    have he := chart_intrinsicBoundary (interiorChart hD.isOpen) regularity_one le_rfl x hxD
    simpa [interiorChart] using (he.mp hx).1
  · intro hxb
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by have := hD.dimension; omega)
    obtain ⟨U, ρ, hxU, hρ⟩ := hD.defining x hxb
    obtain ⟨C⟩ := boundary_coordinates hρ ⟨hxb, hxU⟩
    have hh := boundary_chart_center C hD.isOpen hρ ⟨hxb, hxU⟩
    exact ⟨frontier_subset_closure hxb, C.chart hD.isOpen hρ, C.F x,
      rfl, hh.1.1, hh.1.2 rfl, hh.2⟩

theorem boundary_manifold : boundary_manifoldType := by
  intro d D hD
  rw [← intrinsic_boundary hD]
  exact intrinsic_boundary_manifold (closure_manifold hD).2

theorem boundary_contentZero : boundary_contentZeroType := by
  intro n D hD
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by have := hD.dimension; omega)
  exact compact_manifold_contentZero (boundary_manifold hD)
    ((ClassicalRegularDomains.closure_compact hD).of_isClosed_subset isClosed_frontier frontier_subset_closure)
    (Nat.lt_succ_self d)

theorem boundary_finite_one : boundary_finite_oneType := by
  intro D hD
  exact compact_zero_manifold_finite 1 (frontier D)
    (boundaryless_iff.mp (boundary_manifold hD)).1
    ((compact_iff_isCompact _).mpr
      ((ClassicalRegularDomains.closure_compact hD).of_isClosed_subset isClosed_frontier frontier_subset_closure))

theorem jordan_domain_and_closure : jordan_domain_and_closureType := by
  intro n D hD
  have hn : 0 < n := hD.dimension
  exact ⟨(JordanRegions.jordan_iff_boundary hn D hD.bounded).mpr (boundary_contentZero hD),
    (JordanRegions.jordan_iff_boundary hn (closure D) hD.bounded.closure).mpr
      (contentZero_mono frontier_closure_subset (boundary_contentZero hD))⟩

/-- The derivative of the prescribed final coordinate, with its sign retained. -/
lemma BoundaryCoordinates.final_derivative {d : ℕ} {D U : Set (E (d+1))}
    {ρ : E (d+1) → ℝ} {p : E (d+1)}
    (C : BoundaryCoordinates D U ρ p) (hρ : IsDefiningFunction D U ρ) (v : E (d+1)) :
    (fderiv ℝ C.F p v) (Fin.last d) = -fderiv ℝ ρ p v := by
  have hdF := (C.forward_regular.contDiffAt
    (C.inverse.1.mem_nhds C.inverse.2.2.1)).differentiableAt one_ne_zero
  have hdρ := (hρ.regular.contDiffAt
    (hρ.isOpen.mem_nhds (C.inverse.2.2.2.2.1 C.inverse.2.2.1))).differentiableAt one_ne_zero
  have h₁ := (EuclideanSpace.proj (Fin.last d) : E (d+1) →L[ℝ] ℝ).hasFDerivAt.comp p hdF.hasFDerivAt
  have h₂ : HasFDerivAt (fun x => C.F x (Fin.last d)) (-fderiv ℝ ρ p) p :=
    hdρ.hasFDerivAt.neg.congr_of_eventuallyEq (Eventually.of_forall C.final_coordinate)
  exact congrArg (fun A : E (d+1) →L[ℝ] ℝ => A v) (h₁.unique h₂)

/-- The chart derivative at its center is the inverse ambient differential. -/
lemma BoundaryCoordinates.center_differential {d : ℕ} {D U : Set (E (d+1))}
    {ρ : E (d+1) → ℝ} {p : E (d+1)}
    (C : BoundaryCoordinates D U ρ p) (hD : IsOpen D)
    (hρ : IsDefiningFunction D U ρ) (hp : p ∈ frontier D ∩ U) :
    ∃ B : E (d+1) ≃L[ℝ] E (d+1),
      B.toContinuousLinearMap = fderiv ℝ C.F p ∧
      chartDifferential (C.chart hD hρ) (C.F p) = B.symm.toContinuousLinearMap := by
  have hcenter := boundary_chart_center C hD hρ hp
  obtain ⟨B, hB, hgd, hgB⟩ := C.inverse.2.2.2.2.2.2.2.2.2.2.1 (C.F p) C.inverse.2.2.2.1
  have hBp : B.toContinuousLinearMap = fderiv ℝ C.F p := by
    simpa only [hcenter.2, Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative] using hB
  have hgd' := (hasTotalDerivative_iff_hasFDerivAt C.Y _ _ _
    C.inverse.2.1 C.inverse.2.2.2.1).mp hgd
  refine ⟨B, hBp, ?_⟩
  have hdiff := chartDifferential_extension (C.chart hD hρ) regularity_one (C.F p)
    hcenter.1.1 C.Y C.g C.inverse.2.1 C.inverse.2.2.2.1
    (fun _ _ => rfl) hgd'.differentiableAt
  exact hdiff.trans hgd'.fderiv

theorem defining_normal_conormal : defining_normal_conormalType := by
  intro d D U ρ hD hρ p hp
  obtain ⟨C⟩ := boundary_coordinates hρ hp
  let c := C.chart hD.isOpen hρ
  let u := C.F p
  have hcenter := boundary_chart_center C hD.isOpen hρ hp
  have hu : u ∈ c.source := hcenter.1.1
  have hb : IsBoundaryParameter c u := ⟨rfl, hcenter.1.2 rfl⟩
  have hcu : c.toFun u = p := hcenter.2
  obtain ⟨B, hB, hcB⟩ := C.center_differential hD.isOpen hρ hp
  change chartDifferential c u = B.symm.toContinuousLinearMap at hcB
  have ht := tangentSpace_chart c regularity_one le_rfl u hu
  rw [hcu] at ht
  have ht' : tangentSpace 1 (d+1) (closure D) p =
      LinearMap.range B.symm.toContinuousLinearMap.toLinearMap :=
    ht.trans (congrArg (fun A : E (d+1) →L[ℝ] E (d+1) => LinearMap.range A.toLinearMap) hcB)
  have htb := tangentSpace_intrinsic_boundary c regularity_one le_rfl rfl u hu hb.2
  rw [hcu, intrinsic_boundary hD] at htb
  have htb' : (tangentSpace 1 d (frontier D) p : Set (E (d+1))) =
      B.symm '' flatBoundary (d+1) :=
    htb.trans (congrArg (fun A : E (d+1) →L[ℝ] E (d+1) => A '' flatBoundary (d+1)) hcB)
  have hnormal := ClassicalRegularDomains.normal_properties hρ hp.2 hp.1
  have hlast (v : E (d+1)) : (B v) (Fin.last d) = -fderiv ℝ ρ p v := by
    change (B.toContinuousLinearMap v) (Fin.last d) = _
    rw [hB]
    exact C.final_derivative hρ v
  have hvel (w : E (d+1)) : fderiv ℝ ρ p (B.symm w) = -w (Fin.last d) := by
    have hh := hlast (B.symm w)
    rw [B.apply_symm_apply] at hh
    linarith
  refine ⟨?_, hnormal.1, ?_, c, u, B (normalFromDefining ρ p), hu, hb, hcu, ?_, ?_⟩
  · change normalFromDefining ρ p ∈ tangentSpace 1 (d+1) (closure D) p
    rw [ht']
    exact ⟨B (normalFromDefining ρ p), B.symm_apply_apply _⟩
  · intro w hw
    have hw' : w ∈ (tangentSpace 1 d (frontier D) p : Set (E (d+1))) := by
      rwa [intrinsic_boundary hD] at hw
    rw [htb'] at hw'
    obtain ⟨v, hv, rfl⟩ := hw'
    apply hnormal.2.1
    rw [hvel]
    exact neg_eq_zero.mpr hv
  · change chartDifferential c u (B (normalFromDefining ρ p)) = _
    rw [hcB]
    exact B.symm_apply_apply _
  · rw [hlast]
    exact neg_neg_of_pos hnormal.2.2.2

theorem outward_normal_conormal : outward_normal_conormalType := by
  intro d D hD p
  obtain ⟨U, ρ, hpU, hρ⟩ := hD.defining p p.property
  rw [ClassicalRegularDomains.outwardNormal_formula hD p hρ hpU]
  exact defining_normal_conormal hD hρ p ⟨p.property, hpU⟩

theorem continuous_integral : continuous_integralType := by
  intro n D hD f hf
  have hn : 0 < n := hD.dimension
  obtain ⟨hJD, hJK⟩ := jordan_domain_and_closure hD
  have hK : IsCompact (closure D) := (closure_manifold hD).1
  letI : CompactSpace (closure D) := isCompact_iff_compactSpace.mp hK
  have hb : JordanRegions.RegionBounded f := by
    obtain ⟨M, hM⟩ := (isCompact_range hf).isBounded.exists_norm_le
    exact ⟨M, fun x => hM _ (mem_range_self x)⟩
  have hiK : JordanRegions.RegionIntegrable f :=
    JordanRegions.integrable_of_null_relative_discontinuities hn hJK f hb (by
      apply null_mono (T := ∅) _ ExceptionalSets.null_empty
      rintro x ⟨hx, hh⟩
      exact False.elim (hh hf.continuousAt))
  let g : D → ℝ := fun x => f ⟨x, subset_closure x.property⟩
  have hiD : JordanRegions.RegionIntegrable g :=
    JordanRegions.integrable_continuous_on_closure hn hJD f hf
  obtain ⟨Q, hQK⟩ := (JordanRegions.encloses_exists_iff_bounded (closure D)).mpr hK.isBounded
  have hQD : JordanRegions.Encloses D Q := by
    simpa only [JordanRegions.Encloses, Specs.D04.C06.JordanRegions.Model.Encloses, closure_closure]
      using hQK
  have hiKQ := ((JordanRegions.integrable_iff_on_enclosing_box f hQK).mp hiK).2
  have heq : ∀ x ∈ Darboux.carrier Q, x ∉ frontier D →
      JordanRegions.zeroExtension f x = JordanRegions.zeroExtension g x := by
    intro x _ hx
    by_cases hxD : x ∈ D
    · simp [JordanRegions.zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
        hxD, subset_closure hxD, g]
    · have hxK : x ∉ closure D := by
        intro hxK
        exact hx (by rw [frontier, hD.isOpen.interior_eq]; exact ⟨hxK, hxD⟩)
      simp [JordanRegions.zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hxD, hxK]
  obtain ⟨hiDQ, he⟩ := ExceptionalSets.modification_contentZero hn hiKQ
    (JordanRegions.zeroExtension_bounded g hiD.1 Q) (boundary_contentZero hD) heq
  refine ⟨hiK, hiD, ?_⟩
  change JordanRegions.regionIntegral f = JordanRegions.regionIntegral g
  rw [JordanRegions.integral_eq_on_enclosing_box f hiK hQK hiKQ,
    JordanRegions.integral_eq_on_enclosing_box g hiD hQD hiDQ]
  exact he.symm

end D04.RegularDomainGeometry
