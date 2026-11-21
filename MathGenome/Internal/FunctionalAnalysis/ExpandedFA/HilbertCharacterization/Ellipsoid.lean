import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.Ellipsoid
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.Meridians
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.HomogeneousPlanarEllipse
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Parallelogram
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
namespace ExpandedFA.HilbertCharacterization
universe u
open Set Metric
open scoped Topology
open Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
open Specs.ExpandedFA.HilbertCharacterization.Ellipsoid

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

lemma body_gauge_mem {K : Set V} (hK : ProjectionBody K) (x : V) :
    x ∈ K ↔ gauge K x ≤ 1 := by
  rw [gauge_le_one_iff_mem_closure hK.2.1.2.1
    (mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2), hK.2.1.1.isClosed.closure_eq]

lemma body_gauge_frontier {K : Set V} (hK : ProjectionBody K) (x : V) :
    x ∈ frontier K ↔ gauge K x = 1 :=
  (gauge_eq_one_iff_mem_frontier hK.2.1.2.1
    (mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2)).symm

/-- The meridian equivalence can be chosen to send any given equatorial
boundary point to any other equatorial boundary point. -/
lemma meridian_equatorial_equiv {K : Set V} (hK : ProjectionBody K)
    {r p q : V} (hr : r ∈ frontier K) {f : V →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K r) (hfr : f r = 1)
    (hfp : f p = 0) (hfq : f q = 0)
    (hp : p ∈ frontier K) (hq : q ∈ frontier K)
    (L M : Submodule ℝ V) (hL : Module.finrank ℝ L = 2)
    (hM : Module.finrank ℝ M = 2)
    (hrL : r ∈ L) (hpL : p ∈ L) (hrM : r ∈ M) (hqM : q ∈ M) :
    ∃ A : L ≃ₗ[ℝ] M, A ⟨p, hpL⟩ = ⟨q, hqM⟩ ∧
      ∀ x : L, (A x : V) ∈ K ↔ (x : V) ∈ K := by
  have hgp := (body_gauge_frontier hK p).mp hp
  have hgq := (body_gauge_frontier hK q).mp hq
  have hpn : p ≠ 0 := by intro h; simp [h] at hgp
  have hqn : q ≠ 0 := by intro h; simp [h] at hgq
  obtain ⟨eL, heL⟩ := exists_meridian_coordinate_equiv hfr hfp hpn L hL hrL hpL
  obtain ⟨eM, heM⟩ := exists_meridian_coordinate_equiv hfr hfq hqn M hM hrM hqM
  let A := eL.symm.trans eM
  have hAe (t : ℝ × ℝ) : A (eL t) = eM t := by simp [A]
  refine ⟨A, ?_, ?_⟩
  · have hp' : eL (1, 0) = ⟨p, hpL⟩ := Subtype.ext (by simpa using heL (1, 0))
    have hq' : eM (1, 0) = ⟨q, hqM⟩ := Subtype.ext (by simpa using heM (1, 0))
    rw [← hp', hAe, hq']
  · intro x
    obtain ⟨t, rfl⟩ := eL.surjective x
    rw [hAe, heM, heL, body_gauge_mem hK, body_gauge_mem hK,
      meridianGauge_coordinates_eq hK hr hf hfr hfp hfq hgp hgq t.1 t.2]

/-- A supporting point with supporting plane parallel to a given central plane. -/
lemma exists_parallel_support {K : Set V} (hK : ProjectionBody K)
    (L : Submodule ℝ V) (hL : Module.finrank ℝ L = 2) :
    ∃ r ∈ frontier K, ∃ f : V →L[ℝ] ℝ,
      f ∈ NormalCone K r ∧ f r = 1 ∧ (∀ x ∈ L, f x = 0) := by
  have hd := L.finrank_add_finrank_orthogonal
  rw [hK.1, hL] at hd
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℝ Lᗮ by omega)
  let g : V →L[ℝ] ℝ := innerSL ℝ (v : V)
  have hgn : g ≠ 0 := by
    intro hg
    have hz := congrArg (fun T : V →L[ℝ] ℝ => T (v : V)) hg
    have hvV : (v : V) ≠ 0 := fun h => hv (Subtype.ext h)
    have : ‖(v : V)‖ ^ 2 = 0 := by simpa [g, real_inner_self_eq_norm_sq] using hz
    exact hvV (norm_eq_zero.mp (sq_eq_zero_iff.mp this))
  obtain ⟨r, hrK, hmax⟩ := hK.2.1.1.exists_isMaxOn
    ⟨0, interior_subset hK.2.1.2.2.2⟩ g.continuous.continuousOn
  have hg : g ∈ NormalCone K r := fun x hx => hmax hx
  have hgr : 0 < g r := normalCone_positive K r hK.2.1.2.2.2 g hg hgn
  have hr : r ∈ frontier K := by
    rw [hK.2.1.1.isClosed.frontier_eq]
    refine ⟨hrK, ?_⟩
    intro hri
    have hloc : IsLocalMax g r := Filter.mem_of_superset
      (mem_interior_iff_mem_nhds.mp hri) (fun x hx => hg x hx)
    have hz := hloc.hasFDerivAt_eq_zero g.hasFDerivAt
    exact hgn hz
  let f : V →L[ℝ] ℝ := (g r)⁻¹ • g
  refine ⟨r, hr, f, ?_, ?_, ?_⟩
  · intro x hx
    exact mul_le_mul_of_nonneg_left (hg x hx) (inv_nonneg.mpr hgr.le)
  · simp [f, hgr.ne']
  · intro x hx
    have ho : inner ℝ x (v : V) = 0 := v.property x hx
    have ho' : inner ℝ (v : V) x = 0 := by rwa [real_inner_comm]
    simp [f, g, ho']

/-- Three meridian equivalences act transitively on the boundary of each
central planar section. -/
lemma section_boundary_transitive {K : Set V} (hK : ProjectionBody K)
    (L : Submodule ℝ V) (hL : Module.finrank ℝ L = 2)
    (p q : L) (hp : (p : V) ∈ frontier K) (hq : (q : V) ∈ frontier K) :
    ∃ A : L ≃ₗ[ℝ] L, A p = q ∧ ∀ x : L, (A x : V) ∈ K ↔ (x : V) ∈ K := by
  obtain ⟨r, hr, f, hf, hfr, hfL⟩ := exists_parallel_support hK L hL
  have hfp := hfL p p.property
  have hfq := hfL q q.property
  have hpn : (p : V) ≠ 0 := by
    intro h
    have hg := (body_gauge_frontier hK p).mp hp
    simp [h] at hg
  have hqn : (q : V) ≠ 0 := by
    intro h
    have hg := (body_gauge_frontier hK q).mp hq
    simp [h] at hg
  let M := Submodule.span ℝ ({r, (p : V)} : Set V)
  let N := Submodule.span ℝ ({r, (q : V)} : Set V)
  have hM : Module.finrank ℝ M = 2 := meridianPlane_finrank hfr hfp hpn
  have hN : Module.finrank ℝ N = 2 := meridianPlane_finrank hfr hfq hqn
  have hrM : r ∈ M := Submodule.subset_span (by simp)
  have hrN : r ∈ N := Submodule.subset_span (by simp)
  have hpM : (p : V) ∈ M := Submodule.subset_span (by simp)
  have hqN : (q : V) ∈ N := Submodule.subset_span (by simp)
  obtain ⟨fp, hfp', hfpp⟩ := exists_normalized_support hK.2.1 hp
  obtain ⟨fq, hfq', hfqq⟩ := exists_normalized_support hK.2.1 hq
  obtain ⟨A, hAp, _, hAK⟩ := meridians_of_normalized_support hK hp hfp' hfpp
    L M hL hM p.property hpM
  obtain ⟨B, hBp, hBK⟩ := meridian_equatorial_equiv hK hr hf hfr hfp hfq
    hp hq M N hM hN hrM hpM hrN hqN
  obtain ⟨C, hCq, _, hCK⟩ := meridians_of_normalized_support hK hq hfq' hfqq
    N L hN hL hqN q.property
  refine ⟨(A.trans B).trans C, ?_, ?_⟩
  · change C (B (A p)) = q
    rw [hAp, hBp, hCq]
  · intro x
    exact (hCK (B (A x))).trans ((hBK (A x)).trans (hAK x))

/-- Boundary points of a central section are boundary points of the body. -/
lemma section_frontier_to_body {K : Set V} (hK : ProjectionBody K)
    (L : Submodule ℝ V) {x : L}
    (hx : x ∈ frontier {y : L | (y : V) ∈ K}) : (x : V) ∈ frontier K := by
  have hc : IsClosed {y : L | (y : V) ∈ K} := hK.2.1.1.isClosed.preimage L.subtypeL.continuous
  rw [hc.frontier_eq] at hx
  rw [hK.2.1.1.isClosed.frontier_eq]
  refine ⟨hx.1, ?_⟩
  intro hi
  apply hx.2
  exact (preimage_interior_subset_interior_preimage L.subtypeL.continuous) hi

/-- In any linear coordinates, each central planar section is an ellipse. -/
lemma central_section_isEllipse {K : Set V} (hK : ProjectionBody K)
    (L : Submodule ℝ V) (hL : Module.finrank ℝ L = 2)
    (e : Plane ≃ₗ[ℝ] L) : IsEllipse {x : Plane | (e x : V) ∈ K} := by
  let D : Set L := {x | (x : V) ∈ K}
  let H := e.toContinuousLinearEquiv.toHomeomorph
  have hD : IsCompact D :=
    (L.subtype.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).isCompact_preimage hK.2.1.1
  have hD0 : (0 : L) ∈ interior D := by
    exact (preimage_interior_subset_interior_preimage L.subtypeL.continuous) hK.2.1.2.2.2
  apply HomogeneousPlanarEllipse.homogeneous_planar_ellipse
  · exact H.isCompact_preimage.mpr hD
  · exact hK.2.1.2.1.linear_preimage (L.subtype.comp e.toLinearMap)
  · intro x hx
    simpa using hK.2.1.2.2.1 (e x) hx
  · refine ⟨0, ?_⟩
    have hh : (0 : Plane) ∈ H ⁻¹' interior D := by simpa [H] using hD0
    rwa [H.preimage_interior] at hh
  · intro p hp q hq
    have hpD : e p ∈ frontier D := by
      have hh : p ∈ H ⁻¹' frontier D := by rwa [H.preimage_frontier]
      exact hh
    have hqD : e q ∈ frontier D := by
      have hh : q ∈ H ⁻¹' frontier D := by rwa [H.preimage_frontier]
      exact hh
    obtain ⟨A, hAp, hAK⟩ := section_boundary_transitive hK L hL (e p) (e q)
      (section_frontier_to_body hK L hpD) (section_frontier_to_body hK L hqD)
    let B := (e.trans A).trans e.symm
    refine ⟨B, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change (e (e.symm (A (e y))) : V) ∈ K
        simpa using (hAK (e y)).mpr hy
      · intro hx
        refine ⟨B.symm x, ?_, B.apply_symm_apply x⟩
        have heq : A (e (B.symm x)) = e x := by simp [B]
        exact (hAK (e (B.symm x))).mp (heq.symm ▸ hx)
    · change e.symm (A (e p)) = q
      rw [hAp, e.symm_apply_apply]

lemma gauge_section_coordinates (K : Set V) (L : Submodule ℝ V)
    (e : Plane ≃ₗ[ℝ] L) (x : Plane) :
    gauge {y : Plane | (e y : V) ∈ K} x = gauge K (e x : V) := by
  simp only [gauge_def', mem_ofPred_eq, map_smul, Submodule.coe_smul_of_tower]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma continuous_planar_quadratic (Q : QuadraticForm ℝ Plane) : Continuous Q := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  let a : Plane := ![1, 0]
  let b : Plane := ![0, 1]
  have hex (x : Plane) : x = x 0 • a + x 1 • b := by
    ext i; fin_cases i <;> simp [a, b]
  have hf (x : Plane) : Q x = (x 0 * x 0) * Q a + (x 1 * x 1) * Q b +
      (x 0 * x 1) * B a b := by
    conv_lhs => rw [hex x, hB]
    simp [QuadraticMap.map_smul, smul_eq_mul, mul_assoc]
    ring
  have heq : (Q : Plane → ℝ) = fun x =>
      (x 0 * x 0) * Q a + (x 1 * x 1) * Q b + (x 0 * x 1) * B a b := funext hf
  rw [heq]
  fun_prop

/-- The positive quadratic form of a section is the square of its gauge,
up to the positive level defining the ellipse. -/
lemma section_quadratic_gauge {K : Set V} (hK : ProjectionBody K)
    (L : Submodule ℝ V) (e : Plane ≃ₗ[ℝ] L)
    (Q : QuadraticForm ℝ Plane) (c : ℝ)
    (hD : {y : Plane | (e y : V) ∈ K} = {y | Q y ≤ c}) :
    ∀ x : Plane, Q x = gauge K (e x : V) ^ 2 * c := by
  intro x
  by_cases hx : x = 0
  · subst x; simp
  let D : Set Plane := {y | (e y : V) ∈ K}
  have hxe : (e x : V) ≠ 0 := by
    intro h
    exact hx (e.injective (Subtype.ext (by simpa using h)))
  have ht := projection_gauge_pos hK hxe
  have hcD : Convex ℝ D := hK.2.1.2.1.linear_preimage (L.subtype.comp e.toLinearMap)
  have h0D : (0 : Plane) ∈ interior D := by
    have hh := preimage_interior_subset_interior_preimage (t := K)
      (L.subtypeL.comp e.toContinuousLinearEquiv.toContinuousLinearMap).continuous
    exact hh (by simpa using hK.2.1.2.2.2)
  let y := (gauge K (e x : V))⁻¹ • x
  have hy : y ∈ frontier D := by
    apply (gauge_eq_one_iff_mem_frontier hcD (mem_interior_iff_mem_nhds.mp h0D)).mp
    rw [gauge_section_coordinates, map_smul, Submodule.coe_smul_of_tower,
      gauge_smul_of_nonneg (inv_nonneg.mpr ht.le)]
    simp [ht.ne']
  have hyc : Q y = c := by
    have hclosed : IsClosed D := by change IsClosed {y : Plane | (e y : V) ∈ K}; rw [hD]; exact isClosed_le (continuous_planar_quadratic Q) continuous_const
    have hle : Q y ≤ c := by have := frontier_subset_closure hy; rwa [hclosed.closure_eq, show D = {y | Q y ≤ c} from hD] at this
    apply le_antisymm hle
    by_contra h
    have hlt : Q y < c := lt_of_not_ge h
    have hopen : IsOpen {z | Q z < c} := isOpen_lt (continuous_planar_quadratic Q) continuous_const
    have hsub : {z | Q z < c} ⊆ D := by change {z | Q z < c} ⊆ {y : Plane | (e y : V) ∈ K}; rw [hD]; exact fun z hz => (show Q z ≤ c from le_of_lt hz)
    exact hy.2 (interior_mono hsub (by rwa [hopen.interior_eq]))
  calc
    Q x = Q (gauge K (e x : V) • y) := by dsimp [y]; rw [smul_inv_smul₀ ht.ne']
    _ = gauge K (e x : V) ^ 2 * c := by rw [QuadraticMap.map_smul, hyc]; simp [pow_two]

/-- Every vector pair is contained in a central plane, including dependent
pairs and zero vectors. -/
lemma exists_central_plane_pair (hd : Module.finrank ℝ V = 3) (x y : V) :
    ∃ L : Submodule ℝ V, Module.finrank ℝ L = 2 ∧ x ∈ L ∧ y ∈ L := by
  classical
  let S := Submodule.span ℝ ({x, y} : Set V)
  have hS : Module.finrank ℝ S ≤ 2 := by
    have hh := finrank_span_finset_le_card (R := ℝ) ({x, y} : Finset V)
    have hc : ({x, y} : Finset V).card ≤ 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)
    have heq : (↑({x, y} : Finset V) : Set V) = {x, y} := by ext z; simp
    change Module.finrank ℝ (Submodule.span ℝ (↑({x, y} : Finset V) : Set V)) ≤ _ at hh
    rw [heq] at hh
    exact hh.trans hc
  have hdim := S.finrank_add_finrank_orthogonal
  rw [hd] at hdim
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℝ Sᗮ by omega)
  let f : V →L[ℝ] ℝ := innerSL ℝ (v : V)
  have hfn : f.toLinearMap ≠ 0 := by
    intro h
    have hz := LinearMap.congr_fun h (v : V)
    have hvV : (v : V) ≠ 0 := fun h => hv (Subtype.ext h)
    have : ‖(v : V)‖ ^ 2 = 0 := by simpa [f, real_inner_self_eq_norm_sq] using hz
    exact hvV (norm_eq_zero.mp (sq_eq_zero_iff.mp this))
  have hfker : Module.finrank ℝ f.ker = 2 := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hfn
    change Module.finrank ℝ f.ker + 1 = Module.finrank ℝ V at hh
    omega
  refine ⟨f.ker, hfker, ?_, ?_⟩
  · change inner ℝ (v : V) x = 0
    rw [real_inner_comm]
    exact v.property x (Submodule.subset_span (by simp))
  · change inner ℝ (v : V) y = 0
    rw [real_inner_comm]
    exact v.property y (Submodule.subset_span (by simp))

/-- The planar ellipses give the parallelogram identity for the original gauge. -/
lemma body_gauge_parallelogram {K : Set V} (hK : ProjectionBody K) (x y : V) :
    gauge K (x + y) ^ 2 + gauge K (x - y) ^ 2 =
      2 * gauge K x ^ 2 + 2 * gauge K y ^ 2 := by
  obtain ⟨L, hL, hxL, hyL⟩ := exists_central_plane_pair hK.1 x y
  let e : Plane ≃ₗ[ℝ] L := LinearEquiv.ofFinrankEq _ _ (by simp [Plane, hL])
  obtain ⟨Q, _hQ, c, hc, hD⟩ := central_section_isEllipse hK L hL e
  let a := e.symm ⟨x, hxL⟩
  let b := e.symm ⟨y, hyL⟩
  have hg := section_quadratic_gauge hK L e Q c hD
  have hqa := hg a
  have hqb := hg b
  have hqab := hg (a + b)
  have hqsub := hg (a - b)
  have hea : (e a : V) = x := by simp [a]
  have heb : (e b : V) = y := by simp [b]
  simp only [map_add, map_sub, Submodule.coe_add, Submodule.coe_sub, hea, heb] at hqab hqsub
  rw [hea] at hqa
  rw [heb] at hqb
  have hpolar := Q.polar_neg_right a b
  simp only [QuadraticMap.polar, sub_eq_add_neg, QuadraticMap.map_neg] at hpolar
  have hid : Q (a + b) + Q (a - b) = 2 * Q a + 2 * Q b := by
    rw [sub_eq_add_neg]
    linarith
  rw [hqa, hqb, hqab, hqsub] at hid
  nlinarith

/-- The three-dimensional body is the unit sublevel of a positive definite
quadratic form. The auxiliary Euclidean norm is never identified with its gauge. -/
theorem three_dimensional_ellipsoid : statement.{u} := by
  intro V _ _ _ K hK
  let G : V → ℝ := gauge K
  have hmem : ∀ x, x ∈ K ↔ G x ≤ 1 := body_gauge_mem hK
  have hpar : ∀ x y, G (x + y) ^ 2 + G (x - y) ^ 2 = 2 * G x ^ 2 + 2 * G y ^ 2 :=
    body_gauge_parallelogram hK
  have hpos : ∀ x, x ≠ 0 → 0 < G x := fun x hx => projection_gauge_pos hK hx
  have hn : K ∈ 𝓝 (0 : V) := mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2
  have hbal : Balanced ℝ K := (balanced_iff_neg_mem hK.2.1.2.1).mpr
    (fun x hx => hK.2.1.2.2.1 x hx)
  have hadd : ∀ x y, G (x + y) ≤ G x + G y :=
    gauge_add_le hK.2.1.2.1 (absorbent_nhds_zero hn)
  have hsmul : ∀ (a : ℝ) x, G (a • x) = ‖a‖ * G x := by
    intro a x
    exact gauge_smul hbal a x
  have hzero : ∀ x, G x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro hx
      by_contra hx0
      exact (hpos x hx0).ne' hx
    · rintro rfl; exact gauge_zero
  let m : Module ℝ V := inferInstance
  letI : Norm V := ⟨G⟩
  let core : NormedSpace.Core ℝ V :=
    { norm_nonneg := gauge_nonneg
      norm_smul := hsmul
      norm_triangle := hadd
      norm_eq_zero_iff := hzero }
  letI : NormedAddCommGroup V := NormedAddCommGroup.ofCore core
  letI : Module ℝ V := m
  letI : NormedSpace ℝ V := NormedSpace.ofCore core
  have hp : ExpandedFA.Hilbert.Parallelogram.ParallelogramLaw V := hpar
  letI := (ExpandedFA.Hilbert.Parallelogram.innerProductSpaceOfParallelogram ℝ V hp).val
  let Q : QuadraticForm ℝ V := LinearMap.BilinMap.toQuadraticMap (innerₗ V)
  have hQ (x : V) : Q x = G x ^ 2 := by
    exact real_inner_self_eq_norm_sq x
  refine ⟨Q, ?_, ?_⟩
  · intro x hx
    rw [hQ]
    exact sq_pos_of_pos (hpos x hx)
  · ext x
    change x ∈ K ↔ Q x ≤ 1
    rw [hmem, hQ]
    have hnon : 0 ≤ G x := gauge_nonneg x
    constructor <;> intro h <;> nlinarith

end ExpandedFA.HilbertCharacterization
