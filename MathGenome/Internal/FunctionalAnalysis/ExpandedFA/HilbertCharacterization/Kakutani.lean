import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.Kakutani
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.Ellipsoid
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Parallelogram
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum

/-! Kakutani's projection characterization, paper.tex:9266–9290.
Finite-dimensional subspaces are complete even when the ambient space is not.
The converse transports each three-dimensional unit ball to Euclidean
coordinates, applies the geometric gauge parallelogram theorem, and polarizes.
-/
noncomputable section
open Set Metric
open scoped Topology
namespace ExpandedFA.HilbertCharacterization.Kakutani
universe u v

lemma innerProduct_planeProjections {X : Type u} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] : NormOnePlaneProjections X := by
  intro L hL
  let : FiniteDimensional ℝ L := Module.finite_of_finrank_pos (by omega)
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have hLn : L ≠ ⊥ := by intro h; rw [h, finrank_bot] at hL; omega
  refine ⟨L.starProjection, ?_, ?_, L.norm_starProjection hLn⟩
  · ext x
    exact L.starProjection_eq_self_iff.mpr (L.starProjection_apply_mem x)
  · ext x
    constructor
    · rintro ⟨y, rfl⟩; exact L.starProjection_apply_mem y
    · intro hx
      exact ⟨x, L.starProjection_eq_self_iff.mpr hx⟩

theorem two_dimensional_identity : Spec.TwoDimensionalIdentity.{u} := by
  intro X _ _ hX L hL
  let : FiniteDimensional ℝ X := Module.finite_of_finrank_pos (by omega)
  let : Nontrivial X := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have htop : L = ⊤ := Submodule.eq_top_of_finrank_eq (hL.trans hX.symm)
  refine ⟨htop, ?_, ?_, ContinuousLinearMap.norm_id⟩
  · ext x; rfl
  · change LinearMap.range (LinearMap.id : X →ₗ[ℝ] X) = L
    rw [LinearMap.range_id, htop]

lemma two_dimensional_planeProjections {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (hX : Module.finrank ℝ X = 2) : NormOnePlaneProjections X := by
  intro L hL
  obtain ⟨_, hid, hr, hn⟩ := two_dimensional_identity X hX L hL
  exact ⟨ContinuousLinearMap.id ℝ X, hid, hr, hn⟩

theorem two_dimensional_obstruction : Spec.TwoDimensionalObstruction := by
  have hd : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  refine ⟨hd, two_dimensional_planeProjections hd, ?_⟩
  intro h
  have hp := (ExpandedFA.Hilbert.Parallelogram.parallelogram_characterization ℝ (ℝ × ℝ)).mp h
  have hh := hp (1, 0) (0, 1)
  norm_num [Prod.norm_def] at hh

/-- Contractivity, with the algebraic projection data spelled out. -/
def ContractivePlanes (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ L : Submodule ℝ X, Module.finrank ℝ L = 2 →
    ∃ P : X →L[ℝ] X, (∀ x, P x ∈ L) ∧ (∀ x ∈ L, P x = x) ∧
      ∀ x, ‖P x‖ ≤ ‖x‖

lemma contractivePlanes_of_normOne {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (h : NormOnePlaneProjections X) : ContractivePlanes X := by
  intro L hL
  obtain ⟨P, hi, hr, hn⟩ := h L hL
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x; rw [← hr]; exact ⟨x, rfl⟩
  · intro x hx
    rw [← hr] at hx
    obtain ⟨y, rfl⟩ := hx
    exact congrArg (fun T : X →L[ℝ] X => T y) hi
  · intro x
    simpa only [hn, one_mul] using P.le_opNorm x

/-- The gauge commutes with an invertible linear change of coordinates. -/
lemma gauge_image_equiv {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃L[ℝ] Y) (K : Set X) (x : X) :
    gauge (e '' K) (e x) = gauge K x := by
  rw [gauge_def', gauge_def']
  congr 1
  ext r
  change (0 < r ∧ r⁻¹ • e x ∈ e '' K) ↔ (0 < r ∧ r⁻¹ • x ∈ K)
  rw [← e.map_smul]
  exact and_congr_right fun _ => e.injective.mem_set_image

/-- Apply the accepted three-dimensional body theorem in auxiliary Euclidean
coordinates, then identify its gauge with the original norm. -/
lemma three_dimensional_parallelogram {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (hd : Module.finrank ℝ X = 3) (h : ContractivePlanes X) :
    ExpandedFA.Hilbert.Parallelogram.ParallelogramLaw X := by
  let Y := EuclideanSpace ℝ (Fin (Module.finrank ℝ X))
  let e : X ≃L[ℝ] Y := ContinuousLinearEquiv.ofFinrankEq (by simp [Y])
  let K : Set Y := e '' closedBall (0 : X) 1
  have hK : Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup.ProjectionBody K := by
    refine ⟨by simpa [Y] using hd, ?_, ?_⟩
    · refine ⟨(isCompact_closedBall (0 : X) 1).image e.continuous,
        (convex_closedBall (0 : X) 1).linear_image e.toLinearMap, ?_, ?_⟩
      · rintro z ⟨x, hx, rfl⟩
        exact ⟨-x, by simpa only [mem_closedBall_zero_iff, norm_neg] using hx, map_neg e x⟩
      · have hz : (0 : X) ∈ interior (closedBall (0 : X) 1) := by
          rw [interior_closedBall _ one_ne_zero]
          simp
        change (0 : Y) ∈ interior (e.toHomeomorph '' closedBall (0 : X) 1)
        rw [← e.toHomeomorph.image_interior]
        exact ⟨0, hz, map_zero e⟩
    · intro L hL
      let M := L.map e.symm.toLinearMap
      have hM : Module.finrank ℝ M = 2 :=
        (e.symm.toLinearEquiv.finrank_map_eq L).trans hL
      obtain ⟨P, hinto, hfix, hnorm⟩ := h M hM
      let R : Y →L[ℝ] Y := e.toContinuousLinearMap.comp (P.comp e.symm.toContinuousLinearMap)
      refine ⟨R, ?_, ?_, ?_⟩
      · intro z
        obtain ⟨w, hw, heq⟩ := hinto (e.symm z)
        change e (P (e.symm z)) ∈ L
        rw [← heq]
        simpa using hw
      · intro z hz
        have hm : e.symm z ∈ M := ⟨z, hz, rfl⟩
        change e (P (e.symm z)) = z
        rw [hfix _ hm, e.apply_symm_apply]
      · rintro z ⟨x, hx, rfl⟩
        refine ⟨P x, ?_, ?_⟩
        · exact (mem_closedBall_zero_iff.mpr ((hnorm x).trans (mem_closedBall_zero_iff.mp hx)))
        · simp [R]
  intro x y
  have hg (z : X) : gauge K (e z) = ‖z‖ := by
    change gauge (e '' closedBall (0 : X) 1) (e z) = ‖z‖
    rw [gauge_image_equiv e, gauge_closedBall zero_le_one, div_one]
  have hp := ExpandedFA.HilbertCharacterization.body_gauge_parallelogram hK (e x) (e y)
  simpa only [← map_add, ← map_sub, hg] using hp

/-- Restrict ambient projections to an arbitrary subspace. The codomain of
its restricted projection is still that subspace because its range is a plane
inside it; no projection onto the restricting subspace is needed. -/
lemma contractivePlanes_submodule {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (h : ContractivePlanes X) (V : Submodule ℝ X) :
    ContractivePlanes V := by
  intro L hL
  let M := L.map V.subtype
  have hM : Module.finrank ℝ M = 2 :=
    (Submodule.finrank_map_subtype_eq V L).trans hL
  obtain ⟨P, hinto, hfix, hnorm⟩ := h M hM
  have hV (x : V) : P (x : X) ∈ V := by
    obtain ⟨z, _, heq⟩ := hinto (x : X)
    exact heq ▸ z.property
  let Q : V →L[ℝ] V := (P.comp V.subtypeL).codRestrict V hV
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨z, hz, heq⟩ := hinto (x : X)
    have hq : Q x = z := Subtype.ext heq.symm
    rw [hq]; exact hz
  · intro x hx
    apply Subtype.ext
    exact hfix (x : X) ⟨x, hx, rfl⟩
  · intro x; exact hnorm (x : X)

/-- Extend a finite-dimensional subspace by a prescribed finite number of
vectors. Cardinal rank is used to cover infinite-dimensional ambient spaces. -/
lemma finite_subspace_extension {X : Type u} [AddCommGroup X] [Module ℝ X]
    (S : Submodule ℝ X) [FiniteDimensional ℝ S] (k : ℕ)
    (hr : ((Module.finrank ℝ S + k : ℕ) : Cardinal) ≤ Module.rank ℝ X) :
    ∃ T : Submodule ℝ X, S ≤ T ∧ FiniteDimensional ℝ T ∧
      Module.finrank ℝ T = Module.finrank ℝ S + k := by
  induction k with
  | zero => exact ⟨S, le_rfl, inferInstance, by omega⟩
  | succ k ih =>
    have hstep : ((Module.finrank ℝ S + k : ℕ) : Cardinal) ≤
        ((Module.finrank ℝ S + (k + 1) : ℕ) : Cardinal) := by
      exact_mod_cast (Nat.le_succ (Module.finrank ℝ S + k))
    have hrk : ((Module.finrank ℝ S + k : ℕ) : Cardinal) ≤ Module.rank ℝ X :=
      hstep.trans hr
    obtain ⟨T, hST, hTf, hdim⟩ := ih hrk
    let : FiniteDimensional ℝ T := hTf
    have hTne : T ≠ ⊤ := by
      intro htop
      have heq : (Module.finrank ℝ T : Cardinal) = Module.rank ℝ X := by
        rw [Module.finrank_eq_rank, htop, rank_top]
      rw [← heq] at hr
      have hh : Module.finrank ℝ S + (k + 1) ≤ Module.finrank ℝ T := by
        exact_mod_cast hr
      omega
    obtain ⟨z, _, hz⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hTne)
    let U := T ⊔ Submodule.span ℝ {z}
    have hUf : FiniteDimensional ℝ U := inferInstance
    have hz0 : z ≠ 0 := fun he => hz (he ▸ T.zero_mem)
    have hdis : T ⊓ Submodule.span ℝ {z} = ⊥ :=
      (Submodule.disjoint_span_singleton_of_notMem hz).eq_bot
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq T (Submodule.span ℝ {z})
    rw [hdis, finrank_bot, add_zero, finrank_span_singleton hz0] at hadd
    exact ⟨U, hST.trans le_sup_left, hUf, by dsimp [U]; omega⟩

lemma exists_three_dimensional_pair {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (hr : (3 : Cardinal) ≤ Module.rank ℝ X) (x y : X) :
    ∃ V : Submodule ℝ X, FiniteDimensional ℝ V ∧ Module.finrank ℝ V = 3 ∧
      x ∈ V ∧ y ∈ V := by
  let S := Submodule.span ℝ ({x, y} : Set X)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (by simp)
  have hS : Module.finrank ℝ S ≤ 2 := by
    have hb := finrank_span_le_ncard (R := ℝ) ({x, y} : Set X) (by simp)
    by_cases he : x = y
    · simpa [S, he] using hb.trans (by simp [he] : ({x, y} : Set X).ncard ≤ 2)
    · simpa [S, Set.ncard_pair he] using hb
  have hnum : Module.finrank ℝ S + (3 - Module.finrank ℝ S) = 3 := by omega
  obtain ⟨V, hSV, hVf, hVd⟩ := finite_subspace_extension S (3 - Module.finrank ℝ S)
    (by simpa only [hnum, Nat.cast_ofNat] using hr)
  exact ⟨V, hVf, hVd.trans hnum, hSV (Submodule.subset_span (by simp)),
    hSV (Submodule.subset_span (by simp))⟩

/-- Every pair lies in a three-dimensional space whose unit body satisfies the
geometric theorem. Hence polarization applies on the original whole space. -/
theorem kakutani_characterization : Spec.Characterization.{u} := by
  intro X _ _ hr
  constructor
  · rintro ⟨p, hp⟩
    cases hp
    exact @innerProduct_planeProjections X _ p
  · intro h
    apply (ExpandedFA.Hilbert.Parallelogram.parallelogram_characterization ℝ X).mpr
    intro x y
    obtain ⟨V, hVf, hVd, hx, hy⟩ := exists_three_dimensional_pair hr x y
    let : FiniteDimensional ℝ V := hVf
    exact three_dimensional_parallelogram hVd
      (contractivePlanes_submodule (contractivePlanes_of_normOne h) V) ⟨x, hx⟩ ⟨y, hy⟩

theorem kakutani_complete : Spec.CompleteConclusion.{u} := by
  intro X _ _ _ hr h
  obtain ⟨p, hp⟩ := (kakutani_characterization X hr).mpr h
  exact ⟨p, hp, inferInstance⟩

end ExpandedFA.HilbertCharacterization.Kakutani
