import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OrderedSpectral.KreinRutmanExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Schauder
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

namespace ExpandedFA.OrderedSpectral.KreinRutmanExistence
open Set Filter
open scoped Topology
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Adding a cone point to an interior cone point stays in the interior. -/
lemma interior_add_mem (P : ConvexCone ℝ X) {x y : X}
    (hx : x ∈ interior (P : Set X)) (hy : y ∈ P) :
    x + y ∈ interior (P : Set X) := by
  have ho : IsOpen ((fun z : X => z + y) '' interior (P : Set X)) :=
    (isOpenMap_add_right y) _ isOpen_interior
  apply interior_mono (s := (fun z : X => z + y) '' interior (P : Set X)) _
    (by rw [ho.interior_eq]; exact ⟨x, hx, rfl⟩)
  rintro _ ⟨z, hz, rfl⟩
  exact P.add_mem (interior_subset hz) hy

lemma pos_smul_interior (P : ConvexCone ℝ X) {x : X} {a : ℝ}
    (ha : 0 < a) (hx : x ∈ interior (P : Set X)) :
    a • x ∈ interior (P : Set X) := by
  have ho : IsOpen ((fun z : X => a • z) '' interior (P : Set X)) :=
    (Homeomorph.smulOfNeZero a ha.ne').isOpenMap _ isOpen_interior
  apply interior_mono (s := (fun z : X => a • z) '' interior (P : Set X)) _
    (by rw [ho.interior_eq]; exact ⟨x, hx, rfl⟩)
  rintro _ ⟨z, hz, rfl⟩
  exact P.smul_mem ha (interior_subset hz)

/-- A proper cone cannot have zero in its interior. -/
lemma zero_not_mem_interior (P : ConvexCone ℝ X) (hproper : (P : Set X) ≠ univ) :
    (0 : X) ∉ interior (P : Set X) := by
  intro h0
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  apply hproper
  apply eq_univ_of_forall
  intro x
  let a : ℝ := δ / (‖x‖ + 1)
  have ha : 0 < a := div_pos hδ (by positivity)
  have hax : a • x ∈ P := by
    apply hb
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < ‖x‖ + 1)).2
    nlinarith
  simpa [smul_smul, ha.ne'] using P.smul_mem (inv_pos.mpr ha) hax

/-- An interior point and its negative cannot both lie in a proper cone. -/
lemma neg_not_mem_of_interior (P : ConvexCone ℝ X) (hproper : (P : Set X) ≠ univ)
    {x : X} (hx : x ∈ interior (P : Set X)) : -x ∉ P := by
  intro hn
  have := interior_add_mem P hx hn
  rw [add_neg_cancel] at this
  exact zero_not_mem_interior P hproper this

/-- Source pointedness is Mathlib salience, not Mathlib `Pointed`. -/
theorem forced_pointedness : Spec.ForcedPointedness.{u} := by
  intro X _ _ P hproper T hT x hx hne hn
  apply neg_not_mem_of_interior P hproper (hT x hx hne)
  simpa using interior_subset (hT (-x) hn (neg_ne_zero.mpr hne))

/-- Nonnegative scalar multiplication, including the zero scalar. -/
lemma nonneg_smul_mem (P : ConvexCone ℝ X) (h0 : (0 : X) ∈ P)
    {a : ℝ} (ha : 0 ≤ a) {x : X} (hx : x ∈ P) : a • x ∈ P := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using h0
  · exact P.smul_mem ha hx

/-- Every ray starting in the interior has a short initial segment in the cone. -/
lemma exists_pos_sub_smul_mem (P : ConvexCone ℝ X) {u : X}
    (hu : u ∈ interior (P : Set X)) (x : X) :
    ∃ t : ℝ, 0 < t ∧ u - t • x ∈ interior (P : Set X) := by
  have hc : Continuous (fun t : ℝ => u - t • x) := by fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), u - t • x ∈ interior (P : Set X) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hu)
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ / 2, by positivity, hb ?_⟩
  change |δ / 2 - 0| < δ
  rw [sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

/-- Properness bounds the parameter on any ray with direction outside the cone. -/
lemma ray_parameters_bdd (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    (u x : X) (hneg : -x ∉ P) :
    BddAbove {t : ℝ | 0 ≤ t ∧ u - t • x ∈ P} := by
  have ht : Tendsto (fun t : ℝ => t⁻¹ • u - x) atTop (𝓝 (-x)) := by
    simpa using ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul_const u).sub
      (tendsto_const_nhds (x := x))
  have he : ∀ᶠ t : ℝ in atTop, t⁻¹ • u - x ∉ P :=
    ht.eventually (hP.isOpen_compl.mem_nhds hneg)
  obtain ⟨b, hb⟩ := eventually_atTop.mp he
  refine ⟨max b 1, ?_⟩
  intro t htP
  apply le_of_not_gt
  intro hlt
  have ht0 : 0 < t := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_right b 1) hlt)
  apply hb t (le_trans (le_max_left b 1) hlt.le)
  simpa [smul_sub, smul_smul, ht0.ne'] using
    P.smul_mem (inv_pos.mpr ht0) htP.2

/-- The maximal parameter is attained and gives a boundary point. -/
lemma exists_boundary_ray (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    {u x : X} (hu : u ∈ interior (P : Set X)) (hneg : -x ∉ P) :
    ∃ s : ℝ, 0 < s ∧ u - s • x ∈ P ∧
      u - s • x ∉ interior (P : Set X) ∧
      ∀ t : ℝ, 0 ≤ t → u - t • x ∈ P → t ≤ s := by
  let A : Set ℝ := {t | 0 ≤ t ∧ u - t • x ∈ P}
  have hAclosed : IsClosed A :=
    isClosed_Ici.inter (hP.preimage (by fun_prop : Continuous (fun t : ℝ => u - t • x)))
  obtain ⟨t, ht, htu⟩ := exists_pos_sub_smul_mem P hu x
  have htA : t ∈ A := ⟨ht.le, interior_subset htu⟩
  have hbdd : BddAbove A := ray_parameters_bdd P hP u x hneg
  have hsA : sSup A ∈ A := hAclosed.csSup_mem ⟨t, htA⟩ hbdd
  have hmax : ∀ t ∈ A, t ≤ sSup A := fun t ht => le_csSup hbdd ht
  refine ⟨sSup A, lt_of_lt_of_le ht (hmax t htA), hsA.2, ?_, ?_⟩
  · intro hi
    obtain ⟨d, hd, hdu⟩ := exists_pos_sub_smul_mem P hi x
    have hmem : sSup A + d ∈ A := by
      refine ⟨by linarith [hsA.1], ?_⟩
      have heq : u - (sSup A + d) • x = u - sSup A • x - d • x := by module
      rw [heq]
      exact interior_subset hdu
    have := hmax _ hmem
    linarith
  · intro t ht htu
    exact hmax t ⟨ht, htu⟩

/-- A nonzero cone eigenvector has positive eigenvalue and lies in the interior. -/
lemma cone_eigenvector_positive (P : ConvexCone ℝ X) (hproper : (P : Set X) ≠ univ)
    (T : X →ₗ[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {x : X} {ν : ℝ} (hx : x ∈ P) (hx0 : x ≠ 0) (he : T x = ν • x) :
    0 < ν ∧ x ∈ interior (P : Set X) := by
  have hi : ν • x ∈ interior (P : Set X) := he ▸ hT x hx hx0
  have hν : 0 < ν := by
    by_contra hn
    have hn : ν ≤ 0 := le_of_not_gt hn
    rcases hn.eq_or_lt with rfl | hn
    · exact zero_not_mem_interior P hproper (by simpa using hi)
    · apply neg_not_mem_of_interior P hproper hi
      simpa using P.smul_mem (neg_pos.mpr hn) hx
  refine ⟨hν, ?_⟩
  simpa [smul_smul, hν.ne'] using pos_smul_interior P (inv_pos.mpr hν) hi

/-- A boundary comparison between distinct cone eigenvectors gives a strict
comparison of their eigenvalues. -/
lemma eigenvalue_lt_of_not_proportional (P : ConvexCone ℝ X)
    (hP : IsClosed (P : Set X)) (hproper : (P : Set X) ≠ univ)
    (T : X →ₗ[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {u x : X} {μ ν : ℝ} (hμ : 0 < μ)
    (hu : u ∈ interior (P : Set X)) (hx : x ∈ interior (P : Set X))
    (heu : T u = μ • u) (hex : T x = ν • x)
    (hneq : ¬ ∃ a : ℝ, 0 < a ∧ x = a • u) : ν < μ := by
  obtain ⟨s, hs, hy, hboundary, _⟩ :=
    exists_boundary_ray P hP hu (neg_not_mem_of_interior P hproper hx)
  have hy0 : u - s • x ≠ 0 := by
    intro hzero
    apply hneq
    refine ⟨s⁻¹, inv_pos.mpr hs, ?_⟩
    have hu_eq : u = s • x := sub_eq_zero.mp hzero
    simp [hu_eq, smul_smul, hs.ne']
  by_contra hn
  have hle : μ ≤ ν := le_of_not_gt hn
  have h0 : (0 : X) ∈ P :=
    ConvexCone.Pointed.of_nonempty_of_isClosed ⟨u, interior_subset hu⟩ hP
  have hadd : (s * (ν - μ)) • x ∈ P :=
    nonneg_smul_mem P h0 (mul_nonneg hs.le (sub_nonneg.mpr hle)) (interior_subset hx)
  have hi := interior_add_mem P (hT _ hy hy0) hadd
  have heq : T (u - s • x) + (s * (ν - μ)) • x = μ • (u - s • x) := by
    rw [map_sub, map_smul, heu, hex]
    module
  rw [heq] at hi
  apply hboundary
  simpa [smul_smul, hμ.ne'] using pos_smul_interior P (inv_pos.mpr hμ) hi

/-- Uniqueness includes arbitrary competing real eigenvalues. -/
theorem cone_eigenvector_uniqueness : Spec.ConeEigenvectorUniqueness.{u} := by
  intro X _ _ P hP hproper T hT μ u hμ hu hu0 heu ν x hx hx0 hex
  obtain ⟨hν, hxi⟩ := cone_eigenvector_positive P hproper T hT hx hx0 hex
  have hprop : ∃ a : ℝ, 0 < a ∧ x = a • u := by
    by_contra hn
    have hlt := eigenvalue_lt_of_not_proportional P hP hproper T hT hμ hu hxi heu hex hn
    have hn' : ¬ ∃ a : ℝ, 0 < a ∧ u = a • x := by
      rintro ⟨a, ha, he⟩
      apply hn
      refine ⟨a⁻¹, inv_pos.mpr ha, ?_⟩
      simp [he, smul_smul, ha.ne']
    have hgt := eigenvalue_lt_of_not_proportional P hP hproper T hT hν hxi hu hex heu hn'
    linarith
  obtain ⟨a, ha, hax⟩ := hprop
  refine ⟨?_, a, ha, hax⟩
  have he : ν • x = μ • x := by rw [← hex, hax, map_smul, heu]; module
  exact (smul_left_injective ℝ hx0) he

/-- A compact-range self-map of a closed convex set has a fixed point. The
closed convex hull of its compact range closure is compact in a Banach space. -/
lemma compact_range_fixed_point [CompleteSpace X] (D : Set X)
    (hne : D.Nonempty) (hclosed : IsClosed D) (hconvex : Convex ℝ D)
    (f : D → D) (hf : Continuous f)
    (hcompact : IsCompact (closure (range (fun x : D => (f x : X))))) :
    ∃ x : D, f x = x := by
  let Q : Set X := closure (range (fun x : D => (f x : X)))
  let K : Set X := closure (convexHull ℝ Q)
  have hQD : Q ⊆ D := hclosed.closure_subset_iff.mpr (by
    rintro _ ⟨x, rfl⟩; exact (f x).property)
  have hKD : K ⊆ D := hclosed.closure_subset_iff.mpr (convexHull_min hQD hconvex)
  have hQK : Q ⊆ K := (subset_convexHull ℝ Q).trans subset_closure
  have hKcompact : IsCompact K :=
    isCompact_iff_totallyBounded_isComplete.mpr
      ⟨hcompact.totallyBounded.convexHull.closure, isClosed_closure.isComplete⟩
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨f ⟨x, hx⟩, hQK (subset_closure (mem_range_self _))⟩
  let i : K → D := fun x => ⟨x.val, hKD x.property⟩
  let g : K → K := fun x => ⟨f (i x), hQK (subset_closure (mem_range_self _))⟩
  have hg : Continuous g :=
    ((continuous_subtype_val.comp hf).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  obtain ⟨x, hx⟩ := P1.C24Schauder.schauder X K hKne hKcompact
    ((convex_convexHull ℝ Q).closure) g hg
  have hxv : (g x : X) = (x : X) := congrArg (fun z : K => (z : X)) hx
  exact ⟨i x, Subtype.ext hxv⟩

lemma positive_map_mem (P : ConvexCone ℝ X) (h0 : (0 : X) ∈ P)
    (T : X →ₗ[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {x : X} (hx : x ∈ P) : T x ∈ P := by
  by_cases hx0 : x = 0
  · simpa [hx0] using h0
  · exact interior_subset (hT x hx hx0)

/-- A uniform positive lower bound for the perturbed eigenvalues. The proof
uses a maximal ray parameter and never compares order bounds with norm bounds. -/
lemma perturbed_eigenvalue_lower_bound (P : ConvexCone ℝ X)
    (hP : IsClosed (P : Set X)) (hproper : (P : Set X) ≠ univ)
    (T : X →ₗ[ℝ] X)
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {u x : X} {r ε l : ℝ} (hu : u ∈ interior (P : Set X))
    (hTu : T u - r • u ∈ P)
    (hε : 0 < ε) (hl : 0 < l) (hx : x ∈ P)
    (he : T (x + ε • u) = l • x) : r ≤ l := by
  have h0 : (0 : X) ∈ P :=
    ConvexCone.Pointed.of_nonempty_of_isClosed ⟨u, interior_subset hu⟩ hP
  have hzi : x + ε • u ∈ interior (P : Set X) := by
    simpa [add_comm] using interior_add_mem P (pos_smul_interior P hε hu) hx
  have hz0 : x + ε • u ≠ 0 := by
    intro hz; exact zero_not_mem_interior P hproper (hz ▸ hzi)
  have hxi : x ∈ interior (P : Set X) := by
    have hi : l • x ∈ interior (P : Set X) := he ▸ hT _ (interior_subset hzi) hz0
    simpa [smul_smul, hl.ne'] using pos_smul_interior P (inv_pos.mpr hl) hi
  obtain ⟨s, hs, hy, hboundary, _⟩ :=
    exists_boundary_ray P hP hxi (neg_not_mem_of_interior P hproper hu)
  by_contra hn
  have hlt : l < r := lt_of_not_ge hn
  let c : ℝ := (ε + s) * r - l * s
  have hc : 0 < c := by dsimp [c]; nlinarith
  have hi := interior_add_mem P (pos_smul_interior P hc hu)
    (P.add_mem (positive_map_mem P h0 T hT hy)
      (P.smul_mem (by linarith : 0 < ε + s) hTu))
  have heq : c • u + (T (x - s • u) + (ε + s) • (T u - r • u)) =
      l • (x - s • u) := by
    have hTx : T x = l • x - ε • T u := by
      rw [map_add, map_smul] at he
      exact eq_sub_of_add_eq he
    rw [map_sub, map_smul, hTx]
    dsimp [c]
    module
  rw [heq] at hi
  apply hboundary
  simpa [smul_smul, hl.ne'] using pos_smul_interior P (inv_pos.mpr hl) hi

/-- The normalized, positively shifted compact map has a fixed point.
All these fixed points lie in one compact unit-ball image closure. -/
lemma exists_perturbed_eigenvector [CompleteSpace X] (P : ConvexCone ℝ X)
    (hP : IsClosed (P : Set X)) (hproper : (P : Set X) ≠ univ)
    (T : X →ₗ[ℝ] X) (hcont : Continuous T)
    (hcompact : IsCompact (closure (T '' Metric.closedBall (0 : X) 1)))
    (hT : ∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X))
    {u : X} (hu : u ∈ interior (P : Set X)) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : X, x ∈ P ∧ x ∈ closure (T '' Metric.closedBall (0 : X) 1) ∧
      0 < ‖x + ε • u‖ ∧ T (x + ε • u) = ‖x + ε • u‖ • x := by
  have h0 : (0 : X) ∈ P :=
    ConvexCone.Pointed.of_nonempty_of_isClosed ⟨u, interior_subset hu⟩ hP
  have hzi : ∀ x : (P : Set X), (x : X) + ε • u ∈ interior (P : Set X) := by
    intro x
    simpa [add_comm] using interior_add_mem P (pos_smul_interior P hε hu) x.property
  have hz0 : ∀ x : (P : Set X), (x : X) + ε • u ≠ 0 := by
    intro x hz
    exact zero_not_mem_interior P hproper (hz ▸ hzi x)
  have hn : ∀ x : (P : Set X), 0 < ‖(x : X) + ε • u‖ :=
    fun x => norm_pos_iff.mpr (hz0 x)
  let v : ↥(P : Set X) → X := fun x => ‖(x : X) + ε • u‖⁻¹ • ((x : X) + ε • u)
  have hvP : ∀ x, v x ∈ P := fun x =>
    P.smul_mem (inv_pos.mpr (hn x)) (interior_subset (hzi x))
  have hvball : ∀ x, v x ∈ Metric.closedBall (0 : X) 1 := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖‖(x : X) + ε • u‖⁻¹ • ((x : X) + ε • u)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hn x)),
      inv_mul_cancel₀ (hn x).ne']
  let f : ↥(P : Set X) → ↥(P : Set X) := fun x => ⟨T (v x), positive_map_mem P h0 T hT (hvP x)⟩
  have hvcont : Continuous v := by
    have hzcont : Continuous (fun x : (P : Set X) => (x : X) + ε • u) :=
      continuous_subtype_val.add continuous_const
    exact (hzcont.norm.inv₀ (fun x => (hn x).ne')).smul hzcont
  have hf : Continuous f := (hcont.comp hvcont).subtype_mk _
  have hrange : range (fun x : (P : Set X) => (f x : X)) ⊆
      T '' Metric.closedBall (0 : X) 1 := by
    rintro _ ⟨x, rfl⟩
    exact ⟨v x, hvball x, rfl⟩
  have hfcompact : IsCompact (closure (range (fun x : (P : Set X) => (f x : X)))) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono hrange)
  obtain ⟨x, hx⟩ := compact_range_fixed_point (P : Set X)
    ⟨u, interior_subset hu⟩ hP P.convex f hf hfcompact
  have he : T (v x) = (x : X) := congrArg (fun z : (P : Set X) => (z : X)) hx
  refine ⟨x, x.property, ?_, hn x, ?_⟩
  · rw [← he]
    exact subset_closure ⟨v x, hvball x, rfl⟩
  · have hmul := congrArg (fun z : X => ‖(x : X) + ε • u‖ • z) he
    rw [show v x = ‖(x : X) + ε • u‖⁻¹ • ((x : X) + ε • u) from rfl,
      map_smul, smul_smul, mul_inv_cancel₀ (hn x).ne', one_smul] at hmul
    exact hmul

/-- Existence from compact normalized perturbations, with a uniform positive
lower bound obtained by the boundary-ray comparison. -/
theorem positive_eigenpair : Spec.PositiveEigenpair.{u} := by
  intro X _ _ _ P hP hsolid hproper T hcompact hT
  classical
  have hnative : IsCompactOperator T :=
    (Compactness.compact_iff_isCompactOperator T).mp hcompact
  have hcont : Continuous T := hnative.continuous
  obtain ⟨u, hu⟩ := hsolid
  have hu0 : u ≠ 0 := by
    intro he
    exact zero_not_mem_interior P hproper (he ▸ hu)
  obtain ⟨r, hr, hru⟩ := exists_pos_sub_smul_mem P
    (hT u (interior_subset hu) hu0) u
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hεzero : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  choose x hxP hxK hxn hxe using fun n : ℕ =>
    exists_perturbed_eigenvector P hP hproper T hcont hcompact hT hu (ε n) (hεpos n)
  have hrbound : ∀ n, r ≤ ‖x n + ε n • u‖ := fun n =>
    perturbed_eigenvalue_lower_bound P hP hproper T hT hu
      (interior_subset hru) (hεpos n) (hxn n) (hxP n) (hxe n)
  obtain ⟨v, _, φ, hφ, hv⟩ := hcompact.tendsto_subseq hxK
  have hεlim : Tendsto (fun n => ε (φ n)) atTop (𝓝 0) :=
    hεzero.comp hφ.tendsto_atTop
  have hzlim : Tendsto (fun n => x (φ n) + ε (φ n) • u) atTop (𝓝 v) := by
    simpa using hv.add (hεlim.smul_const u)
  have hrv : r ≤ ‖v‖ := ge_of_tendsto hzlim.norm (Eventually.of_forall (fun n => hrbound (φ n)))
  have hμ : 0 < ‖v‖ := lt_of_lt_of_le hr hrv
  have hv0 : v ≠ 0 := norm_pos_iff.mp hμ
  have hvP : v ∈ P := hP.mem_of_tendsto hv (Eventually.of_forall (fun n => hxP (φ n)))
  have he : T v = ‖v‖ • v := by
    apply tendsto_nhds_unique (hcont.continuousAt.tendsto.comp hzlim)
    exact (hzlim.norm.smul hv).congr (fun n => (hxe (φ n)).symm)
  have hvi : v ∈ interior (P : Set X) := by
    have hi : ‖v‖ • v ∈ interior (P : Set X) := he ▸ hT v hvP hv0
    simpa [smul_smul, hμ.ne'] using pos_smul_interior P (inv_pos.mpr hμ) hi
  exact ⟨‖v‖, v, hμ, hvi, hv0, he⟩

/-- Strong Krein--Rutman: the existence and cone uniqueness clauses assigned
here. No order normality or pre-existing pointedness is assumed. -/
theorem existence_and_uniqueness : Spec.ExistenceAndUniqueness.{u} := by
  intro X _ _ _ P hP hsolid hproper T hcompact hT
  obtain ⟨μ, u, hμ, hu, hu0, heu⟩ :=
    positive_eigenpair X P hP hsolid hproper T hcompact hT
  refine ⟨forced_pointedness X P hproper T hT, μ, u, hμ, hu, hu0, heu, ?_⟩
  exact cone_eigenvector_uniqueness X P hP hproper T hT μ u hμ hu hu0 heu

end ExpandedFA.OrderedSpectral.KreinRutmanExistence
