import MathGenome.Internal.LinearPDE.P201Specs.Heat.Harnack
import MathGenome.Internal.LinearPDE.P201.Heat.CubeHarnack
import Mathlib.Topology.Connected.Clopen

/-! Spatial chaining of the one-cube comparison. We use the open-class
characterization of connectedness, and then a finite subcover of the compact
product of the spatial closure with itself to make the constant uniform. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace P201.Heat.Harnack
open P201Specs (Space Domain)
open P201Specs.Heat (SpaceTime IsClassicalCaloricOn)
open P201Specs.Heat.Cube
open P201.Heat.CubeHarnack (isOpen_cube)

private def corner {n : ℕ} (x : Space n) (d : ℝ) : Space n :=
  WithLp.toLp 2 (fun j => x j - d)

private lemma corner_apply {n : ℕ} (x : Space n) (d : ℝ) (j : Fin n) :
    corner x d j = x j - d := rfl

/-- Centered cubes with arbitrarily small closed outer cube. We use the
homeomorphism with the finite product only for this neighborhood construction. -/
private lemma exists_outer_cube {n : ℕ} (Ω : Domain n) {x : Space n}
    (hx : x ∈ (Ω : Set (Space n))) :
    ∃ d : ℝ, 0 < d ∧ closedCube (8*d) (corner x (4*d)) ⊆ (Ω : Set (Space n)) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin n => ℝ)
  have ho : IsOpen (e.symm ⁻¹' (Ω : Set (Space n))) :=
    Ω.isOpen.preimage e.symm.continuous
  have hx' : e x ∈ e.symm ⁻¹' (Ω : Set (Space n)) := by simpa using hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho (e x) hx'
  refine ⟨ε/8, by positivity, ?_⟩
  intro y hy
  have hdist : dist (e y) (e x) ≤ ε/2 := by
    apply (dist_pi_le_iff (by positivity : 0 ≤ ε/2)).mpr
    intro j
    rw [Real.dist_eq, abs_le]
    have hj := hy j
    simp only [corner_apply] at hj
    change -(ε/2) ≤ y j - x j ∧ y j - x j ≤ ε/2
    constructor <;> linarith [hj.1, hj.2]
  have hy' := hball (lt_of_le_of_lt hdist (by linarith))
  simpa using hy'

/-- The three nested cubes and a small ball needed by the upstream estimate. -/
private lemma nested_cubes {n : ℕ} (x : Space n) {d : ℝ} (hd : 0 < d) :
    x ∈ cube (2*d) (corner x d) ∧
    closedCube (2*d) (corner x d) ⊆ cube (4*d) (corner x (2*d)) ∧
    closedCube (4*d) (corner x (2*d)) ⊆ cube (8*d) (corner x (4*d)) ∧
    ∀ r : ℝ, 0 < r → r ≤ d →
      ∀ y ∈ cube (2*d) (corner x d), ball y r ⊆ cube (4*d) (corner x (2*d)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simp only [corner_apply]
    constructor <;> linarith
  · intro y hy j
    have hj := hy j
    simp only [corner_apply] at hj ⊢
    constructor <;> linarith [hj.1, hj.2]
  · intro y hy j
    have hj := hy j
    simp only [corner_apply] at hj ⊢
    constructor <;> linarith [hj.1, hj.2]
  · intro r hr hrd y hy z hz j
    have hj := hy j
    have hcoord : |z j - y j| < r :=
      lt_of_le_of_lt (by simpa only [Real.norm_eq_abs, PiLp.sub_apply] using
        (PiLp.norm_apply_le (z-y) j)) (by simpa only [mem_ball, dist_eq_norm] using hz)
    have hc := abs_lt.mp hcoord
    simp only [corner_apply] at hj ⊢
    constructor <;> linarith [hj.1, hj.2, hc.1, hc.2]

/-- A comparison on two spatial neighborhoods, uniformly over all solutions and
all final cylinder times. Quantifying over positive ordered times makes this
relation transitive by splitting the elapsed time at its midpoint. -/
private def Comparable {n : ℕ} (Ω : Domain n) (x y : Space n) : Prop :=
  ∀ s t : ℝ, 0 < s → s < t →
    ∃ (U W : Set (Space n)) (C : ℝ),
      IsOpen U ∧ IsOpen W ∧ x ∈ U ∧ y ∈ W ∧ 0 < C ∧
      ∀ T : ℝ, t < T → ∀ u : SpaceTime n → ℝ,
        IsClassicalCaloricOn u ((Ω : Set (Space n)) ×ˢ Ioo 0 T) →
        (∀ z ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T, 0 ≤ u z) →
        ∀ a ∈ U, ∀ b ∈ W, u (a,s) ≤ C * u (b,t)

private lemma comparable_trans {n : ℕ} {Ω : Domain n} {x y z : Space n}
    (hxy : Comparable Ω x y) (hyz : Comparable Ω y z) : Comparable Ω x z := by
  intro s t hs hst
  have hsm : s < (s+t)/2 := by linarith
  have hmt : (s+t)/2 < t := by linarith
  obtain ⟨U, W, A, hU, hW, hx, hy, hA, hcompA⟩ := hxy s ((s+t)/2) hs hsm
  obtain ⟨U', W', B, hU', hW', hy', hz, hB, hcompB⟩ :=
    hyz ((s+t)/2) t (by linarith) hmt
  refine ⟨U, W', A*B, hU, hW', hx, hz, mul_pos hA hB, ?_⟩
  intro T htT u hu hun a ha b hb
  calc
    u (a,s) ≤ A * u (y,(s+t)/2) := hcompA T (hmt.trans htT) u hu hun a ha y hy
    _ ≤ A * (B * u (b,t)) := mul_le_mul_of_nonneg_left
      (hcompB T htT u hu hun y hy' b hb) hA.le
    _ = (A*B) * u (b,t) := (mul_assoc _ _ _).symm

private lemma local_comparable {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    {x : Space n} (hx : x ∈ (Ω : Set (Space n))) :
    ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧
      ∀ a ∈ U, ∀ b ∈ U, Comparable Ω a b := by
  obtain ⟨d, hd, houter⟩ := exists_outer_cube Ω hx
  obtain ⟨hxU, hnest₁, hnest₂, hballs⟩ := nested_cubes x hd
  let U := cube (2*d) (corner x d)
  refine ⟨U, isOpen_cube _ _, hxU, ?_⟩
  intro a ha b hb s t hs hst
  let r := min d (min (s/2) (1/2))
  have hr : 0 < r := lt_min hd (lt_min (by linarith) (by norm_num))
  have hrd : r ≤ d := min_le_left _ _
  have hrs : r ≤ s/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r < 1 := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  have hrsq : r^2 < s := by nlinarith
  obtain ⟨C, hC, hcomp⟩ := P201.Heat.CubeHarnack.oneCubeHarnack n hn
    (8*d) (by positivity) (corner x (4*d))
    (4*d) (by positivity) (corner x (2*d))
    (2*d) (by positivity) (corner x d) hnest₁ hnest₂
    r (t-s) hr (by linarith) (hballs r hr hrd)
  refine ⟨U, U, C, isOpen_cube _ _, isOpen_cube _ _, ha, hb, hC, ?_⟩
  intro T htT u hu hun a' ha' b' hb'
  have h := hcomp Ω T (hs.trans (hst.trans htT)) houter
    s t hs hst htT hrsq u hu hun a' ha' b' hb' s le_rfl (by linarith)
  simpa only [show s + (t-s) = t by ring] using h

/-- Connectedness propagates neighborhood comparisons; it does not require
that the connected spatial set itself be open or path connected. -/
private lemma comparable_on_connected {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    {K : Set (Space n)} (hK : IsPreconnected K) (hKΩ : K ⊆ (Ω : Set (Space n)))
    {x y : Space n} (hx : x ∈ K) (hy : y ∈ K) : Comparable Ω x y := by
  apply hK.induction₂' (Comparable Ω) ?_ (fun _ _ _ _ _ _ => comparable_trans) hx hy
  intro a ha
  obtain ⟨U, hU, haU, hlocal⟩ := local_comparable hn Ω (hKΩ ha)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds haU)] with b hb
  exact ⟨hlocal a haU b hb, hlocal b hb a haU⟩

/-- Compactness upgrades the neighborhood comparisons to a single constant
on the compact spatial set, before any cylinder time or solution is selected. -/
private lemma uniform_comparison {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    {K : Set (Space n)} (hconn : IsPreconnected K) (hcompact : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set (Space n)))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, t < T → ∀ u : SpaceTime n → ℝ,
        IsClassicalCaloricOn u ((Ω : Set (Space n)) ×ˢ Ioo 0 T) →
        (∀ z ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T, 0 ≤ u z) →
        ∀ x ∈ K, ∀ y ∈ K, u (x,s) ≤ C * u (y,t) := by
  classical
  have hex := fun p : K ×ˢ K =>
    comparable_on_connected hn Ω hconn hKΩ p.property.1 p.property.2 s t hs hst
  choose U W C hU hW hx hy hC hbound using hex
  have hcover : K ×ˢ K ⊆ ⋃ p : K ×ˢ K, U p ×ˢ W p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, hx ⟨p,hp⟩, hy ⟨p,hp⟩⟩
  obtain ⟨F, hF⟩ := (hcompact.prod hcompact).elim_finite_subcover
    (fun p : K ×ˢ K => U p ×ˢ W p) (fun p => (hU p).prod (hW p)) hcover
  have hsum : 0 ≤ ∑ p ∈ F, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
  refine ⟨1 + ∑ p ∈ F, C p, by linarith, ?_⟩
  intro T htT u hu hun x hxK y hyK
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hF (show (x,y) ∈ K ×ˢ K from ⟨hxK,hyK⟩))
  obtain ⟨hpF, hxy⟩ := mem_iUnion.mp hp
  have hCp : C p ≤ 1 + ∑ p ∈ F, C p := by
    have := Finset.single_le_sum (fun q _ => (hC q).le) hpF
    linarith
  exact (hbound p T htT u hu hun x hxy.1 y hxy.2).trans
    (mul_le_mul_of_nonneg_right hCp (hun (y,t) ⟨hKΩ hyK, hs.trans hst, htT⟩))

/-- The displayed source inequality, including existence of finite real
supremum and infimum. The chosen constant works for every T > t₂. -/
theorem localParabolicHarnack : P201Specs.Heat.Harnack.localParabolicHarnackStatement := by
  intro n hn Ω V hconn hcompact hVΩ t₁ t₂ ht₁ ht₁₂
  obtain ⟨C, hC, hcomp⟩ := uniform_comparison hn Ω hconn.isPreconnected.closure
    hcompact hVΩ ht₁ ht₁₂
  refine ⟨C, hC, ?_⟩
  intro T ht₂T u hu hun
  have hpoint (x : Space n) (hx : x ∈ V) (y : Space n) (hy : y ∈ V) :
      u (x,t₁) ≤ C * u (y,t₂) :=
    hcomp T ht₂T u hu hun x (subset_closure hx) y (subset_closure hy)
  obtain ⟨y₀, hy₀⟩ := hconn.nonempty
  have hne₁ : (((fun x => u (x,t₁)) '' V) : Set ℝ).Nonempty :=
    ⟨u (y₀,t₁), mem_image_of_mem _ hy₀⟩
  have hne₂ : (((fun y => u (y,t₂)) '' V) : Set ℝ).Nonempty :=
    ⟨u (y₀,t₂), mem_image_of_mem _ hy₀⟩
  have hb₁ : BddAbove ((fun x => u (x,t₁)) '' V) := by
    refine ⟨C * u (y₀,t₂), ?_⟩
    rintro v ⟨x,hx,rfl⟩
    exact hpoint x hx y₀ hy₀
  have hb₂ : BddBelow ((fun y => u (y,t₂)) '' V) := by
    refine ⟨0, ?_⟩
    rintro v ⟨y,hy,rfl⟩
    exact hun (y,t₂) ⟨hVΩ (subset_closure hy), ht₁.trans ht₁₂, ht₂T⟩
  refine ⟨hb₁, hb₂, ?_⟩
  apply csSup_le hne₁
  rintro v ⟨x,hx,rfl⟩
  rw [mul_comm C]
  apply (div_le_iff₀ hC).mp
  apply le_csInf hne₂
  rintro v ⟨y,hy,rfl⟩
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hpoint x hx y hy)

end P201.Heat.Harnack
