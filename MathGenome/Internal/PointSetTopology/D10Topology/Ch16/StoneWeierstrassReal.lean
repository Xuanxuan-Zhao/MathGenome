import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.StoneWeierstrassReal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch16.ClosedLattice

/-!
Real Stone--Weierstrass (paper.tex, chapter 16).

The two compactness selections below are the finite-max/finite-min argument
of the paper. Only the already proved `uniformClosure_lattice` is used for
the lattice step; no general Stone--Weierstrass density theorem is invoked.
The empty domain is treated before selecting nonempty finite subcovers.
The finite-lattice construction also follows the proof of
`ContinuousMap.sublattice_closure_eq_top` in Mathlib (Kim Morrison and
Heather Macbeth), with the norm estimate recorded directly here.
-/

noncomputable section
open Set
open scoped Topology
universe u

namespace D10Topology.Ch16

/-- Affine interpolation at two points in a unital separating real algebra. -/
theorem two_point_interpolation {X : Type u} [TopologicalSpace X]
    (A : RealFunctionAlgebra X) (hunit : IsUnital A)
    (hsep : SeparatesPoints (A : Set C(X, ℝ)))
    (v : X → ℝ) (x y : X) :
    ∃ h ∈ A, h x = v x ∧ h y = v y := by
  have hc := (unital_iff_contains_constants A).mp hunit
  by_cases hxy : x = y
  · subst y
    exact ⟨ContinuousMap.const X (v x), hc _, rfl, rfl⟩
  obtain ⟨a, ha, hax⟩ := hsep x y hxy
  have hd : a y - a x ≠ 0 := sub_ne_zero.mpr hax.symm
  let c := (v y - v x) / (a y - a x)
  let h := ContinuousMap.const X (v x) + c • (a - ContinuousMap.const X (a x))
  refine ⟨h, A.add_mem (hc _) (A.smul_mem c (A.sub_mem ha (hc _))), ?_, ?_⟩
  · simp [h]
  · change v x + c * (a y - a x) = v y
    dsimp [c]
    rw [div_mul_cancel₀ _ hd]
    ring

/-- A nonempty lattice of continuous real functions with two-point
interpolation gives uniform approximants on a compact space. -/
theorem lattice_uniform_approximation {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (L : Set C(X, ℝ)) (hn : L.Nonempty)
    (hi : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L)
    (hs : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L)
    (hsep : ∀ (v : X → ℝ) (x y : X), ∃ h ∈ L, h x = v x ∧ h y = v y)
    (f : C(X, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ L, ‖f - g‖ < ε := by
  classical
  by_cases hX : Nonempty X
  swap
  · obtain ⟨g, hg⟩ := hn
    refine ⟨g, hg, (ContinuousMap.norm_lt_iff _ hε).mpr ?_⟩
    intro x
    exact False.elim (hX ⟨x⟩)
  choose h hh hx hy using hsep (f : X → ℝ)
  -- For each fixed x, finitely many lower-error patches cover the domain.
  let U : X → X → Set X := fun x y => {z | f z - ε < h x y z}
  have hU : ∀ x y, U x y ∈ 𝓝 y := by
    intro x y
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · change f y - ε < h x y y
      rw [hy]
      exact sub_lt_self _ hε
  let ys : X → Finset X := fun x =>
    (CompactSpace.elim_nhds_subcover (U x) (hU x)).choose
  have hys : ∀ x, ⋃ y ∈ ys x, U x y = Set.univ := fun x =>
    (CompactSpace.elim_nhds_subcover (U x) (hU x)).choose_spec
  have hysn : ∀ x, (ys x).Nonempty := fun x =>
    Set.nonempty_of_union_eq_top_of_nonempty _ _ hX (hys x)
  let g : X → L := fun x =>
    ⟨(ys x).sup' (hysn x) (fun y => h x y),
      Finset.sup'_mem _ hs _ _ _ (fun y _ => hh x y)⟩
  have hlow : ∀ x z, f z - ε < (g x : C(X, ℝ)) z := by
    intro x z
    obtain ⟨y, hym, hzy⟩ := Set.exists_set_mem_of_union_eq_top _ _ (hys x) z
    dsimp [g]
    simp only [ContinuousMap.coe_sup', Finset.sup'_apply, Finset.lt_sup'_iff]
    exact ⟨y, hym, hzy⟩
  have heq : ∀ x, (g x : C(X, ℝ)) x = f x := by
    intro x
    simp [g, hx]
  -- Finitely many upper-error patches now cover the domain.
  let W : X → Set X := fun x => {z | (g x : C(X, ℝ)) z < f z + ε}
  have hW : ∀ x, W x ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · change (g x : C(X, ℝ)) x < f x + ε
      rw [heq]
      exact lt_add_of_pos_right _ hε
  let xs : Finset X := (CompactSpace.elim_nhds_subcover W hW).choose
  have hxs : ⋃ x ∈ xs, W x = Set.univ :=
    (CompactSpace.elim_nhds_subcover W hW).choose_spec
  have hxsn : xs.Nonempty :=
    Set.nonempty_of_union_eq_top_of_nonempty _ _ hX hxs
  let k : L := ⟨xs.inf' hxsn (fun x => (g x : C(X, ℝ))),
    Finset.inf'_mem _ hi _ _ _ (fun x _ => (g x).2)⟩
  refine ⟨k, k.2, ?_⟩
  apply (ContinuousMap.norm_lt_iff _ hε).mpr
  intro z
  change ‖f z - (k : C(X, ℝ)) z‖ < ε
  rw [Real.norm_eq_abs, abs_lt]
  have hup : (k : C(X, ℝ)) z < f z + ε := by
    simp only [k, ContinuousMap.inf'_apply, Finset.inf'_lt_iff]
    exact Set.exists_set_mem_of_union_eq_top _ _ hxs z
  have hlo : f z - ε < (k : C(X, ℝ)) z := by
    simp only [k, ContinuousMap.inf'_apply, Finset.lt_inf'_iff]
    intro x _
    exact hlow x z
  constructor <;> linarith

theorem stone_weierstrass_real_closure :
    Specs.D10Topology.Ch16.StoneWeierstrassReal.stone_weierstrass_real_closure := by
  intro X _ _ _ A hunit hsep
  let L := uniformClosure (A : Set C(X, ℝ))
  have hsub : (A : Set C(X, ℝ)) ⊆ L := by
    dsimp only [L, uniformClosure]
    rw [uniformClosure_eq_norm_closure]
    exact subset_closure
  have hclosed : IsClosed L := by
    dsimp only [L, uniformClosure]
    rw [uniformClosure_eq_norm_closure]
    exact isClosed_closure
  have hn : L.Nonempty := ⟨0, hsub A.zero_mem⟩
  have hi : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L := fun f hf g hg =>
    (uniformClosure_lattice A hunit f g hf hg).2.1
  have hs : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L := fun f hf g hg =>
    (uniformClosure_lattice A hunit f g hf hg).2.2
  have hinterp : ∀ (v : X → ℝ) (x y : X), ∃ h ∈ L, h x = v x ∧ h y = v y := by
    intro v x y
    obtain ⟨h, hh, hx, hy⟩ := two_point_interpolation A hunit hsep v x y
    exact ⟨h, hsub hh, hx, hy⟩
  apply Set.eq_univ_of_forall
  intro f
  change f ∈ L
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, herr⟩ := lattice_uniform_approximation L hn hi hs hinterp f ε hε
  exact ⟨g, hg, by simpa only [dist_eq_norm] using herr⟩

theorem stone_weierstrass_real :
    Specs.D10Topology.Ch16.StoneWeierstrassReal.stone_weierstrass_real := by
  intro X _ _ _ A hunit hsep f ε hε
  have hf : f ∈ uniformClosure (A : Set C(X, ℝ)) := by
    change f ∈ Specs.D10Topology.Ch16.SupNormAlgebras.uniformClosure (A : Set C(X, ℝ))
    rw [stone_weierstrass_real_closure A hunit hsep]
    trivial
  exact (mem_uniformClosure_iff (A : Set C(X, ℝ)) f).mp hf ε hε

end D10Topology.Ch16
