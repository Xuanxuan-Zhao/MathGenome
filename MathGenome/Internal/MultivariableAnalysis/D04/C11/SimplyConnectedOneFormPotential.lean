import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.SimplyConnectedOneFormPotential
import MathGenome.Internal.MultivariableAnalysis.D04.C11.LocalAndStarShapedPotentials
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

noncomputable section
open Set Filter Topology
open scoped unitInterval BigOperators Classical
namespace D04.C11
open D04 D04.C09

abbrev FreeLoopContractions :=
  @Specs.D04.C11.SimplyConnectedOneFormPotential.Model.FreeLoopContractions

/-- A free nullhomotopy of a loop gives a based nullhomotopy. The proof uses
only the boundary square relation in the fundamental groupoid. -/
lemma based_contraction_of_free {X : Type*} [TopologicalSpace X] {a b : X}
    (γ : Path a a)
    (H : (γ : C(I, X)).Homotopy (ContinuousMap.const I b))
    (hloop : ∀ s : I, H (s, 0) = H (s, 1)) :
    γ.Homotopic (Path.refl a) := by
  let c : Path a b := (H.evalAt 0).cast γ.source.symm rfl
  let d : Path a b := (H.evalAt 1).cast γ.target.symm rfl
  have tracks : c = d := by
    ext s
    exact hloop s
  obtain ⟨K⟩ := Path.Homotopic.map_trans_evalAt H Path.id
  have h : (γ.trans d).Homotopic (c.trans (Path.refl b)) := by
    refine ⟨(K.pathCast γ.source.symm rfl).cast ?_ ?_⟩
    · ext t
      rfl
    · ext t
      rfl
  rw [← tracks] at h
  have h' : (γ.trans c).Homotopic c := h.trans ⟨Path.Homotopy.transRefl _⟩
  have he := congrArg
    (fun p : Path.Homotopic.Quotient a b =>
      p.trans (Path.Homotopic.Quotient.mk c.symm))
    (Path.Homotopic.Quotient.eq.mpr h')
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] at he
  exact Path.Homotopic.Quotient.eq.mp he

theorem free_iff_based {n : ℕ} (U : Set (E n)) :
    SimplyConnected U ↔ PathConnected U ∧ FreeLoopContractions U := by
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨hp, fun a γ => ?_⟩
    obtain ⟨H⟩ := hb a γ
    exact ⟨a, H.toHomotopy, fun s => (H.source s).trans (H.target s).symm⟩
  · rintro ⟨hp, hf⟩
    refine ⟨hp, fun a γ => ?_⟩
    obtain ⟨b, H, hloop⟩ := hf a γ
    exact based_contraction_of_free γ H hloop

/-- The proper work integral along a chord. The default branch is irrelevant
whenever the field is continuous on the segment. -/
def chordWork {n : ℕ} (F : E n → E n) (x y : E n) : ℝ :=
  if h : WorkIntegrable (segmentData x y) F then
    workLineIntegral (segmentData x y) F h else 0

lemma chordWork_eq {n : ℕ} (F : E n → E n) (x y : E n)
    (h : WorkIntegrable (segmentData x y) F) :
    chordWork F x y = workLineIntegral (segmentData x y) F h := by
  simp only [chordWork, dite_eq_left h]

lemma chordWork_potential {n : ℕ} {V : Set (E n)} {F : E n → E n}
    {f : E n → ℝ} (hV : IsOpen V) (hf : IsPotential V F f)
    (hconv : Convex ℝ V) {x y : E n} (hx : x ∈ V) (hy : y ∈ V) :
    chordWork F x y = f y - f x := by
  have hseg := segmentPath_inside (hconv.segment_subset hx hy)
  have hi := work_integrable_in_domain V F (segmentPath x y) (segmentData x y)
    (potential_continuous_field hf) hseg
  rw [chordWork_eq F x y hi, potential_integral V F f hV hf _ _ hseg hi]
  simp [segmentPath]

lemma chordWork_self {n : ℕ} (F : E n → E n) (x : E n) :
    chordWork F x x = 0 := by
  obtain ⟨hi,he⟩ := D04.C09.PathAlgebra.pieceIntegral_zero (segmentData x x)
    (fun z v => inner ℝ (F z) v) (by intros; simp [segmentData])
  rw [chordWork_eq F x x hi]
  exact he

/-- Four chords in one convex potential neighborhood have zero circulation. -/
lemma chordWork_rectangle {n : ℕ} {V : Set (E n)} {F : E n → E n}
    (hV : IsOpen V) (hp : HasPotential V F) (hc : Convex ℝ V)
    {x y z w : E n} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V) (hw : w ∈ V) :
    chordWork F x y + chordWork F y z = chordWork F x w + chordWork F w z := by
  obtain ⟨f, hf⟩ := hp
  rw [chordWork_potential hV hf hc hx hy, chordWork_potential hV hf hc hy hz,
    chordWork_potential hV hf hc hx hw, chordWork_potential hV hf hc hw hz]
  ring

/-- Algebraic cancellation of the internal edges of a finite rectangular grid. -/
lemma grid_boundary_sum {N M : ℕ} (h : ℕ → ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (hc : ∀ i < N, ∀ j < M, h i j + v i (j+1) = v i j + h (i+1) j) :
    (∑ j ∈ Finset.range M, h 0 j) + (∑ i ∈ Finset.range N, v i M) =
      (∑ i ∈ Finset.range N, v i 0) + (∑ j ∈ Finset.range M, h N j) := by
  have row (i : ℕ) (hi : i < N) :
      (∑ j ∈ Finset.range M, h i j) + v i M =
        v i 0 + ∑ j ∈ Finset.range M, h (i+1) j := by
    have step : ∀ m ≤ M,
        (∑ j ∈ Finset.range m, h i j) + v i m =
          v i 0 + ∑ j ∈ Finset.range m, h (i+1) j := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have he := hc i hi m (by omega)
        have hp := ih (by omega)
        linarith
    exact step M le_rfl
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hr := row N (by omega)
    have hi := ih (fun i hi j hj => hc i (by omega) j hj) (fun i hi => row i (by omega))
    linarith

/-- A continuous contraction supplies a finite polygonal grid with vanishing
bottom circulation. No differentiability of the contraction occurs here. -/
lemma contraction_chord_grid {n : ℕ} {U : Set (E n)} {F : E n → E n}
    (hloc : ∀ x ∈ U, ∃ r > 0, HasPotential (Metric.ball x r) F)
    (H : C(I × I, U))
    (hend : ∀ t : I, H (1,t) = H (1,0))
    (hloop : ∀ s : I, H (s,0) = H (s,1)) :
    ∃ (t : ℕ → I) (N : ℕ), t 0 = 0 ∧ Monotone t ∧ t N = 1 ∧
      (∀ j, ∃ (V : Set (E n)), IsOpen V ∧ Convex ℝ V ∧ HasPotential V F ∧
        ∀ u ∈ Icc (t j) (t (j+1)), (H (0,u) : E n) ∈ V) ∧
      (∑ j ∈ Finset.range N,
        chordWork F (H (0,t j)) (H (0,t (j+1)))) = 0 := by
  choose r hr hp using fun x : U => hloc x x.2
  let c (x : U) : Set (I × I) :=
    (fun p => (H p : E n)) ⁻¹' Metric.ball x (r x)
  have hc : ∀ x, IsOpen (c x) := fun x =>
    Metric.isOpen_ball.preimage (continuous_subtype_val.comp H.continuous)
  have hcover : univ ⊆ ⋃ x, c x := by
    intro p _
    exact mem_iUnion.mpr ⟨H p, Metric.mem_ball_self (hr _)⟩
  obtain ⟨t, hzero, hm, ⟨N,hN⟩, hcell⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc hcover
  have hlast := hN N le_rfl
  have cell (i j : ℕ) :
      chordWork F (H (t i,t j)) (H (t i,t (j+1))) +
          chordWork F (H (t i,t (j+1))) (H (t (i+1),t (j+1))) =
        chordWork F (H (t i,t j)) (H (t (i+1),t j)) +
          chordWork F (H (t (i+1),t j)) (H (t (i+1),t (j+1))) := by
    obtain ⟨x, hx⟩ := hcell i j
    have hi := hm (Nat.le_succ i)
    have hj := hm (Nat.le_succ j)
    exact chordWork_rectangle Metric.isOpen_ball (hp x) (convex_ball _ _)
      (hx ⟨⟨le_rfl,hi⟩,⟨le_rfl,hj⟩⟩)
      (hx ⟨⟨le_rfl,hi⟩,⟨hj,le_rfl⟩⟩)
      (hx ⟨⟨hi,le_rfl⟩,⟨hj,le_rfl⟩⟩)
      (hx ⟨⟨hi,le_rfl⟩,⟨le_rfl,hj⟩⟩)
  have he := grid_boundary_sum (N := N) (M := N)
    (fun i j => chordWork F (H (t i,t j)) (H (t i,t (j+1))))
    (fun i j => chordWork F (H (t i,t j)) (H (t (i+1),t j)))
    (fun i _ j _ => cell i j)
  simp only [hzero, hlast] at he
  have htop : (∑ j ∈ Finset.range N,
      chordWork F (H (1,t j)) (H (1,t (j+1)))) = 0 := by
    simp only [hend, chordWork_self, Finset.sum_const_zero]
  have hsides : (∑ i ∈ Finset.range N,
      chordWork F (H (t i,1)) (H (t (i+1),1))) =
      (∑ i ∈ Finset.range N, chordWork F (H (t i,0)) (H (t (i+1),0))) := by
    simp only [← hloop]
  refine ⟨t,N,hzero,hm,hlast,?_,?main⟩
  · intro j
    obtain ⟨x,hx⟩ := hcell 0 j
    refine ⟨Metric.ball x (r x),Metric.isOpen_ball,convex_ball _ _,hp x,?_⟩
    intro u hu
    exact hx ⟨⟨by rw [hzero], by exact bot_le⟩,hu⟩
  case main => linarith

open SingleVariableAnalysis.Riemann

/-- FTC on a subarc contained in one potential neighborhood, with the actual
one-sided derivatives on the closed interval. -/
lemma smooth_work_potential {n : ℕ} {γ v : ℝ → E n} {l u : ℝ}
    {V : Set (E n)} {F : E n → E n} {f : E n → ℝ}
    (hlu : l ≤ u) (hs : C1Piece γ v l u) (hV : IsOpen V)
    (hf : IsPotential V F f) (hγ : ∀ t ∈ Icc l u, γ t ∈ V)
    (hi : RealIntegrable (fun t => inner ℝ (F (γ t)) (v t)) l u) :
    realIntegral _ hi = f (γ u) - f (γ l) := by
  have hd (t : ℝ) (ht : t ∈ Icc l u) :
      HasDerivWithinAt (fun s => f (γ s)) (inner ℝ (F (γ t)) (v t)) (Icc l u) t :=
    (potential_hasFDerivAt hV hf (hγ t ht)).comp_hasDerivWithinAt t (hs.2 t ht)
  apply real_ftc_second _ _ l u hlu (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) hi

/-- Splitting a proper integral at finitely many monotone nodes permits
repeated nodes. This avoids imposing artificial regularity at path joins. -/
lemma realIntegral_monotone_sum {g : ℝ → ℝ} {a b : ℝ}
    (hg : RealIntegrable g a b) (r : ℕ → ℝ) (N : ℕ)
    (hr : ∀ k, r k ∈ Icc a b) (hm : Monotone r) (hzero : r 0 = a) (hlast : r N = b) :
    realIntegral g hg = ∑ k ∈ Finset.range N,
      realIntegral g (hg.subinterval (hr k).1 (hm (Nat.le_succ k)) (hr (k+1)).2) := by
  have step (m : ℕ) :
      realIntegral g (hg.subinterval le_rfl (hr m).1 (hr m).2) =
        ∑ k ∈ Finset.range m,
          realIntegral g (hg.subinterval (hr k).1 (hm (Nat.le_succ k)) (hr (k+1)).2) := by
    induction m with
    | zero => simp only [hzero, realIntegral_degenerate, Finset.sum_range_zero]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact (real_split g (hr m).1 (hm (Nat.le_succ m))
        (hg.subinterval le_rfl (hr (m+1)).1 (hr (m+1)).2).bounded).2 _ _ _
  simpa only [hlast] using step N

/-- Clamp a parameter to a closed smooth piece. -/
def clipParameter (l u t : ℝ) : ℝ := max l (min u t)

lemma clipParameter_mem {l u : ℝ} (h : l ≤ u) (t : ℝ) :
    clipParameter l u t ∈ Icc l u :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

lemma clipParameter_mono (l u : ℝ) : Monotone (clipParameter l u) :=
  fun _ _ h => max_le_max_left _ (min_le_min_left _ h)

lemma clipParameter_eq_left {l u t : ℝ} (ht : t ≤ l) : clipParameter l u t = l :=
  max_eq_left ((min_le_right _ _).trans ht)

lemma clipParameter_eq_right {l u t : ℝ} (hlu : l ≤ u) (ht : u ≤ t) :
    clipParameter l u t = u := by
  rw [clipParameter, min_eq_left ht, max_eq_right hlu]

lemma clipParameter_difference (g : ℝ → ℝ) {l u x y : ℝ} (hlu : l ≤ u) :
    g (clipParameter l u y) - g (clipParameter l u x) =
      (g (min u y) - g (min l y)) - (g (min u x) - g (min l x)) := by
  have he (t : ℝ) : g (clipParameter l u t) = g (min u t) - g (min l t) + g l := by
    by_cases ht : t ≤ l
    · rw [clipParameter_eq_left ht, min_eq_right (ht.trans hlu), min_eq_right ht]
      ring
    · have hl := le_of_not_ge ht
      rw [clipParameter, min_eq_left hl, max_eq_right (le_min hlu hl)]
      ring
  rw [he, he]
  ring

lemma sum_clipped_differences (g : ℝ → ℝ) {a b : ℝ}
    (P : Partition a b) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (∑ i : Fin P.n,
      (g (clipParameter (P.point i.castSucc) (P.point i.succ) y) -
        g (clipParameter (P.point i.castSucc) (P.point i.succ) x))) = g y - g x := by
  simp_rw [clipParameter_difference g (P.strictMono (Fin.castSucc_lt_succ)).le]
  rw [Finset.sum_sub_distrib,
    sum_cell_differences (fun i => g (min (P.point i) y)),
    sum_cell_differences (fun i => g (min (P.point i) x))]
  simp only [P.first, P.last, min_eq_right hx.2, min_eq_right hy.2,
    min_eq_left hx.1, min_eq_left hy.1]
  ring

/-- A cell of the intersection of two interval partitions lies in both.
When the intersection is a point it contributes zero separately. -/
lemma clipped_cell_subset {l u x y : ℝ} (hlu : l ≤ u) (hxy : x ≤ y)
    (hne : clipParameter l u x < clipParameter l u y) :
    Icc (clipParameter l u x) (clipParameter l u y) ⊆ Icc x y := by
  have hx : x ≤ u := by
    by_contra h
    have hx' := clipParameter_eq_right hlu (le_of_not_ge h)
    have hy' := clipParameter_eq_right hlu ((le_of_not_ge h).trans hxy)
    rw [hx',hy'] at hne
    exact lt_irrefl _ hne
  have hy : l ≤ y := by
    by_contra h
    have hy' := clipParameter_eq_left (u := u) (le_of_not_ge h)
    have hx' := clipParameter_eq_left (u := u) (hxy.trans (le_of_not_ge h))
    rw [hx',hy'] at hne
    exact lt_irrefl _ hne
  intro t ht
  exact ⟨(le_max_of_le_right (by rw [min_eq_right hx])).trans ht.1,
    ht.2.trans (max_le hy (min_le_right _ _))⟩

/-- A subdivision whose subarcs lie in convex potential neighborhoods may be
replaced by its chords, for the original proper Riemann work integral.
The monotone subdivision may have repeated nodes. -/
lemma work_eq_chord_sum {n : ℕ} {a b : ℝ} (γ : IntervalPath n a b)
    (d : PiecewiseC1Data γ) (F : E n → E n) (hi : WorkIntegrable d F)
    (r : ℕ → ℝ) (N : ℕ) (hr : ∀ k, r k ∈ Icc a b) (hm : Monotone r)
    (hzero : r 0 = a) (hlast : r N = b)
    (hlocal : ∀ k < N, ∃ (V : Set (E n)), IsOpen V ∧ Convex ℝ V ∧ HasPotential V F ∧
      ∀ t ∈ Icc (r k) (r (k+1)), γ t ∈ V) :
    workLineIntegral d F hi =
      ∑ k ∈ Finset.range N, chordWork F (γ (r k)) (γ (r (k+1))) := by
  let c (i : Fin d.partition.n) (k : ℕ) :=
    clipParameter (d.partition.point i.castSucc) (d.partition.point i.succ) (r k)
  have cmem (i : Fin d.partition.n) (k : ℕ) : c i k ∈ cell d.partition i :=
    clipParameter_mem (d.partition.strictMono (Fin.castSucc_lt_succ)).le _
  have cmono (i : Fin d.partition.n) : Monotone (c i) :=
    (clipParameter_mono _ _).comp hm
  have czero (i : Fin d.partition.n) : c i 0 = d.partition.point i.castSucc := by
    dsimp only [c]
    rw [hzero]
    exact clipParameter_eq_left (graph_point_mem d.partition i.castSucc).1
  have clast (i : Fin d.partition.n) : c i N = d.partition.point i.succ := by
    dsimp only [c]
    rw [hlast]
    exact clipParameter_eq_right (d.partition.strictMono (Fin.castSucc_lt_succ)).le
      (graph_point_mem d.partition i.succ).2
  have hii (i : Fin d.partition.n) :
      RealIntegrable (fun t => inner ℝ (F (γ t)) (d.velocity i t))
        (d.partition.point i.castSucc) (d.partition.point i.succ) := hi i
  let hv (i : Fin d.partition.n) (k : ℕ) :=
    (hii i).subinterval (cmem i k).1 (cmono i (Nat.le_succ k)) (cmem i (k+1)).2
  have split (i : Fin d.partition.n) : realIntegral _ (hi i) =
      ∑ k ∈ Finset.range N, realIntegral _ (hv i k) :=
    realIntegral_monotone_sum (hi i) (c i) N (cmem i) (cmono i) (czero i) (clast i)
  change (∑ i, realIntegral _ (hi i)) = _
  simp_rw [split]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨V,hV,hconv,⟨f,hf⟩,htrace⟩ := hlocal k (Finset.mem_range.mp hk)
  have he (i : Fin d.partition.n) :
      realIntegral _ (hv i k) = f (γ (c i (k+1))) - f (γ (c i k)) := by
    by_cases hn : c i k = c i (k+1)
    · simp only [← hn, realIntegral_degenerate, sub_self]
    · have hlt := lt_of_le_of_ne (cmono i (Nat.le_succ k)) hn
      have hsub := clipped_cell_subset
        (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
        (hm (Nat.le_succ k)) hlt
      have hs : Icc (c i k) (c i (k+1)) ⊆ cell d.partition i :=
        Icc_subset_Icc (cmem i k).1 (cmem i (k+1)).2
      exact smooth_work_potential hlt.le
        ⟨(d.smooth i).1.mono hs, fun t ht => ((d.smooth i).2 t (hs ht)).mono hs⟩
        hV hf (fun t ht => htrace t (hsub ht)) (hv i k)
  simp_rw [he]
  rw [sum_clipped_differences (fun t => f (γ t)) d.partition (hr k) (hr (k+1))]
  exact (chordWork_potential hV hf hconv
    (htrace _ ⟨le_rfl,hm (Nat.le_succ k)⟩)
    (htrace _ ⟨hm (Nat.le_succ k),le_rfl⟩)).symm

/-- The period conclusion uses a continuous free contraction, including moving
basepoints. All analytic operations take place on the path and on chords. -/
theorem simply_connected_zeroPeriods {n : ℕ} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (_hc : IsPreconnected U) (hfree : FreeLoopContractions U)
    (hF : CrOn 1 U F) (hs : SymmetricPartials U F) : ZeroPeriods U F := by
  intro a b γ d hγ hclosed hi
  by_cases hab : a = b
  · subst b
    exact pieceIntegral_degenerate d _ hi
  have hab' : a < b := lt_of_le_of_ne γ.ordered hab
  have hpos : 0 < b-a := sub_pos.mpr hab'
  let u (t : I) : ℝ := a+(b-a)*(t:ℝ)
  have hu (t : I) : u t ∈ Icc a b := by
    dsimp only [u]
    constructor <;> nlinarith [t.2.1,t.2.2]
  have hum : Monotone u := by
    intro s t hst
    dsimp only [u]
    have hst' : (s:ℝ) ≤ (t:ℝ) := hst
    nlinarith
  let base : U := ⟨γ a,hγ ⟨a,⟨le_rfl,γ.ordered⟩,rfl⟩⟩
  let p : Path base base := {
    toFun := fun t => ⟨γ (u t),hγ ⟨u t,hu t,rfl⟩⟩
    continuous_toFun := (γ.continuousOn.comp_continuous (by fun_prop) hu).subtype_mk _
    source' := by apply Subtype.ext; simp [u,base]
    target' := by apply Subtype.ext; simpa [u,base] using hclosed.symm }
  obtain ⟨z,H,hloop⟩ := hfree base p
  have hloc : ∀ x ∈ U, ∃ r > 0, HasPotential (Metric.ball x r) F := by
    intro x hx
    obtain ⟨r,hr,_,hp⟩ := local_potential U F hU hF hs x hx
    exact ⟨r,hr,hp⟩
  obtain ⟨t,N,htzero,htmono,htlast,hbottom,hzero⟩ :=
    contraction_chord_grid hloc H.toContinuousMap (by intro t; simp) hloop
  let r (k : ℕ) := u (t k)
  have hr (k : ℕ) : r k ∈ Icc a b := hu _
  have hrmono : Monotone r := hum.comp htmono
  have hrzero : r 0 = a := by simp [r,htzero,u]
  have hrlast : r N = b := by simp [r,htlast,u]
  have hbottom_value (v : I) : (H.toContinuousMap (0,v) : E n) = γ (u v) := by
    exact congrArg Subtype.val (H.map_zero_left v)
  have hlocal : ∀ k < N, ∃ V : Set (E n), IsOpen V ∧ Convex ℝ V ∧ HasPotential V F ∧
      ∀ w ∈ Icc (r k) (r (k+1)), γ w ∈ V := by
    intro k _
    obtain ⟨V,hV,hconv,hp,htrace⟩ := hbottom k
    refine ⟨V,hV,hconv,hp,?_⟩
    intro w hw
    have hwab : w ∈ Icc a b := ⟨(hr k).1.trans hw.1,hw.2.trans (hr (k+1)).2⟩
    let v : I := ⟨(w-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hwab.1) hpos.le,
      (div_le_one hpos).mpr (by linarith [hwab.2])⟩⟩
    have hv : v ∈ Icc (t k) (t (k+1)) := by
      constructor
      · change (t k : ℝ) ≤ (w-a)/(b-a)
        apply (le_div_iff₀ hpos).mpr
        have hwl : a+(b-a)*(t k : ℝ) ≤ w := hw.1
        nlinarith [hwl]
      · change (w-a)/(b-a) ≤ (t (k+1) : ℝ)
        apply (div_le_iff₀ hpos).mpr
        have hwr : w ≤ a+(b-a)*(t (k+1) : ℝ) := hw.2
        nlinarith [hwr]
    have hvw : u v = w := by
      dsimp only [u,v]
      field_simp
      <;> ring
    have he := htrace v hv
    rwa [hbottom_value,hvw] at he
  change workLineIntegral d F hi = 0
  rw [work_eq_chord_sum γ d F hi r N hr hrmono hrzero hrlast hlocal]
  simpa only [hbottom_value] using hzero

/-- Global C¹ potential, obtained from the proved vanishing of every proper
piecewise C¹ work period and the upstream endpoint criterion. -/
theorem simply_connected_potential {n : ℕ} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hc : IsPreconnected U) (hfree : FreeLoopContractions U)
    (hF : CrOn 1 U F) (hJac : ∀ x ∈ U, (jacobian F x).IsSymm) : HasPotential U F := by
  have hcont : ContinuousOn F U := ((crOn_iff_contDiffOn 1 U F hU).mp hF).continuousOn
  exact pathIndependent_hasPotential U F hU hc hcont
    (zeroPeriods_pathIndependent U F (simply_connected_zeroPeriods U F hU hc hfree hF
      ((symmetry_iff_jacobian U F hU hF).mpr hJac)))

end D04.C11



