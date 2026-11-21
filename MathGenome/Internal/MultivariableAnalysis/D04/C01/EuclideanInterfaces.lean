import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.Convex.PathConnected

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04

/-- The single ambient representation, including dimension zero. -/
abbrev E : ℕ → Type :=
  fun n => EuclideanSpace ℝ (Fin n)
def coordinates : (n : ℕ) → E n ≃ₗ[ℝ] (Fin n → ℝ) :=
  fun n => WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
def standardBasis : (n : ℕ) → Module.Basis (Fin n) ℝ (E n) :=
  fun n => (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- The finite maximum of absolute coordinates; the empty maximum is zero. -/
def maxNorm : {n : ℕ} → E n → ℝ :=
  fun {n} x => ↑((Finset.univ : Finset (Fin n)).sup (fun i => ‖x i‖₊) : NNReal)
def matrixLinearEquiv : (m n : ℕ) → Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ] (E n →ₗ[ℝ] E m) :=
  fun m n => Matrix.toEuclideanLin
def matrixOfLinearMap : {m n : ℕ} → (E n →ₗ[ℝ] E m) → Matrix (Fin m) (Fin n) ℝ :=
  fun {m n} A => (matrixLinearEquiv m n).symm A

/-- Complex coordinates are explicitly a real linear pair of coordinates. -/
def complexCoordinates : ℂ ≃ₗ[ℝ] E 2 :=
  { toFun := fun z => WithLp.toLp 2 ![z.re, z.im]
    invFun := fun x => ⟨x 0, x 1⟩
    left_inv := by intro z; rfl
    right_inv := by intro x; ext i; fin_cases i <;> rfl
    map_add' := by intro z w; ext i; fin_cases i <;> rfl
    map_smul' := by intro r z; ext i; fin_cases i <;> simp }
def ball : {n : ℕ} → E n → ℝ → Set (E n) :=
  fun a r => {x | ‖x - a‖ < r}
def Open : {n : ℕ} → Set (E n) → Prop :=
  fun U => ∀ a ∈ U, ∃ r > 0, ball a r ⊆ U
def Closed : {n : ℕ} → Set (E n) → Prop :=
  fun F => Open Fᶜ
def Interior : {n : ℕ} → Set (E n) → Set (E n) :=
  fun A => {a | ∃ r > 0, ball a r ⊆ A}
def Closure : {n : ℕ} → Set (E n) → Set (E n) :=
  fun A => {a | ∀ r > 0, ∃ x ∈ A, x ∈ ball a r}

/-- Ambient boundary, distinct from a manifold boundary. -/
def Boundary : {n : ℕ} → Set (E n) → Set (E n) :=
  fun A => Closure A \ Interior A
def relativeBall : {n : ℕ} → Set (E n) → E n → ℝ → Set (E n) :=
  fun A a r => A ∩ ball a r
def RelativeNeighborhood : {n : ℕ} → (A : Set (E n)) → A → Set (E n) → Prop :=
  fun A a N => ∃ r > 0, relativeBall A a r ⊆ N
def RelativelyOpen : {n : ℕ} → Set (E n) → Set (E n) → Prop :=
  fun A U => ∃ V, Open V ∧ U = A ∩ V
def AccumulationPoint : {n : ℕ} → Set (E n) → E n → Prop :=
  fun A a => ∀ r > 0, ∃ x ∈ A, x ≠ a ∧ x ∈ ball a r
def IsolatedPoint : {n : ℕ} → (A : Set (E n)) → A → Prop :=
  fun A a => ∃ r > 0, ∀ x ∈ A, x ∈ ball a r → x = a

/-- Accumulation is part of the assertion, so isolated points have no asserted punctured limit. -/
def RelativeLimit : {n m : ℕ} → (A : Set (E n)) → (A → E m) → E n → E m → Prop :=
  fun A f a b => AccumulationPoint A a ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x : A,
      0 < ‖(x : E _) - a‖ → ‖(x : E _) - a‖ < δ → ‖f x - b‖ < ε
def RelativeContinuousAt : {n m : ℕ} → (A : Set (E n)) → (A → E m) → A → Prop :=
  fun A f a => ∀ ε > 0, ∃ δ > 0, ∀ x : A,
    ‖x.val - a.val‖ < δ → ‖f x - f a‖ < ε
def RelativeContinuous : {n m : ℕ} → (A : Set (E n)) → (A → E m) → Prop :=
  fun A f => ∀ a, RelativeContinuousAt A f a
def RelativeUniformContinuous : {n m : ℕ} → (A : Set (E n)) → (A → E m) → Prop :=
  fun A f => ∀ ε > 0, ∃ δ > 0, ∀ x y : A,
    ‖x.val - y.val‖ < δ → ‖f x - f y‖ < ε
def Compact : {n : ℕ} → Set (E n) → Prop :=
  fun K => ∀ (ι : Type) (U : ι → Set (E _)), (∀ i, Open (U i)) →
    K ⊆ ⋃ i, U i → ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i
def SequentiallyCompact : {n : ℕ} → Set (E n) → Prop :=
  fun K => ∀ x : ℕ → E _, (∀ j, x j ∈ K) →
    ∃ a ∈ K, ∃ s : ℕ → ℕ, StrictMono s ∧ Filter.Tendsto (x ∘ s) Filter.atTop (𝓝 a)

/-- The empty-set-compatible connectedness convention. See connected_iff_no_separation. -/
def Connected : {n : ℕ} → Set (E n) → Prop :=
  fun A => IsPreconnected A
abbrev DomainPath : {n : ℕ} → (A : Set (E n)) → A → A → Type :=
  fun _ a b => Path a b
def PathConnected : {n : ℕ} → Set (E n) → Prop :=
  fun A => ∀ a b : A, Nonempty (DomainPath A a b)

/-- A finite ordered chain of segments in A, including the zero-segment constant path. -/
abbrev PolygonalPath : {n : ℕ} → (A : Set (E n)) → A → A → Type :=
  fun A a b => {p : Σ N : ℕ, Fin (N + 1) → E _ //
    p.2 0 = a ∧ p.2 (Fin.last p.1) = b ∧
    ∀ i : Fin p.1, segment ℝ (p.2 i.castSucc) (p.2 i.succ) ⊆ A}
def PolygonallyConnected : {n : ℕ} → Set (E n) → Prop :=
  fun A => ∀ a b : A, Nonempty (PolygonalPath A a b)
def ConvexSet : {n : ℕ} → Set (E n) → Prop :=
  fun A => Convex ℝ A

/-- All loops contract through loops with their basepoint fixed; path connectedness uses universal pairs. -/
def SimplyConnected : {n : ℕ} → Set (E n) → Prop :=
  fun A => PathConnected A ∧ ∀ a : A, ∀ γ : DomainPath A a a,
    Nonempty (Path.Homotopy γ (Path.refl a))
def linearOperatorNorm : {n m : ℕ} → (E n →ₗ[ℝ] E m) → ℝ :=
  fun A => sSup ((fun v => ‖A v‖) '' {v | ‖v‖ ≤ 1})
def multilinearOperatorNorm : {n m k : ℕ} → MultilinearMap ℝ (fun _ : Fin k => E n) (E m) → ℝ :=
  fun T => sSup ((fun v => ‖T v‖) '' {v | ∀ i, ‖v i‖ ≤ 1})


theorem coordinates_apply {n : ℕ} (x : E n) (i : Fin n) :
    coordinates n x i = x i := by rfl

theorem standardBasis_apply {n : ℕ} (i j : Fin n) :
    standardBasis n i j = if j = i then 1 else 0 := by
  simp [standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem inner_coordinates {n : ℕ} (x y : E n) :
    inner ℝ x y = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

theorem norm_coordinates {n : ℕ} (x : E n) :
    ‖x‖ = Real.sqrt (∑ i, x i ^ 2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq x

theorem maxNorm_eq_coordinate_norm {n : ℕ} (x : E n) :
    maxNorm x = ‖coordinates n x‖ := by
  rfl

theorem norm_dimension_zero (x : E 0) : ‖x‖ = 0 := by
  rw [norm_coordinates]; simp

theorem maxNorm_dimension_zero (x : E 0) : maxNorm x = 0 := by
  simp [maxNorm]

theorem vector_dimension_zero (x : E 0) : x = 0 := by
  ext i; exact Fin.elim0 i

theorem matrix_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : E n) (i : Fin m) :
    matrixLinearEquiv m n M x i = ∑ j, M i j * x j := by
  rfl

theorem matrix_column {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    matrixLinearEquiv m n M (standardBasis n j) i = M i j := by
  simp [matrix_apply, standardBasis_apply]

theorem matrixOfLinearMap_apply {m n : ℕ} (A : E n →ₗ[ℝ] E m) (i : Fin m) (j : Fin n) :
    matrixOfLinearMap A i j = A (standardBasis n j) i := by
  have h := matrix_column (matrixOfLinearMap A) i j
  simpa [matrixOfLinearMap] using h.symm

theorem matrix_linear_roundtrip {m n : ℕ} (A : E n →ₗ[ℝ] E m) :
    matrixLinearEquiv m n (matrixOfLinearMap A) = A := by
  exact (matrixLinearEquiv m n).apply_symm_apply A

theorem matrix_composition {m n p : ℕ} (A : Matrix (Fin p) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) :
    matrixLinearEquiv p n (A * B) =
      (matrixLinearEquiv p m A).comp (matrixLinearEquiv m n B) := by
  exact Matrix.toLpLin_mul_same 2 A B

theorem linearMap_from_zero {m : ℕ} (A : E 0 →ₗ[ℝ] E m) : A = 0 := by
  apply LinearMap.ext
  intro x
  rw [vector_dimension_zero x]
  exact A.map_zero

theorem linearMap_to_zero {n : ℕ} (A : E n →ₗ[ℝ] E 0) : A = 0 := by
  ext x i; exact Fin.elim0 i

theorem empty_matrix_determinant (M : Matrix (Fin 0) (Fin 0) ℝ) : Matrix.det M = 1 := by
  simp

theorem complexCoordinates_re (z : ℂ) : complexCoordinates z 0 = z.re := by rfl

theorem complexCoordinates_im (z : ℂ) : complexCoordinates z 1 = z.im := by rfl

theorem ball_eq_metric {n : ℕ} (a : E n) (r : ℝ) : ball a r = Metric.ball a r := by
  ext x; simp [ball, dist_eq_norm]

theorem open_iff_isOpen {n : ℕ} (U : Set (E n)) : Open U ↔ IsOpen U := by
  simp only [Open, ball_eq_metric, Metric.isOpen_iff]

theorem closed_iff_isClosed {n : ℕ} (F : Set (E n)) : Closed F ↔ IsClosed F := by
  simp [Closed, open_iff_isOpen]

theorem interior_eq {n : ℕ} (A : Set (E n)) : Interior A = interior A := by
  ext a
  simp only [Interior, mem_ofPred_eq, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff,
    ball_eq_metric]

theorem closure_eq {n : ℕ} (A : Set (E n)) : Closure A = closure A := by
  ext a
  simp only [Closure, mem_ofPred_eq, ball_eq_metric, Metric.mem_ball,
    Metric.mem_closure_iff, dist_comm]

theorem boundary_eq_frontier {n : ℕ} (A : Set (E n)) : Boundary A = frontier A := by
  rw [Boundary, closure_eq, interior_eq]; rfl

theorem relativeNeighborhood_iff {n : ℕ} (A : Set (E n)) (a : A) (N : Set (E n)) :
    RelativeNeighborhood A a N ↔ N ∈ 𝓝[A] (a : E n) := by
  rw [RelativeNeighborhood, Metric.mem_nhdsWithin_iff]
  simp only [relativeBall, ball_eq_metric, inter_comm]

theorem relativelyOpen_iff {n : ℕ} (A U : Set (E n)) :
    RelativelyOpen A U ↔ ∃ V, IsOpen V ∧ U = A ∩ V := by
  simp only [RelativelyOpen, open_iff_isOpen]

theorem relativelyOpen_subtype_iff {n : ℕ} (A U : Set (E n)) :
    RelativelyOpen A U ↔ U ⊆ A ∧ IsOpen ((Subtype.val : A → E n) ⁻¹' U) := by
  rw [relativelyOpen_iff]
  constructor
  · rintro ⟨V, hV, rfl⟩
    refine ⟨inter_subset_left, ?_⟩
    have hpre : (Subtype.val : A → E n) ⁻¹' (A ∩ V) = Subtype.val ⁻¹' V := by
      ext x; simp only [mem_preimage, mem_inter_iff, x.property, true_and]
    rw [hpre]
    exact
      hV.preimage continuous_subtype_val
  · rintro ⟨hUA, hU⟩
    rcases isOpen_induced_iff.mp hU with ⟨V, hV, heq⟩
    refine ⟨V, hV, ?_⟩
    ext x
    constructor
    · intro hx
      refine ⟨hUA hx, ?_⟩
      have : (⟨x, hUA hx⟩ : A) ∈ (Subtype.val : A → E n) ⁻¹' V := by
        rw [heq]; exact hx
      exact this
    · rintro ⟨hxA, hxV⟩
      have : (⟨x, hxA⟩ : A) ∈ (Subtype.val : A → E n) ⁻¹' U := by
        rw [← heq]; exact hxV
      exact this

theorem accumulationPoint_iff_accPt {n : ℕ} (A : Set (E n)) (a : E n) :
    AccumulationPoint A a ↔ AccPt a (𝓟 A) := by
  rw [accPt_iff_nhds]
  constructor
  · intro h U hU
    rcases Metric.mem_nhds_iff.mp hU with ⟨r, hr, hsub⟩
    rcases h r hr with ⟨x, hxA, hxa, hxr⟩
    exact ⟨x, ⟨hsub (by simpa [ball_eq_metric] using hxr), hxA⟩, hxa⟩
  · intro h r hr
    rcases h (Metric.ball a r) (Metric.ball_mem_nhds a hr) with ⟨x, ⟨hxr, hxA⟩, hxa⟩
    exact ⟨x, hxA, hxa, by simpa [ball_eq_metric] using hxr⟩

theorem relativeContinuousAt_iff {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A) :
    RelativeContinuousAt A f a ↔ ContinuousAt f a := by
  rw [Metric.continuousAt_iff]
  simp only [RelativeContinuousAt, Subtype.dist_eq, dist_eq_norm]

theorem relativeContinuous_iff {n m : ℕ} (A : Set (E n)) (f : A → E m) :
    RelativeContinuous A f ↔ Continuous f := by
  simp only [RelativeContinuous, relativeContinuousAt_iff, continuous_iff_continuousAt]

theorem relativeUniformContinuous_iff {n m : ℕ} (A : Set (E n)) (f : A → E m) :
    RelativeUniformContinuous A f ↔ UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  simp only [RelativeUniformContinuous, Subtype.dist_eq, dist_eq_norm]

theorem isolated_not_accumulation {n : ℕ} (A : Set (E n)) (a : A) (ha : IsolatedPoint A a) :
    ¬ AccumulationPoint A a := by
  rcases ha with ⟨r, hr, h⟩
  rintro hacc
  rcases hacc r hr with ⟨x, hxA, hxa, hxr⟩
  exact hxa (h x hxA hxr)

theorem continuousAt_isolated {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A)
    (ha : IsolatedPoint A a) : RelativeContinuousAt A f a := by
  rcases ha with ⟨r, hr, h⟩
  intro ε hε
  refine ⟨r, hr, ?_⟩
  intro x hx
  have hxa : x = a := Subtype.ext (h x x.property hx)
  simpa only [hxa, sub_self, norm_zero] using hε

theorem no_limit_at_isolated {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A)
    (ha : IsolatedPoint A a) (b : E m) : ¬ RelativeLimit A f a b := by
  exact fun h => isolated_not_accumulation A a ha h.1

theorem compact_iff_isCompact {n : ℕ} (K : Set (E n)) : Compact K ↔ IsCompact K := by
  simp only [Compact, open_iff_isOpen, isCompact_iff_finite_subcover]

theorem sequentiallyCompact_iff_isSeqCompact {n : ℕ} (K : Set (E n)) :
    SequentiallyCompact K ↔ IsSeqCompact K := by
  rfl

theorem connected_iff_no_separation {n : ℕ} (A : Set (E n)) :
    Connected A ↔ ¬ ∃ U V : Set (E n),
      RelativelyOpen A U ∧ RelativelyOpen A V ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint U V ∧ A = U ∪ V := by
  constructor
  · intro hc
    rintro ⟨U, V, hU, hV, hUn, hVn, hd, he⟩
    rcases relativelyOpen_iff A U |>.mp hU with ⟨u, hu, rfl⟩
    rcases relativelyOpen_iff A V |>.mp hV with ⟨v, hv, rfl⟩
    have hcover : A ⊆ u ∪ v := by
      intro x hx
      rw [he] at hx
      exact hx.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    rcases hc u v hu hv hcover hUn hVn with ⟨x, hxA, hxu, hxv⟩
    exact Set.disjoint_left.mp hd ⟨hxA, hxu⟩ ⟨hxA, hxv⟩
  · intro h u v hu hv hcover hUn hVn
    by_contra hn
    apply h
    refine ⟨A ∩ u, A ∩ v, ?_, ?_, hUn, hVn, ?_, ?_⟩
    · exact (relativelyOpen_iff A _).mpr ⟨u, hu, rfl⟩
    · exact (relativelyOpen_iff A _).mpr ⟨v, hv, rfl⟩
    · exact Set.disjoint_left.mpr fun x hxu hxv => hn ⟨x, hxu.1, hxu.2, hxv.2⟩
    · ext x
      constructor
      · intro hx
        exact (hcover hx).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
      · exact fun h => h.elim And.left And.left

theorem connected_iff_isPreconnected {n : ℕ} (A : Set (E n)) :
    Connected A ↔ IsPreconnected A := by rfl

theorem connected_nonempty_iff_isConnected {n : ℕ} (A : Set (E n)) (hA : A.Nonempty) :
    Connected A ↔ IsConnected A := by
  exact ⟨fun h => ⟨hA, h⟩, fun h => h.2⟩

theorem connected_empty {n : ℕ} : Connected (∅ : Set (E n)) :=
  isPreconnected_empty

theorem pathConnected_empty {n : ℕ} : PathConnected (∅ : Set (E n)) := by
  intro a; exact False.elim a.property

theorem path_properties {n : ℕ} (A : Set (E n)) (a b : A) (γ : DomainPath A a b) :
    Continuous γ ∧ γ 0 = a ∧ γ 1 = b := by
  exact ⟨γ.continuous, γ.source, γ.target⟩

theorem polygonalPath_has_path {n : ℕ} (A : Set (E n)) (a b : A)
    (p : PolygonalPath A a b) : Nonempty (DomainPath A a b) := by
  rcases p with ⟨⟨N, v⟩, hstart, hend, hseg⟩
  dsimp only at hstart hend hseg
  have reach : ∀ j : Fin (N + 1), JoinedIn A (a : E n) (v j) := by
    intro j
    induction j using Fin.induction with
    | zero => rw [hstart]; exact JoinedIn.refl a.property
    | succ j ih => exact ih.trans (JoinedIn.of_segment_subset (hseg j))
  have h := reach (Fin.last N)
  rw [hend] at h
  exact h.joined_subtype

theorem contraction_properties {n : ℕ} (A : Set (E n)) (a : A) (γ : DomainPath A a a)
    (H : Path.Homotopy γ (Path.refl a)) :
    Continuous H ∧ (∀ t, H (0, t) = γ t) ∧ (∀ t, H (1, t) = a) ∧
      (∀ s, H (s, 0) = a ∧ H (s, 1) = a) := by
  exact ⟨H.continuous, H.map_zero_left, H.map_one_left, fun s => ⟨H.source s, H.target s⟩⟩

theorem convexSet_iff_segment {n : ℕ} (A : Set (E n)) :
    ConvexSet A ↔ ∀ x ∈ A, ∀ y ∈ A, segment ℝ x y ⊆ A := by
  exact convex_iff_segment_subset

theorem linearOperatorNorm_eq_standard {n m : ℕ} (A : E n →L[ℝ] E m) :
    linearOperatorNorm A.toLinearMap = ‖A‖ := by
  change sSup ((fun v : E n => ‖A v‖) '' {v | ‖v‖ ≤ 1}) = ‖A‖
  have hball : {v : E n | ‖v‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext v
    exact mem_closedBall_zero_iff.symm
  rw [hball]
  exact A.sSup_unitClosedBall_eq_norm

theorem multilinearOperatorNorm_eq_standard {n m k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E n) (E m)) :
    multilinearOperatorNorm T.toMultilinearMap = ‖T‖ := by
  let S : Set ℝ := (fun v => ‖T v‖) '' {v | ∀ i, ‖v i‖ ≤ 1}
  change sSup S = ‖T‖
  have h0 : ‖T 0‖ ∈ S := ⟨0, by simp, rfl⟩
  have hbound : ∀ r ∈ S, r ≤ ‖T‖ := by
    rintro r ⟨v, hv, rfl⟩
    exact T.unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr hv)
  have hb : BddAbove S := ⟨‖T‖, hbound⟩
  have hnonneg : 0 ≤ sSup S := (norm_nonneg _).trans (le_csSup hb h0)
  refine le_antisymm (csSup_le ⟨_, h0⟩ hbound) ?_
  apply ContinuousMultilinearMap.opNorm_le_bound hnonneg
  intro v
  by_cases hz : ∃ i, v i = 0
  · rcases hz with ⟨i, hi⟩
    have ht : T v = 0 := T.toMultilinearMap.map_coord_zero i hi
    rw [ht]
    simp only [norm_zero]
    exact mul_nonneg hnonneg (Finset.prod_nonneg fun j _ => norm_nonneg _)
  · have hz : ∀ i, v i ≠ 0 := fun i hi => hz ⟨i, hi⟩
    let w : Fin k → E n := fun i => ‖v i‖⁻¹ • v i
    have hn (i : Fin k) : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (hz i)
    have hw : ∀ i, ‖w i‖ ≤ 1 := by
      intro i
      simp [w, norm_smul, hn i]
    have hs : ‖T w‖ ≤ sSup S := le_csSup hb ⟨w, hw, rfl⟩
    have he : T v = (∏ i, ‖v i‖) • T w := by
      rw [← T.map_smul_univ]
      congr 1
      funext i
      simp [w, smul_smul, hn i]
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hs (Finset.prod_nonneg fun i _ => norm_nonneg _)).trans_eq
      (mul_comm _ _)

theorem linearOperatorNorm_from_zero {m : ℕ} (A : E 0 →ₗ[ℝ] E m) :
    linearOperatorNorm A = 0 := by
  rw [linearMap_from_zero A]
  unfold linearOperatorNorm
  simp only [LinearMap.zero_apply, norm_zero]
  rw [Set.Nonempty.image_const ⟨0, by simp⟩, csSup_singleton]

theorem multilinearOperatorNorm_order_zero {n m : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin 0 => E n) (E m)) :
    multilinearOperatorNorm T = ‖T (fun i => Fin.elim0 i)‖ := by
  have hs : ((fun v => ‖T v‖) '' {v | ∀ i, ‖v i‖ ≤ 1}) =
      {‖T (fun i => Fin.elim0 i)‖} := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      congr 2
      funext i; exact Fin.elim0 i
    · intro hr
      refine ⟨(fun i => Fin.elim0 i), ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · exact hr.symm
  rw [multilinearOperatorNorm, hs, csSup_singleton]

theorem multilinearMap_from_zero {m k : ℕ} (hk : 0 < k)
    (T : MultilinearMap ℝ (fun _ : Fin k => E 0) (E m)) : T = 0 := by
  apply MultilinearMap.ext
  intro v
  exact T.map_coord_zero ⟨0, hk⟩ (vector_dimension_zero _)

theorem multilinearOperatorNorm_from_zero {m k : ℕ} (hk : 0 < k)
    (T : MultilinearMap ℝ (fun _ : Fin k => E 0) (E m)) :
    multilinearOperatorNorm T = 0 := by
  rw [multilinearMap_from_zero hk T]
  unfold multilinearOperatorNorm
  simp only [zero_apply, norm_zero]
  rw [Set.Nonempty.image_const ⟨0, by simp⟩, csSup_singleton]

end D04
