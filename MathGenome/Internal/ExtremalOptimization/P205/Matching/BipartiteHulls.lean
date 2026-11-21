import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.BipartiteHulls
import MathGenome.Internal.ExtremalOptimization.P205.Networks.IncidenceTU
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.IntegralVertices
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.BoundedHull

noncomputable section
open scoped BigOperators
open Set Matrix
universe u v
namespace P205.Matching

/-- Integrality transports through arbitrary finite coordinate enumerations. -/
lemma integral_extremePoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b : ι → ℤ) (hA : A.IsTotallyUnimodular)
    (x : κ → ℝ)
    (hx : x ∈ ({x | (A.map (Int.cast : ℤ → ℝ)).mulVec x ≤
      fun i => (b i : ℝ)} : Set (κ → ℝ)).extremePoints ℝ) :
    ∀ j, ∃ z : ℤ, x j = (z : ℝ) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let f : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let T : (Fin (Fintype.card κ) → ℝ) ≃ₗ[ℝ] (κ → ℝ) :=
    LinearEquiv.piCongrLeft ℝ (fun _ => ℝ) f
  let B := A.submatrix e f
  let d := fun i => b (e i)
  let Q := Polyhedra.polyhedron (B.map (Int.cast : ℤ → ℝ))
    (fun i => (d i : ℝ))
  have hQ : T '' Q = {x | (A.map (Int.cast : ℤ → ℝ)).mulVec x ≤
      fun i => (b i : ℝ)} := by
    ext y
    have himage : y ∈ T '' Q ↔ T.symm y ∈ Q := by
      constructor
      · rintro ⟨z, hz, rfl⟩; simpa using hz
      · intro hy; exact ⟨_, hy, T.apply_symm_apply y⟩
    rw [himage]
    change (∀ i, _ ≤ _) ↔ ∀ i, _ ≤ _
    have heq : (B.map (Int.cast : ℤ → ℝ)).mulVec (T.symm y) =
        ((A.map (Int.cast : ℤ → ℝ)).mulVec y) ∘ e := by
      change ((A.map (Int.cast : ℤ → ℝ)).submatrix e f).mulVec (y ∘ f) = _
      rw [Matrix.submatrix_mulVec_equiv]
      simp [Function.comp_def]
    change (∀ i, ((B.map (Int.cast : ℤ → ℝ)).mulVec (T.symm y)) i ≤ _) ↔ _
    rw [heq]
    exact e.forall_congr' (fun i => by simp [d])
  have hv : T.symm x ∈ Q.extremePoints ℝ := by
    have : x ∈ T '' Q.extremePoints ℝ := by
      rw [image_extremePoints T Q, hQ]
      exact hx
    obtain ⟨z, hz, hzx⟩ := this
    simpa [← hzx] using hz
  have hint := Polyhedra.vertex_integral B d (T.symm x) (hA.submatrix e f) hv
  intro j
  simpa [T, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', f] using hint (f.symm j)

/-- A bounded integral TU system is the hull of its integral feasible points.
An empty feasible set is handled explicitly. -/
lemma bounded_tu_hull {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b : ι → ℤ) (hA : A.IsTotallyUnimodular)
    (hb : Bornology.IsBounded
      ({x | (A.map (Int.cast : ℤ → ℝ)).mulVec x ≤ fun i => (b i : ℝ)} : Set (κ → ℝ))) :
    let P : Set (κ → ℝ) := {x | (A.map (Int.cast : ℤ → ℝ)).mulVec x ≤ fun i => (b i : ℝ)}
    P = convexHull ℝ {x ∈ P | ∀ j, ∃ z : ℤ, x j = (z : ℝ)} := by
  intro P
  have hconv : Convex ℝ P :=
    (convex_Iic (fun i => (b i : ℝ))).linear_preimage
      (A.map (Int.cast : ℤ → ℝ)).mulVecLin
  apply le_antisymm
  · by_cases hn : P.Nonempty
    · have hc : IsCompact P := Metric.isCompact_of_isClosed_isBounded
        (isClosed_Iic.preimage (A.map (Int.cast : ℤ → ℝ)).mulVecLin.continuous_of_finiteDimensional) hb
      calc
        P = convexHull ℝ (P.extremePoints ℝ) :=
          VariationalNotes.ConvexGeometry.extremePoint_representation P hn hc hconv
        _ ⊆ convexHull ℝ {x ∈ P | ∀ j, ∃ z : ℤ, x j = (z : ℝ)} :=
          convexHull_mono (fun x hx => ⟨hx.1, integral_extremePoint A b hA x hx⟩)
    · simp [Set.not_nonempty_iff_eq_empty.mp hn]
  · exact convexHull_min (fun _ hx => hx.1) hconv

/-- Adding nonnegativity keeps TU and identifies the ordinary halfspace system. -/
lemma nonnegative_tu_hull {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b : ι → ℤ) (hA : A.IsTotallyUnimodular)
    (hb : Bornology.IsBounded
      ({x : κ → ℝ | (∀ j, 0 ≤ x j) ∧
        (A.map (Int.cast : ℤ → ℝ)).mulVec x ≤ fun i => (b i : ℝ)})) :
    let P : Set (κ → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      (A.map (Int.cast : ℤ → ℝ)).mulVec x ≤ fun i => (b i : ℝ)}
    P = convexHull ℝ {x ∈ P | ∀ j, ∃ z : ℤ, x j = (z : ℝ)} := by
  classical
  intro P
  let B := Matrix.fromRows A (fun i : κ => Pi.single i (-1 : ℤ))
  let d : ι ⊕ κ → ℤ := Sum.elim b (fun _ => 0)
  have hB : B.IsTotallyUnimodular := by
    apply hA.fromRows_unitlike
    intro _ i
    exact ⟨i, -1, by simp⟩
  have hrow (x : κ → ℝ) (j : κ) :
      ((B.map (Int.cast : ℤ → ℝ)).mulVec x) (.inr j) = -x j := by
    change (∑ i, (((Pi.single j (-1 : ℤ) : κ → ℤ) i : ℤ) : ℝ) * x i) = -x j
    simp [Pi.single_apply]
  have hset : {x | (B.map (Int.cast : ℤ → ℝ)).mulVec x ≤ fun i => (d i : ℝ)} = P := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro j
        have h := hx (.inr j)
        rw [hrow] at h
        simpa [d] using h
      · intro i
        exact hx (.inl i)
    · intro hx i
      cases i with
      | inl i => exact hx.2 i
      | inr j => simpa [hrow, d] using hx.1 j
  have h := bounded_tu_hull B d hB (hset.symm ▸ hb)
  dsimp only at h
  simpa only [hset] using h

/-- Equalities are encoded by the two opposing integer rows, with their signs. -/
lemma nonnegative_eq_tu_hull {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b : ι → ℤ) (hA : A.IsTotallyUnimodular)
    (hb : Bornology.IsBounded
      ({x : κ → ℝ | (∀ j, 0 ≤ x j) ∧
        (A.map (Int.cast : ℤ → ℝ)).mulVec x = fun i => (b i : ℝ)})) :
    let P : Set (κ → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      (A.map (Int.cast : ℤ → ℝ)).mulVec x = fun i => (b i : ℝ)}
    P = convexHull ℝ {x ∈ P | ∀ j, ∃ z : ℤ, x j = (z : ℝ)} := by
  intro P
  let B := Matrix.fromRows A (-A)
  let d : ι ⊕ ι → ℤ := Sum.elim b (-b)
  have hB : B.IsTotallyUnimodular := Polyhedra.TotalUnimodularity.opposing_rows hA
  have hneg : B.map (Int.cast : ℤ → ℝ) =
      Matrix.fromRows (A.map (Int.cast : ℤ → ℝ)) (-(A.map (Int.cast : ℤ → ℝ))) := by
    ext (i | i) j <;> simp [B]
  have hset : {x : κ → ℝ | (∀ j, 0 ≤ x j) ∧
      (B.map (Int.cast : ℤ → ℝ)).mulVec x ≤ fun i => (d i : ℝ)} = P := by
    ext x
    simp only [hneg, Matrix.fromRows_mulVec]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, funext (fun i => le_antisymm (h (.inl i)) ?_)⟩
      have hh := h (.inr i)
      simpa [d, Matrix.neg_mulVec] using hh
    · rintro ⟨hx, heq⟩
      refine ⟨hx, ?_⟩
      rintro (i | i)
      · simp [heq, d]
      · simp [Matrix.neg_mulVec, heq, d]
  have h := nonnegative_tu_hull B d hB (hset.symm ▸ hb)
  dsimp only at h
  simpa only [hset] using h

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]
  {G : BipartiteGraph L R}

omit [Fintype L] [Fintype R] in
lemma incidence_nonneg (v : L ⊕ R) (e : Edge G) :
    (0 : ℝ) ≤ (incidence G v e : ℝ) := by
  classical
  simp only [incidence, Specs.P205.Matching.incidence]
  split_ifs <;> norm_num

lemma coordinate_le_load {x : Edge G → ℝ} (hx : ∀ e, 0 ≤ x e) (e : Edge G) :
    x e ≤ load x (.inl e.val.1) := by
  have h := Finset.single_le_sum
    (fun f (_ : f ∈ Finset.univ) => mul_nonneg (incidence_nonneg (.inl e.val.1) f) (hx f))
    (Finset.mem_univ e)
  simpa [load, Specs.P205.Matching.load] using h

lemma matching_feasible_bounded (G : BipartiteGraph L R) :
    Bornology.IsBounded ({x : Edge G → ℝ | (∀ e, 0 ≤ x e) ∧ ∀ v, load x v ≤ 1}) := by
  apply (Metric.isBounded_Icc (0 : Edge G → ℝ) 1).subset
  intro x hx
  exact ⟨hx.1, fun e => (coordinate_le_load hx.1 e).trans (hx.2 _)⟩

lemma perfect_feasible_bounded (G : BipartiteGraph L R) :
    Bornology.IsBounded ({x : Edge G → ℝ | (∀ e, 0 ≤ x e) ∧ ∀ v, load x v = 1}) := by
  apply (matching_feasible_bounded G).subset
  exact fun x hx => ⟨hx.1, fun v => (hx.2 v).le⟩

lemma integral_feasible_indicator {x : Edge G → ℝ}
    (hx : (∀ e, 0 ≤ x e) ∧ ∀ v, load x v ≤ 1)
    (hint : ∀ e, ∃ z : ℤ, x e = (z : ℝ)) :
    ∃ M : Set (Edge G), IsMatching M ∧ x = indicator M := by
  classical
  let M : Set (Edge G) := {e | x e = 1}
  have h01 : ∀ e, x e = 0 ∨ x e = 1 := by
    intro e
    obtain ⟨z, hz⟩ := hint e
    have hl := hx.1 e
    have hu := (coordinate_le_load hx.1 e).trans (hx.2 _)
    rw [hz] at hl hu ⊢
    have hz0 : 0 ≤ z := by exact_mod_cast hl
    have hz1 : z ≤ 1 := by exact_mod_cast hu
    have : z = 0 ∨ z = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have heq : x = indicator M := by
    funext e
    rcases h01 e with h | h <;>
      simp [indicator, Specs.P205.Matching.indicator, M, h]
  refine ⟨M, ?_, heq⟩
  rw [matching_iff_degree]
  intro v
  have h := hx.2 v
  rw [heq, load_indicator] at h
  exact_mod_cast h

lemma indicator_feasible {M : Set (Edge G)} (hM : IsMatching M) :
    (∀ e, 0 ≤ indicator M e) ∧ ∀ v, load (indicator M) v ≤ 1 := by
  constructor
  · intro e
    rcases indicator_zero_one M e with h | h <;> simp [h]
  · intro v
    rw [load_indicator]
    exact_mod_cast (matching_iff_degree M).mp hM v

lemma perfect_indicator_feasible {M : Set (Edge G)} (hM : IsPerfectMatching M) :
    (∀ e, 0 ≤ indicator M e) ∧ ∀ v, load (indicator M) v = 1 := by
  refine ⟨(indicator_feasible hM.1).1, ?_⟩
  intro v
  rw [load_indicator]
  exact_mod_cast (perfect_iff_degree M).mp hM v

lemma integral_perfect_feasible_indicator {x : Edge G → ℝ}
    (hx : (∀ e, 0 ≤ x e) ∧ ∀ v, load x v = 1)
    (hint : ∀ e, ∃ z : ℤ, x e = (z : ℝ)) :
    ∃ M : Set (Edge G), IsPerfectMatching M ∧ x = indicator M := by
  obtain ⟨M, _, heq⟩ := integral_feasible_indicator
    ⟨hx.1, fun v => (hx.2 v).le⟩ hint
  refine ⟨M, (perfect_iff_degree M).mpr ?_, heq⟩
  intro v
  have h := hx.2 v
  rw [heq, load_indicator] at h
  exact_mod_cast h

/-- The allowed-edge degree relaxation is exactly the ordinary matching hull. -/
theorem matching_hull : HullSpecs.matching_hull.{u, v} := by
  intro L R _ _ G
  have h := nonnegative_tu_hull (incidence G) (fun _ => 1)
    (Networks.bipartite_incidence_tu G) (by
      have hb := matching_feasible_bounded G
      convert hb using 1
      ext x
      simp only [Int.cast_one, Set.mem_ofPred_eq]
      rfl)
  dsimp only at h
  simp only [Int.cast_one] at h
  change {x : Edge G → ℝ | (∀ e, 0 ≤ x e) ∧ ∀ v, load x v ≤ 1} =
    convexHull ℝ {x : Edge G → ℝ |
      ((∀ e, 0 ≤ x e) ∧ ∀ v, load x v ≤ 1) ∧
      ∀ e, ∃ z : ℤ, x e = (z : ℝ)} at h
  rw [h]
  congr 1
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    refine ⟨indicator_feasible hM, ?_⟩
    intro e
    rcases indicator_zero_one M e with he | he
    · exact ⟨0, by simpa using he⟩
    · exact ⟨1, by simpa using he⟩
  · rintro ⟨hx, hint⟩
    exact integral_feasible_indicator hx hint

/-- Perfect matching equality constraints include every vertex, even isolates.
Thus no perfect matching forces the entire feasible set to be empty. -/
theorem perfect_matching_hull : HullSpecs.perfect_matching_hull.{u, v} := by
  intro L R _ _ G
  have hb : Bornology.IsBounded {x : Edge G → ℝ | (∀ e, 0 ≤ x e) ∧
      (incidence G |>.map (Int.cast : ℤ → ℝ)).mulVec x = fun _ => (1 : ℝ)} := by
    convert perfect_feasible_bounded G using 1
    ext x
    simp only [Set.mem_ofPred_eq, funext_iff]
    rfl
  have h := nonnegative_eq_tu_hull (incidence G) (fun _ => 1)
    (Networks.bipartite_incidence_tu G) (by simpa only [Int.cast_one] using hb)
  have hload : {x : Edge G → ℝ | (∀ e, 0 ≤ x e) ∧
      (incidence G |>.map (Int.cast : ℤ → ℝ)).mulVec x = fun _ => (1 : ℝ)} =
      {x | (∀ e, 0 ≤ x e) ∧ ∀ v, load x v = 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, funext_iff]
    rfl
  dsimp only at h
  simp only [Int.cast_one] at h
  rw [hload] at h
  rw [h]
  congr 1
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    refine ⟨perfect_indicator_feasible hM, ?_⟩
    intro e
    rcases indicator_zero_one M e with he | he
    · exact ⟨0, by simpa using he⟩
    · exact ⟨1, by simpa using he⟩
  · rintro ⟨hx, hint⟩
    exact integral_perfect_feasible_indicator hx hint

end P205.Matching
