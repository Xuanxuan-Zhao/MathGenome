import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.HoffmanKruskal
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.IntegralVertices
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
open Matrix Set
namespace P205.Polyhedra

/-- Append the coordinate lower bounds in the shared finite-row presentation. -/
def nonnegativeMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m + n)) (Fin n) ℤ :=
  (Matrix.fromRows A (fun j => Pi.single j (-1))).submatrix finSumFinEquiv.symm id

def nonnegativeRhs {m n : ℕ} (b : Fin m → ℤ) : Fin (m + n) → ℤ :=
  Sum.elim b (fun _ : Fin n => 0) ∘ finSumFinEquiv.symm

lemma nonnegativeMatrix_tu {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    (hA : A.IsTotallyUnimodular) : (nonnegativeMatrix A).IsTotallyUnimodular := by
  have h := TotalUnimodularity.append_signed_coordinate_rows hA
    (id : Fin n → Fin n) (fun _ => -1) (fun _ => Or.inr rfl)
  exact h.submatrix finSumFinEquiv.symm id

lemma nonnegative_row_original {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x : Coordinate n) (i : Fin m) :
    rowCovector ((nonnegativeMatrix A).map (Int.cast : ℤ → ℝ)) (Fin.castAdd n i) x =
      rowCovector (A.map (Int.cast : ℤ → ℝ)) i x := by
  simp [rowCovector, nonnegativeMatrix, Matrix.fromRows, Sum.elim]

lemma nonnegative_row_coordinate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x : Coordinate n) (j : Fin n) :
    rowCovector ((nonnegativeMatrix A).map (Int.cast : ℤ → ℝ)) (Fin.natAdd m j) x =
      -x j := by
  simp [rowCovector, nonnegativeMatrix, Matrix.fromRows, Sum.elim, Pi.single_apply]

lemma nonnegativePolyhedron_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) : nonnegativePolyhedron A b =
      polyhedron ((nonnegativeMatrix A).map (Int.cast : ℤ → ℝ))
        (fun i => (nonnegativeRhs (n := n) b i : ℝ)) := by
  ext x
  constructor
  · rintro ⟨hn, hA⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [nonnegative_row_original, nonnegativeRhs] using hA i
    · intro j
      simpa [nonnegative_row_coordinate, nonnegativeRhs] using neg_nonpos.mpr (hn j)
  · intro h
    constructor
    · intro j
      have hj := h (Fin.natAdd m j)
      simpa [nonnegative_row_coordinate, nonnegativeRhs] using hj
    · intro i
      have hi := h (Fin.castAdd n i)
      simpa [nonnegative_row_original, nonnegativeRhs] using hi

/-- The forward implication is the integer-vertex theorem applied after adjoining -I. -/
theorem integral_nonnegative_vertices {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : A.IsTotallyUnimodular) (b : Fin m → ℤ) (x : Coordinate n)
    (hx : x ∈ (nonnegativePolyhedron A b).extremePoints ℝ) : IsIntegralPoint x := by
  rw [nonnegativePolyhedron_eq] at hx
  exact vertex_integral (nonnegativeMatrix A) (nonnegativeRhs b) x
    (nonnegativeMatrix_tu hA) hx


def embedCoordinates {k n : ℕ} (g : Fin k → Fin n) (u : Coordinate k) : Coordinate n :=
  ∑ t, Pi.single (g t) (u t)

lemma embedCoordinates_apply {k n : ℕ} (g : Fin k → Fin n)
    (hg : Function.Injective g) (u : Coordinate k) (t : Fin k) :
    embedCoordinates g u (g t) = u t := by
  classical
  simp [embedCoordinates, Finset.sum_apply, Pi.single_apply, hg.eq_iff]

lemma embedCoordinates_eq_zero {k n : ℕ} (g : Fin k → Fin n)
    (u : Coordinate k) (j : Fin n) (hj : j ∉ Set.range g) :
    embedCoordinates g u j = 0 := by
  classical
  simp only [embedCoordinates, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro t _
  exact Pi.single_eq_of_ne (fun h => hj ⟨t, h.symm⟩) _

lemma rowCovector_embedCoordinates {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (g : Fin k → Fin n) (u : Coordinate k) (i : Fin m) :
    rowCovector A i (embedCoordinates g u) = ∑ t, A i (g t) * u t := by
  classical
  simp [embedCoordinates, map_sum, rowCovector, Pi.single_apply, mul_ite]

lemma embedCoordinates_reconstruct {k n : ℕ} (g : Fin k → Fin n)
    (hg : Function.Injective g) (d : Coordinate n) (hd : ∀ j ∉ Set.range g, d j = 0) :
    embedCoordinates g (d ∘ g) = d := by
  ext j
  by_cases hj : j ∈ Set.range g
  · obtain ⟨t, rfl⟩ := hj
    exact embedCoordinates_apply g hg (d ∘ g) t
  · rw [embedCoordinates_eq_zero g _ j hj, hd j hj]



/-- A nonnegative solution of a nonsingular selected square system extends to a
vertex for a suitable integer right-hand side of the original inequalities. -/
lemma minor_solution_vertex {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (f : Fin k → Fin m) (g : Fin k → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hB : Function.Injective ((A.submatrix f g).map (Int.cast : ℤ → ℝ)).mulVec)
    (z : Coordinate k) (hz : ∀ t, 0 ≤ z t) (q : Fin k → ℤ)
    (hq : ((A.submatrix f g).map (Int.cast : ℤ → ℝ)) *ᵥ z = fun t => (q t : ℝ)) :
    ∃ b : Fin m → ℤ,
      embedCoordinates g z ∈ (nonnegativePolyhedron A b).extremePoints ℝ := by
  classical
  let Ar := A.map (Int.cast : ℤ → ℝ)
  let x := embedCoordinates g z
  let b := Function.extend f q (fun i => ⌈rowCovector Ar i x⌉)
  have hb (t : Fin k) : b (f t) = q t := hf.extend_apply _ _ t
  have hrow (t : Fin k) : rowCovector Ar (f t) x = (q t : ℝ) := by
    rw [rowCovector_embedCoordinates]
    exact congrFun hq t
  have hx : x ∈ nonnegativePolyhedron A b := by
    constructor
    · intro j
      by_cases hj : j ∈ Set.range g
      · obtain ⟨t, rfl⟩ := hj
        simpa [x, embedCoordinates_apply g hg] using hz t
      · rw [show x j = 0 from embedCoordinates_eq_zero g z j hj]
    · intro i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨t, rfl⟩ := hi
        exact le_of_eq ((hrow t).trans (by change (q t : ℝ) = (b (f t) : ℝ); rw [hb]))
      · change rowCovector Ar i x ≤ (b i : ℝ)
        rw [show b i = ⌈rowCovector Ar i x⌉ from Function.extend_apply' _ _ _ hi]
        exact Int.le_ceil _
  refine ⟨b, ?_⟩
  rw [nonnegativePolyhedron_eq]
  apply vertex_of_kernel_trivial _ _ x ((congrArg (fun S => x ∈ S)
    (nonnegativePolyhedron_eq A b)).mp hx)
  intro d hd
  have hoff : ∀ j ∉ Set.range g, d j = 0 := by
    intro j hj
    have hxj : x j = 0 := embedCoordinates_eq_zero g z j hj
    have hactive : Fin.natAdd m j ∈ activeRows
        ((nonnegativeMatrix A).map (Int.cast : ℤ → ℝ))
        (fun i => (nonnegativeRhs (n := n) b i : ℝ)) x := by
      change rowCovector _ _ _ = _
      simp [nonnegative_row_coordinate, nonnegativeRhs, hxj]
    have hzj := hd (Fin.natAdd m j) hactive
    simpa [nonnegative_row_coordinate] using hzj
  have hemb : embedCoordinates g (d ∘ g) = d :=
    embedCoordinates_reconstruct g hg d hoff
  have hzero : ((A.submatrix f g).map (Int.cast : ℤ → ℝ)) *ᵥ (d ∘ g) = 0 := by
    ext t
    have hactive : Fin.castAdd n (f t) ∈ activeRows
        ((nonnegativeMatrix A).map (Int.cast : ℤ → ℝ))
        (fun i => (nonnegativeRhs (n := n) b i : ℝ)) x := by
      change rowCovector _ _ _ = _
      simp only [nonnegative_row_original]
      change rowCovector Ar (f t) x = _
      rw [hrow, show nonnegativeRhs (n := n) b (Fin.castAdd n (f t)) = q t by
        simpa [nonnegativeRhs] using hb t]
    have hr := hd (Fin.castAdd n (f t)) hactive
    rw [nonnegative_row_original, ← hemb, rowCovector_embedCoordinates] at hr
    exact hr
  have hrestrict : d ∘ g = 0 := hB (hzero.trans (Matrix.mulVec_zero _).symm)
  rw [← hemb, hrestrict]
  simp [embedCoordinates]


lemma int_cast_mulVec {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℤ) (v : Fin s → ℤ) :
    (B.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (v j : ℝ)) =
      fun i => ((B *ᵥ v) i : ℝ) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]

/-- Integrality of all ambient vertices forces every solution of a selected
nonsingular system with integer right-hand side to be integral. -/
lemma minor_solution_integral {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hverts : ∀ (b : Fin m → ℤ) (x : Coordinate n),
      x ∈ (nonnegativePolyhedron A b).extremePoints ℝ → IsIntegralPoint x)
    (f : Fin k → Fin m) (g : Fin k → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hB : Function.Injective ((A.submatrix f g).map (Int.cast : ℤ → ℝ)).mulVec)
    (q : Fin k → ℤ) (u : Coordinate k)
    (hu : ((A.submatrix f g).map (Int.cast : ℤ → ℝ)) *ᵥ u = fun t => (q t : ℝ)) :
    IsIntegralPoint u := by
  let B := A.submatrix f g
  let l : Fin k → ℤ := fun t => ⌈-u t⌉
  let z := u + fun t => (l t : ℝ)
  have hz : ∀ t, 0 ≤ z t := by
    intro t
    have h := Int.le_ceil (-u t)
    change 0 ≤ u t + (⌈-u t⌉ : ℝ)
    linarith
  have hq : (B.map (Int.cast : ℤ → ℝ)) *ᵥ z =
      fun t => ((q + B *ᵥ l) t : ℝ) := by
    change (B.map (Int.cast : ℤ → ℝ)) *ᵥ (u + fun t => (l t : ℝ)) = _
    rw [Matrix.mulVec_add, hu, int_cast_mulVec]
    ext t
    simp
  obtain ⟨b, hb⟩ := minor_solution_vertex A f g hf hg hB z hz (q + B *ᵥ l) hq
  have hint := hverts b (embedCoordinates g z) hb
  intro t
  obtain ⟨r, hr⟩ := hint (g t)
  rw [embedCoordinates_apply g hg] at hr
  refine ⟨r - l t, ?_⟩
  change u t + (l t : ℝ) = (r : ℝ) at hr
  push_cast
  linarith

/-- For every integral right-hand side, vertex integrality implies that every
nonsingular square minor is a unit over the integers. -/
theorem totallyUnimodular_of_integral_nonnegative_vertices {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hverts : ∀ (b : Fin m → ℤ) (x : Coordinate n),
      x ∈ (nonnegativePolyhedron A b).extremePoints ℝ → IsIntegralPoint x) :
    A.IsTotallyUnimodular := by
  apply (TotalUnimodularity.square_minors_iff A).mpr
  intro k f g hf hg
  by_cases hdet : (A.submatrix f g).det = 0
  · exact Or.inl hdet
  · right
    let B := A.submatrix f g
    let Br := B.map (Int.cast : ℤ → ℝ)
    have hdetR : Br.det ≠ 0 := by
      rw [show Br.det = (B.det : ℝ) from (Int.cast_det B).symm]
      exact_mod_cast hdet
    have hunitR : IsUnit Br := (Br.isUnit_iff_isUnit_det).mpr
      (isUnit_iff_ne_zero.mpr hdetR)
    have hinj : Function.Injective Br.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hunitR
    have hsurj : Function.Surjective Br.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hunitR
    apply Int.isUnit_iff.mp
    apply (B.isUnit_iff_isUnit_det).mp
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    intro q
    obtain ⟨u, hu⟩ := hsurj (fun t => (q t : ℝ))
    have hint := minor_solution_integral A hverts f g hf hg hinj q u hu
    choose v hv using hint
    refine ⟨v, ?_⟩
    have huv : u = fun t => (v t : ℝ) := funext hv
    have heq : (fun t => ((B *ᵥ v) t : ℝ)) = fun t => (q t : ℝ) := by
      rw [← int_cast_mulVec, ← huv]
      exact hu
    ext t
    exact Int.cast_injective (congrFun heq t)

theorem hoffman_kruskal : HoffmanKruskalSpecs.hoffman_kruskal := by
  intro m n A
  exact ⟨fun hA => integral_nonnegative_vertices A hA,
    totallyUnimodular_of_integral_nonnegative_vertices A⟩

end P205.Polyhedra
