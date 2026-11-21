import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.PathAlgebra

/-! The path algebra, its vertex idempotents, and its corner bases. -/

open scoped BigOperators Classical
open Module

universe u v w

namespace RM03

/-- The total arrow type of the quiver defined by `s,t` is the original arrow type. -/
def arrowsEquiv {V : Type u} {E : Type v} (s t : E → V) :
    @Arrow V (quiverOfArrows s t) ≃ E where
  toFun a := a.2.2.1
  invFun a := ⟨s a, t a, ⟨a, rfl, rfl⟩⟩
  left_inv := by
    rintro ⟨i, j, a, rfl, rfl⟩
    rfl
  right_inv _ := rfl

theorem arrows_equiv_endpoints : PathAlgebraSpec.ArrowData := by
  intro V E s t
  exact ⟨arrowsEquiv s t, fun a => a.2.2.property⟩

theorem finite_arrowsOfMaps {V : Type u} {E : Type v} [Finite E] (s t : E → V) :
    Finite (@Arrow V (quiverOfArrows s t)) :=
  Finite.of_injective _ (arrowsEquiv s t).injective

namespace Path

variable {V : Type u} [Quiver.{v} V]

@[simp] theorem source_ofPath {i j : V} (p : Quiver.Path i j) :
    (ofPath p).source = i := rfl

@[simp] theorem target_ofPath {i j : V} (p : Quiver.Path i j) :
    (ofPath p).target = j := rfl

@[simp] theorem length_ofPath {i j : V} (p : Quiver.Path i j) :
    (ofPath p).length = p.length := rfl

@[simp] theorem source_vertex (i : V) : (vertex i : Path V).source = i := rfl

@[simp] theorem target_vertex (i : V) : (vertex i : Path V).target = i := rfl

@[simp] theorem length_vertex (i : V) : (vertex i : Path V).length = 0 := rfl

@[simp] theorem source_arrow {i j : V} (a : Quiver.Hom i j) : (arrow a).source = i := rfl

@[simp] theorem target_arrow {i j : V} (a : Quiver.Hom i j) : (arrow a).target = j := rfl

@[simp] theorem length_arrow {i j : V} (a : Quiver.Hom i j) : (arrow a).length = 1 := rfl

@[simp] theorem source_concat (p q : Path V) (h : p.source = q.target) :
    (p.concat q h).source = q.source := rfl

@[simp] theorem target_concat (p q : Path V) (h : p.source = q.target) :
    (p.concat q h).target = p.target := rfl

@[simp] theorem length_concat (p q : Path V) (h : p.source = q.target) :
    (p.concat q h).length = q.length + p.length := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  change a = d at h
  subst d
  exact q.length_comp p

@[simp] theorem concat_ofPath {i j l : V} (p : Quiver.Path j l) (q : Quiver.Path i j) :
    (ofPath p).concat (ofPath q) rfl = ofPath (q.comp p) := rfl

theorem concat_assoc (p q r : Path V) (hpq : p.source = q.target)
    (hqr : q.source = r.target) :
    (p.concat q hpq).concat r hqr = p.concat (q.concat r hqr) hpq := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  rcases r with ⟨e, f, r⟩
  change a = d at hpq
  change c = f at hqr
  subst d
  subst f
  exact congrArg ofPath (r.comp_assoc q p).symm

@[simp] theorem vertex_concat (p : Path V) (i : V) (h : i = p.target) :
    (vertex i).concat p h = p := by
  rcases p with ⟨a, b, p⟩
  change i = b at h
  subst i
  rfl

@[simp] theorem concat_vertex (p : Path V) (i : V) (h : p.source = i) :
    p.concat (vertex i) h = p := by
  rcases p with ⟨a, b, p⟩
  change a = i at h
  subst i
  exact congrArg ofPath (Quiver.Path.nil_comp p)

end Path

/-- The path algebra over `k`, with one coefficient for each path. -/
abbrev PathAlgebra (k : Type w) (V : Type u) [Quiver.{v} V] [Zero k] :=
  PathAlgebraSpec.Carrier k V

namespace PathAlgebra

variable (k : Type w) (V : Type u) [Quiver.{v} V] [Field k]

noncomputable section

/-- The basis indexed by all paths. -/
def basis : Basis (Path V) k (PathAlgebra k V) := PathAlgebraSpec.basis k V

variable {V}

/-- A path included as its basis vector in the path algebra. -/
def ofPath (p : Path V) : PathAlgebra k V := PathAlgebraSpec.ofPath k V p

/-- The basis vector of the trivial path at a vertex. -/
def vertex (i : V) : PathAlgebra k V := PathAlgebraSpec.vertex k V i

/-- The basis vector of a length-one path. -/
def arrow {i j : V} (a : Quiver.Hom i j) : PathAlgebra k V := PathAlgebraSpec.arrow k V a

variable (V)

/-- Multiplication as a bilinear map. The right argument is traversed first. -/
def mulBilinear : PathAlgebra k V →ₗ[k] PathAlgebra k V →ₗ[k] PathAlgebra k V :=
  PathAlgebraSpec.mul k V

variable {k V}

@[simp] theorem basis_apply (p : Path V) : basis k V p = ofPath k p :=
  congrFun Finsupp.coe_basisSingleOne p

instance [Nonempty V] : Nontrivial (PathAlgebra k V) := by
  obtain ⟨i⟩ := ‹Nonempty V›
  exact ⟨⟨basis k V (Path.vertex i), 0, (basis k V).ne_zero _⟩⟩

theorem vertex_eq_ofPath (i : V) : vertex k i = ofPath k (Path.vertex i) := rfl

theorem arrow_eq_ofPath {i j : V} (a : Quiver.Hom i j) :
    arrow k a = ofPath k (Path.arrow a) := rfl

theorem mulBilinear_apply (x y : PathAlgebra k V) : mulBilinear k V x y = x * y := rfl

theorem ofPath_mul_ofPath (p q : Path V) : ofPath k p * ofPath k q =
    if h : p.source = q.target then ofPath k (p.concat q h) else 0 := by
  change (PathAlgebraSpec.mul k V) (ofPath k p) (ofPath k q) = _
  rw [← basis_apply p, ← basis_apply q]
  change ((basis k V).constr k (fun p => (basis k V).constr k fun q =>
    if h : p.source = q.target then ofPath k (p.concat q h) else 0))
    (basis k V p) (basis k V q) = _
  rw [Basis.constr_basis, Basis.constr_basis]

@[simp] theorem ofPath_mul_comp {i j l : V} (p : Quiver.Path j l) (q : Quiver.Path i j) :
    ofPath k (Path.ofPath p) * ofPath k (Path.ofPath q) = ofPath k (Path.ofPath (q.comp p)) := by
  simp [ofPath_mul_ofPath]

@[simp] theorem ofPath_cons {i j l : V} (p : Quiver.Path i j) (a : Quiver.Hom j l) :
    arrow k a * ofPath k (Path.ofPath p) = ofPath k (Path.ofPath (p.cons a)) :=
  ofPath_mul_comp (Quiver.Hom.toPath a) p

@[simp] theorem vertex_mul_ofPath (i : V) (p : Path V) :
    vertex k i * ofPath k p = if i = p.target then ofPath k p else 0 := by
  change ofPath k (Path.vertex i) * ofPath k p = _
  rw [ofPath_mul_ofPath]
  by_cases h : i = p.target
  · rw [dite_eq_left (show (Path.vertex i : Path V).source = p.target from h),
      ite_eq_left h, Path.vertex_concat]
  · rw [dite_eq_right (show (Path.vertex i : Path V).source ≠ p.target from h),
      ite_eq_right h]

@[simp] theorem ofPath_mul_vertex (p : Path V) (i : V) :
    ofPath k p * vertex k i = if p.source = i then ofPath k p else 0 := by
  change ofPath k p * ofPath k (Path.vertex i) = _
  rw [ofPath_mul_ofPath]
  by_cases h : p.source = i
  · rw [dite_eq_left (show p.source = (Path.vertex i : Path V).target from h),
      ite_eq_left h, Path.concat_vertex]
  · rw [dite_eq_right (show p.source ≠ (Path.vertex i : Path V).target from h),
      ite_eq_right h]

private theorem assoc_basis (p q r : Path V) :
    (ofPath k p * ofPath k q) * ofPath k r = ofPath k p * (ofPath k q * ofPath k r) := by
  have hm₀ (x : PathAlgebra k V) : x * 0 = 0 := (mulBilinear k V x).map_zero
  have h₀m (x : PathAlgebra k V) : 0 * x = 0 := ((mulBilinear k V).flip x).map_zero
  by_cases hpq : p.source = q.target <;> by_cases hqr : q.source = r.target <;>
    simp [ofPath_mul_ofPath, hpq, hqr, hm₀, h₀m]
  exact congrArg (ofPath k) (Path.concat_assoc p q r hpq hqr)

theorem mul_assoc (x y z : PathAlgebra k V) : (x * y) * z = x * (y * z) := by
  let A := PathAlgebra k V
  let m := mulBilinear k V
  let left : A →ₗ[k] A →ₗ[k] A →ₗ[k] A := m.compr₂ₛₗ m
  let right : A →ₗ[k] A →ₗ[k] A →ₗ[k] A := (LinearMap.llcomp k A A A).compl₁₂ m m
  have h : left = right := by
    apply (basis k V).ext
    intro p
    apply (basis k V).ext
    intro q
    apply (basis k V).ext
    intro r
    change (basis k V p * basis k V q) * basis k V r =
      basis k V p * (basis k V q * basis k V r)
    simpa using (assoc_basis (k := k) p q r)
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun h x) y) z

@[simp] theorem vertex_idempotent (i : V) : vertex k i * vertex k i = vertex k i :=
  by
    change vertex k i * ofPath k (Path.vertex i) = ofPath k (Path.vertex i)
    simp

theorem vertex_orthogonal (i j : V) (h : i ≠ j) : vertex k i * vertex k j = 0 :=
  by
    change vertex k i * ofPath k (Path.vertex j) = 0
    simp [h]

section FiniteVertices

variable [Fintype V]

theorem sum_vertices : (∑ i : V, vertex k i) = (1 : PathAlgebra k V) := rfl

private theorem one_mul_basis (p : Path V) : (1 : PathAlgebra k V) * ofPath k p = ofPath k p := by
  rw [← sum_vertices]
  change (mulBilinear k V).flip (ofPath k p) (∑ i : V, vertex k i) = _
  rw [map_sum]
  change (∑ i : V, vertex k i * ofPath k p) = _
  simp [vertex_mul_ofPath]

private theorem mul_one_basis (p : Path V) : ofPath k p * (1 : PathAlgebra k V) = ofPath k p := by
  rw [← sum_vertices]
  change mulBilinear k V (ofPath k p) (∑ i : V, vertex k i) = _
  rw [map_sum]
  change (∑ i : V, ofPath k p * vertex k i) = _
  simp [ofPath_mul_vertex]

theorem unit_laws (x : PathAlgebra k V) :
    (1 : PathAlgebra k V) * x = x ∧ x * 1 = x := by
  have hl : mulBilinear k V 1 = LinearMap.id := (basis k V).ext fun p => by
    rw [basis_apply]
    exact one_mul_basis p
  have hr : (mulBilinear k V).flip 1 = LinearMap.id := (basis k V).ext fun p => by
    rw [basis_apply]
    exact mul_one_basis p
  exact ⟨DFunLike.congr_fun hl x, DFunLike.congr_fun hr x⟩

instance : Ring (PathAlgebra k V) where
  __ := (inferInstance : AddCommGroup (PathAlgebra k V))
  __ := (inferInstance : Mul (PathAlgebra k V))
  __ := (inferInstance : One (PathAlgebra k V))
  mul_assoc := mul_assoc
  zero_mul x := ((mulBilinear k V).flip x).map_zero
  mul_zero x := (mulBilinear k V x).map_zero
  one_mul x := (unit_laws x).1
  mul_one x := (unit_laws x).2
  left_distrib x y z := (mulBilinear k V x).map_add y z
  right_distrib x y z := ((mulBilinear k V).flip z).map_add x y

instance : Algebra k (PathAlgebra k V) :=
  Algebra.ofModule (R := k) (A := PathAlgebra k V)
    (fun c x y => ((mulBilinear k V).flip y).map_smul c x)
    (fun c x y => (mulBilinear k V x).map_smul c y)

/-- The structure map sends a scalar to that scalar times the sum of the vertices. -/
theorem algebraMap_apply (c : k) :
    algebraMap k (PathAlgebra k V) c = c • (1 : PathAlgebra k V) := rfl

end FiniteVertices

theorem has_algebra_structure : PathAlgebraSpec.AlgebraStructure := by
  intro k V _ _ _
  exact ⟨instRing, rfl, rfl, rfl, instAlgebra, rfl, fun _ => rfl⟩

variable (k)

/-- The subspace `e_j (kQ) e_i`. -/
def corner (i j : V) : Submodule k (PathAlgebra k V) := PathAlgebraSpec.corner k V i j

variable {k}

theorem mem_corner (i j : V) (x : PathAlgebra k V) :
    x ∈ corner k i j ↔ ∃ y : PathAlgebra k V, vertex k j * y * vertex k i = x := by
  change (∃ y : PathAlgebra k V, vertex k j * (y * vertex k i) = x) ↔ _
  simp only [mul_assoc]

theorem vertex_mul_ofPath_mul_vertex (i j : V) (p : Path V) :
    vertex k j * ofPath k p * vertex k i =
      if p.source = i ∧ p.target = j then ofPath k p else 0 := by
  have h₀m (x : PathAlgebra k V) : 0 * x = 0 := ((mulBilinear k V).flip x).map_zero
  by_cases hs : p.source = i <;> by_cases ht : j = p.target <;>
    simp [hs, ht, eq_comm (a := p.target), h₀m]

theorem corner_eq_span (i j : V) :
    corner k i j =
      Submodule.span k (Set.range (fun p : Quiver.Path i j => ofPath k (Path.ofPath p))) := by
  let sandwich := (mulBilinear k V (vertex k j)).comp ((mulBilinear k V).flip (vertex k i))
  let paths := Set.range (fun p : Quiver.Path i j => ofPath k (Path.ofPath p))
  change LinearMap.range sandwich = Submodule.span k paths
  rw [← Submodule.map_top, ← (basis k V).span_eq, Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    change vertex k j * (basis k V p * vertex k i) ∈ Submodule.span k paths
    rw [basis_apply, ← mul_assoc, vertex_mul_ofPath_mul_vertex]
    by_cases h : p.source = i ∧ p.target = j
    · rcases p with ⟨a, b, p⟩
      obtain ⟨rfl, rfl⟩ := h
      simp only [eq_self, and_self, ite_true]
      exact Submodule.subset_span ⟨p, rfl⟩
    · rw [ite_eq_right h]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply Submodule.subset_span
    refine ⟨basis k V (Path.ofPath p), ⟨Path.ofPath p, rfl⟩, ?_⟩
    change vertex k j * (basis k V (Path.ofPath p) * vertex k i) = _
    rw [basis_apply, ← mul_assoc, vertex_mul_ofPath_mul_vertex]
    simp

private theorem cornerPaths_independent (i j : V) :
    LinearIndependent k (fun p : Quiver.Path i j => ofPath k (Path.ofPath p)) := by
  simpa only [Function.comp_def, basis_apply] using
    (basis k V).linearIndependent.comp (fun p : Quiver.Path i j => Path.ofPath p)
      (fun _ _ h => by cases h; rfl)

/-- The basis of a corner indexed by the paths from its right vertex to its left vertex. -/
def cornerBasis (i j : V) : Basis (Quiver.Path i j) k (corner k i j) :=
  (Basis.span (cornerPaths_independent i j)).map (LinearEquiv.ofEq _ _ (corner_eq_span i j).symm)

@[simp] theorem cornerBasis_apply (i j : V) (p : Quiver.Path i j) :
    (cornerBasis (k := k) i j p : PathAlgebra k V) = ofPath k (Path.ofPath p) := by
  simp [cornerBasis]

theorem corner_has_basis (i j : V) : ∃ b : Basis (Quiver.Path i j) k (corner k i j),
    ∀ p, (b p : PathAlgebra k V) = ofPath k (Path.ofPath p) :=
  ⟨cornerBasis i j, cornerBasis_apply i j⟩

end
end PathAlgebra
end RM03
