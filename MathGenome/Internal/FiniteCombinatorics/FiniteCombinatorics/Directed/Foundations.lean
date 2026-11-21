import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Directed.Foundations

/-!
# Finite directed multigraphs, walks, paths, cycles, weights and divergence

This is the common original-arc interface for transfer matrices, LGV and
networks. The independent Specs module owns the canonical `Digraph`, `Arc`
and endpoint-indexed `Walk` data types; this module supplies their public
operations and verifies the interface laws. Parallel arcs and loops are never
collapsed to a relation on pairs of vertices.
-/

open scoped BigOperators

universe u v r

namespace FiniteCombinatorics.Directed

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

namespace Walk

/-- The original arcs of a walk, in order and with multiplicities. -/
def arcs {G : Digraph V A} {x y : V} (p : Walk G x y) : List A := Spec.arcs p

/-- Includes the start and the finish; the empty walk has vertex list `[x]`. -/
def vertices {G : Digraph V A} {x y : V} (p : Walk G x y) : List V := Spec.vertices p

def length {G : Digraph V A} {x y : V} (p : Walk G x y) : ℕ := Spec.length p

def append {G : Digraph V A} {x y z : V} (p : Walk G x y) (q : Walk G y z) :
    Walk G x z := Spec.append p q

def single (G : Digraph V A) (a : A) : Walk G (G.tail a) (G.head a) := Spec.single G a

/-- Vertex-simple directed path predicate, including length-zero paths. -/
def IsPath {G : Digraph V A} {x y : V} (p : Walk G x y) : Prop := Spec.isPath p

def IsClosed {G : Digraph V A} {x y : V} (p : Walk G x y) : Prop := Spec.isClosed p

/-- Positive length, with distinct vertices after removing the final base vertex. -/
def IsCycle {G : Digraph V A} {x : V} (p : Walk G x x) : Prop := Spec.isCycle p

def weight {R : Type r} [CommMonoid R] {G : Digraph V A}
    (w : A → R) {x y : V} (p : Walk G x y) : R := Spec.weight w p

variable {G : Digraph V A} {x y z t : V}

@[simp] theorem arcs_nil (x : V) : (nil (G := G) x).arcs = [] := rfl
@[simp] theorem arcs_cons (a : Arc G x y) (p : Walk G y z) :
    (cons a p).arcs = a.val :: p.arcs := rfl
@[simp] theorem vertices_nil (x : V) : (nil (G := G) x).vertices = [x] := rfl
@[simp] theorem vertices_cons (a : Arc G x y) (p : Walk G y z) :
    (cons a p).vertices = x :: p.vertices := rfl
@[simp] theorem length_nil (x : V) : (nil (G := G) x).length = 0 := rfl
@[simp] theorem length_cons (a : Arc G x y) (p : Walk G y z) :
    (cons a p).length = p.length + 1 := rfl

theorem length_eq_arcs_length (p : Walk G x y) : p.length = p.arcs.length := rfl

@[simp] theorem nil_append (p : Walk G x y) : (nil x).append p = p := rfl
@[simp] theorem cons_append (a : Arc G x y) (p : Walk G y z) (q : Walk G z t) :
    (cons a p).append q = cons a (p.append q) := rfl

@[simp] theorem append_nil (p : Walk G x y) : p.append (nil y) = p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [cons_append, ih]

theorem append_assoc (p : Walk G x y) (q : Walk G y z) (s : Walk G z t) :
    (p.append q).append s = p.append (q.append s) := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [cons_append, ih]

@[simp] theorem arcs_append (p : Walk G x y) (q : Walk G y z) :
    (p.append q).arcs = p.arcs ++ q.arcs := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [cons_append, arcs_cons, ih, List.cons_append]

@[simp] theorem length_append (p : Walk G x y) (q : Walk G y z) :
    (p.append q).length = p.length + q.length := by
  simp only [length_eq_arcs_length, arcs_append, List.length_append]

theorem vertices_ne_nil (p : Walk G x y) : p.vertices ≠ [] := by
  cases p <;> simp

theorem vertices_eq_cons (p : Walk G x y) : ∃ l : List V, p.vertices = x :: l := by
  cases p with
  | nil => exact ⟨[], rfl⟩
  | cons a p => exact ⟨p.vertices, rfl⟩

@[simp] theorem head_vertices (p : Walk G x y) : p.vertices.head? = some x := by
  obtain ⟨l, hl⟩ := vertices_eq_cons p
  simp only [hl, List.head?_cons]

@[simp] theorem getLast_vertices (p : Walk G x y) : p.vertices.getLast? = some y := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    obtain ⟨l, hl⟩ := vertices_eq_cons p
    simpa only [vertices_cons, hl, List.getLast?_cons_cons] using ih

@[simp] theorem length_vertices (p : Walk G x y) : p.vertices.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [vertices_cons, List.length_cons, length_cons, ih]

theorem vertices_append (p : Walk G x y) (q : Walk G y z) :
    (p.append q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    obtain ⟨l, hl⟩ := vertices_eq_cons p
    simp only [cons_append, vertices_cons, ih, hl, List.dropLast_cons_cons,
      List.cons_append]

/-- The arc list and vertex list agree at every step, including both incidences. -/
theorem incidence (p : Walk G x y) :
    p.arcs.map (fun a => (G.tail a, G.head a)) = p.vertices.zip p.vertices.tail := by
  induction p with
  | nil => rfl
  | @cons x y z a p ih =>
    obtain ⟨l, hl⟩ := vertices_eq_cons p
    simp only [arcs_cons, List.map_cons, vertices_cons, List.tail_cons,
      hl, List.zip_cons_cons, List.tail_cons] at *
    rw [a.property.1, a.property.2, ih]

@[simp] theorem arcs_single (a : A) : (single G a).arcs = [a] := rfl
@[simp] theorem vertices_single (a : A) :
    (single G a).vertices = [G.tail a, G.head a] := rfl
@[simp] theorem length_single (a : A) : (single G a).length = 1 := rfl

@[simp] theorem weight_nil {R : Type r} [CommMonoid R] (w : A → R) (x : V) :
    (nil (G := G) x).weight w = 1 := rfl

@[simp] theorem weight_cons {R : Type r} [CommMonoid R] (w : A → R)
    (a : Arc G x y) (p : Walk G y z) :
    (cons a p).weight w = w a.val * p.weight w := rfl

@[simp] theorem weight_single {R : Type r} [CommMonoid R] (w : A → R) (a : A) :
    (single G a).weight w = w a := by
  change w a * 1 = w a
  exact mul_one _

@[simp] theorem weight_append {R : Type r} [CommMonoid R] (w : A → R)
    (p : Walk G x y) (q : Walk G y z) :
    (p.append q).weight w = p.weight w * q.weight w := by
  change (((p.append q).arcs).map w).prod = (p.arcs.map w).prod * (q.arcs.map w).prod
  rw [arcs_append, List.map_append, List.prod_append]

@[simp] theorem nil_isPath (G : Digraph V A) (x : V) : (nil (G := G) x).IsPath := by
  simp [IsPath, Spec.isPath, Spec.vertices]

@[simp] theorem isClosed_iff (p : Walk G x y) : p.IsClosed ↔ x = y := Iff.rfl

@[simp] theorem nil_not_isCycle (G : Digraph V A) (x : V) :
    ¬ (nil (G := G) x).IsCycle := by
  simp [IsCycle, Spec.isCycle, Spec.length, Spec.arcs]

/-- One original loop is a simple directed cycle, as required in W47. -/
theorem loop_isCycle (G : Digraph V A) (x : V) (a : Arc G x x) :
    (cons a (nil x)).IsCycle := by
  simp [IsCycle, Spec.isCycle, Spec.length, Spec.arcs, Spec.vertices]

end Walk

/-- Directed paths retain their walk and its original arcs and incidence proofs. -/
def Path (G : Digraph V A) (x y : V) := Spec.path G x y

/-- Closed directed walks, with their base vertex supplied as an index. -/
def ClosedWalk (G : Digraph V A) (x : V) := Spec.closedWalk G x

/-- Based simple directed cycles. -/
def Cycle (G : Digraph V A) := Spec.cycle G

def Digraph.Acyclic (G : Digraph V A) : Prop := Spec.acyclic G

def Digraph.Reachable (G : Digraph V A) (x y : V) : Prop := Spec.reachable G x y

/-- Outgoing load minus incoming load, independently of network parameters. -/
noncomputable def Digraph.divergence (G : Digraph V A) (f : A → ℝ) (x : V) : ℝ :=
  Spec.divergence G f x

namespace Digraph

variable (G : Digraph V A)

@[simp] theorem reachable_refl (x : V) : G.Reachable x x := ⟨Walk.nil x⟩

theorem Reachable.trans {x y z : V} (h : G.Reachable x y) (h' : G.Reachable y z) :
    G.Reachable x z := by
  obtain ⟨p⟩ := h
  obtain ⟨q⟩ := h'
  exact ⟨p.append q⟩

theorem Acyclic.no_loop (h : G.Acyclic) (a : A) : G.tail a ≠ G.head a := by
  intro ha
  exact h (G.tail a) (Walk.cons ⟨a, rfl, ha.symm⟩ (Walk.nil _))
    (Walk.loop_isCycle G _ _)

open scoped Classical in
/-- An explicit outgoing/incoming sum formula usable by network consumers. -/
theorem divergence_eq (f : A → ℝ) (x : V) :
    G.divergence f x = (∑ a : A, if G.tail a = x then f a else 0) -
      ∑ a : A, if G.head a = x then f a else 0 := by
  classical
  simp [divergence, Spec.divergence, Finset.sum_filter]

end Digraph
end FiniteCombinatorics.Directed
