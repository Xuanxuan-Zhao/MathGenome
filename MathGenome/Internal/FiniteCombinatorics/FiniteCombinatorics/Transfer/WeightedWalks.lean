import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Directed.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Transfer.GeometricMatrixSeries
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Transfer.WeightedWalks

/-!
# Weighted walks and transfer matrices

The walk assertion of `paper.tex`, p204:W17 (lines 550–571). The induction
splits a nonempty walk at its first arc. The disjointness and injectivity
lemmas ensure that the finite-set sums count every original-arc walk once.
The accepted geometric-series theorem then identifies each inverse entry
with the OGF of these sums. All coefficient rings are commutative rings;
empty vertex/arc types, loops and parallel arcs are allowed.
-/

noncomputable section
open scoped BigOperators Classical
universe u v r
namespace FiniteCombinatorics.Transfer
open _root_.FiniteCombinatorics.Directed

/-- All walks of the given length, retaining original arc identities. -/
def walks {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (n : ℕ) (x y : V) : Finset (Walk G x y) :=
  Specs.FiniteCombinatorics.Transfer.WeightedWalks.walks G n x y

/-- The weighted adjacency matrix of a finite directed multigraph. -/
def adjacency {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    {R : Type r} [CommRing R] (G : Digraph V A) (w : A → R) : Matrix V V R :=
  fun x y => ∑ a : Arc G x y, w a.val

/-- Ordinary generating series of the sums of walk weights. -/
def walkSeries {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    {R : Type r} [CommRing R] (G : Digraph V A) (w : A → R) (x y : V) :
    PowerSeries R := Series.ogf (fun n => ∑ p ∈ walks G n x y, p.weight w)

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable {G : Digraph V A} {x y z : V}

private theorem cons_injective (a : Arc G x z) :
    Function.Injective (Walk.cons (z := y) a) := by
  intro p q h
  cases h
  rfl

private theorem cons_first_eq {z' : V} (a : Arc G x z) (b : Arc G x z')
    (p : Walk G z y) (q : Walk G z' y) (h : Walk.cons a p = Walk.cons b q) :
    a.val = b.val := by
  have := congrArg Walk.arcs h
  exact (List.cons.inj this).1

/-- The recursive enumeration includes exactly all walks of length `n`. -/
theorem mem_walks (G : Digraph V A) (n : ℕ) (x y : V) (p : Walk G x y) :
    p ∈ walks G n x y ↔ p.length = n := by
  classical
  induction n generalizing x y with
  | zero =>
    unfold walks Specs.FiniteCombinatorics.Transfer.WeightedWalks.walks
    split_ifs with h
    · subst y
      cases p with
      | nil => simp
      | cons a p => simp
    · cases p with
      | nil => exact (h rfl).elim
      | cons a p => simp
  | succ n ih =>
    change p ∈ Finset.univ.biUnion (fun z : V =>
      Finset.univ.biUnion (fun a : Arc G x z =>
        (walks G n z y).image (Walk.cons a))) ↔ p.length = n + 1
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨z, a, q, hq, rfl⟩
      simpa using (ih z y q).mp hq
    · intro hp
      cases p with
      | nil => simp at hp
      | @cons x z y a p =>
        refine ⟨z, a, p, ?_, rfl⟩
        apply (ih z y p).mpr
        simpa using hp

private theorem disjoint_arcs (n : ℕ) (z : V) :
    (↑(Finset.univ : Finset (Arc G x z)) : Set (Arc G x z)).PairwiseDisjoint
      (fun a => (walks G n z y).image (Walk.cons a)) := by
  classical
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hp
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hq
  apply hab
  exact Subtype.ext (cons_first_eq a b p q (hp.trans hq.symm))

private theorem disjoint_vertices (n : ℕ) :
    (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint
      (fun z => Finset.univ.biUnion (fun a : Arc G x z =>
        (walks G n z y).image (Walk.cons a))) := by
  classical
  intro z _ z' _ hzz
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, _, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨b, _, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hp
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hq
  exact hzz (Walk.cons.inj (hp.trans hq.symm)).1

variable {R : Type r} [CommRing R]

/-- Each empty walk contributes one, and unequal endpoints have none. -/
theorem sum_weights_zero (G : Digraph V A) (w : A → R) (x y : V) :
    (∑ p ∈ walks G 0 x y, p.weight w) = if x = y then 1 else 0 := by
  classical
  unfold walks Specs.FiniteCombinatorics.Transfer.WeightedWalks.walks
  split_ifs with h
  · subst y
    simp
  · simp

/-- Partition by first vertex after the start, and by original first arc. -/
theorem sum_weights_succ (G : Digraph V A) (w : A → R) (n : ℕ) (x y : V) :
    (∑ p ∈ walks G (n + 1) x y, p.weight w) =
      ∑ z : V, (∑ a : Arc G x z, w a.val) *
        ∑ p ∈ walks G n z y, p.weight w := by
  classical
  change (∑ p ∈ Finset.univ.biUnion (fun z : V =>
    Finset.univ.biUnion (fun a : Arc G x z =>
      (walks G n z y).image (Walk.cons a))), p.weight w) = _
  rw [Finset.sum_biUnion (disjoint_vertices n)]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_biUnion (disjoint_arcs n z), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_image (fun p _ q _ h => cons_injective a h)]
  simp only [Walk.weight_cons, Finset.mul_sum]

/-- Transfer matrix powers enumerate all fixed-length walks with their weights. -/
theorem pow_adjacency [DecidableEq V] (G : Digraph V A) (w : A → R)
    (n : ℕ) (x y : V) :
    (adjacency G w ^ n) x y = ∑ p ∈ walks G n x y, p.weight w := by
  induction n generalizing x y with
  | zero => simp [Matrix.one_apply, sum_weights_zero]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, sum_weights_succ]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih]
    rfl

/-- The resolvent's coefficient is the total weight of all `n`-step walks. -/
theorem coeff_geometric_walks [DecidableEq V] (G : Digraph V A) (w : A → R)
    (n : ℕ) (x y : V) :
    PowerSeries.coeff n (geometricSeries (adjacency G w) x y) =
      ∑ p ∈ walks G n x y, p.weight w := by
  rw [coeff_geometricSeries, pow_adjacency]

/-- Each entry of the geometric inverse is the OGF of weighted walks. -/
theorem geometricSeries_eq_walkSeries [DecidableEq V] (G : Digraph V A)
    (w : A → R) (x y : V) :
    geometricSeries (adjacency G w) x y = walkSeries G w x y := by
  apply PowerSeries.ext
  intro n
  rw [coeff_geometric_walks, walkSeries, Series.coeff_ogf]

end FiniteCombinatorics.Transfer
