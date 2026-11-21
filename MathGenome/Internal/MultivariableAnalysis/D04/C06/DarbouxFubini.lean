import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SubdivisionUniformVector
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

noncomputable section
open Set
open scoped BigOperators
namespace D04.Darboux
abbrev productPoint := @Specs.D04.C06.DarbouxFubini.Model.productPoint
abbrev productBox := @Specs.D04.C06.DarbouxFubini.Model.productBox
abbrev lowerSlice := @Specs.D04.C06.DarbouxFubini.Model.lowerSlice
abbrev upperSlice := @Specs.D04.C06.DarbouxFubini.Model.upperSlice
abbrev lowerSliceReverse := @Specs.D04.C06.DarbouxFubini.Model.lowerSliceReverse
abbrev upperSliceReverse := @Specs.D04.C06.DarbouxFubini.Model.upperSliceReverse

namespace Fubini
open Specs.D04.C06.DarbouxFubini.Model (blockPoint blockBox)
variable {p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)

@[simp] theorem blockPoint_left (x : E p) (y : E q) (i : Fin p) :
    blockPoint e x y (e (.inl i)) = x i := by simp
@[simp] theorem blockPoint_right (x : E p) (y : E q) (i : Fin q) :
    blockPoint e x y (e (.inr i)) = y i := by simp

theorem blockPoint_mem {A : Box p} {B : Box q} {x : E p} {y : E q} :
    blockPoint e x y ∈ carrier (blockBox e A B) ↔ x ∈ carrier A ∧ y ∈ carrier B := by
  constructor
  · intro h
    exact ⟨fun i => by simpa [blockBox] using h (e (.inl i)),
      fun i => by simpa [blockBox] using h (e (.inr i))⟩
  · rintro ⟨hx, hy⟩ i
    obtain ⟨i, rfl⟩ := e.surjective i
    cases i with
    | inl j => simpa [blockBox] using hx j
    | inr j => simpa [blockBox] using hy j

/-- Coordinate partition data on the disjoint union of the blocks. -/
def sumGrid {A : Box p} {B : Box q} (P : Grid A) (R : Grid B) :
    ∀ j : Fin p ⊕ Fin q, SingleVariableAnalysis.Riemann.PartitionData
      (Sum.rec (fun i => A.lower i) (fun i => B.lower i) j)
      (Sum.rec (fun i => A.upper i) (fun i => B.upper i) j)
  | .inl i => P i
  | .inr i => R i

/-- A product grid, with coordinates placed by e. -/
def blockGrid {A : Box p} {B : Box q} (P : Grid A) (R : Grid B) :
    Grid (blockBox e A B) := fun i => sumGrid P R (e.symm i)

@[simp] theorem blockGrid_left {A : Box p} {B : Box q} (P : Grid A) (R : Grid B) (i : Fin p) :
    (blockGrid e P R (e (.inl i))).n = (P i).n := by
  exact congrArg (fun j => (sumGrid P R j).n) (e.symm_apply_apply _)
@[simp] theorem blockGrid_right {A : Box p} {B : Box q} (P : Grid A) (R : Grid B) (i : Fin q) :
    (blockGrid e P R (e (.inr i))).n = (R i).n := by
  exact congrArg (fun j => (sumGrid P R j).n) (e.symm_apply_apply _)


def sumIndex {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) : ∀ j : Fin p ⊕ Fin q, Fin (sumGrid P R j).n
  | .inl i => c i
  | .inr i => d i

def blockIndex {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) : CellIndex (blockGrid e P R) :=
  fun i => sumIndex P R c d (e.symm i)

@[simp] theorem blockIndex_left {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) (i : Fin p) :
    (blockIndex e P R c d (e (.inl i))).val = (c i).val := by
  exact congrArg (fun j => (sumIndex P R c d j).val) (e.symm_apply_apply _)
@[simp] theorem blockIndex_right {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) (i : Fin q) :
    (blockIndex e P R c d (e (.inr i))).val = (d i).val := by
  exact congrArg (fun j => (sumIndex P R c d j).val) (e.symm_apply_apply _)

def cellEquiv {A : Box p} {B : Box q} (P : Grid A) (R : Grid B) :
    CellIndex P × CellIndex R ≃ CellIndex (blockGrid e P R) :=
  Equiv.ofBijective (fun cd => blockIndex e P R cd.1 cd.2) (by
    constructor
    · rintro ⟨c,d⟩ ⟨c',d'⟩ h
      apply Prod.ext
      · funext i
        apply Fin.ext
        simpa using congrArg (fun t => (t (e (.inl i))).val) h
      · funext i
        apply Fin.ext
        simpa using congrArg (fun t => (t (e (.inr i))).val) h
    · intro t
      let c : CellIndex P := fun i => Fin.cast (blockGrid_left e P R i) (t (e (.inl i)))
      let d : CellIndex R := fun i => Fin.cast (blockGrid_right e P R i) (t (e (.inr i)))
      refine ⟨(c,d), ?_⟩
      funext i
      apply Fin.ext
      obtain ⟨j,rfl⟩ := e.surjective i
      cases j with
      | inl j => simp [c]
      | inr j => simp [d])

theorem blockBox_content (A : Box p) (B : Box q) :
    content (blockBox e A B) = content A * content B := by
  change (∏ i : Fin n, ((blockBox e A B).upper i - (blockBox e A B).lower i)) = _
  rw [← Equiv.prod_comp e]
  rw [Fintype.prod_sum_type]
  simp [content, Specs.D04.C06.DarbouxIntegral.Model.content]

theorem blockCellLower {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) (i : Fin n) :
    (cellBox (blockGrid e P R) (blockIndex e P R c d)).lower i =
    Sum.rec (fun j => (P j).point (c j).castSucc)
      (fun j => (R j).point (d j).castSucc) (e.symm i) := by
  change (sumGrid P R (e.symm i)).point (sumIndex P R c d (e.symm i)).castSucc = _
  cases e.symm i <;> rfl

theorem blockCellUpper {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) (i : Fin n) :
    (cellBox (blockGrid e P R) (blockIndex e P R c d)).upper i =
    Sum.rec (fun j => (P j).point (c j).succ)
      (fun j => (R j).point (d j).succ) (e.symm i) := by
  change (sumGrid P R (e.symm i)).point (sumIndex P R c d (e.symm i)).succ = _
  cases e.symm i <;> rfl

theorem blockCellBox {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) :
    cellBox (blockGrid e P R) (blockIndex e P R c d) =
      blockBox e (cellBox P c) (cellBox R d) := by
  apply Subdivision.box_ext
  · ext i
    rw [blockCellLower]
    rfl
  · ext i
    rw [blockCellUpper]
    rfl

theorem blockCellContent {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (c : CellIndex P) (d : CellIndex R) :
    cellContent (blockGrid e P R) (blockIndex e P R c d) =
      cellContent P c * cellContent R d := by
  change content (cellBox _ _) = _
  rw [blockCellBox, blockBox_content]
  rfl


/-- Dependent evaluation respects equality of the coordinate index. -/
theorem dependent_congr {ι : Sort*} {T : ι → Sort*} (v : ∀ i, T i)
    {i j : ι} (h : i = j) : HEq (v i) (v j) := by cases h; rfl

def leftGrid {A : Box p} {B : Box q} (S : Grid (blockBox e A B)) : Grid A := fun i =>
  { n := (S (e (.inl i))).n
    point := (S (e (.inl i))).point
    strictMono := (S (e (.inl i))).strictMono
    first := by simpa using (S (e (.inl i))).first
    last := by simpa using (S (e (.inl i))).last }

def rightGrid {A : Box p} {B : Box q} (S : Grid (blockBox e A B)) : Grid B := fun i =>
  { n := (S (e (.inr i))).n
    point := (S (e (.inr i))).point
    strictMono := (S (e (.inr i))).strictMono
    first := by simpa using (S (e (.inr i))).first
    last := by simpa using (S (e (.inr i))).last }

theorem partition_heq {a b a' b' : ℝ}
    (P : SingleVariableAnalysis.Riemann.PartitionData a b)
    (R : SingleVariableAnalysis.Riemann.PartitionData a' b')
    (hn : P.n = R.n) (hp : HEq P.point R.point) : HEq P R := by
  cases P with | mk n point mono first last =>
    cases R with | mk n' point' mono' first' last' =>
      dsimp at hn hp
      subst n'
      have hpt : point = point' := eq_of_heq hp
      subst point'
      have ha : a = a' := first.symm.trans first'
      have hb : b = b' := last.symm.trans last'
      cases ha
      cases hb
      rfl

/-- Every coordinate grid is a product grid, not merely a refinement of one. -/
theorem grid_decomposition {A : Box p} {B : Box q} (S : Grid (blockBox e A B)) :
    S = blockGrid e (leftGrid e S) (rightGrid e S) := by
  symm
  funext i
  obtain ⟨j,rfl⟩ := e.surjective i
  apply eq_of_heq
  cases j with
  | inl j =>
    exact (dependent_congr (sumGrid (leftGrid e S) (rightGrid e S))
      (e.symm_apply_apply (.inl j))).trans
        (partition_heq _ _ rfl HEq.rfl)
  | inr j =>
    exact (dependent_congr (sumGrid (leftGrid e S) (rightGrid e S))
      (e.symm_apply_apply (.inr j))).trans
        (partition_heq _ _ rfl HEq.rfl)

/-- Integral bounds for a bounded function; no integrability is needed. -/
theorem scalar_enclosure {k : ℕ} (Q : Box k) (h : E k → ℝ) (hb : Bounded h Q)
    {a b : ℝ} (ha : ∀ x ∈ carrier Q, a ≤ h x) (hb' : ∀ x ∈ carrier Q, h x ≤ b) :
    a * content Q ≤ lowerIntegral h Q ∧ upperIntegral h Q ≤ b * content Q := by
  obtain ⟨P⟩ := grid_exists Q
  constructor
  · apply le_trans ?_ ((lowerIntegral_isLUB h Q hb).1 ⟨P,rfl⟩)
    calc
      a * content Q = ∑ c, a * cellContent P c := by rw [← Finset.mul_sum, content_partition]
      _ ≤ lowerSum h P := by
        apply Finset.sum_le_sum
        intro c _
        apply mul_le_mul_of_nonneg_right ?_ (cellContent_nonneg P c)
        exact le_csInf ((cell_nonempty P c).image h) (by
          rintro _ ⟨x,hx,rfl⟩
          exact ha x (cell_subset P c hx))
  · apply le_trans ((upperIntegral_isGLB h Q hb).1 ⟨P,rfl⟩)
    calc
      upperSum h P ≤ ∑ c, b * cellContent P c := by
        apply Finset.sum_le_sum
        intro c _
        apply mul_le_mul_of_nonneg_right ?_ (cellContent_nonneg P c)
        exact csSup_le ((cell_nonempty P c).image h) (by
          rintro _ ⟨x,hx,rfl⟩
          exact hb' x (cell_subset P c hx))
      _ = b * content Q := by rw [← Finset.mul_sum, content_partition]

theorem slice_bounded {A : Box p} {B : Box q} {f : E n → ℝ}
    (hb : Bounded f (blockBox e A B)) {x : E p} (hx : x ∈ carrier A) :
    Bounded (fun y => f (blockPoint e x y)) B := by
  obtain ⟨M,_,hM⟩ := exists_abs_bound hb
  exact bounded_of_abs_le fun y hy => hM _ ((blockPoint_mem e).mpr ⟨hx,hy⟩)

theorem outer_bounded {A : Box p} {B : Box q} {f : E n → ℝ}
    (hb : Bounded f (blockBox e A B)) (g : E p → ℝ)
    (hl : ∀ x ∈ carrier A, lowerIntegral (fun y => f (blockPoint e x y)) B ≤ g x)
    (hu : ∀ x ∈ carrier A, g x ≤ upperIntegral (fun y => f (blockPoint e x y)) B) :
    Bounded g A := by
  obtain ⟨M,hM0,hM⟩ := exists_abs_bound hb
  apply bounded_of_abs_le (M := M * content B)
  intro x hx
  have hs := slice_bounded e hb hx
  have he := scalar_enclosure B _ hs
    (fun y hy => (abs_le.mp (hM _ ((blockPoint_mem e).mpr ⟨hx,hy⟩))).1)
    (fun y hy => (abs_le.mp (hM _ ((blockPoint_mem e).mpr ⟨hx,hy⟩))).2)
  exact abs_le.mpr ⟨by linarith [hl x hx], by linarith [hu x hx]⟩

/-- Bounds on one slice from one row of product cells. -/
theorem row_bounds {A : Box p} {B : Box q} {f : E n → ℝ}
    (hb : Bounded f (blockBox e A B)) (P : Grid A) (R : Grid B)
    (c : CellIndex P) {x : E p} (hx : x ∈ cell P c) :
    (∑ d, cellInfimum f (blockGrid e P R) (blockIndex e P R c d) * cellContent R d) ≤
      lowerIntegral (fun y => f (blockPoint e x y)) B ∧
    upperIntegral (fun y => f (blockPoint e x y)) B ≤
      ∑ d, cellSupremum f (blockGrid e P R) (blockIndex e P R c d) * cellContent R d := by
  have hs := slice_bounded e hb (cell_subset P c hx)
  have hm (d : CellIndex R) {y : E q} (hy : y ∈ cell R d) :
      blockPoint e x y ∈ cell (blockGrid e P R) (blockIndex e P R c d) := by
    change blockPoint e x y ∈ carrier (cellBox _ _)
    rw [blockCellBox]
    exact (blockPoint_mem e).mpr ⟨hx,hy⟩
  constructor
  · apply le_trans ?_ ((lowerIntegral_isLUB _ B hs).1 ⟨R,rfl⟩)
    apply Finset.sum_le_sum
    intro d _
    apply mul_le_mul_of_nonneg_right ?_ (cellContent_nonneg R d)
    apply le_csInf ((cell_nonempty R d).image _)
    rintro _ ⟨y,hy,rfl⟩
    exact cellInfimum_le f hb _ _ (hm d hy)
  · apply le_trans ((upperIntegral_isGLB _ B hs).1 ⟨R,rfl⟩)
    apply Finset.sum_le_sum
    intro d _
    apply mul_le_mul_of_nonneg_right ?_ (cellContent_nonneg R d)
    apply csSup_le ((cell_nonempty R d).image _)
    rintro _ ⟨y,hy,rfl⟩
    exact le_cellSupremum f hb _ _ (hm d hy)

/-- The finite product sum is a double sum, including empty cell types. -/
theorem block_sum {A : Box p} {B : Box q} (P : Grid A) (R : Grid B)
    (w : CellIndex (blockGrid e P R) → ℝ) :
    ∑ t, w t = ∑ c, ∑ d, w (blockIndex e P R c d) := by
  rw [← Equiv.sum_comp (cellEquiv e P R), Fintype.sum_prod_type]
  rfl

/-- The central Darboux sandwich, for any outer choice between the two slices. -/
theorem sum_sandwich {A : Box p} {B : Box q} {f : E n → ℝ}
    (hb : Bounded f (blockBox e A B)) (g : E p → ℝ)
    (hl : ∀ x ∈ carrier A, lowerIntegral (fun y => f (blockPoint e x y)) B ≤ g x)
    (hu : ∀ x ∈ carrier A, g x ≤ upperIntegral (fun y => f (blockPoint e x y)) B)
    (P : Grid A) (R : Grid B) :
    lowerSum f (blockGrid e P R) ≤ lowerSum g P ∧
    upperSum g P ≤ upperSum f (blockGrid e P R) := by
  have hg := outer_bounded e hb g hl hu
  have hs (c : CellIndex P) :
      (∑ d, cellInfimum f (blockGrid e P R) (blockIndex e P R c d) * cellContent R d) ≤
        cellInfimum g P c ∧ cellSupremum g P c ≤
      ∑ d, cellSupremum f (blockGrid e P R) (blockIndex e P R c d) * cellContent R d := by
    constructor
    · apply le_csInf ((cell_nonempty P c).image g)
      rintro _ ⟨x,hx,rfl⟩
      exact (row_bounds e hb P R c hx).1.trans (hl x (cell_subset P c hx))
    · apply csSup_le ((cell_nonempty P c).image g)
      rintro _ ⟨x,hx,rfl⟩
      exact (hu x (cell_subset P c hx)).trans (row_bounds e hb P R c hx).2
  have hlow : lowerSum f (blockGrid e P R) =
      ∑ c, (∑ d, cellInfimum f (blockGrid e P R) (blockIndex e P R c d) *
        cellContent R d) * cellContent P c := by
    change (∑ t, cellInfimum f _ t * cellContent _ t) = _
    rw [block_sum e P R]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [blockCellContent]
    ring
  have hupp : upperSum f (blockGrid e P R) =
      ∑ c, (∑ d, cellSupremum f (blockGrid e P R) (blockIndex e P R c d) *
        cellContent R d) * cellContent P c := by
    change (∑ t, cellSupremum f _ t * cellContent _ t) = _
    rw [block_sum e P R]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [blockCellContent]
    ring
  constructor
  · rw [hlow]
    exact Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_right (hs c).1 (cellContent_nonneg P c)
  · rw [hupp]
    exact Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_right (hs c).2 (cellContent_nonneg P c)


/-- Pointwise choices between the Darboux slice integrals all integrate to ∫f. -/
theorem block_fubini {A : Box p} {B : Box q} {f : E n → ℝ}
    (hf : Integrable f (blockBox e A B)) (g : E p → ℝ)
    (hl : ∀ x ∈ carrier A, lowerIntegral (fun y => f (blockPoint e x y)) B ≤ g x)
    (hu : ∀ x ∈ carrier A, g x ≤ upperIntegral (fun y => f (blockPoint e x y)) B) :
    ∃ hg : Integrable g A, integral g A hg = integral f (blockBox e A B) hf := by
  have hb := outer_bounded e hf.1 g hl hu
  have hg : Integrable g A := by
    apply (integrable_iff_gap g A hb).mpr
    intro ε hε
    obtain ⟨S,hS⟩ := (integrable_iff_gap f _ hf.1).mp hf ε hε
    rw [grid_decomposition e S] at hS
    have hh := sum_sandwich e hf.1 g hl hu (leftGrid e S) (rightGrid e S)
    exact ⟨leftGrid e S, by linarith⟩
  refine ⟨hg, ?_⟩
  apply le_antisymm
  · by_contra hnot
    have hε : 0 < integral g A hg - integral f (blockBox e A B) hf :=
      sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨S,hS⟩ := (integrable_iff_gap f _ hf.1).mp hf _ hε
    rw [grid_decomposition e S] at hS
    have hh := sum_sandwich e hf.1 g hl hu (leftGrid e S) (rightGrid e S)
    have hgB := integral_bounds g A hg (leftGrid e S)
    have hfB := integral_bounds f _ hf (blockGrid e (leftGrid e S) (rightGrid e S))
    linarith
  · by_contra hnot
    have hε : 0 < integral f (blockBox e A B) hf - integral g A hg :=
      sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨S,hS⟩ := (integrable_iff_gap f _ hf.1).mp hf _ hε
    rw [grid_decomposition e S] at hS
    have hh := sum_sandwich e hf.1 g hl hu (leftGrid e S) (rightGrid e S)
    have hgB := integral_bounds g A hg (leftGrid e S)
    have hfB := integral_bounds f _ hf (blockGrid e (leftGrid e S) (rightGrid e S))
    linarith


/-- Swap the two blocks while keeping the original ambient coordinate order. -/
def swapBlocks (p q : ℕ) : Fin q ⊕ Fin p ≃ Fin (p + q) :=
  (Equiv.sumComm _ _).trans finSumFinEquiv

@[simp] theorem blockPoint_swap (x : E p) (y : E q) :
    blockPoint (swapBlocks p q) y x = productPoint x y := by
  ext i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p+q)).surjective i
  cases j <;> simp [swapBlocks, blockPoint, productPoint,
    Specs.D04.C06.DarbouxFubini.Model.productPoint]

@[simp] theorem blockBox_swap (A : Box p) (B : Box q) :
    blockBox (swapBlocks p q) B A = productBox A B := by
  apply Subdivision.box_ext
  · exact blockPoint_swap A.lower B.lower
  · exact blockPoint_swap A.upper B.upper

theorem reverse_fubini {A : Box p} {B : Box q} {f : E (p+q) → ℝ}
    (hf : Integrable f (productBox A B)) (g : E q → ℝ)
    (hl : ∀ y ∈ carrier B, lowerIntegral (fun x => f (productPoint x y)) A ≤ g y)
    (hu : ∀ y ∈ carrier B, g y ≤ upperIntegral (fun x => f (productPoint x y)) A) :
    ∃ hg : Integrable g B, integral g B hg = integral f (productBox A B) hf := by
  have hf' : Integrable f (blockBox (swapBlocks p q) B A) := by
    rw [blockBox_swap]
    exact hf
  obtain ⟨hg,hv⟩ := block_fubini (swapBlocks p q) hf' g
    (by intro y hy; simpa only [blockPoint_swap] using hl y hy)
    (by intro y hy; simpa only [blockPoint_swap] using hu y hy)
  refine ⟨hg, ?_⟩
  change lowerIntegral g B = lowerIntegral f (productBox A B)
  change lowerIntegral g B = lowerIntegral f (blockBox (swapBlocks p q) B A) at hv
  simpa only [blockBox_swap] using hv

end Fubini

/-- Darboux Fubini at every parameter, without assuming integrable slices. -/
theorem fubini_lower_upper : Specs.D04.C06.DarbouxFubini.fubini_lower_upperType := by
  intro p q A B f hf
  have horder (x : E p) (hx : x ∈ carrier A) : lowerSlice f B x ≤ upperSlice f B x :=
    lowerIntegral_le_upperIntegral _ B (Fubini.slice_bounded finSumFinEquiv hf.1 hx)
  obtain ⟨hl,hvl⟩ := Fubini.block_fubini finSumFinEquiv hf (lowerSlice f B)
    (fun _ _ => le_rfl) horder
  obtain ⟨hu,hvu⟩ := Fubini.block_fubini finSumFinEquiv hf (upperSlice f B)
    horder (fun _ _ => le_rfl)
  exact ⟨hl,hu,hvl,hvu⟩

/-- The same assertion in the other order, on the same product box and function. -/
theorem fubini_reverse : Specs.D04.C06.DarbouxFubini.fubini_reverseType := by
  intro p q A B f hf
  have hb : Integrable f (Specs.D04.C06.DarbouxFubini.Model.blockBox
      (Fubini.swapBlocks p q) B A) := by rw [Fubini.blockBox_swap]; exact hf
  have horder (y : E q) (hy : y ∈ carrier B) :
      lowerSliceReverse f A y ≤ upperSliceReverse f A y := by
    apply lowerIntegral_le_upperIntegral
    simpa only [Fubini.blockPoint_swap] using Fubini.slice_bounded (Fubini.swapBlocks p q) hb.1 hy
  obtain ⟨hl,hvl⟩ := Fubini.reverse_fubini hf (lowerSliceReverse f A)
    (fun _ _ => le_rfl) horder
  obtain ⟨hu,hvu⟩ := Fubini.reverse_fubini hf (upperSliceReverse f A)
    horder (fun _ _ => le_rfl)
  exact ⟨hl,hu,hvl,hvu⟩

/-- Ordinary inner integrals give the same answer when every inner slice is integrable.
The outer function can be any ambient extension of those values on A. -/
theorem fubini_slices : Specs.D04.C06.DarbouxFubini.fubini_slicesType := by
  intro p q A B f hf hs g hg
  apply Fubini.block_fubini finSumFinEquiv hf g
  · intro x hx
    exact (hg x hx).ge
  · intro x hx
    change g x ≤ upperIntegral (fun y => f (productPoint x y)) B
    rw [hg x hx]
    exact (hs x hx).2.le

/-- The ordinary-slice corollary in the reversed order. -/
theorem fubini_slices_reverse : Specs.D04.C06.DarbouxFubini.fubini_slices_reverseType := by
  intro p q A B f hf hs g hg
  apply Fubini.reverse_fubini hf g
  · intro y hy
    exact (hg y hy).ge
  · intro y hy
    rw [hg y hy]
    exact (hs y hy).2.le

theorem productBox_content : Specs.D04.C06.DarbouxFubini.productBox_contentType :=
  fun A B => Fubini.blockBox_content finSumFinEquiv A B

theorem productBox_degenerate_iff : Specs.D04.C06.DarbouxFubini.productBox_degenerate_iffType := by
  intro p q A B
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p+q)).surjective i
    cases j with
    | inl j => exact Or.inl ⟨j, by simpa [productBox,
        Specs.D04.C06.DarbouxFubini.Model.productBox] using hi⟩
    | inr j => exact Or.inr ⟨j, by simpa [productBox,
        Specs.D04.C06.DarbouxFubini.Model.productBox] using hi⟩
  · rintro (⟨j,hj⟩ | ⟨j,hj⟩)
    · exact ⟨finSumFinEquiv (.inl j), by simpa [productBox,
        Specs.D04.C06.DarbouxFubini.Model.productBox] using hj⟩
    · exact ⟨finSumFinEquiv (.inr j), by simpa [productBox,
        Specs.D04.C06.DarbouxFubini.Model.productBox] using hj⟩

theorem fubini_degenerate : Specs.D04.C06.DarbouxFubini.fubini_degenerateType := by
  intro p q A B f hb hd
  have hprod := (productBox_degenerate_iff A B).mpr hd
  have hf := integrable_degenerate f (productBox A B) hb hprod
  have hz : integral f (productBox A B) hf = 0 := (degenerate_integrals f _ hprod).1
  obtain ⟨hl,hu,hvl,hvu⟩ := fubini_lower_upper A B f hf
  obtain ⟨hrl,hru,hrvl,hrvu⟩ := fubini_reverse A B f hf
  exact ⟨hf,hz,⟨hl,hu,hvl.trans hz,hvu.trans hz⟩,
    ⟨hrl,hru,hrvl.trans hz,hrvu.trans hz⟩⟩

end D04.Darboux
