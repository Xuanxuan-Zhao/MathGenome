import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.WeightedFixedColorings
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.FixedColorings
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.GroupAction.Defs

namespace FiniteCombinatorics.Action
open scoped BigOperators
universe u v w z
variable (G : Type u) (X : Type v) (C : Type w) [Group G] [MulAction G X]
attribute [local instance] coloringAction Classical.propDecidable
variable [Fintype X]

/-- Reindexing the positions leaves any product of color weights unchanged. -/
theorem prod_colorWeight_smul {R : Type z} [CommMonoid R] (w : C → R)
    (g : G) (f : X → C) :
    (∏ x, w ((g • f) x)) = ∏ x, w (f x) := by
  classical
  exact Equiv.prod_comp (MulAction.toPerm g⁻¹) (fun x => w (f x))

/-- The product of a fixed coloring's weights, grouped into complete cycles. -/
theorem prod_colorWeight_cycles {R : Type z} [CommMonoid R] (w : C → R)
    (g : G) (f : fixedColorings G X C g) :
    (∏ x, w (f.val x)) =
      ∏ D : ↥(cycles G X g), w (fixedColoringsEquiv G X C g f D) ^ D.val.card := by
  classical
  calc
    _ = ∏ D ∈ cycles G X g, ∏ x ∈ D, w (f.val x) := by
      simpa only [id_eq, cycles_cover] using
        (Finset.prod_biUnion (f := fun x => w (f.val x))
          (cycles_pairwise_disjoint G X g))
    _ = ∏ D : ↥(cycles G X g), ∏ x ∈ D.val, w (f.val x) :=
      (Finset.prod_coe_sort _ _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro D _
      calc
        _ = ∏ _x ∈ D.val, w (fixedColoringsEquiv G X C g f D) := by
          apply Finset.prod_congr rfl
          intro x hx
          rw [fixedColoringsEquiv_apply G X C g f D x hx]
        _ = _ := by simp

/-- Group one contribution for each complete cycle by its positive length. -/
theorem prod_cycles_by_length {R : Type z} [CommMonoid R] (g : G) (a : ℕ → R) :
    (∏ D : ↥(cycles G X g), a D.val.card) =
      ∏ k ∈ Finset.Icc 1 (Fintype.card X), a k ^ countCycles G X g k := by
  classical
  rw [Finset.prod_coe_sort (cycles G X g) (fun D => a D.card)]
  symm
  calc
    _ = ∏ k ∈ Finset.Icc 1 (Fintype.card X),
        ∏ D ∈ (cycles G X g).filter (fun D => D.card = k), a D.card := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Finset.prod_congr rfl (fun D hD => congrArg a (Finset.mem_filter.mp hD).2)]
      simp only [Finset.prod_const]
      rfl
    _ = _ := Finset.prod_fiberwise_of_maps_to
      (fun D hD => Finset.mem_Icc.mpr (cycleLength_bounds G X g D hD)) _

/-- A finite color set makes the fixed-coloring type finite. -/
noncomputable instance fixedColoringsFintype [Fintype C] (g : G) :
    Fintype (fixedColorings G X C g) :=
  Fintype.ofEquiv (↥(cycles G X g) → C) (fixedColoringsEquiv G X C g).symm

/-- Finite distributivity over the independently chosen cycle colors. -/
theorem sum_fixed_colorWeight [Fintype C] {R : Type z} [CommSemiring R]
    (w : C → R) (g : G) :
    (∑ f : fixedColorings G X C g, ∏ x, w (f.val x)) =
      ∏ k ∈ Finset.Icc 1 (Fintype.card X),
        (∑ c, w c ^ k) ^ countCycles G X g k := by
  classical
  calc
    _ = ∑ a : ↥(cycles G X g) → C,
        ∏ D : ↥(cycles G X g), w (a D) ^ D.val.card := by
      exact Fintype.sum_equiv (fixedColoringsEquiv G X C g) _ _
        (fun f => prod_colorWeight_cycles G X C w g f)
    _ = ∏ D : ↥(cycles G X g), ∑ c : C, w c ^ D.val.card :=
      (Fintype.prod_sum (fun (D : ↥(cycles G X g)) (c : C) =>
        w c ^ D.val.card)).symm
    _ = _ := prod_cycles_by_length G X g (fun k => ∑ c : C, w c ^ k)

/-- The integral monomial recording a coloring's color multiplicities. -/
noncomputable def coloringWeight (f : X → C) : MvPolynomial C ℕ :=
  ∏ x, MvPolynomial.X (f x)

@[simp] theorem coloringWeight_smul (g : G) (f : X → C) :
    coloringWeight X C (g • f) = coloringWeight X C f :=
  prod_colorWeight_smul G X C MvPolynomial.X g f

noncomputable def orbitWeight (O : MulAction.orbitRel.Quotient G (X → C)) :
    MvPolynomial C ℕ := coloringWeight X C O.out

@[simp] theorem orbitWeight_mk (f : X → C) :
    orbitWeight G X C (Quotient.mk (MulAction.orbitRel G (X → C)) f) =
      coloringWeight X C f := by
  have h := Quotient.exact (Quotient.out_eq
    (Quotient.mk (MulAction.orbitRel G (X → C)) f))
  obtain ⟨g, hg⟩ := h
  change coloringWeight X C _ = _
  rw [← hg, coloringWeight_smul]

noncomputable def fixedWeightSum [Fintype C] (g : G) : MvPolynomial C ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f : X → C => g • f = f), coloringWeight X C f

theorem fixedWeightSum_factorization [Fintype C] (g : G) :
    fixedWeightSum G X C g =
      ∏ k ∈ Finset.Icc 1 (Fintype.card X),
        (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℕ) ^ k) ^
          countCycles G X g k := by
  classical
  have hsum : fixedWeightSum G X C g =
      ∑ f : fixedColorings G X C g, ∏ x, (MvPolynomial.X (f.val x) : MvPolynomial C ℕ) := by
    unfold fixedWeightSum coloringWeight
    exact Finset.sum_subtype (p := fun f : X → C => g • f = f)
      _ (by intro f; simp) _
  rw [hsum]
  exact sum_fixed_colorWeight G X C MvPolynomial.X g

@[simp] theorem coloringWeight_empty [IsEmpty X] (f : X → C) :
    coloringWeight X C f = 1 := by
  simp [coloringWeight]

@[simp] theorem fixedWeightSum_empty_positions [Fintype C] [IsEmpty X] (g : G) :
    fixedWeightSum G X C g = 1 := by
  rw [fixedWeightSum_factorization]
  simp

@[simp] theorem fixedWeightSum_empty_colors [Fintype C] [Nonempty X] [IsEmpty C]
    (g : G) : fixedWeightSum G X C g = 0 := by
  classical
  simp [fixedWeightSum]

end FiniteCombinatorics.Action
