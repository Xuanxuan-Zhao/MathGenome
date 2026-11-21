import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtModules
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.RowColumnTest
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.ColumnAlternation

noncomputable section
open scoped BigOperators ComplexConjugate
namespace AdvancedFiniteGroupRepresentations
variable {n : ℕ} {p q : Partition n}

/-- Expansion of the group-algebra action on any shape. -/
theorem columnAlternator_action_sum (t : Tableau p) (x : PermutationModule q) :
    groupAlgebraAction q (columnAlternator t) x =
      ∑ c : columnSubgroup t, permutationSign c.val • permutationRepresentation q c.val x := by
  simp only [columnAlternator, Specs.AdvancedFiniteGroupRepresentations.columnAlternator,
    map_sum, LinearMap.sum_apply, groupAlgebraAction_single]

/-- Right multiplication of the alternator by a column permutation. -/
theorem columnAlternator_right (t : Tableau p) (c : columnSubgroup t)
    (x : PermutationModule q) :
    groupAlgebraAction q (columnAlternator t) (permutationRepresentation q c.val x) =
      permutationSign c.val • groupAlgebraAction q (columnAlternator t) x := by
  classical
  rw [columnAlternator_action_sum, columnAlternator_action_sum, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulRight c)
  intro d
  change permutationSign d.val • (permutationRepresentation q d.val
      (permutationRepresentation q c.val x)) =
    permutationSign c.val • (permutationSign (d.val * c.val) •
      permutationRepresentation q (d.val * c.val) x)
  rw [permutationSign_mul, smul_smul]
  have hs : permutationSign c.val * (permutationSign d.val * permutationSign c.val) =
      permutationSign d.val := by
    rw [mul_left_comm, permutationSign_sq, mul_one]
  rw [hs, map_mul, Module.End.mul_apply]

private theorem fiber_swap {α ι : Type*} [DecidableEq α] (f : α → ι) {a b : α}
    (h : f a = f b) (x : α) : f (Equiv.swap a b x) = f x := by
  by_cases ha : x = a
  · subst x; simpa using h.symm
  by_cases hb : x = b
  · subst x; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A collision transposition has sign -1 and fixes the input tabloid. -/
theorem columnAlternator_collision (t : Tableau p) (u : Tableau q)
    (h : RowColumnCollision t u) :
    groupAlgebraAction q (columnAlternator t) (MonoidAlgebra.single (tabloid u) 1) = 0 := by
  classical
  obtain ⟨a, b, hab, hc, hr⟩ := h
  let c : columnSubgroup t := ⟨Equiv.swap a b, fiber_swap (labelColumn t) hc⟩
  have hfix : c.val • tabloid u = tabloid u := by
    rw [tabloid_smul]
    apply Quotient.sound
    funext x
    change labelRow u ((Equiv.swap a b).symm x) = labelRow u x
    simpa only [Equiv.symm_swap] using fiber_swap (labelRow u) hr x
  have hsign : permutationSign c.val = -1 := by
    simp [c, permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign,
      Equiv.Perm.sign_swap hab]
  have hh := columnAlternator_right t c (MonoidAlgebra.single (tabloid u) 1)
  rw [permutationRepresentation_basis, hfix, hsign, neg_one_smul] at hh
  have hz : (2 : ℂ) • groupAlgebraAction q (columnAlternator t)
      (MonoidAlgebra.single (tabloid u) 1) = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp hh)
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem columnAlternator_column_tabloid (t : Tableau p) (c : columnSubgroup t) :
    groupAlgebraAction p (columnAlternator t)
      (MonoidAlgebra.single (tabloid (c.val • t)) 1) =
        permutationSign c.val • polytabloid t := by
  rw [← tabloid_smul, ← permutationRepresentation_basis,
    columnAlternator_right]
  rfl

@[simp] theorem permutationSign_conj (g : SymmetricGroup n) :
    conj (permutationSign g) = permutationSign g := by
  simp [permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign]

/-- Coordinates of the alternating action, with the inverse required by a left action. -/
theorem columnAlternator_coeff (t : Tableau p) (x : PermutationModule q) (r : Tabloid q) :
    (groupAlgebraAction q (columnAlternator t) x).coeff r =
      ∑ c : columnSubgroup t, permutationSign c.val * x.coeff (c.val⁻¹ • r) := by
  classical
  simp [columnAlternator_action_sum, permutationRepresentation,
    Specs.AdvancedFiniteGroupRepresentations.permutationRepresentation,
    Representation.coeff_ofMulAction]

/-- Pairing with the signed column orbit. -/
theorem tabloidHermitian_polytabloid (t : Tableau p) (x : PermutationModule p) :
    tabloidHermitian x (polytabloid t) =
      ∑ c : columnSubgroup t, permutationSign c.val * x.coeff (tabloid (c.val • t)) := by
  classical
  simp only [tabloidHermitian_sum, polytabloid_sum, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [apply_ite, map_zero, permutationSign_conj]
  simp [eq_comm, mul_comm]

/-- The coefficient at the original tabloid identifies the scalar in the image line. -/
theorem columnAlternator_coeff_self (t : Tableau p) (x : PermutationModule p) :
    (groupAlgebraAction p (columnAlternator t) x).coeff (tabloid t) =
      tabloidHermitian x (polytabloid t) := by
  classical
  rw [columnAlternator_coeff, tabloidHermitian_polytabloid]
  apply Fintype.sum_equiv (Equiv.inv (columnSubgroup t))
  intro c
  simp [tabloid_smul]

private theorem columnAlternator_basis_line (t : Tableau p) (r : Tabloid p) :
    ∃ a : ℂ, groupAlgebraAction p (columnAlternator t) (MonoidAlgebra.single r 1) =
      a • polytabloid t := by
  classical
  induction r using Quotient.inductionOn with
  | _ u =>
    change ∃ a : ℂ, groupAlgebraAction p (columnAlternator t)
      (MonoidAlgebra.single (tabloid u) 1) = a • polytabloid t
    by_cases h : RowColumnCollision t u
    · exact ⟨0, by simp [columnAlternator_collision t u h]⟩
    · obtain ⟨c, hc, _⟩ := row_column_unique t u h
      exact ⟨permutationSign c.val, by rw [hc, columnAlternator_column_tabloid]⟩

/-- The equal-shape image is the polytabloid line. -/
theorem columnAlternator_image_line (t : Tableau p) (x : PermutationModule p) :
    ∃ a : ℂ, groupAlgebraAction p (columnAlternator t) x = a • polytabloid t := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb, add_smul]⟩
  | single r z =>
    obtain ⟨a, ha⟩ := columnAlternator_basis_line t r
    refine ⟨z * a, ?_⟩
    have hz : MonoidAlgebra.single r z = z • MonoidAlgebra.single r (1 : ℂ) := by
      simp
    rw [hz, map_smul, ha, smul_smul]

theorem columnAlternator_rank_one (t : Tableau p) (x : PermutationModule p) :
    groupAlgebraAction p (columnAlternator t) x =
      tabloidHermitian x (polytabloid t) • polytabloid t := by
  obtain ⟨a, ha⟩ := columnAlternator_image_line t x
  have hc := columnAlternator_coeff_self t x
  rw [ha, MonoidAlgebra.coeff_smul_apply, polytabloid_coefficient, smul_eq_mul,
    mul_one] at hc
  exact ha.trans (congrArg (fun z : ℂ => z • polytabloid t) hc)

end AdvancedFiniteGroupRepresentations
