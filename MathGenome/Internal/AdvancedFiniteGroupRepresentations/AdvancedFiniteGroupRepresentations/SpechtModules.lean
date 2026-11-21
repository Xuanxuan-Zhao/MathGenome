import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Tabloids
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules

noncomputable section
open scoped BigOperators ComplexConjugate
namespace AdvancedFiniteGroupRepresentations

abbrev permutationSign := @Specs.AdvancedFiniteGroupRepresentations.permutationSign
abbrev columnAlternator := @Specs.AdvancedFiniteGroupRepresentations.columnAlternator
abbrev groupAlgebraAction := @Specs.AdvancedFiniteGroupRepresentations.groupAlgebraAction
abbrev polytabloid := @Specs.AdvancedFiniteGroupRepresentations.polytabloid
abbrev spechtSpan := @Specs.AdvancedFiniteGroupRepresentations.spechtSpan
abbrev SpechtModule := @Specs.AdvancedFiniteGroupRepresentations.SpechtModule
abbrev tabloidCoordinates := @Specs.AdvancedFiniteGroupRepresentations.tabloidCoordinates
abbrev tabloidHermitian := @Specs.AdvancedFiniteGroupRepresentations.tabloidHermitian

variable {n : ℕ} {p : Partition n}
attribute [local instance] Classical.propDecidable

@[simp] theorem permutationSign_one : permutationSign (1 : SymmetricGroup n) = 1 := by
  simp [permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign]

@[simp] theorem permutationSign_mul (g h : SymmetricGroup n) :
    permutationSign (g * h) = permutationSign g * permutationSign h := by
  simp [permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign]

@[simp] theorem permutationSign_inv (g : SymmetricGroup n) :
    permutationSign g⁻¹ = permutationSign g := by
  simp [permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign]

@[simp] theorem permutationSign_sq (g : SymmetricGroup n) :
    permutationSign g * permutationSign g = 1 := by
  have h := permutationSign_mul g⁻¹ g
  rw [inv_mul_cancel, permutationSign_one, permutationSign_inv] at h
  exact h.symm

@[simp] theorem groupAlgebraAction_single (g : SymmetricGroup n) (z : ℂ)
    (v : PermutationModule p) :
    groupAlgebraAction p (MonoidAlgebra.single g z) v = z • permutationRepresentation p g v := by
  exact congrArg (fun f : Module.End ℂ (PermutationModule p) => f v)
    ((permutationRepresentation p).asAlgebraHom_single g z)

/-- Expanding b_t {t} in the original tabloid basis. -/
theorem polytabloid_sum (t : Tableau p) :
    polytabloid t = ∑ c : columnSubgroup t,
      MonoidAlgebra.single (tabloid (c.val • t)) (permutationSign c.val) := by
  classical
  simp [polytabloid, Specs.AdvancedFiniteGroupRepresentations.polytabloid,
    Specs.AdvancedFiniteGroupRepresentations.columnAlternator,
    groupAlgebraAction_single, LinearMap.sum_apply, permutationRepresentation_basis,
    MonoidAlgebra.smul_single, tabloid_smul]

/-- Column permutations give distinct tabloids, including for the empty diagram. -/
theorem column_tabloid_injective (t : Tableau p) :
    Function.Injective (fun c : columnSubgroup t => tabloid (c.val • t)) := by
  intro c d h
  change tabloid (c.val • t) = tabloid (d.val • t) at h
  have hr : d.val⁻¹ * c.val ∈ rowSubgroup t := by
    rw [← tabloid_stabilizer, MulAction.mem_stabilizer_iff]
    rw [mul_smul]
    change d.val⁻¹ • tabloid (c.val • t) = tabloid t
    rw [h, ← tabloid_smul]
    simp
  have hc : d.val⁻¹ * c.val ∈ columnSubgroup t :=
    (columnSubgroup t).mul_mem ((columnSubgroup t).inv_mem d.property) c.property
  have he : d.val⁻¹ * c.val = 1 := by
    have : d.val⁻¹ * c.val ∈ rowSubgroup t ⊓ columnSubgroup t := ⟨hr, hc⟩
    rw [row_column_inf] at this
    exact this
  apply Subtype.ext
  exact (inv_mul_eq_one.mp he).symm

@[simp] theorem polytabloid_coefficient (t : Tableau p) :
    (polytabloid t).coeff (tabloid t) = 1 := by
  classical
  rw [polytabloid_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  have he : ∀ c : columnSubgroup t, tabloid (c.val • t) = tabloid t ↔ c = 1 := by
    intro c
    have h1 : tabloid ((1 : columnSubgroup t).val • t) = tabloid t := by simp
    rw [← h1]
    exact (column_tabloid_injective t).eq_iff
  simp [Finsupp.single_apply, he]

@[simp] theorem labelColumn_smul (g : SymmetricGroup n) (t : Tableau p) (a : Fin n) :
    labelColumn (g • t) a = labelColumn t (g⁻¹ a) := rfl

/-- Conjugation transports the actual column stabilizers. -/
def columnConjugation (g : SymmetricGroup n) (t : Tableau p) :
    columnSubgroup t ≃ columnSubgroup (g • t) where
  toFun c := ⟨g * c.val * g⁻¹, by
    intro a
    change labelColumn t (g⁻¹ ((g * c.val * g⁻¹) a)) = labelColumn t (g⁻¹ a)
    simpa using c.property (g⁻¹ a)⟩
  invFun d := ⟨g⁻¹ * d.val * g, by
    intro a
    have hd := d.property (g a)
    change labelColumn t (g⁻¹ (d.val (g a))) = labelColumn t (g⁻¹ (g a)) at hd
    simpa using hd⟩
  left_inv c := by apply Subtype.ext; simp [mul_assoc]
  right_inv d := by apply Subtype.ext; simp [mul_assoc]

@[simp] theorem permutationSign_conjugate (g h : SymmetricGroup n) :
    permutationSign (g * h * g⁻¹) = permutationSign h := by
  simp only [permutationSign_mul, permutationSign_inv]
  calc
    _ = (permutationSign g * permutationSign g) * permutationSign h := by ring
    _ = permutationSign h := by simp

theorem polytabloid_equivariant (g : SymmetricGroup n) (t : Tableau p) :
    permutationRepresentation p g (polytabloid t) = polytabloid (g • t) := by
  classical
  rw [polytabloid_sum, map_sum, polytabloid_sum]
  apply Fintype.sum_equiv (columnConjugation g t)
  intro c
  rw [permutationRepresentation_basis]
  change MonoidAlgebra.single (g • tabloid (c.val • t)) (permutationSign c.val) =
    MonoidAlgebra.single (tabloid ((g * c.val * g⁻¹) • (g • t)))
      (permutationSign (g * c.val * g⁻¹))
  rw [permutationSign_conjugate]
  simp [← tabloid_smul, mul_smul]

/-- Left translation reindexes the signed column orbit. -/
theorem column_action_polytabloid (t : Tableau p) (c : columnSubgroup t) :
    permutationRepresentation p c.val (polytabloid t) =
      permutationSign c.val • polytabloid t := by
  classical
  rw [polytabloid_sum, map_sum, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro d
  rw [permutationRepresentation_basis, MonoidAlgebra.smul_single]
  simp only [← tabloid_smul, ← mul_smul]
  congr 1
  change permutationSign d.val = permutationSign c.val * permutationSign (c.val * d.val)
  rw [permutationSign_mul, ← mul_assoc, permutationSign_sq, one_mul]

theorem polytabloid_column (t : Tableau p) (c : columnSubgroup t) :
    polytabloid (c.val • t) = permutationSign c.val • polytabloid t := by
  rw [← polytabloid_equivariant, column_action_polytabloid]

theorem columnAlternator_polytabloid (t : Tableau p) :
    groupAlgebraAction p (columnAlternator t) (polytabloid t) =
      (Fintype.card (columnSubgroup t) : ℂ) • polytabloid t := by
  classical
  simp only [columnAlternator, Specs.AdvancedFiniteGroupRepresentations.columnAlternator,
    map_sum, LinearMap.sum_apply, groupAlgebraAction_single, column_action_polytabloid,
    smul_smul, permutationSign_sq, one_smul, Finset.sum_const, Finset.card_univ]
  exact Nat.cast_smul_eq_nsmul ℂ _ _ |>.symm

theorem polytabloid_ne_zero (t : Tableau p) : polytabloid t ≠ 0 := by
  intro h
  have hh := polytabloid_coefficient t
  rw [h, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hh
  exact zero_ne_one hh

theorem polytabloid_mem_specht (t : Tableau p) : polytabloid t ∈ spechtSpan p :=
  Submodule.subset_span ⟨t, rfl⟩

theorem specht_stable (g : SymmetricGroup n) (v : PermutationModule p)
    (hv : v ∈ spechtSpan p) : permutationRepresentation p g v ∈ spechtSpan p := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, rfl⟩ := hv
    rw [polytabloid_equivariant]
    exact polytabloid_mem_specht _
  | zero => simp
  | add v w hv hw ihv ihw =>
    simpa using (spechtSpan p).add_mem ihv ihw
  | smul z v hv ih =>
    simpa using (spechtSpan p).smul_mem z ih

/-- The action is the restriction of the ambient permutation representation. -/
def spechtSubrepresentation (p : Partition n) : Subrepresentation (permutationRepresentation p) where
  toSubmodule := spechtSpan p
  apply_mem_toSubmodule g v hv := specht_stable g v hv

theorem specht_inheritedAction (p : Partition n) :
    ∃ ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p),
      ∀ g v, (ρ g v).val = permutationRepresentation p g v.val := by
  exact ⟨(spechtSubrepresentation p).toRepresentation, fun _ _ => rfl⟩

theorem specht_nonzero (p : Partition n) : spechtSpan p ≠ ⊥ := by
  intro h
  have ht := polytabloid_mem_specht (canonicalTableau p)
  rw [h, Submodule.mem_bot] at ht
  exact polytabloid_ne_zero _ ht

/-- Every one of the original polytabloids generates the whole Specht module. -/
theorem specht_cyclic (t : Tableau p) :
    spechtSpan p = Submodule.span ℂ
      (Set.range (fun g : SymmetricGroup n => permutationRepresentation p g (polytabloid t))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨u, rfl⟩
    obtain ⟨g, hg, _⟩ := tableau_existsUnique t u
    apply Submodule.subset_span
    exact ⟨g, by
      change permutationRepresentation p g (polytabloid t) = polytabloid u
      rw [polytabloid_equivariant, hg]⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨g, rfl⟩
    change permutationRepresentation p g (polytabloid t) ∈ spechtSpan p
    rw [polytabloid_equivariant]
    exact polytabloid_mem_specht _

theorem specht_generated (t : Tableau p) (U : Subrepresentation (permutationRepresentation p))
    (ht : polytabloid t ∈ U) : spechtSpan p ≤ U.toSubmodule := by
  rw [specht_cyclic t]
  apply Submodule.span_le.mpr
  rintro v ⟨g, rfl⟩
  exact U.apply_mem_toSubmodule g ht

@[simp] theorem tabloidCoordinates_apply (x : PermutationModule p) (q : Tabloid p) :
    tabloidCoordinates x q = x.coeff q := rfl

@[simp] theorem tabloidCoordinates_add (x y : PermutationModule p) :
    tabloidCoordinates (x + y) = tabloidCoordinates x + tabloidCoordinates y := by
  ext q
  simp

@[simp] theorem tabloidCoordinates_smul (z : ℂ) (x : PermutationModule p) :
    tabloidCoordinates (z • x) = z • tabloidCoordinates x := by
  ext q
  simp

@[simp] theorem tabloidCoordinates_zero :
    tabloidCoordinates (0 : PermutationModule p) = 0 := by
  ext q
  simp

theorem tabloidCoordinates_injective :
    Function.Injective (tabloidCoordinates (p := p)) := by
  intro x y h
  ext q
  exact congrArg (fun v : EuclideanSpace ℂ (Tabloid p) => v q) h

/-- Explicit reconciliation with Mathlib: its first argument is conjugate-linear. -/
theorem tabloidHermitian_library (x y : PermutationModule p) :
    tabloidHermitian x y = inner ℂ (tabloidCoordinates y) (tabloidCoordinates x) := rfl

theorem tabloidHermitian_sum (x y : PermutationModule p) :
    tabloidHermitian x y = ∑ q : Tabloid p, x.coeff q * conj (y.coeff q) := by
  simp [tabloidHermitian_library, inner]

theorem tabloidHermitian_add_left (x y z : PermutationModule p) :
    tabloidHermitian (x + y) z = tabloidHermitian x z + tabloidHermitian y z := by
  simp only [tabloidHermitian_library, tabloidCoordinates_add, inner_add_right]

theorem tabloidHermitian_smul_left (a : ℂ) (x y : PermutationModule p) :
    tabloidHermitian (a • x) y = a * tabloidHermitian x y := by
  simp only [tabloidHermitian_library, tabloidCoordinates_smul, inner_smul_right]

theorem tabloidHermitian_add_right (x y z : PermutationModule p) :
    tabloidHermitian x (y + z) = tabloidHermitian x y + tabloidHermitian x z := by
  simp only [tabloidHermitian_library, tabloidCoordinates_add, inner_add_left]

theorem tabloidHermitian_smul_right (a : ℂ) (x y : PermutationModule p) :
    tabloidHermitian x (a • y) = conj a * tabloidHermitian x y := by
  simp only [tabloidHermitian_library, tabloidCoordinates_smul, inner_smul_left]

theorem tabloidHermitian_conj_symm (x y : PermutationModule p) :
    conj (tabloidHermitian y x) = tabloidHermitian x y := by
  exact inner_conj_symm (𝕜 := ℂ) (tabloidCoordinates y) (tabloidCoordinates x)

theorem tabloidHermitian_nonneg (x : PermutationModule p) :
    0 ≤ (tabloidHermitian x x).re := by
  exact inner_self_nonneg (𝕜 := ℂ) (x := tabloidCoordinates x)

theorem tabloidHermitian_pos (x : PermutationModule p) :
    0 < (tabloidHermitian x x).re ↔ x ≠ 0 := by
  change 0 < RCLike.re (inner ℂ (tabloidCoordinates x) (tabloidCoordinates x)) ↔ x ≠ 0
  rw [re_inner_self_pos]
  exact (tabloidCoordinates_injective.ne_iff' tabloidCoordinates_zero)

theorem tabloidHermitian_definite (x : PermutationModule p) :
    tabloidHermitian x x = 0 ↔ x = 0 := by
  rw [tabloidHermitian_library, inner_self_eq_zero]
  exact tabloidCoordinates_injective.eq_iff' tabloidCoordinates_zero

theorem tabloidHermitian_basis (q r : Tabloid p) :
    tabloidHermitian (MonoidAlgebra.single q 1) (MonoidAlgebra.single r 1) =
      if q = r then 1 else 0 := by
  classical
  simp [tabloidHermitian_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem tabloidHermitian_invariant (g : SymmetricGroup n) (x y : PermutationModule p) :
    tabloidHermitian (permutationRepresentation p g x) (permutationRepresentation p g y) =
      tabloidHermitian x y := by
  classical
  simp only [tabloidHermitian_sum, permutationRepresentation,
    Specs.AdvancedFiniteGroupRepresentations.permutationRepresentation,
    Representation.coeff_ofMulAction]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun q => x.coeff q * conj (y.coeff q))

end AdvancedFiniteGroupRepresentations
