import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorEvaluation
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.LengthBound
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

noncomputable section
open scoped BigOperators TensorProduct
universe u
namespace AdvancedFiniteGroupRepresentations

/- Supporting constructions live in this module's namespace so that their
names remain distinct from constructions in the standard-tableau proofs. -/
namespace LengthBound

variable {n : ℕ} {p : Partition n}
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The index of every occupied row is smaller than the number of rows. -/
theorem labelRow_lt_length (t : Tableau p) (a : Fin n) :
    labelRow t a < length p := by
  have hc := (cell_iff p _ _).mp (t.symm a).property
  by_contra h
  have hz := rowLength_zero_of_length_le p (labelRow t a) (Nat.le_of_not_gt h)
  change (t.symm a).val.2 < rowLength p (labelRow t a) at hc
  rw [hz] at hc
  exact Nat.not_lt_zero _ hc

/-- The basis word recording the ordered rows of a tabloid. -/
def tabloidRowWord {d : ℕ} (h : length p ≤ d) (q : Tabloid p) : Fin n → Fin d :=
  Quotient.lift (fun t a => ⟨labelRow t a, (labelRow_lt_length t a).trans_le h⟩)
    (by
      intro t s hts
      funext a
      apply Fin.ext
      exact congrFun hts a) q

@[simp] theorem tabloidRowWord_tabloid {d : ℕ} (h : length p ≤ d) (t : Tableau p)
    (a : Fin n) : (tabloidRowWord h (tabloid t) a).val = labelRow t a := rfl

theorem tabloidRowWord_injective {d : ℕ} (h : length p ≤ d) :
    Function.Injective (tabloidRowWord h) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ t =>
    induction r using Quotient.inductionOn with
    | _ s =>
      apply Quotient.sound
      funext a
      exact congrArg (fun w : Fin n → Fin d => (w a).val) hqr

theorem tabloidRowWord_smul {d : ℕ} (h : length p ≤ d)
    (g : SymmetricGroup n) (q : Tabloid p) :
    tabloidRowWord h (g • q) = fun a => tabloidRowWord h q (g⁻¹ a) := by
  induction q using Quotient.inductionOn with
  | _ t => rfl

/-- Linear extension of the inclusion of row words into the tensor basis. -/
def tabloidTensorMap {d : ℕ} (b : Module.Basis (Fin d) ℂ V) (h : length p ≤ d) :
    PermutationModule p →ₗ[ℂ] TensorPower V n :=
  (Basis.piTensorProduct (fun _ : Fin n => b)).repr.symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℂ ℂ (tabloidRowWord h)).comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)

theorem tabloidTensorMap_injective {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (h : length p ≤ d) : Function.Injective (tabloidTensorMap b h) :=
  (Basis.piTensorProduct (fun _ : Fin n => b)).repr.symm.injective.comp
    ((Finsupp.mapDomain_injective (tabloidRowWord_injective h)).comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).injective)

@[simp] theorem tabloidTensorMap_single {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (h : length p ≤ d) (q : Tabloid p) (z : ℂ) :
    tabloidTensorMap b h (MonoidAlgebra.single q z) =
      z • pureTensor V n (fun a => b (tabloidRowWord h q a)) := by
  simp [tabloidTensorMap, Finsupp.lmapDomain_apply,
    Basis.piTensorProduct_apply, pureTensor,
    Specs.AdvancedFiniteGroupRepresentations.pureTensor]

theorem tabloidTensorMap_equivariant {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (h : length p ≤ d) (g : SymmetricGroup n) (v : PermutationModule p) :
    tabloidTensorMap b h (permutationRepresentation p g v) =
      slotOperator V n g (tabloidTensorMap b h v) := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single q z =>
    rw [permutationRepresentation_basis, tabloidTensorMap_single,
      tabloidTensorMap_single, map_smul, slot_pureTensor, tabloidRowWord_smul]

/-- Restriction to the original Specht subspace gives an element of the actual Hom space. -/
def spechtTensorEmbedding {d : ℕ} (b : Module.Basis (Fin d) ℂ V) (h : length p ≤ d) :
    TensorMultiplicity V p :=
  ⟨(tabloidTensorMap b h).comp (spechtSpan p).subtype, by
    intro g v w hw
    change tabloidTensorMap b h w.val = slotOperator V n g (tabloidTensorMap b h v.val)
    rw [hw, tabloidTensorMap_equivariant]⟩

theorem spechtTensorEmbedding_injective {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (h : length p ≤ d) : Function.Injective (spechtTensorEmbedding b h).val :=
  (tabloidTensorMap_injective b h).comp Subtype.val_injective

theorem tensorMultiplicity_nonzero_of_length_le [FiniteDimensional ℂ V]
    (h : length p ≤ Module.finrank ℂ V) : Nontrivial (TensorMultiplicity V p) := by
  let b := Module.finBasis ℂ V
  let f := spechtTensorEmbedding b h
  let v : SpechtModule p := ⟨polytabloid (canonicalTableau p), polytabloid_mem_specht _⟩
  have hv : v ≠ 0 := by
    intro he
    exact polytabloid_ne_zero _ (congrArg Subtype.val he)
  have hf : f ≠ 0 := by
    intro he
    have hfzero : f.val v = f.val 0 := by simp [he]
    exact hv (spechtTensorEmbedding_injective b h hfzero)
  exact ⟨⟨f, 0, hf⟩⟩

/-- Slot permutation on coordinates of the tensor basis. The index on the
right is precomposed with g, as required for the given left slot action. -/
theorem tensorBasis_repr_slot {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (g : SymmetricGroup n) (x : TensorPower V n) (w : Fin n → Fin d) :
    (Basis.piTensorProduct (fun _ : Fin n => b)).repr (slotOperator V n g x) w =
      (Basis.piTensorProduct (fun _ : Fin n => b)).repr x (fun i => w (g i)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod z v =>
    change (Basis.piTensorProduct (fun _ : Fin n => b)).repr
        (slotOperator V n g (z • pureTensor V n v)) w = _
    rw [map_smul, slot_pureTensor]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, pureTensor,
      Specs.AdvancedFiniteGroupRepresentations.pureTensor,
      Basis.piTensorProduct_repr_tprod_apply]
    congr 1
    simpa using (Equiv.prod_comp g.symm (fun i => b.repr (v i) (w (g i))))
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Labels down the first column, parametrized by all nonempty rows. -/
def firstColumnLabel (t : Tableau p) (i : Fin (length p)) : Fin n :=
  t ⟨(i.val, 0), (cell_iff_column p i.val 0).mpr
    (by rw [← length_eq_columnLength_zero]; exact i.isLt)⟩

theorem firstColumnLabel_injective (t : Tableau p) :
    Function.Injective (firstColumnLabel t) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun c : Cell p => c.val.1) (t.injective hij)

@[simp] theorem labelColumn_firstColumnLabel (t : Tableau p) (i : Fin (length p)) :
    labelColumn t (firstColumnLabel t i) = 0 := by
  simp [firstColumnLabel, labelColumn,
    Specs.AdvancedFiniteGroupRepresentations.labelColumn]

/-- A word with too few letters repeats a letter in the first column. -/
theorem firstColumn_word_collision {d : ℕ} (t : Tableau p) (h : d < length p)
    (w : Fin n → Fin d) :
    ∃ a b : Fin n, a ≠ b ∧ labelColumn t a = labelColumn t b ∧ w a = w b := by
  obtain ⟨i, j, hij, hw⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => w (firstColumnLabel t i)) (by simpa using h)
  exact ⟨firstColumnLabel t i, firstColumnLabel t j,
    (firstColumnLabel_injective t).ne hij, by simp, hw⟩

/-- The image of a polytabloid still transforms by the column sign. -/
theorem tensorMultiplicity_column (f : TensorMultiplicity V p) (t : Tableau p)
    (c : columnSubgroup t) :
    slotOperator V n c.val (f.val (spechtPolytabloid t)) =
      permutationSign c.val • f.val (spechtPolytabloid t) := by
  rw [← f.property c.val (spechtPolytabloid t)
    (permutationSign c.val • spechtPolytabloid t)
    (column_action_polytabloid t c).symm, map_smul]

/-- In a tall shape every tensor coordinate of an image polytabloid is zero.
The collision transposition fixes the coordinate word and negates its image. -/
theorem tensorMultiplicity_polytabloid_zero {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (h : d < length p) (f : TensorMultiplicity V p) (t : Tableau p) :
    f.val (spechtPolytabloid t) = 0 := by
  classical
  apply (Basis.piTensorProduct (fun _ : Fin n => b)).ext_elem
  intro w
  obtain ⟨a, a', haa', hc, hw⟩ := firstColumn_word_collision t h w
  let c : columnSubgroup t := ⟨Equiv.swap a a', Equiv.apply_swap_eq_self hc⟩
  have hs : permutationSign c.val = -1 := by
    simp [c, permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign,
      Equiv.Perm.sign_swap haa']
  have hfix : (fun i => w (c.val i)) = w := funext (Equiv.apply_swap_eq_self hw)
  have he := congrArg (fun x : TensorPower V n =>
    (Basis.piTensorProduct (fun _ : Fin n => b)).repr x w)
      (tensorMultiplicity_column f t c)
  rw [tensorBasis_repr_slot, hfix, hs] at he
  simp only [neg_one_smul, map_neg, Finsupp.neg_apply] at he
  have hz : (2 : ℂ) *
      (Basis.piTensorProduct (fun _ : Fin n => b)).repr (f.val (spechtPolytabloid t)) w = 0 := by
    simpa only [two_mul] using eq_neg_iff_add_eq_zero.mp he
  have hz' := (mul_eq_zero.mp hz).resolve_left (by norm_num)
  simpa using hz'

/-- A map vanishing on polytabloids vanishes on their actual span. -/
theorem tensorMultiplicity_eq_zero_of_polytabloids (f : TensorMultiplicity V p)
    (h : ∀ t : Tableau p, f.val (spechtPolytabloid t) = 0) : f = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  change f.val ⟨x, hx⟩ = 0
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact h t
  | zero => exact map_zero f.val
  | add x y hx hy ihx ihy =>
    change f.val (⟨x, hx⟩ + ⟨y, hy⟩) = 0
    simp only [map_add, ihx, ihy, add_zero]
  | smul a x hx ih =>
    change f.val (a • (⟨x, hx⟩ : SpechtModule p)) = 0
    simp only [map_smul, ih, smul_zero]

theorem tensorMultiplicity_eq_zero_of_length_gt [FiniteDimensional ℂ V]
    (h : Module.finrank ℂ V < length p) (f : TensorMultiplicity V p) : f = 0 := by
  apply tensorMultiplicity_eq_zero_of_polytabloids
  intro t
  exact tensorMultiplicity_polytabloid_zero (Module.finBasis ℂ V) h f t

end LengthBound

/-- FR-D05: the exact length bound for the actual equivariant Hom space. -/
theorem tensorMultiplicity_nonzero_iff (V : Type u) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    Nontrivial (TensorMultiplicity V p) ↔ length p ≤ Module.finrank ℂ V := by
  constructor
  · intro h
    by_contra hle
    have : Subsingleton (TensorMultiplicity V p) :=
      ⟨fun f g => (LengthBound.tensorMultiplicity_eq_zero_of_length_gt
        (Nat.lt_of_not_ge hle) f).trans
        (LengthBound.tensorMultiplicity_eq_zero_of_length_gt (Nat.lt_of_not_ge hle) g).symm⟩
    exact not_nontrivial (TensorMultiplicity V p) h
  · exact LengthBound.tensorMultiplicity_nonzero_of_length_le

end AdvancedFiniteGroupRepresentations
