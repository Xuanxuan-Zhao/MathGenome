import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.DominanceMultiplicity
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.YoungIdempotents
import Mathlib.LinearAlgebra.Trace

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev rowSymmetrizer := @Specs.AdvancedFiniteGroupRepresentations.rowSymmetrizer
abbrev youngSymmetrizer := @Specs.AdvancedFiniteGroupRepresentations.youngSymmetrizer
abbrev reverseYoungSymmetrizer := @Specs.AdvancedFiniteGroupRepresentations.reverseYoungSymmetrizer
abbrev principalLeftIdeal := @Specs.AdvancedFiniteGroupRepresentations.principalLeftIdeal
abbrev tabloidIdealMap := @Specs.AdvancedFiniteGroupRepresentations.tabloidIdealMap
abbrev youngScalar := @Specs.AdvancedFiniteGroupRepresentations.youngScalar
abbrev normalizedYoung := @Specs.AdvancedFiniteGroupRepresentations.normalizedYoung
abbrev normalizedReverseYoung := @Specs.AdvancedFiniteGroupRepresentations.normalizedReverseYoung

variable {n : ℕ} {p : Partition n}
attribute [local instance] Classical.propDecidable

@[simp] theorem tabloidIdealMap_coeff (t : Tableau p) (x : PermutationModule p)
    (g : SymmetricGroup n) : (tabloidIdealMap t x).coeff g = x.coeff (g • tabloid t) := by
  classical
  simp [tabloidIdealMap, Specs.AdvancedFiniteGroupRepresentations.tabloidIdealMap,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

@[simp] theorem rowSymmetrizer_coeff (t : Tableau p) (g : SymmetricGroup n) :
    (rowSymmetrizer t).coeff g = if g ∈ rowSubgroup t then 1 else 0 := by
  classical
  simp only [rowSymmetrizer, Specs.AdvancedFiniteGroupRepresentations.rowSymmetrizer,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  by_cases hg : g ∈ rowSubgroup t
  · rw [ite_eq_left hg]
    rw [Finset.sum_eq_single (⟨g, hg⟩ : rowSubgroup t) (by
        intro b _ hb
        have hb' : b.val ≠ g := fun h => hb (Subtype.ext h)
        simp [hb'])
      (by simp)]
    simp
  · rw [ite_eq_right hg]
    apply Finset.sum_eq_zero
    intro b _
    have : b.val ≠ g := fun h => hg (h ▸ b.property)
    simp [this]

/-- The tabloid-to-coset-sum map on each generator. -/
theorem tabloidIdealMap_basis (t : Tableau p) (g : SymmetricGroup n) (z : ℂ) :
    tabloidIdealMap t (MonoidAlgebra.single (tabloid (g • t)) z) =
      MonoidAlgebra.single g z * rowSymmetrizer t := by
  classical
  ext h
  rw [tabloidIdealMap_coeff, MonoidAlgebra.coeff_single_mul_apply, rowSymmetrizer_coeff]
  have he : g⁻¹ * h ∈ rowSubgroup t ↔ tabloid (g • t) = h • tabloid t := by
    rw [← tabloid_stabilizer, MulAction.mem_stabilizer_iff, mul_smul]
    rw [inv_smul_eq_iff, ← tabloid_smul]
    exact eq_comm
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, he]
  split_ifs <;> simp_all

theorem tabloidIdealMap_injective (t : Tableau p) : Function.Injective (tabloidIdealMap t) := by
  intro x y h
  ext q
  induction q using Quotient.inductionOn with
  | _ u =>
    change x.coeff (tabloid u) = y.coeff (tabloid u)
    obtain ⟨g, hg, _⟩ := tableau_existsUnique t u
    have hh := congrArg (fun a : GroupAlgebra n => a.coeff g) h
    simpa only [tabloidIdealMap_coeff, tabloid_smul, hg] using hh

theorem tabloidIdealMap_equivariant (t : Tableau p) (g : SymmetricGroup n)
    (x : PermutationModule p) :
    tabloidIdealMap t (permutationRepresentation p g x) =
      MonoidAlgebra.single g 1 * tabloidIdealMap t x := by
  ext h
  simp only [tabloidIdealMap_coeff, permutationRepresentation,
    Specs.AdvancedFiniteGroupRepresentations.permutationRepresentation,
    Representation.coeff_ofMulAction, MonoidAlgebra.coeff_single_mul_apply, one_mul]
  rw [mul_smul]

/-- The map's range is the whole principal left ideal, not just its group orbit. -/
theorem tabloidIdealMap_range (t : Tableau p) :
    LinearMap.range (tabloidIdealMap t) = principalLeftIdeal (rowSymmetrizer t) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using MonoidAlgebra.induction_linear with
    | zero => simpa only [map_zero] using (principalLeftIdeal (rowSymmetrizer t)).zero_mem
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | single q z =>
      induction q using Quotient.inductionOn with
      | _ u =>
        obtain ⟨g, hg, _⟩ := tableau_existsUnique t u
        change tabloidIdealMap t (MonoidAlgebra.single (tabloid u) z) ∈ _
        rw [← hg, tabloidIdealMap_basis]
        exact ⟨MonoidAlgebra.single g z, rfl⟩
  · rintro _ ⟨a, rfl⟩
    induction a using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add a b ha hb =>
      simpa only [LinearMap.mulRight_apply, add_mul] using Submodule.add_mem _ ha hb
    | single g z =>
      exact ⟨MonoidAlgebra.single (tabloid (g • t)) z, tabloidIdealMap_basis t g z⟩

theorem tabloid_ideal_isomorphism (t : Tableau p) :
    ∃ e : PermutationModule p ≃ₗ[ℂ] principalLeftIdeal (rowSymmetrizer t),
      (∀ x, (e x).val = tabloidIdealMap t x) ∧
      (∀ g, (e (MonoidAlgebra.single (tabloid (g • t)) 1)).val =
        MonoidAlgebra.single g 1 * rowSymmetrizer t) ∧
      (∀ g x, (e (permutationRepresentation p g x)).val =
        MonoidAlgebra.single g 1 * (e x).val) := by
  let e := (LinearEquiv.ofInjective (tabloidIdealMap t) (tabloidIdealMap_injective t)).trans
    (LinearEquiv.ofEq _ _ (tabloidIdealMap_range t))
  exact ⟨e, fun _ => rfl, (fun g => tabloidIdealMap_basis t g 1), tabloidIdealMap_equivariant t⟩

/-- Equivariance extends linearly to the whole group algebra. -/
theorem tabloidIdealMap_algebra (t : Tableau p) (a : GroupAlgebra n)
    (x : PermutationModule p) :
    tabloidIdealMap t (groupAlgebraAction p a x) = a * tabloidIdealMap t x := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [LinearMap.add_apply, ha, hb, add_mul]
  | single g z =>
    rw [groupAlgebraAction_single, map_smul, tabloidIdealMap_equivariant]
    simp [MonoidAlgebra.smul_single, ← smul_mul_assoc]

@[simp] theorem tabloidIdealMap_polytabloid (t : Tableau p) :
    tabloidIdealMap t (polytabloid t) = youngSymmetrizer t := by
  rw [polytabloid, Specs.AdvancedFiniteGroupRepresentations.polytabloid,
    tabloidIdealMap_algebra]
  change columnAlternator t * tabloidIdealMap t (MonoidAlgebra.single (tabloid t) 1) =
    columnAlternator t * rowSymmetrizer t
  have ht := tabloidIdealMap_basis t 1 1
  simpa only [one_smul, ← MonoidAlgebra.one_def, one_mul] using
    congrArg (columnAlternator t * ·) ht

/-- Stability of the Specht subspace under the full group algebra. -/
theorem groupAlgebraAction_mem_specht (a : GroupAlgebra n) (x : PermutationModule p)
    (hx : x ∈ spechtSpan p) : groupAlgebraAction p a x ∈ spechtSpan p := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simpa [LinearMap.add_apply] using (spechtSpan p).add_mem ha hb
  | single g z =>
    rw [groupAlgebraAction_single]
    exact (spechtSpan p).smul_mem z (specht_stable g x hx)

/-- The cyclic map A → S, a ↦ a e_t, with its genuine Specht-space codomain. -/
def spechtCyclicMap (t : Tableau p) : GroupAlgebra n →ₗ[ℂ] SpechtModule p where
  toFun a := ⟨groupAlgebraAction p a (polytabloid t),
    groupAlgebraAction_mem_specht a _ (polytabloid_mem_specht t)⟩
  map_add' a b := Subtype.ext (by simp [LinearMap.add_apply])
  map_smul' z a := Subtype.ext (by simp)

@[simp] theorem spechtCyclicMap_val (t : Tableau p) (a : GroupAlgebra n) :
    (spechtCyclicMap t a).val = groupAlgebraAction p a (polytabloid t) := rfl

/-- Inclusion of S followed by the coset-sum map. -/
def spechtIdealMap (t : Tableau p) : SpechtModule p →ₗ[ℂ] GroupAlgebra n :=
  (tabloidIdealMap t).comp (spechtSpan p).subtype

@[simp] theorem spechtIdealMap_apply (t : Tableau p) (x : SpechtModule p) :
    spechtIdealMap t x = tabloidIdealMap t x.val := rfl

@[simp] theorem spechtIdealMap_cyclic (t : Tableau p) (a : GroupAlgebra n) :
    spechtIdealMap t (spechtCyclicMap t a) = a * youngSymmetrizer t := by
  simp [tabloidIdealMap_algebra]

theorem spechtIdealMap_injective (t : Tableau p) : Function.Injective (spechtIdealMap t) :=
  (tabloidIdealMap_injective t).comp Subtype.val_injective

theorem spechtIdealMap_range (t : Tableau p) :
    LinearMap.range (spechtIdealMap t) = principalLeftIdeal (youngSymmetrizer t) := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    change tabloidIdealMap t x ∈ principalLeftIdeal (youngSymmetrizer t)
    change x ∈ spechtSpan p at hx
    rw [specht_cyclic t] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [tabloidIdealMap_equivariant, tabloidIdealMap_polytabloid]
      exact ⟨MonoidAlgebra.single g 1, rfl⟩
    | zero => simpa only [map_zero] using (principalLeftIdeal (youngSymmetrizer t)).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih
  · rintro _ ⟨a, rfl⟩
    exact ⟨spechtCyclicMap t a, spechtIdealMap_cyclic t a⟩

theorem specht_ideal_isomorphism (t : Tableau p) :
    ∃ e : SpechtModule p ≃ₗ[ℂ] principalLeftIdeal (youngSymmetrizer t),
      (∀ x, (e x).val = tabloidIdealMap t x.val) ∧
      (∀ (g : SymmetricGroup n) (x y : SpechtModule p),
        y.val = permutationRepresentation p g x.val →
        (e y).val = MonoidAlgebra.single g 1 * (e x).val) := by
  let e := (LinearEquiv.ofInjective (spechtIdealMap t) (spechtIdealMap_injective t)).trans
    (LinearEquiv.ofEq _ _ (spechtIdealMap_range t))
  refine ⟨e, fun _ => rfl, ?_⟩
  intro g x y hy
  change tabloidIdealMap t y.val = _
  rw [hy, tabloidIdealMap_equivariant]
  rfl

theorem youngScalar_ne_zero (p : Partition n) : youngScalar p ≠ 0 := by
  have h : Nontrivial (SpechtModule p) := by
    apply nontrivial_of_ne (spechtPolytabloid (canonicalTableau p)) 0
    intro hz
    exact polytabloid_ne_zero _ (congrArg Subtype.val hz)
  have hd : Module.finrank ℂ (SpechtModule p) ≠ 0 := (Module.finrank_pos (R := ℂ)).ne'
  exact div_ne_zero (by exact_mod_cast n.factorial_ne_zero) (by exact_mod_cast hd)

/-- The identity coefficient uses the actual trivial row-column intersection. -/
@[simp] theorem youngSymmetrizer_coeff_one (t : Tableau p) :
    (youngSymmetrizer t).coeff 1 = 1 := by
  classical
  change ((∑ c : columnSubgroup t,
    MonoidAlgebra.single c.val (permutationSign c.val)) * rowSymmetrizer t).coeff 1 = 1
  rw [Finset.sum_mul]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single_mul_apply, mul_one, rowSymmetrizer_coeff]
  have hr (c : columnSubgroup t) : c.val⁻¹ ∈ rowSubgroup t ↔ c = 1 := by
    constructor
    · intro h
      have h' : c.val ∈ rowSubgroup t := by simpa using (rowSubgroup t).inv_mem h
      have hc : c.val ∈ rowSubgroup t ⊓ columnSubgroup t := ⟨h', c.property⟩
      rw [row_column_inf] at hc
      exact Subtype.ext hc
    · rintro rfl
      simp
  simp [hr, permutationSign_one]

/-- In the group basis, all diagonal entries of right multiplication are z(1). -/
theorem trace_mulRight_groupAlgebra (z : GroupAlgebra n) :
    LinearMap.trace ℂ (GroupAlgebra n) (LinearMap.mulRight ℂ z) =
      (n.factorial : ℂ) * z.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis (SymmetricGroup n) ℂ)]
  have hd (g : SymmetricGroup n) :
      (LinearMap.toMatrix (MonoidAlgebra.basis (SymmetricGroup n) ℂ)
        (MonoidAlgebra.basis (SymmetricGroup n) ℂ) (LinearMap.mulRight ℂ z)) g g = z.coeff 1 := by
    rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
    change (MonoidAlgebra.single g 1 * z).coeff g = z.coeff 1
    simp
  simp only [Matrix.trace, Matrix.diag, hd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp [SymmetricGroup, Specs.AdvancedFiniteGroupRepresentations.SymmetricGroup, Fintype.card_perm]

/-- The cyclic map is equivariant for left multiplication in A. -/
theorem spechtCyclicMap_equivariant (t : Tableau p) (g : SymmetricGroup n)
    (a : GroupAlgebra n) :
    (spechtCyclicMap t (MonoidAlgebra.single g 1 * a)).val =
      permutationRepresentation p g (spechtCyclicMap t a).val := by
  change groupAlgebraAction p (MonoidAlgebra.single g 1 * a) (polytabloid t) = _
  rw [map_mul]
  change groupAlgebraAction p (MonoidAlgebra.single g 1)
    (groupAlgebraAction p a (polytabloid t)) = _
  simp [groupAlgebraAction_single]

/-- Diagonal multiplicity implies that the factorization A → S → A acts
by one scalar on S. This is Schur's lemma in the established Specht model. -/
theorem spechtCyclicMap_comp_scalar (t : Tableau p) :
    ∃ q : ℂ, (spechtCyclicMap t).comp (spechtIdealMap t) =
      q • (LinearMap.id : SpechtModule p →ₗ[ℂ] SpechtModule p) := by
  let f : SpechtHom p p := ⟨(spechtSpan p).subtype.comp
    ((spechtCyclicMap t).comp (spechtIdealMap t)), by
      intro g v w hw
      change (spechtCyclicMap t (tabloidIdealMap t w.val)).val =
        permutationRepresentation p g (spechtCyclicMap t (tabloidIdealMap t v.val)).val
      rw [hw, tabloidIdealMap_equivariant, spechtCyclicMap_equivariant]⟩
  obtain ⟨q, hq⟩ := diagonal_hom_scalar p f
  refine ⟨q, ?_⟩
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have he := congrArg (fun k : SpechtHom p p => k.val v) hq
  exact he.symm

/-- The two compositions have equal trace, so the scalar is exactly n!/dim S. -/
theorem spechtCyclicMap_comp (t : Tableau p) :
    (spechtCyclicMap t).comp (spechtIdealMap t) =
      youngScalar p • (LinearMap.id : SpechtModule p →ₗ[ℂ] SpechtModule p) := by
  obtain ⟨q, hq⟩ := spechtCyclicMap_comp_scalar t
  have hcomp : (spechtIdealMap t).comp (spechtCyclicMap t) =
      LinearMap.mulRight ℂ (youngSymmetrizer t) := by
    apply LinearMap.ext
    intro a
    exact spechtIdealMap_cyclic t a
  have htrace := LinearMap.trace_comp_comm' (spechtIdealMap t) (spechtCyclicMap t)
  rw [hq, hcomp, map_smul, LinearMap.trace_id, trace_mulRight_groupAlgebra,
    youngSymmetrizer_coeff_one, mul_one] at htrace
  have hd : (Module.finrank ℂ (SpechtModule p) : ℂ) ≠ 0 := by
    have h := youngScalar_ne_zero p
    exact (div_ne_zero_iff.mp h).2
  have hq' : q = youngScalar p := (eq_div_iff hd).mpr htrace
  simpa [hq'] using hq

theorem youngSymmetrizer_square (t : Tableau p) :
    youngSymmetrizer t * youngSymmetrizer t = youngScalar p • youngSymmetrizer t := by
  have h := congrArg (fun f : SpechtModule p →ₗ[ℂ] SpechtModule p =>
    spechtIdealMap t (f (spechtPolytabloid t))) (spechtCyclicMap_comp t)
  have he : spechtIdealMap t (spechtPolytabloid t) = youngSymmetrizer t :=
    tabloidIdealMap_polytabloid t
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_smul, he, spechtIdealMap_cyclic] using h

/-- Linear inversion of group elements; coefficients are not conjugated. -/
def groupAlgebraInversion (n : ℕ) : GroupAlgebra n ≃ₗ[ℂ] GroupAlgebra n :=
  MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ (Equiv.inv (SymmetricGroup n))

@[simp] theorem groupAlgebraInversion_single (g : SymmetricGroup n) (z : ℂ) :
    groupAlgebraInversion n (MonoidAlgebra.single g z) = MonoidAlgebra.single g⁻¹ z := by
  simp [groupAlgebraInversion]

theorem groupAlgebraInversion_mul (a b : GroupAlgebra n) :
    groupAlgebraInversion n (a * b) = groupAlgebraInversion n b * groupAlgebraInversion n a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, mul_add, ha, hb]
  | single g z =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [mul_add, add_mul, ha, hb]
    | single h w => simp [MonoidAlgebra.single_mul_single, mul_comm]

@[simp] theorem groupAlgebraInversion_row (t : Tableau p) :
    groupAlgebraInversion n (rowSymmetrizer t) = rowSymmetrizer t := by
  classical
  change groupAlgebraInversion n (∑ r : rowSubgroup t, MonoidAlgebra.single r.val 1) = _
  rw [map_sum]
  simp only [groupAlgebraInversion_single]
  exact Equiv.sum_comp (Equiv.inv (rowSubgroup t)) (fun r => MonoidAlgebra.single r.val (1 : ℂ))

@[simp] theorem groupAlgebraInversion_column (t : Tableau p) :
    groupAlgebraInversion n (columnAlternator t) = columnAlternator t := by
  classical
  change groupAlgebraInversion n (∑ c : columnSubgroup t,
    MonoidAlgebra.single c.val (permutationSign c.val)) = _
  rw [map_sum]
  simp only [groupAlgebraInversion_single]
  have he := Equiv.sum_comp (Equiv.inv (columnSubgroup t))
    (fun c => MonoidAlgebra.single c.val (permutationSign c.val))
  simpa only [Equiv.inv_apply, Subgroup.coe_inv, permutationSign_inv,
    columnAlternator, Specs.AdvancedFiniteGroupRepresentations.columnAlternator] using he

@[simp] theorem groupAlgebraInversion_young (t : Tableau p) :
    groupAlgebraInversion n (youngSymmetrizer t) = reverseYoungSymmetrizer t := by
  change groupAlgebraInversion n (columnAlternator t * rowSymmetrizer t) = _
  rw [groupAlgebraInversion_mul, groupAlgebraInversion_row, groupAlgebraInversion_column]
  rfl

theorem reverseYoungSymmetrizer_square (t : Tableau p) :
    reverseYoungSymmetrizer t * reverseYoungSymmetrizer t =
      youngScalar p • reverseYoungSymmetrizer t := by
  have he := congrArg (groupAlgebraInversion n) (youngSymmetrizer_square t)
  simpa only [groupAlgebraInversion_mul, map_smul, groupAlgebraInversion_young] using he

theorem normalizedYoung_idempotent (t : Tableau p) : IsIdempotentElem (normalizedYoung t) := by
  change ((youngScalar p)⁻¹ • youngSymmetrizer t) *
    ((youngScalar p)⁻¹ • youngSymmetrizer t) = (youngScalar p)⁻¹ • youngSymmetrizer t
  rw [smul_mul_smul_comm, youngSymmetrizer_square, smul_smul]
  congr 1
  field_simp [youngScalar_ne_zero p]

theorem normalizedReverseYoung_idempotent (t : Tableau p) :
    IsIdempotentElem (normalizedReverseYoung t) := by
  change ((youngScalar p)⁻¹ • reverseYoungSymmetrizer t) *
    ((youngScalar p)⁻¹ • reverseYoungSymmetrizer t) =
      (youngScalar p)⁻¹ • reverseYoungSymmetrizer t
  rw [smul_mul_smul_comm, reverseYoungSymmetrizer_square, smul_smul]
  congr 1
  field_simp [youngScalar_ne_zero p]

/-- Right multiplication restricts to principal left ideals whenever the
product of the generator belongs to the target ideal. -/
def principalIdealRightMap (z w d a : GroupAlgebra n) (h : z * d = a * w) :
    principalLeftIdeal z →ₗ[ℂ] principalLeftIdeal w where
  toFun x := ⟨x.val * d, by
    obtain ⟨b, hb⟩ := x.property
    refine ⟨b * a, ?_⟩
    change (b * a) * w = x.val * d
    change b * z = x.val at hb
    rw [← hb]
    simp only [mul_assoc, h]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' c x := Subtype.ext (smul_mul_assoc _ _ _)

@[simp] theorem principalIdealRightMap_val (z w d a : GroupAlgebra n)
    (h : z * d = a * w) (x : principalLeftIdeal z) :
    (principalIdealRightMap z w d a h x).val = x.val * d := rfl

/-- The square relation determines right multiplication on the entire ideal. -/
theorem principalLeftIdeal_mul_scalar (z : GroupAlgebra n) (q : ℂ)
    (h : z * z = q • z) (x : principalLeftIdeal z) : x.val * z = q • x.val := by
  obtain ⟨a, ha⟩ := x.property
  change a * z = x.val at ha
  rw [← ha, mul_assoc, h, mul_smul_comm]

theorem young_ideals_isomorphism (t : Tableau p) :
    ∃ e : principalLeftIdeal (youngSymmetrizer t) ≃ₗ[ℂ]
        principalLeftIdeal (reverseYoungSymmetrizer t),
      ∀ (g : SymmetricGroup n) (x y : principalLeftIdeal (youngSymmetrizer t)),
        y.val = MonoidAlgebra.single g 1 * x.val →
        (e y).val = MonoidAlgebra.single g 1 * (e x).val := by
  let a := rowSymmetrizer t
  let b := columnAlternator t
  let c := youngSymmetrizer t
  let d := reverseYoungSymmetrizer t
  let q := youngScalar p
  have hc : c = b * a := rfl
  have hd : d = a * b := rfl
  let f : principalLeftIdeal c →ₗ[ℂ] principalLeftIdeal d :=
    principalIdealRightMap c d b b (by rw [hc, hd, mul_assoc])
  let k : principalLeftIdeal d →ₗ[ℂ] principalLeftIdeal c :=
    principalIdealRightMap d c a a (by rw [hc, hd, mul_assoc])
  let e : principalLeftIdeal c ≃ₗ[ℂ] principalLeftIdeal d :=
    { f with
      invFun y := q⁻¹ • k y
      left_inv x := by
        apply Subtype.ext
        change q⁻¹ • ((x.val * b) * a) = x.val
        rw [mul_assoc, ← hc,
          principalLeftIdeal_mul_scalar c q (youngSymmetrizer_square t), smul_smul,
          inv_mul_cancel₀ (youngScalar_ne_zero p), one_smul]
      right_inv y := by
        apply Subtype.ext
        change (q⁻¹ • (y.val * a)) * b = y.val
        rw [smul_mul_assoc, mul_assoc, ← hd,
          principalLeftIdeal_mul_scalar d q (reverseYoungSymmetrizer_square t), smul_smul,
          inv_mul_cancel₀ (youngScalar_ne_zero p), one_smul] }
  refine ⟨e, ?_⟩
  intro g x y hy
  change y.val * b = MonoidAlgebra.single g 1 * (x.val * b)
  rw [hy, mul_assoc]

end AdvancedFiniteGroupRepresentations
