import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PolynomialGroupLieComparison
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.LieSchurWeyl
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.PolynomialClassification
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.LengthBound
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.WeylDimension
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalMatrixCartans
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

noncomputable section
open scoped BigOperators Matrix
open Matrix LieAlgebra.SpecialLinear Module
attribute [local instance] LieRing.ofAssociativeRing

namespace LieAlgebrasAndRepresentations.PolynomialGroupLieComparison

open Specs.LieAlgebrasAndRepresentations.PolynomialGroupLieComparison
open AdvancedFiniteGroupRepresentations
open Specs.AdvancedFiniteGroupRepresentations (multiplicityRepresentation)

private def matrixLieAction (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (Coordinates d) :=
  (@lieEquivMatrix' ℂ _ (Fin d) _ _).symm.toLieHom

private def glAction {d n : ℕ} (p : Partition n) :
    Matrix (Fin d) (Fin d) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p) :=
  (derivedTensorMultiplicityLieHom (Coordinates d) p).comp (matrixLieAction d)

private def slAction {d n : ℕ} (p : Partition n) :
    SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p) :=
  (glAction p).comp (sl (Fin d) ℂ).incl

private theorem slAction_spec {d n : ℕ} (p : Partition n) :
    IsDifferentiatedAction (d := d) p (slAction p) := fun _ _ _ => rfl

private theorem differentiated_eq {d n : ℕ} (p : Partition n)
    (ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p))
    (hρ : IsDifferentiatedAction p ρ) : ρ = slAction p := by
  ext A f v
  exact (hρ A f v).trans (slAction_spec p A f v).symm

theorem differentiation : differentiationType := by
  intro d n p
  exact ⟨slAction p, slAction_spec p, fun ρ hρ => differentiated_eq p ρ hρ⟩

private theorem derived_one (d n : ℕ) :
    derivedTensorOperator (Coordinates d) n 1 = (n : ℂ) • 1 := by
  rw [derivedTensorOperator_eq_sum]
  simp [tensorSlotInsertion_eq_map, PiTensorProduct.map_one, Algebra.smul_def]

private theorem glAction_one {d n : ℕ} (p : Partition n) :
    glAction (d := d) p 1 = (n : ℂ) • 1 := by
  ext f v
  change derivedTensorOperator (Coordinates d) n (Matrix.toLin' 1) (f.val v) =
    (n : ℂ) • f.val v
  rw [Matrix.toLin'_one]
  change derivedTensorOperator (Coordinates d) n 1 (f.val v) = _
  rw [derived_one]
  rfl

private theorem stable_gl_of_sl {d n : ℕ} (p : Partition n)
    (W : Submodule ℂ (SchurModule d p)) (hW : IsLieStable (slAction p) W)
    (A : Matrix (Fin d) (Fin d) ℂ) (f : SchurModule d p) (hf : f ∈ W) :
    glAction p A f ∈ W := by
  by_cases hd : d = 0
  · subst d
    have hA : A = 0 := Subsingleton.elim _ _
    simp [hA]
  have hd : 0 < d := Nat.pos_of_ne_zero hd
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  let c := Matrix.trace A / (d : ℂ)
  let S : SpecialLinear d := ⟨A - c • 1, by
    change Matrix.trace (A - c • 1) = 0
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp [c, div_mul_cancel₀ _ hd']⟩
  have hA : A = (S : Matrix (Fin d) (Fin d) ℂ) + c • 1 := (sub_add_cancel _ _).symm
  have heq : glAction p A f = slAction p S f + (c * (n : ℂ)) • f := by
    rw [hA, map_add, map_smul, glAction_one]
    change slAction p S f + c • ((n : ℂ) • f) = _
    rw [smul_smul]
  rw [heq]
  exact W.add_mem (hW S f hf) (W.smul_mem _ hf)

private theorem stable_lie_of_group {d n : ℕ} (p : Partition n)
    (W : Submodule ℂ (SchurModule d p)) (hW : IsGroupStable p W) :
    IsLieStable (slAction p) W := by
  intro A f hf
  apply multiplicity_invariant_endomorphism (Coordinates d) p W _ (slAction p A) f hf
  intro g v hv
  obtain ⟨g', rfl⟩ := (matrixAction d).surjective g
  exact hW g' v hv

private theorem stable_group_of_lie {d n : ℕ} (p : Partition n)
    (W : Submodule ℂ (SchurModule d p)) (hW : IsLieStable (slAction p) W) :
    IsGroupStable p W := by
  intro g f hf
  apply multiplicity_lie_invariant_group (Coordinates d) p W _ (matrixAction d g) f hf
  intro T w hw
  obtain ⟨A, rfl⟩ := ((@lieEquivMatrix' ℂ _ (Fin d) _ _).symm).surjective T
  exact stable_gl_of_sl p W hW A w hw

theorem stable_iff : stable_iffType := by
  intro d n p ρ hρ W
  rw [differentiated_eq p ρ hρ]
  exact ⟨stable_group_of_lie p W, stable_lie_of_group p W⟩

theorem simple_restriction : simple_restrictionType := by
  intro d n p hp ρ hρ
  have hnt : Nontrivial (SchurModule d p) :=
    (tensorMultiplicity_nonzero_iff (Coordinates d) p).2 (by simpa [Coordinates] using hp)
  let := hnt
  refine ⟨hnt, ?_⟩
  rw [differentiated_eq p ρ hρ]
  intro W hW
  apply tensorMultiplicity_lie_irreducible (Coordinates d) p W
  intro T f hf
  obtain ⟨A, rfl⟩ := ((@lieEquivMatrix' ℂ _ (Fin d) _ _).symm).surjective T
  exact stable_gl_of_sl p W hW A f hf

theorem constant_shift : constant_shiftType := by
  intro d n m p q
  cases d with
  | zero => simp
  | succ r =>
    change (∀ i : Fin r, adjacentDifference (d := r + 1) p i =
      adjacentDifference (d := r + 1) q i) ↔ _
    constructor
    · intro h
      refine ⟨(rowLength p 0 : ℤ) - (rowLength q 0 : ℤ), ?_⟩
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ j ih =>
        have hj := h j
        change (rowLength p j.val : ℤ) - (rowLength p (j.val + 1) : ℤ) =
          (rowLength q j.val : ℤ) - (rowLength q (j.val + 1) : ℤ) at hj
        simp only [Fin.val_succ]
        have ih' : (rowLength p j.val : ℤ) - (rowLength q j.val : ℤ) =
          (rowLength p 0 : ℤ) - (rowLength q 0 : ℤ) := ih
        change (rowLength p (j.val + 1) : ℤ) - (rowLength q (j.val + 1) : ℤ) =
          (rowLength p 0 : ℤ) - (rowLength q 0 : ℤ)
        omega
    · rintro ⟨k, hk⟩ i
      have h₁ : (rowLength p i.val : ℤ) - (rowLength q i.val : ℤ) = k := hk i.castSucc
      have h₂ : (rowLength p (i.val + 1) : ℤ) - (rowLength q (i.val + 1) : ℤ) = k := hk i.succ
      change (rowLength p i.val : ℤ) - (rowLength p (i.val + 1) : ℤ) =
        (rowLength q i.val : ℤ) - (rowLength q (i.val + 1) : ℤ)
      omega


private abbrev coordinateBasis (d : ℕ) : Module.Basis (Fin d) ℂ (Coordinates d) :=
  Pi.basisFun ℂ (Fin d)

private abbrev wordBasis (d n : ℕ) :=
  Basis.piTensorProduct (fun _ : Fin n => coordinateBasis d)

private theorem wordBasis_apply {d n : ℕ} (w : Fin n → Fin d) :
    wordBasis d n w = pureTensor (Coordinates d) n (fun a => coordinateBasis d (w a)) :=
  Basis.piTensorProduct_apply _ _

private def wordContent {d n : ℕ} (w : Fin n → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter (fun a => w a = i)).card

private theorem matrixAction_apply {d : ℕ} (g : GeneralLinear d) (v : Coordinates d) :
    matrixAction d g v = (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ v := by
  change Matrix.toLinAlgEquiv' (g : Matrix (Fin d) (Fin d) ℂ) v = _
  rw [Matrix.toLinAlgEquiv'_apply]

private theorem diagonal_mul_basis {d : ℕ} (x : Coordinates d) (i : Fin d) :
    Matrix.diagonal x *ᵥ coordinateBasis d i = x i • coordinateBasis d i := by
  ext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.basisFun_apply, h]

private theorem derived_diagonal_word {d n : ℕ} (x : Coordinates d) (w : Fin n → Fin d) :
    derivedTensorOperator (Coordinates d) n (Matrix.toLin' (Matrix.diagonal x))
        (wordBasis d n w) = (∑ a, x (w a)) • wordBasis d n w := by
  classical
  rw [wordBasis_apply]
  rw [derivedTensorOperator_pure, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.toLin'_apply, diagonal_mul_basis]
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ a _ _ |>.trans
    (by rw [Function.update_eq_self]; rfl)

private theorem group_diagonal_word {d n : ℕ} (x : Fin d → ℂˣ) (w : Fin n → Fin d) :
    diagonalOperator (Coordinates d) n (matrixAction d (diagonalGroup x)) (wordBasis d n w) =
      (∏ a, (x (w a) : ℂ)) • wordBasis d n w := by
  rw [wordBasis_apply]
  rw [diagonal_pureTensor]
  simp only [matrixAction_apply]
  change pureTensor (Coordinates d) n (fun a =>
    Matrix.diagonal (fun i => (x i : ℂ)) *ᵥ coordinateBasis d (w a)) = _
  simp only [diagonal_mul_basis]
  exact (PiTensorProduct.tprod ℂ).map_smul_univ _ _

private theorem prod_word_eq_content {d n : ℕ} (x : Fin d → ℂ) (w : Fin n → Fin d) :
    ∏ a, x (w a) = ∏ i, x i ^ wordContent w i := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := w) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.prod_congr rfl
  intro i _
  calc
    ∏ a ∈ Finset.univ.filter (fun a => w a = i), x (w a) =
        ∏ _a ∈ Finset.univ.filter (fun a => w a = i), x i :=
      Finset.prod_congr rfl fun _ ha => congrArg x (Finset.mem_filter.mp ha).2
    _ = _ := by simp [wordContent]

private theorem sum_word_eq_content {d n : ℕ} (x : Fin d → ℂ) (w : Fin n → Fin d) :
    ∑ a, x (w a) = ∑ i, (wordContent w i : ℂ) * x i := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ a ∈ Finset.univ.filter (fun a => w a = i), x (w a) =
        ∑ _a ∈ Finset.univ.filter (fun a => w a = i), x i :=
      Finset.sum_congr rfl fun _ ha => congrArg x (Finset.mem_filter.mp ha).2
    _ = _ := by simp [wordContent, nsmul_eq_mul]


open LengthBound in
private theorem row_word_content {d n : ℕ} {p : Partition n} (hp : length p ≤ d)
    (q : Tabloid p) (i : Fin d) :
    wordContent (tabloidRowWord hp q) i = rowLength p i.val := by
  induction q using Quotient.inductionOn with
  | _ t =>
    have he : (fun a : Fin n => tabloidRowWord hp (tabloid t) a = i) =
        (fun a => labelRow t a = i.val) := by
      funext a
      exact propext ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    have hc := rowLabels_card t i.val
    change (Finset.univ.filter (fun a => tabloidRowWord hp (tabloid t) a = i)).card = _
    rw [Finset.filter_congr (fun a _ => Iff.of_eq (congrFun he a))]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      rowLabels, Specs.AdvancedFiniteGroupRepresentations.rowLabels, Set.mem_ofPred_eq] using hc

open LengthBound in
private theorem group_diagonal_embedding {d n : ℕ} {p : Partition n} (hp : length p ≤ d)
    (x : Fin d → ℂˣ) :
    groupOnSchur p (diagonalGroup x) (spechtTensorEmbedding (coordinateBasis d) hp) =
      diagonalCharacter p x • spechtTensorEmbedding (coordinateBasis d) hp := by
  have he (u : PermutationModule p) :
      diagonalOperator (Coordinates d) n (matrixAction d (diagonalGroup x))
          (tabloidTensorMap (coordinateBasis d) hp u) =
        diagonalCharacter p x • tabloidTensorMap (coordinateBasis d) hp u := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv, smul_add]
    | single q z =>
      rw [tabloidTensorMap_single, map_smul, ← smul_comm z, ← wordBasis_apply]
      rw [group_diagonal_word, prod_word_eq_content (fun i => (x i : ℂ))]
      simp only [row_word_content, diagonalCharacter]
  apply Subtype.ext
  exact LinearMap.ext fun v => he v.val

open LengthBound in
private theorem lie_diagonal_embedding {d n : ℕ} {p : Partition n} (hp : length p ≤ d)
    (h : Cartan d) :
    slAction p (diagonalLie h) (spechtTensorEmbedding (coordinateBasis d) hp) =
      restrictedWeight p h • spechtTensorEmbedding (coordinateBasis d) hp := by
  have he (u : PermutationModule p) :
      derivedTensorOperator (Coordinates d) n (Matrix.toLin' (Matrix.diagonal h.val))
          (tabloidTensorMap (coordinateBasis d) hp u) =
        restrictedWeight p h • tabloidTensorMap (coordinateBasis d) hp u := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv, smul_add]
    | single q z =>
      rw [tabloidTensorMap_single, map_smul, ← smul_comm z, ← wordBasis_apply]
      rw [derived_diagonal_word, sum_word_eq_content]
      simp only [row_word_content, restrictedWeight, LinearMap.sum_apply,
        LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply,
        smul_eq_mul]
  apply Subtype.ext
  exact LinearMap.ext fun v => he v.val

private theorem diagonal_embedding_ne_zero {d n : ℕ} {p : Partition n} (hp : length p ≤ d) :
    LengthBound.spechtTensorEmbedding (coordinateBasis d) hp ≠ 0 := by
  intro hf
  let t := canonicalTableau p
  have he := congrArg (fun f : SchurModule d p => f.val (spechtPolytabloid t)) hf
  have hz : (spechtPolytabloid t : SpechtModule p) = 0 :=
    LengthBound.spechtTensorEmbedding_injective (coordinateBasis d) hp
      (he.trans (map_zero _).symm)
  exact polytabloid_ne_zero t (congrArg Subtype.val hz)


private def columnAlternation {d n : ℕ} {p : Partition n} (t : Tableau p) :
    Module.End ℂ (TensorPower (Coordinates d) n) :=
  ∑ c : columnSubgroup t, permutationSign c.val • slotOperator (Coordinates d) n c.val

private theorem columnAlternation_eq_zero {d n : ℕ} {p : Partition n} (t : Tableau p)
    (u : Fin n → Coordinates d) (a b : Fin n) (hab : a ≠ b)
    (hcol : labelColumn t a = labelColumn t b) (hu : u a = u b) :
    columnAlternation (d := d) t (pureTensor (Coordinates d) n u) = 0 := by
  classical
  let c : columnSubgroup t := ⟨Equiv.swap a b, Equiv.apply_swap_eq_self hcol⟩
  let y := pureTensor (Coordinates d) n u
  have hc : permutationSign c.val = -1 := by
    simp [c, permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign,
      Equiv.Perm.sign_swap hab]
  have hcy : slotOperator (Coordinates d) n c.val y = y := by
    rw [slot_pureTensor]
    congr 1
    funext k
    exact Equiv.apply_swap_eq_self hu k
  let f := fun g : columnSubgroup t => permutationSign g.val •
    slotOperator (Coordinates d) n g.val y
  have hneg (g : columnSubgroup t) : f ((Equiv.mulRight c) g) = - f g := by
    change permutationSign (g.val * c.val) • slotOperator (Coordinates d) n (g.val * c.val) y =
      -(permutationSign g.val • slotOperator (Coordinates d) n g.val y)
    rw [permutationSign_mul, slot_mul, Module.End.mul_apply, hcy, hc, mul_neg_one]
    exact neg_smul (permutationSign g.val) (slotOperator (Coordinates d) n g.val y)
  have hsum := Equiv.sum_comp (Equiv.mulRight c) f
  simp only [hneg, Finset.sum_neg_distrib] at hsum
  have hz : (2 : ℂ) • (∑ g, f g) = 0 := by
    rw [two_smul, ← eq_neg_iff_add_eq_zero]
    exact hsum.symm
  simpa only [columnAlternation, LinearMap.sum_apply, LinearMap.smul_apply, f, y] using
    (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem single_mul_basis {d : ℕ} (i j k : Fin d) :
    Matrix.single i j (1 : ℂ) *ᵥ coordinateBasis d k =
      if k = j then coordinateBasis d i else 0 := by
  rw [Matrix.single_mulVec_eq]
  by_cases h : k = j
  · subst k
    simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h, Ne.symm h]

open LengthBound in
private theorem upper_kills_embedding {d n : ℕ} {p : Partition n} (hp : length p ≤ d)
    (i j : Fin d) (hij : i < j) :
    slAction p (upperLie i j hij) (spechtTensorEmbedding (coordinateBasis d) hp) = 0 := by
  classical
  let D := derivedTensorOperator (Coordinates d) n (Matrix.toLin' (Matrix.single i j 1))
  let f := spechtTensorEmbedding (coordinateBasis d) hp
  apply tensorMultiplicity_eq_zero_of_polytabloids
  intro t
  let w := tabloidRowWord hp (tabloid t)
  let b := fun a => coordinateBasis d (w a)
  let y := pureTensor (Coordinates d) n b
  have ht : f.val (spechtPolytabloid t) = columnAlternation t y := by
    change tabloidTensorMap (coordinateBasis d) hp (polytabloid t) = _
    rw [polytabloid_sum, map_sum]
    simp only [tabloidTensorMap_single, columnAlternation, LinearMap.sum_apply,
      LinearMap.smul_apply, y, b, w, slot_pureTensor, ← tabloid_smul, tabloidRowWord_smul]
  change D (f.val (spechtPolytabloid t)) = 0
  rw [ht]
  have hcomm : Commute (columnAlternation (d := d) t) D := by
    apply Commute.sum_left
    intro c hc
    exact (derivedTensorOperator_commute _ _ _ _).smul_left _
  rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply]
  change columnAlternation t (derivedTensorOperator _ _ _ (pureTensor _ _ b)) = 0
  rw [derivedTensorOperator_pure, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [Matrix.toLin'_apply]
  change columnAlternation t (pureTensor _ _
    (Function.update b a (Matrix.single i j 1 *ᵥ coordinateBasis d (w a)))) = 0
  rw [single_mul_basis]
  split_ifs with ha
  · have harow : labelRow t a = j.val := congrArg Fin.val ha
    let k := labelColumn t a
    have hcell : (labelRow t a, k) ∈ cells p := (t.symm a).property
    have hnew : (i.val, k) ∈ cells p := by
      apply (cell_iff p _ _).mpr
      exact ((cell_iff p _ _).mp hcell).trans_le
        (rowLength_antitone p (show i.val ≤ labelRow t a by rw [harow]; exact hij.le))
    let a' := t ⟨(i.val, k), hnew⟩
    have har : labelRow t a' = i.val := by
      change (t.symm (t ⟨(i.val, k), hnew⟩)).val.1 = _
      rw [Equiv.symm_apply_apply]
    have hac : labelColumn t a' = k := by
      change (t.symm (t ⟨(i.val, k), hnew⟩)).val.2 = _
      rw [Equiv.symm_apply_apply]
    have haa : a ≠ a' := by
      intro e
      rw [e, har] at harow
      exact hij.ne (Fin.ext harow)
    apply columnAlternation_eq_zero t _ a a' haa hac.symm
    rw [Function.update_self, Function.update_of_ne haa.symm]
    congr 1
    exact Fin.ext har.symm
  · rw [show pureTensor (Coordinates d) n (Function.update b a 0) = 0 from
      (PiTensorProduct.tprod ℂ).map_coord_zero a (Function.update_self ..), map_zero]


private theorem diagonal_repr {d n : ℕ} (x : Fin d → ℂˣ) (y : TensorPower (Coordinates d) n)
    (w : Fin n → Fin d) :
    (wordBasis d n).repr (diagonalOperator (Coordinates d) n
      (matrixAction d (diagonalGroup x)) y) w =
    (∏ i, (x i : ℂ) ^ wordContent w i) * (wordBasis d n).repr y w := by
  let b := wordBasis d n
  let F := (b.coord w).comp (diagonalOperator (Coordinates d) n (matrixAction d (diagonalGroup x)))
  let G := (∏ i, (x i : ℂ) ^ wordContent w i) • b.coord w
  suffices F = G by exact DFunLike.congr_fun this y
  apply b.ext
  intro u
  change b.coord w (diagonalOperator (Coordinates d) n (matrixAction d (diagonalGroup x))
    (b u)) = (∏ i, (x i : ℂ) ^ wordContent w i) * b.coord w (b u)
  rw [group_diagonal_word, prod_word_eq_content (fun i => (x i : ℂ))]
  rw [map_smul, smul_eq_mul, b.coord_apply, b.repr_self, Finsupp.single_apply]
  by_cases hw : w = u
  · subst u
    simp only [ite_true]
  · simp [Ne.symm hw]

private theorem content_of_diagonal_weight {d n : ℕ} {p : Partition n}
    (f : SchurModule d p) (hf : ∀ x : Fin d → ℂˣ,
      groupOnSchur p (diagonalGroup x) f = diagonalCharacter p x • f)
    (v : SpechtModule p) (w : Fin n → Fin d)
    (hw : (wordBasis d n).repr (f.val v) w ≠ 0) :
    ∀ i, wordContent w i = rowLength p i.val := by
  classical
  intro i
  let two : ℂˣ := Units.mk0 2 (by norm_num)
  let x : Fin d → ℂˣ := Function.update (fun _ => 1) i two
  have h := congrArg (fun F : SchurModule d p => (wordBasis d n).repr (F.val v) w) (hf x)
  change (wordBasis d n).repr (diagonalOperator (Coordinates d) n
      (matrixAction d (diagonalGroup x)) (f.val v)) w =
    (wordBasis d n).repr (diagonalCharacter p x • f.val v) w at h
  rw [diagonal_repr, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have he := mul_right_cancel₀ hw h
  unfold diagonalCharacter at he
  have hp (s : Fin d → ℕ) : (∏ j, (x j : ℂ) ^ s j) = (2 : ℂ) ^ s i := by
    rw [Finset.prod_eq_single i]
    · simp [x, two]
    · intro j hj hji
      simp [x, Function.update_of_ne hji]
    · simp
  rw [hp, hp] at he
  have hn : (2 : ℕ) ^ wordContent w i = 2 ^ rowLength p i.val := by exact_mod_cast he
  exact (pow_right_injective₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)) hn

open LengthBound in
private theorem exists_tabloid_of_content {d n : ℕ} {p : Partition n} (hp : length p ≤ d)
    (w : Fin n → Fin d) (hw : ∀ i, wordContent w i = rowLength p i.val) :
    ∃ q : Tabloid p, tabloidRowWord hp q = w := by
  classical
  let t := canonicalTableau p
  let u := tabloidRowWord hp (tabloid t)
  let e (i : Fin d) : {a // u a = i} ≃ {a // w a = i} :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_subtype]
      exact (row_word_content hp (tabloid t) i).trans (hw i).symm)
  let g := Equiv.ofFiberEquiv e
  refine ⟨g • tabloid t, ?_⟩
  rw [tabloidRowWord_smul]
  funext a
  exact (Equiv.ofFiberEquiv_map e (g.symm a)).symm.trans
    (congrArg w (g.apply_symm_apply a))

open LengthBound in
private theorem diagonal_weight_is_scalar {d n : ℕ} {p : Partition n} (hp : length p ≤ d)
    (f : SchurModule d p) (hf : ∀ x : Fin d → ℂˣ,
      groupOnSchur p (diagonalGroup x) f = diagonalCharacter p x • f) :
    ∃ z : ℂ, z • spechtTensorEmbedding (coordinateBasis d) hp = f := by
  classical
  let T := tabloidTensorMap (coordinateBasis d) hp
  have hT (v : SpechtModule p) : f.val v ∈ LinearMap.range T := by
    let S : Set (Fin n → Fin d) := {w | ∀ i, wordContent w i = rowLength p i.val}
    have hS : f.val v ∈ Submodule.span ℂ (wordBasis d n '' S) := by
      apply (wordBasis d n).mem_span_image.mpr
      intro w hw
      exact content_of_diagonal_weight f hf v w (Finsupp.mem_support_iff.mp hw)
    refine Submodule.span_le.mpr ?_ hS
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨q, rfl⟩ := exists_tabloid_of_content hp w hw
    refine ⟨MonoidAlgebra.single q 1, ?_⟩
    rw [wordBasis_apply]
    exact (tabloidTensorMap_single (coordinateBasis d) hp q 1).trans (one_smul _ _)
  let e := LinearEquiv.ofInjective T (tabloidTensorMap_injective (coordinateBasis d) hp)
  let g : SpechtHom p p := ⟨e.symm.toLinearMap.comp (f.val.codRestrict (LinearMap.range T) hT), by
    intro s v u hu
    apply (tabloidTensorMap_injective (coordinateBasis d) hp)
    have he (x : SpechtModule p) : T (e.symm ⟨f.val x, hT x⟩) = f.val x :=
      congrArg Subtype.val (e.apply_symm_apply ⟨f.val x, hT x⟩)
    change T (e.symm ⟨f.val u, hT u⟩) = T (permutationRepresentation p s (e.symm ⟨f.val v, hT v⟩))
    rw [he, tabloidTensorMap_equivariant, he]
    exact f.property s v u hu⟩
  obtain ⟨z, hz⟩ := diagonal_hom_scalar p g
  refine ⟨z, Subtype.ext (LinearMap.ext fun v => ?_)⟩
  have he : T (g.val v) = f.val v :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f.val v, hT v⟩)
  rw [← hz] at he
  change T (z • v.val) = f.val v at he
  change z • T v.val = f.val v
  rwa [map_smul] at he


private theorem sum_adjacent_products (a b : ℕ → ℂ) (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), a i * b i) =
      (∑ j ∈ Finset.range r, (a j - a (j + 1)) * (∑ i ∈ Finset.range (j + 1), b i)) +
        a r * (∑ i ∈ Finset.range (r + 1), b i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ (fun i => a i * b i), ih,
      Finset.sum_range_succ (fun j => (a j - a (j + 1)) * _),
      Finset.sum_range_succ (fun i => b i) (r + 1)]
    ring

private theorem restrictedWeight_eq_sum_succ {r n : ℕ} (p : Partition n) :
    (restrictedWeight p : Module.Dual ℂ (Cartan (r + 1))) =
      ∑ i : Fin r, (adjacentDifference (d := r + 1) p i : ℂ) •
        fundamentalWeight (d := r + 1) i := by
  ext h
  let b : ℕ → ℂ := fun i => if hi : i < r + 1 then h.val ⟨i, hi⟩ else 0
  have hb (i : Fin (r + 1)) : b i.val = h.val i := dite_eq_left i.isLt
  have hzero : (∑ i ∈ Finset.range (r + 1), b i) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [hb]
    have he := LinearMap.mem_ker.mp h.property
    simpa only [sumCoordinates, LinearMap.sum_apply, LinearMap.proj_apply] using he
  have hprefix (j : Fin r) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i.val ≤ j.val), h.val i) =
        ∑ i ∈ Finset.range (j.val + 1), b i := by
    have hfilter : Finset.univ.filter (fun i : Fin (r + 1) => i.val ≤ j.val) =
        Finset.Iic j.castSucc := by
      ext i
      simp [Fin.le_def]
    rw [hfilter]
    simp only [← hb]
    change (∑ i ∈ Finset.Iic j.castSucc, b (Fin.valEmbedding i)) = _
    rw [← Finset.sum_map _ Fin.valEmbedding b, Fin.map_valEmbedding_Iic,
      ← Finset.Iio_add_one_eq_Iic, Nat.Iio_eq_range]
    rfl
  simp only [restrictedWeight, fundamentalWeight, adjacentDifference, Int.cast_sub,
    Int.cast_natCast, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.proj_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  simp_rw [hprefix, ← hb]
  change (∑ i : Fin (r + 1), (rowLength p i.val : ℂ) * b i.val) =
    ∑ j : Fin r, ((rowLength p j.val : ℂ) - rowLength p (j.val + 1)) *
      (∑ i ∈ Finset.range (j.val + 1), b i)
  rw [Fin.sum_univ_eq_sum_range (fun i => (rowLength p i : ℂ) * b i),
    Fin.sum_univ_eq_sum_range (fun j => ((rowLength p j : ℂ) - rowLength p (j + 1)) *
      (∑ i ∈ Finset.range (j + 1), b i))]
  simpa only [hzero, mul_zero, add_zero] using sum_adjacent_products (fun i => (rowLength p i : ℂ)) b r

private theorem restrictedWeight_eq_sum {d n : ℕ} (p : Partition n) :
    (restrictedWeight p : Module.Dual ℂ (Cartan d)) =
      ∑ i : Fin (d - 1), (adjacentDifference (d := d) p i : ℂ) • fundamentalWeight i := by
  cases d with
  | zero => simp [restrictedWeight]
  | succ r => exact restrictedWeight_eq_sum_succ p

theorem highest_line : highest_lineType := by
  intro d n p hp ρ hρ
  rw [differentiated_eq p ρ hρ]
  let v := LengthBound.spechtTensorEmbedding (coordinateBasis d) hp
  refine ⟨v, diagonal_embedding_ne_zero hp, ?_, upper_kills_embedding hp,
    lie_diagonal_embedding hp, restrictedWeight_eq_sum p⟩
  intro f
  rw [Submodule.mem_span_singleton]
  constructor
  · exact diagonal_weight_is_scalar hp f
  · rintro ⟨z, rfl⟩ x
    rw [map_smul, group_diagonal_embedding hp x, smul_comm z]


private def determinantMonomial (d : ℕ) : Alphabet d :=
  ∏ i : Fin d, MvPolynomial.X i

private theorem alternant_add_constant {d : ℕ} (b : Fin d → ℕ) (k : ℕ) :
    alternant (fun i => b i + k) = determinantMonomial d ^ k * alternant b := by
  classical
  let A : Matrix (Fin d) (Fin d) (Alphabet d) := Matrix.of fun i j => MvPolynomial.X i ^ b j
  change (Matrix.of (fun i j : Fin d => (MvPolynomial.X i : Alphabet d) ^ (b j + k))).det =
    _ * A.det
  have hA : Matrix.of (fun i j : Fin d => (MvPolynomial.X i : Alphabet d) ^ (b j + k)) =
      Matrix.of (fun i j => (MvPolynomial.X i : Alphabet d) ^ k * A i j) := by
    ext i j
    simp only [Matrix.of_apply, A, pow_add, mul_comm]
  rw [hA, Matrix.det_mul_column, determinantMonomial, Finset.prod_pow]

private theorem schur_shift_iff {d n m : ℕ} (p : Partition n) (q : Partition m)
    (hp : length p ≤ d) (hq : length q ≤ d) (k : ℕ) :
    schurPolynomial p d = determinantMonomial d ^ k * schurPolynomial q d ↔
      ∀ i : Fin d, rowLength p i.val = rowLength q i.val + k := by
  have hA := schurPolynomial_characterization p d hp
  have hB := schurPolynomial_characterization q d hq
  have hshift : schurPolynomial p d = determinantMonomial d ^ k * schurPolynomial q d ↔
      alternant (shiftedPartition d p) = alternant (fun i => shiftedPartition d q i + k) := by
    rw [alternant_add_constant]
    change _ ↔ partitionAlternant d p = determinantMonomial d ^ k * partitionAlternant d q
    rw [← hA, ← hB, mul_left_comm (determinantMonomial d ^ k)]
    exact (mul_right_inj' (vandermonde_ne_zero d)).symm
  rw [hshift]
  constructor
  · intro he
    let a := shiftedPartition d p
    let b := fun i => shiftedPartition d q i + k
    have ha : StrictAnti a := shiftedPartition_strictAnti p
    have hb : StrictAnti b := fun _ _ h => Nat.add_lt_add_right (shiftedPartition_strictAnti q h) _
    have hcoeff := congrArg (naturalCoefficient a) he
    rw [naturalCoefficient_alternant a a ha ha, naturalCoefficient_alternant a b ha hb,
      ite_eq_left rfl] at hcoeff
    have hab : a = b := by
      by_contra hab
      simp [hab] at hcoeff
    intro i
    have hh := congrFun hab i
    change rowLength p i.val + staircase d i = rowLength q i.val + staircase d i + k at hh
    omega
  · intro hh
    congr 1
    funext i
    change rowLength p i.val + staircase d i = rowLength q i.val + staircase d i + k
    rw [hh]
    omega

private theorem schur_eq_of_diagonal_evals {d : ℕ} {P Q : Alphabet d}
    (h : ∀ x : Fin d → ℂˣ, MvPolynomial.eval (fun i => (x i : ℂ)) P =
      MvPolynomial.eval (fun i => (x i : ℂ)) Q) : P = Q := by
  have hinf : (Set.univ \ ({0} : Set ℂ)).Infinite :=
    Set.infinite_univ.sdiff (Set.finite_singleton 0)
  apply MvPolynomial.funext_set (s := fun _ : Fin d => Set.univ \ ({0} : Set ℂ))
    (fun _ => hinf)
  intro y hy
  have hy' (i : Fin d) : y i ≠ 0 := by simpa using hy i (Set.mem_univ i)
  exact h (fun i => Units.mk0 (y i) (hy' i))

private theorem trace_group_diagonal {d n : ℕ} (p : Partition n) (x : Fin d → ℂˣ) :
    LinearMap.trace ℂ (SchurModule d p) (groupOnSchur p (diagonalGroup x)) =
      MvPolynomial.eval (fun i => (x i : ℂ)) (schurPolynomial p d) := by
  apply weyl_diagonal_character (Coordinates d) p (coordinateBasis d) _ (fun i => (x i).ne_zero)
  intro i
  rw [matrixAction_apply]
  exact diagonal_mul_basis _ _

private theorem det_diagonalGroup {d : ℕ} (x : Fin d → ℂˣ) :
    (↑(Matrix.GeneralLinearGroup.det (diagonalGroup x)) : ℂ) = ∏ i, (x i : ℂ) :=
  Matrix.det_diagonal

private theorem schur_shift_of_equivariant {d n m : ℕ} (p : Partition n) (q : Partition m)
    (k : ℕ) (e : SchurModule d q ≃ₗ[ℂ] SchurModule d p)
    (he : ∀ g v, groupOnSchur p g (e v) =
      (↑(Matrix.GeneralLinearGroup.det g) : ℂ) ^ k • e (groupOnSchur q g v)) :
    schurPolynomial p d = determinantMonomial d ^ k * schurPolynomial q d := by
  apply schur_eq_of_diagonal_evals
  intro x
  rw [map_mul, map_pow, ← trace_group_diagonal p, ← trace_group_diagonal q]
  have hdet : MvPolynomial.eval (fun i => (x i : ℂ)) (determinantMonomial d) =
      (↑(Matrix.GeneralLinearGroup.det (diagonalGroup x)) : ℂ) := by
    simp only [determinantMonomial, map_prod, MvPolynomial.eval_X]
    exact (det_diagonalGroup x).symm
  rw [hdet]
  let c := (↑(Matrix.GeneralLinearGroup.det (diagonalGroup x)) : ℂ) ^ k
  have heq : e.conj (c • groupOnSchur q (diagonalGroup x)) = groupOnSchur p (diagonalGroup x) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.smul_apply, map_smul]
    exact (he (diagonalGroup x) v).symm
  rw [← heq, LinearMap.trace_conj', map_smul]
  rfl


private def determinantPower (d k : ℕ) : LinearGroup (Coordinates d) →* ℂ where
  toFun g := (↑(Matrix.GeneralLinearGroup.det ((matrixAction d).symm g)) : ℂ) ^ k
  map_one' := by simp
  map_mul' := by intros; simp [mul_pow]

private def positiveDetTwist {d m : ℕ} (q : Partition m) (k : ℕ) :
    Representation ℂ (LinearGroup (Coordinates d)) (SchurModule d q) where
  toFun g := determinantPower d k g • multiplicityRepresentation (Coordinates d) q g
  map_one' := by rw [map_one, map_one, one_smul]
  map_mul' g h := by
    rw [map_mul, map_mul, smul_mul_assoc, mul_smul_comm, smul_smul]

private theorem irreducible_of_scalar_multiple {G V : Type*} [Monoid G] [AddCommGroup V]
    [Module ℂ V] [Nontrivial V] {ρ σ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (c : G → ℂ) (hc : ∀ g, c g ≠ 0)
    (hσ : ∀ g, σ g = c g • ρ g) : σ.IsIrreducible := by
  have hn : Nontrivial (Subrepresentation σ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hmem : v ∈ (⊥ : Subrepresentation σ) := by rw [he]; trivial
    exact hv (show v = 0 from hmem)
  apply IsSimpleOrder.mk'
  intro W
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        have hh := W.apply_mem_toSubmodule g hv
        rw [hσ, LinearMap.smul_apply] at hh
        simpa only [smul_smul, inv_mul_cancel₀ (hc g), one_smul] using
          W.toSubmodule.smul_mem (c g)⁻¹ hh }
  rcases eq_top_or_eq_bot W' with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun A : Subrepresentation ρ => A.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun A : Subrepresentation ρ => A.toSubmodule) h)

private theorem positiveDetTwist_irreducible {d m : ℕ} (q : Partition m) (k : ℕ)
    (hq : length q ≤ d) : (positiveDetTwist (d := d) q k).IsIrreducible := by
  have hnt : Nontrivial (SchurModule d q) :=
    (tensorMultiplicity_nonzero_iff (Coordinates d) q).2 (by simpa [Coordinates] using hq)
  exact irreducible_of_scalar_multiple (tensorMultiplicity_irreducible (Coordinates d) q)
    (determinantPower d k) (fun _ => pow_ne_zero _ (Units.ne_zero _)) (fun _ => rfl)

private def determinantPolynomial (d : ℕ) : MvPolynomial (Fin d × Fin d) ℂ :=
  (Matrix.of fun i j => MvPolynomial.X (i, j)).det

private theorem determinantPolynomial_homogeneous (d : ℕ) :
    (determinantPolynomial d).IsHomogeneous d := by
  classical
  rw [determinantPolynomial, Matrix.det_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  have hp : (∏ i : Fin d, (MvPolynomial.X (σ i, i) : MvPolynomial (Fin d × Fin d) ℂ)).IsHomogeneous d := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin d => (MvPolynomial.X (σ i, i) : MvPolynomial (Fin d × Fin d) ℂ))
      (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X ℂ (σ i, i))
  simpa only [Matrix.of_apply, Units.smul_def, zsmul_eq_mul, ← map_intCast (MvPolynomial.C (σ := Fin d × Fin d) (R := ℂ))] using
    hp.C_mul ((Equiv.Perm.sign σ : ℤ) : ℂ)

private theorem determinantPolynomial_eval (d : ℕ) (g : LinearGroup (Coordinates d)) :
    MvPolynomial.eval (Specs.AdvancedFiniteGroupRepresentations.matrixCoordinates (coordinateBasis d) g)
        (determinantPolynomial d) =
      (↑(Matrix.GeneralLinearGroup.det ((matrixAction d).symm g)) : ℂ) := by
  obtain ⟨A, rfl⟩ := (matrixAction d).surjective g
  rw [MulEquiv.symm_apply_apply]
  change _ = (A : Matrix (Fin d) (Fin d) ℂ).det
  rw [determinantPolynomial, RingHom.map_det]
  congr 1
  ext i j
  change (MvPolynomial.eval _) (MvPolynomial.X (i, j)) = _
  rw [MvPolynomial.eval_X]
  change (LinearMap.toMatrix (coordinateBasis d) (coordinateBasis d)
    ((matrixAction d A).toLinearMap)) i j = _
  rw [LinearMap.toMatrix_eq_toMatrix']
  change LinearMap.toMatrix' (Matrix.toLin' (A : Matrix (Fin d) (Fin d) ℂ)) i j = _
  rw [LinearMap.toMatrix'_toLin']

private theorem positiveDetTwist_homogeneous {d m t : ℕ} (q : Partition m) (k : ℕ)
    (b : Basis (Fin t) ℂ (SchurModule d q)) :
    Specs.AdvancedFiniteGroupRepresentations.IsHomogeneousRepresentation
      (coordinateBasis d) b (positiveDetTwist q k) (d * k + m) := by
  intro i j
  obtain ⟨P, hP, hPe⟩ := tensorMultiplicity_homogeneous (Coordinates d) d (coordinateBasis d) q t b i j
  refine ⟨determinantPolynomial d ^ k * P, ((determinantPolynomial_homogeneous d).pow k).mul hP, ?_⟩
  intro g
  rw [map_mul, map_pow, determinantPolynomial_eval, hPe]
  change _ = LinearMap.toMatrix b b
    (determinantPower d k g • multiplicityRepresentation (Coordinates d) q g) i j
  rw [map_smul]
  rfl

private theorem positive_twist_exists {d n m : ℕ} (p : Partition n) (q : Partition m)
    (hp : length p ≤ d) (hq : length q ≤ d) (k : ℕ)
    (hrows : ∀ i : Fin d, rowLength p i.val = rowLength q i.val + k) :
    ∃ e : SchurModule d q ≃ₗ[ℂ] SchurModule d p,
      ∀ g v, groupOnSchur p g (e v) =
        (↑(Matrix.GeneralLinearGroup.det g) : ℂ) ^ k • e (groupOnSchur q g v) := by
  let b := Module.finBasis ℂ (SchurModule d q)
  obtain ⟨p', hp', ⟨e'⟩⟩ := (homogeneous_simple_classification (Coordinates d)
    (SchurModule d q) d _ _ (coordinateBasis d) b (positiveDetTwist q k)
    (positiveDetTwist_homogeneous q k b)).1 (positiveDetTwist_irreducible q k hq)
  have he (g : GeneralLinear d) (v : SchurModule d q) :
      groupOnSchur p' g (e'.toLinearEquiv v) =
        (↑(Matrix.GeneralLinearGroup.det g) : ℂ) ^ k • e'.toLinearEquiv (groupOnSchur q g v) := by
    have h := e'.toIntertwiningMap.isIntertwining _ _ (matrixAction d g) v
    change e'.toLinearEquiv (determinantPower d k (matrixAction d g) • groupOnSchur q g v) =
      groupOnSchur p' g (e'.toLinearEquiv v) at h
    rw [map_smul] at h
    simpa [determinantPower] using h.symm
  have hrows' := (schur_shift_iff p' q hp' hq k).1 (schur_shift_of_equivariant p' q k _ he)
  have hshape : diagram p' = diagram p := by
    apply diagram_eq_of_shiftedPartition_eq p' p hp' hp
    funext i
    change rowLength p' i.val + staircase d i = rowLength p i.val + staircase d i
    rw [hrows' i, hrows i]
  have hsize : d * k + m = n := by
    simpa only [diagram_card] using congrArg YoungDiagram.card hshape
  subst n
  have heq : p' = p := partition_eq_of_diagram_eq p' p hshape
  subst p
  exact ⟨e'.toLinearEquiv, he⟩

private theorem symm_twist {d n m : ℕ} {p : Partition n} {q : Partition m}
    (k : ℤ) (e : SchurModule d q ≃ₗ[ℂ] SchurModule d p)
    (he : ∀ g v, groupOnSchur p g (e v) =
      (↑(Matrix.GeneralLinearGroup.det g) : ℂ) ^ k • e (groupOnSchur q g v)) :
    ∀ g u, groupOnSchur q g (e.symm u) =
      (↑(Matrix.GeneralLinearGroup.det g) : ℂ) ^ (-k) • e.symm (groupOnSchur p g u) := by
  intro g u
  obtain ⟨v, rfl⟩ := e.surjective u
  rw [he g v, map_smul, e.symm_apply_apply, e.symm_apply_apply, smul_smul, _root_.zpow_neg,
    inv_mul_cancel₀ (zpow_ne_zero _ (Units.ne_zero _)), one_smul]

theorem determinant_twist : determinant_twistType := by
  intro d n m p q hp hq k
  have hnat {a b : ℕ} (l : ℕ) (p : Partition a) (q : Partition b)
      (hp : length p ≤ d) (hq : length q ≤ d) :
      (∃ e : SchurModule d q ≃ₗ[ℂ] SchurModule d p,
        ∀ g v, groupOnSchur p g (e v) =
          (↑(Matrix.GeneralLinearGroup.det g) : ℂ) ^ l • e (groupOnSchur q g v)) ↔
        ∀ i : Fin d, (rowLength p i.val : ℤ) - (rowLength q i.val : ℤ) = (l : ℤ) := by
    constructor
    · rintro ⟨e, he⟩ i
      have hi := (schur_shift_iff p q hp hq l).1 (schur_shift_of_equivariant p q l e he) i
      omega
    · intro h
      exact positive_twist_exists p q hp hq l (by intro i; have := h i; omega)
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    simpa only [zpow_natCast] using hnat k p q hp hq
  · have hk' : 0 ≤ -k := by omega
    let l := (-k).toNat
    have hl : (l : ℤ) = -k := Int.toNat_of_nonneg hk'
    have hs := hnat l q p hq hp
    constructor
    · rintro ⟨e, he⟩ i
      have he' := symm_twist k e he
      have hr := hs.1 ⟨e.symm, by simpa only [← hl, zpow_natCast] using he'⟩ i
      change (rowLength p i.val : ℤ) - (rowLength q i.val : ℤ) = k
      omega
    · intro hr
      obtain ⟨e, he⟩ := hs.2 (by
        intro i
        have hi : (rowLength p i.val : ℤ) - (rowLength q i.val : ℤ) = k := hr i
        omega)
      have he' := symm_twist (l : ℤ) e (by simpa only [zpow_natCast] using he)
      exact ⟨e.symm, by simpa only [hl, neg_neg] using he'⟩


private theorem schurModule_finrank_small {d n : ℕ} (p : Partition n)
    (hp : length p ≤ d) (hd : d ≤ 1) : Module.finrank ℂ (SchurModule d p) = 1 := by
  have hdim : Module.finrank ℂ (Coordinates d) = d := by simp [Coordinates]
  have hp' : length p ≤ Module.finrank ℂ (Coordinates d) := by simpa only [hdim] using hp
  have h := schurWeyl_dimension_product (Coordinates d) p hp'
  rw [hdim, weylDimensionProduct_small p d hd] at h
  exact_mod_cast h

/-- In dimension zero the only permitted partition has degree zero, and its
Schur–Weyl line carries the trivial action. Every matrix has determinant one. -/
theorem dimension_zero_action {n : ℕ} (p : Partition n) (hp : length p ≤ 0) :
    n = 0 ∧ Module.finrank ℂ (SchurModule 0 p) = 1 ∧
      ∀ g : GeneralLinear 0, Matrix.GeneralLinearGroup.det g = 1 ∧ groupOnSchur p g = 1 := by
  have hn : n = 0 := by simpa using (sum_rowLength_fin p hp).symm
  refine ⟨hn, schurModule_finrank_small p hp (by decide), fun g => ?_⟩
  have hg : g = 1 := Units.ext (Subsingleton.elim _ _)
  subst g
  simp [groupOnSchur, tensorMultiplicityOperator_one]

/-- In dimension one the partition of degree `n` acts on a line by the
`n`th power of the unique diagonal entry. -/
theorem dimension_one_character {n : ℕ} (p : Partition n) (hp : length p ≤ 1) :
    Module.finrank ℂ (SchurModule 1 p) = 1 ∧
      ∀ g : GeneralLinear 1,
        groupOnSchur p g = ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ n • 1 := by
  have hdim := schurModule_finrank_small p hp (by decide)
  refine ⟨hdim, fun g => ?_⟩
  obtain ⟨ρ, hρ, _⟩ := differentiation (d := 1) p
  obtain ⟨v, hv, hline, _, _, _⟩ := highest_line p hp ρ hρ
  have hspan : ℂ ∙ v = ⊤ := (finrank_eq_one_iff_of_nonzero v hv).mp hdim
  let x : Fin 1 → ℂˣ := fun _ => Matrix.GeneralLinearGroup.det g
  have hg : diagonalGroup x = g := by
    apply Units.ext
    ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j]
    change (Matrix.diagonal fun i => (x i : ℂ)) 0 0 = g.val 0 0
    simp [x]
  have hrow : rowLength p 0 = n := by simpa using sum_rowLength_fin p hp
  apply LinearMap.ext
  intro f
  have h := (hline f).mpr (by rw [hspan]; exact Submodule.mem_top)
  simpa [diagonalCharacter, hrow, x, hg] using h x

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA (cartan epsilon root)
open Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels (direction orderingElement)

/-- At size `r + 1` the Cartan in the comparison is the shared type A Cartan. -/
private theorem diagonalCartan_succ (r : ℕ) : diagonalCartan (r + 1) = cartan r := rfl

private theorem positiveDirection_succ (r : ℕ) :
    positiveDirection (r + 1) = direction r := by
  apply LinearMap.ext
  intro μ
  change (μ ⟨diagonalLie (positiveDirection.heightCoordinates (r + 1)), _⟩).re =
    (μ (orderingElement r)).re
  congr 2
  apply Subtype.ext
  apply Subtype.ext
  change Matrix.diagonal (positiveDirection.heightCoordinates (r + 1)).val = _
  congr 1
  funext i
  simp [positiveDirection.heightCoordinates, sumCoordinates, Nat.cast_succ]

private theorem fundamentalWeight_comp_cartanCoordinates {r : ℕ} (j : Fin r) :
    (fundamentalWeight (d := r + 1) j).comp (cartanCoordinates (r + 1)) =
      Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels.omega r (j.val + 1) := by
  change (cartanCoordinates (r + 1)).dualMap (fundamentalWeight j) = _
  rw [fundamentalWeight, map_sum, Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels.omega]
  simp only [Nat.lt_succ_iff, ← Finset.sum_filter]
  rfl

private theorem restrictedWeight_eq_typeA {r n : ℕ} (p : Partition n) :
    (restrictedWeight p).comp (cartanCoordinates (r + 1)) = ∑ j : Fin r,
      (adjacentDifference (d := r + 1) p j : ℂ) •
        Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels.omega r (j.val + 1) := by
  change (cartanCoordinates (r + 1)).dualMap (restrictedWeight p) = _
  rw [restrictedWeight_eq_sum_succ, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  exact congrArg ((adjacentDifference (d := r + 1) p j : ℂ) • ·)
    (fundamentalWeight_comp_cartanCoordinates j)

private theorem restrictedWeight_coroot {r n : ℕ} (p : Partition n) (i : Fin r) :
    restrictedWeight p (cartanCoordinates (r + 1)
      (RootForm.coroot_value (cartan r) (root r i.castSucc i.succ))) =
      (adjacentDifference (d := r + 1) p i : ℂ) := by
  have hij : i.castSucc ≠ i.succ := (show i.castSucc < i.succ from Nat.lt_succ_self _).ne
  rw [ClassicalRootsA.killing_coroot r i.castSucc i.succ hij]
  let h := Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.coroot r i.castSucc i.succ
  change ((restrictedWeight p).comp (cartanCoordinates (r + 1))) h = _
  rw [restrictedWeight_eq_typeA]
  change (∑ j : Fin r, (adjacentDifference (d := r + 1) p j : ℂ) •
    Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels.omega r (j.val + 1)) h = _
  have hω (j : Fin r) :
      Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels.omega r (j.val + 1) h =
        if i = j then 1 else 0 := by
    have hdiag (a : Fin (r + 1)) : epsilon r a h =
        (if a = i.castSucc then (1 : ℂ) else 0) - (if a = i.succ then 1 else 0) := by
      change h.val.val a a = _
      simp [h, ClassicalRootsA.coroot_apply, Matrix.single_apply, eq_comm]
    rw [Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels.omega, ← Finset.sum_filter,
      LinearMap.sum_apply]
    simp only [hdiag, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_succ]
    by_cases he : i = j
    · subst j
      simp
    · have hne (h : i.val = j.val) : False := he (Fin.ext h)
      by_cases hlt : i.val < j.val
      · have hle : i.val < j.val + 1 := by omega
        simp [he, hlt, hle]
      · have hnle : ¬ i.val < j.val + 1 := by omega
        simp [he, hlt, hnle]
  simp [hω, mul_ite]

private theorem restrictedWeight_eq_iff_adjacent {d n m : ℕ} (p : Partition n) (q : Partition m) :
    (restrictedWeight p : Module.Dual ℂ (Cartan d)) = restrictedWeight q ↔
      ∀ i : Fin (d - 1), adjacentDifference (d := d) p i = adjacentDifference (d := d) q i := by
  constructor
  · intro h
    cases d with
    | zero =>
      intro i
      exact Fin.elim0 i
    | succ r =>
      intro i
      let hᵢ := cartanCoordinates (r + 1)
        (RootForm.coroot_value (cartan r) (root r i.castSucc i.succ))
      have hi := congrArg (fun l : Module.Dual ℂ (Cartan (r + 1)) => l hᵢ) h
      dsimp only [hᵢ] at hi
      rw [restrictedWeight_coroot, restrictedWeight_coroot] at hi
      exact Int.cast_injective hi
  · intro h
    rw [restrictedWeight_eq_sum, restrictedWeight_eq_sum]
    simp only [h]

theorem weight_twist_iff : weight_twist_iffType := by
  intro d n m p q hp hq
  have he := (restrictedWeight_eq_iff_adjacent (d := d) p q).trans (constant_shift p q)
  refine ⟨he, ?_⟩
  rw [he]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨e, he⟩ := (determinant_twist p q hp hq k).2 hk
    exact ⟨k, e, he⟩
  · rintro ⟨k, e, he⟩
    exact ⟨k, (determinant_twist p q hp hq k).1 ⟨e, he⟩⟩

private theorem diagonalLie_cartanCoordinates {d : ℕ} (h : diagonalCartan d) :
    diagonalLie (cartanCoordinates d h) = h.val := by
  apply Subtype.ext
  exact Matrix.IsDiag.diagonal_diag (fun _ _ hij => h.property _ _ hij)

private theorem diagonalCartan_isCartan (d : ℕ) : (diagonalCartan d).IsCartanSubalgebra := by
  cases d with
  | zero =>
    let : IsLieAbelian (diagonalCartan 0) := ⟨fun _ _ => Subsingleton.elim _ _⟩
    refine ⟨inferInstance, ?_⟩
    ext A
    have hz : A = 0 := Subsingleton.elim _ _
    simp [hz]
  | succ r =>
    rw [diagonalCartan_succ]
    exact ClassicalRootsA.cartan_isCartan r

private theorem specialLinear_semisimple (d : ℕ) :
    SolvableRadical.IsSemisimple_value ℂ (SpecialLinear d) := by
  cases d with
  | zero =>
    change LieAlgebra.radical ℂ (SpecialLinear 0) = ⊥
    exact le_bot_iff.mp fun A _ =>
      (LieSubmodule.mem_bot A).mpr (Subsingleton.elim _ _)
  | succ r => exact (ClassicalMatrixCartans.type_a r).1

private theorem rootSet_zero : RootDecomposition.rootSet_value (diagonalCartan 0) = ∅ := by
  ext α
  change (α ≠ 0 ∧ RootDecomposition.rootSpace_value (diagonalCartan 0) α ≠ ⊥) ↔ False
  simp [Submodule.eq_bot_of_subsingleton]

private theorem positiveDirection_root (r : ℕ) (i j : Fin (r + 1)) :
    positiveDirection (r + 1) (root r i j) = (j.val : ℝ) - (i.val : ℝ) := by
  rw [positiveDirection_succ]
  change (root r i j (orderingElement r)).re = _
  rw [ClassicalRootsA.root_apply, Complex.sub_re]
  simp only [orderingElement, Matrix.diagonal_apply_eq, Complex.sub_re, Complex.neg_re,
    Complex.natCast_re]
  ring

private theorem positiveDirection_regular (d : ℕ) :
    VermaModules.Regular (diagonalCartan d) (positiveDirection d) := by
  cases d with
  | zero => simp [VermaModules.Regular, rootSet_zero]
  | succ r =>
    intro α hα
    obtain ⟨i, j, hij, h⟩ := (ClassicalRootsA.root_set r α).mp hα
    rw [h, positiveDirection_root]
    intro he
    apply hij
    exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp he).symm)

private theorem positive_roots_succ (r : ℕ) :
    SerreRelations.positive (diagonalCartan (r + 1)) (positiveDirection (r + 1)) =
      {α | ∃ i j : Fin (r + 1), i < j ∧ α = root r i j} := by
  ext α
  constructor
  · rintro ⟨hα, hφ⟩
    obtain ⟨i, j, _, h⟩ := (ClassicalRootsA.root_set r α).mp hα
    change 0 < positiveDirection (r + 1) α at hφ
    rw [h, positiveDirection_root, sub_pos] at hφ
    exact ⟨i, j, by exact_mod_cast hφ, h⟩
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨(ClassicalRootsA.root_set r _).mpr ⟨i, j, hij.ne, rfl⟩, ?_⟩
    change 0 < positiveDirection (r + 1) (root r i j)
    rw [positiveDirection_root, sub_pos]
    exact_mod_cast hij

private theorem positive_eq_lieSpan_upper (d : ℕ) :
    VermaModules.positive_value (diagonalCartan d) (positiveDirection d) =
      LieSubalgebra.lieSpan ℂ (SpecialLinear d) {A | ∃ i j h, A = upperLie i j h} := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro A ⟨α, hα, hA⟩
    by_cases hz : A = 0
    · rw [hz]
      exact LieSubalgebra.zero_mem _
    have hp : α ∈ SerreRelations.positive (diagonalCartan d) (positiveDirection d) := by
      refine ⟨⟨?_, ?_⟩, hα⟩
      · intro he
        have hpos : 0 < positiveDirection d α := hα
        rw [he, map_zero] at hpos
        exact (lt_irrefl 0) hpos
      · intro he
        rw [he] at hA
        exact hz ((Submodule.mem_bot ℂ).mp hA)
    cases d with
    | zero => exact (hz (Subsingleton.elim _ _)).elim
    | succ r =>
      rw [positive_roots_succ] at hp
      obtain ⟨i, j, hij, rfl⟩ := hp
      change A ∈ rootSpace (cartan r) (root r i j) at hA
      rw [ClassicalRootsA.root_space r i j hij.ne] at hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hA
      exact (LieSubalgebra.lieSpan ℂ _ _).smul_mem c
        (LieSubalgebra.subset_lieSpan ⟨i, j, hij, rfl⟩)
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, j, hij, rfl⟩
    cases d with
    | zero => exact Fin.elim0 i
    | succ r =>
      have hp : root r i j ∈ SerreRelations.positive
          (diagonalCartan (r + 1)) (positiveDirection (r + 1)) := by
        rw [positive_roots_succ]
        exact ⟨i, j, hij, rfl⟩
      exact LieSubalgebra.subset_lieSpan
        ⟨root r i j, hp.2, ClassicalRootsA.rootVector_mem i j hij.ne⟩

private theorem simple_root_upper {d : ℕ}
    (α : SerreRelations.simple (diagonalCartan d) (positiveDirection d)) :
    ∃ (i j : Fin d) (hij : i < j), j.val = i.val + 1 ∧
      upperLie i j hij ∈ RootDecomposition.rootSpace_value (diagonalCartan d) α.val ∧
      upperLie i j hij ≠ 0 := by
  cases d with
  | zero =>
    have hm : α.val ∈ RootDecomposition.rootSet_value (diagonalCartan 0) := α.property.1.1
    rw [rootSet_zero] at hm
    exact hm.elim
  | succ r =>
    have hm := α.property.1
    rw [positive_roots_succ] at hm
    obtain ⟨i, j, hij, hi⟩ := hm
    have hnext : j.val = i.val + 1 := by
      by_contra h
      have hlt : i.val < j.val := hij
      let k : Fin (r + 1) := ⟨i.val + 1, by omega⟩
      have hik : i < k := Nat.lt_succ_self _
      have hkj : k < j := by
        change i.val + 1 < j.val
        omega
      have positive_of_lt {a b : Fin (r + 1)} (hab : a < b) :
          root r a b ∈ SerreRelations.positive (diagonalCartan (r + 1)) (positiveDirection (r + 1)) :=
        (Set.ext_iff.mp (positive_roots_succ r) _).mpr ⟨a, b, hab, rfl⟩
      apply α.property.2 _ (positive_of_lt hik) _ (positive_of_lt hkj)
      rw [hi]
      unfold root
      abel
    refine ⟨i, j, hij, hnext, ?_, ClassicalRootsA.rootVector_ne_zero _ _ hij.ne⟩
    rw [hi]
    exact ClassicalRootsA.rootVector_mem _ _ hij.ne

private theorem positive_annihilates {d n : ℕ} {p : Partition n}
    (ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p))
    (v : SchurModule d p) (hv : ∀ i j h, ρ (upperLie i j h) v = 0)
    (x : VermaModules.positive_value (diagonalCartan d) (positiveDirection d)) :
    ρ (x : SpecialLinear d) v = 0 := by
  let annihilator : LieSubalgebra ℂ (SpecialLinear d) :=
    { carrier := {A | ρ A v = 0}
      zero_mem' := by simp
      add_mem' := by intro A B hA hB; simp_all
      smul_mem' := by intro c A hA; simp_all
      lie_mem' := by
        intro A B hA hB
        change ρ A v = 0 at hA
        change ρ B v = 0 at hB
        change ρ ⁅A, B⁆ v = 0
        rw [ρ.map_lie]
        change ρ A (ρ B v) - ρ B (ρ A v) = 0
        simp [hA, hB] }
  suffices hh : VermaModules.positive_value (diagonalCartan d) (positiveDirection d) ≤ annihilator from
    hh x.property
  rw [positive_eq_lieSpan_upper]
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨i, j, hij, rfl⟩
  exact hv i j hij

section HighestWeight

open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open LieAlgebrasAndRepresentations.VermaModules (character_existsUnique)
open LieAlgebrasAndRepresentations.VermaWeightsUniversal (verma_universal)
open LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
  (highest_weight_iff_positive unique_simple_quotient)

/-- The differentiated Schur module is the simple quotient of the Verma
module with the computed highest weight. -/
theorem highest_quotient : highest_quotientType := by
  classical
  intro d n p hp ρ hρ
  dsimp only
  let H := diagonalCartan d
  let φ := positiveDirection d
  let μ := (restrictedWeight p).comp (cartanCoordinates d)
  let V := SchurModule d p
  letI : H.IsCartanSubalgebra := diagonalCartan_isCartan d
  letI := LieRingModule.compLieHom V ρ
  letI := LieModule.compLieHom V ρ
  obtain ⟨hnt, hsimple⟩ := simple_restriction p hp ρ hρ
  letI : Nontrivial V := hnt
  letI : IsSimpleOrder (LieSubmodule ℂ (SpecialLinear d) V) :=
    { toNontrivial := (LieSubmodule.nontrivial_iff ℂ (SpecialLinear d) V).mpr hnt
      eq_bot_or_eq_top := fun W => by
        rcases hsimple W.toSubmodule (fun A f hf => W.lie_mem hf) with h | h
        · exact Or.inl (LieSubmodule.toSubmodule_injective h)
        · exact Or.inr (LieSubmodule.toSubmodule_injective h) }
  obtain ⟨v, hv, _, hu, hd, _⟩ := highest_line p hp ρ hρ
  have hgen : LieSubmodule.lieSpan ℂ (SpecialLinear d) ({v} : Set V) = ⊤ := by
    rcases eq_bot_or_eq_top (LieSubmodule.lieSpan ℂ (SpecialLinear d) ({v} : Set V)) with h | h
    · have hm : v ∈ LieSubmodule.lieSpan ℂ (SpecialLinear d) ({v} : Set V) :=
        LieSubmodule.subset_lieSpan (Set.mem_singleton v)
      rw [h] at hm
      exact (hv ((LieSubmodule.mem_bot v).mp hm)).elim
    · exact h
  choose i j hij hroot using (fun α : simple H φ => simple_root_upper α)
  let e (α : simple H φ) : SpecialLinear d := upperLie (i α) (j α) (hij α)
  have he (α : simple H φ) : e α ∈ RootDecomposition.rootSpace_value H α.val ∧ e α ≠ 0 :=
    (hroot α).2
  have hss := specialLinear_semisimple d
  have hreg := positiveDirection_regular d
  have hvhw : IsHighestWeight e μ v :=
    (highest_weight_iff_positive hss H φ e he V μ v).2
      ⟨hv, fun h => by
        change ρ h.val v = restrictedWeight p (cartanCoordinates d h) • v
        rw [← diagonalLie_cartanCoordinates h]
        exact hd _, positive_annihilates ρ v hu, hgen⟩
  obtain ⟨χ, hχ, _⟩ := character_existsUnique hss H φ hreg μ
  obtain ⟨f, _, hf⟩ :=
    (verma_universal hss H φ hreg μ χ hχ e he V v hvhw.2.1 hvhw.2.2.1).2
      hv hgen
  obtain ⟨e, _, _⟩ := unique_simple_quotient hss H φ hreg μ χ hχ V f hf
  exact ⟨χ, hχ, ⟨e⟩⟩

end HighestWeight

end LieAlgebrasAndRepresentations.PolynomialGroupLieComparison
