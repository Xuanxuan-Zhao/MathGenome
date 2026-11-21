import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.YoungIdempotents
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TransposeSignTwist

noncomputable section
open scoped BigOperators TensorProduct
namespace AdvancedFiniteGroupRepresentations

abbrev transposeCells := @Specs.AdvancedFiniteGroupRepresentations.transposeCells
abbrev transposeTableau := @Specs.AdvancedFiniteGroupRepresentations.transposeTableau
abbrev signAutomorphism := Specs.AdvancedFiniteGroupRepresentations.signAutomorphism
abbrev signRepresentation := Specs.AdvancedFiniteGroupRepresentations.signRepresentation

variable {n : ℕ} {p : Partition n}

@[simp] theorem transposeTableau_row (t : Tableau p) (a : Fin n) :
    labelRow (transposeTableau t) a = labelColumn t a := rfl

@[simp] theorem transposeTableau_column (t : Tableau p) (a : Fin n) :
    labelColumn (transposeTableau t) a = labelRow t a := rfl

theorem transposeTableau_groups (t : Tableau p) :
    rowSubgroup (transposeTableau t) = columnSubgroup t ∧
    columnSubgroup (transposeTableau t) = rowSubgroup t := ⟨rfl, rfl⟩

@[simp] theorem signAutomorphism_single (g : SymmetricGroup n) (z : ℂ) :
    signAutomorphism n (MonoidAlgebra.single g z) =
      MonoidAlgebra.single g (permutationSign g * z) := by
  simp [signAutomorphism, Specs.AdvancedFiniteGroupRepresentations.signAutomorphism,
    Finsupp.linearCombination_single, MonoidAlgebra.smul_single, mul_comm]

theorem signAutomorphism_mul (x y : GroupAlgebra n) :
    signAutomorphism n (x * y) = signAutomorphism n x * signAutomorphism n y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy]
  | single g z =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [mul_add, hx, hy]
    | single h w =>
      simp only [MonoidAlgebra.single_mul_single, signAutomorphism_single, permutationSign_mul]
      congr 1
      ring

theorem signAutomorphism_involutive (n : ℕ) : Function.Involutive (signAutomorphism n) := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g z => simp [← mul_assoc]

/-- Package the multiplicative involution as an algebra equivalence. -/
theorem signAutomorphism_algebraEquiv (n : ℕ) :
    ∃ θ : GroupAlgebra n ≃ₐ[ℂ] GroupAlgebra n,
      (∀ x, θ x = signAutomorphism n x) ∧ Function.Involutive θ := by
  let e : GroupAlgebra n ≃ₗ[ℂ] GroupAlgebra n :=
    { signAutomorphism n with
      invFun := signAutomorphism n
      left_inv := signAutomorphism_involutive n
      right_inv := signAutomorphism_involutive n }
  have he : e 1 = 1 := by
    change signAutomorphism n 1 = 1
    rw [MonoidAlgebra.one_def, signAutomorphism_single]
    simp
  exact ⟨AlgEquiv.ofLinearEquiv e he signAutomorphism_mul,
    (fun _ => rfl), signAutomorphism_involutive n⟩

@[simp] theorem signAutomorphism_column (t : Tableau p) :
    signAutomorphism n (columnAlternator t) = rowSymmetrizer (transposeTableau t) := by
  classical
  change signAutomorphism n (∑ c : columnSubgroup t,
    MonoidAlgebra.single c.val (permutationSign c.val)) =
      ∑ c : columnSubgroup t, MonoidAlgebra.single c.val 1
  simp only [map_sum, signAutomorphism_single, permutationSign_sq]

@[simp] theorem signAutomorphism_row (t : Tableau p) :
    signAutomorphism n (rowSymmetrizer t) = columnAlternator (transposeTableau t) := by
  classical
  change signAutomorphism n (∑ r : rowSubgroup t, MonoidAlgebra.single r.val 1) =
    ∑ r : rowSubgroup t, MonoidAlgebra.single r.val (permutationSign r.val)
  simp only [map_sum, signAutomorphism_single, mul_one]

theorem signAutomorphism_young (t : Tableau p) :
    signAutomorphism n (columnAlternator t) = rowSymmetrizer (transposeTableau t) ∧
    signAutomorphism n (rowSymmetrizer t) = columnAlternator (transposeTableau t) ∧
    signAutomorphism n (youngSymmetrizer t) = reverseYoungSymmetrizer (transposeTableau t) ∧
    signAutomorphism n (reverseYoungSymmetrizer t) = youngSymmetrizer (transposeTableau t) := by
  refine ⟨signAutomorphism_column t, signAutomorphism_row t, ?_, ?_⟩
  · change signAutomorphism n (columnAlternator t * rowSymmetrizer t) = _
    rw [signAutomorphism_mul, signAutomorphism_column, signAutomorphism_row]
    rfl
  · change signAutomorphism n (rowSymmetrizer t * columnAlternator t) = _
    rw [signAutomorphism_mul, signAutomorphism_column, signAutomorphism_row]
    rfl

/-- The sign map sends the whole principal ideal Az onto Aθ(z). -/
theorem signAutomorphism_mem_ideal (z : GroupAlgebra n) (x : principalLeftIdeal z) :
    signAutomorphism n x.val ∈ principalLeftIdeal (signAutomorphism n z) := by
  obtain ⟨a, ha⟩ := x.property
  refine ⟨signAutomorphism n a, ?_⟩
  change signAutomorphism n a * signAutomorphism n z = signAutomorphism n x.val
  change a * z = x.val at ha
  rw [← signAutomorphism_mul, ha]

/-- Restriction of θ to the two corresponding left ideals. -/
def signIdealEquiv (z w : GroupAlgebra n) (h : signAutomorphism n z = w) :
    principalLeftIdeal z ≃ₗ[ℂ] principalLeftIdeal w where
  toFun x := ⟨signAutomorphism n x.val, by
    rw [← h]
    exact signAutomorphism_mem_ideal z x⟩
  invFun y := ⟨signAutomorphism n y.val, by
    have hw : signAutomorphism n w = z := by
      rw [← h, signAutomorphism_involutive n z]
    rw [← hw]
    exact signAutomorphism_mem_ideal w y⟩
  left_inv x := Subtype.ext (signAutomorphism_involutive n x.val)
  right_inv y := Subtype.ext (signAutomorphism_involutive n y.val)
  map_add' x y := Subtype.ext (map_add (signAutomorphism n) x.val y.val)
  map_smul' a x := Subtype.ext (map_smul (signAutomorphism n) a x.val)

@[simp] theorem signIdealEquiv_val (z w : GroupAlgebra n) (h) (x : principalLeftIdeal z) :
    (signIdealEquiv z w h x).val = signAutomorphism n x.val := rfl

/-- θ changes ordinary equivariance into sign equivariance. -/
theorem signIdealEquiv_equivariant (z w : GroupAlgebra n) (h)
    (g : SymmetricGroup n) (x y : principalLeftIdeal z)
    (hy : y.val = MonoidAlgebra.single g 1 * x.val) :
    (signIdealEquiv z w h y).val =
      permutationSign g • (MonoidAlgebra.single g 1 * (signIdealEquiv z w h x).val) := by
  simp only [signIdealEquiv_val, hy, signAutomorphism_mul, signAutomorphism_single, mul_one]
  rw [← smul_mul_assoc, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Compose the original Specht–ideal maps, θ, and the comparison of the two
Young-operator orders. No choice of a different model for Specht is made. -/
theorem transpose_sign_equiv (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (τ : Representation ℂ (SymmetricGroup n) (SpechtModule (transpose p)))
    (hσ : Specs.AdvancedFiniteGroupRepresentations.InheritedSpechtAction p σ)
    (hτ : Specs.AdvancedFiniteGroupRepresentations.InheritedSpechtAction (transpose p) τ) :
    ∃ e : SpechtModule p ≃ₗ[ℂ] SpechtModule (transpose p),
      ∀ g v, e (σ g v) = permutationSign g • τ g (e v) := by
  let t := canonicalTableau p
  let u := transposeTableau t
  obtain ⟨e, _, he⟩ := specht_ideal_isomorphism t
  obtain ⟨e', _, he'⟩ := specht_ideal_isomorphism u
  obtain ⟨r, hr⟩ := young_ideals_isomorphism u
  let d := signIdealEquiv (youngSymmetrizer t) (reverseYoungSymmetrizer u)
    (signAutomorphism_young t).2.2.1
  let l := e.trans d
  let k := e'.trans r
  have hk (g : SymmetricGroup n) (v : SpechtModule (transpose p)) :
      (k (τ g v)).val = MonoidAlgebra.single g 1 * (k v).val :=
    hr g (e' v) (e' (τ g v)) (he' g v (τ g v) (hτ g v))
  have hl (g : SymmetricGroup n) (v : SpechtModule p) :
      (l (σ g v)).val = permutationSign g • (MonoidAlgebra.single g 1 * (l v).val) :=
    signIdealEquiv_equivariant _ _ (signAutomorphism_young t).2.2.1 g (e v) (e (σ g v))
      (he g v (σ g v) (hσ g v))
  let f := l.trans k.symm
  have hf (v : SpechtModule p) : k (f v) = l v := k.apply_symm_apply (l v)
  refine ⟨f, ?_⟩
  intro g v
  apply k.injective
  apply Subtype.ext
  calc
    (k (f (σ g v))).val = (l (σ g v)).val := congrArg Subtype.val (hf _)
    _ = permutationSign g • (MonoidAlgebra.single g 1 * (l v).val) := hl g v
    _ = permutationSign g • (MonoidAlgebra.single g 1 * (k (f v)).val) := by rw [hf]
    _ = (k (permutationSign g • τ g (f v))).val := by
      rw [map_smul]
      exact congrArg (permutationSign g • ·) (hk g (f v)).symm

/-- The sign line has the defining scalar action. -/
@[simp] theorem signRepresentation_apply (g : SymmetricGroup n) (z : ℂ) :
    signRepresentation n g z = permutationSign g * z := rfl

/-- The tensor version of the transpose/sign isomorphism. The bridge from
scalar twisting to tensoring is the inverse of the tensor right unitor. -/
theorem transpose_sign_tensor (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (τ : Representation ℂ (SymmetricGroup n) (SpechtModule (transpose p)))
    (hσ : Specs.AdvancedFiniteGroupRepresentations.InheritedSpechtAction p σ)
    (hτ : Specs.AdvancedFiniteGroupRepresentations.InheritedSpechtAction (transpose p) τ) :
    Nonempty (τ.Equiv (σ.tprod (signRepresentation n))) := by
  obtain ⟨e, he⟩ := transpose_sign_equiv p σ τ hσ hτ
  have hs (g : SymmetricGroup n) (v : SpechtModule (transpose p)) :
      e.symm (τ g v) = permutationSign g • σ g (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, map_smul, he, e.apply_symm_apply, smul_smul,
      permutationSign_sq, one_smul]
  let f := e.symm.trans (TensorProduct.rid ℂ (SpechtModule p)).symm
  refine ⟨Representation.Equiv.mk f ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  change e.symm (τ g v) ⊗ₜ[ℂ] (1 : ℂ) =
    σ g (e.symm v) ⊗ₜ[ℂ] (signRepresentation n g 1)
  rw [hs, signRepresentation_apply, mul_one]
  simpa only [smul_eq_mul, mul_one] using
    (TensorProduct.smul_tmul (R := ℂ) (permutationSign g) (σ g (e.symm v)) (1 : ℂ))

end AdvancedFiniteGroupRepresentations
