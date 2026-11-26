import Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import LinearAlgebraicGroups.Albert.CliffordModel
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace LinearAlgebraicGroups.Albert.SpinFunctor

open CliffordAlgebra Module SpinSpecification
open scoped TensorProduct

universe u v w w' z z'

noncomputable section

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable (q : QuadraticForm R V) (S : Type z) [CommRing S] [Algebra R S]
variable {I : Type w} [LinearOrder I] (b : Basis I R V)

abbrev spinUnits : SpinSpecification.spinUnitsType.{u,v,z} := SpinSpecification.spinUnits

private def cliffordEquiv := CliffordModel.baseChangeEquiv S q b

open private baseChangeEquiv_reverse baseChangeEquiv_evenOdd
  from LinearAlgebraicGroups.Albert.CliffordModel

private theorem cliffordEquiv_vector (x : S ⊗[R] V) :
    cliffordEquiv q S b (vectors q S x) = ι _ x := by
  induction x with
  | tmul a v => exact CliffordModel.baseChangeEquiv_ι S q b a v
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem cliffordEquiv_even (x : ScalarClifford q S) :
    cliffordEquiv q S b x ∈ evenOdd (CliffordSpecification.coefficientForm S q b) 0 ↔
      x ∈ evenPart q S := by
  rw [← baseChangeEquiv_evenOdd S q b]
  exact ⟨fun ⟨y, hy, he⟩ => (cliffordEquiv q S b).injective he ▸ hy,
    fun h => ⟨x, h, rfl⟩⟩

include b in
private theorem reversion_one : reversion q S 1 = 1 :=
  (cliffordEquiv q S b).injective (by simp [cliffordEquiv, baseChangeEquiv_reverse])

include b in
private theorem reversion_mul (x y : ScalarClifford q S) :
    reversion q S (x * y) = reversion q S y * reversion q S x :=
  (cliffordEquiv q S b).injective (by simp [cliffordEquiv, baseChangeEquiv_reverse])

include b in
private theorem reversion_reversion (x : ScalarClifford q S) :
    reversion q S (reversion q S x) = x :=
  (cliffordEquiv q S b).injective (by simp [cliffordEquiv, baseChangeEquiv_reverse])

include b in
private theorem reversion_even {x : ScalarClifford q S} (h : x ∈ evenPart q S) :
    reversion q S x ∈ evenPart q S := by
  rw [← cliffordEquiv_even q S b, cliffordEquiv, baseChangeEquiv_reverse,
    reverse_mem_evenOdd_iff]
  exact (cliffordEquiv_even q S b x).mpr h

include b in
private theorem even_one : (1 : ScalarClifford q S) ∈ evenPart q S := by
  rw [← cliffordEquiv_even q S b, map_one]
  exact SetLike.one_mem_graded (A := evenOdd (CliffordSpecification.coefficientForm S q b))

include b in
private theorem even_mul {x y : ScalarClifford q S}
    (hx : x ∈ evenPart q S) (hy : y ∈ evenPart q S) : x * y ∈ evenPart q S := by
  rw [← cliffordEquiv_even q S b, map_mul]
  simpa only [add_zero] using SetLike.mul_mem_graded
    ((cliffordEquiv_even q S b x).mpr hx) ((cliffordEquiv_even q S b y).mpr hy)

private theorem reverse_eq_inverse {a : (ScalarClifford q S)ˣ}
    (h : reversion q S a * a = 1) : reversion q S a = ↑a⁻¹ :=
  calc
    reversion q S a = (reversion q S a * a) * ↑a⁻¹ := by simp [mul_assoc]
    _ = ↑a⁻¹ := by rw [h, one_mul]

private theorem conjugate_one (x : ScalarClifford q S) :
    conjugate q S 1 x = x := by simp [conjugate]

private theorem conjugate_mul (a c : (ScalarClifford q S)ˣ) (x : ScalarClifford q S) :
    conjugate q S (a * c) x = conjugate q S a (conjugate q S c x) := by
  simp [conjugate, mul_assoc]

private theorem conjugate_inverse (a : (ScalarClifford q S)ˣ) (x : ScalarClifford q S) :
    conjugate q S a (conjugate q S a⁻¹ x) = x := by
  rw [← conjugate_mul, mul_inv_cancel, conjugate_one]

/-- The spin point group in the scalar-extended Clifford algebra. -/
def spinSubgroup (b : Basis I R V) : Subgroup (ScalarClifford q S)ˣ where
  carrier := spinUnits q S
  one_mem' := by
    refine ⟨even_one q S b, ?_, ?_, ?_⟩
    · simp [reversion_one q S b]
    · intro x hx
      simpa only [conjugate_one] using hx
    · intro x hx
      simpa only [inv_one, conjugate_one] using hx
  mul_mem' := by
    intro a c ha hc
    change a ∈ spinUnits q S at ha
    change c ∈ spinUnits q S at hc
    rcases ha with ⟨ha, han, hav, hai⟩
    rcases hc with ⟨hc, hcn, hcv, hci⟩
    refine ⟨even_mul q S b ha hc, ?_, ?_, ?_⟩
    · change reversion q S ((a : ScalarClifford q S) * c) * (a * c : (ScalarClifford q S)ˣ) = 1
      rw [reversion_mul q S b, Units.val_mul, mul_assoc, ← mul_assoc (reversion q S a), han, one_mul, hcn]
    · intro x hx
      rw [conjugate_mul]
      exact hav (hcv hx)
    · intro x hx
      rw [mul_inv_rev, conjugate_mul]
      exact hci (hai hx)
  inv_mem' := by
    intro a ha
    rcases ha with ⟨ha, hn, hv, hi⟩
    have h := reverse_eq_inverse q S hn
    refine ⟨h ▸ reversion_even q S b ha, ?_, hi, ?_⟩
    · change reversion q S (↑a⁻¹) * ↑a⁻¹ = 1
      rw [← h, reversion_reversion q S b, h, Units.mul_inv]
    · simpa only [inv_inv] using hv

abbrev Spin := spinSubgroup q S b

theorem intrinsicCriterion : SpinSpecification.intrinsicCriterionType.{u,v,w,z} := by
  intro R _ V _ _ I _ q b S _ _
  let e := cliffordEquiv q S b
  have hv (x : S ⊗[R] V) : e (vectors q S x) = ι _ x := cliffordEquiv_vector q S b x
  refine ⟨e, hv, fun a => ?_⟩
  have hn : reverse (e a) * e a = 1 ↔ reversion q S a * a = 1 := by
    have hr : reverse (e a) = e (reversion q S a) := (baseChangeEquiv_reverse S q b a).symm
    rw [hr]
    change e (reversion q S a) * e a = 1 ↔ _
    rw [← map_mul, ← map_one e, e.injective.eq_iff]
  have hc (x : ScalarClifford q S) :
      e (conjugate q S a x) = e a * e x * e ↑a⁻¹ := by simp [conjugate]
  constructor
  · rintro ⟨he, hr, hf, hi⟩
    refine ⟨(cliffordEquiv_even q S b _).mpr he, hn.mpr hr, ?_⟩
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      obtain ⟨t, ht⟩ := hf (LinearMap.mem_range_self _ x)
      refine ⟨t, ?_⟩
      rw [← hv, ht, hc, hv]
    · rintro ⟨x, rfl⟩
      obtain ⟨t, ht⟩ := hi (LinearMap.mem_range_self _ x)
      refine ⟨ι _ t, LinearMap.mem_range_self _ t, ?_⟩
      change e a * ι _ t * e ↑a⁻¹ = ι _ x
      rw [← hv, ← hc, ht, conjugate_inverse, hv]
  · rintro ⟨he, hr, hV⟩
    refine ⟨(cliffordEquiv_even q S b _).mp he, hn.mp hr, ?_, ?_⟩
    · rintro y ⟨x, rfl⟩
      have h : e (conjugate q S a (vectors q S x)) ∈ LinearMap.range
          (ι (CliffordSpecification.coefficientForm S q b)) := by
        rw [hc, hv]
        change _ ∈ (LinearMap.range (ι (CliffordSpecification.coefficientForm S q b)) : Set (CliffordAlgebra (CliffordSpecification.coefficientForm S q b)))
        rw [← hV]
        exact ⟨_, LinearMap.mem_range_self _ x, rfl⟩
      obtain ⟨t, ht⟩ := h
      exact ⟨t, e.injective ((hv t).trans ht)⟩
    · rintro y ⟨x, rfl⟩
      have hx := LinearMap.mem_range_self (ι (CliffordSpecification.coefficientForm S q b)) x
      change _ ∈ (LinearMap.range (ι (CliffordSpecification.coefficientForm S q b)) : Set (CliffordAlgebra (CliffordSpecification.coefficientForm S q b))) at hx
      rw [← hV] at hx
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hx
      change e a * ι _ t * e ↑a⁻¹ = ι _ x at ht
      have ht' : conjugate q S a (vectors q S t) = vectors q S x := e.injective
        ((hc _).trans (by rw [hv, ht, hv]))
      refine ⟨t, ?_⟩
      rw [← ht', ← conjugate_mul, inv_mul_cancel, conjugate_one]

private def vectorProjection : ScalarClifford q S →ₗ[S] S ⊗[R] V :=
  ((CliffordModel.vector_summand q b).choose).baseChange S

private theorem vectorProjection_vector (x : S ⊗[R] V) :
    vectorProjection q S b (vectors q S x) = x := by
  have h := congrArg (LinearMap.baseChange S) (CliffordModel.vector_summand q b).choose_spec
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
  exact LinearMap.congr_fun h x

include b in
private theorem vectors_injective : Function.Injective (vectors q S) :=
  Function.LeftInverse.injective (vectorProjection_vector q S b)

private theorem vectors_projection {x : ScalarClifford q S}
    (h : x ∈ LinearMap.range (vectors q S)) :
    vectors q S (vectorProjection q S b x) = x := by
  obtain ⟨y, rfl⟩ := h
  rw [vectorProjection_vector]

private def conjugationLinear (a : (ScalarClifford q S)ˣ) :
    ScalarClifford q S →ₗ[S] ScalarClifford q S where
  toFun := conjugate q S a
  map_add' x y := by simp only [conjugate, mul_add, add_mul]
  map_smul' t x := by simp only [conjugate, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

private def vectorLinear (a : (ScalarClifford q S)ˣ) : S ⊗[R] V →ₗ[S] S ⊗[R] V :=
  vectorProjection q S b ∘ₗ conjugationLinear q S a ∘ₗ vectors q S

private theorem vectorLinear_characterization (a : (ScalarClifford q S)ˣ)
    (h : Set.MapsTo (conjugate q S a) (LinearMap.range (vectors q S))
      (LinearMap.range (vectors q S))) (x : S ⊗[R] V) :
    vectors q S (vectorLinear q S b a x) = conjugate q S a (vectors q S x) :=
  vectors_projection q S b (h (LinearMap.mem_range_self _ x))

/-- The action by conjugation on the scalar-extended vector module. -/
def vectorAction : Spin q S b →* (S ⊗[R] V) ≃ₗ[S] (S ⊗[R] V) where
  toFun a := LinearEquiv.ofLinearMap (vectorLinear q S b a) (vectorLinear q S b (↑a : _)⁻¹)
    (by
      apply LinearMap.ext
      intro x
      apply vectors_injective q S b
      change vectors q S (vectorLinear q S b a (vectorLinear q S b (↑a : _)⁻¹ x)) = _
      rw [vectorLinear_characterization q S b _ a.property.2.2.1,
        vectorLinear_characterization q S b _ a.property.2.2.2, conjugate_inverse]
      rfl)
    (by
      apply LinearMap.ext
      intro x
      apply vectors_injective q S b
      change vectors q S (vectorLinear q S b (↑a : _)⁻¹ (vectorLinear q S b a x)) = _
      rw [vectorLinear_characterization q S b _ a.property.2.2.2,
        vectorLinear_characterization q S b _ a.property.2.2.1,
        ← conjugate_mul, inv_mul_cancel, conjugate_one]
      rfl)
  map_one' := by
    ext x
    apply vectors_injective q S b
    change vectors q S (vectorLinear q S b (↑(1 : Spin q S b)) x) = vectors q S x
    rw [vectorLinear_characterization q S b _ (1 : Spin q S b).property.2.2.1]
    exact conjugate_one q S _
  map_mul' a c := by
    ext x
    apply vectors_injective q S b
    change vectors q S (vectorLinear q S b (↑(a * c) : _) x) =
      vectors q S (vectorLinear q S b a (vectorLinear q S b c x))
    rw [vectorLinear_characterization q S b _ (a * c).property.2.2.1,
      vectorLinear_characterization q S b _ a.property.2.2.1,
      vectorLinear_characterization q S b _ c.property.2.2.1]
    exact conjugate_mul q S a c _

theorem vectorAction_characterization (a : Spin q S b) :
    IsVectorAction q S a (vectorAction q S b a) :=
  vectorLinear_characterization q S b a a.property.2.2.1

private def orderedBasis : Basis (Finset I) R (CliffordAlgebra q) :=
  (CliffordModel.ordered_basis q b).choose

private theorem orderedBasis_apply (s : Finset I) :
    orderedBasis q b s = CliffordSpecification.orderedWord q b s :=
  (CliffordModel.ordered_basis q b).choose_spec s

@[simp] private theorem orderedBasis_empty : orderedBasis q b ∅ = 1 := by
  rw [orderedBasis_apply]
  simp [CliffordSpecification.orderedWord]

include b in
private theorem scalar_injective : Function.Injective (algebraMap R (CliffordAlgebra q)) := by
  intro r t h
  let c := (orderedBasis q b).coord ∅
  have hc : c 1 = 1 := by
    dsimp [c]
    rw [← orderedBasis_empty q b, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  have hs (a : R) : algebraMap R (CliffordAlgebra q) a = a • (1 : CliffordAlgebra q) := by
    rw [Algebra.smul_def, mul_one]
  simpa only [hs, map_smul, hc, smul_eq_mul, mul_one] using congrArg c h

theorem vectorAction_preserves (a : Spin q S b) (x : S ⊗[R] V) :
    ExtendedForm q S b (vectorAction q S b a x) = ExtendedForm q S b x := by
  let Q := ExtendedForm q S b
  let e := cliffordEquiv q S b
  let A : (ScalarClifford q S)ˣ := a
  let g : (CliffordAlgebra Q)ˣ := Units.map e.toMonoidHom A
  have he : ι Q (vectorAction q S b a x) = (g : CliffordAlgebra Q) * ι Q x * ↑g⁻¹ := by
    change ι Q (vectorAction q S b a x) = e A * ι Q x * e ↑A⁻¹
    have h := congrArg (cliffordEquiv q S b) (vectorAction_characterization q S b a x)
    simpa only [cliffordEquiv_vector, conjugate, map_mul] using h
  apply scalar_injective Q (b.baseChange S)
  change algebraMap S _ (Q (vectorAction q S b a x)) = algebraMap S _ (Q x)
  rw [← ι_sq_scalar Q, he]
  calc
    _ = (g : CliffordAlgebra Q) * (ι Q x * ι Q x) * ↑g⁻¹ := by
      simp only [mul_assoc, ← mul_assoc (↑g⁻¹ : CliffordAlgebra Q), Units.inv_mul, one_mul]
    _ = _ := by
      rw [ι_sq_scalar, ← Algebra.commutes (Q x) (g : CliffordAlgebra Q),
        mul_assoc, Units.mul_inv, mul_one]

/-- The orthogonal homomorphism induced by Clifford conjugation. -/
def orthogonalAction : Spin q S b →* orthogonalGroup q S b :=
  (vectorAction q S b).codRestrict _ (vectorAction_preserves q S b)


theorem orthogonalAction_ker : (orthogonalAction q S b).ker = (vectorAction q S b).ker := by
  ext a
  change orthogonalAction q S b a = 1 ↔ vectorAction q S b a = 1
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem vectorActionSpecification : SpinSpecification.VectorActionType.{u,v,w,z} := by
  intro R _ V _ _ I _ q b S _ _ G hG
  have h : G = Spin q S b := SetLike.coe_injective hG
  subst G
  exact ⟨orthogonalAction q S b, vectorAction_characterization q S b⟩

section ChangeCoefficients

variable {S} {T : Type z'} [CommRing T] [Algebra R T]

/-- Scalar extension along a homomorphism of commutative test algebras. -/
def changeCoefficients (f : S →ₐ[R] T) :
    ScalarClifford q S →ₐ[R] ScalarClifford q T :=
  Algebra.TensorProduct.map f (AlgHom.id R (CliffordAlgebra q))

private def changeModule {M : Type*} [AddCommGroup M] [Module R M] (f : S →ₐ[R] T) :
    S ⊗[R] M →ₗ[R] T ⊗[R] M :=
  TensorProduct.map f.toLinearMap LinearMap.id

private theorem changeModule_baseChange {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : S →ₐ[R] T) (l : M →ₗ[R] N) (x : S ⊗[R] M) :
    changeModule f (l.baseChange S x) = l.baseChange T (changeModule f x) := by
  induction x with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem changeCoefficients_apply (f : S →ₐ[R] T) (x : ScalarClifford q S) :
    changeCoefficients q f x = changeModule f x := rfl

private theorem changeCoefficients_reverse (f : S →ₐ[R] T) (x : ScalarClifford q S) :
    changeCoefficients q f (reversion q S x) = reversion q T (changeCoefficients q f x) :=
  changeModule_baseChange f reverse x

private theorem changeCoefficients_vector (f : S →ₐ[R] T) (x : S ⊗[R] V) :
    changeCoefficients q f (vectors q S x) = vectors q T (changeModule f x) :=
  changeModule_baseChange f (ι q) x

private theorem changeCoefficients_even (f : S →ₐ[R] T) {x : ScalarClifford q S}
    (h : x ∈ evenPart q S) : changeCoefficients q f x ∈ evenPart q T := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨changeModule f y, (changeModule_baseChange f (evenOdd q 0).subtype y).symm⟩

/-- The group homomorphism induced by a change of test algebra. -/
def map (f : S →ₐ[R] T) : Spin q S b →* Spin q T b := by
  let g := Units.map (changeCoefficients q f).toMonoidHom
  have hc (a : (ScalarClifford q S)ˣ) (x : ScalarClifford q S) :
      conjugate q T (g a) (changeCoefficients q f x) =
        changeCoefficients q f (conjugate q S a x) := by simp [conjugate, g]
  have hv (a : (ScalarClifford q S)ˣ)
      (ha : Set.MapsTo (conjugate q S a) (LinearMap.range (vectors q S))
        (LinearMap.range (vectors q S))) :
      Set.MapsTo (conjugate q T (g a)) (LinearMap.range (vectors q T))
        (LinearMap.range (vectors q T)) := by
    rintro y ⟨x, rfl⟩
    induction x with
    | tmul t v =>
      obtain ⟨w, hw⟩ := ha (LinearMap.mem_range_self (vectors q S) (1 ⊗ₜ[R] v))
      have h := congrArg (changeCoefficients q f) hw
      rw [changeCoefficients_vector, ← hc, changeCoefficients_vector] at h
      change vectors q T (changeModule f w) =
        conjugate q T (g a) (vectors q T (f 1 ⊗ₜ[R] v)) at h
      rw [map_one] at h
      have hm : t ⊗ₜ[R] v = t • ((1 : T) ⊗ₜ[R] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hm, map_smul]
      change conjugate q T (g a) (t • vectors q T (1 ⊗ₜ[R] v)) ∈ LinearMap.range (vectors q T)
      simp only [conjugate, mul_smul_comm, smul_mul_assoc]
      rw [← show vectors q T (changeModule f w) =
        (g a : ScalarClifford q T) * vectors q T (1 ⊗ₜ[R] v) * ↑(g a)⁻¹ from h]
      exact
        (LinearMap.range (vectors q T)).smul_mem t
          (LinearMap.mem_range_self (vectors q T) (changeModule f w))
    | add x y hx hy =>
      change conjugate q T (g a) (vectors q T (x + y)) ∈ LinearMap.range (vectors q T)
      simpa only [map_add, conjugate, mul_add, add_mul] using
        (LinearMap.range (vectors q T)).add_mem hx hy
  refine { toFun := fun a => ⟨g a, ?_⟩, map_one' := ?_, map_mul' := ?_ }
  · obtain ⟨he, hn, hf, hi⟩ := a.property
    refine ⟨changeCoefficients_even q f he, ?_, hv a hf, ?_⟩
    · change reversion q T (changeCoefficients q f (a : (ScalarClifford q S)ˣ)) *
        changeCoefficients q f (a : (ScalarClifford q S)ˣ) = 1
      rw [← changeCoefficients_reverse, ← map_mul, hn, map_one]
    · rw [← map_inv g]
      exact hv _ hi
  · apply Subtype.ext
    exact map_one g
  · intro a c
    apply Subtype.ext
    exact map_mul g (a : (ScalarClifford q S)ˣ) (c : (ScalarClifford q S)ˣ)


@[simp] theorem map_id (a : Spin q S b) : map q b (AlgHom.id R S) a = a := by
  apply Subtype.ext
  apply Units.ext
  change changeCoefficients q (AlgHom.id R S) (a : (ScalarClifford q S)ˣ) = _
  exact DFunLike.congr_fun (Algebra.TensorProduct.map_id (R := R) (A := S)
    (B := CliffordAlgebra q)) _

variable {U : Type*} [CommRing U] [Algebra R U]

theorem map_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) (a : Spin q S b) :
    map q b (g.comp f) a = map q b g (map q b f a) := by
  apply Subtype.ext
  apply Units.ext
  change changeCoefficients q (g.comp f) (a : (ScalarClifford q S)ˣ) =
    changeCoefficients q g (changeCoefficients q f (a : (ScalarClifford q S)ˣ))
  generalize (↑(a : (ScalarClifford q S)ˣ) : ScalarClifford q S) = x
  induction x using TensorProduct.inductionOn with
  | tmul s c => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction to vectors commutes with every homomorphism of test algebras. -/
theorem vectorAction_naturality (f : S →ₐ[R] T) (a : Spin q S b) (x : S ⊗[R] V) :
    changeModule f (vectorAction q S b a x) =
      vectorAction q T b (map q b f a) (changeModule f x) := by
  apply vectors_injective q T b
  rw [← changeCoefficients_vector, vectorAction_characterization q S b a,
    vectorAction_characterization q T b (map q b f a), ← changeCoefficients_vector]
  have hu : (↑(map q b f a) : (ScalarClifford q T)ˣ) =
      Units.map (changeCoefficients q f).toMonoidHom a := rfl
  unfold conjugate
  rw [hu]
  simp

end ChangeCoefficients

section Coordinates

variable [Fintype I]

private abbrev EvenIndex (I : Type w) [DecidableEq I] :=
  {s : Finset I // (s.card : ZMod 2) = 0}

private abbrev extendedBasis := (orderedBasis q b).baseChange S

private theorem even_iff_coordinates (x : ScalarClifford q S) :
    x ∈ evenPart q S ↔
      ∀ s : Finset I, (s.card : ZMod 2) ≠ 0 → (extendedBasis q S b).coord s x = 0 := by
  classical
  rw [evenPart, CliffordModel.parity_span q b 0, Submodule.baseChange_span]
  have hgen (s : Finset I) (hs : (s.card : ZMod 2) = 0) :
      extendedBasis q S b s ∈ Submodule.span S
        ((fun x : CliffordAlgebra q => (1 : S) ⊗ₜ[R] x) ''
          (CliffordSpecification.orderedWord q b '' {s | (s.card : ZMod 2) = 0})) := by
    rw [Basis.baseChange_apply, orderedBasis_apply]
    exact Submodule.subset_span ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  constructor
  · intro hx s hs
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hz
      rw [← orderedBasis_apply q b]
      change (extendedBasis q S b).coord s (1 ⊗ₜ[R] orderedBasis q b t) = 0
      rw [← Basis.baseChange_apply S, Basis.coord_apply, Basis.repr_self]
      apply Finsupp.single_eq_of_ne
      rintro rfl
      exact hs ht
    | zero => exact map_zero _
    | add _ _ _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r z _ hz => rw [map_smul, hz, smul_zero]
  · intro h
    rw [← (extendedBasis q S b).sum_repr x]
    apply Submodule.sum_mem
    intro s _
    by_cases hs : (s.card : ZMod 2) = 0
    · exact Submodule.smul_mem _ _ (hgen s hs)
    · rw [← Basis.coord_apply, h s hs, zero_smul]
      exact Submodule.zero_mem _

private def evenElement (c : EvenIndex I → S) : ScalarClifford q S :=
  (extendedBasis q S b).equivFun.symm fun s =>
    if h : (s.card : ZMod 2) = 0 then c ⟨s, h⟩ else 0

@[simp] private theorem evenElement_coord (c : EvenIndex I → S) (s : Finset I) :
    (extendedBasis q S b).coord s (evenElement q S b c) =
      if h : (s.card : ZMod 2) = 0 then c ⟨s, h⟩ else 0 := by
  change (extendedBasis q S b).equivFun (evenElement q S b c) s = _
  rw [evenElement, LinearEquiv.apply_symm_apply]

private theorem evenElement_mem (c : EvenIndex I → S) :
    evenElement q S b c ∈ evenPart q S := by
  apply (even_iff_coordinates q S b _).mpr
  intro s hs
  rw [evenElement_coord, dite_eq_right hs]

private theorem evenElement_coords {x : ScalarClifford q S} (hx : x ∈ evenPart q S) :
    evenElement q S b (fun s => (extendedBasis q S b).coord s.1 x) = x := by
  apply (extendedBasis q S b).equivFun.injective
  funext s
  change (extendedBasis q S b).coord s _ = (extendedBasis q S b).coord s x
  rw [evenElement_coord]
  split_ifs with hs
  · rfl
  · exact ((even_iff_coordinates q S b _).mp hx s hs).symm

variable {S} {T : Type z'} [CommRing T] [Algebra R T]

private theorem changeModule_smul {M : Type*} [AddCommGroup M] [Module R M]
    (f : S →ₐ[R] T) (s : S) (x : S ⊗[R] M) :
    changeModule f (s • x) = f s • changeModule f x := by
  induction x with
  | tmul a x =>
    simp only [TensorProduct.smul_tmul', changeModule, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, smul_eq_mul, map_mul, LinearMap.id_coe, id_eq]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem changeModule_basis {M : Type*} [AddCommGroup M] [Module R M]
    {J : Type*} (B : Basis J R M) (f : S →ₐ[R] T) (j : J) :
    changeModule f (B.baseChange S j) = B.baseChange T j := by
  simp [changeModule]

private theorem changeModule_coord {M : Type*} [AddCommGroup M] [Module R M]
    {J : Type*} [Fintype J] (B : Basis J R M) (f : S →ₐ[R] T) (x : S ⊗[R] M) (j : J) :
    (B.baseChange T).coord j (changeModule f x) = f ((B.baseChange S).coord j x) := by
  classical
  rw [← (B.baseChange S).sum_repr x]
  simp only [map_sum, changeModule_smul, changeModule_basis, map_smul,
    Basis.coord_apply, Basis.repr_self]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : j = i <;> simp [h, smul_eq_mul]

private theorem changeCoefficients_evenElement (f : S →ₐ[R] T) (c : EvenIndex I → S) :
    changeCoefficients q f (evenElement q S b c) = evenElement q T b (f ∘ c) := by
  apply (extendedBasis q T b).equivFun.injective
  funext s
  change (extendedBasis q T b).coord s _ = (extendedBasis q T b).coord s _
  rw [changeCoefficients_apply, changeModule_coord, evenElement_coord, evenElement_coord]
  split_ifs <;> simp

private def vectorResidual (S : Type z) [CommRing S] [Algebra R S] :
    ScalarClifford q S →ₗ[S] ScalarClifford q S :=
  LinearMap.id - (vectors q S).comp (vectorProjection q S b)

omit [Fintype I] in
private theorem vectorResidual_zero (S : Type z) [CommRing S] [Algebra R S]
    (x : ScalarClifford q S) :
    vectorResidual q b S x = 0 ↔ x ∈ LinearMap.range (vectors q S) := by
  change x - vectors q S (vectorProjection q S b x) = 0 ↔ _
  rw [sub_eq_zero]
  exact ⟨fun h => ⟨_, h.symm⟩, fun h => (vectors_projection q S b h).symm⟩

omit [Fintype I] in
private theorem changeCoefficients_vectorResidual (f : S →ₐ[R] T) (x : ScalarClifford q S) :
    changeCoefficients q f (vectorResidual q b S x) =
      vectorResidual q b T (changeCoefficients q f x) := by
  have h := changeModule_baseChange f (CliffordModel.vector_summand q b).choose x
  change changeModule f (vectorProjection q S b x) =
    vectorProjection q T b (changeCoefficients q f x) at h
  change changeCoefficients q f (x - vectors q S (vectorProjection q S b x)) =
    changeCoefficients q f x - vectors q T (vectorProjection q T b (changeCoefficients q f x))
  rw [map_sub, changeCoefficients_vector, h]

private abbrev EquationIndex (I : Type w) [DecidableEq I] :=
  (Bool ⊕ (Bool × I)) × Finset I

private def equationValue (S : Type z) [CommRing S] [Algebra R S]
    (x : ScalarClifford q S) : Bool ⊕ (Bool × I) → ScalarClifford q S
  | .inl true => reversion q S x * x - 1
  | .inl false => x * reversion q S x - 1
  | .inr (true, i) =>
      vectorResidual q b S (x * vectors q S ((b.baseChange S) i) * reversion q S x)
  | .inr (false, i) =>
      vectorResidual q b S (reversion q S x * vectors q S ((b.baseChange S) i) * x)

omit [Fintype I] in
private theorem equationValue_natural (f : S →ₐ[R] T)
    (x : ScalarClifford q S) (j : Bool ⊕ (Bool × I)) :
    changeCoefficients q f (equationValue q b S x j) =
      equationValue q b T (changeCoefficients q f x) j := by
  rcases j with j | ⟨j, i⟩ <;> cases j <;>
    simp only [equationValue, map_sub, map_mul, map_one, changeCoefficients_reverse,
      changeCoefficients_vectorResidual, changeCoefficients_vector, changeModule_basis]

omit [LinearOrder I] in
private theorem normalizes_of_basis (S : Type z) [CommRing S] [Algebra R S]
    (a : (ScalarClifford q S)ˣ)
    (h : ∀ i, conjugate q S a (vectors q S ((b.baseChange S) i)) ∈
      LinearMap.range (vectors q S)) :
    Set.MapsTo (conjugate q S a) (LinearMap.range (vectors q S))
      (LinearMap.range (vectors q S)) := by
  rintro _ ⟨v, rfl⟩
  change conjugationLinear q S a (vectors q S v) ∈ LinearMap.range (vectors q S)
  rw [← (b.baseChange S).sum_repr v]
  simp only [map_sum, map_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)

private def pointOfEquations (S : Type z) [CommRing S] [Algebra R S]
    (x : ScalarClifford q S) (he : x ∈ evenPart q S)
    (h : ∀ j, equationValue q b S x j = 0) : Spin q S b := by
  have hl : reversion q S x * x = 1 := sub_eq_zero.mp (h (.inl true))
  have hr : x * reversion q S x = 1 := sub_eq_zero.mp (h (.inl false))
  let a : (ScalarClifford q S)ˣ := ⟨x, reversion q S x, hr, hl⟩
  refine ⟨a, he, hl, normalizes_of_basis q b S a ?_,
    normalizes_of_basis q b S a⁻¹ ?_⟩
  · intro i
    exact (vectorResidual_zero q b S _).mp (h (.inr (true, i)))
  · intro i
    exact (vectorResidual_zero q b S _).mp (h (.inr (false, i)))

omit [Fintype I] in
private theorem point_equations (S : Type z) [CommRing S] [Algebra R S]
    (a : Spin q S b) (j : Bool ⊕ (Bool × I)) :
    equationValue q b S (a : (ScalarClifford q S)ˣ) j = 0 := by
  let A : (ScalarClifford q S)ˣ := a
  obtain ⟨_, hn, hf, hi⟩ := a.property
  have hr : reversion q S A = ↑A⁻¹ := reverse_eq_inverse q S hn
  rcases j with j | ⟨j, i⟩
  · cases j
    · exact sub_eq_zero.mpr (by rw [hr, Units.mul_inv])
    · exact sub_eq_zero.mpr hn
  · cases j
    · apply (vectorResidual_zero q b S _).mpr
      change reversion q S A * vectors q S ((b.baseChange S) i) * A ∈ LinearMap.range (vectors q S)
      rw [hr]
      exact hi (LinearMap.mem_range_self _ _)
    · apply (vectorResidual_zero q b S _).mpr
      rw [hr]
      exact hf (LinearMap.mem_range_self _ _)

private abbrev PolynomialRing := MvPolynomial (EvenIndex I) R

private def equation (j : EquationIndex I) : PolynomialRing (I := I) (R := R) :=
  let P := PolynomialRing (I := I) (R := R)
  (extendedBasis q P b).coord j.2
    (equationValue q b P (evenElement q P b MvPolynomial.X) j.1)

private def equationIdeal : Ideal (PolynomialRing (I := I) (R := R)) :=
  Ideal.span (Set.range (equation q b))

/-- The universal ring for the even Clifford normalizer of reversion norm one. -/
abbrev CoordinateRing := PolynomialRing (I := I) (R := R) ⧸ equationIdeal q b

instance : Algebra.FinitePresentation R (CoordinateRing q b) :=
  Algebra.FinitePresentation.quotient (I := equationIdeal q b)
    (Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩)

private def variableClass (s : EvenIndex I) : CoordinateRing q b :=
  Ideal.Quotient.mkₐ R (equationIdeal q b) (MvPolynomial.X s)

private theorem equation_evaluate (f : PolynomialRing (I := I) (R := R) →ₐ[R] S)
    (j : EquationIndex I) :
    f (equation q b j) =
      (extendedBasis q S b).coord j.2
        (equationValue q b S (evenElement q S b (f ∘ MvPolynomial.X)) j.1) := by
  rw [equation, ← changeModule_coord, ← changeCoefficients_apply,
    equationValue_natural, changeCoefficients_evenElement]

private def pointFromHom (S : Type z) [CommRing S] [Algebra R S]
    (f : CoordinateRing q b →ₐ[R] S) : Spin q S b := by
  let c := f ∘ variableClass q b
  refine pointOfEquations q b S (evenElement q S b c) (evenElement_mem q S b c) ?_
  intro j
  apply (extendedBasis q S b).equivFun.injective
  funext s
  change (extendedBasis q S b).coord s _ = (extendedBasis q S b).coord s 0
  rw [map_zero]
  let F := f.comp (Ideal.Quotient.mkₐ R (equationIdeal q b))
  change _ = 0
  have h := equation_evaluate q b F (j, s)
  change F (equation q b (j, s)) = (extendedBasis q S b).coord s
    (equationValue q b S (evenElement q S b c) j) at h
  rw [← h]
  change f (Ideal.Quotient.mk (equationIdeal q b) (equation q b (j, s))) = 0
  have hz : Ideal.Quotient.mk (equationIdeal q b) (equation q b (j, s)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self (j, s)))
  rw [hz, map_zero]

private def homFromPoint (S : Type z) [CommRing S] [Algebra R S]
    (a : Spin q S b) : CoordinateRing q b →ₐ[R] S := by
  let c (s : EvenIndex I) := (extendedBasis q S b).coord s.1 (a : (ScalarClifford q S)ˣ)
  let f : PolynomialRing (I := I) (R := R) →ₐ[R] S := MvPolynomial.aeval c
  refine Ideal.Quotient.liftₐ (equationIdeal q b) f ?_
  have h (z : PolynomialRing (I := I) (R := R)) (hz : z ∈ equationIdeal q b) :
      f z = 0 := by
    change z ∈ RingHom.ker f.toRingHom
    apply (Ideal.span_le.mpr ?_) hz
    rintro _ ⟨j, rfl⟩
    change f (equation q b j) = 0
    rw [equation_evaluate]
    have hf : f ∘ MvPolynomial.X = c := by funext s; simp [f]
    rw [hf, evenElement_coords q S b a.property.1, point_equations q b S a, map_zero]
  exact h

@[simp] private theorem homFromPoint_variable (S : Type z) [CommRing S] [Algebra R S]
    (a : Spin q S b) (s : EvenIndex I) :
    homFromPoint q b S a (variableClass q b s) =
      (extendedBasis q S b).coord s.1 (a : (ScalarClifford q S)ˣ) := by
  unfold homFromPoint variableClass
  dsimp only
  rw [← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]

@[simp] private theorem pointFromHom_val (S : Type z) [CommRing S] [Algebra R S]
    (f : CoordinateRing q b →ₐ[R] S) :
    ((pointFromHom q b S f).val : ScalarClifford q S) =
      evenElement q S b (f ∘ variableClass q b) := by
  simp [pointFromHom, pointOfEquations]

/-- Algebra maps out of the coordinate ring correspond to spin points. -/
def pointEquiv (S : Type z) [CommRing S] [Algebra R S] :
    (CoordinateRing q b →ₐ[R] S) ≃ Spin q S b where
  toFun := pointFromHom q b S
  invFun := homFromPoint q b S
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro s
    change homFromPoint q b S (pointFromHom q b S f) (variableClass q b s) =
      f (variableClass q b s)
    rw [homFromPoint_variable, pointFromHom_val, evenElement_coord, dite_eq_left s.2]
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Units.ext
    rw [pointFromHom_val]
    convert evenElement_coords q S b a.property.1 using 2
    funext s
    exact homFromPoint_variable q b S a s

theorem pointEquiv_natural (f : S →ₐ[R] T) (a : CoordinateRing q b →ₐ[R] S) :
    pointEquiv q b T (f.comp a) = map q b f (pointEquiv q b S a) := by
  apply Subtype.ext
  apply Units.ext
  change ((pointFromHom q b T (f.comp a)).val : ScalarClifford q T) =
    changeCoefficients q f ((pointFromHom q b S a).val : ScalarClifford q S)
  rw [pointFromHom_val, pointFromHom_val]
  exact (changeCoefficients_evenElement q b f (a ∘ variableClass q b)).symm

end Coordinates

section Centralizer

open private negativeTriangular changeForm_ordered_list create create_contract_basis
  from LinearAlgebraicGroups.Albert.CliffordModel

omit [LinearOrder I] in
private theorem contract_polar (v : V) (a : CliffordAlgebra q) :
    contractLeft (q.polarBilin v) a = ι q v * a - involute a * ι q v := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap, AlgHom.commutes, Algebra.commutes r, sub_self]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, mul_add, add_mul]
    abel
  | ι_mul x w hx =>
    rw [contractLeft_ι_mul, hx, map_mul, involute_ι, neg_mul, neg_mul,
      ← mul_assoc (ι q v), ι_mul_ι_comm, sub_mul, ← Algebra.smul_def]
    change QuadraticMap.polar q v w • x - ι q w * (ι q v * x - involute x * ι q v) = _
    noncomm_ring

private theorem parity_coord {a : CliffordAlgebra q} (ha : a ∈ evenOdd q 0)
    {s : Finset I} (hs : (s.card : ZMod 2) ≠ 0) : (orderedBasis q b).coord s a = 0 := by
  rw [CliffordModel.parity_span q b 0] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    rw [← orderedBasis_apply q b, Basis.coord_apply, Basis.repr_self]
    have hne : t ≠ s := by
      rintro rfl
      exact hs ht
    exact Finsupp.single_eq_of_ne (Ne.symm hne)
  | zero => exact map_zero _
  | add _ _ _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

private theorem changeForm_orderedBasis (s : Finset I) :
    changeForm (negativeTriangular q b) (orderedBasis q b s) = b.ExteriorAlgebra s := by
  rw [orderedBasis_apply, ExteriorAlgebra.basis_apply_ofCard b (s := s) (n := s.card) rfl]
  let f := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl)
  change changeForm (negativeTriangular q b) (CliffordSpecification.orderedWord q b s) =
    ExteriorAlgebra.ιMulti R s.card (b ∘ f)
  rw [ExteriorAlgebra.ιMulti_apply]
  have h := changeForm_ordered_list q b (List.ofFn f)
    (List.pairwise_ofFn.mpr fun i j hij => f.strictMono hij)
  rw [List.map_ofFn, List.map_ofFn] at h
  exact h

variable [Fintype I]

private theorem contract_coord (a : CliffordAlgebra q) (i : I)
    (ha : contractLeft (b.coord i) a = 0) (s : Finset I) (hi : i ∈ s) :
    (orderedBasis q b).coord s a = 0 := by
  classical
  let B := orderedBasis q b
  let e := changeForm (negativeTriangular q b)
  have he : contractLeft (b.coord i) (e a) = 0 := by
    change contractLeft (b.coord i) (changeForm (negativeTriangular q b) a) = 0
    rw [← changeForm_contractLeft, ha, map_zero]
  have h := congrArg (fun x => b.ExteriorAlgebra.coord s (create (b i) x)) he
  change b.ExteriorAlgebra.coord s (create (b i) (contractLeft (b.coord i) (e a))) =
    b.ExteriorAlgebra.coord s (create (b i) 0) at h
  rw [map_zero, map_zero, ← B.sum_repr a] at h
  simp only [map_sum, map_smul, changeForm_orderedBasis, B, e, create_contract_basis] at h
  rw [Finset.sum_eq_single s] at h
  · simpa [hi, Basis.coord_apply, Basis.repr_self] using h
  · intro t _ ht
    by_cases hit : i ∈ t
    · simp [hit, Basis.coord_apply, Basis.repr_self, Ne.symm ht]
    · simp [hit]
  · simp

/-- The even vector centralizer is scalar whenever every nonempty even set of basis
indices contains one whose dual coordinate is supplied by the polar pairing. -/
theorem evenCentralizer_of_coordinates
    (hp : ∀ s : Finset I, s.Nonempty → (s.card : ZMod 2) = 0 →
      ∃ i ∈ s, ∃ v, q.polarBilin v = b.coord i)
    {a : CliffordAlgebra q} (he : a ∈ evenOdd q 0)
    (hc : ∀ v, Commute a (ι q v)) :
    ∃ t : R, a = algebraMap R _ t := by
  classical
  let B := orderedBasis q b
  refine ⟨B.coord ∅ a, ?_⟩
  have hzero (s : Finset I) (hs : s ≠ ∅) : B.coord s a = 0 := by
    by_cases h : (s.card : ZMod 2) = 0
    · obtain ⟨i, hi, v, hv⟩ := hp s (Finset.nonempty_iff_ne_empty.mpr hs) h
      apply contract_coord q b a i _ s hi
      rw [← hv, contract_polar, involute_eq_of_mem_even he, (hc v).eq, sub_self]
    · exact parity_coord q b he h
  conv_lhs => rw [← B.sum_repr a]
  rw [Finset.sum_eq_single ∅]
  · rw [← Basis.coord_apply]
    change (B.coord ∅ a) • orderedBasis q b ∅ = _
    rw [orderedBasis_empty, Algebra.smul_def, mul_one]
  · intro s _ hs
    rw [← Basis.coord_apply, hzero s hs, zero_smul]
  · simp

omit [Fintype I] in
private theorem polar_baseChange_tmul (v w : V) :
    (ExtendedForm q S b).polarBilin (1 ⊗ₜ[R] v) (1 ⊗ₜ[R] w) =
      algebraMap R S (q.polarBilin v w) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar, ← TensorProduct.tmul_add]
  simp only [ExtendedForm, CliffordModel.coefficientForm_tmul, one_mul, ← map_sub]
  rfl

omit [Fintype I] in
private theorem polarCoordinate_baseChange (v : V) (i : I) (h : q.polarBilin v = b.coord i) :
    (ExtendedForm q S b).polarBilin (1 ⊗ₜ[R] v) = (b.baseChange S).coord i := by
  classical
  apply (b.baseChange S).ext
  intro j
  rw [Basis.baseChange_apply, polar_baseChange_tmul, h, Basis.coord_apply, Basis.repr_self]
  rw [← Basis.baseChange_apply S, Basis.coord_apply, Basis.repr_self]
  by_cases hij : i = j <;> simp [hij]

private theorem scalarCentralizer_baseChange
    (hp : ∀ s : Finset I, s.Nonempty → (s.card : ZMod 2) = 0 →
      ∃ i ∈ s, ∃ v, q.polarBilin v = b.coord i)
    {a : ScalarClifford q S} (ha : a ∈ evenPart q S)
    (hc : ∀ x, Commute a (vectors q S x)) :
    ∃ t : S, a = algebraMap S _ t := by
  let e := cliffordEquiv q S b
  obtain ⟨t, ht⟩ := evenCentralizer_of_coordinates (ExtendedForm q S b) (b.baseChange S)
    (fun s hs he => by
      obtain ⟨i, hi, v, hv⟩ := hp s hs he
      exact ⟨i, hi, 1 ⊗ₜ[R] v, polarCoordinate_baseChange q S b v i hv⟩)
    ((cliffordEquiv_even q S b a).mpr ha) (fun x => by
      have h := (hc x).map e
      have hx : e (vectors q S x) = ι (ExtendedForm q S b) x := cliffordEquiv_vector q S b x
      rwa [hx] at h)
  exact ⟨t, e.injective (ht.trans (e.commutes t).symm)⟩

omit [Fintype I] in
private theorem orderedBasis_singleton (j : I) : orderedBasis q b {j} = ι q (b j) := by
  classical
  let r := ({j} : Finset I)
  have hc : r.card = 1 := Finset.card_singleton _
  rw [orderedBasis_apply]
  unfold CliffordSpecification.orderedWord
  let e := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := r) rfl)
  change (List.ofFn (fun i : Fin r.card => ι q (b (e i)))).prod = _
  have he (i : Fin r.card) : e i = j := by
    have hm : e i ∈ r := Finset.orderEmbOfFin_mem r rfl i
    simpa [r] using hm
  simp only [he, List.ofFn_const, List.prod_replicate, hc, pow_one]

omit [LinearOrder I] in
private theorem involute_of_two_eq_zero (h₂ : (2 : R) = 0) (a : CliffordAlgebra q) :
    involute a = a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => exact AlgHom.commutes _ _
  | ι v =>
    rw [involute_ι]
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_smul R, h₂, zero_smul]
  | mul x y hx hy => rw [map_mul, hx, hy]
  | add x y hx hy => rw [map_add, hx, hy]

private theorem centralizer_coord (h₂ : (2 : R) = 0)
    (a : CliffordAlgebra q) (hc : ∀ v, Commute a (ι q v))
    {i : I} (v : V) (hv : q.polarBilin v = b.coord i) {s : Finset I} (hi : i ∈ s) :
    (orderedBasis q b).coord s a = 0 := by
  apply contract_coord q b a i _ s hi
  rw [← hv, contract_polar, involute_of_two_eq_zero q h₂, (hc v).eq, sub_self]

private theorem charTwo_scalar_of_coordinates (h₂ : (2 : R) = 0)
    (hpolar : ∀ i, ∃ v, q.polarBilin v = b.coord i)
    (a : CliffordAlgebra q) (hc : ∀ v, Commute a (ι q v)) :
    ∃ t : R, a = algebraMap R _ t := by
  classical
  let B := orderedBasis q b
  refine ⟨B.coord ∅ a, ?_⟩
  conv_lhs => rw [← B.sum_repr a]
  rw [Finset.sum_eq_single ∅]
  · rw [← Basis.coord_apply]
    change (B.coord ∅ a) • orderedBasis q b ∅ = _
    rw [orderedBasis_empty, Algebra.smul_def, mul_one]
  · intro s _ hs
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨v, hv⟩ := hpolar i
    rw [← Basis.coord_apply, centralizer_coord q b h₂ a hc v hv hi, zero_smul]
  · simp

private theorem charTwo_radical_of_coordinates (h₂ : (2 : R) = 0) (j₀ : I)
    (hpolar : ∀ i ≠ j₀, ∃ v, q.polarBilin v = b.coord i)
    (a : CliffordAlgebra q) (hc : ∀ v, Commute a (ι q v)) :
    ∃ t s : R, a = algebraMap R _ t + s • ι q (b j₀) := by
  classical
  let B := orderedBasis q b
  refine ⟨B.coord ∅ a, B.coord {j₀} a, ?_⟩
  conv_lhs => rw [← B.sum_repr a]
  rw [← Finset.sum_subset (s₁ := {∅, {j₀}}) (Finset.subset_univ _) (fun s _ hs => ?_)]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton, ← Basis.coord_apply, ← Basis.coord_apply]
    change (B.coord ∅ a) • orderedBasis q b ∅ + (B.coord {j₀} a) • orderedBasis q b {j₀} = _
    rw [orderedBasis_empty, orderedBasis_singleton, Algebra.smul_def (B.coord ∅ a) (1 : CliffordAlgebra q), mul_one]
  · have hs' : s ≠ ∅ ∧ s ≠ {j₀} := by simpa using hs
    have hi : ∃ i ∈ s, i ≠ j₀ := by
      by_contra! h
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs'.1
      exact hs'.2 (Finset.eq_singleton_iff_unique_mem.mpr ⟨h i hi ▸ hi, h⟩)
    obtain ⟨i, hi, hij⟩ := hi
    obtain ⟨v, hv⟩ := hpolar i hij
    rw [← Basis.coord_apply, centralizer_coord q b h₂ a hc v hv hi, zero_smul]

end Centralizer

section FieldCentralizer

variable {K : Type u} [Field K] {W : Type v} [AddCommGroup W] [Module K W]
variable (Q : QuadraticForm K W) (A : Type z) [CommRing A] [Algebra K A]
variable {J : Type w} [LinearOrder J] [Fintype J] (c : Basis J K W)

private theorem polar_flip : Q.polarBilin.flip = Q.polarBilin := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact QuadraticMap.polar_comm Q w v


include c in
omit [LinearOrder J] in
private theorem polar_range :
    LinearMap.range Q.polarBilin = (LinearMap.ker Q.polarBilin).dualAnnihilator := by
  let : FiniteDimensional K W := Module.Finite.of_basis c
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip, polar_flip]

include c in
omit [LinearOrder J] in
private theorem radicalBasis (r : W) (hr : Q r ≠ 0) (hb : LinearMap.ker Q.polarBilin = K ∙ r) :
    ∃ (J : Type v) (d : Basis J K W) (j : J),
      d j = r ∧ ∀ i ≠ j, ∃ v, Q.polarBilin v = d.coord i := by
  classical
  have hr0 : r ≠ 0 := fun h => hr (by simp [h])
  have hind : LinearIndepOn K id ({r} : Set W) := (linearIndepOn_singleton_iff K).mpr hr0
  let d := Basis.extend hind
  let j₀ : hind.extend (Set.subset_univ _) := ⟨r, hind.subset_extend _ (Set.mem_singleton r)⟩
  have hd : d j₀ = r := Basis.extend_apply_self hind j₀
  refine ⟨_, d, j₀, hd, fun i hne => ?_⟩
  change d.coord i ∈ LinearMap.range Q.polarBilin
  rw [polar_range Q c, hb, Submodule.mem_dualAnnihilator]
  intro w hw
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hcoord : d.coord i r = 0 := by
    calc
      d.coord i r = d.coord i (d j₀) := congrArg (d.coord i) hd.symm
      _ = 0 := by simp [Basis.coord_apply, Basis.repr_self, hne]
  rw [map_smul, hcoord, smul_zero]

private theorem two_eq_zero_algebra (h₂ : (2 : K) = 0) : (2 : A) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap K A) h₂

include c in
/-- In characteristic two, a nonsingular polar pairing gives a scalar vector centralizer
in the full Clifford algebra on every test algebra. -/
theorem charTwo_scalarCentralizer (h₂ : (2 : K) = 0) (hb : LinearMap.ker Q.polarBilin = ⊥)
    (a : ScalarClifford Q A) (hc : ∀ x, Commute a (vectors Q A x)) :
    ∃ t : A, a = algebraMap A _ t := by
  let e := cliffordEquiv Q A c
  have hp (i : J) : ∃ v, Q.polarBilin v = c.coord i := by
    change c.coord i ∈ LinearMap.range Q.polarBilin
    rw [polar_range Q c, hb, Submodule.dualAnnihilator_bot]
    trivial
  obtain ⟨t, ht⟩ := charTwo_scalar_of_coordinates (ExtendedForm Q A c) (c.baseChange A)
    (two_eq_zero_algebra A h₂)
    (fun i => by
      obtain ⟨v, hv⟩ := hp i
      exact ⟨1 ⊗ₜ[K] v, polarCoordinate_baseChange Q A c v i hv⟩)
    (e a) (fun x => by
      have h := (hc x).map e
      have hx : e (vectors Q A x) = ι (ExtendedForm Q A c) x := cliffordEquiv_vector Q A c x
      rwa [hx] at h)
  exact ⟨t, e.injective (ht.trans (e.commutes t).symm)⟩

include c in
omit [LinearOrder J] in
/-- In characteristic two with regular radical line, the full vector centralizer is
spanned by the scalar and the radical vector on every test algebra. -/
theorem charTwo_radicalCentralizer (h₂ : (2 : K) = 0) (r : W) (hr : Q r ≠ 0)
    (hb : LinearMap.ker Q.polarBilin = K ∙ r)
    (a : ScalarClifford Q A) (hc : ∀ x, Commute a (vectors Q A x)) :
    ∃ t s : A, a = algebraMap A _ t + s • vectors Q A (1 ⊗ₜ[K] r) := by
  let : FiniteDimensional K W := Module.Finite.of_basis c
  obtain ⟨J', d, j₀, hd, hp⟩ := radicalBasis Q c r hr hb
  let := FiniteDimensional.fintypeBasisIndex d
  let ord := Fintype.equivFin J'
  let := LinearOrder.lift' ord ord.injective
  let e := cliffordEquiv Q A d
  obtain ⟨t, s, ht⟩ := charTwo_radical_of_coordinates (ExtendedForm Q A d) (d.baseChange A)
    (two_eq_zero_algebra A h₂) j₀
    (fun i hi => by
      obtain ⟨v, hv⟩ := hp i hi
      exact ⟨1 ⊗ₜ[K] v, polarCoordinate_baseChange Q A d v i hv⟩)
    (e a) (fun x => by
      have h := (hc x).map e
      have hx : e (vectors Q A x) = ι (ExtendedForm Q A d) x := cliffordEquiv_vector Q A d x
      rwa [hx] at h)
  refine ⟨t, s, e.injective ?_⟩
  rw [ht, map_add, map_smul, e.commutes, Basis.baseChange_apply, hd]
  rw [show e (vectors Q A (1 ⊗ₜ[K] r)) = ι (ExtendedForm Q A d) (1 ⊗ₜ[K] r) from
    cliffordEquiv_vector Q A d _]

include c in
omit [Fintype J] in
/-- Polar-radical vectors commute with all Clifford vectors in characteristic two. -/
theorem charTwo_radicalVector_commute (h₂ : (2 : K) = 0) (r : W)
    (hr : r ∈ LinearMap.ker Q.polarBilin) (x : A ⊗[K] W) :
    Commute (vectors Q A (1 ⊗ₜ[K] r)) (vectors Q A x) := by
  let qA := ExtendedForm Q A c
  let e := cliffordEquiv Q A c
  have hzero : qA.polarBilin (1 ⊗ₜ[K] r) = 0 := by
    apply (c.baseChange A).ext
    intro i
    have h : Q.polarBilin r = 0 := hr
    rw [Basis.baseChange_apply, polar_baseChange_tmul Q A c, h, LinearMap.zero_apply,
      map_zero, LinearMap.zero_apply]
  have h := contract_polar qA (1 ⊗ₜ[K] r) (ι qA x)
  rw [hzero, map_zero, LinearMap.zero_apply, involute_of_two_eq_zero qA (two_eq_zero_algebra A h₂)] at h
  show vectors Q A (1 ⊗ₜ[K] r) * vectors Q A x = vectors Q A x * vectors Q A (1 ⊗ₜ[K] r)
  apply e.injective
  simp only [map_mul]
  have he (v) : e (vectors Q A v) = ι qA v := cliffordEquiv_vector Q A c v
  rw [he, he]
  exact sub_eq_zero.mp h.symm

include c in
omit [Fintype J] in
/-- The image of the polar radical in the full Clifford algebra is central in characteristic two. -/
theorem charTwo_radical_commutes (h₂ : (2 : K) = 0) (r : W)
    (hr : r ∈ LinearMap.ker Q.polarBilin) (a : ScalarClifford Q A) :
    Commute (vectors Q A (1 ⊗ₜ[K] r)) a := by
  let qA := ExtendedForm Q A c
  let e := cliffordEquiv Q A c
  let x := vectors Q A (1 ⊗ₜ[K] r)
  have h (y : CliffordAlgebra qA) : Commute (e x) y := by
    induction y using CliffordAlgebra.induction with
    | algebraMap s => exact (Algebra.commutes s _).symm
    | ι v =>
      have hv := (charTwo_radicalVector_commute Q A c h₂ r hr v).map e
      rw [show e (vectors Q A v) = ι qA v from cliffordEquiv_vector Q A c v] at hv
      exact hv
    | mul y z hy hz => exact hy.mul_right hz
    | add y z hy hz => exact hy.add_right hz
  show x * a = a * x
  apply e.injective
  simpa only [map_mul] using (h (e a)).eq

include c in
theorem charTwo_radicalCentralizer_iff (h₂ : (2 : K) = 0) (r : W)
    (hr : Q r ≠ 0) (hb : LinearMap.ker Q.polarBilin = K ∙ r) (a : ScalarClifford Q A) :
    (∀ x, Commute a (vectors Q A x)) ↔
      ∃ t s : A, a = algebraMap A _ t + s • vectors Q A (1 ⊗ₜ[K] r) := by
  refine ⟨charTwo_radicalCentralizer Q A c h₂ r hr hb a, ?_⟩
  rintro ⟨t, s, rfl⟩ x
  have hr' : r ∈ LinearMap.ker Q.polarBilin := hb ▸ Submodule.mem_span_singleton_self r
  rw [Algebra.smul_def]
  have commScalar (k : A) : Commute (algebraMap A (ScalarClifford Q A) k) (vectors Q A x) :=
    Algebra.commutes k _
  exact (commScalar t).add_left
    ((commScalar s).mul_left (charTwo_radicalVector_commute Q A c h₂ r hr' x))

include c in
/-- The scalar centralizer theorem after arbitrary scalar extension of a regular field form. -/
theorem regular_scalarCentralizer
    (hQ : LinearMap.ker Q.polarBilin = ⊥ ∨
      ∃ r : W, Q r ≠ 0 ∧ LinearMap.ker Q.polarBilin = K ∙ r)
    {a : ScalarClifford Q A} (he : a ∈ evenPart Q A)
    (hc : ∀ x, Commute a (vectors Q A x)) :
    ∃ t : A, a = algebraMap A _ t := by
  classical
  let : FiniteDimensional K W := Module.Finite.of_basis c
  rcases hQ with hb | ⟨r, hr, hb⟩
  · apply scalarCentralizer_baseChange Q A c _ he hc
    intro s hs _
    obtain ⟨i, hi⟩ := hs
    refine ⟨i, hi, ?_⟩
    change c.coord i ∈ LinearMap.range Q.polarBilin
    rw [polar_range Q c, hb, Submodule.dualAnnihilator_bot]
    trivial
  · obtain ⟨J', d, j₀, _, hd⟩ := radicalBasis Q c r hr hb
    let := FiniteDimensional.fintypeBasisIndex d
    let e := Fintype.equivFin J'
    let := LinearOrder.lift' e e.injective
    apply scalarCentralizer_baseChange Q A d _ he hc
    intro s hs hp
    have hn : 1 < s.card := by
      have hpos := Finset.card_pos.mpr hs
      by_contra! h
      have h1 : s.card = 1 := by omega
      rw [h1] at hp
      exact one_ne_zero hp
    obtain ⟨i, hi, hne⟩ := Finset.exists_mem_ne hn j₀
    exact ⟨i, hi, hd i hne⟩

theorem charTwoCentralizersSpecification : SpinSpecification.CharTwoCentralizersType.{u,v,w,z} := by
  intro K _ V _ _ I _ _ q b S _ _ h₂ a
  constructor
  · intro hb
    exact ⟨charTwo_scalarCentralizer q S b h₂ hb a, fun ⟨t, h⟩ x =>
      h.symm ▸ (show Commute (algebraMap S (ScalarClifford q S) t) (vectors q S x) from
        Algebra.commutes t _)⟩
  · intro r hr hb
    exact charTwo_radicalCentralizer_iff q S b h₂ r hr hb a

theorem charTwoRadicalActionSpecification :
    SpinSpecification.CharTwoRadicalActionType.{u,v,w,z} := by
  intro K _ V _ _ I _ q b S _ _ h₂ a g hg r hr
  apply vectors_injective q S b
  rw [hg (1 ⊗ₜ[K] r)]
  change a.val * vectors q S (1 ⊗ₜ[K] r) * ↑a⁻¹ = vectors q S (1 ⊗ₜ[K] r)
  rw [(charTwo_radical_commutes q S b h₂ r hr a.val).eq.symm, mul_assoc, Units.mul_inv, mul_one]

end FieldCentralizer


section Kernel

include b in
private theorem scalar_tensor_injective : Function.Injective
    (algebraMap S (ScalarClifford q S)) := by
  intro r t h
  apply scalar_injective (ExtendedForm q S b) (b.baseChange S)
  simpa only [AlgEquiv.commutes] using congrArg (cliffordEquiv q S b) h

include b in
private theorem reversion_scalar (t : S) :
    reversion q S (algebraMap S _ t) = algebraMap S _ t := by
  have hs : algebraMap S (ScalarClifford q S) t = t • (1 : ScalarClifford q S) :=
    Algebra.algebraMap_eq_smul_one t
  rw [hs, map_smul, reversion_one q S b]

private theorem vectorAction_eq_one_iff_commute (a : Spin q S b) :
    vectorAction q S b a = 1 ↔
      ∀ v, Commute (a : (ScalarClifford q S)ˣ).val (vectors q S v) := by
  let A : (ScalarClifford q S)ˣ := a
  constructor
  · intro h x
    have hx := vectorAction_characterization q S b a x
    rw [h] at hx
    change vectors q S x = A.val * vectors q S x * ↑A⁻¹ at hx
    have hm := congrArg (fun y => y * A.val) hx
    change A.val * vectors q S x = vectors q S x * A.val
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hm.symm
  · intro h
    ext x
    apply vectors_injective q S b
    change vectors q S (vectorAction q S b a x) = vectors q S x
    rw [vectorAction_characterization q S b a]
    change A.val * vectors q S x * ↑A⁻¹ = _
    rw [(h x).eq, mul_assoc, Units.mul_inv, mul_one]

private theorem vectorKernel_of_centralizer
    (h : ∀ ⦃a : ScalarClifford q S⦄, a ∈ evenPart q S →
      (∀ x, Commute a (vectors q S x)) → ∃ t : S, a = algebraMap S _ t)
    (a : Spin q S b) :
    vectorAction q S b a = 1 ↔
      ∃! t : S, t * t = 1 ∧ (a : (ScalarClifford q S)ˣ).val = algebraMap S _ t := by
  rw [vectorAction_eq_one_iff_commute]
  constructor
  · intro hc
    obtain ⟨t, ht⟩ := h a.property.1 hc
    have hn := a.property.2.1
    change reversion q S (a : (ScalarClifford q S)ˣ).val * (a : (ScalarClifford q S)ˣ).val = 1 at hn
    rw [ht, reversion_scalar q S b, ← map_mul, ← map_one (algebraMap S _)] at hn
    refine ⟨t, ⟨scalar_tensor_injective q S b hn, ht⟩, ?_⟩
    intro s hs
    exact scalar_tensor_injective q S b (hs.2.symm.trans ht)
  · rintro ⟨t, ⟨_, ht⟩, _⟩ x
    rw [ht]
    exact Algebra.commutes t _

variable [Fintype I]

/-- The spin kernel for a perfect polar pairing, over all commutative test algebras. -/
theorem vectorKernel_perfectPolar (h : Function.Surjective q.polarBilin) (a : Spin q S b) :
    vectorAction q S b a = 1 ↔
      ∃! t : S, t * t = 1 ∧ (a : (ScalarClifford q S)ˣ).val = algebraMap S _ t := by
  apply vectorKernel_of_centralizer q S b _ a
  intro x hx hc
  apply scalarCentralizer_baseChange q S b _ hx hc
  intro s hs _
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, hi, h (b.coord i)⟩

end Kernel

section RegularKernel

variable {K : Type u} [Field K] {W : Type v} [AddCommGroup W] [Module K W]
variable (Q : QuadraticForm K W) (A : Type z) [CommRing A] [Algebra K A]
variable {J : Type w} [LinearOrder J] [Fintype J] (c : Basis J K W)

/-- The regular field spin kernel on every test algebra is exactly the scalar μ₂. -/
theorem regular_vectorKernel
    (hQ : LinearMap.ker Q.polarBilin = ⊥ ∨
      ∃ r : W, Q r ≠ 0 ∧ LinearMap.ker Q.polarBilin = K ∙ r)
    (a : Spin Q A c) :
    vectorAction Q A c a = 1 ↔
      ∃! t : A, t * t = 1 ∧ (a : (ScalarClifford Q A)ˣ).val = algebraMap A _ t :=
  vectorKernel_of_centralizer Q A c (fun _ => regular_scalarCentralizer Q A c hQ) a

end RegularKernel

section ScalarKernel

/-- Scalar square roots of unity acting as units in the even Clifford algebra. -/
def scalarEmbedding : rootsOfUnity 2 S →* Spin q S b where
  toFun t := by
    let a := Units.map (algebraMap S (ScalarClifford q S)).toMonoidHom t.val
    have ht : (t.val : S) * (t.val : S) = 1 := by
      simpa only [pow_two] using (mem_rootsOfUnity' 2 t.val).mp t.property
    have hcomm (v : ScalarClifford q S) : conjugate q S a v = v := by
      change a.val * v * ↑a⁻¹ = v
      rw [show a.val = algebraMap S _ (t.val : S) from rfl,
        Algebra.commutes, ← show a.val = algebraMap S _ (t.val : S) from rfl,
        mul_assoc, Units.mul_inv, mul_one]
    have hicomm (v : ScalarClifford q S) : conjugate q S a⁻¹ v = v := by
      have h := conjugate_inverse q S a v
      rwa [hcomm] at h
    refine ⟨a, ?_, ?_, ?_, ?_⟩
    · change algebraMap S (ScalarClifford q S) (t.val : S) ∈ evenPart q S
      rw [Algebra.algebraMap_eq_smul_one]
      exact (evenPart q S).smul_mem _ (even_one q S b)
    · change reversion q S (algebraMap S _ (t.val : S)) * algebraMap S _ (t.val : S) = 1
      rw [reversion_scalar q S b, ← map_mul, ht, map_one]
    · intro x hx
      rwa [hcomm]
    · intro x hx
      rwa [hicomm]
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (algebraMap S (ScalarClifford q S)).toMonoidHom)
  map_mul' t s := by
    apply Subtype.ext
    exact map_mul (Units.map (algebraMap S (ScalarClifford q S)).toMonoidHom) t.val s.val

@[simp] theorem scalarEmbedding_val (t : rootsOfUnity 2 S) :
    ((scalarEmbedding q S b t).val : ScalarClifford q S) =
      algebraMap S _ (t.val : S) := rfl

theorem scalarEmbedding_injective : Function.Injective (scalarEmbedding q S b) := by
  intro t s h
  apply Subtype.ext
  apply Units.ext
  apply scalar_tensor_injective q S b
  have he := congrArg (fun a : Spin q S b => (a.val : ScalarClifford q S)) h
  simpa only [scalarEmbedding_val] using he

theorem scalarEmbedding_trivial_action (t : rootsOfUnity 2 S) :
    vectorAction q S b (scalarEmbedding q S b t) = 1 := by
  rw [vectorAction_eq_one_iff_commute]
  intro x
  rw [scalarEmbedding_val]
  exact Algebra.commutes _ _

private def kernelEquiv
    (h : ∀ a : Spin q S b, vectorAction q S b a = 1 ↔
      ∃! t : S, t * t = 1 ∧ a.val.val = algebraMap S _ t) :
    rootsOfUnity 2 S ≃* (vectorAction q S b).ker := by
  let g : rootsOfUnity 2 S →* (vectorAction q S b).ker :=
    (scalarEmbedding q S b).codRestrict _ (scalarEmbedding_trivial_action q S b)
  refine MulEquiv.ofBijective g ⟨?_, ?_⟩
  · intro t s hs
    exact scalarEmbedding_injective q S b (congrArg Subtype.val hs)
  · intro a
    obtain ⟨t, ⟨ht, hv⟩, _⟩ := (h a.val).mp a.property
    let ζ := rootsOfUnity.mkOfPowEq t (n := 2) (by simpa only [pow_two] using ht)
    refine ⟨ζ, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change algebraMap S _ t = a.val.val.val
    exact hv.symm

variable {S} {T : Type z'} [CommRing T] [Algebra R T]

/-- Change of test algebra for scalar square roots of unity. -/
def muTwoMap (f : S →ₐ[R] T) : rootsOfUnity 2 S →* rootsOfUnity 2 T :=
  ((Units.map f.toMonoidHom).comp (rootsOfUnity 2 S).subtype).codRestrict _
    (fun t => map_rootsOfUnity (Units.map f.toMonoidHom) 2 ⟨t.val, t.property, rfl⟩)

/-- Functoriality of the scalar μ₂ inclusion. -/
theorem scalarEmbedding_natural (f : S →ₐ[R] T) (t : rootsOfUnity 2 S) :
    map q b f (scalarEmbedding q S b t) = scalarEmbedding q T b (muTwoMap f t) := by
  apply Subtype.ext
  apply Units.ext
  change changeCoefficients q f ((scalarEmbedding q S b t).val : ScalarClifford q S) = _
  rw [scalarEmbedding_val, scalarEmbedding_val]
  simp [muTwoMap, changeCoefficients, Algebra.TensorProduct.algebraMap_apply]

/-- Change of test algebra on the kernel of the vector representation. -/
def vectorKernelMap (f : S →ₐ[R] T) :
    (vectorAction q S b).ker →* (vectorAction q T b).ker :=
  ((map q b f).comp (vectorAction q S b).ker.subtype).codRestrict _ (fun a => by
    have ha : vectorAction q S b a.val = 1 := a.property
    change vectorAction q T b (map q b f a.val) = 1
    apply LinearEquiv.toLinearMap_injective
    apply (b.baseChange T).ext
    intro i
    change vectorAction q T b (map q b f a.val) (b.baseChange T i) = b.baseChange T i
    have h := vectorAction_naturality q b f a.val (b.baseChange S i)
    rw [ha] at h
    change changeModule f (b.baseChange S i) =
      vectorAction q T b (map q b f a.val) (changeModule f (b.baseChange S i)) at h
    rw [changeModule_basis] at h
    exact h.symm)

private theorem kernelEquiv_natural (f : S →ₐ[R] T)
    (hS : ∀ a : Spin q S b, vectorAction q S b a = 1 ↔
      ∃! t : S, t * t = 1 ∧ a.val.val = algebraMap S _ t)
    (hT : ∀ a : Spin q T b, vectorAction q T b a = 1 ↔
      ∃! t : T, t * t = 1 ∧ a.val.val = algebraMap T _ t)
    (ζ : rootsOfUnity 2 S) :
    vectorKernelMap q b f (kernelEquiv q S b hS ζ) = kernelEquiv q T b hT (muTwoMap f ζ) := by
  apply Subtype.ext
  exact scalarEmbedding_natural q b f ζ

end ScalarKernel

section HyperbolicKernel

variable (d : Basis I R V) [Fintype I]

include d in
omit [LinearOrder I] in
private theorem hyperbolic_polar_surjective :
    Function.Surjective (QuadraticForm.dualProd R V).polarBilin := by
  let : Module.Finite R V := Module.Finite.of_basis d
  let : Module.Free R V := Module.Free.of_basis d
  intro l
  let F := Module.Dual R V
  let x : V := (Module.evalEquiv R V).symm (l.comp (LinearMap.inl R F V))
  let f : F := l.comp (LinearMap.inr R F V)
  refine ⟨(f, x), ?_⟩
  apply LinearMap.ext
  rintro ⟨g, y⟩
  rw [QuadraticMap.polarBilin_apply_apply]
  have hx : g x = l (g, 0) := Module.apply_evalEquiv_symm_apply R V g _
  have hf : f y = l (0, y) := rfl
  calc
    QuadraticMap.polar (QuadraticForm.dualProd R V) (f, x) (g, y) =
      f y + g x := by
        simp only [QuadraticMap.polar, QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add,
          LinearMap.add_apply, map_add]
        abel
    _ = l (g, y) := by
      rw [hx, hf, ← map_add]
      simp

/-- In the split hyperbolic model the kernel is scalar μ₂ over every test algebra. -/
def hyperbolicKernel {J : Type*} [LinearOrder J] [Fintype J]
    (c : Basis J R (Module.Dual R V × V)) :
    rootsOfUnity 2 S ≃* (vectorAction (QuadraticForm.dualProd R V) S c).ker :=
  kernelEquiv (QuadraticForm.dualProd R V) S c
    (vectorKernel_perfectPolar (QuadraticForm.dualProd R V) S c (hyperbolic_polar_surjective d))

omit [LinearOrder I] in
@[simp] theorem hyperbolicKernel_val {J : Type*} [LinearOrder J] [Fintype J]
    (c : Basis J R (Module.Dual R V × V)) (ζ : rootsOfUnity 2 S) :
    ((hyperbolicKernel S d c ζ).val.val : ScalarClifford (QuadraticForm.dualProd R V) S) =
      algebraMap S _ (ζ.val : S) := rfl


omit [LinearOrder I] in
theorem hyperbolicKernel_natural {J : Type*} [LinearOrder J] [Fintype J]
    (c : Basis J R (Module.Dual R V × V))
    {T : Type z'} [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (ζ : rootsOfUnity 2 S) :
    vectorKernelMap (QuadraticForm.dualProd R V) c f (hyperbolicKernel S d c ζ) =
      hyperbolicKernel T d c (muTwoMap f ζ) :=
  kernelEquiv_natural (QuadraticForm.dualProd R V) c f _ _ ζ

end HyperbolicKernel

section RegularKernelEquiv

variable {K : Type u} [Field K] {W : Type v} [AddCommGroup W] [Module K W]
variable (Q : QuadraticForm K W) (A : Type z) [CommRing A] [Algebra K A]
variable {J : Type w} [LinearOrder J] [Fintype J] (c : Basis J K W)

/-- The natural scalar identification of the vector kernel for regular field forms. -/
def regularKernel
    (hQ : LinearMap.ker Q.polarBilin = ⊥ ∨
      ∃ r : W, Q r ≠ 0 ∧ LinearMap.ker Q.polarBilin = K ∙ r) :
    rootsOfUnity 2 A ≃* (vectorAction Q A c).ker :=
  kernelEquiv Q A c (regular_vectorKernel Q A c hQ)

@[simp] theorem regularKernel_val
    (hQ : LinearMap.ker Q.polarBilin = ⊥ ∨
      ∃ r : W, Q r ≠ 0 ∧ LinearMap.ker Q.polarBilin = K ∙ r)
    (ζ : rootsOfUnity 2 A) :
    ((regularKernel Q A c hQ ζ).val.val : ScalarClifford Q A) =
      algebraMap A _ (ζ.val : A) := rfl


theorem regularKernel_natural
    (hQ : LinearMap.ker Q.polarBilin = ⊥ ∨
      ∃ r : W, Q r ≠ 0 ∧ LinearMap.ker Q.polarBilin = K ∙ r)
    {B : Type z'} [CommRing B] [Algebra K B] (f : A →ₐ[K] B) (ζ : rootsOfUnity 2 A) :
    vectorKernelMap Q c f (regularKernel Q A c hQ ζ) =
      regularKernel Q B c hQ (muTwoMap f ζ) :=
  kernelEquiv_natural Q c f _ _ ζ

end RegularKernelEquiv

private theorem vectorAction_unique (a : Spin q S b)
    (g : (S ⊗[R] V) ≃ₗ[S] (S ⊗[R] V)) (hg : IsVectorAction q S a.val g) :
    g = vectorAction q S b a := by
  ext x
  apply vectors_injective q S b
  exact (hg x).trans (vectorAction_characterization q S b a x).symm

theorem functorialitySpecification : SpinSpecification.FunctorialityType.{u,v,w,z,z'} := by
  intro R _ V _ _ q I _ b S _ _ T _ _ G H hG hH f
  have hG' : G = Spin q S b := SetLike.coe_injective hG
  have hH' : H = Spin q T b := SetLike.coe_injective hH
  subst G
  subst H
  refine ⟨map q b f, fun _ => rfl, ?_⟩
  intro a g h hg hh x
  rw [vectorAction_unique q S b a g hg, vectorAction_unique q T b (map q b f a) h hh]
  exact vectorAction_naturality q b f a x

theorem regularKernelSpecification : SpinSpecification.RegularKernelType.{u,v,w,z} := by
  intro K _ V _ _ I _ _ q b h S _ _ G ρ hG hρ
  have h' : G = Spin q S b := SetLike.coe_injective hG
  subst G
  have he : ρ = vectorAction q S b := MonoidHom.ext fun a =>
    vectorAction_unique q S b a _ (hρ a)
  subst ρ
  exact ⟨regularKernel q S b h, regularKernel_val q S b h⟩

theorem hyperbolicKernelSpecification :
    SpinSpecification.HyperbolicKernelType.{u,v,w,w',z} := by
  intro R _ E _ _ I _ _ d J _ _ b S _ _ q G ρ hG hρ
  have h' : G = Spin q S b := SetLike.coe_injective hG
  subst G
  have he : ρ = vectorAction q S b := MonoidHom.ext fun a =>
    vectorAction_unique q S b a _ (hρ a)
  subst ρ
  exact ⟨hyperbolicKernel S d b, hyperbolicKernel_val S d b⟩

section MuTwo

open Polynomial

variable (R)

/-- The coordinate ring of the scalar group of square roots of unity. -/
abbrev MuTwoRing := muTwoCoordinateRing R

/-- Over every test algebra, the scalar kernel functor is cut out by `X² - 1`. -/
def muTwoPoints (S : Type z) [CommRing S] [Algebra R S] :
    (MuTwoRing R →ₐ[R] S) ≃ rootsOfUnity 2 S where
  toFun f := rootsOfUnity.mkOfPowEq (f (AdjoinRoot.root (muTwoPolynomial R))) (by
    have h := AdjoinRoot.aeval_algHom_eq_zero (muTwoPolynomial R) f
    simpa only [muTwoPolynomial, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] using h)
  invFun t := AdjoinRoot.liftAlgHom (muTwoPolynomial R) (Algebra.ofId R S) (t.val : S) (by
    simpa only [muTwoPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one, sub_eq_zero] using
        (mem_rootsOfUnity' 2 t.val).mp t.property)
  left_inv f := by
    apply AdjoinRoot.algHom_ext
    rw [AdjoinRoot.liftAlgHom_root]
    rfl
  right_inv t := by
    apply rootsOfUnity.coe_injective
    exact AdjoinRoot.liftAlgHom_root (muTwoPolynomial R) (Algebra.ofId R S) (t.val : S) _

variable {R} {S} {T : Type z'} [CommRing T] [Algebra R T]

theorem muTwoPoints_natural (f : S →ₐ[R] T) (a : MuTwoRing R →ₐ[R] S) :
    ((muTwoPoints R T (f.comp a)).val : T) =
      f ((muTwoPoints R S a).val : S) := rfl

theorem muTwoRepresentation : SpinSpecification.MuTwoRepresentationType.{u,z} := by
  intro R _
  exact ⟨fun S _ _ => muTwoPoints R S, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩

end MuTwo

section Scheme

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

variable {R₀ : Type u} [CommRing R₀] {V₀ : Type u} [AddCommGroup V₀] [Module R₀ V₀]
variable (q₀ : QuadraticForm R₀ V₀) {I₀ : Type u} [LinearOrder I₀] [Fintype I₀]
variable (b₀ : Basis I₀ R₀ V₀)

private abbrev algebraPoint (S : CommAlgCat.{u} R₀) : ((CommAlgCat.{u} R₀)ᵒᵖ)ᵒᵖ :=
  op (op S)

/-- The spin point functor on commutative test algebras. -/
def pointsFunctor : ((CommAlgCat.{u} R₀)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (Spin q₀ S.unop.unop b₀)
  map f := GrpCat.ofHom (map q₀ b₀ f.unop.unop.hom)
  map_id S := by
    apply GrpCat.ext
    intro a
    change map q₀ b₀ (AlgHom.id R₀ S.unop.unop) a = a
    exact map_id q₀ b₀ a
  map_comp f g := by
    apply GrpCat.ext
    intro a
    exact map_comp q₀ b₀ f.unop.unop.hom g.unop.unop.hom a

private abbrev coordinateObject : (CommAlgCat.{u} R₀)ᵒᵖ :=
  op (CommAlgCat.of R₀ (CoordinateRing q₀ b₀))

private def algebraRepresentation :
    (pointsFunctor q₀ b₀ ⋙ forget _).RepresentableBy (coordinateObject q₀ b₀) where
  homEquiv {S} :=
    { toFun := fun f => pointEquiv q₀ b₀ S.unop f.unop.hom
      invFun := fun x => (CommAlgCat.ofHom ((pointEquiv q₀ b₀ S.unop).symm x)).op
      left_inv := by intro f; simp
      right_inv := by intro x; exact (pointEquiv q₀ b₀ S.unop).apply_symm_apply x }
  homEquiv_comp f g := by
    exact pointEquiv_natural q₀ b₀ f.unop.hom g.unop.hom

local instance coordinateGroup : GrpObj (coordinateObject q₀ b₀) :=
  GrpObj.ofRepresentableBy _ _ (algebraRepresentation q₀ b₀)

local instance spinSpecBraided : (algSpec (CommRingCat.of R₀)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

/-- The affine spin group scheme over the original commutative base ring. -/
def spinScheme : Grp (Over (Spec (CommRingCat.of R₀))) :=
  letI := coordinateGroup q₀ b₀
  ((algSpec (CommRingCat.of R₀)).mapGrp).obj (Grp.mk (coordinateObject q₀ b₀))

theorem spinScheme_affine : IsAffine (spinScheme q₀ b₀).X.left := by
  change IsAffine (Spec (CommRingCat.of (CoordinateRing q₀ b₀)))
  infer_instance

theorem spinScheme_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (spinScheme q₀ b₀).X.hom := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap R₀ (CoordinateRing q₀ b₀))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

private def specPointsMulEquiv {X : (CommAlgCat.{u} R₀)ᵒᵖ} [GrpObj X] (S : CommAlgCat.{u} R₀) :
    (op S ⟶ X) ≃* SchemePoints (((algSpec (CommRingCat.of R₀)).mapGrp).obj (Grp.mk X)) S :=
  { (algSpec.fullyFaithful (R := CommRingCat.of R₀)).homEquiv with
    map_mul' := fun f g => (algSpec (CommRingCat.of R₀)).map_mul f g }

/-- The representing equivalence agrees with the group law of the affine scheme. -/
def schemePoints (S : CommAlgCat.{u} R₀) :
    (((algSpec (CommRingCat.of R₀)).obj (op S)) ⟶ (spinScheme q₀ b₀).X) ≃*
      Spin q₀ S b₀ :=
  letI := coordinateGroup q₀ b₀
  let e := yonedaGrpObjIsoOfRepresentableBy (coordinateObject q₀ b₀) _
    (algebraRepresentation q₀ b₀)
  (specPointsMulEquiv S).symm.trans ((e.app (algebraPoint S)).groupIsoToMulEquiv)


private theorem schemePoints_onSpec {S : CommAlgCat.{u} R₀}
    (p : op S ⟶ coordinateObject q₀ b₀) :
    schemePoints q₀ b₀ S ((algSpec (CommRingCat.of R₀)).map p) =
      pointEquiv q₀ b₀ S p.unop.hom := by
  let e := specPointsMulEquiv (X := coordinateObject q₀ b₀) S
  let φ := (algebraRepresentation q₀ b₀).homEquiv (X := op S)
  change φ (e.symm (e p)) = φ p
  exact congrArg φ (e.symm_apply_apply p)

theorem schemePoints_naturality {S T : CommAlgCat.{u} R₀} (f : S ⟶ T)
    (p : (algSpec (CommRingCat.of R₀)).obj (op S) ⟶ (spinScheme q₀ b₀).X) :
    schemePoints q₀ b₀ T ((algSpec (CommRingCat.of R₀)).map f.op ≫ p) =
      map q₀ b₀ f.hom (schemePoints q₀ b₀ S p) := by
  obtain ⟨g, rfl⟩ := (specPointsMulEquiv (X := coordinateObject q₀ b₀) S).surjective p
  change schemePoints q₀ b₀ T ((algSpec (CommRingCat.of R₀)).map f.op ≫
    (algSpec (CommRingCat.of R₀)).map g) =
      map q₀ b₀ f.hom (schemePoints q₀ b₀ S ((algSpec (CommRingCat.of R₀)).map g))
  let F := algSpec (CommRingCat.of R₀)
  calc
    _ = schemePoints q₀ b₀ T (F.map (f.op ≫ g)) :=
      congrArg (schemePoints q₀ b₀ T) (F.map_comp f.op g).symm
    _ = pointEquiv q₀ b₀ T (f.hom.comp g.unop.hom) := schemePoints_onSpec q₀ b₀ _
    _ = map q₀ b₀ f.hom (pointEquiv q₀ b₀ S g.unop.hom) :=
      pointEquiv_natural q₀ b₀ f.hom g.unop.hom
    _ = _ := congrArg (map q₀ b₀ f.hom) (schemePoints_onSpec q₀ b₀ g).symm

theorem spinScheme_affineMorphism : IsAffineHom (spinScheme q₀ b₀).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R₀ (CoordinateRing q₀ b₀))))
  infer_instance

private def spinUnitPoints (S : CommAlgCat.{u} R₀) :
    SchemePoints (spinScheme q₀ b₀) S →* (ScalarClifford q₀ S)ˣ :=
  (spinSubgroup q₀ S b₀).subtype.comp (schemePoints q₀ b₀ S).toMonoidHom

private theorem spinUnitPoints_represents :
    IsSpinPointRepresentation q₀ (spinScheme q₀ b₀) (spinUnitPoints q₀ b₀) := by
  constructor
  · intro S
    refine ⟨Subtype.val_injective.comp (schemePoints q₀ b₀ S).injective, ?_⟩
    ext a
    constructor
    · rintro ⟨p, rfl⟩
      exact (schemePoints q₀ b₀ S p).property
    · intro ha
      obtain ⟨p, hp⟩ := (schemePoints q₀ b₀ S).surjective ⟨a, ha⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  · intro S T f a
    change ((schemePoints q₀ b₀ T ((algSpec (CommRingCat.of R₀)).map f.op ≫ a)).val) = _
    rw [schemePoints_naturality]
    rfl

theorem affineRepresentation : SpinSpecification.AffineRepresentationType.{u} := by
  intro R _ V _ _ I _ _ q b
  exact ⟨CommAlgCat.of R (CoordinateRing q b), inferInstance, spinScheme q b, rfl,
    spinScheme_affineMorphism q b, spinScheme_locallyOfFinitePresentation q b,
    spinUnitPoints q b, spinUnitPoints_represents q b⟩

variable (R₀) in
private def muTwoFunctor : ((CommAlgCat.{u} R₀)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (rootsOfUnity 2 S.unop.unop)
  map f := GrpCat.ofHom (muTwoMap f.unop.unop.hom)
  map_id _ := by
    apply GrpCat.ext
    intro t
    exact rootsOfUnity.coe_injective rfl
  map_comp _ _ := by
    apply GrpCat.ext
    intro t
    exact rootsOfUnity.coe_injective rfl

variable (R₀) in
private abbrev muTwoObject : (CommAlgCat.{u} R₀)ᵒᵖ :=
  op (CommAlgCat.of R₀ (MuTwoRing R₀))

variable (R₀) in
private def muTwoAlgebraRepresentation :
    (muTwoFunctor R₀ ⋙ forget _).RepresentableBy (muTwoObject R₀) where
  homEquiv {S} :=
    { toFun := fun f => muTwoPoints R₀ S.unop f.unop.hom
      invFun := fun t => (CommAlgCat.ofHom ((muTwoPoints R₀ S.unop).symm t)).op
      left_inv := by intro f; simp
      right_inv := by intro t; exact (muTwoPoints R₀ S.unop).apply_symm_apply t }
  homEquiv_comp f g :=
    rootsOfUnity.coe_injective (muTwoPoints_natural f.unop.hom g.unop.hom)

local instance muTwoCoordinateGroup (R₀ : Type u) [CommRing R₀] : GrpObj (muTwoObject R₀) :=
  GrpObj.ofRepresentableBy _ _ (muTwoAlgebraRepresentation R₀)

/-- The scheme of scalar square roots of unity with their multiplication law. -/
def muTwoScheme (R₀ : Type u) [CommRing R₀] : GroupScheme R₀ :=
  letI := muTwoCoordinateGroup R₀
  ((algSpec (CommRingCat.of R₀)).mapGrp).obj (Grp.mk (muTwoObject R₀))

/-- A point of the scalar group corresponds to its value on the root coordinate. -/
def muTwoSchemePoints (R₀ : Type u) [CommRing R₀] (S : CommAlgCat.{u} R₀) :
    SchemePoints (muTwoScheme R₀) S ≃* rootsOfUnity 2 S :=
  letI := muTwoCoordinateGroup R₀
  let e := yonedaGrpObjIsoOfRepresentableBy (muTwoObject R₀) _ (muTwoAlgebraRepresentation R₀)
  (specPointsMulEquiv S).symm.trans ((e.app (algebraPoint S)).groupIsoToMulEquiv)

private theorem muTwoSchemePoints_onSpec {S : CommAlgCat.{u} R₀} (p : op S ⟶ muTwoObject R₀) :
    muTwoSchemePoints R₀ S ((algSpec (CommRingCat.of R₀)).map p) =
      muTwoPoints R₀ S p.unop.hom := by
  let e := specPointsMulEquiv (X := muTwoObject R₀) S
  let φ := (muTwoAlgebraRepresentation R₀).homEquiv (X := op S)
  change φ (e.symm (e p)) = φ p
  exact congrArg φ (e.symm_apply_apply p)

private def scalarNaturalTransformation : muTwoFunctor R₀ ⟶ pointsFunctor q₀ b₀ where
  app S := GrpCat.ofHom (scalarEmbedding q₀ S.unop.unop b₀)
  naturality := by
    intro _ _ f
    apply GrpCat.ext
    intro t
    exact (scalarEmbedding_natural q₀ b₀ f.unop.unop.hom t).symm

private def scalarAlgebraTransformation :
    yonedaGrp.obj (Grp.mk (muTwoObject R₀)) ⟶ yonedaGrp.obj (Grp.mk (coordinateObject q₀ b₀)) :=
  (yonedaGrpObjIsoOfRepresentableBy _ _ (muTwoAlgebraRepresentation R₀)).hom ≫
    scalarNaturalTransformation q₀ b₀ ≫
      (yonedaGrpObjIsoOfRepresentableBy _ _ (algebraRepresentation q₀ b₀)).inv

private def scalarAlgebraInclusion : Grp.mk (muTwoObject R₀) ⟶ Grp.mk (coordinateObject q₀ b₀) :=
  yonedaGrpFullyFaithful.preimage (scalarAlgebraTransformation q₀ b₀)

/-- The scalar inclusion into the affine spin group. -/
def scalarSchemeInclusion : muTwoScheme R₀ ⟶ spinScheme q₀ b₀ :=
  ((algSpec (CommRingCat.of R₀)).mapGrp).map (scalarAlgebraInclusion q₀ b₀)

private theorem pointEquiv_scalarAlgebraInclusion {S : CommAlgCat.{u} R₀}
    (p : op S ⟶ muTwoObject R₀) :
    pointEquiv q₀ b₀ S (p ≫ (scalarAlgebraInclusion q₀ b₀).hom.hom).unop.hom =
      scalarEmbedding q₀ S b₀ (muTwoPoints R₀ S p.unop.hom) := by
  let e := ((yonedaGrpObjIsoOfRepresentableBy _ _ (algebraRepresentation q₀ b₀)).app
    (algebraPoint S)).groupIsoToMulEquiv
  have h := congrArg (fun α => (α.app (algebraPoint S)).hom p)
    (yonedaGrpFullyFaithful.map_preimage (scalarAlgebraTransformation q₀ b₀))
  change p ≫ (scalarAlgebraInclusion q₀ b₀).hom.hom =
    e.symm (scalarEmbedding q₀ S b₀ (muTwoPoints R₀ S p.unop.hom)) at h
  exact (congrArg e h).trans (e.apply_symm_apply _)

theorem scalarSchemeInclusion_points {S : CommAlgCat.{u} R₀}
    (p : SchemePoints (muTwoScheme R₀) S) :
    schemePoints q₀ b₀ S (p ≫ (scalarSchemeInclusion q₀ b₀).hom.hom) =
      scalarEmbedding q₀ S b₀ (muTwoSchemePoints R₀ S p) := by
  obtain ⟨g, rfl⟩ := (specPointsMulEquiv (X := muTwoObject R₀) S).surjective p
  let F := algSpec (CommRingCat.of R₀)
  change schemePoints q₀ b₀ S (F.map g ≫ F.map (scalarAlgebraInclusion q₀ b₀).hom.hom) =
    scalarEmbedding q₀ S b₀ (muTwoSchemePoints R₀ S (F.map g))
  rw [muTwoSchemePoints_onSpec]
  let i := (scalarAlgebraInclusion q₀ b₀).hom.hom
  calc
    _ = schemePoints q₀ b₀ S (F.map (g ≫ i)) :=
      congrArg (schemePoints q₀ b₀ S) (F.map_comp g i).symm
    _ = pointEquiv q₀ b₀ S (g ≫ i).unop.hom := schemePoints_onSpec q₀ b₀ _
    _ = _ := pointEquiv_scalarAlgebraInclusion q₀ b₀ g

private def scalarAlgebraMap : CoordinateRing q₀ b₀ →ₐ[R₀] MuTwoRing R₀ :=
  (scalarAlgebraInclusion q₀ b₀).hom.hom.unop.hom

private theorem scalarAlgebraMap_root :
    scalarAlgebraMap q₀ b₀ (variableClass q₀ b₀ ⟨∅, rfl⟩) =
      AdjoinRoot.root (muTwoPolynomial R₀) := by
  let S := (muTwoObject R₀).unop
  let c := (extendedBasis q₀ S b₀).coord ∅
  have h := pointEquiv_scalarAlgebraInclusion q₀ b₀ (𝟙 (muTwoObject R₀))
  rw [Category.id_comp] at h
  have hc := congrArg (fun a : Spin q₀ S b₀ => c a.val.val) h
  change c (pointFromHom q₀ b₀ S (scalarAlgebraMap q₀ b₀)).val.val =
    c (algebraMap S _ (AdjoinRoot.root (muTwoPolynomial R₀))) at hc
  have h1 : c 1 = 1 := by
    have he : extendedBasis q₀ S b₀ ∅ = 1 := by
      rw [Basis.baseChange_apply, orderedBasis_empty, Algebra.TensorProduct.one_def]
    rw [← he, show c = (extendedBasis q₀ S b₀).coord ∅ from rfl,
      Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  rw [pointFromHom_val, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_eq_mul, mul_one] at hc
  simpa only [c, evenElement_coord, dite_eq_left (show ((∅ : Finset I₀).card : ZMod 2) = 0
    from rfl), Function.comp_apply] using hc

theorem scalarSchemeInclusion_isClosedImmersion :
    IsClosedImmersion (scalarSchemeInclusion q₀ b₀).hom.hom.left := by
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom (scalarAlgebraMap q₀ b₀).toRingHom))
  apply IsClosedImmersion.spec_of_surjective
  intro t
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective t
  refine ⟨Polynomial.aeval (variableClass q₀ b₀ ⟨∅, rfl⟩) p, ?_⟩
  change scalarAlgebraMap q₀ b₀ _ = _
  rw [← Polynomial.aeval_algHom_apply, scalarAlgebraMap_root, AdjoinRoot.aeval_eq]

private theorem hasScalarSchemeKernel
    (e : ∀ S : CommAlgCat.{u} R₀, rootsOfUnity 2 S ≃* (vectorAction q₀ S b₀).ker)
    (he : ∀ (S : CommAlgCat.{u} R₀) (t : rootsOfUnity 2 S),
      (e S t).val = scalarEmbedding q₀ S b₀ t) :
    HasScalarSchemeKernel q₀ := by
  let i := scalarSchemeInclusion q₀ b₀
  have hscalar (S : CommAlgCat.{u} R₀) (t : SchemePoints (muTwoScheme R₀) S) :
      (spinUnitPoints q₀ b₀ S (t ≫ i.hom.hom)).val =
        algebraMap S _ (muTwoSchemePoints R₀ S t).val.val :=
    congrArg (fun a : Spin q₀ S b₀ => a.val.val) (scalarSchemeInclusion_points q₀ b₀ t)
  refine ⟨spinScheme q₀ b₀, muTwoScheme R₀, i, spinUnitPoints q₀ b₀,
    muTwoSchemePoints R₀, spinUnitPoints_represents q₀ b₀,
    scalarSchemeInclusion_isClosedImmersion q₀ b₀, ?_, hscalar, ?_, ?_⟩
  · refine ⟨rfl, fun S a => ?_⟩
    let p := (CommAlgCat.ofHom a).op
    let f := (algSpec (CommRingCat.of R₀)).map p
    let rootValue (t : SchemePoints (muTwoScheme R₀) S) := (muTwoSchemePoints R₀ S t).val.val
    change rootValue (f ≫ 𝟙 (muTwoUnderlying R₀)) = _
    calc
      _ = rootValue f := congrArg rootValue (Category.comp_id f)
      _ = _ := congrArg (fun t : rootsOfUnity 2 S => t.val.val) (muTwoSchemePoints_onSpec p)
  · intro S t p
    show (t ≫ i.hom.hom) * p = p * (t ≫ i.hom.hom)
    apply ((spinUnitPoints_represents q₀ b₀).1 S).1
    rw [map_mul, map_mul]
    apply Units.ext
    simp only [Units.val_mul, hscalar S t]
    exact Algebra.commutes _ _
  · intro S p
    let v := schemePoints q₀ b₀ S
    let m := muTwoSchemePoints R₀ S
    change (∀ x, Commute (v p).val.val (vectors q₀ S x)) ↔
      ∃! t, t ≫ i.hom.hom = p
    rw [← vectorAction_eq_one_iff_commute]
    constructor
    · intro hp
      let x : (vectorAction q₀ S b₀).ker := ⟨v p, hp⟩
      let t := m.symm ((e S).symm x)
      have ht : t ≫ i.hom.hom = p := v.injective (by
        rw [scalarSchemeInclusion_points]
        change scalarEmbedding q₀ S b₀ (m (m.symm ((e S).symm x))) = x.val
        rw [m.apply_symm_apply, ← he, (e S).apply_symm_apply])
      refine ⟨t, ht, fun s hs => m.injective (scalarEmbedding_injective q₀ S b₀ ?_)⟩
      rw [← scalarSchemeInclusion_points q₀ b₀ s, ← scalarSchemeInclusion_points q₀ b₀ t, hs, ht]
    · rintro ⟨t, ht, _⟩
      rw [← ht, scalarSchemeInclusion_points]
      exact scalarEmbedding_trivial_action q₀ S b₀ (m t)

theorem regularSchemeKernelSpecification : SpinSpecification.RegularSchemeKernelType.{u} := by
  intro K _ V _ _ I _ _ q b h
  exact hasScalarSchemeKernel q b (fun S => regularKernel q S b h) (fun _ _ => rfl)

theorem hyperbolicSchemeKernelSpecification : SpinSpecification.HyperbolicSchemeKernelType.{u} := by
  intro R _ E _ _ I J _ _ _ _ d b
  exact hasScalarSchemeKernel (QuadraticForm.dualProd R E) b
    (fun S => hyperbolicKernel S d b) (fun _ _ => rfl)

private abbrev SpinSchemePoints (S : CommAlgCat.{u} R₀) :=
  (algSpec (CommRingCat.of R₀)).obj (op S) ⟶ (spinScheme q₀ b₀).X

/-- A point lies in the scheme-theoretic kernel when its vector action is the identity. -/
abbrev VectorKernelPoints (S : CommAlgCat.{u} R₀) :=
  {p : SpinSchemePoints q₀ b₀ S // vectorAction q₀ S b₀ (schemePoints q₀ b₀ S p) = 1}

private def kernelSchemePoints (S : CommAlgCat.{u} R₀)
    (e : rootsOfUnity 2 S ≃* (vectorAction q₀ S b₀).ker) :
    (MuTwoRing R₀ →ₐ[R₀] S) ≃ VectorKernelPoints q₀ b₀ S :=
  ((muTwoPoints R₀ S).trans e.toEquiv).trans
    ((schemePoints q₀ b₀ S).toEquiv.subtypeEquivOfSubtype
      (p := fun a => vectorAction q₀ S b₀ a = 1)).symm

private theorem kernelSchemePoints_natural {S T : CommAlgCat.{u} R₀} (f : S ⟶ T)
    (eS : rootsOfUnity 2 S ≃* (vectorAction q₀ S b₀).ker)
    (eT : rootsOfUnity 2 T ≃* (vectorAction q₀ T b₀).ker)
    (he : ∀ ζ, vectorKernelMap q₀ b₀ f.hom (eS ζ) = eT (muTwoMap f.hom ζ))
    (a : MuTwoRing R₀ →ₐ[R₀] S) :
    (kernelSchemePoints q₀ b₀ T eT (f.hom.comp a)).val =
      (algSpec (CommRingCat.of R₀)).map f.op ≫ (kernelSchemePoints q₀ b₀ S eS a).val := by
  apply (schemePoints q₀ b₀ T).injective
  rw [schemePoints_naturality]
  have h (U : CommAlgCat.{u} R₀) (e : rootsOfUnity 2 U ≃* (vectorAction q₀ U b₀).ker)
      (p : MuTwoRing R₀ →ₐ[R₀] U) :
      schemePoints q₀ b₀ U (kernelSchemePoints q₀ b₀ U e p).val =
        (e (muTwoPoints R₀ U p)).val :=
    (schemePoints q₀ b₀ U).apply_symm_apply _
  rw [h, h]
  have hn : muTwoPoints R₀ T (f.hom.comp a) = muTwoMap f.hom (muTwoPoints R₀ S a) :=
    rootsOfUnity.coe_injective (muTwoPoints_natural f.hom a)
  rw [hn]
  exact congrArg Subtype.val (he (muTwoPoints R₀ S a)).symm

/-- The kernel on the split hyperbolic spin scheme is represented by `R[X]/(X²-1)`. -/
def hyperbolicKernelSchemePoints (d : Basis I₀ R₀ V₀)
    {J : Type u} [LinearOrder J] [Fintype J] (b : Basis J R₀ (Module.Dual R₀ V₀ × V₀))
    (S : CommAlgCat.{u} R₀) :
    (MuTwoRing R₀ →ₐ[R₀] S) ≃ VectorKernelPoints (QuadraticForm.dualProd R₀ V₀) b S :=
  kernelSchemePoints (QuadraticForm.dualProd R₀ V₀) b S (hyperbolicKernel S d b)

omit [LinearOrder I₀] in
theorem hyperbolicKernelSchemePoints_natural (d : Basis I₀ R₀ V₀)
    {J : Type u} [LinearOrder J] [Fintype J] (b : Basis J R₀ (Module.Dual R₀ V₀ × V₀))
    {S T : CommAlgCat.{u} R₀} (f : S ⟶ T) (a : MuTwoRing R₀ →ₐ[R₀] S) :
    (hyperbolicKernelSchemePoints d b T (f.hom.comp a)).val =
      (algSpec (CommRingCat.of R₀)).map f.op ≫ (hyperbolicKernelSchemePoints d b S a).val :=
  kernelSchemePoints_natural (QuadraticForm.dualProd R₀ V₀) b f _ _
    (hyperbolicKernel_natural S d b f.hom) a

section FieldSchemeKernel

variable {K : Type u} [Field K] {W : Type u} [AddCommGroup W] [Module K W]
variable (Q : QuadraticForm K W) {J : Type u} [LinearOrder J] [Fintype J]
variable (c : Basis J K W)
variable (hQ : LinearMap.ker Q.polarBilin = ⊥ ∨
  ∃ r : W, Q r ≠ 0 ∧ LinearMap.ker Q.polarBilin = K ∙ r)

/-- The kernel on the regular field spin scheme is represented by `K[X]/(X²-1)`. -/
def regularKernelSchemePoints (S : CommAlgCat.{u} K) :
    (MuTwoRing K →ₐ[K] S) ≃ VectorKernelPoints Q c S :=
  kernelSchemePoints Q c S (regularKernel Q S c hQ)

theorem regularKernelSchemePoints_natural {S T : CommAlgCat.{u} K} (f : S ⟶ T)
    (a : MuTwoRing K →ₐ[K] S) :
    (regularKernelSchemePoints Q c hQ T (f.hom.comp a)).val =
      (algSpec (CommRingCat.of K)).map f.op ≫ (regularKernelSchemePoints Q c hQ S a).val :=
  kernelSchemePoints_natural Q c f _ _ (regularKernel_natural Q S c hQ f.hom) a

end FieldSchemeKernel

end Scheme

end

end LinearAlgebraicGroups.Albert.SpinFunctor
