import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Cone
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.TensorDecomposition
import Mathlib.LinearAlgebra.TensorProduct.Prod

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
universe u v w
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]

@[simp] theorem scalarCone_d (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R) (n : ℕ) :
    (scalarCone C y).d (n+1) n = ModuleCat.ofHom (scalarConeDifferential C y n) := by
  dsimp only [scalarCone]
  exact ChainComplex.of_d _ _ n

/-- The boundary out of degree one includes the scalar term with a positive sign. -/
@[simp] theorem scalarCone_d_one (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R)
    (a : C.X 1) (b : C.X 0) :
    ((scalarCone C y).d 1 0).hom (a,b) = (C.d 1 0).hom a + y • b := by
  rw [scalarCone_d]
  rfl

/-- The higher boundaries have precisely the source's two signs. -/
@[simp] theorem scalarCone_d_succ (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R)
    (n : ℕ) (a : C.X (n+2)) (b : C.X (n+1)) :
    ((scalarCone C y).d (n+2) (n+1)).hom (a,b) =
      ((C.d (n+2) (n+1)).hom a + y • b, -(C.d (n+1) n).hom b) := by
  rw [scalarCone_d]
  rfl

/-- Scalar cones are functorial in the complex, with diagonal component maps. -/
def scalarConeMap {C D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D) (y : R) :
    scalarCone C y ⟶ scalarCone D y :=
  ChainComplex.ofHom
    (fun n => match n with
      | 0 => φ.f 0
      | n+1 => ModuleCat.ofHom ((φ.f (n+1)).hom.prodMap (φ.f n).hom))
    (fun n => by
      rw [scalarCone_d, scalarCone_d]
      have hc (k : ℕ) (a : C.X (k+1)) :
          (D.d (k+1) k).hom ((φ.f (k+1)).hom a) =
            (φ.f k).hom ((C.d (k+1) k).hom a) :=
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.comm (k+1) k)) a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      cases n with
      | zero =>
        rintro ⟨a,b⟩
        change (D.d 1 0).hom ((φ.f 1).hom a) + y • (φ.f 0).hom b =
          (φ.f 0).hom ((C.d 1 0).hom a + y • b)
        simp [hc]
      | succ n =>
        rintro ⟨a,b⟩
        change ((D.d (n+2) (n+1)).hom ((φ.f (n+2)).hom a) +
          y • (φ.f (n+1)).hom b, -(D.d (n+1) n).hom ((φ.f (n+1)).hom b)) =
          ((φ.f (n+1)).hom ((C.d (n+2) (n+1)).hom a + y • b),
            (φ.f n).hom (-(C.d (n+1) n).hom b))
        simp [hc])

@[reassoc] theorem scalarConeInclusion_natural
    {C D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D) (y : R) :
    scalarConeInclusion C y ≫ scalarConeMap φ y = φ ≫ scalarConeInclusion D y := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => simp [scalarConeInclusion, scalarConeMap]
  | succ n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change ((φ.f (n+1)).hom a, (φ.f n).hom 0) = ((φ.f (n+1)).hom a, 0)
    simp

section ExteriorSplitting
variable {E : Type v} [AddCommGroup E] [Module R E]

/-- Projection onto the old exterior algebra, followed by its inclusion. -/
def oldExteriorProjection : ExteriorAlgebra R (E × R) →ₐ[R] ExteriorAlgebra R (E × R) :=
  (ExteriorAlgebra.map (LinearMap.inl R E R)).comp
    (ExteriorAlgebra.map (LinearMap.fst R E R))

/-- The new generator used in the left-wedge cone coordinates. -/
def lastExteriorGenerator : ExteriorAlgebra R (E × R) := ExteriorAlgebra.ι R (0,1)

@[simp] theorem oldExteriorProjection_last :
    oldExteriorProjection (lastExteriorGenerator (R := R) (E := E)) = 0 := by
  simp [oldExteriorProjection, lastExteriorGenerator]

@[simp] theorem oldExteriorProjection_generator (z : E × R) :
    oldExteriorProjection (ExteriorAlgebra.ι R z) = ExteriorAlgebra.ι R (z.1,0) := by
  simp [oldExteriorProjection]

/-- Splitting a generator into its old part and its last scalar coordinate. -/
theorem exterior_generator_split (z : E × R) :
    ExteriorAlgebra.ι R z = ExteriorAlgebra.ι R (z.1,0) +
      z.2 • lastExteriorGenerator (R := R) (E := E) := by
  rw [lastExteriorGenerator, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- Explicit exterior-algebra splitting. Its second coordinate is contraction
by the last-coordinate form, followed by projection onto the old algebra. -/
theorem exterior_last_split (a : ExteriorAlgebra R (E × R)) :
    a = oldExteriorProjection a + lastExteriorGenerator *
      oldExteriorProjection (contraction (LinearMap.snd R E R) a) := by
  let P := oldExteriorProjection (R := R) (E := E)
  let e := lastExteriorGenerator (R := R) (E := E)
  change a = P a + e * P (contraction (LinearMap.snd R E R) a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp [P, oldExteriorProjection]
  | add a b ha hb =>
    simp only [map_add, mul_add]
    calc
      a + b = (P a + e * P (contraction (LinearMap.snd R E R) a)) +
          (P b + e * P (contraction (LinearMap.snd R E R) b)) := congrArg₂ (· + ·) ha hb
      _ = _ := by abel
  | ι_mul a z ha =>
    have hee : e * e = 0 := ExteriorAlgebra.ι_sq_zero _
    have hswap : ExteriorAlgebra.ι R (z.1,0) * e =
        -(e * ExteriorAlgebra.ι R (z.1,0)) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    rw [contraction_generator_mul]
    simp only [LinearMap.snd_apply, map_sub, map_smul, map_mul,
      show P (ExteriorAlgebra.ι R z) = ExteriorAlgebra.ι R (z.1,0) from
        oldExteriorProjection_generator z]
    rw [exterior_generator_split z]
    conv_lhs => rw [ha]
    simp only [add_mul, mul_add, smul_mul_assoc]
    rw [← mul_assoc e e, hee, zero_mul, smul_zero, add_zero,
      ← mul_assoc (ExteriorAlgebra.ι R (z.1,0)) e, hswap, neg_mul]
    rw [mul_sub, mul_smul_comm, mul_assoc]
    abel

/-- The same splitting formula for any specified old/new coordinate decomposition. -/
theorem exterior_retraction_split {A : Type w} [AddCommGroup A] [Module R A]
    (i : E →ₗ[R] A) (p : A →ₗ[R] E) (ℓ : A →ₗ[R] R) (e : A)
    (hsplit : ∀ z, i (p z) + ℓ z • e = z) (a : ExteriorAlgebra R A) :
    a = (ExteriorAlgebra.map i) (ExteriorAlgebra.map p a) + ExteriorAlgebra.ι R e *
      (ExteriorAlgebra.map i) (ExteriorAlgebra.map p (contraction ℓ a)) := by
  let P := (ExteriorAlgebra.map i).comp (ExteriorAlgebra.map p)
  let t := ExteriorAlgebra.ι R e
  change a = P a + t * P (contraction ℓ a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp [P]
  | add a b ha hb =>
    simp only [map_add, mul_add]
    calc
      a + b = (P a + t * P (contraction ℓ a)) +
          (P b + t * P (contraction ℓ b)) := congrArg₂ (· + ·) ha hb
      _ = _ := by abel
  | ι_mul a z ha =>
    have htt : t * t = 0 := ExteriorAlgebra.ι_sq_zero _
    have hswap : ExteriorAlgebra.ι R (i (p z)) * t =
        -(t * ExteriorAlgebra.ι R (i (p z))) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have hz : ExteriorAlgebra.ι R z = ExteriorAlgebra.ι R (i (p z)) + ℓ z • t := by
      rw [← map_smul, ← map_add, hsplit]
    have hP : P (ExteriorAlgebra.ι R z) = ExteriorAlgebra.ι R (i (p z)) := by simp [P]
    rw [contraction_generator_mul]
    simp only [map_sub, map_smul, map_mul, hP]
    rw [hz]
    conv_lhs => rw [ha]
    simp only [add_mul, mul_add, smul_mul_assoc]
    rw [← mul_assoc t t, htt, zero_mul, smul_zero, add_zero,
      ← mul_assoc (ExteriorAlgebra.ι R (i (p z))) t, hswap, neg_mul]
    rw [mul_sub, mul_smul_comm, mul_assoc]
    abel

@[simp] theorem contraction_zero (a : ExteriorAlgebra R E) :
    contraction (0 : E →ₗ[R] R) a = 0 := by
  simp [contraction]

end ExteriorSplitting

/-- Restriction of a vector to its original positions. -/
def appendOldProjection (x : List R) (y : R) :
    (Fin (x ++ [y]).length → R) →ₗ[R] (Fin x.length → R) where
  toFun a i := a ⟨i.val, by simpa using Nat.lt_succ_of_lt i.isLt⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation at the appended position. -/
def appendLastForm (x : List R) (y : R) : (Fin (x ++ [y]).length → R) →ₗ[R] R :=
  LinearMap.proj ⟨x.length, by simp⟩

@[simp] theorem appendOldProjection_old (x : List R) (y : R) (a : Fin x.length → R) :
    appendOldProjection x y (appendOldLinear x y a) = a := by
  ext j
  simp [appendOldProjection, appendOldLinear, j.isLt]

@[simp] theorem appendLastForm_old (x : List R) (y : R) (a : Fin x.length → R) :
    appendLastForm x y (appendOldLinear x y a) = 0 := by
  simp [appendLastForm, appendOldLinear]

@[simp] theorem appendLastForm_last (x : List R) (y : R) :
    appendLastForm x y (appendLastVector x y) = 1 := by
  simp [appendLastForm, appendLastVector]

@[simp] theorem appendOldProjection_last (x : List R) (y : R) :
    appendOldProjection x y (appendLastVector x y) = 0 := by
  classical
  ext j
  have h : (⟨j.val, by simpa using Nat.lt_succ_of_lt j.isLt⟩ : Fin (x ++ [y]).length) ≠
      ⟨x.length, by simp⟩ := by
    intro h
    have := congrArg Fin.val h
    exact Nat.ne_of_lt j.isLt this
  simp [appendOldProjection, appendLastVector, Pi.single_apply, h, Ne.symm h]

theorem append_vector_split (x : List R) (y : R) (a : Fin (x ++ [y]).length → R) :
    appendOldLinear x y (appendOldProjection x y a) +
      appendLastForm x y a • appendLastVector x y = a := by
  classical
  ext j
  by_cases h : j.val < x.length
  · have hj : j ≠ (⟨x.length, by simp⟩ : Fin (x ++ [y]).length) := by
      intro hj
      have : j.val = x.length := congrArg Fin.val hj
      omega
    simp [appendOldLinear, appendOldProjection, appendLastVector, Pi.single_apply,
      h, hj, Ne.symm hj]
  · have hj : j = (⟨x.length, by simp⟩ : Fin (x ++ [y]).length) := by
      apply Fin.ext
      have := j.isLt
      simp only [List.length_append, List.length_singleton] at this
      dsimp
      omega
    subst j
    simp [appendOldLinear, appendLastVector, appendLastForm]

@[simp] theorem append_exterior_project_old (x : List R) (y : R)
    (a : ExteriorAlgebra R (Fin x.length → R)) :
    ExteriorAlgebra.map (appendOldProjection x y) (ExteriorAlgebra.map (appendOldLinear x y) a) = a := by
  have h : (appendOldProjection x y).comp (appendOldLinear x y) = LinearMap.id := by
    apply LinearMap.ext
    intro a
    exact appendOldProjection_old x y a
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id]
  rfl

@[simp] theorem append_exterior_contract_old (x : List R) (y : R)
    (a : ExteriorAlgebra R (Fin x.length → R)) :
    contraction (appendLastForm x y) (ExteriorAlgebra.map (appendOldLinear x y) a) = 0 := by
  rw [contraction_map (0 : (Fin x.length → R) →ₗ[R] R)
    (appendLastForm x y) (appendOldLinear x y) (by ext; simp), contraction_zero, map_zero]

/-- The exterior-power join before tensoring by the coefficient module. -/
def appendPowerJoin (x : List R) (y : R) (n : ℕ) :
    ((⋀[R]^(n+1) (Fin x.length → R)) × (⋀[R]^n (Fin x.length → R))) →ₗ[R]
      (⋀[R]^(n+1) (Fin (x ++ [y]).length → R)) :=
  (exteriorPower.map (n+1) (appendOldLinear x y)).comp (LinearMap.fst R _ _) +
    (appendWedgeLinear x y n).comp (LinearMap.snd R _ _)

/-- Explicit inverse: old-coordinate restriction and last-coordinate contraction. -/
def appendPowerSplit (x : List R) (y : R) (n : ℕ) :
    (⋀[R]^(n+1) (Fin (x ++ [y]).length → R)) →ₗ[R]
      ((⋀[R]^(n+1) (Fin x.length → R)) × (⋀[R]^n (Fin x.length → R))) :=
  (exteriorPower.map (n+1) (appendOldProjection x y)).prod
    ((exteriorPower.map n (appendOldProjection x y)).comp
      (differential (appendLastForm x y) n))

@[simp] theorem appendPowerJoin_coe (x : List R) (y : R) (n : ℕ)
    (a : ⋀[R]^(n+1) (Fin x.length → R)) (b : ⋀[R]^n (Fin x.length → R)) :
    (appendPowerJoin x y n (a,b) : ExteriorAlgebra R (Fin (x ++ [y]).length → R)) =
      ExteriorAlgebra.map (appendOldLinear x y) a +
        ExteriorAlgebra.ι R (appendLastVector x y) * ExteriorAlgebra.map (appendOldLinear x y) b := by
  simp only [appendPowerJoin, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.coe_add, exteriorPower.coe_map]
  rfl

theorem appendPowerJoin_split (x : List R) (y : R) (n : ℕ)
    (a : ⋀[R]^(n+1) (Fin (x ++ [y]).length → R)) :
    appendPowerJoin x y n (appendPowerSplit x y n a) = a := by
  apply Subtype.ext
  simp only [appendPowerSplit, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply]
  rw [appendPowerJoin_coe]
  try simp only [exteriorPower.coe_map, differential_coe]
  exact (exterior_retraction_split (appendOldLinear x y) (appendOldProjection x y)
    (appendLastForm x y) (appendLastVector x y) (append_vector_split x y) a).symm

theorem appendPowerSplit_join (x : List R) (y : R) (n : ℕ)
    (a : ⋀[R]^(n+1) (Fin x.length → R)) (b : ⋀[R]^n (Fin x.length → R)) :
    appendPowerSplit x y n (appendPowerJoin x y n (a,b)) = (a,b) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [appendPowerSplit, LinearMap.prod_apply, Function.prod, exteriorPower.coe_map]
    rw [appendPowerJoin_coe]
    simp
  · apply Subtype.ext
    simp only [appendPowerSplit, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply,
      exteriorPower.coe_map, differential_coe]
    rw [appendPowerJoin_coe, map_add, contraction_generator_mul]
    simp

/-- The splitting is valid over all commutative rings, including characteristic two. -/
def appendPowerEquiv (x : List R) (y : R) (n : ℕ) :
    ((⋀[R]^(n+1) (Fin x.length → R)) × (⋀[R]^n (Fin x.length → R))) ≃ₗ[R]
      (⋀[R]^(n+1) (Fin (x ++ [y]).length → R)) :=
  LinearEquiv.ofLinearMap (appendPowerJoin x y n) (appendPowerSplit x y n)
    (by apply LinearMap.ext; intro a; exact appendPowerJoin_split x y n a)
    (by apply LinearMap.ext; rintro ⟨a,b⟩; exact appendPowerSplit_join x y n a b)

@[simp] theorem appendOldLinear_basis (x : List R) (y : R) (j : Fin x.length) :
    appendOldLinear x y (Pi.basisFun R (Fin x.length) j) =
      Pi.basisFun R (Fin (x ++ [y]).length)
        ⟨j.val, by simpa using Nat.lt_succ_of_lt j.isLt⟩ := by
  classical
  ext k
  simp only [appendOldLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_apply,
    Pi.single_apply]
  by_cases hk : k.val < x.length
  · rw [dite_eq_left hk]
    by_cases he : k.val = j.val
    · have h₁ : (⟨k.val,hk⟩ : Fin x.length) = j := Fin.ext he
      have h₂ : k = (⟨j.val, by simpa using Nat.lt_succ_of_lt j.isLt⟩ :
          Fin (x ++ [y]).length) := Fin.ext he
      simp [h₁, h₂]
    · have h₁ : (⟨k.val,hk⟩ : Fin x.length) ≠ j := fun h => he (congrArg Fin.val h)
      have h₂ : k ≠ (⟨j.val, by simpa using Nat.lt_succ_of_lt j.isLt⟩ :
          Fin (x ++ [y]).length) := fun h => he (congrArg Fin.val h)
      simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂]
  · rw [dite_eq_right hk]
    have h₂ : k ≠ (⟨j.val, by simpa using Nat.lt_succ_of_lt j.isLt⟩ :
          Fin (x ++ [y]).length) := by
      intro h
      have : k.val = j.val := congrArg Fin.val h
      omega
    simp [h₂, Ne.symm h₂]

@[simp] theorem appendForm_last (x : List R) (y : R) :
    listForm (x ++ [y]) (appendLastVector x y) = y := by
  have h : appendLastVector x y = Pi.basisFun R (Fin (x ++ [y]).length)
      ⟨x.length, by simp⟩ := by
    classical
    exact (Pi.basisFun_apply _ _ _).symm
  rw [h, listForm_basis]
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (by omega)]
  simp

/-- The old-coordinate inclusion preserves the original linear form. -/
theorem appendForm_comp_old (x : List R) (y : R) :
    (listForm (x ++ [y])).comp (appendOldLinear x y) = listForm x := by
  apply (Pi.basisFun R (Fin x.length)).ext
  intro j
  simp only [LinearMap.comp_apply, appendOldLinear_basis, listForm_basis]
  simp [List.get_eq_getElem]

/-- The degree-zero comparison is the canonical identification of scalar powers. -/
def appendPowerZeroEquiv (x : List R) (y : R) :
    (⋀[R]^0 (Fin x.length → R)) ≃ₗ[R] (⋀[R]^0 (Fin (x ++ [y]).length → R)) :=
  (exteriorPower.zeroEquiv R _).trans (exteriorPower.zeroEquiv R _).symm

@[simp] theorem appendPowerZeroEquiv_apply (x : List R) (y : R)
    (a : ⋀[R]^0 (Fin x.length → R)) :
    appendPowerZeroEquiv x y a = exteriorPower.map 0 (appendOldLinear x y) a := by
  apply (exteriorPower.zeroEquiv R (Fin (x ++ [y]).length → R)).injective
  simp only [appendPowerZeroEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality (appendOldLinear x y)) a).symm

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Tensoring the explicit exterior decomposition preserves its invertibility
for every coefficient module, with no flatness assumption. -/
def appendCoefficientEquiv (x : List R) (y : R) :
    ∀ n, (scalarCone (coefficientComplex M x) y).X n ≃ₗ[R]
      (coefficientComplex M (x ++ [y])).X n
  | 0 => TensorProduct.congr (appendPowerZeroEquiv x y) (LinearEquiv.refl R M)
  | n+1 =>
      (TensorProduct.prodLeft R R (⋀[R]^(n+1) (Fin x.length → R))
        (⋀[R]^n (Fin x.length → R)) M).symm.trans
        (TensorProduct.congr (appendPowerEquiv x y n) (LinearEquiv.refl R M))

theorem appendCoefficientEquiv_component (x : List R) (y : R) (n : ℕ) :
    (appendCoefficientEquiv M x y n).toLinearMap = appendComparisonComponent M x y n := by
  cases n with
  | zero =>
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro m
    change appendPowerZeroEquiv x y a ⊗ₜ[R] m =
      exteriorPower.map 0 (appendOldLinear x y) a ⊗ₜ[R] m
    rw [appendPowerZeroEquiv_apply]
  | succ n =>
    apply LinearMap.prod_ext
    · apply TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro m
      change appendCoefficientEquiv M x y (n+1) (a ⊗ₜ[R] m,0) = _
      have he : appendPowerEquiv x y n (a,0) =
          exteriorPower.map (n+1) (appendOldLinear x y) a := by
        change appendPowerJoin x y n (a,0) = _
        simp [appendPowerJoin]
      change (TensorProduct.congr (appendPowerEquiv x y n) (LinearEquiv.refl R M))
        ((TensorProduct.prodLeft R R _ _ M).symm (a ⊗ₜ[R] m,0)) =
        appendCoefficientOld M x y (n+1) (a ⊗ₜ[R] m) + appendCoefficientWedge M x y n 0
      rw [show (0 : (⋀[R]^n (Fin x.length → R)) ⊗[R] M) = (0 ⊗ₜ[R] m) from by simp,
        TensorProduct.prodLeft_symm_tmul, TensorProduct.congr_tmul, he]
      simp only [LinearEquiv.refl_apply, TensorProduct.zero_tmul, map_zero, add_zero]
      rfl
    · apply TensorProduct.ext
      apply LinearMap.ext
      intro b
      apply LinearMap.ext
      intro m
      change appendCoefficientEquiv M x y (n+1) (0,b ⊗ₜ[R] m) = _
      have he : appendPowerEquiv x y n (0,b) = appendWedgeLinear x y n b := by
        change appendPowerJoin x y n (0,b) = _
        simp [appendPowerJoin]
      change (TensorProduct.congr (appendPowerEquiv x y n) (LinearEquiv.refl R M))
        ((TensorProduct.prodLeft R R _ _ M).symm (0,b ⊗ₜ[R] m)) =
        appendCoefficientOld M x y (n+1) 0 + appendCoefficientWedge M x y n (b ⊗ₜ[R] m)
      rw [show (0 : (⋀[R]^(n+1) (Fin x.length → R)) ⊗[R] M) = (0 ⊗ₜ[R] m) from by simp,
        TensorProduct.prodLeft_symm_tmul, TensorProduct.congr_tmul, he]
      simp only [LinearEquiv.refl_apply, TensorProduct.zero_tmul, map_zero, zero_add]
      rfl

@[simp] theorem append_differential_old (x : List R) (y : R) (n : ℕ)
    (a : ⋀[R]^(n+1) (Fin x.length → R)) :
    differential (listForm (x ++ [y])) n (exteriorPower.map (n+1) (appendOldLinear x y) a) =
      exteriorPower.map n (appendOldLinear x y) (differential (listForm x) n a) := by
  apply Subtype.ext
  simp only [differential_coe, exteriorPower.coe_map]
  exact contraction_map (listForm x) (listForm (x ++ [y])) (appendOldLinear x y)
    (appendForm_comp_old x y) a

@[simp] theorem append_differential_wedge_zero (x : List R) (y : R)
    (b : ⋀[R]^0 (Fin x.length → R)) :
    differential (listForm (x ++ [y])) 0 (appendWedgeLinear x y 0 b) =
      y • exteriorPower.map 0 (appendOldLinear x y) b := by
  apply Subtype.ext
  change contraction (listForm (x ++ [y]))
    (ExteriorAlgebra.ι R (appendLastVector x y) * ExteriorAlgebra.map (appendOldLinear x y) b) = _
  rw [contraction_generator_mul, appendForm_last,
    contraction_map (listForm x) (listForm (x ++ [y])) (appendOldLinear x y)
      (appendForm_comp_old x y), contraction_degree_zero]
  simp [exteriorPower.coe_map]

@[simp] theorem append_differential_wedge_succ (x : List R) (y : R) (n : ℕ)
    (b : ⋀[R]^(n+1) (Fin x.length → R)) :
    differential (listForm (x ++ [y])) (n+1) (appendWedgeLinear x y (n+1) b) =
      y • exteriorPower.map (n+1) (appendOldLinear x y) b -
        appendWedgeLinear x y n (differential (listForm x) n b) := by
  apply Subtype.ext
  change contraction (listForm (x ++ [y]))
    (ExteriorAlgebra.ι R (appendLastVector x y) * ExteriorAlgebra.map (appendOldLinear x y) b) = _
  rw [contraction_generator_mul, appendForm_last,
    contraction_map (listForm x) (listForm (x ++ [y])) (appendOldLinear x y)
      (appendForm_comp_old x y)]
  simp only [SetLike.val_smul, exteriorPower.coe_map, Submodule.coe_sub]
  rfl

@[simp] theorem coefficientComplex_d (x : List R) (n : ℕ) :
    (coefficientComplex M x).d (n+1) n = ModuleCat.ofHom (coefficientDifferential M x n) := by
  dsimp only [coefficientComplex]
  exact ChainComplex.of_d _ _ n

@[simp] theorem append_coefficient_d_old (x : List R) (y : R) (n : ℕ)
    (a : (coefficientComplex M x).X (n+1)) :
    coefficientDifferential M (x ++ [y]) n (appendCoefficientOld M x y (n+1) a) =
      appendCoefficientOld M x y n (coefficientDifferential M x n a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change differential (listForm (x ++ [y])) n
      (exteriorPower.map (n+1) (appendOldLinear x y) a) ⊗ₜ[R] m =
        exteriorPower.map n (appendOldLinear x y) (differential (listForm x) n a) ⊗ₜ[R] m
    rw [append_differential_old]
  | add a b ha hb => simp [ha, hb]

@[simp] theorem append_coefficient_d_wedge_zero (x : List R) (y : R)
    (b : (coefficientComplex M x).X 0) :
    coefficientDifferential M (x ++ [y]) 0 (appendCoefficientWedge M x y 0 b) =
      y • appendCoefficientOld M x y 0 b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    change differential (listForm (x ++ [y])) 0 (appendWedgeLinear x y 0 b) ⊗ₜ[R] m =
      y • (exteriorPower.map 0 (appendOldLinear x y) b ⊗ₜ[R] m)
    rw [append_differential_wedge_zero, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb, smul_add]

@[simp] theorem append_coefficient_d_wedge_succ (x : List R) (y : R) (n : ℕ)
    (b : (coefficientComplex M x).X (n+1)) :
    coefficientDifferential M (x ++ [y]) (n+1) (appendCoefficientWedge M x y (n+1) b) =
      y • appendCoefficientOld M x y (n+1) b -
        appendCoefficientWedge M x y n (coefficientDifferential M x n b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    change differential (listForm (x ++ [y])) (n+1) (appendWedgeLinear x y (n+1) b) ⊗ₜ[R] m =
      y • (exteriorPower.map (n+1) (appendOldLinear x y) b ⊗ₜ[R] m) -
        appendWedgeLinear x y n (differential (listForm x) n b) ⊗ₜ[R] m
    rw [append_differential_wedge_succ, TensorProduct.sub_tmul, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb, smul_add]; abel

/-- The explicit coordinate isomorphisms commute with the cone differential. -/
theorem appendComparisonComponent_comm (x : List R) (y : R) (n : ℕ) :
    ModuleCat.ofHom (appendComparisonComponent M x y (n+1)) ≫
        (coefficientComplex M (x ++ [y])).d (n+1) n =
      (scalarCone (coefficientComplex M x) y).d (n+1) n ≫
        ModuleCat.ofHom (appendComparisonComponent M x y n) := by
  rw [scalarCone_d, coefficientComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a,b⟩
  cases n with
  | zero =>
    change coefficientDifferential M (x ++ [y]) 0
      (appendCoefficientOld M x y 1 a + appendCoefficientWedge M x y 0 b) =
      appendCoefficientOld M x y 0 (((coefficientComplex M x).d 1 0).hom a + y • b)
    rw [coefficientComplex_d]
    simp
    rfl
  | succ n =>
    change coefficientDifferential M (x ++ [y]) (n+1)
      (appendCoefficientOld M x y (n+2) a + appendCoefficientWedge M x y (n+1) b) =
      appendCoefficientOld M x y (n+1)
        (((coefficientComplex M x).d (n+2) (n+1)).hom a + y • b) +
      appendCoefficientWedge M x y n (-((coefficientComplex M x).d (n+1) n).hom b)
    rw [coefficientComplex_d, coefficientComplex_d]
    simp [sub_eq_add_neg, add_assoc]
    rfl

/-- RK-05: K(x,y;M) is the scalar mapping cone with coordinates a+e∧b. -/
def koszulAppendConeIso (x : List R) (y : R) :
    scalarCone (coefficientComplex M x) y ≅ coefficientComplex M (x ++ [y]) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (appendCoefficientEquiv M x y n).toModuleIso)
    (fun i j hij => by
      have hi : j+1=i := hij
      subst i
      change ModuleCat.ofHom ((appendCoefficientEquiv M x y (j+1)).toLinearMap) ≫ _ =
        _ ≫ ModuleCat.ofHom ((appendCoefficientEquiv M x y j).toLinearMap)
      rw [appendCoefficientEquiv_component, appendCoefficientEquiv_component]
      exact appendComparisonComponent_comm M x y j)

theorem append_cone_comparison : Specs.AdvCommAlg.Koszul.appendConeComparison.{u,v} := by
  intro R _ M _ _ x y
  refine ⟨koszulAppendConeIso M x y, ?_⟩
  intro n
  exact congrArg ModuleCat.ofHom (appendCoefficientEquiv_component M x y n)

section HomologyRepresentatives
variable (C : ChainComplex (ModuleCat.{v} R) ℕ)

@[simp] theorem natChainNext (n : ℕ) : (ComplexShape.down ℕ).next n = n-1 := by
  cases n with
  | zero =>
    apply ComplexShape.next_eq_self'
    intro k h
    change k+1=0 at h
    omega
  | succ n => exact ComplexShape.next_eq' _ rfl

@[simp] theorem natChainPrev (n : ℕ) : (ComplexShape.down ℕ).prev n = n+1 :=
  ComplexShape.prev_eq' _ rfl

@[simp] theorem chain_d_zero : C.d 0 0 = 0 := C.shape 0 0 (by simp)

/-- Kernel-to-cycles lift using the specified next index. -/
def chainCycleLift (n : ℕ) : (LinearMap.ker (C.d n (n-1)).hom) →ₗ[R] C.cycles n :=
  (C.liftCycles (ModuleCat.ofHom (LinearMap.ker (C.d n (n-1)).hom).subtype)
    (n-1) (natChainNext n) (by ext a; exact a.property)).hom

/-- A concrete cycle, as an element of the canonical cycle module. -/
def chainCycleMk (n : ℕ) (a : C.X n) (ha : (C.d n (n-1)).hom a = 0) : C.cycles n :=
  chainCycleLift C n ⟨a,ha⟩

@[simp] theorem chainCycleMk_i (n : ℕ) (a : C.X n) (ha) :
    (C.iCycles n).hom (chainCycleMk C n a ha) = a := by
  exact congrArg (fun f => f.hom ⟨a,ha⟩)
    (C.liftCycles_i (ModuleCat.ofHom (LinearMap.ker (C.d n (n-1)).hom).subtype)
      (n-1) (natChainNext n) _)

@[simp] theorem chain_toCycles_i (i j : ℕ) (a : C.X i) :
    (C.iCycles j).hom ((C.toCycles i j).hom a) = (C.d i j).hom a :=
  congrArg (fun f => f.hom a) (C.toCycles_i i j)

/-- The class of an actual cycle in the canonical homology module. -/
def chainClass (n : ℕ) (a : C.X n) (ha : (C.d n (n-1)).hom a = 0) : C.homology n :=
  (C.homologyπ n).hom (chainCycleMk C n a ha)

/-- A cycle has zero class exactly when it is an actual boundary. -/
theorem chainClass_eq_zero_iff (n : ℕ) (a : C.X n) (ha) :
    chainClass C n a ha = 0 ↔ ∃ b : C.X (n+1), (C.d (n+1) n).hom b = a := by
  let S := ShortComplex.mk (C.toCycles (n+1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n+1) n)
  have he : S.Exact := S.exact_of_g_is_cokernel
    (C.homologyIsCokernel (n+1) n (natChainPrev n))
  constructor
  · intro h
    obtain ⟨b,hb⟩ := (S.moduleCat_exact_iff.mp he) (chainCycleMk C n a ha) h
    refine ⟨b, ?_⟩
    have := congrArg (C.iCycles n).hom hb
    simpa only [S, chain_toCycles_i, chainCycleMk_i] using this
  · rintro ⟨b,hb⟩
    have hc : (C.toCycles (n+1) n).hom b = chainCycleMk C n a ha := by
      apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
      simpa only [chain_toCycles_i, chainCycleMk_i] using hb
    change (C.homologyπ n).hom (chainCycleMk C n a ha) = 0
    rw [← hc]
    exact congrArg (fun f => f.hom b) (C.toCycles_comp_homologyπ (n+1) n)

/-- Every class has a cycle representative. -/
theorem chainClass_surjective (n : ℕ) (h : C.homology n) :
    ∃ (a : C.X n) (ha : (C.d n (n-1)).hom a = 0), chainClass C n a ha = h := by
  obtain ⟨c,rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance h
  refine ⟨(C.iCycles n).hom c, ?_, ?_⟩
  · exact congrArg (fun f => f.hom c) (C.iCycles_d n (n-1))
  · unfold chainClass
    congr 1
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    exact chainCycleMk_i C n _ _

theorem chainClass_add (n : ℕ) (a b : C.X n) (ha hb) :
    chainClass C n (a+b) (by simp [ha,hb]) = chainClass C n a ha + chainClass C n b hb := by
  unfold chainClass
  have hc : chainCycleMk C n (a+b) (by simp [ha,hb]) =
      chainCycleMk C n a ha + chainCycleMk C n b hb := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    simp
  exact (congrArg (C.homologyπ n).hom hc).trans (map_add _ _ _)

theorem chainClass_smul (n : ℕ) (r : R) (a : C.X n) (ha) :
    chainClass C n (r • a) (by simp [ha]) = r • chainClass C n a ha := by
  unfold chainClass
  have hc : chainCycleMk C n (r • a) (by simp [ha]) = r • chainCycleMk C n a ha := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    simp
  exact (congrArg (C.homologyπ n).hom hc).trans (map_smul _ _ _)

theorem chainClass_sub (n : ℕ) (a b : C.X n) (ha hb) :
    chainClass C n (a-b) (by simp [ha,hb]) = chainClass C n a ha - chainClass C n b hb := by
  unfold chainClass
  have hc : chainCycleMk C n (a-b) (by simp [ha,hb]) =
      chainCycleMk C n a ha - chainCycleMk C n b hb := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    simp
  exact (congrArg (C.homologyπ n).hom hc).trans (map_sub _ _ _)

@[simp] theorem chainClass_zero (n : ℕ) (ha : (C.d n (n-1)).hom 0 = 0) :
    chainClass C n 0 ha = 0 := by
  have hc : chainCycleMk C n 0 ha = 0 := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    simp
  unfold chainClass
  rw [hc, map_zero]

/-- Equality of classes can be checked by a single boundary equation. -/
theorem chainClass_eq_iff (n : ℕ) (a b : C.X n) (ha hb) :
    chainClass C n a ha = chainClass C n b hb ↔
      ∃ c : C.X (n+1), (C.d (n+1) n).hom c = a-b := by
  rw [← sub_eq_zero, ← chainClass_sub, chainClass_eq_zero_iff]

/-- Cycle classes commute with maps of the original complexes. -/
theorem chainClass_map {D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D)
    (n : ℕ) (a : C.X n) (ha) (hb : (D.d n (n-1)).hom ((φ.f n).hom a) = 0) :
    (HomologicalComplex.homologyMap φ n).hom (chainClass C n a ha) =
      chainClass D n ((φ.f n).hom a) hb := by
  have h := congrArg (fun f => f.hom (chainCycleMk C n a ha))
    (HomologicalComplex.homologyπ_naturality φ n)
  refine h.trans ?_
  apply congrArg (D.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
  have hi := congrArg (fun f => f.hom (chainCycleMk C n a ha))
    (HomologicalComplex.cyclesMap_i φ n)
  change (D.iCycles n).hom ((HomologicalComplex.cyclesMap φ n).hom (chainCycleMk C n a ha)) =
    (φ.f n).hom ((C.iCycles n).hom (chainCycleMk C n a ha)) at hi
  rw [chainCycleMk_i] at hi
  change (D.iCycles n).hom ((HomologicalComplex.cyclesMap φ n).hom (chainCycleMk C n a ha)) =
    (D.iCycles n).hom (chainCycleMk D n ((φ.f n).hom a) hb)
  rw [chainCycleMk_i]
  exact hi

end HomologyRepresentatives

section ConeHomology
variable (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R)

/-- Projection of a cone cycle onto its second coordinate is a cycle of C. -/
def scalarConeCycleProjection (n : ℕ) :
    (scalarCone C y).cycles (n+1) ⟶ C.cycles n :=
  C.liftCycles ((scalarCone C y).iCycles (n+1) ≫ ModuleCat.ofHom (LinearMap.snd R _ _))
    (n-1) (natChainNext n) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      cases n with
      | zero => simp [chain_d_zero]
      | succ n =>
        have h := congrArg (fun f => f.hom c) ((scalarCone C y).iCycles_d (n+2) (n+1))
        rw [scalarCone_d] at h
        have hs := congrArg Prod.snd h
        change -(C.d (n+1) n).hom (((scalarCone C y).iCycles (n+2)).hom c).2 = 0 at hs
        exact neg_eq_zero.mp hs)

@[reassoc (attr := simp)] theorem scalarConeCycleProjection_i (n : ℕ) :
    scalarConeCycleProjection C y n ≫ C.iCycles n =
      (scalarCone C y).iCycles (n+1) ≫ ModuleCat.ofHom (LinearMap.snd R _ _) := by
  apply HomologicalComplex.liftCycles_i

/-- On boundaries the cycle projection is the negative of a boundary of C. -/
theorem scalarCone_toCycles_projection (n : ℕ) :
    (scalarCone C y).toCycles (n+2) (n+1) ≫ scalarConeCycleProjection C y n =
      ModuleCat.ofHom (-LinearMap.snd R (C.X (n+2)) (C.X (n+1))) ≫ C.toCycles (n+1) n := by
  rw [← cancel_mono (C.iCycles n)]
  simp only [Category.assoc, scalarConeCycleProjection_i,
    HomologicalComplex.toCycles_i, HomologicalComplex.toCycles_i_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a,b⟩
  change (((scalarCone C y).d (n+2) (n+1)).hom (a,b)).2 = (C.d (n+1) n).hom (-b)
  rw [scalarCone_d_succ]
  simp

/-- The cone projection on homology is induced by (a,b) ↦ b, with positive sign. -/
def scalarConeHomologyProjection (n : ℕ) : (scalarCone C y).homology (n+1) ⟶ C.homology n :=
  ((scalarCone C y).homologyIsCokernel (n+2) (n+1) (natChainPrev (n+1))).desc
    (CategoryTheory.Limits.CokernelCofork.ofπ (scalarConeCycleProjection C y n ≫ C.homologyπ n)
      (by rw [← Category.assoc, scalarCone_toCycles_projection, Category.assoc,
        HomologicalComplex.toCycles_comp_homologyπ, comp_zero]))

@[reassoc (attr := simp)] theorem scalarConeHomologyProjection_class (n : ℕ) :
    (scalarCone C y).homologyπ (n+1) ≫ scalarConeHomologyProjection C y n =
      scalarConeCycleProjection C y n ≫ C.homologyπ n := by
  unfold scalarConeHomologyProjection
  exact CategoryTheory.Limits.Cofork.IsColimit.π_desc
    ((scalarCone C y).homologyIsCokernel (n+2) (n+1) (natChainPrev (n+1)))

/-- Projection of a cycle class is exactly the class of the second coordinate. -/
theorem scalarConeHomologyProjection_chainClass (n : ℕ)
    (a : C.X (n+1)) (b : C.X n)
    (hz : ((scalarCone C y).d (n+1) ((n+1)-1)).hom (a,b) = 0)
    (hb : (C.d n (n-1)).hom b = 0) :
    (scalarConeHomologyProjection C y n).hom (chainClass (scalarCone C y) (n+1) (a,b) hz) =
      chainClass C n b hb := by
  have h := congrArg (fun f => f.hom (chainCycleMk (scalarCone C y) (n+1) (a,b) hz))
    (scalarConeHomologyProjection_class C y n)
  change _ = (C.homologyπ n).hom _ at h
  refine h.trans ?_
  apply congrArg (C.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  rw [chainCycleMk_i]
  have hi := congrArg (fun f => f.hom (chainCycleMk (scalarCone C y) (n+1) (a,b) hz))
    (scalarConeCycleProjection_i C y n)
  change (C.iCycles n).hom ((scalarConeCycleProjection C y n).hom
    (chainCycleMk (scalarCone C y) (n+1) (a,b) hz)) =
    (((scalarCone C y).iCycles (n+1)).hom (chainCycleMk (scalarCone C y) (n+1) (a,b) hz)).2 at hi
  rw [chainCycleMk_i] at hi
  exact hi

/-- The two equations defining a cone cycle, also valid at its degree-one boundary. -/
theorem scalarCone_cycle_iff (n : ℕ) (a : C.X (n+1)) (b : C.X n) :
    ((scalarCone C y).d (n+1) n).hom (a,b) = 0 ↔
      (C.d (n+1) n).hom a + y • b = 0 ∧ (C.d n (n-1)).hom b = 0 := by
  cases n with
  | zero =>
    rw [scalarCone_d_one]
    simp
  | succ n =>
    rw [scalarCone_d_succ]
    change (_, -_) = (0,0) ↔ _
    simp only [Prod.mk.injEq, neg_eq_zero]
    rfl

/-- The inclusion on homology preserves the evident cycle representatives. -/
theorem scalarConeInclusion_class_zero (a : C.X 0) (ha) :
    (HomologicalComplex.homologyMap (scalarConeInclusion C y) 0).hom (chainClass C 0 a ha) =
      chainClass (scalarCone C y) 0 a (by simp) := by
  exact chainClass_map C (scalarConeInclusion C y) 0 a ha _

theorem scalarConeInclusion_class_succ (n : ℕ) (a : C.X (n+1)) (ha) :
    (HomologicalComplex.homologyMap (scalarConeInclusion C y) (n+1)).hom
        (chainClass C (n+1) a ha) =
      chainClass (scalarCone C y) (n+1) (a,0) (by
        change ((scalarCone C y).d (n+1) n).hom (a,0) = 0
        apply (scalarCone_cycle_iff C y n a 0).mpr
        constructor
        · simpa only [smul_zero, add_zero] using (show (C.d (n+1) n).hom a = 0 from ha)
        · simp) := by
  exact chainClass_map C (scalarConeInclusion C y) (n+1) a ha _

/-- Boundary equations for a class coming from C, with the missing negative degree handled. -/
theorem scalarCone_boundary_inclusion_iff (n : ℕ) (a : C.X n) :
    (∃ z : (scalarCone C y).X (n+1), ((scalarCone C y).d (n+1) n).hom z =
      ((scalarConeInclusion C y).f n).hom a) ↔
    ∃ (u : C.X (n+1)) (b : C.X n),
      (C.d n (n-1)).hom b = 0 ∧ (C.d (n+1) n).hom u + y • b = a := by
  cases n with
  | zero =>
    simp only [scalarCone_d]
    change (∃ z : C.X 1 × C.X 0, (C.d 1 0).hom z.1 + y • z.2 = a) ↔ _
    simp [Prod.exists]
  | succ n =>
    simp only [scalarCone_d]
    change (∃ z : C.X (n+2) × C.X (n+1),
      ((C.d (n+2) (n+1)).hom z.1 + y • z.2, -(C.d (n+1) n).hom z.2) = (a,0)) ↔ _
    simp only [Prod.exists, Prod.mk.injEq, neg_eq_zero]
    constructor <;> rintro ⟨u,b,h₁,h₂⟩ <;> exact ⟨u,b,h₂,h₁⟩

/-- Exactness at the second copy of Hₙ(C) in the cone sequence. -/
theorem scalarCone_exact_multiply_inclusion (n : ℕ) :
    Function.Exact (homologyScalar C y n).hom
      (HomologicalComplex.homologyMap (scalarConeInclusion C y) n).hom := by
  intro h
  obtain ⟨a,ha,rfl⟩ := chainClass_surjective C n h
  have hi : ((scalarCone C y).d n (n-1)).hom (((scalarConeInclusion C y).f n).hom a) = 0 := by
    have hc := congrArg (fun f => f.hom a) ((scalarConeInclusion C y).comm n (n-1))
    change ((scalarCone C y).d n (n-1)).hom (((scalarConeInclusion C y).f n).hom a) =
      ((scalarConeInclusion C y).f (n-1)).hom ((C.d n (n-1)).hom a) at hc
    rw [ha, map_zero] at hc
    exact hc
  rw [chainClass_map C (scalarConeInclusion C y) n a ha hi, chainClass_eq_zero_iff,
    scalarCone_boundary_inclusion_iff]
  constructor
  · rintro ⟨u,b,hb,hu⟩
    refine ⟨chainClass C n b hb, ?_⟩
    change y • chainClass C n b hb = chainClass C n a ha
    rw [← chainClass_smul]
    apply (chainClass_eq_iff C n _ _ _ _).mpr
    refine ⟨-u, ?_⟩
    rw [map_neg, ← hu]
    abel
  · rintro ⟨h,hh⟩
    obtain ⟨b,hb,rfl⟩ := chainClass_surjective C n h
    change y • chainClass C n b hb = chainClass C n a ha at hh
    rw [← chainClass_smul] at hh
    obtain ⟨u,hu⟩ := (chainClass_eq_iff C n _ _ _ _).mp hh
    refine ⟨-u,b,hb,?_⟩
    rw [map_neg, hu]
    abel

end ConeHomology

section ConeHomology
variable (C : ChainComplex (ModuleCat.{v} R) ℕ) (y : R)

/-- Exactness at the homology of the scalar cone. -/
theorem scalarCone_exact_inclusion_projection (n : ℕ) :
    Function.Exact
      (HomologicalComplex.homologyMap (scalarConeInclusion C y) (n+1)).hom
      (scalarConeHomologyProjection C y n).hom := by
  intro h
  obtain ⟨⟨a,b⟩,hz,rfl⟩ := chainClass_surjective (scalarCone C y) (n+1) h
  have he := (scalarCone_cycle_iff C y n a b).mp hz
  rw [scalarConeHomologyProjection_chainClass C y n a b hz he.2,
    chainClass_eq_zero_iff]
  constructor
  · rintro ⟨c,hc⟩
    have hu : (C.d (n+1) ((n+1)-1)).hom (a + y • c) = 0 := by
      change (C.d (n+1) n).hom (a + y • c) = 0
      simpa only [map_add, map_smul, hc] using he.1
    refine ⟨chainClass C (n+1) (a+y • c) hu, ?_⟩
    rw [scalarConeInclusion_class_succ]
    apply (chainClass_eq_iff (scalarCone C y) (n+1) _ _ _ _).mpr
    refine ⟨(0,c), ?_⟩
    change ((scalarCone C y).d (n+2) (n+1)).hom (0,c) = (a+y • c,0)-(a,b)
    rw [scalarCone_d_succ]
    apply Prod.ext
    · change (C.d (n+2) (n+1)).hom 0 + y • c = (a+y • c)-a
      simp only [map_zero, zero_add]
      abel
    · change -(C.d (n+1) n).hom c = 0-b
      simp [hc]
  · rintro ⟨h,hh⟩
    obtain ⟨c,hc,rfl⟩ := chainClass_surjective C (n+1) h
    have hp := congrArg (scalarConeHomologyProjection C y n).hom hh
    rw [scalarConeInclusion_class_succ,
      scalarConeHomologyProjection_chainClass C y n c 0 _ (by simp),
      scalarConeHomologyProjection_chainClass C y n a b hz he.2,
      chainClass_zero] at hp
    exact (chainClass_eq_zero_iff C n b he.2).mp hp.symm

/-- Exactness at the copy of Hₙ(C) reached by cone projection. -/
theorem scalarCone_exact_projection_multiply (n : ℕ) :
    Function.Exact (scalarConeHomologyProjection C y n).hom (homologyScalar C y n).hom := by
  intro h
  obtain ⟨b,hb,rfl⟩ := chainClass_surjective C n h
  change y • chainClass C n b hb = 0 ↔ _
  rw [← chainClass_smul, chainClass_eq_zero_iff]
  constructor
  · rintro ⟨a,ha⟩
    have hz : ((scalarCone C y).d (n+1) ((n+1)-1)).hom (-a,b) = 0 := by
      change ((scalarCone C y).d (n+1) n).hom (-a,b) = 0
      apply (scalarCone_cycle_iff C y n (-a) b).mpr
      exact ⟨by simp only [map_neg, ha, neg_add_cancel], hb⟩
    refine ⟨chainClass (scalarCone C y) (n+1) (-a,b) hz, ?_⟩
    exact scalarConeHomologyProjection_chainClass C y n (-a) b hz hb
  · rintro ⟨h,hh⟩
    obtain ⟨⟨a,c⟩,hz,rfl⟩ := chainClass_surjective (scalarCone C y) (n+1) h
    have he := (scalarCone_cycle_iff C y n a c).mp hz
    rw [scalarConeHomologyProjection_chainClass C y n a c hz he.2] at hh
    have hc : y • chainClass C n c he.2 = 0 := by
      rw [← chainClass_smul, chainClass_eq_zero_iff]
      refine ⟨-a, ?_⟩
      rw [map_neg]
      rw [eq_neg_of_add_eq_zero_left he.1, neg_neg]
    have hzero : chainClass C n (y • b) (by simp [hb]) = 0 := by
      rw [chainClass_smul C n y b hb, ← hh]
      exact hc
    exact (chainClass_eq_zero_iff C n _ _).mp hzero

/-- The inclusion induces a surjection on zeroth homology. -/
theorem scalarCone_inclusion_surjective_zero :
    Function.Surjective (HomologicalComplex.homologyMap (scalarConeInclusion C y) 0).hom := by
  intro h
  obtain ⟨a,ha,rfl⟩ := chainClass_surjective (scalarCone C y) 0 h
  refine ⟨chainClass C 0 a (by simp), ?_⟩
  exact scalarConeInclusion_class_zero C y a _
end ConeHomology

end AdvCommAlg.Koszul

namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]

@[reassoc] theorem scalarConeCycleProjection_natural
    {C D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D) (y : R) (n : ℕ) :
    HomologicalComplex.cyclesMap (scalarConeMap φ y) (n+1) ≫
        scalarConeCycleProjection D y n =
      scalarConeCycleProjection C y n ≫ HomologicalComplex.cyclesMap φ n := by
  rw [← cancel_mono (D.iCycles n)]
  simp only [Category.assoc, scalarConeCycleProjection_i, scalarConeCycleProjection_i_assoc,
    HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

@[reassoc] theorem scalarConeHomologyProjection_natural
    {C D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D) (y : R) (n : ℕ) :
    HomologicalComplex.homologyMap (scalarConeMap φ y) (n+1) ≫
        scalarConeHomologyProjection D y n =
      scalarConeHomologyProjection C y n ≫ HomologicalComplex.homologyMap φ n := by
  rw [← cancel_epi ((scalarCone C y).homologyπ (n+1))]
  simp only [HomologicalComplex.homologyπ_naturality_assoc,
    scalarConeHomologyProjection_class, scalarConeHomologyProjection_class_assoc,
    HomologicalComplex.homologyπ_naturality,
    scalarConeCycleProjection_natural_assoc]

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The sequence's cycle map is forced by its specified second coordinate. -/
theorem appendSequence_cycleProjection (x : List R) (y : R)
    (S : AppendConeSequence M x y) (n : ℕ) :
    S.cycleProjection n = scalarConeCycleProjection (coefficientComplex M x) y n := by
  rw [← cancel_mono ((coefficientComplex M x).iCycles n)]
  rw [S.cycleProjection_i, scalarConeCycleProjection_i]

/-- The specified cycle formula uniquely fixes the map on homology. -/
@[reassoc] theorem appendSequence_projection (x : List R) (y : R)
    (S : AppendConeSequence M x y) (n : ℕ) :
    HomologicalComplex.homologyMap S.comparison.hom (n+1) ≫ S.projection n =
      scalarConeHomologyProjection (coefficientComplex M x) y n := by
  rw [← cancel_epi ((scalarCone (coefficientComplex M x) y).homologyπ (n+1))]
  rw [S.projection_class, scalarConeHomologyProjection_class,
    appendSequence_cycleProjection]

end AdvCommAlg.Koszul

namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem appendConeComparison_natural (x : List R) (y : R) (φ : M →ₗ[R] N)
    (eM : scalarCone (coefficientComplex M x) y ≅ coefficientComplex M (x ++ [y]))
    (eN : scalarCone (coefficientComplex N x) y ≅ coefficientComplex N (x ++ [y]))
    (hM : IsAppendConeComparison M x y eM) (hN : IsAppendConeComparison N x y eN) :
    scalarConeMap (appendCoefficientMap M x φ) y ≫ eN.hom =
      eM.hom ≫ appendCoefficientMap M (x ++ [y]) φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, hM n, hN n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  cases n with
  | zero =>
    intro a
    change appendCoefficientOld N x y 0 ((TensorProduct.map LinearMap.id φ) a) =
      TensorProduct.map LinearMap.id φ (appendCoefficientOld M x y 0 a)
    change ((TensorProduct.map (exteriorPower.map 0 (appendOldLinear x y)) LinearMap.id).comp
      (TensorProduct.map LinearMap.id φ)) a =
      ((TensorProduct.map LinearMap.id φ).comp
        (TensorProduct.map (exteriorPower.map 0 (appendOldLinear x y)) LinearMap.id)) a
    congr 1
    apply TensorProduct.ext
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro m
    rfl
  | succ n =>
    rintro ⟨a,b⟩
    change appendCoefficientOld N x y (n+1) ((TensorProduct.map LinearMap.id φ) a) +
      appendCoefficientWedge N x y n ((TensorProduct.map LinearMap.id φ) b) =
      TensorProduct.map LinearMap.id φ
        (appendCoefficientOld M x y (n+1) a + appendCoefficientWedge M x y n b)
    rw [map_add]
    congr 1
    · change ((TensorProduct.map (exteriorPower.map (n+1) (appendOldLinear x y)) LinearMap.id).comp
        (TensorProduct.map LinearMap.id φ)) a =
        ((TensorProduct.map LinearMap.id φ).comp
          (TensorProduct.map (exteriorPower.map (n+1) (appendOldLinear x y)) LinearMap.id)) a
      congr 1
      apply TensorProduct.ext
      apply LinearMap.ext
      intro z
      apply LinearMap.ext
      intro m
      rfl
    · change ((TensorProduct.map (appendWedgeLinear x y n) LinearMap.id).comp
        (TensorProduct.map LinearMap.id φ)) b =
        ((TensorProduct.map LinearMap.id φ).comp
          (TensorProduct.map (appendWedgeLinear x y n) LinearMap.id)) b
      congr 1
      apply TensorProduct.ext
      apply LinearMap.ext
      intro z
      apply LinearMap.ext
      intro m
      rfl

@[reassoc] theorem appendInclusion_natural (x : List R) (y : R) (φ : M →ₗ[R] N)
    (eM : scalarCone (coefficientComplex M x) y ≅ coefficientComplex M (x ++ [y]))
    (eN : scalarCone (coefficientComplex N x) y ≅ coefficientComplex N (x ++ [y]))
    (hM : IsAppendConeComparison M x y eM) (hN : IsAppendConeComparison N x y eN) :
    appendCoefficientMap M x φ ≫ appendInclusion N x y eN =
      appendInclusion M x y eM ≫ appendCoefficientMap M (x ++ [y]) φ := by
  unfold appendInclusion
  rw [← Category.assoc, ← scalarConeInclusion_natural, Category.assoc,
    appendConeComparison_natural M N x y φ eM eN hM hN, ← Category.assoc]


end AdvCommAlg.Koszul

namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The complete appended Koszul homology sequence in the prescribed coordinates. -/
def koszulAppendConeSequence (x : List R) (y : R) : AppendConeSequence M x y where
  comparison := koszulAppendConeIso M x y
  canonical n := congrArg ModuleCat.ofHom (appendCoefficientEquiv_component M x y n)
  projection n := HomologicalComplex.homologyMap (koszulAppendConeIso M x y).inv (n+1) ≫
    scalarConeHomologyProjection (coefficientComplex M x) y n
  cycleProjection n := scalarConeCycleProjection (coefficientComplex M x) y n
  cycleProjection_i n := scalarConeCycleProjection_i (coefficientComplex M x) y n
  projection_class n := by
    simp only [← HomologicalComplex.homologyMap_comp_assoc, Iso.hom_inv_id,
      HomologicalComplex.homologyMap_id, Category.id_comp, scalarConeHomologyProjection_class]
  exact_multiply_inclusion n := by
    let he := (HomologicalComplex.homologyMapIso (koszulAppendConeIso M x y) n).toLinearEquiv
    have hi : Function.Injective he := he.injective
    simpa only [appendInclusion, HomologicalComplex.homologyMap_comp,
      ModuleCat.hom_comp, LinearMap.coe_comp, he, ← LinearEquiv.coe_coe, CategoryTheory.Iso.toLinearMap_toLinearEquiv,
      HomologicalComplex.homologyMapIso_hom] using
      (scalarCone_exact_multiply_inclusion (coefficientComplex M x) y n).comp_injective
        he hi (map_zero he)
  exact_inclusion_projection n := by
    have h := (LinearEquiv.conj_exact_iff_exact
      (HomologicalComplex.homologyMap (scalarConeInclusion (coefficientComplex M x) y) (n+1)).hom
      (scalarConeHomologyProjection (coefficientComplex M x) y n).hom
      (HomologicalComplex.homologyMapIso (koszulAppendConeIso M x y) (n+1)).toLinearEquiv).mpr
        (scalarCone_exact_inclusion_projection (coefficientComplex M x) y n)
    simpa only [homology, appendInclusion, HomologicalComplex.homologyMap_comp,
      ModuleCat.hom_comp, CategoryTheory.Iso.toLinearMap_toLinearEquiv,
      CategoryTheory.Iso.toLinearEquiv_symm, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
      HomologicalComplex.homologyMapIso_inv] using h
  exact_projection_multiply n := by
    let he := (HomologicalComplex.homologyMapIso (koszulAppendConeIso M x y) (n+1)).toLinearEquiv.symm
    simpa only [homology, ModuleCat.hom_comp, he, CategoryTheory.Iso.toLinearMap_toLinearEquiv,
      CategoryTheory.Iso.toLinearEquiv_symm, Iso.symm_hom, HomologicalComplex.homologyMapIso_inv] using
      (he.surjective.comp_exact_iff_exact).mpr
        (scalarCone_exact_projection_multiply (coefficientComplex M x) y n)
  surjective_zero := by
    simpa only [appendInclusion, HomologicalComplex.homologyMap_comp,
      ModuleCat.hom_comp, LinearMap.coe_comp, ← LinearEquiv.coe_coe, CategoryTheory.Iso.toLinearMap_toLinearEquiv,
      HomologicalComplex.homologyMapIso_hom] using
      (HomologicalComplex.homologyMapIso (koszulAppendConeIso M x y) 0).toLinearEquiv.surjective.comp
        (scalarCone_inclusion_surjective_zero (coefficientComplex M x) y)

/-- RK-05: the natural long exact homology sequence, including degree zero. -/
theorem append_long_exact_sequence : Specs.AdvCommAlg.Koszul.appendLongExactSequence.{u,v} := by
  intro R _ M _ _ x y
  exact ⟨koszulAppendConeSequence M x y⟩

/-- Multiplication is natural because all homology maps are R-linear. -/
@[reassoc] theorem homologyScalar_natural
    {C D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D) (y : R) (n : ℕ) :
    HomologicalComplex.homologyMap φ n ≫ homologyScalar D y n =
      homologyScalar C y n ≫ HomologicalComplex.homologyMap φ n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change y • (HomologicalComplex.homologyMap φ n).hom a =
    (HomologicalComplex.homologyMap φ n).hom (y • a)
  simp

/-- Both non-scalar maps in the sequence commute with coefficient maps. -/
theorem append_sequence_naturality : Specs.AdvCommAlg.Koszul.appendSequenceNaturality.{u,v} := by
  intro R _ M N _ _ _ _ x y φ S T
  constructor
  · intro n
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f n)
      (appendInclusion_natural M N x y φ S.comparison T.comparison S.canonical T.canonical)
  · intro n
    have hn : HomologicalComplex.homologyMap S.comparison.hom (n+1) ≫
        HomologicalComplex.homologyMap (appendCoefficientMap M (x ++ [y]) φ) (n+1) =
      HomologicalComplex.homologyMap (scalarConeMap (appendCoefficientMap M x φ) y) (n+1) ≫
        HomologicalComplex.homologyMap T.comparison.hom (n+1) := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
      exact congrArg (fun f => HomologicalComplex.homologyMap f (n+1))
        (appendConeComparison_natural M N x y φ S.comparison T.comparison
          S.canonical T.canonical).symm
    rw [← cancel_epi (HomologicalComplex.homologyMap S.comparison.hom (n+1))]
    rw [← Category.assoc, hn, Category.assoc, appendSequence_projection,
      scalarConeHomologyProjection_natural, appendSequence_projection_assoc]

end AdvCommAlg.Koszul
