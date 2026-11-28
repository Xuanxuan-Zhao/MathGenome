import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.GroupAlgebraCenter
import MathGenome.Internal.AlgebraCore.P103.Ch08.ClassSumIntegrality

noncomputable section

open scoped MonoidAlgebra
open P103.Ch08.ClassSumIntegrality (classSum classSum_coeff)

namespace RepTheorySurvey.Modular.GroupAlgebraCenter

variable {G : Type*} [Group G] {R : Type*} [CommRing R]

/-- A group algebra element is central exactly when its coefficients are constant
on each conjugacy class. -/
theorem mem_center_iff (z : R[G]) :
    z ∈ Subalgebra.center R R[G] ↔
      ∀ x y : G, ConjClasses.mk x = ConjClasses.mk y → z.coeff x = z.coeff y := by
  constructor
  · intro hz x y hxy
    obtain ⟨g, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hxy)
    have h := Subalgebra.mem_center_iff.mp hz (MonoidAlgebra.single g 1)
    simpa using congrArg (fun a : R[G] => a.coeff (g * x)) h
  · intro hz
    apply Subalgebra.mem_center_iff.mpr
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      change MonoidAlgebra.single g 1 * z = z * MonoidAlgebra.single g 1
      ext x
      simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
        one_mul, mul_one]
      exact hz _ _ (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, by simp⟩))
    | add a b ha hb => rw [add_mul, mul_add, ha, hb]
    | smul r a ha => rw [smul_mul_assoc, mul_smul_comm, ha]

theorem classSum_mem_center [Fintype G] (R : Type*) [CommRing R] (C : ConjClasses G) :
    classSum R C ∈ Subalgebra.center R R[G] := by
  classical
  apply (mem_center_iff _).2
  intro x y hxy
  by_cases h : ConjClasses.mk y = C <;> simp [classSum_coeff, hxy, h]

@[simp] theorem classCoefficients_mk (z : Subalgebra.center R R[G]) (g : G) :
    classCoefficients R z (ConjClasses.mk g) = z.val.coeff g :=
  (mem_center_iff _).1 z.property _ _ (Quotient.out_eq _)

@[simp] theorem classSumCombination_coeff [Fintype G] (f : ConjClasses G → R) (g : G) :
    (classSumCombination f).coeff g = f (ConjClasses.mk g) := by
  classical
  unfold classSumCombination
  simp [MonoidAlgebra.coeff_sum, classSum_coeff, eq_comm]

/-- The center is linearly equivalent to the functions on conjugacy classes. -/
def centerClassEquiv [Fintype G] (R : Type*) [CommRing R] :
    Subalgebra.center R R[G] ≃ₗ[R] (ConjClasses G → R) where
  __ := classCoefficients R
  invFun f := ⟨classSumCombination f, (mem_center_iff _).2 (by
    intro x y hxy
    simp only [classSumCombination_coeff, hxy])⟩
  left_inv z := by
    apply Subtype.ext
    ext g
    exact (classSumCombination_coeff _ _).trans (classCoefficients_mk _ _)
  right_inv f := by
    funext C
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    exact (classCoefficients_mk _ _).trans (classSumCombination_coeff _ _)

@[simp] theorem centerClassEquiv_apply_mk [Fintype G]
    (z : Subalgebra.center R R[G]) (g : G) :
    centerClassEquiv R z (ConjClasses.mk g) = z.val.coeff g :=
  classCoefficients_mk z g

@[simp] theorem centerClassEquiv_symm_val [Fintype G] (f : ConjClasses G → R) :
    ((centerClassEquiv R).symm f).val = classSumCombination f :=
  rfl

theorem centerClassEquiv_spec : Specs.centerClassEquivType := by
  intro G _ _ R _
  exact ⟨centerClassEquiv R, centerClassEquiv_apply_mk, centerClassEquiv_symm_val⟩

/-- The basis of the center indexed by conjugacy classes. -/
def classSumBasis [Fintype G] (R : Type*) [CommRing R] :
    Module.Basis (ConjClasses G) R (Subalgebra.center R R[G]) :=
  Module.Basis.ofEquivFun (centerClassEquiv R)

@[simp] theorem classSumBasis_val [Fintype G] (C : ConjClasses G) :
    (classSumBasis R C).val = classSum R C := by
  classical
  have hb : classSumBasis R C = (centerClassEquiv R).symm (Pi.single C 1) :=
    congrFun (Module.Basis.coe_ofEquivFun _) C
  rw [hb, centerClassEquiv_symm_val]
  ext g
  rw [classSumCombination_coeff]
  by_cases h : ConjClasses.mk g = C <;> simp [h]

theorem classSumBasis_spec : Specs.classSumBasisType := by
  intro G _ _ R _
  exact ⟨classSumBasis R, classSumBasis_val⟩

variable {S : Type*} [CommRing S]

/-- A coefficient ring homomorphism restricts to the centers. -/
def mapCenter (φ : R →+* S) :
    Subalgebra.center R R[G] →+* Subalgebra.center S S[G] :=
  ((MonoidAlgebra.mapRingHom G φ).comp (Subalgebra.center R R[G]).val.toRingHom).codRestrict
    (Subalgebra.center S S[G]) fun z => (mem_center_iff _).2 fun x y hxy => by
      change (MonoidAlgebra.mapRingHom G φ z.val).coeff x =
        (MonoidAlgebra.mapRingHom G φ z.val).coeff y
      simp only [MonoidAlgebra.coeff_mapRingHom]
      exact congrArg φ ((mem_center_iff _).1 z.property x y hxy)

@[simp] theorem mapCenter_val (φ : R →+* S) (z : Subalgebra.center R R[G]) :
    (mapCenter φ z).val = MonoidAlgebra.mapRingHom G φ z.val := rfl

@[simp] theorem classCoefficients_mapCenter (φ : R →+* S)
    (z : Subalgebra.center R R[G]) (C : ConjClasses G) :
    classCoefficients S (mapCenter φ z) C = φ (classCoefficients R z C) :=
  MonoidAlgebra.coeff_mapRingHom φ z.val (Quotient.out C)

@[simp] theorem centerClassEquiv_mapCenter [Fintype G] (φ : R →+* S)
    (z : Subalgebra.center R R[G]) (C : ConjClasses G) :
    centerClassEquiv S (mapCenter φ z) C = φ (centerClassEquiv R z C) :=
  classCoefficients_mapCenter φ z C

theorem mapCenter_spec : Specs.mapCenterType := by
  intro G _ R _ S _ φ
  exact ⟨mapCenter φ, mapCenter_val φ, classCoefficients_mapCenter φ⟩

end RepTheorySurvey.Modular.GroupAlgebraCenter
