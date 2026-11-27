import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.LinearSystem
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorLocalization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.UniversalSolutionRing
import Batteries.Tactic.OpenPrivate

namespace GaloisFormalization.PV.UniversalSolutionRing

universe u

/-- The polynomial ring on the entries of a square matrix. -/
abbrev PolynomialRing := @Specs.UniversalSolutionRing.polynomialRing.{u}

/-- The square matrix of polynomial variables. -/
noncomputable abbrev indeterminateMatrix := @Specs.UniversalSolutionRing.indeterminateMatrix.{u}

/-- The universal ring obtained by inverting the generic determinant. -/
abbrev Ring := @Specs.UniversalSolutionRing.ring.{u}

/-- The generic matrix over the universal ring, bundled with its inverse. -/
noncomputable abbrev genericMatrix := @Specs.UniversalSolutionRing.genericMatrix.{u}

open scoped Matrix

open private derivationGraph derivationOfSection from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorLocalization

variable {K : Type u} [Field K] {n : ℕ}

/-- The underlying generic unit matrix has the localized variables as its entries. -/
theorem genericMatrix_val (K : Type u) [Field K] (n : ℕ) :
    (genericMatrix K n).val =
      (indeterminateMatrix K n).map (algebraMap (PolynomialRing K n) (Ring K n)) := rfl

/-- The integer algebra structure on a ring is unique. -/
private def rebaseIntDerivation {R : Type u} [CommRing R] (source target : Algebra ℤ R)
    (d : @Derivation ℤ R R _ _ _ source _ _) : @Derivation ℤ R R _ _ _ target _ _ :=
  match Subsingleton.elim source target with
  | rfl => d

private theorem rebaseIntDerivation_apply {R : Type u} [CommRing R]
    (source target : Algebra ℤ R) (d : @Derivation ℤ R R _ _ _ source _ _) (x : R) :
    (@Derivation.toLinearMap ℤ R R _ _ _ target _ _ (rebaseIntDerivation source target d)) x =
      (@Derivation.toLinearMap ℤ R R _ _ _ source _ _ d) x := by
  have h : source = target := Subsingleton.elim _ _
  subst target
  rfl

theorem differentialOperator : Specs.UniversalSolutionRing.differentialOperator.{u} := by
  intro K _ n d A
  let P := PolynomialRing K n
  let U := Ring K n
  let X := indeterminateMatrix K n
  let B := A.map MvPolynomial.C * X
  let g : P →+* TrivSqZeroExt P P :=
    MvPolynomial.eval₂Hom (derivationGraph d MvPolynomial.C)
      (fun p => ⟨MvPolynomial.X p, B p.1 p.2⟩)
  have hg : (TrivSqZeroExt.fstHom P P P).toRingHom.comp g = RingHom.id P := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (g (MvPolynomial.C a)).fst = MvPolynomial.C a
      rw [show g (MvPolynomial.C a) = derivationGraph d MvPolynomial.C a from
        MvPolynomial.eval₂Hom_C _ _ _]
      rfl
    · intro i
      change (g (MvPolynomial.X i)).fst = MvPolynomial.X i
      rw [show g (MvPolynomial.X i) = ⟨MvPolynomial.X i, B i.1 i.2⟩ from
        MvPolynomial.eval₂Hom_X' _ _ _]
      rfl
  let dP := derivationOfSection g (RingHom.congr_fun hg)
  let M := Submonoid.powers X.det
  let δ := Operator.localizeDerivation (R := P) (L := U) M dP
  -- The localization has its own integer algebra instance. Keep the same linear map.
  let dU := rebaseIntDerivation (Ring.toIntAlgebra U) (inferInstanceAs (Algebra ℤ (Ring K n))) δ
  refine ⟨dP, dU, ?_, ?_, ?_⟩
  · intro a
    change (g (MvPolynomial.C a)).snd = _
    rw [show g (MvPolynomial.C a) = derivationGraph d MvPolynomial.C a from
      MvPolynomial.eval₂Hom_C _ _ _]
    rfl
  · apply Matrix.ext
    intro i j
    change (g (MvPolynomial.X (i, j))).snd = B i j
    rw [show g (MvPolynomial.X (i, j)) = ⟨MvPolynomial.X (i, j), B i j⟩ from
      MvPolynomial.eval₂Hom_X' _ _ _]
    rfl
  · intro p
    exact (rebaseIntDerivation_apply _ _ δ _).trans
      (Operator.localizeDerivation_algebraMap (R := P) (L := U) M dP p)

private noncomputable def substitute (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) :
    PolynomialRing K n →+* PolynomialRing K n :=
  let B : Matrix (Fin n) (Fin n) (PolynomialRing K n) :=
    A.map MvPolynomial.C * indeterminateMatrix K n
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp σ.toRingHom) (fun p => B p.1 p.2)

@[simp] private theorem substitute_C (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) (a : K) :
    substitute σ A (MvPolynomial.C a) = MvPolynomial.C (σ a) :=
  MvPolynomial.eval₂Hom_C _ _ _

private theorem indeterminateMatrix_map_substitute (σ : K ≃+* K)
    (A : Matrix (Fin n) (Fin n) K) :
    (indeterminateMatrix K n).map (substitute σ A) = A.map MvPolynomial.C * indeterminateMatrix K n := by
  apply Matrix.ext
  intro i j
  exact MvPolynomial.eval₂Hom_X' _ _ (i, j)

private theorem substitute_comp (σ : K ≃+* K) (A B : Matrix (Fin n) (Fin n) K)
    (h : B.map σ * A = 1) :
    (substitute σ A).comp (substitute σ.symm B) = RingHom.id (PolynomialRing K n) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · have hB : ((B.map MvPolynomial.C).map (substitute σ A)) = (B.map σ).map MvPolynomial.C :=
      Matrix.ext fun i j => substitute_C σ A (B i j)
    have hX : (indeterminateMatrix K n).map ((substitute σ A).comp (substitute σ.symm B)) =
        indeterminateMatrix K n := by
      calc
        _ = ((indeterminateMatrix K n).map (substitute σ.symm B)).map (substitute σ A) := rfl
        _ = (B.map MvPolynomial.C * indeterminateMatrix K n).map (substitute σ A) := by
          rw [indeterminateMatrix_map_substitute]
        _ = (B.map σ).map MvPolynomial.C * (A.map MvPolynomial.C * indeterminateMatrix K n) := by
          rw [Matrix.map_mul, hB, indeterminateMatrix_map_substitute]
        _ = indeterminateMatrix K n := by
          rw [← Matrix.mul_assoc, ← Matrix.map_mul (f := MvPolynomial.C), h,
            Matrix.map_one _ (map_zero MvPolynomial.C) (map_one MvPolynomial.C), Matrix.one_mul]
    rintro ⟨i, j⟩
    exact congrArg (fun M => M i j) hX

private theorem substitute_det (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) :
    substitute σ A (indeterminateMatrix K n).det =
      MvPolynomial.C A.det * (indeterminateMatrix K n).det := by
  rw [RingHom.map_det]
  change ((indeterminateMatrix K n).map (substitute σ A)).det = _
  rw [indeterminateMatrix_map_substitute, Matrix.det_mul]
  change (MvPolynomial.C.mapMatrix A).det * (indeterminateMatrix K n).det = _
  rw [← RingHom.map_det]

private noncomputable def localizeSubstitution (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A.det) : Ring K n →+* Ring K n :=
  IsLocalization.Away.lift (indeterminateMatrix K n).det
    (g := (algebraMap (PolynomialRing K n) (Ring K n)).comp (substitute σ A)) <| by
    rw [RingHom.comp_apply, substitute_det, map_mul]
    exact (hA.map ((algebraMap (PolynomialRing K n) (Ring K n)).comp MvPolynomial.C)).mul
      (IsLocalization.Away.algebraMap_isUnit (indeterminateMatrix K n).det)

@[simp] private theorem localizeSubstitution_algebraMap
    (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det) (p : PolynomialRing K n) :
    localizeSubstitution σ A hA (algebraMap (PolynomialRing K n) (Ring K n) p) =
      algebraMap (PolynomialRing K n) (Ring K n) (substitute σ A p) :=
  IsLocalization.Away.lift_eq _ _ _

private theorem localizeSubstitution_comp (σ : K ≃+* K)
    (A B : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det) (hB : IsUnit B.det)
    (h : B.map σ * A = 1) :
    (localizeSubstitution σ A hA).comp (localizeSubstitution σ.symm B hB) =
      RingHom.id (Ring K n) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (indeterminateMatrix K n).det)
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, localizeSubstitution_algebraMap, RingHom.id_apply]
  exact congrArg (algebraMap (PolynomialRing K n) (Ring K n))
    (RingHom.congr_fun (substitute_comp σ A B h) p)

theorem differenceOperator : Specs.UniversalSolutionRing.differenceOperator.{u} := by
  intro K _ n σ A
  let B := (A⁻¹).val.map σ.symm
  have hBA : B.map σ * A.val = 1 := by
    have hB : B.map σ = (A⁻¹).val := Matrix.ext fun _ _ => σ.apply_symm_apply _
    rw [hB]
    exact A.inv_mul
  have hAB : A.val.map σ.symm * B = 1 := by
    change A.val.map σ.symm * (A⁻¹).val.map σ.symm = 1
    rw [← Matrix.map_mul (f := σ.symm), A.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hdet (V : Matrix.GeneralLinearGroup (Fin n) K) : IsUnit V.val.det :=
    Matrix.GeneralLinearGroup.val_det_apply V ▸ (Matrix.GeneralLinearGroup.det V).isUnit
  have hBdet : IsUnit B.det := by
    change IsUnit (σ.symm.toRingHom.mapMatrix (A⁻¹).val).det
    rw [← RingHom.map_det]
    exact (hdet A⁻¹).map σ.symm.toRingHom
  let σP := RingEquiv.ofRingHom (substitute σ A.val) (substitute σ.symm B)
    (substitute_comp σ A.val B hBA) (substitute_comp σ.symm B A.val hAB)
  let σU := RingEquiv.ofRingHom (localizeSubstitution σ A.val (hdet A))
    (localizeSubstitution σ.symm B hBdet)
    (localizeSubstitution_comp σ A.val B (hdet A) hBdet hBA)
    (localizeSubstitution_comp σ.symm B A.val hBdet (hdet A) hAB)
  exact ⟨σP, σU, substitute_C σ A.val, substitute_C σ.symm B,
    indeterminateMatrix_map_substitute σ A.val,
    indeterminateMatrix_map_substitute σ.symm B, substitute_det σ A.val,
    localizeSubstitution_algebraMap σ A.val (hdet A),
    localizeSubstitution_algebraMap σ.symm B hBdet⟩

theorem nontrivial (K : Type u) [Field K] (n : ℕ) : Nontrivial (Ring K n) := by
  let X := indeterminateMatrix K n
  let f : PolynomialRing K n →+* K :=
    MvPolynomial.eval (fun p => (1 : Matrix (Fin n) (Fin n) K) p.1 p.2)
  have h : f.mapMatrix X = 1 := by
    apply Matrix.ext
    intro i j
    change f (MvPolynomial.X (i, j)) = _
    exact MvPolynomial.eval_X _
  have hdet : f X.det = 1 := by rw [RingHom.map_det, h, Matrix.det_one]
  exact (IsLocalization.Away.lift (S := Ring K n) (g := f) X.det
    (hdet ▸ isUnit_one : IsUnit (f X.det))).domain_nontrivial

private theorem genericMatrix_solution (A : Matrix (Fin n) (Fin n) K)
    (f : PolynomialRing K n → PolynomialRing K n) (g : Ring K n → Ring K n)
    (hX : (indeterminateMatrix K n).map f = A.map MvPolynomial.C * indeterminateMatrix K n)
    (hg : ∀ p, g (algebraMap (PolynomialRing K n) (Ring K n) p) =
      algebraMap (PolynomialRing K n) (Ring K n) (f p)) :
    (genericMatrix K n).val.map g = A.map (algebraMap K (Ring K n)) * (genericMatrix K n).val := by
  let X := indeterminateMatrix K n
  let ι := algebraMap (PolynomialRing K n) (Ring K n)
  have h : (X.map ι).map g = (X.map f).map ι := Matrix.ext fun i j => hg (X i j)
  rw [genericMatrix_val, h, hX, Matrix.map_mul (f := ι)]
  rfl

/-- The generic matrix is fundamental for a compatible operator on the universal ring. -/
theorem exists_operator {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
    (D : Operator kind K) (A : LinearSystem kind K n) :
    ∃ E : Operator kind (Ring K n), D.IsExtension E ∧ A.IsFundamental E (genericMatrix K n) := by
  let := nontrivial K n
  have hinj : Function.Injective (algebraMap K (Ring K n)) :=
    (algebraMap K (Ring K n)).injective
  let ι := algebraMap (PolynomialRing K n) (Ring K n)
  cases kind
  · obtain ⟨dP, dU, hC, hX, hU⟩ :=
      @differentialOperator K _ n D.toDerivation A.coefficientMatrix
    let source : Algebra ℤ (Ring K n) := inferInstance
    let target := Ring.toIntAlgebra (Ring K n)
    let δ := rebaseIntDerivation source target dU
    have hδ (x : Ring K n) : δ x = dU x := rebaseIntDerivation_apply source target dU x
    refine ⟨Operator.differential δ, ⟨?_, hinj⟩, ?_⟩
    · intro a
      change ι (MvPolynomial.C (D.toDerivation a)) = δ (ι (MvPolynomial.C a))
      rw [hδ, hU, hC]
    · exact genericMatrix_solution A.coefficientMatrix dP δ hX
        (fun p => (hδ _).trans (hU p))
  · let M : Matrix.GeneralLinearGroup (Fin n) K := A
    obtain ⟨σP, σU, hC, _, hX, _, _, hU, _⟩ :=
      @differenceOperator K _ n D.toRingEquiv M
    refine ⟨Operator.difference σU, ⟨?_, hinj⟩, ?_⟩
    · intro a
      change ι (MvPolynomial.C (D.toRingEquiv a)) = σU (ι (MvPolynomial.C a))
      rw [hU, hC]
    · exact genericMatrix_solution A.coefficientMatrix σP σU hX hU

/-- The entries of the generic matrix and its inverse determinant generate the ring. -/
theorem generated_by_entries (K : Type u) [Field K] (n : ℕ) :
    Algebra.adjoin K
      (Set.range (fun p : Fin n × Fin n => (genericMatrix K n).val p.1 p.2) ∪
        {LinearSystem.determinantInverse (genericMatrix K n)}) = ⊤ := by
  let P := PolynomialRing K n
  let U := Ring K n
  let ι := algebraMap P U
  let X := indeterminateMatrix K n
  let Y := genericMatrix K n
  let d := Matrix.GeneralLinearGroup.det Y
  let S : Subalgebra K U := Algebra.adjoin K
    (Set.range (fun p : Fin n × Fin n => Y.val p.1 p.2) ∪
      {LinearSystem.determinantInverse Y})
  have hvar (p : Fin n × Fin n) : ι (MvPolynomial.X p) ∈ S :=
    Algebra.subset_adjoin (Set.mem_union_left _ ⟨p, rfl⟩)
  have hinv : (↑d⁻¹ : U) ∈ S :=
    Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
  have hpoly (p : P) : ι p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C a => exact S.algebraMap_mem a
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact S.mul_mem hp (hvar i)
  have hdet : (d : U) = ι X.det := by
    rw [RingHom.map_det]
    exact Matrix.GeneralLinearGroup.val_det_apply Y
  change S = ⊤
  apply top_unique
  intro z _
  obtain ⟨m, p, hp⟩ := IsLocalization.Away.surj X.det z
  have hz : z = ι p * (↑d⁻¹ : U) ^ m := by
    calc
      z = z * ((d : U) ^ m * (↑d⁻¹ : U) ^ m) := by
        rw [← mul_pow, Units.mul_inv, one_pow, mul_one]
      _ = ι p * (↑d⁻¹ : U) ^ m := by rw [← mul_assoc, hdet, hp]
  rw [hz]
  exact S.mul_mem (hpoly p) (S.pow_mem hinv m)

theorem finiteType (K : Type u) [Field K] (n : ℕ) : Algebra.FiniteType K (Ring K n) := by
  classical
  let Y := genericMatrix K n
  let s := Set.range (fun p : Fin n × Fin n => Y.val p.1 p.2) ∪
    {LinearSystem.determinantInverse Y}
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_singleton _)
  exact ⟨hs.toFinset, by rw [hs.coe_toFinset]; exact generated_by_entries K n⟩

theorem isNoetherian (K : Type u) [Field K] (n : ℕ) : IsNoetherianRing (Ring K n) := by
  let := finiteType K n
  exact Algebra.FiniteType.isNoetherianRing K (Ring K n)

end GaloisFormalization.PV.UniversalSolutionRing
