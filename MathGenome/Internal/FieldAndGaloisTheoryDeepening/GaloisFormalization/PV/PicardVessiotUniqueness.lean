import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.ConstantIdealDescent
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteTypeResiduesAndPoints
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FundamentalMatrices
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotExistence
import Mathlib.RingTheory.Flat.Basic
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotUniqueness

namespace GaloisFormalization.PV

open Matrix
open scoped Matrix TensorProduct
open private stable_comap from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotExistence

universe u v w

private theorem determinantInverse_map {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (f : R →+* S) (Y : GL (Fin n) R) :
    LinearSystem.determinantInverse (GeneralLinearGroup.map f Y) =
      f (LinearSystem.determinantInverse Y) := by
  simp only [LinearSystem.determinantInverse, GeneralLinearGroup.map_det, ← map_inv]
  rfl

private theorem determinantInverse_mul {R : Type*} [CommRing R]
    {n : ℕ} (Y Z : GL (Fin n) R) :
    LinearSystem.determinantInverse (Y * Z) =
      LinearSystem.determinantInverse Y * LinearSystem.determinantInverse Z := by
  simp only [LinearSystem.determinantInverse, map_mul, mul_inv, Units.val_mul]

private theorem matrixGeneratedSubalgebra_le_iff {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] {n : ℕ} {Y : GL (Fin n) R} {T : Subalgebra K R} :
    matrixGeneratedSubalgebra K Y ≤ T ↔
      LinearSystem.determinantInverse Y ∈ T ∧ ∀ i j, Y.val i j ∈ T := by
  rw [matrixGeneratedSubalgebra, Algebra.adjoin_le_iff]
  constructor
  · intro h
    exact ⟨h (Set.mem_insert _ _), fun i j => h (Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩)⟩
  · rintro ⟨hdet, hentry⟩ x (hx | ⟨⟨i, j⟩, hx⟩)
    · rwa [hx]
    · rw [← hx]
      exact hentry i j

private theorem matrixGeneratedSubalgebra_mul_le {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] {n : ℕ} {Y Z : GL (Fin n) R} {T : Subalgebra K R}
    (hY : matrixGeneratedSubalgebra K Y ≤ T) (hZ : matrixGeneratedSubalgebra K Z ≤ T) :
    matrixGeneratedSubalgebra K (Y * Z) ≤ T := by
  obtain ⟨hy, hy'⟩ := matrixGeneratedSubalgebra_le_iff.mp hY
  obtain ⟨hz, hz'⟩ := matrixGeneratedSubalgebra_le_iff.mp hZ
  apply matrixGeneratedSubalgebra_le_iff.mpr
  refine ⟨determinantInverse_mul Y Z ▸ T.mul_mem hy hz, fun i j => ?_⟩
  change (Y.val * Z.val) i j ∈ T
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => T.mul_mem (hy' i l) (hz' l j)

private theorem matrixGeneratedSubalgebra_map_le {K R S : Type*}
    [CommRing K] [CommRing R] [CommRing S] [Algebra K S]
    {n : ℕ} (Y : GL (Fin n) R) (f : R →+* S) {T : Subalgebra K S}
    (hf : ∀ r, f r ∈ T) : matrixGeneratedSubalgebra K (GeneralLinearGroup.map f Y) ≤ T := by
  apply matrixGeneratedSubalgebra_le_iff.mpr
  rw [determinantInverse_map]
  exact ⟨hf _, fun _ _ => hf _⟩

private theorem matrixGeneratedSubalgebra_map {K R S : Type*}
    [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {n : ℕ} (Y : GL (Fin n) R) (f : R →ₐ[K] S) :
    matrixGeneratedSubalgebra K (GeneralLinearGroup.map f.toRingHom Y) =
      (matrixGeneratedSubalgebra K Y).map f := by
  let Z := GeneralLinearGroup.map f.toRingHom Y
  have hentries : f '' (Set.range fun ij : Fin n × Fin n => Y.val ij.1 ij.2) =
      Set.range (fun ij : Fin n × Fin n => Z.val ij.1 ij.2) :=
    (Set.range_comp' f _).symm
  have hdet : f (LinearSystem.determinantInverse Y) = LinearSystem.determinantInverse Z :=
    (determinantInverse_map f.toRingHom Y).symm
  change matrixGeneratedSubalgebra K Z = _
  rw [matrixGeneratedSubalgebra, matrixGeneratedSubalgebra, ← Algebra.adjoin_image,
    Set.image_insert_eq, hdet, hentries]

private theorem matrixGeneratedSubalgebra_mul_base {K S : Type*} [CommRing K] [CommRing S]
    [Algebra K S] {n : ℕ} (Y : GL (Fin n) S) (B : GL (Fin n) K) :
    matrixGeneratedSubalgebra K (Y * GeneralLinearGroup.map (algebraMap K S) B) =
      matrixGeneratedSubalgebra K Y := by
  apply le_antisymm
  · exact matrixGeneratedSubalgebra_mul_le le_rfl
      (matrixGeneratedSubalgebra_map_le B _ (Subalgebra.algebraMap_mem _))
  · have h := matrixGeneratedSubalgebra_mul_le
      (T := matrixGeneratedSubalgebra K (Y * GeneralLinearGroup.map (algebraMap K S) B))
      le_rfl (matrixGeneratedSubalgebra_map_le B⁻¹ _ (Subalgebra.algebraMap_mem _))
    rwa [GeneralLinearGroup.map_inv, mul_inv_cancel_right] at h

private theorem matrixGeneratedSubalgebra_fg {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] {n : ℕ} (Y : GL (Fin n) R) : (matrixGeneratedSubalgebra K Y).FG := by
  classical
  let s := insert (LinearSystem.determinantInverse Y)
    (Set.range fun ij : Fin n × Fin n => Y.val ij.1 ij.2)
  have hs : s.Finite := (Set.finite_range _).insert _
  exact ⟨hs.toFinset, by rw [hs.coe_toFinset]; rfl⟩

private theorem matrix_lift_to_generated {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] {n : ℕ} (Y : GL (Fin n) R) :
    let T := matrixGeneratedSubalgebra K Y
    ∃ X : GL (Fin n) T, GeneralLinearGroup.map T.val.toRingHom X = Y := by
  let T := matrixGeneratedSubalgebra K Y
  obtain ⟨hd, he⟩ := matrixGeneratedSubalgebra_le_iff.mp (le_rfl (a := T))
  let M : Matrix (Fin n) (Fin n) T := Matrix.of fun i j => ⟨Y.val i j, he i j⟩
  let d : T := ⟨LinearSystem.determinantInverse Y, hd⟩
  have hM : M.map T.val = Y.val := rfl
  have hdet : T.val M.det = Y.val.det :=
    (RingHom.map_det T.val.toRingHom M).trans (congrArg Matrix.det hM)
  have hunit : IsUnit M.det := by
    apply IsUnit.of_mul_eq_one d
    apply (Subtype.val_injective : Function.Injective T.val)
    change T.val (M.det * d) = T.val 1
    rw [map_mul, hdet, map_one]
    exact (GeneralLinearGroup.det Y).val_inv
  obtain ⟨X, hX⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr hunit
  exact ⟨X, Units.ext (by change X.val.map T.val = Y.val; rw [hX, hM])⟩

/-- A chosen isomorphism extends uniquely over the canonical localizations. -/
theorem picardVessiotEquiv_totalExtension : Specs.picardVessiotEquivTotalExtension.{u, v, w} := by
  intro kind K _ R _ S _ _ _ n D A E F E' F' hE hF e
  change Operator.AlgEquiv K E F at e
  let er : Operator.RingEquiv E F := ⟨e.val.toRingEquiv, e.property⟩
  obtain ⟨g, hg, hg_unique⟩ :=
    Operator.fractionOperatorEquiv_existsUnique er hE.2.1 hF.2.1
  have hl : ∀ k : K, g.val (algebraMap K (TotalQuotientRing R) k) =
      algebraMap K (TotalQuotientRing S) k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K R (TotalQuotientRing R),
      IsScalarTower.algebraMap_apply K S (TotalQuotientRing S)]
    rw [hg]
    exact congrArg (algebraMap S (TotalQuotientRing S)) (e.val.commutes k)
  let ga : TotalQuotientRing R ≃ₐ[K] TotalQuotientRing S :=
    { g.val with commutes' := hl }
  refine ⟨⟨ga, g.property⟩, hg, ?_⟩
  intro f hf
  have heq := hg_unique ⟨f.val.toRingEquiv, f.property⟩ hf
  apply Subtype.ext
  apply AlgEquiv.toRingEquiv_injective
  exact congrArg Subtype.val heq

private theorem fundamental_map_equation {kind : OperatorKind} {K R S : Type*}
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {n : ℕ} {A : LinearSystem kind K n} {F : Operator kind R} {E : Operator kind S}
    (f : R →ₐ[K] S) (hf : F.Commutes E f) (X : GL (Fin n) R) :
    (X.val.map F.apply).map f = (A.mapCoefficients R * X.val).map f ↔
      A.IsFundamental E (GeneralLinearGroup.map f.toRingHom X) := by
  change _ ↔ (X.val.map f).map E.apply = A.mapCoefficients S * X.val.map f
  have hop : (X.val.map F.apply).map f = (X.val.map f).map E.apply :=
    Matrix.ext fun i j => hf (X.val i j)
  have hcoeff : (A.mapCoefficients R).map f = A.mapCoefficients S :=
    Matrix.ext fun i j => f.commutes (A.coefficientMatrix i j)
  rw [hop, Matrix.map_mul (f := f), hcoeff]

private theorem fundamental_map {kind : OperatorKind} {K R S : Type*}
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {n : ℕ} {A : LinearSystem kind K n} {F : Operator kind R} {E : Operator kind S}
    {X : GL (Fin n) R} (hX : A.IsFundamental F X)
    (f : R →ₐ[K] S) (hf : F.Commutes E f) :
    A.IsFundamental E (GeneralLinearGroup.map f.toRingHom X) :=
  (fundamental_map_equation f hf X).mp (congrArg (fun M : Matrix (Fin n) (Fin n) R => M.map f) hX)

private theorem fundamental_of_map {kind : OperatorKind} {K R S : Type*}
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    {n : ℕ} {A : LinearSystem kind K n} {F : Operator kind R} {E : Operator kind S}
    (f : R →ₐ[K] S) (hfi : Function.Injective f) (hf : F.Commutes E f) (X : GL (Fin n) R)
    (hX : A.IsFundamental E (GeneralLinearGroup.map f.toRingHom X)) :
    A.IsFundamental F X := by
  have h := (fundamental_map_equation f hf X).mpr hX
  exact Matrix.ext fun i j => hfi (congrArg (fun M : Matrix (Fin n) (Fin n) S => M i j) h)

section Specialization

private def tensorEvaluation {C S B : Type*} [CommRing C] [CommRing S] [CommRing B]
    [Algebra C S] [Algebra C B] (p : B →ₐ[C] C) :
    S ⊗[C] B →ₐ[S] S :=
  Algebra.TensorProduct.lift (AlgHom.id S S) ((Algebra.ofId C S).comp p)
    (fun _ _ => Commute.all _ _)

private theorem tensorEvaluation_tmul {C S B : Type*} [CommRing C] [CommRing S] [CommRing B]
    [Algebra C S] [Algebra C B] (p : B →ₐ[C] C) (s : S) (b : B) :
    tensorEvaluation p (s ⊗ₜ[C] b) = s * algebraMap C S (p b) :=
  rfl

private theorem tensorEvaluation_commutes {kind : OperatorKind} {C S B : Type*}
    [Field C] [CommRing S] [CommRing B] [Algebra C S] [Algebra C B]
    {E : Operator kind S} {G : Operator kind (S ⊗[C] B)}
    (hC : Operator.HasConstantField (C := C) E)
    (hG : Specs.tensorLaws (R := C) E (Operator.trivial kind B) G) (p : B →ₐ[C] C) :
    G.Commutes E (tensorEvaluation p) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [Operator.map_add, map_add, hx, hy]
  | tmul s b =>
    have hc := (hC (algebraMap C S (p b))).mpr ⟨p b, rfl⟩
    cases kind with
    | differential =>
      have h : G (s ⊗ₜ[C] b) = E s ⊗ₜ[C] b + s ⊗ₜ[C] (0 : B) := hG.1 s b
      rw [h, TensorProduct.tmul_zero, add_zero, tensorEvaluation_tmul, tensorEvaluation_tmul]
      change E.toDerivation (algebraMap C S (p b)) = 0 at hc
      change E.toDerivation s * algebraMap C S (p b) =
        E.toDerivation (s * algebraMap C S (p b))
      rw [E.toDerivation.leibniz, hc, smul_zero, zero_add, smul_eq_mul,
        mul_comm (algebraMap C S (p b))]
    | difference =>
      have h : G (s ⊗ₜ[C] b) = E s ⊗ₜ[C] b := hG.1.1 s b
      rw [h, tensorEvaluation_tmul, tensorEvaluation_tmul]
      change E.toRingEquiv (algebraMap C S (p b)) = algebraMap C S (p b) at hc
      change E s * algebraMap C S (p b) = E.toRingEquiv (s * algebraMap C S (p b))
      rw [map_mul, hc]
      rfl

private theorem injective_of_simple {kind : OperatorKind} {R S : Type*}
    [CommRing R] [CommRing S] [Nontrivial S] {F : Operator kind R} {E : Operator kind S}
    (hR : F.IsSimple) {f : R →+* S} (hf : F.Commutes E f) : Function.Injective f := by
  have hstable := stable_comap hf (J := (⊥ : Ideal S)) (by
    have hforward {x : S} (hx : x ∈ (⊥ : Ideal S)) : E x ∈ (⊥ : Ideal S) :=
      Ideal.mem_bot.mpr ((congrArg E (Ideal.mem_bot.mp hx)).trans E.map_zero)
    cases kind
    · exact fun _ hx => hforward hx
    · exact ⟨fun _ hx => hforward hx,
        fun _ hx => Ideal.mem_bot.mpr ((congrArg E.toRingEquiv.symm (Ideal.mem_bot.mp hx)).trans
          (map_zero _))⟩)
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
  exact (hR.2 _ hstable).resolve_right fun htop =>
    bot_ne_top (Ideal.comap_eq_top_iff.mp htop)

/-- A rational point of the constant subalgebra specializes its generators in the
ambient tensor product while fixing the left factor. -/
private theorem exists_constant_evaluation {kind : OperatorKind} {C S T : Type*}
    [Field C] [IsAlgClosed C] [CommRing S] [CommRing T] [Nontrivial T]
    [Algebra C S] [Algebra C T] [Algebra S T] [IsScalarTower C S T]
    {E : Operator kind S} {G : Operator kind T} (B : Subalgebra C T)
    [Algebra.FiniteType C B]
    (hEs : E.IsSimple) (hC : Operator.HasConstantField (C := C) E)
    (hST : E.IsExtension G) (hBconst : ∀ b : B, G.IsConstant (b : T))
    (hTB : Algebra.adjoin S (B : Set T) = ⊤) :
    ∃ (p : B →ₐ[C] C) (q : T →ₐ[S] S),
      G.Commutes E q ∧ ∀ b : B, q b = algebraMap C S (p b) := by
  let H : Operator kind (S ⊗[C] B) :=
    Operator.tensor (Operator.HasConstantField.isAlgebra hC) (Operator.trivial_isAlgebra kind)
  have hH : Specs.tensorLaws (R := C) E (Operator.trivial kind B) H :=
    Operator.tensor_laws (Operator.HasConstantField.isAlgebra hC) (Operator.trivial_isAlgebra kind)
  obtain ⟨e, he⟩ := Operator.constantTensorMulIsEquiv (G := H) B hEs hC hST hH hBconst hTB
  change Operator.AlgEquiv S H G at e
  change e.val.toAlgHom = Operator.constantTensorMul B at he
  obtain ⟨p⟩ := existsAlgHom C B
  let q : T →ₐ[S] S := (tensorEvaluation p).comp e.val.symm.toAlgHom
  refine ⟨p, q, ?_, fun b => ?_⟩
  · exact (tensorEvaluation_commutes hC hH p).comp
      (Operator.Commutes.inverse (f := e.val.toEquiv) e.property)
  · have hb : e.val ((1 : S) ⊗ₜ[C] b) = (b : T) := by
      change e.val.toAlgHom ((1 : S) ⊗ₜ[C] b) = (b : T)
      rw [he, Operator.constantTensorMul_tmul, map_one, one_mul]
    change tensorEvaluation p (e.val.symm (b : T)) = _
    rw [← hb, e.val.symm_apply_apply, tensorEvaluation_tmul, one_mul]

variable {kind : OperatorKind} {K R S : Type*}
variable [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
variable {n : ℕ} {D : OperatorField kind K} {A : LinearSystem kind K n}
variable {F : Operator kind R} {E : Operator kind S}

/-- Specializing the constant ratio of the two fundamental matrices gives a
compatible embedding whose image is the subalgebra generated by the ambient solution. -/
private theorem exists_embedding_to_solution_algebra
    (hK : D.IsBaseField) (hS : D.IsExtension E) (hEs : E.IsSimple)
    (hC : ∀ s : S, E.IsConstant s ↔ ∃ c : D.constantSubfield, algebraMap K S (c : K) = s)
    (hR : IsPicardVessiotRing D A F) (Y : GL (Fin n) S) (hY : A.IsFundamental E Y) :
    ∃ f : R →ₐ[K] S, F.Commutes E f ∧ Function.Injective f ∧
      f.range = matrixGeneratedSubalgebra K Y := by
  let C := D.constantSubfield
  have hC' : Operator.HasConstantField (C := C) E := hC
  let : IsAlgClosed C := hK.2
  let : Nontrivial S := hEs.1
  obtain ⟨hR, hFs, Y', hY', hgen⟩ := hR
  let T := S ⊗[K] R
  let iS : S →ₐ[K] T := Algebra.TensorProduct.includeLeft
  let iR : R →ₐ[K] T := Algebra.TensorProduct.includeRight
  let G : Operator kind T := Operator.tensor hS.1 hR.1
  have hleft : E.Commutes G iS := Operator.tensor_commutes_includeLeft hS.1 hR.1
  have hright : F.Commutes G iR := Operator.tensor_commutes_includeRight hS.1 hR.1
  have hleftinj : Function.Injective iS :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (A := S) hR.2
  have hST : E.IsExtension G := ⟨hleft, hleftinj⟩
  have hKT : D.IsExtension G :=
    ⟨Operator.tensor_isAlgebra hS.1 hR.1, hleftinj.comp hS.2⟩
  let : Nontrivial T := hleftinj.nontrivial
  let Yl := GeneralLinearGroup.map iS.toRingHom Y
  let Yr := GeneralLinearGroup.map iR.toRingHom Y'
  obtain ⟨W, hW, _⟩ := LinearSystem.fundamentalRightMultiplier D hK G hKT A Yl Yr
    (fundamental_map hY iS hleft) (fundamental_map hY' iR hright)
  let Z := GeneralLinearGroup.map G.constantSubring.subtype W
  have hratio : Yr = Yl * Z := hW
  let B := matrixGeneratedSubalgebra C Z
  let consts : Subalgebra C T :=
    { G.constantSubring with
      algebraMap_mem' := fun c => (Operator.mem_constantSubring G _).mpr
        (hleft.isConstant (f := iS.toRingHom) ((hC' _).mpr ⟨c, rfl⟩)) }
  have hB : B ≤ consts := matrixGeneratedSubalgebra_map_le W _ (fun x => x.property)
  have hBconst (b : B) : G.IsConstant (b : T) :=
    (Operator.mem_constantSubring G _).mp (hB b.property)
  have hTB : Algebra.adjoin S (B : Set T) = ⊤ := by
    let U := Algebra.adjoin S (B : Set T)
    have hl : matrixGeneratedSubalgebra S Yl ≤ U :=
      matrixGeneratedSubalgebra_map_le Y iS.toRingHom (Subalgebra.algebraMap_mem U)
    have hz : matrixGeneratedSubalgebra S Z ≤ U := by
      obtain ⟨hd, he⟩ := matrixGeneratedSubalgebra_le_iff.mp (le_rfl (a := B))
      exact matrixGeneratedSubalgebra_le_iff.mpr
        ⟨Algebra.subset_adjoin hd, fun i j => Algebra.subset_adjoin (he i j)⟩
    have hr : matrixGeneratedSubalgebra S Yr ≤ U := hratio ▸ matrixGeneratedSubalgebra_mul_le hl hz
    have htop : matrixGeneratedSubalgebra S Yr = ⊤ := by
      have hentries :
          iR '' (Set.range fun ij : Fin n × Fin n => Y'.val ij.1 ij.2) =
            Set.range (fun ij : Fin n × Fin n => Yr.val ij.1 ij.2) :=
        (Set.range_comp' iR _).symm
      have hdet : LinearSystem.determinantInverse Yr = iR (LinearSystem.determinantInverse Y') :=
        determinantInverse_map iR.toRingHom Y'
      unfold matrixGeneratedSubalgebra
      rw [hdet, ← hentries, ← Set.image_insert_eq]
      exact Algebra.TensorProduct.adjoin_one_tmul_image_eq_top _ hgen
    exact top_le_iff.mp (htop ▸ hr)
  let : Algebra.FiniteType C B := B.fg_iff_finiteType.mp (matrixGeneratedSubalgebra_fg Z)
  obtain ⟨p, q, hq, hqB⟩ := exists_constant_evaluation B hEs hC' hST hBconst hTB
  let f : R →ₐ[K] S := (q.restrictScalars K).comp iR
  have hf : F.Commutes E f := hq.comp hright
  have hfi : Function.Injective f := injective_of_simple hFs (f := f.toRingHom) hf
  obtain ⟨Zb, hZb⟩ : ∃ Zb : GL (Fin n) B, GeneralLinearGroup.map B.val.toRingHom Zb = Z :=
    matrix_lift_to_generated (K := C) Z
  let Bk : GL (Fin n) K :=
    GeneralLinearGroup.map D.constantSubfield.subtype (GeneralLinearGroup.map p.toRingHom Zb)
  have hqZ : GeneralLinearGroup.map q.toRingHom Z =
      GeneralLinearGroup.map (algebraMap K S) Bk := by
    rw [← hZb]
    apply Units.ext
    ext i j
    change q ((Zb.val i j : B) : T) = algebraMap C S (p (Zb.val i j))
    exact hqB _
  have hqYl : GeneralLinearGroup.map q.toRingHom Yl = Y := by
    apply Units.ext
    ext i j
    change q (algebraMap S T (Y.val i j)) = Y.val i j
    exact q.commutes (Y.val i j)
  have hfY' : GeneralLinearGroup.map f.toRingHom Y' =
      Y * GeneralLinearGroup.map (algebraMap K S) Bk := by
    change GeneralLinearGroup.map q.toRingHom Yr = _
    rw [hratio, GeneralLinearGroup.map_mul, hqYl, hqZ]
  refine ⟨f, hf, hfi, ?_⟩
  have hmap := matrixGeneratedSubalgebra_map Y' f
  rw [hgen, Algebra.map_top, hfY', matrixGeneratedSubalgebra_mul_base] at hmap
  exact hmap.symm

end Specialization

private def transportOperator {kind : OperatorKind} {K R S : Type*}
    [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (F : Operator kind R) (e : R ≃ₐ[K] S) : Operator kind S := by
  cases kind with
  | differential =>
    let d := e.toRingEquiv.toAddMonoidHom.comp
      (F.toDerivation.toLinearMap.toAddMonoidHom.comp e.symm.toRingEquiv.toAddMonoidHom)
    refine Operator.differential (Derivation.mk' d.toIntLinearMap ?_)
    intro x y
    change e (F.toDerivation (e.symm (x * y))) =
      x • e (F.toDerivation (e.symm y)) + y • e (F.toDerivation (e.symm x))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, AlgEquiv.apply_symm_apply]
  | difference =>
    exact Operator.difference (e.symm.toRingEquiv.trans (F.toRingEquiv.trans e.toRingEquiv))

private theorem transportOperator_commutes {kind : OperatorKind} {K R S : Type*}
    [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (F : Operator kind R) (e : R ≃ₐ[K] S) :
    F.Commutes (transportOperator F e) e := by
  intro x
  cases kind <;>
    change e (F x) = e (F (e.symm (e x))) <;> rw [e.symm_apply_apply]

private theorem simple_of_equiv {kind : OperatorKind} {R S : Type*}
    [CommRing R] [CommRing S] {F : Operator kind R} {E : Operator kind S}
    (hR : F.IsSimple) (e : R ≃+* S) (he : F.Commutes E e) : E.IsSimple := by
  let : Nontrivial R := hR.1
  refine ⟨e.injective.nontrivial, fun I hI => ?_⟩
  have hstable := stable_comap (f := e.toRingHom) he hI
  have hinj := Ideal.comap_injective_of_surjective e.toRingHom e.surjective
  rcases hR.2 _ hstable with h | h
  · exact Or.inl (hinj (h.trans (Ideal.comap_bot_of_injective e.toRingHom e.injective).symm))
  · exact Or.inr (hinj (h.trans Ideal.comap_top.symm))

/-- A fundamental matrix in a simple extension with unchanged constants
generates a Picard–Vessiot ring with the restricted operator. -/
theorem picardVessiot_recognition : Specs.picardVessiotRecognition.{u, v} := by
  intro kind K _ S _ _ n D A E hK hS hEs hC Y hY
  change OperatorField kind K at D
  change LinearSystem kind K n at A
  change Operator kind S at E
  change D.IsBaseField at hK
  change D.IsExtension E at hS
  change E.IsSimple at hEs
  change A.IsFundamental E Y at hY
  obtain ⟨R, _, _, F, _, hR, _, _⟩ := picardVessiot_exists D A hK
  change Operator kind R at F
  have hPV : IsPicardVessiotRing D A F := hR.1
  obtain ⟨f, hf, hfi, hfr⟩ := exists_embedding_to_solution_algebra hK hS hEs hC hPV Y hY
  let T := matrixGeneratedSubalgebra K Y
  change f.range = T at hfr
  let g : R →ₐ[K] T := f.codRestrict T fun r => by
    rw [← hfr]
    exact ⟨r, rfl⟩
  have hgb : Function.Bijective g := by
    refine ⟨fun x y h => hfi (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨r, hr⟩ : (x : S) ∈ f.range := hfr.symm ▸ x.property
    exact ⟨r, Subtype.ext hr⟩
  let e := AlgEquiv.ofBijective g hgb
  let H := transportOperator F e
  have he := transportOperator_commutes F e
  have hinc : H.Commutes E T.val := by
    intro x
    obtain ⟨r, rfl⟩ := e.surjective x
    rw [← he r]
    exact hf r
  have hsimple : H.IsSimple := simple_of_equiv hPV.2.1 e.toRingEquiv he
  have hKT : D.IsExtension H := by
    refine ⟨fun k => Subtype.val_injective ?_, ?_⟩
    · exact (hS.1 k).trans (hinc (algebraMap K T k)).symm
    · let : Nontrivial T := hsimple.1
      exact (algebraMap K T).injective
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin n) T, GeneralLinearGroup.map T.val.toRingHom X = Y :=
    matrix_lift_to_generated (K := K) Y
  have hXfundamental : A.IsFundamental H X :=
    fundamental_of_map T.val Subtype.val_injective hinc X (hX.symm ▸ hY)
  have hXgen : matrixGeneratedSubalgebra K X = ⊤ := by
    apply Subalgebra.map_injective (f := T.val) Subtype.val_injective
    rw [← matrixGeneratedSubalgebra_map X T.val, hX, Algebra.map_top, Subalgebra.range_val]
  exact ⟨H, hinc, ⟨hKT, hsimple, X, hXfundamental, hXgen⟩, X, hX, hXfundamental, hXgen⟩

/-- Picard–Vessiot rings for the same system are isomorphic over the base
by an operator-compatible algebra equivalence. -/
theorem picardVessiot_uniqueness : Specs.picardVessiotUniqueness.{u, v, w} := by
  intro kind K _ R _ S _ _ _ n D A F E hK hR hS
  change OperatorField kind K at D
  change LinearSystem kind K n at A
  change Operator kind R at F
  change Operator kind S at E
  change IsPicardVessiotRing D A F at hR
  change IsPicardVessiotRing D A E at hS
  obtain ⟨hS, hEs, Y, hY, hgen⟩ := hS
  let : Algebra.FiniteType K S := ⟨hgen ▸ matrixGeneratedSubalgebra_fg Y⟩
  have hconstants := Operator.constants_finiteType D E hK hEs hS.1
  have hC : ∀ s : S, E.IsConstant s ↔
      ∃ c : D.constantSubfield, algebraMap K S (c : K) = s := by
    intro s
    constructor
    · intro hs
      obtain ⟨c, hc⟩ := hconstants.surjective ⟨s, (Operator.mem_constantSubring E s).mpr hs⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    · rintro ⟨c, rfl⟩
      exact hS.1.isConstant ((Operator.mem_constantSubfield D _).mp c.property)
  obtain ⟨f, hf, hfi, hrange⟩ := exists_embedding_to_solution_algebra hK hS hEs hC hR Y hY
  have hfs : Function.Surjective f := (AlgHom.range_eq_top f).mp (hrange.trans hgen)
  exact ⟨⟨AlgEquiv.ofBijective f ⟨hfi, hfs⟩, hf⟩⟩

end GaloisFormalization.PV
