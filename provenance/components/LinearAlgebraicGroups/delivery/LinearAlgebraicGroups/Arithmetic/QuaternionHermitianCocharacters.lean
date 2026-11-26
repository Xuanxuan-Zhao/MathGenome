import Specs.LinearAlgebraicGroups.Arithmetic.QuaternionHermitianCocharacters
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.Max

open CategoryTheory MulOpposite AddMonoidAlgebra
open scoped TensorProduct

universe u v w

namespace LinearAlgebraicGroups.QuaternionHermitianCocharacters

noncomputable section

variable {F : Type u} [Field F] {B : Type v} [Ring B] [Algebra F B]
  {ι : Type w} [Fintype ι] [DecidableEq ι]

private def column {C : Type*} (x : ι → C) : Matrix ι Unit C :=
  fun i _ => x i

omit [DecidableEq ι] in
private theorem pairing_mulVec {C : Type*} [Ring C] [Algebra F C] (s : C →ₐ[F] Cᵐᵒᵖ)
    (H g : Matrix ι ι C) (x y : ι → C) :
    pairing s H (g.mulVec x) (g.mulVec y) =
      pairing s ((adjoint s g * H) * g) x y := by
  change ((adjoint s (g * column x) * H) * (g * column y)) () () =
    ((adjoint s (column x) * ((adjoint s g * H) * g)) * column y) () ()
  rw [adjoint_mul]
  simp only [Matrix.mul_assoc]

private theorem pairing_single {C : Type*} [Ring C] [Algebra F C]
    (s : C →ₐ[F] Cᵐᵒᵖ) (H : Matrix ι ι C) (i j : ι) :
    pairing s H (Pi.single i 1) (Pi.single j 1) = H i j := by
  classical
  simp [pairing, Pi.single_apply, apply_ite, ite_mul]

/-- The matrix equation defining the point group is exactly preservation of
the pairing on all pairs of column vectors. -/
theorem mem_isometries_iff {C : Type*} [Ring C] [Algebra F C] (s : C →ₐ[F] Cᵐᵒᵖ)
    (H : Matrix ι ι C) (g : (Matrix ι ι C)ˣ) :
    g ∈ isometries s H ↔ ∀ x y : ι → C,
      pairing s H (g.val.mulVec x) (g.val.mulVec y) = pairing s H x y := by
  change (adjoint s g.val * H) * g.val = H ↔ _
  simp only [pairing_mulVec]
  constructor
  · intro hg x y
    rw [hg]
  · intro hg
    ext i j
    simpa only [pairing_single] using hg (Pi.single i 1) (Pi.single j 1)

omit [DecidableEq ι] in
/-- The Gram pairing agrees with the given right Hermitian pairing in any
chosen basis of the right module. -/
theorem pairing_in_basis {V : Type*} [AddCommGroup V] [Module Bᵐᵒᵖ V]
    (s : B →ₐ[F] Bᵐᵒᵖ) (e : Module.Basis ι Bᵐᵒᵖ V) (h : V → V → B)
    (add_right : ∀ a b c, h a (b + c) = h a b + h a c)
    (smul_right : ∀ a b (d : B), h a (op d • b) = h a b * d)
    (hermitian : ∀ a b, h b a = unop (s (h a b))) (x y : ι → B) :
    h (∑ i, op (x i) • e i) (∑ j, op (y j) • e j) =
      pairing s (fun i j => h (e i) (e j)) x y := by
  have add_left (a b c : V) : h (a + b) c = h a c + h b c := by
    rw [hermitian c (a + b), add_right, map_add, MulOpposite.unop_add, ← hermitian c a, ← hermitian c b]
  have smul_left (a b : V) (d : B) : h (op d • a) b = unop (s d) * h a b := by
    rw [hermitian b (op d • a), smul_right, map_mul, unop_mul, ← hermitian b a]
  have sum_right (a : V) (v : ι → V) : h a (∑ j, v j) = ∑ j, h a (v j) :=
    map_sum (AddMonoidHom.mk' (h a) (add_right a)) _ _
  have sum_left (b : V) (v : ι → V) : h (∑ i, v i) b = ∑ i, h (v i) b :=
    map_sum (AddMonoidHom.mk' (fun a => h a b) (fun a c => add_left a c b)) _ _
  unfold pairing
  rw [sum_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_right, sum_left]
  simp only [smul_left]

private abbrev Laurent (C : Type*) [Ring C] := AddMonoidAlgebra C ℤ

private def monomialUnit : (Laurent F)ˣ where
  val := single 1 1
  inv := single (-1) 1
  val_inv := by rw [single_mul_single]; norm_num [one_def]
  inv_val := by rw [single_mul_single]; norm_num [one_def]

private def evaluateUnit {R : Type*} [CommRing R] [Algebra F R] (t : Rˣ) :
    Laurent F →ₐ[F] R :=
  AddMonoidAlgebra.lift F R ℤ
    { toFun := fun n => ↑(t ^ n.toAdd)
      map_one' := by simp
      map_mul' := by
        intro m n
        change ((t ^ (m.toAdd + n.toAdd) : Rˣ) : R) = _
        rw [zpow_add, Units.val_mul] }

@[simp] private theorem evaluateUnit_monomialUnit {R : Type*} [CommRing R] [Algebra F R]
    (t : Rˣ) : Units.map (evaluateUnit t).toMonoidHom (monomialUnit (F := F)) = t := by
  apply Units.ext
  change evaluateUnit t (single 1 1) = (t : R)
  rw [evaluateUnit, lift_single]
  simp

private def laurentToTensor : Laurent B →ₐ[F] Laurent F ⊗[F] B :=
  AddMonoidAlgebra.liftNCAlgHom Algebra.TensorProduct.includeRight
    ((Algebra.TensorProduct.includeLeft (S := F) (B := B)).toMonoidHom.comp
      (AddMonoidAlgebra.of F ℤ))
    (fun b t => ((Commute.one_right (AddMonoidAlgebra.of F ℤ t)).tmul (R := F)
      (Commute.one_left b)).symm)

set_option backward.isDefEq.respectTransparency false in
@[simp] private theorem laurentToTensor_single (m : ℤ) (b : B) :
    laurentToTensor (single m b) = single m (1 : F) ⊗ₜ[F] b := by
  rw [laurentToTensor, coe_liftNCAlgHom, liftNC_single]
  change ((1 : Laurent F) ⊗ₜ[F] b) * (single m (1 : F) ⊗ₜ[F] (1 : B)) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private def tensorToLaurent : Laurent F ⊗[F] B →ₐ[F] Laurent B :=
  Algebra.TensorProduct.lift (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId F B))
    AddMonoidAlgebra.singleZeroAlgHom
    (fun a b => by
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simpa only [map_add] using hx.add_left hy
      | single m r =>
        rw [AddMonoidAlgebra.mapAlgHom_single]
        change Commute (single m (algebraMap F B r)) (single 0 b)
        exact single_commute_single (AddCommute.zero_right _) (Algebra.commutes r b))

@[simp] private theorem tensorToLaurent_single_tmul (m : ℤ) (r : F) (b : B) :
    tensorToLaurent (single m r ⊗ₜ[F] b) = single m (r • b) := by
  rw [tensorToLaurent, Algebra.TensorProduct.lift_tmul, AddMonoidAlgebra.mapAlgHom_single]
  change single m (algebraMap F B r) * single 0 b = _
  rw [single_mul_single, add_zero, Algebra.smul_def]

private def tensorLaurent : Laurent F ⊗[F] B ≃ₐ[F] Laurent B :=
  AlgEquiv.ofAlgHom tensorToLaurent laurentToTensor
    (by
      apply AlgHom.ext
      intro a
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => rw [map_add, hx, hy, map_add]
      | single m b =>
        simp only [AlgHom.comp_apply, laurentToTensor_single, tensorToLaurent_single_tmul,
          one_smul, AlgHom.id_apply])
    (by
      apply Algebra.TensorProduct.ext'
      intro a b
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, hx, hy, map_add]
      | single m r =>
        simp only [AlgHom.comp_apply, tensorToLaurent_single_tmul, laurentToTensor_single,
          AlgHom.id_apply]
        rw [← TensorProduct.smul_tmul, smul_single, smul_eq_mul, mul_one])

@[simp] private theorem tensorLaurent_single_tmul (m : ℤ) (r : F) (b : B) :
    tensorLaurent (single m r ⊗ₜ[F] b) = single m (r • b) :=
  tensorToLaurent_single_tmul m r b

@[simp] private theorem tensorLaurent_symm_single (m : ℤ) (b : B) :
    (tensorLaurent (F := F)).symm (single m b) = single m (1 : F) ⊗ₜ[F] b :=
  laurentToTensor_single m b

private theorem conjugation_coeff (s : B →ₐ[F] Bᵐᵒᵖ) (x : Laurent F ⊗[F] B) (m : ℤ) :
    (tensorLaurent (unop (extendConjugation s x))).coeff m =
      unop (s ((tensorLaurent x).coeff m)) := by
  obtain ⟨p, rfl⟩ := tensorLaurent.symm.surjective x
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, coeff_add, Finsupp.add_apply]
    rw [MulOpposite.unop_add, map_add, coeff_add, Finsupp.add_apply, hx, hy, MulOpposite.unop_add]
  | single n b =>
    simp only [tensorLaurent_symm_single, extendConjugation_tmul, tensorLaurent_single_tmul,
      one_smul, coeff_single, Finsupp.single_apply]
    split <;> simp

/-- In the coefficient of degree `d+d`, the indicated support condition
leaves only the pair of coefficients of degree `d`. -/
private theorem coeff_mul_at_extreme (x y : Laurent B) (d : ℤ)
    (h : ∀ a b : ℤ, x.coeff a ≠ 0 → y.coeff b ≠ 0 → a + b = d + d → a = d) :
    (x * y).coeff (d + d) = x.coeff d * y.coeff d := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  classical
  unfold Finsupp.sum
  rw [Finset.sum_eq_single d]
  · simp
  · intro a ha had
    have hx : x.coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    have hy : y.coeff (-a + (d + d)) = 0 := by
      by_contra hne
      exact had (h a _ hx hne (by omega))
    simp only [hy, mul_zero]
  · intro hd
    have hx : x.coeff d = 0 := Finsupp.notMem_support_iff.mp hd
    simp only [hx, zero_mul]

private theorem coeff_sandwich (x y : Laurent B) (c : B) (d : ℤ)
    (h : ∀ a b : ℤ, x.coeff a ≠ 0 → y.coeff b ≠ 0 → a + b = d + d → a = d) :
    ((x * single 0 c) * y).coeff (d + d) = x.coeff d * c * y.coeff d := by
  have hs (a : ℤ) : (x * single 0 c).coeff a = x.coeff a * c := coeff_mul_single_zero ..
  rw [coeff_mul_at_extreme _ _ d, hs]
  intro a b ha hb hab
  apply h a b _ hb hab
  intro hx
  exact ha (by rw [hs, hx, zero_mul])

private theorem exists_extreme_degree (S : Finset ℤ) {m : ℤ} (hm : m ∈ S) (hm0 : m ≠ 0) :
    ∃ d ∈ S, d ≠ 0 ∧ ∀ a ∈ S, ∀ b ∈ S, a + b = d + d → a = d := by
  have hS : S.Nonempty := ⟨m, hm⟩
  by_cases hpos : 0 < m
  · let d := S.max' hS
    have hmd : m ≤ d := Finset.le_max' S m hm
    refine ⟨d, Finset.max'_mem S hS, by omega, ?_⟩
    intro a ha b hb hab
    have had : a ≤ d := Finset.le_max' S a ha
    have hbd : b ≤ d := Finset.le_max' S b hb
    omega
  · let d := S.min' hS
    have hdm : d ≤ m := Finset.min'_le S m hm
    refine ⟨d, Finset.min'_mem S hS, by omega, ?_⟩
    intro a ha b hb hab
    have hda : d ≤ a := Finset.min'_le S a ha
    have hdb : d ≤ b := Finset.min'_le S b hb
    omega

omit [DecidableEq ι] in
private theorem coeff_column_norm (s : B →ₐ[F] Bᵐᵒᵖ) (H : Matrix ι ι B)
    (x : ι → Laurent F ⊗[F] B) (d : ℤ)
    (h : ∀ i j (a b : ℤ), (tensorLaurent (x i)).coeff a ≠ 0 →
      (tensorLaurent (x j)).coeff b ≠ 0 → a + b = d + d → a = d) :
    (tensorLaurent (pairing (extendConjugation s) (H.map Algebra.TensorProduct.includeRight)
        x x)).coeff (d + d) =
      pairing s H (fun i => (tensorLaurent (x i)).coeff d)
        (fun i => (tensorLaurent (x i)).coeff d) := by
  unfold pairing
  simp only [Finset.sum_mul, map_sum, map_mul, coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have hH : tensorLaurent (Algebra.TensorProduct.includeRight (A := Laurent F) (H i j)) =
      single 0 (H i j) := by
    change tensorLaurent ((1 : Laurent F) ⊗ₜ[F] H i j) = _
    rw [one_def, tensorLaurent_single_tmul, one_smul]
  rw [Matrix.map_apply, hH, coeff_sandwich, conjugation_coeff]
  intro a b ha hb hab
  apply h i j a b _ hb hab
  intro hzero
  exact ha (by rw [conjugation_coeff, hzero]; simp)

omit [DecidableEq ι] in
private theorem column_is_constant (s : B →ₐ[F] Bᵐᵒᵖ) (H : Matrix ι ι B)
    (anisotropic : ∀ x : ι → B, pairing s H x x = 0 → x = 0)
    (x : ι → Laurent F ⊗[F] B) (c : B)
    (hnorm : pairing (extendConjugation s) (H.map Algebra.TensorProduct.includeRight)
      x x = 1 ⊗ₜ[F] c) (i : ι) :
    x i = (1 : Laurent F) ⊗ₜ[F] (tensorLaurent (x i)).coeff 0 := by
  classical
  let S := Finset.univ.biUnion fun j : ι => (tensorLaurent (x j)).coeff.support
  have memS {j : ι} {a : ℤ} (ha : (tensorLaurent (x j)).coeff a ≠ 0) : a ∈ S :=
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩
  have only_zero (m : ℤ) (hm : m ∈ S) : m = 0 := by
    by_contra hm0
    obtain ⟨d, hd, hd0, hextreme⟩ := exists_extreme_degree S hm hm0
    have hcoeff := coeff_column_norm s H x d
      (fun j k a b ha hb hab => hextreme a (memS ha) b (memS hb) hab)
    have hd2 : d + d ≠ 0 := by omega
    rw [hnorm, one_def, tensorLaurent_single_tmul, one_smul] at hcoeff
    simp only [coeff_single, Finsupp.single_apply, ite_eq_right (Ne.symm hd2)] at hcoeff
    have hz := anisotropic _ hcoeff.symm
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hd
    exact (Finsupp.mem_support_iff.mp hj) (congrFun hz j)
  apply tensorLaurent.injective
  rw [one_def, tensorLaurent_single_tmul, one_smul]
  ext m
  by_cases hm : m = 0
  · subst m
    rw [coeff_single, Finsupp.single_eq_same]
  · rw [coeff_single, Finsupp.single_apply, ite_eq_right (Ne.symm hm)]
    by_contra hne
    exact hm (only_zero m (memS hne))

/-- For an anisotropic pairing every natural cocharacter is trivial.
The proof works over any coefficient algebra with an antiautomorphism. -/
theorem cocharacter_eq_one_of_anisotropic (s : B →ₐ[F] Bᵐᵒᵖ) (H : Matrix ι ι B)
    (anisotropic : ∀ x : ι → B, pairing s H x x = 0 → x = 0)
    (cochar : multiplicativePoints.{u,max v w} F ⟶ isometryPoints s H)
    (R : TestAlgebra F) (t : (multiplicativePoints.{u,max v w} F).obj R) :
    cochar.app R t = 1 := by
  let A := CommAlgCat.of F (Laurent F)
  let T : (multiplicativePoints.{u,max v w} F).obj A := ⟨monomialUnit⟩
  let g := cochar.app A T
  let M := g.val.val
  have hconstant (i j : ι) :
      M i j = (1 : Laurent F) ⊗ₜ[F] (tensorLaurent (M i j)).coeff 0 := by
    apply column_is_constant s H anisotropic (fun i => M i j) (H j j)
    exact congrArg (fun X : Matrix ι ι (Laurent F ⊗[F] B) => X j j) g.property
  have natural_eval (r : (multiplicativePoints.{u,max v w} F).obj R) :
      (isometryPoints s H).map (CommAlgCat.ofHom (evaluateUnit r.down)) g =
        cochar.app R r := by
    let f : A ⟶ R := CommAlgCat.ofHom (evaluateUnit r.down)
    have hf : (multiplicativePoints.{u,max v w} F).map f T = r :=
      ULift.ext (evaluateUnit_monomialUnit r.down)
    have hn := congrArg (fun m : (multiplicativePoints.{u,max v w} F).obj A ⟶
        (isometryPoints s H).obj R => m T) (cochar.naturality f)
    change cochar.app R ((multiplicativePoints.{u,max v w} F).map f T) =
      (isometryPoints s H).map f g at hn
    rw [hf] at hn
    exact hn.symm
  have hone : cochar.app R 1 = 1 := (cochar.app R).hom.map_one
  rw [← hone, ← natural_eval t, ← natural_eval 1]
  apply Subtype.ext
  apply Units.ext
  ext i j
  change changeScalars (evaluateUnit t.down) (M i j) =
    changeScalars (evaluateUnit ((1 : (multiplicativePoints.{u,max v w} F).obj R)).down) (M i j)
  rw [hconstant]
  simp [Algebra.TensorProduct.map_tmul]

/-- A noncentral split cocharacter gives a nonzero isotropic vector over the base field. -/
theorem hermitianIsotropy : Specs.QuaternionHermitianCocharacters.HermitianIsotropy.{u,v,w} := by
  intro F _ B _ _ hB hdegree s hcanonical ι _ _ H hHermitian hNondegenerate hCentral cochar h
  classical
  by_contra hiso
  have anisotropic (x : ι → B) (hx : pairing s.toAlgHom H x x = 0) : x = 0 := by
    by_contra hn
    exact hiso ⟨x, hn, hx⟩
  apply h
  intro R t g
  rw [cocharacter_eq_one_of_anisotropic _ _ anisotropic]
  exact Commute.one_left g

end

end LinearAlgebraicGroups.QuaternionHermitianCocharacters
