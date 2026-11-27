import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTopForms
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KaehlerDifferential Module
open scoped BigOperators

namespace DerivedFormalization.ProjectiveTopForms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.style.haveILetI false

open ProjectiveTwists
open private basicStructureEquiv_value coordinateRatio_value variable_powers_le_nonZeroDivisors
  ratio_constant_value from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists

universe u

private theorem det_add_multiple_columns {I F : Type*} [Fintype I] [DecidableEq I] [CommRing F]
    (A : Matrix I I F) (i : I) (c : I → F) (s : Finset I) (hi : i ∉ s) :
    (Matrix.of fun a b ↦ A a b + (if b ∈ s then c b * A a i else 0)).det = A.det := by
  induction s using Finset.induction_on with
  | empty =>
    congr 1
    ext a b
    simp
  | insert b s hb ih =>
    have hbi : b ≠ i := fun e ↦ hi (e ▸ Finset.mem_insert_self b s)
    have his : i ∉ s := fun h ↦ hi (Finset.mem_insert_of_mem h)
    let B : Matrix I I F := Matrix.of fun a d ↦ A a d + (if d ∈ s then c d * A a i else 0)
    have hB : (Matrix.of fun a d ↦ A a d + (if d ∈ insert b s then c d * A a i else 0)) =
        B.updateCol b (fun a ↦ B a b + c b • B a i) := by
      ext a d
      by_cases h : d = b
      · subst d
        simp [B, Matrix.updateCol, hb, his, smul_eq_mul]
      · simp [B, Matrix.updateCol, h]
    rw [hB, Matrix.det_updateCol_add_smul_self B hbi]
    exact ih his

/-- The determinant after differentiating all ratios with denominator x_i,
using the derivatives indexed by the coordinates other than zero. -/
private theorem det_gradient_ratios {F : Type*} [Field F] {n : ℕ}
    (x : Fin (n + 1) → F) (i : Fin (n + 1)) (hi : x i ≠ 0) :
    (-1 : F) ^ i.val *
      (Matrix.of fun a b : Fin n ↦ (x i)⁻¹ *
        ((if a.succ = i.succAbove b then 1 else 0) -
          (x (i.succAbove b) / x i) * (if a.succ = i then 1 else 0))).det =
        x 0 * (x i)⁻¹ ^ (n + 1) := by
  classical
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.of fun a b ↦ Fin.cases (x b) (fun a' ↦ if a'.succ = b then 1 else 0) a
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.of fun a b ↦ A a b + (if b ∈ Finset.univ.erase i then -(x b / x i) * A a i else 0)
  have hA : A.det = x 0 := by
    rw [Matrix.det_succ_column A 0, Finset.sum_eq_single 0]
    · have hsub : A.submatrix (0 : Fin (n + 1)).succAbove (0 : Fin (n + 1)).succAbove = 1 := by
        ext a b
        simp [A, Matrix.one_apply, eq_comm]
      rw [hsub, Matrix.det_one]
      simp [A]
    · intro j _ hj
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
      simp [A, Fin.succ_ne_zero]
    · simp
  have hB : B.det = A.det :=
    det_add_multiple_columns A i (fun b ↦ -(x b / x i)) _ (by simp)
  have hcofactor :
      B.det = (-1 : F) ^ i.val * x i * (B.submatrix (0 : Fin (n + 1)).succAbove i.succAbove).det := by
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single i]
    · simp [B, A]
    · intro b _ hb
      have hzero : B 0 b = 0 := by
        simp [B, A, hb, div_mul_cancel₀ _ hi]
      rw [hzero, mul_zero, zero_mul]
    · simp
  let C := B.submatrix (0 : Fin (n + 1)).succAbove i.succAbove
  have hC : Matrix.of (fun a b : Fin n ↦ (x i)⁻¹ *
        ((if a.succ = i.succAbove b then 1 else 0) -
          (x (i.succAbove b) / x i) * (if a.succ = i then 1 else 0))) = (x i)⁻¹ • C := by
    ext a b
    simp [C, B, A, sub_eq_add_neg, Fin.succAbove_ne, Matrix.smul_apply]
  rw [hC, Matrix.det_smul, Fintype.card_fin, pow_succ]
  change (-1 : F) ^ i.val * ((x i)⁻¹ ^ n * C.det) = x 0 * ((x i)⁻¹ ^ n * (x i)⁻¹)
  rw [← hA, ← hB, hcofactor]
  change (-1 : F) ^ i.val * ((x i)⁻¹ ^ n * C.det) =
    (-1 : F) ^ i.val * x i * C.det * ((x i)⁻¹ ^ n * (x i)⁻¹)
  calc
    _ = ((-1 : F) ^ i.val * ((x i)⁻¹ ^ n * C.det)) * (x i * (x i)⁻¹) := by
      rw [mul_inv_cancel₀ hi, mul_one]
    _ = _ := by ring

section PolynomialLocalization

variable {K σ R : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [Algebra (MvPolynomial σ K) R] [IsScalarTower K (MvPolynomial σ K) R]

/-- The differentials of the variables are a basis after localizing a polynomial algebra. -/
def localizedDifferentialBasis (S : Submonoid (MvPolynomial σ K)) [IsLocalization S R] :
    Basis σ R Ω[R⁄K] := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := R) S
  exact (KaehlerDifferential.isBaseChange_of_formallyEtale K (MvPolynomial σ K) R).basis
    (KaehlerDifferential.mvPolynomialBasis K σ)

@[simp] theorem localizedDifferentialBasis_apply (S : Submonoid (MvPolynomial σ K))
    [IsLocalization S R] (a : σ) :
    localizedDifferentialBasis (R := R) S a =
      D K R (algebraMap (MvPolynomial σ K) R (MvPolynomial.X a)) := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := R) S
  simp [localizedDifferentialBasis, IsBaseChange.basis_apply]

end PolynomialLocalization


variable (k : Type u) [Field k] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev X := projectiveSpace k n

theorem chart_isAffine (i : Index n) : IsAffineOpen (X := X k n) (chart k n i) :=
  Proj.isAffineOpen_basicOpen (grading k n) _ (variable_degree k n i) (by decide)

/-- The isomorphism from the affine coordinate polynomial ring to chart sections. -/
def polynomialChart (i : Index n) :
    CoordinatePolynomials k n i ≃+* structureSections k n (chart k n i) :=
  (singletonCoordinates k n i).symm.trans
    (Proj.basicOpenIsoAway (grading k n) _ (variable_degree k n i) (by decide)).commRingCatIsoToRingEquiv

@[simp] theorem polynomialChart_X (i : Index n) (a : ChartVariables n i) :
    polynomialChart k n i (MvPolynomial.X a) = chartCoordinate k n i a.val := by
  change (Proj.awayToSection (grading k n) _)
    ((singletonCoordinates k n i).symm (MvPolynomial.X a)) = _
  rw [← singletonCoordinates_ratio k n i a, RingEquiv.symm_apply_apply]
  rfl

theorem chartCoordinate_value (i j : Index n) (x : chart k n i) :
    structureToFunctions k n _ (chartCoordinate k n i j) x =
      fraction k n (variablePolynomial k n j) (variablePolynomial k n i) := by
  exact (basicStructureEquiv_value k n _ (variable_degree k n i) (by decide)
    _ rfl (variable_powers_le_nonZeroDivisors k n i) _ x).trans
    (coordinateRatio_value k n i j)

set_option backward.isDefEq.respectTransparency false in
theorem sectionConstants_chart (i : Index n) (r : k) :
    sectionConstants k n (chart k n i) r =
      (Proj.awayToSection (grading k n) _) (constantInSingleton k n i r) := by
  let U : (X k n).Opens := Proj.basicOpen (grading k n) (variablePolynomial k n i)
  let f := ProjectiveTwists.Expected.structureMapValue k n
  let c : CommRingCat.of k ⟶ CommRingCat.of (SingletonRing k n i) :=
    CommRingCat.ofHom (constantInSingleton k n i)
  let e := Proj.basicOpenIsoSpec (grading k n) (variablePolynomial k n i)
    (variable_degree k n i) (by decide)
  have h : U.ι ≫ f = e.hom ≫ Spec.map c := by
    have he : e.inv ≫ U.ι = Proj.awayι (grading k n) (variablePolynomial k n i)
        (variable_degree k n i) (by decide) := rfl
    rw [← cancel_epi e.inv, ← Category.assoc, he, Iso.inv_hom_id_assoc]
    unfold f ProjectiveTwists.Expected.structureMapValue
    rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  have hU : U.ι.appLE U ⊤ (by rw [U.ι_preimage_self]) = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  have hleft : (U.ι ≫ f).appTop = f.appLE ⊤ U (by rw [Scheme.Hom.preimage_top]; exact le_top) ≫
      U.topIso.inv := by
    rw [← hU, Scheme.Hom.appLE_comp_appLE]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  have hright : (e.hom ≫ Spec.map c).appTop =
      (Spec.map c).appTop ≫ ((Scheme.ΓSpecIso (CommRingCat.of (SingletonRing k n i))).hom ≫
        Proj.awayToSection (grading k n) (variablePolynomial k n i) ≫ U.topIso.inv) := by
    rw [Scheme.Hom.comp_appTop]
    congr 1
    exact Proj.basicOpenToSpec_app_top (grading k n) (variablePolynomial k n i)
  have H := congrArg Scheme.Hom.appTop h
  rw [hleft, hright, ← Category.assoc, ← Category.assoc] at H
  have H' := congrArg (fun a ↦ (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ a)
    ((cancel_mono U.topIso.inv).mp H)
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc] at H'
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom H') r

theorem polynomialChart_C (i : Index n) (r : k) :
    polynomialChart k n i (MvPolynomial.C r) = sectionConstants k n (chart k n i) r := by
  change (Proj.awayToSection (grading k n) _)
    ((singletonCoordinates k n i).symm (MvPolynomial.C r)) = _
  rw [← singletonCoordinates_constant k n i r, RingEquiv.symm_apply_apply, sectionConstants_chart]


private def fullIndex (p : ℕ) : Set.powersetCard (Fin p) p :=
  Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin p)).toOrderEmbedding

private abbrev fullIndexUnique (p : ℕ) : Unique (Set.powersetCard (Fin p) p) :=
  { default := fullIndex p
    uniq := fun s ↦ by
      have h (v : Set.powersetCard (Fin p) p) : v.val = Finset.univ :=
        (Finset.card_eq_iff_eq_univ _).mp (v.prop.trans (Fintype.card_fin p).symm)
      exact Subtype.ext ((h s).trans (h (fullIndex p)).symm) }

/-- The wedge of a basis indexed by Fin n is a basis vector of the top exterior power. -/
private def exteriorBasisEquiv {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : ℕ} (b : Basis (Fin p) R M) : R ≃ₗ[R] ⋀[R]^p M :=
  letI := fullIndexUnique p
  (Basis.singleton (Set.powersetCard (Fin p) p) R).equiv (b.exteriorPower p) (Equiv.refl _)

@[simp] private theorem exteriorBasisEquiv_one {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {p : ℕ} (b : Basis (Fin p) R M) :
    exteriorBasisEquiv b 1 = exteriorPower.ιMulti R p b := by
  letI := fullIndexUnique p
  let s := Basis.singleton (Set.powersetCard (Fin p) p) R
  calc
    exteriorBasisEquiv b 1 = exteriorBasisEquiv b (s (fullIndex p)) := by simp [s]
    _ = b.exteriorPower p (fullIndex p) := Basis.equiv_apply s _ _ _
    _ = _ := by simp [exteriorPower.ιMulti_family, fullIndex]

private def chartToBasicOpen (i : Index n) (r : structureSections k n (chart k n i)) :
    CoordinatePolynomials k n i →ₐ[k] structureSections k n ((X k n).basicOpen r) :=
  (restrictFunctions k n (homOfLE ((X k n).basicOpen_le r)).op).comp
    { toRingHom := (polynomialChart k n i).toRingHom
      commutes' := polynomialChart_C k n i }

private theorem isLocalization_chartToBasicOpen
    (i : Index n) (r : structureSections k n (chart k n i)) :
    letI := (chartToBasicOpen k n i r).toRingHom.toAlgebra
    IsLocalization.Away ((polynomialChart k n i).symm r)
      (structureSections k n ((X k n).basicOpen r)) := by
  letI := (chartToBasicOpen k n i r).toRingHom.toAlgebra
  let f := restrictFunctions k n (homOfLE ((X k n).basicOpen_le r)).op
  letI := f.toRingHom.toAlgebra
  letI : IsLocalization.Away r (structureSections k n ((X k n).basicOpen r)) :=
    (chart_isAffine k n i).isLocalization_basicOpen r
  let e := (polynomialChart k n i).symm
  have H := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers r)
    (structureSections k n ((X k n).basicOpen r)) e
  simpa only [Submonoid.map_powers] using H

private def localizedChartBasis (i : Index n) (r : structureSections k n (chart k n i)) :
    Basis (Fin n) (structureSections k n ((X k n).basicOpen r))
      (Differentials k n ((X k n).basicOpen r)) := by
  let e := chartToBasicOpen k n i r
  letI := e.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom e
  letI := isLocalization_chartToBasicOpen k n i r
  exact (localizedDifferentialBasis (Submonoid.powers ((polynomialChart k n i).symm r))).reindex
    (orderedChartVariables n i).symm.toEquiv

private theorem localizedChartBasis_apply (i : Index n)
    (r : structureSections k n (chart k n i)) (a : Fin n) :
    localizedChartBasis k n i r a =
      D k _ (restrictFunctions k n (homOfLE ((X k n).basicOpen_le r)).op
        (chartCoordinate k n i (i.succAbove a))) := by
  let e := chartToBasicOpen k n i r
  letI := e.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom e
  letI := isLocalization_chartToBasicOpen k n i r
  rw [localizedChartBasis, Basis.reindex_apply, localizedDifferentialBasis_apply]
  change D k _ (restrictFunctions k n (homOfLE ((X k n).basicOpen_le r)).op
    (polynomialChart k n i (MvPolynomial.X (orderedChartVariables n i a)))) = _
  rw [polynomialChart_X]
  rfl

private def restrictedChartForm (i : Index n) {U : OpensOfProj k n} (hU : U ≤ chart k n i) :
    Forms k n n U :=
  restrictForms k n n (homOfLE hU).op (chartForm k n i)

private theorem restrictedChartForm_eq (i : Index n) {U : OpensOfProj k n}
    (hU : U ≤ chart k n i) :
    restrictedChartForm k n i hU =
      (-1 : structureSections k n U) ^ i.val • exteriorPower.ιMulti _ _
        (fun a ↦ D k _ (restrictFunctions k n (homOfLE hU).op
          (chartCoordinate k n i (i.succAbove a)))) := by
  unfold restrictedChartForm chartForm
  rw [map_smulₛₗ, map_pow, map_neg, map_one]
  unfold restrictForms
  rw [exteriorMap_ιMulti]
  congr 2
  funext j
  exact differentialMap_D _ _

/-- The signed wedge generates the top differential module on each principal open of its chart. -/
private theorem exists_smul_restrictedChartForm (i : Index n)
    (r : structureSections k n (chart k n i)) (v : Forms k n n ((X k n).basicOpen r)) :
    ∃ a : structureSections k n ((X k n).basicOpen r),
      v = a • restrictedChartForm k n i ((X k n).basicOpen_le r) := by
  let b := localizedChartBasis k n i r
  let e := exteriorBasisEquiv b
  obtain ⟨a, rfl⟩ := e.surjective v
  rw [← mul_one a, ← smul_eq_mul, map_smul, show e 1 = exteriorPower.ιMulti _ _ b from
    exteriorBasisEquiv_one b]
  let sign : structureSections k n ((X k n).basicOpen r) := (-1) ^ i.val
  have hsign : sign * sign = 1 := by
    simp [sign, ← mul_pow]
  refine ⟨a * sign, ?_⟩
  have hform : restrictedChartForm k n i ((X k n).basicOpen_le r) =
      sign • exteriorPower.ιMulti (structureSections k n ((X k n).basicOpen r)) n b := by
    rw [restrictedChartForm_eq]
    congr 2
    funext j
    exact (localizedChartBasis_apply k n i r j).symm
  rw [hform, smul_smul, mul_assoc, hsign, mul_one]


open private linearMap_ext_differential from MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTopForms

private def asLinear {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module B N] (f : A →+* B) (h : M →ₛₗ[f] N) :
    letI := Module.compHom N f
    M →ₗ[A] N := by
  letI := Module.compHom N f
  exact { toFun := h, map_add' := h.map_add, map_smul' := h.map_smulₛₗ }

private theorem differentialMap_comp_apply {K A B C : Type*}
    [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C] (f : A →ₐ[K] B) (g : B →ₐ[K] C) (v : Ω[A⁄K]) :
    differentialMap (g.comp f) v = differentialMap g (differentialMap f v) := by
  letI := Module.compHom Ω[C⁄K] (g.comp f).toRingHom
  have h : asLinear (g.comp f).toRingHom (differentialMap (g.comp f)) =
      asLinear (g.comp f).toRingHom ((differentialMap g).comp
        (differentialMap f) (σ₁₃ := g.toRingHom.comp f.toRingHom)) := by
    apply linearMap_ext_differential
    intro a
    change differentialMap (g.comp f) (D K A a) = differentialMap g (differentialMap f (D K A a))
    simp only [differentialMap_D, AlgHom.comp_apply]
  exact DFunLike.congr_fun h v

private theorem mem_some_chart (x : Base k n) : ∃ i, x ∈ chart k n i := by
  apply Opens.mem_iSup.mp
  rw [standardCover]
  trivial

private theorem structureToFunctions_restrict {U V : OpensOfProj k n} (h : V ≤ U)
    (a : structureSections k n U) (x : V) :
    structureToFunctions k n _ (restrictFunctions k n (homOfLE h).op a) x =
      structureToFunctions k n _ a ⟨x.val, h x.prop⟩ := rfl

private theorem sectionConstants_value (U : OpensOfProj k n) (x : U) (r : k) :
    structureToFunctions k n U (sectionConstants k n U r) x =
      intoFraction k n (MvPolynomial.C r) := by
  obtain ⟨i, hi⟩ := mem_some_chart k n x.val
  let V := U ⊓ chart k n i
  let y : V := ⟨x.val, x.prop, hi⟩
  let f := restrictFunctions k n (homOfLE (inf_le_left : V ≤ U)).op
  let g := restrictFunctions k n (homOfLE (inf_le_right : V ≤ chart k n i)).op
  have h : f (sectionConstants k n U r) = g (sectionConstants k n (chart k n i) r) :=
    (f.commutes r).trans (g.commutes r).symm
  calc
    _ = structureToFunctions k n V (f (sectionConstants k n U r)) y := rfl
    _ = structureToFunctions k n V (g (sectionConstants k n (chart k n i) r)) y :=
      congrArg (fun z ↦ structureToFunctions k n V z y) h
    _ = structureToFunctions k n (chart k n i) (sectionConstants k n (chart k n i) r) ⟨x.val, hi⟩ :=
      rfl
    _ = _ := by
      rw [sectionConstants_chart]
      exact (basicStructureEquiv_value k n _ (variable_degree k n i) (by decide)
        _ rfl (variable_powers_le_nonZeroDivisors k n i) _ ⟨x.val, hi⟩).trans
        (ratio_constant_value k n i r)

private def evaluateFunctions (U : OpensOfProj k n) (x : U) :
    structureSections k n U →ₐ[k] RationalFunctions k n where
  toRingHom := (Pi.evalRingHom (fun _ : U ↦ RationalFunctions k n) x).comp
    (structureToFunctions k n U)
  commutes' r := sectionConstants_value k n U x r

private abbrev F := RationalFunctions k n

private def homogeneousCoordinate (i : Index n) : F k n :=
  intoFraction k n (variablePolynomial k n i)

private theorem homogeneousCoordinate_ne_zero (i : Index n) :
    homogeneousCoordinate k n i ≠ 0 :=
  intoFraction_ne_zero k n (MvPolynomial.X_ne_zero i)

private def fractionDifferentialBasis : Basis (Index n) (F k n) Ω[F k n⁄k] :=
  localizedDifferentialBasis (nonZeroDivisors (Polynomials k n))

@[simp] private theorem fractionDifferentialBasis_apply (i : Index n) :
    fractionDifferentialBasis k n i = D k _ (homogeneousCoordinate k n i) :=
  localizedDifferentialBasis_apply _ i

private def ambientGradient : Ω[F k n⁄k] →ₗ[F k n] (Fin n → F k n) :=
  LinearMap.pi fun a ↦ (fractionDifferentialBasis k n).coord a.succ

private theorem ambientGradient_D_ratio (i j : Index n) (a : Fin n) :
    ambientGradient k n (D k _ (homogeneousCoordinate k n j / homogeneousCoordinate k n i)) a =
      (homogeneousCoordinate k n i)⁻¹ *
        ((if a.succ = j then 1 else 0) -
          (homogeneousCoordinate k n j / homogeneousCoordinate k n i) *
            (if a.succ = i then 1 else 0)) := by
  rw [Derivation.leibniz_div, ← fractionDifferentialBasis_apply, ← fractionDifferentialBasis_apply]
  change (fractionDifferentialBasis k n).coord a.succ
      ((homogeneousCoordinate k n i)⁻¹ ^ 2 •
        (homogeneousCoordinate k n i • fractionDifferentialBasis k n j -
          homogeneousCoordinate k n j • fractionDifferentialBasis k n i)) = _
  simp only [map_smul, map_sub, Basis.coord_apply, Basis.repr_self_apply, smul_eq_mul]
  simp only [eq_comm (a := j), eq_comm (a := i)]
  field_simp [homogeneousCoordinate_ne_zero]

private def ambientDeterminant :
    AlternatingMap (F k n) Ω[F k n⁄k] (F k n) (Fin n) :=
  (homogeneousCoordinate k n 0)⁻¹ •
    Matrix.detRowAlternating.compLinearMap (ambientGradient k n)

/-- Evaluate a top form at a point in the homogeneous fraction field, normalized by x₀. -/
private def evaluateForms (U : OpensOfProj k n) (x : U) :
    Forms k n n U →ₛₗ[(evaluateFunctions k n U x).toRingHom] F k n := by
  let f := (evaluateFunctions k n U x).toRingHom
  letI := Module.compHom (F k n) f
  let L := exteriorPower.alternatingMapLinearEquiv
    (semilinearAlternating f (differentialMap (evaluateFunctions k n U x))
      (ambientDeterminant k n))
  exact { toFun := L, map_add' := L.map_add, map_smul' := L.map_smul }

@[simp] private theorem evaluateForms_ιMulti (U : OpensOfProj k n) (x : U) (v : Fin n → _) :
    evaluateForms k n U x (exteriorPower.ιMulti _ n v) =
      ambientDeterminant k n (differentialMap (evaluateFunctions k n U x) ∘ v) := by
  letI := Module.compHom (F k n) (evaluateFunctions k n U x).toRingHom
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

private theorem evaluateForms_restrict {U V : OpensOfProj k n} (h : V ≤ U)
    (x : V) (v : Forms k n n U) :
    evaluateForms k n V x (restrictForms k n n (homOfLE h).op v) =
      evaluateForms k n U ⟨x.val, h x.prop⟩ v := by
  let a := restrictFunctions k n (homOfLE h).op
  let b := evaluateFunctions k n V x
  let c := evaluateFunctions k n U ⟨x.val, h x.prop⟩
  have hc : b.comp a = c := by ext z; exact structureToFunctions_restrict k n h z x
  let f : Forms k n n U →ₛₗ[c.toRingHom] F k n :=
    { toFun := fun q ↦ evaluateForms k n V x (restrictForms k n n (homOfLE h).op q)
      map_add' := fun q r ↦ by rw [map_add, map_add]
      map_smul' := fun r q ↦ by
        rw [map_smulₛₗ, map_smulₛₗ]
        exact congrArg (· • _) (DFunLike.congr_fun hc r) }
  letI := Module.compHom (F k n) c.toRingHom
  have H : ∀ (q : Forms k n n U), f q = evaluateForms k n U ⟨x.val, h x.prop⟩ q := by
    have H : asLinear c.toRingHom f = asLinear c.toRingHom (evaluateForms k n U ⟨x.val, h x.prop⟩) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro w
      change evaluateForms k n V x (restrictForms k n n (homOfLE h).op
        (exteriorPower.ιMulti _ n w)) = evaluateForms k n U ⟨x.val, h x.prop⟩
          (exteriorPower.ιMulti _ n w)
      simp only [restrictForms, exteriorMap_ιMulti, evaluateForms_ιMulti]
      congr 1
      funext j
      exact (differentialMap_comp_apply a b (w j)).symm.trans
        (congrArg (fun e ↦ differentialMap e (w j)) hc)
    intro q
    exact DFunLike.congr_fun H q
  exact H v

private theorem evaluateForms_chartForm (i : Index n) (x : chart k n i) :
    evaluateForms k n _ x (chartForm k n i) = frame k n i (canonicalDegree n) := by
  let z := homogeneousCoordinate k n
  have hz := homogeneousCoordinate_ne_zero k n i
  rw [chartForm, map_smulₛₗ, evaluateForms_ιMulti, map_pow, map_neg, map_one]
  have hd : ambientDeterminant k n (differentialMap (evaluateFunctions k n _ x) ∘
      fun a ↦ D k _ (chartCoordinate k n i (i.succAbove a))) =
      (z 0)⁻¹ * (Matrix.of fun a b : Fin n ↦ (z i)⁻¹ *
        ((if a.succ = i.succAbove b then 1 else 0) -
          (z (i.succAbove b) / z i) * (if a.succ = i then 1 else 0))).det := by
    unfold ambientDeterminant
    simp only [smul_apply, AlternatingMap.compLinearMap_apply, smul_eq_mul]
    congr 1
    change Matrix.det _ = _
    rw [← Matrix.det_transpose]
    congr 1
    ext a b
    change ambientGradient k n
      (differentialMap (evaluateFunctions k n _ x) (D k _ (chartCoordinate k n i (i.succAbove b)))) a = _
    rw [differentialMap_D, show evaluateFunctions k n _ x (chartCoordinate k n i (i.succAbove b)) =
      z (i.succAbove b) / z i from chartCoordinate_value k n i _ x]
    exact ambientGradient_D_ratio k n i (i.succAbove b) a
  -- Normalize the cofactor of the homogeneous coordinate matrix.
  -- The determinant is computed using only invertibility of the distinguished coordinate.
  change (-1 : F k n) ^ i.val * (ambientDeterminant k n _) = _
  rw [hd]
  let C : Matrix (Fin n) (Fin n) (F k n) := Matrix.of fun a b ↦ (z i)⁻¹ *
    ((if a.succ = i.succAbove b then 1 else 0) -
      (z (i.succAbove b) / z i) * (if a.succ = i then 1 else 0))
  change (-1 : F k n) ^ i.val * ((z 0)⁻¹ * C.det) = _
  calc
    _ = (z 0)⁻¹ * ((-1 : F k n) ^ i.val * C.det) := by ring
    _ = (z 0)⁻¹ * (z 0 * (z i)⁻¹ ^ (n + 1)) :=
      congrArg ((z 0)⁻¹ * ·) (det_gradient_ratios z i hz)
    _ = _ := by
      rw [← mul_assoc, inv_mul_cancel₀ (homogeneousCoordinate_ne_zero k n 0), one_mul]
      change (z i)⁻¹ ^ (n + 1) = (z i) ^ canonicalDegree n
      rw [show canonicalDegree n = -((n + 1 : ℕ) : ℤ) by simp [canonicalDegree]; omega,
        zpow_neg, zpow_natCast, inv_pow]


private theorem principalNeighborhood (U : OpensOfProj k n) (x : U) :
    ∃ (i : Index n) (r : structureSections k n (chart k n i)),
      (X k n).basicOpen r ≤ U ∧ x.val ∈ (X k n).basicOpen r := by
  obtain ⟨i, hi⟩ := mem_some_chart k n x.val
  obtain ⟨r, hr, hx⟩ := (chart_isAffine k n i).exists_basicOpen_le x hi
  exact ⟨i, r, hr, hx⟩

private theorem evaluateForms_smul_chart {U : OpensOfProj k n} (i : Index n)
    (hU : U ≤ chart k n i) (a : structureSections k n U) (x : U) :
    evaluateForms k n U x (a • restrictedChartForm k n i hU) =
      structureToFunctions k n U a x * frame k n i (canonicalDegree n) := by
  rw [map_smulₛₗ, restrictedChartForm, evaluateForms_restrict, evaluateForms_chartForm]
  rfl

/-- The normalized evaluations are locally coefficients times the prescribed twist frame. -/
private theorem evaluateForms_mem (U : OpensOfProj k n) (v : Forms k n n U) :
    TwistProperty k n (canonicalDegree n) (fun x ↦ evaluateForms k n U x v) := by
  apply (twistPrelocal k n (canonicalDegree n)).sheafify.locality
  intro x
  obtain ⟨i, r, hr, hx⟩ := principalNeighborhood k n U x
  let V := (X k n).basicOpen r
  obtain ⟨a, ha⟩ := exists_smul_restrictedChartForm k n i r
    (restrictForms k n n (homOfLE hr).op v)
  refine ⟨V, hx, homOfLE hr, ?_⟩
  have hval : (fun y : V ↦ evaluateForms k n U ⟨y.val, hr y.prop⟩ v) =
      (fun y : V ↦ structureToFunctions k n V a y * frame k n i (canonicalDegree n)) := by
    funext y
    rw [← evaluateForms_restrict k n hr y, ha]
    exact evaluateForms_smul_chart k n i ((X k n).basicOpen_le r) a y
  change TwistProperty k n (canonicalDegree n)
    (fun y : V ↦ evaluateForms k n U ⟨y.val, hr y.prop⟩ v)
  rw [hval]
  exact frame_mul_mem k n i (canonicalDegree n) ((X k n).basicOpen_le r) a

private def formsToTwistApp (U : OpensOfProj k n) :
    Forms k n n U →ₗ[structureSections k n U] TwistSections k n (canonicalDegree n) U where
  toFun v := ⟨fun x ↦ evaluateForms k n U x v, evaluateForms_mem k n U v⟩
  map_add' v w := Subtype.ext (funext fun x ↦ (evaluateForms k n U x).map_add v w)
  map_smul' a v := Subtype.ext (funext fun x ↦ (evaluateForms k n U x).map_smulₛₗ a v)

private theorem formsToTwistApp_chart {U : OpensOfProj k n} (i : Index n)
    (hU : U ≤ chart k n i) (a : structureSections k n U) :
    formsToTwistApp k n U (a • restrictedChartForm k n i hU) =
      frameEquiv k n i (canonicalDegree n) hU a := by
  apply Subtype.ext
  funext x
  exact evaluateForms_smul_chart k n i hU a x

/-- The comparison on the differential presheaf, given by the normalized determinant. -/
def formsToTwistPresheaf : formsPresheaf k n n ⟶ (twistingSheaf k n (canonicalDegree n)).val where
  app U := ModuleCat.ofHom (formsToTwistApp k n U.unop)
  naturality f := by
    apply ModuleCat.Hom.ext
    apply DFunLike.ext
    intro w
    apply Subtype.ext
    funext x
    exact evaluateForms_restrict k n f.unop.le x w

private theorem formsToTwistApp_principal_injective (i : Index n)
    (r : structureSections k n (chart k n i)) :
    Function.Injective (formsToTwistApp k n ((X k n).basicOpen r)) := by
  intro s t h
  obtain ⟨a, rfl⟩ := exists_smul_restrictedChartForm k n i r s
  obtain ⟨b, rfl⟩ := exists_smul_restrictedChartForm k n i r t
  rw [formsToTwistApp_chart, formsToTwistApp_chart] at h
  rw [(frameEquiv k n i (canonicalDegree n) ((X k n).basicOpen_le r)).injective h]

private abbrev topology := Opens.grothendieckTopology (Base k n)

private abbrev underlyingComparison :=
  (PresheafOfModules.toPresheaf (structurePresheaf k n)).map (formsToTwistPresheaf k n)

private theorem formsToTwistLocallyInjective :
    Presheaf.IsLocallyInjective (topology k n) (underlyingComparison k n) := by
  constructor
  intro U s t h x hx
  obtain ⟨i, r, hr, hxV⟩ := principalNeighborhood k n U.unop ⟨x, hx⟩
  refine ⟨(X k n).basicOpen r, homOfLE hr, ?_, hxV⟩
  apply formsToTwistApp_principal_injective k n i r
  have h₁ := PresheafOfModules.naturality_apply (formsToTwistPresheaf k n) (homOfLE hr).op s
  have h₂ := PresheafOfModules.naturality_apply (formsToTwistPresheaf k n) (homOfLE hr).op t
  exact h₁.trans ((congrArg ((twistingSheaf k n (canonicalDegree n)).val.map
    (homOfLE hr).op) h).trans h₂.symm)

private theorem formsToTwistLocallySurjective :
    Presheaf.IsLocallySurjective (topology k n) (underlyingComparison k n) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff (underlyingComparison k n)).mpr
  intro U t x hx
  obtain ⟨i, hi⟩ := mem_some_chart k n x
  let V := U ⊓ chart k n i
  let tV := restriction k n (inf_le_left : V ≤ U) (canonicalDegree n) t
  let e := frameEquiv k n i (canonicalDegree n) (inf_le_right : V ≤ chart k n i)
  refine ⟨V, inf_le_left, ⟨e.symm tV • restrictedChartForm k n i inf_le_right, ?_⟩, ⟨hx, hi⟩⟩
  change formsToTwistApp k n V (e.symm tV • restrictedChartForm k n i inf_le_right) = tV
  rw [formsToTwistApp_chart]
  exact e.apply_symm_apply tV

/-- The comparison after passing to the sheaf of top forms. -/
def topFormsHom : formsSheaf k n n ⟶ twistingSheaf k n (canonicalDegree n) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (structurePresheaf k n))).symm
    (formsToTwistPresheaf k n)

private theorem topFormsHom_fac :
    CategoryTheory.toSheafify (topology k n) (formsPresheaf k n n).presheaf ≫
      (PresheafOfModules.toPresheaf (structurePresheaf k n)).map (topFormsHom k n).val =
        underlyingComparison k n := by
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def (𝟙 (structurePresheaf k n))]
  unfold topFormsHom underlyingComparison
  rw [Equiv.apply_symm_apply]

private theorem topFormsHom_app (U : OpensOfProj k n) (v : Forms k n n U) :
    (topFormsHom k n).val.app (op U) ((toFormsSheaf k n n).app (op U) v) =
      formsToTwistApp k n U v := by
  have h := topFormsHom_fac k n
  have hu := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (structurePresheaf k n)) (𝟙 (formsSheaf k n n))
  let F := PresheafOfModules.toPresheaf (structurePresheaf k n)
  change F.map (toFormsSheaf k n n) =
    CategoryTheory.toSheafify (topology k n) (formsPresheaf k n n).presheaf ≫
      F.map (𝟙 (formsSheaf k n n).val) at hu
  rw [F.map_id] at hu
  have hunit : F.map (toFormsSheaf k n n) =
      CategoryTheory.toSheafify (topology k n) (formsPresheaf k n n).presheaf :=
    hu.trans (Category.comp_id (CategoryTheory.toSheafify (topology k n)
      (formsPresheaf k n n).presheaf))
  rw [← hunit, ← Functor.map_comp] at h
  have h' : toFormsSheaf k n n ≫ (topFormsHom k n).val = formsToTwistPresheaf k n :=
    F.map_injective h
  have he := congrArg (fun f : formsPresheaf k n n ⟶
      (twistingSheaf k n (canonicalDegree n)).val ↦ f.app (op U) v) h'
  exact he

private theorem isIso_topFormsHom : IsIso (topFormsHom k n) := by
  let a := CategoryTheory.toSheafify (topology k n) (formsPresheaf k n n).presheaf
  let b := (PresheafOfModules.toPresheaf (structurePresheaf k n)).map (topFormsHom k n).val
  letI : Presheaf.IsLocallySurjective (topology k n) a :=
    ((topology k n).W_toSheafify (formsPresheaf k n n).presheaf).isLocallySurjective
  letI := formsToTwistLocallyInjective k n
  letI := formsToTwistLocallySurjective k n
  have hb₁ : Presheaf.IsLocallyInjective (topology k n) b :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (topology k n) (underlyingComparison k n) (topFormsHom_fac k n)
  have hb₂ : Presheaf.IsLocallySurjective (topology k n) b :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (topology k n) (topFormsHom_fac k n)
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hb₁, hb₂⟩

/-- The sheaf isomorphism between top forms and the canonical twist. -/
def topFormsIso : formsSheaf k n n ≅ twistingSheaf k n (canonicalDegree n) :=
  letI := isIso_topFormsHom k n
  asIso (topFormsHom k n)

theorem topFormsOnPrincipalOpen : ProjectiveTopForms.Expected.principalOpen.{u} := by
  intro k _ n _ i r
  let U := (X k n).basicOpen r
  let e := (SheafOfModules.evaluation (moduleRingSheaf k n) (op U)).mapIso (topFormsIso k n)
  have hApp : Function.Bijective (formsToTwistApp k n U) := by
    refine ⟨formsToTwistApp_principal_injective k n i r, ?_⟩
    intro s
    let h := (X k n).basicOpen_le r
    let f := frameEquiv k n i (canonicalDegree n) h
    refine ⟨f.symm s • restrictedChartForm k n i h, ?_⟩
    rw [formsToTwistApp_chart]
    exact f.apply_symm_apply s
  have hf : e.toLinearEquiv ∘
      (fun v : Forms k n n U ↦ (toFormsSheaf k n n).app (op U) v) =
        formsToTwistApp k n U := funext (topFormsHom_app k n U)
  apply (e.toLinearEquiv.bijective.of_comp_iff' _).mp
  rw [hf]
  exact hApp

theorem topFormsIso_signedGenerator (i : Index n) (x : chart k n i) :
    ((topFormsIso k n).hom.val.app (op (chart k n i)) (signedGenerator k n i)).val x =
      frame k n i (canonicalDegree n) := by
  change ((topFormsHom k n).val.app (op (chart k n i))
    ((toFormsSheaf k n n).app (op (chart k n i)) (chartForm k n i))).val x = _
  rw [topFormsHom_app]
  exact evaluateForms_chartForm k n i x

theorem topFormsComparison : ProjectiveTopForms.Expected.comparison.{u} := by
  intro k _ n _
  refine ⟨twistingSheaf k n (canonicalDegree n), topFormsIso k n, fun _ ↦ Equiv.refl _, ?_⟩
  exact ⟨by intros; rfl, by intros; rfl, by intros; rfl, topFormsIso_signedGenerator k n⟩

private theorem restrictedCoordinate_value (i j : Index n) {U : OpensOfProj k n}
    (hU : U ≤ chart k n i) (x : U) :
    structureToFunctions k n U (restrictFunctions k n (homOfLE hU).op
      (chartCoordinate k n i j)) x =
        homogeneousCoordinate k n j / homogeneousCoordinate k n i :=
  chartCoordinate_value k n i j ⟨x.val, hU x.prop⟩

private def overlapRatio (i j : Index n) :
    Units (structureSections k n (chart k n i ⊓ chart k n j)) where
  val := restrictFunctions k n (homOfLE inf_le_left).op (chartCoordinate k n i j)
  inv := restrictFunctions k n (homOfLE inf_le_right).op (chartCoordinate k n j i)
  val_inv := by
    apply structureToFunctions_injective
    funext x
    rw [map_mul, Pi.mul_apply, map_one, Pi.one_apply, restrictedCoordinate_value,
      restrictedCoordinate_value, div_mul_div_comm, mul_comm (homogeneousCoordinate k n j)]
    exact div_self (mul_ne_zero (homogeneousCoordinate_ne_zero k n i)
      (homogeneousCoordinate_ne_zero k n j))
  inv_val := by
    apply structureToFunctions_injective
    funext x
    rw [map_mul, Pi.mul_apply, map_one, Pi.one_apply, restrictedCoordinate_value,
      restrictedCoordinate_value, div_mul_div_comm, mul_comm (homogeneousCoordinate k n i)]
    exact div_self (mul_ne_zero (homogeneousCoordinate_ne_zero k n j)
      (homogeneousCoordinate_ne_zero k n i))

private theorem overlapRatio_zpow (i j : Index n) (m : ℤ) (x : ↥(chart k n i ⊓ chart k n j)) :
    structureToFunctions k n _ (↑(overlapRatio k n i j ^ m) : structureSections k n _) x =
      (homogeneousCoordinate k n j / homogeneousCoordinate k n i) ^ m := by
  let e := evaluateFunctions k n (chart k n i ⊓ chart k n j) x
  change (↑(Units.map e.toRingHom.toMonoidHom (overlapRatio k n i j ^ m)) : F k n) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  exact congrArg (· ^ m) (restrictedCoordinate_value k n i j inf_le_left x)

theorem topFormsTransition : ProjectiveTopForms.Expected.transition.{u} := by
  intro k _ n _ i j
  let U := chart k n i ⊓ chart k n j
  let a : op (chart k n i) ⟶ op U := (homOfLE inf_le_left).op
  let b : op (chart k n j) ⟶ op U := (homOfLE inf_le_right).op
  let m := canonicalDegree n
  let v := overlapRatio k n i j
  let e := (SheafOfModules.evaluation (moduleRingSheaf k n) (op U)).mapIso (topFormsIso k n)
  refine ⟨v, rfl, ?_⟩
  change (formsSheaf k n n).val.map b (signedGenerator k n j) =
    (↑(v ^ m) : structureSections k n U) •
    (show (formsSheaf k n n).val.obj (op U) from
      (formsSheaf k n n).val.map a (signedGenerator k n i))
  apply e.toLinearEquiv.injective
  have h₁ := PresheafOfModules.naturality_apply (topFormsIso k n).hom.val b (signedGenerator k n j)
  have h₂ := PresheafOfModules.naturality_apply (topFormsIso k n).hom.val a (signedGenerator k n i)
  rw [map_smul]
  change (topFormsIso k n).hom.val.app (op U) _ =
    (↑(v ^ m) : structureSections k n U) • (topFormsIso k n).hom.val.app (op U) _
  rw [h₁, h₂]
  apply Subtype.ext
  funext x
  change ((topFormsIso k n).hom.val.app (op (chart k n j))
    (signedGenerator k n j)).val ⟨x.val, x.prop.2⟩ =
      structureToFunctions k n U (↑(v ^ m)) x *
      ((topFormsIso k n).hom.val.app (op (chart k n i))
        (signedGenerator k n i)).val ⟨x.val, x.prop.1⟩
  rw [topFormsIso_signedGenerator, topFormsIso_signedGenerator, overlapRatio_zpow, div_zpow]
  change homogeneousCoordinate k n j ^ m =
    (homogeneousCoordinate k n j ^ m / homogeneousCoordinate k n i ^ m) *
      homogeneousCoordinate k n i ^ m
  rw [div_mul_cancel₀ _ (zpow_ne_zero _ (homogeneousCoordinate_ne_zero k n i))]

end DerivedFormalization.ProjectiveTopForms
