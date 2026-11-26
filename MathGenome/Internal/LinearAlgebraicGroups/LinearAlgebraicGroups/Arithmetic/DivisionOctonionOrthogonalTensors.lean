import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.Topology.Algebra.MvPolynomial
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import Mathlib.LinearAlgebra.Charpoly.BaseChange

open scoped TensorProduct MatrixGroups RestrictedProduct
open Matrix

namespace LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
open Specs.DivisionOctonionOrthogonalTensors
open Composition.Specification (normBaseChange)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

noncomputable section

private theorem matrixDet_eq_one {L I : Type*} [CommRing L] [Fintype I] [DecidableEq I]
    (M : GL I L) (h : M.val.det = 1) : M.det = 1 :=
  Units.ext h

private theorem matrixCoordinates_value {L V I : Type*} [CommRing L] [AddCommGroup V]
    [Module L V] [Fintype I] [DecidableEq I] (b : Module.Basis I L V) (f : V ≃ₗ[L] V) :
    (matrixCoordinates b f).val = LinearMap.toMatrix b b f.toLinearMap := rfl

theorem matrixCoordinateComparison : MatrixCoordinateComparison := by
  intro L V I _ _ _ _ _ b f x
  have h (y : V) : (matrixCoordinates b f).val.mulVec (b.equivFun y) = b.equivFun (f y) := by
    change ((Matrix.GeneralLinearGroup.toLin (matrixCoordinates b f)).val) (b.equivFun y) = _
    simp [matrixCoordinates, LinearMap.GeneralLinearGroup.generalLinearEquiv]
  refine ⟨h x, ?_⟩
  rw [matrixCoordinates_value, LinearMap.det_toMatrix b]

theorem rightMultiplicationCentralizer : RightMultiplicationCentralizer := by
  intro k D I _ _ _ b f
  constructor
  · intro h
    have hf : ∀ x, f x = f 1 * x := by
      have heq : f.toLinearMap = LinearMap.mul k D (f 1) := by
        apply b.ext
        intro j
        simpa using h j 1
      exact fun x => DFunLike.congr_fun heq x
    let y := f.symm 1
    have hxy : f 1 * y = 1 := (hf y).symm.trans (f.apply_symm_apply 1)
    have hyx : y * f 1 = 1 := by
      apply f.injective
      calc
        f (y * f 1) = f 1 * (y * f 1) := hf _
        _ = f 1 := by rw [← mul_assoc, hxy, one_mul]
    exact ⟨⟨f 1, y, hxy, hyx⟩, hf⟩
  · rintro ⟨u, hu⟩ i x
    rw [hu, hu, mul_assoc]

theorem divisionNormPolynomial : DivisionNormPolynomial := by
  intro k D I _ _ _ _ hD b
  open RM03.CSA in
  refine ⟨degree_pos hD, genericReducedNorm_homogeneous hD b, ?_⟩
  intro x hx
  have hA : RM03.CSA.IsCentralSimple k D := hD
  change (RM03.CSA.genericReducedNorm hA b).eval x ≠ 0
  rw [RM03.CSA.genericReducedNorm_eval, RM03.CSA.reducedNorm_ne_zero_iff_isUnit]
  rw [← b.equivFun_symm_apply]
  exact isUnit_iff_ne_zero.mpr (fun h => hx (b.equivFun.symm.injective (h.trans (map_zero _).symm)))

private theorem det_matrixLeftMul {L I : Type*} [Field L] [Fintype I] [DecidableEq I]
    (X : Matrix I I L) :
    LinearMap.det (LinearMap.mul L (Matrix I I L) X) = X.det ^ Fintype.card I := by
  let e : Matrix I I L ≃ₗ[L] (I → I → L) :=
    (Matrix.transposeLinearEquiv I I L L).trans (Matrix.ofLinearEquiv L).symm
  let f := LinearMap.mul L (Matrix I I L) X
  have h :
      e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap =
        LinearMap.pi (fun i : I => X.mulVecLin ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext
    intro y
    funext i j
    rfl
  rw [← LinearMap.det_conj f e, h, LinearMap.det_pi]
  simp [← Matrix.toLin'_apply', LinearMap.det_toLin']

private theorem det_leftMul {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (hA : RM03.CSA.IsCentralSimple k A) (a : A) :
    LinearMap.det (LinearMap.mul k A a) = RM03.CSA.reducedNorm hA a ^ RM03.CSA.degree k A := by
  classical
  let : Module.Finite k A := hA.2.2
  let L := AlgebraicClosure k
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hA
  let f := LinearMap.mul k A a
  have hbase : f.baseChange L = LinearMap.mul L (L ⊗[k] A) (1 ⊗ₜ[k] a) := by
    apply LinearMap.ext
    intro x
    exact TensorProduct.inductionOn x
      (fun z x => by simp [f, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul])
      (fun x y hx hy => by simp only [map_add, hx, hy])
  have hconj : e.toLinearEquiv.toLinearMap ∘ₗ f.baseChange L ∘ₗ
      e.toLinearEquiv.symm.toLinearMap =
      LinearMap.mul L _ (e ((1 : L) ⊗ₜ[k] a)) := by
    rw [hbase]
    apply LinearMap.ext
    intro y
    simp
  change f.det = _
  apply (algebraMap k L).injective
  rw [← (LinearMap.det_baseChange (A := L) f), ← LinearMap.det_conj (f.baseChange L) e.toLinearEquiv,
    hconj, det_matrixLeftMul, Fintype.card_fin, map_pow, RM03.CSA.reducedNorm_map hA a e]

private theorem normAt_eq {k L D I : Type*} [Field k] [Field L] [Algebra k L]
    [Ring D] [Algebra k D] [Fintype I] (h : RM03.CSA.IsCentralSimple k D)
    (b : Module.Basis I k D) (x : L ⊗[k] D) :
    normAt h b x =
      RM03.CSA.reducedNorm (RM03.CSA.isCentralSimple_baseChange h) x := by
  change (RM03.CSA.genericReducedNorm h b).eval₂ (algebraMap k L) ((b.baseChange L).repr x) = _
  rw [RM03.CSA.genericReducedNorm_eval₂]
  congr 1
  simpa only [Module.Basis.baseChange_apply] using (b.baseChange L).sum_repr x

private theorem det_leftMul_extension {k L D I : Type*} [Field k] [Field L] [Algebra k L]
    [Ring D] [Algebra k D] [Fintype I] (hD : RM03.CSA.IsCentralSimple k D)
    (b : Module.Basis I k D) (x : L ⊗[k] D) :
    (LinearMap.mul L _ x).det = normAt hD b x ^ _root_.Specs.RM03.CSA.degree k D := by
  rw [det_leftMul (RM03.CSA.isCentralSimple_baseChange hD), ← normAt_eq hD b]
  congr 1
  change (Module.finrank L (L ⊗[k] D)).sqrt = (Module.finrank k D).sqrt
  rw [RM03.CSA.finrank_baseChange hD]

private theorem divisionMatrix_mem_range {k L D I : Type*} [Field k] [Field L] [Algebra k L]
    [Ring D] [Algebra k D] [Fintype I] [DecidableEq I] (b : Module.Basis I k D) (M : GL I L) :
    let c := b.baseChange L
    let f := (matrixCoordinates c).symm M
    M ∈ (divisionMatrixHom (L := L) b).range ↔
      ∀ i x, f (x * c i) = f x * c i := by
  let c := b.baseChange L
  let f := (matrixCoordinates c).symm M
  have hf : matrixCoordinates c f = M := (matrixCoordinates c).apply_symm_apply M
  change (∃ u, matrixCoordinates c (leftUnit u) = M) ↔ ∀ i x, f (x * c i) = f x * c i
  rw [rightMultiplicationCentralizer c f]
  constructor
  · rintro ⟨u, hu⟩
    have h : f = leftUnit u := (matrixCoordinates c).injective (hf.trans hu.symm)
    exact ⟨u, fun x => DFunLike.congr_fun h x⟩
  · rintro ⟨u, hu⟩
    have h : leftUnit u = f := LinearEquiv.ext fun x => (hu x).symm
    exact ⟨u, (congrArg (matrixCoordinates c) h).trans hf⟩

theorem divisionExtensionModel : DivisionExtensionModel := by
  intro k L D I _ _ _ _ _ _ _ hD b
  let c := b.baseChange L
  let ρ := divisionMatrixHom (L := L) b
  have hρ (u : (L ⊗[k] D)ˣ) : ρ u = matrixCoordinates c (leftUnit u) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v h
    apply Units.ext
    have hl := (matrixCoordinates c).injective (show matrixCoordinates c (leftUnit u) =
      matrixCoordinates c (leftUnit v) from h)
    simpa [leftUnit] using DFunLike.congr_fun hl 1
  · intro u x
    exact (matrixCoordinateComparison c (leftUnit u) x).1
  · intro M
    simpa only [MonoidHom.mem_range, Module.Basis.baseChange_apply] using
      divisionMatrix_mem_range b M
  · intro u
    rw [hρ, (matrixCoordinateComparison c _ 0).2]
    exact det_leftMul_extension hD b u.val
  · intro u hu
    have hdet : (ρ u).val.det = 1 := by
      rw [hρ, (matrixCoordinateComparison c _ 0).2]
      change LinearMap.det (LinearMap.mul L _ u.val) = 1
      rw [det_leftMul_extension hD b, hu, one_pow]
    refine ⟨Units.ext hdet, ?_⟩
    intro x
    have h := (matrixCoordinateComparison c (leftUnit u) (c.equivFun.symm x)).1
    rw [LinearEquiv.apply_symm_apply] at h
    rw [hρ, h]
    have heval (y : L ⊗[k] D) : (_root_.Specs.RM03.CSA.genericReducedNorm hD b).eval₂
        (algebraMap k L) (c.equivFun y) = normAt hD b y := rfl
    nth_rw 2 [← c.equivFun.apply_symm_apply x]
    rw [heval, heval]
    change normAt hD b (u.val * c.equivFun.symm x) =
      normAt hD b (c.equivFun.symm x)
    rw [normAt_eq hD b (u.val * c.equivFun.symm x), normAt_eq hD b (c.equivFun.symm x),
      RM03.CSA.reducedNorm_mul, ← normAt_eq hD b u.val, hu, one_mul]

theorem scalarOperatorComparison : ScalarOperatorComparison := by
  intro k K V S _ _ _ _ _ _ _ c f
  constructor
  · intro h
    have he (a : K) (x : V) : f (a • x) = a • f x := by
      let F : K →ₗ[k] V := f.toLinearMap.comp ((LinearMap.id : K →ₗ[k] K).smulRight x)
      let G : K →ₗ[k] V := (LinearMap.id : K →ₗ[k] K).smulRight (f x)
      exact DFunLike.congr_fun (c.ext (show ∀ s, F (c s) = G (c s) from fun s => h s x)) a
    let g : V ≃ₗ[K] V :=
      { f.toAddEquiv with map_smul' := fun a x => he a x }
    exact ⟨g, fun _ => rfl⟩
  · rintro ⟨g, hg⟩ s x
    rw [← hg (c s • x), ← hg x, map_smul]

private theorem quadraticPolynomial_eval {k V I : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Fintype I] [DecidableEq I] [LinearOrder I]
    (b : Module.Basis I k V) (q : QuadraticForm k V) (x : I → k) :
    (quadraticPolynomial b q).eval x = q (b.equivFun.symm x) := by
  have he := DFunLike.congr_fun (q.toQuadraticMap_toBilin b) (b.equivFun.symm x)
  rw [← he]
  simp only [quadraticPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Module.Basis.equivFun_symm_apply,
    LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

theorem quadraticPolynomialComparison : QuadraticPolynomialComparison := by
  intro k V I _ _ _ _ _ _ b q
  constructor
  · apply MvPolynomial.IsHomogeneous.sum
    intro i _
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((MvPolynomial.isHomogeneous_X k i).mul
      (MvPolynomial.isHomogeneous_X k j)).C_mul _
  · intro L _ _ x
    let f := q.toBilin b
    let g := LinearMap.BilinForm.baseChange L f
    have hg : g.toQuadraticMap = normBaseChange L q := by
      apply baseChange_ext
      intro v
      simp only [g, LinearMap.BilinMap.toQuadraticMap_apply,
        LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, f,
        Composition.normBaseChange_tmul, mul_one, one_mul]
      exact congrArg (algebraMap k L) (DFunLike.congr_fun (q.toQuadraticMap_toBilin b) v)
    rw [← hg]
    simp only [quadraticPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
      Module.Basis.equivFun_symm_apply, LinearMap.BilinMap.toQuadraticMap_apply,
      LinearMap.map_sum₂]
    simp only [map_sum, map_smul, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [g, f, LinearMap.BilinForm.baseChange_tmul, smul_eq_mul, Algebra.smul_def]
    ring

private theorem basisVolume_map {L V I : Type*} [Field L] [AddCommGroup V] [Module L V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I L V) (f : V ≃ₗ[L] V) (x : I → V) :
    basisVolume b (fun i => f (x i)) = (matrixCoordinates b f).val.det * basisVolume b x := by
  rw [(matrixCoordinateComparison b f 0).2]
  exact b.det_comp f.toLinearMap x

private theorem basisVolume_basis {L V I : Type*} [Field L] [AddCommGroup V] [Module L V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I L V) :
    basisVolume b b = 1 :=
  b.det_self

theorem volumeBaseChangeComparison : VolumeBaseChangeComparison := by
  intro k L V I _ _ _ _ _ _ _ b x
  rw [basisVolume, Module.Basis.det_apply, basisVolume, Module.Basis.det_apply,
    RingHom.map_det]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

theorem quadraticVolumeStabilizer : QuadraticVolumeStabilizer := by
  intro L V I _ _ _ _ _ b q f
  refine and_congr_right fun _ => ⟨fun hv => ?_, fun hd x => ?_⟩
  · apply Units.ext
    change (matrixCoordinates b f).val.det = 1
    simpa only [basisVolume_basis, mul_one] using (basisVolume_map b f b).symm.trans (hv b)
  · have hd' : (matrixCoordinates b f).val.det = 1 := congrArg Units.val hd
    rw [basisVolume_map, hd', one_mul]

universe u v w

theorem orthogonalPolynomialModel : OrthogonalPolynomialModel.{u,v,w} := by
  intro k V _ _ _ _ n b q _ _ ha
  refine ⟨(quadraticPolynomialComparison.{u,v,0,w} b q).1, ?_, ?_⟩
  · intro x hx hz
    exact hx (b.equivFun.symm.injective ((ha _ ((quadraticPolynomial_eval b q x).symm.trans hz)).trans
      (map_zero _).symm))
  · intro L _ _ f
    dsimp only
    intro hf hv
    refine ⟨((quadraticVolumeStabilizer _ _ f).mp ⟨hf, hv⟩).2, ?_⟩
    intro x
    rw [(quadraticPolynomialComparison b q).2, (quadraticPolynomialComparison b q).2]
    have he := (matrixCoordinateComparison (b.baseChange L) f
      ((b.baseChange L).equivFun.symm x)).1
    rw [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hf]

section Octonions

open LinearAlgebraicGroups.Composition
open Composition.Specification (OctonionNormConditions)
open Composition.PeirceSpecification (SplitAutomorphism SplitEvaluationOver)
open private octonion_norm_comp_equiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.Adjoints
open private splitAutomorphismRing_connected octonion_splits_over_algebraically_closed
  baseChange_mul_of_linearEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
open private zornBasis map_zornBasis pairedFunctions_mapCoordinates from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.PeirceFrames

private theorem determinant_square_of_perfect_isometry {R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
    (p : LinearMap.BilinForm R W) [p.IsPerfPair]
    (f : W ≃ₗ[R] W) (hp : ∀ x y, p (f x) (f y) = p x y) :
    f.toLinearMap.det ^ 2 = 1 := by
  let e := p.toPerfPair
  have h : e.toLinearMap ∘ₗ f.toLinearMap ∘ₗ e.symm.toLinearMap =
      f.symm.toLinearMap.dualMap := by
    apply LinearMap.ext₂
    intro x y
    change p (f (e.symm x)) y = x (f.symm y)
    calc
      p (f (e.symm x)) y = p (f (e.symm x)) (f (f.symm y)) := by rw [f.apply_symm_apply]
      _ = p (e.symm x) (f.symm y) := hp _ _
      _ = x (f.symm y) := DFunLike.congr_fun (e.apply_symm_apply x) _
  have hd := congrArg LinearMap.det h
  rw [LinearMap.det_conj, LinearMap.det_dualMap] at hd
  rw [sq]
  nth_rw 1 [hd]
  rw [← LinearMap.det_comp]
  rw [show f.symm.toLinearMap ∘ₗ f.toLinearMap = LinearMap.id from
    LinearMap.ext (fun x => f.symm_apply_apply x), LinearMap.det_id]

private theorem splitOctonion_determinant_square {R : Type*} [CommRing R]
    (g : SplitAutomorphism R) : g.val.toLinearMap.det ^ 2 = 1 := by
  let q := ZornSpecification.norm R
  have hq : q.comp g.val.toLinearMap = q :=
    (octonion_norm_unique
      (octonion_norm_comp_equiv (Zorn.isOctonion R) g.val g.property.2)
      (Zorn.isOctonion R)).1
  let : q.polarBilin.IsPerfPair := Zorn.perfect R
  apply determinant_square_of_perfect_isometry q.polarBilin g.val
  intro x y
  have h := congrArg QuadraticMap.polarBilin hq
  rw [QuadraticMap.polarBilin_comp] at h
  exact congrArg (fun B : LinearMap.BilinForm R (Zorn R) => B x y) h

set_option backward.isDefEq.respectTransparency false in
private theorem splitOctonion_determinant {K : Type u} [Field K]
    (g : SplitAutomorphism K) : g.val.toLinearMap.det = 1 := by
  classical
  by_cases h₂ : (2 : K) = 0
  · have hd := splitOctonion_determinant_square g
    have hh : (g.val.toLinearMap.det - 1)^2 = 0 := by
      linear_combination hd - (g.val.toLinearMap.det - 1) * h₂
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh)
  obtain ⟨B, _, _, ρ, _, hρ⟩ := Peirce.split_evaluation_scheme.{u,u} K
  let : ConnectedSpace (PrimeSpectrum B) := splitAutomorphismRing_connected hρ
  obtain ⟨_, _, E, _, hE⟩ := hρ
  let G := E B (AlgHom.id K B)
  let d := G.val.toLinearMap.det
  have hd : d ^ 2 = 1 := splitOctonion_determinant_square G
  have hmap (a : B →ₐ[K] K) : a d = (E K a).val.toLinearMap.det := by
    change a.toRingHom G.val.toLinearMap.det = _
    rw [← LinearMap.det_toMatrix (zornBasis B), ← LinearMap.det_toMatrix (zornBasis K),
      RingHom.map_det a.toRingHom]
    congr 1
    ext i j
    have h := hE B K (AlgHom.id K B) a (zornBasis B j)
    rw [AlgHom.comp_id, map_zornBasis] at h
    have hh := congrArg (fun x => Zorn.pairedFunctions K x i) h
    rw [pairedFunctions_mapCoordinates] at hh
    have hc {S : Type u} [CommRing S] (z : Zorn S) (i) :
        (zornBasis S).repr z i = Zorn.pairedFunctions S z i := by
      simp [zornBasis]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, hc, LinearEquiv.coe_coe, G] using hh.symm
  let r : B := algebraMap K B ((2 : K)⁻¹)
  have hr : r * 2 = 1 := by
    change algebraMap K B ((2 : K)⁻¹) * 2 = 1
    rw [← map_ofNat (algebraMap K B) 2, ← map_mul, inv_mul_cancel₀ h₂, map_one]
  let e := r * (1 + d)
  let f := r * (1 - d)
  have hef : e * f = 0 := by
    dsimp only [e, f]
    linear_combination -r^2 * hd
  have hes : e + f = 1 := by
    dsimp only [e, f]
    linear_combination hr
  have hc := PrimeSpectrum.isClopen_basicOpen_of_mul_add e f hef hes
  let a₀ := (E K).symm (⟨LinearEquiv.refl K _, rfl, fun _ _ => rfl⟩ : SplitAutomorphism K)
  have h₀ : a₀ d = 1 := by
    rw [hmap]
    dsimp only [a₀]
    rw [Equiv.apply_symm_apply]
    exact LinearMap.det_id
  let p₀ : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hmem : PrimeSpectrum.comap a₀.toRingHom p₀ ∈ PrimeSpectrum.basicOpen e := by
    change a₀ e ∉ (⊥ : Ideal K)
    have he : a₀ e = 1 := by
      simp only [e, map_mul, map_add, map_one, h₀]
      have hr₀ := congrArg a₀ hr
      simpa only [map_mul, map_ofNat, map_one, one_add_one_eq_two] using hr₀
    rw [he]
    exact fun h => one_ne_zero (Ideal.mem_bot.mp h)
  have hall : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) = Set.univ :=
    (isClopen_iff.mp hc).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨_, hmem⟩)
  let a := (E K).symm g
  have ha : a d = g.val.toLinearMap.det := (hmap a).trans
    (congrArg (fun h : SplitAutomorphism K => h.val.toLinearMap.det) ((E K).apply_symm_apply g))
  have hne : a e ≠ 0 := by
    have hm : PrimeSpectrum.comap a.toRingHom p₀ ∈
        (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) := by
      rw [hall]
      exact Set.mem_univ _
    change a e ∉ (⊥ : Ideal K) at hm
    exact fun hz => hm (Ideal.mem_bot.mpr hz)
  have hz : a e * a f = 0 := by rw [← map_mul, hef, map_zero]
  have hf : a f = 0 := (mul_eq_zero.mp hz).resolve_left hne
  have hh : a e = 1 := by simpa only [map_add, hf, add_zero, map_one] using congrArg a hes
  have hr' : a r * 2 = 1 := by simpa only [map_mul, map_ofNat, map_one] using congrArg a hr
  have hd' : a d = 1 := by
    have h := hh
    simp only [e, map_mul, map_add, map_one] at h
    have hn : a r ≠ 0 := fun he => by simp [he] at hr'
    have key : a r * (1 + a d) = a r * (1 + 1) := h.trans (by simpa only [one_add_one_eq_two] using hr'.symm)
    exact add_left_cancel (mul_left_cancel₀ hn key)
  exact ha.symm.trans hd'

theorem octonionDeterminant : OctonionDeterminant.{u,v} := by
  intro L _ C _ _ _ _ q hq f hf
  let K := AlgebraicClosure L
  let := hq.finite
  let g := f.baseChange L K C C
  have hg (x y : K ⊗[L] C) : g (x * y) = g x * g y :=
    baseChange_mul_of_linearEquiv f hf K x y
  have hK := octonion_norm_baseChange hq K
  obtain ⟨F⟩ := octonion_splits_over_algebraically_closed hK
  let e := F.toLinearEquiv
  let h := (e.trans g).trans e.symm
  have he (x y) : e (x * y) = e x * e y := F.map_mul x y
  have hm (x y) : h (x * y) = h x * h y := by
    apply e.injective
    simp only [h, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he, hg]
  have hu : h 1 = 1 := by
    obtain ⟨y, hy⟩ := h.surjective 1
    simpa only [one_mul, hy, mul_one] using (hm 1 y).symm
  have hd := splitOctonion_determinant ⟨h, hu, hm⟩
  apply (algebraMap L K).injective
  rw [map_one, ← LinearMap.det_baseChange]
  exact (LinearMap.det_conj g.toLinearMap e.symm).symm.trans hd

set_option maxHeartbeats 900000 in
theorem octonionPolynomialModel : OctonionPolynomialModel.{u,v,w} := by
  intro k _ C _ _ _ _ b q hq ha
  refine ⟨(quadraticPolynomialComparison.{u,v,0,w} b q).1, ?_, ?_⟩
  · intro x hx hz
    exact hx (b.equivFun.symm.injective ((ha _ ((quadraticPolynomial_eval b q x).symm.trans hz)).trans
      (map_zero _).symm))
  · intro L _ _ M
    dsimp only
    let c := b.baseChange L
    let f := (matrixCoordinates c).symm M
    have hf : matrixCoordinates c f = M := (matrixCoordinates c).apply_symm_apply M
    have hL := octonion_norm_baseChange hq L
    change ((∀ x y, f (x * y) = f x * f y) ↔
      ∃ g : (L ⊗[k] C) ≃ₗ[L] (L ⊗[k] C),
        matrixCoordinates c g = M ∧ g 1 = 1 ∧ ∀ x y, g (x * y) = g x * g y) ∧
      ((∀ x y, f (x * y) = f x * f y) → _)
    constructor
    · constructor
      · intro hm
        have hu : f 1 = 1 := by
          obtain ⟨y, hy⟩ := f.surjective 1
          simpa only [one_mul, hy, mul_one] using (hm 1 y).symm
        exact ⟨f, hf, hu, hm⟩
      · rintro ⟨g, hg, _, hm⟩
        have hfg : f = g := (matrixCoordinates c).injective (hf.trans hg.symm)
        exact hfg.symm ▸ hm
    · intro hm
      have hdM : M.val.det = 1 :=
        (congrArg (fun A : GL (Fin 8) L => A.val.det) hf).symm.trans
          ((matrixCoordinateComparison c f 0).2.trans (octonionDeterminant _ hL f hm))
      refine ⟨matrixDet_eq_one M hdM, fun x => ?_⟩
      have hq' := (octonion_norm_unique
        (octonion_norm_comp_equiv hL f hm) hL).1
      have he := (matrixCoordinateComparison c f (c.equivFun.symm x)).1
      rw [LinearEquiv.apply_symm_apply, hf] at he
      rw [(quadraticPolynomialComparison b q).2, (quadraticPolynomialComparison b q).2,
        he, LinearEquiv.symm_apply_apply]
      exact DFunLike.congr_fun hq' _

end Octonions

theorem divisionStabilizerNorm : DivisionStabilizerNorm := by
  intro k L D I _ _ _ _ _ _ _ hD b
  have heval (u : (L ⊗[k] D)ˣ) :
      divisionNormInCoordinates hD b (divisionMatrixHom b u) = normAt hD b u.val := by
    unfold divisionNormInCoordinates
    rw [(divisionExtensionModel (L := L) hD b).2.1 u 1, mul_one]
    rfl
  refine ⟨heval, ?_, ?_⟩
  · intro x hx
    have hn : RM03.CSA.reducedNorm (RM03.CSA.isCentralSimple_baseChange hD) x ≠ 0 := by
      rw [← normAt_eq hD b x, hx]
      exact one_ne_zero
    exact (RM03.CSA.reducedNorm_ne_zero_iff_isUnit _ _).mp hn
  · rintro M ⟨u, rfl⟩
    rw [heval]
    exact (divisionExtensionModel (L := L) hD b).2.2.2.1 u

private def divisionCoordinateNormHom {k L D I : Type*} [Field k] [Field L]
    [Algebra k L] [Ring D] [Algebra k D] [Fintype I] [DecidableEq I]
    (hD : _root_.Specs.RM03.CSA.isCentralSimple k D) (b : Module.Basis I k D) :
    (divisionMatrixHom (L := L) b).range →* L where
  toFun M := divisionNormInCoordinates hD b M.val
  map_one' := by
    change divisionNormInCoordinates hD b (1 : GL I L) = 1
    rw [← map_one (divisionMatrixHom (L := L) b), (divisionStabilizerNorm hD b).1,
      normAt_eq hD b]
    exact RM03.CSA.reducedNorm_one _
  map_mul' := by
    rintro ⟨M, ⟨u, rfl⟩⟩ ⟨P, ⟨v, rfl⟩⟩
    change divisionNormInCoordinates hD b (divisionMatrixHom b u * divisionMatrixHom b v) =
      divisionNormInCoordinates hD b (divisionMatrixHom b u) *
        divisionNormInCoordinates hD b (divisionMatrixHom b v)
    rw [← map_mul, (divisionStabilizerNorm hD b).1,
      (divisionStabilizerNorm hD b).1, (divisionStabilizerNorm hD b).1]
    rw [normAt_eq hD b (u * v).val, normAt_eq hD b u.val, normAt_eq hD b v.val]
    exact RM03.CSA.reducedNorm_mul _ _ _

private theorem continuous_matrix_mulVec_const {L I : Type*} [CommRing L] [Fintype I]
    [DecidableEq I] [TopologicalSpace L] [IsTopologicalRing L] (x : I → L) :
    Continuous (fun M : GL I L => M.val.mulVec x) := by
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i)).mul continuous_const

private theorem continuous_divisionNormInCoordinates {k L D I : Type*} [Field k] [Field L]
    [Algebra k L] [Ring D] [Algebra k D] [Fintype I] [DecidableEq I]
    [TopologicalSpace L] [IsTopologicalRing L]
    (hD : _root_.Specs.RM03.CSA.isCentralSimple k D) (b : Module.Basis I k D) :
    Continuous (divisionNormInCoordinates (L := L) hD b) := by
  change Continuous (fun M : GL I L => divisionNormInCoordinates hD b M)
  simp only [divisionNormInCoordinates, MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.continuous_eval _).comp (continuous_matrix_mulVec_const _)

private theorem norm_mem_valuationSubring {L : Type*} [Field L] (V : ValuationSubring L)
    {x : L} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n ∈ V) : x ∈ V := by
  rw [← V.valuationSubring_valuation, Valuation.mem_valuationSubring_iff] at hx ⊢
  rw [map_pow] at hx
  exact (pow_le_one_iff_of_nonneg zero_le hn).mp hx

open Filter in
set_option maxHeartbeats 900000 in
theorem divisionAdelicNorm : DivisionAdelicNorm := by
  intro k D I J _ _ _ _ _ hD b L _ _ _ _ O hO
  dsimp only
  let T j := (divisionMatrixHom (L := L j) b).range
  let U j := ((Matrix.GeneralLinearGroup.map (n := I) (O j).subtype).range).comap (T j).subtype
  let φ (j : J) : T j →* L j := divisionCoordinateNormHom hD b
  have hm (j : J) : Set.MapsTo (φ j) (U j) (O j) := by
    intro a ha
    rcases hO j with htop | ⟨V, hV⟩
    · rw [htop]; exact Subring.mem_top _
    · obtain ⟨M, hM⟩ := ha
      change Matrix.GeneralLinearGroup.map (O j).subtype M = a.val at hM
      have hdet : a.val.val.det ∈ O j := by
        rw [← hM]
        change ((O j).subtype.mapMatrix M.val).det ∈ O j
        rw [← RingHom.map_det (O j).subtype M.val]
        exact M.val.det.property
      rw [(divisionStabilizerNorm hD b).2.2 a.val a.property, hV] at hdet
      change divisionNormInCoordinates hD b a.val ∈ O j
      rw [hV]
      exact norm_mem_valuationSubring V (RM03.CSA.degree_pos hD).ne' hdet
  have hfilter : Tendsto (id : J → J) cofinite cofinite := tendsto_id
  have HE : ∀ᶠ j in cofinite, Set.MapsTo (φ j) (U j) (O j) := Eventually.of_forall hm
  let F := RestrictedProduct.mapAlongMonoidHom (fun j => T j) L id hfilter φ HE
  have hF : Continuous F :=
    RestrictedProduct.mapAlong_continuous (fun j => T j) L id hfilter
      (fun j => φ j) HE
      (fun j => (continuous_divisionNormInCoordinates hD b).comp continuous_subtype_val)
  refine ⟨F.toHomUnits, Units.continuous_iff.mpr ⟨hF, ?_⟩, ?_⟩
  · exact hF.comp continuous_inv
  · intro x j
    rfl

theorem matrixBaseChangeComparison : MatrixBaseChangeComparison := by
  intro k L V I _ _ _ _ _ _ _ b f
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (matrixCoordinates (b.baseChange L) (f.baseChange k L V V)).val i j =
    ((matrixCoordinates b f).val.map (algebraMap k L)) i j
  rw [matrixCoordinates_value, matrixCoordinates_value]
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]

theorem restrictedOctonionStabilizer : RestrictedOctonionStabilizer := by
  intro k K C S _ _ _ _ _ _ _ c f
  constructor
  · rintro ⟨hc, hm⟩
    obtain ⟨g, hg⟩ := (scalarOperatorComparison c f).mp hc
    have hmul (x y : C) : g (x * y) = g x * g y := by
      simp only [hg, hm]
    obtain ⟨y, hy⟩ := g.surjective 1
    exact ⟨g, hg, by simpa only [one_mul, hy, mul_one] using (hmul 1 y).symm, hmul⟩
  · rintro ⟨g, hg, _, hm⟩
    exact ⟨(scalarOperatorComparison c f).mpr ⟨g, hg⟩, by simpa only [hg] using hm⟩

theorem restrictedOrthogonalStabilizer : RestrictedOrthogonalStabilizer := by
  intro k K V S I _ _ _ _ _ _ _ _ _ c b q f
  constructor
  · rintro ⟨hc, hq, hv⟩
    obtain ⟨g, hg⟩ := (scalarOperatorComparison c f).mp hc
    have hgq (x : V) : q (g x) = q x := by rw [hg, hq]
    have hgv (x : I → V) : basisVolume b (fun i => g (x i)) = basisVolume b x := by
      simpa only [hg] using hv x
    exact ⟨g, hg, hgq, ((quadraticVolumeStabilizer b q g).mp ⟨hgq, hgv⟩).2⟩
  · rintro ⟨g, hg, hq, hd⟩
    have hgv := ((quadraticVolumeStabilizer b q g).mpr ⟨hq, hd⟩).2
    exact ⟨(scalarOperatorComparison c f).mpr ⟨g, hg⟩, by simpa only [hg] using hq,
      by simpa only [hg] using hgv⟩

section GlobalAdeles

open LinearAlgebraicGroups.Arithmetic Filter IsDedekindDomain NumberField
open scoped NumberField

private theorem scalarFiniteProjection {k : Type u} [Field k] (G : GlobalFieldData.{u,v} k) :
    ∃ f : (Πʳ j : G.Place, [G.Completion j, completionReferenceRing G j]) →+*
        (Πʳ j : G.FinitePlace, [G.FiniteCompletion j, G.integers j]),
      Continuous f ∧ ∀ x j, f x j = x (.inl j) := by
  let ι : G.FinitePlace → G.Place := Sum.inl
  have hι : Tendsto ι cofinite cofinite := Sum.inl_injective.tendsto_cofinite
  have hm : ∀ᶠ j in cofinite,
      Set.MapsTo (fun x : G.Completion (ι j) => (show G.FiniteCompletion j from x))
        (completionReferenceRing G (ι j) : Set (G.Completion (ι j)))
        (G.integers j : Set (G.FiniteCompletion j)) :=
    Eventually.of_forall fun _ => fun _ hx => hx
  let f := RestrictedProduct.mapAlongRingHom (B₁ := completionReferenceRing G) (B₂ := G.integers)
    G.Completion G.FiniteCompletion ι hι (fun _ => RingHom.id _) hm
  refine ⟨f, ?_, fun _ _ => rfl⟩
  exact RestrictedProduct.mapAlong_continuous
    (A₁ := fun j => (completionReferenceRing G j : Set (G.Completion j)))
    (A₂ := fun j => (G.integers j : Set (G.FiniteCompletion j)))
    G.Completion G.FiniteCompletion ι hι
    (fun j x => (show G.FiniteCompletion j from x)) hm (fun _ => continuous_id)

private theorem scalarAdelesComparison {k : Type u} [Field k] (G : GlobalFieldData.{u,v} k) :
    ∃ f : (Πʳ j : G.Place, [G.Completion j, completionReferenceRing G j]) →+* G.AdeleRing,
      Continuous f ∧ ∀ x j, G.coordinate j (f x) = x j := by
  obtain ⟨πf, hπf, hcoord⟩ := scalarFiniteProjection G
  cases G with
  | number hk =>
    let := hk
    let G : GlobalFieldData.{u,v} k := .number hk
    let fieldAt (j : G.Place) : Field (G.Completion j) := GlobalFieldData.instFieldCompletion G j
    let topologyAt (j : G.Place) : TopologicalSpace (G.Completion j) :=
      GlobalFieldData.instTopologicalSpaceCompletion G j
    have ha : Continuous (fun x : (Πʳ j : G.Place, [G.Completion j, completionReferenceRing G j]) =>
        fun w : NumberField.InfinitePlace k => (show w.Completion from x (Sum.inr w))) :=
      continuous_pi fun w => RestrictedProduct.continuous_eval (Sum.inr w : G.Place)
    refine ⟨{ toFun := fun x => (fun w => x (Sum.inr w), πf x)
              map_zero' := Prod.ext rfl πf.map_zero
              map_one' := Prod.ext rfl πf.map_one
              map_add' := fun x y => Prod.ext rfl (πf.map_add x y)
              map_mul' := fun x y => Prod.ext rfl (πf.map_mul x y) },
      ha.prodMk hπf, ?_⟩
    intro x j
    cases j with
    | inl w => exact hcoord x w
    | inr w => rfl
  | function F t =>
    refine ⟨πf, hπf, ?_⟩
    intro x j
    cases j with
    | inl w => exact hcoord x w
    | inr w => exact w.elim

private theorem completionTopologicalRing {k : Type u} [Field k] (G : GlobalFieldData.{u,v} k)
    (j : G.Place) : IsTopologicalRing (G.Completion j) := by
  cases j with
  | inl j =>
    let : IsNonarchimedeanLocalField (G.FiniteCompletion j) := inferInstance
    exact inferInstanceAs (IsTopologicalRing (G.FiniteCompletion j))
  | inr j =>
    cases G with
    | number hk => exact inferInstanceAs (IsTopologicalRing j.Completion)
    | function F t => exact j.elim

set_option maxHeartbeats 900000 in
theorem divisionGlobalAdelicNorm : DivisionGlobalAdelicNorm := by
  intro k D I _ _ _ _ _ G hD b
  dsimp only
  let alg (j : G.Place) : Algebra k (G.Completion j) := (G.embedding j).toAlgebra
  let localTopology (j : G.Place) : IsTopologicalRing (G.Completion j) := completionTopologicalRing G j
  have hO (j : G.Place) :
      completionReferenceRing G j = ⊤ ∨ ∃ V : ValuationSubring (G.Completion j),
        completionReferenceRing G j = V.toSubring := by
    cases j with
    | inl j => exact Or.inr ⟨G.integers j, rfl⟩
    | inr j => exact Or.inl rfl
  obtain ⟨N, hN, hcoord⟩ := divisionAdelicNorm hD b G.Completion (completionReferenceRing G) hO
  obtain ⟨f, hf, hcoord'⟩ := scalarAdelesComparison G
  exact ⟨(Units.map f.toMonoidHom).comp N, (hf.units_map _).comp hN,
    fun x j => (hcoord' (N x).val j).trans (hcoord x j)⟩

end GlobalAdeles

theorem divisionRationalNormComparison : DivisionRationalNormComparison := by
  intro k L D I _ _ _ _ _ _ _ hD b u
  let i : D →ₐ[k] L ⊗[k] D := Algebra.TensorProduct.includeRight
  dsimp only
  rw [(divisionStabilizerNorm (L := L) hD b).1 (Units.map i.toMonoidHom u)]
  rw [normAt_eq hD b]
  exact RM03.CSA.reducedNorm_baseChange hD u.val

private theorem matrix_commutes_iff {L V I : Type*} [Field L] [AddCommGroup V] [Module L V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I L V) (M : GL I L) (T : V →ₗ[L] V) :
    let f := (matrixCoordinates b).symm M
    (∀ x, f (T x) = T (f x)) ↔
      M.val * LinearMap.toMatrix b b T = LinearMap.toMatrix b b T * M.val := by
  let f := (matrixCoordinates b).symm M
  change (∀ x, f (T x) = T (f x)) ↔ _
  have hf : matrixCoordinates b f = M := (matrixCoordinates b).apply_symm_apply M
  have hfval : M.val = LinearMap.toMatrix b b f.toLinearMap := by
    rw [← hf, matrixCoordinates_value]
  rw [hfval, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  constructor
  · intro H
    apply congrArg (LinearMap.toMatrix b b)
    exact LinearMap.ext H
  · intro H x
    exact DFunLike.congr_fun ((LinearMap.toMatrix b b).injective H) x

theorem divisionTensorStabilizer : DivisionTensorStabilizer := by
  intro k L D I _ _ _ _ _ _ _ hD b
  dsimp only
  let c := b.baseChange L
  let ρ := divisionMatrixHom (L := L) b
  let r (i : I) := (LinearMap.mul L (L ⊗[k] D)).flip (c i)
  have hr (i : I) : LinearMap.toMatrix c c (r i) =
      (rightMultiplicationMatrix b (b i)).map (algebraMap k L) := by
    ext j a
    simp only [rightMultiplicationMatrix, r, Matrix.map_apply, LinearMap.toMatrix_apply,
      LinearMap.flip_apply, LinearMap.mul_apply', c, Module.Basis.baseChange_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Module.Basis.baseChange_repr_tmul, Algebra.smul_def,
      mul_one]
  have h (M : GL I L) : M ∈ ρ.range ↔
      ∀ i, M.val * (rightMultiplicationMatrix b (b i)).map (algebraMap k L) =
        (rightMultiplicationMatrix b (b i)).map (algebraMap k L) * M.val := by
    refine (divisionMatrix_mem_range b M).trans ?_
    apply forall_congr'
    intro i
    rw [← hr i]
    exact matrix_commutes_iff c M (r i)
  refine ⟨h, ?_, ?_⟩
  · intro M
    constructor
    · rintro ⟨hm, hn⟩
      obtain ⟨x, rfl⟩ := (h M).mpr hm
      exact ⟨x, ((divisionStabilizerNorm hD b).1 x).symm.trans hn, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(h _).mp ⟨x, rfl⟩, ((divisionStabilizerNorm hD b).1 x).trans hx⟩
  · intro x
    have hx : (leftUnit (R := k) x).baseChange k L D D =
        leftUnit (Units.map (Algebra.TensorProduct.includeRight :
          D →ₐ[k] L ⊗[k] D).toMonoidHom x) := by
      apply LinearEquiv.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a y =>
        rw [LinearEquiv.baseChange_tmul]
        change (a ⊗ₜ[k] (x.val * y)) = (1 ⊗ₜ[k] x.val) * (a ⊗ₜ[k] y)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | add y z hy hz => rw [map_add, map_add, hy, hz]
    rw [← matrixBaseChangeComparison (L := L) b (leftUnit x), hx]
    rfl

open RM03.CSA.NormOneGroup (normOne) in
theorem divisionNormOneMatrixModel : DivisionNormOneMatrixModel := by
  intro k L D I _ _ _ _ _ _ _ hD b
  dsimp only
  let u := normOneToUnits (L := L) hD b
  let ρ := divisionNormOneMatrixHom (L := L) hD b
  have hρ (x : normOne (R := L) hD b) : ρ x = divisionMatrixHom b (u x) := rfl
  obtain ⟨hinj, hact, _, _, hinv⟩ := divisionExtensionModel (L := L) hD b
  refine ⟨hinj.comp (fun x y h => Subtype.ext (congrArg Units.val h)), ?_, ?_, ?_⟩
  · intro x z
    exact hact (u x) z
  · intro M
    rw [(divisionTensorStabilizer (L := L) hD b).2.1 M]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨u x, x.property, (hρ x).symm⟩
    · rintro ⟨v, hv, rfl⟩
      let x : normOne (R := L) hD b := ⟨v.val, hv⟩
      have h : u x = v := Units.ext rfl
      exact ⟨x, by rw [hρ, h]⟩
  · intro x
    exact hinv (u x) x.property

open private coord_change from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup

open RM03.CSA.NormOneGroup (normOne) in
private theorem divisionNormOneMatrix_apply {k L D I : Type*}
    [Field k] [Field L] [Algebra k L] [Ring D] [Algebra k D]
    [Fintype I] [DecidableEq I] (hD : RM03.CSA.IsCentralSimple k D)
    (b : Module.Basis I k D) (x : normOne (R := L) hD b) (i j : I) :
    (divisionNormOneMatrixHom hD b x).val i j =
      (b.baseChange L).repr (x.val * (1 ⊗ₜ[k] b j)) i := by
  change (matrixCoordinates (b.baseChange L) (leftUnit (normOneToUnits hD b x))).val i j = _
  rw [matrixCoordinates_value, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  rfl

open RM03.CSA.NormOneGroup (normOne mapNormOne changeCoefficients) in
theorem divisionNormOneMatrixNaturality : DivisionNormOneMatrixNaturality := by
  intro k L E D I _ _ _ _ _ _ _ _ _ hD b a x
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (divisionNormOneMatrixHom hD b (mapNormOne hD b a x)).val i j =
    a ((divisionNormOneMatrixHom hD b x).val i j)
  rw [divisionNormOneMatrix_apply, divisionNormOneMatrix_apply]
  change (b.baseChange E).repr (changeCoefficients a x.val * (1 ⊗ₜ[k] b j)) i = _
  have hb : changeCoefficients a ((1 : L) ⊗ₜ[k] b j) = (1 : E) ⊗ₜ[k] b j := by
    simp [changeCoefficients, Algebra.TensorProduct.map_tmul]
  rw [← hb, ← map_mul]
  exact coord_change b a (x.val * (1 ⊗ₜ[k] b j)) i

theorem divisionNormIntegral : DivisionNormIntegral := by
  intro k L D I _ _ _ _ _ _ _ hD b O x hx
  let A := LinearMap.toMatrix (b.baseChange L) (b.baseChange L) (LinearMap.mul L _ x)
  let B : Matrix I I O := fun i j => ⟨A i j, hx i j⟩
  have he : O.toSubring.subtype.mapMatrix B = A := rfl
  have hdet : A.det ∈ O := by
    rw [← he, ← RingHom.map_det]
    exact B.det.property
  have hp : A.det = normAt hD b x ^ _root_.Specs.RM03.CSA.degree k D := by
    dsimp only [A]
    rw [LinearMap.det_toMatrix, det_leftMul_extension hD b]
  exact norm_mem_valuationSubring O (RM03.CSA.degree_pos hD).ne' (hp ▸ hdet)

theorem divisionClosedStabilizers : DivisionClosedStabilizers := by
  intro k L D I _ _ _ _ _ _ _ _ _ _ hD b
  dsimp only
  let T := (divisionMatrixHom (L := L) b).range
  let R (i : I) := (rightMultiplicationMatrix b (b i)).map (algebraMap k L)
  have he : (T : Set (GL I L)) =
      ⋂ i, {M : GL I L | M.val * R i = R i * M.val} := by
    ext M
    rw [Set.mem_iInter]
    exact (divisionTensorStabilizer (L := L) hD b).1 M
  have hv : Continuous (fun M : GL I L => M.val) := Units.continuous_val
  have hT : IsClosed (T : Set (GL I L)) := by
    rw [he]
    exact isClosed_iInter fun i =>
      isClosed_eq (hv.matrix_mul continuous_const) (continuous_const.matrix_mul hv)
  exact ⟨hT, hT.inter (isClosed_eq (continuous_divisionNormInCoordinates hD b) continuous_const)⟩

theorem scalarMatrixComparison : ScalarMatrixComparison := by
  intro k K V S I _ _ _ _ _ _ _ _ _ c b M
  dsimp only
  let f := (matrixCoordinates b).symm M
  have h : (∀ s x, f (c s • x) = c s • f x) ↔
      ∀ s, M.val * LinearMap.toMatrix b b (DistribSMul.toLinearMap k V (c s)) =
        LinearMap.toMatrix b b (DistribSMul.toLinearMap k V (c s)) * M.val :=
    forall_congr' fun s => matrix_commutes_iff b M (DistribSMul.toLinearMap k V (c s))
  rw [← h, scalarOperatorComparison c f]
  constructor
  · rintro ⟨g, hg⟩
    have he : g.restrictScalars k = f := LinearEquiv.ext hg
    exact ⟨g, by rw [he, MulEquiv.apply_symm_apply]⟩
  · rintro ⟨g, hg⟩
    have he : g.restrictScalars k = f := (matrixCoordinates b).injective
      (hg.trans ((matrixCoordinates b).apply_symm_apply M).symm)
    exact ⟨g, fun x => DFunLike.congr_fun he x⟩

theorem octonionMultiplicationCoordinates : OctonionMultiplicationCoordinates := by
  intro k L C I _ _ _ _ _ _ _ _ _ b i j a
  simp only [Module.Basis.baseChange_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

private theorem bilinear_eq_on_basis {L V W I : Type*} [Field L] [AddCommGroup V]
    [Module L V] [AddCommGroup W] [Module L W] (c : Module.Basis I L V)
    {p r : V →ₗ[L] V →ₗ[L] W} (h : ∀ i j, p (c i) (c j) = r (c i) (c j)) : p = r :=
  c.ext fun i => c.ext (h i)

section OctonionPoints

open Composition.OctonionAutomorphismSpecification (octonionAlgebra)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
  (bilinearStabilizer schemePoints)
open private octonionAlgebra_preserves_iff from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms

theorem octonionMatrixStabilizer : OctonionMatrixStabilizer.{u,v} := by
  intro k L _ _ _ C _ _ _ _ b A
  dsimp only
  let S := CommAlgCat.of k L
  let c := b.baseChange L
  let B := bilinearStabilizer (octonionAlgebra (R := k) (C := C)) L
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv L (L ⊗[k] C)
  let a := A.subgroupPoints S
  let ρ := octonionMatrixHom (L := L) b A
  refine ⟨(matrixCoordinates c).injective.comp
    (e.injective.comp (Subtype.val_injective.comp a.injective)), ?_, ?_⟩
  · intro g x
    exact (matrixCoordinateComparison c (e (a g).val) x).1
  · intro M
    let f := (matrixCoordinates c).symm M
    have hBasis : (∀ i j, f (c i * c j) = f (c i) * f (c j)) ↔
        ∀ x y, f (x * y) = f x * f y := by
      refine ⟨fun H x y => ?_, fun H i j => H (c i) (c j)⟩
      let p := LinearMap.mul L (L ⊗[k] C)
      have hp : p.compr₂ f.toLinearMap = p.compl₁₂ f.toLinearMap f.toLinearMap :=
        bilinear_eq_on_basis c H
      exact DFunLike.congr_fun (DFunLike.congr_fun hp x) y
    refine ⟨?_, hBasis⟩
    change M ∈ ρ.range ↔ ∀ i j, f (c i * c j) = f (c i) * f (c j)
    constructor
    · rintro ⟨g, rfl⟩
      have hm := ((octonionAlgebra_preserves_iff (R := k) L (a g).val).mp (a g).property).2
      intro i j
      change (matrixCoordinates c).symm (matrixCoordinates c (e (a g).val)) (c i * c j) =
        (matrixCoordinates c).symm (matrixCoordinates c (e (a g).val)) (c i) *
          (matrixCoordinates c).symm (matrixCoordinates c (e (a g).val)) (c j)
      rw [MulEquiv.symm_apply_apply]
      exact hm _ _
    · intro H
      have hm := hBasis.mp H
      have h1 : f 1 = 1 := by
        obtain ⟨y, hy⟩ := f.surjective 1
        simpa only [one_mul, hy, mul_one] using (hm 1 y).symm
      let g : B := ⟨e.symm f, (octonionAlgebra_preserves_iff (R := k) L _).mpr ⟨h1, hm⟩⟩
      refine ⟨a.symm g, ?_⟩
      change matrixCoordinates c (e ((a (a.symm g)).val)) = M
      rw [MulEquiv.apply_symm_apply]
      change matrixCoordinates c (e (e.symm f)) = M
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end OctonionPoints

private theorem continuous_coordinates_apply {L V I : Type*} [Field L] [AddCommGroup V]
    [Module L V] [Fintype I] [DecidableEq I] [TopologicalSpace L] [IsTopologicalRing L]
    (c : Module.Basis I L V) (x : V) :
    Continuous (fun M : GL I L => c.equivFun ((matrixCoordinates c).symm M x)) := by
  have h (M : GL I L) :
      M.val.mulVec (c.equivFun x) = c.equivFun ((matrixCoordinates c).symm M x) := by
    simpa only [MulEquiv.apply_symm_apply] using
      (matrixCoordinateComparison c ((matrixCoordinates c).symm M) x).1
  simpa only [h] using continuous_matrix_mulVec_const (c.equivFun x)

private theorem continuous_bilinear_coordinates {L V I : Type*} [Field L] [AddCommGroup V]
    [Module L V] [Fintype I] [DecidableEq I] [TopologicalSpace L] [IsTopologicalRing L]
    (c : Module.Basis I L V) (p : V →ₗ[L] V →ₗ[L] V) :
    Continuous (fun z : (I → L) × (I → L) =>
      c.equivFun (p (c.equivFun.symm z.1) (c.equivFun.symm z.2))) := by
  have h (z : (I → L) × (I → L)) (a : I) :
      c.equivFun (p (c.equivFun.symm z.1) (c.equivFun.symm z.2)) a =
        ∑ j, ∑ i, z.2 j * (z.1 i * c.equivFun (p (c i) (c j)) a) := by
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply continuous_pi
  intro a
  simp only [h]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
    ((continuous_apply j).comp continuous_snd).mul
      (((continuous_apply i).comp continuous_fst).mul continuous_const)

theorem octonionClosedStabilizer : OctonionClosedStabilizer.{u,v} := by
  intro k L _ _ _ _ _ _ C _ _ _ _ b A
  let c := b.baseChange L
  let f (M : GL (Fin 8) L) := (matrixCoordinates c).symm M
  let p := LinearMap.mul L (L ⊗[k] C)
  have h :
      ((octonionMatrixHom (L := L) b A).range : Set (GL (Fin 8) L)) =
        ⋂ i, ⋂ j, {M : GL (Fin 8) L |
          c.equivFun (f M (c i * c j)) = c.equivFun (p (f M (c i)) (f M (c j)))} := by
    ext M
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, c.equivFun.injective.eq_iff]
    exact ((octonionMatrixStabilizer (L := L) b A).2.2 M).1
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_coordinates_apply c (c i * c j)) ?_
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
    (continuous_bilinear_coordinates c p).comp
      ((continuous_coordinates_apply c (c i)).prodMk (continuous_coordinates_apply c (c j)))

private theorem quadratic_eq_on_basis {L V I : Type*} [Field L] [AddCommGroup V]
    [Module L V] [Fintype I] (b : Module.Basis I L V)
    {q r : QuadraticForm L V} (hd : ∀ i, q (b i) = r (b i))
    (hp : q.polarBilin = r.polarBilin) (x : V) : q x = r x := by
  classical
  have h (s : Finset I) : q (∑ i ∈ s, b.repr x i • b i) =
      r (∑ i ∈ s, b.repr x i • b i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, QuadraticMap.map_add q, QuadraticMap.map_add r]
      simp only [QuadraticMap.map_smul, hd, ih, ← QuadraticMap.polarBilin_apply_apply, hp]
  simpa only [b.sum_repr] using h Finset.univ

theorem orthogonalMatrixStabilizer : OrthogonalMatrixStabilizer := by
  intro k L V I _ _ _ _ _ _ _ b q
  dsimp only
  let c := b.baseChange L
  let qL := normBaseChange L q
  let ρ := (matrixCoordinates c).toMonoidHom.comp (specialOrthogonalGroup qL).subtype
  refine ⟨(matrixCoordinates c).injective.comp Subtype.val_injective, ?_, ?_⟩
  · intro f x
    exact (matrixCoordinateComparison c f.val x).1
  · intro M
    let f := (matrixCoordinates c).symm M
    have hf : matrixCoordinates c f = M := (matrixCoordinates c).apply_symm_apply M
    have hd : (matrixCoordinates c f).val.det = f.toLinearMap.det :=
      (matrixCoordinateComparison c f 0).2
    change (∃ g : specialOrthogonalGroup qL, matrixCoordinates c g.val = M) ↔
      (∀ i, qL (f (c i)) = qL (c i)) ∧
      (∀ i j, qL.polarBilin (f (c i)) (f (c j)) = qL.polarBilin (c i) (c j)) ∧
      basisVolume c (fun i => f (c i)) = basisVolume c c
    have hq : qL.comp f.toLinearMap = qL ↔ ∀ x, qL (f x) = qL x :=
      ⟨fun h x => DFunLike.congr_fun h x, fun h => QuadraticMap.ext fun x => h x⟩
    have hvol : basisVolume c (fun i => f (c i)) = basisVolume c c ↔ f.det = 1 := by
      rw [basisVolume_map, basisVolume_basis, mul_one, hd, ← LinearEquiv.coe_det,
        ← Units.val_one, Units.val_inj]
    constructor
    · rintro ⟨g, hg⟩
      have hfg : f = g.val := (matrixCoordinates c).injective (hf.trans hg.symm)
      have hpres : (∀ x, qL (f x) = qL x) ∧ f.det = 1 := by
        rw [hfg]
        exact g.property
      have hp := congrArg QuadraticMap.polarBilin (hq.mpr hpres.1)
      rw [QuadraticMap.polarBilin_comp] at hp
      refine ⟨fun i => hpres.1 (c i), fun i j => ?_, hvol.mpr hpres.2⟩
      exact congrArg (fun P : LinearMap.BilinForm L (L ⊗[k] V) => P (c i) (c j)) hp
    · rintro ⟨hdiag, hpolar, hvolume⟩
      have hp : (qL.comp f.toLinearMap).polarBilin = qL.polarBilin := by
        rw [QuadraticMap.polarBilin_comp]
        exact bilinear_eq_on_basis c hpolar
      exact ⟨⟨f, fun x => quadratic_eq_on_basis c hdiag hp x, hvol.mp hvolume⟩, hf⟩

theorem orthogonalClosedStabilizer : OrthogonalClosedStabilizer := by
  intro k L V _ _ _ _ _ _ _ _ n b q
  dsimp only
  let c := b.baseChange L
  let qL := normBaseChange L q
  let ρ := (matrixCoordinates c).toMonoidHom.comp (specialOrthogonalGroup qL).subtype
  let f (M : GL (Fin n) L) := (matrixCoordinates c).symm M
  have hq (x : L ⊗[k] V) : Continuous (fun M : GL (Fin n) L => qL (f M x)) := by
    have he (y : L ⊗[k] V) : (quadraticPolynomial c qL).eval (c.equivFun y) = qL y := by
      rw [quadraticPolynomial_eval, LinearEquiv.symm_apply_apply]
    simpa only [Function.comp_def, he] using
      (MvPolynomial.continuous_eval (quadraticPolynomial c qL)).comp
        (continuous_coordinates_apply c x)
  have he : (ρ.range : Set (GL (Fin n) L)) =
      (⋂ x : L ⊗[k] V, {M : GL (Fin n) L | qL (f M x) = qL x}) ∩
        {M : GL (Fin n) L | M.val.det = 1} := by
    ext M
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    change (∃ g : specialOrthogonalGroup qL, matrixCoordinates c g.val = M) ↔
      (∀ x, qL (f M x) = qL x) ∧ M.val.det = 1
    have hM : matrixCoordinates c (f M) = M := (matrixCoordinates c).apply_symm_apply M
    have hdet : M.val.det = (f M).toLinearMap.det :=
      (congrArg (fun g : GL (Fin n) L => g.val.det) hM).symm.trans
        (matrixCoordinateComparison c (f M) 0).2
    have hd : M.val.det = 1 ↔ (f M).det = 1 := by
      rw [hdet, ← LinearEquiv.coe_det, ← Units.val_one, Units.val_inj]
    constructor
    · rintro ⟨g, hg⟩
      have hfg : f M = g.val := (matrixCoordinates c).injective (hM.trans hg.symm)
      rw [hd, hfg]
      exact g.property
    · rintro ⟨hq, hdM⟩
      exact ⟨⟨f M, hq, hd.mp hdM⟩, hM⟩
  rw [he]
  exact (isClosed_iInter fun x => isClosed_eq (hq x) continuous_const).inter
    (isClosed_eq Units.continuous_val.matrix_det continuous_const)

end
end LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
