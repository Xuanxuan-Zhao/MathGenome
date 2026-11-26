import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticInvolutionTensors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NoncommRing

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients

open scoped BigOperators nonZeroDivisors Polynomial

open LinearAlgebraicGroups.Specs.AnisotropicTensorQuotients
open Set Topology

theorem compactOfFiniteBasisLabels : CompactOfFiniteBasisLabels := by
  classical
  intro A P T _ _ _ _ G i C label S hG hC hS hcompare hreduce
  let f : G → P := fun g => (hreduce g).choose
  have hf (g : G) : (g : A) * i (f g) ∈ C ∧ label (f g) ∈ S :=
    (hreduce g).choose_spec
  let labels := range (label ∘ f)
  have hlabels : labels.Finite := hS.subset (by
    rintro _ ⟨g, rfl⟩
    exact (hf g).2)
  let rep (t : labels) : G := t.property.choose
  have hrep (t : labels) : label (f (rep t)) = t := t.property.choose_spec
  let B : Set A := ⋃ t : labels, (fun x : A => x * (i (f (rep t)))⁻¹) '' C
  let : Finite labels := hlabels.to_subtype
  have hB : IsCompact B := isCompact_iUnion fun t => hC.image (continuous_mul_const _)
  let K : Set G := Subtype.val ⁻¹' B
  have hK : IsCompact K := Subtype.isCompact_iff.mpr (by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    exact hB.inter_right hG)
  let Γ := i.range.subgroupOf G
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have hπ : π '' K = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    let t : labels := ⟨label (f g), ⟨g, rfl⟩⟩
    let d : P := f g * (f (rep t))⁻¹
    have hd : i d ∈ G := hcompare _ _ (hrep t).symm
    let δ : G := ⟨i d, hd⟩
    have hδ : δ ∈ Γ := ⟨d, rfl⟩
    refine ⟨g * δ, ?_, ?_⟩
    · change (g : A) * i d ∈ B
      apply mem_iUnion.mpr
      refine ⟨t, (g : A) * i (f g), (hf g).1, ?_⟩
      simp [d, mul_assoc]
    · exact QuotientGroup.eq.mpr (by simpa using Γ.inv_mem hδ)
  exact ⟨hπ ▸ hK.image QuotientGroup.continuous_mk⟩

theorem compactOfTensorReduction : CompactOfTensorReduction := by
  intro A P T _ _ _ _ _ _ G i C t D hG hC hD hdisc hcont hfix hstab hrat hreduce
  let orbit (a : A) := a⁻¹ • t
  let S := orbit '' C ∩ D
  have hS : S.Finite := ((hC.image hcont).inter_right hD).finite
    (hdisc.mono inter_subset_right)
  apply compactOfFiniteBasisLabels G i C (orbit ∘ i) S hG hC hS
  · intro r s hrs
    apply hstab
    have h := congrArg (fun z : T => i r • z) hrs
    simpa [orbit, mul_smul] using h.symm
  · intro g
    obtain ⟨r, hr⟩ := hreduce g
    refine ⟨r, hr, ⟨⟨(g : A) * i r, hr, ?_⟩, hrat r⟩⟩
    have hf : (g : A)⁻¹ • t = t := by
      simpa [mul_smul] using
        (congrArg (fun z : T => (g : A)⁻¹ • z) (hfix g)).symm
    simp [orbit, mul_smul, hf]

theorem compactOfNormCorrection : CompactOfNormCorrection := by
  intro A P U _ _ _ _ _ _ _ i ν C D hC hν hD hdisc hrat hreduce
  let S := ν '' C ∩ D
  have hS : S.Finite := ((hC.image hν).inter_right hD).finite
    (hdisc.mono inter_subset_right)
  apply compactOfFiniteBasisLabels ν.ker i C (ν ∘ i) S
    (isClosed_singleton.preimage hν) hC hS
  · intro r s h
    change ν (i r) = ν (i s) at h
    change ν (i (r * s⁻¹)) = 1
    simp [h]
  · intro g
    obtain ⟨r, hr⟩ := hreduce g
    have hg : ν (g : A) = 1 := g.property
    refine ⟨r, hr, ⟨⟨(g : A) * i r, hr, ?_⟩, hrat r⟩⟩
    simp [hg]

universe u v z

theorem finiteRationalTensorCoordinates : FiniteRationalTensorCoordinates.{u, v} := by
  classical
  intro k _ D J _ e he hcoord C hC
  let Δ := Specs.DiscreteDiagonals.scalarDiagonalImage D
  obtain ⟨hΔ, hdisc⟩ :=
    (DiscreteDiagonals.scalarClosedDiscrete : Specs.DiscreteDiagonals.scalarClosedDiscrete.{u, v}) D
  have heΔ (x : k) : e x ∈ Δ := ⟨x, fun w => hcoord w x⟩
  let S (j : J) := (fun x : J → D.AdeleRing => x j) '' C ∩ Δ
  have hS (j : J) : (S j).Finite :=
    ((hC.image (continuous_apply j)).inter_right hΔ).finite (hdisc.mono inter_subset_right)
  have hpre (j : J) : (e ⁻¹' S j).Finite := (hS j).preimage he.injOn
  refine (Set.Finite.pi hpre).subset ?_
  intro x hx j _
  exact ⟨⟨fun a => e (x a), hx, rfl⟩, heΔ (x j)⟩

theorem rightMultiplicationCentralizer : RightMultiplicationCentralizer := by
  intro k D J _ _ _ b f
  constructor
  · intro h
    have hf : ∀ x, f x = f 1 * x := by
      have heq : f.toLinearMap = LinearMap.mul k D (f 1) := by
        apply b.ext
        intro j
        simpa using h j 1
      exact fun x => DFunLike.congr_fun heq x
    let y := f.symm 1
    have hy : f y = 1 := f.apply_symm_apply 1
    have hxy : f 1 * y = 1 := (hf y).symm.trans hy
    have hyx : y * f 1 = 1 := by
      apply f.injective
      calc
        f (y * f 1) = f 1 * (y * f 1) := hf _
        _ = f 1 := by rw [← mul_assoc, hxy, one_mul]
    let u : Dˣ := ⟨f 1, y, hxy, hyx⟩
    exact ⟨u, hf⟩
  · rintro ⟨u, hu⟩ j x
    rw [hu, hu, mul_assoc]

theorem divisionNormAnisotropic : DivisionNormAnisotropic := by
  intro k D J _ _ _ _ hD b
  open RM03.CSA in
  refine ⟨degree_pos hD, genericReducedNorm_homogeneous hD b, ?_⟩
  intro x hx
  have hA : RM03.CSA.IsCentralSimple k D := hD
  change (RM03.CSA.genericReducedNorm hA b).eval x ≠ 0
  rw [RM03.CSA.genericReducedNorm_eval, RM03.CSA.reducedNorm_ne_zero_iff_isUnit]
  have hsum : (∑ j, x j • b j) ≠ 0 := by
    rw [← b.equivFun_symm_apply]
    exact fun h => hx (b.equivFun.symm.injective (h.trans (map_zero _).symm))
  exact isUnit_iff_ne_zero.mpr hsum

theorem clearPolynomialDenominators : ClearPolynomialDenominators := by
  classical
  intro R k J _ _ _ _ _ p
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples R⁰ p.support p.coeff
  have hcoeff (m : p.support) :
      ∃ r : R, algebraMap R k r = algebraMap R k (a : R) * p.coeff m :=
    by
      have h := ha m m.property
      change ∃ r : R, algebraMap R k r = (a : R) • p.coeff m at h
      simpa only [Algebra.smul_def] using h
  choose r hr using hcoeff
  refine ⟨a, ∑ m ∈ p.support.attach, MvPolynomial.monomial (m : J →₀ ℕ) (r m),
    mem_nonZeroDivisors_iff_ne_zero.mp a.property, ?_⟩
  calc
    _ = ∑ m ∈ p.support.attach,
        MvPolynomial.monomial (m : J →₀ ℕ) (algebraMap R k (a : R) * p.coeff m) := by
      simp [MvPolynomial.map_monomial, hr]
    _ = ∑ m ∈ p.support,
        MvPolynomial.monomial m (algebraMap R k (a : R) * p.coeff m) :=
      p.support.sum_attach (fun m => MvPolynomial.monomial m
        (algebraMap R k (a : R) * p.coeff m))
    _ = MvPolynomial.C (algebraMap R k (a : R)) *
        (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
      simp only [Finset.mul_sum, MvPolynomial.C_mul_monomial]
    _ = _ := congrArg (MvPolynomial.C (algebraMap R k (a : R)) * ·) p.as_sum.symm

theorem compactOfAdelicTensorCoordinates : CompactOfAdelicTensorCoordinates.{u, v} := by
  intro k _ D e he hcoord A P J _ _ _ _ _ G i C label orbit hG hC hcont hcompare hreduce
  let S := {x : J → k | (fun j => e (x j)) ∈ orbit '' C}
  have hS : S.Finite := finiteRationalTensorCoordinates D e he hcoord _ (hC.image hcont)
  apply compactOfFiniteBasisLabels G i C label S hG hC hS hcompare
  intro g
  obtain ⟨r, hr, hlabel⟩ := hreduce g
  exact ⟨r, hr, (show label r ∈ S from ⟨_, hr, hlabel⟩)⟩

theorem finiteRootsOfUnity : FiniteRootsOfUnity := by
  intro k _ d hd
  let p := (Polynomial.X : k[X]) ^ d - Polynomial.C 1
  have hp : p ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hd 1
  refine (Polynomial.finite_setOfPred_isRoot hp).subset ?_
  intro a ha
  change a ^ d = 1 at ha
  simp [p, Polynomial.IsRoot, ha]

private theorem det_matrixLeftMul {L J : Type*} [Field L] [Fintype J] [DecidableEq J]
    (X : Matrix J J L) :
    LinearMap.det (LinearMap.mul L (Matrix J J L) X) = X.det ^ Fintype.card J := by
  let e : Matrix J J L ≃ₗ[L] (J → J → L) :=
    (Matrix.transposeLinearEquiv J J L L).trans (Matrix.ofLinearEquiv L).symm
  let f := LinearMap.mul L (Matrix J J L) X
  have h :
      e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap =
        LinearMap.pi (fun i : J => X.mulVecLin ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext
    intro y
    funext i j
    rfl
  rw [← LinearMap.det_conj f e, h, LinearMap.det_pi]
  simp [← Matrix.toLin'_apply', LinearMap.det_toLin']

open scoped TensorProduct in
theorem det_leftMul_eq_reducedNorm_pow : DetLeftMulEqReducedNormPow := by
  intro k A _ _ _ hA a
  classical
  have hCSA : RM03.CSA.IsCentralSimple k A := hA
  let : Module.Finite k A := hA.2.2
  let L := AlgebraicClosure k
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hCSA
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
  change f.det = RM03.CSA.reducedNorm hCSA a ^ RM03.CSA.degree k A
  apply (algebraMap k L).injective
  rw [← (LinearMap.det_baseChange (A := L) f), ← LinearMap.det_conj (f.baseChange L) e.toLinearEquiv,
    hconj, det_matrixLeftMul, Fintype.card_fin, map_pow, RM03.CSA.reducedNorm_map hCSA a e]

theorem orthogonalAdjointIdempotents : OrthogonalAdjointIdempotents := by
  intro A _ σ
  let s (x : A) : A := MulOpposite.unop (σ x)
  change Function.Involutive s → ∀ z e : A, z + s z = 1 → e ≠ 0 → e * e = e → s e * e = 0 →
    ∃ p : A, p ≠ 0 ∧ p * p = p ∧ s p * p = 0 ∧ p * s p = 0
  intro hs z e hz he₀ he hezero
  have smul (x y : A) : s (x * y) = s y * s x := by simp [s]
  have ssub (x y : A) : s (x - y) = s x - s y := by simp [s]
  have he' : s e * s e = s e := by rw [← smul, he]
  let corner (w : A) := e * w * s e
  have corner_left (w : A) : e * corner w = corner w := by
    simp only [corner, ← mul_assoc, he]
  have corner_right (w : A) : corner w * s e = corner w := by
    change (e * w * s e) * s e = e * w * s e
    rw [mul_assoc, he']
  have corner_mul_e (w : A) : corner w * e = 0 := by
    change (e * w * s e) * e = 0
    rw [mul_assoc, hezero, mul_zero]
  have adj_e_mul_corner (w : A) : s e * corner w = 0 := by
    change s e * (e * w * s e) = 0
    simp only [← mul_assoc, hezero, zero_mul]
  have corner_mul_corner (u w : A) : corner u * corner w = 0 := by
    change (e * u * s e) * corner w = 0
    rw [mul_assoc, adj_e_mul_corner, mul_zero]
  have adj_corner (w : A) : s (corner w) = corner (s w) := by
    simp [corner, smul, hs e, mul_assoc]
  let p : A := e - corner z
  have hpstar : s p = s e - corner (s z) := by simp only [p, ssub, adj_corner]
  have hpe : p * e = e := by
    simp only [p, sub_mul, he, corner_mul_e, sub_zero]
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro hp
    rw [hp, zero_mul] at hpe
    exact he₀ hpe.symm
  · calc
      p * p = (p * e) - (e * corner z - corner z * corner z) := by
        simp only [p]
        noncomm_ring
      _ = p := by rw [hpe, corner_left, corner_mul_corner, sub_zero]
  · rw [hpstar]
    simp only [p, sub_mul, mul_sub, hezero, adj_e_mul_corner, corner_mul_e,
      corner_mul_corner, sub_self]
  · have hadd : corner (s z) + corner z = e * s e := by
      have h : s z + z = 1 := by simpa only [add_comm] using hz
      simp [corner, ← add_mul, ← mul_add, h]
    calc
      p * s p = e * s e - (e * corner (s z) + corner z * s e) + corner z * corner (s z) := by
        rw [hpstar]
        simp only [p]
        noncomm_ring
      _ = 0 := by rw [corner_left, corner_right, corner_mul_corner, hadd, sub_self, add_zero]

open scoped RestrictedProduct
open IsDedekindDomain AdelicLatticeBounds

section BasisAdeles

noncomputable section

variable {R k B J : Type*} [CommRing R] [IsDedekindDomain R]
  [Field k] [Algebra R k] [IsFractionRing R k] [Field B]
  [Fintype J] [DecidableEq J]

private theorem finiteEntry_mapsTo (i j : J) (p : HeightOneSpectrum R) :
    MapsTo (fun m : Matrix.GeneralLinearGroup J (p.adicCompletion k) => m.val i j)
      (Matrix.GeneralLinearGroup.map (n := J) (p.adicCompletionIntegers k).subtype).range
      (p.adicCompletionIntegers k) := by
  rintro _ ⟨m, rfl⟩
  exact (m.val i j).property

private def finiteEntry (i j : J) (x : FiniteBasisAdeles R k J) : FiniteAdeleRing R k :=
  RestrictedProduct.map (fun p (m : Matrix.GeneralLinearGroup J (p.adicCompletion k)) =>
    m.val i j) (Filter.Eventually.of_forall (finiteEntry_mapsTo i j)) x

private theorem continuous_finiteEntry (i j : J) :
    Continuous (finiteEntry (R := R) (k := k) i j) :=
  RestrictedProduct.mapAlong_continuous
    (fun p : HeightOneSpectrum R => Matrix.GeneralLinearGroup J (p.adicCompletion k))
    (fun p : HeightOneSpectrum R => p.adicCompletion k)
    (A₁ := fun p => ↑(Matrix.GeneralLinearGroup.map
      (n := J) (p.adicCompletionIntegers k).subtype).range)
    (A₂ := fun p => ↑(p.adicCompletionIntegers k))
    id Filter.tendsto_id
    (fun _ m => m.val i j)
    (Filter.Eventually.of_forall (finiteEntry_mapsTo i j))
    (fun _ => (continuous_apply j).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i))

private theorem continuous_finiteBasisInv :
    Continuous (fun a : FiniteBasisAdeles R k J => a⁻¹) := by
  let G (p : HeightOneSpectrum R) := Matrix.GeneralLinearGroup J (p.adicCompletion k)
  let U (p : HeightOneSpectrum R) : Subgroup (G p) :=
    (Matrix.GeneralLinearGroup.map (p.adicCompletionIntegers k).subtype).range
  let h : ∀ᶠ p in Filter.cofinite, MapsTo (fun a : G p => a⁻¹) (U p) (U p) :=
    Filter.Eventually.of_forall fun p _ ha => (U p).inv_mem ha
  exact RestrictedProduct.mapAlong_continuous G G
    (A₁ := fun p => (U p : Set (G p))) (A₂ := fun p => (U p : Set (G p)))
    id Filter.tendsto_id
    (fun _ a => a⁻¹) h (fun _ => continuous_inv)

private def basisCoordinates (a : BasisAdeles R k B J) :
    Matrix J J (FiniteAdeleRing R k × B) :=
  fun i j => (finiteEntry i j a.1, a.2.val i j)

private theorem basisCoordinates_one :
    basisCoordinates (1 : BasisAdeles R k B J) = 1 := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · apply DFunLike.ext
    intro p
    change (1 : Matrix.GeneralLinearGroup J (p.adicCompletion k)).val i j =
      (((1 : Matrix J J (FiniteAdeleRing R k × B)) i j).1) p
    by_cases e : i = j <;> simp [Matrix.one_apply, e] <;> rfl
  · by_cases e : i = j <;> simp [basisCoordinates, Matrix.one_apply, e]

private theorem basisCoordinates_mul (a b : BasisAdeles R k B J) :
    basisCoordinates (a * b) = basisCoordinates a * basisCoordinates b := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · apply DFunLike.ext
    intro p
    change ((a.1 p).val * (b.1 p).val) i j = _
    simp only [basisCoordinates, Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul]
    rw [show (∑ x, finiteEntry i x a.1 * finiteEntry x j b.1) p =
        ∑ x, (finiteEntry i x a.1 * finiteEntry x j b.1) p from
      map_sum (RestrictedProduct.evalRingHom _ p) _ _]
    rfl
  · simp [basisCoordinates, Matrix.mul_apply, Prod.snd_sum]

private def basisCoordinatesHom :
    BasisAdeles R k B J →* Matrix.GeneralLinearGroup J (FiniteAdeleRing R k × B) where
  toFun a :=
    ⟨basisCoordinates a, basisCoordinates a⁻¹,
      by rw [← basisCoordinates_mul, mul_inv_cancel, basisCoordinates_one],
      by rw [← basisCoordinates_mul, inv_mul_cancel, basisCoordinates_one]⟩
  map_one' := Units.ext basisCoordinates_one
  map_mul' a b := Units.ext (basisCoordinates_mul a b)

theorem adelicBasisMatrixCoordinates : AdelicBasisMatrixCoordinates := by
  intro R k B J _ _ _ _ _ _ _ _ _
  refine ⟨basisCoordinatesHom, ?_, ?_, fun a p i j => rfl, fun a i j => rfl⟩
  · rw [Units.continuous_iff]
    constructor
    · exact continuous_matrix fun i j =>
        ((continuous_finiteEntry i j).comp continuous_fst).prodMk
          ((continuous_apply j).comp
            (Matrix.GeneralLinearGroup.continuous_apply _ continuous_snd i))
    · have hInv : Continuous (fun m : Matrix.GeneralLinearGroup J B => m⁻¹.val) :=
        Units.continuous_coe_inv (M := Matrix J J B)
      exact continuous_matrix fun i j =>
        ((continuous_finiteEntry i j).comp (continuous_finiteBasisInv.comp continuous_fst)).prodMk
          ((continuous_apply j).comp ((continuous_apply i).comp (hInv.comp continuous_snd)))
  · intro a b h
    have hc : basisCoordinates a = basisCoordinates b := congrArg Units.val h
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro p
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact congrArg (fun (m : Matrix J J (FiniteAdeleRing R k × B)) => (m i j).1 p) hc
    · apply Units.ext
      apply Matrix.ext
      intro i j
      exact congrArg (fun (m : Matrix J J (FiniteAdeleRing R k × B)) => (m i j).2) hc

end

end BasisAdeles

open scoped MatrixGroups NumberField RestrictedProduct
open TensorAdelicReduction
open IsDedekindDomain

private theorem mem_localConditions {A W : Type*} {B : W → Type*} [Group A]
    [∀ w, Group (B w)] (f : ∀ w, A →* B w) (H : ∀ w, Subgroup (B w)) (x : A) :
    x ∈ localConditions f H ↔ ∀ w, f w x ∈ H w := by
  exact Subgroup.mem_iInf

private theorem compactMatrixQuotient_of_representatives
    {A P : Type*} [Group A] [TopologicalSpace A] [Group P]
    (G : Subgroup A) (Γ : Subgroup P) (δ : P →* A)
    (hΓ : Γ.map δ ≤ G) (C : Set A) (hC : IsCompact C) (hG : IsClosed (G : Set A))
    (hreduce : ∀ g : G, ∃ r ∈ Γ, (g : A) * δ r ∈ C) :
    CompactMatrixQuotient G Γ δ := by
  let K : Set G := Subtype.val ⁻¹' C
  have hK : IsCompact K := Subtype.isCompact_iff.mpr (by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    exact hC.inter_right hG)
  let Λ := (Γ.map δ).subgroupOf G
  let π : G → G ⧸ Λ := QuotientGroup.mk
  have hπ : π '' K = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨r, hr, hgr⟩ := hreduce g
    have hδ : δ r ∈ Γ.map δ := ⟨r, hr, rfl⟩
    let a : G := ⟨δ r, hΓ hδ⟩
    refine ⟨g * a, hgr, QuotientGroup.eq.mpr ?_⟩
    have ha : a ∈ Λ := hδ
    simpa using Λ.inv_mem ha
  exact ⟨hΓ, ⟨hπ ▸ hK.image QuotientGroup.continuous_mk⟩⟩

private theorem isClosed_localConditions {A W : Type*} {B : W → Type*} [Group A]
    [TopologicalSpace A] [∀ w, Group (B w)] [∀ w, TopologicalSpace (B w)]
    (f : ∀ w, A →* B w) (H : ∀ w, Subgroup (B w))
    (hf : ∀ w, Continuous (f w)) (hH : ∀ w, IsClosed (H w : Set (B w))) :
    IsClosed (localConditions f H : Set A) := by
  have h : (localConditions f H : Set A) = ⋂ w, (f w) ⁻¹' (H w : Set (B w)) := by
    ext x
    simp [mem_localConditions]
  rw [h]
  exact isClosed_iInter fun w => (hH w).preimage (hf w)

private theorem continuous_functionAtPlace {k I : Type*} [Field k] [Fintype I] [DecidableEq I]
    (w : FunctionPlace k) : Continuous (functionAtPlace (I := I) w) :=
  RestrictedProduct.continuous_eval w

private theorem continuous_numberAtPlace {k I : Type*} [Field k] [NumberField k]
    [Fintype I] [DecidableEq I] (w : NumberPlace k) : Continuous (numberAtPlace (I := I) w) := by
  cases w with
  | inl w => exact (RestrictedProduct.continuous_eval w).comp continuous_fst
  | inr w => exact (continuous_apply w).comp continuous_snd

open private preservesTensor_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction
open private preservesTensor_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

section TensorCompactness

universe y

variable {k : Type u} {I P J H : Type*} [Field k] [Fintype I] [DecidableEq I] [Fintype P]
  [Finite J] [Finite H] {X : J → Type y} {Y : H → Type y} {O : H → Type*}
  [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] [∀ h, Finite (O h)]

private theorem tensor_system_map (T : TensorSystem k I X Y O)
    {L : Type u} [Field L] (e : k →+* L) (r : GL I k)
    (hr : T.Preserves (RingHom.id k) r) :
    T.Preserves e (Matrix.GeneralLinearGroup.map e r) := by
  classical
  refine ⟨fun j => preservesTensor_map e (T.moving j) r r (hr.1 j), ?_⟩
  intro h
  let : Fintype (O h) := Fintype.ofFinite _
  have hpres : PreservesTensor (T.fixed h) r 1 := by
    intro x
    simpa only [RingHom.id_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] using hr.2 h x
  have he := preservesTensor_map e (T.fixed h) r 1 hpres
  rw [map_one] at he
  intro x
  simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] using he x

private theorem isClosed_tensor_system (T : TensorSystem k I X Y O)
    {L : Type u} [Field L] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L]
    (e : k →+* L) : IsClosed {r : GL I L | T.Preserves e r} := by
  classical
  let (h : H) : Fintype (O h) := Fintype.ofFinite _
  have h : {r : GL I L | T.Preserves e r} =
      (⋂ j, {r | PreservesTensor (fun w a => e (T.moving j w a)) r r}) ∩
        (⋂ h, {r | PreservesTensor (fun w a => e (T.fixed h w a)) r 1}) := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, TensorSystem.Preserves]
    simp [PreservesTensor]
  rw [h]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro j
    simp only [preservesTensor_iff]
    exact isClosed_eq ((transformedTensorContinuous _).comp (continuous_id.prodMk continuous_id))
      continuous_const
  · apply isClosed_iInter
    intro h
    simp only [preservesTensor_iff]
    exact isClosed_eq ((transformedTensorContinuous _).comp (continuous_id.prodMk continuous_const))
      continuous_const

set_option maxHeartbeats 600000 in
private theorem compactFunctionTensorModel {F : Type*} [Field F] [Finite F] [Algebra F k]
    (t : SeparatingParameter F k) (M : MatrixModel k I) (p : P → MvPolynomial I k)
    (d : P → ℕ) (T : TensorSystem k I X Y O)
    (hd : ∀ j, 0 < d j ∧ (p j).IsHomogeneous (d j))
    (ha : ∀ x, x ≠ 0 → ∃ j, (p j).eval x ≠ 0)
    (hgroup : ∀ (L : Type u) [Field L] (e : k →+* L) (g : GL I L),
      g ∈ M L e ↔ T.Preserves e g)
    (hinv : ∀ (L : Type u) [Field L] (e : k →+* L) (g : GL I L), g ∈ M L e →
      g.det = 1 ∧ ∀ j x, (p j).eval₂ e (g.val.mulVec x) = (p j).eval₂ e x) :
    FunctionMatrixQuotientCompact M := by
  obtain ⟨δ, hδ, C, hC, _, hreduce⟩ := functionTensorAdelicReduction t p d T hd ha
  refine ⟨δ, hδ, ?_⟩
  let G := localConditions functionAtPlace (fun (w : FunctionPlace k) => M w.Completion w.embedding)
  have hG (g : G) (w : FunctionPlace k) : (g : FunctionMatrixAdeles k I) w ∈
      M w.Completion w.embedding :=
    (mem_localConditions _ _ _).mp g.property w
  refine compactMatrixQuotient_of_representatives G _ δ ?_ C hC ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    apply (mem_localConditions _ _ _).mpr
    intro w
    change δ r w ∈ M w.Completion w.embedding
    rw [hδ]
    exact (hgroup _ _ _).mpr (tensor_system_map T w.embedding r ((hgroup _ _ _).mp hr))
  · apply isClosed_localConditions _ _ continuous_functionAtPlace
    intro w
    rw [show (M w.Completion w.embedding : Set _) = {r | T.Preserves w.embedding r} from
      Set.ext fun r => hgroup _ _ r]
    exact isClosed_tensor_system T w.embedding
  · intro g
    obtain ⟨r, hr, hgr⟩ := hreduce g.val
      (fun w => (hinv _ _ _ (hG g w)).1)
      (fun j w x => (hinv _ _ _ (hG g w)).2 j x)
      (fun w => (hgroup _ _ _).mp (hG g w))
    exact ⟨r, (hgroup _ _ _).mpr hr, hgr⟩

set_option maxHeartbeats 600000 in
private theorem compactNumberTensorModel [NumberField k]
    (M : MatrixModel k I) (p : P → MvPolynomial I k)
    (d : P → ℕ) (T : TensorSystem k I X Y O)
    (hd : ∀ j, 0 < d j ∧ (p j).IsHomogeneous (d j))
    (ha : ∀ x, x ≠ 0 → ∃ j, (p j).eval x ≠ 0)
    (hgroup : ∀ (L : Type u) [Field L] (e : k →+* L) (g : GL I L),
      g ∈ M L e ↔ T.Preserves e g)
    (hinv : ∀ (L : Type u) [Field L] (e : k →+* L) (g : GL I L), g ∈ M L e →
      g.det = 1 ∧ ∀ j x, (p j).eval₂ e (g.val.mulVec x) = (p j).eval₂ e x) :
    NumberMatrixQuotientCompact M := by
  obtain ⟨δ, hδf, hδi, C, hC, _, hreduce⟩ := numberTensorAdelicReduction p d T hd ha
  have hδ (r : GL I k) (w : NumberPlace k) :
      numberAtPlace w (δ r) = Matrix.GeneralLinearGroup.map w.embedding r := by
    cases w with
    | inl w => exact hδf r w
    | inr w => exact hδi r w
  refine ⟨δ, hδ, ?_⟩
  let G := localConditions numberAtPlace (fun (w : NumberPlace k) => M w.Completion w.embedding)
  have hG (g : G) (w : NumberPlace k) : numberAtPlace w g.val ∈
      M w.Completion w.embedding :=
    (mem_localConditions _ _ _).mp g.property w
  refine compactMatrixQuotient_of_representatives G _ δ ?_ C hC ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    apply (mem_localConditions _ _ _).mpr
    intro w
    rw [hδ]
    exact (hgroup _ _ _).mpr (tensor_system_map T w.embedding r ((hgroup _ _ _).mp hr))
  · apply isClosed_localConditions _ _ continuous_numberAtPlace
    intro w
    rw [show (M w.Completion w.embedding : Set _) = {r | T.Preserves w.embedding r} from
      Set.ext fun r => hgroup _ _ r]
    cases w with
    | inl w => exact isClosed_tensor_system T (algebraMap k (w.adicCompletion k))
    | inr w => exact isClosed_tensor_system T (algebraMap k w.Completion)
  · intro g
    obtain ⟨r, hr, hgr⟩ := hreduce g.val
      (fun w => (hinv _ _ _ (hG g (.inl w))).1)
      (fun w => (hinv _ _ _ (hG g (.inr w))).1)
      (fun j w x => (hinv _ _ _ (hG g (.inl w))).2 j x)
      (fun j w x => (hinv _ _ _ (hG g (.inr w))).2 j x)
      ⟨(fun w => (hgroup _ _ _).mp (hG g (.inl w))),
        (fun w => (hgroup _ _ _).mp (hG g (.inr w)))⟩
    exact ⟨r, (hgroup _ _ _).mpr hr, hgr⟩

end TensorCompactness

open private coordinateTensor_basis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)

private theorem coordinateTensor_of_multilinear {L X I O : Type*} [CommRing L]
    [Fintype X] [Fintype I] [DecidableEq I]
    (F : MultilinearMap L (fun _ : X => I → L) (O → L)) (T : TensorCoefficients L X I O)
    (hT : ∀ w, T w = F (fun a => Pi.basisFun L I (w a))) :
    coordinateTensor T = F := by
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun L I)
  intro w
  rw [coordinateTensor_basis, hT]

private theorem mulVec_coordinates {L V I : Type*} [Field L]
    [AddCommGroup V] [Module L V] [Fintype I] [DecidableEq I]
    (c : Module.Basis I L V) (M : GL I L) (x : I → L) :
    M.val.mulVec x = c.equivFun ((matrixCoordinates c).symm M (c.equivFun.symm x)) := by
  have h := (DivisionOctonionOrthogonalTensors.matrixCoordinateComparison c
    ((matrixCoordinates c).symm M) (c.equivFun.symm x)).1
  rwa [LinearEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h

private def binaryMultilinear {L V W : Type*} [Field L] [AddCommGroup V] [Module L V]
    [AddCommGroup W] [Module L W] (B : V →ₗ[L] V →ₗ[L] W) :
    MultilinearMap L (fun _ : Fin 2 => V) W :=
  MultilinearMap.mk' (fun v => B (v 0) (v 1))
    (fun v i x y => by fin_cases i <;> simp)
    (fun v i a x => by fin_cases i <;> simp)

private theorem coordinateTensor_binary {L V W I O : Type*} [Field L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (c : Module.Basis I L V) (d : Module.Basis O L W) (B : V →ₗ[L] V →ₗ[L] W)
    (T : TensorCoefficients L (Fin 2) I O)
    (hT : ∀ w, T w = d.equivFun (B (c (w 0)) (c (w 1))))
    (x : Fin 2 → I → L) :
    coordinateTensor T x = d.equivFun (B (c.equivFun.symm (x 0)) (c.equivFun.symm (x 1))) := by
  let F := (d.equivFun.toLinearMap.compMultilinearMap (binaryMultilinear B)).compLinearMap
    (fun _ : Fin 2 => c.equivFun.symm.toLinearMap)
  have h : coordinateTensor T = F := by
    apply coordinateTensor_of_multilinear
    intro w
    rw [hT]
    change _ = d.equivFun (B (c.equivFun.symm (Pi.basisFun L I (w 0)))
      (c.equivFun.symm (Pi.basisFun L I (w 1))))
    simp
  rw [h]
  rfl

section Octonions

open Composition.OctonionAutomorphismSpecification (AutomorphismGroup)
open DivisionOctonionOrthogonalTensors
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates quadraticPolynomial octonionMatrixHom)
open scoped TensorProduct

variable {k : Type u} [Field k] {C : Type v} [NonAssocRing C] [Module k C]
  [IsScalarTower k C C] [SMulCommClass k C C]

private noncomputable def multiplicationTensor (b : Module.Basis (Fin 8) k C) :
    TensorSystem k (Fin 8) (fun _ : Unit => Fin 2) (fun _ : Empty => Unit) (fun _ => Unit) where
  moving _ w := b.equivFun (b (w 0) * b (w 1))
  fixed h := h.elim

set_option maxRecDepth 1800 in
private theorem octonion_tensor_comparison (b : Module.Basis (Fin 8) k C)
    (A : AutomorphismGroup k C) (L : Type u) [Field L]
    (e : k →+* L) (M : GL (Fin 8) L) :
    M ∈ octonionMatrixModel b A L e ↔ (multiplicationTensor b).Preserves e M := by
  let : Algebra k L := e.toAlgebra
  let c := b.baseChange L
  let f := (matrixCoordinates c).symm M
  let t : TensorCoefficients L (Fin 2) (Fin 8) (Fin 8) :=
    fun w i => e ((multiplicationTensor b).moving () w i)
  have ht (x : Fin 2 → Fin 8 → L) : coordinateTensor t x =
      c.equivFun (c.equivFun.symm (x 0) * c.equivFun.symm (x 1)) := by
    apply coordinateTensor_binary c c (LinearMap.mul L (L ⊗[k] C)) t _ x
    intro w
    funext i
    exact (octonionMultiplicationCoordinates b (w 0) (w 1) i).symm
  have hs := (octonionMatrixStabilizer (L := L) b A).2.2 M
  change M ∈ (octonionMatrixHom b A).range ↔ _
  rw [hs.1, hs.2]
  have ht' (x : Fin 2 → Fin 8 → L) :
      coordinateTensor t (fun i => M.val.mulVec (x i)) =
      c.equivFun (f (c.equivFun.symm (x 0)) * f (c.equivFun.symm (x 1))) := by
    rw [ht, mulVec_coordinates c M (x 0), mulVec_coordinates c M (x 1)]
    simp only [LinearEquiv.symm_apply_apply, f]
  have hm' (x : Fin 2 → Fin 8 → L) : M.val.mulVec (coordinateTensor t x) =
      c.equivFun (f (c.equivFun.symm (x 0) * c.equivFun.symm (x 1))) := by
    rw [ht, mulVec_coordinates c M]
    simp only [LinearEquiv.symm_apply_apply, f]
  constructor
  · intro h
    refine ⟨?_, fun x => x.elim⟩
    rintro ⟨⟩ x
    change coordinateTensor t (fun s => M.val.mulVec (x s)) = M.val.mulVec (coordinateTensor t x)
    rw [ht' x, hm' x, h]
  · intro h x y
    let v : Fin 2 → Fin 8 → L := ![c.equivFun x, c.equivFun y]
    have hh : coordinateTensor t (fun s => M.val.mulVec (v s)) =
        M.val.mulVec (coordinateTensor t v) := h.1 () v
    rw [ht' v, hm' v] at hh
    exact (c.equivFun.injective (by
      simpa only [v, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearEquiv.symm_apply_apply] using hh)).symm

set_option maxHeartbeats 800000 in
theorem octonionCompactness : OctonionCompactness.{u, v, z} := by
  classical
  intro k _ D C _ _ _ _ b q A hq ha
  let M := octonionMatrixModel b A
  let p : Unit → MvPolynomial (Fin 8) k := fun _ => quadraticPolynomial b q
  let T := multiplicationTensor b
  obtain ⟨hh, hn, hp⟩ := octonionPolynomialModel b q hq ha
  have hd (j : Unit) : 0 < 2 ∧ (p j).IsHomogeneous 2 := ⟨by decide, hh⟩
  have hzero x (hx : x ≠ 0) : ∃ j, (p j).eval x ≠ 0 := ⟨(), hn x hx⟩
  have hgroup (L : Type u) [Field L] (e : k →+* L) (g : GL (Fin 8) L) :
      g ∈ M L e ↔ T.Preserves e g := octonion_tensor_comparison b A L e g
  have hinv (L : Type u) [Field L] (e : k →+* L) (g : GL (Fin 8) L) (hg : g ∈ M L e) :
      g.det = 1 ∧ ∀ j x, (p j).eval₂ e (g.val.mulVec x) = (p j).eval₂ e x := by
    let : Algebra k L := e.toAlgebra
    have hs := (octonionMatrixStabilizer (L := L) b A).2.2 g
    obtain ⟨hdet, hinv⟩ := (hp L g).2 (hs.2.mp (hs.1.mp hg))
    exact ⟨hdet, fun _ => hinv⟩
  cases D with
  | number h =>
    let := h
    exact compactNumberTensorModel M p (fun _ => 2) T hd hzero hgroup hinv
  | function F t =>
    exact compactFunctionTensorModel t M p (fun _ => 2) T hd hzero hgroup hinv

end Octonions

section Orthogonal

open Matrix
open Composition.Specification (normBaseChange)
open DivisionOctonionOrthogonalTensors (matrixCoordinateComparison quadraticPolynomialComparison)
open Specs.DivisionOctonionOrthogonalTensors (quadraticPolynomial specialOrthogonalGroup)
open scoped TensorProduct

private theorem coordinateTensor_scalarBilinear {L V I : Type*} [Field L]
    [AddCommGroup V] [Module L V] [Fintype I] [DecidableEq I]
    (c : Module.Basis I L V) (B : LinearMap.BilinForm L V)
    (T : TensorCoefficients L (Fin 2) I Unit)
    (hT : ∀ w, T w () = B (c (w 0)) (c (w 1))) (x : Fin 2 → I → L) :
    coordinateTensor T x () = B (c.equivFun.symm (x 0)) (c.equivFun.symm (x 1)) := by
  let d : Module.Basis Unit L L := Module.Basis.singleton Unit L
  have hd (z : L) : d.equivFun z () = z := by simp [d, Module.Basis.equivFun_apply]
  rw [coordinateTensor_binary c d B T (fun w => funext fun _ => (hT w).trans (hd _).symm), hd]

/-- Coefficients of the determinant of the matrix whose rows are the inputs. -/
private noncomputable def volumeCoefficients {k I : Type*} [CommRing k] [Fintype I]
    [DecidableEq I] : TensorCoefficients k I I Unit :=
  fun w _ => (Matrix.of (fun a => Pi.basisFun k I (w a))).det

private theorem coordinateTensor_volume {k L I : Type*} [CommRing k] [CommRing L]
    [Fintype I] [DecidableEq I] (e : k →+* L) (x : I → I → L) :
    coordinateTensor (fun w a => e (volumeCoefficients (k := k) (I := I) w a)) x () =
      (Matrix.of x).det := by
  let p : L →ₗ[L] (Unit → L) :=
    { toFun := fun a _ => a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let F := p.compMultilinearMap (Matrix.detRowAlternating : (I → L) [⋀^I]→ₗ[L] L).toMultilinearMap
  have h : coordinateTensor (fun w a => e (volumeCoefficients (k := k) (I := I) w a)) = F := by
    apply coordinateTensor_of_multilinear
    intro w
    funext a
    change e ((Matrix.of (fun i => Pi.basisFun k I (w i))).det) =
      (Matrix.of (fun i => Pi.basisFun L I (w i))).det
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Pi.basisFun, Pi.single_apply]
  rw [h]
  rfl

private theorem volume_mulVec_iff {L I : Type*} [Field L] [Fintype I] [DecidableEq I]
    (g : GL I L) :
    (∀ x : I → I → L, (Matrix.of (fun i => g.val.mulVec (x i))).det = (Matrix.of x).det) ↔
      g.det = 1 := by
  have h (x : I → I → L) :
      Matrix.of (fun i => g.val.mulVec (x i)) = Matrix.of x * g.valᵀ := by
    ext i j
    change (g.val.mulVec (x i)) j = (Matrix.of x * g.valᵀ) i j
    simp only [Matrix.mulVec, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, dotProduct]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  constructor
  · intro hp
    have he := hp (fun i j => (1 : Matrix I I L) i j)
    rw [h, show Matrix.of (fun i j => (1 : Matrix I I L) i j) = 1 from rfl,
      one_mul, Matrix.det_transpose, Matrix.det_one] at he
    exact Units.ext he
  · intro hp x
    rw [h, Matrix.det_mul, Matrix.det_transpose, show g.val.det = 1 from congrArg Units.val hp, mul_one]

private abbrev orthogonalArity (n : ℕ) : Bool → Type
  | false => Fin 2
  | true => Fin n

private instance (n : ℕ) (i : Bool) : Fintype (orthogonalArity n i) :=
  match i with
  | false => inferInstanceAs (Fintype (Fin 2))
  | true => inferInstanceAs (Fintype (Fin n))

private noncomputable def orthogonalTensors {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] {n : ℕ} (b : Module.Basis (Fin n) k V) (q : QuadraticForm k V) :
    TensorSystem k (Fin n) (fun _ : Empty => Unit)
      (orthogonalArity n) (fun _ => Unit) where
  moving i := i.elim
  fixed
    | false => fun w _ => q.polarBilin (b (w (0 : Fin 2))) (b (w (1 : Fin 2)))
    | true => volumeCoefficients (I := Fin n)

set_option maxRecDepth 1600 in
private theorem orthogonal_tensor_comparison {k : Type u} [Field k] [NumberField k]
    {V : Type v} [AddCommGroup V] [Module k V] {n : ℕ}
    (b : Module.Basis (Fin n) k V) (q : QuadraticForm k V)
    {L : Type u} [Field L] (e : k →+* L) (M : GL (Fin n) L) :
    M ∈ orthogonalMatrixModel b q L e ↔ (orthogonalTensors b q).Preserves e M := by
  let : Algebra k L := e.toAlgebra
  have htwo : (2 : L) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using e.injective.ne (by norm_num : (2 : k) ≠ 0)
  let c := b.baseChange L
  let f := (matrixCoordinates c).symm M
  let qL := normBaseChange L q
  let B := qL.polarBilin
  let T : TensorCoefficients L (Fin 2) (Fin n) Unit :=
    fun w z => e ((orthogonalTensors b q).fixed false w z)
  have ht (x : Fin 2 → Fin n → L) :
      coordinateTensor T x () = B (c.equivFun.symm (x 0)) (c.equivFun.symm (x 1)) := by
    apply coordinateTensor_scalarBilinear c B T _ x
    intro w
    change e (q.polarBilin (b (w 0)) (b (w 1))) = qL.polarBilin (c (w 0)) (c (w 1))
    symm
    rw [show qL.polarBilin = LinearMap.BilinForm.baseChange L q.polarBilin from
      Composition.polar_normBaseChange L q]
    change _ = algebraMap k L _
    simp [c, Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
  have ht' (x : Fin 2 → Fin n → L) :
      coordinateTensor T (fun i => M.val.mulVec (x i)) () =
        B (f (c.equivFun.symm (x 0))) (f (c.equivFun.symm (x 1))) := by
    rw [ht, mulVec_coordinates c M (x 0), mulVec_coordinates c M (x 1)]
    simp only [LinearEquiv.symm_apply_apply, f]
  have hpolar :
      (∀ x : Fin 2 → Fin n → L,
        coordinateTensor T (fun i => M.val.mulVec (x i)) = coordinateTensor T x) ↔
      (∀ x y, B (f x) (f y) = B x y) := by
    constructor
    · intro h x y
      let a : Fin 2 → Fin n → L := ![c.equivFun x, c.equivFun y]
      have ha := congrFun (h a) ()
      rw [ht', ht] at ha
      simpa only [a, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearEquiv.symm_apply_apply] using ha
    · intro h x
      funext z
      cases z
      rw [ht', ht, h]
  have hform : (∀ x y, B (f x) (f y) = B x y) ↔ ∀ x, qL (f x) = qL x := by
    constructor
    · intro h x
      have hx := h x x
      change qL.polarBilin (f x) (f x) = qL.polarBilin x x at hx
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul] at hx
      exact mul_left_cancel₀ htwo hx
    · intro h x y
      simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, h]
  have hvol :
      (∀ x : Fin n → Fin n → L,
        coordinateTensor (fun w z => e (volumeCoefficients w z))
          (fun i => M.val.mulVec (x i)) =
        coordinateTensor (fun w z => e (volumeCoefficients w z)) x) ↔ M.det = 1 := by
    rw [← volume_mulVec_iff M]
    constructor
    · intro h x
      simpa only [coordinateTensor_volume] using congrFun (h x) ()
    · intro h x
      funext z
      cases z
      simpa only [coordinateTensor_volume] using h x
  have hdet : f.det = M.det := by
    apply Units.ext
    have hm := (matrixCoordinateComparison c f 0).2
    rw [show matrixCoordinates c f = M from (matrixCoordinates c).apply_symm_apply M] at hm
    simpa only [LinearEquiv.coe_det, GeneralLinearGroup.val_det_apply] using hm.symm
  have hMem : M ∈ orthogonalMatrixModel b q L e ↔
      (∀ x, qL (f x) = qL x) ∧ M.det = 1 := by
    change (∃ g : specialOrthogonalGroup qL, matrixCoordinates c g.val = M) ↔ _
    constructor
    · rintro ⟨g, hg⟩
      have he : (g : (L ⊗[k] V) ≃ₗ[L] (L ⊗[k] V)) = f :=
        (matrixCoordinates c).injective (hg.trans ((matrixCoordinates c).apply_symm_apply M).symm)
      have hp := g.property
      change (∀ x, qL (g.val x) = qL x) ∧ g.val.det = 1 at hp
      rw [he, hdet] at hp
      exact hp
    · intro hg
      exact ⟨⟨f, hg.1, hdet.trans hg.2⟩, (matrixCoordinates c).apply_symm_apply M⟩
  rw [hMem, ← hform, ← hpolar, ← hvol]
  constructor
  · rintro ⟨hp, hv⟩
    refine ⟨fun i => i.elim, ?_⟩
    intro i
    cases i
    · exact hp
    · exact hv
  · intro h
    exact ⟨h.2 false, h.2 true⟩

set_option maxRecDepth 1200 in
theorem orthogonalCompactness : OrthogonalCompactness.{u, v} := by
  classical
  intro k _ _ V _ _ n b q hn hq ha
  let p : Unit → MvPolynomial (Fin n) k := fun _ => quadraticPolynomial b q
  obtain ⟨hhom, hnonzero, _⟩ := DivisionOctonionOrthogonalTensors.orthogonalPolynomialModel.{u, v, u}
    b q hn hq ha
  refine compactNumberTensorModel (orthogonalMatrixModel b q) p (fun _ => 2)
    (orthogonalTensors b q) (fun _ => ⟨by decide, hhom⟩)
    (fun x hx => ⟨(), hnonzero x hx⟩) (fun _ _ _ _ => orthogonal_tensor_comparison b q _ _) ?_
  intro L _ e M hM
  let : Algebra k L := e.toAlgebra
  let c := b.baseChange L
  let qL := normBaseChange L q
  change (∃ g : specialOrthogonalGroup qL, matrixCoordinates c g.val = M) at hM
  obtain ⟨g, rfl⟩ := hM
  have hp (x : Fin n → L) : (p ()).eval₂ e x = qL (c.equivFun.symm x) :=
    (quadraticPolynomialComparison b q).2 L x
  refine ⟨?_, ?_⟩
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, (matrixCoordinateComparison c g.val 0).2, ← LinearEquiv.coe_det]
    exact congrArg Units.val g.property.2
  · rintro ⟨⟩ x
    rw [hp, hp, mulVec_coordinates c, MulEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
    exact g.property.1 _

end Orthogonal

section GlobalMatrixReduction

noncomputable section

open Matrix

universe a

variable {k : Type u} [Field k] {I : Type*} [Fintype I] [DecidableEq I]

private abbrev MatrixAdeles (D : GlobalFieldData.{u, z} k) (I : Type*)
    [Fintype I] [DecidableEq I] : Type _ :=
  match D with
  | .number h => letI := h; NumberMatrixAdeles k I
  | @GlobalFieldData.function _ _ _ _ _ _ _ => FunctionMatrixAdeles k I

private instance (D : GlobalFieldData.{u, z} k) : Group (MatrixAdeles D I) := by
  cases D with
  | number h => letI := h; exact inferInstanceAs (Group (NumberMatrixAdeles k I))
  | function F t => exact inferInstanceAs (Group (FunctionMatrixAdeles k I))

private instance (D : GlobalFieldData.{u, z} k) : TopologicalSpace (MatrixAdeles D I) := by
  cases D with
  | number h => letI := h; exact inferInstanceAs (TopologicalSpace (NumberMatrixAdeles k I))
  | function F t => exact inferInstanceAs (TopologicalSpace (FunctionMatrixAdeles k I))

private def matrixAt (D : GlobalFieldData.{u, z} k) (w : D.Place) :
    MatrixAdeles D I →* GL I (D.Completion w) := by
  cases D with
  | number h =>
    letI := h
    cases w with
    | inl w => exact numberAtPlace (I := I) (.inl w)
    | inr w => exact numberAtPlace (I := I) (.inr w)
  | function F t =>
    cases w with
    | inl w => exact functionAtPlace (I := I) w
    | inr w => exact w.elim

private theorem continuous_matrixAt (D : GlobalFieldData.{u, z} k) (w : D.Place) :
    Continuous (matrixAt (I := I) D w) := by
  cases D with
  | number h =>
    letI := h
    cases w with
    | inl w => exact continuous_numberAtPlace (I := I) (.inl w)
    | inr w => exact continuous_numberAtPlace (I := I) (.inr w)
  | function F t =>
    cases w with
    | inl w => exact continuous_functionAtPlace (I := I) w
    | inr w => exact w.elim

open private continuousFinite_mul_const from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

private theorem continuous_matrixAdeles_mul_const
    (D : GlobalFieldData.{u, z} k) (r : MatrixAdeles D I) :
    Continuous (fun g : MatrixAdeles D I => g * r) := by
  cases D with
  | number h =>
    letI := h
    exact ((continuousFinite_mul_const r.1).comp continuous_fst).prodMk
      (continuous_snd.mul continuous_const)
  | function F t =>
    let B (w : FunctionPlace k) := GL I w.Completion
    let U (w : FunctionPlace k) := integralMatrices (I := I) w.integers.toSubring
    exact RestrictedProduct.mapAlong_continuous B B
      (A₁ := fun w => (U w : Set (B w))) (A₂ := fun w => (U w : Set (B w)))
      id Filter.tendsto_id (fun w (x : GL I w.Completion) => x * r w)
      (r.property.mono fun w hr _ hx => (U w).mul_mem hx hr)
      (fun _ => continuous_id.mul continuous_const)

private abbrev adelicMatrixGroup (D : GlobalFieldData.{u, z} k) (M : MatrixModel k I) :
    Subgroup (MatrixAdeles D I) :=
  localConditions (matrixAt D) (fun w => M (D.Completion w) (D.embedding w))

private theorem globalMatrixQuotient_of_reduction (D : GlobalFieldData.{u, z} k)
    (M : MatrixModel k I) (δ : GL I k →* MatrixAdeles D I)
    (hδ : ∀ r w, matrixAt D w (δ r) = GeneralLinearGroup.map (D.embedding w) r)
    (hQ : CompactMatrixQuotient (adelicMatrixGroup D M) (M k (RingHom.id k)) δ) :
    GlobalMatrixQuotientCompact D M := by
  cases D with
  | number h =>
    letI := h
    let G := adelicMatrixGroup (.number h : GlobalFieldData.{u,z} k) M
    have he : G =
        localConditions numberAtPlace (fun (w : NumberPlace k) => M w.Completion w.embedding) := by
      ext x
      simp only [G, adelicMatrixGroup, mem_localConditions]
      constructor <;> intro hx w <;> cases w
      · exact hx (.inl _)
      · exact hx (.inr _)
      · exact hx (.inl _)
      · exact hx (.inr _)
    refine ⟨δ, fun r w => ?_, he ▸ hQ⟩
    cases w with
    | inl w => exact hδ r (.inl w)
    | inr w => exact hδ r (.inr w)
  | function F t =>
    let G := adelicMatrixGroup (.function F t) M
    have he : G =
        localConditions functionAtPlace (fun (w : FunctionPlace k) => M w.Completion w.embedding) := by
      ext x
      simp only [G, adelicMatrixGroup, mem_localConditions]
      exact ⟨fun h w => h (.inl w), fun h w => by
        cases w with
        | inl w => exact h w
        | inr w => exact w.elim⟩
    exact ⟨δ, fun r w => hδ r (.inl w), he ▸ hQ⟩

private theorem compactMatrixQuotient_of_finite_labels
    {A P T : Type*} [Group A] [TopologicalSpace A] [Group P]
    (G : Subgroup A) (Γ : Subgroup P) (δ : P →* A) (C : Set A)
    (R : Set P) (label : P → T) (S : Set T) (hS : S.Finite)
    (hδ : Γ.map δ ≤ G) (hC : IsCompact C) (hG : IsClosed (G : Set A))
    (hcontinuous : ∀ a : A, Continuous (fun x : A => x * a))
    (hcompare : ∀ r ∈ R, ∀ s ∈ R, label r = label s → r * s⁻¹ ∈ Γ)
    (hreduce : ∀ g : G, ∃ r ∈ R, (g : A) * δ r ∈ C ∧ label r ∈ S) :
    CompactMatrixQuotient G Γ δ := by
  classical
  let f (g : G) := (hreduce g).choose
  have hf (g : G) := (hreduce g).choose_spec
  let L := Set.range (label ∘ f)
  have hL : L.Finite := hS.subset (by rintro _ ⟨g, rfl⟩; exact (hf g).2.2)
  letI : Finite L := hL.to_subtype
  let rep (l : L) := f l.property.choose
  let C' := ⋃ l : L, (fun x : A => x * (δ (rep l))⁻¹) '' C
  have hC' : IsCompact C' := isCompact_iUnion fun l => hC.image (hcontinuous _)
  apply compactMatrixQuotient_of_representatives G Γ δ hδ C' hC' hG
  intro g
  let l : L := ⟨label (f g), ⟨g, rfl⟩⟩
  refine ⟨f g * (rep l)⁻¹, hcompare _ (hf g).1 _ (hf l.property.choose).1
    l.property.choose_spec.symm, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨l, ((g : A) * δ (f g)), (hf g).2.1, ?_⟩
  simp only [map_mul, map_inv, mul_assoc]

variable {P J H : Type*} [Fintype P] [Finite J] [Finite H]
  {X : J → Type a} {Y : H → Type a} {O : H → Type*}
  [∀ j, Fintype (X j)] [∀ h, Fintype (Y h)] [∀ h, Finite (O h)]

set_option maxHeartbeats 700000 in
private theorem globalTensorReduction (D : GlobalFieldData.{u, z} k)
    (p : P → MvPolynomial I k) (d : P → ℕ) (T : TensorSystem k I X Y O)
    (hd : ∀ j, 0 < d j ∧ (p j).IsHomogeneous (d j))
    (ha : ∀ x, x ≠ 0 → ∃ j, (p j).eval x ≠ 0) :
    ∃ δ : GL I k →* MatrixAdeles D I,
      (∀ r w, matrixAt D w (δ r) = GeneralLinearGroup.map (D.embedding w) r) ∧
      ∃ C : Set (MatrixAdeles D I), IsCompact C ∧
        ∀ g : MatrixAdeles D I,
          (∀ w, (matrixAt D w g).det = 1) →
          (∀ j w x, (p j).eval₂ (D.embedding w) ((matrixAt D w g).val.mulVec x) =
            (p j).eval₂ (D.embedding w) x) →
          (∀ w, T.Preserves (D.embedding w) (matrixAt D w g)) →
          ∃ r : GL I k, T.Preserves (RingHom.id k) r ∧ g * δ r ∈ C := by
  cases D with
  | number h =>
    letI := h
    obtain ⟨δ, hδf, hδi, C, hC, _, hred⟩ := numberTensorAdelicReduction p d T hd ha
    refine ⟨δ, fun r w => ?_, C, hC, fun g hdet hinv hT => ?_⟩
    · cases w with
      | inl w => exact hδf r w
      | inr w => exact hδi r w
    · exact hred g (fun w => hdet (.inl w)) (fun w => hdet (.inr w))
        (fun j w x => hinv j (.inl w) x) (fun j w x => hinv j (.inr w) x)
        ⟨fun w => hT (.inl w), fun w => hT (.inr w)⟩
  | function F t =>
    obtain ⟨δ, hδ, C, hC, _, hred⟩ := functionTensorAdelicReduction t p d T hd ha
    refine ⟨δ, fun r w => ?_, C, hC, fun g hdet hinv hT => ?_⟩
    · cases w with
      | inl w => exact hδ r w
      | inr w => exact w.elim
    · exact hred g (fun w => hdet (.inl w)) (fun j w x => hinv j (.inl w) x)
        (fun w => hT (.inl w))

private theorem rational_group_in_adelic (D : GlobalFieldData.{u, z} k)
    (M : MatrixModel k I) (δ : GL I k →* MatrixAdeles D I)
    (hδ : ∀ r w, matrixAt D w (δ r) = GeneralLinearGroup.map (D.embedding w) r)
    (hmap : ∀ r ∈ M k (RingHom.id k), ∀ w,
      GeneralLinearGroup.map (D.embedding w) r ∈ M (D.Completion w) (D.embedding w)) :
    (M k (RingHom.id k)).map δ ≤ adelicMatrixGroup D M := by
  rintro _ ⟨r, hr, rfl⟩
  apply (mem_localConditions _ _ _).mpr
  intro w
  rw [hδ r w]
  exact hmap r hr w

private theorem isClosed_adelicMatrixGroup (D : GlobalFieldData.{u, z} k) (M : MatrixModel k I)
    (hM : ∀ w, IsClosed (M (D.Completion w) (D.embedding w) : Set (GL I (D.Completion w)))) :
    IsClosed (adelicMatrixGroup D M : Set (MatrixAdeles D I)) :=
  isClosed_localConditions _ _ (continuous_matrixAt D) hM

private theorem compactGlobalTensorModel (D : GlobalFieldData.{u, z} k)
    (M : MatrixModel k I) (p : P → MvPolynomial I k) (d : P → ℕ) (T : TensorSystem k I X Y O)
    (hd : ∀ j, 0 < d j ∧ (p j).IsHomogeneous (d j))
    (ha : ∀ x, x ≠ 0 → ∃ j, (p j).eval x ≠ 0)
    (hgroup : ∀ (L : Type u) [Field L] (e : k →+* L) (g : GL I L),
      g ∈ M L e ↔ T.Preserves e g)
    (hinv : ∀ (w : D.Place) (g : GL I (D.Completion w)),
      g ∈ M (D.Completion w) (D.embedding w) →
      g.det = 1 ∧ ∀ j x, (p j).eval₂ (D.embedding w) (g.val.mulVec x) =
        (p j).eval₂ (D.embedding w) x) :
    GlobalMatrixQuotientCompact D M := by
  obtain ⟨δ, hδ, C, hC, hreduce⟩ := globalTensorReduction D p d T hd ha
  let G := adelicMatrixGroup D M
  have hG (g : G) (w : D.Place) : matrixAt D w g.val ∈ M (D.Completion w) (D.embedding w) :=
    (mem_localConditions _ _ _).mp g.property w
  apply globalMatrixQuotient_of_reduction D M δ hδ
  refine compactMatrixQuotient_of_representatives G _ δ
    (rational_group_in_adelic D M δ hδ ?_) C hC (isClosed_adelicMatrixGroup D M ?_) ?_
  · intro r hr w
    exact (hgroup _ _ _).mpr (tensor_system_map T (D.embedding w) r ((hgroup _ _ _).mp hr))
  · intro w
    have h : (M (D.Completion w) (D.embedding w) : Set _) =
        {r | T.Preserves (D.embedding w) r} := Set.ext fun r => hgroup _ _ r
    rw [h]
    cases D with
    | number hk =>
      letI := hk
      cases w with
      | inl w => exact isClosed_tensor_system T (algebraMap k (w.adicCompletion k))
      | inr w => exact isClosed_tensor_system T (algebraMap k w.Completion)
    | function F t =>
      cases w with
      | inl w => exact isClosed_tensor_system T w.embedding
      | inr w => exact w.elim
  · intro g
    obtain ⟨r, hr, hgr⟩ := hreduce g.val (fun w => (hinv w _ (hG g w)).1)
      (fun j w x => (hinv w _ (hG g w)).2 j x) (fun w => (hgroup _ _ _).mp (hG g w))
    exact ⟨r, (hgroup _ _ _).mpr hr, hgr⟩

end

end GlobalMatrixReduction

section DivisionAlgebra

open Matrix
open Specs.DivisionOctonionOrthogonalTensors
open DivisionOctonionOrthogonalTensors (divisionNormOneMatrixModel divisionNormOneMatrixNaturality
  divisionStabilizerNorm divisionTensorStabilizer divisionClosedStabilizers)
open _root_.Specs.RM03.CSA (degree genericReducedNorm)

private theorem coordinateTensor_matrix {L I : Type*} [Field L] [Fintype I] [DecidableEq I]
    (R : Matrix I I L) (x : Unit → I → L) :
    coordinateTensor (fun w i => R i (w ())) x = R.mulVec (x ()) := by
  let F : MultilinearMap L (fun _ : Unit => I → L) (I → L) :=
    MultilinearMap.mk' (fun a => R.mulVec (a ()))
      (fun a i x y => by cases i; simp [Matrix.mulVec_add])
      (fun a i r x => by cases i; simp [Matrix.mulVec_smul])
  have h : coordinateTensor (fun w i => R i (w ())) = F := by
    apply coordinateTensor_of_multilinear
    intro w
    funext i
    change R i (w ()) = (R.mulVec (Pi.basisFun L I (w ()))) i
    simp only [Pi.basisFun_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [h]
  rfl

private theorem preserves_matrixTensor {L I : Type*} [Field L] [Fintype I] [DecidableEq I]
    (R : Matrix I I L) (M : GL I L) :
    PreservesTensor (fun w i => R i (w ())) M M ↔ M.val * R = R * M.val := by
  constructor
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have he := h (fun _ : Unit => Pi.single j 1)
    simpa only [coordinateTensor_matrix] using he.symm
  · intro h x
    rw [coordinateTensor_matrix, coordinateTensor_matrix,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

private theorem preserves_volumeTensor {k L I : Type*} [Field k] [Field L]
    [Fintype I] [DecidableEq I] (e : k →+* L) (M : GL I L) :
    (∀ x : I → I → L, coordinateTensor (fun w a => e (volumeCoefficients w a))
      (fun i => M.val.mulVec (x i)) =
        coordinateTensor (fun w a => e (volumeCoefficients w a)) x) ↔ M.det = 1 := by
  rw [← volume_mulVec_iff M]
  constructor
  · intro h x
    simpa only [coordinateTensor_volume] using congrFun (h x) ()
  · intro h x
    funext z
    cases z
    simpa only [coordinateTensor_volume] using h x

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B]
  {I : Type} [Fintype I] [DecidableEq I]

private noncomputable def divisionTensors (b : Module.Basis I k B) :
    TensorSystem k I (fun _ : I => Unit) (fun _ : Unit => I) (fun _ => Unit) where
  moving j w i := rightMultiplicationMatrix b (b j) i (w ())
  fixed _ := volumeCoefficients

private theorem division_tensor_comparison {L : Type u} [Field L] (e : k →+* L)
    (hB : RM03.CSA.IsCentralSimple k B) (b : Module.Basis I k B) (M : GL I L) :
    letI : Algebra k L := e.toAlgebra
    (divisionTensors b).Preserves e M ↔
      M ∈ (divisionMatrixHom (L := L) b).range ∧ M.det = 1 := by
  let : Algebra k L := e.toAlgebra
  have hs := (divisionTensorStabilizer (L := L) hB b).1 M
  constructor
  · intro h
    refine ⟨hs.mpr (fun j => ?_), (preserves_volumeTensor e M).mp (h.2 ())⟩
    exact (preserves_matrixTensor ((rightMultiplicationMatrix b (b j)).map e) M).mp (h.1 j)
  · rintro ⟨hM, hdet⟩
    refine ⟨fun j => ?_, fun _ => (preserves_volumeTensor e M).mpr hdet⟩
    exact (preserves_matrixTensor ((rightMultiplicationMatrix b (b j)).map e) M).mpr (hs.mp hM j)

private theorem divisionMapMem {L : Type u} [Field L] (e : k →+* L)
    (hB : RM03.CSA.IsCentralSimple k B) (b : Module.Basis I k B)
    (M : GL I k) (hM : M ∈ divisionMatrixModel hB b k (RingHom.id k)) :
    GeneralLinearGroup.map e M ∈ divisionMatrixModel hB b L e := by
  let : Algebra k L := e.toAlgebra
  let a : k →ₐ[k] L := Algebra.ofId k L
  change M ∈ (divisionNormOneMatrixHom (L := k) hB b).range at hM
  obtain ⟨x, rfl⟩ := hM
  exact ⟨RM03.CSA.NormOneGroup.mapNormOne hB b a x, divisionNormOneMatrixNaturality hB b a x⟩

private theorem isClosed_divisionMatrixModel {L : Type u} [Field L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] (e : k →+* L) (hB : RM03.CSA.IsCentralSimple k B)
    (b : Module.Basis I k B) : IsClosed (divisionMatrixModel hB b L e : Set (GL I L)) := by
  let : Algebra k L := e.toAlgebra
  have he : (divisionMatrixModel hB b L e : Set (GL I L)) =
      {M | M ∈ (divisionMatrixHom (L := L) b).range ∧ divisionNormInCoordinates hB b M = 1} := by
    ext M
    exact ((divisionNormOneMatrixModel (L := L) hB b).2.2.1 M).trans
      (and_congr_left fun _ => ((divisionTensorStabilizer (L := L) hB b).1 M).symm)
  rw [he]
  exact (divisionClosedStabilizers hB b).2

open private divisionCoordinateNormHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors

set_option maxHeartbeats 900000 in
theorem divisionCompactness : DivisionCompactness.{u, v, z} := by
  classical
  intro k _ D B _ _ I _ _ hB b
  let M := divisionMatrixModel hB b
  let p : Unit → MvPolynomial I k := fun _ => genericReducedNorm hB b
  let T := divisionTensors b
  obtain ⟨hd, hhom, ha⟩ := divisionNormAnisotropic hB b
  obtain ⟨δ, hδ, C, hC, hreduce⟩ := globalTensorReduction D p (fun _ => degree k B) T
    (fun _ => ⟨hd, hhom⟩) (fun x hx => ⟨(), ha x hx⟩)
  let G := adelicMatrixGroup D M
  let R : Set (GL I k) := {r | T.Preserves (RingHom.id k) r}
  let label (r : GL I k) := divisionNormInCoordinates (L := k) hB b r
  let S : Set k := {a | a ^ degree k B = 1}
  have hrange (r : GL I k) (hr : r ∈ R) :
      r ∈ (divisionMatrixHom (L := k) b).range ∧ r.det = 1 :=
    (division_tensor_comparison (RingHom.id k) hB b r).mp hr
  have hclosed (w : D.Place) :
      IsClosed (M (D.Completion w) (D.embedding w) : Set (GL I (D.Completion w))) := by
    cases D with
    | number hh =>
      let := hh
      cases w with
      | inl w => exact isClosed_divisionMatrixModel (algebraMap k (w.adicCompletion k)) hB b
      | inr w => exact isClosed_divisionMatrixModel (algebraMap k w.Completion) hB b
    | function F t =>
      cases w with
      | inl w => exact isClosed_divisionMatrixModel w.embedding hB b
      | inr w => exact w.elim
  have hlocal (g : G) (w : D.Place) :
      letI : Algebra k (D.Completion w) := (D.embedding w).toAlgebra
      (matrixAt D w g.val) ∈ (divisionMatrixHom (L := D.Completion w) b).range ∧
      (matrixAt D w g.val).det = 1 ∧ ∀ x,
        (p ()).eval₂ (D.embedding w) ((matrixAt D w g.val).val.mulVec x) =
          (p ()).eval₂ (D.embedding w) x := by
    let : Algebra k (D.Completion w) := (D.embedding w).toAlgebra
    have hg : matrixAt D w g.val ∈ M (D.Completion w) (D.embedding w) :=
      (mem_localConditions _ _ _).mp g.property w
    change matrixAt D w g.val ∈ (divisionNormOneMatrixHom hB b).range at hg
    obtain ⟨a, ha⟩ := hg
    rw [← ha]
    exact ⟨⟨normOneToUnits hB b a, rfl⟩,
      (divisionNormOneMatrixModel (L := D.Completion w) hB b).2.2.2 a⟩
  apply globalMatrixQuotient_of_reduction D M δ hδ
  apply compactMatrixQuotient_of_finite_labels G _ δ C R label S (finiteRootsOfUnity _ hd)
    (rational_group_in_adelic D M δ hδ (fun r hr w => divisionMapMem (D.embedding w) hB b r hr))
    hC (isClosed_adelicMatrixGroup D M hclosed) (continuous_matrixAdeles_mul_const D)
  · intro r hr s hs hrs
    let U := (divisionMatrixHom (L := k) b).range
    let a : U := ⟨r, (hrange r hr).1⟩
    let c : U := ⟨s, (hrange s hs).1⟩
    let ν := divisionCoordinateNormHom (L := k) hB b
    have hv : ν a = ν c := hrs
    have hnorm : divisionNormInCoordinates hB b (r * s⁻¹) = 1 := by
      change ν (a * c⁻¹) = 1
      rw [map_mul, hv, ← map_mul, mul_inv_cancel, map_one]
    have hm := (divisionNormOneMatrixModel (L := k) hB b).2.2.1 (r * s⁻¹)
    exact hm.mpr ⟨(divisionTensorStabilizer (L := k) hB b).1 _ |>.mp (a * c⁻¹).property, hnorm⟩
  · intro g
    obtain ⟨r, hr, hgr⟩ := hreduce g.val (fun w => (hlocal g w).2.1)
      (fun _ w x => (hlocal g w).2.2 x)
      (fun w => (division_tensor_comparison (D.embedding w) hB b _).mpr
        ⟨(hlocal g w).1, (hlocal g w).2.1⟩)
    refine ⟨r, hr, hgr, ?_⟩
    have he := (divisionStabilizerNorm (L := k) hB b).2.2 r (hrange r hr).1
    change label r ^ degree k B = 1
    rw [← he, ← GeneralLinearGroup.val_det_apply, (hrange r hr).2]
    rfl

end DivisionAlgebra

section LinearTensors

open Matrix
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)
open DivisionOctonionOrthogonalTensors (matrixCoordinateComparison)

open private matrix_commutes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors

private theorem matrixOfUnits_mulVec {R C V I : Type*} [CommRing R] [Ring C] [Algebra R C]
    [AddCommGroup V] [Module R V] [Fintype I] [DecidableEq I]
    (c : Module.Basis I R V) (ρ : C →ₐ[R] Module.End R V) (g : Cˣ) (x : V) :
    (matrixOfUnits c ρ g).val.mulVec (c.equivFun x) = c.equivFun (ρ g.val x) :=
  (matrixCoordinateComparison c
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R V (Units.map ρ.toMonoidHom g)) x).1

private theorem matrixOfUnits_det {R C V I : Type*} [CommRing R] [Ring C] [Algebra R C]
    [AddCommGroup V] [Module R V] [Fintype I] [DecidableEq I]
    (c : Module.Basis I R V) (ρ : C →ₐ[R] Module.End R V) (g : Cˣ) :
    (matrixOfUnits c ρ g).val.det = LinearMap.det (ρ g.val) :=
  (matrixCoordinateComparison c
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R V (Units.map ρ.toMonoidHom g)) 0).2

private theorem matrixOfUnits_eq_iff {L C V I : Type*} [Field L] [Ring C] [Algebra L C]
    [AddCommGroup V] [Module L V] [Fintype I] [DecidableEq I]
    (c : Module.Basis I L V) (ρ : C →ₐ[L] Module.End L V) (g : Cˣ) (M : GL I L) :
    matrixOfUnits c ρ g = M ↔
      ∀ x, (matrixCoordinates c).symm M x = ρ g.val x := by
  constructor
  · intro h x
    have he := matrixOfUnits_mulVec c ρ g x
    rw [h, mulVec_coordinates c M (c.equivFun x), LinearEquiv.symm_apply_apply] at he
    exact c.equivFun.injective he
  · intro h
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have h₁ := matrixOfUnits_mulVec c ρ g (c j)
    have h₂ : M.val.mulVec (c.equivFun (c j)) = c.equivFun (ρ g.val (c j)) := by
      rw [mulVec_coordinates c M (c.equivFun (c j)), LinearEquiv.symm_apply_apply, h]
    have he := congrFun (h₁.trans h₂.symm) i
    simpa only [Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Finsupp.single_eq_pi_single, Matrix.mulVec_single_one, Matrix.col_apply] using he

private theorem linearTensor_iff {L V I : Type*} [Field L] [AddCommGroup V] [Module L V]
    [Fintype I] [DecidableEq I] (c : Module.Basis I L V) (A : Module.End L V)
    (M : GL I L) (T : TensorCoefficients L Unit I I)
    (hT : ∀ w i, T w i = c.equivFun (A (c (w ()))) i) :
    PreservesTensor T M M ↔
      ∀ x, (matrixCoordinates c).symm M (A x) = A ((matrixCoordinates c).symm M x) := by
  have h : T = fun w i => (LinearMap.toMatrix c c A) i (w ()) := by
    funext w i
    rw [LinearMap.toMatrix_apply, hT]
    rfl
  rw [h, preserves_matrixTensor]
  exact (matrix_commutes_iff c M A).symm

private theorem bilinearTensor_iff {L V W I J : Type*} [Field L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (c : Module.Basis I L V) (d : Module.Basis J L W) (B : V →ₗ[L] V →ₗ[L] W)
    (M : GL I L) (T : TensorCoefficients L (Fin 2) I J)
    (hT : ∀ w, T w = d.equivFun (B (c (w 0)) (c (w 1)))) :
    (∀ x, coordinateTensor T (fun i => M.val.mulVec (x i)) = coordinateTensor T x) ↔
      ∀ x y, B ((matrixCoordinates c).symm M x) ((matrixCoordinates c).symm M y) = B x y := by
  let f := (matrixCoordinates c).symm M
  have ht (x : Fin 2 → I → L) := coordinateTensor_binary c d B T hT x
  have hm (x : Fin 2 → I → L) : coordinateTensor T (fun i => M.val.mulVec (x i)) =
      d.equivFun (B (f (c.equivFun.symm (x 0))) (f (c.equivFun.symm (x 1)))) := by
    rw [ht, mulVec_coordinates c M (x 0), mulVec_coordinates c M (x 1)]
    simp only [LinearEquiv.symm_apply_apply, f]
  constructor
  · intro h x y
    let v : Fin 2 → I → L := ![c.equivFun x, c.equivFun y]
    have hv := h v
    rw [hm v, ht v] at hv
    exact d.equivFun.injective (by simpa only [v, Matrix.cons_val_zero, Matrix.cons_val_one,
      LinearEquiv.symm_apply_apply] using hv)
  · intro h x
    rw [hm x, ht x, h]

private def rightColumnMap {R C I : Type*} [CommRing R] [Ring C] [Algebra R C] (d : C) :
    Module.End R (I → C) where
  toFun x i := x i * d
  map_add' x y := funext fun i => add_mul (x i) (y i) d
  map_smul' a x := funext fun i => smul_mul_assoc a (x i) d

private theorem columnBasis_apply {R V I J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (b : Module.Basis J R V) (ij : I × J) :
    columnBasis b ij = Pi.single ij.1 (b ij.2) := by
  apply (columnBasis b).repr.injective
  ext p
  change _ = b.repr ((show I → V from Pi.single ij.1 (b ij.2)) p.1) p.2
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : p.1 = ij.1
  · have e : ij = p ↔ ij.2 = p.2 := ⟨fun hp => congrArg Prod.snd hp, Prod.ext h.symm⟩
    simp [h, e, Finsupp.single_apply]
  · have e : ¬p = ij := fun hp => h (congrArg Prod.fst hp)
    simp [h, Ne.symm e]

end LinearTensors

section SymplecticInvolution

open scoped TensorProduct
open Matrix
open SymplecticIsometryDescent (Involution)
open AnisotropicSymplecticInvolutionTensors (globalHermitianModel symplecticTensorModel)
open Specs.AnisotropicSymplecticInvolutionTensors (HermitianModel)
open Specs.SymplecticDivisionForms (hermitianValue extendAnti intoTensor)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)

open private formLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticInvolutionTensors
open private form_pure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticInvolutionTensors

variable {k A B : Type u} [Field k] [Ring A] [Algebra k A] [DivisionRing B] [Algebra k B]
  {r : ℕ} {J : Type u} [Fintype J] [DecidableEq J]

private noncomputable def symplecticTensors {s : Involution k A}
    (m : HermitianModel (toDivisionInvolution s) r (D := B)) (b : Module.Basis J k B) :
    TensorSystem k (Fin r × J) (fun _ : J => Unit) (fun _ : Unit => Fin 2) (fun _ => J) where
  moving j w := (columnBasis b).equivFun (rightColumnMap (R := k) (I := Fin r) (b j) (columnBasis b (w ())))
  fixed _ w := b.equivFun (hermitianValue m.involution.anti m.gram.val
    (columnBasis b (w 0)) (columnBasis b (w 1)))

private theorem columnBasis_baseChange_apply {L : Type u} [Field L] [Algebra k L]
    (b : Module.Basis J k B) (ij : Fin r × J) (i : Fin r) :
    columnBasis (b.baseChange L) ij i = (1 : L) ⊗ₜ[k] columnBasis b ij i := by
  simp only [columnBasis_apply, Pi.single_apply, Module.Basis.baseChange_apply]
  split <;> simp

set_option maxHeartbeats 700000 in
set_option maxRecDepth 1800 in
private theorem symplectic_tensors_iff {s : Involution k A}
    (m : HermitianModel (toDivisionInvolution s) r (D := B)) (b : Module.Basis J k B)
    {L : Type u} [Field L] (e : k →+* L) (M : GL (Fin r × J) L) :
    letI : Algebra k L := e.toAlgebra
    let bL := b.baseChange L
    let f := (matrixCoordinates (columnBasis bL)).symm M
    let h := hermitianValue (extendAnti m.involution.anti L) (m.gram.val.map (intoTensor L B))
    (symplecticTensors m b).Preserves e M ↔
      (∀ j x, f (fun i => x i * bL j) = fun i => f x i * bL j) ∧
      ∀ x y, h (f x) (f y) = h x y := by
  letI : Algebra k L := e.toAlgebra
  let bL := b.baseChange L
  let c := columnBasis (I := Fin r) bL
  let F := formLinear (extendAnti m.involution.anti L) (m.gram.val.map (intoTensor L B))
  have hr (j : J) :
    PreservesTensor (fun w i => e ((symplecticTensors m b).moving j w i)) M M ↔
    ∀ x, (matrixCoordinates c).symm M ((rightColumnMap (R := L) (I := Fin r) (bL j)) x) =
      (rightColumnMap (R := L) (I := Fin r) (bL j)) ((matrixCoordinates c).symm M x) := by
    apply linearTensor_iff c
    intro w i
    change e (b.repr (columnBasis b (w ()) i.1 * b j) i.2) =
      bL.repr (c (w ()) i.1 * bL j) i.2
    rw [show c (w ()) i.1 = (1 : L) ⊗ₜ[k] columnBasis b (w ()) i.1 from
      columnBasis_baseChange_apply b _ _, show bL j = (1 : L) ⊗ₜ[k] b j from b.baseChange_apply _ _,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, mul_one]
    rfl
  have hform :
      (∀ x : Fin 2 → (Fin r × J) → L,
        coordinateTensor (fun w i => e ((symplecticTensors m b).fixed () w i))
          (fun j => M.val.mulVec (x j)) =
        coordinateTensor (fun w i => e ((symplecticTensors m b).fixed () w i)) x) ↔
      ∀ x y, F ((matrixCoordinates c).symm M x) ((matrixCoordinates c).symm M y) = F x y := by
    apply bilinearTensor_iff c bL F M
    intro w
    funext j
    change e (b.repr (hermitianValue m.involution.anti m.gram.val
      (columnBasis b (w 0)) (columnBasis b (w 1))) j) =
      bL.repr (hermitianValue (extendAnti m.involution.anti L) (m.gram.val.map (intoTensor L B))
        (c (w 0)) (c (w 1))) j
    have hp (a : Fin r × J) : c a = fun i => (1 : L) ⊗ₜ[k] columnBasis b a i :=
      funext (columnBasis_baseChange_apply b a)
    rw [hp, hp, form_pure, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    rfl
  change (symplecticTensors m b).Preserves e M ↔ _
  constructor
  · intro h
    exact ⟨fun j => (hr j).mp (h.1 j), hform.mp (h.2 ())⟩
  · rintro ⟨hR, hF⟩
    exact ⟨fun j => (hr j).mpr (hR j), fun h => by cases h; exact hform.mpr hF⟩

set_option maxHeartbeats 900000 in
theorem symplecticCompactness : SymplecticCompactness.{u, z} := by
  classical
  intro k A K _ D _ _ _ _ _ hA s n hsplit hanis
  obtain ⟨r, B, instB, algB, hB, ⟨m⟩⟩ := globalHermitianModel hA s hsplit hanis
  letI : DivisionRing B := instB
  letI : Algebra k B := algB
  letI : FiniteDimensional k B := hB.2
  let j := Module.finrank k B
  let b : Module.Basis (ULift.{u} (Fin j)) k B := (Module.finBasis k B).reindex Equiv.ulift.symm
  let T := symplecticTensors m b
  obtain ⟨P, E, hP, ha, hE, _, hf⟩ := symplecticTensorModel hB s hsplit m b
  refine ⟨r, B, instB, algB, hB, m, j, b, E, hE, ?_⟩
  let M := symplecticMatrixModel s b E
  apply compactGlobalTensorModel D M P (fun _ => 2) T (fun _ => ⟨by decide, hP _⟩) ha
  · intro L _ e g
    letI : Algebra k L := e.toAlgebra
    let c := columnBasis (I := Fin r) (b.baseChange L)
    let ρ := matrixColumnAction.comp (E L).toAlgHom
    have hrep : g ∈ M L e ↔
        ∃ u : (s.baseChange L).isometries, matrixOfUnits c ρ u.val = g := by
      change (∃ u ∈ (s.baseChange L).isometries, matrixOfUnits c ρ u = g) ↔ _
      exact ⟨fun ⟨u, hu, hg⟩ => ⟨⟨u, hu⟩, hg⟩, fun ⟨u, hu⟩ => ⟨u.val, u.property, hu⟩⟩
    have ht := symplectic_tensors_iff m b e g
    dsimp only at ht
    change g ∈ M L e ↔ (symplecticTensors m b).Preserves e g
    rw [hrep, ht, (hf L).2.2 ((matrixCoordinates c).symm g)]
    exact exists_congr fun u => matrixOfUnits_eq_iff c ρ u.val g
  · intro w g hg
    let L := D.Completion w
    letI : Algebra k L := (D.embedding w).toAlgebra
    let c := columnBasis (I := Fin r) (b.baseChange L)
    let ρ := matrixColumnAction.comp (E L).toAlgHom
    change (∃ u ∈ (s.baseChange L).isometries, matrixOfUnits c ρ u = g) at hg
    obtain ⟨u, hu, rfl⟩ := hg
    have h := (hf L).2.1 (⟨u, hu⟩ : (s.baseChange L).isometries)
    refine ⟨?_, fun j x => ?_⟩
    · apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, matrixOfUnits_det]
      exact h.1
    · let y := c.equivFun.symm x
      have hx : x = c.equivFun y := (c.equivFun.apply_symm_apply x).symm
      rw [hx, matrixOfUnits_mulVec]
      exact h.2 y j

end SymplecticInvolution

section SpecialUnitary

open scoped TensorProduct
open Matrix
open AnisotropicUnitaryTensors
open LinearAlgebraicGroups.UnitaryNormEquations
open _root_.Specs.RM03.CSA (degree isCentralSimple isCentralDivision reducedNorm genericReducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

open private extendForm_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
open private associateColumn_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
open private columnActionFaithful from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
open private continuous_bilinear_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors

noncomputable section

variable {k E A B : Type u} [Field k] [Field E] [Algebra k E]
    [Ring A] [Algebra k A] [Algebra E A] [IsScalarTower k E A]
    [DivisionRing B] [Algebra k B] [Algebra E B] [IsScalarTower k E B] {r n : ℕ}
    {I J S : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype S] [DecidableEq S]

private def unitaryModel (hA : isCentralSimple E A) (b : Module.Basis S E A)
    (s : SecondKind k E A) (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B)) :
    MatrixModel k I := fun L _ a =>
  letI : Algebra k L := a.toAlgebra
  (specialUnitarySubgroup (R := L) hA b s).map (unitaryMatrixRepresentation e v)

private theorem unitaryModel_mem (hA : isCentralSimple E A) (b : Module.Basis S E A)
    (s : SecondKind k E A) (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B))
    {L : Type u} [Field L] (a : k →+* L) (M : GL I L) :
    letI : Algebra k L := a.toAlgebra
    M ∈ unitaryModel hA b s e v L a ↔
      ∃ x : (L ⊗[k] A)ˣ, IsSpecialUnitary hA b s x ∧ unitaryMatrixRepresentation e v x = M :=
  Iff.rfl

private def actionCoordinates (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B)) :
    A →ₗ[k] Matrix I I k :=
  (LinearMap.toMatrix v v).toLinearMap.comp (groundColumnAction e).toLinearMap

private def extendedCoordinates {L : Type u} [Field L] [Algebra k L]
    (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B)) :
    (L ⊗[k] A) →ₗ[L] Matrix I I L :=
  (LinearMap.toMatrix (v.baseChange L) (v.baseChange L)).toLinearMap.comp
    (extendedColumnAction e).toLinearMap

private theorem extendedCoordinates_tmul {L : Type u} [Field L] [Algebra k L]
    (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B)) (a : A) (c : L) :
    extendedCoordinates e v (c ⊗ₜ[k] a) = c • (actionCoordinates e v a).map (algebraMap k L) := by
  ext i j
  change (LinearMap.toMatrix (v.baseChange L) (v.baseChange L)
    (extendedColumnAction e (c ⊗ₜ[k] a))) i j =
      c * algebraMap k L ((LinearMap.toMatrix v v (groundColumnAction e a)) i j)
  simp only [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply, extendedColumnAction_tmul,
    mul_one, Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
  exact mul_comm _ _

private theorem extendedCoordinates_injective {L : Type u} [Field L] [Algebra k L]
    (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B)) :
    Function.Injective (extendedCoordinates (L := L) e v) := by
  let f := actionCoordinates e v
  have hf : Function.Injective f := by
    intro a b h
    apply columnActionFaithful e
    have he := (LinearMap.toMatrix v v).injective h
    exact LinearMap.ext fun x => DFunLike.congr_fun he x
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let c : Module.Basis (I × I) k (Matrix I I k) := columnBasis (I := I) (Pi.basisFun k I)
  let d : Module.Basis (I × I) L (Matrix I I L) := columnBasis (I := I) (Pi.basisFun L I)
  let F := (c.baseChange L).equivFun.trans d.equivFun.symm
  have hF (X : Matrix I I k) (c₀ : L) :
      F (c₀ ⊗ₜ[k] X) = c₀ • X.map (algebraMap k L) := by
    apply d.equivFun.injective
    funext p
    change d.equivFun (d.equivFun.symm ((c.baseChange L).equivFun (c₀ ⊗ₜ[k] X))) p = _
    rw [LinearEquiv.apply_symm_apply]
    change (c.baseChange L).repr (c₀ ⊗ₜ[k] X) p =
      (Pi.basisFun L I).repr ((c₀ • X.map (algebraMap k L)) p.1) p.2
    have hx : c.repr X p = X p.1 p.2 := by
      change (Pi.basisFun k I).repr (X p.1) p.2 = _
      simp only [Pi.basisFun_repr]
    rw [Module.Basis.baseChange_repr_tmul, hx, Pi.basisFun_repr, Matrix.smul_apply, Matrix.map_apply]
    rw [Algebra.smul_def (R := k), smul_eq_mul, mul_comm]
  have hcomp : extendedCoordinates (L := L) e v = F.toLinearMap.comp (f.baseChange L) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro t a
    change extendedCoordinates (L := L) e v (t ⊗ₜ[k] a) =
      F ((f.baseChange L) (t ⊗ₜ[k] a))
    rw [extendedCoordinates_tmul, LinearMap.baseChange_tmul, hF]
  have hg' : (g.baseChange L).comp (f.baseChange L) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hg, LinearMap.baseChange_id]
  rw [hcomp]
  apply F.injective.comp
  exact Function.LeftInverse.injective (fun x =>
    show ((g.baseChange L).comp (f.baseChange L)) x = x by rw [hg']; rfl)

private theorem unitaryRepresentation_injective {L : Type u} [Field L] [Algebra k L]
    (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B)) :
    Function.Injective (unitaryMatrixRepresentation (L := L) e v) := by
  intro x y h
  apply Units.ext
  apply extendedCoordinates_injective e v
  exact congrArg Units.val h

private theorem unitaryNorm_pure {L : Type u} [Field L] [Algebra k L]
    (hA : isCentralSimple E A) (b : Module.Basis S E A) (a : A) :
    unitaryNorm hA b ((1 : L) ⊗ₜ[k] a) = (1 : L) ⊗ₜ[k] (reducedNorm hA a) := by
  letI : Algebra E (Centre k E L) := Algebra.TensorProduct.rightAlgebra
  change normAt hA b (associateCentre ((1 : L) ⊗ₜ[k] a)) = _
  rw [associateCentre_tmul]
  unfold normAt
  simp only [Module.Basis.baseChange_repr_tmul, show (1 : L) ⊗ₜ[k] (1 : E) = 1 from rfl,
    Algebra.smul_def, mul_one]
  calc
    _ = algebraMap E (Centre k E L) ((genericReducedNorm hA b).eval (fun i => b.repr a i)) :=
      (MvPolynomial.eval₂_comp (algebraMap E (Centre k E L)) (fun i => b.repr a i) _).symm
    _ = _ := by
      apply congrArg (algebraMap E (Centre k E L))
      trans reducedNorm hA (∑ i, b.repr a i • b i)
      · exact RM03.CSA.genericReducedNorm_eval hA (fun i => b i) (fun i => b.repr a i)
      · rw [b.sum_repr]

private theorem unitary_pure_mem {L : Type u} [Field L] [Algebra k L]
    (hA : isCentralSimple E A) (b : Module.Basis S E A) (s : SecondKind k E A)
    (a : Aˣ) (hiso : adj s a.val * a.val = 1) (hnorm : reducedNorm hA a.val = 1) :
    IsSpecialUnitary hA b s (Units.map (Algebra.TensorProduct.includeRight :
      A →ₐ[k] L ⊗[k] A).toMonoidHom a) := by
  change (adjointAt s ((1 : L) ⊗ₜ[k] a.val) * ((1 : L) ⊗ₜ[k] a.val) = 1) ∧
    unitaryNorm hA b ((1 : L) ⊗ₜ[k] a.val) = 1
  rw [adjointAt_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, show
    MulOpposite.unop (s.adjoint a.val) * a.val = 1 from hiso, unitaryNorm_pure, hnorm]
  exact ⟨rfl, rfl⟩

private def unitaryGroundRepresentation (e : A ≃ₐ[E] Mat r B)
    (v : Module.Basis I k (Fin r → B)) : Aˣ →* GL I k :=
  matrixOfUnits v (groundColumnAction e)

private theorem unitaryRepresentation_pure {L : Type u} [Field L] [Algebra k L]
    (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B)) (a : Aˣ) :
    unitaryMatrixRepresentation e v (Units.map (Algebra.TensorProduct.includeRight :
      A →ₐ[k] L ⊗[k] A).toMonoidHom a) =
      GeneralLinearGroup.map (algebraMap k L) (unitaryGroundRepresentation e v a) := by
  apply Units.ext
  change extendedCoordinates e v ((1 : L) ⊗ₜ[k] a.val) =
    (actionCoordinates e v a.val).map (algebraMap k L)
  rw [extendedCoordinates_tmul, one_smul]

private theorem unitary_mapMem (hA : isCentralSimple E A) (b : Module.Basis S E A)
    (s : SecondKind k E A) (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B))
    {L : Type u} [Field L] (a : k →+* L) (M : GL I k)
    (hM : M ∈ unitaryModel hA b s e v k (RingHom.id k)) :
    GeneralLinearGroup.map a M ∈ unitaryModel hA b s e v L a := by
  letI : Algebra k L := a.toAlgebra
  obtain ⟨x, hx, rfl⟩ := (unitaryModel_mem hA b s e v (RingHom.id k) M).mp hM
  let f := Algebra.ofId k L
  let y := mapSpecialUnitary hA b s f ⟨x, hx⟩
  have hbase (z : k ⊗[k] A) :
      ∃ a₀ : A, z = (1 : k) ⊗ₜ[k] a₀ := by
    let d := Algebra.TensorProduct.lid k A
    exact ⟨d z, (d.symm_apply_apply z).symm⟩
  obtain ⟨a₀, ha₀⟩ := hbase x.val
  let a₁ : Aˣ := Units.map (Algebra.TensorProduct.lid k A).toMonoidHom x
  have hx₁ : Units.map (Algebra.TensorProduct.includeRight :
      A →ₐ[k] k ⊗[k] A).toMonoidHom a₁ = x := Units.ext
    ((Algebra.TensorProduct.lid k A).symm_apply_apply x.val)
  refine ⟨y.val, y.property, ?_⟩
  have hy : y.val = Units.map (Algebra.TensorProduct.includeRight :
      A →ₐ[k] L ⊗[k] A).toMonoidHom a₁ := by
    apply Units.ext
    change RM03.CSA.NormOneGroup.changeCoefficients f x.val = (1 : L) ⊗ₜ[k] a₁.val
    rw [ha₀]
    simp [RM03.CSA.NormOneGroup.changeCoefficients, a₁, ha₀]
  rw [hy, unitaryRepresentation_pure, ← hx₁]
  rw [unitaryRepresentation_pure]
  rfl

private theorem fixedTensor_iff {L V W X Q O : Type*} [Field L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
    (c : Module.Basis Q L V) (d : Module.Basis O L W)
    (F : MultilinearMap L (fun _ : X => V) W)
    (M : GL Q L) (T : TensorCoefficients L X Q O)
    (hT : ∀ w, T w = d.equivFun (F (fun i => c (w i)))) :
    (∀ x, coordinateTensor T (fun i => M.val.mulVec (x i)) = coordinateTensor T x) ↔
      ∀ x, F (fun i => (matrixCoordinates c).symm M (x i)) = F x := by
  let P := (d.equivFun.toLinearMap.compMultilinearMap F).compLinearMap
    (fun _ : X => c.equivFun.symm.toLinearMap)
  have hP : coordinateTensor T = P := by
    apply coordinateTensor_of_multilinear
    intro w
    rw [hT]
    change _ = d.equivFun (F (fun i => c.equivFun.symm (Pi.basisFun L Q (w i))))
    simp
  let f := (matrixCoordinates c).symm M
  have hx (x : X → Q → L) :
      coordinateTensor T (fun i => M.val.mulVec (x i)) =
      d.equivFun (F (fun i => f (c.equivFun.symm (x i)))) := by
    rw [hP]
    change d.equivFun (F (fun i => c.equivFun.symm (M.val.mulVec (x i)))) = _
    simp only [mulVec_coordinates c M, LinearEquiv.symm_apply_apply, f]
  have hy (x : X → Q → L) :
      coordinateTensor T x = d.equivFun (F (fun i => c.equivFun.symm (x i))) := by
    rw [hP]
    rfl
  constructor
  · intro h x
    have he := h (fun i => c.equivFun (x i))
    rw [hx (fun i => c.equivFun (x i)), hy (fun i => c.equivFun (x i))] at he
    exact d.equivFun.injective (by simpa only [LinearEquiv.symm_apply_apply] using he)
  · intro h x
    rw [hx x, hy x, h]

private abbrev unitaryOutput (J S : Type u) : Bool → Type u
  | false => J
  | true => S

private instance (i : Bool) : Finite (unitaryOutput J S i) :=
  match i with
  | false => inferInstanceAs (Finite J)
  | true => inferInstanceAs (Finite S)

private def unitaryTensors (v : Module.Basis I k (Fin r → B)) (b : Module.Basis J k B)
    (c : Module.Basis S k E) (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B))
    (F : (Fin r → B) →ₗ[k] (Fin r → B) →ₗ[k] B) :
    TensorSystem k I (fun _ : J => Unit) (orthogonalArity n) (unitaryOutput J S) where
  moving j w := v.equivFun (rightMultiplication (K := k) (r := r) (b j) (v (w ())))
  fixed
    | false => fun w => b.equivFun (F (v (w (0 : Fin 2))) (v (w (1 : Fin 2))))
    | true => fun w => c.equivFun (vE.det (fun i => v (w i.down)))

private theorem unitary_rightTensor_iff {L : Type u} [Field L] (a : k →+* L)
    (v : Module.Basis I k (Fin r → B)) (b : Module.Basis J k B)
    (c : Module.Basis S k E) (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B))
    (F : (Fin r → B) →ₗ[k] (Fin r → B) →ₗ[k] B) (M : GL I L) (j : J) :
    letI : Algebra k L := a.toAlgebra
    let vL := v.baseChange L
    let f := (matrixCoordinates vL).symm M
    let U := (rightMultiplication (K := k) (r := r) (b j)).baseChange L
    PreservesTensor (fun w i => a ((unitaryTensors v b c vE F).moving j w i)) M M ↔
      ∀ x, f (U x) = U (f x) := by
  letI : Algebra k L := a.toAlgebra
  apply linearTensor_iff (v.baseChange L)
  intro w i
  change a (v.repr (rightMultiplication (K := k) (r := r) (b j) (v (w ()))) i) =
    (v.baseChange L).repr
      ((rightMultiplication (K := k) (r := r) (b j)).baseChange L ((v.baseChange L) (w ()))) i
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]
  rfl

private theorem unitary_formTensor_iff {L : Type u} [Field L] (a : k →+* L)
    (v : Module.Basis I k (Fin r → B)) (b : Module.Basis J k B)
    (c : Module.Basis S k E) (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B))
    (F : (Fin r → B) →ₗ[k] (Fin r → B) →ₗ[k] B) (M : GL I L) :
    letI : Algebra k L := a.toAlgebra
    let f := (matrixCoordinates (v.baseChange L)).symm M
    let T : TensorCoefficients L (Fin 2) I J := fun w j => a ((unitaryTensors v b c vE F).fixed false w j)
    (∀ x, coordinateTensor T (fun i => M.val.mulVec (x i)) = coordinateTensor T x) ↔
      ∀ x y, extendForm F (f x) (f y) = extendForm F x y := by
  letI : Algebra k L := a.toAlgebra
  apply bilinearTensor_iff (v.baseChange L) (b.baseChange L) (extendForm F)
  intro w
  funext j
  change a (b.repr (F (v (w 0)) (v (w 1))) j) =
    (b.baseChange L).repr (extendForm F ((v.baseChange L) (w 0)) ((v.baseChange L) (w 1))) j
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply, extendForm_tmul, one_mul,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

local instance (priority := 2000) {L : Type u} [Field L] [Algebra k L] : Algebra E (Centre k E L) :=
  Algebra.TensorProduct.rightAlgebra

private def unitaryVolumeMultilinear {L : Type u} [Field L] [Algebra k L]
    (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B)) :
    MultilinearMap L (fun _ : Fin n => L ⊗[k] (Fin r → B)) (Centre k E L) :=
  (((vE.baseChange (Centre k E L)).det.toMultilinearMap.restrictScalars L).compLinearMap
    (fun _ => associateColumn.toLinearMap)).domDomCongr Equiv.ulift

private theorem unitaryVolume_pure {L : Type u} [Field L] [Algebra k L]
    (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B)) (x : Fin n → Fin r → B) :
    unitaryVolumeMultilinear vE (fun i => (1 : L) ⊗ₜ[k] x i) =
      (1 : L) ⊗ₜ[k] vE.det (fun i => x i.down) := by
  change (vE.baseChange (Centre k E L)).det (fun i =>
    associateColumn ((1 : L) ⊗ₜ[k] x i.down)) =
    algebraMap E (Centre k E L) (vE.det (fun i => x i.down))
  simp only [associateColumn_tmul, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Module.Basis.baseChange_repr_tmul, show (1 : L) ⊗ₜ[k] (1 : E) = 1 from rfl,
    Algebra.smul_def, mul_one]

private theorem unitary_volumeTensor_iff {L : Type u} [Field L] (a : k →+* L)
    (v : Module.Basis I k (Fin r → B)) (b : Module.Basis J k B)
    (c : Module.Basis S k E) (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B))
    (F : (Fin r → B) →ₗ[k] (Fin r → B) →ₗ[k] B) (M : GL I L) :
    letI : Algebra k L := a.toAlgebra
    let f := (matrixCoordinates (v.baseChange L)).symm M
    let T : TensorCoefficients L (Fin n) I S := fun w j => a ((unitaryTensors v b c vE F).fixed true w j)
    (∀ x, coordinateTensor T (fun i => M.val.mulVec (x i)) = coordinateTensor T x) ↔
      ∀ x, unitaryVolumeMultilinear vE (fun i => f (x i)) = unitaryVolumeMultilinear vE x := by
  letI : Algebra k L := a.toAlgebra
  apply fixedTensor_iff (v.baseChange L) (c.baseChange L)
  intro w
  funext j
  change a (c.repr (vE.det (fun i => v (w i.down))) j) =
    (c.baseChange L).repr (unitaryVolumeMultilinear vE (fun i => (v.baseChange L) (w i))) j
  simp_rw [Module.Basis.baseChange_apply]
  rw [unitaryVolume_pure, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

set_option maxRecDepth 1200 in
private theorem unitary_rational_tensors (v : Module.Basis I k (Fin r → B))
    (b : Module.Basis J k B) (c : Module.Basis S k E)
    (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B))
    (F : (Fin r → B) →ₗ[k] (Fin r → B) →ₗ[k] B) (M : GL I k) :
    (unitaryTensors v b c vE F).Preserves (RingHom.id k) M →
      PreservesTensors b vE (fun x y => F x y) ((matrixCoordinates v).symm M) := by
  intro h
  let f := (matrixCoordinates v).symm M
  refine ⟨fun j => ?_, ?_, ?_⟩
  · apply (linearTensor_iff v (rightMultiplication (K := k) (r := r) (b j)) M _ (fun _ _ => rfl)).mp
    exact h.1 j
  · apply (bilinearTensor_iff v b F M _ (fun _ => rfl)).mp
    exact h.2 false
  · let V := (vE.det.toMultilinearMap.restrictScalars k).domDomCongr Equiv.ulift
    have hV := (fixedTensor_iff v c V M _ (fun _ => rfl)).mp (h.2 true)
    intro x
    exact hV (fun i => x (ULift.up i))

set_option maxRecDepth 1200 in
private theorem unitary_local_tensors (D : GlobalFieldData.{u, z} k) (w : D.Place)
    (hA : isCentralSimple E A) (bA : Module.Basis S E A)
    (s : SecondKind k E A) (e : A ≃ₐ[E] Mat r B) (σ : SecondKind k E B)
    (v : Module.Basis I k (Fin r → B)) (b : Module.Basis J k B)
    {S' : Type u} [Fintype S'] [DecidableEq S'] (c : Module.Basis S' k E)
    (vE : Module.Basis (ULift.{u} (Fin n)) E (Fin r → B)) (hB : isCentralDivision E B)
    (F : (Fin r → B) →ₗ[k] (Fin r → B) →ₗ[k] B)
    (hF : IsHermitianForm s e σ (fun x y => F x y))
    (M : GL I (D.Completion w)) (hM : M ∈ unitaryModel hA bA s e v _ (D.embedding w)) :
    (unitaryTensors v b c vE F).Preserves (D.embedding w) M ∧
      M.det = 1 ∧ ∀ j x, (diagonalPolynomial v b F j).eval₂ (D.embedding w) (M.val.mulVec x) =
        (diagonalPolynomial v b F j).eval₂ (D.embedding w) x := by
  let L := D.Completion w
  letI : Algebra k L := (D.embedding w).toAlgebra
  let cL := v.baseChange L
  obtain ⟨x, hx, rfl⟩ := (unitaryModel_mem hA bA s e v (D.embedding w) M).mp hM
  let M := unitaryMatrixRepresentation (L := L) e v x
  have hf (y : L ⊗[k] (Fin r → B)) :
      (matrixCoordinates cL).symm M y = extendedColumnAction e x.val y :=
    (matrixOfUnits_eq_iff cL (extendedColumnAction e) x M).mp rfl y
  have hBilin := completionInvariance D w hA bA s e σ F hF v b x hx
  have hV (y : Fin n → L ⊗[k] (Fin r → B)) :
      unitaryVolumeMultilinear vE (fun i => (matrixCoordinates cL).symm M (y i)) =
        unitaryVolumeMultilinear vE y := by
    simp only [hf]
    exact completionVolumeInvariance D w hA hB bA s e vE x hx (fun i => y i.down)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro j
    apply (unitary_rightTensor_iff (D.embedding w) v b c vE F M j).mpr
    intro y
    let U := (rightMultiplication (K := k) (r := r) (b j)).baseChange L
    change (matrixCoordinates cL).symm M (U y) = U ((matrixCoordinates cL).symm M y)
    rw [hf, hf]
    exact DFunLike.congr_fun (completionRightMultiplication D w e x.val (b j)).eq y
  · intro i
    cases i
    · exact (unitary_formTensor_iff (D.embedding w) v b c vE F M).mpr
        (fun y z => by
          change extendForm F ((matrixCoordinates cL).symm M y) ((matrixCoordinates cL).symm M z) =
            extendForm F y z
          rw [hf, hf]
          exact hBilin.1 y z)
    · exact (unitary_volumeTensor_iff (D.embedding w) v b c vE F M).mpr hV
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, unitaryMatrixRepresentation, matrixOfUnits_det]
    exact completionDeterminantOne D w hA hB bA s e x hx
  · intro j y
    let Y := cL.equivFun.symm y
    have hy : y = cL.equivFun Y := (cL.equivFun.apply_symm_apply y).symm
    rw [hy, unitaryMatrixRepresentation, matrixOfUnits_mulVec]
    exact hBilin.2 Y j

private theorem continuous_linear_coordinates {L V W X Y : Type*} [Field L]
    [TopologicalSpace L] [IsTopologicalRing L] [AddCommGroup V] [Module L V]
    [AddCommGroup W] [Module L W] [Fintype X] [Fintype Y]
    (b : Module.Basis X L V) (c : Module.Basis Y L W) (f : V →ₗ[L] W) :
    Continuous (fun x : X → L => c.equivFun (f (b.equivFun.symm x))) := by
  apply continuous_pi
  intro j
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

private theorem isClosed_unitary_coordinates {L : Type u} [Field L] [Algebra k L]
    [TopologicalSpace L] [IsTopologicalRing L] [T2Space L]
    (hA : isCentralSimple E A) (b : Module.Basis S E A) (s : SecondKind k E A)
    {Q T : Type u} [Fintype Q] [DecidableEq Q] [Fintype T] [DecidableEq T]
    (bA : Module.Basis Q k A) (bE : Module.Basis T k E) :
    let a := (bA.baseChange L).equivFun.symm
    IsClosed {x : Q → L | adjointAt s (a x) * a x = 1 ∧ unitaryNorm hA b (a x) = 1} := by
  let cA := bA.baseChange L
  let cE := bE.baseChange L
  let a := cA.equivFun.symm
  let tE : TopologicalSpace (Centre k E L) := TopologicalSpace.induced cE.equivFun inferInstance
  letI : TopologicalSpace (Centre k E L) := tE
  have hcE : IsEmbedding cE.equivFun := ⟨⟨rfl⟩, cE.equivFun.injective⟩
  letI : T2Space (Centre k E L) := hcE.t2Space
  letI : IsTopologicalRing (Centre k E L) :=
    { continuous_add := by
        apply hcE.continuous_iff.mpr
        change Continuous (fun p : Centre k E L × Centre k E L => cE.equivFun (p.1 + p.2))
        simp only [map_add]
        exact (hcE.continuous.comp continuous_fst).add (hcE.continuous.comp continuous_snd)
      continuous_neg := by
        apply hcE.continuous_iff.mpr
        change Continuous (fun x : Centre k E L => cE.equivFun (-x))
        simp only [map_neg]
        exact hcE.continuous.neg
      continuous_mul := by
        apply hcE.continuous_iff.mpr
        change Continuous (fun p : Centre k E L × Centre k E L => cE.equivFun (p.1 * p.2))
        have h := (continuous_bilinear_coordinates cE
          (LinearMap.mul L (Centre k E L))).comp
          ((hcE.continuous.comp continuous_fst).prodMk (hcE.continuous.comp continuous_snd))
        change Continuous (fun p : Centre k E L × Centre k E L =>
          cE.equivFun (LinearMap.mul L (Centre k E L) p.1 p.2))
        simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h }
  let adjL : (L ⊗[k] A) →ₗ[L] (L ⊗[k] A) :=
    { toFun := adjointAt s
      map_add' := fun x y => by simp [adjointAt]
      map_smul' := fun t x => by simp [adjointAt] }
  have hAdj : Continuous (fun x : Q → L => cA.equivFun (adjointAt s (a x) * a x)) := by
    have h := (continuous_bilinear_coordinates cA (LinearMap.mul L (L ⊗[k] A))).comp
      ((continuous_linear_coordinates cA cA adjL).prodMk continuous_id)
    change Continuous (fun x : Q → L =>
      cA.equivFun (LinearMap.mul L (L ⊗[k] A) (adjL (a x)) (a x)))
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply, id_eq] using h
  have hcoeff (i : S) (x : Q → L) :
      (b.baseChange (Centre k E L)).repr (associateCentre (a x)) i =
        ∑ j, ((x j) ⊗ₜ[k] (1 : E)) * algebraMap E (Centre k E L) (b.repr (bA j) i) := by
    have ha : a x = ∑ j, (x j) ⊗ₜ[k] bA j := by
      simp only [a, cA, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [ha, map_sum, associateCentre_tmul, Finsupp.finsetSum_apply,
      Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]
  have htmul (j : Q) : Continuous (fun x : Q → L => (x j) ⊗ₜ[k] (1 : E)) :=
    hcE.continuous_iff.mpr (continuous_pi fun i => by
      change Continuous (fun x : Q → L => (bE.baseChange L).repr ((x j) ⊗ₜ[k] (1 : E)) i)
      simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
      exact continuous_const.mul (continuous_apply j))
  have hNorm : Continuous (fun x : Q → L => unitaryNorm hA b (a x)) := by
    change Continuous (fun x : Q → L =>
      (genericReducedNorm hA b).eval₂ (algebraMap E (Centre k E L))
        (fun i => (b.baseChange (Centre k E L)).repr (associateCentre (a x)) i))
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    apply (MvPolynomial.continuous_eval _).comp
    exact continuous_pi fun i => by
      simp only [hcoeff]
      exact continuous_finsetSum _ fun j _ => (htmul j).mul continuous_const
  change IsClosed {x : Q → L | adjointAt s (a x) * a x = 1 ∧ unitaryNorm hA b (a x) = 1}
  have h : {x : Q → L | adjointAt s (a x) * a x = 1 ∧ unitaryNorm hA b (a x) = 1} =
      {x | cA.equivFun (adjointAt s (a x) * a x) = cA.equivFun 1} ∩
      {x | unitaryNorm hA b (a x) = 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, EmbeddingLike.apply_eq_iff_eq]
  rw [h]
  exact (isClosed_eq hAdj continuous_const).inter (isClosed_eq hNorm continuous_const)

set_option maxHeartbeats 750000 in
private theorem isClosed_unitaryModel {L : Type u} [Field L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] (a : k →+* L)
    (hA : isCentralSimple E A) (b : Module.Basis S E A) (s : SecondKind k E A)
    (e : A ≃ₐ[E] Mat r B) (v : Module.Basis I k (Fin r → B))
    {Q T : Type u} [Fintype Q] [DecidableEq Q] [Fintype T] [DecidableEq T]
    (bA : Module.Basis Q k A) (bE : Module.Basis T k E) :
    IsClosed (unitaryModel hA b s e v L a : Set (GL I L)) := by
  letI : Algebra k L := a.toAlgebra
  let c := bA.baseChange L
  let m : Module.Basis (I × I) L (Matrix I I L) := columnBasis (I := I) (Pi.basisFun L I)
  let F := extendedCoordinates (L := L) e v
  have hF := extendedCoordinates_injective (L := L) e v
  obtain ⟨f, hf⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hF)
  have hleft (x : L ⊗[k] A) : f (F x) = x := DFunLike.congr_fun hf x
  have hc : Continuous (fun M : GL I L => m.equivFun M.val) := by
    apply continuous_pi
    intro p
    change Continuous (fun M : GL I L => M.val p.1 p.2)
    exact (continuous_apply p.2).comp (GeneralLinearGroup.continuous_apply _ continuous_id p.1)
  have hd : Continuous (fun M : GL I L => c.equivFun (f M.val)) := by
    have h := (continuous_linear_coordinates m c f).comp hc
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h
  have he : Continuous (fun M : GL I L => m.equivFun (F (f M.val))) := by
    have h := (continuous_linear_coordinates c m F).comp hd
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h
  have hclosed : IsClosed {M : GL I L | F (f M.val) = M.val} := by
    have hz : {M : GL I L | F (f M.val) = M.val} =
        {M : GL I L | m.equivFun (F (f M.val)) = m.equivFun M.val} :=
      Set.ext fun M => show F (f M.val) = M.val ↔
        m.equivFun (F (f M.val)) = m.equivFun M.val from
        ⟨fun h => congrArg m.equivFun h, fun h => m.equivFun.injective h⟩
    rw [hz]
    exact isClosed_eq he hc
  let C := {z : Q → L |
    adjointAt s (c.equivFun.symm z) * c.equivFun.symm z = 1 ∧
      unitaryNorm hA b (c.equivFun.symm z) = 1}
  have hC : IsClosed C := isClosed_unitary_coordinates hA b s bA bE
  have hset : (unitaryModel hA b s e v L a : Set (GL I L)) =
      ({M | F (f M.val) = M.val} ∩ (fun M : GL I L => M⁻¹) ⁻¹' {M | F (f M.val) = M.val}) ∩
        (fun M : GL I L => c.equivFun (f M.val)) ⁻¹' C := by
    ext M
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, C,
      LinearEquiv.symm_apply_apply]
    rw [show M ∈ (unitaryModel hA b s e v L a : Set (GL I L)) ↔
      ∃ x : (L ⊗[k] A)ˣ, IsSpecialUnitary hA b s x ∧ unitaryMatrixRepresentation e v x = M from
      unitaryModel_mem hA b s e v a M]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have he (x : (L ⊗[k] A)ˣ) : (unitaryMatrixRepresentation e v x).val = F x.val := rfl
      rw [← map_inv, he, he, hleft, hleft]
      exact ⟨⟨rfl, rfl⟩, hx⟩
    · rintro ⟨⟨hm, hn⟩, hcond⟩
      let ρ := extendedColumnAction (K := k) (R := L) e
      let Fhom := (LinearMap.toMatrixAlgEquiv (v.baseChange L)).toAlgHom.comp ρ
      have hmul (x y : L ⊗[k] A) : F (x * y) = F x * F y := Fhom.map_mul x y
      have h1 : F 1 = 1 := Fhom.map_one
      let x : (L ⊗[k] A)ˣ :=
        { val := f M.val
          inv := f (M⁻¹ : GL I L).val
          val_inv := hF (by rw [hmul, hm, hn, h1]; exact M.val_inv)
          inv_val := hF (by rw [hmul, hm, hn, h1]; exact M.inv_val) }
      exact ⟨x, hcond, Units.ext hm⟩
  rw [hset]
  exact (hclosed.inter (hclosed.preimage continuous_inv)).inter (hC.preimage hd)

private theorem unitary_isometry_div {k E A : Type u} [Field k] [Field E] [Algebra k E]
    [Ring A] [Algebra k A] [Algebra E A]
    (s : SecondKind k E A) (a b : Aˣ)
    (ha : adj s a.val * a.val = 1) (hb : adj s b.val * b.val = 1) :
    adj s (a * b⁻¹).val * (a * b⁻¹).val = 1 := by
  have ha' : adj s a.val = a⁻¹.val :=
    (Units.mul_left_inj a).mp (ha.trans a.inv_val.symm)
  have hb' : adj s b.val = b⁻¹.val :=
    (Units.mul_left_inj b).mp (hb.trans b.inv_val.symm)
  have hb'' : adj s b⁻¹.val = b.val := by
    rw [← hb']
    exact s.adjoint_adjoint b.val
  change adj s (a.val * b⁻¹.val) * (a.val * b⁻¹.val) = 1
  have hh : adj s (a.val * b⁻¹.val) = adj s b⁻¹.val * adj s a.val := by
    simp [adj, map_mul, MulOpposite.unop_mul]
  rw [hh, hb'', ha']
  calc
    _ = b.val * (((a⁻¹ : Aˣ).val * a.val) * (b⁻¹ : Aˣ).val) := by simp only [mul_assoc]
    _ = 1 := by
      rw [show (a⁻¹ : Aˣ).val * a.val = 1 from a.inv_val, one_mul,
        show b.val * (b⁻¹ : Aˣ).val = 1 from b.val_inv]

set_option maxHeartbeats 1100000 in
theorem unitaryCompactness : UnitaryCompactness.{u, z} := by
  classical
  intro k E A _ D _ _ _ _ _ _ _ hKE I _ hA hdegree bA s H hH hanis
  obtain ⟨r, B, instB, algB, hB, hr, hdegB, _, e, x, p, i, τ, G, hcorner, hGram, hHerm,
    F, hF, hAnis⟩ := anisotropicHermitianModel hKE hA hdegree bA s H hH hanis
  letI : DivisionRing B := instB
  letI : Algebra E B := algB
  letI : Algebra k B := Algebra.compHom B (algebraMap k E)
  letI : IsScalarTower k E B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional k E := Module.finite_of_finrank_pos (by rw [hKE]; decide)
  letI : FiniteDimensional E B := hB.2
  letI : FiniteDimensional E A := hA.2.2
  letI : FiniteDimensional k B := FiniteDimensional.trans k E B
  letI : FiniteDimensional k A := FiniteDimensional.trans k E A
  let V := Fin r → B
  let j := Module.finrank k V
  let n := Module.finrank E V
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank k B))) k B :=
    (Module.finBasis k B).reindex Equiv.ulift.symm
  let c : Module.Basis (ULift.{u} (Fin (Module.finrank k E))) k E :=
    (Module.finBasis k E).reindex Equiv.ulift.symm
  let bK : Module.Basis (ULift.{u} (Fin (Module.finrank k A))) k A :=
    (Module.finBasis k A).reindex Equiv.ulift.symm
  let v : Module.Basis (ULift.{u} (Fin j)) k V := (Module.finBasis k V).reindex Equiv.ulift.symm
  let vE : Module.Basis (ULift.{u} (Fin n)) E V := (Module.finBasis E V).reindex Equiv.ulift.symm
  let M := unitaryModel hA bA s e v
  refine ⟨r, B, instB, algB, hB, e, x, p, i, τ, G, hcorner, hGram,
    fun y hy => hF y y ▸ hAnis y hy, j, v, M, ?_, ?_⟩
  · intro L _ a
    letI : Algebra k L := a.toAlgebra
    exact ⟨unitaryRepresentation_injective e v, fun g => unitaryModel_mem hA bA s e v a g⟩
  let T := unitaryTensors v b c vE F
  let P := diagonalPolynomial v b F
  have hForms : IsHermitianForm s e τ (fun x y => F x y) := by
    have he : (fun x y => F x y) = form τ G.val := funext fun y => funext (hF y)
    rw [he]
    exact hHerm
  obtain ⟨hp, _, _, ha⟩ := diagonalCoordinates v b F
  obtain ⟨δ, hδ, C, hC, hreduce⟩ := globalTensorReduction D P (fun _ => 2) T
    (fun l => ⟨by decide, hp l⟩) (fun z hz => by
      let y := v.equivFun.symm z
      have hy : y ≠ 0 := fun h => hz (v.equivFun.apply_symm_apply z ▸
        (show v.equivFun y = 0 by simp [h]))
      obtain ⟨l, hl⟩ := ha hAnis y hy
      change (P l).eval (v.equivFun (v.equivFun.symm z)) ≠ 0 at hl
      rw [v.equivFun.apply_symm_apply] at hl
      exact ⟨l, hl⟩)
  let GroupA := adelicMatrixGroup D M
  let R : Set (GL (ULift.{u} (Fin j)) k) := {g | T.Preserves (RingHom.id k) g}
  have hRep (g : GL (ULift.{u} (Fin j)) k) (hg : g ∈ R) :
      ∃ a : Aˣ, (∀ y, (matrixCoordinates v).symm g y = columnAction e a.val y) ∧
        adj s a.val * a.val = 1 ∧ reducedNorm hA a.val ^ degree E B = 1 :=
    tensorStabilizerNorm hA hB s e τ _ hForms b vE _
      (unitary_rational_tensors v b c vE F g hg)
  let a (g : GL (ULift.{u} (Fin j)) k) := if hg : g ∈ R then (hRep g hg).choose else 1
  have haRep (g : GL (ULift.{u} (Fin j)) k) (hg : g ∈ R) :
      unitaryGroundRepresentation e v (a g) = g ∧
        adj s (a g).val * (a g).val = 1 ∧ reducedNorm hA (a g).val ^ degree E B = 1 := by
    dsimp only [a]
    rw [dite_eq_left hg]
    have he := (hRep g hg).choose_spec
    exact ⟨(matrixOfUnits_eq_iff v (groundColumnAction e) _ _).mpr he.1, he.2⟩
  let label (g : GL (ULift.{u} (Fin j)) k) := reducedNorm hA (a g).val
  let Z : Set E := {z | z ^ degree E B = 1}
  have hclosed (w : D.Place) :
      IsClosed (M (D.Completion w) (D.embedding w) : Set (GL (ULift.{u} (Fin j)) (D.Completion w))) := by
    cases D with
    | number hk =>
      let := hk
      cases w with
      | inl w => exact isClosed_unitaryModel (algebraMap k (w.adicCompletion k)) hA bA s e v bK c
      | inr w => exact isClosed_unitaryModel (algebraMap k w.Completion) hA bA s e v bK c
    | function K t =>
      cases w with
      | inl w => exact isClosed_unitaryModel w.embedding hA bA s e v bK c
      | inr w => exact w.elim
  apply globalMatrixQuotient_of_reduction D M δ hδ
  apply compactMatrixQuotient_of_finite_labels GroupA _ δ C R label Z (finiteRootsOfUnity _ hdegB)
    (rational_group_in_adelic D M δ hδ (fun g hg w => unitary_mapMem hA bA s e v (D.embedding w) g hg))
    hC (isClosed_adelicMatrixGroup D M hclosed) (continuous_matrixAdeles_mul_const D)
  · intro g hg l hl he
    let b := a g * (a l)⁻¹
    have hν : reducedNorm hA b.val = 1 := by
      let x := a g
      let y := a l
      calc
        reducedNorm hA b.val = reducedNorm hA x.val * reducedNorm hA y⁻¹.val :=
          RM03.CSA.reducedNorm_mul hA x.val y⁻¹.val
        _ = reducedNorm hA y.val * reducedNorm hA y⁻¹.val :=
          congrArg (fun z => z * reducedNorm hA y⁻¹.val) he
        _ = reducedNorm hA (y.val * y⁻¹.val) :=
          (RM03.CSA.reducedNorm_mul hA y.val y⁻¹.val).symm
        _ = 1 := (congrArg (reducedNorm hA) y.val_inv).trans (RM03.CSA.reducedNorm_one hA)
    have hU := unitary_isometry_div s (a g) (a l) (haRep g hg).2.1 (haRep l hl).2.1
    let j : Aˣ →* (k ⊗[k] A)ˣ := Units.map (Algebra.TensorProduct.includeRight :
      A →ₐ[k] k ⊗[k] A).toMonoidHom
    apply (unitaryModel_mem hA bA s e v (RingHom.id k) _).mpr
    refine ⟨j b, unitary_pure_mem hA bA s b hU hν, ?_⟩
    rw [show j b = _ from rfl, unitaryRepresentation_pure]
    change GeneralLinearGroup.map (RingHom.id k) (unitaryGroundRepresentation e v b) = _
    simp only [GeneralLinearGroup.map_id, MonoidHom.id_apply, b, map_mul, map_inv,
      (haRep g hg).1, (haRep l hl).1]
  · intro g
    have hAt (w : D.Place) := unitary_local_tensors D w hA bA s e τ v b c vE hB F hForms
      (matrixAt D w g.val) ((mem_localConditions _ _ _).mp g.property w)
    obtain ⟨l, hl, hgl⟩ := hreduce g.val (fun w => (hAt w).2.1)
      (fun j w y => (hAt w).2.2 j y) (fun w => (hAt w).1)
    exact ⟨l, hl, hgl, (haRep l hl).2.2⟩

end

end SpecialUnitary

end LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
