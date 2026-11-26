import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianArchimedeanIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

open AlgebraicGeometry CategoryTheory Opposite Topology
open scoped TensorProduct Matrix

/-!
# Archimedean isotropy for nontrialitarian spin groups

Isotropic projectors give split cocharacters through the spin covering. At a
real place, a definite scalar model gives a compact neutral isometry group,
and compactness pulls back along the finite covering.
-/

universe u

namespace LinearAlgebraicGroups.Arithmetic.NontrialitarianArchimedeanIsotropy

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Arithmetic.NontrialitarianArchimedeanIsotropy (ArchimedeanIsotropy)
open Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel IsOrthogonal gramAdjoint)
open Specs.Arithmetic.QuaternionSpinIsotropy (PureLine)
open Specs.Arithmetic.IsotropicSpinGeneration (IsIsotropic)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open AdelicGroups (LocalPoints PointsIn)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (isCentralSimple isCentralDivision degree)

open private scalarExtendOrthogonal scalarIsotropicProjector isotropicProjector
  orthogonalProjectors IsOrthogonalProjector spinCocharacterOfProjector
  transferFieldPresentation cancelFieldEquiv divisionRingOfEquiv
  pureLine_of_unique realDivisionPresentation skew_isotropy_of_pureLine rightColumn_finrank
  definite_of_real_anisotropic continuous_vectorPoint_linear vectorPoint
  spinScaling projectorUnits diagonalValue diagonalValue_mul_projector
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
open private scalarMatrixBaseChange matrixBaseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open private noncentral_of_ne_zero arithmetic_absolute_simplicity
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

private theorem isotropic_of_squares {F : Type u} [Field F] [CharZero F]
    (hsq : ∀ a : F, ∃ b : F, b ^ 2 = a) {r : ℕ} (hr : 2 ≤ r) (q : QuadraticForm F (Fin r → F)) : IsIsotropic q := by
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨a, ⟨e⟩⟩ := q.equivalent_weightedSumSquares
  have hd : Module.finrank F (Fin r → F) = r := by simp
  let j : Fin (Module.finrank F (Fin r → F)) := ⟨0, by omega⟩
  let l : Fin (Module.finrank F (Fin r → F)) := ⟨1, by omega⟩
  have hlj : l ≠ j := by intro h; exact Nat.one_ne_zero (congrArg Fin.val h)
  classical
  by_cases h : a l = 0
  · let x : Fin (Module.finrank F (Fin r → F)) → F := Pi.single l 1
    refine ⟨e.symm x, ?_, ?_⟩
    · intro hz
      have hx : x = 0 := e.symm.injective (hz.trans e.symm.map_zero.symm)
      exact (one_ne_zero : (1 : F) ≠ 0) (by simpa [x] using congrFun hx l)
    · rw [e.symm.map_app]
      simp [QuadraticMap.weightedSumSquares_apply, x, Pi.single_apply, h]
  · obtain ⟨z, hz⟩ := hsq (-(a j) / a l)
    let x : Fin (Module.finrank F (Fin r → F)) → F := Pi.single j 1 + Pi.single l z
    refine ⟨e.symm x, ?_, ?_⟩
    · intro hz'
      have hx : x = 0 := e.symm.injective (hz'.trans e.symm.map_zero.symm)
      exact (one_ne_zero : (1 : F) ≠ 0) (by simpa [x, hlj.symm] using congrFun hx j)
    · rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply,
        ← Finset.sum_erase_add _ _ (Finset.mem_univ j),
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ l⟩)]
      have hsum : ∑ m ∈ (Finset.univ.erase j).erase l, a m • (x m * x m) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        have hm' := Finset.mem_erase.mp hm
        simp [x, hm'.1, (Finset.mem_erase.mp hm'.2).1]
      rw [hsum]
      simp only [x, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hlj,
        Pi.single_eq_of_ne hlj.symm, zero_add, add_zero, smul_eq_mul, ← pow_two, hz]
      field_simp
      ring

section Models

variable {k L I F : Type u} [Field k] [Field L] [Algebra k L]
  [Fintype I] [DecidableEq I] [Field F] [Algebra k F]
  {ρ : AlgebraAction k L (Matrix (I ⊕ I) (I ⊕ I) L)}
  {G : AffineAlgebraicGroup k} {Q : DescendedQuadraticPair ρ}

private theorem degree_baseChange (Q : DescendedQuadraticPair ρ) :
    degree F (F ⊗[k] ρ.fixedSubalgebra) = 2 * Fintype.card I :=
  (congrArg Nat.sqrt (_root_.RM03.CSA.finrank_baseChange (L := F) Q.centralSimple)).trans Q.degree

private theorem split_matrix_size {A : Type u} [Ring A] [Algebra F A]
    (hA : isCentralSimple F A) {r : ℕ} (hr : 0 < r)
    (E : A ≃ₐ[F] Matrix (Fin r) (Fin r) F) : degree F A = r := by
  have hdF : degree F F = 1 := by change Nat.sqrt (Module.finrank F F) = 1; simp
  have hdim := _root_.RM03.CSA.degree_matrix_division hA
    (show isCentralDivision F F from ⟨inferInstance, inferInstance⟩) hr E
  change degree F A = r * degree F F at hdim
  simpa only [hdF, mul_one] using hdim

private theorem complex_projector (R : F ≃+* ℂ) (hn : 4 ≤ Fintype.card I)
    (ho : IsOrthogonal (toDivisionInvolution Q.involution)) :
    ∃ e : F ⊗[k] ρ.fixedSubalgebra, e ≠ 0 ∧
      IsOrthogonalProjector (Q.involution.baseChange F) e := by
  classical
  letI : Algebra F ℂ := R.toRingHom.toAlgebra
  letI : Algebra ℂ F := R.symm.toRingHom.toAlgebra
  letI : CharZero F := charZero_of_injective_ringHom (f := R.symm.toRingHom) R.symm.injective
  have hsq (a : F) : ∃ z : F, z ^ 2 = a := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (R a) zero_lt_two
    exact ⟨R.symm z, R.injective (by simpa only [map_pow, R.apply_symm_apply] using hz)⟩
  let A := F ⊗[k] ρ.fixedSubalgebra
  let σ := Q.involution.baseChange F
  have hA : isCentralSimple F A := _root_.RM03.CSA.isCentralSimple_baseChange Q.centralSimple
  have hAC : isCentralSimple ℂ (ℂ ⊗[F] A) := _root_.RM03.CSA.isCentralSimple_baseChange hA
  obtain ⟨r, hr, ⟨E⟩⟩ := NontrialitarianSpinModels.archimedeanDivision.2 hAC
  let e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F := (transferFieldPresentation R E).trans
    (scalarMatrixBaseChange (F := ℂ) (R := F) (Fin r))
  have hsize : r = 2 * Fintype.card I :=
    (split_matrix_size hA hr e).symm.trans (degree_baseChange (F := F) (Q := Q))
  have hs := scalarExtendOrthogonal (F := F) Q.involution ho
  obtain ⟨H, q, _, hpolar, _, hadj⟩ :=
    NontrialitarianSpinModels.fieldOrthogonalModel r (two_ne_zero : (2 : F) ≠ 0)
      hA (toDivisionInvolution σ) hs e
  have hr₂ : 2 ≤ r := by
    rw [hsize]
    exact (by decide : 2 ≤ 2 * 4).trans (Nat.mul_le_mul_left 2 hn)
  obtain ⟨p, hp, hpp, hσp⟩ :=
    scalarIsotropicProjector σ e H q hadj hpolar (isotropic_of_squares hsq hr₂ q)
  exact orthogonalProjectors σ two_ne_zero hp hpp hσp

private theorem real_projector_or_definite (R : F ≃+* ℝ) (hn : 4 ≤ Fintype.card I)
    (ho : IsOrthogonal (toDivisionInvolution Q.involution)) :
    (∃ e : F ⊗[k] ρ.fixedSubalgebra, e ≠ 0 ∧ IsOrthogonalProjector (Q.involution.baseChange F) e) ∨
    (∃ (r : ℕ) (E : (F ⊗[k] ρ.fixedSubalgebra) ≃ₐ[F] Matrix (Fin r) (Fin r) F)
        (H : (Matrix (Fin r) (Fin r) F)ˣ) (q : QuadraticForm F (Fin r → F)),
      q.polarBilin = Matrix.toLinearMap₂' F H.val ∧
      (∀ z, E ((Q.involution.baseChange F).toLinearMap z) = gramAdjoint H (E z)) ∧
      ((∀ x, x ≠ 0 → 0 < R (q x)) ∨ (∀ x, x ≠ 0 → R (q x) < 0))) := by
  classical
  letI : Algebra F ℝ := R.toRingHom.toAlgebra
  letI : Algebra ℝ F := R.symm.toRingHom.toAlgebra
  letI : CharZero F := charZero_of_injective_ringHom (f := R.symm.toRingHom) R.symm.injective
  let A := F ⊗[k] ρ.fixedSubalgebra
  let σ := Q.involution.baseChange F
  let s := toDivisionInvolution σ
  have hs := scalarExtendOrthogonal (F := F) Q.involution ho
  have h₂ : (2 : F) ≠ 0 := two_ne_zero
  have hA : isCentralSimple F A := _root_.RM03.CSA.isCentralSimple_baseChange Q.centralSimple
  have hdeg := degree_baseChange (F := F) (Q := Q)
  have hAR : isCentralSimple ℝ (ℝ ⊗[F] A) := _root_.RM03.CSA.isCentralSimple_baseChange hA
  have lift (hp : ∃ p : A, p ≠ 0 ∧ p * p = p ∧ σ.toLinearMap p * p = 0) :
      ∃ e : A, e ≠ 0 ∧ IsOrthogonalProjector σ e := by
    obtain ⟨p, hp, hpp, hσp⟩ := hp
    exact orthogonalProjectors σ h₂ hp hpp hσp
  obtain ⟨r, hr, hE | hE⟩ := NontrialitarianSpinModels.archimedeanDivision.1 hAR
  · obtain ⟨E⟩ := hE
    let e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F := (transferFieldPresentation R E).trans
      (scalarMatrixBaseChange (F := ℝ) (R := F) (Fin r))
    obtain ⟨H, q, _, hpolar, _, hadj⟩ :=
      NontrialitarianSpinModels.fieldOrthogonalModel r h₂ hA s hs e
    by_cases hq : IsIsotropic q
    · exact Or.inl (lift (scalarIsotropicProjector σ e H q hadj hpolar hq))
    · exact Or.inr ⟨r, e, H, q, hpolar, hadj, definite_of_real_anisotropic R q hq⟩
  · obtain ⟨E⟩ := hE
    let B := F ⊗[ℝ] Quaternion ℝ
    letI : DivisionRing B := divisionRingOfEquiv (cancelFieldEquiv R.symm).toRingEquiv
    have hH : isCentralSimple ℝ (Quaternion ℝ) := _root_.RM03.CSA.isCentralSimple_of_isCentralDivision
      ℝ (Quaternion ℝ) _root_.RM03.Brauer.QuaternionSplitting.hamilton_central_division
    have hB : isCentralSimple F B := _root_.RM03.CSA.isCentralSimple_baseChange hH
    have hdB : degree F B = 2 := by
      change Nat.sqrt (Module.finrank F B) = 2
      rw [_root_.RM03.CSA.finrank_baseChange hH, Quaternion.finrank_eq_four]
      exact Nat.sqrt_eq' 2
    let e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B := (transferFieldPresentation R E).trans
      (matrixBaseChange (F := ℝ) (R := F) (Fin r))
    have hsize : r = Fintype.card I := by
      have hd := _root_.RM03.CSA.degree_matrix_division hA hB.2 hr e
      change degree F A = r * degree F B at hd
      rw [hdeg, hdB] at hd
      omega
    obtain ⟨b, H, hb, _, hadj, ⟨h, hh⟩, _, _⟩ :=
      NontrialitarianSpinModels.quaternionSkewModel r h₂ hA s hs hB hdB e
    have hlines : PureLine b :=
      pureLine_of_unique b (hB := hB) hb h₂ (fun C _ _ hC hdC => realDivisionPresentation R hC hdC)
    have hdim : 4 ≤ Module.finrank Bᵐᵒᵖ (Fin r → B) := by
      simpa [rightColumn_finrank, hsize] using hn
    obtain ⟨x, hx, hxx⟩ := skew_isotropy_of_pureLine h (hB := hB) hdB h₂ hlines hdim
    exact Or.inl (lift (isotropicProjector σ b e H hadj x hx (by rw [← hh]; exact hxx)))

private theorem noncentral_cocharacter_of_projector [CharZero k] [CharZero F]
    (M : SpinModel G Q) (hG : Specs.AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G)
    {e : F ⊗[k] ρ.fixedSubalgebra} (he₀ : e ≠ 0)
    (he : IsOrthogonalProjector (Q.involution.baseChange F) e) :
    ∃ c : Cocharacter (baseChangedAlgebraicGroup F G).val, IsNoncentral c := by
  let t : Fˣ := Units.mk0 2 two_ne_zero
  have ht : (t : F) ^ 16 ≠ 1 := by norm_num [t]
  obtain ⟨c, hc⟩ := spinCocharacterOfProjector M two_ne_zero he₀ he t ht
  have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension G (F := F)
    (arithmetic_absolute_simplicity hG)
  exact ⟨c, noncentral_of_ne_zero _ hJ.1 c hc⟩

private theorem noncompact_of_complex_projector [CharZero k] [TopologicalSpace F]
    [IsTopologicalRing F] (M : SpinModel G Q) (i : MatrixRealization G)
    (R : F ≃+* ℂ) (hR : Continuous R)
    {e : F ⊗[k] ρ.fixedSubalgebra} (he₀ : e ≠ 0)
    (he : IsOrthogonalProjector (Q.involution.baseChange F) e) :
    ¬ CompactSpace (PointsIn i F) := by
  intro hc
  classical
  obtain ⟨d, b, _⟩ := M.reducedNormOne (two_ne_zero : (2 : k) ≠ 0)
  let β := b.baseChange F
  obtain ⟨j, hj⟩ : ∃ j, β.repr e j ≠ 0 := by
    by_contra! h
    apply he₀
    apply β.repr.injective
    ext i
    simpa using h i
  let l : (F ⊗[k] ρ.fixedSubalgebra) →ₗ[F] F := (β.repr e j)⁻¹ • β.coord j
  have hl : l e = 1 := inv_mul_cancel₀ hj
  let ℓ := l.comp (LinearMap.mulRight F e)
  let f (g : PointsIn i F) := (R (ℓ (vectorPoint M (CommAlgCat.of k F) g).val)).re
  have hfc : Continuous f :=
    Complex.continuous_re.comp (hR.comp (continuous_vectorPoint_linear M i ℓ))
  obtain ⟨m, hm⟩ := (isCompact_univ.image hfc).bddAbove
  let t₀ := max (m + 1) (2 : ℝ)
  have h₁ : 1 ≤ t₀ := le_trans (by norm_num) (le_max_right _ _)
  have ht₀ : (t₀ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one h₁)
  let t : Fˣ := Units.mk0 (R.symm (t₀ : ℂ)) (fun hh => ht₀ (by simpa using congrArg R hh))
  obtain ⟨g, hg, _⟩ := spinScaling M (two_ne_zero : (2 : k) ≠ 0)
  let p : PointsIn i F := g (CommAlgCat.of k F) he t
  have hp : f p = t₀ ^ 16 := by
    change (R (l ((vectorPoint M (CommAlgCat.of k F) p).val * e))).re = _
    rw [hg (CommAlgCat.of k F) e he t]
    change (R (l (diagonalValue e ((Q.involution.baseChange F).toLinearMap e) (t ^ 16) * e))).re = _
    rw [diagonalValue_mul_projector he.1 he.2.2, map_smul, hl, smul_eq_mul, mul_one]
    simp [t, Units.val_pow_eq_pow_val, ← Complex.ofReal_pow]
  have hle : f p ≤ m := hm ⟨p, Set.mem_univ p, rfl⟩
  rw [hp] at hle
  apply (not_lt_of_ge hle)
  calc
    m < t₀ := lt_of_lt_of_le (lt_add_one m) (le_max_left _ _)
    _ ≤ t₀ ^ 16 := by
      simpa only [pow_one] using pow_le_pow_right₀ h₁ (by decide : (1 : ℕ) ≤ 16)

end Models

section Compactness

open AdelicGroups (asMatrix)
open SymplecticIsometryDescent (tensorMap tensorMap_involution)

open private tensorMap_injective neutralPoints_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
open private pairBasis_repr_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
open private coordinateMap coordinateMap_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private matrixPresentation asMatrix_isClosedEmbedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private compactLocalBasisBox
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
open private compact_local_preimage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism

variable {k L I F : Type u} [Field k] [Field L] [Algebra k L]
  [Fintype I] [DecidableEq I] [Field F] [Algebra k F]
  {ρ : AlgebraAction k L (Matrix (I ⊕ I) (I ⊕ I) L)}
  {G : AffineAlgebraicGroup k} {Q : DescendedQuadraticPair ρ}

/-- The coefficients of the universal neutral isometry generate its coordinate algebra.
The neutral equations descend to the subalgebra generated by those coefficients. -/
private theorem neutral_coordinates_generate (M : SpinModel G Q)
    {d : ℕ} (b : Module.Basis (Fin d) k ρ.fixedSubalgebra)
    (hnorm : ∀ (T : TestAlgebra k) (g : (T ⊗[k] ρ.fixedSubalgebra)ˣ),
      (∃ a : Points M.neutral.val.X T, M.fullPoints T (a ≫ M.inclusion.hom.hom) = g) ↔
        (Q.involution.baseChange T).toLinearMap g.val * g.val = 1 ∧
        MvPolynomial.eval₂ (algebraMap k T) (fun i => (b.baseChange T).repr g.val i)
          (_root_.Specs.RM03.CSA.genericReducedNorm Q.centralSimple b) = 1)
    (B : TestAlgebra k) (E : (testSpec k).obj (op B) ≅ M.neutral.val.X) :
    Function.Surjective (MvPolynomial.aeval (fun i => (b.baseChange B).repr
      (M.fullPoints B (E.hom ≫ M.inclusion.hom.hom)).val i) : MvPolynomial (Fin d) k →ₐ[k] B) := by
  classical
  let z := M.fullPoints B (E.hom ≫ M.inclusion.hom.hom)
  let φ : MvPolynomial (Fin d) k →ₐ[k] B := MvPolynomial.aeval fun i => (b.baseChange B).repr z.val i
  change Function.Surjective φ
  let C := CommAlgCat.of k φ.range
  let f : C ⟶ B := CommAlgCat.ofHom φ.range.val
  have hf : Function.Injective f.hom := Subtype.val_injective
  let y (i : Fin d) : C := ⟨(b.baseChange B).repr z.val i, MvPolynomial.X i, MvPolynomial.aeval_X _ _⟩
  let w : C ⊗[k] ρ.fixedSubalgebra :=
    (b.baseChange C).repr.symm (Finsupp.equivFunOnFinite.symm y)
  have hw (i : Fin d) : (b.baseChange C).repr w i = y i := by simp [w]
  have hz : tensorMap f w = z.val := by
    apply (b.baseChange B).repr.injective
    ext i
    rw [pairBasis_repr_natural, hw]
    rfl
  let σ := (Q.involution.baseChange C).toLinearMap
  have hzrel := (hnorm B z).mp ⟨E.hom, rfl⟩
  have hleft : σ w * w = 1 := by
    apply tensorMap_injective f hf
    rw [map_mul, map_one, tensorMap_involution, hz]
    exact hzrel.1
  have hright : w * σ w = 1 := by
    apply tensorMap_injective f hf
    rw [map_mul, map_one, tensorMap_involution, hz]
    have he := congrArg (· * z.inv) hzrel.1
    rw [mul_assoc, z.val_inv, mul_one, one_mul] at he
    rw [he, z.val_inv]
  let u : (C ⊗[k] ρ.fixedSubalgebra)ˣ := ⟨w, σ w, hright, hleft⟩
  have hnormC :
      MvPolynomial.eval₂ (algebraMap k C) (fun i => (b.baseChange C).repr u.val i)
        (_root_.Specs.RM03.CSA.genericReducedNorm Q.centralSimple b) = 1 := by
    apply hf
    rw [map_one]
    change f.hom.toRingHom (MvPolynomial.eval₂ (algebraMap k C)
      (fun i => (b.baseChange C).repr w i) _) = 1
    rw [MvPolynomial.hom_eval₂]
    change MvPolynomial.eval₂ (f.hom.toRingHom.comp (algebraMap k C))
      (fun i => f.hom ((b.baseChange C).repr w i)) _ = 1
    have hcomp : f.hom.toRingHom.comp (algebraMap k C) = algebraMap k B :=
      f.hom.comp_algebraMap
    rw [hcomp]
    simpa only [← pairBasis_repr_natural, hz] using hzrel.2
  obtain ⟨a, ha⟩ := (hnorm C u).mpr ⟨hleft, hnormC⟩
  have he : mapPoints f a = E.hom := by
    apply neutralPoints_injective M B
    change M.fullPoints B (mapPoints f (a ≫ M.inclusion.hom.hom)) = z
    rw [M.fullNatural, ha]
    exact Units.ext hz
  let v := coordinateMap (k := k) (a ≫ E.inv)
  have heq : v ≫ f = 𝟙 B := by
    apply Quiver.Hom.op_inj
    apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    rw [op_comp, Functor.map_comp, coordinateMap_spec, CategoryTheory.op_id]
    change (mapPoints f a) ≫ E.inv = (testSpec k).map (𝟙 (op B))
    rw [he, E.hom_inv_id, CategoryTheory.Functor.map_id]
  intro t
  have h := congrArg (fun e : B ⟶ B => e.hom t) heq
  change (v.hom t).val = t at h
  exact h ▸ (v.hom t).property

private theorem compact_definite_matrix_container {r : ℕ}
    [TopologicalSpace F] [IsTopologicalRing F]
    (R : F ≃+* ℝ) (hR : IsHomeomorph R)
    (H : (Matrix (Fin r) (Fin r) F)ˣ) (q : QuadraticForm F (Fin r → F))
    (hpolar : q.polarBilin = Matrix.toLinearMap₂' F H.val)
    (hdef : (∀ x, x ≠ 0 → 0 < R (q x)) ∨ (∀ x, x ≠ 0 → R (q x) < 0)) :
    ∃ B : Set (Matrix (Fin r) (Fin r) F), IsCompact B ∧
      ∀ T, gramAdjoint H T * T = 1 → T ∈ B := by
  classical
  let h := hR.homeomorph R
  have hi : Continuous R.symm := by
    convert h.symm.continuous using 1
    ext x
    apply R.injective
    have hh : R (h.symm x) = x := h.apply_symm_apply x
    exact (R.apply_symm_apply x).trans hh.symm
  letI : CharZero F := charZero_of_injective_ringHom (f := R.symm.toRingHom) R.symm.injective
  let v (x : Fin r → ℝ) : Fin r → F := fun j => R.symm (x j)
  let p (x : Fin r → ℝ) := R (q (v x))
  have hp (x : Fin r → ℝ) :
      p x = R ((2 : F)⁻¹) * R (v x ⬝ᵥ (H.val *ᵥ v x)) := by
    have hb := congrArg (fun B : (Fin r → F) →ₗ[F] (Fin r → F) →ₗ[F] F => B (v x) (v x)) hpolar
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, Matrix.toLinearMap₂'_apply'] at hb
    rw [two_nsmul, ← two_mul] at hb
    have he : q (v x) = (2 : F)⁻¹ * (v x ⬝ᵥ (H.val *ᵥ v x)) := by
      rw [← hb, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
    change R (q (v x)) = _
    rw [he, map_mul]
  have hpcont : Continuous p := by
    rw [funext hp]
    simp only [v, dotProduct, Matrix.mulVec]
    exact continuous_const.mul (hR.continuous.comp
      (continuous_finsetSum _ fun j _ => (hi.comp (continuous_apply j)).mul
        (continuous_finsetSum _ fun l _ => continuous_const.mul (hi.comp (continuous_apply l)))))
  have hpsmul (c : ℝ) (x : Fin r → ℝ) : p (c • x) = c ^ 2 * p x := by
    have hv : v (c • x) = R.symm c • v x := by
      ext j
      simp [v, Pi.smul_apply, smul_eq_mul]
    simp [p, hv, q.map_smul, smul_eq_mul, pow_two]
  have hpos (x : Fin r → ℝ) (hx : x ≠ 0) : 0 < |p x| := by
    have hv : v x ≠ 0 := by
      intro hz
      apply hx
      ext j
      exact R.symm.injective (by simpa [v] using congrFun hz j)
    rcases hdef with hpos | hneg
    · exact abs_pos.mpr (ne_of_gt (hpos _ hv))
    · exact abs_pos.mpr (ne_of_lt (hneg _ hv))
  have column_set (j : Fin r) :
      ∃ C : Set (Fin r → ℝ), IsCompact C ∧
        ∀ x, p x = R (q (Pi.single j 1)) → x ∈ C := by
    let S := Metric.sphere (0 : Fin r → ℝ) 1
    have hS : S.Nonempty := by
      refine ⟨Pi.single j 1, ?_⟩
      simp [S, Pi.norm_single]
    obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : Fin r → ℝ) 1).exists_isMinOn hS
      hpcont.abs.continuousOn
    let δ := |p y|
    have hy' : ‖y‖ = 1 := by simpa [S, Metric.mem_sphere, dist_eq_norm] using hy
    have hδ : 0 < δ := hpos y (by intro h0; simp [h0] at hy')
    let c := |R (q (Pi.single j 1))|
    refine ⟨Metric.closedBall 0 (max 1 (c / δ)), isCompact_closedBall _ _, ?_⟩
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_cases hsmall : ‖x‖ ≤ 1
    · exact hsmall.trans (le_max_left _ _)
    have hlarge : 1 < ‖x‖ := lt_of_not_ge hsmall
    have hₓ : 0 < ‖x‖ := zero_lt_one.trans hlarge
    let z := ‖x‖⁻¹ • x
    have hz : z ∈ S := by
      rw [show z ∈ S ↔ ‖z‖ = 1 by simp [S]]
      rw [show ‖z‖ = ‖x‖⁻¹ * ‖x‖ from norm_smul_of_nonneg (inv_nonneg.mpr hₓ.le) x,
        inv_mul_cancel₀ (ne_of_gt hₓ)]
    have hmul : ‖x‖ • z = x := by
      rw [show z = ‖x‖⁻¹ • x from rfl, smul_smul, mul_inv_cancel₀ (ne_of_gt hₓ), one_smul]
    have hscale : c = ‖x‖ ^ 2 * |p z| := by
      have hval : p x = ‖x‖ ^ 2 * p z := (congrArg p hmul).symm.trans (hpsmul ‖x‖ z)
      rw [show c = |p x| from congrArg abs hx.symm, hval, abs_mul,
        abs_of_nonneg (sq_nonneg _)]
    have hb : δ * ‖x‖ ≤ c := by
      calc
        δ * ‖x‖ ≤ δ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hδ.le
        _ ≤ ‖x‖ ^ 2 * |p z| := by rw [mul_comm δ]; exact mul_le_mul_of_nonneg_left (hmin hz) (sq_nonneg _)
        _ = c := hscale.symm
    exact ((le_div_iff₀ hδ).mpr (by simpa [mul_comm] using hb)).trans (le_max_right _ _)
  choose C hC hmem using column_set
  let S : Set (∀ j, Fin r → ℝ) := Set.univ.pi C
  let f (x : ∀ j, Fin r → ℝ) : Matrix (Fin r) (Fin r) F := fun i j => R.symm (x j i)
  have hf : Continuous f := continuous_pi fun i => continuous_pi fun j =>
    hi.comp ((continuous_apply i).comp (continuous_apply j))
  refine ⟨f '' S, (isCompact_univ_pi hC).image hf, ?_⟩
  intro T hT
  have hT' : T.transpose * H.val * T = H.val := by
    have eq := congrArg (H.val * ·) hT
    change H.val * ((H.inv * T.transpose * H.val) * T) = H.val * 1 at eq
    simpa only [← mul_assoc, H.val_inv, one_mul, mul_one] using eq
  have hpres (x : Fin r → F) : q (T *ᵥ x) = q x := by
    have he : (T *ᵥ x) ⬝ᵥ (H.val *ᵥ (T *ᵥ x)) = x ⬝ᵥ (H.val *ᵥ x) := by
      calc
        (T *ᵥ x) ⬝ᵥ (H.val *ᵥ (T *ᵥ x)) =
            x ⬝ᵥ (T.transpose *ᵥ (H.val *ᵥ (T *ᵥ x))) := by
          rw [Matrix.dotProduct_mulVec x T.transpose, Matrix.vecMul_transpose]
        _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT']
    rw [← Matrix.toLinearMap₂'_apply', ← Matrix.toLinearMap₂'_apply', ← hpolar,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, QuadraticMap.polar_self] at he
    rw [two_nsmul, two_nsmul, ← two_mul, ← two_mul] at he
    exact mul_left_cancel₀ (two_ne_zero : (2 : F) ≠ 0) he
  refine ⟨fun j i => R (T i j), ?_, ?_⟩
  · intro j _
    apply hmem j
    have hv : v (fun i => R (T i j)) = T *ᵥ Pi.single j 1 := by
      ext i
      simp [v, Matrix.col_apply]
    change R (q (v (fun i => R (T i j)))) = _
    rw [hv, hpres]
  · ext i j
    exact R.symm_apply_apply _

private theorem neutral_compact_of_definite [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    (M : SpinModel G Q) (h₂ : (2 : k) ≠ 0) (j : MatrixRealization M.neutral)
    (R : F ≃+* ℝ) (hR : IsHomeomorph R)
    {r : ℕ} (E : (F ⊗[k] ρ.fixedSubalgebra) ≃ₐ[F] Matrix (Fin r) (Fin r) F)
    (H : (Matrix (Fin r) (Fin r) F)ˣ) (q : QuadraticForm F (Fin r → F))
    (hpolar : q.polarBilin = Matrix.toLinearMap₂' F H.val)
    (hadj : ∀ z, E ((Q.involution.baseChange F).toLinearMap z) = gramAdjoint H (E z))
    (hdef : (∀ x, x ≠ 0 → 0 < R (q x)) ∨ (∀ x, x ≠ 0 → R (q x) < 0)) :
    IsCompact (Set.univ : Set (PointsIn j F)) := by
  classical
  obtain ⟨B, hB, hmemB⟩ := compact_definite_matrix_container R hR H q hpolar hdef
  obtain ⟨d, b, hn⟩ := M.reducedNormOne h₂
  obtain ⟨C, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr M.neutral.prop.1
  obtain ⟨a, _, ha⟩ := matrixPresentation C.unop e j
  let S := CommAlgCat.of k F
  let y (g : PointsIn j F) := (M.fullPoints S (g ≫ M.inclusion.hom.hom)).val
  let z := (M.fullPoints C.unop (e.hom ≫ M.inclusion.hom.hom)).val
  let ev (g : PointsIn j F) : C.unop ⟶ S := coordinateMap (g ≫ e.inv)
  have hy (g : PointsIn j F) : y g = tensorMap (ev g) z := by
    have hg : g = mapPoints (ev g) e.hom := by
      change g = (testSpec k).map (ev g).op ≫ e.hom
      rw [coordinateMap_spec]
      simp
    change (M.fullPoints S (g ≫ M.inclusion.hom.hom)).val = _
    conv_lhs => rw [hg]
    rw [show (mapPoints (ev g) e.hom) ≫ M.inclusion.hom.hom =
      mapPoints (ev g) (e.hom ≫ M.inclusion.hom.hom) from Category.assoc ..,
      M.fullNatural]
    rfl
  have hz (g : PointsIn j F) (l : Fin d) :
      (ev g).hom ((b.baseChange C.unop).repr z l) = (b.baseChange F).repr (y g) l := by
    rw [hy]
    exact (pairBasis_repr_natural b (ev g) z l).symm
  have hval (g : PointsIn j F) : E (y g) ∈ B := by
    apply hmemB
    have hg := ((hn S (M.fullPoints S (g ≫ M.inclusion.hom.hom))).mp ⟨g, rfl⟩).1
    rw [← hadj, ← map_mul]
    exact congrArg E hg |>.trans (map_one E)
  let f (T : Matrix (Fin r) (Fin r) F) (l : Fin d) :=
    (b.baseChange F).repr (E.symm T) l
  have hf (l : Fin d) : Continuous (fun T => f T l) := by
    let ℓ := (b.baseChange F).coord l ∘ₗ E.symm.toLinearMap
    have hfml (T : Matrix (Fin r) (Fin r) F) :
        f T l = ∑ i, ∑ j, T i j * ℓ (Matrix.single i j 1) := by
      change ℓ T = _
      conv_lhs => rw [Matrix.matrix_eq_sum_single T]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [show Matrix.single i j (T i j) = T i j • Matrix.single i j 1 by
        rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    rw [funext hfml]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((continuous_apply j).comp (continuous_apply i)).mul_const _)
  have hentry (l m : Specs.Unipotent.Index.{u} j.size) :
      ∃ V : Set F, IsCompact V ∧ ∀ g : PointsIn j F, (asMatrix j F g).val l m ∈ V := by
    obtain ⟨p, hp⟩ := neutral_coordinates_generate M b hn C.unop e
      (a.hom (Specs.StandardGroups.universalMatrix k _ l m))
    let f' (T : Matrix (Fin r) (Fin r) F) := MvPolynomial.eval₂ (algebraMap k F) (f T) p
    have hf' : Continuous f' := by
      simp only [f', MvPolynomial.eval₂_eq]
      exact continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_finsetProd _
        fun j _ => (hf j).pow _)
    refine ⟨f' '' B, hB.image hf', fun g => ⟨E (y g), hval g, ?_⟩⟩
    have heq := DFunLike.congr_fun (ha F g) (Specs.StandardGroups.universalMatrix k _ l m)
    rw [glEvaluation_entry] at heq
    change (asMatrix j F g).val l m = (ev g).hom (a.hom (Specs.StandardGroups.universalMatrix k _ l m)) at heq
    rw [heq, ← hp]
    change MvPolynomial.eval₂ (algebraMap k F) (f (E (y g))) p =
      (ev g).hom.toRingHom (MvPolynomial.eval₂ (algebraMap k C.unop) (fun i => (b.baseChange C.unop).repr z i) p)
    rw [MvPolynomial.hom_eval₂]
    change _ = MvPolynomial.eval₂ ((ev g).hom.toRingHom.comp (algebraMap k C.unop))
      (fun i => (ev g).hom ((b.baseChange C.unop).repr z i)) p
    have hcomp : (ev g).hom.toRingHom.comp (algebraMap k C.unop) = algebraMap k F :=
      (ev g).hom.comp_algebraMap
    rw [hcomp]
    simp only [hz, f, AlgEquiv.symm_apply_apply]
  choose V hV hentries using hentry
  let A := ⋃ l, ⋃ m, V l m
  have hA : IsCompact A := isCompact_iUnion fun l => isCompact_iUnion (hV l)
  have hbox := (asMatrix_isClosedEmbedding j F).isCompact_preimage
    (compactLocalBasisBox (I := Specs.Unipotent.Index.{u} j.size) A hA)
  apply hbox.of_isClosed_subset isClosed_univ
  intro g _
  have hm (g : PointsIn j F) (l m : Specs.Unipotent.Index.{u} j.size) :
      (asMatrix j F g).val l m ∈ A :=
    Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨m, hentries l m g⟩⟩
  refine ⟨hm g, fun l m => ?_⟩
  simpa only [map_inv] using hm g⁻¹ l m

private theorem spin_compact_of_definite (D : GlobalFieldData.{u, u} k) (w : D.Place)
    (M : SpinModel G Q) (h₂ : (2 : k) ≠ 0) (i : MatrixRealization G)
    (R : D.Completion w ≃+* ℝ) (hR : IsHomeomorph R)
    {r : ℕ} (E : (D.Completion w ⊗[k] ρ.fixedSubalgebra) ≃ₐ[D.Completion w]
      Matrix (Fin r) (Fin r) (D.Completion w))
    (H : (Matrix (Fin r) (Fin r) (D.Completion w))ˣ)
    (q : QuadraticForm (D.Completion w) (Fin r → D.Completion w))
    (hpolar : q.polarBilin = Matrix.toLinearMap₂' (D.Completion w) H.val)
    (hadj : ∀ z, E ((Q.involution.baseChange (D.Completion w)).toLinearMap z) = gramAdjoint H (E z))
    (hdef : (∀ x, x ≠ 0 → 0 < R (q x)) ∨ (∀ x, x ≠ 0 → R (q x) < 0)) :
    CompactSpace (LocalPoints D i w) := by
  obtain ⟨n, A, ⟨p⟩, f, hf⟩ := LinearAlgebraicGroups.faithfulLinearization k M.neutral
  let j : MatrixRealization M.neutral := ⟨n, A, p, f, hf⟩
  have hC := neutral_compact_of_definite M h₂ j R hR E H q hpolar hadj hdef
  have hc := compact_local_preimage D w M.projection M.centralIsogeny.1 i j Set.univ hC
  exact ⟨by simpa using hc⟩

end Compactness

private theorem real_or_complex_completion {k : Type u} [Field k] [hK : NumberField k]
    (D : GlobalFieldData.{u,u} k) (hD : D = .number hK) (w : D.InfinitePlace) :
    (∃ R : D.Completion (.inr w) ≃+* ℝ, IsHomeomorph R) ∨
    (∃ R : D.Completion (.inr w) ≃+* ℂ, IsHomeomorph R) := by
  subst D
  rcases w.isReal_or_isComplex with hr | hc
  · obtain ⟨R, hR⟩ := numberRealCompletion w hr
    let R' : w.Completion ≃ᵢ ℝ := ⟨R.toEquiv, hR⟩
    exact Or.inl ⟨R, R'.toHomeomorph.isHomeomorph⟩
  · obtain ⟨R, hR⟩ := numberComplexCompletion w hc
    let R' : w.Completion ≃ᵢ ℂ := ⟨R.toEquiv, hR⟩
    exact Or.inr ⟨R, R'.toHomeomorph.isHomeomorph⟩

/-- A noncompact archimedean spin factor has positive split rank, and a complex
completion always gives a noncompact factor. -/
theorem archimedeanIsotropy : ArchimedeanIsotropy.{u} := by
  classical
  intro k L I _ hK _ _ _ _ _ _ _ G hG C Q M hn ho D hD i w
  letI : CharZero (D.Completion (.inr w)) :=
    charZero_of_injective_algebraMap (algebraMap k (D.Completion (.inr w))).injective
  constructor
  · intro hnc
    rcases real_or_complex_completion D hD w with ⟨R, hR⟩ | ⟨R, _⟩
    · rcases real_projector_or_definite (Q := Q) R hn ho with ⟨e, he₀, he⟩ | ⟨r, E, H, q, hp, ha, hd⟩
      · exact noncentral_cocharacter_of_projector M hG he₀ he
      · exact (hnc (spin_compact_of_definite D (.inr w) M two_ne_zero i R hR
          E H q hp ha hd)).elim
    · obtain ⟨e, he₀, he⟩ := complex_projector (Q := Q) R hn ho
      exact noncentral_cocharacter_of_projector M hG he₀ he
  · intro R hR
    obtain ⟨e, he₀, he⟩ := complex_projector (Q := Q) R hn ho
    exact noncompact_of_complex_projector M i R hR.continuous he₀ he

end

end LinearAlgebraicGroups.Arithmetic.NontrialitarianArchimedeanIsotropy
