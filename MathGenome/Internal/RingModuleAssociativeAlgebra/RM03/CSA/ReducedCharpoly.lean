import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedCharpoly
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Descent and specialization of the reduced characteristic polynomial. -/

namespace RM03.CSA

open scoped TensorProduct
open Algebra.TensorProduct
open Specs.RM03.CSA (genericMatrix mapGeneric)

universe u v w z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]

private theorem algebraMap_commute_matrix {n : ℕ}
    (l : L) (M : Matrix (Fin n) (Fin n) L) :
    Commute ((Algebra.ofId L (Matrix (Fin n) (Fin n) L)) l) M :=
  Algebra.commutes l M

/-- A map from the original algebra to matrices over an extension determines a
splitting when the matrix size is the degree. -/
private noncomputable def splittingOfHom (hA : IsCentralSimple k A)
    (f : A →ₐ[k] Matrix (Fin (degree k A)) (Fin (degree k A)) L) :
    BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L := by
  let g := Algebra.TensorProduct.lift (Algebra.ofId L _) f
    (fun l a => algebraMap_commute_matrix l (f a))
  let hL := isCentralSimple_baseChange (L := L) hA
  letI : IsSimpleRing (BaseChange k L A) := hL.1
  letI : FiniteDimensional L (BaseChange k L A) := hL.2.2
  letI : Nonempty (Fin (degree k A)) := Fin.pos_iff_nonempty.mp (degree_pos hA)
  have hinj : Function.Injective g := g.toRingHom.injective
  have hdim : Module.finrank L (BaseChange k L A) =
      Module.finrank L (Matrix (Fin (degree k A)) (Fin (degree k A)) L) := by
    rw [finrank_baseChange hA, finrank_eq_degree_sq hA, Module.finrank_matrix]
    simp [pow_two]
  exact AlgEquiv.ofBijective g ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

private theorem splittingOfHom_tmul (hA : IsCentralSimple k A)
    (f : A →ₐ[k] Matrix (Fin (degree k A)) (Fin (degree k A)) L) (a : A) :
    splittingOfHom hA f (1 ⊗ₜ[k] a) = f a := by
  change Algebra.TensorProduct.lift (Algebra.ofId L _) f
    (fun l b => algebraMap_commute_matrix l (f b)) (1 ⊗ₜ[k] a) = f a
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

private def splittingHom {n : ℕ}
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    A →ₐ[k] Matrix (Fin n) (Fin n) L :=
  (e.toAlgHom.restrictScalars k).comp includeRight

private theorem genericMatrix_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (M : ι → Matrix (Fin n) (Fin n) R) :
    (genericMatrix M).map (MvPolynomial.map f) = genericMatrix (fun i => (M i).map f) := by
  ext j l
  simp [genericMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum]

private theorem genericMatrix_eval {R : Type*} [CommRing R] {n : ℕ}
    (x : ι → R) (M : ι → Matrix (Fin n) (Fin n) R) :
    (genericMatrix M).map (MvPolynomial.eval x) = ∑ i, x i • M i := by
  ext j l
  simp [genericMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum]

private theorem genericMatrix_charpoly_conj {R : Type*} [CommRing R] {n : ℕ}
    (U : (Matrix (Fin n) (Fin n) R)ˣ) (M : ι → Matrix (Fin n) (Fin n) R) :
    (genericMatrix fun i => (U : Matrix (Fin n) (Fin n) R) * M i *
      (↑U⁻¹ : Matrix (Fin n) (Fin n) R)).charpoly = (genericMatrix M).charpoly := by
  let V := Units.map (MvPolynomial.C : R →+* MvPolynomial ι R).mapMatrix.toMonoidHom U
  calc
    _ = ((↑V : Matrix _ _ _) * genericMatrix M * (↑V⁻¹ : Matrix _ _ _)).charpoly := by
      congr 1
      simp only [genericMatrix, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.map_mul]
      rfl
    _ = _ := by rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private theorem genericCharpoly_eq (hA : IsCentralSimple k A) {n : ℕ}
    (e₁ e₂ : BaseChange k L A ≃ₐ[L] Matrix (Fin n) (Fin n) L) (a : ι → A) :
    (genericMatrix fun i => e₁ (1 ⊗ₜ[k] a i)).charpoly =
      (genericMatrix fun i => e₂ (1 ⊗ₜ[k] a i)).charpoly := by
  obtain ⟨u, hu⟩ := algEquiv_isInner (isCentralSimple_baseChange hA) (e₁.trans e₂.symm)
  let U := Units.map e₂.toRingEquiv.toMonoidHom u
  have he (x : BaseChange k L A) : e₁ x = (U : Matrix _ _ _) * e₂ x * (↑U⁻¹ : Matrix _ _ _) := by
    simpa [U] using congrArg e₂ (hu x)
  simp_rw [he]
  exact genericMatrix_charpoly_conj U _

omit [Fintype ι] in
private theorem mapGeneric_comp {R S T : Type*} [Field R] [Field S] [Field T]
    (f : R →+* S) (g : S →+* T) (p : Polynomial (MvPolynomial ι R)) :
    mapGeneric g (mapGeneric f p) = mapGeneric (g.comp f) p := by
  rw [mapGeneric, mapGeneric, mapGeneric, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun q => MvPolynomial.map_map f g q

omit [Fintype ι] in
private theorem mapGeneric_injective {R S : Type*} [Field R] [Field S] (f : R →+* S) :
    Function.Injective (mapGeneric (ι := ι) f) :=
  Polynomial.map_injective _ (MvPolynomial.map_injective f f.injective)

private theorem map_splitCharpoly (hA : IsCentralSimple k A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L)
    {M : Type*} [Field M] [Algebra k M] (f : L →ₐ[k] M) (a : ι → A) :
    mapGeneric f.toRingHom (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).charpoly =
      (genericMatrix fun i =>
        splittingOfHom hA (f.mapMatrix.comp (splittingHom e)) (1 ⊗ₜ[k] a i)).charpoly := by
  rw [mapGeneric, ← Matrix.charpoly_map, genericMatrix_map]
  simp only [splittingOfHom_tmul, AlgHom.comp_apply, AlgHom.mapMatrix_apply]
  rfl

private theorem exists_genericCharpoly_descent (hA : IsCentralSimple k A)
    [FiniteDimensional k L] [IsGalois k L]
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L)
    (a : ι → A) :
    ∃ p : Polynomial (MvPolynomial ι k),
      mapGeneric (algebraMap k L) p = (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).charpoly := by
  let P := (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).charpoly
  have hfixed (σ : L ≃ₐ[k] L) : mapGeneric σ.toRingHom P = P :=
    (map_splitCharpoly hA e σ.toAlgHom a).trans (genericCharpoly_eq hA _ e a)
  change P ∈ (Polynomial.mapRingHom (MvPolynomial.map (algebraMap k L))).range
  rw [Polynomial.mem_map_range]
  intro n
  change P.coeff n ∈ Set.range (MvPolynomial.map (algebraMap k L))
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  intro c hc
  obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).2
  intro σ
  have h := congrArg (fun q : Polynomial (MvPolynomial ι L) => (q.coeff n).coeff m) (hfixed σ)
  change σ.toRingHom ((P.coeff n).coeff m) = _
  simpa only [mapGeneric, Polynomial.coeff_map, MvPolynomial.coeff_map] using h

/-- A comparison through a common overfield accommodates splitting fields
that are neither finite nor Galois. -/
private theorem map_genericCharpoly_of_descent (hA : IsCentralSimple k A)
    {K : Type*} [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (eK : BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)
    (eL : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L)
    (a : ι → A) {p : Polynomial (MvPolynomial ι k)}
    (hp : mapGeneric (algebraMap k K) p = (genericMatrix fun i => eK (1 ⊗ₜ[k] a i)).charpoly) :
    mapGeneric (algebraMap k L) p = (genericMatrix fun i => eL (1 ⊗ₜ[k] a i)).charpoly := by
  let M := AlgebraicClosure L
  let f : K →ₐ[k] M := IsAlgClosed.lift
  let g : L →ₐ[k] M := (Algebra.ofId L M).restrictScalars k
  apply mapGeneric_injective g.toRingHom
  calc
    mapGeneric g.toRingHom (mapGeneric (algebraMap k L) p) =
        mapGeneric f.toRingHom (mapGeneric (algebraMap k K) p) := by
      rw [mapGeneric_comp, mapGeneric_comp]
      exact congrArg (fun j => mapGeneric j p) (g.comp_algebraMap.trans f.comp_algebraMap.symm)
    _ = mapGeneric f.toRingHom (genericMatrix fun i => eK (1 ⊗ₜ[k] a i)).charpoly :=
      congrArg _ hp
    _ = mapGeneric g.toRingHom (genericMatrix fun i => eL (1 ⊗ₜ[k] a i)).charpoly := by
      rw [map_splitCharpoly hA eK, map_splitCharpoly hA eL]
      exact genericCharpoly_eq hA _ _ a

/-- The reduced characteristic polynomial of a formal linear combination
with independent coordinates. -/
noncomputable def genericReducedCharpoly (hA : IsCentralSimple k A) (a : ι → A) :
    Polynomial (MvPolynomial ι k) :=
  Specs.RM03.CSA.genericReducedCharpoly hA a

/-- The generic polynomial becomes the matrix characteristic polynomial in
every splitting and hence also in any choice of split matrix coordinates. -/
theorem genericReducedCharpoly_map (hA : IsCentralSimple k A) (a : ι → A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L) :
    mapGeneric (algebraMap k L) (genericReducedCharpoly hA a) =
      (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).charpoly := by
  classical
  obtain ⟨_, _, K, _, _, hFin, hGal, ⟨eK⟩⟩ := galois_splitting hA
  let : FiniteDimensional k K := hFin
  let : IsGalois k K := hGal
  obtain ⟨p, hp⟩ := exists_genericCharpoly_descent hA eK a
  obtain ⟨eC⟩ := algEquiv_matrix_algebraicClosure hA
  have hex : ∃ q : Polynomial (MvPolynomial ι k),
      ∃ e' : BaseChange k (AlgebraicClosure k) A ≃ₐ[AlgebraicClosure k]
          Matrix (Fin (degree k A)) (Fin (degree k A)) (AlgebraicClosure k),
        mapGeneric (algebraMap k (AlgebraicClosure k)) q =
          (genericMatrix fun i => e' (1 ⊗ₜ[k] a i)).charpoly :=
    ⟨p, eC, map_genericCharpoly_of_descent hA eK eC a hp⟩
  obtain ⟨e', he'⟩ := hex.choose_spec
  have hvalue : genericReducedCharpoly hA a = hex.choose := by
    unfold genericReducedCharpoly Specs.RM03.CSA.genericReducedCharpoly
    exact dite_eq_left hex
  rw [hvalue]
  exact map_genericCharpoly_of_descent hA e' e a he'

/-- The generic polynomial commutes with arbitrary field extension, keeping
the same coordinate variables for the scalar extensions of the family. -/
theorem genericReducedCharpoly_baseChange (hA : IsCentralSimple k A) (a : ι → A)
    (hL : IsCentralSimple L (BaseChange k L A) := isCentralSimple_baseChange hA) :
    genericReducedCharpoly hL (fun i => 1 ⊗ₜ[k] a i) =
      mapGeneric (algebraMap k L) (genericReducedCharpoly hA a) := by
  let M := AlgebraicClosure L
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hL
  have hdeg : degree k A = degree L (BaseChange k L A) := by
    unfold degree
    rw [finrank_baseChange hA]
  let f : A →ₐ[k] Matrix (Fin (degree k A)) (Fin (degree k A)) M :=
    (Matrix.reindexAlgEquiv k M (finCongr hdeg.symm)).toAlgHom.comp
      (((splittingHom e).restrictScalars k).comp includeRight)
  let e' := splittingOfHom hA f
  apply mapGeneric_injective (algebraMap L M)
  rw [genericReducedCharpoly_map hL _ e, mapGeneric_comp, ← IsScalarTower.algebraMap_eq,
    genericReducedCharpoly_map hA a e']
  rw [← Matrix.charpoly_reindex (finCongr hdeg.symm)]
  congr 1
  ext j l
  simp [genericMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.reindex_apply,
    e', splittingOfHom_tmul, f, splittingHom]

omit [Fintype ι] in
private theorem eval_mapGeneric {R S : Type*} [Field R] [Field S]
    (f : R →+* S) (x : ι → R) (p : Polynomial (MvPolynomial ι R)) :
    (mapGeneric f p).map (MvPolynomial.eval (f ∘ x)) = (p.map (MvPolynomial.eval x)).map f := by
  rw [mapGeneric, Polynomial.map_map, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun q => (MvPolynomial.map_eval f x q).symm

/-- The reduced characteristic polynomial of an element. -/
noncomputable def reducedCharpoly (hA : IsCentralSimple k A) (a : A) : Polynomial k :=
  Specs.RM03.CSA.reducedCharpoly hA a

/-- In every splitting, the reduced characteristic polynomial is precisely the
unique polynomial whose coefficient extension is the matrix characteristic polynomial. -/
theorem reducedCharpoly_map_iff (hA : IsCentralSimple k A) (a : A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L)
    (p : Polynomial k) :
    p.map (algebraMap k L) = (e (1 ⊗ₜ[k] a)).charpoly ↔ p = reducedCharpoly hA a := by
  have h : (reducedCharpoly hA a).map (algebraMap k L) =
      (e (1 ⊗ₜ[k] a)).charpoly := by
    change ((genericReducedCharpoly hA (fun _ : Unit => a)).map
      (MvPolynomial.eval (fun _ => 1))).map _ = _
    rw [← eval_mapGeneric, genericReducedCharpoly_map hA _ e, ← Matrix.charpoly_map,
      genericMatrix_eval]
    simp
  rw [← h, (Polynomial.map_injective (algebraMap k L) (algebraMap k L).injective).eq_iff]

/-- In a split matrix presentation, the reduced characteristic polynomial
extends to the ordinary characteristic polynomial. -/
theorem reducedCharpoly_map (hA : IsCentralSimple k A) (a : A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L) :
    (reducedCharpoly hA a).map (algebraMap k L) = (e (1 ⊗ₜ[k] a)).charpoly :=
  (reducedCharpoly_map_iff hA a e _).2 rfl

/-- The polynomial of a scalar-extended element is its coefficient extension. -/
theorem reducedCharpoly_baseChange (hA : IsCentralSimple k A) (a : A)
    (hL : IsCentralSimple L (BaseChange k L A) := isCentralSimple_baseChange hA) :
    reducedCharpoly hL (1 ⊗ₜ[k] a) = (reducedCharpoly hA a).map (algebraMap k L) := by
  change (genericReducedCharpoly hL (fun _ : Unit => 1 ⊗ₜ[k] a)).map
    (MvPolynomial.eval fun _ => 1) =
    ((genericReducedCharpoly hA (fun _ : Unit => a)).map (MvPolynomial.eval fun _ => 1)).map _
  rw [genericReducedCharpoly_baseChange hA _ hL, ← eval_mapGeneric]
  simp [Function.comp_def]

/-- Specializing the independent variables gives the reduced characteristic
polynomial of the corresponding linear combination. -/
theorem genericReducedCharpoly_eval (hA : IsCentralSimple k A) (a : ι → A) (x : ι → k) :
    (genericReducedCharpoly hA a).map (MvPolynomial.eval x) =
      reducedCharpoly hA (∑ i, x i • a i) := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  apply (reducedCharpoly_map_iff hA _ e _).1
  rw [← eval_mapGeneric, genericReducedCharpoly_map hA _ e, ← Matrix.charpoly_map,
    genericMatrix_eval]
  congr 1
  change ∑ i, algebraMap k (AlgebraicClosure k) (x i) • splittingHom e (a i) =
    splittingHom e (∑ i, x i • a i)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, algebraMap_smul]

end RM03.CSA
