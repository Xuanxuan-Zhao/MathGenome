import MathGenome.Internal.Specs.D05.M10.JordanExistence
import MathGenome.Internal.D05.M04.MatrixOfMap
import MathGenome.Internal.D05.M10.GeneralizedDecomposition
import MathGenome.Internal.D05.M10.JordanChains
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

noncomputable section
open scoped BigOperators Classical
namespace D05.M10.JordanExistence

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_chain_basis : Specs.D05.M10.JordanExistence.exists_chain_basis := by
  intro K V _ _ _ _ T hs
  classical
  let U := fun μ : spectrum K T =>
    Specs.D05.M10.Generalized.generalizedEigenspace_value K V T μ.val
  have hd : DirectSum.IsInternal U := GeneralizedDecomposition.decomposition T hs
  have hchain (μ : spectrum K T) :
      ∃ (r : ℕ) (a : Fin r → ℕ), (∀ i, 0 < a i) ∧
        ∃ b : Module.Basis (Σ i, Fin (a i)) K (U μ),
          (∀ i (j : Fin (a i)), j.val = 0 →
            T (b ⟨i, j⟩) = μ.val • (b ⟨i, j⟩ : V)) ∧
          (∀ i (j k : Fin (a i)), j.val = k.val + 1 →
            T (b ⟨i, j⟩) = μ.val • (b ⟨i, j⟩ : V) + b ⟨i, k⟩) := by
    obtain ⟨hT, hN, heq, s, _, hz⟩ := GeneralizedDecomposition.summand_structure T μ
    obtain ⟨r, a, ha, b, hb0, hbS, _⟩ :=
      JordanChains.jordan_chain_basis ((T - μ.val • 1).restrict hN) ⟨s, hz⟩
    refine ⟨r, a, ha, b, ?_, ?_⟩
    · intro i j hj
      have h := congrArg (fun f : Module.End K (U μ) => f (b ⟨i, j⟩)) heq
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hb0 i j hj,
        add_zero] at h
      exact congrArg Subtype.val h
    · intro i j k hjk
      have h := congrArg (fun f : Module.End K (U μ) => f (b ⟨i, j⟩)) heq
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hbS i j k hjk] at h
      exact congrArg Subtype.val h
  choose r a ha B hzero hstep using hchain
  letI : Fintype (spectrum K T) := T.finite_spectrum.fintype
  let I := Σ μ : spectrum K T, Fin (r μ)
  let A : I → ℕ := fun i => a i.1 i.2
  let E : (Σ μ : spectrum K T, Σ i, Fin (a μ i)) ≃ (Σ i : I, Fin (A i)) :=
    (Equiv.sigmaAssoc (fun μ i => Fin (a μ i))).symm
  let b : Module.Basis (Σ i : I, Fin (A i)) K V := (hd.collectedBasis B).reindex E
  have hb (i : I) (j : Fin (A i)) : b ⟨i, j⟩ = (B i.1 ⟨i.2, j⟩ : V) := by
    simp [b, E, Equiv.sigmaAssoc]
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let a' : Fin (Fintype.card I) → ℕ := fun i => A (e.symm i)
  let E' : (Σ i : I, Fin (A i)) ≃ (Σ i, Fin (a' i)) := Equiv.sigmaCongrLeft' e
  let b' := b.reindex E'
  have hb' (i : Fin (Fintype.card I)) (j : Fin (a' i)) :
      b' ⟨i, j⟩ = (B (e.symm i).1 ⟨(e.symm i).2, j⟩ : V) := by
    simpa [b', E', Equiv.sigmaCongrLeft', Equiv.sigmaCongrLeft] using hb (e.symm i) j
  refine ⟨Fintype.card I, a', (fun i => (e.symm i).1.val),
    (fun i => ha _ _), b', ?_, ?_, ?_⟩
  · intro i j hj
    simpa only [hb'] using hzero (e.symm i).1 (e.symm i).2 j hj
  · intro i j k hjk
    simpa only [hb'] using hstep (e.symm i).1 (e.symm i).2 j k hjk
  · simpa using (Module.finrank_eq_card_basis b').symm

/-- Coordinate calculation for any basis satisfying the chain equations. -/
lemma matrix_of_chain_basis {r : ℕ} (a : Fin r → ℕ) (μ : Fin r → K)
    (T : Module.End K V) (b : Module.Basis (Σ i, Fin (a i)) K V)
    (hzero : ∀ i (j : Fin (a i)), j.val = 0 →
      T (b ⟨i, j⟩) = μ i • b ⟨i, j⟩)
    (hstep : ∀ i (j k : Fin (a i)), j.val = k.val + 1 →
      T (b ⟨i, j⟩) = μ i • b ⟨i, j⟩ + b ⟨i, k⟩) :
    LinearMap.toMatrix b b T = Specs.D05.M10.JordanExistence.jordanMatrix a μ := by
  classical
  ext ⟨i, u⟩ ⟨j, v⟩
  rw [LinearMap.toMatrix_apply]
  by_cases hv : v.val = 0
  · rw [hzero j v hv]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
    unfold Specs.D05.M10.JordanExistence.jordanMatrix
    by_cases hij : i = j
    · subst j
      by_cases huv : u = v
      · subst v; simp
      · have hval : u.val ≠ v.val := fun h => huv (Fin.ext h)
        have hsig : (Sigma.mk i v : Σ i, Fin (a i)) ≠ ⟨i, u⟩ := by
          intro h; exact huv (by simpa using (Sigma.mk.inj_iff.mp h).2.symm)
        have hu0 : u.val ≠ 0 := by omega
        simp [hv, hsig, hu0]
    · have hsig : (Sigma.mk j v : Σ i, Fin (a i)) ≠ ⟨i, u⟩ := by
        intro h; exact hij (congrArg Sigma.fst h).symm
      simp [hij, hsig]
  · let k : Fin (a j) := ⟨v.val - 1, by omega⟩
    have hvk : v.val = k.val + 1 := by dsimp [k]; omega
    rw [hstep j v k hvk]
    simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    unfold Specs.D05.M10.JordanExistence.jordanMatrix
    by_cases hij : i = j
    · subst j
      have heq (w : Fin (a i)) :
          (Sigma.mk i w : Σ i, Fin (a i)) = ⟨i, u⟩ ↔ u.val = w.val := by
        constructor
        · intro h; cases h; rfl
        · intro h; cases Fin.ext h; rfl
      simp only [heq, ite_true]
      by_cases huv : u.val = v.val
      · have hvne : v.val ≠ k.val := by omega
        simp [huv, hvne]
      · have hpred : u.val = k.val ↔ u.val + 1 = v.val := by omega
        simp [huv, hpred]
    · have hsig (w : Fin (a j)) :
          (Sigma.mk j w : Σ i, Fin (a i)) ≠ ⟨i, u⟩ := by
        intro h; exact hij (congrArg Sigma.fst h).symm
      simp [hij, hsig]

theorem jordan_form : Specs.D05.M10.JordanExistence.jordan_form := by
  intro K V _ _ _ _ T hs
  obtain ⟨r, a, μ, ha, b, hz, hstep, hdim⟩ := exists_chain_basis T hs
  exact ⟨r, a, μ, ha, b, matrix_of_chain_basis a μ T b hz hstep, hdim⟩

end D05.M10.JordanExistence
