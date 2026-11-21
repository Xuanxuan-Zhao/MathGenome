import MathGenome.Internal.Specs.D07.Ch16.SubmoduleFree
import MathGenome.Internal.D07.Ch16.SubmoduleFreeFirstDiagonalSummand
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

universe u v

namespace D07.Ch16.SubmoduleFree

open Module Submodule
open scoped Pointwise

/-- A split functional supplies a basis by adjoining its section to a kernel basis. -/
noncomputable def extendKernelBasis {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {φ : M →ₗ[R] R} {e : M} (he : φ e = 1) {n : ℕ}
    (b : Basis (Fin n) R (LinearMap.ker φ)) : Basis (Fin (n + 1)) R M :=
  Basis.mkFinCons e b
    (by
      intro c x hx hcx
      have h := congrArg φ hcx
      simpa [he, LinearMap.mem_ker.mp hx] using h)
    (by
      intro x
      refine ⟨-φ x, ?_⟩
      simp [LinearMap.mem_ker, he])

/-- Adjoin the first diagonal vector to a basis of the remaining intersection. -/
noncomputable def extendIntersectionBasis {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Submodule R M} {φ : M →ₗ[R] R} {e : M} {a : R}
    (ha : a ≠ 0) (he : φ e = 1) (hay : a • e ∈ N)
    (himage : N.map φ = Ideal.span {a}) {s : ℕ}
    (b : Basis (Fin s) R ↥(N ⊓ LinearMap.ker φ)) : Basis (Fin (s + 1)) R N :=
  Basis.mkFinConsOfLE (a • e) hay b inf_le_left
    (by
      intro c x hx hcx
      have h : c * a = 0 := by
        simpa [he, LinearMap.mem_ker.mp hx.2] using congrArg φ hcx
      exact (mul_eq_zero.mp h).resolve_right ha)
    (by
      intro x hx
      have hd : a ∣ φ x := Ideal.mem_span_singleton.mp
        (himage ▸ (show φ x ∈ N.map φ from ⟨x, hx, rfl⟩))
      obtain ⟨c, hc⟩ := hd
      refine ⟨-c, ?_, ?_⟩
      · exact N.add_mem hx (N.smul_mem _ hay)
      · simp [LinearMap.mem_ker, he, hc, mul_comm])

/-- Rank induction retains the joining divisibility, not merely diagonal shape. -/
theorem diagonalBasis : Specs.D07.Ch16.SubmoduleFree.DiagonalBasis.{u, v} := by
  intro R _ _ _ n
  induction n with
  | zero =>
      intro M _ _ b N
      have hM : Subsingleton M :=
        ⟨fun x y => b.ext_elem (fun i => Fin.elim0 i)⟩
      let := hM
      exact ⟨0, le_rfl, b, Fin.elim0, Basis.empty _,
        (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
  | succ n ih =>
      intro M _ _ b N
      classical
      by_cases hN : N = ⊥
      · subst N
        exact ⟨0, Nat.zero_le _, b, Fin.elim0, Basis.empty _,
          (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
      obtain ⟨a, φ, e, ha, he, hay, himage, _hcompl, _hdisj, _hsup, hdiv, ⟨bk⟩⟩ :=
        D07.Ch16.SubmoduleFreeFirstDiagonalSummand.firstDiagonalSummand
          R M (n + 1) b (Nat.succ_pos _) N hN
      have bk' : Basis (Fin n) R (LinearMap.ker φ) := by simpa using bk
      let K := LinearMap.ker φ
      let I := N ⊓ K
      let N0 := I.comap K.subtype
      obtain ⟨s, hs, b0, as, f0, hne, hchain, hrel⟩ := ih K bk' N0
      let fI : Basis (Fin s) R I :=
        f0.map (Submodule.comapSubtypeEquivOfLe (show I ≤ K from inf_le_right))
      let B := extendKernelBasis he b0
      let F := extendIntersectionBasis ha he hay himage fI
      have hfirst : ∀ i, a ∣ as i := by
        intro i
        have hx : ((f0 i : N0) : M) ∈ N ⊓ K := (f0 i).property
        obtain ⟨z, hz, haz⟩ :=
          (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hdiv hx)
        let zK : K := ⟨z, hz⟩
        have hh : a • zK = as i • b0 (Fin.castLE hs i) := by
          apply Subtype.ext
          exact haz.trans (congrArg (fun x : K => (x : M)) (hrel i))
        refine ⟨b0.coord (Fin.castLE hs i) zK, ?_⟩
        simpa using (congrArg (b0.coord (Fin.castLE hs i)) hh).symm
      refine ⟨s + 1, Nat.succ_le_succ hs, B, Fin.cons a as, F, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases (by simpa using ha) (fun j => by simpa using hne j) i
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · intro j _
          exact Fin.cases (by simp) (fun j => by simpa using hfirst j) j
        · intro j
          refine Fin.cases ?_ (fun j hij => ?_) j
          · intro hij
            exact False.elim (Nat.not_succ_le_zero i.val hij)
          · simpa using hchain i j (Fin.succ_le_succ_iff.mp hij)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [F, B, extendIntersectionBasis, extendKernelBasis]
        · simp only [F, B, extendIntersectionBasis, extendKernelBasis,
            Basis.coe_mkFinConsOfLE, Basis.coe_mkFinCons, Fin.cons_succ,
            Fin.castLE_succ, Function.comp_apply, coe_inclusion]
          exact congrArg (fun x : K => (x : M)) (hrel j)

/-- The displayed finite basis proves both freeness and finite generation. -/
theorem finiteFree : Specs.D07.Ch16.SubmoduleFree.FiniteFree.{u, v} := by
  intro R _ _ _ n M _ _ b N
  obtain ⟨s, _, _, _, f, _⟩ := diagonalBasis R n M b N
  exact ⟨Module.Free.of_basis f, Module.Finite.of_basis f⟩

end D07.Ch16.SubmoduleFree
