import MathGenome.Internal.Specs.D07.Ch16.Smith
import MathGenome.Internal.D07.Ch16.SubmoduleFree
import MathGenome.Internal.D07.Ch16.FreeGenerators
import MathGenome.Internal.D07.Ch16.SmithEuclideanSmithAlgorithm
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Span

universe u v w
namespace D07.Ch16.Smith
open Module

/-- Lift an image basis to a section, and split off the kernel. -/
theorem splitRange {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {L : Type w} [AddCommGroup L] [Module R L]
    (A : M →ₗ[R] L) {s : ℕ} (f : Basis (Fin s) R (LinearMap.range A)) :
    ∃ E : (LinearMap.range A × LinearMap.ker A) ≃ₗ[R] M,
      ∀ p, A (E p) = p.1 := by
  classical
  choose x hx using (fun i => (f i).property)
  let g : LinearMap.range A →ₗ[R] M := f.constr R x
  have hg : ∀ y, A (g y) = y := by
    have h : A.comp g = (LinearMap.range A).subtype := by
      apply f.ext
      intro i
      simpa [g] using hx i
    exact fun y => DFunLike.congr_fun h y
  let h : (LinearMap.range A × LinearMap.ker A) →ₗ[R] M :=
    (g.comp (LinearMap.fst R _ _)) +
      ((LinearMap.ker A).subtype.comp (LinearMap.snd R _ _))
  have hbij : Function.Bijective h := by
    constructor
    · intro p q hpq
      have hfirst : p.1 = q.1 := by
        apply Subtype.ext
        simpa [h, hg] using congrArg A hpq
      apply Prod.ext hfirst
      apply Subtype.ext
      have hsecond := hpq
      simpa only [h, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply, hfirst,
        add_right_inj] using hsecond
    · intro y
      let z : LinearMap.range A := ⟨A y, ⟨y, rfl⟩⟩
      let k : LinearMap.ker A := ⟨y - g z, by simp [LinearMap.mem_ker, hg, z]⟩
      exact ⟨(z, k), by simp [h, k]⟩
  exact ⟨LinearEquiv.ofBijective h hbij, fun p => by simp [h, hg]⟩

/-- The quotient coordinate map in a diagonal image basis. -/
noncomputable def diagonalQuotientMap {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {s t : ℕ}
    (e : Basis (Fin s ⊕ Fin t) R M) (a : Fin s → R) :
    M →ₗ[R] ((Fin t → R) × (∀ i : Fin s, R ⧸ Ideal.span {a i})) :=
  (LinearMap.pi fun j => e.coord (Sum.inr j)).prod
    (LinearMap.pi fun i => (Ideal.span {a i}).mkQ.comp (e.coord (Sum.inl i)))

/-- Quotient by a diagonal submodule, with all unused coordinates retained. -/
theorem diagonalQuotient {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {s t : ℕ}
    (e : Basis (Fin s ⊕ Fin t) R M) (N : Submodule R M)
    (f : Basis (Fin s) R N) (a : Fin s → R)
    (hf : ∀ i, (f i : M) = a i • e (Sum.inl i)) :
    Nonempty ((M ⧸ N) ≃ₗ[R]
      ((Fin t → R) × (∀ i : Fin s, R ⧸ Ideal.span {a i}))) := by
  classical
  let q := diagonalQuotientMap e a
  have hq : Function.Surjective q := by
    rintro ⟨z, y⟩
    choose x hx using (fun i => Ideal.Quotient.mk_surjective (y i))
    refine ⟨e.equivFun.symm (Sum.elim x z), ?_⟩
    apply Prod.ext
    · ext j
      change e.equivFun (e.equivFun.symm (Sum.elim x z)) (Sum.inr j) = z j
      rw [e.equivFun.apply_symm_apply]
      rfl
    · ext i
      change Ideal.Quotient.mk _ (e.equivFun (e.equivFun.symm (Sum.elim x z)) (Sum.inl i)) = y i
      rw [e.equivFun.apply_symm_apply]
      exact hx i
  have hker : LinearMap.ker q = N := by
    ext x
    constructor
    · intro hx
      have hx' : q x = 0 := hx
      have hz : ∀ j, e.repr x (Sum.inr j) = 0 := by
        intro j
        exact congrArg (fun z => z.1 j) hx'
      have hd : ∀ i, a i ∣ e.repr x (Sum.inl i) := by
        intro i
        exact Ideal.mem_span_singleton.mp
          ((Ideal.Quotient.eq_zero_iff_mem).mp (congrArg (fun z => z.2 i) hx'))
      choose c hc using hd
      have heq : x = ∑ i, c i • (f i : M) := by
        apply e.ext_elem
        intro j
        cases j with
        | inl j => simp [hf, hc, mul_comm, Finsupp.single_apply]
        | inr j => simp [hf, hz]
      rw [heq]
      exact N.sum_mem fun i _ => N.smul_mem _ (f i).property
    · intro hx
      have heq : x = ∑ i, f.repr (⟨x, hx⟩ : N) i • (f i : M) := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using
          (congrArg (fun y : N => (y : M)) (f.sum_repr ⟨x, hx⟩)).symm
      rw [LinearMap.mem_ker, heq, map_sum]
      have hzero : ∀ i, q (f i : M) = 0 := by
        intro i
        apply Prod.ext
        · ext j; simp [q, diagonalQuotientMap, hf]
        · ext j
          by_cases hij : i = j
          · subst j
            change (Ideal.span {a i}).mkQ (e.coord (Sum.inl i) (f i : M)) = 0
            rw [hf]
            apply (Submodule.Quotient.mk_eq_zero _).mpr
            simp [Basis.coord_apply]
          · simp [q, diagonalQuotientMap, hf, Basis.coord_apply, hij]
      simp [hzero]
  exact ⟨(Submodule.quotEquivOfEq N (LinearMap.ker q) hker.symm).trans
    (q.quotKerEquivOfSurjective hq)⟩

/-- Assemble the domain basis from image lifts and a kernel basis. -/
theorem smithDecomposition : Specs.D07.Ch16.Smith.SmithDecomposition.{u} := by
  intro R _ _ _ m n A
  classical
  let bn := Pi.basisFun R (Fin n)
  let bm := Pi.basisFun R (Fin m)
  obtain ⟨s, hs, e0, a, f, hne, hchain, hdiag⟩ :=
    D07.Ch16.SubmoduleFree.diagonalBasis R n (Fin n → R) bn (LinearMap.range A)
  obtain ⟨k, _hk, _c, _d, bk, _⟩ :=
    D07.Ch16.SubmoduleFree.diagonalBasis R m (Fin m → R) bm (LinearMap.ker A)
  obtain ⟨E, hE⟩ := splitRange A f
  let b := (f.prod bk).map E
  have hrank : s + k = m := by
    have h := D07.Ch16.FreeGenerators.finiteBasisCardinality R (Fin m → R)
      (Fin s ⊕ Fin k) (Fin m) b bm
    simpa using h
  let t := n - s
  have ht : s + t = n := Nat.add_sub_of_le hs
  let re : (Fin s ⊕ Fin t) ≃ Fin n := finSumFinEquiv.trans (finCongr ht)
  let e := e0.reindex re.symm
  have he : ∀ i : Fin s, e (Sum.inl i) = e0 (Fin.castLE hs i) := by
    intro i
    simp only [e, Basis.reindex_apply, Equiv.symm_symm]
    apply congrArg e0
    apply Fin.ext
    rfl
  have hf : ∀ i, (f i : Fin n → R) = a i • e (Sum.inl i) := by
    intro i
    rw [he]
    exact hdiag i
  obtain ⟨q⟩ := diagonalQuotient e (LinearMap.range A) f a hf
  refine ⟨s, k, t, b, e, a, hrank, ht, hne, hchain, ?_, ?_, ⟨q⟩, ?_⟩
  · intro i
    have h := hE ((f.prod bk) (Sum.inl i))
    simpa [b, hf] using h
  · intro j
    have h := hE ((f.prod bk) (Sum.inr j))
    simpa [b] using h
  · exact ⟨q.trans ((LinearEquiv.refl R (Fin t → R)).prodCongr
      (DirectSum.linearEquivFunOnFintype R (Fin s) (fun i => R ⧸ Ideal.span {a i})).symm)⟩

theorem unitQuotient : Specs.D07.Ch16.Smith.UnitQuotient.{u} := by
  intro R _ a
  exact Submodule.Quotient.subsingleton_iff.trans Ideal.span_singleton_eq_top

theorem unitCancellation : Specs.D07.Ch16.Smith.UnitCancellation.{u} := by
  intro R _ s a
  classical
  let p : (∀ i : Fin s, R ⧸ Ideal.span {a i}) →ₗ[R]
      (∀ i : {i : Fin s // ¬ IsUnit (a i)}, R ⧸ Ideal.span {a i.val}) :=
    LinearMap.pi fun i => LinearMap.proj i.val
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      ext i
      by_cases h : IsUnit (a i)
      · let := (unitQuotient R (a i)).mpr h
        exact Subsingleton.elim _ _
      · exact congrArg (fun z => z ⟨i, h⟩) hxy
    · intro y
      refine ⟨fun i => if h : IsUnit (a i) then 0 else y ⟨i, h⟩, ?_⟩
      ext i
      simp [p, i.property]
  exact ⟨LinearEquiv.ofBijective p hp, fun _ _ => rfl⟩

/-- The explicit cokernel of a diagonal presentation, also for zero scalars.
This general coordinate lemma needs neither PID hypotheses nor finite indices. -/
theorem diagonalPresentationCokernel {R : Type u} [CommRing R]
    (ι : Type v) (κ : Type w) (a : ι → R) :
    Nonempty ((((κ → R) × (ι → R)) ⧸ LinearMap.range
      (Specs.D07.Ch16.Smith.diagonalPresentation ι κ a)) ≃ₗ[R]
      ((κ → R) × (∀ i, R ⧸ Ideal.span {a i}))) := by
  classical
  let d := Specs.D07.Ch16.Smith.diagonalPresentation ι κ a
  let q : ((κ → R) × (ι → R)) →ₗ[R]
      ((κ → R) × (∀ i, R ⧸ Ideal.span {a i})) :=
    (LinearMap.fst R _ _).prod
      ((LinearMap.pi fun i => (Ideal.span {a i}).mkQ.comp (LinearMap.proj i)).comp
        (LinearMap.snd R _ _))
  have hq : Function.Surjective q := by
    rintro ⟨z, y⟩
    choose x hx using (fun i => Ideal.Quotient.mk_surjective (y i))
    exact ⟨(z, x), Prod.ext rfl (funext hx)⟩
  have hker : LinearMap.ker q = LinearMap.range d := by
    ext x
    constructor
    · intro hx
      have hx' : q x = 0 := hx
      have hz : x.1 = 0 := congrArg Prod.fst hx'
      have hd : ∀ i, a i ∣ x.2 i := by
        intro i
        exact Ideal.mem_span_singleton.mp
          (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun z => z.2 i) hx'))
      choose c hc using hd
      exact ⟨c, Prod.ext hz.symm (funext fun i => (hc i).symm)⟩
    · rintro ⟨y, rfl⟩
      apply Prod.ext
      · rfl
      · ext i
        change (Ideal.span {a i}).mkQ (a i * y i) = 0
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (q.quotKerEquivOfSurjective hq)⟩

theorem presentationCancellation : Specs.D07.Ch16.Smith.PresentationCancellation.{u} := by
  intro R _ s t a
  obtain ⟨E⟩ := diagonalPresentationCokernel (R := R) (Fin s) (Fin t) a
  obtain ⟨F⟩ := diagonalPresentationCokernel (R := R)
    {i : Fin s // ¬ IsUnit (a i)} (Fin t) (fun i => a i.val)
  obtain ⟨U, _⟩ := unitCancellation R s a
  exact ⟨(E.trans ((LinearEquiv.refl R _).prodCongr U)).trans F.symm⟩

theorem euclideanConstruction : Specs.D07.Ch16.Smith.EuclideanConstruction.{u} :=
  D07.Ch16.SmithEuclideanSmithAlgorithm.smithConstruction

theorem identityCancellation : Specs.D07.Ch16.Smith.IdentityCancellation := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_id]
  · exact inferInstance
  · rintro ⟨E⟩
    have h := D07.Ch16.FreeGenerators.finiteFreeRankInvariant ℤ 1 0 E
    exact Nat.noConfusion h

end D07.Ch16.Smith
