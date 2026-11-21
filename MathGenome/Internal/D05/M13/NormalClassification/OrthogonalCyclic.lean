import MathGenome.Internal.Specs.D05.M13.NormalClassification.OrthogonalCyclic
import MathGenome.Internal.D05.M13.NormalClassification.CyclicLayers
import MathGenome.Internal.D05.M13.ComplexSpectral
import MathGenome.Internal.D05.M13.RealNormalBlocks
import MathGenome.Internal.D05.M10.InvariantFactors
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

noncomputable section
namespace D05.M13.NormalClassification.OrthogonalCyclic
open Polynomial
open Specs.D05.M13.NormalClassification.CyclicLayers
open Specs.D05.M13.NormalClassification.OrthogonalCyclic
variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

/-- Normality gives invariant orthogonal complements, hence semisimplicity
for the actual polynomial action. -/
theorem normal_semisimple (T : Module.End F V) (hT : D05.normalOperator T) :
    T.IsSemisimple := by
  apply Module.End.isSemisimple_iff.mpr
  intro M hM
  refine ⟨M.orthogonal, ?_, M.isCompl_orthogonal⟩
  exact (D05.M13.NormalReducing.invariant_subspace_reduces T M hT hM).2.1

theorem normal_minpoly_squarefree (T : Module.End F V) (hT : D05.normalOperator T) :
    Squarefree (minpoly F T) := (normal_semisimple T hT).minpoly_squarefree

/-- Monic squarefree polynomials are literal finite products of distinct
monic irreducibles over the original scalar field. -/
lemma distinct_irreducible_factorization {K : Type*} [Field K] (p : K[X])
    (hp : p.Monic) (hs : Squarefree p) :
    ∃ P : Finset K[X], (∀ q ∈ P, q.Monic ∧ Irreducible q) ∧ p = ∏ q ∈ P, q := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors p
  have hn : s.Nodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hp.ne_zero).mp hs
  refine ⟨⟨s, hn⟩, ?_, ?_⟩
  · intro q hq
    have hh := (Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hq
    exact ⟨hh.2.1, hh.1⟩
  · simpa [Finset.prod_mk, Multiset.map_id, hp.leadingCoeff] using
      (Polynomial.leadingCoeff_mul_prod_normalizedFactors p).symm

/-- Summation is a polynomial-module equivalence for a full orthogonal
family of cyclic spaces. No orthonormality of their power bases is used. -/
def cyclicSumEquiv {ι : Type*} [Fintype ι] (T : Module.End F V) (w : ι → V)
    (ho : Pairwise fun i j => (M10.Cyclic.cyclicSpace F V T (w i)).IsOrtho
      (M10.Cyclic.cyclicSpace F V T (w j)))
    (htop : (⨆ i, M10.Cyclic.cyclicSpace F V T (w i)) = ⊤) :
    (∀ i, M10.Cyclic.cyclicModule F V T (w i)) ≃ₗ[F[X]] Module.AEval' T := by
  classical
  let H := fun i => M10.Cyclic.cyclicSpace F V T (w i)
  let C := fun i => M10.Cyclic.cyclicModule F V T (w i)
  let f : (∀ i, C i) →ₗ[F[X]] Module.AEval' T :=
    LinearMap.lsum F[X] (fun i => ↥(C i)) F[X] (fun i => (C i).subtype)
  let g : (∀ i, C i) →ₗ[F] V :=
    (Module.AEval'.of T).symm.toLinearMap.comp (f.restrictScalars F)
  have hg (x : ∀ i, C i) : g x = ∑ i, (Module.AEval'.of T).symm (x i) := by
    simp [g, f, LinearMap.lsum_apply]
  have hxmem (x : ∀ i, C i) (i : ι) :
      (Module.AEval'.of T).symm (x i) ∈ H i := by
    apply (M10.Cyclic.module_bridge T (w i) _).mp
    simp
  have hO : OrthogonalFamily F (fun i => H i) (fun i => (H i).subtypeₗᵢ) := by
    intro i j hij x y
    exact (ho hij).inner_eq x.property y.property
  have hginj : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    apply (LinearMap.ker_eq_bot').mpr
    intro x hx
    have hz : ∑ i, (Module.AEval'.of T).symm (x i) = 0 := by
      simpa [hg] using hx
    have hh := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero H).mp hO.independent
      Finset.univ (fun i => (Module.AEval'.of T).symm (x i))
      (fun i _ => hxmem x i) (by simpa using hz)
    funext i
    apply Subtype.ext
    exact (Module.AEval'.of T).symm.injective (by simpa using hh i (Finset.mem_univ i))
  have hgsurj : Function.Surjective g := by
    apply LinearMap.range_eq_top.mp
    apply top_le_iff.mp
    rw [← htop]
    apply iSup_le
    intro i x hx
    let y : C i := (M10.Cyclic.moduleSpaceEquiv T (w i)).symm ⟨x, hx⟩
    refine ⟨Pi.single i y, ?_⟩
    change (Module.AEval'.of T).symm (f (Pi.single i y)) = x
    rw [LinearMap.lsum_piSingle]
    exact congrArg Subtype.val ((M10.Cyclic.moduleSpaceEquiv T (w i)).apply_symm_apply ⟨x, hx⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    exact hginj (congrArg (Module.AEval'.of T).symm hxy)
  · intro y
    obtain ⟨x, hx⟩ := hgsurj ((Module.AEval'.of T).symm y)
    exact ⟨x, (Module.AEval'.of T).symm.injective hx⟩

/-- The quotient isomorphisms identify the ordered cyclic decomposition with
the shared invariant factors, after reversing its index order. -/
theorem cyclic_factors : Specs.D05.M13.NormalClassification.OrthogonalCyclic.cyclic_factors := by
  intro F V _ _ _ _ T r w d hm hp ha ho htop hd
  classical
  have he (i : Fin r) :
      Nonempty (Specs.D05.M10.Rational.Residue (d i) ≃ₗ[F[X]]
        M10.Cyclic.cyclicModule F V T (w i)) := by
    rw [← ha i]
    exact ⟨(M10.Cyclic.quotient_iso T (w i)).choose⟩
  let e : (∀ i, Specs.D05.M10.Rational.Residue (d i)) ≃ₗ[F[X]] Module.AEval' T :=
    (LinearEquiv.piCongrRight fun i => (he i).some).trans (cyclicSumEquiv T w ho htop)
  let rev : Fin r ≃ Fin r := Fin.revPerm
  let d' : Fin r → F[X] := fun i => d (rev i)
  have hlist : List.ofFn d' = (List.ofFn d).reverse := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [d', rev, Fin.rev, Nat.sub_sub, Nat.add_comm]
  rw [← hlist]
  apply M10.InvariantFactors.module_identification T d' (fun i => hm (rev i))
    (fun i => hp (rev i))
  · intro i j hij
    exact hd (rev j) (rev i) (by simpa [rev] using hij)
  · exact ⟨e.symm.trans (LinearEquiv.piCongrLeft F[X]
      (fun i => Specs.D05.M10.Rational.Residue (d i)) rev).symm⟩

/-- Orthogonal assembly of the algebraic CRT layers. -/
theorem assemble_layers : Specs.D05.M13.NormalClassification.OrthogonalCyclic.assemble_layers := by
  intro F V ι _ _ _ _ _ T H p hb ho htop
  classical
  obtain ⟨P, m, e, v, he, hm, hv, hl, hd⟩ := CyclicLayers.grouped_layers T H p hb
  let H' : ∀ q : P, Fin (m q) → Submodule F V := fun q k => H (e.symm ⟨q, k⟩)
  let w : Fin (layerCount m) → V := fun j => layerVector m v j
  let d : Fin (layerCount m) → F[X] := fun j => layerPolynomial m (fun q : P => (q : F[X])) j
  have hs (j : Fin (layerCount m)) : M10.Cyclic.cyclicSpace F V T (w j) = layerSpace m H' j :=
    (hl j j.isLt).1
  have ha (j : Fin (layerCount m)) : M10.Cyclic.vectorAnnihilator F V T (w j) = d j :=
    (hl j j.isLt).2.1
  have hmon (j : Fin (layerCount m)) : (d j).Monic := (hl j j.isLt).2.2.1
  have hpos (j : Fin (layerCount m)) : 0 < (d j).natDegree := (hl j j.isLt).2.2.2.1
  have horth : Pairwise fun i j => (M10.Cyclic.cyclicSpace F V T (w i)).IsOrtho
      (M10.Cyclic.cyclicSpace F V T (w j)) := by
    intro i j hij
    rw [hs i, hs j]
    simp only [layerSpace, Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
    intro q s
    apply ho
    intro h
    have hh := e.symm.injective h
    have hh' : (i : ℕ) = (j : ℕ) := congrArg (fun z : Σ q : P, Fin (m q) => (z.2 : ℕ)) hh
    exact hij (Fin.ext hh')
  have hfull : (⨆ j, M10.Cyclic.cyclicSpace F V T (w j)) = ⊤ := by
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro i
    let q := (e i).1
    let k := (e i).2
    have hkm : (k : ℕ) < layerCount m :=
      lt_of_lt_of_le k.isLt (Finset.le_sup (f := m) (Finset.mem_univ q))
    apply le_iSup_of_le (⟨k, hkm⟩ : Fin (layerCount m))
    rw [hs]
    apply le_iSup_of_le (⟨q, k.isLt⟩ : Available m (k : ℕ))
    change H i ≤ H (e.symm (e i))
    simp
  have hdesc : ∀ i j : Fin (layerCount m), i ≤ j → d j ∣ d i := by
    intro i j hij
    have hh : ∀ a b : ℕ, a ≤ b →
        layerPolynomial m (fun q : P => (q : F[X])) b ∣
          layerPolynomial m (fun q : P => (q : F[X])) a := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact dvd_refl _
      | succ b hab ih => exact (hd b).trans ih
    exact hh i j hij
  have hlabels (q : P) : (q : F[X]).Monic ∧ Irreducible (q : F[X]) := by
    let i := e.symm ⟨q, ⟨0, hm q⟩⟩
    have hi : p i = (q : F[X]) := by simpa [i] using (he i).symm
    rw [← hi]
    exact ⟨(hb i).monic, (hb i).irreducible⟩
  have hsq (j : Fin (layerCount m)) : Squarefree (d j) := by
    change Squarefree (∏ q : Available m (j : ℕ), (q.1 : F[X]))
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro q _ s _ hqs
      apply IsCoprime.isRelPrime
      exact CyclicLayers.coprime_labels (fun q : Available m (j : ℕ) => (q.1 : F[X]))
        (fun q => (hlabels q.1).1) (fun q => (hlabels q.1).2)
        (fun q s h => Subtype.ext (Subtype.ext h)) hqs
    · intro q _
      exact (hlabels q.1).2.squarefree
  exact ⟨layerCount m, w, d,
    ⟨hmon, hpos, ha, horth, hfull, hdesc, hsq,
      fun i => distinct_irreducible_factorization (d i) (hmon i) (hsq i),
      cyclic_factors T w d hmon hpos ha horth hfull hdesc⟩⟩

/-- The spectral theorem supplies the orthogonal algebraic blocks over ℂ. -/
theorem complex_decomposition : Specs.D05.M13.NormalClassification.OrthogonalCyclic.complex_decomposition := by
  intro V _ _ _ T hT
  obtain ⟨B, a, hB⟩ := M13.ComplexSpectral.exists_orthonormalBasis T hT
  let H := fun i => (ℂ ∙ B i)
  apply assemble_layers T H (fun i => X - C (a i))
  · intro i
    exact CyclicLayers.line_block T (B i) (a i) (B.toBasis.ne_zero i) (hB i)
  · intro i j hij
    apply Submodule.isOrtho_span.mpr
    rintro x hx y hy
    rcases Set.mem_singleton_iff.mp hx with rfl
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact B.orthonormal.inner_eq_zero hij
  · simpa [H, Submodule.span_range_eq_iSup] using B.toBasis.span_eq

/-- Choose one representative from each orbit of the involutive block partner.
Fixed points are eigenlines; two-element orbits are the real normal planes. -/
theorem real_decomposition : Specs.D05.M13.NormalClassification.OrthogonalCyclic.real_decomposition := by
  intro V _ _ _ T hT
  classical
  obtain ⟨n, B, t, ht, hpart⟩ := M13.RealNormalBlocks.normal_blocks_partitioned T hT
  let I := {i : Fin n // i ≤ t i}
  let H : I → Submodule ℝ V := fun i => Submodule.span ℝ (Set.range ![B i.1, B (t i.1)])
  have horbit (i j : I) (hij : i ≠ j) :
      i.1 ≠ j.1 ∧ i.1 ≠ t j.1 ∧ t i.1 ≠ j.1 ∧ t i.1 ≠ t j.1 := by
    have h1 : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have h2 : i.1 ≠ t j.1 := by
      intro h
      have h' : t i.1 = j.1 := by rw [h, ht]
      exact h1 (le_antisymm (by simpa [h'] using i.2) (by simpa [← h] using j.2))
    have h3 : t i.1 ≠ j.1 := by
      intro h
      exact h2 (by rw [← h, ht])
    exact ⟨h1, h2, h3, fun h => h1 (ht.injective h)⟩
  have hblocks (i : I) : ∃ q : ℝ[X], Block T (H i) q := by
    rcases hpart i.1 with ⟨hfix, a, ha⟩ | ⟨hne, a, b, hb, ha⟩
    · have hH : H i = ℝ ∙ B i.1 := by simp [H, hfix, Matrix.range_cons]
      rw [hH]
      exact ⟨X - C a, CyclicLayers.line_block T (B i.1) a (B.toBasis.ne_zero _) ha⟩
    · have hon : Orthonormal ℝ ![B i.1, B (t i.1)] := by
        have hinj : Function.Injective (![i.1, t i.1] : Fin 2 → Fin n) := by
          exact Matrix.injective_pair_iff_ne.mpr hne.symm
        convert B.orthonormal.comp ![i.1, t i.1] hinj using 1
        funext a
        fin_cases a <;> rfl
      rcases ha with ha | ha
      · exact ⟨planePolynomial a b, CyclicLayers.plane_block T (B i.1) (B (t i.1)) a b hon hb ha⟩
      · have hon' : Orthonormal ℝ ![B (t i.1), B i.1] := by
          have hinj : Function.Injective (![t i.1, i.1] : Fin 2 → Fin n) := by
            exact Matrix.injective_pair_iff_ne.mpr hne
          convert B.orthonormal.comp ![t i.1, i.1] hinj using 1
          funext a
          fin_cases a <;> rfl
        refine ⟨planePolynomial a b, ?_⟩
        have hh := CyclicLayers.plane_block T (B (t i.1)) (B i.1) a b hon' hb ha
        have heq : Set.range (![B (t i.1), B i.1] : Fin 2 → V) = Set.range ![B i.1, B (t i.1)] := by
          ext x
          simp [or_comm]
        rwa [heq] at hh
  choose p hp using hblocks
  apply assemble_layers T H p hp
  · intro i j hij
    obtain ⟨h1, h2, h3, h4⟩ := horbit i j hij
    apply Submodule.isOrtho_span.mpr
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    fin_cases a <;> fin_cases c
    · exact B.orthonormal.inner_eq_zero h1
    · exact B.orthonormal.inner_eq_zero h2
    · exact B.orthonormal.inner_eq_zero h3
    · exact B.orthonormal.inner_eq_zero h4
  · apply top_unique
    rw [← B.toBasis.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ≤ t i
    · exact Submodule.mem_iSup_of_mem (⟨i, hi⟩ : I) (Submodule.subset_span ⟨0, rfl⟩)
    · have hit : t i ≤ t (t i) := by rw [ht]; exact le_of_lt (lt_of_not_ge hi)
      apply Submodule.mem_iSup_of_mem (⟨t i, hit⟩ : I)
      apply Submodule.subset_span
      exact ⟨1, by change B (t (t i)) = B i; rw [ht]⟩

omit [FiniteDimensional F V] in
/-- Polynomial kernels are invariant under the original operator. -/
lemma polynomial_kernel_invariant (T : Module.End F V) (p : F[X]) :
    ∀ x ∈ LinearMap.ker (aeval T p), T x ∈ LinearMap.ker (aeval T p) := by
  intro x hx
  have hc := congrArg (fun f : F[X] => aeval T f x) (mul_comm p X)
  simp only [map_mul, aeval_X, Module.End.mul_apply] at hc
  change aeval T p (T x) = 0
  rw [hc, hx, map_zero]

/-- A Bezout selector is the actual orthogonal projection, because normality
makes the perpendicular of its invariant kernel invariant too. -/
theorem coprime_kernel_projection (T : Module.End F V) (hT : D05.normalOperator T)
    (p q : F[X]) (hc : IsCoprime p q) (hann : aeval T (p * q) = 0) :
    ∃ e : F[X], aeval T e = (LinearMap.ker (aeval T p)).starProjection.toLinearMap := by
  obtain ⟨a, b, hab⟩ := hc
  let M := LinearMap.ker (aeval T p)
  let e := b * q
  have hM := polynomial_kernel_invariant T p
  have hP := (M13.NormalReducing.invariant_subspace_reduces T M hT hM).2.1
  have hE (x : V) : aeval T e x ∈ M := by
    have hh : p * e = b * (p * q) := by dsimp [e]; ring
    have hz : aeval T p * aeval T e = 0 := by
      rw [← map_mul, hh, map_mul, hann, mul_zero]
    exact congrArg (fun S : Module.End F V => S x) hz
  have hfix (x : V) (hx : x ∈ M) : aeval T e x = x := by
    have hh := congrArg (fun f : F[X] => aeval T f x) hab
    simpa [map_add, map_mul, Module.End.mul_apply, show aeval T p x = 0 from hx, e] using hh
  have hzero (x : V) (hx : x ∈ M.orthogonal) : aeval T e x = 0 := by
    have hm := hE x
    have hp := CyclicLayers.polynomial_mem T M.orthogonal hP hx e
    exact M.isCompl_orthogonal.disjoint.le_bot ⟨hm, hp⟩
  refine ⟨e, ?_⟩
  ext x
  let y := M.starProjection x
  have hy : y ∈ M := M.starProjection_apply_mem x
  have hz : x - y ∈ M.orthogonal := M.sub_starProjection_mem_orthogonal x
  change aeval T e x = y
  calc
    aeval T e x = aeval T e y + aeval T e (x - y) := by rw [← map_add, add_sub_cancel]
    _ = y := by rw [hfix y hy, hzero _ hz, add_zero]

/-- Normality rules out nilpotent thickening of every polynomial kernel. -/
theorem polynomial_kernel_powers (T : Module.End F V) (hT : D05.normalOperator T)
    (p : F[X]) (k : ℕ) (hk : 0 < k) :
    LinearMap.ker (aeval T (p ^ k)) = LinearMap.ker (aeval T p) := by
  have hs := ((normal_semisimple T hT).aeval p).isFinitelySemisimple
  have he := hs.genEigenspace_eq_eigenspace (0 : F) (k := (k : ℕ∞)) (by exact_mod_cast hk)
  simpa [Module.End.genEigenspace_nat, Module.End.eigenspace_zero] using he

/-- Primary kernels, including higher powers and absent irreducibles, have
orthogonal polynomial projections. -/
theorem primary_projections : Specs.D05.M13.NormalClassification.OrthogonalCyclic.primary_projections := by
  intro F V _ _ _ _ T hT p _hp hirr k hk
  have heq := polynomial_kernel_powers T hT p k hk
  refine ⟨heq, ?_⟩
  suffices he : ∃ e : F[X], aeval T e = (LinearMap.ker (aeval T p)).starProjection.toLinearMap by
    simpa only [heq] using he
  by_cases hd : p ∣ minpoly F T
  · obtain ⟨q, hq⟩ := hd
    have hs := normal_minpoly_squarefree T hT
    rw [hq] at hs
    exact coprime_kernel_projection T hT p q
      (IsRelPrime.of_squarefree_mul hs).isCoprime (by rw [← hq]; exact minpoly.aeval F T)
  · have hc : IsCoprime p (minpoly F T) := (hirr.isCoprime_or_dvd _).resolve_right hd
    obtain ⟨a, b, hab⟩ := hc
    have hM : LinearMap.ker (aeval T p) = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro x hx
      have hh := congrArg (fun f : F[X] => aeval T f x) hab
      have hx' : aeval T p x = 0 := hx
      simpa [map_add, map_mul, Module.End.mul_apply, minpoly.aeval F T, hx'] using hh.symm
    refine ⟨0, ?_⟩
    simp [hM, Submodule.starProjection_bot]

theorem zero_decomposition : Specs.D05.M13.NormalClassification.OrthogonalCyclic.zero_decomposition := by
  intro F V _ _ _ _ _ T
  refine { monic := fun i => Fin.elim0 i
           nonconstant := fun i => Fin.elim0 i
           annihilator := fun i => Fin.elim0 i
           orthogonal := fun i => Fin.elim0 i
           spanning := ?_
           descending := fun i => Fin.elim0 i
           squarefree := fun i => Fin.elim0 i
           factorization := fun i => Fin.elim0 i
           invariant_factors := ?_ }
  · exact Subsingleton.elim _ _
  · exact (M10.InvariantFactors.zero_case T Module.finrank_zero_of_subsingleton).1

end D05.M13.NormalClassification.OrthogonalCyclic
