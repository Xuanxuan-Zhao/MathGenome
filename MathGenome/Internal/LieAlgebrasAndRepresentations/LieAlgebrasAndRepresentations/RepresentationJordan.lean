import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RepresentationJordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AbstractJordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SemisimpleBaseChange
import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
import Mathlib.LinearAlgebra.Eigenspace.Pi

noncomputable section
open scoped Classical
universe u v w t
namespace LieAlgebrasAndRepresentations.RepresentationJordan
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] [CharZero k]
  {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Both matrix Jordan parts normalize every Lie subalgebra containing the
original operator. This uses the polynomiality of their adjoint operators. -/
theorem jordan_parts_normalize (A : LieSubalgebra k (Module.End k V))
    {y S N : Module.End k V} (hy : y ∈ A)
    (hd : IsJordanDecomposition y S N) :
    (∀ z ∈ A, ⁅S,z⁆ ∈ A) ∧ (∀ z ∈ A, ⁅N,z⁆ ∈ A) := by
  have hs : S.IsSemisimple := (absolutely_semisimple_iff S).mp hd.2.2.1
  have hp := LieAlgebra.ad_mem_adjoin_of_isSemisimple hd.2.1.symm hd.2.2.2 hs
  have hq := LieAlgebra.ad_mem_adjoin_of_isNilpotent hd.2.1.symm hd.2.2.2 hs
  rw [add_comm N S, ← hd.1] at hp hq
  have hstable (z : Module.End k (Module.End k V))
      (hz : z ∈ Algebra.adjoin k {LieAlgebra.ad k (Module.End k V) y}) :
      ∀ a ∈ A, z a ∈ A := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    exact polynomial_preserves_subspace _ p A.toSubmodule
      (fun a ha => A.lie_mem hy ha)
  exact ⟨hstable _ hp, hstable _ hq⟩

/-- Perfect Lie algebras act by traceless operators in every representation. -/
theorem trace_representation_eq_zero {g : Type v} [LieRing g] [LieAlgebra k g]
    [FiniteDimensional k g] (hg : IsSemisimple k g)
    (ρ : g →ₗ⁅k⁆ Module.End k V) (x : g) : LinearMap.trace k V (ρ x) = 0 := by
  have hx : x ∈ Submodule.span k {⁅a,b⁆ | (a : g) (b : g)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]
    change x ∈ ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆
    rw [semisimple_perfect k g hg]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,b,rfl⟩ := hx
    rw [ρ.map_lie, LinearMap.trace_lie]
  | zero => simp
  | add x y _ _ hx hy => simp [hx,hy]
  | smul c x _ hx => simp [hx]

/-- Polynomial evaluation respects an intertwining linear map. -/
theorem aeval_intertwines {M : Type v} [AddCommGroup M] [Module k M]
    (f : V →ₗ[k] M) (a : Module.End k V) (b : Module.End k M)
    (h : b.comp f = f.comp a) (p : Polynomial k) :
    (Polynomial.aeval b p).comp f = f.comp (Polynomial.aeval a p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, LinearMap.smul_comp, LinearMap.comp_smul]
    rw [Module.End.commute_pow_left_of_commute h n]

/-- Semisimplicity descends along a surjective intertwiner. -/
theorem semisimple_of_surjective_intertwiner
    {M : Type v} [AddCommGroup M] [Module k M]
    (f : V →ₗ[k] M) (hf : Function.Surjective f)
    (a : Module.End k V) (b : Module.End k M)
    (h : b.comp f = f.comp a) (ha : a.IsSemisimple) : b.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  apply LinearMap.ext
  intro m
  obtain ⟨v,rfl⟩ := hf m
  have he := LinearMap.congr_fun (aeval_intertwines f a b h (minpoly k a)) v
  simpa only [LinearMap.comp_apply, minpoly.aeval, LinearMap.zero_apply, map_zero] using he

/-- Nilpotence descends along a surjective intertwiner, including zero spaces. -/
theorem nilpotent_of_surjective_intertwiner
    {M : Type v} [AddCommGroup M] [Module k M]
    (f : V →ₗ[k] M) (hf : Function.Surjective f)
    (a : Module.End k V) (b : Module.End k M)
    (h : b.comp f = f.comp a) (ha : IsNilpotent a) : IsNilpotent b := by
  obtain ⟨r,hr⟩ := ha
  refine ⟨r, LinearMap.ext fun m => ?_⟩
  obtain ⟨v,rfl⟩ := hf m
  have he := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h r) v
  simpa only [LinearMap.comp_apply, hr, LinearMap.zero_apply, map_zero] using he

/-- Abstract Jordan decompositions pass to every surjective Lie homomorphism.
No semisimplicity hypothesis is required on the source or target algebra here. -/
theorem abstract_jordan_map_surjective
    {g : Type v} [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    {h : Type t} [LieRing h] [LieAlgebra k h]
    (f : g →ₗ⁅k⁆ h) (hf : Function.Surjective f) {x s n : g}
    (hd : IsAbstractJordanDecomposition (k := k) x s n) :
    IsAbstractJordanDecomposition (k := k) (f x) (f s) (f n) := by
  haveI : FiniteDimensional k h := Module.Finite.of_surjective f.toLinearMap hf
  have hi (z : g) : (LieAlgebra.ad k h (f z)).comp f.toLinearMap =
      f.toLinearMap.comp (LieAlgebra.ad k g z) := by
    ext a
    exact (f.map_lie z a).symm
  refine ⟨by rw [hd.1, map_add], by rw [← f.map_lie, hd.2.1, map_zero], ?_, ?_⟩
  · apply (absolutely_semisimple_iff _).mpr
    exact semisimple_of_surjective_intertwiner f.toLinearMap hf _ _ (hi s)
      ((absolutely_semisimple_iff _).mp hd.2.2.1)
  · exact nilpotent_of_surjective_intertwiner f.toLinearMap hf _ _ (hi n) hd.2.2.2

/-- A commuting semisimple family has an internal sum decomposition indexed by
linear functionals, rather than unbundled functions. -/
theorem simultaneous_eigenspaces_internal [IsAlgClosed k]
    {H : Type t} [AddCommGroup H] [Module k H]
    (f : H →ₗ[k] Module.End k V) (hc : ∀ a b, Commute (f a) (f b))
    (hs : ∀ a, (f a).IsSemisimple) :
    DirectSum.IsInternal (fun χ : H →ₗ[k] k => ⨅ a, (f a).eigenspace (χ a)) := by
  let E (χ : H → k) : Submodule k V := ⨅ a, (f a).maxGenEigenspace (χ a)
  have he (χ : H → k) : E χ = ⨅ a, (f a).eigenspace (χ a) := by
    simp only [E, fun a => (hs a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
  have hi : iSupIndep E :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm (hc b a) c)
  have htop : (⨆ χ, E χ) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun a b _ => hc a b) (fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a))
  have hlinear (χ : H → k) (hχ : E χ ≠ ⊥) :
      ∃ l : H →ₗ[k] k, (l : H → k) = χ := by
    exact ⟨{ toFun := χ
             map_add' := Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute
               f χ ⊤ hχ hc
             map_smul' := Module.End.map_smul_of_iInf_genEigenspace_ne_bot f χ ⊤ hχ }, rfl⟩
  have hind : iSupIndep (fun χ : H →ₗ[k] k => E χ) :=
    hi.comp (fun a b h => LinearMap.ext (congrFun h))
  have hspan : (⨆ χ : H →ₗ[k] k, E χ) = ⊤ := by
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro χ
    by_cases hz : E χ = ⊥
    · simp [hz]
    · obtain ⟨l,hl⟩ := hlinear χ hz
      rw [← hl]
      exact le_iSup (fun l : H →ₗ[k] k => E l) l
  simpa only [he] using
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan

/-- On a nonzero irreducible module over an algebraically closed field,
normalizing operators differ from elements of a semisimple matrix algebra
by scalars. Tracelessness removes that scalar for a matrix Jordan part. -/
theorem jordan_parts_mem_of_irreducible [IsAlgClosed k]
    (A : LieSubalgebra k (Module.End k V))
    (hA : IsSemisimple k A) [LieModule.IsIrreducible k A V]
    {y S N : Module.End k V} (hy : y ∈ A)
    (hd : IsJordanDecomposition y S N) : S ∈ A ∧ N ∈ A := by
  have hnorm := (jordan_parts_normalize A hy hd).1
  let D : LieDerivation k A A :=
    { (LieAlgebra.ad k (Module.End k V) S).restrict hnorm with
      leibniz' := by
        intro a b
        apply Subtype.ext
        change ⁅S, ⁅(a : Module.End k V), (b : Module.End k V)⁆⁆ =
          ⁅(a : Module.End k V), ⁅S,(b : Module.End k V)⁆⁆ - ⁅(b : Module.End k V), ⁅S,(a : Module.End k V)⁆⁆
        rw [leibniz_lie, ← lie_skew (b : Module.End k V) ⁅S,(a : Module.End k V)⁆,
          sub_neg_eq_add, add_comm] }
  obtain ⟨z, hz, _⟩ := derivation_inner_unique k A hA D
  have hcomm (a : A) : Commute (S - z.val) a.val := by
    have he := congrArg (fun d : LieDerivation k A A => (d a).val) hz
    have he' : ⁅z.val, a.val⁆ = ⁅S, a.val⁆ := by
      rw [adjoint_apply] at he
      have hD : (D a).val = ⁅S,a.val⁆ := rfl
      exact he.trans hD
    rw [commute_iff_lie_eq, sub_lie, he', sub_self]
  let c : V →ₗ⁅k,A⁆ V :=
    { S - z.val with
      map_lie' := by
        intro a v
        exact LinearMap.congr_fun (hcomm a).eq v }
  obtain ⟨r, hr⟩ := ModuleCasimir.scalar_of_irreducible k A V c
  have hztr : LinearMap.trace k V z.val = 0 :=
    trace_representation_eq_zero hA A.incl z
  have hytr : LinearMap.trace k V y = 0 :=
    trace_representation_eq_zero hA A.incl ⟨y,hy⟩
  have hNtr : LinearMap.trace k V N = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hd.2.2.2).eq_zero
  have hStr : LinearMap.trace k V S = 0 := by
    rw [hd.1, map_add, hNtr, add_zero] at hytr
    exact hytr
  have hrtr := congrArg (LinearMap.trace k V) hr
  change LinearMap.trace k V (S - z.val) =
    LinearMap.trace k V (r • LinearMap.id) at hrtr
  haveI := LieModule.nontrivial_of_isIrreducible k A V
  have hrzero : r = 0 := by
    have hdim : (Module.finrank k V : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := k) (M := V)))
    simpa only [map_sub, hStr, hztr, sub_self, map_smul,
      LinearMap.trace_id, smul_eq_mul, eq_comm, mul_eq_zero, hdim, or_false] using hrtr
  have he : S = z.val := by
    change S - z.val = r • LinearMap.id at hr
    rw [hrzero, zero_smul] at hr
    exact sub_eq_zero.mp hr
  refine ⟨he ▸ z.property, ?_⟩
  have hN : N = y - S := by rw [hd.1]; abel
  rw [hN]
  exact A.sub_mem hy (he ▸ z.property)

/-- Full uniqueness of abstract Jordan parts, using the faithful adjoint map. -/
theorem abstract_jordan_unique {g : Type v} [LieRing g] [LieAlgebra k g]
    [FiniteDimensional k g] (hg : IsSemisimple k g) {x s n s' n' : g}
    (h₁ : IsAbstractJordanDecomposition (k := k) x s n)
    (h₂ : IsAbstractJordanDecomposition (k := k) x s' n') : s = s' ∧ n = n' := by
  have hh := jordan_decomposition_unique (abstract_jordan_to_linear h₁)
    (abstract_jordan_to_linear h₂)
  exact ⟨adjoint_end_injective hg hh.1, adjoint_end_injective hg hh.2⟩

/-- A faithful irreducible matrix representation preserves the abstract parts.
The normalizer argument proves the matrix parts lie in the algebra first. -/
theorem matrix_preserves_jordan_of_irreducible [IsAlgClosed k]
    (A : LieSubalgebra k (Module.End k V)) (hA : IsSemisimple k A)
    [LieModule.IsIrreducible k A V] {x s n : A}
    (hd : IsAbstractJordanDecomposition (k := k) x s n) :
    IsJordanDecomposition x.val s.val n.val := by
  obtain ⟨S,N,hlin,_,_,_⟩ := linear_jordan_decomposition x.val
  obtain ⟨hS,hN⟩ := jordan_parts_mem_of_irreducible A hA x.property hlin
  let s' : A := ⟨S,hS⟩
  let n' : A := ⟨N,hN⟩
  have hnorm := (jordan_parts_normalize A x.property hlin).1
  have hss : (LieAlgebra.ad k A s').IsSemisimple := by
    have hh := LieAlgebra.ad_isSemisimple_of_isSemisimple
      ((absolutely_semisimple_iff S).mp hlin.2.2.1)
    have hinv : A.toSubmodule ∈ (LieAlgebra.ad k (Module.End k V) S).invtSubmodule := by
      rw [Module.End.mem_invtSubmodule]
      exact hnorm
    exact hh.restrict hinv
  have hnew : IsAbstractJordanDecomposition (k := k) x s' n' := by
    refine ⟨Subtype.ext hlin.1, Subtype.ext ?_,
      (absolutely_semisimple_iff _).mpr hss, ?_⟩
    · exact (commute_iff_lie_eq.mp hlin.2.1)
    · exact LieAlgebra.isNilpotent_ad_of_isNilpotent (L := A) hlin.2.2.2
  obtain ⟨hs,hn⟩ := abstract_jordan_unique hA hd hnew
  have hs' : s.val = S := congrArg Subtype.val hs
  have hn' : n.val = N := congrArg Subtype.val hn
  rw [hs',hn']
  exact hlin

/-- The image of a representation of a semisimple algebra is semisimple. -/
theorem image_semisimple {g : Type v} [LieRing g] [LieAlgebra k g]
    [FiniteDimensional k g] [LieRingModule g V] [LieModule k g V]
    (hg : IsSemisimple k g) : IsSemisimple k (ModuleCasimir.image k g V) := by
  haveI := ModuleCasimir.ideal_isKilling k g hg (ModuleCasimir.support k g V)
  haveI := (ModuleCasimir.supportEquivImage k g V hg).isKilling
  exact LieAlgebra.radical_eq_bot (R := k) (L := ModuleCasimir.image k g V)

/-- Passing from the acting algebra to its image does not change invariant
subspaces, and hence preserves irreducibility. -/
theorem image_irreducible {g : Type v} [LieRing g] [LieAlgebra k g]
    [LieRingModule g V] [LieModule k g V] [LieModule.IsIrreducible k g V] :
    LieModule.IsIrreducible k (ModuleCasimir.image k g V) V := by
  haveI := LieModule.nontrivial_of_isIrreducible k g V
  apply LieModule.IsIrreducible.mk
  intro W hW
  let W' : LieSubmodule k g V :=
    { W.toSubmodule with
      lie_mem := by
        intro x m hm
        exact W.lie_mem (x := (LieModule.toEnd k g V).rangeRestrict x) hm }
  have hW' : W' ≠ ⊥ := by
    intro hh
    apply hW
    apply (LieSubmodule.toSubmodule_inj _ _).mp
    exact congrArg (fun U : LieSubmodule k g V => U.toSubmodule) hh
  have ht : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'
  apply (LieSubmodule.toSubmodule_inj _ _).mp
  exact congrArg (fun U : LieSubmodule k g V => U.toSubmodule) ht

/-- LA-C07 for arbitrary irreducible modules over an algebraically closed field;
faithfulness is recovered by passing to the semisimple image. -/
theorem preserves_jordan_irreducible [IsAlgClosed k]
    {g : Type v} [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [LieRingModule g V] [LieModule k g V] [LieModule.IsIrreducible k g V]
    (hg : IsSemisimple k g) {x s n : g}
    (hd : IsAbstractJordanDecomposition (k := k) x s n) :
    IsJordanDecomposition (LieModule.toEnd k g V x)
      (LieModule.toEnd k g V s) (LieModule.toEnd k g V n) := by
  let f := (LieModule.toEnd k g V).rangeRestrict
  have hf : Function.Surjective f := by
    rintro ⟨y,z,rfl⟩
    exact ⟨z,rfl⟩
  haveI := image_irreducible (k := k) (V := V) (g := g)
  exact matrix_preserves_jordan_of_irreducible (ModuleCasimir.image k g V)
    (image_semisimple hg) (abstract_jordan_map_surjective f hf hd)

/-- Assemble irreducible summands by comparing restrictions of the polynomial
matrix Jordan parts; no choice of compatible matrix bases is required. -/
theorem preserves_jordan_of_isAlgClosed [IsAlgClosed k]
    {g : Type v} [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [LieRingModule g V] [LieModule k g V]
    (hg : IsSemisimple k g) {x s n : g}
    (hd : IsAbstractJordanDecomposition (k := k) x s n) :
    IsJordanDecomposition (LieModule.toEnd k g V x)
      (LieModule.toEnd k g V s) (LieModule.toEnd k g V n) := by
  let ρ := LieModule.toEnd k g V
  obtain ⟨S,N,hlin,_,hstable,_⟩ := linear_jordan_decomposition (ρ x)
  obtain ⟨T,_,hT,hint⟩ := CompleteReducibility.finite_simple_decomposition k g V hg
  have hlocal (W : T) : ∀ v ∈ W.val,
      ρ s v = S v ∧ ρ n v = N v := by
    haveI := hT W.val W.property
    have hW : ∀ v ∈ W.val.toSubmodule, ρ x v ∈ W.val.toSubmodule :=
      fun v hv => W.val.lie_mem hv
    have hSW := (hstable W.val.toSubmodule hW).1
    have hNW := (hstable W.val.toSubmodule hW).2
    let S' : Module.End k W.val := S.restrict hSW
    let N' : Module.End k W.val := N.restrict hNW
    have hsS : S'.IsSemisimple := by
      exact ((absolutely_semisimple_iff S).mp hlin.2.2.1).restrict
        (show W.val.toSubmodule ∈ S.invtSubmodule from hSW)
    have hr : IsJordanDecomposition (LieModule.toEnd k g W.val x) S' N' := by
      refine ⟨?_, LinearMap.restrict_commute hlin.2.1 hSW hNW,
        (absolutely_semisimple_iff _).mpr hsS, Module.End.isNilpotent.restrict hNW hlin.2.2.2⟩
      ext v
      exact LinearMap.congr_fun hlin.1 v.val
    have he := jordan_decomposition_unique (preserves_jordan_irreducible hg hd) hr
    intro v hv
    exact ⟨congrArg Subtype.val (LinearMap.congr_fun he.1 ⟨v,hv⟩),
      congrArg Subtype.val (LinearMap.congr_fun he.2 ⟨v,hv⟩)⟩
  have he (v : V) : ρ s v = S v ∧ ρ n v = N v := by
    have hv : v ∈ ⨆ W : T, W.val.toSubmodule := by
      rw [hint.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction _
      (motive := fun v => ρ s v = S v ∧ ρ n v = N v)
      hv (fun W v hv => hlocal W v hv) ?_ ?_
    · simp
    · intro a b ha hb
      simp [ha.1,ha.2,hb.1,hb.2]
  have hs : ρ s = S := LinearMap.ext (fun v => (he v).1)
  have hn : ρ n = N := LinearMap.ext (fun v => (he v).2)
  change IsJordanDecomposition (ρ x) (ρ s) (ρ n)
  rw [hs,hn]
  exact hlin

open scoped TensorProduct

/-- LA-C07: preservation over the original characteristic-zero field. -/
theorem preserves_jordan :
    Specs.LieAlgebrasAndRepresentations.RepresentationJordan.preserves_jordan_type.{u,v,w} := by
  intro k g V _ _ _ _ _ _ _ _ hg ρ x s n hd
  letI := LieRingModule.compLieHom V ρ
  letI := LieModule.compLieHom V ρ
  let K := AlgebraicClosure k
  have had (z : g) : LieAlgebra.ad K (K ⊗[k] g) ((1 : K) ⊗ₜ[k] z) =
      (LieAlgebra.ad k g z).baseChange K := by
    ext a y
    simp [LieAlgebra.ad_apply, LieAlgebra.ExtendScalars.bracket_tmul]
  have hdK : IsAbstractJordanDecomposition (k := K)
      ((1 : K) ⊗ₜ[k] x) ((1 : K) ⊗ₜ[k] s) ((1 : K) ⊗ₜ[k] n) := by
    refine ⟨by simp only [hd.1, TensorProduct.tmul_add], ?_, ?_, ?_⟩
    · simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, hd.2.1,
        TensorProduct.tmul_zero]
    · apply (absolutely_semisimple_iff _).mpr
      rw [had]
      exact hd.2.2.1
    · rw [had]
      exact hd.2.2.2.map (Module.End.baseChangeHom k K g)
  have hK := preserves_jordan_of_isAlgClosed
    (V := K ⊗[k] V) (lieAlgebra_semisimple_baseChange k K g hg) hdK
  have hrep (z : g) : LieModule.toEnd K (K ⊗[k] g) (K ⊗[k] V) ((1 : K) ⊗ₜ[k] z) =
      (ρ z).baseChange K := LieModule.toEnd_baseChange k K g V z
  rw [hrep x,hrep s,hrep n] at hK
  refine ⟨by rw [hd.1, map_add], ?_, ?_, ?_⟩
  · rw [commute_iff_lie_eq, ← ρ.map_lie, hd.2.1, map_zero]
  · exact (absolutely_semisimple_iff _).mp hK.2.2.1
  · exact (IsNilpotent.map_iff (f := Module.End.baseChangeHom k K V)
      (end_baseChange_injective (K := K))).mp hK.2.2.2

/-- Both explicit equalities in (3.10) follow from full linear uniqueness. -/
theorem jordan_parts_eq :
    Specs.LieAlgebrasAndRepresentations.RepresentationJordan.jordan_parts_eq_type.{u,v,w} := by
  intro k g V _ _ _ _ _ _ _ _ hg ρ x s n S N hd hlin
  exact jordan_decomposition_unique (preserves_jordan k g V hg ρ x s n hd) hlin

/-- The abstract decomposition of an adjoint-semisimple element is (a,0). -/
theorem toral_acts_semisimply :
    Specs.LieAlgebrasAndRepresentations.RepresentationJordan.toral_acts_semisimply_type.{u,v,w} := by
  intro k g V _ _ _ _ _ _ _ _ hg ρ H _ hs a
  have hd : IsAbstractJordanDecomposition (k := k) a.val a.val 0 :=
    ⟨by simp, by simp, hs a, by simpa using (IsNilpotent.zero : IsNilpotent (0 : Module.End k g))⟩
  exact (preserves_jordan k g V hg ρ _ _ _ hd).2.2.1

/-- Canonical simultaneous weight decomposition, including the zero cases. -/
theorem toral_weight_decomposition :
    Specs.LieAlgebrasAndRepresentations.RepresentationJordan.toral_weight_decomposition_type.{u,v,w} := by
  intro k g V _ _ _ _ _ _ _ _ _ hg ρ H hab hs
  let f : H →ₗ[k] Module.End k V := ρ.toLinearMap.comp H.incl.toLinearMap
  have hc (a b : H) : Commute (f a) (f b) := by
    rw [commute_iff_lie_eq]
    change ⁅ρ a.val, ρ b.val⁆ = 0
    rw [← ρ.map_lie]
    have he : ⁅a.val,b.val⁆ = 0 := congrArg (fun z : H => z.val) (hab a b)
    rw [he, map_zero]
  have hf (a : H) : (f a).IsSemisimple :=
    (absolutely_semisimple_iff _).mp (toral_acts_semisimply k g V hg ρ H hab hs a)
  exact simultaneous_eigenspaces_internal f hc hf

end LieAlgebrasAndRepresentations.RepresentationJordan
