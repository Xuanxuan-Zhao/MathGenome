import Specs.LinearAlgebraicGroups.Flag.PluckerEmbedding
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Flag.GrassmannianCharts
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

import LinearAlgebraicGroups.Flag.ProjectiveSpaces
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace LinearAlgebraicGroups.PluckerEmbedding

open Specs.PluckerEmbedding

noncomputable section

section ExteriorBaseChange

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (d : ℕ) (M : Type u) [AddCommGroup M] [Module R M]

private def degreeProjection : ExteriorAlgebra R M →ₗ[R] Wedge R d M :=
  (DirectSum.component R ℕ (fun i => ↥(Wedge R i M)) d).comp
    (ExteriorAlgebra.GradedAlgebra.liftι R M).toLinearMap

private theorem degreeProjection_split :
    (degreeProjection R d M).comp (Submodule.subtype (Wedge R d M)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change DirectSum.component R ℕ (fun i => ↥(Wedge R i M)) d
    (ExteriorAlgebra.GradedAlgebra.liftι R M x.val) = x
  rw [ExteriorAlgebra.GradedAlgebra.liftι_eq]
  change (DirectSum.component R ℕ (fun i => ↥(Wedge R i M)) d)
    ((DirectSum.lof R ℕ (fun i => ↥(Wedge R i M)) d) x) = x
  rw [DirectSum.component.of, dite_eq_left rfl]

private theorem exteriorAlgebra_compare_wedge (s : S) (v : Fin d → M) :
    ExteriorAlgebra.baseChangeEquiv R M S
        (s ⊗ₜ[R] (exteriorPower.ιMulti R d v).val) =
      s • (exteriorPower.ιMulti S d (fun i => (1 : S) ⊗ₜ[R] v i)).val := by
  suffices h : ExteriorAlgebra.baseChangeEquiv R M S
      ((1 : S) ⊗ₜ[R] (exteriorPower.ιMulti R d v).val) =
      (exteriorPower.ιMulti S d (fun i => (1 : S) ⊗ₜ[R] v i)).val by
    have he := (ExteriorAlgebra.baseChangeEquiv R M S).toLinearEquiv.map_smul s
      ((1 : S) ⊗ₜ[R] (exteriorPower.ιMulti R d v).val)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, h,
      AlgEquiv.toLinearEquiv_apply] using he
  let incl := Algebra.TensorProduct.includeRight (R := R) (A := S) (B := ExteriorAlgebra R M)
  change (ExteriorAlgebra.baseChangeEquiv R M S) (incl (ExteriorAlgebra.ιMulti R d v)) =
    ExteriorAlgebra.ιMulti S d (fun i => (1 : S) ⊗ₜ[R] v i)
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact ExteriorAlgebra.baseChangeEquiv_apply R M S 1 (v i)

private def exteriorComparisonMap :
    S ⊗[R] Wedge R d M →ₗ[S] Wedge S d (S ⊗[R] M) :=
  (degreeProjection S d (S ⊗[R] M)).comp
    ((ExteriorAlgebra.baseChangeEquiv R M S).toLinearEquiv.toLinearMap.comp
      ((Submodule.subtype (Wedge R d M)).baseChange S))

private theorem exteriorComparisonMap_wedge (s : S) (v : Fin d → M) :
    exteriorComparisonMap R S d M (s ⊗ₜ[R] exteriorPower.ιMulti R d v) =
      s • exteriorPower.ιMulti S d (fun i => (1 : S) ⊗ₜ[R] v i) := by
  have h (x : Wedge S d (S ⊗[R] M)) :
      degreeProjection S d (S ⊗[R] M) x.val = x :=
    LinearMap.congr_fun (degreeProjection_split S d (S ⊗[R] M)) x
  simp only [exteriorComparisonMap, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    Submodule.subtype_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
    exteriorAlgebra_compare_wedge, map_smul, h]

private theorem exteriorComparisonMap_subtype :
    (Submodule.subtype (Wedge S d (S ⊗[R] M))).comp (exteriorComparisonMap R S d M) =
      (ExteriorAlgebra.baseChangeEquiv R M S).toLinearEquiv.toLinearMap.comp
        ((Submodule.subtype (Wedge R d M)).baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s
  have h (z : Wedge R d M) :
      (exteriorComparisonMap R S d M (s ⊗ₜ[R] z)).val =
        ExteriorAlgebra.baseChangeEquiv R M S (s ⊗ₜ[R] z.val) := by
    refine Submodule.span_induction (s := Set.range (exteriorPower.ιMulti R d (M := M)))
      (p := fun z _ => (exteriorComparisonMap R S d M (s ⊗ₜ[R] z)).val =
        ExteriorAlgebra.baseChangeEquiv R M S (s ⊗ₜ[R] z.val)) ?_ ?_ ?_ ?_
      (by rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top)
    · rintro _ ⟨v, rfl⟩
      rw [exteriorComparisonMap_wedge, exteriorAlgebra_compare_wedge]
      rfl
    · simp
    · intro x y _ _ hx hy
      simpa only [TensorProduct.tmul_add, map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
    · intro a x _ hx
      have hh := congrArg (fun z : ExteriorAlgebra S (S ⊗[R] M) => algebraMap R S a • z) hx
      have ht {N : Type u} [AddCommGroup N] [Module R N] (z : N) :
          s ⊗ₜ[R] (a • z) = (algebraMap R S a) • (s ⊗ₜ[R] z) := by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
        rfl
      simpa only [Submodule.coe_smul_of_tower, ht, map_smul, Submodule.coe_smul] using hh
  intro z
  exact h z

private theorem exteriorComparisonMap_injective :
    Function.Injective (exteriorComparisonMap R S d M) := by
  have h : ((degreeProjection R d M).baseChange S).comp
      ((Submodule.subtype (Wedge R d M)).baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, degreeProjection_split, LinearMap.baseChange_id]
  apply Function.Injective.of_comp (f := (Submodule.subtype (Wedge S d (S ⊗[R] M))))
  change Function.Injective ((Submodule.subtype (Wedge S d (S ⊗[R] M))).comp
    (exteriorComparisonMap R S d M))
  rw [exteriorComparisonMap_subtype]
  exact (ExteriorAlgebra.baseChangeEquiv R M S).injective.comp
    (fun {x y} hxy => by
      have hh := congrArg ((degreeProjection R d M).baseChange S) hxy
      change (((degreeProjection R d M).baseChange S).comp
        ((Submodule.subtype (Wedge R d M)).baseChange S)) x =
          (((degreeProjection R d M).baseChange S).comp
            ((Submodule.subtype (Wedge R d M)).baseChange S)) y at hh
      simpa only [h, LinearMap.id_apply] using hh)

private theorem exteriorComparisonMap_surjective :
    Function.Surjective (exteriorComparisonMap R S d M) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  let pureTensors : Set (S ⊗[R] M) := { x | ∃ s m, s ⊗ₜ[R] m = x }
  have hspan : Submodule.span S pureTensors = ⊤ :=
    Submodule.span_eq_top_of_span_eq_top R S _ (TensorProduct.span_tmul_eq_top R S M)
  rw [← exteriorPower.ιMulti_span_of_span S d (S ⊗[R] M) hspan, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  have hparts (i : Fin d) : ∃ (s : S) (m : M), s ⊗ₜ[R] m = v i :=
    hv (Set.mem_range_self i)
  choose s m hm using hparts
  have heq : v = fun i => s i • ((1 : S) ⊗ₜ[R] m i) := by
    funext i
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hm]
  rw [heq, AlternatingMap.map_smul_univ]
  exact ⟨(∏ i, s i) ⊗ₜ[R] exteriorPower.ιMulti R d m,
    exteriorComparisonMap_wedge R S d M _ _⟩

private def exteriorComparison : ExteriorComparison R S d M where
  equiv := LinearEquiv.ofBijective (exteriorComparisonMap R S d M)
    ⟨exteriorComparisonMap_injective R S d M, exteriorComparisonMap_surjective R S d M⟩
  pure v := by
    change exteriorComparisonMap R S d M _ = _
    rw [exteriorComparisonMap_wedge, one_smul]

private theorem exteriorComparison_naturality {N : Type u} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (exteriorComparison R S d N).equiv.toLinearMap.comp ((exteriorPower.map d f).baseChange S)
      = (exteriorPower.map d (f.baseChange S)).comp (exteriorComparison R S d M).equiv.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s z
  refine Submodule.span_induction (s := Set.range (exteriorPower.ιMulti R d (M := M)))
    (p := fun z _ => ((exteriorComparison R S d N).equiv.toLinearMap.comp
        ((exteriorPower.map d f).baseChange S)) (s ⊗ₜ[R] z) =
      ((exteriorPower.map d (f.baseChange S)).comp
        (exteriorComparison R S d M).equiv.toLinearMap) (s ⊗ₜ[R] z)) ?_ ?_ ?_ ?_
    (by rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top)
  · rintro _ ⟨v, rfl⟩
    change exteriorComparisonMap R S d N (((exteriorPower.map d f).baseChange S)
      (s ⊗ₜ[R] exteriorPower.ιMulti R d v)) =
      exteriorPower.map d (f.baseChange S) (exteriorComparisonMap R S d M
        (s ⊗ₜ[R] exteriorPower.ιMulti R d v))
    simp only [LinearMap.baseChange_tmul, exteriorPower.map_apply_ιMulti, exteriorComparisonMap_wedge,
      map_smul]
    rfl
  · simp
  · intro x y _ _ hx hy
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  · intro a x _ hx
    have ht : s ⊗ₜ[R] (a • x) = (algebraMap R S a) • (s ⊗ₜ[R] x) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
      rfl
    simpa only [ht, map_smul] using congrArg
      (fun z : Wedge S d (S ⊗[R] N) => (algebraMap R S a) • z) hx

end ExteriorBaseChange

open Specs.GrassmannianCharts Specs.ProjectiveSpaces

private theorem tensorWedge_ext {R S P : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module S P] {d : ℕ}
    {f g : S ⊗[R] Wedge R d M →ₗ[S] P}
    (h : ∀ v : Fin d → M, f ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R d v) =
      g ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R d v)) : f = g := by
  let _ : Module R P := Module.restrictScalars R S P
  let _ : IsScalarTower R S P := IsScalarTower.restrictScalars R S P
  let a := TensorProduct.mk R S (Wedge R d M) 1
  have he : (f.restrictScalars R).comp a = (g.restrictScalars R).comp a :=
    exteriorPower.linearMap_ext (AlternatingMap.ext h)
  apply TensorProduct.AlgebraTensorModule.ext
  intro s z
  have hh : f (1 ⊗ₜ[R] z) = g (1 ⊗ₜ[R] z) :=
    LinearMap.congr_fun he z
  have ht : s ⊗ₜ[R] z = s • ((1 : S) ⊗ₜ[R] z) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ht, map_smul, map_smul, hh]

private theorem nestedTensorWedge_ext {R S T P : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    {M : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module T P] {d : ℕ}
    {f g : T ⊗[S] (S ⊗[R] Wedge R d M) →ₗ[T] P}
    (h : ∀ v : Fin d → M,
      f ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R d v)) =
        g ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R d v))) : f = g := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T (Wedge R d M)
  have he : f.comp c.symm.toLinearMap = g.comp c.symm.toLinearMap := by
    apply tensorWedge_ext
    intro v
    simpa only [c, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul] using h v
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun he (c x)

private theorem exteriorComparison_tower (R S T M : Type u) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [AddCommGroup M] [Module R M] (d : ℕ) :
    (exteriorComparison R T d M).equiv.toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T (Wedge R d M)).toLinearMap =
      (exteriorPower.map d
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap).comp
        ((exteriorComparison S T d (S ⊗[R] M)).equiv.toLinearMap.comp
          ((exteriorComparison R S d M).equiv.toLinearMap.baseChange T)) := by
  apply nestedTensorWedge_ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
    LinearMap.baseChange_tmul, ExteriorComparison.pure, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

private theorem range_baseChange {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (f.baseChange S).range = f.range.baseChange S := by
  change (f.baseChange S).range = (f.range.subtype.baseChange S).range
  have hf : f.range.subtype.comp f.rangeRestrict = f := by ext; rfl
  conv_lhs => rw [← hf]
  rw [LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (LinearMap.baseChange_surjective S f.surjective_rangeRestrict))]

private theorem baseChange_map_submodule {R S M N : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : Submodule R M) (f : M →ₗ[R] N) :
    (P.map f).baseChange S = (P.baseChange S).map (f.baseChange S) := by
  have h : (f.comp P.subtype).range = P.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  calc
    (P.map f).baseChange S = ((f.comp P.subtype).range).baseChange S := congrArg _ h.symm
    _ = ((f.comp P.subtype).baseChange S).range := (range_baseChange (S := S) _).symm
    _ = (P.baseChange S).map (f.baseChange S) := by
      rw [LinearMap.baseChange_comp, LinearMap.range_comp]
      rfl

private theorem mapPlane_range {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {d : ℕ} {A B : TestAlgebra k} (a : A ⟶ B) (L : Plane k V d A) :
    let _ : Algebra A B := a.hom.toAlgebra
    let _ : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    (Module.Grassmannian.map a.hom L).toSubmodule =
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B V).toLinearMap.comp
        (LinearMap.baseChange (↥B) (Submodule.subtype (R := ↥A) L.toSubmodule))).range := by
  let _ : Algebra A B := a.hom.toAlgebra
  let _ : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B V
  let P := L.toSubmodule
  have h : (P.mkQ.baseChange (↥B)).ker = (P.subtype.baseChange (↥B)).range := by
    ext x
    change x ∈ (P.mkQ.lTensor (↥B)).ker ↔ x ∈ (P.subtype.lTensor (↥B)).range
    rw [lTensor_mkQ]
  rw [Module.Grassmannian.map_toSubmodule]
  change (L.toSubmodule.mkQ.baseChange B ∘ₗ c.symm.toLinearMap).ker =
    (c.toLinearMap.comp (L.toSubmodule.subtype.baseChange (↥B))).range
  rw [LinearMap.range_comp, LinearMap.ker_comp, Submodule.map_equiv_eq_comap_symm,
    h]

section AffineExteriorLines

variable {R : Type u} [CommRing R] {M N : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private theorem wedgeRange_eq (d : ℕ) (f : M →ₗ[R] N) :
    (exteriorPower.map d f).range = (exteriorPower.map d f.range.subtype).range := by
  have hfac : f = f.range.subtype.comp f.rangeRestrict := by ext x; rfl
  conv_lhs => rw [hfac]
  rw [exteriorPower.map_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (exteriorPower.map_surjective (n := d) f.surjective_rangeRestrict))]

private theorem rangeCompl {f : M →ₗ[R] N} {g : N →ₗ[R] M}
    (hg : g.comp f = LinearMap.id) : ∃ C, IsCompl f.range C := by
  let e := LinearEquiv.ofLeftInverse (f := f) (g := g) (fun x => LinearMap.congr_fun hg x)
  let r := e.toLinearMap.comp g
  refine ⟨r.ker, LinearMap.isCompl_of_proj (f := r) ?_⟩
  rintro ⟨x, ⟨y, rfl⟩⟩
  apply Subtype.ext
  change f (g (f y)) = f y
  exact congrArg f (LinearMap.congr_fun hg y)

private theorem rankAtStalk_exterior [Module.Finite R M] [Module.Projective R M]
    {d : ℕ} (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = d)
    (p : PrimeSpectrum R) : Module.rankAtStalk (Wedge R d M) p = 1 := by
  have proj : Module.Projective R (Wedge R d M) := by
    obtain ⟨i, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
    let s : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
    exact Module.Projective.of_split (exteriorPower.map d i) (exteriorPower.map d s)
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  let _ := proj
  rw [Module.rankAtStalk_eq]
  let F := p.asIdeal.ResidueField
  change Module.finrank F (F ⊗[R] Wedge R d M) = 1
  rw [(exteriorComparison R F d M).equiv.finrank_eq, exteriorPower.finrank_eq]
  have hh : Module.finrank F (F ⊗[R] M) = d := (Module.rankAtStalk_eq (M := M) p).symm.trans (h p)
  rw [hh, Nat.choose_self]

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  {d : ℕ}

private def affineWedgeLine (hplane : PlaneSplitAndRank.{u}) (hd : d ≤ Module.finrank k V)
    (A : TestAlgebra k) (L : Plane k V d A) : AffineLine k (Wedge k d V) A := by
  have h := hplane k V d hd A L
  letI := h.2.1
  letI := h.2.2.1
  let C := h.1.choose
  let r := L.toSubmodule.projectionOnto C h.1.choose_spec
  let c := (exteriorComparison k A d V).equiv
  let f := c.symm.toLinearMap.comp (exteriorPower.map (M := ↥L.toSubmodule) d L.toSubmodule.subtype)
  let g := (exteriorPower.map (N := ↥L.toSubmodule) d r).comp c.toLinearMap
  have hr : g.comp f = LinearMap.id := by
    dsimp only [f, g]
    rw [LinearMap.comp_assoc, LinearEquiv.comp_symm_assoc, ← exteriorPower.map_comp,
      Submodule.projectionOnto_comp_subtype, exteriorPower.map_id]
  let e := LinearEquiv.ofLeftInverse (f := f) (g := g) (fun x => LinearMap.congr_fun hr x)
  letI : Module.Projective A (Wedge A d L.toSubmodule) := Module.Projective.of_split f g hr
  refine ⟨f.range, rangeCompl hr, Module.Finite.of_surjective e.toLinearMap e.surjective,
    Module.Projective.of_equiv' e, ?_⟩
  intro p
  rw [← Module.rankAtStalk_eq_of_equiv e]
  exact rankAtStalk_exterior h.2.2.2 p


set_option maxHeartbeats 500000 in
private theorem extendedWedge_baseChange {k A B V : Type u} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [AddCommGroup V] [Module k V] (d : ℕ) (P : Submodule A (A ⊗[k] V)) :
    let cᵥ := TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B V
    let c𝓌 := TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B (Wedge k d V)
    let Q := (cᵥ.toLinearMap.comp (P.subtype.baseChange B)).range
    ((exteriorComparison k B d V).equiv.symm.toLinearMap.comp
      (exteriorPower.map (M := ↥Q) d Q.subtype)).range =
      ((((exteriorComparison k A d V).equiv.symm.toLinearMap.comp
        (exteriorPower.map (M := ↥P) d P.subtype)).range).baseChange B).map c𝓌.toLinearMap := by
  let cA := (exteriorComparison k A d V).equiv
  let cB := (exteriorComparison k B d V).equiv
  let cᵥ := TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B V
  let c𝓌 := TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B (Wedge k d V)
  let f : P →ₗ[A] A ⊗[k] V := P.subtype
  let g : B ⊗[A] ↥P →ₗ[B] B ⊗[k] V := cᵥ.toLinearMap.comp (f.baseChange B)
  let w := exteriorPower.map (R := A) (M := ↥P) (N := A ⊗[k] V) d f
  let n := (exteriorComparison A B d (A ⊗[k] V)).equiv
  let m := (exteriorComparison A B d P).equiv
  have ht : cB.toLinearMap.comp c𝓌.toLinearMap =
      (exteriorPower.map d cᵥ.toLinearMap).comp
        (n.toLinearMap.comp (cA.toLinearMap.baseChange B)) :=
    exteriorComparison_tower k A B V d
  have hn := exteriorComparison_naturality A B d (↥P) (N := A ⊗[k] V) f
  have he : cB.toLinearMap.comp (c𝓌.toLinearMap.comp
        ((cA.symm.toLinearMap.comp w).baseChange B)) =
      (exteriorPower.map (M := B ⊗[A] ↥P) d g).comp m.toLinearMap := by
    have hcancel : (cA.toLinearMap.baseChange B).comp
        ((cA.symm.toLinearMap.comp w).baseChange B) = w.baseChange B := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.comp_assoc, LinearEquiv.comp_symm,
        LinearMap.id_comp]
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun ht (((cA.symm.toLinearMap.comp w).baseChange B) x)
    change cB (c𝓌 _) = exteriorPower.map d cᵥ.toLinearMap (n
      (((cA.toLinearMap.baseChange B).comp
        ((cA.symm.toLinearMap.comp w).baseChange B)) x)) at hx
    rw [hcancel] at hx
    have hnx := LinearMap.congr_fun hn x
    change n ((w.baseChange B) x) = exteriorPower.map d (f.baseChange B) (m x) at hnx
    rw [hnx] at hx
    change cB (c𝓌 _) = exteriorPower.map d g (m x)
    rw [hx]
    dsimp only [g]
    rw [exteriorPower.map_comp]
    rfl
  have he' : (c𝓌.toLinearMap.comp ((cA.symm.toLinearMap.comp w).baseChange B)) =
      cB.symm.toLinearMap.comp ((exteriorPower.map (M := B ⊗[A] ↥P) d g).comp m.toLinearMap) := by
    exact (cB.eq_toLinearMap_symm_comp _ _).mpr he

  change (cB.symm.toLinearMap.comp (exteriorPower.map (M := ↥g.range) d g.range.subtype)).range =
    ((cA.symm.toLinearMap.comp w).range.baseChange B).map c𝓌.toLinearMap
  rw [← range_baseChange, ← LinearMap.range_comp, he', ← LinearMap.comp_assoc,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr m.surjective),
    LinearMap.range_comp]
  simp only [LinearMap.range_comp, wedgeRange_eq d g]

omit [Module.Finite k V] in
private theorem lineSubmodule_baseChange {A B : TestAlgebra k} (a : A ⟶ B) (L : Plane k V d A) :
    lineSubmodule (exteriorComparison k B d V) (Module.Grassmannian.map a.hom L) =
      changeLineSubmodule k (Wedge k d V) a (lineSubmodule (exteriorComparison k A d V) L) := by
  let _ : Algebra A B := a.hom.toAlgebra
  let _ : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let functorialImage (P : Submodule B (B ⊗[k] V)) :=
    ((exteriorComparison k B d V).equiv.symm.toLinearMap.comp
      (exteriorPower.map (M := ↥P) d P.subtype)).range
  change functorialImage (Module.Grassmannian.map a.hom L).toSubmodule = _
  rw [mapPlane_range a L]
  exact extendedWedge_baseChange (k := k) (A := ↥A) (B := ↥B) d L.toSubmodule

private def affineExteriorLines (hplane : PlaneSplitAndRank.{u}) (hd : d ≤ Module.finrank k V) :
    AffineExteriorLines k V d where
  compare A := exteriorComparison k A d V
  line A L := affineWedgeLine hplane hd A L
  image_eq _ _ := rfl
  baseChange := lineSubmodule_baseChange


private theorem affineExteriorEquivarianceProof : AffineExteriorEquivariance.{u} := by
  intro k V _ _ _ d R c g L M h
  let N : Submodule R (R ⊗[k] V) := L.toSubmodule
  let P : Submodule R (R ⊗[k] V) := M.toSubmodule
  let f := g.toLinearMap.comp N.subtype
  have hP : P = f.range := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact h
  change (c.equiv.symm.toLinearMap.comp (exteriorPower.map (M := ↥P) d P.subtype)).range =
    ((c.equiv.symm.toLinearMap.comp (exteriorPower.map (M := ↥N) d N.subtype)).range).map
      (exteriorTransport c g)
  rw [hP, LinearMap.range_comp]
  have hf := wedgeRange_eq (R := ↥R) (M := ↥N) (N := ↥R ⊗[k] V) d f
  rw [← hf, ← LinearMap.range_comp, ← LinearMap.range_comp]
  congr 1
  simp only [f, exteriorPower.map_comp, exteriorTransport, LinearMap.comp_assoc,
    LinearEquiv.comp_symm_assoc]

end AffineExteriorLines

section GraphCharts

open Set.powersetCard

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype Index] [LinearOrder Index] (b : Basis Index k V) {d : ℕ}
  (I : Pivot Index d) (A : TestAlgebra k) (X : Matrix (Outside I) (Inside I) A)

private theorem graph_column_coordinate (j : Index) (i : Inside I) :
    (b.baseChange A).coord j (graphInclusion b I A X (Pi.single i 1)) =
      if hj : j ∈ I.val then (Pi.single i (1 : A) : Inside I → A) ⟨j, hj⟩ else X ⟨j, hj⟩ i := by
  have h (v : Index → A) :
      (b.baseChange A).coord j ((coordinates b A).symm v) = v j :=
    congrFun ((coordinates b A).apply_symm_apply v) j
  rw [graphInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe, h]
  by_cases hj : j ∈ I.val
  · simp [graphColumns, hj]
  · simp [graphColumns, hj, Matrix.toLin'_apply]

private theorem graphExteriorCoordinate_self :
    graphExteriorCoordinate b I I A X = 1 := by
  rw [graphExteriorCoordinate, graphExteriorVector, exteriorPower.basis_coord,
    exteriorPower.ιMultiDual_apply_ιMulti]
  conv_rhs => rw [← Matrix.det_one (n := Fin d) (R := ↥A)]
  congr 1
  ext i j
  let e := pivotEnumeration I
  change (b.baseChange A).coord (e j).val
    (graphInclusion b I A X (Pi.single (e i) 1)) = (1 : Matrix (Fin d) (Fin d) A) i j
  rw [graph_column_coordinate, dite_eq_left (e j).prop, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- Evaluating a wedge against an ordered list of coordinate forms takes its minor
with precisely that order on the rows. -/
private def orderedMinorForm {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (B : Basis Index R M) (rows : Fin d → Index) : Wedge R d M →ₗ[R] R :=
  exteriorPower.alternatingMapToDual R M d (fun i => B.coord (rows i))

private theorem orderedMinor_recover (row : Outside I) (col : Fin d) :
    orderedMinorForm (b.baseChange A)
      (Function.update (fun j => (pivotEnumeration I j).val) col row.val)
      (graphExteriorVector b I A X) = X row (pivotEnumeration I col) := by
  rw [orderedMinorForm, graphExteriorVector, exteriorPower.alternatingMapToDual_apply_ιMulti]
  let e := pivotEnumeration I
  let D : Matrix (Fin d) (Fin d) A := 1
  have hmat :
      Matrix.of (fun i j =>
        (b.baseChange A).coord (Function.update (fun j => (e j).val) col row.val j)
          (graphInclusion b I A X (Pi.single (e i) 1))) =
      D.updateCol col (fun i => X row (e i)) := by
    ext i j
    by_cases h : j = col
    · subst j
      rw [Matrix.of_apply, Function.update_self, graph_column_coordinate, dite_eq_right row.prop]
      simp
    · rw [Matrix.of_apply, Function.update_of_ne h, graph_column_coordinate, dite_eq_left (e j).prop,
        Matrix.updateCol_ne h]
      change (Pi.single (e i) (1 : A) : Inside I → A) (e j) = (1 : Matrix (Fin d) (Fin d) A) i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  rw [hmat, ← Matrix.cramer_apply]
  change Matrix.cramer (1 : Matrix (Fin d) (Fin d) A) (fun i => X row (e i)) col = _
  rw [Matrix.cramer_one]
  rfl

omit [Fintype Index] in
private theorem orderedMinor_basis_baseChange (rows : Fin d → Index) (J : Pivot Index d) :
    orderedMinorForm (b.baseChange A) rows ((b.baseChange A).exteriorPower d ⟨J.val, J.property⟩) =
      algebraMap k A (orderedMinorForm b rows (b.exteriorPower d ⟨J.val, J.property⟩)) := by
  simp only [orderedMinorForm, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapToDual_apply_ιMulti, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Function.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Basis.baseChange_apply, Basis.coord_apply, Basis.baseChange_repr_tmul, ← Basis.coord_apply,
    Algebra.smul_def, mul_one]

private theorem coordinateRatio_self (k Index : Type u) [Field k] (i : Index) :
    coordinateRatio k Index i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [coordinateRatio]
  erw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  simp

private theorem chartAlgebraSurjectivityProof (hpoly : PolynomialChartCoordinates.{u}) :
    ChartAlgebraSurjectivity.{u} := by
  classical
  intro k V Index _ _ _ _ _ b d I
  let Jset := Pivot Index d
  let P := Specs.GrassmannianCharts.chartAlgebra (k := k) I
  let R := CommAlgCat.of k P
  let A := universalGraph (k := k) I
  let ratio := coordinateRatio k Jset I
  let value := fun J => graphExteriorCoordinate b I J R A
  let _ : Finite Jset := inferInstanceAs (Finite { J : Finset Index // J.card = d })
  let _ : Fintype Jset := Fintype.ofFinite Jset
  obtain ⟨e, hc, hx⟩ := hpoly k Jset I
  let eA : MvPolynomial {J : Jset // J ≠ I} k ≃ₐ[k] chartRing k Jset I :=
    { e with
      commutes' := fun a => hc a }
  let f : chartRing k Jset I →ₐ[k] P :=
    (MvPolynomial.aeval (fun J : {J : Jset // J ≠ I} => value J.val)).comp eA.symm.toAlgHom
  have hf (J : Jset) : f (ratio J) = value J := by
    by_cases h : J = I
    · subst J
      simp only [ratio, coordinateRatio_self, map_one]
      exact (graphExteriorCoordinate_self b I R A).symm
    · have h' : eA (MvPolynomial.X ⟨J, h⟩) = ratio J := hx ⟨J, h⟩
      rw [← h']
      simp [f, value]
  refine ⟨f, ?_, hf⟩
  have hX (p : Outside I × Inside I) : MvPolynomial.X p ∈ f.range := by
    let col := (pivotEnumeration I).symm p.2
    let rows := Function.update (fun j => (pivotEnumeration I j).val) col p.1.val
    let form := orderedMinorForm (b.baseChange R) rows
    let form₀ := orderedMinorForm b rows
    let B := (b.baseChange R).exteriorPower d
    let B₀ := b.exteriorPower d
    let v := graphExteriorVector b I R A
    have hsum : (∑ J : Jset, value J • B ⟨J.val, J.prop⟩) = v := by
      let _ : Fintype (Set.powersetCard Index d) := (inferInstance : Fintype Jset)
      exact B.sum_repr v
    have hrecover : form v = MvPolynomial.X p := by
      have h := orderedMinor_recover b I R A p.1 col
      change form v = A p.1 (pivotEnumeration I col) at h
      simpa [col, A, universalGraph] using h
    refine ⟨∑ J : Jset, ratio J * algebraMap k (chartRing k Jset I)
      (form₀ (B₀ ⟨J.val, J.prop⟩)), ?_⟩
    rw [← hrecover, ← hsum]
    simp only [map_sum, map_mul, map_smul]
    apply Finset.sum_congr rfl
    intro J _
    change f (ratio J) * f (algebraMap k _ (form₀ (B₀ ⟨J.val, J.prop⟩))) =
      value J • form (B ⟨J.val, J.prop⟩)
    rw [hf, f.commutes, smul_eq_mul, orderedMinor_basis_baseChange b R rows J]
  have hall (p : P) : p ∈ f.range := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨algebraMap k _ a, f.commutes a⟩
    | add p q hp hq =>
      exact f.range.add_mem hp hq
    | mul_X p j hp =>
      exact f.range.mul_mem hp (hX j)
  exact fun p => hall p

end GraphCharts

section Morphism

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Fintype Index] [DecidableEq Index] (b : Basis Index k V) {d : ℕ}

private def pluckerFamilies (C : ChartSystem (k := k) (V := V) b d) (E : AffineExteriorLines k V d) :
    LineFamily k (Wedge k d V) C.scheme where
  line R p := E.line R (C.affinePoints.hom.app R p)
  compatible {R T} a p := by
    have hn := ConcreteCategory.congr_hom (C.affinePoints.hom.naturality a) p
    change C.affinePoints.hom.app T (mapPoints a p) =
      Module.Grassmannian.map a.hom (C.affinePoints.hom.app R p) at hn
    change (E.line T (C.affinePoints.hom.app T (mapPoints a p))).submodule = _
    rw [hn]
    exact E.baseChange a (C.affinePoints.hom.app _ p)

private def pluckerMorphism (C : ChartSystem (k := k) (V := V) b d)
    (F : SchemePoints (k := k) (V := V) d C.scheme C.affinePoints)
    (hF : ∀ (R : TestAlgebra k) (p : Points C.scheme R),
      IsTildePlane (k := k) (V := V) b R (C.affinePoints.hom.app R p) (F.subbundle _ (F.family _ p)))
    (ρ : LineRepresentation k (Wedge k d V))
    (hρ : BasisPointFormula k (Wedge k d V) ρ)
    (E : AffineExteriorLines k V d) : PluckerMorphism b d where
  charts := C
  families := F
  affineComparison := hF
  lines := ρ
  basisFormula := hρ
  exteriorLines := E
  morphism := (ρ.points C.scheme).symm (pluckerFamilies b C E)
  imageFormula S p R a := by
    rw [ρ.naturality, Equiv.apply_symm_apply, F.family_apply]
    exact E.image_eq _ _

private theorem pluckerMorphismGeometryProof
    (hplanes : Construction.{u}) (hplane : PlaneSplitAndRank.{u})
    (hpoints : Endpoints.{u}) (hlines : ProjectiveSpaceLineGeometry.{u})
    (hpoint : OneDimensionalProjectiveSpace.{u}) : PluckerMorphismGeometry.{u} := by
  intro k V Index _ _ _ _ _ _ b d hd
  obtain ⟨C, F, hF⟩ := hplanes k V Index b d hd
  obtain ⟨ρ, _, hρ, _⟩ := hlines k (Wedge k d V)
  refine ⟨pluckerMorphism b C F hF ρ hρ (affineExteriorLines hplane hd), ?_⟩
  rintro (rfl | rfl)
  · exact ⟨(hpoints k V Index b).1 C, (hpoint k (Wedge k 0 V) (by simp)).2⟩
  · exact ⟨(hpoints k V Index b).2 C, (hpoint k (Wedge k (Module.finrank k V) V) (by simp)).2⟩

end Morphism

section ChartRestrictions

open Set.powersetCard

private theorem extLineSubmodule {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
    {R : TestAlgebra k} {L M : AffineLine k W R} (h : L.submodule = M.submodule) : L = M := by
  cases L
  cases M
  cases h
  rfl

private theorem extLineFamily {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
    {S : SchemeOver k} {L M : LineFamily k W S} (h : L.line = M.line) : L = M := by
  cases L with
  | mk lineL hL =>
    cases M with
    | mk lineM hM =>
      dsimp at h
      subst lineM
      rfl

private theorem lineRepresentation_affine_ext
    {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρ : LineRepresentation k W) {R : TestAlgebra k}
    {f g : Points (projectiveSpace k W) R}
    (h : ((ρ.points _ f).line R (𝟙 _)).submodule = ((ρ.points _ g).line R (𝟙 _)).submodule) :
    f = g := by
  let L := ρ.points _ f
  let M := ρ.points _ g
  apply (ρ.points _).injective
  have hh : L.line = M.line := by
    funext T p
    obtain ⟨a, ha⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective p
    let α : R ⟶ T := a.unop
    apply extLineSubmodule
    have hL := L.compatible α (𝟙 _)
    have hM := M.compatible α (𝟙 _)
    have he : mapPoints α (𝟙 _) = p := by
      simpa [mapPoints, α] using ha
    rw [he] at hL hM
    rw [hL, hM, h]
  exact extLineFamily hh

private theorem topWedge_span {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {d : ℕ} (b : Basis (Fin d) R M) :
    Submodule.span R {exteriorPower.ιMulti R d b} = ⊤ := by
  let I : Set.powersetCard (Fin d) d := ⟨Finset.univ, by simp⟩
  have hI (J : Set.powersetCard (Fin d) d) : J = I := by
    apply Subtype.ext
    exact (Finset.card_eq_iff_eq_univ J.val).mp (by simp)
  have hJ : (id : Fin d → Fin d) = ⇑(ofFinEmbEquiv.symm I) := by
    rw [ofFinEmbEquiv_symm_apply]
    exact Finset.orderEmbOfFin_unique I.prop (by intro j; exact Finset.mem_univ j) strictMono_id
  have hb : Set.range (b.exteriorPower d) = {exteriorPower.ιMulti R d b} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨J, rfl⟩
      rw [hI J, exteriorPower.basis_apply, exteriorPower.ιMulti_family, ← hJ]
      rfl
    · intro hx
      refine ⟨I, ?_⟩
      rw [hx, exteriorPower.basis_apply, exteriorPower.ιMulti_family, ← hJ]
      rfl
  rw [← hb, Basis.span_eq]

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Fintype Index] [LinearOrder Index] (b : Basis Index k V) {d : ℕ}

omit [Module.Finite k V] in
private theorem graph_wedge_line (I : Pivot Index d) (R : TestAlgebra k)
    (X : Matrix (Outside I) (Inside I) R) (L : Plane k V d R)
    (hL : L.toSubmodule = (graphInclusion b I R X).range)
    (c : ExteriorComparison k R d V) :
    lineSubmodule c L = Submodule.span R {c.equiv.symm (graphExteriorVector b I R X)} := by
  let f := graphInclusion b I R X
  let B := (Pi.basisFun R (Inside I)).reindex (pivotEnumeration I).symm
  let N : Submodule R (R ⊗[k] V) := L.toSubmodule
  change N = f.range at hL
  change (c.equiv.symm.toLinearMap.comp (exteriorPower.map (M := ↥N) d N.subtype)).range = _
  rw [hL, LinearMap.range_comp, ← wedgeRange_eq d f]
  have he : (exteriorPower.map d f).range =
      Submodule.span R {graphExteriorVector b I R X} := by
    rw [LinearMap.range_eq_map, ← topWedge_span B, Submodule.map_span, Set.image_singleton]
    congr 2
    rw [exteriorPower.map_apply_ιMulti, graphExteriorVector]
    congr 1
    funext i
    simp only [Function.comp_apply, f, B, Basis.reindex_apply, Equiv.symm_symm, Pi.basisFun_apply]
  rw [he, Submodule.map_span, Set.image_singleton]
  rfl

omit [Module.Finite k V] [Fintype Index] in
private theorem wedgeComparison_basis (R : TestAlgebra k) (c : ExteriorComparison k R d V)
    (J : Set.powersetCard Index d) :
    c.equiv (((b.exteriorPower d).baseChange R) J) = ((b.baseChange R).exteriorPower d) J := by
  rw [Basis.baseChange_apply, exteriorPower.basis_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMulti_family, c.pure]
  congr 1
  funext j
  exact (Basis.baseChange_apply R b _).symm

omit [Module.Finite k V] in
private theorem graph_wedge_coordinates (I : Pivot Index d) (R : TestAlgebra k)
    (X : Matrix (Outside I) (Inside I) R) (c : ExteriorComparison k R d V) :
    c.equiv.symm (graphExteriorVector b I R X) =
      ((b.exteriorPower d).baseChange R).equivFun.symm
        (fun J => graphExteriorCoordinate b I ⟨J.val, J.prop⟩ R X) := by
  classical
  let _ : Fintype (Set.powersetCard Index d) := Fintype.ofFinite _
  let B := ((b.exteriorPower d).baseChange R)
  let D := (b.baseChange R).exteriorPower d
  have hB : B.map c.equiv = D :=
    DFunLike.ext _ _ fun J => by simpa only [Basis.map_apply] using wedgeComparison_basis b R c J
  apply B.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext J
  change B.repr (c.equiv.symm (graphExteriorVector b I R X)) J =
    D.repr (graphExteriorVector b I R X) J
  rw [← hB]
  rfl

private theorem pluckerChartRestrictionsProof (hpoly : PolynomialChartCoordinates.{u}) :
    PluckerChartRestrictions.{u} := by
  intro k V Index _ _ _ _ _ _ b d P
  let _ : Finite (Pivot Index d) := inferInstanceAs (Finite {I : Finset Index // I.card = d})
  let reindex : Set.powersetCard Index d ≃ Pivot Index d :=
    { toFun := fun J => ⟨J.val, J.prop⟩
      invFun := fun J => ⟨J.val, J.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let B : Basis (Pivot Index d) k (Wedge k d V) := (b.exteriorPower d).reindex reindex
  obtain ⟨e, he⟩ := P.basisFormula (Pivot Index d) B
  refine ⟨e, fun I => ?_⟩
  obtain ⟨f, hf, hr⟩ := chartAlgebraSurjectivityProof hpoly k V Index b I
  refine ⟨f, hf, hr, ?_⟩
  let R := CommAlgCat.of k (Specs.GrassmannianCharts.chartAlgebra (k := k) I)
  let A := universalGraph (k := k) I
  let c := P.exteriorLines.compare R
  let q : Points P.charts.scheme R := P.charts.chart I
  have hL : (P.charts.affinePoints.hom.app R q).toSubmodule = (graphInclusion b I R A).range := by
    have hm : matrixOfPoint I R (𝟙 _) = A := by
      unfold matrixOfPoint A universalGraph
      rw [Functor.FullyFaithful.preimage_id]
      rfl
    have h := P.charts.coordinates_eq I R (𝟙 _)
    rw [hm] at h
    change (P.charts.affinePoints.hom.app R
      (𝟙 ((testSpec k).obj (op R)) ≫ P.charts.chart I)).toSubmodule = _ at h
    have hi : (𝟙 ((testSpec k).obj (op R)) ≫ P.charts.chart I) = q := Category.id_comp _
    exact (congrArg (fun p : Points P.charts.scheme R =>
      (P.charts.affinePoints.hom.app R p).toSubmodule) hi).symm.trans h
  apply lineRepresentation_affine_ext P.lines (R := R)
  rw [he I R f]
  rw [P.imageFormula, P.families.family_apply]
  have hq : (𝟙 ((testSpec k).obj (op R)) ≫ P.charts.chart I) = q := Category.id_comp _
  change _ = lineSubmodule c (P.charts.affinePoints.hom.app R
    (𝟙 ((testSpec k).obj (op R)) ≫ P.charts.chart I))
  rw [hq, graph_wedge_line b I R A _ hL]
  apply congrArg (fun x => Submodule.span R {x})
  apply ((B.baseChange R).equivFun).injective
  rw [LinearEquiv.apply_symm_apply]
  funext J
  rw [hr]
  change graphExteriorCoordinate b I J R A =
    (B.baseChange R).repr (c.equiv.symm (graphExteriorVector b I R A)) J
  have hb : B.baseChange R = ((b.exteriorPower d).baseChange R).reindex reindex := by
    apply DFunLike.ext
    intro J
    simp only [Basis.baseChange_apply, Basis.reindex_apply, B]
  rw [hb, Basis.repr_reindex_apply, graph_wedge_coordinates b I R A c]
  exact congrFun (((b.exteriorPower d).baseChange R).equivFun.apply_symm_apply _) (reindex.symm J) |>.symm

end ChartRestrictions

section PivotCriterion

open Set.powersetCard

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype Index] [LinearOrder Index]
  (b : Basis Index k V) {d : ℕ} (I J : Pivot Index d) (R : TestAlgebra k)
  (A : Matrix (Outside I) (Inside I) R)

private theorem pivotProjection_graph (x : Inside I → R) (j : Inside J) :
    pivotProjection b J R (graphInclusion b I R A x) j = graphColumns I R A x j.val := by
  simp only [pivotProjection, graphInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.funLeft_apply]

private theorem graphInclusion_injective :
    Function.Injective (graphInclusion b I R A) := by
  have h : Function.LeftInverse (pivotProjection b I R) (graphInclusion b I R A) := by
    intro v
    funext i
    rw [pivotProjection_graph]
    simp [graphColumns, i.prop]
  exact h.injective

private theorem pivot_of_graphExteriorCoordinate_unit (P : Plane k V d R)
    (hP : P.toSubmodule = (graphInclusion b I R A).range)
    (hu : IsUnit (graphExteriorCoordinate b I J R A)) : IsPivot b J R P := by
  let eI := LinearEquiv.funCongrLeft R R (pivotEnumeration I).symm
  let eJ := LinearEquiv.funCongrLeft R R (pivotEnumeration J)
  let f := graphInclusion b I R A
  let p := (pivotProjection b J R).comp f
  let w := eJ.toLinearMap.comp (p.comp eI.toLinearMap)
  let M := LinearMap.toMatrix' w
  have hm : graphExteriorCoordinate b I J R A = M.det := by
    rw [graphExteriorCoordinate, graphExteriorVector, exteriorPower.basis_coord,
      exteriorPower.ιMultiDual_apply_ιMulti, ← Matrix.det_transpose M]
    congr 1
    ext i j
    have hsingle : eI (Pi.single i 1) = (Pi.single (pivotEnumeration I i) 1 : Inside I → R) := by
      funext s
      change (Pi.single i (1 : R) : Fin d → R) ((pivotEnumeration I).symm s) =
        (Pi.single (pivotEnumeration I i) (1 : R) : Inside I → R) s
      by_cases hs : s = pivotEnumeration I i
      · subst s
        simp
      · have hh : (pivotEnumeration I).symm s ≠ i := by
          intro hi
          exact hs (by rw [← hi, Equiv.apply_symm_apply])
        simp [Pi.single_eq_of_ne hs, Pi.single_eq_of_ne hh]
    change _ = (LinearMap.toMatrix' w) j i
    rw [LinearMap.toMatrix'_apply]
    change _ = p (eI (Pi.single i 1)) (pivotEnumeration J j)
    rw [hsingle]
    change (coordinates b R (f (Pi.single (pivotEnumeration I i) 1))) (pivotEnumeration J j).val =
      (pivotProjection b J R (f (Pi.single (pivotEnumeration I i) 1))) (pivotEnumeration J j)
    rfl
  let m := Matrix.GeneralLinearGroup.mk'' M (hm ▸ hu)
  have hw : Function.Bijective w := by
    have h := (Matrix.GeneralLinearGroup.toLin m).toLinearEquiv.bijective
    change Function.Bijective (Matrix.toLin' M) at h
    simpa only [M, Matrix.toLin'_toMatrix'] using h
  have hp : Function.Bijective p := by
    have h := eJ.symm.bijective.comp (hw.comp eI.symm.bijective)
    convert h using 1
    funext x
    change p x = eJ.symm (eJ (p (eI (eI.symm x))))
    simp
  let Q : Submodule R (R ⊗[k] V) := P.toSubmodule
  change Function.Bijective ((pivotProjection b J R).comp Q.subtype)
  change Q = f.range at hP
  rw [hP]
  let i := LinearEquiv.ofInjective f (graphInclusion_injective b I R A)
  apply (Function.Bijective.of_comp_iff _ i.bijective).mp
  exact hp

private theorem graphExteriorCoordinate_map {T : TestAlgebra k} (a : R ⟶ T) :
    a.hom (graphExteriorCoordinate b I J R A) =
      graphExteriorCoordinate b I J T (A.map a.hom) := by
  rw [graphExteriorCoordinate, graphExteriorCoordinate, graphExteriorVector, graphExteriorVector,
    exteriorPower.basis_coord, exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti, AlgHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  let row := (pivotEnumeration J j).val
  change a.hom ((b.baseChange R).coord row
    (graphInclusion b I R A (Pi.single (pivotEnumeration I i) 1))) =
    (b.baseChange T).coord row (graphInclusion b I T (A.map a.hom) (Pi.single (pivotEnumeration I i) 1))
  rw [graph_column_coordinate, graph_column_coordinate]
  by_cases h : row ∈ I.val
  · rw [dite_eq_left h, dite_eq_left h]
    by_cases he : (⟨row, h⟩ : Inside I) = pivotEnumeration I i
    · simp [he]
    · simp [Pi.single_eq_of_ne he]
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

end PivotCriterion

section ClosedImmersion

private theorem projectiveChart_preimage (k Index : Type u) [Field k] (i j : Index) :
    (chartMorphism (k := k) i).left ⁻¹ᵁ coordinateOpen k Index j =
      PrimeSpectrum.basicOpen (coordinateRatio k Index i j) := by
  change chartInclusion k Index i ⁻¹ᵁ coordinateOpen k Index j = _
  rw [Proj.awayι_preimage_basicOpen _ (coordinate_mem_degree_one k Index i) Nat.one_pos
    (coordinate_mem_degree_one k Index j) Nat.one_pos]
  congr 1
  unfold HomogeneousLocalization.Away.isLocalizationElem coordinateRatio
  simp only [pow_one]

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Fintype Index] [LinearOrder Index] (b : Basis Index k V) {d : ℕ} (P : PluckerMorphism b d)

private theorem affine_chart_pivot_at_prime (I J : Pivot Index d)
    (y : (Specs.GrassmannianCharts.chartScheme (k := k) J).left)
    (h : graphExteriorCoordinate b J I (CommAlgCat.of k _)
      (universalGraph (k := k) J) ∉ y.asIdeal) :
    (P.charts.chart J).left y ∈ Set.range (P.charts.chart I).left := by
  let B := Specs.GrassmannianCharts.chartAlgebra (k := k) J
  let S := CommAlgCat.of k B
  let y₀ : PrimeSpectrum B := y
  let _ : y₀.asIdeal.IsPrime := y₀.isPrime
  let K := y₀.asIdeal.ResidueField
  let _ : Algebra k K := ((algebraMap B K).comp (algebraMap k B)).toAlgebra
  let T := CommAlgCat.of k K
  let a : S ⟶ T := CommAlgCat.ofHom
    { toRingHom := algebraMap B K
      commutes' := fun _ => rfl }
  let p : Points (Specs.GrassmannianCharts.chartScheme (k := k) J) T := (testSpec k).map a.op
  let η : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  have hη : p.left η = y := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap B K) ⊥ = y.asIdeal
    exact Ideal.ker_algebraMap_residueField y₀.asIdeal
  let A := universalGraph (k := k) J
  have hunit : IsUnit (graphExteriorCoordinate b J I T (A.map a.hom)) := by
    rw [← graphExteriorCoordinate_map b J I S A a]
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply h
    change (algebraMap B K) (graphExteriorCoordinate b J I S A) = 0 at hz
    have hk : graphExteriorCoordinate b J I S A ∈ RingHom.ker (algebraMap B K) := hz
    rwa [Ideal.ker_algebraMap_residueField y₀.asIdeal] at hk
  have hm : matrixOfPoint J T p = A.map a.hom := by
    unfold matrixOfPoint p
    rw [Functor.FullyFaithful.preimage_map]
    rfl
  have hL := P.charts.coordinates_eq J T p
  rw [hm] at hL
  have hP := pivot_of_graphExteriorCoordinate_unit b J I T (A.map a.hom)
    _ hL hunit
  obtain ⟨q, hq⟩ := (P.charts.factor_iff I T (p ≫ P.charts.chart J)).mpr hP
  refine ⟨q.left η, ?_⟩
  have hq' := congrArg (fun f : Points P.charts.scheme T => f.left η) hq
  change (P.charts.chart I).left (q.left η) = (P.charts.chart J).left (p.left η) at hq'
  rwa [hη] at hq'

private theorem pluckerClosedImmersionProof
    (hpoly : PolynomialChartCoordinates.{u}) (hcover : CoordinateOpenCover.{u})
    (hcharts : CoordinateAffineCharts.{u}) : PluckerClosedImmersion.{u} := by
  classical
  intro k V Index _ _ _ _ _ _ b d P
  obtain ⟨e, hf⟩ := pluckerChartRestrictionsProof hpoly k V Index b d P
  choose f hsurj hratio hcomm using hf
  let m := P.morphism ≫ e.inv
  let i (I : Pivot Index d) := (chartMorphism (k := k) I).left
  let g (I : Pivot Index d) := ((testSpec k).map (CommAlgCat.ofHom (f I)).op).left
  let _ (I : Pivot Index d) : IsOpenImmersion (i I) := (hcharts k _ I).1
  let _ (I : Pivot Index d) : IsOpenImmersion (P.charts.chart I).left := P.charts.openChart I
  have hfac (I : Pivot Index d) :
      (P.charts.chart I).left ≫ m.left = g I ≫ i I := by
    have h := congrArg (· ≫ e.inv) (hcomm I)
    have h' : (testSpec k).map (CommAlgCat.ofHom (f I)).op ≫ chartMorphism I =
        P.charts.chart I ≫ m := by simpa [m] using h
    exact congrArg (fun a => a.left) h'.symm
  have hopen (I : Pivot Index d) : (i I).opensRange = coordinateOpen k (Pivot Index d) I := by
    apply SetLike.coe_injective
    exact (hcharts k _ I).2
  have hpreimage (I : Pivot Index d) :
      m.left ⁻¹ᵁ (i I).opensRange = (P.charts.chart I).left.opensRange := by
    apply SetLike.ext
    intro x
    rw [hopen I]
    change m.left x ∈ coordinateOpen k (Pivot Index d) I ↔ x ∈ Set.range (P.charts.chart I).left
    constructor
    · intro hx
      obtain ⟨J, y, hy⟩ := P.charts.cover x
      have hh := congrArg (fun p => p y) (hfac J)
      change m.left ((P.charts.chart J).left y) = i J (g J y) at hh
      have hx' : i J (g J y) ∈ coordinateOpen k (Pivot Index d) I := by rwa [← hh, hy]
      have hy' : g J y ∈ (i J) ⁻¹ᵁ (coordinateOpen k (Pivot Index d) I) := hx'
      rw [projectiveChart_preimage k (Pivot Index d) J I] at hy'
      have hy'' : f J (coordinateRatio k (Pivot Index d) J I) ∉ y.asIdeal := by
        change coordinateRatio k (Pivot Index d) J I ∉
          ((Spec.map (CommRingCat.ofHom (f J).toRingHom)) y).asIdeal at hy'
        exact hy'
      rw [hratio J I] at hy''
      rw [← hy]
      exact affine_chart_pivot_at_prime b P I J y hy''
    · rintro ⟨y, rfl⟩
      have hh := congrArg (fun p => p y) (hfac I)
      change m.left ((P.charts.chart I).left y) = i I (g I y) at hh
      rw [hh, ← hopen I]
      exact ⟨g I y, rfl⟩
  have hm : IsClosedImmersion m.left := by
    apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
      (fun I => (i I).opensRange)
    · simpa only [hopen] using hcover k (Pivot Index d)
    · intro I
      have hpb := IsOpenImmersion.isPullback (g I) (P.charts.chart I).left (i I)
        m.left (hfac I) (hpreimage I)
      have hg : IsClosedImmersion (g I) :=
        IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (f I).toRingHom) (hsurj I)
      have hloc : IsClosedImmersion (pullback.snd m.left (i I)) := by
        rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hpb.flip.isoPullback.hom]
        rwa [hpb.flip.isoPullback_hom_snd]
      exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
        (morphismRestrictOpensRange m.left (i I))).mpr hloc
  let _ := hm
  have he : m.left ≫ e.hom.left = P.morphism.left := by
    exact congrArg (fun a => a.left) (show m ≫ e.hom = P.morphism by simp [m])
  rw [← he]
  infer_instance

end ClosedImmersion

section LinearTransport

private def transportPlane {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {d : ℕ} {R : TestAlgebra k} (g : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V))
    (L : Plane k V d R) : Plane k V d R := by
  let P := L.toSubmodule
  let Q := P.map g.toLinearMap
  let e := Submodule.Quotient.equiv P Q g rfl
  refine ⟨Q, Module.Finite.of_surjective e.toLinearMap e.surjective,
    Module.Projective.of_equiv' e, ?_⟩
  intro p
  rw [← Module.rankAtStalk_eq_of_equiv e, L.rankAtStalk_eq]

private def transportLine {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
    {R : TestAlgebra k} (g : (R ⊗[k] W) ≃ₗ[R] (R ⊗[k] W))
    (L : AffineLine k W R) : AffineLine k W R := by
  let P := L.submodule
  let Q := P.map g.toLinearMap
  let _ := L.finite
  let _ := L.projective
  let e := g.submoduleMap P
  let C := L.split.choose
  refine ⟨Q, ⟨C.map g.toLinearMap, Submodule.isCompl_map g L.split.choose_spec⟩,
    Module.Finite.of_surjective e.toLinearMap e.surjective, Module.Projective.of_equiv' e, ?_⟩
  intro p
  have h := congrFun (Module.rankAtStalk_eq_of_equiv (M := ↥P) (N := ↥Q) e) p
  exact h.symm.trans (L.rank_one p)

private def wedgeEquiv {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (d : ℕ) (g : M ≃ₗ[R] M) : Wedge R d M ≃ₗ[R] Wedge R d M :=
  LinearEquiv.ofLinearMap (exteriorPower.map d g.toLinearMap)
    (exteriorPower.map d g.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, LinearEquiv.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, LinearEquiv.symm_comp, exteriorPower.map_id])

private def extendedWedgeEquiv {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {d : ℕ} {R : TestAlgebra k} (c : ExteriorComparison k R d V)
    (g : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V)) :
    (R ⊗[k] Wedge k d V) ≃ₗ[R] (R ⊗[k] Wedge k d V) :=
  c.equiv ≪≫ₗ wedgeEquiv d g ≪≫ₗ c.equiv.symm

private theorem changePlaneSubmodule {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {d : ℕ} {R T : TestAlgebra k} (a : R ⟶ T) (L : Plane k V d R) :
    (Module.Grassmannian.map a.hom L).toSubmodule = changeLineSubmodule k V a L.toSubmodule := by
  let _ : Algebra R T := a.hom.toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  rw [mapPlane_range a L, LinearMap.range_comp]
  rfl

private theorem changeSubmodule_map {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
    {R T : TestAlgebra k} (a : R ⟶ T)
    (gR : (R ⊗[k] W) →ₗ[R] (R ⊗[k] W)) (gT : (T ⊗[k] W) →ₗ[T] (T ⊗[k] W))
    (hg :
      letI : Algebra R T := a.hom.toAlgebra
      letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
      let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T W
      gT.comp c.toLinearMap = c.toLinearMap.comp (gR.baseChange (↥T)))
    (P : Submodule R (R ⊗[k] W)) :
    changeLineSubmodule k W a (P.map gR) = (changeLineSubmodule k W a P).map gT := by
  let _ : Algebra R T := a.hom.toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let c := (TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T W).toLinearMap
  change ((P.map gR).baseChange (↥T)).map c = ((P.baseChange (↥T)).map c).map gT
  change gT.comp c = c.comp (gR.baseChange (↥T)) at hg
  rw [baseChange_map_submodule, ← Submodule.map_comp, ← hg, Submodule.map_comp]

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype Index] [DecidableEq Index] (b : Basis Index k V)

private theorem matrixTransport_apply_basis (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup Index R)
    (j : Index) :
    matrixTransport b R g (b.baseChange R j) = ∑ i, g.val i j • b.baseChange R i := by
  rw [matrixTransport, Matrix.GeneralLinearGroup.toLin'_apply, Basis.repr_self]
  have h : ((Finsupp.single j 1 : Index →₀ R) : Index → R) = Pi.single j 1 := by
    funext i
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [h, Matrix.mulVec_single_one]
  simp [Fintype.linearCombination_apply]

private theorem matrixTransport_natural {R T : TestAlgebra k} (a : R ⟶ T)
    (g : Matrix.GeneralLinearGroup Index R) :
    letI : Algebra R T := a.hom.toAlgebra
    letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T V
    (matrixTransport b T (Matrix.GeneralLinearGroup.map a.hom.toRingHom g)).toLinearMap.comp c.toLinearMap =
      c.toLinearMap.comp ((matrixTransport b R g).toLinearMap.baseChange (↥T)) := by
  let _ : Algebra R T := a.hom.toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T V
  apply ((b.baseChange R).baseChange T).ext
  intro j
  have hc (t : T) (i : Index) : c (t ⊗ₜ[R] (b.baseChange R i)) = t • (b.baseChange T i) := by
    rw [Basis.baseChange_apply, Basis.baseChange_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  rw [Basis.baseChange_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, matrixTransport_apply_basis, TensorProduct.tmul_sum, map_sum]
  change matrixTransport b T (Matrix.GeneralLinearGroup.map a.hom.toRingHom g)
    (c ((1 : T) ⊗ₜ[R] (b.baseChange R j))) =
    ∑ x, c ((1 : T) ⊗ₜ[R] (g.val x j • (b.baseChange R x)))
  rw [hc, one_smul, matrixTransport_apply_basis]
  apply Finset.sum_congr rfl
  intro i _
  change a.hom (g.val i j) • b.baseChange T i =
    c ((1 : T) ⊗ₜ[R] (g.val i j • b.baseChange R i))
  rw [TensorProduct.tmul_smul]
  change a.hom (g.val i j) • b.baseChange T i =
    c (((algebraMap (↥R) (↥T)) (g.val i j) * 1) ⊗ₜ[↥R] (b.baseChange R i))
  rw [mul_one]
  exact (hc (a.hom (g.val i j)) i).symm

private theorem exteriorComparison_unique {k R M : Type u} [CommRing k] [CommRing R] [Algebra k R]
    [AddCommGroup M] [Module k M] (d : ℕ) (c c' : ExteriorComparison k R d M) : c = c' := by
  cases c with
  | mk e he =>
    cases c' with
    | mk e' he' =>
      have h : e.toLinearMap = e'.toLinearMap := tensorWedge_ext fun v => (he v).trans (he' v).symm
      have h' := LinearEquiv.toLinearMap_injective h
      subst e'
      rfl

set_option maxHeartbeats 600000 in
private theorem exteriorTransport_natural_aux {k R T V : Type u} [Field k]
    [CommRing R] [CommRing T] [Algebra k R] [Algebra k T] [Algebra R T] [IsScalarTower k R T]
    [AddCommGroup V] [Module k V] (d : ℕ)
    (gR : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V)) (gT : (T ⊗[k] V) ≃ₗ[T] (T ⊗[k] V))
    (hg :
      let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T V
      gT.toLinearMap.comp c.toLinearMap = c.toLinearMap.comp (gR.toLinearMap.baseChange T)) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T (Wedge k d V)
    (exteriorTransport (R := CommAlgCat.of k T) (exteriorComparison k T d V) gT).comp
        c.toLinearMap =
      c.toLinearMap.comp ((exteriorTransport (R := CommAlgCat.of k R)
        (exteriorComparison k R d V) gR).baseChange T) := by
  let cV := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T V
  let cW := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T (Wedge k d V)
  let cR := (exteriorComparison k R d V).equiv
  let cT := (exteriorComparison k T d V).equiv
  let cRT := (exteriorComparison R T d (R ⊗[k] V)).equiv
  let eR := exteriorPower.map d gR.toLinearMap
  let eT := exteriorPower.map d gT.toLinearMap
  let eRT := exteriorPower.map d (gR.toLinearMap.baseChange T)
  let wV := exteriorPower.map d cV.toLinearMap
  let nR := exteriorTransport (R := CommAlgCat.of k R) (exteriorComparison k R d V) gR
  let nT := exteriorTransport (R := CommAlgCat.of k T) (exteriorComparison k T d V) gT
  have h₁ (x) : cT (cW x) = wV (cRT ((cR.toLinearMap.baseChange T) x)) :=
    LinearMap.congr_fun (exteriorComparison_tower k R T V d) x
  have h₂ (x) : eT (wV x) = wV (eRT x) := by
    have h := congrArg (exteriorPower.map d) hg
    rw [exteriorPower.map_comp, exteriorPower.map_comp] at h
    exact LinearMap.congr_fun h x
  have h₃ (x) : eRT (cRT x) = cRT ((eR.baseChange T) x) :=
    LinearMap.congr_fun (exteriorComparison_naturality R T d (R ⊗[k] V) gR.toLinearMap).symm x
  have h₄ (x) : (eR.baseChange T) ((cR.toLinearMap.baseChange T) x) =
      (cR.toLinearMap.baseChange T) ((nR.baseChange T) x) := by
    have h : eR.comp cR.toLinearMap = cR.toLinearMap.comp nR := by
      change _ = cR.toLinearMap.comp (cR.symm.toLinearMap.comp _)
      rw [LinearEquiv.comp_symm_assoc]
    have h' := congrArg (LinearMap.baseChange T) h
    simp only [LinearMap.baseChange_comp] at h'
    exact LinearMap.congr_fun h' x
  apply LinearMap.ext
  intro x
  apply cT.injective
  change cT (nT (cW x)) = cT (cW ((nR.baseChange T) x))
  calc
    cT (nT (cW x)) = eT (cT (cW x)) := cT.apply_symm_apply _
    _ = eT (wV (cRT ((cR.toLinearMap.baseChange T) x))) := congrArg eT (h₁ x)
    _ = wV (eRT (cRT ((cR.toLinearMap.baseChange T) x))) := h₂ _
    _ = wV (cRT ((eR.baseChange T) ((cR.toLinearMap.baseChange T) x))) := congrArg wV (h₃ _)
    _ = wV (cRT ((cR.toLinearMap.baseChange T) ((nR.baseChange T) x))) := by rw [h₄]
    _ = cT (cW ((nR.baseChange T) x)) := (h₁ _).symm

private theorem matrixExteriorTransport_natural {d : ℕ} {R T : TestAlgebra k}
    (a : R ⟶ T) (g : Matrix.GeneralLinearGroup Index R)
    (cR : ExteriorComparison k R d V) (cT : ExteriorComparison k T d V) :
    letI : Algebra R T := a.hom.toAlgebra
    letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T (Wedge k d V)
    (exteriorTransport cT (matrixTransport b T (Matrix.GeneralLinearGroup.map a.hom.toRingHom g))).comp
        c.toLinearMap =
      c.toLinearMap.comp ((exteriorTransport cR (matrixTransport b R g)).baseChange (↥T)) := by
  rw [exteriorComparison_unique d cR (exteriorComparison k R d V),
    exteriorComparison_unique d cT (exteriorComparison k T d V)]
  let _ : Algebra R T := a.hom.toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  exact exteriorTransport_natural_aux d (matrixTransport b R g)
    (matrixTransport b T (Matrix.GeneralLinearGroup.map a.hom.toRingHom g))
    (matrixTransport_natural b a g)

end LinearTransport

section SchemeActions

open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k]

private theorem hom_ext_of_affine_points {X Y : SchemeOver k} {f g : X ⟶ Y}
    (h : ∀ (R : TestAlgebra k) (p : Points X R), p ≫ f = p ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  let U := X.left.affineOpenCover
  apply U.openCover.hom_ext
  intro i
  let Z : SchemeOver k := Over.mk (U.f i ≫ X.hom)
  let p : Z ⟶ X := Over.homMk (U.f i) rfl
  obtain ⟨R, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr (show IsAffine Z.left from isAffine_Spec _)
  have he : p ≫ f = p ≫ g := by
    simpa using congrArg (e.inv ≫ ·) (h R.unop (e.hom ≫ p))
  exact congrArg (fun q => q.left) he

private def schemeActionOfSubmodules {G : Specs.GroupScheme k} {X : SchemeOver k}
    {W : Type u} [AddCommGroup W] [Module k W]
    (s : ∀ R : TestAlgebra k, Points X R → Submodule R (R ⊗[k] W))
    (hinj : ∀ R, Function.Injective (s R))
    (r : ∀ R : TestAlgebra k, Points G.X R →* Module.End R (R ⊗[k] W))
    (act : G.X ⊗ X ⟶ X)
    (hact : ∀ (R : TestAlgebra k) (g : Points G.X R) (p : Points X R),
      s R (lift g p ≫ act) = (s R p).map (r R g)) : SchemeAction G X where
  act := act
  unit := by
    apply hom_ext_of_affine_points
    intro R p
    apply hinj R
    simp only [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id]
    change s R (lift (1 : Points G.X R) p ≫ act) = s R p
    simp only [hact, map_one, Module.End.one_eq_id, Submodule.map_id]
  assoc := by
    apply hom_ext_of_affine_points
    intro R p
    let g := p ≫ fst G.X (G.X ⊗ X)
    let h := p ≫ snd G.X (G.X ⊗ X) ≫ fst G.X X
    let x := p ≫ snd G.X (G.X ⊗ X) ≫ snd G.X X
    have hmul : p ≫ lift
        (lift (fst G.X (G.X ⊗ X)) (snd G.X (G.X ⊗ X) ≫ fst G.X X) ≫ μ[G.X])
        (snd G.X (G.X ⊗ X) ≫ snd G.X X) ≫ act = lift (g * h) x ≫ act := by
      simp [g, h, x, Hom.mul_def, comp_lift_assoc]
    have hiter : p ≫ lift (fst G.X (G.X ⊗ X)) (snd G.X (G.X ⊗ X) ≫ act) ≫ act =
        lift g (lift h x ≫ act) ≫ act := by
      have hp : p ≫ snd G.X (G.X ⊗ X) = lift h x := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [h, x]
      rw [comp_lift_assoc]
      simp only [g, ← Category.assoc (f := p) (g := snd G.X (G.X ⊗ X)), hp]
    rw [hmul, hiter]
    apply hinj R
    simp only [hact, map_mul, Module.End.mul_eq_comp, Submodule.map_comp]

variable {V Index : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Fintype Index] [DecidableEq Index] (b : Basis Index k V) {d : ℕ}
  {G : Specs.GroupScheme k}
  (c : (groupPointsFunctor k).obj G ≅ Specs.StandardGroups.generalLinearPoints k Index)

private theorem matrixPoint_natural {R T : TestAlgebra k} (a : R ⟶ T) (g : Points G.X R) :
    c.hom.app T (mapPoints a g) = Matrix.GeneralLinearGroup.map a.hom.toRingHom (c.hom.app R g) := by
  exact ConcreteCategory.congr_hom (c.hom.naturality a) g

omit [Module.Finite k V] in
private theorem transportPlane_natural {R T : TestAlgebra k} (a : R ⟶ T)
    (g : Matrix.GeneralLinearGroup Index R) (L : Plane k V d R) :
    transportPlane (matrixTransport b T (Matrix.GeneralLinearGroup.map a.hom.toRingHom g))
        (Module.Grassmannian.map a.hom L) =
      Module.Grassmannian.map a.hom (transportPlane (matrixTransport b R g) L) := by
  apply Module.Grassmannian.ext
  rw [changePlaneSubmodule a (transportPlane (matrixTransport b R g) L)]
  change (Module.Grassmannian.map a.hom L).toSubmodule.map _ =
    changeLineSubmodule k V a (L.toSubmodule.map _)
  rw [changePlaneSubmodule a L]
  exact (changeSubmodule_map a _ _ (matrixTransport_natural b a g) L.toSubmodule).symm

private def planeActionFamily (C : ChartSystem (k := k) (V := V) b d) :
    Family k V d (G.X ⊗ C.scheme) where
  app R := TypeCat.ofHom fun q =>
    transportPlane (matrixTransport b R (c.hom.app R (q ≫ fst G.X C.scheme)))
      (C.affinePoints.hom.app R (q ≫ snd G.X C.scheme))
  naturality {R T} a := by
    refine ConcreteCategory.hom_ext (C := Type u) _ _ (fun (q : Points (G.X ⊗ C.scheme) R) => ?_)
    let p : Points C.scheme R := q ≫ snd G.X C.scheme
    have h := ConcreteCategory.congr_hom (C.affinePoints.hom.naturality a) p
    change C.affinePoints.hom.app T (mapPoints a p) =
      Module.Grassmannian.map a.hom (C.affinePoints.hom.app R p) at h
    change transportPlane
        (matrixTransport b T (c.hom.app T (mapPoints a q ≫ fst G.X C.scheme)))
        (C.affinePoints.hom.app T (mapPoints a q ≫ snd G.X C.scheme)) = _
    rw [show mapPoints a q ≫ fst G.X C.scheme = mapPoints a (q ≫ fst G.X C.scheme) from
        Category.assoc _ _ _,
      show mapPoints a q ≫ snd G.X C.scheme = mapPoints a p from
        Category.assoc _ _ _,
      matrixPoint_natural c, h]
    exact transportPlane_natural b a _ _

private def matrixPointEquivHom (R : TestAlgebra k) :
    Points G.X R →* ((R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V)) :=
  ((Matrix.GeneralLinearGroup.toLin' (b.baseChange R)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (R ⊗[k] V))).toMonoidHom.comp
    (c.hom.app R).hom

private def matrixPointEndHom (R : TestAlgebra k) :
    Points G.X R →* Module.End R (R ⊗[k] V) :=
  (Units.coeHom _).comp ((Matrix.GeneralLinearGroup.toLin' (b.baseChange R)).toMonoidHom.comp
    (c.hom.app R).hom)

private def grassmannianAction (P : PluckerMorphism b d) :
    { α : SchemeAction G P.charts.scheme //
      ∀ (R : TestAlgebra k) (g : Points G.X R) (p : Points P.charts.scheme R),
        (P.charts.affinePoints.hom.app R (lift g p ≫ α.act)).toSubmodule =
          (P.charts.affinePoints.hom.app R p).toSubmodule.map
            (matrixTransport b R (c.hom.app R g)).toLinearMap } := by
  let C := P.charts
  let s (R : TestAlgebra k) (p : Points C.scheme R) :=
    (C.affinePoints.hom.app R p).toSubmodule
  let A := planeActionFamily b c C
  let act := (P.families.family _).symm A
  have hact (R : TestAlgebra k) (g : Points G.X R) (p : Points C.scheme R) :
      s R (lift g p ≫ act) = (s R p).map (matrixPointEndHom b c R g) := by
    have h := P.families.family_apply _ act R (lift g p)
    rw [show P.families.family _ act = A from Equiv.apply_symm_apply _ _,
      show A = planeActionFamily b c C from rfl] at h
    change transportPlane (matrixTransport b R (c.hom.app R (lift g p ≫ fst G.X C.scheme)))
      (C.affinePoints.hom.app R (lift g p ≫ snd G.X C.scheme)) = _ at h
    rw [lift_fst, lift_snd] at h
    exact congrArg Module.Grassmannian.toSubmodule h.symm
  refine ⟨schemeActionOfSubmodules s (fun R p q hp => ?_) (matrixPointEndHom b c) act hact, hact⟩
  exact (C.affinePoints.app R).toEquiv.injective (Module.Grassmannian.ext hp)

private def lineAt {W : Type u} [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρ : LineRepresentation k W) {R : TestAlgebra k} (p : Points (projectiveSpace k W) R) :
    AffineLine k W R :=
  (ρ.points _ p).line R (𝟙 _)

private theorem lineAt_change {W : Type u} [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρ : LineRepresentation k W) {R T : TestAlgebra k} (a : R ⟶ T)
    (p : Points (projectiveSpace k W) R) :
    (lineAt ρ (mapPoints a p)).submodule = changeLineSubmodule k W a (lineAt ρ p).submodule := by
  unfold lineAt mapPoints
  rw [ρ.naturality]
  simpa only [LineFamily.pullback, mapPoints, Category.comp_id, Category.id_comp] using
    (ρ.points _ p).compatible a (𝟙 _)

private def exteriorTransportHom (R : TestAlgebra k) (e : ExteriorComparison k R d V) :
    ((R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V)) →* Module.End R (R ⊗[k] Wedge k d V) where
  toFun := exteriorTransport e
  map_one' := by
    change e.equiv.symm.toLinearMap.comp
      ((exteriorPower.map d LinearMap.id).comp e.equiv.toLinearMap) = LinearMap.id
    rw [exteriorPower.map_id, LinearMap.id_comp, LinearEquiv.symm_comp]
  map_mul' f g := by
    change e.equiv.symm.toLinearMap.comp
        ((exteriorPower.map d (f.toLinearMap.comp g.toLinearMap)).comp e.equiv.toLinearMap) =
      (exteriorTransport e f).comp (exteriorTransport e g)
    simp only [exteriorPower.map_comp, exteriorTransport, LinearMap.comp_assoc,
      LinearEquiv.comp_symm_assoc]

private def lineActionFamily (P : PluckerMorphism b d) :
    LineFamily k (Wedge k d V) (G.X ⊗ projectiveSpace k (Wedge k d V)) where
  line R q := transportLine (extendedWedgeEquiv (P.exteriorLines.compare R)
    (matrixTransport b R (c.hom.app R (q ≫ fst G.X _)))) (lineAt P.lines (q ≫ snd G.X _))
  compatible {R T} a q := by
    let Y := projectiveSpace k (Wedge k d V)
    let p := q ≫ snd G.X Y
    let g := q ≫ fst G.X Y
    change (lineAt P.lines (mapPoints a q ≫ snd G.X Y)).submodule.map
        (exteriorTransport (P.exteriorLines.compare T)
          (matrixTransport b T (c.hom.app T (mapPoints a q ≫ fst G.X Y)))) =
      changeLineSubmodule k (Wedge k d V) a ((lineAt P.lines p).submodule.map
        (exteriorTransport (P.exteriorLines.compare R) (matrixTransport b R (c.hom.app R g))))
    rw [show mapPoints a q ≫ fst G.X Y = mapPoints a g from Category.assoc _ _ _,
      show mapPoints a q ≫ snd G.X Y = mapPoints a p from Category.assoc _ _ _,
      matrixPoint_natural c, lineAt_change]
    exact (changeSubmodule_map a _ _ (matrixExteriorTransport_natural b a (c.hom.app R g) _ _)
      (lineAt P.lines p).submodule).symm

set_option maxHeartbeats 800000 in
private def projectiveAction (P : PluckerMorphism b d) :
    { β : SchemeAction G (projectiveSpace k (Wedge k d V)) //
      ∀ (R : TestAlgebra k) (g : Points G.X R) (p : Points (projectiveSpace k (Wedge k d V)) R),
        (lineAt P.lines (lift g p ≫ β.act)).submodule = (lineAt P.lines p).submodule.map
          (exteriorTransport (P.exteriorLines.compare R) (matrixTransport b R (c.hom.app R g))) } := by
  let Y := projectiveSpace k (Wedge k d V)
  let r (R : TestAlgebra k) := (exteriorTransportHom R (P.exteriorLines.compare R)).comp
    (matrixPointEquivHom b c R)
  let act := (P.lines.points (G.X ⊗ Y)).symm (lineActionFamily b c P)
  have hact (R : TestAlgebra k) (g : Points G.X R) (p : Points Y R) :
      (lineAt P.lines (lift g p ≫ act)).submodule = (lineAt P.lines p).submodule.map (r R g) := by
    change ((P.lines.points _ (lift g p ≫ act)).line R (𝟙 _)).submodule = _
    rw [P.lines.naturality, show P.lines.points _ act = _ from Equiv.apply_symm_apply _ _]
    change ((lineActionFamily b c P).line R (𝟙 _ ≫ lift g p)).submodule = _
    rw [Category.id_comp]
    change (lineAt P.lines (lift g p ≫ snd G.X Y)).submodule.map
      (exteriorTransport (P.exteriorLines.compare R)
        (matrixTransport b R (c.hom.app R (lift g p ≫ fst G.X Y)))) = _
    rw [lift_fst, lift_snd]
    rfl
  exact ⟨schemeActionOfSubmodules (fun _ p => (lineAt P.lines p).submodule)
    (fun _ _ _ h => lineRepresentation_affine_ext P.lines h) r act hact, hact⟩

private theorem affinePlucker_formula (P : PluckerMorphism b d) {R : TestAlgebra k}
    (p : Points P.charts.scheme R) :
    (lineAt P.lines (p ≫ P.morphism)).submodule =
      lineSubmodule (P.exteriorLines.compare R) (P.charts.affinePoints.hom.app R p) := by
  have h := P.imageFormula _ p R (𝟙 _)
  rw [P.families.family_apply] at h
  exact h.trans (congrArg (fun q : Points P.charts.scheme R =>
    lineSubmodule (P.exteriorLines.compare R) (P.charts.affinePoints.hom.app R q)) (Category.id_comp p))

include c in
private theorem pluckerEquivariance (P : PluckerMorphism b d) : IsEquivariant b P := by
  let α := grassmannianAction b c P
  let β := projectiveAction b c P
  refine ⟨G, c, α.val, β.val, α.property, β.property, ?_⟩
  apply hom_ext_of_affine_points
  intro R q
  let g := q ≫ fst G.X P.charts.scheme
  let p := q ≫ snd G.X P.charts.scheme
  have hq : lift g p = q := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [g, p]
  have hleft : q ≫ α.val.act ≫ P.morphism = (lift g p ≫ α.val.act) ≫ P.morphism := by
    rw [hq, Category.assoc]
  have hright : q ≫ lift (fst G.X P.charts.scheme) (snd G.X P.charts.scheme ≫ P.morphism) ≫ β.val.act =
      lift g (p ≫ P.morphism) ≫ β.val.act := by
    rw [comp_lift_assoc, Category.assoc]
  rw [hleft, hright]
  apply lineRepresentation_affine_ext P.lines
  change (lineAt P.lines ((lift g p ≫ α.val.act) ≫ P.morphism)).submodule =
    (lineAt P.lines (lift g (p ≫ P.morphism) ≫ β.val.act)).submodule
  rw [β.property, affinePlucker_formula, affinePlucker_formula]
  exact affineExteriorEquivarianceProof k V d R (P.exteriorLines.compare R)
    (matrixTransport b R (c.hom.app R g)) _ _ (α.property R g p)

end SchemeActions

private theorem pluckerEquivariantGeometryProof
    (hplanes : Construction.{u}) (hplane : PlaneSplitAndRank.{u}) (hpoints : Endpoints.{u})
    (hlines : ProjectiveSpaceLineGeometry.{u}) (hpoint : OneDimensionalProjectiveSpace.{u})
    (hpoly : PolynomialChartCoordinates.{u}) (hcover : CoordinateOpenCover.{u})
    (hcharts : CoordinateAffineCharts.{u}) : PluckerEquivariantGeometry.{u} := by
  intro k V Index _ _ _ _ _ dec b d hd
  let e := Fintype.equivFin Index
  let o := LinearOrder.lift' e e.injective
  have hdec : dec = o.toDecidableEq := Subsingleton.elim _ _
  subst dec
  let _ : LinearOrder Index := o
  obtain ⟨P, hp⟩ := pluckerMorphismGeometryProof hplanes hplane hpoints hlines hpoint k V Index b d hd
  refine ⟨P, pluckerClosedImmersionProof hpoly hcover hcharts k V Index b d P, ?_, hp⟩
  exact pluckerEquivariance b (StandardGroups.generalLinearGroupPointsIso k Index) P

section ConditionalProofs

set_option linter.unusedSectionVars false

variable
    (_hAffineConstantBundle : LinearAlgebraicGroups.Specs.ProjectiveSpaces.AffineConstantBundle.{u})
    (_hAffineLineSheafInclusion : LinearAlgebraicGroups.Specs.ProjectiveSpaces.AffineLineSheafInclusion.{u})
    (_hAffineLineSheafReverse : LinearAlgebraicGroups.Specs.ProjectiveSpaces.AffineLineSheafReverse.{u})
    (_hAffinePivotCoordinates : LinearAlgebraicGroups.Specs.ProjectiveSpaces.AffinePivotCoordinates.{u})
    (_hAffinePivotNormalForm : LinearAlgebraicGroups.Specs.ProjectiveSpaces.AffinePivotNormalForm.{u})
    (hCoordinateAffineCharts : LinearAlgebraicGroups.Specs.ProjectiveSpaces.CoordinateAffineCharts.{u})
    (hCoordinateOpenCover : LinearAlgebraicGroups.Specs.ProjectiveSpaces.CoordinateOpenCover.{u})
    (_hCoordinateOverlap : LinearAlgebraicGroups.Specs.ProjectiveSpaces.CoordinateOverlap.{u})
    (_hCoordinateTransition : LinearAlgebraicGroups.Specs.ProjectiveSpaces.CoordinateTransition.{u})
    (_hEmptySegre : LinearAlgebraicGroups.Specs.ProjectiveSpaces.EmptySegre.{u})
    (hOneDimensionalProjectiveSpace : LinearAlgebraicGroups.Specs.ProjectiveSpaces.OneDimensionalProjectiveSpace.{u})
    (hPolynomialChartCoordinates : LinearAlgebraicGroups.Specs.ProjectiveSpaces.PolynomialChartCoordinates.{u})
    (_hProjectiveSpaceGeometry : LinearAlgebraicGroups.Specs.ProjectiveSpaces.ProjectiveSpaceGeometry.{u})
    (hProjectiveSpaceLineGeometry : LinearAlgebraicGroups.Specs.ProjectiveSpaces.ProjectiveSpaceLineGeometry.{u})
    (_hProjectiveSpaceProper : LinearAlgebraicGroups.Specs.ProjectiveSpaces.ProjectiveSpaceProper.{u})
    (_hProjectiveSpaceSegreGeometry : LinearAlgebraicGroups.Specs.ProjectiveSpaces.ProjectiveSpaceSegreGeometry.{u})
    (_hSegreChartSurjective : LinearAlgebraicGroups.Specs.ProjectiveSpaces.SegreChartSurjective.{u})
    (_hTensorBaseChange : LinearAlgebraicGroups.Specs.ProjectiveSpaces.TensorBaseChange.{u})

include _hAffineConstantBundle _hAffineLineSheafInclusion
  _hAffineLineSheafReverse _hAffinePivotCoordinates _hAffinePivotNormalForm hCoordinateAffineCharts
  hCoordinateOpenCover _hCoordinateOverlap _hCoordinateTransition _hEmptySegre
  hOneDimensionalProjectiveSpace hPolynomialChartCoordinates _hProjectiveSpaceGeometry
  hProjectiveSpaceLineGeometry _hProjectiveSpaceProper
  _hProjectiveSpaceSegreGeometry _hSegreChartSurjective _hTensorBaseChange

theorem exteriorBaseChange_conditional : ExteriorBaseChange.{u} := by
  intro R S _ _ _ d M _ _
  exact ⟨exteriorComparison R S d M⟩

theorem affineExteriorLineGeometry_conditional : AffineExteriorLineGeometry.{u} := by
  intro k V _ _ _ _ d hd
  exact ⟨affineExteriorLines GrassmannianCharts.planeSplitAndRank hd⟩

theorem affineExteriorEquivariance_conditional : AffineExteriorEquivariance.{u} :=
  affineExteriorEquivarianceProof

theorem chartAlgebraSurjectivity_conditional : ChartAlgebraSurjectivity.{u} :=
  chartAlgebraSurjectivityProof hPolynomialChartCoordinates

theorem pluckerMorphismGeometry_conditional : PluckerMorphismGeometry.{u} :=
  pluckerMorphismGeometryProof GrassmannianCharts.construction
    GrassmannianCharts.planeSplitAndRank GrassmannianCharts.endpoints
    hProjectiveSpaceLineGeometry hOneDimensionalProjectiveSpace

theorem pluckerChartRestrictions_conditional : PluckerChartRestrictions.{u} :=
  pluckerChartRestrictionsProof hPolynomialChartCoordinates

theorem pluckerClosedImmersion_conditional : PluckerClosedImmersion.{u} :=
  pluckerClosedImmersionProof hPolynomialChartCoordinates hCoordinateOpenCover hCoordinateAffineCharts

theorem pluckerEquivariantGeometry_conditional : PluckerEquivariantGeometry.{u} :=
  pluckerEquivariantGeometryProof GrassmannianCharts.construction
    GrassmannianCharts.planeSplitAndRank GrassmannianCharts.endpoints
    hProjectiveSpaceLineGeometry hOneDimensionalProjectiveSpace hPolynomialChartCoordinates
    hCoordinateOpenCover hCoordinateAffineCharts

end ConditionalProofs

end

end LinearAlgebraicGroups.PluckerEmbedding

universe v8_closure_abe06839400efcca_u0
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«affineExteriorEquivariance» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«AffineExteriorEquivariance».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«affineExteriorEquivariance_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«affineExteriorLineGeometry» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«AffineExteriorLineGeometry».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«affineExteriorLineGeometry_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«chartAlgebraSurjectivity» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«ChartAlgebraSurjectivity».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«chartAlgebraSurjectivity_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«exteriorBaseChange» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«ExteriorBaseChange».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«exteriorBaseChange_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerChartRestrictions» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«PluckerChartRestrictions».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerChartRestrictions_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerClosedImmersion» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«PluckerClosedImmersion».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerClosedImmersion_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerEquivariantGeometry» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«PluckerEquivariantGeometry».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerEquivariantGeometry_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
theorem _root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerMorphismGeometry» : _root_.«LinearAlgebraicGroups».«Specs».«PluckerEmbedding».«PluckerMorphismGeometry».{v8_closure_abe06839400efcca_u0} :=
  @_root_.«LinearAlgebraicGroups».«PluckerEmbedding».«pluckerMorphismGeometry_conditional».{v8_closure_abe06839400efcca_u0} (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineConstantBundle».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafInclusion».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affineLineSheafReverse».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«affinePivotNormalForm».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateAffineCharts».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOpenCover».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateOverlap».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«coordinateTransition».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«emptySegre».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«oneDimensionalProjectiveSpace».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«polynomialChartCoordinates».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceLineGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceProper».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«projectiveSpaceSegreGeometry».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«segreChartSurjective».{v8_closure_abe06839400efcca_u0}) (@_root_.«LinearAlgebraicGroups».«ProjectiveSpaces».«tensorBaseChange».{v8_closure_abe06839400efcca_u0})
