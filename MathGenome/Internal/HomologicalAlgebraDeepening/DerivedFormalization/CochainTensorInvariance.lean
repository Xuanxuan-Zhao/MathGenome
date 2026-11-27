import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorInvariance
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ModelQuasiIsoInvariance
import Mathlib.Algebra.DirectSum.Module
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorTransport
/-! Mixed-universe tensor tests for ordinary cochain complexes. -/

namespace DerivedFormalization.CochainTensorInvariance

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open Specs.DerivedFormalization.CochainTensorInvariance
open Specs.DerivedFormalization.CochainTensorTransport
  (adequateModelType closedAdjunctionType curryingType ringComparisonType)
open Specs.DerivedFormalization.CochainRingTransport
  (moduleEquivalenceValue complexFunctorValue)
open Specs.DerivedFormalization.DG.Basic (moduleTensor)
open CochainTensor (tensor map ι pure)
open scoped TensorProduct DirectSum

universe u v

noncomputable section

private theorem quasiIso_iff_of_comm {R : Type u} [CommRing R]
    {X Y X' Y' : Comp.{v} R} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') (h : f ≫ b.hom = a.hom ≫ g) :
    QuasiIso f ↔ QuasiIso g := by
  rw [← quasiIso_iff_comp_right f b.hom, h, quasiIso_iff_comp_left]

theorem adequateTests_conditional
    (adequacy : adequateModelType.{u,v})
    (_ : closedAdjunctionType.{u,v})
    (_ : curryingType.{u,v})
    (_ : ringComparisonType.{u,v}) :
    adequateTestsType.{u,v} := by
  intro R A _ _ e
  obtain ⟨M⟩ := adequacy e
  let F := complexFunctorValue e
  let H := (moduleEquivalenceValue e).functor
  have hq {X Y : Comp.{v} R} (g : X ⟶ Y) : QuasiIso (F.map g) ↔ QuasiIso g :=
    (CochainRingTransport.complexProperties e X Y g).2.1
  have hz (V : ModuleCat.{v} R) : IsZero V ↔ IsZero (H.obj V) :=
    ⟨H.map_isZero, fun h => ((moduleEquivalenceValue e).inverse.map_isZero h).of_iso
      ((moduleEquivalenceValue e).unitIso.app V)⟩
  refine ⟨M, ⟨?_, ?_, ?_, fun g => (hq g).symm, ?_, ?_⟩⟩
  · intro P
    change ((∀ q : ℤ, Module.Flat R (P.X q)) ∧
      (∃ N : ℤ, ∀ q : ℤ, N < q → IsZero (P.X q))) ↔
      ((∀ q : ℤ, Module.Flat A (H.obj (P.X q))) ∧
        (∃ N : ℤ, ∀ q : ℤ, N < q → IsZero (H.obj (P.X q))))
    have hflat (V : ModuleCat.{v} R) : Module.Flat A (H.obj V) ↔ Module.Flat R V :=
      CochainRingTransport.flatness (e := e) V
    simp only [hflat, ← hz]
  · intro P
    exact (M.kFlat P).symm.trans (CochainTensor.diagonalKFlat (F.obj P))
  · intro P
    let := M.chainMonoidal
    exact ⟨fun h E hE n => (h E hE n).of_iso (M.tensorModel E P),
      fun h E hE n => (h E hE n).of_iso (M.tensorModel E P).symm⟩
  · intro P X Y g
    have h := M.tensor_natural (𝟙 P) g
    rw [F.map_id] at h
    exact (hq _).symm.trans ((quasiIso_iff_of_comm _ _ _ _ h).symm)
  · intro P X Y g
    let := M.chainMonoidal
    exact quasiIso_iff_of_comm _ _ _ _ (M.tensorModel_natural (𝟙 P) g)

theorem diagonalTests_conditional
    (_ : adequateModelType.{u,u})
    (_ : closedAdjunctionType.{u,u})
    (_ : curryingType.{u,u})
    (_ : ringComparisonType.{u,u}) :
    diagonalTestsType.{u} := by
  intro R _ P
  refine ⟨CochainTensor.diagonalKFlat P, ?_⟩
  intro X Y g
  rfl

section Flat

variable {R : Type u} [CommRing R]

private abbrev column (P E : Comp.{v} R) (p : ℤ) : Comp.{v} R :=
  (((moduleTensor R).obj (P.X p)).mapHomologicalComplex (.up ℤ)).obj E⟦(-p : ℤ)⟧

private abbrev columnIn (P E : Comp.{v} R) (n p : ℤ) :
    (column P E p).X n ⟶ (tensor P E).X n :=
  ι P E p (n + -p) n (by omega)

private def toColumns (P E : Comp.{v} R) (n : ℤ) :
    (tensor P E).X n ⟶ ModuleCat.of R (⨁ p : ℤ, (column P E p).X n) :=
  mapBifunctorDesc (F := moduleTensor R) (c := .up ℤ) (fun i j h => by
    change i + j = n at h
    obtain rfl : j = n + -i := by omega
    exact ModuleCat.ofHom (DirectSum.lof R ℤ (fun p => (column P E p).X n) i))

@[reassoc]
private theorem columnIn_toColumns (P E : Comp.{v} R) (n p : ℤ) :
    columnIn P E n p ≫ toColumns P E n =
      ModuleCat.ofHom (DirectSum.lof R ℤ (fun q => (column P E q).X n) p) := by
  unfold columnIn toColumns
  rw [ι_mapBifunctorDesc]
  rfl

private def fromColumns (P E : Comp.{v} R) (n : ℤ) :
    ModuleCat.of R (⨁ p : ℤ, (column P E p).X n) ⟶ (tensor P E).X n :=
  ModuleCat.ofHom (DirectSum.toModule R ℤ _ (fun p => (columnIn P E n p).hom))

private theorem toColumns_injective (P E : Comp.{v} R) (n : ℤ) :
    Function.Injective (toColumns P E n) := by
  have h : toColumns P E n ≫ fromColumns P E n = 𝟙 _ := by
    apply mapBifunctor.hom_ext (F := moduleTensor R) (c := .up ℤ)
    intro p q hpq
    change p + q = n at hpq
    obtain rfl : q = n + -p := by omega
    change columnIn P E n p ≫ (toColumns P E n ≫ fromColumns P E n) = _
    rw [columnIn_toColumns_assoc, Category.comp_id]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (DirectSum.toModule_lof R (φ := fun p => (columnIn P E n p).hom) p)
  intro x y hxy
  have hx : fromColumns P E n (toColumns P E n x) = x := ConcreteCategory.congr_hom h x
  have hy : fromColumns P E n (toColumns P E n y) = y := ConcreteCategory.congr_hom h y
  rw [hxy] at hx
  exact hx.symm.trans hy

private def columnProj (P E : Comp.{v} R) (n p : ℤ) :
    (tensor P E).X n ⟶ (column P E p).X n :=
  toColumns P E n ≫ ModuleCat.ofHom (DirectSum.component R ℤ (fun q => (column P E q).X n) p)

@[reassoc (attr := simp)]
private theorem columnIn_proj (P E : Comp.{v} R) (n p : ℤ) :
    columnIn P E n p ≫ columnProj P E n p = 𝟙 _ := by
  rw [columnProj, columnIn_toColumns_assoc]
  apply ModuleCat.hom_ext
  exact DirectSum.component_comp_lof_same R (M := fun q => (column P E q).X n) p

@[reassoc]
private theorem summand_proj_ne (P E : Comp.{v} R) (n p q r : ℤ)
    (h : p + q = n) (hp : p ≠ r) :
    ι P E p q n h ≫ columnProj P E n r = 0 := by
  obtain rfl : q = n + -p := by omega
  change columnIn P E n p ≫ columnProj P E n r = 0
  rw [columnProj, columnIn_toColumns_assoc]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
    DirectSum.component_comp_lof, dite_eq_right hp]

private theorem columnIn_d (P E : Comp.{v} R) (n p : ℤ) :
    columnIn P E n p ≫ (tensor P E).d n (n + 1) =
      (show (column P E p).X n ⟶ (tensor P E).X (n + 1) from
        ((moduleTensor R).map (P.d p (p + 1))).app (E.X (n + -p)) ≫
          ι P E (p + 1) (n + -p) (n + 1) (by omega)) +
      (column P E p).d n (n + 1) ≫ columnIn P E (n + 1) p := by
  classical
  let T := moduleTensor.{u,v} R
  let c := ComplexShape.up ℤ
  have hp : c.Rel p (p + 1) := rfl
  have he : c.Rel (n + -p) (n + 1 + -p) := by
    change n + -p + 1 = n + 1 + -p
    omega
  rw [mapBifunctor.d_eq P E T c, Preadditive.comp_add]
  unfold columnIn
  rw [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq P E T c hp (n + -p) (n + 1) (by change p + 1 + (n + -p) = n + 1; omega),
    mapBifunctor.d₂_eq P E T c p he (n + 1) (by change p + (n + 1 + -p) = n + 1; omega)]
  change 1 • (_ : _ ⟶ _) + p.negOnePow • (_ : _ ⟶ _) =
    _ + ((-p).negOnePow • (_ : _ ⟶ _)) ≫ _
  rw [one_smul, Int.negOnePow_neg, Linear.units_smul_comp]
  rfl

private theorem d_columnProj (P E : Comp.{v} R) (n p : ℤ) :
    (tensor P E).d n (n + 1) ≫ columnProj P E (n + 1) p =
      columnProj P E n p ≫ (column P E p).d n (n + 1) +
      columnProj P E n (p - 1) ≫
        (columnIn P E n (p - 1) ≫ (tensor P E).d n (n + 1) ≫ columnProj P E (n + 1) p) := by
  apply mapBifunctor.hom_ext (F := moduleTensor R) (c := .up ℤ)
  intro i j h
  change i + j = n at h
  obtain rfl : j = n + -i := by omega
  change columnIn P E n i ≫ _ = columnIn P E n i ≫ _
  rw [Preadditive.comp_add, ← Category.assoc]
  by_cases hi : i = p
  · subst i
    rw [columnIn_proj_assoc, summand_proj_ne_assoc _ _ _ _ _ _ _ (by omega), zero_comp,
      add_zero, columnIn_d, Preadditive.add_comp, Category.assoc,
      summand_proj_ne _ _ _ _ _ _ _ (by omega), comp_zero, zero_add, Category.assoc,
      columnIn_proj, Category.comp_id]
  · rw [summand_proj_ne_assoc _ _ _ _ _ _ _ hi, zero_comp, zero_add]
    by_cases hj : i = p - 1
    · subst i
      rw [columnIn_proj_assoc, Category.assoc]
    · rw [summand_proj_ne_assoc _ _ _ _ _ _ _ hj, zero_comp, columnIn_d,
        Preadditive.add_comp, Category.assoc, summand_proj_ne _ _ _ _ _ _ _ (by omega),
        comp_zero, Category.assoc, summand_proj_ne _ _ _ _ _ _ _ hi, comp_zero, add_zero]

private theorem exactAt_iff_cycle {K : Comp.{v} R} (n : ℤ) :
    K.ExactAt n ↔ ∀ x : K.X n, K.d n (n + 1) x = 0 →
      ∃ y : K.X (n - 1), K.d (n - 1) n y = x := by
  rw [K.exactAt_iff' (i := n - 1) (j := n) (k := n + 1)
      ((ComplexShape.up ℤ).prev_eq' (show (n - 1) + 1 = n by omega))
      ((ComplexShape.up ℤ).next_eq' (show n + 1 = n + 1 from rfl)),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  refine ⟨fun h x hx => (h x).1 hx, fun h x => ⟨h x, ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact ConcreteCategory.congr_hom (K.d_comp_d (n - 1) n (n + 1)) y

private theorem column_exact (P E : Comp.{v} R) (p : ℤ) [Module.Flat R (P.X p)]
    (hE : E.Acyclic) : (column P E p).Acyclic := by
  intro n
  let T := (moduleTensor R).obj (P.X p)
  let c := ComplexShape.up ℤ
  have hp : c.Rel (n - 1 + -p) (n + -p) := by change _ + 1 = _; omega
  have hn : c.Rel (n + -p) (n + 1 + -p) := by change _ + 1 = _; omega
  have he := (E.exactAt_iff' _ _ _ (c.prev_eq' hp) (c.next_eq' hn)).1 (hE (n + -p))
  have ht : Function.Exact (T.map (E.d (n - 1 + -p) (n + -p)))
      (T.map (E.d (n + -p) (n + 1 + -p))) :=
    Module.Flat.lTensor_exact (P.X p)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 he)
  rw [exactAt_iff_cycle]
  intro x hx
  change (-p).negOnePow • T.map (E.d (n + -p) (n + 1 + -p)) x = 0 at hx
  obtain ⟨b, hb⟩ := (ht x).1 ((smul_eq_zero_iff_eq (a := (-p).negOnePow)).mp hx)
  refine ⟨(-p).negOnePow • b, ?_⟩
  change (-p).negOnePow • T.map (E.d (n - 1 + -p) (n + -p)) ((-p).negOnePow • b) = x
  have hs {U V : ModuleCat.{v} R} (f : U ⟶ V) (s : ℤˣ) (z : U) :
      f (s • z) = s • f z := by
    change f.hom (s • z) = s • f.hom z
    simp only [Units.smul_def, map_zsmul]
  rw [hs, hb, smul_smul, Int.units_mul_self, one_smul]

private theorem boundedFlat_tensor_acyclic (P E : Comp.{v} R)
    (flat : ∀ p, Module.Flat R (P.X p)) (N : ℤ) (bound : ∀ p > N, IsZero (P.X p))
    (hE : E.Acyclic) : (tensor P E).Acyclic := by
  classical
  intro n
  rw [exactAt_iff_cycle]
  let π := columnProj P E
  let inc := columnIn P E
  let K := tensor P E
  have hd (k l p : ℤ) (hkl : k + 1 = l) (z : K.X k) (hz : π k (p - 1) z = 0) :
      π l p (K.d k l z) = (column P E p).d k l (π k p z) := by
    subst l
    have h := ConcreteCategory.congr_hom (d_columnProj P E k p) z
    change π (k + 1) p (K.d k (k + 1) z) = (column P E p).d k (k + 1) (π k p z) +
      π (k + 1) p (K.d k (k + 1) (inc k (p - 1) (π k (p - 1) z))) at h
    simpa only [hz, map_zero, add_zero] using h
  -- Each step removes the lowest remaining coordinate of a cycle.
  have eliminate (m : ℕ) (x : K.X n) (hx : K.d n (n + 1) x = 0)
      (tail : ∀ p < N + 1 - (m : ℤ), π n p x = 0) :
      ∃ y : K.X (n - 1), K.d (n - 1) n y = x := by
    induction m generalizing x with
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero]
      apply toColumns_injective P E n
      apply DFinsupp.ext
      intro p
      change π n p (0 : K.X n) = π n p x
      rw [map_zero]
      by_cases hp : p ≤ N
      · exact (tail p (by omega)).symm
      · have hzero : IsZero ((column P E p).X n) :=
          ((moduleTensor R).flip.obj (E.X (n + -p))).map_isZero (bound p (by omega))
        exact (@Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hzero) _ _)
    | succ m ih =>
      let p : ℤ := N + 1 - ((m + 1 : ℕ) : ℤ)
      have below (q : ℤ) (hq : q < p) : π n q x = 0 := tail q hq
      have hp := hd n (n + 1) p rfl x (below _ (by omega))
      rw [hx, map_zero] at hp
      let := flat p
      obtain ⟨b, hb⟩ := (exactAt_iff_cycle n).1 (column_exact P E p hE n) _ hp.symm
      let w : K.X (n - 1) := inc (n - 1) p b
      have hw (q : ℤ) (hq : q < p) : π (n - 1) q w = 0 :=
        ConcreteCategory.congr_hom (summand_proj_ne P E (n - 1) p _ q _ (by omega)) b
      have hwp : π (n - 1) p w = b :=
        ConcreteCategory.congr_hom (columnIn_proj P E (n - 1) p) b
      have hdiff (q : ℤ) (hq : q ≤ p) :
          π n q (K.d (n - 1) n w) = (column P E q).d (n - 1) n (π (n - 1) q w) := by
        exact hd (n - 1) n q (by omega) w (hw _ (by omega))
      have hh : K.d n (n + 1) (x - K.d (n - 1) n w) = 0 := by
        rw [map_sub, hx]
        have h : K.d n (n + 1) (K.d (n - 1) n w) = 0 :=
          ConcreteCategory.congr_hom (K.d_comp_d (n - 1) n (n + 1)) w
        rw [h, sub_zero]
      obtain ⟨y, hy⟩ := ih _ hh (by
        intro q hq
        have hqp : q ≤ p := by dsimp [p] at *; omega
        rw [map_sub, hdiff q hqp]
        rcases lt_or_eq_of_le hqp with h | rfl
        · rw [below q h, hw q h, map_zero, sub_zero]
        · rw [hwp, hb, sub_self])
      exact ⟨y + w, by rw [map_add, hy, sub_add_cancel]⟩
  intro x hx
  -- Finite support puts each individual cycle in some bounded degree tail.
  let S := (toColumns P E n x : ⨁ p : ℤ, (column P E p).X n).support
  let a := (insert 0 S).min' (Finset.insert_nonempty _ _)
  have lower (p : ℤ) (hp : p < a) : π n p x = 0 := by
    change (toColumns P E n x : ⨁ q : ℤ, (column P E q).X n) p = 0
    apply DFinsupp.notMem_support_iff.mp
    intro hm
    exact (not_le_of_gt hp) (Finset.min'_le _ _ (Finset.mem_insert_of_mem hm))
  refine eliminate (N + 1 - a).toNat x hx (fun p hp => lower p ?_)
  omega

theorem boundedAboveFlatIsKFlat_conditional
    (_ : adequateModelType.{u,v})
    (_ : closedAdjunctionType.{u,v})
    (_ : curryingType.{u,v})
    (_ : ringComparisonType.{u,v}) :
    boundedAboveFlatIsKFlatType.{u,v} := by
  intro R _ P flat ⟨N, bound⟩ E hE n
  exact (boundedFlat_tensor_acyclic P E flat N bound hE n).of_iso (CochainTensor.symmetryIso P E)

end Flat

section Cone

open CochainComplex (mappingCone)
open CochainComplex.HomComplex CochainComplex.mappingCone
open private differential_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
open private map_sign from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensor
open private quasiIso_iff_acyclic_cone from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ModelQuasiIsoInvariance

variable {R : Type u} [CommRing R]
variable (P : Comp.{v} R) {X Y Z : Comp.{v} R}

private theorem pure_add_right (i j n : ℤ) (h : i + j = n)
    (x : P.X i) (y z : X.X j) :
    pure P X h x (y + z) = pure P X h x y + pure P X h x z := by
  simp only [CochainTensor.pure, TensorProduct.tmul_add, map_add]

private theorem pure_zero_right (i j n : ℤ) (h : i + j = n) (x : P.X i) :
    pure P X h x (0 : X.X j) = 0 := by
  simp only [CochainTensor.pure, TensorProduct.tmul_zero, map_zero]

private theorem pure_sign_right (i j n : ℤ) (h : i + j = n)
    (x : P.X i) (s : ℤˣ) (y : X.X j) :
    pure P X h x (s • y) = s • pure P X h x y := by
  have hs : x ⊗ₜ[R] (s • y) = s • (x ⊗ₜ[R] y) := by
    simp only [Units.smul_def]
    exact map_zsmul (TensorProduct.mk R (P.X i) (X.X j) x) _ y
  unfold CochainTensor.pure
  rw [hs]
  exact map_sign (ι P X i j n h) s _

/-- The graded tensor action on the second factor takes a degree-`a` cochain
with the sign `(-1)^(i*a)` on the first factor of degree `i`. -/
private def tensorCochain {a : ℤ} (f : Cochain X Y a) :
    Cochain (tensor P X) (tensor P Y) a :=
  Cochain.mk fun n m hn =>
    mapBifunctorDesc (F := moduleTensor R) (c := .up ℤ) fun i j hij =>
      (i * a).negOnePow •
        ((moduleTensor R).obj (P.X i)).map (f.v j (j + a) rfl) ≫
          ι P Y i (j + a) m (by change i + j = n at hij; omega)

private theorem tensorCochain_apply {a : ℤ} (f : Cochain X Y a)
    {i j n m j' : ℤ} (h : i + j = n) (hn : n + a = m) (hj : j + a = j')
    (x : P.X i) (y : X.X j) :
    (tensorCochain P f).v n m hn (pure P X h x y) =
      (i * a).negOnePow • pure P Y (by omega : i + j' = m) x (f.v j j' hj y) := by
  subst j'
  have eq := ι_mapBifunctorDesc (K₁ := P) (K₂ := X) (F := moduleTensor R)
    (c := .up ℤ) (fun k l hkl =>
      (k * a).negOnePow • ((moduleTensor R).obj (P.X k)).map (f.v l (l + a) rfl) ≫
        ι P Y k (l + a) m (by change k + l = n at hkl; omega)) i j h
  change ι P X i j n h ≫ (tensorCochain P f).v n m hn = _ at eq
  exact ConcreteCategory.congr_hom eq (x ⊗ₜ[R] y)

private def tensorCochainAddHom (a : ℤ) :
    Cochain X Y a →+ Cochain (tensor P X) (tensor P Y) a where
  toFun := tensorCochain P
  map_zero' := by
    apply Cochain.ext
    intro n m h
    apply CochainTensor.term_hom_ext
    intro i j hij x y
    rw [tensorCochain_apply P _ hij h rfl, Cochain.zero_v, Cochain.zero_v]
    change _ • pure P Y _ x 0 = 0
    rw [pure_zero_right, smul_zero]
  map_add' := by
    intro f g
    apply Cochain.ext
    intro n m h
    apply CochainTensor.term_hom_ext
    intro i j hij x y
    rw [tensorCochain_apply P _ hij h rfl, Cochain.add_v]
    change (i * a).negOnePow • pure P Y _ x (f.v j (j + a) rfl y + g.v j (j + a) rfl y) =
      (tensorCochain P f).v n m h (pure P X hij x y) +
        (tensorCochain P g).v n m h (pure P X hij x y)
    rw [tensorCochain_apply P f hij h rfl, tensorCochain_apply P g hij h rfl,
      pure_add_right, smul_add]

private theorem tensorCochain_ofHom (f : X ⟶ Y) :
    tensorCochain P (Cochain.ofHom f) = Cochain.ofHom (map (𝟙 P) f) := by
  apply Cochain.ext₀
  intro n
  apply CochainTensor.term_hom_ext
  intro i j h x y
  rw [tensorCochain_apply P _ h (add_zero n) (add_zero j), Cochain.ofHom_v, Cochain.ofHom_v,
    mul_zero, Int.negOnePow_zero, one_smul, CochainTensor.map_on_pure, id_f, ModuleCat.id_apply]

private theorem tensorCochain_comp {a b c : ℤ} (f : Cochain X Y a) (g : Cochain Y Z b)
    (hc : a + b = c) :
    tensorCochain P (f.comp g hc) = (tensorCochain P f).comp (tensorCochain P g) hc := by
  apply Cochain.ext
  intro n m h
  apply CochainTensor.term_hom_ext
  intro i j hij x y
  have hs : (i * c).negOnePow = (i * a).negOnePow * (i * b).negOnePow := by
    rw [← hc, mul_add, Int.negOnePow_add]
  rw [tensorCochain_apply P _ hij h rfl, Cochain.comp_v _ _ hc j (j + a) (j + c) rfl (by omega),
    Cochain.comp_v _ _ hc n (n + a) m rfl (by omega), ModuleCat.comp_apply,
    ModuleCat.comp_apply, tensorCochain_apply P _ hij rfl rfl, map_sign,
    tensorCochain_apply P _ (show i + (j + a) = n + a by omega) (by omega)
      (show j + a + b = j + c by omega), hs, smul_smul]

private theorem tensor_d_at (i j n m i' j' : ℤ) (h : i + j = n) (hm : n + 1 = m)
    (hi : i + 1 = i') (hj : j + 1 = j') (x : P.X i) (y : X.X j) :
    (tensor P X).d n m (pure P X h x y) =
      pure P X (by omega : i' + j = m) (P.d i i' x) y +
        i.negOnePow • pure P X (by omega : i + j' = m) x (X.d j j' y) := by
  subst m i' j'
  exact CochainTensor.differential P X i j n h x y

private theorem tensorCochain_δ {a b : ℤ} (hb : a + 1 = b) (f : Cochain X Y a) :
    tensorCochain P (δ a b f) = δ a b (tensorCochain P f) := by
  apply Cochain.ext
  intro n m h
  apply CochainTensor.term_hom_ext
  intro i j hij x y
  rw [tensorCochain_apply P _ hij h rfl,
    differential_apply hb rfl (v₀ := j + a) (i₁ := j + 1) (by omega) rfl,
    differential_apply hb h (v₀ := n + a) (i₁ := n + 1) (by omega) rfl,
    tensorCochain_apply P f hij rfl rfl, map_sign,
    tensor_d_at P i (j + a) (n + a) m (i + 1) (j + b) (by omega) (by omega) rfl (by omega),
    tensor_d_at P i j n (n + 1) (i + 1) (j + 1) hij rfl rfl rfl, map_add, map_sign,
    tensorCochain_apply P f (show i + 1 + j = n + 1 by omega) (by omega) rfl,
    tensorCochain_apply P f (show i + (j + 1) = n + 1 by omega) (by omega)
      (show j + 1 + a = j + b by omega),
    pure_add_right, pure_sign_right]
  have h₁ : (i * b).negOnePow = (i * a).negOnePow * i.negOnePow := by
    rw [← hb, mul_add, mul_one, Int.negOnePow_add]
  have h₂ : b.negOnePow * ((i + 1) * a).negOnePow = -(i * a).negOnePow := by
    rw [← Int.negOnePow_add, add_mul, one_mul]
    rw [show b + (i * a + a) = i * a + (a + a) + 1 by omega,
      Int.negOnePow_succ, Int.negOnePow_add, Int.negOnePow_add, Int.units_mul_self, mul_one]
  have h₃ : b.negOnePow * (i.negOnePow * (i * a).negOnePow) =
      (i * a).negOnePow * i.negOnePow * b.negOnePow := by ac_rfl
  simp only [smul_add, smul_smul]
  rw [h₂, Units.neg_smul, h₁, h₃]
  abel

private theorem tensorCochain_zero (a : ℤ) :
    tensorCochain P (0 : Cochain X Y a) = 0 :=
  (tensorCochainAddHom P a).map_zero

private theorem tensorCochain_neg {a : ℤ} (f : Cochain X Y a) :
    tensorCochain P (-f) = -tensorCochain P f :=
  (tensorCochainAddHom P a).map_neg f

private theorem tensorCochain_add {a : ℤ} (f g : Cochain X Y a) :
    tensorCochain P (f + g) = tensorCochain P f + tensorCochain P g :=
  (tensorCochainAddHom P a).map_add f g

private abbrev tensorLeftFunctor (P : Comp.{v} R) : Comp.{v} R ⥤ Comp.{v} R :=
  (moduleTensor.{u,v} R).map₂CochainComplex.obj P

/-- The cone comparison for the actual signed tensor, with the shifted
projection and inclusion given by the degree (1) and (-1) cochain actions. -/
private def tensorConeIso (f : X ⟶ Y) :
    tensor P (mappingCone f) ≅ mappingCone (map (𝟙 P) f) := by
  let T := tensorLeftFunctor P
  let g := CochainTensor.map (𝟙 P) f
  let l := tensorCochain P (inl f)
  let r := CochainTensor.map (𝟙 P) (inr f)
  let p : Cocycle (tensor P (mappingCone f)) (tensor P X) 1 :=
    Cocycle.mk (tensorCochain P (fst f).1) 2 rfl (by
      rw [← tensorCochain_δ P (show (1 : ℤ) + 1 = 2 by decide),
        Cocycle.δ_eq_zero, tensorCochain_zero])
  let q := tensorCochain P (snd f)
  have hl : δ (-1) 0 l = Cochain.ofHom (g ≫ r) := by
    dsimp only [l, g, r]
    rw [← tensorCochain_δ P (neg_add_cancel 1), δ_inl, tensorCochain_ofHom]
    exact congrArg Cochain.ofHom (T.map_comp _ _)
  have hq : δ 0 1 q + p.1.comp (Cochain.ofHom g) (add_zero 1) = 0 := by
    change δ 0 1 (tensorCochain P (snd f)) +
      (tensorCochain P (fst f).1).comp (Cochain.ofHom (map (𝟙 P) f)) (add_zero 1) = 0
    rw [← tensorCochain_δ P (zero_add 1), δ_snd, tensorCochain_neg,
      tensorCochain_comp, tensorCochain_ofHom, neg_add_cancel]
  let a := lift g p q hq
  let b := desc g l r hl
  have hr : Cochain.ofHom r = tensorCochain P (Cochain.ofHom (inr f)) :=
    (tensorCochain_ofHom P _).symm
  have hId (W : Comp.{v} R) :
      tensorCochain P (Cochain.ofHom (𝟙 W)) = Cochain.ofHom (𝟙 (tensor P W)) := by
    rw [tensorCochain_ofHom]
    exact congrArg Cochain.ofHom (T.map_id W)
  refine ⟨a, b, ?_, ?_⟩
  · apply Cochain.ofHom_injective
    change Cochain.ofHom (a ≫ b) = Cochain.ofHom (𝟙 _)
    simp only [Cochain.ofHom_comp, a, b, ofHom_lift, ofHom_desc, liftCochain_descCochain]
    change (tensorCochain P (fst f).1).comp l (add_neg_cancel 1) +
      q.comp (Cochain.ofHom r) (add_zero 0) = _
    rw [hr, show l = tensorCochain P (inl f) from rfl,
      show q = tensorCochain P (snd f) from rfl,
      ← tensorCochain_comp, ← tensorCochain_comp, ← tensorCochain_add, mappingCone.id, hId]
  · apply Cochain.ofHom_injective
    change Cochain.ofHom (b ≫ a) = Cochain.ofHom (𝟙 (mappingCone g))
    rw [Cochain.ofHom_comp, ext_cochain_from_iff g (-1) 0 (neg_add_cancel 1)]
    constructor
    · rw [← Cochain.comp_assoc_of_third_is_zero_cochain, inl_desc, Cochain.comp_id,
        ext_cochain_to_iff g (-1) 0 (neg_add_cancel 1)]
      simp only [a, Cochain.comp_assoc_of_second_is_zero_cochain, ofHom_lift,
        liftCochain_fst, liftCochain_snd, inl_fst, inl_snd]
      change (tensorCochain P (inl f)).comp (tensorCochain P (fst f).1) (neg_add_cancel 1) =
        _ ∧ (tensorCochain P (inl f)).comp (tensorCochain P (snd f)) (add_zero (-1)) = _
      simp only [← tensorCochain_comp, inl_fst, inl_snd, hId, tensorCochain_zero, and_self]
    · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_desc,
        Cochain.comp_id, ext_cochain_to_iff g 0 1 (zero_add 1)]
      simp only [a, Cochain.comp_assoc_of_first_is_zero_cochain, ofHom_lift,
        liftCochain_fst, liftCochain_snd, inr_fst, inr_snd]
      change (Cochain.ofHom r).comp (tensorCochain P (fst f).1) (zero_add 1) = _ ∧
        (Cochain.ofHom r).comp (tensorCochain P (snd f)) (add_zero 0) = _
      rw [hr, ← tensorCochain_comp, ← tensorCochain_comp]
      simp only [inr_fst, inr_snd, tensorCochain_zero, hId, and_self]

theorem tensorMapQuasiIso_conditional
    (_ : adequateModelType.{u,v})
    (_ : closedAdjunctionType.{u,v})
    (_ : curryingType.{u,v})
    (_ : ringComparisonType.{u,v}) :
    tensorMapQuasiIsoType.{u,v} := by
  intro R _ P hP X Y f hf
  have hcone := hP (mappingCone f) ((quasiIso_iff_acyclic_cone f).1 hf)
  apply (quasiIso_iff_acyclic_cone _).2
  intro n
  exact (hcone n).of_iso (CochainTensor.symmetryIso (mappingCone f) P ≪≫ tensorConeIso P f)

end Cone

end

end DerivedFormalization.CochainTensorInvariance

universe v8_closure_da721fa7b46ec428_u0 v8_closure_da721fa7b46ec428_u1
theorem _root_.«DerivedFormalization».«CochainTensorInvariance».«adequateTests» : _root_.«Specs».«DerivedFormalization».«CochainTensorInvariance».«adequateTestsType».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1} :=
  @_root_.«DerivedFormalization».«CochainTensorInvariance».«adequateTests_conditional».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1})
theorem _root_.«DerivedFormalization».«CochainTensorInvariance».«boundedAboveFlatIsKFlat» : _root_.«Specs».«DerivedFormalization».«CochainTensorInvariance».«boundedAboveFlatIsKFlatType».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1} :=
  @_root_.«DerivedFormalization».«CochainTensorInvariance».«boundedAboveFlatIsKFlat_conditional».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1})
theorem _root_.«DerivedFormalization».«CochainTensorInvariance».«diagonalTests» : _root_.«Specs».«DerivedFormalization».«CochainTensorInvariance».«diagonalTestsType».{v8_closure_da721fa7b46ec428_u0} :=
  @_root_.«DerivedFormalization».«CochainTensorInvariance».«diagonalTests_conditional».{v8_closure_da721fa7b46ec428_u0} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u0})
theorem _root_.«DerivedFormalization».«CochainTensorInvariance».«tensorMapQuasiIso» : _root_.«Specs».«DerivedFormalization».«CochainTensorInvariance».«tensorMapQuasiIsoType».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1} :=
  @_root_.«DerivedFormalization».«CochainTensorInvariance».«tensorMapQuasiIso_conditional».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_da721fa7b46ec428_u0, v8_closure_da721fa7b46ec428_u1})
