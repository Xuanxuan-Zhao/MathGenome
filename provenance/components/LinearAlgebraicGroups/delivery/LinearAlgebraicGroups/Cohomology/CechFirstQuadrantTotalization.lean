import Specs.LinearAlgebraicGroups.Cohomology.CechFirstQuadrantTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Mathlib.CategoryTheory.Linear.LinearFunctor

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations

universe v u v' u'

namespace LinearAlgebraicGroups.CechFirstQuadrantTotalization

private theorem finiteDiagonals {A : Type u} [Category.{v} A] [Abelian A]
    (K : CohomologicalBicomplex A) (hK : Specs.FirstQuadrant K) : FiniteDiagonals K :=
  quadrantFinite K 0 0 (fun p q hpq => hK p q (by omega))

private theorem singleQuasiIso_isIso_atZero
    {A : Type u} [Category.{v} A] [Abelian A] {X : A} {D : CochainComplex A ℤ}
    (f : (single A (.up ℤ) 0).obj X ⟶ D) (hf : QuasiIso f) :
    IsIso (homologyMap f 0) :=
  (quasiIsoAt_iff_isIso_homologyMap f 0).mp ((quasiIso_iff f).mp hf 0)

private theorem singleQuasiIso_isZero_offZero
    {A : Type u} [Category.{v} A] [Abelian A] {X : A} {D : CochainComplex A ℤ}
    (f : (single A (.up ℤ) 0).obj X ⟶ D) (hf : QuasiIso f) (n : ℤ) (hn : n ≠ 0) :
    IsZero (D.homology n) := by
  let := (quasiIsoAt_iff_isIso_homologyMap f n).mp ((quasiIso_iff f).mp hf n)
  exact (isZero_single_obj_homology (.up ℤ) 0 X n hn).of_iso (asIso (homologyMap f n)).symm

theorem rowAssembly : Specs.RowAssembly.{v,u} := by
  intro A _ _ K _ hK G a₀ z h
  exact AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochain_row_assembly
    K (finiteDiagonals K hK) (fun p q hp => hK p q (Or.inl hp)) G a₀ z
    (fun q => singleQuasiIso_isIso_atZero _ (h q))
    (fun q p hp => singleQuasiIso_isZero_offZero _ (h q) p hp)

theorem columnAssembly : Specs.ColumnAssembly.{v,u} := by
  intro A _ _ K _ hK C b₀ z h
  exact AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochain_column_assembly
    K (finiteDiagonals K hK) (fun p q hq => hK p q (Or.inr hq)) C b₀ z
    (fun p => singleQuasiIso_isIso_atZero _ (h p))
    (fun p q hq => singleQuasiIso_isZero_offZero _ (h p) q hq)

section

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type u'} [Category.{v'} B] [Preadditive B]
  (R : B ⥤ A) [R.Additive]
  {K : CohomologicalBicomplex A} {L : CohomologicalBicomplex B}
  [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]
  (φ : K ⟶ (Specs.mapBicomplex R).obj L)

private def totalMapComponent (n : ℤ) :
    (K.total (.up ℤ)).X n ⟶ R.obj ((L.total (.up ℤ)).X n) :=
  K.totalDesc (fun p q h => (φ.f p).f q ≫ R.map (L.ιTotal (.up ℤ) p q n h))

/-- The map of total complexes obtained by descending on each diagonal. -/
private def totalMap :
    K.total (.up ℤ) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (L.total (.up ℤ)) where
  f := totalMapComponent R φ
  comm' n m h := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p + q = n at hpq
    change n + 1 = m at h
    have h₁ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    have hm₁ : p + 1 + q = m := by omega
    have hm₂ : p + (q + 1) = m := by omega
    have horizontal :
        (φ.f p).f q ≫ R.map ((L.d p (p + 1)).f q) =
          (K.d p (p + 1)).f q ≫ (φ.f (p + 1)).f q :=
      HomologicalComplex₂.comm_f φ p (p + 1) q
    have vertical :
        (φ.f p).f q ≫ R.map ((L.X p).d q (q + 1)) =
          (K.X p).d q (q + 1) ≫ (φ.f p).f (q + 1) :=
      (φ.f p).comm q (q + 1)
    change K.ιTotal (.up ℤ) p q n hpq ≫
        totalMapComponent R φ n ≫ R.map (L.D₁ (.up ℤ) n m + L.D₂ (.up ℤ) n m) =
      K.ιTotal (.up ℤ) p q n hpq ≫
        (K.D₁ (.up ℤ) n m + K.D₂ (.up ℤ) n m) ≫ totalMapComponent R φ m
    simp only [totalMapComponent, HomologicalComplex₂.ι_totalDesc_assoc,
      Functor.map_add, Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
      ← Functor.map_comp, Category.assoc]
    rw [HomologicalComplex₂.d₁_eq L _ h₁ q m hm₁,
      HomologicalComplex₂.d₂_eq L _ p h₂ m hm₂,
      HomologicalComplex₂.d₁_eq K _ h₁ q m hm₁,
      HomologicalComplex₂.d₂_eq K _ p h₂ m hm₂]
    simp only [Functor.map_units_smul, Linear.comp_units_smul, Linear.units_smul_comp,
      Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((φ.f p).f q), horizontal, Category.assoc,
      ← Category.assoc ((φ.f p).f q), vertical, Category.assoc]
    simp only [HomologicalComplex₂.ι_totalDesc]

private theorem totalMap_components : Specs.TotalMapComponents R K L φ (totalMap R φ) := by
  intro p q n h
  simp only [totalMap, totalMapComponent, HomologicalComplex₂.ι_totalDesc]

end

theorem totalMapExists : Specs.TotalMap.{v,u,v',u'} := by
  intro A _ _ B _ _ R _ K L _ _ φ
  refine ⟨totalMap R φ, totalMap_components R φ, ?_⟩
  intro t ht
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  exact (ht p q n h).trans ((totalMap_components R φ) p q n h).symm

theorem rowNaturality : Specs.RowNaturality.{v,u,v',u'} := by
  intro A _ _ B _ _ R _ K L _ _ φ G G' g a₀ a₀' a a' t ha ha' ht h
  apply HomologicalComplex.hom_ext
  intro n
  have hn : a₀.f n ≫ (φ.f 0).f n = g.f n ≫ R.map (a₀'.f n) := congr_hom h n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [ha n, ha' n, Functor.map_comp, Category.assoc, ht 0 n n (zero_add n)]
  simp only [← Category.assoc, hn]

set_option backward.isDefEq.respectTransparency false in
theorem columnNaturality : Specs.ColumnNaturality.{v,u,v',u'} := by
  intro A _ _ B _ _ R _ K L _ _ φ C C' g b₀ b₀' b b' t hb hb' ht h
  apply HomologicalComplex.hom_ext
  intro n
  have hn : b₀.f n ≫ (φ.f n).f 0 = g.f n ≫ R.map (b₀'.f n) := congr_hom h n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [hb n, hb' n, Functor.map_comp, Category.assoc, ht n 0 n (add_zero n)]
  simp only [← Category.assoc, hn]

end LinearAlgebraicGroups.CechFirstQuadrantTotalization
