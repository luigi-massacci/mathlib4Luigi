import Mathlib

--For testing
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic


open TopologicalSpace SeminormFamily Set Function Seminorm UniformSpace
open scoped BoundedContinuousFunction Topology NNReal

-- Think `𝕜 = ℝ` or `𝕜 = ℂ`
variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable {n : ℕ∞}

-- Q: parametrize by some Ω : Opens E?
structure TestFunction (n : ℕ∞) : Type _ where
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected compact_supp' : HasCompactSupport toFun

scoped[Distributions] notation "𝓓^{" n "}(" E ", " F ")" =>
  TestFunction E F n

open Distributions

class TestFunctionClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  compact_supp (f : B) : HasCompactSupport f

open TestFunctionClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    rcases (map_continuous f).bounded_above_of_compact_support (compact_supp f) with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)


namespace TestFunction

instance toTestFunctionClass :
    TestFunctionClass 𝓓^{n}(E, F) E F n where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  compact_supp f := f.compact_supp'

variable {E F}

protected theorem contDiff (f : 𝓓^{n}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem compact_supp (f : 𝓓^{n}(E, F)) : HasCompactSupport f := compact_supp f

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : 𝓓^{n}(E, F)) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections TestFunction (toFun → apply)

@[ext]
theorem ext {f g : 𝓓^{n}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `BoundedContDiffMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  compact_supp' := h.symm ▸ f.compact_supp

@[simp]
theorem coe_copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h


@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓓^{n}(E, F)) (x : E) :
   (f : BoundedContinuousFunction E F) x  = (f x) := rfl


section AddCommGroup

instance : Zero 𝓓^{n}(E, F) where
  zero := TestFunction.mk 0 contDiff_zero_fun HasCompactSupport.zero

@[simp]
lemma coe_zero : (0 : 𝓓^{n}(E, F)) = (0 : E → F) :=
  rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓓^{n}(E, F)) x = 0 :=
  rfl

instance : Add 𝓓^{n}(E, F) where
  add f g := TestFunction.mk (f + g) (f.contDiff.add g.contDiff) (f.compact_supp.add g.compact_supp)

@[simp]
lemma coe_add (f g : 𝓓^{n}(E, F)) : (f + g : 𝓓^{n}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

instance : Neg 𝓓^{n}(E, F) where
  neg f := TestFunction.mk (-f) (f.contDiff.neg) (f.compact_supp.neg')

-- TOOD: add HasCompactSupport.sub in general
instance instSub : Sub 𝓓^{n}(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.contDiff').sub (g.contDiff'),
    sub_eq_add_neg (f : E → F) g ▸ f.compact_supp.add g.compact_supp.neg'
    ⟩
  ⟩

-- TOOD: add HasCompactSupport.const_smul_left in general
instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
   SMul R 𝓓^{n}(E, F) :=
  ⟨fun c f ↦
    TestFunction.mk (c • (f : E → F)) (f.contDiff.const_smul c)  f.compact_supp.smul_left
  ⟩

@[simp]
lemma coe_smul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) : (c • f : 𝓓^{n}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) (x : E) : (c • f) x = c • (f x) :=
  rfl


instance instNSMul : SMul ℕ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance instZSMul : SMul ℤ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance : AddCommGroup 𝓓^{n}(E, F) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F K n)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓓^{n}(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

variable {E F}

theorem coe_coeHom : (coeHom E F n : 𝓓^{n}(E, F) → E → F) = DFunLike.coe :=
  rfl

theorem coeHom_injective : Function.Injective (coeHom E F n) := by
  rw [coe_coeHom]
  exact DFunLike.coe_injective

end AddCommGroup

section Module

-- TODO: replace ext ... ext... elsewhere where possible
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}(E, F) :=
  (coeHom_injective n).module R (coeHom E F n) fun _ _ => rfl

end Module

-- Testing:

variable (S : Compacts (Fin 3 → ℝ))
-- This shoudl fail:
-- #synth Module ℂ 𝓓^{5}_{S}(Fin 3 → ℝ, Fin 3 → ℝ)
#synth Module ℝ 𝓓^{5}_{S}(Fin 3 → ℝ, Fin 3 → ℂ)

#synth Module ℂ 𝓓^{⊤}_{S}(Fin 3 → ℝ, Fin 3 → ℂ)

variable (S': Compacts (Fin 3 → ℂ))
#synth Module ℂ 𝓓^{⊤}_{S'}(Fin 3 → ℂ, Fin 3 → ℂ)


variable (n : ℕ∞) (F)

def ContDiffMapSupportedIn.toTestFunction (K : Compacts E) : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}(E, F) where
  toFun f := TestFunction.mk f (f.contDiff) (f.hasCompactSupport)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


open ContDiffMapSupportedIn

noncomputable def originalTop : TopologicalSpace 𝓓^{n}(E, F) :=
  ⨆ (K : Compacts E), coinduced (toTestFunction 𝕜 F n K) (inferInstance)

variable (E)
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}(E, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}(E, F)
       | originalTop ℝ F n ≤ t ∧ @LocallyConvexSpace ℝ 𝓓^{n}(E, F) _ _ _ _ t}

---------------------------------------------------------------------------------------------------
-- This part is self-contained

noncomputable def seminorm : Seminorm 𝕜 𝓓^{n}(E, F) :=
  sorry

def TestFunctionSeminormFamily : SeminormFamily 𝕜 𝓓^{n}(E, F) (Compacts E) :=
  sorry

theorem TestFunction_WithSeminorms : WithSeminorms (TestFunctionSeminormFamily 𝕜 E F n) := by
  sorry

instance instContinuousSMul : ContinuousSMul 𝕜 𝓓^{n}(E, F) := by
  rw [(TestFunction_WithSeminorms 𝕜 E F n).withSeminorms_eq]
  exact (TestFunctionSeminormFamily 𝕜 E F n).moduleFilterBasis.continuousSMul

-- TODO: Obviously cannot register any of the following as instances for 𝕜
-- (cannot reasonably synthetize it), so what now?
instance instIsTopologicalAddGroup : IsTopologicalAddGroup 𝓓^{n}(E, F) := by
  rw [(TestFunction_WithSeminorms ℝ E F n).withSeminorms_eq]
  exact (TestFunctionSeminormFamily ℝ E F n).addGroupFilterBasis.isTopologicalAddGroup

instance instUniformSpace : UniformSpace 𝓓^{n}(E, F) := by
  exact (TestFunctionSeminormFamily ℝ E F n).addGroupFilterBasis.uniformSpace

instance instIsUniformAddGroup : IsUniformAddGroup 𝓓^{n}(E, F) :=
  (TestFunctionSeminormFamily ℝ E F n).addGroupFilterBasis.isUniformAddGroup


--------------------------------------------------------------------------------------------

noncomputable instance : LocallyConvexSpace ℝ 𝓓^{n}(E, F) := by
  apply LocallyConvexSpace.sInf
  simp only [mem_setOf_eq, and_imp, imp_self, implies_true]

theorem continuous_toTestFunction (K : Compacts E):
    Continuous (toTestFunction 𝕜 F n K) := by
  apply continuous_iff_coinduced_le.2
  have : originalTop 𝕜 F n ≤ TestFunction.topologicalSpace E F n := by
    exact le_sInf (by aesop)
  exact le_trans (le_sSup (by aesop)) this

variable {n E F}


variable (𝕜': Type*) [NontriviallyNormedField 𝕜']

protected theorem continuous_iff {V : Type*} [AddCommMonoid V] [Module ℝ V] [Module 𝕜' V]
  [SMulCommClass ℝ 𝕜' V] [t : TopologicalSpace V] [LocallyConvexSpace ℝ V]
  (f : 𝓓^{n}(E, F) →ₗ[ℝ] V) :
    Continuous f ↔
    ∀ K : Compacts E, Continuous (f ∘ toTestFunction 𝕜 F n K) := by
    rw [continuous_iff_le_induced]
    have : TestFunction.topologicalSpace E F n ≤ induced f t
          ↔ originalTop ℝ F n ≤ induced f t := by
        constructor <;> refine fun h ↦ ?_
        · refine le_trans (le_sInf (fun _ _ ↦ ?_)) h
          simp_all only [LocallyConvexSpace.induced f, mem_setOf_eq]
        · refine sInf_le ?_
          simp only [mem_setOf_eq, LocallyConvexSpace.induced f, and_true, h]
    rw [this, originalTop, iSup_le_iff]
    simp_rw [← @coinduced_le_iff_le_induced _ _ f _ t, coinduced_compose]
    simp_rw [← continuous_iff_coinduced_le]
    rfl

variable (E F n)

@[simps]
noncomputable def to_bcfₗ : 𝓓^{n}(E, F) →ₗ[𝕜] E →ᵇ F  where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma to_bcf_comp_eq (K : Compacts E) :
  (to_bcfₗ 𝕜 E F n) ∘ (ContDiffMapSupportedIn.toTestFunction 𝕜 F n K)  =
    ContDiffMapSupportedIn.to_bcfₗ 𝕜 := by
    congr

@[simps!]
noncomputable def to_bcfL : 𝓓^{n}(E, F) →L[𝕜] E →ᵇ F  :=
  { toLinearMap := to_bcfₗ 𝕜 E F n
    cont := show Continuous (to_bcfₗ ℝ E F n)
      by
        (
          rw [TestFunction.continuous_iff ℝ ℝ (to_bcfₗ ℝ E F n)]
          intro K
          rw [to_bcf_comp_eq _ _]
          exact (ContDiffMapSupportedIn.to_bcfL 𝕜).continuous
        )
  }

theorem injective_to_bcfL: Function.Injective (to_bcfL 𝕜 E F n) := by
  intro f g
  simp [to_bcfL, to_bcfₗ]

-- Testing:
#check to_bcfL ℂ (Fin 3 → ℝ) (Fin 3 → ℂ) 5

#check to_bcfL ℝ (Fin 3 → ℝ) (Fin 3 → ℂ) ⊤


theorem T25Space_TestFunction : T25Space 𝓓^{n}(E, F) :=
  T25Space.of_injective_continuous (injective_to_bcfL ℝ E F n) (to_bcfL ℝ E F n).continuous

variable {G 𝕜': Type*} [NontriviallyNormedField 𝕜']
variable {σ : 𝕜 →+* 𝕜'}
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]

variable {E F n}
variable (𝕜')

def toTestFunction_comp
  (f : 𝓓^{n}(E, F) → 𝓓^{n}(E, G)) : Prop :=
  ∀ K : Compacts E, ∃ g : 𝓓^{n}_{K}(E, F) → 𝓓^{n}_{K}(E, G), Continuous g
        ∧ f ∘ toTestFunction 𝕜 F n K = toTestFunction 𝕜' G n K ∘ g

open ContDiffMapSupportedIn in
theorem continuous_of_commute_toTestFunction
  (f : 𝓓^{n}(E, F) →ₗ[ℝ] 𝓓^{n}(E, G))
  (hc : toTestFunction_comp 𝕜 𝕜' f) :
    Continuous f := by
  refine (TestFunction.continuous_iff ℝ ℝ f).mpr (fun K ↦ ?_)
  obtain ⟨g, hg, hfg⟩ := hc K
  exact hfg ▸ (continuous_toTestFunction ℝ E G n K).comp hg

variable {𝕜 𝕜'}
def mkLM (A : (E → F) → (E → G))
    (hadd : ∀ (f g : 𝓓^{n}(E, F)) (x), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓓^{n}(E, F)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : ∀ f : 𝓓^{n}(E, F), ContDiff ℝ n (A f))
    (hsupp : ∀ f : 𝓓^{n}(E, F), HasCompactSupport (A f)) :
    𝓓^{n}(E, F) →ₛₗ[σ] 𝓓^{n}(E, G) where
  toFun f :=
    { toFun := A f
      contDiff' := hsmooth f
      compact_supp' := hsupp f }
  map_add' f g := ext (hadd f g)
  map_smul' a f := ext (hsmul a f)


-- TODO: think about hsmul / hsmul'
noncomputable def mkCLM [RingHomIsometric σ] (A : (E → F) → (E → G))
    (hadd : ∀ (f g : 𝓓^{n}(E, F)) (x : E), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓓^{n}(E, F)) (x : E), A (a • f) x = σ a • A f x)
    (hsmul' : ∀ (a : ℝ) (f : 𝓓^{n}(E, F)) (x : E), A (a • f) x = a • A f x)
    (hsmooth : ∀ f : 𝓓^{n}(E, F), ContDiff ℝ n (A f))
    (hsupp : ∀ f : 𝓓^{n}(E, F), HasCompactSupport (A f))
    (hcomp : toTestFunction_comp 𝕜 𝕜' (mkLM A hadd hsmul hsmooth hsupp)) :
    𝓓^{n}(E, F) →SL[σ] 𝓓^{n}(E, G) where
  cont := continuous_of_commute_toTestFunction 𝕜 𝕜' (mkLM A hadd hsmul' hsmooth hsupp) hcomp
  toLinearMap := mkLM A hadd hsmul hsmooth hsupp


variable (𝕜 E F n)
noncomputable def fderivCLM : 𝓓^{n}(E, F) →L[𝕜] 𝓓^{n-1}(E, E →L[ℝ] F) :=
  sorry

-- Pause on derivates because they are painful.

section Integration

open MeasureTheory Module

variable [MeasurableSpace E]
variable (μ : Measure E)

-- Consider just replacing F with RCLike 𝕜

variable {E F}
noncomputable def ofMeasure: 𝓓^{n}(E, F) → F := (∫ x, · x ∂μ)

@[simp]
lemma ofMeasure_apply (f : 𝓓^{n}(E, F)) : ofMeasure n μ f = (∫ x, f x ∂μ) := by
  rfl

variable [BorelSpace E] [IsFiniteMeasureOnCompacts μ]

lemma map_integrable (f : 𝓓^{n}(E, F)) : Integrable f μ  := by
  apply Continuous.integrable_of_hasCompactSupport (map_continuous f) (compact_supp f)

variable {K : Compacts E}


-- TODO: move to ContDiffMapSupportedIn
lemma map_integrable' (f : 𝓓^{n}_{K}(E, F)) : Integrable f μ  := by
  apply Continuous.integrable_of_hasCompactSupport (map_continuous f) (f.hasCompactSupport)


variable [SecondCountableTopology E] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

noncomputable def ofMeasureₗ : 𝓓^{n}(E, F) →ₗ[𝕜] F :=
  { toFun := ofMeasure n μ
    map_add' := fun f g ↦ integral_add (f.map_integrable n μ) (g.map_integrable n μ)
    map_smul' := fun c f ↦ integral_smul c f}

variable [CompleteSpace F]


--TODO : Spin off continuity of integration
@[simps! apply]
noncomputable def ofMeasureL : 𝓓^{n}(E, F) →L[𝕜] F where
  toLinearMap := (ofMeasureₗ 𝕜 n μ : 𝓓^{n}(E, F) →ₗ[𝕜] F)
  cont := show Continuous (ofMeasureₗ ℝ n μ) by
    (
      rw [TestFunction.continuous_iff ℝ 𝕜 (ofMeasureₗ ℝ n μ)]
      intro K
      have fin_μ : IsFiniteMeasure (μ.restrict K) := by
        have : Fact (μ K < ⊤) := fact_iff.mpr <| IsCompact.measure_lt_top (Compacts.isCompact K)
        apply MeasureTheory.Restrict.isFiniteMeasure
      set int' : (E →ᵇ F) →ₗ[𝕜] F := {
          toFun := fun f => (∫ x, f x ∂(μ.restrict K))
          map_add' := by
            intro f g
            apply integral_add
            · exact BoundedContinuousFunction.integrable (μ.restrict ↑K) f
            · exact BoundedContinuousFunction.integrable (μ.restrict ↑K) g
          map_smul' := fun c f ↦ integral_smul c f
        }
      have : IsBoundedLinearMap 𝕜 int' := by
        constructor
        · exact LinearMap.isLinear int'
        · by_cases h : (μ.restrict K) = 0
          · use 1
            refine ⟨zero_lt_one, fun f ↦ ?_⟩
            simp [int', h]
          · use (MeasureTheory.measureUnivNNReal (μ.restrict K))
            constructor
            · apply_mod_cast @MeasureTheory.measureUnivNNReal_pos _ _ _ fin_μ
              exact h
            · intro f
              simp [int']
              apply le_trans (BoundedContinuousFunction.norm_integral_le_mul_norm _ f)
              gcongr
              apply le_of_eq
              rfl
      set int : (E →ᵇ F) →L[𝕜] F :=
        { toLinearMap := int'
          cont := by
            apply IsBoundedLinearMap.continuous this  }
      have : ofMeasureₗ ℝ n μ ∘ (toTestFunction ℝ F n K)
          = int ∘ (ContDiffMapSupportedIn.to_bcfL 𝕜) := by
        ext f
        simp [ofMeasureₗ, int, int']
        have hK : MeasurableSet (K : Set E) := by
          refine IsCompact.measurableSet ?_
          exact Compacts.isCompact K
        have : ∫ (x : E) in (K : Set E)ᶜ, f x ∂μ = 0 := by
          refine setIntegral_eq_zero_of_forall_eq_zero ?_
          exact f.zero_on_compl
        rw [← add_zero (∫ (x : E) in ↑K, f x ∂μ), ← this,
          MeasureTheory.integral_add_compl hK (map_integrable' n μ f)]
        congr
      rw [this]
      exact int.continuous.comp (ContDiffMapSupportedIn.to_bcfL 𝕜).continuous
    )


end Integration


section LocallyIntegrable


open MeasureTheory Module

variable [MeasurableSpace E]
variable (μ : Measure E)

variable [NormedSpace ℝ 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [ContinuousConstSMul 𝕜 F]

variable {E F}

-- At this stage, probably easier to assume RCLike 𝕜 everywhere
variable [Module 𝕜 F] [SMulCommClass ℝ 𝕜 F] [ContinuousConstSMul 𝕜 F] [IsScalarTower ℝ 𝕜 F]
-- Q: Remove hf at this stage?
noncomputable def ofLocallyIntegrable (f : E → F)  :
    𝓓^{n}(E, 𝕜) → F := fun φ : 𝓓^{n}(E, 𝕜) ↦ (∫ x, (φ x) • (f x) ∂μ)

@[simp]
lemma ofLocallyIntegrable_apply (f : E → F) (φ : 𝓓^{n}(E, 𝕜)) :
    ofLocallyIntegrable 𝕜 n μ f φ = (∫ x, (φ x) • (f x) ∂μ) := by
  rfl

variable [OpensMeasurableSpace E]

-- TODO: Generalize lemma to 𝕜
-- Note: restricting to ℝ to use the lemma.
lemma ofLocallyIntegrable_integrable {f : E → F} (hf : LocallyIntegrable f μ) (φ : 𝓓^{n}(E, ℝ)) :
    Integrable (fun x ↦ (φ x) • (f x)) μ := by
  apply MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hf
          (map_continuous φ) (compact_supp φ)

-- TODO: This fails to synthetize Module 𝕜 𝓓^{n}(E, 𝕜), so fixing map to be ℝ-linear.
-- (Having 𝓓^{n}(E, 𝕜) otherwise works, see note on ofLocallyIntegrable_integrable for why it is
-- fixed to ℝ.)
noncomputable def ofLocallyIntegrableₗ {f : E → F} (hf : LocallyIntegrable f μ) :
    𝓓^{n}(E, ℝ) →ₗ[ℝ] F :=
  { toFun := ofLocallyIntegrable ℝ n μ f
    map_add' := fun φ Φ  ↦ by
      simp only [ofLocallyIntegrable_apply, add_apply]
      simp_rw [add_smul]
      apply integral_add (ofLocallyIntegrable_integrable n μ hf φ)
        (ofLocallyIntegrable_integrable n μ hf Φ)
    map_smul' := fun c φ ↦ by
      simp only [ofLocallyIntegrable_apply, smul_apply, RingHom.id_apply]
      simp_rw [smul_assoc, integral_smul c (fun x ↦  φ x • f x)]
  }

@[simps! apply]
noncomputable def ofLocallyIntegrableL {f : E → F} (hf : LocallyIntegrable f μ) :
    𝓓^{n}(E, ℝ) →L[ℝ] F where
  toLinearMap := (ofLocallyIntegrableₗ n μ hf : 𝓓^{n}(E, ℝ) →ₗ[ℝ] F)
  cont := show Continuous (ofLocallyIntegrableₗ n μ hf) by
    (
        rw [TestFunction.continuous_iff ℝ ℝ (ofLocallyIntegrableₗ n μ hf)]
        intro K
        sorry
    )

end LocallyIntegrable


section DiracDelta

variable {E}

noncomputable def delta (x : E) : 𝓓^{n}(E, F) →L[𝕜] F :=
  (BoundedContinuousFunction.evalCLM 𝕜 x).comp (to_bcfL 𝕜 E F n)

@[simp]
theorem delta_apply (x₀ : E) (f : 𝓓^{n}(E, F)) : delta 𝕜 F n x₀ f = f x₀ :=
  rfl

open MeasureTheory Measure

variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
variable [CompleteSpace F]
/-- Integrating against the Dirac measure is equal to the delta distribution. -/
@[simp]
theorem integralCLM_dirac_eq_delta (x : E) : ofMeasureL 𝕜 n (dirac x) = delta 𝕜 F n x := by
  aesop

end DiracDelta

variable (f : ContDiffBump (![1, 2, 3]: Fin 3 → ℝ))

#check delta ℝ (Fin 3 → ℂ) 5 (![1, 2, 3]: Fin 3 → ℝ)


end TestFunction

namespace Distribution

open TestFunction

variable [RCLike 𝕜] [Module ℝ F]

def HasOrder (T : 𝓓^{n}(E, 𝕜) →L[ℝ] F) (m : ℕ) : Prop := sorry

end Distribution

#min_imports
