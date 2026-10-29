import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Dobra de Mellin de um FE-pair

Portado do ATK kernel (espelho público, M-Core commit `390e378`), parte abstrata de
`ATK/BaseRiemannTeta.lean` (`cauda`, `f_modif_eq`, `mellinConvergent_cauda`, `Λ₀_eq_caudas`).
A parte sobre a teta de Jacobi e `ζ` não foi portada (não é usada aqui).

Para todo FE-pair fraco `P` da Mathlib:
`Λ₀(s) = M[cauda f](s) + ε · M[cauda g](k − s)`, onde `cauda f = 𝟙_{(1,∞)}(f − f₀)`.
-/

open Complex Set MeasureTheory
open scoped Real

namespace ClayBSDProof.MellinFold

/-! ### Parte abstrata: dobrar a transformada de Mellin de `f_modif` -/

/-- Cauda `𝟙_{(1,∞)} (f − f₀)` de um FE-pair. -/
noncomputable def cauda (P : WeakFEPair ℂ) : ℝ → ℂ := (Ioi 1).indicator fun x => P.f x - P.f₀

theorem f_modif_eq (P : WeakFEPair ℂ) {x : ℝ} (hx : 0 < x) :
    P.f_modif x = cauda P x + P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • cauda P.symm x⁻¹) := by
  rcases lt_trichotomy x 1 with h1 | rfl | h1
  · have hinv : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr h1
    have hFE := P.hf_modif_FE x⁻¹ (inv_pos.mpr hx)
    rw [one_div, inv_inv] at hFE
    rw [hFE, cauda, indicator_of_notMem (notMem_Ioi.mpr h1.le), zero_add, cauda,
      indicator_of_mem (mem_Ioi.mpr hinv)]
    simp only [WeakFEPair.g_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hinv),
      indicator_of_notMem (notMem_Ioo_of_ge hinv.le), add_zero, WeakFEPair.symm, smul_eq_mul]
    rw [Real.inv_rpow hx.le, ofReal_inv, ofReal_cpow hx.le, cpow_neg]
    ring
  · simp [WeakFEPair.f_modif, cauda]
  · have hinv : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr h1),
      indicator_of_notMem (notMem_Ioo_of_ge h1.le), add_zero, cauda, cauda,
      indicator_of_mem (mem_Ioi.mpr h1), indicator_of_notMem (notMem_Ioi.mpr hinv.le)]
    simp

theorem mellinConvergent_f_modif (P : WeakFEPair ℂ) (s : ℂ) : MellinConvergent P.f_modif s :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin s).1

/-- A cauda tem transformada de Mellin convergente em todo `s`. -/
theorem mellinConvergent_cauda (P : WeakFEPair ℂ) (s : ℂ) : MellinConvergent (cauda P) s := by
  have h := (mellinConvergent_f_modif P s).indicator (measurableSet_Ioi (a := (1 : ℝ)))
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  by_cases h1 : 1 < x
  · simp only [indicator_of_mem (mem_Ioi.mpr h1), cauda, WeakFEPair.f_modif, Pi.add_apply,
      indicator_of_notMem (notMem_Ioo_of_ge h1.le), add_zero]
  · simp only [indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h1)), cauda, smul_zero]

/-- **Dobra de Mellin**: `Λ₀(s) = M[cauda f](s) + ε · M[cauda g](k − s)`. -/
theorem Λ₀_eq_caudas (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ₀ s = mellin (cauda P) s + P.ε * mellin (cauda P.symm) (P.k - s) := by
  have hA := mellinConvergent_cauda P s
  set B : ℝ → ℂ := fun x => P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • cauda P.symm x⁻¹) with hB
  have hEq : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t)
      (fun t => (t : ℂ) ^ (s - 1) • cauda P t + (t : ℂ) ^ (s - 1) • B t) (Ioi 0) := by
    intro t ht
    simp only [hB, f_modif_eq P ht, smul_add]
  have hBc : MellinConvergent B s := by
    have h := (mellinConvergent_f_modif P s).sub hA
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hB, f_modif_eq P ht, smul_add, add_sub_cancel_left]
  rw [WeakFEPair.Λ₀, mellin, setIntegral_congr_fun measurableSet_Ioi hEq, integral_add hA hBc]
  change mellin (cauda P) s + mellin B s = _
  rw [hB, mellin_const_smul, mellin_cpow_smul, mellin_comp_inv, smul_eq_mul]
  congr 3
  ring

end ClayBSDProof.MellinFold
