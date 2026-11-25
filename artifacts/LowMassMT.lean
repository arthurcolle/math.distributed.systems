/-
ZetaMult/LowMassMT.lean — the low-multiplicity bound with the Montgomery–Taylor constant.

`ZetaMult.LowMass` gives L₃ ≥ (5/6 − ε)·N from zeta23's Theorem C pipeline (second-moment constant
κ = 4/3). zeta23's Theorem D pipeline uses the optimal (Montgomery–Taylor) window and has
κ = 1/c₁*, c₁* = `cMT` = 0.7532960…. The same substitution there gives
  L₃(T,2T) ≥ (3/2 − 1/(2c₁*) − ε)·N(T,2T),   so   M₃(T,2T) ≤ ((1/c₁* − 1)/2 + ε)·N(T,2T),
numerically 83.625 % and 16.375 % (the decimals are not part of the formal statements).

A linear program over all the rank–trace constraints zeta23 provides (every real c, ζ side and ξ′
side, linked by the multiplicity transfer) has optimum (1/c₁* − 1)/2 for multiplicity ≥ 3, so this
is the best bound obtainable from those inputs. The LP is a numerical computation, not formalized.
-/
import ZetaMult.LowMass
import Zeta23.ThmD.Mult
import Solution

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace ThmD

open Assembly

section AbstractLow

/-- **Low-multiplicity mass with the optimal window, c = 3, abstract**: (3/2 − 1/(2c) − ε)·N ≤ L₃.
The proof is that of `thmD_mult3_abstract` with the seam `seamA_mult3_low`. -/
theorem thmD_low3_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z (P.atD T) T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - c⁻¹ / 2 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nlow T (2 * T) := by
  intro ε hε
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  -- the functions of T (abbreviations)
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (6 * R₁ T + R₂ T + 5 * (NII Z T : ℝ)
      + B T * (6 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
  -- basic limits
  have hLtop := tendsto_L_atTop P hlam0
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  ------------------------------------------------------------------
  -- (1) the main inequality, eventually in T
  ------------------------------------------------------------------
  have hmain : ∀ᶠ T in atTop, (3 - c⁻¹) * N T - err T ≤ 2 * (Z.Nlow T (2 * T) : ℝ) := by
    filter_upwards [hBlock, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hBl hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    -- Seam A for the window-realizing parameters
    have hA := seamA_mult3_low hT0 (fun z => GzGp.phiHat_conj _ T z) (fun r => GzGp.phiHat_ofReal _ T r)
      (poissonSqD hP h8) hTl haposD hLpos
    -- the hat-unit traces in terms of the abstract data
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    -- |tr Ĝ − N| ≤ R₁
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    -- ‖Ĝ‖² ≤ cinv N + R₂
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := Nd_lower_c3 hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (3 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (3 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  ------------------------------------------------------------------
  -- (2) err = o(N)
  ------------------------------------------------------------------
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  -- R₁ = o(N)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- cinv is eventually in [0, 2/c] and bounded
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2
  -- R₂ = o(N)
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  -- N(I′∖I) = o(N)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  -- B → 0
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1
  -- the bracket and the constant-drift term
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  -- the extra 2R₁ + 2NII + 2B of the c = 3 bracket
  have oB : B =o[atTop] N := by
    refine ((isLittleO_one_iff ℝ).2 o4).trans_isBigO (IsBigO.of_bound 1 ?_)
    filter_upwards [hNtop.eventually_ge_atTop 1] with T h1
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by linarith), one_mul]; exact h1
  have o5' : (fun T => 6 * R₁ T + R₂ T + 5 * (NII Z T : ℝ)
      + B T * (6 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) =o[atTop] N := by
    have := o5.add (((o1.const_mul_left 2).add (o3.const_mul_left 2)).add (oB.const_mul_left 2))
    exact this.congr_left fun T => by ring
  have herr_o : err =o[atTop] N := o5'.add o6
  ------------------------------------------------------------------
  -- (3) conclude (halve)
  ------------------------------------------------------------------
  have hfin := eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
    (2 * ε) (by linarith)
  obtain ⟨T₀, hT₀⟩ := hfin
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

end AbstractLow

/-- fixed λ ∈ (0,1), abstract zero configuration: (GD(λ) − ε)·N ≤ L₃. -/
theorem thmD_low_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (GD P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nlow T (2 * T) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  have hBlock := eventually_blockInputsD Z hP
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_low3_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha hBlock θ₀ hTail hθ₀ hNII
    hGzGp hId hcalE
  simpa only [GD] using h

/-- ζ at fixed λ ∈ (0,1): (GD(λ) − ε)·N ≤ L₃, unconditional. -/
theorem thmD_low_mult_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (GD lam - ε) * (Ncount T (2 * T) : ℝ) ≤ zetaZeroConfig.Nlow T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  simpa [paramsOf] using thmD_low_lam_abstract zetaZeroConfig paperInputs_zeta
    (paramsOf stdProfile lam) hP h1

/-- **(3 − 1/c₁*)/2 of the zeros of ζ are simple or double** (with multiplicity; dyadic windows). -/
theorem thmD₀_low_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (GD 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ zetaZeroConfig.Nlow T (2 * T) := by
  have h := eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => 2 * (zetaZeroConfig.Nlow T (2 * T) : ℝ) - (Ncount T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun lam hl1 hl2 ε hε => by
      obtain ⟨T₀, hT₀⟩ := thmD_low_mult_lam (by linarith) hl2 (ε / 2) (by linarith)
      refine ⟨T₀, fun T hT => ?_⟩
      have := hT₀ T hT
      simp only [GD_eq] at this
      linarith)
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h (2 * ε) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have := hT₀ T hT
  rw [GD_eq]
  linarith

/-- cumulative form. -/
theorem thmD₀_low_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (GD 1 - ε) * (Ncount 0 T : ℝ) ≤ zetaZeroConfig.Nlow 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ hab hbd => Nlow_add zetaZeroConfig hab hbd) thmD₀_low_mult

end ThmD
end Zeta23

/-! ## In the vocabulary of the trusted definition layer -/

namespace ZetaMult

/-- **At least (3 − 1/c₁*)/2 = 0.83625… of the nontrivial zeros of ζ are simple or double.**
For every ε > 0 and all large T: `(3/2 − 1/(2c₁*) − ε)·N(T,2T) ≤ L₃(T,2T)`, with c₁* = `cMT`. -/
theorem simple_or_double_MT :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ (NmultLT 3 T (2 * T) : ℝ) := by
  have h := Zeta23.ThmD.thmD₀_low_mult
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

theorem simple_or_double_MT_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount 0 T : ℝ) ≤ (NmultLT 3 0 T : ℝ) := by
  have h := Zeta23.ThmD.thmD₀_low_mult_cumulative
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

/-- **At most (1/c₁* − 1)/2 = 0.16375… of the nontrivial zeros of ζ have multiplicity three or
more** (with multiplicity): for every ε > 0 and all large T,
`M₃(T,2T) ≤ (1/(2c₁*) − 1/2 + ε)·N(T,2T)`. -/
theorem triple_zeros_MT :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (NmultGE 3 T (2 * T) : ℝ) ≤ (cMT⁻¹ / 2 - 1 / 2 + ε) * (Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := simple_or_double_MT ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsplit : (Ncount T (2 * T) : ℝ) = (NmultLT 3 T (2 * T) : ℝ) + (NmultGE 3 T (2 * T) : ℝ) := by
    exact_mod_cast Ncount_eq_LT_add_GE (Zeta23.zerosIn_finite T (2 * T)) 3
  linarith [h T hT]

theorem triple_zeros_MT_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (NmultGE 3 0 T : ℝ) ≤ (cMT⁻¹ / 2 - 1 / 2 + ε) * (Ncount 0 T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := simple_or_double_MT_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsplit : (Ncount 0 T : ℝ) = (NmultLT 3 0 T : ℝ) + (NmultGE 3 0 T : ℝ) := by
    exact_mod_cast Ncount_eq_LT_add_GE (Zeta23.zerosIn_finite 0 T) 3
  linarith [h T hT]

end ZetaMult

#print axioms ZetaMult.simple_or_double_MT
#print axioms ZetaMult.simple_or_double_MT_cumulative
#print axioms ZetaMult.triple_zeros_MT
#print axioms ZetaMult.triple_zeros_MT_cumulative
