import CollatzCoalescence.Generic

/-!
# Quantitative rates for the generic fair-coin framework

* `stay_mul_le_of_potential` (R1): a potential `Q` with unit drift on `{t ∉ F, V t < lam}`
  bounds the staying probability, `(k + 1) * stay k s ≤ Q s`.
* `one_sub_hit_le` (R2): tail of the hitting time of `F`.
* `survival_rate_of_renewal` (R3): a `t ^ (-1/2)` tail for the hitting time of `F` from `R`,
  together with uniform absorption from `F` and return to `R ∪ {abs}`, gives a
  `t ^ (-1/2)` survival bound.
-/

namespace Coalescence.Generic

variable {S : Type*} (step : S → Bool → S)

/-! ## R1 and R2 -/

section rate
variable (F : Set S) [DecidablePred (· ∈ F)] (V : S → ℝ) (lam : ℝ) (Q : S → ℝ)

/-- **R1 (expected time).** A nonnegative potential `Q` that drops by at least `1` on average
at every state of `{t ∉ F, V t < lam}` bounds `(k + 1) * stay k`. -/
theorem stay_mul_le_of_potential (hQ : ∀ s, 0 ≤ Q s)
    (hstep : ∀ s, s ∉ F → V s < lam → (Q (step s false) + Q (step s true)) / 2 + 1 ≤ Q s)
    (k : ℕ) (s : S) : ((k : ℝ) + 1) * stay step F V lam k s ≤ Q s := by
  induction k generalizing s with
  | zero =>
    rw [stay_zero]
    split_ifs with h1 h2
    · simpa using hQ s
    · simpa using hQ s
    · have := hstep s h1 (lt_of_not_ge h2)
      have := hQ (step s false)
      have := hQ (step s true)
      norm_num
      linarith
  | succ k ih =>
    have h0 := ih (step s false)
    have h1 := ih (step s true)
    have l0 := stay_le_one step F V lam k (step s false)
    have l1 := stay_le_one step F V lam k (step s true)
    rw [stay_succ]
    split_ifs with hF h2
    · simpa using hQ s
    · simpa using hQ s
    · have := hstep s hF (lt_of_not_ge h2)
      push_cast
      nlinarith

/-- **R2 (hitting-time tail).** -/
theorem one_sub_hit_le (hV : ∀ s, 0 ≤ V s) (hlam : 0 < lam)
    (hsuper : ∀ s, s ∉ F → (V (step s false) + V (step s true)) / 2 ≤ V s)
    (hQ : ∀ s, 0 ≤ Q s)
    (hstep : ∀ s, s ∉ F → V s < lam → (Q (step s false) + Q (step s true)) / 2 + 1 ≤ Q s)
    (k : ℕ) (s : S) : 1 - hit step F k s ≤ V s / lam + Q s / ((k : ℝ) + 1) := by
  have h1 := one_le_hit_add_big_add_stay step F V lam k s
  have h2 := big_mul_le step F V lam hV hsuper hlam k s
  have h3 := stay_mul_le_of_potential step F V lam Q hQ hstep k s
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2' : big step F V lam k s ≤ V s / lam := by
    rw [le_div_iff₀ hlam]; exact h2
  have h3' : stay step F V lam k s ≤ Q s / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ hk]; linarith
  linarith

end rate

/-! ## R3: renewal -/

section renewal
variable [DecidableEq S] (abs : S) (habs : ∀ b, step abs b = abs)
  (F : Set S) [DecidablePred (· ∈ F)] (R : Set S)
include habs

omit [DecidablePred (· ∈ F)] in
/-- Step (a): from `F`, after `K₀` steps the walk is absorbed with probability `≥ c` and
otherwise sits in `R`, where the survival probability over `r` further steps is `≤ H`. -/
theorem one_sub_pAbs_le_of_mem (K₀ : ℕ) (c : ℝ)
    (hF : ∀ f ∈ F, c ≤ pAbs step abs K₀ f)
    (hR : ∀ f ∈ F, ∀ w : List Bool, w.length = K₀ →
      List.foldl step f w ∈ R ∨ List.foldl step f w = abs)
    (r : ℕ) (H : ℝ) (hH : 0 ≤ H) (hrH : ∀ y ∈ R, 1 - pAbs step abs r y ≤ H)
    (f : S) (hf : f ∈ F) :
    1 - pAbs step abs (K₀ + r) f ≤ (1 - c) * H := by
  have h1 := one_sub_pAbs_add_le step abs habs K₀ r f H (fun w hw => by
    rcases hR f hf w hw with h | h
    · exact hrH _ h
    · rw [h, pAbs_abs step abs habs r]; simpa using hH)
  have h2 := hF f hf
  have h3 : H * (1 - pAbs step abs K₀ f) ≤ H * (1 - c) :=
    mul_le_mul_of_nonneg_left (by linarith) hH
  linarith

/-- Step (b): from anywhere, survive `s + K₀ + r` steps only if `F` is not hit within `s`
steps, or it is hit and step (a) applies. -/
theorem one_sub_pAbs_le_one_sub_hit_add (K₀ : ℕ) (c : ℝ) (hc1 : c ≤ 1)
    (hF : ∀ f ∈ F, c ≤ pAbs step abs K₀ f)
    (hR : ∀ f ∈ F, ∀ w : List Bool, w.length = K₀ →
      List.foldl step f w ∈ R ∨ List.foldl step f w = abs)
    (r : ℕ) (H : ℝ) (hH : 0 ≤ H) (hrH : ∀ y ∈ R, 1 - pAbs step abs r y ≤ H)
    (s : ℕ) (x : S) :
    1 - pAbs step abs (s + (K₀ + r)) x ≤ (1 - hit step F s x) + (1 - c) * H := by
  have hcH : 0 ≤ (1 - c) * H := mul_nonneg (by linarith) hH
  induction s generalizing x with
  | zero =>
    rw [Nat.zero_add, hit_zero]
    split_ifs with hx
    · have := one_sub_pAbs_le_of_mem step abs habs F R K₀ c hF hR r H hH hrH x hx
      linarith
    · have := pAbs_nonneg step abs (K₀ + r) x
      linarith
  | succ s ih =>
    have h0 := ih (step x false)
    have h1 := ih (step x true)
    have hjk : s + 1 + (K₀ + r) = (s + (K₀ + r)) + 1 := by omega
    rw [hit_succ]
    split_ifs with hx
    · have := one_sub_pAbs_le_of_mem step abs habs F R K₀ c hF hR r H hH hrH x hx
      have := pAbs_mono step abs habs (Nat.le_add_left (K₀ + r) (s + 1)) x
      linarith
    · rw [hjk, pAbs_succ]; linarith

omit habs in
/-- Pure arithmetic used in the renewal induction. -/
theorem renewal_arith₁ {a B sr st : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hsr : 0 < sr) (hst : 0 < st)
    (h : a * st ≤ sr) : a * a * (B / sr) ≤ a * B / st := by
  rw [← mul_div_assoc, div_le_div_iff₀ hsr hst]
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg ha hB)]

/-- **R3 (renewal).** -/
theorem survival_rate_of_renewal
    (K₀ : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hF : ∀ f ∈ F, c₀ ≤ pAbs step abs K₀ f)
    (hR : ∀ f ∈ F, ∀ w : List Bool, w.length = K₀ →
      List.foldl step f w ∈ R ∨ List.foldl step f w = abs)
    (G₀ : ℝ) (hG₀ : 0 ≤ G₀)
    (htail : ∀ x ∈ R, ∀ t : ℕ, 1 ≤ t → 1 - hit step F t x ≤ G₀ / Real.sqrt t) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, x ∈ R ∨ x ∈ F → ∀ t : ℕ, 1 ≤ t →
      1 - pAbs step abs t x ≤ B / Real.sqrt t := by
  -- normalise the absorption constant to `c ≤ 1`
  obtain ⟨c, hc, hc1, hFc⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ f ∈ F, c ≤ pAbs step abs K₀ f :=
    ⟨min c₀ 1, lt_min hc₀ one_pos, min_le_right _ _,
      fun f hf => (min_le_left _ _).trans (hF f hf)⟩
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = c / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; positivity
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = Real.sqrt (1 - c) := ⟨_, rfl⟩
  have hq0 : 0 ≤ 1 - c := by linarith
  have ha0 : 0 ≤ a := by rw [ha_def]; exact Real.sqrt_nonneg _
  have haa : a * a = 1 - c := by rw [ha_def]; exact Real.mul_self_sqrt hq0
  have ha1 : a < 1 := by
    by_contra hcon
    have hcon' : 1 ≤ a := not_lt.mp hcon
    nlinarith
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hD : 0 < Real.sqrt η * (1 - a) := mul_pos hsη (by linarith)
  obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = ((K₀ : ℝ) + 1) / η := ⟨_, rfl⟩
  have hT : 0 < T := by rw [hT_def]; positivity
  obtain ⟨B₁, hB₁T, hB₁G⟩ :
      ∃ B₁ : ℝ, Real.sqrt T ≤ B₁ ∧ G₀ / (Real.sqrt η * (1 - a)) ≤ B₁ :=
    ⟨max (Real.sqrt T) (G₀ / (Real.sqrt η * (1 - a))), le_max_left _ _, le_max_right _ _⟩
  have hB₁ : 0 < B₁ := lt_of_lt_of_le (Real.sqrt_pos.mpr hT) hB₁T
  have e3 : G₀ / Real.sqrt η ≤ B₁ * (1 - a) := by
    rw [div_le_iff₀ hD] at hB₁G
    rw [div_le_iff₀ hsη]; linarith
  have hu1 : ∀ (t : ℕ) (x : S), 1 - pAbs step abs t x ≤ 1 := fun t x => by
    have := pAbs_nonneg step abs t x; linarith
  -- (c) strong induction on `t` for starting points in `R`
  have hmain : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ R, 1 - pAbs step abs t y ≤ B₁ / Real.sqrt t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht y hy
      have htpos : (0 : ℝ) < t := by exact_mod_cast ht
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
      by_cases hbig : (K₀ : ℝ) + 1 ≤ η * t
      · obtain ⟨s, hs_ge, hs_lt⟩ : ∃ s : ℕ, η * (t : ℝ) ≤ s ∧ (s : ℝ) < η * t + 1 :=
          ⟨⌈η * (t : ℝ)⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩
        have hηt : 0 < η * (t : ℝ) := by positivity
        have hspos : (0 : ℝ) < s := lt_of_lt_of_le hηt hs_ge
        have hs1 : 1 ≤ s := by exact_mod_cast hspos
        have hct : c * (t : ℝ) = 2 * (η * t) := by rw [hη_def]; ring
        have hct' : c * (t : ℝ) ≤ t := by nlinarith
        have hsKt : s + K₀ < t := by
          have : (s : ℝ) + K₀ < t := by linarith
          exact_mod_cast this
        obtain ⟨r, hr⟩ : ∃ r, t = s + (K₀ + r) := ⟨t - s - K₀, by omega⟩
        have hr1 : 1 ≤ r := by omega
        have hrt : r < t := by omega
        have hrR : (t : ℝ) = s + (K₀ + r) := by exact_mod_cast hr
        have hr_ge : (1 - c) * (t : ℝ) ≤ r := by nlinarith
        have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
        have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
        have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
        have hH : 0 ≤ B₁ / Real.sqrt r := by positivity
        have hb := one_sub_pAbs_le_one_sub_hit_add step abs habs F R K₀ c hc1 hFc hR r
          (B₁ / Real.sqrt r) hH (fun z hz => ih r hrt hr1 z hz) s y
        rw [← hr] at hb
        have ht1 := htail y hy s hs1
        have e1 : G₀ / Real.sqrt s ≤ G₀ / (Real.sqrt η * Real.sqrt t) := by
          apply div_le_div_of_nonneg_left hG₀ (by positivity)
          rw [← Real.sqrt_mul hη.le]
          exact Real.sqrt_le_sqrt hs_ge
        have hat : a * Real.sqrt t ≤ Real.sqrt r := by
          rw [ha_def, ← Real.sqrt_mul hq0]
          exact Real.sqrt_le_sqrt hr_ge
        have e2 : (1 - c) * (B₁ / Real.sqrt r) ≤ a * B₁ / Real.sqrt t := by
          rw [← haa]
          exact renewal_arith₁ ha0 hB₁.le hsr hst hat
        have e4 : G₀ / (Real.sqrt η * Real.sqrt t) + a * B₁ / Real.sqrt t
            ≤ B₁ / Real.sqrt t := by
          rw [← div_div, ← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hst.le
        linarith
      · have hbig' : η * (t : ℝ) < (K₀ : ℝ) + 1 := not_le.mp hbig
        have htT : (t : ℝ) ≤ T := by
          rw [hT_def, le_div_iff₀ hη]; linarith
        have h1 : Real.sqrt t ≤ B₁ := (Real.sqrt_le_sqrt htT).trans hB₁T
        have h2 : 1 ≤ B₁ / Real.sqrt t := by
          rw [le_div_iff₀ hst]; linarith
        exact (hu1 t y).trans h2
  -- (d) enlarge the constant to cover starting points in `F`
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsK : 0 ≤ Real.sqrt (2 * (K₀ : ℝ) + 1) := Real.sqrt_nonneg _
  refine ⟨B₁ * Real.sqrt 2 + Real.sqrt (2 * (K₀ : ℝ) + 1), by positivity, ?_⟩
  intro x hx t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hBB : B₁ ≤ B₁ * Real.sqrt 2 + Real.sqrt (2 * (K₀ : ℝ) + 1) := by nlinarith
  rcases hx with hx | hx
  · exact (hmain t ht x hx).trans (div_le_div_of_nonneg_right hBB hst.le)
  · by_cases htK : 2 * K₀ + 1 ≤ t
    · obtain ⟨r, hr⟩ : ∃ r, t = K₀ + r := ⟨t - K₀, by omega⟩
      have hr1 : 1 ≤ r := by omega
      have htr : t ≤ 2 * r := by omega
      have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
      have hH : 0 ≤ B₁ / Real.sqrt r := by positivity
      have ha := one_sub_pAbs_le_of_mem step abs habs F R K₀ c hFc hR r (B₁ / Real.sqrt r) hH
        (fun z hz => hmain r hr1 z hz) x hx
      rw [← hr] at ha
      have h1 : (1 - c) * (B₁ / Real.sqrt r) ≤ B₁ / Real.sqrt r := by nlinarith
      have htr' : (t : ℝ) ≤ 2 * r := by exact_mod_cast htr
      have h2 : Real.sqrt t ≤ Real.sqrt 2 * Real.sqrt r := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt htr'
      have h3 : B₁ / Real.sqrt r ≤ B₁ * Real.sqrt 2 / Real.sqrt t := by
        rw [div_le_div_iff₀ hsr hst]
        nlinarith [mul_le_mul_of_nonneg_left h2 hB₁.le]
      have h4 : B₁ * Real.sqrt 2 / Real.sqrt t
          ≤ (B₁ * Real.sqrt 2 + Real.sqrt (2 * (K₀ : ℝ) + 1)) / Real.sqrt t :=
        div_le_div_of_nonneg_right (by linarith) hst.le
      linarith
    · have htK' : (t : ℝ) ≤ 2 * (K₀ : ℝ) + 1 := by
        have : t ≤ 2 * K₀ + 1 := by omega
        exact_mod_cast this
      have h1 : Real.sqrt t ≤ Real.sqrt (2 * (K₀ : ℝ) + 1) := Real.sqrt_le_sqrt htK'
      have hB0 : 0 ≤ B₁ * Real.sqrt 2 := by positivity
      have h2 : 1 ≤ (B₁ * Real.sqrt 2 + Real.sqrt (2 * (K₀ : ℝ) + 1)) / Real.sqrt t := by
        rw [le_div_iff₀ hst]; linarith
      exact (hu1 t x).trans h2

end renewal

end Coalescence.Generic

#print axioms Coalescence.Generic.stay_mul_le_of_potential
#print axioms Coalescence.Generic.one_sub_hit_le
#print axioms Coalescence.Generic.survival_rate_of_renewal
