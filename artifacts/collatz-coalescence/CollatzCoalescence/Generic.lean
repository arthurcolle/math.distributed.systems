import Mathlib

/-!
# Generic potential theory by induction for a system driven by fair coins

A deterministic system `step : S → Bool → S` is driven by independent fair coins.
Everything is phrased through finite recursions (no measure theory):

* `E step f k s`      : expected value of `f` after `k` coin steps from `s`;
* `pAbs step abs k s` : probability of sitting at `abs` after `k` steps;
* `hit step F k s`    : probability of visiting `F` at some time `≤ k`.

Headline results: `G1_bootstrap`, `G2_lyapunov_hitting`, `G3_assembly`,
`G4_corollary`, `G5_count`.
-/

namespace Coalescence.Generic
open Filter Topology

variable {S : Type*} (step : S → Bool → S)

/-! ## Expectation after `k` fair coin steps -/

/-- Expected value of `f` after `k` fair coin steps. -/
noncomputable def E (f : S → ℝ) : ℕ → S → ℝ
  | 0, s => f s
  | k + 1, s => (E f k (step s false) + E f k (step s true)) / 2

@[simp] theorem E_zero (f : S → ℝ) (s : S) : E step f 0 s = f s := rfl

theorem E_succ (f : S → ℝ) (k : ℕ) (s : S) :
    E step f (k + 1) s = (E step f k (step s false) + E step f k (step s true)) / 2 := rfl

theorem E_mono {f g : S → ℝ} (h : ∀ t, f t ≤ g t) :
    ∀ (k : ℕ) (s : S), E step f k s ≤ E step g k s
  | 0, s => h s
  | k + 1, s => by
    have h0 := E_mono h k (step s false)
    have h1 := E_mono h k (step s true)
    simp only [E_succ]; linarith

theorem E_const (a : ℝ) : ∀ (k : ℕ) (s : S), E step (fun _ => a) k s = a
  | 0, _ => rfl
  | k + 1, s => by
    rw [E_succ, E_const a k, E_const a k]; ring

theorem E_add (f g : S → ℝ) :
    ∀ (k : ℕ) (s : S), E step (fun t => f t + g t) k s = E step f k s + E step g k s
  | 0, _ => rfl
  | k + 1, s => by
    rw [E_succ, E_succ, E_succ, E_add f g k, E_add f g k]; ring

theorem E_sub (f g : S → ℝ) :
    ∀ (k : ℕ) (s : S), E step (fun t => f t - g t) k s = E step f k s - E step g k s
  | 0, _ => rfl
  | k + 1, s => by
    rw [E_succ, E_succ, E_succ, E_sub f g k, E_sub f g k]; ring

theorem E_const_mul (a : ℝ) (f : S → ℝ) :
    ∀ (k : ℕ) (s : S), E step (fun t => a * f t) k s = a * E step f k s
  | 0, _ => rfl
  | k + 1, s => by
    rw [E_succ, E_succ, E_const_mul a f k, E_const_mul a f k]; ring

/-- Markov property: `j + k` steps is `j` steps followed by `k` steps. -/
theorem E_comp (f : S → ℝ) (k : ℕ) :
    ∀ (j : ℕ) (s : S), E step f (j + k) s = E step (E step f k) j s
  | 0, s => by simp
  | j + 1, s => by
    have hjk : j + 1 + k = (j + k) + 1 := by omega
    rw [hjk, E_succ, E_succ, E_comp f k j, E_comp f k j]

/-- Comparison of expectations only needs the comparison at states reachable in `j` steps. -/
theorem E_le_of_words {f g : S → ℝ} :
    ∀ (j : ℕ) (s : S),
      (∀ w : List Bool, w.length = j → f (List.foldl step s w) ≤ g (List.foldl step s w)) →
      E step f j s ≤ E step g j s
  | 0, s, h => by simpa using h [] rfl
  | j + 1, s, h => by
    have h0 := E_le_of_words j (step s false)
      (fun w hw => by simpa using h (false :: w) (by simp [hw]))
    have h1 := E_le_of_words j (step s true)
      (fun w hw => by simpa using h (true :: w) (by simp [hw]))
    simp only [E_succ]; linarith

/-- Counting form of the expectation: `2 ^ k * E` is the sum over all coin words of length `k`. -/
theorem E_mul_two_pow (f : S → ℝ) :
    ∀ (k : ℕ) (s : S),
      E step f k s * 2 ^ k = ∑ w : Fin k → Bool, f (List.foldl step s (List.ofFn w))
  | 0, s => by simp
  | k + 1, s => by
    have h0 := E_mul_two_pow f k (step s false)
    have h1 := E_mul_two_pow f k (step s true)
    have key : ∀ (b : Bool) (y : Fin k → Bool),
        List.foldl step s (List.ofFn ((Fin.consEquiv fun _ : Fin (k + 1) => Bool) (b, y))) =
          List.foldl step (step s b) (List.ofFn y) := by
      intro b y
      show List.foldl step s (List.ofFn (Fin.cons b y : Fin (k + 1) → Bool)) = _
      rw [List.ofFn_cons, List.foldl_cons]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [key]
    rw [← h0, ← h1, E_succ]; ring

/-! ## Absorption probability -/

/-- Probability of being at `abs` after `k` fair coin steps. -/
noncomputable def pAbs [DecidableEq S] (abs : S) (k : ℕ) (s : S) : ℝ :=
  E step (fun t => if t = abs then 1 else 0) k s

section pAbs
variable [DecidableEq S] (abs : S)

theorem pAbs_zero (s : S) : pAbs step abs 0 s = if s = abs then 1 else 0 := rfl

theorem pAbs_succ (k : ℕ) (s : S) :
    pAbs step abs (k + 1) s =
      (pAbs step abs k (step s false) + pAbs step abs k (step s true)) / 2 := rfl

theorem pAbs_nonneg (k : ℕ) (s : S) : 0 ≤ pAbs step abs k s := by
  have h := E_mono step (f := fun _ => (0 : ℝ)) (g := fun t => if t = abs then 1 else 0)
    (fun t => by split_ifs <;> norm_num) k s
  rwa [E_const] at h

theorem pAbs_le_one (k : ℕ) (s : S) : pAbs step abs k s ≤ 1 := by
  have h := E_mono step (f := fun t => if t = abs then (1 : ℝ) else 0) (g := fun _ => (1 : ℝ))
    (fun t => by split_ifs <;> norm_num) k s
  rwa [E_const] at h

variable (habs : ∀ b, step abs b = abs)
include habs

theorem pAbs_abs : ∀ k : ℕ, pAbs step abs k abs = 1
  | 0 => by simp [pAbs_zero]
  | k + 1 => by rw [pAbs_succ, habs, habs, pAbs_abs k]; norm_num

theorem pAbs_le_succ : ∀ (k : ℕ) (s : S), pAbs step abs k s ≤ pAbs step abs (k + 1) s
  | 0, s => by
    rw [pAbs_succ, pAbs_zero]
    split_ifs with hs
    · subst hs
      rw [habs, habs, pAbs_abs step s habs 0]; norm_num
    · have h0 := pAbs_nonneg step abs 0 (step s false)
      have h1 := pAbs_nonneg step abs 0 (step s true)
      linarith
  | k + 1, s => by
    have h0 := pAbs_le_succ k (step s false)
    have h1 := pAbs_le_succ k (step s true)
    rw [pAbs_succ step abs (k + 1) s, pAbs_succ step abs k s]; linarith

theorem pAbs_mono {j k : ℕ} (hjk : j ≤ k) (s : S) : pAbs step abs j s ≤ pAbs step abs k s := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (pAbs_le_succ step abs habs _ s)

/-- One round of the bootstrap: if after `j` steps every reachable state has failure
probability `≤ B` within `K` further steps, then the failure probabilities multiply. -/
theorem one_sub_pAbs_add_le (j K : ℕ) (s : S) (B : ℝ)
    (h : ∀ w : List Bool, w.length = j → 1 - pAbs step abs K (List.foldl step s w) ≤ B) :
    1 - pAbs step abs (j + K) s ≤ B * (1 - pAbs step abs j s) := by
  have e1 : 1 - pAbs step abs (j + K) s = E step (fun t => 1 - pAbs step abs K t) j s := by
    rw [E_sub, E_const]
    unfold pAbs
    rw [E_comp]
  have e2 : E step (fun t => B * (1 - if t = abs then (1 : ℝ) else 0)) j s
      = B * (1 - pAbs step abs j s) := by
    rw [E_const_mul, E_sub, E_const]
    rfl
  rw [e1, ← e2]
  apply E_le_of_words
  intro w hw
  by_cases ht : List.foldl step s w = abs
  · rw [ht, pAbs_abs step abs habs K]; simp
  · simpa [ht] using h w hw

/-- A single horizon `K` works for all states reachable in exactly `j` steps. -/
theorem exists_uniform_horizon (B : ℝ) (h : ∀ s, ∃ k, 1 - pAbs step abs k s ≤ B) :
    ∀ (j : ℕ) (s : S),
      ∃ K, ∀ w : List Bool, w.length = j → 1 - pAbs step abs K (List.foldl step s w) ≤ B
  | 0, s => by
    obtain ⟨K, hK⟩ := h s
    refine ⟨K, fun w hw => ?_⟩
    have hw' : w = [] := List.length_eq_zero_iff.mp hw
    subst hw'
    simpa using hK
  | j + 1, s => by
    obtain ⟨K0, h0⟩ := exists_uniform_horizon B h j (step s false)
    obtain ⟨K1, h1⟩ := exists_uniform_horizon B h j (step s true)
    refine ⟨max K0 K1, fun w hw => ?_⟩
    cases w with
    | nil => simp at hw
    | cons b w' =>
      have hw' : w'.length = j := by simpa using hw
      rw [List.foldl_cons]
      cases b
      · have := pAbs_mono step abs habs (le_max_left K0 K1) (List.foldl step (step s false) w')
        have := h0 w' hw'
        linarith
      · have := pAbs_mono step abs habs (le_max_right K0 K1) (List.foldl step (step s true) w')
        have := h1 w' hw'
        linarith

/-- Geometric decay of the failure probability along a suitable sequence of times. -/
theorem exists_pow_bound (c : ℝ) (hc1 : c ≤ 1) (h : ∀ s, ∃ k, c ≤ pAbs step abs k s) :
    ∀ (n : ℕ) (s : S), ∃ k, 1 - pAbs step abs k s ≤ (1 - c) ^ n
  | 0, s => ⟨0, by have := pAbs_nonneg step abs 0 s; simp only [pow_zero]; linarith⟩
  | n + 1, s => by
    obtain ⟨k₁, hk₁⟩ := h s
    obtain ⟨K, hK⟩ := exists_uniform_horizon step abs habs ((1 - c) ^ n)
      (exists_pow_bound c hc1 h n) k₁ s
    have hB : (0 : ℝ) ≤ (1 - c) ^ n := pow_nonneg (by linarith) n
    refine ⟨k₁ + K, ?_⟩
    calc 1 - pAbs step abs (k₁ + K) s
        ≤ (1 - c) ^ n * (1 - pAbs step abs k₁ s) :=
          one_sub_pAbs_add_le step abs habs k₁ K s _ hK
      _ ≤ (1 - c) ^ n * (1 - c) := mul_le_mul_of_nonneg_left (by linarith) hB
      _ = (1 - c) ^ (n + 1) := by ring

/-- **G1 (bootstrap).** If `abs` is absorbing and every state reaches `abs` with probability
at least a uniform `c > 0` at some time, then the absorption probability tends to `1`. -/
theorem G1_bootstrap (h : ∃ c > 0, ∀ s, ∃ k, c ≤ pAbs step abs k s) :
    ∀ s, Tendsto (fun k => pAbs step abs k s) atTop (𝓝 1) := by
  obtain ⟨c, hc, h⟩ := h
  intro s
  have hc1 : c ≤ 1 := by
    obtain ⟨k, hk⟩ := h s
    exact hk.trans (pAbs_le_one step abs k s)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show 1 - c < 1 by linarith)
  obtain ⟨k₀, hk₀⟩ := exists_pow_bound step abs habs c hc1 h n s
  refine ⟨k₀, fun k hk => ?_⟩
  have h1 := pAbs_mono step abs habs hk s
  have h2 := pAbs_le_one step abs k s
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end pAbs

/-! ## Hitting probabilities -/

/-- Probability of visiting `F` at some time `≤ k`. -/
noncomputable def hit (F : Set S) [DecidablePred (· ∈ F)] : ℕ → S → ℝ
  | 0, s => if s ∈ F then 1 else 0
  | k + 1, s => if s ∈ F then 1 else (hit F k (step s false) + hit F k (step s true)) / 2

/-- Probability of reaching `{lam ≤ V}` at some time `≤ k` without having visited `F`
at or before that time. -/
noncomputable def big (F : Set S) [DecidablePred (· ∈ F)] (V : S → ℝ) (lam : ℝ) : ℕ → S → ℝ
  | 0, t => if t ∈ F then 0 else if lam ≤ V t then 1 else 0
  | k + 1, t => if t ∈ F then 0 else if lam ≤ V t then 1 else
      (big F V lam k (step t false) + big F V lam k (step t true)) / 2

/-- Probability of remaining in `{t ∉ F, V t < lam}` at all times `0..k`. -/
noncomputable def stay (F : Set S) [DecidablePred (· ∈ F)] (V : S → ℝ) (lam : ℝ) : ℕ → S → ℝ
  | 0, t => if t ∈ F then 0 else if lam ≤ V t then 0 else 1
  | k + 1, t => if t ∈ F then 0 else if lam ≤ V t then 0 else
      (stay F V lam k (step t false) + stay F V lam k (step t true)) / 2

section hit
variable (F : Set S) [DecidablePred (· ∈ F)]

theorem hit_zero (s : S) : hit step F 0 s = if s ∈ F then 1 else 0 := rfl

theorem hit_succ (k : ℕ) (s : S) :
    hit step F (k + 1) s =
      if s ∈ F then 1 else (hit step F k (step s false) + hit step F k (step s true)) / 2 := rfl

theorem hit_nonneg : ∀ (k : ℕ) (s : S), 0 ≤ hit step F k s
  | 0, s => by rw [hit_zero]; split_ifs <;> norm_num
  | k + 1, s => by
    have h0 := hit_nonneg k (step s false)
    have h1 := hit_nonneg k (step s true)
    rw [hit_succ]; split_ifs
    · norm_num
    · linarith

section lyapunov
variable (V : S → ℝ) (lam : ℝ)

theorem big_zero (t : S) :
    big step F V lam 0 t = if t ∈ F then 0 else if lam ≤ V t then 1 else 0 := rfl

theorem big_succ (k : ℕ) (t : S) :
    big step F V lam (k + 1) t = if t ∈ F then 0 else if lam ≤ V t then 1 else
      (big step F V lam k (step t false) + big step F V lam k (step t true)) / 2 := rfl

theorem stay_zero (t : S) :
    stay step F V lam 0 t = if t ∈ F then 0 else if lam ≤ V t then 0 else 1 := rfl

theorem stay_succ (k : ℕ) (t : S) :
    stay step F V lam (k + 1) t = if t ∈ F then 0 else if lam ≤ V t then 0 else
      (stay step F V lam k (step t false) + stay step F V lam k (step t true)) / 2 := rfl

/-- At every time, one of the three events (hit `F`, reach `{lam ≤ V}` first, stay) occurs. -/
theorem one_le_hit_add_big_add_stay :
    ∀ (k : ℕ) (t : S), 1 ≤ hit step F k t + big step F V lam k t + stay step F V lam k t
  | 0, t => by
    rw [hit_zero, big_zero, stay_zero]; split_ifs <;> norm_num
  | k + 1, t => by
    have h0 := one_le_hit_add_big_add_stay k (step t false)
    have h1 := one_le_hit_add_big_add_stay k (step t true)
    have g0 := hit_nonneg step F k (step t false)
    have g1 := hit_nonneg step F k (step t true)
    rw [hit_succ, big_succ, stay_succ]; split_ifs
    · norm_num
    · linarith
    · linarith

/-- Maximal inequality for the nonnegative supermartingale `V` (stopped at `F`). -/
theorem big_mul_le (hV : ∀ s, 0 ≤ V s)
    (hsuper : ∀ s, s ∉ F → (V (step s false) + V (step s true)) / 2 ≤ V s) (hlam : 0 < lam) :
    ∀ (k : ℕ) (t : S), big step F V lam k t * lam ≤ V t
  | 0, t => by
    have := hV t
    rw [big_zero]; split_ifs with h1 h2
    · linarith
    · linarith
    · linarith
  | k + 1, t => by
    have h0 := big_mul_le hV hsuper hlam k (step t false)
    have h1 := big_mul_le hV hsuper hlam k (step t true)
    have := hV t
    rw [big_succ]; split_ifs with hF h2
    · linarith
    · linarith
    · have := hsuper t hF
      linarith

theorem stay_nonneg : ∀ (k : ℕ) (t : S), 0 ≤ stay step F V lam k t
  | 0, t => by rw [stay_zero]; split_ifs <;> norm_num
  | k + 1, t => by
    have h0 := stay_nonneg k (step t false)
    have h1 := stay_nonneg k (step t true)
    rw [stay_succ]; split_ifs
    · norm_num
    · norm_num
    · linarith

theorem stay_le_one : ∀ (k : ℕ) (t : S), stay step F V lam k t ≤ 1
  | 0, t => by rw [stay_zero]; split_ifs <;> norm_num
  | k + 1, t => by
    have h0 := stay_le_one k (step t false)
    have h1 := stay_le_one k (step t true)
    rw [stay_succ]; split_ifs
    · norm_num
    · norm_num
    · linarith

theorem stay_eq_zero_of_exit (k : ℕ) (t : S) (h : t ∈ F ∨ lam ≤ V t) :
    stay step F V lam k t = 0 := by
  cases k with
  | zero =>
    rw [stay_zero]; split_ifs with h1 h2
    · rfl
    · rfl
    · exact absurd h (by tauto)
  | succ k =>
    rw [stay_succ]; split_ifs with h1 h2
    · rfl
    · rfl
    · exact absurd h (by tauto)

theorem stay_succ_le : ∀ (k : ℕ) (t : S), stay step F V lam (k + 1) t ≤ stay step F V lam k t
  | 0, t => by
    have h0 := stay_le_one step F V lam 0 (step t false)
    have h1 := stay_le_one step F V lam 0 (step t true)
    rw [stay_succ step F V lam 0 t, stay_zero step F V lam t]; split_ifs
    · exact le_rfl
    · exact le_rfl
    · linarith
  | k + 1, t => by
    have h0 := stay_succ_le k (step t false)
    have h1 := stay_succ_le k (step t true)
    rw [stay_succ step F V lam (k + 1) t, stay_succ step F V lam k t]; split_ifs
    · exact le_rfl
    · exact le_rfl
    · linarith

theorem stay_anti {j k : ℕ} (hjk : j ≤ k) (t : S) :
    stay step F V lam k t ≤ stay step F V lam j t := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => exact (stay_succ_le step F V lam _ t).trans ih

/-- If the word `w` leads out of `{t ∉ F, V t < lam}`, staying for `|w|` steps fails with
probability at least `2 ^ (-|w|)`. -/
theorem stay_le_of_word :
    ∀ (w : List Bool) (t : S),
      (List.foldl step t w ∈ F ∨ lam ≤ V (List.foldl step t w)) →
      stay step F V lam w.length t ≤ 1 - (1 / 2) ^ w.length
  | [], t, h => by
    rw [stay_eq_zero_of_exit step F V lam _ t (by simpa using h)]; simp
  | b :: w, t, h => by
    have hrec := stay_le_of_word w (step t b) (by simpa using h)
    have h0 := stay_le_one step F V lam w.length (step t false)
    have h1 := stay_le_one step F V lam w.length (step t true)
    have hpos : (0 : ℝ) < (1 / 2) ^ w.length := by positivity
    have hle : ((1 : ℝ) / 2) ^ w.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [List.length_cons, stay_succ step F V lam w.length t, pow_succ]
    split_ifs
    · linarith
    · linarith
    · cases b <;> linarith

/-- Sub-multiplicativity of the staying probability. -/
theorem stay_add_le (k : ℕ) (q : ℝ) (hq : ∀ u, stay step F V lam k u ≤ q) :
    ∀ (j : ℕ) (t : S), stay step F V lam (j + k) t ≤ q * stay step F V lam j t
  | 0, t => by
    rw [Nat.zero_add, stay_zero]
    split_ifs with h1 h2
    · rw [stay_eq_zero_of_exit step F V lam k t (Or.inl h1)]; simp
    · rw [stay_eq_zero_of_exit step F V lam k t (Or.inr h2)]; simp
    · simpa using hq t
  | j + 1, t => by
    have h0 := stay_add_le k q hq j (step t false)
    have h1 := stay_add_le k q hq j (step t true)
    have hjk : j + 1 + k = (j + k) + 1 := by omega
    rw [hjk, stay_succ step F V lam (j + k) t, stay_succ step F V lam j t]
    split_ifs
    · simp
    · simp
    · linarith

theorem stay_mul_le (L : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : ∀ u, stay step F V lam L u ≤ q) :
    ∀ (n : ℕ) (t : S), stay step F V lam (n * L) t ≤ q ^ n
  | 0, t => by simpa using stay_le_one step F V lam 0 t
  | n + 1, t => by
    have h1 := stay_add_le step F V lam L q hq (n * L) t
    have h2 := stay_mul_le L q hq0 hq n t
    rw [Nat.succ_mul, pow_succ]
    calc stay step F V lam (n * L + L) t ≤ q * stay step F V lam (n * L) t := h1
      _ ≤ q * q ^ n := mul_le_mul_of_nonneg_left h2 hq0
      _ = q ^ n * q := by ring

end lyapunov

/-- **G2 (Lyapunov ⇒ hitting).** A nonnegative function that is superharmonic off `F`,
together with a uniform escape property from every sublevel set, forces `F` to be hit
with probability at least `1/2` from every starting state. -/
theorem G2_lyapunov_hitting (V : S → ℝ) (hV : ∀ s, 0 ≤ V s)
    (hsuper : ∀ s, s ∉ F → (V (step s false) + V (step s true)) / 2 ≤ V s)
    (hesc : ∀ lam : ℝ, ∃ L : ℕ, ∀ s, s ∉ F → V s < lam →
      ∃ w : List Bool, w.length ≤ L ∧
        (List.foldl step s w ∈ F ∨ lam ≤ V (List.foldl step s w))) :
    ∀ s, ∃ k, 1 / 2 ≤ hit step F k s := by
  intro s
  by_cases hs : s ∈ F
  · exact ⟨0, by rw [hit_zero, if_pos hs]; norm_num⟩
  set lam : ℝ := 4 * V s + 1 with hlam_def
  have hVs := hV s
  have hlam : 0 < lam := by linarith
  obtain ⟨L, hL⟩ := hesc lam
  set q : ℝ := 1 - (1 / 2) ^ L with hq_def
  have hpowL : (0 : ℝ) < (1 / 2) ^ L := by positivity
  have hpowL1 : ((1 : ℝ) / 2) ^ L ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq0 : 0 ≤ q := by linarith
  have hq1 : q < 1 := by linarith
  have hstayL : ∀ u, stay step F V lam L u ≤ q := by
    intro u
    by_cases hu : u ∈ F ∨ lam ≤ V u
    · rw [stay_eq_zero_of_exit step F V lam L u hu]; exact hq0
    · have huF : u ∉ F := fun h => hu (Or.inl h)
      have huV : V u < lam := lt_of_not_ge (fun h => hu (Or.inr h))
      obtain ⟨w, hwL, hw⟩ := hL u huF huV
      have h1 := stay_le_of_word step F V lam w u hw
      have h2 := stay_anti step F V lam hwL u
      have h3 : ((1 : ℝ) / 2) ^ L ≤ (1 / 2) ^ w.length :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hwL
      linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 4 by norm_num) hq1
  refine ⟨n * L, ?_⟩
  have hsum := one_le_hit_add_big_add_stay step F V lam (n * L) s
  have hstay := stay_mul_le step F V lam L q hq0 hstayL n s
  have hbig := big_mul_le step F V lam hV hsuper hlam (n * L) s
  have hbig' : big step F V lam (n * L) s ≤ 1 / 4 :=
    le_of_mul_le_mul_right (by linarith) hlam
  linarith

/-- A uniform lower bound for absorption from `F` propagates through the hitting time. -/
theorem mul_hit_le_pAbs [DecidableEq S] (abs : S) (habs : ∀ b, step abs b = abs)
    (K : ℕ) (c₀ : ℝ) (hc₀ : 0 ≤ c₀) (hF : ∀ f ∈ F, c₀ ≤ pAbs step abs K f) :
    ∀ (k : ℕ) (s : S), c₀ * hit step F k s ≤ pAbs step abs (k + K) s
  | 0, s => by
    rw [hit_zero, Nat.zero_add]
    split_ifs with hs
    · simpa using hF s hs
    · simpa using pAbs_nonneg step abs K s
  | k + 1, s => by
    have h0 := mul_hit_le_pAbs abs habs K c₀ hc₀ hF k (step s false)
    have h1 := mul_hit_le_pAbs abs habs K c₀ hc₀ hF k (step s true)
    have hjk : k + 1 + K = (k + K) + 1 := by omega
    rw [hit_succ]
    split_ifs with hs
    · have := pAbs_mono step abs habs (Nat.le_add_left K (k + 1)) s
      have := hF s hs
      linarith
    · rw [hjk, pAbs_succ]; linarith

end hit

/-- Finitely many states with positive absorption probability admit a common time and a
common positive lower bound. -/
theorem exists_uniform_on_finset [DecidableEq S] (abs : S) (habs : ∀ b, step abs b = abs)
    (F : Finset S) (hF : ∀ f ∈ F, ∃ k, 0 < pAbs step abs k f) :
    ∃ (K : ℕ) (c₀ : ℝ), 0 < c₀ ∧ ∀ f ∈ F, c₀ ≤ pAbs step abs K f := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, 1, one_pos, by simp⟩
  | insert a F' _ ih =>
    obtain ⟨K', c', hc', hK'⟩ := ih (fun f hf => hF f (Finset.mem_insert_of_mem hf))
    obtain ⟨k, hk⟩ := hF a (Finset.mem_insert_self a F')
    refine ⟨max K' k, min c' (pAbs step abs k a), lt_min hc' hk, fun f hf => ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · exact (min_le_right _ _).trans (pAbs_mono step abs habs (le_max_right K' k) f)
    · exact (min_le_left _ _).trans
        ((hK' f hf').trans (pAbs_mono step abs habs (le_max_left K' k) f))

/-- **G3 (assembly).** If a finite set `F` is hit with probability `≥ 1/2` from everywhere and
every point of `F` is absorbed with positive probability, then absorption has a uniform
positive lower bound. -/
theorem G3_assembly [DecidableEq S] (F : Finset S) [DecidablePred (· ∈ (↑F : Set S))]
    (abs : S) (habs : ∀ b, step abs b = abs)
    (hF : ∀ f ∈ F, ∃ k, 0 < pAbs step abs k f)
    (hhit : ∀ s, ∃ k, 1 / 2 ≤ hit step (↑F) k s) :
    ∃ c > 0, ∀ s, ∃ k, c ≤ pAbs step abs k s := by
  obtain ⟨K, c₀, hc₀, hK⟩ := exists_uniform_on_finset step abs habs F hF
  refine ⟨c₀ / 2, by linarith, fun s => ?_⟩
  obtain ⟨k, hk⟩ := hhit s
  refine ⟨k + K, ?_⟩
  have h := mul_hit_le_pAbs step (↑F : Set S) abs habs K c₀ hc₀.le
    (fun f hf => hK f (Finset.mem_coe.mp hf)) k s
  have : c₀ * (1 / 2) ≤ c₀ * hit step (↑F : Set S) k s :=
    mul_le_mul_of_nonneg_left hk hc₀.le
  linarith

/-- **G4 (corollary).** Lyapunov function + escape + positive absorption from the finite set
`F` + `abs` absorbing imply that the absorption probability tends to `1`. -/
theorem G4_corollary [DecidableEq S] (F : Finset S) [DecidablePred (· ∈ (↑F : Set S))]
    (abs : S) (habs : ∀ b, step abs b = abs)
    (hF : ∀ f ∈ F, ∃ k, 0 < pAbs step abs k f)
    (V : S → ℝ) (hV : ∀ s, 0 ≤ V s)
    (hsuper : ∀ s, s ∉ (↑F : Set S) → (V (step s false) + V (step s true)) / 2 ≤ V s)
    (hesc : ∀ lam : ℝ, ∃ L : ℕ, ∀ s, s ∉ (↑F : Set S) → V s < lam →
      ∃ w : List Bool, w.length ≤ L ∧
        (List.foldl step s w ∈ (↑F : Set S) ∨ lam ≤ V (List.foldl step s w))) :
    ∀ s, Tendsto (fun k => pAbs step abs k s) atTop (𝓝 1) :=
  G1_bootstrap step abs habs
    (G3_assembly step F abs habs hF (G2_lyapunov_hitting step (↑F : Set S) V hV hsuper hesc))

/-- **G5 (counting interpretation).** `2 ^ k * pAbs k s` is the number of coin words
`w : Fin k → Bool` that drive `s` to `abs`. -/
theorem G5_count [DecidableEq S] (abs : S) (k : ℕ) (s : S) :
    pAbs step abs k s * 2 ^ k =
      (((Finset.univ : Finset (Fin k → Bool)).filter
        (fun w => List.foldl step s (List.ofFn w) = abs)).card : ℝ) := by
  unfold pAbs
  rw [E_mul_two_pow, Finset.sum_boole]

/-- With `DecidableEq S`, the coercion of a `Finset` has a canonical membership decision
procedure, so `hit step (↑F)` and the theorems above can be used without extra instances. -/
example [DecidableEq S] (F : Finset S) (abs : S) (habs : ∀ b, step abs b = abs)
    (hF : ∀ f ∈ F, ∃ k, 0 < pAbs step abs k f)
    (hhit : ∀ s, ∃ k, 1 / 2 ≤ hit step (↑F) k s) :
    ∃ c > 0, ∀ s, ∃ k, c ≤ pAbs step abs k s :=
  G3_assembly step F abs habs hF hhit

end Coalescence.Generic

#print axioms Coalescence.Generic.G1_bootstrap
#print axioms Coalescence.Generic.G2_lyapunov_hitting
#print axioms Coalescence.Generic.G3_assembly
#print axioms Coalescence.Generic.G4_corollary
#print axioms Coalescence.Generic.G5_count
