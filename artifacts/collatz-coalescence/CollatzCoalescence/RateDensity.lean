import CollatzCoalescence.RateMain
import CollatzCoalescence.Gao

/-!
# The rate, as a statement about natural density

`unmerged_density_rate`: there are constants `0 < c₁`, `0 < c₂` such that for every `k ≥ 1` the set
of `n` with `Tn^[k] n ≠ Tn^[k] (n + 1)` has lower and upper natural density between `c₁ / √k` and
`c₂ / √k`.

The residue classes mod `2^k` split into merged ones, on which `Tn^[k] n = Tn^[k] (n + 1)` holds
identically, and unmerged ones, on which it holds for at most one `n` (both sides are affine in the
class parameter).  The number of unmerged classes is `survival_rate`.
-/

namespace Coalescence
open Generic

/-- If `G` is a set of residues modulo `m`, at most `G.card * (N / m + 1)` of the `n < N` reduce
into `G`. -/
theorem card_filter_mod_le (m : ℕ) (G : Finset ℕ) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % m ∈ G)).card ≤ G.card * (N / m + 1) := by
  have h : ((Finset.range N).filter (fun n => n % m ∈ G)).card ≤
      (G ×ˢ Finset.range (N / m + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n % m, n / m))
    · intro n hn
      have hn' : n < N ∧ n % m ∈ G := by simpa using hn
      have hlt : n / m < N / m + 1 := Nat.lt_succ_of_le (Nat.div_le_div_right hn'.1.le)
      have hgoal : (n % m, n / m) ∈ G ×ˢ Finset.range (N / m + 1) := by
        rw [Finset.mem_product, Finset.mem_range]
        exact ⟨hn'.2, hlt⟩
      exact hgoal
    · intro a _ b _ heq
      have heq' : (a % m, a / m) = (b % m, b / m) := heq
      have h1 : a % m = b % m := congrArg Prod.fst heq'
      have h2 : a / m = b / m := congrArg Prod.snd heq'
      rw [← Nat.mod_add_div a m, ← Nat.mod_add_div b m, h1, h2]
  rwa [Finset.card_product, Finset.card_range] at h

/-- Two-sided counting on residue classes: if `P` forces the residue into `U`, and on each class
of `U` the property `P` fails at most once, then the number of `n < N` with `P n` is
`U.card * (N / m)` up to an error of `U.card`. -/
theorem card_filter_bounds_of_classes (P : ℕ → Prop) [DecidablePred P] (m : ℕ) (hm : 0 < m)
    (U : Finset ℕ) (hU : ∀ g ∈ U, g < m) (hsub : ∀ n : ℕ, P n → n % m ∈ U)
    (hinj : ∀ n₁ n₂ : ℕ, n₁ % m ∈ U → n₁ % m = n₂ % m → ¬ P n₁ → ¬ P n₂ → n₁ = n₂) (N : ℕ) :
    ((Finset.range N).filter P).card ≤ U.card * (N / m + 1) ∧
      U.card * (N / m) ≤ ((Finset.range N).filter P).card + U.card := by
  constructor
  · refine (Finset.card_le_card ?_).trans (card_filter_mod_le m U N)
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hsub n hn.2⟩
  · have h1 := card_filter_mod_ge m hm U hU N
    have h2 : (((Finset.range N).filter (fun n => n % m ∈ U)).filter (fun n => ¬ P n)).card
        ≤ U.card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => n % m)
      · intro n hn
        have hn1 := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
        exact (Finset.mem_filter.mp hn1.1).2
      · intro a ha b hb heq
        have ha1 := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
        have hb1 := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        exact hinj a b (Finset.mem_filter.mp ha1.1).2 heq ha1.2 hb1.2
    have h3 := Finset.card_filter_add_card_filter_not
      (s := (Finset.range N).filter (fun n => n % m ∈ U)) P
    have h4 : (((Finset.range N).filter (fun n => n % m ∈ U)).filter P).card
        ≤ ((Finset.range N).filter P).card := by
      apply Finset.card_le_card
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨(Finset.mem_filter.mp hn.1).1, hn.2⟩
    omega

/-- On a merged class the orbits of `n` and `n + 1` agree at time `k`. -/
theorem Tn_iterate_eq_of_mem_merged (k n : ℕ) (hn : n % 2 ^ k ∈ merged ⟨0, 1⟩ k) :
    Tn^[k] n = Tn^[k] (n + 1) := by
  have H := merged_class k n 1 (by rw [Nat.cast_one]; exact hn) 0
  simp only [mul_zero, add_zero] at H
  exact Tn_iterate_eq_of_T k n 1 H

/-- On an unmerged class the orbits of `n` and `n + 1` agree at time `k` for at most one `n`:
both `T^[k] (r + 2^k t)` and `T^[k] (r + 1 + 2^k t)` are affine in `t`. -/
theorem eq_of_unmerged_class (k n₁ n₂ : ℕ) (hU : n₁ % 2 ^ k ∉ merged ⟨0, 1⟩ k)
    (hmod : n₁ % 2 ^ k = n₂ % 2 ^ k)
    (h₁ : Tn^[k] n₁ = Tn^[k] (n₁ + 1)) (h₂ : Tn^[k] n₂ = Tn^[k] (n₂ + 1)) : n₁ = n₂ := by
  by_contra hne
  apply hU
  have hZ : ∀ n : ℕ, Tn^[k] n = Tn^[k] (n + 1) → T^[k] (n : ℤ) = T^[k] ((n : ℤ) + 1) := by
    intro n h
    have e : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, T_iterate_natCast, T_iterate_natCast, h]
  have d₁ : ((n₁ % 2 ^ k : ℕ) : ℤ) + 2 ^ k * ((n₁ / 2 ^ k : ℕ) : ℤ) = (n₁ : ℤ) := by
    have := Nat.mod_add_div n₁ (2 ^ k)
    exact_mod_cast this
  have d₂ : ((n₁ % 2 ^ k : ℕ) : ℤ) + 2 ^ k * ((n₂ / 2 ^ k : ℕ) : ℤ) = (n₂ : ℤ) := by
    have := Nat.mod_add_div n₂ (2 ^ k)
    rw [← hmod] at this
    exact_mod_cast this
  have hq : ((n₁ / 2 ^ k : ℕ) : ℤ) ≠ ((n₂ / 2 ^ k : ℕ) : ℤ) := by
    intro h
    apply hne
    have h' : n₁ / 2 ^ k = n₂ / 2 ^ k := by exact_mod_cast h
    rw [← Nat.mod_add_div n₁ (2 ^ k), ← Nat.mod_add_div n₂ (2 ^ k), hmod, h']
  have g₁ := hZ n₁ h₁
  have g₂ := hZ n₂ h₂
  rw [← d₁] at g₁
  rw [← d₂] at g₂
  have hlt : n₁ % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  rw [mem_merged]
  refine ⟨hlt, ?_⟩
  generalize ((n₁ % 2 ^ k : ℕ) : ℤ) = r at g₁ g₂ ⊢
  generalize ((n₁ / 2 ^ k : ℕ) : ℤ) = q₁ at g₁ hq
  generalize ((n₂ / 2 ^ k : ℕ) : ℤ) = q₂ at g₂ hq
  have e1 : ∀ t : ℤ, T^[k] (r + 2 ^ k * t) = T^[k] r + 3 ^ oddCount k r * t :=
    T_iterate_add k r
  have e2 : ∀ t : ℤ, T^[k] (r + 2 ^ k * t + 1)
      = T^[k] (r + 1) + 3 ^ oddCount k (r + 1) * t := by
    intro t
    rw [← T_iterate_add]
    congr 1
    ring
  rw [e1, e2] at g₁ g₂
  have hβ : ((3 : ℤ) ^ oddCount k r - 3 ^ oddCount k (r + 1)) * (q₁ - q₂) = 0 := by
    linear_combination g₁ - g₂
  have hβ' := (mul_eq_zero.mp hβ).resolve_right (sub_ne_zero.mpr hq)
  intro t
  show T^[k] (r + 2 ^ k * t) = T^[k] (3 ^ 0 * (r + 2 ^ k * t) + 1)
  rw [pow_zero, one_mul, e1, e2]
  linear_combination g₁ + (t - q₁) * hβ'

open Classical in
/-- For each `k ≥ 1`, the integers `n` whose orbit has not met that of `n + 1` after `k` steps
have lower and upper natural density between `c₁ / √k` and `c₂ / √k`. -/
theorem unmerged_density_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (c₁ / Real.sqrt k - ε) * (N : ℝ) ≤
          (((Finset.range N).filter fun n : ℕ => Tn^[k] n ≠ Tn^[k] (n + 1)).card : ℝ) ∧
        (((Finset.range N).filter fun n : ℕ => Tn^[k] n ≠ Tn^[k] (n + 1)).card : ℝ) ≤
          (c₂ / Real.sqrt k + ε) * (N : ℝ) := by
  obtain ⟨c₁, c₂, h1, h2, h⟩ := survival_rate
  refine ⟨c₁, c₂, h1, h2, fun k hk ε hε => ⟨⌈2 * (2 : ℝ) ^ k / ε⌉₊, fun N hN => ?_⟩⟩
  obtain ⟨hlo, hhi⟩ := h k hk
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  have hL : 0 < c₁ / Real.sqrt k := div_pos h1 hsk
  -- the unmerged classes
  have hMg : merged ⟨0, 1⟩ k ⊆ Finset.range (2 ^ k) := by
    unfold merged
    exact Finset.filter_subset _ _
  have hUcard : ((Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k).card : ℝ)
      = (1 - pAbs step absorbed k ⟨0, 1⟩) * 2 ^ k := by
    have h3 := Finset.card_sdiff_add_card_eq_card hMg
    rw [Finset.card_range] at h3
    have h4 : ((Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k).card : ℝ)
        + ((merged ⟨0, 1⟩ k).card : ℝ) = (2 : ℝ) ^ k := by exact_mod_cast h3
    rw [card_merged_eq] at h4
    linarith
  have hUle : (Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k).card ≤ 2 ^ k := by
    have h3 := Finset.card_sdiff_add_card_eq_card hMg
    rw [Finset.card_range] at h3
    omega
  -- counting
  have hnat := card_filter_bounds_of_classes (fun n : ℕ => Tn^[k] n ≠ Tn^[k] (n + 1)) (2 ^ k)
    (by positivity) (Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k)
    (fun g hg => Finset.mem_range.mp (Finset.mem_sdiff.mp hg).1)
    (fun n hn => Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)),
      fun hmem => hn (Tn_iterate_eq_of_mem_merged k n hmem)⟩)
    (fun n₁ n₂ hmem hmod hn₁ hn₂ => eq_of_unmerged_class k n₁ n₂ (Finset.mem_sdiff.mp hmem).2 hmod
      (not_not.mp hn₁) (not_not.mp hn₂)) N
  obtain ⟨hup, hlow⟩ := hnat
  have hupR : (((Finset.range N).filter fun n : ℕ => Tn^[k] n ≠ Tn^[k] (n + 1)).card : ℝ) ≤
      ((Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k).card : ℝ) * (((N / 2 ^ k : ℕ) : ℝ) + 1) := by
    exact_mod_cast hup
  have hlowR : ((Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k).card : ℝ) * ((N / 2 ^ k : ℕ) : ℝ) ≤
      (((Finset.range N).filter fun n : ℕ => Tn^[k] n ≠ Tn^[k] (n + 1)).card : ℝ)
        + ((Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k).card : ℝ) := by
    exact_mod_cast hlow
  have hUleR : ((Finset.range (2 ^ k) \ merged ⟨0, 1⟩ k).card : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hUle
  rw [hUcard] at hupR hlowR hUleR
  -- the threshold
  have hNreal : 2 * (2 : ℝ) ^ k / ε ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN2 : 2 * (2 : ℝ) ^ k ≤ ε * N := by
    rw [div_le_iff₀ hε] at hNreal
    linarith
  have hdiv1 : (2 : ℝ) ^ k * ((N / 2 ^ k : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hle : 2 ^ k * (N / 2 ^ k) ≤ N := Nat.mul_div_le N (2 ^ k)
    have hle' : ((2 ^ k * (N / 2 ^ k) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hle'
    exact hle'
  have hdiv2 : (N : ℝ) ≤ (2 : ℝ) ^ k * ((N / 2 ^ k : ℕ) : ℝ) + (2 : ℝ) ^ k := by
    have hlt : N < 2 ^ k * (N / 2 ^ k + 1) := Nat.lt_mul_div_succ N (by positivity)
    have hlt' : (N : ℝ) < ((2 ^ k * (N / 2 ^ k + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at hlt'
    linarith
  have hn0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hM : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  generalize ((N / 2 ^ k : ℕ) : ℝ) = q at hupR hlowR hdiv1 hdiv2
  generalize (((Finset.range N).filter fun n : ℕ => Tn^[k] n ≠ Tn^[k] (n + 1)).card : ℝ) = c
    at hupR hlowR ⊢
  generalize (1 - pAbs step absorbed k ⟨0, 1⟩) = d at hlo hhi hupR hlowR hUleR
  generalize c₁ / Real.sqrt k = L at hlo hL ⊢
  generalize c₂ / Real.sqrt k = R at hhi ⊢
  generalize (2 : ℝ) ^ k = M at hupR hlowR hUleR hN2 hdiv1 hdiv2 hM
  generalize (N : ℝ) = n at hN2 hdiv1 hdiv2 hn0 ⊢
  have hd0 : 0 ≤ d := hL.le.trans hlo
  have p1 : d * (n - M) ≤ d * (M * q) := mul_le_mul_of_nonneg_left (by linarith) hd0
  have p2 : L * n ≤ d * n := mul_le_mul_of_nonneg_right hlo hn0
  have p3 : d * (M * q) ≤ d * n := mul_le_mul_of_nonneg_left hdiv1 hd0
  have p4 : d * n ≤ R * n := mul_le_mul_of_nonneg_right hhi hn0
  constructor
  · nlinarith
  · nlinarith

#print axioms unmerged_density_rate

end Coalescence
