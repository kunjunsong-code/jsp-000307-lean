/-!
# JSP-000307 — Lean 4.20.0, no Mathlib
Counterexample: n=13: P(13)=13 > P(14)=7 > P(15)=5.
Helpers copied verbatim from JSP000301.lean (same repo, verified build).
-/

set_option maxRecDepth 20000

def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
def IsLPF (n p : Nat) : Prop := PrimeP p ∧ p ∣ n ∧ ∀ q, PrimeP q → q ∣ n → q ≤ p

theorem mod_eq_zero_of_dvd {m n : Nat} (h : m ∣ n) : n % m = 0 := by
  cases h with | intro k hk => rw [hk]; exact Nat.mul_mod_right m k

private theorem le_of_dvd_pos {m n : Nat} (hn : 0 < n) (h : m ∣ n) : m ≤ n := by
  cases h with
  | intro k hk =>
    cases Nat.eq_zero_or_pos k with
    | inl hk0 => rw [hk, hk0, Nat.mul_zero] at hn; exact absurd hn (Nat.lt_irrefl 0)
    | inr hk0 => rw [hk]; exact Nat.le_mul_of_pos_right m hk0

theorem primeP_of_cert (p : Nat) (h2 : 2 ≤ p)
    (h : ((List.range (p + 1)).all fun m =>
      decide (p % m ≠ 0) || decide (m = 1) || decide (m = p)) = true) :
    PrimeP p := by
  refine ⟨h2, fun m hm => ?_⟩
  have hmp : m ≤ p := le_of_dvd_pos (by omega) hm
  have hall := List.all_eq_true.mp h m (by rw [List.mem_range]; omega)
  have hmod : p % m = 0 := mod_eq_zero_of_dvd hm
  rw [Bool.or_eq_true] at hall
  cases hall with
  | inr hpq => exact Or.inr (decide_eq_true_eq.mp hpq)
  | inl hab =>
    rw [Bool.or_eq_true] at hab
    cases hab with
    | inl hne => exact absurd hmod (decide_eq_true_eq.mp hne)
    | inr h1 => exact Or.inl (decide_eq_true_eq.mp h1)

theorem primeP_2  : PrimeP 2  := primeP_of_cert 2  (by decide) (by decide)
theorem primeP_3  : PrimeP 3  := primeP_of_cert 3  (by decide) (by decide)
theorem primeP_5  : PrimeP 5  := primeP_of_cert 5  (by decide) (by decide)
theorem primeP_7  : PrimeP 7  := primeP_of_cert 7  (by decide) (by decide)
theorem primeP_13 : PrimeP 13 := primeP_of_cert 13 (by decide) (by decide)

theorem not_primeP_14 : ¬ PrimeP 14 := by
  intro h
  have hdiv : 2 ∣ 14 := by decide
  have h2 : 2 = 1 ∨ 2 = 14 := h.2 2 hdiv
  simpa using h2

theorem not_primeP_15 : ¬ PrimeP 15 := by
  intro h
  have hdiv : 3 ∣ 15 := by decide
  have h2 : 3 = 1 ∨ 3 = 15 := h.2 3 hdiv
  simpa using h2

theorem lpf_13 : IsLPF 13 13 := by
  refine ⟨primeP_13, by decide, fun q hq hqd => ?_⟩
  exact le_of_dvd_pos (by decide) hqd

private theorem q_cases_14 (q : Nat) (hq2 : 2 ≤ q) (hqd : q ∣ 14) :
    q = 2 ∨ q = 7 ∨ q = 14 := by
  have hle : q ≤ 14 := le_of_dvd_pos (by decide) hqd
  by_cases h2 : q = 2
  · exact Or.inl h2
  by_cases h3 : q = 3
  · exfalso
    have hf : 3 ∣ 14 := by rwa [←h3]
    simpa using hf
  by_cases h4 : q = 4
  · exfalso
    have hf : 4 ∣ 14 := by rwa [←h4]
    simpa using hf
  by_cases h5 : q = 5
  · exfalso
    have hf : 5 ∣ 14 := by rwa [←h5]
    simpa using hf
  by_cases h6 : q = 6
  · exfalso
    have hf : 6 ∣ 14 := by rwa [←h6]
    simpa using hf
  by_cases h7 : q = 7
  · exact Or.inr (Or.inl h7)
  by_cases h8 : q = 8
  · exfalso
    have hf : 8 ∣ 14 := by rwa [←h8]
    simpa using hf
  by_cases h9 : q = 9
  · exfalso
    have hf : 9 ∣ 14 := by rwa [←h9]
    simpa using hf
  by_cases h10 : q = 10
  · exfalso
    have hf : 10 ∣ 14 := by rwa [←h10]
    simpa using hf
  by_cases h11 : q = 11
  · exfalso
    have hf : 11 ∣ 14 := by rwa [←h11]
    simpa using hf
  by_cases h12 : q = 12
  · exfalso
    have hf : 12 ∣ 14 := by rwa [←h12]
    simpa using hf
  by_cases h13 : q = 13
  · exfalso
    have hf : 13 ∣ 14 := by rwa [←h13]
    simpa using hf
  by_cases h14 : q = 14
  · exact Or.inr (Or.inr h14)
  omega

private theorem q_cases_15 (q : Nat) (hq2 : 2 ≤ q) (hqd : q ∣ 15) :
    q = 3 ∨ q = 5 ∨ q = 15 := by
  have hle : q ≤ 15 := le_of_dvd_pos (by decide) hqd
  by_cases h2 : q = 2
  · exfalso
    have hf : 2 ∣ 15 := by rwa [←h2]
    simpa using hf
  by_cases h3 : q = 3
  · exact Or.inl h3
  by_cases h4 : q = 4
  · exfalso
    have hf : 4 ∣ 15 := by rwa [←h4]
    simpa using hf
  by_cases h5 : q = 5
  · exact Or.inr (Or.inl h5)
  by_cases h6 : q = 6
  · exfalso
    have hf : 6 ∣ 15 := by rwa [←h6]
    simpa using hf
  by_cases h7 : q = 7
  · exfalso
    have hf : 7 ∣ 15 := by rwa [←h7]
    simpa using hf
  by_cases h8 : q = 8
  · exfalso
    have hf : 8 ∣ 15 := by rwa [←h8]
    simpa using hf
  by_cases h9 : q = 9
  · exfalso
    have hf : 9 ∣ 15 := by rwa [←h9]
    simpa using hf
  by_cases h10 : q = 10
  · exfalso
    have hf : 10 ∣ 15 := by rwa [←h10]
    simpa using hf
  by_cases h11 : q = 11
  · exfalso
    have hf : 11 ∣ 15 := by rwa [←h11]
    simpa using hf
  by_cases h12 : q = 12
  · exfalso
    have hf : 12 ∣ 15 := by rwa [←h12]
    simpa using hf
  by_cases h13 : q = 13
  · exfalso
    have hf : 13 ∣ 15 := by rwa [←h13]
    simpa using hf
  by_cases h14 : q = 14
  · exfalso
    have hf : 14 ∣ 15 := by rwa [←h14]
    simpa using hf
  by_cases h15 : q = 15
  · exact Or.inr (Or.inr h15)
  omega

theorem lpf_14 : IsLPF 14 7 := by
  refine ⟨primeP_7, by decide, fun q hq hqd => ?_⟩
  have hq2 : 2 ≤ q := hq.1
  have hcases := q_cases_14 q hq2 hqd
  rcases hcases with rfl | rfl | rfl
  · decide
  · decide
  · exfalso; exact not_primeP_14 hq

theorem lpf_15 : IsLPF 15 5 := by
  refine ⟨primeP_5, by decide, fun q hq hqd => ?_⟩
  have hq2 : 2 ≤ q := hq.1
  have hcases := q_cases_15 q hq2 hqd
  rcases hcases with rfl | rfl | rfl
  · decide
  · decide
  · exfalso; exact not_primeP_15 hq

theorem jsp_000307_counterexample :
    IsLPF 13 13 ∧ IsLPF 14 7 ∧ IsLPF 15 5 ∧ 13 > 7 ∧ 7 > 5 := by
  exact ⟨lpf_13, lpf_14, lpf_15, by decide, by decide⟩

theorem jsp_000307 :
    ∃ n, ∃ p1 p2 p3, IsLPF n p1 ∧ IsLPF (n+1) p2 ∧ IsLPF (n+2) p3 ∧ p1 > p2 ∧ p2 > p3 := by
  refine ⟨13, 13, 7, 5, lpf_13, lpf_14, lpf_15, by decide, by decide⟩

#print axioms jsp_000307
#print axioms jsp_000307_counterexample
