import DiscreteAlgebra.DivisibilityGcd
import DiscreteAlgebra.CardinalityBounds

namespace DiscreteAlgebra

/-- Extended Euclidean algorithm returning Bézout coefficients `(u, v) : Int × Int`. -/
def extGcd (a b : Nat) : Int × Int :=
  if hb : b = 0 then
    (1, 0)
  else
    let p := extGcd b (a % b)
    (p.2, p.1 - Int.ofNat (a / b) * p.2)
termination_by b
decreasing_by
  exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

/-- Primality predicate on `Nat`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Product of all elements in a list of natural numbers. -/
def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

/-- Factorial function `n!`. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

private theorem mul_left_cancel_pos' {k a b : Nat} (hk : 0 < k) (h : k * a = k * b) :
    a = b := by
  have hstep : ∀ x y : Nat, x < y → k * x < k * y := by
    intro x y hxy
    have hsub : y = x + (y - x - 1 + 1) := by omega
    rw [hsub, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  cases Nat.lt_or_ge a b with
  | inl hlt => have := hstep a b hlt; omega
  | inr hge =>
    cases Nat.lt_or_ge b a with
    | inl hgt => have := hstep b a hgt; omega
    | inr hle => omega

private theorem le_of_dvd_pos {d n : Nat} (hn : 0 < n) (hd : d ∣ n) : d ≤ n := by
  cases hd with
  | intro q hq =>
    cases Nat.eq_zero_or_pos q with
    | inl hq0 => rw [hq0, Nat.mul_zero] at hq; omega
    | inr hqpos =>
      have hq1 : q = (q - 1) + 1 := by omega
      rw [hq1, Nat.mul_add, Nat.mul_one] at hq
      omega

private theorem dvd_of_mod_eq_zero {d n : Nat} (h : n % d = 0) : d ∣ n := by
  refine ⟨n / d, ?_⟩
  have hdiv := Nat.div_add_mod n d
  omega

private theorem mod_eq_zero_of_dvd {d n : Nat} (h : d ∣ n) : n % d = 0 := by
  cases h with
  | intro q hq =>
    rw [hq, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]

/-- Bézout's identity over `Int`: `gcd a b = u * a + v * b` for the coefficients of `extGcd a b`. -/
theorem bezout_identity (a b : Nat) :
    Int.ofNat (Nat.gcd a b) =
      (extGcd a b).1 * Int.ofNat a + (extGcd a b).2 * Int.ofNat b := by
  unfold extGcd
  cases Nat.eq_zero_or_pos b with
  | inl hb =>
    subst hb
    simp
  | inr hbpos =>
    have hb : b ≠ 0 := by omega
    simp only [dif_neg hb]
    have ih := bezout_identity b (a % b)
    have hstep : Nat.gcd a b = Nat.gcd b (a % b) := gcd_step a b
    have hdivI : Int.ofNat b * Int.ofNat (a / b) + Int.ofNat (a % b) = Int.ofNat a := by
      rw [← Int.ofNat_mul, ← Int.ofNat_add, Nat.div_add_mod]
    have hrem : Int.ofNat (a % b) = Int.ofNat a - Int.ofNat (a / b) * Int.ofNat b := by
      rw [Int.mul_comm (Int.ofNat (a / b)) (Int.ofNat b)]
      omega
    dsimp only
    calc Int.ofNat (Nat.gcd a b)
        = Int.ofNat (Nat.gcd b (a % b)) := by rw [hstep]
      _ = (extGcd b (a % b)).1 * Int.ofNat b +
          (extGcd b (a % b)).2 * Int.ofNat (a % b) := ih
      _ = (extGcd b (a % b)).1 * Int.ofNat b +
          (extGcd b (a % b)).2 * (Int.ofNat a - Int.ofNat (a / b) * Int.ofNat b) := by
            rw [hrem]
      _ = (extGcd b (a % b)).1 * Int.ofNat b +
          ((extGcd b (a % b)).2 * Int.ofNat a -
           (extGcd b (a % b)).2 * (Int.ofNat (a / b) * Int.ofNat b)) := by
            rw [Int.mul_sub]
      _ = (extGcd b (a % b)).2 * Int.ofNat a +
          ((extGcd b (a % b)).1 * Int.ofNat b -
           (Int.ofNat (a / b) * (extGcd b (a % b)).2) * Int.ofNat b) := by
            rw [← Int.mul_assoc (extGcd b (a % b)).2 (Int.ofNat (a / b)) (Int.ofNat b),
                Int.mul_comm (extGcd b (a % b)).2 (Int.ofNat (a / b))]
            omega
      _ = (extGcd b (a % b)).2 * Int.ofNat a +
          ((extGcd b (a % b)).1 - Int.ofNat (a / b) * (extGcd b (a % b)).2) * Int.ofNat b := by
            rw [Int.sub_mul]
termination_by b
decreasing_by
  exact Nat.mod_lt a hbpos

/-- Euclid's lemma for coprime numbers: if `gcd a b = 1` and `a ∣ b * c`, then `a ∣ c`. -/
theorem coprime_dvd_of_dvd_mul {a b c : Nat} (hcop : Nat.gcd a b = 1) (hdvd : a ∣ b * c) :
    a ∣ c := by
  cases hdvd with
  | intro k hk =>
    cases Nat.eq_zero_or_pos a with
    | inl ha0 =>
      subst ha0
      simp only [Nat.gcd_zero_left] at hcop
      rw [hcop, Nat.one_mul, Nat.zero_mul] at hk
      rw [hk]
      exact ⟨0, rfl⟩
    | inr hapos =>
      have hbez : Int.ofNat 1 = (extGcd a b).1 * Int.ofNat a + (extGcd a b).2 * Int.ofNat b := by
        have h := bezout_identity a b
        rw [hcop] at h
        exact h
      have hkI : Int.ofNat b * Int.ofNat c = Int.ofNat a * Int.ofNat k := by
        rw [← Int.ofNat_mul, ← Int.ofNat_mul, hk]
      have hcI : Int.ofNat c =
          Int.ofNat a * ((extGcd a b).1 * Int.ofNat c + (extGcd a b).2 * Int.ofNat k) := by
        calc Int.ofNat c
            = Int.ofNat 1 * Int.ofNat c := (Int.one_mul (Int.ofNat c)).symm
          _ = ((extGcd a b).1 * Int.ofNat a + (extGcd a b).2 * Int.ofNat b) * Int.ofNat c := by
                rw [hbez]
          _ = (extGcd a b).1 * Int.ofNat a * Int.ofNat c +
              (extGcd a b).2 * (Int.ofNat b * Int.ofNat c) := by
                rw [Int.add_mul, Int.mul_assoc (extGcd a b).2 (Int.ofNat b) (Int.ofNat c)]
          _ = (extGcd a b).1 * Int.ofNat a * Int.ofNat c +
              (extGcd a b).2 * (Int.ofNat a * Int.ofNat k) := by
                rw [hkI]
          _ = Int.ofNat a * ((extGcd a b).1 * Int.ofNat c) +
              Int.ofNat a * ((extGcd a b).2 * Int.ofNat k) := by
                rw [Int.mul_comm (extGcd a b).1 (Int.ofNat a),
                    Int.mul_assoc (Int.ofNat a) (extGcd a b).1 (Int.ofNat c),
                    ← Int.mul_assoc (extGcd a b).2 (Int.ofNat a) (Int.ofNat k),
                    Int.mul_comm (extGcd a b).2 (Int.ofNat a),
                    Int.mul_assoc (Int.ofNat a) (extGcd a b).2 (Int.ofNat k)]
          _ = Int.ofNat a * ((extGcd a b).1 * Int.ofNat c + (extGcd a b).2 * Int.ofNat k) := by
                rw [← Int.mul_add]
      cases hq : ((extGcd a b).1 * Int.ofNat c + (extGcd a b).2 * Int.ofNat k) with
      | ofNat m =>
        rw [hq, ← Int.ofNat_mul] at hcI
        exact ⟨m, Int.ofNat.inj hcI⟩
      | negSucc m =>
        rw [hq] at hcI
        have hneg : Int.negSucc m = - Int.ofNat (m + 1) := by omega
        rw [hneg, Int.mul_neg, ← Int.ofNat_mul] at hcI
        have ha1 : a = (a - 1) + 1 := by omega
        have hpos : 0 < a * (m + 1) := by
          rw [ha1, Nat.add_mul, Nat.one_mul]
          omega
        omega

/-- Euclid's lemma for primes: if a prime `p` divides `a * b`, then `p ∣ a` or `p ∣ b`. -/
theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (hdvd : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  cases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with
  | inl hcop =>
    exact Or.inr (coprime_dvd_of_dvd_mul hcop hdvd)
  | inr hp_eq =>
    left
    rw [← hp_eq]
    exact Nat.gcd_dvd_right p a

private theorem findPrimeDvd (n k : Nat) (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hmin : ∀ d : Nat, 2 ≤ d → d < k → ¬ d ∣ n) :
    ∃ p, IsPrime p ∧ p ∣ n := by
  cases Nat.eq_zero_or_pos (n % k) with
  | inl hmod =>
    have hkdvd : k ∣ n := dvd_of_mod_eq_zero hmod
    refine ⟨k, ⟨hk2, ?_⟩, hkdvd⟩
    intro d hdk
    have hdn : d ∣ n := Nat.dvd_trans hdk hkdvd
    have hdle : d ≤ k := le_of_dvd_pos (by omega) hdk
    cases Nat.eq_zero_or_pos d with
    | inl hd0 =>
      cases hdk with
      | intro q hq => rw [hd0, Nat.zero_mul] at hq; omega
    | inr hdpos =>
      cases Nat.lt_or_ge d 2 with
      | inl hdlt2 => left; omega
      | inr hdge2 =>
        cases Nat.lt_or_ge d k with
        | inl hdltk => exact False.elim (hmin d hdge2 hdltk hdn)
        | inr hdgek => right; omega
  | inr hmodpos =>
    have hkne : k ≠ n := by
      intro heq
      rw [heq, Nat.mod_self] at hmodpos
      omega
    have hk1le : k + 1 ≤ n := by omega
    have hmin' : ∀ d : Nat, 2 ≤ d → d < k + 1 → ¬ d ∣ n := by
      intro d hd2 hdk1 hdn
      cases Nat.lt_or_ge d k with
      | inl hdltk => exact hmin d hd2 hdltk hdn
      | inr hdgek =>
        have hdk : d = k := by omega
        rw [hdk] at hdn
        have h0 := mod_eq_zero_of_dvd hdn
        omega
    exact findPrimeDvd n (k + 1) (by omega) hk1le hmin'
termination_by n - k
decreasing_by
  omega

/-- Every integer `n ≥ 2` admits a prime divisor. -/
theorem exists_prime_dvd (n : Nat) (hn : 2 ≤ n) : ∃ p, IsPrime p ∧ p ∣ n :=
  findPrimeDvd n 2 (by omega) hn (fun _ h1 h2 _ => by omega)

/-- Existence of prime factorization: every positive natural number is a product of primes. -/
theorem exists_prime_factorization (n : Nat) (hn : 1 ≤ n) :
    ∃ ps : List Nat, (∀ p, p ∈ ps → IsPrime p) ∧ listProd ps = n := by
  cases Nat.lt_or_ge n 2 with
  | inl hn2 =>
    refine ⟨[], ?_, ?_⟩
    · intro p hp; simp at hp
    · simp only [listProd]; omega
  | inr hn2 =>
    cases exists_prime_dvd n hn2 with
    | intro p hp_pair =>
      have hp : IsPrime p := hp_pair.1
      cases hp_pair.2 with
      | intro q hq =>
        have hqpos : 1 ≤ q := by
          cases Nat.eq_zero_or_pos q with
          | inl hq0 => rw [hq0, Nat.mul_zero] at hq; omega
          | inr h => omega
        have hqlt : q < n := by
          have hp2 : p = (p - 2) + 2 := by have := hp.1; omega
          rw [hp2, Nat.add_mul] at hq
          omega
        cases exists_prime_factorization q hqpos with
        | intro ps hps =>
          refine ⟨p :: ps, ?_, ?_⟩
          · intro r hr
            simp only [List.mem_cons] at hr
            cases hr with
            | inl hrp => rw [hrp]; exact hp
            | inr hrps => exact hps.1 r hrps
          · simp only [listProd, hps.2, ← hq]
termination_by n
decreasing_by
  exact hqlt

private theorem mem_of_mem_eraseFirst {x y : Nat} {l : List Nat}
    (h : y ∈ eraseFirst x l) : y ∈ l := by
  induction l with
  | nil => simp [eraseFirst] at h
  | cons a xs ih =>
    simp only [eraseFirst] at h
    split at h
    · exact List.mem_cons_of_mem a h
    · simp only [List.mem_cons] at h ⊢
      cases h with
      | inl hya => exact Or.inl hya
      | inr hys => exact Or.inr (ih hys)

private theorem mul_listProd_eraseFirst {x : Nat} {l : List Nat} (hmem : x ∈ l) :
    x * listProd (eraseFirst x l) = listProd l := by
  induction l with
  | nil => simp at hmem
  | cons a xs ih =>
    simp only [eraseFirst, listProd]
    split
    · next hax => rw [hax]
    · next hax =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hxa => exact False.elim (hax hxa.symm)
      | inr hxs =>
        simp only [listProd]
        rw [← Nat.mul_assoc, Nat.mul_comm x a, Nat.mul_assoc, ih hxs]

private theorem count_eq_count_eraseFirst {x q : Nat} {l : List Nat} (hmem : x ∈ l) :
    count q l = if x = q then count q (eraseFirst x l) + 1 else count q (eraseFirst x l) := by
  induction l with
  | nil => simp at hmem
  | cons a xs ih =>
    simp only [eraseFirst, count]
    split
    · next hax =>
      subst hax
      rfl
    · next hax =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hxa => exact False.elim (hax hxa.symm)
      | inr hxs =>
        have ih' := ih hxs
        simp only [count]
        by_cases haq : a = q
        · simp only [if_pos haq]
          by_cases hxq : x = q
          · simp only [if_pos hxq] at ih' ⊢; omega
          · simp only [if_neg hxq] at ih' ⊢; omega
        · simp only [if_neg haq]
          by_cases hxq : x = q
          · simp only [if_pos hxq] at ih' ⊢; omega
          · simp only [if_neg hxq] at ih' ⊢; omega

private theorem prime_mem_of_dvd_listProd {p : Nat} {ps : List Nat}
    (hp : IsPrime p) (hps : ∀ r, r ∈ ps → IsPrime r) (hdvd : p ∣ listProd ps) :
    p ∈ ps := by
  induction ps with
  | nil =>
    have hle := le_of_dvd_pos (by decide) hdvd
    have hp2 := hp.1
    omega
  | cons r rs ih =>
    have hr : IsPrime r := hps r (by simp)
    have hrs : ∀ s, s ∈ rs → IsPrime s := fun s hs => hps s (by simp [hs])
    simp only [listProd] at hdvd
    cases prime_dvd_mul hp hdvd with
    | inl hpr =>
      cases hr.2 p hpr with
      | inl hp1 => have hp2 := hp.1; omega
      | inr hpeq => simp [hpeq]
    | inr hprs =>
      simp [ih hrs hprs]

private theorem listProd_pos_of_primes {ps : List Nat} (hps : ∀ r, r ∈ ps → IsPrime r) :
    1 ≤ listProd ps := by
  induction ps with
  | nil => decide
  | cons r rs ih =>
    have hr2 : 2 ≤ r := (hps r (by simp)).1
    have hrs1 : 1 ≤ listProd rs := ih (fun s hs => hps s (by simp [hs]))
    have hr1 : r = (r - 1) + 1 := by omega
    simp only [listProd]
    rw [hr1, Nat.add_mul, Nat.one_mul]
    omega

/-- Uniqueness of prime factorization (Fundamental Theorem of Arithmetic): any two lists
of primes with equal product have identical prime multiplicities. -/
theorem prime_factorization_unique {ps₁ ps₂ : List Nat}
    (hp₁ : ∀ p, p ∈ ps₁ → IsPrime p)
    (hp₂ : ∀ p, p ∈ ps₂ → IsPrime p)
    (heq : listProd ps₁ = listProd ps₂) :
    ∀ q : Nat, count q ps₁ = count q ps₂ := by
  induction ps₁ generalizing ps₂ with
  | nil =>
    cases ps₂ with
    | nil => intro q; rfl
    | cons r rs =>
      have hr2 : 2 ≤ r := (hp₂ r (by simp)).1
      have hrs1 : 1 ≤ listProd rs := listProd_pos_of_primes (fun s hs => hp₂ s (by simp [hs]))
      have hr' : r = (r - 2) + 2 := by omega
      simp only [listProd] at heq
      rw [hr', Nat.add_mul] at heq
      omega
  | cons p rest ih =>
    have hp : IsPrime p := hp₁ p (by simp)
    have hrest : ∀ r, r ∈ rest → IsPrime r := fun r hr => hp₁ r (by simp [hr])
    have hdvd : p ∣ listProd ps₂ := ⟨listProd rest, heq.symm⟩
    have hmem : p ∈ ps₂ := prime_mem_of_dvd_listProd hp hp₂ hdvd
    have hprod_erase : p * listProd (eraseFirst p ps₂) = listProd ps₂ :=
      mul_listProd_eraseFirst hmem
    have hprod_rest : listProd rest = listProd (eraseFirst p ps₂) := by
      apply mul_left_cancel_pos' (by have := hp.1; omega)
      simp only [listProd] at heq
      omega
    have hp₂' : ∀ r, r ∈ eraseFirst p ps₂ → IsPrime r :=
      fun r hr => hp₂ r (mem_of_mem_eraseFirst hr)
    have hih := ih hrest hp₂' hprod_rest
    intro q
    rw [count_eq_count_eraseFirst hmem]
    simp only [count, hih q]

private theorem factorial_pos (n : Nat) : 1 ≤ factorial n := by
  induction n with
  | zero => decide
  | succ k ih =>
    simp only [factorial]
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem dvd_factorial {k n : Nat} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    k ∣ factorial n := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [factorial]
    cases Nat.lt_or_ge k (m + 1) with
    | inl hlt =>
      cases ih (by omega) with
      | intro q hq =>
        refine ⟨(m + 1) * q, ?_⟩
        rw [hq, Nat.mul_left_comm]
    | inr hge =>
      have hkeq : k = m + 1 := by omega
      rw [hkeq]
      exact ⟨factorial m, rfl⟩

/-- Euclid's theorem: there are infinitely many primes (`∀ n, ∃ p > n, IsPrime p`). -/
theorem exists_prime_gt (n : Nat) : ∃ p : Nat, n < p ∧ IsPrime p := by
  have hfac : 1 ≤ factorial n := factorial_pos n
  cases exists_prime_dvd (factorial n + 1) (by omega) with
  | intro p hp_pair =>
    refine ⟨p, ?_, hp_pair.1⟩
    cases Nat.lt_or_ge n p with
    | inl hlt => exact hlt
    | inr hle =>
      have hp2 : 2 ≤ p := hp_pair.1.1
      have hpf : p ∣ factorial n := dvd_factorial (by omega) hle
      have hp1 : p ∣ (factorial n + 1) - factorial n :=
        dvd_sub_of_dvd (by omega) hp_pair.2 hpf
      have hsub : (factorial n + 1) - factorial n = 1 := by omega
      rw [hsub] at hp1
      have hple1 : p ≤ 1 := le_of_dvd_pos (by decide) hp1
      omega

end DiscreteAlgebra
