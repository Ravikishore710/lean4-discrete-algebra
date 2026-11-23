
# lean4-discrete-algebra (`v2.0.0`)

A complete, self-contained, zero-dependency Lean 4 (`v4.24.0`) formalization of discrete algebra, elementary number theory, and finite combinatorics.

`v2.0.0` completes the full project scope constructively from first principles using pure Lean 4 core (`Init`/`Std`) with `autoImplicit = false` and CI enforcement of zero `sorry`, `admit`, or custom `axiom` declarations.

## Theorem Index

### Core Induction Identities (`DiscreteAlgebra/InductionIdentities.lean`)

| File | Theorem Name | Mathematical Statement | Status |
| :--- | :--- | :--- | :--- |
| `DiscreteAlgebra/InductionIdentities.lean` | `two_mul_sumFirst` | $2 \sum_{k=0}^{n} k = n(n+1)$ | Verified |
| `DiscreteAlgebra/InductionIdentities.lean` | `sumOdd_eq_sq` | $\sum_{k=0}^{n-1} (2k+1) = n^2$ | Verified |
| `DiscreteAlgebra/InductionIdentities.lean` | `six_mul_sumSquares` | $6 \sum_{k=0}^{n} k^2 = n(n+1)(2n+1)$ | Verified |
| `DiscreteAlgebra/InductionIdentities.lean` | `sumCubes_eq_sumFirst_sq` | $\sum_{k=0}^{n} k^3 = \left(\sum_{k=0}^{n} k\right)^2$ | Verified |
| `DiscreteAlgebra/InductionIdentities.lean` | `sumPowTwo_add_one` | $\left(\sum_{k=0}^{n} 2^k\right) + 1 = 2^{n+1}$ | Verified |

### Divisibility & Euclidean GCD (`DiscreteAlgebra/DivisibilityGcd.lean`)

| File | Theorem Name | Mathematical Statement | Status |
| :--- | :--- | :--- | :--- |
| `DiscreteAlgebra/DivisibilityGcd.lean` | `dvd_linear_comb` | $d \mid a \land d \mid b \implies d \mid (xa + yb)$ | Verified |
| `DiscreteAlgebra/DivisibilityGcd.lean` | `dvd_sub_of_dvd` | $b \le a \land d \mid a \land d \mid b \implies d \mid (a - b)$ | Verified |
| `DiscreteAlgebra/DivisibilityGcd.lean` | `dvd_iff_dvd_mod` | $d \mid b \implies (d \mid a \iff d \mid (a \bmod b))$ | Verified |
| `DiscreteAlgebra/DivisibilityGcd.lean` | `gcd_step` | $\gcd(a, b) = \gcd(b, a \bmod b)$ | Verified |
| `DiscreteAlgebra/DivisibilityGcd.lean` | `gcd_mul_left` | $\gcd(ka, kb) = k \cdot \gcd(a, b)$ | Verified |

### Modular Congruence Equivalence Classes (`DiscreteAlgebra/ModularArithmetic.lean`)

| File | Theorem Name | Mathematical Statement | Status |
| :--- | :--- | :--- | :--- |
| `DiscreteAlgebra/ModularArithmetic.lean` | `ModEq.equivalence` | $\equiv \pmod{m}$ is an equivalence relation on $\mathbb{N}$ | Verified |
| `DiscreteAlgebra/ModularArithmetic.lean` | `ModEq.add` | $a \equiv b \land c \equiv d \pmod{m} \implies a + c \equiv b + d \pmod{m}$ | Verified |
| `DiscreteAlgebra/ModularArithmetic.lean` | `ModEq.mul` | $a \equiv b \land c \equiv d \pmod{m} \implies ac \equiv bd \pmod{m}$ | Verified |
| `DiscreteAlgebra/ModularArithmetic.lean` | `ModEq.pow` | $a \equiv b \pmod{m} \implies a^k \equiv b^k \pmod{m}$ | Verified |
| `DiscreteAlgebra/ModularArithmetic.lean` | `ModEq.iff_dvd_sub` | $b \le a \implies (a \equiv b \pmod{m} \iff m \mid (a - b))$ | Verified |
| `DiscreteAlgebra/ModularArithmetic.lean` | `ModEq.of_dvd` | $n \mid m \land a \equiv b \pmod{m} \implies a \equiv b \pmod{n}$ | Verified |

### Finite List Cardinality & Pigeonhole (`DiscreteAlgebra/CardinalityBounds.lean`)

| File | Theorem Name | Mathematical Statement | Status |
| :--- | :--- | :--- | :--- |
| `DiscreteAlgebra/CardinalityBounds.lean` | `length_filter_le` | $\lvert \text{filter}(p, l) \rvert \le \lvert l \rvert$ | Verified |
| `DiscreteAlgebra/CardinalityBounds.lean` | `length_filter_add_not` | $\lvert \text{filter}(p, l) \rvert + \lvert \text{filter}(\neg p, l) \rvert = \lvert l \rvert$ | Verified |
| `DiscreteAlgebra/CardinalityBounds.lean` | `nodup_length_le_of_subset` | $\text{NoDup}(l_1) \land l_1 \subseteq l_2 \implies \lvert l_1 \rvert \le \lvert l_2 \rvert$ | Verified |
| `DiscreteAlgebra/CardinalityBounds.lean` | `pigeonhole_exists_dup` | $\lvert l_2 \rvert < \lvert l_1 \rvert \land l_1 \subseteq l_2 \implies \exists x,\, \text{count}(x, l_1) \ge 2$ | Verified |

### Bezout Identity & Fundamental Theorem of Arithmetic (`DiscreteAlgebra/BezoutAndPrimes.lean`)

| File | Theorem Name | Mathematical Statement | Status |
| :--- | :--- | :--- | :--- |
| `DiscreteAlgebra/BezoutAndPrimes.lean` | `bezout_identity` | $\gcd(a, b) = u a + v b$ over $\mathbb{Z}$ via `extGcd` | Verified |
| `DiscreteAlgebra/BezoutAndPrimes.lean` | `coprime_dvd_of_dvd_mul` | $\gcd(a, b) = 1 \land a \mid bc \implies a \mid c$ | Verified |
| `DiscreteAlgebra/BezoutAndPrimes.lean` | `prime_dvd_mul` | $\text{IsPrime}(p) \land p \mid ab \implies p \mid a \lor p \mid b$ | Verified |
| `DiscreteAlgebra/BezoutAndPrimes.lean` | `exists_prime_dvd` | $n \ge 2 \implies \exists p,\, \text{IsPrime}(p) \land p \mid n$ | Verified |
| `DiscreteAlgebra/BezoutAndPrimes.lean` | `exists_prime_factorization` | $n \ge 1 \implies \exists ps,\, (\forall p \in ps,\, \text{IsPrime}(p)) \land \prod ps = n$ | Verified |
| `DiscreteAlgebra/BezoutAndPrimes.lean` | `prime_factorization_unique` | Equal products of primes have identical prime multiplicities | Verified |
| `DiscreteAlgebra/BezoutAndPrimes.lean` | `exists_prime_gt` | $\forall n \in \mathbb{N},\, \exists p > n,\, \text{IsPrime}(p)$ (Euclid theorem) | Verified |

### `ZMod` Quotient Algebra, CRT & Totient (`DiscreteAlgebra/ChineseRemainder.lean`)

| File | Theorem Name | Mathematical Statement | Status |
| :--- | :--- | :--- | :--- |
| `DiscreteAlgebra/ChineseRemainder.lean` | `ZMod.mk_eq_iff` | $[a]_m = [b]_m \iff a \equiv b \pmod{m}$ in `ZMod m` | Verified |
| `DiscreteAlgebra/ChineseRemainder.lean` | `ZMod.mul_add` | $x(y + z) = xy + xz$ in the quotient algebra `ZMod m` | Verified |
| `DiscreteAlgebra/ChineseRemainder.lean` | `ModEq.mul_left_cancel_of_coprime` | $\gcd(c, m) = 1 \land ca \equiv cb \pmod{m} \implies a \equiv b \pmod{m}$ | Verified |
| `DiscreteAlgebra/ChineseRemainder.lean` | `ModEq.of_coprime_mul` | $\gcd(m, n) = 1 \land a \equiv b \pmod{m, n} \implies a \equiv b \pmod{mn}$ | Verified |
| `DiscreteAlgebra/ChineseRemainder.lean` | `exists_mod_inv` | $\gcd(m, n) = 1 \implies \exists k \in \mathbb{N},\, km \equiv 1 \pmod{n}$ | Verified |
| `DiscreteAlgebra/ChineseRemainder.lean` | `chinese_remainder_exists` | $\gcd(m, n) = 1 \implies \exists x,\, x \equiv a \pmod{m} \land x \equiv b \pmod{n}$ | Verified |
| `DiscreteAlgebra/ChineseRemainder.lean` | `chinese_remainder_unique` | Coprime CRT solutions are unique modulo $mn$ | Verified |
| `DiscreteAlgebra/ChineseRemainder.lean` | `totient_prime` | $\text{IsPrime}(p) \implies \varphi(p) = p - 1$ | Verified |

### Finite Bijections & Double Counting (`DiscreteAlgebra/DoubleCounting.lean`)

| File | Theorem Name | Mathematical Statement | Status |
| :--- | :--- | :--- | :--- |
| `DiscreteAlgebra/DoubleCounting.lean` | `nodup_map_of_injective` | Injective $f$ preserves `NoDup` under `List.map` | Verified |
| `DiscreteAlgebra/DoubleCounting.lean` | `card_le_of_inj_on_list` | Injective $f : l_1 \to l_2$ with $\text{NoDup}(l_1) \implies \lvert l_1 \rvert \le \lvert l_2 \rvert$ | Verified |
| `DiscreteAlgebra/DoubleCounting.lean` | `card_eq_of_bij_on_list` | Bijection between duplicate-free lists implies $\lvert l_1 \rvert = \lvert l_2 \rvert$ | Verified |
| `DiscreteAlgebra/DoubleCounting.lean` | `double_counting` | $\sum_{a \in xs} \deg_R(a) = \sum_{b \in ys} \deg_R(b)$ | Verified |
| `DiscreteAlgebra/DoubleCounting.lean` | `double_counting_regular` | Constant row degree $r$ and column degree $c \implies \lvert xs \rvert r = \lvert ys \rvert c$ | Verified |
| `DiscreteAlgebra/DoubleCounting.lean` | `length_cartProd` | $\lvert xs \times ys \rvert = \lvert xs \rvert \cdot \lvert ys \rvert$ | Verified |

## Build Instructions

Install [`elan`](https://github.com/leanprover/elan) and compile the complete verified library from the repository root:

```bash
lake build
```

`elan` automatically selects the pinned toolchain (`leanprover/lean4:v4.24.0`) declared in `lean-toolchain`.
