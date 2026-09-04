# ols

Lean 4 formalization of OLS for the linear projection coefficient.
Probability is a small kernel *postulated in this repo*: named limit theorems
are fields of a structure, not measure theory. Mathlib is used for algebra
and topology only.

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake exe cache get   # skip this and `lake build` compiles Mathlib from source
lake build
```

Headline theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Theorem 1, as a paper writes it

The claim (`Ols/Main.lean`): under iid second moments and a positive definite
Gram matrix,

$$
\sqrt{n}\,(\hat\beta_n - \beta_0) \to_d \mathcal{N}(0,\, Q^{-1}\Omega Q^{-1}).
$$

On the blackboard this is one identity and three citations.

**Identity (proved, algebra).** For every sample,

$$
\sqrt{n}\,(\hat\beta_n - \beta_0)
  = \hat Q_n^{-1}\,(\sqrt{n}\,\bar g_n)
  + R_n,
$$

where $\bar g_n$ is the average of the scores $X_i e_i$ and $R_n$ is
zero whenever $\hat Q_n$ is invertible. That is `olsHat_sub_beta0` /
`normError_eq`. The scores are orthogonal, $E[X e] = 0$, because $\beta_0$
is defined as $Q^{-1}E[XY]$ and $E$ is linear — `E_score_eq_zero` in
`Ols/Projection.lean`, no limit theorem.

**Citations (assumed).** A paper says “by the WLLN / CLT / Slutsky” and does
not unfold those theorems. Here they are fields of `Simple.Kernel`, not
proofs:

| Paper | Kernel field | Used for |
|---|---|---|
| functions of iid data are iid | `iid_comp` (T0) | scores and Gram outer products are iid |
| WLLN | `wlln` (T1) | $\hat Q_n \to_p Q$ |
| CLT | `clt` (T2) | $\sqrt{n}\,\bar g_n \to_d \mathcal{N}(0,\Omega)$ |
| Slutsky | `slutsky` (T4) | $\hat Q_n^{-1}(\sqrt{n}\,\bar g_n) + R_n \to_d \mathcal{N}(0, Q^{-1}\Omega Q^{-1})$ |

Slutsky is not proved. The last line of Theorem 1 is one call to `K.slutsky`,
once the identity is rewritten into the form $B_n Z_n + R_n$.

**In between (proved from the kernel).** Continuous mapping, joint
convergence, and “the remainder lives on a vanishing event” are theorems
about the *definition* of $\to_p$ (`Simple/Kernel/Convergence.lean`). They
turn the WLLN into $\hat Q_n^{-1} \to_p Q^{-1}$ and $R_n \to_p 0$
(`Ols/GramInverse.lean`). Linearity of $E$ over finite sums is likewise
derived from the expectation postulates.

```
Defs          β₀, Q̂, β̂, Ω, V, assumptions (A1)–(A4)
  └─ Projection     E[Xe]=0 and the exact identity
       └─ GramInverse   Q̂ →p Q, Q̂⁻¹ →p Q⁻¹, Rₙ →p 0
            └─ Main     CLT on scores, then Slutsky
```

`Simple/Kernel/` is the language those files speak: `Expectation.lean` for
$E$ and moments, `Events.lean` / `Convergence.lean` for $\Pr$ and
$\to_p$, `Asymptotics.lean` for iid, the CLT, and Slutsky.

Theorems 2 and 3 (`Ols/Consistency.lean`, `Ols/TStat.lean`) reuse the same
kernel; they are not spelled out here.
