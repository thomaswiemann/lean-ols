# ols

Lean 4 formalization of OLS for the linear projection coefficient. Three
theorems, over a probability kernel postulated in this repository:

1. `√n (β̂ₙ − β₀) →d N(0, Q⁻¹ Ω Q⁻¹)`
2. `β̂ₙ →p β₀`, `Ω̂ₙ →p Ω`, `V̂ₙ →p V`
3. `t_{n,j} →d N(0, 1)`

A law is an operator `E` with a moment class `HasMoment`. iid, `→p`, and
`→d N(μ, Σ)` are primitives; the WLLN, CLT, continuous mapping, and Slutsky
are named fields of `Simple.Kernel`. There is no measure theory. Mathlib is
used for algebra and topology only.

```sh
# elan reads lean-toolchain (currently Lean 4.34.0-rc2)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake exe cache get   # Mathlib oleans; omit this and lake compiles Mathlib from source
lake build
```

Headline theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`. CI runs `lake build` and an axiom allowlist audit.

| File | Content |
|---|---|
| `Simple/Kernel/` | Postulated kernel: `E`, `HasMoment`, `Pr`, `→p`, iid, WLLN, CLT, Slutsky |
| `Ols/Defs.lean` | `gram`, `beta0`, `olsHat`, `scoreVar`; `Setting` = (A1)–(A4) |
| `Ols/Projection.lean` | orthogonality `E[X e] = 0`; exact OLS identity |
| `Ols/GramInverse.lean` | `Q̂ₙ →p Q`, `Q̂ₙ⁻¹ →p Q⁻¹` |
| `Ols/Main.lean` | Theorem 1 `ols_asymptotic_normality` |
| `Ols/Consistency.lean` | Theorem 2 |
| `Ols/TStat.lean` | Theorem 3 `tStat_asymptotic_normality` |
