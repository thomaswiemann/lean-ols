import Simple.Kernel.Expectation
import Simple.Kernel.Events
import Simple.Kernel.Convergence
import Simple.Kernel.Asymptotics

/-!
# The postulate kernel

Probability as a paper writes it, not as measure theory. A sample space is a
bare type `Ω`. Every probabilistic notion is either a primitive or a named
postulate; OLS proofs derive from those by algebra. Nothing here is a
`Measure`, a σ-algebra, or an integral.

* `Kernel.Expectation` — postulates (E1)–(E11): the operator `E` and the
  regularity class `HasMoment`; derived linearity over finite sums.
* `Kernel.Events` — derived: `Pr A = E[𝟙_A]`, union bound, Markov.
* `Kernel.Convergence` — defined: `→p`; derived: continuous mapping, joint
  convergence, vanishing events.
* `Kernel.Asymptotics` — postulates (T0)–(T2), (T4): primitives `IID` and
  `→d N(μ, Σ)`; named theorems WLLN, CLT, Slutsky.

A theorem takes `(K : Simple.Kernel Ω)`. Postulates are structure fields, not
global `axiom`s, so `#print axioms` stays Lean's standard three.
-/
