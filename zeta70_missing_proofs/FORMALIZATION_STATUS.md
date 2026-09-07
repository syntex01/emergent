# Zeta70 formalization status

## Verdict

An unconditional Lean theorem proving that at least 70% of the nontrivial zeros of the Riemann zeta function are simple and lie on the critical line is not currently justified by the supplied proof chain.

The finite-dimensional detector is formalized and kernel-checked. The missing part is still analytic: one must prove the exact cutoff-preserving balanced Gabor determinant estimate and connect it to the formal zeta-zero objects. Introducing that statement as an `axiom`, a structure field, or a theorem with an unproved premise would produce only a conditional theorem.

## Kernel-checked layer

`Zeta70MissingProofs.lean` proves, without `sorry`, `admit`, or local axioms:

- the quartic detector identities and pointwise inequalities;
- admissibility of the optimized detector;
- the repaired scalar zero-side inequality;
- the hard-channel error budget
  \[
  \Delta<\frac{11}{630}
  \Longrightarrow
  \liminf \frac{N_0^s(T,2T)}{N(T,2T)}>\frac7{10};
  \]
- the exact value of the proposed constants;
- the normalization obstruction to the discarded `1/H` contraction proof.

`Zeta70FormalBoundary.lean` additionally formalizes weighted finite Cauchy--Schwarz after the complete modulus family has been aggregated, the abstract geometric-mean transfer for two globally weighted square sums, exact cancellation of the reciprocal scale ratios, and the filter-level implication from a genuine analytic certificate below `11/630` to an eventual 70% lower bound.

The new file intentionally supplies no constructor for the analytic certificate.

## Exact remaining analytic certificate

For the actual cutoff-preserving one-sided Gabor matrix `A_{lambda,T}`, define

\[
\Delta=
\limsup_{\lambda\to1^-}\limsup_{T\to\infty}
\left(
 \frac{\|A_{\lambda,T}A_{\lambda,T}^*\|_F^2}{N(T,2T)}
 -\frac{\lambda}{10}
\right).
\]

The remaining theorem is

\[
\boxed{\Delta<\frac{11}{630}.}
\]

The exact dyadic coefficient is

\[
c_{\theta,\eta;D,M}(n)
 =\frac1{\sqrt n}\sum_{dm=n}
 (\Lambda_\theta*\mu_\eta)(d)
 (\log m)m^{i\eta}U(d/D)V(m/M).
\]

After the already-controlled ranges are removed, the residual balanced block has

\[
H<M<D<T,\qquad DM\asymp Y,\qquad H=Y/T,
\]

and becomes a determinant-one strip

\[
d=nx+bt,\qquad e=ny+at,\qquad ax-by=1,
\]

with natural area `D^2/T` and arithmetic core

\[
\sum_{q,a,b,n}\frac{\omega(q,a,b,n)}{abq}
\sum_{t\asymp Dq/M}
\frac{\mu(nx+bt)\mu(ny+at)}{t}
\mathcal W_{q,a,b,n}(t).
\]

## Audit of the newest full-shift proposal

The proposed full-shift prime-pair variance theorem is a plausible classical circle-method target. The weighted multiplicity calculation is also a valid abstract mechanism. They do not yet constitute a proof of the exact Gabor strip estimate.

The argument applies the full-shift variance theorem to ordinary correlations of `Lambda`. The exact residual coefficient in the Gabor word is instead `(Lambda_theta * mu_eta)(d) ell_eta(m)`, and the balanced residual is the Möbius two-linear-form strip displayed above. A theorem identifying the full cutoff-preserving, path-weighted, cross-dyadic determinant form with the specific product of ordinary prime-pair errors used by the multiplicity argument has not been derived. The earlier verified bridge/glue theorem only covers blocks that already reduce to two von-Mangoldt correlations with logarithmic dilation parameters; it explicitly leaves the polynomially balanced strip untreated.

Therefore the line “the `k != 0` part is exactly of the form in Theorem B” is presently an unproved analytic identification, not a definitional rewrite. Formalization stops precisely there.

A second independent obligation is the exact centered major-arc sign after all Mellin twists, path amplitudes, orientations, and cross-dyadic blocks are recombined. A scalar singular-series sign is not enough unless the required Gram factorization is proved for the actual channel.

## Honest Lean dependency graph

```text
Existing explicit-formula / zero-side formalization
+ exact cutoff-preserving trace identification
+ balanced strip estimate at natural D^2/T normalization
+ exact centered major-arc sign
------------------------------------------------------
analytic certificate Delta < 11/630
+ kernel-checked finite-dimensional detector
------------------------------------------------------
liminf N0simple(T,2T) / N(T,2T) > 7/10
```

Only the bottom implication and several exact algebraic reductions are currently kernel-checked. The top analytic row cannot be replaced by a local axiom while retaining the word “unconditional.”
