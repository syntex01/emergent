# Audit of the proposed full-shift closure of the balanced determinant strip

## Verdict

The proposed full-shift prime-pair variance estimate and the weighted multiplicity lemma do **not** yet prove the balanced Gabor determinant estimate. The obstruction is exact: the determinant/output window survives the dispersion swap. It cannot generally be replaced by a coefficient depending only on the autocorrelation shift.

The finite counterexample in `Zeta70WeightedDispersion.lean` kernel-checks this obstruction.

## 1. Exact weighted dispersion identity

Let `u` and `v` be finitely supported complex sequences and let `b₁,b₂ ≥ 1`. Define

\[
 A_j=\sum_{b_1n-b_2m=j}u_m v_n.
\]

For an arbitrary output weight `W`, expansion gives

\[
\begin{aligned}
 \sum_j W(j)|A_j|^2
 ={}&\sum_{m,n,m',n'}
 1_{b_1n-b_2m=b_1n'-b_2m'}
 W(b_1n-b_2m)\\
 &\qquad\qquad\times
 u_m\overline{u_{m'}}v_n\overline{v_{n'}}.
\end{aligned}
\tag{1}
\]

Put

\[
 g=(b_1,b_2),\qquad r=b_1/g,\qquad q=b_2/g.
\]

The equality of the two fibers is equivalent to

\[
 n-n'=qk,\qquad m-m'=rk
\]

for a unique integer `k`. Therefore (1) becomes

\[
\boxed{
 \sum_j W(j)|A_j|^2
 =\sum_k\sum_{m,n}
 W(b_1n-b_2m)
 u_m\overline{u_{m-rk}}
 v_n\overline{v_{n-qk}}.
}
\tag{2}
\]

Only for constant `W` does (2) factor into

\[
 \sum_k
 \left(\sum_m u_m\overline{u_{m-rk}}\right)
 \left(\sum_n v_n\overline{v_{n-qk}}\right).
\tag{3}
\]

Thus the unweighted dispersion-swap identity is correct, but it is not the identity needed for the Gabor channel, whose determinant window is nonconstant.

## 2. Kernel-checked finite obstruction

Take `b₁=b₂=1` and

\[
 W(j)=1_{j=0}.
\]

Let `v=δ₀`, and compare `u=δ₀` with the translate `u'=δ₁`. Translation leaves the entire autocorrelation vector unchanged:

\[
 \sum_m u_m\overline{u_{m-k}}
 =\sum_m u'_m\overline{u'_{m-k}}
 \qquad\text{for every }k.
\]

Consequently every expression of the form (3), even with an arbitrary multiplier `ω(k)`, has the same value for `u` and `u'`. But the weighted fiber energies are

\[
 \sum_jW(j)|A_j(u,v)|^2=1,
 \qquad
 \sum_jW(j)|A_j(u',v)|^2=0.
\]

Therefore no universal shift-only multiplier can represent the weighted energy. `Zeta70WeightedDispersion.lean` proves this statement without `sorry`, `admit`, local axioms, or `native_decide`.

## 3. Fourier separation does not reduce to the stated full-shift theorem

Fourier inversion gives

\[
 W\!\left(\frac{b_1n-b_2m}{H}\right)
 =\int \widehat W(\xi)
 e\!\left(\frac{\xi b_1n}{H}\right)
 e\!\left(-\frac{\xi b_2m}{H}\right)d\xi.
\tag{4}
\]

Hence one may factor (2) only after introducing additively twisted correlations. In the balanced block

\[
 n\asymp D,\qquad b_1\asymp M,
 \qquad H=DM/T,
\]

so the phase in the normalized variable `n/D` has derivative of order

\[
 \frac{Db_1}{H}\asymp T.
\tag{5}
\]

It is therefore not a slowly varying dyadic weight with polylogarithmic Sobolev norms. A uniform theorem for these conductor-`T` additive twists, including its simultaneous-major-arc main term, would be a new **determinant-locked shifted circle-method theorem**. It is not the untwisted full-shift variance theorem stated in the proposed closure.

## 4. Exact arithmetic coefficient still present

The cutoff-preserving coefficient in the audited fourth word is

\[
 c_{\theta,\eta;D,M}(n)
 =\frac1{\sqrt n}\sum_{dm=n}
 (\Lambda_\theta*\mu_\eta)(d)
 (\log m)m^{i\eta}U(d/D)V(m/M).
\tag{6}
\]

After the already-controlled ranges are removed, the residual block is the balanced determinant-one strip

\[
 d=nx+bt,\qquad e=ny+at,\qquad ax-by=1,
\]

with natural area `D²/T` and arithmetic core

\[
 \sum_{q,a,b,n}\frac{\omega(q,a,b,n)}{abq}
 \sum_{t\asymp Dq/M}
 \frac{\mu(nx+bt)\mu(ny+at)}{t}
 \mathcal W_{q,a,b,n}(t).
\tag{7}
\]

The previously verified long-shift bridge/glue argument applies only to blocks already reduced to two ordinary von-Mangoldt correlations with logarithmic dilation parameters. It explicitly does not cover (7).

## 5. Exact remaining theorem

Let

\[
 \Delta=
 \limsup_{\lambda\to1^-}\limsup_{T\to\infty}
 \left(
  \frac{\|A_{\lambda,T}A_{\lambda,T}^*\|_F^2}{N(T,2T)}
  -\frac{\lambda}{10}
 \right).
\]

The missing analytic statement remains

\[
 \boxed{\Delta<\frac{11}{630}.}
\]

A valid proof must retain the determinant window in (2), the exact coefficient (6), all Mellin and Gabor amplitudes, both orientations, and all cross-dyadic blocks. Once this certificate is supplied, the existing kernel-checked finite-dimensional argument yields a strict 70% bound.
