# Theorem 10.13 and Lemma 12.2 of Montgomery–Vaughan without the Hadamard product

Detailed proofs for the node `ZetaGoodHeights.v1` (drafts in `blueprint/ieantn/ZetaGoodHeights/v1/`), written on
26 November 2026 by Claude for H. Helfgott, to be formalized. [MV] = Montgomery–Vaughan, *Multiplicative Number
Theory I*. Every Mathlib name below was checked at IEANTN's Mathlib pin (`71a80585`); every IEANTN name in
IEANTN at commit `cd9c2dd` (23 November 2026).

**What [MV] do.** Theorem 10.13: Jensen's inequality applied to $\xi(s)$ on the disc with centre $2+i(T+\frac12)$,
$R=\frac{11}6$, $r=\frac74$, with the estimates of their Corollary 1.17, plus the symmetry of the zeros.
Lemma 12.2: from Lemma 12.1, $\frac{\zeta'}\zeta(s)=\frac{-1}{s-1}+\sum_{|\gamma-t|\le1}\frac1{s-\rho}+O(\log\tau)$
for $-1\le\sigma\le2$, by choosing $T_1$ with $|T_1-\gamma|\gg1/\log T$ for all zeros. They prove Lemma 12.1 from
(10.29) (part of Corollary 10.14) and Theorem C.1, hence from the Hadamard product (Theorem 10.12), and remark that
it could also be proved "by the same method that we used to prove Lemma 6.4".

**What is done here.** Mathlib has no Hadamard product, so we take the other route [MV] mention:
* Theorem 10.13: Jensen, on [MV]'s disc, applied to $(s-1)\zeta(s)$ instead of $\xi(s)$ (no Gamma-function
  estimates needed);
* the local expansion of $\zeta'/\zeta$ over nearby zeros for $\frac12\le\sigma\le2$, by Landau's lemma
  ([MV, Lemma 6.3], as in their Lemma 6.4), whose proof uses Borel–Carathéodory, now in Mathlib;
* $-1\le\sigma<\frac12$ by the functional equation of $\zeta'/\zeta$ (IEANTN `ZetaLogDeriv.v1`, proved) and a bound
  for the digamma function.

The bound for the digamma function uniform on a vertical strip that this needs is in the Riemann–Stieltjes library
(see (D) and §5). Appendix A, which proves IEANTN's stronger `GammaAsymptotics.v1` instead, is no longer on the
critical path.

Notation: $s=\sigma+it$; zeros $\rho=\beta+i\gamma$ of $\zeta$ with $0<\beta<1$, counted with multiplicity
$m_\rho$ (IEANTN's `zetaOrder`); $N[a,b]$ = number of such zeros with $a\le\gamma\le b$.

## 1. Inputs

**(Z1) A bound for $\zeta$ in $\sigma>0$.** For $\sigma>0$, $s\ne1$,
$$\zeta(s)=\frac{s}{s-1}-s\int_1^\infty\{u\}u^{-s-1}\,du ,$$
hence, with $(s-1)\zeta(s)$ extended by $1$ at $s=1$,
$$|(s-1)\zeta(s)|\le|s|\Bigl(1+\frac{|s-1|}{\sigma}\Bigr)\quad(\sigma>0),\qquad
|\zeta(s)|\le\frac{|s|}{|s-1|}+\frac{|s|}{\sigma}\quad(\sigma>0,\ s\ne1).$$
*Proof.* For $\sigma>1$, partial summation gives $\sum_{n\le x}n^{-s}=\lfloor x\rfloor x^{-s}+s\int_1^x\lfloor u\rfloor
u^{-s-1}du$; let $x\to\infty$ and write $\lfloor u\rfloor=u-\{u\}$. The right-hand side is holomorphic on
$\sigma>0$, $s\ne1$ (differentiate under the integral; $|\{u\}u^{-s-1}|\le u^{-\sigma-1}$), so it equals $\zeta$
there by the identity theorem. The bounds follow from $\int_1^\infty u^{-\sigma-1}du=1/\sigma$.
Sources for the representation, any one of which will do:
* Mathlib's partial summation, `NumberTheory/AbelSummation.lean` (`sum_mul_eq_sub_integral_mul`);
* the Riemann–Stieltjes library (`Mathlib/Analysis/BoxIntegral/Stieltjes/Sum.lean` in mathlib-at-ICERM26, to be
  ported): `BoxIntegral.sum_mul_eq_sub_stieltjes_integral`, [MV] (A.5), which needs only continuity of the weight;
  it asks for continuity on $[0,N]$, so modify $x^{-s}$ on $[0,1)$;
* PNT+ (`PrimeNumberTheoremAnd/ZetaBounds.lean`), `Zeta0EqZeta`: for $N\ge1$, $\sigma>0$, $s\ne1$,
  $\zeta(s)=\sum_{n\le N}n^{-s}-\frac{N^{1-s}}{1-s}-\frac{N^{-s}}2+s\int_N^\infty(\lfloor x\rfloor+\frac12-x)x^{-s-1}dx$.
  At $N=1$ this is the representation above, after $s\int_1^\infty\frac12x^{-s-1}dx=\frac12$. Port with credit.

*In Lean*, use Mathlib's `riemannZeta₁` (`NumberTheory/Harmonic/ZetaAsymp.lean`) for $(s-1)\zeta(s)$:
`differentiable_riemannZeta₁`, `riemannZeta₁_one : riemannZeta₁ 1 = 1`, and
`riemannZeta_eq_inv_sub_mul : s ≠ 1 → riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s`. Do **not** use
`fun s ↦ (s - 1) * riemannZeta s`: Lean's `riemannZeta 1` is finite (`riemannZeta_one`: $(\gamma-\log4\pi)/2$), so
that function is $0$ at $s=1$ and is not continuous there.

**(Z2) A lower bound at $\sigma=2$.** $|\zeta(2+it)|\ge1-\sum_{n\ge2}n^{-2}=2-\zeta(2)=2-\pi^2/6>0.35$.
(`zeta_eq_tsum_one_div_nat_cpow`, `riemannZeta_two`.)

**(Z3) Symmetry of the zeros.** If $0<\beta<1$, then $1-\bar\rho$ is a zero with $m_{1-\bar\rho}=m_\rho$.
*Proof.* `riemannZeta_conj : riemannZeta (conj s) = conj (riemannZeta s)` (Mathlib, `ZetaAsymp.lean`) gives
$m_{\bar\rho}=m_\rho$. And `riemannZeta_one_sub` gives $\zeta(1-s)=2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)\zeta(s)$
for $s\ne1$, $s\notin\{0,-1,-2,\dots\}$; near $\rho$ the factor in front of $\zeta(s)$ is holomorphic and non-zero
(`Complex.Gamma_ne_zero_of_re_pos`; $\cos(\pi s/2)$ vanishes only at odd integers), so $\zeta(1-s)$ and $\zeta(s)$
vanish to the same order at $s=\rho$, i.e. $m_{1-\rho}=m_\rho$. (IEANTN's `ZetaZeroes.v1` has no symmetry
conclusion; this is proved in the solution.)

**(J) Jensen's inequality**, Mathlib's form of [MV, Lemma 6.1], `AnalyticOnNhd.sum_divisor_le`: if $f$ is analytic on
$\overline B(c,R)$, $f(c)\ne0$, $|f|\le M$ on the circle $|z-c|=R$, $M\ge1$ and $0<r<R$, then
$\sum_u \operatorname{divisor}(f,\overline B(c,r))(u)\le\log(M/|f(c)|)/\log(R/r)$.

**(L) Landau's lemma**, [MV, Lemma 6.3] with $1+\log$ in place of $\log$ (which only matters when $M/|f(0)|$ is
near $1$). Let $0<r<R<1$. If $f$ is analytic on a neighbourhood of $|z|\le1$, $|f|\le M$ there and $f(0)\ne0$,
then for $|z|\le r$ with $f(z)\ne0$
$$\frac{f'}{f}(z)=\sum_{|z_k|\le R}\frac{m_k}{z-z_k}+O_{r,R}\Bigl(1+\log\frac M{|f(0)|}\Bigr),$$
the sum running over the distinct zeros $z_k$, with multiplicities $m_k$.

*Proof*, [MV]'s, with Mathlib's tools. Dividing $f$ by $M$ changes neither $f'/f$ nor $\log(M/|f(0)|)$, so assume
$M=1$; put $L=\log(1/|f(0)|)\ge0$, $R_2=\frac{1+R}2$, and $K=\sum_{|z_k|\le R_2}m_k$. By (J) with radii
$R_2<1$, $K\le L/\log(1/R_2)$.
1. There are finitely many zeros in $|z|\le R_2$, so we can choose $R<R'<R''<R_2$ with no zero in
   $R'\le|z|<R''$. For $|z|\le r$, the zeros with $R<|z_k|\le R'$ contribute at most $K/(R-r)$ to the sum, so it is
   enough to prove the expansion with the sum over $|z_k|\le R'$.
2. On the open ball $U=B(0,R'')$, `MeromorphicOn.extract_zeros_poles` gives $g_0$, analytic and zero-free on $U$, with
   $f=\prod_k(z-z_k)^{m_k}g_0$ off a codiscrete subset of $U$, hence on all of $U$ by continuity. The product runs
   over the zeros in $U$, which are those with $|z_k|<R'$. Put
   $$G(z)=g_0(z)\prod_k\Bigl(\frac{R'^2-\bar z_kz}{R'}\Bigr)^{m_k}=f(z)\prod_k\Bigl(\frac{R'^2-\bar z_kz}{R'(z-z_k)}\Bigr)^{m_k}$$
   ([MV]'s function). The new factors vanish only at $R'^2/\bar z_k$, of modulus $>R'$ (and $z_k\ne0$ since
   $f(0)\ne0$), so $G$ is analytic on $U$ and zero-free on $\overline B(0,R')$.
3. On $|z|=R'$, $|R'^2-\bar z_kz|=R'|z-z_k|$, so $|G|=|f|\le1$; by the maximum modulus principle
   (`Complex.norm_le_of_forall_mem_frontier_norm_le`), $|G|\le1$ on $\overline B(0,R')$. Also
   $|G(0)|=|f(0)|\prod_k(R'/|z_k|)^{m_k}\ge|f(0)|$.
4. $G'/G$ is holomorphic on $B(0,R')$, so it has a primitive $h$ there with $h(0)=0$
   (`DifferentiableOn.isExactOn_ball`). Then $(Ge^{-h})'=0$, so $G=G(0)e^h$ and $\Re h=\log|G|-\log|G(0)|\le L$.
5. Borel–Carathéodory (`Complex.borelCaratheodory`, with $M_1=1+L>0$ and $h(0)=0$) on $B(0,R')$:
   $|h(w)|\le2M_1|w|/(R'-|w|)$. For $|z|\le r$, Cauchy's estimate
   (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) on the circle of radius $\delta=(R'-r)/2$ about $z$,
   where $|w|\le(R'+r)/2$, gives $|h'(z)|\le\frac{2M_1(R'+r)}{(R'-r)\delta}=\frac{4M_1(R'+r)}{(R'-r)^2}
   \le\frac{8M_1}{(R-r)^2}$.
6. Where $f(z)\ne0$: $h'=\frac{G'}G=\frac{f'}f-\sum_k\frac{m_k}{z-z_k}+\sum_k\frac{m_k}{z-R'^2/\bar z_k}$, and for
   $|z|\le r$ each term of the last sum has modulus at most $m_k/(R'-r)<m_k/(R-r)$.

So the error is at most $\frac{2K}{R-r}+\frac{8(1+L)}{(R-r)^2}\ll_{r,R}1+L$. $\square$

**(FE) The functional equation of $\zeta'/\zeta$**, IEANTN `ZetaLogDeriv.v1.logDeriv_functional_equation` (solved,
through Comparator): if $s\notin\{0,-1,-2,\dots\}$, $s\ne1$, $\zeta(s)\ne0$ and $\cos(\pi s/2)\ne0$, then
$\frac{\zeta'}{\zeta}(s)=-\frac{\zeta'}{\zeta}(1-s)+\log2\pi-\psi(s)+\frac\pi2\tan\frac{\pi s}2$.

**(D) Digamma.** Needed: $|\psi(\sigma+it)|\le C_D\log(|t|+2)$ for $1\le\sigma\le\frac52$ and all real $t$.
* **Source (decided 27 November 2026):** the library's `Complex.exists_norm_digamma_le_log` (blueprint B3, first
  statement, as drafted in `blueprint/drafts/DigammaFourier.lean`:
  `0 < σ₁ → ∃ C, ∀ σ t : ℝ, σ ∈ Set.Icc σ₁ σ₂ → ‖digamma (σ + t * I)‖ ≤ C * Real.log (|t| + 2)`), with
  $[\sigma_1,\sigma_2]=[1,\frac52]$. Proved by the other chat (`SpecialFunctions/Gamma/DigammaSeries.lean`, branch
  `mv-lemma-12-14`, commit `77ccfc1e`, statement as drafted), from its `Complex.norm_digamma_sub_le`:
  $\|\psi(a+it)-\psi(a)\|\le2(\frac1{m^2}+\frac1m)\log(1+|t|)$, $m=\min(a,1)$. For instance, on $1\le a\le\frac52$
  this gives $|\psi(a+it)|\le0.71+4\log(1+|t|)$, since $\psi$ increases on $(0,\infty)$ from $\psi(1)=-\gamma$ to
  $\psi(\frac52)=\frac83-\gamma-2\log2<0.71$.
* Not used any more: IEANTN `GammaAsymptotics.v1.digamma_sub_log_isBigO` ($\|\psi(w)-\log w\|\le C/\|w\|$ for
  $\Re w\ge1$), which also gives (D) but is unproved (status `awaiting-solution`). Appendix A proves it.
  `GammaAsymptotics.v2` (proved) is the version for bounded $|\Im w|$, which would not do: $T_1\to\infty$.

The recurrence $\psi(w+1)=\psi(w)+1/w$ is Mathlib's `Complex.digamma_apply_add_one`.

## 2. Theorem 10.13: $N[T,T+1]\le C\log(T+2)$ for $T\ge0$

Let $f(s)=(s-1)\zeta(s)$ (entire, `riemannZeta₁` in Lean; its zeros are those of $\zeta$ with the same orders, and
$f(1)=1$). Take $c=2+i(T+\frac12)$, $R=\frac{11}6$, $r=\frac74$.

* On $|s-c|=R$: $\sigma\ge2-\frac{11}6=\frac16$, $|s|\le|c|+R\le T+5$ and $|s-1|\le|c-1|+R\le T+4$, so by (Z1)
  $|f(s)|\le(T+5)(1+6(T+4))\le6(T+5)^2=:M$ ($\ge1$).
* $|f(c)|=|c-1|\,|\zeta(c)|\ge0.35$ by (Z2), since $|c-1|\ge1$.
* By (J), the zeros of $f$ in $\overline B(c,\frac74)$, with multiplicity, number at most
  $\log\bigl(6(T+5)^2/0.35\bigr)/\log\frac{22}{21}$.
* A zero with $\frac12\le\beta<1$ and $T\le\gamma\le T+1$ satisfies $|\rho-c|^2\le(\frac32)^2+(\frac12)^2=\frac52$,
  so $|\rho-c|<1.59<\frac74$: it is counted.
* By (Z3), $\rho\mapsto1-\bar\rho=(1-\beta)+i\gamma$ maps the zeros with $0<\beta<\frac12$ injectively, with the
  same multiplicity and ordinate, to zeros with $\frac12<\beta<1$.

Hence $N[T,T+1]\le2\log\bigl(6(T+5)^2/0.35\bigr)/\log\frac{22}{21}\le C\log(T+2)$ (use $T+5\le\frac52(T+2)$ and
$\log(T+2)\ge\log2$). $\square$

In Lean the left side is `zetaZeroesSum (Set.Ioo 0 1) (Set.Icc T (T+1)) (fun _ ↦ 1)`, a finite sum by Mathlib's
`IsCompact.inter_riemannZetaZeros_finite` (at the pin; the library's `WeilExplicitFormula.zetaZeroesIn_finite` and
`zetaZeroesSum_eq_sum` already do this for the library's verbatim copy of `zetaZeroesSum`). It is at most twice the sum over the zeros with $\frac12\le\beta<1$, which
is at most the `divisor` sum of (J); at $\rho\ne1$ the divisor of `riemannZeta₁` is `zetaOrder ρ`.

## 3. The local expansion: $\frac12\le\sigma\le2$, $|t|\ge2$

Apply (L) to $F(z)=\zeta(s_0+\frac{15}8z)$, $s_0=2+it$, with $r=\frac45$ and $R=\frac9{10}$.

* $F$ is analytic on a neighbourhood of $|z|\le1$: the pole $s=1$ is at distance $\sqrt{1+t^2}\ge\sqrt5>\frac{15}8$
  from $s_0$ (`differentiableAt_riemannZeta`).
* For $|s-s_0|\le\frac{15}8$: $\sigma\ge\frac18$, $|s-1|\ge|\Im s|\ge|t|-\frac{15}8\ge\frac18$ and $|s|\le|t|+4$,
  so by (Z1) $|\zeta(s)|\le8|s|+8|s|\le16(|t|+4)=:M$.
* $|F(0)|=|\zeta(2+it)|\ge0.35$ by (Z2), so $\log(M/|F(0)|)\le\log(46(|t|+4))\ll\log|t|$.
* $|z|\le\frac45$ is $|s-s_0|\le\frac32$, which contains the segment $\frac12\le\sigma\le2$ at height $t$. The zeros
  in the sum are those with $|\rho-s_0|\le\frac9{10}\cdot\frac{15}8=\frac{27}{16}$; they have $|\gamma-t|<2$ and
  $\beta\ge2-\frac{27}{16}>0$, so $0<\beta<1$.
* $F'/F(z)=\frac{15}8\frac{\zeta'}\zeta(s)$ and $\frac1{z-z_k}=\frac{15/8}{s-\rho}$. Dividing by $\frac{15}8$:

$$\Bigl|\frac{\zeta'}{\zeta}(s)-\sum_{|\rho-s_0|\le27/16}\frac{m_\rho}{s-\rho}\Bigr|\le C_1\log|t|
\qquad(\tfrac12\le\sigma\le2,\ |t|\ge2,\ \zeta(s)\ne0).$$

## 4. Lemma 12.2

Let $T\ge2$.

**Choice of $T_1$.** Let $Z$ be the zeros with $0<\beta<1$ and $T-2\le\gamma\le T+3$, and $n_Z$ their number with
multiplicity. By §2 on $[T-2+j,T-1+j]$, $j=0,\dots,4$ (all with $T-2+j\ge0$): $n_Z\le5C\log(T+4)\le C_2\log T$.
Cut $[T,T+1]$ into $2n_Z+1$ closed pieces of length $\ell=1/(2n_Z+1)$. Each ordinate lies in at most two pieces, so
some piece contains no ordinate of $Z$; let $T_1$ be its midpoint. Then $|T_1-\gamma|\ge\eta:=\ell/2$ for every
$\rho\in Z$ (including those with $\gamma\notin[T,T+1]$), and $1/\eta=2(2n_Z+1)\ll\log T$. (Equivalently, by measure:
the $\eta$-neighbourhoods of the ordinates have total length $2\eta n_Z<1$ once $\eta<1/(2n_Z)$.)

**No zeros on the segment.** For $-1\le\sigma\le2$, $\zeta(\sigma+iT_1)\ne0$:
* $0<\sigma<1$: such a zero would be in $Z$ with $\gamma=T_1$;
* $\sigma\ge1$: `riemannZeta_ne_zero_of_one_le_re`;
* $\sigma\le0$: with $w=1-s$ ($\Re w\ge1$, $\Im w=-T_1\ne0$), `riemannZeta_one_sub` at $w$ gives
  $\zeta(s)=2(2\pi)^{-w}\Gamma(w)\cos(\pi w/2)\zeta(w)$, and each factor is non-zero ($\Gamma$:
  `Complex.Gamma_ne_zero_of_re_pos`; $\cos$: $\pi w/2$ is not real; $\zeta(w)$: `riemannZeta_ne_zero_of_one_le_re`).
  (This is the argument of `ZetaZeroes.v1.no_nontrivial_zeroes_left`, which covers only $\sigma<0$.)

**$\frac12\le\sigma\le2$.** By §3 at $t=T_1$: the zeros in the sum have $|\gamma-T_1|<2$, so they lie in $Z$, and
$|s-\rho|\ge|T_1-\gamma|\ge\eta$. Hence
$$\Bigl|\frac{\zeta'}\zeta(\sigma+iT_1)\Bigr|\le\frac{n_Z}\eta+C_1\log T_1\le2n_Z(2n_Z+1)+2C_1\log T\le C_3\log^2T.$$

**$-1\le\sigma<\frac12$.** Apply (FE) at $s=\sigma+iT_1$: $s$ is not real, so $s\ne1$, $s\notin\{0,-1,\dots\}$ and
$\cos(\pi s/2)\ne0$; and $\zeta(s)\ne0$ was shown. Then:
* $1-s=(1-\sigma)-iT_1$, $\frac12<1-\sigma\le2$. By `riemannZeta_conj` (and hence $\zeta'(\bar w)=\overline{\zeta'(w)}$),
  $|\frac{\zeta'}\zeta(1-s)|=|\frac{\zeta'}\zeta((1-\sigma)+iT_1)|\le C_3\log^2T$.
* $\psi(s)=\psi(s+2)-\frac1s-\frac1{s+1}$ (`Complex.digamma_apply_add_one` twice), with $1\le\Re(s+2)<\frac52$ and
  $\Im(s+2)=T_1\le T+1$; by (D), $|\psi(s)|\le C_D\log(T+3)+1\ll\log T$.
* $|\tan(\pi s/2)|\le\coth(\pi T_1/2)\le\coth\pi<1.01$, from
  $|\tan(x+iy)|^2=\frac{\sin^2x+\sinh^2y}{\cos^2x+\sinh^2y}\le\coth^2y$ (and $\pi T_1/2\ge\pi$).

So $|\frac{\zeta'}\zeta(\sigma+iT_1)|\le C_3\log^2T+\log2\pi+O(\log T)+\frac\pi2\cdot1.01\le C\log^2T$. $\square$

## 5. Imports of `ZetaGoodHeights.v1`

* `theorem_10_13`: nothing (`imports: []`): Mathlib and the pinned library suffice.
* `lemma_12_2`: `ZetaLogDeriv.v1.logDeriv_functional_equation`. Everything else is Mathlib or the pinned library, (D)
  included. (Until 27 November both also imported `ZetaZeroes.v1.finite_zeroes_on_compact`; Mathlib's
  `IsCompact.inter_riemannZetaZeros_finite` does the same job.)

On 26 November `lemma_12_2` also imported `GammaAsymptotics.v1`, which is unproved, so `lemma_12_2` and Theorem 12.13
would have been conditional on it. On 27 November Harald decided that the other chat adds (D) to the library instead
(blueprint §4, decision 4), so that import is gone.

## 6. Where this is done (decided by Harald, 27 November 2026)

In the Riemann–Stieltjes library, by the other chat, against the verbatim copies `WeilExplicitFormula.Theorem_10_13`
and `WeilExplicitFormula.Lemma_12_2` in `Mathlib/NumberTheory/WeilExplicitFormula/ExplicitFormula.lean` (branch
`mv-lemma-12-14`), which are what `theorem_12_13_of` takes as hypotheses. The fork's Mathlib has every name used above
(checked on that branch), except:
* `riemannZeta₁`, `differentiable_riemannZeta₁`, `riemannZeta₁_one`, `riemannZeta_eq_inv_sub_mul`. Use
  `Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1`, analytic at $1$ by `riemannZeta_residue_one` and
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (both on the fork);
* Mathlib's `riemannZeta_conj` (for all $s$). Use the library's `WeilExplicitFormula.riemannZeta_conj` ($s\ne1$) and
  its companions in `Xi.lean` (`deriv_`, `logDeriv_`, `analyticOrderAt_riemannZeta_conj`).

The functional equation of $\zeta'/\zeta$ (IEANTN `ZetaLogDeriv.v1.logDeriv_functional_equation`, which `lemma_12_2`
imports) is not on the fork. Either take its statement as a hypothesis, copied verbatim as was done for
`ResidueTheoremRectangle`, so that the IEANTN solution of `lemma_12_2` again comes by unfolding definitions; or prove it
from `riemannZeta_one_sub` and drop the import. Whichever is chosen, the node's `imports` must say so.

## Appendix A. `GammaAsymptotics.v1` from the Gauss representation

*Optional since 27 November 2026: nothing on our path uses it. Kept as a possible contribution to IEANTN (which
would need Harald's go-ahead). The library's `Complex.hasSum_digamma` (other chat) is the same Gauss series and can
replace Tao's lemma below.*

The `GammaAsymptotics.v2` solution (T. Tao) proves, in `Solutions/GammaAsymptotics.v2/Analytic.lean`,
`GammaSolution.digamma_eq_gaussSum : 0 < s.re → Complex.digamma s = gaussSum s`, where
`gaussSum s = -γ + ∑' k, (1/(k+1) - 1/(k+s))`. The docstring of `GammaAsymptotics.v2` says v1 needs, beyond this,
"a further uniformity argument as `Im w → ∞`". Here it is.

Let $\Re w=u\ge1$ and $f(x)=1/(x+w)$ for $x\ge0$. For $y\ge0$, $|y+w|^2=(y+u)^2+v^2\ge y^2+|w|^2$. Write
$$\sum_{k<N}f(k)=\int_0^Nf+E_N,\qquad E_N=\sum_{k<N}\int_k^{k+1}\bigl(f(k)-f(x)\bigr)dx,
\qquad\int_0^Nf=\log(N+w)-\log w$$
(principal logarithm; $x+w$ stays in $\Re>0$). For $x\in[k,k+1]$, $|f(k)-f(x)|\le\max_{[k,k+1]}|f'|\le1/(k^2+|w|^2)$,
so $E_N\to E$ with
$$|E|\le\sum_{k\ge0}\frac1{k^2+|w|^2}\le\frac1{|w|^2}+\int_0^\infty\frac{dy}{y^2+|w|^2}=\frac1{|w|^2}+\frac\pi{2|w|}
\le\frac3{|w|}.$$
Now $\sum_{k<N}\bigl(\frac1{k+1}-\frac1{k+w}\bigr)=\bigl(H_N-\log N\bigr)-\bigl(\log(N+w)-\log N\bigr)+\log w-E_N$, and
$H_N-\log N\to\gamma$ (`Real.tendsto_harmonic_sub_log`), $\log(N+w)-\log N=\log(1+w/N)\to0$. So the Gauss
representation gives $\psi(w)=\log w-E$, i.e. $\|\psi(w)-\log w\|\le3/\|w\|$ for $\Re w\ge1$: `digamma_sub_log_isBigO`
with $C=3$.
