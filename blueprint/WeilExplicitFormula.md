# Weil's explicit formula, Montgomery–Vaughan Theorem 12.13 with $q=1$: formalization blueprint

Draft of 23 November 2026, revised 26 November 2026, written by Claude for H. Helfgott. **Nothing here has been
compiled**: the sandbox where it was written cannot download Lean or Mathlib's build cache. The Lean files in
`blueprint/drafts/` contain statements only (`sorry` everywhere), and `blueprint/ieantn/` contains drafts of IEANTN
nodes; their purpose is to fix the interfaces. `blueprint/HANDOFF.md` is the task list for Claude Code.

Names of existing declarations were checked by `grep` in branch `dirichlet-jordan` of `Garald1/mathlib-at-ICERM26`
(commit `90f274f`, Lean v4.30.0-rc2); the Mathlib files that the plan relies on (Jensen, Borel–Carathéodory,
`extract_zeros_poles`, digamma) were also checked to exist at IEANTN's Mathlib pin (`71a80585`). IEANTN nodes and
solutions were checked in `teorth/IEANTN` at commit `cd9c2dd` (23 November 2026); PrimeNumberTheoremAnd (PNT+) in
the files of its `main` branch on 23 November.

References: [MV] = Montgomery–Vaughan, *Multiplicative Number Theory I* (2007). All theorem, lemma and equation
numbers of [MV] quoted below were checked against the text of the book.

## 0. The statement

**Hypotheses** ([MV, Theorem 12.13]). $\delta_0>0$; $F:\mathbb R\to\mathbb C$ measurable, with
$$\int e^{(\frac12+\delta_0)2\pi|x|}|F(x)|\,dx<\infty \quad(12.20),\qquad
\int e^{(\frac12+\delta_0)2\pi|x|}|dF(x)|<\infty\quad(12.21),$$
$F(x)=\frac12(F(x-)+F(x+))$ for all $x$, and $F(x)+F(-x)=2F(0)+O(|x|)$ (as $x\to0$).
Put $\Phi(s)=\int F(x)e^{-(s-1/2)2\pi x}\,dx$ for $-\delta_0<\sigma<1+\delta_0$.

**Conclusion** for $q=1$ ($\chi=\chi_0$, $E_0=1$, $\kappa=0$, $\log(q/\pi)=-\log\pi$), from (12.22):
$$\lim_{T\to\infty}\sum_{|\gamma|\le T}\Phi(\rho)=\Phi(0)+\Phi(1)+\frac{F(0)}{2\pi}\Bigl(\frac{\Gamma'}{\Gamma}(\tfrac14)-\log\pi\Bigr)
-\frac1{2\pi}\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}\Bigl(F\bigl(-\tfrac{\log n}{2\pi}\bigr)+F\bigl(\tfrac{\log n}{2\pi}\bigr)\Bigr)
+\int_0^\infty\frac{e^{-\pi x}}{1-e^{-4\pi x}}\bigl(2F(0)-F(x)-F(-x)\bigr)dx ,$$
the sum running over the non-trivial zeros $\rho=\beta+i\gamma$ of $\zeta$, with multiplicity.

**Form of the hypotheses used in Lean.** With $a=(\frac12+\delta_0)2\pi$ and $G(x)=e^{a|x|}F(x)$:
(12.20) and (12.21) together are equivalent to "$G$ is integrable and of bounded variation on $\mathbb R$".
($\Rightarrow$ is the remark that follows Theorem 12.13 in [MV]; $\Leftarrow$: $dF=e^{-a|x|}dG+G\,d(e^{-a|x|})$, so
$\int e^{a|x|}|dF|\le\int|dG|+a\int|G|$.) This avoids variation measures: everything is stated with
`Integrable` and `BoundedVariationOn _ Set.univ`, as in `Stieltjes/Fourier.lean`.

**What the Mertens note needs.** Proposition 2.2 of the note applies the formula to
$F(x)=e^{2\pi itx}\widehat m(x)$, which is continuous, Lipschitz and supported in $|x|\le\frac{\log N}{2\pi}$. Such an
$F$ satisfies the hypotheses for every $\delta_0>0$ (lemma E0). Restricting the theorem to such $F$ would make $\Phi$
entire and the prime sum finite, but it would not remove any of the hard parts (A, B4–B5, C4–C7), so I propose to
formalize the theorem as stated and to add E0 as a corollary. (Beyond Theorem 12.13, the proof of Proposition 2.2 also
uses Hadamard's factorization of $\xi$ [MV, Theorem 10.12] and Gauss's integral for $\Gamma'/\Gamma$; these are not
part of this blueprint.)

## 1. MV's proof for $q=1$, step by step

Let $\xi(s)=\frac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ [MV, (10.5)], fix $0<\delta_1<\delta_0$.

1. $T_1$ with $|T-T_1|\le1$ and $\frac{\xi'}{\xi}(\sigma\pm iT_1)\ll(\log T)^2$ for $-1\le\sigma\le2$. (C7)
2. Argument principle on the rectangle with vertices $-\delta_1\pm iT_1$, $1+\delta_1\pm iT_1$:
   $\sum_{|\gamma|\le T_1}\Phi(\rho)=\frac1{2\pi i}\oint\Phi\,\frac{\xi'}{\xi}$. (D1)
   The horizontal sides are $O((\log T)^2/T)$ by step 1 and $\Phi(s)\ll1/(|t|+1)$ (E3).
3. $\frac{\xi'}{\xi}(s)=-\frac{\xi'}{\xi}(1-s)$ turns the left side into the right one: (12.23) becomes
   $\frac1{2\pi i}\int_{1+\delta_1-iT}^{1+\delta_1+iT}(\Phi(s)+\Phi(1-s))\frac{\xi'}{\xi}(s)\,ds$. (C1)
4. (10.25): $\frac{\xi'}{\xi}(s)=\frac1s+\frac1{s-1}+\frac{\zeta'}{\zeta}(s)+\frac12\frac{\Gamma'}{\Gamma}(\frac s2)-\frac12\log\pi$. (C3)
5. $\zeta'/\zeta$ part: on $\sigma=1+\delta_1$, $(\Phi(s)+\Phi(1-s))\frac{\zeta'}{\zeta}(s)=\widehat H(t)$ with
   $H(x)=-\sum_n\Lambda(n)n^{-1/2}\bigl(F(x-\frac{\log n}{2\pi})+F(-x+\frac{\log n}{2\pi})\bigr)e^{-(\frac12+\delta_1)2\pi x}$
   ((12.25), (12.26)); $H$ is integrable, of bounded variation and normalized, so by the Fourier integral theorem
   $\lim_T\int_{-T}^T\widehat H=H(0)$, which gives the prime sum. (F1–F3, A5)
6. The rest, $G(s)=\bigl(\frac1s+\frac1{s-1}-\frac12\log\pi+\frac12\frac{\Gamma'}{\Gamma}(\frac s2)\bigr)(\Phi(s)+\Phi(1-s))$,
   is moved to $\sigma=\frac12$ by Cauchy's theorem, picking up $\Phi(0)+\Phi(1)$ at $s=1$. (G4)
7. On $\sigma=\frac12$: the $\frac1s+\frac1{s-1}$ term integrates to $0$ (odd integrand); the $\log\pi$ term tends to
   $-\frac{\log\pi}{2\pi}F(0)$ (A5 applied to $F$); the $\Gamma'/\Gamma$ term is Lemma 12.14 with $a=\frac14$,
   $b=\frac12$, $J(x)=F(x)+F(-x)$. (G5, B5)
8. Replace $T_1$ by $T$: the zeros with $T<|\gamma|\le T_1$ contribute $O((\log T)/T)$ (C4, E3). (G6)

Lemma 12.14 [MV]: for fixed $a,b>0$ and $J\in L^1(\mathbb R)$ of bounded variation with $J(x)=J(0)+O(|x|)$,
$$\lim_{T\to\infty}\int_{-T}^T\frac{\Gamma'}{\Gamma}(a\pm ibt)\widehat J(t)\,dt=\frac{\Gamma'}{\Gamma}(a)J(0)
+\frac{2\pi}b\int_0^\infty\frac{e^{-2\pi ax/b}}{1-e^{-2\pi x/b}}\bigl(J(0)-J(\mp x)\bigr)dx\qquad(12.27).$$
(The factor is $2\pi/b$; it is what makes the last term of (12.22) come out with coefficient $1$ when $b=\frac12$.)
MV prove it from Theorem C.5 (the integral $\int_{-T}^T\frac{\Gamma'}{\Gamma}(a+ibt)e(-xt)dt$, by a contour shift
through the poles of $\Gamma'/\Gamma$), first for $J(0)=0$ (cutting at $|x|=\delta=T^{-2/3}$), then in general by
subtracting $J(0)e^{-\pi x^2/A}$ and letting $A\to\infty$.

## 2. Lemmas

(The labels A1, …, G6 are lemmas of this blueprint, not IEANTN nodes.) Status: **M** = in Mathlib (the
`dirichlet-jordan` snapshot), **H** = in the `dirichlet-jordan` branch (ICERM files), **L** = proved in the
`mv-lemma-12-14` branch (the other chat's files, on top of `dirichlet-jordan`; added 27 November 2026), **I** = in
IEANTN, **P** = in PNT+ (would have to be ported), **new** = to be written.

### A. Fourier integral theorem (integral analogue of Dirichlet–Jordan)

Plan: exactly the route of `DirichletJordan.lean`: Fejér for integrals + Hardy's Tauberian theorem + $\widehat H(t)=O(1/|t|)$.

- **A1** $\|\widehat g(\xi)\|\le\frac{V(g)}{2\pi|\xi|}$ for $g\in L^1\cap BV(\mathbb R)$, $\xi\ne0$.
  **H**: `FourierTransform.fourier_bounded_variation`.
- **A2** Fejér kernel on $\mathbb R$: for $T>0$, $\int_{-T}^T(1-\frac{|t|}T)e(ty)\,dt=K_T(y):=T\,\mathrm{sinc}(\pi Ty)^2$;
  $K_T\ge0$, even, $\int K_T=1$, $\int_{|y|\ge\eta}K_T\le\frac{2}{\pi^2T\eta}$. **new** (`Real.sinc` is **M**;
  $\int K_T=1$ can be obtained from `Continuous.fourierInv_fourier_eq` (**M**) applied to the triangle function).
- **A3** Fejér's theorem for Fourier integrals: $g\in L^1$ with one-sided limits $\ell_\pm$ at $x$ ⇒
  $\int_{-T}^T(1-\frac{|t|}T)\widehat g(t)e(tx)\,dt=\int g(x-y)K_T(y)\,dy\to\frac{\ell_++\ell_-}2$. **new**
  (parallel to `FourierSeries.tendsto_fejerMean_of_tendsto`, **H**).
- **A4** Hardy's Tauberian theorem for integrals: $u$ locally integrable on $[0,\infty)$, $|u(t)|\le A/t$ for $t\ge1$,
  $\frac1T\int_0^T\!\!\int_0^v u\,dv\to s$ ⇒ $\int_0^T u\to s$. **new**, by reduction to the discrete case
  `tendsto_sum_range_of_tendsto_cesaroMean` (**H**, `SpecificLimits/Cesaro.lean`) with $u_k=\int_k^{k+1}u$.
- **A5** **Fourier integral theorem**: $g\in L^1\cap BV(\mathbb R)$ ⇒ for every $x$,
  $\lim_{T\to\infty}\int_{-T}^T\widehat g(t)e(tx)\,dt=\frac{g(x+)+g(x-)}2$; at a normalized point this is $g(x)$.
  **new** (A1+A3+A4; one-sided limits of BV functions as in `tendsto_rightLim_of_periodic`, **H**).
- **A6** (by-product, as (12.50)(c)) $\sup_{T,x}|\int_{-T}^T\widehat g(t)e(tx)\,dt|<\infty$. **new**, optional.

*Update, 27 November 2026:* A2–A6 are **L**: `Stieltjes/FourierIntegral.lean` (branch `mv-lemma-12-14`, commit
`3992e7d7`) proves every statement of `drafts/FourierIntegral.lean` (twelve theorems, three definitions; checked
here to be textually identical, namespace `FourierIntegral`), e.g. A5 = `tendsto_partialInv` and
`tendsto_partialInv_of_normalized`, A6 = `exists_norm_partialInv_le`.

### B. The digamma function $\psi=\Gamma'/\Gamma$ ([MV, Appendix C])

`Complex.digamma = logDeriv Gamma` is **M** (`Gamma/Digamma.lean`, with `digamma_one`, `digamma_one_half`,
`digamma_apply_add_one`).
- **B1** (C.10) $\psi(s)=-\frac1s-C_0-\sum_{n\ge1}\bigl(\frac1{s+n}-\frac1n\bigr)$ for $s\ne0,-1,-2,\dots$
  **I**: already proved in IEANTN's `Solutions/GammaAsymptotics.v2/Analytic.lean` as `digamma_eq_gaussSum`
  (for $\operatorname{Re}s>0$; the general case follows by the recurrence). **L**, proved independently:
  `Complex.hasSum_digamma` ($\operatorname{Re}s>0$) in `SpecialFunctions/Gamma/DigammaSeries.lean`; use that one.
  The draft's form (all $s\ne0,-1,\dots$) is not proved, and nothing needs it.
- **B2** $\psi'(s)=\sum_{n\ge0}(n+s)^{-2}$; hence $\psi'(a+iy)\ll_a1/|y|$ for $|y|\ge1$. **L** for
  $\operatorname{Re}s>0$: `Complex.hasSum_deriv_digamma`; on vertical lines `Complex.norm_deriv_digamma_le'`,
  $|\psi'(a+it)|\le2(\frac1{m^2}+\frac1m)/(1+|t|)$ with $m=\min(a,1)$. The draft's statement, uniform in
  $\sigma\in\mathbb R$, is not proved; only B4 used B2.
- **B3** For fixed $a,b>0$: $\psi(a+ibt)\ll\log(|t|+2)$ and $\psi(a+ibt)=\psi(a)+O(|t|)$ for $|t|\le1$; also
  $\psi(\sigma+it)\ll\log(|t|+2)$ uniformly for $\frac14\le\sigma\le2$ (needed in C7, G2, G4). Imported from the
  IEANTN node `GammaAsymptotics.v1` ($\psi(w)=\log w+O(1/|w|)$ for $\operatorname{Re}w\ge1$; statement only, awaiting a
  solution) and the recurrence. (Planned on 26 November: a solution for `GammaAsymptotics.v1`, from B1. Superseded;
  see the update below.)
  *Update, 27 November 2026.* The second statement is **L**: `Complex.exists_norm_digamma_sub_le`, under the draft's
  name. The first (draft name `exists_norm_digamma_le_log`, uniform for $\sigma\in[\sigma_1,\sigma_2]\subset(0,\infty)$)
  is not proved yet, but is a few lines from **L** `Complex.norm_digamma_sub_le`:
  $\|\psi(a+it)-\psi(a)\|\le2(\frac1{m^2}+\frac1m)\log(1+|t|)$, $m=\min(a,1)$, together with the boundedness of $\psi$
  on $[\sigma_1,\sigma_2]$. Harald's decision (§4, decision 4): the other chat adds it to the library, under the draft's
  name and statement; nothing here imports `GammaAsymptotics.v1` any more. Done: **L**,
  `Complex.exists_norm_digamma_le_log` in `Gamma/DigammaSeries.lean` (commit `77ccfc1e`), the draft's statement.
- **B4** [MV, Theorem C.5]: for $a,b>0$, $x\ne0$, $T\ge1$,
  $\int_{-T}^T\psi(a+ibt)e(-xt)\,dt=-\psi(a+ibT)\frac{e(-xT)}{2\pi ix}+\psi(a-ibT)\frac{e(xT)}{2\pi ix}
  -\mathbf 1_{x<0}\frac{2\pi}b\frac{e^{2\pi ax/b}}{1-e^{2\pi x/b}}+O\bigl(\frac1{x^2T}\bigr)$.
  **new**. Contour shift to $\sigma\to-\infty$ (if $x<0$) or $+\infty$ (if $x>0$) through the simple poles of
  $\psi(a+bs)$ (residue $-1/b$): rectangles $[-R_k,0]\times[-T,T]$ with $R_k\to\infty$ between poles, the
  far side tends to $0$. Needs a residue theorem for finitely many simple poles in a rectangle (D2).
  *Update:* **L**, `Complex.exists_integral_digamma_mul_exp` (`Stieltjes/DigammaPairing.lean`, restating
  `Complex.norm_integral_digamma_line_mul_cexp_sub_le` of `Gamma/DigammaFourier.lean`). It was proved by integrating by
  parts twice and Fourier inversion, without residues, so B4 does not need D2.
- **B5** [MV, Lemma 12.14], (12.27). **new**. MV's proof uses B3, B4, Fubini, and Gaussian subtraction
  (the Gaussian's Fourier transform is **M**: `fourier_gaussian_pi`, `fourierIntegral_gaussian` in
  `Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`). *Update:* **L**, both signs:
  `Complex.tendsto_integral_digamma_mul_fourier` and `Complex.tendsto_integral_digamma_conj_mul_fourier`, under the
  draft's names.

### C. $\xi$ and the zeros of $\zeta$

- **C1** $\xi(s)=\frac12\bigl(s(s-1)\Lambda_0(s)+1\bigr)$ with $\Lambda_0$ = `completedRiemannZeta₀` (**M**, entire:
  `differentiable_completedZeta₀`); this equals [MV, (10.5)] for $s\ne0,1$. $\xi(1-s)=\xi(s)$ from
  `completedRiemannZeta₀_one_sub` (**M**); $\xi(\bar s)=\overline{\xi(s)}$. **new** (short).
- **C2** Zeros of $\xi$ = zeros of $\zeta$ in $0<\sigma<1$, with the same orders; none with $\sigma\le0$ or
  $\sigma\ge1$. **new**, using `riemannZeta_ne_zero_of_one_le_re` (**M**), C1, and $\Gamma(s/2)\pi^{-s/2}\ne0$.
  Imported from IEANTN's `ZetaZeroes.v1` (proved, with receipts): `finite_zeroes_on_compact`,
  `no_nontrivial_zeroes_left`, `zeroes_off_axis_in_strip`.
- **C3** (10.25) $\frac{\xi'}{\xi}=\frac1s+\frac1{s-1}+\frac{\zeta'}{\zeta}+\frac12\psi(\frac s2)-\frac12\log\pi$
  where $\xi\ne0$. **new** (short).
- **C4** [MV, Theorem 10.13]: the number of zeros (with multiplicity) with $T\le\gamma\le T+1$ is $\ll\log(T+2)$.
  To be a conclusion of the new IEANTN node `ZetaGoodHeights.v1` (draft in `blueprint/ieantn/`). Proof
  from Jensen's inequality [MV, Lemma 6.1] = `AnalyticOnNhd.sum_divisor_le` (**M**,
  `Analysis/Complex/JensenFormula.lean`) applied to $(s-1)\zeta(s)$ on a disc centred at $2+i(T+\frac12)$ (and the
  symmetry $\rho\mapsto1-\bar\rho$). Inputs: $|\zeta(s)|\ll|t|$ for $\sigma\ge\frac18$, $|t|\ge1$ (**P** has such bounds,
  via `Zeta0EqZeta` in `ZetaBounds.lean`), and $|\zeta(2+it)|\ge2-\zeta(2)>0.35$. Detailed proof:
  `blueprint/proofs/GoodHeights.md`, §2.
- **C5** [MV, Lemma 6.3] (Landau): $f$ analytic on $|z|\le1$, $|f|\le M$, $f(0)\ne0$, $0<r<R<1$ ⇒ for $|z|\le r$,
  $\frac{f'}f(z)=\sum_{|z_k|\le R}\frac1{z-z_k}+O_{r,R}(\log\frac M{|f(0)|})$. **new**, from Borel–Carathéodory
  [MV, Lemma 6.2] = `Complex.borelCaratheodory` (**M**) and `MeromorphicOn.extract_zeros_poles` (**M**). Prove it with
  $1+\log\frac M{|f(0)|}$ in the error term, which is all that is needed and avoids the degenerate case
  $M=|f(0)|$; proof step by step in `blueprint/proofs/GoodHeights.md`, (L).
- **C6** Local partial fractions: for $|t|\ge2$, $\frac12\le\sigma\le2$:
  $\frac{\zeta'}{\zeta}(s)=\sum_{|\gamma-t|\le1}\frac1{s-\rho}+O(\log|t|)$. **new** (C5 on discs centred at $2+it$;
  compare [MV, Lemma 12.1], which MV derive from the Hadamard product, via (10.29) and Corollary 10.14, remarking that
  the method of their Lemma 6.4 would also do). `proofs/GoodHeights.md` §3 proves the version with the sum over
  $|\rho-(2+it)|\le\frac{27}{16}$, which is what C7 uses; the two sums differ by $O(\log|t|)$ there.
- **C7** Good heights ([MV, Lemma 12.2], which is the conclusion `lemma_12_2` of the new node `ZetaGoodHeights.v1`,
  then transferred to $\xi'/\xi$): for $T\ge2$ there is $T_1\in[T,T+1]$ with
  $|\frac{\xi'}{\xi}(\sigma\pm iT_1)|\le C(\log T)^2$ for $-1\le\sigma\le2$, and no zero has ordinate $\pm T_1$.
  **new**: pigeonhole with C4 gives $|T_1-\gamma|\gg1/\log T$; then C6, C3, B3 for $\frac12\le\sigma\le2$, and C1
  ($\frac{\xi'}{\xi}(s)=-\frac{\xi'}{\xi}(1-s)$, conjugation) for $-1\le\sigma\le\frac12$. The conclusion
  `lemma_12_2` itself is about $\zeta'/\zeta$, as in [MV]; for $-1\le\sigma<\frac12$ it is proved from the functional
  equation of $\zeta'/\zeta$ (IEANTN `ZetaLogDeriv.v1`, proved) and B3. Detailed proof: `proofs/GoodHeights.md` §4.

### D. Contour integration on rectangles

Rectangle integrals: `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (**M**, Cauchy–Goursat);
`RectangleIntegral`, `RectangleIntegralHSplit`, `ResidueTheoremOnRectangleWithSimplePole` (**P**,
`ResidueCalcOnRectangles.lean`).
- **D1** Argument principle with a weight: $f$ analytic near the closed rectangle $R$, no zeros on $\partial R$,
  $\varphi$ analytic near $R$ ⇒ $\frac1{2\pi i}\oint_{\partial R}\varphi\frac{f'}f=\sum_{\rho\in R^\circ}
  \mathrm{ord}_\rho(f)\varphi(\rho)$. **new**: `MeromorphicOn.extract_zeros_poles` (**M**) writes
  $f=\prod(s-\rho)^{m_\rho}g$ with $g$ analytic and zero-free near $R$; Cauchy for $\varphi g'/g$; D2 for
  $\varphi(s)/(s-\rho)$.
- **D2** Residue theorem on rectangles, residues written as circle integrals: the IEANTN node
  `ContourIntegration.v1` (`residue_theorem_rectangle`; statement only, currently inactive, the first thing IEANTN
  says to reactivate when a node needs contour integration). **To do: reactivate it and give it a solution**
  (PNT+'s rectangle lemmas, ported with credit, and Mathlib's annulus invariance). Needed for D1 and G4; B4 turned
  out not to need it.

### E. The test function and $\Phi$

- **E0** Continuous, Lipschitz, compactly supported $F$ satisfy the hypotheses for every $\delta_0>0$. **new** (easy).
- **E1** Hypotheses ⇒ $e^{c|x|}F$ integrable and BV for $0\le c\le a$; $|F(x)|\ll e^{-a|x|}$. **new**.
- **E2** $\Phi$ is holomorphic on $-\delta_0<\sigma<1+\delta_0$, continuous on the closed strip;
  $\Phi(\sigma+it)=\widehat{g_\sigma}(t)$ with $g_\sigma(x)=F(x)e^{(1-2\sigma)\pi x}$; in particular
  $\Phi(\frac12+it)=\widehat F(t)$; and $\Phi(1-s)=\Phi_{F(-\cdot)}(s)$. **new**.
- **E3** $\Phi(s)\ll1/(|t|+1)$ uniformly for $-\delta_0\le\sigma\le1+\delta_0$ (remark after Theorem 12.13 in [MV]).
  **new**: A1 applied to $g_\sigma$, whose variation is bounded uniformly in $\sigma$.

### F. The Dirichlet series part

- **F1** (12.25)–(12.26) for $q=1$: for $1<\sigma<1+\delta_0$,
  $\Phi(s)\frac{\zeta'}{\zeta}(s)=-\sum_n\Lambda(n)n^{-1/2}\int F(x-\frac{\log n}{2\pi})e^{-(s-\frac12)2\pi x}dx$ and
  similarly for $\Phi(1-s)\frac{\zeta'}{\zeta}(s)$. **new**: `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (**M**)
  and Fubini (the bound displayed in [MV] after (12.26)).
- **F2** $H\in L^1\cap BV(\mathbb R)$, $H$ normalized, $\widehat H(t)=(\Phi(s)+\Phi(1-s))\frac{\zeta'}{\zeta}(s)$
  at $s=1+\delta_1+it$. **new** (variation bound as in [MV]: translation invariance + $\sum\Lambda(n)n^{-1-\delta_1}<\infty$).
- **F3** $\lim_T\frac1{2\pi i}\int_{1+\delta_1-iT}^{1+\delta_1+iT}(\Phi(s)+\Phi(1-s))\frac{\zeta'}{\zeta}(s)ds
  =\frac{H(0)}{2\pi}$. **new** (A5).

### G. Assembly

- **G1** Steps 1–2 above (D1 with $f=\xi$, $\varphi=\Phi$; C2, C7).
- **G2** Horizontal sides: $O((\log T)^2/T)$ (C7, E3).
- **G3** (12.23) (C1).
- **G4** Cauchy for $G(s)$ between $\sigma=\frac12$ and $\sigma=1+\delta_1$; residue $\Phi(0)+\Phi(1)$ at $s=1$;
  horizontal sides $O(\log T/T)$ (B3, E3). **new** (D2).
- **G5** The three terms on $\sigma=\frac12$ (A5, B5).
- **G6** From $T_1$ to $T$ (C4, E3). Main theorem.

*Update, 27 November 2026 (afternoon).* C1–C3, D1, E0–E3, F1–F3 and G1–G6 are **L**: eight files in
`Mathlib/NumberTheory/WeilExplicitFormula/` (about 2,900 lines; branch `mv-lemma-12-14`, commits `9a234c7f`,
`dd112489`, `737b220f`). The end result is
`WeilExplicitFormula.theorem_12_13_of (h1013 : Theorem_10_13) (h122 : Lemma_12_2) (hres : ResidueTheoremRectangle) :
Theorem_12_13`, where the conclusion and the three hypotheses are the statements of `WeilExplicitFormula.v1.theorem_12_13`,
`ZetaGoodHeights.v1.theorem_10_13`, `ZetaGoodHeights.v1.lemma_12_2` and `ContourIntegration.v1.residue_theorem_rectangle`,
and IEANTN's `zetaZeroesIn`, `zetaOrder`, `zetaZeroesSum` are copied too (all checked here to be verbatim, except that
`Phi` writes `π` for `Real.pi`). Kept from `drafts/WeilExplicitFormula.lean`: the names and statements of
`IsTestFunction`, `Phi`, E0, E2, E3, `H`, F2, `riemannXi`, C1–C3 and `rhs`. Departures: D1 is
`rectIntegral_mul_logDeriv_eq_sum` (it takes the residue theorem as a hypothesis and sums over a `Finset` of points
containing the zeros); G1 and the final theorem use `zetaZeroesSum`, so the drafts' `sum_zeros_eq_rectIntegral`,
`tendsto_sum_zeros` and `tendsto_sum_riemannZeta_zeros` are not proved as written, and neither are `riemannXi_conj`
and `zeroMult` (not needed). F3 is `IsTestFunction.tendsto_integral_Phi_mul_logDeriv`; G5 is
`IsTestFunction.tendsto_integral_gammaFactor_half`.

## 3. Order of work

See `blueprint/HANDOFF.md`, which turns this into tasks for Claude Code:
1. the Riemann–Stieltjes library as a standalone Lake package on IEANTN's Lean/Mathlib pin;
2. the draft statements compiled (library: A, B; IEANTN: the two node drafts);
3. **A** (Fourier integral theorem), then **B** (digamma, Theorem C.5, Lemma 12.14) in the library;
4. a solution for `ContourIntegration.v1` (and, as planned on 26 November, for `GammaAsymptotics.v1`: no longer
   needed, see §4, decision 4);
5. `ZetaGoodHeights.v1` (C4–C7: Jensen, Borel–Carathéodory, a polynomial bound for $\zeta$ in $\sigma\ge\frac18$,
   the choice of $T_1$) — the most delicate part;
6. `WeilExplicitFormula.v1` (C1–C3, D1, E, F, G);
7. Comparator, receipts, and the Palomar spin-off.

Rough size: A 600–900 lines, B 800–1200, C 1000–1500, D 200–400, E 200–300, F 300–500, G 500–800.

**State (27 November 2026, afternoon).** Everything except C4–C7 is done, in another chat, in branch
`mv-lemma-12-14` (about 6,300 lines; see the **L** entries in §2): Theorem 12.13 is proved in the library from
Theorem 10.13, Lemma 12.2 and the residue theorem on rectangles, taken as hypotheses in their IEANTN form. Left:
1. Theorem 10.13 and Lemma 12.2 (C4–C7, `ZetaGoodHeights.v1`; proofs in `proofs/GoodHeights.md`): in the library,
   by the other chat (§4, decision 5);
2. a solution for `ContourIntegration.v1` (who does it: Harald's call, with the maintainers' agreement);
3. the equivalence of (12.20)–(12.21), as printed, with the node's form of the hypotheses, which the node's
   docstring and metadata promise ("proved in the solution"; §4, decision 2): in the library, by the other chat
   (§4, decision 5);
4. the port of the library to IEANTN's pin, and the IEANTN solutions, where `theorem_12_13_of` gives
   `WeilExplicitFormula.v1` by unfolding definitions: on the laptop, through Claude Code.

## 4. Decisions (26 November 2026)

1. **The full statement**: Theorem 12.13 with $q=1$ and $F$ as in (12.20)–(12.21). The case of the Mertens note (E0)
   is a corollary.
2. **The Riemann–Stieltjes library is used in the proofs**: integration by parts for $\Phi$ and $H$, the Fourier
   integral theorem, the variation estimates, and the equivalence of (12.20)–(12.21) with the form used in the
   statement. The *statement* itself must stay Mathlib-only, because IEANTN conclusions and Palomar challenges may
   import nothing else; that is why (12.21) appears as "$e^{a|x|}F$ is integrable and of bounded variation".
3. **The result goes into IEANTN**, importing the nodes already there rather than copying them, and the Palomar
   version is generated from IEANTN (`ieantn.py spinoff`).
4. (27 November 2026) **The digamma bound uniform on vertical strips** (B3, first statement, `exists_norm_digamma_le_log`)
   **is added to the library by the other chat**, from its `Complex.norm_digamma_sub_le`. So neither
   `ZetaGoodHeights.v1` nor `WeilExplicitFormula.v1` imports `GammaAsymptotics.v1`.
5. (27 November 2026, afternoon) **Theorem 10.13 and Lemma 12.2, and the equivalence of (12.20)–(12.21) with the
   node's hypotheses, are proved in the library by the other chat**, against the verbatim copies of the IEANTN
   statements (for 10.13 and 12.2, following `proofs/GoodHeights.md`). The laptop ports the library to IEANTN's pin
   and writes the IEANTN solutions, which then come by unfolding definitions.

## 5. IEANTN integration

**How IEANTN treats such lemmas.** Textbook facts that Mathlib lacks are nodes of kind `standard`, stated once and
imported by statement: `ContourIntegration`, `ZetaZeroes`, `ZetaHadamard`, `ZetaLogDeriv`, `GammaAsymptotics`,
`CotangentSeries`. The reason is bookkeeping and reuse, not that they might be improved. Nodes import each other's
*statements* only; proofs live in *solutions*, separate Lake projects that may import anything pinned (PNT+,
LeanCert, our library), but must use the core's Mathlib revision. Lemmas internal to a proof stay in the solution or
in a library.

**Palomar.** `ieantn.py spinoff <conclusion>` composes the designated path, vendoring each verified node's solution,
and refuses a citation in the middle. So the Palomar version needs a Lean solution (with a receipt) for every node on
our path — which is also what an unconditional result means.

**The node** `WeilExplicitFormula.v1` (draft in `blueprint/ieantn/WeilExplicitFormula/v1/`) and its imports:

| imported conclusion | used for | status in IEANTN (23 Nov 2026) | to do |
|---|---|---|---|
| `ContourIntegration.v1.residue_theorem_rectangle` | D1, G4 | inactive, none-yet | reactivate; prove |
| `ZetaGoodHeights.v1.theorem_10_13`, `.lemma_12_2` | C4, C7, G2, G6 | new node (draft) | state; prove |

`ZetaZeroes.v1` (proved) is no longer imported (27 November): Mathlib's `IsCompact.inter_riemannZetaZeros_finite`,
present at the pin, gives the finiteness, and $\xi(1-s)=\xi(s)$ with $\zeta\ne0$ on $\Re s\ge1$ the location of the
zeros.

`ZetaGoodHeights.v1` in turn imports only `ZetaLogDeriv.v1.logDeriv_functional_equation` (proved, lean-comparator), for
`lemma_12_2`. Its proofs are written out in `blueprint/proofs/GoodHeights.md`.

`GammaAsymptotics.v1` (awaiting-solution) is no longer imported (decision 4, §4): the digamma bounds, B3 included,
come from the library. Appendix A of `GoodHeights.md` derives `GammaAsymptotics.v1` from the Gauss series; a solution
for it would be an optional contribution to IEANTN, off our path.

Not imported: `ZeroCount.v1` (Rosser's explicit count) and `ZetaHadamard.v1` (MV Corollary 10.14), both resting on the
literature: the route here does not need the Hadamard product.

**The library.** The Riemann–Stieltjes files (with Dirichlet–Jordan, Fejér and Cesàro) become a standalone Lake
package pinned to IEANTN's Lean and Mathlib (v4.34.0-rc2 and `71a80585` on 23 November), because an IEANTN solution
must use the core's Mathlib revision and cannot depend on a fork of Mathlib. Parts A and B and the general complex
analysis (D1, C5) go there; the parts about $\zeta$ go into the solutions.

**An erratum noticed in IEANTN.** The `sources` entry of `ZetaHadamard.v1/formalization.yaml` says "Theorem 10.13 is
the Hadamard product for xi". In [MV] the Hadamard product is Theorem 10.12; Theorem 10.13 is
$N(T+1)-N(T)\ll\log(T+2)$.
