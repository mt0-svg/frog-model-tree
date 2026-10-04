\\ Outward-rounded bounds for the inequalities of Lemma 14.2 of the paper, used by dcheck_m1.gp.
\\ Every bound is a rational: lower bounds are rounded down and upper bounds up, to dyadics with R
\\ significant bits; logarithms and exponentials come from series with explicit remainders, square
\\ roots from integer square roots. No floating point enters a bound. The constant c0 is a global set
\\ by the caller.

R = 256;


\\ ---------- outward rounding and elementary bounds ----------
ex2(x) = my(a = abs(x)); logint(numerator(a), 2) - logint(denominator(a), 2);
rdn(x) = if(x == 0, 0, my(s = R - ex2(x)); floor(x * 2^s) / 2^s);
rup(x) = if(x == 0, 0, my(s = R - ex2(x)); ceil(x * 2^s) / 2^s);
\\ bounds on b^n for a rational b >= 0
powdn(b, n) = my(r = 1, p = b); while (n, if (n % 2, r = rdn(r * p)); n \= 2; if (n, p = rdn(p * p))); r;
powup(b, n) = my(r = 1, p = b); while (n, if (n % 2, r = rup(r * p)); n \= 2; if (n, p = rup(p * p))); r;

\\ [lo, hi] around 2 atanh(z) for rational |z| <= 1/3: partial sum, remainder <= |t|/((2i + 1)(1 - z^2))
NSER = 0;
atanh2(z) =
{
  my(s = 0, t = z, z2 = z^2, i = 0, rem);
  while (t != 0 && abs(t) >= 2^(-R - 40), s += t/(2*i + 1); t *= z2; i++; NSER++);
  rem = abs(t)/((2*i + 1)*(1 - z2));
  [rdn(2*(s - rem)), rup(2*(s + rem))]
}
LN2 = atanh2(1/3);
\\ [lo, hi] around ln(r), rational r > 0 (r = 2^k r1, r1 in [2/3, 4/3], ln r1 = 2 atanh((r1 - 1)/(r1 + 1)))
lnB(r) =
{
  my(k = ex2(r), r1 = r / 2^k);
  while (r1 > 4/3, r1 /= 2; k++);
  while (r1 < 2/3, r1 *= 2; k--);
  my(A = atanh2((r1 - 1)/(r1 + 1)));
  if (k >= 0, [rdn(k*LN2[1] + A[1]), rup(k*LN2[2] + A[2])], [rdn(k*LN2[2] + A[1]), rup(k*LN2[1] + A[2])])
}
\\ [lo, hi] around exp(f), 0 <= f <= 1: partial sum S_N, remainder <= 2 f^N/N! <= 3 f^N/N! (N >= 1)
expf(f) =
{
  my(s = 0, t = 1, i = 0);
  while (t >= 2^(-R - 40), s += t; i++; t = t*f/i; NSER++);
  [rdn(s), rup(s + 3*t)]
}
E1 = expf(1);
\\ [lo, hi] around exp(x), rational x
expB(x) =
{
  if (x < 0, my(b = expB(-x)); return([rdn(1/b[2]), rup(1/b[1])]));
  my(n = floor(x), f = x - n, lo = expf(rdn(f))[1], hi = expf(min(1, rup(f)))[2]);
  [rdn(lo * powdn(E1[1], n)), rup(hi * powup(E1[2], n))]
}
sqrt_up(r) = (sqrtint(floor(r * 4^R)) + 1) / 2^R;
sqrt_dn(r) = sqrtint(floor(r * 4^R)) / 2^R;

\\ ---------- the bounds of the lemmas ----------
\\ Lemma 11.1 of the paper: P(G >= x) >= 1 - ((1 - c) mu + mu^(1/2)/2)/(mu - x) when E G >= c mu (a lower bound)
lem12(c, mu, x) = if(x >= mu, 0, max(0, rdn(1 - ((1 - c)*mu + sqrt_up(mu)/2)/(mu - x))));
\\ KL(x, p) from below, 0 <= x < p < 1
kl_low(x, p) = if(x == 0, -lnB(1 - p)[2], rdn(x*lnB(x/p)[1] + (1 - x)*lnB((1 - x)/(1 - p))[1]));
\\ Chernoff: P(Bin(n, p) < k) <= exp(-n KL(k/n, p)) for k <= n p (an upper bound)
blt(n, p, k) = if(k <= 0, 0, if(k > n*p, 1, min(1, expB(-n * kl_low(k/n, p))[2])));
bge(n, p, k) = max(0, 1 - blt(n, p, k));

\\ Lemma 11.5 of the paper at depth D, k = a J, y = ceil(b k 3^(D-1)), jackpot at height ml + 1 - D: upper bound on LJ
lj10(J, D, a, b, ml) =
{
  my(k = a*J, y = ceil(b*k*3^(D - 1)), ps = lem12(c0, (ml + 3 - D)/3, y), co = 2/3 - J/3^D);
  if (co <= 0 || ps <= 0, return([1, y, ps]));
  [rup(powup(rup(1 - co*ps), J + 1) + blt(y, 1/3^(D - 1), k) + blt(k, 1/4, J)), y, ps]
}

\\ The step operator T of the adversarial recursion of dp15.gp (not used by dcheck_m1.gp), each value rounded up.
\\ LP of one entry: max sum m_j v_j over m >= 0 with sum_{i >= j} m_i <= u_j. Weak duality gives the
\\ bound sum_j (Y_j - Y_{j-1}) ut_j with Y_j = max_{i <= j} v_i (Y_0 = 0, v >= 0) and ut_j = max(0,
\\ min_{i <= j} u_i): sum_k m_k v_k <= sum_k m_k Y_k = sum_j (Y_j - Y_{j-1}) T_j, T_j = sum_{k >= j} m_k
\\ <= ut_j. lpbound is that bound; lpgreedy (the greedy of dp15.gp) attains it on every call (checked).
lpbound(u, v) =
{
  my(n = #u, ut = oo, Y = 0, Yp = 0, val = 0);
  for (j = 1, n, ut = min(ut, u[j]); Y = max(Y, v[j]); val += (Y - Yp)*max(0, ut); Yp = Y);
  val
}
lpgreedy(u, v) =
{
  my(n = #u, m = vector(n), ord = vecsort(v, , 1 + 4), val = 0);
  for (t = 1, n,
    my(k = ord[t], cap = oo);
    for (j = 1, k, cap = min(cap, u[j] - sum(i = j, n, m[i])));
    m[k] = max(0, cap); val += m[k]*v[k]);
  val
}
NLP = 0; NLPNE = 0;
lpb(u, v) = my(b = lpbound(u, v)); NLP++; if (lpgreedy(u, v) != b, NLPNE++); b;
tkey(t) = my(s = vecsort(t, , 4)); s[1]*25 + s[2]*5 + s[3];
getV(a, t) = if(a <= 0, 1, mapget(DPV, [min(a, DPAMAX), tkey(t)]));
NDP = 0;
\\ W(a, t) >= (T W)(a, t) state by state: the self-loop (mass n_v/16) is solved exactly, every other
\\ transition goes to a state computed before (smaller a, or one more visited child). For a visited
\\ child with f unvisited children the LP bound is concave and piecewise linear in tau on [f/4, 3/4]
\\ (each ut_j is the min of 3/4 - s1 tau >= 0 and beta^(j-1) tau), with breakpoints at
\\ tau = (3/4)/(s1 + beta^i), so its maximum is at a breakpoint or an end.
dpV(q, s0, s1, amax) =
{
  my(beta = 1 - s1, s0c = min(s0, 15/16), MF = max(0, 1 - s0c - 1/16), tl = List());
  DPV = Map(); DPAMAX = amax;
  forvec (t = [[0, 4], [0, 4], [0, 4]], listput(tl, t), 1);
  for (nf = 0, 3, for (a = 1, amax, foreach (tl, t, if (sum(i = 1, 3, t[i] == 4) != nf, next);
    my(nv = sum(i = 1, 3, t[i] != 4), A = 1/4*getV(a - 1, t));
    for (c = 1, 3,
      my(tc = t[c], tt = t);
      if (tc == 4,
        tt[c] = 3; A += 1/4*(1/16)*getV(a + 1, tt);
        my(u = vector(3, j, if(j == 1, min(MF, 15/16*beta), 15/16*beta^j)), v = vector(3));
        for (j = 1, 3, tt = t; tt[c] = 3 - j; v[j] = getV(a - 1, tt));
        A += 1/4*lpb(u, v)
      ,
        my(f = tc, n = f + 1, v = vector(n), best = 0);
        for (j = 0, f, tt = t; tt[c] = f - j; v[j+1] = getV(a - 1, tt));
        my(taus = if(f == 0, [0], concat([f/4, 3/4], vector(f, j, (3/4)/(s1 + beta^j)))));
        foreach (taus, tau, if (tau < f/4 || tau > 3/4, next);
          my(u = vector(n, i, if(i == 1, max(0, 3/4 - s1*tau), beta^(i-1)*tau)));
          best = max(best, lpb(u, v)));
        A += 1/4*best));
    NDP++;
    mapput(DPV, [a, tkey(t)], rup(A/(1 - nv/16))))));
  getV(q, [4, 4, 4])
}

\\ 1-closure by the recursion of dp15.gp, V(2) with K, Y = ceil(bK K), children at heights ml and ml - 1
l1_15(J, K, bK, ml) =
{
  my(Y = ceil(bK*K), s0 = lem12(c0, (ml + 2)/3, K), s1 = rdn(lem12(c0, (ml + 1)/3, Y) * bge(Y, 1/3, K)));
  if (s0 <= 0 || s1 <= 0, return([1, s0, s1, 1]));
  my(V2 = dpV(2, s0, s1, 6));
  [rup(V2 + blt(K, 1/4, J)), s0, s1, V2]
}

\\ ---------- printing in the safe direction ----------
\\ A printed lower bound is rounded down and a printed upper bound up, to d decimals (fdn, fup) or to
\\ d decimals of the mantissa (edn, eup). Printing only; no comparison reads these strings.
fdn(x, d) = Strprintf(Str("%.", d, "f"), floor(x*10^d)/10^d);
fup(x, d) = Strprintf(Str("%.", d, "f"), ceil(x*10^d)/10^d);
e10(x) = my(e = floor(log(x)/log(10))); while (10^e > x, e--); while (10^(e + 1) <= x, e++); e;
edn(x, d) = if (x == 0, "0", x < 0, Str("-", eup(-x, d)), my(e = e10(x)); Strprintf(Str("%.", d, "fe%d"), floor(x/10^e*10^d)/10^d, e));
eup(x, d) = if (x == 0, "0", x < 0, Str("-", edn(-x, d)), my(e = e10(x)); Strprintf(Str("%.", d, "fe%d"), ceil(x/10^e*10^d)/10^d, e));
