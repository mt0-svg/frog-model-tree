\\ The induction of Theorem 14.1 of the paper: first height m1 from which it closes with Lemma 10.6 (the loss),
\\ Lemmas 11.4, 11.5 and 11.1 of the paper and the recursion of dp15.gp, and the base it then requires. In the
\\ labels below, "Lemma 9", "Lemma 10", "Lemma 12" and "Lemma 15" are Lemmas 11.4, 11.5, 11.1 and that recursion.
\\ Usage: gp -q scale4.gp < /dev/null > scale4.out (from this directory); MODE set below.
\\ Heights are split into intervals [10^e, 10^(e+1/4)]; on each, the jackpot bounds are taken at
\\ the left end ml (they increase with m) and the loss (K1) at the right end mh.
\\ For a vertex w at height m + 1 (children at m) and comparison index J:
\\   J-closure loss  LJ = min over parameters of [P(N(J) < k) bound + P(Bin(k, 1/4) < J)],
\\   1-closure loss  L1 = min over parameters of [P(N(1) < k) bound + P(Bin(k, 1/4) < J)],
\\ with P(N(J) < k) from Lemma 11.5 (jackpot p* from Lemma 11.1) or from the recursion of dp15.gp, and
\\ P(N(1) < k) from Lemma 11.4 (p_1 from Lemma 11.1) or that recursion. Conditions on each interval:
\\   (K1) ((mh + J + 1)/3) LJ <= eps,   (K2, slope) (1/3 - eps)(1 - L1) >= c0/3,
\\ J nondecreasing; base b1 >= max over intervals of ((c0 (ml+3) + J - 2)/3)/(1 - L1)
\\ - (1/3 - eps)(ml - m1). Floating point (38 digits), Chernoff upper bounds for binomial tails.

read("dp15.gp");
kl(x, p) = if(x <= 0, -log(1 - p), x*log(x/p) + (1-x)*log((1-x)/(1-p)));
ex(t) = if(t < -2000, 0., exp(t));
\\ upper bound on P(Bin(n, p) < k), Chernoff
blt(n, p, k) = if(k <= 0, 0., if(p >= 1, if(n < k, 1., 0.), if(k > n*p, 1., ex(-n*kl(k/n, p)))));
\\ lower bound on P(Bin(n, p) >= k)
bge(n, p, k) = max(0., 1 - blt(n, p, k));
\\ Lemma 11.1: P(G >= x) >= 1 - ((1 - c) mu + mu^(1/2)/2)/(mu - x) when E G >= c mu
lem12(c, mu, x) = if(x >= mu, 0., max(0., 1 - ((1-c)*mu + sqrt(mu)/2)/(mu - x)));
S(p) = 15/16 - 9/16*(1-p) - 3/8*(1-p)^2;

JMAX = 400;          \\ largest J tried
DPA = 48;            \\ a_max of the DP (J <= DPA - 1 through dp15.gp)
DPMAXM = 10^6;       \\ dp15.gp used on intervals with ml <= DPMAXM (beyond, its floor is too high)
KGRID = [16, 24, 32, 48, 64, 96, 128, 192, 256, 384];
BGRID = [3.5, 4.5, 6];
if (type(MODE) == "t_POL", MODE = 3);   \\ 1: Lemmas 11.4, 11.5 only; 2: dp15.gp only; 3: both
V2C = Map();

\\ vectors over J = 1..JMAX of the two losses on [ml, mh] (independent of eps and of m1)
losses(ml, c0) =
{
  my(LJ = vector(JMAX, J, 1.), L1 = vector(JMAX, J, 1.), B1 = vector(JMAX, J, "trivial"));
  if (MODE != 2,
    \\ Lemma 11.4 for the 1-closure, k = a J
    for (J = 1, JMAX, foreach ([4, 6, 8, 12, 16], a,
      my(k = a*J, p1 = lem12(c0, (ml+2)/3., k));
      if (p1 > 0, my(v = 1 - S(p1) + blt(k, 1/4, J)); if (v < L1[J], L1[J] = v; B1[J] = Strprintf("Lemma 9 k=%dJ", a)))));
    \\ Lemma 11.5 for the J-closure
    for (J = 1, JMAX, for (D = 1, 30,
      if (J*3.^(-D) > 2/3, next);
      foreach ([6, 8, 12], a, foreach ([1.5, 2], b,
        my(k = a*J, y = ceil(b*k*3^(D-1)), ps = lem12(c0, (ml+3-D)/3., y));
        if (ps <= 0, next);
        my(piJ = (1 - (2/3 - J*3.^(-D))*ps)^(J+1) + blt(y, 3.^(1-D), k));
        LJ[J] = min(LJ[J], piJ + blt(k, 1/4, J)))))));
  if (MODE != 1,
    foreach (KGRID, K, foreach (BGRID, b,
      my(Y = ceil(b*K), s0 = lem12(c0, (ml+2)/3., K), s1 = lem12(c0, (ml+1)/3., Y)*bge(Y, 1/3, K));
      if (s0 <= 0 || s1 <= 0, next);
      \\ above DPMAXM only the 1-closure bound V(2) is computed (a_max = 6 is exact for q = 2)
      my(V = if(ml <= DPMAXM, dp15(0, s0, s1, DPA), concat(dp15(0, s0, s1, 6), vector(DPA - 6, i, 1.))));
      for (J = 1, DPA - 1,
        my(PB = blt(K, 1/4, J));
        LJ[J] = min(LJ[J], V[J+1] + PB);
        if (V[2] + PB < L1[J], L1[J] = V[2] + PB; B1[J] = Strprintf("Lemma 15 K=%d b=%.1f", K, b)))));
    \\ 1-closure at every J: K = a J beyond KGRID; V(2) is nonincreasing in s0 and s1 (the
    \\ adversary's constraint sets shrink), so s0, s1 are rounded down to multiples of 1/2000
    \\ and V(2) is cached on that grid (global map V2C)
    for (J = 1, JMAX, foreach ([4, 6, 8], a, foreach (BGRID, b,
      my(K = a*J, Y = ceil(b*K), s0 = lem12(c0, (ml+2)/3., K), s1 = lem12(c0, (ml+1)/3., Y)*bge(Y, 1/3, K));
      if (s0 <= 0 || s1 <= 0, next);
      my(key = [floor(2000*s0), floor(2000*s1)], V2);
      if (!mapisdefined(V2C, key, &V2), V2 = dp15(2, key[1]/2000., key[2]/2000., 6); mapput(V2C, key, V2));
      my(v = V2 + blt(K, 1/4, J)); if (v < L1[J], L1[J] = v; B1[J] = Strprintf("Lemma 15 K=%dJ b=%.1f", a, b))))));
  [LJ, L1, B1]
}

\\ first m1 = 10^e1 from which every interval up to 10^30 passes; returns
\\ [e1, J(m1), b1 required, b1 relative to (m1 + J + 1)/3, J at 10^30, 1-closure branch and L1
\\ on the first interval, the same on the last interval [10^29.75, 10^30]]
run(c0, eps, estart) =
{
  my(cache = Map());
  forstep (e1 = estart, 30 - 1/4, 1/4,
    my(J = 1, ok = 1, b1req = -oo, J1 = 0, m1 = round(10^e1), br1 = 0, brl = 0);
    forstep (e = e1, 30 - 1/4, 1/4,
      my(ml = round(10^e), mh = round(10^(e + 1/4)), L);
      if (mapisdefined(cache, e, &L), , L = losses(ml, c0); mapput(cache, e, L));
      my(Jok = 0);
      for (Jt = J, JMAX,
        if ((mh + Jt + 1)/3*L[1][Jt] <= eps && (1/3 - eps)*(1 - L[2][Jt]) >= c0/3, Jok = Jt; break));
      if (!Jok, ok = 0; break);
      J = Jok; if (e == e1, J1 = J; br1 = [L[3][J], L[2][J]]); brl = [L[3][J], L[2][J]];
      b1req = max(b1req, ((c0*(ml+3) + J - 2)/3)/(1 - L[2][J]) - (1/3 - eps)*(ml - m1)));
    if (ok, return([e1, J1, b1req, b1req/((m1 + J1 + 1)/3), J, br1, brl])));
  [oo]
}

\\ dp15.gp alone at s0 = 0.92, s1 = 0.85 (not run when MAINRUN = 0, as dbranch_m1.gp sets it)
if (type(MAINRUN) == "t_POL", MAINRUN = 1);
{if (MAINRUN,
  my(V = dp15(0, 0.92, 0.85, 20));
  printf("dp15 at s0 = 0.92, s1 = 0.85: V(2) = %.4g (Lemma 9: 1 - S(0.92) = %.4g); V(q+1)/V(q), q = 2..15:", V[2], 1 - S(0.92));
  for (q = 2, 15, printf(" %.3f", V[q+1]/V[q])); print();
  if (type(PAIRS) == "t_POL", PAIRS = [[0.6, 0.02], [0.7, 0.02], [0.8, 0.02], [0.85, 0.01]]);
  foreach (PAIRS, pr,
    my(c0 = pr[1], eps = pr[2], r = run(c0, eps, 2));
    if (r[1] == oo, printf("mode %d c0 %.2f eps %.2f: no m1 <= 10^30\n", MODE, c0, eps),
      printf("mode %d c0 %.2f eps %.2f: m1 = 10^%.2f, J(m1) %d, J at 10^30 %d, base b1 >= %.4g = %.4f (m1+J1+1)/3\n  b1 = %.12g, m1 = %d, mu_m1(J1) = (m1 + J1 + 1)/3 = %.12g, 1 - b1/mu_m1(J1) = %.10f\n  1-closure on the first interval: %s, L1 = %.6f; on the last interval: %s, L1 = %.6f\n", MODE, c0, eps, r[1], r[2], r[5], r[3], r[4], r[3], round(10^r[1]), (round(10^r[1]) + r[2] + 1)/3, 1 - r[4], r[6][1], r[6][2], r[7][1], r[7][2]))))};
