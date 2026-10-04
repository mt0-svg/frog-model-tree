\\ An adversarial recursion ("Lemma 15" in the labels of scale4.gp; the proof does not use it, and the table of
\\ Proposition 15.2 of the paper, MODE 1 of scale4.gp, does not call it): upper bound V(q) on P(N(q-1) < K) at a vertex w
\\ whose children are at height m, from
\\   s0 <= P(G_m(1) >= K)                                   (fresh first entry of a child),
\\   s1 <= P(G_(m-1)(1) >= Y) P(Bin(Y, 1/3) >= K)           (fresh grandchild).
\\ State: a pending frogs at w (capped at amax, extra frogs discarded), and the type of each
\\ child: 4 = never entered, f in 0..3 = entered, no increment >= K yet, f children unvisited.
\\ V(0; .) = 1. A step: up with probability 1/4; into child c with probability 1/4:
\\   type 4: increment >= K with prob >= s0; atom (both frogs up) prob 1/16, 2 frogs back,
\\           type 3; other failures mass <= 1 - s0 - 1/16, no frog back (discarded), at least
\\           j children of c visited with mass <= (15/16) beta^j, beta = 1 - s1, j >= 1;
\\   type f: first step up, prob 1/4: the frog comes back, type unchanged (self-loop); with
\\           tau = P(at least one fresh grandchild trial) in [f/4, 3/4] (adversarial): increment
\\           >= K with prob >= s1 tau; other failures mass <= 3/4 - s1 tau, no frog back, at least
\\           j new children visited with mass <= beta^j tau.
\\ The adversary maximizes over the masses (an LP over nonincreasing tail masses T_j).

\\ max of sum_k m_k v_k over m >= 0 with tail sums sum_(i >= j) m_i <= u_j: the constraints form a
\\ laminar family, so the feasible set is a polymatroid and the greedy order by v is optimal
\\ (checked against a grid search)
lpmax(u, v) =
{
  my(n = #u, m = vector(n), ord = vecsort(v, , 1 + 4), val = 0.);
  for (t = 1, n,
    my(k = ord[t], cap = oo);
    for (j = 1, k, cap = min(cap, u[j] - sum(i = j, n, m[i])));
    m[k] = max(0, cap); val += m[k]*v[k]);
  val
}

\\ value of a state already computed (global map DPV of the current dp15 call)
getV(a, t) = if(a <= 0, 1., mapget(DPV, [min(a, DPAMAX), tkey(t)]));

\\ child types as a sorted vector [t1 >= t2 >= t3]; index of a state
tkey(t) = my(s = vecsort(t, , 4)); s[1]*25 + s[2]*5 + s[3];

\\ dp15(q, ...) = V(q); dp15(0, ...) = [V(1), ..., V(amax)]
dp15(q, s0, s1, amax) =
{
  my(beta = 1 - s1, s0c = min(s0, 15/16), MF = max(0., 1 - s0c - 1/16), types = List());
  DPV = Map(); DPAMAX = amax;
  forvec (t = [[0, 4], [0, 4], [0, 4]], listput(types, t), 1);
  \\ sort types by number of never-entered children (transitions only add visited children)
  my(tl = vecsort(Vec(types), (x, y) -> sum(i = 1, 3, x[i] == 4) - sum(i = 1, 3, y[i] == 4)));
  for (nf = 0, 3, for (a = 1, amax, foreach (tl, t, if (sum(i = 1, 3, t[i] == 4) != nf, next);
    my(nv = sum(i = 1, 3, t[i] != 4));
      my(A = 1/4*getV(a - 1, t));
      for (c = 1, 3,
        my(tc = t[c], tt = t);
        if (tc == 4,
          tt[c] = 3; A += 1/4*(1/16)*getV(a + 1, tt);
          my(u = vector(3, j, if(j == 1, min(MF, 15/16*beta), 15/16*beta^j)), v = vector(3));
          for (j = 1, 3, tt = t; tt[c] = 3 - j; v[j] = getV(a - 1, tt));
          A += 1/4*lpmax(u, v)
        ,
          my(f = tc, n = f + 1, v = vector(n), best = 0.);
          for (j = 0, f, tt = t; tt[c] = f - j; v[j+1] = getV(a - 1, tt));
          \\ tau = P(at least one fresh grandchild trial) in [f/4, 3/4]: success >= s1 tau,
          \\ other failures <= 3/4 - s1 tau, at least j new children visited <= beta^j tau; the LP
          \\ value is concave piecewise linear in tau, with breakpoints where 3/4 - s1 tau = beta^j tau
          my(taus = if(f == 0, [0], concat([f/4, 3/4], vector(f, j, (3/4)/(s1 + beta^j)))));
          foreach (taus, tau, if (tau < f/4 || tau > 3/4, next);
            my(u = vector(n, i, if(i == 1, max(0., 3/4 - s1*tau), beta^(i-1)*tau)));
            best = max(best, lpmax(u, v)));
          A += 1/4*best));
      mapput(DPV, [a, tkey(t)], A/(1 - nv/16)))));
  if (q == 0, vector(amax, i, getV(i, [4, 4, 4])), getV(q, [4, 4, 4]))
}
