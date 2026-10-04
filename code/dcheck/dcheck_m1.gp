\\ The inequalities of the induction of Theorem 14.1 of the paper on the table of Proposition 15.2 (MODE 1:
\\ Lemmas 11.4 and 11.5 only), in exact rational arithmetic with outward rounding (bounds in dcheck_lib.gp). No
\\ floating point enters a comparison. Row (c0, eps) = (3/5, 1/50), m1 = M(3) = round(10^6.25) = 1778279, Lemma 11.5
\\ of the paper for the J-closure and Lemma 11.4 (q = 2) for the 1-closure.
\\ Input CERT (dcheck_m1_cert.gp, made by dbranch_m1.gp): for each interval [M(i), M(i + 1)], i = 3..97,
\\ M(i) = round(10^(5.5 + i/4)), the entry [J, D, a, b, a9, src10, src9]: J the comparison index;
\\ Lemma 11.5 at depth D with k = a J and y = ceil(b k 3^(D - 1)) for the J-closure; Lemma 11.4 with
\\ k = a9 J for the 1-closure.
\\ Checks per interval (Lemma 14.2 of the paper): J nondecreasing, D <= 30, and
\\   (K1)  ((mh + J + 1)/3) LJ <= eps;   slope  (1/3 - eps)(1 - L1) > c0/3;
\\   base  ((c0 (ml + 3) + J - 2)/3)/(1 - L1) - (1/3 - eps)(ml - m1) <= b1 (largest over the intervals);
\\ with LJ = (1 - (2/3 - J 3^-D) p_D)^(J+1) + P(Bin(y, 3^(1-D)) < k) + P(Bin(k, 1/4) < J), p_D from
\\ Lemma 11.1 at height ml + 1 - D and threshold y, and L1 = 1 - S(p1) + P(Bin(k, 1/4) < J), p1 from
\\ Lemma 11.1 at height ml and threshold k = a9 J, S(p) = 15/16 - (9/16)(1 - p) - (3/8)(1 - p)^2.
\\ Then the inequalities past 10^30 (Lemma 14.3 of the paper), with J(m) = max(J_last, ceil(A ln m)).
\\ Printed decimals: the interval lines round the certified rationals to nearest; the detail lines and
\\ the past 10^30 block print lower bounds rounded down and upper bounds rounded up. Comparisons are exact.
\\ Usage: gp -q dcheck_m1_cert.gp dcheck_m1.gp < /dev/null; a negative control sets NEGCTL = [eps, b1, A].

c0 = 3/5; eps = 1/50; b1 = 54580886/100; APAST = 11/5;
if (type(NEGCTL) == "t_VEC", [eps, b1, APAST] = NEGCTL; printf("negative control: eps %s, b1 %s, A %s\n", eps, b1, APAST));
read("dcheck_lib.gp");
default(realprecision, 60);

\\ Lemma 11.4 with q = 2: P(N(1) < k) <= 1 - S(p1); 1 - S is decreasing in p, so p1 rounded down is sound
Sx(p) = 15/16 - 9/16*(1 - p) - 3/8*(1 - p)^2;
l1_9(J, a9, ml) =
{
  my(k = a9*J, p1 = lem12(c0, (ml + 2)/3, k));
  if (p1 <= 0, return([1, p1]));
  [rup(1 - Sx(p1) + blt(k, 1/4, J)), p1]
}

\\ ---------- the 95 intervals from m1 ----------
M(i) = my(f = sqrtint(sqrtint(16*10^(22 + i)))); (f + 1) \ 2;   \\ round(10^((22 + i)/4)), exactly
I0 = 3; m1 = M(I0);
if (m1 != 1778279 || M(98) != 10^30 || #CERT != 98 - I0, error("interval data"));
sci(x, d) = strjoin(strsplit(Strprintf(Str("%.", d, "e"), x), " "), "");
\\ Fail-safe verdict: PASS needs NBAD = 0 and both blocks
\\ completed, with all 95 interval lines; a gp error inside a block leaves its flag at 0.
NBAD = 0; NINT = 0; DONE1 = 0; DONEP = 0;
{
  my(bmax = -oo, k1max = 0, slmin = oo, Jprev = 0, t0 = getabstime());
  for (i = I0, 97,
    my(c = CERT[i - I0 + 1], J = c[1], D = c[2], a = c[3], b = c[4], a9 = c[5], ml = M(i), mh = M(i + 1));
    my(L10 = lj10(J, D, a, b, ml), LJ = L10[1], L = l1_9(J, a9, ml), L1 = L[1]);
    my(k1 = (mh + J + 1)/3 * LJ, sl = (1/3 - eps)*(1 - L1) - c0/3);
    my(base = ((c0*(ml + 3) + J - 2)/3)/(1 - L1) - (1/3 - eps)*(ml - m1));
    my(pass = (J >= Jprev) && (D <= 30) && (k1 <= eps) && (sl > 0) && (L1 < 1));
    if (!pass, NBAD++);
    Jprev = J; bmax = max(bmax, base); k1max = max(k1max, k1/eps); slmin = min(slmin, sl);
    printf("e %.2f [%s, %s]: J %d LJ %s (%s) (K1) %s; L1 %.6f (%s) slope margin %s; base required %.2f%s\n",
      (22 + i)/4, sci(ml, 6), sci(mh, 6), J, sci(LJ, 4), c[6], sci(k1, 4), L1, c[7], sci(sl, 4), base, if(pass, "", " FAILS"));
    printf("  detail: y %d jackpot10 >= %s; p1 >= %s; (K1)/eps <= %s\n", L10[2], fdn(L10[3], 10), fdn(L[2], 10), fup(k1/eps, 6));
    NINT++);
  printf("c0 %s eps %s: m1 = %d, J(m1) %d, J at 10^30 %d, b1 >= %.4f = %.6f (m1 + J1 + 1)/3; largest (K1)/eps %.4f, smallest slope margin %s\n",
    c0, eps, m1, CERT[1][1], CERT[#CERT][1], bmax, bmax/((m1 + CERT[1][1] + 1)/3), k1max, sci(slmin, 4));
  printf("exact: largest base required < %.8f (rounded up), b1 = %s: base check %s\n",
    ceil(bmax*10^8)/10^8, b1, if(bmax <= b1, "passes", "FAILS"));
  my(J1 = CERT[1][1], mu = (m1 + J1 + 1)/3);
  printf("hand-over threshold: delta_T(%d) <= 1 - b1/mu_m1(%d) = %s = %.12f (exact rational, b1 = %s, mu = %s)\n",
    J1, J1, 1 - b1/mu, 1 - b1/mu, b1, mu);
  printf("%d intervals: %d failing; series terms so far %d; %.1f s\n", #CERT, NBAD, NSER, (getabstime() - t0)/1000.);
  if (bmax > b1, NBAD++);
  LASTI = [CERT[#CERT], M(97), M(98)];
  DONE1 = 1;
}

\\ ---------- past 10^30 (Lemma 14.3 of the paper) ----------
\\ J(m) = max(J_last, ceil(A ln m)) for m > 10^30, A = APAST; (K1) by Lemma 11.5 with k = 12 J,
\\ D = ceil(log_3(100 J)), y = 18 J 3^(D - 1); (K2) by Lemma 11.4 with k = a9 J, a9 of the last interval.
OKP = 1;
chk(name, cond) = printf("  %s: %s\n", name, if(cond, "holds", "FAILS")); if (!cond, OKP = 0);
{
  my(t0 = getabstime(), A = APAST, mm = 10^30, LM = lnB(mm), CJ = A + 1/50);
  my(cl = LASTI[1], Jl = cl[1], Ml = LASTI[2], a9 = cl[5]);
  print("past 10^30, for every m >= 10^30 (each line an exact comparison; bounds at m = 10^30 extend by monotonicity):");
  printf("  ln(10^30) in [%s, %s]; A = %s, CJ = A + 1/50 = %s, J_last = %d\n", fdn(LM[1], 12), fup(LM[2], 12), A, CJ, Jl);
  \\ (a) J(m) <= max(J_last, A ln m + 1) <= CJ ln m
  chk("(a) A ln m + 1 <= CJ ln m, i.e. ln m >= 50", LM[1] >= 50);
  chk("(a) J_last <= CJ ln m", CJ*LM[1] >= Jl);
  \\ (b) D(m) <= ln m, mu = (m + 3 - D)/3 >= (999/1000) m/3; y <= 1800 J^2; y/mu <= e1, 1/(2 mu^(1/2)) <= e2
  my(lnD = lnB(100*CJ*LM[2]), ln3 = lnB(3), Dbound = rup(lnD[2]/ln3[1] + 1));
  chk("(b) log_3(100 CJ ln m) + 1 <= ln m at 10^30 (the difference increases in ln m)", Dbound <= LM[1]);
  chk("(b) ln m <= m/1000 at 10^30 (ln m / m decreases)", LM[2] <= mm/1000);
  chk("(b) D(m) <= 30 at 10^30 (window of (B'); D(m) = O(log log m), and m + 1 - D(m) > m1 - 30 trivially)", Dbound <= 30);
  my(e1 = rup(1800*CJ^2*3000/999 * LM[2]^2/mm), e2 = rup(1/(2*sqrt_dn(999*mm/3000))));
  printf("  y/mu <= %s, 1/(2 mu^(1/2)) <= %s ((ln m)^2/m and m^(-1/2) decrease)\n", eup(e1, 6), eup(e2, 6));
  my(ps = rdn(1 - ((1 - c0) + e2)/(1 - e1)), q = rup(1 - (197/300)*ps), lam = rdn(-lnB(q)[2]));
  printf("  jackpot p_D >= %s; q = 1 - (197/300) p_D <= %s; lambda = ln(1/q) >= %s\n", fdn(ps, 15), fup(q, 15), fdn(lam, 15));
  my(c2 = rdn(18*(1/3 - 2/3*lnB(3/2)[2])), c3 = rdn(12*kl_low(1/12, 1/4)));
  printf("  c2 = 18 h(2/3) >= %s; c3 = 12 KL(1/12, 1/4) >= %s\n", fdn(c2, 15), fdn(c3, 15));
  printf("  A lambda >= %s, A c2 >= %s, A c3 >= %s\n", fdn(A*lam, 12), fdn(A*c2, 12), fdn(A*c3, 12));
  chk("(f) A lambda > 1, A c2 > 1, A c3 > 1", A*lam > 1 && A*c2 > 1 && A*c3 > 1);
  chk("(g) CJ ln m + 1 <= 10^-27 m at 10^30", CJ*LM[2] + 1 <= mm/10^27);
  my(t1 = expB((1 - A*lam)*LM[1])[2], t2 = expB((1 - A*c2)*LM[1])[2], t3 = expB((1 - A*c3)*LM[1])[2]);
  my(Phi = rup((1 + 10^-27)/3*(q*t1 + t2 + t3)));
  printf("  (K1) for m >= 10^30: ((m + J + 1)/3) LJ(m) <= %s\n", eup(Phi, 6));
  chk("(K1) past 10^30: Phi(10^30) <= eps", Phi <= eps);
  \\ (h) (K2): the last interval's p1 stays a valid lower bound at every m >= 10^30 with k = a9 J(m)
  chk("(h) a9 > 4 (so that P(Bin(a9 J, 1/4) < J) <= exp(-a9 J KL(1/a9, 1/4)) decreases in J)", a9 > 4);
  chk("(h) 3 a9 J(m)/(m + 2) at m = 10^30 <= 3 a9 J_last/(M_97 + 2) (k/mu_m(1); ln m/(m + 2) decreases)",
    3*a9*CJ*LM[2]/(mm + 2) <= 3*a9*Jl/(Ml + 2));
  my(L = l1_9(Jl, a9, Ml), L1 = L[1], sig = (1/3 - eps)*(1 - L1) - c0/3);
  printf("  L1(m) <= L1 of the last interval <= %s; slope sigma >= %s\n", fup(L1, 10), edn(sig, 6));
  chk("(h) sigma > 0", sig > 0);
  chk("(h) base of the last interval <= b1", ((c0*(Ml + 3) + Jl - 2)/3)/(1 - L1) - (1/3 - eps)*(Ml - m1) <= b1);
  chk("(h) sigma (1 - M_97/10^30) >= (CJ/3) ln m/m at 10^30 (ln m/m decreases)", sig*(1 - Ml/mm) >= CJ/3*LM[2]/mm);
  printf("past 10^30: %s; %.1f s\n", if(OKP, "all inequalities hold", "FAIL"), (getabstime() - t0)/1000.);
  if (!OKP, NBAD++);
  DONEP = 1;
}
printf("series terms %d\n", NSER);
VOK = (NBAD == 0 && NINT == 95 && DONE1 && DONEP);
printf("verdict inputs: failing %d, interval lines %d of 95, interval block %s, past 10^30 block %s\n", NBAD, NINT, if(DONE1, "completed", "NOT completed"), if(DONEP, "completed", "NOT completed"));
printf("(D'check) in MODE 1 with outward rounding: %s\n", if(VOK, "PASS", "FAIL"));
quit;
