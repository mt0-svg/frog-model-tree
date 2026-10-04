\\ Branches of the table of Proposition 15.2 of the paper (the induction of Theorem 14.1 in MODE 1 of scale4.gp):
\\ the row (c0, eps) = (0.6, 0.02) from m1 = round(10^6.25) = 1778279, with Lemma 11.5 of the paper for the
\\ J-closure and Lemma 11.4 for the 1-closure only (not the recursion of dp15.gp). Floating point search with the functions of scale4.gp (MODE 1); it only proposes the
\\ branches, which dcheck_m1.gp then checks in exact rationals with outward rounding.
\\ On each interval [M(i), M(i + 1)], M(i) = round(10^(5.5 + i/4)), i = 3..97, J is the least index
\\ >= the previous one for which some branch of Lemma 11.5 (D <= 30, a in {6, 8, 12}, b in {1.5, 2}) gives
\\ (K1) and some branch of Lemma 11.4 (k = a J, a in {4, 6, 8, 12, 16}) gives the slope condition.
\\ Output: gp code CERT = [[J, D, a, b, a9, "Lemma 10 ...", "Lemma 9 ..."], ...] (dcheck_m1_cert.gp);
\\ the labels "Lemma 10" and "Lemma 9" of the entries name Lemmas 11.5 and 11.4 of the paper.
\\ Usage: gp -q dbranch_m1.gp < /dev/null > dcheck_m1_cert.gp (from this directory).
MAINRUN = 0; MODE = 1;
read("scale4.gp");
default(realprecision, 38);
C0 = 0.6; EPS = 0.02;
M(i) = my(f = sqrtint(sqrtint(16*10^(22 + i)))); (f + 1) \ 2;
lj(J, ml) =
{
  my(best = 1., br = 0);
  for (D = 1, 30,
    if (J*3.^(-D) > 2/3, next);
    foreach ([6, 8, 12], a, foreach ([3/2, 2], b,
      my(k = a*J, y = ceil(b*k*3^(D-1)), ps = lem12(C0, (ml+3-D)/3., y));
      if (ps <= 0, next);
      my(v = (1 - (2/3 - J*3.^(-D))*ps)^(J+1) + blt(y, 3.^(1-D), k) + blt(k, 1/4, J));
      if (v < best, best = v; br = [D, a, b]))));
  [best, br]
}
l1(J, ml) =
{
  my(best = 1., br = 0);
  foreach ([4, 6, 8, 12, 16], a,
    my(k = a*J, p1 = lem12(C0, (ml+2)/3., k));
    if (p1 > 0, my(v = 1 - S(p1) + blt(k, 1/4, J)); if (v < best, best = v; br = a)));
  [best, br]
}
{
  my(Jp = 1, out = List());
  for (i = 3, 97,
    my(ml = M(i), mh = M(i + 1), ok = 0);
    for (J = Jp, 400,
      my(A = lj(J, ml));
      if ((mh + J + 1)/3*A[1] > EPS, next);
      my(B = l1(J, ml));
      if ((1/3 - EPS)*(1 - B[1]) < C0/3, next);
      listput(out, Strprintf("[%d, %d, %d, %d/2, %d, \"Lemma 10 D=%d a=%d b=%.1f\", \"Lemma 9 k=%dJ\"]",
        J, A[2][1], A[2][2], 2*A[2][3], B[2], A[2][1], A[2][2], A[2][3], B[2]));
      Jp = J; ok = 1; break);
    if (!ok, error(Str("no branch on interval ", i))));
  print("{CERT = [", strjoin(Vec(out), ",\n"), "];}");
}
quit;
