\\ The numbers of the paper that the Lean kernel decides as inequalities, printed here as values for reading:
\\ 5 gamma / (1 - gamma) (Section 2), the constants of the table (Proposition 7.1 (1) to (3) and (6)): the sum of
\\ pi delta over the root row, E B*(1), phi rho, M, kappa^4 - M, theta, theta rho and eps theta^9, and the size of
\\ the table (Section 7), read from the table file. Run: gp -q small_checks.gp < /dev/null | diff - small_checks.out
\p 30
g = 9337230319347/17448304640000;
print("gamma = ", g, " = ", g * 1.);
print("5 gamma/(1 - gamma) = ", 5*g/(1-g), " = ", 5*g/(1-g) * 1.);
print("5 gamma/(1 - gamma) < 5.756: ", 5*g/(1-g) < 5756/1000);
L = externstr("cat ../certificate/table.cert");
par(k) = for(n = 1, #L, w = strsplit(L[n], " "); if(#w == 2 && w[1] == k, return(eval(w[2]))));
J = par("J"); T = par("T"); eps = par("eps"); rho = par("rho"); phi = par("phi"); kappa = par("kappa");
tr = [];
for(n = 1, #L, w = strsplit(L[n], " "); if(#w >= 6 && w[1] == "tr", tr = concat(tr, [[eval(w[2]), w[3], eval(w[4]), w[5], eval(w[6])]])));
s = sum(k = 1, #tr, if(tr[k][1] == 0, tr[k][5] * tr[k][3]));
print("sum of pi delta over the root row = ", s, " = ", s * 1.);
print("(1 - eps) sum + eps (T + 1/(1 - rho)) = gamma: ", (1 - eps)*s + eps*(T + 1/(1 - rho)) == g);
\\ r_q(s) = sum over the row of s of pi phi^delta r_(q+1)(s'), r_J(end) = 1
r = Map(); mapput(r, [J, "end"], 1);
forstep(q = J - 1, 0, -1, for(k = 1, #tr, if(tr[k][1] == q, my(key = [q, tr[k][2]], v = tr[k][5] * phi^tr[k][3] * mapget(r, [q + 1, tr[k][4]])); mapput(r, key, if(mapisdefined(r, key), mapget(r, key), 0) + v))));
M = (1 - eps) * mapget(r, [0, "root"]) + eps * (1 - rho) * phi^(T + 1) / (1 - phi*rho);
th = 5*phi - 4*kappa;
print("phi rho = ", phi*rho * 1.);
print("M = ", M * 1.);
print("kappa^4 - M = ", (kappa^J - M) * 1.);
print("theta = ", th, " = ", th * 1.);
print("theta rho = ", th * rho * 1.);
print("eps theta^9 = ", eps * th^(T + 1) * 1.);
\\ The size of the table (Section 7): labels per level, rows, transitions, the denominators, the atoms of P_tab.
nlab(q) = sum(n = 1, #L, my(w = strsplit(L[n], " ")); #w == 3 && w[1] == "label" && eval(w[2]) == q);
print("labels at levels 1 to ", J - 1, ": ", vector(J - 1, q, nlab(q)));
print("rows: ", #Set(vector(#tr, k, [tr[k][1], tr[k][2]])), "; transitions: ", #tr);
print("every pi a multiple of 2^-28: ", vecmax(vector(#tr, k, denominator(tr[k][5] * 2^28))) == 1);
\\ P_tab, the law of (B(1), ..., B(J)) along the label paths from the root to the end
add(~m, key, v) = mapput(~m, key, if(mapisdefined(m, key), mapget(m, key), 0) + v);
step(cur, q) = {
  my(nxt = Map(), K = Mat(cur));
  for(i = 1, matsize(K)[1],
    my(v = K[i, 1][1], s = K[i, 1][2], m = K[i, 2]);
    for(k = 1, #tr,
      if(tr[k][1] == q && tr[k][2] == s,
        add(~nxt, [concat(v, if(#v, v[#v], 0) + tr[k][3]), tr[k][4]], m * tr[k][5]))));
  nxt;
}
cur = Map(); mapput(~cur, [[], "root"], 1);
for(q = 0, J - 1, cur = step(cur, q));
K = Mat(cur); A = Map();
for(i = 1, matsize(K)[1], add(~A, K[i, 1][1], K[i, 2]));
KA = Mat(A);
print("atoms of P_tab: ", sum(i = 1, matsize(KA)[1], KA[i, 2] > 0), "; total mass: ", vecsum(KA[, 2]));
