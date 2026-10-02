\\ The values of the certificate at the start state s_0 = (1, {F, F, F, F}, 1), its state 0 (Proposition 7.1 (6) and
\\ (7)): u(s_0)[8] = W'(s_0)[8] / 2^40 against eps theta^9, and the mass of L, the sum of V'(s_0)[x] / 2^40 over the
\\ 495 compositions x, against 1 - eps. Reads the table file and the certificate, unpacked, at the path in the
\\ environment variable CERT. Run: CERT=PATH gp -q start_values.gp < /dev/null | diff - start_values.out
\p 30
f = getenv("CERT");
line(k) = my(v = externstr(Str("grep -m1 '^", k, " ' ", f))); if(#v != 1, error("no line ", k)); strsplit(v[1], " ");
s = line("state 0");
if(s[3..#s] != ["1", "1", "1", "F", "F", "F", "F"], error("state 0 is not s_0"));
V = apply(eval, line("V 0")[3..-1]);
W = apply(eval, line("W 0")[3..-1]);
T = #W - 1;
Lt = externstr("cat ../certificate/table.cert");
par(k) = for(n = 1, #Lt, my(w = strsplit(Lt[n], " ")); if(#w == 2 && w[1] == k, return(eval(w[2]))));
eps = par("eps"); th = 5*par("phi") - 4*par("kappa");
u = W[T + 1] / 2^40;
print("T = ", T, "; values of V'(s_0): ", #V);
print("u(s_0)[T] = ", u, " = ", u * 1.);
print("eps theta^(T + 1) = ", eps * th^(T + 1) * 1.);
print("u(s_0)[T] < eps theta^(T + 1): ", u < eps * th^(T + 1));
mL = vecsum(V) / 2^40;
print("mass of L - (1 - eps) = ", mL - (1 - eps), " = ", (mL - (1 - eps)) * 1.);
