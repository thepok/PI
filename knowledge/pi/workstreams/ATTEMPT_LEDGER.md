# Compressed attempt ledger

This is route-family memory, not a prohibition list. A research prompt should
carry at most three nearby rows. Historical transcripts are deliberately not
preserved here.

| Route family | Strongest durable lemma | First fatal line | Reopen only with |
|---|---|---|---|
| Generic lacunary, metric, topological, complexity | Finite irrationality exponent gives an adaptively selected positive primitive unit, and Bellman choice gives unit ladders (`proof sketch`; T191--T194 contain the checked analytic seed). Stronger still, a transcendental `mu=2` deleted-digit continuation can eventually realize every one of the `9^k` labels of a proper alphabet as a central positive unit inside `[10^k,10^(k+1))`. [Kleinbock--Weiss](https://doi.org/10.1007/BF02772538) and [Kristensen--Thorn--Velani](https://arxiv.org/abs/math/0405433) supply a badly approximable `{1,2}`-digit orbit, hence one with exact `mu=2`, for which the generic central-unit and predecessor-lift premises hold at every time and scale (`literature-checked` existence, `proof sketch` analytic transfer). [Fishman's later Schmidt-game formulation](https://arxiv.org/abs/0809.2065) supplies the winning/countable-intersection strengthening. An elementary Furstenberg corollary strengthens mixed recurrence: for every irrational `x`, prescribed open target, floor residue, and modulus `M`, one fixed off-diagonal ray `p^(Mb)*10^n*x` realizes the target and residue infinitely often (`proof sketch`; Furstenberg input literature-checked). For multiplicatively independent integers `b,r>=2` and irrational `x`, a corrected omega-limit argument gives `T_r x in closure{T_b^n x}` iff the base-`b` orbit is dense (`proof sketch`; Furstenberg input `literature-checked`, independently audited). For every forbidden nonempty decimal word and compatible finite prefix there is a Borel family of exact dimension `s=log 2/log 10` whose members avoid the word, are transcendental with irrationality exponent at most `2/s`, and are simultaneously normal in every integer base multiplicatively independent of `10` (`proof sketch`; [Algom--Baker--Shmerkin](https://arxiv.org/abs/2111.10082) input `literature-checked`, independently audited). More sharply, an explicit prefixed decimal Bernoulli measure has `nuHat(k)=0` whenever `v2(k) != v5(k)` after removing the prefix scale. For every preassigned countable family of coordinatewise strictly increasing paths `(r_n,s_n)` with `|r_n-s_n| -> infinity`, almost every point for this measure is uniformly distributed along every `2^(r_n)5^(s_n)` path, while its exact decimal diagonal avoids the prescribed word forever; one may choose such a point transcendental with `mu_irr <= 2*log(10)/log(5)` (`proof sketch`, independently audited). | T194's coordinate identity is `10^k*x_n-floor(10^k*x_n)-1/2=x_(n+k)-1/2`; its target is selected after observing the orbit, and identifying it with a fixed `A*` is already the desired cylinder hit. The proper-alphabet examples can therefore have abundant central capital while omitting a prescribed word forever. The fixed-ray hit pulls back under `p=2` to an exact union of `10^r` deeper decimal aliases rather than the literal target; a `mu=2` word-avoider satisfies every such transformed recurrence while missing the diagonal word. Even a single cross-return `T_r x in closure{T_b^n x}` is not a cheap synchronization rung: for irrational `x` it is already equivalent to full base-`b` density. For fixed irrational `theta`, word `w`, and `sigma<1`, an eventual directed gap `c*10^(-sigma*n)` from all lower `w`-avoiding decimal endpoints exists iff `w` already occurs in `theta`; by Northcott, bounded degree/height holonomy classes are finite, so a freely chosen class constant merely hides their first target occurrences (`proof sketch`, independently audited). Even simultaneous normality in every independent integer base remains compatible with literal decimal word avoidance. More strongly, every selected escaping-offset path may have the correct target density even when its projective slope tends to the decimal diagonal, while the exact diagonal target sign stays negative: projective proximity does not control the singular absolute resonance `v2=v5`. This does not cover the diagonal or any bounded-offset tube `r_n-s_n=c`. Thus abundance, finite `mu`, mixed recurrence, marginal cross-base normality, escaping-offset equidistribution, finite-class gap constants, or one suffix-local ladder do not supply prescribed target sign. The retired topological entry's durable fatal line is that even full-circle omega spread along the zero-residue slice for every modulus can coexist with density-one shadowing of the harmful `1/3` fixed point and arbitrarily long negative literal-sector blocks; its BA continuation and all-label conclusion are strengthened by Theorems A and B (both independently audited `proof sketch` results). | A selected-node actual-pi accumulation/transition theorem controlling the intervening target-weighted blocks and false on deleted-digit, period-one and sparse-prefix continuations; for a cross-base route, an independent π-specific theorem native to the exact `v2=v5` diagonal, or a uniform absolute-phase coupling across a bounded-offset tube down to offset zero, with a direct literal base-10 target consequence and failure on the finite-exponent word-avoiding family. A one-point return can reopen only with a named actual-π mechanism selecting the literal diagonal or correct inverse branch for a target fixed beforehand; proving the return itself already proves density. A gap route requires an independently derived regular-language-sensitive estimate with `sigma<1`, uniform over a genuinely infinite arithmetic family with constants fixed before locating any target occurrence. More marginal normality, countable escaping paths, or punctured-cone Fourier cancellation is insufficient. |
| BBP, p-adic fibres, residues, rational shadows | The strongest retained base-10 shadow package is now `machine-checked`: `Theory.PiDigits.T199BBPShadowPack.bbp10_soh0_iff_piCW0` proves `SOH⁰_{BBP,10} ↔ CW0`, and `bbp10_rightApproach_iff_piCW0` and `bbp10_leftApproach_iff_piCW9` prove the two one-sided approach equivalences. These are representation-level results, not π progress; the Archimedean-lift obstruction stands. Exact BBP residue systems and positive scalar tails can be retained while the Archimedean phase or rotated Fourier sign changes. The delayed errors `10^n*(pi-bbpRealPartial(n+K))` form a strict Hausdorff moment sequence on `(0,5/8)`, and yield an exponentially sharp full-primitive same-child stability bound (`proof sketch`). More sharply, for the inclusive rational BBP partial `B_n=P_n/D_n`, `|norm((10^n-16)pi)-norm((10^n-16)B_n)|<(5/8)^n`; hence T69's fixed-sixteen return is exactly `liminf min(r_n,D_n-r_n)/D_n=0`, where `r_n=(10^n-16)P_n mod D_n` (`proof sketch`, independently audited). With `E_n=(10^n-16)(pi-B_n)`, the exact scalar residue forcing satisfies `Theta_n-144*pi=10E_n-E_(n+1)`; translation by `E_n` conjugates every one-step and fixed block transfer to the fixed affine pi-orbit. The final focused audit also proves `144*pi<Theta_(n+1)<Theta_n` for `n>=2`, so `Theta_n` is a strict rational upper approximation to `144*pi`. Every fixed finite complex linear filter of the unwrapped `X_n=(10^n-16)B_n` decomposes exactly into the modes `pi*10^n*C(10)`, `-16*pi*C(1)`, and a remainder bounded by `(4/15)*(5/8)^n*sum_j |c_j|*(5/8)^j`; annihilating both modes leaves only the exponentially decaying BBP tail (`proof sketch`, independently audited). Cubic Riesz--Jacobi lattice sums likewise give an explicit power-of-ten rational shadow with error `O(10^-m)`, an exact divisor-floor numerator, and a decimal cocycle. At one scale its unsigned enclosure decides a target exactly off the boundary radius; inside that radius two quadratic-irrational `mu=2` replacements flip the target. The full packet satisfies `RJ(theta) iff theta=pi`, while fixed-depth `2/5`-adic data are cell-translation invariant (`proof sketch`). A nonlinear translated variant exponentiates integral cubic Riesz counts before first-character projection: its unique unit dual vector gives an eventually positive imaginary amplitude, and for fixed `q>=10` and finite `H`, `U_(h+1,q)(R)/((h+1)U_(1,q)(R))=e(h*pi*R)+O_(q,H)(R^(-7/2))` simultaneously for `1<=h<=H` and all sufficiently large integer `R` (`proof sketch`, independently audited; Poisson--Bessel background only literature-checked). | Every finite moment truncation is shadowed by nearby replacement constants; the dual range over positive-density measures is exactly `[min P,max P]`, so total positivity cannot create a target-polynomial sign. The BBP interpolation is off the decimal orbit for every interior parameter, and its fresh dual has a forced `t^q` factor. BBP valuations, positive tails and even the strict scalar order `Theta_n downarrow 144*pi` do not control whether `r_n/D_n` approaches either endpoint: `(10^n-16)B_n=k_n+r_n/D_n` contains an unknown integer lift, while the forcing deviation is the removable coboundary above. Fixed finite linear filters therefore either retain the unknown decimal `10^n*pi` mode or collapse to constant plus scalar tail; applying `fract`, floors or digits reintroduces the unresolved wrap. Zudilin's advertised base-five BBP-style extraction explicitly fails when `2n+1>d-k`: an uncancelled `5^(2n+1-d+k)` remains in the denominator, while truncating before this range loses the tail bound (`literature-checked`; independently audited). A targeted PaperSearch audit found only universal perturbed-orbit coupling, fixed-modulus automatic congruences and probabilistic pi heuristics; none orders the canonical residue in the moving modulus (`literature-checked`, 2026-08-30). Separate base-five/base-sixteen data then recombine only through universal floor/CRT recodings. The fixed-sixteen return is already conditionally equivalent to V1 by T69 and Furstenberg. For the Riesz shadow, guarded prescribed high-residue recurrence has V1 strength (and is equivalent after standard padding); linear target characters discard the area zero mode, while exponentiate--project--normalize restores the whole phase only by cancelling the oriented auxiliary amplitude. It therefore yields a wrap-aware cyclotomic exactification, not a target half-plane sign; its compatibility property uniquely selecting `pi` is the existing `RJ(theta) iff theta=pi` phenomenon in nonlinear coordinates, and its all-word cylinder comparator is V1-equivalent after padding. Approximation accuracy and exactification therefore do not manufacture the sign. | Reopen only with a wrap-aware, adaptive or genuinely nonlinear numerator quantity that breaks `r_n <-> D_n-r_n`, has a proved distinguished-real sign, and forces one-sided Archimedean control of `r_n/D_n` on an unbounded subsequence; alternatively a cross-base identity bounding the Furstenberg exponent offset absolutely to one, or a proved target- and child-dependent inequality using structure beyond approximation. For the nonlinear Riesz packet this specifically requires an independently derived `R -> 10R` numerator or bilinear law signing the target-rotated ratio without using its proximity to `e(h*pi*R)` or locating the cylinder first. More fixed finite filters, scalar forcing refinements, fixed-modulus automata, moment-cone structure, denominator factorization, p-adic shells, mixed recurrence, generic duality, exact divisor formulas, separate radix formulas, phase reconstruction, or accuracy are insufficient. |
| BBP base-16 dynamical orbit (Bailey--Crandall) | For the BBP orbit `Y_0=0`, `Y_(n+1)=16Y_n+R(n)`, `R(n)=4/(8n+1)-2/(8n+4)-1/(8n+5)-1/(8n+6)`, the finite-attractor branch of Hypothesis A is excluded unconditionally for pi: the forced orbit has finitely many limit points iff the represented number is rational ([Bailey--Crandall 2001](https://doi.org/10.1080/10586458.2001.10504441) Thm 2.10/3.1, [Lagarias 2001](https://arxiv.org/abs/math/0101055) Thm 3.1/3.3; `literature-checked`), so `(y_n)` has infinitely many limit points; density of `(y_n)` is equivalent to base-16 disjunctivity and is open (Lagarias's Weak Dichotomy). The forcing is an exact coboundary, `R(n)=16*tau_n-tau_(n+1)` with `tau_n=sum_(j>=0) R(n+j)/16^(j+1)=1/(64n^2)+O(n^-3)>0`, so `{Y_n+tau_n}={16^(n-1) pi}` exactly: the skew orbit is the base-16 orbit of pi after a time-dependent translation (`proof sketch`). Van der Corput differencing at lag `r` maps frequency `h` to `(16^r-1)h` with a negligible pole factor. A 2-adic invariant graph `Phi(t)=sum_(j>=1) 16^(j-1) R(t-j)` satisfies `Phi(t+1)=16 Phi(t)+R(t)` and `Y_n-Phi(n)->0` in `Q_2` (`proof sketch`). | Turning the moving-modulus rational lift `Y_n=K_n+A_n/D_n` into Archimedean order: the carry in `16 A_n/D_n+R(n)=c_(n+1)+A_(n+1)/D_(n+1)` is exactly the digit to be predicted, one canonical numerator per changing odd modulus, no averaging variable and no fixed modulus over a long block. `A_n <-> D_n-A_n` preserves all valuation data and reverses the orientation. Same obstruction as the base-10 BBP and Machin rows. | A numerator-sensitive, moving-modulus exponential-sum or shrinking-target theorem for the one canonical BBP residue selected at each time (e.g. a deterministic bound excluding infinitely many visits `\|\|16^n pi - a\|\| << n^-2` to cylinder boundaries), false for a base-16 word-avoiding replacement seed. No irrational BBP-type number with everywhere-active rational forcing has proved density in its base (`literature-checked`, 2026-09-02); Stoneham/Korobov proofs need a fixed modulus over long blocks, which pi's orbit does not have. |
| Machin, Padé, Leibniz and positive-period carriers | An endpoint-corrected Leibniz carrier has private scale `p^-1` and positive error `O(p^-9)`. Exact large-`p` transport controls every primitive ray by its last temporal layer within relative `pi/18`; Dalzell powers give explicit two-sided rational brackets for `pi`. The Euler--Wallis spigot gives rational nested enclosures `C_m([3,4])` of `pi` with exact width `2^m*(m!)^2/(2m+1)!<2^-m`, and every actual decimal hit eventually admits a safe rational endpoint certificate (`proof sketch`, independently audited). For every `q=10^k` and horizon `N`, the literal T139 functions at `(x,A)=(4/9,4(q-1)/9)` and `(5/9,5(q-1)/9)` have identical strictly positive scores but exactly opposite nonzero derivatives (`proof sketch`, independently audited). A positive relative-period carrier `g(x)=5x^2(1-x)^2(x^2-x+1)` has exact decimal pole value `g(i)=10`: for `Q_n=(g^n-10^n)/(1+x^2)` and `a_n=4*integral_0^1 Q_n`, one has `Q_n in Z[x]` and `0<10^n*pi+a_n<pi*(15/64)^n` (`proof sketch`, independently audited). If `n>1` and `p=6n-1` is prime, then `v_p(a_n)=-1`; hence the raw carrier is nonintegral at infinitely many levels (`proof sketch`; infinitude of primes `p=5 mod 6` literature-checked, independently audited). Writing the rational companion as `r_n=A_n/D_n` and choosing `s_n=-A_n mod D_n`, the monomial correction `P_n#=4g^n+(1+x^2)s_n*x^(D_n-1)` preserves positivity and pole value while making the companion integral exactly `ceil(r_n)`. More sharply, for every fixed `k` and `0<beta<1`, unrestricted-degree general PL8 existence, derivative-lattice PL8 existence and `0<{10^k*pi}<beta` are equivalent (`proof sketch`, independently audited). At `q=1/10`, little-q-Legendre Pade forms give integer one-sided approximants to the Lambert value `h_10(1)`, while the exact q-reflection identity for `pi` retains both `Gamma_(1/10)(1/2)` and the dual nome `exp(-pi^2/(2*log 10))` ([Van Assche](https://arxiv.org/abs/math/0101187), [El-Guindy--Mansour](https://arxiv.org/abs/1309.4585); `literature-checked`, independently audited). Two-sided Machin brackets also give an exact second-order chord bound for the literal primitive packet: barycentric interpolation cancels the first derivative and leaves error at most `(delta_minus*delta_plus/2)*norm(f'')`, with `norm(f'') <= (4*pi^2/99)*(10^(2*N)-1)*M_2(q,A)` and `M_2(q,A)<10*q^2` (`proof sketch`, independently audited). | Neither approximation nor coefficient positivity signs the distinguished real embedding. Every route ending only in `pi=r+epsilon`, `epsilon>0`, collapses to `Phi(pi)-Phi(r)=epsilon*integral Phi'(r+t*epsilon)dt`; positive remainder density gives length, not the target-rotated derivative sign. Universal existence of safe Euler--Wallis endpoint certificates is equivalent to the original cylinder-hitting claim: enclosure width supplies a certification horizon but no target alignment. Exact tenth-root filtering reconstructs the child polynomial at `e(-C_child)*exp(2i*10^n*pi^2)` but does not preserve Padé endpoint order: already Sorokin's improper but finite integral at `z=1` is positive and its regular value at `z=-1` is negative (`proof sketch`). The mirror period-one twins show the orientation bit is independent of favorable score, denominator, period and unsigned phase data. The exactified value is `s_n/D_n+J_n` and can equal either `{10^n*pi}` or `1+{10^n*pi}`; even a bound below one selects the unknown lower integer lift. In derivative form the endpoint is exactly `-floor(10^k*pi)`. Thus positivity, integrality and unrestricted-degree approximation realize a chosen chamber but cannot choose it. The exact rational recurrence `s_(n+1)/D_(n+1)={10s_n/D_n+e_n}` has positive exponentially decaying kicks, but such nonvanishing kicks admit a high-chamber orbit trapped forever in `[8/9,1)`, so sign and decay alone do not orient the distinguished initial condition (`proof sketch`, independently audited). Large carriers merely resolve the chamber already containing pi unless an independent oriented input enters. The q-Lambert signs and q-reflection identity therefore miss at the value level: the denominator-controlled positive remainder belongs to `h_10(1)`, whereas the exact `pi` value retains nonrational/self-referential factors; removing them leaves only another scalar enclosure. Two-sided Machin interpolation closes the obvious first-order loophole but moves the unknown orientation into the target-rotated curvature and the two complete cyclotomic endpoint packets. Opposite curvature signs occur on two missed targets of the same period-one orbit (`experiment`, independently reproduced), while keeping the interpolation error `O(1)` forces `m >= (log(10)/(4*log(5)))*N+O(log q+log m)`, so the endpoints shadow essentially the whole horizon phase. | A complete target-weighted half-plane inequality for the rotated Padé remainders, cross-ray target-phase control or deterministic target alignment for the Euler--Wallis endpoints, a nonseparable positive kernel with its target dual already signed, or an actual-pi theorem signing the complete horizon defect and distinguishing the `4/9`--`5/9` twins. Do not reopen the positive-period line with another exactifier, Bernstein approximation or residue scan. Require a named numerator-derived, non-coboundary theorem orienting the distinguished residues on an explicit unbounded set, false on a suitable word-avoider, and upgraded to a fixed digit, prescribed cylinder or literal T189 sign without choosing from `floor(10^n*pi)`, testing `s_n/D_n`, or assuming the desired chamber. A q-Lambert route additionally needs a rational/algebraic-q identity whose target-rotated form has controlled algebraic denominators and a half-plane sign without a `pi`-dependent dual nome or q-Gamma integration constant. |
| CM, singular moduli, modular traces | The shadows `U_n=(1/2)log j(i·10^n)=pi·10^n+epsilon_n` have exponentially tiny positive error and exact cocycle `U_(n+1)=10U_n-rho_n`. On the distinguished positive real branch, `9epsilon_n<rho_n<10epsilon_n` and `0<j(i·10^(n+1))/j(i·10^n)^10=exp(-2rho_n)<1` (`proof sketch`, independently audited). For `N=10^n`, the principal root `j(iN)` of the ring-class polynomial of discriminant `-4N^2` is the sole root outside `R_N=e^(2*pi*N/3)+2079`; hence `sgn H_N(M)=sgn(M-j(iN))` for real `M>R_N`. Together with the known irrationality-measure bound, this makes the comparator uniformly complete after an onset for every fixed decimal denominator and boundaries restricted to `[3N,4N]`. Additive class-character traces still satisfy `|T_(chi,N)-j(iN)|≤4N^2 R_N`, uniformly in `chi`, so even their growing rank retains the same target-blind dominant real direction (`proof sketch`; CM magnitude and irrationality-measure inputs `literature-checked`; independently audited). Varying-`M` principal CM rays retain exact `Phi_10` edges while realizing arbitrary finite scalar words; a controlled Siegel product decodes one lifted orbit plus a cusp tail. For a fixed cusp germ `F(Q)=Q^nu U(Q)`, every nonzero additive horizontal character kills the common affine cusp slope: with canonical lifts and `1≤r<q`, `sum_a zeta_q^(-ra) log F(rho zeta_q^a) = -2*pi*i*nu/(1-zeta_q^(-r)) + q sum_(m≡r mod q) b_m exp(-2*pi*m*T/q)` (`proof sketch`, independently audited). At `N=10^n`, the complete elliptic period/quasiperiod matrix `P_N=[[K,iK'],[E,i(K'-E')]]` has `det P_N=-i*pi/2`, while `K'=N*K`; this Legendre minor is independent of `n,A,d`, and `2N*(pi/2)=10^n*pi` merely reconstructs the original decimal orbit (`proof sketch`, independently audited; Legendre/quasiperiod and degree-10 modular inputs `literature-checked`, 2026-08-31). | Even the fixed `M=1` order supplies no phase: restoring `epsilon_(n+1)=10epsilon_n-rho_n` cancels `e(-h rho_n)` exactly and returns `e(h*pi*10^(n+1))=e(10h*pi*10^n)`. The modular polynomial and positive-root order contain no target character. Requiring the corrected ring-class sign pair for every prescribed word at some late scale is exactly decimal disjunctivity; evaluating enough individual comparisons merely replays the fresh digits. Class-character twists cannot rotate the dominant term because `chi(1)=1`, while subtracting two such traces removes that principal term. The Siegel characteristic likewise changes only an integer power of the same lifted phase, not an independent coordinate. More generally, `-(2*pi*nu*T/q) sum_a zeta_q^(-ra)=0` for `r≠0`: a fixed-germ finite horizontal packet retains only a `T`-independent Fourier constant and decaying residue-class tails. Target rotation does not preserve the eta tail's unrotated sign. Complete rank-two period minors do not repair this: symplectic basis changes preserve the Legendre determinant, target-character twists insert only an external gauge phase, torsion translation changes no complete period, and the degree-10 isogeny changes homology determinant independently of the chosen child. This closes fixed rank-one additive packets, additive ring-class character traces, and complete rank-two period/quasiperiod data under homology gauge or torsion translation; it does not close incomplete periods at non-torsion algebraic points, moving or `a`-dependent germs, nonlinear/dynamic coupling, interacting cusp strata, or native oscillatory trace/spectral terms. | Reopen only with a native nonzero-target-character orbit-scale oscillation and a proved signed transfer to the complete same-child or flexible-horizon expression. A rank-two elliptic reopening specifically requires an `A,d`-dependent non-torsion algebraic point or correspondence, not related by common gauge, whose incomplete-period/holonomy amplitude has a distinguished-real sign and expands to the literal T179 carrier without first evaluating an elliptic logarithm equivalent to `{10^t*pi}`. |
| Euler zero, Gamma/Laplace, nonperiodic E-function frames | Half-grid factorization separates a positive suffix carrier from the literal signed target distance. The Gamma representation is a positive measure against one sign-changing threshold. Every absolutely convergent scalar translation kernel on the commuting `(1,pi)` lattice likewise has exact rectangular endpoint collapse `H_N-V_N=Phi({N*pi})-Phi(pi)`; logarithmically separable positive products obey the corresponding ratio identity (`proof sketch`, independently audited). More exactly, for `zeta=e(1/10)` and `1<=r<=9`, the nonzero-character reflection transform is `pi*sum_a zeta^(-r*a)*cot(pi*(z+a/10))=20*pi*i*e(z)^r/(e(10z)-1)` (`proof sketch`, independently audited). Euler-compatible frequencies after time `N` are exactly `2Z/10^N`, disjoint from nonzero unit-periodic frequencies `2piZ`; a bounded nonperiodic surrogate changing sign across a `1/Q` child needs bandwidth `Omega(Q)` (`proof sketch`). | Base-ten Gamma multiplication controls only the zero character; reflection restores every target-sensitive character only as a rational recoding of the original target-relative phase, with the `r=5` orientation flipping at reflected child-centered points. Moving Euler-reflection Gamma arguments to the positive real axis makes the loss exact: the remaining signs are `(-1)^floor(2y)` and `(-1)^floor(2y+1/2)`, precisely the original sine/cosine quadrant bits (`proof sketch`; DLMF 5.5.1 and 5.5.3 `literature-checked`; independently audited). Positive carrier, pole separation or measure therefore does not order the target factor. In the rectangular lattice packet, comparison with a target threshold is exactly the original inequality `{N*pi}<c`, and its finite cutoff already contains `floor(N*pi)`; the result does not cover regularized or nonseparable/non-diagonal spectral interactions. Euler's exact zero cannot act frequency-by-frequency on the decimal torus, while high-bandwidth Lindemann--Weierstrass gives nonvanishing rather than real order. For a fixed exponential polynomial `F(z)=sum_nu P_nu(z) exp(lambda_nu*z)`, all translates span dimension at most `sum_nu (deg P_nu+1)`; consequently every shifted-Euler determinant built only from translates of that fixed family vanishes above this rank (`proof sketch`, independently audited). This closes fixed finite-mode translate schemes only, not nonlinear products, moving/depth-dependent germs or growing mode families. The bandwidth statement is conditional on a stable localized surrogate. | An actual-pi half-plane inequality for the complete literal coefficient-weighted character block, or a one-sided high-bandwidth E-function/Hermite--Pade inequality for the complete selected-child form; qualitative transcendence, reflection/multiplication identities, or positive reparametrization is insufficient. A translate/determinant route additionally requires nontranslation-separable arithmetic rank growing with decimal depth and limit-stable distinguished-real order. |
| Theta / automorphic and lattice renormalization | Rivoal--Seuret's quadratic functional equation is pointwise at every irrational parameter (`literature-checked`, [arXiv:1211.5426](https://arxiv.org/abs/1211.5426)), but fixed `J` pure square-class blocks capture only `O(sqrt(J/q))` of literal T179 mass. Exact branch rotation gives `F_r(y+j/10)=e(rj/10)F_r(y)`, so unsigned theta data are identical while odd sectors flip sign. Separately, the square shells of the half-boundary Gauss discrepancy have a coherent negative `-S*sqrt(R)/(pi*sqrt(2))+O(R^-1/2)` channel at integer `R` (`proof sketch`). | Direct/affine theta reindexing degenerates; completion produces an unsigned lag-two correlation; no `SL_2(Q)` map realizes the decimal multiplier. For the full lattice count, the boundary correction is integral at `R=10^m` and the complete discrepancy modulo one is exactly the reflected original pi orbit; nonsquare shells are uncontrolled. These statements do not exclude nonlinear decoders, varying twists or `Omega(q)` classes. | A theorem orienting the actual determinant-10 branch or complete lag-two time sum; alternatively a target-sensitive subunit square-versus-nonsquare shell bound at `R=10^m`. Magnitudes, partial coherent signs and ordinary modular identities are insufficient. |
| New kernels or equivalent consumers | Central weights satisfy `9u_d<=p_d<=10u_d`; `M=sum p_d(D_d-max(0,-G_d))` has a self-financing lower bound and `M>0` supplies literal FMR (`proof sketch`). Exact predecessor routing inserts the selected carrier into the chosen child's old vector with transported mass `>=0.9p_d`. Corrected cross-energy `E>0` also supplies FMR and retains every character block. | None is generically hereditary. A transcendental `mu=2` replacement sharing the T173-certified first 10015 pi digits has `E>5.889*10^9` at `(1000,334)`, yet every one of its seven legal root FMR choices reaches a positive node with negative `E` and exactly one next FMR child (`experiment` plus `proof sketch`). Thus even persistent-FMR active-scale adaptive/existential heredity fails. Transported old mass cannot create the next fresh `p+`; adjacent parents remain disjoint refinement rays; telescoping `E` is equivalent to its open terminal sign. | Pause cross-energy as a primary proxy. Reopen only with an actual-pi selected-target theorem controlling weighted opposite-sign leakage or selection through information false for the pi-prefix `mu=2` separator. |
| Finite π prefix and certificate replay | Certified seed/replay levels prove T189 non-vacuous. At `(100000,51334)`, directed intervals certify `d=1` FMR and two same-target positive child atoms, one the exact predecessor lift of a central parent atom (`experiment`). Deterministically, selected-child positivity requires adverse-annulus count `R<=125H+27` (`proof sketch`). | The full fresh sign is independently computed, not implied by the atoms: the complement after removing the central atom is `<-629252`. A transcendental `mu=2` continuation can share any finite pi prefix and place two exact predecessor atoms in every later selected fresh block while forcing `D_1<-Q/225`. At the hard inherited child, a realizable period-four tail gives the literal prescribed sector-5 sum `<-7681` while preserving the old strict premises, so target-covariant multiplier-10 decimation and positive coefficient defects also do not orient that sector. Generic fixed-child fresh gain has mean `-21/10` over completions (`proof sketch`). | A selected-node theorem using genuinely fresh actual-π information at unbounded horizons and controlling the weighted negative complement or distinguished-real terminal shell; not another isolated certificate, finite-prefix continuation, or bounded family of central returns. |
| Counts and low-dimensional empirical statistics | Periodic, de Bruijn, and replacement-constant controls reproduce or reverse count/run/small-cell predictions; near-perfect predictors nearly evaluate (Xi) itself. The literal sector split `{0,2,6}` versus its complement puts both halves in the FMR cone at the selected root and all seven audited next parents (`experiment`). | Coarse statistics lose relative multi-sector phase and same-digit alignment. The unusually stable two-cone split already fails at the reached node `(100000,51334)`, where every full-FMR child loses at least one half. | An independently motivated π-specific order-sensitive theorem for the complete literal multi-sector vector, not another finite sector partition. |
| Zero sector, scalar moments, unsigned energy | Exact ray compression gives `P+N*c_q/2=(1/2)sum B_q+V(x_0)-V(x_N)`. More generally, a finite mean-zero trigonometric polynomial is an `L1` state-only decimal coboundary iff every primitive ray sum `sum_j fhat(10^j*r)` vanishes. For every one of T189's nine nonzero child sectors, the top frequency `h=2Q-(10-rho)` is alone on its ray and has residue `a_Q(h)e((10-rho)c_0)e(-rho*d/10)` with `a_Q(h)>(10-rho)/(3Q^2)` (`proof sketch`, independently audited). At one time the literal T179 polynomial also has nonzero coefficients on the `9q/5` distinct primitive rays `1<=h<=2q`, `10` not dividing `h`. Every nonconstant rational self-centralizer `Phi(z^10)=Phi(z)^10` is `omega*z^m`, with `m` a nonzero integer and `omega^9=1`; hence any formal per-time coefficient-linear Laurent reconstruction from forward iterates `Phi_j(lambda*Z^(10^a))`, `a` a nonnegative integer, has rank at least `9q/5` (`proof sketch`, independently audited). The native T179 time weight is rectangular, and shifted `1/100` Abel synthesis has linear coefficient variation. The literal T139 coefficient profile also lies outside both natural positive radial cones (`proof sketch`). On the pure mean-zero ten-child space, every fixed additive, nonnegatively homogeneous, pointed and cyclically invariant cone is trivial, since `-v=sum_(j=1)^9 S^j v` (`proof sketch`, independently audited). More strongly, for every finite decimal word `w` there is a binary Cantor family `E_w` of exact Hausdorff dimension `log 2/log 10` such that every `y in E_w` avoids `w` and admits integer lifts with `0<pi*L_n-floor(10^n*y)<1` at every level; its transcendental finite-irrationality-exponent subfamily has the same dimension. Hence every well-defined single-time `pi`-periodic sign packet uniform on the complete residual arc is counterfeit-compatible, including the oriented tangent cone. A causal prefix-local lift law with at least three allowed successor defects at every root-reachable admissible history likewise admits, for every nonempty `w`, an exact-dimension `log 2/log 10` word-avoiding family; with at least two successors it admits, for every constant word `delta^ell`, `ell>=2`, a family of dimension `((ell-1)/ell)*(log 2/log 10)`. Both retain full dimension after restricting to transcendental finite-exponent members. More sharply, if every node of a nonempty prefix-closed target-safe decimal tree retains at least two already-safe children, it contains an `s=log 2/log 10` Ahlfors-regular binary subset; BFKRW strong `C1` incompressibility leaves a full-`s`-dimensional subfamily of transcendental badly approximable, hence exact-`mu=2`, counterfeits (`proof sketch`; [BFKRW](https://arxiv.org/abs/1106.1621) input `literature-checked`, independently audited). For every nonempty `w`, the compact avoidance coding image `X_w` is also a trigonometric U-set: it lies inside an aligned base-`10^|w|` deleted-digit self-similar set to which [Varju--Yu](https://arxiv.org/abs/2004.09358) applies. Consequently `X_w` supports no nonzero pseudofunction or Rajchman measure; a decimal orbit closure supports a nonzero Rajchman probability measure exactly when the underlying number is already disjunctive (`proof sketch`; Varju--Yu input `literature-checked`, independently audited). | All nine literal inverse child characters therefore survive every `L1` scalar endpoint potential; scalar summation by parts cannot eliminate the joint remainder. The self-centralizer rank bound excludes only exact linear `o(q)`-rank ray reconstructions: after-evaluation or cross-time cancellation, nonlinear products or observables, vector/general semiconjugacies, inverse Puiseux branches and `Theta(q)`-bandwidth remain outside its scope. Orbit-supported Fourier decay is likewise V1 in spectral clothing, not a weaker bridge; the special orbit-closure equivalence does not assert that every arbitrary non-U set supports a Rajchman measure. The `1/100` identity telescopes only an auxiliary quadratic observable and leaves coefficient `99/2` under the actual unweighted sum. Fixed cycles block orbit-universal scalar Bellman certificates. More sharply, on an adverse fixed cycle with compensated increment `-gamma`, every additive consecutive-block extended-state certificate with cumulative defect `o(N)` forces its correction to fall as `-gamma*N+o(N)`; bounded-below or sublinear fixed-potential finite-/compact-state schemes therefore fail. If uniform horizon and correction-oscillation bounds `H,M` are fixed for the whole claimed exact-`mu=2` class before the control is chosen, block-coded Thue--Morse target avoiders give the same contradiction (`proof sketch`; Thue--Morse irrationality-exponent input `literature-checked`; independently audited). This does not cover linearly escaping state with an actual-pi barrier, pointwise-only bounds, unbounded horizons, existential favorable blocks, or global/nonadditive stopping. Predecessor/suffix recoding supplies no independent pi sign, and exact scale factorization has opposite-sign branch multipliers. Transcendence, finite or exact irrationality exponent, bad approximability, an auxiliary `pi`-lift corridor and even infinitely many uniform nonlinear periodic order signs still do not locate a prescribed target while two safe children remain. Residual nonuniformity, target/history dependence and finite-window multistate coupling remain counterfeit-compatible while they retain robust branching. A reachable `<=1`-safe-child event is therefore necessary for any such prefix-tree route, but is not sufficient. The pruning theorem does not cover extinction, genuinely anticipatory/global constraints, additional π-specific global hypotheses, or nonlocal spectral laws not verifiable from a proposed successor. Imposing the actual lift defect `L_(n+1)-10L_n=0` with `L_1=10` forces `L_n=10^n` and recovers `floor(10^n*pi)`, so the Euler sine-zero repair is an exact prefix detector rather than new order. | A named independent actual-pi relation, parameterized by the target in advance, with correct lower orientation and a `<=1`-successor bottleneck or extinction on every target-avoiding continuation; it must fail on the exact-`mu=2` safe-tree counterfamily without encoding exact winding/prefix. Genuinely global/non-prefix-local laws remain open; in the T189 setting the relation must still sign the complete literal target expression. |
| Pair/DC1, Laurent nonvanishing | The paired carrier is a formally nonzero Laurent polynomial, and DC1 is sharp. Actual-π experiments show Pair/DC1 failure at `(1000,689)` and, on the legal edge to `(10000,1334)`, unique FMR at `d=5` while every parity-balanced convex mask is negative. At that hard node, independently checked LP optima are negative after deleting any one of the five real character blocks (`experiment`). Exact anti-periodicity collapses sector 5 to an odd-frequency correlation on the `5π` orbit (`proof sketch`). | Formal nonzero gives no evaluated sign; uniform Pair/DC1 and block-deleting convex-mask transport are false over the uncoupled completion space. The LP does not exclude an actual-orbit admissibility relation, and the odd-frequency collapse still lacks a sign. | A path-constructing actual-π cross-sector admissibility theorem retaining the complete relative phases and same-child inherited alignment. |
| Separate marginals and coherent single rays | Exact ten-vectors with identical (D)- and (G)-marginals can have zero or five FMR witnesses solely by permutation; a single coherent selector ray covers only factors of one word. | Separate witnesses lose the joint digit, and an infinite ray alone does not imply V1. | Joint actual-π control of (min(D_d,D_d+G_d)), followed by viable branching or proof that the selector word is disjunctive. |
| `Machin 3/7 bracket residues for CW0 (constant words)` | The exact rational endpoints `L_m<pi<U_m` from `pi=8*arctan(1/3)+4*arctan(1/7)` and the bracket-containment equivalence `MC0 ↔ CW0` are `machine-checked`; the strongest theorem is `Theory.PiDigits.T198MachinBracketPack.machinMC0_iff_piCW0`. The later integer-normalized presentation with `D_m=lcm(den L_m, den U_m)`, `R_{m,n}=10^n D_m L_m mod D_m`, `Delta_m=D_m(U_m-L_m)`, and `forall k exists m,n: 10^k R_{m,n}+10^(n+k) Delta_m < D_m` remains `proof sketch`. Both reduced denominators are odd with exact 5-adic valuation `floor(log_5(4m+3))` (`proof sketch`; `experiment`, verified numerically for `m<=400` in `t196_machin37_bracket_valuation.py`), so after `O(log m)` decimal shifts the lower-endpoint residue evolves invertibly modulo a number coprime to 10 while the bracket stays thinner than half a `0^k` cylinder for a further `Theta(m)` shifts (sufficient condition SOH). | Inferring from a linearly long invertible orbit `10^t c_m mod e_m` that some iterate lies in `[0, e_m/(2*10^k))`. Pigeonhole yields close pairs, not endpoint hits; `10^t mod 9 = 1` is the minimal counterexample. Same unknown-integer-lift obstruction as the BBP residue route. | A one-sided theorem using the exact Machin numerator structure that gives `D_m-10^k R_{m,n}-10^(n+k) Delta_m>0` for every fixed `k` on unboundedly many scales and fails for deleted-digit endpoint avoiders. |
| `Erdős carry-killing on integer-coefficient series (Lambert-series precedent)` | Exact criterion (`proof sketch`): for `x=sum a_m b^-m` with integer `a_m`, if `b^L` divides the block aggregate `sum_(r=1)^L a_(n+r) b^(L-r)` and the tail `sum_(r>L) a_(n+r) b^-r` lies in `[0,b^-h)`, then the `h` digits after position `n` are zero; Erdős 1948 realizes this for `E_t=sum d(m)t^-m` by a CRT family plus tail averaging, and Liouville-weighted and squarefree-indicator Lambert series give further examples. Pi-specific: Ramanujan's `4/pi=sum (6n+1)C(2n,n)^3 256^-n` inverts to `pi/4=sum r_n 256^-n` with integer `r_n` and exact law `v_2(r_n)=3 s_2(n)` (`experiment` for `n<=600` in `t197_ramanujan_inverse_valuation.py`, `proof sketch` in general), hence a decimal series `pi=4+sum g_m 10^-m` with `g_(8n)=4 r_n 5^(8n)`, `g_m=0` otherwise, `v_10(g_(8n))=2+3 s_2(n)`. | A usable tail estimate first requires an independent bound `|rho_n|<=C*Lambda^n` with `Lambda<256`; the asymptotic `c_n~64^n/sqrt(n)` for the original Ramanujan coefficients does not imply such a bound for the reciprocal coefficients. Conditional on that estimate, direct absolute tail control requires `L>[N*log(5^8*Lambda)+h*log(10^8)+O(1)]/log(256/Lambda)`; at the benchmark `Lambda=64` this is `L>12.2877...N+13.2877...h+O(1)`, not `3N+O(log N)`. The signed reciprocal coefficients remove automatic positive-tail control but do not prove that selected blocks or cancellations can never satisfy P3. BBP coefficients are rational with moving non-base-smooth denominators; long division restores integrality but destroys the structure. | An independently defined exact series `pi/q=Z+sum a_m B^-m`, `B=10^s`, integer `a_m`, with an unbounded family of blocks satisfying block integrality `B^L | sum_(r=1)^L a_(n+r) B^(L-r)` together with a positive tail `0<=sum_(r>L) a_(n+r)B^-r<B^-h`, `h->infinity`; a naive "interval of coefficientwise divisibility" is insufficient (a compensating coefficient after the interval defeats it). |

The generic-lacunary row's exact bounded-offset boundary is sharper than
marginal recurrence.  For fixed integer offset `c`, multiplication by the
complementary factor gives
`e(h*b_c*a_c*10^n*x)=e(h*10^(n+|c|)*x)`; hence the fixed-offset orbit
`a_c*10^n*x` is uniformly distributed iff the decimal orbit is.  Jointly,
`x |-> (2^c*x,5^d*x)` is a conjugacy onto
`{(u,v):5^d*u=2^c*v}`, with inverse `a*u+b*v` whenever
`a*2^c+b*5^d=1`.  Thus full bounded-offset joint control already contains
the resonant diagonal characters; separate marginals do not (`proof sketch`,
independently audited).  This does not exclude a partial resonant-character
estimate as an intermediate theorem, but that estimate must already carry
literal diagonal information.

After exact primitive-ray compression, the complete target-weighted PBFS
observable `F_(q,A)` is annihilated by the decimal Perron operator because
every surviving frequency is indivisible by ten.  Thus it is a bounded
reverse-martingale-difference observable, all positive-lag correlations vanish,
and its exact variance is
`(1/2)*sum_u |C_(q,A)(u)|^2>0`; the singleton top ray `2q-1` rules out
degeneracy.  The Dedecker--Gouëzel--Merlevède ASIP therefore gives the
two-sided signed LIL and infinitely many PBFS threshold crossings,
simultaneously for all decimal scales and targets, for Lebesgue-almost every
seed (`proof sketch`; [arXiv:1108.5292](https://arxiv.org/abs/1108.5292)
`literature-checked`, independently audited).  This retains the full literal
coefficient profile but gives no information at `x=pi`; periodic and
exact-`mu=2` word-avoiding exceptional seeds remain.  A pointwise vector
Strassen law for `pi` is not a smaller rung: in its standard form it implies
base-ten normality.  More elementarily, every continuous real
`f in ker(L_10)` admits a coherent backward orbit with `f(10^n*x)<=0` at every
time (`proof sketch`, independently audited).  Thus branch averaging cannot
force positive increments on every orbit; this neither prevents the partial
sums from crossing the sufficient `-122091/200000` threshold nor selects the
actual pi branch.  Reopen this metric route only with a named deterministic
π-specific half-space or inverse-branch theorem for the exact literal
projection, false on those controls—not with another almost-everywhere limit
law, discrepancy estimate or unsigned covariance.

A single-cylinder localization theorem closes the corresponding positive-mass
escape (`proof sketch`, independently audited, 2026-09-01).  Let a pruned
decimal tree have between `kappa^L` and `B^L` descendants at every node and
horizon, let `L_n=o(n)`, and give those descendants nonnegative weights whose
total mass is uniformly comparable to their number.  For every fixed
Lipschitz `h`, the packet over one length-`n` cylinder satisfies
`S_(u,L_n)=M_(u,L_n)*h(x_u)+O(M_(u,L_n)*10^(-n))`.  Consequently a uniform
lower bound `|S_(u,L_n)|>=C*kappa^(L_n)*q_n^(-1+eta)`,
`q_n=10^(n+L_n)`, for every safe node and all large `n` holds for some
`C,eta>0` iff the infinite path set avoids `h^(-1)(0)`.  For
`h(x)=1+e^(i*x)` this is exactly occurrence of the prescribed word, not an
intermediate bridge.  Odd-frequency amplification does not repair this
mass-scale argument: `|k_n|*10^(-n)` simultaneously controls descendant
resolution and loss of the small prefix upper bound.  Transcendental
exact-`mu=2` word avoiders lie in every word-safe cylinder (`proof sketch`;
Thue--Morse inputs `literature-checked`).  This does not cover signed or
adaptive weights, scale-dependent high-frequency kernels, nonlinear packets,
or genuine cross-cylinder/cross-scale coupling.  Reopen only when a proposed
construction explicitly breaks one of these hypotheses and carries an
independent one-sided actual-pi sign through the resulting coupling.

The complete elliptic CM separator in the CM row uses Bonk's
[quasiperiod relation](https://arxiv.org/abs/2212.07012) and Maier's
[degree-ten modular equations](https://arxiv.org/abs/math/0611041)
(`literature-checked`, 2026-08-31).
At the parameter level there is an exact narrower boundary: for every fixed
`gamma in GL_2^+(Q)`, both coordinates of `gamma(i*10^n)` are rational, so
its nome has a root-of-unity angle (of possibly growing order); if the lower
left entry is nonzero that angle is `O(10^(-2n))` from the fixed cusp angle.
Finite fixed rational-isogeny chains and finite nome monomials therefore do
not natively produce the horizontal character `exp(2*pi^2*i*10^m)`
(`proof sketch`, independently audited).  This does not cover nonlinear
modular-function branches, eta/Siegel values, moving correspondences or open
coefficients.

Varying Siegel characteristics evades only the common-cusp-order cancellation.
For standard `g_a=g_(a/q,1/q)`, `rho=exp(-2*pi*T/q)` and `1<=r<q`, the
characteristic-label transform satisfies
`|S_(q,r)(T)+pi*T/(2q*sin(pi*r/q)^2)| <=
2q*rho/((1-rho)*(1-rho^q))` (`proof sketch`, independently audited; the
[product formula](https://arxiv.org/abs/1007.2317) is `literature-checked`,
2026-08-31).  This is a generally complex disk estimate; a real sign requires
the main term to exceed the error.  Its character indexes an auxiliary Siegel
family, not a decimal target, and the vertical nome `exp(-2*pi*10^n)` has no
proved coupling to the horizontal phase `exp(2*pi^2*i*10^n)`.  The statement
therefore remains true alongside every word-avoiding replacement and supplies
no actual-pi target sign.  Reopen only with a non-gauge identity natively
containing `e(h*10^n*pi)`, independently ordered in the distinguished real
embedding and expanding directly to PBFS or literal FMR.

The remaining one-coordinate incomplete-period opening also has an exact
boundary (`proof sketch`; standard real-elliptic and Legendre inputs
`literature-checked`, independently audited).  On an oriented real elliptic
identity circle with normalized Abel coordinate `a`, multiplication by ten
has topological degree ten and satisfies `a([10]P)={10*a(P)}`.  Any child rule
formed by the half-open ordered thresholds
`d/10<=a(P)<(d+1)/10` therefore selects exactly `floor(10*a(P))`; iteration is
the ordinary canonical decimal itinerary of that one scalar coordinate.
Matched strictly increasing reparameterizations and common positive
complete-period or Legendre normalizations do not change the selector, so a
target-filtered extinction occurs exactly when the already selected itinerary
completes the target.  This closes one-coordinate ordered real-isogeny, AGM
and abelian-holonomy selectors only.  It does not close arithmetic constraints
on independently specified algebraic non-torsion points, moving
`A,d`-dependent points, nonmonotone or nonseparable period couplings, two
independent incomplete periods, or nonabelian holonomy.  Reopen only with an
independently signed multicoordinate amplitude whose elimination does not first
reconstruct `{10^n*pi}`, which fails on a suitable word avoider and sends the
same child directly to PBFS or literal FMR.

Finite linear incomplete-Legendre traces on the conductor chain give a sharper
affine-gauge boundary (`proof sketch`; standard Jacobi/Legendre identities
`literature-checked`, independently audited).  For
`K_n'/K_n=10^n`, the incomplete determinant splits exactly as

```text
L_n(u)=pi*u/(2*K_n)+K_n'*Z_n(u).
```

Hence every finite linear packet is `pi*a+B`, with
`a=sum_j c_j*u_j/(2*K_(n_j))` and a Jacobi-zeta remainder `B`.  Affine-balanced
packets (`a=0`) erase the distinguished Legendre `pi` term exactly.  In a
complete nonzero-character trace over `u=2*K_n*(x+d/Q)`, its surviving
contribution is the frequency-labelled, orbit-independent baseline
`-pi/(1-omega_Q^(-r))` (up to an inserted target character), rather than a
target detector.  Real-oval concavity and subadditivity also cancel the affine
term and are universal Jacobi geometry.  This closes Legendre-affine
orientation in affine-balanced finite linear torsion/chamber-independent
traces.  It does not show that every affine-unbalanced trace is useless, nor
exclude independently signed zeta remainders, algebraic non-torsion sections,
nonlinear products or multicoordinate cross-fiber relations.  Reopen only with
a concrete independently algebraic non-torsion or cross-fiber observable whose
affine-gauge quotient retains a native target character, has a proved
pi-specific real sign before inserting the decimal endpoint, fails the
word-avoiding controls and maps directly to PBFS or FMR.

The CM row also covers canonical Chudnovsky binary splitting (`proof sketch`,
independently audited).  Its adjacent determinant is exactly
`Delta_N=ell_N*P_(N+1)*Q_N`, has parity-fixed sign, and in the standard
unreduced normalization vanishes modulo every fixed `10^k` eventually;
dividing out `Q_N` removes the decimal center.  The alternating partial sums
give genuine nested scalar brackets, but their first center-sensitive carry is
exactly an integer-boundary crossing, and the corrected quadratic norm has
sign `sign(10^m*pi_N-b)`.  The fully quantified carry-cylinder statement is
equivalent to V1 (the reverse implication uses arbitrarily late occurrences
of zero-padded target words), so it is not an intermediate rung.  This closes
only the natural determinant/remainder/bracket-carry readouts: recentering
preserves their increments and widths but not the absolute canonical `P,Q,T`
packet or its CM initial condition.  Reopen with a floor- and lift-free,
moving-modulus function of that canonical packet whose distinguished-real
sign fails on finite-exponent word avoiders and directly forces a prescribed
cylinder or literal FMR.

The positive-period row also covers the normalized Zeilberger--Zudilin
integer forms `I_n*=a_n*+b_n*pi`.  Their proved normalization implies
`b_n*>0` and `b_n*=lcm(1,...,4n)*u_n` with `u_n>0`, hence
`10^k_n | b_n*` for
`k_n=floor(log_5(4n))->infinity`.  More generally, if
`0<C+D*pi<1`, `D=tau*m*10^k`, and `r` is the least residue of `-C`
modulo `m`, then exactly
`{tau*10^k*pi}=(r+C+D*pi)/m` and `r=floor(m*{tau*10^k*pi})`.
The full conjugate-root asymptotic has power `n^(-1/2)` and forces both signs
of `I_n*` in every sufficiently late 70-index window.  Opposite signs give a
positive integer cross-determinant; in particular, for the sign-corrected
moving residue `R_n` and modulus `M_n=b_n*/10^k_n`,
`M_n/gcd(R_n,M_n) >= exp((alpha-o(1))*n)` with
`alpha=1.90291648559998...`.  Thus these forms do select both inverse branches
syndetically and exclude collapse to bounded reduced denominators.  However,
at any common decimal scale every decoded form returns exactly the unknown
block `W_k=floor(q*{10^k*pi})` or its nine's complement `q-1-W_k`; sign,
divisibility, primitivity and determinant width do not order either atom.
More strongly, the simultaneous rational shear
`(U_j,pi) -> (U_j-c*V_j,pi+c)` preserves the small forms, their signs and
asymptotics, the recurrence, denominators, saddles and pairwise determinants.
For `c=1/3`, integrality holds eventually, both constants remain in `(3,4)`,
and every sign-corrected decoded phase shifts by `tau_j/3`.  On a finite
formal window, the polynomial invariants of this shear are generated by the
`V_j` and determinants `U_i*V_j-U_j*V_i` ([Nowicki--Weitzenbock invariant
theorem](https://arxiv.org/abs/0909.3602) `literature-checked`; application
`proof sketch`, independently audited).  This separator covers only
shear-invariant polynomial closed data, not the canonical open endpoint
numerator itself.
The ten canonical `n=0` fixed-endpoint pole-coordinate cross-ratios satisfy
`U_0=i` and `U_(r+5)=U_r^(-1)`.  Four separating primes above `401` prove that
`U_1,...,U_4` are multiplicatively independent modulo torsion.  Baker's
inhomogeneous logarithm theorem therefore forces every algebraically weighted
fixed-branch combination of these ten logarithms that returns to
`Qbar + pi*i*Qbar` to pair its coefficients under `r <-> r+5` (`proof
sketch`; [Baker formulation](https://arxiv.org/abs/2212.00358) and the
[untwisted ZZ normalization](https://arxiv.org/abs/1912.06345)
`literature-checked`; independently audited).  Thus odd child characters
cannot return to the two-period span, while even pairing erases the reflected
digit distinction.  This closes logarithmic cancellation and torsion products
only in this explicit ten-member simple-log span.  New cross-ratios, a retained
enlarged logarithm space, higher or nonlogarithmic endpoint terms, moving
contours and genuine digit-coupled open packets remain outside scope; moreover
the formal twist's Laurent degree modulo ten is not the actual T179
predecessor digit.
For the untwisted ZZ rational integrand, every finite pole-free subcontour with
algebraic split points and every algebraic AZ boundary term Hermite-reduces to
algebraic endpoint data, logarithms of algebraic cross-ratios, and closed
`a+b*pi` or winding terms.  At the canonical midpoint this is exactly
`U_n^+=I_n*/2+i(rational-b_n*log(9/8))`, with the displayed logarithmic term
strictly negative.  Thus linearly extracted reflection-odd open signs are
independent of the decimal seed, while the explicit `pi` dependence lies in
the reflection-even closed part (`proof sketch`; independently audited).  This
closes midpoint, algebraic-split, homotopic and algebraic AZ-forcing attempts
only; it does not close new cross-ratios, nonlinear open--residue coupling,
actual-pi- or target-dependent contours, or literal digit-coupled packets.
The first fatal line is now the missing sign of the target comparators
`q*R_n-A_sigma*M_n` and `(A_sigma+1)*M_n-q*R_n` on an independently selected
unbounded set (`proof sketch`, independently audited;
[source and recurrence](https://arxiv.org/abs/1912.06345)
`literature-checked`, 2026-08-31).  Reopen only with an independently proved
non-reflection-invariant and shear-breaking open-endpoint contour or arithmetic
theorem coupling the canonical numerator to that moving residue cell.  More
sign asymptotics, divisibility, gcd control, determinant positivity,
shear-invariant recurrence packaging, or coefficient indices per scale are
insufficient.

A further audit closes the natural positive-moment deformation of the
published ZZ contour (`proof sketch`, independently algebra-checked; the
[integrand and arithmetic normalization](https://arxiv.org/abs/1912.06345)
are `literature-checked`, 2026-09-01).  With
`B=25-x^2` and `W=B^3/(x^2*(x^4+6*x^2+25)^2)`, its correct vertical-contour
density is `10*Re(1/(B*(-W)^n))`, not the reciprocal expression.  Its phase
crosses both sign chambers for every `n>=1`; polynomial-square localization
therefore gives a negative direction for the original moment functional at
every level.  More rigidly, a rational multiplier that preserves the even
`x -> -x` pi-extraction symmetry and is real on `Re x=-1` obeys, with
coefficient conjugation retained, two reflection identities and hence is
period-four and constant.  A genuinely positive finite moment reweighting
cannot preserve even the literal first two frequency coefficients except as
point evaluation, while Hermitian sector squares carry relative characters
`r-s`, not T179's absolute child character `r`.  Loading the exact T179
generating polynomial into the contour instead inserts the unknown orbit
phases externally and abandons the fixed-number-field `Z+Z*pi` mechanism.

The literal boundary profile has an exact positive-radial-cone obstruction
(`proof sketch`, independently audited; coefficient identities machine-checked
in T130/T142).  Every positive Hausdorff profile
`m_h=integral_[0,1] r^h dnu(r)` satisfies `m_2<=m_1` and cannot have a positive
terminal moment followed by zero.  In contrast, for every integer `Q>=10`,

```text
alpha_(Q,2)-alpha_(Q,1) > 3/(20*Q^2),
alpha_(Q,2*Q-1)=1/(2*Q^2),
alpha_(Q,h)=0 for h>=2*Q.
```

Thus no positive scalar radial Poisson/Abel/Laplace mixture, nor any positive
Lerch/Stieltjes or Beta--Gamma weight that is a Hausdorff moment sequence, can
realize even the first two literal coefficients.  Completing the target
character through frequency `2*Q` restores a positive finite Abel kernel only
by restoring the missing endpoint; deleting it gives
`K_(2*Q-1)(1,theta_(Q,A))=-1`.  This excludes only the positive radial cone
and endpoint completion, not signed, nonradial, non-Hermitian, matrix-valued,
frequency-dependent, nonlinear or pi-dependent kernels.

This does not exclude a noneven equal-residue deformation with exact
cancellation of its extra logarithmic periods, an isolated target-specific
signed integral, or a new non-Hermitian numerator identity.  Reopen only when
such a native functional has an independently proved distinguished-real sign
and expands to the literal same-child remainder without externally loading
the orbit phase.

The same row also covers a `q`-adapted rational Machin--Hausdorff carrier
(`proof sketch`, independently audited).  For every `q=10^k`, explicit
rational truncations `M_n` give
`delta_n=10^n*(pi-M_n)=integral y^n d nu_q(y)` with positive density,
support `rho_q=1-O(1/q)<1`, and
`1/(60000q^2)<delta_n<1/(3000q)` for `n<=q`.  Hence every literal primitive
phase in T139's compressed PBFS is a counterclockwise rotation by less than
`pi/750`, with an exact target-preserving chord decomposition.  This removes
the fixed-carrier size obstruction but not scalar rigidity: the rational
kicks satisfy `d_n=10delta_n-delta_(n+1)>0` and recover `delta` as their future
decimal coboundary.  Moment positivity controls chord length, while the
complete chord retains an unoriented target sine.  The all-depth support law
uniquely characterizes `pi` essentially because its exponential error already
forces the limit; every finite-horizon cone consequence remains
counterfeit-stable.  The corresponding moment dual takes both signs when the
center varies continuously, but this alone does not rule out its values on
the discrete target grid.  Reopen only with an independent uniform arithmetic
estimate for the rational carrier residues that signs the complete
target-weighted sine sum for preassigned targets on unbounded scales and fails
finite-irrationality-exponent word avoiders; rewriting PBFS as the exact
moment integral is not such an estimate.

The denominator-sensitive G-function route is also quantitatively unavailable
at the actual decimal specialization (`literature-checked`, Fischler--Rivoal
2018; independently audited, 2026-09-01).  For
`F_M(z)=16*atan(2z)-4*atan(10z/239)`, `F_M(1/10)=pi`, a valid coefficient
denominator bound is `d_N<=956^N`, the Taylor radius is `1/2`, and the minimal
inhomogeneous differential order is one.  Fischler--Rivoal's theorem has
`c_2=9` here and always `c_1>=4`, so its required
`b>(c_1*|a|)^c_2` already demands `10>4^9` at `(a,b)=(1,10)`; honest constants
are far worse.  The large-depth variant cannot repair this because keeping the
value `pi` forces the numerator `a=10^(s-1)` to grow with `s`.  Moreover even a
hypothetical `v_10(pi)=0` or bounded-power conclusion would be target-blind:
two-digit Thue--Morse decimals can avoid a prescribed word, have exact
irrationality exponent two, satisfy `v_10=0`, and have bounded block powers.
Reopen only with a numerator-language-sensitive G-function theorem excluding
an entire prescribed-word survivor language, not another restricted-denominator
or repetition estimate.

The positive-period row also covers the directed polygon tower
`alpha_R=10^R*sin(pi/10^R)`.  It is an algebraic integer of degree
`4*10^(R-1)`, generates the maximal real subfield of the corresponding
base-ten cyclotomic field, and is its unique conjugate in `(3,4)`.  The
published bound `mu(pi)<36/5` implies that `alpha_(4N)` and `pi` eventually
share the same unknown `10^(-N)` cell.  For a fixed-word survivor product at
denominator `D=10^N`, however, avoidance forces the full norm to satisfy
`|Norm F_(N,w)(alpha_(4N))| > (1/4)*D^(-62/5)*(4*D^2)^(d-1)`, where
`d=4*10^(4N-1)`: one polynomially small distinguished factor is overwhelmed
by the large factors at every other embedding.  The relative degree-ten norm
already contains eight unavoidable large branches; uniform local division by
`D` is unavailable, while cross-ratio normalization is exactly the unknown
decimal-chamber comparator.  Contraction itself is nevertheless explicit:
the norm-coherent totally positive unit
`u_R=(2-zeta_R-zeta_R^(-1))^(-1)` has a unique largest principal value and
maximum secondary ratio
`(sin(pi/(2*10^R))/sin(3*pi/(2*10^R)))^2<1/8`.  This does not turn the small
survivor into a signed integer.  If a nonzero totally real algebraic integer
`y` of degree `d` has secondary `L1` mass at most `eta` times its principal
magnitude `A`, the product formula forces
`A>=|Norm y|^(1/d)*(d-1)^((d-1)/d)*eta^(-(d-1)/d)`.  Thus absolute one-place
dominance cannot produce a contradiction `0<|Tr y|<1`; reflection-even affine
traces erase `alpha_R`, while the anti-invariant case leaves the unordered
integer comparator `D*B-M*A` (`proof sketch`, independently audited; external
irrationality-measure input `literature-checked`, 2026-08-31).  This closes
local safe-cell products followed by norms or resultants, their naive relative
norm variants, affine or fixed-rank identification of the ten Galois branches
with decimal children, reflection-even affine traces, and localization followed
by a small-nonzero-integer argument.  It does not exclude exact signed
cancellation among secondary places, nonlinear semiconjugacies, or a genuinely
global nonmultiplicative automaton--cyclotomic trace.  Reopen only with an
independent pre-localization sign or cancellation theorem for the complete
target-dependent anti-invariant trace, false on a suitable word avoider; the
trace of a polynomial deliberately encoding the finite hit is only another
consumer.

The Euler/Gamma row also covers the complete quadratic-character
half-Gamma bridge (`proof sketch`, independently algebra-checked; the
[Morita/Diamond domains and formulas](https://arxiv.org/abs/1702.04200) and
[Gross--Koblitz identity](https://doi.org/10.2307/1971226) are
`literature-checked`, 2026-09-01).  At `p=5`, after fixing
`varpi_5^4=-5` and the compatible fifth-root branch,
`Gamma_5(1/2)=-i_5` is torsion; at `p=2`, Morita's half-value is outside its
domain and Diamond's `LogGamma_D,2(1/2)=0`.  For `k>=1`, `M=2*10^k`, the
normalized complete chirp satisfies
`S_M(2b)=(1+i)*e(-b^2/M)` and vanishes for odd integral coefficients.  The
complex branch `1+i` comes from the chosen complex additive character; the
Gross--Koblitz formula only identifies its chosen 5-adic realization, and the
branch cancels from adjacent ratios.  For arbitrary real `t`, exactly

`S_M(t+2)=e(-(t+1)/M)*(S_M(t)+(e(t)-1)/sqrt(M))`.

Thus `t=M*10^n*pi` introduces the unresolved deeper decimal phase
`e(2*10^(n+k)*pi)-1`; replacing `t` by `2b` supplies the unknown lower cell
residue `b=floor(10^k*{10^n*pi})`.  Gross--Koblitz depth over `F_(5^k)` does
not repair this: its fifth-root trace character is not the ramified conductor
character on `Z/5^k Z`, and the 2-power factor is likewise a ramified ring
Gauss sum.  This closes only complete integer-character CRT/Gross--Koblitz
evaluation as the source of the moving carry.  It does not close
irrational-parameter incomplete chirps, higher characters, or a new
Archimedean--ramified coupling.  Reopen only with an independently proved
one-sided theorem for the irrational-parameter object which avoids inserting
the nearest/lower residue, fails on the exact-`mu=2` Thue--Morse word avoider,
and directly signs a prescribed cylinder or literal FMR.

Integral/rational-frequency regular-language auxiliaries have a further exact
arithmetic-transfer obstruction (`proof sketch`, independently audited;
Nesterenko--Waldschmidt and Lindemann--Weierstrass inputs
`literature-checked`, 2026-09-01).  For nonzero
`R in Z[X,Y,Y^(-1)]`,
`ord_(z=pi) R(z,e^(i*z)) = ord_(Y=-1) R`: every exact finite-order
integral-frequency zero is the visible Euler factor `e^(i*z)+1`.  Rational
frequencies specialize algebraically at pi, but a decimal inverse branch sends
`r` to `r/10` and multiplies the natural mode by
`exp(i*r*(3*10^N+p-3)/10^N)`, which is transcendental for `r != 0`;
distinct-prefix algebraic linear combinations remain transcendental, and no
finite nonzero rational-frequency set is stable under division by ten.  This
closes fixed finite-state linear algebraic-coefficient transfer in the natural
rational-frequency basis, not nonlinear cancellation, gauge changes,
growing/depth-dependent modes, or mixed transcendental coefficient fields.
Reopen only with both a concrete nonlinear/global automaton auxiliary and a
new applicable mixed pi--exponential lower-bound theorem.

Primitive cyclotomic absolute-log packets have a separate conductor-descent
separator (`proof sketch`, independently algebra-checked, 2026-09-01).  For
every `q=2^a*5^b`, `a,b>=1`, the primitive decimal-character trace descends
exactly to conductor ten:
`P_(q,r)=2*log(phi)*(cos(3*pi*r/5)-cos(pi*r/5))`, where
`phi=(1+sqrt(5))/2`.  It is therefore independent
of `a,b`, and its parity coordinate `r=5` vanishes.  In the gcd-shell
decomposition, constant-on-shell parity traces vanish for every mixed 2--5
quotient; the only nonzero terminal pure-prime contributions are in the span
of `log 2,log 5`.  Hence these unweighted or unit-orbit-constant real
absolute-log packets detect prime support and terminal valuations, not the
balanced decimal diagonal or the literal T179 predecessor/suffix correlation.
This does not cover nonconstant shell weights, polynomially weighted Barnes
packets, complex logarithm/Gauss--Jacobi phases, nonlinear cross-shell
coupling, or an independent orbit-index map.  Reopen only with a concretely
defined such observable carrying a proved directed real order and an exact or
one-sided T179 coupling preserving predecessor character, target centre and
suffix phase.

The `BBP, p-adic fibres, residues, rational shadows` row also covers finite
nonlinear rational phase observables.  The exact BBP recurrence gives, at a
fixed finite horizon, `z_(n+j)=omega_(n,j)*z_n^(10^j)` with root-of-unity
`omega_(n,j)`.  Any real rational observable in these phases, with
reflection-fixed coefficients and both reflected evaluations defined, has a
unique meromorphic decomposition
`Phi(t)=A(cos t)+sin(t)*H(cos t)` and hence
`Phi(t)-Phi(-t)=2*sin(t)*H(cos t)` (`proof sketch`, independently audited).
At `t=2*pi*r_n/D_n`, a coefficient-level sign for `H` therefore factors out
rather than supplies the unresolved residue half-order.  This closes only
reflection-even norms/full resultants and determinant or total-positivity
templates that sign the cofactor alone.  It does not exclude horizons growing
with `n`, nonuniform arithmetic information in `H`, a pi-specific theorem
signing the complete skew, or infinite/nonlocal/canonical-lift mechanisms.
Reopen with an independently specified unbounded set and a named actual-pi
theorem that signs the complete skew and supplies endpoint proximity on that
same set, or directly proves literal same-child FMR.

At a single scale the obvious gcd channel is numerator-blind as well.  For the
reduced BBP partial `B_n=P_n/D_n`, `m_n=10^n-16`, and
`r_n=m_n*P_n mod D_n`, one has exactly
`gcd(r_n,D_n)=gcd(m_n,D_n)`; hence the phase order is
`D_n/gcd(m_n,D_n)` and is unchanged by residue reflection (`proof sketch`,
independently audited).  This closes single-time gcd, valuations inside the
modulus, and cyclotomic-order arguments, but not numerator-sensitive
cross-level relations or principal-real inequalities.

The canonical modular inverse gives the sharpest remaining numerator-sensitive
reduction.  If `s_n=P_n^-1 mod D_n` lies in `[1,D_n)` and
`P_n/D_n=[a_0;...;a_L]` is canonical, then
`sign(2*s_n-D_n)=(-1)^L`.  Consequently, for
`Q_n=(2*r_n-D_n)*(2*s_n-D_n)`,
`sign(2*r_n-D_n)=sign((-1)^L*Q_n)` (`proof sketch`, independently audited).
But `Q_n≡4*(10^n-16) mod D_n`, and its real sign contains an uncontrolled
integer lift.  Modular-hyperbola and inverse-distribution theorems range over
many units or averaged moduli, not this selected BBP numerator point
(`literature-checked`, 2026-08-30).  Reopen only with a theorem signing this
canonical point on an explicit unbounded set and then strengthening half-order
to endpoint proximity or literal same-child FMR.

The delayed reduced BBP carrier makes the complementary-coordinate obstruction
fully explicit (`proof sketch`, independently audited, 2026-09-01).  Write it
as `U/(M*X)`, with `M=2^J`, `X` odd, `R=U mod (M*X)`, and CRT coordinates
`v=[R*X^(-1)]_M`, `w=[R*M^(-1)]_X`.  Its rational Archimedean `M`-cell is
`[v+floor(M*w/X)]_M`; after the positive BBP tail `epsilon`, the actual cell is
`[v+floor(M*(w/X+epsilon))]_M`.  Thus the top bit of the dyadic primary
coordinate is not half-order: the odd coordinate can change every bit (already
`M=8,X=3,U=5` has `v=7` but phase `5/24<1/2`).  The checked delayed-tail bound
is only `M*epsilon<2*5^(n-1)`, so it proves neither zero carry nor clearance
from `0` or `1/2`.  Retaining all carries makes the actual top bit exactly
`floor(2*{10^n*pi})=floor(a_n/5)`, the original unknown predecessor-digit bit.
Reopen only with a noncircular block theorem jointly controlling `U`, the odd
CRT coordinate and tail crossings, then correlating the resulting signs with
all five complete target-rotated odd T179 sectors strongly enough for literal
same-child T189.

There is one exact nonlinear boundary-reset separator (`proof sketch`,
independently audited).  Let `a_(n+1)` be the first omitted positive BBP term,
`x_n=r_n/D_n` and `delta_n=(10^n-16)*a_(n+1)`.  For every `n>=3`,

```text
min(x_n,1-x_n) < delta_n
  -> 3/10 + gamma < x_(n+1) < 4/10 - gamma,
gamma = 76831/13885440.
```

Indeed the exact update and
`20/53 < {144*pi} < 44/113` send both boundary branches into the same
oriented child `3`.  Hence first-omitted-term boundary events cannot be
consecutive, closing boundary sticking, consecutive-wrap cascades and
reflection-persistent boundary induction.  This supplies no unconditional
target order: `delta_n` is summable and exponentially shrinking, no boundary
event occurs in the exact scan through `n=2000` (`experiment`), and the
2-syndetic complement merely avoids a vanishing boundary layer.  Reopen only
with an independent BBP numerator or principal-embedding theorem forcing
infinitely many canonical shrinking-boundary hits (or a weaker fixed-margin
target event) together with a direct T69 or FMR transfer.

The same row also records an anticipatory scalar-carry separator.  Writing the
exact BBP forcing as `tau_n=Theta_n-452 in (0,1)`, every prescribed future
carry word `d_n in {8,9}` has the unique bounded trajectory
`s_n=sum_(j>=0) (d_(n+j)-tau_(n+j))/10^(j+1)`, with
`7/9<s_n<1` and `s_(n+1)=10*s_n+tau_n-d_n` (`proof sketch`, independently
audited).  Thus even complete knowledge of the future scalar forcing leaves a
translated binary Cantor family of word-restricted trajectories.  These are
counterfactual real initial conditions, not canonical rational BBP residues:
membership of the actual residue is precisely the shifted deleted-digit
identity
`delta_N(d)=10^N*pi-floor(X_N)-452/9`, and rationality alone would not select
that value or its past-compatible numerator class.  Reopen this scalar-carry
route only with a theorem about the canonical BBP numerator/gcd or principal
real embedding that forces a target-directed one-branch bottleneck or
extinction on an independently chosen unbounded set.  More scalar carry
chambers or numerical residue hits do not qualify.

The same separator holds coordinatewise for every finite or countable family
of uniformly small scalar forcings `|tau_n^j|<=1`: the canonical future sums
`E_n^j=sum_(r>=0) tau_(n+r)^j/10^(r+1)` satisfy
`E_(n+1)^j=10E_n^j-tau_n^j`, so translation by `E_n^j` conjugates every
coordinate to one ordinary decimal branch.  For every forbidden word and
compatible prefix, a two-digit self-similar tail contains a transcendental
badly approximable point, hence one with exact `mu=2`, realizing that same safe
digit in all coordinates (`proof sketch`;
[Kleinbock--Weiss](https://doi.org/10.1007/BF02772538) and
[Kristensen--Thorn--Velani](https://arxiv.org/abs/math/0405433) full-dimension
inputs `literature-checked`; independently audited).  In particular, after the
correct normalization
`U_(c,n)=-(12/c)*log eta(i*c*10^n)=pi*10^n+epsilon_(c,n)`, the positive eta
errors give forcings of magnitude `<1/3` and are dynamically removable when
only their signs, bounds and affine scalar recurrences are used.  This does
not counterfeit canonical cross-coordinate algebraic relations, integrality
or numerator constraints, nonlinear principal-embedding signs, or
matrix-valued noncommuting cocycles.  Arbitrary larger bounded forcings also
require a separate invariant-margin hypothesis; rescaling does not preserve
the common digit decoder.

Exact punctured decimal decimation gives a narrower boundary for the finite
seed route (`proof sketch`, independently audited).  For `Q=10q`, deleting the
selected child time and splitting frequencies into `10∤ell` and `ell=10h`
leaves a nondivisible innovation plus fine-child-weighted parent frequencies
on the late punctured window `[q+1,Q]` minus `{n}`.  The same deletion removes the
shifted parent time, so neither inherited `[0,q)` capital nor the T194 central
atom transfers through this identity.  The existing `3q/2` atom floor is
experimentally insufficient, but this does not exclude a stronger
actual-π atom estimate.  More generally, at a fixed tuple write
`Y_d(x)=D_d(x)-max(0,-G_d(x))`.  For any certified rational shadows
`|pi-r_j|<=epsilon_j->0` and finite Lipschitz constant `Lambda_q`, existence
of an index with `Y_d(r_j)>Lambda_q*epsilon_j` is equivalent to
`Y_d(pi)>0`; it exactifies FMR rather than weakening it.  Factoring the
rational denominator rewrites the same sign as a distinguished generalized
Gaussian-period combination in a moving modulus.  Special modulus classes
can sign individual periods, but no theorem puts a named π-approximant
sequence in those classes or controls the complete target-weighted
combination and path alignment.  Reopen only with a named actual-π sign theorem for
the complete punctured literal sum that survives the period-four and exact
`mu=2` continuation separators.

The `Zero sector, scalar moments, unsigned energy` row also covers pure-gauge
spectral lifts.  For finite indices `nu_j`, any difference kernel `c`, and a
target character `chi_A`, the twist
`T_A(j,l)=c(nu_j-nu_l) * conj(chi_A(nu_j-nu_l))` satisfies
`T_A=D_A*T_0*D_A^*`, with `D_A=diag(conj(chi_A(nu_j)))`.  Thus every
unitary-similarity invariant is target-independent at every rank.  For the
exact full-circulant lift of the T172 support expansion—after grouping the
raw frequencies modulo `q`, not on the compressed primitive-ray index—the
minimum Hermitian eigenvalue is precisely the minimum of the simultaneous
fixed-horizon target real parts (`proof sketch`, independently audited).
More generally, on any finite directed graph with arbitrary target-independent
edge amplitudes, if every literal-character exponent is congruent modulo `q`
to a vertex-label difference, then the matrices for any two integer targets
are diagonally unitarily similar.  Integer lifts give only target-independent
closed holonomy, and a nonprincipal minor retains at most the original
endpoint character (`proof sketch`, independently audited).  Thus neither
non-difference amplitudes nor lifted wrapping reopen the closed spectral route
inside this exact-gradient class.  A target-blind invariant with one uniform
sufficient implication could only certify all targets at a common horizon; it
cannot exploit the weaker `forall A, exists N_A` quantifier by itself.  This
does not exclude target-dependent amplitudes, non-exact target cocycles,
nonzero literal phases on self-loops, open matrix coefficients, or
constructions without a common vertex-potential representation.  Reopen only
after an explicit actual-pi packet already exhibits target-dependent
underlying-cycle holonomy not inserted externally, together with a proved
distinguished-real sign, an exact PBFS/FMR readout, and failure on suitable
word-avoiding replacements.

The same closed-invariant boundary persists for a wider noncommuting class
(`proof sketch`, independently audited): if simultaneous phase reversal is
implemented by one involution `J`, every variable factor satisfies
`R(-theta)=J*R(theta)*J`, and all interleaved fixed factors commute with `J`,
then the full ordered product is `J`-conjugate under reversal.  Trace,
spectrum, singular values, conjugacy-invariant norms and corresponding closed
growth data are therefore reflection-even.  This does not cover a `J`-breaking
or nonsimultaneous phase law, nor an open coefficient with boundary vectors
whose orientation is supplied independently by actual-π arithmetic.  The
literal T179 digit-DFT operator itself is already commuting; its natural
Heisenberg--Weyl realization closes to the original scalar phase, while a
Magnus enlargement leaves the missing `Xi_d` as its linear open coefficient
and adds commutators with no deterministic same-child sign.  Robustly
branching successor-local matrix rules remain a special case of the existing
representation-free safe-tree separator, not a new escape.

Two-step KZ data add one narrow boundary (`proof sketch`, independently
audited).  In the explicit convention whose degree-two term is
`-zeta(2)*X*Y+zeta(2)*Y*X`, the relations
`[X,[X,Y]]=[Y,[X,Y]]=0` give formally
`Phi_KZ(X,Y)=exp(-zeta(2)*[X,Y])`.  A finite-dimensional central commutator is
nilpotent, so every closed spectral readout is unipotent.  A Weyl
central-character specialization instead makes the associator scalar and can
formally reproduce `e(h*10^n*pi)`, but target rotation then returns exactly
the original unoriented character.  This closes only formal two-step central
spectra and scalar central-character phase readers; analytic unbounded-operator
realizations require domain/completion control, and non-two-step noncentral
representations or independently oriented open coefficients remain outside
scope.

A proposed positive cyclotomic-fibre compression has a sharper conditional
separator (`proof sketch`, independently audited).  For nonnegative weights
`a_d`, `S=sum_d a_d`, `lambda_r=sum_d a_d*omega^(r*d)`, one has
`S^2-|lambda_r|^2=4*sum_(d<e) a_d*a_e*sin^2(pi*r*(d-e)/10)`.  Thus two
phase-distinct branches of mass at least `eta*S` contract the normalized
character by at most `sqrt(1-4*eta^2*sin^2(pi/10))`, multiplicatively across
adaptive scales.  Equality means support in one coset modulo
`10/gcd(r,10)`, hence a single preselected digit for primitive `r`.  This
closes only scalar nonnegative translation-covariant fibre descents: the
cyclotomic KZ distribution maps themselves supply neither such weights nor a
decimal-child identification.  Reopen with an explicit signed or
noncirculant conductor coefficient whose actual-pi distinguished-real sign is
proved before inserting the target and directly signs a nonzero child mode.

The uniform high-degree integer-polynomial exclusion route has an additional
quantitative boundary (`proof sketch`; source input `literature-checked`,
independently audited).  For every nonempty forbidden word `w`, the compact
symbolic avoidance image `X_w` contains an affine two-digit Cantor copy and
satisfies
`cap(X_w) >= (2/225) * 10^(-(abs(w)-1))`.  Hence an integer polynomial `P`
of degree `m` obeys
`norm(P, 3+X_w) >= abs(leadingCoefficient(P)) * cap(X_w)^m`.  By contrast,
the available Nesterenko--Waldschmidt lower bound for `P(pi)`
([Theorem 2(2)](https://arxiv.org/abs/math/0002047), with coefficient length
`L(P)`) is only
`exp(-O(d * (log L + d log d) * (1 + log d)))`.  For fixed `w` this is too
weak, at sufficiently large degree, to contradict membership in `3+X_w`
through one uniformly small integer polynomial.  This closes only that
asymptotic capacity-plus-current-transcendence-measure comparison: bounded
degree, nonuniform or local analytic families, and stronger signed
pi-specific estimates remain open.  Reopen the polynomial route only with a
pi bound at the exponential-in-degree scale, a strictly smaller
word-sensitive norm, and an actual exclusion or orientation mechanism.

For every audited turn merge duplicates into one row and retain only the
strongest new lemma, first fatal line or surviving step, and genuinely new
input required to reopen.
