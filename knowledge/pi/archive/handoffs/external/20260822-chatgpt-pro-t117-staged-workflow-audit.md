# ChatGPT Pro T117 staged-workflow architecture audit

Date: 2026-08-22 UTC

Status: `proof sketch` workflow audit

Model label: ChatGPT Pro

Prompt SHA-256: `1b2cd730597f88b477235ada702812c276e0798d0a98f2e5f48bb67409d021fe`

Response SHA-256: `0e69e8d483934d2e649aa0d0c0258329c5093c33f6dc41102214a746e61086c1`

The reviewer could inspect pushed branch head `dc6bc36`, but not later local S1/T118 changes. Treat this as an architecture critique, not verification of current code. The browser job completed normally with no re-login requirement.

---

Scope and verdict

I audited the GitHub branch head dc6bc36f0f42aa1b2fdbdb93e3cb84af0839c40c. The local checkout /home/Marcel/dev/PI was not mounted, so uncommitted or unpushed local changes are outside this audit. The audited branch currently contains only the older README.md, census.py, and verify_census.py under t116-gcd-census; the proposed S1–S9 implementation is not present.

The checked-in census is a different experiment: N=0,…,511, g=gcd(∣U∣,V), and laws G1–G4. Its verifier does independently replay four literal BBP poles, but it is not filesystem-isolated from the generator. It must not be reused under the new experiment/schema identity.

Verdict: the staged decomposition is fundamentally sound, but the architecture as written is not yet trustworthy. The mandatory corrections below make it sound as an exact finite experiment—not as proof of any listed mathematical claim.

Mandatory corrections, prioritized
P0.1 — Freeze a new experiment identity and noncircular artifact graph

Create a new immutable experiment_id and schema namespace. Do not reuse t116-gcd-census-v1; its range, records, and laws differ.

Freeze two controller-owned inputs:

math_spec: the exact definitions in the prompt, including inclusivity and failure polarity.

plan: only the ordered shard table and boundary indices, plus math_spec_sha256.

Every checkpoint, shard, receipt, aggregate, and documentation result must bind both hashes. Do not make plan contain checkpoint hashes if checkpoints themselves contain plan_sha256; that would be circular. Use:

math spec→plan→audited checkpoint set→shards→S6 receipts→aggregate→final manifest.

Treat S4–S7 before S8 as program qualification, not production execution. Production checkpoints and shards must be generated only by the S8-sealed source/runtime assembly.

P0.2 — Freeze the indexing and endpoint contract explicitly

With inclusive bbpPartial:

P
N
	​

=
j=0
∑
7N
	​

t
j
	​

,P
N+1
	​

=P
N
	​

+
j=7N+1
∑
7N+7
	​

t
j
	​

.

The increment is exactly the seven indices

7N+1,7N+2,…,7N+7.

For a shard [a,b):

input state is exactly P
a
	​

;

records are exactly N=a,…,b−1;

after each record, advance from P
N
	​

 to P
N+1
	​

;

final state is exactly P
b
	​

;

no F
b
	​

, P
b+1
	​

, or record N=b belongs to the shard.

The minimal semantic checkpoint is:

B
N
	​

=(schema,experiment,math hash,plan hash,N,7N,P
N
num
	​

,P
N
den
	​

).

Including next_bbp_index = 7*N+1 is useful redundant protection. Q
N
	​

 may also be stored redundantly, but it is not required state. Any cached power of 16 is operational state and must be derived from N, never trusted as checkpoint authority.

S4a and S4b must both start from P
0
	​

=t
0
	​

=47/15 and sequentially reach P
4096
	​

. They must not accept a supplied P
512
	​

 as their trust root.

The production plan is exactly:

i=0,1:
i=2,…,9:
i=10,…,41:
	​

[512+256i,512+256(i+1)),
[1024+128(i−2),1024+128(i−1)),
[2048+64(i−10),2048+64(i−9)).
	​


That means 42 shards, 43 checkpoints, 3,584 records, and records exactly N=512,…,4095.

P0.3 — Freeze the exact record and compute redundant identities independently

The record semantics should be explicitly frozen as something equivalent to

R
N
	​

=(N,A,D,C,E,H,d,e,X,U,V,k,g,W,k
2
,K1fail,K2fail).

Large integers should be canonical decimal strings.

Both arithmetic routes must independently establish:

D,E>0;

gcd(∣A∣,D)=gcd(∣C∣,E)=1;

H=gcd(D,E);

D=Hd, E=He, gcd(d,e)=1;

X=10Ae+Cd;

U=10AE+CD=HX;

V=DE=H
2
de;

k=gcd(∣X∣,Hd);

g=gcd(∣U∣,V), computed directly rather than defined as Hk;

W=V/g, computed directly rather than defined as De/k;

g=Hk;

W=De/k;

10Q
N
	​

+F
N
	​

=Q
N+1
	​

.

The equality g=Hk is not a free algebraic rewrite. It uses reducedness:

X≡Cd(mode),gcd(C,e)=1,gcd(d,e)=1,

hence gcd(X,e)=1. Both routes should check that coprimality rather than silently depend on it.

A valuable fixed oracle is:

N=1:k=95.

This kills several plausible wrong implementations, including gcd(C,D), gcd(X,H), and mishandling of the common denominator.

Also enforce the structural implication

K2fail⟹K1fail,

because d≥1.

P0.4 — Replace import bans with actual source isolation

“Forbidden import” checks are not isolation. Python code can use importlib, exec, subprocesses, PYTHONPATH, sitecustomize, symlinks, package data, or direct file reads.

The controller must construct disjoint, allowlisted execution images:

S2 image: S1 + S2 only.

S3 image: S1 + S3 only; no S2 bytes anywhere.

S4b image: S1 + S3 + checkpoint inputs; no S2 or builder source.

S6 image: S1 + S3 + approved checkpoint/shard inputs; no S2/S5 source or prior shard workspace.

S7 image: S1 only.

Use read-only source/input mounts, sanitized environment, controlled sys.path, no user site, no network, and a dedicated output directory. Static source scans remain useful but are only supplementary.

S1 must contain no BBP constants, rational normalization, gcd calls, arithmetic lookup tables, or law classification. Its canonicalization and SHA behavior must be tested against controller-owned byte vectors, because an S1 bug is otherwise a common-mode failure.

The N=0,1,2 and hidden oracles must be immutable controller data, not generated at runtime by S2, S3, or a shared arithmetic helper. A “hidden” index committed beside the candidates is not hidden.

P0.5 — Make approval controller-authenticated and eliminate TOCTOU

SHA-256 establishes byte identity. It does not establish that S6 approved those bytes.

The safe sequence is:

Candidate process exits and loses write access.

Controller ingests each regular file into controller-owned content-addressed storage.

S4b or S6 verifies that exact immutable blob.

Controller—not candidate code—mints a receipt over that blob.

All later stages consume the same content-addressed blob, never the original path.

Do not verify a mutable path and then copy or reopen it. Reject symlinks, path traversal, unexpected hard links, nonregular files, and artifact changes after verification.

Each S6 receipt must bind at least:

assembly-manifest hash;

experiment, math-spec, plan, and checkpoint-set hashes;

shard index and exact [a,b);

record count;

raw shard SHA-256;

start and end checkpoint hashes;

verifier source digest and runtime/container digest;

verdict;

exact per-shard first K1 failure or null;

exact per-shard first K2 failure or null.

Use two manifests:

an assembly manifest, sealed after the tiny E2E, binding source, runtime, tests, spec, plan, and E2E receipts;

a final run manifest, binding the checkpoint set, production shards, S6 receipts, aggregate, and assembly-manifest hash.

The external root hash or signature must be stored outside candidate write authority. A manifest made “read-only” inside a candidate-controlled directory is not a trust root.

P0.6 — Restrict S7 to selection, never classification

S7 can remain schema-only only if it does not calculate k
2
>e or k
2
>de.

The clean design is for each controller-authenticated S6 receipt to contain the verified first failure projection for that shard. S7 then:

requires exactly indices 0,…,41;

validates each index’s exact bounds against the frozen plan;

validates all receipt hashes against the external allowlist;

validates end_checkpoint_sha256[i] == start_checkpoint_sha256[i+1];

selects the smallest numeric N among non-null per-shard projections;

copies the projection without recomputation or normalization.

An exact aggregate witness should be self-contained and source-bound:

(law, n, k, d, e, lhs=k², relation="gt", rhs,
 shard_index, record_offset, record_sha256,
 shard_sha256, verifier_receipt_sha256)

For K1, rhs=e; for K2, rhs=d*e. Equality is not failure. No failure is JSON null, never an empty object, zero, "passed", or a success witness.

Numeric ordering must be based on parsed bounded integers, never filenames or strings.

P1.7 — Make canonical serialization genuinely strict

Freeze exact bytes, not merely equivalent parsed JSON:

UTF-8, no BOM;

ASCII-only keys and constrained ASCII values;

sorted keys, no insignificant whitespace;

LF line endings and mandatory final LF;

duplicate keys rejected during parsing;

unknown and missing fields rejected;

arbitrary-precision integers encoded as canonical decimal strings;

reject +1, 01, -0, whitespace, floats, exponents, and booleans in integer fields;

denominators lexically positive and later arithmetically checked;

lowercase 64-character SHA-256;

raw input bytes must equal canonical re-encoding before acceptance.

Apply controller-owned limits for total bytes, line length, nesting, and decimal digits before expensive integer conversion. Pin Python version and int_max_str_digits; the tiny run does not exercise production-sized integers.

Every security-critical binding field must be mutation-tested to ensure changing it either invalidates the schema or changes the digest.

P1.8 — Expand the tests; [0,8) alone is inadequate

The tiny run is useful, but insufficient. Under the frozen definitions, N=0,…,7 has no K1 or K2 failure, so it never exercises a non-null witness path.

Use an uneven split such as:

[0,3),[3,8),

and run the second shard in a fresh pod containing neither shard 0 nor its output directory.

Additionally require:

a plan-only fixture for all 42 production indices and all 43 boundaries;

an aggregate fixture with at least indices 0–11, preferably all 0–41, to expose 10 versus 2 ordering;

synthetic controller receipts covering K1-only failure, K2 failure, equality, and all-null results;

after S8 succeeds, generate and verify production shard 41 first, in isolation. This exercises the largest indices and integers without running the full census.

P1.9 — Kill these deterministic mutations

The external controller suite must reject every one of the following classes:

Index and scale mutations: inclusive-to-exclusive partial; 7N−1 or 7N+1; six, eight, shifted, duplicated, or omitted advancement terms; wrong pole/sign/base; 10
N
 instead of 10
N+1
 in F
N
	​

; wrong Q
N
	​

 scale; computing F
N
	​

 only as Q_next - 10*Q so the recurrence becomes tautological.

Normalization and polarity mutations: unreduced rational; negative denominator; wrong H; swapped d,e; missing factor 10 or wrong sign in X; gcd(C,D), gcd(X,H), gcd(X,d), or gcd(U,V) substituted for k; omitted abs; deriving g only from Hk; wrong factor in W; E substituted for e; DE substituted for de; squaring g instead of k; >= instead of >; K1/K2 label swap. Include synthetic negative-X, zero-numerator, and equality inputs.

Artifact mutations: missing, extra, duplicate, reordered, or out-of-range record; record N=b; boundary changed while retaining the same rational; start/end hash swap; checkpoint from another plan; duplicate JSON key; leading zero; boolean-for-integer; CRLF; BOM; missing final LF; single-byte mutation; digest over reserialized rather than raw bytes.

Trust and aggregate mutations: missing or duplicate shard index; gap or overlap; lexicographic ordering; stale or forged receipt; changed verifier/runtime digest; artifact modified after receipt; checkpoint splice across runs; later witness selected while an earlier one exists; equality emitted as failure; non-null changed to null; K1/K2 witness swap; S3 attempting to import/read/execute S2; S6 attempting to access S5 source.

P1.10 — Separate artifact verification from mathematical claims

The existing README correctly describes its finite result as an experiment, but the older code also uses terminology such as "accepted_experiment" for laws that survived its range. Do not carry that vocabulary into the new pipeline.

The final machine-readable result should contain:

status: "experiment";

exact tested interval and record count;

first_k1_failure: <object|null>;

first_k2_failure: <object|null>;

an exact forbidden-claims array covering K1, K2, occupancy, density, cancellation, normality, decimal occurrence, and V1.

verified may describe artifact integrity. It must never describe K1 or K2 as mathematically established.

Minimal acceptance checklist

 New experiment/schema identity; exact Git commit, stage-source hashes, controller-test hashes, runtime image digest, math-spec hash, and plan hash are pinned.

 S1 passes fixed canonical byte/hash vectors and rejects duplicate keys, noncanonical integers, unknown fields, malformed NDJSON, and oversized inputs.

 S2 and S3 run in physically disjoint allowlisted images and pass full-record oracles at N=0,1,2, including k
1
	​

=95, plus the hidden vector and synthetic sign/equality vectors.

 S4a and S4b independently derive from P
0
	​

=47/15 and agree on exactly 43 canonical checkpoint blobs at the frozen boundaries.

 Tiny E2E [0,3) + [3,8) succeeds; the second shard succeeds in a fresh workspace with no shard-0 artifact.

 Every deterministic mutation above is rejected by the appropriate external gate.

 S8 seals an assembly manifest only after the complete tiny E2E; production runs use only those sealed blobs.

 Controller CAS ingestion, verifier invocation, receipt creation, and later consumption use the same immutable bytes; no verify-then-copy path exists.

 Production shard 41 succeeds first in isolation, followed by exactly 42 independently verified shards covering 512,…,4095, with 42 controller-authenticated receipts.

 S7 rejects any index, bound, checkpoint-chain, artifact-hash, receipt-hash, plan, or verifier-identity discrepancy and emits only exact strict-failure witnesses or null.

 The final run manifest binds the assembly, checkpoint set, all shards, receipts, aggregate, and documentation.

 All outputs and documentation retain status experiment and contain no positive proof claim for any forbidden property.

What the experiment can legitimately answer

It can determine, exactly and reproducibly for every N∈[512,4096):

the frozen rational tuple R
N
	​

;

whether k
2
>e and whether k
2
>de;

the first strict failure of each inequality in that finite interval, or that no such failure was observed there;

whether the combined and literal implementations agree under the sealed software stack.

A non-null strict witness is a finite counterexample to the corresponding universal inequality under the frozen computational definitions. A null result says only that no strict failure occurred in the tested interval. Neither outcome establishes occupancy, density, cancellation bounds outside the records, normality, decimal occurrence, V1, or any bridge from these finite rational computations to those claims.

After the corrections above, the architecture is sound for its declared finite-experiment purpose. No smaller replacement is necessary; collapsing these stages would weaken the route-independence and artifact-authority boundaries that the design is trying to obtain.
