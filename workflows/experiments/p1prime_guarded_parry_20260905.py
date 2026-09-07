"""Finite guard, Parry-mask and conditional-tail audits; not an infinite proof.

Requires Python 3.10+ and NumPy. Prints results, writes no files.
"""
import numpy as np
from p1prime_arbitrary_word_audit_20260905 import transition_table, follow


def run_case(word):
    m = len(word)
    B = 10**m
    tab = transition_table(word)
    digit_matrix = np.zeros((m, m))
    for row in range(m):
        for v in tab[row]:
            if v >= 0:
                digit_matrix[row, v] += 1
    eigenvalues, vectors = np.linalg.eig(digit_matrix)
    i = np.argmax(eigenvalues.real)
    lam = eigenvalues[i].real
    h = vectors[:, i].real
    h /= h[0]
    assert np.max(abs(digit_matrix @ h - lam*h)) < 1e-10
    assert h.min() > 0 and h.max()/h.min() <= 2 + 1e-10
    assert 10**m/lam**m <= 9/8 + 1e-10
    free = np.zeros((m, 10, m))
    for u in range(m):
        for digit, v in enumerate(tab[u]):
            if v >= 0:
                free[u, digit, v] = h[v]/(lam*h[u])
    assert np.max(abs(free.sum(axis=(1, 2))-1)) < 1e-10
    assert free[free > 0].min() >= .05 - 1e-10

    beta = next(str(d) for d in range(1, 9)
                if str(d) not in (word[0], word[-1]))
    for u in range(m):
        assert tab[u][int(beta)] >= 0
        assert follow(tab, u, beta*m) == 0
    omitted = word[0]
    alphabet = [str(d) for d in range(10) if str(d) != omitted]
    marker = next(a for a in alphabet if a not in ('0', '9'))
    packet = ''.join(a+marker for a in alphabet)
    # Unaligned guards exercise blocks containing both free and forced digits.
    start = 2*m+1
    prescribed = beta*m+packet
    forced = {start+i: int(a) for i, a in enumerate(prescribed)}
    N = ((start+len(prescribed)+m-1)//m+2)*m
    kernels = []
    reachable = {0}
    for pos in range(N):
        kernel = free.copy()
        if pos in forced:
            kernel[:] = 0
            digit = forced[pos]
            for u in range(m):
                v = tab[u][digit]
                if v >= 0:
                    kernel[u, digit, v] = 1
        assert all(abs(kernel[u].sum()-1) < 1e-10 for u in reachable)
        reachable = {v for u in reachable for d in range(10)
                     for v in range(m) if kernel[u, d, v] > 0}
        kernels.append(kernel)

    # Direct path enumeration within each block, independent of conjugation.
    masks = []
    words = [f'{a:0{m}d}' for a in range(B)]
    for j in range(N//m):
        mask = np.zeros((m, m, B))
        for u in range(m):
            for a, block in enumerate(words):
                state, probability = u, 1.
                for offset, digit in enumerate(map(int, block)):
                    nxt = tab[state][digit]
                    if nxt < 0:
                        probability = 0.
                        break
                    probability *= kernels[j*m+offset][state, digit, nxt]
                    state = nxt
                if probability:
                    mask[u, state, a] = probability
        if not any(j*m <= pos < (j+1)*m for pos in forced):
            for u in range(m):
                for a, block in enumerate(words):
                    v = follow(tab, u, block)
                    if v >= 0:
                        assert abs(mask[u, v, a]-h[v]/(lam**m*h[u])) < 1e-11
        masks.append(mask)

    maximum_error = 0.
    checks = 0
    # Start after arbitrary block depths and states: a stronger finite check
    # than only conditioning on one sampled positive-mass prefix.
    for depth in range(0, N, m):
        for state in range(m):
            for frequency in (0, 1, 17, B-1, B+7):
                row = np.eye(m)[state].astype(complex)
                for j, kernel in enumerate(kernels[depth:]):
                    phase = np.exp(-2j*np.pi*frequency*np.arange(10)/10**(j+1))
                    row = row @ np.einsum('udv,d->uv', kernel, phase)
                direct = row.sum()
                row = np.eye(m)[state].astype(complex)
                for j, mask in enumerate(masks[depth//m:]):
                    phase = np.exp(-2j*np.pi*frequency*np.arange(B)/B**(j+1))
                    row = row @ np.einsum('uva,a->uv', mask, phase)
                error = abs(direct-row.sum())
                assert error < 1e-10
                maximum_error = max(maximum_error, error)
                checks += 1
    return checks, maximum_error


if __name__ == '__main__':
    # A legal guard digit need not reset in one step.
    table = transition_table('121')
    assert follow(table, 1, '2') == 2
    assert all(follow(table, u, '222') == 0 for u in range(3))
    cases = ('00', '01', '000', '001', '010', '012', '121', '0010', '0123')
    results = [run_case(word) for word in cases]
    print('PASS: guarded Parry finite experiment;', len(cases), 'words;',
          sum(c for c, _ in results), 'conditional-tail comparisons;',
          'max error', max(e for _, e in results))
