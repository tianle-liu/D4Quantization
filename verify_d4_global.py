"""Run the computations for the optimality proof for D4.

The program reconstructs the geometry and moment polynomials in a temporary
directory, checks six polynomial identities, and verifies the final scalar
comparisons. REVIEWING.md relates these calculations to the proof.
Only the Python standard library is required.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
import json
import shutil
import subprocess
import sys
import tempfile


def run(folder, name, *args):
    print("Running", name, *args, flush=True)
    subprocess.run([sys.executable, "-B", str(folder / name), *map(str, args)],
                   cwd=folder, check=True)


def determinant(M):
    if len(M) == 1:
        return M[0][0]
    return sum((-1)**j * M[0][j] * determinant(
        [row[:j] + row[j+1:] for row in M[1:]]) for j in range(len(M)))


def scalar_checks():
    """Check the endpoints and lattice identification in Section 2.4.

    The paper supplies the AM--GM bounds and the concavity arguments which
    make these finitely many endpoint comparisons sufficient on intervals.
    """
    A = [[2,1,-1,-1], [1,2,-1,-1], [-1,-1,2,0], [-1,-1,0,2]]
    Ai = [[F(x,2) for x in row] for row in
          [[2,0,1,1], [0,2,1,1], [1,1,2,1], [1,1,1,2]]]
    B = [[1,1,-1,-1], [1,0,0,0], [0,1,0,0], [0,0,1,-1]]
    assert determinant(A) == 4 and abs(determinant(B)) == 2
    assert [[sum(B[k][i]*B[k][j] for k in range(4))
             for j in range(4)] for i in range(4)] == A
    assert all(sum(B[k][j] for k in range(4)) % 2 == 0 for j in range(4))
    assert [[sum(A[i][k]*Ai[k][j] for k in range(4))
             for j in range(4)] for i in range(4)] == [
                 [int(i == j) for j in range(4)] for i in range(4)]
    for cone in (2,3):
        vectors = []
        for i,j in combinations(range(5),2):
            if (i,j) == (1,2) or (cone == 3 and (i,j) == (3,4)):
                continue
            vectors.append([int(j == k+1)-int(i == k+1) for k in range(4)])
        if cone == 3:
            vectors.append([1,1,-1,-1])
        assert len(vectors) == 9
        assert all(sum(Ai[i][j]*v[i]*v[j] for i in range(4)
                       for j in range(4)) == 1 for v in vectors)
    assert F(7,20) < F(10,13)**4
    for lo,hi,slope,intercept in [
        (F(7,20),F(2,3),110,F(21,2)),
        (F(2,3),F(1),124,F(20))]:
        for d in (lo,hi):
            line = slope*d-intercept
            assert line > 0
            residual = line**4-104**4*d**5
            assert (residual == 0) if d == 1 else (residual > 0)
    scaled_bound_fourth = F(114244,625)  # (48*13/(120*sqrt(2)))**4
    assert scaled_bound_fourth == 48**4*F(169,28800)**2
    assert scaled_bound_fourth < 200
    for lo,hi,k,beta in [
        (F(1,200),F(9,1000),F(13,10),F(29,20000)),
        (F(9,1000),F(1,80),F(3,2),F(163,50000))]:
        for d in (lo,hi):
            line = k*d-beta
            assert line > 0 and line**4 > scaled_bound_fourth*d**5
    print("Trace normalization, scalar endpoints, and D4 identification PASS.")


def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError("Verification requires assertions; do not use -O.")
    source = Path(__file__).resolve().parent / "d4-certificate"
    with tempfile.TemporaryDirectory(prefix="d4-global-proof-") as tmp:
        folder = Path(tmp) / "certificate"
        shutil.copytree(source, folder)
        # These stages overwrite the copied geometry and moment files. The
        # SOS checkers below therefore use freshly reconstructed polynomials.
        print("[1/5] Reconstruct Voronoi geometry and moment polynomials.", flush=True)
        for name in ("reconstruct_c1.py", "reconstruct_c23_geometry.py",
                     "reconstruct_c23_moments.py"):
            run(folder, name)
        print("[2/5] Compare every distributed moment coefficient with its reconstruction.", flush=True)
        for cone in (1,2,3):
            old = json.loads((source / f"c{cone}-moment.json").read_text())
            new = json.loads((folder / f"c{cone}-moment.json").read_text())
            for key in ("D_coefficients", "S_coefficients" if cone == 1 else "N_coefficients"):
                assert old[key] == new[key]
        print("[3/5] Verify all six polynomial identities.", flush=True)
        run(folder, "verify_c1_simplified.py")
        run(folder, "verify_c23_simplified.py")
        print("[4/5] Reconstruct moments again by boundary triangulation.", flush=True)
        run(folder, "rebuild_triangulation.py")
        for cone in (1,2,3):
            tri = json.loads((folder / f"rebuilt_C{cone}.json").read_text())
            geo = json.loads((folder / f"c{cone}-moment.json").read_text())
            # Triangulation places a last; the C2/C3 localization data place
            # it first. Compare polynomials only after aligning parameters.
            move = (lambda e: tuple(e)) if cone == 1 else (lambda e: (e[-1], *e[:-1]))
            assert {move(e):c for e,c in tri["D"]} == {
                tuple(e):c for e,c in geo["D_coefficients"]}
            moment_key = "S_coefficients" if cone == 1 else "N_coefficients"
            # Triangulation always returns 60*D*M; on C1 the stored S is
            # 12*D*M, so the comparison there is with 5*S.
            factor = 5 if cone == 1 else 1
            assert {move(e):c for e,c in tri["N"]} == {
                tuple(e):factor*c for e,c in geo[moment_key]}
        print("The two integrations give the same moment polynomial on each cone.")
    print("[5/5] Verify scalar endpoints and the identification of D4.", flush=True)
    scalar_checks()
    print("ALL D4 GLOBAL PROOF CHECKS PASSED.")


if __name__ == "__main__":
    main()
