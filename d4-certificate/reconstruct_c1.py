"""Zonotope integration for the principal cone in dimension four.

Standard library only.  Integrates a coherent 125-parallelotope tiling, then
compares its complete degree-nine numerator with D times the degree-five
formula recorded in Zimmermann (2017), equation (6.10).
"""
from itertools import combinations, permutations
from fractions import Fraction
from collections import defaultdict
from pathlib import Path
import json, time

N=10
ZERO=(0,)*N
EDGES=list(combinations(range(5),2))
GS=[tuple(int(i==v)-int(j==v) for v in range(1,5)) for i,j in EDGES]

def add(*args):
    r=defaultdict(int)
    for p in args:
        for e,c in p.items(): r[e]+=c
    return {e:c for e,c in r.items() if c}
def scale(p,c): return {e:v*c for e,v in p.items() if v*c}
def mul(p,q):
    r=defaultdict(int)
    for e,c in p.items():
        for f,d in q.items(): r[tuple(a+b for a,b in zip(e,f))]+=c*d
    return {e:c for e,c in r.items() if c}
def shift(p,indices,c=1):
    f=[0]*N
    for i in indices:f[i]+=1
    return {tuple(a+b for a,b in zip(e,f)):v*c for e,v in p.items()}
def variable(i):
    e=[0]*N;e[i]=1;return {tuple(e):1}
def parity(p): return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def determinant(A):
    out={}
    for p in permutations(range(len(A))):
        term={ZERO:parity(p)}
        for i,j in enumerate(p):term=mul(term,A[i][j])
        out=add(out,term)
    return out
def inverse(A):
    n=len(A);M=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(n)] for i,row in enumerate(A)];det=Fraction(1)
    for i in range(n):
        j=next((j for j in range(i,n) if M[j][i]),None)
        if j is None:return None,0
        if i!=j:M[i],M[j]=M[j],M[i];det=-det
        p=M[i][i];det*=p;M[i]=[x/p for x in M[i]]
        for j in range(n):
            if i!=j and M[j][i]:
                p=M[j][i];M[j]=[x-p*y for x,y in zip(M[j],M[i])]
    return [r[n:] for r in M],det
def orbit(edges):
    monos=set()
    for p in permutations(range(5)):
        e=[0]*N
        for i,j in edges:e[EDGES.index(tuple(sorted((p[i],p[j]))))]+=1
        monos.add(tuple(e))
    return {e:1 for e in monos}
def evaluate(p,x):return sum(c*prod(xi**ei for xi,ei in zip(x,e)) for e,c in p.items())
def prod(x):
    p=1
    for y in x:p*=y
    return p

def main():
    """Implement the zonotope integration identity in Proposition 2.2.

    W is D*S, computed by integration over the coherent parallelotope tiling.
    S is constructed from graph orbits. Compare the coefficients of W and D*S.
    """
    start=time.time()
    xs=[variable(i) for i in range(N)]
    Q=[[add(*(scale(xs[k],g[i]*g[j]) for k,g in enumerate(GS))) for j in range(4)] for i in range(4)]
    D=determinant(Q)
    adj=[[scale(determinant([[Q[a][b] for b in range(4) if b!=i] for a in range(4) if a!=j]),(-1)**(i+j)) for j in range(4)] for i in range(4)]
    K={}
    for i in range(N):
        for j in range(i,N):
            K[i,j]=add(*(scale(adj[a][b],GS[i][a]*GS[j][b]) for a in range(4) for b in range(4)))
    # A nonzero minor of the reduced incidence matrix selects a spanning
    # tree. The signs below select the upper facets of the lifted zonotope.
    trees=[];W={};treepoly={}
    h=[2**i for i in range(N)]
    for B in combinations(range(N),4):
        G=[[GS[j][i] for j in B] for i in range(4)]
        inv,det=inverse(G)
        if not det:continue
        assert abs(det)==1
        trees.append(B);treepoly=add(treepoly,shift({ZERO:1},B))
        non=[j for j in range(N) if j not in B]
        signs={}
        for j in non:
            coeff=[sum(inv[i][a]*GS[j][a] for a in range(4)) for i in range(4)]
            height=h[j]-sum(h[b]*coeff[i] for i,b in enumerate(B))
            assert height
            signs[j]=1 if height>0 else -1
        # Expand lambda_T * (3*c_T^T adj(Q) c_T
        #                       + sum_{e in T} lambda_e^2 g_e^T adj(Q) g_e).
        # The off-diagonal contributions have factor 6, including both orders.
        term={}
        for i in non:term=add(term,shift(K[i,i],(i,i),3))
        for i,j in combinations(non,2):term=add(term,shift(K[i,j],(i,j),6*signs[i]*signs[j]))
        for i in B:term=add(term,shift(K[i,i],(i,i)))
        W=add(W,shift(term,B))
    assert len(trees)==125 and D==treepoly
    # The five graph orbits partition the connected spanning five-edge
    # graphs. Their coefficients are cycle_length - 2. The SOS checker also
    # enumerates these graphs directly, without using these representatives.
    patterns=[[(0,1),(0,2),(0,3),(1,2),(1,4)],
              [(0,1),(0,2),(0,3),(1,2),(3,4)],
              [(0,1),(0,2),(0,3),(1,4),(2,4)],
              [(0,1),(0,2),(1,3),(2,4),(3,4)],
              [(0,1),(0,2),(0,3),(0,4),(1,2)]]
    orbits=[orbit(p) for p in patterns]
    assert list(map(len,orbits))==[60,60,60,12,30]
    L=add(*xs)
    R=add(*(scale(p,c) for p,c in zip(orbits,[1,1,2,3,1])))
    S=add(mul(D,L),R)
    assert W==mul(D,S),'Geometric moment does not equal the literature polynomial'
    # Every coefficient of R is positive.
    assert min(R.values())==1 and max(R.values())==3
    vals=[evaluate(p,[1]*10) for p in (D,L,R,S,W)]
    assert vals==[125,10,306,1556,194500]
    output={'edges':[list(e) for e in EDGES],'D_terms':len(D),'S_terms':len(S),'R_terms':len(R),
            'DS_terms':len(W),'parallelotopes':len(trees),'orbit_sizes':list(map(len,orbits)),
            'coherent_heights':h,'formula_identity_verified':True,
            'all_unit_weights_D_L_R_S_DS':vals,
            'S_coefficients':[[list(e),c] for e,c in sorted(S.items())],
            'D_coefficients':[[list(e),c] for e,c in sorted(D.items())],
            'seconds':time.time()-start}
    Path(__file__).with_name('c1-moment.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if not k.endswith('_coefficients')},indent=2))

if __name__=='__main__':main()
