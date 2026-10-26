"""A second moment calculation by triangulating Voronoi boundaries.

The program constructs the cone generators, enumerates facets and vertices,
triangulates the facets, and integrates the simplices joined to the origin.
The wrapper compares the resulting moment polynomials with those obtained
by zonotope and vertex integration.
"""
from fractions import Fraction as F
from itertools import product, combinations
from math import isqrt
from collections import defaultdict
from pathlib import Path
import json, sys, time

A=((2,1,-1,-1),(1,2,-1,-1),(-1,-1,2,0),(-1,-1,0,2))
EDGES=list(combinations(range(5),2))

def det(M):
    if len(M)==1:return M[0][0]
    return sum((-1)**j*M[0][j]*
        det([r[:j]+r[j+1:] for r in M[1:]])
        for j in range(len(M)))

def adj(M):
    n=len(M)
    return [[(-1)**(i+j)*det(
        [[M[u][v] for v in range(n) if v!=i]
         for u in range(n) if u!=j])
        for j in range(n)] for i in range(n)]

def dot(x,y):return sum(a*b for a,b in zip(x,y))
def norm(z,Q):
    return sum(z[i]*Q[i][j]*z[j] for i in range(4) for j in range(4))

def rays(k):
    out=[];labels=[]
    for i,j in EDGES:
        if k>=2 and (i,j)==(1,2):continue
        if k==3 and (i,j)==(3,4):continue
        v=[int(l==j-1)-int(i>0 and l==i-1) for l in range(4)]
        out.append([[x*y for y in v] for x in v])
        labels.append(str(i)+str(j))
    if k==3:
        v=[1,1,-1,-1]
        out.append([[x*y for y in v] for x in v]);labels.append('b')
    if k>=2:
        out.append([list(r) for r in A]);labels.append('a')
    assert len(out)==10
    return out,labels

def shortest(Q):
    """Find all shortest vectors in each nonzero parity class.

    A representative in {0,1}^4 supplies the common squared-length bound b.
    Cauchy--Schwarz gives z_i^2 <= b*(Q^-1)_{ii}; hence the box is exhaustive.
    """
    d=det(Q);J=adj(Q)
    assert all(det([r[:i] for r in Q[:i]])>0 for i in range(1,5))
    b=max(norm(z,Q) for z in product((0,1),repeat=4))
    lim=[isqrt(b*J[i][i]//d) for i in range(4)]
    low={};vec={}
    for z in product(*(range(-v,v+1) for v in lim)):
        c=tuple(t%2 for t in z)
        if not any(c):continue
        n=norm(z,Q)
        if c not in low or n<low[c]:low[c]=n;vec[c]={z}
        elif n==low[c]:vec[c].add(z)
    assert len(low)==15
    return sorted(set().union(*vec.values()))

# Exponent e_i occupies bits 4i,...,4i+3.
# All products below have total degree <=9, so no digit carry occurs.
def add(*pp):
    z=defaultdict(int)
    for p in pp:
        for m,c in p.items():z[m]+=c
    return {m:c for m,c in z.items() if c}

def scale(p,c):return {m:v*c for m,v in p.items() if v*c}

def mul(p,q):
    z=defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():z[a+b]+=c*d
    return {m:c for m,c in z.items() if c}

def pd(M):
    if len(M)==1:return M[0][0]
    return add(*(scale(mul(M[0][j],
        pd([r[:j]+r[j+1:] for r in M[1:]])),(-1)**j)
        for j in range(len(M))))

def lin(v):return {1<<(4*i):c for i,c in enumerate(v) if c}

def quad(v,J):
    return add(*(scale(mul(mul(v[i],v[j]),J[i][j]),
        1 if i==j else 2)
        for i in range(4) for j in range(i,4)))

def divide(p,q):
    p=p.copy();ans={};lead=max(q)
    while p:
        top=max(p)
        assert all(((top>>(4*i))&15)>=((lead>>(4*i))&15)
                   for i in range(10))
        e=top-lead;c=F(p[top],q[lead])
        ans[e]=ans.get(e,0)+c
        for m,v in q.items():
            k=m+e;p[k]=p.get(k,0)-c*v
            if not p[k]:del p[k]
    assert all(c.denominator==1 for c in ans.values())
    return {e:int(c) for e,c in ans.items() if c}

def export(p):
    return [[[(e>>(4*i))&15 for i in range(10)],c]
            for e,c in sorted(p.items())]

def rebuild(k):
    """Reconstruct cone k with a placed last, unlike the localization files."""
    start=time.monotonic();R,labels=rays(k)
    Q0=[[sum(r[i][j] for r in R) for j in range(4)] for i in range(4)]
    Z=shortest(Q0);assert len(Z)==30
    assert all(
        sum(tuple(v%2 for v in z)==p for z in Z)==2
        for p in product((0,1),repeat=4) if any(p)
    )
    for r in R:
        if det(r):
            assert set(Z)<=set(shortest(r))
        else:
            i=next(i for i in range(4) if r[i][i]==1);u=r[i]
            assert r==[[a*b for b in u] for a in u]
            assert all(norm(z,r) in (0,1) for z in Z)

    rhs=[[norm(z,r) for r in R] for z in Z]
    vertices={}
    for ids in combinations(range(30),4):
        M=[list(Z[i]) for i in ids];d=det(M)
        if not d:continue
        J=adj(M)
        C=[[F(sum(J[i][j]*rhs[ids[j]][l] for j in range(4)),d)
            for l in range(10)] for i in range(4)]
        at0=[sum(row) for row in C]
        if any(dot(z,at0)>sum(b) for z,b in zip(Z,rhs)):continue
        assert all(x.denominator==1 for row in C for x in row)
        C=[[int(x) for x in row] for row in C]
        active=[]
        for j,(z,b) in enumerate(zip(Z,rhs)):
            slack=[b[l]-sum(z[i]*C[i][l] for i in range(4))
                   for l in range(10)]
            assert min(slack)>=0
            if not any(slack):active.append(j)
        assert len(active)==4 and det([list(Z[j]) for j in active])
        vertices[tuple(sum(C,[]))]=(C,active)

    # The coefficientwise slack tests above retain vertices on the whole
    # positive parameter cone. Completeness follows from the normal-cone
    # argument in Proposition 2.3.
    vv=sorted(vertices.values(),key=lambda v:tuple(sum(row) for row in v[0]))
    assert len(vv)==120
    C=[v[0] for v in vv];act=[v[1] for v in vv]
    facets=[{i for i,a in enumerate(act) if j in a} for j in range(30)]
    # A pulling triangulation: choose the smallest vertex of each facet,
    # then of each face not containing it. Join the resulting tetrahedra
    # to the origin to obtain four-dimensional simplices.
    tets=[]
    for j,facet in enumerate(facets):
        root=min(facet)
        faces={tuple(sorted(facet&g)) for i,g in enumerate(facets)
               if i!=j and len(facet&g)>=3}
        for face in sorted(faces):
            if root in face:continue
            f=set(face);v=min(f)
            edges={tuple(sorted(f&g)) for g in facets if len(f&g)==2}
            for e in sorted(edges):
                if v in e:continue
                t=[root,v,*e]
                d=det([[sum(row) for row in C[i]] for i in t]);assert d
                if d<0:t[0],t[1]=t[1],t[0]
                tets.append(t)
    assert len(tets)==(582 if k==3 else 580)

    # Every oriented triangle in the boundary triangulation must cancel.
    boundary=defaultdict(int)
    for t in tets:
        for i in range(4):
            f=t[:i]+t[i+1:]
            s=(-1)**(i+sum(f[a]>f[b]
                          for a in range(3) for b in range(a+1,3)))
            boundary[tuple(sorted(f))]+=s
    assert not any(boundary.values())

    Q=[[lin([r[i][j] for r in R]) for j in range(4)] for i in range(4)]
    D=pd(Q)
    J=[[scale(pd([[Q[u][v] for v in range(4) if v!=i]
                  for u in range(4) if u!=j]),(-1)**(i+j))
        for j in range(4)] for i in range(4)]
    points=[[lin(row) for row in c] for c in C]
    mom=[quad(v,J) for v in points]
    W={};Vol={}
    for t in tets:
        v=[points[i] for i in t];delta=pd(v)
        Vol=add(Vol,delta)
        summed=[add(*(p[i] for p in v)) for i in range(4)]
        W=add(W,mul(delta,add(*(mom[i] for i in t),quad(summed,J))))
    assert Vol==scale(D,384)

    # For conv(0,v1,...,v4), the quadratic moment uses 4!*5*6 = 720.
    # After r=2Qx, M has factor 1/(64*D^2). Thus W=768*D*N,
    # where N=60*D*M on every cone (and equals 5*S on C1).
    N=divide(W,scale(D,768))
    assert W==scale(mul(D,N),768)
    assert all(sum((e>>(4*i))&15 for i in range(10))==5 for e in N)

    out=dict(labels=labels,rays=R,facets=Z,vertices=C,active=act,
             tetrahedra=tets,D=export(D),N=export(N))
    path=Path(__file__).resolve().parent/f'rebuilt_C{k}.json'
    path.write_text(json.dumps(out,separators=(',',':')))
    print('C%d: %d facets, %d vertices, %d tetrahedra; '
          'D:%d N:%d W:%d terms; %.2fs' %
          (k,len(Z),len(C),len(tets),len(D),len(N),len(W),
           time.monotonic()-start),flush=True)

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run without -O.')
    for k in map(int,sys.argv[1:] or ['1','2','3']):rebuild(k)
