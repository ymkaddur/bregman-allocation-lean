import math
from itertools import combinations, product

def frontier(pairs):
    out={}
    best=math.inf
    for (a,b),w in sorted(pairs.items()):
        if b<best:
            out[a,b]=w
            best=b
    return out

def solve(menus,forget=True):
    rest=[0]*(len(menus)+1)
    for i in reversed(range(len(menus))):
        mask=rest[i+1]
        for ask,_,_ in menus[i]:
            mask|=ask
        rest[i]=mask
    states={0:{(0,0):()}}
    attempts=0
    peak=1
    for i,menu in enumerate(menus):
        out={}
        for seen,opts in states.items():
            for j,(ask,work,extra) in enumerate(menu):
                nxt=seen|ask
                if forget:
                    nxt &= rest[i+1]
                box=out.setdefault(nxt,{})
                for (cost,ops),w in opts.items():
                    attempts+=1
                    box.setdefault((cost+(ask&~seen).bit_count()+extra,ops+work),w+(j,))
        states={k:frontier(v) for k,v in out.items()}
        peak=max(peak,len(states))
    result=frontier({c:w for opts in states.values() for c,w in opts.items()})
    for c,w in result.items():
        assert score(menus,w)==c
    return result,attempts,peak

def score(menus,w):
    seen=total=ops=0
    for menu,j in zip(menus,w):
        ask,work,extra=menu[j]
        total+=(ask&~seen).bit_count()+extra
        seen|=ask
        ops+=work
    return total,ops

def exhaustive(menus):
    return frontier({score(menus,w):w for w in product(*(range(len(menu)) for menu in menus))})

def check_synthesis():
    options=[(1,1,0),(2,0,1),(3,1,1),(0,2,1)]
    candidate=list(combinations(options,2))
    n=0
    for menus in product(candidate,repeat=4):
        raw=exhaustive(menus)
        assert raw.keys()==solve(menus)[0].keys()==solve(menus,False)[0].keys()
        n+=1
    # Each private producer is dead after its own stage. One shared producer may recur.
    family=[[(1<<(i+1),0,0),(1,1,0)] for i in range(14)]
    a,b=solve(family),solve(family,False)
    assert a[0].keys()==b[0].keys()==exhaustive(family).keys()
    return {"finite_four_stage_instances":n,"choices_per_instance":16,
            "family":{"stages":14,"quotient_visits":a[1],"raw_visits":b[1],
            "quotient_peak":a[2],"raw_peak":b[2],"pareto":[list(c) for c in a[0]]}}

if __name__=="__main__":
    print(check_synthesis())
