"""Two independent permanent computations."""
import math


def rook(n,points):
    # Rook DP allows a row to stay empty. Ryser below sums over column masks.
    allowed=[[int(j<=i or (i+1,j+1) in points) for j in range(n)] for i in range(n)]
    dp={0:1}
    for row in allowed:
        new=dp.copy()
        for used,val in dp.items():
            for j,t in enumerate(row):
                if t and not used&(1<<j):
                    target=used|(1<<j)
                    new[target]=new.get(target,0)+val
        dp=new
    rk=[0]*(n+1)
    for mask,v in dp.items():
        rk[mask.bit_count()]+=v
    def ryser(x):
        ans=0
        masks=[sum(t<<j for j,t in enumerate(row)) for row in allowed]
        for s in range(1<<n):
            z=s.bit_count()
            ans+=(-1)**(n-z)*math.prod((row&s).bit_count()+x*z for row in masks)
        return ans
    coeff=[math.factorial(t)*rk[n-t] for t in range(n+1)]
    for x in range(n+1):
        assert sum(c*x**i for i,c in enumerate(coeff))==ryser(x)
    return coeff


def board_checks():
    result={}
    for n,d in [(8,4),(13,6)]:
        A={(i,n+1-i) for i in range(1,d+1)}
        B={(1,n),(2,n-d+2),(d-1,n-1)}|{(i,i+n-d+1) for i in range(2,d-1)}
        a,b=rook(n,A),rook(n,B)
        diff=[y-x for x,y in zip(a,b)]
        assert min(diff)>=0 and diff[0]>0
        result[n]=dict(antidiagonal=a[0],witness=b[0],difference_coefficients=diff)
    return result


if __name__ == "__main__":
    print(board_checks())
