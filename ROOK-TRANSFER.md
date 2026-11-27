# Paired borders and strict domination

Let P(X) = per(A + XJ). Its coefficient of Xʲ is j! times the number of placements of n−j nonattacking rooks on A. The triangular and paired-border operators in the module implement the polynomial recurrence for bordering the triangular board. The matrix-to-polynomial transfer is derived in the [upstream construction](https://github.com/aliromman/math/pull/44).

The transfer is additive over natural-coefficient polynomials. Its new constant is twice the old constant plus the old linear coefficient. A coefficientwise gap with positive constant therefore stays strictly positive under any number of transfers. Comparing only the two constants can give the opposite order after a single step, as the pair 1 and 3X demonstrates in the polynomial domain.

The exact independent program evaluates every coefficient by subset dynamic programming and cross-checks by Ryser interpolation at n+1 integers. At order eight the counts are 584 and 589. At order thirteen they are 666169 and 691829. The finite tests concern the two displayed boards, with no claim that a band is globally optimal at every order. Run `python scripts/rook_counts.py`.
