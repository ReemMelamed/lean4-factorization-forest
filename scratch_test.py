# Test if there exists a word u of length L in a semigroup S of size n
# such that no two adjacent factors evaluate to the same idempotent.

def test_truncated_add(n, L):
    # S = {1, ..., n}, a*b = min(a+b, n)
    # unique idempotent is n
    # Any factor evaluates to n iff its sum >= n
    # Two adjacent factors both evaluate to n iff u = ... w1 w2 ... with sum(w1)>=n and sum(w2)>=n.
    # If all letters are >= 1, sum(w1 ++ w2) >= 2n.
    # Can we have a word of length L where no two adjacent factors have sum >= n?
    pass

# What if S is non-commutative or has other structure?
# Let's search all semigroups of size 2, 3, 4!
