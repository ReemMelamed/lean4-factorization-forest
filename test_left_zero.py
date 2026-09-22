# Let S = {0, 1}. Both are idempotents: 0*0 = 0, 1*1 = 1.
# What are the operations on {0, 1}?
# 1. Left zero: 0*1 = 0, 1*0 = 1.
# eval(w) is the first letter!
# If w = 0 1 0 1 0 1...
# What are the evaluations of factors?
# eval(w[i:j]) is w[i]!
# So eval(w[i:j]) depends ONLY on the start position!
# Now, can two adjacent factors have the same evaluation?
# Factor 1: w[i:j], starts at i, evaluates to w[i].
# Factor 2: w[j:k], starts at j, evaluates to w[j]!
# For Factor 1 and Factor 2 to evaluate to the SAME idempotent:
# we must have w[i] == w[j]!
# If w[i] != w[j], they evaluate to DIFFERENT idempotents!
print("Let's analyze Left Zero semigroup!")
