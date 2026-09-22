import scratch_search2 as s, itertools

tables = [ [list(tf[i*3:(i+1)*3]) for i in range(3)] for tf in itertools.product(range(3), repeat=9) if s.is_assoc([list(tf[i*3:(i+1)*3]) for i in range(3)]) and s.is_aperiodic([list(tf[i*3:(i+1)*3]) for i in range(3)]) ]

# To find if any word has min_height >= 5:
# For each height h = 0, 1, 2, 3, 4:
# What language of words can be formed at height <= h with evaluation v?
# A tree has height <= h and evaluates to v.
# This is a context-free grammar / language!
# Can all words be formed at height <= 4?
# If the set of words parseable at height <= 4 is ALL of Sigma^+, then max height is <= 4!
# If there is some word NOT parseable at height <= 4, then that word has height >= 5!
print("Script ready")
