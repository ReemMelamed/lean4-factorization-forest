def find_word_and_semigroup():
    # Let n = 3. L = 2^(2*3-1) = 2^5 = 32.
    # Can we find an aperiodic semigroup S of size 3,
    # an evaluation map eval, and a word u of length 32
    # such that no two adjacent factors of u evaluate to the same idempotent?
    
    # What aperiodic semigroups of size 3 exist?
    # Let S = {0, 1, 2}.
    # Let's search over all associative operations on {0, 1, 2} that are aperiodic.
    import itertools
    
    def is_assoc(table):
        for x in range(3):
            for y in range(3):
                for z in range(3):
                    if table[table[x][y]][z] != table[x][table[y][z]]:
                        return False
        return True

    def is_aperiodic(table):
        # A finite semigroup is aperiodic iff for all x, x^3 = x^4 (or x^k = x^(k+1))
        # in S of size 3, x^3 = x^4 for all x.
        for x in range(3):
            p = [x]
            for _ in range(5):
                p.append(table[p[-1]][x])
            # p[k] is x^(k+1)
            # check if powers eventually become constant (period 1)
            # x^3 == x^4
            if p[2] != p[3]:
                return False
        return True

    def idempotents(table):
        return [x for x in range(3) if table[x][x] == x]

    # Find an aperiodic semigroup of size 3
    tables = []
    for table_flat in itertools.product(range(3), repeat=9):
        table = [list(table_flat[i*3:(i+1)*3]) for i in range(3)]
        if is_assoc(table) and is_aperiodic(table):
            tables.append(table)
            
    print(f'Total aperiodic semigroups of size 3: {len(tables)}')
    
    # For each table, let's see if there is a word u of length 32 where no two adjacent factors evaluate to the same idempotent
    for t_idx, table in enumerate(tables):
        idems = idempotents(table)
        # Try to find a word u of length 32 over {0, 1, 2}
        # Evaluation of factor u[i:j] is product of u[i]..u[j-1]
        # We want: for all 0 <= i < j < k <= 32: NOT (eval(u[i:j]) in idems and eval(u[j:k]) == eval(u[i:j]))
        
        # Let's greedily or via backtracking build such a word
        def can_extend(prefix, x):
            # check new factor ending at len(prefix)
            # For all split points j and start points i:
            new_word = prefix + [x]
            # new_word has length m
            m = len(new_word)
            # k = m
            # For each j from 1 to m-1:
            # eval(new_word[j:m]):
            val_right = new_word[j]
            # but wait, let's precompute products:
            pass

    return len(tables)

if __name__ == '__main__':
    find_word_and_semigroup()
