import itertools

def is_assoc(table):
    for x in range(3):
        for y in range(3):
            for z in range(3):
                if table[table[x][y]][z] != table[x][table[y][z]]:
                    return False
    return True

def is_aperiodic(table):
    for x in range(3):
        p = [x]
        for _ in range(5):
            p.append(table[p[-1]][x])
        if p[2] != p[3]:
            return False
    return True

def idempotents(table):
    return [x for x in range(3) if table[x][x] == x]

def eval_word(table, w):
    val = w[0]
    for x in w[1:]:
        val = table[val][x]
    return val

def check_word(table, idems, w):
    # Check all 0 <= i < j < k <= len(w)
    # where eval(w[i:j]) == eval(w[j:k]) in idems
    L = len(w)
    # precompute factor evaluations
    # ev[i][j] = eval_word(table, w[i:j])
    ev = [[0]*(L+1) for _ in range(L)]
    for i in range(L):
        val = w[i]
        ev[i][i+1] = val
        for j in range(i+2, L+1):
            val = table[val][w[j-1]]
            ev[i][j] = val
    for i in range(L):
        for j in range(i+1, L):
            val1 = ev[i][j]
            if val1 in idems:
                for k in range(j+1, L+1):
                    if ev[j][k] == val1:
                        return False
    return True

def find_word():
    tables = []
    for table_flat in itertools.product(range(3), repeat=9):
        table = [list(table_flat[i*3:(i+1)*3]) for i in range(3)]
        if is_assoc(table) and is_aperiodic(table):
            tables.append(table)
            
    print(f'Total aperiodic: {len(tables)}')
    for t_idx, table in enumerate(tables):
        idems = idempotents(table)
        # Search for a word of length 10 or 15 or 32
        # Backtracking search
        target_len = 32
        found = []
        def dfs(w):
            if len(w) == target_len:
                found.append(w)
                return True
            # Try appending 0, 1, 2
            for a in range(3):
                new_w = w + [a]
                # Check condition for new_w ending at len(new_w)
                # k = len(new_w)
                k = len(new_w)
                ok = True
                for j in range(1, k):
                    val2 = eval_word(table, new_w[j:k])
                    if val2 in idems:
                        for i in range(0, j):
                            if eval_word(table, new_w[i:j]) == val2:
                                ok = False
                                break
                    if not ok:
                        break
                if ok:
                    if dfs(new_w):
                        return True
            return False
        
        if dfs([]):
            print(f'Table {t_idx} found word of length {target_len}: {found[0]}')
            print('Table:', table)
            print('Idempotents:', idems)
            return table, found[0]

find_word()
