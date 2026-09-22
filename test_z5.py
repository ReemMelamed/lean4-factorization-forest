import test_height as th, scratch_search2 as s, itertools

tables = [ [list(tf[i*3:(i+1)*3]) for i in range(3)] for tf in itertools.product(range(3), repeat=9) if s.is_assoc([list(tf[i*3:(i+1)*3]) for i in range(3)]) and s.is_aperiodic([list(tf[i*3:(i+1)*3]) for i in range(3)]) ]

# Zimin words modulo 3:
z = [0]
for step in range(1, 5):
    # step letter: 1, 2, 0, 1...
    letter = step % 3
    z = z + [letter] + z

z5 = tuple(z)
print("z5 length:", len(z5)) # 31

max_h = 0
best_t = None
for idx, table in enumerate(tables):
    idems = s.idempotents(table)
    h_fn = th.solve_min_height(table, idems)
    h = h_fn(z5)
    if h > max_h:
        max_h = h
        best_t = idx
        print(f"Table {idx} has height {h} on z5!")
print(f"Max height on z5: {max_h}")
