import test_height as th, scratch_search2 as s, itertools

tables = [ [list(tf[i*3:(i+1)*3]) for i in range(3)] for tf in itertools.product(range(3), repeat=9) if s.is_assoc([list(tf[i*3:(i+1)*3]) for i in range(3)]) and s.is_aperiodic([list(tf[i*3:(i+1)*3]) for i in range(3)]) ]

# Zimin words:
# Z1 = (0,)
# Z2 = (0, 1, 0)
# Z3 = (0, 1, 0, 2, 0, 1, 0)
# Z4 = Z3 + (0,) + Z3 etc.
z1 = (0,)
z2 = (0, 1, 0)
z3 = (0, 1, 0, 2, 0, 1, 0)
z4 = z3 + (1,) + z3

for t_idx, table in enumerate(tables):
    idems = s.idempotents(table)
    h_fn = th.solve_min_height(table, idems)
    h3 = h_fn(z3)
    if h3 >= 4:
        print(f"Table {t_idx} on Z3 (len 7): height = {h3}")
        h4 = h_fn(z4)
        print(f"  on Z4 (len 15): height = {h4}")
        print("  Table:", table)
        print("  Idems:", idems)
