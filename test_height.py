import itertools

def solve_min_height(table, idems):
    memo = {}
    def eval_w(w):
        v = w[0]
        for x in w[1:]: v = table[v][x]
        return v

    def get_h(w):
        if len(w) == 1: return 0
        if w in memo: return memo[w]
        ans = 999
        # Option 1: binary splits
        for i in range(1, len(w)):
            h = 1 + max(get_h(w[:i]), get_h(w[i:]))
            if h < ans: ans = h
        # Option 2: idempotent splits
        # w = w_1 ++ ... ++ w_k (k >= 2) with eval(w_j) == e for some e in idems
        for e in idems:
            # dp[j, cnt] = min max_child_height for w[:j] partitioned into cnt pieces
            # cnt can be 0, 1, 2 (where 2 means >= 2)
            dp = {0: {0: 0}}
            for j in range(1, len(w) + 1):
                dp[j] = {}
                for i in range(0, j):
                    if j - i < len(w) and i in dp and eval_w(w[i:j]) == e:
                        h_piece = get_h(w[i:j])
                        for cnt, max_h in dp[i].items():
                            new_cnt = min(cnt + 1, 2)
                            new_max_h = max(max_h, h_piece)
                            if new_cnt not in dp[j] or new_max_h < dp[j][new_cnt]:
                                dp[j][new_cnt] = new_max_h
            if 2 in dp[len(w)]:
                h = 1 + dp[len(w)][2]
                if h < ans: ans = h
        memo[w] = ans
        return ans

    return get_h

table2 = [[1, 1], [1, 1]]
idems2 = [1]
h_fn = solve_min_height(table2, idems2)
print("TruncatedAdd 2, word of 0s:")
for L in range(1, 16):
    w = tuple([0]*L)
    print(f"L={L}: min_height = {h_fn(w)}")
