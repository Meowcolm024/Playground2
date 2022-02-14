def subsetsum(set: list, mx: int) -> list:
    def s(i: int) -> int: return set[i-1]

    def dp(n: int, W: int) -> list:
        M = [[0 for _ in range(W+1)] for _ in range(n+1)]
        for i in range(1, n+1):
            for j in range(1, W+1):
                if s(i) > j:
                    M[i][j] = M[i-1][j]
                M[i][j] = max(M[i-1][j], s(i) + M[i-1][j-s(i)])
        return M

    def opt(M: list, n: int, W: int) -> list:
        if M[n][W] == 0:
            return []
        if M[n][W] > W:
            return opt(M, n-1, W)
        return [s(n)] + opt(M, n-1, W-s(n))

    return opt(dp(len(set), mx), len(set), mx)


print(subsetsum([1, 2, 3, 4, 5, 6, 7], 12))
