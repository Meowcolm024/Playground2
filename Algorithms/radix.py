from typing import List


def cs(xs: List[int]) -> List[int]:
    assert min(xs) >= 1
    counter = [0 for _ in range(max(xs)+1)]
    result = [0 for _ in xs]
    for x in xs:
        counter[x] += 1
    for i in range(1, len(counter)):
        counter[i] += counter[i-1]
    for j in range(len(xs)-1, -1, -1):
        result[counter[xs[j]]-1] = xs[j]
        counter[xs[j]] -= 1
    return result


def radix(xs: List[List[int]]) -> List[List[int]]:
    if xs == []: return []
    assert all(xs, lambda k: len(k) == len(xs[0]))
    assert all(xs, lambda k: all(k, k >= 0 and k <= 9)) 
    return []


print(cs([4, 3, 6, 9, 1]))
