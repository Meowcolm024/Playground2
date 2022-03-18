
def part(xs, p, q):
    m = xs[q]
    i = p - 1
    for j in range(p, q):
        if xs[j] <= m:
            i += 1
            xs[i], xs[j] = xs[j], xs[i]
    xs[i+1], xs[q] = xs[q], xs[i+1]
    return i + 1


def qsort(xs, p, q):
    if p >= q:
        return
    m = part(xs, p, q)
    qsort(xs, p, m-1)
    qsort(xs, m+1, q)


def quicksort(xs):
    if xs == []:
        return []
    else:
        p = xs[0]
        l = list(filter(lambda x: x < p, xs[1:]))
        r = list(filter(lambda x: x >= p, xs[1:]))
        return quicksort(l) + [p] + quicksort(r)


print(quicksort([4, 3, 7, 6, 1]))

a = [3, 5, 2, 9, 7, 6]
qsort(a, 0, 5)
print(a)
