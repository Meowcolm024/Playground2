from math import floor


def unimodal(A, p, q):
    if p > q:
        return None
    if p == q:
        return A[p]
    else:
        mid = floor((p + q)/2)
        if A[mid] < A[mid + 1]:
            return unimodal(A, p, mid)
        else:
            return unimodal(A, mid+1, q)

print(unimodal([9,5,4,6,8,12,14], 0, 6))
