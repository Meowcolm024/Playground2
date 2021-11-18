#include <iostream>

template <class T, class U>
struct Pair
{
    T x;
    U y;
};

template <class A>
Pair<A, A> f(A x, int acc)
{
    if (!acc)
        return Pair<A, A>{x, x};
    // ! template expansion diverges
    return f<Pair<A, A>>(Pair<A, A>{x, x}, acc - 1);
}

int main()
{
    auto r = f<int>(1, 10);
    return 0;
}
