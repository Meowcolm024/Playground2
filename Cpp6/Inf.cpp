#include <iostream>

template <class T, class U>
struct Pair
{
    T x;
    U y;
};

template <class A>
void f(A x, int acc)
{
    if (acc == 0)
        return;
    std::cout << x << std::endl;
    f(Pair<A, A>{x, x}, acc-1);
}

int main()
{
    f<int>(1, 10);
    return 0;
}
