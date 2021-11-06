#include <iostream>
using namespace std;

template <typename T, typename U>
auto larger(T &x, U &y) -> decltype(auto)
{
    return x > y ? x : y;
}

template <typename T, size_t N>
auto arrsize(T (&x)[N]) -> decltype(auto)
{
    return N;
}

auto add = [](auto x, auto y) -> auto
{
    return x + y;
};

int main()
{
    auto a = 10;
    auto b = 3.14;

    auto z = larger(a, b);

    cout << z << endl;

    int xs[] = {1, 2, 3, 4, 5};

    cout << arrsize(xs) << endl;

    cout << add(1.4, 1.7) << endl;

    return 0;
}