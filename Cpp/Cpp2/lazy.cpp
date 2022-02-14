#include <iostream>

using namespace std;

template <typename L, typename R>
struct Sum
{
    L left;
    R right;

    Sum(L l, R r) : left(l), right(r) {}
};

auto add(int l, int r) -> decltype(Sum(l, r))
{
    return Sum(l, r);
}

template <typename T>
auto add(int l, Sum<int, T> r) -> decltype(Sum(l, r))
{
    return Sum(l, r);
}

template <typename L, typename R>
auto eval(Sum<L, R> s) -> int = delete;

template <>
auto eval(Sum<int, int> s) -> int
{
    return s.left + s.right;
}

template <typename L, typename R>
auto eval(Sum<int, Sum<L, R>> s) -> int
{
    return s.left + eval(s.right);
}

int main()
{
    auto a = Sum(1, Sum(2, Sum(3, Sum(4, Sum(5, 6)))));

    cout << eval(a) << endl;

    return 0;
}