#include <iostream>
#include <vector>
#include <functional>

using namespace std;

template <template <class> class T, class S, class U>
auto map(T<S> x, function<U(S)> f) -> decltype(auto)
{
    T<U> y{};
    for (auto &i : x)
        y.push_back(f(i));
    return y;
}

int main()
{
    auto haha = vector{1,2,3,4,5};
    auto bang = map<vector, int, int>(haha, [](auto i) { return i * 2;});

    for (auto &i : bang)
        cout << i << " ";
    cout << endl;
    return 0;
}
