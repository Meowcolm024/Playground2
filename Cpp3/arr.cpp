#include <iostream>
#include <functional>
using namespace std;

template <typename T, size_t L>
class Arr
{
private:
    T internal[L];

public:
    Arr() {}

    template <typename Z>
    Arr<Z, L> map(function<Z(T)> f) const
    {
        auto t = Arr<Z, L>();
        for (int i = 0; i < L; i++)
            t[i] = f(internal[i]);
        return t;
    }

    T &operator[](size_t i)
    {
        return internal[i];
    }
    const T &operator[](size_t i) const
    {
        return internal[i];
    }
};

int main()
{
    int xs[10];
    auto zs = xs;
    auto ys = &xs;

    auto ps = Arr<int, 5>{};
    for (int i = 0; i < 5; i++)
        ps[i] = i;

    cout << ps.map<int>([](int x)
                        { return x * x; })[2]
         << endl;

    return 0;
}