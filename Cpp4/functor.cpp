#include <iostream>
#include <functional>
using namespace std;

#define TOONE(T)                                                      \
    template <>                                                       \
    struct ToOne<T>                                                   \
    {                                                                 \
        template <typename a>                                         \
        static T<int>                                                 \
        toOne(const T<a> &m)                                          \
        {                                                             \
            return Functor<T>::map<a, int>(m, [](a x) { return 1; }); \
        }                                                             \
    };

template <template <typename> class f>
struct Functor
{
    template <typename a, typename b>
    static f<b> map(const f<a> &, function<b(a)>);
};

template <template <typename> class f>
struct ToOne
{
    template <typename a>
    static f<int> toOne(const f<a> &m);
};

template <typename T>
struct Maybe
{
    bool nothing;
    T just;
    Maybe() : nothing(true) {}
    Maybe(T x) : nothing(false), just(x) {}
};

template <>
struct Functor<Maybe>
{
    template <typename a, typename b>
    static Maybe<b> map(const Maybe<a> &m, function<b(a)> f)
    {
        Maybe<b> tmp;
        if (m.nothing)
            tmp.nothing = true;
        else
        {
            tmp.nothing = false;
            tmp.just = f(m.just);
        }
        return tmp;
    }
};

// create function for Maybe
TOONE(Maybe)

template <typename a>
a unwarp(const Maybe<a> &m, a d)
{
    if (m.nothing)
        return d;
    else
        return m.just;
}

int main()
{
    auto hi = Maybe(11);
    auto ha = Maybe<int>();

    cout << unwarp(Functor<Maybe>::map<int, int>(hi, [](int x)
                                                 { return x * 2; }),
                   0)
         << " " << unwarp(ha, 0) << endl;

    cout << ToOne<Maybe>::toOne(hi).just << endl;

    return 0;
}