#include <iostream>

template <template <typename> class m>
struct Monad
{
    template <typename a>
    static m<a> mreturn(const a &);

    template <typename a, typename b>
    static m<b> mbind(const m<a> &, std::function<m<b>(const a &)>);
};

template <template <typename> class f>
struct Applicative
{
    template<typename a, typename b>
    static f<b> ap(const f<a> &,  f<std::function<b(const a &)>>);
};

template <template <typename> class f>
struct Functor
{
    template <typename a, typename b>
    static f<b> fmap(const f<a> &, std::function<b(const a &)>);
};

template <typename a>
struct Maybe
{
    bool isNothing;
    a value;
};

template <>
struct Functor<Maybe>
{
    template <typename a, typename b>
    static Maybe<b> fmap(const Maybe<a> &v, std::function<b(const a &)> f)
    {
        if (v.isNothing)
            return Maybe<b>{true, 0};
        else
            return Maybe<b>{false, f(v.value)};
    }
};

template<>
struct Applicative<Maybe>
{
    template<typename a, typename b>
    static Maybe<b> ap(const Maybe<a> &m,  Maybe<std::function<b(const a &)>>f)
    {
        if (m.isNothing || f.isNothing)
            return Maybe<b>{true, 0};
        else
            return Maybe<b>{false, f.value(m.value)};
    }
};

template <>
struct Monad<Maybe>
{
    template <typename a>
    static Maybe<a> mreturn(const a &v)
    {
        Maybe<a> x{false, v};
        return x;
    }

    template <typename a, typename b>
    static Maybe<b> mbind(const Maybe<a> &action, std::function<Maybe<b>(const a &)> f)
    {
        if (action.isNothing)
            return Maybe<b>{true, 0};
        else
            return f(action.value);
    }
};

int main()
{
    auto a = Monad<Maybe>::mreturn(1);
    auto b = Functor<Maybe>::fmap<int, int>(a, [](auto a)
                                            { return a * (-2); });

    std::cout << b.value << std::endl;

    auto c = Monad<Maybe>::mbind<int, char>(b, [](auto x)
                                            {
                                                if (x > 0)
                                                    return Maybe<char>{true, 0};
                                                else
                                                    return Maybe<char>{false, 'x'};
                                            });

    std::cout << c.value << std::endl;

    return 0;
}