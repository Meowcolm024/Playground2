struct Z
{
    using result = Z;
};

template <class n>
struct S
{
    using result = S<typename n::result>;
};

template <class x, class y>
struct Add
{
};

template <class y>
struct Add<Z, y>
{
    using result = y;
};

template <class x, class y>
struct Add<S<x>, y>
{
    using result = S<typename Add<x, y>::result>;
};

using three = Add<S<Z>, S<S<Z>>>::result;
