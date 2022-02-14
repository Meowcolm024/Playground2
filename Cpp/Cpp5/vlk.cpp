#include <string>
#include <iostream>
#include <variant>
#include <memory>

// Overload functions to a single overloaded definition
template <class... Ts>
struct overloaded : Ts...
{
    using Ts::operator()...;
};

template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

template <typename T>
using Ptr = std::shared_ptr<T>;

struct Nil
{
};

template <typename T>
struct Cons
{
    T h;
    Ptr<std::variant<Nil, Cons<T>>> ts;
    Cons(T a, Ptr<std::variant<Nil, Cons<T>>> b) : h(a) { ts = b; };
};

template <typename T>
using list = std::variant<Nil, Cons<T>>;

template <typename T>
Ptr<list<T>> nil()
{
    return std::make_shared<list<T>>(Nil());
}

template <typename T>
Ptr<list<T>> cons(T a, Ptr<list<T>> b)
{
    return std::make_shared<list<T>>(Cons(a, b));
}

// Match wrapper around std::visit for more intuitive interface, similar to Coq
template <typename T, typename Func, typename Func2>
auto match(Ptr<list<T>> l, Func f, Func2 g)
{
    return std::visit(overloaded{[&](Nil n)
                                 { return f(); },
                                 [&](Cons<T> c)
                                 { return g(c.h, c.ts); }},
                      *l);
}

// Print a list recursively
template <typename T>
void print(Ptr<list<T>> l)
{
    match(
        l,
        []()
        { std::cout << "null" << std::endl; },
        [](T t, Ptr<list<T>> tail)
        {
            std::cout << t << " ";
            print(tail);
        });
}

int main()
{
    auto l = cons(3, cons(4, nil<int>()));
    print(l);
    return 0;
}