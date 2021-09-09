#include <iostream>
#include <functional>
#include <memory>
using namespace std;

enum class ListTag
{
    NIL,
    CONS
};

template <typename T>
class List
{
public:
    const ListTag tag;
    List() = delete;
    List(ListTag t) : tag(t) {}
    virtual ~List() = default;
};

template <typename T>
class Nil : public List<T>
{
public:
    Nil() : List<T>(ListTag::NIL) {}
};

template <typename T>
class Cons : public List<T>
{
public:
    const T head;
    const unique_ptr<List<T>> tail;
    Cons(T h, unique_ptr<List<T>> t) : List<T>(ListTag::CONS), head(h), tail(move(t)) {}
};

// head: destruction function
template <typename T>
const T &head(const unique_ptr<List<T>> &xs)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        throw exception();
    case ListTag::CONS:
        auto zs = dynamic_cast<const Cons<T> *>(xs.get());
        return zs->head;
    }
}

// tail: destruction function
template <typename T>
const unique_ptr<List<T>> &tail(const unique_ptr<List<T>> &xs)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        throw exception();
    case ListTag::CONS:
        auto zs = dynamic_cast<const Cons<T> *>(xs.get());
        return zs->tail;
    }
}

// cons: smart constructor
template <typename T>
unique_ptr<List<T>> cons(T h, unique_ptr<List<T>> t)
{
    return unique_ptr<List<T>>(dynamic_cast<List<T> *>(new Cons<T>(h, move(t))));
}

// nil: smart constractor
template <typename T>
unique_ptr<List<T>> nil()
{
    return unique_ptr<List<T>>(dynamic_cast<List<T> *>(new Nil<T>()));
}

template <typename A, typename B>
unique_ptr<List<B>> map(const unique_ptr<List<A>> &xs, function<B(A)> f)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return nil<B>();
    case ListTag::CONS:
        return cons(f(head(xs)), map(tail(xs), f));
    }
}

template <typename T>
unique_ptr<List<T>> filter(const unique_ptr<List<T>> &xs, function<bool(T)> f)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return nil<T>();
    case ListTag::CONS:
        auto z = head(xs);
        if (f(z))
            return cons<T>(z, filter(tail(xs), f));
        else
            return filter(tail(xs), f);
    }
}

template <typename T>
unique_ptr<List<T>> append(const unique_ptr<List<T>> &xs, const unique_ptr<List<T>> &ys)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return copyList(ys);
    case ListTag::CONS:
        return cons(head(xs), append(tail(xs), ys));
    }
}

template <typename A, typename B>
unique_ptr<List<B>> flatMap(const unique_ptr<List<A>> &xs, function<unique_ptr<List<B>>(A)> f)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return nil<B>();
    case ListTag::CONS:
        return append<B>(f(head(xs)), flatMap(tail(xs), f));
    }
}

template <typename T>
unique_ptr<List<T>> reverse(const unique_ptr<List<T>> &xs)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return nil<T>();
    case ListTag::CONS:
        return append(reverse(tail(xs)), cons(head(xs), nil<T>()));
    }
}

template <typename T>
void showHelper(const unique_ptr<List<T>> &xs)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return;
    case ListTag::CONS:
        cout << head(xs) << " ";
        showHelper(tail(xs));
    }
}

template <typename T>
void showList(const unique_ptr<List<T>> &xs)
{
    cout << "[ ";
    showHelper(xs);
    cout << "]" << endl;
}

template <typename T>
unique_ptr<List<T>> copyList(const unique_ptr<List<T>> &xs)
{
    switch (xs->tag)
    {
    case ListTag::CONS:
        return cons(head(xs), copyList(tail(xs)));
    case ListTag::NIL:
        return nil<T>();
    }
}

int main()
{
    auto l1 = cons(1, cons(2, cons(3, nil<int>())));
    auto l2 = filter<int>(map<int, int>(cons(0, copyList(l1)), [](int x)
                                        { return x + 1; }),
                          [](int x)
                          { return x > 2; });
    auto l3 = nil<int>();
    auto l4 = map<int, int>(l3, [](int x)
                            { return x; });

    showList(l1);
    showList(l2);
    showList(l3);
    showList(l4);
    showList(
        reverse(
            flatMap<int, int>(
                append(l1, l2),
                [](int x)
                { return cons(x, cons(x, nil<int>())); })));

    cout << head(l1) << endl;

    return 0;
}