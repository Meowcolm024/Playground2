#include <iostream>
#include <functional>
#include <memory>
using namespace std;

template <typename T>
class List;

template <typename T>
using ListPtr = unique_ptr<List<T>>;

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
    const ListPtr<T> tail;
    Cons(T h, ListPtr<T> t) : List<T>(ListTag::CONS),
                              head(h),
                              tail(move(t)) {}
};

// head: destruction function
template <typename T>
const T &head(const ListPtr<T> &xs)
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
const ListPtr<T> &tail(const ListPtr<T> &xs)
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
ListPtr<T> cons(T h, ListPtr<T> t)
{
    return ListPtr<T>(dynamic_cast<List<T> *>(new Cons<T>(h, move(t))));
}

// nil: smart constractor
template <typename T>
ListPtr<T> nil()
{
    return ListPtr<T>(dynamic_cast<List<T> *>(new Nil<T>()));
}

template <typename A, typename B>
ListPtr<B> map(const ListPtr<A> &xs, function<B(A)> f)
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
ListPtr<T> filter(const ListPtr<T> &xs, function<bool(T)> f)
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
ListPtr<T> append(const ListPtr<T> &xs, const ListPtr<T> &ys)
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
ListPtr<B> flatMap(const ListPtr<A> &xs, function<ListPtr<B>(A)> f)
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
ListPtr<T> reverse(const ListPtr<T> &xs)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return nil<T>();
    case ListTag::CONS:
        return append(reverse(tail(xs)), cons(head(xs), nil<T>()));
    }
}

template <typename A, typename B>
B foldl(const ListPtr<A> &xs, B z, function<B(B, A)> f)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return z;
    case ListTag::CONS:
        return foldl(tail(xs), f(z, head(xs)), f);
    }
}

template <typename A, typename B>
B foldr(const ListPtr<A> &xs, B z, function<B(A, B)> f)
{
    switch (xs->tag)
    {
    case ListTag::NIL:
        return z;
    case ListTag::CONS:
        return f(head(xs), foldr(tail(xs), z, f));
    }
}

template <typename T>
void showHelper(const ListPtr<T> &xs)
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
void showList(const ListPtr<T> &xs)
{
    cout << "[ ";
    showHelper(xs);
    cout << "]" << endl;
}

template <typename T>
ListPtr<T> copyList(const ListPtr<T> &xs)
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
    auto l2 = filter<int>(
        map<int, int>(
            cons(0, copyList(l1)),
            [](int x)
            { return x + 1; }),
        [](int x)
        { return x > 2; });
    auto l3 = nil<int>();
    auto l4 = map<int, int>(l3, [](int x)
                            { return x; });

    auto l5 = reverse(
        flatMap<int, int>(
            append(l1, l2),
            [](int x)
            { return cons(x, cons(x, nil<int>())); }));

    showList(l1);
    showList(l2);
    showList(l3);
    showList(l4);
    showList(l5);

    cout << head(l1) << endl;
    cout << foldr<int, int>(l5, 0, [](int x, int y)
                            { return x + y; })
         << endl;

    return 0;
}