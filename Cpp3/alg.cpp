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
    ListTag tag;
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
    T head;
    unique_ptr<List<T>> tail;
    Cons(T h, unique_ptr<List<T>> t) : List<T>(ListTag::CONS), head(h), tail(move(t)) {}
};

// unsafeMap: returns a raw pointer (dyn)
template <typename A, typename B>
List<B> *unsafeMap(const List<A> *xs, function<B(A)> f)
{
    if (xs->tag == ListTag::NIL)
    {
        return dynamic_cast<List<B> *>(new Nil<B>());
    }
    else
    {
        auto zs = dynamic_cast<const Cons<A> *>(xs);
        return dynamic_cast<List<B> *>(new Cons<B>(f(zs->head), unique_ptr<List<B>>(unsafeMap(zs->tail.get(), f))));
    }
}

template <typename A, typename B>
unique_ptr<List<B>> map(const unique_ptr<List<A>> &xs, function<B(A)> f)
{
    return unique_ptr<List<B>>(unsafeMap(xs.get(), f));
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

// unsafeShowList: accepts raw pointer (dyn)
template <typename T>
void unsafeShowList(const List<T> *xs)
{
    if (xs->tag != ListTag::NIL)
    {
        auto z = dynamic_cast<const Cons<T> *>(xs);
        cout << z->head << " ";
        unsafeShowList(z->tail.get());
    }
}

template <typename T>
void showList(const unique_ptr<List<T>> &xs)
{
    cout << "[ ";
    unsafeShowList(xs.get());
    cout << "]" << endl;
    ;
}

int main()
{
    auto l1 = cons(1, cons(2, cons(3, nil<int>())));
    auto l2 = map<int, int>(l1, [](int x)
                            { return x + 1; });
    auto l3 = nil<int>();
    auto l4 = map<int, int>(l3, [](int x)
                            { return x; });

    showList(l1);
    showList(l2);
    showList(l3);
    showList(l4);

    return 0;
}