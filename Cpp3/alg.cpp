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
    List() {}
    virtual ~List() = default;
};

template <typename T>
class Nil : public List<T>
{
public:
    ListTag tag;
    Nil() : tag(ListTag::NIL) {}
};

template <typename T>
class Cons : public List<T>
{
public:
    ListTag tag;
    T head;
    unique_ptr<List<T>> tail;
    Cons(T h, unique_ptr<List<T>> t) : head(h), tail(move(t)), tag(ListTag::CONS) {}
};

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

template <typename T>
unique_ptr<List<T>> cons(T h, unique_ptr<List<T>> t)
{
    auto x = new Cons<T>(h, move(t));
    // cout << "cons: " << int(x->tag) << " " << h << endl;
    auto z = dynamic_cast<List<T> *>(x);
    // cout << "cons: " << int(z->tag) << " " << h << endl;
    return unique_ptr<List<T>>(z);
}

template <typename T>
unique_ptr<List<T>> nil()
{
    auto *x = dynamic_cast<List<T> *>(new Nil<T>());
    return unique_ptr<List<T>>(x);
}

template <typename T>
void unsafeShow(const List<T> *xs)
{
    // cout << "tag: " << int(xs->tag) << endl;
    if (xs->tag == ListTag::NIL)
    {
        cout << "end" << endl;
    }
    else
    {
        const Cons<T> *z = dynamic_cast<const Cons<T> *>(xs);
        cout << z->head << " ";
        unsafeShow(z->tail.get());
    }
}

template <typename T>
void show(const unique_ptr<List<T>> &xs)
{
    // cout << "tag: " << int(xs->tag) << endl;
    unsafeShow(xs.get());
}

int main()
{
    auto l1 = cons(1, cons(2, cons(3, nil<int>())));
    auto l2 = map<int, int>(l1, [](int x)
                            { return x + 1; });
    auto l3 = nil<int>();
    auto l4 = map<int, int>(l3, [](int x)
                            { return x; });

    cout << "tag: " << int(l1->tag) << endl;
    show(l1);

    auto z = dynamic_cast<const Cons<int> *>(l1.get());
    cout << z->head << " " << int(z->tag) << endl;
    // auto x = dynamic_cast<const Cons<int> *>(l2.get());
    // cout << x->head << endl;

    return 0;
}