#include <iostream>
#include <optional>
#include <memory>

using namespace std;

template <typename T>
struct Node
{
    T head;
    unique_ptr<Node<T>> tail;
    Node(T h, unique_ptr<Node<T>> t) : head(h), tail(move(t)) {}
};

template <typename T>
struct List
{
    unique_ptr<Node<T>> nodes;

    List() : nodes(nullptr) {}

    List<T> &cons(T value)
    {
        nodes = make_unique<Node<T>>(value, move(nodes));
        return *this;
    }

    optional<T> head() const
    {
        if (nodes != nullptr)
            return nodes->head;
        else
            return nullopt;
    }

    List<T> &dropFirst()
    {
        if (nodes != nullptr)
            nodes = move(nodes->tail);
        return *this;
    }
};

int main()
{
    auto test = List<int>();
    test.cons(1).cons(2).cons(3).dropFirst().cons(4);

    cout << test.head().value_or(-1) << endl;

    return 0;
}