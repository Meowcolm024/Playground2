#include <iostream>

struct node
{
    int head;
    node *tail;
};

node *insert(node *n, node *rest)
{
    if (!rest)
    {
        n->tail = nullptr;
        return n;
    }
    else if (n->head > rest->head)
    {
        rest->tail = insert(n, rest->tail);
        return rest;
    }
    else
    {
        n->tail = rest;
        return n;
    }
}

node *isort(node *xs)
{
    if (!xs)
        return xs;
    return insert(xs, isort(xs->tail));
}

int main()
{
    using namespace std;

    auto x1 = node{5, nullptr};
    auto x2 = node{7, &x1};
    auto x3 = node{0, &x2};
    auto x4 = node{3, &x3};
    auto x5 = node{8, &x4};
    auto x6 = node{4, &x5};
    auto x7 = node{2, &x6};

    auto result = isort(&x7);

    for (auto i = result; i; i = i->tail)
        cout << i->head << endl;

    return 0;
}