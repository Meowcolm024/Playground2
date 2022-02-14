#include <iostream>
#include <optional>
#include <memory>
using namespace std;

struct node
{
    int value;
    optional<unique_ptr<node>> next;

    node(int v, optional<unique_ptr<node>> n)
    {
        value = v;
        if (n != nullopt)
            next = move(n.value());
        else
            next = nullopt;
    }
};

struct stack
{
    optional<unique_ptr<node>> internal;
    int size;

    stack() : internal(nullopt), size(0) {}

    void push(int val)
    {
        internal = make_unique<node>(val, move(internal));
        size++;
    }

    optional<int> pop()
    {
        if (internal == nullopt)
            return nullopt;
        auto tmp = move(internal.value());
        internal = move(tmp->next);
        size--;
        return tmp->value;
    }
};

int main()
{
    stack box = stack();
    box.push(10);
    box.push(20);
    cout << box.size << endl;
    cout << box.pop().value_or(0) << endl;
    box.push(30);
    cout << box.pop().value_or(0) << endl;
    cout << box.pop().value_or(0) << endl;
    cout << box.pop().value_or(0) << endl;
    cout << box.size << endl;
    return 0;
}
